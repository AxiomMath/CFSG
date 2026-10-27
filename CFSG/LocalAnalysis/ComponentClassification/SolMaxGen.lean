module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxQuot
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxAscent

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]

theorem conj_mem_coreActionKernel {M : Subgroup G} {g c : G} (hg : g ∈ normalizer (M : Set G))
    (hc : c ∈ coreActionKernel M) : g * c * g⁻¹ ∈ coreActionKernel M := by
  obtain ⟨hcN, hcM⟩ := mem_coreActionKernel.mp hc
  refine mem_coreActionKernel.mpr ⟨mul_mem (mul_mem hg hcN) (inv_mem hg), fun j hj => ?_⟩
  have hj' : g⁻¹ * j * g ∈ M := by
    have := (mem_normalizer_iff.mp (inv_mem hg) j).mp hj
    simpa using this
  have h1 := hcM _ hj'
  have hO := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic M (pPrimeCore 2 M) hg
  have h2 := (mem_normalizer_iff.mp hO _).mp h1
  have e : g * ((g⁻¹ * j * g)⁻¹ * c⁻¹ * (g⁻¹ * j * g) * c) * g⁻¹ =
      j⁻¹ * (g * c * g⁻¹)⁻¹ * j * (g * c * g⁻¹) := by group
  rwa [e] at h2

variable [Finite G]

theorem le_coreActionKernel_of_layerAt {K A B M : Subgroup G}
    (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K)) (hA2 : IsPGroup 2 A) (hB2 : IsPGroup 2 B)
    (hAB : A ≤ B) (hBQ : B ≤ coreActionKernel K) (hstarA : StarAt K A)
    (hM : IsTwoComponentIn M (centralizer (A : Set G)))
    (hB : twoLayerIn (K ⊓ centralizer (B : Set G)) ≤ coreActionKernel M) :
    twoLayerIn (K ⊓ centralizer (A : Set G)) ≤ coreActionKernel M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LA := twoLayerIn (K ⊓ centralizer (A : Set G)) with hLA
  set LB := twoLayerIn (K ⊓ centralizer (B : Set G)) with hLB
  have hLBA : LB ≤ LA := layerAt_mono hKq hA2 hB2 hAB hBQ
  obtain ⟨hLAp, -, -, -⟩ := layerAt_facts hKq hA2 (hAB.trans hBQ)
  obtain ⟨-, hLBe, hBsup, -⟩ := Sol76.cover_facts hKq inf_le_left
    (Sol76.inf_centralizer_sup_oddCoreIn_eq hB2 hBQ)
  have hLAK : LA ≤ K := (map_subtype_le _).trans inf_le_left
  have hLBK : LB ≤ K := hLBA.trans hLAK
  have hLAN : LA ≤ normalizer (M : Set G) :=
    hstarA.trans (twoLayerIn_le_normalizer hM.1 hM.2)
  set D := coreActionKernel M ⊓ LA with hD
  set R := LA ⊓ oddCoreIn K with hR
  have hRn : (R.subgroupOf LA).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact fun l hl => mem_normalizer_inf (le_normalizer hl)
      (Sol76.le_normalizer_oddCoreIn K (hLAK hl))
  have hRodd : Odd (Nat.card (R.subgroupOf LA)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : R ≤ LA)).toEquiv]
    have h1 : Odd (Nat.card (oddCoreIn K)) := by
      rw [oddCoreIn, Nat.card_congr ((pPrimeCore 2 ↥K).equivMapOfInjective _
        K.subtype_injective).symm.toEquiv]
      exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥K))
    exact h1.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hDn : LA ≤ normalizer (D : Set G) := by
    intro l hl
    refine mem_normalizer_inf ?_ (le_normalizer hl)
    rw [mem_normalizer_iff]
    intro c
    constructor
    · exact fun hc => conj_mem_coreActionKernel (hLAN hl) hc
    · intro hc
      have := conj_mem_coreActionKernel (inv_mem (hLAN hl)) hc
      simpa [mul_assoc] using this
  have hRD : R.subgroupOf LA ≤ normalizer ((D.subgroupOf LA : Subgroup LA) : Set LA) := by
    intro r _
    rw [mem_normalizer_iff]
    intro d
    rw [mem_subgroupOf, mem_subgroupOf]
    have h := (mem_normalizer_iff.mp (hDn r.2) d).symm
    simpa using h.symm
  have hLAp' : Group.IsPerfect ↥LA := Subgroup.isPerfect_iff.mpr hLAp
  have htop : Group.IsPerfect ↥(⊤ : Subgroup LA) :=
    Group.IsPerfect.ofSurjective
      (f := ((Subgroup.topEquiv : (⊤ : Subgroup ↥LA) ≃* ↥LA).symm).toMonoidHom)
      (Subgroup.topEquiv : (⊤ : Subgroup ↥LA) ≃* ↥LA).symm.surjective
  have hcov : (⊤ : Subgroup LA) ≤ D.subgroupOf LA ⊔ R.subgroupOf LA := by
    rintro ⟨l, hl⟩ -
    have hlK : l ∈ oddCoreIn K ⊔ LB := by
      rw [sup_comm, hLB, hLBe, hBsup]
      exact hLAK hl
    have hLBn : LB ≤ normalizer (oddCoreIn K : Set G) :=
      fun b hb => Sol76.le_normalizer_oddCoreIn K (hLBK hb)
    obtain ⟨o, ho, b, hb, rfl⟩ := Sol76.exists_mul_of_mem_sup_normalizer hLBn hlK
    have hbA : b ∈ LA := hLBA hb
    have hoA : o ∈ LA := by
      have : o = o * b * b⁻¹ := by group
      rw [this]
      exact mul_mem hl (inv_mem hbA)
    have e : (⟨o * b, hl⟩ : LA) = ⟨o, hoA⟩ * ⟨b, hbA⟩ := rfl
    rw [e]
    exact mul_mem (mem_sup_right (show (⟨o, hoA⟩ : LA) ∈ R.subgroupOf LA from ⟨hoA, ho⟩))
      (mem_sup_left (show (⟨b, hbA⟩ : LA) ∈ D.subgroupOf LA from ⟨hB hb, hbA⟩))
  have h := le_of_perfect_le_sup_of_odd hRodd hRD htop hcov
  intro l hl
  exact (h (mem_top ⟨l, hl⟩)).1

theorem map_le_centralizer_of_le_coreActionKernel {Y T R : Subgroup G}
    (hT : IsTwoComponentIn T Y) (hR : R ≤ coreActionKernel T) :
    (R.subgroupOf Y).map (QuotientGroup.mk' (pPrimeCore 2 ↥Y)) ≤
      centralizer (((T.subgroupOf Y).map (QuotientGroup.mk' (pPrimeCore 2 ↥Y)) : Subgroup _) :
        Set (↥Y ⧸ pPrimeCore 2 ↥Y)) := by
  set O := pPrimeCore 2 ↥Y
  rintro _ ⟨r, hr, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  have h1 := commutator_mem_oddCoreIn_of_le hT hR (mem_subgroupOf.mp hr) (mem_subgroupOf.mp hk)
  obtain ⟨o, ho, hoe⟩ := h1
  have h3 : o = k⁻¹ * r⁻¹ * k * r := Subtype.ext (by simpa using hoe)
  rw [h3] at ho
  rw [← map_mul, ← map_mul]
  refine (QuotientGroup.eq (s := O)).mpr ?_
  have e : (k * r)⁻¹ * (r * k) = (k⁻¹ * r⁻¹ * k * r)⁻¹ := by group
  rw [e]
  exact inv_mem ho

theorem le_sSup_moved_twoComponents {Y P : Subgroup G} (hPY : P ≤ twoLayerIn Y)
    (hP : ⁅P, P⁆ = P) :
    P ≤ sSup {T : Subgroup G | IsTwoComponentIn T Y ∧ ¬ P ≤ coreActionKernel T} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := {T : Subgroup G | IsTwoComponentIn T Y ∧ ¬ P ≤ coreActionKernel T} with hS
  have hPY' : P ≤ Y := hPY.trans (map_subtype_le _)
  set O := pPrimeCore 2 ↥Y with hO
  set π := QuotientGroup.mk' O with hπ
  set S' := (fun T : Subgroup G => T.subgroupOf Y) '' S with hS'
  set D' := sSup S' with hD'
  have hOD : O ≤ normalizer ((D' : Subgroup Y) : Set Y) := by
    intro n hn
    refine mem_normalizer_sSup (S := S') (g := n) fun T' hT' => ?_
    obtain ⟨T, hT, rfl⟩ := hT'
    exact UnbalancedLayer.pPrimeCore_le_normalizer hT.1.2 hn
  set Pb := (P.subgroupOf Y).map π with hPb
  have hPbE : Pb ≤ layer (↥Y ⧸ O) := by
    refine le_trans ?_ (LBalance.Quot.map_pLayer_eq_layer_quotient (H := ↥Y) (p := 2)).le
    refine map_mono fun y hy => ?_
    obtain ⟨z, hz, hzy⟩ := hPY (mem_subgroupOf.mp hy)
    rwa [← Subtype.ext hzy]
  have hPs : Group.IsPerfect ↥(P.subgroupOf Y) := by
    have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPY').symm.toMonoidHom)
      (subgroupOfEquivOfLe hPY').symm.surjective
  have hPbp : ⁅Pb, Pb⁆ = Pb := by
    have : Group.IsPerfect ↥Pb := Group.IsPerfect.map _
    exact Subgroup.isPerfect_iff.mp this
  have hPbD : Pb ≤ D'.map π := by
    refine (le_sSup_moved hPbp hPbE).trans (sSup_le fun Kc hKc => ?_)
    obtain ⟨hK0, hK0map, -, -⟩ := (CatalogueBPrimeJoin.canonical_prime_component_lift
      (X := ↥Y) 2).1 Kc hKc.1
    set K0 := CatalogueBPrimeJoin.canonicalPrimeLift 2 Kc
    set Kt := K0.map Y.subtype with hKt
    have hK0eq : Kt.subgroupOf Y = K0 := by
      rw [hKt, ← comap_subtype, comap_map_eq_self_of_injective Y.subtype_injective]
    have hKtY : IsTwoComponentIn Kt Y := ⟨map_subtype_le _, hK0eq ▸ hK0⟩
    have hmove : ¬ P ≤ coreActionKernel Kt := by
      intro hc
      apply hKc.2
      have h := map_le_centralizer_of_le_coreActionKernel hKtY hc
      rwa [hK0eq, hK0map] at h
    have hmem : Kt.subgroupOf Y ∈ S' := ⟨Kt, ⟨hKtY, hmove⟩, rfl⟩
    rw [← hK0map, ← hK0eq]
    exact map_mono (le_sSup hmem)
  have hPsup : P.subgroupOf Y ≤ D' ⊔ O := by
    have h1 : P.subgroupOf Y ≤ Pb.comap π := le_comap_map π _
    have h2 : Pb.comap π ≤ (D'.map π).comap π := comap_mono hPbD
    have h3 : (D'.map π).comap π = D' ⊔ O := by rw [comap_map_eq, hπ, QuotientGroup.ker_mk']
    exact h1.trans (h2.trans h3.le)
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hPD : P.subgroupOf Y ≤ D' := le_of_perfect_le_sup_of_odd hOodd hOD hPs hPsup
  intro p hp
  have h1 : (⟨p, hPY' hp⟩ : Y) ∈ D' := hPD (mem_subgroupOf.mpr hp)
  have h2 : D'.map Y.subtype ≤ sSup S := by
    refine map_le_iff_le_comap.mpr (sSup_le fun T' hT' => ?_)
    obtain ⟨T, hT, rfl⟩ := hT'
    rw [← map_le_iff_le_comap, map_subgroupOf_eq_of_le hT.1.1]
    exact le_sSup hT
  exact h2 (mem_map_of_mem Y.subtype h1)

end CFSG.ComponentClassification.SolMax
