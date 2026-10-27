module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxProj
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Steps
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

section Layer

variable {W : Type} [Group W] [Finite W]

theorem le_sSup_moved {P : Subgroup W} (hP : ⁅P, P⁆ = P) (hPE : P ≤ layer W) :
    P ≤ sSup {K : Subgroup W | IsComponent K ∧ ¬ P ≤ centralizer (K : Set W)} := by
  classical
  set D := sSup {K : Subgroup W | IsComponent K ∧ ¬ P ≤ centralizer (K : Set W)} with hD
  set C := sSup {K : Subgroup W | IsComponent K ∧ P ≤ centralizer (K : Set W)} with hC
  have hEDC : layer W = D ⊔ C := by
    rw [hD, hC, ← sSup_union]
    simp only [CFSG.layer.eq_sSup]
    congr 1
    refine Set.ext fun K => ⟨fun hK => ?_, fun hK => ?_⟩
    · by_cases h : P ≤ centralizer (K : Set W)
      · exact Or.inr ⟨hK, h⟩
      · exact Or.inl ⟨hK, h⟩
    · rcases hK with hK | hK
      · exact hK.1
      · exact hK.1
  have hEn : layer W ≤ normalizer (D : Set W) := by
    intro e he
    have h := mem_normalizer_sSup
      (S := {K : Subgroup W | IsComponent K ∧ ¬ P ≤ centralizer (K : Set W)}) (g := e)
      (fun K hK => layer_le_normalizer hK.1 he)
    exact h
  have hCP : C ≤ centralizer (P : Set W) := by
    refine sSup_le fun K hK => ?_
    exact le_centralizer_iff.mp hK.2
  have hCn : C ≤ normalizer (D : Set W) := (le_sup_right.trans hEDC.symm.le).trans hEn
  rw [← hP, commutator_le]
  intro p₁ hp₁ p₂ hp₂
  have hp₁' : p₁ ∈ D ⊔ C := hEDC ▸ hPE hp₁
  obtain ⟨d, hd, c, hc, rfl⟩ := Sol76.exists_mul_of_mem_sup_normalizer hCn hp₁'
  have hcp : c * p₂ = p₂ * c := ((mem_centralizer_iff.mp (hCP hc)) p₂ hp₂).symm
  have e : ⁅d * c, p₂⁆ = d * (p₂ * d⁻¹ * p₂⁻¹) := by
    rw [commutatorElement_def]
    calc d * c * p₂ * (d * c)⁻¹ * p₂⁻¹ = d * (c * p₂) * c⁻¹ * d⁻¹ * p₂⁻¹ := by group
      _ = d * (p₂ * c) * c⁻¹ * d⁻¹ * p₂⁻¹ := by rw [hcp]
      _ = d * (p₂ * d⁻¹ * p₂⁻¹) := by group
  rw [e]
  refine mul_mem hd ?_
  have h := (mem_normalizer_iff.mp (hEn (hPE hp₂)) d⁻¹).mp (inv_mem hd)
  exact h

end Layer

section Moved

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_oddCoreIn_of_odd {P N : Subgroup G} (hNP : N ≤ P) (hNn : P ≤ normalizer (N : Set G))
    (hN : Odd (Nat.card N)) : N ≤ oddCoreIn P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (N.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hNP).mpr hNn
  have hc : Nat.Coprime 2 (Nat.card (N.subgroupOf P)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hNP).toEquiv]
    exact Nat.coprime_two_left.mpr hN
  have h : N.subgroupOf P ≤ pPrimeCore 2 ↥P := le_sSup ⟨hn, hc⟩
  intro x hx
  exact ⟨⟨x, hNP hx⟩, h (mem_subgroupOf.mpr hx), rfl⟩

theorem commutator_mem_oddCoreIn_of_le {Y M J : Subgroup G} (hM : IsTwoComponentIn M Y)
    (hJ : J ≤ coreActionKernel M) {j m : G} (hj : j ∈ J) (hm : m ∈ M) :
    m⁻¹ * j⁻¹ * m * j ∈ oddCoreIn Y :=
  oddCoreIn_le_of_isTwoComponentIn hM ((hJ hj).2 m hm)

theorem exists_moved_both {Y P J : Subgroup G} (hPY : P ≤ twoLayerIn Y) (hJY : J ≤ twoLayerIn Y)
    (hP : ⁅P, P⁆ = P) (hJP : J ≤ normalizer (P : Set G)) (hmove : ¬ J ≤ coreActionKernel P) :
    ∃ M : Subgroup G, IsTwoComponentIn M Y ∧ ¬ J ≤ coreActionKernel M ∧
      ¬ P ≤ coreActionKernel M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hPY' : P ≤ Y := hPY.trans (map_subtype_le _)
  have hJY' : J ≤ Y := hJY.trans (map_subtype_le _)
  set O := pPrimeCore 2 ↥Y with hO
  set π := QuotientGroup.mk' O with hπ
  set Pb := (P.subgroupOf Y).map π with hPb
  set Jb := (J.subgroupOf Y).map π with hJb
  have hlayer : ∀ {R : Subgroup G}, R ≤ twoLayerIn Y → (R.subgroupOf Y).map π ≤ layer (↥Y ⧸ O) :=
    by
    intro R hR
    refine le_trans ?_ (LBalance.Quot.map_pLayer_eq_layer_quotient (H := ↥Y) (p := 2)).le
    refine map_mono fun y hy => ?_
    obtain ⟨z, hz, hzy⟩ := hR (mem_subgroupOf.mp hy)
    rwa [← Subtype.ext hzy]
  have hPbE := hlayer hPY
  have hJbE := hlayer hJY
  have hPbp : ⁅Pb, Pb⁆ = Pb := by
    have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
    have hPs : Group.IsPerfect ↥(P.subgroupOf Y) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPY').symm.toMonoidHom)
        (subgroupOfEquivOfLe hPY').symm.surjective
    have : Group.IsPerfect ↥Pb := Group.IsPerfect.map _
    exact Subgroup.isPerfect_iff.mp this
  have hcomp : ∀ Kc : Subgroup (↥Y ⧸ O), IsComponent Kc →
      ¬ Pb ≤ centralizer (Kc : Set (↥Y ⧸ O)) → Jb ≤ centralizer (Kc : Set (↥Y ⧸ O)) := by
    intro Kc hKc hPK
    obtain ⟨hK0, hK0map, -, -⟩ := (CatalogueBPrimeJoin.canonical_prime_component_lift
      (X := ↥Y) 2).1 Kc hKc
    set K0 := CatalogueBPrimeJoin.canonicalPrimeLift 2 Kc
    set Kt := K0.map Y.subtype with hKt
    have hKtY : IsTwoComponentIn Kt Y := by
      refine ⟨map_subtype_le _, ?_⟩
      rw [hKt, ← comap_subtype, comap_map_eq_self_of_injective Y.subtype_injective]
      exact hK0
    have hcen : ∀ {R : Subgroup G}, R ≤ Y → R ≤ coreActionKernel Kt →
        (R.subgroupOf Y).map π ≤ centralizer (Kc : Set (↥Y ⧸ O)) := by
      intro R hRY hR
      rintro _ ⟨r, hr, rfl⟩
      rw [mem_centralizer_iff]
      intro x hx
      rw [SetLike.mem_coe, ← hK0map] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have h1 := commutator_mem_oddCoreIn_of_le hKtY hR (mem_subgroupOf.mp hr)
        (mem_map_of_mem Y.subtype hk)
      obtain ⟨o, ho, hoe⟩ := h1
      have h3 : o = k⁻¹ * r⁻¹ * k * r := Subtype.ext (by simpa using hoe)
      rw [h3] at ho
      rw [← map_mul, ← map_mul]
      refine (QuotientGroup.eq (s := O)).mpr ?_
      have e : (k * r)⁻¹ * (r * k) = (k⁻¹ * r⁻¹ * k * r)⁻¹ := by group
      rw [e]
      exact inv_mem ho
    by_cases hJK : J ≤ coreActionKernel Kt
    · exact hcen hJY' hJK
    · exact absurd (hcen hPY' (hcon Kt hKtY hJK)) hPK
  have hPJ : Pb ≤ centralizer (Jb : Set (↥Y ⧸ O)) := by
    refine (le_sSup_moved hPbp hPbE).trans (sSup_le fun Kc hKc => ?_)
    exact le_centralizer_iff.mp (hcomp Kc hKc.1 hKc.2)
  apply hmove
  intro j hj
  refine ⟨hJP hj, fun p hp => ?_⟩
  have hc : p⁻¹ * j⁻¹ * p * j ∈ P := by
    have h1 : j⁻¹ * p * j ∈ P := by
      have := (mem_normalizer_iff.mp (hJP (inv_mem hj)) p).mp hp
      simpa using this
    have h2 : p⁻¹ * (j⁻¹ * p * j) ∈ P := mul_mem (inv_mem hp) h1
    simpa [mul_assoc] using h2
  have hcO : p⁻¹ * j⁻¹ * p * j ∈ oddCoreIn Y := by
    have hcomm : π ⟨p, hPY' hp⟩ * π ⟨j, hJY' hj⟩ = π ⟨j, hJY' hj⟩ * π ⟨p, hPY' hp⟩ :=
      ((mem_centralizer_iff.mp (hPJ (mem_map_of_mem π (mem_subgroupOf.mpr hp))))
        _ (mem_map_of_mem π (mem_subgroupOf.mpr hj))).symm
    have hcY : p⁻¹ * j⁻¹ * p * j ∈ Y := hPY' hc
    have e : (⟨p⁻¹ * j⁻¹ * p * j, hcY⟩ : ↥Y) =
        (⟨p, hPY' hp⟩ : ↥Y)⁻¹ * (⟨j, hJY' hj⟩ : ↥Y)⁻¹ * ⟨p, hPY' hp⟩ * ⟨j, hJY' hj⟩ := rfl
    have h1 : π (⟨p⁻¹ * j⁻¹ * p * j, hcY⟩ : ↥Y) = 1 := by
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
      calc (π ⟨p, hPY' hp⟩)⁻¹ * (π ⟨j, hJY' hj⟩)⁻¹ * π ⟨p, hPY' hp⟩ * π ⟨j, hJY' hj⟩
          = (π ⟨p, hPY' hp⟩)⁻¹ * (π ⟨j, hJY' hj⟩)⁻¹ *
              (π ⟨p, hPY' hp⟩ * π ⟨j, hJY' hj⟩) := by group
        _ = (π ⟨p, hPY' hp⟩)⁻¹ * (π ⟨j, hJY' hj⟩)⁻¹ *
              (π ⟨j, hJY' hj⟩ * π ⟨p, hPY' hp⟩) := by rw [hcomm]
        _ = 1 := by group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, rfl⟩
  have hodd : Odd (Nat.card (P ⊓ oddCoreIn Y : Subgroup G)) := by
    have h1 : Odd (Nat.card (oddCoreIn Y)) := by
      rw [oddCoreIn, Nat.card_congr ((pPrimeCore 2 ↥Y).equivMapOfInjective _
        Y.subtype_injective).symm.toEquiv]
      exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥Y))
    exact h1.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hn : P ≤ normalizer ((P ⊓ oddCoreIn Y : Subgroup G) : Set G) := by
    refine fun q hq => mem_normalizer_inf (le_normalizer hq) ?_
    exact Sol76.le_normalizer_oddCoreIn Y (hPY' hq)
  exact le_oddCoreIn_of_odd inf_le_left hn hodd (mem_inf.mpr ⟨hc, hcO⟩)

end Moved

end CFSG.ComponentClassification.SolMax
