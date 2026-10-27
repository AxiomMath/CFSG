module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bZStar
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypes

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

theorem eq_one_of_mem_iSup_of_commute {G : Type*} [Group G] (F : Finset (Subgroup G))
    (hZ : ∀ A ∈ F, center ↥A = ⊥) (hc : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ⁅A, B⁆ = ⊥) {z : G}
    (hz : z ∈ ⨆ A ∈ F, A) (hzc : ∀ y ∈ ⨆ A ∈ F, A, z * y = y * z) : z = 1 := by
  classical
  induction F using Finset.induction_on generalizing z with
  | empty => simpa using hz
  | insert A F hA ih =>
    rw [Finset.iSup_insert] at hz hzc
    set N := ⨆ B ∈ F, B with hN
    have hNA : N ≤ centralizer (A : Set G) := by
      refine iSup₂_le fun B hB => ?_
      have hne : A ≠ B := fun h => hA (h ▸ hB)
      have := hc A (Finset.mem_insert_self A F) B (Finset.mem_insert_of_mem hB) hne
      rw [Subgroup.commutator_comm] at this
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp this
    have hAN : A ≤ centralizer (N : Set G) := Subgroup.le_centralizer_iff.mpr hNA
    have hzm : z ∈ (A : Set G) * (N : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A N
        (hAN.trans (centralizer_le_normalizer _))]
      exact hz
    obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.mp hzm
    have hwu : ∀ y ∈ A, w * y = y * w := fun y hy =>
      (mem_centralizer_iff.mp (hNA hw) y hy).symm
    have hu1 : u = 1 := by
      have hcen : (⟨u, hu⟩ : A) ∈ center ↥A := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        have h1 := hzc y (mem_sup_left y.2)
        have h2 := hwu y y.2
        simp only [coe_mul]
        calc (y : G) * u = (y * (u * w)) * w⁻¹ := by group
          _ = ((u * w) * y) * w⁻¹ := by rw [h1]
          _ = (u * (w * y)) * w⁻¹ := by group
          _ = (u * (y * w)) * w⁻¹ := by rw [h2]
          _ = u * y := by group
      rw [hZ A (Finset.mem_insert_self A F)] at hcen
      exact congrArg Subtype.val (mem_bot.mp hcen)
    subst hu1
    rw [one_mul]
    refine ih (fun B hB => hZ B (Finset.mem_insert_of_mem hB))
      (fun B hB C hC => hc B (Finset.mem_insert_of_mem hB) C (Finset.mem_insert_of_mem hC)) hw
      fun y hy => ?_
    have := hzc y (mem_sup_right hy)
    rwa [one_mul] at this

theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : center A = ⊥) : center B = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hcen : e.symm y ∈ center A := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.symm.surjective z
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hy w]
  rw [hA] at hcen
  have : e.symm y = e.symm 1 := by rw [map_one]; exact mem_bot.mp hcen
  exact mem_bot.mpr (e.symm.injective this)

variable {H : Type} [Group H]

theorem center_oddBar_conjugate {Y : Subgroup H} (hY : center (OddBar Y) = ⊥) (n : H) :
    center (OddBar (conjugate Y n)) = ⊥ :=
  center_eq_bot_of_mulEquiv (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
    (Y.equivMapOfInjective (MulAut.conj n⁻¹).toMonoidHom (MulAut.conj n⁻¹).injective)) hY

theorem mk_mem_center_quotient_iff {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {y : G} :
    (QuotientGroup.mk y : G ⧸ N) ∈ center (G ⧸ N) ↔ ∀ j : G, j⁻¹ * y⁻¹ * j * y ∈ N := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h j
    have h1 := h (QuotientGroup.mk j)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    have h2 := inv_mem h1
    convert h2 using 1
    group
  · intro h q
    induction q using QuotientGroup.induction_on with
    | H j =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have h2 := inv_mem (h j)
      convert h2 using 1
      group

theorem inf_coreActionKernel_le_of_center_eq_bot {Y : Subgroup H}
    (hY : center (OddBar Y) = ⊥) : Y ⊓ coreActionKernel Y ≤ (pPrimeCore 2 Y).map Y.subtype := by
  rw [← map_fusionZStar_eq]
  apply map_mono
  intro y hy
  have h1 : (QuotientGroup.mk y : ↥Y ⧸ Open.fusionOddCore ↥Y) ∈ center _ := hy
  rw [mk_mem_center_quotient_iff] at h1
  have h2 : (QuotientGroup.mk y : OddBar Y) ∈ center (OddBar Y) := by
    rw [mk_mem_center_quotient_iff]
    intro j
    rw [← fusionOddCore_eq_pPrimeCore]
    exact h1 j
  rw [hY] at h2
  have h3 := mem_bot.mp h2
  rwa [QuotientGroup.eq_one_iff] at h3

theorem isPComponent_conjugate_centralizer_singleton {a n : H} {L : Subgroup H}
    (hL : L ≤ centralizer ({a} : Set H))
    (hLp : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set H))))
    (hn : n ∈ centralizer ({a} : Set H)) :
    conjugate L n ≤ centralizer ({a} : Set H) ∧
      IsPComponent 2 ((conjugate L n).subgroupOf (centralizer ({a} : Set H))) := by
  set C := centralizer ({a} : Set H) with hC
  set φ : H ≃* H := MulAut.conj n⁻¹ with hφ
  have hCφ : C.map φ.toMonoidHom = C := by
    rw [hC, GSLit.map_centralizer_singleton]
    congr 2
    have hna := mem_centralizer_singleton_iff.mp hn
    rw [hφ, MulAut.conj_apply, inv_inv]
    calc n⁻¹ * a * n = n⁻¹ * (n * a) := by rw [mul_assoc, ← hna]
      _ = a := by group
  refine ⟨hCφ ▸ map_mono hL, ?_⟩
  let ψ : C ≃* C := (C.equivMapOfInjective φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr hCφ)
  have h := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 ψ hLp
  convert h using 1
  ext y
  constructor
  · intro hy
    obtain ⟨j, hj, hjy⟩ := mem_map.mp (mem_subgroupOf.mp hy)
    exact ⟨⟨j, hL hj⟩, mem_subgroupOf.mpr hj, Subtype.ext hjy⟩
  · rintro ⟨w, hw, rfl⟩
    exact mem_subgroupOf.mpr ⟨w, mem_subgroupOf.mp hw, rfl⟩

variable [Finite H]

theorem oddCore_le_of_isPComponent {X Y : Subgroup H} (hYX : Y ≤ X)
    (hY : IsPComponent 2 (Y.subgroupOf X)) :
    (pPrimeCore 2 Y).map Y.subtype ≤ (pPrimeCore 2 X).map X.subtype := by
  intro y hy
  have hyX : y ∈ X := hYX (map_subtype_le _ hy)
  have h1 := GSLit.map_pPrimeCore_subgroupOf_le hYX hY (show (⟨y, hyX⟩ : X) ∈
    ((pPrimeCore 2 Y).map Y.subtype).subgroupOf X from hy)
  exact ⟨⟨y, hyX⟩, h1, rfl⟩

theorem inf_oddCore_le {X Y : Subgroup H} (hYX : Y ≤ X) :
    Y ⊓ (pPrimeCore 2 X).map X.subtype ≤ (pPrimeCore 2 Y).map Y.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := (pPrimeCore 2 X).map X.subtype with hO
  have hnorm : (O.subgroupOf Y).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨o, ho, hoe⟩ := mem_map.mp hn
    have hg : ((g : H)) ∈ X := hYX g.2
    refine ⟨⟨g, hg⟩ * o * ⟨g, hg⟩⁻¹, (inferInstance : (pPrimeCore 2 X).Normal).conj_mem _ ho _,
      ?_⟩
    simp only [subtype_apply, coe_mul, coe_inv] at hoe ⊢
    rw [hoe]
  have hcop : Nat.Coprime 2 (Nat.card (O.subgroupOf Y)) := by
    have hc : Nat.Coprime 2 (Nat.card O) := by
      rw [hO, Subgroup.card_map_of_injective X.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have h1 : Nat.card ↥(O.subgroupOf Y) = Nat.card ↥(O ⊓ Y) := by
      rw [← Subgroup.card_map_of_injective Y.subtype_injective, subgroupOf_map_subtype]
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hc
  have hle : O.subgroupOf Y ≤ pPrimeCore 2 Y := le_sSup ⟨hnorm, hcop⟩
  intro y hy
  obtain ⟨hyY, hyO⟩ := mem_inf.mp hy
  exact ⟨⟨y, hyY⟩, hle (mem_subgroupOf.mpr hyO), rfl⟩

end CFSG.ComponentClassification.GSThmB
