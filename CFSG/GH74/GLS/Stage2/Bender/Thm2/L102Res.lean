module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import CFSG.FeitThompson.OddOrderTheorem

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L102

section Basic

variable {G : Type*} [Group G]

@[expose] def dres (B : Subgroup G) : Subgroup G := (CFSG.perfectResidual ↥B).map B.subtype

theorem dres_le (B : Subgroup G) : dres B ≤ B := Subgroup.map_subtype_le _

theorem le_dres_of_perfect {P B : Subgroup G} (hP : ⁅P, P⁆ = P) (hPB : P ≤ B) : P ≤ dres B :=
  CFSG.SignalizerFunctorTheorem.Nonsolvable.le_perfectResidual_map_of_isPerfect
    (Subgroup.isPerfect_iff.mpr hP) hPB

theorem normalizer_le_normalizer_dres (B : Subgroup G) :
    normalizer (B : Set G) ≤ normalizer ((dres B : Subgroup G) : Set G) :=
  CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map B

theorem exists_mem_inv_mul_mem {K Z : Subgroup G} (hZ : Z ≤ normalizer (K : Set G)) {w : G}
    (hw : w ∈ K ⊔ Z) : ∃ z ∈ Z, z⁻¹ * w ∈ K := by
  have h : w ∈ ((K ⊔ Z : Subgroup G) : Set G) := hw
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K Z hZ] at h
  obtain ⟨k, hk, z, hz, rfl⟩ := h
  refine ⟨z, hz, ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hZ hz)) k).mp hk
  simpa [mul_assoc] using this

theorem surjective_mk_comp_inclusion {K W Z : Subgroup G} [(K.subgroupOf W).Normal]
    (hZW : Z ≤ W) (hZK : Z ≤ normalizer (K : Set G)) (hWKZ : W ≤ K ⊔ Z) :
    Function.Surjective ((QuotientGroup.mk' (K.subgroupOf W)).comp (Subgroup.inclusion hZW)) := by
  intro c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨z, hz, hzk⟩ := exists_mem_inv_mul_mem hZK (hWKZ x.2)
  refine ⟨⟨z, hz⟩, ?_⟩
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq]
  exact Subgroup.mem_subgroupOf.mpr (by simpa using hzk)

theorem perfect_le_of_le_sup_solvable {P N Y : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hY : Group.IsSolvable ↥Y) (hYN : Y ≤ normalizer (N : Set G)) (hPNY : P ≤ N ⊔ Y) :
    P ≤ N := by
  have hWn : N ⊔ Y ≤ normalizer (N : Set G) := sup_le le_normalizer hYN
  have : (N.subgroupOf (N ⊔ Y)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hWn
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  have hsolv : Group.IsSolvable (↥(N ⊔ Y) ⧸ N.subgroupOf (N ⊔ Y)) :=
    Group.isSolvable_of_surjective (surjective_mk_comp_inclusion le_sup_right hYN le_rfl)
  let ψ : ↥P →* ↥(N ⊔ Y) ⧸ N.subgroupOf (N ⊔ Y) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hPNY)
  obtain ⟨k, hk⟩ := hsolv
  have h := map_derivedSeries_le_derivedSeries ψ k
  rw [Group.IsPerfect.derivedSeries_eq_top, hk] at h
  intro x hx
  have h1 : ψ ⟨x, hx⟩ = 1 := by
    have := h ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    simpa using this
  simp only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at h1
  rw [QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem odd_card_sup_of_normalizes {A B : Subgroup G} (hA : Odd (Nat.card A))
    (hB : Odd (Nat.card B)) (hAB : A ≤ normalizer (B : Set G)) :
    Odd (Nat.card (A ⊔ B : Subgroup G)) := by
  have hBS : B ≤ A ⊔ B := le_sup_right
  have hSn : A ⊔ B ≤ normalizer (B : Set G) := sup_le hAB le_normalizer
  have : (B.subgroupOf (A ⊔ B)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hSn
  have hsurj := surjective_mk_comp_inclusion (K := B) (W := A ⊔ B) (Z := A) le_sup_left hAB
    (by rw [sup_comm])
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf (A ⊔ B))
  have h2 : Nat.card (B.subgroupOf (A ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv
  have h3 := Subgroup.card_dvd_of_surjective hsurj
  rw [h1, h2]
  exact (hA.of_dvd_nat h3).mul hB

end Basic

section Perfect

variable {Γ : Type*} [Group Γ]

theorem eq_top_of_sup_center [Group.IsPerfect Γ] {A C : Subgroup Γ} (hAC : A ⊔ C = ⊤)
    (hC : C ≤ Subgroup.center Γ) : A = ⊤ := by
  have hCn : C.Normal := Subgroup.normal_of_le_center hC
  have hl : ∀ c ∈ C, ∀ g : Γ, ⁅c, g⁆ = 1 := fun c hc g =>
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (hC hc) g).symm
  have hr : ∀ c ∈ C, ∀ g : Γ, ⁅g, c⁆ = 1 := fun c hc g =>
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (hC hc) g)
  have h : ⁅(⊤ : Subgroup Γ), ⊤⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    have hx : x ∈ A ⊔ C := by rw [hAC]; exact Subgroup.mem_top x
    have hy : y ∈ A ⊔ C := by rw [hAC]; exact Subgroup.mem_top y
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨b, hb, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    have e1 : ⁅a * c, b * d⁆ = ⁅a, b * d⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hl c hc]; simp
    have e2 : ⁅a, b * d⁆ = ⁅a, b⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hr d hd]; simp
    rw [e1, e2, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hperf : ⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆ = (⊤ : Subgroup Γ) := by
    have := Group.IsPerfect.commutator_eq_top (G := Γ)
    rwa [commutator_def] at this
  rw [eq_top_iff]
  exact hperf ▸ h

theorem sup_eq_top_of_perfect_central [Group.IsPerfect Γ] {A C M : Subgroup Γ} [M.Normal]
    (hAC : A ⊔ C = ⊤) (hC : ∀ z ∈ C, ∀ y : Γ, ⁅z, y⁆ ∈ M) : A ⊔ M = ⊤ := by
  let q : Γ →* Γ ⧸ M := QuotientGroup.mk' M
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective M
  have : Group.IsPerfect (Γ ⧸ M) := Group.IsPerfect.ofSurjective hq
  have hsup : A.map q ⊔ C.map q = ⊤ := by
    rw [← Subgroup.map_sup, hAC, Subgroup.map_top]
    exact MonoidHom.range_eq_top_of_surjective q hq
  have hcen : C.map q ≤ Subgroup.center (Γ ⧸ M) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hq g
    have h1 : q ⁅z, y⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hC z hz y)
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hAtop : A.map q = ⊤ := eq_top_of_sup_center hsup hcen
  rw [eq_top_iff]
  intro x _
  have hx : q x ∈ A.map q := by rw [hAtop]; exact Subgroup.mem_top _
  obtain ⟨a, ha, haq⟩ := hx
  have h2 : a⁻¹ * x ∈ M := QuotientGroup.eq.mp haq
  have h3 : x = a * (a⁻¹ * x) := by group
  rw [h3]
  exact Subgroup.mul_mem_sup ha h2

end Perfect

section Central

variable {G : Type*} [Group G]

theorem le_sup_of_perfect_central {J P Z N : Subgroup G} (hJ : ⁅J, J⁆ = J) (hPJ : P ≤ J)
    (hZJ : Z ≤ J) (hJPZ : J ≤ P ⊔ Z) (hN : J ≤ normalizer (N : Set G))
    (hcent : ∀ z ∈ Z, ∀ y ∈ J, ⁅z, y⁆ ∈ N) : J ≤ P ⊔ N := by
  have hM : (N.subgroupOf J).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJ
  have hsup : P.subgroupOf J ⊔ Z.subgroupOf J = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPJ hZJ]
    exact Subgroup.subgroupOf_eq_top.mpr hJPZ
  have key : P.subgroupOf J ⊔ N.subgroupOf J = ⊤ :=
    sup_eq_top_of_perfect_central hsup (fun z hz y => by
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      have e : ((⁅z, y⁆ : ↥J) : G) = ⁅(z : G), (y : G)⁆ := map_commutatorElement J.subtype z y
      rw [e]
      exact hcent z hz y y.2)
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥J) ∈ P.subgroupOf J ⊔ N.subgroupOf J := by
    rw [key]; exact Subgroup.mem_top _
  obtain ⟨a, ha, m, hm, hxm⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  have hx2 : x = (a : G) * (m : G) := congrArg Subtype.val hxm.symm
  rw [hx2]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hm)

end Central

section Residual

variable {G : Type*} [Group G] [Finite G]

theorem dres_perfect (B : Subgroup G) : ⁅dres B, dres B⁆ = dres B :=
  Subgroup.isPerfect_iff.mp
    (CFSG.SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map B)

theorem perfect_le_of_le_sup_odd {P N Y : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hY : Odd (Nat.card Y)) (hYN : Y ≤ normalizer (N : Set G)) (hPNY : P ≤ N ⊔ Y) : P ≤ N :=
  perfect_le_of_le_sup_solvable hP (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hY) hYN hPNY

theorem map_perfectResidual_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (hf : Function.Surjective f) :
    (CFSG.perfectResidual A).map f = CFSG.perfectResidual B := by
  have := Finite.of_surjective f hf
  exact CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq f hf

theorem dres_le_sup_of_covering {W K Z : Subgroup G} (hZW : Z ≤ W) (_hKW : K ≤ W)
    (hW : W ≤ normalizer (K : Set G)) (hWKZ : W ≤ K ⊔ Z) : dres W ≤ dres Z ⊔ K := by
  have : (K.subgroupOf W).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hW
  let q : ↥W →* ↥W ⧸ K.subgroupOf W := QuotientGroup.mk' _
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hf : Function.Surjective (q.comp (Subgroup.inclusion hZW)) :=
    surjective_mk_comp_inclusion hZW (hZW.trans hW) hWKZ
  have h1 := map_perfectResidual_of_surjective q hq
  have h2 := map_perfectResidual_of_surjective _ hf
  intro x hx
  obtain ⟨x', hx', rfl⟩ := hx
  have hmem : q x' ∈ (CFSG.perfectResidual ↥Z).map (q.comp (Subgroup.inclusion hZW)) := by
    rw [h2, ← h1]
    exact Subgroup.mem_map_of_mem q hx'
  obtain ⟨z', hz', hz'q⟩ := hmem
  have h3 : (Subgroup.inclusion hZW z')⁻¹ * x' ∈ K.subgroupOf W :=
    QuotientGroup.eq.mp hz'q
  have h4 : (z' : G)⁻¹ * (x' : G) ∈ K := Subgroup.mem_subgroupOf.mp h3
  have h5 : (x' : G) = (z' : G) * ((z' : G)⁻¹ * (x' : G)) := by group
  show (x' : G) ∈ dres Z ⊔ K
  rw [h5]
  exact Subgroup.mul_mem_sup ⟨z', hz', rfl⟩ h4

theorem cover_dres {I K B : Subgroup G} (hI : ⁅I, I⁆ = I) (hKI : K ≤ I)
    (hKn : I ≤ normalizer (K : Set G)) (hBI : B ≤ I) (hcov : I ≤ B ⊔ K) : I ≤ dres B ⊔ K := by
  have h := dres_le_sup_of_covering hBI hKI hKn (by rwa [sup_comm] at hcov)
  exact (le_dres_of_perfect hI le_rfl).trans h

end Residual

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L102
