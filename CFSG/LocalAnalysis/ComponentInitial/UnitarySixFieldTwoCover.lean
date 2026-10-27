module

public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoLevi
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCover

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace UnitarySixFieldTwo

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension
open scoped commutatorElement Pointwise

variable {F : Type} [Field F] [CharP F 2] {h : UnitaryFieldData 2 1 F} {E : Type*} [Group E]
  {θ : E →* hypPSU h 3 0}

theorem kernel_sq_eq_one [Finite E] [Group.IsPerfect E] (hθ : Function.Surjective θ)
    (hC : θ.ker ≤ Subgroup.center E) (h4 : ∀ c, θ c = 1 → c ^ 4 = 1) {c : E} (hc : θ c = 1) :
    c ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.finite
  set ρ : SpecialLinearGroup (Fin 3) F →* hypPSU h 3 0 := (hypProj h 3 0).comp (lHom h) with hρ
  set R := ρ.range with hR
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  have : Group.IsPerfect R := Group.IsPerfect.range _
  set H := R.comap θ with hH
  set F₀ := ⁅H, H⁆ with hF₀
  have hFR : F₀.map θ = R := by
    rw [hF₀, Subgroup.map_commutator, hH, Subgroup.map_comap_eq_self_of_surjective hθ,
      Subgroup.commutator_eq_self]
  have hFH : F₀ ≤ H := Subgroup.commutator_le_self H
  have hHF : H ≤ F₀ ⊔ θ.ker := by
    intro x hx
    have hxR : θ x ∈ F₀.map θ := by rw [hFR]; exact hx
    obtain ⟨f, hf, hfx⟩ := hxR
    have hk : f⁻¹ * x ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfx, inv_mul_cancel]
    have := Subgroup.mul_mem_sup hf hk
    rwa [mul_inv_cancel_left] at this
  have hFF : ⁅F₀, F₀⁆ = F₀ := le_antisymm (Subgroup.commutator_le_self F₀)
    ((Subgroup.commutator_mono hHF hHF).trans (BinarySymplecticSix.commutator_sup_le hC))
  have : Group.IsPerfect F₀ := Subgroup.isPerfect_iff.mpr hFF
  set θF : F₀ →* R := (θ.comp F₀.subtype).codRestrict R fun f => hFH f.2 with hθF
  have hθFsurj : Function.Surjective θF := by
    rintro ⟨r, hr⟩
    rw [← hFR] at hr
    obtain ⟨f, hf, hfr⟩ := hr
    exact ⟨⟨f, hf⟩, Subtype.ext hfr⟩
  have hθFker : ∀ f : F₀, θF f = 1 ↔ θ f = 1 := fun f =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hθFcen : θF.ker ≤ Subgroup.center F₀ := fun f hf => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hθFker f).mp hf)) g)
  have hθF2 : IsPGroup 2 θF.ker := fun k => ⟨2, Subtype.ext (Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact h4 _ ((hθFker k).mp k.2)))⟩
  obtain ⟨PUT, hPUT⟩ := LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  set UR : Sylow 2 R := PUT.mapSurjective ρ.rangeRestrict_surjective with hUR
  have hURle : (UR : Subgroup R) ≤ θF.range := by
    rw [MonoidHom.range_eq_top_of_surjective θF hθFsurj]
    exact le_top
  set T : Sylow 2 F₀ := UR.comapOfKerIsPGroup θF hθF2 hURle with hT
  have htrans : θF.ker ≤ ⁅(T : Subgroup F₀), (T : Subgroup F₀)⁆ := by
    have h := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived T θF.ker hθFcen hθF2
    rwa [Subgroup.map_subtype_commutator] at h
  have hTle : (T : Subgroup F₀).map F₀.subtype ≤ utPre θ := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    rw [hT, Sylow.coe_comapOfKerIsPGroup, Subgroup.mem_comap, hUR, Sylow.coe_mapSurjective, hPUT,
      Subgroup.mem_map] at ht
    obtain ⟨A, hA, hAt⟩ := ht
    exact mem_utPre.mpr ⟨A, hA, (congrArg Subtype.val hAt).symm⟩
  have hFC₀ : ∀ f ∈ F₀, θ f = 1 → f ^ 2 = 1 := by
    intro f hf hθf
    have hk : (⟨f, hf⟩ : F₀) ∈ θF.ker := (hθFker _).mpr hθf
    have h2 : f ∈ ⁅(T : Subgroup F₀).map F₀.subtype, (T : Subgroup F₀).map F₀.subtype⁆ := by
      rw [← Subgroup.map_commutator]
      exact ⟨⟨f, hf⟩, htrans hk, rfl⟩
    exact sq_eq_one_of_mem_commutator_utPre hθ hC (Subgroup.commutator_mono hTle hTle h2)
  let M₀ : Subgroup E :=
    { carrier := {x | (∃ B : Matrix (Fin 3) (Fin 3) F, IsLift θ (nMat B) x) ∧ x ^ 2 = 1}
      mul_mem' := by
        rintro x y ⟨⟨B, hx⟩, hx2⟩ ⟨⟨B', hy⟩, hy2⟩
        exact ⟨⟨B + B', by rw [← nMat_mul]; exact hx.mul hy⟩,
          by rw [(commute_of_isLift_nMat hθ hC hx hy).mul_pow, hx2, hy2, mul_one]⟩
      one_mem' := ⟨⟨0, by rw [nMat_zero]; exact isLift_one_iff.mpr (map_one θ)⟩, one_pow 2⟩
      inv_mem' := by
        rintro x ⟨⟨B, hx⟩, hx2⟩
        exact ⟨⟨-B, hx.inv (by rw [nMat_mul, add_neg_cancel, nMat_zero])⟩,
          by rw [inv_pow, hx2, inv_one]⟩ }
  have hM₀ : ∀ x, x ∈ M₀ ↔ (∃ B : Matrix (Fin 3) (Fin 3) F, IsLift θ (nMat B) x) ∧ x ^ 2 = 1 :=
    fun _ => Iff.rfl
  have hconjM₀ : ∀ u ∈ utPre θ, ∀ x ∈ M₀, u * x * u⁻¹ ∈ M₀ := by
    intro u hu x hx
    obtain ⟨⟨B, hxB⟩, hx2⟩ := (hM₀ x).mp hx
    obtain ⟨A, -, hAu⟩ := mem_utPre.mp hu
    exact (hM₀ _).mpr ⟨⟨_, (isLift_lMat_iff.mpr hAu).conj_nMat hxB⟩,
      by rw [conj_pow, hx2, mul_one, mul_inv_cancel]⟩
  set Ũ := utPre θ ⊓ F₀ with hŨ
  have hŨN : Ũ ≤ Subgroup.normalizer (M₀ : Set E) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconjM₀ u (Subgroup.mem_inf.mp hu).1 x hx, fun hx => ?_⟩
    have := hconjM₀ u⁻¹ (inv_mem (Subgroup.mem_inf.mp hu).1) _ hx
    rwa [inv_inv, show u⁻¹ * (u * x * u⁻¹) * u = x by group] at this
  set P₀ := Ũ ⊔ M₀ with hP₀
  have hP₀mul : (P₀ : Set E) = (Ũ : Set E) * (M₀ : Set E) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Ũ M₀ hŨN
  have hP₀ker : ∀ p ∈ P₀, θ p = 1 → p ^ 2 = 1 := by
    intro p hp hθp
    rw [← SetLike.mem_coe, hP₀mul, Set.mem_mul] at hp
    obtain ⟨u, hu, m, hm, rfl⟩ := hp
    obtain ⟨A, hA, hAu⟩ := mem_utPre.mp (Subgroup.mem_inf.mp hu).1
    obtain ⟨⟨B, hmB⟩, hm2⟩ := (hM₀ m).mp hm
    have hB := hmB.hconj_eq
    have hθm := hmB.map_eq (coe_nElt h hB)
    rw [map_mul, hAu, hθm, ← map_mul] at hθp
    obtain ⟨rfl, rfl⟩ := eq_one_of_hypProj_lHom_mul_nElt h hA hB hθp
    have hθu : θ u = 1 := by rw [hAu, map_one, map_one]
    have hθm' : θ m = 1 := by
      rw [nMat_zero] at hmB
      exact isLift_one_iff.mp hmB
    rw [(show Commute u m from Subgroup.mem_center_iff.mp (hC hθm') u).mul_pow,
      hFC₀ u (Subgroup.mem_inf.mp hu).2 hθu, hm2, mul_one]
  have hP₀surj : ∀ g ∈ hypUnitriangular h 3 0, ∃ p ∈ P₀, θ p = hypProj h 3 0 g := by
    intro g hg
    obtain ⟨A, hA, B, hB, hgAB⟩ := exists_lMat_mul_nMat_of_mem h hg
    have hg' : g = lHom h A * nElt h hB :=
      Subtype.ext (Units.ext (by rw [hgAB]; rfl))
    have hAR : hypProj h 3 0 (lHom h A) ∈ F₀.map θ := by rw [hFR]; exact ⟨A, rfl⟩
    obtain ⟨u, hu, hθu⟩ := hAR
    obtain ⟨x, hx⟩ := exists_isLift_nMat hθ hB
    obtain ⟨k, hk, hxk⟩ := exists_sq_eq_of_isLift_nMat hθ hC hx
    have hxk' : Commute x k := Subgroup.mem_center_iff.mp (hC hk) x
    have hm : x * k⁻¹ ∈ M₀ := (hM₀ _).mpr ⟨⟨B, hx.mul_ker (by rw [map_inv, hk, inv_one])⟩, by
      rw [hxk'.inv_right.mul_pow, hxk, inv_pow, mul_inv_cancel]⟩
    refine ⟨u * (x * k⁻¹), Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨mem_utPre.mpr ⟨A, hA, hθu⟩, hu⟩))
      (Subgroup.mem_sup_right hm), ?_⟩
    rw [map_mul, hθu, map_mul, map_inv, hk, inv_one, mul_one, hx.map_eq (coe_nElt h hB), hg',
      map_mul]
  obtain ⟨-, -, -, -, ⟨PU, hPU⟩, -, -⟩ :=
    unitary_order_and_Sylow h (r := 3) (ε := 0) (by norm_num) (by norm_num)
  have hkerP : IsPGroup 2 θ.ker := fun k => ⟨2, Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact h4 _ k.2)⟩
  have hrange : (PU : Subgroup (hypPSU h 3 0)) ≤ θ.range := by
    rw [MonoidHom.range_eq_top_of_surjective θ hθ]
    exact le_top
  set P₂ := PU.comapOfKerIsPGroup θ hkerP hrange with hP₂def
  have hP₂ : (P₂ : Subgroup E) = (hypProjUnitriangular h 3 0).comap θ := by
    rw [hP₂def, Sylow.coe_comapOfKerIsPGroup, hPU]
  have htransE : θ.ker ≤ ⁅(P₂ : Subgroup E), (P₂ : Subgroup E)⁆ := by
    have h := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived P₂ θ.ker hC hkerP
    rwa [Subgroup.map_subtype_commutator] at h
  have hP₂P₀ : (P₂ : Subgroup E) ≤ P₀ ⊔ θ.ker := by
    intro x hx
    rw [hP₂, Subgroup.mem_comap] at hx
    obtain ⟨g, hg, hgx⟩ := hx
    obtain ⟨p, hp, hpx⟩ := hP₀surj g hg
    have hk : p⁻¹ * x ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpx, ← hgx]
      exact inv_mul_cancel _
    have := Subgroup.mul_mem_sup hp hk
    rwa [mul_inv_cancel_left] at this
  have hcP₀ : c ∈ P₀ :=
    Subgroup.commutator_le_self P₀ ((BinarySymplecticSix.commutator_sup_le hC)
      (Subgroup.commutator_mono hP₂P₀ hP₂P₀ (htransE hc)))
  exact hP₀ker c hcP₀ hc


theorem forall_sq_eq_pow_four {P : Type*} [Group P] [Finite P] [Group.IsPerfect P]
    (η : P →* hypPSU h 3 0) (hη : Function.Surjective η) (hK : η.ker ≤ Subgroup.center P) :
    ∀ x ∈ η.ker, ∃ y ∈ η.ker, x ^ 2 = y ^ 4 := by
  set D := BinarySymplecticSix.powers hK 4 with hD
  have : D.Normal := Subgroup.normal_of_le_center ((BinarySymplecticSix.powers_le hK 4).trans hK)
  have hDle : D ≤ η.ker := BinarySymplecticSix.powers_le hK 4
  set θ' := QuotientGroup.lift D η hDle with hθ'
  have hθsurj : Function.Surjective θ' := by
    intro x
    obtain ⟨y, rfl⟩ := hη x
    exact ⟨y, QuotientGroup.lift_mk _ _ _⟩
  have hθmk : ∀ y : P, θ' (y : P ⧸ D) = η y := fun y => QuotientGroup.lift_mk _ _ _
  have hθC : θ'.ker ≤ Subgroup.center (P ⧸ D) := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H y =>
      rw [MonoidHom.mem_ker, hθmk] at hc
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hK hc) g]
  have h4 : ∀ c, θ' c = 1 → c ^ 4 = 1 := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H y =>
      rw [hθmk] at hc
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨y, hc, rfl⟩
  intro x hx
  have hsq := kernel_sq_eq_one hθsurj hθC h4 (c := (x : P ⧸ D)) (by rw [hθmk]; exact hx)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hsq
  exact hsq

theorem kernel_sq_eq_one_of_isPGroup {P : Type*} [Group P] [Finite P] [Group.IsPerfect P]
    (η : P →* hypPSU h 3 0) (hη : Function.Surjective η) (hK : η.ker ≤ Subgroup.center P)
    (h2 : IsPGroup 2 η.ker) : ∀ x ∈ η.ker, x ^ 2 = 1 :=
  BinarySymplecticSix.sq_eq_one_of_forall_sq_eq_pow_four hK h2 (forall_sq_eq_pow_four η hη hK)

end UnitarySixFieldTwo

open UnitarySixFieldTwo CFSG.ClassicalGroups.UnitaryFlag

theorem unitary_six_field_two_perfect_central_two_kernel_elementary {P : Type*} {Q : Type}
    [Group P] [Group Q] [Finite P] [Group.IsPerfect P] (η : P →* Q)
    (hη : Function.Surjective η) (hK : η.ker ≤ Subgroup.center P) (h2 : IsPGroup 2 η.ker)
    (hQ : CFSG.Blueprint.LieModel Q .PSU 6 2 1) : CFSG.IsElementaryAbelian 2 η.ker := by
  have hsq : ∀ x ∈ η.ker, x ^ 2 = 1 := by
    rcases hQ with ⟨-, -, K, _, _, hcard, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hcard]; norm_num⟩
      have := h.charP
      obtain ⟨R, hR⟩ := exists_isHypTransport (r := 3) (ε := 0) h
      let f : hypPSU h 3 0 ≃* Q := (hypPSUEquivStatedProj h hR (by norm_num)).trans e.symm
      set η' : P →* hypPSU h 3 0 := f.symm.toMonoidHom.comp η with hη'
      have hker : η'.ker = η.ker := by
        ext z
        exact f.symm.map_eq_one_iff
      have := kernel_sq_eq_one_of_isPGroup η' (f.symm.surjective.comp hη) (hker ▸ hK)
        (hker ▸ h2)
      rwa [hker] at this
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  exact { is_comm := ⟨fun u v => Subtype.ext (Subgroup.mem_center_iff.mp (hK v.2) u)⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
            Subtype.ext (by simpa using hsq x x.2) }

end CFSG.LocalAnalysis.ComponentInitial
