module

public import CFSG.LargeExtraspecial.S12InspFamDFi
public import CFSG.LargeExtraspecial.S12InspFamOMinus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap Matrix CFSG.RankThree.OrthogonalInvolutions
open CFSG.Fischer.Classification CFSG.Fischer.Classification.Recognition.SymO
  CFSG.ClassicalGroups.Orthogonal

namespace S12InspO

theorem nonempty_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) (a : A) :
    Nonempty (centralizer ({a} : Set A) ≃* centralizer ({ψ a} : Set B)) := by
  have h : (centralizer ({a} : Set A)).map ψ.toMonoidHom = centralizer ({ψ a} : Set B) := by
    ext b
    rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hb
      have := congrArg ψ hb
      simpa using this
    · intro hb
      apply ψ.injective
      simpa using hb
  exact ⟨(ψ.subgroupMap _).trans (MulEquiv.subgroupCongr h)⟩

theorem nonempty_commutator_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nonempty (commutator A ≃* commutator B) := by
  have h : (commutator A).map e.toMonoidHom = commutator B := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  exact ⟨(e.subgroupMap _).trans (MulEquiv.subgroupCongr h)⟩

theorem mul_comm_of_eq_one_or_eq {A : Type*} [Group A] {a : A} {k : centralizer ({a} : Set A)}
    (h : (k : A) = 1 ∨ (k : A) = a) (x : centralizer ({a} : Set A)) : k * x = x * k := by
  rcases h with h | h
  · rw [show k = 1 from Subtype.ext (h.trans (OneMemClass.coe_one _).symm), one_mul, mul_one]
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, h]
    exact (mem_centralizer_singleton_iff.mp x.2).symm

theorem exists_commutator_hom {C P : Type*} [Group C] [Group P] (ρ : C →* P) {A : Subgroup P}
    (hA : (commutator C).map ρ = A) (hker : ∀ k ∈ ρ.ker, ∀ x, k * x = x * k) :
    ∃ ρ' : commutator C →* A, Function.Surjective ρ' ∧ ∀ k ∈ ρ'.ker, ∀ x, k * x = x * k := by
  have hmem : ∀ x : commutator C, (ρ.comp (commutator C).subtype) x ∈ A := fun x => by
    have h := Subgroup.mem_map_of_mem ρ x.2
    rw [hA] at h
    exact h
  refine ⟨(ρ.comp (commutator C).subtype).codRestrict A hmem, ?_, fun k hk x => ?_⟩
  · rintro ⟨a, ha⟩
    rw [← hA] at ha
    obtain ⟨c, hc, rfl⟩ := ha
    exact ⟨⟨c, hc⟩, rfl⟩
  · have hk' : (k : C) ∈ ρ.ker := MonoidHom.mem_ker.mpr (congrArg Subtype.val
      (MonoidHom.mem_ker.mp hk))
    exact Subtype.ext (hker _ hk' x)

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem isSimpleGroup_alternatingGroup_six : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)

theorem not_isSolvable_alternatingGroup_six : ¬ Group.IsSolvable (alternatingGroup (Fin 6)) := by
  have := isSimpleGroup_alternatingGroup_six
  refine s12_not_isSolvable_of_simple ?_
  rw [card_alternatingGroup_six]
  norm_num

theorem commutator_alternatingGroup_six :
    ⁅alternatingGroup (Fin 6), alternatingGroup (Fin 6)⁆ = alternatingGroup (Fin 6) := by
  have := isSimpleGroup_alternatingGroup_six
  have h := congrArg (Subgroup.map (alternatingGroup (Fin 6)).subtype)
    (s12_commutator_eq_top_of_simple not_isSolvable_alternatingGroup_six)
  rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    range_subtype] at h

theorem commutator_eq_alternatingGroup_six {R : Subgroup (Equiv.Perm (Fin 6))}
    (hR : alternatingGroup (Fin 6) ≤ R) : ⁅R, R⁆ = alternatingGroup (Fin 6) := by
  have h6 : 5 ≤ Nat.card (Fin 6) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  apply le_antisymm
  · rw [← alternatingGroup.commutator_perm_eq h6, _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · calc alternatingGroup (Fin 6) = ⁅alternatingGroup (Fin 6), alternatingGroup (Fin 6)⁆ :=
          commutator_alternatingGroup_six.symm
      _ ≤ ⁅R, R⁆ := Subgroup.commutator_mono hR hR

theorem nonempty_isometryGroup_mulEquiv_perm_six {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] (B : LinearMap.BilinForm (ZMod 2) W)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (hdim : finrank (ZMod 2) W = 4) :
    Nonempty (TauCeti.BilinForm.isometryGroup B ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨k, b, hk, hb⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis B hB hnd
  obtain rfl : k = 2 := by omega
  exact ⟨(CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryMatrixEquiv b B
    hb).trans (((CFSG.Timmesfeld.Transvection.QTwo.glFourEquiv.subgroupMap
      CFSG.ComponentClassification.PresentationLocal.sympFour).trans
      (MulEquiv.subgroupCongr CFSG.Timmesfeld.Transvection.QTwo.map_sympFour)).symm.trans
      (MulEquiv.ofBijective CFSG.ComponentClassification.PresentationLocal.omegaPerm
        ⟨CFSG.ComponentClassification.PresentationLocal.omegaPerm_injective,
          CFSG.ComponentClassification.PresentationLocal.omegaPerm_surjective⟩))⟩

theorem not_prime_card_sp {k : ℕ} (hk : 1 ≤ k) :
    ¬ (2 ^ (k ^ 2) * ∏ j ∈ Finset.Icc 1 k, (2 ^ (2 * j) - 1)).Prime := fun hp => by
  have h2 : 2 ∣ 2 ^ (k ^ 2) * ∏ j ∈ Finset.Icc 1 k, (2 ^ (2 * j) - 1) :=
    Dvd.dvd.mul_right (dvd_pow_self 2 (pow_ne_zero 2 (by omega))) _
  have h3 : 3 ∣ 2 ^ (k ^ 2) * ∏ j ∈ Finset.Icc 1 k, (2 ^ (2 * j) - 1) := by
    have h := Finset.dvd_prod_of_mem (fun j => 2 ^ (2 * j) - 1)
      (Finset.mem_Icc.mpr ⟨le_refl 1, hk⟩)
    norm_num at h
    exact Dvd.dvd.mul_left h _
  have e2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
  have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
  omega

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem rho_ker_eq (hnd : (polarBilin Q).Nondegenerate) {v y : V} (hv : Q v = 1)
    (hyv : polar Q y v = 1) (t : TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht : ∀ x, (t : V ≃ₗ[ZMod 2] V) x = x + polar Q x v • v)
    {c : centralizer ({t} : Set (TauCeti.QuadraticMap.orthogonalGroup Q))}
    (hc : c ∈ (rho hnd hv hyv t ht).ker) :
    (c : TauCeti.QuadraticMap.orthogonalGroup Q) = 1 ∨
      (c : TauCeti.QuadraticMap.orthogonalGroup Q) = t := by
  set g : V ≃ₗ[ZMod 2] V := ((c : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V)
    with hgdef
  have hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (c : TauCeti.QuadraticMap.orthogonalGroup Q).2
  have hgv : g v = v := apply_eq_self_of_mem_centralizer hnd hv t ht c.2
  have h1 : ∀ w, restr hyv g w = w := by
    intro w
    rw [← rho_apply hnd hv hyv t ht, MonoidHom.mem_ker.mp hc]
    rfl
  have hform := apply_eq_of_restr_eq_id hv hyv hg hgv h1
  have hgw : ∀ w : perp Q v y, g w = w := fun w => by
    rw [hform, (mem_perp.mp w.2).1, zero_smul, sub_zero]
  have huW : ∀ w : perp Q v y, polar Q (g y - y) w = 0 := fun w => by
    have h := polar_map_of_mem hg y w
    rw [hgw w] at h
    rw [polar_sub_left, h, sub_self]
  have huv : polar Q v (g y - y) = 0 := by
    have h := polar_map_of_mem hg y v
    rw [hgv] at h
    rw [polar_comm, polar_sub_left, h, sub_self]
  have hpu : proj hyv (g y - y) = 0 := by
    refine separatingLeft_restrict hnd hyv _ fun w => ?_
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, bil_apply]
    rw [coe_proj, huv, zero_smul, add_zero, polar_sub_left, polar_smul_left, huW w,
      (mem_perp.mp w.2).1, smul_zero, sub_zero]
  have hu : g y - y = polar Q y (g y - y) • v := by
    have := eq_proj_add hyv (g y - y)
    rw [hpu, huv, zero_smul, sub_zero, Submodule.coe_zero, zero_add] at this
    exact this
  rcases zmod_two_eq_zero_or_eq_one (polar Q y (g y - y)) with h0 | h0
  · left
    have hg1 : g = 1 := LinearEquiv.ext fun x => by
      rw [hform, hu, h0, zero_smul, smul_zero, sub_zero]
      rfl
    exact Subtype.ext hg1
  · right
    apply Subtype.ext
    refine LinearEquiv.ext fun x => ?_
    rw [← hgdef, hform, hu, h0, one_smul, ht, polar_comm, sub_eq_add_neg, ← neg_smul,
      ZMod.neg_eq_self_mod_two]

theorem exists_normal_le_range_rho (hnd : (polarBilin Q).Nondegenerate) {v y : V}
    (hv : Q v = 1) (hyv : polar Q y v = 1) (t : TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht : ∀ x, (t : V ≃ₗ[ZMod 2] V) x = x + polar Q x v • v) (hW : ∃ w : perp Q v y, w ≠ 0) :
    ∃ N : Subgroup (TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y))),
      N.Normal ∧ N ≠ ⊥ ∧ N ≤ (rho hnd hv hyv t ht).range := by
  set T : Set (TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y))) :=
    {σ | ∃ w : perp Q v y, ∀ x, (σ : perp Q v y ≃ₗ[ZMod 2] perp Q v y) x = x + polar Q x w • w}
  have hTρ : T ⊆ (rho hnd hv hyv t ht).range := by
    rintro σ ⟨w, hw⟩
    obtain ⟨c, hc⟩ := exists_rho_eq hnd hv hyv t ht w
    exact ⟨c, Subtype.ext (LinearEquiv.ext fun x => (hc x).trans (hw x).symm)⟩
  have hconj : Group.conjugatesOfSet T ⊆ T := by
    intro σ hσ
    obtain ⟨τ, ⟨w, hw⟩, hτσ⟩ := Group.mem_conjugatesOfSet_iff.mp hσ
    obtain ⟨s, rfl⟩ := isConj_iff.mp hτσ
    refine ⟨(s : perp Q v y ≃ₗ[ZMod 2] perp Q v y) w, fun x => ?_⟩
    have key : polar Q ((s : perp Q v y ≃ₗ[ZMod 2] perp Q v y)⁻¹ x : V) w =
        polar Q x ((s : perp Q v y ≃ₗ[ZMod 2] perp Q v y) w) := by
      have := TauCeti.BilinForm.mem_isometryGroup_iff.mp s.2
        ((s : perp Q v y ≃ₗ[ZMod 2] perp Q v y)⁻¹ x) w
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, bil_apply,
        LinearEquiv.apply_inv_apply'] at this
      exact this.symm
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, hw, map_add, map_smul, LinearEquiv.apply_inv_apply', key]
  obtain ⟨w, hw0⟩ := hW
  obtain ⟨x, hx⟩ : ∃ x : perp Q v y, polar Q x w = 1 := by
    by_contra! h
    refine hw0 (separatingLeft_restrict hnd hyv w fun x => ?_)
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, bil_apply]
    rw [polar_comm]
    exact (zmod_two_eq_zero_or_eq_one _).resolve_right (h x)
  obtain ⟨c, hc⟩ := exists_rho_eq hnd hv hyv t ht w
  refine ⟨Subgroup.normalClosure T, inferInstance, fun h => ?_,
    (Subgroup.closure_le _).mpr (hconj.trans hTρ)⟩
  have hmem : rho hnd hv hyv t ht c ∈ Subgroup.normalClosure T :=
    Subgroup.subset_normalClosure ⟨w, hc⟩
  rw [h, Subgroup.mem_bot] at hmem
  have := hc x
  rw [hmem, hx, one_smul] at this
  exact hw0 (by simpa using this)

end S12InspO

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_orth_mulEquiv {g : G} {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (htX : t ∈ S.Xbar12 g) {m : ℕ}
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hmod : CFSG.Open.fischerLinearModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (CFSG.Open.fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (CFSG.Open.fischerTransvections (polar Q) fun v => Q v = 1)) :
    ∃ ψ : S.Xbar12 g ≃* TauCeti.QuadraticMap.orthogonalGroup Q, ∃ v, Q v = 1 ∧
      ∀ x, ((ψ ⟨t, htX⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) :
        (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) x = x + polar Q x v • v := by
  obtain ⟨φ, hφ⟩ := hmod
  have hd : (⟨t, htX⟩ : S.Xbar12 g) ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) :=
    mem_Ebar12_of_mem_Lbar ht htA
  obtain ⟨v, hv, hφt⟩ := eq_orthTransvectionGL_of_mem_fischerTransvections ((hφ _).mp hd)
  have hmap : (CFSG.Open.fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
      ∀ x, Q (A *ᵥ x) = Q x).map (toLinEquiv (Fin (2 * m)) (ZMod 2)).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [fischerMatrixGroup_isometry_eq_comap,
      Subgroup.map_comap_eq_self_of_surjective (toLinEquiv (Fin (2 * m)) (ZMod 2)).surjective]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : S.Xbar12 g ≃* TauCeti.QuadraticMap.orthogonalGroup Q,
      ∀ x, ((ψ x : TauCeti.QuadraticMap.orthogonalGroup Q) :
        (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) =
        toLinEquiv (Fin (2 * m)) (ZMod 2) (φ x : GL (Fin (2 * m)) (ZMod 2)) :=
    ⟨φ.trans (((toLinEquiv (Fin (2 * m)) (ZMod 2)).subgroupMap _).trans
      (MulEquiv.subgroupCongr hmap)), fun x => rfl⟩
  exact ⟨ψ, v, hv, fun x => by
    rw [hψ, hφt, toLinEquiv_orthTransvectionGL, reflect_apply_of_map_eq_one hv]⟩

theorem finrank_perp {m : ℕ} {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hQ : (polarBilin Q).Nondegenerate) {v y : Fin (2 * m) → ZMod 2} (hyv : polar Q y v = 1) :
    finrank (ZMod 2) (perp Q v y) = 2 * (m - 1) := by
  have h : finrank (ZMod 2) (perp Q v y) + 2 = finrank (ZMod 2) (Fin (2 * m) → ZMod 2) :=
    (bil_isAlt Q).finrank_orthogonal_span_pair_add_two hQ (bil_eq_one hyv)
  rw [Module.finrank_fin_fun] at h
  omega

theorem polarBilin_nondegenerate {m : ℕ} {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) : (polarBilin Q).Nondegenerate :=
  ⟨fun x hx => hnd x fun y => by simpa using hx y,
    fun y hy => hnd y fun x => by rw [polar_comm]; simpa using hy x⟩

theorem false_of_orth_ge_four {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {m : ℕ} (hm : 4 ≤ m)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmod : CFSG.Open.fischerLinearModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (CFSG.Open.fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (CFSG.Open.fischerTransvections (polar Q) fun v => Q v = 1)) : False := by
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  obtain ⟨ψ, v, hv, ht'⟩ := exists_orth_mulEquiv ht htA htX hmod
  have hQ := polarBilin_nondegenerate hnd
  obtain ⟨y, hyv⟩ := exists_polar_eq_one hQ hv
  have hB' : ((bil Q).restrict (perp Q v y)).IsAlt := fun x => (bil_isAlt Q).self_eq_zero x
  have hnd' : ((bil Q).restrict (perp Q v y)).Nondegenerate :=
    (bil_isAlt Q).restrict_nondegenerate_orthogonal_span_pair (bil_eq_one hyv) hQ
  have hdim := finrank_perp hQ hyv
  have hS := isSimpleGroup_isometryGroup _ hB' hnd' hdim (by omega)
  have : Nontrivial (perp Q v y) := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hsurj := rho_surjective hQ hv hyv _ ht' hS (exists_ne 0)
  have : Finite (perp Q v y ≃ₗ[ZMod 2] perp Q v y) :=
    Finite.of_injective _ DFunLike.coe_injective
  have hns : ¬ Group.IsSolvable
      (TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y))) := by
    refine s12_not_isSolvable_of_simple ?_
    rw [card_isometryGroup_two _ hB' hnd' hdim]
    exact S12InspO.not_prime_card_sp (by omega)
  have hker : ∀ k ∈ (rho hQ hv hyv _ ht').ker, ∀ x, k * x = x * k := fun k hk =>
    S12InspO.mul_comm_of_eq_one_or_eq (S12InspO.rho_ker_eq hQ hv hyv _ ht' hk)
  obtain ⟨e⟩ := S12InspO.nonempty_centralizer_mulEquiv ψ ⟨t, htX⟩
  obtain ⟨ρ', hρ', hker'⟩ := s12_exists_hom_of_mulEquiv e.symm (rho hQ hv hyv _ ht') hsurj hker
  exact false_of_centralizer_hom_simple haQ hne hn ht htA htX hns ρ' hρ' hker'

theorem false_of_orth_six {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 3) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmod : CFSG.Open.fischerLinearModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (CFSG.Open.fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (CFSG.Open.fischerTransvections (polar Q) fun v => Q v = 1)) : False := by
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  obtain ⟨ψ, v, hv, ht'⟩ := exists_orth_mulEquiv ht htA htX hmod
  have hQ := polarBilin_nondegenerate hnd
  obtain ⟨y, hyv⟩ := exists_polar_eq_one hQ hv
  have hB' : ((bil Q).restrict (perp Q v y)).IsAlt := fun x => (bil_isAlt Q).self_eq_zero x
  have hnd' : ((bil Q).restrict (perp Q v y)).Nondegenerate :=
    (bil_isAlt Q).restrict_nondegenerate_orthogonal_span_pair (bil_eq_one hyv) hQ
  have hdim := finrank_perp hQ hyv
  have : Nontrivial (perp Q v y) := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨φ₆⟩ := S12InspO.nonempty_isometryGroup_mulEquiv_perm_six _ hB' hnd' (by omega)
  obtain ⟨N, hNn, hN1, hNle⟩ := S12InspO.exists_normal_le_range_rho hQ hv hyv _ ht' (exists_ne 0)
  obtain ⟨σ, hσdef⟩ : ∃ σ : centralizer ({ψ ⟨t, htX⟩} :
      Set (TauCeti.QuadraticMap.orthogonalGroup Q)) →* Equiv.Perm (Fin 6),
      σ = φ₆.toMonoidHom.comp (rho hQ hv hyv _ ht') := ⟨_, rfl⟩
  have hA6 : alternatingGroup (Fin 6) ≤ σ.range := by
    have hNn' : (N.map φ₆.toMonoidHom).Normal := hNn.map _ φ₆.surjective
    have hnt : Nontrivial (N.map φ₆.toMonoidHom) := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      intro h
      exact hN1 ((Subgroup.map_eq_bot_iff_of_injective _ φ₆.injective).mp h)
    refine (Equiv.Perm.alternatingGroup_le_of_normal
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) hnt).trans ?_
    rw [hσdef, MonoidHom.range_comp]
    exact Subgroup.map_mono hNle
  have hcomm6 : (commutator (centralizer ({ψ ⟨t, htX⟩} :
      Set (TauCeti.QuadraticMap.orthogonalGroup Q)))).map σ = alternatingGroup (Fin 6) := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
    exact S12InspO.commutator_eq_alternatingGroup_six hA6
  have hker : ∀ k ∈ σ.ker, ∀ x, k * x = x * k := fun k hk => by
    rw [hσdef, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff] at hk
    exact S12InspO.mul_comm_of_eq_one_or_eq
      (S12InspO.rho_ker_eq hQ hv hyv _ ht' (MonoidHom.mem_ker.mpr hk))
  obtain ⟨σ', hσ', hker'⟩ := S12InspO.exists_commutator_hom σ hcomm6 hker
  obtain ⟨e⟩ := S12InspO.nonempty_centralizer_mulEquiv ψ ⟨t, htX⟩
  obtain ⟨ec⟩ := S12InspO.nonempty_commutator_mulEquiv e
  have := S12InspO.isSimpleGroup_alternatingGroup_six
  obtain ⟨ρ', hρ', hker''⟩ := s12_exists_hom_of_mulEquiv ec.symm σ' hσ' hker'
  exact false_of_centralizer_commutator_hom_simple haQ hne hn ht htA htX
    S12InspO.not_isSolvable_alternatingGroup_six ρ' hρ' hker''

end Setting

theorem inspOTv3 : InspOTv3 := by
  intro G _ _ _ S g t haQ hne hn ht htA hS hred h
  obtain ⟨-, m, hm, Q, hnd, hmod⟩ := h
  exfalso
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  · obtain rfl : m = 3 := by omega
    exact Setting.false_of_orth_six haQ hne (by omega) ht htA hnd hmod
  · exact Setting.false_of_orth_ge_four haQ hne (by omega) ht htA hm4 hnd hmod

end CFSG.LargeExtraspecial
