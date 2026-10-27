module

public import CFSG.Fischer.Classification.Orthogonal2.Reflect
public import CFSG.Fischer.Classification.Orthogonal2.Symplectic
public import CFSG.LargeExtraspecial.S2Three

public section

namespace CFSG.Fischer.Classification.Orth2

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.LargeExtraspecial
open CFSG.Fischer.Classification.Recognition.SymO
open CFSG.Blueprint.Fischer

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

section Rho

variable [FiniteDimensional (ZMod 2) V] (hnd : (polarBilin Q).Nondegenerate) {v y : V}
  (hv : Q v = 1) (hyv : polar Q y v = 1) (t : TauCeti.QuadraticMap.orthogonalGroup Q)
  (ht : ∀ x, (t : V ≃ₗ[ZMod 2] V) x = x + polar Q x v • v)

include hnd hv hyv ht in
theorem eq_one_or_eq_of_mem_ker_rho {c : Subgroup.centralizer {t}}
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
  set δ := g y - y with hδ
  have hgw : ∀ w ∈ perp Q v y, g w = w := by
    intro w hw
    rw [hform, (mem_perp.mp hw).1, zero_smul, sub_zero]
  have hδW : ∀ w ∈ perp Q v y, polar Q δ w = 0 := by
    intro w hw
    rw [hδ, polar_sub_left, ← polar_map_of_mem hg y w, hgw w hw, sub_self]
  have hδv : polar Q v δ = 0 := by
    rw [hδ, polar_sub_right, polar_apply_fix hg hgv, sub_self]
  have hproj : proj hyv δ = 0 := by
    refine separatingLeft_restrict hnd hyv _ fun w => ?_
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, bil_apply, coe_proj,
      polar_add_left, polar_sub_left, polar_smul_left, polar_smul_left, hδW w w.2,
      (mem_perp.mp w.2).1, (mem_perp.mp w.2).2]
    simp
  have hδeq : δ = polar Q y δ • v := by
    have h := eq_proj_add hyv δ
    rw [hproj, hδv, zero_smul, sub_zero, Submodule.coe_zero, zero_add] at h
    exact h
  rcases zmod_two_eq_zero_or_eq_one (polar Q y δ) with h0 | h0
  · left
    refine Subtype.ext (LinearEquiv.ext fun x => ?_)
    rw [← hgdef, hform, hδeq, h0, zero_smul, smul_zero, sub_zero]
    rfl
  · right
    refine Subtype.ext (LinearEquiv.ext fun x => ?_)
    rw [← hgdef, hform, hδeq, h0, one_smul, ht, polar_comm, sub_eq_add_neg, ← neg_smul,
      ZMod.neg_eq_self_mod_two]

omit [FiniteDimensional (ZMod 2) V] in
theorem localGroup_le_centralizer (t : TauCeti.QuadraticMap.orthogonalGroup Q) :
    LocalGroup (reflClass Q) t ≤ Subgroup.centralizer {t} := by
  rw [LocalGroup, Subgroup.closure_le]
  intro f hf
  exact Subgroup.mem_centralizer_singleton_iff.mpr hf.2.2

noncomputable def rhoL : LocalGroup (reflClass Q) t →*
    TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y)) :=
  (rho hnd hv hyv t ht).comp (Subgroup.inclusion (localGroup_le_centralizer t))

theorem rhoL_apply (l : LocalGroup (reflClass Q) t) (w : perp Q v y) :
    (rhoL hnd hv hyv t ht l : perp Q v y ≃ₗ[ZMod 2] perp Q v y) w =
      restr hyv (((l : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) :
        V →ₗ[ZMod 2] V) w :=
  rho_apply hnd hv hyv t ht _ w

include hnd hv hyv ht in
theorem coe_eq_reflect : (t : V ≃ₗ[ZMod 2] V) = reflect Q v :=
  LinearEquiv.ext fun x => by rw [ht, reflect_apply_of_map_eq_one hv]

include hnd hv hyv ht in
theorem lift_mem_localClass {w : perp Q v y} (hw0 : w ≠ 0) :
    (⟨reflect Q (lift Q v w), reflect_mem_orthogonalGroup Q _⟩ :
      TauCeti.QuadraticMap.orthogonalGroup Q) ∈ LocalClass (reflClass Q) t := by
  refine ⟨⟨_, map_lift hv w, rfl⟩, fun h => ?_, Subtype.ext ?_⟩
  · have h2 : reflect Q (lift Q v w) = reflect Q v := by
      rw [← coe_eq_reflect hnd hv hyv t ht, ← h]
    have h3 := eq_of_reflect_eq hnd (map_lift hv w) h2 hv
    apply hw0
    rw [← proj_lift hyv w, h3, proj_left]
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_eq_reflect hnd hv hyv t ht]
    exact reflect_lift_commute hv (t := reflect Q v) (fun x => reflect_apply_of_map_eq_one hv x) w

include hnd hv hyv ht in
theorem rhoL_surjective : Function.Surjective (rhoL hnd hv hyv t ht) := by
  have hv0 : v ≠ 0 := ne_zero_of_map_eq_one hv
  have hvy : bil Q v y = 1 := by rw [bil_apply, polar_comm]; exact hyv
  obtain ⟨-, hsplit⟩ :=
    CFSG.ClassicalGroups.Alternating.alternating_hyperbolic_splitting (bil_isAlt Q) hnd hv0
  obtain ⟨-, -, -, -, hndW, -⟩ := hsplit y hvy
  have hB : ((bil Q).restrict (perp Q v y)).IsAlt := fun x => (bil_isAlt Q).self_eq_zero x
  intro σ
  have hσ := CFSG.LargeExtraspecial.S2.sp_le_closure_spTransvection hB hndW σ.2
  have hle : Subgroup.closure (Set.range (spTransvection _ hB)) ≤
      (rhoL hnd hv hyv t ht).range.map
        (TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y))).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨w, rfl⟩
    by_cases hw0 : w = 0
    · subst hw0
      refine ⟨1, Subgroup.one_mem _, LinearEquiv.ext fun x => ?_⟩
      rw [spTransvection_apply, smul_zero, add_zero]
      rfl
    · let r : TauCeti.QuadraticMap.orthogonalGroup Q :=
        ⟨reflect Q (lift Q v w), reflect_mem_orthogonalGroup Q _⟩
      have hrD : r ∈ LocalClass (reflClass Q) t := lift_mem_localClass hnd hv hyv t ht hw0
      refine ⟨rhoL hnd hv hyv t ht ⟨r, Subgroup.subset_closure hrD⟩, ⟨_, rfl⟩,
        LinearEquiv.ext fun x => ?_⟩
      change (rhoL hnd hv hyv t ht ⟨r, _⟩ : perp Q v y ≃ₗ[ZMod 2] perp Q v y) x = _
      rw [rhoL_apply, restr_reflect_lift hv hyv, spTransvection_apply,
        LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, bil_apply]
  obtain ⟨τ, ⟨l, rfl⟩, hτ⟩ := hle hσ
  exact ⟨l, Subtype.ext hτ⟩

include hnd hv hyv ht in
theorem ker_rhoL_eq_center :
    (rhoL hnd hv hyv t ht).ker = Subgroup.center (LocalGroup (reflClass Q) t) := by
  have hv0 : v ≠ 0 := ne_zero_of_map_eq_one hv
  have hvy : bil Q v y = 1 := by rw [bil_apply, polar_comm]; exact hyv
  obtain ⟨-, hsplit⟩ :=
    CFSG.ClassicalGroups.Alternating.alternating_hyperbolic_splitting (bil_isAlt Q) hnd hv0
  obtain ⟨-, -, -, -, hndW, -⟩ := hsplit y hvy
  have hB : ((bil Q).restrict (perp Q v y)).IsAlt := fun x => (bil_isAlt Q).self_eq_zero x
  apply le_antisymm
  · intro l hl
    rw [Subgroup.mem_center_iff]
    intro l'
    have hc : Subgroup.inclusion (localGroup_le_centralizer t) l ∈ (rho hnd hv hyv t ht).ker :=
      hl
    have hl't : (l' : TauCeti.QuadraticMap.orthogonalGroup Q) * t =
        t * (l' : TauCeti.QuadraticMap.orthogonalGroup Q) :=
      Subgroup.mem_centralizer_singleton_iff.mp (localGroup_le_centralizer t l'.2)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    rcases eq_one_or_eq_of_mem_ker_rho hnd hv hyv t ht hc with h1 | h1
    · change (l' : TauCeti.QuadraticMap.orthogonalGroup Q) *
          (Subgroup.inclusion (localGroup_le_centralizer t) l :
            TauCeti.QuadraticMap.orthogonalGroup Q) =
        (Subgroup.inclusion (localGroup_le_centralizer t) l :
            TauCeti.QuadraticMap.orthogonalGroup Q) * l'
      rw [h1, mul_one, one_mul]
    · change (l' : TauCeti.QuadraticMap.orthogonalGroup Q) *
          (Subgroup.inclusion (localGroup_le_centralizer t) l :
            TauCeti.QuadraticMap.orthogonalGroup Q) =
        (Subgroup.inclusion (localGroup_le_centralizer t) l :
            TauCeti.QuadraticMap.orthogonalGroup Q) * l'
      rw [h1, hl't]
  · intro z hz
    rw [MonoidHom.mem_ker]
    have hcen : rhoL hnd hv hyv t ht z ∈
        Subgroup.center (TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y))) := by
      rw [Subgroup.mem_center_iff]
      intro σ
      obtain ⟨l, rfl⟩ := rhoL_surjective hnd hv hyv t ht σ
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [center_isometryGroup_eq_bot hB hndW] at hcen
    exact Subgroup.mem_bot.mp hcen

noncomputable def localQuotientEquiv : LocalQuotient (reflClass Q) t ≃*
    TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_rhoL_eq_center hnd hv hyv t ht).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (rhoL_surjective hnd hv hyv t ht))

end Rho

theorem exists_ne_commutator_of_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    (h : ∃ a b : commutator G, a * b ≠ b * a) : ∃ a b : commutator H, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  have hmap : (commutator G).map (φ : G →* H) = commutator H := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective (φ : G →* H) φ.surjective]
  have hmem : ∀ x : commutator G, φ x ∈ commutator H := fun x => by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (φ : G →* H) x.2
  refine ⟨⟨φ a, hmem a⟩, ⟨φ b, hmem b⟩, fun hc => hab (Subtype.ext ?_)⟩
  have := congrArg (fun z : commutator H => φ.symm (z : H)) hc
  simpa using this

theorem localQuotient_simple [FiniteDimensional (ZMod 2) V] (hnd : (polarBilin Q).Nondegenerate)
    {m : ℕ} (hdim : finrank (ZMod 2) V = 2 * m) (hm : 3 ≤ m)
    {t : TauCeti.QuadraticMap.orthogonalGroup Q} (htD : t ∈ reflClass Q) :
    IsSimpleGroup (commutator (LocalQuotient (reflClass Q) t)) ∧
      ∃ a b : commutator (LocalQuotient (reflClass Q) t), a * b ≠ b * a := by
  obtain ⟨v, hv, htv⟩ := htD
  have ht : ∀ x, (t : V ≃ₗ[ZMod 2] V) x = x + polar Q x v • v := fun x => by
    rw [htv, reflect_apply_of_map_eq_one hv]
  obtain ⟨y, hyv⟩ := exists_polar_eq_one hnd hv
  have hv0 : v ≠ 0 := ne_zero_of_map_eq_one hv
  have hvy : bil Q v y = 1 := by rw [bil_apply, polar_comm]; exact hyv
  obtain ⟨-, hsplit⟩ :=
    CFSG.ClassicalGroups.Alternating.alternating_hyperbolic_splitting (bil_isAlt Q) hnd hv0
  obtain ⟨-, -, -, -, hndW, hdimW⟩ := hsplit y hvy
  have hB : ((bil Q).restrict (perp Q v y)).IsAlt := fun x => (bil_isAlt Q).self_eq_zero x
  have hk : finrank (ZMod 2) (perp Q v y) = 2 * (m - 1) := by
    rw [hdimW, hdim]
    omega
  let e := localQuotientEquiv hnd hv hyv t ht
  haveI := isSimpleGroup_commutator_isometryGroup hB hndW hk (by omega)
  exact ⟨Recognition.R3.isSimpleGroup_commutator_of_mulEquiv e.symm,
    exists_ne_commutator_of_mulEquiv e.symm
      (nonabelian_commutator_isometryGroup hB hndW (by omega))⟩

end CFSG.Fischer.Classification.Orth2
