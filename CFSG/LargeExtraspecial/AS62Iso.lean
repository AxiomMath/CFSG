module

public import CFSG.LargeExtraspecial.AS62Y2
public import CFSG.LargeExtraspecial.AS62Pres
public import CFSG.LargeExtraspecial.AS62Model

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.CosetTable AS62.Sem

namespace AS62

theorem le_of_relIndex_prime_of_mem {X : Type*} [Group X] {B R P : Subgroup X} (hBR : B ≤ R)
    (hRP : R ≤ P) (hp : (B.relIndex P).Prime) {g : X} (hg : g ∈ R) (hgB : g ∉ B) : P ≤ R := by
  have hmul := Subgroup.relIndex_mul_relIndex B R P hBR hRP
  rcases hp.eq_one_or_self_of_dvd _ ⟨_, hmul.symm⟩ with h | h
  · exact absurd (Subgroup.relIndex_eq_one.1 h hg) hgB
  · rw [h] at hmul
    exact Subgroup.relIndex_eq_one.1
      (Nat.eq_of_mul_eq_mul_left hp.pos (hmul.trans (mul_one _).symm))

theorem surjective_of_le_map_range {X α : Type*} [Group X] [Group α] {K : Subgroup X}
    (f : α →* ↥K) (h : K ≤ f.range.map K.subtype) : Function.Surjective f := by
  intro p
  obtain ⟨y, hy, hyp⟩ := Subgroup.mem_map.1 (h p.2)
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
  exact ⟨x, Subtype.ext hyp⟩

theorem Frame.conj_mem_V {G : Type*} [Group G] (F : Frame G) {h v : G} (hh : h ∈ F.H)
    (hv : v ∈ F.V) : h * v * h⁻¹ ∈ F.V := by
  obtain ⟨d, hd⟩ := F.rep_exists hh
  obtain ⟨-, a, -, rfl⟩ := hd
  obtain ⟨c, -, rfl⟩ := F.exists_vOf hv
  have e : F.vOf d.1 * (a : G) * F.vOf c * (F.vOf d.1 * a)⁻¹ =
      F.vOf d.1 * ((a : G) * F.vOf c * (a : G)⁻¹) * (F.vOf d.1)⁻¹ := by group
  rw [e, F.conj_vOf]
  exact F.V.mul_mem (F.V.mul_mem (F.vOf_mem _) (F.vOf_mem _)) (F.V.inv_mem (F.vOf_mem _))

variable {G : Type} [Group G] [Finite G]

namespace ConfHyp

variable {S : Setting G} {H : Subgroup G}

theorem relIndex_inf_M (hc : ConfHyp S H) (h18 : Nat.card S.Mbar = 18) :
    (S.M ⊓ H).relIndex S.M = 3 := by
  have h1 := Setting.card_eq_relIndex_mul S.M (S.M ⊓ H)
  rw [inf_left_idem, hc.card_M_of_card_Mbar h18, hc.card_M_inf] at h1
  omega

omit [Finite G] in
theorem z_mem_inf (hc : ConfHyp S H) : S.z ∈ S.M ⊓ H := ⟨S.mem_M_iff.mpr rfl, hc.z_mem⟩

end ConfHyp

structure Gens (S : Setting G) (H : Subgroup G) where
  F : Frame G
  t : G
  e : G
  x : G
  s : G
  isFrameOf : IsFrameOf S H F
  rep_t : F.Rep t tD
  rep_e : F.Rep e eD
  rep_x : F.Rep x xD
  rep_s : F.Rep s sD

theorem ConfHyp.exists_gens {S : Setting G} {H : Subgroup G} (hc : ConfHyp S H) :
    Nonempty (Gens S H) := by
  obtain ⟨p, hp, hpz⟩ :=
    Set.exists_ne_of_one_lt_ncard (by rw [hc.ncard_zConj]; norm_num) S.z
  obtain ⟨F, e, x, s, hF, -, -, ht, he, hx, hs, -⟩ := hc.exists_frame_gens hp hpz
  exact ⟨⟨F, p, e, x, s, hF, ht, he, hx, hs⟩⟩

namespace Gens

variable {S : Setting G} {H : Subgroup G} (g : Gens S H)

omit [Finite G] in
theorem rep_z : g.F.Rep S.z zD := g.isFrameOf.rep_z

omit [Finite G] in
theorem mem_H {h : G} {d : ℕ × ℕ} (hd : g.F.Rep h d) : h ∈ H :=
  g.isFrameOf.H_eq ▸ g.F.mem_H_of_rep hd

omit [Finite G] in
theorem t_eq : g.t = g.F.zz 1 := g.F.eq_of_rep g.rep_t g.F.rep_tD

omit [Finite G] in
theorem t_mem_zConj : g.t ∈ S.zConj H := g.t_eq ▸ g.isFrameOf.zz_mem 1

omit [Finite G] in
theorem t_ne_z : g.t ≠ S.z := by
  intro h
  have h1 : g.F.Rep g.t zD := by rw [h]; exact g.rep_z
  exact absurd (g.F.rep_unique g.rep_t h1) (by decide)

theorem t_mem_M (hc : ConfHyp S H) : g.t ∈ S.M := hc.mem_M_of_mem g.t_mem_zConj

theorem e_mem_QG (hc : ConfHyp S H) : g.e ∈ S.QG := g.isFrameOf.mem_QG_of_rep_eD hc g.rep_e

theorem e_mem_M (hc : ConfHyp S H) : g.e ∈ S.M := S.QG_le_M (g.e_mem_QG hc)

omit [Finite G] in
theorem x_mem_M : g.x ∈ S.M := g.isFrameOf.mem_M_of_rep_xD g.rep_x

omit [Finite G] in
theorem s_not_mem_M : g.s ∉ S.M := g.isFrameOf.not_mem_M_of_rep_sD g.rep_s

@[expose] def ΦB (hc : ConfHyp S H) : PG 4 relsB →* ↥(S.M ⊓ H) :=
  g.F.homB g.rep_z g.rep_t g.rep_e g.rep_x (S.M ⊓ H) hc.z_mem_inf
    ⟨g.t_mem_M hc, g.mem_H g.rep_t⟩ ⟨g.e_mem_M hc, g.mem_H g.rep_e⟩
    ⟨g.x_mem_M, g.mem_H g.rep_x⟩

@[expose] def Φ2 (hc : ConfHyp S H) : PG 5 rels2 →* ↥H :=
  g.F.hom2 g.rep_z g.rep_t g.rep_e g.rep_x g.rep_s H hc.z_mem (g.mem_H g.rep_t)
    (g.mem_H g.rep_e) (g.mem_H g.rep_x) (g.mem_H g.rep_s)

theorem ΦB_of (hc : ConfHyp S H) (i : Fin 4) :
    (g.ΦB hc (PresentedGroup.of i) : G) = ![S.z, g.t, g.e, g.x] i :=
  congrArg Subtype.val (g.F.homB_of i)

omit [Finite G] in
theorem Φ2_of (hc : ConfHyp S H) (i : Fin 5) :
    (g.Φ2 hc (PresentedGroup.of i) : G) = ![S.z, g.t, g.e, g.x, g.s] i :=
  congrArg Subtype.val (g.F.hom2_of i)

theorem ΦB_surjective (hc : ConfHyp S H) : Function.Surjective (g.ΦB hc) :=
  g.F.homB_surjective _ _ _ _ _ _ _ _ _ hc.card_M_inf.le

theorem Φ2_surjective (hc : ConfHyp S H) : Function.Surjective (g.Φ2 hc) :=
  g.F.hom2_surjective _ _ _ _ _ _ _ _ _ _ _ hc.card_H.le

theorem ΦB_bijective (hc : ConfHyp S H) :
    Function.Bijective (g.ΦB hc) :=
  (g.ΦB_surjective hc).bijective_of_nat_card_le (relsB_card_le.trans hc.card_M_inf.ge)

theorem Φ2_bijective (hc : ConfHyp S H) :
    Function.Bijective (g.Φ2 hc) :=
  (g.Φ2_surjective hc).bijective_of_nat_card_le (rels2_card_le.trans hc.card_H.ge)

theorem inclusion_comp_ΦB_right (hc : ConfHyp S H) :
    (Subgroup.inclusion (inf_le_right : S.M ⊓ H ≤ H)).comp (g.ΦB hc) = (g.Φ2 hc).comp ι₂ := by
  refine PresentedGroup.ext fun i => Subtype.ext ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ι₂_of]
  change (g.ΦB hc (PresentedGroup.of i) : G) = (g.Φ2 hc (PresentedGroup.of i.castSucc) : G)
  rw [g.ΦB_of, g.Φ2_of, Frame.gens2_castSucc]

structure IsY (y : G) : Prop where
  mem_M : y ∈ S.M
  cube : y * y * y = 1
  comm_x : g.x * y = y * g.x
  sq_ty : g.t * y * g.t * y = 1
  conj_b₁ : y * (g.t * g.e * g.t * g.e) * y⁻¹ = S.z * g.e

omit [Finite G] in
theorem rels1_hold {y : G} (hy : g.IsY y) :
    ∀ r ∈ {r : FreeGroup (Fin 5) | r ∈ rels1.map FreeGroup.mk},
      FreeGroup.lift ![S.z, g.t, g.e, g.x, y] r = 1 :=
  forall_mem_setOf_map_mk (lift_rels1_eq_one
    (g.F.lift_relsB_eq_one g.rep_z g.rep_t g.rep_e g.rep_x) S.z_mul_z
    (YCon.mul_self_of_rep_eD g.rep_e) hy.cube hy.comm_x hy.sq_ty hy.conj_b₁)

theorem gens1_mem (hc : ConfHyp S H) {y : G} (hy : g.IsY y) :
    ∀ i, ![S.z, g.t, g.e, g.x, y] i ∈ S.M := by
  intro i
  fin_cases i
  · exact S.mem_M_iff.mpr rfl
  · exact g.t_mem_M hc
  · exact g.e_mem_M hc
  · exact g.x_mem_M
  · exact hy.mem_M

@[expose] def Φ1 (hc : ConfHyp S H) {y : G} (hy : g.IsY y) : PG 5 rels1 →* ↥S.M :=
  Sem.toSubgroup (g.rels1_hold hy) S.M (g.gens1_mem hc hy)

theorem Φ1_of (hc : ConfHyp S H) {y : G} (hy : g.IsY y) (i : Fin 5) :
    (g.Φ1 hc hy (PresentedGroup.of i) : G) = ![S.z, g.t, g.e, g.x, y] i :=
  congrArg Subtype.val (Sem.toSubgroup_of _ _ _ i)

theorem inclusion_comp_ΦB_left (hc : ConfHyp S H) {y : G} (hy : g.IsY y) :
    (Subgroup.inclusion (inf_le_left : S.M ⊓ H ≤ S.M)).comp (g.ΦB hc) =
      (g.Φ1 hc hy).comp ι₁ := by
  refine PresentedGroup.ext fun i => Subtype.ext ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ι₁_of]
  change (g.ΦB hc (PresentedGroup.of i) : G) = (g.Φ1 hc hy (PresentedGroup.of i.castSucc) : G)
  rw [g.ΦB_of, g.Φ1_of, Frame.gens2_castSucc]

omit [Finite G] in
theorem b₁_mem_V : g.t * g.e * g.t * g.e ∈ g.F.V := by
  have h := g.F.rep_b1 g.rep_t g.rep_e
  rw [show b1D = (6, 1234) by decide] at h
  rw [g.F.eq_of_rep h (g.F.rep_vOf (by decide))]
  exact g.F.vOf_mem 6

omit [Finite G] in
theorem e_not_mem_V : g.e ∉ g.F.V := by
  intro he
  obtain ⟨a, ha, -⟩ := g.F.exists_A_eq_of_rep_vec_zero g.rep_e
  have h1 : g.e ∈ g.F.V ⊓ g.F.A := ⟨he, ha ▸ a.2⟩
  rw [g.F.inf_eq, mem_bot] at h1
  have h2 : g.F.Rep g.e one := by rw [h1]; exact g.F.rep_one
  exact absurd (g.F.rep_unique g.rep_e h2) (by decide)

theorem Φ1_surjective (hc : ConfHyp S H) (h18 : Nat.card S.Mbar = 18) {y : G} (hy : g.IsY y) :
    Function.Surjective (g.Φ1 hc hy) := by
  have hBR : S.M ⊓ H ≤ (g.Φ1 hc hy).range.map S.M.subtype := by
    intro b hb
    obtain ⟨w, hw⟩ := g.ΦB_surjective hc ⟨b, hb⟩
    refine Subgroup.mem_map.2 ⟨g.Φ1 hc hy (ι₁ w), MonoidHom.mem_range.2 ⟨_, rfl⟩, ?_⟩
    rw [← MonoidHom.comp_apply (g.Φ1 hc hy) ι₁, ← g.inclusion_comp_ΦB_left hc hy,
      MonoidHom.comp_apply, hw]
    rfl
  have hyR : y ∈ (g.Φ1 hc hy).range.map S.M.subtype :=
    Subgroup.mem_map.2 ⟨g.Φ1 hc hy (PresentedGroup.of 4), MonoidHom.mem_range.2 ⟨_, rfl⟩,
      g.Φ1_of hc hy 4⟩
  refine surjective_of_le_map_range _ (le_of_relIndex_prime_of_mem hBR
    (Subgroup.map_subtype_le _) ?_ hyR fun h =>
      YCon.not_mem_H g.isFrameOf g.rep_t g.rep_e hy.conj_b₁ h.2)
  rw [hc.relIndex_inf_M h18]
  exact Nat.prime_three

theorem Φ1_bijective (hc : ConfHyp S H)
    (h18 : Nat.card S.Mbar = 18) {y : G} (hy : g.IsY y) : Function.Bijective (g.Φ1 hc hy) :=
  (g.Φ1_surjective hc h18 hy).bijective_of_nat_card_le
    (rels1_card_le.trans (hc.card_M_of_card_Mbar h18).ge)

theorem exists_isY_not_mem (hc : ConfHyp S H)
    (hMbar : Nat.card S.Mbar = 18 ∨ Nat.card S.Mbar = 36) : ∃ y, g.IsY y ∧ y ∉ H := by
  obtain ⟨y, hyM, hyH, h1, h2, h3, h4, -⟩ :=
    g.isFrameOf.exists_y hc hMbar g.rep_t g.rep_e g.rep_x
  exact ⟨y, ⟨hyM, h1, h2, h3, h4⟩, hyH⟩

theorem exists_isY (hc : ConfHyp S H) (h18 : Nat.card S.Mbar = 18) : ∃ y, g.IsY y := by
  obtain ⟨y, hy, -⟩ := g.exists_isY_not_mem hc (Or.inl h18)
  exact ⟨y, hy⟩

end Gens

end AS62

end CFSG.LargeExtraspecial
