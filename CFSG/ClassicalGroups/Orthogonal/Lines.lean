module

public import CFSG.ClassicalGroups.Orthogonal.Restrict
public import Mathlib.LinearAlgebra.Projectivization.Action

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap
open scoped LinearAlgebra.Projectivization

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

attribute [local simp] HypPair.Q_e HypPair.Q_f HypPair.polar_ef HypPair.polar_fe
  HypPair.polar_ee HypPair.polar_ff

theorem map_rep_mk_eq_zero_iff {v : V} (hv : v ≠ 0) :
    Q (Projectivization.mk K v hv).rep = 0 ↔ Q v = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  rw [← ha, Units.smul_def, map_smul_eq_sq, mul_eq_zero, or_iff_right (pow_ne_zero 2 a.ne_zero)]

theorem smul_projectivization_mk (g : elementaryGroup Q) {v : V} (hv : v ≠ 0) :
    g • Projectivization.mk K v hv = Projectivization.mk K ((g : V ≃ₗ[K] V) v)
      (fun h => hv ((g : V ≃ₗ[K] V).map_eq_zero_iff.mp h)) :=
  rfl

variable (Q) in
@[expose] def singularLines : SubMulAction (elementaryGroup Q) (ℙ K V) where
  carrier := {p | Q p.rep = 0}
  smul_mem' g p hp := by
    induction p using Projectivization.ind with | h v hv => ?_
    change Q (g • Projectivization.mk K v hv).rep = 0
    rw [smul_projectivization_mk, map_rep_mk_eq_zero_iff,
      map_of_mem (elementaryGroup_le_orthogonalGroup Q g.2)]
    exact (map_rep_mk_eq_zero_iff hv).mp hp

@[expose] def lineMk (v : V) (hv : v ≠ 0) (hQ : Q v = 0) : singularLines Q :=
  ⟨Projectivization.mk K v hv, (map_rep_mk_eq_zero_iff hv).mpr hQ⟩

theorem lineMk_eq_lineMk_iff {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) (hQv : Q v = 0)
    (hQw : Q w = 0) : lineMk v hv hQv = lineMk w hw hQw ↔ ∃ a : K, a • w = v := by
  rw [Subtype.ext_iff]
  exact Projectivization.mk_eq_mk_iff' K v w hv hw

theorem smul_lineMk (g : elementaryGroup Q) {v : V} (hv : v ≠ 0) (hQ : Q v = 0) :
    g • lineMk v hv hQ = lineMk ((g : V ≃ₗ[K] V) v)
      (fun h => hv ((g : V ≃ₗ[K] V).map_eq_zero_iff.mp h))
      (by rw [map_of_mem (elementaryGroup_le_orthogonalGroup Q g.2), hQ]) :=
  rfl

theorem exists_eq_lineMk (p : singularLines Q) :
    ∃ (v : V) (hv : v ≠ 0) (hQ : Q v = 0), p = lineMk v hv hQ :=
  ⟨p.1.rep, p.1.rep_nonzero, p.2, Subtype.ext (Projectivization.mk_rep p.1).symm⟩

theorem smul_lineMk_of_apply_eq_smul {g : elementaryGroup Q} {v w : V} (hv : v ≠ 0) (hw : w ≠ 0)
    (hQv : Q v = 0) (hQw : Q w = 0) {c : K} (h : (g : V ≃ₗ[K] V) v = c • w) :
    g • lineMk v hv hQv = lineMk w hw hQw := by
  rw [smul_lineMk, lineMk_eq_lineMk_iff]
  exact ⟨c, h.symm⟩

theorem mem_scalars_of_forall_singular {P P' : HypPair Q} (h : P.Orth P') {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ v, v ≠ 0 → Q v = 0 → ∃ c : K, g v = c • v) : g ∈ scalars K V := by
  obtain ⟨a, ha⟩ := hfix P.e P.e_ne_zero P.Q_e
  obtain ⟨c, hc⟩ := hfix P.f P.f_ne_zero P.Q_f
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, LinearEquiv.map_eq_zero_iff] at hc
    exact P.f_ne_zero hc
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul, LinearEquiv.map_eq_zero_iff] at ha
    exact P.e_ne_zero ha
  have hW : ∀ w ∈ P.perp, g w = a • w ∧ Q w * (c - a) = 0 := by
    intro w hw
    rw [HypPair.mem_perp] at hw
    set s := P.e + w - Q w • P.f with hs
    have hQs : Q s = 0 := by
      rw [hs, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_neg,
        map_smul_eq_sq, polar_neg_right, polar_smul_right_eq, polar_add_left, P.Q_e, P.Q_f,
        polar_comm Q w P.f, hw.2, P.polar_ef, hw.1]
      ring
    have hsf : polar Q s P.f = 1 := by
      rw [hs, polar_sub_left, polar_add_left, polar_smul_left_eq, P.polar_ef, polar_comm, hw.2,
        P.polar_ff]
      ring
    have hs0 : s ≠ 0 := by
      rintro h0
      rw [h0, polar_zero_left] at hsf
      exact zero_ne_one hsf
    obtain ⟨μ, hμ⟩ := hfix s hs0 hQs
    have hgwf : polar Q (g w) P.f = 0 := by
      have : polar Q (g w) (g P.f) = 0 := by rw [polar_map_of_mem hg, polar_comm, hw.2]
      rwa [hc, polar_smul_right_eq, mul_eq_zero, or_iff_right hc0] at this
    have hgwe : polar Q (g w) P.e = 0 := by
      have : polar Q (g w) (g P.e) = 0 := by rw [polar_map_of_mem hg, polar_comm, hw.1]
      rwa [ha, polar_smul_right_eq, mul_eq_zero, or_iff_right ha0] at this
    have hgs : g s = a • P.e + g w - (Q w * c) • P.f := by
      rw [hs, map_sub, map_add, map_smul, ha, hc, smul_smul]
    have h1 : μ = a := by
      have := congrArg (fun z => polar Q z P.f) hμ
      rw [hgs, polar_sub_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
        polar_smul_left_eq, hsf, P.polar_ef, hgwf, P.polar_ff] at this
      linear_combination -this
    have h2 : g w = a • w + (Q w * (c - a)) • P.f := by
      have h3 : g w = μ • s - a • P.e + (Q w * c) • P.f := by
        rw [← hμ, hgs]
        abel
      rw [h3, h1, hs]
      module
    refine ⟨?_, ?_⟩
    · have h4 := congrArg (fun z => polar Q z P.e) h2
      rw [hgwe, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_comm Q w P.e, hw.1,
        P.polar_fe] at h4
      have h5 : Q w * (c - a) = 0 := by linear_combination -h4
      rw [h2, h5, zero_smul, add_zero]
    · have h4 := congrArg (fun z => polar Q z P.e) h2
      rw [hgwe, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_comm Q w P.e, hw.1,
        P.polar_fe] at h4
      linear_combination -h4
  have hw₀ : P'.e + P'.f ∈ P.perp := by
    rw [HypPair.mem_perp, polar_add_right, polar_add_right, h.ee, h.ef, h.fe, h.ff]
    simp
  have hca : c = a := by
    have := (hW _ hw₀).2
    rw [QuadraticMap.map_add Q, P'.Q_e, P'.Q_f, P'.polar_ef] at this
    linear_combination this
  refine mem_scalars.mpr ⟨a, fun x => ?_⟩
  rw [P.eq_add_proj x, map_add, map_add, map_smul, map_smul, ha, hc, hca, (hW _ (P.proj_mem_perp x)).1,
    smul_add, smul_add, smul_comm a, smul_comm a]

theorem isPretransitive_singularLines (hQ : (polarBilin Q).Nondegenerate) {P P' : HypPair Q}
    (h : P.Orth P') : MulAction.IsPretransitive (elementaryGroup Q) (singularLines Q) := by
  refine ⟨fun p q => ?_⟩
  obtain ⟨v, hv, hQv, rfl⟩ := exists_eq_lineMk p
  obtain ⟨w, hw, hQw, rfl⟩ := exists_eq_lineMk q
  obtain ⟨g, hg, hgv⟩ := exists_mem_elementaryGroup_apply_eq hQ h hv hw (by rw [hQv, hQw])
  exact ⟨⟨g, hg⟩, smul_lineMk_of_apply_eq_smul hv hw hQv hQw (c := 1) (by rw [hgv, one_smul])⟩

theorem exists_fix_apply_eq_smul_of_polar_ne_zero {e x y : V} (he : Q e = 0) (hx : Q x = 0)
    (hy : Q y = 0) (hex : polar Q e x ≠ 0) (hey : polar Q e y ≠ 0) :
    ∃ g ∈ elementaryGroup Q, g e = e ∧ ∃ c : K, g x = c • y := by
  set x' := (polar Q e x)⁻¹ • x
  set y' := (polar Q e y)⁻¹ • y
  have hx' : polar Q e x' = 1 := by rw [polar_smul_right_eq, inv_mul_cancel₀ hex]
  have hy' : polar Q e y' = 1 := by rw [polar_smul_right_eq, inv_mul_cancel₀ hey]
  have hQx' : Q x' = Q y' := by rw [map_smul_eq_sq, map_smul_eq_sq, hx, hy, mul_zero, mul_zero]
  refine ⟨eichler Q e ((1 : K)⁻¹ • (y' - x')), eichler_mem_elementaryGroup Q _ _,
    eichler_apply_self e _, polar Q e x / polar Q e y, ?_⟩
  have h1 := eichler_apply_eq_of_polar_eq he hQx' hx' hy' one_ne_zero
  have hxx : x = polar Q e x • x' := by rw [smul_smul, mul_inv_cancel₀ hex, one_smul]
  have h2 : eichler Q e ((1 : K)⁻¹ • (y' - x')) x = polar Q e x • y' := by
    conv_lhs => rw [hxx]
    rw [map_smul, h1]
  rw [h2, smul_smul, div_eq_mul_inv]

section ThreePairs

variable {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)

include h₁₂ h₁₃ h₂₃ in
theorem exists_fix_apply_eq_of_polar_eq_zero (hQ : (polarBilin Q).Nondegenerate) {x : V}
    (hx : Q x = 0) (hex : polar Q P₁.e x = 0) (hxe : ∀ c : K, x ≠ c • P₁.e) :
    ∃ g ∈ elementaryGroup Q, g P₁.e = P₁.e ∧ g x = P₂.e := by
  have hW := P₁.polarNondegOn_perp hQ
  set w := x - polar Q x P₁.f • P₁.e with hw
  have hwperp : w ∈ P₁.perp := by
    have := P₁.proj_mem_perp x
    rwa [HypPair.proj, polar_comm Q x P₁.e, hex, zero_smul, sub_zero] at this
  have hQw : Q w = 0 := by
    rw [hw, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, map_smul_eq_sq, P₁.Q_e,
      polar_neg_right, polar_smul_right_eq, polar_comm Q x P₁.e, hex, hx]
    ring
  have hw0 : w ≠ 0 := by
    intro h0
    exact hxe (polar Q x P₁.f) (sub_eq_zero.mp h0)
  obtain ⟨v, hvW, hwv⟩ := hW.exists_polar_ne_zero hwperp hw0
  set v' := (polar Q x P₁.f / polar Q w v) • v with hv'
  have hv'W : v' ∈ P₁.perp := P₁.perp.smul_mem _ hvW
  have he₁v' : polar Q P₁.e v' = 0 := (HypPair.mem_perp.mp hv'W).1
  have hwv' : polar Q w v' = polar Q x P₁.f := by
    rw [hv', polar_smul_right_eq, div_mul_cancel₀ _ hwv]
  have hxv' : polar Q x v' = polar Q x P₁.f := by
    have : x = w + polar Q x P₁.f • P₁.e := by rw [hw]; abel
    rw [this, polar_add_left, polar_smul_left_eq, he₁v', mul_zero, add_zero, hwv', ← this]
  have h1 : eichler Q P₁.e v' x = w := by
    rw [eichler_apply P₁.Q_e he₁v', polar_comm Q x P₁.e, hex, hxv', zero_smul, add_zero,
      mul_zero, add_zero, hw]
  have he₂W : P₂.e ∈ P₁.perp := HypPair.mem_perp.mpr ⟨h₁₂.ee, h₁₂.fe⟩
  have hf₂W : P₂.f ∈ P₁.perp := HypPair.mem_perp.mpr ⟨h₁₂.ef, h₁₂.ff⟩
  have he₃W : P₃.e ∈ P₁.perp := HypPair.mem_perp.mpr ⟨h₁₃.ee, h₁₃.fe⟩
  have hf₃W : P₃.f ∈ P₁.perp := HypPair.mem_perp.mpr ⟨h₁₃.ef, h₁₃.ff⟩
  obtain ⟨g, hg, hgw, -, hgfix⟩ := exists_mem_elementaryGroup_apply_eq_of_mem hW h₂₃ he₂W hf₂W
    he₃W hf₃W hwperp he₂W hw0 P₂.e_ne_zero (by rw [hQw, P₂.Q_e])
  refine ⟨g * eichler Q P₁.e v', mul_mem hg (eichler_mem_elementaryGroup Q _ _), ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, eichler_apply_self]
    exact hgfix _ fun z hz => (HypPair.mem_perp.mp hz).1
  · rw [LinearEquiv.mul_apply, h1, hgw]

variable {B : Set (singularLines Q)}

private theorem smul_mem_of_isBlock (hB : MulAction.IsBlock (elementaryGroup Q) B)
    {p q : singularLines Q} (hp : p ∈ B) (hq : q ∈ B) {g : elementaryGroup Q} (hg : g • p = p) :
    g • q ∈ B := by
  have h := hB.smul_eq_of_mem hp (by rwa [hg])
  rw [← h]
  exact Set.smul_mem_smul_set hq

private theorem inv_smul_mem_of_isBlock (hB : MulAction.IsBlock (elementaryGroup Q) B)
    {p q : singularLines Q} (hp : p ∈ B) (hq : q ∈ B) {g : elementaryGroup Q} (hg : g • p = p) :
    g⁻¹ • q ∈ B :=
  smul_mem_of_isBlock hB hp hq (by rw [inv_smul_eq_iff, hg])

include h₁₂ h₁₃ h₂₃ in
private theorem mem_of_isBlock_perp (hQ : (polarBilin Q).Nondegenerate)
    (hB : MulAction.IsBlock (elementaryGroup Q) B)
    (hα : lineMk P₁.e P₁.e_ne_zero P₁.Q_e ∈ B) {x : V} (hx0 : x ≠ 0) (hx : Q x = 0)
    (hex : polar Q P₁.e x = 0) (hxe : ∀ c : K, x ≠ c • P₁.e) (hxB : lineMk x hx0 hx ∈ B)
    {y : V} (hy0 : y ≠ 0) (hy : Q y = 0) (hey : polar Q P₁.e y = 0) (hye : ∀ c : K, y ≠ c • P₁.e) :
    lineMk y hy0 hy ∈ B := by
  obtain ⟨g, hg, hge, hgx⟩ := exists_fix_apply_eq_of_polar_eq_zero h₁₂ h₁₃ h₂₃ hQ hx hex hxe
  obtain ⟨k, hk, hke, hky⟩ := exists_fix_apply_eq_of_polar_eq_zero h₁₂ h₁₃ h₂₃ hQ hy hey hye
  have hgα : (⟨g, hg⟩ : elementaryGroup Q) • lineMk P₁.e P₁.e_ne_zero P₁.Q_e =
      lineMk P₁.e P₁.e_ne_zero P₁.Q_e :=
    smul_lineMk_of_apply_eq_smul _ _ _ _ (c := 1) (by rw [one_smul]; exact hge)
  have hkα : (⟨k, hk⟩ : elementaryGroup Q) • lineMk P₁.e P₁.e_ne_zero P₁.Q_e =
      lineMk P₁.e P₁.e_ne_zero P₁.Q_e :=
    smul_lineMk_of_apply_eq_smul _ _ _ _ (c := 1) (by rw [one_smul]; exact hke)
  have he₂ : lineMk P₂.e P₂.e_ne_zero P₂.Q_e ∈ B := by
    have := smul_mem_of_isBlock hB hα hxB hgα
    rwa [smul_lineMk_of_apply_eq_smul hx0 P₂.e_ne_zero hx P₂.Q_e (c := 1)
      (by rw [one_smul]; exact hgx)] at this
  have := inv_smul_mem_of_isBlock hB hα he₂ hkα
  have hky' : (⟨k, hk⟩ : elementaryGroup Q) • lineMk y hy0 hy = lineMk P₂.e P₂.e_ne_zero P₂.Q_e :=
    smul_lineMk_of_apply_eq_smul _ _ _ _ (c := 1) (by rw [one_smul]; exact hky)
  rwa [← hky', inv_smul_smul] at this

include h₁₂ h₁₃ h₂₃ in
private theorem eq_univ_of_isBlock_perp (hQ : (polarBilin Q).Nondegenerate)
    (hB : MulAction.IsBlock (elementaryGroup Q) B)
    (hα : lineMk P₁.e P₁.e_ne_zero P₁.Q_e ∈ B) {x : V} (hx0 : x ≠ 0) (hx : Q x = 0)
    (hex : polar Q P₁.e x = 0) (hxe : ∀ c : K, x ≠ c • P₁.e) (hxB : lineMk x hx0 hx ∈ B) :
    B = Set.univ := by
  have hperp : ∀ {y : V} (hy0 : y ≠ 0) (hy : Q y = 0), polar Q P₁.e y = 0 →
      (∀ c : K, y ≠ c • P₁.e) → lineMk y hy0 hy ∈ B := fun hy0 hy hey hye =>
    mem_of_isBlock_perp h₁₂ h₁₃ h₂₃ hQ hB hα hx0 hx hex hxe hxB hy0 hy hey hye
  have hnot : ∀ {z : V}, polar Q z P₁.f = 0 → polar Q z P₂.e ≠ 0 → ∀ c : K, z ≠ c • P₁.e := by
    intro z hz1 hz2 c hc
    rw [hc, polar_smul_left_eq, h₁₂.ee, mul_zero] at hz2
    exact hz2 rfl
  have he₂B : lineMk P₂.e P₂.e_ne_zero P₂.Q_e ∈ B :=
    hperp _ _ h₁₂.ee (fun c hc => by
      have := congrArg (fun z => polar Q z P₂.f) hc
      simp only [polar_smul_left_eq, P₂.polar_ef, h₁₂.ef, mul_zero] at this
      exact one_ne_zero this)
  have hf₂B : lineMk P₂.f P₂.f_ne_zero P₂.Q_f ∈ B :=
    hperp _ _ h₁₂.ef (hnot (by rw [polar_comm, h₁₂.ff]) (by rw [P₂.polar_fe]; exact one_ne_zero))
  obtain ⟨h, hh, hhe⟩ := exists_mem_elementaryGroup_apply_eq hQ h₁₂ P₂.e_ne_zero P₁.e_ne_zero
    (by rw [P₂.Q_e, P₁.Q_e])
  have hhO := elementaryGroup_le_orthogonalGroup Q hh
  have hhα : (⟨h, hh⟩ : elementaryGroup Q) • lineMk P₂.e P₂.e_ne_zero P₂.Q_e =
      lineMk P₁.e P₁.e_ne_zero P₁.Q_e :=
    smul_lineMk_of_apply_eq_smul _ _ _ _ (c := 1) (by rw [one_smul]; exact hhe)
  have hBh := hB.smul_eq_of_mem he₂B (by rw [hhα]; exact hα)
  have hzB : (⟨h, hh⟩ : elementaryGroup Q) • lineMk P₂.f P₂.f_ne_zero P₂.Q_f ∈ B := by
    rw [← hBh]
    exact Set.smul_mem_smul_set hf₂B
  rw [smul_lineMk] at hzB
  set z := h P₂.f
  have hez : polar Q P₁.e z ≠ 0 := by
    rw [← hhe, polar_map_of_mem hhO, P₂.polar_ef]
    exact one_ne_zero
  have hz0 : z ≠ 0 := fun h0 => hez (by rw [h0, polar_zero_right])
  have hQz : Q z = 0 := by rw [map_of_mem hhO, P₂.Q_f]
  refine Set.eq_univ_of_forall fun p => ?_
  obtain ⟨y, hy0, hy, rfl⟩ := exists_eq_lineMk p
  by_cases hey : polar Q P₁.e y = 0
  · by_cases hye : ∀ c : K, y ≠ c • P₁.e
    · exact hperp hy0 hy hey hye
    · push Not at hye
      obtain ⟨c, rfl⟩ := hye
      have hc : c ≠ 0 := by rintro rfl; exact hy0 (zero_smul K _)
      have : lineMk (c • P₁.e) hy0 hy = lineMk P₁.e P₁.e_ne_zero P₁.Q_e := by
        rw [lineMk_eq_lineMk_iff]
        exact ⟨c, rfl⟩
      rw [this]
      exact hα
  · obtain ⟨k, hk, hke, c, hkz⟩ := exists_fix_apply_eq_smul_of_polar_ne_zero P₁.Q_e hQz hy hez hey
    have hkα : (⟨k, hk⟩ : elementaryGroup Q) • lineMk P₁.e P₁.e_ne_zero P₁.Q_e =
        lineMk P₁.e P₁.e_ne_zero P₁.Q_e :=
      smul_lineMk_of_apply_eq_smul _ _ _ _ (c := 1) (by rw [one_smul]; exact hke)
    have := smul_mem_of_isBlock hB hα hzB hkα
    rwa [smul_lineMk_of_apply_eq_smul hz0 hy0 hQz hy hkz] at this

include h₁₂ h₁₃ h₂₃ in
theorem isPreprimitive_singularLines (hQ : (polarBilin Q).Nondegenerate) :
    MulAction.IsPreprimitive (elementaryGroup Q) (singularLines Q) := by
  have := isPretransitive_singularLines hQ h₁₂
  apply MulAction.IsPreprimitive.of_isTrivialBlock_base (lineMk P₁.e P₁.e_ne_zero P₁.Q_e)
  intro B hα hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  obtain ⟨b, hbB, hbα⟩ : ∃ b ∈ B, b ≠ lineMk P₁.e P₁.e_ne_zero P₁.Q_e := by
    by_contra hcon
    push Not at hcon
    exact hsub fun p hp q hq => by rw [hcon p hp, hcon q hq]
  obtain ⟨x, hx0, hx, rfl⟩ := exists_eq_lineMk b
  have hxe : ∀ c : K, x ≠ c • P₁.e := by
    intro c hc
    apply hbα
    rw [lineMk_eq_lineMk_iff]
    exact ⟨c, hc.symm⟩
  by_cases hex : polar Q P₁.e x = 0
  · exact eq_univ_of_isBlock_perp h₁₂ h₁₃ h₂₃ hQ hB hα hx0 hx hex hxe hbB
  ·
    have hef₁ : polar Q P₁.e P₁.f ≠ 0 := by rw [P₁.polar_ef]; exact one_ne_zero
    have hQfe : Q (P₁.f + P₂.e) = 0 := by
      rw [QuadraticMap.map_add Q, P₁.Q_f, P₂.Q_e, h₁₂.fe, add_zero, add_zero]
    have hefe : polar Q P₁.e (P₁.f + P₂.e) ≠ 0 := by
      rw [polar_add_right, P₁.polar_ef, h₁₂.ee, add_zero]; exact one_ne_zero
    have hfe0 : P₁.f + P₂.e ≠ 0 := fun h0 => hefe (by rw [h0, polar_zero_right])
    have hmem : ∀ {y : V} (hy0 : y ≠ 0) (hy : Q y = 0), polar Q P₁.e y ≠ 0 →
        lineMk y hy0 hy ∈ B := by
      intro y hy0 hy hey
      obtain ⟨k, hk, hke, c, hkx⟩ := exists_fix_apply_eq_smul_of_polar_ne_zero P₁.Q_e hx hy hex hey
      have hkα : (⟨k, hk⟩ : elementaryGroup Q) • lineMk P₁.e P₁.e_ne_zero P₁.Q_e =
          lineMk P₁.e P₁.e_ne_zero P₁.Q_e :=
        smul_lineMk_of_apply_eq_smul _ _ _ _ (c := 1) (by rw [one_smul]; exact hke)
      have := smul_mem_of_isBlock hB hα hbB hkα
      rwa [smul_lineMk_of_apply_eq_smul hx0 hy0 hx hy hkx] at this
    have hf₁B := hmem P₁.f_ne_zero P₁.Q_f hef₁
    have hfeB := hmem hfe0 hQfe hefe
    obtain ⟨h, hh, hhf⟩ := exists_mem_elementaryGroup_apply_eq hQ h₁₂ P₁.f_ne_zero P₁.e_ne_zero
      (by rw [P₁.Q_f, P₁.Q_e])
    have hhO := elementaryGroup_le_orthogonalGroup Q hh
    have hhα : (⟨h, hh⟩ : elementaryGroup Q) • lineMk P₁.f P₁.f_ne_zero P₁.Q_f =
        lineMk P₁.e P₁.e_ne_zero P₁.Q_e :=
      smul_lineMk_of_apply_eq_smul _ _ _ _ (c := 1) (by rw [one_smul]; exact hhf)
    have hBh := hB.smul_eq_of_mem hf₁B (by rw [hhα]; exact hα)
    have hzB : (⟨h, hh⟩ : elementaryGroup Q) • lineMk (P₁.f + P₂.e) hfe0 hQfe ∈ B := by
      rw [← hBh]
      exact Set.smul_mem_smul_set hfeB
    rw [smul_lineMk] at hzB
    refine eq_univ_of_isBlock_perp h₁₂ h₁₃ h₂₃ hQ hB hα _ _ ?_ ?_ hzB
    · rw [← hhf, polar_map_of_mem hhO, polar_add_right, P₁.polar_ff, h₁₂.fe, add_zero]
    · intro c hc
      have h1 : P₁.f + P₂.e = c • P₁.f := by
        apply h.injective
        rw [hc, map_smul, hhf]
      have := congrArg (fun z => polar Q z P₂.f) h1
      simp only [polar_add_left, polar_smul_left_eq, P₂.polar_ef, h₁₂.ff, mul_zero,
        zero_add] at this
      exact one_ne_zero this

end ThreePairs

end CFSG.ClassicalGroups.Orthogonal
