module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Basic
public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Dec
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6

theorem card_le_81_of_three_group {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W ≤ 64) {P : Subgroup (MulAut W)} (hP : IsPGroup 3 P) : Nat.card P ≤ 81 := by
  have hW2 : IsPGroup 2 W := fun w => ⟨1, by simpa using hW w⟩
  obtain ⟨n, hn⟩ := hW2.exists_card_eq
  have hn6 : n ≤ 6 := by
    by_contra h
    have : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b => mul_comm a b) (fun a => hW a) hn
  have hGL : Nat.card (MulAut W) = Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :=
    Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toEquiv
  have hdvd : Nat.card (MulAut W) ∣ 20158709760 := by
    rw [hGL, Matrix.card_GL_field]
    interval_cases n <;> norm_num [Finset.prod_fin_eq_prod_range, Finset.prod_range_succ]
  have hP' : Nat.card P ∣ 20158709760 := (Subgroup.card_subgroup_dvd_card P).trans hdvd
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  by_contra hlt
  have hk5 : 5 ≤ k := by
    by_contra h
    have : k ≤ 4 := by omega
    have : 3 ^ k ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h243 : 3 ^ 5 ∣ 3 ^ k := Nat.pow_dvd_pow 3 hk5
  rw [← hk] at h243
  have := h243.trans hP'
  omega

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem mem_stabV_commV_zpowers {d x : MulAut V} (hx : x * d = d * x) :
    x ∈ stabV (commV (Subgroup.zpowers d)) := by
  refine mem_stabV_commV (Subgroup.mem_normalizer_iff.mpr fun g => ?_)
  have hc : ∀ g ∈ Subgroup.zpowers d, x * g * x⁻¹ = g := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have : x * d ^ k = d ^ k * x := (Commute.zpow_right (show Commute x d from hx) k).eq
    rw [this]; group
  constructor
  · intro hg; rw [hc g hg]; exact hg
  · intro hg
    have hg' : x⁻¹ * (x * g * x⁻¹) * x ∈ Subgroup.zpowers d := by
      have e : x * g * x⁻¹ ∈ Subgroup.zpowers d := hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp e
      have : x⁻¹ * d ^ k * x = d ^ k := by
        have h1 : x * d ^ k = d ^ k * x := (Commute.zpow_right (show Commute x d from hx) k).eq
        calc x⁻¹ * d ^ k * x = x⁻¹ * (d ^ k * x) := by group
          _ = x⁻¹ * (x * d ^ k) := by rw [h1]
          _ = d ^ k := by group
      rw [← hk, this]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers d) k
    have e : x⁻¹ * (x * g * x⁻¹) * x = g := by group
    rwa [e] at hg'

theorem card_le_81_of_faithful (hV : ∀ v : V, v ^ 2 = 1) {d : MulAut V} (hd3 : d ^ 3 = 1)
    (hW : Nat.card (commV (Subgroup.zpowers d)) ≤ 64) {P : Subgroup (MulAut V)}
    (hP3 : IsPGroup 3 ↥P) (hPd : ∀ x ∈ P, x * d = d * x)
    (hPC : ∀ x ∈ P, ∀ v : V, d v = v → x v = v) : Nat.card ↥P ≤ 81 := by
  set W : Subgroup V := commV (Subgroup.zpowers d) with hWdef
  have hPle : P ≤ stabV W := fun x hx => mem_stabV_commV_zpowers (hPd x hx)
  set f : ↥P →* MulAut ↥W := (resStab W).comp (Subgroup.inclusion hPle) with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have htriv : ∀ w ∈ W, (x : MulAut V) w = w := by
      intro w hw
      have := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : V)) hx
      simpa [hf, resStab_apply] using this
    apply Subtype.ext
    ext v
    have h1 : v * (normHom d v)⁻¹ ∈ W := mul_inv_normHom_mem_commV hV v
    have h2 : d (normHom d v) = normHom d v := apply_normHom hd3 v
    have e : v = (v * (normHom d v)⁻¹) * normHom d v := by group
    have h3 := htriv _ h1
    have h4 := hPC x x.2 _ h2
    conv_lhs => rw [e]
    rw [map_mul, h3, h4]
    simp
  have hWe : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  have hrange : IsPGroup 3 f.range :=
    hP3.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have h81 : Nat.card f.range ≤ 81 := card_le_81_of_three_group hWe hW hrange
  have : Nat.card ↥P = Nat.card f.range := Nat.card_congr (Equiv.ofInjective _ hinj)
  omega

end CFSG.CGT.PushingUpLit.CGT6E
