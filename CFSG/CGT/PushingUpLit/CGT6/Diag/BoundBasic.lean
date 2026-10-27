module

public import CFSG.Quasithin.Background.OddCoprimeFixV
public import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Bound

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

theorem commV_zpowers_le {Y : Subgroup (MulAut V)} {y : MulAut V} (hy : y ∈ Y) :
    commV (Subgroup.zpowers y) ≤ commV Y :=
  Subgroup.closure_mono fun _ ⟨x, hx, v, hxv⟩ => ⟨x, Subgroup.zpowers_le.mpr hy hx, v, hxv⟩

theorem fixV_le_fixV_zpowers {Y : Subgroup (MulAut V)} {y : MulAut V} (hy : y ∈ Y) :
    fixV Y ≤ fixV (Subgroup.zpowers y) :=
  fun _ hv x hx => hv x (Subgroup.zpowers_le.mpr hy hx)

theorem mem_fixV_zpowers_of_apply_eq {y : MulAut V} {w : V} (h : y w = w) :
    w ∈ fixV (Subgroup.zpowers y) :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply.2 h

theorem commV_inf_fixV_eq_bot_of_odd (hV : ∀ v : V, v ^ 2 = 1) (P : Subgroup (MulAut V))
    [Finite P] (hodd : Odd (Nat.card P)) : commV P ⊓ fixV P = ⊥ :=
  CFSG.Quasithin.commV_inf_fixV_eq_bot_of_odd_card hV P hodd

theorem commV_zpowers_inf_fixV (hV : ∀ v : V, v ^ 2 = 1) {y : MulAut V}
    (hodd : Odd (orderOf y)) :
    commV (Subgroup.zpowers y) ⊓ fixV (Subgroup.zpowers y) = ⊥ := by
  have hcard : Nat.card (Subgroup.zpowers y) = orderOf y := Nat.card_zpowers y
  have : Finite (Subgroup.zpowers y) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hodd.pos.ne')
  exact commV_inf_fixV_eq_bot_of_odd hV _ (by rw [hcard]; exact hodd)

theorem eq_one_of_mem_commV_zpowers_of_fixed (hV : ∀ v : V, v ^ 2 = 1) {y : MulAut V}
    (hodd : Odd (orderOf y)) {w : V} (hw : w ∈ commV (Subgroup.zpowers y)) (hfix : y w = w) :
    w = 1 := by
  have h : w ∈ commV (Subgroup.zpowers y) ⊓ fixV (Subgroup.zpowers y) :=
    ⟨hw, mem_fixV_zpowers_of_apply_eq hfix⟩
  rw [commV_zpowers_inf_fixV hV hodd] at h
  exact h

theorem injective_comp_inclusion (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    {y : MulAut V} (hy : y ∈ Y) (hodd : Odd (orderOf y)) {Z : Subgroup V} (hZ : Z ≤ fixV Y)
    {M : Type*} [Group M] (β : ↥(commV Y) →* M) (hβ : β.ker = Z.subgroupOf (commV Y)) :
    Function.Injective (β.comp (Subgroup.inclusion (commV_zpowers_le hy))) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro r hr
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hr
  have h1 : Subgroup.inclusion (commV_zpowers_le hy) r ∈ β.ker := hr
  rw [hβ, Subgroup.mem_subgroupOf] at h1
  have h2 : (r : V) ∈ fixV (Subgroup.zpowers y) := fixV_le_fixV_zpowers hy (hZ h1)
  have h3 : (r : V) ∈ commV (Subgroup.zpowers y) ⊓ fixV (Subgroup.zpowers y) := ⟨r.2, h2⟩
  rw [commV_zpowers_inf_fixV hV hodd] at h3
  exact Subtype.ext h3

theorem card_commV_zpowers_le (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    {y : MulAut V} (hy : y ∈ Y) (hodd : Odd (orderOf y)) {Z : Subgroup V} (hZ : Z ≤ fixV Y)
    {M : Type*} [Group M] [Finite M] (β : ↥(commV Y) →* M)
    (hβ : β.ker = Z.subgroupOf (commV Y)) :
    Nat.card ↥(commV (Subgroup.zpowers y)) ≤ Nat.card M :=
  Nat.card_le_card_of_injective _ (injective_comp_inclusion hV hy hodd hZ β hβ)

theorem exists_comm_eq [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {y : MulAut V}
    (hodd : Odd (orderOf y)) {r : V} (hr : r ∈ commV (Subgroup.zpowers y)) :
    ∃ u ∈ commV (Subgroup.zpowers y), y u * u⁻¹ = r := by
  have hmem : ∀ u : V, y u * u⁻¹ ∈ commV (Subgroup.zpowers y) := fun u =>
    Subgroup.subset_closure ⟨y, Subgroup.mem_zpowers y, u, rfl⟩
  let f : ↥(commV (Subgroup.zpowers y)) → ↥(commV (Subgroup.zpowers y)) :=
    fun u => ⟨y (u : V) * (u : V)⁻¹, hmem u⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : y (a : V) * (a : V)⁻¹ = y (b : V) * (b : V)⁻¹ := congrArg Subtype.val hab
    have h2 : y ((a : V) * (b : V)⁻¹) = (a : V) * (b : V)⁻¹ := by
      have h3 : y (a : V) / y (b : V) = (a : V) / (b : V) := by
        have h4 : y (a : V) / (a : V) = y (b : V) / (b : V) := by
          simpa [div_eq_mul_inv] using h1
        exact div_eq_div_iff_div_eq_div.mp h4
      simpa [div_eq_mul_inv] using h3
    have h5 : (a : V) * (b : V)⁻¹ ∈ commV (Subgroup.zpowers y) :=
      Subgroup.mul_mem _ a.2 (Subgroup.inv_mem _ b.2)
    have h6 := eq_one_of_mem_commV_zpowers_of_fixed hV hodd h5 h2
    exact Subtype.ext (mul_inv_eq_one.mp h6)
  obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.mp hf ⟨r, hr⟩
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

end CFSG.CGT.PushingUpLit.CGT6.Diag.Bound
