module

public import CFSG.CGT.Foote82.T66.BranchASmallBasic
import CFSG.CGT.Foote82.Lemma62Tools
public import CFSG.CGT.Foote82.T66.CitedBAS

public section

namespace CFSG.CGT.Foote82.BAS

open CFSG.Open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem apply_mem_commSpace_of_normalizer {L : Subgroup (GLV V)} {x : GLV V}
    (hx : x ∈ Subgroup.normalizer (L : Set (GLV V))) {w : V} (hw : w ∈ commSpace L ⊤) :
    x w ∈ commSpace L ⊤ := by
  have hle : commSpace L ⊤ ≤ (commSpace L ⊤).comap (x : V →ₗ[ZMod 2] V) := by
    refine commSpace_le_iff.2 fun k hk u _ => ?_
    show x (k u - u) ∈ commSpace L ⊤
    have e : x (k u - u) = (x * k * x⁻¹) (x u) - x u := by
      rw [map_sub, glv_mul_apply, glv_mul_apply, glv_inv_apply_apply]
    rw [e]
    exact sub_mem_commSpace ((Subgroup.mem_normalizer_iff.1 hx k).1 hk) Submodule.mem_top
  exact hle hw

theorem apply_mem_fixedSpace_of_normalizer {L : Subgroup (GLV V)} {x : GLV V}
    (hx : x ∈ Subgroup.normalizer (L : Set (GLV V))) {w : V} (hw : w ∈ fixedSpace L) :
    x w ∈ fixedSpace L := by
  intro k hk
  have hk' : x⁻¹ * k * x ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hx) k).1 hk
    simpa using this
  have := hw _ hk'
  rw [glv_mul_apply, glv_mul_apply] at this
  have h2 := congrArg x this
  rwa [glv_apply_inv_apply] at h2

theorem apply_mem_tildeVBot_of_normalizer {L : Subgroup (GLV V)} {x : GLV V}
    (hx : x ∈ Subgroup.normalizer (L : Set (GLV V))) {w : V} (hw : w ∈ tildeVBot L) :
    x w ∈ tildeVBot L :=
  ⟨apply_mem_fixedSpace_of_normalizer hx hw.1, apply_mem_commSpace_of_normalizer hx hw.2⟩

theorem finrank_commSpace_add_le {L : Subgroup (GLV V)} {c : GLV V} (hcL : c ∈ L)
    (hodd : Odd (orderOf c)) :
    Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) +
        Module.finrank (ZMod 2) ↥(tildeVBot L) ≤
      Module.finrank (ZMod 2) ↥(tvComm L c) := by
  have hcompl : IsCompl (fixedSpace (Subgroup.zpowers c)) (commSpace (Subgroup.zpowers c) ⊤) :=
    isCompl_fixedSpace_commSpace (by rwa [Nat.card_zpowers])
  have hCfix : tildeVBot L ≤ fixedSpace (Subgroup.zpowers c) := fun w hw k hk =>
    hw.1 k (Subgroup.zpowers_le.2 hcL hk)
  have hle : commSpace (Subgroup.zpowers c) ⊤ ≤ commSpace (Subgroup.zpowers c) (commSpace L ⊤) := by
    refine commSpace_le_iff.2 fun k hk v _ => ?_
    have hv : v ∈ fixedSpace (Subgroup.zpowers c) ⊔ commSpace (Subgroup.zpowers c) ⊤ := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨f, hf, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    have hwU : w ∈ commSpace L ⊤ :=
      commSpace_mono (Subgroup.zpowers_le.2 hcL) le_rfl hw
    have e : k (f + w) - (f + w) = k w - w := by
      rw [map_add, hf k hk]
      abel
    rw [e]
    exact sub_mem_commSpace hk hwU
  have hdis : commSpace (Subgroup.zpowers c) ⊤ ⊓ tildeVBot L = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have h1 : v ∈ fixedSpace (Subgroup.zpowers c) ⊓ commSpace (Subgroup.zpowers c) ⊤ :=
      ⟨hCfix hv.2, hv.1⟩
    rwa [hcompl.inf_eq_bot] at h1
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (commSpace (Subgroup.zpowers c) ⊤)
    (tildeVBot L)
  rw [hdis, finrank_bot, add_zero] at h3
  rw [← h3]
  exact Submodule.finrank_mono (sup_le_sup_right hle _)

private theorem eq_one_or_eq_of_mem_zpowers' {e k : GLV V} (he : e * e = 1)
    (hk : k ∈ Subgroup.zpowers e) : k = 1 ∨ k = e := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have h2 : e ^ (2 : ℤ) = 1 := by rw [zpow_two, he]
  rw [zpow_eq_zpow_emod n h2]
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [h] <;> simp

private theorem commSpace_zpowers_inv {e : GLV V} (he : e * e = 1) (U : Submodule (ZMod 2) V)
    {w : V} : w ∈ commSpace (Subgroup.zpowers e) U ↔ ∃ u ∈ U, w = e u - u := by
  constructor
  · intro hw
    have hsub : commSpace (Subgroup.zpowers e) U ≤
        U.map ((e : V →ₗ[ZMod 2] V) - LinearMap.id) := by
      refine commSpace_le_iff.2 fun k hk u hu => ?_
      rcases eq_one_or_eq_of_mem_zpowers' he hk with rfl | rfl
      · exact ⟨0, U.zero_mem, by simp⟩
      · exact ⟨u, hu, by simp⟩
    obtain ⟨u, hu, rfl⟩ := hsub hw
    exact ⟨u, hu, by simp⟩
  · rintro ⟨u, hu, rfl⟩
    exact sub_mem_commSpace (Subgroup.mem_zpowers e) hu

theorem commSpace_mul_le {e f : GLV V} (he : e * e = 1) (hf : f * f = 1)
    {U : Submodule (ZMod 2) V} (heU : ∀ u ∈ U, e u ∈ U) (hfU : ∀ u ∈ U, f u ∈ U) :
    commSpace (Subgroup.zpowers (e * f)) U ≤
      commSpace (Subgroup.zpowers e) U ⊔ commSpace (Subgroup.zpowers f) U := by
  set W := commSpace (Subgroup.zpowers e) U ⊔ commSpace (Subgroup.zpowers f) U with hW
  have hstep : ∀ x ∈ U, (e * f) x - x ∈ W := by
    intro x hx
    have hfx : f x - x ∈ U := U.sub_mem (hfU x hx) hx
    have e1 : (e * f) x - x = (e (f x - x) - (f x - x)) + (f x - x) + (e x - x) := by
      rw [glv_mul_apply, map_sub]
      abel
    rw [e1]
    refine W.add_mem (W.add_mem ?_ ?_) ?_
    · exact Submodule.mem_sup_left ((commSpace_zpowers_inv he U).2 ⟨_, hfx, rfl⟩)
    · exact Submodule.mem_sup_right ((commSpace_zpowers_inv hf U).2 ⟨_, hx, rfl⟩)
    · exact Submodule.mem_sup_left ((commSpace_zpowers_inv he U).2 ⟨_, hx, rfl⟩)
  have hcU : ∀ u ∈ U, (e * f) u ∈ U := fun u hu => by
    rw [glv_mul_apply]
    exact heU _ (hfU u hu)
  have hpow : ∀ m : ℕ, ∀ u ∈ U, ((e * f) ^ m) u - u ∈ W ∧ ((e * f) ^ m) u ∈ U := by
    intro m
    induction m with
    | zero => intro u hu; simpa using hu
    | succ m ih =>
      intro u hu
      obtain ⟨h1, h2⟩ := ih u hu
      refine ⟨?_, ?_⟩
      · have e2 : ((e * f) ^ (m + 1)) u - u =
            ((e * f) (((e * f) ^ m) u) - ((e * f) ^ m) u) + (((e * f) ^ m) u - u) := by
          rw [pow_succ', glv_mul_apply]
          abel
        rw [e2]
        exact W.add_mem (hstep _ h2) h1
      · rw [pow_succ', glv_mul_apply]
        exact hcU _ h2
  refine commSpace_le_iff.2 fun k hk u hu => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hfin : orderOf (e * f) ≠ 0 := (isOfFinOrder_of_finite (e * f)).orderOf_pos.ne'
  have hn : (e * f) ^ n = (e * f) ^ (n % (orderOf (e * f) : ℤ)).toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hfin)),
      zpow_mod_orderOf]
  rw [hn]
  exact (hpow _ u hu).1

theorem tvComm_mul_le {L : Subgroup (GLV V)} {e f : GLV V} (he : e * e = 1) (hf : f * f = 1)
    (heN : e ∈ Subgroup.normalizer (L : Set (GLV V)))
    (hfN : f ∈ Subgroup.normalizer (L : Set (GLV V))) :
    tvComm L (e * f) ≤ tvComm L e ⊔ tvComm L f := by
  refine sup_le ?_ (le_sup_right.trans le_sup_left)
  refine (commSpace_mul_le he hf (fun u hu => apply_mem_commSpace_of_normalizer heN hu)
    (fun u hu => apply_mem_commSpace_of_normalizer hfN hu)).trans ?_
  exact sup_le_sup le_sup_left le_sup_left

theorem finrank_tvComm_sup_le (L : Subgroup (GLV V)) (e f : GLV V) :
    Module.finrank (ZMod 2) ↥(tvComm L e ⊔ tvComm L f) + Module.finrank (ZMod 2) ↥(tildeVBot L) ≤
      Module.finrank (ZMod 2) ↥(tvComm L e) + Module.finrank (ZMod 2) ↥(tvComm L f) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (tvComm L e) (tvComm L f)
  have hle : tildeVBot L ≤ tvComm L e ⊓ tvComm L f := le_inf le_sup_right le_sup_right
  have := Submodule.finrank_mono hle
  omega

private theorem conjSub_commSpace_of_mem {L : Subgroup (GLV V)} {l : GLV V} (hl : l ∈ L) :
    conjSub l (commSpace L ⊤) = commSpace L ⊤ := by
  have hN : l ∈ Subgroup.normalizer (L : Set (GLV V)) :=
    Subgroup.le_normalizer hl
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    exact apply_mem_commSpace_of_normalizer hN hw
  · intro w hw
    rw [mem_conjSub]
    exact apply_mem_commSpace_of_normalizer (Subgroup.inv_mem _ hN) hw

private theorem conjSub_tildeVBot_of_mem {L : Subgroup (GLV V)} {l : GLV V} (hl : l ∈ L) :
    conjSub l (tildeVBot L) = tildeVBot L := by
  have hN : l ∈ Subgroup.normalizer (L : Set (GLV V)) :=
    Subgroup.le_normalizer hl
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    exact apply_mem_tildeVBot_of_normalizer hN hw
  · intro w hw
    rw [mem_conjSub]
    exact apply_mem_tildeVBot_of_normalizer (Subgroup.inv_mem _ hN) hw

theorem tvComm_conj {L : Subgroup (GLV V)} {l : GLV V} (hl : l ∈ L) (e : GLV V) :
    tvComm L (l * e * l⁻¹) = conjSub l (tvComm L e) := by
  show commSpace (Subgroup.zpowers (l * e * l⁻¹)) (commSpace L ⊤) ⊔ tildeVBot L =
    conjSub l (commSpace (Subgroup.zpowers e) (commSpace L ⊤) ⊔ tildeVBot L)
  rw [conjSub_sup, conjSub_tildeVBot_of_mem hl, ← conjSg_zpowers]
  congr 1
  conv_lhs => rw [← conjSub_commSpace_of_mem hl]
  exact commSpace_conjSg l _ _

theorem finrank_tvComm_conj {L : Subgroup (GLV V)} {l : GLV V} (hl : l ∈ L) (e : GLV V) :
    Module.finrank (ZMod 2) ↥(tvComm L (l * e * l⁻¹)) = Module.finrank (ZMod 2) ↥(tvComm L e) := by
  rw [tvComm_conj hl, finrank_conjSub]

theorem mem_centralizer_of_tvComm_le {L : Subgroup (GLV V)} (hfaith : FaithfulTildeV L)
    {x : GLV V} (hx : x * x = 1) (hxN : x ∈ Subgroup.normalizer (L : Set (GLV V)))
    (hle : tvComm L x ≤ tildeVBot L) : x ∈ Subgroup.centralizer (L : Set (GLV V)) := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have htriv : ∀ w ∈ commSpace L ⊤, x w - w ∈ fixedSpace L := fun w hw =>
    (hle (Submodule.mem_sup_left (sub_mem_commSpace (Subgroup.mem_zpowers x) hw))).1
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hkL : x * l * x⁻¹ * l⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.1 hxN l).1 hl) (L.inv_mem hl)
  have hk : x * l * x⁻¹ * l⁻¹ = 1 := by
    refine hfaith _ hkL fun w hw => ?_
    have hw1 : l⁻¹ w ∈ commSpace L ⊤ :=
      apply_mem_commSpace_of_normalizer (Subgroup.inv_mem _ (Subgroup.le_normalizer hl)) hw
    set c₁ := x (l⁻¹ w) - l⁻¹ w with hc₁
    have hc₁F : c₁ ∈ fixedSpace L := htriv _ hw1
    set c₂ := x w - w with hc₂
    have hc₂F : c₂ ∈ fixedSpace L := htriv _ hw
    have e1 : (x * l * x⁻¹ * l⁻¹) w - w = c₂ + x c₁ := by
      rw [hxinv, glv_mul_apply, glv_mul_apply, glv_mul_apply]
      have h1 : x (l⁻¹ w) = l⁻¹ w + c₁ := by rw [hc₁]; abel
      have h2 : l (l⁻¹ w + c₁) = w + c₁ := by
        rw [map_add, glv_apply_inv_apply, hc₁F l hl]
      rw [h1, h2, map_add, hc₂]
      abel
    rw [e1]
    exact (fixedSpace L).add_mem hc₂F (apply_mem_fixedSpace_of_normalizer hxN hc₁F)
  calc l * x = (x * l * x⁻¹ * l⁻¹)⁻¹ * (x * l) := by group
    _ = x * l := by rw [hk, inv_one, one_mul]

end CFSG.CGT.Foote82.BAS
