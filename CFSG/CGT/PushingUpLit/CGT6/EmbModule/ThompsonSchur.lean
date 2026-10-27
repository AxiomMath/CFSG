module

public import CFSG.Quasithin.Background.CommVCommute
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

section Schur

variable {V : Type*} [CommGroup V]

theorem aut_mul_mul_inv' (q : MulAut V) (a b : V) :
    q (a * b) * (a * b)⁻¹ = (q a * a⁻¹) * (q b * b⁻¹) := by
  rw [map_mul, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

theorem aut_psi_sq (hV : ∀ v : V, v ^ 2 = 1) (q : MulAut V) (v : V) :
    q (q v * v⁻¹) * (q v * v⁻¹)⁻¹ = (q ^ 2) v * v⁻¹ := by
  have h1 : (q v)⁻¹ = q v := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV _)
  have h2 : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV _)
  have h3 : (q ^ 2) v = q (q v) := by rw [pow_two]; rfl
  rw [map_mul, map_inv, mul_inv_rev, inv_inv, h3, h1, h2]
  have h4 : q v * q v = 1 := by rw [← sq]; exact hV _
  calc q (q v) * q v * (v * q v) = q (q v) * (q v * q v) * v := by ac_rfl
    _ = q (q v) * v := by rw [h4, mul_one]

theorem aut_psi_iterate (hV : ∀ v : V, v ^ 2 = 1) (q : MulAut V) (j : ℕ) (v : V) :
    (fun w => q w * w⁻¹)^[2 ^ j] v = (q ^ 2 ^ j) v * v⁻¹ := by
  induction j generalizing v with
  | zero => simp
  | succ j ih =>
    have hfun : (fun w => q w * w⁻¹)^[2 ^ j] = fun w => (q ^ 2 ^ j) w * w⁻¹ := funext ih
    rw [pow_succ, Function.iterate_mul, hfun]
    show (q ^ 2 ^ j) ((q ^ 2 ^ j) v * v⁻¹) * ((q ^ 2 ^ j) v * v⁻¹)⁻¹ = _
    rw [aut_psi_sq hV, ← pow_mul]

theorem aut_psi_iterate_eq_one (hV : ∀ v : V, v ^ 2 = 1) {q : MulAut V} {k : ℕ}
    (hk : q ^ 2 ^ k = 1) (v : V) : (fun w => q w * w⁻¹)^[2 ^ k] v = 1 := by
  rw [aut_psi_iterate hV, hk]
  exact mul_inv_cancel v

theorem apply_mem_commV_of_comm {Y : Subgroup (MulAut V)} {h : MulAut V}
    (hch : ∀ b ∈ Y, b * h = h * b) : ∀ w ∈ commV Y, h w ∈ commV Y :=
  fun _ hw => CFSG.Quasithin.apply_mem_commV_of_forall_commute (fun b hb => (hch b hb).symm) hw

theorem apply_mem_commV_of_mem {Y : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ Y) :
    ∀ w ∈ commV Y, g w ∈ commV Y := by
  intro w hw
  have hw' : w ∈ Subgroup.closure {w | ∃ x ∈ Y, ∃ v : V, x v * v⁻¹ = w} := hw
  refine Subgroup.closure_induction (p := fun w _ => g w ∈ commV Y) ?_ ?_ ?_ ?_ hw'
  · rintro _ ⟨b, hb, v, rfl⟩
    have h2 : g (b v * v⁻¹) = (g * b * g⁻¹) (g v) * (g v)⁻¹ := by
      rw [map_mul, map_inv]
      congr 1
      show g (b v) = g (b (g⁻¹ (g v)))
      rw [MulAut.inv_apply_self]
    rw [h2]
    exact Subgroup.subset_closure ⟨g * b * g⁻¹, Y.mul_mem (Y.mul_mem hg hb) (Y.inv_mem hg),
      g v, rfl⟩
  · rw [map_one]
    exact one_mem _
  · intro a b _ _ ha hb
    rw [map_mul]
    exact mul_mem ha hb
  · intro a _ ha
    rw [map_inv]
    exact inv_mem ha

theorem aut_psi_inv (q : MulAut V) (a : V) : q a⁻¹ * (a⁻¹)⁻¹ = (q a * a⁻¹)⁻¹ := by
  rw [map_inv, inv_inv, mul_inv_rev, inv_inv, mul_comm]

theorem commV_le_fixV_of_irreducible (hV : ∀ v : V, v ^ 2 = 1) {Y Q : Subgroup (MulAut V)}
    (hUY : ∀ N : Subgroup V, (∀ g ∈ Y, ∀ u ∈ commV Y, g u * u⁻¹ ∈ N) → commV Y ≤ N)
    (hirr : ∀ N : Subgroup V, (∀ g ∈ Y, ∀ n ∈ N, g n ∈ N) → N ≤ commV Y →
      commV Y ⊓ fixV Y ≤ N → N = commV Y ⊓ fixV Y ∨ N = commV Y)
    (hQ2 : IsPGroup 2 ↥Q) (hQY : ∀ q ∈ Q, ∀ y ∈ Y, q * y = y * q) : commV Y ≤ fixV Q := by
  intro u hu
  rw [mem_fixV]
  intro q hq
  have hqc : ∀ y ∈ Y, q * y = y * q := hQY q hq
  have hcy : ∀ y ∈ Y, y * q = q * y := fun y hy => (hqc y hy).symm
  have hqy : ∀ y ∈ Y, ∀ v : V, q (y v) = y (q v) := fun y hy v =>
    congrArg (fun g : MulAut V => g v) (hqc y hy)
  have hqU : ∀ w ∈ commV Y, q w ∈ commV Y := apply_mem_commV_of_comm hcy
  have hψU : ∀ w ∈ commV Y, q w * w⁻¹ ∈ commV Y := fun w hw =>
    mul_mem (hqU w hw) (inv_mem hw)
  have hψC : ∀ w ∈ commV Y ⊓ fixV Y, q w * w⁻¹ ∈ commV Y ⊓ fixV Y := by
    intro w hw
    refine ⟨hψU w hw.1, fun y hy => ?_⟩
    rw [map_mul, map_inv, ← hqy y hy w, hw.2 y hy]
  let N : Subgroup V :=
    { carrier := {w | w ∈ commV Y ∧ q w * w⁻¹ ∈ commV Y ⊓ fixV Y}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [aut_mul_mul_inv']
        exact mul_mem ha.2 hb.2⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        rw [aut_psi_inv]
        exact inv_mem ha.2⟩ }
  have hNY : ∀ g ∈ Y, ∀ n ∈ N, g n ∈ N := by
    intro g hg n hn
    refine ⟨apply_mem_commV_of_mem hg n hn.1, ?_⟩
    have h1 : q (g n) * (g n)⁻¹ = g (q n * n⁻¹) := by
      rw [map_mul, map_inv, hqy g hg n]
    rw [h1, hn.2.2 g hg]
    exact hn.2
  have hNU : N ≤ commV Y := fun n hn => hn.1
  have hCN : commV Y ⊓ fixV Y ≤ N := fun w hw => ⟨hw.1, hψC w hw⟩
  rcases hirr N hNY hNU hCN with hN | hN
  · have key : ∀ j : ℕ, ∀ w ∈ commV Y, (fun x => q x * x⁻¹)^[j] w ∈ commV Y ⊓ fixV Y →
        w ∈ commV Y ⊓ fixV Y := by
      intro j
      induction j with
      | zero => intro w _ h; simpa using h
      | succ j ih =>
        intro w hw h
        rw [Function.iterate_succ_apply] at h
        have h1 : q w * w⁻¹ ∈ commV Y ⊓ fixV Y := ih _ (hψU w hw) h
        have : w ∈ N := ⟨hw, h1⟩
        rw [hN] at this
        exact this
    obtain ⟨k, hk⟩ : ∃ k : ℕ, q ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have hUC : ∀ w ∈ commV Y, w ∈ commV Y ⊓ fixV Y := fun w hw =>
      key (2 ^ k) w hw (by rw [aut_psi_iterate_eq_one hV hk]; exact one_mem _)
    have hbot : commV Y ≤ ⊥ := hUY ⊥ fun g hg w hw => by
      rw [(hUC w hw).2 g hg, mul_inv_cancel]
      exact one_mem _
    have : u = 1 := Subgroup.mem_bot.mp (hbot hu)
    rw [this, map_one]
  · have hall : ∀ w ∈ commV Y, q w * w⁻¹ ∈ commV Y ⊓ fixV Y := fun w hw => by
      have : w ∈ N := by rw [hN]; exact hw
      exact this.2
    let F : Subgroup V :=
      { carrier := {w | q w = w}
        one_mem' := map_one q
        mul_mem' := fun {a b} ha hb => by
          show q (a * b) = a * b
          rw [map_mul, show q a = a from ha, show q b = b from hb]
        inv_mem' := fun {a} ha => by
          show q a⁻¹ = a⁻¹
          rw [map_inv, show q a = a from ha] }
    have hF : commV Y ≤ F := hUY F fun g hg w hw => by
      show q (g w * w⁻¹) = g w * w⁻¹
      have hc := hall w hw
      have h1 : q (g w * w⁻¹) * (g w * w⁻¹)⁻¹ = 1 := by
        rw [aut_mul_mul_inv', aut_psi_inv, show q (g w) * (g w)⁻¹ = g (q w * w⁻¹) by
          rw [map_mul, map_inv, hqy g hg w], hc.2 g hg]
        exact mul_inv_cancel _
      exact mul_inv_eq_one.mp h1
    exact hF hu

end Schur

end CFSG.CGT.PushingUpLit.CGT6
