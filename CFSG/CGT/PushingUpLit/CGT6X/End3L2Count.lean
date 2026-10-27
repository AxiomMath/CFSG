module

public import CFSG.CGT.PushingUpLit.CGT6X.End3G23
public import CFSG.CGT.PushingUpLit.CGT6M.FiveComm

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End3

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6M

section Gen

variable {V : Type} [CommGroup V] [Finite V]

theorem card_mul_commSub_le {Y L : Subgroup (MulAut V)} {g c : MulAut V}
    (hgen : Y ⊔ Y.map (MulAut.conj g).toMonoidHom = L) (hL : commV L = ⊤) (hcY : c ∈ Y)
    (hcg : c ∈ Y.map (MulAut.conj g).toMonoidHom) :
    Nat.card V * Nat.card ↥(commSub c) ≤ Nat.card ↥(commV Y) ^ 2 := by
  set Y' := Y.map (MulAut.conj g).toMonoidHom with hY'
  have hU' : commV Y' = (commV Y).map g.toMonoidHom := commV_map_conj g Y
  have hsup : commV Y ⊔ commV Y' = ⊤ := by
    rw [eq_top_iff, ← hL, ← hgen]
    exact commV_sup_le Y Y'
  have hC1 : commSub c ≤ commV Y := by
    rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨c, hcY, v, rfl⟩
  have hC2 : commSub c ≤ commV Y' := by
    rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨c, hcg, v, rfl⟩
  have h1 := card_sup_mul_card_le (le_inf hC1 hC2)
  rw [hsup, Subgroup.card_top, hU', Subgroup.card_map_of_injective g.injective] at h1
  rw [sq]
  exact h1

theorem two_le_card_commSub {c : MulAut V} (hc : c ≠ 1) : 2 ≤ Nat.card ↥(commSub c) := by
  have h : commSub c ≠ ⊥ := fun h => hc (commSub_eq_bot_iff.mp h)
  have : 1 < Nat.card ↥(commSub c) := (Subgroup.one_lt_card_iff_ne_bot _).mpr h
  omega

end Gen

section Natural

theorem exists_mulVec_sub {F : Type} [Field F] [CharP F 2]
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (hodd : Odd (orderOf A)) (hgt : 1 < orderOf A)
    (w : Fin 2 → F) :
    ∃ v : Fin 2 → F, (A : Matrix (Fin 2) (Fin 2) F).mulVec v - v = w := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨a, b, c, d, hA⟩ : ∃ a b c d : F, (A : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have := A.2
    rw [hA, Matrix.det_fin_two_of] at this
    exact this
  have htr : a + d ≠ 0 := by
    intro htr
    have hda : d = a := by linear_combination htr - a * h2
    subst hda
    have hsq : A ^ 2 = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, hA]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination hdet + (b * c) * h2
      · linear_combination b * htr
      · linear_combination c * htr
      · linear_combination hdet + (b * c) * h2
    have hdvd : orderOf A ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · omega
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have hD : a + d ≠ 0 := htr
  have hv : ∀ v : Fin 2 → F, ((A : Matrix (Fin 2) (Fin 2) F).mulVec v - v) 0 =
      a * v 0 + b * v 1 - v 0 ∧ ((A : Matrix (Fin 2) (Fin 2) F).mulVec v - v) 1 =
      c * v 0 + d * v 1 - v 1 := by
    intro v
    rw [hA]
    constructor <;> simp [dotProduct, Fin.sum_univ_two]
  have key0 : (a - 1) * ((d - 1) * w 0 - b * w 1) + b * ((a - 1) * w 1 - c * w 0) =
      w 0 * (a + d) := by
    linear_combination w 0 * hdet + w 0 * (1 - a - d) * h2
  have key1 : c * ((d - 1) * w 0 - b * w 1) + (d - 1) * ((a - 1) * w 1 - c * w 0) =
      w 1 * (a + d) := by
    linear_combination w 1 * hdet + w 1 * (1 - a - d) * h2
  have h0 : ((A : Matrix (Fin 2) (Fin 2) F).mulVec
      ![((d - 1) * w 0 - b * w 1) / (a + d), ((a - 1) * w 1 - c * w 0) / (a + d)] -
      ![((d - 1) * w 0 - b * w 1) / (a + d), ((a - 1) * w 1 - c * w 0) / (a + d)]) 0 = w 0 := by
    rw [(hv _).1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have : a * (((d - 1) * w 0 - b * w 1) / (a + d)) + b * (((a - 1) * w 1 - c * w 0) / (a + d)) -
        ((d - 1) * w 0 - b * w 1) / (a + d) =
        ((a - 1) * ((d - 1) * w 0 - b * w 1) + b * ((a - 1) * w 1 - c * w 0)) / (a + d) := by
      ring
    rw [this, key0, mul_div_cancel_right₀ _ hD]
  have h1 : ((A : Matrix (Fin 2) (Fin 2) F).mulVec
      ![((d - 1) * w 0 - b * w 1) / (a + d), ((a - 1) * w 1 - c * w 0) / (a + d)] -
      ![((d - 1) * w 0 - b * w 1) / (a + d), ((a - 1) * w 1 - c * w 0) / (a + d)]) 1 = w 1 := by
    rw [(hv _).2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have : c * (((d - 1) * w 0 - b * w 1) / (a + d)) + d * (((a - 1) * w 1 - c * w 0) / (a + d)) -
        ((a - 1) * w 1 - c * w 0) / (a + d) =
        (c * ((d - 1) * w 0 - b * w 1) + (d - 1) * ((a - 1) * w 1 - c * w 0)) / (a + d) := by
      ring
    rw [this, key1, mul_div_cancel_right₀ _ hD]
  refine ⟨![((d - 1) * w 0 - b * w 1) / (a + d), ((a - 1) * w 1 - c * w 0) / (a + d)], ?_⟩
  funext i
  fin_cases i
  · exact h0
  · exact h1

variable {V : Type} [CommGroup V]

theorem card_commSub_inf_ge_of_sl {f : ℕ} (hf : 1 ≤ f) {X : Subgroup (MulAut V)}
    {P Z : Subgroup V} (hsec : IsNatSectionBy (slAct f) X P Z) {c : MulAut V} (hcX : c ∈ X)
    (hodd : Odd (orderOf c)) (hgt : 1 < orderOf c) [Finite V] :
    2 ^ (2 * f) ≤ Nat.card ↥(commSub c ⊓ P) := by
  obtain ⟨hinv, θ, β, hβs, -, hβe⟩ := hsec
  have hA : orderOf (θ ⟨c, hcX⟩) = orderOf c := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  let ψ : ↥(commSub c ⊓ P) → Multiplicative (Fin 2 → Fq f) := fun x => β ⟨x, x.2.2⟩
  have hψ : Function.Surjective ψ := by
    intro m
    obtain ⟨v, hv⟩ := exists_mulVec_sub (F := Fq f) (θ ⟨c, hcX⟩) (hA ▸ hodd) (hA ▸ hgt)
      (Multiplicative.toAdd m)
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd v)
    have hcu : c (u : V) ∈ P := hinv c hcX u u.2
    have hx : c (u : V) * (u : V)⁻¹ ∈ commSub c ⊓ P :=
      Subgroup.mem_inf.mpr ⟨deltaHom_mem_commSub c _, mul_mem hcu (inv_mem u.2)⟩
    refine ⟨⟨_, hx⟩, ?_⟩
    show β ⟨c (u : V) * (u : V)⁻¹, hx.2⟩ = m
    have h1 : (⟨c (u : V) * (u : V)⁻¹, hx.2⟩ : ↥P) = ⟨c (u : V), hcu⟩ * u⁻¹ := rfl
    rw [h1, map_mul, map_inv, hβe ⟨c, hcX⟩ u hcu, hu]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv]
    change (θ ⟨c, hcX⟩ : Matrix (Fin 2) (Fin 2) (Fq f)).mulVec v + -v = _
    rw [← sub_eq_add_neg]
    exact hv
  calc 2 ^ (2 * f) = Nat.card (Multiplicative (Fin 2 → Fq f)) := (card_sl_model hf).symm
    _ ≤ Nat.card ↥(commSub c ⊓ P) := Nat.card_le_card_of_surjective ψ hψ

theorem card_commSub_le_of_section [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {S M : Type} [Group S]
    [Group M] [Finite M] {act : S → M → M} {Y : Subgroup (MulAut V)} {Z : Subgroup V}
    (hZ : Z ≤ commV Y ⊓ fixV Y) (hsec : IsNatSectionBy act Y (commV Y) Z) {c : MulAut V}
    (hcY : c ∈ Y) (hodd : Odd (orderOf c)) : Nat.card ↥(commSub c) ≤ Nat.card M := by
  obtain ⟨-, θ, β, -, hβk, -⟩ := hsec
  have hle : commSub c ≤ commV Y := by
    rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨c, hcY, v, rfl⟩
  let ψ : ↥(commSub c) →* M := β.comp (Subgroup.inclusion hle)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : Subgroup.inclusion hle x ∈ β.ker := hx
    rw [hβk, Subgroup.mem_subgroupOf] at hx1
    have hxZ := hZ hx1
    have hxfix : (x : V) ∈ fixSub c := hxZ.2 c hcY
    have := commSub_inf_fixSub_eq_bot hodd (pow_orderOf_eq_one c) hV
    have hx0 : (x : V) ∈ commSub c ⊓ fixSub c := ⟨x.2, hxfix⟩
    rw [this] at hx0
    exact Subtype.ext (Subgroup.mem_bot.mp hx0)
  exact Nat.card_le_card_of_injective ψ hψ

end Natural

end CFSG.CGT.PushingUpLit.CGT6X.End3
