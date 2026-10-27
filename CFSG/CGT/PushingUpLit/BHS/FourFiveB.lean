module

public import CFSG.CGT.PushingUpLit.BHS.FourFiveA

public section

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

namespace Hyp413Comm

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
  {T M L A B : Subgroup (MulAut V)} {n : ℕ}

theorem exists_image_line (h : Hyp42 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) (d : Hyp413Comm P D M L A B n) {x : MulAut V} (hx : x ∈ A ⊔ B)
    {D₁ : Subgroup (MulAut V)} (hD₁ : IsSylowOf 2 D₁ L) (hne : D₁ ≠ A) :
    ∃ Y₁ : Subgroup (MulAut V), IsSylowOf 2 Y₁ L ∧ Y₁ ≠ A ∧
      (commV D₁ ⊔ fixV (L ⊔ B)).map x.toMonoidHom = commV Y₁ ⊔ fixV (L ⊔ B) := by
  have hD₁D : D₁ ∈ D := ((d.lam.2.2.1 D₁).2 hD₁).1
  have hABab : IsElemAbelian2 (A ⊔ B) :=
    isElemAbelian2_sup (h.elemAb A d.memA) (h.elemAb B d.memB) d.comm
  have hxP : x ∈ P := (sup_le (h.le A d.memA) (h.le B d.memB)) hx
  have hxLB : x ∈ L ⊔ B := sup_le_sup_right d.leA B hx
  have hxfix : ∀ z ∈ fixV (L ⊔ B), x z = z := fun z hz => hz x hxLB
  have hxA : conjSub x A = A :=
    FourOneTools.conjSub_eq_of_comm fun a ha => hABab.1 x hx a (Subgroup.mem_sup_left ha)
  have hmap := map_commV_sup_of_fix hxfix D₁
  have hD₁'D : conjSub x D₁ ∈ D := h.conj_mem D₁ hD₁D x hxP
  have hne' : conjSub x D₁ ≠ A := by
    intro heq
    apply hne
    apply FourTwoTools.conjSub_injective x
    rw [heq, hxA]
  obtain ⟨a, ha, y, hy, hay⟩ : ∃ a ∈ A, ∃ y ∈ D₁, a * y ≠ y * a := by
    by_contra hcon
    push Not at hcon
    have hsup : A ⊔ D₁ = L := d.sl.sylow_sup_eq d.one_le d.sylowA hD₁ hne.symm
    have hab : IsElemAbelian2 (A ⊔ D₁) :=
      isElemAbelian2_sup (h.elemAb A d.memA) (h.elemAb D₁ hD₁D) hcon
    rw [hsup] at hab
    apply h.ne_bot A d.memA
    rw [eq_bot_iff]
    intro a ha
    exact Subgroup.mem_bot.2 (d.sl.center_eq_bot d.one_le (d.leA ha) fun z hz =>
      hab.1 z hz a (d.leA ha))
  have hyD' : x * y * x⁻¹ ∈ conjSub x D₁ := mem_conjSub_of_mem hy
  have hnc : a * (x * y * x⁻¹) ≠ (x * y * x⁻¹) * a := by
    intro heq
    apply hay
    have hxa : x * a = a * x := hABab.1 x hx a (Subgroup.mem_sup_left ha)
    have hxia : x⁻¹ * a = a * x⁻¹ := (Commute.inv_left (show Commute x a from hxa)).eq
    have e1 : a * (x * y * x⁻¹) = x * (a * y) * x⁻¹ := by
      calc a * (x * y * x⁻¹) = (a * x) * y * x⁻¹ := by group
        _ = (x * a) * y * x⁻¹ := by rw [hxa]
        _ = x * (a * y) * x⁻¹ := by group
    have e2 : (x * y * x⁻¹) * a = x * (y * a) * x⁻¹ := by
      calc (x * y * x⁻¹) * a = x * y * (x⁻¹ * a) := by group
        _ = x * y * (a * x⁻¹) := by rw [hxia]
        _ = x * (y * a) * x⁻¹ := by group
    rw [e1, e2] at heq
    exact mul_left_cancel (mul_right_cancel heq)
  by_cases hDL : conjSub x D₁ ≤ L
  · exact ⟨conjSub x D₁, (d.lam.2.2.1 _).1 ⟨hD₁'D, hDL⟩, hne', hmap⟩
  · obtain ⟨Ax, hAxD, hAxL, hAxcomm⟩ := exists_comm_sylow h hV d.lam hD₁'D
    have hAxA : Ax ≠ A := by
      intro hEq
      exact hnc (hAxcomm a (by rw [hEq]; exact ha) _ hyD')
    have d' : Hyp413Comm P D M L Ax (conjSub x D₁) n :=
      ⟨d.hyp, d.lam, d.one_le, d.sl, hAxD, hAxL, hD₁'D, hDL, hAxcomm,
        ⟨a, d.leA ha, x * y * x⁻¹, hyD', hnc⟩⟩
    have hD₁'LB : conjSub x D₁ ≤ L ⊔ B := by
      have h3 : conjSub x D₁ ≤ conjSub x (L ⊔ B) := conjSub_mono x (hD₁.1.trans le_sup_left)
      rwa [conjSub_self_of_mem hxLB] at h3
    have hfix_eq : fixV (L ⊔ B) = fixV (L ⊔ conjSub x D₁) := by
      refine Subgroup.eq_of_le_of_card_ge (fixV_anti (sup_le le_sup_left hD₁'LB)) ?_
      have e1 := d.card_fixV
      have e2 := d'.card_fixV
      have hpos : 0 < 2 ^ n := by positivity
      exact (Nat.eq_of_mul_eq_mul_left hpos (e1.symm.trans e2)).ge
    refine ⟨Ax, (d.lam.2.2.1 Ax).1 ⟨hAxD, hAxL⟩, hAxA, ?_⟩
    rw [hmap, hfix_eq]
    exact d'.commV_B_sup_eq.trans d'.commV_sup_eq.symm

theorem exists_mul_mem_cenSection (h : Hyp42 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) (d : Hyp413Comm P D M L A B n) {x : MulAut V} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ c ∈ (A ⊔ B) ⊓ cenSection (commV L ⊔ fixV (L ⊔ B)) (fixV (L ⊔ B)), x = a * c := by
  obtain ⟨D₀, hD₀, hD₀A⟩ := d.sl.exists_sylow_ne d.one_le d.sylowA
  obtain ⟨Y₁, hY₁, hY₁A, hmapx⟩ := d.exists_image_line h hV hx hD₀ hD₀A
  obtain ⟨a, haA, hconj⟩ := d.sl.exists_conj_sylow_of_ne d.one_le d.sylowA hD₀ hY₁ hD₀A hY₁A
  have hD₀D : D₀ ∈ D := ((d.lam.2.2.1 D₀).2 hD₀).1
  have haL : a ∈ L := d.leA haA
  have hafix : ∀ z ∈ fixV (L ⊔ B), a z = z := fun z hz => hz a (Subgroup.mem_sup_left haL)
  have hmapa : (commV D₀ ⊔ fixV (L ⊔ B)).map a.toMonoidHom = commV Y₁ ⊔ fixV (L ⊔ B) := by
    rw [hconj]
    exact map_commV_sup_of_fix hafix D₀
  have hcAB : a⁻¹ * x ∈ A ⊔ B :=
    (A ⊔ B).mul_mem ((A ⊔ B).inv_mem (Subgroup.mem_sup_left haA)) hx
  refine ⟨a, haA, a⁻¹ * x, ⟨hcAB, ?_⟩, (mul_inv_cancel_left a x).symm⟩
  have hcLB : a⁻¹ * x ∈ L ⊔ B := sup_le_sup_right d.leA B hcAB
  have hcω : ∀ u ∈ commV D₀ ⊔ fixV (L ⊔ B), (a⁻¹ * x) u ∈ commV D₀ ⊔ fixV (L ⊔ B) := by
    intro u hu
    have h1 : x u ∈ (commV D₀ ⊔ fixV (L ⊔ B)).map a.toMonoidHom := by
      rw [hmapa, ← hmapx]
      exact ⟨u, hu, rfl⟩
    obtain ⟨u', hu', hu'x⟩ := h1
    have hu'x' : a u' = x u := hu'x
    have : (a⁻¹ * x) u = u' := by
      rw [MulAut.mul_apply, ← hu'x']
      exact MulAut.inv_apply_self _ _ _
    rw [this]
    exact hu'
  have hi : ∀ w : V, w ∈ commV L ⊔ fixV (L ⊔ B) ↔ (a⁻¹ * x) w ∈ commV L ⊔ fixV (L ⊔ B) := by
    intro w
    refine ⟨d.invariant _ hcLB w, fun hcw => ?_⟩
    have := d.invariant _ ((L ⊔ B).inv_mem hcLB) _ hcw
    rwa [MulAut.inv_apply_self] at this
  have hcx : ∀ z ∈ fixV (A ⊔ B), (a⁻¹ * x) z = z := fun z hz => hz _ hcAB
  have hX : fixV (A ⊔ B) = commV A ⊔ fixV (L ⊔ B) := d.commV_sup_eq.symm
  have hsup : A ⊔ D₀ = L := d.sl.sylow_sup_eq d.one_le d.sylowA hD₀ hD₀A.symm
  have hcL : commV L = commV A ⊔ commV D₀ := by rw [← B19.commV_sup, hsup]
  have hW : commV L ⊔ fixV (L ⊔ B) = fixV (A ⊔ B) ⊔ (commV D₀ ⊔ fixV (L ⊔ B)) := by
    rw [hX, hcL, sup_sup_distrib_right]
  have hωX : ∀ u ∈ commV D₀ ⊔ fixV (L ⊔ B), u ∈ fixV (A ⊔ B) → u ∈ fixV (L ⊔ B) := by
    intro u hu huX
    have h1 : u ∈ fixV D₀ :=
      (sup_le (h.quad D₀ hD₀D) (fixV_anti (hD₀.1.trans le_sup_left)) :
        commV D₀ ⊔ fixV (L ⊔ B) ≤ fixV D₀) hu
    have h2 : u ∈ fixV A := fixV_anti (le_sup_left : A ≤ A ⊔ B) huX
    have h3 : u ∈ fixV L := by
      rw [← hsup, sup_comm, fixV_sup]
      exact ⟨h1, h2⟩
    rw [← d.fixV_AB_inf]
    exact ⟨huX, h3⟩
  have hii : ∀ w ∈ commV L ⊔ fixV (L ⊔ B), (a⁻¹ * x) w * w⁻¹ ∈ fixV (L ⊔ B) := by
    intro w hw
    rw [hW] at hw
    obtain ⟨x', hx', w₀, hw₀, rfl⟩ := Subgroup.mem_sup.1 hw
    have h1 : (a⁻¹ * x) (x' * w₀) * (x' * w₀)⁻¹ = (a⁻¹ * x) w₀ * w₀⁻¹ := by
      rw [map_mul, hcx x' hx']
      comm_group
    rw [h1]
    have h2 : (a⁻¹ * x) w₀ * w₀⁻¹ ∈ commV D₀ ⊔ fixV (L ⊔ B) :=
      mul_mem (hcω w₀ hw₀) (inv_mem hw₀)
    have h3 : (a⁻¹ * x) w₀ * w₀⁻¹ ∈ fixV (A ⊔ B) :=
      (four_six d.hyp d.memA d.memB d.ne d.comm).2 (G6.mem_commV_of_mem hcAB w₀)
    exact hωX _ h2 h3
  exact ⟨hi, hii⟩

end Hyp413Comm

end CFSG.CGT.PushingUpLit.BHS
