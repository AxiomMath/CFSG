module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.YuBasic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section CommOn

variable {V : Type} [CommGroup V] (Y : Subgroup (MulAut V))

@[expose] def commOn (S : Subgroup V) : Subgroup V :=
  Subgroup.closure {w | ∃ g ∈ Y, ∃ s ∈ S, g s * s⁻¹ = w}

variable {Y}

theorem commOn_top : commOn Y ⊤ = commV Y := by
  unfold commOn commV
  congr 1
  ext w
  simp

theorem commOn_mono {S S' : Subgroup V} (h : S ≤ S') : commOn Y S ≤ commOn Y S' :=
  Subgroup.closure_mono fun _ ⟨g, hg, s, hs, e⟩ => ⟨g, hg, s, h hs, e⟩

theorem commOn_le_self {S : Subgroup V} (hS : ∀ g ∈ Y, ∀ s ∈ S, g s ∈ S) : commOn Y S ≤ S := by
  unfold commOn
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, s, hs, rfl⟩
  exact mul_mem (hS g hg s hs) (inv_mem hs)

theorem commOn_le_commV (S : Subgroup V) : commOn Y S ≤ commV Y :=
  (commOn_mono (le_top : S ≤ ⊤)).trans commOn_top.le

theorem commOn_invariant {S : Subgroup V} (hS : ∀ g ∈ Y, ∀ s ∈ S, g s ∈ S) :
    ∀ h ∈ Y, ∀ w ∈ commOn Y S, h w ∈ commOn Y S := by
  intro h hh w hw
  unfold commOn at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨g, hg, s, hs, rfl⟩ := hw
    refine Subgroup.subset_closure ⟨h * g * h⁻¹, Y.mul_mem (Y.mul_mem hh hg) (Y.inv_mem hh),
      h s, hS h hh s hs, ?_⟩
    simp only [MulAut.mul_apply, map_mul, map_inv]
    simp
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem commOn_sup_le {A B : Subgroup V} : commOn Y (A ⊔ B) ≤ commOn Y A ⊔ commOn Y B := by
  unfold commOn
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, s, hs, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hs
  have h1 : g a * a⁻¹ ∈ commOn Y A := Subgroup.subset_closure ⟨g, hg, a, ha, rfl⟩
  have h2 : g b * b⁻¹ ∈ commOn Y B := Subgroup.subset_closure ⟨g, hg, b, hb, rfl⟩
  have : g (a * b) * (a * b)⁻¹ = (g a * a⁻¹) * (g b * b⁻¹) := by
    rw [map_mul, mul_inv_rev]
    ac_rfl
  rw [this]
  exact Subgroup.mul_mem_sup h1 h2

end CommOn

section Irr

variable {V : Type} [CommGroup V] [Finite V] (Y : Subgroup (MulAut V))

omit [Finite V] in
theorem commV_le_commOn_commV [Group.IsPerfect ↥Y] : commV Y ≤ commOn Y (commV Y) :=
  commV_le_of_perfect Y (commOn Y (commV Y)) fun g u =>
    Subgroup.subset_closure ⟨g, g.2, u, u.2, rfl⟩

theorem invariant_irreducible [Group.IsPerfect ↥Y] (hV : ∀ v : V, v ^ 2 = 1)
    (hX : IsShortGroup ↥(yuHol Y)) (hU : shortU ↥(yuHol Y) = (yuInc Y).range)
    (N : Subgroup V) (hN : ∀ g ∈ Y, ∀ n ∈ N, g n ∈ N) (hNU : N ≤ commV Y)
    (hAN : commV Y ⊓ fixV Y ≤ N) : N = commV Y ⊓ fixV Y ∨ N = commV Y := by
  let N_L : Subgroup ↥(yuHol Y) := (N.subgroupOf (commV Y)).map (yuInc Y)
  have hnormal : N_L.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hx
    rw [conj_yuInc]
    refine ⟨⟨(g.1.right : MulAut V) u, apply_mem_commV_self Y g.2.2 u.2⟩, ?_, rfl⟩
    exact hN _ g.2.2 _ hu
  have hle : N_L ≤ shortU ↥(yuHol Y) := by
    rintro _ ⟨u, -, rfl⟩
    exact yuInc_mem_shortU Y hV u
  have hge : shortC ↥(yuHol Y) ≤ N_L := by
    intro x hx
    obtain ⟨u, rfl⟩ : x ∈ (yuInc Y).range := hU ▸ hx.1
    refine ⟨u, ?_, rfl⟩
    show (u : V) ∈ N
    apply hAN
    refine ⟨u.2, fun g hg => ?_⟩
    exact apply_eq_of_yuInc_mem_center Y (g := ⟨g, hg⟩) hx.2
  rcases hX.irreducible N_L hnormal hle hge with h | h
  · left
    refine le_antisymm (fun n hn => ?_) hAN
    have hmem : yuInc Y ⟨n, hNU hn⟩ ∈ N_L := ⟨⟨n, hNU hn⟩, hn, rfl⟩
    rw [h] at hmem
    refine ⟨hNU hn, fun g hg => ?_⟩
    exact apply_eq_of_yuInc_mem_center Y (g := ⟨g, hg⟩) hmem.2
  · right
    refine le_antisymm hNU (fun u hu => ?_)
    have hmem : yuInc Y ⟨u, hu⟩ ∈ shortU ↥(yuHol Y) := yuInc_mem_shortU Y hV ⟨u, hu⟩
    rw [← h] at hmem
    obtain ⟨u', hu', hu'u⟩ := hmem
    have : u' = ⟨u, hu⟩ := yuInc_injective Y hu'u
    subst this
    exact hu'

omit [Finite V] in
theorem inv_sup {A B : Subgroup V} (hA : ∀ g ∈ Y, ∀ a ∈ A, g a ∈ A)
    (hB : ∀ g ∈ Y, ∀ b ∈ B, g b ∈ B) : ∀ g ∈ Y, ∀ x ∈ A ⊔ B, g x ∈ A ⊔ B := by
  intro g hg x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hA g hg a ha) (hB g hg b hb)

@[expose] def UGen (W₀ S : Subgroup V) : Prop :=
  S ≤ W₀ ∧ (∀ g ∈ Y, ∀ s ∈ S, g s ∈ S) ∧ commV Y ≤ commOn Y S

theorem minimal_indecomposable [Group.IsPerfect ↥Y] (hV : ∀ v : V, v ^ 2 = 1)
    (hX : IsShortGroup ↥(yuHol Y)) (hU : shortU ↥(yuHol Y) = (yuInc Y).range)
    (hUA : commV Y ≠ commV Y ⊓ fixV Y) {W₀ S : Subgroup V} (hS : UGen Y W₀ S)
    (hmin : ∀ S', UGen Y W₀ S' → S' ≤ S → S' = S) (A' B' : Subgroup V) (hA'S : A' ≤ S)
    (hB'S : B' ≤ S) (hA'inv : ∀ g ∈ Y, ∀ a ∈ A', g a ∈ A')
    (hB'inv : ∀ g ∈ Y, ∀ b ∈ B', g b ∈ B') (hinf : A' ⊓ B' = ⊥) (hsup : A' ⊔ B' = S) :
    A' = ⊥ ∨ B' = ⊥ := by
  have hA₀inv : ∀ g ∈ Y, ∀ a ∈ commV Y ⊓ fixV Y, g a ∈ commV Y ⊓ fixV Y := by
    intro g hg a ha
    rw [ha.2 g hg]
    exact ha
  have hcommSY : commOn Y S = commV Y :=
    le_antisymm (commOn_le_commV S) hS.2.2
  have key : ∀ A'' B'' : Subgroup V, A'' ≤ S → B'' ≤ S → (∀ g ∈ Y, ∀ a ∈ A'', g a ∈ A'') →
      A'' ⊓ B'' = ⊥ → commOn Y A'' ⊔ commV Y ⊓ fixV Y = commV Y → B'' = ⊥ := by
    intro A'' B'' hA''S hB''S hA''inv hinf'' hNA
    have hinvA : ∀ g ∈ Y, ∀ w ∈ commOn Y A'', g w ∈ commOn Y A'' := commOn_invariant hA''inv
    have hUle : commV Y ≤ commOn Y A'' := by
      have h1 : commV Y ≤ commOn Y (commOn Y A'' ⊔ commV Y ⊓ fixV Y) := by
        rw [hNA]; exact commV_le_commOn_commV Y
      refine h1.trans (commOn_sup_le.trans (sup_le (commOn_le_self hinvA) ?_))
      unfold commOn
      rw [Subgroup.closure_le]
      rintro _ ⟨g, hg, s, hs, rfl⟩
      rw [hs.2 g hg, mul_inv_cancel]
      exact one_mem _
    have hA''UG : UGen Y W₀ A'' := ⟨hA''S.trans hS.1, hA''inv, hUle⟩
    have hA''eq : A'' = S := hmin A'' hA''UG hA''S
    rw [eq_bot_iff, ← hinf'']
    exact le_inf (hB''S.trans hA''eq.ge) le_rfl
  have hNA := invariant_irreducible Y hV hX hU (commOn Y A' ⊔ commV Y ⊓ fixV Y)
    (inv_sup Y (commOn_invariant hA'inv) hA₀inv) (sup_le (commOn_le_commV A') inf_le_left)
    le_sup_right
  have hNB := invariant_irreducible Y hV hX hU (commOn Y B' ⊔ commV Y ⊓ fixV Y)
    (inv_sup Y (commOn_invariant hB'inv) hA₀inv) (sup_le (commOn_le_commV B') inf_le_left)
    le_sup_right
  rcases hNA with hA | hA
  · rcases hNB with hB | hB
    · exfalso
      apply hUA
      refine le_antisymm ?_ inf_le_left
      calc commV Y = commOn Y S := hcommSY.symm
        _ = commOn Y (A' ⊔ B') := by rw [hsup]
        _ ≤ commOn Y A' ⊔ commOn Y B' := commOn_sup_le
        _ ≤ commV Y ⊓ fixV Y := sup_le
          ((le_sup_left (b := commV Y ⊓ fixV Y)).trans hA.le)
          ((le_sup_left (b := commV Y ⊓ fixV Y)).trans hB.le)
    · exact Or.inl (key B' A' hB'S hA'S hB'inv (by rw [inf_comm]; exact hinf) hB)
  · exact Or.inr (key A' B' hA'S hB'S hA'inv hinf hA)

end Irr

end CFSG.CGT.PushingUpLit.CGT6
