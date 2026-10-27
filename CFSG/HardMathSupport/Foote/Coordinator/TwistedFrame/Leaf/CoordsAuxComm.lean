module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordSpec
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement

set_option linter.unusedSectionVars false


namespace CoordsAux

section Field

variable {τ : Tag} {F : Type} [Field F]

private theorem mul_conj_assoc {G : Type*} [Group G] (x y z : G) :
    x * y * z * y⁻¹ = x * (y * z * y⁻¹) := by
  simp only [mul_assoc]

private theorem conj_pinnedX_highRoot {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Deg1 τ) (t r : F) :
    pinnedX τ F γ t * pinnedX τ F (highRoot τ) r * (pinnedX τ F γ t)⁻¹ =
      pinnedX τ F (highRoot τ) r := by
  rw [← CoordAux.Uθ_comm (mem_rootSubgroup.2 ⟨r, rfl⟩) (CoordAux.pinnedX_mem_pos hγ t),
    mul_inv_cancel_right]

private theorem comm_pinnedX_of_ne {β γ : Fin τ.rank → ℤ} (hβ : β ∈ Deg1 τ) (hγ : γ ∈ Deg1 τ)
    (h : β + γ ≠ highRoot τ) (a b : F) : ⁅pinnedX τ F β a, pinnedX τ F γ b⁆ = 1 := by
  refine commutatorElement_eq_one_iff_commute.2
    (CoordAux.commute_pinnedX_of_not_isRoot_add hβ hγ (fun hr => h ?_) a b)
  refine CoordAux.eq_highRoot_of_two_le (mem_rootFinset.1 hr) ?_
  rw [Pi.add_apply, (CoordAux.mem_Deg1.1 hβ).2, (CoordAux.mem_Deg1.1 hγ).2]
  norm_num

private theorem comm_prodX_pinnedX {l : List (Fin τ.rank → ℤ)} (hD : ∀ β ∈ l, β ∈ Deg1 τ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Deg1 τ) (N : (Fin τ.rank → ℤ) → F)
    (hN : ∀ β ∈ l, β + γ = highRoot τ → ∀ a b : F,
      ⁅pinnedX τ F β a, pinnedX τ F γ b⁆ = pinnedX τ F (highRoot τ) (N β * a * b))
    (c : (Fin τ.rank → ℤ) → F) (b : F) :
    ⁅CoordAux.prodX l c, pinnedX τ F γ b⁆ = pinnedX τ F (highRoot τ)
      (l.map fun β => if β + γ = highRoot τ then N β * c β * b else 0).sum := by
  induction l with
  | nil =>
    rw [CoordAux.prodX_nil, commutatorElement_one_left, List.map_nil, List.sum_nil, pinnedX_zero]
  | cons β l ih =>
    have hβ := hD β List.mem_cons_self
    have hc : ⁅pinnedX τ F β (c β), pinnedX τ F γ b⁆ = pinnedX τ F (highRoot τ)
        (if β + γ = highRoot τ then N β * c β * b else 0) := by
      by_cases h : β + γ = highRoot τ
      · rw [if_pos h]
        exact hN β List.mem_cons_self h (c β) b
      · rw [if_neg h, pinnedX_zero]
        exact comm_pinnedX_of_ne hβ hγ h _ _
    rw [CoordAux.prodX_cons, commutatorElement_mul_left_eq_conj_mul,
      ih (fun α hα => hD α (List.mem_cons_of_mem _ hα))
        (fun α hα => hN α (List.mem_cons_of_mem _ hα)),
      conj_pinnedX_highRoot hβ, hc, ← pinnedX_add, List.map_cons, List.sum_cons, add_comm]

private theorem comm_prodX_prodX_list {l l' : List (Fin τ.rank → ℤ)}
    (hD : ∀ β ∈ l, β ∈ Deg1 τ) (hD' : ∀ β ∈ l', β ∈ Deg1 τ) (N : (Fin τ.rank → ℤ) → F)
    (hN : ∀ β ∈ l, ∀ γ ∈ l', β + γ = highRoot τ → ∀ a b : F,
      ⁅pinnedX τ F β a, pinnedX τ F γ b⁆ = pinnedX τ F (highRoot τ) (N β * a * b))
    (c c' : (Fin τ.rank → ℤ) → F) :
    ⁅CoordAux.prodX l c, CoordAux.prodX l' c'⁆ = pinnedX τ F (highRoot τ)
      (l'.map fun γ => (l.map fun β =>
        if β + γ = highRoot τ then N β * c β * c' γ else 0).sum).sum := by
  induction l' with
  | nil =>
    rw [CoordAux.prodX_nil, commutatorElement_one_right, List.map_nil, List.sum_nil,
      pinnedX_zero]
  | cons γ l' ih =>
    have hγ := hD' γ List.mem_cons_self
    rw [CoordAux.prodX_cons, commutatorElement_mul_right_eq_mul_conj,
      comm_prodX_pinnedX hD hγ N (fun β hβ h => hN β hβ γ List.mem_cons_self h) c (c' γ),
      ih (fun α hα => hD' α (List.mem_cons_of_mem _ hα))
        (fun β hβ α hα => hN β hβ α (List.mem_cons_of_mem _ hα)),
      mul_conj_assoc, conj_pinnedX_highRoot hγ, ← pinnedX_add, List.map_cons, List.sum_cons]

theorem comm_prodX_prodX {l l' : List (Fin τ.rank → ℤ)} (hl : l.Nodup) (hl' : l'.Nodup)
    (hD : ∀ β ∈ l, β ∈ Deg1 τ) (hD' : ∀ β ∈ l', β ∈ Deg1 τ) (N : (Fin τ.rank → ℤ) → F)
    (hN : ∀ β ∈ l, ∀ γ ∈ l', β + γ = highRoot τ → ∀ a b : F,
      ⁅pinnedX τ F β a, pinnedX τ F γ b⁆ = pinnedX τ F (highRoot τ) (N β * a * b))
    (c c' : (Fin τ.rank → ℤ) → F) :
    ⁅CoordAux.prodX l c, CoordAux.prodX l' c'⁆ = pinnedX τ F (highRoot τ)
      (∑ β ∈ l.toFinset, if highRoot τ - β ∈ l' then N β * c β * c' (highRoot τ - β) else 0) := by
  rw [comm_prodX_prodX_list hD hD' N hN c c']
  congr 1
  have key : ∀ β, (∑ γ ∈ l'.toFinset, if β + γ = highRoot τ then N β * c β * c' γ else 0) =
      if highRoot τ - β ∈ l' then N β * c β * c' (highRoot τ - β) else 0 := by
    intro β
    by_cases hm : highRoot τ - β ∈ l'
    · rw [if_pos hm, Finset.sum_eq_single (highRoot τ - β)]
      · rw [if_pos (add_sub_cancel β (highRoot τ))]
      · intro γ _ hne
        refine if_neg fun h => hne ?_
        rw [← h, add_sub_cancel_left]
      · intro h
        exact absurd (List.mem_toFinset.2 hm) h
    · rw [if_neg hm]
      refine Finset.sum_eq_zero fun γ hγ => if_neg fun h => hm ?_
      rw [← h, add_sub_cancel_left]
      exact List.mem_toFinset.1 hγ
  calc (l'.map fun γ => (l.map fun β =>
        if β + γ = highRoot τ then N β * c β * c' γ else 0).sum).sum
      = ∑ γ ∈ l'.toFinset, ∑ β ∈ l.toFinset,
          if β + γ = highRoot τ then N β * c β * c' γ else 0 := by
        rw [List.sum_toFinset _ hl']
        refine congrArg List.sum (List.map_congr_left fun γ _ => ?_)
        rw [List.sum_toFinset _ hl]
    _ = ∑ β ∈ l.toFinset, ∑ γ ∈ l'.toFinset,
          if β + γ = highRoot τ then N β * c β * c' γ else 0 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun β _ => key β

end Field

section ClassData

private theorem isRoot_highRoot_sub {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : β ∈ Deg1 τ) :
    IsRoot τ (highRoot τ - β) := by
  have hθ := isRoot_highRoot τ
  have hcp : corootPair (highRoot τ) β = 1 := by
    have h := corootPair_mul hθ β
    rw [iform_highRoot_apply, iform_highRoot_apply, (CoordAux.mem_Deg1.1 hβ).2,
      CoordAux.highRoot_degree] at h
    have hne : cθ τ * 2 ≠ 0 := mul_ne_zero (cθ_ne_zero τ) two_ne_zero
    exact mul_right_cancel₀ hne (h.trans (by ring))
  have h := IsRoot.neg (IsRoot.smul (CoordAux.mem_Deg1.1 hβ).1 (rootReflection (highRoot τ)))
  rwa [rootReflection_smul hθ, hcp, one_smul, neg_sub] at h

private theorem ne_highRoot_sub_of_odd {τ : Tag} (i : Fin τ.rank) (hi : highRoot τ i % 2 = 1)
    (β : Fin τ.rank → ℤ) : β ≠ highRoot τ - β := by
  intro h
  have h1 := congrFun h i
  simp only [Pi.sub_apply] at h1
  omega

private theorem exists_pair_comm_simplyLaced {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {β : Fin τ.rank → ℤ} (hβ : β ∈ Deg1 τ)
    (hne : β ≠ highRoot τ - β) (F : Type) [Field F] :
    ∃ N : F, N * N = 1 ∧ ∀ a b : F, ⁅pinnedX τ F β a, pinnedX τ F (highRoot τ - β) b⁆ =
      pinnedX τ F (highRoot τ) (N * a * b) := by
  have hne' : β ≠ -(highRoot τ - β) := by
    intro h
    have h1 := congrFun h (iθ τ)
    have h2 := (CoordAux.mem_Deg1.1 hβ).2
    have h3 := CoordAux.highRoot_degree τ
    simp only [Pi.neg_apply, Pi.sub_apply] at h1
    omega
  have hsum : β + (highRoot τ - β) = highRoot τ := add_sub_cancel β (highRoot τ)
  obtain ⟨h1, -⟩ := simply_laced_root_commutator_unit.{0} τ hτ (CoordAux.mem_Deg1.1 hβ).1
    (isRoot_highRoot_sub hβ) hne hne'
  obtain ⟨hC, hF⟩ := h1 (by rw [hsum]; exact isRoot_highRoot τ)
  refine ⟨(commConst τ β (highRoot τ - β) (1, 1) : F), ?_, fun a b => ?_⟩
  · rcases hC with h | h <;> rw [h] <;> norm_num
  · rw [hF F a b, hsum]

private def f4A : Fin Tag.F4.rank → ℤ := ![1, 0, 0, 0]

private def f4B : Fin Tag.F4.rank → ℤ := ![1, 3, 4, 2]

private theorem f4_deg1_S₁_check : ∀ β ∈ rootFinset Tag.F4, β 0 = 1 →
    CFSG.LieType.Steinberg.Adjoint.iform β (Pi.single 2 1) = 0 →
    CFSG.LieType.Steinberg.Adjoint.iform β (Pi.single 3 1) = 0 → β = f4A ∨ β = f4B := by
  decide +kernel

private theorem f4_deg1_S₁ {β : Fin TwClass.f4Six.tag.rank → ℤ} (hβ : β ∈ Deg1 TwClass.f4Six.tag)
    (hS : β ∈ TwClass.f4Six.S₁) : β = f4A ∨ β = f4B := by
  have h2 := hS.2 (Pi.single (2 : Fin Tag.F4.rank) 1) ⟨isRoot_single Tag.F4 2, by decide⟩
  have h3 := hS.2 (Pi.single (3 : Fin Tag.F4.rank) 1) ⟨isRoot_single Tag.F4 3, by decide⟩
  exact f4_deg1_S₁_check β (mem_rootFinset.2 hβ.1) hβ.2 h2 h3

open CFSG.RankThree.PartOne.KE in
private theorem f4_word_facts :
    (coxeterSystem Tag.F4).wordProd f4LongWord • (Pi.single 0 1 : Fin Tag.F4.rank → ℤ) = f4A ∧
      (coxeterSystem Tag.F4).wordProd f4LongWord • (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) = f4B ∧
      (coxeterSystem Tag.F4).wordProd (f4LongWord ++ [0]) •
        (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) = highRoot Tag.F4 := by
  rw [wordProd_smul_eq_wordMat_mulVec, wordProd_smul_eq_wordMat_mulVec,
    wordProd_smul_eq_wordMat_mulVec]
  decide +kernel

private theorem f4_a2 (F : Type) [Field F] (c d : F) :
    ⁅xUnit Tag.F4 F 0 c, xUnit Tag.F4 F 1 d⁆ =
      weylElt Tag.F4 F 0 1 * xUnit Tag.F4 F 1 (c * d) * (weylElt Tag.F4 F 0 1)⁻¹ :=
  (a2_simple_root_commutatorElement F (by decide) (by decide) c d).1

private theorem f4_comm (F : Type) [Field F] : ∃ N : F, N * N = 1 ∧ ∀ a b : F,
    ⁅pinnedX Tag.F4 F f4A a, pinnedX Tag.F4 F f4B b⁆ =
      pinnedX Tag.F4 F (highRoot Tag.F4) (N * a * b) := by
  obtain ⟨h0, h1, hθ⟩ := f4_word_facts
  obtain ⟨ε₁, hε₁, e₁⟩ :=
    exists_prod_weylElt_mul_pinnedX_mul_inv F f4LongWord (isRoot_single Tag.F4 0)
  obtain ⟨ε₂, hε₂, e₂⟩ :=
    exists_prod_weylElt_mul_pinnedX_mul_inv F f4LongWord (isRoot_single Tag.F4 1)
  obtain ⟨ε₃, hε₃, e₃⟩ :=
    exists_prod_weylElt_mul_pinnedX_mul_inv F (f4LongWord ++ [0]) (isRoot_single Tag.F4 1)
  rw [h0] at e₁
  rw [h1] at e₂
  rw [hθ, List.map_append, List.prod_append] at e₃
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at e₃
  obtain ⟨n, hn⟩ : ∃ n, n = (f4LongWord.map fun i => weylElt Tag.F4 F i 1).prod := ⟨_, rfl⟩
  rw [← hn] at e₁ e₂ e₃
  refine ⟨ε₃ * ε₁ * ε₂, by linear_combination (ε₃ * ε₃ * ε₁ * ε₁) * hε₂ + (ε₃ * ε₃) * hε₁ + hε₃,
    fun a b => ?_⟩
  have ea : pinnedX Tag.F4 F f4A a = n * xUnit Tag.F4 F 0 (ε₁ * a) * n⁻¹ := by
    rw [← pinnedX_single, e₁, ← mul_assoc, hε₁, one_mul]
  have eb : pinnedX Tag.F4 F f4B b = n * xUnit Tag.F4 F 1 (ε₂ * b) * n⁻¹ := by
    rw [← pinnedX_single, e₂, ← mul_assoc, hε₂, one_mul]
  have e : ∀ x : (Module.End F (RootModule Tag.F4 F))ˣ,
      n * (weylElt Tag.F4 F 0 1 * x * (weylElt Tag.F4 F 0 1)⁻¹) * n⁻¹ =
        n * weylElt Tag.F4 F 0 1 * x * (n * weylElt Tag.F4 F 0 1)⁻¹ := fun x => by group
  rw [ea, eb, ← conjugate_commutatorElement, f4_a2, ← pinnedX_single, e, e₃]
  congr 1
  ring

private theorem exists_pair_comm_F4 {β : Fin Tag.F4.rank → ℤ} (hβ : β = f4A ∨ β = f4B)
    (F : Type) [Field F] :
    ∃ N : F, N * N = 1 ∧ ∀ a b : F,
      ⁅pinnedX Tag.F4 F β a, pinnedX Tag.F4 F (highRoot Tag.F4 - β) b⁆ =
        pinnedX Tag.F4 F (highRoot Tag.F4) (N * a * b) := by
  obtain ⟨N, hN, hc⟩ := f4_comm F
  rcases hβ with rfl | rfl
  · have e : highRoot Tag.F4 - f4A = f4B := by decide
    exact ⟨N, hN, fun a b => by rw [e]; exact hc a b⟩
  · have e : highRoot Tag.F4 - f4B = f4A := by decide
    refine ⟨-N, by rw [neg_mul_neg]; exact hN, fun a b => ?_⟩
    rw [e, ← commutatorElement_inv, hc b a, pinnedX_neg]
    congr 1
    ring

theorem exists_pair_comm (c : TwClass) {β : Fin c.tag.rank → ℤ} (hβ : β ∈ Deg1 c.tag)
    (hS : β ∈ c.S₁) (F : Type) [Field F] :
    ∃ N : F, N * N = 1 ∧ ∀ a b : F, ⁅pinnedX c.tag F β a, pinnedX c.tag F (highRoot c.tag - β) b⁆ =
      pinnedX c.tag F (highRoot c.tag) (N * a * b) := by
  cases c with
  | f4Six => exact exists_pair_comm_F4 (f4_deg1_S₁ hβ hS) F
  | e6Six =>
    exact exists_pair_comm_simplyLaced (τ := TwClass.e6Six.tag) (Or.inr (Or.inl rfl)) hβ
      (ne_highRoot_sub_of_odd (τ := Tag.E6) 0 (by decide) β) F
  | e8Ten =>
    exact exists_pair_comm_simplyLaced (τ := TwClass.e8Ten.tag) (Or.inr (Or.inr (Or.inr rfl))) hβ
      (ne_highRoot_sub_of_odd (τ := Tag.E8) 1 (by decide) β) F
  | e8Twelve =>
    exact exists_pair_comm_simplyLaced (τ := TwClass.e8Twelve.tag)
      (Or.inr (Or.inr (Or.inr rfl))) hβ (ne_highRoot_sub_of_odd (τ := Tag.E8) 1 (by decide) β) F

end ClassData

end CoordsAux

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
