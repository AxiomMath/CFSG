module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EA16Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8E615Abs

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TS8EA16

open CFSG.EvenSporadicStandard.Fin76b.TS8D8 CFSG.EvenSporadicStandard.Fin76b.E615

variable {Γ : Type*} [Group Γ]

theorem hasChainIx_of_sublist (e : ℕ → Γ) (M : Array (Array ℕ))
    (hmul : ∀ a < 256, ∀ b < 256, mulIx M a b < 256 ∧ e (mulIx M a b) = e a * e b)
    (hinj : ∀ a < 256, ∀ b < 256, e a = e b → a = b)
    {B : Subgroup Γ} (F : Γ → ℕ) (hF : ∀ b ∈ B, F b < 256 ∧ e (F b) = b)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    ∀ (k : ℕ) (S C : List ℕ) (G P : List Γ), G.length = k → List.Sublist (G.map F) C →
      IndepOn P G → (∀ g ∈ G, g ∈ B) → (∀ Y ∈ S, Y < 256 ∧ ∃ p ∈ subProd P, e Y = p) →
      hasChainIx M k S C = true := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro S C G P hlen hsub hInd hA hS
    cases G with
    | nil => simp at hlen
    | cons g G' =>
      have hgB : g ∈ B := hA g (by simp)
      have hsub' : List.Sublist (F g :: G'.map F) C := hsub
      obtain ⟨T, hT, hTsub⟩ := cons_tails_of_sublist' hsub' (F g) (G'.map F) rfl
      have hInd' : g ∉ subProd P ∧ IndepOn (P ++ [g]) G' := hInd
      have hFg := hF g hgB
      have hFgS : F g ∉ S := by
        intro hmem
        obtain ⟨-, p, hp, hpe⟩ := hS (F g) hmem
        have hgp : g = p := hFg.2.symm.trans hpe
        apply hInd'.1
        rw [hgp]
        exact hp
      have hall : ∀ y ∈ G'.map F, commIx M (F g) y = true := by
        intro y hy
        obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hy
        have hg'B : g' ∈ B := hA g' (List.mem_cons_of_mem _ hg')
        have hg'F := hF g' hg'B
        unfold commIx
        rw [beq_iff_eq]
        refine hinj _ (hmul _ hFg.1 _ hg'F.1).1 _ (hmul _ hg'F.1 _ hFg.1).1 ?_
        rw [(hmul _ hFg.1 _ hg'F.1).2, (hmul _ hg'F.1 _ hFg.1).2, hFg.2, hg'F.2]
        exact hcomm g hgB g' hg'B
      have hsubF : List.Sublist (G'.map F) (T.filter fun Y => commIx M (F g) Y) := by
        have h1 := hTsub.filter (fun Y => commIx M (F g) Y)
        rwa [List.filter_eq_self.2 hall] at h1
      have hS' : ∀ Y ∈ spanIx M S (F g), Y < 256 ∧ ∃ p ∈ subProd (P ++ [g]), e Y = p := by
        intro Y hY
        unfold spanIx at hY
        rcases List.mem_append.1 hY with hYS | hYS
        · obtain ⟨hlt, p, hp, hpe⟩ := hS Y hYS
          exact ⟨hlt, p, mem_subProd_snoc_left hp, hpe⟩
        · obtain ⟨Z, hZS, rfl⟩ := List.mem_map.1 hYS
          obtain ⟨hZlt, p, hp, hpe⟩ := hS Z hZS
          refine ⟨(hmul Z hZlt (F g) hFg.1).1, p * g, mul_mem_subProd_snoc hp, ?_⟩
          rw [(hmul Z hZlt (F g) hFg.1).2, hpe, hFg.2]
      have hchoose : hasChainIx M k (spanIx M S (F g)) (T.filter fun Y => commIx M (F g) Y) = true :=
        ih (spanIx M S (F g)) (T.filter fun Y => commIx M (F g) Y) G' (P ++ [g])
          (by simpa using hlen) hsubF hInd'.2 (fun g' hg' => hA g' (List.mem_cons_of_mem _ hg')) hS'
      rw [hasChainIx, List.any_eq_true]
      exact ⟨F g :: T, hT, by simp [hFgS, hchoose]⟩

theorem chain_bound (e : ℕ → Γ) (M : Array (Array ℕ)) (he0 : e 0 = 1)
    (hmul : ∀ a < 256, ∀ b < 256, mulIx M a b < 256 ∧ e (mulIx M a b) = e a * e b)
    (hinj : ∀ a < 256, ∀ b < 256, e a = e b → a = b)
    (hch : hasChainIx M 5 [0] (invsIx M) = false)
    {B : Subgroup Γ} (hB : ∀ b ∈ B, ∃ a, a < 256 ∧ e a = b) (hsq : ∀ b ∈ B, b * b = 1) :
    Nat.card ↥B ≤ 16 := by
  classical
  by_contra hgt
  push_neg at hgt
  let F : Γ → ℕ := fun g => if h : ∃ a, a < 256 ∧ e a = g then h.choose else 0
  have hF : ∀ b ∈ B, F b < 256 ∧ e (F b) = b := by
    intro b hb
    have h := hB b hb
    have hFb : F b = h.choose := dif_pos h
    rw [hFb]
    exact h.choose_spec
  have hinjB : ∀ a ∈ B, ∀ b ∈ B, F a = F b → a = b := by
    intro a ha b hb hab
    rw [← (hF a ha).2, ← (hF b hb).2, hab]
  have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have hab : (a * b) * (a * b) = 1 := hsq _ (B.mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    have hinv : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
    rw [mul_inv_rev, ha', hb'] at hinv
    exact hinv.symm
  have hyp : ∀ b ∈ B, b ∉ subProd ([] : List Γ) → F b ∈ invsIx M := by
    intro b hb hbn
    have hb1 : b ≠ 1 := by
      intro h1
      apply hbn
      rw [h1]
      exact one_mem_subProd []
    obtain ⟨hlt, he⟩ := hF b hb
    have hne : F b ≠ 0 := by
      intro h0
      apply hb1
      rw [← he, h0, he0]
    have hsq' : mulIx M (F b) (F b) = 0 := by
      apply hinj (mulIx M (F b) (F b)) (hmul _ hlt _ hlt).1 0 (by decide)
      rw [(hmul _ hlt _ hlt).2, he, hsq b hb, he0]
    unfold invsIx
    rw [List.mem_filter, List.mem_range]
    exact ⟨hlt, by simp [hne, hsq']⟩
  obtain ⟨G, hG, hGB, hInd, hsub⟩ := exists_chain B F hinjB hgt (invsIx M) [] 5 rfl hyp
  have htrue := hasChainIx_of_sublist e M hmul hinj F hF hcomm 5 [0] (invsIx M) G [] hG hsub hInd
    hGB (by
      intro Y hY
      rw [List.mem_singleton] at hY
      subst hY
      exact ⟨by decide, 1, one_mem_subProd [], he0⟩)
  rw [hch] at htrue
  exact Bool.false_ne_true htrue

end CFSG.EvenSporadicStandard.Fin76b.TS8EA16
