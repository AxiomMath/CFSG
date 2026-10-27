module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IsolatedBlocks
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.CoreGenAbs
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderOfNatural
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.SFourClosure

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Quasithin.A4 CFSG.Open
  CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
open CFSG.HardMathSupport.RichardWeiss.Coordinator

variable {G : Type} [Group G] [Finite G]

theorem false_of_isolated_blocks {S L : Subgroup G}
    (hA : Asc81bHyp (L ⊔ S) S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) {d : ℕ} (hd : 5 ≤ d)
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hπ : Function.Surjective π)
    (hker : π.ker =
      (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅blockV S L, L⁆)
    (hAlt : ∀ σ ∈ alternatingGroup (Fin d),
      ∃ l : ↥L, θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ = σ)
    (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hD : EOffenderData S (blockV S L))
    (a a' : Fin 3 → Fin d) (hne : ∀ i, a i ≠ a' i)
    (hdisj : ∀ i j, i ≠ j → a i ≠ a j ∧ a i ≠ a' j ∧ a' i ≠ a j ∧ a' i ≠ a' j)
    (hJ : ∀ i, ∃ j : ↥(L ⊔ S), (j : G) ∈ thompsonJ S ∧ θ j = swap (a i) (a' i))
    (hS : ∀ s : ↥(L ⊔ S), (s : G) ∈ S → ∀ i,
      (θ s (a i) = a i ∨ θ s (a i) = a' i) ∧ (θ s (a' i) = a i ∨ θ s (a' i) = a' i))
    (hne' : ⁅omegaOneCenterOf (thompsonJ S), S⁆ ≠ ⊥) : False := by
  classical
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L
  have hUV : ⁅blockV S L, L⁆ ≤ blockV S L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    have := (Subgroup.mem_normalizer_iff.1 (hMV ((le_sup_left : L ≤ L ⊔ S) hl)) v⁻¹).1
      ((blockV S L).inv_mem hv)
    simpa [mul_assoc] using (blockV S L).mul_mem hv this
  have hcen : ∀ m : ↥(L ⊔ S), (m : G) ∈ Subgroup.centralizer (blockV S L : Set G) → θ m = 1 :=
    fun m hm => (theta_eq_one_iff hd hπ hequiv hUV hθV m).2 hm
  have hAlt' : ∀ σ ∈ alternatingGroup (Fin d), ∃ m : ↥(L ⊔ S), θ m = σ := fun σ hσ => by
    obtain ⟨l, hl⟩ := hAlt σ hσ
    exact ⟨_, hl⟩
  have hVJ : blockV S L ≤ thompsonJ S :=
    hD.V_le_eOf.trans ((eOf_le_thompsonJ S _).trans hD.thompsonJ_cenS_le_thompsonJ)
  obtain ⟨t, htJ, ht⟩ := hJ 0
  have hswap : (θ t).IsSwap := ⟨a 0, a' 0, hne 0, ht⟩
  have hZL := commutator_mem_blockV_of_mem_omegaOneCenter hS2 hperf θ hθS hcen hAlt' hD t hswap htJ
  have hXL := commute_commutator_of_mem_omegaOneCenter hS2 hperf θ hθS hθV hcen hAlt' hD t hswap htJ
  have hZC : ∀ z ∈ omegaOneCenterOf (thompsonJ S), ∀ v ∈ blockV S L, z * v = v * z := by
    intro z hz v hv
    exact (Subgroup.mem_centralizer_iff.1 (omegaOneCenterOf_le_centerOf _ hz).2 v (hVJ hv)).symm
  set σ : Perm (Fin d) := swap (a 0) (a 1) * swap (a 1) (a 2) with hσdef
  have h01 : a 0 ≠ a 1 := (hdisj 0 1 (by decide)).1
  have h12 : a 1 ≠ a 2 := (hdisj 1 2 (by decide)).1
  have h02 : a 0 ≠ a 2 := (hdisj 0 2 (by decide)).1
  have hσ3c : σ.IsThreeCycle := by
    have := isThreeCycle_swap_mul_swap_same (a := a 1) (b := a 0) (c := a 2) h01.symm h12 h02
    rwa [swap_comm (a 1) (a 0)] at this
  have hσA : σ ∈ alternatingGroup (Fin d) := mem_alternatingGroup.2 hσ3c.sign
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ3c.orderOf]; exact pow_orderOf_eq_one σ
  obtain ⟨l, hl⟩ := hAlt σ hσA
  set m0 : ↥(L ⊔ S) := ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ with hm0
  have hθm0 : θ m0 = σ := hl
  obtain ⟨n, hn⟩ := exists_pow_eq_one_of_ker hS2 θ hθS (m0 ^ 3) (by rw [map_pow, hθm0, hσ3])
  set g : G := (l : G) ^ 2 ^ n with hg
  have hgL : g ∈ L := L.pow_mem l.2 _
  have hgM : g ∈ L ⊔ S := (le_sup_left : L ≤ L ⊔ S) hgL
  have hgm0 : (⟨g, hgM⟩ : ↥(L ⊔ S)) = m0 ^ 2 ^ n := by
    apply Subtype.ext; simp [hg, hm0]
  have hg3 : g ^ 3 = 1 := by
    have h1 : (m0 ^ 3) ^ 2 ^ n = 1 := hn
    have h2 : (⟨g, hgM⟩ : ↥(L ⊔ S)) ^ 3 = 1 := by
      rw [hgm0, ← pow_mul, mul_comm, pow_mul]; exact h1
    exact congrArg Subtype.val h2
  have hθg : θ ⟨g, hgM⟩ = σ ^ 2 ^ n := by rw [hgm0, map_pow, hθm0]
  have hs2 : σ ^ 2 = σ⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hσ3)
  have hpow2 : ∀ k : ℕ, σ ^ 2 ^ k = σ ∨ σ ^ 2 ^ k = σ⁻¹ := by
    intro k
    induction k with
    | zero => left; simp
    | succ k ih =>
      have e : σ ^ 2 ^ (k + 1) = (σ ^ 2 ^ k) ^ 2 := by rw [pow_succ, pow_mul]
      rcases ih with h | h
      · right; rw [e, h, hs2]
      · left; rw [e, h, inv_pow, hs2, inv_inv]
  have hNσ : σ ^ 2 ^ n ∉ Subgroup.normalizer
      ((((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin d))) :
        Set (Perm (Fin d))) := by
    intro hN
    have hWp : IsPGroup 2 (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) :=
      ((hS2.to_le (thompsonJ_le_self S)).comap_subtype (K := L ⊔ S)).map θ
    have hW1 : swap (a 0) (a' 0) ∈ ((thompsonJ S).subgroupOf (L ⊔ S)).map θ := by
      obtain ⟨j, hj, hθj⟩ := hJ 0
      exact ⟨j, Subgroup.mem_subgroupOf.2 hj, hθj⟩
    have hW2 : swap (a 1) (a' 1) ∈ ((thompsonJ S).subgroupOf (L ⊔ S)).map θ := by
      obtain ⟨j, hj, hθj⟩ := hJ 1
      exact ⟨j, Subgroup.mem_subgroupOf.2 hj, hθj⟩
    refine not_mem_normalizer_of_cycle _ hWp (hne 0) (hne 1) h01 (hdisj 0 1 (by decide)).2.1
      (hdisj 0 1 (by decide)).2.2.1 (hdisj 0 1 (by decide)).2.2.2 h02.symm h12.symm
      (hdisj 0 2 (by decide)).2.2.1.symm hW1 hW2 ?_
    rcases hpow2 n with h | h
    · rwa [h] at hN
    · rw [h] at hN
      have := Subgroup.inv_mem _ hN
      rwa [inv_inv] at this
  have hgT : ∀ x ∉ (Finset.univ.image a : Finset (Fin d)), θ ⟨g, hgM⟩ x = x := by
    intro x hx
    have hx0 : x ≠ a 0 := fun h => hx (Finset.mem_image.2 ⟨0, Finset.mem_univ _, h.symm⟩)
    have hx1 : x ≠ a 1 := fun h => hx (Finset.mem_image.2 ⟨1, Finset.mem_univ _, h.symm⟩)
    have hx2 : x ≠ a 2 := fun h => hx (Finset.mem_image.2 ⟨2, Finset.mem_univ _, h.symm⟩)
    rw [hθg]
    refine Equiv.Perm.pow_apply_eq_self_of_apply_eq_self ?_ _
    rw [hσdef, Perm.mul_apply, swap_apply_of_ne_of_ne hx1 hx2, swap_apply_of_ne_of_ne hx0 hx1]
  have hdecomp : ∀ s ∈ S, ∃ j ∈ thompsonJ S, ∃ δ : ↥(L ⊔ S), (δ : G) ∈ S ∧
      (∀ x ∉ (Finset.univ.filter fun x : Fin d => ∀ i, x ≠ a i ∧ x ≠ a' i), θ δ x = x) ∧
        s = (δ : G) * j := by
    intro s hs
    obtain ⟨j, hjJ, δ, hδS, hfix, hseq⟩ := exists_decomp_of_isolated_blocks θ a a' hne hdisj hJ hS
      Finset.univ ⟨s, (le_sup_right : S ≤ L ⊔ S) hs⟩ hs
    refine ⟨(j : G), hjJ, δ, hδS, ?_, congrArg Subtype.val hseq⟩
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    by_cases h : x = a i
    · rw [h]; exact (hfix i (Finset.mem_univ _)).1
    · have : x = a' i := by_contra fun h' => hi ⟨h, h'⟩
      rw [this]; exact (hfix i (Finset.mem_univ _)).2
  have hTΓ : Disjoint (Finset.univ.image a : Finset (Fin d))
      (Finset.univ.filter fun x : Fin d => ∀ i, x ≠ a i ∧ x ≠ a' i) := by
    rw [Finset.disjoint_left]
    intro x hx hΓ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact (Finset.mem_filter.1 hΓ).2 i |>.1 rfl
  have hfree : ∃ i : Fin d, i ∉ (Finset.univ.image a : Finset (Fin d)) ∧
      i ∉ (Finset.univ.filter fun x : Fin d => ∀ i, x ≠ a i ∧ x ≠ a' i) := by
    refine ⟨a' 0, ?_, ?_⟩
    · intro h
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
      by_cases hi0 : i = 0
      · subst hi0; exact hne 0 hi
      · exact (hdisj i 0 hi0).2.1 hi
    · intro h
      exact ((Finset.mem_filter.1 h).2 0).2 rfl
  exact false_of_small_support_decomposition hA hSL π θ hker hequiv hθS _ _ hfree hTΓ hgL
    (m := 3) (by decide) hg3 hg3 hgT (by rw [hθg]; exact hNσ) hdecomp hZC
    (fun z hz l hl => by rw [commutatorElement_def]; exact hZL z hz l hl) hXL hne'

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
