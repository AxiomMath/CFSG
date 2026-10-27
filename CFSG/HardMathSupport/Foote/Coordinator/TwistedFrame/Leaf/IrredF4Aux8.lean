module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredF4Aux7
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredF4Aux4

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K]

theorem two_ne_zero_of_ringChar (hodd : ringChar K ≠ 2) : (2 : K) ≠ 0 := by
  intro h
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, -⟩ := FiniteField.card K (ringChar K)
  have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  have hdvd : ringChar K ∣ 2 := (CharP.cast_eq_zero_iff K (ringChar K) 2).1 h2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
  · exact hp.one_lt.ne' h1
  · exact hodd h1

theorem span_emb_onDeg1 {K L : Type} [Field K] [Field L] [Algebra K L]
    (W : Submodule K ((Fin Tag.F4.rank → ℤ) → K)) (hW : ∀ w ∈ W, OnDeg1 w) :
    ∀ u ∈ Submodule.span L (emb (L := L) '' (W : Set ((Fin Tag.F4.rank → ℤ) → K))), OnDeg1 u := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact emb_onDeg1 (hW w hw)
  | zero => exact fun β _ => rfl
  | add x y _ _ hx hy => exact fun β hβ => by simp [hx β hβ, hy β hβ]
  | smul c x _ hx => exact fun β hβ => by simp [hx β hβ]

theorem main (hK : 3 ≤ Nat.card K) (hodd : ringChar K ≠ 2) (D : LangLevi Tag.F4 K wF) :
    TwIrred (D.frame TwClass.f4Six.S₁) (D.frame TwClass.f4Six.S₂) := by
  classical
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  intro W hWV hst
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  right
  refine le_antisymm hWV ?_
  obtain ⟨a1, a2, h1, h2, hact⟩ := exists_action_data D.L
  obtain ⟨Φ, hΦ⟩ := levi_action (τ := Tag.F4) (L := D.L) (l := D.g⁻¹) (inv_mem D.g_mem)
  have hΦ' : ∀ q ∈ Qθ Tag.F4 D.L, D.g⁻¹ * q * D.g ∈ Qθ Tag.F4 D.L ∧
      heisCoord Tag.F4 D.L (D.g⁻¹ * q * D.g) = Φ (heisCoord Tag.F4 D.L q) := by
    intro q hq
    simpa using hΦ q hq
  let C : Ctx D W := ⟨Φ, hΦ', hWV, hst⟩
  have hsupp := Wb_support C hK hodd
  have hstab := Wb_stab_all C hK hodd h1 h2 hact hsupp
  obtain ⟨ε, hε, hn⟩ := coord_conj_n (τ := Tag.F4) (L := D.L) (w := wF) wF_theta
  have hS := Wb_stab_S C hε hn
  have hembinj : ∀ w : (Fin Tag.F4.rank → ℤ) → K, emb (L := D.L) w = 0 → w = 0 := by
    intro w hw
    funext β
    exact (algebraMap K D.L).injective (by simpa [emb] using congrFun hw β)
  have hne : WbOf C ≠ ⊥ := by
    intro hbot
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hmem : C.Φ (emb w) ∈ WbOf C := by
      rw [WbOf_eq_span]
      exact Submodule.subset_span ⟨w, hw, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    have hon : OnDeg1 (emb (L := D.L) w) := emb_onDeg1 (VM_onDeg1 _ w (hWV hw))
    exact hw0 (hembinj w (Phi_inj D.g_mem hΦ' hon hmem))
  have h2K := two_ne_zero_of_ringChar hodd
  have h2L : (2 : D.L) ≠ 0 := by
    intro h
    apply h2K
    apply (algebraMap K D.L).injective
    rw [map_ofNat, map_zero]
    exact h
  obtain ⟨t, ht0, ht1⟩ := exists_two_ne_of_card K hK
  have hL : ∃ t : D.L, t ≠ 0 ∧ t ≠ 1 :=
    ⟨algebraMap K D.L t, (map_ne_zero _).2 ht0, fun h =>
      ht1 ((algebraMap K D.L).injective (by rw [map_one]; exact h))⟩
  have hε0 : ∀ ν, IsRoot Tag.F4 ν → ε ν ≠ 0 := fun ν hν h => by
    have := hε ν hν
    rw [h] at this
    simp at this
  have hSe : ∀ ν ∈ mRoots, ∀ c : D.L, c ≠ 0 → ∃ ν' ∈ mRoots, ν' 1 ≠ ν 1 ∧
      ∃ c' : D.L, c' ≠ 0 ∧ Sfun D.Fr ε (Pi.single ν c) = Pi.single ν' c' := by
    intro ν hν c hc
    have hνD : ν ∈ Deg1 Tag.F4 :=
      ⟨mem_rootFinset.1 (mRoots_data ν hν).1, (mRoots_data ν hν).2.1⟩
    obtain ⟨hm, hdiff⟩ := wF_mRoots ν hν
    exact ⟨wF • ν, hm, hdiff, ε ν * D.Fr c, mul_ne_zero (hε0 ν hνD.1) ((map_ne_zero D.Fr).2 hc),
      Sfun_single D.Fr ε hνD c⟩
  have hcore := irreducible_core h2L hL h1 h2 (WbOf C)
    (fun v hv ν hne' => by_contra fun hnot => hne' (hsupp v hv ν hnot)) hstab
    (Sfun D.Fr ε) hS hSe hne
  have hMS : ∀ u : (Fin Tag.F4.rank → ℤ) → D.L, (∀ ν, ν ∉ mRoots → u ν = 0) → u ∈ WbOf C := by
    intro u hu
    have hnd : mRoots.Nodup := by decide +kernel
    have hs : ∀ ν, u ν ≠ 0 → ν ∈ mRoots := fun ν hν => by_contra fun hnot => hν (hu ν hnot)
    rw [Words.eq_list_sum hnd hs]
    refine list_sum_mem fun x hx => ?_
    obtain ⟨ν, hν, rfl⟩ := List.mem_map.1 hx
    exact hcore ν hν _
  intro v hv
  have hΦv : C.Φ (emb v) ∈ WbOf C := hMS _ (VM_support C hK hodd v hv)
  obtain ⟨u, hu, huv⟩ := Submodule.mem_map.1 hΦv
  have huD : OnDeg1 u := span_emb_onDeg1 W (fun w hw => VM_onDeg1 _ w (hWV hw)) u hu
  have hvD : OnDeg1 (emb (L := D.L) v) := emb_onDeg1 (VM_onDeg1 _ v hv)
  have hsub : u - emb v = 0 :=
    Phi_inj D.g_mem hΦ' (fun β hβ => by simp [Pi.sub_apply, huD β hβ, hvD β hβ])
      (by rw [map_sub, huv, sub_self])
  have hueq : u = emb v := sub_eq_zero.1 hsub
  exact mem_of_mem_span_map W (hueq ▸ hu)

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux
