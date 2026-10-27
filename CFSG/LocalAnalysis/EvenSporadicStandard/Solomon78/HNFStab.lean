module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSetup

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.HNSchreier CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.HNSchreier.Native

@[expose] noncomputable def hnfStabElem (k : ℕ) : ↥JH := wordProd hnfGen hnfStabWords[k]!

@[expose] noncomputable def hnfT : Subgroup ↥JH := Subgroup.closure {hnfStabElem 0, hnfStabElem 1}

theorem hnfStabWords_ok : ∀ k < 2, plettersOK 3 hnfStabWords[k]! = true := by decide

theorem hnfStabWords_size : hnfStabWords.size = 2 := by decide

theorem wordProd_mem_hnfC0 {w : List ℤ} (hw : plettersOK 3 w = true) :
    wordProd hnfGen w ∈ hnfC0 := by
  induction w with
  | nil => simp [wordProd]
  | cons l w ih =>
    have hw' := plettersOK_iff.1 hw
    have hl := hw' l (List.mem_cons_self)
    have hrest : plettersOK 3 w = true :=
      plettersOK_iff.2 fun x hx => hw' x (List.mem_cons_of_mem _ hx)
    rw [wordProd_cons]
    refine mul_mem ?_ (ih hrest)
    unfold letterVal
    by_cases hpos : 0 < l
    · rw [ite_eq_left hpos]
      exact hnfGen_mem (by omega)
    · rw [ite_eq_right hpos]
      exact inv_mem (hnfGen_mem (by omega))

theorem hnfStabElem_mem {k : ℕ} (hk : k < 2) : hnfStabElem k ∈ hnfC0 :=
  wordProd_mem_hnfC0 (hnfStabWords_ok k hk)

section Stab

attribute [local irreducible] pword pcomp pinvCand

variable
  {tA tAi tB tBi g1 g1i g2 g2i : Array Nat}

theorem hnfStabCore_sound (h : TabHyp tA tAi tB tBi g1 g2)
    (hc : hnfStabCore tA tAi tB tBi g1 g1i g2 g2i = true) :
    240 ≤ Nat.card ↥(hnfC0 ⊓ centralizer ({hnfRep hnfRepWords[8]!} : Set ↥JH)) := by
  have := finite_JH
  unfold hnfStabCore at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨htab, -⟩, hcomm⟩, hwalk⟩ := hc
  obtain ⟨hA, hAi, hB, hBi, hg1, hg1i, hg2, hg2i⟩ := h.prep htab
  set G : Array (Array Nat) := #[tA, g1, g2] with hGdef
  set Ginv : Array (Array Nat) := #[tAi, g1i, g2i] with hGidef
  set s : Array (Array Nat) := hnfStabWords.map fun w => pword hnfN G Ginv w with hsdef
  have hGp : ∀ k < 3, PRep hnfN G[k]! (permHom (hnfGen k)) := by
    intro k hk
    interval_cases k
    · rw [hnfGen_zero]; exact hA
    · rw [hnfGen_one]; exact hg1
    · rw [hnfGen_two]; exact hg2
  have hGip : ∀ k < 3, PRep hnfN Ginv[k]! (permHom (hnfGen k))⁻¹ := by
    intro k hk
    interval_cases k
    · rw [hnfGen_zero]; exact hAi
    · rw [hnfGen_one]; exact hg1i
    · rw [hnfGen_two]; exact hg2i
  have hsz : s.size = 2 := by rw [hsdef, Array.size_map, hnfStabWords_size]
  have hsp : ∀ k < 2, PRep hnfN s[k]! (permHom (hnfStabElem k)) := by
    intro k hk
    have e : s[k]! = pword hnfN G Ginv hnfStabWords[k]! := by
      rw [hsdef, getElem!_pos _ k (by rw [Array.size_map, hnfStabWords_size]; exact hk),
        Array.getElem_map, ← getElem!_pos hnfStabWords k (by rw [hnfStabWords_size]; exact hk)]
    rw [e]
    exact prep_pword_prod permHom hnfGen hGp hGip _ (hnfStabWords_ok k hk)
  have hbeta := hnfRepTab_prep h htab (hnfRepWords_ok 8 (by norm_num))
  have hcom : ∀ k < 2, hnfStabElem k ∈ centralizer ({hnfRep hnfRepWords[8]!} : Set ↥JH) := by
    intro k hk
    have hk' : k < s.size := by rw [hsz]; exact hk
    have hall := Array.all_eq_true.1 hcomm k hk'
    rw [← getElem!_pos s k hk'] at hall
    have := (peq_iff (prep_pcomp (hsp k hk) hbeta) (prep_pcomp hbeta (hsp k hk))).1 hall
    exact mem_centralizer_of_map_commute permHom permHom_injective this
  have hlt : hnfStabSeed < hnfN := by decide
  let ω₀ : X := ⟨hnfStabSeed, hlt⟩
  have hstep : ∀ k < 2, ∀ p : X,
      (fun q : X => #[(q : ℕ)]) ((fun k q => permHom (hnfStabElem k) q) k p) =
        hnfPtStep s k ((fun q : X => #[(q : ℕ)]) p) := by
    intro k hk p
    unfold hnfPtStep
    have e : (#[(p : ℕ)] : Array Nat)[0]! = (p : ℕ) := rfl
    simp only [e]
    rw [(hsp k hk).apply p.2]
    rfl
  obtain ⟨L, hnd, hlen, hreach⟩ := hnfWalk_sound' (m := 2)
    (act := fun k q => permHom (hnfStabElem k) q) (st := fun q : X => #[(q : ℕ)])
    (step := hnfPtStep s) (key := fun S => S[0]!) hstep ω₀ (hnfDecodeMoves hnfStabMovesStr)
    hnfStabN hwalk
  have hgen : ∀ k < 2, hnfStabElem k ∈ hnfT := by
    intro k hk
    interval_cases k
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hreachT : ∀ p : X, HNFReach 2 (fun k q => permHom (hnfStabElem k) q) ω₀ p →
      ∃ t ∈ hnfT, permHom t ω₀ = p := by
    intro p hp
    induction hp with
    | base => exact ⟨1, one_mem _, by simp⟩
    | step hg _ ih =>
      obtain ⟨t, ht, rfl⟩ := ih
      exact ⟨hnfStabElem _ * t, mul_mem (hgen _ hg) ht, by simp [map_mul]⟩
  have hsub : (L.toFinset : Set X) ⊆ Set.range (fun t : ↥hnfT => permHom (t : ↥JH) ω₀) := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := hreachT p (hreach p (by simpa using hp))
    exact ⟨⟨t, ht⟩, rfl⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen] at h1
  have h2 : Nat.card (Set.range (fun t : ↥hnfT => permHom (t : ↥JH) ω₀)) ≤ Nat.card ↥hnfT :=
    Finite.card_range_le _
  have h3 : Nat.card ↥hnfT ≤
      Nat.card ↥(hnfC0 ⊓ centralizer ({hnfRep hnfRepWords[8]!} : Set ↥JH)) := by
    apply Subgroup.card_le_of_le
    unfold hnfT
    rw [Subgroup.closure_le]
    have hmem : ∀ k < 2, hnfStabElem k ∈ hnfC0 ⊓ centralizer ({hnfRep hnfRepWords[8]!} : Set ↥JH) :=
      fun k hk => Subgroup.mem_inf.2 ⟨hnfStabElem_mem hk, hcom k hk⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hmem 0 (by norm_num)
    · rw [hx]; exact hmem 1 (by norm_num)
  have h4 : hnfStabN = 240 := rfl
  rw [Nat.card_coe_set_eq] at h2
  omega

end Stab

end CFSG.EvenSporadicStandard.Solomon78
