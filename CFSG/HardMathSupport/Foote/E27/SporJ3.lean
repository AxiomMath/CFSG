module

public import CFSG.HardMathSupport.Foote.E27.SporSylowCheck
public import CFSG.HardMathSupport.Foote.E27.SporKill
public import CFSG.Sporadic.Schreier.PairJ3Order
public import Certificates.Certificate131001
public import CFSG.HardMathSupport.Foote.E27.SporSylowBound

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem tp_mem_genOf_of_word {n : ℕ} (hn : n < 2 ^ 32) {gs : List Table}
    (hg : ∀ g ∈ gs, permOK n g = true) {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ gs.length)
    {t : Table} (ht : permOK n t = true) (h : tblEq n (wordTbl n gs w) t = true) :
    tp n t ∈ genOf n gs := by
  obtain ⟨x, hx, hrep⟩ := rep_wordTbl hn hg w hw
  have := (tblEq_iff_eq hrep (rep_tp ht)).1 h
  rwa [← this]

section Certificates


set_option maxRecDepth 100000 in
theorem j3_sylow_facts :
    ∃ T : Subgroup (Equiv.Perm (Fin 6156)), T ≤ j3P ∧ Nat.card T = 243 ∧
      ∀ s ∈ T, s ^ 3 = 1 → s ≠ 1 →
        81 ∣ Nat.card ↥(T ⊓ centralizer ({s} : Set (Equiv.Perm (Fin 6156)))) ∨
          ∃ D : Subgroup (Equiv.Perm (Fin 6156)), D ≤ centralizer ({s} : Set (Equiv.Perm (Fin 6156))) ∧
            D ≤ j3P ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  have hOK : j3SylOK = true := Certificates.certificate131001
  simp only [j3SylOK, Bool.and_eq_true] at hOK
  obtain ⟨⟨⟨hperm, harr⟩, hwords⟩, hsyl⟩ := hOK
  have hn : 6156 < 2 ^ 32 := by norm_num
  have hgen : ∀ g ∈ j3GenTbls, permOK 6156 g = true := fun g hg => List.all_eq_true.1 hperm g hg
  have hsyl' := hsyl
  simp only [sylowCentWitOK, Bool.and_eq_true] at hsyl'
  obtain ⟨⟨⟨hsg, -⟩, hws⟩, -⟩ := hsyl'
  have hgen0 : natArr (hexT 4 6156 0 j3StrongHex) = j3StrongArrs[0]! ∧
      natArr (hexT 4 6156 6156 j3StrongHex) = j3StrongArrs[1]! := by
    have := harr
    simp only [j3GenTbls, List.map_cons, List.map_nil, beq_iff_eq, List.cons.injEq,
      and_true] at this
    exact this
  have htp0 : tp 6156 (hexT 4 6156 0 j3StrongHex) = j3Gen 0 := by
    show CFSG.Monster.B.Co2.permOfArr 6156 (natArr (hexT 4 6156 0 j3StrongHex)) = _
    rw [hgen0.1]; rfl
  have htp1 : tp 6156 (hexT 4 6156 6156 j3StrongHex) = j3Gen 1 := by
    show CFSG.Monster.B.Co2.permOfArr 6156 (natArr (hexT 4 6156 6156 j3StrongHex)) = _
    rw [hgen0.2]; rfl
  have hJ : genOf 6156 j3GenTbls = j3P := by
    unfold genOf j3P
    apply le_antisymm
    · rw [closure_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ j3GenTbls := List.mem_toArray.1 hx
      simp only [j3GenTbls, List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with h | h
      · rw [h, htp0]; exact subset_closure (Set.mem_insert _ _)
      · rw [h, htp1]; exact subset_closure (Set.mem_insert_of_mem _ rfl)
    · rw [closure_le]
      rintro _ (rfl | rfl)
      · exact subset_closure ⟨_, List.mem_toArray.2 (by simp [j3GenTbls]), htp0⟩
      · exact subset_closure ⟨_, List.mem_toArray.2 (by simp [j3GenTbls]), htp1⟩
  have hpair : ∀ p ∈ j3WordPairs, tp 6156 p.2 ∈ j3P := by
    intro p hp
    have h := List.all_eq_true.1 hwords p hp
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hl, hperm2⟩, heq⟩ := h
    rw [← hJ]
    refine tp_mem_genOf_of_word hn hgen (w := p.1) (fun l hl' => ?_) hperm2 heq
    have := hl l hl'
    simpa [j3GenTbls] using this
  have hpair6 := hpair
  simp only [j3WordPairs, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at hpair6
  obtain ⟨h0, h1, h3, h4, h6, h7⟩ := hpair6
  have hT_le : genOf 6156 j3SylGens ≤ j3P := by
    unfold genOf
    rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ j3SylGens := List.mem_toArray.1 hx
    simp only [j3SylGens, List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with h | h
    · rw [h]; exact h0
    · rw [h]; exact h1
  obtain ⟨hcard, hprop⟩ := sylowCentWitOK_spec hn hsyl
  refine ⟨genOf 6156 j3SylGens, hT_le, hcard, fun s hs hs3 hs1 => ?_⟩
  rcases hprop s hs hs3 hs1 with h81 | ⟨w, hw, P, hP, hsP, hax, hbx, ha2, hb3, hab5, hb1⟩
  · exact Or.inl h81
  · right
    have hw' : (w.a = j3SylTbl 3 ∧ w.b = j3SylTbl 4) ∨ (w.a = j3SylTbl 6 ∧ w.b = j3SylTbl 7) := by
      simp only [j3Wits, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | h
      · exact Or.inl ⟨congrArg Wit235.a h, congrArg Wit235.b h⟩
      · exact Or.inr ⟨congrArg Wit235.a h, congrArg Wit235.b h⟩
    have hab : tp 6156 w.a ∈ j3P ∧ tp 6156 w.b ∈ j3P := by
      rcases hw' with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha, hb]; exact ⟨h3, h4⟩
      · rw [ha, hb]; exact ⟨h6, h7⟩
    obtain ⟨D, hD, hDp, hD3, hDJ⟩ :=
      exists_perfect_of_pair P (tp 6156 w.x) (tp 6156 w.a) (tp 6156 w.b) hax hbx ha2 hb3 hab5 hb1
    exact ⟨D, hsP ▸ hD, hDJ j3P (hT_le hP) hab.1 hab.2, hDp, hD3⟩


theorem E27Config.false_of_j3 {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.J3) :
    False := by
  have e' : ↥K ≃* ↥j3P := e.trans j3PermEquiv
  obtain ⟨T, hTJ, hT243, hprop⟩ := j3_sylow_facts
  have hcardJ : Nat.card j3P = 50232960 := card_j3P
  have hfac : (Nat.card j3P).factorization 3 = 5 := by
    have h5 : 50232960 = 3 ^ 5 * 206720 := by norm_num
    rw [hcardJ, h5, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hT : Nat.card T = 3 ^ (Nat.card j3P).factorization 3 := by rw [hT243, hfac]; norm_num
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  exact h.false_of_sylow_kill hz S₀ fun s hs hs3 =>
    sylow_kill_of_equiv_ambient j3P e' T hTJ hT hprop S₀ hs hs3

theorem E27Config.false_of_sporadic_j3 {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group))
    (e : ↥K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) : False :=
  h.false_of_j3 hz (e.trans hbr.some.symm)

end Certificates

end CFSG.HardMathSupport.Foote.E27
