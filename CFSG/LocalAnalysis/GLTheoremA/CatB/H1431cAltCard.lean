module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Inputs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (lieOrderBridge_holds)

theorem altS_two_mul_card_alt {m : ℕ} (hm : 2 ≤ m) :
    2 * Nat.card (alternatingGroup (Fin m)) = m.factorial := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem altS_card_alt9 : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  have h := altS_two_mul_card_alt (m := 9) (by norm_num)
  rw [show Nat.factorial 9 = 362880 from by decide] at h
  omega

theorem altS_card_J3
    {S : Type} [Group S] (φ : S ≃* TauCeti.SporadicName.J3.Group) :
    Nat.card S = 50232960 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  calc Nat.card S = Nat.card TauCeti.SporadicName.J3.Group := Nat.card_congr φ.toEquiv
    _ = Nat.card Blueprint.NativeSporadic.J3 := Nat.card_congr e.symm.toEquiv
    _ = 50232960 := CFSG.Sporadic.J3.card_J3

theorem altS_card_lieA
    {S : Type} [Group S] [Finite S] (n : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A n q).Valid)
    (φ : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A n q, hv⟩).Group) :
    Nat.card S = CFSG.Open.orderA n q.card :=
  lieOrderBridge_holds ⟨TauCeti.LieTypeIndex.A n q, hv⟩ S ⟨φ⟩

theorem altS_card_lieB
    {S : Type} [Group S] [Finite S] (n : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B n q).Valid)
    (φ : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group) :
    Nat.card S = CFSG.Open.orderBC n q.card :=
  lieOrderBridge_holds ⟨TauCeti.LieTypeIndex.B n q, hv⟩ S ⟨φ⟩

theorem altS_card_of_isType1430
    {S : Type} [Group S] [Finite S] (i : TauCeti.CFSGIndex) (φ : S ≃* i.Group)
    (h : S8.L84.isType1430 i) :
    Nat.card S = 181440 ∨ Nat.card S = 50232960 ∨ Nat.card S = 1451520 ∨
      Nat.card S = 193709880 ∨ Nat.card S = 1056706560 := by
  cases i with
  | cyclic p hp => rcases h with h | h | h <;> first | exact h.elim | cases h
  | alternating n hn =>
    rcases h with h | h | h
    · have hn9 : n = 9 := h
      subst hn9
      left
      rw [Nat.card_congr φ.toEquiv, altS_card_alt9]
    · cases h
    · exact h.elim
  | sporadic s =>
    rcases h with h | h | h
    · exact h.elim
    · have hs : s = TauCeti.SporadicName.J3 := by injection h
      subst hs
      right; left
      exact altS_card_J3 φ
    · exact h.elim
  | lie j =>
    rcases h with h | h | h
    · cases h
    · cases h
    · rcases j with ⟨d, hv⟩
      cases d with
      | B n q =>
        rcases n with _ | _ | _ | _ | n
        · exact h.elim
        · exact h.elim
        · have hq : q.card = 8 := h
          right; right; right; right
          rw [altS_card_lieB _ q hv φ, hq]
          decide
        · have hq : q.card = 2 := h
          right; right; left
          rw [altS_card_lieB _ q hv φ, hq]
          decide
        · exact h.elim
      | A n q =>
        rcases n with _ | _ | n
        · exact h.elim
        · have hq : q.card = 729 := h
          right; right; right; left
          rw [altS_card_lieA _ q hv φ, hq]
          decide
        · exact h.elim
      | _ => exact h.elim

theorem altS_eq_nine_of_isType1430
    {S : Type} [Group S] [Finite S] (hS : catalogIs S S8.L84.isType1430) {m : ℕ} (hm : 5 ≤ m)
    (e : S ≃* alternatingGroup (Fin m)) : m = 9 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := hS
  have h5 := altS_card_of_isType1430 i f hi
  have hfact : 2 * Nat.card S = m.factorial := by
    rw [Nat.card_congr e.toEquiv]
    exact altS_two_mul_card_alt (by omega)
  have key : ∀ N : ℕ, (N = 181440 ∨ N = 50232960 ∨ N = 1451520 ∨ N = 193709880 ∨
      N = 1056706560) → 2 * N = m.factorial → m = 9 := by
    intro N hN hmN
    have hm12 : m ≤ 12 := by
      by_contra hlt
      have h13 : Nat.factorial 13 ≤ Nat.factorial m := Nat.factorial_le (by omega)
      rw [show Nat.factorial 13 = 6227020800 from by decide] at h13
      rcases hN with rfl | rfl | rfl | rfl | rfl <;> omega
    interval_cases m <;>
      first
        | rfl
        | (exfalso
           rcases hN with rfl | rfl | rfl | rfl | rfl <;>
             simp [Nat.factorial] at hmN)
  exact key _ h5 hfact

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
