module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Links
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

@[expose] def NotExc (K : Subgroup H) : Prop :=
  ¬ Nonempty ((↥K ⧸ center ↥K) ≃* alternatingGroup (Fin 7)) ∧
    ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (↥K ⧸ center ↥K) .PSL 2 p f

theorem NotExc.of_cqEquiv {H' : Type} [Group H'] {X : Subgroup H} {K : Subgroup H'}
    (e : (↥X ⧸ center ↥X) ≃* (↥K ⧸ center ↥K)) (hK : NotExc K) : NotExc X := by
  refine ⟨fun ⟨f⟩ => hK.1 ⟨e.symm.trans f⟩, fun ⟨p, f, hp, hp2, hmodel⟩ => hK.2 ⟨p, f, hp, hp2, ?_⟩⟩
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hmodel

theorem Sol78Links.single {L₀ L₁ T₀ T₁ : Subgroup H} {s : H}
    (hT₀ : IsPGroup 2 T₀) (hT₁ : IsPGroup 2 T₁)
    (hL₀ : IsCompIn L₀ (centralizer (T₀ : Set H))) (hL₁ : IsCompIn L₁ (centralizer (T₁ : Set H)))
    (hs : IsPGroup 2 (zpowers s)) (hsN : s ∈ normalizer (T₁ : Set H)) (hsT : s ^ 2 ∈ T₁)
    (hL₀s : IsCompIn L₀ (centralizer ((T₁ ⊔ zpowers s : Subgroup H) : Set H)))
    (hle : L₀ ≤ L₁ ⊔ L₁.map (MulAut.conj s).toMonoidHom)
    (hlayer : L₁ ⊔ L₁.map (MulAut.conj s).toMonoidHom =
      conjClosure L₀ (layerIn (centralizer (T₁ : Set H))))
    (hlink : Sol78Link5a L₁ L₀ s ∨ Sol78Link5b L₁ L₀ s) :
    Sol78Links H 1 (fun i => if i = 0 then L₀ else L₁) (fun i => if i = 0 then T₀ else T₁)
      (fun _ => s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
    · exact ⟨hT₀, hL₀⟩
    · exact ⟨hT₁, hL₁⟩
  · intro i h1 h2
    obtain rfl : i = 1 := le_antisymm h2 h1
    exact ⟨hs, hsN, hsT, hL₀s⟩
  · intro i h1 h2
    obtain rfl : i = 1 := le_antisymm h2 h1
    exact ⟨hle, hlayer⟩
  · intro i h1 h2
    obtain rfl : i = 1 := le_antisymm h2 h1
    exact hlink

@[expose] def Conn (R : Subgroup H → Subgroup H → H → Prop) (K M : Subgroup H) : Prop :=
  ∃ (m : ℕ) (L T : ℕ → Subgroup H) (s : ℕ → H), Sol78Links H m L T s ∧ L 0 = K ∧ L m = M ∧
    ∀ i, 1 ≤ i → i ≤ m → R (L i) (T i) (s i)

section Conn

variable {R : Subgroup H → Subgroup H → H → Prop} {K M N : Subgroup H}

theorem Conn.trans (h₁ : Conn R K M) (h₂ : Conn R M N) : Conn R K N := by
  obtain ⟨a, L, T, s, hl, h0, hm, hR⟩ := h₁
  obtain ⟨b, L', T', s', hl', h0', hm', hR'⟩ := h₂
  have hjoin : L' 0 = L a := h0'.trans hm.symm
  refine ⟨a + b, concat a L L', concat a T T', concat a s s', hl.concat hl' hjoin, ?_, ?_, ?_⟩
  · rw [concat_of_le (Nat.zero_le a)]
    exact h0
  · rw [concat_add hjoin]
    exact hm'
  · intro i hi1 hi
    by_cases hia : i ≤ a
    · rw [concat_of_le hia, concat_of_le hia, concat_of_le hia]
      exact hR i hi1 hia
    · obtain ⟨k, rfl⟩ : ∃ k, i = a + (k + 1) := ⟨i - a - 1, by omega⟩
      rw [concat_add_succ, concat_add_succ, concat_add_succ]
      exact hR' (k + 1) (by omega) (by omega)

theorem Conn.exists_inj (hc : Conn R K M) :
    ∃ (m : ℕ) (L T : ℕ → Subgroup H) (s : ℕ → H), Sol78Links H m L T s ∧ L 0 = K ∧ L m = M ∧
      (∀ i, 1 ≤ i → i ≤ m → R (L i) (T i) (s i)) ∧ ∀ i ≤ m, ∀ j ≤ m, L i = L j → i = j := by
  classical
  obtain ⟨L, T, s, hl, h0, hm, hR⟩ := Nat.find_spec (show ∃ m, ∃ (L T : ℕ → Subgroup H)
    (s : ℕ → H), Sol78Links H m L T s ∧ L 0 = K ∧ L m = M ∧
      ∀ i, 1 ≤ i → i ≤ m → R (L i) (T i) (s i) from hc)
  refine ⟨_, L, T, s, hl, h0, hm, hR, ?_⟩
  by_contra hcon
  push Not at hcon
  have hex : ∃ m, ∃ (L T : ℕ → Subgroup H) (s : ℕ → H), Sol78Links H m L T s ∧ L 0 = K ∧
      L m = M ∧ ∀ i, 1 ≤ i → i ≤ m → R (L i) (T i) (s i) := hc
  have key : ∃ i j, i < j ∧ j ≤ Nat.find hex ∧ L i = L j := by
    obtain ⟨i, hi, j, hj, hij, hne⟩ := hcon
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, hj, hij⟩
    · exact ⟨j, i, h, hi, hij.symm⟩
  obtain ⟨i, j, hij, hj, hLij⟩ := key
  set m := Nat.find hex with hmdef
  have hjoin : (fun k => L (j + k)) 0 = L i := by
    simp only [Nat.add_zero]
    exact hLij.symm
  have hnew := (hl.mono (show i ≤ m by omega)).concat (hl.shift j hj) hjoin
  have hlt : i + (m - j) < m := by omega
  refine Nat.find_min hex hlt ⟨concat i L (fun k => L (j + k)), concat i T (fun k => T (j + k)),
    concat i s (fun k => s (j + k)), hnew, ?_, ?_, ?_⟩
  · rw [concat_of_le (Nat.zero_le _)]
    exact h0
  · rw [concat_add hjoin, show j + (m - j) = m by omega]
    exact hm
  · intro k hk1 hk
    by_cases hki : k ≤ i
    · rw [concat_of_le hki, concat_of_le hki, concat_of_le hki]
      exact hR k hk1 (by omega)
    · obtain ⟨k', rfl⟩ : ∃ k', k = i + (k' + 1) := ⟨k - i - 1, by omega⟩
      rw [concat_add_succ, concat_add_succ, concat_add_succ]
      exact hR (j + (k' + 1)) (by omega) (by omega)

end Conn

@[expose] def JConn (K M : Subgroup H) : Prop :=
  ∃ (m : ℕ) (L T : ℕ → Subgroup H) (s : ℕ → H), Sol78Links H m L T s ∧ L 0 = K ∧ L m = M ∧
    (∀ i, 1 ≤ i → i ≤ m → T i ≠ ⊥) ∧ (K ≤ M → ∀ i, 1 ≤ i → i ≤ m → L i ≤ M)

theorem JConn.toConn {K M : Subgroup H} (hc : JConn K M) :
    Conn (fun L T _ => T ≠ ⊥ ∧ (K ≤ M → L ≤ M)) K M := by
  obtain ⟨m, L, T, s, hl, h0, hm, hT, hLM⟩ := hc
  exact ⟨m, L, T, s, hl, h0, hm, fun i h1 h2 => ⟨hT i h1 h2, fun hKM => hLM hKM i h1 h2⟩⟩

theorem JConn.exists_inj {K M : Subgroup H} (hc : JConn K M) :
    ∃ (m : ℕ) (L T : ℕ → Subgroup H) (s : ℕ → H), Sol78Links H m L T s ∧ L 0 = K ∧ L m = M ∧
      (∀ i, 1 ≤ i → i ≤ m → T i ≠ ⊥) ∧ (K ≤ M → ∀ i, 1 ≤ i → i ≤ m → L i ≤ M) ∧
      ∀ i ≤ m, ∀ j ≤ m, L i = L j → i = j := by
  obtain ⟨m, L, T, s, hl, h0, hm, hR, hinj⟩ := hc.toConn.exists_inj
  exact ⟨m, L, T, s, hl, h0, hm, fun i h1 h2 => (hR i h1 h2).1,
    fun hKM i h1 h2 => (hR i h1 h2).2 hKM, hinj⟩

end CFSG.EvenSporadicStandard.Induction.Junction
