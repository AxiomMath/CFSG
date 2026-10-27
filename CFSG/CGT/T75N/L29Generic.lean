module

public import CFSG.CGT.T75N.L29Kernel
public import CFSG.CGT.T75N.L29TwoFour
public import CFSG.CGT.T75N.L29Exc
public import CFSG.CGT.T75N.L29Transport
public import CFSG.CGT.Timmesfeld75.Sec5Eleven

public section

namespace CFSG.CGT.T75N

open CFSG.Open CFSG.Timmesfeld CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

theorem charP_two_of_card_pow {F : Type} [Field F] [Finite F] {m : ℕ}
    (h : Nat.card F = 2 ^ m) : CharP F 2 := by
  have := Fintype.ofFinite F
  obtain ⟨p, hp⟩ : ∃ p, CharP F p := CharP.exists F
  have hpp : p.Prime := CharP.char_is_prime F p
  obtain ⟨k, -, hk⟩ := FiniteField.card F p
  have h1 : p ^ (k : ℕ) = 2 ^ m := by rw [← hk, ← Nat.card_eq_fintype_card, h]
  have h2 : p ∣ 2 ^ m := by
    rw [← h1]
    exact dvd_pow_self p k.ne_zero
  have h3 : p ∣ 2 := hpp.dvd_of_dvd_pow h2
  have h4 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h3
  rw [h4] at hp
  exact hp

theorem lemma29StdInput :
    Lemma29Input := by
  intro n m hn hm Y _ _ E hperf hWC _ hEZ hE4 hF hstd V _ _ hcomm hexp hcard ρ hρ htrans
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨e₀⟩⟩ := hF
  have hCharP : CharP F 2 := charP_two_of_card_pow hFcard
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 2 := ⟨n - 2, by omega⟩
  let _ : CommGroup V := { ‹Group V› with mul_comm := hcomm }
  have hVcard : Nat.card V = Nat.card F ^ (m' + 2) := by rw [hcard, hFcard]
  let ε : Y ⧸ Subgroup.center Y ≃* PSL(m' + 2, F) :=
    e₀.trans (projectiveSpecialLinearGroupEquivStatedProj (m' + 2) F).symm
  obtain ⟨π, hπsurj, hπker, hcompat, α, hαα, φ, hφ⟩ :=
    lemma29_core hperf ε hexp hVcard ρ hρ htrans
  have : Group.IsPerfect Y := ⟨hperf⟩
  have h8 : 3 ≤ m → 8 ≤ Nat.card F := fun h => by
    rw [hFcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
  have h4 : 2 ≤ m → 4 ≤ Nat.card F := fun h => by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
  have hcenπ : π.ker ≤ Subgroup.center Y := by rw [hπker]; exact hρ
  have hcompat' : ∀ y : Y, projectiveSpecialLinearGroupEquivStatedProj (m' + 2) F
      (QuotientGroup.mk (π y)) = e₀ (QuotientGroup.mk y) := by
    intro y
    rw [hcompat y]
    exact (projectiveSpecialLinearGroupEquivStatedProj (m' + 2) F).apply_symm_apply _
  have hker : π.ker = ⊥ := by
    by_cases h21 : m' = 0 ∧ m = 1
    · obtain ⟨rfl, rfl⟩ := h21
      exact (false_of_perfect_sl_two_two (F := F) (by rw [hFcard]; norm_num) π hπsurj).elim
    by_cases h22 : m' = 0 ∧ m = 2
    · obtain ⟨rfl, rfl⟩ := h22
      refine ker_eq_bot_two_four (F := F) (by rw [hFcard]; norm_num) π hπsurj hcenπ E hWC.1.2 ?_ hE4
      rw [eq_bot_iff, ← hEZ]
      exact inf_le_inf_left E hcenπ
    by_cases hstd1 : (m' = 1 ∧ m = 1) ∨ (m' = 1 ∧ m = 2) ∨ (m' = 2 ∧ m = 1)
    · obtain ⟨hcardstd, hpos⟩ := hstd (by omega) F hFfield hFfin hFcard e₀
      have hexp' : m' + 2 - 1 = m' + 1 := by omega
      rw [hexp'] at hcardstd
      rcases hstd1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ker_eq_bot_of_std (m := 1) (k := 1) hFcard e₀ π hπsurj hcenπ hcompat' hWC hEZ hE4
          hcardstd hpos (hsyl_three_two (by rw [hFcard]; norm_num))
      · exact ker_eq_bot_of_std (m := 1) (k := 2) hFcard e₀ π hπsurj hcenπ hcompat' hWC hEZ hE4
          hcardstd hpos (hsyl_three_four (by rw [hFcard]; norm_num))
      · exact ker_eq_bot_of_std (m := 2) (k := 1) hFcard e₀ π hπsurj hcenπ hcompat' hWC hEZ hE4
          hcardstd hpos (hsyl_four_two (by rw [hFcard]; norm_num))
    · refine ker_eq_bot_of_generic ?_ π hπsurj hcenπ
      by_cases h0 : m' = 0
      · subst h0
        exact Or.inl ⟨rfl, h8 (by omega)⟩
      by_cases h1 : m' = 1
      · subst h1
        exact Or.inr (Or.inl ⟨rfl, h8 (by omega)⟩)
      by_cases h2 : m' = 2
      · subst h2
        exact Or.inr (Or.inr (Or.inl ⟨rfl, h4 (by omega)⟩))
      · exact Or.inr (Or.inr (Or.inr (by omega)))
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
  let αE : SL(m' + 2, F) ≃* SL(m' + 2, F) :=
    MonoidHom.toMulEquiv α α (MonoidHom.ext hαα) (MonoidHom.ext hαα)
  let e1 : Y ≃* SL(m' + 2, F) :=
    (MulEquiv.ofBijective π ⟨hinj, hπsurj⟩).trans αE
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hFcard' : Fintype.card F = Fintype.card (GaloisField 2 m) := by
    rw [← Nat.card_eq_fintype_card, hFcard, ← Nat.card_eq_fintype_card,
      GaloisField.card 2 m (by omega)]
  obtain ⟨e', φ', h'⟩ := transport_natural (m' + 2) (FiniteField.ringEquivOfCardEq hFcard') ρ e1 φ
    (fun y v => hφ y v)
  exact ⟨e', φ', h'⟩

end CFSG.CGT.T75N
