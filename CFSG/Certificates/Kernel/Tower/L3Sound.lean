module

public import Certificates.Data.Kernel.Tower.T2
public import CFSG.Certificates.Kernel.Tower.TreeSound

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4.Tower

variable {Y : Type*} [Group Y] {mul2 mulW : Nat → Nat → Nat} {dec : Nat → Y}
  {GS PT IMW FTW b U HM : Nat} {H S X : Nat → Nat}

theorem xbit_le (T k : Nat) : xbit T k ≤ 1 := Nat.and_le_right

theorem famB_parts (h : famB mul2 PT IMW FTW b H S X U HM = true) :
    (∀ i < 4, l16 IMW i < 16384) ∧ b < 16384 ∧ l16 FTW 0 = 0 ∧
      (∀ j < 16, H j < 16384 ∧ bitS HM (H j) = true ∧ bitS HM (Nat.xor (H j) 2) = true) ∧
      ∀ c < 8192, famC mul2 PT IMW FTW b H S X U HM c (l16 FTW c) = true := by
  simp only [famB, Bool.and_eq_true, allB_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, Nat.eq_of_beq_eq_true h3, fun j hj => ⟨(h4 j hj).1.1, (h4 j hj).1.2, (h4 j hj).2⟩,
    h5⟩

theorem famC_parts {c f : Nat} (h : famC mul2 PT IMW FTW b H S X U HM c f = true) :
    (c ≠ 0 → f = mul2 (l16 IMW (ptGi PT c)) (l16 FTW (ptPar PT c))) ∧
      famK H S X U HM (2 * c) (mul2 (2 * c) f) = true ∧
      famK H S X U HM (2 * c + 1) (mul2 (2 * c + 1) (mul2 f b)) = true := by
  simp only [famC, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun hc => ?_, h2, h3⟩
  rcases h1 with h1 | h1
  · exact absurd (Nat.eq_of_beq_eq_true h1) hc
  · exact Nat.eq_of_beq_eq_true h1

theorem famK_sound {k p : Nat} (h : famK H S X U HM k p = true)
    (hHM : ∀ j < 16, bitS HM (H j) = true ∧ bitS HM (Nat.xor (H j) 2) = true)
    (hU : ∀ j < 16, bitS (S j) k = true → bitS U k = true) :
    ∀ j < 16, (bitS (S j) k = true ↔ p ^^^ (2 * xbit (X j) k) = H j) := by
  intro j hj
  unfold famK at h
  cases hp : bitS HM p
  · rw [hp] at h
    change notB (bitS U k) = true at h
    have hUk : bitS U k = false := by
      cases e : bitS U k
      · rfl
      · rw [e] at h
        exact absurd h (by decide)
    constructor
    · intro hs
      rw [hU j hj hs] at hUk
      exact absurd hUk (by decide)
    · intro he
      exfalso
      have he' : p ^^^ (2 * xbit (X j) k) = H j := he
      have hp' : p = H j ^^^ (2 * xbit (X j) k) := by
        rw [← he', Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      have hH1 : bitS HM (H j) = true := (hHM j hj).1
      have hH2 : bitS HM (H j ^^^ 2) = true := (hHM j hj).2
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (xbit_le (X j) k) with hx | hx
      · rw [hx, Nat.mul_zero, Nat.xor_zero] at hp'
        rw [hp', hH1] at hp
        exact absurd hp (by decide)
      · rw [hx, Nat.mul_one] at hp'
        rw [hp', hH2] at hp
        exact absurd hp (by decide)
  · rw [hp] at h
    have h' : allB 16 (fun j => eqB (bitS (S j) k)
        (Nat.beq (p ^^^ (2 * xbit (X j) k)) (H j))) = true := h
    have hj' := allB_eq_true.1 h' j hj
    have key : ∀ b c : Bool, eqB b c = true → b = c := by decide
    rw [key _ _ hj']
    exact ⟨Nat.eq_of_beq_eq_true, fun e => by rw [e]; exact Nat.beq_refl _⟩

theorem famB_table (M : IsModel (⊤ : Subgroup Y) 16384 mul2 dec)
    (hT : treeB 8192 4 mulW GS PT = true)
    (hW : ∀ a < 8192, ∀ c < 8192, mul2 (2 * a) (2 * c) = 2 * mulW a c)
    (hF : famB mul2 PT IMW FTW b H S X U HM = true) (β : Y →* Y)
    (hβ : ∀ i < 4, β (dec (2 * l16 GS i)) = dec (l16 IMW i)) :
    ∀ c < 8192, l16 FTW c < 16384 ∧ β (dec (2 * c)) = dec (l16 FTW c) := by
  obtain ⟨hIM, -, h0, -, hC⟩ := famB_parts hF
  suffices H' : ∀ d, ∀ c < 8192, ptDep PT c = d → l16 FTW c < 16384 ∧
      β (dec (2 * c)) = dec (l16 FTW c) from fun c hc => H' _ c hc rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro c hc hd
    by_cases hc0 : c = 0
    · subst hc0
      rw [h0, Nat.mul_zero, M.dec_zero, map_one]
      exact ⟨by omega, rfl⟩
    · obtain ⟨hgi, hpar, hdep, hmul⟩ := treeB_get hT hc hc0
      obtain ⟨ih1, ih2⟩ := ih _ (hd ▸ hdep) _ hpar rfl
      have hg := treeB_gen hT hgi
      have hi := hIM _ hgi
      rw [(famC_parts (hC c hc)).1 hc0]
      refine ⟨M.mul_lt _ hi _ ih1, ?_⟩
      have e1 : dec (2 * c) = dec (2 * l16 GS (ptGi PT c)) * dec (2 * ptPar PT c) := by
        rw [← M.dec_mul (2 * l16 GS (ptGi PT c)) (by omega) (2 * ptPar PT c) (by omega),
          hW _ hg _ hpar, hmul]
      rw [e1, map_mul, hβ _ hgi, ih2, M.dec_mul _ hi _ ih1]

theorem famB_sound (M : IsModel (⊤ : Subgroup Y) 16384 mul2 dec)
    (hT : treeB 8192 4 mulW GS PT = true)
    (hW : ∀ a < 8192, ∀ c < 8192, mul2 (2 * a) (2 * c) = 2 * mulW a c)
    (h1 : ∀ c < 8192, mul2 (2 * c) 1 = 2 * c + 1)
    (hz : ∀ k < 16384, mul2 2 k = k ^^^ 2)
    (hF : famB mul2 PT IMW FTW b H S X U HM = true)
    (hU : ∀ j < 16, ∀ k, bitS (S j) k = true → bitS U k = true) (β : Y →* Y)
    (hβ : ∀ i < 4, β (dec (2 * l16 GS i)) = dec (l16 IMW i)) (hb : β (dec 1) = dec b) :
    ∀ j < 16, ∀ k < 16384,
      (bitS (S j) k = true ↔ dec 2 ^ xbit (X j) k * (dec k * β (dec k)) = dec (H j)) := by
  obtain ⟨-, hb', -, hH, hC⟩ := famB_parts hF
  have hTab := famB_table M hT hW hF β hβ
  have hHM : ∀ j < 16, bitS HM (H j) = true ∧ bitS HM (Nat.xor (H j) 2) = true :=
    fun j hj => (hH j hj).2
  have key : ∀ k < 16384, ∃ p < 16384, dec p = dec k * β (dec k) ∧
      famK H S X U HM k p = true := by
    intro k hk
    obtain ⟨hf, hβf⟩ := hTab (k / 2) (by omega)
    obtain ⟨-, hK0, hK1⟩ := famC_parts (hC (k / 2) (by omega))
    rcases Nat.mod_two_eq_zero_or_one k with hr | hr
    · have ek : 2 * (k / 2) = k := by omega
      refine ⟨mul2 (2 * (k / 2)) (l16 FTW (k / 2)), M.mul_lt (2 * (k / 2)) (by omega) _ hf, ?_,
        (congrArg (fun x => famK H S X U HM x (mul2 (2 * (k / 2)) (l16 FTW (k / 2))) = true)
          ek).mp hK0⟩
      rw [M.dec_mul (2 * (k / 2)) (by omega) _ hf, ← hβf, ek]
    · have ek : 2 * (k / 2) + 1 = k := by omega
      have hfb := M.mul_lt _ hf _ hb'
      refine ⟨mul2 (2 * (k / 2) + 1) (mul2 (l16 FTW (k / 2)) b),
        M.mul_lt (2 * (k / 2) + 1) (by omega) _ hfb, ?_,
        (congrArg (fun x => famK H S X U HM x
          (mul2 (2 * (k / 2) + 1) (mul2 (l16 FTW (k / 2)) b)) = true) ek).mp hK1⟩
      have e1 : dec k = dec (2 * (k / 2)) * dec 1 := by
        rw [← M.dec_mul (2 * (k / 2)) (by omega) 1 (by omega), h1 (k / 2) (by omega), ek]
      rw [M.dec_mul (2 * (k / 2) + 1) (by omega) _ hfb, M.dec_mul _ hf _ hb', ek, e1, map_mul,
        hβf, hb]
  intro j hj k hk
  obtain ⟨p, hp, hdp, hK⟩ := key k hk
  rw [famK_sound hK hHM (fun j hj => hU j hj k) j hj, ← hdp]
  have hHj := (hH j hj).1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (xbit_le (X j) k) with hx | hx
  · rw [hx, Nat.mul_zero, Nat.xor_zero, pow_zero, one_mul]
    exact (M.eq_iff hp hHj).symm
  · rw [hx, Nat.mul_one, pow_one, ← M.dec_mul 2 (by omega) p hp, hz _ hp]
    have hlt : p ^^^ 2 < 16384 := Nat.xor_lt_two_pow (n := 14) hp (by omega)
    exact (M.eq_iff hlt hHj).symm

end Certificates.KernelTower
