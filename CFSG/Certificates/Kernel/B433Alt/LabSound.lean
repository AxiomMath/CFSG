module

public import CFSG.Certificates.Kernel.B433Alt.Sound
public import Certificates.Data.Kernel.B433Alt.Lab

public section

namespace CFSG.KC.B433Alt

open CFSG.YGroups CFSG.KC.B4A CFSG.KC.Y333 CFSG.Certificates.CosetEnumeration

@[expose] noncomputable def genSub (RW : ℕ → ℕ) (G nG : ℕ) : Subgroup (YGroup 4 3 2) :=
  Subgroup.closure (Set.range fun k : Fin nG => wVal (yGen 4 3 2) (RW (fld G (20 * k) (ones 20))))

theorem labS_sN (v : ℕ) (k : ℕ → ℕ) : sN v k = k v := by cases v <;> rfl

theorem labS_andB {a b : Bool} : B4A.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem labS_brec (a b : ℕ) (c : Bool) :
    Bool.rec (motive := fun _ => ℕ) a b c = if c = true then b else a := by
  cases c <;> rfl

theorem labS_land_two_pow (a n : ℕ) : a &&& 2 ^ n = if a.testBit n then 2 ^ n else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hj : n = j
  · subst hj
    by_cases h : a.testBit n <;> simp [h, Nat.testBit_two_pow_self]
  · by_cases h : a.testBit n <;> simp [h, hj, Nat.testBit_two_pow_of_ne hj]

theorem labS_genW {RD RW : ℕ → ℕ} {j G nG k : ℕ}
    (h : 0 < genW RD RW (fun _ => 0) (fun _ => 0) j 0 G nG k) :
    k < nG ∧ isStab (dKind (RD (fld G (20 * k) (ones 20)))) = true ∧
      genW RD RW (fun _ => 0) (fun _ => 0) j 0 G nG k - 1 = RW (fld G (20 * k) (ones 20)) := by
  unfold genW at h ⊢
  simp only [labS_sN] at h ⊢
  cases h1 : Nat.blt k nG
  · simp only [h1] at h
    exact absurd h (lt_irrefl 0)
  · simp only [h1] at h ⊢
    have h2 : Nat.beq 0 0 = true := rfl
    rw [h2] at h ⊢
    cases h3 : B4A.andB (isStab (dKind (RD (fld G (Nat.mul 20 k) (ones 20)))))
        (Nat.beq (dN2 (RD (fld G (Nat.mul 20 k) (ones 20)))) j)
    · rw [h3] at h
      exact absurd h (lt_irrefl 0)
    · rw [labS_andB] at h3
      exact ⟨Nat.blt_eq.mp h1, h3.1, rfl⟩

@[expose] def LabOrbInv (O : Set (Fin 31671)) (S : ℕ) : Prop :=
  S = 0 ∨ ∃ V : Finset (Fin 31671), (∀ p ∈ V, p ∈ O) ∧ S % 2 ^ 32 = V.card ∧
    ∀ q, (S / 2 ^ 32).testBit q = true ↔ ∃ p ∈ V, (p : ℕ) = q

theorem labS_init {O : Set (Fin 31671)} {b : ℕ} (hb : b < 31671) (hbO : ⟨b, hb⟩ ∈ O) :
    LabOrbInv O (orbInit b) := by
  right
  refine ⟨{⟨b, hb⟩}, by simpa using hbO, ?_, fun q => ?_⟩
  · change (1 ||| 1 <<< (b + 32)) % 2 ^ 32 = _
    rw [Nat.one_shiftLeft, Nat.or_two_pow_eq_add_of_lt (Nat.one_lt_two_pow (by omega)),
      pow_add, mul_comm, Nat.add_mul_mod_self_left]
    rfl
  · change ((1 ||| 1 <<< (b + 32)) / 2 ^ 32).testBit q = true ↔ _
    rw [Nat.one_shiftLeft, Nat.or_two_pow_eq_add_of_lt (Nat.one_lt_two_pow (by omega)),
      pow_add, mul_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 32)]
    rw [show (1 : ℕ) / 2 ^ 32 = 0 by norm_num, zero_add, Nat.testBit_two_pow]
    simp [eq_comm]

theorem labS_step {O : Set (Fin 31671)} {S o q : ℕ} (hS : LabOrbInv O S) (hS0 : 0 < S)
    (ho : o < 31671) (hq : 0 < S &&& 2 ^ (q + 32)) (hno : S &&& 2 ^ (o + 32) = 0)
    (hmove : ∀ hq' : q < 31671, ⟨q, hq'⟩ ∈ O → (⟨o, ho⟩ : Fin 31671) ∈ O) :
    LabOrbInv O ((S ||| 2 ^ (o + 32)) + 1) := by
  rcases hS with h0 | ⟨V, hVO, hc, hbits⟩
  · omega
  rw [labS_land_two_pow] at hq hno
  have hqb : S.testBit (q + 32) = true := by
    by_contra h
    simp [h] at hq
  have hob : S.testBit (o + 32) = false := by
    by_contra h
    simp [h] at hno
  obtain ⟨p, hpV, hpq⟩ := (hbits q).1 (by rw [Nat.testBit_div_two_pow]; exact hqb)
  have hqlt : q < 31671 := hpq ▸ p.2
  have hpe : p = ⟨q, hqlt⟩ := Fin.ext hpq
  have hoO := hmove hqlt (hpe ▸ hVO p hpV)
  have hoV : (⟨o, ho⟩ : Fin 31671) ∉ V := fun h => by
    have := (hbits o).2 ⟨_, h, rfl⟩
    rw [Nat.testBit_div_two_pow, hob] at this
    exact absurd this (by decide)
  have hcard : V.card < 31671 := by
    have : V.card + 1 ≤ 31671 := by
      calc V.card + 1 = (insert (⟨o, ho⟩ : Fin 31671) V).card :=
            (Finset.card_insert_of_notMem hoV).symm
        _ ≤ Finset.univ.card := Finset.card_le_univ _
        _ = 31671 := by simp
    omega
  have hm : (S ||| 2 ^ (o + 32)) % 2 ^ 32 = S % 2 ^ 32 := by
    rw [Nat.or_mod_two_pow, show 2 ^ (o + 32) = 2 ^ 32 * 2 ^ o by rw [pow_add, mul_comm],
      Nat.mul_mod_right, Nat.or_zero]
  have hd : (S ||| 2 ^ (o + 32)) / 2 ^ 32 = S / 2 ^ 32 ||| 2 ^ o := by
    rw [Nat.or_div_two_pow, show 2 ^ (o + 32) = 2 ^ 32 * 2 ^ o by rw [pow_add, mul_comm],
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos 32)]
  generalize S ||| 2 ^ (o + 32) = T at hm hd
  right
  refine ⟨insert ⟨o, ho⟩ V, ?_, ?_, fun q' => ?_⟩
  · intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact hoO
    · exact hVO p hp
  · rw [Finset.card_insert_of_notMem hoV, ← hc, ← hm]
    rw [show (2 : ℕ) ^ 32 = 4294967296 by norm_num] at *
    omega
  · have e : (T + 1) / 2 ^ 32 = T / 2 ^ 32 := by
      rw [show (2 : ℕ) ^ 32 = 4294967296 by norm_num] at *
      omega
    rw [e, hd, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, hbits q']
    simp only [Finset.mem_insert, decide_eq_true_eq]
    constructor
    · rintro (⟨p, hp, rfl⟩ | rfl)
      · exact ⟨p, Or.inr hp, rfl⟩
      · exact ⟨⟨o, ho⟩, Or.inl rfl, rfl⟩
    · rintro ⟨p, rfl | hp, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl ⟨p, hp, rfl⟩

theorem labS_orbRun_succ (LP RD RW : ℕ → ℕ) (j G nG n Rs S : ℕ) :
    orbRun LP RD RW (fun _ => 0) (fun _ => 0) j 0 G nG (n + 1) Rs S =
      sN (Nat.land Rs (nat_lit 32767)) (fun o => sN (fld Rs (nat_lit 15) (nat_lit 32767)) (fun q =>
      sN (fld Rs (nat_lit 30) (nat_lit 255)) (fun k =>
        sN (genW RD RW (fun _ => 0) (fun _ => 0) j 0 G nG k) (fun gw =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (sN (Nat.add (Nat.lor S (Nat.shiftLeft (nat_lit 1) (Nat.add o (nat_lit 32)))) (nat_lit 1))
            (fun S' => orbRun LP RD RW (fun _ => 0) (fun _ => 0) j 0 G nG n
              (Nat.shiftRight Rs (nat_lit 38)) S'))
          (B4A.andB (Nat.blt (nat_lit 0) S) (B4A.andB (Nat.blt (nat_lit 0) gw)
            (B4A.andB (Nat.blt o (nat_lit 31671))
            (B4A.andB
              (Nat.blt (nat_lit 0) (Nat.land S (Nat.shiftLeft (nat_lit 1) (Nat.add q (nat_lit 32)))))
              (B4A.andB (Nat.beq (Nat.land S (Nat.shiftLeft (nat_lit 1) (Nat.add o (nat_lit 32))))
                  (nat_lit 0))
                (Nat.beq (ev1 LP (Nat.sub gw (nat_lit 1)) q) o)))))))))) := rfl

theorem labS_orbRun {ρ : YGroup 4 3 2 →* Equiv.Perm (Fin 31671)} {LP RD RW : ℕ → ℕ}
    (hT : Tables ρ LP) (hrw : ∀ g, isStab (dKind (RD g)) = true → wInH (RW g) = true)
    {j G nG : ℕ} {O : Set (Fin 31671)}
    (hO : ∀ k < nG, ∀ x : Fin 31671, x ∈ O →
      ρ (wVal (yGen 4 3 2) (RW (fld G (20 * k) (ones 20)))) x ∈ O) :
    ∀ n Rs S, LabOrbInv O S →
      LabOrbInv O (orbRun LP RD RW (fun _ => 0) (fun _ => 0) j 0 G nG n Rs S) := by
  intro n
  induction n with
  | zero => intro Rs S h; exact h
  | succ n ih =>
    intro Rs S h
    rw [labS_orbRun_succ]
    simp only [labS_sN, labS_brec]
    split_ifs with hc
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := by simpa only [labS_andB] using hc
      have hS0 : 0 < S := Nat.blt_eq.mp h1
      have hgw := Nat.blt_eq.mp h2
      have ho : (Rs &&& 32767) < 31671 := Nat.blt_eq.mp h3
      have hq : 0 < S &&& 2 ^ (fld Rs 15 32767 + 32) := by
        have := Nat.blt_eq.mp h4
        change 0 < S &&& 1 <<< (fld Rs 15 32767 + 32) at this
        rwa [Nat.one_shiftLeft] at this
      have hno : S &&& 2 ^ ((Rs &&& 32767) + 32) = 0 := by
        have := Nat.eq_of_beq_eq_true h5
        change S &&& 1 <<< ((Rs &&& 32767) + 32) = 0 at this
        rwa [Nat.one_shiftLeft] at this
      have hev := Nat.eq_of_beq_eq_true h6
      have e1 : Nat.add (Nat.lor S (Nat.shiftLeft 1 (Nat.add (Nat.land Rs 32767) 32))) 1 =
          (S ||| 2 ^ ((Rs &&& 32767) + 32)) + 1 := by
        change (S ||| 1 <<< ((Rs &&& 32767) + 32)) + 1 = _
        rw [Nat.one_shiftLeft]
      rw [e1]
      refine ih _ _ (labS_step h hS0 ho hq hno fun hq' hqO => ?_)
      obtain ⟨hk, hs, hwd⟩ := labS_genW hgw
      change ev1 LP (genW RD RW (fun _ => 0) (fun _ => 0) j 0 G nG (fld Rs 30 255) - 1)
        (fld Rs 15 32767) = Rs &&& 32767 at hev
      rw [hwd] at hev
      have hmv := hO _ hk _ hqO
      have e := ev1_spec hT (hrw _ hs) hq'
      rw [hev] at e
      have : (⟨Rs &&& 32767, ho⟩ : Fin 31671) =
          ρ (wVal (yGen 4 3 2) (RW (fld G (20 * fld Rs 30 255) (ones 20)))) ⟨_, hq'⟩ :=
        Fin.ext e.symm
      rw [this]
      exact hmv
    · exact Or.inl rfl

theorem orbChunks_sound {ρ : YGroup 4 3 2 →* Equiv.Perm (Fin 31671)} {LP RD RW : ℕ → ℕ}
    (hT : Tables ρ LP) (hrw : ∀ g, isStab (dKind (RD g)) = true → wInH (RW g) = true)
    {j G nG b o : ℕ} {cs : List (ℕ × ℕ)} (hb : b < 31671)
    (h : orbCount (orbChunks LP RD RW (fun _ => 0) (fun _ => 0) j 0 G nG cs (orbInit b)) = o) :
    o ≤ {y : Fin 31671 | ∃ k ∈ genSub RW G nG, ρ k ⟨b, hb⟩ = y}.ncard := by
  set O := {y : Fin 31671 | ∃ k ∈ genSub RW G nG, ρ k ⟨b, hb⟩ = y} with hOdef
  have hO : ∀ k < nG, ∀ x : Fin 31671, x ∈ O →
      ρ (wVal (yGen 4 3 2) (RW (fld G (20 * k) (ones 20)))) x ∈ O := by
    rintro k hk x ⟨k', hk', rfl⟩
    refine ⟨wVal (yGen 4 3 2) (RW (fld G (20 * k) (ones 20))) * k',
      (genSub RW G nG).mul_mem (Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩) hk', ?_⟩
    rw [map_mul, Equiv.Perm.mul_apply]
  have hrun := labS_orbRun (j := j) hT hrw hO
  have hchunks : ∀ cs S, LabOrbInv O S →
      LabOrbInv O (orbChunks LP RD RW (fun _ => 0) (fun _ => 0) j 0 G nG cs S) := by
    intro cs
    induction cs with
    | nil => intro S hS; exact hS
    | cons p cs ih => intro S hS; exact ih _ (hrun _ _ _ hS)
  have hfinal := hchunks cs _ (labS_init hb ⟨1, (genSub RW G nG).one_mem, by simp⟩)
  have hcnt : ∀ S, orbCount S = S % 2 ^ 32 := fun S => by
    change S &&& 4294967295 = _
    rw [show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  rw [hcnt] at h
  rcases hfinal with h0 | ⟨V, hVO, hc, -⟩
  · rw [h0] at h
    rw [← h]
    exact Nat.zero_le _
  · rw [← h, hc, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun p hp => hVO p hp) (Set.toFinite _)

end CFSG.KC.B433Alt

end
