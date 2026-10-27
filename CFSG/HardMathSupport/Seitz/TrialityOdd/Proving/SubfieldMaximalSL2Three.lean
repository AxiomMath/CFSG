module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.SubfieldMaximalSL2

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.RankThree.PartOne.CTP
open CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair
open CFSG.Glauberman.Dickson

theorem sl2_range_maximal_of_card_three {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F]
    [Finite K]
    (h3 : Module.finrank F K = 3) (hF : Nat.card F = 3)
    (M : Subgroup (SpecialLinearGroup (Fin 2) K))
    (hM : sl2Range F K ≤ M) {j : SpecialLinearGroup (Fin 2) K} (hj : j ∈ M)
    (hjn : j ∉ sl2Range F K) : M = ⊤ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hpP : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨hpP⟩
  have : CharP K p := ringChar.charP K
  obtain ⟨f, -, hFf⟩ := FiniteField.card K p
  have hKf : Nat.card K = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hFf
  have hf0 : 0 < (f : ℕ) := f.pos
  have hFK : Nat.card K = Nat.card F ^ 3 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), h3]
  have hK27 : Nat.card K = 27 := by rw [hFK, hF]; norm_num
  have hp3 : p = 3 := by
    have h27 : p ^ (f : ℕ) = 3 ^ 3 := by rw [← hKf, hK27]; norm_num
    have hdvd : p ∣ 3 ^ 3 := by rw [← h27]; exact dvd_pow_self p hf0.ne'
    exact (Nat.prime_dvd_prime_iff_eq hpP Nat.prime_three).1 (hpP.dvd_of_dvd_pow hdvd)
  have hp2 : p ≠ 2 := by rw [hp3]; norm_num
  have hK : ringChar K ≠ 2 := by rw [← hp]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  let k : Subfield K := (algebraMap F K).fieldRange
  have hkcard : Nat.card k = Nat.card F := by
    have h1 : Nat.card k = Nat.card (Set.range (algebraMap F K)) := by
      have : (k : Set K) = Set.range (algebraMap F K) := RingHom.coe_fieldRange _
      rw [← this]; rfl
    rw [h1, Nat.card_range_of_injective (algebraMap F K).injective]
  let H : Subgroup (PSL2MatrixGroup K) := M.map (mkPSL K)
  let P0 : Subgroup (PSL2MatrixGroup K) := (sl2Range F K).map (mkPSL K)
  have hP0H : P0 ≤ H := Subgroup.map_mono hM
  have hP0card : Nat.card F * (Nat.card F ^ 2 - 1) ≤ 2 * Nat.card P0 := by
    rw [← card_sl2Range (F := F) (K := K)]
    exact card_le_two_mul_card_map _
  have hprod : Nat.card F * (Nat.card F ^ 2 - 1) = 24 := by rw [hF]; norm_num
  have hP012 : 12 ≤ Nat.card P0 := by
    have := hP0card
    omega
  have hcontra : Nat.card H ≤ Nat.card P0 → False := by
    intro hle
    have hHP : P0 = H := Subgroup.eq_of_le_of_card_ge hP0H hle
    have hjH : mkPSL K j ∈ H := Subgroup.mem_map_of_mem _ hj
    rw [← hHP] at hjH
    obtain ⟨s, hs, hsj⟩ := Subgroup.mem_map.1 hjH
    have hc : s⁻¹ * j ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
      have := hsj
      rw [mkPSL, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
      exact this
    exact hjn (by
      have : j = s * (s⁻¹ * j) := by group
      rw [this]
      exact (sl2Range F K).mul_mem hs (center_le_sl2Range hc))
  have hu1 : u2 (1 : K) ∈ sl2Range F K := by
    have := u2_mem_sl2Range (F := F) (K := K) 1
    rwa [map_one] at this
  have hl1 : l2 (1 : K) ∈ sl2Range F K := by
    have := l2_mem_sl2Range (F := F) (K := K) 1
    rwa [map_one] at this
  let x : H := ⟨mkPSL K (u2 1), Subgroup.mem_map_of_mem _ (hM hu1)⟩
  let y : H := ⟨mkPSL K (l2 1), Subgroup.mem_map_of_mem _ (hM hl1)⟩
  have hxy : x * y ≠ y * x := fun h =>
    mkPSL_u2_l2_comm_ne (F := K) (one_ne_zero) (congrArg Subtype.val h)
  have h11 : (1 : K) + 1 ≠ 0 := by rw [one_add_one_eq_two]; exact h2
  have hx2 : x * x ≠ 1 := fun h => by
    have h' : mkPSL K (u2 1) * mkPSL K (u2 1) = 1 := congrArg Subtype.val h
    rw [← map_mul, ← u2_add] at h'
    exact mkPSL_u2_ne_one h11 h'
  have hy2 : y * y ≠ 1 := fun h => by
    have h' : mkPSL K (l2 1) * mkPSL K (l2 1) = 1 := congrArg Subtype.val h
    rw [← map_mul, ← l2_add] at h'
    exact mkPSL_l2_ne_one h11 h'
  have hPSLcard : Nat.card (PSL2MatrixGroup K) = 9828 := by
    have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
      ⟨3, 3, Nat.prime_three, ⟨1, rfl⟩, by norm_num, by rw [hK27]; norm_num⟩
    have h1 : Nat.card (PSL2MatrixGroup K) = Nat.card (CFSG.GorensteinWalter.PSL2 K) := rfl
    rw [h1, CFSG.GorensteinWalter.psl2_card_formula K hodd, hK27]; norm_num
  have hLag : Nat.card H ∣ 9828 := by
    have := Subgroup.card_subgroup_dvd_card H
    rw [hPSLcard] at this
    exact this
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield (p := p)
      (f := (f : ℕ)) hKf H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hcard, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m', t, -, ht, N', C, hN', hNel, hNcard, hCcyc, hCcard, hdisj, hsup⟩ |
      ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩ | ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩
  · exact absurd (hEl.toIsMulCommutative.is_comm.comm x y) hxy
  · have : IsCyclic H := hcyc
    exact absurd (IsCyclic.isMulCommutative.is_comm.comm x y) hxy
  · exact absurd (dihedral_comm e hx2 hy2) hxy
  ·
    exfalso
    have h12 : Nat.card H = 12 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Fintype.card_fin]
      decide
    exact hcontra (by omega)
  ·
    exfalso
    have h24 : Nat.card H = 24 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Fintype.card_fin]
      decide
    rw [h24] at hLag
    omega
  ·
    exfalso
    have h60 : Nat.card H = 60 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Fintype.card_fin]
      decide
    rw [h60] at hLag
    omega
  ·
    exfalso
    have hr1 : ¬ p ∣ p ^ (f : ℕ) - 1 := by
      intro h
      have h1 : p ∣ (p ^ (f : ℕ) - 1) + 1 := by
        rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hpP.pos)]
        exact dvd_pow_self p hf0.ne'
      exact hpP.not_dvd_one ((Nat.dvd_add_right h).1 h1)
    have hcop : ¬ p ∣ Nat.card C := by
      rw [hCcard]
      intro h
      exact hr1 (h.trans (ht.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))))
    have hcast : (p : K) = 0 := CharP.cast_eq_zero K p
    have hxr : x ^ p = 1 := Subtype.ext (by
      show (mkPSL K (u2 1)) ^ p = 1
      rw [← map_pow, u2_pow, hcast, zero_mul, u2_zero, map_one])
    have hyr : y ^ p = 1 := Subtype.ext (by
      show (mkPSL K (l2 1)) ^ p = 1
      rw [← map_pow, l2_pow, hcast, zero_mul, l2_zero, map_one])
    have hxN : x ∈ N' := mem_of_pow_eq_one_of_sup hdisj hsup hpP hcop hxr
    have hyN : y ∈ N' := mem_of_pow_eq_one_of_sup hdisj hsup hpP hcop hyr
    exact hxy (congrArg Subtype.val (hNel.toIsMulCommutative.is_comm.comm (⟨x, hxN⟩ : N') ⟨y, hyN⟩))
  ·
    have hkW : k ≤ W.K := by
      intro y' hy'
      obtain ⟨c, rfl⟩ := RingHom.mem_fieldRange.1 hy'
      exact range_le_witness h2 M hM W c
    rcases subfield_eq_or_eq_top hkW Nat.prime_three (by rw [hkcard]; exact hFK) with hk | htop
    · exfalso
      have hFpm : Nat.card F = p ^ m := by rw [← W.card_eq, hk, hkcard]
      have e2 : GaloisField p m ≃+* F := by
        have := Fintype.ofFinite (GaloisField p m)
        have := Fintype.ofFinite F
        exact FiniteField.ringEquivOfCardEq (by
          rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hFpm, GaloisField.card p m hm0])
      have hcardH : Nat.card H = Nat.card (PSL2MatrixGroup F) := by
        rw [Nat.card_congr eP.toEquiv]
        exact Nat.card_congr (h826_pslEquiv e2).toEquiv
      have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
        ⟨p, m, hpP, hpP.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.2 hm0, hFpm⟩
      have hpsl := CFSG.GorensteinWalter.psl2_card_formula F hodd
      apply hcontra
      rw [hcardH]
      have : Nat.card (PSL2MatrixGroup F) = Nat.card (CFSG.GorensteinWalter.PSL2 F) := rfl
      rw [this, hpsl]
      omega
    · have hmf' : m = (f : ℕ) := by
        have h1 : Nat.card W.K = Nat.card K := by
          rw [htop]; exact Nat.card_congr Subfield.topEquiv.toEquiv
        rw [W.card_eq, hKf] at h1
        exact Nat.pow_right_injective hpP.two_le h1
      have e2 : GaloisField p m ≃+* K := by
        have := Fintype.ofFinite (GaloisField p m)
        exact FiniteField.ringEquivOfCardEq (by
          rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hKf, GaloisField.card p m hm0,
            hmf'])
      have hcardH : Nat.card H = Nat.card (PSL2MatrixGroup K) := by
        rw [Nat.card_congr eP.toEquiv]
        exact Nat.card_congr (h826_pslEquiv e2).toEquiv
      exact eq_top_of_map_mkPSL_eq_top h2 (Subgroup.eq_top_of_card_eq H hcardH)
  ·
    exfalso
    have hkW : k ≤ W.K := by
      intro y' hy'
      obtain ⟨c, rfl⟩ := RingHom.mem_fieldRange.1 hy'
      exact range_le_witness h2 M hM W c
    rcases subfield_eq_or_eq_top hkW Nat.prime_three (by rw [hkcard]; exact hFK) with hk | htop
    · have hFpm : Nat.card F = p ^ m := by rw [← W.card_eq, hk, hkcard]
      have hfm : (f : ℕ) = 3 * m := by
        have : p ^ (f : ℕ) = p ^ (3 * m) := by rw [← hKf, hFK, hFpm, ← pow_mul, mul_comm]
        exact Nat.pow_right_injective hpP.two_le this
      obtain ⟨c, hc⟩ := hmf
      have hm1 : 0 < m := Nat.pos_of_ne_zero hm0
      rcases Nat.lt_or_ge c 2 with h | h
      · interval_cases c <;> omega
      · have := Nat.mul_le_mul_left (2 * m) h
        omega
    · have hmf' : m = (f : ℕ) := by
        have h1 : Nat.card W.K = Nat.card K := by
          rw [htop]; exact Nat.card_congr Subfield.topEquiv.toEquiv
        rw [W.card_eq, hKf] at h1
        exact Nat.pow_right_injective hpP.two_le h1
      have := Nat.le_of_dvd hf0 hmf
      omega

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving
