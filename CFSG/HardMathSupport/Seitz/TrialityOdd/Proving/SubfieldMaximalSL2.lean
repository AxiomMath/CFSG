module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.TwoTorusSL2

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.RankThree.PartOne.CTP
open CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair

section Basic

variable {F K : Type} [Field F] [Field K] [Algebra F K]

@[expose] def sl2Range (F K : Type) [Field F] [Field K] [Algebra F K] :
    Subgroup (SpecialLinearGroup (Fin 2) K) :=
  (SpecialLinearGroup.map (algebraMap F K)).range

theorem u2_mem_sl2Range (c : F) : u2 (algebraMap F K c) ∈ sl2Range F K := by
  refine ⟨u2 c, ?_⟩
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, u2_coe, u2_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem l2_mem_sl2Range (c : F) : l2 (algebraMap F K c) ∈ sl2Range F K := by
  refine ⟨l2 c, ?_⟩
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, l2_coe, l2_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem center_eq_scalar {z : SpecialLinearGroup (Fin 2) K}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K)) :
    ∃ r : K, (r = 1 ∨ r = -1) ∧ (z : Matrix (Fin 2) (Fin 2) K) = r • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hz
  obtain ⟨r, hr, hzr⟩ := hz
  rw [Fintype.card_fin] at hr
  refine ⟨r, ?_, by rw [← hzr, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
  have : (r - 1) * (r + 1) = 0 := by linear_combination hr
  rcases mul_eq_zero.1 this with h | h
  · left; linear_combination h
  · right; linear_combination h

theorem center_le_sl2Range :
    Subgroup.center (SpecialLinearGroup (Fin 2) K) ≤ sl2Range F K := by
  intro z hz
  obtain ⟨r, hr, hzr⟩ := center_eq_scalar hz
  rcases hr with rfl | rfl
  · have : z = 1 := Subtype.ext (by rw [hzr]; simp)
    rw [this]; exact one_mem _
  · obtain ⟨e, he⟩ : ∃ e : SpecialLinearGroup (Fin 2) F,
        (e : Matrix (Fin 2) (Fin 2) F) = (-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) :=
      ⟨⟨(-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F), by
        rw [neg_smul, one_smul, Matrix.det_neg]; simp⟩, rfl⟩
    refine ⟨e, ?_⟩
    ext i j
    have h1 := congrFun (congrFun hzr i) j
    have h2 := congrFun (congrFun he i) j
    rw [SpecialLinearGroup.map_apply_coe]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [h2]
    rw [h1]
    fin_cases i <;> fin_cases j <;> simp

theorem card_le_two_mul_card_map [Finite K] (S : Subgroup (SpecialLinearGroup (Fin 2) K)) :
    Nat.card S ≤ 2 * Nat.card (S.map (mkPSL K)) := by
  classical
  let φ : S →* PSL2MatrixGroup K := (mkPSL K).comp S.subtype
  have hmul := Subgroup.card_ker_mul_card_range φ
  have hrange : φ.range = S.map (mkPSL K) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card φ.ker ≤ 2 := by
    let f : φ.ker → ({1, -1} : Finset K) := fun z => ⟨(z.1.1 : Matrix (Fin 2) (Fin 2) K) 0 0, by
      have hz : (z.1.1 : SpecialLinearGroup (Fin 2) K) ∈
          Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
        have := z.2
        rw [MonoidHom.mem_ker] at this
        simpa [φ, mkPSL, QuotientGroup.eq_one_iff] using this
      obtain ⟨r, hr, hzr⟩ := center_eq_scalar hz
      rw [hzr]
      rcases hr with rfl | rfl <;> simp⟩
    have hf : Function.Injective f := by
      intro z w h
      have hz : (z.1.1 : SpecialLinearGroup (Fin 2) K) ∈
          Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
        have := z.2
        rw [MonoidHom.mem_ker] at this
        simpa [φ, mkPSL, QuotientGroup.eq_one_iff] using this
      have hw : (w.1.1 : SpecialLinearGroup (Fin 2) K) ∈
          Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
        have := w.2
        rw [MonoidHom.mem_ker] at this
        simpa [φ, mkPSL, QuotientGroup.eq_one_iff] using this
      obtain ⟨r, -, hzr⟩ := center_eq_scalar hz
      obtain ⟨r', -, hwr⟩ := center_eq_scalar hw
      have h0 : (z.1.1 : Matrix (Fin 2) (Fin 2) K) 0 0 = (w.1.1 : Matrix (Fin 2) (Fin 2) K) 0 0 :=
        congrArg Subtype.val h
      rw [hzr, hwr] at h0
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h0
      apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
      rw [hzr, hwr, h0]
    calc Nat.card φ.ker ≤ Nat.card ({1, -1} : Finset K) :=
          Nat.card_le_card_of_injective f hf
      _ ≤ 2 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        exact Finset.card_le_two
  rw [hrange] at hmul
  have hpos : 0 < Nat.card (S.map (mkPSL K)) := Nat.card_pos
  calc Nat.card S = Nat.card φ.ker * Nat.card (S.map (mkPSL K)) := hmul.symm
    _ ≤ 2 * Nat.card (S.map (mkPSL K)) := Nat.mul_le_mul_right _ hker

theorem card_sl2Range [Finite F] : Nat.card (sl2Range F K) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have hinj : Function.Injective (SpecialLinearGroup.map (n := Fin 2) (algebraMap F K)) := by
    intro A B h
    apply Subtype.ext
    ext i j
    have := congrArg (fun C : SpecialLinearGroup (Fin 2) K => (C : Matrix (Fin 2) (Fin 2) K) i j) h
    simpa [SpecialLinearGroup.map_apply_coe] using (algebraMap F K).injective this
  rw [sl2Range, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact CFSG.GorensteinWalter.sl2_card_formula F

end Basic

section Witness

open CFSG.Glauberman.Dickson

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K]

theorem range_le_witness (h2 : (2 : K) ≠ 0) {p m : ℕ}
    (M : Subgroup (SpecialLinearGroup (Fin 2) K)) (hM : sl2Range F K ≤ M)
    (W : SubfieldConjugacyWitness p m (M.map (mkPSL K))) (c : F) :
    algebraMap F K c ∈ W.K := by
  have h2K : (2 : K) ∈ W.K := by simp
  have h8K : (8 : K) ∈ W.K := by simp
  have h8 : (8 : K) ≠ 0 := by
    rw [show (8 : K) = 2 * 2 * 2 by norm_num]; exact mul_ne_zero (mul_ne_zero h2 h2) h2
  have hu1 : u2 (1 : K) ∈ M := by
    have := hM (u2_mem_sl2Range (F := F) (K := K) 1)
    rwa [map_one] at this
  have hsq : ∀ d : K, l2 d ∈ M → 2 + d ≠ 0 → (2 + d) ^ 2 ∈ W.K := by
    intro d hd hT0
    set A : SpecialLinearGroup (Fin 2) K := u2 1 * l2 d with hA
    have hAM : A ∈ M := M.mul_mem hu1 hd
    have hT : Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) = 2 + d := by
      rw [hA, trace_u2_mul_l2_odd, one_mul]
    have h := normalizedTrace_mem_subfield (M.map (mkPSL K)) W
      ⟨mkPSL K A, Subgroup.mem_map_of_mem _ hAM⟩ ⟨mkPSL K A, Subgroup.mem_map_of_mem _ hAM⟩
      A A rfl rfl (by rw [hT]; exact hT0) (by rw [hT]; exact hT0)
    rw [← pow_two, trace_pow_two, hT] at h
    have e1 : ((2 + d) ^ 2 - 2) / ((2 + d) * (2 + d)) = 1 - 2 / (2 + d) ^ 2 := by
      field_simp
    rw [e1] at h
    have h3 : 2 / (2 + d) ^ 2 ∈ W.K := by
      have := W.K.sub_mem W.K.one_mem h
      simpa using this
    have h4 : (2 + d) ^ 2 / 2 ∈ W.K := by
      have := W.K.inv_mem h3
      rwa [inv_div] at this
    have h5 := W.K.mul_mem h4 h2K
    rwa [div_mul_cancel₀ _ h2] at h5
  set c' := algebraMap F K c with hc'
  have hl1 : l2 c' ∈ M := hM (l2_mem_sl2Range c)
  have hl2 : l2 (-c') ∈ M := by
    have := hM (l2_mem_sl2Range (F := F) (K := K) (-c))
    rwa [map_neg] at this
  by_cases hp : 2 + c' = 0
  · have : c' = -2 := by linear_combination hp
    rw [this]; exact W.K.neg_mem h2K
  by_cases hm : 2 + -c' = 0
  · have : c' = 2 := by linear_combination -hm
    rw [this]; exact h2K
  have h3 := W.K.sub_mem (hsq c' hl1 hp) (hsq (-c') hl2 hm)
  have e : (2 + c') ^ 2 - (2 + -c') ^ 2 = 8 * c' := by ring
  rw [e] at h3
  have := W.K.mul_mem h3 (W.K.inv_mem h8K)
  rwa [mul_comm, ← mul_assoc, inv_mul_cancel₀ h8, one_mul] at this

end Witness


section Main

open CFSG.Glauberman.Dickson

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] [Finite K]

theorem sl2_range_maximal (h3 : Module.finrank F K = 3) (hK : ringChar K ≠ 2)
    (hF : 5 ≤ Nat.card F) (M : Subgroup (SpecialLinearGroup (Fin 2) K))
    (hM : sl2Range F K ≤ M) {j : SpecialLinearGroup (Fin 2) K} (hj : j ∈ M)
    (hjn : j ∉ sl2Range F K) : M = ⊤ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hpP : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨hpP⟩
  have : CharP K p := ringChar.charP K
  have hp2 : p ≠ 2 := hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨f, -, hFf⟩ := FiniteField.card K p
  have hKf : Nat.card K = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hFf
  have hf0 : 0 < (f : ℕ) := f.pos
  have hFK : Nat.card K = Nat.card F ^ 3 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), h3]
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
  have hq5 : 120 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := by
    calc 120 = 5 * (5 ^ 2 - 1) := by norm_num
      _ ≤ Nat.card F * (Nat.card F ^ 2 - 1) :=
        Nat.mul_le_mul hF (Nat.sub_le_sub_right (Nat.pow_le_pow_left hF 2) 1)
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
  have hx60 : ∀ n : ℕ, Nat.card H = n → n ≤ 60 → False := fun n hn hn60 =>
    hcontra (by omega)
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
    apply hx60 12 _ (by norm_num)
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Fintype.card_fin]
    decide
  ·
    exfalso
    apply hx60 24 _ (by norm_num)
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Fintype.card_fin]
    decide
  ·
    exfalso
    apply hx60 60 _ (by norm_num)
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Fintype.card_fin]
    decide
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
    have := hN'
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

theorem sl2_range_sup_eq_top (h3 : Module.finrank F K = 3) (hK : ringChar K ≠ 2)
    (hF : 5 ≤ Nat.card F) (S₂ : Subgroup (SpecialLinearGroup (Fin 2) K))
    (hcard : Nat.card S₂ = Nat.card (sl2Range F K)) (hne : S₂ ≠ sl2Range F K) :
    sl2Range F K ⊔ S₂ = ⊤ := by
  have hnle : ¬ S₂ ≤ sl2Range F K := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle hcard.ge)
  obtain ⟨j, hj2, hjn⟩ := Set.not_subset.1 hnle
  exact sl2_range_maximal h3 hK hF _ le_sup_left (j := j) (le_sup_right (a := sl2Range F K) hj2) hjn

end Main

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving
