module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YTheorem5

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

section CharTwo

variable {F : Type*} [Field F] [CharP F 2]

theorem sl2_mul_self_eq_trace_smul (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (g : Matrix (Fin 2) (Fin 2) F) * g =
      ((g : Matrix (Fin 2) (Fin 2) F) 0 0 + (g : Matrix (Fin 2) (Fin 2) F) 1 1) • g + 1 := by
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one] <;>
    simp <;> first | ring1 | linear_combination (-1 : F) * hdet - h2

theorem mul_self_eq_one_of_mul_self_eq {A : Matrix (Fin 2) (Fin 2) F} {t : F}
    (hsq : A * A = t • A + 1) (h4 : A * A * (A * A) = 1) : A * A = 1 := by
  have htt : t + t = 0 := CharTwo.add_self_eq_zero t
  have hexp : A * A * (A * A) = t ^ 2 • (A * A) + 1 := by
    calc A * A * (A * A) = (t • A + 1) * (t • A + 1) := by rw [hsq]
      _ = t ^ 2 • (A * A) + (t + t) • A + 1 := by
          simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one]
          module
      _ = t ^ 2 • (A * A) + 1 := by rw [htt, zero_smul, add_zero]
  have hz : t ^ 2 • (A * A) = 0 := add_eq_right.1 (hexp.symm.trans h4)
  have hAA : A * A ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h4
    exact zero_ne_one h4
  have ht0 : t = 0 := by
    rcases smul_eq_zero.1 hz with h | h
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    · exact absurd h hAA
  rw [hsq, ht0, zero_smul, zero_add]

theorem sl2_sq_eq_one_of_pow_four (g : Matrix.SpecialLinearGroup (Fin 2) F) (hg : g ^ 4 = 1) :
    g ^ 2 = 1 := by
  have hg' : g * g * (g * g) = 1 := by
    rw [← hg]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have h4 : (g : Matrix (Fin 2) (Fin 2) F) * g * (g * g) = 1 := congrArg Subtype.val hg'
  have h2 := mul_self_eq_one_of_mul_self_eq (sl2_mul_self_eq_trace_smul g) h4
  rw [pow_two]
  exact Subtype.ext h2

theorem sl2_sq_eq_one_of_pow_two_pow (g : Matrix.SpecialLinearGroup (Fin 2) F) {k : ℕ}
    (hg : g ^ 2 ^ k = 1) : g ^ 2 = 1 := by
  have key : ∀ k : ℕ, ∀ x : Matrix.SpecialLinearGroup (Fin 2) F, x ^ 2 ^ (k + 1) = 1 →
      x ^ 2 = 1 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      apply ih
      have h4 : (x ^ 2 ^ k) ^ 4 = 1 := by
        rw [← pow_mul, show 2 ^ k * 4 = 2 ^ (k + 1 + 1) by ring, hx]
      have h2 := sl2_sq_eq_one_of_pow_four _ h4
      rwa [← pow_mul, show 2 ^ k * 2 = 2 ^ (k + 1) by ring] at h2
  rcases k with _ | k
  · rw [pow_zero, pow_one] at hg
    rw [hg, one_pow]
  · exact key k g hg

end CharTwo

theorem sq_eq_one_of_pow_two_pow_prod {n : ℕ}
    (x : Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {k : ℕ} (hx : x ^ 2 ^ k = 1) : x ^ 2 = 1 := by
  refine Prod.ext ?_ ?_
  · rw [Prod.pow_fst, Prod.fst_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat]
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
  rw [Prod.pow_snd, Prod.snd_one]
  apply sl2_sq_eq_one_of_pow_two_pow x.2 (k := k)
  rw [← Prod.pow_snd, hx, Prod.snd_one]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem false_of_caseThree (hΩ : Assumption41 Ω) {K T : Subgroup G} (hK : K ∈ Ω) {n : ℕ}
    (φ : oUpperTwoPrime (K ⊔ T) →*
      Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hker : φ.ker = (oddCoreIn K).subgroupOf (oUpperTwoPrime (K ⊔ T))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 K
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
  obtain ⟨ρ, hρU, hρo⟩ := hU.exists_gen
  have hρR : ρ ∈ R := hU.le (hρU ▸ mem_zpowers ρ)
  obtain ⟨k, hk⟩ := hR.isPGroup ⟨ρ, hρR⟩
  have hk' : ρ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hρY : ρ ∈ oUpperTwoPrime (K ⊔ T) := mem_oUpperTwoPrime (mem_sup_left (hR.le hρR)) hk'
  have hy : (⟨ρ, hρY⟩ : oUpperTwoPrime (K ⊔ T)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
  have hφ : φ ⟨ρ, hρY⟩ ^ 2 = 1 :=
    sq_eq_one_of_pow_two_pow_prod _ (k := k) (by rw [← map_pow, hy, map_one])
  have hy2 : (⟨ρ, hρY⟩ : oUpperTwoPrime (K ⊔ T)) ^ 2 ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hφ]
  rw [hker, mem_subgroupOf] at hy2
  have h2 : ρ ^ 2 ∈ oddCoreIn K ⊓ R := ⟨by simpa using hy2, pow_mem hρR 2⟩
  rw [oddCoreIn_inf_eq_bot hR.isPGroup, mem_bot] at h2
  exact hU.gen_mul_self_ne_one hρo (by rw [← pow_two]; exact h2)

theorem not_isCyclic_sylow_of_isPerfect {Q : Type*} [Group Q] [Finite Q] [Nontrivial Q]
    [Group.IsPerfect Q] (P : Sylow 2 Q) : ¬ IsCyclic P := by
  intro hPcyc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card Q := dvd_trans (by norm_num) (four_dvd_card_of_isPerfect (Q := Q))
  have hmin : (Nat.card Q).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
  have hcomp := IsCyclic.isComplement' hmin hPcyc
  have : Group.IsSolvable (P : Subgroup Q) := by
    have := P.isPGroup'.isNilpotent
    infer_instance
  rw [CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one
    (MonoidHom.transferSylow P (hPcyc.normalizer_le_centralizer hmin)), MonoidHom.ker_one]
    at hcomp
  have h := hcomp.card_mul_card
  rw [card_top] at h
  have hP1 : Nat.card (P : Subgroup Q) = 1 :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (h.trans (mul_one _).symm)
  exact Sylow.ne_bot_of_dvd_card P h2 (card_eq_one.mp hP1)

omit [Finite G] in
theorem imgOf_twoPrimeLayerIn (K : Subgroup G) :
    imgOf K (twoPrimeLayerIn K) = CFSG.layer (K ⧸ CFSG.Assembly.oddCore K) := by
  rw [imgOf, twoPrimeLayerIn, subgroupOf, comap_map_eq_self_of_injective K.subtype_injective,
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem not_isCyclic_of_isSylowOf_twoPrimeLayerIn {K P : Subgroup G}
    (hA : twoPrimeLayerIn K ≠ oddCoreIn K) (hP : IsSylowOf 2 P (twoPrimeLayerIn K)) :
    ¬ IsCyclic P := by
  intro hPc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE1 : CFSG.layer (K ⧸ CFSG.Assembly.oddCore K) ≠ ⊥ := fun h =>
    hA ((twoPrimeLayerIn_eq_oddCoreIn_iff K).mpr h)
  have : Nontrivial (CFSG.layer (K ⧸ CFSG.Assembly.oddCore K)) :=
    (nontrivial_iff_ne_bot _).mpr hE1
  have : Group.IsPerfect (CFSG.layer (K ⧸ CFSG.Assembly.oddCore K)) :=
    CFSG.LocalCores.layer_isPerfect
  have hPS := isSylowOf_imgOf hP (twoPrimeLayerIn_le K)
  rw [imgOf_twoPrimeLayerIn] at hPS
  obtain ⟨Q, hQ⟩ := hPS
  obtain ⟨e⟩ := nonempty_mulEquiv_imgOf hP.isPGroup (hP.le.trans (twoPrimeLayerIn_le K))
  have : IsCyclic (imgOf K P) := isCyclic_of_surjective e.toMonoidHom e.surjective
  have e2 : (Q : Subgroup (CFSG.layer (K ⧸ CFSG.Assembly.oddCore K))) ≃* imgOf K P :=
    ((Q : Subgroup (CFSG.layer (K ⧸ CFSG.Assembly.oddCore K))).equivMapOfInjective
      (CFSG.layer (K ⧸ CFSG.Assembly.oddCore K)).subtype (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr hQ)
  exact not_isCyclic_sylow_of_isPerfect Q
    (isCyclic_of_surjective e2.symm.toMonoidHom e2.symm.surjective)

theorem oddCoreIn_eq_bot_of_normalIn (hO : CFSG.Open.standardComponentOddCore G = ⊥)
    {L : Subgroup G} (hL : NormalIn L (twoPrimeLayerIn (⊤ : Subgroup G))) : oddCoreIn L = ⊥ := by
  have hEn : ((twoPrimeLayerIn (⊤ : Subgroup G)).subgroupOf ⊤).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_top).mpr (le_normalizer_twoPrimeLayerIn ⊤)
  exact le_bot_iff.mp ((oddCoreIn_le_of_isSubnormal (CFSG.Assembly.IsSubnormal.step hL.1 hL.2
    (CFSG.Assembly.IsSubnormal.step le_top hEn (CFSG.Assembly.IsSubnormal.refl ⊤)))).trans
    (oddCoreIn_top_eq_bot hO).le)

omit [Finite G] in
theorem normalIn_rightConjugate {L E : Subgroup G} (hE : E.Normal) (hL : NormalIn L E) (g : G) :
    rightConjugate L g ≤ E ∧ E ≤ normalizer (rightConjugate L g : Set G) := by
  have hEN : E ≤ normalizer (L : Set G) := (normal_subgroupOf_iff_le_normalizer hL.1).mp hL.2
  constructor
  · intro x hx
    rw [mem_rightConjugate_iff] at hx
    have := hE.conj_mem _ (hL.1 hx) g⁻¹
    simpa [mul_assoc] using this
  · intro e he
    rw [normalizer_rightConjugate, mem_rightConjugate_iff]
    exact hEN (hE.conj_mem e he g)

theorem commute_of_normalIn (hO : CFSG.Open.standardComponentOddCore G = ⊥) {K : Subgroup G}
    (hK : TightlyEmbedded K) (hL : NormalIn (twoPrimeLayerIn K) (twoPrimeLayerIn ⊤))
    {g : G} (hg : g ∉ normalizer (K : Set G)) {a b : G} (ha : a ∈ twoPrimeLayerIn K)
    (hb : b ∈ rightConjugate (twoPrimeLayerIn K) g) : a * b = b * a := by
  have hE : (twoPrimeLayerIn (⊤ : Subgroup G)).Normal :=
    normalizer_eq_top_iff.mp (eq_top_iff.mpr (le_normalizer_twoPrimeLayerIn ⊤))
  have hEN : twoPrimeLayerIn (⊤ : Subgroup G) ≤ normalizer (twoPrimeLayerIn K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hL.1).mp hL.2
  obtain ⟨hLgE, hEN'⟩ := normalIn_rightConjugate hE hL g
  have hinf : twoPrimeLayerIn K ⊓ rightConjugate (twoPrimeLayerIn K) g = ⊥ := by
    have h1 : twoPrimeLayerIn K ⊓ rightConjugate (twoPrimeLayerIn K) g ≤
        oddCoreIn (twoPrimeLayerIn K) := by
      apply le_oddCoreIn_of_le_normalizer inf_le_left
      · exact fun x hx => inf_le_normalizer_inf ⟨le_normalizer hx, hEN' (hL.1 hx)⟩
      · exact (hK.2 g hg).of_dvd_nat (card_dvd_of_le (inf_le_inf (twoPrimeLayerIn_le K)
          (rightConjugate_le_rightConjugate (twoPrimeLayerIn_le K) g)))
    exact le_bot_iff.mp (h1.trans (oddCoreIn_eq_bot_of_normalIn hO hL).le)
  exact commute_of_inf_eq_bot (hL.1.trans hEN') (hLgE.trans hEN) hinf ha hb

omit [Finite G] in
theorem not_isCyclic_of_rightConjugate_le {P V : Subgroup G} (hP : ¬ IsCyclic P) {g : G}
    (hPV : rightConjugate P g ≤ V) : ¬ IsCyclic V := by
  intro hV
  apply hP
  have e1 : P ≃* rightConjugate P g := P.equivMapOfInjective _ (MulAut.conj g⁻¹).injective
  have e2 := subgroupOfEquivOfLe hPV
  have : IsCyclic (rightConjugate P g) := isCyclic_of_surjective e2.toMonoidHom e2.surjective
  exact isCyclic_of_surjective e1.symm.toMonoidHom e1.symm.surjective

theorem sylowNormalizes_of_normalIn (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hA : twoPrimeLayerIn K ≠ oddCoreIn K)
    (hL : NormalIn (twoPrimeLayerIn K) (twoPrimeLayerIn ⊤)) (g : G) :
    SylowNormalizes (rightConjugate K g) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hg : g ∈ normalizer (K : Set G)
  · rw [(rightConjugate_eq_self_iff K g).mpr hg]
    obtain ⟨R, hR⟩ := exists_isSylowOf 2 K
    exact ⟨R, hR, hR.le.trans le_normalizer⟩
  have hKt := Assumption41.tightlyEmbedded hΩ hK
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (twoPrimeLayerIn K)
  have hPc := not_isCyclic_of_isSylowOf_twoPrimeLayerIn hA hP
  have hP1 : P ≠ ⊥ := by
    rintro rfl
    exact hPc inferInstance
  have h2P : 2 ∣ Nat.card P := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP.isPGroup
    rcases m with _ | m
    · exact absurd (card_eq_one.mp (by simpa using hm)) hP1
    · rw [hm, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨⟨e, heP⟩, he⟩ := exists_prime_orderOf_dvd_card' 2 h2P
  have he' : orderOf e = 2 := (Subgroup.orderOf_coe _).trans he
  have he1 : e ≠ 1 := fun h => by rw [h, orderOf_one] at he'; omega
  have hee : e * e = 1 := by rw [← pow_two, ← he', pow_orderOf_eq_one]
  have heL : e ∈ twoPrimeLayerIn K := hP.le heP
  have hLgN : rightConjugate (twoPrimeLayerIn K) g ≤ normalizer (K : Set G) := fun x hx =>
    Sec4.centralizer_le_normalizer hKt (twoPrimeLayerIn_le K heL) he1 hee
      (mem_centralizer_singleton_iff.mpr (commute_of_normalIn hΩ.oddCore hKt hL hg heL hx).symm)
  have hPg : rightConjugate P g ≤ rightConjugate K g ⊓ normalizer (K : Set G) :=
    le_inf (rightConjugate_le_rightConjugate (hP.le.trans (twoPrimeLayerIn_le K)) g)
      ((rightConjugate_le_rightConjugate hP.le g).trans hLgN)
  obtain ⟨V, hV, hPV⟩ := exists_isSylowOf_le (isPGroup_rightConjugate hP.isPGroup g) hPg
  have hVc := not_isCyclic_of_rightConjugate_le hPc hPV
  have hV1 : V ≠ ⊥ := by
    rintro rfl
    exact hVc inferInstance
  obtain ⟨R, hR, hVR⟩ := exists_isSylowOf_normalized hV.isPGroup (hV.le.trans inf_le_right)
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
  have := hU.isCyclic
  rcases lemma415 h22 hΩ hK (hΩ.conj_mem K hK g) hR hU hV hV1 hVR with
    ⟨hVJ, -, -⟩ | ⟨⟨e⟩, -, -, -⟩ | ⟨hV2, -, -⟩
  · exact ⟨V, hVJ, hV.le.trans inf_le_right⟩
  · exact absurd (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective) hVc
  · exact absurd (isCyclic_of_prime_card (p := 2) hV2) hVc

theorem lemma42_of (h22 : Asc76Lemma22) (h1 : Asc76Theorem1) (h4 : Asc75Theorem4) :
    Lemma42 := by
  intro G _ _ Ω hΩ K hK hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h4 G K (Assumption41.tightlyEmbedded hΩ hK) hA with hL | ⟨-, hstar⟩ |
      ⟨g, -, T, -, -, n, -, φ, -, hker⟩
  · exact normal_of_star h1 hΩ hK fun g _ => sylowNormalizes_of_normalIn h22 hΩ hK hA hL g
  · refine normal_of_star h1 hΩ hK fun g heven => ?_
    by_cases hg : g ∈ normalizer (K : Set G)
    · rw [(rightConjugate_eq_self_iff K g).mpr hg]
      obtain ⟨R, hR⟩ := exists_isSylowOf 2 K
      exact ⟨R, hR, hR.le.trans le_normalizer⟩
    exact hstar (Assumption41.one_lt_pRank hΩ hK) g hg heven
  · exact (false_of_caseThree hΩ hK φ hker).elim

theorem asc76Theorem5_of_thm5Flat (h22 : Asc76Lemma22) (h1 : Asc76Theorem1) (h4 : Asc75Theorem4)
    (hflat : Thm5Flat) : Asc76Theorem5 :=
  asc76Theorem5_of h22 h1 (lemma42_of h22 h1 h4) hflat

end CFSG.ComponentClassification.Asc76.Sec4
