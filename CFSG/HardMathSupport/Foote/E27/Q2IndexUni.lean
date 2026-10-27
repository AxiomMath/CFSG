module

public import CFSG.HardMathSupport.Foote.E27.UniFour
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.IndexUnitary
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.HardMathSupport.Foote.E27.NormalAbelianEquiv
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Open TauCeti CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher Subgroup

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

private theorem factorization_three_of_eq {m v r : ℕ} (hm : m = 3 ^ v * r) (hr : ¬ 3 ∣ r) :
    m.factorization 3 = v := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr (dvd_zero 3)
  rw [hm, Nat.factorization_mul (by positivity) hr0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hr, add_zero]

theorem card_pgroup_eq {J : Type*} [Group J] [Finite J] {S : Subgroup J} (hS : IsPGroup 3 S)
    {v : ℕ} (hv : (Nat.card J).factorization 3 = v) (hlow : 3 ^ v ≤ Nat.card S) :
    Nat.card S = 3 ^ v := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  rw [hk] at hlow ⊢
  have h1 : v ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hlow
  have h2 : 3 ^ k ∣ Nat.card J := hk ▸ Subgroup.card_subgroup_dvd_card S
  have hJ : Nat.card J ≠ 0 := Nat.card_pos.ne'
  have h3 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hJ).mp h2
  rw [hv] at h3
  rw [show k = v by omega]

theorem E27Config.false_of_primeFormP_big {E : Type} [Field E] {p f : ℕ} (hp : p = 2) (hf : f = 1)
    (hU : UnitaryFieldData p f E) {n : ℕ} (h : E27Config X K R T z) (hz : z ∈ K)
    (θ : ↥K ≃* primeFormP hU (1 : Matrix (Fin n) (Fin n) E)) (hn : n = 8 ∨ n = 9)
    (hN : Nat.card ↥K = ordTwistedA (n - 1) 2) : False := by
  subst hp hf
  have hfin : Finite (primeFormP hU (1 : Matrix (Fin n) (Fin n) E)) :=
    Finite.of_equiv ↥K θ.toEquiv
  have hJ : Nat.card (primeFormP hU (1 : Matrix (Fin n) (Fin n) E)) = ordTwistedA (n - 1) 2 := by
    rw [← hN]; exact (Nat.card_congr θ.toEquiv).symm
  obtain ⟨P⟩ : Nonempty (Sylow 3 (Equiv.Perm (Fin n))) := inferInstance
  have hP : Nat.card P = 3 ^ (Nat.card (Equiv.Perm (Fin n))).factorization 3 :=
    Sylow.card_eq_multiplicity P
  have hperm : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rcases hn with rfl | rfl
  · have hv : (Nat.card (primeFormP hU (1 : Matrix (Fin 8) (Fin 8) E))).factorization 3 = 9 := by
      rw [hJ]
      refine factorization_three_of_eq (v := 9) (r := 377735662796800) ?_ (by decide)
      unfold ordTwistedA; decide +kernel
    have hPc : Nat.card P = 3 ^ 2 := by
      rw [hP, hperm]
      have : (Nat.factorial 8).factorization 3 = 2 :=
        factorization_three_of_eq (v := 2) (r := 4480) (by decide) (by decide)
      rw [this]
    have hZ : Nat.card (Uni.Zsc hU 8) ≤ 1 := by
      rw [Uni.Zsc_eq_bot_of_coprime hU (by norm_num), Subgroup.card_bot]
    obtain ⟨hSp, hS, hAS, hnorm, hcomm, hexp, hA⟩ := Uni.monomial_data hU (by norm_num) P 1 hZ
    rw [hPc] at hS
    have hSc := card_pgroup_eq hSp hv (by omega)
    refine h.false_of_normal_abelian_of_equiv hz θ (Uni.Smono hU 8 P) (Uni.Amono hU 8) ?_ hAS hnorm hcomm hexp (by omega)
    rw [hSc, hv]
  · have hv : (Nat.card (primeFormP hU (1 : Matrix (Fin 9) (Fin 9) E))).factorization 3 = 11 := by
      rw [hJ]
      refine factorization_three_of_eq (v := 11) (r := 1837306263843635200) ?_ (by decide)
      unfold ordTwistedA; decide +kernel
    have hPc : Nat.card P = 3 ^ 4 := by
      rw [hP, hperm]
      have : (Nat.factorial 9).factorization 3 = 4 :=
        factorization_three_of_eq (v := 4) (r := 4480) (by decide) (by decide)
      rw [this]
    have hZ : Nat.card (Uni.Zsc hU 9) ≤ 3 := Uni.card_Zsc_le_three hU
    obtain ⟨hSp, hS, hAS, hnorm, hcomm, hexp, hA⟩ := Uni.monomial_data hU (by norm_num) P 3 hZ
    rw [hPc] at hS
    have hSc := card_pgroup_eq hSp hv (by omega)
    refine h.false_of_normal_abelian_of_equiv hz θ (Uni.Smono hU 9 P) (Uni.Amono hU 9) ?_ hAS hnorm hcomm hexp (by omega)
    rw [hSc, hv]

theorem E27Config.false_of_primeFormP_mid {E : Type} [Field E] {p f : ℕ} (hp : p = 2) (hf : f = 1)
    (hU : UnitaryFieldData p f E) {n : ℕ} (h : E27Config X K R T z) (hz : z ∈ K)
    (θ : ↥K ≃* primeFormP hU (1 : Matrix (Fin n) (Fin n) E)) (hn : n = 5 ∨ n = 6 ∨ n = 7)
    (hN : Nat.card ↥K = ordTwistedA (n - 1) 2) : False := by
  subst hp hf
  have hEfin : Finite E := hU.finite
  have hfin : Finite (primeFormP hU (1 : Matrix (Fin n) (Fin n) E)) :=
    Finite.of_equiv ↥K θ.toEquiv
  have hJ : Nat.card (primeFormP hU (1 : Matrix (Fin n) (Fin n) E)) = ordTwistedA (n - 1) 2 := by
    rw [← hN]; exact (Nat.card_congr θ.toEquiv).symm
  obtain ⟨P⟩ : Nonempty (Sylow 3 (Equiv.Perm (Fin n))) := inferInstance
  have hP : Nat.card P = 3 ^ (Nat.card (Equiv.Perm (Fin n))).factorization 3 :=
    Sylow.card_eq_multiplicity P
  have hperm : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hn1 : 1 ≤ n := by omega
  have hc0 : ∀ c : Fin n → Eˣ, ∏ i, c i = 1 → ∀ σ : Equiv.Perm (Fin n), σ ^ 3 = 1 →
      ∀ c0 : Eˣ, c0 ^ n = 1 → (∀ i, c i * c (σ.symm i) * c (σ.symm (σ.symm i)) = c0) →
      c0 = 1 := by
    rcases hn with rfl | rfl | rfl
    · intro c _ σ _ c0 hcn _
      exact Uni.c0_eq_one_of_coprime hU (by norm_num) hcn
    · intro c hc σ hσ c0 hcn hν
      exact Uni.c0_eq_one_six hU c hc σ hσ hν
    · intro c _ σ _ c0 hcn _
      exact Uni.c0_eq_one_of_coprime hU (by norm_num) hcn
  have key : ∀ zb v : ℕ, Nat.card (Uni.Zsc hU n) ≤ zb →
      (Nat.card (primeFormP hU (1 : Matrix (Fin n) (Fin n) E))).factorization 3 = v →
      3 ^ v * zb ≤ 3 ^ (n - 1) * Nat.card P → 81 * zb ≤ 3 ^ (n - 1) → False := by
    intro zb v hZ hv hlow hA
    have hzb : 0 < zb := lt_of_lt_of_le Nat.card_pos hZ
    obtain ⟨hSp, hS, hAS, -, -, -, hAc⟩ := Uni.monomial_data hU hn1 P zb hZ
    have hSge : 3 ^ v ≤ Nat.card (Uni.Smono hU n P) :=
      Nat.le_of_mul_le_mul_right (hlow.trans hS) hzb
    have hSc := card_pgroup_eq hSp hv hSge
    have hAge : 81 ≤ Nat.card (Uni.Amono hU n) :=
      Nat.le_of_mul_le_mul_right (hA.trans hAc) hzb
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨a, ha⟩ := (hSp.to_le hAS).exists_card_eq
    have h81 : 81 ∣ Nat.card (Uni.Amono hU n) := by
      rw [ha] at hAge ⊢
      have : 4 ≤ a := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp
        (by simpa using hAge : 3 ^ 4 ≤ 3 ^ a)
      exact (pow_dvd_pow 3 this : 3 ^ 4 ∣ 3 ^ a)
    have hgood : ∀ s ∈ Uni.Smono hU n P, orderOf s = 3 → FusGood (Uni.Smono hU n P) s :=
      fun s hs h3 => Uni.fusGood_Smono hU (P : Subgroup (Equiv.Perm (Fin n)))
        (fun c σ _ hz => Uni.cube_eq_one_of hU hc0 c σ hz) h81 hs h3
    obtain ⟨S₀, hS₀⟩ := exists_sylow_fusion_of_equiv θ (Uni.Smono hU n P)
      (by rw [hSc, hv]) hgood
    exact h.false_of_fusion_kill hz S₀ hS₀
  rcases hn with rfl | rfl | rfl
  · have hv : (Nat.card (primeFormP hU (1 : Matrix (Fin 5) (Fin 5) E))).factorization 3 = 5 := by
      rw [hJ]
      refine factorization_three_of_eq (v := 5) (r := 56320) ?_ (by decide)
      unfold ordTwistedA; decide +kernel
    have hPc : Nat.card P = 3 ^ 1 := by
      rw [hP, hperm]
      have : (Nat.factorial 5).factorization 3 = 1 :=
        factorization_three_of_eq (v := 1) (r := 40) (by decide) (by decide)
      rw [this]
    have hZ : Nat.card (Uni.Zsc hU 5) ≤ 1 := by
      rw [Uni.Zsc_eq_bot_of_coprime hU (by norm_num), Subgroup.card_bot]
    exact key 1 5 hZ hv (by rw [hPc]; norm_num) (by norm_num)
  · have hv : (Nat.card (primeFormP hU (1 : Matrix (Fin 6) (Fin 6) E))).factorization 3 = 6 := by
      rw [hJ]
      refine factorization_three_of_eq (v := 6) (r := 12615680) ?_ (by decide)
      unfold ordTwistedA; decide +kernel
    have hPc : Nat.card P = 3 ^ 2 := by
      rw [hP, hperm]
      have : (Nat.factorial 6).factorization 3 = 2 :=
        factorization_three_of_eq (v := 2) (r := 80) (by decide) (by decide)
      rw [this]
    exact key 3 6 (Uni.card_Zsc_le_three hU) hv (by rw [hPc]; norm_num) (by norm_num)
  · have hv : (Nat.card (primeFormP hU (1 : Matrix (Fin 7) (Fin 7) E))).factorization 3 = 8 := by
      rw [hJ]
      refine factorization_three_of_eq (v := 8) (r := 34718351360) ?_ (by decide)
      unfold ordTwistedA; decide +kernel
    have hPc : Nat.card P = 3 ^ 2 := by
      rw [hP, hperm]
      have : (Nat.factorial 7).factorization 3 = 2 :=
        factorization_three_of_eq (v := 2) (r := 560) (by decide) (by decide)
      rw [this]
    have hZ : Nat.card (Uni.Zsc hU 7) ≤ 1 := by
      rw [Uni.Zsc_eq_bot_of_coprime hU (by norm_num), Subgroup.card_bot]
    exact key 1 8 hZ hv (by rw [hPc]; norm_num) (by norm_num)

theorem E27Config.false_of_primeFormP_four {E : Type} [Field E] {p f : ℕ} (hp : p = 2) (hf : f = 1)
    (hU : UnitaryFieldData p f E) (h : E27Config X K R T z) (hz : z ∈ K)
    (θ : ↥K ≃* primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E))
    (hN : Nat.card ↥K = ordTwistedA (4 - 1) 2) : False := by
  subst hp hf
  have hEfin : Finite E := hU.finite
  have hfin : Finite (primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E)) :=
    Finite.of_equiv ↥K θ.toEquiv
  have hJ : Nat.card (primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E)) = ordTwistedA (4 - 1) 2 := by
    rw [← hN]; exact (Nat.card_congr θ.toEquiv).symm
  obtain ⟨P⟩ : Nonempty (Sylow 3 (Equiv.Perm (Fin 4))) := inferInstance
  have hPcard : Nat.card P = 3 ^ (Nat.card (Equiv.Perm (Fin 4))).factorization 3 :=
    Sylow.card_eq_multiplicity P
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = (4 : ℕ).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hPc : Nat.card (P : Subgroup (Equiv.Perm (Fin 4))) = 3 := by
    have h24 : ((4 : ℕ).factorial).factorization 3 = 1 :=
      factorization_three_of_eq (v := 1) (r := 8) (by decide) (by decide)
    have : Nat.card P = 3 := by rw [hPcard, hperm, h24]; norm_num
    exact this
  have hv : (Nat.card (primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E))).factorization 3 = 4 := by
    rw [hJ]
    refine factorization_three_of_eq (v := 4) (r := 320) ?_ (by decide)
    unfold ordTwistedA; decide +kernel
  have hZ : Nat.card (Uni.Zsc hU 4) ≤ 1 := by
    rw [Uni.Zsc_eq_bot_of_coprime hU (by norm_num), Subgroup.card_bot]
  have hPp : IsPGroup 3 (P : Subgroup (Equiv.Perm (Fin 4))) := P.isPGroup'
  obtain ⟨hSp, hS, -, -, -, -, -⟩ :=
    Uni.monomial_data_of_pgroup hU (by norm_num) (P : Subgroup (Equiv.Perm (Fin 4))) hPp 1 hZ
  have hSge : 3 ^ 4 ≤ Nat.card (Uni.Smono hU 4 (P : Subgroup (Equiv.Perm (Fin 4)))) := by
    rw [hPc] at hS
    omega
  have hSc := card_pgroup_eq hSp hv hSge
  have hS81 : Nat.card (Uni.Smono hU 4 (P : Subgroup (Equiv.Perm (Fin 4)))) = 81 := by
    rw [hSc]; norm_num
  have hgen := Uni.hgen_four hU (P : Subgroup (Equiv.Perm (Fin 4))) hPp hPc hS81
  obtain ⟨S₀, hS₀⟩ := exists_sylow_gen_of_equiv θ
    (Uni.Smono hU 4 (P : Subgroup (Equiv.Perm (Fin 4)))) (by rw [hSc, hv]) hgen
  exact h.false_of_fusion_gen hz S₀ hS₀

theorem E27Config.false_of_typeTwistedA_two (h : E27Config X K R T z) (hz : z ∈ K) {r : ℕ}
    {q : PrimePower} (hv : (LieTypeIndex.twistedA r q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩)) (hp : q.p = 2)
    (hf : q.exponent = 1) (hr : 3 ≤ r ∧ r ≤ 8) : False := by
  obtain ⟨e⟩ := e
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have hm' := hm
  rw [hp, hf] at hm'
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hm').2.1 rfl
  obtain ⟨E, _, hU, ⟨θ⟩⟩ :=
    CFSG.HardMathSupport.Malle.E27Lie.exists_primeFormP_of_twistedA' r q hv e (by omega)
  have hN : Nat.card ↥K = ordTwistedA (r + 1 - 1) 2 := by rw [hcard]; norm_num
  by_cases hr3 : r = 3
  · subst hr3
    exact h.false_of_primeFormP_four hp hf hU hz θ hN
  by_cases hbig : 7 ≤ r
  · exact h.false_of_primeFormP_big hp hf hU hz θ (n := r + 1) (by omega) hN
  · exact h.false_of_primeFormP_mid hp hf hU hz θ (n := r + 1) (by omega) hN

end CFSG.HardMathSupport.Foote.E27

end
