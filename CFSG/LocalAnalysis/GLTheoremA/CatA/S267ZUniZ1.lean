module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniRoots

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S267Z.SL3 (blk mem_blk)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K]

theorem two_ne_zero_of_char (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2) : (2 : K) ≠ 0 := by
  haveI : CharP K ℓ := h.charP
  intro h0
  have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
  rw [CharP.cast_eq_zero_iff K ℓ] at this
  exact hℓ ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this)

theorem le_normalizer_zpowers_of_comm {G : Type*} [Group G] {x : G} {R : Subgroup G}
    (hR : ∀ s ∈ R, s * x = x * s) : R ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hc : ∀ k : ℤ, s * x ^ k * s⁻¹ = x ^ k := fun k => by
    rw [(Commute.zpow_right (hR s hs) k).eq, mul_assoc, mul_inv_cancel, mul_one]
  constructor
  · rintro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [hc]
    exact Subgroup.zpow_mem_zpowers x k
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h1 : s * y * s⁻¹ = s * x ^ k * s⁻¹ := by rw [hc k, hk]
    have : y = x ^ k := by
      calc y = s⁻¹ * (s * y * s⁻¹) * s := by group
        _ = s⁻¹ * (s * x ^ k * s⁻¹) * s := by rw [h1]
        _ = x ^ k := by group
    rw [this]
    exact Subgroup.zpow_mem_zpowers x k

theorem z1AutData_fieldAut (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) {f₀ : ℕ}
    (hK0 : Nat.card (semilinearFixedSubfield σ) = (ℓ ^ f₀) ^ 2)
    (hbar : ∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ f₀)) (hpQ : p ∣ ℓ ^ f₀ + 1)
    (hq : ℓ ^ f = (ℓ ^ f₀) ^ p) (hq0 : 5 ≤ ℓ ^ f₀) :
    Z1AutData p (PU h) (fieldAut h σ) := by
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP K ℓ := h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (PU h) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq5 : 5 ≤ ℓ ^ f := hq0.trans (by rw [hq]; exact Nat.le_self_pow (by omega) _)
  obtain ⟨ζ, hζσ, hζ, hζn⟩ := exists_primitiveRoot_fixed h hp hK0 hbar hpQ
  obtain ⟨lam, hlamn, hlam3p, hlam3, hlamσ⟩ : ∃ lam : K, h.bar lam * lam = 1 ∧
      lam ^ (3 * p) = 1 ∧ lam ^ 3 ≠ 1 ∧ (σ lam * lam⁻¹) ^ 3 = 1 := by
    by_cases hp3' : p = 3
    · subst hp3'
      have hσ3 : σ ^ 3 = 1 := by rw [← hσ, pow_orderOf_eq_one]
      obtain ⟨lam, hn, hprim, hc⟩ := exists_primitiveRoot_nine h hσ3 hq hpQ
      refine ⟨lam, hn, hprim.pow_eq_one, fun h3 => ?_, hc⟩
      have := hprim.dvd_of_pow_eq_one 3 h3
      omega
    · refine ⟨ζ, hζn, by rw [mul_comm, pow_mul, hζ.pow_eq_one, one_pow], fun h3 => ?_, ?_⟩
      · have := hζ.dvd_of_pow_eq_one 3 h3
        exact hp3' ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this)
      · rw [hζσ, mul_inv_cancel₀ (hζ.ne_zero hp.ne_zero), one_pow]
  obtain ⟨a, han, haσ⟩ := exists_norm_one_not_fixed h hp3 hK0 hq (le_trans (by norm_num) hq0)
  have hlam0 : lam ≠ 0 := ne_zero_of_norm hlamn
  have h12 : dOne lam 1 = dOne lam 2 := dOne_one_eq_two lam
  have hd01 : dOne lam 0 ≠ dOne lam 1 := dOne_zero_ne_one hlam0 hlam3
  have htOne : tOne h hlamn = diagU h (dOne lam) (norm_dOne hlamn) (prod_dOne hlam0) := rfl
  have hlayer : GLAPLayer p
      (Subgroup.centralizer ({projU h (tOne h hlamn)} : Set (PU h))) = JU h := by
    rw [htOne]
    exact glaPLayer_centralizer_projU_diagU (d := dOne lam) (hn := norm_dOne hlamn)
      (hd := prod_dOne hlam0) hK hq5 hp hp2 hζ hζn h12 hd01
  have hcomp : GLAPComponent p
      (Subgroup.centralizer ({projU h (tOne h hlamn)} : Set (PU h))) (JU h) := by
    rw [htOne]
    exact glaPComponent_centralizer_projU_diagU (d := dOne lam) (hn := norm_dOne hlamn)
      (hd := prod_dOne hlam0) hK hq5 hp hp2 hζ hζn h12 hd01
  obtain ⟨hRel, hRcard⟩ := isElemAbelian_RU (hlamn := hlamn) (hζn := hζn) hp hp2 hζ hlam3p hlam3
  have hRu : RU h hlamn hζn ≤ Subgroup.centralizer ({projU h (uU h)} : Set (PU h)) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_) <;>
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] <;>
      exact congrArg _ diagU_mul_comm
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_char h hℓ
  refine ⟨RU h hlamn hζn, hRel, hRcard, fun s hs => RU_le_fixSubgroup hlamσ hζσ hs,
    projU h (tOne h hlamn),
    (le_sup_left : Subgroup.zpowers _ ≤ RU h hlamn hζn) (Subgroup.mem_zpowers _),
    projU_tOne_ne_one hlamn hlam3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlayer]
    exact hcomp
  · intro k s hs hj
    rw [hlayer] at hj
    exact centMod_RU hK hq5 hp hp2 hσ hlam3p hlam3 hζ han haσ k s hs hj
  · rw [hlayer]
    exact glaPLayer_JU_inf_fixSubgroup_ne_bot hbar hK0 hq0 hp hp2 hζ hζn hζσ
  · refine ⟨Subgroup.zpowers (projU h (uU h)), ?_, ?_, ?_, ?_⟩
    · intro hb
      apply projU_uU_ne_one h2
      have hmem : projU h (uU h) ∈ Subgroup.zpowers (projU h (uU h)) := Subgroup.mem_zpowers _
      rw [hb, Subgroup.mem_bot] at hmem
      exact hmem
    · intro x
      refine ⟨1, Subtype.ext ?_⟩
      have hdvd : orderOf (x : PU h) ∣ 2 :=
        (orderOf_dvd_of_mem_zpowers x.2).trans (orderOf_dvd_of_pow_eq_one projU_uU_sq)
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact orderOf_dvd_iff_pow_eq_one.1 hdvd
    · rw [MonoidHom.map_zpowers]
      congr 1
      exact fieldAut_uU σ
    · exact le_normalizer_zpowers_of_comm fun s hs =>
        Subgroup.mem_centralizer_singleton_iff.1 (hRu hs)
  · refine ⟨projU h (uU h), projU_uU_ne_one h2, projU_uU_sq, ?_, ?_⟩
    · rw [← map_mul, ← map_mul]
      exact congrArg _ diagU_mul_comm
    · rw [hlayer]
      intro j hj
      exact projU_uU_comm_JU hj

theorem z1Model_PU (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) : Z1Model p (PU h) := by
  haveI : Finite (PU h) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  refine ⟨fun E hE => card_le_pow_three h hℓ hp hp2 hpℓ hE, fun E hE hcard => ?_⟩
  obtain ⟨α, hαE, hαD, σ, hσ, -, hpf, hpQ, hK0, hbar, M, hM⟩ :=
    exists_fieldAut_mem h hℓ hp hp2 hpℓ hE hcard
  have hq : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by rw [← pow_mul, Nat.div_mul_cancel hpf]
  have hq0 : 5 ≤ ℓ ^ (f / p) := by
    have hodd : Odd (ℓ ^ (f / p)) := (h.prime.odd_of_ne_two hℓ).pow
    have h2 : 2 ∣ ℓ ^ (f / p) + 1 := by
      obtain ⟨m, hm⟩ := hodd
      exact ⟨m + 1, by omega⟩
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    have h2p : 2 * p ∣ ℓ ^ (f / p) + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 hpQ
    have hle := Nat.le_of_dvd (by omega) h2p
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    omega
  refine ⟨α, hαE, fun hinn => hαD (inner_le_innDiag h hinn), ?_⟩
  have hM' : (primeFormConjHom h _ M)⁻¹ * α * primeFormConjHom h _ M = fieldAut h σ := hM
  have hα : α = primeFormConjHom h _ M * fieldAut h σ * (primeFormConjHom h _ M)⁻¹ := by
    rw [← hM']
    group
  rw [hα]
  exact CFSG.LocalAnalysis.GLTheoremA.S267Z.z1AutData_conj hp _
    (z1AutData_fieldAut h hℓ hp hp2 hσ hK0 hbar hpQ hq hq0)

theorem z1UniBranch_holds : Z1UniBranch := by
  intro p Q hp hp2 hQ2 hQp M _ _ hM
  obtain ⟨K, _, _, h, -, ⟨e⟩⟩ := exists_mulEquiv_PU hM
  haveI : Finite (PU h) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  exact z1Model_congr hp e.symm (z1Model_PU h hQ2 hp hp2 (Ne.symm hQp))

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end
