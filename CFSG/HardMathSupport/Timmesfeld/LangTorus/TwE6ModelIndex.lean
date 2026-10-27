module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSyl

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Classical2

theorem mem_of_sq_mem_of_pow_mem {G : Type*} [Group G] (N : Subgroup G) (k : ℕ) {m : G}
    (h3 : m ^ 3 ^ k ∈ N) (h2 : m ^ 2 ∈ N) : m ∈ N := by
  obtain ⟨j, hj⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have hm : m = ((m ^ 2) ^ j)⁻¹ * m ^ 3 ^ k := by
    rw [hj, ← pow_mul, pow_succ]
    group
  rw [hm]
  exact mul_mem (inv_mem (pow_mem h2 j)) h3

section Pow



theorem twE6_model_pow_mem_Γ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup TwistTag.E6.tag L p) (hAlg : S.IsAlgebraic) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr) :
    ∃ k : ℕ, ∀ m ∈ S.D.model, m ^ 3 ^ k ∈ S.Γ := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨K, hKcard, -⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.mnSyl_exists_subfield (Ω := L) (ℓ := r) (f := e) he
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hKcard]
    exact pow_ne_zero _ (pow_ne_zero _ hr.ne_zero))
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K r := charP_of_card_eq_prime_pow (f := e * 2)
    (by rw [← Nat.card_eq_fintype_card, hKcard, ← pow_mul])
  have hFr' : ∀ c, Fr c = c ^ (r ^ e) := fun c => by rw [hFr, hq]
  let σ : K →+* K := iterateFrobenius K r e
  have hσ : ∀ c, σ c = c ^ (r ^ e) := fun c => iterateFrobenius_def r e c
  have hq1 : 1 < S.D.q := S.hqpow.1.one_lt
  haveI : IsAlgClosure K L := ⟨inferInstance, ⟨fun x => by
    obtain ⟨n, hn, hx⟩ := hAlg x
    refine ⟨Polynomial.X ^ (S.D.q ^ n) - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero _ (Nat.one_lt_pow hn.ne' hq1), ?_⟩
    simp [hx]⟩⟩
  obtain ⟨-, -, hder, ⟨k, hk⟩, -⟩ :=
    twisted_E6_full_rational_fixed_group_order hr he K hKcard σ hσ L Fr hFr'
  refine ⟨k, fun m hm => ?_⟩
  rw [model_eq_map_twistedFixedGroup S.D hΦ] at hm
  obtain ⟨x, hx, rfl⟩ := hm
  set R := twistedFixedGroup TwistTag.E6 L Fr with hR
  set C := (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K L)) with hC
  have hnormal : (C.subgroupOf R).Normal := by
    have e : C.subgroupOf R = ⁅(⊤ : Subgroup R), ⊤⁆ := by
      have h1 : ⁅R, R⁆ = Subgroup.map R.subtype ⁅(⊤ : Subgroup R), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  have h1 : (⟨x, hx⟩ : R) ^ (C.subgroupOf R).index ∈ C.subgroupOf R :=
    Subgroup.pow_index_mem _ _
  rw [hk] at h1
  have h2 : x ^ 3 ^ k ∈ C := h1
  have hΓ : S.Γ = C.map (MulAut.conj S.D.g0⁻¹).toMonoidHom := by
    show S.D.Γ = _
    rw [LangDatum.Γ, model_eq_map_twistedFixedGroup S.D hΦ, ← Subgroup.map_commutator, hder]
  rw [hΓ]
  exact ⟨x ^ 3 ^ k, h2, by simp [map_pow]⟩

end Pow

end CFSG.HardMathSupport.Timmesfeld.LangTorus
