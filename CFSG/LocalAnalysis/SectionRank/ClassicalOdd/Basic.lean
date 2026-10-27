module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.SectionRank.ClassicalOdd

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

theorem charP_of_card [Finite K] {p f : ℕ} [Fact p.Prime] (h : Nat.card K = p ^ f) :
    CharP K p := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, h])

@[expose] def glOfAdd {V : Type*} [AddGroup V] (M : V → Matrix ι ι K) (h0 : M 0 = 1)
    (hadd : ∀ a b, M (a + b) = M a * M b) : Multiplicative V →* GL ι K where
  toFun a := ⟨M a.toAdd, M (-a.toAdd), by rw [← hadd, add_neg_cancel, h0],
    by rw [← hadd, neg_add_cancel, h0]⟩
  map_one' := Units.ext h0
  map_mul' a b := Units.ext (hadd a.toAdd b.toAdd)

theorem coe_glOfAdd {V : Type*} [AddGroup V] (M : V → Matrix ι ι K) (h0 : M 0 = 1)
    (hadd : ∀ a b, M (a + b) = M a * M b) (a : Multiplicative V) :
    (glOfAdd M h0 hadd a : Matrix ι ι K) = M a.toAdd :=
  rfl

theorem glOfAdd_injective {V : Type*} [AddGroup V] {M : V → Matrix ι ι K} {h0 : M 0 = 1}
    {hadd : ∀ a b, M (a + b) = M a * M b} (hM : Function.Injective M) :
    Function.Injective (glOfAdd M h0 hadd) := fun _ _ h =>
  Multiplicative.toAdd.injective (hM (congrArg Units.val h))

theorem det_eq_one_of_pow_char {p : ℕ} [Fact p.Prime] [CharP K p] {A : Matrix ι ι K}
    (h : A ^ p = 1) : A.det = 1 := by
  have h1 : A.det ^ p = 1 := by rw [← det_pow, h, det_one]
  have h2 : (A.det - 1) ^ p = 0 := by rw [sub_pow_char, h1, one_pow, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).1 h2)

theorem pow_char_eq_one {V : Type*} [AddCommGroup V] [Module K V] {p : ℕ} [CharP K p]
    (a : Multiplicative V) : a ^ p = 1 := by
  change Multiplicative.ofAdd (p • a.toAdd) = Multiplicative.ofAdd 0
  rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

theorem det_eq_one_of_hom {V : Type*} [AddCommGroup V] [Module K V] {p : ℕ} [Fact p.Prime]
    [CharP K p] (φ : Multiplicative V →* GL ι K) (a : Multiplicative V) :
    (φ a : Matrix ι ι K).det = 1 :=
  det_eq_one_of_pow_char (p := p) (by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_char_eq_one (K := K), map_one, Units.val_one])

omit [Field K] in
theorem card_multiplicative_fun {P : Type*} [Fintype P] {p f : ℕ} (hK : Nat.card K = p ^ f) :
    Nat.card (Multiplicative (P → K)) = p ^ (f * Fintype.card P) := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hK, Nat.card_eq_fintype_card, ← pow_mul]

theorem multiplicative_comm {V : Type*} [AddCommGroup V] (a b : Multiplicative V) :
    a * b = b * a :=
  mul_comm a b

theorem le_pRank_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {A : Type*} [Group A] {p k : ℕ} (hp : 1 < p)
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) (hA : Nat.card A = p ^ k)
    (φ : A →* GL ι K) (hφ : Function.Injective φ) (hH : ∀ a, φ a ∈ H) {v : ι → K}
    (hv : v ≠ 0) (hfix : ∀ a, (φ a : Matrix ι ι K) *ᵥ v = v) :
    k ≤ pRank p (⊤ : Subgroup (StatedProj H)) := by
  refine le_pRank_of_injective hp hcomm hpow hA
    ((QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)).comp (φ.codRestrict H hH)) ?_ le_top
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at ha
  obtain ⟨c, hc⟩ := ha
  have hc' : (φ a : Matrix ι ι K) = scalar ι (c : K) := by
    rw [← GeneralLinearGroup.coe_scalar, hc]
    rfl
  have h1 : (c : K) • v = v := by
    have h := hfix a
    rw [hc'] at h
    calc (c : K) • v = scalar ι (c : K) *ᵥ v := by
          ext i
          simp [scalar_apply, mulVec_diagonal]
      _ = v := h
  have hc1 : (c : K) = 1 := by
    by_contra hne
    apply hv
    have h2 : ((c : K) - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)
  have h3 : φ a = 1 := by
    apply Units.ext
    rw [hc', hc1, map_one, Units.val_one]
  exact Subgroup.mem_bot.2 (hφ (h3.trans (map_one φ).symm))

end CFSG.SectionRank.ClassicalOdd
