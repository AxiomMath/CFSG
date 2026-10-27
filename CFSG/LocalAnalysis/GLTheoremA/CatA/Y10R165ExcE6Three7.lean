module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six3
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three3
public import CFSG.Monster.B.E6.StdF4RadicalRoots
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Basic

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.Isogeny
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective
  adjEmb_mem adjEmb_frobenius sigma_embedding_data subtorusImage mem_subtorusImage_iff
  twistedTorusOf twistedFixedPoints mem_twistedFixedPoints subtorusSigma)
open CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.Classical2 (torusRootKernel torusRootKernel_rootDiagUnit
  rootSpan_torusRootKernel_le_centralizer)
open CFSG.HardMathSupport.Lang.TwE6Step3
open CFSG.RankThree.Lattice (e6T3W)
open scoped Matrix MatrixGroups Pointwise

private theorem three_lt_of_rk2Ord_eq_three {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : rk2Ord p n = 3) : 3 < p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
  have hpowne : ((2 : ZMod p) ^ n) ≠ 0 := pow_ne_zero n h2ne
  have hdvd : orderOf ((2 : ZMod p) ^ n) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hpowne
  change rk2Ord p n ∣ p - 1 at hdvd
  rw [hrk] at hdvd
  have hpodd : p ≠ 2 := hp2
  have hpge3 : 3 ≤ p := by have := hp.two_le; omega
  rcases Nat.lt_or_ge p 7 with h | h
  · interval_cases p <;> simp_all [Nat.Prime]
  · omega

private theorem dvd_two_pow_add {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : rk2Ord p n = 3) : p ∣ 2 ^ (2 * n) + 2 ^ n + 1 := by
  have h3' : rk2Ord p n ∣ 3 := by rw [hrk]
  have h3 : p ∣ 2 ^ (n * 3) - 1 := (rk2Ord_dvd_iff 3).1 h3'
  have h1 : ¬ p ∣ 2 ^ n - 1 := by
    intro h
    have := rk2Ord_eq_one_iff.2 h
    omega
  have hfac : 2 ^ (n * 3) - 1 = (2 ^ n - 1) * (2 ^ (2 * n) + 2 ^ n + 1) := by
    have hx1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hpow3 : 2 ^ (n * 3) = (2 ^ n) ^ 3 := by rw [pow_mul]
    have hpow2 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [mul_comm 2 n, pow_mul]
    rw [hpow3, hpow2]
    obtain ⟨x, hx⟩ : ∃ x, 2 ^ n = x + 1 := ⟨2 ^ n - 1, by omega⟩
    rw [hx]
    have hx' : x + 1 - 1 = x := by omega
    rw [hx']
    have : (x + 1) ^ 3 = x * ((x + 1) ^ 2 + (x + 1) + 1) + 1 := by ring
    omega
  rw [hfac] at h3
  rcases (Nat.Prime.dvd_mul hp).1 h3 with h | h
  · exact absurd h h1
  · exact h

theorem three_dvd_card_sq_add {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : rk2Ord p n = 3) : p ∣ Nat.card F ^ 2 + Nat.card F + 1 := by
  have h := dvd_two_pow_add hp hp2 hrk
  have h2 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [mul_comm 2 n, pow_mul]
  rw [h2] at h
  rw [hcard]
  exact h

theorem three_lt_of_card {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : rk2Ord p n = 3) : 3 < p :=
  three_lt_of_rk2Ord_eq_three hp hp2 hrk

private theorem seven_le_of_rk2Ord_eq_three {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : rk2Ord p n = 3) : 7 ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
  have hpowne : ((2 : ZMod p) ^ n) ≠ 0 := pow_ne_zero n h2ne
  have hdvd : orderOf ((2 : ZMod p) ^ n) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hpowne
  change rk2Ord p n ∣ p - 1 at hdvd
  rw [hrk] at hdvd
  have hpge3 : 3 ≤ p := by have := hp.two_le; omega
  rcases Nat.lt_or_ge p 7 with h | h
  · interval_cases p
    · norm_num at hdvd
    · exact absurd hp (by decide)
    · norm_num at hdvd
    · exact absurd hp (by decide)
  · exact h

theorem seven_le_of_card {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : rk2Ord p n = 3) : 7 ≤ p :=
  seven_le_of_rk2Ord_eq_three hp hp2 hrk

theorem three_dvd_card_sq_add_int {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : rk2Ord p n = 3) :
    (p : ℤ) ∣ (Nat.card F : ℤ) ^ 2 + (Nat.card F : ℤ) + 1 := by
  exact_mod_cast three_dvd_card_sq_add hcard hp hp2 hrk

def frameImage {F : Type} [Field F] {L : Type} [Field L] [Algebra F L]
    (c : adjointGroup Tag.E6 F) (g0 : ModGL Tag.E6 L)
    (Q : Subgroup (adjointGroup Tag.E6 F)) : Subgroup (ModGL Tag.E6 L) :=
  ((Q.map (MulAut.conj c).toMonoidHom).map (adjEmb Tag.E6 F L)).map
    (MulAut.conj g0⁻¹).toMonoidHom

theorem mem_frameImage {F : Type} [Field F] {L : Type} [Field L] [Algebra F L]
    {c : adjointGroup Tag.E6 F} {g0 : ModGL Tag.E6 L}
    {Q : Subgroup (adjointGroup Tag.E6 F)} {y : ModGL Tag.E6 L} :
    y ∈ frameImage c g0 Q ↔
      ∃ q ∈ Q, y = g0⁻¹ * adjEmb Tag.E6 F L (c * q * c⁻¹) * g0 := by
  constructor
  · intro hy
    rw [frameImage, Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Subgroup.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [Subgroup.mem_map] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    rw [frameImage, Subgroup.mem_map]
    exact ⟨_, ⟨_, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩

theorem exists_frame_image {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : rk2Ord p n = 3)
    [Finite ↥(e6Data_valid.minGroup F)]
    {Ã : Subgroup ↥(e6Data_valid.minGroup F)} (hAe : IsElemAbelian p Ã)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup ↥(e6Data_valid.minGroup F)) ≤
      CFSG.Open.pRank p Ã) :
    ∃ (g0 : ModGL Tag.E6 (AlgebraicClosure F)) (c : adjointGroup Tag.E6 F)
      (A : Subgroup (ModGL Tag.E6 (AlgebraicClosure F))),
      A = frameImage c g0 (Ã.map (e6Isogeny F)) ∧
      A ≤ twistedTorus (phi3N (AlgebraicClosure F))
        (iterateFrobenius (AlgebraicClosure F) 2 n) ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ 3 ∧
      g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure F) ∧
      Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n)) g0 =
        g0 * phi3N (AlgebraicClosure F) ∧
      (∀ P : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)),
        Finite P → P ≤ adjointGroup Tag.E6 (AlgebraicClosure F) →
        (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n)) x = x) →
        ⁅P, P⁆ = P → P ≤ (adjEmb Tag.E6 F (AlgebraicClosure F)).range) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  have hf : 1 ≤ n := by omega
  have hp3 : 3 < p := three_lt_of_card hcard hp hp2 hrk
  have hpqi : (p : ℤ) ∣ (Nat.card F : ℤ) ^ 2 + (Nat.card F : ℤ) + 1 :=
    three_dvd_card_sq_add_int hcard hp hp2 hrk
  have hker : (e6Isogeny F).ker = Subgroup.center ↥(e6Data_valid.minGroup F) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := F)
  have hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥(e6Data_valid.minGroup F)) :=
    not_dvd_card_center_e6_three hcard hp hrk
  have hpk : ¬ p ∣ Nat.card (e6Isogeny F).ker := by rwa [hker]
  have hA3 : 3 ≤ CFSG.Open.pRank p Ã := by
    rw [← pRank_minGroup_e6_three hcard hp hp2 hrk]
    exact hmax
  have hAcard : Nat.card Ã = p ^ 3 :=
    card_maximal_elemAbelian_e6_three hcard hp hp2 hrk hAe hmax hA3
  have hdisj : Disjoint Ã (e6Isogeny F).ker := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hAcard, hker]
    exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpZ)
  have hinjOn : Set.InjOn (e6Isogeny F) (Ã : Set ↥(e6Data_valid.minGroup F)) := by
    intro a ha b hb hab
    have hd : (a⁻¹ * b : ↥(e6Data_valid.minGroup F)) ∈ (e6Isogeny F).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    have hmem : (a⁻¹ * b : ↥(e6Data_valid.minGroup F)) ∈ Ã ⊓ (e6Isogeny F).ker :=
      ⟨Ã.mul_mem (Ã.inv_mem ha) hb, hd⟩
    have hbot : (a⁻¹ * b : ↥(e6Data_valid.minGroup F)) = 1 := by
      have h1 : (a⁻¹ * b : ↥(e6Data_valid.minGroup F)) ∈
          (⊥ : Subgroup ↥(e6Data_valid.minGroup F)) := by
        rwa [← hdisj.eq_bot]
      exact Subgroup.mem_bot.mp h1
    have hba : b = a := by
      have h := congrArg (fun x : ↥(e6Data_valid.minGroup F) => a * x) hbot
      simpa [mul_assoc] using h
    exact hba.symm
  set Q : Subgroup (adjointGroup Tag.E6 F) := Ã.map (e6Isogeny F) with hQdef
  have hQel : IsElemAbelian p Q := CFSG.SectionRank.isElemAbelian_map hAe (e6Isogeny F)
  have hQcard : Nat.card Q = p ^ 3 := by
    rw [hQdef, CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral.card_map_eq_of_injOn
      hinjOn, hAcard]
  have hQp : IsPGroup p Q := IsElemAbelian.isPGroup hQel
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ :=
    e6_three_frame F hf hcard hp hp3 hpqi (AlgebraicClosure F)
  obtain ⟨c, hc⟩ := hconj Q hQp
  refine ⟨g0, c, frameImage c g0 Q, rfl, ?_, ?_, ?_, hg0C, hg0, hperf⟩
  · intro y hy
    rw [mem_frameImage] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    exact hc q hq
  · rw [frameImage]
    exact CFSG.SectionRank.isElemAbelian_map
      (CFSG.SectionRank.isElemAbelian_map
        (CFSG.SectionRank.isElemAbelian_map hQel (MulAut.conj c).toMonoidHom)
        (adjEmb Tag.E6 F (AlgebraicClosure F)))
      (MulAut.conj g0⁻¹).toMonoidHom
  · rw [frameImage, Subgroup.card_map_of_injective (MulAut.conj g0⁻¹).injective,
      Subgroup.card_map_of_injective adjEmb_injective,
      Subgroup.card_map_of_injective (MulAut.conj c).injective, hQcard]

private theorem zmod_quadratic {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : rk2Ord p n = 3) :
    ((2 : ZMod p) ^ n) ^ 2 + (2 : ZMod p) ^ n + 1 = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h3' : rk2Ord p n ∣ 3 := by rw [hrk]
  have h3 : p ∣ 2 ^ (n * 3) - 1 := (rk2Ord_dvd_iff 3).1 h3'
  have hx3 : ((2 : ZMod p) ^ n) ^ 3 = 1 := by
    have hcast : ((2 ^ (n * 3) - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h3
    rw [Nat.cast_sub (Nat.one_le_two_pow)] at hcast
    push_cast at hcast
    rw [pow_mul] at hcast
    exact sub_eq_zero.mp hcast
  have hxne : (2 : ZMod p) ^ n ≠ 1 := by
    intro h1
    have h0 : ((2 ^ n - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow)]
      push_cast
      rw [h1]
      ring
    have : p ∣ 2 ^ n - 1 := (ZMod.natCast_eq_zero_iff _ _).1 h0
    have := (rk2Ord_eq_one_iff (p := p) (n := n)).2 this
    omega
  have hprod : ((2 : ZMod p) ^ n - 1) * (((2 : ZMod p) ^ n) ^ 2 + (2 : ZMod p) ^ n + 1) = 0 := by
    have h : ((2 : ZMod p) ^ n - 1) * (((2 : ZMod p) ^ n) ^ 2 + (2 : ZMod p) ^ n + 1) =
        ((2 : ZMod p) ^ n) ^ 3 - 1 := by ring
    rw [h, hx3]; ring
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hxne)

private theorem ne_one_of_isA2A2Kernel {L : Type} [Field L]
    {x : ModGL Tag.E6 L} (hx : IsA2A2Kernel (torusRootKernel x)) : x ≠ 1 := by
  obtain ⟨w, hw⟩ := hx
  intro h1
  rw [h1] at hw
  have hroot : torusRootKernel (1 : ModGL Tag.E6 L) = {α | IsRoot Tag.E6 α} := by
    ext α
    constructor
    · rintro ⟨hα, -⟩
      exact hα
    · intro hα
      exact ⟨hα, 1, by simp [CFSG.LieType.Chevalley.rootDiagUnit_one], by simp [rootChar]⟩
  rw [hroot] at hw
  have himg : (w • ·) '' {α | IsRoot Tag.E6 α} = {α | IsRoot Tag.E6 α} := by
    ext α
    constructor
    · rintro ⟨β, hβ, rfl⟩
      exact IsRoot.smul hβ w
    · intro hα
      exact ⟨w⁻¹ • α, IsRoot.smul hα w⁻¹, by simp⟩
  rw [himg] at hw
  have hmem : (Pi.single (1 : Fin Tag.E6.rank) (1 : ℤ)) ∈ {α | IsRoot Tag.E6 α} :=
    IsRoot.basis 1
  rw [hw] at hmem
  have h0 := hmem.2 1 (by
    rw [(mem_supportA2A2 (1 : Fin Tag.E6.rank)).not]
    decide)
  norm_num at h0

theorem exists_A2A2_point {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : rk2Ord p n = 3)
    {A : Subgroup (ModGL Tag.E6 (AlgebraicClosure F))} (hA : IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 3)
    (hAT : A ≤ twistedTorus (phi3N (AlgebraicClosure F))
      (iterateFrobenius (AlgebraicClosure F) 2 n)) :
    ∃ x ∈ A, x ≠ 1 ∧ IsA2A2Kernel (torusRootKernel x) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  have hp5 : 5 < p := by
    have := seven_le_of_card hcard hp hp2 hrk
    omega
  have hFr : ∀ c, iterateFrobenius (AlgebraicClosure F) 2 n c = c ^ Nat.card F := by
    intro c
    rw [iterateFrobenius_def, hcard]
  have hq0 : ((Nat.card F : ℕ) : ZMod p) ^ 2 + ((Nat.card F : ℕ) : ZMod p) + 1 = 0 := by
    have h := zmod_quadratic hp hp2 hrk
    rw [hcard]
    push_cast
    exact h
  set q' : ℕ := p - Nat.card F % p with hq'def
  have hq'val : ((q' : ℕ) : ZMod p) = -((Nat.card F : ℕ) : ZMod p) := by
    have hrle : Nat.card F % p ≤ p := le_of_lt (Nat.mod_lt _ hp.pos)
    rw [hq'def, Nat.cast_sub hrle, ZMod.natCast_self, ZMod.natCast_mod]
    ring
  have hq' : ((q' : ZMod p)) ^ 2 - (q' : ZMod p) + 1 = 0 := by
    rw [hq'val]
    linear_combination hq0
  have hq'neg : ((Nat.card F : ℕ) : ZMod p) = -((q' : ℕ) : ZMod p) := by
    rw [hq'val]; ring
  have hcount : Nat.card {z : Fin Tag.E6.rank → ZMod p //
      (CFSG.RankThree.E6.dualMatrix (ZMod p) e6T3W) *ᵥ z =
        ((Nat.card F : ℕ) : ZMod p) • z} = p ^ 3 := by
    have h := CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6.tw6Six_charSpace_card
      (p := p) (q := q') hp5 hq'
    have hval : -((q' : ℕ) : ZMod p) = ((Nat.card F : ℕ) : ZMod p) := by
      rw [hq'val]; ring
    let e : {z : Fin Tag.E6.rank → ZMod p //
        (CFSG.RankThree.E6.dualMatrix (ZMod p) e6T3W) *ᵥ z = -((q' : ℕ) : ZMod p) • z} ≃
        {z : Fin Tag.E6.rank → ZMod p //
        (CFSG.RankThree.E6.dualMatrix (ZMod p) e6T3W) *ᵥ z =
          ((Nat.card F : ℕ) : ZMod p) • z} :=
      Equiv.subtypeEquivRight (fun z => by rw [hval])
    exact (Nat.card_congr e).symm.trans h
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_units (L := AlgebraicClosure F) (ℓ := 2)
    Nat.prime_two hp hp2
  obtain ⟨x, hxA, -, -, -, hxker, -, -⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three.exists_second_point_of_A2A2
      (Ω := AlgebraicClosure F) (q₀ := Nat.card F) (q := q') hp5 hFr hq0
      hq' hq'neg hcount hζ hA hAcard hAT
  exact ⟨x, hxA, ne_one_of_isA2A2Kernel hxker, hxker⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
