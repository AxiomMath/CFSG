module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallReeBorel
public import CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.SmallReeWard
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeFixedPoints

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallReeF2Core

open CFSG.LieType.Ree CFSG.ComponentClassification.LiteratureLocal.SmallRee
open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallReeBorel
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SignalizerFunctorTheorem.CatalogBridge (frobeniusΓ_eq_reeGammaFieldAut)
open scoped Pointwise


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem sq_pow_four {G : Type} [Group G] (f : G) : (f * f) ^ 2 = f ^ 4 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq f, mul_assoc, ← mul_assoc f f, ← sq]
  simp [sq, mul_assoc]

theorem frob_sq_eq : (ReeTag.G2.finiteFrobeniusAut K) ^ 2 = (ReeTag.G2.finiteExceptionalAut K) ^ 4 := by
  rw [← CFSG.LieType.Chevalley.finiteExceptionalAut_mul_self ReeTag.G2]
  exact sq_pow_four _

theorem phi_cube_fix (g : ReeTag.G2.reeGamma K 1) :
    (ReeTag.G2.finiteExceptionalAut K ^ 3) (CFSG.RankThree.reeGammaToAdjoint 1 g) =
      CFSG.RankThree.reeGammaToAdjoint 1 g := by
  obtain ⟨hg, h⟩ := ReeTag.mem_reeGamma.1 g.2
  rw [CFSG.RankThree.finiteReeAut_eq_pow 1] at h
  exact h

theorem frob_two_apply (g : ReeTag.G2.reeGamma K 1) :
    CFSG.RankThree.reeGammaToAdjoint 1 ((frobeniusΓ ^ 2) g) =
      ReeTag.G2.finiteExceptionalAut K (CFSG.RankThree.reeGammaToAdjoint 1 g) := by
  have hg : (g : ModGL ReeTag.G2.tag K) ∈ adjointGroup ReeTag.G2.tag K :=
    (ReeTag.mem_reeGamma.1 g.2).1
  have h4 : (ReeTag.G2.finiteFrobeniusAut K ^ 2) (CFSG.RankThree.reeGammaToAdjoint 1 g) =
      ReeTag.G2.finiteExceptionalAut K (CFSG.RankThree.reeGammaToAdjoint 1 g) := by
    rw [frob_sq_eq, show (ReeTag.G2.finiteExceptionalAut K) ^ 4 =
      ReeTag.G2.finiteExceptionalAut K * (ReeTag.G2.finiteExceptionalAut K) ^ 3 by
        rw [← pow_succ'],
      MulAut.mul_apply, phi_cube_fix]
  apply Subtype.ext
  have e := congrArg Subtype.val h4
  change ((frobeniusΓ ^ 2) g : ModGL ReeTag.G2.tag K) = _
  rw [coe_frobeniusΓ_pow 2 g hg]
  exact e

@[expose] noncomputable def fix3 (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime] : Subfield K :=
  fixSubfield (frobRing : K ≃+* K)

theorem frobRing_three (hK : Nat.card K = 27) : (frobRing : K ≃+* K) ^ 3 = 1 := by
  ext x
  rw [frobRing_pow_apply]
  show x ^ 3 ^ 3 = x
  haveI := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rw [← Nat.card_eq_fintype_card, hK] at h
  norm_num
  exact h

theorem frobRing_ne_one (hK : Nat.card K = 27) : (frobRing : K ≃+* K) ≠ 1 := by
  intro h
  have hroot : ∀ x : K, x ^ 3 = x := fun x => by
    have := frobRing_pow_apply (K := K) 1 x
    rw [pow_one, h] at this
    change x = x ^ 3 ^ 1 at this
    norm_num at this
    exact this.symm
  haveI := Fintype.ofFinite K
  have hdeg : (Polynomial.X ^ 3 - Polynomial.X : Polynomial K).natDegree = 3 := by
    compute_degree!
  have hne : (Polynomial.X ^ 3 - Polynomial.X : Polynomial K) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    norm_num at hdeg
  have hsub : (Finset.univ : Finset K).val ⊆ (Polynomial.X ^ 3 - Polynomial.X : Polynomial K).roots := by
    intro x _
    rw [Polynomial.mem_roots hne]
    simp [Polynomial.IsRoot, hroot x]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg] at hle
  have hc : Fintype.card K = 27 := by rw [← Nat.card_eq_fintype_card, hK]
  simp only [Finset.card_univ, hc] at hle
  norm_num at hle

theorem orderOf_frobRing (hK : Nat.card K = 27) : orderOf (frobRing : K ≃+* K) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (frobRing_three hK) (frobRing_ne_one hK)

theorem card_fix3 (hK : Nat.card K = 27) : Nat.card (fix3 K) = 3 := by
  have h := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 3) (f := 3) Nat.prime_three
    (by norm_num) hK (frobRing : K ≃+* K)
  rw [orderOf_frobRing hK] at h
  simpa [fix3] using h.2

theorem mem_fix3_iff (t : K) : t ∈ fix3 K ↔ t ^ 3 = t := by
  rw [fix3, mem_fixSubfield]
  have h := frobRing_pow_apply (K := K) 1 t
  rw [pow_one] at h
  rw [h]
  norm_num

theorem sigma_fix3 {t : K} (ht : t ∈ fix3 K) : smallReeSigma 1 t = t := by
  have h3 := (mem_fix3_iff t).1 ht
  show t ^ (3 * 3 ^ 1) = t
  rw [show 3 * 3 ^ 1 = 3 * 3 by norm_num, pow_mul, h3, h3]

@[expose] noncomputable def gam0 : Subgroup (ReeTag.G2.reeGamma K 1) :=
  (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K 1)).toMonoidHom.eqLocus (MonoidHom.id _)

theorem mem_gam0 {x : ReeTag.G2.reeGamma K 1} : x ∈ gam0 ↔ frobeniusΓ x = x := by
  unfold gam0
  exact Iff.rfl

theorem card_gam0 (hK : Nat.card K = 27) : Nat.card (gam0 : Subgroup (ReeTag.G2.reeGamma K 1)) = 1512 := by
  have hP := card_fix3 hK
  have e : (gam0 : Subgroup (ReeTag.G2.reeGamma K 1)) =
      ((ReeTag.G2.reeGammaFieldAut K 1 (frobRing : K ≃+* K)).toMonoidHom.eqLocus (MonoidHom.id _)) := by
    unfold gam0
    rw [frobeniusΓ_eq_reeGammaFieldAut]
  have h := CFSG.RankThree.fixed_reeGamma_eq_map (K := K) (a := 1) (b := 0) (d := 1) (m := 1)
    (frobRing : K ≃+* K) (show Nat.card (fix3 K) = 3 ^ 1 by rw [hP]; norm_num) (by norm_num)
  have hc3 : Nat.card (fix3 K) = 3 ^ (2 * 0 + 1) := by rw [hP]; norm_num
  have h1 : Nat.card (gam0 : Subgroup (ReeTag.G2.reeGamma K 1)) =
      Nat.card (Subgroup.map (ReeTag.G2.reeGamma K 1).subtype gam0) :=
    (Subgroup.card_map_of_injective Subtype.val_injective).symm
  have hcard0 : Nat.card (ReeTag.G2.reeGamma (↥(fix3 K)) 0) = 1512 := by
    rw [CFSG.ComponentClassification.LiteratureLocal.G2_card_reeGamma (a := 0) hc3]
    norm_num
  rw [h1, e, h, Subgroup.card_map_of_injective (baseChangeGL_injective (f := (fixSubfield (frobRing : K ≃+* K)).subtype))]
  exact hcard0

theorem sigma_of_cube {t : K} (ht : t ^ 3 = t) : smallReeSigma 1 t = t :=
  sigma_fix3 ((mem_fix3_iff t).2 ht)

theorem cube_add {x y : K} (hx : x ^ 3 = x) (hy : y ^ 3 = y) : (x + y) ^ 3 = x + y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [add_pow_char, hx, hy]

theorem cube_mul {x y : K} (hx : x ^ 3 = x) (hy : y ^ 3 = y) : (x * y) ^ 3 = x * y := by
  rw [mul_pow, hx, hy]

theorem cube_neg {x : K} (hx : x ^ 3 = x) : (-x) ^ 3 = -x := by
  calc (-x) ^ 3 = -(x ^ 3) := by ring
    _ = -x := by rw [hx]

theorem cube_sub {x y : K} (hx : x ^ 3 = x) (hy : y ^ 3 = y) : (x - y) ^ 3 = x - y := by
  rw [sub_eq_add_neg, cube_add hx (cube_neg hy)]

theorem uIn_mul_inv_fix3 (hK : Nat.card K = 3 ^ (2 * 1 + 1)) {t b c : K} (ht : t ^ 3 = t) :
    uIn hK t b c * uIn hK (-t) (-b + t * t) (-c - b * t - t * t ^ 2) = 1 := by
  rw [uIn_mul, sigma_of_cube ht, ← uIn_zero hK]
  congr 1
  · ring
  · ring
  · ring

@[expose] noncomputable def qSub (hK : Nat.card K = 3 ^ (2 * 1 + 1)) :
    Subgroup (ReeTag.G2.reeGamma K 1) where
  carrier := {x | ∃ t : K, t ^ 3 = t ∧ ∃ b : K, b ^ 3 = b ∧ ∃ c : K, c ^ 3 = c ∧ x = uIn hK t b c}
  mul_mem' := by
    intro x y hx hy
    obtain ⟨t, ht, b, hb, c, hc, rfl⟩ := hx
    obtain ⟨s, hs, d, hd, e, he, rfl⟩ := hy
    refine ⟨t + s, cube_add ht hs, b + d + smallReeSigma 1 t * s, ?_,
      c + e - b * s + smallReeSigma 1 t * s ^ 2, ?_, uIn_mul hK t b c s d e⟩
    · rw [sigma_of_cube ht]
      exact cube_add (cube_add hb hd) (cube_mul ht hs)
    · rw [sigma_of_cube ht]
      exact cube_add (cube_sub (cube_add hc he) (cube_mul hb hs))
        (cube_mul ht (by rw [pow_two]; exact cube_mul hs hs))
  one_mem' := ⟨0, by norm_num, 0, by norm_num, 0, by norm_num, (uIn_zero hK).symm⟩
  inv_mem' := by
    intro x hx
    obtain ⟨t, ht, b, hb, c, hc, rfl⟩ := hx
    refine ⟨-t, cube_neg ht, -b + t * t, ?_, -c - b * t - t * t ^ 2, ?_, ?_⟩
    · exact cube_add (cube_neg hb) (cube_mul ht ht)
    · exact cube_sub (cube_sub (cube_neg hc) (cube_mul hb ht))
        (cube_mul ht (by rw [pow_two]; exact cube_mul ht ht))
    · exact inv_eq_of_mul_eq_one_right (uIn_mul_inv_fix3 hK ht)

@[expose] noncomputable def q0Sub (hK : Nat.card K = 3 ^ (2 * 1 + 1)) :
    Subgroup (ReeTag.G2.reeGamma K 1) where
  carrier := {x | ∃ b : K, b ^ 3 = b ∧ ∃ c : K, c ^ 3 = c ∧ x = uIn hK 0 b c}
  mul_mem' := by
    intro x y hx hy
    obtain ⟨b, hb, c, hc, rfl⟩ := hx
    obtain ⟨d, hd, e, he, rfl⟩ := hy
    refine ⟨b + d, cube_add hb hd, c + e, cube_add hc he, ?_⟩
    rw [uIn_mul]
    simp [smallReeSigma_zero]
  one_mem' := ⟨0, by norm_num, 0, by norm_num, (uIn_zero hK).symm⟩
  inv_mem' := by
    intro x hx
    obtain ⟨b, hb, c, hc, rfl⟩ := hx
    refine ⟨-b, cube_neg hb, -c, cube_neg hc, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [uIn_mul]
    simp [smallReeSigma_zero, uIn_zero hK]

theorem mem_qSub_iff (hK : Nat.card K = 3 ^ (2 * 1 + 1)) (x : ReeTag.G2.reeGamma K 1) :
    x ∈ qSub hK ↔ ∃ t : K, t ^ 3 = t ∧ ∃ b : K, b ^ 3 = b ∧ ∃ c : K, c ^ 3 = c ∧ x = uIn hK t b c :=
  Iff.rfl

theorem mem_q0Sub_iff (hK : Nat.card K = 3 ^ (2 * 1 + 1)) (x : ReeTag.G2.reeGamma K 1) :
    x ∈ q0Sub hK ↔ ∃ b : K, b ^ 3 = b ∧ ∃ c : K, c ^ 3 = c ∧ x = uIn hK 0 b c :=
  Iff.rfl

theorem qSub_eq_range (hK : Nat.card K = 3 ^ (2 * 1 + 1)) :
    (qSub hK : Set (ReeTag.G2.reeGamma K 1)) =
      Set.range (fun p : fix3 K × fix3 K × fix3 K => uIn hK (p.1 : K) (p.2.1 : K) (p.2.2 : K)) := by
  ext x
  constructor
  · rintro ⟨t, ht, b, hb, c, hc, rfl⟩
    exact ⟨(⟨t, (mem_fix3_iff t).2 ht⟩, ⟨b, (mem_fix3_iff b).2 hb⟩, ⟨c, (mem_fix3_iff c).2 hc⟩), rfl⟩
  · rintro ⟨⟨⟨t, ht⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, rfl⟩
    exact ⟨t, (mem_fix3_iff t).1 ht, b, (mem_fix3_iff b).1 hb, c, (mem_fix3_iff c).1 hc, rfl⟩

theorem q0Sub_eq_range (hK : Nat.card K = 3 ^ (2 * 1 + 1)) :
    (q0Sub hK : Set (ReeTag.G2.reeGamma K 1)) =
      Set.range (fun p : fix3 K × fix3 K => uIn hK 0 (p.1 : K) (p.2 : K)) := by
  ext x
  constructor
  · rintro ⟨b, hb, c, hc, rfl⟩
    exact ⟨(⟨b, (mem_fix3_iff b).2 hb⟩, ⟨c, (mem_fix3_iff c).2 hc⟩), rfl⟩
  · rintro ⟨⟨⟨b, hb⟩, ⟨c, hc⟩⟩, rfl⟩
    exact ⟨b, (mem_fix3_iff b).1 hb, c, (mem_fix3_iff c).1 hc, rfl⟩

theorem card_qSub (hK : Nat.card K = 3 ^ (2 * 1 + 1)) : Nat.card (qSub hK) = 27 := by
  have hK27 : Nat.card K = 27 := by rw [hK]; norm_num
  have hinj : Function.Injective
      (fun p : fix3 K × fix3 K × fix3 K => uIn hK (p.1 : K) (p.2.1 : K) (p.2.2 : K)) := by
    rintro ⟨⟨t, _⟩, ⟨b, _⟩, ⟨c, _⟩⟩ ⟨⟨t', _⟩, ⟨b', _⟩, ⟨c', _⟩⟩ h
    dsimp only at h
    obtain ⟨rfl, rfl, rfl⟩ := uIn_inj hK h
    rfl
  have e : Nat.card (qSub hK) = Nat.card (Set.range
      (fun p : fix3 K × fix3 K × fix3 K => uIn hK (p.1 : K) (p.2.1 : K) (p.2.2 : K))) :=
    congrArg (fun s : Set (ReeTag.G2.reeGamma K 1) => Nat.card s) (qSub_eq_range hK)
  rw [e, Nat.card_range_of_injective hinj, Nat.card_prod, Nat.card_prod, card_fix3 hK27]

theorem card_q0Sub (hK : Nat.card K = 3 ^ (2 * 1 + 1)) : Nat.card (q0Sub hK) = 9 := by
  have hK27 : Nat.card K = 27 := by rw [hK]; norm_num
  have hinj : Function.Injective (fun p : fix3 K × fix3 K => uIn hK 0 (p.1 : K) (p.2 : K)) := by
    rintro ⟨⟨b, _⟩, ⟨c, _⟩⟩ ⟨⟨b', _⟩, ⟨c', _⟩⟩ h
    dsimp only at h
    obtain ⟨-, rfl, rfl⟩ := uIn_inj hK h
    rfl
  have e : Nat.card (q0Sub hK) = Nat.card (Set.range
      (fun p : fix3 K × fix3 K => uIn hK 0 (p.1 : K) (p.2 : K))) :=
    congrArg (fun s : Set (ReeTag.G2.reeGamma K 1) => Nat.card s) (q0Sub_eq_range hK)
  rw [e, Nat.card_range_of_injective hinj, Nat.card_prod, card_fix3 hK27]

theorem qSub_le_gam0 (hK : Nat.card K = 3 ^ (2 * 1 + 1)) : qSub hK ≤ gam0 := by
  intro x hx
  obtain ⟨t, ht, b, hb, c, hc, rfl⟩ := hx
  rw [mem_gam0]
  have h := frobeniusΓ_pow_uIn hK 1 t b c
  simp only [pow_one] at h
  rw [h, ht, hb, hc]

theorem mem_q0_of_cube (hK : Nat.card K = 3 ^ (2 * 1 + 1)) {x : ReeTag.G2.reeGamma K 1}
    (hx : x ∈ qSub hK) (h3 : x ^ 3 = 1) : x ∈ q0Sub hK := by
  obtain ⟨t, ht, b, hb, c, hc, rfl⟩ := hx
  rw [uIn_pow_three hK t b c] at h3
  have h0 : uIn hK 0 0 (-(t ^ 2 * smallReeSigma 1 t)) = uIn hK 0 0 0 := by
    rw [h3, uIn_zero]
  obtain ⟨-, -, h⟩ := uIn_inj hK h0
  rw [sigma_of_cube ht] at h
  have ht3 : t ^ 3 = 0 := by linear_combination -h
  rw [ht] at ht3
  subst ht3
  exact ⟨b, hb, c, hc, rfl⟩

theorem conj_pow3 {G : Type} [Group G] (a b : G) : (a * b * a⁻¹) ^ 3 = a * b ^ 3 * a⁻¹ := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
    mul_inv_cancel, mul_one]

theorem fact_1512 : Nat.factorization 1512 3 = 3 := by
  rw [show (1512 : ℕ) = 3 ^ 3 * 56 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three]
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

set_option maxHeartbeats 400000 in
theorem exists_conj_z0_mem (hK : Nat.card K = 3 ^ (2 * 1 + 1)) (X : Subgroup (ReeTag.G2.reeGamma K 1))
    (hX0 : X ≤ gam0) (hX9 : Nat.card X = 9) (hX3 : ∀ x ∈ X, x ^ 3 = 1) :
    ∃ g : ReeTag.G2.reeGamma K 1, g * uIn hK 0 0 1 * g⁻¹ ∈ X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK27 : Nat.card K = 27 := by rw [hK]; norm_num
  have hG0 : Nat.card (gam0 : Subgroup (ReeTag.G2.reeGamma K 1)) = 1512 := card_gam0 hK27
  have hQle : qSub hK ≤ gam0 := qSub_le_gam0 hK
  obtain ⟨Qs, hQsdef⟩ : ∃ Qs : Subgroup (gam0 : Subgroup (ReeTag.G2.reeGamma K 1)),
      Qs = (qSub hK).subgroupOf gam0 := ⟨_, rfl⟩
  have hQs : Nat.card Qs =
      3 ^ (Nat.card (gam0 : Subgroup (ReeTag.G2.reeGamma K 1))).factorization 3 := by
    rw [hQsdef, hG0, fact_1512, show (3 : ℕ) ^ 3 = 27 by norm_num, ← card_qSub hK]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv
  obtain ⟨QS, hQSc⟩ : ∃ QS : Sylow 3 (gam0 : Subgroup (ReeTag.G2.reeGamma K 1)),
      (QS : Subgroup (gam0 : Subgroup (ReeTag.G2.reeGamma K 1))) = Qs :=
    ⟨Sylow.ofCard Qs hQs, Sylow.coe_ofCard _ _⟩
  have hXs : IsPGroup 3 (X.subgroupOf gam0) := by
    apply IsPGroup.of_card (n := 2)
    have : Nat.card (X.subgroupOf gam0) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX0).toEquiv
    rw [this, hX9]
    norm_num
  obtain ⟨P, hP⟩ := hXs.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥(gam0 : Subgroup (ReeTag.G2.reeGamma K 1))) QS P
  have hsub : X ≤ (q0Sub hK).map (MulAut.conj (g : ReeTag.G2.reeGamma K 1)).toMonoidHom := by
    intro x hx
    have hxP : (⟨x, hX0 hx⟩ : gam0) ∈ (P : Subgroup (gam0 : Subgroup (ReeTag.G2.reeGamma K 1))) :=
      hP (Subgroup.mem_subgroupOf.2 hx)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxP
    obtain ⟨q, hq, hqx⟩ := hxP
    rw [hQSc, hQsdef] at hq
    have hqΓ : (q : ReeTag.G2.reeGamma K 1) ∈ qSub hK := Subgroup.mem_subgroupOf.1 hq
    have hxeq : (g : ReeTag.G2.reeGamma K 1) * (q : ReeTag.G2.reeGamma K 1) *
        (g : ReeTag.G2.reeGamma K 1)⁻¹ = x := congrArg Subtype.val hqx
    have hq3 : (q : ReeTag.G2.reeGamma K 1) ^ 3 = 1 := by
      have h := hX3 x hx
      rw [← hxeq] at h
      have h' : (g : ReeTag.G2.reeGamma K 1) * (q : ReeTag.G2.reeGamma K 1) ^ 3 *
          (g : ReeTag.G2.reeGamma K 1)⁻¹ = 1 := by
        rw [← h, conj_pow3]
      calc (q : ReeTag.G2.reeGamma K 1) ^ 3
          = (g : ReeTag.G2.reeGamma K 1)⁻¹ * ((g : ReeTag.G2.reeGamma K 1) *
              (q : ReeTag.G2.reeGamma K 1) ^ 3 * (g : ReeTag.G2.reeGamma K 1)⁻¹) *
              (g : ReeTag.G2.reeGamma K 1) := by group
        _ = 1 := by rw [h']; group
    refine Subgroup.mem_map.2 ⟨(q : ReeTag.G2.reeGamma K 1), mem_q0_of_cube hK hqΓ hq3, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hxeq
  have hcardmap : Nat.card ((q0Sub hK).map (MulAut.conj (g : ReeTag.G2.reeGamma K 1)).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (g : ReeTag.G2.reeGamma K 1)).injective,
      card_q0Sub hK]
  have heq := Subgroup.eq_of_le_of_card_ge hsub (by rw [hcardmap, hX9])
  refine ⟨(g : ReeTag.G2.reeGamma K 1), ?_⟩
  rw [heq]
  refine Subgroup.mem_map.2 ⟨uIn hK 0 0 1, ?_, ?_⟩
  · exact (mem_q0Sub_iff hK _).2 ⟨0, by norm_num, 1, by norm_num, rfl⟩
  · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem commute_z_gen (hK : Nat.card K = 3 ^ (2 * 1 + 1)) (t b c e : K) :
    uIn hK t b c * uIn hK 0 0 e = uIn hK 0 0 e * uIn hK t b c := by
  rw [uIn_mul, uIn_mul]
  congr 1 <;> simp [smallReeSigma_zero] <;> ring

theorem no_invol_centralizes_z0 (hK : Nat.card K = 3 ^ (2 * 1 + 1)) {y : ReeTag.G2.reeGamma K 1}
    (hy2 : y * y = 1) (hy1 : y ≠ 1) (hyz : y * uIn hK 0 0 1 = uIn hK 0 0 1 * y) : False := by
  have hz0 : uIn hK 0 0 1 ∈ ub K := uIn_mem_ub hK 0 0 1
  have hz0n : uIn hK 0 0 1 ≠ 1 := by
    intro h
    rw [← uIn_zero hK] at h
    exact one_ne_zero (uIn_inj hK h).2.2
  have hzξ : uIn hK 0 0 1 • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K) =
      QuotientGroup.mk 1 :=
    (smul_base_eq_iff hK _).2 (ub_le_bor hz0)
  have hfix : uIn hK 0 0 1 • (y • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K)) =
      y • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K) := by
    rw [← mul_smul, ← hyz, mul_smul, hzξ]
  have hy_bor : y ∈ bor K := (smul_base_eq_iff hK y).1 (reg_ub hK hz0 hz0n hfix)
  obtain ⟨u, hu, hyu⟩ := invol_bor hK hy_bor hy2 hy1
  have hconj : y * uIn hK 0 0 1 * y⁻¹ = uIn hK 0 0 1 := by
    rw [hyz, mul_assoc, mul_inv_cancel, mul_one]
  have hz' : hIn hK (-1) * uIn hK 0 0 1 * (hIn hK (-1))⁻¹ = uIn hK 0 0 (-1) := by
    rw [conj_z hK (-1)]
    norm_num
  obtain ⟨t, b, c, rfl⟩ := exists_uIn_of_mem_ub hK hu
  have hcomm : uIn hK t b c * uIn hK 0 0 (-1) = uIn hK 0 0 (-1) * uIn hK t b c :=
    commute_z_gen hK t b c (-1)
  have e : y * uIn hK 0 0 1 * y⁻¹ = uIn hK t b c * (hIn hK (-1) * uIn hK 0 0 1 * (hIn hK (-1))⁻¹) *
      (uIn hK t b c)⁻¹ := by
    rw [hyu]
    group
  have h1 : uIn hK 0 0 1 = uIn hK 0 0 (-1) := by
    calc uIn hK 0 0 1 = y * uIn hK 0 0 1 * y⁻¹ := hconj.symm
      _ = uIn hK t b c * uIn hK 0 0 (-1) * (uIn hK t b c)⁻¹ := by rw [e, hz']
      _ = uIn hK 0 0 (-1) := by rw [hcomm]; group
  have h2 : (1 : K) = -1 := (uIn_inj hK h1).2.2
  exact two_ne_zero_of_charP (by linear_combination h2)

theorem f2_core (hK : Nat.card K = 3 ^ (2 * 1 + 1)) (X : Subgroup (ReeTag.G2.reeGamma K 1))
    (hX0 : X ≤ gam0) (hX9 : Nat.card X = 9) (hX3 : ∀ x ∈ X, x ^ 3 = 1)
    {y : ReeTag.G2.reeGamma K 1} (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hXy : ∀ x ∈ X, x * y = y * x) : False := by
  obtain ⟨g, hg⟩ := exists_conj_z0_mem hK X hX0 hX9 hX3
  have hc := hXy _ hg
  refine no_invol_centralizes_z0 hK (y := g⁻¹ * y * g) ?_ ?_ ?_
  · calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
      _ = 1 := by rw [hy2]; group
  · intro h
    apply hy1
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h]
      _ = 1 := by group
  · calc g⁻¹ * y * g * uIn hK 0 0 1 = g⁻¹ * (y * (g * uIn hK 0 0 1 * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * uIn hK 0 0 1 * g⁻¹) * y) * g := by rw [hc]
      _ = uIn hK 0 0 1 * (g⁻¹ * y * g) := by group

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallReeF2Core
