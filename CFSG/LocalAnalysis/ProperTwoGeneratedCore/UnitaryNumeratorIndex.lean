module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoSectionEightFour
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerTorusIndex
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryModel
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.ProperTwoGeneratedCore.CosetNormalizer
open scoped Pointwise

universe u v

theorem eq_one_of_mul_self_eq_one_of_odd_card {A : Type u} [Group A] (K : Subgroup A)
    (hK : Odd (Nat.card K)) {r : A} (hr : r ∈ K) (hrr : r * r = 1) : r = 1 := by
  have h2 : orderOf (⟨r, hr⟩ : K) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using hrr))
  have hodd' : Odd (orderOf (⟨r, hr⟩ : K)) := Odd.of_dvd_nat hK (orderOf_dvd_natCard _)
  have h1 : orderOf (⟨r, hr⟩ : K) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)

theorem card_inverted_eq_of_odd_kernel {A : Type u} {P : Type v} [Group A] [Group P] [Finite A]
    (hA : ∀ a b : A, a * b = b * a) (σ : A →* A) (ρ : A →* P) (g : P)
    (hcomm : ∀ a, ρ (σ a) = g⁻¹ * ρ a * g)
    (hodd : Odd (Nat.card ρ.ker)) (hfix : ∀ r ∈ ρ.ker, σ r = r) :
    Nat.card {a : A // σ a = a⁻¹} =
      Nat.card {c : P // c ∈ ρ.range ∧ g⁻¹ * c * g = c⁻¹} := by
  classical
  have hker_sq : ∀ r ∈ ρ.ker, r * r = 1 → r = 1 := fun r hr hrr =>
    eq_one_of_mul_self_eq_one_of_odd_card ρ.ker hodd hr hrr
  have hker_sqrt : ∀ k ∈ ρ.ker, ∃ r ∈ ρ.ker, r * r = k := by
    intro k hk
    obtain ⟨m, hm⟩ := hodd
    refine ⟨k ^ (m + 1), ρ.ker.pow_mem hk _, ?_⟩
    have hk1 : k ^ Nat.card ρ.ker = 1 := by
      have h' := congrArg Subtype.val (pow_card_eq_one' (G := ρ.ker) (x := ⟨k, hk⟩))
      rwa [SubgroupClass.coe_pow] at h'
    rw [← pow_add, show m + 1 + (m + 1) = Nat.card ρ.ker + 1 by omega, pow_succ, hk1, one_mul]
  let F : {a : A // σ a = a⁻¹} → {c : P // c ∈ ρ.range ∧ g⁻¹ * c * g = c⁻¹} := fun a =>
    ⟨ρ a, ⟨a, rfl⟩, by rw [← hcomm, a.2, map_inv]⟩
  have hF : Function.Bijective F := by
    constructor
    · intro a b hab
      have hρab : ρ (a.1 * b.1⁻¹) = 1 := by
        have := congrArg Subtype.val hab
        simp only [F] at this
        rw [map_mul, map_inv, this, mul_inv_cancel]
      have hk : a.1 * b.1⁻¹ ∈ ρ.ker := hρab
      have hσ := hfix _ hk
      rw [map_mul, map_inv, a.2, b.2, inv_inv] at hσ
      have hsq : (a.1 * b.1⁻¹) * (a.1 * b.1⁻¹) = 1 := by
        calc (a.1 * b.1⁻¹) * (a.1 * b.1⁻¹) = (a.1⁻¹ * b.1) * (a.1 * b.1⁻¹) := by rw [hσ]
          _ = 1 := by
            rw [hA a.1⁻¹ b.1, mul_assoc, ← mul_assoc a.1⁻¹ a.1, inv_mul_cancel, one_mul,
              mul_inv_cancel]
      exact Subtype.ext (mul_inv_eq_one.mp (hker_sq _ hk hsq))
    · rintro ⟨c, ⟨a, rfl⟩, hc⟩
      have hk : σ a * a ∈ ρ.ker := by
        change ρ (σ a * a) = 1
        rw [map_mul, hcomm, hc, inv_mul_cancel]
      obtain ⟨r, hr, hrr⟩ := hker_sqrt _ (ρ.ker.inv_mem hk)
      refine ⟨⟨a * r, ?_⟩, ?_⟩
      · rw [map_mul, hfix r hr]
        apply eq_inv_of_mul_eq_one_left
        calc σ a * r * (a * r) = σ a * (r * a) * r := by simp only [mul_assoc]
          _ = σ a * (a * r) * r := by rw [hA r a]
          _ = σ a * a * (r * r) := by simp only [mul_assoc]
          _ = 1 := by rw [hrr, mul_inv_cancel]
      · apply Subtype.ext
        change ρ (a * r) = ρ a
        rw [map_mul, hr, mul_one]
  exact Nat.card_congr (Equiv.ofBijective F hF)

variable {G : Type u} [Group G]

theorem flip_mem_normalizer_pairPointStabilizer [Finite G] {H : Subgroup G} {z : G}
    (hz : orderOf z = 2) {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    t ∈ Subgroup.normalizer (pairPointStabilizer H beta : Set G) := by
  have := pair_stabilizer_normal hz hbeta ht
  exact Subgroup.le_normalizer_of_normal_subgroupOf
    (pairPointStabilizer_le_pairFlipGroup H beta t) (flip_mem_pairFlipGroup H beta t)

theorem commutator_pairPointStabilizer_le [Finite G] {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    ⁅pairPointStabilizer H beta, Subgroup.zpowers t⁆ ≤ pairOddCore H beta := by
  obtain ⟨hcen, -⟩ := pair_flip_zStar_factorization h S hzS hzcenter hbeta ht
  set K := pairFlipGroup H beta t
  set J := (pairOddCore H beta).subgroupOf K
  have : J.Normal := pairOddCore_normal_in_pair_group h.distinguished_order hbeta ht
  rw [Subgroup.commutator_le]
  intro e he x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have heK : e ∈ K := pairPointStabilizer_le_pairFlipGroup H beta t he
  have htK : t ∈ K := flip_mem_pairFlipGroup H beta t
  set e' : K := ⟨e, heK⟩
  set t' : K := ⟨t, htK⟩
  have hmem : e' * t' ^ k * e'⁻¹ * (t' ^ k)⁻¹ ∈ J := by
    rw [← QuotientGroup.eq_one_iff]
    have hc := Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hcen k) (e' : K ⧸ J)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow] at hc ⊢
    rw [hc]
    group
    rw [← zpow_add, add_neg_cancel, zpow_zero]
  have h' := Subgroup.mem_subgroupOf.mp hmem
  simpa [commutatorElement_def, e', t'] using h'

section Main

theorem pointRightCosetMul_inv_eq_self_iff (H : Subgroup G) (omega : pointRightCosetSpace H)
    (g : G) : pointRightCosetMul H omega g⁻¹ = omega ↔ pointRightCosetMul H omega g = omega := by
  constructor
  · intro h
    calc pointRightCosetMul H omega g
        = pointRightCosetMul H (pointRightCosetMul H omega g⁻¹) g := by rw [h]
      _ = omega := by rw [pointRightCosetMul_mul, inv_mul_cancel, pointRightCosetMul_one]
  · intro h
    calc pointRightCosetMul H omega g⁻¹
        = pointRightCosetMul H (pointRightCosetMul H omega g) g⁻¹ := by rw [h]
      _ = omega := by rw [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one]

theorem mem_rightCosetStabilizer_iff_pointRightCosetMul (H : Subgroup G)
    (omega : rightCosetSpace H) (g : G) :
    g ∈ rightCosetStabilizer H omega ↔ pointRightCosetMul H omega g = omega := by
  rw [mem_rightCosetStabilizer_iff,
    LocalCriterionInvariantNormalizer.pointRightCosetMul_eq_translate]

theorem centralizer_zpowers_sup_zpowers (w t : G) :
    Subgroup.centralizer ((Subgroup.zpowers w ⊔ Subgroup.zpowers t : Subgroup G) : Set G) =
      Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    exact ⟨(Subgroup.mem_centralizer_iff.mp hg w
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers w))).symm,
      (Subgroup.mem_centralizer_iff.mp hg t
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))).symm⟩
  · rintro ⟨h1, h2⟩
    have hle : Subgroup.zpowers w ⊔ Subgroup.zpowers t ≤ Subgroup.centralizer ({g} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h1.symm))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h2.symm))
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem odd_torus_card {f : ℕ} (hf : 1 ≤ f) :
    Odd (((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1)) := by
  have hdvd : Nat.gcd 3 (2 ^ f + 1) ∣ (2 ^ f) ^ 2 - 1 := by
    refine (Nat.gcd_dvd_right _ _).trans ?_
    rw [show (2 ^ f) ^ 2 - 1 = (2 ^ f) ^ 2 - 1 ^ 2 by rw [one_pow], Nat.sq_sub_sq]
    exact dvd_mul_right _ _
  have hev : Even ((2 ^ f) ^ 2) :=
    (Nat.even_pow.mpr ⟨(Nat.even_pow.mpr ⟨even_two, by omega⟩), two_ne_zero⟩)
  have hpos : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hodd : Odd ((2 ^ f) ^ 2 - 1) := Nat.Even.sub_odd hpos hev odd_one
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, Nat.mul_div_cancel_left _ (Nat.gcd_pos_of_pos_left _ (by norm_num))]
  rw [hm] at hodd
  exact (Nat.odd_mul.mp hodd).2

theorem pairOddCore_subgroupOf_normal [Finite G] (H : Subgroup G) (beta : rightCosetSpace H) :
    ((pairOddCore H beta).subgroupOf (pairPointStabilizer H beta)).Normal := by
  change (((CFSG.oddCore (pairPointStabilizer H beta)).map
    (pairPointStabilizer H beta).subtype).comap (pairPointStabilizer H beta).subtype).Normal
  rw [Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
  infer_instance

theorem torus_inverted_count [Finite G] {P : Type v} [Group P]
    (L E : Subgroup G) (K : Subgroup L) (hKc : K ≤ Subgroup.center L)
    (hKodd : Odd (Nat.card K)) (θ : L →* P) (hθker : ∀ l, θ l = 1 ↔ l ∈ K)
    (hθsurj : Function.Surjective θ) (T : Subgroup P) [IsCyclic T] (hTodd : Odd (Nat.card T))
    (hcrit : ∀ l : L, (l : G) ∈ E ↔ θ l ∈ T) {t : G} (htL : t ∈ L)
    (htE : t ∈ Subgroup.normalizer (E : Set G)) :
    ∃ _ : IsMulCommutative ↥(L ⊓ E), Odd (Nat.card ↥(L ⊓ E)) ∧
      Nat.card (invertedPart (L ⊓ E) t) =
        Nat.card {c : P // c ∈ T ∧ (θ ⟨t, htL⟩)⁻¹ * c * θ ⟨t, htL⟩ = c⁻¹} ∧
      K.map L.subtype ≤ L ⊓ E ∧ ((L ⊓ E).subgroupOf L).map θ = T ∧
      ∃ C : Subgroup G, (C : Set G) = invertedPart (L ⊓ E) t ∧ IsCyclic C := by
  classical
  obtain ⟨incl, hincl⟩ : ∃ incl : ↥(L ⊓ E) →* L, ∀ a, ((incl a : L) : G) = a :=
    ⟨Subgroup.inclusion inf_le_left, fun a => rfl⟩
  obtain ⟨ρA, hρA⟩ : ∃ ρA : ↥(L ⊓ E) →* P, ∀ a, ρA a = θ (incl a) :=
    ⟨θ.comp incl, fun a => rfl⟩
  have hrange : ρA.range = T := by
    ext c
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      rw [hρA]
      exact (hcrit (incl a)).mp (by rw [hincl]; exact a.2.2)
    · intro hc
      obtain ⟨x, rfl⟩ := hθsurj c
      refine ⟨⟨x, x.2, (hcrit x).mpr hc⟩, ?_⟩
      rw [hρA, show incl ⟨x, x.2, (hcrit x).mpr hc⟩ = x from Subtype.ext (hincl _)]
  have hker : ∀ a, a ∈ ρA.ker ↔ incl a ∈ K := fun a => by
    rw [MonoidHom.mem_ker, hρA]
    exact hθker (incl a)
  have hcentral : ∀ a ∈ ρA.ker, ∀ l : L, l * incl a = incl a * l := fun a ha l =>
    Subgroup.mem_center_iff.mp (hKc ((hker a).mp ha)) l
  have hAcommI : IsMulCommutative ↥(L ⊓ E) := by
    have : IsCyclic ρA.range := by
      rw [hrange]
      infer_instance
    refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center ρA.rangeRestrict ?_
    intro a ha
    rw [MonoidHom.ker_rangeRestrict] at ha
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    have := congrArg Subtype.val (hcentral a ha (incl b))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hincl, hincl] at this
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact this
  have hAcomm : ∀ a b : ↥(L ⊓ E), a * b = b * a := fun a b => hAcommI.is_comm.comm a b
  have hkerodd : Odd (Nat.card ρA.ker) := by
    let j : ρA.ker →* K := (incl.comp ρA.ker.subtype).codRestrict K fun x => (hker x.1).mp x.2
    have hj : Function.Injective j := by
      intro x y hxy
      have h1 : ((incl x.1 : L) : G) = ((incl y.1 : L) : G) :=
        congrArg (fun c : K => ((c : L) : G)) hxy
      rw [hincl, hincl] at h1
      exact Subtype.ext (Subtype.ext h1)
    exact Odd.of_dvd_nat hKodd (Subgroup.card_dvd_of_injective j hj)
  have hAodd : Odd (Nat.card ↥(L ⊓ E)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρA.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρA).toEquiv, hrange]
    exact hTodd.mul hkerodd
  have hσmem : ∀ a : ↥(L ⊓ E), t⁻¹ * (a : G) * t ∈ L ⊓ E := by
    intro a
    refine ⟨L.mul_mem (L.mul_mem (L.inv_mem htL) a.2.1) htL, ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htE) a).mp a.2.2
    rwa [inv_inv] at this
  let σ : ↥(L ⊓ E) →* ↥(L ⊓ E) :=
    { toFun := fun a => ⟨t⁻¹ * a * t, hσmem a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change t⁻¹ * ((a : G) * b) * t = (t⁻¹ * a * t) * (t⁻¹ * b * t)
        group) }
  have hσ : ∀ a : ↥(L ⊓ E), ((σ a : ↥(L ⊓ E)) : G) = t⁻¹ * a * t := fun a => rfl
  have hcard1 : Nat.card (invertedPart (L ⊓ E) t) = Nat.card {a : ↥(L ⊓ E) // σ a = a⁻¹} :=
    Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
        invFun := fun a => ⟨a.1.1, a.1.2, congrArg Subtype.val a.2⟩
        left_inv := fun x => rfl
        right_inv := fun a => rfl }
  have hcommρ : ∀ a, ρA (σ a) = (θ ⟨t, htL⟩)⁻¹ * ρA a * θ ⟨t, htL⟩ := by
    intro a
    have : incl (σ a) = (⟨t, htL⟩ : L)⁻¹ * incl a * ⟨t, htL⟩ := Subtype.ext (by
      simp only [hincl, hσ, Subgroup.coe_mul, Subgroup.coe_inv])
    rw [hρA, hρA, this, map_mul, map_mul, map_inv]
  have hfixσ : ∀ r ∈ ρA.ker, σ r = r := by
    intro r hr
    apply Subtype.ext
    rw [hσ]
    have h1 : t * (r : G) = (r : G) * t := by
      have := congrArg Subtype.val (hcentral r hr ⟨t, htL⟩)
      rwa [Subgroup.coe_mul, Subgroup.coe_mul, hincl] at this
    rw [mul_assoc, ← h1, ← mul_assoc, inv_mul_cancel, one_mul]
  have hKA : K.map L.subtype ≤ L ⊓ E := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨k.2, (hcrit k).mpr ?_⟩
    rw [(hθker k).mpr hk]
    exact T.one_mem
  have himage : ((L ⊓ E).subgroupOf L).map θ = T := by
    ext c
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact (hcrit l).mp (Subgroup.mem_subgroupOf.mp hl).2
    · intro hc
      obtain ⟨x, rfl⟩ := hθsurj c
      exact ⟨x, Subgroup.mem_subgroupOf.mpr ⟨x.2, (hcrit x).mpr hc⟩, rfl⟩
  have hcyc : ∃ C : Subgroup G, (C : Set G) = invertedPart (L ⊓ E) t ∧ IsCyclic C := by
    refine ⟨invertedSubgroup (L ⊓ E) t, rfl, ?_⟩
    have hle : invertedSubgroup (L ⊓ E) t ≤ L ⊓ E := fun x hx => hx.1
    let j : ↥(invertedSubgroup (L ⊓ E) t) →* ↥T :=
      (ρA.comp (Subgroup.inclusion hle)).codRestrict T fun x => by
        rw [← hrange]
        exact ⟨_, rfl⟩
    refine isCyclic_of_injective j fun x y hxy => ?_
    have hρxy : ρA (Subgroup.inclusion hle x * (Subgroup.inclusion hle y)⁻¹) = 1 := by
      have h1 := congrArg Subtype.val hxy
      change ρA (Subgroup.inclusion hle x) = ρA (Subgroup.inclusion hle y) at h1
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have hr : Subgroup.inclusion hle x * (Subgroup.inclusion hle y)⁻¹ ∈ ρA.ker := hρxy
    have hx : t⁻¹ * (x : G) * t = (x : G)⁻¹ := x.2.2
    have hy : t⁻¹ * (y : G) * t = (y : G)⁻¹ := y.2.2
    have hσr := congrArg Subtype.val (hfixσ _ hr)
    rw [hσ] at hσr
    change t⁻¹ * ((x : G) * (y : G)⁻¹) * t = (x : G) * (y : G)⁻¹ at hσr
    have hxy' : (x : G) * y = y * x := congrArg Subtype.val
      (hAcomm (Subgroup.inclusion hle x) (Subgroup.inclusion hle y))
    have hsq : (x : G) * (y : G)⁻¹ * ((x : G) * (y : G)⁻¹) = 1 := by
      have h2 : t⁻¹ * ((x : G) * (y : G)⁻¹) * t = (x : G)⁻¹ * y := by
        calc t⁻¹ * ((x : G) * (y : G)⁻¹) * t = (t⁻¹ * x * t) * (t⁻¹ * y * t)⁻¹ := by group
          _ = (x : G)⁻¹ * y := by rw [hx, hy, inv_inv]
      rw [hσr] at h2
      calc (x : G) * (y : G)⁻¹ * ((x : G) * (y : G)⁻¹)
          = (x : G) * (y : G)⁻¹ * ((x : G)⁻¹ * y) := by rw [h2]
        _ = 1 := by
          have : (y : G)⁻¹ * (x : G)⁻¹ = (x : G)⁻¹ * (y : G)⁻¹ := by
            rw [← mul_inv_rev, ← mul_inv_rev, hxy']
          calc (x : G) * (y : G)⁻¹ * ((x : G)⁻¹ * y)
              = (x : G) * ((y : G)⁻¹ * (x : G)⁻¹) * y := by group
            _ = 1 := by rw [this]; group
    have h1 := eq_one_of_mul_self_eq_one_of_odd_card ρA.ker hkerodd hr (Subtype.ext (by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion,
        OneMemClass.coe_one] using hsq))
    exact Subtype.ext (by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion,
        OneMemClass.coe_one, mul_inv_eq_one] using congrArg Subtype.val h1)
  refine ⟨hAcommI, hAodd, ?_, hKA, himage, hcyc⟩
  rw [hcard1, card_inverted_eq_of_odd_kernel hAcomm σ ρA _ hcommρ hkerodd hfixσ, hrange]

theorem unitary_pair_centralizer_numerator_is_q_minus_one
    [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : twoRank (pairPointStabilizer H beta) = 1)
    {w : G} (hwB : w ∈ pairPointStabilizer H beta) (hw : orderOf w = 2) (hwz : Commute w z)
    (hwt : Commute w t)
    (hdeg : Nat.card (elementFixedSet H w) =
      Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 3 + 1) :
    (∃ f : ℕ, 2 ≤ f ∧ Nat.card ({1} ∪ distinguishedRoots H z w : Set G) = 2 ^ f) ∧
    ∃ _ : IsMulCommutative ↥(localInvolutionPointHull z w ⊓ pairPointStabilizer H beta),
      Odd (Nat.card ↥(localInvolutionPointHull z w ⊓ pairPointStabilizer H beta)) ∧
      (CFSG.oddCore (localInvolutionPointHull z w)).map (localInvolutionPointHull z w).subtype ≤
        localInvolutionPointHull z w ⊓ pairPointStabilizer H beta ∧
      IsCyclic (((localInvolutionPointHull z w ⊓ pairPointStabilizer H beta).subgroupOf
        (localInvolutionPointHull z w)).map (QuotientGroup.mk' (CFSG.oddCore _))) ∧
      Nat.card (((localInvolutionPointHull z w ⊓ pairPointStabilizer H beta).subgroupOf
        (localInvolutionPointHull z w)).map (QuotientGroup.mk' (CFSG.oddCore _))) =
        (Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 2 - 1) /
          Nat.gcd 3 (Nat.card ({1} ∪ distinguishedRoots H z w : Set G) + 1) ∧
      invertedSubgroup (localInvolutionPointHull z w ⊓ pairPointStabilizer H beta) t ≤
        pairOddCore H beta ∧
      IsCyclic (invertedSubgroup (localInvolutionPointHull z w ⊓ pairPointStabilizer H beta) t) ∧
      Nat.card (invertedSubgroup (localInvolutionPointHull z w ⊓ pairPointStabilizer H beta) t) =
        Nat.card ({1} ∪ distinguishedRoots H z w : Set G) - 1 ∧
      ⁅pairOddCore H beta ⊓ Subgroup.centralizer ({w} : Set G), Subgroup.zpowers t⁆ =
        invertedSubgroup (localInvolutionPointHull z w ⊓ pairPointStabilizer H beta) t ∧
      ((pairPointStabilizer H beta ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) : Set G) =
        ((pairPointStabilizer H beta ⊓ Subgroup.centralizer
            ((Subgroup.zpowers w ⊔ Subgroup.zpowers t : Subgroup G) : Set G) : Subgroup G) :
          Set G) * invertedPart (localInvolutionPointHull z w ⊓ pairPointStabilizer H beta) t ∧
      ((pairPointStabilizer H beta ⊓ Subgroup.centralizer
            ((Subgroup.zpowers w ⊔ Subgroup.zpowers t : Subgroup G) : Set G) : Subgroup G) :
          Set G) ∩ invertedPart (localInvolutionPointHull z w ⊓ pairPointStabilizer H beta) t =
        {1} ∧
      (pairPointStabilizer H beta ⊓ Subgroup.centralizer
          ((Subgroup.zpowers w ⊔ Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
        (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({w} : Set G)) =
        Nat.card ({1} ∪ distinguishedRoots H z w : Set G) - 1 := by
  classical
  have htclass : t ∈ involutionPointClass z := ht.1
  have hflip : pointRightCosetMul H (rightCosetMk H 1) t = beta := by
    rw [LocalCriterionInvariantNormalizer.pointRightCosetMul_eq_translate]
    exact ht.2
  have hesc := LocalCriterionNumerator.original_pair_centralizer_escapes H beta hbeta w t hwt
    hflip
  obtain ⟨ht2, htL, hLC, hLnormal, -⟩ :=
    LocalCriterionNumerator.original_pair_local_hull_inputs h.local_datum beta hbeta w t hw hwz
      hwt htclass hflip
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) := inferInstance
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) := inferInstance
  obtain ⟨-, -, -, hRcenter, hRodd, U, hU, -, hU4, -, -, hmodel, -⟩ :=
    RankOnePair.rank_one_pair_centralizer_model_and_two_global_involution_classes h
      (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G) beta hbeta hrank hwB hw
      hwz hesc R T₁
  have hUcard : Nat.card U = Nat.card ({1} ∪ distinguishedRoots H z w : Set G) := by
    have hset : (U : Set G) = {1} ∪ distinguishedRoots H z w := by
      rw [hU]
      ext x
      simp only [distinguishedRoots, Set.mem_union, Set.mem_inter_iff]
      tauto
    rw [← hset]
    rfl
  rw [← hUcard] at hdeg
  have hlt2 : Nat.card U ^ 2 < Nat.card U ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hlt1 : Nat.card U < Nat.card U ^ 2 := by
    calc Nat.card U = Nat.card U ^ 1 := (pow_one _).symm
      _ < Nat.card U ^ 2 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  rcases hmodel with ⟨hΓ, -⟩ | ⟨hΓ, -⟩ |
      ⟨-, f, hf, hUf, k, _, _, J, hJ, hk, hfixk, ρ, hρ, e, ψ, hψα, hψ⟩
  · omega
  · omega
  obtain ⟨-, -, -, -, -, rho3, -, hrho3, -, -, hstabα, hstabβ, -, -, hUTB, hTeq, hTcyc, hTcard,
    -, -, hreg, -, -, -, -, -, hswapC⟩ :=
    UnitaryModel.unitary_three_point_structure J f hf (by rw [hk, hUf]) (by rw [hfixk, hUf]) hJ
  have hρeq : rho3 = ρ :=
    MonoidHom.ext fun g => Equiv.ext fun p => Subtype.ext (by rw [hrho3, hρ])
  subst rho3
  obtain ⟨α₀, hα₀⟩ : ∃ p, p = unitaryOuterIsotropicPoint J hJ 0 (by decide) := ⟨_, rfl⟩
  obtain ⟨β₀, hβ₀⟩ : ∃ p, p = unitaryOuterIsotropicPoint J hJ 2 (by decide) := ⟨_, rfl⟩
  have hαβ : β₀ ≠ α₀ := by
    rw [hα₀, hβ₀]
    intro heq
    have h1 := congrArg Subtype.val heq
    simp only [unitaryOuterIsotropicPoint, unitaryCoordinatePoint] at h1
    rw [Projectivization.mk_eq_mk_iff] at h1
    obtain ⟨a, ha⟩ := h1
    have := congrFun ha 2
    simp at this
  rw [← hα₀] at hψα hstabα hreg hswapC
  rw [← hβ₀] at hstabβ hswapC
  let := hullFixedSetAction H z w
  have hwα : rightCosetMk H 1 ∈ elementFixedSet H w :=
    (mem_rightCosetStabilizer_iff_pointRightCosetMul H _ w).mp hwB.1
  have hwβ : beta ∈ elementFixedSet H w :=
    (mem_rightCosetStabilizer_iff_pointRightCosetMul H _ w).mp hwB.2
  obtain ⟨γα, hγα⟩ : ∃ γ : elementFixedSet H w, (γ : pointRightCosetSpace H) = rightCosetMk H 1 :=
    ⟨⟨_, hwα⟩, rfl⟩
  obtain ⟨γβ, hγβ⟩ : ∃ γ : elementFixedSet H w, (γ : pointRightCosetSpace H) = beta :=
    ⟨⟨_, hwβ⟩, rfl⟩
  have hγne : γβ ≠ γα := fun h' => hbeta (by rw [← hγβ, ← hγα, h'])
  have hψγα : ψ γα = α₀ := hψα γα hγα
  have hψβne : ψ γβ ≠ α₀ := by
    rw [← hψγα]
    exact fun h' => hγne (ψ.injective h')
  obtain ⟨⟨v, hvU⟩, hv, -⟩ := hreg (ψ γβ) β₀ hψβne hαβ
  have hvB : v ∈ unitaryCoordinateStabilizer J 0 := by
    rw [← hUTB]
    exact Subgroup.mem_sup_left hvU
  have hvα : ρ v α₀ = α₀ := by
    rw [← hstabα] at hvB
    exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_comap.mp hvB)
  obtain ⟨ψ', hψ'def⟩ : ∃ ψ' : elementFixedSet H w ≃ unitaryIsotropicPoints J,
      ∀ γ, ψ' γ = ρ v (ψ γ) := ⟨ψ.trans (ρ v), fun γ => rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : localInvolutionPointHull z w →* ProjectiveSpecialUnitaryMatrixGroup J,
      ∀ l, θ l = v * e (QuotientGroup.mk' (CFSG.oddCore (localInvolutionPointHull z w)) l) * v⁻¹ :=
    ⟨(MulAut.conj v).toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' _)), fun l => rfl⟩
  have hψ' : ∀ (l : localInvolutionPointHull z w) (γ : elementFixedSet H w),
      ψ' (l • γ) = ρ (θ l) (ψ' γ) := by
    intro l γ
    simp only [hψ'def, hψ l γ, hθ, map_mul, map_inv, Equiv.Perm.mul_apply,
      Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  have hψ'α : ψ' γα = α₀ := by rw [hψ'def, hψγα, hvα]
  have hψ'β : ψ' γβ = β₀ := by rw [hψ'def]; exact hv
  have hfixL : ∀ (l : localInvolutionPointHull z w) (γ : elementFixedSet H w),
      l • γ = γ ↔ pointRightCosetMul H γ (l : G) = γ := by
    intro l γ
    rw [← pointRightCosetMul_inv_eq_self_iff]
    exact ⟨fun h' => congrArg Subtype.val h', fun h' => Subtype.ext h'⟩
  have hcrit : ∀ l : localInvolutionPointHull z w,
      (l : G) ∈ pairPointStabilizer H beta ↔ θ l ∈ (torusPSU J hJ).range := by
    intro l
    have hE : (l : G) ∈ pairPointStabilizer H beta ↔ l • γα = γα ∧ l • γβ = γβ := by
      rw [hfixL, hfixL, hγα, hγβ, pairPointStabilizer, Subgroup.mem_inf,
        mem_rightCosetStabilizer_iff_pointRightCosetMul,
        mem_rightCosetStabilizer_iff_pointRightCosetMul]
    rw [hE, hTeq, Subgroup.mem_inf, ← hstabα, ← hstabβ, Subgroup.mem_comap, Subgroup.mem_comap,
      MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def,
      Equiv.Perm.smul_def, ← hψ'α, ← hψ'β, ← hψ', ← hψ', ψ'.injective.eq_iff,
      ψ'.injective.eq_iff]
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  obtain ⟨tL, htLval⟩ : ∃ x : localInvolutionPointHull z w, (x : G) = t := ⟨⟨t, htL⟩, rfl⟩
  have hflipα : tL • γα = γβ := by
    apply Subtype.ext
    change pointRightCosetMul H (γα : pointRightCosetSpace H) (tL : G)⁻¹ = γβ
    rw [htLval, htinv, hγα, hγβ, hflip]
  have hflipβ : tL • γβ = γα := by
    apply Subtype.ext
    change pointRightCosetMul H (γβ : pointRightCosetSpace H) (tL : G)⁻¹ = γα
    rw [htLval, hγβ, hγα, ← hflip, pointRightCosetMul_mul, mul_inv_cancel,
      pointRightCosetMul_one]
  have hθtα : ρ (θ tL) α₀ = β₀ := by rw [← hψ'α, ← hψ', hflipα, hψ'β]
  have hθtβ : ρ (θ tL) β₀ = α₀ := by rw [← hψ'β, ← hψ', hflipβ, hψ'α]
  obtain ⟨-, C, hCset, -, hCcard⟩ := hswapC (θ tL) hθtα hθtβ
  have htLeq : tL = ⟨t, htL⟩ := Subtype.ext htLval
  subst htLeq
  have hθker : ∀ l, θ l = 1 ↔ l ∈ CFSG.oddCore (localInvolutionPointHull z w) := by
    intro l
    rw [hθ, mul_inv_eq_one, mul_eq_left, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hθsurj : Function.Surjective θ := by
    intro c
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective _ (e.symm (v⁻¹ * c * v))
    exact ⟨x, by rw [hθ, hx, MulEquiv.apply_symm_apply]; group⟩
  have hTodd : Odd (Nat.card (torusPSU J hJ).range) := by
    rw [hTcard]
    exact odd_torus_card (by omega)
  have htE := flip_mem_normalizer_pairPointStabilizer h.local_datum.distinguished_order hbeta ht
  obtain ⟨hAc, hAodd, hcount, hKA, himage, C', hC'set, hC'cyc⟩ :=
    torus_inverted_count (localInvolutionPointHull z w) (pairPointStabilizer H beta) _ hRcenter
      hRodd θ hθker hθsurj _ hTodd hcrit htL htE
  obtain ⟨S, hzS, hzc⟩ := h.central_sylow
  obtain ⟨h1, h2, h3, h4, h5, hidx, -⟩ :=
    odd_pair_torus_controls_common_involution_centralizer_index _ ht2 htE _
      (pairOddCore_le H beta t).1 (pairOddCore_subgroupOf_normal H beta) (pairOddCore_odd H beta)
      (commutator_pairPointStabilizer_le h.local_datum S hzS hzc hbeta ht) hwB hw hwt _ hLC
      hLnormal htL hAodd
  have hinv : Nat.card (invertedPart (localInvolutionPointHull z w ⊓ pairPointStabilizer H beta) t)
      = 2 ^ f - 1 := by
    rw [hcount, ← hCcard]
    change _ = Nat.card ↑(C : Set (ProjectiveSpecialUnitaryMatrixGroup J))
    rw [hCset]
    rfl
  have hq : Nat.card ({1} ∪ distinguishedRoots H z w : Set G) = 2 ^ f := hUcard ▸ hUf
  let φ : localInvolutionPointHull z w ⧸ CFSG.oddCore (localInvolutionPointHull z w) →*
      ProjectiveSpecialUnitaryMatrixGroup J := (MulAut.conj v).toMonoidHom.comp e.toMonoidHom
  have hφ : Function.Injective φ := fun x y hxy => e.injective ((MulAut.conj v).injective hxy)
  have hθφ : θ = φ.comp (QuotientGroup.mk' _) := MonoidHom.ext fun l => hθ l
  set Abar := ((localInvolutionPointHull z w ⊓ pairPointStabilizer H beta).subgroupOf
    (localInvolutionPointHull z w)).map (QuotientGroup.mk' (CFSG.oddCore _)) with hAbar
  have hAbarT : Abar.map φ = (torusPSU J hJ).range := by
    rw [hAbar, Subgroup.map_map, ← hθφ, himage]
  let eA : Abar ≃* (torusPSU J hJ).range :=
    (Subgroup.equivMapOfInjective Abar φ hφ).trans (MulEquiv.subgroupCongr hAbarT)
  have hinvset : ((invertedSubgroup (localInvolutionPointHull z w ⊓ pairPointStabilizer H beta)
      t : Subgroup G) : Set G) = ((⁅localInvolutionPointHull z w ⊓ pairPointStabilizer H beta,
        Subgroup.zpowers t⁆ : Subgroup G) : Set G) := h1
  have hinveq : invertedSubgroup (localInvolutionPointHull z w ⊓ pairPointStabilizer H beta) t =
      ⁅pairOddCore H beta ⊓ Subgroup.centralizer {w}, Subgroup.zpowers t⁆ := by
    rw [← h2]
    exact SetLike.coe_injective hinvset
  have hC'eq : C' = invertedSubgroup (localInvolutionPointHull z w ⊓ pairPointStabilizer H beta)
      t := SetLike.coe_injective hC'set
  refine ⟨⟨f, hf, hq⟩, hAc, hAodd, hKA, isCyclic_of_injective eA.toMonoidHom eA.injective, ?_,
    ?_, hC'eq ▸ hC'cyc, ?_, hinveq.symm, ?_, ?_, ?_⟩
  · rw [Nat.card_congr eA.toEquiv, hTcard, hq]
  · rw [hinveq]
    exact h3
  · rw [hq, ← hinv]
    rfl
  · rw [centralizer_zpowers_sup_zpowers, ← inf_assoc]
    exact h4
  · rw [centralizer_zpowers_sup_zpowers, ← inf_assoc]
    exact h5
  · rw [centralizer_zpowers_sup_zpowers, ← inf_assoc, hidx, hinv, hq]


theorem unitary_pair_centralizer_numerator_of_trivial_odd_core
    [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : twoRank (pairPointStabilizer H beta) = 1)
    {w : G} (hwB : w ∈ pairPointStabilizer H beta) (hw : orderOf w = 2) (hwz : Commute w z)
    (hwt : Commute w t)
    (hdeg : Nat.card (elementFixedSet H w) =
      Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 3 + 1)
    (hodd : CFSG.oddCore (localInvolutionPointHull z w) = ⊥) :
    IsCyclic ↥(localInvolutionPointHull z w ⊓ pairPointStabilizer H beta) ∧
      Nat.card ↥(localInvolutionPointHull z w ⊓ pairPointStabilizer H beta) =
        (Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 2 - 1) /
          Nat.gcd 3 (Nat.card ({1} ∪ distinguishedRoots H z w : Set G) + 1) := by
  obtain ⟨-, -, -, -, hcyc, hcard, -⟩ :=
    unitary_pair_centralizer_numerator_is_q_minus_one h hbeta ht hrank hwB hw hwz hwt hdeg
  have hinj : Function.Injective
      (QuotientGroup.mk' (CFSG.oddCore (localInvolutionPointHull z w))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hodd]
  let eA : ↥(localInvolutionPointHull z w ⊓ pairPointStabilizer H beta) ≃*
      ↥(((localInvolutionPointHull z w ⊓ pairPointStabilizer H beta).subgroupOf
        (localInvolutionPointHull z w)).map (QuotientGroup.mk' (CFSG.oddCore _))) :=
    (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans
      (Subgroup.equivMapOfInjective _ _ hinj)
  exact ⟨isCyclic_of_injective eA.toMonoidHom eA.injective,
    (Nat.card_congr eA.toEquiv).trans hcard⟩

theorem unitaryNumeratorTheorem
    (G : Type u) [Group G] [Finite G] :
    UnitaryNumeratorTheorem G := by
  intro H z h beta hbeta t ht hrank w hwB hw hwz hwt hdeg
  obtain ⟨hq, _, -, -, -, -, -, -, -, -, -, -, hidx⟩ :=
    unitary_pair_centralizer_numerator_is_q_minus_one h hbeta ht hrank hwB hw hwz hwt hdeg
  exact ⟨hq, hidx⟩

end Main
end CFSG.ProperTwoGeneratedCore.HighRankPair
