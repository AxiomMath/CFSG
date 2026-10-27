module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {H : Type*} [Group H]

structure Hyp46 (B T X : Subgroup H) : Prop where
  elem : IsElemAbelian 2 T
  four_le : 4 ≤ Nat.card T
  le_normalizer : T ≤ normalizer (B : Set H)
  faithful : T ⊓ centralizer (B : Set H) = ⊥
  le_sup : X ≤ T ⊔ B
  sylow : IsSylowOf 2 T X
  twoNilpotent : IsTwoNilpotent X
  tight : TightlyEmbedded (X.subgroupOf (T ⊔ B))

variable {B T X : Subgroup H}

theorem Hyp46.exists_of (hT : NoncyclicFaithful T B) (hK : SylowInTightTwoNilpotent T B) :
    ∃ X, Hyp46 B T X := by
  obtain ⟨hel, h4, hN, hC⟩ := hT
  obtain ⟨X, hX, hTX, hnil, htight⟩ := hK
  exact ⟨X, hel, h4, hN, hC, hX, hTX, hnil, htight⟩

theorem mem_normalizer_of_mem_normalizer_subgroupOf {X M : Subgroup H} (hXM : X ≤ M) {y : M}
    (hy : y ∈ normalizer ((X.subgroupOf M : Subgroup M) : Set M)) :
    (y : H) ∈ normalizer (X : Set H) := by
  rw [mem_normalizer_iff] at hy ⊢
  intro g
  constructor
  · intro hg
    have h1 := (hy ⟨g, hXM hg⟩).mp (mem_subgroupOf.mpr hg)
    simpa [mem_subgroupOf] using h1
  · intro hg
    have hgM : g ∈ M := by
      have h2 : (y : H) * g * (y : H)⁻¹ ∈ M := hXM hg
      have h3 := M.mul_mem (M.mul_mem (M.inv_mem y.2) h2) y.2
      simpa [mul_assoc] using h3
    have h4 := (hy ⟨g, hgM⟩).mpr (by simpa [mem_subgroupOf] using hg)
    simpa [mem_subgroupOf] using h4

theorem Hyp46.le_X (h : Hyp46 B T X) : T ≤ X := h.sylow.le

theorem Hyp46.even_card [Finite H] (h : Hyp46 B T X) : Even (Nat.card T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h.sylow.isPGroup
  have h4 := h.four_le
  rw [hn] at h4 ⊢
  rcases n with _ | n
  · norm_num at h4
  · exact Nat.even_pow.mpr ⟨even_two, n.succ_ne_zero⟩

theorem Hyp46.exists_ne [Finite H] (h : Hyp46 B T X) {s : H} (hs : s ∈ T) :
    ∃ t ∈ T, t ≠ 1 ∧ t ≠ s := by
  by_contra hcon
  push Not at hcon
  have hle : T ≤ zpowers s := fun t ht => by
    by_cases ht1 : t = 1
    · rw [ht1]; exact one_mem _
    · rw [hcon t ht ht1]; exact mem_zpowers s
  have h1 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at h1
  have h2 : orderOf s ≤ 2 := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (h.elem.2 s hs))
  have := h.four_le
  omega

theorem Hyp46.mem_normalizer_of_mem [Finite H] (h : Hyp46 B T X) {y : H} (hy : y ∈ T ⊔ B)
    {x : H} (hxX : x ∈ X) (hxy : y * x * y⁻¹ ∈ X) (hx1 : x ≠ 1) (k : ℕ) (hxk : x ^ (2 ^ k) = 1) :
    y ∈ normalizer (X : Set H) := by
  by_contra hyN
  set M := T ⊔ B
  set y' : M := ⟨y, hy⟩
  have hy'N : y' ∉ normalizer ((X.subgroupOf M : Subgroup M) : Set M) := fun hN =>
    hyN (mem_normalizer_of_mem_normalizer_subgroupOf h.le_sup hN)
  have hodd := h.tight.2 y' hy'N
  set x' : M := ⟨x, h.le_sup hxX⟩
  have hmem : x' ∈ X.subgroupOf M ⊓ rightConjugate (X.subgroupOf M) y' :=
    Subgroup.mem_inf.mpr ⟨mem_subgroupOf.mpr hxX,
      (mem_rightConjugate_iff _ _ _).mpr (mem_subgroupOf.mpr hxy)⟩
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  have hx'k : x' ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hxk)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx'k)
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hx1
    have : orderOf x' = 1 := by simpa using hm
    have := orderOf_eq_one_iff.mp this
    simpa [x'] using congrArg Subtype.val this
  have h2 : 2 ∣ orderOf x' := by
    rw [hm]
    exact dvd_pow_self 2 hm0
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd))

theorem Hyp46.inf_centralizer_le [Finite H] (h : Hyp46 B T X) {x : H} (hxX : x ∈ X) (hx1 : x ≠ 1)
    (k : ℕ) (hxk : x ^ (2 ^ k) = 1) :
    (T ⊔ B) ⊓ centralizer ({x} : Set H) ≤ normalizer (X : Set H) := by
  intro y hy
  obtain ⟨hy, hyc⟩ := Subgroup.mem_inf.mp hy
  have hyx : y * x * y⁻¹ = x := by
    rw [mem_centralizer_singleton_iff] at hyc
    rw [hyc, mul_inv_cancel_right]
  exact h.mem_normalizer_of_mem hy hxX (by rw [hyx]; exact hxX) hx1 k hxk

theorem Hyp46.inf_centralizer_le_of_mem [Finite H] (h : Hyp46 B T X) {t : H} (ht : t ∈ T)
    (ht1 : t ≠ 1) : (T ⊔ B) ⊓ centralizer ({t} : Set H) ≤ normalizer (X : Set H) :=
  h.inf_centralizer_le (h.le_X ht) ht1 1 (by simpa using h.elem.2 t ht)

theorem Hyp46.sq_eq_one [Finite H] (h : Hyp46 B T X) {x : H} (hx : x ∈ X) (k : ℕ)
    (hxk : x ^ 2 ^ k = 1) : x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := h.sylow.exists_sylow_eq_subgroupOf
  set x' : X := ⟨x, hx⟩
  have hx'k : x' ^ 2 ^ k = 1 := Subtype.ext (by simpa using hxk)
  have hP : IsPGroup 2 (zpowers x') := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx'k)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S₀ S
  have hxS : x' ∈ (S : Subgroup X) := hS (mem_zpowers x')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hS₀,
    mem_subgroupOf] at hxS
  have h2 := h.elem.2 _ hxS
  have : (g⁻¹ * x' * g) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [MulAut.inv_def, MulAut.conj_symm_apply] using h2
  have h3 : x' ^ 2 = 1 := by
    have e : (g⁻¹ * x' * g) ^ 2 = g⁻¹ * x' ^ 2 * g := by rw [sq, sq]; group
    rw [e] at this
    calc x' ^ 2 = g * (g⁻¹ * x' ^ 2 * g) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  simpa [x'] using congrArg Subtype.val h3

theorem Hyp46.restrict [Finite H] (h : Hyp46 B T X) {B' : Subgroup H} (hB' : B' ≤ B)
    (hTB' : T ≤ normalizer (B' : Set H)) (hfaith : T ⊓ centralizer (B' : Set H) = ⊥) :
    Hyp46 B' T (X ⊓ (T ⊔ B')) := by
  have hTX : T ≤ X ⊓ (T ⊔ B') := le_inf h.le_X le_sup_left
  have heven : Even (Nat.card (X ⊓ (T ⊔ B') : Subgroup H)) :=
    even_iff_two_dvd.mpr ((even_iff_two_dvd.mp h.even_card).trans (card_dvd_of_le hTX))
  exact ⟨h.elem, h.four_le, hTB', hfaith, inf_le_right, h.sylow.of_le hTX inf_le_left,
    h.twoNilpotent.mono inf_le_left,
    tightlyEmbedded_inf_subgroupOf (sup_le_sup_left hB' T) h.tight heven⟩

theorem le_iSup_inf_centralizer_of_odd [Finite H] {T Q C : Subgroup H} (hT : IsElemAbelian 2 T)
    (h4 : 4 ≤ Nat.card T) (hodd : Odd (Nat.card Q)) (hTQ : T ≤ normalizer (Q : Set H))
    (hQC : Q ≤ C) :
    Q ≤ ⨆ t ∈ T, ⨆ (_ : t ≠ 1), C ⊓ centralizer ({t} : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsElementaryAbelian 2 T :=
    { toIsMulCommutative := hT.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (hT.2 g g.2) }
  let : MulDistribMulAction T Q := MulDistribMulAction.compHom Q (Subgroup.inclusion hTQ)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := T) (H := Q)
    (by simpa using h4) (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])
  have hle : (⨆ (a : T) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) Q) ≤
      (⨆ t ∈ T, ⨆ (_ : t ≠ 1), C ⊓ centralizer ({t} : Set H)).comap Q.subtype := by
    refine iSup₂_le fun a ha => fun x hx => ?_
    have hfix := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).1 hx
    have hc : (a : H) * x * (a : H)⁻¹ = x := congrArg Subtype.val hfix
    have ha1 : (a : H) ≠ 1 := fun h => ha (Subtype.ext h)
    refine Subgroup.mem_iSup_of_mem (a : H) (Subgroup.mem_iSup_of_mem a.2
      (Subgroup.mem_iSup_of_mem ha1 (Subgroup.mem_inf.2 ⟨hQC x.2, ?_⟩)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x : H) * a = (a : H) * x * (a : H)⁻¹ * a := by rw [hc]
      _ = a * x := by rw [inv_mul_cancel_right]
  intro q hq
  have hmem : (⟨q, hq⟩ : Q) ∈
      ⨆ (a : T) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) Q := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact hle hmem

theorem Hyp46.le_normalizer_of_odd [Finite H] (h : Hyp46 B T X) {Q : Subgroup H}
    (hQ : Q ≤ T ⊔ B) (hTQ : T ≤ normalizer (Q : Set H)) (hodd : Odd (Nat.card Q)) :
    Q ≤ normalizer (X : Set H) :=
  (le_iSup_inf_centralizer_of_odd h.elem h.four_le hodd hTQ hQ).trans
    (iSup₂_le fun _ ht => iSup_le fun ht1 => h.inf_centralizer_le_of_mem ht ht1)

theorem subsingleton_of_isSolvable_of_commutator_eq_top {G : Type*} [Group G] [Group.IsSolvable G]
    (h : commutator G = ⊤) : Subsingleton G := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := G)
  have : ∀ m, derivedSeries G m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [derivedSeries_succ, ih, ← commutator_def, h]
  rw [this n] at hn
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ (⊥ : Subgroup G) := hn ▸ Subgroup.mem_top x
  have hy : y ∈ (⊥ : Subgroup G) := hn ▸ Subgroup.mem_top y
  rw [Subgroup.mem_bot.mp hx, Subgroup.mem_bot.mp hy]

theorem not_isTwoNilpotent_of_isQuasisimple [Finite H] {B : Subgroup H} (hB : Open.IsQuasisimple B)
    (heven : Even (Nat.card B)) : ¬ IsTwoNilpotent B := by
  rintro ⟨O, hOB, hOn, hOodd, k, hk⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (B ⧸ O.subgroupOf B) := IsPGroup.of_card (n := k) (by
    rw [← Subgroup.index, ← hk, Subgroup.relIndex])
  have : Group.IsNilpotent (B ⧸ O.subgroupOf B) := hp.isNilpotent
  have hperf : commutator (B ⧸ O.subgroupOf B) = ⊤ := by
    have : Group.IsPerfect B := ⟨hB.1⟩
    exact (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (O.subgroupOf B))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  have hsub := subsingleton_of_isSolvable_of_commutator_eq_top hperf
  have htop : O.subgroupOf B = ⊤ := by
    rw [← QuotientGroup.ker_mk' (O.subgroupOf B), MonoidHom.ker_eq_top_iff]
    ext x
    exact Subsingleton.elim _ _
  have hBO : B ≤ O := by
    intro b hb
    have := htop ▸ (Subgroup.mem_top (⟨b, hb⟩ : B))
    exact mem_subgroupOf.mp this
  have : Odd (Nat.card B) := hOodd.of_dvd_nat (card_dvd_of_le hBO)
  exact (Nat.not_even_iff_odd.mpr this) heven

theorem Hyp46.false_of_le_normalizer [Finite H] (h : Hyp46 B T X) (hB : Open.IsQuasisimple B)
    (heven : Even (Nat.card B)) (hle : B ≤ normalizer (X : Set H)) : False := by
  have hY : ((B ⊓ X).subgroupOf B).Normal := by
    refine ⟨fun y hy b => ?_⟩
    rw [mem_subgroupOf] at hy ⊢
    obtain ⟨hyB, hyX⟩ := Subgroup.mem_inf.mp hy
    exact Subgroup.mem_inf.mpr ⟨B.mul_mem (B.mul_mem b.2 hyB) (B.inv_mem b.2),
      (mem_normalizer_iff.mp (hle b.2) y).mp hyX⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hB
      ((B ⊓ X).subgroupOf B) with hc | htop
  ·
    have hYC : B ⊓ X ≤ centralizer (B : Set H) := by
      intro y hy
      rw [mem_centralizer_iff]
      intro b hb
      have := hc (mem_subgroupOf.mpr (show ((⟨y, hy.1⟩ : B) : H) ∈ B ⊓ X from hy))
      rw [Subgroup.mem_center_iff] at this
      exact congrArg Subtype.val (this ⟨b, hb⟩)
    have hBT : ⁅B, T⁆ ≤ centralizer (B : Set H) := by
      refine (Subgroup.commutator_le.mpr fun b hb t ht => ?_).trans hYC
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have e : ⁅b, t⁆ = b * (t * b⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
        rw [e]
        exact B.mul_mem hb ((mem_normalizer_iff.mp (h.le_normalizer ht) _).mp (B.inv_mem hb))
      · rw [commutatorElement_def]
        exact X.mul_mem ((mem_normalizer_iff.mp (hle hb) t).mp (h.le_X ht))
          (X.inv_mem (h.le_X ht))
    have h1 : ⁅⁅B, T⁆, B⁆ = ⊥ :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hBT
    have h2 : ⁅⁅T, B⁆, B⁆ = ⊥ := by rwa [Subgroup.commutator_comm T B]
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    have hBB : ⁅B, B⁆ = B := by
      have := congrArg (Subgroup.map B.subtype) hB.1
      rwa [_root_.commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at this
    rw [hBB] at h3
    have hTC : T ≤ centralizer (B : Set H) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact h3
    have hT1 : T = ⊥ := by
      rw [← h.faithful]
      exact (inf_eq_left.mpr hTC).symm
    have := h.four_le
    rw [hT1, Subgroup.card_bot] at this
    omega
  ·
    have hBX : B ≤ X := by
      intro b hb
      have := htop ▸ (Subgroup.mem_top (⟨b, hb⟩ : B))
      exact (Subgroup.mem_inf.mp (mem_subgroupOf.mp this)).2
    exact not_isTwoNilpotent_of_isQuasisimple hB heven (h.twoNilpotent.mono hBX)

end CFSG.ComponentClassification.RankTwoOddLie
