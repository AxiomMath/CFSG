module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526D
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526F1
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Transport

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
  KFactsPair
open scoped commutatorElement

section SevenElement

theorem exists_sevenElement_centralizing_D_aux_fixed {X : Type} [Group X] [Finite X]
    {N : Subgroup X} [N.Normal] (hN : IsPGroup 2 N) {A Y : Subgroup X} (hA : IsPGroup 3 A)
    (hAY : A ≤ Y) {x : X} (hxY : x ∈ Y) (hcomm : ∀ a ∈ A, x⁻¹ * (a * x * a⁻¹) ∈ N) :
    ∃ y ∈ Y, x⁻¹ * y ∈ N ∧ ∀ a ∈ A, a * y = y * a := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Ω : Set X := {y | y ∈ Y ∧ x⁻¹ * y ∈ N}
  have hmem : ∀ (a : ↥A) (y : ↥Ω), (a : X) * (y : X) * (a : X)⁻¹ ∈ Ω := by
    rintro ⟨a, ha⟩ ⟨y, hyY, hyN⟩
    refine ⟨Y.mul_mem (Y.mul_mem (hAY ha) hyY) (Y.inv_mem (hAY ha)), ?_⟩
    have h1 := hcomm a ha
    have h2 : a * (x⁻¹ * y) * a⁻¹ ∈ N := Normal.conj_mem ‹N.Normal› _ hyN a
    have h3 : x⁻¹ * (a * y * a⁻¹) = (x⁻¹ * (a * x * a⁻¹)) * (a * (x⁻¹ * y) * a⁻¹) := by group
    show x⁻¹ * (a * y * a⁻¹) ∈ N
    rw [h3]
    exact N.mul_mem h1 h2
  letI : MulAction ↥A ↥Ω :=
    { smul := fun a y => ⟨(a : X) * y * (a : X)⁻¹, hmem a y⟩
      one_smul := fun y => Subtype.ext (by
        show ((1 : ↥A) : X) * (y : X) * ((1 : ↥A) : X)⁻¹ = y
        simp)
      mul_smul := fun a b y => Subtype.ext (by
        show ((a * b : ↥A) : X) * (y : X) * ((a * b : ↥A) : X)⁻¹ =
          (a : X) * ((b : X) * (y : X) * (b : X)⁻¹) * (a : X)⁻¹
        simp [mul_assoc]) }
  have hcard : Nat.card ↥Ω = Nat.card ↥(N ⊓ Y) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * (y : X), y.2.2, Y.mul_mem (Y.inv_mem hxY) y.2.1⟩
        invFun := fun n => ⟨x * (n : X), Y.mul_mem hxY n.2.2, by simpa using n.2.1⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
  have hnd : ¬ 3 ∣ Nat.card ↥Ω := by
    rw [hcard]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hN.to_le (inf_le_left : N ⊓ Y ≤ N))
    rw [hn]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  obtain ⟨y, hy⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card ↥Ω hnd
  refine ⟨(y : X), y.2.1, y.2.2, fun a ha => ?_⟩
  have h1 := (MulAction.mem_fixedPoints.1 hy) ⟨a, ha⟩
  have h2 : a * (y : X) * a⁻¹ = (y : X) := congrArg Subtype.val h1
  calc a * (y : X) = a * y * a⁻¹ * a := by group
    _ = y * a := by rw [h2]

theorem exists_sevenElement_centralizing_D_aux_sevenPart {X : Type} [Group X] {N : Subgroup X}
    [N.Normal] (hN : IsPGroup 2 N) {x y : X} (hx : orderOf x = 7) (hxy : x⁻¹ * y ∈ N) :
    ∃ k : ℕ, orderOf (y ^ k) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hπ : (QuotientGroup.mk' N) y = (QuotientGroup.mk' N) x :=
    ((QuotientGroup.eq (a := x) (b := y)).2 hxy).symm
  have hx7 : x ^ 7 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hπx1 : (QuotientGroup.mk' N) x ≠ 1 := by
    intro h1
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).1 h1
    obtain ⟨j, hj⟩ := hN ⟨x, hxN⟩
    have h2 : x ^ (2 ^ j) = 1 := congrArg Subtype.val hj
    have h3 : 7 ∣ 2 ^ j := hx ▸ orderOf_dvd_of_pow_eq_one h2
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow (by norm_num) h3)
    omega
  have hy7 : y ^ 7 ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' N) (y ^ 7) = 1
    rw [map_pow, hπ, ← map_pow, hx7, map_one]
  obtain ⟨j, hj⟩ := hN ⟨y ^ 7, hy7⟩
  have hj' : (y ^ 7) ^ (2 ^ j) = 1 := congrArg Subtype.val hj
  refine ⟨2 ^ j, orderOf_eq_prime ?_ ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]
    exact hj'
  · intro h1
    have h2 : (QuotientGroup.mk' N) x ^ (2 ^ j) = 1 := by
      rw [← hπ, ← map_pow, h1, map_one]
    have h3 : 7 ∣ 2 ^ j := by
      have := orderOf_dvd_of_pow_eq_one h2
      rwa [orderOf_eq_prime (by rw [← map_pow, hx7, map_one]) hπx1] at this
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow (by norm_num) h3)
    omega

theorem exists_sevenElement_centralizing_D_aux_outList {S : Type} [Group S]
    (h : IsLThreeOfExp 1 S) : IsOutTwoGroupList S := by
  rcases h with ⟨-, d, q, hq, hd, he⟩ | ⟨h, -⟩
  · exact Or.inr (Or.inr ⟨d, Or.inr (Or.inr ⟨q, hq, hd⟩), he⟩)
  · omega

theorem exists_sevenElement_centralizing_D_aux_kernel (hKOut : KOut) {X Y : Type} [Group X]
    [Group Y] [Finite Y] (f : X →* Y) {Is : Subgroup Y} (h3 : IsLThreeOfExp 1 ↥Is)
    {E : Subgroup X} (hE : CFSG.Open.IsElemAbelian 7 E) (hEcard : Nat.card ↥E = 7 ^ 2)
    (hEN : ∀ e ∈ E, f e ∈ Subgroup.normalizer (Is : Set Y)) :
    ∃ x ∈ E, x ≠ 1 ∧ f x ∈ Subgroup.centralizer (Is : Set Y) := by
  classical
  by_contra hcon
  push Not at hcon
  let ρ0 : ↥E →* ↥(Subgroup.normalizer (Is : Set Y)) :=
    (f.comp E.subtype).codRestrict (Subgroup.normalizer (Is : Set Y)) (fun e => hEN e e.2)
  let ρ : ↥E →* MulAut ↥Is := Is.normalizerMonoidHom.comp ρ0
  have hρ : ∀ (e : ↥E) (s : ↥Is), ((ρ e) s : Y) = f e * s * (f e)⁻¹ := fun e s =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Is (ρ0 e) s
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro e he
    by_contra hne
    have hne' : (e : X) ≠ 1 := fun h => hne (Subtype.ext h)
    refine hcon e e.2 hne' ?_
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := hρ e ⟨s, hs⟩
    rw [he] at h1
    have h2 : s = f e * s * (f e)⁻¹ := h1
    calc s * f e = (f e * s * (f e)⁻¹) * f e := by rw [← h2]
      _ = f e * s := by group
  have hrange : ∀ e : ↥E, ρ e ∈ (MulAut.conj : ↥Is →* MulAut ↥Is).range := by
    intro e
    have h7 : (ρ e) ^ 7 = 1 := by
      rw [← map_pow]
      have h8 : e ^ 7 = 1 := Subtype.ext (by simpa using hE.2 e e.2)
      rw [h8, map_one]
    obtain ⟨k, hk⟩ := hKOut ↥Is (exists_sevenElement_centralizing_D_aux_outList h3) (ρ e)
    have hcop : Nat.Coprime (2 ^ k) (orderOf (ρ e)) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h7)
        (Nat.Coprime.pow_left k (by norm_num))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Subgroup.pow_mem _ hk m
  let ρ' : ↥E →* ↥(MulAut.conj : ↥Is →* MulAut ↥Is).range := ρ.codRestrict _ hrange
  have hinj' : Function.Injective ρ' := fun a b h => hinj (congrArg Subtype.val h)
  have d1 : Nat.card ↥E ∣ Nat.card ↥(MulAut.conj : ↥Is →* MulAut ↥Is).range :=
    Subgroup.card_dvd_of_injective ρ' hinj'
  have d2 : Nat.card ↥(MulAut.conj : ↥Is →* MulAut ↥Is).range ∣ Nat.card ↥Is :=
    Subgroup.card_dvd_of_surjective
      (f := (MulAut.conj : ↥Is →* MulAut ↥Is).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  rw [hEcard] at d1
  rw [card_eq_of_isLThreeOfExp_one h3] at d2
  have h49 := d1.trans d2
  norm_num at h49

variable {X : Type} [Group X] [Finite X]

theorem exists_sevenElement_centralizing_D_aux_comm {L I Q A : Subgroup X} (hI : I ≤ cMHat L)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q I) (hAL : A ≤ L)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set X)) : ∀ a ∈ A, ∀ q ∈ Q, a * q = q * a := by
  intro a ha q hq
  have hc : QuotientGroup.mk' (CFSG.pCore 2 X) a * QuotientGroup.mk' (CFSG.pCore 2 X) q =
      QuotientGroup.mk' (CFSG.pCore 2 X) q * QuotientGroup.mk' (CFSG.pCore 2 X) a :=
    Subgroup.mem_centralizer_iff.1 (hI (hQ.le hq)) (QuotientGroup.mk' (CFSG.pCore 2 X) a)
      ⟨a, hAL ha, rfl⟩
  have hcQ : a * q * a⁻¹ * q⁻¹ ∈ Q :=
    Q.mul_mem ((Subgroup.mem_normalizer_iff.1 (hAQ ha) q).1 hq) (Q.inv_mem hq)
  have hc2 : a * q * a⁻¹ * q⁻¹ ∈ CFSG.pCore 2 X := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 X), MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hc]
    group
  obtain ⟨k, hk⟩ := hQ.isPGroup ⟨_, hcQ⟩
  obtain ⟨j, hj⟩ := pRank_barO2_eq_aux_powTwo hc2
  have hc3 : (a * q * a⁻¹ * q⁻¹) ^ (3 ^ k) = 1 := congrArg Subtype.val hk
  have hdvd1 := orderOf_dvd_of_pow_eq_one hc3
  have hdvd2 := orderOf_dvd_of_pow_eq_one hj
  have hcop : Nat.Coprime (3 ^ k) (2 ^ j) := Nat.Coprime.pow k j (by norm_num)
  have h1 : orderOf (a * q * a⁻¹ * q⁻¹) = 1 :=
    Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hdvd1 hdvd2)
  have h2 : a * q * a⁻¹ * q⁻¹ = 1 := orderOf_eq_one_iff.1 h1
  calc a * q = (a * q * a⁻¹ * q⁻¹) * (q * a) := by group
    _ = q * a := by rw [h2, one_mul]

theorem exists_sevenElement_centralizing_D_aux_main (hKOut : KOut) {L : Subgroup X}
    (hLn : L.Normal) (h3b : IsLThreeOfExp 1 ↥(barO2 L)) {I Q A : Subgroup X} (hI : I ≤ cMHat L)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q I) (hA : CFSG.ABGLocalTools.IsSylowOf 3 A L)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set X))
    (h2 : 2 ≤ CFSG.Open.pRank 7 (Subgroup.centralizer (Q : Set X))) :
    ∃ x : X, orderOf x = 7 ∧ (∀ y ∈ Q, x * y = y * x) ∧ ∀ a ∈ A, x * a = a * x := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨E, hEle, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 7) h2
  haveI : (barO2 L).Normal :=
    hLn.map (QuotientGroup.mk' (CFSG.pCore 2 X)) (QuotientGroup.mk'_surjective _)
  have hEN : ∀ e ∈ E, QuotientGroup.mk' (CFSG.pCore 2 X) e ∈
      Subgroup.normalizer ((barO2 L : Subgroup (X ⧸ CFSG.pCore 2 X)) : Set (X ⧸ CFSG.pCore 2 X)) := by
    intro e _
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  obtain ⟨x₀, hx₀E, hx₀1, hx₀c⟩ :=
    exists_sevenElement_centralizing_D_aux_kernel hKOut (QuotientGroup.mk' (CFSG.pCore 2 X))
      h3b hE hEcard hEN
  have hx₀7 : orderOf x₀ = 7 := orderOf_eq_prime (hE.2 x₀ hx₀E) hx₀1
  have hAQc := exists_sevenElement_centralizing_D_aux_comm hI hQ hA.le hAQ
  have hAY : A ≤ Subgroup.centralizer (Q : Set X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hAQc a ha q hq).symm
  obtain ⟨y, hyY, hyN, hyA⟩ := exists_sevenElement_centralizing_D_aux_fixed
    (N := CFSG.pCore 2 X) (CFSG.pCore_isPGroup (p := 2) (G := X)) hA.isPGroup hAY (hEle hx₀E)
    (by
      intro a ha
      have hc := Subgroup.mem_centralizer_iff.1 hx₀c (QuotientGroup.mk' (CFSG.pCore 2 X) a)
        ⟨a, hA.le ha, rfl⟩
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 X), MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hc]
      group)
  obtain ⟨k, hk⟩ := exists_sevenElement_centralizing_D_aux_sevenPart
    (CFSG.pCore_isPGroup (p := 2) (G := X)) hx₀7 hyN
  refine ⟨y ^ k, hk, fun q hq => ?_, fun a ha => ?_⟩
  · have hq' : Commute q y := Subgroup.mem_centralizer_iff.1 hyY q hq
    exact (hq'.pow_right k).eq.symm
  · have ha' : Commute a y := hyA a ha
    exact (ha'.pow_right k).eq.symm

theorem exists_sevenElement_centralizing_D_le_six (hKSML3 : KSML3) (hKOut : KOut)
    {T : Subgroup X}
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : IsComponentOf Ls ⊤)
    (hL : LiftOf T L Ls) (h3 : IsLThreeOfExp 1 ↥Ls) (h7X : CFSG.Open.pRank 7 (⊤ : Subgroup X) ≤ 6)
    (hLn : L.Normal) (hrank : 1 < CFSG.Open.pRank 7 (cMBar L)) {I Q A : Subgroup X}
    (hI : I ≤ cMHat L) (hIc : CFSG.IsPComponent 7 (I.subgroupOf (cMHat L)))
    (hI1 : CFSG.Open.pRank 7 I = 1) (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q I)
    (hQ2 : CFSG.Open.pRank 3 Q ≤ 2) (hA : CFSG.ABGLocalTools.IsSylowOf 3 A L)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set X)) :
    ∃ x : X, orderOf x = 7 ∧ (∀ y ∈ Q, x * y = y * x) ∧ ∀ a ∈ A, x * a = a * x :=
  exists_sevenElement_centralizing_D_aux_main hKOut hLn
    (barO2_isLThree_of_lift hKSML3 hX hLs hL h3).1 hI hQ hA hAQ
    (two_le_pRank_centralizer_of_pComponent_le_six hKSML3 hX hLs hL h3 h7X hrank hI hIc hI1 hQ hQ2)

end SevenElement

section OddNormalizer

variable {X : Type} [Group X] [Finite X]

theorem normal_I_of_noncyclic_aux_isPComponent_conj {C I : Subgroup X} [C.Normal] (g : X)
    (hIC : I ≤ C) (hI : CFSG.IsPComponent 7 (I.subgroupOf C)) :
    conjSub g I ≤ C ∧ CFSG.IsPComponent 7 ((conjSub g I).subgroupOf C) := by
  have hC : C.map (MulAut.conj g).toMonoidHom = C := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      simpa [MulAut.conj_apply] using ‹C.Normal›.conj_mem c hc g
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · simpa using ‹C.Normal›.conj_mem x hx g⁻¹
      · simp [MulAut.conj_apply, mul_assoc]
  have h := CFSG.ComponentClassification.CatFactsSp4.isPComponent_map_subgroupOf 7
    (MulAut.conj g) hIC hI
  rw [hC] at h
  refine ⟨?_, h⟩
  rintro _ ⟨a, ha, rfl⟩
  simpa [MulAut.conj_apply] using ‹C.Normal›.conj_mem a (hIC ha) g

theorem mem_normalizer_I_of_odd_order_aux_conj_mul (g h : X) (H : Subgroup X) :
    conjSub g (conjSub h H) = conjSub (g * h) H := by
  unfold conjSub
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [mul_assoc]

theorem mem_normalizer_I_of_odd_order_aux_coset {I : Subgroup X} {g g' : X}
    (h : conjSub g I = conjSub g' I) : g⁻¹ * g' ∈ Subgroup.normalizer (I : Set X) := by
  apply mem_normalizer_iff_map_conj_eq.2
  show conjSub (g⁻¹ * g') I = I
  have h1 : conjSub g⁻¹ (conjSub g I) = I := by
    rw [mem_normalizer_I_of_odd_order_aux_conj_mul, inv_mul_cancel]
    unfold conjSub
    ext y
    simp
  rw [← mem_normalizer_I_of_odd_order_aux_conj_mul, ← h, h1]

end OddNormalizer

end CFSG.LocalAnalysis.RankThreeUC.S15
