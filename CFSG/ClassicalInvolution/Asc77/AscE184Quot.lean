module

public import CFSG.ClassicalInvolution.Asc77.AscQuot614
public import CFSG.Goldschmidt.Steps.LemmaXBasic
public import CFSG.ClassicalInvolution.Asc77.AscSteps182

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

@[expose] def quotFamily (Ω : Set (Subgroup G)) (N : Subgroup G) [N.Normal] :
    Set (Subgroup (G ⧸ N)) :=
  Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' N)) Ω

variable (p f) in
@[expose] def OddQuotHyp : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ (N : Subgroup G) [N.Normal], Odd (Nat.card N) → HypOmegaMod p f (quotFamily Ω N)

theorem mem_quotFamily_iff {N : Subgroup G} [N.Normal] {M : Subgroup (G ⧸ N)} :
    M ∈ quotFamily Ω N ↔ ∃ K ∈ Ω, K.map (QuotientGroup.mk' N) = M := Iff.rfl

theorem map_mem_quotFamily {N : Subgroup G} [N.Normal] {K : Subgroup G} (hK : K ∈ Ω) :
    K.map (QuotientGroup.mk' N) ∈ quotFamily Ω N := ⟨K, hK, rfl⟩

section Finite

variable [Finite G] {N : Subgroup G} [N.Normal]

omit [Finite G] [N.Normal] in
theorem odd_natCard_inf (hN : Odd (Nat.card N)) (K : Subgroup G) : Odd (Nat.card ↥(N ⊓ K)) :=
  hN.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

omit [Finite G] in
theorem natCard_map_mk_mul (K : Subgroup G) :
    Nat.card ↥(K.map (QuotientGroup.mk' N)) * Nat.card ↥(N ⊓ K) = Nat.card K := by
  have hker : (AscQuot.quotRestrict K N).ker = N.subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subtype.ext_iff, AscQuot.quotRestrict_apply]
    exact QuotientGroup.eq_one_iff (x : G)
  have h1 : Nat.card (↥K ⧸ (AscQuot.quotRestrict K N).ker) =
      Nat.card ↥(K.map (QuotientGroup.mk' N)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (AscQuot.quotRestrict_surjective K N)).toEquiv
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (AscQuot.quotRestrict K N).ker
  have h3 : Nat.card ↥(AscQuot.quotRestrict K N).ker = Nat.card ↥(N ⊓ K) := by
    rw [hker, ← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← h1, ← h3]
  exact h2.symm

theorem factorization_two_natCard_map_mk (hN : Odd (Nat.card N)) (K : Subgroup G) :
    (Nat.card ↥(K.map (QuotientGroup.mk' N))).factorization 2 = (Nat.card K).factorization 2 := by
  have hmul := natCard_map_mk_mul (N := N) K
  have h0 : Nat.card ↥(K.map (QuotientGroup.mk' N)) ≠ 0 := Nat.card_pos.ne'
  have h1 : Nat.card ↥(N ⊓ K) ≠ 0 := Nat.card_pos.ne'
  have hodd := odd_natCard_inf hN K
  have h2 : (Nat.card ↥(N ⊓ K)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr h2))
  rw [← hmul, Nat.factorization_mul h0 h1, Finsupp.add_apply, h2, add_zero]

theorem exists_isPGroup_lift_of_mem_map {K : Subgroup G} {b : G ⧸ N}
    (hbK : b ∈ K.map (QuotientGroup.mk' N)) (hb : IsPGroup 2 (Subgroup.zpowers b)) :
    ∃ k ∈ K, QuotientGroup.mk' N k = b ∧ IsPGroup 2 (Subgroup.zpowers k) := by
  have hb' : IsPGroup 2 (Subgroup.zpowers (⟨b, hbK⟩ : ↥(K.map (QuotientGroup.mk' N)))) := by
    obtain ⟨n, hn⟩ := hb.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← Nat.card_zpowers]
    exact hn
  obtain ⟨k, hk, hk2⟩ := exists_isPGroup_zpowers_lift (AscQuot.quotRestrict K N)
    (AscQuot.quotRestrict_surjective K N) hb'
  refine ⟨(k : G), k.2, congrArg Subtype.val hk, ?_⟩
  obtain ⟨n, hn⟩ := hk2.exists_card_eq
  refine IsPGroup.of_card (n := n) ?_
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, ← Nat.card_zpowers]
  exact hn

theorem eight_le_natCard_of_mem (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K : Subgroup G}
    (hK : K ∈ Ω) : 8 ≤ Nat.card K := by
  obtain ⟨R, hR, hRK, -⟩ := exists_mem_RSet_ge hK (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    bot_le
  have h8 := hΩ.eight_le_of_mem_RSet hp hR
  have := Subgroup.card_le_of_le hRK.1
  omega

omit [Finite G] in
theorem exists_conj_eq_of_map_eq (hN : Odd (Nat.card N)) {z t : G} (hz : z * z = 1)
    (ht : t * t = 1) (h : QuotientGroup.mk' N z = QuotientGroup.mk' N t) :
    ∃ n ∈ N, n * t * n⁻¹ = z := by
  have hoN : z * t ∈ N := by
    have : QuotientGroup.mk' N (z * t) = 1 := by
      rw [map_mul, h, ← map_mul, ht, map_one]
    exact (QuotientGroup.eq_one_iff _).mp this
  have hodd : Odd (orderOf (z * t)) := hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hoN)
  have e : z * (z * t) = t := by rw [← mul_assoc, hz, one_mul]
  obtain ⟨a, ha⟩ := CFSG.Goldschmidt.LemmaX.exists_pow_conj_eq_mul (t := z) (o := z * t) hz
    (by rw [e]; exact ht) hodd
  rw [e] at ha
  obtain ⟨n, hn, ht'⟩ : ∃ n ∈ N, t = n⁻¹ * z * n := ⟨(z * t) ^ a, N.pow_mem hoN a, ha⟩
  refine ⟨n, hn, ?_⟩
  rw [ht']
  group

theorem E187C.eq_one_or_eq_of_map_eq_of_twin_of
    (hcomm : ∀ {K J : Subgroup G} {z : G}, K ∈ Ω → J ∈ Ω → K ≠ J →
      IsUniqueInvolution K z → IsUniqueInvolution J z → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J)
    (hc2 : ∀ {K : Subgroup G} {z : G}, K ∈ Ω → IsUniqueInvolution K z → ∀ w ∈ K,
      IsPGroup 2 (Subgroup.zpowers w) → (∀ y ∈ K, ⁅w, y⁆ ∈ oddCoreOf K) → w = 1 ∨ w = z)
    (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z) {x k : G} (hx : x ∈ J)
    (hk : k ∈ K) (hk2 : IsPGroup 2 (Subgroup.zpowers k))
    (hxk : QuotientGroup.mk' N x = QuotientGroup.mk' N k) : k = 1 ∨ k = z := by
  have hcomm := hcomm hK hJ hKJ hzK hzJ
  have hm : k⁻¹ * x ∈ N := by
    have := hxk.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
    exact this
  obtain ⟨m, hmN, rfl⟩ : ∃ m ∈ N, x = k * m := ⟨k⁻¹ * x, hm, by group⟩
  refine hc2 hK hzK k hk hk2 fun k' hk' => ?_
  have hc : ⁅k * m, k'⁆ ∈ oddCoreOf K := by
    have h1 : ⁅k * m, k'⁆ ∈ ⁅J, K⁆ := Subgroup.commutator_mem_commutator hx hk'
    rw [Subgroup.commutator_comm] at h1
    exact (hcomm h1).1
  have hu : m * (k' * m⁻¹ * k'⁻¹) ∈ N :=
    N.mul_mem hmN (‹N.Normal›.conj_mem _ (N.inv_mem hmN) k')
  have hn₁N : (k * (m * (k' * m⁻¹ * k'⁻¹)) * k⁻¹)⁻¹ ∈ N :=
    N.inv_mem (‹N.Normal›.conj_mem _ hu k)
  have e : ⁅k, k'⁆ = (k * (m * (k' * m⁻¹ * k'⁻¹)) * k⁻¹)⁻¹ * ⁅k * m, k'⁆ := by
    simp only [commutatorElement_def]
    group
  have hKk : ⁅k, k'⁆ ∈ K := by
    simp only [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) (K.inv_mem hk')
  have hn₁K : (k * (m * (k' * m⁻¹ * k'⁻¹)) * k⁻¹)⁻¹ ∈ K := by
    have : (k * (m * (k' * m⁻¹ * k'⁻¹)) * k⁻¹)⁻¹ = ⁅k, k'⁆ * (⁅k * m, k'⁆)⁻¹ := by
      rw [e]
      group
    rw [this]
    exact K.mul_mem hKk (K.inv_mem (oddCoreOf_le_self K hc))
  have hn₁O := inf_le_oddCoreOf_of_odd N (odd_natCard_inf hN K) ⟨hn₁K, hn₁N⟩
  rw [e]
  exact (oddCoreOf K).mul_mem hn₁O hc

theorem eq_one_or_eq_of_map_eq_of_twin (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z) {x k : G} (hx : x ∈ J)
    (hk : k ∈ K) (hk2 : IsPGroup 2 (Subgroup.zpowers k))
    (hxk : QuotientGroup.mk' N x = QuotientGroup.mk' N k) : k = 1 ∨ k = z :=
  E187C.eq_one_or_eq_of_map_eq_of_twin_of
    (fun hK hJ hKJ hzK hzJ => hΩ.comm_le_oddCore_of_twin hK hJ hKJ hzK hzJ)
    (fun hK hz => hΩ.center_two hp hq hK hz)
    hN hK hJ hKJ hzK hzJ hx hk hk2 hxk

theorem E187C.exists_conj_of_map_eq_of
    (hzK : ∀ {K : Subgroup G}, K ∈ Ω → ∃ z : G, IsUniqueInvolution K z)
    (hc : ConjInvariant Ω) (h8R : ∀ {Q : Subgroup G}, Q ∈ RSet Ω → 8 ≤ Nat.card Q)
    (hcomm : ∀ {K J : Subgroup G} {z : G}, K ∈ Ω → J ∈ Ω → K ≠ J →
      IsUniqueInvolution K z → IsUniqueInvolution J z → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J)
    (hc2 : ∀ {K : Subgroup G} {z : G}, K ∈ Ω → IsUniqueInvolution K z → ∀ w ∈ K,
      IsPGroup 2 (Subgroup.zpowers w) → (∀ y ∈ K, ⁅w, y⁆ ∈ oddCoreOf K) → w = 1 ∨ w = z)
    (hN : Odd (Nat.card N)) {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω)
    (h : K.map (QuotientGroup.mk' N) = L.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, L = conjSub n K := by
  set mk := QuotientGroup.mk' N with hmk
  obtain ⟨z, hz⟩ := hzK hK
  obtain ⟨t, ht⟩ := hzK hL
  have hzb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hz
  have htb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN L) ht
  have hzt : mk z = mk t := by
    have hmem : mk t ∈ K.map mk := h ▸ htb.mem
    exact ((hzb.unique _ hmem htb.sq).resolve_left htb.ne_one).symm
  obtain ⟨n, hn, e2⟩ := exists_conj_eq_of_map_eq hN hz.sq ht.sq hzt
  have hn1 : mk n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  have hL' : conjSub n L ∈ Ω := hc n L hL
  have hL'z : IsUniqueInvolution (conjSub n L) z := by
    have := ht.conj n
    rwa [e2] at this
  have himg : (conjSub n L).map mk = L.map mk := by
    rw [AscQuot.map_conjSub, hn1, conjSub_one]
  by_cases hKL' : conjSub n L = K
  · refine ⟨n⁻¹, N.inv_mem hn, ?_⟩
    rw [← hKL', conjSub_inv_conjSub]
  · exfalso
    obtain ⟨T, hT, hTsyl, -⟩ :=
      exists_mem_RSet_ge hL' (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G)) bot_le
    have hT8 := h8R hT
    have hTN : T ⊓ N = ⊥ :=
      AscQuot.inf_eq_bot_of_isPGroup_of_odd N hTsyl.2.1 hTsyl.1 (odd_natCard_inf hN _)
    have hsub : ∀ y ∈ T.map mk, y = 1 ∨ y = mk z := by
      rintro _ ⟨x, hxT, rfl⟩
      have hxL' : x ∈ conjSub n L := hTsyl.1 hxT
      have hxbar : mk x ∈ K.map mk := by
        rw [h, ← himg]
        exact Subgroup.mem_map_of_mem _ hxL'
      have hx2 : IsPGroup 2 (Subgroup.zpowers (mk x)) :=
        (hTsyl.2.1.map mk).to_le (Subgroup.zpowers_le.mpr ⟨x, hxT, rfl⟩)
      obtain ⟨k, hk, hkx, hk2⟩ := exists_isPGroup_lift_of_mem_map hxbar hx2
      rcases E187C.eq_one_or_eq_of_map_eq_of_twin_of hcomm hc2 hN hK hL' (Ne.symm hKL') hz hL'z hxL'
        hk hk2
        hkx.symm with h1 | h1
      · left
        rw [← hkx, h1, map_one]
      · right
        rw [← hkx, h1]
    have hcard2 : Nat.card ↥(T.map mk) ≤ 2 := natCard_subgroup_le_two_of_subset hsub
    have hcardT : Nat.card ↥(T.map mk) = Nat.card T :=
      (Nat.card_congr (AscQuot.quotRestrictEquiv hTN).toEquiv).symm
    omega

theorem exists_conj_of_map_eq (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hN : Odd (Nat.card N)) {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω)
    (h : K.map (QuotientGroup.mk' N) = L.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, L = conjSub n K :=
  E187C.exists_conj_of_map_eq_of (fun hK => hΩ.exists_uniqueInvolution hp hq hK) hΩ.conjInvariant
    (fun hQ => hΩ.eight_le_of_mem_RSet hp hQ)
    (fun hK hJ hKJ hzK hzJ => hΩ.comm_le_oddCore_of_twin hK hJ hKJ hzK hzJ)
    (fun hK hz => hΩ.center_two hp hq hK hz)
    hN hK hL h

omit [Finite G] [N.Normal] in
theorem odd_natCard_conjSubClass (hN : Odd (Nat.card N)) (T : Subgroup G) :
    Odd (Nat.card ↥{M : Subgroup G | ∃ n ∈ N, M = conjSub n T}) := by
  set X : Set (Subgroup G) := {M | ∃ n ∈ N, M = conjSub n T} with hX
  have hconj : ∀ n ∈ N, conjSub n T ∈ X := fun n hn => ⟨n, hn, rfl⟩
  set T' : Subgroup ↥N := (N ⊓ Subgroup.normalizer (T : Set G)).subgroupOf N with hT'
  let ψ : ↥N → ↥X := fun n => ⟨conjSub (n : G) T, hconj n n.2⟩
  have hψeq : ∀ a b : ↥N, ψ a = ψ b ↔ a⁻¹ * b ∈ T' := by
    intro a b
    constructor
    · intro h
      have h1 : conjSub (a : G) T = conjSub (b : G) T := congrArg Subtype.val h
      have h2 : conjSub ((a : G)⁻¹ * (b : G)) T = T := by
        rw [conjSub_mul, ← h1, conjSub_inv_conjSub]
      show ((a⁻¹ * b : ↥N) : G) ∈ N ⊓ Subgroup.normalizer (T : Set G)
      refine ⟨(a⁻¹ * b).2, ?_⟩
      have : ((a⁻¹ * b : ↥N) : G) = (a : G)⁻¹ * (b : G) := by simp
      rw [this]
      exact mem_normalizer_iff_conjSub_eq.mpr h2
    · intro h
      have h1 : ((a⁻¹ * b : ↥N) : G) ∈ Subgroup.normalizer (T : Set G) := h.2
      have h2 : conjSub ((a : G)⁻¹ * (b : G)) T = T := by
        have : ((a⁻¹ * b : ↥N) : G) = (a : G)⁻¹ * (b : G) := by simp
        rw [← this]
        exact mem_normalizer_iff_conjSub_eq.mp h1
      apply Subtype.ext
      show conjSub (a : G) T = conjSub (b : G) T
      have : (b : G) = (a : G) * ((a : G)⁻¹ * (b : G)) := by group
      rw [this, conjSub_mul, h2]
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨M, n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, rfl⟩
  let φ : (↥N ⧸ T') → ↥X := Quotient.lift ψ (fun a b hab => by
    exact (hψeq a b).mpr (QuotientGroup.leftRel_apply.mp hab))
  have hφbij : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    · intro a b
      induction a using Quotient.inductionOn with | _ a => ?_
      induction b using Quotient.inductionOn with | _ b => ?_
      intro hab
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hψeq a b).mp hab))
    · intro y
      obtain ⟨n, hn⟩ := hψsurj y
      exact ⟨Quotient.mk _ n, hn⟩
  have hcard : Nat.card ↥X = T'.index := by
    rw [← Nat.card_congr (Equiv.ofBijective φ hφbij)]
    rfl
  rw [hcard]
  exact hN.of_dvd_nat (Subgroup.index_dvd_card T')

omit [Finite G] in
theorem exists_conj_normalizer_of_perm (hN : Odd (Nat.card N)) (T : Subgroup G) {V : Subgroup G}
    (hV : IsPGroup 2 V) (hperm : ∀ v ∈ V, ∃ n ∈ N, conjSub v T = conjSub n T) :
    ∃ n ∈ N, V ≤ Subgroup.normalizer ((conjSub n T : Subgroup G) : Set G) := by
  set X : Set (Subgroup G) := {M | ∃ n ∈ N, M = conjSub n T} with hX
  have hclosed : ∀ v ∈ V, ∀ M ∈ X, conjSub v M ∈ X := by
    rintro v hv _ ⟨n, hn, rfl⟩
    obtain ⟨n', hn', hvT⟩ := hperm v hv
    refine ⟨(v * n * v⁻¹) * n', N.mul_mem (‹N.Normal›.conj_mem n hn v) hn', ?_⟩
    calc conjSub v (conjSub n T) = conjSub (v * n) T := (conjSub_mul v n T).symm
      _ = conjSub ((v * n * v⁻¹) * v) T := by congr 1; group
      _ = conjSub (v * n * v⁻¹) (conjSub v T) := conjSub_mul _ _ _
      _ = conjSub (v * n * v⁻¹) (conjSub n' T) := by rw [hvT]
      _ = conjSub ((v * n * v⁻¹) * n') T := (conjSub_mul _ _ _).symm
  let _ : MulAction V X :=
    { smul := fun v M => ⟨conjSub (v : G) M.1, hclosed v v.2 M.1 M.2⟩
      one_smul := fun M => Subtype.ext (conjSub_one M.1)
      mul_smul := fun a b M => Subtype.ext (conjSub_mul (a : G) (b : G) M.1) }
  have hodd : ¬ 2 ∣ Nat.card X := by
    have h := odd_natCard_conjSubClass hN T
    exact fun h2 => (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)
  have hVp : IsPGroup 2 ↥V := hV
  obtain ⟨M₀, hM₀⟩ := hVp.nonempty_fixed_point_of_prime_not_dvd_card X hodd
  obtain ⟨n, hn, hMn⟩ := M₀.2
  refine ⟨n, hn, fun v hv => ?_⟩
  have hfix : conjSub (v : G) M₀.1 = M₀.1 := congrArg Subtype.val (hM₀ ⟨v, hv⟩)
  rw [hMn] at hfix
  exact mem_normalizer_iff_conjSub_eq.mpr hfix

theorem E187C.exists_conj_normalizer_of (hc : ConjInvariant Ω)
    (hexc : ∀ {K L : Subgroup G}, K ∈ Ω → L ∈ Ω →
      K.map (QuotientGroup.mk' N) = L.map (QuotientGroup.mk' N) → ∃ n ∈ N, L = conjSub n K)
    (hN : Odd (Nat.card N)) {K : Subgroup G} (hK : K ∈ Ω) {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hUN : ∀ u ∈ U, QuotientGroup.mk' N u ∈
      Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) :
    ∃ n ∈ N, U ≤ Subgroup.normalizer ((conjSub n K : Subgroup G) : Set G) := by
  refine exists_conj_normalizer_of_perm hN K hU2 fun u hu => ?_
  have himg : K.map (QuotientGroup.mk' N) = (conjSub u K).map (QuotientGroup.mk' N) := by
    rw [AscQuot.map_conjSub]
    exact (mem_normalizer_iff_conjSub_eq.mp (hUN u hu)).symm
  obtain ⟨n, hn, hnK⟩ := hexc hK (hc u K hK) himg
  exact ⟨n, hn, hnK⟩


theorem exists_conj_normalizer (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hN : Odd (Nat.card N)) {K : Subgroup G} (hK : K ∈ Ω) {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hUN : ∀ u ∈ U, QuotientGroup.mk' N u ∈
      Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) :
    ∃ n ∈ N, U ≤ Subgroup.normalizer ((conjSub n K : Subgroup G) : Set G) := by
  exact E187C.exists_conj_normalizer_of hΩ.conjInvariant (fun hK hL h => exists_conj_of_map_eq hp hq hΩ hN hK hL h) hN hK hU2 hUN

omit [N.Normal] in
theorem exists_conjSub_eq_of_isSylow2In {P V₁ V₂ : Subgroup G} (h₁ : IsSylow2In V₁ P)
    (h₂ : IsSylow2In V₂ P) : ∃ x ∈ P, conjSub x V₁ = V₂ := by
  obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow (G := ↥P) (AscQuot.sylowOfIsSylow2In' h₁)
    (AscQuot.sylowOfIsSylow2In' h₂)
  refine ⟨(x : G), x.2, ?_⟩
  have hV₁x : conjSub (x : G) V₁ ≤ P := by
    have := conjSub_mono (n := (x : G)) h₁.1
    rwa [conjSub_eq_self_of_mem x.2] at this
  have h1 : (conjSub (x : G) V₁).subgroupOf P = V₂.subgroupOf P := by
    rw [← conjSub_subgroupOf P x V₁]
    exact hx
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_eq_left.mpr hV₁x, inf_eq_left.mpr h₂.1] at h2

omit [Fact p.Prime] in
theorem natCard_eq_pow_of_isSylow2In {V P : Subgroup G} (h : IsSylow2In V P) :
    Nat.card V = 2 ^ (Nat.card P).factorization 2 := by
  have e1 := Sylow.card_eq_multiplicity (AscQuot.sylowOfIsSylow2In' h)
  have c1 : Nat.card ↥(V.subgroupOf P) = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv
  have e1' : Nat.card ↥(V.subgroupOf P) = 2 ^ (Nat.card P).factorization 2 := e1
  rw [← c1, e1']

theorem natCard_sylow_map_eq (hN : Odd (Nat.card N)) {J V : Subgroup G} {W' : Subgroup (G ⧸ N)}
    (hV : IsSylow2In V J) (hV' : IsSylow2In W' (J.map (QuotientGroup.mk' N))) :
    Nat.card V = Nat.card W' := by
  rw [natCard_eq_pow_of_isSylow2In hV, natCard_eq_pow_of_isSylow2In hV',
    factorization_two_natCard_map_mk hN J]

theorem E187C.exists_lift_USet_of
    (hdata : ∀ {U : Subgroup (G ⧸ N)}, U ∈ USet (quotFamily Ω N) →
      ∃ R ∈ RSet (quotFamily Ω N), ∃ J ∈ quotFamily Ω N, IsSylow2In R J ∧ U ≤ R ∧
        IsCyclic ↥U ∧ Nat.card R = 2 * Nat.card U ∧ 4 ≤ Nat.card U)
    (heq : ∀ {K J A : Subgroup (G ⧸ N)}, K ∈ quotFamily Ω N → J ∈ quotFamily Ω N →
      IsPGroup 2 A → 4 ≤ Nat.card A → A ≤ K → A ≤ J → K = J)
    (hN : Odd (Nat.card N)) {J : Subgroup G} (hJ : J ∈ Ω)
    {Ub : Subgroup (G ⧸ N)} (hUb : Ub ∈ USet (quotFamily Ω N))
    (hUbJ : Ub ≤ J.map (QuotientGroup.mk' N)) :
    ∃ U ∈ USet Ω, U ≤ J ∧ U.map (QuotientGroup.mk' N) = Ub := by
  set mk := QuotientGroup.mk' N with hmk
  obtain ⟨Rb, hRb, Jb₁, hJb₁, hRbsyl, hUbRb, hcyc, hcard, h4⟩ := hdata hUb
  have hUb2 : IsPGroup 2 Ub := hRbsyl.2.1.to_le hUbRb
  have hJb : Jb₁ = J.map mk :=
    heq hJb₁ (map_mem_quotFamily hJ) hUb2 h4 (hUbRb.trans hRbsyl.1) hUbJ
  rw [hJb] at hRbsyl
  obtain ⟨ub, hub⟩ := hcyc.exists_generator
  have hUbz : Subgroup.zpowers (ub : G ⧸ N) = Ub := by
    refine le_antisymm (Subgroup.zpowers_le.mpr ub.2) fun y hy => ?_
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hub ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hub2 : IsPGroup 2 (Subgroup.zpowers (ub : G ⧸ N)) := by
    rw [hUbz]
    exact hUb2
  obtain ⟨a, haJ, hamk, ha2⟩ := exists_isPGroup_lift_of_mem_map (hUbJ ub.2) hub2
  set U : Subgroup G := Subgroup.zpowers a with hU
  have hUJ : U ≤ J := Subgroup.zpowers_le.mpr haJ
  have hUmap : U.map mk = Ub := by
    rw [hU, MonoidHom.map_zpowers, hamk, hUbz]
  have hUN : U ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N ha2 hUJ (odd_natCard_inf hN J)
  have hUcard : Nat.card U = Nat.card Ub := by
    rw [← hUmap]
    exact Nat.card_congr (AscQuot.quotRestrictEquiv hUN).toEquiv
  obtain ⟨R, hR, hRsyl, hUR⟩ := exists_mem_RSet_ge hJ ha2 hUJ
  have hRcard : Nat.card R = 2 * Nat.card U := by
    rw [natCard_sylow_map_eq hN hRsyl hRbsyl, hcard, hUcard]
  exact ⟨U, mem_USet_of_natCard hJ hRsyl hUR (by rw [hU]; infer_instance) hRcard, hUJ, hUmap⟩



theorem exists_lift_USet (hp : p ≠ 2) (hΩ' : HypOmegaMod p f (quotFamily Ω N))
    (hN : Odd (Nat.card N)) {J : Subgroup G} (hJ : J ∈ Ω)
    {Ub : Subgroup (G ⧸ N)} (hUb : Ub ∈ USet (quotFamily Ω N))
    (hUbJ : Ub ≤ J.map (QuotientGroup.mk' N)) :
    ∃ U ∈ USet Ω, U ≤ J ∧ U.map (QuotientGroup.mk' N) = Ub := by
  exact E187C.exists_lift_USet_of (fun hU => hΩ'.exists_data_of_mem_USet hp hU)
    (fun hK hJ hA h4 hAK hAJ => hΩ'.eq_of_le_of_le hK hJ hA h4 hAK hAJ) hN hJ hUb hUbJ

theorem E187C.exists_conj_omegaStarNbr_of
    (hlift : ∀ {J : Subgroup G} {Ub : Subgroup (G ⧸ N)}, J ∈ Ω → Ub ∈ USet (quotFamily Ω N) →
      Ub ≤ J.map (QuotientGroup.mk' N) →
      ∃ U ∈ USet Ω, U ≤ J ∧ U.map (QuotientGroup.mk' N) = Ub)
    (hUp : ∀ {U : Subgroup G}, U ∈ USet Ω → IsPGroup 2 U)
    (hnorm : ∀ {K U : Subgroup G}, K ∈ Ω → IsPGroup 2 U →
      (∀ u ∈ U, QuotientGroup.mk' N u ∈
        Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) →
      ∃ n ∈ N, U ≤ Subgroup.normalizer ((conjSub n K : Subgroup G) : Set G))
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaStarNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ n ∈ N, J ∈ omegaStarNbr Ω (conjSub n K) := by
  obtain ⟨-, hne, Ub, hUb, hUbJ, hUbN⟩ := h
  obtain ⟨U, hU, hUJ, hUmap⟩ := hlift hJ hUb hUbJ
  have hU2 : IsPGroup 2 U := hUp hU
  obtain ⟨n, hn, hUn⟩ := hnorm hK hU2 (fun u hu =>
    hUbN (hUmap ▸ Subgroup.mem_map_of_mem _ hu))
  refine ⟨n, hn, hJ, ?_, U, hU, hUJ, hUn⟩
  intro hJK
  apply hne
  rw [hJK, AscQuot.map_conjSub, show QuotientGroup.mk' N n = 1 from
    (QuotientGroup.eq_one_iff _).mpr hn, conjSub_one]



theorem exists_conj_omegaStarNbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hΩ' : HypOmegaMod p f (quotFamily Ω N)) (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaStarNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ n ∈ N, J ∈ omegaStarNbr Ω (conjSub n K) := by
  exact E187C.exists_conj_omegaStarNbr_of (fun hJ hUb hUbJ => exists_lift_USet hp hΩ' hN hJ hUb hUbJ)
    (fun hU => hΩ.isPGroup_of_mem_USet hp hU) (fun hK hU2 hUN => exists_conj_normalizer hp hq hΩ hN hK hU2 hUN) hK hJ h

omit [Fact p.Prime] [Finite G] in
theorem mk_mem_normalizer_map {K : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G)) :
    QuotientGroup.mk' N t ∈
      Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
  rw [mem_normalizer_iff_conjSub_eq, ← AscQuot.map_conjSub, mem_normalizer_iff_conjSub_eq.mp ht]

omit [Fact p.Prime] [Finite G] in
theorem map_pairNormalizers_le (K J : Subgroup G) (zK zJ : G) :
    (pairNormalizers K J zK zJ).map (QuotientGroup.mk' N) ≤
      pairNormalizers (K.map (QuotientGroup.mk' N)) (J.map (QuotientGroup.mk' N))
        (QuotientGroup.mk' N zK) (QuotientGroup.mk' N zJ) := by
  have hZ : (Subgroup.closure ({zK, zJ} : Set G)).map (QuotientGroup.mk' N) =
      Subgroup.closure ({QuotientGroup.mk' N zK, QuotientGroup.mk' N zJ} : Set (G ⧸ N)) := by
    rw [MonoidHom.map_closure, Set.image_pair]
  have hA : ∀ A : Subgroup G, (A ⊓ Subgroup.normalizer ((Subgroup.closure ({zK, zJ} : Set G) :
      Subgroup G) : Set G)).map (QuotientGroup.mk' N) ≤
      A.map (QuotientGroup.mk' N) ⊓ Subgroup.normalizer ((Subgroup.closure
        ({QuotientGroup.mk' N zK, QuotientGroup.mk' N zJ} : Set (G ⧸ N)) : Subgroup (G ⧸ N)) :
        Set (G ⧸ N)) := by
    intro A
    rintro _ ⟨x, ⟨hxA, hxN⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ hxA, ?_⟩
    rw [← hZ]
    exact mk_mem_normalizer_map hxN
  unfold pairNormalizers
  rw [Subgroup.map_sup]
  exact sup_le_sup (hA K) (hA J)

theorem isSylow2In_map_mk (hN : Odd (Nat.card N)) {J V : Subgroup G} (hV : IsSylow2In V J) :
    IsSylow2In (V.map (QuotientGroup.mk' N)) (J.map (QuotientGroup.mk' N)) := by
  obtain ⟨V₀, hV₀, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := J.map (QuotientGroup.mk' N))
    (IsPGroup.of_bot) bot_le
  have hcard : Nat.card V = Nat.card V₀ := natCard_sylow_map_eq hN hV hV₀
  have hVN : V ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hV.2.1 hV.1 (odd_natCard_inf hN J)
  have hmapcard : Nat.card ↥(V.map (QuotientGroup.mk' N)) = Nat.card V :=
    (Nat.card_congr (AscQuot.quotRestrictEquiv hVN).toEquiv).symm
  exact hV₀.of_natCard_le (hV.2.1.map _) (Subgroup.map_mono hV.1) (by rw [hmapcard, hcard])

theorem E187C.aEmpty_quotFamily_of (hc : ConjInvariant Ω)
    (hexn : ∀ {K J : Subgroup G}, K ∈ Ω → J ∈ Ω →
      J.map (QuotientGroup.mk' N) ∈
        omegaStarNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) →
      ∃ n ∈ N, J ∈ omegaStarNbr Ω (conjSub n K))
    (hsyl : ∀ {K Q : Subgroup G}, K ∈ Ω → Q ∈ RSet Ω → Q ≤ K → IsSylow2In Q K)
    (hzK : ∀ {K : Subgroup G}, K ∈ Ω → ∃ z : G, IsUniqueInvolution K z)
    (hN : Odd (Nat.card N)) (hA : ∀ J ∈ Ω, AEmpty Ω J) :
    ∀ M ∈ quotFamily Ω N, AEmpty (quotFamily Ω N) M := by
  rintro _ ⟨K, hK, rfl⟩
  intro Jb hJbstar hJbnbr zKb zJb hzKb hzJb
  obtain ⟨J, hJ, rfl⟩ := hJbstar.1
  obtain ⟨n, hn, hstar⟩ := hexn hK hJ hJbstar
  have hnN : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  set K₁ : Subgroup G := conjSub n K with hK₁def
  have hK₁ : K₁ ∈ Ω := hc n K hK
  have himg : K₁.map (QuotientGroup.mk' N) = K.map (QuotientGroup.mk' N) := by
    rw [hK₁def, AscQuot.map_conjSub, hnN, conjSub_one]
  have hnbr : J ∉ omegaNbr Ω K₁ := by
    rintro ⟨-, -, T, hT, hTJ, hTN⟩
    apply hJbnbr
    have hTsyl : IsSylow2In T J := hsyl hJ hT hTJ
    refine ⟨map_mem_quotFamily hJ, hJbstar.2.1, T.map (QuotientGroup.mk' N),
      mem_RSet_of_isSylow2In (map_mem_quotFamily hJ) (isSylow2In_map_mk hN hTsyl),
      Subgroup.map_mono hTJ, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have := mk_mem_normalizer_map (N := N) (hTN ht)
    rwa [himg] at this
  obtain ⟨z₁, hz₁⟩ := hzK hK₁
  obtain ⟨zJ, hzJ⟩ := hzK hJ
  have e1 : QuotientGroup.mk' N z₁ = zKb := by
    have h1 := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K₁) hz₁
    rw [himg] at h1
    exact h1.eq hzKb
  have e2 : QuotientGroup.mk' N zJ = zJb :=
    (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN J) hzJ).eq hzJb
  obtain ⟨g, hg, hgK⟩ := hA K₁ hK₁ J hstar hnbr z₁ zJ hz₁ hzJ
  refine ⟨QuotientGroup.mk' N g, ?_, ?_⟩
  · have h2 := map_pairNormalizers_le (N := N) K₁ J z₁ zJ (Subgroup.mem_map_of_mem _ hg)
    rw [himg, e1, e2] at h2
    exact h2
  · have h3 := congrArg (Subgroup.map (QuotientGroup.mk' N)) hgK
    rw [AscQuot.map_conjSub, himg] at h3
    exact h3



theorem aEmpty_quotFamily (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hΩ' : HypOmegaMod p f (quotFamily Ω N)) (hN : Odd (Nat.card N)) (hA : ∀ J ∈ Ω, AEmpty Ω J) :
    ∀ M ∈ quotFamily Ω N, AEmpty (quotFamily Ω N) M := by
  exact E187C.aEmpty_quotFamily_of hΩ.conjInvariant
    (fun hK hJ h => exists_conj_omegaStarNbr hp hq hΩ hΩ' hN hK hJ h)
    (fun hK hT hTJ => hΩ.isSylow2In_of_mem_RSet_of_le hp hK hT hTJ)
    (fun hK => hΩ.exists_uniqueInvolution hp hq hK) hN hA

end Finite

end CFSG.ClassicalInvolution.Asc77
