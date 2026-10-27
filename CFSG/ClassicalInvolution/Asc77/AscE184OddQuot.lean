module

public import CFSG.ClassicalInvolution.Asc77.AscE184Quot

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

section Finite

variable [Finite G] {N : Subgroup G} [N.Normal]

omit [Finite G] [N.Normal] in
theorem odd_natCard_conjClass (hN : Odd (Nat.card N)) (z : G) :
    Odd (Nat.card ↥{w : G | ∃ n ∈ N, w = n * z * n⁻¹}) := by
  set X : Set G := {w | ∃ n ∈ N, w = n * z * n⁻¹} with hX
  set T' : Subgroup ↥N := (N ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf N with hT'
  let ψ : ↥N → ↥X := fun n => ⟨(n : G) * z * (n : G)⁻¹, n, n.2, rfl⟩
  have hψeq : ∀ a b : ↥N, ψ a = ψ b ↔ a⁻¹ * b ∈ T' := by
    intro a b
    have hmem : a⁻¹ * b ∈ T' ↔ ((a : G)⁻¹ * (b : G)) * z = z * ((a : G)⁻¹ * (b : G)) := by
      have hab : ((a⁻¹ * b : ↥N) : G) = (a : G)⁻¹ * (b : G) := by simp
      show ((a⁻¹ * b : ↥N) : G) ∈ N ⊓ Subgroup.centralizer ({z} : Set G) ↔ _
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, hab]
      exact ⟨fun h => h.2, fun h => ⟨N.mul_mem (N.inv_mem a.2) b.2, h⟩⟩
    rw [hmem]
    constructor
    · intro h
      have h1 : (a : G) * z * (a : G)⁻¹ = (b : G) * z * (b : G)⁻¹ := congrArg Subtype.val h
      calc ((a : G)⁻¹ * (b : G)) * z = (a : G)⁻¹ * ((b : G) * z * (b : G)⁻¹) * (b : G) := by group
        _ = (a : G)⁻¹ * ((a : G) * z * (a : G)⁻¹) * (b : G) := by rw [h1]
        _ = z * ((a : G)⁻¹ * (b : G)) := by group
    · intro h
      apply Subtype.ext
      show (a : G) * z * (a : G)⁻¹ = (b : G) * z * (b : G)⁻¹
      calc (a : G) * z * (a : G)⁻¹ = (a : G) * (z * ((a : G)⁻¹ * (b : G))) * (b : G)⁻¹ := by
            group
        _ = (a : G) * (((a : G)⁻¹ * (b : G)) * z) * (b : G)⁻¹ := by rw [h]
        _ = (b : G) * z * (b : G)⁻¹ := by group
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨w, n, hn, rfl⟩
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
theorem exists_fixed_conj_involution (hN : Odd (Nat.card N)) {z : G} (hz : z * z = 1)
    {V : Subgroup G} (hV : IsPGroup 2 V)
    (hVc : ∀ v ∈ V, QuotientGroup.mk' N v * QuotientGroup.mk' N z =
      QuotientGroup.mk' N z * QuotientGroup.mk' N v) :
    ∃ n ∈ N, ∀ v ∈ V, v * (n * z * n⁻¹) = (n * z * n⁻¹) * v := by
  set mk := QuotientGroup.mk' N with hmk
  set X : Set G := {w | ∃ n ∈ N, w = n * z * n⁻¹} with hX
  have hclosed : ∀ v ∈ V, ∀ w ∈ X, v * w * v⁻¹ ∈ X := by
    rintro v hv _ ⟨n, hn, rfl⟩
    have hmkn : mk n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
    have hsq : (v * (n * z * n⁻¹) * v⁻¹) * (v * (n * z * n⁻¹) * v⁻¹) = 1 := by
      calc (v * (n * z * n⁻¹) * v⁻¹) * (v * (n * z * n⁻¹) * v⁻¹)
          = v * n * (z * z) * n⁻¹ * v⁻¹ := by group
        _ = 1 := by rw [hz]; group
    have hmkw : mk (v * (n * z * n⁻¹) * v⁻¹) = mk z := by
      have hc := hVc v hv
      calc mk (v * (n * z * n⁻¹) * v⁻¹) = mk v * (mk n * mk z * (mk n)⁻¹) * (mk v)⁻¹ := by
            simp only [map_mul, map_inv]
        _ = mk v * mk z * (mk v)⁻¹ := by rw [hmkn]; group
        _ = mk z := by rw [hc]; group
    obtain ⟨m, hm, hmw⟩ := exists_conj_eq_of_map_eq hN hz hsq hmkw.symm
    refine ⟨m⁻¹, N.inv_mem hm, ?_⟩
    have : v * (n * z * n⁻¹) * v⁻¹ = m⁻¹ * (m * (v * (n * z * n⁻¹) * v⁻¹) * m⁻¹) * m := by group
    rw [this, hmw, inv_inv]
  let _ : MulAction V X :=
    { smul := fun v w => ⟨(v : G) * w.1 * (v : G)⁻¹, hclosed v v.2 w.1 w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ((1 : V) : G) * w.1 * ((1 : V) : G)⁻¹ = w.1
        simp)
      mul_smul := fun a b w => Subtype.ext (by
        show ((a * b : V) : G) * w.1 * ((a * b : V) : G)⁻¹ =
          (a : G) * ((b : G) * w.1 * (b : G)⁻¹) * (a : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  have hodd : ¬ 2 ∣ Nat.card X := by
    have h := odd_natCard_conjClass hN z
    exact fun h2 => (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)
  have hVp : IsPGroup 2 ↥V := hV
  obtain ⟨w₀, hw₀⟩ := hVp.nonempty_fixed_point_of_prime_not_dvd_card X hodd
  obtain ⟨n, hn, hw⟩ := w₀.2
  refine ⟨n, hn, fun v hv => ?_⟩
  have hfix : (v : G) * w₀.1 * (v : G)⁻¹ = w₀.1 := congrArg Subtype.val (hw₀ ⟨v, hv⟩)
  rw [hw] at hfix
  calc v * (n * z * n⁻¹) = v * (n * z * n⁻¹) * v⁻¹ * v := by group
    _ = (n * z * n⁻¹) * v := by rw [hfix]

theorem mem_of_two_dvd_card {K A : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hAK : A ≤ K) (h2 : 2 ∣ Nat.card A) : z ∈ A := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have htG : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have htsq : (t : G) * (t : G) = 1 := by
    have := pow_orderOf_eq_one (t : G)
    rwa [htG, pow_two] at this
  have htne : (t : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htG
    omega
  rcases hz.unique (t : G) (hAK t.2) htsq with h | h
  · exact absurd h htne
  · exact h ▸ t.2

open scoped commutatorElement in
theorem E187C.omega4_quot_odd_of
    (hzK0 : ∀ {K : Subgroup G}, K ∈ Ω → ∃ z : G, IsUniqueInvolution K z)
    (hcI : ConjInvariant Ω)
    (hcomm0 : ∀ {K J : Subgroup G} {z : G}, K ∈ Ω → J ∈ Ω → K ≠ J →
      IsUniqueInvolution K z → IsUniqueInvolution J z → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J)
    (hc20 : ∀ {K : Subgroup G} {z : G}, K ∈ Ω → IsUniqueInvolution K z → ∀ w ∈ K,
      IsPGroup 2 (Subgroup.zpowers w) → (∀ y ∈ K, ⁅w, y⁆ ∈ oddCoreOf K) → w = 1 ∨ w = z)
    (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hne : K.map (QuotientGroup.mk' N) ≠ J.map (QuotientGroup.mk' N)) :
    padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓ J.map (QuotientGroup.mk' N))) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓
        J.map (QuotientGroup.mk' N))) = 1 →
        ⁅K.map (QuotientGroup.mk' N), J.map (QuotientGroup.mk' N)⁆ ≤
          oddCoreOf (K.map (QuotientGroup.mk' N)) ⊓ oddCoreOf (J.map (QuotientGroup.mk' N))) := by
  set mk := QuotientGroup.mk' N with hmk
  by_cases h2 : 2 ∣ Nat.card ↥(K.map mk ⊓ J.map mk)
  swap
  · have : padicValNat 2 (Nat.card ↥(K.map mk ⊓ J.map mk)) = 0 :=
      padicValNat.eq_zero_of_not_dvd h2
    exact ⟨by omega, fun h => by omega⟩
  obtain ⟨z, hz⟩ := hzK0 hK
  obtain ⟨t, ht⟩ := hzK0 hJ
  have hzb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hz
  have htb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN J) ht
  have hzmem : mk z ∈ K.map mk ⊓ J.map mk := mem_of_two_dvd_card hzb inf_le_left h2
  have hzt : mk z = mk t := by
    rcases htb.unique (mk z) hzmem.2 hzb.sq with h | h
    · exact absurd h hzb.ne_one
    · exact h
  obtain ⟨n, hn, hnt⟩ := exists_conj_eq_of_map_eq hN hz.sq ht.sq hzt
  have hnN : mk n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  have hJ' : conjSub n J ∈ Ω := hcI n J hJ
  have hJ'z : IsUniqueInvolution (conjSub n J) z := by
    have := ht.conj n
    rwa [hnt] at this
  have himg : (conjSub n J).map mk = J.map mk := by
    rw [AscQuot.map_conjSub, hnN, conjSub_one]
  have hne' : K ≠ conjSub n J := fun h => hne (by rw [h, himg])
  have hcomm := hcomm0 hK hJ' hne' hz hJ'z
  have hsub : ∀ b ∈ K.map mk ⊓ J.map mk, IsPGroup 2 (Subgroup.zpowers b) →
      b = 1 ∨ b = mk z := by
    rintro b ⟨hbK, hbJ⟩ hb2
    obtain ⟨k, hk, hkb, hk2⟩ := exists_isPGroup_lift_of_mem_map hbK hb2
    obtain ⟨x, hx, hxb⟩ : b ∈ (conjSub n J).map mk := by
      rw [himg]
      exact hbJ
    rcases E187C.eq_one_or_eq_of_map_eq_of_twin_of hcomm0 hc20 hN hK hJ' hne' hz hJ'z hx hk hk2
      (hxb.trans hkb.symm) with h1 | h1
    · left
      rw [← hkb, h1, map_one]
    · right
      rw [← hkb, h1]
  refine ⟨padicValNat_natCard_le_one_of_forall_isPGroup hsub, fun _ => ?_⟩
  have h1 : ⁅K.map mk, J.map mk⁆ = (⁅K, conjSub n J⁆).map mk := by
    rw [Subgroup.map_commutator, himg]
  have hK' : oddCoreOf (K.map mk) = (oddCoreOf K).map mk :=
    oddCoreOf_map_mk_of_odd (odd_natCard_inf hN K)
  have hJ'' : oddCoreOf (J.map mk) = (oddCoreOf (conjSub n J)).map mk := by
    rw [← himg]
    exact oddCoreOf_map_mk_of_odd (odd_natCard_inf hN (conjSub n J))
  rw [h1, hK', hJ'']
  exact le_inf (Subgroup.map_mono (hcomm.trans inf_le_left))
    (Subgroup.map_mono (hcomm.trans inf_le_right))

theorem omega4_quot_odd (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hne : K.map (QuotientGroup.mk' N) ≠ J.map (QuotientGroup.mk' N)) :
    padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓ J.map (QuotientGroup.mk' N))) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓
        J.map (QuotientGroup.mk' N))) = 1 →
        ⁅K.map (QuotientGroup.mk' N), J.map (QuotientGroup.mk' N)⁆ ≤
          oddCoreOf (K.map (QuotientGroup.mk' N)) ⊓ oddCoreOf (J.map (QuotientGroup.mk' N))) :=
  E187C.omega4_quot_odd_of (fun hK => hΩ.exists_uniqueInvolution hp hq hK) hΩ.conjInvariant
    (fun hK hJ hKJ hzK hzJ => hΩ.comm_le_oddCore_of_twin hK hJ hKJ hzK hzJ)
    (fun hK hz => hΩ.center_two hp hq hK hz)
    hN hK hJ hne

theorem E187C.omega5_quot_odd_of
    (hzK : ∀ {K : Subgroup G}, K ∈ Ω → ∃ z : G, IsUniqueInvolution K z)
    (hc : ConjInvariant Ω)
    (h5 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → ∀ z : G, IsUniqueInvolution K z → ∀ v ∈ J,
      (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
        v ∈ Subgroup.normalizer (K : Set G))
    (hN : Odd (Nat.card N)) :
    ∀ L ∈ quotFamily Ω N, ∀ L' ∈ quotFamily Ω N, L ≠ L' → ∀ z : G ⧸ N, IsUniqueInvolution L z →
      ∀ v ∈ L', (¬ ∀ w ∈ L', v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
        v ∈ Subgroup.normalizer (L : Set (G ⧸ N)) := by
  rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne z' hz' _ ⟨v₀, hv₀J, rfl⟩ hvnc hv2 hcomm
  have hne0 : K.map (QuotientGroup.mk' N) ≠ J.map (QuotientGroup.mk' N) := hne
  obtain ⟨z, hz⟩ := hzK hK
  have hz'eq : z' = QuotientGroup.mk' N z :=
    hz'.eq (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hz)
  obtain ⟨v, hvJ, hvmk, hv2'⟩ :=
    exists_isPGroup_lift_of_mem_map (Subgroup.mem_map_of_mem _ hv₀J) hv2
  have hvnc' : ¬ ∀ w ∈ J, v * w = w * v := fun h => hvnc (by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hvmk, ← map_mul, ← map_mul, h w hw])
  have hvz : QuotientGroup.mk' N v * QuotientGroup.mk' N z =
      QuotientGroup.mk' N z * QuotientGroup.mk' N v := by
    rw [hvmk]
    exact hz'eq ▸ hcomm
  obtain ⟨n, hn, hfix⟩ := exists_fixed_conj_involution hN hz.sq hv2' (V := Subgroup.zpowers v)
    (fun u hu => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      rw [map_zpow]
      exact ((Commute.zpow_left (show Commute (QuotientGroup.mk' N v)
        (QuotientGroup.mk' N z) from hvz) k)).eq)
  have hnN : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  have hK₁ : conjSub n K ∈ Ω := hc n K hK
  have hz₁ : IsUniqueInvolution (conjSub n K) (n * z * n⁻¹) := hz.conj n
  have himg : (conjSub n K).map (QuotientGroup.mk' N) = K.map (QuotientGroup.mk' N) := by
    rw [AscQuot.map_conjSub, hnN, conjSub_one]
  have hK₁J : conjSub n K ≠ J := fun h => hne0 (by rw [← himg, h])
  have hvK₁ : v ∈ Subgroup.normalizer ((conjSub n K : Subgroup G) : Set G) :=
    h5 (conjSub n K) hK₁ J hJ hK₁J (n * z * n⁻¹) hz₁ v hvJ hvnc' hv2'
      (hfix v (Subgroup.mem_zpowers v))
  have := mk_mem_normalizer_map (N := N) hvK₁
  rw [himg, hvmk] at this
  exact this

theorem omega5_quot_odd (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hN : Odd (Nat.card N)) :
    ∀ L ∈ quotFamily Ω N, ∀ L' ∈ quotFamily Ω N, L ≠ L' → ∀ z : G ⧸ N, IsUniqueInvolution L z →
      ∀ v ∈ L', (¬ ∀ w ∈ L', v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
        v ∈ Subgroup.normalizer (L : Set (G ⧸ N)) :=
  E187C.omega5_quot_odd_of
    (fun hK => hΩ.exists_uniqueInvolution hp hq hK) hΩ.conjInvariant hΩ.omega5 hN

theorem classical_quot_odd (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hN : Odd (Nat.card N)) :
    ∀ L ∈ quotFamily Ω N, ∃ z : G ⧸ N, IsClassicalMember p f L z := by
  rintro _ ⟨K, hK, rfl⟩
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  have hz' := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hz
  obtain ⟨e⟩ := hΩ.nonempty_equiv_sl2 hK
  obtain ⟨e'⟩ := AscQuot.nonempty_quotOddCoreEquiv (odd_natCard_inf hN K)
  refine ⟨QuotientGroup.mk' N z, ?_⟩
  refine
    { orderOf_eq_two := orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one
      mem := hz'.mem
      perfect := ?_
      subnormal := ?_
      nonempty_equiv := ⟨e'.symm.trans e⟩ }
  · have : Group.IsPerfect ↥K := hΩ.isPerfect hK
    exact Group.IsPerfect.ofSurjective (AscQuot.quotRestrict_surjective K N)
  refine AscQuot.isSubnormal_centralizer ?_ ?_
  · rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul, hz.commute_of_mem hk]
  · intro c hc hne
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N c
    rw [← AscQuot.map_conjSub] at hne ⊢
    have hJ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
    obtain ⟨h4, h4'⟩ := omega4_quot_odd hp hq hΩ hN hK hJ (Ne.symm hne)
    have hzJ : QuotientGroup.mk' N z ∈ (conjSub g K).map (QuotientGroup.mk' N) := by
      have h1 : g * z * g⁻¹ ∈ conjSub g K := conj_mem_conjSub hz.mem
      refine ⟨g * z * g⁻¹, h1, ?_⟩
      rw [map_mul, map_mul, map_inv]
      rw [mul_inv_eq_iff_eq_mul]
      exact hc
    have hdvd : 2 ∣ Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓
        (conjSub g K).map (QuotientGroup.mk' N)) := by
      have := Subgroup.orderOf_dvd_natCard
        (K.map (QuotientGroup.mk' N) ⊓ (conjSub g K).map (QuotientGroup.mk' N))
        (x := QuotientGroup.mk' N z) ⟨hz'.mem, hzJ⟩
      rwa [orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one] at this
    have h1 := one_le_padicValNat_of_dvd Nat.card_pos.ne' hdvd
    exact (h4' (le_antisymm h4 h1)).trans inf_le_left

variable (p f) in
theorem oddQuotHyp : OddQuotHyp p f := by
  intro hp hq G _ _ Ω hΩ N _ hN
  refine
    { conjInvariant := AscQuot.conjInvariant_quot hΩ.conjInvariant N
      classical := classical_quot_odd hp hq hΩ hN
      omega4 := ?_
      omega5 := omega5_quot_odd hp hq hΩ hN }
  rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne
  exact omega4_quot_odd hp hq hΩ hN hK hJ hne

end Finite

end CFSG.ClassicalInvolution.Asc77
