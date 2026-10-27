module

public import CFSG.ClassicalInvolution.Q3.Q3DBExactConn
public import CFSG.ClassicalInvolution.Q3.Q3DBFuzzy
public import CFSG.ClassicalInvolution.Q3.Q3NFClosure

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3DB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open scoped MatrixGroups commutatorElement


section AutSL3

theorem autSL3_hom_central_involution_eq_one {R : Type*} [Group R] [Finite R] (hp : IsPGroup 2 R)
    (hR8 : Nat.card R = 8) {u : R} (hu1 : u ≠ 1) (hu2 : u * u = 1)
    (hu : ∀ x : R, x * x = 1 → x = 1 ∨ x = u) (ψ : R →* MulAut SL(2, ZMod 3)) : ψ u = 1 := by
  by_contra hψ
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hx1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hp) x
    have hk1 : 1 ≤ k := by
      by_contra h
      have h0 : k = 0 := by omega
      rw [h0, pow_zero, orderOf_eq_one_iff] at hk
      exact hx1 hk
    have hord : orderOf (x ^ (2 ^ (k - 1))) = 2 := by
      rw [orderOf_pow_of_dvd (by positivity) (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk]
      have : 2 ^ k = 2 * 2 ^ (k - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [this]
      exact Nat.mul_div_cancel _ (by positivity)
    have hy2 : x ^ (2 ^ (k - 1)) * x ^ (2 ^ (k - 1)) = 1 := by
      rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
    have hy1 : x ^ (2 ^ (k - 1)) ≠ 1 := by
      intro h; rw [h, orderOf_one] at hord; omega
    have hyu : x ^ (2 ^ (k - 1)) = u := (hu _ hy2).resolve_left hy1
    apply hψ
    rw [← hyu, map_pow, hx, one_pow]
  set π : MulAut SL(2, ZMod 3) →* MulAut SL(2, ZMod 3) ⧸ Q3T6.inn3 :=
    QuotientGroup.mk' Q3T6.inn3 with hπ
  set χ : R →* MulAut SL(2, ZMod 3) ⧸ Q3T6.inn3 := π.comp ψ with hχ
  set T : Subgroup R := χ.ker with hT
  have hTidx : T.index ≤ 2 := by
    rw [hT, Subgroup.index_ker]
    calc Nat.card χ.range ≤ Nat.card (MulAut SL(2, ZMod 3) ⧸ Q3T6.inn3) :=
          Subgroup.card_le_card_group _
      _ = Q3T6.inn3.index := (Subgroup.index_eq_card Q3T6.inn3).symm
      _ = 2 := Q3T6.inn3_index
  have hTcard : 4 ≤ Nat.card T := by
    have h := Subgroup.card_mul_index T
    rw [hR8] at h
    have hpos : 0 < T.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    interval_cases hi : T.index <;> omega
  have hTsq : ∀ x ∈ T, x * x = 1 := by
    intro x hx
    by_contra hx2
    have hψx : ψ x ∈ Q3T6.inn3 := by
      have : χ x = 1 := hx
      exact (QuotientGroup.eq_one_iff _).mp this
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hp) x
    have hk2 : 2 ≤ k := by
      by_contra h
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with h0 | h1
      · rw [h0, pow_zero, orderOf_eq_one_iff] at hk
        exact hx2 (by rw [hk, one_mul])
      · rw [h1, pow_one] at hk
        exact hx2 (by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hk]))
    have hord : orderOf (x ^ (2 ^ (k - 2))) = 4 := by
      rw [orderOf_pow_of_dvd (by positivity) (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk]
      have : 2 ^ k = 4 * 2 ^ (k - 2) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
      rw [this]
      exact Nat.mul_div_cancel _ (by positivity)
    have hmem : ψ (x ^ (2 ^ (k - 2))) ∈ Q3T6.inn3 := by
      rw [map_pow]; exact Subgroup.pow_mem _ hψx _
    have hord' : orderOf (ψ (x ^ (2 ^ (k - 2)))) = 4 := by
      rw [orderOf_injective ψ hinj, hord]
    exact Q3T6.orderOf_ne_four_of_mem_inn3 hmem hord'
  have hTle : T ≤ Subgroup.zpowers u := by
    intro x hx
    rcases hu x (hTsq x hx) with h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · rw [h1]; exact Subgroup.mem_zpowers u
  have hord2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have := Subgroup.card_le_of_le hTle
  rw [Nat.card_zpowers, hord2] at this
  omega

end AutSL3

section Edge

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem fuzzy_symm_of_mem_omegaNbr (hK : IsClassicalMember3 K z) {M N : Subgroup G}
    (hN : N ∈ omegaNbr (CoreAssembly.conjClass K) M) {a u : G} (ha : IsClassicalMember3 M a)
    (hu : IsClassicalMember3 N u) :
    conjSub u M = M ∧ ∀ x ∈ M, ⁅u, x⁆ ∈ oddCoreOf M := by
  obtain ⟨R, hRsyl, hR8, hRM⟩ := exists_sylow_of_mem_omegaNbr hK hN
  have hUN : IsUniqueInvolution N u :=
    (IsClassicalMemberU.ofQ3 hu).isUniqueInvolution (MemberType.cert_sl2 3 1)
  have huR : u ∈ R := mem_of_isSylow2In_of_isUniqueInvolution hUN hRsyl
  have huM : u ∈ Subgroup.normalizer (M : Set G) := hRM huR
  refine ⟨mem_normalizer_iff_conjSub_eq.mp huM, ?_⟩
  obtain ⟨e⟩ := ha.nonempty_equiv
  let ψ : ↥R →* MulAut SL(2, ZMod 3) :=
    (Q3T6.normalizerToAutSL3 e).comp (Subgroup.inclusion hRM)
  have hψ : ψ ⟨u, huR⟩ = 1 :=
    autSL3_hom_central_involution_eq_one hRsyl.2.1 hR8
      (fun h => hUN.ne_one (congrArg Subtype.val h)) (Subtype.ext hUN.sq)
      (fun x hx => by
        rcases hUN.unique x.1 (hRsyl.1 x.2) (by simpa using congrArg Subtype.val hx) with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h))
      ψ
  exact (Q3T6.normalizerToAutSL3_eq_one_iff e ⟨u, huM⟩).mp hψ

theorem oddCoreIn_exactCore3_le_exactLayer {Ω : Set (Subgroup G)} {a u : G} {N : Subgroup G}
    (hΩ : InClass3 Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers a))
    (hBelow : CIT3Below (Nat.card G)) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (hNtq : N ∈ tqMembers3 Ω a) (hu : IsClassicalMember3 N u) :
    oddCoreIn (exactCore3 a N) ≤ oddCoreIn (exactLayer3 Ω a) := by
  have hLie := lieSystemMod3_exactPair3 hΩ hc2 hBelow hnc
  obtain ⟨ι, -, ⟨D⟩⟩ := hLie
  set J := exactCore3 a N with hJ
  have hJm : J ∈ centralizingMembers (exactFamily3 Ω a) {a} :=
    ⟨exactCore3_mem_exactFamily3 hNtq, exactCore3_le_centralizer a N⟩
  have hJY : J ≤ exactLayer3 Ω a := le_centralizingLayer hJm
  have hmemΦ : (J.subgroupOf (exactLayer3 Ω a)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer3 Ω a))) ∈
      oddQuotientFamily (restrictFamily (centralizingMembers (exactFamily3 Ω a) {a})
        (exactLayer3 Ω a)) :=
    ⟨J.subgroupOf (exactLayer3 Ω a), ⟨J, hJm, hJY, rfl⟩, rfl⟩
  have h24 := D.card_eq _ hmemΦ
  have hOidx : (classicalInvolutionOddCore ↥J).index = 24 := by
    obtain ⟨e1⟩ := nonempty_equiv_exactCore3 hu hc2 hNtq.2
    obtain ⟨e2⟩ := hu.nonempty_equiv
    rw [Subgroup.index_eq_card, Nat.card_congr (e1.trans e2).toEquiv, natCard_sl2Three]
  set π : ↥(exactLayer3 Ω a) →* ↥(exactLayer3 Ω a) ⧸
    classicalInvolutionOddCore ↥(exactLayer3 Ω a) := QuotientGroup.mk' _ with hπ
  set φ : ↥J →* ↥(exactLayer3 Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer3 Ω a) :=
    π.comp (Subgroup.inclusion hJY) with hφ
  have hrange : φ.range = (J.subgroupOf (exactLayer3 Ω a)).map π := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
  set N' : Subgroup ↥J := φ.ker with hN'
  have hNmem : ∀ x : ↥J, x ∈ N' ↔
      ((Subgroup.inclusion hJY x : ↥(exactLayer3 Ω a))) ∈
        classicalInvolutionOddCore ↥(exactLayer3 Ω a) := by
    intro x
    rw [hN', MonoidHom.mem_ker]
    exact QuotientGroup.eq_one_iff _
  have hNidx : N'.index = 24 := by
    rw [Subgroup.index_eq_card, ← h24, ← hrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hNodd : Odd (Nat.card N') := by
    let θ : ↥N' →* ↥(classicalInvolutionOddCore ↥(exactLayer3 Ω a)) :=
      ((Subgroup.inclusion hJY).comp N'.subtype).codRestrict
        (classicalInvolutionOddCore ↥(exactLayer3 Ω a)) (fun x => (hNmem x.1).mp x.2)
    have hθ : Function.Injective θ := by
      intro x y hxy
      have : Subgroup.inclusion hJY x.1 = Subgroup.inclusion hJY y.1 :=
        congrArg Subtype.val hxy
      exact Subtype.ext (Subgroup.inclusion_injective hJY this)
    exact (CFSG.ComponentClassification.OddCore.odd_card ↥(exactLayer3 Ω a)).of_dvd_nat
      (Subgroup.card_dvd_of_injective θ hθ)
  have hNle : N' ≤ classicalInvolutionOddCore ↥J :=
    CFSG.ComponentClassification.OddCore.maximal ↥J N' inferInstance hNodd
  have hrel : N'.relIndex (classicalInvolutionOddCore ↥J) = 1 := by
    have h1 := Subgroup.relIndex_mul_index hNle
    rw [hNidx, hOidx] at h1
    omega
  have hON : classicalInvolutionOddCore ↥J ≤ N' := Subgroup.relIndex_eq_one.mp hrel
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨Subgroup.inclusion hJY x, (hNmem x).mp (hON hx), rfl⟩

theorem oddCoreIn_exactLayer3_le {Ω : Set (Subgroup G)} {a : G} (hΩ : InClass3 Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers a)) (hne : (tqMembers3 Ω a).Nonempty) :
    oddCoreIn (exactLayer3 Ω a) ≤ oddCoreIn (Subgroup.centralizer ({a} : Set G)) :=
  le_oddCoreIn_of_normalizes ((oddCoreIn_le _).trans (exactLayer3_le_centralizer Ω a))
    (fun _ hn => Balance.mem_normalizer_oddCoreIn_of_mem_normalizer
      (Q3NF.mem_normalizer_centralizingLayer_of_secData (secData3_exactFamily hΩ hc2 hne) hn))
    (odd_card_oddCoreIn _)

variable [IsSimpleGroup G]

theorem centralizer_inf_oddCoreIn_le_of_mem_omegaNbr (hnab : ∃ x y : G, x * y ≠ y * x)
    (hK : IsClassicalMember3 K z) (hint : IsIntrinsicU (.sl2 3 1) K z)
    (hBelow : CIT3Below (Nat.card G)) {M N : Subgroup G}
    (hN : N ∈ omegaNbr (CoreAssembly.conjClass K) M) {a u : G} (ha : IsClassicalMember3 M a)
    (hu : IsClassicalMember3 N u) :
    Subgroup.centralizer ({a} : Set G) ⊓ oddCoreIn N ≤
      oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
  have hΩ : InClass3 (CoreAssembly.conjClass K) := inClass3_conjugates hK
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ha.orderOf_eq_two]
    norm_num
  have hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G :=
    Q3W.not_subset_center_of_ne_one hnab ha.ne_one
  have hNtq := mem_tqMembers3_of_mem_omegaNbr hK hint hN ha
  have h1 := oddCoreIn_exactCore3_le_exactLayer hΩ hc2 hBelow hnc hNtq hu
  have h2 := oddCoreIn_exactLayer3_le hΩ hc2 ⟨N, hNtq⟩
  have h3 := oddCoreIn_exactCore3 hu hc2 hNtq.2
  intro x hx
  have hx' := Subgroup.mem_inf.mp hx
  have hxN : x ∈ N := oddCoreIn_le N hx'.2
  refine h2 (h1 ?_)
  rw [h3]
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxN, hx'.1⟩, hx'.2⟩

theorem eq_mul_of_mem_omegaNbr (hK : IsClassicalMember3 K z) (hint : IsIntrinsicU (.sl2 3 1) K z)
    {M N : Subgroup G} (hN : N ∈ omegaNbr (CoreAssembly.conjClass K) M) {a u : G}
    (ha : IsClassicalMember3 M a) (hu : IsClassicalMember3 N u) :
    ∀ x ∈ N, ∃ i ∈ N ⊓ Subgroup.centralizer ({a} : Set G), ∃ n ∈ oddCoreIn N, x = i * n := by
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ha.orderOf_eq_two]
    norm_num
  exact exactCore3_cover hu hc2 (mem_tqMembers3_of_mem_omegaNbr hK hint hN ha).2

theorem oddCoreIn_le_oddCoreIn_centralizer_iff (hnab : ∃ x y : G, x * y ≠ y * x)
    (hK : IsClassicalMember3 K z) (hint : IsIntrinsicU (.sl2 3 1) K z)
    (hBelow : CIT3Below (Nat.card G)) {M N : Subgroup G}
    (hN : N ∈ omegaNbr (CoreAssembly.conjClass K) M) {a u : G} (ha : IsClassicalMember3 M a)
    (hu : IsClassicalMember3 N u) :
    oddCoreIn N ≤ oddCoreIn (Subgroup.centralizer ({a} : Set G)) ↔
      ∀ x ∈ oddCoreIn N, a * x = x * a := by
  constructor
  · intro h x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (oddCoreIn_le _ (h hx))).symm
  · intro h x hx
    exact centralizer_inf_oddCoreIn_le_of_mem_omegaNbr hnab hK hint hBelow hN ha hu
      (Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr (h x hx).symm, hx⟩)

theorem oddCoreIn_le_oddCoreIn_iff (hnab : ∃ x y : G, x * y ≠ y * x)
    (hK : IsClassicalMember3 K z) (hint : IsIntrinsicU (.sl2 3 1) K z)
    (hBelow : CIT3Below (Nat.card G)) {M N : Subgroup G} (hM : M ∈ CoreAssembly.conjClass K)
    (hN : N ∈ omegaNbr (CoreAssembly.conjClass K) M) {a u : G} (ha : IsClassicalMember3 M a)
    (hu : IsClassicalMember3 N u) :
    oddCoreIn N ≤ oddCoreIn M ↔ ∀ x ∈ oddCoreIn N, a * x = x * a := by
  have hint' : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K :=
    hint (MemberType.isSolvableType_sl2.mpr (by norm_num))
  have hintM := oddCoreIn_centralizer_le_of_mem_conjClass hK hint' hM ha
  rw [oddCoreIn_eq_of_intrinsic3 ha hintM]
  exact oddCoreIn_le_oddCoreIn_centralizer_iff hnab hK hint hBelow hN ha hu

end Edge

end CFSG.ClassicalInvolution.Q3.Q3DB
