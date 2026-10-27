module

public import CFSG.ClassicalInvolution.Q3.TL3T22
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotGen
public import CFSG.ClassicalInvolution.Asc77.AscFusionR7
public import CFSG.ClassicalInvolution.Asc77.WP2Branch
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CLNine3
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Comp
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Main
public import CFSG.ClassicalInvolution.Q3.Q3T7T2Main
public import CFSG.ClassicalInvolution.Q3.Q3T8Std8
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.ClassicalInvolution.Uniform.U3IH8
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QTOutChar

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Rigid

variable (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {Z : Subgroup G}
  (hZc : Z ≤ Subgroup.center G) (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥)
include hΩ h2 hZc hZK

theorem eq_of_mem_sup_center {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {a : G} (haK : a ∈ K)
    (ha2 : a * a ≠ 1) {j c : G} (hj : j ∈ J) (hc : c ∈ Z) (hjc : a = j * c) : K = J := by
  by_contra hKJ
  have hcz : ∀ x : G, c * x = x * c := fun x => (Subgroup.mem_center_iff.mp (hZc hc) x).symm
  have hpow : ∀ k : ℕ, a ^ k = j ^ k * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, hjc, pow_succ, pow_succ]
      have h1 : c ^ k * j = j * c ^ k := (Commute.pow_left (hcz j) k)
      calc j ^ k * c ^ k * (j * c) = j ^ k * (c ^ k * j) * c := by group
        _ = j ^ k * (j * c ^ k) * c := by rw [h1]
        _ = j ^ k * j * (c ^ k * c) := by group
  have hiff : ∀ k : ℕ, j ^ k = 1 → a ^ k = 1 := by
    intro k hk
    have h1 : a ^ k = c ^ k := by rw [hpow, hk, one_mul]
    have h2' : a ^ k ∈ Z ⊓ K := ⟨h1 ▸ Z.pow_mem hc k, K.pow_mem haK k⟩
    rw [hZK K hK, Subgroup.mem_bot] at h2'
    exact h2'
  obtain ⟨⟨zK, hzK⟩, -⟩ := hΩ.omega1 K hK
  obtain ⟨⟨t, ht⟩, -⟩ := hΩ.omega1 J hJ
  have hj2 : j * j ≠ 1 := by
    intro h
    apply ha2
    have := hiff 2 (by rw [pow_two]; exact h)
    rwa [pow_two] at this
  obtain ⟨m, hm⟩ : ∃ m : ℕ, orderOf j = 2 ^ (m + 1) := by
    have hJ2 := h2 J hJ
    obtain ⟨k, hk⟩ := hJ2 ⟨j, hj⟩
    have hdvd : orderOf j ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hi0 : i ≠ 0 := by
      intro h0
      rw [h0, pow_zero, orderOf_eq_one_iff] at hi
      apply hj2
      rw [hi, one_mul]
    exact ⟨i - 1, by rw [hi]; congr 1; omega⟩
  have hjm : j ^ 2 ^ m ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (pow_pos (by norm_num) m) h
    rw [hm, pow_succ] at this
    have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m
    omega
  have hjm2 : j ^ 2 ^ m * j ^ 2 ^ m = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hm, pow_orderOf_eq_one]
  have hjt : j ^ 2 ^ m = t :=
    (ht.unique _ (J.pow_mem hj _) hjm2).resolve_left hjm
  have ham : a ^ 2 ^ m ≠ 1 := by
    intro h
    rw [hpow] at h
    apply hjm
    have h3 : j ^ 2 ^ m = (c ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h
    have h4 : j ^ 2 ^ m ∈ Z ⊓ J := ⟨h3 ▸ Z.inv_mem (Z.pow_mem hc _), J.pow_mem hj _⟩
    rw [hZK J hJ, Subgroup.mem_bot] at h4
    exact h4
  have ham2 : a ^ 2 ^ m * a ^ 2 ^ m = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    have h5 : j ^ 2 ^ (m + 1) = 1 := by rw [← hm, pow_orderOf_eq_one]
    exact hiff _ h5
  have haz : a ^ 2 ^ m = zK := (hzK.unique _ (K.pow_mem haK _) ham2).resolve_left ham
  have hzt : zK = t * c ^ 2 ^ m := by rw [← haz, hpow, hjt]
  have hcm : c ^ 2 ^ m ∈ Z := Z.pow_mem hc _
  have hKt : ∀ k ∈ K, k * t = t * k := by
    intro k hk
    have ht' : t = zK * (c ^ 2 ^ m)⁻¹ := by rw [hzt]; group
    have hc1 : k * zK = zK * k := isUniqueInvolution_comm hzK hk
    have hc2 : k * (c ^ 2 ^ m)⁻¹ = (c ^ 2 ^ m)⁻¹ * k :=
      Subgroup.mem_center_iff.mp (hZc (Z.inv_mem hcm)) k
    calc k * t = k * zK * (c ^ 2 ^ m)⁻¹ := by rw [ht', mul_assoc]
      _ = zK * (k * (c ^ 2 ^ m)⁻¹) := by rw [hc1, mul_assoc]
      _ = zK * ((c ^ 2 ^ m)⁻¹ * k) := by rw [hc2]
      _ = t * k := by rw [ht', mul_assoc]
  have hJz : ∀ x ∈ J, x * zK = zK * x := by
    intro x hx
    have hc1 : x * t = t * x := isUniqueInvolution_comm ht hx
    have hc2 : x * c ^ 2 ^ m = c ^ 2 ^ m * x := Subgroup.mem_center_iff.mp (hZc hcm) x
    calc x * zK = x * t * c ^ 2 ^ m := by rw [hzt, mul_assoc]
      _ = t * (x * c ^ 2 ^ m) := by rw [hc1, mul_assoc]
      _ = t * (c ^ 2 ^ m * x) := by rw [hc2]
      _ = zK * x := by rw [hzt, mul_assoc]
  have hKN : K ≤ Subgroup.normalizer (J : Set G) := by
    intro k hk
    by_cases hc' : ∀ w ∈ K, k * w = w * k
    · have hq : IsQuatSub K := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isPGroup hK (h2 K hK))
      rcases hzK.unique k hk (hq.sq_eq_one_of_central hk hc') with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h, hzt]
        exact Subgroup.mul_mem _ (Subgroup.le_normalizer ht.mem)
          (Subgroup.mem_normalizer_iff.mpr fun x => by
            rw [show c ^ 2 ^ m * x * (c ^ 2 ^ m)⁻¹ = x by
              rw [(Subgroup.mem_center_iff.mp (hZc hcm) x).symm]; group])
    · exact hΩ.omega5 J hJ K hK (Ne.symm hKJ) t ht k hk hc'
        ((h2 K hK).to_le (Subgroup.zpowers_le.mpr hk)) (hKt k hk)
  have hJN : J ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    by_cases hc' : ∀ w ∈ J, x * w = w * x
    · have hq : IsQuatSub J := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isPGroup hJ (h2 J hJ))
      rcases ht.unique x hx (hq.sq_eq_one_of_central hx hc') with h | h
      · rw [h]; exact Subgroup.one_mem _
      · have ht' : t = zK * (c ^ 2 ^ m)⁻¹ := by rw [hzt]; group
        rw [h, ht']
        exact Subgroup.mul_mem _ (Subgroup.le_normalizer hzK.mem)
          (Subgroup.mem_normalizer_iff.mpr fun y => by
            rw [show (c ^ 2 ^ m)⁻¹ * y * (c ^ 2 ^ m)⁻¹⁻¹ = y by
              rw [(Subgroup.mem_center_iff.mp (hZc (Z.inv_mem hcm)) y).symm]; group])
    · exact hΩ.omega5 K hK J hJ hKJ zK hzK x hx hc'
        ((h2 J hJ).to_le (Subgroup.zpowers_le.mpr hx)) (hJz x hx)
  have hP2 : IsPGroup 2 ↥(J ⊔ K) := (h2 J hJ).to_sup_of_normal_right' (h2 K hK) hJN
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  have hcomm : ∀ x ∈ K, ∀ y ∈ J, x * y = y * x :=
    Q3CP.l67Gen G Ω hΩ S K (mem_RSet_of_isPGroup hK (h2 K hK)) J
      (mem_RSet_of_isPGroup hJ (h2 J hJ)) (le_sup_right.trans hPS) (le_sup_left.trans hPS) hKJ
  have hjc : ∀ w ∈ J, j * w = w * j := by
    intro w hw
    have h1 := hcomm a haK w hw
    rw [hjc] at h1
    calc j * w = j * c * w * c⁻¹ := by rw [mul_assoc j c w, hcz w]; group
      _ = w * (j * c) * c⁻¹ := by rw [h1]
      _ = w * j := by group
  have hq : IsQuatSub J := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isPGroup hJ (h2 J hJ))
  exact hj2 (hq.sq_eq_one_of_central hj hjc)

theorem eq_of_map_eq [Z.Normal] {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : K.map (QuotientGroup.mk' Z) = J.map (QuotientGroup.mk' Z)) : K = J := by
  have hq : IsQuatSub K := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isPGroup hK (h2 K hK))
  obtain ⟨a, haK, ha4⟩ := hq.exists_orderOf_four
  have ha2 : a * a ≠ 1 := by
    intro h1
    have hd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
    rw [ha4] at hd
    norm_num at hd
  have hmem : QuotientGroup.mk' Z a ∈ J.map (QuotientGroup.mk' Z) := h ▸ ⟨a, haK, rfl⟩
  obtain ⟨j, hj, hja⟩ := hmem
  have hc : j⁻¹ * a ∈ Z := by
    rw [← QuotientGroup.eq]
    exact hja
  exact eq_of_mem_sup_center hΩ h2 hZc hZK hK hJ haK ha2 hj hc (by group)

omit h2 hZc hZK in
theorem exists_of_mem_USet {U : Subgroup G} (hU : U ∈ USet Ω) :
    ∃ K ∈ Ω, U ≤ K ∧ ∃ u ∈ U, u * u ≠ 1 ∧ Subgroup.zpowers u = U := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨K, hK, hRK, -, -⟩ := mem_RSet_iff.mp hR
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥U)
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR
  have h1 := Subgroup.relIndex_mul_card U R
  rw [inf_eq_left.mpr hUR, hidx] at h1
  have hU4 : 4 ≤ Nat.card U := by omega
  have hzp : Subgroup.zpowers (g : G) = U := by
    apply le_antisymm (Subgroup.zpowers_le.mpr g.2)
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
      have := congrArg Subtype.val hk
      simpa using this⟩
  refine ⟨K, hK, hUR.trans hRK, g, g.2, fun hgg => ?_, hzp⟩
  have hord : orderOf (g : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hgg)
  have hcard : Nat.card U = orderOf (g : G) := by
    have := Nat.card_zpowers (g : G)
    rwa [hzp] at this
  have := Nat.le_of_dvd (by norm_num) hord
  omega

theorem eq_of_map_eq_of_mem_USet [Z.Normal] {U U' : Subgroup G} (hU : U ∈ USet Ω)
    (hU' : U' ∈ USet Ω) (h : U.map (QuotientGroup.mk' Z) = U'.map (QuotientGroup.mk' Z)) :
    U = U' := by
  have key : ∀ {A B : Subgroup G}, A ∈ USet Ω → B ∈ USet Ω →
      A.map (QuotientGroup.mk' Z) = B.map (QuotientGroup.mk' Z) → A ≤ B := by
    intro A B hA hB hAB
    obtain ⟨K, hK, hAK, a, haA, ha2, -⟩ := exists_of_mem_USet hΩ hA
    obtain ⟨K', hK', hBK', -, -, -, -⟩ := exists_of_mem_USet hΩ hB
    have hmem : ∀ {x : G}, x ∈ A → ∃ y ∈ B, y⁻¹ * x ∈ Z := by
      intro x hx
      have : QuotientGroup.mk' Z x ∈ B.map (QuotientGroup.mk' Z) := hAB ▸ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := this
      exact ⟨y, hy, by rw [← QuotientGroup.eq]; exact hyx⟩
    obtain ⟨b, hb, hba⟩ := hmem haA
    have hKK' : K = K' :=
      eq_of_mem_sup_center hΩ h2 hZc hZK hK hK' (hAK haA) ha2 (hBK' hb) hba (by group)
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hmem hx
    have hyK : y⁻¹ * x ∈ K := K.mul_mem (K.inv_mem (hKK' ▸ hBK' hy)) (hAK hx)
    have h1 : y⁻¹ * x ∈ Z ⊓ K := ⟨hyx, hyK⟩
    rw [hZK K hK, Subgroup.mem_bot] at h1
    have : x = y := by
      calc x = y * (y⁻¹ * x) := by group
        _ = y := by rw [h1, mul_one]
    rw [this]
    exact hy
  exact le_antisymm (key hU hU' h) (key hU' hU h.symm)

end Rigid

section Quot

local notation "πc" => QuotientGroup.mk' (Subgroup.center G)

omit [Finite G] in
theorem isPGroup_center_of_oddCore [Finite G] (hO : classicalInvolutionOddCore G = ⊥) :
    IsPGroup 2 ↥(Subgroup.center G) := by
  rw [IsPGroup.iff_orderOf]
  intro x
  obtain ⟨a, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  set y : G := (x : G) ^ 2 ^ a with hy
  have hyc : y ∈ Subgroup.center G := (Subgroup.center G).pow_mem x.2 _
  have hyo : orderOf y = m := by
    rw [hy, orderOf_pow' _ (pow_ne_zero _ (by norm_num)), Subgroup.orderOf_coe, hom,
      Nat.gcd_comm, Nat.gcd_mul_right_right]
    exact Nat.mul_div_cancel_left m (by positivity)
  have hN : (Subgroup.zpowers y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hyc hn) g]
    simpa using hn
  have hle : Subgroup.zpowers y ≤ classicalInvolutionOddCore G :=
    le_sSup ⟨hN, by rw [Nat.card_zpowers, hyo]; exact hm⟩
  rw [hO, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  rw [hle, orderOf_one] at hyo
  refine ⟨a, ?_⟩
  rw [hom, ← hyo, mul_one]

omit [Finite G] in
theorem orderOf_mk_eq {Z L : Subgroup G} [Z.Normal] (hZL : Z ⊓ L = ⊥) {u : G} (hu : u ∈ L) :
    orderOf (QuotientGroup.mk' Z u) = orderOf u := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  constructor
  · intro h
    rw [← map_pow, ← map_one (QuotientGroup.mk' Z)] at h
    have h1 : (u ^ n)⁻¹ * 1 ∈ Z := QuotientGroup.eq.mp h
    have h2 : u ^ n ∈ Z ⊓ L := ⟨by simpa using Z.inv_mem h1, L.pow_mem hu n⟩
    rw [hZL, Subgroup.mem_bot] at h2
    exact h2
  · intro h
    rw [← map_pow, h, map_one]

variable {r : ℕ}

abbrev quotFam (Ω : Set (Subgroup G)) : Set (Subgroup (G ⧸ Subgroup.center G)) :=
  (fun K : Subgroup G => K.map πc) '' Ω

theorem aEmpty_quot (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    (hΩ' : HypOmegaGen (quotFam Ω)) {K : Subgroup G} (hK : K ∈ Ω) :
    AEmpty (quotFam Ω) (K.map πc) := by
  have h2' : ∀ J ∈ quotFam Ω, IsPGroup 2 J := by
    rintro _ ⟨J, hJ, rfl⟩
    exact (hD.two J hJ).map _
  have hodd : ∀ L ∈ Ω, Odd (Nat.card ↥(Subgroup.center G ⊓ L)) := fun L hL => by
    rw [hZK L hL, Subgroup.card_bot]; exact odd_one
  intro J' hJ'star hJ'nbr zK' zJ' hzK' hzJ'
  obtain ⟨hJ'Ω, hne, U', hU', hU'J, hU'N⟩ := hJ'star
  obtain ⟨J, hJ, rfl⟩ := hJ'Ω
  beta_reduce at hJ'nbr hzJ' hne hU'J ⊢
  have hJK : J ≠ K := fun h => hne (by rw [h])
  obtain ⟨L', hL', hU'L', u', hu'U', hu'2, hzp'⟩ := exists_of_mem_USet hΩ' hU'
  obtain ⟨L, hL, rfl⟩ := hL'
  beta_reduce at hU'L'
  obtain ⟨u, huL, rfl⟩ := hU'L' hu'U'
  have hu2 : u * u ≠ 1 := fun h => hu'2 (by rw [← map_mul, h, map_one])
  set U := Subgroup.zpowers u with hUdef
  have hUmap : U.map πc = U' := by rw [hUdef, MonoidHom.map_zpowers, hzp']
  have hUL : U ≤ L := Subgroup.zpowers_le.mpr huL
  have hU : U ∈ USet Ω := by
    refine ⟨L, mem_RSet_of_isPGroup hL (hD.two L hL), hUL, inferInstance, ?_⟩
    obtain ⟨R', hR', hU'R', -, hidx'⟩ := hU'
    obtain ⟨L'', hL'', hR'L'', -, hmax'⟩ := mem_RSet_iff.mp hR'
    obtain ⟨L₂, hL₂, rfl⟩ := hL''
    beta_reduce at hR'L'' hmax'
    have hL₂2 : IsPGroup 2 ↥(L₂.map πc) := (hD.two L₂ hL₂).map _
    have hR'eq : L₂.map πc = R' := hmax' _ le_rfl hL₂2 hR'L''
    have hcardL : ∀ {M : Subgroup G}, M ∈ Ω → Nat.card ↥(M.map πc) = Nat.card M := by
      intro M hM
      have hinj := TwistQ.subgroupMap_injective (N := Subgroup.center G)
        (show M ⊓ Subgroup.center G = ⊥ by rw [inf_comm]; exact hZK M hM)
      exact (Nat.card_eq_of_bijective _ ⟨hinj, MonoidHom.subgroupMap_surjective πc M⟩).symm
    have hcU : Nat.card U = Nat.card U' := by
      rw [← hzp', Nat.card_zpowers, Nat.card_zpowers, orderOf_mk_eq (hZK L hL) huL]
    have h1 := Subgroup.relIndex_mul_card U' R'
    rw [inf_eq_left.mpr hU'R', hidx', ← hR'eq, hcardL hL₂, hD.card L₂ hL₂] at h1
    have h3 := Subgroup.relIndex_mul_card U L
    rw [inf_eq_left.mpr hUL, hcU, hD.card L hL] at h3
    have hpos : 0 < Nat.card U' := Nat.card_pos
    have h4 : U.relIndex L * Nat.card U' = 2 * Nat.card U' := by rw [h3, h1]
    exact Nat.eq_of_mul_eq_mul_right hpos h4
  have hLJ : L = J := by
    obtain ⟨j, hj, hju⟩ := hU'J hu'U'
    have hc : j⁻¹ * u ∈ Subgroup.center G := by
      rw [← QuotientGroup.eq]
      exact hju
    exact eq_of_mem_sup_center hD.hyp hD.two le_rfl hZK hL hJ huL hu2 hj hc (by group)
  subst hLJ
  have hUN : U ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    have hx' : πc x ∈ U' := hUmap ▸ ⟨x, hx, rfl⟩
    have h1 := (mem_normalizer_iff_conjSub_eq).mp (hU'N hx')
    rw [← TwistQ.conjSub_map] at h1
    exact (mem_normalizer_iff_conjSub_eq).mpr
      (eq_of_map_eq hD.hyp hD.two le_rfl hZK (hD.hyp.conjInvariant x K hK) hK h1)
  have hstar : L ∈ omegaStarNbr Ω K := ⟨hJ, hJK, U, hU, hUL, hUN⟩
  have hnbr : L ∉ omegaNbr Ω K := by
    intro h
    apply hJ'nbr
    obtain ⟨-, -, hLN⟩ := (TC.mem_omegaNbr_iff hD.hyp hD.two).mp h
    refine (TC.mem_omegaNbr_iff hΩ' h2').mpr ⟨⟨L, hJ, rfl⟩, hne, ?_⟩
    exact (Subgroup.map_mono hLN).trans (Subgroup.le_normalizer_map πc)
  obtain ⟨⟨zK, hzK⟩, -⟩ := hD.hyp.omega1 K hK
  obtain ⟨⟨zJ, hzJ⟩, -⟩ := hD.hyp.omega1 L hJ
  have hzK'' := isUniqueInvolution_map_mk_of_odd (hodd K hK) hzK
  have hzJ'' := isUniqueInvolution_map_mk_of_odd (hodd L hJ) hzJ
  rw [hzK'.eq hzK'', hzJ'.eq hzJ'']
  obtain ⟨g, hg, hgK⟩ := hD.aEmpty K hK L hstar hnbr zK zJ hzK hzJ
  refine ⟨πc g, ?_, by rw [← TwistQ.conjSub_map, hgK]⟩
  have hC : (Subgroup.closure ({zK, zJ} : Set G)).map πc =
      Subgroup.closure ({πc zK, πc zJ} : Set (G ⧸ Subgroup.center G)) := by
    rw [MonoidHom.map_closure, Set.image_pair]
  have hle : (pairNormalizers K L zK zJ).map πc ≤
      pairNormalizers (K.map πc) (L.map πc) (πc zK) (πc zJ) := by
    unfold pairNormalizers
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · refine (Subgroup.map_inf_le _ _ _).trans (inf_le_inf_left _ ?_)
      rw [← hC]
      exact Subgroup.le_normalizer_map πc
    · refine (Subgroup.map_inf_le _ _ _).trans (inf_le_inf_left _ ?_)
      rw [← hC]
      exact Subgroup.le_normalizer_map πc
  exact hle ⟨g, hg, rfl⟩

theorem thmDHyp_quot (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥) :
    ThmDHyp r (quotFam Ω) := by
  have hodd : ∀ L ∈ Ω, Odd (Nat.card ↥(Subgroup.center G ⊓ L)) := fun L hL => by
    rw [hZK L hL, Subgroup.card_bot]; exact odd_one
  have hΩ' : HypOmegaGen (quotFam Ω) :=
    PhilipHall.QuaternionBridge.CentQ.quotient_hypOmegaGen hD.hyp (Subgroup.center G) le_rfl hodd
  have hsurj := QuotientGroup.mk'_surjective (Subgroup.center G)
  refine ⟨hΩ', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨J, hJ, rfl⟩
    exact (hD.two J hJ).map _
  · rintro _ ⟨M, hM, rfl⟩
    have hinj := TwistQ.subgroupMap_injective (N := Subgroup.center G)
      (show M ⊓ Subgroup.center G = ⊥ by rw [inf_comm]; exact hZK M hM)
    rw [← hD.card M hM]
    exact (Nat.card_eq_of_bijective _
      ⟨hinj, MonoidHom.subgroupMap_surjective πc M⟩).symm
  · rintro _ ⟨K, hK, rfl⟩
    exact aEmpty_quot hD hZK hΩ' hK
  · rw [eq_top_iff, ← Subgroup.map_top_of_surjective _ hsurj, ← hD.gen,
      Subgroup.map_le_iff_le_comap]
    refine pSpan_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_pSpan ⟨K, hK, rfl⟩
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨L, hL, rfl⟩
    obtain ⟨g, hg⟩ := hD.trans K hK L hL
    exact ⟨πc g, by rw [← TwistQ.conjSub_map, hg]⟩
  · exact TwistQ.oddFree le_rfl (isPGroup_center_of_oddCore hD.odd) hD.odd
  · rintro _ ⟨L, hL, rfl⟩ ū hū
    obtain ⟨⟨u, hu⟩, -⟩ := hD.hyp.omega1 L hL
    have hū' := isUniqueInvolution_map_mk_of_odd (hodd L hL) hu
    rw [hū.eq hū']
    obtain ⟨Q, hQn, hQ2, huQ⟩ := hD.inO2 L hL u hu
    exact ⟨Q.map πc, hQn.map _ hsurj,
      hQ2.map _, ⟨u, huQ, rfl⟩⟩

omit [Finite G] in
theorem card_map_mk_eq {Z M : Subgroup G} [Z.Normal] (hM : Z ⊓ M = ⊥) :
    Nat.card ↥(M.map (QuotientGroup.mk' Z)) = Nat.card M := by
  have hinj := TwistQ.subgroupMap_injective (N := Z)
    (show M ⊓ Z = ⊥ by rw [inf_comm]; exact hM)
  exact (Nat.card_eq_of_bijective _ ⟨hinj, (QuotientGroup.mk' Z).subgroupMap_surjective M⟩).symm

omit [Finite G] in
theorem le_member_of_mem_USet (hD : ThmDHyp r Ω) {U : Subgroup G} (hU : U ∈ USet Ω) :
    ∃ L ∈ Ω, U ≤ L ∧ U.relIndex L = 2 ∧ IsCyclic ↥U := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨L, hL, hRL, -, hmax⟩ := mem_RSet_iff.mp hR
  have hRe : L = R := hmax L le_rfl (hD.two L hL) hRL
  subst hRe
  exact ⟨L, hL, hUR, hidx, hcyc⟩

theorem map_mem_USet_quot (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    {U : Subgroup G} (hU : U ∈ USet Ω) :
    U.map πc ∈ USet (quotFam Ω) := by
  obtain ⟨L, hL, hUL, hidx, hcyc⟩ := le_member_of_mem_USet hD hU
  refine ⟨L.map πc,
    mem_RSet_of_isPGroup ⟨L, hL, rfl⟩ ((hD.two L hL).map _), Subgroup.map_mono hUL,
    isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective πc U),
    ?_⟩
  have hUZ : Subgroup.center G ⊓ U = ⊥ := eq_bot_iff.mpr ((inf_le_inf_left _ hUL).trans
    (hZK L hL).le)
  have h1 := Subgroup.relIndex_mul_card (U.map πc)
    (L.map πc)
  rw [inf_eq_left.mpr (Subgroup.map_mono hUL), card_map_mk_eq hUZ, card_map_mk_eq (hZK L hL)]
    at h1
  have h3 := Subgroup.relIndex_mul_card U L
  rw [inf_eq_left.mpr hUL, hidx] at h3
  have hpos : 0 < Nat.card U := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h3.symm)

theorem le_of_map_le_of_mem_USet (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    {U J : Subgroup G} (hU : U ∈ USet Ω) (hJ : J ∈ Ω)
    (h : U.map πc ≤
      J.map πc) : U ≤ J := by
  obtain ⟨K, hK, hUK, u, huU, hu2, -⟩ := exists_of_mem_USet hD.hyp hU
  obtain ⟨j, hj, hju⟩ := h ⟨u, huU, rfl⟩
  have hc : j⁻¹ * u ∈ Subgroup.center G := by
    rw [← QuotientGroup.eq]
    exact hju
  have hKJ := eq_of_mem_sup_center hD.hyp hD.two le_rfl hZK hK hJ (hUK huU) hu2 hj hc (by group)
  exact hKJ ▸ hUK

theorem exists_lift_USet_quot (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    (hΩ' : HypOmegaGen (quotFam Ω)) {V : Subgroup (G ⧸ Subgroup.center G)}
    (hV : V ∈ USet (quotFam Ω)) {S : Subgroup G} (hZS : Subgroup.center G ≤ S)
    (hVS : V ≤ S.map πc) :
    ∃ U ∈ USet Ω, U ≤ S ∧ U.map πc = V := by
  obtain ⟨L', hL', hVL', v', hv'V, hv'2, hzp'⟩ := exists_of_mem_USet hΩ' hV
  obtain ⟨L, hL, rfl⟩ := hL'
  obtain ⟨u, huL, rfl⟩ := hVL' hv'V
  have hu2 : u * u ≠ 1 := fun h => hv'2 (by rw [← map_mul, h, map_one])
  have hUL : Subgroup.zpowers u ≤ L := Subgroup.zpowers_le.mpr huL
  have hmap : (Subgroup.zpowers u).map πc = V := by
    rw [MonoidHom.map_zpowers, hzp']
  refine ⟨Subgroup.zpowers u, ?_, ?_, hmap⟩
  · refine ⟨L, mem_RSet_of_isPGroup hL (hD.two L hL), hUL, inferInstance, ?_⟩
    obtain ⟨-, -, hidx', hcyc'⟩ := le_member_of_mem_USet (thmDHyp_quot hD hZK) hV
    obtain ⟨R', hR', hVR', -, hidx⟩ := hV
    obtain ⟨L₂', hL₂', hR'L₂', -, hmax'⟩ := mem_RSet_iff.mp hR'
    obtain ⟨L₂, hL₂, rfl⟩ := hL₂'
    beta_reduce at hR'L₂' hmax'
    have hR'eq : L₂.map πc = R' :=
      hmax' _ le_rfl ((hD.two L₂ hL₂).map _) hR'L₂'
    have hUZ : Subgroup.center G ⊓ Subgroup.zpowers u = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_left _ hUL).trans (hZK L hL).le)
    have h1 := Subgroup.relIndex_mul_card V R'
    rw [inf_eq_left.mpr hVR', hidx, ← hR'eq, card_map_mk_eq (hZK L₂ hL₂), hD.card L₂ hL₂,
      ← hmap, card_map_mk_eq hUZ] at h1
    have h3 := Subgroup.relIndex_mul_card (Subgroup.zpowers u) L
    rw [inf_eq_left.mpr hUL, hD.card L hL] at h3
    have hpos : 0 < Nat.card ↥(Subgroup.zpowers u) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h3.trans h1.symm)
  · have hu' : πc u ∈
        S.map πc := hVS hv'V
    obtain ⟨s', hs', hsu⟩ := hu'
    have hc : s'⁻¹ * u ∈ Subgroup.center G := by
      rw [← QuotientGroup.eq]
      exact hsu
    have huS : u ∈ S := by
      have : u = s' * (s'⁻¹ * u) := by group
      rw [this]
      exact S.mul_mem hs' (hZS hc)
    exact Subgroup.zpowers_le.mpr huS

theorem map_mem_etaG_quot (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    {η : Set (Subgroup G)} (hη : η ∈ etaG Ω) :
    (fun U : Subgroup G => U.map πc) '' η ∈
      etaG (quotFam Ω) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj := QuotientGroup.mk'_surjective (Subgroup.center G)
  have hΩ' := (thmDHyp_quot hD hZK).hyp
  obtain ⟨S, ⟨hηsub, hηd, hηmax⟩, hinv⟩ := hη
  have hZS : Subgroup.center G ≤ S := (isPGroup_center_of_oddCore hD.odd).le_sylow_of_normal S
  have hinj : ∀ {U U' : Subgroup G}, U ∈ USet Ω → U' ∈ USet Ω →
      U.map πc =
        U'.map πc → U = U' :=
    fun hU hU' h => eq_of_map_eq_of_mem_USet hD.hyp hD.two le_rfl hZK hU hU' h
  refine ⟨S.mapSurjective hsurj, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨U, hU, rfl⟩
    rw [Sylow.coe_mapSurjective]
    exact ⟨map_mem_USet_quot hD hZK (hηsub hU).1, Subgroup.map_mono (hηsub hU).2⟩
  · rintro _ ⟨U, hU, rfl⟩ _ ⟨U', hU', rfl⟩ hne J' hJ' ⟨h1, h2⟩
    obtain ⟨J, hJ, rfl⟩ := hJ'
    have hUU' : U ≠ U' := fun h => hne (by rw [h])
    exact hηd U hU U' hU' hUU' J hJ ⟨le_of_map_le_of_mem_USet hD hZK (hηsub hU).1 hJ h1,
      le_of_map_le_of_mem_USet hD hZK (hηsub hU').1 hJ h2⟩
  · intro η' hη'sub hη'd
    rw [Sylow.coe_mapSurjective] at hη'sub
    set η₀ : Set (Subgroup G) := {U | U ∈ USet Ω ∧ U ≤ S ∧
      U.map πc ∈ η'} with hη₀
    have himg : (fun U : Subgroup G => U.map πc) '' η₀ =
        η' := by
      ext V
      constructor
      · rintro ⟨U, ⟨-, -, hV⟩, rfl⟩
        exact hV
      · intro hV
        obtain ⟨U, hU, hUS, hUV⟩ :=
          exists_lift_USet_quot hD hZK hΩ' (hη'sub hV).1 hZS (hη'sub hV).2
        exact ⟨U, ⟨hU, hUS, hUV ▸ hV⟩, hUV⟩
    have hinj₀ : Set.InjOn (fun U : Subgroup G => U.map πc)
        η₀ := fun U hU U' hU' h => hinj hU.1 hU'.1 h
    have hinjη : Set.InjOn (fun U : Subgroup G => U.map πc)
        η := fun U hU U' hU' h => hinj (hηsub hU).1 (hηsub hU').1 h
    rw [← himg, hinj₀.ncard_image, hinjη.ncard_image]
    refine hηmax η₀ (fun U hU => ⟨hU.1, hU.2.1⟩) ?_
    intro U hU U' hU' hne J hJ ⟨h1, h2⟩
    have hne' : U.map πc ≠
        U'.map πc := fun h => hne (hinj hU.1 hU'.1 h)
    exact hη'd _ hU.2.2 _ hU'.2.2 hne' _ ⟨J, hJ, rfl⟩
      ⟨Subgroup.map_mono h1, Subgroup.map_mono h2⟩
  · intro s' hs' V hV
    rw [Sylow.coe_mapSurjective] at hs'
    obtain ⟨s, hs, rfl⟩ := hs'
    obtain ⟨U, hU, rfl⟩ := hV
    exact ⟨conjSub s U, hinv s hs U hU, TwistQ.conjSub_map s U⟩

theorem wSet_singleton_of_quot (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    {W' : Subgroup (G ⧸ Subgroup.center G)} (hW' : WSet (quotFam Ω) = {W'}) :
    ∃ W : Subgroup G, WSet Ω = {W} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD' := thmDHyp_quot hD hZK
  have hmapW : ∀ {η : Set (Subgroup G)}, η ∈ etaG Ω →
      (⨆ U ∈ η, U).map πc =
        ⨆ V ∈ (fun U : Subgroup G => U.map πc) '' η, V := by
    intro η _
    rw [iSup_image]
    simp only [Subgroup.map_iSup]
  have hto : ∀ {η : Set (Subgroup G)}, η ∈ etaG Ω →
      (⨆ U ∈ η, U).map πc = W' := by
    intro η hη
    have h1 : (⨆ U ∈ η, U).map πc ∈ WSet (quotFam Ω) :=
      ⟨_, map_mem_etaG_quot hD hZK hη, hmapW hη⟩
    rw [hW'] at h1
    exact h1
  have hsub : ∀ {η η' : Set (Subgroup G)}, η ∈ etaG Ω → η' ∈ etaG Ω → η ⊆ η' := by
    intro η η' hη hη' U hU
    obtain ⟨S', hS', hinv'⟩ := map_mem_etaG_quot hD hZK hη'
    have h69 := (Q3T8.Asc77.l6_9_proved _ (quotFam Ω) hD'.hyp S').2 _ hS' hinv'
    obtain ⟨S, hηS, hinvS⟩ := id hη
    have hU' := hηS.1 hU
    have hUle : U.map πc ≤
        ⨆ V ∈ (fun U : Subgroup G => U.map πc) '' η', V := by
      rw [← hmapW hη', hto hη', ← hto hη]
      exact Subgroup.map_mono (le_biSup (fun U => U) hU)
    have hmem : U.map πc ∈
        (fun U : Subgroup G => U.map πc) '' η' := by
      rw [← h69.2]
      exact ⟨map_mem_USet_quot hD hZK hU'.1, hUle⟩
    obtain ⟨U'', hU'', hUU''⟩ := hmem
    obtain ⟨S₂, hη'S, -⟩ := hη'
    have heq := eq_of_map_eq_of_mem_USet hD.hyp hD.two le_rfl hZK (hη'S.1 hU'').1 hU'.1 hUU''
    rw [← heq]
    exact hU''
  obtain ⟨η₀, hη₀, hinv₀⟩ := (Q3T8.Asc77.l6_9_proved G Ω hD.hyp default).1
  have hη₀G : η₀ ∈ etaG Ω := ⟨default, hη₀, hinv₀⟩
  refine ⟨⨆ U ∈ η₀, U, ?_⟩
  ext W₁
  constructor
  · rintro ⟨η₁, hη₁, rfl⟩
    have h1 : η₁ = η₀ := le_antisymm (hsub hη₁ hη₀G) (hsub hη₀G hη₁)
    rw [h1]
    rfl
  · intro h
    rw [Set.mem_singleton_iff.mp h]
    exact ⟨η₀, hη₀G, rfl⟩

theorem subsingleton_of_quot (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    (h : ∀ L ∈ quotFam Ω, ∀ L' ∈ quotFam Ω, L = L') : ∀ L ∈ Ω, ∀ L' ∈ Ω, L = L' :=
  fun L hL L' hL' =>
    eq_of_map_eq hD.hyp hD.two le_rfl hZK hL hL' (h _ ⟨L, hL, rfl⟩ _ ⟨L', hL', rfl⟩)

theorem centralizes_of_mk_central (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    {x : G} (hx : ∀ g : G, πc x * πc g = πc g * πc x) {K : Subgroup G} (hK : K ∈ Ω) :
    ∀ k ∈ K, x * k = k * x := by
  have hconj : conjSub x K = K := by
    apply eq_of_map_eq hD.hyp hD.two le_rfl hZK (hD.hyp.conjInvariant x K hK) hK
    rw [TwistQ.conjSub_map]
    ext y
    rw [mem_conjSub_iff]
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) y
    have h1 : (πc x)⁻¹ * πc g * πc x = πc g := by
      rw [mul_assoc, ← hx g]
      group
    rw [h1]
  intro k hk
  have hk' : x * k * x⁻¹ ∈ K := by
    rw [← hconj]
    exact conj_mem_conjSub hk
  have hc : (x * k * x⁻¹) * k⁻¹ ∈ Subgroup.center G := by
    rw [← QuotientGroup.eq_one_iff (N := Subgroup.center G)]
    show πc ((x * k * x⁻¹) * k⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx k]
    group
  have h1 : (x * k * x⁻¹) * k⁻¹ ∈ Subgroup.center G ⊓ K := ⟨hc, K.mul_mem hk' (K.inv_mem hk)⟩
  rw [hZK K hK, Subgroup.mem_bot] at h1
  calc x * k = (x * k * x⁻¹) * k⁻¹ * k * x := by group
    _ = k * x := by rw [h1, one_mul]

theorem pSpan_quotFam (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥) :
    pSpan (quotFam Ω) = ⊤ := (thmDHyp_quot hD hZK).gen

@[expose] noncomputable def spanQuot (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥) :
    ↥(pSpan Ω) →* ↥(pSpan (quotFam Ω)) :=
  (MonoidHom.comp πc (pSpan Ω).subtype).codRestrict (pSpan (quotFam Ω)) fun x => by
    rw [pSpan_quotFam hD hZK]
    exact Subgroup.mem_top _

theorem spanQuot_coe (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    (x : ↥(pSpan Ω)) : (spanQuot hD hZK x : G ⧸ Subgroup.center G) = πc (x : G) := rfl

theorem spanQuot_surjective (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥) :
    Function.Surjective (spanQuot hD hZK) := by
  intro y
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) (y : G ⧸ Subgroup.center G)
  refine ⟨⟨g, by rw [hD.gen]; exact Subgroup.mem_top g⟩, Subtype.ext ?_⟩
  rw [spanQuot_coe]
  exact hg

theorem map_spanQuot (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    (L : Subgroup G) :
    (L.subgroupOf (pSpan Ω)).map (spanQuot hD hZK) = (L.map πc).subgroupOf (pSpan (quotFam Ω)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  · intro hy
    obtain ⟨l, hl, hly⟩ := Subgroup.mem_subgroupOf.mp hy
    refine ⟨⟨l, by rw [hD.gen]; exact Subgroup.mem_top l⟩, Subgroup.mem_subgroupOf.mpr hl, ?_⟩
    apply Subtype.ext
    rw [spanQuot_coe]
    exact hly

theorem ker_comp_spanQuot_le {M : Type} [Group M] (hD : ThmDHyp r Ω)
    (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥) {φ : ↥(pSpan (quotFam Ω)) →* M}
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (quotFam Ω))) :
    (φ.comp (spanQuot hD hZK)).ker ≤ Subgroup.center ↥(pSpan Ω) := by
  intro x hx
  have h1 : spanQuot hD hZK x ∈ Subgroup.center _ := hker hx
  have hc : ∀ g : G, πc (x : G) * πc g = πc g * πc (x : G) := by
    intro g
    have h2 := Subgroup.mem_center_iff.mp h1
      ⟨πc g, by rw [pSpan_quotFam hD hZK]; exact Subgroup.mem_top _⟩
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, spanQuot_coe] at h3
    exact h3.symm
  have hle : pSpan Ω ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
    refine pSpan_le fun K hK k hk => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (centralizes_of_mk_central hD hZK hc hK k hk).symm
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle y.2)
  simp only [Subgroup.coe_mul]
  exact this

theorem range_comp_spanQuot {M : Type} [Group M] (hD : ThmDHyp r Ω)
    (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥) (φ : ↥(pSpan (quotFam Ω)) →* M) :
    (φ.comp (spanQuot hD hZK)).range = φ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (spanQuot_surjective hD hZK),
    ← MonoidHom.range_eq_map]

noncomputable def AEIdentOn.ofQuot (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    {n : ℕ} {𝒜 : Set (Finset (Fin n))} {H : Subgroup (AE.AEQ n)}
    (I : AEIdentOn (quotFam Ω) n 𝒜 H) : AEIdentOn Ω n 𝒜 H where
  φ := I.φ.comp (spanQuot hD hZK)
  range_eq := by rw [range_comp_spanQuot, I.range_eq]
  ker_le := ker_comp_spanQuot_le hD hZK I.ker_le
  label := by
    intro L hL
    obtain ⟨α, hα, h, b, hlab⟩ := I.label _ ⟨L, hL, rfl⟩
    exact ⟨α, hα, h, b, by rw [← Subgroup.map_map, map_spanQuot, hlab]⟩
  label_surj := by
    intro α hα h b
    obtain ⟨_, ⟨L, hL, rfl⟩, hlab⟩ := I.label_surj α hα h b
    exact ⟨L, hL, by rw [← Subgroup.map_map, map_spanQuot, hlab]⟩

noncomputable def AEIdent.ofQuot (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    {n : ℕ} (I : AEIdent (quotFam Ω) n) : AEIdent Ω n where
  φ := I.φ.comp (spanQuot hD hZK)
  range_eq := by rw [range_comp_spanQuot, I.range_eq]
  ker_le := ker_comp_spanQuot_le hD hZK I.ker_le
  label := by
    intro L hL
    obtain ⟨α, h, b, hlab⟩ := I.label _ ⟨L, hL, rfl⟩
    exact ⟨α, h, b, by rw [← Subgroup.map_map, map_spanQuot, hlab]⟩
  label_surj := by
    intro α h b
    obtain ⟨_, ⟨L, hL, rfl⟩, hlab⟩ := I.label_surj α h b
    exact ⟨L, hL, by rw [← Subgroup.map_map, map_spanQuot, hlab]⟩

omit [Finite G] in
theorem subsingleton_of_center [Finite G] (hD : ThmDHyp r Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) (hzc : z ∈ Subgroup.center G) :
    ∀ L ∈ Ω, ∀ L' ∈ Ω, L = L' := by
  have hinv : ∀ L ∈ Ω, IsUniqueInvolution L z := by
    intro L hL
    obtain ⟨g, rfl⟩ := hD.trans K hK L hL
    have h1 := hz.conj g
    rwa [show g * z * g⁻¹ = z by rw [Subgroup.mem_center_iff.mp hzc g]; group] at h1
  have hLN : ∀ L ∈ Ω, L ≤ Subgroup.normalizer (K : Set G) := by
    intro L hL v hv
    by_cases hLK : L = K
    · subst hLK
      exact Subgroup.le_normalizer hv
    by_cases hc : ∀ w ∈ L, v * w = w * v
    · have hq : IsQuatSub L :=
        Sec6Gen.isQuatSub_of_mem_RSet hD.hyp (mem_RSet_of_isPGroup hL (hD.two L hL))
      rcases (hinv L hL).unique v hv (hq.sq_eq_one_of_central hv hc) with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.le_normalizer hz.mem
    · exact hD.hyp.omega5 K hK L hL (Ne.symm hLK) z hz v hv hc
        ((hD.two L hL).to_le (Subgroup.zpowers_le.mpr hv)) (isUniqueInvolution_comm (hinv L hL) hv)
  have htop : (⊤ : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [← hD.gen]
    exact pSpan_le hLN
  have hall : ∀ L ∈ Ω, L = K := by
    intro L hL
    obtain ⟨g, rfl⟩ := hD.trans K hK L hL
    exact conjSub_eq_of_mem_normalizer (htop (Subgroup.mem_top g))
  intro L hL L' hL'
  rw [hall L hL, hall L' hL']

theorem center_inf_eq_bot (hD : ThmDHyp r Ω) (hns : ¬ ∀ L ∈ Ω, ∀ L' ∈ Ω, L = L') :
    ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro K hK
  by_contra hne
  obtain ⟨⟨z, hz⟩, -⟩ := hD.hyp.omega1 K hK
  have h2 : IsPGroup 2 ↥(Subgroup.center G ⊓ K) := (hD.two K hK).to_le inf_le_right
  rcases h2.card_eq_or_dvd with h1 | h1
  · exact hne (Subgroup.eq_bot_of_card_eq _ h1)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h1
  have hw1 : (w : G) ≠ 1 := by
    intro h
    have : w = 1 := Subtype.ext h
    rw [this, orderOf_one] at hw
    exact absurd hw (by norm_num)
  have hww : (w : G) * w = 1 := by
    have := pow_orderOf_eq_one w
    rw [hw, pow_two] at this
    exact congrArg Subtype.val this
  have hwz := (hz.unique w w.2.2 hww).resolve_left hw1
  exact hns (subsingleton_of_center hD hK hz (hwz ▸ w.2.1))

end Quot

@[expose] def DLeafZ8 (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), DCex r IH Ω →
    (∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥) →
    ∀ E : Subgroup (G ⧸ Subgroup.center G), E8Struct ⊤ E → Subgroup.center G = ⊥

theorem dLeafZ_of {r : ℕ} {IH : ℕ → Prop} (h8 : DLeafZ8 r IH) : DLeafZ r IH := by
  intro G _ _ Ω hc
  by_contra hZ
  have hns : ¬ ∀ L ∈ Ω, ∀ L' ∈ Ω, L = L' := fun h => hc.not (Or.inl h)
  have hZK := center_inf_eq_bot hc.toThmDHyp hns
  have hD' := thmDHyp_quot hc.toThmDHyp hZK
  have hlt : Nat.card (G ⧸ Subgroup.center G) < Nat.card G := TwistQ.card_lt hZ
  have hconc := (thmDAbsAt_iff.mp (hc.below _ hlt)) _ hD'
  rcases hconc with h0 | ⟨W', hW'⟩ | ⟨E', hE'⟩ | hI | ⟨n, hn, hI⟩ | hI
  · exact hns (subsingleton_of_quot hc.toThmDHyp hZK h0)
  · exact hc.not (Or.inr (Or.inl (wSet_singleton_of_quot hc.toThmDHyp hZK hW')))
  · exact hZ (h8 G Ω hc hZK E' hE')
  · obtain ⟨I⟩ := hI
    exact hc.not (Or.inr (Or.inr (Or.inr (Or.inl ⟨AEIdentOn.ofQuot hc.toThmDHyp hZK I⟩))))
  · obtain ⟨I⟩ := hI
    exact hc.not (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨n, hn, ⟨AEIdent.ofQuot hc.toThmDHyp hZK I⟩⟩)))))
  · obtain ⟨I⟩ := hI
    exact hc.not (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨AEIdentOn.ofQuot hc.toThmDHyp hZK I⟩)))))


theorem thmDAbs_of_leaves₂ {r : ℕ} {IH : ℕ → Prop} (h8 : DLeafZ8 r IH) (hC : DLeafC r IH)
    (hE4 : DLeafE4 r IH) (hstar : DLeafStar r IH) (hend : DLeafEnd r IH) (hih : ∀ n, IH n) :
    ThmDAbs r :=
  thmDAbs_of_leaves (dLeafZ_of h8) hC (dLeafCls_holds r) hE4 hstar hend hih

end CFSG.ClassicalInvolution.Q3.TC.Thin
