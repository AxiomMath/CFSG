module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsLeaf
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8Model
public import Certificates.Certificate13666

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T Timmesfeld.Co1Leaf

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K]

theorem card_units_four (hK : Nat.card K = 4) : Nat.card Kˣ = 3 := by
  rw [Nat.card_units, hK]

theorem pow_three_units (hK : Nat.card K = 4) (u : Kˣ) : u ^ 3 = 1 := by
  rw [← card_units_four hK]
  exact pow_card_eq_one'

theorem exists_eq_pow (hK : Nat.card K = 4) {ω : Kˣ} (hω : orderOf ω = 3) (u : Kˣ) :
    ∃ m : ℕ, u = ω ^ m := by
  have hz : Subgroup.zpowers ω = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_zpowers, hω, card_units_four hK]
  have hu : u ∈ Subgroup.zpowers ω := hz ▸ Subgroup.mem_top u
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  refine ⟨(n % 3).toNat, ?_⟩
  rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, hω]
  have h0 : 0 ≤ n % 3 := Int.emod_nonneg _ (by norm_num)
  rw [Int.toNat_of_nonneg h0]
  exact (Int.mod_modEq n 3).symm

theorem exists_torV (hK : Nat.card K = 4) {ω : Kˣ} (hω : orderOf ω = 3) {τ : Tag}
    (a : Fin τ.rank → Kˣ) : ∃ y : Fin τ.rank → ZMod 3, a = torV ω y := by
  choose m hm using fun i => exists_eq_pow hK hω (a i)
  refine ⟨fun i => (m i : ZMod 3), funext fun i => ?_⟩
  rw [torV, hm i, ZMod.val_natCast]
  have h3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  conv_lhs => rw [← Nat.mod_add_div (m i) 3]
  rw [pow_add, pow_mul, h3, one_pow, mul_one]

variable {τ : Tag}

theorem pow_three_of_mem_torusGroup (hK : Nat.card K = 4) {g : ModGL τ K}
    (hg : g ∈ torusGroup τ K) : g ^ 3 = 1 := by
  obtain ⟨a, rfl⟩ := torusGroup_le_range_rootDiagUnitHom hg
  rw [← map_pow]
  have : a ^ 3 = 1 := funext fun i => pow_three_units hK (a i)
  rw [this, map_one]

theorem dV_mem_adjointGroup {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hB : B * τ.cartan = 1)
    (ω : Kˣ) (x : Fin τ.rank → ZMod 3) : dV ω x ∈ adjointGroup τ K :=
  CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup'
    (rootDiagUnit_mem_torusGroup_of_unimodular hB _)

theorem pow_three_mem_of_mem_sup (hK : Nat.card K = 4) {L : Subgroup (ModGL τ K)}
    (hL : torusGroup τ K ≤ Subgroup.normalizer (L : Set (ModGL τ K))) {g : ModGL τ K}
    (hg : g ∈ torusGroup τ K ⊔ L) : g ^ 3 ∈ L := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hL] at hg
  obtain ⟨t, ht, l, hl, rfl⟩ := hg
  have ht3 : t ^ 3 = 1 := pow_three_of_mem_torusGroup hK ht
  have hc : ∀ n : ℕ, t ^ n * l * (t ^ n)⁻¹ ∈ L := fun n =>
    (Subgroup.mem_normalizer_iff.1 (hL (pow_mem ht n)) l).1 hl
  have e : (t * l) ^ 3 = (t ^ 1 * l * (t ^ 1)⁻¹) * (t ^ 2 * l * (t ^ 2)⁻¹) *
      (t ^ 3 * l * (t ^ 3)⁻¹) * t ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev]
    group
  rw [e]
  refine mul_mem (mul_mem (mul_mem (hc 1) (hc 2)) (hc 3)) ?_
  rw [ht3]
  exact one_mem _

theorem le_center_or_eq_top_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    (N : Subgroup Q) [N.Normal] : N ≤ Subgroup.center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hsimp, -⟩ := hQ
  set π := QuotientGroup.mk' (Subgroup.center Q)
  have hnorm : (N.map π).Normal := Subgroup.Normal.map ‹_› π (QuotientGroup.mk'_surjective _)
  rcases hsimp.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    intro x hx
    have : π x ∈ N.map π := Subgroup.mem_map_of_mem π hx
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).1 this
  · right
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : π x ∈ N.map π := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      have hz : n⁻¹ * x ∈ Subgroup.center Q := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        change (π n)⁻¹ * π x = 1
        rw [hnx, inv_mul_cancel]
      have : x = n * (n⁻¹ * x) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hz)
    have hcomm : ∀ a b : Q, a * b * a⁻¹ * b⁻¹ ∈ N := by
      intro a b
      have ha : a ∈ N ⊔ Subgroup.center Q := hsup ▸ Subgroup.mem_top a
      have hb : b ∈ N ⊔ Subgroup.center Q := hsup ▸ Subgroup.mem_top b
      rw [← SetLike.mem_coe, Subgroup.normal_mul] at ha hb
      obtain ⟨n, hn, z, hz, rfl⟩ := ha
      obtain ⟨m, hm, y, hy, rfl⟩ := hb
      have hz' := Subgroup.mem_center_iff.1 hz
      have hy' := Subgroup.mem_center_iff.1 hy
      have e : n * z * (m * y) * (n * z)⁻¹ * (m * y)⁻¹ = n * m * n⁻¹ * m⁻¹ := by
        calc n * z * (m * y) * (n * z)⁻¹ * (m * y)⁻¹
            = n * (z * (m * y)) * z⁻¹ * n⁻¹ * (y⁻¹ * m⁻¹) := by group
          _ = n * ((m * y) * z) * z⁻¹ * n⁻¹ * (y⁻¹ * m⁻¹) := by rw [hz' (m * y)]
          _ = n * m * (y * n⁻¹ * y⁻¹) * m⁻¹ := by group
          _ = n * m * (n⁻¹ * y * y⁻¹) * m⁻¹ := by rw [hy' n⁻¹]
          _ = n * m * n⁻¹ * m⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem (mul_mem hn hm) (inv_mem hn)) (inv_mem hm)
    rw [eq_top_iff, ← hperf.commutator_eq_top]
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    exact hcomm a b

section Normal


theorem mem_torusGroup_of_mem_familyCentralizer_std {ω : Kˣ}
    (hstd : familyKernel (famV (τ := τ) ω (Native.stdBasis τ.rank)) = ∅ ∧
      ∀ w ∈ familyStabilizer (famV (τ := τ) ω (Native.stdBasis τ.rank)), w = 1)
    {g : ModGL τ K} (hg : g ∈ familyCentralizer τ K (famV (τ := τ) ω (Native.stdBasis τ.rank))) :
    g ∈ torusGroup τ K := by
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul τ K _ hg
  rw [hstd.2 w hw, canonicalRep_one, mul_one]
  have hm' : m ∈ torusGroup τ K ⊔ rootSpan τ K (familyKernel (famV (τ := τ) ω
      (Native.stdBasis τ.rank))) := hm
  rw [hstd.1] at hm'
  have hbot : rootSpan τ K (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by simp [rootSpan]
  rwa [hbot, sup_bot_eq] at hm'

theorem mem_familyCentralizer_std {ω : Kˣ} {g : ModGL τ K} (hgC : g ∈ adjointGroup τ K)
    (h : ∀ x : Fin τ.rank → ZMod 3, Commute (dV ω x) g) :
    g ∈ familyCentralizer τ K (famV (τ := τ) ω (Native.stdBasis τ.rank)) := by
  rw [mem_familyCentralizer]
  refine ⟨hgC, fun j => ?_⟩
  change dV ω (listVec τ.rank ((Native.stdBasis τ.rank).get j)) * g *
    (dV ω (listVec τ.rank ((Native.stdBasis τ.rank).get j)))⁻¹ = g
  rw [(h _).eq, mul_assoc, mul_inv_cancel, mul_one]

theorem rootDiagUnit_mem_centralizer_rootSpan {a : Fin τ.rank → Kˣ} {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h1 : rootChar a α = 1) {g : ModGL τ K}
    (hg : g ∈ rootSpan τ K {α, -α}) : Commute (rootDiagUnit τ a) g := by
  have hneg : rootChar a (-α) = 1 := by
    rw [← zero_sub, rootChar_sub, rootChar_zero, h1, inv_one, one_mul]
  have hle : rootSpan τ K {α, -α} ≤ Subgroup.centralizer {rootDiagUnit τ a} := by
    refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hβr : IsRoot τ β := by
      rcases hβ with rfl | rfl
      · exact hα
      · exact IsRoot.neg hα
    have hχ : rootChar a β = 1 := by
      rcases hβ with rfl | rfl
      · exact h1
      · exact hneg
    have e := rootDiagUnit_conj_pinnedX a hβr c
    rw [hχ, Units.val_one, one_mul, mul_inv_eq_iff_eq_mul] at e
    exact e.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

theorem eq_bot_of_le_rootSpan (hK : Nat.card K = 4) {ω : Kˣ} (hω : orderOf ω = 3)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hkerχ : kernelRoots χ = {α, -α})
    (htor : ∀ g ∈ adjointGroup τ K, (∀ x, Commute (dV (τ := τ) ω x) g) → g ∈ torusGroup τ K)
    (N : Subgroup (adjointGroup τ K))
    (hNL : ∀ n ∈ N, (n : ModGL τ K) ∈ rootSpan τ K {α, -α})
    (hnorm : ∀ g : adjointGroup τ K, (g : ModGL τ K) ∈ rootSpan τ K {α, -α} →
      ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hcop : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hαk : α ∈ kernelRoots χ := by rw [hkerχ]; exact Set.mem_insert _ _
  have hnαk : -α ∈ kernelRoots χ := by rw [hkerχ]; exact Set.mem_insert_of_mem _ rfl
  set i : KernelComponent χ := ⟦⟨α, hαk⟩⟧ with hi
  have hcomp : componentRoots χ i = {α, -α} := by
    ext β
    constructor
    · rintro ⟨hβ, -⟩
      rwa [hkerχ] at hβ
    · rintro (rfl | rfl)
      · exact ⟨hαk, rfl⟩
      · refine ⟨hnαk, ?_⟩
        refine mk_eq_of_iform_ne_zero ?_
        change iform (-α) α ≠ 0
        rw [show iform (-α) α = -iform α α by simp [iform]]
        exact neg_ne_zero.2 (iform_self_pos_of_isRoot hα).ne'
  set L := rootSpan τ K {α, -α} with hL
  have hspan : componentRootSpan K χ i = L := by
    show rootSpan τ K (componentRoots χ i) = L
    rw [hcomp]
  have ht : (ω ^ 2 : Kˣ) ^ 2 ≠ 1 := by
    intro h
    rw [← pow_mul] at h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hω] at this
    norm_num at this
  have hqs := isQuasisimple_componentRootSpan_of_sq_ne_one (K := K) (χ := χ) ht i
  rw [hspan] at hqs
  have hLG : L ≤ adjointGroup τ K := rootSpan_le_adjointGroup K _
  obtain ⟨w, k, hwk⟩ := isRoot_iff_exists_smul_single.1 hα
  set t₀ := canonicalRep (coxeterSystem τ) K w * torusElt τ K k ω *
    (canonicalRep (coxeterSystem τ) K w)⁻¹ with ht₀
  have ht₀L : t₀ ∈ L := by
    have h := canonicalRep_conj_torusElt_mem (χ := χ) (i := i) (w := w) (k := k)
      (by rw [hwk, hcomp]; exact Set.mem_insert _ _) ω
    rw [← hspan]
    exact h.1
  set b : Fin τ.rank → Kˣ := fun j => ω ^ τ.cartan k j with hb
  have ht₀b : t₀ = rootDiagUnit τ (weylTuple w b) := by
    rw [ht₀, torusElt_eq_rootDiagUnit, canonicalRep_conj_rootDiagUnit]
  have hχt₀ : rootChar (weylTuple w b) α = ω ^ 2 := by
    rw [rootChar_weylTuple, ← hwk, inv_smul_smul]
    have := rootChar_nsmul_single b k 1
    rw [one_nsmul, pow_one] at this
    rw [this, hb]
    simp [Tag.cartan_self]
  obtain ⟨y, hy⟩ := exists_torV hK hω (weylTuple w b)
  have ht₀y : t₀ = dV ω y := by rw [ht₀b, hy]; rfl
  set N' : Subgroup L := (N.map (adjointGroup τ K).subtype).subgroupOf L with hN'
  have hN'norm : N'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hN', Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨n, hn, hnx⟩ := hx
    refine ⟨⟨g, hLG g.2⟩ * n * ⟨g, hLG g.2⟩⁻¹, hnorm ⟨g, hLG g.2⟩ g.2 n hn, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hnx ⊢
    rw [hnx]
  have hmemN' : ∀ (n : adjointGroup τ K) (hn : n ∈ N), (⟨n, hNL n hn⟩ : L) ∈ N' :=
    fun n hn => by
      rw [hN', Subgroup.mem_subgroupOf]
      exact ⟨n, hn, rfl⟩
  have hω2 : (ω ^ 2 : Kˣ) ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hω] at this
    norm_num at this
  have ht₀1 : t₀ ≠ 1 := by
    intro h
    rw [ht₀b] at h
    have h1 : weylTuple w b = 1 := rootDiagUnit_injective (τ := τ) (K := K)
      (h.trans (Units.ext rootDiag_one).symm)
    rw [h1] at hχt₀
    exact hω2 (hχt₀.symm.trans (by simp [rootChar]))
  have ht₀3 : t₀ ^ 3 = 1 := by
    rw [ht₀y, ← dVHom_ofAdd hω3, ← map_pow, ← ofAdd_nsmul]
    have h : (3 • y) = 0 := by
      funext j
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      have : (3 : ZMod 3) = 0 := rfl
      rw [Nat.cast_ofNat, this, zero_mul]
    rw [h, ofAdd_zero, map_one]
  have hordt₀ : orderOf t₀ = 3 := by
    rw [orderOf_eq_prime_iff]
    exact ⟨ht₀3, ht₀1⟩
  have hcent : ∀ n ∈ N, Commute (n : ModGL τ K) t₀ := by
    rcases le_center_or_eq_top_of_isQuasisimple hqs N' with h | h
    · intro n hn
      have hz := Subgroup.mem_center_iff.1 (h (hmemN' n hn)) ⟨t₀, ht₀L⟩
      have := congrArg Subtype.val hz
      exact (this.symm : (n : ModGL τ K) * t₀ = t₀ * n)
    · exfalso
      have ht₀N : (⟨t₀, ht₀L⟩ : L) ∈ N' := h ▸ Subgroup.mem_top _
      rw [hN', Subgroup.mem_subgroupOf] at ht₀N
      obtain ⟨n₀, hn₀, hn₀t⟩ := ht₀N
      have hord : orderOf n₀ = 3 := by
        have h1 : orderOf (n₀ : ModGL τ K) = orderOf t₀ := congrArg orderOf hn₀t
        rw [Subgroup.orderOf_coe] at h1
        rw [h1, hordt₀]
      have h3 : orderOf (⟨n₀, hn₀⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, hord] at h3
      exact absurd (Nat.Coprime.coprime_dvd_right h3 hcop) (by norm_num)
  have hrc : ∀ (a c : Fin τ.rank → Kˣ), rootChar (a * c) α = rootChar a α * rootChar c α := by
    intro a c
    simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
  have htorV_pow : ∀ (x : Fin τ.rank → ZMod 3) (m : ℕ), torV ω (m • x) = torV ω x ^ m := by
    intro x m
    induction m with
    | zero => rw [zero_smul, pow_zero, torV_zero]
    | succ m ih => rw [succ_nsmul, torV_add hω3, ih, pow_succ]
  have hrcpow : ∀ (a : Fin τ.rank → Kˣ) (m : ℕ), rootChar (a ^ m) α = rootChar a α ^ m := by
    intro a m
    induction m with
    | zero => simp [rootChar]
    | succ m ih => rw [pow_succ, hrc, ih, pow_succ]
  have hall : ∀ n ∈ N, ∀ x : Fin τ.rank → ZMod 3, Commute (dV ω x) (n : ModGL τ K) := by
    intro n hn x
    obtain ⟨m, hm⟩ := exists_eq_pow hK hω (rootChar (torV ω x) α)
    set x' := x + m • y with hx'
    have hχx' : rootChar (torV ω x') α = 1 := by
      rw [hx', torV_add hω3, htorV_pow, hrc, hrcpow, hm, ← hy, hχt₀, ← pow_mul, ← pow_add]
      have : m + 2 * m = 3 * m := by ring
      rw [this, pow_mul, hω3, one_pow]
    have hx : x = x' + (2 * m) • y := by
      rw [hx', add_assoc, ← add_nsmul]
      have h3 : (m + 2 * m) • y = 0 := by
        funext j
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
        push_cast
        have : ((m : ZMod 3) + 2 * m) = 3 * m := by ring
        rw [this]
        have : (3 : ZMod 3) = 0 := rfl
        rw [this, zero_mul, zero_mul]
      rw [h3, add_zero]
    have hc1 : Commute (dV ω x') (n : ModGL τ K) :=
      rootDiagUnit_mem_centralizer_rootSpan hα hχx' (hNL n hn)
    have hc2 : Commute (dV ω ((2 * m) • y)) (n : ModGL τ K) := by
      rw [← dVHom_ofAdd hω3, ofAdd_nsmul, map_pow, dVHom_ofAdd, ← ht₀y]
      exact ((hcent n hn).symm).pow_left _
    rw [hx, dV_add hω3]
    exact hc1.mul_left hc2
  refine eq_bot_iff.2 fun n hn => ?_
  have hnT := htor _ (n : adjointGroup τ K).2 (hall n hn)
  have hn3 : (n : ModGL τ K) ^ 3 = 1 := pow_three_of_mem_torusGroup hK hnT
  have hord : orderOf (⟨n, hn⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  have hord3 : orderOf (⟨n, hn⟩ : N) ∣ 3 := by
    rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hn3
  have hcop' : Nat.Coprime (orderOf (⟨n, hn⟩ : N)) 3 :=
    (Nat.Coprime.coprime_dvd_right hord hcop).symm
  have h1 : orderOf (⟨n, hn⟩ : N) = 1 := Nat.Coprime.eq_one_of_dvd hcop' hord3
  rw [orderOf_eq_one_iff] at h1
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h1

end Normal

section Balance


theorem gLAPPrimeCoreOf_centralizer_dV_split (hK : Nat.card K = 4) {ω : Kˣ}
    (hω : orderOf ω = 3) {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hB : B * τ.cartan = 1)
    (hcert : Native.hypOK τ = true) {x : Fin τ.rank → ZMod 3} (hx : x ≠ 0) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer
      {dG (G := adjointGroup τ K) (dV_mem_adjointGroup hB ω) x}) = ⊥ := by
  have : Finite (ModGL τ K) := finite_modGL
  have hG := dV_mem_adjointGroup (K := K) hB ω
  have hX3 : ∀ g ∈ adjointGroup τ K, g ∈ torusGroup τ K → g ^ 3 = 1 :=
    fun g _ hg => pow_three_of_mem_torusGroup hK hg
  have hstd : familyKernel (famV (τ := τ) ω (Native.stdBasis τ.rank)) = ∅ ∧
      ∀ w ∈ familyStabilizer (famV (τ := τ) ω (Native.stdBasis τ.rank)), w = 1 :=
    famData0_of_famOK0 hω length_of_mem_stdBasis lt_of_mem_stdBasis (famOK_std_of_hypOK hcert)
  have htor : ∀ g ∈ adjointGroup τ K, (∀ x, Commute (dV (τ := τ) ω x) g) →
      g ∈ torusGroup τ K := fun g hg h =>
    mem_torusGroup_of_mem_familyCentralizer_std hstd (mem_familyCentralizer_std hg h)
  have hleaf : ∀ (kb : List (List ℕ)), (∀ b ∈ kb, b.length = τ.rank) →
      (∀ b ∈ kb, ∀ x ∈ b, x < 3) →
      Native.famOK (Native.gramL τ) (Native.rootsN τ) (Native.simpleL τ)
        ((Native.simpleL τ).map fun e => Native.formB (Native.gramL τ) e e) kb = true →
      GLAPPrimeCoreOf 3 (famCent hG kb) = ⊥ := by
    intro kb hlen hlt hok
    refine gLAPPrimeCoreOf_leaf (G := adjointGroup τ K) le_rfl hG hX3 ?_
    rcases famData_of_famOK hω hlen hlt hok with h | ⟨α, hα, hker, hW⟩
    · exact Or.inl h
    · refine Or.inr ⟨α, hα, hker, hW, fun g _ hg => ?_, fun N hNL hnorm hcop => ?_⟩
      · refine pow_three_mem_of_mem_sup hK ?_ hg
        exact torusGroup_le_normalizer_rootSpan fun β hβ => by
          rcases hβ with rfl | rfl
          · exact hα
          · exact IsRoot.neg hα
      · refine eq_bot_of_le_rootSpan hK hω (χ := familyChar (famV (τ := τ) ω kb)) hα
          (by rw [kernelRoots_familyChar, hker]) htor N hNL hnorm hcop
  exact gLAPPrimeCoreOf_centralizer_dG hω hG
    (fun fl hfl => hleaf _ (length_of_mem_kerBasis hfl) lt_of_mem_kerBasis
      (famOK_of_hypOK hcert hfl))
    (gLAPPrimeCoreOf_leaf (G := adjointGroup τ K) le_rfl hG hX3 (Or.inl hstd)) hx

theorem dV_mem_F4 (ω : Kˣ) (x : Fin Tag.F4.rank → ZMod 3) : dV ω x ∈ adjointGroup Tag.F4 K :=
  dV_mem_adjointGroup CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_mul_cartan_F4.choose_spec ω x

theorem dV_mem_E8 (ω : Kˣ) (x : Fin Tag.E8.rank → ZMod 3) : dV ω x ∈ adjointGroup Tag.E8 K :=
  dV_mem_adjointGroup CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_mul_cartan_E8.choose_spec ω x

theorem gLAPPrimeCoreOf_centralizer_dV_F4
    (hK : Nat.card K = 4) {ω : Kˣ} (hω : orderOf ω = 3) {x : Fin Tag.F4.rank → ZMod 3}
    (hx : x ≠ 0) : GLAPPrimeCoreOf 3 (Subgroup.centralizer {dG (dV_mem_F4 ω) x}) = ⊥ :=
  gLAPPrimeCoreOf_centralizer_dV_split hK hω
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_mul_cartan_F4.choose_spec
    Certificates.certificate13666.1 hx

theorem gLAPPrimeCoreOf_centralizer_dV_E8
    (hK : Nat.card K = 4) {ω : Kˣ} (hω : orderOf ω = 3) {x : Fin Tag.E8.rank → ZMod 3}
    (hx : x ≠ 0) : GLAPPrimeCoreOf 3 (Subgroup.centralizer {dG (dV_mem_E8 ω) x}) = ⊥ :=
  gLAPPrimeCoreOf_centralizer_dV_split hK hω
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_mul_cartan_E8.choose_spec
    Certificates.certificate13666.2.2.1 hx

end Balance

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
