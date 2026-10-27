module

public import CFSG.ClassicalInvolution.Balance.ToralBalance
public import CFSG.ClassicalInvolution.Balance.TwoBalancedFrame

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic

section Members

theorem IsInvolutionMember.of_isUniqueInvolution {G : Type*} [Group G] {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hperf : commutator K = ⊤)
    (hq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hsub : IsSubnormal K (Subgroup.centralizer ({z} : Set G))) : IsInvolutionMember K :=
  ⟨hperf, hq, z, hz.mem, hz.sq, fun k hk => by
    have h := hz.conj_eq (conjSub_eq_self_of_mem hk)
    calc z * k = (k * z * k⁻¹) * k := by rw [h]
      _ = k * z := by group, hsub⟩

variable {G : Type} [Group G] [Finite G]

theorem isInvolutionMember_modOdd {a : G} {K : Subgroup G} (hK : IsInvolutionMember K)
    (hKa : K ≤ Subgroup.centralizer ({a} : Set G)) : IsInvolutionMember (modOdd a K) := by
  obtain ⟨z, hzK, hzsq, hzcentral, hsub⟩ := hK.exists_involution
  have hperf := hK.perfect
  have hq := hK.quasisimple
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  set ρ : ↥C →* OddQuot a := oddQuotMk a with hρ
  let K₀ : Subgroup ↥C := K.subgroupOf C
  let e : K₀ ≃* K := Subgroup.subgroupOfEquivOfLe hKa
  have hρsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hρodd : Odd (Nat.card ρ.ker) := by
    rw [hρ, oddQuotMk, QuotientGroup.ker_mk']
    exact OddCore.odd_card ↥C
  let r : ↥K₀ →* ↥(modOdd a K) := (ρ.domRestrict K₀).codRestrict (modOdd a K)
    fun x => Subgroup.mem_map_of_mem ρ x.2
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hkerr : r.ker = (ρ.domRestrict K₀).ker := by
    ext x
    change r x = 1 ↔ ρ x.val = 1
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hroddker : Odd (Nat.card r.ker) := by
    rw [hkerr]
    exact OddKernel.odd_card_restriction_kernel ρ hρodd K₀
  have hperf₀ : Group.IsPerfect K₀ := by
    have : Group.IsPerfect K := ⟨hperf⟩
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hq₀ : CFSG.Open.IsQuasisimple (↥K₀ ⧸ componentClassificationOddCore K₀) :=
    Components.quasisimple_of_equiv
      (QuotientGroup.congr (componentClassificationOddCore K₀) (componentClassificationOddCore K)
        e (OddCore.equiv_invariant e)) hq
  have hKbarperf : Group.IsPerfect ↥(modOdd a K) := Group.IsPerfect.ofSurjective (f := r) hr
  have hKbarq : CFSG.Open.IsQuasisimple (↥(modOdd a K) ⧸
      componentClassificationOddCore (modOdd a K)) :=
    Components.quasisimple_of_equiv (OddKernel.coreQuotientEquiv r hr hroddker).symm hq₀
  have hzC : z ∈ C := hKa hzK
  let z' : ↥C := ⟨z, hzC⟩
  have hz2 : z' * z' = 1 := Subtype.ext hzsq
  have hpg : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_mul_self_eq_one hzsq
  have heq := imageModOddCore_centralizer hzC hpg
  have hsub' : IsSubnormal (modOdd a K) (Subgroup.centralizer {ρ z'}) := by
    have h1 := isSubnormal_inf hsub C
    rw [inf_eq_left.mpr hKa] at h1
    have h2 := CFSG.ComponentClassification.LBalance.subnormal_subgroupOf h1 C
    have h3 := Components.chain_map ρ h2
    have h4 : (((Subgroup.centralizer {z} ⊓ C).subgroupOf C).map ρ) =
        Subgroup.centralizer {ρ z'} := heq
    rwa [h4] at h3
  refine ⟨hKbarperf.commutator_eq_top, hKbarq, ρ z', oddQuotMk_mem_modOdd hzK hzC, ?_, ?_, hsub'⟩
  · rw [← map_mul, hz2, map_one]
  · intro y hy
    obtain ⟨k, hkK, rfl⟩ := mem_modOdd_iff.mp hy
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext (hzcentral k hkK))

end Members

section Frame

variable {G : Type} [Group G] [Finite G]
variable {F : Type*} [Field F] {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

omit [Finite G] in
private theorem exists_two_ne_one_of_card_eq_four {F₀ : Subgroup G} (h4 : Nat.card F₀ = 4) :
    ∃ x ∈ F₀, ∃ y ∈ F₀, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have hfin : Finite F₀ := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F₀
  have hc : 2 < Fintype.card F₀ := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hc
  by_cases ha1 : a = 1
  · refine ⟨b, b.2, c, c.2, ?_, ?_, fun h => hbc (Subtype.ext h)⟩
    · intro h
      exact hab (ha1.trans (Subtype.ext h).symm)
    · intro h
      exact hac (ha1.trans (Subtype.ext h).symm)
  · by_cases hb1 : b = 1
    · refine ⟨a, a.2, c, c.2, fun h => ha1 (Subtype.ext h), ?_, fun h => hac (Subtype.ext h)⟩
      intro h
      exact hbc (hb1.trans (Subtype.ext h).symm)
    · exact ⟨a, a.2, b, b.2, fun h => ha1 (Subtype.ext h), fun h => hb1 (Subtype.ext h),
        fun h => hab (Subtype.ext h)⟩

omit [Finite G] in
theorem exists_mem_ne_one_mem_axisSub (Fr : ToralFrame F Ω E S) {K : Subgroup G} (hK : K ∈ S)
    {F₀ : Subgroup G} (hF₀ : F₀ ≤ E) (h4 : Nat.card F₀ = 4) :
    ∃ f ∈ F₀, f ≠ 1 ∧ f ∈ axisSub E K := by
  obtain ⟨a, haE, -, hsplit⟩ := (Fr.inSigma hK).exists_split
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ := exists_two_ne_one_of_card_eq_four h4
  by_cases hxK : x ∈ axisSub E K
  · exact ⟨x, hx, hx1, hxK⟩
  by_cases hyK : y ∈ axisSub E K
  · exact ⟨y, hy, hy1, hyK⟩
  have hxa : x * a ∈ axisSub E K := (hsplit x (hF₀ hx)).resolve_left hxK
  have hya : y * a ∈ axisSub E K := (hsplit y (hF₀ hy)).resolve_left hyK
  have hxy' : x * y ∈ axisSub E K := by
    have e1 : x * a * (y * a) = x * y := by
      calc x * a * (y * a) = x * (a * y) * a := by group
        _ = x * (y * a) * a := by rw [frame_comm Fr haE (hF₀ hy)]
        _ = x * y * (a * a) := by group
        _ = x * y := by rw [Fr.elem a haE, mul_one]
    rw [← e1]
    exact (axisSub E K).mul_mem hxa hya
  refine ⟨x * y, F₀.mul_mem hx hy, ?_, hxy'⟩
  intro h
  apply hxy
  have hyy : y * y = 1 := Fr.elem y (hF₀ hy)
  calc x = x * (y * y) := by rw [hyy, mul_one]
    _ = (x * y) * y := (mul_assoc _ _ _).symm
    _ = y := by rw [h, one_mul]

theorem exists_mem_modOdd_ne_one_centralizes (Fr : ToralFrame F Ω E S) {a : G} (ha : a ∈ E)
    {K : Subgroup G} (hK : K ∈ S) {F₀ : Subgroup G} (hF₀ : F₀ ≤ E) (h4 : Nat.card F₀ = 4) :
    ∃ f ∈ modOdd a F₀, f ≠ 1 ∧ modOdd a K ≤ Subgroup.centralizer ({f} : Set (OddQuot a)) := by
  obtain ⟨f, hfF, hf1, hfax⟩ := exists_mem_ne_one_mem_axisSub Fr hK hF₀ h4
  have hfC : f ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (frame_comm Fr ha (hF₀ hfF)).symm
  refine ⟨oddQuotMk a ⟨f, hfC⟩, oddQuotMk_mem_modOdd hfF hfC, ?_, ?_⟩
  · intro h
    have hsq : (⟨f, hfC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨f, hfC⟩ = 1 :=
      Subtype.ext (Fr.elem f (hF₀ hfF))
    exact hf1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
  · intro y hy
    obtain ⟨k, hkK, rfl⟩ := mem_modOdd_iff.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk a) (Subtype.ext (hfax.2 (k : G) hkK))

variable (𝒜 : Set (Subgroup G)) in
@[expose] def CentralizedGeneratedAt (a : G) (F₀ : Subgroup G) (L : Subgroup (OddQuot a)) :
    Prop :=
  L ≤ ⨆ K ∈ 𝒜, ⨆ (_ : K ≤ Subgroup.centralizer ({a} : Set G)),
    ⨆ (_ : ∃ f ∈ modOdd a F₀, f ≠ 1 ∧
      modOdd a K ≤ Subgroup.centralizer ({f} : Set (OddQuot a))),
    ⨆ (_ : modOdd a K ≤ L), modOdd a K

variable (E S) in
@[expose] def FrameGeneratedAt (a : G) (L : Subgroup (OddQuot a)) : Prop :=
  L ≤ ⨆ K ∈ S, ⨆ (_ : a ∈ axisSub E K), ⨆ (_ : modOdd a K ≤ L), modOdd a K

theorem FrameGeneratedAt.centralizedGeneratedAt (Fr : ToralFrame F Ω E S) {a : G} (ha : a ∈ E)
    {L : Subgroup (OddQuot a)} (h : FrameGeneratedAt E S a L) {F₀ : Subgroup G} (hF₀ : F₀ ≤ E)
    (h4 : Nat.card F₀ = 4) : CentralizedGeneratedAt S a F₀ L := by
  refine h.trans (iSup₂_le fun K hK => iSup_le fun haK => iSup_le fun hKL => ?_)
  exact le_iSup₂_of_le K hK (le_iSup_of_le (le_centralizer_of_mem_axisSub haK)
    (le_iSup_of_le (exists_mem_modOdd_ne_one_centralizes Fr ha hK hF₀ h4)
      (le_iSup_of_le hKL le_rfl)))

theorem CentralizedGeneratedAt.oddCentralizerFreeMembers {𝒜 : Set (Subgroup G)} {a : G}
    {F₀ : Subgroup G} {L : Subgroup (OddQuot a)} (h : CentralizedGeneratedAt 𝒜 a F₀ L)
    (h𝒜 : ∀ K ∈ 𝒜, IsInvolutionMember K) : OddCentralizerFreeMembers (modOdd a F₀) L := by
  refine OddCentralizerFreeMembers.of_le_iSup
    (𝒦 := {K' | ∃ K ∈ 𝒜, K ≤ Subgroup.centralizer ({a} : Set G) ∧
      (∃ f ∈ modOdd a F₀, f ≠ 1 ∧ modOdd a K ≤ Subgroup.centralizer ({f} : Set (OddQuot a))) ∧
      modOdd a K ≤ L ∧ K' = modOdd a K}) ?_ ?_
  · refine h.trans (iSup₂_le fun K hK => iSup_le fun hKa => iSup_le fun hcen =>
      iSup_le fun hKL => ?_)
    exact le_iSup₂_of_le (modOdd a K) ⟨K, hK, hKa, hcen, hKL, rfl⟩ le_rfl
  · rintro _ ⟨K, hK, hKa, hcen, hKL, rfl⟩
    exact ⟨hKL, isInvolutionMember_modOdd (h𝒜 K hK) hKa, hcen⟩

theorem FrameGeneratedAt.oddCentralizerFreeMembers (Fr : ToralFrame F Ω E S) {a : G}
    (ha : a ∈ E) {L : Subgroup (OddQuot a)} (h : FrameGeneratedAt E S a L)
    (hS : ∀ K ∈ S, IsInvolutionMember K) {F₀ : Subgroup G} (hF₀ : F₀ ≤ E)
    (h4 : Nat.card F₀ = 4) : OddCentralizerFreeMembers (modOdd a F₀) L :=
  (h.centralizedGeneratedAt Fr ha hF₀ h4).oddCentralizerFreeMembers hS

variable (Ω E) in
@[expose] def ComponentLayersAt (a : G) : Prop :=
  ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
    OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨
      ∀ F₀ : Subgroup G, F₀ ≤ E → Nat.card F₀ = 4 →
        modOdd a F₀ ≤ Subgroup.normalizer (L : Set (OddQuot a)) →
        (∀ f ∈ modOdd a F₀, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) →
          OddCentralizerFree (modOdd a F₀) L

theorem twoBalancedWrt_of_frame_of_layers (Fr : ToralFrame F Ω E S)
    (hsym : PairingSymmetric E S) (hconn : PairingConnected E S)
    (hloc : ∀ a ∈ E, a ≠ 1 → ComponentLayersAt Ω E a) : TwoBalancedWrt E := by
  have hcomm := frame_isMulCommutative Fr
  refine twoBalancedWrt_of_quotient_deltaCore_eq_bot hcomm ?_
  intro a ha ha1 F₀ hF₀
  obtain ⟨hF₀E, hF₀card⟩ := hF₀
  have h4 : Nat.card F₀ = 4 := by rw [hF₀card]; norm_num
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (frame_comm Fr ha (hF₀E hf)).symm
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => Fr.elem f (hF₀E hf)
  have hF2bar : ∀ f ∈ modOdd a F₀, f * f = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hF2 _ hx')
    rw [this, map_one]
  show deltaCore (modOdd a F₀) = ⊥
  refine deltaCore_eq_bot_of_oddCentralizerFree (pPrimeCore_oddQuot_eq_bot a)
    (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) hF2bar ?_
  intro L hL hFn hfaith
  rcases hloc a ha ha1 L hL with h | h | hfree
  · obtain ⟨f, hf, hf1, hfc⟩ :=
      exists_mem_ne_one_centralizes_of_omegaFree_or_rankOne Fr hsym hconn ha hF₀E h4 (Or.inl h)
    exact absurd hfc (hfaith f hf hf1)
  · obtain ⟨f, hf, hf1, hfc⟩ :=
      exists_mem_ne_one_centralizes_of_omegaFree_or_rankOne Fr hsym hconn ha hF₀E h4 (Or.inr h)
    exact absurd hfc (hfaith f hf hf1)
  · exact hfree F₀ hF₀E h4 hFn hfaith

theorem twoBalancedWrt_of_frame_of_a2Dichotomy_of_layers (Fr : ToralFrame F Ω E S)
    (hA2 : A2Dichotomy E S) (hfib : FibreLE2 S) (hnc : NonCommConnected S)
    (hloc : ∀ a ∈ E, a ≠ 1 → ComponentLayersAt Ω E a) : TwoBalancedWrt E :=
  twoBalancedWrt_of_frame_of_layers Fr (pairingSymmetric_of_a2Dichotomy Fr hA2)
    (pairingConnected_of_nonCommConnected Fr hA2 hfib hnc) hloc

theorem deltaCore_eq_bot_of_frame_of_layers (Fr : ToralFrame F Ω E S) (hsym : PairingSymmetric E S)
    (hconn : PairingConnected E S) (h16 : 16 ≤ Nat.card E)
    (hloc : ∀ a ∈ E, a ≠ 1 → ComponentLayersAt Ω E a)
    (hO : componentClassificationOddCore G = ⊥) (hGen : FusionGenerated E) :
    ∀ F₀ ∈ signalizerFunctorEk 2 2 E, deltaCore F₀ = ⊥ :=
  deltaCore_eq_bot_of_fusionGenerated
    ⟨frame_isMulCommutative Fr, fun x hx => by rw [pow_two]; exact Fr.elem x hx⟩ h16
    (twoBalancedWrt_of_frame_of_layers Fr hsym hconn hloc) hO hGen

end Frame

end CFSG.ClassicalInvolution.Balance
