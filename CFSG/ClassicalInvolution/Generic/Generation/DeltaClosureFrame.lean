module

public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureLink
public import CFSG.ClassicalInvolution.Reduction
import CFSG.ClassicalInvolution.Generic.InductionLocal

public section

namespace CFSG.ClassicalInvolution.Generic.DeltaClosure

open CFSG.Open
open CFSG.ClassicalInvolution.Balance (oddCoreIn odd_card_oddCoreIn conj_mem_oddCoreIn)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {S : Set (Subgroup G)}

section SimplyLaced

omit [Finite G] in
theorem FrameGenerationModO.centralizerGenerationModO (hS : S ⊆ Ω)
    (hrank : ∀ K ∈ S, ∃ E₀ ∈ signalizerFunctorEk 2 3 A, K ≤ Subgroup.centralizer (E₀ : Set G))
    {a : G} (h : FrameGenerationModO Ω S a) : CentralizerGenerationModO Ω A a := by
  refine h.trans (sup_le_sup_left (iSup₂_le fun K hK => iSup_le fun hKa => ?_) _)
  obtain ⟨E₀, hE₀, hKE⟩ := hrank K hK
  exact le_iSup₂_of_le E₀ hE₀ (le_inf hKE (le_centralizingLayer ⟨hS hK, hKa⟩))

theorem FrameGenerationModO.cover (hΩ : InClass p f Ω) (hS : S ⊆ Ω) {a : G}
    (h : FrameGenerationModO Ω S a) : FrameCoversModO Ω S a := by
  intro L hL
  by_contra hno
  push Not at hno
  set Y := centralizingLayer Ω {a} with hY
  have hLY : L ≤ Y := le_centralizingLayer hL
  obtain ⟨z, hz⟩ := hΩ.classical L hL.1
  have hclaim : ∀ x ∈ L, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ oddCoreIn Y := by
    intro x hx y hy
    have hxY : x ∈ Y := hLY hx
    let C : Subgroup ↥Y :=
      (Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨x, hxY⟩} :
        Set (↥Y ⧸ classicalInvolutionOddCore ↥Y))).comap
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))
    have hC : ∀ t : ↥Y, t ∈ C ↔ x * (t : G) * x⁻¹ * (t : G)⁻¹ ∈ oddCoreIn Y := by
      intro t
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, eq_comm]
      exact mk_comm_eq_iff hxY t.2
    have hO : oddCoreIn Y ≤ C.map Y.subtype := by
      rintro _ ⟨w, hw, rfl⟩
      have hwO : (w : G) ∈ oddCoreIn Y := ⟨w, hw, rfl⟩
      exact ⟨w, (hC w).mpr ((oddCoreIn Y).mul_mem (conj_mem_oddCoreIn hxY hwO)
        ((oddCoreIn Y).inv_mem hwO)), rfl⟩
    have hKle : ∀ K ∈ S, K ≤ Subgroup.centralizer ({a} : Set G) → K ≤ C.map Y.subtype := by
      intro K hK hKa k hk
      have hkY : k ∈ Y := le_centralizingLayer ⟨hS hK, hKa⟩ hk
      exact ⟨⟨k, hkY⟩, (hC ⟨k, hkY⟩).mpr (hno K hK hKa x hx k hk), rfl⟩
    have hYle : Y ≤ C.map Y.subtype :=
      h.trans (sup_le hO (iSup₂_le fun K hK => iSup_le fun hKa => hKle K hK hKa))
    obtain ⟨t, ht, rfl⟩ := hYle hy
    exact (hC t).mp ht
  have hcomm : commutator ↥L ≤ (oddCoreIn Y).subgroupOf L := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    rw [Subgroup.mem_subgroupOf]
    exact hclaim x x.2 y (hLY y.2)
  have hzc : (⟨z, hz.mem⟩ : ↥L) ∈ commutator ↥L := by
    rw [hz.perfect.commutator_eq_top]
    exact Subgroup.mem_top _
  have hzO : z ∈ oddCoreIn Y := hcomm hzc
  have hz1 := eq_one_of_mem_of_odd_of_sq (odd_card_oddCoreIn Y) hzO (sq_eq_one hz)
  have := hz.orderOf_eq_two
  rw [hz1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem FrameSide.of_frameGeneration (hL : LocalHypotheses p f Ω A) (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hS : S ⊆ Ω) (hne : S.Nonempty)
    (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z)
    (hrank : ∀ K ∈ S, ∃ E₀ ∈ signalizerFunctorEk 2 3 A, K ≤ Subgroup.centralizer (E₀ : Set G))
    (hgen : ∀ a ∈ A, IsFrameInvolution p f S a → FrameGenerationModO Ω S a) :
    FrameSide p f Ω A S :=
  FrameSide.of_cover hL hA h16 hS hne hinv
    (fun a ha hfa => (hgen a ha hfa).centralizerGenerationModO hS hrank)
    (fun a ha hfa => (hgen a ha hfa).cover hL.inClass hS)

end SimplyLaced

section Toral

variable {F : Type*} [Field F] {E : Subgroup G}

omit [Finite G] in
private theorem comm_of_sq_eq_one {x y : G} (hE : ∀ z ∈ E, z * z = 1) (hx : x ∈ E) (hy : y ∈ E) :
    x * y = y * x := by
  have h1 := hE (x * y) (E.mul_mem hx hy)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hE x hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hE y hy)
  have hxyi : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
  calc x * y = (x * y)⁻¹ := hxyi.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hxi, hyi]

omit [Finite G] in
theorem isElemAbelian_two_of_sq_eq_one (hE : ∀ x ∈ E, x * x = 1) : IsElemAbelian 2 E :=
  ⟨⟨⟨fun x y => Subtype.ext (comm_of_sq_eq_one hE x.2 y.2)⟩⟩, fun x hx => by
    rw [pow_two]
    exact hE x hx⟩

theorem exists_subgroup_card_eight_le {X : Subgroup G} (hE : IsElemAbelian 2 E) (hXE : X ≤ E)
    (h8 : 8 ≤ Nat.card X) : ∃ E₀ ∈ signalizerFunctorEk 2 3 E, E₀ ≤ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 X := by
    refine IsPGroup.iff_orderOf.mpr fun g => ?_
    have hg : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (hE.2 g (hXE g.2)))
    rcases (Nat.dvd_prime Nat.prime_two).mp hg with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have h3 : 3 ≤ n := by
    by_contra hlt
    have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := X) 2 (n := 3)
    (by rw [hn]; exact pow_dvd_pow 2 h3)
  refine ⟨K.map X.subtype, ⟨(Subgroup.map_subtype_le K).trans hXE, ?_⟩, Subgroup.map_subtype_le K⟩
  rw [Subgroup.card_map_of_injective X.subtype_injective, hK]

theorem exists_rank3_of_relIndex_two (hE : IsElemAbelian 2 E) (h16 : 16 ≤ Nat.card E)
    {K : Subgroup G} (h2 : (axisSub E K).relIndex E = 2) :
    ∃ E₀ ∈ signalizerFunctorEk 2 3 E, K ≤ Subgroup.centralizer (E₀ : Set G) := by
  have hXE : axisSub E K ≤ E := inf_le_left
  have hmul := Subgroup.card_mul_index ((axisSub E K).subgroupOf E)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXE).toEquiv] at hmul
  have hidx : ((axisSub E K).subgroupOf E).index = 2 := h2
  rw [hidx] at hmul
  obtain ⟨E₀, hE₀, hE₀X⟩ := exists_subgroup_card_eight_le hE hXE (by omega)
  exact ⟨E₀, hE₀, Subgroup.le_centralizer_iff.mp (hE₀X.trans inf_le_right)⟩

theorem exists_rank3_of_toralFrame {S : Set (Subgroup G)} (Fr : ToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) {K : Subgroup G} (hK : K ∈ S) :
    ∃ E₀ ∈ signalizerFunctorEk 2 3 E, K ≤ Subgroup.centralizer (E₀ : Set G) := by
  obtain ⟨φ, rfl, hD⟩ := Fr.inSigma hK
  exact exists_rank3_of_relIndex_two (isElemAbelian_two_of_sq_eq_one Fr.elem) h16 hD.index_two

omit [Finite G] in
theorem exists_involution_mem_of_toralFrame {S : Set (Subgroup G)} (Fr : ToralFrame F Ω E S)
    (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ S) :
    ∃ z ∈ E, IsClassicalMember p f K z := by
  obtain ⟨z₀, hz₀⟩ := hΩ.classical K (Fr.subset hK)
  obtain ⟨z, hz⟩ := Fr.exists_isUniqueInvolution hK
  have hne : z₀ ≠ 1 := by
    intro h1
    have := hz₀.orderOf_eq_two
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hzz : z₀ = z := (hz.unique z₀ hz₀.mem (sq_eq_one hz₀)).resolve_left hne
  exact ⟨z₀, hzz ▸ Fr.mem_of_isUniqueInvolution hK hz, hz₀⟩

theorem FrameSide.of_toralFrame {S : Set (Subgroup G)} (Fr : ToralFrame F Ω E S)
    (hL : LocalHypotheses p f Ω E) (h16 : 16 ≤ Nat.card E)
    (hgen : ∀ a ∈ E, IsFrameInvolution p f S a → FrameGenerationModO Ω S a) :
    FrameSide p f Ω E S :=
  FrameSide.of_frameGeneration hL (isElemAbelian_two_of_sq_eq_one Fr.elem) h16 Fr.subset
    (let ⟨K, hK, _⟩ := Fr.exists_ne; ⟨K, hK⟩)
    (fun _ hK => exists_involution_mem_of_toralFrame Fr hL.inClass hK)
    (fun _ hK => exists_rank3_of_toralFrame Fr h16 hK) hgen

theorem fusionGenerated_of_toralFrame {S : Set (Subgroup G)} (Fr : ToralFrame F Ω E S)
    (hL : LocalHypotheses p f Ω E) (h16 : 16 ≤ Nat.card E)
    (hgen : ∀ a ∈ E, IsFrameInvolution p f S a → FrameGenerationModO Ω S a)
    (hconn : OmegaConnected Ω) : CFSG.ClassicalInvolution.Balance.FusionGenerated E :=
  fusionGenerated_of_deltaClosure hL.inClass (FrameSide.of_toralFrame Fr hL h16 hgen) hconn

theorem fusionGenerated_of_toralFrame_of_cover {S : Set (Subgroup G)} (Fr : ToralFrame F Ω E S)
    (hL : LocalHypotheses p f Ω E) (h16 : 16 ≤ Nat.card E)
    (hgen : ∀ a ∈ E, IsFrameInvolution p f S a → CentralizerGenerationModO Ω E a)
    (hcover : ∀ a ∈ E, IsFrameInvolution p f S a → FrameCoversModO Ω S a)
    (hconn : OmegaConnected Ω) : CFSG.ClassicalInvolution.Balance.FusionGenerated E :=
  fusionGenerated_of_lie hL (isElemAbelian_two_of_sq_eq_one Fr.elem) h16 Fr.subset
    (let ⟨K, hK, _⟩ := Fr.exists_ne; ⟨K, hK⟩)
    (fun _ hK => exists_involution_mem_of_toralFrame Fr hL.inClass hK) hgen hcover hconn

end Toral

section Connected

omit [Finite G] in
theorem omegaConnected_of_deltaConnected {J : Subgroup G}
    (h : CFSG.ClassicalInvolution.DeltaConnected J) :
    OmegaConnected (CFSG.ClassicalInvolution.conjugateSet J) := by
  intro L hL L' hL'
  have hle : CFSG.ClassicalInvolution.commutingAdj J ≤
      fun M N : Subgroup G => N ∈ CFSG.ClassicalInvolution.conjugateSet J ∧ Commutes M N :=
    fun _ _ hMN => ⟨hMN.2.1, fun x hx y hy => hMN.2.2.2 x hx y hy⟩
  exact Relation.ReflTransGen.mono hle L L' (h L hL L' hL')

omit [Finite G] in
theorem omegaConnected_range_conjSub {J : Subgroup G}
    (h : CFSG.ClassicalInvolution.DeltaConnected J) :
    OmegaConnected (Set.range fun g : G => conjSub g J) := by
  have hset : Set.range (fun g : G => conjSub g J) = CFSG.ClassicalInvolution.conjugateSet J := by
    ext L
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [conjSub]⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [conjSub]⟩
  rw [hset]
  exact omegaConnected_of_deltaConnected h

end Connected

end CFSG.ClassicalInvolution.Generic.DeltaClosure
