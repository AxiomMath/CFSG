module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf44Loc
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43HsStab

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

section Block

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem aStar_eq_of_mem_aStar {L M : Subgroup G} (hL : L ∈ Ω) (hM : M ∈ aStar Ω L) :
    aStar Ω M = aStar Ω L := by
  exact Set.Subset.antisymm (aStar_subset_aStar_of_mem hM)
    (aStar_subset_aStar_of_mem (mem_aStar_symm hL hM).2)

theorem aStar_ne_of_not_mem {L M : Subgroup G} (hM : M ∉ aStar Ω L) : aStar Ω M ≠ aStar Ω L := by
  intro h
  apply hM
  rw [← h]
  exact Relation.ReflTransGen.refl

theorem conjSub_mem_aStar_conjSub_iff (hΩ : ConjInvariant Ω) {L M : Subgroup G} (g : G) :
    conjSub g M ∈ aStar Ω (conjSub g L) ↔ M ∈ aStar Ω L := by
  constructor
  · intro h
    have := aStar_conj hΩ h g⁻¹
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  · intro h
    exact aStar_conj hΩ h g

theorem normalizer_le_conjStab_aStar (hΩ : ConjInvariant Ω) {L M : Subgroup G} (hL : L ∈ Ω)
    (hM : M ∈ aStar Ω L) : Subgroup.normalizer (M : Set G) ≤ conjStab (aStar Ω L) := by
  exact fun _ hx => mem_conjStab_aStar hΩ hL hM (conjSub_eq_of_mem_normalizer hx)

theorem mem_aStar_of_twin {L M Q : Subgroup G} {w : G} (hM : M ∈ aStar Ω L) (hQ : Q ∈ Ω)
    (hwM : IsUniqueInvolution M w) (hwQ : IsUniqueInvolution Q w) : Q ∈ aStar Ω L := by
  by_cases h : Q = M
  · rw [h]
    exact hM
  · exact hM.tail ⟨hQ, Or.inr (Or.inr ⟨⟨hQ, w, hwM, hwQ⟩, h⟩)⟩

theorem mem_aStar_of_aViol {L J : Subgroup G} {zL zJ : G} (hv : AViol Ω L J zL zJ) :
    J ∈ aStar Ω L := by
  exact Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨zL, zJ, hv⟩⟩

theorem aViol_involution_ne [Finite G] (hΩ : HypOmegaGen Ω) {L J : Subgroup G} {zL zJ : G}
    (hL : L ∈ Ω) (hv : AViol Ω L J zL zJ) : zJ ≠ zL := by
  intro h
  exact hv.not_nbr (Q3CL.T3.twin_mem_omegaNbr hΩ hL hv.mem hv.ne hv.hzK (h ▸ hv.hzJ))

theorem conjStab_aStar_ne_top {K : Subgroup G} (hΩ : ConjInvariant (CoreAssembly.conjClass K))
    (hne : aStar (CoreAssembly.conjClass K) K ≠ CoreAssembly.conjClass K) {L : Subgroup G}
    (hL : L ∈ CoreAssembly.conjClass K) :
    conjStab (aStar (CoreAssembly.conjClass K) L) ≠ ⊤ := by
  obtain ⟨g, rfl⟩ := hL
  intro htop
  have htop' : conjStab (aStar (CoreAssembly.conjClass K) (conjSub g K)) = ⊤ := htop
  apply hne
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  refine Set.Subset.antisymm (fun M hM => mem_of_mem_aStar hK hM) ?_
  rintro _ ⟨h, rfl⟩
  have hx : g * h * g⁻¹ ∈ conjStab (aStar (CoreAssembly.conjClass K) (conjSub g K)) := by
    rw [htop']
    exact Subgroup.mem_top _
  have h1 := (mem_conjStab_iff.mp hx (conjSub g K)).mpr Relation.ReflTransGen.refl
  have e : conjSub (g * h * g⁻¹) (conjSub g K) = conjSub g (conjSub h K) := by
    rw [← conjSub_mul, ← conjSub_mul, show g * h * g⁻¹ * g = g * h by group]
  rw [e] at h1
  exact (conjSub_mem_aStar_conjSub_iff hΩ g).mp h1

theorem exists_aViol_of_mem_conjClass {K J : Subgroup G} {zK zJ : G}
    (hΩ : ConjInvariant (CoreAssembly.conjClass K))
    (hv : AViol (CoreAssembly.conjClass K) K J zK zJ)
    {L : Subgroup G} (hL : L ∈ CoreAssembly.conjClass K) :
    ∃ J' : Subgroup G, ∃ zL zJ' : G, AViol (CoreAssembly.conjClass K) L J' zL zJ' := by
  obtain ⟨g, rfl⟩ := hL
  exact ⟨_, _, _, hv.conj hΩ g⟩

theorem le_oddCoreOf_sup_of_isSylow2In [Finite G] {P R : Subgroup G}
    (h2 : IsPGroup 2 (↥P ⧸ classicalInvolutionOddCore ↥P)) (hR : IsSylow2In R P) :
    P ≤ oddCoreOf P ⊔ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (oddCoreOf P ⊔ R).relIndex P ∣ R.relIndex P :=
    Subgroup.relIndex_dvd_of_le_left P le_sup_right
  have h2' : (oddCoreOf P ⊔ R).relIndex P ∣ (oddCoreOf P).relIndex P :=
    Subgroup.relIndex_dvd_of_le_left P le_sup_left
  have hodd : ¬ 2 ∣ R.relIndex P := Sylow.not_dvd_index (Asc77.T3.sylowOfIsSylow2In hR)
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hidx : (oddCoreOf P).relIndex P = 2 ^ n := by
    rw [← hn, ← Subgroup.index_eq_card]
    unfold Subgroup.relIndex oddCoreOf
    rw [subgroupOf_map_subtype']
  rw [hidx] at h2'
  have hcop : Nat.Coprime ((oddCoreOf P ⊔ R).relIndex P) (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun h => hodd (h.trans h1)))
  exact Subgroup.relIndex_eq_one.mp (Nat.Coprime.eq_one_of_dvd hcop h2')

theorem commutator_le_oddCoreOf_sup_inf_of_subgroupOf {X A B : Subgroup G} (hA : A ≤ X)
    (hB : B ≤ X)
    (h : ⁅A.subgroupOf X, B.subgroupOf X⁆ ≤
      (oddCoreOf (A.subgroupOf X) ⊔ classicalInvolutionOddCore ↥X) ⊓
        (oddCoreOf (B.subgroupOf X) ⊔ classicalInvolutionOddCore ↥X)) :
    ⁅A, B⁆ ≤ (oddCoreOf A ⊔ oddCoreOf X) ⊓ (oddCoreOf B ⊔ oddCoreOf X) := by
  have h1 := Subgroup.map_mono (f := X.subtype) h
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB] at h1
  refine h1.trans ((Subgroup.map_inf_le _ _ _).trans ?_)
  rw [Subgroup.map_sup, Subgroup.map_sup, oddCoreOf_subgroupOf hA, oddCoreOf_subgroupOf hB,
    Subgroup.map_subgroupOf_eq_of_le ((oddCoreOf_le_self A).trans hA),
    Subgroup.map_subgroupOf_eq_of_le ((oddCoreOf_le_self B).trans hB)]
  exact le_rfl

end Block

section Restrict

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

private theorem restrict_thm3_data (hΩ : TypeRHyp Ω) (hb : Thm3A.Thm3RBelowG (Nat.card G))
    {X L J M : Subgroup G} {zL zJ : G} (hX : X ≠ ⊤) (hL : L ∈ Ω) (hLX : L ≤ X) (hJX : J ≤ X)
    (hv : AViol Ω L J zL zJ) (hM : M ∈ Ω) (hMX : M ≤ X) (hMB : M ∉ aStar Ω L) :
    Thm3A.Thm3RGroupQuotG ↥X ∧ TypeRHyp (restrictFamily Ω X) ∧
      L.subgroupOf X ∈ restrictFamily Ω X ∧ ¬ AEmpty (restrictFamily Ω X) (L.subgroupOf X) ∧
      M.subgroupOf X ∈ restrictFamily Ω X ∧
      M.subgroupOf X ∉ aStar (restrictFamily Ω X) (L.subgroupOf X) := by
  have hlt : Nat.card ↥X < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group X)
      (fun h => hX ((Subgroup.card_eq_iff_eq_top X).mp h))
  refine ⟨Thm3A.thm3RGroupQuotG_of_belowG hb hlt, hΩ.restrict X,
    subgroupOf_mem_restrictFamily hL hLX,
    not_aEmpty_iff.mpr ⟨J.subgroupOf X, _, _, aViol_restrict_gen hΩ.hyp hLX hJX hv⟩,
    subgroupOf_mem_restrictFamily hM hMX, fun h => hMB ?_⟩
  have h1 := mem_aStar_of_restrict_gen hΩ.hyp hLX h
  rwa [Subgroup.map_subgroupOf_eq_of_le hMX] at h1

theorem comm_of_le_of_aViol (hΩ : TypeRHyp Ω) (hb : Thm3A.Thm3RBelowG (Nat.card G))
    {X L J M : Subgroup G} {zL zJ : G} (hX : X ≠ ⊤) (hL : L ∈ Ω) (hLX : L ≤ X) (hJX : J ≤ X)
    (hv : AViol Ω L J zL zJ) (hM : M ∈ Ω) (hMX : M ≤ X) (hMB : M ∉ aStar Ω L) :
    ⁅M, L⁆ ≤ (oddCoreOf M ⊔ oddCoreOf X) ⊓ (oddCoreOf L ⊔ oddCoreOf X) := by
  obtain ⟨hQ, hΦ, hLΦ, hnA, hMΦ, hMA⟩ := restrict_thm3_data hΩ hb hX hL hLX hJX hv hM hMX hMB
  exact commutator_le_oddCoreOf_sup_inf_of_subgroupOf hMX hLX
    (Thm3A.thm3R_comm_mod hQ hΦ hLΦ hnA hMΦ hMA Relation.ReflTransGen.refl)

theorem exists_conj_omegaNbr_of_le_of_aViol (hΩ : TypeRHyp Ω)
    (hb : Thm3A.Thm3RBelowG (Nat.card G)) {X L J M : Subgroup G} {zL zJ : G} (hX : X ≠ ⊤)
    (hL : L ∈ Ω) (hLX : L ≤ X) (hJX : J ≤ X) (hv : AViol Ω L J zL zJ) (hM : M ∈ Ω)
    (hMX : M ≤ X) (hMB : M ∉ aStar Ω L) :
    ∀ R : Subgroup G, IsSylow2In R M → ∃ n ∈ oddCoreOf X,
      R ≤ Subgroup.normalizer ((conjSub n L : Subgroup G) : Set G) ∧ conjSub n L ∈ aStar Ω L := by
  obtain ⟨hQ, hΦ, hLΦ, hnA, hMΦ, hMA⟩ := restrict_thm3_data hΩ hb hX hL hLX hJX hv hM hMX hMB
  intro R hR
  have hRX : R ≤ X := hR.1.trans hMX
  have hRs : IsSylow2In (R.subgroupOf X) (M.subgroupOf X) := by
    rw [← isSylow2In_map_subtype_iff, Subgroup.map_subgroupOf_eq_of_le hRX,
      Subgroup.map_subgroupOf_eq_of_le hMX]
    exact hR
  obtain ⟨n, hn, hRn, hnA'⟩ :=
    (Thm3A.thm3R_lift_stab hQ hΦ hLΦ hnA hMΦ hMA Relation.ReflTransGen.refl).2 _ hRs
  have hnLX : conjSub (n : G) L ≤ X := by
    have := conjSub_mono (n := (n : G)) hLX
    rwa [conjSub_eq_self_of_mem n.2] at this
  refine ⟨(n : G), Subgroup.mem_map_of_mem X.subtype hn, ?_, ?_⟩
  · have h1 := Asc77.map_le_normalizer_map hRn
    rwa [Subgroup.map_subgroupOf_eq_of_le hRX, conjSub_subgroupOf,
      Subgroup.map_subgroupOf_eq_of_le hnLX] at h1
  · have h1 := mem_aStar_of_restrict_gen hΩ.hyp hLX hnA'
    rwa [conjSub_subgroupOf, Subgroup.map_subgroupOf_eq_of_le hnLX] at h1

end Restrict

namespace FrameStd

variable {T : Type} [Group T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}

theorem hyp (hs : FrameStd K z J zJ) : HypOmegaGen (CoreAssembly.conjClass K) := hs.datum.hyp

theorem typeRHyp (hs : FrameStd K z J zJ) : TypeRHyp (CoreAssembly.conjClass K) :=
  typeRHyp_of_datum hs.datum

theorem tightCore_eq (hs : FrameStd K z J zJ) {P : Subgroup T}
    (hP : P ∈ CoreAssembly.conjClass K) : tightCore P = P :=
  tightCore_eq_of_mem_conjClass hs.datum hP

theorem conjStab_ne_top (hs : FrameStd K z J zJ) {L : Subgroup T}
    (hL : L ∈ CoreAssembly.conjClass K) : conjStab (aStar (CoreAssembly.conjClass K) L) ≠ ⊤ :=
  conjStab_aStar_ne_top hs.hyp.conjInvariant hs.ne hL

theorem exists_aViol (hs : FrameStd K z J zJ) {L : Subgroup T}
    (hL : L ∈ CoreAssembly.conjClass K) :
    ∃ J' : Subgroup T, ∃ zL zJ' : T, AViol (CoreAssembly.conjClass K) L J' zL zJ' :=
  exists_aViol_of_mem_conjClass hs.hyp.conjInvariant hs.viol hL

end FrameStd

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
