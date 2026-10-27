module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIX
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K K' S V : Subgroup G} {z : G}

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hA hB ⊢
  rw [conjSub_sup', hA, hB]

namespace Twin20

theorem hz' (d : Twin20 Ω K K' z S V) : IsUniqueInvolution K' z := by
  have hK' : K' ∈ twinSet Ω K := by rw [d.htw]; exact Or.inr rfl
  obtain ⟨-, z', hzK, hzK'⟩ := hK'
  have e := d.hz.eq hzK
  subst e
  exact hzK'

theorem hVX (d : Twin20 Ω K K' z S V) : V ≤ sec20X Ω z K K' :=
  le_trans (le_iSup₂ (f := fun (U : Subgroup G) (_ : U ∈ {U : Subgroup G | U ∈ USet Ω ∧
    U ≤ Subgroup.centralizer ({z} : Set G)}) => U) V ⟨d.hV, d.hVS.trans d.hSz⟩)
    (le_trans le_sup_left le_sup_left)

end Twin20

theorem le_sec20X_left : K ≤ sec20X Ω z K K' := le_trans le_sup_right le_sup_left

theorem le_sec20X_right : K' ≤ sec20X Ω z K K' := le_sup_right

theorem le_sec20X_pair : K ⊔ K' ≤ sec20X Ω z K K' := sup_le le_sec20X_left le_sec20X_right

section Finite

variable [Finite G]

omit [Finite G] in
theorem sec20X_le_normalizer_oddCore :
    sec20X Ω z K K' ≤ Subgroup.normalizer (oddCoreOf (sec20X Ω z K K') : Set G) :=
  fun _ hg => mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hg)

namespace Twin20

variable (d : Twin20 Ω K K' z S V)
include d

omit [Finite G] in
theorem V_le_normalizer_N1 :
    V ≤ Subgroup.normalizer ((oddCoreOf (sec20X Ω z K K') ⊔ (K ⊔ K') : Subgroup G) : Set G) := by
  intro v hv
  refine mem_normalizer_sup (sec20X_le_normalizer_oddCore (d.hVX hv)) ?_
  exact le_normalizer_sup_pair d.hΩ d.hz d.htw d.hne (d.hSz (d.hVS hv))

omit [Finite G] in
theorem X_le_normalizer_N1
    (c3 : sec20X Ω z K K' = oddCoreOf (sec20X Ω z K K') ⊔ (V ⊔ (K ⊔ K'))) :
    sec20X Ω z K K' ≤
      Subgroup.normalizer ((oddCoreOf (sec20X Ω z K K') ⊔ (K ⊔ K') : Subgroup G) : Set G) := by
  have hN : (oddCoreOf (sec20X Ω z K K') ⊔ (K ⊔ K') : Subgroup G) ≤
      Subgroup.normalizer ((oddCoreOf (sec20X Ω z K K') ⊔ (K ⊔ K') : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  exact (Eq.le c3).trans (sup_le (le_trans le_sup_left hN)
    (sup_le d.V_le_normalizer_N1 (le_trans le_sup_right hN)))

theorem sec20O2_sup_eq
    (c3 : sec20X Ω z K K' = oddCoreOf (sec20X Ω z K K') ⊔ (V ⊔ (K ⊔ K'))) :
    K ⊔ K' ⊔ sec20O2 (sec20X Ω z K K') = oddCoreOf (sec20X Ω z K K') ⊔ (K ⊔ K') := by
  apply le_antisymm
  · refine sup_le le_sup_right ?_
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxX, hxodd⟩
    have hxV : x ∈ (oddCoreOf (sec20X Ω z K K') ⊔ (K ⊔ K')) ⊔ V := by
      have h1 : sec20X Ω z K K' ≤ (oddCoreOf (sec20X Ω z K K') ⊔ (K ⊔ K')) ⊔ V :=
        (Eq.le c3).trans (sup_le (le_trans le_sup_left le_sup_left)
          (sup_le le_sup_right (le_trans le_sup_right le_sup_left)))
      exact h1 hxX
    exact mem_of_odd_orderOf_of_mem_sup d.hV2 d.V_le_normalizer_N1 hxV hxodd
  · refine sup_le ?_ le_sup_left
    refine le_trans ?_ le_sup_right
    intro x hx
    refine Subgroup.subset_closure ⟨oddCoreOf_le_self _ hx, ?_⟩
    exact (oddCoreOf_odd_natCard (sec20X Ω z K K')).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ hx)

theorem oddCoreOf_sup_eq
    (c3 : sec20X Ω z K K' = oddCoreOf (sec20X Ω z K K') ⊔ (V ⊔ (K ⊔ K'))) :
    oddCoreOf (oddCoreOf (sec20X Ω z K K') ⊔ (K ⊔ K')) = oddCoreOf (sec20X Ω z K K') := by
  have hN1X : (oddCoreOf (sec20X Ω z K K') ⊔ (K ⊔ K') : Subgroup G) ≤ sec20X Ω z K K' :=
    sup_le (oddCoreOf_le_self _) le_sec20X_pair
  apply le_antisymm
  · have hnorm : sec20X Ω z K K' ≤ Subgroup.normalizer
        (oddCoreOf (oddCoreOf (sec20X Ω z K K') ⊔ (K ⊔ K')) : Set G) :=
      fun g hg => mem_normalizer_oddCore_of_mem_normalizer (d.X_le_normalizer_N1 c3 hg)
    exact le_oddCoreIn_of_normalizes ((oddCoreOf_le_self _).trans hN1X) hnorm
      (oddCoreOf_odd_natCard _)
  · exact le_oddCoreIn_of_normalizes le_sup_left (hN1X.trans sec20X_le_normalizer_oddCore)
      (oddCoreOf_odd_natCard _)

theorem oddCoreOf_pair_le
    (c3 : sec20X Ω z K K' = oddCoreOf (sec20X Ω z K K') ⊔ (V ⊔ (K ⊔ K'))) :
    oddCoreOf (K ⊔ K') ≤ oddCoreOf (sec20X Ω z K K') := by
  have hMN : oddCoreOf (K ⊔ K') ≤ Subgroup.normalizer (oddCoreOf (sec20X Ω z K K') : Set G) :=
    fun _ hg => sec20X_le_normalizer_oddCore (le_sec20X_pair (oddCoreOf_le_self _ hg))
  have hodd := Bootstrap.odd_card_sup_of_le_normalizer hMN (oddCoreOf_odd_natCard (K ⊔ K'))
    (oddCoreOf_odd_natCard (sec20X Ω z K K'))
  have hQX : (oddCoreOf (K ⊔ K') ⊔ oddCoreOf (sec20X Ω z K K') : Subgroup G) ≤
      sec20X Ω z K K' := sup_le ((oddCoreOf_le_self _).trans le_sec20X_pair) (oddCoreOf_le_self _)
  have hQN : (oddCoreOf (K ⊔ K') ⊔ oddCoreOf (sec20X Ω z K K') : Subgroup G) ≤
      Subgroup.normalizer ((oddCoreOf (K ⊔ K') ⊔ oddCoreOf (sec20X Ω z K K') : Subgroup G) :
        Set G) := Subgroup.le_normalizer
  have hnorm : sec20X Ω z K K' ≤ Subgroup.normalizer
      ((oddCoreOf (K ⊔ K') ⊔ oddCoreOf (sec20X Ω z K K') : Subgroup G) : Set G) := by
    refine (Eq.le c3).trans (sup_le (le_trans le_sup_right hQN) (sup_le ?_ ?_))
    · intro v hv
      refine mem_normalizer_sup ?_ (sec20X_le_normalizer_oddCore (d.hVX hv))
      exact mem_normalizer_oddCore_of_mem_normalizer
        (le_normalizer_sup_pair d.hΩ d.hz d.htw d.hne (d.hSz (d.hVS hv)))
    · intro m hm
      exact mem_normalizer_sup (mem_normalizer_oddCore_of_mem_normalizer
        (Subgroup.le_normalizer hm)) (sec20X_le_normalizer_oddCore (le_sec20X_pair hm))
  exact le_trans le_sup_left (le_oddCoreIn_of_normalizes hQX hnorm hodd)

end Twin20

omit [Finite G] in
theorem commutatorElement_mul_right' (u a b : G) :
    ⁅u, a * b⁆ = ⁅u, a⁆ * (a * ⁅u, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def]
  group

end Finite

variable (p f : ℕ) [Fact p.Prime]

theorem c20_7 : C20_7 p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5
  have hp := d.branch.odd
  have hV2 : IsPGroup 2 V := d.hyp.isPGroup_of_mem_USet hp d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  have c3' : sec20X (CoreAssembly.conjClass K) z K K' =
      oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K')) := c3
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hRmem : R ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hKΩ d.hR
  have h8 := d.hyp.eight_le_of_mem_RSet hp hRmem
  have hzR : z ∈ R := mem_of_isPGroup d.viol.hzK d.hR.1 d.hR.2.1 (by omega)
  have hzS : z ∈ (S : Subgroup G) := d.hRS hzR
  have hzM : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr
      (d.viol.hzK.commute_of_mem hw).symm)
      (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (tw.hz'.commute_of_mem hw).symm)
  have hzMem : z ∈ K ⊔ K' := Subgroup.mem_sup_left d.viol.hzK.mem
  show centralizerModOdd (S : Subgroup G) (K ⊔ K') = Subgroup.zpowers z
  apply le_antisymm
  · intro u hu
    obtain ⟨huS, huM, huOM, hucomm⟩ := hu
    have huX : u ∈ Subgroup.normalizer
        (sec20X (CoreAssembly.conjClass K) z K K' : Set G) :=
      le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins (d.hSz huS)
    have huOX := mem_normalizer_oddCore_of_mem_normalizer huX
    have hL := tw.sec20O2_sup_eq c3'
    have hOL := tw.oddCoreOf_sup_eq c3'
    have hOM := tw.oddCoreOf_pair_le c3'
    have hu5 : u ∈ centralizerModOdd (S : Subgroup G)
        (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K')) := by
      rw [hL]
      refine ⟨huS, mem_normalizer_sup huOX huM, ?_, ?_⟩
      · rw [hOL]
        exact huOX
      · intro l hl
        rw [hOL]
        rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
          (fun m hm => sec20X_le_normalizer_oddCore (le_sec20X_pair hm))] at hl
        obtain ⟨a, ha, b, hb, rfl⟩ := hl
        rw [commutatorElement_mul_right']
        refine (oddCoreOf _).mul_mem ?_ ((oddCoreOf _).mul_mem
          ((oddCoreOf _).mul_mem ha (hOM (hucomm b hb))) ((oddCoreOf _).inv_mem ha))
        have h1 := mem_normalizer_oddCoreOf_of_mem_normalizer huX ha
        rw [commutatorElement_def]
        exact (oddCoreOf _).mul_mem h1 ((oddCoreOf _).inv_mem ha)
    rw [c5] at hu5
    exact hu5
  · refine Subgroup.zpowers_le.mpr ⟨hzS, Subgroup.le_normalizer hzMem,
      mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hzMem), ?_⟩
    intro l hl
    have := commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hzM hl)).symm
    rw [this]
    exact (oddCoreOf _).one_mem

end CFSG.ClassicalInvolution.Asc77.T3CII
