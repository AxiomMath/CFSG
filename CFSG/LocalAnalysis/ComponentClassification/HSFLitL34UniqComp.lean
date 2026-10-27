module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvL2
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvTools

public section

namespace CFSG.ComponentClassification.HSFLit.L34Uniq

open CFSG Subgroup Equiv CFSG.GH74.KGroups CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
  CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.HSFLit.L34Inv
  CFSG.ComponentClassification.HSFLit.AutL2
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mem_two_of_odd {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x : G} (hxQ : x ∈ Q)
    (hx : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨x, hxQ⟩
  have h1 : orderOf x ∣ 2 ^ k := by
    have := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases j with _ | j
  · simpa using hj
  · rw [hj] at hx
    exact absurd hx (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, by omega⟩))

theorem exists_fourth_conjugate {S K : Subgroup G} (hS : IsPGroup 2 S) {s₂ s₃ : G} (hs₂ : s₂ ∈ S)
    (hs₃ : s₃ ∈ S) (h₂ : conjugate K s₂ ≠ K) (h₃ : conjugate K s₃ ≠ K)
    (h₂₃ : conjugate K s₃ ≠ conjugate K s₂) :
    ∃ s₄ ∈ S, conjugate K s₄ ≠ K ∧ conjugate K s₄ ≠ conjugate K s₂ ∧
      conjugate K s₄ ≠ conjugate K s₃ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction ↥S (Subgroup G) :=
    { smul := fun s H => conjugate H (s : G)⁻¹
      one_smul := fun H => by
        show conjugate H ((1 : ↥S) : G)⁻¹ = H
        rw [OneMemClass.coe_one, inv_one]
        exact conjugate_one H
      mul_smul := fun s s' H => by
        show conjugate H ((s * s' : ↥S) : G)⁻¹ = conjugate (conjugate H (s' : G)⁻¹) (s : G)⁻¹
        rw [conjugate_conjugate'', Subgroup.coe_mul, mul_inv_rev] }
  have hsmul : ∀ s : ↥S, s • K = conjugate K (s : G)⁻¹ := fun _ => rfl
  have hmem : ∀ g ∈ S, conjugate K g ∈ MulAction.orbit ↥S K := fun g hg =>
    MulAction.mem_orbit_iff.mpr ⟨⟨g⁻¹, inv_mem hg⟩, by rw [hsmul, inv_inv]⟩
  have hidx := MulAction.index_stabilizer ↥S K
  obtain ⟨n, hn⟩ := (hS.of_equiv (MulEquiv.refl _)).exists_card_eq
  have hdvd : (MulAction.stabilizer ↥S K).index ∣ 2 ^ n := hn ▸ Subgroup.index_dvd_card _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hk] at hidx
  have hfin : (MulAction.orbit ↥S K).Finite := Set.toFinite _
  have h3 : 3 ≤ (MulAction.orbit ↥S K).ncard := by
    have hsub : ({K, conjugate K s₂, conjugate K s₃} : Set (Subgroup G)) ⊆
        MulAction.orbit ↥S K := by
      intro H hH
      rcases hH with h | h | h
      · rw [h]; exact MulAction.mem_orbit_self K
      · rw [h]; exact hmem s₂ hs₂
      · rw [Set.mem_singleton_iff.mp h]; exact hmem s₃ hs₃
    have h1 := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_eq_three.mpr ⟨K, conjugate K s₂, conjugate K s₃, h₂.symm, h₃.symm, h₂₃.symm,
      rfl⟩] at h1
    exact h1
  have h4 : 4 ≤ (MulAction.orbit ↥S K).ncard := by
    rw [← hidx] at h3 ⊢
    rcases k with _ | _ | k
    · norm_num at h3
    · norm_num at h3
    · rw [pow_succ, pow_succ]
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
  by_contra hcon
  push Not at hcon
  have hsub : MulAction.orbit ↥S K ⊆ ({K, conjugate K s₂, conjugate K s₃} : Set (Subgroup G)) := by
    intro H hH
    obtain ⟨s, rfl⟩ := MulAction.mem_orbit_iff.mp hH
    rw [hsmul]
    by_cases ha : conjugate K (s : G)⁻¹ = K
    · exact Or.inl ha
    by_cases hb : conjugate K (s : G)⁻¹ = conjugate K s₂
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (hcon _ (inv_mem s.2) ha hb))
  have h5 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h6 : ({K, conjugate K s₂, conjugate K s₃} : Set (Subgroup G)).ncard ≤ 3 :=
    (Set.ncard_insert_le _ _).trans (Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans
      (by rw [Set.ncard_singleton])))
  omega

theorem conj_component
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) {u : G} (hu : u ∈ L34UnbalancingSet L t S)
    (huc : ∀ s ∈ S, s * u = u * s) {K : Subgroup G} (hKu : K ≤ centralizer ({u} : Set G))
    (hKp : IsPComponent 2 (K.subgroupOf (centralizer ({u} : Set G))))
    (hKn : ¬ ⁅K, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K) {s : G} (hs : s ∈ S) :
    conjugate K s ≤ centralizer ({u} : Set G) ∧
      IsPComponent 2 ((conjugate K s).subgroupOf (centralizer ({u} : Set G))) ∧
      ¬ ⁅conjugate K s, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn (conjugate K s) := by
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hsu : s ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr (huc s hs)
  obtain ⟨h1, h2⟩ := GSThmB.isPComponent_conjugate_centralizer_singleton hKu hKp hsu
  obtain ⟨-, -, -, h54⟩ := l34Notation54_of_inputs hS hU hheld hSol hGW hMax G L t S T hset u hu
  have hsN : s ∈ normalizer ((l34K L u : Subgroup G) : Set G) :=
    h54 (mem_inf.mpr ⟨hsu, mem_centralizer_singleton_iff.mpr (hZS s hs)⟩)
  have hle : conjugate K s ≤ l34K L u := by
    rw [← conjugate_eq_self hsN]
    exact map_mono (le_l34K hKu hKp hKn)
  exact ⟨h1, h2, not_commutator_le_of_le_l34K hle h1 h2⟩

theorem le_coreActionKernel_of_ne {C K K' : Subgroup G} (hKC : K ≤ C) (hK'C : K' ≤ C)
    (hK : IsPComponent 2 (K.subgroupOf C)) (hK' : IsPComponent 2 (K'.subgroupOf C))
    (hne : K ≠ K') : K' ≤ coreActionKernel K := by
  intro g hg
  obtain ⟨-, hN⟩ := commutator_le_of_ne hKC hK'C hK hK' hne
  have h1 := commutator_le_inf_oddIn hKC hK'C hK hK' hne
  refine mem_coreActionKernel.mpr ⟨hN hg, fun j hj => ?_⟩
  have h2 : ⁅j⁻¹, g⁻¹⁆ ∈ ⁅K, K'⁆ := commutator_mem_commutator (inv_mem hj) (inv_mem hg)
  have h3 := (h1 h2).1
  rwa [commutatorElement_def, inv_inv, inv_inv] at h3

theorem commute_of_ne {C K K' S : Subgroup G} (hKC : K ≤ C) (hK'C : K' ≤ C)
    (hK : IsPComponent 2 (K.subgroupOf C)) (hK' : IsPComponent 2 (K'.subgroupOf C))
    (hne : K ≠ K') (hS : IsPGroup 2 S) {x y : G} (hxS : x ∈ S) (hxK : x ∈ K) (hyS : y ∈ S)
    (hyK' : y ∈ K') : x * y = y * x := by
  have h1 := commutator_le_inf_oddIn hKC hK'C hK hK' hne
  have h2 : ⁅x, y⁆ ∈ oddIn K := (h1 (commutator_mem_commutator hxK hyK')).1
  have h3 : ⁅x, y⁆ ∈ S := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxS hyS) (inv_mem hxS)) (inv_mem hyS)
  have hodd : Odd (Nat.card (oddIn K)) := by
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have h4 : ⁅x, y⁆ = 1 := eq_one_of_mem_two_of_odd hS h3
    (Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ h2))
  exact commutatorElement_eq_one_iff_mul_comm.mp h4

theorem odd_orderOf_inner_l2
    {K : Subgroup G}
    (htype : IsL2Type 5 (K ⧸ pPrimeCore 2 K) ∨ IsL2Type 7 (K ⧸ pPrimeCore 2 K)) {c : G}
    (hc : c ∈ K) (hcK : c ∈ coreActionKernel K) : Odd (orderOf c) := by
  obtain ⟨n, M, hF, -⟩ := exists_l2Model' htype
  have h1 := (rhoHom_eq_one_iff M ⟨c, le_normalizer hc⟩).mpr hcK
  have h2 := mem_oddIn_of_rhoHom M hF.le hc h1
  have hoddO : Odd (Nat.card (oddIn K)) := by
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact Odd.of_dvd_nat hoddO (Subgroup.orderOf_dvd_natCard _ h2)

end CFSG.ComponentClassification.HSFLit.L34Uniq
