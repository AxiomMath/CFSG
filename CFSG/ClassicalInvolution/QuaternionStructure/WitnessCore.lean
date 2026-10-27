module

public import CFSG.ClassicalInvolution.QuaternionStructure.Structure
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreSubgroup
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs

public section

namespace CFSG.ClassicalInvolution.QuaternionStructure

open CFSG CFSG.GorensteinWalter
open scoped MatrixGroups

universe u v

theorem classicalInvolutionOddCore_eq_oddCore (H : Type*) [Group H] :
    CFSG.Open.classicalInvolutionOddCore H = oddCore H := rfl

@[expose] def slRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) := by
  let f : SL(2, R) →* SL(2, S) := Matrix.SpecialLinearGroup.map e.toRingHom
  let g : SL(2, S) →* SL(2, R) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  refine MonoidHom.toMulEquiv f g ?_ ?_
  · ext x i j
    simp [f, g]
  · ext x i j
    simp [f, g]

theorem odd_natCard_of_ringChar_ne_two (F : Type*) [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    Odd (Nat.card F) := by
  have : Fintype F := Fintype.ofFinite F
  have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  rw [Nat.card_eq_fintype_card, hn]
  exact (hp.odd_of_ne_two hF).pow

theorem exists_witness_of_normal_specialLinear {G : Type u} [Group G] [Finite G] (J : Subgroup G)
    (M : Subgroup (J ⧸ oddCore J)) [M.Normal] {F : Type v} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) (e : M ≃* SL(2, F)) :
    ∃ J' : Subgroup G, J' ≤ J ∧ (J'.subgroupOf J).Normal ∧
      CFSG.Open.classicalInvolutionWitness J' ∧
      ∃ S' : Sylow 2 J', ∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((S' : Subgroup J') ≃* QuaternionGroup (2 ^ (r - 2))) := by
  classical
  let π : J →* J ⧸ oddCore J := QuotientGroup.mk' (oddCore J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let K : Subgroup J := M.comap π
  have hKn : K.Normal := Subgroup.Normal.comap inferInstance π
  have hOK : oddCore J ≤ K := by
    intro x hx
    change π x ∈ M
    have h1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact one_mem _
  let J' : Subgroup G := K.map J.subtype
  have hJ'K : J'.subgroupOf J = K :=
    Subgroup.comap_map_eq_self_of_injective J.subtype_injective K
  let eJ : J' ≃* K := (Subgroup.equivMapOfInjective K J.subtype J.subtype_injective).symm
  let θ : K →* M := (π.comp K.subtype).codRestrict M (fun x => x.2)
  have hθ : Function.Surjective θ := by
    intro m
    obtain ⟨x, hx⟩ := hπ (m : J ⧸ oddCore J)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change π x ∈ M
    rw [hx]
    exact m.2
  have hθker : θ.ker = (oddCore J).subgroupOf K := by
    ext x
    change (θ x = 1) ↔ _
    rw [Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff (x : J)]
    exact Subtype.ext_iff
  let Θ : K →* SL(2, F) := e.toMonoidHom.comp θ
  have hΘ : Function.Surjective Θ := e.surjective.comp hθ
  have hΘker : Θ.ker = (oddCore J).subgroupOf K := by
    rw [← hθker]
    ext x
    change e (θ x) = 1 ↔ θ x = 1
    exact MulEquiv.map_eq_one_iff e
  have hOcoreK : oddCore K = (oddCore J).subgroupOf K := oddCore_eq_subgroupOf K hOK
  let eK : (K ⧸ oddCore K) ≃* SL(2, F) :=
    (QuotientGroup.quotientMulEquivOfEq (hOcoreK.trans hΘker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hΘ)
  have hFodd : Odd (Nat.card F) := odd_natCard_of_ringChar_ne_two F hF
  refine ⟨J', Subgroup.map_subtype_le K, by rw [hJ'K]; exact hKn, Or.inl ?_, ?_⟩
  ·
    have : Fintype F := Fintype.ofFinite F
    have hp : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
    obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
    have hn0 : (n : ℕ) ≠ 0 := n.ne_zero
    have : Fintype (GaloisField (ringChar F) n) := Fintype.ofFinite _
    let eF : F ≃+* GaloisField (ringChar F) n :=
      FiniteField.ringEquivOfCardEq (by
        rw [hn, Fintype.card_eq_nat_card (α := GaloisField (ringChar F) n),
          GaloisField.card _ _ hn0])
    refine ⟨ringChar F, n, hp, hF, n.pos, ⟨?_⟩⟩
    let eQ : (J' ⧸ CFSG.Open.classicalInvolutionOddCore J') ≃* (K ⧸ oddCore K) :=
      QuotientGroup.congr _ _ eJ (oddCore_map_mulEquiv eJ)
    exact (eQ.trans eK).trans (slRingEquiv eF)
  ·
    obtain ⟨S'⟩ : Nonempty (Sylow 2 J') := inferInstance
    obtain ⟨U⟩ : Nonempty (Sylow 2 SL(2, F)) := inferInstance
    let Θ' : J' →* SL(2, F) := Θ.comp eJ.toMonoidHom
    have hΘ' : Function.Surjective Θ' := hΘ.comp eJ.surjective
    have hker' : Odd (Nat.card Θ'.ker) := by
      have h1 : Nat.card Θ'.ker = Nat.card Θ.ker :=
        Nat.card_congr (eJ.toEquiv.subtypeEquiv (fun x => Iff.rfl))
      rw [h1, hΘker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOK).toEquiv]
      exact odd_natCard_oddCore J
    obtain ⟨f⟩ := nonempty_sylow_equiv_of_surjective Θ' hΘ' hker' S' U
    obtain ⟨n, hn3, ⟨q⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion F hFodd U
    exact ⟨S', n, hn3, ⟨f.trans q⟩⟩

theorem exists_witness_of_alt7 {G : Type u} [Group G] [Finite G] (J : Subgroup G) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hcomm : commutator (J ⧸ oddCore J) = ⊤)
    (hsimple : IsSimpleGroup ((J ⧸ oddCore J) ⧸ Subgroup.center (J ⧸ oddCore J)))
    (hcard : Nat.card (Subgroup.center (J ⧸ oddCore J)) = 2)
    (hiso : Nonempty (((J ⧸ oddCore J) ⧸ Subgroup.center (J ⧸ oddCore J)) ≃*
      alternatingGroup (Fin 7))) :
    ∃ J' : Subgroup G, J' ≤ J ∧ (J'.subgroupOf J).Normal ∧
      CFSG.Open.classicalInvolutionWitness J' ∧
      ∃ S' : Sylow 2 J', ∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((S' : Subgroup J') ≃* QuaternionGroup (2 ^ (r - 2))) := by
  refine ⟨J, le_rfl, ?_, Or.inr ⟨⟨hcomm, hsimple⟩, hcard, hiso⟩, S, hS⟩
  rw [Subgroup.subgroupOf_self]
  exact Subgroup.normal_top

theorem exists_witness_of_not_isPGroup_of_hyps (hGW : gorensteinWalterStatement.{u})
    {G : Type u} [Group G] [Finite G] (J : Subgroup G) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hBS : ∀ t ∈ (S : Subgroup J), orderOf t = 2 →
      (QuotientGroup.mk t : J ⧸ oddCore J) ∈ Subgroup.center (J ⧸ oddCore J))
    (hnot : ¬ IsPGroup 2 (J ⧸ CFSG.Open.classicalInvolutionOddCore J)) :
    ∃ J' : Subgroup G, J' ≤ J ∧ (J'.subgroupOf J).Normal ∧
      CFSG.Open.classicalInvolutionWitness J' ∧
      ∃ S' : Sylow 2 J', ∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((S' : Subgroup J') ≃* QuaternionGroup (2 ^ (r - 2))) := by
  obtain ⟨z, -, -, -, hstr⟩ := quaternion_structure_of_hyps hGW S hS hBS
  rcases hstr with h2 | ⟨F, _, _, hF, L, hLn, -, ⟨e⟩⟩ |
      ⟨F, _, _, hF, L, hLn, -, -, -, M, hMn, -, ⟨eM⟩⟩ | ⟨hcomm, hsimple, hcard, hiso⟩
  · exact absurd h2 hnot
  · exact exists_witness_of_normal_specialLinear J L hF e
  · exact exists_witness_of_normal_specialLinear J M hF eM
  · exact exists_witness_of_alt7 J S hS hcomm hsimple hcard hiso

end CFSG.ClassicalInvolution.QuaternionStructure
