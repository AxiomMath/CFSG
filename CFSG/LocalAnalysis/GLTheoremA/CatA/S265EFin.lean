module

public import CFSG.Blueprint.LieModelAPI
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4OuterSigma
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescSzFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived Outer inner)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

section Pure

private theorem s265e_fin_commutator_le_inner {Y : Type} [Group Y] (hY : IsCyclic (Outer Y)) :
    commutator (MulAut Y) ≤ inner Y := by
  haveI := hY
  have hc : ∀ a b : Outer Y, a * b = b * a := isMulCommutative_iff.1 inferInstance
  rw [commutator_def, Subgroup.commutator_le]
  intro g _ h _
  refine (QuotientGroup.eq_one_iff _).1 ?_
  have e1 : (QuotientGroup.mk g : Outer Y) * QuotientGroup.mk h =
      QuotientGroup.mk h * QuotientGroup.mk g := hc _ _
  simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [e1]
  group

end Pure

section SzBasic


private theorem s265e_fin_center_suzuki {X : Type} [Group X] {f : ℕ}
    (hS : SuzukiModel X 2 f) : Subgroup.center X = ⊥ := by
  obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ := hS
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨-, hnt, hsimp⟩ := CFSG.LieType.Ree.suzuki_simple (K := K) ha hK'
  obtain ⟨x, y, hxy⟩ := HDesc.exists_noncomm_of_commutator_eq_top
    (CFSG.LieType.Ree.suzuki_perfect (K := K) ha hK').1
  haveI := hsimp
  haveI := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    apply hxy
    have h1 := Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top (e.symm x)) (e.symm y)
    have h2 := congrArg e h1
    simpa using h2.symm

private theorem s265e_fin_card_sz32 {R : Type} [Group R] (hM : SuzukiModel R 2 5) :
    Nat.card R = 32537600 := by
  obtain ⟨-, a, -, F, _, _, hf, hF, ⟨e'⟩⟩ := hM
  have ha : a = 2 := by omega
  subst ha
  rw [Nat.card_congr e'.toEquiv, CFSG.LieType.Ree.suzuki_order hF]
  norm_num

end SzBasic

section Sz


theorem s265e_fin_sz {X : Type} [Group X] [Finite X] (hS : SuzukiModel X 2 5)
    {A : Subgroup (MulAut X)} (hA : IsElemAbelian 5 A) : Nat.card A ≤ 5 ^ 2 := by
  have hZ : Subgroup.center X = ⊥ := s265e_fin_center_suzuki hS
  have h1 := HDesc.card_le_prime_mul_inf_inner Nat.prime_five (HDesc.suzuki_outer_cyclic hS) hA
  obtain ⟨hel, hcard⟩ := HDesc.inner_part_elemAbelian hZ hA
  have h2 : Nat.card ↥(A ⊓ inner X) ≤ 5 := by
    rw [← hcard]
    exact HDesc.suzuki_rank_one hS Nat.prime_five (by norm_num) _ hel
  calc Nat.card A ≤ 5 * Nat.card ↥(A ⊓ inner X) := h1
    _ ≤ 5 * 5 := Nat.mul_le_mul_left _ h2
    _ = 5 ^ 2 := by norm_num

end Sz

section F4


theorem s265e_fin_f4 {X : Type} [Group X] [Finite X] (hS : ReeTitsModel X .twistedF4 2 5)
    {A : Subgroup (MulAut X)} (hA : IsElemAbelian 5 A) (hAd : A ≤ innAutDerived X) :
    Nat.card A ≤ 5 ^ 2 := by
  obtain ⟨-, -, -, -, -, hiso⟩ := large_Ree_model_Schreier X 2 5 hS
  obtain ⟨-, a, hfa, F, _, _, hF, ⟨e'⟩⟩ := id hS
  have ha : a = 2 := by omega
  subst ha
  have hF' : Nat.card F = 2 ^ (2 * 2 + 1) := by simpa using hF
  haveI : CharP F F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hF
  obtain ⟨eΓ⟩ := hiso 2 F rfl hF ⟨e'⟩
  have hZ : Subgroup.center X = ⊥ := by
    have hZΓ := large_Ree_fixed_group_center_trivial 2 F hF'
    refine eq_bot_iff.2 fun g hg => ?_
    have hmem : eΓ g ∈ Subgroup.center (F4.reeGamma F 2) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨q, rfl⟩ := eΓ.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg eΓ (Subgroup.mem_center_iff.1 hg q)
    rw [hZΓ, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (eΓ.injective (by rw [hmem, map_one]))
  have hcyc : IsCyclic (Outer X) := by
    obtain ⟨hcycΓ, -⟩ := CFSG.AGLEmbedding.outer_reeGamma (a := 2) (K := F) (by norm_num) hF'
    haveI := hcycΓ
    exact isCyclic_of_surjective (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eΓ).symm.toMonoidHom
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eΓ).symm.surjective
  have hAinn : A ≤ inner X :=
    hAd.trans (sup_le le_rfl (s265e_fin_commutator_le_inner hcyc))
  obtain ⟨hA₀, hcard⟩ := HDesc.inner_part_elemAbelian hZ hA
  rw [inf_eq_left.2 hAinn] at hcard
  rw [← hcard]
  have hE' : IsElemAbelian 5 ((A.comap (MulAut.conj : X →* MulAut X)).map eΓ.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hA₀ eΓ.toMonoidHom
  have := CFSG.HardMathSupport.Malle.LocalAction.card_le_twentyfive_of_elemAbelian_reeGamma hF' _ hE'
  rwa [Subgroup.card_map_of_injective eΓ.injective] at this

end F4

section Tits


theorem s265e_card_tits {X : Type} [Group X] (hT : ReeTitsModel X .Tits 2 1) :
    Nat.card X = 17971200 :=
  (CFSG.SeitzReduction.F4Pilot.EvenExc.card_of_reeTitsModel_tits hT).trans rfl

theorem s265e_order_contra {X : Type} [Group X] [Finite X] (hX : Nat.card X ≤ 17971200)
    {β : MulAut X} (hβ : β ≠ 1) {J : Subgroup X} (hJ : IsComponentOf J (fixSubgroup β))
    (hQ : LieModel (↥J ⧸ Subgroup.center ↥J) .twistedB2 0 2 5 ∨
      LieModel (↥J ⧸ Subgroup.center ↥J) .Tits 0 2 1) : False := by
  have hge : 17971200 ≤ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
    rcases hQ with h | h
    · have hcard := s265e_fin_card_sz32 (LieModel.suzukiModel h).2
      omega
    · have hcard := s265e_card_tits (LieModel.reeTitsModel h (by simp [reeTitsTags])).2
      omega
  have h1 : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card J :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have h2 : Nat.card J ≤ Nat.card X := Subgroup.card_le_card_group J
  have hJtop : J = ⊤ := Subgroup.eq_top_of_card_eq J (by omega)
  have hfix : fixSubgroup β = ⊤ := eq_top_iff.2 (hJtop ▸ hJ.1)
  apply hβ
  ext x
  have hx : x ∈ fixSubgroup β := hfix ▸ Subgroup.mem_top x
  rw [MulAut.one_apply]
  exact hx

end Tits

end CFSG.LocalAnalysis.GLTheoremA.S265

end
