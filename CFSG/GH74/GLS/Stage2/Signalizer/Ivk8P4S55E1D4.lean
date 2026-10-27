module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1D4Par
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Tr
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1BT
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Types
public import CFSG.RankThree.PartOne.KF.ParabolicNormalizes

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley

section Native

variable (K : Type) [Field K] (σ : K ≃+* K)

theorem BB_le_normalizer_U (r : ℕ) [Fact r.Prime] [Finite K] [CharP K r] :
    BB K σ ≤ Subgroup.normalizer
      (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
          Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
            Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  intro b hb
  have hb' : (b : ModGL TwistTag.D4.tag K) ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := hb
  have : b ∈ (Subgroup.normalizer (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
      Set (ModGL TwistTag.D4.tag K))).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent hb'
  rwa [Subgroup.subgroupOf_normalizer_eq hUC] at this

theorem aut_eq_one_d4 {r : ℕ} [Fact r.Prime] [Finite K] [CharP K r] (hK : ringChar K ≠ 2)
    (b : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hb : ¬ r ∣ orderOf b)
    {a a' : Fin TwistTag.D4.foldedTag.rank} (hne : a ≠ a')
    (hfix : ∀ q ∈ QJ K σ {a}, b q = q) : b = 1 := by
  have hBle : ∀ c, BB K σ ≤ PJ K σ {c} := fun c => by
    rw [← PJ_empty K σ]
    exact (PJ_le_iff K σ _ _).2 (Set.empty_subset _)
  have hJne : ∀ c : Fin TwistTag.D4.foldedTag.rank, ({c} : Set (Fin TwistTag.D4.foldedTag.rank)) ≠
      Set.univ := by
    intro c h
    have hex : ∀ c : Fin TwistTag.D4.foldedTag.rank,
        ∃ x : Fin TwistTag.D4.foldedTag.rank, x ≠ c := by decide
    obtain ⟨x, hx⟩ := hex c
    have hxc : x ∈ ({c} : Set (Fin TwistTag.D4.foldedTag.rank)) := by
      rw [h]
      exact Set.mem_univ x
    exact hx (Set.mem_singleton_iff.1 hxc)
  have hMne : PJ K σ {a} ≠ PJ K σ {a'} := fun h => hne (Set.singleton_subset_singleton.1
    ((PJ_le_iff K σ _ _).1 h.le))
  refine aut_eq_one_of_two_maximals b hb (B := BB K σ) (isCoatom_PJ_singleton K σ a)
    (isCoatom_PJ_singleton K σ a') hMne (hBle a) (hBle a') ?_ (QJ_ne_bot K σ (hJne a))
    (QJ_isPGroup K σ r _) (PJ_normalizes K σ) (PJ_selfCentralizing K σ (hJne a))
    (QJ_isPGroup K σ r _) (QJ_le_BB K σ _) (PJ_normalizes K σ)
    (PJ_selfCentralizing K σ (hJne a')) (no_normal_pGroup K σ r hK) hfix
  intro A hA hBA
  obtain ⟨c, rfl⟩ := coatom_eq_PJ K σ hA hBA
  rcases two_elements a a' (Ne.symm hne) c with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem e1Core_d4_native {r : ℕ} [Fact r.Prime] [Finite K] [CharP K r] (hK : ringChar K ≠ 2)
    (hBT : LieType.BorelTits.Holds ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) r) :
    E1Core r ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  intro b hb1 hbr hHH E hE hinv
  by_contra hne
  obtain ⟨M, S, hM, hS, hR⟩ := e1_engine hBT b hHH hE hinv hne
  have hUp := isPGroup_graphFixedPosUnipotent_subgroupOf r (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom)
  have hUi := not_dvd_index_graphFixedPosUnipotent r (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom) σ.surjective
  have hUc := IsPGroup.toSylow_coe hUp hUi
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.KFU.exists_conj_le_of_normalizes (hUp.toSylow hUi) S
    (BB K σ) M (by rw [hUc]; exact BB_le_normalizer_U K σ r) hS
  have hM' : IsCoatom (M.comap (MulAut.conj g).toMonoidHom) :=
    isCoatom_comap_mulAut _ hM
  obtain ⟨a, ha⟩ := coatom_eq_PJ K σ hM' hg
  obtain ⟨a', hne'⟩ : ∃ a' : Fin TwistTag.D4.foldedTag.rank, a ≠ a' := by
    have hex : ∀ c : Fin TwistTag.D4.foldedTag.rank,
        ∃ x : Fin TwistTag.D4.foldedTag.rank, c ≠ x := by decide
    exact hex a
  set b' : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (MulAut.conj g)⁻¹ * b * MulAut.conj g with hb'
  have hRp : IsPGroup r ↥((QJ K σ {a}).map (MulAut.conj g).toMonoidHom) :=
    (QJ_isPGroup K σ r {a}).map _
  have hRM : (QJ K σ {a}).map (MulAut.conj g).toMonoidHom ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    have hxP : x ∈ M.comap (MulAut.conj g).toMonoidHom := by
      rw [ha]
      exact QJ_le_PJ K σ {a} hx
    exact hxP
  have hMR : M ≤ Subgroup.normalizer (((QJ K σ {a}).map (MulAut.conj g).toMonoidHom :
      Subgroup _) : Set _) := by
    refine le_normalizer_of_conj_mem ?_
    rintro m hm _ ⟨q, hq, rfl⟩
    have hm' : (MulAut.conj g) ((MulAut.conj g)⁻¹ m) = m := (MulAut.conj g).apply_symm_apply m
    have hn : (MulAut.conj g)⁻¹ m ∈ PJ K σ {a} := by
      rw [← ha]
      show (MulAut.conj g) ((MulAut.conj g)⁻¹ m) ∈ M
      rw [hm']
      exact hm
    refine ⟨(MulAut.conj g)⁻¹ m * q * ((MulAut.conj g)⁻¹ m)⁻¹, PJ_normalizes K σ _ hn q hq, ?_⟩
    show (MulAut.conj g) ((MulAut.conj g)⁻¹ m * q * ((MulAut.conj g)⁻¹ m)⁻¹) =
      m * (MulAut.conj g) q * m⁻¹
    rw [map_mul, map_mul, map_inv, hm']
  have hfix : ∀ q ∈ QJ K σ {a}, b' q = q := by
    intro q hq
    have h1 := hR _ hRp hRM hMR ((MulAut.conj g) q) ⟨q, hq, rfl⟩
    simp only [hb', MulAut.mul_apply]
    rw [h1]
    exact (MulAut.conj g).symm_apply_apply q
  have hb'ord : ¬ r ∣ orderOf b' := by
    have : orderOf b' = orderOf b := by
      refine (SemiconjBy.orderOf_eq (MulAut.conj g)⁻¹ ?_).symm
      show (MulAut.conj g)⁻¹ * b = ((MulAut.conj g)⁻¹ * b * MulAut.conj g) * (MulAut.conj g)⁻¹
      group
    rw [this]
    exact hbr
  have hb'1 := aut_eq_one_d4 K σ hK b' hb'ord hne' hfix
  apply hb1
  have h1 : b = MulAut.conj g * b' * (MulAut.conj g)⁻¹ := by rw [hb']; group
  rw [h1, hb'1]
  group

theorem e1_d4_aux {r f : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) {Y : Type} [Group Y] [Finite Y]
    (hf : 1 ≤ f) (hm : LieModel Y .trialityD4 0 r f) : E1Core r Y := by
  have htw : TwistedChevalleyModel Y .D4 (r ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Fact.out hf htw
  have hM3 : Nat.card M = (r ^ f) ^ 3 := hM
  have hK3 : Nat.card M = r ^ (3 * f) := by rw [hM3, ← pow_mul, mul_comm]
  have : CharP M r := finite_field_prime_power_characteristic Fact.out (by omega) hK3
  have hodd : ringChar M ≠ 2 := by
    rw [ringChar.eq M r]
    exact hr2
  have hBT : LieType.BorelTits.Holds Y r := holds_of_lieModel hm (by decide)
  have hBT' : LieType.BorelTits.Holds ↥(graphFixedRootGroup TwistTag.D4 M σ.toRingHom) r :=
    LieType.BorelTits.Holds.of_mulEquiv e hBT
  exact E1Core.of_mulEquiv e (e1Core_d4_native M σ hodd hBT')

end Native

section Top


theorem e1_d4 : E1Type FD4d := by
  intro r Y _ _ hr hr2 hF b hb1 hbr hHH E hE hinv
  obtain ⟨f, hf, hm⟩ := hF
  have : Fact r.Prime := ⟨hr⟩
  exact e1_d4_aux hr2 hf hm b hb1 hbr hHH E hE hinv

end Top

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
