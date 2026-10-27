module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Levi
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Frame

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.SeitzReduction (highRoot isRoot_highRoot)
open CFSG.LieType.Steinberg CFSG.LieType.Universal

variable (K : Type) [Field K]

@[expose] noncomputable def e7L :
    Subgroup (adjointGroup .E7 K) :=
  (subsystemGroup .E7 K e7LeviNodes).comap (adjointGroup .E7 K).subtype

variable {K}

theorem range_e7D6Node : Set.range CatLeafProof.e7D6Node = e7LeviNodes := by
  ext i
  constructor
  · rintro ⟨k, rfl⟩ h
    fin_cases k <;> exact absurd h (by decide)
  · intro hi
    obtain ⟨n, hn⟩ := i
    have hn0 : n ≠ 0 := fun h => hi (Fin.ext h)
    have hn7 : n < 7 := hn
    interval_cases n
    · exact absurd rfl hn0
    · exact ⟨5, Fin.ext rfl⟩
    · exact ⟨4, Fin.ext rfl⟩
    · exact ⟨3, Fin.ext rfl⟩
    · exact ⟨2, Fin.ext rfl⟩
    · exact ⟨1, Fin.ext rfl⟩
    · exact ⟨0, Fin.ext rfl⟩

theorem e7L_eq_iSup :
    e7L K = ⨆ k, LieType.CurtisTits.rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup
      (CatLeafProof.e7D6Node k) := by
  rw [e7L, ← range_e7D6Node, ← CatLeafProof.map_subtype_iSup_rankOne,
    Subgroup.comap_map_eq_self_of_injective (adjointGroup .E7 K).subtype_injective]

theorem e7L_recognition
    [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    CFSG.Open.IsQuasisimple ↥(e7L K) ∧
      LieModel (↥(e7L K) ⧸ Subgroup.center ↥(e7L K)) .POmegaPlus 6 2 m := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaPlus 6 2 m :=
    ⟨Nat.prime_two, hm, by norm_num⟩
  obtain ⟨O, C, hE⟩ := CatLeafProof.exists_e7_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := CatLeafProof.exists_levi_frame hE rfl CatLeafProof.e7D6Node
    CatLeafProof.e7D6_adj CatLeafProof.e7D6_nadj
  obtain ⟨-, -, -, hqs, hlie⟩ :=
    CatLeafProof.spinPlus_frame_subgroup hadm (by norm_num) hK hcomm hρ hψ
  rw [← e7L_eq_iSup] at hqs hlie
  exact ⟨⟨hqs.1.commutator_eq_top, hqs.2.1⟩, hlie⟩

theorem statedClassicalModel_of_lieModel_POmegaPlus {S : Type} [Group S] {n p f : ℕ}
    (h : LieModel S .POmegaPlus n p f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel S .POmegaPlus n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem pow_card_units_eq_one_of_mem_torusGroup_e7
    [Finite K]
    {t : ModGL .E7 K} (ht : t ∈ torusGroup .E7 K) : t ^ Nat.card Kˣ = 1 := by
  obtain ⟨a, rfl, -⟩ := (exceptional_Lang_root_rank_one_torus_transport (τ := .E7) (K := K)
    (isRoot_highRoot .E7)).2.2.2.2.2.1 t ht
  have hpow : ∀ n : ℕ, rootDiagUnit .E7 a ^ n = rootDiagUnit .E7 (a ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
    | succ n ih => rw [pow_succ, ih, ← rootDiagUnit_mul, pow_succ]
  rw [hpow]
  have ha : a ^ Nat.card Kˣ = 1 := funext fun i => by
    rw [Pi.pow_apply, Pi.one_apply]
    exact pow_card_eq_one'
  rw [ha, rootDiagUnit_one]

theorem subsystemGroup_le_adjointGroup_e7
    (J : Set (Fin Tag.E7.rank)) :
    subsystemGroup .E7 K J ≤ adjointGroup .E7 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, -, c, rfl | rfl⟩
  exacts [xUnit_mem_adjointGroup i c, yUnit_mem_adjointGroup i c]

theorem odd_card_center_e7L
    [Finite K]
    {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    Odd (Nat.card (Subgroup.center ↥(e7L K))) := by
  have : Finite (ModGL .E7 K) := finite_modGL
  set S := subsystemGroup .E7 K e7LeviNodes with hSdef
  have hmap : (e7L K).map (adjointGroup .E7 K).subtype = S := by
    rw [e7L, Subgroup.map_comap_eq_self (by
      rw [Subgroup.range_subtype]
      exact subsystemGroup_le_adjointGroup_e7 _)]
  let E : ↥(e7L K) ≃* ↥S :=
    ((e7L K).equivMapOfInjective _ (adjointGroup .E7 K).subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hE : ∀ z : ↥(e7L K),
      ((E z : ↥S) : ModGL .E7 K) = ((z : adjointGroup .E7 K) : ModGL .E7 K) := fun z => rfl
  have hodd := E8.odd_card_units_e8 hm hK
  have hz : ∀ z ∈ Subgroup.center ↥(e7L K), z ^ Nat.card Kˣ = 1 := by
    intro z hz
    have hEz : E z ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := E.surjective y
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz x)]
    have hT := supportedTorus_le_torusGroup e7LeviNodes (mem_supportedTorus_of_mem_center hEz)
    rw [hE] at hT
    have h1 := pow_card_units_eq_one_of_mem_torusGroup_e7 hT
    apply Subtype.ext
    apply Subtype.ext
    simpa using h1
  by_contra hne
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hne
  have h2 : orderOf g ∣ Nat.card Kˣ := orderOf_dvd_of_pow_eq_one (by
    apply Subtype.ext
    simpa using hz g g.2)
  rw [hg] at h2
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

variable (K)

@[expose] noncomputable def e7Rho :
    SL2 K →* adjointGroup .E7 K :=
  (rootSL2 .E7 K (highRoot .E7)).codRestrict (adjointGroup .E7 K)
    (exceptional_Lang_root_rank_one_data .E7 K (highRoot .E7)).2.2.2.2.1

@[expose] noncomputable def e7D :
    Subgroup (adjointGroup .E7 K) :=
  (e7Rho K).range

@[expose] noncomputable def e7Q :
    Subgroup (adjointGroup .E7 K) :=
  ((e7Rho K).comp (E8.e8HSLHom K)).range

variable {K}

theorem coe_e7Rho
    (A : SL2 K) :
    ((e7Rho K A : adjointGroup .E7 K) : ModGL .E7 K) = rootSL2 .E7 K (highRoot .E7) A :=
  rfl

theorem e7Q_le_e7D :
    e7Q K ≤ e7D K := by
  rintro _ ⟨c, rfl⟩
  exact ⟨_, rfl⟩

theorem commutator_e7D
    [Finite K] (h4 : 4 ≤ Nat.card K) :
    ⁅e7D K, e7D K⁆ = e7D K := by
  have hP := CFSG.LinearGroups.special_linear_dimension_two_perfect
    (CFSG.RankThree.Chevalley.exists_finset_card_four h4)
  rw [e7D, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    hP.commutator_eq_top]

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
