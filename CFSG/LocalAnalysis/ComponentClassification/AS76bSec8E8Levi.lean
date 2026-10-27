module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8Levi
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.SeitzReduction (highRoot isRoot_highRoot)

variable (K : Type) [Field K]

@[expose] noncomputable def e8L :
    Subgroup (adjointGroup .E8 K) :=
  (subsystemGroup .E8 K e8LeviNodes).comap (adjointGroup .E8 K).subtype

variable {K}

theorem range_e8E7Node : Set.range CatLeafProof.e8E7Node = e8LeviNodes := by
  have h7 : (e8Top : Fin Tag.E8.rank).val = 7 := rfl
  ext i
  constructor
  · rintro ⟨k, rfl⟩ h
    have h1 := congrArg Fin.val h
    have h2 : (CatLeafProof.e8E7Node k).val = k.val := rfl
    have h3 : k.val < 7 := k.2
    omega
  · intro hi
    have h1 : i.val < 8 := i.2
    have h2 : i.val ≠ 7 := fun h => hi (Fin.ext (h.trans h7.symm))
    exact ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩

theorem e8L_eq_iSup :
    e8L K = ⨆ k, LieType.CurtisTits.rankOne (e8Datum K).rootGroup (CatLeafProof.e8E7Node k) := by
  rw [e8L, ← range_e8E7Node, ← CatLeafProof.map_subtype_iSup_rankOne,
    Subgroup.comap_map_eq_self_of_injective (adjointGroup .E8 K).subtype_injective]

theorem e8L_recognition
    [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    CFSG.Open.IsQuasisimple ↥(e8L K) ∧
      ChevalleyExceptionalModel (↥(e8L K) ⧸ Subgroup.center ↥(e8L K)) .E7 2 m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hqs, hlie⟩ :=
    CatLeafProof.exists_psi_E7_E8 (p := 2) (f := m) ⟨Nat.prime_two, hm, rfl⟩ hK
  rw [← e8L_eq_iSup] at hqs hlie
  refine ⟨⟨hqs.1.commutator_eq_top, hqs.2.1⟩, ?_⟩
  rcases hlie with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · simp [classicalTags] at ht
  · exact h
  · simp [reeTitsTags] at ht
  · exact absurd ht (by decide)

theorem pow_card_units_eq_one_of_mem_torusGroup
    [Finite K]
    {t : ModGL .E8 K} (ht : t ∈ torusGroup .E8 K) : t ^ Nat.card Kˣ = 1 := by
  obtain ⟨a, rfl, -⟩ := (exceptional_Lang_root_rank_one_torus_transport (τ := .E8) (K := K)
    (isRoot_highRoot .E8)).2.2.2.2.2.1 t ht
  have hpow : ∀ n : ℕ, rootDiagUnit .E8 a ^ n = rootDiagUnit .E8 (a ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
    | succ n ih => rw [pow_succ, ih, ← rootDiagUnit_mul, pow_succ]
  rw [hpow]
  have ha : a ^ Nat.card Kˣ = 1 := funext fun i => by
    rw [Pi.pow_apply, Pi.one_apply]
    exact pow_card_eq_one'
  rw [ha, rootDiagUnit_one]

theorem odd_two_pow_sub_one_e8 {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  refine ⟨2 ^ i - 1, ?_⟩
  rw [pow_succ]
  have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  omega

theorem odd_card_units_e8 {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    Odd (Nat.card Kˣ) := by
  rw [Nat.card_units, hK]
  exact odd_two_pow_sub_one_e8 hm

theorem subsystemGroup_le_adjointGroup_e8
    (J : Set (Fin Tag.E8.rank)) :
    subsystemGroup .E8 K J ≤ adjointGroup .E8 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, -, c, rfl | rfl⟩
  exacts [xUnit_mem_adjointGroup i c, yUnit_mem_adjointGroup i c]

theorem odd_card_center_e8L
    [Finite K]
    {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    Odd (Nat.card (Subgroup.center ↥(e8L K))) := by
  have : Finite (ModGL .E8 K) := finite_modGL
  set S := subsystemGroup .E8 K e8LeviNodes with hSdef
  have hmap : (e8L K).map (adjointGroup .E8 K).subtype = S := by
    rw [e8L, Subgroup.map_comap_eq_self (by
      rw [Subgroup.range_subtype]
      exact subsystemGroup_le_adjointGroup_e8 _)]
  let E : ↥(e8L K) ≃* ↥S :=
    ((e8L K).equivMapOfInjective _ (adjointGroup .E8 K).subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hE : ∀ z : ↥(e8L K),
      ((E z : ↥S) : ModGL .E8 K) = ((z : adjointGroup .E8 K) : ModGL .E8 K) := fun z => rfl
  have hodd := odd_card_units_e8 hm hK
  have hz : ∀ z ∈ Subgroup.center ↥(e8L K), z ^ Nat.card Kˣ = 1 := by
    intro z hz
    have hEz : E z ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := E.surjective y
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz x)]
    have hT := supportedTorus_le_torusGroup e8LeviNodes (mem_supportedTorus_of_mem_center hEz)
    rw [hE] at hT
    have h1 := pow_card_units_eq_one_of_mem_torusGroup hT
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

@[expose] noncomputable def e8Rho :
    SL2 K →* adjointGroup .E8 K :=
  (rootSL2 .E8 K (highRoot .E8)).codRestrict (adjointGroup .E8 K)
    (exceptional_Lang_root_rank_one_data .E8 K (highRoot .E8)).2.2.2.2.1

@[expose] noncomputable def e8D :
    Subgroup (adjointGroup .E8 K) :=
  (e8Rho K).range

@[expose] noncomputable def e8HSLHom : Kˣ →* SL2 K where
  toFun := HSL
  map_one' := Subtype.ext (by ext i j; fin_cases i <;> fin_cases j <;> simp [HSL])
  map_mul' a b := Subtype.ext (by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [HSL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm])

@[expose] noncomputable def e8Q :
    Subgroup (adjointGroup .E8 K) :=
  ((e8Rho K).comp (e8HSLHom K)).range

variable {K}

theorem coe_e8Rho
    (A : SL2 K) :
    ((e8Rho K A : adjointGroup .E8 K) : ModGL .E8 K) = rootSL2 .E8 K (highRoot .E8) A :=
  rfl

theorem e8Q_le_e8D :
    e8Q K ≤ e8D K := by
  rintro _ ⟨c, rfl⟩
  exact ⟨_, rfl⟩

theorem commutator_e8D
    [Finite K] (h4 : 4 ≤ Nat.card K) :
    ⁅e8D K, e8D K⁆ = e8D K := by
  have hP := CFSG.LinearGroups.special_linear_dimension_two_perfect
    (CFSG.RankThree.Chevalley.exists_finset_card_four h4)
  rw [e8D, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    hP.commutator_eq_top]

end CFSG.ComponentClassification.RankTwoExceptional.E8
