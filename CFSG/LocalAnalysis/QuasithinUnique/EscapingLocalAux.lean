module

public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.Foundations.Basic

public section

namespace CFSG.QuasithinUnique.EscapingLocal

open CFSG.Open

variable {G : Type*} [Group G]

theorem exists_mem_inf_normalizer_not_mem [Finite G] {U V : Subgroup G} (hV : IsPGroup 2 V)
    (hUV : U ≤ V) (hne : U ≠ V) :
    ∃ x ∈ V ⊓ Subgroup.normalizer (U : Set G), x ∉ U := by
  have : Group.IsNilpotent V := hV.isNilpotent
  have hlt : U.subgroupOf V < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne ?_
    refine le_antisymm hUV ?_
    intro v hv
    have : (⟨v, hv⟩ : V) ∈ U.subgroupOf V := htop ▸ Subgroup.mem_top _
    exact this
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := V) _ hlt
  obtain ⟨x, hx, hxn⟩ := Set.exists_of_ssubset hnorm
  refine ⟨x, ?_, hxn⟩
  rw [← map_subtype_normalizer hUV]
  exact ⟨x, hx, rfl⟩

theorem exists_conj_mem_of_isPGroup [Finite G] {M T S : Subgroup G} (hTM : T ≤ M)
    (hT : IsPGroup 2 T) (hTind : ¬ 2 ∣ (T.subgroupOf M).index) (hSM : S ≤ M)
    (hS : IsPGroup 2 S) : ∃ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ T := by
  have hT' : IsPGroup 2 (T.subgroupOf M) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm
  have hS' : IsPGroup 2 (S.subgroupOf M) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm
  let P : Sylow 2 M := hT'.toSylow hTind
  obtain ⟨Q, hQ⟩ := hS'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P Q
  refine ⟨(g : G)⁻¹, M.inv_mem g.2, fun s hs => ?_⟩
  have hsQ : (⟨s, hSM hs⟩ : M) ∈ ((g • P : Sylow 2 M) : Subgroup M) := by
    rw [hg]
    exact hQ (Subgroup.mem_subgroupOf.mpr hs)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hsQ
  have h2 : (g : G)⁻¹ * s * g ∈ T := hsQ
  simpa using h2

theorem pCoreOf_le_of_isSylowTwoOf {S H : Subgroup G} (hS : IsSylowTwoOf S H) :
    pCoreOf 2 H ≤ S := by
  have hS' : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let P : Sylow 2 H := hS'.toSylow hS.2.2
  have : (CFSG.Open.pCore 2 H).Normal := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal 2
  have h1 : CFSG.Open.pCore 2 H ≤ (P : Subgroup H) :=
    IsPGroup.le_sylow_of_normal (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2) P
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  have h3 : (P : Subgroup H).map H.subtype = S := by
    change (S.subgroupOf H).map H.subtype = S
    rw [Subgroup.map_subgroupOf_eq_of_le hS.1]
  change Subgroup.map H.subtype (CFSG.Open.pCore 2 H) ≤ S
  rw [← h3]
  exact h2

theorem exists_isSylowTwoOf_ge [Finite G] {P H : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    ∃ S : Subgroup G, IsSylowTwoOf S H ∧ P ≤ S := by
  have hP' : IsPGroup 2 (P.subgroupOf H) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  have hQS : (Q : Subgroup H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  refine ⟨(Q : Subgroup H).map H.subtype, ⟨hQS, Q.isPGroup'.map H.subtype, ?_⟩, ?_⟩
  · change ¬ 2 ∣ (Subgroup.comap H.subtype ((Q : Subgroup H).map H.subtype)).index
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact Sylow.not_dvd_index Q
  · intro x hx
    have := hQ (show (⟨x, hPH hx⟩ : H) ∈ P.subgroupOf H from hx)
    exact ⟨_, this, rfl⟩

theorem oddCore_eq_pPrimeCore (K : Type*) [Group K] : CFSG.oddCore K = CFSG.pPrimeCore 2 K := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem odd_card_oddCore (K : Type*) [Group K] [Finite K] : Odd (Nat.card (CFSG.oddCore K)) := by
  rw [oddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem le_of_forall_hyperplane_centralizer [Finite G] {R U X : Subgroup G}
    (hRU : ∀ u ∈ U, ∀ r ∈ R, u * r * u⁻¹ ∈ R) (hR : ¬ 2 ∣ Nat.card R) (hU : IsElemAbelian 2 U)
    (hU1 : U ≠ ⊥)
    (hX : ∀ B : Subgroup U, B.index = 2 → ∀ r ∈ R,
      (∀ b : B, ((b : U) : G) * r = r * ((b : U) : G)) → r ∈ X) :
    R ≤ X := by
  let _ : MulDistribMulAction U R :=
    { smul := fun a r => ⟨a * r * a⁻¹, hRU a a.2 r r.2⟩
      one_smul := fun r => Subtype.ext (by
        change ((1 : U) : G) * (r : G) * ((1 : U) : G)⁻¹ = r
        simp)
      mul_smul := fun a b r => Subtype.ext (by
        change ((a * b : U) : G) * (r : G) * ((a * b : U) : G)⁻¹ =
          (a : G) * ((b : G) * (r : G) * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc])
      smul_mul := fun a r s => Subtype.ext (by
        change (a : G) * ((r * s : R) : G) * (a : G)⁻¹ =
          (a : G) * (r : G) * (a : G)⁻¹ * ((a : G) * (s : G) * (a : G)⁻¹)
        simp [mul_assoc])
      smul_one := fun a => Subtype.ext (by
        change (a : G) * ((1 : R) : G) * (a : G)⁻¹ = ((1 : R) : G)
        simp) }
  have : IsElementaryAbelian 2 U :=
    { toIsMulCommutative := hU.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hU.2 x x.2) }
  have : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hU1
  have key := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := U) (H := R) hR
  have hle : (⨆ (B : Subgroup U) (_ : B.index = 2), CFSG.fixedPointSubgroup B R) ≤
      X.comap R.subtype := by
    refine iSup₂_le fun B hB x hx => ?_
    refine hX B hB x x.2 fun b => ?_
    have h1 : ((b : U) • x : R) = x := hx b
    have h2 := congrArg Subtype.val h1
    change ((b : U) : G) * (x : G) * ((b : U) : G)⁻¹ = (x : G) at h2
    calc ((b : U) : G) * (x : G)
        = ((b : U) : G) * (x : G) * ((b : U) : G)⁻¹ * ((b : U) : G) := by group
      _ = (x : G) * ((b : U) : G) := by rw [h2]
  intro r hr
  have hr' : (⟨r, hr⟩ : R) ∈ (⊤ : Subgroup R) := trivial
  rw [← key] at hr'
  exact hle hr'

theorem isCharacteristicP_of_charTwo {K : Subgroup G} (hK : CharTwo K) :
    CFSG.IsCharacteristicP 2 K := CFSG.QuasithinUnique.charTwo_iff_isCharacteristicP.mp hK

end CFSG.QuasithinUnique.EscapingLocal
