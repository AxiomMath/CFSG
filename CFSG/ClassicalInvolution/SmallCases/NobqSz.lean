module

public import CFSG.ClassicalInvolution.SmallCases.NobqBender
public import CFSG.Dihedral.BrauerSuzuki.Helpers
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCoverRootData
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.Blueprint.Catalog
public import Certificates.Certificate113
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.SmallCases.NobqOut
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
  CFSG.BenderSuzuki.PFAppendixIII CFSG.ComponentClassification.OuterAutomorphisms

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)

theorem suzukiCoverRootElement_sq' (hm : 0 < m) (a b : K) :
    suzukiCoverRootElement m a b ^ 2 =
      suzukiCoverRootElement m 0 (a * suzukiCoverTits m a) := by
  rw [pow_two, suzukiCoverRootElement_mul m hm, CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero, zero_add]

theorem suzukiCoverRootElement_zero_mul_comm (hm : 0 < m) (e : K) (x : suzukiCoverRoot m) :
    suzukiCoverRootElement m 0 e * x = x * suzukiCoverRootElement m 0 e := by
  obtain ⟨c, d, rfl⟩ := suzukiCoverRootElement_surjective m x
  rw [suzukiCoverRootElement_mul m hm, suzukiCoverRootElement_mul m hm]
  congr 1
  · exact (add_zero c).symm ▸ zero_add c
  · rw [map_zero, zero_mul, mul_zero, add_zero, add_zero, add_comm e d]

theorem suzukiCoverRootElement_commutator (hm : 0 < m) (a b c d : K) :
    suzukiCoverRootElement m a b * suzukiCoverRootElement m c d =
      suzukiCoverRootElement m c d * suzukiCoverRootElement m a b *
        suzukiCoverRootElement m 0 (a * suzukiCoverTits m c + c * suzukiCoverTits m a) := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  rw [suzukiCoverRootElement_mul m hm, suzukiCoverRootElement_mul m hm,
    suzukiCoverRootElement_mul m hm]
  congr 1
  · rw [add_zero]
    exact add_comm a c
  · rw [map_zero, mul_zero, add_zero]
    linear_combination (-(c * suzukiCoverTits m a)) * h2

theorem exists_not_mem_commutator_values (hm : 0 < m) {a : K} (ha : a ≠ 0) :
    ∃ c : K, a * suzukiCoverTits m c + c * suzukiCoverTits m a ≠ 0 ∧
      a * suzukiCoverTits m c + c * suzukiCoverTits m a ≠ a * suzukiCoverTits m a := by
  by_contra hcon
  push Not at hcon
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hθa : suzukiCoverTits m a ≠ 0 := fun h =>
    ha ((map_eq_zero_iff _ (suzukiCoverTits m).injective).1 h)
  have hr : a * suzukiCoverTits m a ≠ 0 := mul_ne_zero ha hθa
  have hT : ∀ u : K, suzukiCoverTits m u + u = 0 ∨ suzukiCoverTits m u + u = 1 := by
    intro u
    have hE : a * suzukiCoverTits m (u * a) + (u * a) * suzukiCoverTits m a =
        (a * suzukiCoverTits m a) * (suzukiCoverTits m u + u) := by
      rw [map_mul]
      ring
    by_cases h0 : a * suzukiCoverTits m (u * a) + (u * a) * suzukiCoverTits m a = 0
    · left
      rw [hE] at h0
      exact (mul_eq_zero.1 h0).resolve_left hr
    · right
      have h1 := hcon (u * a) h0
      rw [hE] at h1
      exact mul_left_cancel₀ hr (by rw [mul_one]; exact h1)
  have hfix : ∀ u : K, suzukiCoverTits m u + u = 0 → u = 0 ∨ u = 1 := by
    intro u hu
    have h1 : suzukiCoverTits m u = u := CharTwo.add_eq_zero.1 hu
    have h3 : u ^ 2 = u := by
      rw [← suzukiCoverTits_square m u, h1, h1]
    have : u * (u - 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have : Fintype K := Fintype.ofFinite K
  have hcard : 8 ≤ Fintype.card K := by
    have h : Nat.card K = 2 ^ (2 * m + 1) := GaloisField.card 2 (2 * m + 1) (by omega)
    rw [← Nat.card_eq_fintype_card, h]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  classical
  obtain ⟨u₁, -, hu₁⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset K)) (t := Finset.univ)
    (lt_of_le_of_lt Finset.card_le_two (by rw [Finset.card_univ]; omega))
  obtain ⟨u₂, -, hu₂⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1, u₁, u₁ + 1} : Finset K)) (t := Finset.univ)
    (lt_of_le_of_lt (Finset.card_le_four) (by rw [Finset.card_univ]; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu₁ hu₂
  have hone : ∀ u : K, u ≠ 0 → u ≠ 1 → suzukiCoverTits m u + u = 1 := fun u h0 h1 =>
    (hT u).resolve_left fun h => (hfix u h).elim h0 h1
  have h₁ := hone u₁ hu₁.1 hu₁.2
  have h₂ := hone u₂ hu₂.1 hu₂.2.1
  have hs0 : u₁ + u₂ ≠ 0 := fun h => hu₂.2.2.1 (CharTwo.add_eq_zero.1 h).symm
  have hs1 : u₁ + u₂ ≠ 1 := fun h => hu₂.2.2.2 (by linear_combination h - u₁ * h2)
  have h₃ := hone (u₁ + u₂) hs0 hs1
  rw [map_add] at h₃
  have : (1 : K) = 0 := by linear_combination h₃ - h₁ - h₂
  exact one_ne_zero this

theorem not_uniqueInvNormal_of_mem_root (hm : 0 < m) {z : SuzukiMatrixGroup m}
    (hzQ : z ∈ suzukiCoverRoot m) (hz : orderOf z = 2) (N : Subgroup (SuzukiMatrixGroup m)) :
    ¬ UniqueInvNormal z N := by
  intro h
  obtain ⟨s, hsN, hss, hs4⟩ := h.exists_sq_eq
  have hs4' : s ^ 4 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs4] at this
  have hsQ : s ∈ suzukiCoverRoot m := by
    have hM := (CFSG.Open.bender_suzukiMatrixGroup_borel m hm (suzukiCoverSylow m hm)).1
    have hzM : z ∈ Subgroup.normalizer
        ((suzukiCoverSylow m hm : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m)) :=
      Subgroup.le_normalizer (H := (suzukiCoverSylow m hm : Subgroup (SuzukiMatrixGroup m))) hzQ
    have hsM := centralizer_le_of_fusionStronglyEmbedded hM hzM hz (h.le_centralizer hsN)
    exact mem_sylow_of_mem_normalizer_of_pow_four (suzukiCoverSylow m hm) hsM hs4'
  obtain ⟨a, b, hab⟩ := suzukiCoverRootElement_surjective m ⟨s, hsQ⟩
  have hzS : (⟨z, hzQ⟩ : suzukiCoverRoot m) =
      suzukiCoverRootElement m 0 (a * suzukiCoverTits m a) := by
    rw [← suzukiCoverRootElement_sq' m hm a b, hab, pow_two]
    exact Subtype.ext hss.symm
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  have ha : a ≠ 0 := by
    rintro rfl
    apply hz1
    have := congrArg Subtype.val hzS
    rw [zero_mul, suzukiCoverRootElement_zero_zero] at this
    exact this
  obtain ⟨c, hc0, hcr⟩ := exists_not_mem_commutator_values m hm ha
  set E := a * suzukiCoverTits m c + c * suzukiCoverTits m a with hE
  set gQ := suzukiCoverRootElement m c 0 with hgQ
  set w := suzukiCoverRootElement m 0 E with hw
  have hgz : ((gQ : suzukiCoverRoot m) : SuzukiMatrixGroup m) ∈
      Subgroup.centralizer ({z} : Set (SuzukiMatrixGroup m)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := suzukiCoverRootElement_zero_mul_comm m hm (a * suzukiCoverTits m a) gQ
    rw [← hzS] at this
    exact congrArg Subtype.val this.symm
  have hconj := h.conj_mem _ hgz s hsN
  have hcomm := suzukiCoverRootElement_commutator m hm a b c 0
  rw [hab] at hcomm
  have hcomm' : s * (gQ : SuzukiMatrixGroup m) =
      (gQ : SuzukiMatrixGroup m) * s * (w : SuzukiMatrixGroup m) := congrArg Subtype.val hcomm
  have hw2 : (w : SuzukiMatrixGroup m) * (w : SuzukiMatrixGroup m) = 1 := by
    have := suzukiCoverRootElement_sq' m hm 0 E
    rw [pow_two, zero_mul, suzukiCoverRootElement_zero_zero] at this
    exact congrArg Subtype.val this
  have hwi : (w : SuzukiMatrixGroup m)⁻¹ = (w : SuzukiMatrixGroup m) :=
    inv_eq_of_mul_eq_one_right hw2
  have hwc : (gQ : SuzukiMatrixGroup m) * (w : SuzukiMatrixGroup m) =
      (w : SuzukiMatrixGroup m) * (gQ : SuzukiMatrixGroup m) :=
    congrArg Subtype.val (suzukiCoverRootElement_zero_mul_comm m hm E gQ).symm
  have hgs : (gQ : SuzukiMatrixGroup m) * s =
      s * (gQ : SuzukiMatrixGroup m) * (w : SuzukiMatrixGroup m)⁻¹ := by
    rw [hcomm']
    group
  have hx : s⁻¹ * ((gQ : SuzukiMatrixGroup m) * s * (gQ : SuzukiMatrixGroup m)⁻¹) =
      (w : SuzukiMatrixGroup m) := by
    calc s⁻¹ * ((gQ : SuzukiMatrixGroup m) * s * (gQ : SuzukiMatrixGroup m)⁻¹)
        = s⁻¹ * (s * (gQ : SuzukiMatrixGroup m) * (w : SuzukiMatrixGroup m)⁻¹ *
            (gQ : SuzukiMatrixGroup m)⁻¹) := by rw [hgs]
      _ = (gQ : SuzukiMatrixGroup m) * (w : SuzukiMatrixGroup m)⁻¹ *
            (gQ : SuzukiMatrixGroup m)⁻¹ := by group
      _ = (w : SuzukiMatrixGroup m) := by
        rw [hwi, hwc]
        group
  have hwN : (w : SuzukiMatrixGroup m) ∈ N := by
    rw [← hx]
    exact N.mul_mem (N.inv_mem hsN) hconj
  have hw1 : (w : SuzukiMatrixGroup m) ≠ 1 := by
    intro h1
    apply hc0
    have : w = suzukiCoverRootElement m 0 0 := by
      rw [suzukiCoverRootElement_zero_zero]
      exact Subtype.ext h1
    exact (suzukiCoverRootElement_injective m 0 E 0 0 this).2
  have hord : orderOf (w : SuzukiMatrixGroup m) = 2 := orderOf_eq_prime (by rwa [pow_two]) hw1
  have hwz := h.eq_of_orderOf_eq_two _ hwN hord
  apply hcr
  have : suzukiCoverRootElement m 0 E = suzukiCoverRootElement m 0 (a * suzukiCoverTits m a) := by
    rw [hzS.symm]
    exact Subtype.ext hwz
  exact ((suzukiCoverRootElement_injective m 0 E 0 _ this).2).symm.symm

theorem noUniqueInvNormal_suzukiMatrixGroup (hm : 0 < m) :
    NoUniqueInvNormal (SuzukiMatrixGroup m) := by
  refine NoUniqueInvNormal.of_conj_reps {r | r ∈ suzukiCoverRoot m ∧ orderOf r = 2} ?_ ?_
  · intro u hu
    obtain ⟨c, s, hs, hs2, hcs⟩ := CFSG.ClassicalInvolution.exists_conj_mem_sylow_of_orderOf_eq_two
      (suzukiCoverSylow m hm) hu
    exact ⟨s, ⟨hs, hs2⟩, c, hcs.symm⟩
  · rintro r ⟨hr, hr2⟩ - N
    exact not_uniqueInvNormal_of_mem_root m hm hr hr2 N

theorem noDatum_of_suzukiModel (F : Type) [Group F] {p f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel F p f) : NoDatum F := by
  have hout := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} F p f h).1.1
  obtain ⟨-, a, ha, L, hLf, hLfin, hf, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card L = 2 ^ (2 * a + 1) := by rw [← hf]; exact hcard
  let e' : F ≃* SuzukiMatrixGroup a :=
    e.trans (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)
  exact noDatum_of_noUniqueInvNormal
    (NoUniqueInvNormal.of_mulEquiv e' (noUniqueInvNormal_suzukiMatrixGroup a ha))
    (fun P _ => by
      have := hout
      exact Subgroup.isCyclic P)

theorem noDatum_of_lieModel_twistedB2 (F : Type) [Group F] {f : ℕ}
    (h : CFSG.Blueprint.LieModel F .twistedB2 0 2 f) : NoDatum F := by
  rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact noDatum_of_suzukiModel F h

end CFSG.ClassicalInvolution.Nobq
