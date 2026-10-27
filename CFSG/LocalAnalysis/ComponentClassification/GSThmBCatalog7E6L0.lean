module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6Grp
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4F2Model
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Conf

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ABGLocalTools

namespace Cat7E6

open CatFactsSp4 Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag
open scoped commutatorElement

section General

variable {K₀ : Type} [Group K₀] [Finite K₀]

omit [Finite K₀] in
theorem L0_le_innFix (α : MulAut K₀) : Cat8.L0 K₀ α ≤ Cat8.innFix K₀ α := by
  rw [Cat8.L0, commutator_le]
  intro x hx y hy
  exact (Cat8.innFix K₀ α).mul_mem ((Cat8.innFix K₀ α).mul_mem
    ((Cat8.innFix K₀ α).mul_mem hx hy) ((Cat8.innFix K₀ α).inv_mem hx))
    ((Cat8.innFix K₀ α).inv_mem hy)

omit [Finite K₀] in
theorem innFix_le (α : MulAut K₀) :
    Cat8.innFix K₀ α ≤ Cat8.innA K₀ α ⊓ centralizer ({α} : Set (MulAut K₀)) :=
  inf_le_inf_right _ le_sup_left

theorem map_conj_innFix {α x : MulAut K₀} (hx : x ∈ centralizer ({α} : Set (MulAut K₀))) :
    (Cat8.innFix K₀ α).map (MulAut.conj x).toMonoidHom = Cat8.innFix K₀ α := by
  have : Finite (MulAut K₀) := Finite.of_injective (fun φ : MulAut K₀ => (φ : K₀ → K₀))
    (fun φ ψ h => MulEquiv.ext (congrFun h))
  apply Subgroup.eq_of_le_of_card_ge _ (by rw [Subgroup.card_map_of_injective
    (MulAut.conj x).injective])
  rintro _ ⟨y, ⟨hyI, hyC⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · exact (inn_normal (G := K₀)).conj_mem _ hyI x
  · change x * y * x⁻¹ ∈ centralizer ({α} : Set (MulAut K₀))
    exact mul_mem (mul_mem hx hyC) (inv_mem hx)

theorem le_normalizer_L0 (α : MulAut K₀) :
    Cat8.innA K₀ α ⊓ centralizer ({α} : Set (MulAut K₀)) ≤
      normalizer ((Cat8.L0 K₀ α : Subgroup (MulAut K₀)) : Set (MulAut K₀)) := by
  have : Finite (MulAut K₀) := Finite.of_injective (fun φ : MulAut K₀ => (φ : K₀ → K₀))
    (fun φ ψ h => MulEquiv.ext (congrFun h))
  intro x hx
  apply mem_normalizer_of_conj_mem
  intro y hy
  have h : (Cat8.L0 K₀ α).map (MulAut.conj x).toMonoidHom = Cat8.L0 K₀ α := by
    rw [Cat8.L0, Subgroup.map_commutator, map_conj_innFix hx.2]
  rw [← h]
  exact ⟨y, hy, rfl⟩

theorem isSylowOf_D {q : ℕ} (c : Cat8.QConf K₀ q) : IsSylowOf 2 c.D (Cat8.L0 K₀ c.a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut K₀) := Finite.of_injective (fun φ : MulAut K₀ => (φ : K₀ → K₀))
    (fun φ ψ h => MulEquiv.ext (congrFun h))
  have hQ : IsSylowOf 2 c.Q (Cat8.innA K₀ c.a ⊓ centralizer ({c.a} : Set (MulAut K₀))) := by
    obtain ⟨T, hT⟩ := c.Q_sylow
    refine ⟨T, ?_⟩
    rw [hT, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr c.Q_le]
  exact hQ.inf_of_le_normalizer ((L0_le_innFix c.a).trans (innFix_le c.a)) (le_normalizer_L0 c.a)

end General

variable {K : Type} [Field K]

@[expose] def trx : Matrix (Fin 2) (Fin 2) K := !![1, 1; 0, 1]
@[expose] def try' : Matrix (Fin 2) (Fin 2) K := !![1, 0; 1, 1]

theorem center_P_eq_one [Finite K] (hodd : Odd (Nat.card K)) {z : StatedProj (StatedSp 2 K)}
    (hz : z ∈ center (StatedProj (StatedSp 2 K))) : z = 1 := by
  have h2 := two_ne_zero_of_odd_card hodd
  have hq3 : 3 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hodd
    omega
  have hs : IsSimpleGroup (StatedProj (StatedSp 2 K)) := by
    apply CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
    rcases Nat.lt_or_ge (Nat.card K) 4 with h | h
    · exact Or.inr (Or.inl ⟨by omega, le_rfl⟩)
    · exact Or.inl (Or.inr h)
  rcases (center (StatedProj (StatedSp 2 K))).normal_of_characteristic.eq_bot_or_eq_top with
    hb | ht
  · rw [hb] at hz
    exact hz
  · exfalso
    have hdx : (trx : Matrix (Fin 2) (Fin 2) K).det = 1 := by simp [trx, det_fin_two]
    have hdy : (try' : Matrix (Fin 2) (Fin 2) K).det = 1 := by simp [try', det_fin_two]
    set X := toSp (blk trx 1) (blk_symplectic_of_det hdx det_one) with hX
    set Y := toSp (blk try' 1) (blk_symplectic_of_det hdy det_one) with hY
    have hc := mem_center_iff.mp (ht ▸ mem_top (proj 2 K X)) (proj 2 K Y)
    rw [← map_mul, ← map_mul] at hc
    rcases eq_or_eq_neg_of_proj_eq hc with h | h
    · have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
      simp [hX, hY, blk, trx, try', diag2, Matrix.mul_apply, Fin.sum_univ_two] at this
    · have := congrFun (congrFun h (Sum.inl 1)) (Sum.inl 1)
      simp [hX, hY, blk, trx, try', diag2, Matrix.mul_apply, Fin.sum_univ_two] at this
      exact h2 (by linear_combination this)

theorem commutator_fix_eq_map (θ : MulAut (StatedSp 2 K))
    {α : MulAut (StatedProj (StatedSp 2 K))} (hθα : ∀ g, α (proj 2 K g) = proj 2 K (θ g))
    (hperf : Group.IsPerfect (fixOf θ)) :
    ⁅fixOf α, fixOf α⁆ = (fixOf θ).map (proj 2 K) := by
  have hfix : ∀ x ∈ fixOf α, ∃ g, proj 2 K g = x ∧ θ g * g⁻¹ ∈ spScalars 2 K := by
    intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective x
    refine ⟨g, rfl, ?_⟩
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, ← hθα, mem_fixOf.mp hx, mul_inv_cancel]
  apply le_antisymm
  · rw [commutator_le]
    intro x hx y hy
    obtain ⟨g, rfl, hg⟩ := hfix x hx
    obtain ⟨h, rfl, hh⟩ := hfix y hy
    refine ⟨⁅g, h⁆, ?_, map_commutatorElement _ _ _⟩
    exact fix_commutator (fun z hz => mem_center_of_mem_spScalars hz) θ.toMonoidHom hg hh
  · have hc : ⁅fixOf θ, fixOf θ⁆ = fixOf θ := by
      have h := congrArg (Subgroup.map (fixOf θ).subtype) hperf.commutator_eq_top
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h
      exact h
    rw [← hc, Subgroup.map_commutator]
    exact commutator_mono (map_fixOf_le θ hθα) (map_fixOf_le θ hθα)

theorem L0_eq_map [Finite K] (hodd : Odd (Nat.card K)) (A : gsp 2 K)
    (hperf : Group.IsPerfect (fixOf (conjSp 2 K A))) :
    Cat8.L0 (StatedProj (StatedSp 2 K)) (conjAut 2 K A) =
      ((fixOf (conjSp 2 K A)).map (proj 2 K)).map (MulAut.conj : _ →* MulAut _) := by
  have hc : ∀ z : StatedProj (StatedSp 2 K), z ∈ center _ → z = 1 :=
    fun z hz => center_P_eq_one hodd hz
  have hθα : ∀ g, conjAut 2 K A (proj 2 K g) = proj 2 K (conjSp 2 K A g) := fun g => rfl
  rw [← commutator_fix_eq_map _ hθα hperf, Subgroup.map_commutator, map_conj_fixOf hc]

theorem card_L0 [Finite K] (hodd : Odd (Nat.card K)) (A : gsp 2 K)
    (hperf : Group.IsPerfect (fixOf (conjSp 2 K A))) :
    Nat.card (Cat8.L0 (StatedProj (StatedSp 2 K)) (conjAut 2 K A)) * 2 =
      Nat.card (fixOf (conjSp 2 K A)) := by
  have hc : ∀ z : StatedProj (StatedSp 2 K), z ∈ center _ → z = 1 :=
    fun z hz => center_P_eq_one hodd hz
  rw [L0_eq_map hodd A hperf, Subgroup.card_map_of_injective
    (fun g h hgh => conj_injective_of_center hc hgh)]
  exact card_map_fixOf_mul_two (two_ne_zero_of_odd_card hodd) _ (fun z hz => conjSp_scalar A hz)

end Cat7E6

end CFSG.ComponentClassification.GSThmB
