module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureUnitMain
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureSymplectic
import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank Matrix Subgroup SpClosure
  CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC

theorem mem_twoLocalClosure_of_equiv {G H : Type} [Group G] [Group H] (Φ : G ≃* H)
    (E : Subgroup G) {g : G} (h : Φ g ∈ twoLocalClosure (E.map Φ.toMonoidHom)) :
    g ∈ twoLocalClosure E := by
  have hle := map_twoLocalClosure_le Φ.symm (E.map Φ.toMonoidHom)
  have hE : (E.map Φ.toMonoidHom).map Φ.symm.toMonoidHom = E := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨Φ x, ⟨x, hx, rfl⟩, by simp⟩
  rw [hE] at hle
  have := hle ⟨Φ g, h, rfl⟩
  simpa using this

section Unitary

variable {K : Type} [Field K] {f : ℕ} (n : ℕ)

@[expose] noncomputable def suGamma (K : Type) [Field K] (f : ℕ) :
    Subgroup ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
  (StatedSU n (2 ^ f) K).map (toLinEquiv (Fin n) K).toMonoidHom

@[expose] noncomputable def suEquiv (K : Type) [Field K] (f : ℕ) :
    StatedSU n (2 ^ f) K ≃* suGamma n K f :=
  (toLinEquiv (Fin n) K).subgroupMap _

variable {n}

variable [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]

theorem unitData_statedSU (hK : Nat.card K = (2 ^ f) ^ 2) :
    UnitClosure.UnitData (unitaryForm 2 f hK n) (suGamma n K f) where
  herm u v := (unitaryForm_symm hK u v).symm
  invol := unitaryInvolution_involutive hK
  trace a ha := exists_add_unitaryInvolution_eq hK ha
  iso g u v := by
    obtain ⟨A, hA, hAg⟩ := g.2
    have : (g : (Fin n → K) ≃ₗ[K] (Fin n → K)) = toLinEquiv (Fin n) K A := hAg.symm
    show (unitaryForm 2 f hK n).β ((g : (Fin n → K) ≃ₗ[K] (Fin n → K)) u)
      ((g : (Fin n → K) ≃ₗ[K] (Fin n → K)) v) = _
    rw [this]
    exact statedSU_preserves hK hA u v
  eichler x y c hx hxy hc := by
    obtain ⟨A, hA, hAv⟩ := exists_mem_statedSU_eichler hK hx hxy hc
    exact ⟨⟨toLinEquiv (Fin n) K A, ⟨A, hA, rfl⟩⟩, fun v => hAv v⟩

theorem exists_invariant_isotropic_statedSU (hK : Nat.card K = (2 ^ f) ^ 2)
    {R E : Subgroup (StatedSU n (2 ^ f) K)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hE : E ≤ Subgroup.normalizer (R : Set (StatedSU n (2 ^ f) K))) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (unitaryForm 2 f hK n).IsTotallyIsotropic W ∧
      ∀ e ∈ E, ∀ w ∈ W, ((e : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
  have hρ := isIsometric_natRep_statedSU hK n
  have hinj : Function.Injective (natRep (StatedSU n (2 ^ f) K)) := natRep_injective _
  refine ⟨isoSeq (unitaryForm 2 f hK n) (natRep (StatedSU n (2 ^ f) K)) R 1,
    isoSeq_one_ne_bot _ _ 2 hρ hinj R hR2 hR, isoSeq_isTotallyIsotropic _ _ R 1,
    fun e he w hw => ?_⟩
  have := apply_mem_isoSeq _ _ hρ R 1 (hE he) hw
  rwa [natRep_apply] at this

@[expose] def tvSetSU (hK : Nat.card K = (2 ^ f) ^ 2) (n : ℕ) : Set (StatedSU n (2 ^ f) K) :=
  {g | ∃ (a : Fin n → K) (c : K), (unitaryForm 2 f hK n).β a a = 0 ∧
    unitaryInvolution K 2 f c = -c ∧
    ∀ v, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
      v + (c * (unitaryForm 2 f hK n).β a v) • a}

theorem tvSetSU_conj (hK : Nat.card K = (2 ^ f) ^ 2) (g t : StatedSU n (2 ^ f) K)
    (ht : t ∈ tvSetSU hK n) : g * t * g⁻¹ ∈ tvSetSU hK n := by
  obtain ⟨a, c, ha, hc, hT⟩ := ht
  have hU := unitData_statedSU (n := n) hK
  have hT' : ∀ v, suEquiv n K f t • v = v + (c * (unitaryForm 2 f hK n).β a v) • a := hT
  refine ⟨suEquiv n K f g • a, c, ?_, hc, fun v => ?_⟩
  · rw [hU.iso, ha]
  · have := hU.conj_tv hT' (suEquiv n K f g) v
    rw [← map_inv, ← map_mul, ← map_mul] at this
    exact this

theorem tvSetSU_subset_twoLocalClosure (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 3 ≤ n)
    (E P : Subgroup (StatedSU n (2 ^ f) K)) (hE : Odd (Nat.card E)) (hP : P ≠ ⊥)
    (hP2 : IsPGroup 2 P) (hEN : E ≤ Subgroup.normalizer (P : Set (StatedSU n (2 ^ f) K))) :
    tvSetSU hK n ⊆ (twoLocalClosure E : Set (StatedSU n (2 ^ f) K)) := by
  rintro T ⟨a, c, ha, hc, hT⟩
  obtain ⟨W, hW0, hWti, hWE⟩ := exists_invariant_isotropic_statedSU hK hP hP2 hEN
  have hU := unitData_statedSU (n := n) hK
  have hd : 3 ≤ Module.finrank K (Fin n → K) := by simpa using hn
  refine mem_twoLocalClosure_of_equiv (suEquiv n K f) E ?_
  refine UnitClosure.tv_mem_twoLocalClosure hU hd (E.map (suEquiv n K f).toMonoidHom) ?_ hW0
    hWti ?_ ha (fun v => hT v)
  · rwa [Subgroup.card_map_of_injective (suEquiv n K f).injective]
  · rintro _ ⟨e, he, rfl⟩ x hx
    exact hWE e he x hx

theorem exists_tvSetSU_not_scalar (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 3 ≤ n) :
    ∃ t ∈ tvSetSU hK n,
      t ∉ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) := by
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  set a₀ : Fin n → K := Pi.single i0 1 + Pi.single i1 1 with ha₀
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hβ : ∀ v, (unitaryForm 2 f hK n).β a₀ v = v i0 + v i1 := by
    intro v
    simp [unitaryForm_β, ha₀, add_mul, Finset.sum_add_distrib, Pi.single_apply]
  have hiso : (unitaryForm 2 f hK n).β a₀ a₀ = 0 := by
    rw [hβ]
    simp [ha₀, h01, h01.symm]
    linear_combination h2
  obtain ⟨c, hc0, hc⟩ := exists_unitaryInvolution_eq_neg hK
  obtain ⟨A, hA, hAv⟩ := exists_mem_statedSU_transvection hK hiso hc
  refine ⟨⟨_, hA⟩, ⟨a₀, c, hiso, hc, hAv⟩, fun hsc => ?_⟩
  obtain ⟨u, hu⟩ := hsc
  have h1 := congrFun (hAv (Pi.single i0 1)) i1
  have hu' : A = Matrix.GeneralLinearGroup.scalar (Fin n) u := hu.symm
  rw [hu', hβ] at h1
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal,
    h01.symm, ha₀] at h1
  exact hc0 h1.symm

end Unitary

theorem not_rankThreeUC_of_PSU {G : Type} [Group G] [Finite G] (hS : Standing G) {n f : ℕ}
    (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2)
    (e : G ≃* StatedProj (StatedSU n (2 ^ f) K)) : ¬ rankThreeUC G := by
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := f) hK
  exact not_rankThreeUC_of_proj_gen hS (StatedSU n (2 ^ f) K) e (tvSetSU hK n)
    (tvSetSU_conj hK) (exists_tvSetSU_not_scalar hK hn)
    (fun E P hE hP hP2 hEN => tvSetSU_subset_twoLocalClosure hK hn E P hE hP hP2 hEN)

end CFSG.LocalAnalysis.RankThreeUC
