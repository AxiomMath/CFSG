module

public import CFSG.CGT.Timmesfeld75.ListWCLinMain
import CFSG.LargeExtraspecial.A2ModSL
import CFSG.CGT.T75N.L29Levi
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourRoots
import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelSL

open CFSG.CGT.Timmesfeld75 Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem exists_dot_eq_zero_not_smul {m : ℕ} (hm : 3 ≤ m) (c α : Fin m → K) :
    ∃ d : Fin m → K, α ⬝ᵥ d = 0 ∧ ∀ μ : K, d ≠ μ • c := by
  by_contra hcon
  push Not at hcon
  have hle : LinearMap.ker (dotLin α) ≤ K ∙ c := by
    intro d hd
    obtain ⟨μ, hμ⟩ := hcon d hd
    rw [Submodule.mem_span_singleton]
    exact ⟨μ, hμ.symm⟩
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank K (K ∙ c) ≤ 1 :=
    (finrank_span_le_card ({c} : Set (Fin m → K))).trans (by simp)
  have h3 := LinearMap.finrank_range_add_finrank_ker (dotLin α)
  have h4 : Module.finrank K (LinearMap.range (dotLin α)) ≤ 1 :=
    (Submodule.finrank_le _).trans (by simp)
  rw [Module.finrank_fin_fun] at h3
  omega

theorem exists_ne_zero_dot_eq_zero_pair {m : ℕ} (hm : 3 ≤ m) (c d : Fin m → K) :
    ∃ γ : Fin m → K, γ ≠ 0 ∧ γ ⬝ᵥ c = 0 ∧ γ ⬝ᵥ d = 0 := by
  let f : (Fin m → K) →ₗ[K] K × K := (dotLin c).prod (dotLin d)
  have hlt : Module.finrank K (K × K) < Module.finrank K (Fin m → K) := by
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]
    omega
  obtain ⟨γ, hγ, hne⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt hlt)
  have hf : f γ = 0 := LinearMap.mem_ker.1 hγ
  refine ⟨γ, hne, ?_, ?_⟩
  · have := congrArg Prod.fst hf
    simpa [f, dotLin_apply, dotProduct_comm] using this
  · have := congrArg Prod.snd hf
    simpa [f, dotLin_apply, dotProduct_comm] using this

private theorem tvSL_zero_eq_one {n : ℕ} (c : Fin n → K) (h : (0 : Fin n → K) ⬝ᵥ c = 0) :
    tvSL c 0 h = 1 :=
  Subtype.ext (by rw [coe_tvSL, vecMulVec_zero, add_zero, Matrix.SpecialLinearGroup.coe_one])

private theorem tvSL_add_eq_mul {n : ℕ} {c a b : Fin n → K} (ha : a ⬝ᵥ c = 0) (hb : b ⬝ᵥ c = 0)
    (hab : (a + b) ⬝ᵥ c = 0) : tvSL c (a + b) hab = tvSL c a ha * tvSL c b hb :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL, coe_tvSL, coe_tvSL, tv_mul_tv_center ha])

private theorem tvSL_neg_eq_inv {n : ℕ} {c a : Fin n → K} (ha : a ⬝ᵥ c = 0)
    (hna : (-a) ⬝ᵥ c = 0) : tvSL c (-a) hna = (tvSL c a ha)⁻¹ :=
  Subtype.ext (by rw [coe_tvSL, coe_tvSL_inv, vecMulVec_neg, sub_eq_add_neg])

theorem tvCenterSL_single_zero_le {m' : ℕ} (H : Subgroup SL(m' + 2, K))
    (hH : ∀ (γ : Fin (m' + 2) → K) (h : γ ⬝ᵥ (Pi.single (0 : Fin (m' + 2)) (1 : K)) = 0),
      (∃ j : Fin (m' + 2), j ≠ 0 ∧ ∃ μ : K, γ = μ • Pi.single j 1) →
      tvSL (Pi.single (0 : Fin (m' + 2)) (1 : K)) γ h ∈ H) :
    tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K)) ≤ H := by
  set e₀ : Fin (m' + 2) → K := Pi.single (0 : Fin (m' + 2)) (1 : K) with he₀
  let A : AddSubgroup (Fin (m' + 2) → K) :=
    { carrier := {a | ∃ h : a ⬝ᵥ e₀ = 0, tvSL e₀ a h ∈ H}
      zero_mem' := ⟨zero_dotProduct e₀, by rw [tvSL_zero_eq_one]; exact H.one_mem⟩
      add_mem' := by
        rintro a b ⟨ha, hHa⟩ ⟨hb, hHb⟩
        exact ⟨by rw [add_dotProduct, ha, hb, add_zero],
          by rw [tvSL_add_eq_mul ha hb]; exact H.mul_mem hHa hHb⟩
      neg_mem' := by
        rintro a ⟨ha, hHa⟩
        exact ⟨by rw [neg_dotProduct, ha, neg_zero],
          by rw [tvSL_neg_eq_inv ha]; exact H.inv_mem hHa⟩ }
  rintro x ⟨a, ha, hx⟩
  have hxa : x = tvSL e₀ a ha := Subtype.ext hx
  have ha0 : a 0 = 0 := by simpa [he₀, dotProduct_single] using ha
  have hsum : ∑ j ∈ Finset.univ.erase (0 : Fin (m' + 2)), a j • Pi.single j (1 : K) = a := by
    rw [Finset.sum_erase _ (by rw [ha0, zero_smul]), ← pi_eq_sum_univ']
  have hmem : ∑ j ∈ Finset.univ.erase (0 : Fin (m' + 2)), a j • Pi.single j (1 : K) ∈ A := by
    refine A.sum_mem fun j hj => ?_
    have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
    set γ : Fin (m' + 2) → K := a j • Pi.single j (1 : K) with hγ
    have hγ0 : γ ⬝ᵥ e₀ = 0 := by
      simp [hγ, he₀, hj0]
    exact ⟨hγ0, hH γ hγ0 ⟨j, hj0, a j, rfl⟩⟩
  rw [hsum] at hmem
  obtain ⟨_, hmem⟩ := hmem
  rw [hxa]
  exact hmem

private theorem tvCenterSL_eq_pointGroup {n : ℕ} (c : Fin n → K) :
    tvCenterSL c = CFSG.LargeExtraspecial.A2Mod.pointGroup c := by
  ext x
  rw [mem_tvCenterSL, CFSG.LargeExtraspecial.A2Mod.mem_pointGroup]
  constructor
  · rintro ⟨a, ha, hx⟩
    exact ⟨a, ha, Subtype.ext (by rw [CFSG.LargeExtraspecial.A2Mod.coe_tv ha, hx])⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, CFSG.LargeExtraspecial.A2Mod.coe_tv ha⟩

private theorem tvAxisSL_eq_hyperplaneGroup {n : ℕ} (a : Fin n → K) :
    tvAxisSL a = CFSG.LargeExtraspecial.A2Mod.hyperplaneGroup a := by
  ext x
  rw [mem_tvAxisSL, CFSG.LargeExtraspecial.A2Mod.mem_hyperplaneGroup]
  constructor
  · rintro ⟨v, hv, hx⟩
    exact ⟨v, hv, Subtype.ext (by rw [CFSG.LargeExtraspecial.A2Mod.coe_tv hv, hx])⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, CFSG.LargeExtraspecial.A2Mod.coe_tv hv⟩

theorem tvCenterSL_sup_tvAxisSL_single_zero (m' : ℕ) :
    tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K)) ⊔
      tvAxisSL (Pi.single (0 : Fin (m' + 2)) (1 : K)) = ⊤ := by
  rw [tvCenterSL_eq_pointGroup, tvAxisSL_eq_hyperplaneGroup]
  exact CFSG.LargeExtraspecial.A2Mod.pointGroup_sup_hyperplaneGroup 0

section Involutions

open CFSG.CGT.T75N CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem rootElt_mulVec_single_zero {n : ℕ} {i j : Fin (n + 2)} (hij : i < j) (a : K) :
    ((rootElt i j a : SL(n + 2, K)) : Matrix (Fin (n + 2)) (Fin (n + 2)) K) *ᵥ
      (Pi.single (0 : Fin (n + 2)) (1 : K) : Fin (n + 2) → K) = Pi.single 0 1 := by
  have hj : j ≠ 0 := ((Fin.zero_le i).trans_lt hij).ne'
  rw [coe_rootElt_of_ne hij.ne, Matrix.transvection, add_mulVec, one_mulVec, single_mulVec_eq,
    Pi.single_eq_of_ne hj, mul_zero, zero_smul, add_zero]

private theorem rootElt_mul_self_eq_one [CharP K 2] {n : ℕ} (i j : Fin n) (a : K) :
    rootElt i j a * rootElt i j a = (1 : SL(n, K)) := by
  rw [← rootElt_add, CharTwo.add_self_eq_zero, rootElt_zero]

private theorem mem_of_mem_unitriangular [CharP K 2] {n : ℕ} (H : Subgroup SL(n + 2, K))
    (hH : ∀ t : SL(n + 2, K), t * t = 1 →
      (t : Matrix (Fin (n + 2)) (Fin (n + 2)) K) *ᵥ Pi.single 0 1 =
        (Pi.single (0 : Fin (n + 2)) (1 : K) : Fin (n + 2) → K) → t ∈ H)
    {u : SL(n + 2, K)} (hu : u ∈ unitriangular (n + 2) K) : u ∈ H := by
  refine (Subgroup.closure_le H).2 ?_ (unitriangular_le_closure_rootElt hu)
  rintro _ ⟨i, j, a, hij, rfl⟩
  exact hH _ (rootElt_mul_self_eq_one i j a) (rootElt_mulVec_single_zero hij a)

private theorem epsHom_mem_of_forall_involution [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    (H : Subgroup SL(n + 2, K))
    (hH : ∀ t : SL(n + 2, K), t * t = 1 →
      (t : Matrix (Fin (n + 2)) (Fin (n + 2)) K) *ᵥ Pi.single 0 1 =
        (Pi.single (0 : Fin (n + 2)) (1 : K) : Fin (n + 2) → K) → t ∈ H)
    (A : SL(n + 1, K)) : epsHom n K A ∈ H := by
  have : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  have htop : H.comap (epsHom n K) = ⊤ := by
    refine CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem _
      fun i j hij c => ?_
    rw [Subgroup.mem_comap]
    refine hH _ ?_ (epsHom_fix_e0 _)
    rw [← map_mul, ← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
      Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]
  have hA : A ∈ H.comap (epsHom n K) := by
    rw [htop]
    exact Subgroup.mem_top A
  exact hA

end Involutions

theorem mem_of_forall_involution_fix [CharP K 2] {m' : ℕ} (hm' : 1 ≤ m')
    (H : Subgroup SL(m' + 2, K))
    (hH : ∀ t : SL(m' + 2, K), t * t = 1 →
      (t : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K) *ᵥ Pi.single 0 1 =
        (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K) → t ∈ H)
    {g : SL(m' + 2, K)}
    (hg : (g : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K) *ᵥ Pi.single 0 1 =
      (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K)) :
    g ∈ H := by
  obtain ⟨A, hA⟩ := CFSG.CGT.T75N.exists_unitriangular_of_fix g hg
  have hu := mem_of_mem_unitriangular H hH hA
  have he := epsHom_mem_of_forall_involution hm' H hH A
  simpa using H.mul_mem hu he

end CFSG.ClassicalGroups.Orthogonal.SiegelSL
