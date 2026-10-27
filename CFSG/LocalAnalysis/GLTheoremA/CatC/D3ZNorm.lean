module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FCoord

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three


section Perm

theorem perm_eq_one_of_commute_sq (ε : ℕ) (hε : ε = 1 ∨ ε = 2) (π : Equiv.Perm (Fin Tag.D4.rank))
    (hπ : π * d4Rho ^ ε = d4Rho ^ ε * π) (h2 : π * π = 1) : π = 1 := by
  rcases hε with rfl | rfl
  · revert π
    unfold d4Rho TwistTag.perm
    decide +kernel
  · revert π
    unfold d4Rho TwistTag.perm
    decide +kernel

end Perm

section Aux

variable {K : Type} [Field K] [Finite K]

theorem d3z_d4Graph_zero : d4Graph K 0 = 1 :=
  MulEquiv.ext fun x => Subtype.ext (by simp [coe_d4Graph])

theorem perm_exactNormalAut (b : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) :
    simplePermHom Tag.D4 K ⟨exactNormalAut Tag.D4 K b σ 0, exactNormalAut_mem b σ 0⟩ = 1 := by
  let α : unipotentPairAut Tag.D4 K := ⟨exactNormalAut Tag.D4 K b σ 0, exactNormalAut_mem b σ 0⟩
  show simplePerm Tag.D4 K α = 1
  refine perm_map_simple_unique (α := (α : MulAut (adjointGroup Tag.D4 K)))
    (fun i => (simplePerm_spec α i).1) (fun i => ?_)
  rw [map_simplePosSubgroup_exactNormalAut]
  rfl

theorem perm_normal_graph (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) :
    simplePermHom Tag.D4 K ⟨exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε,
      mul_mem (exactNormalAut_mem a σ 0) (d4Graph_mem ε)⟩ = d4Rho ^ ε := by
  let α : unipotentPairAut Tag.D4 K := ⟨exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε,
      mul_mem (exactNormalAut_mem a σ 0) (d4Graph_mem ε)⟩
  show simplePerm Tag.D4 K α = d4Rho ^ ε
  refine perm_map_simple_unique (α := (α : MulAut (adjointGroup Tag.D4 K)))
    (fun i => (simplePerm_spec α i).1) (fun i => ?_)
  show (simplePosSubgroup Tag.D4 K i).map (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε).toMonoidHom = _
  rw [map_toMonoidHom_mul_mulAut, map_simplePosSubgroup_d4Graph,
    map_simplePosSubgroup_exactNormalAut]
  rfl

theorem perm_conj_eq_one (x : adjointGroup Tag.D4 K)
    (hx : MulAut.conj x ∈ unipotentPairAut Tag.D4 K) :
    simplePermHom Tag.D4 K ⟨MulAut.conj x, hx⟩ = 1 := by
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag hx
  have h1 : (⟨MulAut.conj x, hx⟩ : unipotentPairAut Tag.D4 K) =
      ⟨exactNormalAut Tag.D4 K b 1 0, exactNormalAut_mem b 1 0⟩ := Subtype.ext hb
  rw [h1]
  exact perm_exactNormalAut b 1

end Aux

section ZForm

variable {K : Type} [Field K] [Finite K]

theorem z_normal_form (t z : MulAut (adjointGroup Tag.D4 K)) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (hε : ε = 1 ∨ ε = 2)
    (ht : t = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))
    (hz2 : z * z = 1) (hzt : z * t = t * z) :
    ∃ (c : adjointGroup Tag.D4 K) (a_z : Fin Tag.D4.rank → Kˣ) (σ_z : K ≃+* K),
      σ_z ^ 2 = 1 ∧ z = MulAut.conj c * exactNormalAut Tag.D4 K a_z σ_z 0 := by
  classical
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨c, β, hU, hV, hzβ⟩ :=
    (exceptional_ordinary_Sylow_opposition Tag.D4 K (ringChar K) w₀ hw₀).2.2.2.2.2 z
  have hβA : β ∈ unipotentPairAut Tag.D4 K := ⟨hU, hV⟩
  set βt : MulAut (adjointGroup Tag.D4 K) := exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε with hβt
  have hβtA : βt ∈ unipotentPairAut Tag.D4 K :=
    mul_mem (exactNormalAut_mem a σ 0) (d4Graph_mem ε)
  let Bz : unipotentPairAut Tag.D4 K := ⟨β, hβA⟩
  let Bt : unipotentPairAut Tag.D4 K := ⟨βt, hβtA⟩
  have hpt : simplePermHom Tag.D4 K Bt = d4Rho ^ ε := perm_normal_graph a σ ε
  have e1 : z * t = MulAut.conj (c * β g) * (β * βt) := by
    rw [hzβ, ht]
    calc MulAut.conj c * β * (MulAut.conj g * βt)
        = MulAut.conj c * (β * MulAut.conj g) * βt := by group
      _ = MulAut.conj c * (MulAut.conj (β g) * β) * βt := by rw [mul_conj_eq]
      _ = MulAut.conj (c * β g) * (β * βt) := by rw [map_mul]; group
  have e2 : t * z = MulAut.conj (g * βt c) * (βt * β) := by
    rw [hzβ, ht]
    calc MulAut.conj g * βt * (MulAut.conj c * β)
        = MulAut.conj g * (βt * MulAut.conj c) * β := by group
      _ = MulAut.conj g * (MulAut.conj (βt c) * βt) * β := by rw [mul_conj_eq]
      _ = MulAut.conj (g * βt c) * (βt * β) := by rw [map_mul]; group
  obtain ⟨x, hx⟩ : ∃ x : adjointGroup Tag.D4 K, x = (c * β g)⁻¹ * (g * βt c) := ⟨_, rfl⟩
  have hxx : β * βt = MulAut.conj x * (βt * β) := by
    have h := hzt
    rw [e1, e2] at h
    have h' := congrArg (fun m => (MulAut.conj (c * β g))⁻¹ * m) h
    rw [hx, map_mul, map_inv]
    calc β * βt = (MulAut.conj (c * β g))⁻¹ * (MulAut.conj (c * β g) * (β * βt)) := by group
      _ = (MulAut.conj (c * β g))⁻¹ * (MulAut.conj (g * βt c) * (βt * β)) := h'
      _ = _ := (mul_assoc _ _ _).symm
  have hxA : MulAut.conj x ∈ unipotentPairAut Tag.D4 K := by
    have : MulAut.conj x = (β * βt) * (βt * β)⁻¹ := by rw [hxx]; group
    rw [this]
    exact mul_mem (mul_mem hβA hβtA) (inv_mem (mul_mem hβtA hβA))
  have hcomm : simplePermHom Tag.D4 K Bz * simplePermHom Tag.D4 K Bt =
      simplePermHom Tag.D4 K Bt * simplePermHom Tag.D4 K Bz := by
    have h1 : Bz * Bt = ⟨MulAut.conj x, hxA⟩ * (Bt * Bz) := Subtype.ext hxx
    have h2 := congrArg (simplePermHom Tag.D4 K) h1
    have hp1 := perm_conj_eq_one x hxA
    calc simplePermHom Tag.D4 K Bz * simplePermHom Tag.D4 K Bt
        = simplePermHom Tag.D4 K (Bz * Bt) := (map_mul _ _ _).symm
      _ = simplePermHom Tag.D4 K (⟨MulAut.conj x, hxA⟩ * (Bt * Bz)) := h2
      _ = simplePermHom Tag.D4 K ⟨MulAut.conj x, hxA⟩ *
          (simplePermHom Tag.D4 K Bt * simplePermHom Tag.D4 K Bz) := by rw [map_mul, map_mul]
      _ = simplePermHom Tag.D4 K Bt * simplePermHom Tag.D4 K Bz := by rw [hp1, one_mul]
  have hsq : β * β = MulAut.conj (c * β c)⁻¹ := by
    have h := hz2
    rw [hzβ] at h
    have e3 : MulAut.conj c * β * (MulAut.conj c * β) = MulAut.conj (c * β c) * (β * β) := by
      calc MulAut.conj c * β * (MulAut.conj c * β) = MulAut.conj c * (β * MulAut.conj c) * β := by group
        _ = MulAut.conj c * (MulAut.conj (β c) * β) * β := by rw [mul_conj_eq]
        _ = MulAut.conj (c * β c) * (β * β) := by rw [map_mul]; group
    rw [e3] at h
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_right h
  have hyA : MulAut.conj (c * β c)⁻¹ ∈ unipotentPairAut Tag.D4 K := by
    rw [← hsq]; exact mul_mem hβA hβA
  have hperm2 : simplePermHom Tag.D4 K Bz * simplePermHom Tag.D4 K Bz = 1 := by
    have h1 : Bz * Bz = ⟨MulAut.conj (c * β c)⁻¹, hyA⟩ := Subtype.ext hsq
    have h2 := congrArg (simplePermHom Tag.D4 K) h1
    have hp1 := perm_conj_eq_one (c * β c)⁻¹ hyA
    calc simplePermHom Tag.D4 K Bz * simplePermHom Tag.D4 K Bz
        = simplePermHom Tag.D4 K (Bz * Bz) := (map_mul _ _ _).symm
      _ = simplePermHom Tag.D4 K ⟨MulAut.conj (c * β c)⁻¹, hyA⟩ := h2
      _ = 1 := hp1
  have hπ1 : simplePermHom Tag.D4 K Bz = 1 := by
    refine perm_eq_one_of_commute_sq ε hε _ ?_ hperm2
    rw [← hpt]; exact hcomm
  have hmap : ∀ i, (simplePosSubgroup Tag.D4 K i).map β.toMonoidHom =
        simplePosSubgroup Tag.D4 K ((d4Rho ^ 0) i) ∧
      (simpleNegSubgroup Tag.D4 K i).map β.toMonoidHom = simpleNegSubgroup Tag.D4 K ((d4Rho ^ 0) i) := by
    intro i
    have := simplePerm_spec Bz i
    have e : simplePerm Tag.D4 K Bz = 1 := hπ1
    rw [e] at this
    simpa using this
  obtain ⟨a_z, σ_z, hβ⟩ := exists_normalAut_mul_graph hmap
  rw [d3z_d4Graph_zero, mul_one] at hβ
  refine ⟨c, a_z, σ_z, ?_, by rw [hzβ, hβ]⟩
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag hyA
  have hsq' : exactNormalAut Tag.D4 K a_z σ_z 0 * exactNormalAut Tag.D4 K a_z σ_z 0 =
      exactNormalAut Tag.D4 K b 1 0 := by
    rw [← hb, ← hsq, hβ]
  rw [exactNormalAut_mul] at hsq'
  refine RingEquiv.ext fun u => ?_
  have h1 := congrArg (fun m => m (adjX Tag.D4 K 0 u)) hsq'
  have h0 := congrArg (fun m => m (adjX Tag.D4 K 0 1)) hsq'
  simp only [exactNormalAut_adjX] at h1 h0
  have h1' := adjX_injective (τ := Tag.D4) (K := K) 0 h1
  have h0' := adjX_injective (τ := Tag.D4) (K := K) 0 h0
  simp at h0' h1'
  have hperm : exactPerm Tag.D4 0 = 1 := rfl
  rw [hperm] at h0' h1'
  simp only [Equiv.Perm.one_apply] at h0' h1'
  have hA : ((a_z 0 : Kˣ) : K) * σ_z ((a_z 0 : Kˣ) : K) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (by simpa using Units.ne_zero (a_z 0))
  rw [← h0'] at h1'
  have e : σ_z (σ_z u) = u := mul_left_cancel₀ hA h1'
  rw [pow_two, RingAut.mul_apply]
  exact e

end ZForm

end CFSG.LocalAnalysis.GLTheoremA
