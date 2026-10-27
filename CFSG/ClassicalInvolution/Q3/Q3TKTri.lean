module

public import CFSG.ClassicalInvolution.Q3.Q3TJTri
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.Q3TKComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
open CFSG.ComponentClassification CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

theorem exists_eq_conj_of_sq_eq_one_td4 (β : MulAut (twistedGroup σ27)) (hβ : β ^ 2 = 1) :
    ∃ g : twistedGroup σ27, β = MulAut.conj g := by
  have hσ' : ∀ c, σe27 c = c ^ (3 ^ 1) := fun c => iterateFrobeniusEquiv_def F27 3 1 c
  have hK : Nat.card F27 = (3 ^ 1) ^ 3 := by
    rw [GaloisField.card 3 (3 * 1) (by norm_num)]
    norm_num
  obtain ⟨-, -, ⟨Θ, -, -, hker, hinv⟩, -⟩ := odd_triality_exact_automorphism_normal_form
    Nat.prime_three (by norm_num) le_rfl F27 hK σe27 hσ'
  have hrange : (twistedIncl σ27).range = graphFixedRootGroup TwistTag.D4 F27 σ27 :=
    range_twistedIncl_eq (p := 3) (by norm_num) 1 le_rfl
  have hC : graphFixedRootGroup TwistTag.D4 F27 σ27 =
      graphFixedRootGroup TwistTag.D4 F27 σe27.toRingHom := rfl
  let ι : twistedGroup σ27 ≃* ↥(graphFixedRootGroup TwistTag.D4 F27 σe27.toRingHom) :=
    (MonoidHom.ofInjective (twistedIncl_injective σ27)).trans
      (MulEquiv.subgroupCongr (hrange.trans hC))
  have hγ2 : MulAut.congr ι β ^ 2 = 1 := by rw [← map_pow, hβ, map_one]
  rcases hinv _ hγ2 with h | ⟨hev, -⟩
  · obtain ⟨c, hc⟩ : MulAut.congr ι β ∈
        (MulAut.conj : graphFixedRootGroup TwistTag.D4 F27 σe27.toRingHom →* _).range := by
      rw [← hker]
      exact h
    refine ⟨ι.symm c, (MulAut.congr ι).injective ?_⟩
    rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, hc]
  · exact absurd hev (by decide)

theorem slB_mul_neg_one_comm (B : SL(2, F27)) :
    slB σ27 σ27_cube B * slB σ27 σ27_cube (-1) = slB σ27 σ27_cube (-1) * slB σ27 σ27_cube B := by
  have hcen : B * (-1) = (-1) * B := by
    ext i j
    simp
  calc slB σ27 σ27_cube B * slB σ27 σ27_cube (-1) = slB σ27 σ27_cube (B * -1) :=
        (map_mul _ _ _).symm
    _ = slB σ27 σ27_cube (-1 * B) := by rw [hcen]
    _ = slB σ27 σ27_cube (-1) * slB σ27 σ27_cube B := map_mul _ _ _

theorem exists_conj_eq_slB_neg_one {x : twistedGroup σ27} (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ h : twistedGroup σ27, h * x * h⁻¹ = slB σ27 σ27_cube (-1) := by
  have hτ2 : slB σ27 σ27_cube (-1) * slB σ27 σ27_cube (-1) = 1 := by
    rw [← map_mul, neg_one_mul_neg_one_SL2, map_one]
  have hK1 := neg_one_ne_one_galoisField_td4 (p := 3) (by norm_num) (3 * 1)
  have hτ1 : slB σ27 σ27_cube (-1) ≠ 1 := by
    intro h
    rw [← map_one (slB σ27 σ27_cube)] at h
    have h2 := congrArg (fun B : SL(2, F27) => (B : Matrix (Fin 2) (Fin 2) F27) 0 0)
      (slB_injective σ27_cube h)
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h2
    exact hK1 (Units.ext (by simpa using h2))
  exact CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj
    (p := 3) (by norm_num) le_rfl hx2 hτ2 hx1 hτ1

theorem exists_slB_conj_of_commute {c : twistedGroup σ27}
    (hc : c * slB σ27 σ27_cube (-1) = slB σ27 σ27_cube (-1) * c) (B : SL(2, F27)) :
    ∃ B' : SL(2, F27), c * slB σ27 σ27_cube B * c⁻¹ = slB σ27 σ27_cube B' := by
  have hK1 := neg_one_ne_one_galoisField_td4 (p := 3) (by norm_num) (3 * 1)
  have hrange : (twistedIncl σ27).range = graphFixedRootGroup TwistTag.D4 F27 σ27 :=
    range_twistedIncl_eq (p := 3) (by norm_num) 1 le_rfl
  have hgF : ∀ x : twistedGroup σ27,
      twistedIncl σ27 x ∈ graphFixedRootGroup TwistTag.D4 F27 σ27 :=
    fun x => hrange ▸ ⟨x, rfl⟩
  rw [slB_neg_one σ27_cube] at hc
  exact SProd_conj_slB σ27_cube (mem_SProd_of_centralizes σ27_cube hK1 hrange.ge hgF hc) B

theorem eq_conj_of_fix_slB_td4 (β : MulAut (twistedGroup σ27))
    (hβ : ∀ B : SL(2, F27), β (slB σ27 σ27_cube B) = slB σ27 σ27_cube B) :
    ∃ g : twistedGroup σ27, β = MulAut.conj g := by
  obtain ⟨n, hn⟩ : ∃ n : twistedGroup σ27, n = nB σ27 := ⟨_, rfl⟩
  have hB : ∀ A, n * slShort σ27 σ27_cube A * n⁻¹ = slB σ27 σ27_cube A := fun A => by
    rw [hn, slB_apply]
  obtain ⟨γ, hγdef⟩ : ∃ γ : MulAut (twistedGroup σ27),
      γ = (MulAut.conj n)⁻¹ * β * MulAut.conj n := ⟨_, rfl⟩
  have hγapp : ∀ y, γ y = n⁻¹ * β (n * y * n⁻¹) * n := fun y => by
    rw [hγdef, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
  have hγ : ∀ A, γ (slShort σ27 σ27_cube A) = slShort σ27 σ27_cube A := by
    intro A
    rw [hγapp, hB, hβ, ← hB]
    group
  obtain ⟨g, hg⟩ := eq_conj_of_fix_slShort_td4 γ hγ
  refine ⟨n * g * n⁻¹, MulEquiv.ext fun y => ?_⟩
  have h1 := hγapp (n⁻¹ * y * n)
  rw [hg, MulAut.conj_apply] at h1
  have h2 : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
  rw [h2] at h1
  rw [MulAut.conj_apply]
  calc β y = n * (n⁻¹ * β y * n) * n⁻¹ := by group
    _ = n * (g * (n⁻¹ * y * n) * g⁻¹) * n⁻¹ := by rw [← h1]
    _ = n * g * n⁻¹ * y * (n * g * n⁻¹)⁻¹ := by group

theorem mem_of_socle_td4 {Y : Type} [Group Y] {T : Subgroup Y} [T.Normal]
    (hCT : Subgroup.centralizer (T : Set Y) = ⊥) (e : twistedGroup σ27 ≃* T) {z : Y}
    (hz2 : orderOf z = 2) : z ∈ T := by
  have h2 : (MulAut.congr e.symm (MulAut.conjNormal z : MulAut T)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ← hz2, pow_orderOf_eq_one, map_one, map_one]
  obtain ⟨g, hg⟩ := exists_eq_conj_of_sq_eq_one_td4 _ h2
  have h3 : (MulAut.conjNormal z : MulAut T) = MulAut.conj (e g) := by
    apply (MulAut.congr e.symm).injective
    rw [hg, OuterAutomorphisms.congr_conj, MulEquiv.symm_apply_apply]
  rw [eq_of_conjNormal_eq_conj hCT h3]
  exact (e g).2

theorem le_of_socle_td4 {Y : Type} [Group Y] [Finite Y] {z : Y} {L : Subgroup Y}
    (hz : IsClassicalMember3 L z) {T : Subgroup Y} [hTn : T.Normal]
    (hCT : Subgroup.centralizer (T : Set Y) = ⊥) (e : twistedGroup σ27 ≃* T) : L ≤ T := by
  have hzT := mem_of_socle_td4 hCT e hz.orderOf_eq_two
  obtain ⟨zT, hzTdef⟩ : ∃ zT : T, zT = ⟨z, hzT⟩ := ⟨_, rfl⟩
  have hzT2 : zT * zT = 1 := by
    rw [hzTdef]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← sq, ← hz.orderOf_eq_two, pow_orderOf_eq_one]
  have hzT1 : zT ≠ 1 := by
    rw [hzTdef]
    intro h
    exact hz.ne_one (congrArg Subtype.val h)
  have hz₀2 : e.symm zT * e.symm zT = 1 := by rw [← map_mul, hzT2, map_one]
  have hz₀1 : e.symm zT ≠ 1 := fun h => hzT1 (e.symm.injective (h.trans (map_one _).symm))
  obtain ⟨h, hh⟩ := exists_conj_eq_slB_neg_one hz₀2 hz₀1
  obtain ⟨ε, hε⟩ : ∃ ε : T ≃* twistedGroup σ27, ε = e.symm.trans (MulAut.conj h) := ⟨_, rfl⟩
  have hτz : ((ε.symm (slB σ27 σ27_cube (-1)) : T) : Y) = z := by
    have hεz : ε zT = slB σ27 σ27_cube (-1) := by
      rw [hε, MulEquiv.trans_apply, MulAut.conj_apply]
      exact hh
    rw [← hεz, MulEquiv.symm_apply_apply, hzTdef]
  have h4 : 4 ≤ Nat.card F27 := by
    rw [GaloisField.card 3 (3 * 1) (by norm_num)]
    norm_num
  intro x hx
  have hxB := commute_of_component_of_member (F := F27) (G := twistedGroup σ27) h4 hz ε hτz
    (slB σ27 σ27_cube) (slB_injective σ27_cube) slB_mul_neg_one_comm
    (fun c hc B => exists_slB_conj_of_commute hc B) x hx
  obtain ⟨β, hβdef⟩ : ∃ β, β = MulAut.congr ε (MulAut.conjNormal x : MulAut T) := ⟨_, rfl⟩
  have hβ : ∀ B, β (slB σ27 σ27_cube B) = slB σ27 σ27_cube B := by
    intro B
    have h1 : (MulAut.conjNormal x (ε.symm (slB σ27 σ27_cube B)) : T) =
        ε.symm (slB σ27 σ27_cube B) := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hxB B, mul_inv_cancel_right]
    rw [hβdef]
    show ε (MulAut.conjNormal x (ε.symm (slB σ27 σ27_cube B))) = slB σ27 σ27_cube B
    rw [h1, MulEquiv.apply_symm_apply]
  obtain ⟨g, hg⟩ := eq_conj_of_fix_slB_td4 β hβ
  have hα : (MulAut.conjNormal x : MulAut T) = MulAut.conj (ε.symm g) := by
    apply (MulAut.congr ε).injective
    rw [← hβdef, hg, OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
  rw [eq_of_conjNormal_eq_conj hCT hα]
  exact (ε.symm g).2

end CFSG.ClassicalInvolution.Q3.Q3T
