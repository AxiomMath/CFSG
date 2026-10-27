module

public import CFSG.ClassicalInvolution.Q3.TL4StarSecGD
public import CFSG.ClassicalInvolution.Q3.Q3AM289Z4
public import CFSG.ClassicalInvolution.Q3.TL4StarSecSqrt

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section U3

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Q3.Q3PP

theorem su3_sqrt_root : ∃ k : SU3, (∀ r ∈ rootSU2₃, k * r = r * k) ∧ k * k = rootInvSU₃ := by
  obtain ⟨i, hi⟩ := Q3T8.Asc77.s3_exists_sq_neg_one_F9
  set j : SU3 := blockEmb F9 3 1 3 2 0 (by omega) (Q3T8.Asc77.jjSU hi) with hj
  set d : SU3 := blockEmb F9 3 1 3 2 1 (by omega) (negOneSU F9 3 1) with hd
  have hmat : suMat (j * d) = Matrix.diagonal ![i, i, -1] := by
    rw [suMat_mul, hj, hd, Q3T8.Asc77.suMat_blockEmb_jj hi, Q3T8.Asc77.suMat_blockEmb_negOne,
      Matrix.diagonal_mul_diagonal]
    congr 1
    ext a
    fin_cases a <;> simp
  refine ⟨j * d, fun r hr => ?_, ?_⟩
  · obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hr
    apply suMat_injective
    rw [suMat_mul (j * d), suMat_mul _ (j * d), hmat, suMat_blockEmb]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [blockMat_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  · apply suMat_injective
    rw [suMat_mul, hmat, suMat_rootInvSU₃, Matrix.diagonal_mul_diagonal]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hi]

theorem su3_sqrt : SqrtFund (CompData.model .PSU 3) := by
  intro R hR
  obtain ⟨e', he'⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num)
    Q3PP.statedLieAdmissible_psu3
  obtain ⟨g₀, hg₀⟩ := (Models.mem_longRootSetU_iff (by norm_num)).mp ((he' R).mp hR)
  have hg₀' : R.map e'.toMonoidHom = conjSub g₀ rootSU2₃ := hg₀
  have hmemR : ∀ y, y ∈ conjSub g₀ rootSU2₃ → e'.symm y ∈ R := fun y hy => by
    rw [← hg₀'] at hy
    exact Subgroup.mem_map_equiv.mp hy
  obtain ⟨k₀, hk₀, hkk₀⟩ := su3_sqrt_root
  have hsq : e'.symm (g₀ * k₀ * g₀⁻¹) * e'.symm (g₀ * k₀ * g₀⁻¹) =
      e'.symm (g₀ * rootInvSU₃ * g₀⁻¹) := by
    rw [← map_mul, ← hkk₀]
    congr 1
    group
  have hrinv : rootInvSU₃ ∈ rootSU2₃ := ⟨negOneSU F9 3 1, rfl⟩
  refine ⟨e'.symm (g₀ * k₀ * g₀⁻¹), fun x hx => ?_, ?_, ?_, ?_⟩
  · have hx' : e' x ∈ conjSub g₀ rootSU2₃ := hg₀' ▸ Subgroup.mem_map_of_mem e'.toMonoidHom hx
    set y := g₀⁻¹ * e' x * g₀ with hy
    have hyr : y ∈ rootSU2₃ := mem_conjSub_iff.mp hx'
    have hxe : e' x = g₀ * y * g₀⁻¹ := by rw [hy]; group
    apply e'.injective
    rw [map_mul e', map_mul e', MulEquiv.apply_symm_apply, hxe]
    calc g₀ * k₀ * g₀⁻¹ * (g₀ * y * g₀⁻¹) = g₀ * (k₀ * y) * g₀⁻¹ := by group
      _ = g₀ * (y * k₀) * g₀⁻¹ := by rw [hk₀ y hyr]
      _ = g₀ * y * g₀⁻¹ * (g₀ * k₀ * g₀⁻¹) := by group
  · rw [hsq]
    exact hmemR _ (conj_mem_conjSub hrinv)
  · rw [hsq]
    intro h
    apply rootInvSU₃_ne_one
    have h1 : g₀ * rootInvSU₃ * g₀⁻¹ = 1 := by
      rw [← e'.apply_symm_apply (g₀ * rootInvSU₃ * g₀⁻¹), h, map_one]
    calc rootInvSU₃ = g₀⁻¹ * (g₀ * rootInvSU₃ * g₀⁻¹) * g₀ := by group
      _ = 1 := by rw [h1]; group
  · rw [hsq, ← map_mul]
    have h1 : g₀ * rootInvSU₃ * g₀⁻¹ * (g₀ * rootInvSU₃ * g₀⁻¹) = 1 := by
      calc g₀ * rootInvSU₃ * g₀⁻¹ * (g₀ * rootInvSU₃ * g₀⁻¹) =
          g₀ * (rootInvSU₃ * rootInvSU₃) * g₀⁻¹ := by group
        _ = 1 := by rw [rootInvSU₃_mul_self]; group
    rw [h1, map_one]

end U3

section Bridge

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem starNbr_of_q8Shape {c : CompData} (hZ : Subgroup.center c.G = ⊥)
    (hconj : S19M.InvolutionsConj c.G) (hsq : SqrtFund c) (hR : TypeRFam 3 Φ)
    (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') (h : SecIdQ8Shape c Φ) :
    ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L := by
  obtain ⟨ψ, hsurj, hker, hfund⟩ := h
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hconjX : S19M.InvolutionsConj X :=
    S19M.InvolutionsConj.of_mulEquiv (MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm hconj
  intro L hL
  obtain ⟨R, hRf, hLR⟩ := hfund L hL
  obtain ⟨k, hk, hkR, hk1, hk2⟩ := hsq R hRf
  obtain ⟨⟨z, hz⟩, -⟩ := hR.hyp.omega1 L hL
  have hk' : ∀ x ∈ L, ψ k * x = x * ψ k := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hLR.1 hx
    rw [← map_mul, ← map_mul, hk x' hx']
  have hc2 : ψ (k * k) * ψ (k * k) = 1 := by rw [← map_mul, hk2, map_one]
  have hc1 : ψ (k * k) ≠ 1 := fun h => hk1 (hinj (h.trans (map_one ψ).symm))
  have hzL : ψ (k * k) ∈ L := by
    have h2 : IsPGroup 2 (Subgroup.zpowers (ψ (k * k))) :=
      IsPGroup.of_card (n := 1)
        (by rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1, pow_one])
    have hN : Subgroup.zpowers (ψ (k * k)) ≤ Subgroup.normalizer (L : Set X) := by
      refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (L : Set X) ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [map_mul]
      calc x * (ψ k * ψ k) = (x * ψ k) * ψ k := by group
        _ = (ψ k * x) * ψ k := by rw [← hk' x hx]
        _ = ψ k * (x * ψ k) := by group
        _ = ψ k * (ψ k * x) := by rw [← hk' x hx]
        _ = ψ k * ψ k * x := by group
    have h3 : IsPGroup 2 ↥(L ⊔ Subgroup.zpowers (ψ (k * k))) :=
      hLR.2.1.to_sup_of_normal_left' h2 hN
    have h4 := hLR.2.2 _ (sup_le hLR.1 (Subgroup.zpowers_le.mpr
      (Subgroup.mem_map_of_mem ψ hkR))) h3 le_sup_left
    exact h4 ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hzeq : ψ (k * k) = z := (hz.unique _ hzL hc2).resolve_left hc1
  have hkk' : ψ k * ψ k = z := by rw [← map_mul, hzeq]
  exact starNbr_of_sqrt_involutionsConj hR htr hconjX hL hz hk' hkk' L hL

end Bridge

section LieS3


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem starNbr_of_lieS3 (hR : TypeRFam 3 Φ)
    (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') (h : SecIdLieS3 Φ) :
    ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L := by
  rcases h with h | h | h
  · exact starNbr_of_q8Shape (Q3T8.Asc77.center_eq_bot_of_rows (Or.inl rfl))
      (Q3T8.Asc77.involutionsConj_of_rows (Or.inl rfl)) su3_sqrt hR htr h
  · exact starNbr_of_q8Shape (Q3T8.Asc77.center_eq_bot_of_rows (Or.inr (Or.inl rfl)))
      (Q3T8.Asc77.involutionsConj_of_rows (Or.inr (Or.inl rfl)))
      (fun R hR' => g2_sqrt (p := 3) (e := 1) (by norm_num) le_rfl hR') hR htr h
  · exact starNbr_of_q8Shape (Q3T8.Asc77.center_eq_bot_of_rows (Or.inr (Or.inr rfl)))
      (Q3T8.Asc77.involutionsConj_of_rows (Or.inr (Or.inr rfl)))
      (fun R hR' => td4_sqrt (p := 3) (by norm_num) (e := 1)
        (show CFSG.Assembly.LowTwoRank.StatedLieAdmissible .trialityD4 0 3 1 from
          ⟨Nat.prime_three, le_rfl, rfl⟩) hR') hR htr h

end LieS3

end CFSG.ClassicalInvolution.Q3.TL4
