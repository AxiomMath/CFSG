module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelRational
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts.Levi

variable {F : Type} [Field F]

theorem exists_eq_uSL_mul_HSL_of_lower_eq_zero {A : SL2 F}
    (hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) : ∃ (a : Fˣ) (t : F), A = uSL t * HSL a := by
  have ha := SL2_apply_zero_zero_ne_zero hc
  have hdet := det_SL2 A
  rw [hc, mul_zero, sub_zero] at hdet
  refine ⟨Units.mk0 _ ha, (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 1,
    ?_⟩
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two, hc]
  · field_simp
  · exact eq_inv_of_mul_eq_one_right hdet

variable (F) in
@[expose] def leviMulRank1 : Subgroup (ModGL .E7 F) where
  carrier := {x | ∃ n ∈ parabolicLevi .E7 F JE7, ∃ A : SL2 F, x = n * rootSL2 .E7 F thetaE7 A}
  mul_mem' := by
    rintro _ _ ⟨n₁, hn₁, A₁, rfl⟩ ⟨n₂, hn₂, A₂, rfl⟩
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_E7 (inv_mem hn₂) A₁
    rw [inv_inv] at hA'
    refine ⟨n₁ * n₂, mul_mem hn₁ hn₂, A' * A₂, ?_⟩
    calc n₁ * rootSL2 .E7 F thetaE7 A₁ * (n₂ * rootSL2 .E7 F thetaE7 A₂) =
        n₁ * n₂ * (n₂⁻¹ * rootSL2 .E7 F thetaE7 A₁ * n₂) * rootSL2 .E7 F thetaE7 A₂ := by group
      _ = _ := by rw [hA', map_mul]; group
  one_mem' := ⟨1, one_mem _, 1, by simp⟩
  inv_mem' := by
    rintro _ ⟨n, hn, A, rfl⟩
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_E7 hn A⁻¹
    refine ⟨n⁻¹, inv_mem hn, A', ?_⟩
    rw [← hA', map_inv]
    group

theorem toralRootGroup_le_leviMulRank1 (hF : ringChar F ≠ 2) :
    toralRootGroup .E7 F (thetaDiag thetaE7 (-1 : Fˣ)) ≤ leviMulRank1 F := by
  refine sup_le (fun t ht => ⟨t, torusGroup_le_parabolicLevi JE7 ht, 1, by simp⟩) ?_
  refine iSup₂_le fun σ hσ => ?_
  obtain ⟨hσr, hσ1⟩ := hσ
  have hev : Even (iform thetaE7 σ) := by
    refine even_of_neg_one_zpow_eq_one hF ?_
    rw [← rootChar_thetaDiag]
    exact hσ1
  have hL := (exceptional_Lang_root_rank_one_torus_transport .E7 F isRoot_thetaE7).1
  rcases eq_or_iform_eq_zero_of_even_E7 hσr hev with rfl | rfl | h0
  · intro x hx
    have : x ∈ rootRankOneGroup .E7 F thetaE7 := by
      rw [hL]
      exact Subgroup.mem_sup_left hx
    obtain ⟨A, rfl⟩ := this
    exact ⟨1, one_mem _, A, by simp⟩
  · intro x hx
    have : x ∈ rootRankOneGroup .E7 F thetaE7 := by
      rw [hL]
      exact Subgroup.mem_sup_right hx
    obtain ⟨A, rfl⟩ := this
    exact ⟨1, one_mem _, A, by simp⟩
  · intro x hx
    exact ⟨x, rootSubgroup_le_parabolicLevi' (mem_parabolicRoots_E7 hσr h0) hx, 1, by simp⟩


local notation "ρθ" => rootSL2 Tag.E7 F thetaE7

theorem exists_conj_mem_levi_of_inverts_upper (hF : ringChar F ≠ 2) {c : ModGL .E7 F}
    (hcG : c ∈ adjointGroup .E7 F)
    (hcd : c * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) * c)
    (hinv : ∀ t : F, c * ρθ (uSL t) * c⁻¹ = (ρθ (uSL t))⁻¹) :
    ∃ s : F, ρθ (uSL s) * c * (ρθ (uSL s))⁻¹ ∈ parabolicLevi .E7 F JE7 := by
  have hinj : Function.Injective ρθ :=
    ((exceptional_Lang_root_rank_one_data .E7 F thetaE7).2.2.2.2.2.2.2.1 hF).1
  have hcT : c ∈ toralCentralizer .E7 F (thetaDiag thetaE7 (-1 : Fˣ)) := by
    rw [mem_toralCentralizer]
    refine ⟨hcG, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact hcd.symm
  have hM := toralCentralizer_le_toralRootGroup_thetaE7 hF hcT
  obtain ⟨n, hn, A, rfl⟩ := toralRootGroup_le_leviMulRank1 hF hM
  obtain ⟨l', hu', -⟩ := exists_levi_conj_rootSL2_thetaE7 (inv_mem hn)
  have h1 : A * uSL (1 : F) * A⁻¹ = uSL (-(l' : F)) := by
    apply hinj
    have h := hinv 1
    have e : ρθ (A * uSL 1 * A⁻¹) = n⁻¹ * (ρθ (uSL 1))⁻¹ * n := by
      calc ρθ (A * uSL 1 * A⁻¹) = n⁻¹ * (n * ρθ A * ρθ (uSL 1) * (n * ρθ A)⁻¹) * n := by
            rw [map_mul, map_mul, map_inv]; group
        _ = n⁻¹ * (ρθ (uSL 1))⁻¹ * n := by rw [h]
    rw [e, ← map_inv, uSL_inv_eq]
    have h2 := hu' (-1)
    rw [inv_inv] at h2
    rw [h2]
    congr 2
    ring
  have hA10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have e00 := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 0 0)
      (mul_inv_eq_iff_eq_mul.1 h1)
    simp only [Matrix.SpecialLinearGroup.coe_mul] at e00
    simp [uSL, Matrix.mul_apply, Fin.sum_univ_two] at e00
    exact e00
  obtain ⟨a, t, rfl⟩ := exists_eq_uSL_mul_HSL_of_lower_eq_zero hA10
  obtain ⟨l, hu, -⟩ := exists_levi_conj_rootSL2_thetaE7 hn
  set n₁ := n * ρθ (HSL a) with hn₁def
  have hn₁ : n₁ ∈ parabolicLevi .E7 F JE7 :=
    mul_mem hn (torusGroup_le_parabolicLevi JE7
      ((exceptional_Lang_root_rank_one_torus_transport .E7 F isRoot_thetaE7).2.1 a))
  have hc₁ : n * ρθ (uSL t * HSL a) = ρθ (uSL ((l : F) * t)) * n₁ := by
    rw [map_mul]
    calc n * (ρθ (uSL t) * ρθ (HSL a)) = (n * ρθ (uSL t) * n⁻¹) * (n * ρθ (HSL a)) := by group
      _ = _ := by rw [hu t]
  obtain ⟨l₁, hu₁, -⟩ := exists_levi_conj_rootSL2_thetaE7 hn₁
  have hcomm : ∀ y z : F, ρθ (uSL y) * ρθ (uSL z) = ρθ (uSL z) * ρθ (uSL y) := fun y z => by
    rw [← map_mul, ← map_mul, ← uSL_add_eq_mul, ← uSL_add_eq_mul, add_comm]
  have hl₁ : (l₁ : F) = -1 := by
    have h := hinv 1
    rw [hc₁] at h
    have e : ρθ (uSL ((l : F) * t)) * n₁ * ρθ (uSL 1) * (ρθ (uSL ((l : F) * t)) * n₁)⁻¹ =
        ρθ (uSL ((l₁ : F) * 1)) := by
      calc ρθ (uSL ((l : F) * t)) * n₁ * ρθ (uSL 1) * (ρθ (uSL ((l : F) * t)) * n₁)⁻¹ =
          ρθ (uSL ((l : F) * t)) * (n₁ * ρθ (uSL 1) * n₁⁻¹) * (ρθ (uSL ((l : F) * t)))⁻¹ := by
            group
        _ = ρθ (uSL ((l : F) * t)) * ρθ (uSL ((l₁ : F) * 1)) * (ρθ (uSL ((l : F) * t)))⁻¹ := by
            rw [hu₁ 1]
        _ = ρθ (uSL ((l₁ : F) * 1)) := by
            rw [mul_inv_eq_iff_eq_mul, hcomm]
    rw [e, ← map_inv, uSL_inv_eq] at h
    have h3 := uSL_injective_of_field (hinj h)
    simpa using h3
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  refine ⟨-((l : F) * t / 2), ?_⟩
  have e1 : n₁ * (ρθ (uSL (-((l : F) * t / 2))))⁻¹ * n₁⁻¹ = ρθ (uSL (-((l : F) * t / 2))) := by
    rw [← map_inv, uSL_inv_eq, neg_neg]
    have := hu₁ ((l : F) * t / 2)
    rw [hl₁] at this
    rw [this, neg_one_mul]
  have e2 : ρθ (uSL (-((l : F) * t / 2))) * (ρθ (uSL ((l : F) * t)) * n₁) *
      (ρθ (uSL (-((l : F) * t / 2))))⁻¹ = n₁ := by
    calc ρθ (uSL (-((l : F) * t / 2))) * (ρθ (uSL ((l : F) * t)) * n₁) *
        (ρθ (uSL (-((l : F) * t / 2))))⁻¹ =
        ρθ (uSL (-((l : F) * t / 2))) * ρθ (uSL ((l : F) * t)) *
          (n₁ * (ρθ (uSL (-((l : F) * t / 2))))⁻¹ * n₁⁻¹) * n₁ := by group
      _ = ρθ (uSL (-((l : F) * t / 2))) * ρθ (uSL ((l : F) * t)) *
          ρθ (uSL (-((l : F) * t / 2))) * n₁ := by rw [e1]
      _ = n₁ := by
        rw [← map_mul, ← map_mul, ← uSL_add_eq_mul, ← uSL_add_eq_mul]
        have : -((l : F) * t / 2) + (l : F) * t + -((l : F) * t / 2) = 0 := by
          field_simp
          ring
        rw [this, uSL_zero_eq_one, map_one, one_mul]
  rw [hc₁, e2]
  exact hn₁

theorem HSL_neg_one_mul (g : SL2 F) : HSL (-1 : Fˣ) * g = g * HSL (-1 : Fˣ) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem rootSL2_uSL_comm (y z : F) :
    ρθ (uSL y) * ρθ (uSL z) = ρθ (uSL z) * ρθ (uSL y) := by
  rw [← map_mul, ← map_mul, ← uSL_add_eq_mul, ← uSL_add_eq_mul, add_comm]

theorem exists_conj_mem_levi_of_inverts [Finite F] {p f : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ f) (hF : ringChar F ≠ 2) {c : ModGL .E7 F}
    (hcG : c ∈ adjointGroup .E7 F)
    (hcd : c * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) * c)
    {U : Subgroup (SL2 F)} (hU : Nat.card U = Nat.card F)
    (hinv : ∀ A ∈ U, c * ρθ A * c⁻¹ = (ρθ A)⁻¹) :
    ∃ e : SL2 F, ρθ e * c * (ρθ e)⁻¹ ∈ parabolicLevi .E7 F JE7 ∧
      (ρθ e * c * (ρθ e)⁻¹) * ρθ (uSL 1) * (ρθ e * c * (ρθ e)⁻¹)⁻¹ = (ρθ (uSL 1))⁻¹ := by
  obtain ⟨g, hg⟩ := CFSG.SL2MinimalFaithful.exists_conj_unipotent_mem hp hcard hU
  set d := rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) with hd
  have hdθ : d = ρθ (HSL (-1)) := (rootTorusSL2_thetaE7 (-1)).symm
  have hgd : ∀ x : SL2 F, Commute (ρθ x) d := fun x => by
    show ρθ x * d = d * ρθ x
    rw [hdθ, ← map_mul, ← map_mul, HSL_neg_one_mul]
  set r := ρθ g with hr
  set c₁ := r⁻¹ * c * r with hc₁
  have hc₁G : c₁ ∈ adjointGroup .E7 F :=
    mul_mem (mul_mem (inv_mem (rootSL2_mem_adjointGroup _ _)) hcG)
      (rootSL2_mem_adjointGroup _ _)
  have hc₁d : c₁ * d = d * c₁ := by
    have h1 : Commute (r⁻¹ * c * r) d :=
      (((hgd g).inv_left).mul_left (show Commute c d from hcd)).mul_left (hgd g)
    exact h1
  have hc₁inv : ∀ t : F, c₁ * ρθ (uSL t) * c₁⁻¹ = (ρθ (uSL t))⁻¹ := fun t => by
    have h := hinv (g * uSL t * g⁻¹) (hg t)
    have h' : c * (r * ρθ (uSL t) * r⁻¹) * c⁻¹ = (r * ρθ (uSL t) * r⁻¹)⁻¹ := by
      simpa only [map_mul, map_inv] using h
    calc c₁ * ρθ (uSL t) * c₁⁻¹ =
        r⁻¹ * (c * (r * ρθ (uSL t) * r⁻¹) * c⁻¹) * r := by rw [hc₁]; group
      _ = r⁻¹ * (r * ρθ (uSL t) * r⁻¹)⁻¹ * r := by rw [h']
      _ = (ρθ (uSL t))⁻¹ := by group
  obtain ⟨s, hs⟩ := exists_conj_mem_levi_of_inverts_upper hF hc₁G hc₁d hc₁inv
  have hconj : ρθ (uSL s * g⁻¹) * c * (ρθ (uSL s * g⁻¹))⁻¹ = ρθ (uSL s) * c₁ * (ρθ (uSL s))⁻¹ := by
    simp only [map_mul, map_inv, hc₁, hr]
    group
  refine ⟨uSL s * g⁻¹, ?_, ?_⟩
  · rw [hconj]
    exact hs
  · rw [hconj]
    have hab : ρθ (uSL s) * ρθ (uSL 1) = ρθ (uSL 1) * ρθ (uSL s) := rootSL2_uSL_comm s 1
    have hc : (ρθ (uSL s))⁻¹ * ρθ (uSL 1) * ρθ (uSL s) = ρθ (uSL 1) := by
      calc (ρθ (uSL s))⁻¹ * ρθ (uSL 1) * ρθ (uSL s) =
          (ρθ (uSL s))⁻¹ * (ρθ (uSL 1) * ρθ (uSL s)) := by group
        _ = (ρθ (uSL s))⁻¹ * (ρθ (uSL s) * ρθ (uSL 1)) := by rw [← hab]
        _ = ρθ (uSL 1) := by group
    have hc' : ρθ (uSL s) * (ρθ (uSL 1))⁻¹ * (ρθ (uSL s))⁻¹ = (ρθ (uSL 1))⁻¹ := by
      have h3 : (ρθ (uSL 1))⁻¹ * ρθ (uSL s) = ρθ (uSL s) * (ρθ (uSL 1))⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hab]
        group
      rw [← h3]
      group
    calc ρθ (uSL s) * c₁ * (ρθ (uSL s))⁻¹ * ρθ (uSL 1) *
          (ρθ (uSL s) * c₁ * (ρθ (uSL s))⁻¹)⁻¹ =
        ρθ (uSL s) * (c₁ * ((ρθ (uSL s))⁻¹ * ρθ (uSL 1) * ρθ (uSL s)) * c₁⁻¹) *
          (ρθ (uSL s))⁻¹ := by group
      _ = ρθ (uSL s) * (c₁ * ρθ (uSL 1) * c₁⁻¹) * (ρθ (uSL s))⁻¹ := by rw [hc]
      _ = ρθ (uSL s) * (ρθ (uSL 1))⁻¹ * (ρθ (uSL s))⁻¹ := by rw [hc₁inv 1]
      _ = (ρθ (uSL 1))⁻¹ := hc'

end CFSG.ClassicalInvolution.ModelFacts.E7Model
