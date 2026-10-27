module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F12Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.PlaneTree

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin (pairVec)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

@[expose] noncomputable def tPair
    (a b : Fin 24) : Q3 :=
  (((e0.symm (cocodeCoords.κ (pairVec (tauM24 a) (tauM24 b))) : ↥E0q) : ↥Zq) : Q3)

@[expose] noncomputable def t13 :
    Q3 :=
  tPair 0 2

theorem tPair_mem_E0
    (a b : Fin 24) :
    tPair a b ∈ E0 :=
  (e0.symm (cocodeCoords.κ (pairVec (tauM24 a) (tauM24 b)))).2

theorem t13_mem_E0 :
    t13 ∈ E0 :=
  tPair_mem_E0 0 2

theorem tPair_comm
    (a b : Fin 24) :
    tPair a b = tPair b a := by
  have h : pairVec (tauM24 a) (tauM24 b) = pairVec (tauM24 b) (tauM24 a) :=
    mul_comm _ _
  unfold tPair
  rw [h]

theorem tPair_mul_tPair
    (a b c : Fin 24) :
    tPair a b * tPair a c = tPair b c := by
  have hv : pairVec (tauM24 a) (tauM24 b) * pairVec (tauM24 a) (tauM24 c) =
      pairVec (tauM24 b) (tauM24 c) := by
    unfold pairVec
    rw [mul_mul_mul_comm, unitVec_sq, one_mul]
  have h : e0.symm (cocodeCoords.κ (pairVec (tauM24 a) (tauM24 b))) *
      e0.symm (cocodeCoords.κ (pairVec (tauM24 a) (tauM24 c))) =
      e0.symm (cocodeCoords.κ (pairVec (tauM24 b) (tauM24 c))) := by
    rw [← map_mul, ← map_mul, hv]
  exact congrArg (fun z : ↥E0q => ((z : ↥Zq) : Q3)) h

theorem conj_tPair
    {g : Q3} (hg : g ∈ Zq) {a b c d : Fin 24} (hac : g • planePt a = planePt c)
    (hbd : g • planePt b = planePt d) : g * tPair a b * g⁻¹ = tPair c d := by
  let x : ↥E0q := e0.symm (cocodeCoords.κ (pairVec (tauM24 a) (tauM24 b)))
  let n : ↥Zq := ⟨g, hg⟩
  have hx : e0 x = cocodeCoords.κ (pairVec (tauM24 a) (tauM24 b)) :=
    MulEquiv.apply_symm_apply e0 _
  have hpa : planeHom n a = c := (smul_planePt_eq_planePt_iff n a c).1 hac
  have hpb : planeHom n b = d := (smul_planePt_eq_planePt_iff n b d).1 hbd
  have hpia : ((cocodeExtension_Zq.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) (tauM24 a) =
      tauM24 c := by
    rw [π_cocodeExtension_Zq]
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hpa]
  have hpib : ((cocodeExtension_Zq.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) (tauM24 b) =
      tauM24 d := by
    rw [π_cocodeExtension_Zq]
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hpb]
  have hp := cocodeExtension_Zq.π_apply_e n x
  rw [hx, rho11_kappa_pairVec, hpia, hpib] at hp
  have hconj : cocodeExtension_Zq.conjE n x =
      e0.symm (cocodeCoords.κ (pairVec (tauM24 c) (tauM24 d))) := by
    apply e0.injective
    rw [MulEquiv.apply_symm_apply]
    exact hp.symm
  have key : (((cocodeExtension_Zq.conjE n x : ↥E0q) : ↥Zq) : Q3) =
      g * ((x : ↥Zq) : Q3) * g⁻¹ := by
    rw [cocodeExtension_Zq.coe_conjE]
    rfl
  show g * ((x : ↥Zq) : Q3) * g⁻¹ = _
  rw [← key, hconj]
  rfl

@[expose] noncomputable def g0 :
    Q3 :=
  Classical.choose (exists_mem_Zq_smul_base_triple x1_mem_plane x2_mem_plane x0_mem_plane
    x1_ne_x2 x0_ne_x1.symm x0_ne_x2.symm)

theorem g0_spec :
    g0 ∈ Zq ∧ g0 • x0 = x1 ∧ g0 • x1 = x2 ∧ g0 • x2 = x0 :=
  Classical.choose_spec (exists_mem_Zq_smul_base_triple x1_mem_plane x2_mem_plane x0_mem_plane
    x1_ne_x2 x0_ne_x1.symm x0_ne_x2.symm)

theorem g0_mem_Zq :
    g0 ∈ Zq :=
  g0_spec.1

theorem g0_smul_x0 :
    g0 • x0 = x1 :=
  g0_spec.2.1

theorem g0_smul_x1 :
    g0 • x1 = x2 :=
  g0_spec.2.2.1

theorem g0_smul_x2 :
    g0 • x2 = x0 :=
  g0_spec.2.2.2

theorem g0_conj_t0 :
    g0 * t0 * g0⁻¹ = t0 * t13 := by
  have h := conj_tPair (a := 0) (b := 1) (c := 1) (d := 2) g0_mem_Zq
    (by rw [planePt_zero, planePt_one]; exact g0_smul_x0)
    (by rw [planePt_one, planePt_two]; exact g0_smul_x1)
  have e : tPair 1 2 = t0 * t13 := (tPair_mul_tPair 0 1 2).symm
  exact h.trans e

theorem g0_conj_t13 :
    g0 * t13 * g0⁻¹ = t0 := by
  have h := conj_tPair (a := 0) (b := 2) (c := 1) (d := 0) g0_mem_Zq
    (by rw [planePt_zero, planePt_one]; exact g0_smul_x0)
    (by rw [planePt_two, planePt_zero]; exact g0_smul_x2)
  have e : tPair 1 0 = t0 := tPair_comm 1 0
  exact h.trans e

theorem conj_g0_mem_Ze_iff
    {x : Q3} : g0⁻¹ * x * g0 ∈ Ze ↔ x ∈ Ze'' := by
  have h : ∀ {p q : Ω}, (g0⁻¹ * x * g0) • p = q ↔ x • (g0 • p) = g0 • q := by
    intro p q
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
  rw [mem_Ze_iff, mem_Ze''_iff, h, h, h, h, g0_smul_x0, g0_smul_x1]

theorem conj_g0_mem_Q0_iff
    {x : Q3} : g0⁻¹ * x * g0 ∈ Q0 ↔ x ∈ Q0 := by
  have h : ∀ {p q : Ω}, (g0⁻¹ * x * g0) • p = q ↔ x • (g0 • p) = g0 • q := by
    intro p q
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
  rw [mem_Q0_iff_of_fix, mem_Q0_iff_of_fix, h, h, h, g0_smul_x0, g0_smul_x1, g0_smul_x2]
  tauto

theorem Ze_inf_Ze'' :
    Ze ⊓ Ze'' = Q0 := by
  ext g
  rw [Subgroup.mem_inf, mem_Ze_iff, mem_Ze''_iff, mem_Q0_iff_of_fix]
  constructor
  · rintro ⟨h | h, h' | h'⟩
    · exact ⟨h.1, h.2, h'.2⟩
    · exact absurd (h.2.symm.trans h'.1) x1_ne_x2
    · exact absurd (h.2.symm.trans h'.1) x0_ne_x1
    · exact absurd (h.2.symm.trans h'.1) x0_ne_x2
  · rintro ⟨h0, h1, h2⟩
    exact ⟨Or.inl ⟨h0, h1⟩, Or.inl ⟨h1, h2⟩⟩

theorem mul_comm_t13_of_mem_Q0
    {r : Q3} (hr : r ∈ Q0) :
    r * t13 = t13 * r := by
  have h1 : r * t0 = t0 * r := mul_comm_t0_of_mem_L0 (Q0_le_L0 hr)
  have h2 : (g0⁻¹ * r * g0) * t0 = t0 * (g0⁻¹ * r * g0) :=
    mul_comm_t0_of_mem_L0 (Q0_le_L0 (conj_g0_mem_Q0_iff.2 hr))
  have h3 : r * (t0 * t13) = (t0 * t13) * r := by
    rw [← g0_conj_t0]
    calc r * (g0 * t0 * g0⁻¹) = g0 * ((g0⁻¹ * r * g0) * t0) * g0⁻¹ := by group
      _ = g0 * (t0 * (g0⁻¹ * r * g0)) * g0⁻¹ := by rw [h2]
      _ = g0 * t0 * g0⁻¹ * r := by group
  have h4 : t0 * (r * t13) = t0 * (t13 * r) := by
    calc t0 * (r * t13) = (t0 * r) * t13 := (mul_assoc _ _ _).symm
      _ = (r * t0) * t13 := by rw [h1]
      _ = r * (t0 * t13) := mul_assoc _ _ _
      _ = (t0 * t13) * r := h3
      _ = t0 * (t13 * r) := mul_assoc _ _ _
  exact mul_left_cancel h4

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
