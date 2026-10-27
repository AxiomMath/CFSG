module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3S197Lift
public import CFSG.HardMathSupport.Solomon.Coordinator.L3S197Alg

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance

section Het

variable {π : Bool} {p f : ℕ} {F : Type} [Field F]

theorem congr_conj_eq {A B : Type*} [Group A] [Group B] (e : A ≃* B) (x : A) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

@[expose] noncomputable def psiG (_hF : PiField π p f F) {M : Type*} [Group M]
    (η : (↥(slPi π 3 (p ^ f) F) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) F)) ≃* M) :
    MulAut ↥(slPi π 3 (p ^ f) F) →* MulAut M :=
  (MulAut.congr η).toMonoidHom.comp (centerDescend _)

theorem psiG_injective (hF : PiField π p f F) (hq2 : π = false → 2 < p ^ f) {M : Type*} [Group M]
    (η : (↥(slPi π 3 (p ^ f) F) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) F)) ≃* M) :
    Function.Injective (psiG hF η) := by
  have hGq : CFSG.Open.IsQuasisimple ↥(slPi π 3 (p ^ f) F) :=
    isQuasisimple_slPi hF (fun hf => by have := hq2 hf; omega)
  rw [injective_iff_map_eq_one]
  intro α hα
  apply eq_one_of_centerDescend_eq_one hGq
  exact (MulAut.congr η).injective (by
    have : MulAut.congr η (centerDescend _ α) = 1 := hα
    rw [this, map_one])

theorem lam_eq_psiG_cj (hF : PiField π p f F) {M : Type*} [Group M]
    (η : (↥(slPi π 3 (p ^ f) F) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) F)) ≃* M)
    (g : ↥(glPi π 3 (p ^ f) F)) : lam hF η g = psiG hF η (cj hF g.2) := rfl

theorem cj_slPi (hF : PiField π p f F) (x : ↥(slPi π 3 (p ^ f) F)) :
    cj hF (slPi_le_glPi (fun h => by subst h; exact hF.unitary) x.2) = MulAut.conj x := by
  refine MulEquiv.ext fun s => Subtype.ext ?_
  show (x : GL (Fin 3) F) * s * (x : GL (Fin 3) F)⁻¹ = ((MulAut.conj x s : ↥(slPi π 3 (p ^ f) F)) :
    GL (Fin 3) F)
  simp [MulAut.conj_apply]

theorem het_G (hF : PiField π p f F) (hmod : ModThree π (p ^ f)) (hq2 : π = false → 2 < p ^ f)
    {M : Type*} [Group M]
    (η : (↥(slPi π 3 (p ^ f) F) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) F)) ≃* M)
    {DG : Subgroup (MulAut ↥(slPi π 3 (p ^ f) F))}
    (hD : CFSG.Open.IsElemAbelian 3 (DG.map (psiG hF η)))
    (hcard : Nat.card (DG.map (psiG hF η)) = 9)
    (hnc : ∃ a b : ↥(glPi π 3 (p ^ f) F), lam hF η a ∈ DG.map (psiG hF η) ∧
      lam hF η b ∈ DG.map (psiG hF η) ∧ a * b ≠ b * a)
    (x : ↥(slPi π 3 (p ^ f) F)) (hx : (MulAut.conj x : MulAut ↥(slPi π 3 (p ^ f) F)) ∈ DG)
    (hx1 : (MulAut.conj x : MulAut ↥(slPi π 3 (p ^ f) F)) ≠ 1) :
    ∃ v ∈ DG, ∃ b : ↥(glPi π 3 (p ^ f) F), v = cj hF b.2 ∧ v x ≠ x := by
  have hinj := psiG_injective hF hq2 η
  set xg : ↥(glPi π 3 (p ^ f) F) :=
    ⟨x, slPi_le_glPi (fun h => by subst h; exact hF.unitary) x.2⟩ with hxg
  have hlx : lam hF η xg = psiG hF η (MulAut.conj x) := by
    rw [lam_eq_psiG_cj]
    exact congrArg (psiG hF η) (cj_slPi hF x)
  obtain ⟨b, hb, hbx⟩ := het_star hF hmod hq2 η hD hcard hnc xg
    (by rw [hlx]; exact ⟨_, hx, rfl⟩)
    (by rw [hlx]; intro h; exact hx1 (hinj (by rw [h, map_one])))
  obtain ⟨v, hv, hvb⟩ := hb
  have hvcj : v = cj hF b.2 := hinj (by rw [hvb, lam_eq_psiG_cj])
  refine ⟨v, hv, b, hvcj, fun hvx => hbx ?_⟩
  rw [hvcj] at hvx
  have h1 := congrArg (fun s : ↥(slPi π 3 (p ^ f) F) => (s : GL (Fin 3) F)) hvx
  simp only [coe_cj] at h1
  apply Subtype.ext
  show (b : GL (Fin 3) F) * (x : GL (Fin 3) F) = (x : GL (Fin 3) F) * (b : GL (Fin 3) F)
  generalize (b : GL (Fin 3) F) = B at h1 ⊢
  generalize (x : GL (Fin 3) F) = X at h1 ⊢
  calc B * X = (B * X * B⁻¹) * B := by group
    _ = X * B := by rw [h1]

theorem cube_of_conj_central (hF : PiField π p f F) (hmod : ModThree π (p ^ f))
    (x : ↥(slPi π 3 (p ^ f) F)) (b : ↥(glPi π 3 (p ^ f) F))
    {z : ↥(slPi π 3 (p ^ f) F)} (hz : z ∈ Subgroup.center ↥(slPi π 3 (p ^ f) F)) (hz1 : z ≠ 1)
    (h : cj hF b.2 x = x * z) : x ^ 3 = 1 := by
  obtain ⟨ζ, hζ3, hζ⟩ := exists_scalar_of_mem_center hF hmod hz
  have hζ1 : (ζ : F) ≠ 1 := by
    intro h1
    have : ζ = 1 := Units.ext h1
    rw [this, map_one] at hζ
    exact hz1 (Subtype.ext hζ)
  have hζ3' : (ζ : F) ^ 3 = 1 := by
    have := congrArg Units.val hζ3
    simpa using this
  have h1 := congrArg (fun s : ↥(slPi π 3 (p ^ f) F) => (s : GL (Fin 3) F)) h
  simp only [coe_cj, Subgroup.coe_mul] at h1
  rw [hζ] at h1
  have hmat : ((b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)⁻¹ =
        (ζ : F) • ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have h2 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h1
    simp only [Units.val_mul, Matrix.coe_units_inv] at h2
    have hs : ((Matrix.GeneralLinearGroup.scalar (Fin 3) ζ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = (ζ : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [Matrix.GeneralLinearGroup.coe_scalar]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    rw [h2, hs, Matrix.mul_smul, Matrix.mul_one]
  have hdet : ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    ((mem_slPi_iff (fun h => by subst h; exact hF.unitary)).1 x.2).2
  have h3 := cube_eq_one_of_conj_smul (b : GL (Fin 3) F) hζ1 hζ3' hmat hdet
  apply Subtype.ext
  apply Units.ext
  simpa using h3

end Het

end CFSG.HardMathSupport.Solomon.Coordinator
