module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenBase
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldSemi
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftGen

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen

open Matrix CFSG CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField

variable {k : Type} [Field k]

theorem exists_pow_three_scalar {e : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)}
    {M : GL (Fin 3) k} (hM : IsConjBy e M) (he3 : e ^ 3 = 1) :
    ∃ c : kˣ, (M : Matrix (Fin 3) (Fin 3) k) ^ 3 = (c : k) • (1 : Matrix (Fin 3) (Fin 3) k) := by
  obtain ⟨c, hc⟩ := eq_scalar_of_forall_commute (M ^ 3) (fun t => by
    have h3 := (hM.pow 3) t
    have h4 : (e ^ 3) t = t := by rw [he3]; rfl
    rw [h4] at h3
    exact comm_of_conj_eq h3)
  exact ⟨c, by rw [← Units.val_pow_eq_pow_val]; exact hc⟩

theorem exists_commutation_scalar {e f : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)}
    {s : Matrix.SpecialLinearGroup (Fin 3) k} {g : GL (Fin 3) k}
    (hs : IsConjBy e (Matrix.SpecialLinearGroup.toGL s)) (hg : IsConjBy f g)
    (hef : e * f = f * e) :
    ∃ w : kˣ, (w : k) ^ 3 = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) *
        ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
          (w : k) • (s : Matrix (Fin 3) (Fin 3) k) := by
  have h1 := hs.mul hg
  have h2 := hg.mul hs
  rw [hef] at h1
  obtain ⟨c, hc⟩ := exists_scalar_of_conj_eq_aux (Matrix.SpecialLinearGroup.toGL s * g)
    (g * Matrix.SpecialLinearGroup.toGL s) (fun t => by
      apply Units.ext
      simp only [Units.val_mul]
      exact (h1 t).symm.trans (h2 t))
  have hc' := congrArg Units.val hc
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_mul_diagonal] at hc'
  have hmat : (g : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) *
      ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        (c : k) • (s : Matrix (Fin 3) (Fin 3) k) := by
    have e1 : (g : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) =
        (c : k) • ((s : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k)) := hc'
    rw [e1, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  refine ⟨c, ?_, hmat⟩
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_units_conj, Matrix.det_smul] at hdet
  have h1' : (s : Matrix (Fin 3) (Fin 3) k).det = 1 := s.det_coe
  rw [h1'] at hdet
  simpa using hdet.symm

theorem closure_fixSet_eq_top_of_conj [Finite k] (h3 : 3 ∣ Nat.card k - 1)
    (E : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) k))) (hEab : Open.IsElemAbelian 3 E)
    (hEcard : Nat.card E = 9) (hFix : FixCube E)
    (hconj : ∀ e ∈ E, ∃ g : GL (Fin 3) k, IsConjBy e g) :
    Subgroup.closure (fixSet E) = ⊤ := by
  classical
  have hfinE : Finite E := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨a, hakernot, s, hs⟩ := exists_inner_of_index (E.subtype) (fun a => hconj a a.2)
    (by
      have : Nat.card (E.subtype : E →* MulAut (Matrix.SpecialLinearGroup (Fin 3) k)).ker = 1 := by
        rw [Subgroup.ker_subtype, Subgroup.card_bot]
      omega)
  set e₁ : MulAut (Matrix.SpecialLinearGroup (Fin 3) k) :=
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 3) k)) with he₁
  have he₁E : e₁ ∈ E := a.2
  have he₁1 : e₁ ≠ 1 := fun h => hakernot (by
    rw [MonoidHom.mem_ker]
    exact h)
  have hs' : ∀ t, e₁ t = s * t * s⁻¹ := hs
  have he₁conj : e₁ = MulAut.conj s := MulEquiv.ext fun t => by
    rw [MulAut.conj_apply]
    exact hs' t
  have hsG : IsConjBy e₁ (Matrix.SpecialLinearGroup.toGL s) := by
    intro t
    rw [hs' t, ← map_inv]
    rfl
  obtain ⟨e₂, he₂E, he₂not⟩ := exists_mem_not_mem_zpowers hEab hEcard he₁E
  obtain ⟨g₂, hg₂⟩ := hconj e₂ he₂E
  have he₂3 : e₂ ^ 3 = 1 := hEab.2 e₂ he₂E
  have he₁3 : e₁ ^ 3 = 1 := hEab.2 e₁ he₁E
  have hcomm : e₁ * e₂ = e₂ * e₁ := congrArg Subtype.val (hEab.1.is_comm.comm ⟨e₁, he₁E⟩ ⟨e₂, he₂E⟩)
  obtain ⟨w, hw3, hmat⟩ := exists_commutation_scalar hsG hg₂ hcomm
  have hw1 : (w : k) = 1 := by
    by_contra hw1
    have hs3 : (s : Matrix (Fin 3) (Fin 3) k) ^ 3 = 1 :=
      cube_eq_one_of_conj_eq_smul s g₂ hw3 hw1 hmat
    have hs3' : s ^ 3 = 1 := Subtype.ext (by simpa using hs3)
    have hfix := hFix e₂ he₂E s hs3' (he₁conj ▸ he₁E)
    have h1 : ((e₂ s : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        (s : Matrix (Fin 3) (Fin 3) k) := congrArg Subtype.val hfix
    have h2 := hg₂ s
    rw [h1] at h2
    rw [hmat] at h2
    have h3' : ((w : k) - 1) • (s : Matrix (Fin 3) (Fin 3) k) = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero.2 h2.symm
    have hs0 := (smul_eq_zero.1 h3').resolve_left (sub_ne_zero.2 hw1)
    have hdet : (s : Matrix (Fin 3) (Fin 3) k).det = 1 := s.det_coe
    rw [hs0] at hdet
    simp at hdet
  rw [hw1, one_smul] at hmat
  set sG : GL (Fin 3) k := Matrix.SpecialLinearGroup.toGL s with hsGdef
  have hsg : (sG : Matrix (Fin 3) (Fin 3) k) * (g₂ : Matrix (Fin 3) (Fin 3) k) =
      (g₂ : Matrix (Fin 3) (Fin 3) k) * (sG : Matrix (Fin 3) (Fin 3) k) := by
    have h1 : (g₂ : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) =
        (s : Matrix (Fin 3) (Fin 3) k) * (g₂ : Matrix (Fin 3) (Fin 3) k) := by
      calc (g₂ : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k)
          = ((g₂ : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) *
            ((g₂⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) *
              (g₂ : Matrix (Fin 3) (Fin 3) k) := by
            rw [Matrix.mul_assoc _ _ (g₂ : Matrix (Fin 3) (Fin 3) k), Units.inv_mul, Matrix.mul_one]
        _ = (s : Matrix (Fin 3) (Fin 3) k) * (g₂ : Matrix (Fin 3) (Fin 3) k) := by rw [hmat]
    exact h1.symm
  have hdet : (sG : Matrix (Fin 3) (Fin 3) k).det = 1 := s.det_coe
  have hns : ∀ c : k, (sG : Matrix (Fin 3) (Fin 3) k) ≠ c • (1 : Matrix (Fin 3) (Fin 3) k) := by
    intro c hc
    apply he₁1
    ext1 t
    apply Subtype.ext
    rw [hsG t]
    apply conj_eq_self_of_comm
    rw [hc]
    simp
  obtain ⟨c₀, hc₀⟩ := exists_pow_three_scalar hsG he₁3
  obtain ⟨c₂, hc₂⟩ := exists_pow_three_scalar hg₂ he₂3
  obtain ⟨ωu, hωu⟩ : ∃ ω : kˣ, orderOf ω = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply exists_prime_orderOf_dvd_card' 3
    rw [Nat.card_units]
    exact h3
  have hω3 : (ωu : k) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ωu
    rw [hωu] at this
    simpa [← Units.val_pow_eq_pow_val] using congrArg Units.val this
  have hω1 : (ωu : k) ≠ 1 := by
    intro h
    have : ωu = 1 := Units.ext h
    rw [this, orderOf_one] at hωu
    omega
  obtain ⟨P, u, v, hu, hv⟩ := exists_common_frame hω3 hω1 sG g₂ hsg hdet hc₀ hc₂ hns
  have hu3 := diag_cube_of_conj P sG u _ hc₀ hu
  have hv3 := diag_cube_of_conj P g₂ v _ hc₂ hv
  have hT := closure_fixed_eq_top P sG g₂ u v hu hv
    (fun a b => (hu3 a).trans (hu3 b).symm) (fun a b => (hv3 a).trans (hv3 b).symm)
  have he₂1 : e₂ ≠ 1 := fun h => he₂not (h ▸ one_mem _)
  obtain ⟨hne1, hne2⟩ := mul_ne_one_of_not_mem_zpowers (a := e₁) he₂3 he₂not
  rw [eq_top_iff, ← hT]
  refine Subgroup.closure_mono ?_
  rintro x ⟨M, hM, hMx⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · exact ⟨e₁, he₁E, he₁1, hsG.fix hMx⟩
  · exact ⟨e₂, he₂E, he₂1, hg₂.fix hMx⟩
  · exact ⟨e₁ * e₂, E.mul_mem he₁E he₂E, hne1, (hsG.mul hg₂).fix hMx⟩
  · exact ⟨e₁ * e₂ ^ 2, E.mul_mem he₁E (E.pow_mem he₂E 2), hne2, (hsG.mul (hg₂.pow 2)).fix hMx⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen
