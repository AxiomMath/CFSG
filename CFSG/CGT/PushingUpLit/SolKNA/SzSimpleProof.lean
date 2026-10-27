module

public import CFSG.CGT.PushingUpLit.SolKNA.SzSimple
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleFpf
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleTransport

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit CFSG.Blueprint Matrix
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.B45Sz

theorem szFpfSimpleNatural_of_certificate : SzFpfSimpleNatural := by
  classical
  intro a ha V _ _ _ ρ hfpf hnt hirr
  have : Fintype (F a) := Fintype.ofFinite _
  have hK : Nat.card (F a) = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  let π : ↥(suzukiGroup a (F a)) →* (V ≃ₗ[ZMod 2] V) :=
    repToHom (ρ.comp (szEquiv a).toMonoidHom)
  have hπ : ∀ (h : ↥(suzukiGroup a (F a))) (w : V), π h w = ρ (szEquiv a h) w :=
    fun _ _ => rfl
  have : Fact (repOfG π).IsIrreducible := ⟨isIrreducible_repToHom_comp ρ hnt hirr⟩
  obtain ⟨g, hg5, hgfix⟩ := hfpf
  have hz : orderOf ((szEquiv a).symm g) = 5 := by
    rw [MulEquiv.orderOf_eq]
    exact hg5
  have hzfpf : ∀ w, repOfG π ((szEquiv a).symm g) w = w → w = 0 := fun w hw =>
    hgfix w (by simpa [repOfG_repToHom, π] using hw)
  have hntπ : ∃ g', repOfG π g' ≠ 1 := by
    refine ⟨(szEquiv a).symm g, fun h1 => ?_⟩
    obtain ⟨x, y, hxy⟩ := hnt
    have hall : ∀ w : V, w = 0 := fun w => hzfpf w (by rw [h1]; rfl)
    exact hxy ((hall x).trans (hall y).symm)
  have hdim := finrank_eq_four_of_fpf hK π hntπ hz hzfpf
  obtain ⟨c, φ, hφ⟩ := sz_exists_natural_of_four hK π hntπ hdim
  let σ : F a ≃+* F a := iterateFrobeniusEquiv (F a) 2 c
  let φ' : V ≃+ (Fin 4 → F a) := φ.trans (AddEquiv.piCongrRight fun _ : Fin 4 => σ.symm.toAddEquiv)
  have hφ' : ∀ (h : ↥(suzukiGroup a (F a))) (w : V),
      φ' (π h w) = (glMat (h : GL (Fin 4) (F a))).mulVec (φ' w) := by
    intro h w
    funext j
    have h1 := congrFun (hφ h w) j
    show σ.symm (φ (π h w) j) = _
    rw [h1, Matrix.mulVec, dotProduct, map_sum, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [map_mul, Matrix.map_apply]
    have hσ : σ.symm ((glMat (h : GL (Fin 4) (F a))) j c' ^ 2 ^ c) =
        (glMat (h : GL (Fin 4) (F a))) j c' := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    rw [hσ]
    rfl
  let J := CFSG.LinearAlgebra.exteriorSquareJ (F a)
  have hJJ : J * J = 1 := exteriorSquareJ_mul_self (F a)
  let θ : (Fin 4 → F a) →+ V :=
    { toFun := fun v => φ'.symm (J *ᵥ v)
      map_zero' := by simp
      map_add' := fun x y => by simp [Matrix.mulVec_add] }
  refine ⟨θ, ?_, ?_⟩
  · have hJi : Function.Involutive (fun v : Fin 4 → F a => J *ᵥ v) := fun v => by
      simp [Matrix.mulVec_mulVec, hJJ]
    exact φ'.symm.bijective.comp hJi.bijective
  · intro g' v
    obtain ⟨h, rfl⟩ := (szEquiv a).surjective g'
    have hGJ := szEquiv_mul_J a h
    have hJG : J * (((szEquiv a h : ↥(Sz a)) : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) =
        glMat (h : GL (Fin 4) (F a)) * J := by
      calc J * (((szEquiv a h : ↥(Sz a)) : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a))
          = J * (((szEquiv a h : ↥(Sz a)) : GL (Fin 4) (F a)) :
              Matrix (Fin 4) (Fin 4) (F a)) * (J * J) := by rw [hJJ, Matrix.mul_one]
        _ = J * ((((szEquiv a h : ↥(Sz a)) : GL (Fin 4) (F a)) :
              Matrix (Fin 4) (Fin 4) (F a)) * J) * J := by simp only [Matrix.mul_assoc]
        _ = J * (J * glMat (h : GL (Fin 4) (F a))) * J := by rw [hGJ]
        _ = (J * J) * glMat (h : GL (Fin 4) (F a)) * J := by simp only [Matrix.mul_assoc]
        _ = glMat (h : GL (Fin 4) (F a)) * J := by rw [hJJ, Matrix.one_mul]
    show φ'.symm (J *ᵥ ((((szEquiv a h : ↥(Sz a)) : GL (Fin 4) (F a)) :
      Matrix (Fin 4) (Fin 4) (F a)) *ᵥ v)) = ρ (szEquiv a h) (φ'.symm (J *ᵥ v))
    rw [Matrix.mulVec_mulVec, hJG, ← Matrix.mulVec_mulVec]
    have h2 := hφ' h (φ'.symm (J *ᵥ v))
    rw [AddEquiv.apply_symm_apply] at h2
    rw [← h2, AddEquiv.symm_apply_apply]
    rfl

end CFSG.CGT.PushingUpLit.SolKNA
