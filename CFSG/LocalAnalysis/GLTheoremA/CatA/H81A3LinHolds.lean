module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81ChoiceTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinTorus
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinType
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinBlock

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  LinA3

private theorem map_map_symm {A B : Type*} [Group A] [Group B] (e : A ≃* B) (P : Subgroup A) :
    (P.map e.toMonoidHom).map e.symm.toMonoidHom = P := by
  ext x
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

private theorem h81Choice_torus {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {μ : F} (hμ : IsPrimitiveRoot μ p) (hF : 4 ≤ Nat.card F)
    {JType : Subgroup (projectiveSL 4 F) → Prop} (hJT : JType (JH F))
    {P : Subgroup (projectiveSL 4 F)}
    (hP : ∀ (d : Fin 4 → F) (hd : ∏ i, d i = 1), (∀ i, d i ^ p = 1) → proj 4 F (diagSL d hd) ∈ P) :
    H81Choice p P JType := by
  have hμ0 := ne_zero_of_root hp hp2 hμ
  refine ⟨proj 4 F (ySL hμ0), hP _ _ (yd_pow hp hp2 hμ), ?_, JH F,
    glaPComponent_centralizer_proj_ySL hp hp2 hμ hF,
    fun K hK => eq_of_glaPComponent_centralizer_proj_ySL hp hp2 hμ hF hK, hJT,
    ⟨proj 4 F (zSL hμ0), hP _ _ (zd_pow hp hp2 hμ), proj_zSL_not_mem_zpowers hp hp2 hμ,
      glaPLayer_JH_inf_centralizer_ne_bot hp hp2 hμ hF⟩,
    fun α hα hc => aut_eq_conj_ySL_zpow hp hp2 hμ hF α hα hc⟩
  intro h1
  have hk : ySL hμ0 ∈ scalars 4 F := by
    rw [← ker_proj]
    exact h1
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hk
  have h0 := congrFun (congrFun hc 0) 0
  have h1' := congrFun (congrFun hc 1) 1
  simp only [ySL, coe_diagSL, Matrix.diagonal_apply_eq, Matrix.scalar_apply] at h0 h1'
  exact yd_zero_ne hp hp2 hμ 1 (by decide) (h0.trans h1'.symm)

theorem h81FactA3_holds : H81FactA3 := by
  intro p Q hp hp2 hQ2 hdiv H _ _ hcat P hPel hPcard
  classical
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  change d = .A 3 Q at hi
  subst hi
  set F := GaloisField Q.p Q.exponent
  let e : H ≃* projectiveSL 4 F := e₀.trans
    ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 Q hv).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        4 F))
  have hcardF : Nat.card F = Q.card := by
    rw [GaloisField.card Q.p Q.exponent Q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hQ1 : 1 ≤ Q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ Q.prime_p.pos
  have hF : 4 ≤ Nat.card F := by
    have hpos : 0 < Q.card - 1 := by
      have h2 : 2 ≤ Q.card := by
        rw [TauCeti.PrimePower.card_def]
        exact Q.prime_p.two_le.trans (Nat.le_self_pow Q.exponent_pos.ne' _)
      omega
    have hle := Nat.le_of_dvd hpos hdiv
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    omega
  have : Fintype F := Fintype.ofFinite F
  have : Fintype Fˣ := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := Fˣ) p (by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, hcardF]
    exact hdiv)
  have hμ : IsPrimitiveRoot (x : F) p := by
    rw [← hx]
    exact IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.orderOf x)
  have hP'el : IsElemAbelian p (P.map e.toMonoidHom) :=
    (CFSG.LocalAnalysis.GLTheoremA.T123C.isElemAbelian_map_iff e.injective p P).2 hPel
  have hP'card : Nat.card (P.map e.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hPcard]
  obtain ⟨g, hg⟩ := exists_conjAut_diagSL_mem hp hp2 ⟨(x : F), hμ⟩ hP'el hP'card
  set c := conjAut 4 F g with hc
  have hch := h81Choice_torus hp hp2 hμ hF
    (isSL3Type_JH Q hQ2 hp hp2 hμ hF) (P := (P.map e.toMonoidHom).map c.toMonoidHom) hg
  have h1 := h81Choice_map_mulEquiv hp c.symm (fun J hJ => isSL3Type_map_mulEquiv c.symm hJ) hch
  rw [map_map_symm] at h1
  have h2 := h81Choice_map_mulEquiv hp e.symm (fun J hJ => isSL3Type_map_mulEquiv e.symm hJ) h1
  rwa [map_map_symm] at h2

end CFSG.LocalAnalysis.GLTheoremA.H81
