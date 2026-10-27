module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk411Model
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk411Transport
public import CFSG.GH74.GLS.Stage2.Final.ModelLUFam
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CFD411

public section

namespace CFSG.GH74.Ivk411

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.L5U5
open CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT (Data411 Data411Clauses)

variable {F : Type} [Field F]

theorem exists_S1 [Finite F] {M : ModelData F} (hG : GoodModel M) :
    ∃ S : Sylow 2 (PG M), CenterIs (S : Subgroup (PG M)) (yP M) := by
  obtain ⟨a, b, hab, hH⟩ := hG.quat
  obtain ⟨S, hS⟩ := exists_sylow_center M hG.two_ne_zero hG.odd_index (rhoQ hab) hH
    (rhoQ_irr hab hG.two_ne_zero) (rhoQ_nc hab) isPGroup_q8q8
  exact ⟨S, (centerIs_iff _ _).1 hS⟩

theorem data411_of_equiv {K : Type} [Group K] [Finite K] [Finite F] {M : ModelData F}
    (hG : GoodModel M) {q n : ℕ} (hSL : HasSL2Model ↥M.H2 (fun r => r = q))
    (hU2 : ∀ l : Fˣ, sc2 l ∈ M.U2 ↔ l ^ n = 1)
    (hdetn : ∀ a ∈ M.U2, ((a : Matrix (Fin 2) (Fin 2) F).det) ^ n = 1)
    (e : K ≃* PG M) (z : K) (hz : IsCentralInvolution z) :
    ∃ I₁ I₂ : Subgroup K, Data411 z q I₁ I₂ := by
  obtain ⟨hzo, S, hzS, hzc⟩ := hz
  obtain ⟨S₁, hS₁⟩ := exists_S1 hG
  obtain ⟨Φ, hΦ⟩ := exists_equiv_sylow e S₁ S
  have hcen : CenterIs (S : Subgroup K) (Φ.symm (yP M)) := by
    have h1 := hS₁.map_equiv Φ.symm
    have h2 : (S₁ : Subgroup (PG M)).map Φ.symm.toMonoidHom = (S : Subgroup K) := by
      rw [← hΦ]
      exact ModelLUT.map_symm_map Φ _
    rwa [h2] at h1
  have hzmem : z ∈ Subgroup.zpowers (Φ.symm (yP M)) := (hcen z).1 ⟨hzS, hzc⟩
  have hord : orderOf (Φ.symm (yP M)) = 2 := by
    rw [MulEquiv.orderOf_eq]; exact orderOf_yP M hG.two_ne_zero
  have hzy : z = Φ.symm (yP M) := eq_of_mem_zpowers_of_orderOf_two hord hzo hzmem
  have hd := data411_map_equiv Φ.symm (data411_PG hG hSL hU2 hdetn)
  rw [← hzy] at hd
  exact ⟨_, _, hd⟩


theorem data411Clauses_proved : Data411Clauses := by
  intro K _ _ ε q hε hodd hq3 h8 hK z hz
  have h5 : 5 ≤ q := by obtain ⟨k, hk⟩ := hodd; omega
  rcases hK with ⟨hε1, F, iF, fF, hF, ⟨e⟩⟩ | ⟨hε1, F, iF, fF, hF, ⟨e⟩⟩
  · have h2 : (2 : F) ≠ 0 := ModelBlock.two_ne_zero_of_odd_card (by rw [hF]; exact hodd)
    have h5' : 5 ≤ Nat.card F := by rw [hF]; exact h5
    have hG := goodModel_lin h2 h5'
    have hSL : HasSL2Model ↥(ModelData.lin F).H2 (fun r => r = q) := by
      have := hasSL2Model_H2_lin F
      rwa [hF] at this
    exact data411_of_equiv hG hSL (n := Nat.card F - 1)
      (fun l => ⟨fun _ => by
        have h := pow_card_eq_one' (G := Fˣ) (x := l)
        rwa [Nat.card_units] at h, fun _ => Subgroup.mem_top _⟩)
      (fun a _ => det_lin_pow a) (show K ≃* PG (ModelData.lin F) from e) z hz
  · obtain ⟨p, f, hfp, hcp, hqf⟩ := exists_uni_params hF
    subst hqf
    have hp2 : p ≠ 2 := by
      rintro rfl
      rcases Nat.eq_zero_or_pos f with rfl | hf
      · simp at h5
      · have : 2 ∣ 2 ^ f := dvd_pow_self 2 hf.ne'
        obtain ⟨k, hk⟩ := hodd
        omega
    have hG := goodModel_uni hF hp2 h5
    exact data411_of_equiv hG (hasSL2Model_H2_uni hF) (n := p ^ f + 1) (sc2_mem_uni_iff hF)
      (fun a ha => det_uni_pow hF ha) (show K ≃* PG (ModelData.uni hF) from e) z hz

end CFSG.GH74.Ivk411
