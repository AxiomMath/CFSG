module

public import CFSG.GH74.GLS.Stage2.Final.ModelFam
public import CFSG.GH74.GLS.Stage2.Final.ModelLayer
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerTransport

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm3.Sec7

variable {F : Type} [Field F]

theorem rhoQ_a_one_sq {a b : F} (h : a ^ 2 + b ^ 2 = -1) :
    rhoQ h (QuaternionGroup.a 1) * rhoQ h (QuaternionGroup.a 1) = (-1 : GL (Fin 2) F) := by
  rw [← map_mul]
  have h2 : (QuaternionGroup.a 1 : CFSG.GH74.Filter.ClassicalOdd.Q8) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by
    rw [QuaternionGroup.a_mul_a]
    rfl
  rw [h2]
  apply Units.ext
  show ((CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom h (QuaternionGroup.a 2) :
    Matrix (Fin 2) (Fin 2) F)) = _
  rw [CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom_a_two h]
  simp

theorem exists_typeMinus_in_E {M : ModelData F} [Finite F] (hG : GoodModel M) :
    ∃ x ∈ K1 M ⊔ K2 M, HasSqLift M x M.xK := by
  obtain ⟨a, b, hab, hH⟩ := hG.quat
  set A : GL (Fin 2) F := rhoQ hab (QuaternionGroup.a 1) with hA
  have hAH : A ∈ M.H2 := hH _
  have hA2 : A * A = (-1 : GL (Fin 2) F) := rhoQ_a_one_sq hab
  refine ⟨iota1 M ⟨A, hAH⟩ * iota2 M ⟨A, hAH⟩, ?_, ?_⟩
  · rw [mem_E_iff]
    exact ⟨⟨A, hAH⟩, ⟨A, hAH⟩, rfl⟩
  · show ∃ g : ↥M.K4, mkP M g = iota1 M ⟨A, hAH⟩ * iota2 M ⟨A, hAH⟩ ∧ g * g = M.xK
    refine ⟨⟨blkL F A, M.blkL_mem_K4 hAH⟩ * ⟨blkR F A, M.blkR_mem_K4 hAH⟩, ?_, ?_⟩
    · rw [map_mul]
      rfl
    · apply Subtype.ext
      show (blkL F A * blkR F A) * (blkL F A * blkR F A) = xGL F
      rw [← diagGL_eq_blkL_mul_blkR, diagGL_mul, hA2]
      rfl

theorem exists_Phi {K : Type} [Group K] [Finite K] [Finite F] {M : ModelData F} (hG : GoodModel M)
    (e : K ≃* PG M) (S' : Sylow 2 K) (z' : K) (hz : orderOf z' = 2) (hzS : z' ∈ (S' : Subgroup K))
    (hzc : ∀ x ∈ (S' : Subgroup K), x * z' = z' * x) : ∃ Φ : K ≃* PG M, Φ z' = yP M := by
  obtain ⟨a, b, hab, hH⟩ := hG.quat
  obtain ⟨S₁, hS₁⟩ := exists_sylow_center M hG.two_ne_zero hG.odd_index (rhoQ hab) hH
    (rhoQ_irr hab hG.two_ne_zero) (rhoQ_nc hab) isPGroup_q8q8
  obtain ⟨z₀, hz₀, hc₀⟩ := sylow_center_transport e S₁ (yP M) (orderOf_yP M hG.two_ne_zero)
    ((centerIs_iff _ _).1 hS₁) S'
  have hmem : z' ∈ (Subgroup.center ↥(S' : Subgroup K)).map (S' : Subgroup K).subtype := by
    refine ⟨⟨z', hzS⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext (hzc g g.2)
  rw [hc₀] at hmem
  have hzz : z' = z₀ := eq_of_mem_zpowers_of_orderOf_two hz₀ hz hmem
  have hc : (Subgroup.center ↥(S' : Subgroup K)).map (S' : Subgroup K).subtype = zpowers z' := by
    rw [hc₀, hzz]
  exact exists_equiv_of_center e S₁ (yP M) (orderOf_yP M hG.two_ne_zero)
    ((centerIs_iff _ _).1 hS₁) S' z' hz hc

theorem Ez_map_eq {K : Type} [Group K] [Finite K] [Finite F] {M : ModelData F} (hG : GoodModel M)
    (Φ : K ≃* PG M) (z : K) (hz : Φ z = yP M) :
    (IVK.Ez z).map Φ.toMonoidHom = K1 M ⊔ K2 M := by
  have h1 : IVK.Ez z = CFSG.GH74.GLS.layerTimesSylow z ⊥ := by
    unfold CFSG.GH74.GLS.layerTimesSylow IVK.Ez
    rw [sup_bot_eq]
  have h2 := ModelLT.layerTimesSylow_map Φ z ⊥
  rw [h1, h2, Subgroup.map_bot, hz]
  unfold CFSG.GH74.GLS.layerTimesSylow
  rw [sup_bot_eq]
  exact layer_map_eq M hG.two_ne_zero hG.qs


theorem supp_generic {K : Type} [Group K] [Finite K] [Finite F] {M : ModelData F}
    (hG : GoodModel M) (hZ : ZsTwo M) (e : K ≃* PG M) {q : ℕ} {z' : K} {S' : Sylow 2 K}
    {t' w' : K} {E₁ E₂ : Subgroup K} (hz : orderOf z' = 2) (hzS : z' ∈ (S' : Subgroup K))
    (hzc : ∀ x ∈ (S' : Subgroup K), x * z' = z' * x)
    (hD : Dat410 q z' (S' : Subgroup K) t' w' E₁ E₂) (hw : w' ≠ 1) :
    ¬ IsConj z' (t' * w' * z') := by
  obtain ⟨Φ, hΦ⟩ := exists_Phi hG e S' z' hz hzS hzc
  have h2 := hG.two_ne_zero
  have hxK1 : M.xK ≠ 1 := by
    intro h
    have := M.orderOf_xK h2
    rw [h, orderOf_one] at this
    omega
  have hzy : HasSqLift M (yP M) 1 := ⟨M.yK, rfl, M.yK_mul_self⟩
  have h1c : (1 : ↥M.K4) ∈ Subgroup.center ↥M.K4 := Subgroup.one_mem _
  have hxc : M.xK ∈ Subgroup.center ↥M.K4 := M.xK_mem_center
  have hconj : ∀ x : K, IsConj z' x → HasSqLift M (Φ x) 1 := fun x hx => by
    refine HasSqLift.conj h1c hzy ?_
    rw [← hΦ]
    exact MonoidHom.map_isConj Φ.toMonoidHom hx
  have hw2 : orderOf w' = 2 := hD.w_ord.resolve_left hw
  have hwS : w' ∈ (S' : Subgroup K) := hD.w_mem
  have hztw : IsConj z' (t' * w') := (hD.w_fus hw).1
  have hwz : w' * z' = z' * w' := hzc w' hwS
  have hzEz : z' ∈ IVK.Ez z' := by
    rw [hD.Ez_eq]
    have : z' ∈ E₁ ⊓ E₂ := by
      rw [hD.inter_E]
      exact Subgroup.mem_zpowers z'
    exact Subgroup.mem_sup_left this.1
  have hw_conj : IsConj z' w' := by
    have := (hD.w_fus hw).2 1 (Subgroup.mem_inf.2 ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩)
      (by rw [one_mul]; exact hw2)
    simpa using this
  have hz2 : z' * z' = 1 := by
    rw [← pow_two]
    exact hz ▸ pow_orderOf_eq_one z'
  have hw2' : w' * w' = 1 := by
    rw [← pow_two]
    exact hw2 ▸ pow_orderOf_eq_one w'
  have hsq : (z' * w') * (z' * w') = 1 := by
    calc z' * w' * (z' * w') = z' * (w' * z') * w' := by group
      _ = z' * (z' * w') * w' := by rw [hwz]
      _ = (z' * z') * (w' * w') := by group
      _ = 1 := by rw [hz2, hw2', one_mul]
  have hne : z' * w' ≠ 1 := by
    intro h
    have hw_eq : w' = z' := by
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_eq_of_mul_eq_one_right hz2
    have hmem : w' ∈ IVK.Ez z' ⊓ (zpowers t' ⊔ zpowers w') :=
      Subgroup.mem_inf.2 ⟨hw_eq ▸ hzEz, Subgroup.mem_sup_right (Subgroup.mem_zpowers w')⟩
    rw [hD.inter] at hmem
    exact hw (Subgroup.mem_bot.1 hmem)
  have hzw_ord : orderOf (z' * w') = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
  have hzw_conj : IsConj z' (z' * w') :=
    (hD.w_fus hw).2 z' (Subgroup.mem_inf.2 ⟨hzS, hzEz⟩) hzw_ord
  obtain ⟨x₀, hx₀E, hx₀⟩ := exists_typeMinus_in_E hG
  rw [← Ez_map_eq hG Φ z' hΦ] at hx₀E
  obtain ⟨y, hyE, hyx⟩ := Subgroup.mem_map.1 hx₀E
  have hΦy : Φ y = x₀ := hyx
  have hx₀sq : x₀ * x₀ = 1 := by
    obtain ⟨g, hg, hgs⟩ := hx₀
    rw [← hg, ← map_mul, hgs]
    exact (QuotientGroup.eq_one_iff _).2 (xK_mem_Zs M)
  have hx₀ne : x₀ ≠ 1 := by
    intro h
    have h' : HasSqLift M 1 1 := ⟨1, map_one _, one_mul 1⟩
    rw [h] at hx₀
    exact hxK1 (HasSqLift.unique hZ hx₀ h')
  have hx₀ord : orderOf x₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx₀sq) hx₀ne
  have hyord : orderOf y = 2 := by
    rw [← MulEquiv.orderOf_eq Φ y, hΦy]
    exact hx₀ord
  have hyz : y ≠ z' := by
    intro h
    rw [h, hΦ] at hΦy
    rw [← hΦy] at hx₀
    exact hxK1 (HasSqLift.unique hZ hx₀ hzy)
  have hfus : IsConj (t' * z') y := hD.E_fus y hyE hyord hyz
  have htz : HasSqLift M (Φ (t' * z')) M.xK :=
    HasSqLift.conj hxc (hΦy ▸ hx₀) (MonoidHom.map_isConj Φ.toMonoidHom hfus).symm
  have ht' : HasSqLift M (Φ t') 1 := hconj t' hD.t_conj
  have hw' : HasSqLift M (Φ w') 1 := hconj w' hw_conj
  have hz' : HasSqLift M (Φ z') 1 := by rw [hΦ]; exact hzy
  have htw : HasSqLift M (Φ t' * Φ w') 1 := by rw [← map_mul]; exact hconj _ hztw
  have hzw : HasSqLift M (Φ z' * Φ w') 1 := by rw [← map_mul]; exact hconj _ hzw_conj
  have htz' : HasSqLift M (Φ t' * Φ z') M.xK := by rw [← map_mul]; exact htz
  have hprod := hasSqLift_mul3 hZ ht' hw' hz' htw hzw htz'
  intro hc
  have hfin : HasSqLift M (Φ t' * Φ w' * Φ z') 1 := by
    rw [← map_mul, ← map_mul]
    exact hconj _ hc
  exact hxK1 (HasSqLift.unique hZ hprod hfin)

end CFSG.GH74.GLS.Stage2.Final.ModelBlock

namespace CFSG.GH74.GLS.Stage2.Final

open CFSG.GH74.GLS.Stage2.Final.ModelBlock

theorem ivk_4_10_supp : Stage1.Thm3.Sec7.IVK_4_10_supp := by
  intro K _ _ q hq h5 hK z' S' t' w' E₁ E₂ hz hzc hzS hD hw
  rcases cases_IsSp4L4U4 hq h5 hK with ⟨F, iF, fF, -, hG, hZ, ⟨e⟩⟩ |
      ⟨F, iF, fF, -, -, hG, hZ, ⟨e⟩⟩ | ⟨F, iF, fF, p, f, hfp, hcp, hF, -, -, hG, hZ, ⟨e⟩⟩
  · exact supp_generic hG hZ e hz hzS hzc hD hw
  · exact supp_generic hG hZ e hz hzS hzc hD hw
  · exact supp_generic hG hZ e hz hzS hzc hD hw

end CFSG.GH74.GLS.Stage2.Final
