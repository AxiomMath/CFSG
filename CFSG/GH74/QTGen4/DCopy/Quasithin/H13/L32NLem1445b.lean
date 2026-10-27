module

public import CFSG.Quasithin.H13.L32NLem1445b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1444k

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setup5_F4
open Setup5
open CFSG.Quasithin.H13.L1444.Setup5_F4

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup5_F4 G T L V V₂ g D Q₁ Q₂)
include S

theorem isPGroup_cent_F4 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
  obtain ⟨_, S'⟩ := S.set14
  exact S'.isPGroup_cent_sup_F4

theorem le_normalizer_cent_F4 :
    L ⊔ T ≤ Subgroup.normalizer
      (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun x hx => ⟨(L ⊔ T).mul_mem ((L ⊔ T).mul_mem hg hx.1)
    ((L ⊔ T).inv_mem hg), Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  have hgv : g⁻¹ * v * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem (S.normV hg)) v).mp hv
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hgv
  calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [hc]
    _ = g * x * g⁻¹ * v := by group

theorem cent_le_T_F4 : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
  obtain ⟨_, S'⟩ := S.set14
  exact (le_pCoreOf_of_le_normalizer 2 inf_le_left S.le_normalizer_cent_F4 S.isPGroup_cent_F4).trans
    (pCoreOf_two_le_of_isSylowTwoOf
      (isSylowTwoOf_of_quasithinIsSylowTwo S'.hH.sylow le_sup_right))

theorem mem_V_of_mem_cent_F4 {c : G} (hc : c ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))
    (hcL : c ∈ L) : c ∈ V :=
  S.centL.le ⟨hcL, hc.2⟩

theorem comm_mem_V_of_cent_F4 {c : G} (hc : c ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))
    {l : G} (hl : l ∈ L) : l * c * l⁻¹ * c⁻¹ ∈ V := by
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := (sup_le Subgroup.le_normalizer S.TL) hc.1
  refine S.mem_V_of_mem_cent_F4 ?_ ?_
  · have h1 : l * c * l⁻¹ ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (S.le_normalizer_cent_F4 (Subgroup.mem_sup_left hl)) c).mp hc
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hc)
  · rw [show l * c * l⁻¹ * c⁻¹ = l * (c * l⁻¹ * c⁻¹) by group]
    exact L.mul_mem hl ((Subgroup.mem_normalizer_iff.mp hcN _).mp (L.inv_mem hl))

theorem mul_self_cent_F4 (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {c : G}
    (hc : c ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) : c * c = 1 := by
  have hc2 : c * c ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := Subgroup.mul_mem _ hc hc
  refine eq_one_of_comm_L hCTL (S.cent_le_T_F4 hc2) fun l hl => ?_
  have hv := S.comm_mem_V_of_cent_F4 hc hl
  set v := l * c * l⁻¹ * c⁻¹ with hvdef
  have hlc : l * c * l⁻¹ = v * c := by rw [hvdef]; group
  have hcv : c * v = v * c := (Subgroup.mem_centralizer_iff.mp hc.2 v hv).symm
  have hvv : v * v = 1 := by rw [← pow_two]; exact S.elem.2 v hv
  calc l * (c * c) * l⁻¹ = (l * c * l⁻¹) * (l * c * l⁻¹) := by group
    _ = v * c * (v * c) := by rw [hlc]
    _ = v * (c * v) * c := by group
    _ = v * (v * c) * c := by rw [hcv]
    _ = c * c := by rw [← mul_assoc, hvv, one_mul]

theorem comm_cent_F4 (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {c c' : G}
    (hc : c ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))
    (hc' : c' ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) : c * c' = c' * c := by
  set k := c * c' * c⁻¹ * c'⁻¹ with hk
  have hkC : k ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hc') (Subgroup.inv_mem _ hc))
      (Subgroup.inv_mem _ hc')
  have hk1 : k = 1 := by
    refine eq_one_of_comm_L hCTL (S.cent_le_T_F4 hkC) fun l hl => ?_
    have hv := S.comm_mem_V_of_cent_F4 hc hl
    have hv' := S.comm_mem_V_of_cent_F4 hc' hl
    set v := l * c * l⁻¹ * c⁻¹ with hvdef
    set v' := l * c' * l⁻¹ * c'⁻¹ with hv'def
    have hlc : l * c * l⁻¹ = v * c := by rw [hvdef]; group
    have hlc' : l * c' * l⁻¹ = v' * c' := by rw [hv'def]; group
    have hcomm : ∀ w ∈ V, ∀ x ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G), Commute w x :=
      fun w hw x hx => (Subgroup.mem_centralizer_iff.mp hx.2 w hw)
    calc l * k * l⁻¹ = (l * c * l⁻¹) * (l * c' * l⁻¹) * (l * c * l⁻¹)⁻¹ * (l * c' * l⁻¹)⁻¹ := by
          rw [hk]; group
      _ = (v * c) * (v' * c') * (v * c)⁻¹ * (v' * c')⁻¹ := by rw [hlc, hlc']
      _ = k := comm_mul_of_comm (hcomm v hv c hc) (hcomm v hv c' hc') (hcomm v' hv' c hc)
          (hcomm v' hv' c' hc') (S.comm_V hv hv')
  calc c * c' = k * (c' * c) := by rw [hk]; group
    _ = c' * c := by rw [hk1, one_mul]

theorem mem_Q_of_fix_F4 {x : G} (hxH : x ∈ l32nH T V) (hx₁ : ∀ q ∈ Q₁, x * q * x⁻¹ ∈ Q₁)
    (hx₂ : ∀ q ∈ Q₂, x * q * x⁻¹ ∈ Q₂) (hxV : x ∈ Subgroup.centralizer (V : Set G)) :
    x ∈ pCoreOf 2 (l32nH T V) := by
  have hxN := L14332.l32nH_le_normalizer_fsuU T V hxH
  rw [← S.cHat]
  refine (L14332.rho_eq_one_iff_mem (D := D) hxH hxN).mp (LinearEquiv.ext fun w => ?_)
  exact eq_of_trivial_on S.hat_V_sup_Q₁ (by rw [sup_comm]; exact S.hat_V_sup_Q₂)
    (by rw [inf_comm]; exact S.hat_Q_inf) (D.ρ ⟨x, hxN⟩).toLinearMap
    (fun _ hw => Setup3.rho_mem_hat hxN hx₁ hw) (fun _ hw => Setup3.rho_mem_hat hxN hx₂ hw)
    (fun _ hw => rho_fix_hat_V hxN hxV hw) w

theorem swap_of_cent_F4 {c : G} (hc : c ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))
    (hcV : c ∉ V) :
    (Q₁.map (MulAut.conj c).toMonoidHom = Q₂ ∧ Q₂.map (MulAut.conj c).toMonoidHom = Q₁) := by
  have hcH : c ∈ l32nH T V := S.TH (S.cent_le_T_F4 hc)
  have hcU : ∀ q ∈ Q₁ ⊔ Q₂, c * q * c⁻¹ ∈ Q₁ ⊔ Q₂ := fun q hq => by
    rw [S.sup] at hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp (L14332.l32nH_le_normalizer_fsuU T V hcH) q).mp hq
  rcases S.cfg.map_conj_cases hcU with ⟨h1, h2⟩ | h
  · exfalso
    apply hcV
    have hQ := S.mem_Q_of_fix_F4 hcH
      (fun q hq => by rw [← h1]; exact ⟨q, hq, by simp⟩)
      (fun q hq => by rw [← h2]; exact ⟨q, hq, by simp⟩) hc.2
    rw [← S.QU] at hQ
    exact S.mem_V_of_mem_cent_F4 hc (S.U_le_L hQ)
  · exact h

theorem inv_mul_mem_V_F4 {c c' : G} (hc : c ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))
    (hc' : c' ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (hcV : c ∉ V) (hc'V : c' ∉ V) :
    c⁻¹ * c' ∈ V := by
  obtain ⟨h1, h2⟩ := S.swap_of_cent_F4 hc hcV
  obtain ⟨h1', h2'⟩ := S.swap_of_cent_F4 hc' hc'V
  have hx : c⁻¹ * c' ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hc'
  have hxH : c⁻¹ * c' ∈ l32nH T V := S.TH (S.cent_le_T_F4 hx)

  have hmap : ∀ {A B : Subgroup G} {x : G}, A.map (MulAut.conj x).toMonoidHom = B →
      ∀ q ∈ B, x⁻¹ * q * x ∈ A := by
    intro A B x hAB q hq
    rw [← hAB] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    simpa [MulAut.conj_apply, mul_assoc] using ha
  have hmap' : ∀ {A B : Subgroup G} {x : G}, A.map (MulAut.conj x).toMonoidHom = B →
      ∀ q ∈ A, x * q * x⁻¹ ∈ B := by
    intro A B x hAB q hq
    rw [← hAB]
    exact ⟨q, hq, by simp [MulAut.conj_apply]⟩
  have hx₁ : ∀ q ∈ Q₁, (c⁻¹ * c') * q * (c⁻¹ * c')⁻¹ ∈ Q₁ := fun q hq => by
    have := hmap h1 _ (hmap' h1' q hq)
    rwa [show c⁻¹ * (c' * q * c'⁻¹) * c = (c⁻¹ * c') * q * (c⁻¹ * c')⁻¹ by group] at this
  have hx₂ : ∀ q ∈ Q₂, (c⁻¹ * c') * q * (c⁻¹ * c')⁻¹ ∈ Q₂ := fun q hq => by
    have := hmap h2 _ (hmap' h2' q hq)
    rwa [show c⁻¹ * (c' * q * c'⁻¹) * c = (c⁻¹ * c') * q * (c⁻¹ * c')⁻¹ by group] at this
  have hQ := S.mem_Q_of_fix_F4 hxH hx₁ hx₂ hx.2
  rw [← S.QU] at hQ
  exact S.mem_V_of_mem_cent_F4 hx (S.U_le_L hQ)

end Setup5_F4

end L1444

end CFSG.Quasithin.H13
