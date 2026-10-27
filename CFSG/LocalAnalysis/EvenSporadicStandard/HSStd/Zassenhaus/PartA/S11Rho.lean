module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S11Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S11Cover

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath

set_option linter.unusedSectionVars false

section Aux

theorem s11_congr_conj {K H : Type*} [Group K] [Group H] (e : K ≃* H) (k : K) :
    MulAut.congr e (MulAut.conj k) = MulAut.conj (e k) := by
  ext h
  simp [MulAut.congr_apply, MulAut.conj_apply]

end Aux

section Rho

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
variable (hb : PAB G L t E W z) (a : PA10 L t E z)

include hb in
theorem S11_pd : PairData (Cen a.u) a.L₁ t := by
  have := PA8.pairData hb a.toPA9.toPA8
  rw [a.ub_eq] at this
  exact this

include a in
@[expose] noncomputable def S11_e : ↥a.L₁ ⧸ center ↥a.L₁ ≃* alternatingGroup (Fin 6) :=
  Classical.choice a.L₁_A6

include a in
theorem S11_perfect : commutator ↥a.L₁ = ⊤ := by
  obtain ⟨-, -, hq⟩ := a.L₁_comp
  exact hq.2.1

include a in
@[expose] noncomputable def S11_f₀ : MulAut ↥a.L₁ →* MulAut (alternatingGroup (Fin 6)) :=
  (MulAut.congr (S11_e a)).toMonoidHom.comp (s11AutQuot ↥a.L₁)

theorem S11_f₀_injective : Function.Injective (S11_f₀ a) :=
  (MulAut.congr (S11_e a)).injective.comp (s11AutQuot_injective (S11_perfect a))

theorem S11_f₀_apply (φ : MulAut ↥a.L₁) (l : ↥a.L₁) :
    S11_f₀ a φ (s11Pi a.L₁ (S11_e a) l) = s11Pi a.L₁ (S11_e a) (φ l) := by
  show MulAut.congr (S11_e a) (s11AutQuot ↥a.L₁ φ) (S11_e a (QuotientGroup.mk l)) =
    S11_e a (QuotientGroup.mk (φ l))
  simp [MulAut.congr_apply, s11AutQuot_mk]

theorem S11_f₀_conj (l : ↥a.L₁) :
    S11_f₀ a (MulAut.conj l) = MulAut.conj (s11Pi a.L₁ (S11_e a) l) := by
  show MulAut.congr (S11_e a) (s11AutQuot ↥a.L₁ (MulAut.conj l)) = _
  rw [s11AutQuot_conj, s11_congr_conj]
  rfl

@[expose] noncomputable def S11_rhoBar : ↥(Cen a.u) →* Wr2 (MulAut (alternatingGroup (Fin 6))) :=
  (mapHom (S11_f₀ a)).comp (S11_pd hb a).rho

theorem S11_rhoBar_ker : (S11_rhoBar hb a).ker = (S11_pd hb a).rho.ker := by
  ext p
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  show mapHom (S11_f₀ a) ((S11_pd hb a).rho p) = 1 ↔ _
  exact map_eq_one_iff _ (s11_mapHom_injective (S11_f₀_injective a))

theorem S11_card_ker : Nat.card (S11_rhoBar hb a).ker = 4 := by
  rw [S11_rhoBar_ker, (S11_pd hb a).ker_rho]
  have hF : Cen a.u ⊓ centralizer (a.L₁ : Set G) ⊓ centralizer ((conjSub t a.L₁ : Subgroup G) : Set G)
      = a.F₀ := by
    rw [← a.CPE_eq, centralizer_sup_eq_inf, a.ub_eq, inf_assoc]
  have h4 : Nat.card a.F₀ = 4 := a.F₀_card a.d8_case
  rw [← h4, ← hF,
    ← Subgroup.card_map_of_injective (Cen a.u).subtype_injective,
    Subgroup.subgroupOf_map_subtype]
  congr 2
  ext g
  simp only [mem_inf]
  tauto

theorem S11_y_normalizes {x : G} (hx : x ∈ a.L₁) (hxy : a.y = x * (t * x * t⁻¹)) :
    a.y ∈ normalizer (a.L₁ : Set G) := by
  have h1 : x ∈ normalizer (a.L₁ : Set G) := le_normalizer hx
  have h2 : t * x * t⁻¹ ∈ normalizer (a.L₁ : Set G) :=
    mem_normalizer_of_forall_commute a.L₁ fun k hk => (a.L₁_comm k hk x hx).symm
  rw [hxy]
  exact mul_mem h1 h2

include hb in
theorem S11_y_mem_Cen : a.y ∈ Cen a.u := mem_Cen.2 (S11_u_y hb a).symm

theorem S11_rho_y {x : G} (hx : x ∈ a.L₁) (hxy : a.y = x * (t * x * t⁻¹)) :
    S11_rhoBar hb a ⟨a.y, S11_y_mem_Cen hb a⟩ =
    base (MulAut.conj (s11Pi a.L₁ (S11_e a) ⟨x, hx⟩))
      (MulAut.conj (s11Pi a.L₁ (S11_e a) ⟨x, hx⟩)) := by
  have hn := S11_y_normalizes a hx hxy
  have hcomm : Commute (a.y) t := S11_y_t hb a
  have h1 := (S11_pd hb a).rho_of_commute_t_of_normalizes ⟨a.y, S11_y_mem_Cen hb a⟩ hn hcomm
  have h2 : conjAutOf a.L₁ hn = MulAut.conj (⟨x, hx⟩ : ↥a.L₁) := by
    ext l
    rw [conjAutOf_apply]
    show a.y * l * a.y⁻¹ = x * l * x⁻¹
    have hc : (t * x * t⁻¹) * l = l * (t * x * t⁻¹) := (a.L₁_comm l.1 l.2 x hx).eq.symm
    rw [hxy]
    calc x * (t * x * t⁻¹) * l * (x * (t * x * t⁻¹))⁻¹
        = x * ((t * x * t⁻¹) * l) * (t * x * t⁻¹)⁻¹ * x⁻¹ := by group
      _ = x * (l * (t * x * t⁻¹)) * (t * x * t⁻¹)⁻¹ * x⁻¹ := by rw [hc]
      _ = x * l * x⁻¹ := by group
  show mapHom (S11_f₀ a) ((S11_pd hb a).rho _) = _
  rw [h1, h2, mapHom_base, S11_f₀_conj]

include hb in
theorem S11_pi_x_ord {x : G} (hx : x ∈ a.L₁) (hx3 : orderOf x = 3) :
    orderOf (s11Pi a.L₁ (S11_e a) ⟨x, hx⟩) = 3 := by
  obtain ⟨X, -, -, -, -, -, -, -, h⟩ := s11_exists_X (e := S11_e a) (S11_u_sq hb a)
    (S11_hZ hb a) hx hx3
  exact h

end Rho

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
