module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRFuT5

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10 Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau : G} {T₂ : Subgroup G}
variable (D : FzRNum t x₁ x₂ lam rho tau T₂)

private theorem fzrAux_sq_eq_one {x : ℕ} (hx : x < 512)
    (hxx : (fzrPar D).e x x = 0) : fzrMu D x * fzrMu D x = 1 := by
  have h := fzrMu_mul D hx hx
  rw [hxx, fzrMu_zero] at h
  exact h.symm

private theorem fzrAux_ne_one {x : ℕ} (hx : x < 512) (hx0 : x ≠ 0) :
    fzrMu D x ≠ 1 := by
  intro h
  have h0 : fzrMu D x = fzrMu D 0 := by rw [h, fzrMu_zero]
  exact hx0 (fzrMu_inj D hx (by norm_num) h0)

private theorem fzrAux_wreath_le_L (h : Ctx t L S x₁ x₂ lam rho tau) :
    wreathGrp x₁ x₂ lam ≤ L := by
  rw [← h.inf_eq]
  exact inf_le_right

private theorem fzrAux_comm_L (h : Ctx t L S x₁ x₂ lam rho tau) {c : G} (hc : c ∈ L) :
    c * t = t * c :=
  Subgroup.mem_centralizer_iff.mp h.hyp.mem_centralizer c hc

private theorem fzrAux_conj_iff {v w l : G} (hl : w = l * v * l⁻¹) :
    (∃ g : G, g * t * g⁻¹ = w) ↔ ∃ g : G, g * t * g⁻¹ = v := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨l⁻¹ * g, by
      calc (l⁻¹ * g) * t * (l⁻¹ * g)⁻¹ = l⁻¹ * (g * t * g⁻¹) * l := by group
        _ = l⁻¹ * w * l := by rw [hg]
        _ = v := by rw [hl]; group⟩
  · rintro ⟨g, hg⟩
    exact ⟨l * g, by
      calc (l * g) * t * (l * g)⁻¹ = l * (g * t * g⁻¹) * l⁻¹ := by group
        _ = l * v * l⁻¹ := by rw [hg]
        _ = w := hl.symm⟩

private theorem fzrAux_kout_outer (h : Ctx t L S x₁ x₂ lam rho tau) {sp l : ℕ}
    (hsp_lt : sp < 512) (hl : l < 512) (hTL : (fzrPar D).inTL l = true)
    (hv2 : fzrMu D sp * fzrMu D sp = 1) (hvC : fzrMu D sp ∈ invCent t)
    (hvL : fzrMu D sp ∉ twoCore t ⊔ L)
    (hw2 : fzrMu D ((fzrPar D).e l sp) * fzrMu D ((fzrPar D).e l sp) = 1) :
    fzrTh D ((fzrPar D).e l sp) ↔ fzrTh D sp := by
  have hlL : fzrMu D l ∈ L := fzrAux_wreath_le_L h (fzrMu_inTL D hl hTL)
  have hL_le : L ≤ invCent t := S4A.L_le_invCent h.hyp
  have hwv : fzrMu D ((fzrPar D).e l sp) * (fzrMu D sp)⁻¹ ∈ L := by
    rw [fzrMu_mul D hl hsp_lt]
    have h : (fzrMu D l * fzrMu D sp) * (fzrMu D sp)⁻¹ = fzrMu D l := by group
    rw [h]
    exact hlL
  have hwC : fzrMu D ((fzrPar D).e l sp) ∈ invCent t := by
    rw [fzrMu_mul D hl hsp_lt]
    exact (invCent t).mul_mem (hL_le hlL) hvC
  obtain ⟨l', -, hl'eq⟩ :=
    S4A.outer_coset_conj h.hyp hvC hv2 hvL hwC hw2 hwv
  have help_lt : (fzrPar D).e l sp < 512 := (fzrPar_mul D).lt l sp hl hsp_lt
  have hiff := fzrAux_conj_iff (t := t) hl'eq
  exact ⟨fun hθ => ⟨hsp_lt, (hiff.mp hθ.2)⟩, fun hθ => ⟨help_lt, (hiff.mpr hθ.2)⟩⟩

theorem fzr_th_forb (h : Ctx t L S x₁ x₂ lam rho tau) {x : ℕ} (hx : x < 512)
    (hTL : (fzrPar D).inTL x = true) (hx0 : x ≠ 0) (hxx : (fzrPar D).e x x = 0) :
    ¬ fzrTh D x := by
  rintro ⟨-, g, hg⟩
  have hzL : fzrMu D x ∈ L := fzrAux_wreath_le_L h (fzrMu_inTL D hx hTL)
  have hsq : fzrMu D x * fzrMu D x = 1 := fzrAux_sq_eq_one D hx hxx
  have hne : fzrMu D x ≠ 1 := fzrAux_ne_one D hx hx0
  obtain ⟨c, hcL, hcz⟩ := h.invol_L (fzrMu D x) hzL hsq hne
  exact S4A.not_conj_z_of_ctx h ⟨c⁻¹ * g, by
    calc (c⁻¹ * g) * t * (c⁻¹ * g)⁻¹
        = c⁻¹ * (g * t * g⁻¹) * c := by group
      _ = c⁻¹ * fzrMu D x * c := by rw [hg]
      _ = c⁻¹ * (c * (x₁ * x₂) ^ 2 * c⁻¹) * c := by rw [← hcz]
      _ = (x₁ * x₂) ^ 2 := by group⟩

theorem fzr_th_wrule (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) {x : ℕ}
    (hW : (fzrPar D).inW x = true) (hθ : fzrTh D x) : (fzrPar D).inTZ x = true := by
  obtain ⟨hx, g, hg⟩ := hθ
  have hMxW : fzrMu D x ∈ ctxW t x₁ x₂ := fzrMu_inW D hW
  obtain ⟨z, hz, hz_eq⟩ := fzr_conj_t_mem_W h hK (hg.symm ▸ hMxW)
  exact fzrMu_inTZ D hz hx (hg ▸ hz_eq)

theorem fzr_th_ktl [IsSimpleGroup G] (h : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 2) {x : ℕ} (hx : x < 512) (hTL : (fzrPar D).inTL x = true)
    (hx0 : x ≠ 0) (hxx : (fzrPar D).e x x = 0) :
    fzrTh D ((fzrPar D).e (fzrPar D).tI x) := by
  have hz : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  obtain ⟨n, -, hn⟩ := fzr_exists_conj_t_mul h hK hz
  have hyL : fzrMu D x ∈ L := fzrAux_wreath_le_L h (fzrMu_inTL D hx hTL)
  have hy2 : fzrMu D x * fzrMu D x = 1 := fzrAux_sq_eq_one D hx hxx
  have hy1 : fzrMu D x ≠ 1 := fzrAux_ne_one D hx hx0
  obtain ⟨c, hcL, hcz⟩ := h.invol_L (fzrMu D x) hyL hy2 hy1
  have hct : c * t = t * c := fzrAux_comm_L h hcL
  have htI : (fzrPar D).tI = 64 := (fzrPar_nums D).1
  have htI_lt : (fzrPar D).tI < 512 := (fzrPar_lt D).1
  have he_lt : (fzrPar D).e (fzrPar D).tI x < 512 := (fzrPar_mul D).lt _ _ htI_lt hx
  refine ⟨he_lt, c * n, ?_⟩
  rw [fzrMu_mul D htI_lt hx, htI, fzrMu_tI D]
  calc (c * n) * t * (c * n)⁻¹
      = c * (n * t * n⁻¹) * c⁻¹ := by group
    _ = c * (t * (x₁ * x₂) ^ 2) * c⁻¹ := by rw [hn]
    _ = (c * t * c⁻¹) * (c * (x₁ * x₂) ^ 2 * c⁻¹) := by group
    _ = t * fzrMu D x := by rw [hct, hcz]; group

theorem fzr_th_kout (h : Ctx t L S x₁ x₂ lam rho tau) {sp : ℕ}
    (hsp : sp = (fzrPar D).sI ∨ sp = (fzrPar D).e (fzrPar D).tI (fzrPar D).sI) {l : ℕ}
    (hl : l < 512) (hTL : (fzrPar D).inTL l = true)
    (hinv : (fzrPar D).e ((fzrPar D).e l sp) ((fzrPar D).e l sp) = 0) :
    fzrTh D ((fzrPar D).e l sp) ↔ fzrTh D sp := by
  have hsI : (fzrPar D).sI = 128 := (fzrPar_nums D).2
  have htI : (fzrPar D).tI = 64 := (fzrPar_nums D).1
  have htI_lt : (fzrPar D).tI < 512 := (fzrPar_lt D).1
  have hsI_lt : (fzrPar D).sI < 512 := (fzrPar_lt D).2.1
  have hsp_lt : sp < 512 := by
    rcases hsp with rfl | rfl
    · exact hsI_lt
    · exact (fzrPar_mul D).lt _ _ htI_lt hsI_lt
  have help_lt : (fzrPar D).e l sp < 512 := (fzrPar_mul D).lt l sp hl hsp_lt
  have hw2 : fzrMu D ((fzrPar D).e l sp) * fzrMu D ((fzrPar D).e l sp) = 1 :=
    fzrAux_sq_eq_one D help_lt hinv
  have htt : t * t = 1 := by rw [← pow_two]; exact D.t_sq
  have htautau : tau * tau = 1 := by rw [← pow_two]; exact D.tau_sq1
  have htaut : tau * t = t * tau := by
    calc tau * t = (tau * t * tau⁻¹) * tau := by group
      _ = t * tau := by rw [D.tau_t]
  have htauC : tau ∈ invCent t := h.le_invCent h.tau_mem
  have hv2 : fzrMu D sp * fzrMu D sp = 1 := by
    rcases hsp with rfl | rfl
    · rw [hsI, fzrMu_sI D]; exact htautau
    · rw [fzrMu_mul D htI_lt hsI_lt, htI, hsI, fzrMu_tI D, fzrMu_sI D]
      calc (t * tau) * (t * tau) = t * (tau * t) * tau := by group
        _ = t * (t * tau) * tau := by rw [htaut]
        _ = (t * t) * (tau * tau) := by group
        _ = 1 := by rw [htt, htautau, one_mul]
  have hvC : fzrMu D sp ∈ invCent t := by
    rcases hsp with rfl | rfl
    · rw [hsI, fzrMu_sI D]; exact htauC
    · rw [fzrMu_mul D htI_lt hsI_lt, htI, hsI, fzrMu_tI D, fzrMu_sI D]
      exact (invCent t).mul_mem (by rw [S4A.mem_invCent_iff]) htauC
  have hvL : fzrMu D sp ∉ twoCore t ⊔ L := by
    rcases hsp with rfl | rfl
    · rw [hsI, fzrMu_sI D]; exact h.tau_not_mem
    · rw [fzrMu_mul D htI_lt hsI_lt, htI, hsI, fzrMu_tI D, fzrMu_sI D]
      intro hmem
      exact h.tau_not_mem (by
        have htmem : t ∈ twoCore t ⊔ L := Subgroup.mem_sup_left h.hyp.mem_twoCore
        have hprod := Subgroup.mul_mem (twoCore t ⊔ L) ((twoCore t ⊔ L).inv_mem htmem) hmem
        simpa using hprod)
  exact fzrAux_kout_outer D h hsp_lt hl hTL hv2 hvC hvL hw2

end CFSG.OddStandard.SmallF3.FritzII
