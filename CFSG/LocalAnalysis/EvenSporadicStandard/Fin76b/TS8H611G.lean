module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H611E
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H611F

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem center_W1 {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) {w : G}
    (hw : w ∈ Wsub h hα (zpowers α))
    (hc : ∀ w' ∈ Wsub h hα (zpowers α), w * w' * w⁻¹ * w'⁻¹ = 1) :
    w ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
  have hpair := hp
  obtain ⟨a, b, c, d, hE⟩ := hF.gen_four
  have hgen : ∀ g ∈ ({a, b, c, d} : Set G), g ∈ E := fun g hg =>
    hE ▸ Subgroup.subset_closure hg
  have ha : a ∈ E := hgen a (by simp)
  have hb : b ∈ E := hgen b (by simp)
  have hc' : c ∈ E := hgen c (by simp)
  have hd : d ∈ E := hgen d (by simp)
  obtain ⟨x, hx, hwx⟩ := h.exists_isLift_of_mem_Wsub hα (h.zinv_alpha hα) hE ha hb hc' hd hw
  have hxy : ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ = 1 := by
    intro y hy
    obtain ⟨w', hw'⟩ := h.exists_isLift hM hα (h.zinv_alpha hα) hE ha hb hc' hd hy
    have := hc w' (h.isLift_mem_Wsub hα (mem_zpowers α) hw')
    rw [(hpair x hx y hy w w' hwx hw').1] at this
    exact (iota_eq_one_iff hα.ne_one).1 this
  have hxz := h.oe.econfig.center x hx (fun f hf => (cmt_eq_one_iff.1 (hxy f hf)).symm)
  rcases hxz with rfl | rfl
  · exact h.mem_Zg_of_isLift_one hα hwx
  · have : IsLift h hα α (1 * x) w := by rwa [one_mul]
    exact h.mem_Zg_of_isLift_one hα (h.isLift_of_mul_t hα (one_mem E) this)

theorem center_W2 {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) {w : G}
    (hw : w ∈ Wsub h hα (zpowers (α * t)))
    (hc : ∀ w' ∈ Wsub h hα (zpowers (α * t)), w * w' * w⁻¹ * w'⁻¹ = 1) :
    w ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
  have hzz : ∀ u : G, z * (z * u * z⁻¹) * z⁻¹ = u := fun u => by
    calc z * (z * u * z⁻¹) * z⁻¹ = (z * z) * u * (z * z)⁻¹ := by group
      _ = u := by rw [h.z_sq]; group
  have h1 : z * w * z⁻¹ ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
    refine h.center_W1 hα hF hM hp (h.conj_z_W2 hα hw) fun w' hw' => ?_
    have hw'' := h.conj_z_W1 hα hw'
    have := hc _ hw''
    have e : (z * w * z⁻¹) * w' * (z * w * z⁻¹)⁻¹ * w'⁻¹ =
        z * (w * (z * w' * z⁻¹) * w⁻¹ * (z * w' * z⁻¹)⁻¹) * z⁻¹ := by
      calc (z * w * z⁻¹) * w' * (z * w * z⁻¹)⁻¹ * w'⁻¹ =
          (z * w * z⁻¹) * (z * (z * w' * z⁻¹) * z⁻¹) * (z * w * z⁻¹)⁻¹ *
            (z * (z * w' * z⁻¹) * z⁻¹)⁻¹ := by rw [hzz]
        _ = _ := by group
    rw [e, this]
    group
  have h2 : z * (z * w * z⁻¹) * z⁻¹ ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
    rcases (h.mem_Zg hα).1 h1 with e | e | e | e
    · rw [e]; simp
    · rw [e, h.z_conj_t]; exact h.t_mem_Zg hα
    · rw [e, h.z_conj_alpha hα]
      exact mul_mem (h.alpha_mem_Zg hα) (h.t_mem_Zg hα)
    · have : z * (α * t) * z⁻¹ = α := by
        calc z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
          _ = α * t * t := by rw [h.z_conj_alpha hα, h.z_conj_t]
          _ = α := by rw [mul_assoc, h.t_sq, mul_one]
      rw [e, this]
      exact h.alpha_mem_Zg hα
  rwa [hzz] at h2

theorem cmt_W1_Q {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) {w q : G}
    (hw : w ∈ Wsub h hα (zpowers α))
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    w * q * w⁻¹ * q⁻¹ = 1 ∨ w * q * w⁻¹ * q⁻¹ = α := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := h.Qs_eq_W1_W2 hα hF hM hq
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcomm, hd1, -, -, -, -, -⟩ :=
    h.lemma611Cl_of_pairing hα hF hM hp
  have c2 : Commute w b₂ := hcomm w hw b₂ hb₂
  have e : w * (b₁ * b₂) * w⁻¹ * (b₁ * b₂)⁻¹ = w * b₁ * w⁻¹ * b₁⁻¹ := by
    calc w * (b₁ * b₂) * w⁻¹ * (b₁ * b₂)⁻¹ = (w * b₁) * (b₂ * w⁻¹) * b₂⁻¹ * b₁⁻¹ := by group
      _ = (w * b₁) * (w⁻¹ * b₂) * b₂⁻¹ * b₁⁻¹ := by rw [c2.inv_left.eq.symm]
      _ = w * b₁ * w⁻¹ * b₁⁻¹ := by group
  rw [e]
  exact hd1 w hw b₁ hb₁

theorem cmt_W2_Q {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) {w q : G}
    (hw : w ∈ Wsub h hα (zpowers (α * t)))
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    w * q * w⁻¹ * q⁻¹ = 1 ∨ w * q * w⁻¹ * q⁻¹ = α * t := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := h.Qs_eq_W1_W2 hα hF hM hq
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcomm, -, -, hd2, -, -, -⟩ :=
    h.lemma611Cl_of_pairing hα hF hM hp
  have c1 : Commute w b₁ := (hcomm b₁ hb₁ w hw).symm
  have c12 : Commute b₁ b₂ := hcomm b₁ hb₁ b₂ hb₂
  have e : w * (b₁ * b₂) * w⁻¹ * (b₁ * b₂)⁻¹ = w * b₂ * w⁻¹ * b₂⁻¹ := by
    calc w * (b₁ * b₂) * w⁻¹ * (b₁ * b₂)⁻¹ = (w * b₁) * b₂ * w⁻¹ * b₂⁻¹ * b₁⁻¹ := by group
      _ = (b₁ * w) * b₂ * w⁻¹ * b₂⁻¹ * b₁⁻¹ := by rw [c1.eq]
      _ = b₁ * (w * b₂ * w⁻¹ * b₂⁻¹) * b₁⁻¹ := by group
      _ = w * b₂ * w⁻¹ * b₂⁻¹ := by
        have c3 : Commute b₁ (w * b₂ * w⁻¹ * b₂⁻¹) :=
          ((c1.symm.mul_right c12).mul_right c1.symm.inv_right).mul_right c12.inv_right
        rw [c3.eq]; group
  rw [e]
  exact hd2 w hw b₂ hb₂

theorem mem_Zg_of_cmt_t {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) {u : G}
    (hu : u ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hc : ∀ q ∈ Fsub h hα ⊓ centralizer ({α} : Set G),
      u * q * u⁻¹ * q⁻¹ = 1 ∨ u * q * u⁻¹ * q⁻¹ = t) :
    u ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := h.Qs_eq_W1_W2 hα hF hM hu
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcomm, hd1, -, hd2, -, -, -⟩ :=
    h.lemma611Cl_of_pairing hα hF hM hp
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  have hαt1 : α * t ≠ 1 := fun e => hα.ne_t (by rw [eq_inv_of_mul_eq_one_left e, hti])
  have hαt2 : α * t ≠ t := fun e => hα.ne_one (by simpa using e)
  have c12 : Commute a₁ a₂ := hcomm a₁ ha₁ a₂ ha₂
  have h1 : a₁ ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
    refine h.center_W1 hα hF hM hp ha₁ fun w' hw' => ?_
    have c2w : Commute a₂ w' := (hcomm w' hw' a₂ ha₂).symm
    have e1 : a₁ * a₂ * w' * (a₁ * a₂)⁻¹ * w'⁻¹ = a₁ * w' * a₁⁻¹ * w'⁻¹ := by
      have : a₂ * w' * a₂⁻¹ = w' := by rw [c2w.eq]; group
      calc a₁ * a₂ * w' * (a₁ * a₂)⁻¹ * w'⁻¹ = a₁ * (a₂ * w' * a₂⁻¹) * a₁⁻¹ * w'⁻¹ := by group
        _ = a₁ * w' * a₁⁻¹ * w'⁻¹ := by rw [this]
    rcases hd1 a₁ ha₁ w' hw' with e | e
    · exact e
    · exfalso
      rcases hc w' hw'.1 with e' | e'
      · rw [e1, e] at e'; exact hα.ne_one e'
      · rw [e1, e] at e'; exact hα.ne_t e'
  have h2 : a₂ ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
    refine h.center_W2 hα hF hM hp ha₂ fun w' hw' => ?_
    have c1w : Commute a₁ w' := hcomm a₁ ha₁ w' hw'
    have cy : Commute a₁ (a₂ * w' * a₂⁻¹) := (c12.mul_right c1w).mul_right c12.inv_right
    have e1 : a₁ * a₂ * w' * (a₁ * a₂)⁻¹ * w'⁻¹ = a₂ * w' * a₂⁻¹ * w'⁻¹ := by
      calc a₁ * a₂ * w' * (a₁ * a₂)⁻¹ * w'⁻¹ = a₁ * (a₂ * w' * a₂⁻¹) * a₁⁻¹ * w'⁻¹ := by group
        _ = (a₂ * w' * a₂⁻¹) * a₁ * a₁⁻¹ * w'⁻¹ := by rw [cy.eq]
        _ = a₂ * w' * a₂⁻¹ * w'⁻¹ := by group
    rcases hd2 a₂ ha₂ w' hw' with e | e
    · exact e
    · exfalso
      rcases hc w' hw'.1 with e' | e'
      · rw [e1, e] at e'; exact hαt1 e'
      · rw [e1, e] at e'; exact hαt2 e'
  exact mul_mem h1 h2

theorem normalizer_Q_fixes_t {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) {g : G}
    (hg : ∀ q : G, q ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ↔
      g * q * g⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    g * t * g⁻¹ = t := by
  have hgq : ∀ q ∈ Fsub h hα ⊓ centralizer ({α} : Set G),
      g * q * g⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G) := fun q hq => (hg q).1 hq
  have hgi : ∀ q ∈ Fsub h hα ⊓ centralizer ({α} : Set G),
      g⁻¹ * q * g ∈ Fsub h hα ⊓ centralizer ({α} : Set G) := fun q hq => by
    rw [hg, show g * (g⁻¹ * q * g) * g⁻¹ = q by group]
    exact hq
  have htZ : t ∈ (zpowers α ⊔ zpowers t : Subgroup G) := h.t_mem_Zg hα
  have hZ : g * t * g⁻¹ ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
    refine (h.mem_Zg hα).2 ((h.center_QF hα).1 ⟨hgq t (h.Zg_cent_Q hα htZ).1, fun q hq => ?_⟩)
    have e := (h.Zg_cent_Q hα htZ).2 (g⁻¹ * q * g) (hgi q hq)
    calc g * t * g⁻¹ * q = g * (t * (g⁻¹ * q * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * q * g) * t) * g⁻¹ := by rw [e]
      _ = q * (g * t * g⁻¹) := by group
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hex1, -, hex2, -, -⟩ :=
    h.lemma611Cl_of_pairing hα hF hM hp
  rcases (h.mem_Zg hα).1 hZ with e | e | e | e
  · exact absurd (by simpa using e) h.t_ne
  · exact e
  · exfalso
    have hgα : g⁻¹ * α * g = t := by rw [← e]; group
    obtain ⟨w, hw, w', hw', hww⟩ := hex1
    have hu : ∀ w₀ ∈ Wsub h hα (zpowers α),
        g⁻¹ * w₀ * g ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
      intro w₀ hw₀
      refine h.mem_Zg_of_cmt_t hα hF hM hp (hgi w₀ hw₀.1) fun q hq => ?_
      have e2 : g⁻¹ * w₀ * g * q * (g⁻¹ * w₀ * g)⁻¹ * q⁻¹ =
          g⁻¹ * (w₀ * (g * q * g⁻¹) * w₀⁻¹ * (g * q * g⁻¹)⁻¹) * g := by group
      rw [e2]
      rcases h.cmt_W1_Q hα hF hM hp hw₀ (hgq q hq) with e3 | e3
      · left; rw [e3]; group
      · right; rw [e3, hgα]
    have hc1 := (h.Zg_cent_Q hα (hu w hw)).2 _ (hgi w' hw'.1)
    have e4 : g⁻¹ * (w * w' * w⁻¹ * w'⁻¹) * g = 1 := by
      calc g⁻¹ * (w * w' * w⁻¹ * w'⁻¹) * g
          = (g⁻¹ * w * g) * (g⁻¹ * w' * g) * (g⁻¹ * w * g)⁻¹ * (g⁻¹ * w' * g)⁻¹ := by group
        _ = 1 := by rw [hc1]; group
    rw [hww, hgα] at e4
    exact h.t_ne e4
  · exfalso
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
    have hgα : g⁻¹ * (α * t) * g = t := by rw [← e]; group
    obtain ⟨w, hw, w', hw', hww⟩ := hex2
    have hu : ∀ w₀ ∈ Wsub h hα (zpowers (α * t)),
        g⁻¹ * w₀ * g ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
      intro w₀ hw₀
      refine h.mem_Zg_of_cmt_t hα hF hM hp (hgi w₀ hw₀.1) fun q hq => ?_
      have e2 : g⁻¹ * w₀ * g * q * (g⁻¹ * w₀ * g)⁻¹ * q⁻¹ =
          g⁻¹ * (w₀ * (g * q * g⁻¹) * w₀⁻¹ * (g * q * g⁻¹)⁻¹) * g := by group
      rw [e2]
      rcases h.cmt_W2_Q hα hF hM hp hw₀ (hgq q hq) with e3 | e3
      · left; rw [e3]; group
      · right; rw [e3, hgα]
    have hc1 := (h.Zg_cent_Q hα (hu w hw)).2 _ (hgi w' hw'.1)
    have e4 : g⁻¹ * (w * w' * w⁻¹ * w'⁻¹) * g = 1 := by
      calc g⁻¹ * (w * w' * w⁻¹ * w'⁻¹)
          * g = (g⁻¹ * w * g) * (g⁻¹ * w' * g) * (g⁻¹ * w * g)⁻¹ * (g⁻¹ * w' * g)⁻¹ := by group
        _ = 1 := by rw [hc1]; group
    rw [hww, hgα] at e4
    exact h.t_ne e4

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
