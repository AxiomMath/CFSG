module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Prop46c

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q F : Subgroup G} {FA : G → Prop}

namespace Cfg1

theorem S_le_normalizer_R (h : Cfg1 G z S P Q F FA) : S ≤ normalizer ((P ⊔ Q : Subgroup G) : Set G) := by
  have key : ∀ s ∈ S, ∀ r ∈ P ⊔ Q, s * r * s⁻¹ ∈ P ⊔ Q := by
    intro s hs r hr
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute (fun a ha b hb => h.PQ_comm a ha b hb) hr
    have e : s * (p * q) * s⁻¹ = (s * p * s⁻¹) * (s * q * s⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left (h.P_norm s hs p hp)) (mem_sup_right (h.Q_norm s hs q hq))
  intro s hs
  refine mem_normalizer_of_both (fun x hx => key s hs x hx) (fun x hx => ?_)
  have := key s⁻¹ (S.inv_mem hs) x hx
  simpa using this

theorem exists_g_into_S (h : Cfg1 G z S P Q F FA) {y : G} (hzy : IsConj z y) {B : Subgroup G}
    (hBS : B ≤ S) (hBy : ∀ b ∈ B, b * y = y * b) :
    ∃ g : G, g⁻¹ * z * g = y ∧ ∀ b ∈ B, g * b * g⁻¹ ∈ S := by
  obtain ⟨c₀, hc₀⟩ := isConj_iff.1 hzy
  have hB2 : IsPGroup 2 ↥B := h.S_pgroup.to_le hBS
  have hB'2 : IsPGroup 2 ↥(cj B c₀) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hB2
    exact (IsPGroup.iff_card).2 ⟨n, by rw [cj_card, hn]⟩
  have hB'C : cj B c₀ ≤ centralizer ({z} : Set G) := by
    intro x hx
    rw [mem_cj] at hx
    have h1 := hBy _ hx
    rw [← hc₀] at h1
    apply Subgroup.mem_centralizer_singleton_iff.2
    have e : c₀ * (x * z) * c₀⁻¹ = c₀ * (z * x) * c₀⁻¹ := by
      calc c₀ * (x * z) * c₀⁻¹ = (c₀ * x * c₀⁻¹) * (c₀ * z * c₀⁻¹) := by group
        _ = (c₀ * z * c₀⁻¹) * (c₀ * x * c₀⁻¹) := h1
        _ = c₀ * (z * x) * c₀⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  obtain ⟨P', hP', hBP'⟩ := exists_syl2In_ge hB'2 hB'C
  obtain ⟨c, hcC, hPc⟩ := h.S_syl_C.exists_conj hP'
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  refine ⟨c * c₀⁻¹, ?_, ?_⟩
  · calc (c * c₀⁻¹)⁻¹ * z * (c * c₀⁻¹) = c₀ * (c⁻¹ * z * c) * c₀⁻¹ := by group
      _ = c₀ * z * c₀⁻¹ := by rw [show c⁻¹ * z * c = z by
          calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
            _ = c⁻¹ * (c * z) := by rw [hcz]
            _ = z := by group]
      _ = y := hc₀
  · intro b hb
    have hx : c₀⁻¹ * b * c₀ ∈ cj B c₀ := by
      rw [mem_cj]
      have e : c₀ * (c₀⁻¹ * b * c₀) * c₀⁻¹ = b := by group
      rw [e]; exact hb
    have hxP' : c₀⁻¹ * b * c₀ ∈ P' := hBP' hx
    rw [hPc, mem_cj] at hxP'
    have e : c * c₀⁻¹ * b * (c * c₀⁻¹)⁻¹ = c * (c₀⁻¹ * b * c₀) * c⁻¹ := by group
    rw [e]; exact hxP'

end Cfg1

namespace Cfg1K

theorem final_block (h : Cfg1K G z S P Q F FA) {y : G} (hy : Is47b S P F y) (hzy : IsConj z y)
    (hR : ∀ w ∈ P ⊔ Q, w * w = 1 → w ≠ 1 → w ≠ z → ¬ IsConj z w)
    (he : ∀ e ∈ S, e * e = 1 → e ∈ (P ⊔ Q) ⊔ zpowers y) {u : G} (huR : u ∈ P ⊔ Q) (hu1 : u ≠ 1)
    (huz : u ≠ z) (hu2 : u * u = 1) (hyu : y * u = u * y) (hzyu : IsConj z (y * u)) : False := by
  have hy' := hy
  obtain ⟨hyS, hy2, hyPF, -⟩ := hy'
  have hz1 := h.z_ne
  have hz2 := h.z_sq
  have huS : u ∈ S := (sup_le h.P_le h.Q_le) huR
  have hyuS : y * u ∈ S := mul_mem hyS huS
  have hyu2 : (y * u) * (y * u) = 1 := by
    calc (y * u) * (y * u) = y * (u * y) * u := by group
      _ = y * (y * u) * u := by rw [hyu]
      _ = (y * y) * (u * u) := by group
      _ = 1 := by rw [hy2, hu2]; group
  have hyuPF : y * u ∉ P ⊔ F := by
    intro hmem
    apply hyPF
    have : (y * u) * u⁻¹ ∈ P ⊔ F := mul_mem hmem (inv_mem (h.toCfg1.R_le_PF huR))
    simpa using this
  have hyu' : Is47b S P F (y * u) := h.toCfg1.is47b_of hyuS hyu2 hyuPF
  have hzc : z * (y * u) = (y * u) * z := h.z_cent _ hyuS
  have hyuz2 : (y * u * z) * (y * u * z) = 1 := by
    calc (y * u * z) * (y * u * z) = (y * u) * (z * (y * u)) * z := by group
      _ = (y * u) * ((y * u) * z) * z := by rw [hzc]
      _ = ((y * u) * (y * u)) * (z * z) := by group
      _ = 1 := by rw [hyu2, hz2]; group
  have hyuz_P : (y * u * z) * (y * u)⁻¹ ∈ P := by
    have e : (y * u * z) * (y * u)⁻¹ = z := by
      calc (y * u * z) * (y * u)⁻¹ = (z * (y * u)) * (y * u)⁻¹ := by rw [hzc]
        _ = z := by group
    rw [e]; exact h.z_P
  obtain ⟨p, hp, hpy⟩ := h.conj_in_Py hyu' hyuz2 hyuz_P
  have hzyuz : IsConj z (y * u * z) :=
    hzyu.trans (isConj_iff.2 ⟨p⁻¹, by rw [inv_inv]; exact hpy⟩)
  have hBS : zpowers (y * u) ⊔ zpowers z ≤ S := sup_le (zpowers_le.2 hyuS) (zpowers_le.2 h.z_mem)
  have hBy : ∀ b ∈ zpowers (y * u) ⊔ zpowers z, b * y = y * b := by
    have hle : zpowers (y * u) ⊔ zpowers z ≤ centralizer ({y} : Set G) := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · apply Subgroup.mem_centralizer_singleton_iff.2
        calc y * u * y = y * (u * y) := by group
          _ = y * (y * u) := by rw [hyu]
      · exact Subgroup.mem_centralizer_singleton_iff.2 (h.z_cent y hyS)
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hb)
  obtain ⟨g, hg, hgB⟩ := h.exists_g_into_S hzy hBS hBy
  have hyuB : y * u ∈ zpowers (y * u) ⊔ zpowers z := mem_sup_left (mem_zpowers _)
  have hyuzB : y * u * z ∈ zpowers (y * u) ⊔ zpowers z :=
    mul_mem hyuB (mem_sup_right (mem_zpowers z))
  have he₁S := hgB _ hyuB
  have he₂S := hgB _ hyuzB
  have hconjg : ∀ w : G, (g * w * g⁻¹) * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := fun w => by group
  have he₁2 : (g * (y * u) * g⁻¹) * (g * (y * u) * g⁻¹) = 1 := by rw [hconjg, hyu2]; group
  have he₂2 : (g * (y * u * z) * g⁻¹) * (g * (y * u * z) * g⁻¹) = 1 := by
    rw [hconjg, hyuz2]; group
  have hconj1 : ∀ w : G, g * w * g⁻¹ = 1 → w = 1 := by
    intro w e
    calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  have hconjy : ∀ w : G, g * w * g⁻¹ = z → w = y := by
    intro w e
    calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = g⁻¹ * z * g := by rw [e]
      _ = y := hg
  have hyu1 : y * u ≠ 1 := fun e => hyuPF (e ▸ one_mem _)
  have he₁1 : g * (y * u) * g⁻¹ ≠ 1 := fun e => hyu1 (hconj1 _ e)
  have he₁z : g * (y * u) * g⁻¹ ≠ z := by
    intro e
    have := hconjy _ e
    apply hu1
    calc u = y⁻¹ * (y * u) := by group
      _ = 1 := by rw [this]; group
  have hyuz1 : y * u * z ≠ 1 := by
    intro e
    apply hyuPF
    have : y * u = z⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [this, inv_eq_of_mul_eq_one_right hz2]
    exact mem_sup_left h.z_P
  have he₂1 : g * (y * u * z) * g⁻¹ ≠ 1 := fun e => hyuz1 (hconj1 _ e)
  have he₂z : g * (y * u * z) * g⁻¹ ≠ z := by
    intro e
    have := hconjy _ e
    apply huz
    have e1 : u * z = 1 := by
      calc u * z = y⁻¹ * (y * u * z) := by group
        _ = 1 := by rw [this]; group
    calc u = u * z * z := by rw [mul_assoc, hz2, mul_one]
      _ = z := by rw [e1, one_mul]
  have hze₁ : IsConj z (g * (y * u) * g⁻¹) := hzyu.trans (isConj_iff.2 ⟨g, rfl⟩)
  have hze₂ : IsConj z (g * (y * u * z) * g⁻¹) := hzyuz.trans (isConj_iff.2 ⟨g, rfl⟩)
  have hnormR : ∀ s ∈ S, ∀ r ∈ P ⊔ Q, s * r * s⁻¹ ∈ P ⊔ Q := fun s hs r hr =>
    (mem_normalizer_iff.1 (h.toCfg1.S_le_normalizer_R hs) r).1 hr
  have hdec : ∀ e ∈ S, e * e = 1 → e ≠ 1 → e ≠ z → IsConj z e → ∃ r ∈ P ⊔ Q, e = y * r := by
    intro e heS he2 he1 hez hze
    have hmem := he e heS he2
    have hnorm : zpowers y ≤ normalizer ((P ⊔ Q : Subgroup G) : Set G) :=
      zpowers_le.2 (h.toCfg1.S_le_normalizer_R hyS)
    rw [sup_comm] at hmem
    obtain ⟨b, hb, r, hr, rfl⟩ := mem_sup_of_le_normalizer hnorm hmem
    rcases (mem_zpowers_of_sq hy2).1 hb with hb1 | hb1
    · exfalso
      rw [hb1, one_mul] at he2 he1 hez hze
      exact hR r hr he2 he1 hez hze
    · exact ⟨r, hr, by rw [hb1]⟩
  obtain ⟨r₁, hr₁, hr₁e⟩ := hdec _ he₁S he₁2 he₁1 he₁z hze₁
  obtain ⟨r₂, hr₂, hr₂e⟩ := hdec _ he₂S he₂2 he₂1 he₂z hze₂
  have he₃ : g * z * g⁻¹ = (g * (y * u) * g⁻¹) * (g * (y * u * z) * g⁻¹) := by
    have e : (y * u) * (y * u * z) = z := by
      calc (y * u) * (y * u * z) = ((y * u) * (y * u)) * z := by group
        _ = z := by rw [hyu2, one_mul]
    calc g * z * g⁻¹ = g * ((y * u) * (y * u * z)) * g⁻¹ := by rw [e]
      _ = (g * (y * u) * g⁻¹) * (g * (y * u * z) * g⁻¹) := by group
  have he₃R : g * z * g⁻¹ ∈ P ⊔ Q := by
    rw [he₃, hr₁e, hr₂e]
    have e : y * r₁ * (y * r₂) = (y * r₁ * y⁻¹) * r₂ := by
      calc y * r₁ * (y * r₂) = (y * r₁ * y⁻¹) * (y * y) * r₂ := by group
        _ = (y * r₁ * y⁻¹) * r₂ := by rw [hy2]; group
    rw [e]
    exact mul_mem (hnormR y hyS r₁ hr₁) hr₂
  have he₃2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by rw [hconjg, hz2]; group
  have he₃1 : g * z * g⁻¹ ≠ 1 := fun e => hz1 (hconj1 _ e)
  have hze₃ : IsConj z (g * z * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  by_cases he₃z : g * z * g⁻¹ = z
  · have hyz' : y = z := by
      calc y = g⁻¹ * z * g := hg.symm
        _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [he₃z]
        _ = z := by group
    exact hyPF (hyz' ▸ mem_sup_left h.z_P)
  · exact hR _ he₃R he₃2 he₃1 he₃z hze₃

theorem prop46 (h : Cfg1K G z S P Q F FA) (hF : IsCyclic ↥F)
    (h1024 : Bg.B_maximalClass_of_small_centralizer)
    (h119 : ∀ s ∈ P ⊔ F, s ∉ P ⊔ Q → ∀ V : Subgroup G, V ≤ P → IsCyclic ↥V →
      V.relIndex P = 2 → ∃ v ∈ V, s * v ≠ v * s)
    (hT : HThompson G z S) (hTr : HTransfer G S) (hZ : ∃ t ∈ S, t ≠ z ∧ IsConj z t)
    (hSR : ∀ a ∈ S, ∀ b ∈ S, a * b * a⁻¹ * b⁻¹ ∈ P ⊔ Q)
    (hCR : ∀ w ∈ P ⊔ Q, ∀ w' ∈ P ⊔ Q, w * w = 1 → w' * w' = 1 → w ≠ 1 → w ≠ z → w' ≠ 1 →
      w' ≠ z → IsConj w w') : False := by
  have hR := h.R_not_zG hF h1024 h119 hT hCR
  obtain ⟨y, hyS0, hyz, hzy⟩ := hZ
  have hy : Is47b S P F y := h.Y_of_conj hF hR hyS0 hzy hyz
  obtain ⟨U, hUR, hU4, hUn, hUy, u, huU, hu1, huz, u₁, hu₁P, u₂, hu₂Q, hu, hu₁sq, hu₂sq, hinv₂,
    hinv₁⟩ := h.cfg_for_y hF h1024 hy
  have huR : u ∈ P ⊔ Q := hUR huU
  have hu2 : u * u = 1 := hU4.1 u huU
  have hnotz : ¬ IsConj z u := hR u huR hu2 hu1 huz
  have hyu : y * u = u * y := hUy u huU
  obtain ⟨s, hsS, hs⟩ :=
    h.exists_conj_yu hF hSR hTr hy hzy hu₁P hu₂Q hu hu₁sq hu₂sq hu1 hyu hinv₂ hnotz
  have hzyu : IsConj z (y * u) := hzy.trans (isConj_iff.2 ⟨s, hs⟩)
  exact h.final_block hy hzy hR ((h.lemma47 hF h1024).2 y hy).2.2.1 huR hu1 huz hu2 hyu hzyu

end Cfg1K

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
