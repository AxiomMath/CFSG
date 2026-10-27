module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCNSC
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Orbit

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitC

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

theorem qfV_e0 (ε : Eps) : qfV ε (Pi.single 0 1 : V6) = 0 := by
  have h := toVec_two_pow' (0 : Fin 6)
  simp only [Fin.val_zero, pow_zero] at h
  rw [← h, qfV_toVec ε (by norm_num), qfB_one]
  rfl

theorem e0_ne_zero : (Pi.single 0 1 : V6) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

namespace Setting

variable {ε : Eps} {t : G} {L H₀ U Q P S₀ : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hS : Setting ε t L H₀ U Q P S₀ a ψ p)
include hS

theorem isNSC_Q : IsNSC S₀ Q 64 where
  le := hS.Q_le_S₀
  normal := fun s hs f hf => (mem_normalizer_iff.1 (hS.data.le_normalizer hs) f).1 hf
  comm := fun _ hx _ hy => hS.rad.Q_comm hx hy
  mul_self := fun _ hx => hS.rad.Q_mul_self hx
  card_eq := hS.rad.card_Q
  self_centralizing := fun s hs hc => by
    have h1 : s ∈ Q ⊔ zpowers t := hS.data.centralizer_Q
      ⟨mem_centralizer_singleton_iff.2 (hS.shape.commute_of_mem (hS.data.S₀_le hs)),
        mem_centralizer_iff.2 fun q hq => (hc q hq).symm⟩
    rw [← hS.shape.sup_inf_eq hS.Q_le_H₀]
    exact ⟨h1, hS.data.S₀_le hs⟩

theorem eq_E_of (hU : ∀ F, IsNSC S₀ F 64 → F = Q) {F : Subgroup G}
    (hF : IsNSC (S₀ ⊔ zpowers t) F 128) (htF : t ∈ F) : F = Q ⊔ zpowers t := by
  have hS₀ := hS.data.S₀_le
  have hpart : ∀ f ∈ F, ∃ u ∈ F ⊓ S₀, f = u ∨ f = u * t := by
    intro f hf
    obtain ⟨u, hu, h | h⟩ := (hS.shape.mem_sup_iff hS₀).1 (hF.le hf)
    · exact ⟨u, ⟨h ▸ hf, hu⟩, Or.inl h⟩
    · have : u = f * t := by rw [h, mul_assoc, hS.shape.mul_self, mul_one]
      exact ⟨u, ⟨this ▸ F.mul_mem hf htF, hu⟩, Or.inr h⟩
  have hFeq : F = F ⊓ S₀ ⊔ zpowers t := by
    refine le_antisymm (fun f hf => ?_) (sup_le inf_le_left (zpowers_le.2 htF))
    obtain ⟨u, hu, h | h⟩ := hpart f hf
    · exact h ▸ mem_sup_left hu
    · exact h ▸ mul_mem (mem_sup_left hu) (mem_sup_right (mem_zpowers t))
  have hcard : Nat.card (F ⊓ S₀ : Subgroup G) = 64 := by
    have h := hS.shape.card_sup (inf_le_right.trans hS₀ : F ⊓ S₀ ≤ H₀)
    rw [← hFeq, hF.card_eq] at h
    omega
  have hF₀ : IsNSC S₀ (F ⊓ S₀) 64 := by
    refine ⟨inf_le_right, fun s hs f hf => ⟨hF.normal s (mem_sup_left hs) f hf.1,
      S₀.mul_mem (S₀.mul_mem hs hf.2) (S₀.inv_mem hs)⟩, fun x hx y hy => hF.comm x hx.1 y hy.1,
      fun x hx => hF.mul_self x hx.1, hcard, ?_⟩
    intro s hs hc
    refine ⟨hF.self_centralizing s (mem_sup_left hs) fun f hf => ?_, hs⟩
    have hst : s * t = t * s := hS.shape.commute_of_mem (hS₀ hs)
    obtain ⟨u, hu, h | h⟩ := hpart f hf
    · exact h ▸ hc u hu
    · rw [h, ← mul_assoc, hc u hu, mul_assoc, hst, mul_assoc]
  rw [hFeq, hU _ hF₀]

theorem exists_normalizer_E [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hU : ∀ F, IsNSC S₀ F 64 → F = Q) :
    ∃ n ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G), n * t * n⁻¹ = t * a := by
  obtain ⟨n, hnN, hnt⟩ := hS.exists_conj_eq_mul hG hnab
  set E : Subgroup G := Q ⊔ zpowers t with hE
  set TH : Subgroup G := S₀ ⊔ zpowers t with hTH
  set F : Subgroup G := E.map (MulAut.conj n⁻¹).toMonoidHom with hFdef
  have hmemF : ∀ {x : G}, x ∈ F ↔ n * x * n⁻¹ ∈ E := by
    intro x
    rw [hFdef, mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨n * x * n⁻¹, hx, by simp [mul_assoc]⟩
  have hTHn : ∀ x ∈ TH, n * x * n⁻¹ ∈ TH := fun x hx => (mem_normalizer_iff.1 hnN x).1 hx
  have hTHn' : ∀ x ∈ TH, n⁻¹ * x * n ∈ TH := fun x hx => by
    simpa using (mem_normalizer_iff.1 (inv_mem hnN) x).1 hx
  have hF : IsNSC TH F 128 := by
    refine ⟨fun _x hx => ?_, fun s hs f hf => ?_, fun x hx y hy => ?_, fun x hx => ?_, ?_, ?_⟩
    · have := hTHn' _ (hS.E_le_TH (hmemF.1 hx))
      simpa [mul_assoc] using this
    · rw [hmemF] at hf ⊢
      have h1 := (mem_normalizer_iff.1 (hS.TH_le_normalizer_E (hTHn s hs)) _).1 hf
      have e1 : n * (s * f * s⁻¹) * n⁻¹ = n * s * n⁻¹ * (n * f * n⁻¹) * (n * s * n⁻¹)⁻¹ := by
        group
      rw [e1]
      exact h1
    · have h1 := hS.E_comm (hmemF.1 hx) (hmemF.1 hy)
      have h2 : n * (x * y) * n⁻¹ = n * (y * x) * n⁻¹ := by
        calc n * (x * y) * n⁻¹ = n * x * n⁻¹ * (n * y * n⁻¹) := by group
          _ = n * y * n⁻¹ * (n * x * n⁻¹) := h1
          _ = n * (y * x) * n⁻¹ := by group
      simpa using h2
    · have h1 := hS.E_mul_self (hmemF.1 hx)
      have h2 : n * (x * x) * n⁻¹ = 1 := by
        calc n * (x * x) * n⁻¹ = n * x * n⁻¹ * (n * x * n⁻¹) := by group
          _ = 1 := h1
      simpa using h2
    · rw [hFdef, card_map_of_injective (MulAut.conj n⁻¹).injective, hS.card_E]
    · intro s hs hc
      rw [hmemF]
      have hcE := hS.centralizer_E
      rw [← hE] at hcE
      rw [← hcE]
      refine mem_centralizer_iff.2 fun y hy => ?_
      have hyF : n⁻¹ * y * n ∈ F := hmemF.2 (by simpa [mul_assoc] using hy)
      have h1 := hc _ hyF
      calc y * (n * s * n⁻¹) = n * ((n⁻¹ * y * n) * s) * n⁻¹ := by group
        _ = n * (s * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
        _ = n * s * n⁻¹ * y := by group
  have htF : t ∈ F := by
    rw [hmemF, hnt]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hS.rad.a_mem_Q)
  have hFE : F = E := hS.eq_E_of hU hF htF
  refine ⟨n, mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩, hnt⟩
  · have : x ∈ F := hFE ▸ hx
    exact hmemF.1 this
  · exact hFE ▸ hmemF.2 hx

theorem P_le_normalizer_E : P ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
  fun _ hx => mem_normalizer_sup (hS.rad.P_le_normalizer hx)
    (mem_normalizer_zpowers (hS.shape.commute_of_mem (hS.shape.L_le (hS.rad.P_le_L hx))))

theorem zero_mem_Zset : (0 : V6) ∈ Zset t Q ψ :=
  ⟨1, one_mem _, by rw [hS.rad.ψ_zero]; group⟩

theorem lin_mem_Zset {x : G} (hx : x ∈ P) {v : V6} (hv : v ∈ Zset t Q ψ) :
    lin ψ x v ∈ Zset t Q ψ := by
  obtain ⟨g, hg, hgt⟩ := hv
  refine ⟨x * g, mul_mem (hS.P_le_normalizer_E hx) hg, ?_⟩
  have hxt : x * t * x⁻¹ = t := by
    rw [hS.shape.commute_of_mem (hS.shape.L_le (hS.rad.P_le_L hx)), mul_inv_cancel_right]
  rw [hS.rad.ψ_lin (hS.rad.P_le_normalizer hx)]
  calc x * g * t * (x * g)⁻¹ = x * (g * t * g⁻¹) * x⁻¹ := by group
    _ = x * t * x⁻¹ * (x * ψ v * x⁻¹) := by rw [hgt]; group
    _ = t * (x * ψ v * x⁻¹) := by rw [hxt]

theorem mem_Zset_of {v w : V6} (hv : v ≠ 0) (hw : w ≠ 0) (h : qfV ε v = qfV ε w)
    (hvZ : v ∈ Zset t Q ψ) : w ∈ Zset t Q ψ := by
  obtain ⟨x, hx, rfl⟩ := hS.rad.exists_lin_eq hv hw h
  exact hS.lin_mem_Zset hx hvZ

theorem Zset_cases [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hU : ∀ F, IsNSC S₀ F 64 → F = Q) :
    (∀ v, v ∈ Zset t Q ψ ↔ qfV ε v = 0) ∨ ∀ v, v ∈ Zset t Q ψ := by
  have he0 : (Pi.single 0 1 : V6) ∈ Zset t Q ψ := by
    obtain ⟨n, hn, hnt⟩ := hS.exists_normalizer_E hG hnab hU
    exact ⟨n, hn, by rw [hnt, hS.rad.a_eq]⟩
  have hsing : ∀ v, qfV ε v = 0 → v ∈ Zset t Q ψ := by
    intro v hv
    by_cases h0 : v = 0
    · exact h0 ▸ hS.zero_mem_Zset
    · exact hS.mem_Zset_of e0_ne_zero h0 (by rw [qfV_e0, hv]) he0
  by_cases hN : ∃ w ∈ Zset t Q ψ, qfV ε w = 1
  · obtain ⟨w, hwZ, hw⟩ := hN
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [qfV_zero] at hw
      exact zero_ne_one hw
    refine Or.inr fun v => ?_
    rcases qfV_cases ε v with hv | hv
    · exact hsing v hv
    · have hv0 : v ≠ 0 := by
        rintro rfl
        rw [qfV_zero] at hv
        exact zero_ne_one hv
      exact hS.mem_Zset_of hw0 hv0 (by rw [hw, hv]) hwZ
  · push Not at hN
    refine Or.inl fun v => ⟨fun hv => ?_, hsing v⟩
    rcases qfV_cases ε v with h | h
    · exact h
    · exact absurd h (hN v hv)

end Setting

end CFSG.EvenSmallLie.OmegaEight.SplitC
