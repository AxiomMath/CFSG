module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Phase1
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Swap

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Ctx3

variable {x : G} {T V H : Subgroup G} {f : G} (c : Ctx3 G x T V H f)
include c

theorem phase2_abel [Finite G] {n : ℕ} (e : ↥(Hzero H f) ≃* Z2n2 n)
    (hP16 : Nat.card (Hzero H f) = 16) (hSyl : Sylow2In (H ⊔ T) ⊤)
    (hPn : ∀ s ∈ H ⊔ T, ∀ q ∈ Hzero H f, s * q * s⁻¹ ∈ Hzero H f)
    (hrel : (Hzero H f).relIndex (H ⊔ T) = 4) (hsq : ∀ s ∈ H ⊔ T, s * s ∈ Hzero H f)
    {w : G} (hwS : w * x * w⁻¹ ∈ H ⊔ T) (hwH : w * x * w⁻¹ ∉ H)
    (hY : YCtx (Hzero H f) V (w * x * w⁻¹)) :
    Sylow2In (H ⊔ T) ⊤ ∧ (∀ s ∈ H ⊔ T, ∀ h ∈ Hzero H f, s * h * s⁻¹ ∈ Hzero H f) ∧
      Hzero H f ≤ H ⊔ T ∧ (Hzero H f).relIndex (H ⊔ T) = 4 ∧
      (∀ s ∈ H ⊔ T, s * s ∈ Hzero H f) ∧
      (H ⊔ T) ⊓ centralizer ((Hzero H f : Subgroup G) : Set G) = Hzero H f ∧
      Nonempty (↥(Hzero H f) ≃* Z2n2 2) ∧
      ∃ g : G, g * x * g⁻¹ ∈ H ⊔ T ∧ IsZ4WrZ2 (Hzero H f) (g * x * g⁻¹) ∧
        x ∉ Hzero H f ⊔ zpowers (g * x * g⁻¹) := by
  have hPcard : Nat.card (Hzero H f) = 4 ^ n := by rw [Nat.card_congr e.toEquiv, card_Z2n2]
  have hn2 : n = 2 := by
    have : 4 ^ n = 4 ^ 2 := by rw [← hPcard, hP16]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) this
  subst hn2
  have hP : ∀ a ∈ Hzero H f, ∀ b ∈ Hzero H f, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (comm_of_equiv_comm e ⟨a, ha⟩ ⟨b, hb⟩)
  have hPS : Hzero H f ≤ H ⊔ T := c.H0_le.trans le_sup_left
  have hV4 : Nat.card V = 4 := c.out.V_four.2
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => c.out.V_sq hv
  have hy2 : (w * x * w⁻¹) * (w * x * w⁻¹) = 1 := hY.sq
  refine ⟨hSyl, hPn, hPS, hrel, hsq, ?_, ⟨e⟩, w, hwS, ?_, ?_⟩
  ·
    apply le_antisymm
    · rintro s ⟨hsS, hsC⟩
      by_contra hsP
      by_cases hsH : s ∈ H
      · obtain ⟨q, hq, h1 | h1⟩ := (c.mem_H_iff).1 hsH
        · exact hsP (h1 ▸ hq)
        ·
          have hxC : x ∈ centralizer ((Hzero H f : Subgroup G) : Set G) := by
            rw [mem_centralizer_iff]
            intro a ha
            have hs' := mem_centralizer_iff.1 hsC a ha
            have hq' := hP a ha q hq
            have e1 : x = q⁻¹ * s := by rw [h1]; group
            rw [e1]
            calc a * (q⁻¹ * s) = (a * q⁻¹) * s := by group
              _ = (q⁻¹ * a) * s := by rw [(hP a ha q⁻¹ ((Hzero H f).inv_mem hq))]
              _ = q⁻¹ * (a * s) := by group
              _ = q⁻¹ * (s * a) := by rw [hs']
              _ = (q⁻¹ * s) * a := by group
          have hle : Hzero H f ≤ V := by
            intro a ha
            rw [← c.C_H0_x]
            refine ⟨ha, ?_⟩
            show a ∈ centralizer ({x} : Set G)
            rw [mem_centralizer_iff]
            intro z hz
            rw [Set.mem_singleton_iff] at hz
            rw [hz]
            exact (mem_centralizer_iff.1 hxC a ha).symm
          have := Subgroup.card_le_of_le hle
          rw [hP16, hV4] at this
          omega
      ·
        have hsV : s ∈ centralizer (V : Set G) := by
          rw [mem_centralizer_iff]
          intro v hv
          exact mem_centralizer_iff.1 hsC v (c.V_le_H0 hv)
        have : s ∈ (H ⊔ T) ⊓ centralizer (V : Set G) := ⟨hsS, hsV⟩
        rw [c.Hstar_inf_C] at this
        exact hsH this
    · intro p hp
      refine ⟨hPS hp, ?_⟩
      show p ∈ centralizer ((Hzero H f : Subgroup G) : Set G)
      rw [mem_centralizer_iff]
      intro a ha
      exact hP a ha p hp
  ·
    have hVO : V = Om (Hzero H f) hP 1 :=
      Om_one_eq hP (by norm_num) e c.V_le_H0 hV4 hVsq
    obtain ⟨a, b, haP, hbP, ha4, hb4, hab, hcl, hya, hyb⟩ :=
      exists_swap_basis hP e hVO hy2 hY.yP hV4 hY.moved
    refine ⟨fun h => hwH (c.H0_le h), hy2, hP16, a, b, haP, hbP, ha4, hb4, hab, hcl, hya, hyb⟩
  ·
    intro hx
    obtain ⟨q, hq, h1 | h1⟩ := (mem_sup_zpowers_invol hy2 (fun q hq => hPn _ hwS q hq)).1 hx
    · exact c.x_notin_H0 (h1 ▸ hq)
    · apply hwH
      have : w * x * w⁻¹ = q⁻¹ * x := by
        have e1 : w * x * w⁻¹ = q⁻¹ * (q * (w * x * w⁻¹)) := by group
        rw [e1, ← h1]
      rw [this]
      exact H.mul_mem (H.inv_mem (c.H0_le hq)) c.x_mem_H

end Ctx3

theorem lemma13_3 (h9 : IG_9_16) (h10 : IG_10_31) (h15 : IG_15_15) : Lemma13_3 := by
  intro G _ _ x T V H f hout hc hp hne
  have c : Ctx3 G x T V H f := ⟨hout, hc, hp⟩
  have hV4 : Nat.card V = 4 := hout.V_four.2
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => hout.V_sq hv
  have hVP : V ≤ Hzero H f := c.V_le_H0
  have hVc : ∀ v ∈ V, ∀ a ∈ Hzero H f, v * a = a * v := c.V_central
  rcases hc.c_type with h1 | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact absurd h1 hne
  ·
    have hY : YFacts V (Hzero H f) := yfacts_abel hn e hVP hV4 hVsq
    have hchain : ∀ (y : G) (S : Subgroup G), YCtx (Hzero H f) V y → Hzero H f ≤ S → y ∈ S →
        y ∉ Hzero H f → (∀ s ∈ S, ∀ n ∈ V ⊓ centralizer ({y} : Set G), s * n * s⁻¹ = n) →
        Nat.card ↥(S ⊓ centralizer ({y} : Set G)) ≤ 16 →
        ∃ (n : ℕ) (Pi : ℕ → Subgroup G), Pi 0 = ⊥ ∧ Pi n = Hzero H f ∧
          ∀ i < n, FreeSec2 y (Pi i) (Pi (i + 1)) := by
      intro y S hY' _ _ _ _ _
      obtain ⟨Pi, h0, hn', hf⟩ := abel_chain (by omega : 1 ≤ n) e hVP hV4 hVsq hY'.sq hY'.yP
        hY'.moved
      exact ⟨n, Pi, h0, hn', hf⟩
    obtain ⟨hSyl, hPn, hrel, hsq, hP16, w, hwS, hwH, hY'⟩ := c.phase1 h9 h10 h15 hY hchain
    exact c.phase2_abel e hP16 hSyl hPn hrel hsq hwS hwH hY'
  ·
    exfalso
    have hF : NabFacts (Hzero H f) := NabFacts.of_model (NabModel.of_equiv e nabModel_UT3)
    have hY : YFacts V (Hzero H f) := hF.yfacts hVP hV4 hVsq hVc
    have hchain : ∀ (y : G) (S : Subgroup G), YCtx (Hzero H f) V y → Hzero H f ≤ S → y ∈ S →
        y ∉ Hzero H f → (∀ s ∈ S, ∀ n ∈ V ⊓ centralizer ({y} : Set G), s * n * s⁻¹ = n) →
        Nat.card ↥(S ⊓ centralizer ({y} : Set G)) ≤ 16 →
        ∃ (n : ℕ) (Pi : ℕ → Subgroup G), Pi 0 = ⊥ ∧ Pi n = Hzero H f ∧
          ∀ i < n, FreeSec2 y (Pi i) (Pi (i + 1)) := by
      intro y S hY' hPS hyS hyP' hSZ hSy
      obtain ⟨Pi, h0, h2, hf⟩ := hF.chain hVP hV4 hVsq hVc hY' h9 hPS hyS hyP' hSZ hSy
      exact ⟨2, Pi, h0, h2, hf⟩
    obtain ⟨-, -, -, -, hP16, -⟩ := c.phase1 h9 h10 h15 hY hchain
    have := hF.card
    omega
  ·
    exfalso
    have hF : NabFacts (Hzero H f) := NabFacts.of_model (NabModel.of_equiv e nabModel_Syl)
    have hY : YFacts V (Hzero H f) := hF.yfacts hVP hV4 hVsq hVc
    have hchain : ∀ (y : G) (S : Subgroup G), YCtx (Hzero H f) V y → Hzero H f ≤ S → y ∈ S →
        y ∉ Hzero H f → (∀ s ∈ S, ∀ n ∈ V ⊓ centralizer ({y} : Set G), s * n * s⁻¹ = n) →
        Nat.card ↥(S ⊓ centralizer ({y} : Set G)) ≤ 16 →
        ∃ (n : ℕ) (Pi : ℕ → Subgroup G), Pi 0 = ⊥ ∧ Pi n = Hzero H f ∧
          ∀ i < n, FreeSec2 y (Pi i) (Pi (i + 1)) := by
      intro y S hY' hPS hyS hyP' hSZ hSy
      obtain ⟨Pi, h0, h2, hf⟩ := hF.chain hVP hV4 hVsq hVc hY' h9 hPS hyS hyP' hSZ hSy
      exact ⟨2, Pi, h0, h2, hf⟩
    obtain ⟨-, -, -, -, hP16, -⟩ := c.phase1 h9 h10 h15 hY hchain
    have := hF.card
    omega

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
