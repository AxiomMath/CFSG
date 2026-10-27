module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoBYe
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoBF
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoBSplit

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HarrisLit (SectionalRankLeFour)
open CFSG.ComponentClassification.HSFLit (HaradaInput ElemAbelianTwo)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A] [Finite A]

namespace LocalDatum

variable {Δ : LocalDatum X A} {k : A} (h2 : Δ.CaseTwo k) {φ : Δ.Fusion}

namespace TwoBY

variable (YD : TwoBY φ)

include h2 in
theorem false_of_field_noncentral (hA : AutFacts Δ)
    (hbig : ¬ ∀ r ∈ Δ.R, r ∈ Δ.Dbar ∨ r * k ∈ Δ.Dbar) {y : X} (hy : y ∈ YD.Y) (hy1 : y ≠ 1)
    (hyt : y ≠ Δ.t) (hyz : y ≠ Δ.dz) (hytz : y ≠ Δ.t * Δ.dz) (hyD : Δ.ψe y ∉ Δ.Dbar)
    {d w₀ : X} (hd : d ∈ Δ.D) (hw₀S : w₀ ∈ Δ.S) (hyeq : y = d * w₀) (hw₀k : Δ.ψe w₀ = k)
    (hd2 : d ^ 2 = 1)
    (hcomm : ∀ g ∈ Δ.D, d * g * d⁻¹ * g⁻¹ = 1 ∨ d * g * d⁻¹ * g⁻¹ = Δ.dz)
    (hdz : ¬ (d = 1 ∨ d = Δ.dz)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 := h2.2.2.2.2.1
  have hD8 : Nat.card Δ.D = 8 := by
    have h16 : ¬ 16 ≤ Nat.card Δ.D := fun h => hdz (Δ.eq_of_comm_mod_dz h hd hd2 hcomm)
    obtain ⟨j, hj⟩ := (Δ.sylow.isPGroup.to_le Δ.D_le).exists_card_eq
    rw [hj] at h8 h16 ⊢
    have hj3 : 3 ≤ j := by
      by_contra h
      push Not at h
      have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hj4 : j < 4 := by
      by_contra h
      push Not at h
      have : 2 ^ 4 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h
      omega
    rw [show j = 3 by omega]
    norm_num
  obtain ⟨Tbar, hTR, hDT, -, -, h8c, hdih⟩ := hA.two k h2
  have hT : Tbar = Δ.Dbar := by
    by_contra hTne
    obtain ⟨m, ⟨e⟩⟩ := hdih hTne
    have hRp : IsPGroup 2 Δ.R :=
      Δ.sylow.isPGroup.of_surjective Δ.ψ.rangeRestrict Δ.ψ.rangeRestrict_surjective
    obtain ⟨hm, h8m⟩ := Tbar_facts e (hRp.to_le hTR) hDT hTne (by rw [Δ.card_Dbar]; exact h8)
    have hzS := Δ.D_le Δ.dz_mem
    set zb := Δ.ψe Δ.dz
    have hzR : ∀ s ∈ Δ.S, zb * Δ.ψe s = Δ.ψe s * zb := fun s hs => by
      rw [← Δ.ψe_mul hzS hs, ← Δ.ψe_mul hs hzS, Δ.dz_comm_S h8 hs]
    have hzT : zb ∈ Tbar := hDT (Δ.ψe_mem_Dbar Δ.dz_mem)
    have hzc : ∀ g ∈ Tbar, zb * g = g * zb := fun g hg => by
      obtain ⟨s, hs, rfl⟩ := (Δ.mem_R_iff).mp (hTR hg)
      exact hzR s hs
    have hz1 : zb ≠ 1 := fun h => Δ.dz_ne_one (Δ.eq_one_of_ψe Δ.dz_mem h)
    have hz2 : zb * zb = 1 := by
      rw [← Δ.ψe_mul hzS hzS, ← pow_two, Δ.dz_sq, Δ.ψe_one]
    have hzinv : zb⁻¹ = zb := inv_eq_of_mul_eq_one_right hz2
    have hdT : Δ.ψe d ∈ Tbar := hDT (Δ.ψe_mem_Dbar hd)
    have hdb2 : Δ.ψe d ^ 2 = 1 := by rw [← Δ.ψe_pow (Δ.D_le hd), hd2, Δ.ψe_one]
    have hyS := YD.le_S hy
    have he : Δ.ψe y = Δ.ψe d * k := by rw [hyeq, Δ.ψe_mul (Δ.D_le hd) hw₀S, hw₀k]
    have hzk : zb * k = k * zb := by rw [← hw₀k]; exact hzR w₀ hw₀S
    have hzd : zb * Δ.ψe d = Δ.ψe d * zb := hzR d (Δ.D_le hd)
    have hc : ∀ g ∈ Tbar, Δ.ψe d * g * (Δ.ψe d)⁻¹ * g⁻¹ = 1 ∨
        Δ.ψe d * g * (Δ.ψe d)⁻¹ * g⁻¹ = zb := by
      intro g hg
      obtain ⟨s, hs, rfl⟩ := (Δ.mem_R_iff).mp (hTR hg)
      set g := Δ.ψe s
      have hconj : g * Δ.ψe y * g⁻¹ = Δ.ψe y ∨ g * Δ.ψe y * g⁻¹ = zb * Δ.ψe y := by
        rcases YD.ψe_cases hy hy1 hyt hyz hytz (YD.conj_S hs hy) with h | h | h | h <;>
          rw [Δ.ψe_conj hs hyS] at h
        · exfalso
          apply hyD
          have : Δ.ψe y = g⁻¹ * (g * Δ.ψe y * g⁻¹) * g := by group
          rw [this, h]
          simp
        · exfalso
          apply hyD
          have : Δ.ψe y = g⁻¹ * (g * Δ.ψe y * g⁻¹) * g := by group
          rw [this, h, mul_assoc, hzR s hs, ← mul_assoc, inv_mul_cancel, one_mul]
          exact Δ.ψe_mem_Dbar Δ.dz_mem
        · exact Or.inl h
        · exact Or.inr h
      have hdbar : Δ.ψe d = Δ.ψe y * k⁻¹ := by rw [he]; group
      have hgd : g * Δ.ψe d * g⁻¹ = (g * Δ.ψe y * g⁻¹) * (g * k * g⁻¹)⁻¹ := by
        rw [hdbar]; group
      have hfin : g * Δ.ψe d * g⁻¹ = Δ.ψe d ∨ g * Δ.ψe d * g⁻¹ = Δ.ψe d * zb := by
        have hza : zb * Δ.ψe y = Δ.ψe y * zb := hzR y hyS
        have hzki : zb * k⁻¹ = k⁻¹ * zb := by
          calc zb * k⁻¹ = k⁻¹ * (k * zb) * k⁻¹ := by group
            _ = k⁻¹ * (zb * k) * k⁻¹ := by rw [hzk]
            _ = k⁻¹ * zb := by group
        rw [hgd]
        rcases hconj with h | h <;> rcases Δ.conj_k h2 hs with h' | h' <;> rw [h, h']
        · exact Or.inl hdbar.symm
        · right
          rw [hdbar, mul_inv_rev, hzinv]
          group
        · right
          rw [hdbar, hza, mul_assoc, hzki, ← mul_assoc]
        · left
          rw [hdbar, mul_inv_rev, hzinv]
          calc zb * Δ.ψe y * (k⁻¹ * zb) = Δ.ψe y * (zb * k⁻¹) * zb := by
                rw [hza]; group
              _ = Δ.ψe y * k⁻¹ * (zb * zb) := by rw [hzki]; group
              _ = Δ.ψe y * k⁻¹ := by rw [hz2, mul_one]
      have hinv : Δ.ψe d * g * (Δ.ψe d)⁻¹ * g⁻¹ = Δ.ψe d * (g * Δ.ψe d * g⁻¹)⁻¹ := by group
      rcases hfin with h | h
      · left; rw [hinv, h, mul_inv_cancel]
      · right; rw [hinv, h, mul_inv_rev, hzinv, ← mul_assoc, ← hzd, mul_inv_cancel_right]
    rcases Tbar_eq_of_comm_mod e hm h8m hzT hzc hz1 hdT hdb2 hc with h | h
    · exact hdz (Or.inl (Δ.eq_one_of_ψe hd h))
    · exact hdz (Or.inr (Δ.eq_of_ψe_eq hd Δ.dz_mem h))
  exact hbig fun r hr => by
    rcases h8c hD8 r hr with h | h
    · exact Or.inl (hT ▸ h)
    · exact Or.inr (hT ▸ h)

end TwoBY

include h2 in
theorem TwoB_false_of_big
    (hA : AutFacts Δ) (hX : ¬ SectionalRankLeFour X) (φ : Δ.Fusion)
    (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1)
    (hbig : ¬ ∀ r ∈ Δ.R, r ∈ Δ.Dbar ∨ r * k ∈ Δ.Dbar) : False := by
  classical
  obtain ⟨YD⟩ := exists_TwoBY h2 φ hX hD1
  obtain ⟨y, hyY, hy1, hyt, hyz, hytz⟩ : ∃ y ∈ YD.Y, y ≠ 1 ∧ y ≠ Δ.t ∧ y ≠ Δ.dz ∧
      y ≠ Δ.t * Δ.dz := by
    by_contra hno
    push Not at hno
    have := card_le_of_forall_mem_finset YD.Y {1, Δ.t, Δ.dz, Δ.t * Δ.dz} fun y hy => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h1 : y = 1
      · exact Or.inl h1
      by_cases h2' : y = Δ.t
      · exact Or.inr (Or.inl h2')
      by_cases h3 : y = Δ.dz
      · exact Or.inr (Or.inr (Or.inl h3))
      exact Or.inr (Or.inr (Or.inr (hno y hy h1 h2' h3)))
    have := this.trans Finset.card_le_four
    rw [YD.card] at this
    omega
  have hyS := YD.le_S hyY
  by_cases hyD : Δ.ψe y ∈ Δ.Dbar
  · exact YD.false_of_Dbar h2 hD1 hyY hy1 hyt hyz hytz hyD
  obtain ⟨Tbar, hTR, hDT, hinv, -, -, hdih⟩ := hA.two k h2
  have hy2 : Δ.ψe y ^ 2 = 1 := by rw [← Δ.ψe_pow hyS, YD.elem.sq_eq_one y hyY, Δ.ψe_one]
  rcases hinv _ (Δ.ψe_mem_R hyS) hy2 with hyT | hyk
  · have hTne : Tbar ≠ Δ.Dbar := fun h => hyD (h ▸ hyT)
    obtain ⟨m, ⟨e⟩⟩ := hdih hTne
    have hRp : IsPGroup 2 Δ.R :=
      Δ.sylow.isPGroup.of_surjective Δ.ψ.rangeRestrict Δ.ψ.rangeRestrict_surjective
    obtain ⟨hm, h8m⟩ := Tbar_facts e (hRp.to_le hTR) hDT hTne
      (by rw [Δ.card_Dbar]; exact h2.2.2.2.2.1)
    exact YD.false_of_Tbar h2 e hm h8m hTR hDT hyY hy1 hyt hyz hytz hyT hyD
  · obtain ⟨d, hd, w₀, hw₀S, hyeq, hw₀D, hw₀k, hd2, hcomm⟩ :=
      YD.field_decomp h2 hyY hy1 hyt hyz hytz hyk
    by_cases hdz : d = 1 ∨ d = Δ.dz
    · exact YD.false_of_field_central h2 hD1 hyY hy1 hyt hyz hytz hd hw₀S hyeq hw₀D hw₀k hdz hyD
    · exact YD.false_of_field_noncentral h2 hA hbig hyY hy1 hyt hyz hytz hyD hd hw₀S hyeq hw₀k
        hd2 hcomm hdz

include h2 in
theorem TwoB_false
    (hH : HaradaInput) (hA : AutFacts Δ) (hX : ¬ SectionalRankLeFour X) (φ : Δ.Fusion)
    (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1) : False := by
  by_cases hsplit : ∀ r ∈ Δ.R, r ∈ Δ.Dbar ∨ r * k ∈ Δ.Dbar
  · obtain ⟨d₀, hd₀, hsq⟩ := TwoB_sq_decomp h2 φ hD1 hsplit
    exact (⟨d₀, hd₀, hsq, h2.2.2.2.2.1, hD1, TwoB_conj_dz h2 φ hD1, TwoB_conj_t h2 φ hD1,
      fun s hs => TwoB_decomp h2 φ hD1 hsplit hs⟩ : TwoBSplit φ).false_of_harada_split hH hX
  · exact TwoB_false_of_big h2 hA hX φ hD1 hsplit

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
