module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreMacW
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoA

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HarrisLit (SectionalRankLeFour)
open CFSG.ComponentClassification.HSFLit (ElemAbelianTwo)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A] [Finite A]

namespace LocalDatum

variable {Δ : LocalDatum X A} {k : A} (h2 : Δ.CaseTwo k) (φ : Δ.Fusion)

include h2 φ in
theorem TwoA_false_of_sigma (hA : AutFacts Δ) (hX : ¬ SectionalRankLeFour X)
    (hxt : φ.x * Δ.t * φ.x⁻¹ = Δ.t * Δ.dz) (hxz : φ.x * Δ.dz * φ.x⁻¹ = Δ.dz)
    (hQ : ∀ q ∈ Δ.Q, q = 1 ∨ q = Δ.t) {c : X} (hcS : c ∈ Δ.S)
    (hcD : ∀ d ∈ Δ.D, c * d = d * c) (hct : c ^ 2 = Δ.t) {σ : X} (hσS : σ ∈ Δ.S)
    (hσ2 : σ ^ 2 = 1) (hσD : Δ.ψe σ ∉ Δ.Dbar) : False := by
  classical
  have hD8 := h2.2.2.2.2.1
  obtain ⟨Tbar, hTR, hDT, hinv, hnc, -, hdih⟩ := hA.two k h2
  have himT : ∀ s ∈ Δ.S, s ^ 2 = 1 → Δ.ψe s ∈ Tbar := fun s hs hs2 =>
    (hinv _ (Δ.ψe_mem_R hs) (by rw [← Δ.ψe_pow hs, hs2, Δ.ψe_one])).resolve_right
      (TwoA_no_inv h2 hQ hcS hcD hct hs hs2)
  have hσT := himT σ hσS hσ2
  have hTne : Tbar ≠ Δ.Dbar := fun h => hσD (h ▸ hσT)
  obtain ⟨m, ⟨e⟩⟩ := hdih hTne
  have hRp : IsPGroup 2 Δ.R :=
    Δ.sylow.isPGroup.of_surjective Δ.ψ.rangeRestrict Δ.ψ.rangeRestrict_surjective
  obtain ⟨hm, h8⟩ := Tbar_facts e (hRp.to_le hTR) hDT hTne (by rw [Δ.card_Dbar]; exact hD8)
  have hzS := Δ.D_le Δ.dz_mem
  have hcen : ∀ u ∈ Δ.S, (∀ s ∈ Δ.S, s * u = u * s) → φ.x * u * φ.x⁻¹ = u →
      u = 1 ∨ u = Δ.dz := by
    intro u hu huc hux
    have huD : ∀ d ∈ Δ.D, u * d = d * u := fun d hd => (huc d (Δ.D_le hd)).symm
    rcases h2.2.2.2.2.2 _ (Δ.ψe_mem_R hu) (Δ.commute_Dbar hu huD) with h | h
    · obtain ⟨q, hq, hcq⟩ := Δ.mem_Qz_of_centralizes hD8 hu huD h
      rcases hQ q hq with rfl | rfl
      · rcases hcq with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (one_mul _)
      · exfalso
        rcases hcq with rfl | rfl
        · rw [hxt] at hux
          exact Δ.dz_ne_one (by simpa using hux)
        · have : φ.x * (Δ.t * Δ.dz) * φ.x⁻¹ = Δ.t := by
            calc φ.x * (Δ.t * Δ.dz) * φ.x⁻¹ = φ.x * Δ.t * φ.x⁻¹ * (φ.x * Δ.dz * φ.x⁻¹) := by
                  group
              _ = Δ.t := by rw [hxt, hxz, mul_assoc, ← pow_two, Δ.dz_sq, mul_one]
          rw [this] at hux
          exact Δ.dz_ne_one (by simpa using hux.symm)
    · exfalso
      have hec : ∀ d ∈ Δ.Dbar, Δ.ψe u * k * d = d * (Δ.ψe u * k) := fun d hd => by
        rw [mul_assoc, h2.2.1 d hd, ← mul_assoc, Δ.commute_Dbar hu huD d hd, mul_assoc]
      have hσu : Commute (Δ.ψe σ) (Δ.ψe u) := by
        change Δ.ψe σ * Δ.ψe u = Δ.ψe u * Δ.ψe σ
        rw [← Δ.ψe_mul hσS hu, ← Δ.ψe_mul hu hσS, huc σ hσS]
      have hσe : Commute (Δ.ψe σ) (Δ.ψe u * k) := by
        change Δ.ψe σ * (Δ.ψe u * k) = Δ.ψe u * k * Δ.ψe σ
        rcases Δ.eq_of_central_Dbar hD8 h hec with h' | h'
        · rw [h', one_mul, mul_one]
        · rw [h', ← Δ.ψe_mul hσS hzS, ← Δ.ψe_mul hzS hσS, Δ.dz_comm_S hD8 hσS]
      have hk : (Δ.ψe u)⁻¹ * (Δ.ψe u * k) = k := by group
      have := hσu.inv_right.mul_right hσe
      rw [hk] at this
      exact hnc _ hσT hσD this
  obtain ⟨Y, hYT, hYn, hYel, hY8, v, hvY, hv1, hvS, hvc, hvx⟩ := φ.exists_Y hX
  have hzY : Δ.dz ∈ Y := by
    rcases hcen v hvS hvc hvx with h | h
    · exact absurd h hv1
    · exact h ▸ hvY
  have hC := four_le_card_fix hYel hY8 (fun y hy => hYn _ (φ.le Δ.t_mem) y hy) Δ.t_sq
  have hCS : ∀ y ∈ Y, y * Δ.t = Δ.t * y → y ∈ Δ.S := fun y hy hyt =>
    Δ.mem_S_of_commute_t φ.isPGroup φ.le (hYT hy) hyt
  have hex : ∃ y ∈ Y, y ∈ Δ.S ∧ y ≠ 1 ∧ y ≠ Δ.t ∧ y ≠ Δ.dz ∧ y ≠ Δ.t * Δ.dz := by
    by_contra hno
    push Not at hno
    by_cases htY : Δ.t ∈ Y
    · have := card_le_of_forall_mem_finset Y {1, Δ.t, Δ.dz, Δ.t * Δ.dz} fun y hy => by
        have hyS := hCS y hy (hYel.comm y hy _ htY)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases h1 : y = 1
        · exact Or.inl h1
        by_cases h2 : y = Δ.t
        · exact Or.inr (Or.inl h2)
        by_cases h3 : y = Δ.dz
        · exact Or.inr (Or.inr (Or.inl h3))
        exact Or.inr (Or.inr (Or.inr (hno y hy hyS h1 h2 h3)))
      have := this.trans Finset.card_le_four
      omega
    · have htzY : Δ.t * Δ.dz ∉ Y := fun h => htY (by
        have := hYn _ (inv_mem φ.mem) _ h
        rwa [show φ.x⁻¹ * (Δ.t * Δ.dz) * φ.x⁻¹⁻¹ = Δ.t by
          rw [← hxt]; group] at this)
      have := card_le_of_forall_mem_finset (Y ⊓ centralizer ({Δ.t} : Set X)) {1, Δ.dz}
        fun y hy => by
          obtain ⟨hyY, hyC⟩ := mem_inf.mp hy
          have hyS := hCS y hyY (mem_centralizer_singleton_iff.mp hyC)
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_cases h1 : y = 1
          · exact Or.inl h1
          by_cases h3 : y = Δ.dz
          · exact Or.inr h3
          exfalso
          by_cases h2 : y = Δ.t
          · exact htY (h2 ▸ hyY)
          exact htzY (hno y hyY hyS h1 h2 h3 ▸ hyY)
      have := this.trans Finset.card_le_two
      omega
  obtain ⟨y, hyY, hyS, hy1, hyt, hyz, hytz⟩ := hex
  have hψy1 : Δ.ψe y ≠ 1 := fun h => by
    rcases hQ y ((Δ.mem_Q_iff).mpr ⟨hyS, h⟩) with h' | h'
    · exact hy1 h'
    · exact hyt h'
  have hψyz : Δ.ψe y ≠ Δ.ψe Δ.dz := fun h => by
    have hq : y * Δ.dz⁻¹ ∈ Δ.Q := (Δ.mem_Q_iff).mpr ⟨mul_mem hyS (inv_mem hzS), by
      rw [Δ.ψe_mul hyS (inv_mem hzS), Δ.ψe_inv hzS, h, mul_inv_cancel]⟩
    rcases hQ _ hq with h' | h'
    · exact hyz (by
        calc y = y * Δ.dz⁻¹ * Δ.dz := by group
          _ = Δ.dz := by rw [h', one_mul])
    · exact hytz (by
        calc y = y * Δ.dz⁻¹ * Δ.dz := by group
          _ = Δ.t * Δ.dz := by rw [h'])
  refine false_of_normal_elem h2 e hm h8 hTR hDT (Y' := Y ⊓ Δ.S) inf_le_right
    (fun s hs y' hy' => mem_inf.mpr ⟨hYn s (φ.le hs) y' (mem_inf.mp hy').1,
      mul_mem (mul_mem hs (mem_inf.mp hy').2) (inv_mem hs)⟩)
    ⟨fun a ha b hb => hYel.comm a (mem_inf.mp ha).1 b (mem_inf.mp hb).1,
      fun a ha => hYel.sq_eq_one a (mem_inf.mp ha).1⟩
    (fun y' hy' => himT y' (mem_inf.mp hy').2 (hYel.sq_eq_one y' (mem_inf.mp hy').1))
    (mem_inf.mpr ⟨hzY, hzS⟩) (mem_inf.mpr ⟨hyY, hyS⟩) hψy1 hψyz

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
