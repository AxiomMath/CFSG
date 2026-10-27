module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2Defs
public import CFSG.LocalAnalysis.OddStandard.ThmCO2Pre
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement

public section

namespace CFSG.OddStandard.ThmC.O2.Gor


open CFSG Subgroup

variable {Q : Type} [Group Q] [Finite Q]

theorem eq_top_of_normalizer_le_centralizer (hO : pPrimeCore 2 Q = ⊥) (R : Sylow 2 Q)
    (h : normalizer ((R : Subgroup Q) : Set Q) ≤ centralizer ((R : Subgroup Q) : Set Q)) :
    (R : Subgroup Q) = ⊤ := by
  have hS : (R : Subgroup Q) ≤ centerIn (Subgroup.normalizer (R : Subgroup Q)) := by
    intro s hs
    refine ⟨Subgroup.le_normalizer hs, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    exact (Subgroup.mem_centralizer_iff.mp (h hg) s hs).symm
  obtain ⟨N, hN, hcop, hquot⟩ :=
    exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer 2 R hS
  have hNle : N ≤ pPrimeCore 2 Q := le_sSup ⟨hN, hcop⟩
  have hNbot : N = ⊥ := le_bot_iff.1 (hO ▸ hNle)
  subst hNbot
  have hQ : IsPGroup 2 Q := by
    have e : Q ≃* Q ⧸ (⊥ : Subgroup Q) := (QuotientGroup.quotientBot).symm
    exact hquot.of_equiv e.symm
  have hTop : IsPGroup 2 (⊤ : Subgroup Q) := by
    intro x
    obtain ⟨n, hn⟩ := hQ x.1
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  exact (R.is_maximal' hTop le_top).symm

omit [Finite Q] in
theorem centralizer_normal (P : Subgroup Q) [P.Normal] : (centralizer (P : Set Q)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [mem_centralizer_iff] at hx ⊢
  intro p hp
  have h1 := hx (g⁻¹ * p * g) (by simpa using (inferInstance : P.Normal).conj_mem p hp g⁻¹)
  calc p * (g * x * g⁻¹) = g * ((g⁻¹ * p * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * p * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * p := by group

theorem normal_of_pCore_ne_bot (hO : pPrimeCore 2 Q = ⊥) (R : Sylow 2 Q)
    (habel : ∀ r ∈ (R : Subgroup Q), ∀ s ∈ (R : Subgroup Q), r * s = s * r)
    (hD : ∀ g ∈ normalizer ((R : Subgroup Q) : Set Q),
      (∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r) ∨
        (∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r → r = 1))
    (hP : pCore 2 Q ≠ ⊥) : (R : Subgroup Q).Normal := by
  set P : Subgroup Q := pCore 2 Q with hPdef
  have hPR : P ≤ R := IsPGroup.le_sylow_of_normal pCore_isPGroup R
  have : P.Normal := pCore_normal
  set Q₀ : Subgroup Q := centralizer (P : Set Q) with hQ₀
  have hQ₀n : Q₀.Normal := centralizer_normal P
  have hRQ₀ : (R : Subgroup Q) ≤ Q₀ := fun r hr =>
    mem_centralizer_iff.2 fun p hp => habel p (hPR hp) r hr
  have hO₀ : pPrimeCore 2 Q₀ = ⊥ := by
    have h1 : (pPrimeCore 2 Q₀).map Q₀.subtype = ⊥ := le_bot_iff.1 (hO ▸ pPrimeCore_normal_le Q₀)
    exact (Subgroup.map_injective (f := Q₀.subtype) Q₀.subtype_injective)
      (by rw [h1, Subgroup.map_bot])
  obtain ⟨p, hpP, hp1⟩ : ∃ p ∈ P, p ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hP ((Subgroup.eq_bot_iff_forall _).2 hcon)
  let R' : Sylow 2 Q₀ := R.subtype hRQ₀
  have hmemR' : ∀ x : Q₀, x ∈ (R' : Subgroup Q₀) ↔ (x : Q) ∈ (R : Subgroup Q) := fun x => by
    simp [R', Sylow.coe_subtype, Subgroup.mem_subgroupOf]
  have hgR : ∀ h ∈ normalizer ((R' : Subgroup Q₀) : Set Q₀), ∀ x ∈ (R : Subgroup Q),
      (h : Q) * x * (h : Q)⁻¹ ∈ (R : Subgroup Q) := by
    intro h hh x hx
    have := (Subgroup.mem_normalizer_iff.1 hh ⟨x, hRQ₀ hx⟩).1 ((hmemR' _).2 hx)
    exact (hmemR' _).1 this
  have hN : normalizer ((R' : Subgroup Q₀) : Set Q₀) ≤
      centralizer ((R' : Subgroup Q₀) : Set Q₀) := by
    intro g hg
    have hgn : (g : Q) ∈ normalizer ((R : Subgroup Q) : Set Q) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact hgR g hg x
      · intro hx
        have := hgR g⁻¹ (Subgroup.inv_mem _ hg) _ hx
        simpa [mul_assoc] using this
    rcases hD _ hgn with hc | hfpf
    · refine mem_centralizer_iff.2 fun x hx => ?_
      apply Subtype.ext
      have := hc (x : Q) ((hmemR' x).1 hx)
      simp only [Subgroup.coe_mul]
      calc (x : Q) * g = (g : Q) * x * (g : Q)⁻¹ * g := by rw [this]
        _ = g * x := by group
    · exfalso
      have hgp : (g : Q) * p * (g : Q)⁻¹ = p := by
        have := mem_centralizer_iff.1 g.2 p hpP
        rw [← this]; group
      exact hp1 (hfpf p (hPR hpP) hgp)
  have hTop := eq_top_of_normalizer_le_centralizer hO₀ R' hN
  have hQ₀R : Q₀ ≤ (R : Subgroup Q) := by
    intro x hx
    have : (⟨x, hx⟩ : Q₀) ∈ (R' : Subgroup Q₀) := by rw [hTop]; exact Subgroup.mem_top _
    exact (hmemR' _).1 this
  have hEq : (R : Subgroup Q) = Q₀ := le_antisymm (hRQ₀) hQ₀R |>.symm ▸ rfl
  rw [hEq]
  exact hQ₀n

@[expose] def Gor42Hard : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], pPrimeCore 2 Q = ⊥ → pCore 2 Q = ⊥ →
    ∀ R : Sylow 2 Q, Nat.card (R : Subgroup Q) = 16 → (∀ r ∈ (R : Subgroup Q), r * r = 1) →
      (∀ r ∈ (R : Subgroup Q), ∀ s ∈ (R : Subgroup Q), r * s = s * r) →
      (∀ g ∈ normalizer ((R : Subgroup Q) : Set Q),
        (∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r) ∨
          ((∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r → r = 1) ∧
            ∀ r ∈ (R : Subgroup Q), g ^ 3 * r * (g ^ 3)⁻¹ = r)) →
      normalizer ((R : Subgroup Q) : Set Q) ≤ centralizer ((R : Subgroup Q) : Set Q)

theorem gor42_of_hard (hH : Gor42Hard) : Gor42 := by
  intro Q _ _ hO R hcard hsq habel hD
  by_cases hN : normalizer ((R : Subgroup Q) : Set Q) ≤ centralizer ((R : Subgroup Q) : Set Q)
  · have := eq_top_of_normalizer_le_centralizer hO R hN
    rw [this]
    exact Subgroup.normal_top
  · by_cases hP : pCore 2 Q = ⊥
    · exact absurd (hH Q hO hP R hcard hsq habel hD) hN
    · exact normal_of_pCore_ne_bot hO R habel
        (fun g hg => (hD g hg).imp id (fun h => h.1)) hP

end CFSG.OddStandard.ThmC.O2.Gor
