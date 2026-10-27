module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxQuot
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxGroupB
public import CFSG.LocalAnalysis.GLTheoremB.LayerTools

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {Y : Type} [Group Y] [Finite Y] {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} [Fact p.Prime]

section Helpers

theorem normalizer_le_normalizer_centralizer' {Q : Type*} [Group Q] (A : Subgroup Q) :
    Subgroup.normalizer (A : Set Q) ≤ Subgroup.normalizer (Subgroup.centralizer (A : Set Q) : Set Q) := by
  intro g hg
  have key : ∀ g ∈ Subgroup.normalizer (A : Set Q), ∀ x ∈ Subgroup.centralizer (A : Set Q),
      g * x * g⁻¹ ∈ Subgroup.centralizer (A : Set Q) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : g⁻¹ * a * g ∈ A := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) a).1 ha
      simpa using this
    have h2 := (Subgroup.mem_centralizer_iff.1 hx) _ h1
    calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [← h2]
      _ = g * x * g⁻¹ * a := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem map_eq_of_map_le {Q : Type*} [Group Q] {Γ : Type*} [Group Γ] (σ : Γ →* MulAut Q)
    (A : Subgroup Q) (h : ∀ γ, A.map (σ γ).toMonoidHom ≤ A) : ∀ γ, A.map (σ γ).toMonoidHom = A := by
  intro γ
  refine le_antisymm (h γ) ?_
  intro a ha
  have h1 : (σ γ⁻¹) a ∈ A := by
    have := (h γ⁻¹) ⟨a, ha, rfl⟩
    exact this
  refine ⟨(σ γ⁻¹) a, h1, ?_⟩
  show (σ γ) ((σ γ⁻¹) a) = a
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem map_centralizer_le {Q : Type*} [Group Q] {Γ : Type*} [Group Γ] (σ : Γ →* MulAut Q)
    (A : Subgroup Q) (h : ∀ γ, A.map (σ γ).toMonoidHom = A) (γ : Γ) :
    (Subgroup.centralizer (A : Set Q)).map (σ γ).toMonoidHom ≤
      Subgroup.centralizer (A : Set Q) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : y ∈ A.map (σ γ).toMonoidHom := by rw [h γ]; exact hy
  obtain ⟨y', hy', rfl⟩ := hy'
  have := (Subgroup.mem_centralizer_iff.1 hx) y' hy'
  show (σ γ) y' * (σ γ) x = (σ γ) x * (σ γ) y'
  rw [← map_mul, ← map_mul, this]

theorem map_iSup_of_mem {Q : Type*} [Group Q] {Γ : Type*} [Group Γ] (σ : Γ →* MulAut Q)
    (ℒ : Set (Subgroup Q)) (hst : ∀ γ : Γ, ∀ K ∈ ℒ, K.map (σ γ).toMonoidHom ∈ ℒ) (γ : Γ) :
    (⨆ K ∈ ℒ, K : Subgroup Q).map (σ γ).toMonoidHom ≤ (⨆ K ∈ ℒ, K : Subgroup Q) := by
  rw [Subgroup.map_iSup]
  refine iSup_le fun K => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hK => ?_
  exact le_iSup₂_of_le _ (hst γ K hK) le_rfl

theorem layer_sup_pCore_le_normalizer {Q : Type} [Group Q] [Finite Q] (p : ℕ) [Fact p.Prime]
    (ℒ : Set (Subgroup Q)) (hℒ : ∀ K ∈ ℒ, IsComponentOf K ⊤) :
    CFSG.ComponentClassification.Layer.subgroup Q ⊔ CFSG.Open.pCore p Q ≤
      Subgroup.normalizer ((⨆ K ∈ ℒ, K : Subgroup Q) : Set Q) := by
  set A : Subgroup Q := ⨆ K ∈ ℒ, K with hA
  have hAE : A ≤ CFSG.ComponentClassification.Layer.subgroup Q :=
    iSup₂_le fun K hK => CFSG.ComponentClassification.Layer.component_le (hℒ K hK)
  refine sup_le ?_ ?_
  · refine sSup_le fun K hK => ?_
    by_cases hK𝒜 : K ∈ ℒ
    · exact (le_iSup₂_of_le K hK𝒜 le_rfl : K ≤ A).trans Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (A : Set Q))
      refine Subgroup.le_centralizer_iff.2 (iSup₂_le fun K' hK' => ?_)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne K' K (hℒ K' hK') hK
          (fun h => hK𝒜 (h ▸ hK')))
  · have hPn : (CFSG.Open.pCore p Q).Normal := CFSG.LieType.BorelTits.pCore_normal p
    have hPp : IsPGroup p (CFSG.Open.pCore p Q) :=
      CFSG.LieType.BorelTits.pCore_isPGroup (G := Q) p
    have : Group.IsNilpotent ↥(CFSG.Open.pCore p Q) := hPp.isNilpotent
    have : Group.IsSolvable ↥(CFSG.Open.pCore p Q) := inferInstance
    have hsub : IsSubnormal (CFSG.Open.pCore p Q) ⊤ := isSubnormal_of_normal hPn
    have h0 := CFSG.ComponentClassification.Layer.commutes_with_solvable_subnormal
      (CFSG.Open.pCore p Q) hsub
    have h1 : CFSG.Open.pCore p Q ≤ Subgroup.centralizer
        ((CFSG.ComponentClassification.Layer.subgroup Q : Subgroup Q) : Set Q) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]; exact h0
    exact h1.trans ((Subgroup.centralizer_le hAE).trans (Subgroup.centralizer_le_normalizer _))

end Helpers

theorem key_centralizer_eq_bot (hΓ : IsPGroup p Γ) (ρ : Γ →* MulAut Y) (hY : ¬ p ∣ Nat.card Y)
    (hS2 : ∀ S : Subgroup Y, IsPGroup 2 S → (∀ γ, S.map (ρ γ).toMonoidHom = S) → S ≠ ⊥ →
      ∀ K : Subgroup (Qt Y), IsComponentOf K ⊤ →
        ¬ S.map (mkQ Y) ≤ Subgroup.centralizer (K : Set (Qt Y)))
    (ℒ : Set (Subgroup (Qt Y))) (hℒ : ∀ K ∈ ℒ, IsComponentOf K ⊤) (hne : ℒ.Nonempty)
    (hst : ∀ γ : Γ, ∀ K ∈ ℒ, K.map (qAct ρ γ).toMonoidHom ∈ ℒ) :
    Ybar Y ⊓ Subgroup.centralizer ((⨆ K ∈ ℒ, K : Subgroup (Qt Y)) : Set (Qt Y)) = ⊥ := by
  classical
  set Lb : Subgroup (Qt Y) := ⨆ K ∈ ℒ, K with hLb
  set Kb : Subgroup (Qt Y) := Ybar Y ⊓ Subgroup.centralizer (Lb : Set (Qt Y)) with hKb
  set K : Subgroup Y := preimQ Kb with hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYN : Ybar Y ≤ Subgroup.normalizer (Lb : Set (Qt Y)) :=
    layer_sup_pCore_le_normalizer 2 ℒ hℒ
  have hKbY : Kb ≤ Ybar Y := inf_le_left
  have hNY : (Ybar Y).Normal := normal_Ybar
  have hKbn : (Kb.subgroupOf (Ybar Y)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKbY]
    intro y hy
    have h1 : y ∈ Subgroup.normalizer (Ybar Y : Set (Qt Y)) := by
      rw [Subgroup.normalizer_eq_top_iff.2 hNY]; exact Subgroup.mem_top y
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨h1, normalizer_le_normalizer_centralizer' Lb (hYN hy)⟩
  have hKn : (K.subgroupOf (preimQ (Ybar Y))).Normal := normal_subgroupOf_preimQ hKbY hKbn
  have hLbinv : ∀ γ, Lb.map (qAct ρ γ).toMonoidHom = Lb :=
    map_eq_of_map_le (qAct ρ) Lb (map_iSup_of_mem (qAct ρ) ℒ hst)
  have hCinv : ∀ γ, (Subgroup.centralizer (Lb : Set (Qt Y))).map (qAct ρ γ).toMonoidHom =
      Subgroup.centralizer (Lb : Set (Qt Y)) :=
    map_eq_of_map_le (qAct ρ) _ (map_centralizer_le (qAct ρ) Lb hLbinv)
  have hKbinv : ∀ γ, Kb.map (qAct ρ γ).toMonoidHom = Kb := by
    intro γ
    refine le_antisymm ?_ (fun x hx => ?_)
    · calc Kb.map (qAct ρ γ).toMonoidHom
          ≤ (Ybar Y).map (qAct ρ γ).toMonoidHom ⊓
            (Subgroup.centralizer (Lb : Set (Qt Y))).map (qAct ρ γ).toMonoidHom :=
            Subgroup.map_inf_le _ _ _
        _ = Kb := by rw [map_qAct_Ybar, hCinv]
    · have : x ∈ (Ybar Y).map (qAct ρ γ).toMonoidHom ⊓
          (Subgroup.centralizer (Lb : Set (Qt Y))).map (qAct ρ γ).toMonoidHom := by
        rw [map_qAct_Ybar, hCinv]; exact hx
      obtain ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩ := this
      have hab : a = b := (qAct ρ γ).injective (hax.trans hbx.symm)
      exact ⟨a, ⟨ha, hab ▸ hb⟩, hax⟩
  have hKinv : ∀ γ, K.map (ρ γ).toMonoidHom = K := fun γ => map_preimQ ρ γ (hKbinv γ)
  have hKcop : ¬ p ∣ Nat.card K := fun h => hY (h.trans (Subgroup.card_subgroup_dvd_card K))
  obtain ⟨S, hSK, hS2g, hSord, hSinv⟩ :=
    exists_sylow_invariant (q := 2) hΓ ρ K hKinv hKcop
  obtain ⟨K₁, hK₁⟩ := hne
  have hSbot : S = ⊥ := by
    by_contra hSne
    refine hS2 S hS2g hSinv hSne K₁ (hℒ K₁ hK₁) ?_
    intro x hx
    obtain ⟨s, hs, rfl⟩ := hx
    have h1 : mkQ Y s ∈ Kb := hSK hs
    have h2 : mkQ Y s ∈ Subgroup.centralizer (Lb : Set (Qt Y)) := h1.2
    exact Subgroup.centralizer_le
      (show (K₁ : Set (Qt Y)) ⊆ (Lb : Set (Qt Y)) from
        fun z hz => (le_iSup₂_of_le K₁ hK₁ le_rfl : K₁ ≤ Lb) hz) h2
  have hKodd : ¬ 2 ∣ Nat.card K := by
    intro h
    have := hSord 1 (by simpa using h)
    rw [hSbot, Subgroup.card_bot] at this
    simp at this
  have hKle : K ≤ GLAPPrimeCore 2 Y :=
    le_ker_of_normal_odd hNY (Subgroup.comap_mono hKbY) hKn hKodd
  have hker : Kb = ⊥ := by
    rw [← map_mkQ_preimQ Kb]
    rw [eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact (QuotientGroup.eq_one_iff y).2 (hKle hy)
  exact hker

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
