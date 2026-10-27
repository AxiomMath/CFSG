module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPair
import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.LieType.CurtisTits

section Transport

variable {K : Type*} [Group K] {X : Type} [Group X]

theorem map_le_centralizerLayer_of_le_iSup_components {ψ : K →* X}
    (hker : ψ.ker ≤ Subgroup.center K) (hL : IsSubnormal ψ.range ⊤) (g s : K) (f : X)
    (hf : ∀ y : K, f * ψ (g * y * g⁻¹) * f⁻¹ = ψ (g * (s * y * s⁻¹) * g⁻¹)) {R : Subgroup K}
    (hR : R ≤ ⨆ (Q : Subgroup K) (_ : IsComponentOf Q (Subgroup.centralizer ({s} : Set K))), Q) :
    R.map (ψ.comp (MulAut.conj g).toMonoidHom) ≤ centralizerLayer f := by
  have hQ : ∀ Q : Subgroup K, IsComponentOf Q (Subgroup.centralizer ({s} : Set K)) →
      Q.map (ψ.comp (MulAut.conj g).toMonoidHom) ≤ centralizerLayer f := by
    intro Q hQ
    have hQ' : IsComponentOf Q (fixedGroup (MulAut.conj s)) := by
      rwa [fixedGroup_conj_eq_centralizer]
    have h := isComponentOf_map_centralizer hker g f (MulAut.conj s)
      (fun y => by rw [MulAut.conj_apply]; exact hf y) hQ'
    rw [range_comp_conj] at h
    exact le_centralizerLayer_of_isComponentOf hL h
  refine (Subgroup.map_mono hR).trans ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun Q => ?_
  rw [Subgroup.map_iSup]
  exact iSup_le fun hQc => hQ Q hQc

end Transport

section Assembly

theorem layerGenerationPairAt_of_toralLayers {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n p e : ℕ} [Fact p.Prime]
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e)
    (𝒯 : Subgroup (modelUniv t n p e Fact.out).K)
    (hlayer : ∀ i : Fin (modelUniv t n p e Fact.out).D.rank, ∀ s₁ ∈ 𝒯, ∀ s₂ ∈ 𝒯, s₁ ≠ 1 →
      s₂ ≠ 1 → s₁ * s₂ ≠ 1 → ∃ s ∈ ({s₁, s₂, s₁ * s₂} : Set (modelUniv t n p e Fact.out).K),
        rankOne (modelUniv t n p e Fact.out).D.rootGroup i ≤
          ⨆ (Q : Subgroup (modelUniv t n p e Fact.out).K)
            (_ : IsComponentOf Q (Subgroup.centralizer
              ({s} : Set (modelUniv t n p e Fact.out).K))), Q)
    (hframe : PairFrame 𝒯 (fundamentalSubgroups t (modelUniv t n p e Fact.out).D)) :
    LayerGenerationPairAt t n p e Fact.out := by
  intro X _ _ ψ hker hcomp R₁ hR₁ R₂ hR₂ z₁ hz₁ z₂ hz₂ hc₁ hc₂ hc₁₂ hc₂₁ F hF4 hF2 hFN hfaith f₁ hf₁
    f₂ hf₂ hf₁1 hf₂1 hf₁₂ hact₁ hact₂
  have hperf := CFSG.ClassicalInvolution.ModelFacts.fundPerfect_core t n p e hp2 hfund hadm
    (by omega)
  have hperf' : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, ⁅R, R⁆ = R :=
    fun R hR => le_antisymm (Subgroup.commutator_le.mpr fun _ hx _ hy =>
      R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy)) (hperf R hR)
  have cent : ∀ {R : Subgroup (modelUniv t n p e Fact.out).K}
      {c : (modelUniv t n p e Fact.out).K},
      ⁅R, R⁆ = R → (∀ y ∈ R.map ψ, ψ c * y = y * ψ c) → ∀ r ∈ R, c * r = r * c := by
    intro R c hR hc r hr
    have h := Models.Transfer.mem_centralizer_of_map (θ := ψ) hker hR (g := c)
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm)
    exact (Subgroup.mem_centralizer_iff.mp h r hr).symm
  obtain ⟨c₁, hc₁R, rfl⟩ := hz₁
  obtain ⟨c₂, hc₂R, rfl⟩ := hz₂
  obtain ⟨g, hg₁, hg₂⟩ := hframe R₁ hR₁ R₂ hR₂ c₁ hc₁R c₂ hc₂R (cent (hperf' R₁ hR₁) hc₁)
    (cent (hperf' R₂ hR₂) hc₂) (cent (hperf' R₁ hR₁) hc₁₂) (cent (hperf' R₂ hR₂) hc₂₁)
  have hsub : IsSubnormal ψ.range ⊤ := ((CFSG.isComponent_iff_open _).mp hcomp).2.1
  set s₁ : (modelUniv t n p e Fact.out).K := g⁻¹ * c₁ * g with hs₁
  set s₂ : (modelUniv t n p e Fact.out).K := g⁻¹ * c₂ * g with hs₂
  have h₁ : ∀ y : (modelUniv t n p e Fact.out).K,
      f₁ * ψ (g * y * g⁻¹) * f₁⁻¹ = ψ (g * (s₁ * y * s₁⁻¹) * g⁻¹) := fun y => by
    rw [hact₁ _ ⟨_, rfl⟩]
    simp only [map_mul, map_inv, hs₁]
    group
  have h₂ : ∀ y : (modelUniv t n p e Fact.out).K,
      f₂ * ψ (g * y * g⁻¹) * f₂⁻¹ = ψ (g * (s₂ * y * s₂⁻¹) * g⁻¹) := fun y => by
    rw [hact₂ _ ⟨_, rfl⟩]
    simp only [map_mul, map_inv, hs₂]
    group
  have h₃ : ∀ y : (modelUniv t n p e Fact.out).K,
      (f₁ * f₂) * ψ (g * y * g⁻¹) * (f₁ * f₂)⁻¹ =
        ψ (g * ((s₁ * s₂) * y * (s₁ * s₂)⁻¹) * g⁻¹) := fun y => by
    have e1 : (f₁ * f₂) * ψ (g * y * g⁻¹) * (f₁ * f₂)⁻¹ =
        f₁ * (f₂ * ψ (g * y * g⁻¹) * f₂⁻¹) * f₁⁻¹ := by group
    rw [e1, h₂, h₁ (s₂ * y * s₂⁻¹)]
    congr 1
    group
  have hnt : ∀ (f : X), f ∈ F → f ≠ 1 → ∀ s : (modelUniv t n p e Fact.out).K,
      (∀ y : (modelUniv t n p e Fact.out).K,
        f * ψ (g * y * g⁻¹) * f⁻¹ = ψ (g * (s * y * s⁻¹) * g⁻¹)) → s ≠ 1 := by
    intro f hf hf1 s hs hs1
    refine hfaith f hf hf1 fun x hx => ?_
    obtain ⟨y, rfl⟩ := hx
    have h := hs (g⁻¹ * y * g)
    rw [hs1] at h
    have e1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    have e2 : g * (1 * (g⁻¹ * y * g) * 1⁻¹) * g⁻¹ = y := by group
    rw [e1, e2] at h
    exact (mul_inv_eq_iff_eq_mul.1 h)
  have hf₃ : f₁ * f₂ ∈ F := F.mul_mem hf₁ hf₂
  have hf₃1 : f₁ * f₂ ≠ 1 := by
    intro h
    apply hf₁₂
    have := mul_eq_one_iff_eq_inv.1 h
    rw [this]
    exact inv_eq_of_mul_eq_one_right (hF2 f₂ hf₂)
  have hs₁1 : s₁ ≠ 1 := hnt f₁ hf₁ hf₁1 s₁ h₁
  have hs₂1 : s₂ ≠ 1 := hnt f₂ hf₂ hf₂1 s₂ h₂
  have hs₃1 : s₁ * s₂ ≠ 1 := hnt (f₁ * f₂) hf₃ hf₃1 (s₁ * s₂) h₃
  rw [← iSup_rankOneImage_simple_eq_range t n p e Fact.out hfund hadm ψ g]
  refine iSup_le fun i => ?_
  obtain ⟨s, hs, hsR⟩ := hlayer i s₁ hg₁ s₂ hg₂ hs₁1 hs₂1 hs₃1
  have hR : rankOneImage (modelUniv t n p e Fact.out).D ψ g (Pi.single i 1) =
      (rankOne (modelUniv t n p e Fact.out).D.rootGroup i).map
        (ψ.comp (MulAut.conj g).toMonoidHom) :=
    rankOneImage_eq_map ψ g (Pi.single i 1)
  rw [hR]
  rcases hs with rfl | rfl | rfl
  · exact (map_le_centralizerLayer_of_le_iSup_components hker hsub g _ f₁ h₁ hsR).trans
      (le_iSup₂_of_le f₁ hf₁ (le_iSup_of_le hf₁1 le_rfl))
  · exact (map_le_centralizerLayer_of_le_iSup_components hker hsub g _ f₂ h₂ hsR).trans
      (le_iSup₂_of_le f₂ hf₂ (le_iSup_of_le hf₂1 le_rfl))
  · exact (map_le_centralizerLayer_of_le_iSup_components hker hsub g _ (f₁ * f₂) h₃ hsR).trans
      (le_iSup₂_of_le (f₁ * f₂) hf₃ (le_iSup_of_le hf₃1 le_rfl))

end Assembly

section Vacuous

theorem layerGenerationPairAt_of_shared_central {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n p e : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center (modelUniv t n p e hp).K = ⊥)
    (hshare : ∀ R₁ ∈ fundamentalSubgroups t (modelUniv t n p e hp).D,
      ∀ R₂ ∈ fundamentalSubgroups t (modelUniv t n p e hp).D,
      ∀ c₁ ∈ R₁, ∀ c₂ ∈ R₂, (∀ r ∈ R₁, c₁ * r = r * c₁) → (∀ r ∈ R₂, c₂ * r = r * c₂) →
        (∀ r ∈ R₁, c₂ * r = r * c₂) → (∀ r ∈ R₂, c₁ * r = r * c₁) → c₁ * c₁ = 1 →
        c₂ * c₂ = 1 → c₁ ≠ 1 → c₂ ≠ 1 → c₁ = c₂) :
    LayerGenerationPairAt t n p e hp := by
  intro X _ _ ψ hker _ R₁ hR₁ R₂ hR₂ z₁ hz₁ z₂ hz₂ hc₁ hc₂ hc₁₂ hc₂₁ F hF4 hF2 hFN hfaith f₁ hf₁
    f₂ hf₂ hf₁1 hf₂1 hf₁₂ hact₁ hact₂
  exfalso
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (le_of_eq hZ)
  have lift : ∀ {R : Subgroup (modelUniv t n p e hp).K} {c : (modelUniv t n p e hp).K},
      (∀ y ∈ R.map ψ, ψ c * y = y * ψ c) → ∀ r ∈ R, c * r = r * c := by
    intro R c h r hr
    apply hinj
    rw [map_mul, map_mul]
    exact h (ψ r) ⟨r, hr, rfl⟩
  have hsq : ∀ (f : X) (c : (modelUniv t n p e hp).K), f ∈ F →
      (∀ y ∈ ψ.range, f * y * f⁻¹ = ψ c * y * (ψ c)⁻¹) → c * c = 1 := by
    intro f c hf hact
    have hff : f * f = 1 := hF2 f hf
    have hmem : c * c ∈ Subgroup.center (modelUniv t n p e hp).K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply hinj
      have h1 : f * ψ y * f⁻¹ = ψ c * ψ y * (ψ c)⁻¹ := hact (ψ y) ⟨y, rfl⟩
      have h2 : f * (ψ c * ψ y * (ψ c)⁻¹) * f⁻¹ =
          ψ c * (ψ c * ψ y * (ψ c)⁻¹) * (ψ c)⁻¹ := by
        have := hact (ψ (c * y * c⁻¹)) ⟨_, rfl⟩
        simpa only [map_mul, map_inv] using this
      have h3 : ψ y = ψ c * (ψ c * ψ y * (ψ c)⁻¹) * (ψ c)⁻¹ := by
        rw [← h2, ← h1]
        have e1 : f * (f * ψ y * f⁻¹) * f⁻¹ = (f * f) * ψ y * (f * f)⁻¹ := by group
        rw [e1, hff]
        simp
      have h4 : ψ c * ψ c * ψ y = ψ y * (ψ c * ψ c) := by
        calc ψ c * ψ c * ψ y =
            (ψ c * (ψ c * ψ y * (ψ c)⁻¹) * (ψ c)⁻¹) * (ψ c * ψ c) := by group
          _ = ψ y * (ψ c * ψ c) := by rw [← h3]
      simp only [map_mul]
      exact h4.symm
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨c₁, hc₁R, rfl⟩ := hz₁
  obtain ⟨c₂, hc₂R, rfl⟩ := hz₂
  by_cases h1 : c₁ = 1
  · refine hfaith f₁ hf₁ hf₁1 fun x hx => ?_
    have := hact₁ x hx
    rw [h1, map_one, one_mul, inv_one, mul_one] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  by_cases h2 : c₂ = 1
  · refine hfaith f₂ hf₂ hf₂1 fun x hx => ?_
    have := hact₂ x hx
    rw [h2, map_one, one_mul, inv_one, mul_one] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  have hc : c₁ = c₂ := hshare R₁ hR₁ R₂ hR₂ c₁ hc₁R c₂ hc₂R (lift hc₁) (lift hc₂) (lift hc₁₂)
    (lift hc₂₁) (hsq f₁ c₁ hf₁ hact₁) (hsq f₂ c₂ hf₂ hact₂) h1 h2
  refine hfaith (f₂⁻¹ * f₁) (F.mul_mem (F.inv_mem hf₂) hf₁) ?_ fun x hx => ?_
  · intro h
    exact hf₁₂ (inv_mul_eq_one.1 h).symm
  · have e1 := hact₁ x hx
    have e2 := hact₂ x hx
    rw [hc] at e1
    have e3 : f₁ * x * f₁⁻¹ = f₂ * x * f₂⁻¹ := e1.trans e2.symm
    have e4 : f₁ * x = f₂ * x * f₂⁻¹ * f₁ := by
      rw [← e3]
      group
    calc f₂⁻¹ * f₁ * x = f₂⁻¹ * (f₁ * x) := by group
      _ = x * (f₂⁻¹ * f₁) := by
        rw [e4]
        group

end Vacuous

end CFSG.ClassicalInvolution.Balance.Bootstrap
