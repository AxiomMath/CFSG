module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPair
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTransfer
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcSigns

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
  CFSG.Assembly.LowTwoRank

section Abstract

variable {t : StatedLieTag} {K : Type} [Group K] {F : Type*} [Field F] {G : Type*} [Group G]

theorem map_conj_le_centralizer {X : Subgroup K} {g c : K}
    (h : ∀ r ∈ X, (g⁻¹ * c * g) * r = r * (g⁻¹ * c * g)) :
    X.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({c} : Set K) := by
  rintro _ ⟨r, hr, rfl⟩
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  have h1 := h r hr
  show g * r * g⁻¹ * c = c * (g * r * g⁻¹)
  calc g * r * g⁻¹ * c = g * (r * (g⁻¹ * c * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * c * g) * r) * g⁻¹ := by rw [h1]
    _ = c * (g * r * g⁻¹) := by group

open CFSG.LieType.CurtisTits in
theorem commutingGeneration_of_signTorus {ι : Type*} (D : UniversalRootDatum K) (𝒯 : Subgroup K)
    (emb : K →* G) (σ : Fin D.rank → ι) (d : (ι → Fˣ) →* G)
    (hframe : PairFrame 𝒯 (fundamentalSubgroups t D))
    (hsign : ∀ u ∈ 𝒯, ∃ b : ι → Fˣ, (∀ i, b i = 1 ∨ b i = -1) ∧ emb u = d b)
    (hcomm : ∀ (u : K) (b : ι → Fˣ) (k : Fin D.rank), emb u = d b → b (σ k) = 1 →
      ∀ r ∈ rankOne D.rootGroup k, u * r = r * u)
    (hlong : ∀ k : Fin D.rank, IsLongestRoot D (Pi.single k 1))
    (hgen : ∀ g : K, ⨆ k : Fin D.rank, rankOneRoot D g (Pi.single k 1) = ⊤) :
    ModelFacts.CommutingGeneration (fundamentalSubgroups t D) := by
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₁₂ hx₂₁
  obtain ⟨g, hg₁, hg₂⟩ := hframe R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₁₂ hx₂₁
  obtain ⟨b₁, hb₁, he₁⟩ := hsign _ hg₁
  obtain ⟨b₂, hb₂, he₂⟩ := hsign _ hg₂
  have hu₁₂ : g⁻¹ * (c₁ * c₂) * g = (g⁻¹ * c₁ * g) * (g⁻¹ * c₂ * g) := by group
  have hkey : ∀ k : Fin D.rank,
      (∀ r ∈ rankOne D.rootGroup k, (g⁻¹ * c₁ * g) * r = r * (g⁻¹ * c₁ * g)) ∨
      (∀ r ∈ rankOne D.rootGroup k, (g⁻¹ * c₂ * g) * r = r * (g⁻¹ * c₂ * g)) ∨
      (∀ r ∈ rankOne D.rootGroup k, (g⁻¹ * (c₁ * c₂) * g) * r = r * (g⁻¹ * (c₁ * c₂) * g)) := by
    intro k
    by_cases h1 : b₁ (σ k) = 1
    · exact Or.inl (hcomm _ b₁ k he₁ h1)
    by_cases h2 : b₂ (σ k) = 1
    · exact Or.inr (Or.inl (hcomm _ b₂ k he₂ h2))
    have h1' : b₁ (σ k) = -1 := (hb₁ _).resolve_left h1
    have h2' : b₂ (σ k) = -1 := (hb₂ _).resolve_left h2
    refine Or.inr (Or.inr ?_)
    rw [hu₁₂]
    exact hcomm _ (b₁ * b₂) k (by rw [map_mul, he₁, he₂, ← map_mul])
      (by simp [h1', h2'])
  rw [← hgen g]
  refine iSup_le fun k => ?_
  have hmem : rankOneRoot D g (Pi.single k 1) ∈ fundamentalSubgroups t D :=
    ⟨g, Pi.single k 1, Or.inl (hlong k), rfl⟩
  rcases hkey k with h | h | h
  · exact le_iSup₂_of_le _ hmem (le_iSup_of_le (Or.inl (map_conj_le_centralizer h)) le_rfl)
  · exact le_iSup₂_of_le _ hmem
      (le_iSup_of_le (Or.inr (Or.inl (map_conj_le_centralizer h))) le_rfl)
  · exact le_iSup₂_of_le _ hmem
      (le_iSup_of_le (Or.inr (Or.inr (map_conj_le_centralizer h))) le_rfl)

end Abstract

section Tags

open CFSG.LieType.Chevalley

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

theorem commutingFundamentalGeneration_exc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {t : StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) (hadm : StatedLieAdmissible t 0 p e)
    (hframe : PairFrame (ModelFacts.excSignGroup t p e)
      (Generic.fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D)) :
    ModelFacts.CommutingFundamentalGeneration p t 0 e := by
  have ht' : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4 := by tauto
  have hfund : Generic.IsFundTag t := by rcases ht with rfl | rfl | rfl <;> trivial
  have hlong : ∀ k : Fin (Generic.modelUniv t 0 p e Fact.out).D.rank,
      IsLongestRoot (Generic.modelUniv t 0 p e Fact.out).D (Pi.single k 1) := fun k =>
    ModelFacts.isLongestRoot_single t 0 p e Fact.out hfund hadm k
      (by rcases ht with rfl | rfl | rfl <;> trivial)
  exact commutingGeneration_of_signTorus _ (ModelFacts.excSignGroup t p e)
    (ModelFacts.excEmbed t p e) (Fin.cast (ModelFacts.excRank_eq ht'))
    (rootDiagUnitHom (ModelFacts.excTag t) (GaloisField p e)) hframe
    (fun u hu => ModelFacts.mem_excSignGroup.1 hu)
    (fun _ _ k hu hk => ModelFacts.commute_rankOne_of_excEmbed_eq hp2 hq ht' hadm hu k hk) hlong
    (iSup_rankOneRoot_simple_eq_top t 0 p e Fact.out hfund hadm)

end Tags

end CFSG.ClassicalInvolution.Balance.Bootstrap
