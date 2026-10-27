module

public import CFSG.Quasithin.H13.A7Nat1238Q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7NatMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB

@[expose] def Insp1238QTab_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (hyp : Hyp1223 G T L V)
    (ψ : V ≃* Multiplicative (evenWeight 7)) (e : V), Setting1238 hyp ψ e →
    A7NatPre T L V ψ → vec ψ e = vecFS →
    ∀ K K₀ : Subgroup G, K ∈ cComp (hyp.Gv e) → Kv hyp e < K → K ≤ K₀ →
      quasithinIsMaximalLocal T K₀ → quasithinIsFaithfulLocal T K₀ →
      CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) → K₀ = ⁅K₀, thompsonJ T⁆ →
      ¬ K₀ ≤ centralizer (omegaOneCenterOf (pCoreOf 2 (K₀ ⊔ T)) : Set G) →
      K = K₀ ∧ Nonempty ((↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ⧸ center (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ≃*
        alternatingGroup (Fin 7))

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem exists_hyp1223_of_maximal_F4 (h1222 : Stmt12_2_2_F4) (hyp : Hyp1223 G T L V) {K : Subgroup G}
    (hKmax : quasithinIsMaximalLocal T K) (hKf : quasithinIsFaithfulLocal T K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ∃ V₁ : Subgroup G, Hyp1223 G T K V₁ ∧ V₁ ≤ T ∧ T ≤ normalizer (V₁ : Set G) ∧
      IsTwoReducedIn (K ⊔ T) V₁ ∧ ∀ m ∈ normalizer (K : Set G),
        CFSG.conjugate V₁ m = V₁ ∨ V₁ ⊓ CFSG.conjugate V₁ m = ⊥ := by
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hA | h3
  · exact absurd hA hyp.notAlt
  obtain ⟨hTK, ⟨V₁, hV₁⟩, hall⟩ := h3 K hKmax hKf hq
  obtain ⟨⟨hV₁T, hTV₁, hred₁, -⟩, hTI₁, -, -⟩ := hall V₁ hV₁
  exact ⟨V₁, ⟨hyp.simple, hyp.nonabelian, hyp.qtke, hyp.sylow, hyp.notAlt, hKmax, hKf, hq, hTK,
    hV₁⟩, hV₁T, hTV₁,
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hV₁T.trans le_sup_right, hred₁⟩, hTI₁⟩

theorem exists_aligned_coords_F4 (h331 : Stmt3_3_1_F4) (h1233 : Stmt12_3_3_F4) {K V₁ : Subgroup G}
    (hyp₁ : Hyp1223 G T K V₁) (hV₁T : V₁ ≤ T) (hTV₁ : T ≤ normalizer (V₁ : Set G))
    (hTI₁ : ∀ m ∈ normalizer (K : Set G), CFSG.conjugate V₁ m = V₁ ∨ V₁ ⊓ CFSG.conjugate V₁ m = ⊥)
    (hA7 : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ center (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
      alternatingGroup (Fin 7))) :
    ∃ ψ₁ : V₁ ≃* Multiplicative (evenWeight 7), A7NatPre T K V₁ ψ₁ ∧
      ∀ t ∈ T, ∃ σ ∈ sevenP, IsCoordAct ψ₁ t σ := by
  obtain ⟨ψ₁, hKact, hKonto⟩ := h1233 G T K V₁ hyp₁ hA7
  have hKV₁ : K ≤ normalizer (V₁ : Set G) := hyp₁.irrPlus.2.2.1
  have hNM := normalizer_le_of_hyp1223_F4 h331 hyp₁ hV₁T hTV₁
  have hpre : A7NatPre T K V₁ ψ₁ :=
    ⟨hV₁T, hKV₁, hTV₁, hKact, hKonto, nact_of_lact hKV₁ hKact hKonto hNM, hNM, hTI₁⟩
  obtain ⟨ψ₂, h₂, hTalign⟩ := hpre.exists_aligned hyp₁.sylow
  refine ⟨ψ₂, h₂, fun t ht => ?_⟩
  obtain ⟨σ, hσ⟩ := h₂.Nact t (h₂.T_le ht)
  exact ⟨σ, ((hTalign σ).1 ⟨t, ht, hσ⟩).1, hσ⟩

theorem insp1238Q_core_F4 (hTab : Insp1238QTab_F4) (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4)
    (h1233 : Stmt12_3_3_F4) (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ) {e : V}
    (he : vec ψ e = vecFS) (hS : Setting1238 hyp ψ e) {y : V}
    (hyZ : (y : G) ∈ quasithinOmegaOneCenter T) (hy4 : hammingNorm (vec ψ y) = 4)
    {K K₀ : Subgroup G} (hK : K ∈ cComp (hyp.Gv e)) (hKeK : Kv hyp e ≤ K) (hKK₀ : K ≤ K₀)
    (hK₀max : quasithinIsMaximalLocal T K₀) (hK₀f : quasithinIsFaithfulLocal T K₀)
    (hq : CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) (hK₀J : K₀ = ⁅K₀, thompsonJ T⁆)
    (hV₀ : ¬ K₀ ≤ centralizer (omegaOneCenterOf (pCoreOf 2 (K₀ ⊔ T)) : Set G)) :
    Kv hyp e = K ∨ (K = K₀ ∧ ∀ v : V, (v : G) ∈ ⁅V, Kv hyp e⁆ → hammingNorm (vec ψ v) = 4 →
      K ≤ closure ((Kv hyp e : Set G) ∪ (K ⊓ centralizer ({(v : G)} : Set G)))) := by
  by_cases hne : Kv hyp e = K
  · exact Or.inl hne
  right
  obtain ⟨hKK₀', hA7⟩ := hTab G T L V hyp ψ e hS h he K K₀ hK (lt_of_le_of_ne hKeK hne) hKK₀
    hK₀max hK₀f hq hK₀J hV₀
  refine ⟨hKK₀', fun v hvW hv4 => ?_⟩
  obtain ⟨V₁, hyp₁, hV₁T, hTV₁, hred₁, hTI₁⟩ := exists_hyp1223_of_maximal_F4 h1222 hyp hK₀max hK₀f hq
  obtain ⟨ψ₁, h₁, hTP⟩ := exists_aligned_coords_F4 h331 h1233 hyp₁ hV₁T hTV₁ hTI₁ hA7

  have hcomm := commutator_omegaOneCenter_le_of_alt7_natural hyp₁ h₁ hTP hred₁ hK₀J
  have hVKe : ⁅V, Kv hyp e⁆ ≤ V₁ :=
    (commutator_le_commutator_of_weight_four hyp h he
      (omegaOneCenter_le_of_local hyp hK₀max.1 hyZ) hy4).trans
      ((commutator_mono le_rfl (hKeK.trans hKK₀)).trans hcomm)
  have hv1 : (⟨v, hVKe hvW⟩ : V₁) ≠ 1 := by
    intro h1
    have h2 : (v : G) = 1 := by simpa using congrArg Subtype.val h1
    have h3 : v = 1 := Subtype.ext h2
    rw [h3, vec_one] at hv4
    exact absurd hv4 (by decide)
  have hKev : ¬ ∀ b ∈ Kv hyp e, b * ((⟨v, hVKe hvW⟩ : V₁) : G) * b⁻¹ = (⟨v, hVKe hvW⟩ : V₁) := by
    intro hc
    have h1 := eq_one_of_mem_commutator_of_centralizes hyp h he hvW hc
    rw [h1, vec_one] at hv4
    exact absurd hv4 (by decide)
  rw [hKK₀']
  have key := le_closure_of_not_centralizes h₁ (hKeK.trans hKK₀) hv1 hKev
  exact key

end CFSG.Quasithin.H13.A7
