module

public import CFSG.FeitThompson.Representations.WeightedExtensionFailureEqualityDegreeBound
public import CFSG.FeitThompson.Representations.IntegralProjectionsWeightedEqualityBridge
public import CFSG.FeitThompson.Representations.SmallNormZeroConstantCoeffLargeFamily
public import CFSG.FeitThompson.Representations.ExceptionalScalarCountExceedsNorm

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace ScalarCoherenceAssembly

open WeightedMinDegreeRigidity WeightedEqualityBridge WeightedFeitExtension EqualDegreeFamily
open scoped ComplexOrder

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]

omit [Fintype L] [Fintype G] in
theorem charSpanZero_mono {S T : Set (L → ℂ)} (h : S ⊆ T) :
    charSpanZero S ≤ charSpanZero T := fun _ hf =>
  mem_charSpanZero.2 ⟨Submodule.span_mono h (mem_charSpanZero.1 hf).1, (mem_charSpanZero.1 hf).2⟩

noncomputable def toSpanIrr {M : Type*} [AddCommGroup M] (φ : M →+ virtualChars G) :
    M →+ Submodule.span ℤ (Irr G) :=
  ((LinearEquiv.ofEq _ _ (virtualChars_eq_span_Irr G)).toAddMonoidHom).comp φ

omit [Fintype L] in
theorem coe_toSpanIrr {M : Type*} [AddCommGroup M] (φ : M →+ virtualChars G) (x : M) :
    ((toSpanIrr φ x : Submodule.span ℤ (Irr G)) : G → ℂ) = ((φ x : virtualChars G) : G → ℂ) :=
  (rfl)

omit [Fintype L] [Group L] in
theorem cfInner_eq_zero_of_forall_mem (w : G → ℂ) {T : Finset (L → ℂ)}
    {ν : Submodule.span ℤ (T : Set (L → ℂ)) →+ virtualChars G}
    (h : ∀ χ ∈ T, ∀ hχ : χ ∈ Submodule.span ℤ (T : Set (L → ℂ)),
      cfInner w (ν ⟨χ, hχ⟩ : G → ℂ) = 0)
    (f : Submodule.span ℤ (T : Set (L → ℂ))) : cfInner w (ν f : G → ℂ) = 0 := by
  set φ : Submodule.span ℤ (T : Set (L → ℂ)) →+ ℂ :=
    AddMonoidHom.mk' (fun g => cfInner w (ν g : G → ℂ)) (fun g g' => by
      rw [map_add]; exact cfInner_add_right _ _ _) with hφ
  have := addMonoidHom_eq_of_eq_on_generators (T := (T : Set (L → ℂ)))
    (fun t ht => Submodule.subset_span ht) le_rfl φ 0 (fun t ht => h t ht _) f
  simpa [hφ] using this

theorem cfInner_tauhat_nu_eq_zero {T Q : Finset (L → ℂ)} {e : ℂ}
    {D : Submodule ℤ (L → ℂ)} (hD0 : charSpanZero (T : Set (L → ℂ)) ≤ D)
    {tauhat : D →+ virtualChars G}
    {ν : Submodule.span ℤ (T : Set (L → ℂ)) →+ virtualChars G}
    (hQT : Q ⊆ T) (hQIrr : ∀ χ ∈ Q, χ ∈ Irr L) (hdeg : ∀ χ ∈ T, χ 1 = e)
    (hτ : ∀ f g : D, cfInner (tauhat f : G → ℂ) (tauhat g : G → ℂ)
      = cfInner (f : L → ℂ) (g : L → ℂ))
    (hν : ∀ f g : Submodule.span ℤ (T : Set (L → ℂ)),
      cfInner (ν f : G → ℂ) (ν g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hντ : ∀ f : charSpanZero (T : Set (L → ℂ)),
      (ν (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ)
        = (tauhat (Submodule.inclusion hD0 f) : G → ℂ))
    {α : D} (hα : ∀ χ ∈ T, cfInner (α : L → ℂ) χ = 0)
    (hcard : (cfInner (α : L → ℂ) (α : L → ℂ)).re < Q.card)
    (f : Submodule.span ℤ (T : Set (L → ℂ))) :
    cfInner (tauhat α : G → ℂ) (ν f : G → ℂ) = 0 := by
  refine cfInner_eq_zero_of_forall_mem (ν := ν) _ (fun χ hχ _ => ?_) f
  exact cfInner_tau_nu_eq_zero (hD0 := hD0) (τ := toSpanIrr tauhat) (ν := toSpanIrr ν)
    hQT hQIrr hdeg (fun f g => hτ f g) (fun f g => hν f g) (fun f => hντ f) hα hcard hχ

theorem exists_nu_of_isTauCoherent {S : Finset (L → ℂ)} {tau : (L → ℂ) → G → ℂ}
    {R : (L → ℂ) → Finset (G → ℂ)} (hsub : IsSubcoherent S tau R) {T : Finset (L → ℂ)}
    (hTS : (T : Set (L → ℂ)) ⊆ (S : Set (L → ℂ))) (h : IsTauCoherent tau T) :
    ∃ ν : Submodule.span ℤ (T : Set (L → ℂ)) →+ virtualChars G,
      (∀ f g : Submodule.span ℤ (T : Set (L → ℂ)),
        cfInner (ν f : G → ℂ) (ν g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ)) ∧
      ∀ f : charSpanZero (T : Set (L → ℂ)),
        (ν (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ) = tau (f : L → ℂ) := by
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 ((isTauCoherent_iff hsub hTS).1 h)
  exact ⟨ν, hν.inner_eq, fun f => by
    rw [show ((ν (Submodule.inclusion (charSpanZero_le _) f) : virtualChars G) : G → ℂ)
      = ((subTauHom hsub hTS f : virtualChars G) : G → ℂ) from congrArg _ (hν.eq_on_zero f),
      subTauHom_apply]⟩

theorem exists_isTauCoherent_ssupset
    {S S1 S3 Q : Finset (L → ℂ)} {tau : (L → ℂ) → G → ℂ} {R : (L → ℂ) → Finset (G → ℂ)}
    {ν₁ : Submodule.span ℤ (S1 : Set (L → ℂ)) →+ virtualChars G}
    {ν₃ : Submodule.span ℤ (S3 : Set (L → ℂ)) →+ virtualChars G}
    {k d : ℤ} {D : Submodule ℤ (L → ℂ)} {tauhat : D →+ virtualChars G} {α ψ : L → ℂ}
    (hcfg : IsWeightedEqualityConfig S S1 S3 Q tau R ν₁ ν₃ k d D tauhat α ψ) :
    ∃ T : Finset (L → ℂ), S1 ⊂ T ∧ T ⊆ S ∧ (∀ γ ∈ T, star γ ∈ T) ∧ IsTauCoherent tau T := by
  classical
  obtain ⟨lam, hlam⟩ := hcfg.Q_nonempty
  obtain ⟨ν, hν, -⟩ := hcfg.exists_isCoherentWith_insert_pair hlam
  have hlam3 : lam ∈ S3 := hcfg.Q_subset hlam
  have hslam3 : star lam ∈ S3 := hcfg.Q_subset (hcfg.Q_star _ hlam)
  have hlamS1 : lam ∉ S1 := fun h => (Finset.disjoint_left.1 hcfg.disjoint h) hlam3
  set T : Finset (L → ℂ) := insert lam (insert (star lam) S1) with hT
  have hTS : T ⊆ S := by
    intro x hx
    rw [hT, Finset.mem_insert, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact hcfg.S3_subset hlam3
    · exact hcfg.S3_subset hslam3
    · exact hcfg.S1_subset hx
  have hcoe : (S1 : Set (L → ℂ)) ∪ {lam, star lam} = (T : Set (L → ℂ)) := by
    rw [hT]; ext f
    simp only [Finset.coe_insert, Set.mem_insert_iff, Set.mem_union, Finset.mem_coe,
      Set.mem_singleton_iff]
    tauto
  have hUS : (S1 : Set (L → ℂ)) ∪ {lam, star lam} ⊆ (S : Set (L → ℂ)) := by
    rw [hcoe]; exact_mod_cast hTS
  refine ⟨T, ⟨?_, ?_⟩, hTS, ?_, ?_⟩
  · intro x hx; rw [hT]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  · intro hs; exact hlamS1 (hs (by rw [hT]; exact Finset.mem_insert_self _ _))
  · intro x hx
    rw [hT, Finset.mem_insert, Finset.mem_insert] at hx ⊢
    rcases hx with rfl | rfl | hx
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (star_star _)
    · exact Or.inr (Or.inr (hcfg.S1_star _ hx))
  · refine isTauCoherent_of_isCoherent hcfg.subcoherent hcoe hUS ?_
    exact (isCoherentWith_congr_baseline
      (fun f => by rw [coe_baselineOn, subTauHom_apply]) hν).isCoherent

set_option maxHeartbeats 1600000 in
theorem isCoherent_of_layers
    {S : Finset (L → ℂ)} {tau : (L → ℂ) → G → ℂ} {R : (L → ℂ) → Finset (G → ℂ)}
    (hsub : IsSubcoherent S tau R)
    {D : Submodule ℤ (L → ℂ)} (hD : charSpanZero (S : Set (L → ℂ)) ≤ D)
    (tauhat : D →+ virtualChars G)
    (htauhatIsom : ∀ f g : D, cfInner (tauhat f : G → ℂ) (tauhat g : G → ℂ)
      = cfInner (f : L → ℂ) (g : L → ℂ))
    (htauhatTau : ∀ f : charSpanZero (S : Set (L → ℂ)),
      (tauhat (Submodule.inclusion hD f) : G → ℂ) = tau (f : L → ℂ))
    {τS : charSpanZero (S : Set (L → ℂ)) →+ virtualChars G}
    (hτS : ∀ f : charSpanZero (S : Set (L → ℂ)), (τS f : G → ℂ) = tau (f : L → ℂ))
    {p q a u v : ℕ}
    (hp : 3 ≤ p) (hpodd : Odd p) (hq : 3 ≤ q) (ha1 : 1 < a) (haodd : Odd a)
    (hadvd : a ∣ p - 1) (haud : a ∣ u) (hu : 0 < u) (huv : u ≤ v)
    (hdeg : ∀ χ ∈ S, ∃ m : ℕ, 0 < m ∧ χ 1 = ((q * a * m : ℕ) : ℂ))
    (hdegle : ∀ χ ∈ S, χ 1 ≤ ((q * u : ℕ) : ℂ))
    {Q : Finset (L → ℂ)} (hQS : Q ⊆ S) (hQIrr : ∀ γ ∈ Q, γ ∈ Irr L)
    (hQdeg : ∀ γ ∈ Q, γ 1 = ((q * a : ℕ) : ℂ))
    {r : ℕ} (hr : 0 < r) (hrdef : r * a ^ 2 = (p - 1) * v) (hQcard : r ≤ Q.card)
    (hlarge : 2 * a = p - 1 → v = u → a < u →
      (∀ χ ∈ S, χ 1 = ((q * a : ℕ) : ℂ) ∨ χ 1 = ((q * u : ℕ) : ℂ)) →
      u ≤ a ^ 2 ∧ ∃ S4 : Finset (L → ℂ), S4 ⊆ S ∧ (∀ γ ∈ S4, γ ∈ Irr L) ∧
        (∀ γ ∈ S4, star γ ∈ S4) ∧ (∀ γ ∈ S4, γ 1 = ((q * u : ℕ) : ℂ)) ∧
        (q : ℝ) * (u : ℝ) * (S4.card : ℝ) + ((p : ℝ) - 1) * ((q : ℝ) + (u : ℝ))
          = (p : ℝ) ^ q - 1)
    (halpha : ∀ ψ ∈ S, ψ ∈ Irr L → ψ 1 = ((q * a : ℕ) : ℂ) →
      2 * a = p - 1 → v = u → a < u →
      (∀ χ ∈ S, χ 1 = ((q * a : ℕ) : ℂ) ∨ χ 1 = ((q * u : ℕ) : ℂ)) →
      ∃ α ∈ D, cfInner α α = (a : ℂ) + 1 + ((q : ℂ) - 1) * (a : ℂ) ^ 2 / (u : ℂ) ∧
        cfInner α ψ = -1 ∧ ∀ χ ∈ S, χ ≠ ψ → cfInner α χ = 0) :
    IsCoherent (S : Set (L → ℂ)) τS := by
  classical
  by_contra hnc
  have hSnc : ¬ IsTauCoherent tau S := fun h => by
    obtain ⟨ν, hν⟩ := isCoherent_iff.1 ((isTauCoherent_iff hsub le_rfl).1 h)
    exact hnc (isCoherentWith_congr_baseline (fun f => by rw [subTauHom_apply, hτS]) hν).isCoherent
  set S1 : Finset (L → ℂ) := S.filter (fun χ => χ 1 = ((q * a : ℕ) : ℂ)) with hS1def
  have hS1 : ∀ χ : L → ℂ, χ ∈ S1 ↔ χ ∈ S ∧ χ 1 = ((q * a : ℕ) : ℂ) := by
    intro χ; rw [hS1def, Finset.mem_filter]
  have hQS1 : Q ⊆ S1 := fun γ hγ => (hS1 γ).2 ⟨hQS hγ, hQdeg γ hγ⟩
  obtain ⟨h2a, hvu, hau, hS1Q, hQcard', hQa, hdeg3, hcoh1, hmax⟩ :=
    rigidity hsub hp hpodd (by omega) ha1 haodd hadvd haud hu huv hdeg hdegle hS1 hQS1 hQIrr
      hr hrdef hQcard hSnc
  have hdeg2 : ∀ χ ∈ S, χ 1 = ((q * a : ℕ) : ℂ) ∨ χ 1 = ((q * u : ℕ) : ℂ) := by
    intro χ hχ
    by_cases h : χ ∈ S1
    · exact Or.inl ((hS1 χ).1 h).2
    · exact Or.inr (hdeg3 χ hχ h)
  obtain ⟨hua, S4, hS4S, hS4Irr, hS4star, hS4deg, hcount⟩ := hlarge h2a hvu hau hdeg2
  set S3 : Finset (L → ℂ) := S \ S1 with hS3def
  have hS1S : S1 ⊆ S := fun γ hγ => ((hS1 γ).1 hγ).1
  have hS3S : S3 ⊆ S := Finset.sdiff_subset
  have hS3deg : ∀ χ ∈ S3, χ 1 = ((q * u : ℕ) : ℂ) := fun χ hχ =>
    hdeg3 χ (Finset.mem_sdiff.1 hχ).1 (Finset.mem_sdiff.1 hχ).2
  have hS1deg : ∀ χ ∈ S1, χ 1 = ((q * a : ℕ) : ℂ) := fun χ hχ => ((hS1 χ).1 hχ).2
  have hstarS1 : ∀ γ ∈ S1, star γ ∈ S1 := by
    intro γ hγ
    obtain ⟨hγS, hγd⟩ := (hS1 γ).1 hγ
    exact (hS1 _).2 ⟨hsub.star_mem γ hγS, by
      rw [(hsub.isCharacter γ hγS).star_apply_one, hγd]⟩
  have hstarS3 : ∀ γ ∈ S3, star γ ∈ S3 := by
    intro γ hγ
    obtain ⟨hγS, hγn⟩ := Finset.mem_sdiff.1 hγ
    refine Finset.mem_sdiff.2 ⟨hsub.star_mem γ hγS, fun h => hγn ?_⟩
    have := hstarS1 _ h; rwa [star_star] at this
  have hqane : ((q * a : ℕ) : ℂ) ≠ ((q * u : ℕ) : ℂ) := by
    have h : q * a ≠ q * u := fun h =>
      absurd (Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) h) (by omega)
    exact_mod_cast h
  have hS4S3 : S4 ⊆ S3 := fun γ hγ =>
    Finset.mem_sdiff.2 ⟨hS4S hγ, fun h => hqane (((hS1 γ).1 h).2.symm.trans (hS4deg γ hγ))⟩
  have hQne : Q.Nonempty := Finset.card_pos.1 (by omega)
  have hS1ne : S1.Nonempty := hQne.mono hQS1
  have hS1Irr : (S1 : Set (L → ℂ)) ⊆ Irr L := by
    rw [hS1Q]; exact fun γ hγ => hQIrr γ hγ
  have hpe : p = 2 * a + 1 := by omega
  have hnormlt : (a : ℝ) + 1 + ((q : ℝ) - 1) * (a : ℝ) ^ 2 / (u : ℝ) < (S4.card : ℝ) :=
    lt_of_exceptional_count_eq (by omega) hq hu hua hpe hcount
  have hS4ne : S4.Nonempty := by
    refine Finset.card_pos.1 ?_
    have h0 : (0 : ℝ) < (S4.card : ℝ) := pos_of_exceptional_count_eq (by omega) hq hu hua hpe hcount
    exact_mod_cast h0
  obtain ⟨ν₁, hν₁iso, hν₁tau⟩ :=
    exists_nu_of_isTauCoherent hsub (by exact_mod_cast hS1S) hcoh1
  obtain ⟨ν₃, hν₃iso, hν₃tau⟩ := exists_nu_of_isTauCoherent hsub (by exact_mod_cast hS3S)
    (isTauCoherent_of_uniform_degree hsub hS3S hstarS3
      (fun χ hχ ψ hψ => by rw [hS3deg χ hχ, hS3deg ψ hψ]))
  obtain ⟨ψ, hψ⟩ := hS1ne
  obtain ⟨α, hαD, hαα, hαψ, hαne⟩ :=
    halpha ψ (hS1S hψ) (hS1Irr hψ) (hS1deg ψ hψ) h2a hvu hau hdeg2
  have hS3Sset : (S3 : Set (L → ℂ)) ⊆ (S : Set (L → ℂ)) := by exact_mod_cast hS3S
  have hD3 : charSpanZero (S3 : Set (L → ℂ)) ≤ D := (charSpanZero_mono hS3Sset).trans hD
  have hν₃tauhat : ∀ f : charSpanZero (S3 : Set (L → ℂ)),
      (ν₃ (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ)
        = (tauhat (Submodule.inclusion hD3 f) : G → ℂ) := by
    intro f
    rw [hν₃tau f]
    exact (htauhatTau ⟨(f : L → ℂ), charSpanZero_mono hS3Sset f.2⟩).symm
  have hαre : (cfInner α α).re < S4.card := by
    rw [hαα, show ((a : ℂ) + 1 + ((q : ℂ) - 1) * (a : ℂ) ^ 2 / (u : ℂ))
      = ((((a : ℝ) + 1 + ((q : ℝ) - 1) * (a : ℝ) ^ 2 / (u : ℝ)) : ℝ) : ℂ) from by push_cast; ring,
      Complex.ofReal_re]
    exact hnormlt
  have horth : ∀ f : Submodule.span ℤ (S3 : Set (L → ℂ)),
      cfInner (tauhat ⟨α, hαD⟩ : G → ℂ) (ν₃ f : G → ℂ) = 0 :=
    cfInner_tauhat_nu_eq_zero hD3 hS4S3 hS4Irr hS3deg htauhatIsom hν₃iso hν₃tauhat
      (α := ⟨α, hαD⟩) (fun χ hχ => hαne χ (hS3S hχ) (fun h => by
        exact hqane (((h ▸ hS3deg χ hχ : ψ 1 = ((q * u : ℕ) : ℂ))).symm.trans (hS1deg ψ hψ)).symm))
      hαre
  have hkd : (u / a) * (q * a) = q * u := by
    rw [show (u / a) * (q * a) = q * (u / a * a) from by ring, Nat.div_mul_cancel haud]
  have hcfg : IsWeightedEqualityConfig S S1 S3 S4 tau R ν₁ ν₃ ((u / a : ℕ) : ℤ)
      ((q * a : ℕ) : ℤ) D tauhat α ψ := by
    refine
    { subcoherent := hsub
      union := ?_
      disjoint := Finset.disjoint_sdiff
      S1_nonempty := ⟨ψ, hψ⟩
      S3_nonempty := hS4ne.mono hS4S3
      S1_star := hstarS1
      S3_star := hstarS3
      nu1_isometry := hν₁iso
      nu1_eq_tau := hν₁tau
      nu3_isometry := hν₃iso
      nu3_eq_tau := hν₃tau
      one_lt_k := ?_
      d_pos := ?_
      S1_subset_Irr := hS1Irr
      card_S1 := ?_
      S1_degree := ?_
      S3_degree := ?_
      Q_subset := hS4S3
      Q_subset_Irr := hS4Irr
      Q_nonempty := hS4ne
      Q_star := hS4star
      charSpanZero_le_D := hD
      alpha_mem := hαD
      tauhat_isometry := htauhatIsom
      tauhat_eq_tau := htauhatTau
      psi_mem := hψ
      alpha_inner_psi := hαψ
      alpha_inner_ne := hαne
      tauhat_alpha_orthogonal := horth }
    · rw [hS3def]
      ext f
      simp only [Finset.coe_sdiff, Set.mem_union, Finset.mem_coe, Set.mem_sdiff]
      exact ⟨fun h => by by_cases hf : f ∈ S1 <;> tauto,
        fun h => by rcases h with h | h; exacts [hS1S h, h.1]⟩
    · have h : 1 < u / a := by
        obtain ⟨m, rfl⟩ := haud
        rw [Nat.mul_div_cancel_left _ (by omega)]
        rcases Nat.lt_or_ge m 2 with hm | hm
        · interval_cases m <;> omega
        · omega
      exact_mod_cast h
    · have h : 0 < q * a := by positivity
      exact_mod_cast h
    · have h : S1.card = 2 * (u / a) := by
        refine Nat.eq_of_mul_eq_mul_right (show 0 < a by omega) ?_
        rw [hS1Q, hQa, mul_assoc, Nat.div_mul_cancel haud]
      rw [h]; push_cast; ring
    · intro χ hχ; rw [hS1deg χ hχ]; norm_cast
    · intro χ hχ
      rw [hS3deg χ hχ,
        show (((u / a : ℕ) : ℤ) * ((q * a : ℕ) : ℤ) : ℤ) = ((q * u : ℕ) : ℤ) from
          by push_cast [← hkd]; ring]
      norm_cast
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := exists_isTauCoherent_ssupset hcfg
  exact absurd (hmax T hT1.le hT2 hT3 hT4) (ne_of_gt hT1)

end ScalarCoherenceAssembly

end CFSG.FeitThompson
