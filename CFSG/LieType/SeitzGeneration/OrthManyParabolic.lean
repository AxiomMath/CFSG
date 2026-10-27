module

public import CFSG.LieType.SeitzGeneration.OrthStatementScopes
public import CFSG.LieType.SeitzGeneration.HyperAveraging
public import CFSG.LieType.SeitzGeneration.OrthHyperFixed
public import CFSG.LieType.SeitzGeneration.OrthHyperRoot
public import CFSG.RankThree.PartOne.KE8F.HyperGen

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.Classical CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)

theorem le_closure_centralizers_of_normalized {P : Type} [Group P] [Finite P] {p : ℕ}
    (hp : p.Prime) {E : Subgroup P} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    {Q : Subgroup P} (hnorm : ∀ e ∈ E, ∀ v ∈ Q, e * v * e⁻¹ ∈ Q) (hQp : ¬ p ∣ Nat.card Q) :
    Q ≤ Subgroup.closure {k : P | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hEel : CFSG.IsElementaryAbelian p E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, hE.2 x x.2, Subgroup.coe_one]) }
  have hnt : Nontrivial E :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcard]; exact Nat.one_lt_pow (by norm_num) hp.one_lt)
  have hAV : E ≤ Subgroup.normalizer (Q : Set P) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hnorm e he v hv, fun hv => ?_⟩
    have := hnorm e⁻¹ (E.inv_mem he) _ hv
    simpa [mul_assoc] using this
  have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (p := p) (A := E)
    (V := Q) hAV hQp
  refine hgen.trans (iSup₂_le fun B hB => ?_)
  intro k hk
  rw [Subgroup.mem_inf] at hk
  have hBcard : Nat.card B = p := by
    have h := B.card_mul_index
    rw [hB, hcard] at h
    have h2 : Nat.card B * p = p * p := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos h2
  have hBnt : Nontrivial B :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hBcard]; exact hp.one_lt)
  obtain ⟨b, hb⟩ := exists_ne (1 : B)
  refine Subgroup.subset_closure ⟨((b : E) : P), (b : E).2,
    fun h => hb (Subtype.ext (Subtype.ext h)), ?_⟩
  exact (Subgroup.mem_centralizer_iff.1 hk.2 _ (Subgroup.mem_map_of_mem E.subtype b.2)).symm

section Parabolic

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem closure_eq_top_of_singular_stable (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpl : p ≠ ringChar K) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) {W : Submodule K V} (hW0 : W ≠ ⊥) (hW : ∀ x ∈ W, Q x = 0)
    (hstab : ∀ e ∈ E, ∀ w ∈ W, ((e : orthDerived Q) : V ≃ₗ[K] V) w ∈ W) :
    Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have hℓ : (ringChar K).Prime := by
      have := Fintype.ofFinite K
      exact CharP.char_is_prime K _
    have : ringChar K ∣ p := (CharP.cast_eq_zero_iff K (ringChar K) p).mp h0
    exact hpl ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp this).symm
  have hfinV : Finite V := Module.finite_of_finite K
  have hfinGL : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g => (g : V → V)) DFunLike.coe_injective
  obtain ⟨hGE, -⟩ := orthDerived_eq_and_le_closure hQ hT
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := hGE.ge
  have hGO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup Q
  have hEG : ∀ u w, eichler Q u w ∈ orthDerived Q := fun u w =>
    hEΩ (eichler_mem_elementaryGroup Q u w)
  set H : Subgroup (V ≃ₗ[K] V) := orthCentralizerSpan Q E with hH
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthCentralizerSpan_le_orthogonalGroup E
  let ρ : E →* Module.End K V := (autToEnd K V).comp ((orthDerived Q).subtype.comp E.subtype)
  have hAc : ∀ a b : E, a * b = b * a := fun a b => Subtype.ext (hcomm _ a.2 _ b.2)
  have hAp : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (hexp _ a.2)
  have hAstab : ∀ a : E, ∀ w ∈ W, ρ a w ∈ W := fun a w hw => hstab a.1 a.2 w hw
  obtain ⟨F', hF'idx, hW1⟩ : ∃ F' : Subgroup E, F'.index = p ∧ hyperFixed ρ F' ⊓ W ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hmem := mem_iSup_hyperFixed_top hpK hAc hAp ρ W hAstab (k := 2) (by norm_num) hcard hm
    have hbot : (⨆ (F' : Subgroup E) (_ : F'.index = p), hyperFixed ρ F' ⊓ W) = ⊥ :=
      iSup_eq_bot.2 fun F' => iSup_eq_bot.2 fun hF' => hcon F' hF'
    rw [hbot] at hmem
    exact hm0 (by simpa using hmem)
  set C : Submodule K V := hyperFixed ρ F' with hC
  set X₁ : Submodule K V := hyperFixed ρ F' ⊓ W with hX₁
  have hX₁mem : ∀ v, v ∈ X₁ ↔ (∀ f ∈ F', ρ f v = v) ∧ v ∈ W := fun v => by
    rw [hX₁, Submodule.mem_inf, mem_hyperFixed]
  have hX₁C : X₁ ≤ C := inf_le_left
  have hX₁Q : ∀ x ∈ X₁, Q x = 0 := fun x hx => hW x ((hX₁mem x).1 hx).2
  let φ : F' →* (V ≃ₗ[K] V) := ((orthDerived Q).subtype.comp E.subtype).comp F'.subtype
  have hφ : ∀ f, φ f ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun f => hGO f.1.1.2
  have hqfix : qFix φ = C := by
    ext v
    rw [mem_qFix, hC, mem_hyperFixed]
    exact ⟨fun h n hn => h ⟨n, hn⟩, fun h f => h f.1 f.2⟩
  have : Fintype F' := Fintype.ofFinite F'
  have hcardF' : Nat.card F' = p := by
    have h := Subgroup.card_mul_index F'
    rw [hF'idx, hcard] at h
    have h2 : Nat.card F' * p = p * p := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos h2
  have hF : ((Fintype.card F' : ℕ) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hcardF']
    exact hpK
  have hF'nt : Nontrivial F' :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardF']; exact hp.one_lt)
  have hS : RootSetup Q H C := by
    refine ⟨hHO, hqfix ▸ polarNondegOn_qFix hQ hφ hF, fun v => ?_, fun u hu w hw => ?_⟩
    · exact ⟨qAvg φ v, hqfix ▸ qAvg_mem φ v, hqfix ▸ sub_qAvg_mem_qPerp hφ hF v⟩
    · obtain ⟨f₀, hf₀⟩ := exists_ne (1 : F')
      exact eichler_mem_orthCentralizerSpan_of_fix hEΩ f₀.1.2
        (fun h => hf₀ (Subtype.ext (Subtype.ext h))) (mem_hyperFixed.1 hu f₀ f₀.2)
        (mem_hyperFixed.1 hw f₀ f₀.2)
  set 𝒜 : Subgroup (V ≃ₗ[K] V) := E.map (orthDerived Q).subtype with h𝒜
  have h𝒜O : 𝒜 ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨x, -, rfl⟩
    exact hGO x.2
  have hC𝒜 : ∀ a ∈ 𝒜, ∀ c ∈ C, a c ∈ C := by
    rintro _ ⟨x, hx, rfl⟩ c hc
    exact apply_mem_hyperFixed hAc ⟨x, hx⟩ hc
  have hX₁𝒜 : ∀ a ∈ 𝒜, ∀ x ∈ X₁, a x ∈ X₁ := by
    rintro _ ⟨y, hy, rfl⟩ x hx
    rw [hX₁mem] at hx ⊢
    exact ⟨fun f hf => mem_hyperFixed.1 (apply_mem_hyperFixed hAc ⟨y, hy⟩
      (mem_hyperFixed.2 hx.1)) f hf, hAstab ⟨y, hy⟩ x hx.2⟩
  have hrad : ∀ X : Submodule K V, X ≤ C → (∀ x ∈ X, Q x = 0) →
      (∀ a ∈ 𝒜, ∀ x ∈ X, a x ∈ X) → ∀ x ∈ X, ∀ d ∈ qPerp Q X, eichler Q x d ∈ H := by
    intro X _ hXQ hX𝒜 x hx d hd
    set Qx : Subgroup (orthDerived Q) := (qRad Q X hXQ).comap (orthDerived Q).subtype with hQx
    have hnorm : ∀ e ∈ E, ∀ v ∈ Qx, e * v * e⁻¹ ∈ Qx := by
      intro e he v hv
      have haS : ∀ y ∈ X, ((e : orthDerived Q) : V ≃ₗ[K] V) y ∈ X := fun y hy =>
        hX𝒜 _ ⟨e, he, rfl⟩ y hy
      have haS' : ∀ y ∈ X, ((e : orthDerived Q) : V ≃ₗ[K] V)⁻¹ y ∈ X := fun y hy =>
        hX𝒜 _ ⟨e⁻¹, E.inv_mem he, rfl⟩ y hy
      exact qRad_conj_mem (hX := hXQ) (hGO e.2) haS haS' hv
    have hQp : ¬ p ∣ Nat.card Qx :=
      not_dvd_card_comap_qRad (hX := hXQ) hp hp2 hpK (orthDerived Q)
    have hle := le_closure_centralizers_of_normalized hp ⟨⟨⟨hAc⟩⟩, hexp⟩ hcard hnorm hQp
    have hmem : (⟨eichler Q x d, hEG x d⟩ : orthDerived Q) ∈ Qx :=
      eichler_mem_qRad (hX := hXQ) hx hd
    rw [hH, orthCentralizerSpan_eq_map]
    exact ⟨_, hle hmem, rfl⟩
  obtain ⟨e₀, he₀, he₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW1
  obtain ⟨a, b, ha, hb, hab⟩ := exists_rootCenter_pair hS h𝒜O hC𝒜 hrad hX₁C hX₁Q hX₁𝒜 he₀ he₀0
  let P₀ : HypPair Q :=
    { e := a
      f := (polar Q a b)⁻¹ • b
      Q_e := ha.2.1
      Q_f := by rw [map_smul_eq_sq, hb.2.1, mul_zero]
      polar_ef := by rw [polar_smul_right_eq, inv_mul_cancel₀ hab] }
  have hle : elementaryGroup Q ≤ H :=
    elementaryGroup_le_of_hypPair hQ hHO P₀ ha (hb.smul (inv_ne_zero hab))
  exact closure_centralizers_eq_top_of_le E (hGE.le.trans hle)

theorem orthMasterParabolic_of_stable
    (h : ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (Q : QuadraticForm K V), (polarBilin Q).Nondegenerate →
      (∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) → ∀ p : ℕ, p.Prime → p ≠ 2 →
      p ≠ ringChar K → ∀ E : Subgroup (orthDerived Q), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 → ∀ {W : Submodule K V}, W ≠ ⊥ →
      (∀ x ∈ W, Q x = 0) → (∀ e ∈ E, ∀ w ∈ W, ((e : orthDerived Q) : V ≃ₗ[K] V) w ∈ W) →
      Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤) :
    OrthMasterParabolic := by
  intro K V _ _ _ _ _ Q hQ hT hdim p hp hp5 hpl E hcomm hexp hcard hNS
  classical
  have hNS' : ¬ ∀ T : Submodule K V, (∀ e ∈ E, ∀ vector ∈ T,
      ((e : orthDerived Q) : V ≃ₗ[K] V) vector ∈ T) → (∀ vector ∈ T, Q vector = 0) → T = ⊥ := hNS
  push Not at hNS'
  obtain ⟨W, hWst, hWQ, hW0⟩ := hNS'
  exact h K V Q hQ hT p hp (by omega) hpl E hcomm hexp hcard hW0 hWQ hWst

end Parabolic

theorem orthMasterParabolic : OrthMasterParabolic :=
  orthMasterParabolic_of_stable fun _ _ _ _ _ _ _ Q hQ hT _ hp hp2 hpl E hcomm hexp hcard _ hW0 hW
    hstab => closure_eq_top_of_singular_stable hQ hT hp hp2 hpl E hcomm hexp hcard hW0 hW hstab

end CFSG.LieType.SeitzGeneration
