module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigH

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem eq_of_support_four {n : ℕ} {D : Finset (Fin n)} (hD : D.card = 4)
    {V W : Subgroup (alternatingGroup (Fin n))} (hV : Nat.card V = 4) (hW : Nat.card W = 4)
    (hVsq : ∀ σ ∈ V, σ * σ = 1) (hWsq : ∀ σ ∈ W, σ * σ = 1)
    (hVs : ∀ σ ∈ V, ∀ ω ∉ D, (σ : Perm (Fin n)) ω = ω)
    (hWs : ∀ σ ∈ W, ∀ ω ∉ D, (σ : Perm (Fin n)) ω = ω) : V = W := by
  classical
  set T : Set (Perm (Fin n)) :=
    {π | π * π = 1 ∧ Perm.sign π = 1 ∧ ∀ ω ∉ D, π ω = ω} with hT
  have hTle : T.ncard ≤ 4 := Sol78.ncard_evenInvolutions_le_four hD
  have key : ∀ U : Subgroup (alternatingGroup (Fin n)), Nat.card U = 4 →
      (∀ σ ∈ U, σ * σ = 1) → (∀ σ ∈ U, ∀ ω ∉ D, (σ : Perm (Fin n)) ω = ω) →
      ((U.map (alternatingGroup (Fin n)).subtype : Subgroup (Perm (Fin n))) : Set _) = T := by
    intro U hU hUsq hUs
    have hsub : ((U.map (alternatingGroup (Fin n)).subtype : Subgroup (Perm (Fin n))) :
        Set (Perm (Fin n))) ⊆ T := by
      rintro _ ⟨σ, hσ, rfl⟩
      refine ⟨?_, σ.2, hUs σ hσ⟩
      have := congrArg Subtype.val (hUsq σ hσ)
      simpa using this
    have hcard : ((U.map (alternatingGroup (Fin n)).subtype : Subgroup (Perm (Fin n))) :
        Set (Perm (Fin n))).ncard = 4 := by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Subgroup.card_map_of_injective
        (alternatingGroup (Fin n)).subtype_injective, hU]
    exact Set.eq_of_subset_of_ncard_le hsub (hcard ▸ hTle) (Set.toFinite _)
  have h1 := (key V hV hVsq hVs).trans (key W hW hWsq hWs).symm
  exact Subgroup.map_injective (alternatingGroup (Fin n)).subtype_injective
    (SetLike.coe_injective h1)

theorem exists_alt_map_four {n : ℕ} (hn : 6 ≤ n) {D₁ D₂ : Finset (Fin n)} (h₁ : D₁.card = 4)
    (h₂ : D₂.card = 4) :
    ∃ σ : alternatingGroup (Fin n), ∀ ω, ω ∈ D₁ ↔ (σ : Perm (Fin n)) ω ∈ D₂ := by
  classical
  have : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin n)) (Fin n) (n - 2) := by
    have h := alternatingGroup.isMultiplyPretransitive (Fin n)
    rwa [Nat.card_fin] at h
  have h4 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin n)) (Fin n) 4 :=
    MulAction.isMultiplyPretransitive_of_le (n := n - 2) (by omega)
      (by rw [Nat.card_fin]; omega)
  let f₁ : Fin 4 ↪ Fin n := (D₁.orderEmbOfFin h₁).toEmbedding
  let f₂ : Fin 4 ↪ Fin n := (D₂.orderEmbOfFin h₂).toEmbedding
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin n)) f₁ f₂
  have hσi : ∀ i, (σ : Perm (Fin n)) (f₁ i) = f₂ i := fun i => by
    have := congrArg (fun f : Fin 4 ↪ Fin n => f i) hσ
    simpa [Subgroup.smul_def, Perm.smul_def] using this
  refine ⟨σ, fun ω => ?_⟩
  have hr₁ : ∀ ω, ω ∈ D₁ ↔ ∃ i, f₁ i = ω := fun ω => by
    rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin D₁ h₁, Set.mem_range]
    rfl
  have hr₂ : ∀ ω, ω ∈ D₂ ↔ ∃ i, f₂ i = ω := fun ω => by
    rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin D₂ h₂, Set.mem_range]
    rfl
  rw [hr₁, hr₂]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, (hσi i).symm⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, (σ : Perm (Fin n)).injective ?_⟩
    rw [hσi, hi]

theorem conj_support {n : ℕ} {D₁ D₂ : Finset (Fin n)} {σ : alternatingGroup (Fin n)}
    (hσ : ∀ ω, ω ∈ D₁ ↔ (σ : Perm (Fin n)) ω ∈ D₂) {τ : alternatingGroup (Fin n)}
    (hτ : ∀ ω ∉ D₁, (τ : Perm (Fin n)) ω = ω) :
    ∀ ω ∉ D₂, ((σ * τ * σ⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω := by
  intro ω hω
  have h1 : (σ⁻¹ : Perm (Fin n)) ω ∉ D₁ := by
    rw [hσ]
    simpa using hω
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
  rw [hτ _ h1]
  simp

theorem exists_conj_of_le_sup_odd {G : Type*} [Group G] [Finite G] {A B O : Subgroup G}
    [hOn : O.Normal] (hB : IsPGroup 2 B) (hO : Odd (Nat.card O)) (hAK : A ≤ B ⊔ O)
    (hcard : Nat.card A = Nat.card B) :
    ∃ k ∈ B ⊔ O, A.map (MulAut.conj k).toMonoidHom = B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := B ⊔ O with hK
  have hcardK : Nat.card K = Nat.card B * Nat.card O := by
    have hBN : B ≤ normalizer (O : Set G) := by
      rw [normalizer_eq_top_iff.mpr hOn]
      exact le_top
    have h := Sol78.card_sup_mul_card_inf' hBN
    rw [inf_eq_bot_of_two_odd hB hO, Subgroup.card_bot, mul_one] at h
    exact h
  have hBK : B ≤ K := le_sup_left
  obtain ⟨a, ha⟩ := hB.exists_card_eq
  have hOpos : 0 < Nat.card O := Nat.card_pos
  have hfact : (Nat.card K).factorization 2 = a := by
    rw [hcardK, ha, Nat.factorization_mul (by positivity) (by omega),
      Nat.Prime.factorization_pow Nat.prime_two]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by
      intro h2
      exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h2)), add_zero]
  let P1 : Sylow 2 K := Sylow.ofCard (A.subgroupOf K) (by
    rw [hfact, ← ha, ← hcard]
    exact Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv)
  let P2 : Sylow 2 K := Sylow.ofCard (B.subgroupOf K) (by
    rw [hfact, ← ha]
    exact Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv)
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P1 P2
  refine ⟨k, k.2, ?_⟩
  have h0 : ((k • P1 : Sylow 2 K) : Subgroup K) =
      (A.subgroupOf K).map (MulAut.conj k).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have h1 : (((k • P1 : Sylow 2 K) : Subgroup K)).map K.subtype =
      ((P2 : Sylow 2 K) : Subgroup K).map K.subtype := by rw [hk]
  rw [h0] at h1
  have h2 : ((P2 : Sylow 2 K) : Subgroup K).map K.subtype = B := by
    simp only [P2, Sylow.coe_ofCard]
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hBK]
  rw [h2] at h1
  rw [← h1]
  ext g
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype,
    mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨k * ⟨y, hAK hy⟩ * k⁻¹, ⟨⟨y, hAK hy⟩, hy, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by simp⟩

theorem map_map_conj {G Q : Type*} [Group G] [Group Q] (f : G →* Q) (A : Subgroup G) (c : G) :
    (A.map (MulAut.conj c).toMonoidHom).map f = (A.map f).map (MulAut.conj (f c)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem map_subtype_map_conj {G : Type*} [Group G] {K : Subgroup G} (A : Subgroup K) (c : K) :
    (A.map (MulAut.conj c).toMonoidHom).map K.subtype =
      (A.map K.subtype).map (MulAut.conj (c : G)).toMonoidHom :=
  map_map_conj K.subtype A c

theorem exists_conj_four_subgroup {X : Type} [Group X] [Finite X] {J : Subgroup X} {n : ℕ}
    (hn : 6 ≤ n) (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) {E₁ E₂ : Subgroup X}
    (h₁J : E₁ ≤ J) (h₂J : E₂ ≤ J) (h₁ : Nat.card E₁ = 4) (h₂ : Nat.card E₂ = 4)
    (h₁sq : ∀ x ∈ E₁, x * x = 1) (h₂sq : ∀ x ∈ E₂, x * x = 1) {D₁ D₂ : Finset (Fin n)}
    (hD₁ : D₁.card = 4) (hD₂ : D₂.card = 4)
    (h₁s : ∀ x : J, (x : X) ∈ E₁ → ∀ ω ∉ D₁,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω)
    (h₂s : ∀ x : J, (x : X) ∈ E₂ → ∀ ω ∉ D₂,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω) :
    ∃ j ∈ J, E₁.map (MulAut.conj j).toMonoidHom = E₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : J →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 J))
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective (pPrimeCore 2 J))
  have hker : π.ker = pPrimeCore 2 J := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (pPrimeCore 2 J) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hO : Odd (Nat.card π.ker) := by
    rw [hker]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have himg : ∀ A : Subgroup X, A ≤ J → Nat.card A = 4 → (∀ x ∈ A, x * x = 1) →
      ∀ D : Finset (Fin n), (∀ x : J, (x : X) ∈ A → ∀ ω ∉ D,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω) →
      Nat.card (A.subgroupOf J) = 4 ∧ IsPGroup 2 (A.subgroupOf J) ∧
        Nat.card ((A.subgroupOf J).map π) = 4 ∧ (∀ a ∈ (A.subgroupOf J).map π, a * a = 1) ∧
        ∀ a ∈ (A.subgroupOf J).map π, ∀ ω ∉ D, (a : Perm (Fin n)) ω = ω := by
    intro A hAJ hA4 hAsq D hAs
    have hcardA : Nat.card (A.subgroupOf J) = 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv, hA4]
    have hp : IsPGroup 2 (A.subgroupOf J) := IsPGroup.of_card (n := 2) (by rw [hcardA]; norm_num)
    refine ⟨hcardA, hp, ?_, ?_, ?_⟩
    · rw [SolMax.card_map_of_inf_ker π _ (inf_eq_bot_of_two_odd hp hO), hcardA]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul]
      have : x * x = 1 := Subtype.ext (by rw [Subgroup.coe_mul]; exact hAsq _ hx)
      rw [this, map_one]
    · rintro _ ⟨x, hx, rfl⟩ ω hω
      exact hAs x hx ω hω
  obtain ⟨hA₁, -, hV₁, hV₁sq, hV₁s⟩ := himg E₁ h₁J h₁ h₁sq D₁ h₁s
  obtain ⟨hA₂, hp₂, hV₂, hV₂sq, hV₂s⟩ := himg E₂ h₂J h₂ h₂sq D₂ h₂s
  obtain ⟨σ, hσ⟩ := exists_alt_map_four hn hD₁ hD₂
  have hV : ((E₁.subgroupOf J).map π).map (MulAut.conj σ).toMonoidHom =
      (E₂.subgroupOf J).map π := by
    refine eq_of_support_four hD₂ ?_ hV₂ ?_ hV₂sq ?_ hV₂s
    · rw [Subgroup.card_map_of_injective (MulAut.conj σ).injective, hV₁]
    · rintro _ ⟨τ, hτ, rfl⟩
      change σ * τ * σ⁻¹ * (σ * τ * σ⁻¹) = 1
      have := hV₁sq τ hτ
      calc σ * τ * σ⁻¹ * (σ * τ * σ⁻¹) = σ * (τ * τ) * σ⁻¹ := by group
        _ = 1 := by rw [this]; group
    · rintro _ ⟨τ, hτ, rfl⟩
      exact conj_support hσ (hV₁s τ hτ)
  obtain ⟨j₀, hj₀⟩ := hπ σ
  set A₁' := (E₁.subgroupOf J).map (MulAut.conj j₀).toMonoidHom with hA₁'
  have hA₁'V : A₁'.map π = (E₂.subgroupOf J).map π := by
    rw [hA₁', map_map_conj, hj₀, hV]
  have hle : A₁' ≤ E₂.subgroupOf J ⊔ π.ker := by
    rw [← comap_map_eq, ← hA₁'V]
    exact le_comap_map π A₁'
  have hcard' : Nat.card A₁' = Nat.card (E₂.subgroupOf J) := by
    rw [hA₁', Subgroup.card_map_of_injective (MulAut.conj j₀).injective, hA₁, hA₂]
  obtain ⟨k, -, hk⟩ := exists_conj_of_le_sup_odd hp₂ hO hle hcard'
  refine ⟨((k * j₀ : J) : X), (k * j₀).2, ?_⟩
  have h1 : (E₁.subgroupOf J).map (MulAut.conj (k * j₀)).toMonoidHom = E₂.subgroupOf J := by
    rw [map_conj_mul, ← hA₁', hk]
  have h2 : ((E₁.subgroupOf J).map (MulAut.conj (k * j₀)).toMonoidHom).map J.subtype =
      (E₂.subgroupOf J).map J.subtype := by rw [h1]
  rw [map_subtype_map_conj, Subgroup.subgroupOf_map_subtype, inf_of_le_left h₁J,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left h₂J] at h2
  exact h2

theorem exists_support_conj {X : Type} [Group X] [Finite X] {J : Subgroup X} {n : ℕ}
    (hn : 7 ≤ n) (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) {E : Subgroup X}
    (hEJ : E ≤ J) {D : Finset (Fin n)} (hD : D.card = 4)
    (hDs : ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω)
    {g : X} (hg : g ∈ normalizer (J : Set X)) :
    E.map (MulAut.conj g).toMonoidHom ≤ J ∧ ∃ D' : Finset (Fin n), D'.card = 4 ∧
      ∀ x : J, (x : X) ∈ E.map (MulAut.conj g).toMonoidHom → ∀ ω ∉ D',
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω := by
  classical
  have hJg : J.map (MulAut.conj g).toMonoidHom = J := mem_normalizer_iff_map_conj_eq.mp hg
  refine ⟨hJg ▸ map_mono hEJ, ?_⟩
  let φ : J ≃* J := ((MulAut.conj g).subgroupMap J).trans (MulEquiv.subgroupCongr hJg)
  have hφ : ∀ x : J, ((φ x : J) : X) = g * x * g⁻¹ := fun x => rfl
  have hφO : (pPrimeCore 2 J).map φ.toMonoidHom = pPrimeCore 2 J := pPrimeCore_map_iso 2 φ
  let φb : J ⧸ pPrimeCore 2 J ≃* J ⧸ pPrimeCore 2 J :=
    QuotientGroup.congr (pPrimeCore 2 J) (pPrimeCore 2 J) φ hφO
  let ψ : MulAut (alternatingGroup (Fin n)) := (e.symm.trans φb).trans e
  obtain ⟨τ, hτ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
    (by omega) (by omega)).2 ψ
  have hψ : ∀ a : alternatingGroup (Fin n),
      ((ψ a : alternatingGroup (Fin n)) : Perm (Fin n)) = τ * a * τ⁻¹ := by
    intro a
    rw [← hτ]
    exact MulAut.conjNormal_apply τ a
  refine ⟨D.map τ.toEmbedding, by rw [Finset.card_map, hD], fun y hy ω hω => ?_⟩
  obtain ⟨x, hx, hxy⟩ := hy
  have hxJ : x ∈ J := hEJ hx
  have hy' : y = φ ⟨x, hxJ⟩ := Subtype.ext (by rw [hφ]; exact hxy.symm)
  have hkey : e (y : J ⧸ pPrimeCore 2 J) = ψ (e ((⟨x, hxJ⟩ : J) : J ⧸ pPrimeCore 2 J)) := by
    rw [hy']
    change e (QuotientGroup.mk' _ (φ ⟨x, hxJ⟩)) = e (φb (e.symm (e (QuotientGroup.mk' _ _))))
    rw [MulEquiv.symm_apply_apply]
    rfl
  rw [hkey, hψ]
  have hω' : τ⁻¹ ω ∉ D := by
    intro h
    apply hω
    rw [Finset.mem_map]
    exact ⟨τ⁻¹ ω, h, by simp⟩
  simp only [Perm.mul_apply]
  rw [hDs ⟨x, hxJ⟩ hx _ hω']
  simp

namespace Sig36

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem normalizer_le_normalizer_completion (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) :
    normalizer (J : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  intro g hg
  obtain ⟨hE4, hE2⟩ := card_sq_of_klein S.klein
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hE2 x hx
  obtain ⟨hEgJ, D', hD', hD's⟩ := exists_support_conj (by have := S.nine_le; omega) e S.le S.card
    S.supp hg
  have hEg4 : Nat.card (E.map (MulAut.conj g).toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE4]
  have hEgsq : ∀ x ∈ E.map (MulAut.conj g).toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hEsq x hx, map_one]
  obtain ⟨j, hj, hjE⟩ := exists_conj_four_subgroup (by have := S.nine_le; omega) e S.le hEgJ hE4
    hEg4 hEsq hEgsq S.card hD' S.supp hD's
  have hgj : g⁻¹ * j ∈ normalizer (E : Set X) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change E.map (MulAut.conj (g⁻¹ * j)).toMonoidHom = E
    rw [map_conj_mul, hjE, ← map_conj_mul, inv_mul_cancel]
    ext x
    simp
  have hH1 := normalizer_le_normalizer_signalizerCompletion_self E hgj
  have hH2 := S.le_normalizer_completion h33 h35 hj
  have : g = j * (g⁻¹ * j)⁻¹ := by group
  rw [this]
  exact mul_mem hH2 (inv_mem hH1)

end Sig36

end CFSG.ComponentClassification.SolMax
