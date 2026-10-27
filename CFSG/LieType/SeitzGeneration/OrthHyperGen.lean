module

public import CFSG.LieType.SeitzGeneration.OrthHyperRoot
public import CFSG.LieType.SeitzGeneration.OrthHyperFixed
public import CFSG.LieType.SeitzGeneration.SpHyperGen
public import CFSG.LieType.SeitzGeneration.UnitaryHyperGen

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem hyperGen_top_of_singular_stable (hQ : (polarBilin Q).Nondegenerate)
    {G : Subgroup (V ≃ₗ[K] V)} (hGE : G = elementaryGroup Q) {P : Type} [Group P] (π : G →* P)
    (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hker : ¬ p ∣ Nat.card π.ker) {E : Subgroup P} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) {W : Submodule K V} (hW0 : W ≠ ⊥) (hW : ∀ x ∈ W, Q x = 0)
    (hstab : ∀ g : G, π g ∈ E → ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W) :
    (⊤ : Subgroup P) ≤ Subgroup.closure {k : P | k ∈ (⊤ : Subgroup P) ∧
      ∃ F₀ : Subgroup P, F₀ ≤ E ∧ F₀.relIndex E = p ∧ ∀ f ∈ F₀, f * k = k * f} := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hfinV : Finite V := Module.finite_of_finite K
  have hfinGL : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g => (g : V → V)) DFunLike.coe_injective
  have hfinP : Finite P := Finite.of_surjective π hπ
  have hGO : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hGE]
    exact elementaryGroup_le_orthogonalGroup Q
  have hEG : ∀ u w, eichler Q u w ∈ G := fun u w => by
    rw [hGE]
    exact eichler_mem_elementaryGroup Q u w
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨A, hAE, hAdis, hAcomm, hAexp, hAcard⟩ :=
    exists_lift_elemAbelian π hπ hker hcomm hE.2
  have hAcardp : Nat.card A = p ^ 3 := hAcard.trans hcard
  let ρ : A →* Module.End K V := (autToEnd K V).comp (G.subtype.comp A.subtype)
  have hAc : ∀ a b : A, a * b = b * a := fun a b => Subtype.ext (hAcomm a a.2 b b.2)
  have hAp : ∀ a : A, a ^ p = 1 := fun a => Subtype.ext (hAexp a a.2)
  have hAmem : ∀ a : A, π a.1 ∈ E := fun a => by
    rw [← hAE]
    exact Subgroup.mem_map_of_mem _ a.2
  have hAstab : ∀ a : A, ∀ w ∈ W, ρ a w ∈ W := fun a w hw => hstab a.1 (hAmem a) w hw
  obtain ⟨F', hF'idx, hW1⟩ : ∃ F' : Subgroup A, F'.index = p ∧ hyperFixed ρ F' ⊓ W ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hmem := mem_iSup_hyperFixed_top hpK hAc hAp ρ W hAstab (k := 3) (by norm_num) hAcardp hm
    have hbot : (⨆ (F' : Subgroup A) (_ : F'.index = p), hyperFixed ρ F' ⊓ W) = ⊥ :=
      iSup_eq_bot.2 fun F' => iSup_eq_bot.2 fun hF' => hcon F' hF'
    rw [hbot] at hmem
    exact hm0 (by simpa using hmem)
  set C : Submodule K V := hyperFixed ρ F' with hC
  set X₁ : Submodule K V := hyperFixed ρ F' ⊓ W with hX₁
  have hX₁mem : ∀ v, v ∈ X₁ ↔ (∀ f ∈ F', ρ f v = v) ∧ v ∈ W := fun v => by
    rw [hX₁, Submodule.mem_inf, mem_hyperFixed]
  have hX₁C : X₁ ≤ C := inf_le_left
  have hX₁Q : ∀ x ∈ X₁, Q x = 0 := fun x hx => hW x ((hX₁mem x).1 hx).2
  set Kset : Subgroup P := Subgroup.closure {k : P | k ∈ (⊤ : Subgroup P) ∧
    ∃ F₀ : Subgroup P, F₀ ≤ E ∧ F₀.relIndex E = p ∧ ∀ f ∈ F₀, f * k = k * f} with hKset
  set H : Subgroup G := Kset.comap π with hH
  set HV : Subgroup (V ≃ₗ[K] V) := H.map G.subtype with hHV
  have hHVO : HV ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨x, -, rfl⟩
    exact hGO x.2
  have hmemHV : ∀ x : G, π x ∈ Kset → (x : V ≃ₗ[K] V) ∈ HV := fun x hx => ⟨x, hx, rfl⟩
  have hF₀E : F'.map (π.comp A.subtype) ≤ E := by
    rintro _ ⟨f, -, rfl⟩
    exact hAmem f
  have hF₀rel := relIndex_map_lift hAE hAdis hF'idx
  have hcent : ∀ x : G, (∀ f : F', ((f.1 : G) : V ≃ₗ[K] V) * (x : V ≃ₗ[K] V) =
      (x : V ≃ₗ[K] V) * ((f.1 : G) : V ≃ₗ[K] V)) → (x : V ≃ₗ[K] V) ∈ HV := by
    intro x hx
    refine hmemHV x (Subgroup.subset_closure ⟨Subgroup.mem_top _, F'.map (π.comp A.subtype),
      hF₀E, hF₀rel, ?_⟩)
    rintro _ ⟨f, hf, rfl⟩
    show π f.1 * π x = π x * π f.1
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hx ⟨f, hf⟩))
  let φ : F' →* (V ≃ₗ[K] V) := (G.subtype.comp A.subtype).comp F'.subtype
  have hφ : ∀ f, φ f ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun f => hGO f.1.1.2
  have hqfix : qFix φ = C := by
    ext v
    rw [mem_qFix, hC, mem_hyperFixed]
    exact ⟨fun h n hn => h ⟨n, hn⟩, fun h f => h f.1 f.2⟩
  have : Fintype F' := Fintype.ofFinite F'
  have hcardF' : Nat.card F' = p ^ 2 := by
    have h := Subgroup.card_mul_index F'
    rw [hF'idx, hAcardp] at h
    have h2 : Nat.card F' * p = p ^ 2 * p := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos h2
  have hF : ((Fintype.card F' : ℕ) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hcardF', Nat.cast_pow]
    exact pow_ne_zero 2 hpK
  have hS : RootSetup Q HV C := by
    refine ⟨hHVO, hqfix ▸ polarNondegOn_qFix hQ hφ hF, fun v => ?_, fun u hu w hw => ?_⟩
    · exact ⟨qAvg φ v, hqfix ▸ qAvg_mem φ v, hqfix ▸ sub_qAvg_mem_qPerp hφ hF v⟩
    · by_cases h : Q u = 0 ∧ polar Q u w = 0
      · refine hcent ⟨eichler Q u w, hEG u w⟩ fun f => ?_
        refine commute_eichler_of_fix (hGO f.1.1.2) ?_ ?_
        · exact mem_hyperFixed.1 hu f.1 f.2
        · exact mem_hyperFixed.1 hw f.1 f.2
      · rw [eichler_of_not h]
        exact HV.one_mem
  set 𝒜 : Subgroup (V ≃ₗ[K] V) := A.map G.subtype with h𝒜
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
      (∀ a ∈ 𝒜, ∀ x ∈ X, a x ∈ X) → ∀ x ∈ X, ∀ d ∈ qPerp Q X, eichler Q x d ∈ HV := by
    intro X _ hXQ hX𝒜 x hx d hd
    set Qx : Subgroup G := (qRad Q X hXQ).comap G.subtype with hQx
    have hnorm : ∀ e ∈ E, ∀ v ∈ Qx.map π, e * v * e⁻¹ ∈ Qx.map π := by
      intro e he v hv
      rw [← hAE] at he
      obtain ⟨a, ha, rfl⟩ := he
      obtain ⟨q, hq, rfl⟩ := hv
      refine ⟨a * q * a⁻¹, ?_, by simp⟩
      have haS : ∀ y ∈ X, ((a : G) : V ≃ₗ[K] V) y ∈ X := fun y hy => hX𝒜 _ ⟨a, ha, rfl⟩ y hy
      have haS' : ∀ y ∈ X, ((a : G) : V ≃ₗ[K] V)⁻¹ y ∈ X := fun y hy =>
        hX𝒜 _ ⟨a⁻¹, A.inv_mem ha, rfl⟩ y hy
      exact qRad_conj_mem (hX := hXQ) (hGO a.2) haS haS' hq
    have hQp : ¬ p ∣ Nat.card (Qx.map π) := fun hd' =>
      not_dvd_card_comap_qRad (hX := hXQ) hp hp2 hpK G (hd'.trans (Subgroup.card_map_dvd _ π))
    have hle := le_hyperClosure_of_normalized hp hE hcard hnorm hQp
    have hmem : (⟨eichler Q x d, hEG x d⟩ : G) ∈ Qx :=
      eichler_mem_qRad (hX := hXQ) hx hd
    exact hmemHV _ (hle (Subgroup.mem_map_of_mem _ hmem))
  obtain ⟨e₀, he₀, he₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW1
  obtain ⟨a, b, ha, hb, hab⟩ := exists_rootCenter_pair hS h𝒜O hC𝒜 hrad hX₁C hX₁Q hX₁𝒜 he₀ he₀0
  let P₀ : HypPair Q :=
    { e := a
      f := (polar Q a b)⁻¹ • b
      Q_e := ha.2.1
      Q_f := by rw [map_smul_eq_sq, hb.2.1, mul_zero]
      polar_ef := by rw [polar_smul_right_eq, inv_mul_cancel₀ hab] }
  have hle : elementaryGroup Q ≤ HV :=
    elementaryGroup_le_of_hypPair hQ hHVO P₀ ha (hb.smul (inv_ne_zero hab))
  intro k _
  obtain ⟨g, rfl⟩ := hπ k
  obtain ⟨x, hx, hxg⟩ := hle (by rw [← hGE]; exact g.2)
  have : x = g := Subtype.ext hxg
  rw [this] at hx
  exact hx

end CFSG.LieType.SeitzGeneration
