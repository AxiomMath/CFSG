module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCF
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCG

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerNineFusionCountReducedInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (E : Subgroup X) (D : Finset (Fin 9)),
    Sig36 X t J 9 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)), IsPermAction θ ρ →
      (∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
        ∀ K : Subgroup X, K ≤ centralizer ({x} : Set X) →
          IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
          IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9))) →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
      (∀ y ∈ S, y * t = t * y) →
      (∀ y ∈ Q, orderOf y = 2 →
        centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∀ x y : X, y ∈ S → y ∉ Q → y ∈ Q.map (MulAut.conj x).toMonoidHom →
        Q ⊓ Q.map (MulAut.conj x).toMonoidHom = ⊥) →
    ∀ s ∈ S, s ∉ Q →
      (∀ s' ∈ S, s' ∉ Q → orderOf s' < orderOf s → ∀ a' ∈ Q, ∀ g' : X, g'⁻¹ * a' * g' ≠ s') →
    ∀ a ∈ Q, ∀ g : X, g⁻¹ * a * g = s → g ∉ normalizer (Sol78.signalizerCompletion E E : Set X) →
      s ∈ normalizer (Q : Set X) → s * s = 1 →
      centralizer ({a} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      (∀ y ∈ Q, y * s = s * y → y ≠ 1 → ∀ hy : g * y * g⁻¹ ∈ normalizer (M : Set X),
        6 ≤ (ρ ⟨g * y * g⁻¹, hy⟩).support.card) →
    ∀ hsN : s ∈ normalizer (M : Set X), ρ ⟨s, hsN⟩ * ρ ⟨s, hsN⟩ = 1 → ρ ⟨s, hsN⟩ ≠ 1 →
      5 ≤ (ρ ⟨s, hsN⟩).support.card → False

theorem signalizerNineFusionCountInvolInput_of_reduced (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hFC : SignalizerNineFusionCountReducedInput) : SignalizerNineFusionCountInvolInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ Q Sc hQK hQ2 hQcard htQ hQS hSH
    hS2 hScard _ s hsS hsQ hmin a ha g hgs hgH hsNQ hs2 hsN hρs2 hρs1 h5
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  obtain ⟨h, hhH, hth, hh⟩ := S₀.exists_conj_central h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup
    hQK hQcard htQ hQS hSH hS2 hScard
  have hhN : h ∈ normalizer (M : Set X) := hHN hhH
  set c : MulAut X := MulAut.conj h⁻¹ with hcdef
  have hc : ∀ x : X, c x = h⁻¹ * x * h := fun x => by simp [hcdef]
  have hcH : ∀ x ∈ H, c x ∈ H := fun x hx => by
    rw [hc]
    exact mul_mem (mul_mem (inv_mem hhH) hx) hhH
  have hcK : ∀ x ∈ UnbalancedLayer.coreActionKernel M,
      c x ∈ UnbalancedLayer.coreActionKernel M := fun x hx => by
    have h1 := UnbalancedLayer.conj_mem_coreActionKernel (inv_mem hhN) hx
    rwa [inv_inv, ← hc] at h1
  set Q₀ := Q.map c.toMonoidHom with hQ₀def
  set S₁ := Sc.map c.toMonoidHom with hS₁def
  have hQ₀K : Q₀ ≤ H ⊓ UnbalancedLayer.coreActionKernel M := by
    rintro _ ⟨q, hq, rfl⟩
    exact mem_inf.mpr ⟨hcH q (hQK hq).1, hcK q (hQK hq).2⟩
  have hQ₀2 : IsPGroup 2 Q₀ := hQ2.map _
  have hQ₀card : Nat.card Q₀ = 2 ^ (Nat.card ↥(H ⊓
      UnbalancedLayer.coreActionKernel M)).factorization 2 := by
    rw [hQ₀def, card_map_of_injective c.injective]
    exact hQcard
  have hhtQ : h * t * h⁻¹ ∈ Q := by
    have htH : t ∈ H := (hQK htQ).1
    have h1 : h * t * h⁻¹ ∈ Sc ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) :=
      mem_inf.mpr ⟨hth, mem_inf.mpr ⟨mul_mem (mul_mem hhH htH) (inv_mem hhH),
        UnbalancedLayer.conj_mem_coreActionKernel hhN (hQK htQ).2⟩⟩
    rwa [inf_kernel_eq_of_sylow hQK hQcard hQS hS2] at h1
  have htQ₀ : t ∈ Q₀ := ⟨h * t * h⁻¹, hhtQ, by rw [MulEquiv.coe_toMonoidHom, hc]; group⟩
  have hQ₀S : Q₀ ≤ S₁ := map_mono hQS
  have hS₁H : S₁ ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact hcH y (hSH hy)
  have hS₁2 : IsPGroup 2 S₁ := hS2.map _
  have hS₁card : Nat.card S₁ = 2 ^ (Nat.card ↥H).factorization 2 := by
    rw [hS₁def, card_map_of_injective c.injective]
    exact hScard
  have htZ : ∀ y ∈ S₁, y * t = t * y := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hh y hy
    rw [MulEquiv.coe_toMonoidHom, hc]
    calc h⁻¹ * y * h * t = h⁻¹ * (y * (h * t * h⁻¹)) * h := by group
      _ = h⁻¹ * (h * t * h⁻¹ * y) * h := by rw [h1]
      _ = t * (h⁻¹ * y * h) := by group
  have hCQ₀ : ∀ y ∈ Q₀, orderOf y = 2 → centralizer ({y} : Set X) ≤ H := fun y hy hyo =>
    S₀.centralizer_le_of_mem_sylow_kernel h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup hQ₀K
      hQ₀card htQ₀ hQ₀S hS₁H hS₁2 hS₁card hy hyo
  have hd3 : ∀ x y : X, y ∈ S₁ → y ∉ Q₀ → y ∈ Q₀.map (MulAut.conj x).toMonoidHom →
      Q₀ ⊓ Q₀.map (MulAut.conj x).toMonoidHom = ⊥ := fun x y hyS hyQ hyx =>
    S₀.inf_conj_eq_bot_of_mem h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup hρ hQ₀K hQ₀2 hQ₀card
      htQ₀ hQ₀S hS₁H hS₁2 hCQ₀ hyS hyQ hyx
  have hNoA9 : ∀ (x : X) (hx : x ∈ M), x * x = 1 →
      (ρ ⟨x, le_normalizer hx⟩).support.card = 4 → ∀ K : Subgroup X,
      K ≤ centralizer ({x} : Set X) → IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
      IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9)) :=
    fun x hx hx2 hx4 K hKC hKpc => ⟨fun θK => S₀.false_of_isPComponent_centralizer_of_four h33 h35
      hT13 hML hSch hMH hMpc hJM hHN hsup θ hρ hx hx2 hx4 hKC hKpc θK⟩
  have hs₀S : c s ∈ S₁ := ⟨s, hsS, rfl⟩
  have hs₀Q : c s ∉ Q₀ := by
    rintro ⟨q, hq, hqs⟩
    apply hsQ
    rwa [c.injective hqs] at hq
  have hmin₀ : ∀ s' ∈ S₁, s' ∉ Q₀ → orderOf s' < orderOf (c s) → ∀ a' ∈ Q₀, ∀ g' : X,
      g'⁻¹ * a' * g' ≠ s' := by
    rintro _ ⟨s'', hs''S, rfl⟩ hs'Q hord _ ⟨a'', ha''Q, rfl⟩ g' heq
    refine hmin s'' hs''S (fun h' => hs'Q ⟨s'', h', rfl⟩) ?_ a'' ha''Q (h * g' * h⁻¹) ?_
    · rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq] at hord
    · have heq' : g'⁻¹ * (h⁻¹ * a'' * h) * g' = h⁻¹ * s'' * h := by
        rw [← hc, ← hc]
        exact heq
      calc (h * g' * h⁻¹)⁻¹ * a'' * (h * g' * h⁻¹) =
          h * (g'⁻¹ * (h⁻¹ * a'' * h) * g') * h⁻¹ := by group
        _ = h * (h⁻¹ * s'' * h) * h⁻¹ := by rw [heq']
        _ = s'' := by group
  have ha₀ : c a ∈ Q₀ := ⟨a, ha, rfl⟩
  have hgs₀ : (c g)⁻¹ * c a * c g = c s := by
    rw [← map_inv, ← map_mul, ← map_mul, hgs]
  have hgH₀ : c g ∉ H := by
    intro h'
    apply hgH
    have h1 := mul_mem (mul_mem hhH h') (inv_mem hhH)
    rwa [hc, show h * (h⁻¹ * g * h) * h⁻¹ = g by group] at h1
  have hsNQ₀ : c s ∈ normalizer (Q₀ : Set X) := by
    rw [mem_normalizer_iff]
    intro y
    have hy : y = c (c.symm y) := (MulEquiv.apply_symm_apply c y).symm
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨s * q * s⁻¹, (mem_normalizer_iff.mp hsNQ q).mp hq, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    · intro hy'
      obtain ⟨q, hq, hqe⟩ := hy'
      refine ⟨s⁻¹ * q * s, ?_, ?_⟩
      · have h1 := (mem_normalizer_iff.mp (inv_mem hsNQ) q).mp hq
        rwa [inv_inv] at h1
      · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv] at hqe ⊢
        rw [hqe]
        group
  have hs₀2 : c s * c s = 1 := by rw [← map_mul, hs2, map_one]
  have hao : orderOf a = 2 := by
    have hags : a = g * s * g⁻¹ := by rw [← hgs]; group
    have ha1 : a ≠ 1 := by
      rintro rfl
      apply hsQ
      rw [← hgs, show g⁻¹ * 1 * g = 1 by group]
      exact one_mem Q
    refine orderOf_eq_prime ?_ ha1
    rw [sq, hags]
    calc g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hCa₀ : centralizer ({c a} : Set X) ≤ H := hCQ₀ (c a) ha₀ (by rw [MulEquiv.orderOf_eq, hao])
  have hd4 : ∀ y ∈ Q₀, y * c s = c s * y → y ≠ 1 →
      ∀ hy : c g * y * (c g)⁻¹ ∈ normalizer (M : Set X),
        6 ≤ (ρ ⟨c g * y * (c g)⁻¹, hy⟩).support.card := fun y hy hys hy1 hyN =>
    S₀.six_le_card_support_of_commute h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup θ hρ hQ₀K hQ₀2
      hQ₀card htQ₀ hQ₀S hS₁H hS₁2 hCQ₀ hs₀S hs₀Q ha₀ hgs₀ hs₀2 hy hys hy1 hyN
  have hs₀N : c s ∈ normalizer (M : Set X) := hHN (hS₁H hs₀S)
  have hkey : ρ ⟨c s, hs₀N⟩ = (ρ ⟨h, hhN⟩)⁻¹ * ρ ⟨s, hsN⟩ * ρ ⟨h, hhN⟩ := by
    have h1 : (⟨c s, hs₀N⟩ : ↥(normalizer (M : Set X))) =
        (⟨h, hhN⟩ : ↥(normalizer (M : Set X)))⁻¹ * ⟨s, hsN⟩ * ⟨h, hhN⟩ :=
      Subtype.ext (by change c s = h⁻¹ * s * h; exact hc s)
    rw [h1, map_mul, map_mul, map_inv]
  have hρs₀2 : ρ ⟨c s, hs₀N⟩ * ρ ⟨c s, hs₀N⟩ = 1 := by
    rw [hkey]
    calc (ρ ⟨h, hhN⟩)⁻¹ * ρ ⟨s, hsN⟩ * ρ ⟨h, hhN⟩ * ((ρ ⟨h, hhN⟩)⁻¹ * ρ ⟨s, hsN⟩ * ρ ⟨h, hhN⟩)
        = (ρ ⟨h, hhN⟩)⁻¹ * (ρ ⟨s, hsN⟩ * ρ ⟨s, hsN⟩) * ρ ⟨h, hhN⟩ := by group
      _ = 1 := by rw [hρs2]; group
  have hρs₀1 : ρ ⟨c s, hs₀N⟩ ≠ 1 := by
    rw [hkey]
    intro h1
    apply hρs1
    calc ρ ⟨s, hsN⟩ = ρ ⟨h, hhN⟩ * ((ρ ⟨h, hhN⟩)⁻¹ * ρ ⟨s, hsN⟩ * ρ ⟨h, hhN⟩) *
        (ρ ⟨h, hhN⟩)⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have h5₀ : 5 ≤ (ρ ⟨c s, hs₀N⟩).support.card := by
    rw [hkey]
    have h1 := Perm.card_support_conj (σ := (ρ ⟨h, hhN⟩)⁻¹) (τ := ρ ⟨s, hsN⟩)
    rw [inv_inv] at h1
    rw [h1]
    exact h5
  exact hFC X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q₀ S₁ hQ₀K hQ₀2 hQ₀card htQ₀
    hQ₀S hS₁H hS₁2 hS₁card htZ hCQ₀ hd3 (c s) hs₀S hs₀Q hmin₀ (c a) ha₀ (c g) hgs₀ hgH₀ hsNQ₀
    hs₀2 hCa₀ hd4 hs₀N hρs₀2 hρs₀1 h5₀

theorem signalizerNineFusionCountInput_of_reduced (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hFC : SignalizerNineFusionCountReducedInput) : SignalizerNineFusionCountInput :=
  signalizerNineFusionCountInput_of_involution h33 h35 hT13 hML hSch
    (signalizerNineFusionCountInvolInput_of_reduced h33 h35 hT13 hML hSch hFC)

end CFSG.ComponentClassification.SolMax
