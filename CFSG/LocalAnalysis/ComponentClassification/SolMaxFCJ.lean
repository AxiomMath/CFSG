module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCI
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveN

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped Pointwise

variable {X : Type} [Group X]

theorem exists_conj_le_of_card_eq_of_le [Finite X] {H Sc B : Subgroup X} (hSH : Sc ≤ H)
    (hScard : Nat.card Sc = 2 ^ (Nat.card H).factorization 2) (hBH : B ≤ H)
    (hB2 : IsPGroup 2 B) : ∃ h ∈ H, ∀ b ∈ B, h * b * h⁻¹ ∈ Sc := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁ : Nat.card (Sc.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv, hScard]
  have hB₁ : IsPGroup 2 (B.subgroupOf H) := hB2.of_equiv (subgroupOfEquivOfLe hBH).symm
  obtain ⟨T, hT⟩ := hB₁.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H T (Sylow.ofCard _ hS₁)
  refine ⟨h, h.2, fun b hb => ?_⟩
  have key : ((h • T : Sylow 2 H) : Subgroup H) = Sc.subgroupOf H := by
    rw [hh, Sylow.coe_ofCard]
  rw [Sylow.coe_subgroup_smul] at key
  have h1 : MulAut.conj h • (⟨b, hBH hb⟩ : H) ∈ MulAut.conj h • (T : Subgroup H) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hT (show (⟨b, hBH hb⟩ : H) ∈ B.subgroupOf H from hb))
  rw [key] at h1
  simpa [MulAut.smul_def, MulAut.conj_apply, mem_subgroupOf] using h1

theorem apply_conj_of_mem_normalizer {M : Subgroup X} {G : Type*} [Group G]
    (ρ : ↥(normalizer (M : Set X)) →* G) {h y : X} (hh : h ∈ normalizer (M : Set X))
    (hy : y ∈ normalizer (M : Set X)) (hhy : h * y * h⁻¹ ∈ normalizer (M : Set X)) :
    ρ ⟨h * y * h⁻¹, hhy⟩ = ρ ⟨h, hh⟩ * ρ ⟨y, hy⟩ * (ρ ⟨h, hh⟩)⁻¹ := by
  have h1 : (⟨h * y * h⁻¹, hhy⟩ : ↥(normalizer (M : Set X))) =
      (⟨h, hh⟩ : ↥(normalizer (M : Set X))) * ⟨y, hy⟩ * (⟨h, hh⟩)⁻¹ :=
    Subtype.ext rfl
  rw [h1, map_mul, map_mul, map_inv]

@[expose] def SignalizerNineFusionCountSplitInput : Prop :=
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
    ∀ s ∈ S, s ∉ Q → ∀ g : X, g⁻¹ * t * g = s →
      g ∉ normalizer (Sol78.signalizerCompletion E E : Set X) → s * s = 1 →
      (∀ y ∈ Q, y * s = s * y → y ≠ 1 → ∀ hy : g * y * g⁻¹ ∈ normalizer (M : Set X),
        6 ≤ (ρ ⟨g * y * g⁻¹, hy⟩).support.card) →
    ∀ hsN : s ∈ normalizer (M : Set X), ρ ⟨s, hsN⟩ * ρ ⟨s, hsN⟩ = 1 → ρ ⟨s, hsN⟩ ≠ 1 →
      5 ≤ (ρ ⟨s, hsN⟩).support.card →
      (ρ ⟨s, hsN⟩ ∈ alternatingGroup (Fin 9) → ∃ q ∈ Q, ∃ m ∈ S, m ∈ M ∧
        (∀ y ∈ Q, y * m = m * y) ∧ s = q * m) → False

theorem signalizerNineFusionCountCentralInput_of_split (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hFC : SignalizerNineFusionCountSplitInput) : SignalizerNineFusionCountCentralInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 hρs1 h5
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  by_cases hsA : ρ ⟨s, hsN⟩ ∈ alternatingGroup (Fin 9)
  swap
  · exact hFC X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
      hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 hρs1 h5
      (fun h => absurd h hsA)
  have hKQ := inf_kernel_eq_of_sylow hQK hQcard hQS hS2
  have hsNQ : s ∈ normalizer (Q : Set X) :=
    le_normalizer_of_sylow_kernel hHN hQK hQcard hQS hSH hS2 hsS
  set B₀ := Q ⊔ zpowers s with hB₀def
  have hB₀2 : IsPGroup 2 B₀ :=
    hQ2.to_sup_of_normal_left' (isPGroup_zpowers_of_mul_self hs2) (zpowers_le.mpr hsNQ)
  have hB₀H : B₀ ≤ H := sup_le (hQK.trans inf_le_left) (zpowers_le.mpr (hSH hsS))
  have hB₀N : B₀ ≤ normalizer (M : Set X) := hB₀H.trans hHN
  have hb : ∀ (y : X) (hy : y ∈ B₀),
      ρ ⟨s, hsN⟩ * ρ ⟨y, hB₀N hy⟩ = ρ ⟨y, hB₀N hy⟩ * ρ ⟨s, hsN⟩ := by
    set Z : Subgroup X := ((centralizer ({ρ ⟨s, hsN⟩} : Set (Perm (Fin 9)))).comap ρ).map
      (normalizer (M : Set X)).subtype with hZdef
    have hQZ : Q ≤ Z := fun q hq => by
      refine ⟨⟨q, hHN (hQK hq).1⟩, ?_, rfl⟩
      have h1 : ρ ⟨q, hHN (hQK hq).1⟩ = 1 :=
        hρ.eq_one_of_mem_coreActionKernel (by norm_num) (hQK hq).2
      show ρ ⟨q, hHN (hQK hq).1⟩ ∈ centralizer ({ρ ⟨s, hsN⟩} : Set (Perm (Fin 9)))
      rw [h1]
      exact one_mem _
    have hsZ : s ∈ Z := ⟨⟨s, hsN⟩, mem_comap.mpr (mem_centralizer_singleton_iff.mpr rfl), rfl⟩
    intro y hy
    obtain ⟨y', hy', hyy⟩ := sup_le hQZ (zpowers_le.mpr hsZ) hy
    have h1 : (⟨y, hB₀N hy⟩ : ↥(normalizer (M : Set X))) = y' := Subtype.ext hyy.symm
    rw [h1]
    exact (mem_centralizer_singleton_iff.mp (mem_comap.mp hy')).symm
  obtain ⟨x, hxC, hxθ⟩ := hρ.exists_lift_of_isPGroup hB₀N hB₀2 (b := ⟨ρ ⟨s, hsN⟩, hsA⟩) hb
  have hρx : ρ ⟨x, le_normalizer x.2⟩ = ρ ⟨s, hsN⟩ := by
    rw [hρ.apply_of_mem (by norm_num) x, hxθ]
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : X)).ne'
  set x₂ : X := (x : X) ^ m with hx₂def
  have hx₂M : x₂ ∈ M := pow_mem x.2 m
  have hx₂C : x₂ ∈ centralizer (B₀ : Set X) := pow_mem hxC m
  have hx₂2 : IsPGroup 2 (zpowers x₂) := by
    have h1 : x₂ ^ 2 ^ k = 1 := by
      rw [hx₂def, ← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hρx₂ : ρ ⟨x₂, le_normalizer hx₂M⟩ = ρ ⟨s, hsN⟩ := by
    have h1 : (⟨x₂, le_normalizer hx₂M⟩ : ↥(normalizer (M : Set X))) =
        (⟨x, le_normalizer x.2⟩ : ↥(normalizer (M : Set X))) ^ m :=
      Subtype.ext (by simp [hx₂def])
    obtain ⟨j, rfl⟩ := hm
    rw [h1, map_pow, hρx, pow_succ, pow_mul, sq, hρs2, one_pow, one_mul]
  set B₁ := B₀ ⊔ zpowers x₂ with hB₁def
  have hB₁2 : IsPGroup 2 B₁ := hB₀2.to_sup_of_normal_left' hx₂2
    (zpowers_le.mpr (Subgroup.centralizer_le_normalizer (B₀ : Set X) hx₂C))
  have hB₁H : B₁ ≤ H := sup_le hB₀H (zpowers_le.mpr (hMH hx₂M))
  obtain ⟨h, hhH, hh⟩ := exists_conj_le_of_card_eq_of_le hSH hScard hB₁H hB₁2
  have hhN : h ∈ normalizer (M : Set X) := hHN hhH
  have hQB₁ : Q ≤ B₁ := le_sup_left.trans le_sup_left
  have hhQ : ∀ y ∈ Q, h * y * h⁻¹ ∈ Q := fun y hy => by
    have h1 : h * y * h⁻¹ ∈ Sc ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) :=
      mem_inf.mpr ⟨hh y (hQB₁ hy), mem_inf.mpr ⟨mul_mem (mul_mem hhH (hQK hy).1) (inv_mem hhH),
        UnbalancedLayer.conj_mem_coreActionKernel hhN (hQK hy).2⟩⟩
    rwa [hKQ] at h1
  have hQmap : Q.map (MulAut.conj h).toMonoidHom = Q := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj h).injective).ge
    rintro _ ⟨y, hy, rfl⟩
    exact hhQ y hy
  have hhQ' : ∀ y ∈ Q, h⁻¹ * y * h ∈ Q := fun y hy => by
    rw [← hQmap] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simpa [MulAut.conj_apply, mul_assoc] using hz
  set s'' := h * s * h⁻¹ with hs''def
  set mm := h * x₂ * h⁻¹ with hmmdef
  have hs''S : s'' ∈ Sc := hh s (mem_sup_left (mem_sup_right (mem_zpowers s)))
  have hmmS : mm ∈ Sc := hh x₂ (mem_sup_right (mem_zpowers x₂))
  have hmmM : mm ∈ M := (mem_normalizer_iff.mp hhN x₂).mp hx₂M
  have hmmC : ∀ y ∈ Q, y * mm = mm * y := fun y hy => by
    have h1 := mem_centralizer_iff.mp hx₂C (h⁻¹ * y * h) (mem_sup_left (hhQ' y hy))
    rw [hmmdef]
    calc y * (h * x₂ * h⁻¹) = h * ((h⁻¹ * y * h) * x₂) * h⁻¹ := by group
      _ = h * (x₂ * (h⁻¹ * y * h)) * h⁻¹ := by rw [h1]
      _ = h * x₂ * h⁻¹ * y := by group
  have hs''N : s'' ∈ normalizer (M : Set X) := hHN (hSH hs''S)
  have hmmN : mm ∈ normalizer (M : Set X) := le_normalizer hmmM
  have hρs'' : ρ ⟨s'', hs''N⟩ = ρ ⟨h, hhN⟩ * ρ ⟨s, hsN⟩ * (ρ ⟨h, hhN⟩)⁻¹ :=
    apply_conj_of_mem_normalizer ρ hhN hsN hs''N
  have hρmm : ρ ⟨mm, hmmN⟩ = ρ ⟨h, hhN⟩ * ρ ⟨s, hsN⟩ * (ρ ⟨h, hhN⟩)⁻¹ := by
    rw [apply_conj_of_mem_normalizer ρ hhN (le_normalizer hx₂M) hmmN, hρx₂]
  set q := s'' * mm⁻¹ with hqdef
  have hqQ : q ∈ Q := by
    have hqS : q ∈ Sc := mul_mem hs''S (inv_mem hmmS)
    have hqN : q ∈ normalizer (M : Set X) := mul_mem hs''N (inv_mem hmmN)
    have hρq : ρ ⟨q, hqN⟩ = 1 := by
      have h1 : (⟨q, hqN⟩ : ↥(normalizer (M : Set X))) = ⟨s'', hs''N⟩ * (⟨mm, hmmN⟩)⁻¹ :=
        Subtype.ext rfl
      rw [h1, map_mul, map_inv, hρs'', hρmm, mul_inv_cancel]
    have h1 : q ∈ Sc ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) :=
      mem_inf.mpr ⟨hqS, mem_inf.mpr ⟨hSH hqS, hρ.mem_coreActionKernel hqN hρq⟩⟩
    rwa [hKQ] at h1
  have hs''qm : s'' = q * mm := by rw [hqdef]; group
  set g'' := g * h⁻¹ with hg''def
  have hgs'' : g''⁻¹ * t * g'' = s'' := by rw [hg''def, hs''def, ← hgs]; group
  have hgH'' : g'' ∉ H := by
    intro h'
    apply hgH
    have h1 := mul_mem h' hhH
    rwa [hg''def, inv_mul_cancel_right] at h1
  have hs''2 : s'' * s'' = 1 := by
    rw [hs''def]
    calc h * s * h⁻¹ * (h * s * h⁻¹) = h * (s * s) * h⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hρs''1 : ρ ⟨s'', hs''N⟩ ≠ 1 := by
    rw [hρs'']
    intro h1
    apply hρs1
    calc ρ ⟨s, hsN⟩ = (ρ ⟨h, hhN⟩)⁻¹ * (ρ ⟨h, hhN⟩ * ρ ⟨s, hsN⟩ * (ρ ⟨h, hhN⟩)⁻¹) *
        ρ ⟨h, hhN⟩ := by group
      _ = 1 := by rw [h1]; group
  have hs''Q : s'' ∉ Q := fun h1 =>
    hρs''1 (hρ.eq_one_of_mem_coreActionKernel (by norm_num) (hQK h1).2)
  have hρs''2 : ρ ⟨s'', hs''N⟩ * ρ ⟨s'', hs''N⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨s'', hs''N⟩ : ↥(normalizer (M : Set X))) * ⟨s'', hs''N⟩ = 1 := Subtype.ext hs''2
    rw [h1, map_one]
  have h5'' : 5 ≤ (ρ ⟨s'', hs''N⟩).support.card := by
    rw [hρs'', Perm.card_support_conj]
    exact h5
  have hd4'' : ∀ y ∈ Q, y * s'' = s'' * y → y ≠ 1 →
      ∀ hy : g'' * y * g''⁻¹ ∈ normalizer (M : Set X),
        6 ≤ (ρ ⟨g'' * y * g''⁻¹, hy⟩).support.card := fun y hy hys hy1 hyN =>
    S₀.six_le_card_support_of_commute h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup θ hρ hQK hQ2
      hQcard htQ hQS hSH hS2 hCQ hs''S hs''Q htQ hgs'' hs''2 hy hys hy1 hyN
  exact hFC X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s'' hs''S hs''Q g'' hgs'' hgH'' hs''2 hd4'' hs''N hρs''2 hρs''1 h5''
    (fun _ => ⟨q, hqQ, mm, hmmS, hmmM, hmmC, hs''qm⟩)

theorem signalizerNineFusionCountReducedInput_of_split (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hFC : SignalizerNineFusionCountSplitInput) : SignalizerNineFusionCountReducedInput :=
  signalizerNineFusionCountReducedInput_of_central h33 h35 hT13 hML hSch
    (signalizerNineFusionCountCentralInput_of_split h33 h35 hT13 hML hSch hFC)

end CFSG.ComponentClassification.SolMax
