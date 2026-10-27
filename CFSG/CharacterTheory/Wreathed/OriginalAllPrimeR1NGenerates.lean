module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeR1NCentralizer
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeR1NDickson
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeR1NLinear

public section

namespace CFSG.Wreathed.OriginalAllPrime.R1NFacts

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.OriginalAllPrime.ModelSignalizers CFSG.Wreathed.CentralSL2

theorem torus_le_of_le {F : Type} [Field F] [Finite F]
    {W K : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hW : ∀ g, g ∈ W ↔ g ∈ Subgroup.centralizer {weyl F} ∧ Odd (orderOf g)) (hWK : W ≤ K)
    (h2K : ∀ t ∈ Subgroup.centralizer {weyl F}, ∀ s : ℕ, t ^ 2 ^ s = 1 → t ∈ K) :
    Subgroup.centralizer {weyl F} ≤ K := by
  intro t ht
  have hpos : orderOf t ≠ 0 := (orderOf_pos t).ne'
  obtain ⟨a, c, hc, hn⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  have h1 : t ^ 2 ^ a ∈ K := by
    apply hWK
    rw [hW]
    refine ⟨Subgroup.pow_mem _ ht _, ?_⟩
    apply Odd.of_dvd_nat hc
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← hn, pow_orderOf_eq_one]
  have h2 : t ^ c ∈ K := by
    apply h2K _ (Subgroup.pow_mem _ ht _) a
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have hcop : Nat.Coprime (2 ^ a) c := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hc)
  have hbez := Nat.gcd_eq_gcd_ab (2 ^ a) c
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  have ht' : t = (t ^ 2 ^ a) ^ (Nat.gcdA (2 ^ a) c) * (t ^ c) ^ (Nat.gcdB (2 ^ a) c) := by
    rw [← _root_.zpow_natCast t (2 ^ a), ← _root_.zpow_natCast t c, ← _root_.zpow_mul,
      ← _root_.zpow_mul, ← _root_.zpow_add,
      ← hbez, zpow_one]
  rw [ht']
  exact K.mul_mem (K.zpow_mem h1 _) (K.zpow_mem h2 _)

theorem mem_normalizer_of_forall_conj_eq {G : Type*} [Group G] {X : Subgroup G} {t : G}
    (h : ∀ x ∈ X, t * x * t⁻¹ = x) : t ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h x hx]
    exact hx
  · intro hx
    have h1 := h _ hx
    have h2 : t * x * t⁻¹ = x := by
      have h3 := congrArg (fun z => t⁻¹ * z * t) h1
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at h3
      simpa only [mul_assoc] using h3
    rw [← h2]
    exact hx

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem exists_conj_mem_range_inr {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (hm2 : m = 2 ^ padicValInt 2 ((p ^ f : ℕ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1)))
    (hd : Odd (Nat.card Sigma)) (hb : ¬ IsSquare b)
    {W : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hW : ∀ g, g ∈ W ↔ g ∈ Subgroup.centralizer {weyl F} ∧ Odd (orderOf g))
    {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hX : IsPGroup p X)
    (hXC : X ≤ modelC b m hm heven Sigma hSigma) :
    ∃ w ∈ W, ∀ x ∈ X, ∃ σ : Sigma,
      (SemidirectProduct.inl (specialInclusion F b m hm heven w))⁻¹ * x *
        SemidirectProduct.inl (specialInclusion F b m hm heven w) = SemidirectProduct.inr σ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
  have hred :=
    ReducedInvolution.reduced_noncentral_involution_centralizer_has_exact_odd_torus_field_complement
    hp hpodd hf hcard _ rfl m hm heven hm2 Sigma hd b hSigma hb
  dsimp only at hred
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hWall⟩ := hred
  obtain ⟨-, ⟨φ, hφ⟩, hφall⟩ := hWall W hW
  obtain ⟨⟨Ψ, hΨ⟩, -, -, -⟩ := hφall φ hφ
  set ψ : W ⋊[φ] Sigma →* SemilinearExtension F b m hm heven Sigma hSigma :=
    (Subgroup.subtype _).comp Ψ.toMonoidHom with hψdef
  have hψ : ∀ y, ψ y = SemidirectProduct.inl (specialInclusion F b m hm heven y.left) *
      SemidirectProduct.inr y.right := fun y => hΨ y
  have hψinj : Function.Injective ψ := (Subgroup.subtype_injective _).comp Ψ.injective
  have : Finite (W ⋊[φ] Sigma) := Finite.of_injective ψ hψinj
  have hXψ : ∀ x ∈ X, ∃ y, ψ y = x := by
    intro x hx
    obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
    have hk' : x ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨w', hw', σ', rfl⟩ := exists_eq_inl_mul_inr hp hpodd hf hcard hm2 hd hb hW (hXC hx)
      hpodd.pow hk'
    exact ⟨SemidirectProduct.inl ⟨w', hw'⟩ * SemidirectProduct.inr σ', by rw [hψ]; simp⟩
  set Xt := X.comap ψ
  have hXt : IsPGroup p Xt := hX.comap_of_injective ψ hψinj
  have hWp : ¬ p ∣ Nat.card W := by
    intro hpW
    have hTcard := CFSG.Wreathed.OddFieldTorus.torus_card (L := F) h2
    have hWT : Nat.card W ∣ Nat.card (CFSG.Wreathed.OddFieldTorus.torus F) :=
      Subgroup.card_dvd_of_le (CFSG.Wreathed.OddFieldTorus.W_le_torus W hW)
    obtain ⟨c, hc⟩ := hpW.trans hWT
    have hpq : (p : ℤ) ∣ (p ^ f : ℕ) := by exact_mod_cast dvd_pow_self p (by omega)
    rw [hcard] at hTcard
    have hpe : (p : ℤ) ∣ (if p ^ f % 4 = 1 then (1 : ℤ) else -1) := by
      have h1 : (p : ℤ) ∣ ((p ^ f : ℕ) : ℤ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1) :=
        ⟨c, by rw [← hTcard, hc]; push_cast; ring⟩
      have := dvd_sub hpq h1
      simpa using this
    have hp1 : (p : ℤ) ∣ 1 := by
      split_ifs at hpe
      · exact hpe
      · exact (dvd_neg).mp hpe
    have := Int.eq_one_of_dvd_one (by positivity) hp1
    have : p = 1 := by exact_mod_cast this
    exact hp.one_lt.ne' this
  obtain ⟨Psig⟩ : Nonempty (Sylow p Sigma) := inferInstance
  set S₀ := (Psig : Subgroup Sigma).map (SemidirectProduct.inr : Sigma →* W ⋊[φ] Sigma)
  have hS₀card : Nat.card S₀ = p ^ (Nat.card (W ⋊[φ] Sigma)).factorization p := by
    rw [Subgroup.card_map_of_injective SemidirectProduct.inr_injective,
      Sylow.card_eq_multiplicity, SemidirectProduct.card,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hWp, zero_add]
  let S : Sylow p (W ⋊[φ] Sigma) := Sylow.ofCard S₀ hS₀card
  obtain ⟨P, hXtP⟩ := hXt.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (W ⋊[φ] Sigma) S P
  obtain ⟨a, c, rfl⟩ : ∃ (a : W) (c : Sigma),
      g = SemidirectProduct.inl a * SemidirectProduct.inr c :=
    ⟨g.left, g.right, (SemidirectProduct.inl_left_mul_inr_right g).symm⟩
  refine ⟨(a : SpecialLinearGroup (Fin 2) F), a.2, ?_⟩
  intro x hx
  obtain ⟨y, rfl⟩ := hXψ x hx
  have hyP : y ∈ (P : Subgroup (W ⋊[φ] Sigma)) := hXtP hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyP
  change (MulAut.conj _)⁻¹ y ∈ (S : Subgroup (W ⋊[φ] Sigma)) at hyP
  rw [Sylow.coe_ofCard, MulAut.inv_def, MulAut.conj_symm_apply] at hyP
  obtain ⟨s, -, hs⟩ := hyP
  have hy : y = (SemidirectProduct.inl a * SemidirectProduct.inr c) * SemidirectProduct.inr s *
      (SemidirectProduct.inl a * SemidirectProduct.inr c)⁻¹ := by
    rw [hs]
    group
  refine ⟨c * s * c⁻¹, ?_⟩
  have hgl : SemidirectProduct.inl (specialInclusion F b m hm heven
      (a : SpecialLinearGroup (Fin 2) F)) = ψ (SemidirectProduct.inl a) := by
    rw [hψ]
    simp
  have hinr : ∀ τ : Sigma, (SemidirectProduct.inr τ :
      SemilinearExtension F b m hm heven Sigma hSigma) = ψ (SemidirectProduct.inr τ) := by
    intro τ
    rw [hψ]
    simp
  rw [hgl, hinr, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [hy]
  simp only [_root_.mul_inv_rev, map_mul, map_inv]
  group

theorem le_sup_normalizer
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (hm2 : m = 2 ^ padicValInt 2 ((p ^ f : ℕ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1)))
    (hd : Odd (Nat.card Sigma)) (hdvd : Nat.card Sigma ∣ f)
    (hcomm : ∀ σ τ : Sigma, σ * τ = τ * σ) (hb : ¬ IsSquare b)
    {W : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hW : ∀ g, g ∈ W ↔ g ∈ Subgroup.centralizer {weyl F} ∧ Odd (orderOf g))
    {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hX : IsPGroup p X)
    (hXC : X ≤ modelC b m hm heven Sigma hSigma)
    {M : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hM : ModelSignalizers.modelBase b m hm heven Sigma hSigma ≤ M) :
    M ≤ W.map ((SemidirectProduct.inl :
        CentralExtension F b m hm heven →* SemilinearExtension F b m hm heven Sigma hSigma).comp
      (specialInclusion F b m hm heven)) ⊔
      (M ⊓ Subgroup.normalizer (X : Set (SemilinearExtension F b m hm heven Sigma hSigma))) := by
  classical
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
  set A := W.map ((SemidirectProduct.inl :
        CentralExtension F b m hm heven →* SemilinearExtension F b m hm heven Sigma hSigma).comp
      (specialInclusion F b m hm heven)) ⊔
      (M ⊓ Subgroup.normalizer (X : Set (SemilinearExtension F b m hm heven Sigma hSigma)))
    with hAdef
  by_cases hX1 : X = ⊥
  · intro g hg
    apply Subgroup.mem_sup_right
    refine Subgroup.mem_inf.mpr ⟨hg, ?_⟩
    rw [hX1, Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  obtain ⟨w, hw, hconj⟩ := exists_conj_mem_range_inr hp hpodd hf hcard hm2 hd hb hW hX hXC
  set c : SemilinearExtension F b m hm heven Sigma hSigma :=
    SemidirectProduct.inl (specialInclusion F b m hm heven w) with hcdef
  have hcA : c ∈ A := Subgroup.mem_sup_left ⟨w, hw, rfl⟩
  have hcM : c ∈ M := hM ⟨_, rfl⟩
  have hkey : ∀ g ∈ M, (∀ x ∈ X, g * (c⁻¹ * x * c) = c⁻¹ * x * c * g) → g ∈ A := by
    intro g hgM hgc
    have hg' : c * g * c⁻¹ ∈ M ⊓ Subgroup.normalizer (X : Set _) := by
      refine Subgroup.mem_inf.mpr ⟨M.mul_mem (M.mul_mem hcM hgM) (M.inv_mem hcM), ?_⟩
      apply mem_normalizer_of_forall_conj_eq
      intro x hx
      have h := hgc x hx
      calc c * g * c⁻¹ * x * (c * g * c⁻¹)⁻¹ = c * (g * (c⁻¹ * x * c)) * g⁻¹ * c⁻¹ := by group
        _ = c * (c⁻¹ * x * c * g) * g⁻¹ * c⁻¹ := by rw [h]
        _ = x := by group
    have hg : g = c⁻¹ * (c * g * c⁻¹) * c := by group
    rw [hg]
    exact A.mul_mem (A.mul_mem (A.inv_mem hcA) (Subgroup.mem_sup_right hg')) hcA
  have hfixed : ∀ v : CentralExtension F b m hm heven,
      (∀ σ : Sigma, fieldAction F b m hm heven Sigma hSigma σ v = v) →
        (SemidirectProduct.inl v : SemilinearExtension F b m hm heven Sigma hSigma) ∈ A := by
    intro v hv
    apply hkey _ (hM ⟨v, rfl⟩)
    intro x hx
    obtain ⟨σ, hσ⟩ := hconj x hx
    rw [hσ]
    have h := SemidirectProduct.inl_aut
      (φ := fieldAction F b m hm heven Sigma hSigma) σ v
    rw [hv σ] at h
    calc (SemidirectProduct.inl v : SemilinearExtension F b m hm heven Sigma hSigma) *
          SemidirectProduct.inr σ =
        SemidirectProduct.inr σ * SemidirectProduct.inl v * SemidirectProduct.inr σ⁻¹ *
          SemidirectProduct.inr σ := by rw [← h]
      _ = SemidirectProduct.inr σ * SemidirectProduct.inl v := by
        rw [mul_assoc _ (SemidirectProduct.inr σ⁻¹), ← map_mul, inv_mul_cancel, map_one, mul_one]
  have hinr : ∀ σ : Sigma, (SemidirectProduct.inr σ : SemilinearExtension F b m hm heven Sigma
      hSigma) ∈ M → (SemidirectProduct.inr σ : SemilinearExtension F b m hm heven Sigma hSigma) ∈
        A := by
    intro σ hσ
    apply hkey _ hσ
    intro x hx
    obtain ⟨τ, hτ⟩ := hconj x hx
    rw [hτ, ← map_mul, ← map_mul, hcomm]
  have hfixedSL : ∀ Y : SpecialLinearGroup (Fin 2) F, (∀ σ : Sigma, fieldSL F σ Y = Y) →
      (SemidirectProduct.inl (specialInclusion F b m hm heven Y) :
        SemilinearExtension F b m hm heven Sigma hSigma) ∈ A := by
    intro Y hY
    apply hfixed
    intro σ
    rw [fieldAction_specialInclusion, hY]
  set K₀ := A.comap ((SemidirectProduct.inl :
      CentralExtension F b m hm heven →* SemilinearExtension F b m hm heven Sigma hSigma).comp
    (specialInclusion F b m hm heven)) with hK₀def
  have hWK : W ≤ K₀ := fun w hw => Subgroup.mem_sup_left ⟨w, hw, rfl⟩
  have h2K : ∀ t ∈ Subgroup.centralizer {weyl F}, ∀ s : ℕ, t ^ 2 ^ s = 1 → t ∈ K₀ := by
    intro t ht s hts
    exact hfixedSL t fun σ =>
      ReducedInvolution.fieldSL_eq_of_pow_two_pow h2 (odd_orderOf_of_mem_sigma hd σ) ht hts
  have hTK := torus_le_of_le hW hWK h2K
  have hK₀ : K₀ = ⊤ := by
    by_cases hs : IsSquare (-1 : F)
    · obtain ⟨i, hi⟩ := hs
      have hi' : i * i = -1 := hi.symm
      apply eq_top_of_torus_le_of_rootSL_mem h2 hi' hTK
      · exact hfixedSL _ fun σ => by rw [fieldSL_rootSL hd h2 σ hi', map_one]
      · exact hfixedSL _ fun σ => by
          rw [fieldSL_rootSL hd h2 σ (neg_mul_neg_eq_neg_one hi'), map_one]
    ·
      have hq9 : 9 < p ^ f := by
        obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
        obtain ⟨σ, hσ⟩ := hconj x hx
        have hσ1 : σ ≠ 1 := by
          rintro rfl
          apply hx1
          apply Subtype.ext
          change x = 1
          rw [map_one] at hσ
          have := congrArg (fun z => c * z * c⁻¹) hσ
          simpa [mul_assoc] using this
        have hcard1 : Nat.card Sigma ≠ 1 := by
          intro h1
          exact hσ1 ((Nat.card_eq_one_iff_unique.mp h1).1.elim σ 1)
        have h3 : 3 ≤ Nat.card Sigma := by
          obtain ⟨k, hk⟩ := hd
          have : 0 < Nat.card Sigma := Nat.card_pos
          omega
        have hf3 : 3 ≤ f := h3.trans (Nat.le_of_dvd (by omega) hdvd)
        have hp3 : 3 ≤ p := by
          have := hp.two_le
          obtain ⟨k, hk⟩ := hpodd
          omega
        calc 9 < 3 ^ 3 := by norm_num
          _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
          _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf3
      apply eq_top_of_torus_le_of_upperSL_mem hp hp2 hcard hq9 hs hTK
      exact hfixedSL _ fun σ => by
        apply SL_ext_entries <;> rw [fieldSL_apply] <;> simp [upperSL]
  have hLA : modelLayer b m hm heven Sigma hSigma ≤ A := by
    intro x hx
    obtain ⟨Z, rfl⟩ := mem_modelLayer_iff.mp hx
    have hZ : Z ∈ K₀ := hK₀ ▸ Subgroup.mem_top Z
    exact hZ
  have huA : (SemidirectProduct.inl (cyclicGenerator F b m hm heven) :
      SemilinearExtension F b m hm heven Sigma hSigma) ∈ A :=
    hfixed _ fun σ => fieldAction_cyclicGenerator F b m hm heven Sigma hSigma σ
  have hBA : ModelSignalizers.modelBase b m hm heven Sigma hSigma ≤ A := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨Y, j, rfl⟩ := quotientClass_surjective F b m hm heven v
    rw [quotientClass_eq_specialInclusion_mul, map_mul, map_pow]
    exact A.mul_mem (hLA (inl_specialInclusion_mem_modelLayer Y)) (A.pow_mem huA _)
  intro g hg
  have hl : (SemidirectProduct.inl g.left : SemilinearExtension F b m hm heven Sigma hSigma) ∈
      M := hM ⟨_, rfl⟩
  have hr : (SemidirectProduct.inr g.right : SemilinearExtension F b m hm heven Sigma hSigma) ∈
      M := by
    have h' : (SemidirectProduct.inr g.right : SemilinearExtension F b m hm heven Sigma hSigma) =
        (SemidirectProduct.inl g.left)⁻¹ * g := by
      rw [eq_inv_mul_iff_mul_eq, SemidirectProduct.inl_left_mul_inr_right]
    rw [h']
    exact M.mul_mem (M.inv_mem hl) hg
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  exact A.mul_mem (hBA ⟨_, rfl⟩) (hinr _ hr)

end CFSG.Wreathed.OriginalAllPrime.R1NFacts
