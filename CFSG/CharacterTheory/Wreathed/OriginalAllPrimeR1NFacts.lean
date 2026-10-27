module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeR1NGenerates
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeTIFactsFull
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeChapterIIFusion
public import CFSG.LocalAnalysis.ABGTheoremB.R1NFacts
public import CFSG.LocalAnalysis.ABGTheoremB.IV1
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeR1NModel
public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data
public import CFSG.LocalAnalysis.ABGTheoremB.V4Defs

public section

namespace CFSG.Wreathed.OriginalAllPrime

namespace R1NFacts

open CFSG.ABGTheoremB CFSG.Wreathed.OriginalAllPrime.TIFacts
open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.OriginalAllPrime.ModelSignalizers CFSG.Wreathed.CentralSL2

variable {G : Type} [Group G]

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp hA x,
    Subgroup.mem_normalizer_iff.mp hB x]

theorem mem_oddCoreIn_of_odd_orderOf [Finite G] {C P : Subgroup G} (hP : IsPGroup 2 P)
    (hsup : oddCoreIn C ⊔ P = C) {g : G} (hg : g ∈ C) (hodd : Odd (orderOf g)) :
    g ∈ oddCoreIn C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC : P ≤ C := le_sup_right.trans hsup.le
  set O := CFSG.oddCore C
  set π := QuotientGroup.mk' O
  have hOC : (oddCoreIn C).subgroupOf C = O :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective O
  have hsupC : O ⊔ P.subgroupOf C = ⊤ := by
    rw [← hOC, ← Subgroup.subgroupOf_sup (oddCoreIn_le C) hPC, hsup, Subgroup.subgroupOf_self]
  have hmap : (P.subgroupOf C).map π = ⊤ := by
    have h := congrArg (Subgroup.map π) hsupC
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective O)] at h
    have hO : O.map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hO, bot_sup_eq] at h
    exact h
  have hP' : IsPGroup 2 ((P.subgroupOf C).map π) := (hP.comap_subtype).map π
  rw [hmap] at hP'
  obtain ⟨s, hs⟩ := hP' ⟨π ⟨g, hg⟩, Subgroup.mem_top _⟩
  have hs' : π ⟨g, hg⟩ ^ 2 ^ s = 1 := by
    have := congrArg Subtype.val hs
    simpa using this
  have ho : π ⟨g, hg⟩ ^ orderOf g = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : C) ^ orderOf g = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ s) (orderOf g) :=
    Nat.Coprime.pow_left s (Nat.coprime_two_left.mpr hodd)
  have h1 : π ⟨g, hg⟩ = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hs', ho⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
  have h2 : (⟨g, hg⟩ : C) ∈ O := by
    rw [← QuotientGroup.ker_mk' O]
    exact h1
  exact ⟨⟨g, hg⟩, h2, rfl⟩

variable [Finite G] {σ : Setting G} {H : Type} [Group H] {φ : σ.N →* H} {M : Subgroup H}
  {y : H}

omit [Finite G] in
theorem mem_normalizer_sup_of_map (hφ : IsModelMap σ φ M y) {X : Subgroup G} (hX : X ≤ σ.N)
    {g : σ.N} (hg : φ g ∈ Subgroup.normalizer
      (((X.subgroupOf σ.N).map φ : Subgroup H) : Set H)) :
    (g : G) ∈ Subgroup.normalizer ((σ.ON ⊔ X : Subgroup G) : Set G) := by
  have hK : σ.ON ⊔ X ≤ σ.N := sup_le (ON_le_N σ) hX
  have hKimg : ((σ.ON ⊔ X).subgroupOf σ.N).map φ = (X.subgroupOf σ.N).map φ := by
    rw [Subgroup.subgroupOf_sup (ON_le_N σ) hX, Subgroup.map_sup, ← hφ.ker_eq,
      (Subgroup.map_eq_bot_iff _).mpr le_rfl, bot_sup_eq]
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have haN := hK ha
    have hmem : φ (g * ⟨a, haN⟩ * g⁻¹) ∈ ((σ.ON ⊔ X).subgroupOf σ.N).map φ := by
      rw [hKimg, map_mul, map_mul, map_inv]
      have h1 : φ ⟨a, haN⟩ ∈ (X.subgroupOf σ.N).map φ := hKimg ▸ ⟨⟨a, haN⟩, ha, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp h1
    have := hφ.mem_of_map_mem le_sup_left hmem
    simpa using this
  · intro ha
    have haN : a ∈ σ.N := by
      have h1 := hK ha
      have h2 : a = (g : G)⁻¹ * ((g : G) * a * (g : G)⁻¹) * g := by group
      rw [h2]
      exact σ.N.mul_mem (σ.N.mul_mem (σ.N.inv_mem g.2) h1) g.2
    have hmem : φ ⟨a, haN⟩ ∈ ((σ.ON ⊔ X).subgroupOf σ.N).map φ := by
      rw [hKimg]
      have h1 : φ (g * ⟨a, haN⟩ * g⁻¹) ∈ (X.subgroupOf σ.N).map φ := by
        rw [← hKimg]
        exact ⟨g * ⟨a, haN⟩ * g⁻¹, by simpa [Subgroup.mem_subgroupOf] using ha, rfl⟩
      rw [map_mul, map_mul, map_inv] at h1
      exact (Subgroup.mem_normalizer_iff.mp hg _).mpr h1
    exact hφ.mem_of_map_mem le_sup_left hmem

theorem r1NFacts_of_isModelMap
    {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m}
    {heven : Even m} {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ τ ∈ Sigma, τ (b : F) = b}
    {f : ℕ} (hp : σ.p.Prime) (hpodd : Odd σ.p) (hf : 1 ≤ f) (hcard : Nat.card F = σ.p ^ f)
    {n : ℕ} (hmn : m = 2 ^ n) (h4 : 4 ∣ m)
    (hm2 : m = 2 ^ padicValInt 2 ((σ.p ^ f : ℕ) - (if σ.p ^ f % 4 = 1 then (1 : ℤ) else -1)))
    (hd : Odd (Nat.card Sigma)) (hdvd : Nat.card Sigma ∣ f)
    (hcomm : ∀ τ υ : Sigma, τ * υ = υ * τ) (hb : ¬ IsSquare b)
    {φ : σ.N →* SemilinearExtension F b m hm heven Sigma hSigma}
    (hφ : IsModelMap σ φ (ModelSignalizers.modelLayer b m hm heven Sigma hSigma)
      (ModelSignalizers.modelY b m hm heven Sigma hSigma))
    (hD2 : IsPGroup 2 σ.D) (hx₂D : σ.x₂ ∈ σ.D) {z : G} (hzD : z ∈ σ.D)
    (hzN : z ∈ σ.N)
    (hz : φ ⟨z, hzN⟩ * ModelSignalizers.modelY b m hm heven Sigma hSigma * (φ ⟨z, hzN⟩)⁻¹ =
      ModelSignalizers.modelX b m hm heven Sigma hSigma *
        ModelSignalizers.modelY b m hm heven Sigma hSigma)
    (hL : ModelSignalizers.modelBase b m hm heven Sigma hSigma ≤ (σ.L.subgroupOf σ.N).map φ)
    (hOC : ∀ g ∈ σ.C, Odd (orderOf g) → g ∈ oddCoreIn σ.C)
    {J : Subgroup G} (hJ : σ.IsV21Layer J) : σ.R1NFacts J := by
  classical
  have : Fact σ.p.Prime := ⟨hp⟩
  have hp2 : σ.p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  have : CharP F σ.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hcard
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
  obtain ⟨Wf, hWf⟩ := CFSG.Wreathed.OddFieldTorus.exists_oddTorus F
  have hWf' : ∀ g, g ∈ Wf ↔ g ∈ Subgroup.centralizer {weyl F} ∧ Odd (orderOf g) := hWf
  set x₂' : σ.N := ⟨σ.x₂, hφ.x₂_mem⟩ with hx₂'
  have hJN : J ≤ σ.N := hJ.le.trans hφ.L₀_le
  have hJM : (J.subgroupOf σ.N).map φ = ModelSignalizers.modelLayer b m hm heven Sigma hSigma := by
    rw [← hφ.map_L₀, hJ.sup_eq, Subgroup.subgroupOf_sup hJN (ON_le_N σ), Subgroup.map_sup,
      ← hφ.ker_eq, (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]
  have hpN : pCoreIn σ.p σ.N ≤ σ.ON := hJ.inf_eq ▸ inf_le_right
  have hXbar : ∀ X : Subgroup G, X ≤ σ.N → IsPGroup σ.p X →
      σ.D ≤ Subgroup.normalizer (X : Set G) →
        IsPGroup σ.p ((X.subgroupOf σ.N).map φ) ∧
          (X.subgroupOf σ.N).map φ ≤ ModelSignalizers.modelC b m hm heven Sigma hSigma ∧
          (X.subgroupOf σ.N).map φ ⊓ ModelSignalizers.modelBase b m hm heven Sigma hSigma = ⊥ := by
    intro X hXN hXp hDX
    have hXp' : IsPGroup σ.p ((X.subgroupOf σ.N).map φ) := hXp.comap_subtype.map φ
    have hDnorm := hφ.le_normalizer_map hXN hDX
    have hyX : ModelSignalizers.modelY b m hm heven Sigma hSigma ∈
        Subgroup.normalizer (((X.subgroupOf σ.N).map φ : Subgroup _) : Set _) := by
      rw [← hφ.map_x₂]
      exact hDnorm ⟨x₂', hx₂D, rfl⟩
    have hzX : φ ⟨z, hzN⟩ ∈
        Subgroup.normalizer (((X.subgroupOf σ.N).map φ : Subgroup _) : Set _) :=
      hDnorm ⟨⟨z, hzN⟩, hzD, rfl⟩
    have hzr : (φ ⟨z, hzN⟩).right = 1 := by
      obtain ⟨k, hk⟩ := hD2 ⟨z, hzD⟩
      have hk' : (φ ⟨z, hzN⟩) ^ 2 ^ k = 1 := by
        have h1 : (⟨z, hzN⟩ : σ.N) ^ 2 ^ k = 1 := by
          apply Subtype.ext
          have := congrArg Subtype.val hk
          simpa using this
        rw [← map_pow, h1, map_one]
      have h1 : (φ ⟨z, hzN⟩).right ^ 2 ^ k = 1 := by
        have := congrArg SemidirectProduct.rightHom hk'
        rwa [map_pow, map_one] at this
      have h2' : (φ ⟨z, hzN⟩).right ^ Nat.card Sigma = 1 := pow_card_eq_one'
      have hcop : Nat.Coprime (2 ^ k) (Nat.card Sigma) :=
        Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hd)
      have h := pow_gcd_eq_one.mpr ⟨h1, h2'⟩
      rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
    exact ⟨hXp', le_modelC hp2 h2 h4 hmn hXp' hyX hz hzr hzX,
      inf_modelBase_eq_bot hp2 h2 h4 hmn hXp' hyX hz hzr hzX⟩
  have hWbar : ∀ W ∈ σ.familyW J, ∀ t ∈ Wf, ∃ w : σ.N, (w : G) ∈ W ∧
      φ w = SemidirectProduct.inl (specialInclusion F b m hm heven t) := by
    intro W hW t ht
    obtain ⟨hWJ, -, -, hWsup⟩ := hW
    have htM : (SemidirectProduct.inl (specialInclusion F b m hm heven t) :
        SemilinearExtension F b m hm heven Sigma hSigma) ∈ (J.subgroupOf σ.N).map φ :=
      hJM ▸ inl_specialInclusion_mem_modelLayer t
    obtain ⟨j, hj, hjeq⟩ := htM
    have htC : (SemidirectProduct.inl (specialInclusion F b m hm heven t) :
        SemilinearExtension F b m hm heven Sigma hSigma) ∈
          ModelSignalizers.modelC b m hm heven Sigma hSigma :=
      (inl_specialInclusion_mem_modelC_iff t).mpr ((hWf' t).mp ht).1
    have hc : φ j * φ x₂' = φ x₂' * φ j := by
      rw [hjeq, hx₂', hφ.map_x₂]
      exact Subgroup.mem_centralizer_singleton_iff.mp htC
    have hU : ∀ u ∈ J.subgroupOf σ.N, x₂' * u * x₂'⁻¹ ∈ J.subgroupOf σ.N := by
      intro u hu
      rw [Subgroup.mem_subgroupOf] at hu ⊢
      have h1 := (Subgroup.mem_normalizer_iff.mp (hJ.normal hφ.x₂_mem) u).mp hu
      simpa using h1
    obtain ⟨u, hu, hφu, hux⟩ :=
      exists_commute_lift φ hφ.odd_card_ker (Subtype.ext hφ.x₂_mul_self) hU hj hc
    have huC : (u : G) ∈ σ.C := (mem_C_iff σ u.2).mpr (congrArg Subtype.val hux)
    have huodd : Odd (orderOf (u : G)) := by
      have hinj : Function.Injective ((SemidirectProduct.inl :
          CentralExtension F b m hm heven →* SemilinearExtension F b m hm heven Sigma hSigma).comp
            (specialInclusion F b m hm heven)) :=
        inl_specialInclusion_injective (b := b) (hm := hm) (heven := heven) (Sigma := Sigma)
          (hSigma := hSigma)
      have hord : orderOf (φ u) = orderOf t := by
        rw [hφu, hjeq]
        exact orderOf_injective _ hinj t
      have hk : φ (u ^ orderOf t) = 1 := by rw [map_pow, ← hord, pow_orderOf_eq_one]
      have hkON : ((u ^ orderOf t : σ.N) : G) ∈ σ.ON := by
        have h1 : u ^ orderOf t ∈ φ.ker := hk
        rw [hφ.ker_eq, Subgroup.mem_subgroupOf] at h1
        exact h1
      have hr : ((u : G) ^ orderOf t) ^ Nat.card σ.ON = 1 := by
        have h1 : (⟨_, hkON⟩ : σ.ON) ^ Nat.card σ.ON = 1 := pow_card_eq_one'
        have h2 := congrArg Subtype.val h1
        simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
        exact h2
      rw [← pow_mul] at hr
      exact Odd.of_dvd_nat ((((hWf' t).mp ht).2.mul (odd_card_oddCoreIn σ.N)))
        (orderOf_dvd_of_pow_eq_one hr)
    have huO : (u : G) ∈ oddCoreIn σ.C := hOC _ huC huodd
    have huW : (u : G) ∈ W ⊔ pCoreIn σ.p σ.N := by
      rw [hWsup]
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨huO, Subgroup.mem_subgroupOf.mp hu⟩)
    have hmem : φ u ∈ (W.subgroupOf σ.N).map φ := by
      have h1 : φ u ∈ ((W ⊔ pCoreIn σ.p σ.N).subgroupOf σ.N).map φ := ⟨u, huW, rfl⟩
      have hker : ((pCoreIn σ.p σ.N).subgroupOf σ.N).map φ = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, hφ.ker_eq]
        exact subgroupOf_mono_of_le hpN σ.N
      rwa [Subgroup.subgroupOf_sup (hWJ.trans hJN) (pCoreIn_le σ.p σ.N), Subgroup.map_sup,
        hker, sup_bot_eq] at h1
    obtain ⟨w', hw', hw'eq⟩ := hmem
    exact ⟨w', hw', hw'eq.trans (hφu.trans hjeq)⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    intro W hW X hXN hXp hDX
    obtain ⟨-, hXC, -⟩ := hXbar X hXN hXp hDX
    have hXCN : X ≤ σ.C ⊔ σ.ON := by
      intro x hx
      apply hφ.mem_of_map_mem le_sup_right (g := ⟨x, hXN hx⟩)
      have h1 : φ ⟨x, hXN hx⟩ ∈ (σ.C.subgroupOf σ.N).map φ := by
        rw [hφ.map_C]
        exact hXC ⟨⟨x, hXN hx⟩, hx, rfl⟩
      exact Subgroup.map_mono (subgroupOf_mono_of_le le_sup_left σ.N) h1
    have hWON : W ⊔ σ.ON = (oddCoreIn σ.C ⊓ J) ⊔ σ.ON := by
      obtain ⟨-, -, -, hsup⟩ := hW
      calc W ⊔ σ.ON = W ⊔ pCoreIn σ.p σ.N ⊔ σ.ON := by rw [sup_assoc, sup_eq_right.mpr hpN]
        _ = (oddCoreIn σ.C ⊓ J) ⊔ pCoreIn σ.p σ.N ⊔ σ.ON := by rw [hsup]
        _ = (oddCoreIn σ.C ⊓ J) ⊔ σ.ON := by rw [sup_assoc, sup_eq_right.mpr hpN]
    refine hXCN.trans (sup_le ?_ ?_)
    · intro c hc
      rw [hWON]
      apply normalizer_inf_normalizer_le_normalizer_sup
      exact Subgroup.mem_inf.mpr ⟨mem_normalizer_inf (le_normalizer_oddCoreIn σ.C hc)
        (hJ.normal (C_le_N σ hc)), le_normalizer_oddCoreIn σ.N (C_le_N σ hc)⟩
    · exact le_sup_right.trans Subgroup.le_normalizer
  ·
    intro W hW X hXN hXp hDX yy hyy hcomm'
    obtain ⟨hXp', hXC, hXB⟩ := hXbar X hXN hXp hDX
    have h1 : φ ⟨yy, hXN hyy⟩ = 1 := by
      refine eq_one_of_forall_commute hp hpodd hf hcard hm2 hd hb hWf' hXp' hXC hXB
        ⟨⟨yy, hXN hyy⟩, hyy, rfl⟩ ?_
      intro t ht
      obtain ⟨w', hw', hw'eq⟩ := hWbar W hW t ht
      rw [← hw'eq]
      have h2 : (⟨yy, hXN hyy⟩ * w' * (⟨yy, hXN hyy⟩ : σ.N)⁻¹ * w'⁻¹ : σ.N) ∈ φ.ker := by
        rw [hφ.ker_eq, Subgroup.mem_subgroupOf]
        simpa using hcomm' w' hw'
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
      calc φ ⟨yy, hXN hyy⟩ * φ w' =
          φ ⟨yy, hXN hyy⟩ * φ w' * (φ ⟨yy, hXN hyy⟩)⁻¹ * (φ w')⁻¹ * (φ w' * φ ⟨yy, hXN hyy⟩) := by
            group
        _ = φ w' * φ ⟨yy, hXN hyy⟩ := by rw [h2, one_mul]
    have h2 : (⟨yy, hXN hyy⟩ : σ.N) ∈ φ.ker := h1
    rw [hφ.ker_eq, Subgroup.mem_subgroupOf] at h2
    exact h2
  ·
    intro W hW X hXN hXp hDX Mm hLM hMN
    obtain ⟨hXp', hXC, -⟩ := hXbar X hXN hXp hDX
    have hBM : ModelSignalizers.modelBase b m hm heven Sigma hSigma ≤ (Mm.subgroupOf σ.N).map φ :=
      hL.trans (Subgroup.map_mono (subgroupOf_mono_of_le hLM σ.N))
    have hMG := le_sup_normalizer hp hpodd hf hcard hm2 hd hdvd hcomm hb hWf' hXp' hXC hBM
    set T₀ := W ⊔ σ.D ⊔ (Mm ⊓ Subgroup.normalizer ((σ.ON ⊔ X : Subgroup G) : Set G)) ⊔ σ.ON
    have hON : σ.ON ≤ T₀ := le_sup_right
    have hWT : W ≤ T₀ := le_sup_left.trans (le_sup_left.trans le_sup_left)
    have hMT : Mm ⊓ Subgroup.normalizer ((σ.ON ⊔ X : Subgroup G) : Set G) ≤ T₀ :=
      le_sup_right.trans le_sup_left
    have hle : Wf.map ((SemidirectProduct.inl : CentralExtension F b m hm heven →*
        SemilinearExtension F b m hm heven Sigma hSigma).comp (specialInclusion F b m hm heven)) ⊔
        ((Mm.subgroupOf σ.N).map φ ⊓ Subgroup.normalizer
          (((X.subgroupOf σ.N).map φ : Subgroup _) : Set _)) ≤
        (T₀.subgroupOf σ.N).map φ := by
      refine sup_le ?_ ?_
      · rintro _ ⟨t, ht, rfl⟩
        obtain ⟨w', hw', hw'eq⟩ := hWbar W hW t ht
        exact ⟨w', Subgroup.mem_subgroupOf.mpr (hWT hw'), hw'eq⟩
      · rintro _ ⟨⟨g', hg', rfl⟩, hn⟩
        exact ⟨g', Subgroup.mem_subgroupOf.mpr (hMT (Subgroup.mem_inf.mpr
          ⟨Subgroup.mem_subgroupOf.mp hg', mem_normalizer_sup_of_map hφ hXN hn⟩)), rfl⟩
    intro g hg
    apply hφ.mem_of_map_mem hON (g := ⟨g, hMN hg⟩)
    exact hle (hMG ⟨⟨g, hMN hg⟩, hg, rfl⟩)

theorem wreathedSetting_dGroup_le_oddCoreIn (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) (H : Subgroup G)
    (hDH : (wreathedSetting n S e p f).D ≤ H)
    (hDw : CFSG.QuasiDihedralFusion.IsDGroupWrt ((wreathedSetting n S e p f).T.subgroupOf H))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {X : Subgroup G} (hXH : X ≤ H) (hX : IsPGroup r X)
    (hTX : (wreathedSetting n S e p f).T ≤ Subgroup.normalizer (X : Set G)) :
    X ≤ CFSG.ABGTheoremB.oddCoreIn H := by
  have hSH := ChapterII.sylow_le_of_D_le n hn S e p f (Or.inl hDH)
  have hW := CFSG.QuasiDihedralFusion.hasWreathedSylow_of hn (S.subtype hSH)
    ((Subgroup.subgroupOfEquivOfLe hSH).trans e)
  obtain ⟨hD, hK4, -⟩ := hDw
  rcases hD with ⟨hdih, -⟩ | ⟨K, hK⟩
  · exact (CFSG.QuasiDihedralFusion.not_hasWreathedSylow_and_dihedral hW hdih).elim
  · have : Fact r.Prime := ⟨hr⟩
    have hXodd : Odd (Nat.card (X.subgroupOf H)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv]
      obtain ⟨k, hk⟩ := hX.exists_card_eq
      rw [hk]
      exact (hr.odd_of_ne_two hr2).pow
    have hXT : (wreathedSetting n S e p f).T.subgroupOf H ≤
        Subgroup.normalizer ((X.subgroupOf H : Subgroup H) : Set H) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hXH]
      exact fun t ht => hTX ht
    have h := CFSG.ABGDGroups.wreathed_dGroup_odd_four_invariant_le_oddCore hK hW hK4 hXodd hXT
    intro x hx
    exact ⟨⟨x, hXH hx⟩, h hx, rfl⟩

end R1NFacts

theorem wreathedSetting_r1NFacts
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ J : Subgroup G, (wreathedSetting n S e p f).IsV21Layer J →
      (wreathedSetting n S e p f).R1NFacts J := by
  intro J hJ
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  obtain ⟨F, hfield, hfinite, Sigma, b, hSigma, ρ, Ψ, hdata⟩ :=
    exists_conditionalCompatibleModelData hnonab n hn S e hfour p f hp hp2 hf hlocal
  let : Field F := hfield
  let : Finite F := hfinite
  let : Fintype F := Fintype.ofFinite F
  have hm2 := NormalComponentLift.two_pow_eq_two_part hnonab hfour hp hp2 hf hlocal
  obtain ⟨h, hh⟩ := TIFacts.exists_liftMap_eq_modelY hnonab hfour hp hpodd hf hlocal hdata
  have hφ := TIFacts.liftMap_isModelMap hnonab hfour hp hpodd hf hlocal hdata hh
  obtain ⟨z, hzD, hzN, hz⟩ := TIFacts.exists_swap_conj hn hφ
    (TIFacts.liftMap_x_eq hnonab hfour hp hpodd hf hlocal hdata h)
  have hTI := wreathedSetting_tiFacts_of hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  have hDS : (wreathedSetting n S e p f).D = (S : Subgroup G) :=
    wreathedSetting_D_eq n (by omega) S e p f
  have hD2 : IsPGroup 2 (wreathedSetting n S e p f).D := by
    rw [hDS]
    exact S.isPGroup'
  have hcomm : ∀ τ υ : Sigma, τ * υ = υ * τ := by
    have := hdata.sigma_cyclic
    exact fun τ υ => (IsCyclic.isMulCommutative (α := Sigma)).is_comm.comm τ υ
  refine R1NFacts.r1NFacts_of_isModelMap (σ := wreathedSetting n S e p f) hp hpodd hf
    hdata.card rfl (pow_dvd_pow 2 hn) hm2 hdata.sigma_odd hdata.sigma_dvd hcomm hdata.nonsquare
    hφ hD2 ?_ hzD hzN hz (TIFacts.modelBase_le_map_L hn hφ) ?_ hJ
  · rw [hDS]
    exact (e.symm (Original.x2 (2 ^ n))).property
  · intro g hg hodd
    exact R1NFacts.mem_oddCoreIn_of_odd_orderOf (hD2.to_le inf_le_left) hTI.C_eq hg hodd

open CFSG.ABGTheoremB CFSG.ABGLocalTools in
theorem wreathedSetting_h_R23 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (_hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ J : Subgroup G, (wreathedSetting n S e p f).IsV21Layer J →
      (wreathedSetting n S e p f).HypIV7 (wreathedSetting n S e p f).p →
      ∀ W ∈ (wreathedSetting n S e p f).familyW J,
      ∀ P : Subgroup G, IsSylowOf (wreathedSetting n S e p f).p P (wreathedSetting n S e p f).C →
      (wreathedSetting n S e p f).D ≤ Subgroup.normalizer (P : Set G) →
      ∀ K ∈ (wreathedSetting n S e p f).familyMstar (wreathedSetting n S e p f).p, W ≤ K →
      ∀ U ∈ maximals (signalizersPerm K (wreathedSetting n S e p f).D W
        (wreathedSetting n S e p f).p),
      U ∈ maximals (signalizers K (wreathedSetting n S e p f).D (wreathedSetting n S e p f).p) →
      P ≤ U → pPrimeCoreIn (wreathedSetting n S e p f).p (U ⊔ W) = ⊥ →
      ∀ L : Subgroup G, oddCoreIn K < L → L ≤ K → K ≤ Subgroup.normalizer (L : Set G) →
        K ≤ L ⊔ (K ⊓ Subgroup.normalizer ((oddCoreIn K ⊔ U : Subgroup G) : Set G)) := by
  intro J _ _ W _ P _ _ K hK _ U _ hU2 _ _ L _ _ _
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  obtain ⟨⟨hUK, hUp, hDU, -⟩, -⟩ := hU2
  obtain ⟨-, hDK, hDw, -⟩ := hK
  have hTD : (wreathedSetting n S e p f).T ≤ (wreathedSetting n S e p f).D := by
    rw [wreathedSetting_D_eq n (by omega) S e p f, Setting.T, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact (e.symm (Original.x (2 ^ n))).property
    · exact (e.symm (Original.x2 (2 ^ n))).property
  have hUO : U ≤ oddCoreIn K :=
    R1NFacts.wreathedSetting_dGroup_le_oddCoreIn n hn S e p f K hDK hDw hp hp2 hUK hUp
      (hTD.trans hDU)
  rw [sup_eq_left.mpr hUO]
  intro k hk
  exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hk, le_normalizer_oddCoreIn K hk⟩)

end CFSG.Wreathed.OriginalAllPrime
