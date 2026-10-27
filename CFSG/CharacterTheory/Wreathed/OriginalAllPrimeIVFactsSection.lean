module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsCenter
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.Wreathed.OriginalAllPrime.IVFacts

open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.OddFieldTorus CFSG.Semidihedral.ProjectiveSL2Cover
open CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
open scoped Pointwise

variable {G : Type} [Group G]

theorem card_sup_eq_mul_of_le_normalizer [Finite G] {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hinf : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B hAB
  let f : A × B → (A ⊔ B : Subgroup G) := fun x =>
    ⟨(x.1 : G) * x.2, by
      rw [← SetLike.mem_coe, hset]
      exact Set.mul_mem_mul x.1.2 x.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
      have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
          _ = b' * (b : G)⁻¹ := by group
      have h3 : (a' : G)⁻¹ * a ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem a'.2) a.2, h2 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
      rw [hinf, Subgroup.mem_bot] at h3
      have ha : a = a' := Subtype.ext (by
        have := congrArg (fun t => (a' : G) * t) h3
        simpa using this)
      have hb : b = b' := Subtype.ext (by
        rw [ha] at h1
        exact mul_left_cancel h1)
      rw [ha, hb]
    · rintro ⟨x, hx⟩
      rw [← SetLike.mem_coe, hset] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem card_map_of_inf_ker_eq_bot {G' : Type*} [Group G'] (f : G →* G') {A : Subgroup G}
    (h : ∀ a ∈ A, f a = 1 → a = 1) : Nat.card (A.map f) = Nat.card A := by
  have hinj : Function.Injective (f.comp A.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (h a a.2 ha)
  have hmap : A.map f = (f.comp A.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hmap]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

namespace IsWModel

variable {σ : Setting G} {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ}
  {hm : 0 < m} {heven : Even m} {Sigma : Subgroup (F ≃+* F)}
  {hSigma : ∀ τ ∈ Sigma, τ (b : F) = b}
  {φ : σ.N →* SemilinearExtension F b m hm heven Sigma hSigma}

theorem centralizer_SL2_section [Finite G] (hW : IsWModel σ φ) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → ∀ P : Subgroup G, IsSylowOf r P σ.C →
      σ.D ≤ Subgroup.normalizer (P : Set G) → ¬ centerOf P ≤ σ.L₀ → P ⊓ σ.L ≤ σ.ON →
        ∃ Λ : Subgroup G, (∀ l : G, l ∈ Λ ↔ l ∈ σ.L₀ ∧ ∀ g ∈ P, g * l * g⁻¹ * l⁻¹ ∈ σ.ON) ∧
          ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (m : ℕ), 1 < m ∧ Odd m ∧
            σ.q = Nat.card F₀ ^ m ∧ ∃ φ : Λ →* Matrix.SpecialLinearGroup (Fin 2) F₀,
              Function.Surjective φ ∧ φ.ker = σ.ON.subgroupOf Λ := by
  intro r hr hrON P hP _ hZ hPL
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn σ.N)) (even_iff_two_dvd.mpr hrON)
  have hPC : P ≤ σ.C := hP.le
  have hCN : σ.C ≤ σ.N := TIFacts.C_le_N σ
  set ι := iota b m hm heven Sigma hSigma with hι
  have hιinj : Function.Injective ι := iota_injective b m hm heven Sigma hSigma
  obtain ⟨W, hW'⟩ := exists_oddTorus F
  set Pb : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) :=
    (P.subgroupOf σ.N).map φ with hPb
  set Wb : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) := W.map ι with hWb
  have hPbB : ∀ x ∈ Pb, x ∈ ModelSignalizers.modelBase b m hm heven Sigma hSigma → x = 1 := by
    rintro _ ⟨g, hg, rfl⟩ hgB
    have hgP : (g : G) ∈ P := Subgroup.mem_subgroupOf.mp hg
    have hgL : (g : G) ∈ σ.L := (hW.mem_L_iff g).mpr hgB
    exact (hW.mem_ON_iff g).mp (hPL ⟨hgP, hgL⟩)
  have hWbB : Wb ≤ ModelSignalizers.modelBase b m hm heven Sigma hSigma := by
    rintro _ ⟨w, -, rfl⟩
    exact ⟨_, rfl⟩
  have hinf : Pb ⊓ Wb = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact hPbB x hx.1 (hWbB hx.2)
  have hPbC : Pb ≤ ModelSignalizers.modelC b m hm heven Sigma hSigma := (hW.isSylowOf_map hP).le
  have hSylW : IsSylowOf r (Pb ⊓ Wb) Wb :=
    (hW.isSylowOf_map hP).inf_of_le_normalizer (map_W_le_modelC hW')
      (hW.modelC_le_normalizer_map_W hW')
  have hWcard : Nat.card Wb = Nat.card W := Subgroup.card_map_of_injective hιinj
  have hrW : (Nat.card Wb).factorization r = 0 := by
    have h := hSylW.card_eq
    rw [hinf, Subgroup.card_bot] at h
    have h' := congrArg (fun n => n.factorization r) h
    simp only [Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply,
      Nat.Prime.factorization_pow hr, Finsupp.single_eq_same] at h'
    exact h'.symm
  have hPON : ¬ P ≤ σ.ON := fun h => hZ ((inf_le_left.trans h).trans hW.model.ON_le)
  obtain ⟨g₁, hg₁P, hg₁ON⟩ := Set.not_subset.mp hPON
  have hg₁N : g₁ ∈ σ.N := hCN (hPC hg₁P)
  set ρ : (SemilinearExtension F b m hm heven Sigma hSigma) →* Sigma :=
    SemidirectProduct.rightHom with hρ
  have hρinj : ∀ x ∈ Pb, ρ x = 1 → x = 1 := by
    intro x hx h1
    apply hPbB x hx
    rw [ModelSignalizers.modelBase, SemidirectProduct.range_inl_eq_ker_rightHom]
    exact h1
  set SP : Subgroup Sigma := Pb.map ρ with hSP
  set A : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) :=
    SP.map SemidirectProduct.inr with hA
  have hAcard : Nat.card A = Nat.card Pb := by
    rw [hA, Subgroup.card_map_of_injective SemidirectProduct.inr_injective, hSP,
      card_map_of_inf_ker_eq_bot ρ hρinj]
  have hPbform : ∀ x ∈ Pb, ∃ w ∈ W, x = ι w * SemidirectProduct.inr (ρ x) := by
    rintro _ ⟨g, hg, rfl⟩
    have hgP : (g : G) ∈ P := Subgroup.mem_subgroupOf.mp hg
    obtain ⟨k, hk⟩ := hP.isPGroup ⟨g, hgP⟩
    have hodd : Odd (orderOf (φ g)) := odd_orderOf_map hr hr2 g
      (by simpa using congrArg Subtype.val hk)
    obtain ⟨w, hw, τ, hτ⟩ := exists_eq_of_odd hW.p_prime hW.p_odd hW.one_le_f hW.card hm heven
      hW.two_part hW.sigma_odd hSigma hW.nonsquare hW' (hW.map_mem_modelC g (hPC hgP)) hodd
    refine ⟨w, hw, ?_⟩
    rw [hτ, map_mul, hι, iota_apply, SemidirectProduct.rightHom_inl,
      SemidirectProduct.rightHom_inr, one_mul]
  have hPbN : Pb ≤ Subgroup.normalizer
      (Wb : Set (SemilinearExtension F b m hm heven Sigma hSigma)) :=
    hPbC.trans (hW.modelC_le_normalizer_map_W hW')
  set K : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) := Pb ⊔ Wb with hK
  have hKcard : Nat.card K = Nat.card Pb * Nat.card Wb :=
    card_sup_eq_mul_of_le_normalizer hPbN hinf
  have hAK : A ≤ K := by
    rintro _ ⟨τ, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨w, hw, hxw⟩ := hPbform x hx
    have h : SemidirectProduct.inr (ρ x) = (ι w)⁻¹ * x := by
      rw [eq_inv_mul_iff_mul_eq]
      exact hxw.symm
    rw [h]
    exact K.mul_mem (K.inv_mem (le_sup_right (a := Pb) ⟨w, hw, rfl⟩)) (le_sup_left (b := Wb) hx)
  have hPbp : IsPGroup r Pb := (hW.isSylowOf_map hP).isPGroup
  obtain ⟨a, ha⟩ := hPbp.exists_card_eq
  have hKfact : (Nat.card K).factorization r = a := by
    rw [hKcard, ha, Nat.factorization_mul (pow_ne_zero _ hr.ne_zero) Nat.card_pos.ne',
      Finsupp.add_apply, Nat.Prime.factorization_pow hr, Finsupp.single_eq_same, hrW, add_zero]
  have hSylPb : IsSylowOf r Pb K := isSylowOf_of_card le_sup_left (by rw [ha, hKfact])
  have hSylA : IsSylowOf r A K := isSylowOf_of_card hAK (by rw [hAcard, ha, hKfact])
  obtain ⟨k, hkK, hk⟩ := hSylA.exists_mem_conj hSylPb
  rw [← SetLike.mem_coe, hK, Subgroup.coe_mul_of_left_le_normalizer_right Pb Wb hPbN] at hkK
  obtain ⟨y, hy, u, hu, rfl⟩ := hkK
  have hk' : ∀ x : (SemilinearExtension F b m hm heven Sigma hSigma),
      x ∈ Pb ↔ (y * u)⁻¹ * x * (y * u) ∈ A := hk
  have hconj : ∀ x : (SemilinearExtension F b m hm heven Sigma hSigma),
      x ∈ Pb ↔ u⁻¹ * x * u ∈ A := by
    intro x
    have h1 : x ∈ Pb ↔ y * x * y⁻¹ ∈ Pb := by
      constructor
      · intro h
        exact Pb.mul_mem (Pb.mul_mem hy h) (Pb.inv_mem hy)
      · intro h
        have h2 := Pb.mul_mem (Pb.mul_mem (Pb.inv_mem hy) h) hy
        have h3 : y⁻¹ * (y * x * y⁻¹) * y = x := by simp [mul_assoc]
        rwa [h3] at h2
    have h3 : (y * u)⁻¹ * (y * x * y⁻¹) * (y * u) = u⁻¹ * x * u := by simp [mul_assoc]
    rw [h1, hk', h3]
  obtain ⟨u₀, hu₀W, rfl⟩ := hu
  have hcyc : IsCyclic Sigma := hW.sigma_cyclic
  obtain ⟨τ₀, hτ₀⟩ := IsCyclic.exists_generator (α := SP)
  set τ₀' : F ≃+* F := ((τ₀ : Sigma) : F ≃+* F) with hτ₀'
  have hSPgen : ∀ τ : Sigma, τ ∈ SP ↔ τ ∈ Subgroup.zpowers (τ₀ : Sigma) := by
    intro τ
    constructor
    · intro hτ
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hτ₀ ⟨τ, hτ⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, by rw [← Subgroup.coe_zpow, hj]⟩
    · intro hτ
      exact Subgroup.zpowers_le.mpr τ₀.2 hτ
  have hcentA : ∀ Z : Matrix.SpecialLinearGroup (Fin 2) F,
      ι Z ∈ Subgroup.centralizer (A : Set (SemilinearExtension F b m hm heven Sigma hSigma)) ↔
        fieldSL F τ₀' Z = Z := by
    intro Z
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      have h1 := h _ ⟨_, τ₀.2, rfl⟩
      have h2 : SemidirectProduct.inr (τ₀ : Sigma) * ι Z * (SemidirectProduct.inr (τ₀ : Sigma))⁻¹ =
          ι Z := by rw [h1, mul_inv_cancel_right]
      rw [hι, inr_conj_iota] at h2
      exact hιinj h2
    · rintro h _ ⟨τ, hτ, rfl⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ((hSPgen τ).mp hτ)
      have hfix : fieldSL F ((τ₀ : Sigma) ^ j : Sigma) Z = Z := by
        rw [Subgroup.coe_zpow]
        rcases j with j | j
        · rw [Int.ofNat_eq_natCast, zpow_natCast]
          exact fieldSL_pow_eq h j
        · rw [zpow_negSucc]
          have h' := fieldSL_pow_eq h (j + 1)
          calc fieldSL F (τ₀' ^ (j + 1))⁻¹ Z = fieldSL F (τ₀' ^ (j + 1))⁻¹
                (fieldSL F (τ₀' ^ (j + 1)) Z) := by rw [h']
            _ = Z := by rw [← MulAut.mul_apply, ← fieldSL_mul, inv_mul_cancel, fieldSL_one,
                  MulAut.one_apply]
      have h2 := inr_conj_iota b m hm heven Sigma hSigma ((τ₀ : Sigma) ^ j) Z
      rw [hfix, ← hι] at h2
      calc SemidirectProduct.inr ((τ₀ : Sigma) ^ j) * ι Z =
          SemidirectProduct.inr ((τ₀ : Sigma) ^ j) * ι Z *
            (SemidirectProduct.inr ((τ₀ : Sigma) ^ j))⁻¹ *
            SemidirectProduct.inr ((τ₀ : Sigma) ^ j) := by group
        _ = ι Z * SemidirectProduct.inr ((τ₀ : Sigma) ^ j) := by rw [h2]
  have hcentP : ∀ x : (SemilinearExtension F b m hm heven Sigma hSigma),
      x ∈ Subgroup.centralizer (Pb : Set (SemilinearExtension F b m hm heven Sigma hSigma)) ↔
      (ι u₀)⁻¹ * x * ι u₀ ∈
        Subgroup.centralizer (A : Set (SemilinearExtension F b m hm heven Sigma hSigma)) := by
    intro x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h z hz
      have hz' : ι u₀ * z * (ι u₀)⁻¹ ∈ Pb := by
        rw [hconj]
        have h3 : (ι u₀)⁻¹ * (ι u₀ * z * (ι u₀)⁻¹) * ι u₀ = z := by group
        rwa [h3]
      have h1 := h _ hz'
      calc z * ((ι u₀)⁻¹ * x * ι u₀) =
          (ι u₀)⁻¹ * ((ι u₀ * z * (ι u₀)⁻¹) * x) * ι u₀ := by group
        _ = (ι u₀)⁻¹ * (x * (ι u₀ * z * (ι u₀)⁻¹)) * ι u₀ := by rw [h1]
        _ = (ι u₀)⁻¹ * x * ι u₀ * z := by group
    · intro h z hz
      have h1 := h _ ((hconj z).mp hz)
      calc z * x = ι u₀ * (((ι u₀)⁻¹ * z * ι u₀) * ((ι u₀)⁻¹ * x * ι u₀)) * (ι u₀)⁻¹ := by
            group
        _ = ι u₀ * (((ι u₀)⁻¹ * x * ι u₀) * ((ι u₀)⁻¹ * z * ι u₀)) * (ι u₀)⁻¹ := by rw [h1]
        _ = x * z := by group
  set Λ : Subgroup G := (σ.L₀.subgroupOf σ.N ⊓
    (Subgroup.centralizer (Pb : Set (SemilinearExtension F b m hm heven Sigma hSigma))).comap φ).map
      σ.N.subtype with hΛ
  have hΛN : Λ ≤ σ.N := Subgroup.map_subtype_le _
  have hmemΛ : ∀ l : G, l ∈ Λ ↔ ∃ hl : l ∈ σ.N, l ∈ σ.L₀ ∧
      φ ⟨l, hl⟩ ∈
        Subgroup.centralizer (Pb : Set (SemilinearExtension F b m hm heven Sigma hSigma)) := by
    intro l
    constructor
    · rintro ⟨l', ⟨hl'₁, hl'₂⟩, rfl⟩
      exact ⟨l'.2, Subgroup.mem_subgroupOf.mp hl'₁, hl'₂⟩
    · rintro ⟨hl, hl₁, hl₂⟩
      exact ⟨⟨l, hl⟩, ⟨Subgroup.mem_subgroupOf.mpr hl₁, hl₂⟩, rfl⟩
  refine ⟨Λ, fun l => ?_, ?_⟩
  ·
    rw [hmemΛ]
    constructor
    · rintro ⟨hl, hlL₀, hlc⟩
      refine ⟨hlL₀, fun g hg => ?_⟩
      have hgN : g ∈ σ.N := hCN (hPC hg)
      have h1 := Subgroup.mem_centralizer_iff.mp hlc (φ ⟨g, hgN⟩)
        ⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
      have h2 := (hW.mem_ON_iff (⟨g, hgN⟩ * ⟨l, hl⟩ * (⟨g, hgN⟩ : σ.N)⁻¹ * (⟨l, hl⟩ : σ.N)⁻¹)).mpr
        (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]; group)
      simpa using h2
    · rintro ⟨hlL₀, hlc⟩
      have hl : l ∈ σ.N := hW.model.L₀_le hlL₀
      refine ⟨hl, hlL₀, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨g, hg, rfl⟩
      have hgP : (g : G) ∈ P := Subgroup.mem_subgroupOf.mp hg
      have h1 := (hW.mem_ON_iff (g * ⟨l, hl⟩ * g⁻¹ * (⟨l, hl⟩ : σ.N)⁻¹)).mp
        (by simpa using hlc g hgP)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h2 : φ g * φ ⟨l, hl⟩ = φ ⟨l, hl⟩ * φ g := by
        calc φ g * φ ⟨l, hl⟩ = φ g * φ ⟨l, hl⟩ * (φ g)⁻¹ * (φ ⟨l, hl⟩)⁻¹ * (φ ⟨l, hl⟩ * φ g) := by
              group
          _ = φ ⟨l, hl⟩ * φ g := by rw [h1, one_mul]
      exact h2
  have hτ₀mem : τ₀' ∈ Sigma := (τ₀ : Sigma).2
  have hp2 : σ.p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hW.p_odd)
  obtain ⟨-, -, -, -, hall⟩ := odd_field_fixed_torus_derived_centralizer hW.p_prime hp2
    hW.one_le_f hW.card _ rfl m hW.two_part Sigma hW.sigma_odd
  obtain ⟨-, -, hfix, -⟩ := hall W hW'
  obtain ⟨hq, -⟩ := hfix τ₀' hτ₀mem
  have hordτ₀ : orderOf τ₀' = orderOf (τ₀ : Sigma) := Subgroup.orderOf_coe _
  have hτ₀ne : (τ₀ : Sigma) ≠ 1 := by
    intro h1
    have hSP1 : SP = ⊥ := by
      rw [eq_bot_iff]
      intro τ hτ
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ((hSPgen τ).mp hτ)
      rw [h1, one_zpow]
      exact Subgroup.one_mem _
    apply hg₁ON
    apply (hW.mem_ON_iff ⟨g₁, hg₁N⟩).mpr
    apply hρinj _ ⟨⟨g₁, hg₁N⟩, Subgroup.mem_subgroupOf.mpr hg₁P, rfl⟩
    have : ρ (φ ⟨g₁, hg₁N⟩) ∈ SP := ⟨_, ⟨⟨g₁, hg₁N⟩, Subgroup.mem_subgroupOf.mpr hg₁P, rfl⟩, rfl⟩
    rw [hSP1] at this
    exact this
  refine ⟨fixedField τ₀', inferInstance, inferInstance, orderOf (τ₀ : Sigma), ?_, ?_, ?_, ?_⟩
  ·
    rcases Nat.lt_or_ge 1 (orderOf (τ₀ : Sigma)) with h | h
    · exact h
    · exfalso
      have h0 : orderOf (τ₀ : Sigma) ≠ 0 := (orderOf_pos _).ne'
      have h1 : orderOf (τ₀ : Sigma) = 1 := by omega
      exact hτ₀ne (orderOf_eq_one_iff.mp h1)
  ·
    exact hW.sigma_odd.of_dvd_nat (orderOf_dvd_natCard _)
  ·
    change σ.p ^ σ.f = _
    rw [hq, card_fixedField_eq, hordτ₀]
  ·
    set fI := (ι.comp (fixedIncl τ₀')) with hfI
    have hfIinj : Function.Injective fI := hιinj.comp (fixedIncl_injective τ₀')
    set e := MonoidHom.ofInjective hfIinj with he
    set β : Λ →* (SemilinearExtension F b m hm heven Sigma hSigma) :=
      (MulAut.conj (ι u₀)⁻¹).toMonoidHom.comp
      (φ.comp (Subgroup.inclusion hΛN)) with hβ
    have hβapply : ∀ l : Λ,
        (β l : (SemilinearExtension F b m hm heven Sigma hSigma)) =
          (ι u₀)⁻¹ * φ ⟨l, hΛN l.2⟩ * ι u₀ := by
      intro l
      rw [hβ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]
      rfl
    have hβmem : ∀ l : Λ, β l ∈ fI.range := by
      intro l
      obtain ⟨hl, hlL₀, hlc⟩ := (hmemΛ l).mp l.2
      have hM := hW.map_mem_modelLayer ⟨l, hl⟩ hlL₀
      rw [modelLayer_eq_range] at hM
      obtain ⟨Z, hZ⟩ := hM
      have hβl : β l = ι ((u₀)⁻¹ * Z * u₀) := by
        rw [hβapply]
        change (ι u₀)⁻¹ * φ ⟨l, hl⟩ * ι u₀ = _
        rw [← hZ, map_mul, map_mul, map_inv]
      have hc := (hcentP _).mp hlc
      rw [← hZ, ← map_inv, ← map_mul, ← map_mul, hcentA] at hc
      obtain ⟨Z₀, hZ₀⟩ := exists_fixedIncl τ₀' (g := (u₀)⁻¹ * Z * u₀)
        (by rw [← fieldSL_eq_fieldAction]; exact hc)
      exact ⟨Z₀, by rw [hβl, hfI, MonoidHom.comp_apply, hZ₀]⟩
    refine ⟨e.symm.toMonoidHom.comp (β.codRestrict _ hβmem), ?_, ?_⟩
    ·
      intro Z₀
      set y : (SemilinearExtension F b m hm heven Sigma hSigma) := ι u₀ * fI Z₀ * (ι u₀)⁻¹ with hy
      have hyM : y ∈ ModelSignalizers.modelLayer b m hm heven Sigma hSigma := by
        rw [modelLayer_eq_range, hy, hfI, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
        exact ⟨_, rfl⟩
      obtain ⟨l, hlL₀, hly⟩ := hW.exists_mem_L₀ hyM
      have hlc : φ l ∈
          Subgroup.centralizer (Pb : Set (SemilinearExtension F b m hm heven Sigma hSigma)) := by
        rw [hcentP, hly, hy]
        have h3 : (ι u₀)⁻¹ * (ι u₀ * fI Z₀ * (ι u₀)⁻¹) * ι u₀ = fI Z₀ := by simp [mul_assoc]
        rw [h3, hfI, MonoidHom.comp_apply, hcentA, fieldSL_eq_fieldAction]
        exact fieldAction_fixedIncl τ₀' Z₀
      have hlΛ : (l : G) ∈ Λ := (hmemΛ l).mpr ⟨l.2, hlL₀, hlc⟩
      refine ⟨⟨l, hlΛ⟩, ?_⟩
      apply e.injective
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      change (β ⟨l, hlΛ⟩ : (SemilinearExtension F b m hm heven Sigma hSigma)) = fI Z₀
      rw [hβapply]
      change (ι u₀)⁻¹ * φ l * ι u₀ = fI Z₀
      rw [hly, hy]
      simp [mul_assoc]
    ·
      have hconj1 : ∀ x : (SemilinearExtension F b m hm heven Sigma hSigma),
          (ι u₀)⁻¹ * x * ι u₀ = 1 ↔ x = 1 := by
        intro x
        constructor
        · intro h
          have h3 := congrArg (fun t => ι u₀ * t * (ι u₀)⁻¹) h
          simpa [mul_assoc] using h3
        · rintro rfl
          simp
      ext l
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, ← Subtype.coe_inj, OneMemClass.coe_one,
        Subgroup.mem_subgroupOf]
      change (β l : (SemilinearExtension F b m hm heven Sigma hSigma)) = 1 ↔ _
      rw [hβapply, hconj1]
      exact (hW.mem_ON_iff _).symm

end IsWModel

end CFSG.Wreathed.OriginalAllPrime.IVFacts
