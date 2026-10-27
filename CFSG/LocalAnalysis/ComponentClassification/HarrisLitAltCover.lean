module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoreInner

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup Equiv Equiv.Perm

namespace AltCover

@[expose] def y6 : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 3 4 * swap 4 5

@[expose] def v6 : Perm (Fin 6) := swap 0 3 * swap 1 4

@[expose] def τ6 : Perm (Fin 6) := swap 0 3 * swap 1 4 * swap 2 5

@[expose] def y4 : Perm (Fin 4) := swap 0 1 * swap 1 2

@[expose] def v4 : Perm (Fin 4) := swap 0 1 * swap 2 3

theorem conj_viaEmbedding {α β : Type*} (ι : α ↪ β) (π : Perm β) (τ σ : Perm α)
    (hπ : ∀ a, π (ι a) = ι (τ a)) :
    π * σ.viaEmbedding ι * π⁻¹ = (τ * σ * τ⁻¹).viaEmbedding ι := by
  ext b
  have hπb : ∀ c : β, π (π⁻¹ c) = c := fun c => π.apply_symm_apply c
  have hτa : ∀ a : α, τ (τ⁻¹ a) = a := fun a => τ.apply_symm_apply a
  have hinv : ∀ a, π⁻¹ (ι a) = ι (τ⁻¹ a) := fun a => by
    rw [Perm.inv_eq_iff_eq, hπ, hτa]
  by_cases hb : b ∈ Set.range ι
  · obtain ⟨a, rfl⟩ := hb
    simp only [Perm.mul_apply, hinv, Perm.viaEmbedding_apply, hπ]
  · have hb' : π⁻¹ b ∉ Set.range ι := by
      rintro ⟨a, ha⟩
      apply hb
      refine ⟨τ a, ?_⟩
      rw [← hπ, ha, hπb]
    simp only [Perm.mul_apply, Perm.viaEmbedding_apply_of_notMem _ _ _ hb', hπb,
      Perm.viaEmbedding_apply_of_notMem _ _ _ hb]

theorem witness_of_embedding {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (ι : α ↪ β) (π : Perm β) (τ y v : Perm α) (hπ : ∀ a, π (ι a) = ι (τ a))
    (hy : τ * y * τ⁻¹ = y) (hv : τ * v * τ⁻¹ = v) (hy3 : y ^ 3 = 1)
    (hc2 : (y * v * y⁻¹ * v⁻¹) ^ 2 = 1) (hc1 : y * v * y⁻¹ * v⁻¹ ≠ 1) (hys : sign y = 1)
    (hvs : sign v = 1) :
    ∃ y' v' : Perm β, y' ∈ alternatingGroup β ∧ v' ∈ alternatingGroup β ∧ π * y' = y' * π ∧
      π * v' = v' * π ∧ y' ^ 3 = 1 ∧ (y' * v' * y'⁻¹ * v'⁻¹) ^ 2 = 1 ∧
      y' * v' * y'⁻¹ * v'⁻¹ ≠ 1 := by
  have hφ := Perm.viaEmbeddingHom_injective ι
  set φ := Perm.viaEmbeddingHom ι
  have hsign : ∀ σ : Perm α, sign (φ σ) = sign σ := fun σ => by
    rw [Perm.viaEmbeddingHom_apply, Perm.viaEmbedding, Perm.sign_extendDomain]
  have hcomm : ∀ σ : Perm α, τ * σ * τ⁻¹ = σ → π * φ σ = φ σ * π := fun σ hσ => by
    have h1 := conj_viaEmbedding ι π τ σ hπ
    rw [hσ, ← Perm.viaEmbeddingHom_apply] at h1
    calc π * φ σ = π * φ σ * π⁻¹ * π := by group
      _ = φ σ * π := by rw [h1]
  refine ⟨φ y, φ v, by rw [mem_alternatingGroup, hsign, hys],
    by rw [mem_alternatingGroup, hsign, hvs], hcomm y hy, hcomm v hv, ?_, ?_, ?_⟩
  · rw [← map_pow, hy3, map_one]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, hc2, map_one]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    intro h1
    exact hc1 (hφ (h1.trans (map_one φ).symm))

theorem injective_vec6 {β : Type*} {a b c d e f : β} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d)
    (h4 : a ≠ e) (h5 : a ≠ f) (h6 : b ≠ c) (h7 : b ≠ d) (h8 : b ≠ e) (h9 : b ≠ f)
    (h10 : c ≠ d) (h11 : c ≠ e) (h12 : c ≠ f) (h13 : d ≠ e) (h14 : d ≠ f) (h15 : e ≠ f) :
    Function.Injective ![a, b, c, d, e, f] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem exists_witness {m : ℕ} (hm : 8 ≤ m) (π : Perm (Fin m)) (hπ : π * π = 1) :
    ∃ y v : Perm (Fin m), y ∈ alternatingGroup (Fin m) ∧ v ∈ alternatingGroup (Fin m) ∧
      π * y = y * π ∧ π * v = v * π ∧ y ^ 3 = 1 ∧ (y * v * y⁻¹ * v⁻¹) ^ 2 = 1 ∧
      y * v * y⁻¹ * v⁻¹ ≠ 1 := by
  classical
  have hππ : ∀ i, π (π i) = i := fun i => by
    rw [← Perm.mul_apply, hπ, Perm.one_apply]
  set Fx := Finset.univ.filter (fun i : Fin m => π i = i) with hFx
  by_cases h4 : 4 ≤ Fx.card
  ·
    obtain ⟨s, hsF, hs4⟩ := Finset.exists_subset_card_eq h4
    let ι : Fin 4 ↪ Fin m := (s.orderEmbOfFin hs4).toEmbedding
    have hι : ∀ a, π (ι a) = ι ((1 : Perm (Fin 4)) a) := fun a => by
      have hmem : ι a ∈ s := Finset.orderEmbOfFin_mem s hs4 a
      have := (Finset.mem_filter.mp (hsF hmem)).2
      rw [Perm.one_apply, this]
    exact witness_of_embedding ι π 1 y4 v4 hι (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  ·
    push Not at h4
    set Mv := Finset.univ.filter (fun i : Fin m => ¬ π i = i) with hMv
    have hcard : Fx.card + Mv.card = m := by
      rw [hFx, hMv, Finset.card_filter_add_card_filter_not]
      simp
    have hmemMv : ∀ i, i ∈ Mv ↔ π i ≠ i := fun i => by simp [hMv]
    have hpick : ∀ T : Finset (Fin m), T.card < Mv.card → ∃ a ∈ Mv, a ∉ T := by
      intro T hT
      by_contra hno
      push Not at hno
      exact absurd (Finset.card_le_card (fun a ha => hno a ha)) (by omega)
    obtain ⟨a₁, ha₁, -⟩ := hpick ∅ (by rw [Finset.card_empty]; omega)
    obtain ⟨a₂, ha₂, ha₂T⟩ := hpick {a₁, π a₁} (by
      have := Finset.card_le_two (a := a₁) (b := π a₁); omega)
    obtain ⟨a₃, ha₃, ha₃T⟩ := hpick {a₁, π a₁, a₂, π a₂} (by
      have : ({a₁, π a₁, a₂, π a₂} : Finset (Fin m)).card ≤ 4 := Finset.card_le_four
      omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha₂T ha₃T
    have h1 := (hmemMv a₁).mp ha₁
    have h2 := (hmemMv a₂).mp ha₂
    have h3 := (hmemMv a₃).mp ha₃
    have hπinj : ∀ i j, π i = π j → i = j := fun i j h => π.injective h
    have e₁ : π a₂ ≠ a₁ := fun h => ha₂T.2 (by rw [← h, hππ])
    have e₂ : π a₂ ≠ π a₁ := fun h => ha₂T.1 (hπinj _ _ h)
    have e₃ : π a₃ ≠ a₁ := fun h => ha₃T.2.1 (by rw [← h, hππ])
    have e₄ : π a₃ ≠ π a₁ := fun h => ha₃T.1 (hπinj _ _ h)
    have e₅ : π a₃ ≠ a₂ := fun h => ha₃T.2.2.2 (by rw [← h, hππ])
    have e₆ : π a₃ ≠ π a₂ := fun h => ha₃T.2.2.1 (hπinj _ _ h)
    have hf : Function.Injective ![a₁, a₂, a₃, π a₁, π a₂, π a₃] :=
      injective_vec6 (Ne.symm ha₂T.1) (Ne.symm ha₃T.1) h1.symm e₁.symm e₃.symm
        (Ne.symm ha₃T.2.2.1) ha₂T.2 h2.symm e₅.symm ha₃T.2.1 ha₃T.2.2.2 h3.symm e₂.symm
        e₄.symm e₆.symm
    let ι : Fin 6 ↪ Fin m := ⟨_, hf⟩
    have hι : ∀ a, π (ι a) = ι (τ6 a) := by
      intro a
      fin_cases a
      · show π a₁ = ι (τ6 0); rw [show τ6 0 = 3 by decide]; rfl
      · show π a₂ = ι (τ6 1); rw [show τ6 1 = 4 by decide]; rfl
      · show π a₃ = ι (τ6 2); rw [show τ6 2 = 5 by decide]; rfl
      · show π (π a₁) = ι (τ6 3); rw [show τ6 3 = 0 by decide]; exact hππ a₁
      · show π (π a₂) = ι (τ6 4); rw [show τ6 4 = 1 by decide]; exact hππ a₂
      · show π (π a₃) = ι (τ6 5); rw [show τ6 5 = 2 by decide]; exact hππ a₃
    exact witness_of_embedding ι π τ6 y6 v6 hι (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)

theorem exists_odd_preimage_hom {A B : Type*} [Group A] [Group B] [Finite A] (φ : A →* B)
    (a : A) (h : Odd (orderOf (φ a))) : ∃ a' : A, φ a' = φ a ∧ Odd (orderOf a') := by
  have hs : Odd (orderOf (QuotientGroup.mk a : A ⧸ φ.ker)) := by
    rwa [← orderOf_injective (QuotientGroup.kerLift φ) (QuotientGroup.kerLift_injective φ),
      QuotientGroup.kerLift_mk]
  obtain ⟨a', ha', hodd⟩ := FooteLit.exists_odd_preimage φ.ker hs
  refine ⟨a', ?_, hodd⟩
  have h1 := congrArg (QuotientGroup.kerLift φ) ha'
  rwa [QuotientGroup.kerLift_mk, QuotientGroup.kerLift_mk] at h1

variable {G : Type} [Group G]

@[expose] def toQuot (J : Subgroup G) (x : G) :
    ↥(J ⊓ centralizer ({x} : Set G)) →* ↥J ⧸ Open.fusionZStar ↥J :=
  (QuotientGroup.mk' (Open.fusionZStar ↥J)).comp (Subgroup.inclusion inf_le_left)

theorem normalizerConj_involutive {J : Subgroup G} {x : G} (hxN : x ∈ normalizer (J : Set G))
    (hx2 : x * x = 1) (y : ↥J) :
    normalizerConj J ⟨x, hxN⟩ (normalizerConj J ⟨x, hxN⟩ y) = y := by
  apply Subtype.ext
  rw [normalizerConj_apply, normalizerConj_apply]
  show x * (x * (y : G) * x⁻¹) * x⁻¹ = y
  rw [inv_eq_of_mul_eq_one_right hx2]
  calc x * (x * (y : G) * x) * x = (x * x) * y * (x * x) := by group
    _ = y := by rw [hx2, one_mul, mul_one]

theorem mem_map_of_odd [Finite G] {J : Subgroup G} {x : G} (hxN : x ∈ normalizer (J : Set G))
    (hx2 : x * x = 1)
    (hP : IsPGroup 2 (↥(J ⊓ centralizer {x}) ⧸ pPrimeCore 2 ↥(J ⊓ centralizer {x})))
    {s : ↥J ⧸ Open.fusionZStar ↥J} (hs : Odd (orderOf s))
    (hsx : FooteLit.zStarAut ↥J (normalizerConj J ⟨x, hxN⟩) s = s) :
    s ∈ (pPrimeCore 2 ↥(J ⊓ centralizer {x})).map (toQuot J x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, rfl⟩ := FooteLit.exists_fixed_lift (normalizerConj_involutive hxN hx2) hs hsx
  have hcx : (c : G) ∈ centralizer ({x} : Set G) := by
    have h1 : x * (c : G) * x⁻¹ = c := congrArg Subtype.val hc
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hc' : toQuot J x ⟨c, c.2, hcx⟩ = QuotientGroup.mk c := rfl
  obtain ⟨d, hd, hdodd⟩ := exists_odd_preimage_hom (toQuot J x) ⟨c, c.2, hcx⟩ (hc' ▸ hs)
  refine ⟨d, ?_, hd.trans hc'⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) (QuotientGroup.mk d)
  have hdvd : orderOf (QuotientGroup.mk d : ↥(J ⊓ centralizer {x}) ⧸
      pPrimeCore 2 ↥(J ⊓ centralizer {x})) ∣ orderOf d := orderOf_map_dvd (QuotientGroup.mk' _) d
  rw [hk] at hdvd
  have hk1 : 2 ^ k = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hdodd)) hdvd
  rw [hk1, orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at hk
  exact hk

end AltCover

open AltCover in
theorem alternatingCoverInvolutionFact_holds : AlternatingCoverInvolutionFact := by
  intro G _ _ J x m hm _ ⟨e⟩ hxN hx2 hP
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ᾱ := FooteLit.zStarAut ↥J (normalizerConj J ⟨x, hxN⟩) with hᾱ
  have hᾱ2 : ∀ s, ᾱ (ᾱ s) = s := fun s => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
    simp only [hᾱ, FooteLit.zStarAut_mk, normalizerConj_involutive hxN hx2]
  let κ : MulAut (alternatingGroup (Fin m)) := (e.symm.trans ᾱ).trans e
  have hκ : ∀ a, κ (κ a) = a := fun a => by
    simp only [κ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hᾱ2,
      MulEquiv.apply_symm_apply]
  have hbij :=
    GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m (by omega) (by omega)
  obtain ⟨π, hπ⟩ := hbij.2 κ
  have hππ : π * π = 1 := hbij.1 (by
    rw [map_mul, hπ, map_one]
    exact MulEquiv.ext fun a => hκ a)
  have hfix : ∀ a : alternatingGroup (Fin m), π * (a : Perm (Fin m)) = a * π →
      ᾱ (e.symm a) = e.symm a := by
    intro a ha
    have h1 : κ a = a := by
      rw [← hπ]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, ha, mul_inv_cancel_right]
    have h2 : e.symm (κ a) = e.symm a := by rw [h1]
    rwa [show κ a = e (ᾱ (e.symm a)) from rfl, MulEquiv.symm_apply_apply] at h2
  obtain ⟨y, v, hy, hv, hπy, hπv, hy3, hc2, hc1⟩ := exists_witness hm π hππ
  obtain ⟨yb, hybdef⟩ : ∃ yb, yb = e.symm ⟨y, hy⟩ := ⟨_, rfl⟩
  obtain ⟨vb, hvbdef⟩ : ∃ vb, vb = e.symm ⟨v, hv⟩ := ⟨_, rfl⟩
  have hyb : ᾱ yb = yb := hybdef ▸ hfix _ hπy
  have hvb : ᾱ vb = vb := hvbdef ▸ hfix _ hπv
  have hyb3 : yb ^ 3 = 1 := by
    have h1 : (⟨y, hy⟩ : alternatingGroup (Fin m)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hy3)
    rw [hybdef, ← map_pow, h1, map_one]
  have hw3 : (vb * yb⁻¹ * vb⁻¹) ^ 3 = 1 := by
    rw [conj_pow, inv_pow, hyb3, inv_one, mul_one, mul_inv_cancel]
  have hw : ᾱ (vb * yb⁻¹ * vb⁻¹) = vb * yb⁻¹ * vb⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv, hyb, hvb]
  have hodd : ∀ s : ↥J ⧸ Open.fusionZStar ↥J, s ^ 3 = 1 → Odd (orderOf s) := fun s hs =>
    Odd.of_dvd_nat (⟨1, rfl⟩ : Odd 3) (orderOf_dvd_of_pow_eq_one hs)
  obtain ⟨d, hd, hdeq⟩ := mul_mem (mem_map_of_odd hxN hx2 hP (hodd _ hyb3) hyb)
    (mem_map_of_odd hxN hx2 hP (hodd _ hw3) hw)
  have hdodd : Odd (orderOf d) := Odd.of_dvd_nat
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) (Subgroup.orderOf_dvd_natCard _ hd)
  have h4 : orderOf (yb * (vb * yb⁻¹ * vb⁻¹)) ∣ orderOf d := by
    rw [← hdeq]
    exact orderOf_map_dvd _ d
  have h5 : orderOf (yb * (vb * yb⁻¹ * vb⁻¹)) = 2 := by
    rw [← MulEquiv.orderOf_eq e]
    have h6 : e (yb * (vb * yb⁻¹ * vb⁻¹)) = ⟨y * v * y⁻¹ * v⁻¹,
        mul_mem (mul_mem (mul_mem hy hv) (inv_mem hy)) (inv_mem hv)⟩ := by
      apply Subtype.ext
      simp [hybdef, hvbdef, mul_assoc]
    rw [h6, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hc2 hc1
  rw [h5] at h4
  exact absurd (Odd.of_dvd_nat hdodd h4) (by decide)

end CFSG.ComponentClassification.HarrisLit
