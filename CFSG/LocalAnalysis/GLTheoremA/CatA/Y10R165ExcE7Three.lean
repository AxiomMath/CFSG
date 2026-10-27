module

public import CFSG.RankThree.PartOne.KA5L.Final
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.RankThree.PartOne.KE.E7ThreeLayerProof

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KA5L
  CFSG.RankThree.Classical2 CFSG.Open
open scoped MatrixGroups Pointwise commutatorElement

theorem dvd_card_statedProj_statedSU_six {F : Type} [Field F] [Finite F] {ℓ f p q : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime) (hp3 : 3 < p) (hq : q = ℓ ^ f)
    (hF : Nat.card F = q ^ 2) (hΦ : (q : ZMod p) ^ 2 - q + 1 = 0) :
    p ∣ Nat.card (StatedProj (StatedSU 6 q F)) := by
  subst hq
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (p := ℓ) (f := f) hℓ hf hF
    (by norm_num)]
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ ≤ ℓ ^ f := Nat.le_pow (by omega)
  have hq3 : p ∣ (ℓ ^ f) ^ 3 + 1 := by
    have h1 : (((ℓ ^ f : ℕ) : ZMod p)) ^ 3 = -1 := by
      have h2 : (((ℓ ^ f : ℕ) : ZMod p)) ^ 2 = ((ℓ ^ f : ℕ) : ZMod p) - 1 := by
        linear_combination hΦ
      calc (((ℓ ^ f : ℕ) : ZMod p)) ^ 3
          = (((ℓ ^ f : ℕ) : ZMod p)) * (((ℓ ^ f : ℕ) : ZMod p)) ^ 2 := by ring
        _ = (((ℓ ^ f : ℕ) : ZMod p)) * (((ℓ ^ f : ℕ) : ZMod p) - 1) := by rw [h2]
        _ = -1 := by linear_combination hΦ
    have h3 : (((ℓ ^ f) ^ 3 + 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, h1]
      ring
    exact (ZMod.natCast_eq_zero_iff ((ℓ ^ f) ^ 3 + 1) p).1 h3
  have hmem : 3 ∈ Finset.Icc 2 6 := by decide
  have hterm : p ∣ (((((ℓ ^ f : ℕ)) : ℤ)) ^ 3 - (-1) ^ 3).toNat := by
    have h4 : (((((ℓ ^ f : ℕ)) : ℤ)) ^ 3 - (-1) ^ 3).toNat = (ℓ ^ f) ^ 3 + 1 := by
      rw [show (-1 : ℤ) ^ 3 = -1 by norm_num]
      have h : (((ℓ ^ f : ℕ)) : ℤ) ^ 3 - -1 = (((ℓ ^ f) ^ 3 + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h, Int.toNat_natCast]
    rw [h4]
    exact hq3
  have hprod : p ∣ ∏ i ∈ Finset.Icc 2 6, ((((ℓ ^ f : ℕ)) : ℤ) ^ i - (-1) ^ i).toNat :=
    hterm.trans (Finset.dvd_prod_of_mem _ hmem)
  have hA : p ∣ (ℓ ^ f) ^ (6 * (6 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 6, ((((ℓ ^ f : ℕ)) : ℤ) ^ i - (-1) ^ i).toNat :=
    hprod.mul_left _
  have hg : Nat.gcd 6 ((ℓ ^ f) + 1) ∣ (ℓ ^ f) ^ (6 * (6 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 6, ((((ℓ ^ f : ℕ)) : ℤ) ^ i - (-1) ^ i).toNat := by
    refine (Nat.gcd_dvd_right 6 ((ℓ ^ f) + 1)).trans ?_
    have h2 : ((((ℓ ^ f : ℕ)) : ℤ) ^ 2 - (-1) ^ 2).toNat = (ℓ ^ f) ^ 2 - 1 := by
      rw [show (-1 : ℤ) ^ 2 = 1 by norm_num]
      have h5 : (((ℓ ^ f : ℕ)) : ℤ)^2 - 1 = (((ℓ ^ f) ^ 2 - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (Nat.one_le_pow 2 (ℓ ^ f) (by omega))]
        push_cast
        ring
      rw [h5, Int.toNat_natCast]
    have h6 : (ℓ ^ f) + 1 ∣ (ℓ ^ f) ^ 2 - 1 := by
      have h7 : (ℓ ^ f) ^ 2 - 1 = ((ℓ ^ f) + 1) * ((ℓ ^ f) - 1) := by
        have h8 : (ℓ ^ f) ^ 2 = ((ℓ ^ f) + 1) * ((ℓ ^ f) - 1) + 1 := by
          obtain ⟨r, hr⟩ : ∃ r, ℓ ^ f = r + 1 := ⟨ℓ ^ f - 1, by omega⟩
          rw [hr]
          simp only [Nat.add_sub_cancel]
          ring
        omega
      rw [h7]
      exact dvd_mul_right _ _
    have hdvd : (ℓ ^ f) + 1 ∣
        ∏ i ∈ Finset.Icc 2 6, ((((ℓ ^ f : ℕ)) : ℤ) ^ i - (-1) ^ i).toNat := by
      have h := Finset.dvd_prod_of_mem (fun i => ((((ℓ ^ f : ℕ)) : ℤ) ^ i - (-1) ^ i).toNat)
        (by decide : 2 ∈ Finset.Icc 2 6)
      rw [h2] at h
      exact h6.trans h
    exact hdvd.mul_left _
  have hpg : ¬ p ∣ Nat.gcd 6 ((ℓ ^ f) + 1) := by
    intro h
    have h1 : p ∣ (ℓ ^ f) + 1 := h.trans (Nat.gcd_dvd_right 6 ((ℓ ^ f) + 1))
    have h2 : ((ℓ ^ f : ℕ) : ZMod p) = -1 := by
      have h3 : (((ℓ ^ f) + 1 : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff ((ℓ ^ f) + 1) p).2 h1
      rw [Nat.cast_add, Nat.cast_one] at h3
      linear_combination h3
    rw [h2] at hΦ
    norm_num at hΦ
    have h3 : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 hΦ
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hAg : (ℓ ^ f) ^ (6 * (6 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 6, ((((ℓ ^ f : ℕ)) : ℤ) ^ i - (-1) ^ i).toNat =
      ((ℓ ^ f) ^ (6 * (6 - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 6, ((((ℓ ^ f : ℕ)) : ℤ) ^ i - (-1) ^ i).toNat) /
        Nat.gcd 6 ((ℓ ^ f) + 1) * Nat.gcd 6 ((ℓ ^ f) + 1) := (Nat.div_mul_cancel hg).symm
  rw [hAg] at hA
  rcases (Nat.Prime.dvd_mul hp).1 hA with h | h
  · exact h
  · exact absurd h hpg

theorem dvd_card_of_surjective_of_ker_dvd_six {G H : Type} [Group G] [Finite G] [Group H]
    [Finite H] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (ρ : G →* H) (hρ : Function.Surjective ρ)
    (hker : Nat.card ρ.ker ∣ 6) (hpG : p ∣ Nat.card G) : p ∣ Nat.card H := by
  have hcard : Nat.card G = Nat.card H * Nat.card ρ.ker := by
    have e : G ⧸ ρ.ker ≃* H := QuotientGroup.quotientKerEquivOfSurjective ρ hρ
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  rw [hcard] at hpG
  have hpg : ¬ p ∣ Nat.card ρ.ker := by
    intro h
    have h1 : p ∣ 6 := h.trans hker
    have h2 : p ∣ 2 * 3 := by simpa using h1
    rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
    · have := Nat.le_of_dvd (by norm_num) h3; omega
    · have := Nat.le_of_dvd (by norm_num) h3; omega
  rcases (Nat.Prime.dvd_mul hp).1 hpG with h | h
  · exact h
  · exact absurd h hpg

theorem dvd_card_SL_six {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : (Nat.card K : ZMod p) ^ 2 + Nat.card K + 1 = 0) :
    p ∣ Nat.card (SL(6, K)) := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 6) (by norm_num)]
  set q := Nat.card K
  have hq3 : p ∣ q ^ 3 - 1 := by
    have h1 : ((q : ZMod p)) ^ 3 = 1 := by
      have h2 : (q : ZMod p) ^ 2 = -1 - q := by linear_combination hΦ
      calc (q : ZMod p) ^ 3 = (q : ZMod p) * (q : ZMod p) ^ 2 := by ring
        _ = (q : ZMod p) * (-1 - q) := by rw [h2]
        _ = 1 := by linear_combination -hΦ
    have h2 : ((q ^ 3 - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (Nat.one_le_pow 3 q (by omega)), Nat.cast_pow, Nat.cast_one, h1, sub_self]
    exact (ZMod.natCast_eq_zero_iff (q ^ 3 - 1) p).1 h2
  have hmem : 3 ∈ Finset.Icc 2 6 := by decide
  have hprod : p ∣ ∏ j ∈ Finset.Icc 2 6, (q ^ j - 1) :=
    hq3.trans (Finset.dvd_prod_of_mem (fun j : ℕ => q ^ j - 1) hmem)
  exact hprod.mul_left _

theorem dvd_card_statedSU_six {F : Type} [Field F] [Finite F] {ℓ f p q : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hp : p.Prime) (hp3 : 3 < p) (hq : q = ℓ ^ f) (hF : Nat.card F = q ^ 2)
    (hΦ : (q : ZMod p) ^ 2 - q + 1 = 0) :
    p ∣ Nat.card (StatedSU 6 q F) := by
  refine (dvd_card_statedProj_statedSU_six hℓ hf hp hp3 hq hF hΦ).trans ?_
  exact ⟨Nat.card ((StatedScalars (Fin 6) F).subgroupOf (StatedSU 6 q F)),
    Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩

section Model

variable {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {ε : ℤ}

theorem exists_a5Layer_sigma_of_aut (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f)
    {n : ModGL Tag.E7 L} (hnm : n ∈ monomialSubgroup Tag.E7 L)
    (hnC : n ∈ adjointGroup Tag.E7 L) {v : WeylGroup Tag.E7}
    (hcert : ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v) • α = u • (ε • α))
    (Φ' : SL(6, L) ≃* SL(6, L))
    (hΦ' : ∀ X, ((canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ * n *
        canonicalRep (coxeterSystem Tag.E7) L v) *
        Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (a5Frame L X) *
        ((canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ * n *
          canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ = a5Frame L (Φ' X))
    (hq : CFSG.IsQuasisimple (fixSubgroup Φ'))
    (hcent : Nat.card (Subgroup.center (fixSubgroup Φ')) ∣ 6) :
    ∃ P : Subgroup (ModGL Tag.E7 L),
      IsSigmaFamily n (iterateFrobenius L ℓ f)
        ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7)) (fun _ : Unit => P) ∧
      P = (fixSubgroup Φ').map
        ((MulAut.conj (canonicalRep (coxeterSystem Tag.E7) L v)).toMonoidHom.comp (a5Frame L)) ∧
      ∃ ρ : fixSubgroup Φ' →* P, Function.Surjective ρ ∧
        (∀ z ∈ ρ.ker, ∀ u : fixSubgroup Φ', z * u = u * z) ∧ Nat.card ρ.ker ∣ 6 := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L :=
    isAlgebraic_zmod_of_card (ℓ := ℓ) (L := L) hK
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  set V : ModGL Tag.E7 L := canonicalRep (coxeterSystem Tag.E7) L v with hVdef
  have hVm : V ∈ monomialSubgroup Tag.E7 L := canonicalRep_mem_monomialSubgroup L v
  have hVadj : V ∈ adjointGroup Tag.E7 L := canonicalRep_mem_adjointGroup _ L v
  set n' : ModGL Tag.E7 L := V⁻¹ * n * V with hn'def
  have hn'm : n' ∈ monomialSubgroup Tag.E7 L :=
    mul_mem (mul_mem (inv_mem hVm) hnm) hVm
  have hn'adj : n' ∈ adjointGroup Tag.E7 L :=
    mul_mem (mul_mem (inv_mem hVadj) hnC) hVadj
  have hπV : weylQuotientHom Tag.E7 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ =
      v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v := by
    have h : (⟨n', hn'm⟩ : monomialSubgroup Tag.E7 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hnm⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [h, map_mul, map_mul, map_inv, hπV]
  obtain ⟨u, hu, hact⟩ := hcert
  have hact' : ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ • α = u • (ε • α) :=
    ⟨u, hu, fun α hα => by rw [hπn']; exact hact α hα⟩
  have hΦ'n : ∀ X, n' * Units.map (entrywiseHom Fr) (a5Frame L X) * n'⁻¹ = a5Frame L (Φ' X) :=
    hΦ'
  set Γ' : Subgroup (ModGL Tag.E7 L) :=
    rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓
      twistedFixedPoints n' (Units.map (entrywiseHom Fr)) with hΓ'def
  set P' : Subgroup (ModGL Tag.E7 L) := (fixSubgroup Φ').map (a5Frame L) with hP'def
  have hP'eq : P' = ⁅Γ', Γ'⁆ := (commutator_Gamma Fr n' Φ' hΦ'n hq).symm
  have hA5 : A5Layer Tag.E7 := a5Layer_E7
  obtain ⟨hfinP, hqP, hcentP, -⟩ := hA5 L ℓ f hf halg ε hε hq2 n' hn'm hn'adj hact' Γ' P' rfl hP'eq
  have hroots : ∀ r ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7), IsRoot Tag.E7 r := fun r hr => hr.1
  have hnormΓ : ∀ y ∈ Subgroup.normalizer
      (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) : Set (ModGL Tag.E7 L)),
      y ∈ twistedFixedPoints n' (Units.map (entrywiseHom Fr)) → ∀ γ ∈ Γ', y * γ * y⁻¹ ∈ Γ' :=
    fun y hy hyR γ hγ => Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hy γ).1 hγ.1,
      mul_mem (mul_mem hyR hγ.2) (inv_mem hyR)⟩
  have hstd : SigmaFactor n' Fr (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) (fun _ : Unit => P')
      (Subgroup.normalizer (rootSpan Tag.E7 L
        (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) : Set (ModGL Tag.E7 L))) := by
    refine ⟨fun _ => hfinP, fun _ => hqP, fun _ => ?_, fun _ => ?_, fun _ => ?_,
      fun _ y hy hyR u hu => ?_, fun y hy hc => hcentP y hy (fun u hu => hc () u hu)⟩
    · rw [hP'eq]; exact (commutator_le_self_subgroup Γ').trans inf_le_left
    · rw [hP'eq]; exact (commutator_le_self_subgroup Γ').trans inf_le_right
    · rw [hP'eq]
      exact ((commutator_le_self_subgroup Γ').trans inf_le_left).trans
        (rootSpan_le_adjointGroup L _)
    · rw [hP'eq] at hu ⊢
      exact conj_mem_commutator_of_normalizes (hnormΓ y hy hyR) hu
  set c₀ : ModGL Tag.E7 L →* ModGL Tag.E7 L := (MulAut.conj V).toMonoidHom with hc₀def
  have hc₀app : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [c₀, MulAut.conj_apply]
  have htr := SigmaFactor.transport Fr hFrbij v n hroots hstd
  have hN : Subgroup.map c₀ (Subgroup.normalizer (rootSpan Tag.E7 L
        (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) : Set (ModGL Tag.E7 L))) =
      Subgroup.normalizer (rootSpan Tag.E7 L
        ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7)) :
          Set (ModGL Tag.E7 L)) := by
    rw [Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj V).bijective,
      show Subgroup.map c₀ (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7))) =
        rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7)) from
        map_conj_rootSpan v hroots]
  have htr' : SigmaFactor n Fr ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7))
      (fun _ : Unit => P'.map c₀)
      (Subgroup.normalizer (rootSpan Tag.E7 L
        ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7)) :
          Set (ModGL Tag.E7 L))) := hN ▸ htr
  have hfam : IsSigmaFamily n Fr ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7))
      (fun _ : Unit => P'.map c₀) :=
    sigmaFactor_toSigma_E7 (n := n) (Fr := Fr) (P := P'.map c₀)
      (isRoot_image_parabolicRoots v (a5Nodes Tag.E7)) htr'
  have hPeq : P'.map c₀ = (fixSubgroup Φ').map (c₀.comp (a5Frame L)) := by
    rw [hP'def, Subgroup.map_map]
  have hfam' : IsSigmaFamily n Fr ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7))
      (fun _ : Unit => (fixSubgroup Φ').map (c₀.comp (a5Frame L))) := by
    rw [← hPeq]
    exact hfam
  refine ⟨(fixSubgroup Φ').map (c₀.comp (a5Frame L)), hfam', rfl, ?_⟩
  refine ⟨(c₀.comp (a5Frame L)).subgroupMap (fixSubgroup Φ'),
    MonoidHom.subgroupMap_surjective _ _, ?_, ?_⟩
  · intro z hz u
    have hz1 : (c₀.comp (a5Frame L)) (z : SL(6, L)) = 1 := by
      have h := congrArg Subtype.val hz
      simpa using h
    have hz2 : a5Frame L (z : SL(6, L)) = 1 := (MulAut.conj V).injective (by simpa [c₀] using hz1)
    have hzc : (z : SL(6, L)) ∈ Subgroup.center (SL(6, L)) :=
      ker_a5Frame_le_center (MonoidHom.mem_ker.2 hz2)
    exact Subtype.ext (Subgroup.mem_center_iff.1 hzc (u : SL(6, L))).symm
  · have hle : ((c₀.comp (a5Frame L)).subgroupMap (fixSubgroup Φ')).ker ≤
        Subgroup.center (fixSubgroup Φ') := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro u
      have hz1 : (c₀.comp (a5Frame L)) (z : SL(6, L)) = 1 := by
        have h := congrArg Subtype.val hz
        simpa using h
      have hz2 : a5Frame L (z : SL(6, L)) = 1 := (MulAut.conj V).injective (by simpa [c₀] using hz1)
      have hzc : (z : SL(6, L)) ∈ Subgroup.center (SL(6, L)) :=
        ker_a5Frame_le_center (MonoidHom.mem_ker.2 hz2)
      exact Subtype.ext (Subgroup.mem_center_iff.1 hzc (u : SL(6, L)))
    exact (Subgroup.card_dvd_of_le hle).trans hcent

end Model

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
