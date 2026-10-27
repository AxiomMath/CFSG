module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OuterData
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxElim

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OutInv

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {α τ : G} (hα : α * α = 1)
    (hτ : τ ∈ zpowers α) : τ = 1 ∨ τ = α := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hτ
  have hα2 : α ^ (2 : ℤ) = 1 := by rw [zpow_two, hα]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [← Int.mul_ediv_add_emod k 2, hk, add_zero, zpow_mul, hα2, one_zpow]
  · right
    rw [← Int.mul_ediv_add_emod k 2, hk, zpow_add, zpow_mul, hα2, one_zpow, one_mul, zpow_one]

theorem conj_mem_coreActionKernel {G : Type*} [Group G] {L : Subgroup G} {g x : G}
    (hg : g ∈ normalizer (L : Set G)) (hx : x ∈ coreActionKernel L) :
    g * x * g⁻¹ ∈ coreActionKernel L := by
  have hxN : x ∈ normalizer (L : Set G) := (mem_coreActionKernel.mp hx).1
  have h1 : oddBarConj L (⟨g, hg⟩ * ⟨x, hxN⟩ * (⟨g, hg⟩)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, oddBarConj_eq_one_of_mem_kernel (g := ⟨x, hxN⟩) hx, mul_one,
      mul_inv_cancel]
  exact mem_coreActionKernel_of_oddBarConj_eq_one h1

theorem le_of_sup_odd {Y : Type*} [Group Y] [Finite Y] {Q X O : Subgroup Y}
    (hQ : IsQuasisimple ↥Q) (hXQ : X ≤ Q) (hOQ : O ≤ Q) (hOn : (O.subgroupOf Q).Normal)
    (hO : Odd (Nat.card O)) (hsup : X ⊔ O = Q) : Q ≤ X := by
  have hsup' : X.subgroupOf Q ⊔ O.subgroupOf Q = ⊤ := by
    rw [← subgroupOf_sup hXQ hOQ, hsup, subgroupOf_self]
  rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ (O.subgroupOf Q) with
    hc | ht
  · have : Group.IsPerfect ↥Q := hQ.1
    have h1 : X.subgroupOf Q ⊔ center ↥Q = ⊤ := by
      rw [eq_top_iff, ← hsup']
      exact sup_le_sup_left hc _
    have h2 := eq_top_of_sup_center h1
    intro q hq
    have h3 : (⟨q, hq⟩ : ↥Q) ∈ X.subgroupOf Q := by
      rw [h2]
      exact mem_top _
    exact h3
  · exfalso
    have hQO : Q ≤ O := fun q hq => by
      have h3 : (⟨q, hq⟩ : ↥Q) ∈ O.subgroupOf Q := by
        rw [ht]
        exact mem_top _
      exact h3
    have hodd : Odd (Nat.card ↥Q) := Odd.of_dvd_nat hO (Subgroup.card_dvd_of_le hQO)
    exact false_of_isSolvable hQ (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

include hKa in
theorem mem_zStar_of_mem_kernel {y : H} (hyK : y ∈ h.K) (hy : y ∈ coreActionKernel h.K) :
    y ∈ (Open.fusionZStar ↥h.K).map h.K.subtype := by
  refine ⟨⟨y, hyK⟩, ?_, rfl⟩
  have hZ := mem_center_of_mem_kernel hKa (k := ⟨y, hyK⟩) hy
  have hMeq : Open.fusionZStar ↥h.K =
      (center (OddBar h.K)).comap (QuotientGroup.mk' (pPrimeCore 2 h.K)) :=
    comap_center_congr (fusionOddCore_eq_pPrimeCore ↥h.K)
  rw [SetLike.mem_coe, hMeq]
  exact hZ

include hKa in
theorem exists_conj_eq_of_mem_kernel {z g₁ : H} (hzK : z ∈ h.K) (hza : z * h.a = h.a * z)
    (hz2' : z * z = 1) (hg₁K : g₁ ∈ h.K)
    (hcker : (h.a * z)⁻¹ * (g₁ * h.a * g₁⁻¹) ∈ coreActionKernel h.K) :
    ∃ g ∈ h.K, ∃ y ∈ h.B ⊓ (Open.fusionZStar ↥h.K).map h.K.subtype,
      g⁻¹ * h.a * g = h.a * z * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haN : h.a ∈ normalizer (h.K : Set H) := mem_normalizer_of_conjugate_eq hKa
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  set c := (h.a * z)⁻¹ * (g₁ * h.a * g₁⁻¹) with hc
  have hcK : c ∈ h.K := by
    have e2 : c = z⁻¹ * (h.a⁻¹ * g₁ * h.a) * g₁⁻¹ := by rw [hc]; group
    rw [e2]
    refine mul_mem (mul_mem (inv_mem hzK) ?_) (inv_mem hg₁K)
    have := (mem_normalizer_iff.mp (inv_mem haN) g₁).mp hg₁K
    simpa using this
  obtain ⟨c₁, hc₁, c₂, hc₂, hcc, hc₁odd, n₂, hn₂⟩ :=
    exists_odd_mul_twoPow c (orderOf_pos c)
  have hzpK : zpowers c ≤ h.K := zpowers_le.mpr hcK
  have hKW : h.K ≤ h.W := h.isPComponent_K.1
  have hc₂B : c₂ ∈ h.B :=
    mem_B_of_mem_coreActionKernel' h hKa (hKW (hzpK hc₂))
      ((zpowers_le.mpr hcker) hc₂) ⟨n₂, hn₂⟩
  have hBn : (h.B.subgroupOf h.W).Normal := Subgroup.normal_in_normalizer
  set π : ↥h.W →* ↥h.W ⧸ h.B.subgroupOf h.W := QuotientGroup.mk' _ with hπ
  have haW : h.a ∈ h.W := h.a_mem_normalizer
  have hzW : z ∈ h.W := hKW hzK
  have hg₁W : g₁ ∈ h.W := hKW hg₁K
  have hc₁W : c₁ ∈ h.W := hKW (hzpK hc₁)
  have hc₂W : c₂ ∈ h.W := hKW (hzpK hc₂)
  set u : ↥h.W ⧸ h.B.subgroupOf h.W := π ⟨h.a * z, mul_mem haW hzW⟩ with hu
  set cc : ↥h.W ⧸ h.B.subgroupOf h.W := π ⟨c₁, hc₁W⟩ with hcc'
  have hc₂1 : π ⟨c₂, hc₂W⟩ = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hc₂B
  have hconjW : g₁ * h.a * g₁⁻¹ ∈ h.W := mul_mem (mul_mem hg₁W haW) (inv_mem hg₁W)
  have htu : π ⟨g₁ * h.a * g₁⁻¹, hconjW⟩ = u * cc := by
    have e3 : (⟨g₁ * h.a * g₁⁻¹, hconjW⟩ : ↥h.W) =
        ⟨h.a * z, mul_mem haW hzW⟩ * ⟨c₁, hc₁W⟩ * ⟨c₂, hc₂W⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [show h.a * z * c₁ * c₂ = h.a * z * (c₁ * c₂) by group, ← hcc, hc]
      group
    rw [e3, map_mul, map_mul, hc₂1, mul_one]
  have hu2 : u * u = 1 := by
    rw [hu, ← map_mul, ← map_one π]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    calc h.a * z * (h.a * z) = h.a * (z * h.a) * z := by group
      _ = h.a * (h.a * z) * z := by rw [hza]
      _ = (h.a * h.a) * (z * z) := by group
      _ = 1 := by rw [ha2, hz2', one_mul]
  have hucc2 : u * cc * (u * cc) = 1 := by
    rw [← htu, ← map_mul, ← map_one π]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    calc g₁ * h.a * g₁⁻¹ * (g₁ * h.a * g₁⁻¹) = g₁ * (h.a * h.a) * g₁⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have hc₁odd' : Odd (orderOf (⟨c₁, hc₁W⟩ : ↥h.W)) := by rwa [Subgroup.orderOf_mk]
  have hccodd : Odd (orderOf cc) := Odd.of_dvd_nat hc₁odd' (orderOf_map_dvd π _)
  obtain ⟨n, hn⟩ := exists_zpow_conj_eq_of_odd hu2 hucc2 hccodd
  set o : H := c₁ ^ n with ho
  have hoW : o ∈ h.W := zpow_mem hc₁W n
  have hoK : o ∈ h.K := hzpK (zpow_mem hc₁ n)
  have hoC : o ∈ coreActionKernel h.K := (zpowers_le.mpr hcker) (zpow_mem hc₁ n)
  have hπo : π ⟨o, hoW⟩ = cc ^ n := by
    rw [hcc', ← map_zpow]
    rfl
  have hX'W : o⁻¹ * (g₁ * h.a * g₁⁻¹) * o ∈ h.W := mul_mem (mul_mem (inv_mem hoW) hconjW) hoW
  have hfin : π ⟨o⁻¹ * (g₁ * h.a * g₁⁻¹) * o, hX'W⟩ = u := by
    have e4 : (⟨o⁻¹ * (g₁ * h.a * g₁⁻¹) * o, hX'W⟩ : ↥h.W) =
        (⟨o, hoW⟩ : ↥h.W)⁻¹ * ⟨g₁ * h.a * g₁⁻¹, hconjW⟩ * ⟨o, hoW⟩ := Subtype.ext rfl
    rw [e4, map_mul, map_mul, map_inv, hπo, htu, hn]
  set y := (h.a * z)⁻¹ * (o⁻¹ * (g₁ * h.a * g₁⁻¹) * o) with hy
  have hyB : y ∈ h.B := by
    have h5 := QuotientGroup.eq.mp hfin.symm
    rw [hy]
    simpa [mem_subgroupOf] using h5
  have hyK : y ∈ h.K := by
    have e5 : y = z⁻¹ * (h.a⁻¹ * (o⁻¹ * g₁) * h.a) * (g₁⁻¹ * o) := by rw [hy]; group
    rw [e5]
    have h6 : h.a⁻¹ * (o⁻¹ * g₁) * h.a ∈ h.K := by
      have := (mem_normalizer_iff.mp (inv_mem haN) (o⁻¹ * g₁)).mp
        (mul_mem (inv_mem hoK) hg₁K)
      simpa using this
    exact mul_mem (mul_mem (inv_mem hzK) h6) (mul_mem (inv_mem hg₁K) hoK)
  have hyC : y ∈ coreActionKernel h.K := by
    have hazN : h.a * z ∈ normalizer (h.K : Set H) := mul_mem haN (le_normalizer hzK)
    have e6 : y = ((h.a * z)⁻¹ * o⁻¹ * (h.a * z)⁻¹⁻¹) * (c * o) := by rw [hy, hc]; group
    rw [e6]
    exact mul_mem (conj_mem_coreActionKernel (inv_mem hazN) (inv_mem hoC)) (mul_mem hcker hoC)
  refine ⟨g₁⁻¹ * o, mul_mem (inv_mem hg₁K) hoK, y, mem_inf.mpr ⟨hyB,
    mem_zStar_of_mem_kernel hKa hyK hyC⟩, ?_⟩
  rw [hy]
  group

theorem cfProp23Row516_of (hFus : OuterL2Fusion) : CFProp23Row516 := by
  intro H _ _ h hrow hout z hzD hzS hz2
  obtain ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩ := hrow
  have hcfg := outer_config hKa hJ hK hout
  have hzJB := mem_fixedLayer_of_mem_D h hzD hzS hz2
  have hzK : z ∈ h.K := fixedLayer_le_K h hKa hzJB
  have hzW : z ∈ h.W := K_le_W h hzK
  have hza : z * h.a = h.a * z := h.comm_a (h.D_le_S hzD)
  have hz2' : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  set aw : h.W := ⟨h.a, h.a_mem_normalizer⟩ with haw
  set zw : h.W := ⟨z, hzW⟩ with hzw
  set ζ : ↥(GAut hKa) := phi hKa (wbarMk h.B zw) with hζ
  have hζJ : ζ ∈ Jhat hKa := ⟨wbarMk h.B zw, ⟨zw, hzJB, rfl⟩, rfl⟩
  have hζ2 : ζ * ζ = 1 := by
    rw [hζ, ← map_mul, ← map_mul, ← map_one (phi hKa), ← map_one (wbarMk h.B)]
    congr 2
    exact Subtype.ext hz2'
  obtain ⟨γ, hγN, hγ⟩ : ∃ γ ∈ NL hKa, γ⁻¹ * phi hKa (abar h) * γ = phi hKa (abar h) * ζ := by
    by_cases hζ1 : ζ = 1
    · exact ⟨1, one_mem _, by rw [hζ1]; group⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hζo : orderOf ζ = 2 := orderOf_eq_prime (by rw [sq]; exact hζ2) hζ1
      exact hFus _ _ p f hp hp2 hf _ _ hcfg (Jhat_le_NL hKa) ζ hζJ hζo
  rw [mem_subgroupOf] at hγN
  obtain ⟨l, hl⟩ := hγN
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective l
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  set kw : h.W := ⟨k, K_le_W h k.2⟩ with hkw
  have h1 : rhoL hKa (kw⁻¹ * aw * kw) = rhoL hKa (aw * zw) := by
    have h2 := congrArg (fun g : ↥(GAut hKa) => (g : MulAut (LK h))) hγ
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [← hl] at h2
    rw [map_mul, map_mul, map_inv, map_mul, hkw, rhoL_of_mem_K]
    exact h2
  have h3 : rhoL hKa ((aw * zw)⁻¹ * (kw⁻¹ * aw * kw)) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have h4 := (rhoL_eq_one_iff hKa _).mp h3
  have hcker : (h.a * z)⁻¹ * ((k : H)⁻¹ * h.a * (k : H)⁻¹⁻¹) ∈ coreActionKernel h.K := by
    rw [inv_inv]
    simpa [haw, hzw, hkw] using h4
  obtain ⟨g, hgK, y, hy, hg⟩ :=
    exists_conj_eq_of_mem_kernel hKa hzK hza hz2' (inv_mem k.2) hcker
  exact ⟨g, K_le_W h hgK, y, hy, hg⟩

include hKa in
theorem tbar_mem_centralizer {t : H} (ht : t ∈ h.T) :
    wbarMk h.B ⟨t, Idx.mem_W_of_mem_T h ht⟩ ∈
      centralizer ((wbarImage h.B (GSLit.fixedLayer h.J h.B) : Subgroup (Wbar h.B)) :
        Set (Wbar h.B)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set JB := GSLit.fixedLayer h.J h.B with hJB
  set JE := GSLit.fixedLayer h.J (Idx.E h t) with hJE
  obtain ⟨hJEB, hsupE⟩ := GSLit.fixedLayer_nested h.isQuasisimple_J (Idx.E_le_kernel h ht)
    (Idx.isPGroup_E h ht) le_sup_right
  set OJ : Subgroup H := (pPrimeCore 2 ↥JB).map JB.subtype with hOJ
  have hOJB : OJ ≤ JB := by
    rintro _ ⟨o, -, rfl⟩
    exact o.2
  have hJBW : JB ≤ h.W := (fixedLayer_le_K h hKa).trans (K_le_W h)
  set Q := wbarImage h.B JB with hQ
  set Xb := wbarImage h.B JE with hXb
  set Ob := wbarImage h.B OJ with hOb
  have hXQ : Xb ≤ Q := map_mono (subgroupOf_mono _ hJEB)
  have hOQ : Ob ≤ Q := map_mono (subgroupOf_mono _ hOJB)
  have hsupb : Xb ⊔ Ob = Q := by
    rw [hXb, hOb, hQ, wbarImage, wbarImage, wbarImage, ← Subgroup.map_sup,
      ← subgroupOf_sup (hJEB.trans hJBW) (hOJB.trans hJBW), hsupE]
  have hQq : IsQuasisimple ↥Q := h.isStandard_bar.1
  have hOn : (Ob.subgroupOf Q).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨o, ho, hoe⟩ := hn
    obtain ⟨j, hj, hje⟩ := g.2
    rw [SetLike.mem_coe, mem_subgroupOf] at ho hj
    obtain ⟨o', ho', hoe'⟩ := ho
    have hm : (j : H) * o * (j : H)⁻¹ ∈ OJ := by
      refine ⟨⟨j, hj⟩ * o' * (⟨j, hj⟩ : ↥JB)⁻¹,
        (pPrimeCore_normal (p := 2) (G := ↥JB)).conj_mem _ ho' _, ?_⟩
      rw [subtype_apply] at hoe' ⊢
      simp only [coe_mul, coe_inv, hoe']
    refine ⟨j * o * j⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf]
      simpa using hm
    · rw [map_mul, map_mul, map_inv, hoe, hje]
      simp
  have hOodd : Odd (Nat.card Ob) := by
    have h1 : Nat.card Ob ∣ Nat.card (OJ.subgroupOf h.W) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (OJ.subgroupOf h.W) = Nat.card (pPrimeCore 2 ↥JB) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe (hOJB.trans hJBW)).toEquiv, hOJ,
        card_map_of_injective JB.subtype_injective]
    rw [h2] at h1
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h1
  have hle := le_of_sup_odd hQq hXQ hOQ hOn hOodd hsupb
  rw [mem_centralizer_iff]
  intro q hq
  obtain ⟨x, hx, rfl⟩ := hle hq
  rw [SetLike.mem_coe, mem_subgroupOf] at hx
  have hxC : (x : H) ∈ centralizer (Idx.E h t : Set H) :=
    (mem_inf.mp ((GSLit.fixedLayer_le_inf h.J (Idx.E h t)) hx)).2
  have hxt : (x : H) * t = t * x :=
    (mem_centralizer_iff.mp hxC t (mem_sup_left (mem_zpowers t))).symm
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hxt

theorem indexElimOuter_of (hCent : OuterL2Cent) : Idx.IndexElimOuter := by
  intro H _ _ h hrow hout t ht
  obtain ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩ := hrow
  have hcfg := outer_config hKa hJ hK hout
  have htW := Idx.mem_W_of_mem_T h ht
  set w : h.W := ⟨t, htW⟩ with hw
  set aw : h.W := ⟨h.a, h.a_mem_normalizer⟩ with haw
  set χ : h.W →* ↥(GAut hKa) := (phi hKa).comp (wbarMk h.B) with hχ
  have hτα : χ w * χ aw = χ aw * χ w := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.comm_a (Idx.mem_S_of_mem_T h ht))
  have hτJ : ∀ x ∈ Jhat hKa, χ w * x = x * χ w := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := mem_centralizer_iff.mp (tbar_mem_centralizer hKa ht) y hy
    show phi hKa (wbarMk h.B w) * phi hKa y = phi hKa y * phi hKa (wbarMk h.B w)
    rw [← map_mul, ← map_mul, h1]
  have hτ2 : ∃ k : ℕ, χ w ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := h.orderOf_eq_two_pow_of_mem_S (Idx.mem_S_of_mem_T h ht)
    refine ⟨k, ?_⟩
    rw [← map_pow, ← map_one χ]
    congr 1
    apply Subtype.ext
    simp only [hw, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hk, pow_orderOf_eq_one]
  have hmem := hCent _ _ p f hp hp2 hf _ _ hcfg (Jhat_le_NL hKa) (χ w) hτα hτJ hτ2
  have hα2 : χ aw * χ aw = 1 := by
    show phi hKa (abar h) * phi hKa (abar h) = 1
    rw [← map_mul, abar_mul_self, map_one]
  have hinj := GH74.KGroups.inducedHom_injective (K := OddBar h.K) h.isQuasisimple_K.1
  apply Idx.mem_of_actW h hKa ht
  rcases eq_one_or_eq_of_mem_zpowers hα2 hmem with h1 | h1
  · left
    have h2 : rhoL hKa w = 1 := by
      have := congrArg (fun g : ↥(GAut hKa) => (g : MulAut (LK h))) h1
      rw [← rhoBar_mk]
      simpa [hχ] using this
    apply hinj
    rw [map_one]
    exact h2
  · right
    have h2 : rhoL hKa w = rhoL hKa aw := by
      have := congrArg (fun g : ↥(GAut hKa) => (g : MulAut (LK h))) h1
      rw [← rhoBar_mk, ← rhoBar_mk]
      simpa [hχ] using this
    exact hinj h2

theorem cfProp23IndexElim_of
    (hCent : OuterL2Cent) : CFProp23IndexElim :=
  Idx.indexElim_of_case3 (indexElimOuter_of hCent)

end OutInv

end CFSG.ComponentClassification.CatFactsL4U4
