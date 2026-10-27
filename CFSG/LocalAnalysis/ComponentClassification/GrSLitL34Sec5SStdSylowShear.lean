module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdAutomizer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCentralSylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdShear
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdShearCenter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdTransfer
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.GH72.Sec4Basic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotZStar

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_shear_of_standard [IsSimpleGroup G] (hnonab : ∃ g h : G, g * h ≠ h * g)
    {J : Subgroup G} (hst : IsStandardSubgroup J) (hZ : Odd (Nat.card (center ↥J)))
    (hcen : center (↥J ⧸ center ↥J) = ⊥)
    (hOut : ∀ α β : MulAut (↥J ⧸ center ↥J),
      α ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      β ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      α * β ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range)
    (hfix : ∀ (T : Sylow 2 (↥J ⧸ center ↥J)) (α : MulAut (↥J ⧸ center ↥J)),
      (∀ x ∈ (T : Subgroup (↥J ⧸ center ↥J)), α x = x) →
        α ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range)
    (hZT : ∀ T : Sylow 2 (↥J ⧸ center ↥J), Nat.card (center (T : Subgroup (↥J ⧸ center ↥J))) = 2)
    (hcls : ∀ a b : ↥J, orderOf a = 2 → orderOf b = 2 → ∃ j : ↥J, b = j⁻¹ * a * j)
    (hpow : ∀ a : ↥J, orderOf a = 2 → ∃ y : ↥J, y ^ 8 = a)
    (hC2 : ∀ P : Subgroup G, P ≤ centralizer (J : Set G) → IsPGroup 2 P → Nat.card P ≤ 2)
    {t : G} (ht : orderOf t = 2) (htJ : t ∈ centralizer (J : Set G)) :
    ∃ (P : Sylow 2 G) (z : G), z ∈ J ∧ orderOf z = 2 ∧ z ∈ (P : Subgroup G) ∧
      (∀ p ∈ (P : Subgroup G), p * z = z * p) ∧ t ∈ (P : Subgroup G) ∧
      IsSylowTwoIn ((P : Subgroup G) ⊓ centralizer ({t} : Set G)) (centralizer ({t} : Set G)) ∧
      CFSG.GH74.GLS.Bg.Thompson.IsExtremalIn 2 (P : Subgroup G) t ∧
      (∀ w ∈ (P : Subgroup G) ⊓ centralizer ({t} : Set G),
        (∀ s ∈ (P : Subgroup G) ⊓ centralizer ({t} : Set G), w * s = s * w) → orderOf w = 2 →
          w = z ∨ w = t ∨ w = z * t) ∧
      (∀ y : G, y⁻¹ * t * y ≠ z) ∧ (∀ y : G, y⁻¹ * (z * t) * y ≠ z) ∧
      ∀ u ∈ J, orderOf u = 2 → ∃ g : G, g⁻¹ * t * g = u * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← ht]
    exact pow_orderOf_eq_one t
  have hC4 : ∀ P : Subgroup G, P ≤ centralizer (J : Set G) → IsPGroup 2 P → Nat.card P ≤ 4 :=
    fun P hPC hP => (hC2 P hPC hP).trans (by norm_num)
  have hcyc : ∀ P : Subgroup G, P ≤ centralizer (J : Set G) → IsPGroup 2 P → IsCyclic P := by
    intro P hPC hP
    have h2 := hC2 P hPC hP
    have h0 : 0 < Nat.card P := Nat.card_pos
    exact isCyclic_of_card_dvd_prime (p := 2) (by interval_cases (Nat.card P) <;> norm_num)
  have hJN : centralizer ({t} : Set G) ≤ normalizer (J : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      hst.assembly htJ ht).1
  set C : Subgroup G := centralizer ({t} : Set G) with hCdef
  obtain ⟨S₁⟩ := (inferInstance : Nonempty (Sylow 2 ↥C))
  set S : Subgroup G := (S₁ : Subgroup ↥C).map C.subtype with hSdef
  have hS : IsSylowTwoIn S C := by
    refine ⟨map_subtype_le _, S₁, ?_⟩
    rw [hSdef, ← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective
      C.subtype_injective]
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S C := ⟨S₁, rfl⟩
  have hSp : IsPGroup 2 S := S₁.isPGroup'.map _
  have htC : t ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have htc : ∀ s ∈ S, s * t = t * s := fun s hs => mem_centralizer_singleton_iff.mp (hS.1 hs)
  have htS : t ∈ S := by
    refine CFSG.AGLEmbedding.sylow_contains_centralizing_order_prime S₁ t htC ?_ ht
    rw [mem_centralizer_iff]
    intro s hs
    exact htc s hs
  obtain ⟨z, hzS, hzc, hz⟩ := exists_mem_inf_center_of_card_center_sylow hst hZ hZT ht htJ hS
  have hZ' := fun w hwS hwc hw =>
    eq_or_eq_or_eq_of_mem_center_of_sylow_fix hst hZ hcen hfix hZT hcyc ht htJ hS hzS hzc hz
      (w := w) hwS hwc hw
  have hnotJ : ∀ g : G, g⁻¹ * t * g ∉ J :=
    conj_not_mem_of_forall_pow_eight hst hOut hZ hpow hC4 ht htJ
  have hnot : ∀ g : G, g⁻¹ * t * g ≠ z := fun g hg => hnotJ g (hg ▸ hzS.2)
  have hzt : z ≠ t := fun h' => hnotJ 1 (by rw [inv_one, one_mul, mul_one, ← h']; exact hzS.2)
  have hz2 : z * z = 1 := by
    rw [← pow_two, ← hz]
    exact pow_orderOf_eq_one z
  have hJt : ∀ j ∈ J, j * t = t * j := fun j hj => mem_centralizer_iff.mp htJ j hj
  have hclsz : ∀ u ∈ J, orderOf u = 2 → ∃ j ∈ J, u = j⁻¹ * z * j := by
    intro u huJ hu
    obtain ⟨j, hj⟩ := hcls ⟨z, hzS.2⟩ ⟨u, huJ⟩ (by rw [Subgroup.orderOf_mk]; exact hz)
      (by rw [Subgroup.orderOf_mk]; exact hu)
    exact ⟨j, j.2, by simpa using congrArg Subtype.val hj⟩
  have hnotSyl : ¬ ∃ P : Sylow 2 G, (P : Subgroup G) = S := by
    rintro ⟨P, hP⟩
    obtain ⟨g₀, hgne, hgc⟩ :=
      CFSG.SeitzReduction.F4Pilot.exists_conj_ne_commute_of_isSimpleGroup hnonab ht
    obtain ⟨g, rfl⟩ : ∃ g : G, g⁻¹ = g₀ := ⟨g₀⁻¹, inv_inv g₀⟩
    rw [inv_inv] at hgne hgc
    have hs₀C : g * t * g⁻¹ ∈ C := mem_centralizer_singleton_iff.mpr hgc
    have hs₀ord : orderOf (g * t * g⁻¹) = 2 := by
      rw [show g * t * g⁻¹ = (MulAut.conj g) t by simp, MulEquiv.orderOf_eq, ht]
    have hs₀p : IsPGroup 2 (zpowers (g * t * g⁻¹)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs₀ord, pow_one])
    obtain ⟨c, hcC, hcS⟩ := CFSG.GH72.exists_mem_conj_mem_of_isSylowOf hSyl hs₀C hs₀p
    set y : G := (c * g)⁻¹ with hydef
    set s : G := c * (g * t * g⁻¹) * c⁻¹ with hsdef
    have hsy : s = y⁻¹ * t * y := by rw [hsdef, hydef]; group
    have hsS : s ∈ S := hcS
    have hs : orderOf s = 2 := by
      rw [hsy, show y⁻¹ * t * y = (MulAut.conj y⁻¹) t by simp, MulEquiv.orderOf_eq, ht]
    have hs2 : s * s = 1 := by
      rw [← pow_two, ← hs]
      exact pow_orderOf_eq_one s
    have hct : c * t = t * c := mem_centralizer_singleton_iff.mp hcC
    have hsne : s ≠ t := by
      intro h
      apply hgne
      calc g * t * g⁻¹ = c⁻¹ * s * c := by rw [hsdef]; group
        _ = c⁻¹ * (t * c) := by rw [h, mul_assoc]
        _ = t := by rw [← hct, ← mul_assoc, inv_mul_cancel, one_mul]
    have hst' : s * t = t * s := htc s hsS
    have hPS : ∀ b ∈ (P : Subgroup G), b ∈ S := fun b hb => hP ▸ hb
    have hSP : ∀ b ∈ S, b ∈ (P : Subgroup G) := fun b hb => hP.symm ▸ hb
    by_cases hin : ∃ j ∈ J, ∃ c' ∈ centralizer (J : Set G), s = j * c'
    · obtain ⟨j, hj, c', hc', hsjc⟩ := hin
      rcases mem_or_mul_mem_of_eq_mul hZ hC2 ht htJ ⟨1, by rw [pow_one, pow_two, hs2]⟩ hst' hj hc'
          hsjc with hsJ | hstJ
      · exact hnotJ y (hsy ▸ hsJ)
      ·
        have hst1 : s * t ≠ 1 := by
          intro h
          apply hsne
          calc s = s * (t * t) := by rw [ht2, mul_one]
            _ = (s * t) * t := (mul_assoc s t t).symm
            _ = t := by rw [h, one_mul]
        have hstord : orderOf (s * t) = 2 := by
          refine orderOf_eq_prime ?_ hst1
          rw [pow_two]
          calc s * t * (s * t) = s * (t * s) * t := by group
            _ = s * (s * t) * t := by rw [← hst']
            _ = (s * s) * (t * t) := by group
            _ = 1 := by rw [hs2, ht2, mul_one]
        obtain ⟨j', hj'J, hj'⟩ := hclsz (s * t) hstJ hstord
        have hfus : (y * j'⁻¹)⁻¹ * t * (y * j'⁻¹) = z * t := by
          have hs' : s = j'⁻¹ * z * j' * t := by
            rw [← hj']
            calc s = s * (t * t) := by rw [ht2, mul_one]
              _ = s * t * t := (mul_assoc s t t).symm
          have hj't : j' * t = t * j' := hJt j' hj'J
          calc (y * j'⁻¹)⁻¹ * t * (y * j'⁻¹) = j' * (y⁻¹ * t * y) * j'⁻¹ := by group
            _ = j' * s * j'⁻¹ := by rw [← hsy]
            _ = j' * (j'⁻¹ * z * j' * t) * j'⁻¹ := by rw [← hs']
            _ = z * (j' * t * j'⁻¹) := by group
            _ = z * t := by rw [hj't, mul_assoc, mul_inv_cancel, mul_one]
        exact false_of_sylow_of_conj_eq_mul P (hSP t htS) (fun b hb => htc b (hPS b hb))
          (hSP z hzS.1) (fun b hb => hzc b (hPS b hb)) ht hz hzt
          (fun w hw hwc hw2 => hZ' w (hPS w hw) (fun b hb => hwc b (hSP b hb)) hw2) hnot hfus
    ·
      have hJp : Group.IsPerfect ↥J := hst.1.1
      have h2elt : ∀ b ∈ (P : Subgroup G), ∃ k : ℕ, b ^ 2 ^ k = 1 := by
        intro b hb
        obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨b, hb⟩
        refine ⟨k, ?_⟩
        rw [← hk, Subgroup.orderOf_mk]
        exact pow_orderOf_eq_one b
      refine false_of_sylow_of_not_exists_mul_eq hnonab hst ht htJ hnotJ P
        (fun b hb => hS.1 (hPS b hb)) (hSP t htS) hzS.2
        (fun w hw hwc hw2 => hZ' w (hPS w hw) (fun b hb => hwc b (hSP b hb)) hw2)
        (hSP s hsS) hs hin ?_ ?_
      · intro b hb hb'
        exact exists_mul_eq_mul_of_mem_normalizer hJp hOut (hJN (hS.1 (hPS b hb)))
          (hJN (hS.1 hsS)) hb' hin
      · rintro b hb ⟨j, hj, c', hc', hbjc⟩
        exact mem_or_mul_mem_of_eq_mul hZ hC2 ht htJ (h2elt b hb) (htc b (hPS b hb)) hj hc' hbjc
  obtain ⟨P, hSP⟩ := hSp.exists_le_sylow
  have hlt : S < (P : Subgroup G) := lt_of_le_of_ne hSP fun h' => hnotSyl ⟨P, h'.symm⟩
  obtain ⟨x, hxP, -, hxt, hxz⟩ := exists_shear_of_lt ht hS P.isPGroup' hlt hzS.1 hzc hz hzt hZ'
    hnot
  have hzP : ∀ p ∈ (P : Subgroup G), p * z = z * p :=
    commute_of_shear ht hz hS P hSP hZ' hxP hxt hxz
  have hPS : (P : Subgroup G) ⊓ C = S := inf_centralizer_eq_of_isSylowTwoIn hS P.isPGroup' hSP
  refine ⟨P, z, hzS.2, hz, hSP hzS.1, hzP, hSP htS, hPS ▸ hS,
    isExtremalIn_of_isSylowTwoIn hS hPS, ?_, hnot, ?_, ?_⟩
  · intro w hw hwc hw2
    rw [hPS] at hw hwc
    exact hZ' w hw (fun b hb => (hwc b hb).symm) hw2
  · intro y hy
    apply hnot (x * y)
    calc (x * y)⁻¹ * t * (x * y) = y⁻¹ * (x⁻¹ * t * x) * y := by group
      _ = z := by rw [hxt, hy]
  · intro u huJ hu
    obtain ⟨j, hjJ, hj⟩ := hclsz u huJ hu
    refine ⟨x * j, ?_⟩
    have hjt : j * t = t * j := hJt j hjJ
    calc (x * j)⁻¹ * t * (x * j) = j⁻¹ * (x⁻¹ * t * x) * j := by group
      _ = j⁻¹ * z * j * (j⁻¹ * t * j) := by rw [hxt]; group
      _ = u * t := by
        rw [← hj]
        congr 1
        rw [mul_assoc, ← hjt, ← mul_assoc, inv_mul_cancel, one_mul]

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
