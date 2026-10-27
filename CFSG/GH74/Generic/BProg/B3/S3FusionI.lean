module

public import CFSG.GH74.Generic.BProg.B3.S3FusionCtx

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Fusion

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_in_T (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) {x : G}
    (hx : orderOf x = 2) {T : Subgroup G} (hT : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hxT : x ∈ T) : ∃ g : G, g * x * g⁻¹ ∈ T ∧ g * x * g⁻¹ ≠ x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hTtop : IsSylowOf 2 T ⊤ := isSylowOf_top_of_isolated hT hxT hcon
  obtain ⟨-, hTp, hdvd⟩ := isSylowOf_iff.1 hTtop
  rw [Subgroup.relIndex_top_right] at hdvd
  let Sy : Sylow 2 G := hTp.toSylow hdvd
  have hSy : (Sy : Subgroup G) = T := IsPGroup.toSylow_coe hTp hdvd
  have hxc : ∀ t ∈ (Sy : Subgroup G), t * x = x * t := fun t ht =>
    mem_centralizer_singleton_iff.mp (hT.le (hSy ▸ ht))
  obtain ⟨g, hg1, hg2⟩ := exists_conj_in_sylow_ne hs hn hx Sy (hSy ▸ hxT) hxc
  rw [hSy] at hg1
  apply hg2
  have := hcon g⁻¹ (by simpa using hg1)
  simpa using this

theorem exists_conj_of_piC_eq {x a b : G} (ha : a ∈ centralizer ({x} : Set G))
    (hb : b ∈ centralizer ({x} : Set G)) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (h : piC x a = piC x b) : ∃ r ∈ centralizer ({x} : Set G), r * a * r⁻¹ = b := by
  obtain ⟨r, -, hr⟩ := S1.exists_conj_of_proj_eq (u := ⟨a, ha⟩) (v := ⟨b, hb⟩) (Subtype.ext ha2)
    (Subtype.ext hb2) (by rwa [piC_of_mem x ha, piC_of_mem x hb] at h)
  exact ⟨(r : G), r.2, congrArg Subtype.val hr⟩

theorem fusion_of_inner {x y u : G} {K : Subgroup G}
    (hshape : BarShape (CentralizerBar x) (xbar x) (S3.imgBar x K)) (hx : orderOf x = 2)
    (hyC : y ∈ centralizer ({x} : Set G)) (hyK : y ∈ K) (hy : orderOf y = 2)
    (huC : u ∈ centralizer ({x} : Set G)) (hu2 : u * u = 1) (hune : u ≠ x)
    (hconj : ∃ g : G, g * x * g⁻¹ = u)
    (hin : ∃ k ∈ S3.imgBar x K, ∃ c ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)), piC x u = k * c) :
    (∃ g : G, g * x * g⁻¹ = y) ∨ (∃ g : G, g * x * g⁻¹ = x * y) := by
  classical
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  have hy1 : y ≠ 1 := fun h => by
    rw [h, orderOf_one] at hy
    omega
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hxy : x * y = y * x := (mem_centralizer_singleton_iff.mp hyC).symm
  obtain ⟨g₀, hg₀⟩ := hconj
  obtain ⟨k, hk, c, hc, hukc⟩ := hin
  have hkc : k * c = c * k := (mem_centralizer_iff.mp hc k hk)
  have hpu2 : piC x u * piC x u = 1 := by rw [← piC_mul x huC huC, hu2, piC_one]
  have hkkcc : (k * k) * (c * c) = 1 := by
    calc (k * k) * (c * c) = (k * c) * (k * c) := by
          calc (k * k) * (c * c) = k * (k * c) * c := by group
            _ = k * (c * k) * c := by rw [hkc]
            _ = (k * c) * (k * c) := by group
      _ = 1 := by rw [← hukc]; exact hpu2
  have hk2 : k * k = 1 := by
    have hkk : k * k ∈ S3.imgBar x K := (S3.imgBar x K).mul_mem hk hk
    have hu' : k * k = (c * c)⁻¹ := eq_inv_of_mul_eq_one_left hkkcc
    have hcc : (c * c)⁻¹ ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
        Set (CentralizerBar x)) :=
      (centralizer _).inv_mem ((centralizer _).mul_mem hc hc)
    have hmem : (⟨k * k, hkk⟩ : ↥(S3.imgBar x K)) ∈ center ↥(S3.imgBar x K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      rw [← hu'] at hcc
      exact (mem_centralizer_iff.mp hcc g g.2)
    rw [hshape.centerless, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hc2 : c * c = 1 := by rwa [hk2, one_mul] at hkkcc
  have hcx : c = 1 ∨ c = xbar x := by
    by_cases hc1 : c = 1
    · exact Or.inl hc1
    · exact Or.inr (hshape.only c hc (orderOf_eq_prime (by rw [sq]; exact hc2) hc1))
  have hu1 : u ≠ 1 := by
    intro h
    have : x = 1 := by
      have e : x = g₀⁻¹ * (g₀ * x * g₀⁻¹) * g₀ := by group
      rw [e, hg₀, h]
      group
    rw [this, orderOf_one] at hx
    omega
  have hk1 : k ≠ 1 := by
    intro hk1
    rw [hk1, one_mul] at hukc
    rcases hcx with hc1 | hc1
    · rw [hc1] at hukc
      have hTp : IsPGroup 2 ↥(Subgroup.zpowers u) := isPGroup_zpowers_of_involution hu2
      exact hu1 (eq_one_of_piC_eq_one hTp (Subgroup.zpowers_le.mpr huC) (Subgroup.mem_zpowers u)
        hukc)
    · rw [hc1, ← piC_x x] at hukc
      obtain ⟨r, hrC, hr⟩ := exists_conj_of_piC_eq huC hxC hu2 hx2 hukc
      apply hune
      have hrx : r * x = x * r := mem_centralizer_singleton_iff.mp hrC |>.symm.symm
      calc u = r⁻¹ * (r * u * r⁻¹) * r := by group
        _ = r⁻¹ * x * r := by rw [hr]
        _ = x := by
          have : r⁻¹ * x * r = r⁻¹ * (x * r) := by group
          rw [this, ← hrx]; group
  have hybK : piC x y ∈ S3.imgBar x K := mem_imgBar.2 ⟨⟨y, hyC⟩, hyK, (piC_of_mem x hyC).symm⟩
  have hyb2 : piC x y * piC x y = 1 := by rw [← piC_mul x hyC hyC, hy2, piC_one]
  have hyb1 : piC x y ≠ 1 := fun h => by
    have hTp : IsPGroup 2 ↥(Subgroup.zpowers y) := isPGroup_zpowers_of_involution hy2
    exact hy1 (eq_one_of_piC_eq_one hTp (Subgroup.zpowers_le.mpr hyC) (Subgroup.mem_zpowers y) h)
  obtain ⟨κ, hκK, hκ⟩ := hshape.exists_conj_invol hk hybK hk2 hk1 hyb2 hyb1
  obtain ⟨κ₀, hκ₀K, hκ₀⟩ := mem_imgBar.1 hκK
  have hκ₀C : (κ₀ : G) ∈ centralizer ({x} : Set G) := κ₀.2
  set u' : G := (κ₀ : G) * u * (κ₀ : G)⁻¹ with hu'def
  have hu'C : u' ∈ centralizer ({x} : Set G) :=
    (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).mul_mem hκ₀C huC)
      ((centralizer ({x} : Set G)).inv_mem hκ₀C)
  have hu'2 : u' * u' = 1 := by
    calc u' * u' = (κ₀ : G) * (u * u) * (κ₀ : G)⁻¹ := by rw [hu'def]; group
      _ = 1 := by rw [hu2]; group
  have hpiκ : piC x (κ₀ : G) = κ := by rw [piC_of_mem x hκ₀C]; exact hκ₀
  have hpu' : piC x u' = piC x y * c := by
    rw [hu'def, piC_mul x (mul_mem hκ₀C huC) ((centralizer ({x} : Set G)).inv_mem hκ₀C),
      piC_mul x hκ₀C huC, piC_inv x hκ₀C, hpiκ, hukc]
    have hcκ : c * κ⁻¹ = κ⁻¹ * c := (mem_centralizer_iff.mp hc κ⁻¹ ((S3.imgBar x K).inv_mem hκK)).symm
    calc κ * (k * c) * κ⁻¹ = (κ * k) * (c * κ⁻¹) := by group
      _ = (κ * k) * (κ⁻¹ * c) := by rw [hcκ]
      _ = (κ * k * κ⁻¹) * c := by group
      _ = piC x y * c := by rw [hκ]
  have hxyC : x * y ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).mul_mem hxC hyC
  have hxy2 : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2, hy2, one_mul]
  rcases hcx with hc1 | hc1
  · rw [hc1, mul_one] at hpu'
    obtain ⟨r, -, hr⟩ := exists_conj_of_piC_eq hu'C hyC hu'2 hy2 (hpu'.trans rfl)
    left
    refine ⟨r * (κ₀ : G) * g₀, ?_⟩
    calc r * (κ₀ : G) * g₀ * x * (r * (κ₀ : G) * g₀)⁻¹
        = r * ((κ₀ : G) * (g₀ * x * g₀⁻¹) * (κ₀ : G)⁻¹) * r⁻¹ := by group
      _ = r * u' * r⁻¹ := by rw [hg₀]
      _ = y := hr
  · rw [hc1] at hpu'
    obtain ⟨r, -, hr⟩ := exists_conj_of_piC_eq hu'C hxyC hu'2 hxy2 (by
      rw [hpu', piC_mul x hxC hyC, piC_x x]
      exact xbar_comm x _)
    right
    refine ⟨r * (κ₀ : G) * g₀, ?_⟩
    calc r * (κ₀ : G) * g₀ * x * (r * (κ₀ : G) * g₀)⁻¹
        = r * ((κ₀ : G) * (g₀ * x * g₀⁻¹) * (κ₀ : G)⁻¹) * r⁻¹ := by group
      _ = r * u' * r⁻¹ := by rw [hg₀]
      _ = x * y := hr

@[expose] def OuterCaseFusion {G : Type} [Group G] (x : G) (K : Subgroup G) (y : G) : Prop :=
  ∀ u : G, u ∈ centralizer ({x} : Set G) → u * u = 1 → u ≠ x → (∃ g : G, g * x * g⁻¹ = u) →
    (¬ ∃ k ∈ S3.imgBar x K, ∃ c ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)), piC x u = k * c) →
    (∃ g : G, g * x * g⁻¹ = y) ∨ (∃ g : G, g * x * g⁻¹ = x * y)

theorem lemma302 {x y : G} {K : Subgroup G} (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hshape : BarShape (CentralizerBar x) (xbar x) (S3.imgBar x K)) (hx : orderOf x = 2)
    (hyC : y ∈ centralizer ({x} : Set G)) (hyK : y ∈ K) (hy : orderOf y = 2)
    {T : Subgroup G} (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) (hxT : x ∈ T)
    (hOuter : OuterCaseFusion x K y) :
    (∃ g : G, g * x * g⁻¹ = y) ∨ (∃ g : G, g * x * g⁻¹ = x * y) := by
  obtain ⟨g, hgT, hgne⟩ := exists_conj_in_T hs hn hx hT hxT
  have huC : g * x * g⁻¹ ∈ centralizer ({x} : Set G) := hT.le hgT
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hu2 : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
    calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  by_cases hin : ∃ k ∈ S3.imgBar x K, ∃ c ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)), piC x (g * x * g⁻¹) = k * c
  · exact fusion_of_inner hshape hx hyC hyK hy huC hu2 hgne ⟨g, rfl⟩ hin
  · exact hOuter _ huC hu2 hgne ⟨g, rfl⟩ hin

end S3Fusion

end CFSG.GH74.Generic.BProg.B3
