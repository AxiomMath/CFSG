module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step3

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace Q81

variable {G : Type} [Group G] [Finite G]

theorem inf_center_ne_bot {R U : Subgroup G} (hR : IsPGroup 2 R) (hUR : U ≤ R)
    (hUn : R ≤ normalizer (U : Set G)) (hU : U ≠ ⊥) :
    U ⊓ (R ⊓ centralizer (R : Set G)) ≠ ⊥ := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hnormal : (U.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf R ≠ ⊥ := by
    intro h
    apply hU
    rw [← map_subgroupOf_eq_of_le hUR, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ centralizer (R : Set G) := by
    rw [mem_centralizer_iff]
    intro r hr
    exact congrArg Subtype.val (mem_center_iff.mp hy.2 ⟨r, hr⟩)
  intro h
  have hmem : (y : G) ∈ U ⊓ (R ⊓ centralizer (R : Set G)) := ⟨hy.1, y.2, hyC⟩
  rw [h, mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem mem_of_normalized {R U : Subgroup G} (hR : IsPGroup 2 R) {z : G} (hz : orderOf z = 2)
    (hZ : R ⊓ centralizer (R : Set G) = zpowers z) (hUR : U ≤ R)
    (hUn : R ≤ normalizer (U : Set G)) (hU : U ≠ ⊥) : z ∈ U := by
  have h1 := inf_center_ne_bot hR hUR hUn hU
  rw [hZ] at h1
  obtain ⟨⟨y, hy⟩, hy1⟩ := ne_bot_iff_exists_ne_one.mp h1
  obtain ⟨hyU, hyz⟩ := mem_inf.mp hy
  rcases eq_one_or_eq_of_mem_zpowers_two hz hyz with h2 | h2
  · exact absurd (Subtype.ext h2) hy1
  · rw [← h2]
    exact hyU

end Q81

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Setting46e

variable {S : Subgroup X} {w z : X} {V : Subgroup X} {i₀ j₀ : ℕ}

theorem exists_R [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hs : Setting46e t L 3 4 S w z V i₀ j₀)
    (hQ : ∀ i j : ℕ, IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →
      (Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
          center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSL 4 3 1 ∨
        Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
          center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSU 4 3 1) →
      hs.setup.Q81Data i j)
    {i j : ℕ} (hD : hs.setup.Q81Data i j) (hF : L4U4ThreeInvolutionFacts)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hKG : AutPSL2SylowInput)
    (hβt : ∀ c : X, c * t * c⁻¹ ≠ w ^ (orderOf w / 2) * t ^ i * z ^ j) :
    ∃ W R : Subgroup X, IsSylowOf 2 W (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ∧
      zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W ∧
      W ⊓ centralizer (W : Set X) = closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} ∧
      IsSylowOf 2 R ⊤ ∧ W ≤ R ∧ W ≠ R ∧ R ≤ centralizer {z} ∧
      R ⊓ centralizer (R : Set X) = zpowers z ∧
      R ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} = W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hW, -, hTW, -, hZW⟩ := hD.exists_W hF hFC hKC hKG
  have htW : t ∈ W := hTW (mem_sup_left (mem_sup_left (mem_zpowers t)))
  obtain ⟨R, hR, hWR⟩ := Q81.exists_isSylowOf_ge hW.isPGroup (le_top : W ≤ ⊤)
  have hWne : W ≠ R := fun h1 =>
    hs.not_isSylowOf_top hnab hQ hD hβt hW.le hW.isPGroup htW (h1 ▸ hR)
  have hRp := hR.isPGroup
  have hRβ : R ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} = W :=
    hW.eq_of_le (le_inf hWR hW.le) inf_le_right (hRp.to_le inf_le_left)
  have hlt : W < R ⊓ normalizer (W : Set X) := by
    have : Group.IsNilpotent R := hRp.isNilpotent
    have hWR' : W.subgroupOf R ≠ ⊤ := by
      intro h1
      apply hWne
      refine le_antisymm hWR fun x hx => ?_
      have : (⟨x, hx⟩ : R) ∈ W.subgroupOf R := h1 ▸ mem_top _
      exact mem_subgroupOf.mp this
    have h2 := (Group.normalizerCondition_of_isNilpotent (G := R)) _ (lt_top_iff_ne_top.mpr hWR')
    obtain ⟨⟨g, hgR⟩, hgN, hgW⟩ := IsConcreteLE.exists_of_lt h2
    refine lt_of_le_of_ne (le_inf hWR le_normalizer) fun h3 => hgW ?_
    have hg : g ∈ R ⊓ normalizer (W : Set X) := by
      refine mem_inf.mpr ⟨hgR, mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
      · have h4 := (mem_normalizer_iff.mp hgN ⟨y, hWR hy⟩).mp (mem_subgroupOf.mpr hy)
        exact mem_subgroupOf.mp h4
      · have hyR : y ∈ R := by
          have h4 : y = g⁻¹ * (g * y * g⁻¹) * g := by group
          rw [h4]
          exact mul_mem (mul_mem (inv_mem hgR) (hWR hy)) hgR
        have h4 := (mem_normalizer_iff.mp hgN ⟨y, hyR⟩).mpr (mem_subgroupOf.mpr hy)
        exact mem_subgroupOf.mp h4
    rw [← h3] at hg
    exact mem_subgroupOf.mpr hg
  obtain ⟨g, hgN, hgW⟩ := IsConcreteLE.exists_of_lt hlt
  obtain ⟨hgR, hgNW⟩ := mem_inf.mp hgN
  have hgZ := Q81.mem_normalizer_center hgNW
  rw [hZW] at hgZ
  have hgz := hD.conj_z_eq_of_normalizes hF hFC hKC hgZ
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one (w ^ (orderOf w / 2) * t ^ i * z ^ j)
    rwa [hs.setup.orderOf_beta i j] at h1
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order, pow_orderOf_eq_one]
  have hβz : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z =
      z * (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
    (mem_centralizer_singleton_iff.mp (hs.setup.z_mem_centralizer_beta hFC hKC i j)).symm
  have hgβ : g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ =
      (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z := by
    have hmem : g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ∈
        closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} :=
      (mem_normalizer_iff.mp hgZ _).mp (subset_closure (by simp))
    rcases mem_closure_pair hβ2 hz2 hβz hmem with h1 | h1 | h1 | h1
    · exfalso
      have h2 : w ^ (orderOf w / 2) * t ^ i * z ^ j = 1 := by
        calc w ^ (orderOf w / 2) * t ^ i * z ^ j =
              g⁻¹ * (g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      have h3 := hs.setup.orderOf_beta i j
      rw [h2, orderOf_one] at h3
      exact absurd h3 (by decide)
    · exfalso
      apply hgW
      rw [← hRβ]
      refine mem_inf.mpr ⟨hgR, mem_centralizer_singleton_iff.mpr ?_⟩
      calc g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
            g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ * g := by group
        _ = (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g := by rw [h1]
    · exfalso
      apply hs.setup.z_ne_beta i j
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = g⁻¹ * (g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹) * g := by rw [hgz, h1]
        _ = w ^ (orderOf w / 2) * t ^ i * z ^ j := by group
    · exact h1
  have hZR : R ⊓ centralizer (R : Set X) ≤ zpowers z := by
    intro x hx
    obtain ⟨hxR, hxc⟩ := mem_inf.mp hx
    have hxW : x ∈ W := by
      rw [← hRβ]
      refine mem_inf.mpr ⟨hxR, mem_centralizer_singleton_iff.mpr ?_⟩
      exact (mem_centralizer_iff.mp hxc _ (hWR (hTW (hs.setup.beta_mem_T i j)))).symm
    have hxZ : x ∈ closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} := by
      rw [← hZW]
      exact mem_inf.mpr ⟨hxW, mem_centralizer_iff.mpr fun y hy => mem_centralizer_iff.mp hxc y
        (hWR hy)⟩
    have hxg : g * x = x * g := mem_centralizer_iff.mp hxc g hgR
    rcases mem_closure_pair hβ2 hz2 hβz hxZ with h1 | h1 | h1 | h1
    · rw [h1]
      exact one_mem _
    · exfalso
      rw [h1] at hxg
      have h2 : g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ =
          w ^ (orderOf w / 2) * t ^ i * z ^ j := by rw [hxg]; group
      rw [hgβ] at h2
      apply hs.setup.z_ne_one
      calc z = (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹ *
            ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * z) := by group
        _ = 1 := by rw [h2]; group
    · rw [h1]
      exact mem_zpowers z
    · exfalso
      rw [h1] at hxg
      have h2 : g * ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * z) * g⁻¹ =
          (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z := by rw [hxg]; group
      rw [show g * ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * z) * g⁻¹ =
          (g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹) * (g * z * g⁻¹) by group,
        hgβ, hgz] at h2
      apply hs.setup.z_ne_one
      calc z = ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * z)⁻¹ *
            ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * z * z) := by group
        _ = 1 := by rw [h2]; group
  have hRnt : Nontrivial R := by
    refine ⟨⟨⟨t, hWR htW⟩, 1, fun h1 => ?_⟩⟩
    have h2 : t = 1 := congrArg Subtype.val h1
    have h3 := hs.standing.config.orderOf_eq
    rw [h2, orderOf_one] at h3
    exact absurd h3 (by decide)
  have hZR' : R ⊓ centralizer (R : Set X) = zpowers z := by
    refine le_antisymm hZR ?_
    have := hRp.center_nontrivial
    obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : center R)
    have hyc : (y : X) ∈ R ⊓ centralizer (R : Set X) :=
      mem_inf.mpr ⟨y.2, mem_centralizer_iff.mpr fun r hr =>
        congrArg Subtype.val (mem_center_iff.mp hy ⟨r, hr⟩)⟩
    rcases Q81.eq_one_or_eq_of_mem_zpowers_two hs.setup.z_order (hZR hyc) with h1 | h1
    · exact absurd (Subtype.ext (Subtype.ext h1)) hy1
    · rw [zpowers_le, ← h1]
      exact hyc
  have hRz : R ≤ centralizer {z} := by
    intro x hx
    have hzZ : z ∈ R ⊓ centralizer (R : Set X) := by rw [hZR']; exact mem_zpowers z
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (mem_inf.mp hzZ).2 x hx)
  exact ⟨W, R, hW, hTW, hZW, hR, hWR, hWne, hRz, hZR', hRβ⟩

end Setting46e

end CFSG.ComponentClassification.HarrisLit
