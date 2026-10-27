module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbX
import CFSG.Adapters.WholeGroupLayer

public section

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G] [Finite G]

theorem goldschmidt_of_normal (hGold : Asc76X.GoldschmidtTheoremA) {X : Subgroup G} [X.Normal]
    (hXs : IsSimpleGroup X) (hX2 : ¬ IsPGroup 2 X) (hCX : centralizer (X : Set G) = ⊥)
    (hO : standardComponentOddCore G = ⊥) (hcomm : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ X)
    (S : Sylow 2 G) {W : Subgroup G} (hWS : W ≤ S) (hWab : IsMulCommutative W)
    (hWcl : ∀ a ∈ W, ∀ x : G, x⁻¹ * a * x ∈ (S : Subgroup G) → x⁻¹ * a * x ∈ W)
    (hW1 : W ≠ ⊥) : W ≤ X ∧ ∀ v ∈ (S : Subgroup G), v ∈ X → v ^ 2 = 1 → v ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hGa, hGb, -⟩ := hGold G S W hWS hWab hWcl
  set M := normalClosure (W : Set G) with hMdef
  have hMn : M.Normal := normalClosure_normal
  have hWM : W ≤ M := subset_normalClosure
  have hO' : CFSG.Open.goldschmidtOddCore ↥M = ⊥ := Asc76X.oddCore_eq_bot_of_normal' hO hMn
  set π := QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore ↥M) with hπdef
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO']
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Wb := (W.subgroupOf M).map π with hWbdef
  have hGb' : Wb = CFSG.Open.pCore 2 (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) ⊔
      Subgroup.closure {t | t ∈ ((S : Subgroup G).subgroupOf M).map π ⊓
        CFSG.Open.goldschmidtLayer (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) ∧ t ^ 2 = 1} := hGb
  have hQW : CFSG.Open.pCore 2 (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) ≤ Wb := by
    rw [hGb']
    exact le_sup_left
  set Q₀ := ((CFSG.Open.pCore 2 (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M)).comap π).map M.subtype
    with hQ₀def
  have hQ₀W : Q₀ ≤ W := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨w, hw, hwm⟩ := hQW hm
    have hwm' : w = m := hπinj hwm
    rw [← hwm']
    exact hw
  have hQ₀n : Q₀.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hx
    have h1 : (Asc76X.conjQuot hMn g) (π m) ∈
        CFSG.Open.pCore 2 (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) := by
      rw [← Asc76X.openPCore_map_eq 2 (Asc76X.conjQuot hMn g)]
      exact ⟨π m, hm, rfl⟩
    rw [hπdef, Asc76X.conjQuot_mk] at h1
    exact ⟨⟨g * m * g⁻¹, hMn.conj_mem m m.2 g⟩, h1, rfl⟩
  have hQ₀bot : Q₀ = ⊥ := by
    have hQ₀2 : IsPGroup 2 Q₀ := (S.isPGroup').to_le (hQ₀W.trans hWS)
    have hQX : Q₀ ⊓ X = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q₀.subgroupOf X) with h1 | h1
      · rw [eq_bot_iff]
        intro y hy
        obtain ⟨hyQ, hyX⟩ := mem_inf.mp hy
        have h2 : (⟨y, hyX⟩ : X) ∈ Q₀.subgroupOf X := mem_subgroupOf.mpr hyQ
        rw [h1, mem_bot] at h2
        exact mem_bot.mpr (congrArg Subtype.val h2)
      · exfalso
        apply hX2
        intro y
        have h2 : y ∈ Q₀.subgroupOf X := by rw [h1]; exact mem_top y
        obtain ⟨n, hn⟩ := hQ₀2 ⟨y, mem_subgroupOf.mp h2⟩
        refine ⟨n, Subtype.ext ?_⟩
        have := congrArg Subtype.val hn
        simpa using this
    have hc : ⁅Q₀, X⁆ = ⊥ := le_bot_iff.mp ((Subgroup.commutator_le_inf Q₀ X).trans hQX.le)
    rw [← le_bot_iff, ← hCX]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc
  have hQbot : CFSG.Open.pCore 2 (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨m, rfl⟩ := hπsurj q
    have hm : (m : G) ∈ Q₀ := ⟨m, hq, rfl⟩
    rw [hQ₀bot, mem_bot] at hm
    rw [mem_bot, show m = 1 from Subtype.ext hm, map_one]
  have hLE : CFSG.Open.goldschmidtLayer (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) = ⊤ := by
    have hGa' : CFSG.Open.pCore 2 (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) ⊔
        CFSG.Open.goldschmidtLayer (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) = ⊤ := hGa
    rwa [hQbot, bot_sup_eq] at hGa'
  have hlayer : CFSG.Open.goldschmidtLayer (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) =
      CFSG.layer (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) :=
    CFSG.Adapters.goldschmidtLayer_eq_foundations _
  have hperf : ⁅(⊤ : Subgroup (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M)),
      (⊤ : Subgroup (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M))⁆ = ⊤ := by
    have := CFSG.LocalCores.layer_perfect (G := ↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M)
    rwa [← hlayer, hLE] at this
  have hMX : M ≤ X := by
    intro m hm
    have h1 : π ⟨m, hm⟩ ∈ (⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆).map π := by
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπsurj, hperf]
      exact mem_top _
    have h2 : (⟨m, hm⟩ : ↥M) ∈ ⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆ :=
      (mem_map_iff_mem hπinj).mp h1
    have h3 : m ∈ ⁅M, M⁆ := by
      have := mem_map_of_mem M.subtype h2
      rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype] at this
    refine (Subgroup.commutator_le.mpr fun a _ b _ => ?_) h3
    rw [commutatorElement_def]
    exact hcomm a b
  refine ⟨hWM.trans hMX, fun v hvS hvX hv2 => ?_⟩
  have hXM : X ≤ M := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf X) with h1 | h1
    · exfalso
      apply hW1
      rw [eq_bot_iff]
      intro w hw
      have h2 : (⟨w, hMX (hWM hw)⟩ : X) ∈ M.subgroupOf X := mem_subgroupOf.mpr (hWM hw)
      rw [h1, mem_bot] at h2
      exact mem_bot.mpr (congrArg Subtype.val h2)
    · intro y hy
      have h2 : (⟨y, hy⟩ : X) ∈ M.subgroupOf X := by rw [h1]; exact mem_top _
      exact mem_subgroupOf.mp h2
  have hvM : v ∈ M := hXM hvX
  have hmem : π ⟨v, hvM⟩ ∈ Wb := by
    rw [hGb', hQbot, bot_sup_eq, hLE, inf_top_eq]
    refine subset_closure ⟨⟨⟨v, hvM⟩, mem_subgroupOf.mpr hvS, rfl⟩, ?_⟩
    rw [← map_pow, show (⟨v, hvM⟩ : ↥M) ^ 2 = 1 from Subtype.ext (by simpa using hv2), map_one]
  obtain ⟨w, hw, hwv⟩ := hmem
  have hwv' : w = ⟨v, hvM⟩ := hπinj hwv
  have := mem_subgroupOf.mp hw
  rwa [hwv'] at this

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

theorem centralizer_X_eq_bot :
    centralizer ((rankTwoX A : Subgroup G) : Set G) = ⊥ := by
  obtain ⟨hXF, -⟩ := asc08Lemma34 G A h.toHyp31
  have hXs := h.isSimpleGroup_X
  have hle : centralizer ((rankTwoX A : Subgroup G) : Set G) ≤ rankTwoX A := by
    have := CFSG.centralizer_generalizedFitting_le G
    rwa [← hXF] at this
  obtain ⟨eA⟩ := h.equiv
  have hAX : A ≤ rankTwoX A := le_normalClosure
  rw [eq_bot_iff]
  intro y hy
  have hyX := hle hy
  have hcen : (⟨y, hyX⟩ : ↥(rankTwoX A)) ∈ center ↥(rankTwoX A) := by
    rw [mem_center_iff]
    intro u
    exact Subtype.ext (mem_centralizer_iff.mp hy u u.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥(rankTwoX A)) with h1 | h1
  · rw [h1, mem_bot] at hcen
    exact mem_bot.mpr (congrArg Subtype.val hcen)
  · exfalso
    have hcomm : ∀ a b : A, a * b = b * a := fun a b => by
      have h2 : (⟨a, hAX a.2⟩ : ↥(rankTwoX A)) ∈ center ↥(rankTwoX A) := by rw [h1]; exact mem_top _
      have h3 := mem_center_iff.mp h2 ⟨b, hAX b.2⟩
      exact Subtype.ext (congrArg Subtype.val h3).symm
    have hA5 : ∀ a b : A5, a * b = b * a := fun a b => by
      have := hcomm (eA.symm a) (eA.symm b)
      have := congrArg eA this
      simpa using this
    exact absurd hA5 (by decide)

theorem commutator_mem_X (a b : G) : a * b * a⁻¹ * b⁻¹ ∈ rankTwoX A := by
  have hXn : (rankTwoX A).Normal := normalClosure_normal
  have hdec : ∀ w : G, ∃ y ∈ rankTwoX A, ∃ s ∈ R, w = y * s := fun w => by
    have hw : w ∈ rankTwoX A ⊔ R := by rw [h.sup_top]; exact mem_top w
    exact AS76b.exists_mul_of_mem_sup_of_le_normalizer
      (by rw [normalizer_eq_top_iff.mpr hXn]; exact le_top) hw
  obtain ⟨x, hx, s, hs, rfl⟩ := hdec a
  obtain ⟨y, hy, t, ht, rfl⟩ := hdec b
  have hst : s * t = t * s := h.comm (mem_sup_left hs) (mem_sup_left ht)
  have e : x * s * (y * t) * (x * s)⁻¹ * (y * t)⁻¹ =
      x * (s * y * s⁻¹) * (s * t * s⁻¹) * x⁻¹ * t⁻¹ * y⁻¹ := by group
  have hst' : s * t * s⁻¹ = t := by rw [hst]; group
  rw [e, hst', show x * (s * y * s⁻¹) * t * x⁻¹ * t⁻¹ * y⁻¹ =
    x * (s * y * s⁻¹) * (t * x⁻¹ * t⁻¹) * y⁻¹ by group]
  exact mul_mem (mul_mem (mul_mem hx (hXn.conj_mem y hy s)) (hXn.conj_mem _ (inv_mem hx) t))
    (inv_mem hy)

theorem goldschmidt_X (hGold : Asc76X.GoldschmidtTheoremA)
    (S : Sylow 2 G) {W : Subgroup G} (hWS : W ≤ S) (hWab : IsMulCommutative W)
    (hWcl : ∀ a ∈ W, ∀ x : G, x⁻¹ * a * x ∈ (S : Subgroup G) → x⁻¹ * a * x ∈ W)
    (hW1 : W ≠ ⊥) : W ≤ rankTwoX A ∧
      ∀ v ∈ (S : Subgroup G), v ∈ rankTwoX A → v ^ 2 = 1 → v ∈ W := by
  have : (rankTwoX A).Normal := normalClosure_normal
  exact goldschmidt_of_normal hGold h.isSimpleGroup_X h.not_isPGroup_X h.centralizer_X_eq_bot
    h.oddCore h.commutator_mem_X S hWS hWab hWcl hW1

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
