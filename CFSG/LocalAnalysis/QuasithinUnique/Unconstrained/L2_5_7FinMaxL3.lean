module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxL3Fix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinL3Pkg
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxRank

public section

namespace CFSG.QuasithinUnique.Fin257

namespace L3

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.ComponentClassification

open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2]

theorem sq_wxy (c a b : F) :
    (wP c * xP a * yP b) * (wP c * xP a * yP b) = wP (a * b) := by
  have hWX : wP c * xP a = xP a * wP c := wP_mul_xP c a
  have hWY : wP c * yP b = yP b * wP c := wP_mul_yP c b
  have hZX : wP (a * b) * xP a = xP a * wP (a * b) := wP_mul_xP _ a
  calc wP c * xP a * yP b * (wP c * xP a * yP b)
      = wP c * xP a * (yP b * wP c) * xP a * yP b := by group
    _ = wP c * xP a * (wP c * yP b) * xP a * yP b := by rw [hWY]
    _ = wP c * (xP a * wP c) * yP b * xP a * yP b := by group
    _ = wP c * (wP c * xP a) * yP b * xP a * yP b := by rw [hWX]
    _ = (wP c * wP c) * xP a * (yP b * xP a) * yP b := by group
    _ = xP a * (yP b * xP a) * yP b := by rw [wP_mul_self, one_mul]
    _ = xP a * (wP (a * b) * xP a * yP b) * yP b := by rw [yP_mul_xP]
    _ = (xP a * wP (a * b)) * xP a * (yP b * yP b) := by group
    _ = (wP (a * b) * xP a) * xP a * (yP b * yP b) := by rw [hZX]
    _ = wP (a * b) * (xP a * xP a) * (yP b * yP b) := by group
    _ = wP (a * b) := by rw [xP_mul_self, yP_mul_self, mul_one, mul_one]

theorem mem_V1_or_V2_of_sq {g : projectiveSL 3 F} (hg : g ∈ projUnitriangular 3 F)
    (hg2 : g * g = 1) : g ∈ (V1 : Subgroup (projectiveSL 3 F)) ∨ g ∈ (V2 : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp hg
  rw [sq_wxy] at hg2
  have hab : a * b = 0 := (wP_eq_one_iff _).mp hg2
  rcases mul_eq_zero.mp hab with ha | hb
  · right
    subst ha
    refine mem_V2.mpr ⟨b, c, ?_⟩
    rw [xP_zero, mul_one]
    exact wP_mul_yP c b
  · left
    subst hb
    refine mem_V1.mpr ⟨a, c, ?_⟩
    rw [yP_zero, mul_one, wP_mul_xP]

theorem elem_le_V1_or_V2 {B : Subgroup (projectiveSL 3 F)} (hBU : B ≤ projUnitriangular 3 F)
    (hB : ∀ x ∈ B, x * x = 1) :
    B ≤ (V1 : Subgroup (projectiveSL 3 F)) ∨ B ≤ (V2 : Subgroup (projectiveSL 3 F)) :=
  CFSG.QuasithinUnique.Setup.X7b.subgroup_le_of_subset_union fun x hx =>
    mem_V1_or_V2_of_sq (hBU hx) (hB x hx)


theorem V1_eq_map_V2 : (V1 : Subgroup (projectiveSL 3 F)) =
    (V2 : Subgroup (projectiveSL 3 F)).map (iota (F := F)).toMonoidHom := by
  apply le_antisymm
  · intro g hg
    obtain ⟨a, c, rfl⟩ := mem_V1.mp hg
    exact ⟨yP a * wP c, mem_V2.mpr ⟨a, c, rfl⟩, iota_yP_wP a c⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact iota_mem_V1 hg

theorem card_V1_eq_card_V2 [Finite F] :
    Nat.card (V1 : Subgroup (projectiveSL 3 F)) = Nat.card (V2 : Subgroup (projectiveSL 3 F)) := by
  rw [V1_eq_map_V2]
  exact Subgroup.card_map_of_injective (iota (F := F)).injective

theorem xP_wP_inj {a c a' c' : F} (h : xP a * wP c = xP a' * wP c') : a = a' ∧ c = c' := by
  have hsq : (xP a * wP c) * (xP a' * wP c') = 1 := by
    rw [← h]
    have h2 := isElemAbelian_V1.2 _ (mem_V1.mpr ⟨a, c, rfl⟩ : xP a * wP c ∈ (V1 : Subgroup (projectiveSL 3 F)))
    simpa [pow_two] using h2
  rw [V1_mul] at hsq
  have haa : a + a' = 0 := by
    by_contra hne
    exact xP_wP_ne (a + a') (c + c') 0 hne (by rw [hsq, wP_zero])
  have ha : a = a' := CharTwo.add_eq_zero.mp haa
  subst ha
  rw [haa, xP_zero, one_mul] at hsq
  exact ⟨rfl, CharTwo.add_eq_zero.mp ((wP_eq_one_iff _).mp hsq)⟩

theorem card_V1 [Finite F] :
    Nat.card (V1 : Subgroup (projectiveSL 3 F)) = Nat.card F ^ 2 := by
  have hbij : Function.Bijective (fun p : F × F =>
      (⟨xP p.1 * wP p.2, mem_V1.mpr ⟨p.1, p.2, rfl⟩⟩ : (V1 : Subgroup (projectiveSL 3 F)))) := by
    constructor
    · intro p p' h
      have := xP_wP_inj (congrArg Subtype.val h)
      exact Prod.ext this.1 this.2
    · rintro ⟨g, hg⟩
      obtain ⟨a, c, rfl⟩ := mem_V1.mp hg
      exact ⟨(a, c), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, sq]


section Index

variable [Finite F]

theorem inf_linear_eq_inf_inner (E : Subgroup (MulAut (projectiveSL 3 F)))
    (h2 : ∀ a ∈ E, a * a = 1) :
    E ⊓ linearAutGroup 3 F = E ⊓ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
  obtain ⟨hID, -⟩ := standard_outer_quotients (K := F) (n := 3)
  refine le_antisymm ?_ (inf_le_inf_left _ hID)
  rintro a ⟨haE, haD⟩
  obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.mp haD
  exact ⟨haE, CFSG.QuasithinUnique.Setup.X7a.mem_inner_of_sq_conjAut (h2 _ haE)⟩

omit [CharP F 2] in
theorem relIndex_inf_semilinear_le (E : Subgroup (MulAut (projectiveSL 3 F))) :
    (E ⊓ semilinearAutGroup 3 F).relIndex E ≤ 2 := by
  obtain ⟨-, -, -, -, -, -, -, hRE, -⟩ := standard_outer_quotients (K := F) (n := 3)
  have hR : standardAutGroup 3 F = ⊤ := (automorphism_generation (K := F) le_rfl).1
  have hEi : (semilinearAutGroup 3 F).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hRE' : (semilinearAutGroup 3 F).index ≤ 2 := by
    rw [hR] at hRE
    have h1 : (semilinearAutGroup 3 F).relIndex ⊤ ≤ 2 := hRE
    rwa [Subgroup.relIndex_top_right] at h1
  rw [inf_comm, Subgroup.inf_relIndex_right]
  calc (semilinearAutGroup 3 F).relIndex E ≤ (semilinearAutGroup 3 F).relIndex ⊤ :=
        Subgroup.relIndex_le_of_le_right le_top
          (by rw [Subgroup.relIndex_top_right]; exact hEi)
    _ = (semilinearAutGroup 3 F).index := Subgroup.relIndex_top_right _
    _ ≤ 2 := hRE'


theorem relIndex_inner_le (E : Subgroup (MulAut (projectiveSL 3 F))) (h2 : ∀ a ∈ E, a * a = 1) :
    (E ⊓ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range).relIndex
      (E ⊓ semilinearAutGroup 3 F) ≤ 2 := by
  classical
  obtain ⟨hID, -, hDnorm, -, -, hEcyc, -, hRE, -, -⟩ := standard_outer_quotients (K := F) (n := 3)
  have hR : standardAutGroup 3 F = ⊤ := (automorphism_generation (K := F) le_rfl).1
  set I := (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range with hI
  set D := linearAutGroup 3 F with hD
  set Es := semilinearAutGroup 3 F with hEs
  have hDE : D ≤ Es := linearAutGroup_le_semilinearAutGroup
  have hAD : E ⊓ D = E ⊓ I := inf_linear_eq_inf_inner E h2
  set A0 := E ⊓ I with hA0
  have hDn : (D.subgroupOf Es).Normal := by
    rw [hR] at hDnorm
    rw [Subgroup.normal_subgroupOf_iff hDE]
    intro h k hh _
    exact ((Subgroup.normal_subgroupOf_iff le_top).mp hDnorm) h k hh (Subgroup.mem_top k)
  let θ : ↥(E ⊓ Es) →* ↥Es ⧸ D.subgroupOf Es :=
    (QuotientGroup.mk' (D.subgroupOf Es)).comp (Subgroup.inclusion inf_le_right)
  have hker : θ.ker = A0.subgroupOf (E ⊓ Es) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk (Subgroup.inclusion inf_le_right x) : ↥Es ⧸ D.subgroupOf Es) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have : (x : MulAut (projectiveSL 3 F)) ∈ E ⊓ D := ⟨x.2.1, hx⟩
      rwa [hAD] at this
    · intro hx
      have : (x : MulAut (projectiveSL 3 F)) ∈ E ⊓ D := by rwa [hAD]
      exact this.2
  have hcyc : IsCyclic (↥Es ⧸ D.subgroupOf Es) := by
    obtain ⟨g, hgE, hg⟩ := hEcyc
    refine ⟨⟨(QuotientGroup.mk (⟨g, hgE⟩ : ↥Es) : ↥Es ⧸ D.subgroupOf Es), fun q => ?_⟩⟩
    induction q using QuotientGroup.induction_on with
    | _ x =>
      obtain ⟨k, hk⟩ := hg x x.2
      refine ⟨-k, ?_⟩
      show (QuotientGroup.mk (⟨g, hgE⟩ : ↥Es) : ↥Es ⧸ D.subgroupOf Es) ^ (-k) =
        (QuotientGroup.mk x : ↥Es ⧸ D.subgroupOf Es)
      rw [← QuotientGroup.mk_zpow]
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      simpa [_root_.zpow_neg] using hk
  have hsq : ∀ y : ↥Es ⧸ D.subgroupOf Es, y ∈ θ.range → y ^ 2 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
      exact h2 (x : MulAut (projectiveSL 3 F)) x.2.1)
    rw [this, map_one]
  have hcard2 : Nat.card θ.range ≤ 2 := by
    have := Fintype.ofFinite (↥Es ⧸ D.subgroupOf Es)
    calc Nat.card θ.range
        ≤ Nat.card {y : ↥Es ⧸ D.subgroupOf Es // y ^ 2 = 1} :=
          Nat.card_le_card_of_injective (fun y => ⟨y.1, hsq y.1 y.2⟩)
            (fun a b h => Subtype.ext (by
              have := congrArg Subtype.val h
              simpa using this))
      _ ≤ 2 := by
        have h1 := IsCyclic.card_pow_eq_one_le (α := ↥Es ⧸ D.subgroupOf Es) (n := 2) (by norm_num)
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        exact h1
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact hcard2


theorem card_lt_of_outer {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (E : Subgroup (MulAut (projectiveSL 3 F))) (h2 : ∀ α ∈ E, α * α = 1)
    (hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α)
    (hU : ∀ α ∈ E, ∀ u ∈ projUnitriangular 3 F, α u ∈ projUnitriangular 3 F)
    (hout : ∃ θ ∈ E, θ ∉ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range) :
    Nat.card E < Nat.card (V1 : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨θ₀, hθ₀E, hθ₀I⟩ := hout
  set c : projectiveSL 3 F →* MulAut (projectiveSL 3 F) := MulAut.conj with hcdef
  set I := c.range with hI
  set Es := semilinearAutGroup 3 F with hEs
  set D := linearAutGroup 3 F with hD
  have hinj : Function.Injective c := conj_injective_of_center center_trivial_M
  set B := E.comap c with hB
  set E₀ := E ⊓ I with hE₀
  set E₁ := E ⊓ Es with hE₁
  have hEB : B.map c = E₀ := by
    rw [Subgroup.map_comap_eq, inf_comm]
  have hcardB : Nat.card E₀ = Nat.card B := by
    rw [← hEB]
    exact Subgroup.card_map_of_injective hinj
  obtain ⟨hB2, hBU⟩ := comap_conj_le_U (modelData_L3 hn hF) E h2 hU
  have hBV : B ≤ V1 ∨ B ≤ V2 := elem_le_V1_or_V2 hBU hB2
  have hBfix : ∀ θ ∈ E, ∀ g ∈ B, θ g = g := fun θ hθ g hg =>
    fixes_of_comm hinj (hc θ hθ _ hg)
  have hθ₀D : θ₀ ∉ D := by
    intro hD'
    have : θ₀ ∈ E ⊓ D := ⟨hθ₀E, hD'⟩
    rw [inf_linear_eq_inf_inner E h2] at this
    exact hθ₀I this.2
  have hBq : Nat.card B ≤ Nat.card F := card_le_of_not_linear hBV hθ₀D (hBfix θ₀ hθ₀E)
  have hE₀E₁ : E₀ ≤ E₁ := inf_le_inf_left _ (by
    obtain ⟨hID, -⟩ := standard_outer_quotients (K := F) (n := 3)
    exact hID.trans linearAutGroup_le_semilinearAutGroup)
  have hc1 : Nat.card E = E₁.relIndex E * Nat.card E₁ := by
    have := Subgroup.relIndex_mul_card (H := E₁) (K := E)
    rw [inf_of_le_left inf_le_left] at this
    exact this.symm
  have hc2 : Nat.card E₁ = E₀.relIndex E₁ * Nat.card E₀ := by
    have := Subgroup.relIndex_mul_card (H := E₀) (K := E₁)
    rw [inf_of_le_left hE₀E₁] at this
    exact this.symm
  have hi₁ : E₁.relIndex E ≤ 2 := relIndex_inf_semilinear_le E
  have hi₂ : E₀.relIndex E₁ ≤ 2 := relIndex_inner_le E h2
  have hEpos : 0 < Nat.card E := Nat.card_pos
  have hE₁pos : 0 < Nat.card E₁ := Nat.card_pos
  have hi₁pos : 0 < E₁.relIndex E := Nat.pos_of_ne_zero fun h => by
    rw [h, zero_mul] at hc1; omega
  have hi₂pos : 0 < E₀.relIndex E₁ := Nat.pos_of_ne_zero fun h => by
    rw [h, zero_mul] at hc2; omega
  rw [card_V1, hF]
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hqq : Nat.card F = 2 ^ n := hF
  by_cases hi : E₁.relIndex E = 1 ∨ E₀.relIndex E₁ = 1
  ·
    have hEle : Nat.card E ≤ 2 * Nat.card B := by
      rw [hc1, hc2, ← hcardB]
      rcases hi with h | h
      · rw [h, one_mul]
        exact Nat.mul_le_mul_right _ hi₂
      · rw [h, one_mul]
        exact Nat.mul_le_mul_right _ hi₁
    have : 2 * Nat.card B ≤ 2 * 2 ^ n := by omega
    calc Nat.card E ≤ 2 * 2 ^ n := hEle.trans this
      _ < (2 ^ n) ^ 2 := by nlinarith
  · push Not at hi
    obtain ⟨hi₁2, hi₂2⟩ := hi
    have hi₁e : E₁.relIndex E = 2 := by omega
    have hi₂e : E₀.relIndex E₁ = 2 := by omega
    have hEnle : ¬ E ≤ E₁ := fun h => hi₁2 (Subgroup.relIndex_eq_one.mpr h)
    have hE₁nle : ¬ E₁ ≤ E₀ := fun h => hi₂2 (Subgroup.relIndex_eq_one.mpr h)
    obtain ⟨θ₂, hθ₂E, hθ₂⟩ : ∃ θ₂ ∈ E, θ₂ ∉ Es := by
      by_contra hcon
      push Not at hcon
      exact hEnle fun x hx => ⟨hx, hcon x hx⟩
    obtain ⟨θ₁, hθ₁E₁, hθ₁⟩ : ∃ θ₁ ∈ E₁, θ₁ ∉ E₀ := by
      by_contra hcon
      push Not at hcon
      exact hE₁nle fun x hx => hcon x hx
    have hθ₁D : θ₁ ∉ D := by
      intro hD'
      have : θ₁ ∈ E ⊓ D := ⟨hθ₁E₁.1, hD'⟩
      rw [inf_linear_eq_inf_inner E h2] at this
      exact hθ₁ this
    have hsq : Nat.card B ^ 2 ≤ Nat.card F :=
      card_sq_le_of_pair hBV hθ₁E₁.2 hθ₁D hθ₂ (hBfix θ₁ hθ₁E₁.1) (hBfix θ₂ hθ₂E)
    have hE4 : Nat.card E = 4 * Nat.card B := by
      rw [hc1, hc2, hi₁e, hi₂e, hcardB]
      ring
    have hlt : Nat.card E ^ 2 < ((2 ^ n) ^ 2) ^ 2 := by
      calc Nat.card E ^ 2 = 16 * Nat.card B ^ 2 := by rw [hE4]; ring
        _ ≤ 16 * 2 ^ n := by rw [← hqq]; exact Nat.mul_le_mul_left _ hsq
        _ < ((2 ^ n) ^ 2) ^ 2 := by
          have hq3 : 16 < (2 ^ n) ^ 3 := by
            calc 16 < 4 ^ 3 := by norm_num
              _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h4 3
          calc 16 * 2 ^ n < (2 ^ n) ^ 3 * 2 ^ n :=
                Nat.mul_lt_mul_of_pos_right hq3 (by positivity)
            _ = ((2 ^ n) ^ 2) ^ 2 := by ring
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt

end Index

theorem maxRankModel_L3 [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    MaxRankModel (projectiveSL 3 F) (projUnitriangular 3 F) V1 V2 :=
  maxRankModel_of_outer (modelData_L3 hn hF) card_V1_eq_card_V2
    (fun _ hBU hB => elem_le_V1_or_V2 hBU fun x hx => hB x hx)
    (fun E h2 hc hU hout => card_lt_of_outer hn hF E h2 hc hU hout)

end L3

end CFSG.QuasithinUnique.Fin257
