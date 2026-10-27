module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellOffender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSeed

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization

theorem NI_arith {aV cV nV nK q2 κ cK bB fB : ℕ}
    (h1 : aV * cV = nV) (h2 : nV = nK * q2) (h3 : κ * cK = nK) (h4 : cV ≤ fB * cK)
    (h5 : aV ≤ bB) (h6 : bB * fB ≤ q2) (hq : 0 < q2) (hcK : 0 < cK) (hnK : 0 < nK)
    (hfB : 0 < fB) : κ = 1 ∧ aV = bB ∧ bB * fB = q2 := by
  have h7 : κ * cK * q2 ≤ aV * fB * cK := by
    calc κ * cK * q2 = aV * cV := by rw [h1, h2, ← h3]
      _ ≤ aV * (fB * cK) := Nat.mul_le_mul_left _ h4
      _ = aV * fB * cK := by ring
  have h8 : κ * q2 ≤ aV * fB := by
    refine Nat.le_of_mul_le_mul_right ?_ hcK
    calc κ * q2 * cK = κ * cK * q2 := by ring
      _ ≤ aV * fB * cK := h7
  have h9 : aV * fB ≤ bB * fB := Nat.mul_le_mul_right _ h5
  have hκ1 : κ ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have : 2 * q2 ≤ κ * q2 := Nat.mul_le_mul_right _ hlt
    omega
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    simp at h3
    omega
  have hκ : κ = 1 := by omega
  subst hκ
  have h10 : q2 ≤ aV * fB := by simpa using h8
  have h11 : bB * fB = q2 := by omega
  refine ⟨rfl, ?_, h11⟩
  have : aV * fB = bB * fB := by omega
  exact Nat.eq_of_mul_eq_mul_right hfB this

section Image

variable {k : Type*} [Field k] [Finite k] [CharP k 2] {R : Type*} [Group R] [Finite R]

theorem natural_quotient_per_elementary (V : Subgroup R) [V.Normal]
    (hV : IsElementaryAbelian 2 V) (ρ : R →* Gamma k) (φ : V →* Multiplicative (Fin 2 → k))
    (hφ : Function.Surjective φ)
    (hφρ : ∀ (r : R) (v v' : V), (v' : R) = r * v * r⁻¹ →
      Multiplicative.toAdd (φ v') =
        ((ρ r : Gamma k) : Equiv.Perm (Fin 2 → k)) (Multiplicative.toAdd (φ v)))
    (hker : ρ.ker = Subgroup.centralizer (V : Set R))
    {A : Subgroup R} (hA : A ∈ elemThompsonFamily R 2) :
    (A ⊓ Subgroup.centralizer (V : Set R)).relIndex A =
        (V ⊓ Subgroup.centralizer (A : Set R)).relIndex V ∧
      (∀ v : V, φ v = 1 → (v : R) ∈ Subgroup.centralizer (A : Set R)) ∧
      (¬ A ≤ Subgroup.centralizer (V : Set R) →
        ∃ ℓ : ℙ k (Fin 2 → k), A.map ρ = rootGamma ℓ ∧
          (∀ w : Fin 2 → k, w ∈ ℓ.submodule ↔ ∃ v : V, (v : R) ∈ Subgroup.centralizer (A : Set R) ∧
            Multiplicative.toAdd (φ v) = w) ∧
          (V ⊓ Subgroup.centralizer (A : Set R)).relIndex V = Nat.card k) := by
  classical
  set ρp : R →* Equiv.Perm (Fin 2 → k) := (Gamma k).subtype.comp ρ with hρp
  obtain ⟨hAel, hAmax⟩ := mem_elemThompsonFamily_iff.mp hA
  obtain ⟨hcommA, hsqA⟩ := isElementaryAbelian_iff.mp hAel
  have hρpker : ρp.ker = ρ.ker := by
    ext r
    simp only [MonoidHom.mem_ker, hρp, MonoidHom.comp_apply]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  set B : Subgroup (Equiv.Perm (Fin 2 → k)) := A.map ρp with hB
  have hBΓ : B ≤ Gamma k := by
    rintro _ ⟨a, -, rfl⟩
    exact (ρ a).2
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcommA a ha b hb]
  have hBsq : ∀ x ∈ B, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← pow_two, hsqA a ha, map_one]
  have hAB : Nat.card A = Nat.card B * Nat.card (A ⊓ Subgroup.centralizer (V : Set R) : Subgroup R) := by
    have := card_eq_card_map_mul_card_inf_ker ρp A
    rwa [hρpker, hker] at this
  have hApos : 0 < Nat.card (A ⊓ Subgroup.centralizer (V : Set R) : Subgroup R) := Nat.card_pos
  have hAidx : (A ⊓ Subgroup.centralizer (V : Set R)).relIndex A = Nat.card B := by
    have h := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set R)) A
    rw [inf_of_le_left inf_le_left] at h
    rw [hAB] at h
    have h' : (A ⊓ Subgroup.centralizer (V : Set R)).relIndex A *
        Nat.card (A ⊓ Subgroup.centralizer (V : Set R) : Subgroup R) =
        Nat.card B * Nat.card (A ⊓ Subgroup.centralizer (V : Set R) : Subgroup R) := h
    exact Nat.eq_of_mul_eq_mul_right hApos h'
  have hact := relIndex_inf_centralizer_le hV hAel hAmax
  have hBbot_iff : B = ⊥ ↔ A ≤ Subgroup.centralizer (V : Set R) := by
    constructor
    · intro hB1 a ha
      have h1 : ρp a ∈ B := ⟨a, ha, rfl⟩
      rw [hB1, Subgroup.mem_bot] at h1
      have h2 : a ∈ ρp.ker := h1
      rw [hρpker, hker] at h2
      exact h2
    · intro hAC
      rw [eq_bot_iff]
      rintro _ ⟨a, ha, rfl⟩
      have h2 : a ∈ ρ.ker := by rw [hker]; exact hAC ha
      have h3 : a ∈ ρp.ker := by rw [hρpker]; exact h2
      exact h3
  set C₁ : Subgroup R := V ⊓ Subgroup.centralizer (A : Set R) with hC₁
  set Dv : Subgroup V := C₁.subgroupOf V with hDv
  have hmemDv : ∀ v : V, v ∈ Dv ↔ (v : R) ∈ Subgroup.centralizer (A : Set R) := fun v => by
    rw [hDv, Subgroup.mem_subgroupOf, hC₁, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨v.2, h⟩⟩
  have hcDv : Nat.card Dv = Nat.card C₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have hnV : Nat.card V = Nat.card φ.ker * Nat.card k ^ 2 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd,
      card_fin_two_pi] at h
    exact h.symm
  have hidx : Nat.card C₁ * C₁.relIndex V = Nat.card V := by
    have h := Subgroup.relIndex_mul_card C₁ V
    rw [inf_of_le_left inf_le_left] at h
    rw [mul_comm]; exact h
  have hcnt := card_eq_card_map_mul_card_inf_ker φ Dv
  have hmapfix : ∀ m ∈ Dv.map φ, Multiplicative.toAdd m ∈ fixSet B := by
    rintro _ ⟨d, hd, rfl⟩ b ⟨a, ha, rfl⟩
    have hda : (d : R) ∈ Subgroup.centralizer (A : Set R) := (hmemDv d).mp hd
    have hcomm := Subgroup.mem_centralizer_iff.mp hda a ha
    have hc : (d : R) = a * d * a⁻¹ := by rw [hcomm]; group
    exact (hφρ a d d hc).symm
  have hinjIm : Function.Injective (fun m : Dv.map φ =>
      (⟨Multiplicative.toAdd (m : Multiplicative (Fin 2 → k)), hmapfix m m.2⟩ : fixSet B)) := by
    intro m m' h
    have h2 : Multiplicative.toAdd (m : Multiplicative (Fin 2 → k)) =
        Multiplicative.toAdd (m' : Multiplicative (Fin 2 → k)) := by
      simpa using congrArg Subtype.val h
    exact Subtype.ext (Multiplicative.toAdd.injective h2)
  have hIm : Nat.card (Dv.map φ) ≤ Nat.card (fixSet B) := Nat.card_le_card_of_injective _ hinjIm
  set Kd : Subgroup V := Dv ⊓ φ.ker with hKd
  have hκ : (Kd).relIndex φ.ker * Nat.card Kd = Nat.card φ.ker := by
    have h := Subgroup.relIndex_mul_card Kd φ.ker
    rwa [inf_of_le_left inf_le_right] at h
  have hKdpos : 0 < Nat.card Kd := Nat.card_pos
  have hkerpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hC₁pos : 0 < Nat.card C₁ := Nat.card_pos
  have hindexpos : 0 < C₁.relIndex V := by
    rcases Nat.eq_zero_or_pos (C₁.relIndex V) with h | h
    · rw [h, mul_zero] at hidx; omega
    · exact h
  have hcV : Nat.card C₁ ≤ Nat.card (fixSet B) * Nat.card Kd :=
    calc Nat.card C₁ = Nat.card Dv := hcDv.symm
      _ = Nat.card (Dv.map φ) * Nat.card Kd := hcnt
      _ ≤ Nat.card (fixSet B) * Nat.card Kd := Nat.mul_le_mul_right _ hIm
  by_cases hB1 : B = ⊥
  ·
    have hAC := hBbot_iff.mp hB1
    have hrel : (A ⊓ Subgroup.centralizer (V : Set R)).relIndex A = 1 :=
      Subgroup.relIndex_eq_one.mpr (le_inf le_rfl hAC)
    have hle1 : C₁.relIndex V ≤ 1 := hrel ▸ hact
    have hrel1 : C₁.relIndex V = 1 := by omega
    refine ⟨hrel.trans hrel1.symm, fun v _ => ?_, fun h => absurd hAC h⟩
    refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hAC ha) v v.2).symm ▸ rfl
  · obtain ⟨hdich1, hdich2⟩ := offender_dichotomy B hBΓ hBcomm hBsq hB1
    have hfBpos : 0 < Nat.card (fixSet B) := by
      rcases Nat.eq_zero_or_pos (Nat.card (fixSet B)) with h | h
      · exfalso
        have : Nonempty (fixSet B) := ⟨⟨0, fun b hb => Gamma_apply_zero (hBΓ hb)⟩⟩
        have := Nat.card_pos (α := fixSet B)
        omega
      · exact h
    obtain ⟨hκ1, haV, hbf⟩ := NI_arith (aV := C₁.relIndex V) (cV := Nat.card C₁)
      (nV := Nat.card V) (nK := Nat.card φ.ker) (q2 := Nat.card k ^ 2)
      (κ := Kd.relIndex φ.ker) (cK := Nat.card Kd) (bB := Nat.card B) (fB := Nat.card (fixSet B))
      ((mul_comm _ _).trans hidx) hnV hκ hcV (hAidx ▸ hact) hdich1
      (by have := Nat.card_pos (α := k); positivity) hKdpos hkerpos hfBpos
    have hkerle : φ.ker ≤ Dv := (Subgroup.relIndex_eq_one.mp hκ1).trans inf_le_left
    obtain ⟨ℓ, hℓ⟩ := hdich2 hbf
    have hBcard : Nat.card B = Nat.card k := by rw [hℓ]; exact card_rootPerm ℓ
    have hfBcard : Nat.card (fixSet B) = Nat.card k := by rw [hℓ]; exact card_fixSet_rootPerm ℓ
    refine ⟨hAidx.trans haV.symm, fun v hv => (hmemDv v).mp (hkerle hv), fun _ => ⟨ℓ, ?_, ?_, ?_⟩⟩
    · apply Subgroup.map_injective (Gamma k).subtype_injective
      rw [map_subtype_rootGamma, ← hℓ, Subgroup.map_map]
    · have hqpos : 0 < Nat.card k := Nat.card_pos
      have hnKeq : Nat.card φ.ker = Nat.card Kd := by
        rw [hκ1, one_mul] at hκ
        exact hκ.symm
      have hcVeq : Nat.card C₁ = Nat.card k * Nat.card Kd := by
        have h1 : Nat.card k * Nat.card C₁ = Nat.card k * (Nat.card k * Nat.card Kd * 1) := by
          calc Nat.card k * Nat.card C₁ = Nat.card B * Nat.card C₁ := by rw [hBcard]
            _ = C₁.relIndex V * Nat.card C₁ := by rw [← haV]
            _ = Nat.card V := (mul_comm _ _).trans hidx
            _ = Nat.card Kd * Nat.card k ^ 2 := by rw [hnV, hnKeq]
            _ = Nat.card k * (Nat.card k * Nat.card Kd * 1) := by ring
        have := Nat.eq_of_mul_eq_mul_left hqpos h1
        simpa using this
      have hImeq : Nat.card (Dv.map φ) = Nat.card (fixSet B) := by
        have h1 : Nat.card (Dv.map φ) * Nat.card Kd = Nat.card k * Nat.card Kd := by
          rw [← hcnt, hcDv, hcVeq]
        rw [Nat.eq_of_mul_eq_mul_right hKdpos h1, hfBcard]
      have hbij := hinjIm.bijective_of_nat_card_le (le_of_eq hImeq.symm)
      intro w
      constructor
      · intro hw
        have hw' : w ∈ fixSet B := by rw [hℓ, fixSet_rootPerm]; exact hw
        obtain ⟨⟨m, hm⟩, hmw⟩ := hbij.2 ⟨w, hw'⟩
        obtain ⟨d, hd, rfl⟩ := hm
        refine ⟨d, (hmemDv d).mp hd, ?_⟩
        exact congrArg Subtype.val hmw
      · rintro ⟨v, hv, rfl⟩
        have := hmapfix (φ v) ⟨v, (hmemDv v).mpr hv, rfl⟩
        rwa [hℓ, fixSet_rootPerm] at this
    · rw [haV, hBcard]

theorem natural_quotient_internal_Thompson_Baumann_image (hR : IsPGroup 2 R)
    (V : Subgroup R) [V.Normal] (hV : IsElementaryAbelian 2 V) (ρ : R →* Gamma k)
    (φ : V →* Multiplicative (Fin 2 → k)) (hφ : Function.Surjective φ)
    (hφρ : ∀ (r : R) (v v' : V), (v' : R) = r * v * r⁻¹ →
      Multiplicative.toAdd (φ v') =
        ((ρ r : Gamma k) : Equiv.Perm (Fin 2 → k)) (Multiplicative.toAdd (φ v)))
    (hker : ρ.ker = Subgroup.centralizer (V : Set R))
    (hJ : ⁅elemThompson R 2, V⁆ ≠ ⊥) :
    ∃ ℓ : ℙ k (Fin 2 → k),
      (elemThompson R 2).map ρ = rootGamma ℓ ∧ (elemBaumann R 2).map ρ = rootGamma ℓ ∧
      (∀ v : V, φ v = 1 → (v : R) ∈ Subgroup.centralizer (elemThompson R 2 : Set R)) ∧
      (∀ w : Fin 2 → k, w ∈ ℓ.submodule ↔ ∃ v : V,
        (v : R) ∈ Subgroup.centralizer (elemThompson R 2 : Set R) ∧
          Multiplicative.toAdd (φ v) = w) ∧
      (V ⊓ Subgroup.centralizer (elemThompson R 2 : Set R)).relIndex V = Nat.card k := by
  classical
  set ρp : R →* Equiv.Perm (Fin 2 → k) := (Gamma k).subtype.comp ρ with hρp
  have hJnot : ¬ elemThompson R 2 ≤ Subgroup.centralizer (V : Set R) := fun h =>
    hJ (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h)
  have hper := fun (A : Subgroup R) (hA : A ∈ elemThompsonFamily R 2) =>
    natural_quotient_per_elementary V hV ρ φ hφ hφρ hker hA
  obtain ⟨A₀, hA₀, hA₀C⟩ : ∃ A₀ ∈ elemThompsonFamily R 2,
      ¬ A₀ ≤ Subgroup.centralizer (V : Set R) := by
    by_contra hall
    push Not at hall
    exact hJnot (sSup_le hall)
  obtain ⟨ℓ, hℓA₀, hℓline, hℓidx⟩ := (hper A₀ hA₀).2.2 hA₀C
  have hPgroup : IsPGroup 2 ρp.range :=
    hR.of_surjective ρp.rangeRestrict ρp.rangeRestrict_surjective
  have hrootle : ∀ (A : Subgroup R) (ℓ' : ℙ k (Fin 2 → k)), A.map ρ = rootGamma ℓ' →
      rootPerm ℓ' ≤ ρp.range := by
    intro A ℓ' h
    rw [← map_subtype_rootGamma, ← h, Subgroup.map_map]
    exact Subgroup.map_le_range _ _
  have hA₀le : rootPerm ℓ ≤ ρp.range := hrootle A₀ ℓ hℓA₀
  have hmapA : ∀ A ∈ elemThompsonFamily R 2, A.map ρ ≤ rootGamma ℓ := by
    intro A hA
    by_cases hAC : A ≤ Subgroup.centralizer (V : Set R)
    · rintro _ ⟨a, ha, rfl⟩
      have : a ∈ ρ.ker := by rw [hker]; exact hAC ha
      rw [MonoidHom.mem_ker.mp this]
      exact Subgroup.one_mem _
    · obtain ⟨ℓ', hℓ', -, -⟩ := (hper A hA).2.2 hAC
      have := rootPerm_eq_of_le_two_group hPgroup (hrootle A ℓ' hℓ') hA₀le
      rw [hℓ', this]
  have hJmap : (elemThompson R 2).map ρ = rootGamma ℓ := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact sSup_le fun A hA => Subgroup.map_le_iff_le_comap.mp (hmapA A hA)
    · rw [← hℓA₀]
      exact Subgroup.map_mono (le_elemThompson hA₀)
  have hJcent : ∀ v : V, φ v = 1 → (v : R) ∈ Subgroup.centralizer (elemThompson R 2 : Set R) := by
    intro v hv
    have hle : elemThompson R 2 ≤ Subgroup.centralizer (({(v : R)} : Set R)) := by
      refine sSup_le fun A hA a ha => ?_
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.mp ((hper A hA).2.1 v hv) a ha).symm
    refine Subgroup.mem_centralizer_iff.mpr fun j hj => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hle hj) (v : R) (Set.mem_singleton _)).symm
  have hCV : ∀ v : V, (v : R) ∈ Subgroup.centralizer (elemThompson R 2 : Set R) ↔
      (v : R) ∈ Subgroup.centralizer (A₀ : Set R) := by
    intro v
    constructor
    · intro hv
      exact Subgroup.centralizer_le (le_elemThompson hA₀) hv
    · intro hv
      refine Subgroup.mem_centralizer_iff.mpr fun j hj => ?_
      have hρj : ρ j ∈ rootGamma ℓ := by
        rw [← hJmap]; exact ⟨j, hj, rfl⟩
      rw [← hℓA₀] at hρj
      obtain ⟨a, ha, hρa⟩ := hρj
      have hc : j * a⁻¹ ∈ Subgroup.centralizer (V : Set R) := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hρa, mul_inv_cancel]
      have h1 : (j * a⁻¹) * (v : R) = (v : R) * (j * a⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hc (v : R) v.2).symm
      have h2 : a * (v : R) = (v : R) * a := Subgroup.mem_centralizer_iff.mp hv a ha
      calc j * (v : R) = (j * a⁻¹) * (a * (v : R)) := by group
        _ = (j * a⁻¹) * ((v : R) * a) := by rw [h2]
        _ = ((j * a⁻¹) * (v : R)) * a := by group
        _ = ((v : R) * (j * a⁻¹)) * a := by rw [h1]
        _ = (v : R) * j := by group
  have hVC : V ⊓ Subgroup.centralizer (elemThompson R 2 : Set R) =
      V ⊓ Subgroup.centralizer (A₀ : Set R) := by
    ext x
    constructor
    · rintro ⟨hxV, hxJ⟩
      exact ⟨hxV, (hCV ⟨x, hxV⟩).mp hxJ⟩
    · rintro ⟨hxV, hxA⟩
      exact ⟨hxV, (hCV ⟨x, hxV⟩).mpr hxA⟩
  have hline : ∀ w : Fin 2 → k, w ∈ ℓ.submodule ↔ ∃ v : V,
      (v : R) ∈ Subgroup.centralizer (elemThompson R 2 : Set R) ∧
        Multiplicative.toAdd (φ v) = w := by
    intro w
    rw [hℓline w]
    constructor
    · rintro ⟨v, hv, hw⟩
      exact ⟨v, (hCV v).mpr hv, hw⟩
    · rintro ⟨v, hv, hw⟩
      exact ⟨v, (hCV v).mp hv, hw⟩
  have hJB : elemThompson R 2 ≤ elemBaumann R 2 := by
    intro j hj
    refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
    have := (mem_elemThompsonCenterTorsion_iff_centralizer.mp he).1
    exact (Subgroup.mem_centralizer_iff.mp this j hj).symm
  have hBmap : (elemBaumann R 2).map ρ ≤ rootGamma ℓ := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_rootGamma]
    refine mem_rootPerm_of_fixes_line (ρ b).2 ℓ fun w hw => ?_
    obtain ⟨v, hv, rfl⟩ := (hline w).mp hw
    have hvE : (v : R) ∈ elemThompsonCenterTorsion R 2 :=
      mem_elemThompsonCenterTorsion_iff_centralizer.mpr
        ⟨hv, (isElementaryAbelian_iff.mp hV).2 (v : R) v.2⟩
    have hbv : (v : R) * b = b * (v : R) := Subgroup.mem_centralizer_iff.mp hb (v : R) hvE
    have hc : (v : R) = b * (v : R) * b⁻¹ := by rw [← hbv]; group
    exact (hφρ b v v hc).symm
  refine ⟨ℓ, hJmap, le_antisymm hBmap (hJmap ▸ Subgroup.map_mono hJB), hJcent, hline, ?_⟩
  rw [hVC]
  exact hℓidx

end Image

end CFSG.QuasithinUnique.Setup.Campbell
