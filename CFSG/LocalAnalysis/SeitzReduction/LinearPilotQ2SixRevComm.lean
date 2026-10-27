module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2FiveSixKinds

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open scoped commutatorElement

section Formulas

variable {n : ℕ} {K : Type*} [Field K]

theorem transvection_conj_left {i j p : Fin n} (hij : i ≠ j) (hpi : p ≠ i) (hpj : p ≠ j)
    (c d : K) :
    SpecialLinearGroup.transvection hij c * SpecialLinearGroup.transvection hpi d *
        (SpecialLinearGroup.transvection hij c)⁻¹ =
      SpecialLinearGroup.transvection hpi d * (SpecialLinearGroup.transvection hpj (d * c))⁻¹ := by
  have h := SpecialLinearGroup.transvection_mul_transvection_eq_mul_mul hpi hij hpj d c
  have hAC := SpecialLinearGroup.commute_transvection hij hpj (Ne.symm hpj) (Ne.symm hij) c (d * c)
  have h' : SpecialLinearGroup.transvection hij c * SpecialLinearGroup.transvection hpi d =
      SpecialLinearGroup.transvection hpi d * SpecialLinearGroup.transvection hij c *
        (SpecialLinearGroup.transvection hpj (d * c))⁻¹ :=
    eq_mul_inv_of_mul_eq h.symm
  rw [h', mul_assoc, mul_assoc, ← mul_assoc _ _ (SpecialLinearGroup.transvection hij c)⁻¹,
    hAC.inv_right.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem transvection_conj_right {i j q : Fin n} (hij : i ≠ j) (hjq : j ≠ q) (hiq : i ≠ q)
    (c d : K) :
    SpecialLinearGroup.transvection hij c * SpecialLinearGroup.transvection hjq d *
        (SpecialLinearGroup.transvection hij c)⁻¹ =
      SpecialLinearGroup.transvection hjq d * SpecialLinearGroup.transvection hiq (c * d) := by
  have h := SpecialLinearGroup.transvection_mul_transvection_eq_mul_mul hij hjq hiq c d
  have hAC := SpecialLinearGroup.commute_transvection hij hiq (Ne.symm hij) (Ne.symm hiq) c
    (c * d)
  rw [h, mul_assoc, mul_assoc, ← mul_assoc (SpecialLinearGroup.transvection hij c), hAC.eq,
    mul_assoc, mul_inv_cancel, mul_one]

end Formulas

section Group

variable {H : Type*} [Group H]

theorem commute_mul_mul_inv_mul_inv {u y g : H} (h1 : Commute u g)
    (h2 : Commute u (y⁻¹ * g * y)) : Commute (u * y * u⁻¹ * y⁻¹) g := by
  have e2 : u⁻¹ * (y⁻¹ * g * y) * u = y⁻¹ * g * y := by
    rw [mul_assoc, ← h2.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  show u * y * u⁻¹ * y⁻¹ * g = g * (u * y * u⁻¹ * y⁻¹)
  calc u * y * u⁻¹ * y⁻¹ * g
      = u * y * (u⁻¹ * (y⁻¹ * g * y) * u) * y⁻¹ * u⁻¹ * (u * y * u⁻¹ * y⁻¹) := by group
    _ = u * y * (y⁻¹ * g * y) * y⁻¹ * u⁻¹ * (u * y * u⁻¹ * y⁻¹) := by rw [e2]
    _ = u * g * u⁻¹ * (u * y * u⁻¹ * y⁻¹) := by group
    _ = g * u * u⁻¹ * (u * y * u⁻¹ * y⁻¹) := by rw [h1.eq]
    _ = g * (u * y * u⁻¹ * y⁻¹) := by group

theorem mem_centralizer_of_conj_eq_mul {S : Set H} {Z : Subgroup H}
    (hperf : ⁅closure S, closure S⁆ = closure S) (hSZ : ∀ y ∈ S, ∀ z ∈ Z, Commute y z)
    (hZ : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, Commute z₁ z₂) {u : H}
    (hu : ∀ y ∈ S, ∃ z ∈ Z, u * y * u⁻¹ = y * z) :
    u ∈ centralizer (closure S : Set H) := by
  have hMZ : ∀ y ∈ closure S, ∀ z ∈ Z, Commute y z := by
    intro y hy z hz
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact hSZ y hy z hz
    | one => exact Commute.one_left z
    | mul y₁ y₂ _ _ h₁ h₂ => exact h₁.mul_left h₂
    | inv y _ h => exact h.inv_left
  have hcl : ∀ y ∈ closure S, ∃ z ∈ Z, u * y * u⁻¹ = y * z := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact hu y hy
    | one => exact ⟨1, Z.one_mem, by group⟩
    | mul y₁ y₂ hy₁ hy₂ h₁ h₂ =>
      obtain ⟨z₁, hz₁, e₁⟩ := h₁
      obtain ⟨z₂, hz₂, e₂⟩ := h₂
      refine ⟨z₁ * z₂, Z.mul_mem hz₁ hz₂, ?_⟩
      calc u * (y₁ * y₂) * u⁻¹ = (u * y₁ * u⁻¹) * (u * y₂ * u⁻¹) := by group
        _ = y₁ * (z₁ * y₂) * z₂ := by rw [e₁, e₂]; group
        _ = y₁ * (y₂ * z₁) * z₂ := by rw [(hMZ y₂ hy₂ z₁ hz₁).eq]
        _ = y₁ * y₂ * (z₁ * z₂) := by group
    | inv y hy h =>
      obtain ⟨z, hz, e⟩ := h
      refine ⟨z⁻¹, Z.inv_mem hz, ?_⟩
      calc u * y⁻¹ * u⁻¹ = (u * y * u⁻¹)⁻¹ := by group
        _ = z⁻¹ * y⁻¹ := by rw [e]; group
        _ = y⁻¹ * z⁻¹ := ((hMZ y hy z hz).inv_inv).eq.symm
  have hle : ⁅closure S, closure S⁆ ≤ centralizer ({u} : Set H) := by
    rw [Subgroup.commutator_le]
    intro y₁ hy₁ y₂ hy₂
    obtain ⟨z₁, hz₁, e₁⟩ := hcl y₁ hy₁
    obtain ⟨z₂, hz₂, e₂⟩ := hcl y₂ hy₂
    have hconj : u * ⁅y₁, y₂⁆ * u⁻¹ = ⁅y₁, y₂⁆ := by
      calc u * ⁅y₁, y₂⁆ * u⁻¹ = ⁅u * y₁ * u⁻¹, u * y₂ * u⁻¹⁆ := by
            rw [commutatorElement_def, commutatorElement_def]; group
        _ = ⁅y₁, y₂⁆ := by
            rw [e₁, e₂]
            exact commutatorElement_mul_right_mul_right_of_commute (hMZ y₂ hy₂ z₁ hz₁).symm
              (hMZ y₁ hy₁ z₂ hz₂).symm (hZ z₁ hz₁ z₂ hz₂)
    rw [mem_centralizer_singleton_iff]
    rw [mul_inv_eq_iff_eq_mul] at hconj
    exact hconj.symm
  rw [← hperf, mem_centralizer_iff]
  intro h hh
  exact mem_centralizer_singleton_iff.1 (hle hh)

end Group

section Radical

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  {F : Type*} [Field F] [Finite F]

theorem commute_gens_six [CharP K 2] (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    {ι : K →+* F} {σ : F ≃+* F} (hn : n = 6) (hF : 4 ≤ Nat.card F)
    {Xr : Fin n → Fin n → Subgroup (LinearFlag.projectiveSL n K)}
    (hXr : ∀ a b, Xr a b ≤ rootSL2 a b)
    (hXy : ∀ (a b : Fin n) (hab : a ≠ b), order3Elt K hab ∈ Xr a b)
    (P : ∀ a b : Fin n, a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin n)))
    {a b p q : Fin n} (hab : a ≠ b) (hpq : p ≠ q) (hp : p ∈ ({a, b}ᶜ : Finset (Fin n)))
    (hq : q ∈ ({a, b}ᶜ : Finset (Fin n))) (s : F) :
    (∀ (m : Fin n) (hm : p ≠ m) (r : K),
      Commute ((P a b hab).Φ ⟨SpecialLinearGroup.transvection hpq s,
          transvection_mem_blockSpecialLinear hpq hp hq s⟩)
        ((e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hm r)) : L) : G)) ∧
    ∀ (m : Fin n) (hm : m ≠ q) (r : K),
      Commute ((P a b hab).Φ ⟨SpecialLinearGroup.transvection hpq s,
          transvection_mem_blockSpecialLinear hpq hp hq s⟩)
        ((e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hm r)) : L) : G) := by
  classical
  obtain ⟨u, hu⟩ : ∃ u, u = (P a b hab).Φ ⟨SpecialLinearGroup.transvection hpq s,
      transvection_mem_blockSpecialLinear hpq hp hq s⟩ := ⟨_, rfl⟩
  rw [← hu]
  have hF2 : (2 : F) = 0 := by rw [← map_ofNat ι 2, CharTwo.two_eq_zero, map_zero]
  have hA : ∀ (i j : Fin n) (hij : i ≠ j) (hi : i ∈ ({a, b}ᶜ : Finset (Fin n)))
      (hj : j ∈ ({a, b}ᶜ : Finset (Fin n))) (r : K),
      SpecialLinearGroup.transvection hpq s * SpecialLinearGroup.transvection hij (ι r) =
        SpecialLinearGroup.transvection hij (ι r) * SpecialLinearGroup.transvection hpq s →
      Commute u
        ((e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hij r)) : L) : G) := by
    intro i j hij hi hj r hc
    rw [hu]
    refine commute_map_of_commute (P a b hab) (transvection_mem_blockSpecialLinear hij hi hj r) ?_
    rw [SpecialLinearGroup.map_transvection]
    exact hc
  have hpab : p ∉ ({a, b} : Finset (Fin n)) := Finset.mem_compl.1 hp
  have hqab : q ∉ ({a, b} : Finset (Fin n)) := Finset.mem_compl.1 hq
  have hdis : Disjoint ({a, b} : Finset (Fin n)) {p, q} := by
    rw [Finset.disjoint_right]
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hpab
    · rw [Finset.mem_singleton.1 hx]
      exact hqab
  have hcard : (({a, b} ∪ {p, q} : Finset (Fin n))ᶜ).card = 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_union_of_disjoint hdis,
      Finset.card_pair hab, Finset.card_pair hpq]
    omega
  obtain ⟨c, d, hcd, hcdS⟩ := Finset.card_eq_two.1 hcard
  have hmemcd : ∀ x, x ∈ ({c, d} : Finset (Fin n)) ↔
      x ∉ ({a, b} : Finset (Fin n)) ∧ x ∉ ({p, q} : Finset (Fin n)) := by
    intro x
    rw [← hcdS, Finset.mem_compl, Finset.mem_union, not_or]
  have h1 : Disjoint ({a, b} : Finset (Fin n)) {c, d} :=
    Finset.disjoint_left.2 fun x hx hx' => ((hmemcd x).1 hx').1 hx
  have hM : ({a, b}ᶜ : Finset (Fin n)) \ {c, d} = {p, q} := by
    ext x
    rw [Finset.mem_sdiff, Finset.mem_compl, hmemcd]
    constructor
    · rintro ⟨hx1, hx2⟩
      by_contra hx3
      exact hx2 ⟨hx1, hx3⟩
    · intro hx
      exact ⟨fun h => Finset.disjoint_left.1 hdis h hx, fun h => h.2 hx⟩
  have hM' : ({c, d}ᶜ : Finset (Fin n)) \ {a, b} = {p, q} := by
    rw [← compl_pair_sdiff_comm, hM]
  have hperf : ⁅blockSpecialLinear (K := F) (({a, b}ᶜ : Finset (Fin n)) \ {c, d}),
      blockSpecialLinear (K := F) (({a, b}ᶜ : Finset (Fin n)) \ {c, d})⁆ =
        blockSpecialLinear (K := F) (({a, b}ᶜ : Finset (Fin n)) \ {c, d}) := by
    rw [hM]
    exact commutator_blockSpecialLinear_eq_of_card_two (Finset.card_pair hpq) hF
  have hle := map_le_map_of_disjoint_roots_of_perfect e hXr hXy P hab hcd h1 hperf
  rw [hM, hM'] at hle
  have humem : u ∈ ((blockSpecialLinear (K := F) ({p, q} : Finset (Fin n))).subgroupOf
      (blockSpecialLinear ({a, b}ᶜ : Finset (Fin n)))).map (P a b hab).Φ := by
    rw [hu]
    exact mem_map_of_mem _ (mem_subgroupOf.2
      (transvection_mem_blockSpecialLinear hpq (by simp) (by simp) s))
  obtain ⟨Y, hYpq, hYu⟩ := hle humem
  replace hYpq : (Y : SpecialLinearGroup (Fin n) F) ∈
      blockSpecialLinear (K := F) ({p, q} : Finset (Fin n)) := mem_subgroupOf.1 hYpq
  have hpqcd : ({p, q} : Finset (Fin n)) ⊆ ({c, d}ᶜ : Finset (Fin n)) := by
    intro x hx
    rw [Finset.mem_compl, hmemcd, not_and_or, not_not, not_not]
    exact Or.inr hx
  have hacd : a ∈ ({c, d}ᶜ : Finset (Fin n)) := Finset.mem_compl.2 fun h =>
    ((hmemcd a).1 h).1 (by simp)
  have hbcd : b ∈ ({c, d}ᶜ : Finset (Fin n)) := Finset.mem_compl.2 fun h =>
    ((hmemcd b).1 h).1 (by simp)
  have hapq : a ∉ ({p, q} : Finset (Fin n)) := fun h => Finset.disjoint_left.1 hdis (by simp) h
  have hcdc : 2 ≤ (({c, d}ᶜ : Finset (Fin n))).card := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hcd]
    omega
  have hinj := (P c d hcd).injective_comp_inclusion hpqcd hacd hapq hcdc
  set Y₀ : blockSpecialLinear (K := F) ({p, q} : Finset (Fin n)) := ⟨Y, hYpq⟩ with hY₀
  have hY₀Y : Subgroup.inclusion (blockSpecialLinear_mono (K := F) hpqcd) Y₀ = Y := rfl
  have hu1 : Commute u ((e.symm (LinearFlag.proj n K
      (SpecialLinearGroup.transvection hpq (1 : K))) : L) : G) := by
    refine hA p q hpq hp hq 1 ?_
    rw [map_one]
    exact (SpecialLinearGroup.commute_transvection hpq hpq (Ne.symm hpq) (Ne.symm hpq) s 1).eq
  have hT₀mem : SpecialLinearGroup.transvection hpq (1 : F) ∈
      blockSpecialLinear (K := F) ({p, q} : Finset (Fin n)) :=
    transvection_mem_blockSpecialLinear hpq (by simp) (by simp) 1
  set T₀ : blockSpecialLinear (K := F) ({p, q} : Finset (Fin n)) := ⟨_, hT₀mem⟩ with hT₀
  have hT₀N1 : (P c d hcd).Φ (Subgroup.inclusion (blockSpecialLinear_mono (K := F) hpqcd) T₀) =
      ((e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hpq (1 : K))) : L) : G) := by
    rw [← (P c d hcd).N1 ⟨SpecialLinearGroup.transvection hpq (1 : K),
      transvection_mem_blockSpecialLinear hpq (hpqcd (by simp)) (hpqcd (by simp)) 1⟩]
    have hmapT : SpecialLinearGroup.map ι (SpecialLinearGroup.transvection hpq (1 : K)) =
        SpecialLinearGroup.transvection hpq (1 : F) := by
      rw [SpecialLinearGroup.map_transvection, map_one]
    congr 1
    exact Subtype.ext hmapT.symm
  have hYT : (Y : SpecialLinearGroup (Fin n) F) * SpecialLinearGroup.transvection hpq (1 : F) =
      SpecialLinearGroup.transvection hpq (1 : F) * (Y : SpecialLinearGroup (Fin n) F) := by
    have h : Y₀ * T₀ = T₀ * Y₀ := by
      apply hinj
      simp only [MonoidHom.comp_apply, map_mul]
      rw [hY₀Y, hT₀N1, hYu]
      exact hu1.eq
    exact congrArg Subtype.val h
  have hss : s + s = 0 := by rw [← two_mul, hF2, zero_mul]
  have huu : u * u = 1 := by
    rw [hu, ← map_mul]
    have h : (⟨SpecialLinearGroup.transvection hpq s,
        transvection_mem_blockSpecialLinear hpq hp hq s⟩ *
        ⟨SpecialLinearGroup.transvection hpq s, transvection_mem_blockSpecialLinear hpq hp hq s⟩ :
          blockSpecialLinear (K := F) ({a, b}ᶜ : Finset (Fin n))) = 1 := by
      apply Subtype.ext
      change SpecialLinearGroup.transvection hpq s * SpecialLinearGroup.transvection hpq s = 1
      rw [← SpecialLinearGroup.transvection_add, hss, SpecialLinearGroup.transvection_coeff_zero]
    rw [h, map_one]
  have hYY : (Y : SpecialLinearGroup (Fin n) F) * Y = 1 := by
    have h : Y₀ * Y₀ = 1 := by
      apply hinj
      simp only [MonoidHom.comp_apply, map_mul, map_one]
      rw [hY₀Y, hYu]
      exact huu
    exact congrArg Subtype.val h
  have hab' : ∀ m, m ∉ ({a, b}ᶜ : Finset (Fin n)) →
      m ≠ p ∧ m ≠ q ∧ m ∈ ({c, d}ᶜ : Finset (Fin n)) := by
    intro m hm
    have hm' : m ∈ ({a, b} : Finset (Fin n)) := by
      rw [Finset.mem_compl, not_not] at hm
      exact hm
    refine ⟨fun h => hpab (h ▸ hm'), fun h => hqab (h ▸ hm'), ?_⟩
    rcases Finset.mem_insert.1 hm' with rfl | h
    · exact hacd
    · rw [Finset.mem_singleton.1 h]
      exact hbcd
  have hB : ∀ (i j : Fin n) (hij : i ≠ j) (hi : i ∈ ({c, d}ᶜ : Finset (Fin n)))
      (hj : j ∈ ({c, d}ᶜ : Finset (Fin n))) (r : K),
      (Y : SpecialLinearGroup (Fin n) F) * SpecialLinearGroup.transvection hij (ι r) =
        SpecialLinearGroup.transvection hij (ι r) * (Y : SpecialLinearGroup (Fin n) F) →
      Commute u
        ((e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hij r)) : L) : G) := by
    intro i j hij hi hj r hc
    rw [← hYu]
    refine commute_map_of_commute (P c d hcd) (transvection_mem_blockSpecialLinear hij hi hj r) ?_
    rw [SpecialLinearGroup.map_transvection]
    exact hc
  refine ⟨fun m hm r => ?_, fun m hm r => ?_⟩
  · by_cases hmN : m ∈ ({a, b}ᶜ : Finset (Fin n))
    · exact hA p m hm hp hmN r
        (SpecialLinearGroup.commute_transvection hpq hm (Ne.symm hpq) (Ne.symm hm) s (ι r)).eq
    · obtain ⟨hmp, hmq, hmcd⟩ := hab' m hmN
      exact hB p m hm (hpqcd (by simp)) hmcd r
        (commute_transvection_of_block_sq hF2 hpq hYpq hYT hYY hmp hmq (ι r)).1
  · by_cases hmN : m ∈ ({a, b}ᶜ : Finset (Fin n))
    · exact hA m q hm hmN hq r
        (SpecialLinearGroup.commute_transvection hpq hm (Ne.symm hm) (Ne.symm hpq) s (ι r)).eq
    · obtain ⟨hmp, hmq, hmcd⟩ := hab' m hmN
      exact hB m q hm hmcd (hpqcd (by simp)) r
        (commute_transvection_of_block_sq hF2 hpq hYpq hYT hYY hmp hmq (ι r)).2

omit [Finite F] in
theorem conj_mem_six (hL : CFSG.Open.standardComponentIsStandard L) [CharP K 2]
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {ι : K →+* F} {σ : F ≃+* F} (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (hn : n = 6)
    {Xr : Fin n → Fin n → Subgroup (LinearFlag.projectiveSL n K)}
    (P : ∀ a b : Fin n, a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin n)))
    {a b p q : Fin n} (hab : a ≠ b) (hpq : p ≠ q) (hp : p ∈ ({a, b}ᶜ : Finset (Fin n)))
    (hq : q ∈ ({a, b}ᶜ : Finset (Fin n))) (s : F) {i j : Fin n} (hij : i ≠ j)
    (hi : i ∉ ({p, q} : Finset (Fin n))) (hj : j ∉ ({p, q} : Finset (Fin n))) (r : K) :
    (P a b hab).Φ ⟨SpecialLinearGroup.transvection hpq s,
        transvection_mem_blockSpecialLinear hpq hp hq s⟩ *
      ((e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hij r)) : L) : G) *
      ((P a b hab).Φ ⟨SpecialLinearGroup.transvection hpq s,
        transvection_mem_blockSpecialLinear hpq hp hq s⟩)⁻¹ ∈ L := by
  have hF2 : (2 : F) = 0 := by rw [← map_ofNat ι 2, CharTwo.two_eq_zero, map_zero]
  have hss : s + s = 0 := by rw [← two_mul, hF2, zero_mul]
  have hσs : σ (σ s) = s := DFunLike.congr_fun hσσ s
  obtain ⟨k, hk⟩ := (hfix (σ s + s)).1 (by rw [map_add, hσs, add_comm])
  have hk' : σ s = s + ι k := by
    rw [hk, ← add_assoc, add_comm s (σ s), add_assoc, hss, add_zero]
  obtain ⟨g₁, g₂, hg, hgdis⟩ := exists_root_disjoint (n := n)
    (S := ({p, q} ∪ {i, j} : Finset (Fin n))) (by
      have h1 := Finset.card_union_le ({p, q} : Finset (Fin n)) {i, j}
      have h2 := Finset.card_le_two (a := p) (b := q)
      have h3 := Finset.card_le_two (a := i) (b := j)
      omega)
  have hmemg : ∀ x ∈ ({p, q} ∪ {i, j} : Finset (Fin n)), x ∈ ({g₁, g₂}ᶜ : Finset (Fin n)) :=
    fun x hx => Finset.mem_compl.2 fun h => Finset.disjoint_left.1 hgdis hx h
  have hpg := hmemg p (by simp)
  have hqg := hmemg q (by simp)
  have hig := hmemg i (by simp)
  have hjg := hmemg j (by simp)
  set u := (P a b hab).Φ ⟨SpecialLinearGroup.transvection hpq s,
    transvection_mem_blockSpecialLinear hpq hp hq s⟩ with hu
  set u' := (P g₁ g₂ hg).Φ ⟨SpecialLinearGroup.transvection hpq s,
    transvection_mem_blockSpecialLinear hpq hpg hqg s⟩ with hu'
  set z := ((e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hpq k)) : L) : G)
    with hz
  have htu : t * u * t⁻¹ = u * z := conj_fieldParam_transvection (P a b hab) hpq hp hq hk'
  have htu' : t * u' * t⁻¹ = u' * z := conj_fieldParam_transvection (P g₁ g₂ hg) hpq hpg hqg hk'
  have hth : t * (u * u'⁻¹) * t⁻¹ = u * u'⁻¹ := by
    calc t * (u * u'⁻¹) * t⁻¹ = (t * u * t⁻¹) * (t * u' * t⁻¹)⁻¹ := by group
      _ = u * u'⁻¹ := by rw [htu, htu']; group
  have hhC : u * u'⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    rw [mul_inv_eq_iff_eq_mul] at hth
    exact hth.symm
  have hhN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht hhC
  have hu'y := commute_map_of_commute (P g₁ g₂ hg) (x := ⟨SpecialLinearGroup.transvection hpq s,
      transvection_mem_blockSpecialLinear hpq hpg hqg s⟩)
    (transvection_mem_blockSpecialLinear hij hig hjg r) (by
      rw [SpecialLinearGroup.map_transvection]
      exact (SpecialLinearGroup.commute_transvection hpq hij
        (fun h => hi (by simp [h])) (fun h => hj (by simp [h])) s (ι r)).eq)
  set y := ((e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hij r)) : L) : G)
    with hy
  have hyL : y ∈ L := (e.symm _).2
  have hconj : u * y * u⁻¹ = (u * u'⁻¹) * y * (u * u'⁻¹)⁻¹ := by
    calc u * y * u⁻¹ = (u * u'⁻¹) * (u' * y) * u'⁻¹ * (u * u'⁻¹)⁻¹ := by group
      _ = (u * u'⁻¹) * (y * u') * u'⁻¹ * (u * u'⁻¹)⁻¹ := by rw [hu'y]
      _ = (u * u'⁻¹) * y * (u * u'⁻¹)⁻¹ := by group
  rw [hconj]
  exact (mem_normalizer_iff.mp hhN y).mp hyL

end Radical

section Main

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  {F : Type*} [Field F] [Finite F]

theorem map_transvection_mem_centralizer_six (hL : CFSG.Open.standardComponentIsStandard L)
    [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {ι : K →+* F} {σ : F ≃+* F}
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (hn : n = 6)
    (hF : 4 ≤ Nat.card F) {Xr : Fin n → Fin n → Subgroup (LinearFlag.projectiveSL n K)}
    (hXr : ∀ a b, Xr a b ≤ rootSL2 a b)
    (hXy : ∀ (a b : Fin n) (hab : a ≠ b), order3Elt K hab ∈ Xr a b)
    (P : ∀ a b : Fin n, a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin n)))
    {a b p q : Fin n} (hab : a ≠ b) (hpq : p ≠ q) (hp : p ∈ ({a, b}ᶜ : Finset (Fin n)))
    (hq : q ∈ ({a, b}ᶜ : Finset (Fin n))) (s : F) :
    (P a b hab).Φ ⟨SpecialLinearGroup.transvection hpq s,
        transvection_mem_blockSpecialLinear hpq hp hq s⟩ ∈
      centralizer (modelToG e (blockSL (K := K) ({p, q} : Finset (Fin n))ᶜ) : Set G) := by
  classical
  set φ : SpecialLinearGroup (Fin n) K →* G :=
    L.subtype.comp (e.symm.toMonoidHom.comp (LinearFlag.proj n K)) with hφ
  have hφapp : ∀ x, φ x = ((e.symm (LinearFlag.proj n K x) : L) : G) := fun x => rfl
  have hφinj : Function.Injective φ :=
    L.subtype_injective.comp (e.symm.injective.comp (proj_injective_of_card_two hK))
  obtain ⟨hgen1, hgen2⟩ := commute_gens_six e hn hF hXr hXy P hab hpq hp hq s
  set u := (P a b hab).Φ ⟨SpecialLinearGroup.transvection hpq s,
    transvection_mem_blockSpecialLinear hpq hp hq s⟩ with hu
  set Qg : Set (SpecialLinearGroup (Fin n) K) :=
    {x | (∃ (m : Fin n) (hm : p ≠ m) (r : K), SpecialLinearGroup.transvection hm r = x) ∨
      ∃ (m : Fin n) (hm : m ≠ q) (r : K), SpecialLinearGroup.transvection hm r = x} with hQg
  have hQ : ∀ x ∈ closure Qg, Commute u (φ x) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨m, hm, r, rfl⟩ | ⟨m, hm, r, rfl⟩
      · exact hgen1 m hm r
      · exact hgen2 m hm r
    | one => rw [map_one]; exact Commute.one_right u
    | mul x₁ x₂ _ _ h₁ h₂ => rw [map_mul]; exact h₁.mul_right h₂
    | inv x _ h => rw [map_inv]; exact h.inv_right
  have hQ1 : ∀ (m : Fin n) (hm : p ≠ m) (r : K),
      SpecialLinearGroup.transvection hm r ∈ closure Qg :=
    fun m hm r => subset_closure (Or.inl ⟨m, hm, r, rfl⟩)
  have hQ2 : ∀ (m : Fin n) (hm : m ≠ q) (r : K),
      SpecialLinearGroup.transvection hm r ∈ closure Qg :=
    fun m hm r => subset_closure (Or.inr ⟨m, hm, r, rfl⟩)
  set Z : Subgroup G := (φ.comp (SpecialLinearGroup.transvectionHom (A := K) hpq)).range with hZ
  set S : Set G := φ '' {x | ∃ (i j : Fin n) (hij : i ≠ j) (c : K),
      i ∈ ({p, q} : Finset (Fin n))ᶜ ∧ j ∈ ({p, q} : Finset (Fin n))ᶜ ∧
        SpecialLinearGroup.transvection hij c = x} with hS
  have hJ : modelToG e (blockSL (K := K) ({p, q} : Finset (Fin n))ᶜ) = closure S := by
    rw [hS, ← MonoidHom.map_closure, ← blockSpecialLinear_eq_closure, modelToG, blockSL,
      Subgroup.map_map, Subgroup.map_map]
    rfl
  have hyZ : ∀ (i j : Fin n) (hij : i ≠ j) (c : K), i ∉ ({p, q} : Finset (Fin n)) →
      j ∉ ({p, q} : Finset (Fin n)) → ∀ z ∈ Z,
      Commute (φ (SpecialLinearGroup.transvection hij c)) z := by
    rintro i j hij c hi hj _ ⟨μ, rfl⟩
    show Commute (φ (SpecialLinearGroup.transvection hij c))
      (φ (SpecialLinearGroup.transvectionHom hpq μ))
    rw [SpecialLinearGroup.transvectionHom_apply]
    exact (SpecialLinearGroup.commute_transvection hij hpq (fun h => hj (by simp [h]))
      (fun h => hi (by simp [h])) c _).map φ
  have hZZ : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, Commute z₁ z₂ := by
    rintro _ ⟨μ₁, rfl⟩ _ ⟨μ₂, rfl⟩
    exact (Commute.all μ₁ μ₂).map _
  have hSZ : ∀ y ∈ S, ∀ z ∈ Z, Commute y z := by
    rintro _ ⟨_, ⟨i, j, hij, c, hi, hj, rfl⟩, rfl⟩ z hz
    exact hyZ i j hij c (Finset.mem_compl.1 hi) (Finset.mem_compl.1 hj) z hz
  have hcard : 3 ≤ (({p, q} : Finset (Fin n))ᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hpq]
    omega
  have hperf : ⁅closure S, closure S⁆ = closure S := by
    rw [← hJ]
    exact modelToG_perfect e (commutator_blockSL_eq_of_three_le hcard)
  have hconj : ∀ y ∈ S, ∃ z ∈ Z, u * y * u⁻¹ = y * z := by
    rintro _ ⟨_, ⟨i, j, hij, c, hi, hj, rfl⟩, rfl⟩
    have hi' := Finset.mem_compl.1 hi
    have hj' := Finset.mem_compl.1 hj
    have hpi : p ≠ i := fun h => hi' (by simp [h])
    have hpj : p ≠ j := fun h => hj' (by simp [h])
    have hqi : q ≠ i := fun h => hi' (by simp [h])
    have hqj : q ≠ j := fun h => hj' (by simp [h])
    set y := φ (SpecialLinearGroup.transvection hij c) with hy
    have hyL : y ∈ L := (e.symm _).2
    have huyL : u * y * u⁻¹ ∈ L := conj_mem_six hL e htC ht hσσ hfix hn P hab hpq hp hq s hij hi'
      hj' c
    have hwL : u * y * u⁻¹ * y⁻¹ ∈ L := L.mul_mem huyL (L.inv_mem hyL)
    have hyinv : y⁻¹ = φ (SpecialLinearGroup.transvection hij (-c)) := by
      rw [hy, ← map_inv, SpecialLinearGroup.transvection_inv]
    have hyy : y = φ (SpecialLinearGroup.transvection hij (-c))⁻¹ := by
      rw [hy, SpecialLinearGroup.transvection_inv, neg_neg]
    have hgen : ∀ g ∈ closure Qg, SpecialLinearGroup.transvection hij (-c) * g *
        (SpecialLinearGroup.transvection hij (-c))⁻¹ ∈ closure Qg →
        Commute (u * y * u⁻¹ * y⁻¹) (φ g) := by
      intro g hg hcg
      refine commute_mul_mul_inv_mul_inv (hQ g hg) ?_
      have : y⁻¹ * φ g * y = φ (SpecialLinearGroup.transvection hij (-c) * g *
          (SpecialLinearGroup.transvection hij (-c))⁻¹) := by
        conv_lhs => rw [hyinv, hyy]
        rw [map_mul, map_mul]
      rw [this]
      exact hQ _ hcg
    have hw1 : ∀ (m : Fin n) (hm : p ≠ m), Commute (u * y * u⁻¹ * y⁻¹)
        (φ (SpecialLinearGroup.transvection hm 1)) := by
      intro m hm
      refine hgen _ (hQ1 m hm 1) ?_
      rcases eq_or_ne m i with rfl | hmi
      · rw [transvection_conj_left hij hm hpj (-c) 1]
        exact mul_mem (hQ1 m hm 1) (inv_mem (hQ1 j hpj _))
      · rw [(SpecialLinearGroup.commute_transvection hij hm (Ne.symm hpj) hmi (-c) 1).eq,
          mul_inv_cancel_right]
        exact hQ1 m hm 1
    have hw2 : ∀ (m : Fin n) (hm : m ≠ q), Commute (u * y * u⁻¹ * y⁻¹)
        (φ (SpecialLinearGroup.transvection hm 1)) := by
      intro m hm
      refine hgen _ (hQ2 m hm 1) ?_
      rcases eq_or_ne m j with rfl | hmj
      · rw [transvection_conj_right hij hm (Ne.symm hqi) (-c) 1]
        exact mul_mem (hQ2 m hm 1) (hQ2 i (Ne.symm hqi) _)
      · rw [(SpecialLinearGroup.commute_transvection hij hm (Ne.symm hmj) hqi (-c) 1).eq,
          mul_inv_cancel_right]
        exact hQ2 m hm 1
    obtain ⟨M, hM⟩ := LinearFlag.proj_surjective n K (e ⟨_, hwL⟩)
    have hφM : φ M = u * y * u⁻¹ * y⁻¹ := by
      rw [hφapp, hM, MulEquiv.symm_apply_apply]
    have hM1 : ∀ (m : Fin n) (hm : p ≠ m),
        M * SpecialLinearGroup.transvection hm 1 = SpecialLinearGroup.transvection hm 1 * M := by
      intro m hm
      apply hφinj
      rw [map_mul, map_mul, hφM]
      exact (hw1 m hm).eq
    have hM2 : ∀ (m : Fin n) (hm : m ≠ q),
        M * SpecialLinearGroup.transvection hm 1 = SpecialLinearGroup.transvection hm 1 * M := by
      intro m hm
      apply hφinj
      rw [map_mul, map_mul, hφM]
      exact (hw2 m hm).eq
    have hMeq := eq_transvection_of_commute_row_col hK hpq hM1 hM2
    have hwZ : u * y * u⁻¹ * y⁻¹ ∈ Z := by
      refine ⟨Multiplicative.ofAdd ((M : Matrix (Fin n) (Fin n) K) p q), ?_⟩
      rw [← hφM, MonoidHom.comp_apply, SpecialLinearGroup.transvectionHom_apply, toAdd_ofAdd,
        ← hMeq]
    refine ⟨u * y * u⁻¹ * y⁻¹, hwZ, ?_⟩
    have hc := (hyZ i j hij c hi' hj' _ hwZ).eq
    calc u * y * u⁻¹ = (u * y * u⁻¹ * y⁻¹) * y := by group
      _ = y * (u * y * u⁻¹ * y⁻¹) := hc.symm
  rw [hJ]
  exact mem_centralizer_of_conj_eq_mul hperf hSZ hZZ hconj

end Main

section RevComm

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]
  {F : Type} [Field F] [Finite F]

theorem fieldRevComm_six (hL : CFSG.Open.standardComponentIsStandard L) [CharP K 2]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {ι : K →+* F} {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (hn : n = 6)
    {Xr : Fin n → Fin n → Subgroup (LinearFlag.projectiveSL n K)}
    (hXr : ∀ a b, Xr a b ≤ rootSL2 a b)
    (hXc : ∀ a b, a ≠ b → Nat.card (Xr a b) = Nat.card K + 1)
    (P : ∀ a b : Fin n, a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin n))) :
    FieldRevComm e P := by
  classical
  have hF : 4 ≤ Nat.card F := by
    rw [natCard_eq_sq_of_fixedField ι hσ1 hσσ hfix, hK]
    norm_num
  have hXy : ∀ (a b : Fin n) (hab : a ≠ b), order3Elt K hab ∈ Xr a b := fun a b hab =>
    order3Elt_mem_of_card_eq_three hK (by omega) hab (hXr a b) (by rw [hXc a b hab, hK])
  intro a b hab A hA hdis
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.1 hA
  have hsub : ({p, q} : Finset (Fin n)) ⊆ ({a, b}ᶜ : Finset (Fin n)) :=
    Finset.subset_compl_iff_disjoint_right.2 hdis
  have key : ∀ (i j : Fin n) (hij : i ≠ j) (hi : i ∈ ({p, q} : Finset (Fin n)))
      (hj : j ∈ ({p, q} : Finset (Fin n))) (s : F),
      (P a b hab).Φ ⟨SpecialLinearGroup.transvection hij s,
          transvection_mem_blockSpecialLinear hij (hsub hi) (hsub hj) s⟩ ∈
        centralizer (modelToG e (blockSL (K := K) ({p, q} : Finset (Fin n))ᶜ) : Set G) := by
    intro i j hij hi hj s
    have hij_eq : ({i, j} : Finset (Fin n)) = {p, q} := by
      refine Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_pair hij, Finset.card_pair hpq])
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hi
      · rw [Finset.mem_singleton.1 hx]
        exact hj
    have h := map_transvection_mem_centralizer_six hL hK e htC ht hσσ hfix hn hF hXr hXy P hab
      hij (hsub hi) (hsub hj) s
    rwa [hij_eq] at h
  rintro _ ⟨x, hx, rfl⟩
  replace hx : (x : SpecialLinearGroup (Fin n) F) ∈
      blockSpecialLinear (K := F) ({p, q} : Finset (Fin n)) := mem_subgroupOf.1 hx
  have hle : blockSpecialLinear (K := F) ({p, q} : Finset (Fin n)) ≤
      ((centralizer (modelToG e (blockSL (K := K) ({p, q} : Finset (Fin n))ᶜ) : Set G)).comap
        (P a b hab).Φ).map (blockSpecialLinear (K := F) ({a, b}ᶜ : Finset (Fin n))).subtype := by
    rw [blockSpecialLinear_eq_closure (K := F) ({p, q} : Finset (Fin n)), closure_le]
    rintro _ ⟨i, j, hij, s, hi, hj, rfl⟩
    exact ⟨⟨_, transvection_mem_blockSpecialLinear hij (hsub hi) (hsub hj) s⟩, key i j hij hi hj s,
      rfl⟩
  obtain ⟨x', hx', hxx'⟩ := hle hx
  have hx'x : x' = x := Subtype.ext hxx'
  rw [← hx'x]
  exact hx'

end RevComm

theorem linearTwoFieldRevCommSixInput_holds : LinearTwoFieldRevCommSixInput := by
  intro G _ _ L hset n K _ _ hK hn e t ht hKt F _ _ ι σ hσ1 hσσ hfix Xr hXr hXc P
  exact fieldRevComm_six hset.standardSetting.standard hK e
    (mem_centralizer_of_inf_eq_zpowers hKt) ht hσ1 hσσ hfix hn hXr hXc P

section Assembly

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

theorem linearTwoFiveSixInput_of_at_six (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor3 : CatSLmSporadicAt 3) (hSpor4 : CatSLmSporadicAt 4)
    (hF5 : LinearTwoFieldKindAtInput 5) (hS5 : LinearTwoSwapRowAtInput 5)
    (hR5 : LinearTwoSmallKindAtInput 5) (hS6 : LinearTwoSwapRowAtInput 6)
    (hR6 : LinearTwoSmallKindAtInput 6) : LinearTwoFiveSixInput :=
  linearTwoFiveSixInput_of_at_of_revComm hGLS hSpor3 hSpor4 hF5 hS5 hR5
    linearTwoFieldRevCommSixInput_holds hS6 hR6

end Assembly

end CFSG.SeitzReduction.LinearPilot
