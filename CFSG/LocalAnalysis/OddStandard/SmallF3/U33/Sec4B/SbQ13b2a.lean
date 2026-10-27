module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a3

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13b_tau_comm_aux {t om tau f : G} {V : Subgroup G}
    (ht : t * t = 1) (hom : om * om = 1) (hto : om * t * om⁻¹ = t * tau)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a * a = 1)
    (htV : ∀ a ∈ V, t * a = a * t) (homV : ∀ a ∈ V, om * a = a * om)
    (ha : t * f * t⁻¹ * f⁻¹ ∈ V) (hb : om * f * om⁻¹ * f⁻¹ ∈ V) :
    tau * f = f * tau := by
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_right hom
  let a : G := t * f * t⁻¹ * f⁻¹
  let b : G := om * f * om⁻¹ * f⁻¹
  have haV : a ∈ V := ha
  have hbV : b ∈ V := hb
  have h1 : t * f * t⁻¹ = a * f := by dsimp only [a]; group
  have h2inv : om * f * om⁻¹ = b * f := by dsimp only [b]; group
  have h2 : om * f * om = b * f := by simpa only [hom_inv] using h2inv
  have h2' : om * f = b * f * om := by
    rw [← h2]
    rw [mul_assoc, hom, mul_one]
  have htb : t * b * t⁻¹ = b := by rw [htV b hbV]; group
  have hta : t * a * t⁻¹ = a := by rw [htV a haV]; group
  have homa : om * a * om = a := by
    calc om * a * om = (a * om) * om := by rw [homV a haV]
      _ = a * (om * om) := by group
      _ = a := by rw [hom, mul_one]
  have homb : om * b * om = b := by
    calc om * b * om = (b * om) * om := by rw [homV b hbV]
      _ = b * (om * om) := by group
      _ = b := by rw [hom, mul_one]
  have hab : a * b = b * a := hVc a haV b hbV
  have ha2 : a * a = 1 := hV2 a haV
  have hb2 : b * b = 1 := hV2 b hbV
  have hbab : b * a * b = a := by
    calc b * a * b = a * b * b := by rw [hab]
      _ = a * (b * b) := by group
      _ = a := by rw [hb2, mul_one]
  have htfae : t * (b * f) * t = b * (a * f) := by
    calc t * (b * f) * t = (t * b * t⁻¹) * (t * f * t⁻¹) * (t * t) := by group
      _ = b * (a * f) * (t * t) := by rw [htb, h1]
      _ = b * (a * f) := by rw [ht, mul_one]
  have homabf : om * (b * (a * f)) * om = a * f := by
    calc om * (b * (a * f)) * om = (om * b) * a * f * om := by group
      _ = (b * om) * a * f * om := by rw [homV b hbV]
      _ = b * (om * a) * f * om := by group
      _ = b * (a * om) * f * om := by rw [homV a haV]
      _ = b * a * (om * f) * om := by group
      _ = b * a * (b * f * om) * om := by rw [h2']
      _ = b * a * b * f * (om * om) := by group
      _ = b * a * b * f := by rw [hom, mul_one]
      _ = a * f := by rw [hbab]
  have hsf : (om * t * om) * f * (om * t * om)⁻¹ = a * f := by
    have hs_inv : (om * t * om)⁻¹ = om * t * om := by
      rw [mul_inv_rev, mul_inv_rev, hom_inv, ht_inv]; group
    rw [hs_inv]
    calc om * t * om * f * (om * t * om)
        = om * (t * (om * f * om) * t) * om := by group
      _ = om * (t * (b * f) * t) * om := by rw [h2]
      _ = om * (b * (a * f)) * om := by rw [htfae]
      _ = a * f := homabf
  have htau : tau * f * tau⁻¹ = f := by
    have hto' : om * t * om = t * tau := by simpa only [hom_inv] using hto
    have htau_eq : tau = t * (om * t * om) := by
      calc tau = (t * t) * tau := by rw [ht, one_mul]
        _ = t * (t * tau) := by group
        _ = t * (om * t * om) := by rw [← hto']
    rw [htau_eq]
    calc t * (om * t * om) * f * (t * (om * t * om))⁻¹
        = t * ((om * t * om) * f * (om * t * om)⁻¹) * t⁻¹ := by group
      _ = t * (a * f) * t⁻¹ := by rw [hsf]
      _ = (t * a * t⁻¹) * (t * f * t⁻¹) := by group
      _ = a * (a * f) := by rw [hta, h1]
      _ = f := by rw [← mul_assoc, ha2, one_mul]
  calc tau * f = (tau * f * tau⁻¹) * tau := by group
    _ = f * tau := by rw [htau]

theorem q13b_comm_mem_of_index_two {F F₀ : Subgroup G} (hle : F₀ ≤ F)
    (hcard : Nat.card F = 2 * Nat.card F₀) {g : G}
    (hgF : ∀ x ∈ F, g * x * g⁻¹ ∈ F) (hgF₀ : ∀ x ∈ F₀, g * x * g⁻¹ ∈ F₀)
    (hgF₀' : ∀ x ∈ F₀, g⁻¹ * x * g ∈ F₀) : ∀ f ∈ F, g * f * g⁻¹ * f⁻¹ ∈ F₀ := by
  intro f hf
  have hindex : (F₀.subgroupOf F).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := F₀) (K := F)
    rw [inf_eq_left.mpr hle] at h1
    have h2 : F₀.relIndex F * Nat.card F₀ = 2 * Nat.card F₀ := by rw [h1, hcard]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  let f' : ↥F := ⟨f, hf⟩
  let g' : ↥F := ⟨g * f * g⁻¹, hgF f hf⟩
  have hiff : g' ∈ F₀.subgroupOf F ↔ f'⁻¹ ∈ F₀.subgroupOf F := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hgv
      have hf₀ : f ∈ F₀ := by
        have h1 := hgF₀' (g' : G) hgv
        have hg'coe : (g' : G) = g * f * g⁻¹ := rfl
        rw [hg'coe] at h1
        convert h1 using 1
        group
      exact F₀.inv_mem hf₀
    · intro hfv
      have hf₀ : f ∈ F₀ := by
        have h1 : f⁻¹ ∈ F₀ := by simpa [f'] using hfv
        simpa using F₀.inv_mem h1
      exact hgF₀ f hf₀
  have hmul : g' * f'⁻¹ ∈ F₀.subgroupOf F :=
    (Subgroup.mul_mem_iff_of_index_two hindex).mpr hiff
  have hcoe : ((g' * f'⁻¹ : ↥F) : G) = g * f * g⁻¹ * f⁻¹ := by simp [g', f']
  rw [Subgroup.mem_subgroupOf] at hmul
  rw [hcoe] at hmul
  exact hmul

private theorem q13b_card_range_eq_index {H X : Type*} [Group H] (f : H → X) (K : Subgroup H)
    (hK : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ K) : Nat.card (Set.range f) = K.index := by
  rw [Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective (fun q : H ⧸ K => (⟨Quotient.liftOn' q f
    (fun a b hab => (hK a b).mpr (QuotientGroup.leftRel_apply.mp hab)), by
      induction q using QuotientGroup.induction_on with | H a => exact ⟨a, rfl⟩⟩ :
      Set.range f)) ⟨fun q q' hqq => ?_, fun y => ?_⟩).symm
  · induction q using QuotientGroup.induction_on with | H a => ?_
    induction q' using QuotientGroup.induction_on with | H b => ?_
    have e : f a = f b := congrArg Subtype.val hqq
    exact QuotientGroup.eq.mpr ((hK a b).mp e)
  · obtain ⟨_, a, rfl⟩ := y
    exact ⟨QuotientGroup.mk a, rfl⟩

private theorem q13b_card_conj_orbit {H P : Type*} [Group H] [Group P] (σ : H →* P) (F : P) :
    Nat.card (Set.range fun c : H => σ c * F * (σ c)⁻¹) =
      ((centralizer ({F} : Set P)).comap σ).index := by
  refine q13b_card_range_eq_index _ _ fun a b => ?_
  rw [mem_comap, mem_centralizer_singleton_iff, map_mul, map_inv]
  constructor
  · intro h
    calc (σ a)⁻¹ * σ b * F = (σ a)⁻¹ * (σ b * F * (σ b)⁻¹) * σ b := by group
      _ = (σ a)⁻¹ * (σ a * F * (σ a)⁻¹) * σ b := by rw [h]
      _ = F * ((σ a)⁻¹ * σ b) := by group
  · intro h
    calc σ a * F * (σ a)⁻¹ = σ a * (F * ((σ a)⁻¹ * σ b)) * (σ b)⁻¹ := by group
      _ = σ a * ((σ a)⁻¹ * σ b * F) * (σ b)⁻¹ := by rw [h]
      _ = σ b * F * (σ b)⁻¹ := by group

private theorem q13b_card_le_mul_card_orbit {H : Subgroup G} (x : G) {n : ℕ}
    (hn : Nat.card (Set.range fun h : H => (h : G) * x * (h : G)⁻¹) ≤ n) :
    Nat.card H ≤ n * Nat.card ↥(H ⊓ centralizer ({x} : Set G)) := by
  have h1 := q13b_card_conj_orbit H.subtype x
  have h2 := Subgroup.card_mul_index ((centralizer ({x} : Set G)).comap H.subtype)
  have h3 : Nat.card ((centralizer ({x} : Set G)).comap H.subtype) =
      Nat.card (H ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    have e := Subgroup.inf_subgroupOf_left (centralizer ({x} : Set G)) H
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : H ⊓ centralizer ({x} : Set G) ≤ H)).toEquiv, e]
    rfl
  have h4 : ((centralizer ({x} : Set G)).comap H.subtype).index ≤ n := by
    rw [← h1]
    exact hn
  rw [← h3, ← h2]
  calc Nat.card ((centralizer ({x} : Set G)).comap H.subtype) *
        ((centralizer ({x} : Set G)).comap H.subtype).index
      ≤ Nat.card ((centralizer ({x} : Set G)).comap H.subtype) * n := Nat.mul_le_mul_left _ h4
    _ = n * Nat.card ((centralizer ({x} : Set G)).comap H.subtype) := mul_comm _ _

theorem q13b_card_le_two_mul {H : Subgroup G} {f z : G}
    (hf : ∀ n ∈ H, n * f * n⁻¹ = f ∨ n * f * n⁻¹ = f * z) :
    Nat.card H ≤ 2 * Nat.card ↥(H ⊓ centralizer ({f} : Set G)) := by
  refine q13b_card_le_mul_card_orbit (H := H) f (n := 2) ?_
  have hsub : Set.range (fun n : H => (n : G) * f * (n : G)⁻¹) ⊆ ({f, f * z} : Set G) := by
    rintro _ ⟨n, rfl⟩
    rcases hf n n.2 with h | h <;> simp [h]
  have hfin : ({f, f * z} : Set G).Finite := Set.toFinite _
  have hpair : Nat.card ({f, f * z} : Set G) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    exact le_trans (Set.ncard_insert_le f {f * z}) (by simp)
  exact le_trans (Nat.card_mono hfin hsub) hpair

theorem q13b_omega1_A (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, a * a = 1 → a ∈ fourGrp x₁ x₂ := by
  classical
  intro a haA haa
  haveI hAfin : Fintype ↥(q13A t tau x₁ x₂ rho) := Fintype.ofFinite _
  haveI hVfin : Fintype ↥(fourGrp x₁ x₂) := Fintype.ofFinite _
  have hVleA : fourGrp x₁ x₂ ≤ q13A t tau x₁ x₂ rho := q13a_V_le_A h
  have hVexp : ∀ v ∈ fourGrp x₁ x₂, v * v = 1 := by
    intro v hv
    have := (h.c11.wreath.fourGrp_eq_omega.2.1).2 v hv
    simpa [pow_two] using this
  have hVcard : Nat.card (fourGrp x₁ x₂) = 4 := h.c11.wreath.fourGrp_eq_omega.2.2
  obtain ⟨e⟩ := q13a_A_iso h
  have hZcard : (Finset.univ.filter (fun x : Outside.Z4pow 2 => x * x = 1)).card = 4 := by
    decide +kernel
  have hAle4 : (Finset.univ.filter (fun x : ↥(q13A t tau x₁ x₂ rho) => x * x = 1)).card ≤ 4 := by
    have hsub : (Finset.univ.filter (fun x : ↥(q13A t tau x₁ x₂ rho) => x * x = 1)).image e ⊆
        (Finset.univ.filter (fun x : Outside.Z4pow 2 => x * x = 1)) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [← map_mul, hx.2, map_one]⟩
    have hh := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ e.injective, hZcard] at hh
    exact hh
  have hVfull : (Finset.univ.filter (fun x : ↥(fourGrp x₁ x₂) => x * x = 1)) = Finset.univ :=
    Finset.filter_true_of_mem (fun x _ => Subtype.ext (by simpa using hVexp x x.2))
  have hVcard4 : (Finset.univ.filter (fun x : ↥(fourGrp x₁ x₂) => x * x = 1)).card = 4 := by
    rw [hVfull, Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hVcard
  have himage : (Finset.univ.filter (fun x : ↥(fourGrp x₁ x₂) => x * x = 1)).image
        (Subgroup.inclusion hVleA) ⊆
        (Finset.univ.filter (fun x : ↥(q13A t tau x₁ x₂ rho) => x * x = 1)) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← map_mul, hx.2, map_one]
  have hTeq : (Finset.univ.filter (fun x : ↥(fourGrp x₁ x₂) => x * x = 1)).image
        (Subgroup.inclusion hVleA) =
        (Finset.univ.filter (fun x : ↥(q13A t tau x₁ x₂ rho) => x * x = 1)) := by
    refine Finset.eq_of_subset_of_card_le himage ?_
    rw [Finset.card_image_of_injective _ (Subgroup.inclusion_injective hVleA), hVcard4]
    exact hAle4
  have haT : (⟨a, haA⟩ : ↥(q13A t tau x₁ x₂ rho)) ∈
      (Finset.univ.filter (fun x : ↥(q13A t tau x₁ x₂ rho) => x * x = 1)) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Subtype.ext (by simpa using haa)⟩
  rw [← hTeq] at haT
  obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp haT
  have hxa : a = (x : G) := by
    have h1 := congrArg Subtype.val hxeq
    simpa using h1.symm
  rw [hxa]
  exact x.2

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
