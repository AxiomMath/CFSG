module

public import CFSG.FeitThompson.Representations.CoprimeAutomorphismCosetPartition
public import CFSG.FeitThompson.Representations.DadeInducedTransportFormula
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {G : Type*} [Group G]

def conjTransporter (S : Set G) (g : G) : Set G := {x : G | x⁻¹ * g * x ∈ S}

theorem mem_conjTransporter_iff {S : Set G} {g x : G} :
    x ∈ conjTransporter S g ↔ x⁻¹ * g * x ∈ S := Iff.rfl

theorem conjTransporter_mono {S T : Set G} (h : S ⊆ T) (g : G) :
    conjTransporter S g ⊆ conjTransporter T g := fun _ hx => h hx

theorem dadeTransporter_eq_conjTransporter (H : G → Subgroup G) (B : Set G) (g a : G) :
    dadeTransporter H B g a
      = conjTransporter (((dadeInter H B : Subgroup G) : Set G) * {a}) g := by
  ext x
  rw [mem_dadeTransporter_iff, mem_conjTransporter_iff, Set.mul_singleton, Set.mem_image]
  exact ⟨fun h => ⟨_, h, by group⟩, fun ⟨u, hu, he⟩ => by rw [← he]; simpa using hu⟩

theorem natCard_eq_natCard_mul_of_natCard_fiber {α β : Type*} [Finite α] [Finite β]
    {f : α → β} {s : Set α} {t : Set β} (hmaps : Set.MapsTo f s t) {n : ℕ}
    (hfib : ∀ y ∈ t, Nat.card {x : α | x ∈ s ∧ f x = y} = n) :
    Nat.card s = Nat.card t * n := by
  classical
  have _ := Fintype.ofFinite α
  have _ := Fintype.ofFinite β
  have h1 : s.toFinset.card = ∑ y ∈ t.toFinset, ({x ∈ s.toFinset | f x = y}).card :=
    Finset.card_eq_sum_card_fiberwise (by simpa using hmaps)
  have h2 : ∀ y ∈ t.toFinset, ({x ∈ s.toFinset | f x = y}).card = n := by
    intro y hy
    rw [Set.mem_toFinset] at hy
    have he : ({x ∈ s.toFinset | f x = y}) = ({x : α | x ∈ s ∧ f x = y} : Set α).toFinset := by
      ext z; simp
    rw [he, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hfib y hy
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul] at h1
  simpa [Set.toFinset_card, Nat.card_eq_fintype_card] using h1

section Toggle

variable {K : Subgroup G} {a g : G}

theorem centralizerCoset_eq_coe_mul_singleton (K : Subgroup G) (a : G) :
    centralizerCoset K a
      = ((K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) * {a} := by
  ext x
  rw [mem_centralizerCoset_iff, Set.mul_singleton, Set.mem_image]
  refine ⟨fun hx => ⟨x * a⁻¹, hx, by group⟩, ?_⟩
  rintro ⟨y, hy, rfl⟩
  simpa using hy

theorem centralizerCoset_subset_coe_mul_singleton (K : Subgroup G) (a : G) :
    centralizerCoset K a ⊆ (K : Set G) * {a} := by
  rw [centralizerCoset_eq_coe_mul_singleton]
  exact Set.mul_subset_mul_right (by exact_mod_cast inf_le_left (a := K))

theorem conj_mem_coe_mul_singleton (hnorm : a ∈ Subgroup.normalizer (K : Set G)) {h : G}
    (hh : h ∈ K) {w : G} (hw : w ∈ (K : Set G) * {a}) : h * w * h⁻¹ ∈ (K : Set G) * {a} := by
  rw [Set.mul_singleton, Set.mem_image] at hw ⊢
  obtain ⟨k, hk, rfl⟩ := hw
  refine ⟨h * k * (a * h⁻¹ * a⁻¹), ?_, by group⟩
  have h2 : a * h⁻¹ * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hnorm h⁻¹).1 (K.inv_mem hh)
  exact K.mul_mem (K.mul_mem hh hk) h2

private def transporterPairs (K : Subgroup G) (a g : G) : Set (G × G) :=
  {p : G × G | p.2 ∈ K ∧ p.1 * p.2 ∈ conjTransporter (centralizerCoset K a) g}

private theorem mapsTo_fst_transporterPairs (hnorm : a ∈ Subgroup.normalizer (K : Set G)) :
    Set.MapsTo Prod.fst (transporterPairs K a g)
      (conjTransporter ((K : Set G) * {a}) g) := by
  rintro ⟨z, h⟩ ⟨hh, hz⟩
  rw [mem_conjTransporter_iff] at hz
  have hz' : (z * h)⁻¹ * g * (z * h) ∈ (K : Set G) * {a} :=
    centralizerCoset_subset_coe_mul_singleton K a hz
  have key : z⁻¹ * g * z = h * ((z * h)⁻¹ * g * (z * h)) * h⁻¹ := by group
  rw [mem_conjTransporter_iff, key]
  exact conj_mem_coe_mul_singleton hnorm hh hz'

private theorem mapsTo_mul_transporterPairs :
    Set.MapsTo (fun p : G × G => p.1 * p.2) (transporterPairs K a g)
      (conjTransporter (centralizerCoset K a) g) := fun _ hp => hp.2

private theorem natCard_fiber_mul_transporterPairs {y : G}
    (hy : y ∈ conjTransporter (centralizerCoset K a) g) :
    Nat.card {p : G × G | p ∈ transporterPairs K a g ∧ p.1 * p.2 = y} = Nat.card K := by
  have himg : {p : G × G | p ∈ transporterPairs K a g ∧ p.1 * p.2 = y}
      = (fun h : G => (y * h⁻¹, h)) '' (K : Set G) := by
    ext ⟨z, h⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, transporterPairs, SetLike.mem_coe]
    constructor
    · rintro ⟨⟨hh, -⟩, hzh⟩
      exact ⟨h, hh, by simp [← hzh]⟩
    · rintro ⟨k, hk, hEq⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hEq
      refine ⟨⟨hk, ?_⟩, by group⟩
      simpa using hy
  rw [himg, Nat.card_image_of_injective (fun h₁ h₂ hE => by simpa using (Prod.ext_iff.1 hE).2)]
  rfl

theorem natCard_setOf_conj_mem_centralizerCoset [Finite K]
    (hcop : (Nat.card K).Coprime (orderOf a)) (hfin : IsOfFinOrder a)
    (hnorm : a ∈ Subgroup.normalizer (K : Set G)) {w : G} (hw : w ∈ (K : Set G) * {a}) :
    Nat.card {h : G | h ∈ K ∧ h⁻¹ * w * h ∈ centralizerCoset K a}
      = Nat.card (K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) := by
  obtain ⟨S, ⟨hSmem, hwS⟩, hSuniq⟩ :=
    existsUnique_mem_centralizerCosetConjugates hcop hfin hnorm hw
  obtain ⟨h₀, hh₀, rfl⟩ := mem_centralizerCosetConjugates_iff.1 hSmem
  have hset : {h : G | h ∈ K ∧ h⁻¹ * w * h ∈ centralizerCoset K a}
      = h₀ • ((K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨hhK, hconj⟩
      have hw' : w ∈ ConjAct.toConjAct h • centralizerCoset K a :=
        mem_conjAct_smul_set_iff.2 hconj
      have hEq := hSuniq _ ⟨mem_centralizerCosetConjugates_iff.2 ⟨h, hhK, rfl⟩, hw'⟩
      have hmul : ConjAct.toConjAct (h₀⁻¹ * h) • centralizerCoset K a = centralizerCoset K a := by
        rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff, hEq]
      exact (smul_centralizerCoset_eq_iff hcop hfin (K.mul_mem (K.inv_mem hh₀) hhK)).1 hmul
    · intro hc
      have hhK : h ∈ K := by
        have hh : h = h₀ * (h₀⁻¹ * h) := by group
        rw [hh]
        exact K.mul_mem hh₀ (Subgroup.mem_inf.1 hc).1
      refine ⟨hhK, mem_conjAct_smul_set_iff.1 ?_⟩
      have hEq : ConjAct.toConjAct h • centralizerCoset K a
          = ConjAct.toConjAct h₀ • centralizerCoset K a := by
        have hs := smul_centralizerCoset_of_mem (a := a) hc
        rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff] at hs
        exact hs
      rw [hEq]; exact hwS
  rw [hset, Set.natCard_smul_set]
  rfl

private theorem natCard_transporterPairs_fst [Finite G]
    (hcop : (Nat.card K).Coprime (orderOf a)) (hfin : IsOfFinOrder a)
    (hnorm : a ∈ Subgroup.normalizer (K : Set G)) :
    Nat.card (transporterPairs K a g)
      = Nat.card (conjTransporter ((K : Set G) * {a}) g)
        * Nat.card (K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) := by
  refine natCard_eq_natCard_mul_of_natCard_fiber (mapsTo_fst_transporterPairs hnorm) ?_
  intro z hz
  have hw : z⁻¹ * g * z ∈ (K : Set G) * {a} := mem_conjTransporter_iff.1 hz
  have himg : {p : G × G | p ∈ transporterPairs K a g ∧ p.1 = z}
      = (fun h : G => (z, h)) ''
        {h : G | h ∈ K ∧ h⁻¹ * (z⁻¹ * g * z) * h ∈ centralizerCoset K a} := by
    ext ⟨z', h⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, transporterPairs, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hh, hmem⟩, rfl⟩
      refine ⟨h, ⟨hh, ?_⟩, rfl, rfl⟩
      have key : h⁻¹ * (z'⁻¹ * g * z') * h = (z' * h)⁻¹ * g * (z' * h) := by group
      rw [key]; exact hmem
    · rintro ⟨k, ⟨hk, hkmem⟩, rfl, rfl⟩
      refine ⟨⟨hk, ?_⟩, rfl⟩
      have key : (z * k)⁻¹ * g * (z * k) = k⁻¹ * (z⁻¹ * g * z) * k := by group
      rw [mem_conjTransporter_iff, key]; exact hkmem
  rw [himg, Nat.card_image_of_injective (fun h₁ h₂ hE => by simpa using (Prod.ext_iff.1 hE).2)]
  exact natCard_setOf_conj_mem_centralizerCoset hcop hfin hnorm hw

private theorem natCard_transporterPairs_mul [Finite G] :
    Nat.card (transporterPairs K a g)
      = Nat.card (conjTransporter (centralizerCoset K a) g) * Nat.card K :=
  natCard_eq_natCard_mul_of_natCard_fiber mapsTo_mul_transporterPairs
    fun _ hy => natCard_fiber_mul_transporterPairs hy

theorem natCard_conjTransporter_mul_natCard_inf_centralizer [Finite G]
    (hcop : (Nat.card K).Coprime (orderOf a)) (hnorm : a ∈ Subgroup.normalizer (K : Set G))
    (g : G) :
    Nat.card (conjTransporter ((K : Set G) * {a}) g)
        * Nat.card (K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G)
      = Nat.card (conjTransporter (centralizerCoset K a) g) * Nat.card K := by
  rw [← natCard_transporterPairs_fst hcop (isOfFinOrder_of_finite a) hnorm,
    natCard_transporterPairs_mul]

end Toggle

variable {L : Subgroup G} {A B : Set G} {H : G → Subgroup G} {a g : G}

namespace IsDadeData

variable [Finite G]

theorem mem_normalizer_dadeInter (hD : IsDadeData L A H) (ha : a ∈ A) (hBA : B ⊆ A)
    (hnB : a ∈ Subgroup.normalizer B) :
    a ∈ Subgroup.normalizer ((dadeInter H B : Subgroup G) : Set G) := by
  have hBa : (fun x => a * x * a⁻¹) '' B = B := Subgroup.mem_normalizer_iff_conj_image_eq.1 hnB
  have heq : MulAut.conj a • dadeInter H B = dadeInter H B := by
    rw [hD.conj_smul_dadeInter hBA (hD.mem_of_mem ha), hBa]
  rw [Subgroup.mem_normalizer_iff]
  refine fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · have hm : a * h * a⁻¹ ∈ MulAut.conj a • dadeInter H B := by
      rw [mem_conj_smul_iff]; simpa [mul_assoc] using hh
    rwa [heq] at hm
  · rw [← heq, mem_conj_smul_iff] at hh
    simpa [mul_assoc] using hh

theorem coprime_natCard_dadeInter_orderOf (hD : IsDadeData L A H) (ha : a ∈ A) (hBA : B ⊆ A)
    (hB : B.Nonempty) : (Nat.card (dadeInter H B)).Coprime (orderOf a) := by
  refine coprime_of_isPiNumber_compl Nat.card_pos.ne' (orderOf_pos a).ne'
    (hD.isPiNumber_compl_card_dadeInter hBA hB) ?_
  refine (IsDadeData.isPiNumber_card_inf_centralizer (L := L) (A := A) ha).of_dvd ?_
    Nat.card_pos.ne'
  exact Subgroup.orderOf_dvd_natCard _ ⟨hD.mem_of_mem ha, by simp [Subgroup.mem_centralizer_iff]⟩

theorem dadeTransporter_insert_eq (hD : IsDadeData L A H) (ha : a ∈ A) (hBA : B ⊆ A)
    (hB : B.Nonempty) (g : G) :
    dadeTransporter H (insert a B) g a
      = conjTransporter (centralizerCoset (dadeInter H B) a) g := by
  rw [dadeTransporter_eq_conjTransporter, centralizerCoset_eq_coe_mul_singleton,
    hD.dadeInter_insert_eq_inf_centralizer ha hBA hB]

theorem natCard_dadeTransporter_mul_natCard_dadeInter_insert (hD : IsDadeData L A H) (ha : a ∈ A)
    (hBA : B ⊆ A) (hB : B.Nonempty) (hnB : a ∈ Subgroup.normalizer B) (g : G) :
    Nat.card (dadeTransporter H B g a) * Nat.card (dadeInter H (insert a B))
      = Nat.card (dadeTransporter H (insert a B) g a) * Nat.card (dadeInter H B) := by
  rw [hD.dadeTransporter_insert_eq ha hBA hB, dadeTransporter_eq_conjTransporter,
    hD.dadeInter_insert_eq_inf_centralizer ha hBA hB]
  exact natCard_conjTransporter_mul_natCard_inf_centralizer
    (hD.coprime_natCard_dadeInter_orderOf ha hBA hB)
    (hD.mem_normalizer_dadeInter ha hBA hnB) g

theorem natCard_dadeTransporter_div_natCard_dadeInter (hD : IsDadeData L A H) (ha : a ∈ A)
    (hBA : B ⊆ A) (hB : B.Nonempty) (hnB : a ∈ Subgroup.normalizer B) (g : G) :
    (Nat.card (dadeTransporter H B g a) : ℚ) / Nat.card (dadeInter H B)
      = (Nat.card (dadeTransporter H (insert a B) g a) : ℚ)
        / Nat.card (dadeInter H (insert a B)) := by
  have h1 : (0 : ℚ) < Nat.card (dadeInter H B) := by
    exact_mod_cast Nat.card_pos (α := (dadeInter H B : Subgroup G))
  have h2 : (0 : ℚ) < Nat.card (dadeInter H (insert a B)) := by
    exact_mod_cast Nat.card_pos (α := (dadeInter H (insert a B) : Subgroup G))
  rw [div_eq_div_iff h1.ne' h2.ne']
  exact_mod_cast hD.natCard_dadeTransporter_mul_natCard_dadeInter_insert ha hBA hB hnB g

end IsDadeData

end CFSG.FeitThompson
