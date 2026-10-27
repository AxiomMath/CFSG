module

public import CFSG.LargeExtraspecial.AS35GBasic
public import CFSG.LocalAnalysis.SignalizerFunctor.RelativeWeakClosure

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.SignalizerFunctor.Helpers

namespace AschTI

variable {G : Type} [Group G] (S : Setting G)

theorem card_le_four_of_subset {A : Subgroup G} {a b c d : G}
    (h : (A : Set G) ⊆ {a, b, c, d}) : Nat.card A ≤ 4 := by
  have h1 := Set.ncard_le_ncard h (Set.toFinite _)
  have h2 : ({a, b, c, d} : Set G).ncard ≤ 4 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1).trans ?_
    rw [Set.ncard_singleton]
  have hcard : Nat.card A = (A : Set G).ncard := Nat.card_coe_set_eq (A : Set G)
  omega

theorem commutator_mem_QG {x p : G} (hx : x ∈ S.QG) (hp : p ∈ S.M) :
    x * p * x⁻¹ * p⁻¹ ∈ S.QG := by
  have h := S.QG.mul_mem hx (S.conj_mem_QG hp (S.QG.inv_mem hx))
  simpa only [mul_assoc] using h

theorem not_QG_le_tiR {g : G} (hgM : g ∉ S.M) (hgz : g * S.z * g⁻¹ ∈ S.M) :
    ¬ S.QG ≤ S.tiR g := by
  intro h
  have hc : ∀ x ∈ S.QG, g * S.z * g⁻¹ * x = x * (g * S.z * g⁻¹) := fun x hx =>
    (mem_centralizer_singleton_iff.mp (h hx).2).symm
  have htQ := S.mem_QG_of_commute hgz hc
  rcases S.eq_one_or_z_of_commute htQ hc with h1 | h1
  · exact t_ne_one S g h1
  · exact hgM (S.mem_M_iff.mpr (by calc g * S.z = g * S.z * g⁻¹ * g := by group
      _ = S.z * g := by rw [h1]))

theorem conj_mem_relativeWeakClosure {g x p : G} (hx : x ∈ S.QG) (hp : p ∈ S.tiP g) :
    x * p * x⁻¹ ∈ relativeWeakClosure S.QG (S.tiP g) (S.QG ⊔ S.tiP g) := by
  have hle : conjugateSubgroup x (S.tiP g) ≤ S.QG ⊔ S.tiP g := by
    rintro _ ⟨q, hq, rfl⟩
    have h : x * q * x⁻¹ = x * q * x⁻¹ * q⁻¹ * q := by group
    change x * q * x⁻¹ ∈ S.QG ⊔ S.tiP g
    rw [h]
    exact mul_mem (mem_sup_left (commutator_mem_QG S hx hq.2)) (mem_sup_right hq)
  have hmem : x * p * x⁻¹ ∈ conjugateSubgroup x (S.tiP g) := ⟨p, hp, rfl⟩
  have hW : conjugateSubgroup x (S.tiP g) ≤
      relativeWeakClosure S.QG (S.tiP g) (S.QG ⊔ S.tiP g) :=
    le_iSup_of_le (⟨x, hx⟩ : S.QG) (le_iSup_of_le hle le_rfl)
  exact hW hmem

theorem conj_conj_eq {p y r : G} (hp : p ∈ S.M) (hy : y ∈ S.QG) (hr : r ∈ S.QG)
    (hpr : p * r = r * p) :
    p * y * p⁻¹ * r * (p * y * p⁻¹)⁻¹ = y * r * y⁻¹ := by
  have hpz : p * S.z = S.z * p := S.mem_M_iff.mp hp
  have hrp : p⁻¹ * r * p = r := by
    calc p⁻¹ * r * p = p⁻¹ * (p * r) := by rw [mul_assoc, hpr]
      _ = r := by group
  have hconj : p * y * p⁻¹ * r * (p * y * p⁻¹)⁻¹ = p * (y * r * y⁻¹) * p⁻¹ := by
    calc p * y * p⁻¹ * r * (p * y * p⁻¹)⁻¹ = p * (y * (p⁻¹ * r * p) * y⁻¹) * p⁻¹ := by group
      _ = p * (y * r * y⁻¹) * p⁻¹ := by rw [hrp]
  rw [hconj]
  rcases S.commutator_eq_one_or_z hy hr with h | h
  · have h1 : y * r * y⁻¹ = r := by
      calc y * r * y⁻¹ = y * r * y⁻¹ * r⁻¹ * r := by group
        _ = r := by rw [h, one_mul]
    rw [h1]
    calc p * r * p⁻¹ = r * p * p⁻¹ := by rw [hpr]
      _ = r := by group
  · have h1 : y * r * y⁻¹ = S.z * r := by
      calc y * r * y⁻¹ = y * r * y⁻¹ * r⁻¹ * r := by group
        _ = S.z * r := by rw [h]
    rw [h1]
    calc p * (S.z * r) * p⁻¹ = (p * S.z) * r * p⁻¹ := by group
      _ = S.z * (p * r) * p⁻¹ := by rw [hpz]; group
      _ = S.z * r := by rw [hpr]; group

theorem commutator_commute_of_mem_tiR (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g : G}
    (hgM : g ∉ S.M) {x p r : G} (hx : x ∈ S.QG) (hp : p ∈ S.tiP g) (hr : r ∈ S.tiR g) :
    x * p * x⁻¹ * p⁻¹ * r = r * (x * p * x⁻¹ * p⁻¹) := by
  have hpr : p * r = r * p := (commute_of_mem_tiR_of_mem_tiP S hTI hgM hr hp).symm
  have h := conj_conj_eq S hp.2 (S.QG.inv_mem hx) hr.1 hpr
  rw [inv_inv] at h
  calc x * p * x⁻¹ * p⁻¹ * r
      = x * (p * x⁻¹ * p⁻¹ * r * (p * x⁻¹ * p⁻¹)⁻¹) * x⁻¹ * (x * p * x⁻¹ * p⁻¹) := by group
    _ = x * (x⁻¹ * r * x) * x⁻¹ * (x * p * x⁻¹ * p⁻¹) := by rw [h]
    _ = r * (x * p * x⁻¹ * p⁻¹) := by group

theorem relativeWeakClosure_le (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g : G}
    (hgM : g ∉ S.M) :
    relativeWeakClosure S.QG (S.tiP g) (S.QG ⊔ S.tiP g) ≤
      (S.QG ⊓ centralizer (S.tiR g : Set G)) ⊔ S.tiP g := by
  refine iSup_le fun x => iSup_le fun _ => ?_
  rintro _ ⟨p, hp, rfl⟩
  have h : x.1 * p * x.1⁻¹ = x.1 * p * x.1⁻¹ * p⁻¹ * p := by group
  change x.1 * p * x.1⁻¹ ∈ _
  rw [h]
  refine mul_mem (mem_sup_left ⟨commutator_mem_QG S x.2 hp.2, ?_⟩) (mem_sup_right hp)
  exact mem_centralizer_iff.mpr fun r hr =>
    (commutator_commute_of_mem_tiR S hTI hgM x.2 hp hr).symm

theorem false_of_relativeWeakClosure_eq (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M)
    {g : G} (hgM : g ∉ S.M) (hgz : g * S.z * g⁻¹ ∈ S.M)
    (h : relativeWeakClosure S.QG (S.tiP g) (S.QG ⊔ S.tiP g) = S.tiP g) : False := by
  apply not_QG_le_tiR S hgM hgz
  intro x hx
  have ht := t_mem_tiP S hgz
  have h1 : x * (g * S.z * g⁻¹) * x⁻¹ ∈ S.tiP g := h ▸ conj_mem_relativeWeakClosure S hx ht
  have h2 := eq_one_of_mem_tiP_of_mem_QG S hTI hgM ((S.tiP g).mul_mem h1 ((S.tiP g).inv_mem ht))
    (commutator_mem_QG S hx hgz)
  refine ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩
  calc x * (g * S.z * g⁻¹)
      = x * (g * S.z * g⁻¹) * x⁻¹ * (g * S.z * g⁻¹)⁻¹ * ((g * S.z * g⁻¹) * x) := by group
    _ = g * S.z * g⁻¹ * x := by rw [h2, one_mul]

variable [Finite G]

theorem eight_le_card_tiR (hn : 3 ≤ S.width) {g : G} (hgz : g * S.z * g⁻¹ ∈ S.M) :
    8 ≤ Nat.card (S.tiR g) := by
  have hxx : g * S.z * g⁻¹ * (g * S.z * g⁻¹) = 1 := by
    rw [show g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ by group, S.z_mul_z]
    group
  have h1 := S.two_pow_width_le_card_centralizer hgz hxx
  have h2 : 2 ^ 3 ≤ 2 ^ S.width := Nat.pow_le_pow_right (by norm_num) hn
  exact le_trans (by norm_num) (h2.trans h1)

theorem exists_mem_tiR_ne (hn : 3 ≤ S.width) {g : G} (hgz : g * S.z * g⁻¹ ∈ S.M) :
    ∃ r ∈ S.tiR g, r ≠ 1 ∧ r ≠ S.z := by
  by_contra h
  push Not at h
  have hsub : (S.tiR g : Set G) ⊆ {1, S.z, 1, S.z} := by
    intro r hr
    by_cases hr1 : r = 1
    · exact Or.inl hr1
    · exact Or.inr (Or.inl (h r hr hr1))
  have h4 := card_le_four_of_subset hsub
  have h8 := eight_le_card_tiR S hn hgz
  have h2 : ({1, S.z, 1, S.z} : Set G) = {1, S.z} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have h3 := Set.ncard_le_ncard (h2 ▸ hsub) (Set.toFinite _)
  have h5 : ({1, S.z} : Set G).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  have hcard : Nat.card (S.tiR g) = (S.tiR g : Set G).ncard := Nat.card_coe_set_eq _
  omega

theorem false_of_isCyclic (hn : 3 ≤ S.width) (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M)
    {g : G} (hgM : g ∉ S.M) (hgz : g * S.z * g⁻¹ ∈ S.M) (h : IsCyclic (S.tiP g)) : False := by
  have hexp : Monoid.exponent (S.tiP g) ∣ 4 := Monoid.exponent_dvd_of_forall_pow_eq_one
    fun x => Subtype.ext (by simpa using (S.conjBy g).pow_four_eq_one x.2.1)
  rw [IsCyclic.exponent_eq_card] at hexp
  have h4 : Nat.card (S.tiP g) ≤ 4 := Nat.le_of_dvd (by norm_num) hexp
  have := card_tiR_eq_card_tiP S hTI hgM hgz
  have := eight_le_card_tiR S hn hgz
  omega

theorem false_of_relIndex_eq_two (hn : 3 ≤ S.width)
    (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g : G} (hgM : g ∉ S.M)
    (hgz : g * S.z * g⁻¹ ∈ S.M)
    (h : (relativeWeakClosure S.QG (S.tiP g) (S.QG ⊔ S.tiP g)).relIndex
      (S.QG ⊔ S.tiP g) = 2) : False := by
  set P := S.tiP g with hPdef
  set C := S.QG ⊓ centralizer (S.tiR g : Set G) with hCdef
  have hdvd := Subgroup.relIndex_dvd_of_le_left (S.QG ⊔ P) (relativeWeakClosure_le S hTI hgM)
  rw [h] at hdvd
  have hle2 : (C ⊔ P).relIndex (S.QG ⊔ P) ≤ 2 := Nat.le_of_dvd two_pos hdvd
  have hPnC : P ≤ normalizer (C : Set G) := by
    intro p hp
    rw [mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      refine ⟨S.conj_mem_QG hp.2 hc.1, mem_centralizer_iff.mpr fun r hr => ?_⟩
      have hpr := commute_of_mem_tiR_of_mem_tiP S hTI hgM hr hp
      have hcr := mem_centralizer_iff.mp hc.2 r hr
      calc r * (p * c * p⁻¹) = p * (p⁻¹ * (r * p) * c) * p⁻¹ := by group
        _ = p * (r * c) * p⁻¹ := by rw [hpr]; group
        _ = p * (c * r) * p⁻¹ := by rw [hcr]
        _ = p * c * p⁻¹ * (p * r * p⁻¹) := by group
        _ = p * c * p⁻¹ * r := by rw [← hpr]; group
    · intro hc
      have hpinv : p⁻¹ ∈ S.M := S.M.inv_mem hp.2
      have hc' : c = p⁻¹ * (p * c * p⁻¹) * p⁻¹⁻¹ := by group
      refine ⟨by rw [hc']; exact S.conj_mem_QG hpinv hc.1, mem_centralizer_iff.mpr fun r hr => ?_⟩
      have hpr := commute_of_mem_tiR_of_mem_tiP S hTI hgM hr hp
      have hcr := mem_centralizer_iff.mp hc.2 r hr
      calc r * c = p⁻¹ * ((p * r * p⁻¹) * (p * c * p⁻¹)) * p := by group
        _ = p⁻¹ * (r * (p * c * p⁻¹)) * p := by rw [← hpr]; group
        _ = p⁻¹ * ((p * c * p⁻¹) * r) * p := by rw [hcr]
        _ = c * (p⁻¹ * r * p) := by group
        _ = c * r := by rw [mul_assoc p⁻¹, hpr]; group
  have hCPbot : C ⊓ P = ⊥ := by
    rw [eq_bot_iff, ← tiP_inf_QG S hTI hgM, inf_comm]
    exact inf_le_inf_left _ inf_le_left
  have hQPbot : S.QG ⊓ P = ⊥ := by rw [inf_comm]; exact tiP_inf_QG S hTI hgM
  have hcCP := AschbacherTheorem3.card_sup_of_le_normalizer hPnC hCPbot
  have hcQP :=
    AschbacherTheorem3.card_sup_of_le_normalizer (tiP_le_normalizer S g) hQPbot
  have hmul := Subgroup.relIndex_mul_card (C ⊔ P) (S.QG ⊔ P)
  rw [inf_eq_left.mpr (sup_le_sup_right inf_le_left P), hcCP, hcQP] at hmul
  have hPpos : 0 < Nat.card P := Nat.card_pos
  have hQC : Nat.card S.QG ≤ 2 * Nat.card C := by
    have h1 : Nat.card S.QG * Nat.card P ≤ 2 * Nat.card C * Nat.card P := by
      rw [← hmul, mul_assoc]
      exact Nat.mul_le_mul_right _ hle2
    exact Nat.le_of_mul_le_mul_right h1 hPpos
  obtain ⟨r₀, hr₀R, hr₀1, hr₀z⟩ := exists_mem_tiR_ne S hn hgz
  have hCD : C ≤ S.QG ⊓ centralizer ({r₀} : Set G) := fun c hc =>
    ⟨hc.1, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc.2 r₀ hr₀R).symm⟩
  have hD2 := S.relIndex_centralizer_eq_two hr₀R.1 hr₀1 hr₀z
  have hDcard : Nat.card S.QG = 2 * Nat.card ↥(S.QG ⊓ centralizer ({r₀} : Set G)) := by
    have h1 := Subgroup.relIndex_mul_card (S.QG ⊓ centralizer ({r₀} : Set G)) S.QG
    rw [inf_eq_left.mpr inf_le_left, hD2] at h1
    omega
  have hCeq : C = S.QG ⊓ centralizer ({r₀} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hCD (by omega)
  have hsub : (S.tiR g : Set G) ⊆ {1, S.z, r₀, r₀ * S.z} := by
    intro r hr
    have hrC : r ∈ S.QG ⊓ centralizer ((S.QG ⊓ centralizer ({r₀} : Set G) : Subgroup G) :
        Set G) := by
      refine ⟨hr.1, mem_centralizer_iff.mpr fun d hd => ?_⟩
      rw [← hCeq] at hd
      exact (mem_centralizer_iff.mp hd.2 r hr).symm
    rcases (S.mem_centralizer_centralizer_iff hr₀R.1).mp hrC with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have h4 := card_le_four_of_subset hsub
  have h8 := eight_le_card_tiR S hn hgz
  omega

end AschTI

end CFSG.LargeExtraspecial
