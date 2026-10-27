module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Base

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Sporadic.SmallOddCore

theorem autModel_of_equiv {M : Type*} [Group M] {P R : Subgroup M} (hPR : P ≤ R)
    (e : ↥R ≃* MulAut P) (he : ∀ (x : ↥R) (p : P), ((e x p : P) : M) = (x : M) * p * (x : M)⁻¹) :
    AutModel P R where
  le := hPR
  conj_mem := fun x hx p hp => by
    have := (e ⟨x, hx⟩ ⟨p, hp⟩).2
    rwa [he] at this
  surj α := ⟨e.symm α, (e.symm α).2, fun p => by rw [← he, MulEquiv.apply_symm_apply]⟩
  inj x hx hc := by
    have h1 : e ⟨x, hx⟩ = 1 := MulEquiv.ext fun p => Subtype.ext (by
      rw [he, hc p p.2, mul_inv_cancel_right]
      rfl)
    have h2 : (⟨x, hx⟩ : R) = 1 := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val h2

theorem embed_mem_iff {M : Type*} [Group M] {P R : Subgroup M} (h : AutModel P R)
    {G : Type*} [Group G] {N : Subgroup G} [N.Normal] (hC : centralizer (N : Set G) = ⊥)
    (θ : N ≃* P) (g : G) : h.embed N θ g ∈ P ↔ g ∈ N := by
  constructor
  · intro hg
    have e : h.embed N θ g = h.embed N θ (θ.symm ⟨_, hg⟩ : G) := by
      rw [h.embed_coe, MulEquiv.apply_symm_apply]
    rw [h.embed_injective N θ hC e]
    exact (θ.symm _).2
  · intro hg
    rw [show g = ((⟨g, hg⟩ : N) : G) from rfl, h.embed_coe]
    exact (θ _).2

theorem conj_mem_iff {M : Type*} [Group M] {P : Subgroup M} {g : M} (hg : g ∈ P) (t : M) :
    g * t * g⁻¹ ∈ P ↔ t ∈ P := by
  constructor
  · intro h
    have := P.mul_mem (P.mul_mem (P.inv_mem hg) h) hg
    rwa [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at this
  · intro h
    exact P.mul_mem (P.mul_mem hg h) (P.inv_mem hg)

theorem coset_of_table {M : Type*} [Group M] {P R : Subgroup M} (hPR : P ≤ R) {ι : Type*}
    (rep : ι → M) (hcls : ∀ t ∈ R, orderOf t = 2 → ∃ i, ∃ g ∈ P, t = g * rep i * g⁻¹)
    (hinj : ∀ i j, (rep i ∈ P ↔ rep j ∈ P) → i = j) :
    ∀ t ∈ R, orderOf t = 2 → ∀ s ∈ P, orderOf (t * s) = 2 → ∃ c ∈ P, c⁻¹ * t * c = t * s := by
  intro t ht ht2 s hs hts
  obtain ⟨i, g, hg, rfl⟩ := hcls t ht ht2
  obtain ⟨j, g', hg', he⟩ := hcls _ (R.mul_mem ht (hPR hs)) hts
  have hij : i = j := by
    apply hinj
    rw [← conj_mem_iff hg, ← conj_mem_iff hg' (rep j), ← he]
    exact ⟨fun h => P.mul_mem h hs, fun h => by simpa using P.mul_mem h (P.inv_mem hs)⟩
  subst hij
  refine ⟨g * g'⁻¹, P.mul_mem hg (P.inv_mem hg'), ?_⟩
  rw [he]
  group

theorem coset_of_rep_outer {M : Type*} [Group M] {P R : Subgroup M} (hPR : P ≤ R) (u : M)
    (hcls : ∀ t ∈ R, t ∉ P → orderOf t = 2 → ∃ g ∈ P, t = g * u * g⁻¹) :
    ∀ t ∈ R, t ∉ P → orderOf t = 2 → ∀ s ∈ P, orderOf (t * s) = 2 →
      ∃ c ∈ P, c⁻¹ * t * c = t * s := by
  intro t ht htP ht2 s hs hts
  obtain ⟨g, hg, rfl⟩ := hcls t ht htP ht2
  have hn : g * u * g⁻¹ * s ∉ P := fun h => htP (by simpa using P.mul_mem h (P.inv_mem hs))
  obtain ⟨g', hg', he⟩ := hcls _ (R.mul_mem ht (hPR hs)) hn hts
  refine ⟨g * g'⁻¹, P.mul_mem hg (P.inv_mem hg'), ?_⟩
  rw [he]
  group

theorem false_of_inner_card {G : Type} [Group G] {N J : Subgroup G} {α : G} (hα : orderOf α = 2)
    (hαN : α ∈ N) (hJN : J ≤ N) (hJα : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G))))
    (hsmall : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 2 p f) ∨
      Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7)))
    (hcard : ∀ a : N, orderOf a = 2 → ∀ B : Subgroup N,
      Assembly.IsComponentOf B (centralizer ({a} : Set N)) → Nat.card (↥B ⧸ center ↥B) = 20160) :
    False := by
  obtain ⟨hle, hcomp⟩ := isComponent_inner hαN hJN hJα hJ
  have hc := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hle).2 hcomp
  have h := hcard ⟨α, hαN⟩ (by rw [Subgroup.orderOf_mk, hα]) _ hc
  exact not_small_of_card_20160
    ((card_quotient_center_congr (subgroupOfEquivOfLe hJN)).symm.trans h) hsmall

theorem false_of_inner_card' {G : Type} [Group G] {N J : Subgroup G} {α : G}
    (hα : orderOf α = 2) (hαN : α ∈ N) (hJN : J ≤ N) (hJα : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G))))
    (hsmall : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 2 p f) ∨
      Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7)))
    (hcard : ∀ a : N, orderOf a = 2 → ∀ B : Subgroup (centralizer ({a} : Set N)),
      IsComponent B → Nat.card (↥B ⧸ center ↥B) = 20160) :
    False := by
  obtain ⟨hle, hcomp⟩ := isComponent_inner hαN hJN hJα hJ
  have h := hcard ⟨α, hαN⟩ (by rw [Subgroup.orderOf_mk, hα]) _ hcomp
  exact not_small_of_card_20160 ((card_quotient_center_congr
    ((subgroupOfEquivOfLe hle).trans (subgroupOfEquivOfLe hJN))).symm.trans h) hsmall

end CFSG.ComponentClassification.GSThmB.CF23I
