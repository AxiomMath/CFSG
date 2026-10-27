module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CentralizerCard
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CentralizerA6

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.RankThree.PartTwo.KFacts.K426 CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

theorem center_alt6_eq_bot : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 6))) with h | h
  · exact h
  · exfalso
    let g1 : alternatingGroup (Fin 6) :=
      ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
    let g2 : alternatingGroup (Fin 6) :=
      ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
    have hmem : g1 ∈ Subgroup.center (alternatingGroup (Fin 6)) := by rw [h]; exact mem_top _
    have hc := Subgroup.mem_center_iff.1 hmem g2
    have hne : g1 * g2 ≠ g2 * g1 := by decide +kernel
    exact hne hc.symm

theorem center_eq_bot_of_equiv_alt6 {S : Type*} [Group S] (I : Subgroup S)
    (e : ↥I ≃* alternatingGroup (Fin 6)) : Subgroup.center ↥I = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro t ht
  have h1 : e t ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨u, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 ht u]
  rw [center_alt6_eq_bot, Subgroup.mem_bot] at h1
  exact e.injective (h1.trans (map_one e).symm)

theorem card_mul_le_card_sup_of_disjoint {G : Type*} [Group G] [Finite G] (M K : Subgroup G)
    (h : Disjoint M K) : Nat.card M * Nat.card K ≤ Nat.card ↥(M ⊔ K) := by
  classical
  let f : M × K → ↥(M ⊔ K) := fun p =>
    ⟨(p.1 : G) * (p.2 : G),
      Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨m, k⟩ ⟨m', k'⟩ hmk
    have h1 : (m : G) * k = m' * k' := congrArg Subtype.val hmk
    have h2 : (m' : G)⁻¹ * m = k' * (k : G)⁻¹ := by
      calc (m' : G)⁻¹ * m = (m' : G)⁻¹ * (m * k) * (k : G)⁻¹ := by group
        _ = (m' : G)⁻¹ * (m' * k') * (k : G)⁻¹ := by rw [h1]
        _ = k' * (k : G)⁻¹ := by group
    have hmM : (m' : G)⁻¹ * m ∈ M := M.mul_mem (M.inv_mem m'.2) m.2
    have hkK : (m' : G)⁻¹ * m ∈ K := h2 ▸ K.mul_mem k'.2 (K.inv_mem k.2)
    have h0 : (m' : G)⁻¹ * m = 1 := by
      exact Subgroup.disjoint_def.1 h hmM hkK
    have hm : (m : G) = m' := by
      calc (m : G) = m' * ((m' : G)⁻¹ * m) := by group
        _ = m' := by rw [h0, mul_one]
    have hk : (k : G) = k' := by
      have := h1
      rw [hm] at this
      exact mul_left_cancel this
    exact Prod.ext (Subtype.ext hm) (Subtype.ext hk)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at this

section Main

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000 in
theorem centralizer_structure_J3Cover {X : Type} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) (hZ3 : Nat.card (center X) = 3)
    (e : X ⧸ center X ≃* NativeSporadic.J3) {a : X} (ha : a ∉ center X)
    (ha3 : a ^ 3 ∈ center X)
    (h5 : 5 ∣ Nat.card (centralizer ({e (a : X ⧸ center X)} : Set NativeSporadic.J3))) :
    ∃ I : Subgroup X, I ≤ centralizer ({a} : Set X) ∧ ⁅I, I⁆ = I ∧
      Nonempty (↥I ≃* alternatingGroup (Fin 6)) ∧
      (∀ P' : Subgroup X, P' ≤ centralizer ({a} : Set X) → ⁅P', P'⁆ = P' → P' ≤ I) ∧
      Nat.card (centralizer ({a} : Set X)) = 3240 ∧
      Nat.card ↥(zpowers a ⊔ center X) = 9 ∧ Disjoint (zpowers a ⊔ center X) I ∧
      (∀ d ∈ zpowers a ⊔ center X, ∀ x ∈ centralizer ({a} : Set X), d * x = x * d) ∧
      zpowers a ⊔ center X ⊔ I = centralizer ({a} : Set X) := by
  obtain ⟨I, hIC, hIperf, ⟨eI⟩, hImax⟩ :=
    perfect_core_centralizer_J3Cover hX hZ3 e ha ha3 h5
  have hx3 : (a : X ⧸ center X) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 ha3
  have hx1 : (a : X ⧸ center X) ≠ 1 := fun h => ha ((QuotientGroup.eq_one_iff a).1 h)
  have hcQ : Nat.card (centralizer ({(a : X ⧸ center X)} : Set (X ⧸ center X))) = 1080 :=
    card_centralizer_of_equiv_J3 e hx3 hx1 h5
  clear h5 hx3 hx1
  set C : Subgroup X := centralizer ({a} : Set X) with hC
  set D : Subgroup X := zpowers a ⊔ center X with hD
  set π : X →* X ⧸ center X := QuotientGroup.mk' (center X) with hπ
  have hπapp : ∀ w : X, π w = (w : X ⧸ center X) := fun w => rfl
  have hπker : ∀ w : X, π w = 1 ↔ w ∈ center X := by
    intro w
    rw [hπapp, QuotientGroup.eq_one_iff]
  have hker : π.ker = center X := by
    ext w; rw [MonoidHom.mem_ker, hπker]
  have hZC : center X ≤ C := by
    intro z hz
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.1 hz a).symm
  have haC : a ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have hDcomm : ∀ d ∈ D, ∀ x ∈ C, d * x = x * d := by
    have hle : D ≤ centralizer (C : Set X) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro x hx
        exact (Subgroup.mem_centralizer_singleton_iff.1 hx)
      · intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro x _
        exact (Subgroup.mem_center_iff.1 hz x)
    intro d hd x hx
    exact (Subgroup.mem_centralizer_iff.1 (hle hd) x hx).symm
  have hDC : D ≤ C := sup_le (Subgroup.zpowers_le.2 haC) hZC
  have hπa3 : π a ^ 3 = 1 := by rw [← map_pow]; exact (hπker _).2 ha3
  have hπa1 : π a ≠ 1 := fun h => ha ((hπker a).1 h)
  have hπa : orderOf (π a) = 3 := orderOf_eq_prime hπa3 hπa1
  have hCle : Nat.card C ≤ 3240 := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥C →* X ⧸ center X, ∀ w : ↥C, ψ w = π w :=
      ⟨π.comp C.subtype, fun _ => rfl⟩
    have hkerψ : ψ.ker = (center X).subgroupOf C := by
      ext ⟨w, hw⟩
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ]
      exact hπker w
    have hk3 : Nat.card ψ.ker = 3 := by
      rw [hkerψ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv, hZ3]
    have hrange : ψ.range ≤ centralizer ({π a} : Set (X ⧸ center X)) := by
      rintro _ ⟨⟨w, hw⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hψ]
      have hw' : w * a = a * w := (Subgroup.mem_centralizer_singleton_iff.1 hw)
      rw [← map_mul, ← map_mul, hw']
    have hcentr : Nat.card (centralizer ({π a} : Set (X ⧸ center X))) = 1080 := by
      rw [hπapp a]; exact hcQ
    have hr : Nat.card ψ.range ≤ 1080 := by
      rw [← hcentr]; exact Subgroup.card_le_of_le hrange
    have := Subgroup.card_ker_mul_card_range ψ
    rw [hk3] at this
    omega
  have hD9 : Nat.card D = 9 := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥D →* X ⧸ center X, ψ = π.comp D.subtype := ⟨_, rfl⟩
    have hZD : center X ≤ D := le_sup_right
    have hkerψ : ψ.ker = (center X).subgroupOf D := by
      ext ⟨w, hw⟩
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ]
      exact hπker w
    have hk3 : Nat.card ψ.ker = 3 := by
      rw [hkerψ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv, hZ3]
    have hrange : ψ.range = zpowers (π a) := by
      rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype, hD, Subgroup.map_sup,
        MonoidHom.map_zpowers, (Subgroup.map_eq_bot_iff _).2 hker.ge, sup_bot_eq]
    have hr : Nat.card ψ.range = 3 := by
      rw [hrange, Nat.card_zpowers, hπa]
    have := Subgroup.card_ker_mul_card_range ψ
    rw [hk3, hr] at this
    omega
  have hDI : Disjoint D I := by
    rw [Subgroup.disjoint_def]
    intro t htD htI
    have hcen : (⟨t, htI⟩ : ↥I) ∈ Subgroup.center ↥I := by
      rw [Subgroup.mem_center_iff]
      intro i
      exact Subtype.ext (hDcomm t htD i (hIC i.2)).symm
    rw [center_eq_bot_of_equiv_alt6 I eI, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hI360 : Nat.card I = 360 := by
    rw [Nat.card_congr eI.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hlow : 3240 ≤ Nat.card ↥(D ⊔ I) := by
    have := card_mul_le_card_sup_of_disjoint D I hDI
    rw [hD9, hI360] at this
    exact this
  have hsup : D ⊔ I ≤ C := sup_le hDC hIC
  have hCeq : D ⊔ I = C := by
    refine Subgroup.eq_of_le_of_card_ge hsup ?_
    have := hCle
    omega
  have hC3240 : Nat.card C = 3240 := by
    have h1 := Subgroup.card_le_of_le hsup
    omega
  exact ⟨I, hIC, hIperf, ⟨eI⟩, hImax, hC3240, hD9, hDI, hDcomm, hCeq⟩

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
