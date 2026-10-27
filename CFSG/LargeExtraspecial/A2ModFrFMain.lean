module

public import CFSG.LargeExtraspecial.A2ModFrFGen
public import CFSG.LargeExtraspecial.A2ModSqueeze

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrF

open Module CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.ExclNS
  CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

section Collinear

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem finrank_commSpaceOf_sup_closure_le (hA : A2Action D Q ρ) {H : Subgroup X} {e : X}
    (he : e ∈ D) (heH : e ∈ H) (T : Finset X) (hT : ∀ t ∈ T, t ∈ D ∧ t * e ∈ D) :
    finrank (ZMod 2) (commSpaceOf ρ (H ⊔ Subgroup.closure (T : Set X))) ≤
      finrank (ZMod 2) (commSpaceOf ρ H) + T.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, Subgroup.closure_empty, sup_bot_eq, Finset.card_empty, add_zero]
  | insert a T ha ih =>
    have hT' : ∀ t ∈ T, t ∈ D ∧ t * e ∈ D := fun t ht => hT t (Finset.mem_insert_of_mem ht)
    have e1 : H ⊔ Subgroup.closure (↑(insert a T) : Set X) =
        H ⊔ Subgroup.closure (T : Set X) ⊔ Subgroup.zpowers a := by
      rw [Finset.coe_insert, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
        sup_comm (Subgroup.zpowers a), sup_assoc]
    rw [e1, Finset.card_insert_of_notMem ha]
    have h1 := hA.finrank_commSpaceOf_sup_zpowers_le_of_collinear
      (H := H ⊔ Subgroup.closure (T : Set X)) (hT a (Finset.mem_insert_self a T)).1 he
      (Subgroup.mem_sup_left heH) (hT a (Finset.mem_insert_self a T)).2
    have h2 := ih hT'
    omega

end Collinear

namespace F4Frame

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : F4Frame G R}

variable (F) in
noncomputable abbrev extra (c : F.K) : F.K := c * F.xL r2 * c⁻¹

variable (F) in
noncomputable abbrev extra' (c : F.K) : F.K :=
  (F.n 2 * F.n 3) * F.extra c * (F.n 2 * F.n 3)⁻¹

variable {D : Set G} (hR : IsRootClass R) (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d)
  (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
include hR hRD hDc

theorem map_extra_mem {c : F.K} (hc : c ∈ F.X a2v) :
    F.Ψ (F.extra c) ∈ D ∧ F.Ψ (F.extra c) * F.lr (-r1) ∈ D := by
  have hL2 := isLong_r2 (F := F)
  have hcom : Commute c (F.xL (-r1)) :=
    (commuting_neg_r1_a2v _ (xL_mem (isLong_r1 (F := F)).neg.mem_roots) _ hc).symm
  have hcoll : F.lr r2 * F.lr (-r1) ∈ D := by
    have e : r1 + r2 + -r1 = r2 := by decide
    have := mul_lr_mem (F := F) hR hRD hDc isLong_r1_add_r2 isLong_r1.neg
      (by rw [e]; exact hL2) (by rw [form_apply]; decide)
    rwa [e] at this
  refine ⟨?_, ?_⟩
  · rw [map_mul, map_mul, map_inv]
    exact hDc _ _ (lr_mem hR hRD hL2)
  · have e : F.extra c * F.xL (-r1) = c * (F.xL r2 * F.xL (-r1)) * c⁻¹ := by
      rw [extra, mul_assoc, mul_assoc, hcom.inv_left.eq]
      group
    rw [lr, ← map_mul, e, map_mul, map_mul, map_mul, map_inv]
    exact hDc _ _ hcoll

theorem map_extra'_mem {c : F.K} (hc : c ∈ F.X a2v) :
    F.Ψ (F.extra' c) ∈ D ∧ F.Ψ (F.extra' c) * F.lr (-r1) ∈ D := by
  obtain ⟨h1, h2⟩ := map_extra_mem hR hRD hDc hc
  have hfix : (F.n 2 * F.n 3) * F.xL (-r1) * (F.n 2 * F.n 3)⁻¹ = F.xL (-r1) := by
    rw [conj_xL hR hRD (actsAs_mw (F := F)) (isLong_r1 (F := F)).neg, weylAction_mul_apply,
      weylAction_simple_eq F.hA, weylAction_simple_eq F.hA,
      show reflF f4M 2 (reflF f4M 3 (-r1)) = -r1 by decide]
  refine ⟨?_, ?_⟩
  · rw [extra', map_mul, map_mul, map_inv]
    exact hDc _ _ h1
  · have e : F.extra' c * F.xL (-r1) =
        (F.n 2 * F.n 3) * (F.extra c * F.xL (-r1)) * (F.n 2 * F.n 3)⁻¹ := by
      conv_lhs => rw [← hfix]
      rw [extra']
      group
    have h2' : F.Ψ (F.extra c * F.xL (-r1)) ∈ D := by rw [map_mul]; exact h2
    rw [lr, ← map_mul, e, map_mul, map_mul, map_inv]
    exact hDc _ _ h2'

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {ρ : G →* (V ≃ₗ[ZMod 2] V)}

variable (F) in
theorem finrank_commSpaceOf_top_le [Finite G] (hiso : NoIsolated R) (hA : A2Action D Q ρ) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 7 + 2 * Nat.card (F.X a2v) := by
  classical
  obtain ⟨H₀, h9, hH₀⟩ := exists_finrank_commSpaceOf_le_nine hR hRD hiso hDc hA
  have : Finite (F.X a2v) := finite_rootGroup (a2v_mem_roots F.hA)
  set C : Finset F.K := ((Set.toFinite (F.X a2v : Set F.K)).toFinset).erase 1 with hC
  have hmemC : ∀ {c : F.K}, c ∈ C ↔ c ≠ 1 ∧ c ∈ F.X a2v := by
    intro c
    rw [hC, Finset.mem_erase, Set.Finite.mem_toFinset, SetLike.mem_coe]
  have hCcard : C.card + 1 = Nat.card (F.X a2v) := by
    rw [hC, Finset.card_erase_add_one (by rw [Set.Finite.mem_toFinset]; exact one_mem _),
      ← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    exact (Nat.card_coe_set_eq (F.X a2v : Set F.K)).symm
  set T : Finset G := C.image (fun c => F.Ψ (F.extra c)) ∪ C.image (fun c => F.Ψ (F.extra' c))
    with hTdef
  have hTcard : T.card ≤ 2 * C.card := by
    have h1 : T.card ≤ (C.image (fun c => F.Ψ (F.extra c))).card +
        (C.image (fun c => F.Ψ (F.extra' c))).card := Finset.card_union_le _ _
    have h2 := Finset.card_image_le (s := C) (f := fun c => F.Ψ (F.extra c))
    have h3 := Finset.card_image_le (s := C) (f := fun c => F.Ψ (F.extra' c))
    omega
  have hL1 := isLong_r1 (F := F)
  have he1 : F.lr (-r1) ∈ H₀ :=
    (hH₀ r1 (Or.inr (Or.inl rfl))).2 (Subgroup.mem_map_of_mem F.Ψ (xL_mem hL1.neg.mem_roots))
  have hT : ∀ t ∈ T, t ∈ D ∧ t * F.lr (-r1) ∈ D := by
    intro t ht
    rcases Finset.mem_union.1 ht with ht | ht
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ht
      exact map_extra_mem hR hRD hDc (hmemC.1 hc).2
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ht
      exact map_extra'_mem hR hRD hDc (hmemC.1 hc).2
  have hdim := finrank_commSpaceOf_sup_closure_le hA (lr_mem hR hRD hL1.neg) he1 T hT
  have htop : H₀ ⊔ Subgroup.closure (T : Set G) = ⊤ := by
    set H₁ := H₀ ⊔ Subgroup.closure (T : Set G)
    have hTH : ∀ t ∈ T, t ∈ H₁ := fun t ht =>
      Subgroup.mem_sup_right (Subgroup.subset_closure (Finset.mem_coe.2 ht))
    have hP : H₁.comap F.Ψ = ⊤ := by
      refine eq_top_of_le hR hRD (fun γ hγ => ?_) (fun c hc => ?_) (fun c hc => ?_)
      · obtain ⟨h1, h2⟩ := hH₀ γ hγ
        exact ⟨Subgroup.map_le_iff_le_comap.1 (h1.trans le_sup_left),
          Subgroup.map_le_iff_le_comap.1 (h2.trans le_sup_left)⟩
      · rw [Subgroup.mem_comap]
        by_cases hc1 : c = 1
        · subst hc1
          rw [one_mul, inv_one, mul_one]
          exact Subgroup.mem_sup_left ((hH₀ r2 (Or.inr (Or.inr (Or.inl rfl)))).1
            (Subgroup.mem_map_of_mem F.Ψ (xL_mem (isLong_r2 (F := F)).mem_roots)))
        · exact hTH _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨c, hmemC.2 ⟨hc1, hc⟩, rfl⟩))
      · rw [Subgroup.mem_comap]
        by_cases hc1 : c = 1
        · subst hc1
          have e : F.extra' 1 = F.xL r3 := by
            rw [extra', extra, one_mul, inv_one, mul_one,
              conj_xL hR hRD (actsAs_mw (F := F)) (isLong_r2 (F := F)),
              weylAction_mul_apply, weylAction_simple_eq F.hA, weylAction_simple_eq F.hA,
              show reflF f4M 2 (reflF f4M 3 r2) = r3 by decide]
          change F.Ψ (F.extra' 1) ∈ H₁
          rw [e]
          exact Subgroup.mem_sup_left ((hH₀ r3 (Or.inr (Or.inr (Or.inr rfl)))).1
            (Subgroup.mem_map_of_mem F.Ψ (xL_mem (isLong_r3 (F := F)).mem_roots)))
        · exact hTH _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨c, hmemC.2 ⟨hc1, hc⟩, rfl⟩))
    rw [eq_top_iff]
    intro g _
    obtain ⟨k, rfl⟩ := F.surj g
    have hk : k ∈ H₁.comap F.Ψ := by rw [hP]; exact Subgroup.mem_top k
    exact hk
  rw [htop] at hdim
  omega

variable (F) in
theorem false_of_a2Action [Finite G] (hiso : NoIsolated R) (hA : A2Action D Q ρ) {m p : ℕ}
    (hm : Nat.card (F.X a2v) ≤ m) (hp : p.Prime) (hp2 : p ≠ 2) (hpG : p ∣ Nat.card G)
    (hpj : ∀ j, 1 ≤ j → j ≤ 7 + 2 * m → ¬ p ∣ 2 ^ j - 1) : False := by
  have hdim := F.finrank_commSpaceOf_top_le hR hRD hDc hiso hA
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpG
  have h1 : ρ g = 1 := eq_one_of_pow_prime_of_finrank_commSpace_le hp hp2
    (by rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one])
    ((Submodule.finrank_mono (commSpace_le_commSpaceOf ρ (Subgroup.mem_top g))).trans
      (hdim.trans (by omega))) hpj
  have hg1 : g = 1 := hA.injective (h1.trans (map_one ρ).symm)
  rw [hg1, orderOf_one] at hg
  exact hp.one_lt.ne hg

end F4Frame

end CFSG.LargeExtraspecial.A2Mod.FrF
