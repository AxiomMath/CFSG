module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalOuter
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBActionKernel
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasASplit

public section

namespace CFSG.ComponentClassification.M12Cover

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

private theorem exists_conj_of_index_two {H : Type*} [Group H] {L : Subgroup H}
    (hidx : L.index = 2) {p y : H} (hpL : p ∉ L) (hy : IsConj p y) :
    ∃ l : L, (l : H) * p * (l : H)⁻¹ = y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hy
  by_cases hgL : g ∈ L
  · exact ⟨⟨g, hgL⟩, hg⟩
  · have hmem : g * p⁻¹ ∈ L := by
      rw [mul_mem_iff_of_index_two hidx]
      simp [hgL, hpL]
    refine ⟨⟨g * p⁻¹, hmem⟩, ?_⟩
    rw [← hg]
    group

section Fixed

variable {H : Type*} [Group H] [Finite H] {L : Subgroup H} [L.Normal] {t : L}

omit [Finite H] in
theorem map_centralizer_eq_commutator_fixSub [Group.IsPerfect L] (ht : orderOf t = 2)
    (hZ : center L = zpowers t) (π : L →* NativeSporadic.M12) (hπ : Function.Surjective π)
    (hker : π.ker = zpowers t) (hCL : centralizer (L : Set H) = zpowers (t : H))
    (hidx : L.index = 2) {p : H} (hpL : p ∉ L) (hp : orderOf p = 2)
    (hconj : IsConj p ((t : H) * p)) (α : MulAut NativeSporadic.M12)
    (hα : ∀ l : L, α (π l) = π (MulAut.conjNormal p l)) :
    (∃ g : NativeSporadic.M12, α = MulAut.conj g * beta * (MulAut.conj g)⁻¹) ∧
      ((centralizer {p}).subgroupOf L).map π = ⁅fixSub α, fixSub α⁆ := by
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have htH : (t : H) ∈ center H := CentralCover.coe_mem_center_of_center_eq_zpowers hZ ht2
  have hkerZ : π.ker = center L := hker.trans hZ.symm
  have hCL' : centralizer (L : Set H) ≤ L := by
    rw [hCL, zpowers_le]
    exact t.2
  have hθ : CentralCover.fullAction π hπ hkerZ p = α := by
    ext q
    obtain ⟨l, rfl⟩ := hπ q
    rw [CentralCover.fullAction_apply, hα]
  have hα2 : orderOf α = 2 := hθ ▸ CentralCover.orderOf_fullAction π hπ hkerZ hCL' hpL hp
  have hαo : α ∉ inner NativeSporadic.M12 :=
    hθ ▸ CentralCover.fullAction_notMem_inner π hπ hkerZ hCL' hpL
  obtain ⟨g, hg⟩ := exists_conj_beta_of_outer hα2 hαo
  refine ⟨⟨g, hg⟩, ?_⟩
  obtain ⟨l, hl⟩ := exists_conj_of_index_two hidx hpL hconj
  have hF : FixedCommutingProduct.fixedSubgroup α = fixSub α := rfl
  obtain ⟨δ, hδs, hδk⟩ : ∃ δ : FixedCommutingProduct.fixedSubgroup α →* zpowers (t : H),
      Function.Surjective δ ∧ δ.ker.map (FixedCommutingProduct.fixedSubgroup α).subtype =
        ((centralizer {p}).subgroupOf L).map π :=
    ⟨_, CentralCover.fixedLiftObstruction_surjective_of_conj π hπ hker htH p α hα hl,
      CentralCover.map_ker_fixedLiftObstruction π hπ hker htH p α hα⟩
  have hcardF : Nat.card (FixedCommutingProduct.fixedSubgroup α) = 120 := by
    rw [hF, hg]
    exact card_fixSub_conj_beta g
  have hcardT : Nat.card (zpowers (t : H)) = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht]
  have hcardK : Nat.card δ.ker = 60 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective δ hδs).toEquiv, hcardF,
      hcardT] at h1
    omega
  have hle : ⁅FixedCommutingProduct.fixedSubgroup α, FixedCommutingProduct.fixedSubgroup α⁆ ≤
      δ.ker.map (FixedCommutingProduct.fixedSubgroup α).subtype := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.map_mono (Abelianization.commutator_subset_ker δ)
  have heq : δ.ker.map (FixedCommutingProduct.fixedSubgroup α).subtype =
      ⁅FixedCommutingProduct.fixedSubgroup α, FixedCommutingProduct.fixedSubgroup α⁆ := by
    symm
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcardK, hF, hg,
      commutator_fixSub_conj_beta, card_fixedD_map_conj]
  rw [← hδk, heq, hF]

omit [Finite H] in
theorem ctss_m12_central_double_cover_conjugate_lifts_have_exact_fixed_quotient
    (hLq : CFSG.Assembly.IsQuasisimple L) (ht : orderOf t = 2) (hZ : center L = zpowers t)
    (π : L →* NativeSporadic.M12) (hπ : Function.Surjective π) (hker : π.ker = zpowers t)
    (hCL : centralizer (L : Set H) = zpowers (t : H)) (hidx : L.index = 2) {p : H}
    (hpL : p ∉ L) (hp : orderOf p = 2) (hconj : IsConj p ((t : H) * p))
    (α : MulAut NativeSporadic.M12) (hα : ∀ l : L, α (π l) = π (MulAut.conjNormal p l)) :
    ((centralizer {p}).subgroupOf L).map π = ⁅fixSub α, fixSub α⁆ ∧
    Nat.card ((centralizer {p}).subgroupOf L) = 120 ∧
    (π.comp ((centralizer {p}).subgroupOf L).subtype).ker =
      (zpowers t).subgroupOf ((centralizer {p}).subgroupOf L) ∧
    (∃ e : (centralizer {p}).subgroupOf L ⧸ (π.comp ((centralizer {p}).subgroupOf L).subtype).ker
        ≃* (⁅fixSub α, fixSub α⁆ : Subgroup NativeSporadic.M12),
      ∀ u : (centralizer {p}).subgroupOf L,
        (e (QuotientGroup.mk u) : NativeSporadic.M12) = π u) ∧
    (∃ g : NativeSporadic.M12, α = MulAut.conj g * beta * (MulAut.conj g)⁻¹) ∧
    (∀ g : NativeSporadic.M12, α = MulAut.conj g * beta * (MulAut.conj g)⁻¹ →
      ⁅fixSub α, fixSub α⁆ = fixedD.map (MulAut.conj g).toMonoidHom ∧
      ∃ e : (centralizer {p}).subgroupOf L ⧸
          (π.comp ((centralizer {p}).subgroupOf L).subtype).ker ≃* alternatingGroup (Fin 5),
        ∀ (u : (centralizer {p}).subgroupOf L) (d : fixedD),
          (d : NativeSporadic.M12) = g⁻¹ * π u * g → e (QuotientGroup.mk u) = fivePointEquiv d) ∧
    ⁅⁅fixSub α, fixSub α⁆, ⁅fixSub α, fixSub α⁆⁆ = ⁅fixSub α, fixSub α⁆ ∧
    Nat.card (⁅fixSub α, fixSub α⁆ : Subgroup NativeSporadic.M12) = 60 ∧
    Nat.card (Outer (⁅fixSub α, fixSub α⁆ : Subgroup NativeSporadic.M12)) ∣ 2 ∧
    ∀ θ : H →* MulAut NativeSporadic.M12,
      (∀ (h : H) (l : L), θ h (π l) = π (MulAut.conjNormal h l)) → θ.ker = zpowers (t : H) := by
  have : Group.IsPerfect L := Group.isPerfect_def.2 hLq.1
  obtain ⟨⟨g, hg⟩, hmap⟩ := map_centralizer_eq_commutator_fixSub ht hZ π hπ hker hCL hidx hpL
    hp hconj α hα
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have htH : (t : H) ∈ center H := CentralCover.coe_mem_center_of_center_eq_zpowers hZ ht2
  have htK : t ∈ (centralizer {p}).subgroupOf L := by
    rw [mem_subgroupOf, mem_centralizer_singleton_iff]
    exact (mem_center_iff.mp htH p).symm
  have hkerρ : (π.comp ((centralizer {p}).subgroupOf L).subtype).ker =
      (zpowers t).subgroupOf ((centralizer {p}).subgroupOf L) := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, ← MonoidHom.mem_ker, hker,
      mem_subgroupOf]
  have hrange : (π.comp ((centralizer {p}).subgroupOf L).subtype).range = ⁅fixSub α, fixSub α⁆ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  have hC' : ⁅fixSub α, fixSub α⁆ = fixedD.map (MulAut.conj g).toMonoidHom := by
    rw [hg]
    exact commutator_fixSub_conj_beta g
  have hcardC' : Nat.card (⁅fixSub α, fixSub α⁆ : Subgroup NativeSporadic.M12) = 60 := by
    rw [hC']
    exact card_fixedD_map_conj g
  let e : (centralizer {p}).subgroupOf L ⧸ (π.comp ((centralizer {p}).subgroupOf L).subtype).ker
      ≃* (⁅fixSub α, fixSub α⁆ : Subgroup NativeSporadic.M12) :=
    (QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr hrange)
  have he : ∀ u : (centralizer {p}).subgroupOf L,
      (e (QuotientGroup.mk u) : NativeSporadic.M12) = π u := fun u => rfl
  have hcardK : Nat.card ((centralizer {p}).subgroupOf L) = 120 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (π.comp ((centralizer {p}).subgroupOf L).subtype).ker
    rw [Nat.card_congr e.toEquiv, hcardC', hkerρ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_le.2 htK)).toEquiv,
      Nat.card_zpowers, ht] at h1
    exact h1
  refine ⟨hmap, hcardK, hkerρ, ⟨e, he⟩, ⟨g, hg⟩, fun g' hg' => ?_, ?_, hcardC', ?_, ?_⟩
  · have hC'' : ⁅fixSub α, fixSub α⁆ = fixedD.map (MulAut.conj g').toMonoidHom := by
      rw [hg']
      exact commutator_fixSub_conj_beta g'
    refine ⟨hC'', e.trans ((MulEquiv.subgroupCongr hC'').trans
      ((conjFixedDEquiv g').trans fivePointEquiv)), fun u d hd => ?_⟩
    simp only [MulEquiv.trans_apply]
    congr 1
    apply Subtype.ext
    have h1 := conj_conjFixedDEquiv g' (MulEquiv.subgroupCongr hC'' (e (QuotientGroup.mk u)))
    have h2 : ((MulEquiv.subgroupCongr hC'' (e (QuotientGroup.mk u)) :
        fixedD.map (MulAut.conj g').toMonoidHom) : NativeSporadic.M12) = π u := he u
    rw [hd, ← h2, ← h1]
    group
  · rw [hC']
    exact fixedD_map_conj_perfect g
  · rw [hC']
    exact card_outer_fixedD_map_conj_dvd g
  · intro θ hθ
    rw [CentralCover.fullAction_unique π hπ (hker.trans hZ.symm) θ hθ, CentralCover.ker_fullAction,
      hCL]

theorem ctss_m12_central_double_cover_external_fixed_section_frontier
    (hLq : CFSG.Assembly.IsQuasisimple L) (ht : orderOf t = 2) (hZ : center L = zpowers t)
    (π : L →* NativeSporadic.M12) (hπ : Function.Surjective π) (hker : π.ker = zpowers t)
    (hCL : centralizer (L : Set H) = zpowers (t : H)) (hidx : L.index = 2) {p : H}
    (hpL : p ∉ L) (hp : orderOf p = 2) (hconj : IsConj p ((t : H) * p))
    (α : MulAut NativeSporadic.M12) (hα : ∀ l : L, α (π l) = π (MulAut.conjNormal p l)) :
    (∃ σ : (⁅fixSub α, fixSub α⁆ : Subgroup NativeSporadic.M12) →* (centralizer {p}).subgroupOf L,
      ∀ q, π (σ q) = q) ∧
    ⁅fixSub α, fixSub α⁆.comap π = (centralizer {p}).subgroupOf L ∧
    zpowers t ⊔ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ =
      (centralizer {p}).subgroupOf L ∧
    zpowers t ⊓ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ = ⊥ ∧
    t ∈ center L ∧
    (∃ e : (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ : Subgroup L) ≃*
        (⁅fixSub α, fixSub α⁆ : Subgroup NativeSporadic.M12),
      (∀ a, (e a : NativeSporadic.M12) = π a) ∧
      ∃ σ : (⁅fixSub α, fixSub α⁆ : Subgroup NativeSporadic.M12) →* (centralizer {p}).subgroupOf L,
        (∀ q, (σ q : L) = e.symm q) ∧ ∀ q, π (σ q) = q) ∧
    Nat.card (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ : Subgroup L) = 60 ∧
    π.ker ⊓ (centralizer {p}).subgroupOf L = zpowers t ∧
    ∀ x : L, π x ∈ ⁅fixSub α, fixSub α⁆ → orderOf (π x) = 2 → orderOf x = 2 := by
  have : Group.IsPerfect L := Group.isPerfect_def.2 hLq.1
  obtain ⟨⟨g, hg⟩, hmap⟩ := map_centralizer_eq_commutator_fixSub ht hZ π hπ hker hCL hidx hpL
    hp hconj α hα
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have htH : (t : H) ∈ center H := CentralCover.coe_mem_center_of_center_eq_zpowers hZ ht2
  have htZ : t ∈ center L := by
    rw [hZ]
    exact mem_zpowers t
  have htK : t ∈ (centralizer {p}).subgroupOf L := by
    rw [mem_subgroupOf, mem_centralizer_singleton_iff]
    exact (mem_center_iff.mp htH p).symm
  have hkerK : π.ker ≤ (centralizer {p}).subgroupOf L := by
    rw [hker, zpowers_le]
    exact htK
  have hRK : ⁅fixSub α, fixSub α⁆.comap π = (centralizer {p}).subgroupOf L := by
    rw [← hmap, Subgroup.comap_map_eq, sup_eq_left.2 hkerK]
  obtain ⟨hD, hDD, -, hz2, hzc, -, hW, hWD, -, -, -, -, hWsq, -, hP, hinv, -, hh⟩ :=
    fusionData_pinned.map (MulAut.conj g)
  rw [← hg] at hD
  rw [hD] at hDD hzc hWD hP hinv
  obtain ⟨P, hPW⟩ := hP
  have hrD : (MulAut.conj g) elemR ∈ ⁅fixSub α, fixSub α⁆ :=
    hWD (by rw [hW]; exact subset_closure (Set.mem_insert _ _))
  obtain ⟨⟨hinf, hsup, -, -⟩, ⟨e, he, σ, hσ, hσπ⟩, hlifts⟩ :=
    CentralCover.central_double_cover_splits_over_perfect_factor_from_involution_fusion π hπ hker
      ht htZ (Subgroup.isPerfect_iff.2 hDD) P
      (fun w hw => by
        rw [hPW, mem_subgroupOf] at hw
        exact Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hWsq _ hw))
      hrD (fun q hq hq2 => by
        obtain ⟨d, hd, hqd⟩ := hinv q hq hq2
        exact ⟨d, hd, hqd.symm⟩) hzc hz2 ⟨_, hh⟩
  rw [hRK] at hinf hsup
  have hRR : ⁅⁅fixSub α, fixSub α⁆.comap π, ⁅fixSub α, fixSub α⁆.comap π⁆ =
      ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ := by
    rw [hRK]
  have hσπ' : ∀ q, π (σ q) = q := fun q => congrArg (fun f => (f q : NativeSporadic.M12)) hσπ
  let e' := (MulEquiv.subgroupCongr hRR).symm.trans e
  let σ' := (Subgroup.inclusion hRK.le).comp σ
  have hcard : Nat.card (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ :
      Subgroup L) = 60 := by
    rw [Nat.card_congr e'.toEquiv, ← hD, card_fixedD_map_conj]
  refine ⟨⟨σ', hσπ'⟩, hRK, hsup, hinf, htZ, ⟨e', fun a => he _, σ', fun q => hσ q, hσπ'⟩, hcard,
    by rw [inf_eq_left.2 hkerK, hker], hlifts⟩

end Fixed

end CFSG.ComponentClassification.M12Cover
