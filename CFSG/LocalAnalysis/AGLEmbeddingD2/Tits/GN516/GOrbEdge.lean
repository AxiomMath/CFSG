module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbLeviRad
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbSmall
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParND
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbEdgeAux

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Edge

open scoped commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.Tits.GN516.Levi

variable {K S : Type} [Group K] [Finite K] [Group S] [Finite S] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* S} {M : ℕ}

@[expose] def EdgeLevi (D : UniversalRootDatum K) (u v : Fin D.rank) : Prop :=
  IsQuasisimpleTwoNonab ↥(twoResidual (rankOne D.rootGroup u ⊔ rankOne D.rootGroup v))

theorem quasisimpleModTwoNonab_of_edgeLevi (h : BorelQuotient D n H π M) {u v : Fin D.rank}
    (he : EdgeLevi D u v) : QuasisimpleModTwoNonab ↥(twoResidual ((unipJ D {u, v}).map π)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hct := h.ct
  have hext := h.extras
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos hext h.pGroup
  have hUpos : ∀ x ∈ unipRad D {u, v}, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hU2 ⟨x, unipRad_le_posUnipotent (D := D) {u, v} hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hN : unipJ D {u, v} =
      unipRad D {u, v} ⊔ (rankOne D.rootGroup u ⊔ rankOne D.rootGroup v) := by
    rw [unipJ_eq_sup hct hext, iSup_pair]
  have hL_norm : rankOne D.rootGroup u ⊔ rankOne D.rootGroup v ≤
      Subgroup.normalizer ((unipRad D {u, v} : Subgroup K) : Set K) :=
    sup_le ((rankOne_le_parJ (Set.mem_insert _ _)).trans (parJ_le_normalizer_unipRad hct hext _))
      ((rankOne_le_parJ (Set.mem_insert_of_mem _ (Set.mem_singleton _))).trans
        (parJ_le_normalizer_unipRad hct hext _))
  have he' : IsQuasisimpleTwoNonab ↥(twoResidual (rankOne D.rootGroup u ⊔ rankOne D.rootGroup v)) :=
    he
  set L : Subgroup K := rankOne D.rootGroup u ⊔ rankOne D.rootGroup v with hL
  set U : Subgroup K := unipRad D {u, v} with hU
  set E : Subgroup K := twoResidual L with hE
  have hLN : L ≤ unipJ D {u, v} := by
    rw [hN]
    exact le_sup_right
  have hEL : E ≤ L := twoResidual_le L
  have hLπV : L.map π ≤ Subgroup.normalizer ((U.map π : Subgroup S) : Set S) :=
    (Subgroup.map_mono (f := π) hL_norm).trans (Subgroup.le_normalizer_map π)
  have hPL : E.map π ≤ L.map π := Subgroup.map_mono (f := π) hEL
  have hLPn : L.map π ≤ Subgroup.normalizer ((E.map π : Subgroup S) : Set S) :=
    (Subgroup.map_mono (f := π) (le_normalizer_twoResidual L)).trans
      (Subgroup.le_normalizer_map π)
  have hP2 : ∀ x ∈ L.map π, ∃ k : ℕ, x ^ 2 ^ k ∈ E.map π := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient L l hl
    exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_map_of_mem π hk⟩
  have hV : ∀ x ∈ U.map π, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := hUpos y hy
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hW : U.map π ⊔ L.map π = (unipJ D {u, v}).map π := by
    rw [hN]
    exact (Subgroup.map_sup U L π).symm
  have hPT : E.map π ≤ twoResidual (U.map π ⊔ L.map π) := by
    rw [hW]
    exact (Subgroup.map_mono (f := π) (EdgeAux.twoResidual_mono_aux hLN)).trans
      (EdgeAux.map_twoResidual_le_aux π (unipJ D {u, v}))
  have hPq : IsQuasisimpleTwoNonab ↥(E.map π) := by
    let ψ : ↥E →* ↥(E.map π) :=
      (π.comp E.subtype).codRestrict (E.map π) (fun e => Subgroup.mem_map_of_mem π e.2)
    have hψ : Function.Surjective ψ := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨x, hx⟩, rfl⟩
    refine EdgeAux.isQuasisimpleTwoNonab_of_central_odd_image ψ hψ ?_ he'
    intro e he_ker
    have he1 : π (e : K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 he_ker)
    have hcK : (e : K) ∈ Subgroup.center K := h.ker_central _ (MonoidHom.mem_ker.2 he1)
    refine ⟨Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 hcK g), ?_⟩
    rw [← Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat h.odd
      (orderOf_dvd_of_pow_eq_one (h.ker_pow _ (MonoidHom.mem_ker.2 he1)))
  rw [← hW]
  exact EdgeAux.quasisimpleModTwoNonab_of_factor hV hLπV hPL hLPn hP2 hPT hPq

theorem quasisimpleModTwoNonab_of_simple {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hs : IsSimpleGroup ↥L)
    (hQ : ∃ Q : Subgroup ↥L, IsPGroup 2 Q ∧ ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) :
    QuasisimpleModTwoNonab ↥(twoResidual (pElementSubgroup 2 L)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hs
  obtain ⟨Q, hQ2, a, ha, b, hb, hab⟩ := hQ
  have hquasi : IsQuasisimpleTwoNonab ↥L :=
    isQuasisimpleTwoNonab_of_simple hs
      (Small.card_gt_120_of_nonabelian_two_subgroup ⟨Q, hQ2, a, ha, b, hb, hab⟩)
      ⟨Q, hQ2, a, ha, b, hb, hab⟩
  have hnotP : ¬ IsPGroup 2 ↥L := fun hL =>
    hab (EdgeAux.commute_of_isSimpleGroup_of_isPGroup_two hL a b)
  have hX : pElementSubgroup 2 L = L := by
    have key : ∀ g ∈ L, pElementSubgroup 2 L ≤
        (pElementSubgroup 2 L).comap (MulAut.conj g).toMonoidHom := by
      intro g hg
      unfold pElementSubgroup
      rw [Subgroup.closure_le]
      rintro y ⟨hyL, k, hk⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      exact Subgroup.subset_closure
        ⟨L.mul_mem (L.mul_mem hg hyL) (L.inv_mem hg), k,
          (MulEquiv.orderOf_eq (MulAut.conj g) y).trans hk⟩
    have hLN : L ≤ Subgroup.normalizer ((pElementSubgroup 2 L : Subgroup Y) : Set Y) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => key g hg hx, fun hx => ?_⟩
      have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ pElementSubgroup 2 L :=
        Subgroup.mem_comap.1 (key g⁻¹ (L.inv_mem hg) hx)
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [e] at h2
    haveI := EdgeAux.normal_subgroupOf_of_le_normalizer hLN
    apply le_antisymm (pElementSubgroup_le (p := 2) L)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((pElementSubgroup 2 L).subgroupOf L) with h0 | h1
    · exfalso
      obtain ⟨j, hj⟩ := EdgeAux.orderOf_two_pow_of_mem hQ2 ha
      have haL : (a : Y) ∈ pElementSubgroup 2 L :=
        Subgroup.subset_closure ⟨a.2, j, (Subgroup.orderOf_coe a).trans hj⟩
      have hmem : a ∈ (pElementSubgroup 2 L).subgroupOf L := Subgroup.mem_subgroupOf.2 haL
      rw [h0, Subgroup.mem_bot] at hmem
      apply hab
      rw [hmem, one_mul, mul_one]
    · intro y hy
      have hmem : (⟨y, hy⟩ : ↥L) ∈ (pElementSubgroup 2 L).subgroupOf L := by
        rw [h1]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 hmem
  have hO : twoResidual L = L := by
    have hLN : L ≤ Subgroup.normalizer ((twoResidual L : Subgroup Y) : Set Y) :=
      le_normalizer_twoResidual L
    haveI := EdgeAux.normal_subgroupOf_of_le_normalizer hLN
    apply le_antisymm (twoResidual_le L)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((twoResidual L).subgroupOf L) with h0 | h1
    · exfalso
      apply hnotP
      intro y
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient L (y : Y) y.2
      refine ⟨k, ?_⟩
      have hmem : y ^ 2 ^ k ∈ (twoResidual L).subgroupOf L :=
        Subgroup.mem_subgroupOf.2 (by rw [Subgroup.coe_pow]; exact hk)
      rw [h0, Subgroup.mem_bot] at hmem
      exact hmem
    · intro x hx
      have hmem : (⟨x, hx⟩ : ↥L) ∈ (twoResidual L).subgroupOf L := by
        rw [h1]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 hmem
  have hC : CFSG.pCore 2 ↥L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥L) with h0 | h1
    · exact h0
    · exfalso
      apply hnotP
      intro y
      have hy : y ∈ CFSG.pCore 2 ↥L := by
        rw [h1]
        exact Subgroup.mem_top y
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨y, hy⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  rw [hX, hO]
  exact quasisimpleModTwoNonab_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot) hquasi

theorem exists_nonabelian_two_of_adj (h : BorelQuotient D n H π M) {j k : Fin D.rank}
    (hjk : j ≠ k) (hc : D.cartan j k ≠ 0) :
    ∃ Q : Subgroup S, IsPGroup 2 Q ∧ ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos h.extras h.pGroup
  obtain ⟨a, ha, c, hcc, hac⟩ := exists_not_commute_of_cartan_ne_zero h.ct h.extras hjk hc
  have haU : a ∈ posUnipotent D :=
    rootGroup_le_posUnipotent ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j)
      (ht_single_pos j) ha
  have hcU : c ∈ posUnipotent D :=
    rootGroup_le_posUnipotent ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k)
      (ht_single_pos k) hcc
  have hzc : ⁅a, c⁆ ∈ posUnipotent D := by
    rw [commutatorElement_def]
    exact (posUnipotent D).mul_mem
      ((posUnipotent D).mul_mem ((posUnipotent D).mul_mem haU hcU) ((posUnipotent D).inv_mem haU))
      ((posUnipotent D).inv_mem hcU)
  refine ⟨(posUnipotent D).map π, hU2.map π, π a, Subgroup.mem_map_of_mem π haU,
    π c, Subgroup.mem_map_of_mem π hcU, fun hcomm => hac ?_⟩
  have hker : π ⁅a, c⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  have hzM : ⁅a, c⁆ ^ M = 1 := h.ker_pow _ (MonoidHom.mem_ker.2 hker)
  have hodd : Odd (orderOf ⁅a, c⁆) := Odd.of_dvd_nat h.odd (orderOf_dvd_of_pow_eq_one hzM)
  obtain ⟨r, hr⟩ := hU2 ⟨⁅a, c⁆, hzc⟩
  have hr' : ⁅a, c⁆ ^ 2 ^ r = 1 := congrArg Subtype.val hr
  exact commutatorElement_eq_one_iff_mul_comm.1 (EdgeAux.eq_one_of_odd_orderOf_of_pow_two hodd hr')

end CFSG.AGLEmbeddingD2.Tits.GN516.Edge
