module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviBQ
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoNode

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open scoped Pointwise
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.LeviBlock
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar CFSG.AGLEmbeddingD2.Tits.GN516
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section Levi

variable {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

private theorem exists_sylow_map_posUnipotent (h : BorelQuotient D n H π M) :
    ∃ S : Sylow 2 Y, (S : Subgroup Y) = (posUnipotent D).map π := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos h.extras h.pGroup
  have hidx : ¬ 2 ∣ ((posUnipotent D).map π).index := fun hd =>
    h.not_dvd_index (hd.trans (Subgroup.index_map_dvd _ h.surj))
  exact ⟨(hU2.map π).toSylow hidx, rfl⟩

private theorem conj_n_mem_negUnipotent (h : BorelQuotient D n H π M) (i : Fin D.rank) {x : K}
    (hx : x ∈ D.rootGroup (Pi.single i 1)) : n i * x * (n i)⁻¹ ∈ negUnipotent D := by
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have h1 := h.ct.conj_mem i _ hα x hx
  rw [weylAction_simple_single] at h1
  have hα' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  refine rootGroup_le_negUnipotent hα' ?_ h1
  rw [ht_neg]
  have := ht_single_pos (D := D) i
  omega

private theorem exists_mul_of_mem_posUnipotent (h : BorelQuotient D n H π M) (i : Fin D.rank) {u : K}
    (hu : u ∈ posUnipotent D) : ∃ w ∈ posUnipotentExcept D i,
      ∃ x ∈ D.rootGroup (Pi.single i 1), u = w * x := by
  rw [posUnipotent_eq_sup h.extras i, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (rootGroup_single_le_normalizer h.extras i),
    Set.mem_mul] at hu
  obtain ⟨w, hw, x, hx, rfl⟩ := hu
  exact ⟨w, hw, x, hx, rfl⟩

private theorem mem_posUnipotentExcept_of_conj (h : BorelQuotient D n H π M) (i : Fin D.rank) {u' : K}
    (hu' : u' ∈ posUnipotent D) {v : K} (hv : v ∈ posUnipotent D) (hvu : v = n i * u' * (n i)⁻¹) :
    v ∈ posUnipotentExcept D i := by
  obtain ⟨w, hw, x, hx, rfl⟩ := exists_mul_of_mem_posUnipotent h i hu'
  have hw' : n i * w * (n i)⁻¹ ∈ posUnipotentExcept D i := conj_n_mem_posUnipotentExcept h.ct i hw
  have hx' : n i * x * (n i)⁻¹ ∈ negUnipotent D := conj_n_mem_negUnipotent h i hx
  have hsplit : n i * (w * x) * (n i)⁻¹ = (n i * w * (n i)⁻¹) * (n i * x * (n i)⁻¹) := by group
  have hx1 : n i * x * (n i)⁻¹ ∈ posUnipotent D := by
    have : n i * x * (n i)⁻¹ = (n i * w * (n i)⁻¹)⁻¹ * v := by rw [hvu, hsplit]; group
    rw [this]
    exact mul_mem (inv_mem (posUnipotentExcept_le_posUnipotent i hw')) hv
  have hx2 : n i * x * (n i)⁻¹ ∈ posUnipotent D ⊓ negUnipotent D := ⟨hx1, hx'⟩
  rw [posUnipotent_inf_negUnipotent h.extras, Subgroup.mem_bot] at hx2
  rw [hvu, hsplit, hx2, mul_one]
  exact hw'

theorem le_map_posUnipotentExcept_of_normal (h : BorelQuotient D n H π M) (i : Fin D.rank)
    {N : Subgroup Y} (hNR : N ≤ (unipJ D {i}).map π)
    (hN : (N.subgroupOf ((unipJ D {i}).map π)).Normal) (hN2 : IsPGroup 2 N) :
    N ≤ (posUnipotentExcept D i).map π := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_map_posUnipotent h
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos h.extras h.pGroup
  set Rb : Subgroup Y := (unipJ D {i}).map π with hRb
  have hSR : (S : Subgroup Y) ≤ Rb := by
    rw [hS]
    exact Subgroup.map_mono (posUnipotent_le_unipJ {i})
  have hnR : π (n i) ∈ Rb :=
    ⟨n i, rankOne_le_unipJ (Set.mem_singleton i) (h.ct.n_mem i), rfl⟩
  haveI := hN
  have hN2' : IsPGroup 2 (N.subgroupOf Rb) := hN2.comap_subtype
  have key : ∀ T : Sylow 2 Y, (T : Subgroup Y) ≤ Rb → N ≤ T := by
    intro T hT x hx
    have h1 := IsPGroup.le_sylow_of_normal hN2' (T.subtype hT)
    have h2 := h1 (Subgroup.mem_subgroupOf.2 hx : (⟨x, hNR hx⟩ : ↥Rb) ∈ N.subgroupOf Rb)
    rw [Sylow.coe_subtype] at h2
    exact Subgroup.mem_subgroupOf.1 h2
  have hS1 : N ≤ (S : Subgroup Y) := key S hSR
  set T₂ : Sylow 2 Y := (π (n i)) • S with hT₂
  have hT₂R : (T₂ : Subgroup Y) ≤ Rb := by
    intro x hx
    rw [hT₂, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    exact mul_mem (mul_mem hnR (hSR hs)) (inv_mem hnR)
  have hS2 : N ≤ (T₂ : Subgroup Y) := key T₂ hT₂R
  intro y hy
  have hy1 : y ∈ (S : Subgroup Y) := hS1 hy
  have hy2 : y ∈ (T₂ : Subgroup Y) := hS2 hy
  rw [hS] at hy1
  obtain ⟨u, hu, rfl⟩ := hy1
  rw [hT₂, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hy2
  obtain ⟨s, hs, hsu⟩ := hy2
  rw [hS] at hs
  obtain ⟨u', hu', rfl⟩ := hs
  set b : K := n i * u' * (n i)⁻¹ with hb
  have hconj : π b = π u := by
    rw [hb, map_mul, map_mul, map_inv]
    exact hsu
  have hz : u⁻¹ * b ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hconj, inv_mul_cancel]
  have hzM : (u⁻¹ * b) ^ M = 1 := h.ker_pow _ hz
  have hzc : Commute u b := by
    have h1 := Subgroup.mem_center_iff.1 (h.ker_central _ hz) u
    have h2 : u * (u⁻¹ * b) = u⁻¹ * b * u := h1
    have h3 : b = u⁻¹ * b * u := by rw [← h2]; group
    show u * b = b * u
    calc u * b = u * (u⁻¹ * b * u) := by rw [← h3]
      _ = b * u := by group
  obtain ⟨r, hr⟩ : ∃ r : ℕ, u ^ 2 ^ r = 1 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).1 hU2 ⟨u, hu⟩
    refine ⟨k, ?_⟩
    have : u ^ orderOf u = 1 := pow_orderOf_eq_one u
    rwa [← Subgroup.orderOf_mk u hu, hk] at this
  obtain ⟨s', hs'⟩ : ∃ s : ℕ, u' ^ 2 ^ s = 1 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).1 hU2 ⟨u', hu'⟩
    refine ⟨k, ?_⟩
    have : u' ^ orderOf u' = 1 := pow_orderOf_eq_one u'
    rwa [← Subgroup.orderOf_mk u' hu', hk] at this
  have hbs : b ^ 2 ^ s' = 1 := by
    rw [hb, conj_pow, hs', mul_one, mul_inv_cancel]
  have h1 : u⁻¹ * b = 1 := eq_one_of_central_odd h.odd hzM rfl hzc hr hbs
  have hub : u = b := inv_mul_eq_one.1 h1
  have hmem : u ∈ posUnipotentExcept D i := mem_posUnipotentExcept_of_conj h i hu' hu hub
  exact ⟨u, hmem, rfl⟩

theorem map_posUnipotentExcept_le (h : BorelQuotient D n H π M) (i : Fin D.rank) :
    (posUnipotentExcept D i).map π ≤ (unipJ D {i}).map π :=
  Subgroup.map_mono (by rw [unipJ_singleton h i]; exact le_sup_right)

theorem map_posUnipotentExcept_normal (h : BorelQuotient D n H π M) (i : Fin D.rank) :
    (((posUnipotentExcept D i).map π).subgroupOf ((unipJ D {i}).map π)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (map_posUnipotentExcept_le h i),
    unipJ_singleton h i, Subgroup.map_sup]
  exact sup_le ((Subgroup.map_mono (rankOne_le_normalizer_posUnipotentExcept h.ct h.extras i)).trans
    (Subgroup.le_normalizer_map π)) Subgroup.le_normalizer

theorem isPGroup_map_posUnipotentExcept (h : BorelQuotient D n H π M) (i : Fin D.rank) :
    IsPGroup 2 ((posUnipotentExcept D i).map π) :=
  (isPGroup_posUnipotentExcept h i).map π

theorem exists_mulEquiv_levi (h : BorelQuotient D n H π M) (i : Fin D.rank)
    [hWn : (((posUnipotentExcept D i).map π).subgroupOf ((unipJ D {i}).map π)).Normal]
    (hLU : rankOne D.rootGroup i ⊓ posUnipotentExcept D i = ⊥)
    (hker : π.ker ⊓ rankOne D.rootGroup i = ⊥) :
    Nonempty (↥((unipJ D {i}).map π) ⧸
      ((posUnipotentExcept D i).map π).subgroupOf ((unipJ D {i}).map π) ≃*
        ↥(rankOne D.rootGroup i)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Rb : Subgroup Y := (unipJ D {i}).map π with hRb
  set W : Subgroup Y := (posUnipotentExcept D i).map π with hW
  have hL : rankOne D.rootGroup i ≤ unipJ D {i} := rankOne_le_unipJ (Set.mem_singleton i)
  let π₁ : ↥(rankOne D.rootGroup i) →* ↥Rb :=
    (π.comp (rankOne D.rootGroup i).subtype).codRestrict Rb (fun x => ⟨x.1, hL x.2, rfl⟩)
  let τ : ↥(rankOne D.rootGroup i) →* ↥Rb ⧸ W.subgroupOf Rb :=
    (QuotientGroup.mk' (W.subgroupOf Rb)).comp π₁
  have hinj : Function.Injective τ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine eq_bot_iff.2 fun x hx => ?_
    rw [Subgroup.mem_bot]
    have h1 : π₁ x ∈ W.subgroupOf Rb := (QuotientGroup.eq_one_iff _).1 hx
    have h2 : π (x : K) ∈ W := h1
    obtain ⟨w, hw, hwx⟩ := h2
    have hz : w⁻¹ * (x : K) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwx, inv_mul_cancel]
    have hzM : (w⁻¹ * (x : K)) ^ M = 1 := h.ker_pow _ hz
    have hxw : (x : K) = w * (w⁻¹ * (x : K)) := by group
    have hxM : (x : K) ^ M = w ^ M := by
      have hc : Commute w (w⁻¹ * (x : K)) := Subgroup.mem_center_iff.1 (h.ker_central _ hz) w
      calc (x : K) ^ M = (w * (w⁻¹ * (x : K))) ^ M := by rw [← hxw]
        _ = w ^ M * (w⁻¹ * (x : K)) ^ M := hc.mul_pow M
        _ = w ^ M := by rw [hzM, mul_one]
    have hwM : w ^ M = 1 := by
      have hmem : w ^ M ∈ rankOne D.rootGroup i ⊓ posUnipotentExcept D i :=
        ⟨by rw [← hxM]; exact (rankOne D.rootGroup i).pow_mem x.2 M,
          (posUnipotentExcept D i).pow_mem hw M⟩
      rw [hLU, Subgroup.mem_bot] at hmem
      exact hmem
    have hw1 : w = 1 := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).1 (isPGroup_posUnipotentExcept h i) ⟨w, hw⟩
      have hd1 : orderOf w ∣ 2 ^ k := by
        rw [← Subgroup.orderOf_mk w hw, hk]
      have hd2 : orderOf w ∣ M := orderOf_dvd_of_pow_eq_one hwM
      have hcop : Nat.Coprime (2 ^ k) M := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 h.odd)
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
    have hxz : (x : K) ∈ π.ker := by
      rw [hw1] at hz
      simpa using hz
    have hmem : (x : K) ∈ π.ker ⊓ rankOne D.rootGroup i := ⟨hxz, x.2⟩
    rw [hker, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hsurj : Function.Surjective τ := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H r =>
      obtain ⟨g, hg, hgr⟩ := r.2
      have hg' : g ∈ ((rankOne D.rootGroup i : Set K) * (posUnipotentExcept D i : Set K)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
          (rankOne_le_normalizer_posUnipotentExcept h.ct h.extras i), ← unipJ_singleton h i]
        exact hg
      obtain ⟨l, hl, u, hu, rfl⟩ := hg'
      refine ⟨⟨l, hl⟩, ?_⟩
      show QuotientGroup.mk (π₁ ⟨l, hl⟩) = QuotientGroup.mk r
      rw [QuotientGroup.eq]
      show (π l)⁻¹ * (r : Y) ∈ W
      rw [← hgr, map_mul, ← mul_assoc, inv_mul_cancel, one_mul]
      exact ⟨u, hu, rfl⟩
  exact ⟨(MulEquiv.ofBijective τ ⟨hinj, hsurj⟩).symm⟩

end Levi

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
