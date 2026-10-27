module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeDefs
public import CFSG.LocalAnalysis.GLTheoremB.BarXTools
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Input19DeltaReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

section Transfer

variable {M M' : Type*} [Group M] [Group M']

theorem map_glaPPrimeCoreOf_of_injective (p : ℕ) (ψ : M →* M') (hψ : Function.Injective ψ)
    (A : Subgroup M) : (GLAPPrimeCoreOf p A).map ψ = GLAPPrimeCoreOf p (A.map ψ) := by
  unfold GLAPPrimeCoreOf
  rw [Subgroup.map_map]
  set e := A.equivMapOfInjective ψ hψ with he
  have h1 : ψ.comp A.subtype = (A.map ψ).subtype.comp e.toMonoidHom := by
    ext a
    rfl
  rw [h1, ← Subgroup.map_map]
  congr 1
  exact CFSG.pPrimeCore_map_iso p e

theorem map_inf_centralizer_of_injective (ψ : M →* M') (hψ : Function.Injective ψ)
    (H : Subgroup M) (d : M) :
    (H ⊓ Subgroup.centralizer ({d} : Set M)).map ψ =
      H.map ψ ⊓ Subgroup.centralizer ({ψ d} : Set M') := by
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, ⟨hxH, hxC⟩, rfl⟩
    exact ⟨⟨x, hxH, rfl⟩, by rw [← map_mul, ← map_mul, hxC]⟩
  · rintro ⟨⟨x, hxH, rfl⟩, hxC⟩
    refine ⟨x, ⟨hxH, ?_⟩, rfl⟩
    rw [← map_mul, ← map_mul] at hxC
    exact hψ hxC

theorem map_localDeltaIn_le (p : ℕ) (ψ : M →* M') (hψ : Function.Injective ψ)
    (H D : Subgroup M) :
    (localDeltaIn p H D).map ψ ≤ localDeltaIn p (H.map ψ) (D.map ψ) := by
  unfold localDeltaIn
  simp only [le_iInf_iff]
  rintro _ ⟨d, hd, rfl⟩ hd1
  have hd1' : d ≠ 1 := fun h => hd1 (by rw [h, map_one])
  rw [← map_inf_centralizer_of_injective ψ hψ, ← map_glaPPrimeCoreOf_of_injective p ψ hψ]
  exact Subgroup.map_mono (iInf₂_le_of_le d hd (iInf_le_of_le hd1' le_rfl))

variable {K K' : Type*} [Group K] [Group K']

theorem IsLocallyBalancedAbs.of_injective {p k : ℕ} (ψ : MulAut K →* MulAut K')
    (hψ : Function.Injective ψ) (hinn : innerAut K' ≤ (innerAut K).map ψ)
    (h : IsLocallyBalancedAbs p k K') : IsLocallyBalancedAbs p k K := by
  intro D hD hcard H hH hDH
  have hD' : IsElemAbelian p (D.map ψ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      change ψ x * ψ y = ψ y * ψ x
      have := congrArg Subtype.val (hD.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [← map_mul, ← map_mul]
      exact congrArg ψ this
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hD.2 x hx, map_one]
  have hcard' : Nat.card (D.map ψ) = p ^ k := by
    rw [Subgroup.card_map_of_injective hψ, hcard]
  have hH' : innerAut K' ≤ H.map ψ := hinn.trans (Subgroup.map_mono hH)
  have hDH' : D.map ψ ≤ Subgroup.normalizer ((H.map ψ : Subgroup (MulAut K')) : Set (MulAut K')) :=
    (Subgroup.map_mono hDH).trans (Subgroup.le_normalizer_map ψ)
  have h0 := h (D.map ψ) hD' hcard' (H.map ψ) hH' hDH'
  have hle := map_localDeltaIn_le p ψ hψ H D
  rw [h0, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hψ] at hle
  exact hle

theorem IsLocallyBalancedAbs.of_mulEquiv {p k : ℕ} (e : K ≃* K')
    (h : IsLocallyBalancedAbs p k K') : IsLocallyBalancedAbs p k K := by
  refine IsLocallyBalancedAbs.of_injective (MulAut.congr e).toMonoidHom
    (MulAut.congr e).injective ?_ h
  rintro _ ⟨y, rfl⟩
  refine ⟨MulAut.conj (e.symm y), ⟨e.symm y, rfl⟩, ?_⟩
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

@[expose] noncomputable def autCenterQuot (K : Type*) [Group K] :
    MulAut K →* MulAut (K ⧸ Subgroup.center K) where
  toFun β := QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) β
    (Subgroup.map_center_eq β)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' β γ := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x => rfl

theorem autCenterQuot_mk (β : MulAut K) (x : K) :
    autCenterQuot K β (x : K ⧸ Subgroup.center K) = (β x : K ⧸ Subgroup.center K) := rfl

theorem autCenterQuot_injective_of_perfect (hK : commutator K = ⊤) :
    Function.Injective (autCenterQuot K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro β hβ
  rw [MonoidHom.mem_ker] at hβ
  have hβ' : ∀ x : K, x⁻¹ * β x ∈ Subgroup.center K := by
    intro x
    have h1 := congrArg (fun γ : MulAut (K ⧸ Subgroup.center K) => γ (x : K ⧸ Subgroup.center K)) hβ
    simp only [autCenterQuot_mk, MulAut.one_apply] at h1
    exact QuotientGroup.eq.1 h1.symm
  rw [Subgroup.mem_bot]
  let δ : K →* Subgroup.center K :=
    { toFun := fun x => ⟨x⁻¹ * β x, hβ' x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [map_mul]
        have hx := Subgroup.mem_center_iff.1 (hβ' x)
        calc (x * y)⁻¹ * (β x * β y) = y⁻¹ * (x⁻¹ * β x) * β y := by group
          _ = (x⁻¹ * β x) * (y⁻¹ * β y) := by rw [hx y⁻¹]; group }
  have hcomm : commutator K ≤ δ.ker := by
    rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.1 (δ b).2 (δ a))
  ext x
  have hx : x ∈ δ.ker := hcomm (hK ▸ Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at hx
  have h1 : x⁻¹ * β x = 1 := congrArg Subtype.val hx
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.1 h1).symm

theorem innerAut_le_map_autCenterQuot :
    innerAut (K ⧸ Subgroup.center K) ≤ (innerAut K).map (autCenterQuot K) := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨MulAut.conj x, ⟨x, rfl⟩, ?_⟩
  ext z
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
  rw [autCenterQuot_mk]
  simp [MulAut.conj_apply]

theorem IsLocallyBalancedAbs.of_quotient_center {p k : ℕ} (hK : commutator K = ⊤)
    (h : IsLocallyBalancedAbs p k (K ⧸ Subgroup.center K)) : IsLocallyBalancedAbs p k K :=
  IsLocallyBalancedAbs.of_injective _ (autCenterQuot_injective_of_perfect hK)
    innerAut_le_map_autCenterQuot h

end Transfer

section Components

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_barOf {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) : CFSG.Open.IsQuasisimple (barOf p L) := by
  have e := quotEquivBarX hp hL.1 hL.2.1
  have hq : CFSG.Open.IsQuasisimple ↥(barX p X L) := hL.2.2.1.2.2
  obtain ⟨hcomm, hsimple⟩ := hq
  refine ⟨?_, ?_⟩
  · have h1 := congrArg (Subgroup.map e.symm.toMonoidHom) hcomm
    rw [commutator, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.symm.surjective]
      at h1
    rw [commutator]
    exact h1
  · have := hsimple
    exact (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)).symm.isSimpleGroup

theorem isCatalogGroup_quotient_center_barOf {p : ℕ} (hp : p.Prime) (hG : IsKProper G)
    {X L : Subgroup G} (hX : X ≠ ⊤) (hL : GLAPComponent p X L) :
    IsSimpleGroup (barOf p L ⧸ Subgroup.center (barOf p L)) ∧
      (∃ a b : barOf p L ⧸ Subgroup.center (barOf p L), a * b ≠ b * a) ∧
      IsCatalogGroup (barOf p L ⧸ Subgroup.center (barOf p L)) := by
  obtain ⟨hperf, hsimple⟩ := isQuasisimple_barOf hp hL
  have hnab : ∃ a b : barOf p L ⧸ Subgroup.center (barOf p L), a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    have hcomm : ∀ a b : barOf p L, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center (barOf p L) := by
      intro a b
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hab (a : barOf p L ⧸ Subgroup.center (barOf p L)) b]
      group
    have hle : commutator (barOf p L) ≤ Subgroup.center (barOf p L) := by
      rw [commutator, Subgroup.commutator_le]
      intro a _ b _
      rw [commutatorElement_def]
      exact hcomm a b
    rw [hperf, top_le_iff] at hle
    have hall : ∀ q : barOf p L ⧸ Subgroup.center (barOf p L), q = 1 := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x => exact (QuotientGroup.eq_one_iff x).2 (hle ▸ Subgroup.mem_top x)
    have := hsimple
    obtain ⟨a, b, hab⟩ := exists_pair_ne (barOf p L ⧸ Subgroup.center (barOf p L))
    exact hab ((hall a).trans (hall b).symm)
  refine ⟨hsimple, hnab, ?_⟩
  set π : ↥L →* barOf p L := QuotientGroup.mk' (GLAPPrimeCore p ↥L) with hπ
  set N : Subgroup ↥L := (Subgroup.center (barOf p L)).comap π with hN
  have hNn : N.Normal := Subgroup.Normal.comap inferInstance π
  have hker : GLAPPrimeCore p ↥L ≤ N := by
    intro x hx
    change π x ∈ Subgroup.center (barOf p L)
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact Subgroup.one_mem _
  have e1 : (↥L ⧸ N) ≃* (barOf p L ⧸ Subgroup.center (barOf p L)) := by
    have hNmap : N.map π = Subgroup.center (barOf p L) :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    exact (QuotientGroup.quotientQuotientEquivQuotient (GLAPPrimeCore p ↥L) N hker).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hNmap)
  set M : Subgroup G := N.map L.subtype with hM
  have hML : M ≤ L := by
    rintro _ ⟨n, -, rfl⟩
    exact n.2
  have hMsub : M.subgroupOf L = N := by
    rw [hM]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective N
  have hMn : (M.subgroupOf L).Normal := by
    rw [hMsub]
    exact hNn
  have hLtop : L ≠ ⊤ := fun h => hX (top_le_iff.1 (h ▸ hL.1))
  have e2 : (↥L ⧸ M.subgroupOf L) ≃* (↥L ⧸ N) := QuotientGroup.quotientMulEquivOfEq hMsub
  have := hsimple
  have hs2 : IsSimpleGroup (↥L ⧸ M.subgroupOf L) := (e2.trans e1).isSimpleGroup
  have hna2 : ∃ a b : ↥L ⧸ M.subgroupOf L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨(e2.trans e1).symm a, (e2.trans e1).symm b, fun h => hab ?_⟩
    have := congrArg (e2.trans e1) h
    simpa using this
  obtain ⟨i, ⟨φ⟩⟩ := hG L M hLtop hML hs2 hna2
  exact ⟨i, ⟨(e2.trans e1).symm.trans φ⟩⟩

end Components

theorem localThreeBalanceSimple_of_families (hD : LocalThreeBalanceDefChar)
    (hC : LocalThreeBalanceCrossChar) (hSp : LocalThreeBalanceSporadic) :
    LocalThreeBalanceSimple := by
  intro S _ _ hsimple hnab hcat hnalt p hp hp2
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exact ((hnalt n).false e).elim
  | lie idx =>
    by_cases hch : idx.1.characteristic = p
    · exact hD S hsimple hnab idx ⟨e⟩ p hp hp2 hch
    · exact hC S hsimple hnab idx ⟨e⟩ p hp hp2 hch
  | sporadic name =>
    exact hSp S hsimple hnab name ⟨e⟩ p hp hp2

theorem localThreeBalance_of_simple_alt (hS : LocalThreeBalanceSimple)
    (hA : LocalThreeBalanceAlt) : LocalThreeBalance := by
  intro G _ _ hG p hp hp2 X hX B hBX hB hrank h3 L hL
  obtain ⟨hsimple, hnab, hcat⟩ := isCatalogGroup_quotient_center_barOf hp hG hX hL
  by_cases halt : ∃ n : ℕ,
      Nonempty ((barOf p L ⧸ Subgroup.center (barOf p L)) ≃* ↥(alternatingGroup (Fin n)))
  · obtain ⟨n, hn⟩ := halt
    exact hA G hG p hp hp2 X hX B hBX hB hrank h3 L hL n hn
  · have hnalt : ∀ n : ℕ,
        IsEmpty ((barOf p L ⧸ Subgroup.center (barOf p L)) ≃* ↥(alternatingGroup (Fin n))) :=
      fun n => not_nonempty_iff.1 fun h => halt ⟨n, h⟩
    have hperf : commutator (barOf p L) = ⊤ := (isQuasisimple_barOf hp hL).1
    exact (IsLocallyBalancedAbs.of_quotient_center hperf
      (hS _ hsimple hnab hcat hnalt p hp hp2)).isLocallyBalanced _

end CFSG.HardMathSupport.Timmesfeld.Coordinator
