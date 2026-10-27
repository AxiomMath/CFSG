module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankOneCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerRankOneKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitContainmentTransfer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSemidihedralKernel
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open CFSG Subgroup CentralTwoActionKernel
open scoped commutatorElement Pointwise

namespace RankProjectiveAction

variable {H : Type*} [Group H]

theorem oddCore_eq_pPrimeCore (X : Type*) [Group X] : CFSG.oddCore X = pPrimeCore 2 X :=
  (CFSG.oddCore_eq_piCore X).trans (CFSG.pPrimeCore_eq_piCore X 2).symm

instance pLayer_two_normal {X : Type*} [Group X] [Finite X] : (pLayer X 2).Normal := by
  have := CatalogueBPrimeJoin.pLayer_characteristic (G := X) (p := 2)
  infer_instance

@[expose] noncomputable def quotT (E : Subgroup H) [E.Normal] : E →* OddQuotT E :=
  (QuotientGroup.mk' (center (OddQuot E))).comp (QuotientGroup.mk' (CFSG.oddCore E))

@[expose] noncomputable def factorImage (E : Subgroup H) [E.Normal] (X : Subgroup H) :
    Subgroup (OddQuotT E) :=
  (X.subgroupOf E).map (quotT E)

theorem center_quotient_congr {X : Type*} [Group X] {M M' : Subgroup X} [M.Normal] [M'.Normal]
    (h : M = M') {x : X} (hc : center (X ⧸ M') = zpowers (x : X ⧸ M'))
    (hcard : Nat.card (center (X ⧸ M')) = 2) :
    center (X ⧸ M) = zpowers (x : X ⧸ M) ∧ Nat.card (center (X ⧸ M)) = 2 := by
  subst h
  exact ⟨hc, hcard⟩

theorem center_coreQuotient_eq_zpowers {X : Type*} [Group X] [Finite X]
    (hrank : CFSG.pRank 2 X ≤ 1) (hA : IsQuasisimple (X ⧸ pPrimeCore 2 X)) {a : X}
    (ha : orderOf a = 2) : center (X ⧸ pPrimeCore 2 X) = zpowers (a : X ⧸ pPrimeCore 2 X) := by
  have hO := oddCore_eq_pPrimeCore X
  have hA' : IsQuasisimple (X ⧸ CFSG.oddCore X) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hO).symm hA
  obtain ⟨-, z, -, hzu, hzc, hzcard, -⟩ :=
    rank_one_quasisimple_odd_core_quotient_central_cover.{_, 0} hrank hA'
  have ha' : orderOf (a : X ⧸ CFSG.oddCore X) = 2 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, ← ha, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h1
      rw [QuotientGroup.eq_one_iff] at h1
      have hodd : Odd (Nat.card (CFSG.oddCore X)) := by
        rw [hO]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      have hdvd := orderOf_dvd_natCard (⟨a, h1⟩ : CFSG.oddCore X)
      rw [Subgroup.orderOf_mk, ha] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  rw [← hzu _ ha'] at hzc
  exact (center_quotient_congr hO.symm hzc hzcard).1

theorem exists_sylow_inf_of_le_normalizer [Finite H] {N S K : Subgroup H} (hSN : S ≤ N)
    (hS : ∃ T : Sylow 2 N, (T : Subgroup N) = S.subgroupOf N) (hKN : K ≤ N)
    (hK : N ≤ normalizer (K : Set H)) :
    ∃ T : Sylow 2 K, (T : Subgroup K) = (S ⊓ K).subgroupOf K := by
  obtain ⟨T, hT⟩ := hS
  have hKn : (K.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hKN).mpr hK
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal T hKn.isSubnormal
  let e : K.subgroupOf N ≃* K := subgroupOfEquivOfLe hKN
  have he : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨P.mapSurjective he, ?_⟩
  rw [Sylow.coe_mapSurjective]
  apply map_injective K.subtype_injective
  have hcomp : K.subtype.comp e.toMonoidHom = N.subtype.comp (K.subgroupOf N).subtype := by
    ext x
    rfl
  rw [map_map, subgroupOf_map_subtype, inf_assoc, inf_idem, hcomp, ← map_map, hP, hT,
    map_inf_eq _ _ N.subtype N.subtype_injective, subgroupOf_map_subtype,
    subgroupOf_map_subtype, inf_eq_left.mpr hSN, inf_eq_left.mpr hKN]

variable [Finite H]

theorem projective_action_of_sup {a : H} (ha : orderOf a = 2) (haZ : a ∈ center H)
    {J L : Subgroup H} (hJ : IsPComponent 2 J) (hL : IsPComponent 2 L) (hJL : J ≠ L)
    (haJ : a ∈ J) (haL : a ∈ L) (hJrank : CFSG.pRank 2 J ≤ 1) (hLrank : CFSG.pRank 2 L ≤ 1)
    (hswap : ∀ h : H, h ∉ normalizer (J : Set H) → conjugate J h = L)
    (hLN : normalizer (J : Set H) ≤ normalizer (L : Set H))
    (hNidx : (normalizer (J : Set H)).index = 2) {S : Subgroup H}
    (hSN : S ≤ normalizer (J : Set H))
    (hSsyl : ∃ T : Sylow 2 (normalizer (J : Set H)),
      (T : Subgroup _) = S.subgroupOf (normalizer (J : Set H)))
    (haS : a ∈ S) (hDsyl : ∃ T : Sylow 2 L, (T : Subgroup L) = (S ⊓ L).subgroupOf L)
    {r : ℕ} (hr : 3 ≤ r)
    (hDQ : Nonempty ((S ⊓ L : Subgroup H) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hDP : S ⊓ L ≤ S ⊓ UnbalancedLayer.coreActionKernel J)
    (hidx : (S ⊓ L).relIndex (S ⊓ UnbalancedLayer.coreActionKernel J) = 2) {n : ℕ}
    (hn : 4 ≤ n) (hPSD : Nonempty ((S ⊓ UnbalancedLayer.coreActionKernel J : Subgroup H) ≃*
      Open.SemidihedralGroup n))
    (E : Subgroup H) [E.Normal] (hE : E = J ⊔ L) :
    oddCoreIn E = (pPrimeCore 2 J).map J.subtype ⊔ (pPrimeCore 2 L).map L.subtype ∧
    ((oddCoreIn E : Subgroup H) : Set H) =
      ((pPrimeCore 2 J).map J.subtype : Set H) * ((pPrimeCore 2 L).map L.subtype : Set H) ∧
    CFSG.oddCore H ⊓ E = oddCoreIn E ∧
    ∃ aE : E, (aE : H) = a ∧
      center (OddQuot E) = zpowers (aE : OddQuot E) ∧ Nat.card (center (OddQuot E)) = 2 ∧
      (∃ φ : ↥(factorImage E J) × ↥(factorImage E L) ≃* OddQuotT E,
        ∀ x y, φ (x, y) = x * y) ∧
      (IsSimpleGroup ↥(factorImage E J) ∧ ∃ x y : ↥(factorImage E J), x * y ≠ y * x) ∧
      (IsSimpleGroup ↥(factorImage E L) ∧ ∃ x y : ↥(factorImage E L), x * y ≠ y * x) ∧
      (∃ ι : ↥(factorImage E J) ≃* (J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J),
        ∀ (j : J) (x : E) (t : factorImage E J), (x : H) = j →
          (t : OddQuotT E) = quotT E x →
            ι t = ((j : J ⧸ pPrimeCore 2 J) : (J ⧸ pPrimeCore 2 J) ⧸
              center (J ⧸ pPrimeCore 2 J))) ∧
      (∃ ι : ↥(factorImage E L) ≃* (L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L),
        ∀ (l : L) (x : E) (t : factorImage E L), (x : H) = l →
          (t : OddQuotT E) = quotT E x →
            ι t = ((l : L ⧸ pPrimeCore 2 L) : (L ⧸ pPrimeCore 2 L) ⧸
              center (L ⧸ pPrimeCore 2 L))) ∧
      (∀ (h : H) (e : E), betaHom E h ((e : OddQuot E) : OddQuotT E) =
        (((MulAut.conjNormal h e : E) : OddQuot E) : OddQuotT E)) ∧
      (betaHom E).ker = CFSG.oddCore H ⊔ zpowers (aE : H) ∧
      CFSG.oddCore H ⊓ zpowers (aE : H) = ⊥ ∧
      (∀ x ∈ CFSG.oddCore H, ∀ y ∈ zpowers (aE : H), x * y = y * x) ∧
      E.map (betaHom E) = (MulAut.conj : OddQuotT E →* MulAut (OddQuotT E)).range ∧
      (∃ φ : ↥(J.map (betaHom E)) × ↥(L.map (betaHom E)) ≃* ↥(E.map (betaHom E)),
        ∀ x y, (φ (x, y) : MulAut (OddQuotT E)) = x * y) ∧
      (∀ j ∈ J, ∃ t ∈ factorImage E J, ∀ x ∈ factorImage E J,
        betaHom E j x = t * x * t⁻¹) ∧
      (∀ t ∈ factorImage E J, ∃ j ∈ J, ∀ x ∈ factorImage E J,
        betaHom E j x = t * x * t⁻¹) ∧
      (∀ j ∈ J, ∀ y ∈ factorImage E L, betaHom E j y = y) ∧
      (∀ l ∈ L, ∃ t ∈ factorImage E L, ∀ x ∈ factorImage E L,
        betaHom E l x = t * x * t⁻¹) ∧
      (∀ t ∈ factorImage E L, ∃ l ∈ L, ∀ x ∈ factorImage E L,
        betaHom E l x = t * x * t⁻¹) ∧
      (∀ l ∈ L, ∀ y ∈ factorImage E J, betaHom E l y = y) ∧
      (∀ h : H, ((factorImage E J).map (betaHom E h).toMonoidHom = factorImage E J ∧
          (factorImage E L).map (betaHom E h).toMonoidHom = factorImage E L) ∨
        ((factorImage E J).map (betaHom E h).toMonoidHom = factorImage E L ∧
          (factorImage E L).map (betaHom E h).toMonoidHom = factorImage E J)) ∧
      (∀ h : H, betaHom E h ∈ (normalizer (J : Set H)).map (betaHom E) ↔
        ((factorImage E J).map (betaHom E h).toMonoidHom = factorImage E J ∧
          (factorImage E L).map (betaHom E h).toMonoidHom = factorImage E L)) ∧
      ((normalizer (J : Set H)).map (betaHom E)).relIndex (betaHom E).range = 2 ∧
      (∀ h : H, betaHom E h ∉ (normalizer (J : Set H)).map (betaHom E) →
        (factorImage E J).map (betaHom E h).toMonoidHom = factorImage E L ∧
          (factorImage E L).map (betaHom E h).toMonoidHom = factorImage E J) ∧
      (E.map (QuotientGroup.mk' (CFSG.oddCore H))).Normal ∧
      (∃ ι : E.map (QuotientGroup.mk' (CFSG.oddCore H)) ≃* OddQuot E,
        ∀ e : E, ι ⟨QuotientGroup.mk' (CFSG.oddCore H) e, mem_map_of_mem _ e.2⟩ =
          (e : OddQuot E)) ∧
      (∃ βbar : H ⧸ CFSG.oddCore H →* MulAut (OddQuotT E),
        (∀ h : H, βbar h = betaHom E h) ∧
        βbar.ker = zpowers (QuotientGroup.mk' (CFSG.oddCore H) (aE : H)) ∧
        zpowers (QuotientGroup.mk' (CFSG.oddCore H) (aE : H)) ≤ center (H ⧸ CFSG.oddCore H) ∧
        Nat.card (zpowers (QuotientGroup.mk' (CFSG.oddCore H) (aE : H))) = 2) ∧
      center (H ⧸ CFSG.oddCore H) = zpowers (QuotientGroup.mk' (CFSG.oddCore H) (aE : H)) := by
  subst hE
  have hJE : J ≤ J ⊔ L := le_sup_left
  have hLE : L ≤ J ⊔ L := le_sup_right
  obtain ⟨-, hrest⟩ :=
    CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two J L hJ hL
  obtain ⟨hLnJ, hJnL, hcommJL, -⟩ := hrest hJL
  have hacJ : ∀ j ∈ J, a * j = j * a := fun j _ => (mem_center_iff.mp haZ j).symm
  have hacL : ∀ l ∈ L, a * l = l * a := fun l _ => (mem_center_iff.mp haZ l).symm
  have hQJ := CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 J hJ
  have hQL := CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 L hL
  have hZA := center_coreQuotient_eq_zpowers hJrank hQJ
    (show orderOf (⟨a, haJ⟩ : J) = 2 by rw [Subgroup.orderOf_mk, ha])
  have hZB := center_coreQuotient_eq_zpowers hLrank hQL
    (show orderOf (⟨a, haL⟩ : L) = 2 by rw [Subgroup.orderOf_mk, ha])
  obtain ⟨s1, s2, s3, -, ⟨-, -, -, -, -, -, hcenter, hcard⟩, ⟨ν, -, hνker, hνJ, hνL, Ψ, hΨ⟩⟩ :=
    shared_involution_odd_core_product_quotient hJnL hLnJ hcommJL haJ haL hacJ hacL ha hZA hZB
  have hOeq : oddCoreIn (J ⊔ L) =
      (pPrimeCore 2 J).map J.subtype ⊔ (pPrimeCore 2 L).map L.subtype := by
    show (CFSG.oddCore ↥(J ⊔ L)).map (J ⊔ L).subtype = _
    rw [oddCore_eq_pPrimeCore, s1]
  have hOset : ((oddCoreIn (J ⊔ L) : Subgroup H) : Set H) =
      ((pPrimeCore 2 J).map J.subtype : Set H) * ((pPrimeCore 2 L).map L.subtype : Set H) := by
    rw [hOeq]
    exact coe_mul_of_left_le_normalizer_right _ _ ((map_subtype_le _).trans
      (hJnL.trans (normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 L))))
  have haE : a ∈ J ⊔ L := mem_sup_left haJ
  obtain ⟨hZ, hZcard⟩ := center_quotient_congr (oddCore_eq_pPrimeCore ↥(J ⊔ L)) hcenter hcard
  have hperf : Group.IsPerfect ↥(J ⊔ L) := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 J hJ
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 L hL
    rw [Subgroup.isPerfect_iff]
    refine le_antisymm (commutator_le.mpr fun x hx y hy => ?_) (sup_le ?_ ?_)
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    · calc J = ⁅J, J⁆ := Subgroup.commutator_eq_self.symm
        _ ≤ ⁅J ⊔ L, J ⊔ L⁆ := commutator_mono le_sup_left le_sup_left
    · calc L = ⁅L, L⁆ := Subgroup.commutator_eq_self.symm
        _ ≤ ⁅J ⊔ L, J ⊔ L⁆ := commutator_mono le_sup_right le_sup_right
  have : Group.IsPerfect (OddQuot (J ⊔ L)) := Group.IsPerfect.instQuotientSubgroup
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup H, K = (actA (J ⊔ L)).ker := ⟨_, rfl⟩
  have hK : ∀ h, h ∈ K ↔ ∀ e ∈ J ⊔ L, ⁅e, h⁆ ∈ oddCoreIn (J ⊔ L) := fun h => by
    rw [hKdef, MonoidHom.mem_ker, actA_eq_one_iff]
  have hKn : K.Normal := by
    rw [hKdef]
    infer_instance
  have hKN : K ≤ normalizer (J : Set H) := by
    intro h hh
    by_contra hhN
    have hc := hswap h hhN
    have : IsSimpleGroup ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L)) := hQL.2.1
    obtain ⟨y, hy⟩ := exists_ne (1 : (L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L))
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective w
    have hx : h * (l : H) * h⁻¹ ∈ J := by
      have hl : (l : H) ∈ conjugate J h := by
        rw [hc]
        exact l.2
      exact UnbalancedLayer.mem_conjugate_iff.mp hl
    have hcm := (hK h).mp hh l (hLE l.2)
    have hker : (⟨(l : H), hLE l.2⟩ : ↥(J ⊔ L)) * (⟨h * l * h⁻¹, hJE hx⟩ : ↥(J ⊔ L))⁻¹ ∈
        ν.ker := by
      rw [hνker, mem_subgroupOf]
      apply mem_sup_left
      rw [← hOeq]
      have he : (((⟨(l : H), hLE l.2⟩ : ↥(J ⊔ L)) *
          (⟨h * l * h⁻¹, hJE hx⟩ : ↥(J ⊔ L))⁻¹ : ↥(J ⊔ L)) : H) = ⁅(l : H), h⁆ := by
        show (l : H) * (h * l * h⁻¹)⁻¹ = _
        rw [commutatorElement_def]
        group
      rw [he]
      exact hcm
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hker
    have h3 := ((hνL l).symm.trans hker).trans (hνJ ⟨h * l * h⁻¹, hx⟩)
    exact hy (congrArg Prod.snd h3)
  have hNK : normalizer (J : Set H) ≤ normalizer (K : Set H) := fun g _ => by
    rw [normalizer_eq_top]
    exact mem_top g
  obtain ⟨TK, hTK⟩ := exists_sylow_inf_of_le_normalizer hSN hSsyl hKN hNK
  have hS2 : IsPGroup 2 S := by
    obtain ⟨T₀, hT₀⟩ := hSsyl
    have h := T₀.isPGroup'.map (normalizer (J : Set H)).subtype
    rwa [hT₀, subgroupOf_map_subtype, inf_of_le_left hSN] at h
  have hQN : UnbalancedLayer.coreActionKernel J ≤ normalizer (J : Set H) := fun g hg =>
    (UnbalancedLayer.mem_coreActionKernel.mp hg).1
  have : Fact ((S ⊓ UnbalancedLayer.coreActionKernel J : Subgroup H) ≤
      normalizer (L : Set H)) := ⟨inf_le_right.trans (hQN.trans hLN)⟩
  have hzZ : (⟨a, haL⟩ : L) ∈ center L :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp haZ g)
  obtain ⟨-, -, -, -, -, -, -, -, hCPD, -⟩ := semidihedral_quaternion_odd_quotient_action_kernel L
    (pPrimeCore 2 L) (Nat.coprime_two_left.mp pPrimeCore_coprime_card) hQL haL hzZ ha hZB
    (S ⊓ L) inf_le_right hDsyl hr hDQ (S ⊓ UnbalancedLayer.coreActionKernel J)
    (hS2.to_le inf_le_left) hDP hidx hn hPSD
  have hSK : S ⊓ K = zpowers a := by
    refine le_antisymm (fun x hx => ?_) (zpowers_le.mpr ⟨haS, (hK a).mpr fun e _ => ?_⟩)
    · obtain ⟨hxS, hxK⟩ := mem_inf.mp hx
      have hxN := hKN hxK
      have hcore : ∀ X : Subgroup H, X ≤ J ⊔ L → x ∈ normalizer (X : Set H) → ∀ y ∈ X,
          y⁻¹ * x⁻¹ * y * x ∈ oddCoreIn (J ⊔ L) ⊓ X := by
        intro X hXE hxX y hy
        refine mem_inf.mpr ⟨?_, ?_⟩
        · have h1 := (hK x⁻¹).mp (inv_mem hxK) y⁻¹ (hXE (inv_mem hy))
          rwa [commutatorElement_def, inv_inv, inv_inv] at h1
        · have h1 := (mem_normalizer_iff.mp (inv_mem hxX) y).mp hy
          rw [inv_inv] at h1
          rw [show y⁻¹ * x⁻¹ * y * x = y⁻¹ * (x⁻¹ * y * x) by group]
          exact mul_mem (inv_mem hy) h1
      have hxQ : x ∈ UnbalancedLayer.coreActionKernel J := by
        refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨hxN, fun j hj => ?_⟩
        have h := hcore J hJE hxN j hj
        rwa [hOeq, s2] at h
      rw [← hCPD]
      refine ⟨mem_centralizer_iff.mpr fun d hd => ?_, hxS, hxQ⟩
      have hdL := hcore L hLE (hLN hxN) d (mem_inf.mp hd).2
      rw [hOeq, s3] at hdL
      have hdS : d⁻¹ * x⁻¹ * d * x ∈ S :=
        mul_mem (mul_mem (mul_mem (inv_mem (mem_inf.mp hd).1) (inv_mem hxS)) (mem_inf.mp hd).1)
          hxS
      have hbot := UnbalancedLayer.eq_bot_of_le_two_group_of_le_odd hS2
        (odd_card_map_pPrimeCore_two L) (zpowers_le.mpr hdS) (zpowers_le.mpr hdL)
      have hc1 : d⁻¹ * x⁻¹ * d * x = 1 := by
        have h := mem_zpowers (d⁻¹ * x⁻¹ * d * x)
        rwa [hbot, mem_bot] at h
      calc d * x = x * d * (d⁻¹ * x⁻¹ * d * x) := by group
        _ = x * d := by rw [hc1, mul_one]
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp haZ e)]
      exact one_mem _
  have hPK : ∃ P : Sylow 2 K, Nat.card P = 2 := ⟨TK, by
    rw [hTK, Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : S ⊓ K ≤ K)).toEquiv, hSK,
      Nat.card_zpowers, ha]⟩
  obtain ⟨c1, ⟨-, -, c2c, c2d, c2e⟩, c3, c4, c5, c6, -, -, c9, c10, c11, c12⟩ :=
    perfect_odd_quotient_central_two_action_kernel (J ⊔ L) haE haZ ha hZ K hK hPK
  have hπs : Function.Surjective (quotT (J ⊔ L)) :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hπker : (quotT (J ⊔ L)).ker = ν.ker := by
    ext x
    rw [MonoidHom.mem_ker, hνker, mem_subgroupOf, ← hOeq,
      ← mk_mem_zpowers_iff (J ⊔ L) haE haZ x, ← hZ, quotT, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  let Θ := (QuotientGroup.quotientKerEquivOfSurjective _ hπs).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hπker).trans Ψ)
  have hΘ : ∀ x, Θ (quotT (J ⊔ L) x) = ν x := by
    intro x
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective _ hπs).symm (quotT (J ⊔ L) x) =
        (x : ↥(J ⊔ L) ⧸ (quotT (J ⊔ L)).ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    simp only [Θ, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk, hΨ]
  have hνJ' : ∀ (e : ↥(J ⊔ L)) (he : (e : H) ∈ J), ν e =
      ((((⟨e, he⟩ : J) : J ⧸ pPrimeCore 2 J) : (J ⧸ pPrimeCore 2 J) ⧸
        center (J ⧸ pPrimeCore 2 J)), 1) := fun e he => hνJ ⟨e, he⟩
  have hνL' : ∀ (e : ↥(J ⊔ L)) (he : (e : H) ∈ L), ν e =
      (1, (((⟨e, he⟩ : L) : L ⧸ pPrimeCore 2 L) : (L ⧸ pPrimeCore 2 L) ⧸
        center (L ⧸ pPrimeCore 2 L))) := fun e he => hνL ⟨e, he⟩
  have hΘJ : ∀ t ∈ factorImage (J ⊔ L) J, (Θ t).2 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [hΘ, hνJ' e (mem_subgroupOf.mp he)]
  have hΘL : ∀ t ∈ factorImage (J ⊔ L) L, (Θ t).1 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [hΘ, hνL' e (mem_subgroupOf.mp he)]
  let fJ : ↥(factorImage (J ⊔ L) J) →* (J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J) :=
    (MonoidHom.fst _ _).comp (Θ.toMonoidHom.comp (factorImage (J ⊔ L) J).subtype)
  have hfJinj : Function.Injective fJ := fun t t' htt => Subtype.ext (Θ.injective
    (Prod.ext htt ((hΘJ t t.2).trans (hΘJ t' t'.2).symm)))
  have hfJsurj : Function.Surjective fJ := by
    intro u
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective w
    refine ⟨⟨quotT (J ⊔ L) ⟨j, hJE j.2⟩, mem_map_of_mem _ (mem_subgroupOf.mpr j.2)⟩, ?_⟩
    show (Θ (quotT (J ⊔ L) ⟨j, hJE j.2⟩)).1 = _
    rw [hΘ, hνJ' _ j.2]
  let ιJ := MulEquiv.ofBijective fJ ⟨hfJinj, hfJsurj⟩
  let fL : ↥(factorImage (J ⊔ L) L) →* (L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L) :=
    (MonoidHom.snd _ _).comp (Θ.toMonoidHom.comp (factorImage (J ⊔ L) L).subtype)
  have hfLinj : Function.Injective fL := fun t t' htt => Subtype.ext (Θ.injective
    (Prod.ext ((hΘL t t.2).trans (hΘL t' t'.2).symm) htt))
  have hfLsurj : Function.Surjective fL := by
    intro u
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective w
    refine ⟨⟨quotT (J ⊔ L) ⟨l, hLE l.2⟩, mem_map_of_mem _ (mem_subgroupOf.mpr l.2)⟩, ?_⟩
    show (Θ (quotT (J ⊔ L) ⟨l, hLE l.2⟩)).2 = _
    rw [hΘ, hνL' _ l.2]
  let ιL := MulEquiv.ofBijective fL ⟨hfLinj, hfLsurj⟩
  have hιJ : ∀ (j : J) (x : ↥(J ⊔ L)) (t : factorImage (J ⊔ L) J), (x : H) = j →
      (t : OddQuotT (J ⊔ L)) = quotT (J ⊔ L) x →
        ιJ t = ((j : J ⧸ pPrimeCore 2 J) : (J ⧸ pPrimeCore 2 J) ⧸
          center (J ⧸ pPrimeCore 2 J)) := by
    intro j x t hxj htx
    have hxJ : (x : H) ∈ J := hxj ▸ j.2
    show (Θ t).1 = _
    rw [htx, hΘ, hνJ' x hxJ, show (⟨(x : H), hxJ⟩ : J) = j from Subtype.ext hxj]
  have hιL : ∀ (l : L) (x : ↥(J ⊔ L)) (t : factorImage (J ⊔ L) L), (x : H) = l →
      (t : OddQuotT (J ⊔ L)) = quotT (J ⊔ L) x →
        ιL t = ((l : L ⧸ pPrimeCore 2 L) : (L ⧸ pPrimeCore 2 L) ⧸
          center (L ⧸ pPrimeCore 2 L)) := by
    intro l x t hxl htx
    have hxL : (x : H) ∈ L := hxl ▸ l.2
    show (Θ t).2 = _
    rw [htx, hΘ, hνL' x hxL, show (⟨(x : H), hxL⟩ : L) = l from Subtype.ext hxl]
  have : IsSimpleGroup ((J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J)) := hQJ.2.1
  have : IsSimpleGroup ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L)) := hQL.2.1
  have hsimpJ : IsSimpleGroup ↥(factorImage (J ⊔ L) J) := ιJ.isSimpleGroup
  have hsimpL : IsSimpleGroup ↥(factorImage (J ⊔ L) L) := ιL.isSimpleGroup
  have hnabJ : ∃ x y : ↥(factorImage (J ⊔ L) J), x * y ≠ y * x := by
    obtain ⟨u, v, huv⟩ := hQJ.2.2
    refine ⟨ιJ.symm u, ιJ.symm v, fun h => huv ?_⟩
    have h1 := congrArg ιJ h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  have hnabL : ∃ x y : ↥(factorImage (J ⊔ L) L), x * y ≠ y * x := by
    obtain ⟨u, v, huv⟩ := hQL.2.2
    refine ⟨ιL.symm u, ιL.symm v, fun h => huv ?_⟩
    have h1 := congrArg ιL h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  have hΘx : ∀ t : factorImage (J ⊔ L) J, Θ t = (ιJ t, 1) := fun t =>
    Prod.ext rfl (hΘJ t t.2)
  have hΘy : ∀ t : factorImage (J ⊔ L) L, Θ t = (1, ιL t) := fun t =>
    Prod.ext (hΘL t t.2) rfl
  have hφ : ∀ x y, ((ιJ.prodCongr ιL).trans Θ.symm) (x, y) = (x : OddQuotT (J ⊔ L)) * y := by
    intro x y
    show Θ.symm (ιJ x, ιL y) = _
    rw [MulEquiv.symm_apply_eq, map_mul, hΘx, hΘy, Prod.mk_mul_mk, mul_one, one_mul]
  have hdisjT : ∀ t, t ∈ factorImage (J ⊔ L) J → t ∈ factorImage (J ⊔ L) L → t = 1 := by
    intro t ht1 ht2
    apply Θ.injective
    rw [map_one]
    exact Prod.ext (hΘL t ht2) (hΘJ t ht1)
  have hcommT : ∀ x ∈ factorImage (J ⊔ L) J, ∀ y ∈ factorImage (J ⊔ L) L, x * y = y * x := by
    intro x hx y hy
    apply Θ.injective
    rw [map_mul, map_mul]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_mul, Prod.fst_mul, hΘL y hy, mul_one, one_mul]
    · rw [Prod.snd_mul, Prod.snd_mul, hΘJ x hx, mul_one, one_mul]
  have hTJne : factorImage (J ⊔ L) J ≠ factorImage (J ⊔ L) L := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(factorImage (J ⊔ L) J))
    exact hx (Subtype.ext (hdisjT x x.2 (h ▸ x.2)))
  have hβE : ∀ (x : H) (hx : x ∈ J ⊔ L),
      betaHom (J ⊔ L) x = MulAut.conj (quotT (J ⊔ L) ⟨x, hx⟩) :=
    fun x hx => betaHom_of_mem (J ⊔ L) ⟨x, hx⟩
  have hconjinj :
      Function.Injective (MulAut.conj : OddQuotT (J ⊔ L) →* MulAut (OddQuotT (J ⊔ L))) := by
    intro x y hxy
    have h1 : MulAut.conj (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    rw [conj_eq_one_iff_mem_center, c5, mem_bot] at h1
    exact mul_inv_eq_one.mp h1
  have hβin : ∀ X : Subgroup H, X ≤ J ⊔ L →
      (∀ x ∈ X, ∃ t ∈ factorImage (J ⊔ L) X, ∀ y ∈ factorImage (J ⊔ L) X,
        betaHom (J ⊔ L) x y = t * y * t⁻¹) ∧
      (∀ t ∈ factorImage (J ⊔ L) X, ∃ x ∈ X, ∀ y ∈ factorImage (J ⊔ L) X,
        betaHom (J ⊔ L) x y = t * y * t⁻¹) := by
    intro X hXE
    refine ⟨fun x hx => ⟨quotT (J ⊔ L) ⟨x, hXE hx⟩, mem_map_of_mem _ (mem_subgroupOf.mpr hx),
      fun y _ => by rw [hβE x (hXE hx), MulAut.conj_apply]⟩, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, mem_subgroupOf.mp he, fun y _ => by rw [hβE e e.2, MulAut.conj_apply]⟩
  have hβtriv : ∀ X Y : Subgroup H, X ≤ J ⊔ L →
      (∀ x ∈ factorImage (J ⊔ L) X, ∀ y ∈ factorImage (J ⊔ L) Y, x * y = y * x) →
        ∀ x ∈ X, ∀ y ∈ factorImage (J ⊔ L) Y, betaHom (J ⊔ L) x y = y := by
    intro X Y hXE hc x hx y hy
    rw [hβE x (hXE hx), MulAut.conj_apply,
      hc _ (mem_map_of_mem _ (mem_subgroupOf.mpr hx)) y hy, mul_inv_cancel_right]
  have hmapβ : ∀ (h : H) (X : Subgroup H),
      (factorImage (J ⊔ L) X).map (betaHom (J ⊔ L) h).toMonoidHom =
        factorImage (J ⊔ L) (conjugate X h⁻¹) := by
    intro h X
    ext t
    constructor
    · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
      refine ⟨MulAut.conjNormal h e, ?_, (betaHom_mk (J ⊔ L) h e).symm⟩
      rw [SetLike.mem_coe, mem_subgroupOf, MulAut.conjNormal_apply,
        UnbalancedLayer.mem_conjugate_iff, inv_inv,
        show h⁻¹ * (h * (e : H) * h⁻¹) * h = e by group]
      exact he
    · rintro ⟨e, he, rfl⟩
      refine ⟨quotT (J ⊔ L) (MulAut.conjNormal h⁻¹ e), mem_map_of_mem _ ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf, UnbalancedLayer.mem_conjugate_iff] at he
        rw [mem_subgroupOf, MulAut.conjNormal_apply]
        exact he
      · have h1 : MulAut.conjNormal h (MulAut.conjNormal h⁻¹ e) = e := Subtype.ext (by
          rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
          group)
        calc (betaHom (J ⊔ L) h).toMonoidHom (quotT (J ⊔ L) (MulAut.conjNormal h⁻¹ e))
            = quotT (J ⊔ L) (MulAut.conjNormal h (MulAut.conjNormal h⁻¹ e)) :=
              betaHom_mk (J ⊔ L) h _
          _ = quotT (J ⊔ L) e := by rw [h1]
  have hpermN : ∀ h ∈ normalizer (J : Set H),
      (factorImage (J ⊔ L) J).map (betaHom (J ⊔ L) h).toMonoidHom = factorImage (J ⊔ L) J ∧
        (factorImage (J ⊔ L) L).map (betaHom (J ⊔ L) h).toMonoidHom =
          factorImage (J ⊔ L) L := fun h hh =>
    ⟨by rw [hmapβ, UnbalancedLayer.conjugate_eq_of_mem_normalizer (inv_mem hh)],
      by rw [hmapβ, UnbalancedLayer.conjugate_eq_of_mem_normalizer (hLN (inv_mem hh))]⟩
  have hpermout : ∀ h ∉ normalizer (J : Set H),
      (factorImage (J ⊔ L) J).map (betaHom (J ⊔ L) h).toMonoidHom = factorImage (J ⊔ L) L ∧
        (factorImage (J ⊔ L) L).map (betaHom (J ⊔ L) h).toMonoidHom =
          factorImage (J ⊔ L) J := fun h hh =>
    ⟨by rw [hmapβ, hswap h⁻¹ fun h' => hh (by simpa using inv_mem h')],
      by rw [hmapβ, (congrArg (fun X => conjugate X h⁻¹) (hswap h hh)).symm.trans
        (UnbalancedLayer.conjugate_conjugate_inv J h)]⟩
  have hβN : ∀ h : H, betaHom (J ⊔ L) h ∈ (normalizer (J : Set H)).map (betaHom (J ⊔ L)) ↔
      ((factorImage (J ⊔ L) J).map (betaHom (J ⊔ L) h).toMonoidHom = factorImage (J ⊔ L) J ∧
        (factorImage (J ⊔ L) L).map (betaHom (J ⊔ L) h).toMonoidHom =
          factorImage (J ⊔ L) L) := by
    intro h
    constructor
    · rintro ⟨g, hg, hgh⟩
      rw [← hgh]
      exact hpermN g hg
    · intro hfix
      by_cases hh : h ∈ normalizer (J : Set H)
      · exact mem_map_of_mem _ hh
      · exact absurd ((hpermout h hh).1.symm.trans hfix.1) hTJne.symm
  have hkerN : (betaHom (J ⊔ L)).ker ≤ normalizer (J : Set H) := by
    rw [c4]
    exact hKN
  have hidxβ : ((normalizer (J : Set H)).map (betaHom (J ⊔ L))).relIndex
      (betaHom (J ⊔ L)).range = 2 := by
    rw [MonoidHom.range_eq_map, relIndex_map_map, sup_eq_left.mpr hkerN, top_sup_eq,
      relIndex_top_right, hNidx]
  have hJβ : J.map (betaHom (J ⊔ L)) ≤ (J ⊔ L).map (betaHom (J ⊔ L)) := map_mono le_sup_left
  have hLβ : L.map (betaHom (J ⊔ L)) ≤ (J ⊔ L).map (betaHom (J ⊔ L)) := map_mono le_sup_right
  have hcommβ : ∀ x ∈ J, ∀ y ∈ L,
      betaHom (J ⊔ L) x * betaHom (J ⊔ L) y = betaHom (J ⊔ L) y * betaHom (J ⊔ L) x := by
    intro x hx y hy
    rw [hβE x (hJE hx), hβE y (hLE hy), ← map_mul MulAut.conj, ← map_mul MulAut.conj,
      hcommT _ (mem_map_of_mem (quotT (J ⊔ L))
        (mem_subgroupOf.mpr hx : (⟨x, hJE hx⟩ : ↥(J ⊔ L)) ∈ J.subgroupOf (J ⊔ L))) _
        (mem_map_of_mem (quotT (J ⊔ L))
          (mem_subgroupOf.mpr hy : (⟨y, hLE hy⟩ : ↥(J ⊔ L)) ∈ L.subgroupOf (J ⊔ L)))]
  let fβ := (inclusion hJβ).noncommCoprod (inclusion hLβ) (by
    rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    exact Subtype.ext (hcommβ x hx y hy))
  have hdisjβ : Disjoint (J.map (betaHom (J ⊔ L))) (L.map (betaHom (J ⊔ L))) := by
    rw [disjoint_def]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have h1 : quotT (J ⊔ L) ⟨y, hLE hy⟩ = quotT (J ⊔ L) ⟨x, hJE hx⟩ := hconjinj (by
      rw [← hβE, ← hβE]
      exact hyx)
    rw [hβE x (hJE hx), hdisjT _ (mem_map_of_mem _ (mem_subgroupOf.mpr hx))
      (h1 ▸ mem_map_of_mem _ (mem_subgroupOf.mpr hy)), map_one]
  have hfβinj : Function.Injective fβ := by
    intro p q hpq
    have h := congrArg (fun z : ↥((J ⊔ L).map (betaHom (J ⊔ L))) =>
      (z : MulAut (OddQuotT (J ⊔ L)))) hpq
    exact mul_injective_of_disjoint hdisjβ h
  have hfβsurj : Function.Surjective fβ := by
    rintro ⟨_, e, he, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_exists_mul hJnL).mp he
    exact ⟨(⟨_, mem_map_of_mem _ hx⟩, ⟨_, mem_map_of_mem _ hy⟩),
      Subtype.ext (map_mul _ x y).symm⟩
  refine ⟨hOeq, hOset, c1, ⟨a, haE⟩, rfl, hZ, hZcard, ⟨(ιJ.prodCongr ιL).trans Θ.symm, hφ⟩,
    ⟨hsimpJ, hnabJ⟩, ⟨hsimpL, hnabL⟩, ⟨ιJ, hιJ⟩, ⟨ιL, hιL⟩, c3, c4.trans c2c.symm, c2d, c2e,
    c6, ⟨MulEquiv.ofBijective fβ ⟨hfβinj, hfβsurj⟩, fun x y => rfl⟩, (hβin J hJE).1,
    (hβin J hJE).2, hβtriv J L hJE hcommT, (hβin L hLE).1, (hβin L hLE).2,
    hβtriv L J hLE (fun x hx y hy => (hcommT y hy x hx).symm), fun h => ?_, hβN, hidxβ,
    fun h hh => hpermout h fun hN => hh (mem_map_of_mem _ hN), c9, c10, c11, c12⟩
  by_cases hh : h ∈ normalizer (J : Set H)
  · exact Or.inl (hpermN h hh)
  · exact Or.inr (hpermout h hh)

end RankProjectiveAction

open RankProjectiveAction

theorem nonnormal_small_kernel_full_centralizer_projective_action {G : Type*} [Group G]
    [Finite G] {a : G} (ha : orderOf a = 2) {H : Subgroup G}
    (hH : H = centralizer ({a} : Set G)) {J : Subgroup H} (hJ : IsPComponent 2 J)
    (haJ : a ∈ J.map H.subtype) (hJrank : CFSG.pRank 2 J ≤ 1)
    (hQrank : CFSG.pRank 2 (UnbalancedLayer.coreActionKernel J) ≤ 2) (hJn : ¬ J.Normal)
    {S : Subgroup H} (hSN : S ≤ normalizer (J : Set H))
    (hSsyl : ∃ T : Sylow 2 (normalizer (J : Set H)),
      (T : Subgroup _) = S.subgroupOf (normalizer (J : Set H)))
    (hP : (∃ d : ℕ, 3 ≤ d ∧ Nonempty ((S ⊓ UnbalancedLayer.coreActionKernel J : Subgroup H) ≃*
        DihedralGroup (2 ^ (d - 1)))) ∨
      (∃ e : ℕ, 4 ≤ e ∧ Nonempty ((S ⊓ UnbalancedLayer.coreActionKernel J : Subgroup H) ≃*
        Open.SemidihedralGroup e))) :
    ∃ L : Subgroup H, ((∃ h, L = conjugate J h) ∧ L ≠ J) ∧
    (∀ L' : Subgroup H, (∃ h, L' = conjugate J h) → L' ≠ J → L' = L) ∧
    pLayer H 2 = J ⊔ L ∧ ((J ⊔ L : Subgroup H) : Set H) = (J : Set H) * L ∧
    (pLayer H 2).Normal ∧
    oddCoreIn (pLayer H 2) = (pPrimeCore 2 J).map J.subtype ⊔ (pPrimeCore 2 L).map L.subtype ∧
    ((oddCoreIn (pLayer H 2) : Subgroup H) : Set H) =
      ((pPrimeCore 2 J).map J.subtype : Set H) * ((pPrimeCore 2 L).map L.subtype : Set H) ∧
    CFSG.oddCore H ⊓ pLayer H 2 = oddCoreIn (pLayer H 2) ∧
    ∃ aE : pLayer H 2, ((aE : H) : G) = a ∧
      center (OddQuot (pLayer H 2)) = zpowers (aE : OddQuot (pLayer H 2)) ∧
      Nat.card (center (OddQuot (pLayer H 2))) = 2 ∧
      (∃ φ : ↥(factorImage (pLayer H 2) J) × ↥(factorImage (pLayer H 2) L) ≃*
          OddQuotT (pLayer H 2), ∀ x y, φ (x, y) = x * y) ∧
      (IsSimpleGroup ↥(factorImage (pLayer H 2) J) ∧
        ∃ x y : ↥(factorImage (pLayer H 2) J), x * y ≠ y * x) ∧
      (IsSimpleGroup ↥(factorImage (pLayer H 2) L) ∧
        ∃ x y : ↥(factorImage (pLayer H 2) L), x * y ≠ y * x) ∧
      (∃ ι : ↥(factorImage (pLayer H 2) J) ≃* (J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J),
        ∀ (j : J) (x : pLayer H 2) (t : factorImage (pLayer H 2) J), (x : H) = j →
          (t : OddQuotT (pLayer H 2)) = quotT (pLayer H 2) x →
            ι t = ((j : J ⧸ pPrimeCore 2 J) : (J ⧸ pPrimeCore 2 J) ⧸
              center (J ⧸ pPrimeCore 2 J))) ∧
      (∃ ι : ↥(factorImage (pLayer H 2) L) ≃* (L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L),
        ∀ (l : L) (x : pLayer H 2) (t : factorImage (pLayer H 2) L), (x : H) = l →
          (t : OddQuotT (pLayer H 2)) = quotT (pLayer H 2) x →
            ι t = ((l : L ⧸ pPrimeCore 2 L) : (L ⧸ pPrimeCore 2 L) ⧸
              center (L ⧸ pPrimeCore 2 L))) ∧
      (∀ (h : H) (e : pLayer H 2),
        betaHom (pLayer H 2) h ((e : OddQuot (pLayer H 2)) : OddQuotT (pLayer H 2)) =
          (((MulAut.conjNormal h e : pLayer H 2) : OddQuot (pLayer H 2)) :
            OddQuotT (pLayer H 2))) ∧
      (betaHom (pLayer H 2)).ker = CFSG.oddCore H ⊔ zpowers (aE : H) ∧
      CFSG.oddCore H ⊓ zpowers (aE : H) = ⊥ ∧
      (∀ x ∈ CFSG.oddCore H, ∀ y ∈ zpowers (aE : H), x * y = y * x) ∧
      (pLayer H 2).map (betaHom (pLayer H 2)) =
        (MulAut.conj : OddQuotT (pLayer H 2) →* MulAut (OddQuotT (pLayer H 2))).range ∧
      (∃ φ : ↥(J.map (betaHom (pLayer H 2))) × ↥(L.map (betaHom (pLayer H 2))) ≃*
          ↥((pLayer H 2).map (betaHom (pLayer H 2))),
        ∀ x y, (φ (x, y) : MulAut (OddQuotT (pLayer H 2))) = x * y) ∧
      (∀ j ∈ J, ∃ t ∈ factorImage (pLayer H 2) J, ∀ x ∈ factorImage (pLayer H 2) J,
        betaHom (pLayer H 2) j x = t * x * t⁻¹) ∧
      (∀ t ∈ factorImage (pLayer H 2) J, ∃ j ∈ J, ∀ x ∈ factorImage (pLayer H 2) J,
        betaHom (pLayer H 2) j x = t * x * t⁻¹) ∧
      (∀ j ∈ J, ∀ y ∈ factorImage (pLayer H 2) L, betaHom (pLayer H 2) j y = y) ∧
      (∀ l ∈ L, ∃ t ∈ factorImage (pLayer H 2) L, ∀ x ∈ factorImage (pLayer H 2) L,
        betaHom (pLayer H 2) l x = t * x * t⁻¹) ∧
      (∀ t ∈ factorImage (pLayer H 2) L, ∃ l ∈ L, ∀ x ∈ factorImage (pLayer H 2) L,
        betaHom (pLayer H 2) l x = t * x * t⁻¹) ∧
      (∀ l ∈ L, ∀ y ∈ factorImage (pLayer H 2) J, betaHom (pLayer H 2) l y = y) ∧
      (∀ h : H,
        ((factorImage (pLayer H 2) J).map (betaHom (pLayer H 2) h).toMonoidHom =
            factorImage (pLayer H 2) J ∧
          (factorImage (pLayer H 2) L).map (betaHom (pLayer H 2) h).toMonoidHom =
            factorImage (pLayer H 2) L) ∨
        ((factorImage (pLayer H 2) J).map (betaHom (pLayer H 2) h).toMonoidHom =
            factorImage (pLayer H 2) L ∧
          (factorImage (pLayer H 2) L).map (betaHom (pLayer H 2) h).toMonoidHom =
            factorImage (pLayer H 2) J)) ∧
      (∀ h : H, betaHom (pLayer H 2) h ∈ (normalizer (J : Set H)).map (betaHom (pLayer H 2)) ↔
        ((factorImage (pLayer H 2) J).map (betaHom (pLayer H 2) h).toMonoidHom =
            factorImage (pLayer H 2) J ∧
          (factorImage (pLayer H 2) L).map (betaHom (pLayer H 2) h).toMonoidHom =
            factorImage (pLayer H 2) L)) ∧
      ((normalizer (J : Set H)).map (betaHom (pLayer H 2))).relIndex
        (betaHom (pLayer H 2)).range = 2 ∧
      (∀ h : H, betaHom (pLayer H 2) h ∉ (normalizer (J : Set H)).map (betaHom (pLayer H 2)) →
        (factorImage (pLayer H 2) J).map (betaHom (pLayer H 2) h).toMonoidHom =
            factorImage (pLayer H 2) L ∧
          (factorImage (pLayer H 2) L).map (betaHom (pLayer H 2) h).toMonoidHom =
            factorImage (pLayer H 2) J) ∧
      ((pLayer H 2).map (QuotientGroup.mk' (CFSG.oddCore H))).Normal ∧
      (∃ ι : (pLayer H 2).map (QuotientGroup.mk' (CFSG.oddCore H)) ≃* OddQuot (pLayer H 2),
        ∀ e : pLayer H 2, ι ⟨QuotientGroup.mk' (CFSG.oddCore H) e, mem_map_of_mem _ e.2⟩ =
          (e : OddQuot (pLayer H 2))) ∧
      (∃ βbar : H ⧸ CFSG.oddCore H →* MulAut (OddQuotT (pLayer H 2)),
        (∀ h : H, βbar h = betaHom (pLayer H 2) h) ∧
        βbar.ker = zpowers (QuotientGroup.mk' (CFSG.oddCore H) (aE : H)) ∧
        zpowers (QuotientGroup.mk' (CFSG.oddCore H) (aE : H)) ≤ center (H ⧸ CFSG.oddCore H) ∧
        Nat.card (zpowers (QuotientGroup.mk' (CFSG.oddCore H) (aE : H))) = 2) ∧
      center (H ⧸ CFSG.oddCore H) = zpowers (QuotientGroup.mk' (CFSG.oddCore H) (aE : H)) := by
  subst hH
  have haH : a ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have ha' : orderOf (⟨a, haH⟩ : centralizer ({a} : Set G)) = 2 := by
    rw [Subgroup.orderOf_mk, ha]
  have ha'Z : (⟨a, haH⟩ : centralizer ({a} : Set G)) ∈ center (centralizer ({a} : Set G)) :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  have hmem : ∀ X : Subgroup (centralizer ({a} : Set G)),
      a ∈ X.map (centralizer ({a} : Set G)).subtype → (⟨a, haH⟩ : centralizer ({a} : Set G)) ∈ X :=
    fun X hX => by
      obtain ⟨x, hx, hxa⟩ := mem_map.mp hX
      rwa [show x = ⟨a, haH⟩ from Subtype.ext hxa] at hx
  obtain ⟨-, -, -, -, hnn⟩ :=
    UnbalancedLayer.rank_one_small_kernel_normal_or_two_conjugates ha hJ haJ hJrank hQrank
  obtain ⟨L, hL1, hL2, hNidx, -, -, hLN', hLc, haL, hLQ, hS⟩ := hnn hJn
  obtain ⟨-, hDsyl, ⟨r, hr, hDQ⟩, ⟨haD, -⟩, hDP, hshape⟩ := hS S hSN hSsyl
  obtain ⟨n, hn, hPSD, hidx⟩ := hshape hP
  have haS : (⟨a, haH⟩ : centralizer ({a} : Set G)) ∈ S := (mem_inf.mp (hmem _ haD)).1
  have hQN : UnbalancedLayer.coreActionKernel J ≤
      normalizer (J : Set (centralizer ({a} : Set G))) := fun g hg =>
    (UnbalancedLayer.mem_coreActionKernel.mp hg).1
  have hLN : normalizer (J : Set (centralizer ({a} : Set G))) ≤
      normalizer (L : Set (centralizer ({a} : Set G))) :=
    (normal_subgroupOf_iff_le_normalizer (hLQ.trans hQN)).mp hLN'
  have hswap : ∀ h, h ∉ normalizer (J : Set (centralizer ({a} : Set G))) →
      conjugate J h = L := fun h hh =>
    hL2 _ ⟨h, rfl⟩ fun he => hh (UnbalancedLayer.mem_normalizer_iff_conjugate_eq.mpr he)
  have hLrank : CFSG.pRank 2 L ≤ 1 := by
    obtain ⟨h₀, hh₀⟩ := hL1.1
    rw [hh₀]
    unfold conjugate
    rw [← UnbalancedLayer.pRank_eq_of_mulEquiv (by norm_num)
      (J.equivMapOfInjective _ (MulAut.conj h₀⁻¹).injective)]
    exact hJrank
  have hLn : (L.subgroupOf (UnbalancedLayer.coreActionKernel J)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLQ).mpr (hQN.trans hLN)
  have hPsyl := exists_sylow_inf_of_le_normalizer hSN hSsyl hQN
    (UnbalancedLayer.normalizer_le_normalizer_coreActionKernel J)
  have hPL : S ⊓ UnbalancedLayer.coreActionKernel J ⊓ L = S ⊓ L := by
    rw [inf_assoc, inf_eq_right.mpr hLQ]
  have hDQ' : Nonempty ((S ⊓ UnbalancedLayer.coreActionKernel J ⊓ L :
      Subgroup (centralizer ({a} : Set G))) ≃* QuaternionGroup (2 ^ (r - 2))) := by
    rw [hPL]
    exact hDQ
  have hidx' : (S ⊓ UnbalancedLayer.coreActionKernel J ⊓ L).relIndex
      (S ⊓ UnbalancedLayer.coreActionKernel J) = 2 := by
    rw [hPL]
    exact hidx
  obtain ⟨-, hE, hEset⟩ := UnbalancedLayer.semidihedral_action_kernel_exact_two_component_list
    hL1.2.symm hJ hLc hLQ hLn inf_le_right hPsyl hr hDQ' hidx' hn hPSD
  obtain ⟨o1, o2, o3, aE, haE, hrest⟩ := projective_action_of_sup ha' ha'Z hJ hLc hL1.2.symm
    (hmem _ haJ) (hmem _ haL) hJrank hLrank hswap hLN hNidx hSN hSsyl haS hDsyl hr hDQ hDP hidx
    hn hPSD (pLayer _ 2) hE
  exact ⟨L, hL1, hL2, hE, hEset, inferInstance, o1, o2, o3, aE, by rw [haE], hrest⟩

end CFSG.ComponentClassification.UnbalancedGS
