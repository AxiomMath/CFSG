module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aKernel
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerTwoLayerOrbitLocation
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyCentralizers

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace B5a

variable {G : Type*} [Group G]

omit [Group G] in
theorem mem_normalizer_sup [Group G] {A C : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hC : g ∈ normalizer (C : Set G)) :
    g ∈ normalizer ((A ⊔ C : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hC ⊢
  rw [Subgroup.map_sup, hA, hC]

theorem conjClosure_le {T Y L : Subgroup G} (hT : T ≤ L) (hY : Y ≤ normalizer (L : Set G)) :
    conjClosure T Y ≤ L :=
  iSup₂_le fun _ hy => (map_mono hT).trans (conjugate_eq_of_mem_normalizer (hY hy)).le

theorem le_conjClosure (T Y : Subgroup G) : T ≤ conjClosure T Y := by
  have h1 : conjugate T 1 ≤ conjClosure T Y := le_iSup₂_of_le (1 : G) (one_mem Y) le_rfl
  rwa [conjugate_one] at h1

theorem conjugate_conjClosure_le {T Y : Subgroup G} {g : G} (hg : g ∈ Y) :
    conjugate (conjClosure T Y) g ≤ conjClosure T Y := by
  unfold conjClosure
  change (⨆ y ∈ Y, conjugate T y).map (MulAut.conj g⁻¹).toMonoidHom ≤ _
  rw [Subgroup.map_iSup]
  refine iSup_le fun y => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hy => ?_
  change conjugate (conjugate T y) g ≤ _
  rw [conjugate_conjugate]
  exact le_iSup₂_of_le (y * g) (mul_mem hy hg) le_rfl

theorem le_normalizer_conjClosure (T Y : Subgroup G) :
    Y ≤ normalizer (conjClosure T Y : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    apply conjugate_conjClosure_le (inv_mem hg)
    rw [mem_conjugate_iff, inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    exact hx
  · intro hx
    apply conjugate_conjClosure_le hg
    rw [mem_conjugate_iff]
    exact hx

theorem mem_normalizer_centralizer {L : Subgroup G} {g : G}
    (hg : g ∈ normalizer (L : Set G)) : g ∈ normalizer (centralizer (L : Set G) : Set G) := by
  rw [mem_normalizer_iff]
  intro c
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hc l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (mem_normalizer_iff.mp (inv_mem hg) l).mp hl
      rwa [inv_inv] at this
    have h1 := hc _ hl'
    calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * l := by group
  · intro hc l hl
    have hl' : g * l * g⁻¹ ∈ L := (mem_normalizer_iff.mp hg l).mp hl
    have h1 := hc _ hl'
    have h2 : g * (l * c) * g⁻¹ = g * (c * l) * g⁻¹ := by
      calc g * (l * c) * g⁻¹ = (g * l * g⁻¹) * (g * c * g⁻¹) := by group
        _ = (g * c * g⁻¹) * (g * l * g⁻¹) := h1
        _ = g * (c * l) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem centralizer_le_coreActionKernel (L : Subgroup G) :
    centralizer (L : Set G) ≤ coreActionKernel L := by
  intro g hg
  refine mem_coreActionKernel.mpr ⟨centralizer_le_normalizer _ hg, fun j hj => ?_⟩
  have hc : j * g⁻¹ = g⁻¹ * j := mem_centralizer_iff.mp (inv_mem hg) j hj
  rw [show j⁻¹ * g⁻¹ * j * g = 1 by
    rw [show j⁻¹ * g⁻¹ * j * g = j⁻¹ * (g⁻¹ * j) * g by group, ← hc]; group]
  exact one_mem _

variable [Finite G]

theorem isPerfect_of_isPComponent_subgroupOf {J C : Subgroup G} (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) : Group.IsPerfect J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hJ
  exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJC).toMonoidHom)
    (subgroupOfEquivOfLe hJC).surjective

theorem nontrivial_of_isPComponent_subgroupOf {J C : Subgroup G} (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) : Nontrivial J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).1 hJ
  have := isQuasisimple_nontrivial hq
  have : Nontrivial (J.subgroupOf C) :=
    (QuotientGroup.mk'_surjective (pPrimeCore 2 (J.subgroupOf C))).nontrivial
  exact (subgroupOfEquivOfLe hJC).symm.surjective.nontrivial

omit [Finite G] in
theorem not_forall_commute_of_isPerfect {J : Subgroup G} [Group.IsPerfect J] [Nontrivial J] :
    ¬ ∀ u ∈ J, ∀ v ∈ J, u * v = v * u := by
  intro hc
  exact Group.IsPerfect.not_isSolvable (G := J)
    (Group.isSolvable_of_comm fun u v => Subtype.ext (hc u u.2 v v.2))

theorem isComponent_of_isPComponent (hO : pPrimeCore 2 G = ⊥) {M : Subgroup G}
    (hM : IsPComponent 2 M) : IsComponent M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).1 hM
  have hcore : pPrimeCore 2 M = ⊥ := by
    have h1 := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hs
    rw [hO, inf_bot_eq] at h1
    exact (map_eq_bot_iff_of_injective _ M.subtype_injective).mp h1
  refine ⟨?_, hs⟩
  have e : M ⧸ pPrimeCore 2 M ≃* M :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1 hq

theorem pPrimeCore_eq_bot_of_isComponent (hO : pPrimeCore 2 G = ⊥) {M : Subgroup G}
    (hM : IsComponent M) : pPrimeCore 2 M = ⊥ := by
  have h1 := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hM.2
  rw [hO, inf_bot_eq] at h1
  exact (map_eq_bot_iff_of_injective _ M.subtype_injective).mp h1

theorem odd_card_of_normal_of_inf_sylow {N : Subgroup G} [N.Normal] (U : Sylow 2 G)
    (hUN : (U : Subgroup G) ⊓ N = ⊥) : ¬ 2 ∣ Nat.card N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := Glauberman.sylow_inf_normal U (N := N)
  rw [hUN, bot_subgroupOf] at hP
  have h1 := P.card_eq_multiplicity
  rw [show Nat.card P = Nat.card (P : Subgroup N) from rfl, hP, card_bot] at h1
  intro h2
  have h3 : 1 ≤ (Nat.card N).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp (by rwa [pow_one])
  have h4 : 2 ^ (Nat.card N).factorization 2 ≠ 1 :=
    (Nat.one_lt_pow (by omega) one_lt_two).ne'
  exact h4 h1.symm

theorem eq_bot_of_normal_of_inf_sylow (hO : pPrimeCore 2 G = ⊥) {N : Subgroup G} [N.Normal]
    (U : Sylow 2 G) (hUN : (U : Subgroup G) ⊓ N = ⊥) : N = ⊥ := by
  have hle : N ≤ pPrimeCore 2 G :=
    le_sSup ⟨inferInstance, Nat.prime_two.coprime_iff_not_dvd.mpr
      (odd_card_of_normal_of_inf_sylow U hUN)⟩
  rwa [hO, le_bot_iff] at hle

theorem inf_sylow_ne_bot_of_isComponent {K : Subgroup G} (hK : IsComponent K) (U : Sylow 2 G) :
    (U : Subgroup G) ⊓ K ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hUK
  have : (layer G).Characteristic := layer_characteristic
  have : (layer G).Normal := inferInstance
  obtain ⟨hKE, hKn⟩ := components_normal_in_layer hK
  obtain ⟨P, hP⟩ := Glauberman.sylow_inf_normal U (N := layer G)
  have hbot : (P : Subgroup (layer G)) ⊓ K.subgroupOf (layer G) = ⊥ := by
    rw [hP, eq_bot_iff]
    rintro ⟨y, hyE⟩ ⟨hy1, hy2⟩
    have hy : y ∈ (U : Subgroup G) ⊓ K :=
      mem_inf.mpr ⟨(mem_inf.mp (mem_subgroupOf.mp hy1)).1, mem_subgroupOf.mp hy2⟩
    rw [hUK, mem_bot] at hy
    exact (mem_bot).mpr (Subtype.ext hy)
  have hodd := odd_card_of_normal_of_inf_sylow P hbot
  rw [show Nat.card (K.subgroupOf (layer G)) = Nat.card K from
    Nat.card_congr (subgroupOfEquivOfLe hKE).toEquiv] at hodd
  have hsolv : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (by omega))
  have : Nontrivial K := isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect K := hK.1.1
  exact Group.IsPerfect.not_isSolvable (G := K) hsolv

section Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem isQuasisimple_J : IsQuasisimple (h.J ⧸ pPrimeCore 2 h.J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).1 h.isPComponent_J
  exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe h.J_le))).1 hq

theorem isPComponent_fixedLayer :
    IsPComponent 2 ((GSLit.fixedLayer h.J h.B).subgroupOf
      (centralizer ({h.a} : Set H) ⊓ centralizer (h.B : Set H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hs, -, -⟩ := id h.isPComponent_J
  exact GSLit.fixedLayer_isPComponent h.J_le hs
    (h.B_le.trans (inf_le_left.trans (h.S_le.trans inf_le_left)))
    (h.B_le.trans inf_le_right) (isPGroup_B h) (isQuasisimple_J h)

theorem fixedLayer_ne_bot : GSLit.fixedLayer h.J h.B ≠ ⊥ := by
  intro hbot
  have := nontrivial_of_isPComponent_subgroupOf
    ((GSLit.fixedLayer_le_inf h.J h.B).trans (inf_le_inf_right _ h.J_le))
    (isPComponent_fixedLayer h)
  rw [hbot] at this
  exact not_nontrivial (⊥ : Subgroup H) this

theorem fixedLayer_le_V : GSLit.fixedLayer h.J h.B ≤ h.V := by
  show GSLit.fixedLayer h.J h.B ≤ layerIn (normalizer (h.B : Set H))
  rw [← h.conjClosure_eq]
  exact le_conjClosure _ _

theorem V_le_layerIn_centralizer : h.V ≤ layerIn (centralizer (h.B : Set H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := LBalance.lBalancePLayer_normalizer_le_centralizer (p := 2) h.B (isPGroup_B h)
  rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h1
  exact h1

theorem V_le_centralizer : h.V ≤ centralizer (h.B : Set H) :=
  (V_le_layerIn_centralizer h).trans (map_subtype_le _)

theorem a_not_mem_B : h.a ∉ h.B := by
  intro haB
  have hcomm : ⁅h.V, zpowers h.a⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq]
    exact (V_le_centralizer h).trans (centralizer_le (Set.singleton_subset_iff.mpr haB))
  rw [h.commutator_eq] at hcomm
  exact fixedLayer_ne_bot h (le_bot_iff.mp (hcomm ▸ fixedLayer_le_V h))

theorem J_le_pLayer : h.J ≤ pLayer H 2 := by
  have h1 : h.J ≤ (pLayer ↥(centralizer ({h.a} : Set H)) 2).map
      (centralizer ({h.a} : Set H)).subtype := by
    have h2 : h.J.subgroupOf (centralizer ({h.a} : Set H)) ≤
        pLayer ↥(centralizer ({h.a} : Set H)) 2 := le_sSup h.isPComponent_J
    have h3 := map_mono (f := (centralizer ({h.a} : Set H)).subtype) h2
    rwa [map_subgroupOf_eq_of_le h.J_le] at h3
  have hza : IsPGroup 2 (zpowers h.a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, h.orderOf_a, pow_one])
  have h4 := ClassicalInvolution.l2PrimeBalance H (zpowers h.a) hza
  rw [centralizer_zpowers_eq] at h4
  exact h1.trans h4

theorem V_le_pLayer : h.V ≤ pLayer H 2 :=
  (V_le_layerIn_centralizer h).trans (ClassicalInvolution.l2PrimeBalance H h.B (isPGroup_B h))

end Hyp52

section Swap

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem le_centralizer_sup {X A C : Subgroup H} (hA : X ≤ centralizer (A : Set H))
    (hC : X ≤ centralizer (C : Set H)) : X ≤ centralizer ((A ⊔ C : Subgroup H) : Set H) := by
  rw [le_centralizer_iff] at hA hC ⊢
  exact sup_le hA hC

omit [Finite H] in
theorem eq_one_of_isPerfect {M : Type*} [Group M] [Group.IsPerfect M] (c : M →* H)
    (hc : ∀ u v : M, c u * c v = c v * c u) (u : M) : c u = 1 := by
  have hle : commutator M ≤ c.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc g₁ g₂
  rw [Group.IsPerfect.commutator_eq_top] at hle
  exact hle (mem_top u)

omit [Finite H] in
theorem mem_centralizer_of_diagonal {M : Subgroup H} (hM : IsComponent M) {t g : H}
    (hcomm : ∀ m ∈ M, ∀ w ∈ conjugate M t, m * w = w * m)
    (hgM : g ∈ normalizer (M : Set H)) (hgMt : g ∈ normalizer (conjugate M t : Set H))
    (hgd : ∀ u ∈ M, g * (u * (t⁻¹ * u * t)) * g⁻¹ = u * (t⁻¹ * u * t)) :
    g ∈ centralizer ((M ⊔ conjugate M t : Subgroup H) : Set H) := by
  have hcM : ∀ u ∈ M, u⁻¹ * (g * u * g⁻¹) ∈ M ⊓ conjugate M t := by
    intro u hu
    have h1 : g * u * g⁻¹ ∈ M := (mem_normalizer_iff.mp hgM u).mp hu
    have h2 : g * (t⁻¹ * u * t) * g⁻¹ ∈ conjugate M t :=
      (mem_normalizer_iff.mp hgMt _).mp (conj_mem_conjugate hu t)
    have heq : u⁻¹ * (g * u * g⁻¹) = (t⁻¹ * u * t) * (g * (t⁻¹ * u * t) * g⁻¹)⁻¹ := by
      have h3 := hgd u hu
      rw [show g * (u * (t⁻¹ * u * t)) * g⁻¹ = (g * u * g⁻¹) * (g * (t⁻¹ * u * t) * g⁻¹) by
        group] at h3
      calc u⁻¹ * (g * u * g⁻¹) = u⁻¹ * ((g * u * g⁻¹) * (g * (t⁻¹ * u * t) * g⁻¹)) *
            (g * (t⁻¹ * u * t) * g⁻¹)⁻¹ := by group
        _ = u⁻¹ * (u * (t⁻¹ * u * t)) * (g * (t⁻¹ * u * t) * g⁻¹)⁻¹ := by rw [h3]
        _ = (t⁻¹ * u * t) * (g * (t⁻¹ * u * t) * g⁻¹)⁻¹ := by group
    refine mem_inf.mpr ⟨mul_mem (inv_mem hu) h1, ?_⟩
    rw [heq]
    exact mul_mem (conj_mem_conjugate hu t) (inv_mem h2)
  have hcentral : ∀ d ∈ M ⊓ conjugate M t, ∀ m ∈ M, d * m = m * d := fun d hd m hm =>
    (hcomm m hm d (mem_inf.mp hd).2).symm
  let c : ↥M →* H :=
    { toFun := fun u => (u : H)⁻¹ * (g * u * g⁻¹)
      map_one' := by simp
      map_mul' := by
        intro u v
        have hv := hcentral _ (hcM u u.2) (v : H)⁻¹ (inv_mem v.2)
        simp only [coe_mul]
        calc ((u : H) * v)⁻¹ * (g * (u * v) * g⁻¹)
            = (v : H)⁻¹ * ((u : H)⁻¹ * (g * u * g⁻¹)) * (g * v * g⁻¹) := by group
          _ = ((u : H)⁻¹ * (g * u * g⁻¹)) * (v : H)⁻¹ * (g * v * g⁻¹) := by rw [← hv]
          _ = (u : H)⁻¹ * (g * u * g⁻¹) * ((v : H)⁻¹ * (g * v * g⁻¹)) := by group }
  have : Group.IsPerfect M := hM.1.1
  have hc1 : ∀ u : ↥M, c u = 1 := eq_one_of_isPerfect c fun u v =>
    hcentral _ (hcM u u.2) _ (mem_inf.mp (hcM v v.2)).1
  have hgu : ∀ u ∈ M, g * u * g⁻¹ = u := by
    intro u hu
    have h1 : (u : H)⁻¹ * (g * u * g⁻¹) = 1 := hc1 ⟨u, hu⟩
    calc g * u * g⁻¹ = u * (u⁻¹ * (g * u * g⁻¹)) := by group
      _ = u := by rw [h1, mul_one]
  have hgw : ∀ u ∈ M, g * (t⁻¹ * u * t) * g⁻¹ = t⁻¹ * u * t := by
    intro u hu
    have h3 := hgd u hu
    rw [show g * (u * (t⁻¹ * u * t)) * g⁻¹ = (g * u * g⁻¹) * (g * (t⁻¹ * u * t) * g⁻¹) by group,
      hgu u hu] at h3
    exact mul_left_cancel h3
  have hgC : ∀ y ∈ M ⊔ conjugate M t, g * y * g⁻¹ = y := by
    intro y hy
    have hle : M ⊔ conjugate M t ≤ centralizer ({g} : Set H) := by
      refine sup_le (fun u hu => ?_) (fun w hw => ?_)
      · rw [mem_centralizer_singleton_iff]
        have := hgu u hu
        calc u * g = g * u * g⁻¹ * g := by rw [this]
          _ = g * u := by group
      · rw [mem_centralizer_singleton_iff]
        obtain ⟨u, hu, rfl⟩ : ∃ u ∈ M, t⁻¹ * u * t = w := ⟨t * w * t⁻¹,
          (mem_conjugate_iff.mp hw), by group⟩
        have := hgw u hu
        calc (t⁻¹ * u * t) * g = g * (t⁻¹ * u * t) * g⁻¹ * g := by rw [this]
          _ = g * (t⁻¹ * u * t) := by group
    have h1 := mem_centralizer_singleton_iff.mp (hle hy)
    calc g * y * g⁻¹ = y * g * g⁻¹ := by rw [← h1]
      _ = y := by group
  rw [mem_centralizer_iff]
  intro y hy
  have := hgC y hy
  calc y * g = g * y * g⁻¹ * g := by rw [this]
    _ = g * y := by group

omit [Finite H] in
theorem mem_sup_iff_of_commute {A C : Subgroup H} (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    {y : H} : y ∈ A ⊔ C ↔ ∃ a ∈ A, ∃ c ∈ C, a * c = y := by
  have hc : ∀ (a : A) (c : C), Commute (A.subtype a) (C.subtype c) := fun a c => hcomm a a.2 c c.2
  have hrange := MonoidHom.noncommCoprod_range A.subtype C.subtype hc
  rw [range_subtype, range_subtype] at hrange
  rw [← hrange]
  constructor
  · rintro ⟨⟨a, c⟩, rfl⟩
    exact ⟨a, a.2, c, c.2, rfl⟩
  · rintro ⟨a, ha, c, hc', rfl⟩
    exact ⟨(⟨a, ha⟩, ⟨c, hc'⟩), rfl⟩

omit [Finite H] in
theorem commutatorElement_mul_left_of_commute {z x w : H} (hx : Commute z x)
    (hw : Commute z w) : ⁅z * x, w⁆ = ⁅x, w⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h1 : Commute z (x * w * x⁻¹) := (hx.mul_right hw).mul_right hx.inv_right
  calc z * x * w * (z * x)⁻¹ * w⁻¹ = z * (x * w * x⁻¹) * z⁻¹ * w⁻¹ := by group
    _ = (x * w * x⁻¹) * z * z⁻¹ * w⁻¹ := by rw [h1.eq]
    _ = x * w * x⁻¹ * w⁻¹ := by group

omit [Finite H] in
theorem commutatorElement_mul_right_of_commute {z x w : H} (hx : Commute z x)
    (hw : Commute z w) : ⁅w, z * x⁆ = ⁅w, x⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_left_of_commute hx hw, commutatorElement_inv]

omit [Finite H] in
theorem commutator_self_of_isPerfect {J : Subgroup H} [Group.IsPerfect J] : ⁅J, J⁆ = J := by
  have h1 : (commutator J).map J.subtype = J := by
    rw [Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h1
  exact h1

theorem diagonal_of_swap {M J : Subgroup H} (hM : IsComponent M) (hcore : pPrimeCore 2 M = ⊥)
    {t : H} (ht : t * t = 1) (hcomm : ∀ m ∈ M, ∀ w ∈ conjugate M t, m * w = w * m)
    (hJL : J ≤ (M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H))
    (hJ : IsPComponent 2 (J.subgroupOf ((M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H)))) :
    (∀ u ∈ M, u * (t⁻¹ * u * t) ∈ J) ∧ pPrimeCore 2 J = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set C := (M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H) with hC
  let δ : ↥M →* H :=
    { toFun := fun u => (u : H) * (t⁻¹ * u * t)
      map_one' := by simp
      map_mul' := fun u v => by
        simp only [coe_mul]
        have hc := hcomm v v.2 (t⁻¹ * u * t) (conj_mem_conjugate u.2 t)
        calc (u : H) * v * (t⁻¹ * (u * v) * t) = u * (v * (t⁻¹ * u * t)) * (t⁻¹ * v * t) := by
              group
          _ = u * ((t⁻¹ * u * t) * v) * (t⁻¹ * v * t) := by rw [hc]
          _ = u * (t⁻¹ * u * t) * (v * (t⁻¹ * v * t)) := by group }
  have hδ : ∀ u : ↥M, δ u = (u : H) * (t⁻¹ * u * t) := fun u => rfl
  have hδC : ∀ u : ↥M, δ u ∈ C := by
    intro u
    refine mem_inf.mpr ⟨mul_mem (mem_sup_left u.2) (mem_sup_right (conj_mem_conjugate u.2 t)), ?_⟩
    rw [mem_centralizer_singleton_iff, hδ]
    have hc := hcomm u u.2 (t⁻¹ * u * t) (conj_mem_conjugate u.2 t)
    calc (u : H) * (t⁻¹ * u * t) * t = u * t⁻¹ * u * (t * t) := by group
      _ = u * t * u := by rw [ht, mul_one, htinv]
      _ = t * ((t⁻¹ * u * t) * u) := by group
      _ = t * ((u : H) * (t⁻¹ * u * t)) := by rw [hc]
  have hdc : ∀ d ∈ M ⊓ conjugate M t, ∀ y ∈ M ⊔ conjugate M t, Commute d y := by
    intro d hd y hy
    obtain ⟨m, hm, w, hw, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hy
    have h1 : Commute d m := (hcomm m hm d (mem_inf.mp hd).2).symm
    have h2 : Commute d w := hcomm d (mem_inf.mp hd).1 w hw
    exact h1.mul_right h2
  have hdec : ∀ k ∈ C, ∃ d ∈ M ⊓ conjugate M t, ∃ v : ↥M, k = d * δ v := by
    intro k hk
    obtain ⟨hkL, hkt⟩ := mem_inf.mp hk
    obtain ⟨m, hm, w, hw, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hkL
    have hv : t * w * t⁻¹ ∈ M := mem_conjugate_iff.mp hw
    refine ⟨m * (t * w * t⁻¹)⁻¹, ?_, ⟨t * w * t⁻¹, hv⟩, ?_⟩
    · have hdM : m * (t * w * t⁻¹)⁻¹ ∈ M := mul_mem hm (inv_mem hv)
      refine mem_inf.mpr ⟨hdM, ?_⟩
      have hdt : m * (t * w * t⁻¹)⁻¹ ∈ centralizer ({t} : Set H) := by
        have hδv := (mem_inf.mp (hδC ⟨t * w * t⁻¹, hv⟩)).2
        have h1 : m * (t * w * t⁻¹)⁻¹ = (m * w) * (δ ⟨t * w * t⁻¹, hv⟩)⁻¹ := by
          rw [hδ]
          simp only
          group
        rw [h1]
        exact mul_mem hkt (inv_mem hδv)
      have h2 := conj_mem_conjugate hdM t
      have h3 : t⁻¹ * (m * (t * w * t⁻¹)⁻¹) * t = m * (t * w * t⁻¹)⁻¹ :=
        mem_centralizer_singleton_iff_conj.mp hdt
      rwa [h3] at h2
    · rw [hδ]
      simp only
      group
  have : Group.IsPerfect J := isPerfect_of_isPComponent_subgroupOf hJL hJ
  have hJnt : Nontrivial J := nontrivial_of_isPComponent_subgroupOf hJL hJ
  have hJΔ : J ≤ δ.range := by
    rw [← commutator_self_of_isPerfect (J := J), Subgroup.commutator_le]
    intro j₁ hj₁ j₂ hj₂
    obtain ⟨d₁, hd₁, v₁, rfl⟩ := hdec j₁ (hJL hj₁)
    obtain ⟨d₂, hd₂, v₂, rfl⟩ := hdec j₂ (hJL hj₂)
    have hδL : ∀ v : ↥M, δ v ∈ M ⊔ conjugate M t := fun v => (mem_inf.mp (hδC v)).1
    have hd₁L : d₁ ∈ M ⊔ conjugate M t := mem_sup_left (mem_inf.mp hd₁).1
    rw [commutatorElement_mul_left_of_commute (hdc d₁ hd₁ _ (hδL v₁))
      (hdc d₁ hd₁ _ (mul_mem (mem_sup_left (mem_inf.mp hd₂).1) (hδL v₂))),
      commutatorElement_mul_right_of_commute (hdc d₂ hd₂ _ (hδL v₂)) (hdc d₂ hd₂ _ (hδL v₁))]
    exact ⟨⁅v₁, v₂⁆, map_commutatorElement δ v₁ v₂⟩
  have hΔq : IsQuasisimple δ.range := by
    refine (LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hM.1 δ).resolve_left
      fun hbot => ?_
    rw [hbot] at hJΔ
    obtain ⟨j, hj⟩ := exists_ne (1 : J)
    exact hj (Subtype.ext (mem_bot.mp (hJΔ j.2)))
  have hΔJ : δ.range ≤ J := by
    have hΔC : δ.range ≤ C := by
      rintro _ ⟨u, rfl⟩
      exact hδC u
    have hsub : (J.subgroupOf δ.range).IsSubnormal := by
      obtain ⟨-, -, hs, -, -⟩ := id hJ
      have h1 := hs.comap (inclusion hΔC)
      have h2 : (J.subgroupOf C).comap (inclusion hΔC) = J.subgroupOf δ.range := by
        ext y
        rfl
      rwa [h2] at h1
    have htop : IsComponent (⊤ : Subgroup ↥δ.range) :=
      ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr Subgroup.topEquiv).2 hΔq,
        Subgroup.IsSubnormal.top⟩
    rcases component_subnormal_subgroup htop hsub with h1 | h1
    · intro y hy
      exact h1 (mem_top (⟨y, hy⟩ : δ.range))
    · exfalso
      refine not_forall_commute_of_isPerfect (J := J) fun u hu v hv => ?_
      have h2 : ⁅(⟨u, hJΔ hu⟩ : δ.range), (⟨v, hJΔ hv⟩ : δ.range)⁆ = 1 := by
        have h3 := commutator_mem_commutator (mem_top (⟨u, hJΔ hu⟩ : δ.range))
          (show (⟨v, hJΔ hv⟩ : δ.range) ∈ J.subgroupOf δ.range from hv)
        rwa [h1, mem_bot] at h3
      have h4 := congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.mp h2)
      exact h4
  have hOΔ : pPrimeCore 2 δ.range = ⊥ := by
    have hker : δ.rangeRestrict.ker ≤ center M := by
      intro u hu
      have hu1 : δ u = 1 := by
        rw [MonoidHom.mem_ker] at hu
        exact congrArg Subtype.val hu
      rw [hδ] at hu1
      have hw : (u : H) ∈ conjugate M t := by
        have h1 : t⁻¹ * u * t = (u : H)⁻¹ := eq_inv_of_mul_eq_one_right hu1
        have h2 := conj_mem_conjugate (inv_mem u.2) t
        rwa [show t⁻¹ * (u : H)⁻¹ * t = (t⁻¹ * u * t)⁻¹ by group, h1, inv_inv] at h2
      rw [mem_center_iff]
      intro m
      exact Subtype.ext (hcomm m m.2 u hw)
    have hker2 : IsPGroup 2 δ.rangeRestrict.ker := fun g =>
      UnbalancedGS.SwappedCentralProduct.pow_two_pow_eq_one_of_mem_center hcore (hker g.2) |>.imp
        fun k hk => Subtype.ext (by simpa using hk)
    have h1 := central_p_kernel_prime_core_image δ.rangeRestrict δ.rangeRestrict_surjective hker
      hker2
    rw [hcore, Subgroup.map_bot] at h1
    exact h1
  have hJeq : J = δ.range := le_antisymm hJΔ hΔJ
  refine ⟨fun u hu => hΔJ ⟨⟨u, hu⟩, rfl⟩, ?_⟩
  have h1 := pPrimeCore_map_iso 2 (MulEquiv.subgroupCongr hJeq).symm
  rw [hOΔ, Subgroup.map_bot] at h1
  exact h1.symm

end Swap

end B5a

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem generalizedFitting_simple :
    generalizedFitting H = conjClosure h.J (pLayer H 2) ∧
      IsSimpleGroup ↥(generalizedFitting H) ∧
      centralizer (conjClosure h.J (pLayer H 2) : Set H) = ⊥ ∧
      IsComponent (conjClosure h.J (pLayer H 2)) ∧
      ∀ L : Subgroup H, IsComponent L → L = conjClosure h.J (pLayer H 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := h.oddCore_eq_bot
  have hE : pLayer H 2 = layer H :=
    ClassicalInvolution.LBalanceProof.pLayer_eq_layer_of_pPrimeCore_eq_bot hO
  have hEc : (layer H).Characteristic := layer_characteristic
  have hEn : (layer H).Normal := inferInstance
  have ha2 : h.a * h.a = 1 := by rw [← sq, ← h.orderOf_a, pow_orderOf_eq_one]
  have hainv : h.a⁻¹ = h.a := inv_eq_of_mul_eq_one_right ha2
  have : Group.IsPerfect h.J := B5a.isPerfect_of_isPComponent_subgroupOf h.J_le h.isPComponent_J
  have : Nontrivial h.J := B5a.nontrivial_of_isPComponent_subgroupOf h.J_le h.isPComponent_J
  obtain ⟨M, hMc, hJM, hJMc⟩ := two_layer_fixed_component_orbit_location h.orderOf_a h.J_le
    h.isPComponent_J (B5a.J_le_pLayer h.toHyp52)
  have hM : IsComponent M := B5a.isComponent_of_isPComponent hO hMc
  have hMa : IsComponent (conjugate M h.a) := isComponent_conjugate hM h.a
  set L := M ⊔ conjugate M h.a with hL
  have hLE : L ≤ layer H := sup_le (component_le_layer hM) (component_le_layer hMa)
  have hEN : layer H ≤ normalizer (L : Set H) := fun g hg =>
    B5a.mem_normalizer_sup (layer_le_normalizer hM hg) (layer_le_normalizer hMa hg)
  have hVL : h.V ≤ L := by
    show layerIn (normalizer (h.B : Set H)) ≤ L
    rw [← h.conjClosure_eq]
    exact B5a.conjClosure_le ((GSLit.fixedLayer_le_inf h.J h.B).trans (inf_le_left.trans hJM))
      ((hE ▸ B5a.V_le_pLayer h.toHyp52).trans hEN)
  have hxJ : h.x ∈ normalizer (h.J : Set H) := (mem_inf.mp (h.S_le h.x_mem)).2
  have hxa : h.a * h.x = h.x * h.a :=
    (mem_centralizer_singleton_iff.mp (mem_inf.mp (h.S_le h.x_mem)).1).symm
  have hconj_ax : ∀ N : Subgroup H, conjugate (conjugate N h.a) h.x =
      conjugate (conjugate N h.x) h.a := fun N => by
    rw [conjugate_conjugate, conjugate_conjugate, hxa]
  have hJx : h.J ≤ conjugate L h.x := by
    rw [← conjugate_eq_of_mem_normalizer hxJ]
    exact map_mono hJM
  have hcase : conjugate M h.x = M ∨ conjugate M h.x = conjugate M h.a := by
    by_contra hne
    push Not at hne
    obtain ⟨hne1, hne2⟩ := hne
    have hMx : IsComponent (conjugate M h.x) := isComponent_conjugate hM h.x
    have hMxa : IsComponent (conjugate (conjugate M h.x) h.a) := isComponent_conjugate hMx h.a
    have hne3 : conjugate (conjugate M h.x) h.a ≠ M := by
      intro heq
      apply hne2
      have h1 := congrArg (fun N => conjugate N h.a) heq
      simp only [conjugate_conjugate, mul_assoc, ha2, mul_one] at h1
      exact h1
    have hne4 : conjugate (conjugate M h.x) h.a ≠ conjugate M h.a := by
      intro heq
      apply hne1
      have h1 := congrArg (fun N => conjugate N h.a) heq
      simp only [conjugate_conjugate, mul_assoc, ha2, mul_one, conjugate_one] at h1
      exact h1
    have hcomm : ∀ A C : Subgroup H, IsComponent A → IsComponent C → A ≠ C →
        A ≤ centralizer (C : Set H) := fun A C hA hC hAC => by
      rcases distinct_components_commute hA hC with h1 | h1
      · exact absurd h1 hAC
      · exact commutator_eq_bot_iff_le_centralizer.mp h1
    have hLx : conjugate L h.x ≤ centralizer (L : Set H) := by
      rw [hL, show conjugate (M ⊔ conjugate M h.a) h.x =
        conjugate M h.x ⊔ conjugate (conjugate M h.x) h.a by
          rw [← hconj_ax]; exact Subgroup.map_sup _ _ _]
      refine sup_le (B5a.le_centralizer_sup (hcomm _ _ hMx hM hne1)
          (hcomm _ _ hMx hMa hne2))
        (B5a.le_centralizer_sup (hcomm _ _ hMxa hM hne3) (hcomm _ _ hMxa hMa hne4))
    exact B5a.not_forall_commute_of_isPerfect (J := h.J) fun u hu v hv =>
      (mem_centralizer_iff.mp (hLx (hJx hu)) v (hJM hv)).symm
  have hxL : h.x ∈ normalizer (L : Set H) := by
    apply mem_normalizer_of_conjugate_eq
    change (M ⊔ conjugate M h.a).map (MulAut.conj h.x⁻¹).toMonoidHom = M ⊔ conjugate M h.a
    rw [Subgroup.map_sup]
    change conjugate M h.x ⊔ conjugate (conjugate M h.a) h.x = M ⊔ conjugate M h.a
    rw [hconj_ax]
    rcases hcase with h1 | h1
    · rw [h1]
    · rw [h1, conjugate_conjugate, ha2, conjugate_one, sup_comm]
  obtain ⟨U, hSU⟩ := (B5a.isPGroup_S h.toHyp52).exists_le_sylow
  have hUB : (U : Subgroup H) ⊓ coreActionKernel h.V ≤ h.B := by
    obtain ⟨hBC, R, hR⟩ := h.toHyp52.sylow_kernel
    have hp : IsPGroup 2 (((U : Subgroup H) ⊓ coreActionKernel h.V).subgroupOf
        (coreActionKernel h.V)) :=
      (U.isPGroup'.to_inf_left).comap_subtype
    have hle : (R : Subgroup _) ≤ ((U : Subgroup H) ⊓ coreActionKernel h.V).subgroupOf
        (coreActionKernel h.V) := by
      rw [hR]
      intro y hy
      exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hSU (h.B_le.trans inf_le_left hy), hBC hy⟩)
    have heq := R.is_maximal' hp hle
    intro y hy
    have h1 : (⟨y, (mem_inf.mp hy).2⟩ : coreActionKernel h.V) ∈ (R : Subgroup _) := by
      rw [← heq]
      exact hy
    rw [hR] at h1
    exact h1
  have hCU : (U : Subgroup H) ⊓ centralizer (L : Set H) = ⊥ := by
    have hCV : centralizer (L : Set H) ≤ coreActionKernel h.V :=
      (centralizer_le (SetLike.coe_subset_coe.mpr hVL)).trans
        (B5a.centralizer_le_coreActionKernel h.V)
    have hY : (U : Subgroup H) ⊓ centralizer (L : Set H) ≤ h.B :=
      (inf_le_inf_left _ hCV).trans hUB
    have hxU : h.x ∈ normalizer (((U : Subgroup H) ⊓ centralizer (L : Set H) : Subgroup H) :
        Set H) := by
      have h1 : h.x ∈ normalizer ((U : Subgroup H) : Set H) := le_normalizer (hSU h.x_mem)
      have h2 := B5a.mem_normalizer_centralizer hxL
      exact mem_normalizer_iff.mpr fun y => by
        rw [mem_inf, mem_inf]
        exact and_congr (mem_normalizer_iff.mp h1 y) (mem_normalizer_iff.mp h2 y)
    have hYx := conjugate_eq_of_mem_normalizer hxU
    refine le_bot_iff.mp ?_
    rw [← h.inf_conjugate_x]
    refine le_inf hY ?_
    rw [← hYx]
    exact map_mono hY
  have hcomp : ∀ K : Subgroup H, IsComponent K → K = M ∨ K = conjugate M h.a := by
    intro K hK
    by_contra hne
    push Not at hne
    have hKC : K ≤ centralizer (L : Set H) := by
      refine B5a.le_centralizer_sup ?_ ?_
      · rcases distinct_components_commute hK hM with h1 | h1
        · exact absurd h1 hne.1
        · exact commutator_eq_bot_iff_le_centralizer.mp h1
      · rcases distinct_components_commute hK hMa with h1 | h1
        · exact absurd h1 hne.2
        · exact commutator_eq_bot_iff_le_centralizer.mp h1
    exact B5a.inf_sylow_ne_bot_of_isComponent hK U
      (le_bot_iff.mp ((inf_le_inf_left _ hKC).trans hCU.le))
  have hlayer : layer H = L := by
    refine le_antisymm (sSup_le fun K hK => ?_) hLE
    rcases hcomp K hK with h1 | h1
    · rw [h1]
      exact le_sup_left
    · rw [h1]
      exact le_sup_right
  have hLn : L.Normal := hlayer ▸ hEn
  have hCL : centralizer (L : Set H) = ⊥ := B5a.eq_bot_of_normal_of_inf_sylow hO U hCU
  have hMM : conjugate M h.a = M := by
    by_contra hne
    have hcm : ∀ m ∈ M, ∀ w ∈ conjugate M h.a, m * w = w * m := by
      intro m hm w hw
      rcases distinct_components_commute hM hMa with h1 | h1
      · exact absurd h1.symm hne
      · exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h1 hm) w hw).symm
    obtain ⟨hdiag, hOJ⟩ := B5a.diagonal_of_swap hM (B5a.pPrimeCore_eq_bot_of_isComponent hO hM)
      ha2 hcm (le_inf hJM h.J_le) hJMc
    have hBJ : ∀ b ∈ h.B, ∀ j ∈ h.J, b * j = j * b := by
      intro b hb j hj
      have h1 := (mem_coreActionKernel.mp (h.B_le hb).2).2 j hj
      rw [hOJ, Subgroup.map_bot, mem_bot] at h1
      have h2 : b⁻¹ * j * b = j := by
        calc b⁻¹ * j * b = j * (j⁻¹ * b⁻¹ * j * b) := by group
          _ = j := by rw [h1, mul_one]
      calc b * j = b * (b⁻¹ * j * b) := by rw [h2]
        _ = j * b := by group
    have hkey : ∀ g : H, g ∈ normalizer (M : Set H) →
        g ∈ normalizer (conjugate M h.a : Set H) → (∀ j ∈ h.J, g * j = j * g) → g = 1 := by
      intro g hgM hgMa hgJ
      have h1 := B5a.mem_centralizer_of_diagonal hM hcm hgM hgMa fun u hu => by
        rw [hgJ _ (hdiag u hu), mul_inv_cancel_right]
      rw [← hL, hCL, mem_bot] at h1
      exact h1
    have hBN : ∀ g : H, g ∈ normalizer (L : Set H) → ∀ N : Subgroup H, IsComponent N →
        conjugate N g = M ∨ conjugate N g = conjugate M h.a := fun g _ N hN =>
      hcomp _ (isComponent_conjugate hN g)
    apply h.B_ne_bot
    rw [eq_bot_iff]
    intro b hb
    rw [mem_bot]
    have hbL : b ∈ normalizer (L : Set H) := by
      have : (L : Subgroup H).Normal := hLn
      rw [normalizer_eq_top]
      exact mem_top b
    rcases hBN b hbL M hM with h1 | h1
    ·
      have hbM : b ∈ normalizer (M : Set H) := mem_normalizer_of_conjugate_eq h1
      have hbMa : b ∈ normalizer (conjugate M h.a : Set H) := by
        rcases hBN b hbL _ hMa with h2 | h2
        · exfalso
          apply hne
          have h3 : conjugate M h.a = conjugate M b⁻¹ := by
            rw [← conjugate_conjugate_inv (conjugate M h.a) b, h2]
          have h4 : conjugate M b⁻¹ = M := by
            conv_lhs => rw [← h1]
            exact conjugate_conjugate_inv M b
          rw [h3, h4]
        · exact mem_normalizer_of_conjugate_eq h2
      exact hkey b hbM hbMa (hBJ b hb)
    ·
      exfalso
      have hbaM : conjugate M (b * h.a) = M := by
        rw [← conjugate_conjugate, h1, conjugate_conjugate, ha2, conjugate_one]
      have hbaL : b * h.a ∈ normalizer (L : Set H) := by
        have : (L : Subgroup H).Normal := hLn
        rw [normalizer_eq_top]
        exact mem_top _
      have hbaMa : b * h.a ∈ normalizer (conjugate M h.a : Set H) := by
        rcases hBN _ hbaL _ hMa with h2 | h2
        · exfalso
          apply hne
          have h3 : conjugate M h.a = conjugate M (b * h.a)⁻¹ := by
            rw [← conjugate_conjugate_inv (conjugate M h.a) (b * h.a), h2]
          have h4 : conjugate M (b * h.a)⁻¹ = M := by
            conv_lhs => rw [← hbaM]
            exact conjugate_conjugate_inv M (b * h.a)
          rw [h3, h4]
        · exact mem_normalizer_of_conjugate_eq h2
      have hbaJ : ∀ j ∈ h.J, b * h.a * j = j * (b * h.a) := by
        intro j hj
        have hja : h.a * j = j * h.a := (mem_centralizer_singleton_iff.mp (h.J_le hj)).symm
        rw [mul_assoc, hja, ← mul_assoc, hBJ b hb j hj, mul_assoc]
      have h5 := hkey _ (mem_normalizer_of_conjugate_eq hbaM) hbaMa hbaJ
      have hba : b = h.a := by
        rw [← hainv]
        exact eq_inv_of_mul_eq_one_left h5
      exact B5a.a_not_mem_B h.toHyp52 (hba ▸ hb)
  rw [hMM, sup_idem] at hL
  have hLM : L = M := hL
  rw [hLM] at hlayer hCL hJM
  have hJcl : conjClosure h.J (pLayer H 2) = M := by
    rw [hE, hlayer]
    refine le_antisymm (B5a.conjClosure_le hJM le_normalizer) ?_
    have hXM : conjClosure h.J M ≤ M := B5a.conjClosure_le hJM le_normalizer
    have hn : ((conjClosure h.J M).subgroupOf M).Normal :=
      (normal_subgroupOf_iff_le_normalizer hXM).mpr (B5a.le_normalizer_conjClosure _ _)
    rcases quasisimple_normal_subgroups hM.1 hn with h1 | h1
    · intro y hy
      have h2 : (⟨y, hy⟩ : M) ∈ (conjClosure h.J M).subgroupOf M := h1 ▸ mem_top _
      exact h2
    · exfalso
      refine B5a.not_forall_commute_of_isPerfect (J := h.J) fun u hu v hv => ?_
      have hu' : (⟨u, hJM hu⟩ : M) ∈ center M :=
        h1 (show (⟨u, hJM hu⟩ : M) ∈ (conjClosure h.J M).subgroupOf M from
          B5a.le_conjClosure _ _ hu)
      exact (congrArg Subtype.val (mem_center_iff.mp hu' ⟨v, hJM hv⟩)).symm
  have hF : fittingSubgroup H = ⊥ := by
    have h1 := fitting_layer_commute (G := H)
    rw [commutator_eq_bot_iff_le_centralizer, hlayer, hCL] at h1
    exact le_bot_iff.mp h1
  have hFs : generalizedFitting H = M := by
    rw [generalizedFitting, hF, hlayer, bot_sup_eq]
  have hZ : center M = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : (z : H) ∈ centralizer (M : Set H) := mem_centralizer_iff.mpr fun m hm =>
      congrArg Subtype.val (mem_center_iff.mp hz ⟨m, hm⟩)
    rw [hCL, mem_bot] at h1
    exact (mem_bot).mpr (Subtype.ext h1)
  have hsimple : IsSimpleGroup M := by
    have : IsSimpleGroup (M ⧸ center M) := hM.1.2.1
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  refine ⟨hFs.trans hJcl.symm, ?_, ?_, ?_, fun K hK => ?_⟩
  · rw [hFs]
    exact hsimple
  · rw [hJcl]
    exact hCL
  · rw [hJcl]
    exact hM
  · rw [hJcl]
    rcases hcomp K hK with h1 | h1
    · exact h1
    · rw [h1, hMM]

end Hyp59

end CFSG.ComponentClassification.GSThmB
