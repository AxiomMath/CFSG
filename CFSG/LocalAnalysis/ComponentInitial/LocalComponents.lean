module

public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isQuasisimple_congr {H : Type*} [Group H] (e : G ≃* H) :
    CFSG.IsQuasisimple G ↔ CFSG.IsQuasisimple H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem quasisimple_normal_subgroups {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ center Q := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  have hNmap : (N.map (QuotientGroup.mk' (center Q))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  have := hsimple
  rcases hNmap.eq_bot_or_eq_top with h | h
  · right
    intro n hn
    have : (QuotientGroup.mk' (center Q)) n = 1 := by
      rw [← mem_bot, ← h]
      exact mem_map_of_mem _ hn
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  · left
    have hdecomp : ∀ x : Q, ∃ n ∈ N, n⁻¹ * x ∈ center Q := fun x => by
      have hx : (QuotientGroup.mk' (center Q)) x ∈ N.map (QuotientGroup.mk' (center Q)) := by
        rw [h]; exact mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      refine ⟨n, hn, ?_⟩
      rw [← QuotientGroup.eq]
      exact hnx
    have hle : commutator Q ≤ N := by
      rw [commutator_def]
      refine (commutator_le).2 fun x _ y _ => ?_
      obtain ⟨n, hn, hzx⟩ := hdecomp x
      obtain ⟨m, hm, hzy⟩ := hdecomp y
      have hx : x = n * (n⁻¹ * x) := by group
      have hy : y = m * (m⁻¹ * y) := by group
      rw [hx, hy, CentralExtensions.commutator_mul_center_left _ _ _ hzx,
        CentralExtensions.commutator_mul_center_right _ _ _ hzy]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn hm) (N.inv_mem hn)) (N.inv_mem hm)
    exact eq_top_iff.2 (hperf.commutator_eq_top ▸ hle)

theorem quasisimple_normal_subgroups_assembly {Q : Type*} [Group Q]
    (hQ : CFSG.Assembly.IsQuasisimple Q) {N : Subgroup Q} (hN : N.Normal) :
    N = ⊤ ∨ N ≤ center Q :=
  quasisimple_normal_subgroups ((AssemblyBPredicates.isQuasisimple_iff_native Q).1 hQ) hN

theorem perfect_double_commutator {P X : Subgroup G} (hP : ⁅P, P⁆ = P)
    (h : ⁅⁅P, X⁆, P⁆ = ⊥) : ⁅P, X⁆ = ⊥ := by
  have h' : ⁅⁅X, P⁆, P⁆ = ⊥ := by rw [commutator_comm X P]; exact h
  have h3 := commutator_commutator_eq_bot_of_rotate h h'
  rwa [hP] at h3

theorem perfect_central_quotient_automorphism_faithful (L : Type*) [Group L]
    [Group.IsPerfect L] : Function.Injective (PerfectAutomorphisms.centerQuotientHom L) :=
  PerfectAutomorphisms.centerQuotientHom_injective L

theorem central_extension_derived {H : Type*} [Group H] {A : Subgroup H} [A.Normal]
    (hA : A ≤ center H) [Group.IsPerfect (H ⧸ A)] :
    commutator H ⊔ A = ⊤ ∧ Group.IsPerfect (commutator H) ∧
      Function.Surjective ((QuotientGroup.mk' A).comp (commutator H).subtype) := by
  have hker : (QuotientGroup.mk' A).ker ≤ center H := by rw [QuotientGroup.ker_mk']; exact hA
  have hsurj := QuotientGroup.mk'_surjective A
  refine ⟨?_, CentralExtensions.derived_perfect _ hsurj hker, ?_⟩
  · have hmap := CentralExtensions.derived_map_eq_top (QuotientGroup.mk' A) hsurj
    have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' A) (commutator H)
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
    exact hcomap.symm
  · intro y
    have hy : y ∈ (commutator H).map (QuotientGroup.mk' A) := by
      rw [CentralExtensions.derived_map_eq_top (QuotientGroup.mk' A) hsurj]; exact mem_top y
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩

theorem component_overgroup [Finite G] {K H : Subgroup G} (hK : CFSG.IsComponent K)
    (hKH : K ≤ H) : CFSG.IsComponent (K.subgroupOf H) :=
  ⟨(isQuasisimple_congr (subgroupOfEquivOfLe hKH)).2 hK.1, hK.2.subgroupOf⟩

theorem component_overgroup_assembly [Finite G] {K H : Subgroup G}
    (hK : CFSG.Assembly.IsComponentOf K ⊤) (hKH : K ≤ H) : CFSG.Assembly.IsComponentOf K H :=
  hK.of_le_of_le hKH le_top

theorem isComponentOf_iff_isComponent_subgroupOf {K H : Subgroup G} (hKH : K ≤ H) :
    CFSG.Assembly.IsComponentOf K H ↔ CFSG.IsComponent (K.subgroupOf H) := by
  have hq : CFSG.Assembly.IsQuasisimple K ↔ CFSG.IsQuasisimple (K.subgroupOf H) := by
    rw [AssemblyBPredicates.isQuasisimple_iff_native]
    exact isQuasisimple_congr (subgroupOfEquivOfLe hKH).symm
  unfold CFSG.Assembly.IsComponentOf CFSG.IsComponent
  rw [hq, CFSG.Assembly.IsSubnormal.iff_subgroupOf hKH]
  exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨hKH, h.2, h.1⟩⟩

theorem component_subnormal_lift [Finite G] {H : Subgroup G} (hH : H.IsSubnormal)
    {K : Subgroup H} (hK : CFSG.IsComponent K) : CFSG.IsComponent (K.map H.subtype) :=
  ⟨(isQuasisimple_congr (K.equivMapOfInjective H.subtype H.subtype_injective)).1 hK.1,
    hK.2.trans' hH⟩

theorem assembly_isSubnormal_trans {L M K : Subgroup G} (hLM : CFSG.Assembly.IsSubnormal L M)
    (hMK : CFSG.Assembly.IsSubnormal M K) : CFSG.Assembly.IsSubnormal L K :=
  hLM.trans hMK

theorem component_subnormal_lift_assembly {H K : Subgroup G}
    (hH : CFSG.Assembly.IsSubnormal H ⊤) (hK : CFSG.Assembly.IsComponentOf K H) :
    CFSG.Assembly.IsComponentOf K ⊤ :=
  ⟨le_top, assembly_isSubnormal_trans hK.2.1 hH, hK.2.2⟩

theorem isComponent_map_of_isComponent {H : Type*} [Group H] (f : G ≃* H) {K : Subgroup G}
    (hK : CFSG.IsComponent K) : CFSG.IsComponent (K.map f.toMonoidHom) :=
  ⟨(isQuasisimple_congr (K.equivMapOfInjective f.toMonoidHom f.injective)).1 hK.1,
    hK.2.map f.surjective⟩

theorem isComponent_map_iff {H : Type*} [Group H] (f : G ≃* H) (K : Subgroup G) :
    CFSG.IsComponent (K.map f.toMonoidHom) ↔ CFSG.IsComponent K := by
  refine ⟨fun h => ?_, isComponent_map_of_isComponent f⟩
  have h' := isComponent_map_of_isComponent f.symm h
  rwa [Subgroup.map_map, show f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id G from by
    ext; simp, Subgroup.map_id] at h'

theorem component_isomorphism [Finite G] {H : Type*} [Group H] [Finite H] (f : G ≃* H) :
    (∀ K : Subgroup G, CFSG.IsComponent K ↔ CFSG.IsComponent (K.map f.toMonoidHom)) ∧
      ∃ e : {K : Subgroup G // CFSG.IsComponent K} ≃ {L : Subgroup H // CFSG.IsComponent L},
        ∀ K, (e K : Subgroup H) = (K : Subgroup G).map f.toMonoidHom := by
  refine ⟨fun K => (isComponent_map_iff f K).symm, ?_⟩
  refine ⟨{ toFun := fun K => ⟨K.1.map f.toMonoidHom, isComponent_map_of_isComponent f K.2⟩
            invFun := fun L => ⟨L.1.map f.symm.toMonoidHom,
              isComponent_map_of_isComponent f.symm L.2⟩
            left_inv := fun K => Subtype.ext ?_
            right_inv := fun L => Subtype.ext ?_ }, fun K => rfl⟩
  · change (K.1.map f.toMonoidHom).map f.symm.toMonoidHom = K.1
    rw [Subgroup.map_map, show f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id G from by
      ext; simp, Subgroup.map_id]
  · change (L.1.map f.symm.toMonoidHom).map f.toMonoidHom = L.1
    rw [Subgroup.map_map, show f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id H from by
      ext; simp, Subgroup.map_id]

theorem commutator_inf_eq_bot_of_isSubnormal {K N H M : Subgroup G} (hN : N.Normal)
    (hKK : ⁅K, K⁆ = K) (hHM : CFSG.Assembly.IsSubnormal H M) (hKH : K ≤ H)
    (h0 : ⁅K, N ⊓ H⁆ = ⊥) : ⁅K, N ⊓ M⁆ = ⊥ := by
  induction hHM with
  | refl => exact h0
  | @step H M' M hle hnormal _ ih =>
    refine ih (hKH.trans hle) ?_
    have h1 : ⁅K, N ⊓ M'⁆ ≤ N ⊓ H := by
      refine (commutator_le).2 fun k hk x hx => ⟨?_, ?_⟩
      · exact (commutator_le_right K N) (commutator_mem_commutator hk hx.1)
      · have h3 : ⁅k, x⁆ = k * (x * k⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
        rw [h3]
        exact H.mul_mem (hKH hk)
          (((normal_subgroupOf_iff hle).1 hnormal) k⁻¹ x (H.inv_mem (hKH hk)) hx.2)
    have h2 : ⁅⁅K, N ⊓ M'⁆, K⁆ = ⊥ := by
      refine eq_bot_iff.2 ((commutator_mono h1 le_rfl).trans ?_)
      rw [commutator_comm, h0]
    exact perfect_double_commutator hKK h2

theorem component_normal_subgroup [Finite G] {K N : Subgroup G} (hK : CFSG.IsComponent K)
    (hN : N.Normal) : K ≤ N ∨ ⁅K, N⁆ = ⊥ := by
  have hKA := (AssemblyBPredicates.isQuasisimple_iff_native K).2 hK.1
  have hKK : ⁅K, K⁆ = K := by
    have h := congrArg (Subgroup.map K.subtype) hKA.1
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  have hNK : (N.subgroupOf K).Normal := hN.subgroupOf K
  rcases quasisimple_normal_subgroups hK.1 hNK with h | h
  · left
    rwa [Subgroup.subgroupOf_eq_top] at h
  · right
    have h0 : ⁅K, N ⊓ K⁆ = ⊥ := by
      refine eq_bot_iff.2 ((commutator_le).2 fun k hk x hx => ?_)
      have hxc : (⟨x, hx.2⟩ : K) ∈ center K := h hx.1
      have := mem_center_iff.1 hxc ⟨k, hk⟩
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val this
    have hchain := (AssemblyBPredicates.isSubnormal_top_iff_mathlib K).2 hK.2
    have := commutator_inf_eq_bot_of_isSubnormal hN hKK hchain le_rfl h0
    rwa [inf_top_eq] at this

theorem quasisimple_central_quotient {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {A : Subgroup Q} [A.Normal] (hA : A ≤ center Q) :
    CFSG.IsQuasisimple (Q ⧸ A) ∧ (center (Q ⧸ A)).comap (QuotientGroup.mk' A) = center Q ∧
      center (Q ⧸ A) = (center Q).map (QuotientGroup.mk' A) := by
  obtain ⟨hperf, hsimple, hnab⟩ := hQ
  have hsurj := QuotientGroup.mk'_surjective A
  have hker : (QuotientGroup.mk' A).ker ≤ center Q := by rw [QuotientGroup.ker_mk']; exact hA
  have hcomap := Quasisimple.center_comap_of_central_kernel (QuotientGroup.mk' A) hsurj hker
  have hmap : center (Q ⧸ A) = (center Q).map (QuotientGroup.mk' A) := by
    rw [← hcomap, Subgroup.map_comap_eq_self_of_surjective hsurj]
  let φ := (QuotientGroup.mk' (center (Q ⧸ A))).comp (QuotientGroup.mk' A)
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hsurj
  have hφker : φ.ker = center Q := by
    rw [← hcomap]
    ext x
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_comap,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let e : Q ⧸ center Q ≃* (Q ⧸ A) ⧸ center (Q ⧸ A) := QuotientGroup.liftEquiv _ hφ hφker.symm
  refine ⟨⟨Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' A) hsurj,
    e.isSimpleGroup_congr.1 hsimple, ?_⟩, hcomap, hmap⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩

theorem quasisimple_central_extension_derived {H : Type*} [Group H] {A : Subgroup H} [A.Normal]
    (hA : A ≤ center H) (hHA : CFSG.IsQuasisimple (H ⧸ A)) :
    CFSG.IsQuasisimple (commutator H) := by
  rw [← AssemblyBPredicates.isQuasisimple_iff_native] at hHA ⊢
  have hker : (QuotientGroup.mk' A).ker ≤ center H := by rw [QuotientGroup.ker_mk']; exact hA
  exact CentralExtensions.derived_quasisimple hHA (QuotientGroup.mk' A)
    (QuotientGroup.mk'_surjective A) hker

theorem quasisimple_subnormal_subgroups {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {H : Subgroup Q} (hH : H.IsSubnormal) : H = ⊤ ∨ H ≤ center Q := by
  have hQA := (AssemblyBPredicates.isQuasisimple_iff_native Q).2 hQ
  have hchain := (AssemblyBPredicates.isSubnormal_iff_open H ⊤).1
    ((AssemblyBPredicates.isSubnormal_top_iff_mathlib H).2 hH)
  exact (Quasisimple.subnormal_le_center_or_eq_top hQA H hchain).symm

theorem quasisimple_homomorphic_images {Q H : Type*} [Group Q] [Group H]
    (hQ : CFSG.IsQuasisimple Q) (f : Q →* H) : f.range = ⊥ ∨ CFSG.IsQuasisimple f.range := by
  rcases quasisimple_normal_subgroups hQ f.normal_ker with h | h
  · left
    rw [MonoidHom.range_eq_bot_iff, ← MonoidHom.ker_eq_top_iff]
    exact h
  · right
    have hq := (quasisimple_central_quotient hQ h).1
    exact (isQuasisimple_congr (QuotientGroup.quotientKerEquivRange f)).1 hq

theorem subnormal_prime_core_component_criterion {X : Type*} [Group X] [Finite X]
    (ϖ : Set Nat.Primes) {L : Subgroup X} (hL : L.IsSubnormal) :
    (∃ e : L ⧸ piCore ϖ L ≃* L.map (QuotientGroup.mk' (piCore ϖ X)),
      ∀ l : L, (e (l : L ⧸ piCore ϖ L) : X ⧸ piCore ϖ X) = ((l : X) : X ⧸ piCore ϖ X)) ∧
      (CFSG.IsComponent (L.map (QuotientGroup.mk' (piCore ϖ X))) ↔
        CFSG.IsQuasisimple (L ⧸ piCore ϖ L)) := by
  set q := QuotientGroup.mk' (piCore ϖ X)
  let f : L →* L.map q := (q.comp L.subtype).codRestrict _ fun l => mem_map_of_mem q l.2
  have hf : Function.Surjective f := by
    rintro ⟨_, l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩
  have hker : f.ker = piCore ϖ L := by
    have hint := CFSG.LocalCores.prime_set_core_subnormal_intersection ϖ hL
    ext l
    rw [MonoidHom.mem_ker, ← Subtype.coe_inj]
    change q (l : X) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hl
      have hmem : (l : X) ∈ L ⊓ piCore ϖ X := ⟨l.2, hl⟩
      rw [← hint] at hmem
      obtain ⟨l', hl', hll'⟩ := hmem
      rwa [show l' = l from Subtype.ext hll'] at hl'
    · intro hl
      have hmem : (l : X) ∈ (piCore ϖ L).map L.subtype := mem_map_of_mem _ hl
      rw [hint] at hmem
      exact hmem.2
  let e : L ⧸ piCore ϖ L ≃* L.map q :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨⟨e, fun l => rfl⟩, ?_⟩
  have hsub : (L.map q).IsSubnormal := hL.map (QuotientGroup.mk'_surjective _)
  constructor
  · intro h
    exact (isQuasisimple_congr e).2 h.1
  · intro h
    exact ⟨(isQuasisimple_congr e).1 h, hsub⟩

theorem isPComponent_map_of_isPComponent {H : Type*} [Group H] (p : ℕ) (f : G ≃* H)
    {L : Subgroup G} (hL : CFSG.IsPComponent p L) : CFSG.IsPComponent p (L.map f.toMonoidHom) := by
  obtain ⟨K, hK, hLs, hLK, hmin⟩ := hL
  let fb : G ⧸ CFSG.pPrimeCore p G ≃* H ⧸ CFSG.pPrimeCore p H :=
    QuotientGroup.congr _ _ f (CFSG.pPrimeCore_map_iso p f)
  have hcomm : (QuotientGroup.mk' (CFSG.pPrimeCore p H)).comp f.toMonoidHom =
      fb.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore p G)) := by
    ext x
    rfl
  have hmapmap : ∀ J : Subgroup G, (J.map f.toMonoidHom).map (QuotientGroup.mk' _) =
      (J.map (QuotientGroup.mk' (CFSG.pPrimeCore p G))).map fb.toMonoidHom := fun J => by
    rw [Subgroup.map_map, Subgroup.map_map, hcomm]
  refine ⟨K.map fb.toMonoidHom, isComponent_map_of_isComponent fb hK, hLs.map f.surjective, ?_,
    fun J' hJ' hJ's => ?_⟩
  · rw [hmapmap, hLK]
  · set J := J'.map f.symm.toMonoidHom
    have hJ'eq : J.map f.toMonoidHom = J' := by
      rw [Subgroup.map_map, show f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id H from by
        ext; simp, Subgroup.map_id]
    have hLeq : (L.map f.toMonoidHom).map f.symm.toMonoidHom = L := by
      rw [Subgroup.map_map, show f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id G from by
        ext; simp, Subgroup.map_id]
    have hJL : J < L := by
      refine lt_of_le_of_ne ?_ ?_
      · rw [← hLeq]; exact Subgroup.map_mono hJ'.le
      · intro h; apply hJ'.ne; rw [← hJ'eq, h]
    have hJs : J.IsSubnormal := hJ's.map f.symm.surjective
    intro heq
    apply hmin J hJL hJs
    rw [← hJ'eq, hmapmap] at heq
    exact Subgroup.map_injective fb.injective heq

theorem p_component_isomorphism_transport [Finite G] {H : Type*} [Group H] [Finite H] (p : ℕ)
    (_hp : p.Prime) (f : G ≃* H) :
    (∀ L : Subgroup G, CFSG.IsPComponent p L ↔ CFSG.IsPComponent p (L.map f.toMonoidHom)) ∧
      ∃ e : {L : Subgroup G // CFSG.IsPComponent p L} ≃ {L : Subgroup H // CFSG.IsPComponent p L},
        ∀ L, (e L : Subgroup H) = (L : Subgroup G).map f.toMonoidHom := by
  have hback : ∀ L : Subgroup G,
      (L.map f.toMonoidHom).map f.symm.toMonoidHom = L := fun L => by
    rw [Subgroup.map_map, show f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id G from by
      ext; simp, Subgroup.map_id]
  have hfwd : ∀ L : Subgroup H,
      (L.map f.symm.toMonoidHom).map f.toMonoidHom = L := fun L => by
    rw [Subgroup.map_map, show f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id H from by
      ext; simp, Subgroup.map_id]
  refine ⟨fun L => ⟨isPComponent_map_of_isPComponent p f, fun h => ?_⟩, ?_⟩
  · have := isPComponent_map_of_isPComponent p f.symm h
    rwa [hback] at this
  · refine ⟨{ toFun := fun L => ⟨L.1.map f.toMonoidHom, isPComponent_map_of_isPComponent p f L.2⟩
              invFun := fun L => ⟨L.1.map f.symm.toMonoidHom,
                isPComponent_map_of_isPComponent p f.symm L.2⟩
              left_inv := fun L => Subtype.ext (hback L.1)
              right_inv := fun L => Subtype.ext (hfwd L.1) }, fun L => rfl⟩

theorem component_quotient_image [Finite G] {N : Subgroup G} [N.Normal] {K : Subgroup G}
    (hK : CFSG.IsComponent K) (hKN : ¬ K ≤ N) :
    CFSG.IsComponent (K.map (QuotientGroup.mk' N)) := by
  set f := (QuotientGroup.mk' N).comp K.subtype
  have hrange : f.range = K.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rcases quasisimple_homomorphic_images hK.1 f with h | h
  · exfalso
    apply hKN
    intro k hk
    have hk' : f ⟨k, hk⟩ = 1 := by
      have : f ⟨k, hk⟩ ∈ f.range := ⟨⟨k, hk⟩, rfl⟩
      rw [h, mem_bot] at this
      exact this
    rw [← QuotientGroup.ker_mk' N]
    exact hk'
  · refine ⟨?_, hK.2.map (QuotientGroup.mk'_surjective N)⟩
    rw [← hrange]
    exact h

end CFSG.LocalAnalysis.ComponentInitial
