module

public import CFSG.FeitThompson.Representations.FixedWeightStabilizerIsCentralizer
public import CFSG.FeitThompson.Representations.CoprimeInvariantCharacterInductionSupport
public import CFSG.FeitThompson.Representations.AbelianNormalDetectingRestrictionSplit
public import CFSG.FeitThompson.Representations.FreeCentralSectionInducedLayerIrreducible
public import CFSG.FeitThompson.Foundations.SolvableHallExistence
public import CFSG.FeitThompson.Representations.AbelianPointStabilizersCharacterStabilizers

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise
open scoped ComplexOrder

variable {L : Type*} [Group L]

def coreCentralizer (N U : Subgroup L) : Subgroup L := U ⊓ centralizer (N : Set L)

theorem mem_coreCentralizer {N U : Subgroup L} {u : L} :
    u ∈ coreCentralizer N U ↔ u ∈ U ∧ ∀ n ∈ N, n * u = u * n := by
  simp only [coreCentralizer, mem_inf, mem_centralizer_iff, SetLike.mem_coe]

theorem coreCentralizer_le_left (N U : Subgroup L) : coreCentralizer N U ≤ U := inf_le_left

theorem coreCentralizer_le_centralizer (N U : Subgroup L) :
    coreCentralizer N U ≤ centralizer (N : Set L) := inf_le_right

def coreProduct (N U : Subgroup L) : Subgroup L := N ⊔ coreCentralizer N U

theorem coe_coreProduct (N U : Subgroup L) [N.Normal] :
    ((coreProduct N U : Subgroup L) : Set L) = (N : Set L) * (coreCentralizer N U : Set L) :=
  Subgroup.normal_mul N _

theorem le_coreProduct (N U : Subgroup L) : N ≤ coreProduct N U := le_sup_left

theorem coreCentralizer_le_coreProduct (N U : Subgroup L) :
    coreCentralizer N U ≤ coreProduct N U := le_sup_right

theorem coreProduct_le_sup (N U : Subgroup L) : coreProduct N U ≤ N ⊔ U :=
  sup_le le_sup_left ((coreCentralizer_le_left N U).trans le_sup_right)

private theorem mul_comm_of_mem (U : Subgroup L) [IsMulCommutative ↥U] {a b : L} (ha : a ∈ U)
    (hb : b ∈ U) : a * b = b * a :=
  congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥U) ⟨b, hb⟩)

theorem sup_le_centralizer_coreCentralizer (N U : Subgroup L) [N.Normal] [IsMulCommutative ↥U] :
    (N ⊔ U : Subgroup L) ≤ centralizer ((coreCentralizer N U : Subgroup L) : Set L) := by
  rw [le_centralizer_iff]
  intro c hc
  rw [mem_centralizer_iff]
  intro k hk
  have hk' : k ∈ (N : Set L) * (U : Set L) := by
    rw [← Subgroup.normal_mul N U]; exact hk
  obtain ⟨n, hn, u, hu, rfl⟩ := hk'
  obtain ⟨hcU, hcN⟩ := mem_coreCentralizer.1 hc
  have h1 : n * c = c * n := hcN n hn
  have h2 : u * c = c * u := mul_comm_of_mem U hu hcU
  calc n * u * c = n * (u * c) := mul_assoc ..
    _ = n * (c * u) := by rw [h2]
    _ = n * c * u := (mul_assoc ..).symm
    _ = c * n * u := by rw [h1]
    _ = c * (n * u) := mul_assoc ..

instance isMulCommutative_coreProduct (N U : Subgroup L) [N.Normal] [IsMulCommutative ↥N]
    [IsMulCommutative ↥U] : IsMulCommutative ↥(coreProduct N U) := by
  rw [← le_centralizer_iff_isMulCommutative]
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  have hxset : x ∈ (N : Set L) * (coreCentralizer N U : Set L) := by
    rw [← coe_coreProduct N U]; exact hx
  have hyset : y ∈ (N : Set L) * (coreCentralizer N U : Set L) := by
    rw [← coe_coreProduct N U]; exact hy
  obtain ⟨n, hn, c, hc, rfl⟩ := hxset
  obtain ⟨m, hm, d, hd, rfl⟩ := hyset
  obtain ⟨hcU, hcN⟩ := mem_coreCentralizer.1 hc
  obtain ⟨hdU, hdN⟩ := mem_coreCentralizer.1 hd
  have hnm : n * m = m * n := mul_comm_of_mem N hn hm
  have hcd : c * d = d * c := mul_comm_of_mem U hcU hdU
  calc m * d * (n * c) = m * (d * n) * c := by group
    _ = m * (n * d) * c := by rw [← hdN n hn]
    _ = m * n * (d * c) := by group
    _ = n * m * (c * d) := by rw [hnm, hcd]
    _ = n * (m * c) * d := by group
    _ = n * (c * m) * d := by rw [hcN m hm]
    _ = n * c * (m * d) := by group

private theorem mem_normalizer_sup {A B : Subgroup L} {g : L} (hA : g ∈ normalizer (A : Set L))
    (hB : g ∈ normalizer (B : Set L)) : g ∈ normalizer ((A ⊔ B : Subgroup L) : Set L) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem sup_le_normalizer_coreProduct (N U : Subgroup L) [N.Normal] [IsMulCommutative ↥U] :
    (N ⊔ U : Subgroup L) ≤ normalizer ((coreProduct N U : Subgroup L) : Set L) := by
  intro k hk
  refine mem_normalizer_sup ?_ ?_
  · rw [mem_normalizer_iff]
    refine fun n => ⟨fun h => ‹N.Normal›.conj_mem _ h k, fun h => ?_⟩
    have h2 := ‹N.Normal›.conj_mem _ h k⁻¹
    simpa [mul_assoc] using h2
  · exact centralizer_le_normalizer _ (sup_le_centralizer_coreCentralizer N U hk)

theorem coreProduct_normal_subgroupOf (N U : Subgroup L) [N.Normal] [IsMulCommutative ↥U] :
    ((coreProduct N U).subgroupOf (N ⊔ U)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (coreProduct_le_sup N U)).mpr
    (sup_le_normalizer_coreProduct N U)

private theorem card_mul_card_of_inf_eq_bot [Finite L] {A B : Subgroup L} [A.Normal]
    (h : A ⊓ B = ⊥) : Nat.card A * Nat.card B = Nat.card (A ⊔ B : Subgroup L) := by
  set K : Subgroup L := A ⊔ B with hK
  have hAK : A ≤ K := le_sup_left
  have hBK : B ≤ K := le_sup_right
  have : (A.subgroupOf K).Normal := ‹A.Normal›.subgroupOf K
  have hsup : A.subgroupOf K ⊔ B.subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAK hBK, ← hK, Subgroup.subgroupOf_self]
  have hdisj : Disjoint (A.subgroupOf K) (B.subgroupOf K) := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : L) ∈ A ⊓ B := ⟨mem_subgroupOf.1 hx.1, mem_subgroupOf.1 hx.2⟩
    rw [h] at hx'
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by simpa [Subgroup.mem_bot] using hx')
  have hcompl : (A.subgroupOf K).IsComplement' (B.subgroupOf K) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
    have h2 := Subgroup.normal_mul (A.subgroupOf K) (B.subgroupOf K)
    rw [← h2, hsup]
    simp
  have hres := hcompl.card_mul_card
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv] at hres

theorem card_coreProduct_mul_relIndex [Finite L] (N U : Subgroup L) [N.Normal]
    (hNU : N ⊓ U = ⊥) :
    Nat.card (coreProduct N U) * (coreCentralizer N U).relIndex U
      = Nat.card (N ⊔ U : Subgroup L) := by
  have hCU : coreCentralizer N U ≤ U := coreCentralizer_le_left N U
  have hNC : N ⊓ coreCentralizer N U = ⊥ :=
    le_antisymm (le_trans (inf_le_inf_left N hCU) hNU.le) bot_le
  have hT : Nat.card N * Nat.card (coreCentralizer N U) = Nat.card (coreProduct N U) :=
    card_mul_card_of_inf_eq_bot hNC
  have hK : Nat.card N * Nat.card U = Nat.card (N ⊔ U : Subgroup L) :=
    card_mul_card_of_inf_eq_bot hNU
  have hidx : (coreCentralizer N U).relIndex U * Nat.card (coreCentralizer N U)
      = Nat.card U := by
    have h := Subgroup.index_mul_card ((coreCentralizer N U).subgroupOf U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCU).toEquiv] at h
  calc Nat.card (coreProduct N U) * (coreCentralizer N U).relIndex U
      = Nat.card N * ((coreCentralizer N U).relIndex U * Nat.card (coreCentralizer N U)) := by
        rw [← hT]; ring
    _ = Nat.card N * Nat.card U := by rw [hidx]
    _ = Nat.card (N ⊔ U : Subgroup L) := hK

theorem indClassFun_one_eq_index {K : Type*} [Group K] [Fintype K] (H : Subgroup K)
    {θ : ↥H → ℂ} (h1 : θ 1 = 1) : indClassFun H θ 1 = (H.index : ℂ) := by
  have hHcard : (Nat.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h : ((H.index * Nat.card ↥H : ℕ) : ℂ) = (Nat.card K : ℂ) := by
    rw [Subgroup.index_mul_card H]
  rw [indClassFun_one, h1, mul_one, div_eq_iff hHcard, ← h]
  push_cast
  ring

theorem mem_coreProduct_iff {N U : Subgroup L} [N.Normal] {x : L} :
    x ∈ coreProduct N U ↔ ∃ n ∈ N, ∃ c ∈ coreCentralizer N U, x = n * c := by
  have h : x ∈ ((coreProduct N U : Subgroup L) : Set L) ↔
      x ∈ (N : Set L) * (coreCentralizer N U : Set L) := by rw [coe_coreProduct]
  simp only [SetLike.mem_coe] at h
  rw [h]
  exact ⟨fun ⟨n, hn, c, hc, he⟩ => ⟨n, hn, c, hc, he.symm⟩,
    fun ⟨n, hn, c, hc, he⟩ => ⟨n, hn, c, hc, he.symm⟩⟩

theorem coreProduct_le {N U X : Subgroup L} [N.Normal] (hN : N ≤ X)
    (hC : coreCentralizer N U ≤ X) : coreProduct N U ≤ X := fun x hx => by
  obtain ⟨n, hn, c, hc, rfl⟩ := mem_coreProduct_iff.1 hx
  exact mul_mem (hN hn) (hC hc)

theorem subgroupOf_le_coreProduct_subgroupOf (N U : Subgroup L) :
    N.subgroupOf (N ⊔ U) ≤ (coreProduct N U).subgroupOf (N ⊔ U) :=
  Subgroup.comap_mono (le_coreProduct N U)

instance isMulCommutative_coreProduct_subgroupOf (N U : Subgroup L) [N.Normal]
    [IsMulCommutative ↥N] [IsMulCommutative ↥U] :
    IsMulCommutative ↥((coreProduct N U).subgroupOf (N ⊔ U)) :=
  isMulCommutative_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (coreProduct_le_sup N U))

theorem mem_inertiaGroup_subgroupOf_iff {N K : Subgroup L} [N.Normal] (hNK : N ≤ K)
    {lam : ↥N →* ℂˣ} {k : ↥K} :
    k ∈ inertiaGroup (N.subgroupOf K)
        (fun y => (lam ((subgroupOfEquivOfLe hNK) y) : ℂ)) ↔
      (k : L) ∈ charInertia N lam := by
  rw [mem_inertiaGroup_iff_forall_conj, mem_charInertia]
  constructor
  · intro h
    refine ⟨mem_normalizer_coe_of_normal N _, fun m n hmn => ?_⟩
    set y : ↥(N.subgroupOf K) := ⟨⟨(n : L), hNK n.2⟩, Subgroup.mem_subgroupOf.2 n.2⟩ with hy
    have hval := h y
    have hc : (((MulAut.conjNormal (H := N.subgroupOf K) k⁻¹) y : ↥(N.subgroupOf K)) : ↥K)
        = k⁻¹ * (y : ↥K) * k := by rw [MulAut.conjNormal_apply]; simp
    have hcoe : (subgroupOfEquivOfLe hNK) ((MulAut.conjNormal k⁻¹) y) = m := by
      refine Subtype.ext ?_
      change ((((MulAut.conjNormal k⁻¹) y : ↥(N.subgroupOf K)) : ↥K) : L) = (m : L)
      rw [hmn, hc]; push_cast; simp [hy]
    have hcoe2 : (subgroupOfEquivOfLe hNK) y = n := Subtype.ext rfl
    rw [hcoe, hcoe2] at hval
    exact Units.ext hval
  · rintro ⟨-, h⟩ y
    refine congrArg Units.val (h _ _ ?_)
    change ((((MulAut.conjNormal k⁻¹) y : ↥(N.subgroupOf K)) : ↥K) : L)
      = (k : L)⁻¹ * (((y : ↥K) : L)) * (k : L)
    have hc : (((MulAut.conjNormal (H := N.subgroupOf K) k⁻¹) y : ↥(N.subgroupOf K)) : ↥K)
        = k⁻¹ * (y : ↥K) * k := by rw [MulAut.conjNormal_apply]; simp
    rw [hc]; push_cast; simp

theorem inertiaGroup_subgroupOf_eq_coreProduct {N U : Subgroup L} [N.Normal]
    [IsMulCommutative ↥N] {lam : ↥N →* ℂˣ}
    (hC : U ⊓ charInertia N lam = coreCentralizer N U) :
    inertiaGroup (N.subgroupOf (N ⊔ U))
        (fun y => (lam ((subgroupOfEquivOfLe (le_sup_left : N ≤ N ⊔ U)) y) : ℂ))
      = (coreProduct N U).subgroupOf (N ⊔ U) := by
  have hNc : N ≤ charInertia N lam :=
    (le_centralizer_iff_isMulCommutative.2 ‹IsMulCommutative ↥N›).trans centralizer_le_charInertia
  have hCc : coreCentralizer N U ≤ charInertia N lam :=
    (coreCentralizer_le_centralizer N U).trans centralizer_le_charInertia
  ext k
  rw [mem_inertiaGroup_subgroupOf_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro hk
    have hkK : (k : L) ∈ (N : Set L) * (U : Set L) := by
      rw [← Subgroup.normal_mul N U]; exact k.2
    obtain ⟨n, hn, u, hu, hnu⟩ := hkK
    have hu' : u ∈ charInertia N lam := by
      have he : u = n⁻¹ * (k : L) := by rw [← hnu]; group
      rw [he]
      exact mul_mem (inv_mem (hNc hn)) hk
    exact mem_coreProduct_iff.2 ⟨n, hn, u, hC ▸ Subgroup.mem_inf.2 ⟨hu, hu'⟩, hnu.symm⟩
  · exact fun hk => coreProduct_le hNc hCc hk

theorem inf_charInertia_eq_coreCentralizer {N U Q : Subgroup L} [N.Normal]
    [IsMulCommutative ↥U] (hQU : Q ≤ normalizer (U : Set L))
    {lam : ↥N →* ℂˣ} (hlam : lam ≠ 1)
    (hmin : ∀ M : Subgroup L, M ≤ N → U ≤ normalizer (M : Set L) →
      Q ≤ normalizer (M : Set L) → M = ⊥ ∨ M = N)
    (hQlam : ∀ t ∈ Q, ∀ (n : ↥N) (hn : t⁻¹ * (n : L) * t ∈ N),
      lam ⟨t⁻¹ * (n : L) * t, hn⟩ = lam n) :
    U ⊓ charInertia N lam = coreCentralizer N U := by
  have hAN : (U ⊔ Q : Subgroup L) ≤ normalizer (N : Set L) :=
    sup_le Subgroup.le_normalizer_of_normal Subgroup.le_normalizer_of_normal
  have hA : ((U ⊔ Q : Subgroup L) : Set L) = (U : Set L) * (Q : Set L) :=
    Subgroup.coe_mul_of_right_le_normalizer_left U Q hQU
  have hUnormal : (U.subgroupOf (U ⊔ Q)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hQU)
  have hmin' : ∀ M : Subgroup L, M ≤ N → (U ⊔ Q : Subgroup L) ≤ normalizer (M : Set L) →
      M = ⊥ ∨ M = N := fun M hMN hUQ =>
    hmin M hMN (le_sup_left.trans hUQ) (le_sup_right.trans hUQ)
  rw [inf_charInertia_eq_inf_centralizer hlam hAN hA hUnormal hmin' hQlam]
  ext u
  rw [mem_coreCentralizer, mem_inf, mem_centralizer_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun n hn => h2 n hn⟩, fun ⟨h1, h2⟩ => ⟨h1, fun n hn => h2 n hn⟩⟩

theorem eq_indClassFun_of_inertiaGroup_eq {K : Type*} [Group K] [Fintype K]
    {A T : Subgroup K} [A.Normal] [T.Normal] [Fintype ↥T] [IsMulCommutative ↥T] (hAT : A ≤ T)
    {χ : K → ℂ} (hχ : χ ∈ Irr K) {lam : ↥A → ℂ} (hI : inertiaGroup A lam ≤ T)
    {ψ : ↥T → ℂ} (hψ : ψ ∈ Irr ↥T) (hpos : 0 < cfInner (resClassFun T χ) ψ)
    (hres : ψ ∘ Subgroup.inclusion hAT = lam) :
    χ = indClassFun T ψ := by
  have hIψ : inertiaGroup T ψ = T := by
    refine le_antisymm (le_trans ?_ hI) (le_inertiaGroup T (Irr_subset_classFun hψ))
    rw [← hres]
    exact inertiaGroup_le_inertiaGroup_comp_inclusion hAT ψ
  have hIrr : indClassFun T ψ ∈ Irr K := indClassFun_mem_Irr_of_inertiaGroup_eq hψ hIψ
  have hrec : cfInner (indClassFun T ψ) χ = cfInner (resClassFun T χ) ψ :=
    cfInner_indClassFun_eq_cfInner_resClassFun hχ hψ
  by_contra hne
  rw [cfInner_eq_zero_of_mem_Irr hIrr hχ (fun h => hne h.symm)] at hrec
  exact (ne_of_gt hpos) hrec.symm

theorem exists_linearChar_eq_indClassFun_coreProduct {N U Q : Subgroup L} [Finite L]
    [Fintype ↥(N ⊔ U)] [N.Normal] [IsMulCommutative ↥N] [IsMulCommutative ↥U]
    (hN : N ≠ ⊥) (hNU : N ⊓ U = ⊥)
    (hL : (N ⊔ U) ⊔ Q = ⊤) (hKQ : (N ⊔ U) ⊓ Q = ⊥)
    (hQU : Q ≤ normalizer (U : Set L))
    {q : ℕ} (hq : q.Prime) (hQcard : Nat.card Q = q) (hqU : q.Coprime (Nat.card U))
    (hmin : ∀ M : Subgroup L, M ≤ N → U ≤ normalizer (M : Set L) →
      Q ≤ normalizer (M : Set L) → M = ⊥ ∨ M = N)
    {χ : ↥(N ⊔ U) → ℂ} (hχ : χ ∈ Irr ↥(N ⊔ U))
    (hker : ∃ x : ↥(N ⊔ U), (x : L) ∈ N ∧ χ x ≠ χ 1)
    (hQinv : ∀ t ∈ Q, ∀ x y : ↥(N ⊔ U), (y : L) = t⁻¹ * (x : L) * t → χ y = χ x) :
    ∃ ψ : ↥((coreProduct N U).subgroupOf (N ⊔ U)) → ℂ,
      ψ ∈ Irr ↥((coreProduct N U).subgroupOf (N ⊔ U)) ∧ ψ 1 = 1 ∧
        (∃ x : ↥((coreProduct N U).subgroupOf (N ⊔ U)),
          ((x : ↥(N ⊔ U)) : L) ∈ N ∧ ψ x ≠ 1) ∧
        χ = indClassFun ((coreProduct N U).subgroupOf (N ⊔ U)) ψ := by
  classical
  have hNK : N ≤ N ⊔ U := le_sup_left
  set A : Subgroup ↥(N ⊔ U) := N.subgroupOf (N ⊔ U) with hAdef
  set T : Subgroup ↥(N ⊔ U) := (coreProduct N U).subgroupOf (N ⊔ U) with hTdef
  have hAnormal : A.Normal := ‹N.Normal›.subgroupOf _
  have hTnormal : T.Normal := coreProduct_normal_subgroupOf N U
  have hAT : A ≤ T := subgroupOf_le_coreProduct_subgroupOf N U
  have hAfin : Fintype ↥A := Fintype.ofFinite _
  have hTfin : Fintype ↥T := Fintype.ofFinite _
  have hQle : Q ≤ normalizer (N : Set L) ⊓ normalizer ((N ⊔ U : Subgroup L) : Set L) := fun t ht =>
    mem_inf.2 ⟨mem_normalizer_coe_of_normal N t,
      mem_normalizer_sup' (mem_normalizer_coe_of_normal N t) (hQU ht)⟩
  set γ : ↥Q →* MulAut ↥A :=
    (conjAutSubgroupOfHom N (N ⊔ U)).comp (Subgroup.inclusion hQle) with hγdef
  have hγcoe : ∀ (t : ↥Q) (x : ↥A), (((γ t x : ↥A) : ↥(N ⊔ U)) : L)
      = (t : L) * (((x : ↥(N ⊔ U))) : L) * (t : L)⁻¹ := fun t x => by
    rw [hγdef, MonoidHom.comp_apply, coe_conjAutSubgroupOfHom_apply_apply, Subgroup.coe_inclusion]
  have hinv : ∀ t : ↥Q, resClassFun A χ ∘ γ t = resClassFun A χ := by
    intro t
    funext x
    rw [Function.comp_apply, resClassFun_apply, resClassFun_apply]
    refine hQinv (t : L)⁻¹ (inv_mem t.2) _ _ ?_
    rw [hγcoe, inv_inv]
  have hcard : ¬ q ∣ (resConstituents A χ).card := by
    intro h
    have hdvd : (resConstituents A χ).card ∣ Nat.card U := by
      rw [← index_subgroupOf_sup_eq_card (A := N) (B := U) hNU]
      exact card_resConstituents_dvd_index _ hχ
    exact hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hqU dvd_rfl (h.trans hdvd))
  obtain ⟨lam, hlamS, hlamfix⟩ :=
    exists_mem_resConstituents_comp_eq (M := A) (χ := χ) (P := ↥Q) hq
      (a := 1) (by rw [hQcard, pow_one]) γ hinv hcard
  obtain ⟨hlamIrr, hlampos⟩ := mem_resConstituents.1 hlamS
  have hlam1 : lam ≠ 1 := by
    intro h1
    obtain ⟨x, hxN, hxχ⟩ := hker
    refine hxχ ?_
    have hmem : (1 : ↥A → ℂ) ∈ resConstituents A χ := h1 ▸ hlamS
    have hconst := resClassFun_eq_const_of_one_mem_resConstituents hχ hmem
      (⟨x, Subgroup.mem_subgroupOf.2 hxN⟩ : ↥A)
    rw [resClassFun_apply, resClassFun_apply] at hconst
    exact hconst
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_mulEquiv (subgroupOfEquivOfLe hNK)
  obtain ⟨ν, hν⟩ := exists_monoidHom_coe_eq_of_mem_Irr hlamIrr
  set mu : ↥N →* ℂˣ := ν.comp (subgroupOfEquivOfLe hNK).symm.toMonoidHom with hmudef
  have hmulam : (fun y : ↥A => (mu ((subgroupOfEquivOfLe hNK) y) : ℂ)) = lam := by
    rw [← hν, hmudef]
    funext y
    simp
  have hmu1 : mu ≠ 1 := by
    intro h
    refine hlam1 ?_
    rw [← hmulam, h]
    funext y
    simp
  have hQmu : ∀ t ∈ Q, ∀ (n : ↥N) (hn : t⁻¹ * (n : L) * t ∈ N),
      mu ⟨t⁻¹ * (n : L) * t, hn⟩ = mu n := by
    intro t ht n hn
    refine Units.ext ?_
    set x : ↥A := ⟨⟨(n : L), hNK n.2⟩, Subgroup.mem_subgroupOf.2 n.2⟩ with hx
    set y : ↥A := ⟨⟨t⁻¹ * (n : L) * t, hNK hn⟩, Subgroup.mem_subgroupOf.2 hn⟩ with hy
    have h := congrFun (hlamfix ⟨t, ht⟩) y
    rw [Function.comp_apply] at h
    have hgy : γ ⟨t, ht⟩ y = x := by
      refine Subtype.ext (Subtype.ext ?_)
      rw [hγcoe]
      change (t : L) * (t⁻¹ * (n : L) * t) * (t : L)⁻¹ = (n : L)
      group
    rw [hgy] at h
    have e1 : (subgroupOfEquivOfLe hNK) y = ⟨t⁻¹ * (n : L) * t, hn⟩ := Subtype.ext rfl
    have e2 : (subgroupOfEquivOfLe hNK) x = n := Subtype.ext rfl
    have hval := congrFun hmulam
    rw [← hval y, ← hval x, e1, e2] at h
    exact h.symm
  have hC : U ⊓ charInertia N mu = coreCentralizer N U :=
    inf_charInertia_eq_coreCentralizer hQU hmu1 hmin hQmu
  have hI : inertiaGroup A lam = T := by
    rw [← hmulam]
    exact inertiaGroup_subgroupOf_eq_coreProduct hC
  obtain ⟨ψ, hψIrr, hψpos, hψres⟩ :=
    exists_mem_Irr_comp_inclusion_eq (A := A) (T := T) hAT hχ hlamIrr hlampos
  refine ⟨ψ, hψIrr, Irr.apply_one_eq_one_of_isMulCommutative hψIrr, ?_, ?_⟩
  ·
    by_contra hcon
    push Not at hcon
    refine hlam1 ?_
    funext x
    rw [← hψres, Function.comp_apply, Pi.one_apply]
    exact hcon _ (Subgroup.mem_subgroupOf.1 x.2)
  · exact eq_indClassFun_of_inertiaGroup_eq hAT hχ (le_of_eq hI) hψIrr hψpos hψres

theorem apply_one_eq_relIndex_coreCentralizer {N U Q : Subgroup L} [Finite L]
    [Fintype ↥(N ⊔ U)] [N.Normal] [IsMulCommutative ↥N] [IsMulCommutative ↥U]
    (hN : N ≠ ⊥) (hNU : N ⊓ U = ⊥)
    (hL : (N ⊔ U) ⊔ Q = ⊤) (hKQ : (N ⊔ U) ⊓ Q = ⊥)
    (hQU : Q ≤ normalizer (U : Set L))
    {q : ℕ} (hq : q.Prime) (hQcard : Nat.card Q = q) (hqU : q.Coprime (Nat.card U))
    (hmin : ∀ M : Subgroup L, M ≤ N → U ≤ normalizer (M : Set L) →
      Q ≤ normalizer (M : Set L) → M = ⊥ ∨ M = N)
    {χ : ↥(N ⊔ U) → ℂ} (hχ : χ ∈ Irr ↥(N ⊔ U))
    (hker : ∃ x : ↥(N ⊔ U), (x : L) ∈ N ∧ χ x ≠ χ 1)
    (hQinv : ∀ t ∈ Q, ∀ x y : ↥(N ⊔ U), (y : L) = t⁻¹ * (x : L) * t → χ y = χ x) :
    χ 1 = ((coreCentralizer N U).relIndex U : ℂ) := by
  obtain ⟨ψ, -, hψ1, -, hind⟩ := exists_linearChar_eq_indClassFun_coreProduct
    hN hNU hL hKQ hQU hq hQcard hqU hmin hχ hker hQinv
  have hTK : coreProduct N U ≤ N ⊔ U := coreProduct_le_sup N U
  have hdeg : χ 1 = (((coreProduct N U).subgroupOf (N ⊔ U)).index : ℂ) := by
    rw [hind]; exact indClassFun_one_eq_index _ hψ1
  have hidx : ((coreProduct N U).subgroupOf (N ⊔ U)).index * Nat.card (coreProduct N U)
      = Nat.card ↥(N ⊔ U) := by
    have h := Subgroup.index_mul_card ((coreProduct N U).subgroupOf (N ⊔ U))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv] at h
  have hcard := card_coreProduct_mul_relIndex N U hNU
  have hpos : 0 < Nat.card (coreProduct N U) := Nat.card_pos
  have : ((coreProduct N U).subgroupOf (N ⊔ U)).index = (coreCentralizer N U).relIndex U := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hidx, ← hcard]
    ring
  rw [hdeg, this]

theorem eq_zero_of_notMem_coreProduct {N U Q : Subgroup L} [Finite L]
    [Fintype ↥(N ⊔ U)] [N.Normal] [IsMulCommutative ↥N] [IsMulCommutative ↥U]
    (hN : N ≠ ⊥) (hNU : N ⊓ U = ⊥)
    (hL : (N ⊔ U) ⊔ Q = ⊤) (hKQ : (N ⊔ U) ⊓ Q = ⊥)
    (hQU : Q ≤ normalizer (U : Set L))
    {q : ℕ} (hq : q.Prime) (hQcard : Nat.card Q = q) (hqU : q.Coprime (Nat.card U))
    (hmin : ∀ M : Subgroup L, M ≤ N → U ≤ normalizer (M : Set L) →
      Q ≤ normalizer (M : Set L) → M = ⊥ ∨ M = N)
    {χ : ↥(N ⊔ U) → ℂ} (hχ : χ ∈ Irr ↥(N ⊔ U))
    (hker : ∃ x : ↥(N ⊔ U), (x : L) ∈ N ∧ χ x ≠ χ 1)
    (hQinv : ∀ t ∈ Q, ∀ x y : ↥(N ⊔ U), (y : L) = t⁻¹ * (x : L) * t → χ y = χ x)
    {x : ↥(N ⊔ U)} (hx : (x : L) ∉ coreProduct N U) : χ x = 0 := by
  obtain ⟨ψ, -, -, -, hind⟩ := exists_linearChar_eq_indClassFun_coreProduct
    hN hNU hL hKQ hQU hq hQcard hqU hmin hχ hker hQinv
  have : ((coreProduct N U).subgroupOf (N ⊔ U)).Normal := coreProduct_normal_subgroupOf N U
  have hxT : x ∉ (coreProduct N U).subgroupOf (N ⊔ U) := fun h => hx (mem_subgroupOf.1 h)
  rw [hind, ← normalInduction_indClassFun_eq]
  exact NormalInduction.indClassFun_eq_zero_of_notMem _ ψ hxT

end CFSG.FeitThompson
