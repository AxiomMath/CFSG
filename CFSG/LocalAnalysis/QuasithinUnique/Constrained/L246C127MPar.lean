module

import CFSG.Quasithin.Background.C126Glue
import CFSG.Quasithin.Background.F1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127DegGamma
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127DegNorm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellShort
public import CFSG.Quasithin.Background.B6Basic

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L246C127

namespace MPar

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def W0 (T K : Subgroup G) : Subgroup G := conjClosure (blockU K) T

theorem W0_le_T {T K : Subgroup G} (hUT : blockU K ≤ T) : W0 T K ≤ T :=
  conjClosure_le fun h hh z hz => T.mul_mem (T.mul_mem hh (hUT hz)) (T.inv_mem hh)

theorem blockU_le_W0 (T K : Subgroup G) : blockU K ≤ W0 T K := le_conjClosure _ _

theorem conj_mem_W0 {T K : Subgroup G} {t u : G} (ht : t ∈ T) (hu : u ∈ blockU K) :
    t * u * t⁻¹ ∈ W0 T K :=
  Subgroup.subset_closure ⟨t, ht, u, hu, rfl⟩

theorem conj_blockU_comm {P T K : Subgroup G} (hP : CharTwo P) (hTP : T ≤ P)
    (hK : IsBlock2 P K) {t t' u u' : G} (ht : t ∈ T) (ht' : t' ∈ T) (hu : u ∈ blockU K)
    (hu' : u' ∈ blockU K) :
    (t * u * t⁻¹) * (t' * u' * t'⁻¹) = (t' * u' * t'⁻¹) * (t * u * t⁻¹) := by
  by_cases h : conjByElt t K = conjByElt t' K
  · have hs : t⁻¹ * t' ∈ Subgroup.normalizer (K : Set G) := Deg.fh7_inv_mul_normalizer h
    have hw : (t⁻¹ * t') * u' * (t⁻¹ * t')⁻¹ ∈ blockU K := Deg.conj_mem_blockU hs hu'
    have e : t' * u' * t'⁻¹ = t * ((t⁻¹ * t') * u' * (t⁻¹ * t')⁻¹) * t⁻¹ := by group
    rw [e]
    have hab := (C1.elemAb2_blockU hK.1).1 u hu _ hw
    calc (t * u * t⁻¹) * (t * ((t⁻¹ * t') * u' * (t⁻¹ * t')⁻¹) * t⁻¹)
        = t * (u * ((t⁻¹ * t') * u' * (t⁻¹ * t')⁻¹)) * t⁻¹ := by group
      _ = t * (((t⁻¹ * t') * u' * (t⁻¹ * t')⁻¹) * u) * t⁻¹ := by rw [hab]
      _ = _ := by group
  · have hB1 : IsBlock2 P (conjByElt t K) := IsBlock2.conjByElt_of_mem hK (hTP ht)
    have hB2 : IsBlock2 P (conjByElt t' K) := IsBlock2.conjByElt_of_mem hK (hTP ht')
    have hcomm := distinctBlocksCommuteStatement P (conjByElt t K) (conjByElt t' K) hP hB1 hB2 h
    have huK : u ∈ K := C1.blockQ_le K (C1.blockU_le_blockQ hK.1 hu)
    have hu'K : u' ∈ K := C1.blockQ_le K (C1.blockU_le_blockQ hK.1 hu')
    have hx : t * u * t⁻¹ ∈ conjByElt t K := by
      rw [mem_conjByElt]
      have e : t⁻¹ * (t * u * t⁻¹) * t = u := by group
      rw [e]
      exact huK
    have hy : t' * u' * t'⁻¹ ∈ conjByElt t' K := by
      rw [mem_conjByElt]
      have e : t'⁻¹ * (t' * u' * t'⁻¹) * t' = u' := by group
      rw [e]
      exact hu'K
    exact Deg.fh7_mul_comm_of_comm_eq_bot hcomm hx hy

theorem isElemAbelian_W0 {P T K : Subgroup G} (hP : CharTwo P) (hTP : T ≤ P)
    (hK : IsBlock2 P K) : IsElemAbelian 2 (W0 T K) := by
  have hScomm : ∀ x ∈ {x | ∃ h ∈ T, ∃ z ∈ blockU K, h * z * h⁻¹ = x},
      ∀ y ∈ {x | ∃ h ∈ T, ∃ z ∈ blockU K, h * z * h⁻¹ = x}, x * y = y * x := by
    rintro x ⟨t, ht, u, hu, rfl⟩ y ⟨t', ht', u', hu', rfl⟩
    exact conj_blockU_comm hP hTP hK ht ht' hu hu'
  have hSsq : ∀ x ∈ {x | ∃ h ∈ T, ∃ z ∈ blockU K, h * z * h⁻¹ = x}, x ^ 2 = 1 := by
    rintro x ⟨t, ht, u, hu, rfl⟩
    have hu2 : u ^ 2 = 1 := C1.blockU_sq hK.1 u hu
    have huu : u * u = 1 := (sq u).symm.trans hu2
    rw [sq]
    calc t * u * t⁻¹ * (t * u * t⁻¹) = t * (u * u) * t⁻¹ := by group
      _ = 1 := by simp [huu]
  have hcomm := Deg.fh7_closure_comm hScomm
  have hsq := Deg.fh7_closure_sq hScomm hSsq
  exact C5.isElemAbelian_two_iff.2 ⟨hcomm, hsq⟩

theorem K_le_normalizer_W0 {P T K : Subgroup G} (hP : CharTwo P) (hTP : T ≤ P)
    (hK : IsBlock2 P K) : K ≤ Subgroup.normalizer (W0 T K : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ k ∈ K, ∀ w ∈ W0 T K, k * w * k⁻¹ ∈ W0 T K := by
    intro k hk w hw
    have hw' : w ∈ Subgroup.closure {x | ∃ h ∈ T, ∃ z ∈ blockU K, h * z * h⁻¹ = x} := hw
    clear hw
    induction hw' using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨t, ht, u, hu, rfl⟩ := hx
      by_cases h : conjByElt t K = K
      · have hs : t ∈ Subgroup.normalizer (K : Set G) := Deg.fh7_normalizer_of_conj_eq h
        have h1 : t * u * t⁻¹ ∈ blockU K := Deg.conj_mem_blockU hs hu
        have h2 : k * (t * u * t⁻¹) * k⁻¹ ∈ blockU K := by
          have := (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU K hk) _).mp h1
          exact this
        exact blockU_le_W0 T K h2
      · have hB1 : IsBlock2 P (conjByElt t K) := IsBlock2.conjByElt_of_mem hK (hTP ht)
        have hne : conjByElt t K ≠ K := h
        have hcomm := distinctBlocksCommuteStatement P (conjByElt t K) K hP hB1 hK hne
        have hx : t * u * t⁻¹ ∈ conjByElt t K := by
          rw [mem_conjByElt]
          have e : t⁻¹ * (t * u * t⁻¹) * t = u := by group
          rw [e]
          exact C1.blockQ_le K (C1.blockU_le_blockQ hK.1 hu)
        have hc := Deg.fh7_mul_comm_of_comm_eq_bot hcomm hx hk
        have : k * (t * u * t⁻¹) * k⁻¹ = t * u * t⁻¹ := by
          rw [← hc]; group
        rw [this]
        exact conj_mem_W0 ht hu
    | one => simpa using (W0 T K).one_mem
    | mul x y _ _ hx hy =>
      have e : k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
      rw [e]
      exact (W0 T K).mul_mem hx hy
    | inv x _ hx =>
      have e : k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ := by group
      rw [e]
      exact (W0 T K).inv_mem hx
  intro x
  constructor
  · intro hx
    exact key k hk x hx
  · intro hx
    have := key k⁻¹ (K.inv_mem hk) _ hx
    simpa [mul_assoc] using this

theorem three_subgroups_mod' {X Y Z N : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (N : Set G)) (hY : Y ≤ Subgroup.normalizer (N : Set G))
    (hZ : Z ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅X, Y⁆, Z⁆ ≤ N) (h2 : ⁅⁅Y, Z⁆, X⁆ ≤ N) :
    ⁅⁅Z, X⁆, Y⁆ ≤ N := by
  set M := Subgroup.normalizer (N : Set G)
  have hN : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  set π := QuotientGroup.mk' (N.subgroupOf M)
  have hmap : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      ⁅⁅A, B⁆, C⁆ = (⁅⁅A.subgroupOf M, B.subgroupOf M⁆, C.subgroupOf M⁆).map M.subtype := by
    intro A B C hA hB hC
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hC]
  have key : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      (⁅⁅A, B⁆, C⁆ ≤ N ↔ ⁅⁅(A.subgroupOf M).map π, (B.subgroupOf M).map π⁆,
        (C.subgroupOf M).map π⁆ = ⊥) := by
    intro A B C hA hB hC
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', hmap A B C hA hB hC]
    constructor
    · intro h x hx
      exact Subgroup.mem_subgroupOf.mpr (h ⟨x, hx, rfl⟩)
    · rintro h _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h hx)
  rw [key X Y Z hX hY hZ] at h1
  rw [key Y Z X hY hZ hX] at h2
  rw [key Z X Y hZ hX hY]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem le_normalizer_commutator' {A B X : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro g hg
  rw [← conjSubgroup_eq_iff_mem_normalizer, C5.conjSubgroup_commutator,
    C5.conjSubgroup_eq_self (hA hg), C5.conjSubgroup_eq_self (hB hg)]

theorem commutator_lt_self' {T V : Subgroup G} (hT : IsPGroup 2 T) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hV : V ≠ ⊥) : ⁅V, T⁆ < V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine lt_of_le_of_ne (Subgroup.le_normalizer_iff_commutator_le_left.1 hTV) fun h => hV ?_
  have hnil : Group.IsNilpotent T := hT.isNilpotent
  obtain ⟨m, hm⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries T).mp hnil
  have key : ∀ k, V ≤ T.lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact hVT
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ, ← h]
      exact Subgroup.commutator_mono ih le_rfl
  rw [eq_bot_iff, ← hm]
  exact key m

theorem pCoreOf_le_centralizer_blockU {P K : Subgroup G} (hK : IsBlock2 P K) :
    pCoreOf 2 P ≤ Subgroup.centralizer (blockU K : Set G) := by
  have hshort : IsShort2 K := hK.1
  have hKP : K ≤ P := hK.2.1
  have hsub : IsSubnormal K P := C1GN.isSubnormal_of_isBlock2 hK
  set N := pCoreOf 2 P with hNdef
  set U := blockU K with hUdef
  have hNP : N ≤ P := pCoreOf_le 2 P
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pCoreOf 2 P
  have hNn : (N.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).2 hPN
  have hN2 : IsPGroup 2 N := pCoreOf_isPGroup 2 P
  have hNK : ⁅N, K⁆ ≤ U := commutator_le_blockU hshort hsub hNP hNn hN2
  have hUK : U ≤ K := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le K)
  have hUN : U ≤ N :=
    (C1.blockU_le_blockQ hshort).trans (Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hKP hK.2.2)
  have hNnK : N ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left, Subgroup.commutator_comm]
    exact hNK.trans hUK
  have hNnU : N ≤ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left, Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl hUK).trans hNK
  have hKnU : K ≤ Subgroup.normalizer (U : Set G) := C1.le_normalizer_blockU K
  have hKnN : K ≤ Subgroup.normalizer (N : Set G) := hKP.trans hPN
  have hUnK : U ≤ Subgroup.normalizer (K : Set G) := hUK.trans Subgroup.le_normalizer
  have hUnU : U ≤ Subgroup.normalizer (U : Set G) := Subgroup.le_normalizer
  have hUnN : U ≤ Subgroup.normalizer (N : Set G) := hUN.trans Subgroup.le_normalizer
  have hKnK : K ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer
  have hNnN : N ≤ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer
  set A : Subgroup G := ⁅U, N⁆ with hAdef
  have hAU : A ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.1 hNnU
  have hKnA : K ≤ Subgroup.normalizer (A : Set G) := le_normalizer_commutator' hKnU hKnN
  have hNnA : N ≤ Subgroup.normalizer (A : Set G) := le_normalizer_commutator' hNnU hNnN
  have hUnA : U ≤ Subgroup.normalizer (A : Set G) := le_normalizer_commutator' hUnU hUnN
  have hKnA' : K ≤ Subgroup.normalizer ((⁅A, K⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator' hKnA hKnK
  have hNnA' : N ≤ Subgroup.normalizer ((⁅A, K⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator' hNnA hNnK
  have hUnA' : U ≤ Subgroup.normalizer ((⁅A, K⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator' hUnA hUnK
  have hUU : ⁅U, U⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    exact Subgroup.mem_centralizer_iff.2 fun b hb => (C1.elemAb2_blockU hshort).1 b hb a ha
  have h1 : ⁅⁅K, N⁆, U⁆ ≤ ⁅A, K⁆ := by
    have : ⁅⁅K, N⁆, U⁆ ≤ ⁅U, U⁆ := by
      refine Subgroup.commutator_mono ?_ le_rfl
      rw [Subgroup.commutator_comm]
      exact hNK
    rw [hUU] at this
    exact this.trans bot_le
  have h2 : ⁅⁅N, U⁆, K⁆ ≤ ⁅A, K⁆ := by
    rw [Subgroup.commutator_comm N U]
  have hmain : ⁅⁅U, K⁆, N⁆ ≤ ⁅A, K⁆ :=
    three_subgroups_mod' hKnA' hNnA' hUnA' h1 h2
  have hUKU : ⁅U, K⁆ = U := C1.commutator_blockU hshort
  rw [hUKU] at hmain
  have hAA : A = ⁅A, K⁆ :=
    le_antisymm hmain (Subgroup.le_normalizer_iff_commutator_le_left.1 hKnA)
  have hAbot : A = ⊥ := by
    have hZnorm : K ≤ Subgroup.normalizer (blockZ K : Set G) := fun g hg =>
      C1.mem_normalizer_blockZ (Subgroup.le_normalizer hg)
    have hW'norm : K ≤ Subgroup.normalizer ((A ⊔ blockZ K : Subgroup G) : Set G) := fun g hg =>
      C1.mem_normalizer_sup (hKnA hg) (hZnorm hg)
    have hZU : blockZ K ≤ U := inf_le_left
    rcases hshort.2.2.2.2.2 (A ⊔ blockZ K) le_sup_right (sup_le hAU hZU) hW'norm with h | h
    · have hAZ : A ≤ blockZ K := le_sup_left.trans h.le
      have hAc : A ≤ Subgroup.centralizer (K : Set G) := hAZ.trans inf_le_right
      rw [hAA]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hAc
    · exfalso
      have hUA : U ≤ A := blockU_le_of_sup_eq hshort hKnA hAU h
      have hAeq : A = U := le_antisymm hAU hUA
      have hUne : U ≠ ⊥ := by
        intro hb
        have := hshort.2.2.2.2.1
        rw [← hUdef, hb] at this
        exact not_lt_bot this
      have hlt := commutator_lt_self' hN2 hUN hNnU hUne
      rw [← hAdef, hAeq] at hlt
      exact lt_irrefl _ hlt
  have hcomm : ⁅N, U⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hAbot
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm

theorem T_le_normalizer_W0 (T K : Subgroup G) : T ≤ Subgroup.normalizer (W0 T K : Set G) :=
  le_normalizer_conjClosure _ _

theorem P_le_normalizer_W0 {P T K : Subgroup G} (hP : CharTwo P) (hTP : T ≤ P)
    (hK : IsBlock2 P K) (hPK : P = T ⊔ conjClosure K T) :
    P ≤ Subgroup.normalizer (W0 T K : Set G) := by
  rw [hPK]
  refine sup_le (T_le_normalizer_W0 T K) (conjClosure_le fun t ht k hk => ?_)
  have hkN := K_le_normalizer_W0 hP hTP hK hk
  have htN := T_le_normalizer_W0 T K ht
  exact (Subgroup.normalizer (W0 T K : Set G)).mul_mem
    ((Subgroup.normalizer (W0 T K : Set G)).mul_mem htN hkN)
    ((Subgroup.normalizer (W0 T K : Set G)).inv_mem htN)

theorem pCoreOf_le_centralizer_W0 {P T K : Subgroup G} (hK : IsBlock2 P K) (hTP : T ≤ P) :
    pCoreOf 2 P ≤ Subgroup.centralizer (W0 T K : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  have hqU := pCoreOf_le_centralizer_blockU hK hq
  have key : W0 T K ≤ Subgroup.centralizer ({q} : Set G) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨t, ht, u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hq' : t⁻¹ * q * t ∈ pCoreOf 2 P := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 P (hTP (T.inv_mem ht))) q).mp hq
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 (pCoreOf_le_centralizer_blockU hK hq') u hu
    calc (t * u * t⁻¹) * q = t * (u * (t⁻¹ * q * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * q * t) * u) * t⁻¹ := by rw [h1]
      _ = q * (t * u * t⁻¹) := by group
  intro w hw
  exact Subgroup.mem_centralizer_singleton_iff.1 (key hw)

theorem not_le_centralizer_W0 {P T K : Subgroup G} (hK : IsBlock2 P K) :
    ¬ K ≤ Subgroup.centralizer (W0 T K : Set G) := by
  intro h
  have hZ : blockU K ≤ blockZ K := by
    intro u hu
    refine Subgroup.mem_inf.2 ⟨hu, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 (h hk) u (blockU_le_W0 T K hu)).symm
  exact not_lt_of_ge hZ hK.1.2.2.2.2.1

theorem not_thompsonJ_le_centralizer_W0 {P T K : Subgroup G} (hP : CharTwo P) (hTP : T ≤ P)
    (hK : IsBlock2 P K) (hKJ : ⁅K, thompsonJ T⁆ = K) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (W0 T K : Set G) := by
  intro hJ
  apply not_le_centralizer_W0 (T := T) hK
  have hKN := K_le_normalizer_W0 hP hTP hK
  conv_lhs => rw [← hKJ]
  rw [Subgroup.commutator_le]
  intro k hk j hj
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hjc := Subgroup.mem_centralizer_iff.1 (hJ hj)
  have hw1 : k⁻¹ * w * k ∈ W0 T K := by
    have := (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem hk)) w).mp hw
    simpa using this
  have hw2 : k * w * k⁻¹ ∈ W0 T K := (Subgroup.mem_normalizer_iff.mp (hKN hk) w).mp hw
  have h1 := hjc _ hw1
  have h2 := hjc _ hw
  have h3 := hjc _ hw2
  simp only [commutatorElement_def]
  calc w * (k * j * k⁻¹ * j⁻¹) = k * (((k⁻¹ * w * k) * j) * k⁻¹) * j⁻¹ := by group
    _ = k * ((j * (k⁻¹ * w * k)) * k⁻¹) * j⁻¹ := by rw [h1]
    _ = (k * j * k⁻¹) * w * j⁻¹ := by group
    _ = (k * j * k⁻¹ * w) * j⁻¹ := by group
    _ = (k * j * k⁻¹ * j⁻¹) * (j * w * j⁻¹) := by group
    _ = (k * j * k⁻¹ * j⁻¹) * w := by rw [show j * w * j⁻¹ = w by rw [← h2]; group]

theorem pow_mul_mem_of_pow_mem {C : Subgroup G} {d c : G}
    (hd : d ∈ Subgroup.normalizer (C : Set G)) (hc : c ∈ C) {n : ℕ} (h : d ^ n ∈ C) :
    (d * c) ^ n ∈ C := by
  set M := Subgroup.normalizer (C : Set G) with hM
  have hCn : (C.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  have hcM : c ∈ M := Subgroup.le_normalizer hc
  have h1 : (QuotientGroup.mk' (C.subgroupOf M)) ⟨c, hcM⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hc)
  have h2 : (QuotientGroup.mk' (C.subgroupOf M)) ((⟨d, hd⟩ : M) ^ n) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 (by simpa using h))
  have h3 : (QuotientGroup.mk' (C.subgroupOf M)) ((⟨d, hd⟩ * ⟨c, hcM⟩ : M) ^ n) = 1 := by
    rw [map_pow, map_mul, h1, mul_one, ← map_pow]
    exact h2
  have h4 := (QuotientGroup.eq_one_iff _).1 h3
  have := Subgroup.mem_subgroupOf.1 h4
  simpa using this

theorem exists_minParabolic_of_uFamHat {X T P : Subgroup G} (hT : IsSylowTwoOf T X)
    (hP : P ∈ uFamHat X T) : ∃ M, MinParabolic P T M := by
  obtain ⟨⟨hPX, hlt, hncard⟩, hnn⟩ := hP
  have hsyl : IsSylowTwoOf T P := C1GN.isSylowTwoOf_of_le hT hlt.le hPX
  obtain ⟨M, hM⟩ := maxOver_ncard_eq_one_iff.mp hncard
  exact ⟨M, minParabolic_iff.mpr ⟨⟨T, hsyl, ⟨le_rfl, hlt, hncard⟩, hnn⟩, hsyl, hM⟩⟩

theorem isTwoReducedIn_W0 {P T M K : Subgroup G} (hmp : MinParabolic P T M) (hP : CharTwo P)
    (hK : IsBlock2 P K) (hPK : P = T ⊔ conjClosure K T) (hUT : blockU K ≤ T) :
    IsTwoReducedIn P (W0 T K) := by
  have hTP : T ≤ P := hmp.isSylow.1
  have hPN := P_le_normalizer_W0 hP hTP hK hPK
  refine ⟨(W0_le_T hUT).trans hTP, hPN, isElemAbelian_W0 hP hTP hK, ?_⟩
  intro D hDP hDn hD2
  set C : Subgroup G := P ⊓ Subgroup.centralizer (W0 T K : Set G) with hC
  have hCP : C ≤ P := inf_le_left
  have hPnC : P ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [← conjSubgroup_eq_iff_mem_normalizer, C5.conjSubgroup_inf, C5.conjSubgroup_centralizer,
      C5.conjSubgroup_eq_self (Subgroup.le_normalizer hg), C5.conjSubgroup_eq_self (hPN hg)]
  have hQC : pCoreOf 2 P ≤ C := le_inf (pCoreOf_le 2 P) (pCoreOf_le_centralizer_W0 hK hTP)
  have hnot : ¬ twoResidual P ≤ C := by
    intro h
    apply not_le_centralizer_W0 (T := T) hK
    exact (C126.le_twoResidual_of_short hK.2.1 hK.1).trans (h.trans inf_le_right)
  have hCM : C ≤ M := (hmp.le_kerIn_of_not_twoResidual_le hCP hPnC hnot).trans kerIn_le
  have hDC : C ≤ D ⊔ C := le_sup_right
  have hDP' : D ⊔ C ≤ P := sup_le hDP hCP
  have hDn' : P ≤ Subgroup.normalizer ((D ⊔ C : Subgroup G) : Set G) := fun g hg =>
    C1.mem_normalizer_sup (hDn hg) (hPnC hg)
  have h2pow : ∀ x ∈ D ⊔ C, ∃ k : ℕ, x ^ 2 ^ k ∈ C := by
    intro x hx
    obtain ⟨d, hd, c, hc, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer
      (hDP.trans hPnC)).1 hx
    obtain ⟨k, hk⟩ := hD2 d hd
    exact ⟨k, pow_mul_mem_of_pow_mem (hPnC (hDP hd)) hc (Subgroup.mem_inf.2 ⟨
      P.pow_mem (hDP hd) _, hk⟩)⟩
  have := hmp.le_of_isTwoQuotient_of_pCoreOf_le hPnC hQC hCM hDC hDP' hDn' h2pow
  exact (le_sup_left.trans this).trans inf_le_right

end MPar

end L246C127

end CFSG.QuasithinUnique
