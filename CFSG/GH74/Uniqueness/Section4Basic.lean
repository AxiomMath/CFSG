module

public import CFSG.GH74.Uniqueness.Setup

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Lemma41

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem mem_sylow_of_mem_center {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {x : G} (hx : x ∈ center G) (hxp : IsPGroup p (zpowers x)) :
    x ∈ (P : Subgroup G) := by
  have : (zpowers x).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hg : g * x = x * g := (Subgroup.mem_center_iff.mp hx g)
    have : g * x ^ k * g⁻¹ = x ^ k := by
      have h1 : g * x * g⁻¹ = x := by rw [hg]; group
      rw [← conj_zpow, h1]
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _
  exact hxp.le_sylow_of_normal P (Subgroup.mem_zpowers x)

theorem ZDSetup.exists_sylow_central (S : ZDSetup X Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) :
    ∃ T : Sylow 2 X, (T : Subgroup X) ≤ M ∧ z ∈ (T : Subgroup X) ∧
      ∀ s ∈ (T : Subgroup X), s * z = z * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set X) with hCdef
  have hCM : C ≤ M := S.prodDisc.centralizer_le_of_mem hz hzM
  have hcard := S.prodDisc.card_inter_mul_card_centralizer S.invariant hz hzM
  have hodd : Odd (Nat.card ↥(Z ∩ (M : Set X))) := S.odd_zNum
  obtain ⟨S0, hS0⟩ := S.prodDisc.exists_sylow_normalizer_le S.invariant
  have hS0M : (S0 : Subgroup X) ≤ M := fun x hx => hS0 (Subgroup.le_normalizer hx)
  set a := (Nat.card X).factorization 2 with ha
  have h1 : 2 ^ a ∣ Nat.card M := by
    have : Nat.card S0 = 2 ^ a := S0.card_eq_multiplicity
    rw [← this]
    exact Subgroup.card_dvd_of_le hS0M
  have h2 : 2 ^ a ∣ Nat.card C := by
    rw [← hcard] at h1
    have hcop : Nat.Coprime (2 ^ a) (Nat.card ↥(Z ∩ (M : Set X))) := by
      apply Nat.Coprime.pow_left
      exact Nat.coprime_two_left.mpr hodd
    exact hcop.dvd_of_dvd_mul_left h1
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
  have hPcard : Nat.card (P : Subgroup ↥C) = 2 ^ a := by
    have e1 : Nat.card (P : Subgroup ↥C) = 2 ^ (Nat.card C).factorization 2 :=
      P.card_eq_multiplicity
    have e2 : (Nat.card C).factorization 2 = a := by
      apply le_antisymm
      · exact (Nat.factorization_le_iff_dvd (Nat.card_pos).ne' (Nat.card_pos).ne').mpr
          (Subgroup.card_subgroup_dvd_card C) 2
      · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos).ne').mp h2
    rw [e1, e2]
  set P' : Subgroup X := (P : Subgroup ↥C).map C.subtype with hP'
  have hP'card : Nat.card P' = 2 ^ a := by
    rw [hP', Subgroup.card_map_of_injective C.subtype_injective, hPcard]
  let T : Sylow 2 X := Sylow.ofCard P' hP'card
  have hTP : (T : Subgroup X) = P' := rfl
  have hP'C : P' ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  refine ⟨T, hTP ▸ hP'C.trans hCM, ?_, fun s hs => ?_⟩
  · rw [hTP]
    have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    set z' : ↥C := ⟨z, hzC⟩ with hz'
    have hcent : z' ∈ center ↥C := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.mp g.2)
    have hz2 : IsPGroup 2 (zpowers z') := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hz', Subgroup.orderOf_mk, S.invariant.1 z hz, pow_one]
    have hmem := mem_sylow_of_mem_center P hcent hz2
    exact ⟨z', hmem, rfl⟩
  · rw [hTP] at hs
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hP'C hs))

theorem mem_smul_sylow_iff {G : Type*} [Group G] {p : ℕ} (T : Sylow p G) (g y : G) :
    y ∈ ((g • T : Sylow p G) : Subgroup G) ↔ ∃ t ∈ (T : Subgroup G), g * t * g⁻¹ = y := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  simp [MulAut.smul_def]

theorem ZDSetup.isCentralInvolution (S : ZDSetup X Z M) {z : X} (hz : z ∈ Z) :
    IsCentralInvolution z := by
  obtain ⟨g, hg⟩ := S.prodDisc.exists_conj_mem_subgroup S.invariant hz
  have hz₀ : g⁻¹ * z * g ∈ Z := S.invariant.2 z hz g
  obtain ⟨T, -, hzT, hcomm⟩ := S.exists_sylow_central hz₀ hg
  refine ⟨S.invariant.1 z hz, g • T, ?_, fun s hs => ?_⟩
  · rw [mem_smul_sylow_iff]
    exact ⟨_, hzT, by group⟩
  · obtain ⟨t, ht, rfl⟩ := (mem_smul_sylow_iff T g s).mp hs
    have := hcomm t ht
    calc g * t * g⁻¹ * z = g * (t * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * t) * g⁻¹ := by rw [this]
      _ = z * (g * t * g⁻¹) := by group

theorem ZDSetup.eq_conjClass (S : ZDSetup X Z M) {z : X} (hz : z ∈ Z) :
    Z = {y : X | IsConj z y} := by
  ext y
  exact ⟨fun hy => S.prodDisc.isConj_of_mem S.invariant hz hy,
    fun hy => S.invariant.isConj_mem hz hy.symm⟩

end Lemma41

section Lemma42

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.exists_mem_fusion (S : ZDSetup X Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M)
    {T : Sylow 2 X} (hTM : (T : Subgroup X) ≤ M) (hzT : z ∈ (T : Subgroup X))
    (hcomm : ∀ s ∈ (T : Subgroup X), s * z = z * s) {P : Subgroup X} (hP : P ≤ (T : Subgroup X))
    {g : X} (hg : conjugate P g ≤ (T : Subgroup X)) :
    ∃ c ∈ M, ∀ x ∈ P, c⁻¹ * x * c = g⁻¹ * x * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, hcg⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion T hP hg
  refine ⟨c, ?_, hcg⟩
  have hU := S.prodDisc.isUniqueSubgroup_zpowers hz hzM
  clear hcg
  induction hc with
  | one => exact M.one_mem
  | step hc' hQ hPQ hn ih =>
    refine M.mul_mem ih ?_
    have hzQ : z ∈ _ := hQ.2.2.1 ⟨Subgroup.mem_centralizer_iff.mpr (fun h hh => hcomm h (hQ.1 hh)),
      hzT⟩
    exact hU.normalizer_le (Subgroup.zpowers_le.mpr hzQ) (hQ.1.trans hTM) hn

omit [Finite X] in
theorem conjugate_closure (A : Set X) (g : X) :
    conjugate (Subgroup.closure A) g = Subgroup.closure (conjSet A g) := by
  unfold conjugate conjSet
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp

theorem ZDSetup.controlsFusion_sylow (S : ZDSetup X Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M)
    {T : Sylow 2 X} (hTM : (T : Subgroup X) ≤ M) (hzT : z ∈ (T : Subgroup X))
    (hcomm : ∀ s ∈ (T : Subgroup X), s * z = z * s) : ControlsFusion M (T : Subgroup X) := by
  intro A hA B hB ⟨g, hg⟩
  have hP : Subgroup.closure A ≤ (T : Subgroup X) := (Subgroup.closure_le _).mpr hA
  have hPg : conjugate (Subgroup.closure A) g ≤ (T : Subgroup X) := by
    rw [conjugate_closure, hg]
    exact (Subgroup.closure_le _).mpr hB
  obtain ⟨c, hcM, hc⟩ := S.exists_mem_fusion hz hzM hTM hzT hcomm hP hPg
  refine ⟨c, hcM, ?_⟩
  rw [← hg]
  ext x
  simp only [conjSet, Set.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (hc a (Subgroup.subset_closure ha)).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, hc a (Subgroup.subset_closure ha)⟩

omit [Finite X] in
theorem map_subtype_sylow_subtype {p : ℕ} (T : Sylow p X) {N : Subgroup X} (hTN : (T : Subgroup X) ≤ N) :
    ((T.subtype hTN : Sylow p ↥N) : Subgroup ↥N).map N.subtype = (T : Subgroup X) := by
  rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hTN]

theorem ZDSetup.exists_controlsFusion (S : ZDSetup X Z M) :
    ∃ P : Sylow 2 ↥M, ControlsFusion M ((P : Subgroup ↥M).map M.subtype) := by
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  obtain ⟨T, hTM, hzT, hcomm⟩ := S.exists_sylow_central hz hzM
  refine ⟨T.subtype hTM, ?_⟩
  rw [map_subtype_sylow_subtype T hTM]
  exact S.controlsFusion_sylow hz hzM hTM hzT hcomm

theorem ZDSetup.mem_uniqU_of_mem_productInvolutions (S : ZDSetup X Z M) {u : X}
    (hu : u ∈ productInvolutions Z) (huM : u ∈ M) : u ∈ uniqU M 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := S.exists_controlsFusion
  rw [← uniqC_eq_uniqU_of_controlsFusion 2 P hP]
  exact S.prodDisc.mem_uniqC hu huM

theorem exists_mem_conj_mem_sylow {T : Sylow 2 X} (hTM : (T : Subgroup X) ≤ M) {x : X}
    (hx : x ∈ M) (hx2 : IsPGroup 2 (zpowers x)) : ∃ h ∈ M, h⁻¹ * x * h ∈ (T : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x' : ↥M := ⟨x, hx⟩ with hx'
  have hx2' : IsPGroup 2 (zpowers x') := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hx2
    refine (IsPGroup.iff_card).mpr ⟨n, ?_⟩
    rw [Nat.card_zpowers, hx', Subgroup.orderOf_mk, ← Nat.card_zpowers, hn]
  obtain ⟨Q, hQ⟩ := hx2'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq M Q (T.subtype hTM)
  have hxQ : x ∈ (Q : Subgroup ↥M).map M.subtype := ⟨x', hQ (Subgroup.mem_zpowers _), rfl⟩
  have hmem := mem_map_smul Q h hxQ
  rw [hh, map_subtype_sylow_subtype T hTM] at hmem
  refine ⟨(h : X)⁻¹, M.inv_mem h.2, ?_⟩
  simpa using hmem

omit [Finite X] in
theorem isPGroup_zpowers_conj {p : ℕ} {x : X} (hx : IsPGroup p (zpowers x)) (g : X) :
    IsPGroup p (zpowers (g⁻¹ * x * g)) := by
  have : zpowers (g⁻¹ * x * g) = (zpowers x).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    simp
  rw [this]
  exact hx.map _

theorem ZDSetup.exists_mem_conj_of_isPGroup (S : ZDSetup X Z M) {x : X} (hx : x ∈ M)
    (hx2 : IsPGroup 2 (zpowers x)) {g : X} (hg : g⁻¹ * x * g ∈ M) :
    ∃ m ∈ M, m⁻¹ * x * m = g⁻¹ * x * g := by
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  obtain ⟨T, hTM, hzT, hcomm⟩ := S.exists_sylow_central hz hzM
  have hy2 : IsPGroup 2 (zpowers (g⁻¹ * x * g)) := isPGroup_zpowers_conj hx2 g
  obtain ⟨h, hhM, hh⟩ := exists_mem_conj_mem_sylow hTM hx hx2
  obtain ⟨k, hkM, hk⟩ := exists_mem_conj_mem_sylow hTM hg hy2
  set x' := h⁻¹ * x * h with hx'
  set w := h⁻¹ * g * k with hw
  have hww : w⁻¹ * x' * w = k⁻¹ * (g⁻¹ * x * g) * k := by
    rw [hw, hx']; group
  have hP : zpowers x' ≤ (T : Subgroup X) := Subgroup.zpowers_le.mpr hh
  have hPg : conjugate (zpowers x') w ≤ (T : Subgroup X) := by
    have : conjugate (zpowers x') w = zpowers (w⁻¹ * x' * w) := by
      unfold conjugate
      rw [MonoidHom.map_zpowers]
      simp
    rw [this, hww]
    exact Subgroup.zpowers_le.mpr hk
  obtain ⟨c, hcM, hc⟩ := S.exists_mem_fusion hz hzM hTM hzT hcomm hP hPg
  have hcx := hc x' (Subgroup.mem_zpowers x')
  refine ⟨h * c * k⁻¹, M.mul_mem (M.mul_mem hhM hcM) (M.inv_mem hkM), ?_⟩
  rw [hww] at hcx
  calc (h * c * k⁻¹)⁻¹ * x * (h * c * k⁻¹)
      = k * (c⁻¹ * (h⁻¹ * x * h) * c) * k⁻¹ := by group
    _ = k * (k⁻¹ * (g⁻¹ * x * g) * k) * k⁻¹ := by rw [← hx', hcx]
    _ = g⁻¹ * x * g := by group

omit [Finite X] in
theorem IsProductDisconnected.conjugate_eq_of_mul_inv_mem (h : IsProductDisconnected Z M)
    {x y : X} (hxy : x * y⁻¹ ∈ M) : conjugate M x = conjugate M y := by
  have hnorm : conjugate M (x * y⁻¹) = M := by
    rw [conjugate_eq_iff_mem_normalizer, h.normalizer_eq_self]
    exact hxy
  calc conjugate M x = conjugate (conjugate M (x * y⁻¹)) y := by
        rw [conjugate_conjugate]
        congr 1
        group
    _ = conjugate M y := by rw [hnorm]

theorem ZDSetup.exists_centralizer_conj (S : ZDSetup X Z M) {u : X} (hu : orderOf u = 2)
    {β γ : Subgroup X} (hβ : β ∈ omega M) (hγ : γ ∈ omega M) (hβu : conjugate β u = β)
    (hγu : conjugate γ u = γ) : ∃ c ∈ centralizer ({u} : Set X), conjugate β c = γ := by
  obtain ⟨a, rfl⟩ := hβ
  obtain ⟨b, rfl⟩ := hγ
  have hua : a * u * a⁻¹ ∈ M :=
    mem_conjugate_iff.mp ((S.prodDisc.conjugate_eq_iff_mem ⟨a, rfl⟩).mp hβu)
  have hub : b * u * b⁻¹ ∈ M :=
    mem_conjugate_iff.mp ((S.prodDisc.conjugate_eq_iff_mem ⟨b, rfl⟩).mp hγu)
  have hu2 : IsPGroup 2 (zpowers (b * u * b⁻¹)) := by
    have h1 : IsPGroup 2 (zpowers u) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hu, pow_one]
    have h3 : b * u * b⁻¹ = b⁻¹⁻¹ * u * b⁻¹ := by rw [inv_inv]
    rw [h3]
    exact isPGroup_zpowers_conj h1 b⁻¹
  have hg : (b * a⁻¹)⁻¹ * (b * u * b⁻¹) * (b * a⁻¹) ∈ M := by
    have e : (b * a⁻¹)⁻¹ * (b * u * b⁻¹) * (b * a⁻¹) = a * u * a⁻¹ := by group
    rw [e]; exact hua
  obtain ⟨m, hmM, hm⟩ := S.exists_mem_conj_of_isPGroup hub hu2 hg
  have e : (b * a⁻¹)⁻¹ * (b * u * b⁻¹) * (b * a⁻¹) = a * u * a⁻¹ := by group
  rw [e] at hm
  refine ⟨a⁻¹ * m⁻¹ * b, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have : (a⁻¹ * m⁻¹ * b) * u * (a⁻¹ * m⁻¹ * b)⁻¹ = u := by
      have h2 : m⁻¹ * (b * u * b⁻¹) * m = a * u * a⁻¹ := hm
      calc (a⁻¹ * m⁻¹ * b) * u * (a⁻¹ * m⁻¹ * b)⁻¹
          = a⁻¹ * (m⁻¹ * (b * u * b⁻¹) * m) * a := by group
        _ = a⁻¹ * (a * u * a⁻¹) * a := by rw [h2]
        _ = u := by group
    calc (a⁻¹ * m⁻¹ * b) * u
        = ((a⁻¹ * m⁻¹ * b) * u * (a⁻¹ * m⁻¹ * b)⁻¹) * (a⁻¹ * m⁻¹ * b) := by group
      _ = u * (a⁻¹ * m⁻¹ * b) := by rw [this]
  · rw [conjugate_conjugate]
    apply S.prodDisc.conjugate_eq_of_mul_inv_mem
    have : a * (a⁻¹ * m⁻¹ * b) * b⁻¹ = m⁻¹ := by group
    rw [this]
    exact M.inv_mem hmM

end Lemma42

end CFSG.GH74.Uniqueness
