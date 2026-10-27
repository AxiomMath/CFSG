module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotMainEnd
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotUniqueField
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotCTField

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.EvenSmallLie
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open F4Pilot (normalizerMulAut)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG)


section Tori

variable {k : Type} [Field k]

theorem units_map_entrywiseHom_mem_leviTorus (ρ : k ≃+* k) {J : Finset (Fin (Tag.rank .E7))}
    {g : ModGL .E7 k} (hg : g ∈ leviTorus k J) :
    Units.map (entrywiseHom ρ.toRingHom) g ∈ leviTorus k J := by
  obtain ⟨b, hb, rfl⟩ := mem_leviTorus.1 hg
  rw [units_map_entrywiseHom_rootDiagUnit_ringEquiv]
  exact rootDiagUnit_mem_leviTorus fun j hj => by rw [hb j hj, map_one]

variable {G : Type} [Group G] {L : Subgroup G}

theorem mem_normalizer_modelToG_leviTorus_of_entrywise (e : L ≃* adjointGroup .E7 k) {n : G}
    (ρ : k ≃+* k)
    (hn : ∀ y : adjointGroup .E7 k,
      n * ((e.symm y : L) : G) * n⁻¹ = ((e.symm (entrywiseAdjointAut .E7 ρ y) : L) : G))
    (J : Finset (Fin (Tag.rank .E7))) :
    n ∈ normalizer (modelToG e (leviTorus k J) : Set G) := by
  have hn' : ∀ y : adjointGroup .E7 k,
      n⁻¹ * ((e.symm y : L) : G) * n = ((e.symm (entrywiseAdjointAut .E7 ρ⁻¹ y) : L) : G) := by
    intro y
    have h := hn (entrywiseAdjointAut .E7 ρ⁻¹ y)
    rw [← MulAut.mul_apply, ← entrywiseAdjointAut_mul, mul_inv_cancel, entrywiseAdjointAut_one,
      MulAut.one_apply] at h
    rw [← h]
    group
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hg
    rw [hn y]
    exact symm_mem_modelToG e (units_map_entrywiseHom_mem_leviTorus ρ hy)
  · intro hg
    obtain ⟨y, hy, hyg⟩ := (mem_modelToG e).1 hg
    have hgy : g = ((e.symm (entrywiseAdjointAut .E7 ρ⁻¹ y) : L) : G) := by
      rw [← hn' y, hyg]
      group
    rw [hgy]
    exact symm_mem_modelToG e (units_map_entrywiseHom_mem_leviTorus ρ⁻¹ hy)

theorem mem_normalizer_pieceSup_of_entrywise (e : L ≃* adjointGroup .E7 k) {n : G}
    (ρ : k ≃+* k)
    (hn : ∀ y : adjointGroup .E7 k,
      n * ((e.symm y : L) : G) * n⁻¹ = ((e.symm (entrywiseAdjointAut .E7 ρ y) : L) : G)) :
    n ∈ normalizer (pieceSup e : Set G) :=
  F4Pilot.mem_normalizer_iSup fun J =>
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
      (mem_normalizer_modelToG_leviTorus_of_entrywise e ρ hn J.1)

theorem normalizer_le_normalizer_pieceSup [Finite k] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (e : L ≃* adjointGroup .E7 k) (hLG : L ≤ pieceSup e) :
    normalizer (L : Set G) ≤ normalizer (pieceSup e : Set G) := by
  intro n hn
  obtain ⟨hNF, -⟩ := even_E7_E8_exact_inner_field_automorphism_normal_form hf k hk .E7 (Or.inl rfl)
  set β : MulAut (adjointGroup .E7 k) := (e.symm.trans (L.normalizerMonoidHom ⟨n, hn⟩)).trans e
    with hβ
  obtain ⟨⟨g, ρ⟩, hgρ, -⟩ := hNF β
  set x : G := ((e.symm g : L) : G) with hxdef
  have hx : x ∈ normalizer (pieceSup e : Set G) := le_normalizer (hLG (e.symm g).2)
  have h1 : ∀ y : adjointGroup .E7 k,
      n * ((e.symm y : L) : G) * n⁻¹ = ((e.symm (β y) : L) : G) := by
    intro y
    rw [hβ, F4Pilot.conj_mulEquiv_apply, MulEquiv.symm_apply_apply,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
  have h2 : ∀ y : adjointGroup .E7 k, β y = g * entrywiseAdjointAut .E7 ρ y * g⁻¹ := fun y =>
    Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_entrywiseAdjointAut]
      exact hgρ y)
  have hn' : ∀ y : adjointGroup .E7 k, (x⁻¹ * n) * ((e.symm y : L) : G) * (x⁻¹ * n)⁻¹ =
      ((e.symm (entrywiseAdjointAut .E7 ρ y) : L) : G) := by
    intro y
    calc (x⁻¹ * n) * ((e.symm y : L) : G) * (x⁻¹ * n)⁻¹ =
          x⁻¹ * (n * ((e.symm y : L) : G) * n⁻¹) * x := by group
      _ = x⁻¹ * ((e.symm (β y) : L) : G) * x := by rw [h1]
      _ = ((e.symm (g⁻¹ * β y * g) : L) : G) := by
        rw [hxdef, map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]
      _ = ((e.symm (entrywiseAdjointAut .E7 ρ y) : L) : G) := by
        rw [h2]
        congr 2
        group
  have hn'N := mem_normalizer_pieceSup_of_entrywise e ρ hn'
  have hnx : n = x * (x⁻¹ * n) := by group
  rw [hnx]
  exact mul_mem hx hn'N

end Tori

section Outer

variable {K : Type} [Field K] [Finite K]

theorem exists_eq_conj_mul_of_outer_E7 {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {α : MulAut (adjointGroup .E7 K)} (hα2 : α ^ 2 = 1)
    (hαo : α ∉ (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range) :
    ∃ (g : adjointGroup .E7 K) (ι : (entrywiseAdjointAutHom (τ := .E7) (K := K)).range),
      ι ^ 2 = 1 ∧ ι ≠ 1 ∧ α = MulAut.conj g * (ι : MulAut (adjointGroup .E7 K)) *
        (MulAut.conj g)⁻¹ := by
  obtain ⟨hcyc, -, hNF⟩ := e7_entrywise_complement hn hK
  obtain ⟨φ, hφC⟩ := exists_conj_mem_range_entrywise_of_outer_E7 hn hK hα2 hαo
  set ι : (entrywiseAdjointAutHom (τ := .E7) (K := K)).range := ⟨φ * α * φ⁻¹, hφC⟩ with hιdef
  have hι2 : ι ^ 2 = 1 := Subtype.ext (by
    change (φ * α * φ⁻¹) ^ 2 = 1
    rw [conj_pow, hα2, mul_one, mul_inv_cancel])
  have hι1 : ι ≠ 1 := by
    intro h
    have h' : φ * α * φ⁻¹ = 1 := congrArg Subtype.val h
    apply hαo
    have : α = 1 := by
      calc α = φ⁻¹ * (φ * α * φ⁻¹) * φ := by group
        _ = 1 := by rw [h']; group
    exact ⟨1, by rw [this, map_one]⟩
  obtain ⟨g, β, hβ, hφg⟩ := hNF φ⁻¹
  have hcomm : β * (ι : MulAut (adjointGroup .E7 K)) = ι * β :=
    congrArg Subtype.val ((IsCyclic.commGroup (α := (entrywiseAdjointAutHom (τ := .E7)
      (K := K)).range)).mul_comm ⟨β, hβ⟩ ι)
  refine ⟨g, ι, hι2, hι1, ?_⟩
  have hι : (ι : MulAut (adjointGroup .E7 K)) = φ * α * φ⁻¹ := rfl
  have hφ : φ = (MulAut.conj g * β)⁻¹ := by rw [← hφg, inv_inv]
  calc α = φ⁻¹ * (φ * α * φ⁻¹) * φ := by group
    _ = (MulAut.conj g * β) * (ι : MulAut (adjointGroup .E7 K)) * (MulAut.conj g * β)⁻¹ := by
        rw [← hι, hφ, inv_inv]
    _ = MulAut.conj g * (β * (ι : MulAut (adjointGroup .E7 K))) * β⁻¹ * (MulAut.conj g)⁻¹ := by
        group
    _ = MulAut.conj g * (ι : MulAut (adjointGroup .E7 K)) * (MulAut.conj g)⁻¹ := by
        rw [hcomm]; group

theorem exists_conj_eq_of_outer_E7 {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {α α' : MulAut (adjointGroup .E7 K)} (hα2 : α ^ 2 = 1) (hα'2 : α' ^ 2 = 1)
    (hαo : α ∉ (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range)
    (hα'o : α' ∉ (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range) :
    ∃ y : adjointGroup .E7 K, MulAut.conj y * α * (MulAut.conj y)⁻¹ = α' := by
  have : Finite (adjointGroup .E7 K) := by
    have : Finite (ModGL Tag.E7 K) := finite_modGL
    infer_instance
  have : Finite (MulAut (adjointGroup .E7 K)) :=
    Finite.of_injective (fun f : MulAut (adjointGroup .E7 K) => (f : adjointGroup .E7 K →
      adjointGroup .E7 K)) DFunLike.coe_injective
  obtain ⟨hcyc, -, -⟩ := e7_entrywise_complement hn hK
  obtain ⟨g, ι, hι2, hι1, rfl⟩ := exists_eq_conj_mul_of_outer_E7 hn hK hα2 hαo
  obtain ⟨g', ι', hι'2, hι'1, rfl⟩ := exists_eq_conj_mul_of_outer_E7 hn hK hα'2 hα'o
  have hιι : ι = ι' := EPilot.eq_of_sq_eq_one_of_ne_one_of_isCyclic hι2 hι'2 hι1 hι'1
  refine ⟨g' * g⁻¹, ?_⟩
  rw [hιι, map_mul, map_inv]
  group

end Outer

section Step3

theorem mem_conjugate_iff_E7 {G : Type*} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  simp only [conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e1 : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
    rw [e1]
    exact hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by group⟩

theorem exists_inner_of_normalizerMulAut_mem_range_E7 {G X : Type*} [Group G] [Group X]
    {G₀ : Subgroup G} (e₀ : G₀ ≃* X) {n : G} (hn : n ∈ normalizer (G₀ : Set G))
    (h : normalizerMulAut e₀ ⟨n, hn⟩ ∈ (MulAut.conj : X →* MulAut X).range) :
    ∃ m ∈ G₀, ∀ x ∈ G₀, n * x * n⁻¹ = m * x * m⁻¹ := by
  obtain ⟨g, hg⟩ := h
  refine ⟨(e₀.symm g : G), (e₀.symm g).2, fun x hx => ?_⟩
  have h1 := F4Pilot.coe_symm_normalizerMulAut_apply e₀ ⟨n, hn⟩ (e₀ ⟨x, hx⟩)
  rw [← hg, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply] at h1
  rw [← h1]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem eq_of_conjugate_E7_field (hset : StandardSetting G L) {f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₀ : Subgroup G}
    {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (e₀ : G₀ ≃* adjointGroup .E7 K₂)
    (htN : t ∈ normalizer (G₀ : Set G))
    (hNL : normalizer (L : Set G) ≤ normalizer (G₀ : Set G)) (h : G)
    (htM : t ∈ normalizer (conjugate G₀ h : Set G))
    (hML : conjugate G₀ h ⊓ centralizer ({t} : Set G) = L) : conjugate G₀ h = G₀ := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₂
  have hf := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hG₀L : G₀ ⊓ centralizer ({t} : Set G) = L :=
    inf_centralizer_eq_of_mem_normalizer_E7_field hset hK e ht hKt hK₂ e₀ htN
  have ht₁N : h * t * h⁻¹ ∈ normalizer (G₀ : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    have hx := mem_normalizer_iff.1 htM (h⁻¹ * x * h)
    rw [mem_conjugate_iff_E7, mem_conjugate_iff_E7] at hx
    have e1 : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    have e2 : h * (t * (h⁻¹ * x * h) * t⁻¹) * h⁻¹ = h * t * h⁻¹ * x * (h * t * h⁻¹)⁻¹ := by
      group
    rw [e1, e2] at hx
    exact hx
  have ht₁2 : (h * t * h⁻¹) ^ 2 = 1 := by
    have e1 : (h * t * h⁻¹) ^ 2 = h * t ^ 2 * h⁻¹ := by rw [sq, sq]; group
    rw [e1, ht2, mul_one, mul_inv_cancel]
  have hAo : normalizerMulAut e₀ ⟨t, htN⟩ ∉
      (MulAut.conj : adjointGroup .E7 K₂ →* MulAut (adjointGroup .E7 K₂)).range := fun hin =>
    not_exists_inner_E7_field hset hK e ht hKt hK₂ e₀
      (exists_inner_of_normalizerMulAut_mem_range_E7 e₀ htN hin)
  have hA₁o : normalizerMulAut e₀ ⟨h * t * h⁻¹, ht₁N⟩ ∉
      (MulAut.conj : adjointGroup .E7 K₂ →* MulAut (adjointGroup .E7 K₂)).range := by
    intro hin
    obtain ⟨m, hm, hmx⟩ := exists_inner_of_normalizerMulAut_mem_range_E7 e₀ ht₁N hin
    set eM : conjugate G₀ h ≃* adjointGroup .E7 K₂ :=
      (G₀.equivMapOfInjective _ (MulAut.conj h⁻¹).injective).symm.trans e₀
    refine not_exists_inner_E7_field hset hK e ht hKt hK₂ eM ⟨h⁻¹ * m * h, ?_, fun y hy => ?_⟩
    · rw [mem_conjugate_iff_E7]
      have e1 : h * (h⁻¹ * m * h) * h⁻¹ = m := by group
      rw [e1]
      exact hm
    · have hy' := mem_conjugate_iff_E7.1 hy
      have h2 := hmx _ hy'
      calc t * y * t⁻¹ = h⁻¹ * ((h * t * h⁻¹) * (h * y * h⁻¹) * (h * t * h⁻¹)⁻¹) * h := by group
        _ = h⁻¹ * (m * (h * y * h⁻¹) * m⁻¹) * h := by rw [h2]
        _ = (h⁻¹ * m * h) * y * (h⁻¹ * m * h)⁻¹ := by group
  obtain ⟨g, hg⟩ := exists_conj_eq_of_outer_E7 (by omega : 1 ≤ 2 * f) hK₂
    (EPilot.action_sq_eq_one (normalizerMulAut e₀) htN ht2)
    (EPilot.action_sq_eq_one (normalizerMulAut e₀) ht₁N ht₁2) hAo hA₁o
  set c : G := ((e₀.symm g : G₀) : G) with hcdef
  have hcG₀ : c ∈ G₀ := (e₀.symm g).2
  have hAc : normalizerMulAut e₀ ⟨c, le_normalizer hcG₀⟩ = MulAut.conj g := by
    rw [F4Pilot.normalizerMulAut_of_mem e₀ hcG₀]
    congr 1
    exact e₀.apply_symm_apply g
  clear_value c
  obtain ⟨z, hzdef⟩ : ∃ z : G, z = (h * t * h⁻¹) * (c * t * c⁻¹)⁻¹ := ⟨_, rfl⟩
  have hzC : z ∈ centralizer (G₀ : Set G) := by
    have hk : (⟨h * t * h⁻¹, ht₁N⟩ : normalizer (G₀ : Set G)) *
        (⟨c, le_normalizer hcG₀⟩ * ⟨t, htN⟩ * (⟨c, le_normalizer hcG₀⟩)⁻¹)⁻¹ ∈
          (normalizerMulAut e₀).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hAc, ← hg]
      group
    rw [EPilot.ker_normalizerMulAut, mem_subgroupOf] at hk
    simpa only [hzdef, Subgroup.coe_mul, Subgroup.coe_inv] using hk
  have hzc : c * z = z * c := mem_centralizer_iff.1 hzC c hcG₀
  obtain ⟨g', hg'def⟩ : ∃ g' : G, g' = c⁻¹ * h := ⟨_, rfl⟩
  have hg't : g' * t * g'⁻¹ = z * t := by
    have ht₁ : h * t * h⁻¹ = z * (c * t * c⁻¹) := by rw [hzdef]; group
    have hczc : c⁻¹ * z * c = z := by
      rw [mul_assoc, ← hzc, ← mul_assoc, inv_mul_cancel, one_mul]
    calc g' * t * g'⁻¹ = c⁻¹ * (h * t * h⁻¹) * c := by rw [hg'def]; group
      _ = c⁻¹ * (z * (c * t * c⁻¹)) * c := by rw [ht₁]
      _ = (c⁻¹ * z * c) * t := by group
      _ = z * t := by rw [hczc]
  have hcomm : ∀ w ∈ G₀, (w * (z * t) = z * t * w ↔ w * t = t * w) := by
    intro w hw
    have hwz : w * z = z * w := mem_centralizer_iff.1 hzC w hw
    constructor
    · intro h1
      have h2 : z * (w * t) = z * (t * w) := by
        calc z * (w * t) = (w * z) * t := by rw [hwz, mul_assoc]
          _ = w * (z * t) := by rw [mul_assoc]
          _ = z * t * w := h1
          _ = z * (t * w) := by rw [mul_assoc]
      exact mul_left_cancel h2
    · intro h1
      calc w * (z * t) = (w * z) * t := (mul_assoc _ _ _).symm
        _ = (z * w) * t := by rw [hwz]
        _ = z * (w * t) := mul_assoc _ _ _
        _ = z * (t * w) := by rw [h1]
        _ = z * t * w := (mul_assoc _ _ _).symm
  have hg'L : g' ∈ normalizer (L : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← hML] at hy
      obtain ⟨hyM, hyt⟩ := mem_inf.1 hy
      have hyM' := mem_conjugate_iff_E7.1 hyM
      have hw : g' * y * g'⁻¹ ∈ G₀ := by
        have e1 : g' * y * g'⁻¹ = c⁻¹ * (h * y * h⁻¹) * c := by rw [hg'def]; group
        rw [e1]
        exact mul_mem (mul_mem (inv_mem hcG₀) hyM') hcG₀
      rw [← hG₀L]
      refine mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 ?_⟩
      have hyt' : y * t = t * y := mem_centralizer_singleton_iff.1 hyt
      have h1 : (g' * y * g'⁻¹) * (g' * t * g'⁻¹) = (g' * t * g'⁻¹) * (g' * y * g'⁻¹) := by
        calc (g' * y * g'⁻¹) * (g' * t * g'⁻¹) = g' * (y * t) * g'⁻¹ := by group
          _ = g' * (t * y) * g'⁻¹ := by rw [hyt']
          _ = (g' * t * g'⁻¹) * (g' * y * g'⁻¹) := by group
      rw [hg't] at h1
      exact (hcomm _ hw).1 h1
    · intro hy
      rw [← hG₀L] at hy
      obtain ⟨hw, hwt⟩ := mem_inf.1 hy
      rw [← hML]
      refine mem_inf.2 ⟨?_, ?_⟩
      · rw [mem_conjugate_iff_E7]
        have e1 : h * y * h⁻¹ = c * (g' * y * g'⁻¹) * c⁻¹ := by rw [hg'def]; group
        rw [e1]
        exact mul_mem (mul_mem hcG₀ hw) (inv_mem hcG₀)
      · rw [mem_centralizer_singleton_iff]
        have hwt' : (g' * y * g'⁻¹) * t = t * (g' * y * g'⁻¹) :=
          mem_centralizer_singleton_iff.1 hwt
        have h1 := (hcomm _ hw).2 hwt'
        rw [← hg't] at h1
        have h2 : g' * (y * t) * g'⁻¹ = g' * (t * y) * g'⁻¹ := by
          calc g' * (y * t) * g'⁻¹ = (g' * y * g'⁻¹) * (g' * t * g'⁻¹) := by group
            _ = (g' * t * g'⁻¹) * (g' * y * g'⁻¹) := h1
            _ = g' * (t * y) * g'⁻¹ := by group
        exact mul_left_cancel (mul_right_cancel h2)
  have hg'N := hNL hg'L
  ext x
  rw [mem_conjugate_iff_E7]
  have e1 : h * x * h⁻¹ = c * (g' * x * g'⁻¹) * c⁻¹ := by rw [hg'def]; group
  rw [e1]
  constructor
  · intro hx
    have h1 : g' * x * g'⁻¹ ∈ G₀ := by
      have e2 : g' * x * g'⁻¹ = c⁻¹ * (c * (g' * x * g'⁻¹) * c⁻¹) * c := by group
      rw [e2]
      exact mul_mem (mul_mem (inv_mem hcG₀) hx) hcG₀
    exact (mem_normalizer_iff.1 hg'N x).2 h1
  · intro hx
    exact mul_mem (mul_mem hcG₀ ((mem_normalizer_iff.1 hg'N x).1 hx)) (inv_mem hcG₀)

end Step3

section PieceSup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem eq_of_conjugate_pieceSup_E7_field (hset : StandardSetting G L) {K₂ : Type} [Field K₂]
    {σ : K₂ ≃+* K₂} {f : ℕ} (hK₂ : Nat.card K₂ = 2 ^ (2 * f))
    (hk : Nat.card (fixSubfield σ) = 2 ^ f) (e : L ≃* adjointGroup .E7 (fixSubfield σ)) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (Ψ : adjointGroup .E7 K₂ ≃* pieceSup e)
    (hΨfix : ∀ x : adjointGroup .E7 (fixSubfield σ),
      ((Ψ (fixedFieldInclusion σ x) : pieceSup e) : G) = ((e.symm x : L) : G)) (h : G)
    (htM : t ∈ normalizer (conjugate (pieceSup e) h : Set G))
    (hML : conjugate (pieceSup e) h ⊓ centralizer ({t} : Set G) = L) :
    conjugate (pieceSup e) h = pieceSup e := by
  have : Finite (fixSubfield σ) := F4Pilot.finite_of_natCard_eq_two_pow hk
  have hf : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hk
  have hLG : L ≤ pieceSup e := fun g hg => by
    have h1 := hΨfix (e ⟨g, hg⟩)
    rw [MulEquiv.symm_apply_apply] at h1
    have h2 : g = ((Ψ (fixedFieldInclusion σ (e ⟨g, hg⟩)) : pieceSup e) : G) := h1.symm
    rw [h2]
    exact (Ψ _).2
  exact eq_of_conjugate_E7_field hset hk e ht hKt hK₂ Ψ.symm (mem_normalizer_pieceSup htC)
    (normalizer_le_normalizer_pieceSup hf hk e hLG) h htM hML

end PieceSup

end CFSG.SeitzReduction.E7Pilot
