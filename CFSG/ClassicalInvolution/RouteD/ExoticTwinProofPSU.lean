module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofBasic
public import CFSG.ClassicalInvolution.RouteD.TypeULocal

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.Unitary CFSG.Assembly.LowTwoRank Matrix Module
open scoped MatrixGroups

section Unitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem le_of_commutes_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n} (hn3 : 3 ≤ n)
    {L₁ L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n} (h₁ : IsLongRootSU2 K p f hn L₁ i₁)
    (h₂ : IsLongRootSU2 K p f hn L₂ i₂) (hne : L₁ ≠ L₂) (hc : Commutes L₁ L₂) :
    minusSpaceSU i₁ ≤ fixSpaceSU i₂ ∧ minusSpaceSU i₂ ≤ fixSpaceSU i₁ ∧
      minusSpaceSU i₁ ⊓ minusSpaceSU i₂ = ⊥ := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) (p := p) hp
  have hi : i₁ ≠ i₂ := by
    rintro rfl
    exact hne ((h₁.eq_longRootGroupSU h2).trans (h₂.eq_longRootGroupSU h2).symm)
  rcases lemma_6_5_su hK hp hn3 h₁ h₂ (hc _ h₁.mem _ h₂.mem) hi with ⟨-, h⟩ | ⟨hnot, -⟩
  · exact h
  · exact absurd (Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx i₂ h₂.mem) hnot

theorem commute_of_le_su (hp : p ≠ 2) {hn : 2 ≤ n} {L₁ L₂ : Subgroup (Su K p f n)}
    {i₁ i₂ : Su K p f n} (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂)
    (h12 : minusSpaceSU i₁ ≤ fixSpaceSU i₂) (h21 : minusSpaceSU i₂ ≤ fixSpaceSU i₁) :
    Commute i₁ i₂ := by
  have c₁ := h₁.isCompl hp
  have c₂ := h₂.isCompl hp
  have hmul : ∀ v : Fin n → K, suMat (i₁ * i₂) *ᵥ v = suMat (i₂ * i₁) *ᵥ v := by
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
      (c₁.sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule K (Fin n → K))))
    obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp
      (c₂.sup_eq_top ▸ (Submodule.mem_top : b ∈ (⊤ : Submodule K (Fin n → K))))
    have hd1 : d ∈ fixSpaceSU i₁ := by
      have := Submodule.sub_mem _ hb (h21 hc)
      simpa using this
    have e1a := mem_minusSpaceSU.mp ha
    have e2a := mem_fixSpaceSU.mp (h12 ha)
    have e2c := mem_minusSpaceSU.mp hc
    have e1c := mem_fixSpaceSU.mp (h21 hc)
    have e1d := mem_fixSpaceSU.mp hd1
    have e2d := mem_fixSpaceSU.mp hd
    simp only [suMat_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, e1a, e2a, e2c, e1c, e1d, e2d,
      Matrix.mulVec_neg]
  apply suMat_injective (σ := unitaryInvolution K p f)
  rw [Matrix.ext_iff_mulVec]
  exact hmul

theorem commutes_of_le_su (hp : p ≠ 2) {hn : 2 ≤ n} {L₁ L₂ : Subgroup (Su K p f n)}
    {i₁ i₂ : Su K p f n} (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂)
    (h12 : minusSpaceSU i₁ ≤ fixSpaceSU i₂) (h21 : minusSpaceSU i₂ ≤ fixSpaceSU i₁) :
    Commutes L₁ L₂ := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) (p := p) hp
  have hcc : suMat i₁ * suMat i₂ = suMat i₂ * suMat i₁ := by
    rw [← suMat_mul, ← suMat_mul, (commute_of_le_su hp h₁ h₂ h12 h21).eq]
  have hV : eigSpace (suMat i₁) (-1) ⊓ eigSpace (suMat i₂) (-1) = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rintro v ⟨hv1, hv2⟩
    have : v ∈ minusSpaceSU i₁ ⊓ fixSpaceSU i₁ := ⟨hv1, h21 hv2⟩
    rwa [(h₁.isCompl hp).inf_eq_bot] at this
  intro x hx y hy
  rw [h₁.eq_longRootGroupSU h2] at hx
  rw [h₂.eq_longRootGroupSU h2] at hy
  exact mul_comm_of_inf_eq_bot_su h2 h₁.coe_mul_self h₂.coe_mul_self hcc hV hx hy

theorem commutes_iff_le_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    (hn3 : 3 ≤ n) {L₁ L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n}
    (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂) (hne : L₁ ≠ L₂) :
    Commutes L₁ L₂ ↔ minusSpaceSU i₁ ≤ fixSpaceSU i₂ ∧ minusSpaceSU i₂ ≤ fixSpaceSU i₁ :=
  ⟨fun hc => ⟨(le_of_commutes_su hK hp hn3 h₁ h₂ hne hc).1,
    (le_of_commutes_su hK hp hn3 h₁ h₂ hne hc).2.1⟩,
    fun h => commutes_of_le_su hp h₁ h₂ h.1 h.2⟩

section Planes

variable (K p f) in
@[expose] noncomputable def planeGroupU {n : ℕ} (V : Submodule K (Fin n → K)) :
    Subgroup (Su K p f n) :=
  fixingSubgroup (Su K p f n) (perp (unitaryInvolution K p f) V : Set (Fin n → K))

theorem exists_inv_planeGroupU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 2 ≤ n)
    {V : Submodule K (Fin n → K)} (hV : Nondeg (unitaryInvolution K p f) V)
    (hV2 : finrank K V = 2) :
    ∃ i, IsLongRootSU2 K p f hn (planeGroupU K p f V) i ∧ minusSpaceSU i = V := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have h2 := two_ne_zero_of_charP_ne_two (K := K) (p := p) hp
  obtain ⟨i, hi⟩ := exists_isLongRootSU2_of_nondeg hK hp hn hV hV2 (L := planeGroupU K p f V)
    fun x => by
      unfold planeGroupU
      rw [mem_fixingSubgroup_iff]
      rfl
  refine ⟨i, hi, ?_⟩
  have hperpdim : finrank K (perp (unitaryInvolution K p f) V) = n - 2 := by
    have := finrank_add_finrank_herm_perp hσ hV
    omega
  have hfixdim : finrank K (fixSpaceSU i) = n - 2 := by
    have := Submodule.finrank_add_eq_of_isCompl (hi.isCompl hp)
    rw [Module.finrank_fin_fun, hi.finrank_minusSpaceSU h2] at this
    omega
  have hile : perp (unitaryInvolution K p f) V ≤ fixSpaceSU i := by
    intro w hw
    have hmem : i ∈ planeGroupU K p f V := hi.mem
    have := (mem_fixingSubgroup_iff _).mp hmem w hw
    exact mem_fixSpaceSU.mpr (by rw [← suMat_smul]; exact this)
  have heq : perp (unitaryInvolution K p f) V = fixSpaceSU i :=
    Submodule.eq_of_le_of_finrank_eq hile (by rw [hperpdim, hfixdim])
  have hmin : minusSpaceSU i =
      perp (unitaryInvolution K p f) (perp (unitaryInvolution K p f) V) := by
    rw [heq]
    exact (perp_eigSpace_one hσ h2 i hi.coe_mul_self).symm
  have hVle : V ≤ perp (unitaryInvolution K p f) (perp (unitaryInvolution K p f) V) :=
    fun v hv w hw => herm_eq_zero_comm _ hσ.invol (hw v hv)
  exact (Submodule.eq_of_le_of_finrank_eq (by rw [hmin]; exact hVle)
    (by rw [hV2, hi.finrank_minusSpaceSU h2])).symm

theorem planeGroupU_injective (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 2 ≤ n)
    {V₁ V₂ : Submodule K (Fin n → K)} (h₁ : Nondeg (unitaryInvolution K p f) V₁)
    (h₁' : finrank K V₁ = 2) (h₂ : Nondeg (unitaryInvolution K p f) V₂) (h₂' : finrank K V₂ = 2)
    (h : planeGroupU K p f V₁ = planeGroupU K p f V₂) : V₁ = V₂ := by
  obtain ⟨i₁, hi₁, hm₁⟩ := exists_inv_planeGroupU hK hp hn h₁ h₁'
  obtain ⟨i₂, hi₂, hm₂⟩ := exists_inv_planeGroupU hK hp hn h₂ h₂'
  rw [h] at hi₁
  rw [← hm₁, ← hm₂, hi₁.involution_unique hK hp hi₂]

theorem commutes_planeGroupU_iff (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 2 ≤ n)
    (hn3 : 3 ≤ n) {V₁ V₂ : Submodule K (Fin n → K)} (h₁ : Nondeg (unitaryInvolution K p f) V₁)
    (h₁' : finrank K V₁ = 2) (h₂ : Nondeg (unitaryInvolution K p f) V₂) (h₂' : finrank K V₂ = 2)
    (hne : V₁ ≠ V₂) :
    Commutes (planeGroupU K p f V₁) (planeGroupU K p f V₂) ↔
      Orth (unitaryInvolution K p f) V₁ V₂ := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨i₁, hi₁, hm₁⟩ := exists_inv_planeGroupU hK hp hn h₁ h₁'
  obtain ⟨i₂, hi₂, hm₂⟩ := exists_inv_planeGroupU hK hp hn h₂ h₂'
  have hne' : planeGroupU K p f V₁ ≠ planeGroupU K p f V₂ := fun h =>
    hne (planeGroupU_injective hK hp hn h₁ h₁' h₂ h₂' h)
  have fix₁ : fixSpaceSU i₁ = perp (unitaryInvolution K p f) V₁ := by
    rw [← hi₁.perp_minusSpaceSU hK hp, hm₁]
  have fix₂ : fixSpaceSU i₂ = perp (unitaryInvolution K p f) V₂ := by
    rw [← hi₂.perp_minusSpaceSU hK hp, hm₂]
  rw [commutes_iff_le_su hK hp hn3 hi₁ hi₂ hne', hm₁, hm₂, fix₁, fix₂]
  constructor
  · rintro ⟨h12, -⟩ u hu v hv
    exact h12 hu v hv
  · intro horth
    exact ⟨fun u hu v hv => horth u hu v hv, fun u hu v hv => horth.symm hσ u hu v hv⟩

end Planes

section Twin

omit [Finite K] [CharP K p] in
theorem exists_aniso_of_plane_su {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
    {V : Submodule K (Fin n → K)} (hV : Nondeg σ V) (hV2 : finrank K V = 2) :
    ∃ v ∈ V, herm σ v v ≠ 0 := by
  refine exists_aniso_of_nondeg hσ hV fun h => ?_
  rw [h, finrank_bot] at hV2
  omega

theorem exists_separating_su (hK : Nat.card K = (p ^ f) ^ 2) (hn5 : 5 ≤ n)
    {V₀ V₁ : Submodule K (Fin n → K)} (h₀ : Nondeg (unitaryInvolution K p f) V₀)
    (h₀' : finrank K V₀ = 2) (h₁ : Nondeg (unitaryInvolution K p f) V₁) (h₁' : finrank K V₁ = 2)
    (horth : Orth (unitaryInvolution K p f) V₀ V₁) :
    ∃ V : Submodule K (Fin n → K), Nondeg (unitaryInvolution K p f) V ∧ finrank K V = 2 ∧
      V ≠ V₀ ∧ V ≠ V₁ ∧ Orth (unitaryInvolution K p f) V V₀ ∧
      ¬ Orth (unitaryInvolution K p f) V V₁ := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have hV₁W₀ : V₁ ≤ perp (unitaryInvolution K p f) V₀ := fun v hv s hs =>
    horth.symm hσ v hv s hs
  have hW₀nd := nondeg_herm_perp hσ h₀
  have hW₀dim : finrank K (perp (unitaryInvolution K p f) V₀) = n - 2 := by
    have := finrank_add_finrank_herm_perp hσ h₀
    omega
  have hRnd := Nondeg.inf_perp hσ hW₀nd h₁ hV₁W₀
  have hRdim := finrank_eq_add_finrank_inf_perp hσ h₁ hV₁W₀
  have hRne : perp (unitaryInvolution K p f) V₀ ⊓ perp (unitaryInvolution K p f) V₁ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hRdim
    omega
  obtain ⟨r, hr, hr0⟩ := exists_aniso_of_nondeg hσ hRnd hRne
  obtain ⟨v₁, hv₁, hv₁0⟩ := exists_aniso_of_plane_su hσ h₁ h₁'
  have hvr : herm (unitaryInvolution K p f) v₁ r = 0 := herm_eq_zero_comm _ hσ.invol (hr.2 v₁ hv₁)
  have hrv : herm (unitaryInvolution K p f) r v₁ = 0 := hr.2 v₁ hv₁
  have hv₁ne : v₁ ≠ 0 := fun h => hv₁0 (by rw [h]; simp)
  have hrne : r ≠ 0 := fun h => hr0 (by rw [h]; simp)
  have hdisj : Disjoint (K ∙ v₁) (K ∙ r) :=
    (disjoint_span_perp hv₁0).mono_right
      ((Submodule.span_singleton_le_iff_mem _ _).mpr (mem_perp_span_singleton.mpr hrv))
  have hv₁V : v₁ ∈ K ∙ v₁ ⊔ K ∙ r := Submodule.mem_sup_left (Submodule.mem_span_singleton_self v₁)
  have hrV : r ∈ K ∙ v₁ ⊔ K ∙ r := Submodule.mem_sup_right (Submodule.mem_span_singleton_self r)
  refine ⟨K ∙ v₁ ⊔ K ∙ r, Nondeg.sup_of_orth hσ (nondeg_span_singleton hv₁0)
    (nondeg_span_singleton hr0) (orth_span_singleton_iff.mpr hvr), ?_, ?_, ?_, ?_, ?_⟩
  · rw [finrank_sup_of_disjoint hdisj, finrank_span_singleton hv₁ne, finrank_span_singleton hrne]
  · intro h
    have hh : herm (unitaryInvolution K p f) v₁ v₁ = 0 := by
      have hv₁' : v₁ ∈ V₀ := h ▸ hv₁V
      exact absurd hv₁' (fun hv₁' => by
        have := horth v₁ hv₁' v₁ hv₁
        exact hv₁0 this)
    exact hv₁0 hh
  · intro h
    have hrV₁ : r ∈ V₁ := h ▸ hrV
    exact hr0 (hr.2 r hrV₁)
  · intro u hu w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [herm_add_left, herm_smul_left, herm_smul_left, hr.1 w hw,
      horth.symm hσ v₁ hv₁ w hw, mul_zero, mul_zero, add_zero]
  · intro horth'
    exact hv₁0 (horth' v₁ hv₁V v₁ hv₁)

omit [Finite K] in
theorem false_of_orth_three_four {σ : K ≃+* K}
    {V₀ V₁ V₂ : Submodule K (Fin 4 → K)} (n₁ : Nondeg σ V₁) (n₂ : Nondeg σ V₂)
    (d₀ : finrank K V₀ = 2) (d₁ : finrank K V₁ = 2) (d₂ : finrank K V₂ = 2)
    (o01 : Orth σ V₀ V₁) (o02 : Orth σ V₀ V₂) (o12 : Orth σ V₁ V₂) : False := by
  have hdisj : Disjoint V₀ V₁ := by
    rw [Submodule.disjoint_def]
    intro v hv₀ hv₁
    exact n₁ v hv₁ fun t ht => by
      have := o01 v hv₀ t ht
      exact this
  have hsum := finrank_sup_of_disjoint hdisj
  have hV : finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  have htop : V₀ ⊔ V₁ = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hsum, d₀, d₁, hV])
  have hbot : V₂ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    refine n₂ v hv fun t ht => ?_
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : v ∈ V₀ ⊔ V₁)
    rw [herm_add_left]
    have h1 : herm σ x t = 0 := o02 x hx t ht
    have h2 : herm σ y t = 0 := o12 y hy t ht
    rw [h1, h2, add_zero]
  rw [hbot, finrank_bot] at d₂
  omega

omit [Finite K] [CharP K p] in
theorem disjoint_of_orth {σ : K ≃+* K} {V₀ V₁ : Submodule K (Fin n → K)} (n₁ : Nondeg σ V₁)
    (o : Orth σ V₀ V₁) : Disjoint V₀ V₁ := by
  rw [Submodule.disjoint_def]
  intro v hv₀ hv₁
  exact n₁ v hv₁ fun t ht => o v hv₀ t ht

theorem mem_longRootSetU_iff_plane (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 2 ≤ n)
    {L : Subgroup (Su K p f n)} :
    L ∈ longRootSetU (K := K) (p := p) (f := f) hn ↔
      ∃ V : Submodule K (Fin n → K), Nondeg (unitaryInvolution K p f) V ∧ finrank K V = 2 ∧
        L = planeGroupU K p f V :=
  exists_isLongRootSU2_iff_fixingSubgroup hK hp hn L

theorem planeGroupU_mem (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 2 ≤ n)
    {V : Submodule K (Fin n → K)} (hV : Nondeg (unitaryInvolution K p f) V)
    (hV2 : finrank K V = 2) :
    planeGroupU K p f V ∈ longRootSetU (K := K) (p := p) (f := f) hn :=
  (mem_longRootSetU_iff_plane hK hp hn).mpr ⟨V, hV, hV2, rfl⟩

theorem psu_twinFamily (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n} (hn3 : 3 ≤ n)
    {a : ℕ} (ha : 2 ≤ a) (h : TwinFamily (longRootSetU (K := K) (p := p) (f := f) hn) a) :
    n = 4 ∧ a = 2 := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨R₀, R₁, hP⟩ := h.exists_two ha
  obtain ⟨hR₀, hR₁, hne, hc, htw⟩ := hP
  obtain ⟨V₀, n₀, d₀, rfl⟩ := (mem_longRootSetU_iff_plane hK hp hn).mp hR₀
  obtain ⟨V₁, n₁, d₁, rfl⟩ := (mem_longRootSetU_iff_plane hK hp hn).mp hR₁
  have hne' : V₀ ≠ V₁ := fun e => hne (by rw [e])
  have horth := (commutes_planeGroupU_iff hK hp hn hn3 n₀ d₀ n₁ d₁ hne').mp hc
  have h4 : 4 ≤ n := by
    have hsum := finrank_sup_of_disjoint (disjoint_of_orth n₁ horth)
    have hle := Submodule.finrank_le (V₀ ⊔ V₁)
    rw [Module.finrank_fin_fun] at hle
    omega
  have hn4 : n = 4 := by
    by_contra hn4
    obtain ⟨V, nV, dV, hV0, hV1, hVo, hVn⟩ := exists_separating_su hK (by omega) n₀ d₀ n₁ d₁ horth
    have hS := planeGroupU_mem hK hp hn nV dV
    have hS0 : planeGroupU K p f V ≠ planeGroupU K p f V₀ := fun e =>
      hV0 (planeGroupU_injective hK hp hn nV dV n₀ d₀ e)
    have hS1 : planeGroupU K p f V ≠ planeGroupU K p f V₁ := fun e =>
      hV1 (planeGroupU_injective hK hp hn nV dV n₁ d₁ e)
    have c0 := (commutes_planeGroupU_iff hK hp hn hn3 nV dV n₀ d₀ hV0).mpr hVo
    have := (htw _ hS hS0 hS1).mp c0
    exact hVn ((commutes_planeGroupU_iff hK hp hn hn3 nV dV n₁ d₁ hV1).mp this)
  refine ⟨hn4, ?_⟩
  by_contra ha2
  obtain ⟨R₀', R₁', R₂', ⟨hP₀, hP₁, h01, c01, -⟩, ⟨-, hP₂, h02, c02, -⟩, ⟨-, -, h12, c12, -⟩,
    -, -, -⟩ := h.exists_three (by omega)
  obtain ⟨W₀, m₀, e₀, rfl⟩ := (mem_longRootSetU_iff_plane hK hp hn).mp hP₀
  obtain ⟨W₁, m₁, e₁, rfl⟩ := (mem_longRootSetU_iff_plane hK hp hn).mp hP₁
  obtain ⟨W₂, m₂, e₂, rfl⟩ := (mem_longRootSetU_iff_plane hK hp hn).mp hP₂
  subst hn4
  exact false_of_orth_three_four m₁ m₂ e₀ e₁ e₂
    ((commutes_planeGroupU_iff hK hp hn hn3 m₀ e₀ m₁ e₁ (fun e => h01 (by rw [e]))).mp c01)
    ((commutes_planeGroupU_iff hK hp hn hn3 m₀ e₀ m₂ e₂ (fun e => h02 (by rw [e]))).mp c02)
    ((commutes_planeGroupU_iff hK hp hn hn3 m₁ e₁ m₂ e₂ (fun e => h12 (by rw [e]))).mp c12)

end Twin

end Unitary

section Model

variable {p f : ℕ} [Fact p.Prime]

theorem modelTwinClass_psu (hp2 : p ≠ 2) {n a : ℕ} (hadm : StatedLieAdmissible .PSU n p f)
    (ha : 2 ≤ a) (h : ModelTwinClass p .PSU n f a) : n = 4 ∧ a = 2 := by
  have hf : 1 ≤ f := hadm.2.1
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨e, he⟩ := psu_model_equiv hp2 hadm
  have hF : TwinFamily (longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
      (by omega : 2 ≤ n)) a := TwinFamily.of_equiv e he h
  exact psu_twinFamily (CFSG.LieType.Universal.card_galoisField_two_mul p f hf) hp2 hn3 ha hF

end Model

end CFSG.ClassicalInvolution.RouteD.Exotic
