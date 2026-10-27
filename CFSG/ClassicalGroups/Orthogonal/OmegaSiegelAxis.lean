module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelSetting
public import CFSG.HardMathSupport.Kantor79.DisjointLongRoot

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.ClassicalGroups.Orthogonal.SiegelSL CFSG.RankThree.GF2n.Smith81 QuadraticMap Module
open scoped commutatorElement

variable {K' : Type*} [Field K'] [CharP K' 2] [Finite K'] {N : Type*} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N} {K : Type*} [Field K]
  [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qf : QuadraticForm K V} {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

omit [Finite K] [FiniteDimensional K V] in
private theorem commute_of_orthogonal_univ (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {s s' : V ≃ₗ[K] V} (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s')
    (h : ∀ x ∈ movedSpace s, ∀ y ∈ movedSpace s', polar Qf x y = 0) : s * s' = s' * s := by
  have hQ := nondegenerate_polarBilin hnd
  obtain ⟨a, b, ha, hb, hab, hli, hmem, hne⟩ :=
    (isLongRootElement_iff_exists_mem_longRootGroup hQ).mp hs
  obtain ⟨a', b', ha', hb', hab', hli', hmem', hne'⟩ :=
    (isLongRootElement_iff_exists_mem_longRootGroup hQ).mp hs'
  have h1 := (mem_longRootGroup_isLongRootElement hnd hli hmem hne).2
  have h2 := (mem_longRootGroup_isLongRootElement hnd hli' hmem' hne').2
  rw [h1, h2] at h
  exact longRootGroup_comm_of_orthogonal ha hb hab ha' hb' hab' h hmem hmem'

private theorem axes_eq_of_copl (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {E₁ E₂ : Subgroup (V ≃ₗ[K] V)} (hE₁ : IsSiegelFamily Qf E₁) (hE₂ : IsSiegelFamily Qf E₂)
    (hc : Copl E₁) {x y : V ≃ₗ[K] V} (hx : x ∈ E₁) (hy : y ∈ E₂) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : x * y ≠ y * x) {A A' : Submodule K V} (hA₁ : A ∈ axes E₁) (hA₂ : A ∈ axes E₂)
    (hA₁' : A' ∈ axes E₁) (hA₂' : A' ∈ axes E₂) : A = A' := by
  have h3 := hE₁.finrank_commutatorSpace_of_copl hnd hc
  have hnle : ¬ commutatorSpace E₁ ≤ commutatorSpace E₂ := by
    intro hle
    refine hxy (commute_of_orthogonal_univ hnd (hE₁.siegel x hx hx1) (hE₂.siegel y hy hy1) ?_)
    intro u hu v hv
    exact polar_eq_zero_of_totallySingular (hE₂.qf_eq_zero_of_mem_commutatorSpace hnd)
      (hle (movedSpace_le_commutatorSpace hx hu)) (movedSpace_le_commutatorSpace hy hv)
  have hlt : commutatorSpace E₁ ⊓ commutatorSpace E₂ < commutatorSpace E₁ :=
    lt_of_le_of_ne inf_le_left fun h => hnle (h ▸ inf_le_right)
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  have key : ∀ B ∈ axes E₁, B ∈ axes E₂ → B = commutatorSpace E₁ ⊓ commutatorSpace E₂ := by
    intro B h₁ h₂
    refine Submodule.eq_of_le_of_finrank_le (le_inf (le_commutatorSpace_of_mem_axes h₁)
      (le_commutatorSpace_of_mem_axes h₂)) ?_
    have := hE₁.finrank_eq_two hnd h₁
    omega
  exact (key A hA₁ hA₂).trans (key A' hA₁' hA₂').symm

private theorem axes_eq_of_conc (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {E₁ E₂ : Subgroup (V ≃ₗ[K] V)} (hE₁ : IsSiegelFamily Qf E₁) (hE₂ : IsSiegelFamily Qf E₂)
    (hc₁ : Conc E₁) (hc₂ : Conc E₂) {x y : V ≃ₗ[K] V} (hx : x ∈ E₁) (hy : y ∈ E₂)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hdisj : movedSpace x ⊓ movedSpace y = ⊥)
    {A A' : Submodule K V} (hA₁ : A ∈ axes E₁) (hA₂ : A ∈ axes E₂)
    (hA₁' : A' ∈ axes E₁) (hA₂' : A' ∈ axes E₂) : A = A' := by
  have h1 := hE₁.finrank_axisInf_of_conc hnd hc₁
  have h2 := hE₂.finrank_axisInf_of_conc hnd hc₂
  have hP₁ : axisInf E₁ ≤ movedSpace x := axisInf_le ⟨x, hx, hx1, rfl⟩
  have hP₂ : axisInf E₂ ≤ movedSpace y := axisInf_le ⟨y, hy, hy1, rfl⟩
  have hinf : axisInf E₁ ⊓ axisInf E₂ = ⊥ := eq_bot_iff.mpr (hdisj ▸ inf_le_inf hP₁ hP₂)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (axisInf E₁) (axisInf E₂)
  rw [hinf, finrank_bot, h1, h2] at hsum
  have key : ∀ B ∈ axes E₁, B ∈ axes E₂ → B = axisInf E₁ ⊔ axisInf E₂ := by
    intro B h₁ h₂
    refine (Submodule.eq_of_le_of_finrank_le (sup_le (axisInf_le h₁) (axisInf_le h₂)) ?_).symm
    have := hE₁.finrank_eq_two hnd h₁
    omega
  exact (key A hA₁ hA₂).trans (key A' hA₁' hA₂').symm

private theorem axes_eq_of_not_commute (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {E₁ E₂ : Subgroup (V ≃ₗ[K] V)} (hE₁ : IsSiegelFamily Qf E₁) (hE₂ : IsSiegelFamily Qf E₂)
    {x y : V ≃ₗ[K] V} (hx : x ∈ E₁) (hy : y ∈ E₂) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : x * y ≠ y * x) (hdisj : movedSpace x ⊓ movedSpace y = ⊥)
    {A A' : Submodule K V} (hA₁ : A ∈ axes E₁) (hA₂ : A ∈ axes E₂)
    (hA₁' : A' ∈ axes E₁) (hA₂' : A' ∈ axes E₂) : A = A' := by
  rcases hE₁.conc_or_copl hnd with hc₁ | hc₁
  · rcases hE₂.conc_or_copl hnd with hc₂ | hc₂
    · exact axes_eq_of_conc hnd hE₁ hE₂ hc₁ hc₂ hx hy hx1 hy1 hdisj hA₁ hA₂ hA₁' hA₂'
    · exact axes_eq_of_copl hnd hE₂ hE₁ hc₂ hy hx hy1 hx1 (Ne.symm hxy) hA₂ hA₁ hA₂' hA₁'
  · exact axes_eq_of_copl hnd hE₁ hE₂ hc₁ hx hy hx1 hy1 hxy hA₁ hA₂ hA₁' hA₂'

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem linearIndependent_pair_smul {u v : N} (h : LinearIndependent K' ![u, v])
    {μ : K'} (hμ : μ ≠ 0) : LinearIndependent K' ![u, μ • v] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  have h' := h s (t * μ) (by rw [mul_smul]; exact hst)
  exact ⟨h'.1, (mul_eq_zero.mp h'.2).resolve_right hμ⟩

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem linearIndependent_pair_of_polar_zero {u v z : N} (hu : u ≠ 0)
    (huz : polar QN u z = 0) (hvz : polar QN v z ≠ 0) : LinearIndependent K' ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : t * polar QN v z = 0 := by
    have h := congrArg (fun x => polar QN x z) hst
    simpa [polar_add_left, polar_smul_left_eq, huz] using h
  have ht : t = 0 := (mul_eq_zero.mp h1).resolve_right hvz
  subst ht
  rw [zero_smul, add_zero] at hst
  exact ⟨(smul_eq_zero.mp hst).resolve_right hu, rfl⟩

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem linearIndependent_triple_of_polar {a d u z : N} (hli : LinearIndependent K' ![a, d])
    (haz : polar QN a z = 0) (hdz : polar QN d z = 0) (huz : polar QN u z ≠ 0) :
    LinearIndependent K' ![a, d, u] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
  have h2 : g 2 * polar QN u z = 0 := by
    have h := congrArg (fun x => polar QN x z) hg
    simpa [polar_add_left, polar_smul_left_eq, haz, hdz] using h
  have hg2 : g 2 = 0 := (mul_eq_zero.mp h2).resolve_right huz
  rw [hg2, zero_smul, add_zero] at hg
  obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.mp hli (g 0) (g 1) hg
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact hg2

omit [Finite K'] [FiniteDimensional K' N] in
private theorem qf_eq_zero_of_mem_span_triple {a d u : N} (ha : QN a = 0) (hd : QN d = 0)
    (hu : QN u = 0) (had : polar QN a d = 0) (hau : polar QN a u = 0) (hdu : polar QN d u = 0) :
    ∀ w ∈ Submodule.span K' ({a, d, u} : Set N), QN w = 0 := by
  have hda : polar QN d a = 0 := by rw [polar_comm]; exact had
  have hua : polar QN u a = 0 := by rw [polar_comm]; exact hau
  have hud : polar QN u d = 0 := by rw [polar_comm]; exact hdu
  intro w hw
  refine map_eq_zero_of_mem_span (S := {a, d, u}) ?_ ?_ hw
  · intro x hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · intro x hx y hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | assumption | exact SiegelRT1.polar_self_eq_zero _

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem finrank_span_triple {a d u : N} (h : LinearIndependent K' ![a, d, u]) :
    finrank K' (Submodule.span K' ({a, d, u} : Set N)) = 3 := by
  have h3 := finrank_span_eq_card h
  rw [show Set.range ![a, d, u] = ({a, d, u} : Set N) by
    ext x; simp [eq_comm]; tauto] at h3
  simpa using h3

omit [Finite K] [FiniteDimensional K V] in
private theorem ne_one_of_isLongRootElement (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {s : V ≃ₗ[K] V} (hs : IsLongRootElement Qf s) : s ≠ 1 :=
  fun h => not_isLongRootElement_one hnd (h ▸ hs)

omit [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem rhoE_mem_map_sigma (hnd : ∀ x : N, (∀ y, polar QN x y = 0) → x = 0) {u w : N}
    (hu : QN u = 0) (hw : QN w = 0) (huw : polar QN u w = 0) (hli : LinearIndependent K' ![u, w])
    {π : Submodule K' N} (hu' : u ∈ π) (hw' : w ∈ π) :
    rhoE ρ u w ∈ ((sigmaGroup QN π).subgroupOf (elementaryGroup QN)).map ρ := by
  have hu0 : u ≠ 0 := by simpa using hli.ne_zero 0
  have hwu : w ∉ Submodule.span K' ({u} : Set N) := fun hmem => by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact (LinearIndependent.pair_iff' hu0).mp hli c hc
  obtain ⟨h1, h2⟩ := isLongRootElement_eichler hnd hu hw huw hu0 hwu
  refine Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr
    (isLongRootElement_mem_sigmaGroup h1 ?_))
  rw [h2, Submodule.span_le]
  exact Set.insert_subset_iff.mpr ⟨hu', Set.singleton_subset_iff.mpr hw'⟩

omit [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem commutatorElement_rhoE {a b c d : N} (ha : QN a = 0) (hb : QN b = 0)
    (hc : QN c = 0) (hd : QN d = 0) (hab : polar QN a b = 0) (hcd : polar QN c d = 0)
    (hac : polar QN a c = 0) (had : polar QN a d = 0) (hbd : polar QN b d = 0) :
    ⁅rhoE ρ a b, rhoE ρ c d⁆ = rhoE ρ a (polar QN b c • d) := by
  unfold rhoE
  rw [← map_commutatorElement]
  congr 1
  exact Subtype.ext (commutatorElement_eichler ha hb hc hd hab hcd hac had hbd)

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem OmegaSetting.single_axis_not_commute (hs : OmegaSetting QN Qf ρ) {a b c d : N}
    (ha : QN a = 0) (hb : QN b = 0) (hc : QN c = 0) (hd : QN d = 0) (hab : polar QN a b = 0)
    (hcd : polar QN c d = 0) (hac : polar QN a c = 0) (had : polar QN a d = 0)
    (hbd : polar QN b d = 0) (hbc : polar QN b c = 1) (hlad : LinearIndependent K' ![a, d]) :
    rhoE ρ a b * rhoE ρ c d ≠ rhoE ρ c d * rhoE ρ a b := by
  intro h
  have h1 : ⁅rhoE ρ a b, rhoE ρ c d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h
  rw [commutatorElement_rhoE ha hb hc hd hab hcd hac had hbd, hbc, one_smul] at h1
  exact ne_one_of_isLongRootElement hs.nd (hs.isLongRootElement_rhoE ha hd had hlad) h1

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem OmegaSetting.single_axis_mem_axes (hs : OmegaSetting QN Qf ρ) {u w : N}
    (hu : QN u = 0) (hw : QN w = 0) (huw : polar QN u w = 0) (hli : LinearIndependent K' ![u, w])
    {π : Submodule K' N} (hu' : u ∈ π) (hw' : w ∈ π) :
    movedSpace (rhoE ρ u w) ∈
      axes (((sigmaGroup QN π).subgroupOf (elementaryGroup QN)).map ρ) :=
  ⟨rhoE ρ u w, rhoE_mem_map_sigma (fun x hx => hs.ndN.1 x fun y => hx y) hu hw huw hli hu' hw',
    ne_one_of_isLongRootElement hs.nd (hs.isLongRootElement_rhoE hu hw huw hli), rfl⟩

private theorem OmegaSetting.single_axis_eq (hs : OmegaSetting QN Qf ρ) {a d b c : N}
    (ha : QN a = 0) (hd : QN d = 0) (hb : QN b = 0) (hc : QN c = 0) (had : polar QN a d = 0)
    (hab : polar QN a b = 0) (hdb : polar QN d b = 0) (hac : polar QN a c = 0)
    (hdc : polar QN d c = 0) (hbc : polar QN b c = 1) (hli : LinearIndependent K' ![a, d])
    {μ ν : K'} (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    movedSpace (rhoE ρ a (μ • d)) = movedSpace (rhoE ρ a (ν • d)) := by
  have hndN : ∀ x : N, (∀ y, polar QN x y = 0) → x = 0 := fun x hx => hs.ndN.1 x fun y => hx y
  have hcd : polar QN c d = 0 := by rw [polar_comm]; exact hdc
  have hbd : polar QN b d = 0 := by rw [polar_comm]; exact hdb
  have hcb : polar QN c b = 1 := by rw [polar_comm]; exact hbc
  have hbc0 : polar QN b c ≠ 0 := by rw [hbc]; exact one_ne_zero
  have hcb0 : polar QN c b ≠ 0 := by rw [hcb]; exact one_ne_zero
  have ha0 : a ≠ 0 := by simpa using hli.ne_zero 0
  have hd0 : d ≠ 0 := by simpa using hli.ne_zero 1
  have hli_ab : LinearIndependent K' ![a, b] := linearIndependent_pair_of_polar_zero ha0 hac hbc0
  have hli_cd : LinearIndependent K' ![c, d] :=
    LinearIndependent.pair_symm_iff.mpr (linearIndependent_pair_of_polar_zero hd0 hdb hcb0)
  have hli₁ : LinearIndependent K' ![a, d, b] := linearIndependent_triple_of_polar hli hac hdc hbc0
  have hli₂ : LinearIndependent K' ![a, d, c] := linearIndependent_triple_of_polar hli hab hdb hcb0
  have ha₁ : a ∈ Submodule.span K' ({a, d, b} : Set N) := Submodule.subset_span (by simp)
  have hd₁ : d ∈ Submodule.span K' ({a, d, b} : Set N) := Submodule.subset_span (by simp)
  have hb₁ : b ∈ Submodule.span K' ({a, d, b} : Set N) := Submodule.subset_span (by simp)
  have ha₂ : a ∈ Submodule.span K' ({a, d, c} : Set N) := Submodule.subset_span (by simp)
  have hd₂ : d ∈ Submodule.span K' ({a, d, c} : Set N) := Submodule.subset_span (by simp)
  have hc₂ : c ∈ Submodule.span K' ({a, d, c} : Set N) := Submodule.subset_span (by simp)
  have hE₁ := hs.isSiegelFamily_map (π := Submodule.span K' ({a, d, b} : Set N))
    (qf_eq_zero_of_mem_span_triple ha hd hb had hab hdb) (finrank_span_triple hli₁)
  have hE₂ := hs.isSiegelFamily_map (π := Submodule.span K' ({a, d, c} : Set N))
    (qf_eq_zero_of_mem_span_triple ha hd hc had hac hdc) (finrank_span_triple hli₂)
  have hmem : ∀ τ : K', τ ≠ 0 →
      movedSpace (rhoE ρ a (τ • d)) ∈ axes (((sigmaGroup QN
        (Submodule.span K' ({a, d, b} : Set N))).subgroupOf (elementaryGroup QN)).map ρ) ∧
      movedSpace (rhoE ρ a (τ • d)) ∈ axes (((sigmaGroup QN
        (Submodule.span K' ({a, d, c} : Set N))).subgroupOf (elementaryGroup QN)).map ρ) := by
    intro τ hτ
    have hτd : QN (τ • d) = 0 := by rw [QuadraticMap.map_smul, hd, smul_zero]
    have hpol : polar QN a (τ • d) = 0 := by rw [polar_smul_right_eq, had, mul_zero]
    have hlτ := linearIndependent_pair_smul hli hτ
    exact ⟨hs.single_axis_mem_axes ha hτd hpol hlτ ha₁ (Submodule.smul_mem _ τ hd₁),
      hs.single_axis_mem_axes ha hτd hpol hlτ ha₂ (Submodule.smul_mem _ τ hd₂)⟩
  exact axes_eq_of_not_commute hs.nd hE₁ hE₂ (rhoE_mem_map_sigma hndN ha hb hab hli_ab ha₁ hb₁)
    (rhoE_mem_map_sigma hndN hc hd hcd hli_cd hc₂ hd₂)
    (ne_one_of_isLongRootElement hs.nd (hs.isLongRootElement_rhoE ha hb hab hli_ab))
    (ne_one_of_isLongRootElement hs.nd (hs.isLongRootElement_rhoE hc hd hcd hli_cd))
    (hs.single_axis_not_commute ha hb hc hd hab hcd hac had hbd hbc hli)
    (hs.movedSpace_rhoE_inf_eq_bot ha hb hc hd hab hcd hac had hbd hbc0 hli_ab hli_cd hli)
    (hmem μ hμ).1 (hmem μ hμ).2 (hmem ν hν).1 (hmem ν hν).2

theorem OmegaSetting.movedSpace_rhoE_smul (hs : OmegaSetting QN Qf ρ) {a d b c : N}
    (ha : QN a = 0) (hd : QN d = 0) (hb : QN b = 0) (hc : QN c = 0) (had : polar QN a d = 0)
    (hab : polar QN a b = 0) (hdb : polar QN d b = 0) (hac : polar QN a c = 0)
    (hdc : polar QN d c = 0) (hbc : polar QN b c = 1) (hli : LinearIndependent K' ![a, d])
    {μ : K'} (hμ : μ ≠ 0) :
    movedSpace (rhoE ρ a (μ • d)) = movedSpace (rhoE ρ a d) := by
  have h := hs.single_axis_eq ha hd hb hc had hab hdb hac hdc hbc hli hμ
    (one_ne_zero : (1 : K') ≠ 0)
  rwa [one_smul] at h

theorem OmegaSetting.movedSpace_rhoE_smul_le (hs : OmegaSetting QN Qf ρ) {a d b c : N}
    (ha : QN a = 0) (hd : QN d = 0) (hb : QN b = 0) (hc : QN c = 0) (had : polar QN a d = 0)
    (hab : polar QN a b = 0) (hdb : polar QN d b = 0) (hac : polar QN a c = 0)
    (hdc : polar QN d c = 0) (hbc : polar QN b c = 1) (hli : LinearIndependent K' ![a, d])
    (μ : K') : movedSpace (rhoE ρ a (μ • d)) ≤ movedSpace (rhoE ρ a d) := by
  by_cases hμ : μ = 0
  · subst hμ
    rw [zero_smul, rhoE_zero_right]
    rintro _ ⟨x, rfl⟩
    simp
  · exact (hs.movedSpace_rhoE_smul ha hd hb hc had hab hdb hac hdc hbc hli hμ).le

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
