module

public import CFSG.Goldschmidt75.A2M

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt CFSG.Walter Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {A : Subgroup G} {TM : Sylow 2 M}

theorem omega_comp
    {T : Sylow 2 G} (hcore : CoreHyp M TM (A.subgroupOf M))
    (hTM : (TM : Subgroup M).map M.subtype = (T : Subgroup G) ⊓ M) {K : Subgroup M}
    (hK : IsComponentOf K ⊤) (hZK : Subgroup.center K = ⊥) :
    ∀ t ∈ (T : Subgroup G) ⊓ K.map M.subtype, t ^ 2 = 1 → t ∈ A := by
  obtain ⟨-, hind, hcov⟩ := comp_data hcore hK
  rintro t ⟨htT, ⟨t', ht'K, rfl⟩⟩ ht2
  have ht'TM : t' ∈ (TM : Subgroup M) := by
    have : (t' : G) ∈ (T : Subgroup G) ⊓ M := mem_inf.mpr ⟨htT, t'.2⟩
    rw [← hTM] at this
    obtain ⟨w, hw, hwt⟩ := this
    rwa [show t' = w from Subtype.ext hwt.symm]
  have ht'2 : t' ^ 2 = 1 := Subtype.ext (by simpa using ht2)
  obtain ⟨a, ha, hat⟩ := hind.2 t' (mem_inf.mpr ⟨ht'TM, ht'K⟩) (by rw [ht'2]; exact one_mem _)
  obtain ⟨x, hx, hax⟩ := hcov a ha
  have hxK := (mem_inf.mp hx).2
  have hu : (⟨t' * x⁻¹, K.mul_mem ht'K (K.inv_mem hxK)⟩ : K) ∈ Subgroup.center K := by
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    have h1 := (hat y y.2).symm.trans (hax y y.2)
    simp only [Subgroup.coe_mul]
    calc (y : M) * (t' * x⁻¹) = t' * (t'⁻¹ * y * t') * x⁻¹ := by group
      _ = t' * (x⁻¹ * y * x) * x⁻¹ := by rw [h1]
      _ = t' * x⁻¹ * y := by group
  rw [hZK, mem_bot] at hu
  have h2 : t' * x⁻¹ = 1 := congrArg Subtype.val hu
  rw [mul_inv_eq_one] at h2
  rw [h2]
  exact mem_subgroupOf.mp (mem_inf.mp hx).1

theorem le_normalizer_comp
    [M.Normal] (hcore : CoreHyp M TM (A.subgroupOf M)) {K : Subgroup M}
    (hK : IsComponentOf K ⊤) {s : G} (hs : s ∈ centralizer (A : Set G)) :
    s ∈ normalizer ((K.map M.subtype : Subgroup G) : Set G) := by
  obtain ⟨-, -, hcov⟩ := comp_data hcore hK
  obtain ⟨x, hxA, hxK, hxC⟩ := exists_mem_inf_not_mem_centralizer TM hcore hK hcov
  have hα : (MulAut.conjNormal s : MulAut M) x = x := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hc := mem_centralizer_iff.mp hs (x : G) (mem_subgroupOf.mp hxA)
    calc s * x * s⁻¹ = x * s * s⁻¹ := by rw [hc]
      _ = x := by group
  have hKeq := map_component_eq hK hxK hxC (MulAut.conjNormal s) hα
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨y', hy', rfl⟩
    have : (MulAut.conjNormal s : MulAut M) y' ∈ K := by
      rw [← hKeq]
      exact ⟨y', hy', rfl⟩
    exact ⟨_, this, by simp [MulAut.conjNormal_apply]⟩
  · rintro ⟨w, hw, hwy⟩
    have hw' : w ∈ K.map (MulAut.conjNormal s : MulAut M).toMonoidHom := by rw [hKeq]; exact hw
    obtain ⟨v, hv, hvw⟩ := hw'
    refine ⟨v, hv, ?_⟩
    have h1 : s * (v : G) * s⁻¹ = s * y * s⁻¹ := by
      rw [← hwy, ← hvw]
      simp [MulAut.conjNormal_apply]
    simpa using h1

theorem normalClosure_le_normalizer_comp
    [M.Normal] (hcore : CoreHyp M TM (A.subgroupOf M))
    {S : Subgroup G} (hS : S ≤ centralizer (A : Set G)) {K : Subgroup M}
    (hK : IsComponentOf K ⊤) :
    normalClosure (S : Set G) ≤ normalizer ((K.map M.subtype : Subgroup G) : Set G) := by
  refine (closure_le _).mpr ?_
  intro c hc
  obtain ⟨s, hs, hsc⟩ := Group.mem_conjugatesOfSet_iff.mp hc
  obtain ⟨g, rfl⟩ := isConj_iff.mp hsc
  set K' := K.map (MulAut.conjNormal g⁻¹ : MulAut M).toMonoidHom with hK'def
  have hK' : IsComponentOf K' ⊤ := SStarTransport.isComponentOf_top_map_mulEquiv _ hK
  have hsN := le_normalizer_comp hcore hK' (hS hs)
  have hmem : ∀ x : G, x ∈ K'.map M.subtype ↔ g * x * g⁻¹ ∈ K.map M.subtype := by
    intro x
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨w, hw, ?_⟩
      simp [mul_assoc]
    · rintro ⟨w, hw, hwx⟩
      refine ⟨(MulAut.conjNormal g⁻¹ : MulAut M) w, ⟨w, hw, rfl⟩, ?_⟩
      have hwx' : (w : G) = g * x * g⁻¹ := hwx
      simp only [MulAut.conjNormal_apply, Subgroup.coe_subtype]
      rw [hwx']
      group
  rw [SetLike.mem_coe, mem_normalizer_iff]
  intro y
  have e1 : y ∈ K.map M.subtype ↔ g⁻¹ * y * g ∈ K'.map M.subtype := by
    rw [hmem, show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
  have e2 : g * s * g⁻¹ * y * (g * s * g⁻¹)⁻¹ ∈ K.map M.subtype ↔
      s * (g⁻¹ * y * g) * s⁻¹ ∈ K'.map M.subtype := by
    rw [hmem, show g * (s * (g⁻¹ * y * g) * s⁻¹) * g⁻¹ =
      g * s * g⁻¹ * y * (g * s * g⁻¹)⁻¹ by group]
  rw [e1, e2]
  exact mem_normalizer_iff.mp hsN _

theorem exists_comp
    (hcore : CoreHyp M TM (A.subgroupOf M)) (hZ : CFSG.Open.pCore 2 M = ⊥)
    (hM : M ≠ ⊥) : ∃ K : Subgroup M, IsComponentOf K ⊤ := by
  obtain ⟨h1, -, -⟩ := coreStatement M TM _ hcore.le hcore.comm hcore.closed hcore.gen
    hcore.oddCore
  rw [hZ, bot_sup_eq] at h1
  by_contra hno
  have hE : goldschmidtLayer M = ⊥ := sSup_eq_bot.mpr fun K hK => absurd ⟨K, hK⟩ hno
  apply hM
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : M) ∈ goldschmidtLayer M := h1 ▸ mem_top _
  rw [hE, mem_bot] at this
  exact (mem_bot).mpr (congrArg Subtype.val this)

theorem le_sup_centralizer_comp
    (hcore : CoreHyp M TM (A.subgroupOf M))
    (hZ : CFSG.Open.pCore 2 M = ⊥) {K : Subgroup M} (hK : IsComponentOf K ⊤) :
    M ≤ K.map M.subtype ⊔ centralizer ((K.map M.subtype : Subgroup G) : Set G) := by
  obtain ⟨h1, -, -⟩ := coreStatement M TM _ hcore.le hcore.comm hcore.closed hcore.gen
    hcore.oddCore
  rw [hZ, bot_sup_eq] at h1
  have hle : goldschmidtLayer M ≤ K ⊔ centralizer (K : Set M) := by
    refine sSup_le fun K' hK' => ?_
    by_cases hKK : K' = K
    · rw [hKK]
      exact le_sup_left
    · refine le_sup_of_le_right ?_
      have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne K' K hK' hK hKK
      exact commutator_eq_bot_iff_le_centralizer.mp hc
  rw [h1] at hle
  intro x hx
  have hx' := hle (mem_top (⟨x, hx⟩ : M))
  have hmap := Subgroup.mem_map_of_mem M.subtype hx'
  rw [Subgroup.map_sup] at hmap
  have hle2 : K.map M.subtype ⊔ (centralizer (K : Set M)).map M.subtype ≤
      K.map M.subtype ⊔ centralizer ((K.map M.subtype : Subgroup G) : Set G) := by
    refine sup_le_sup_left ?_ _
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp hc k hk)
  exact hle2 hmap

end CFSG.Goldschmidt75
