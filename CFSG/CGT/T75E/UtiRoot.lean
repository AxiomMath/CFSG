module

public import CFSG.CGT.T75E.Basic
public import CFSG.Timmesfeld.Reduction.RootClass
public import CFSG.Timmesfeld.ARS.Sec4Defs

public section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld

variable {K : Type} [Group K] {T : Subgroup K}

theorem rootSet_subset_of_isWC (hT : IsWC T) {a : K} (ha : a ∈ T) :
    rootSet (classD T) a ⊆ T := by
  intro e he
  obtain ⟨g, t, ht, ht1, rfl⟩ := he.1
  have hTe : ∀ y ∈ T, (g⁻¹ * t * g) * y = y * (g⁻¹ * t * g) := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1, mul_one, one_mul]
    · exact ((he.2 y (mem_classD_of_mem hy hy1)).2 (elemAbelian_mul_comm hT.1 ha hy)).eq
  have hconj : conjSubgroup g T ≤ Subgroup.centralizer ({t} : Set K) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    have hy := hTe (g⁻¹ * x * g) (mem_conjSubgroup.1 hx)
    calc s * x = g * ((g⁻¹ * s * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * s * g)) * g⁻¹ := by rw [hy]
      _ = x * s := by group
  have h1 : conjSubgroup g T = T := (hT.2 t ht ht1).2 g hconj
  have h2 : t ∈ conjSubgroup g T := by rw [h1]; exact ht
  exact mem_conjSubgroup.1 h2

theorem rootGroup_le_of_isWC (hT : IsWC T) {a : K} (ha : a ∈ T) :
    rootGroup (classD T) a ≤ T :=
  (Subgroup.closure_le T).2 (rootSet_subset_of_isWC hT ha)

theorem hyp_ne_top [Finite K] (h : Lemma26Hyp K T) : T ≠ ⊤ := by
  intro hT
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hyp_ne_bot h)
  have ha1' : a ≠ 1 := fun e => ha1 (Subtype.ext e)
  refine hyp_classD_inf_center h (mem_classD_of_mem ha ha1') (Subgroup.mem_center_iff.2 fun g => ?_)
  have hg : g ∈ T := by rw [hT]; exact Subgroup.mem_top g
  exact elemAbelian_mul_comm h.1.1 hg ha

section Root

variable {R : Set (Subgroup K)}

theorem exists_commuting_ne (hars : ARS.Hyp K R) {A : Subgroup K} (hA : A ∈ R) :
    ∃ B ∈ R, B ≠ A ∧ ARS.Commuting A B := by
  obtain ⟨E, hE, F, hF, hC, hCE, hCF⟩ := hars.nondeg
  have hne : ⁅E, F⁆ ≠ E := by
    intro h
    have hEF : ARS.Commuting E F := h ▸ hCF
    have hbot : ⁅E, F⁆ = ⊥ := ARS.commuting_iff_commutator_eq_bot.1 hEF
    exact hars.root.ne_bot E hE (h.symm.trans hbot)
  obtain ⟨g, hg⟩ := hars.root.exists_conjSub_eq hE hA
  refine ⟨ARS.conjSub ⁅E, F⁆ g, hars.root.conjSub_mem hC g, fun h => hne ?_, ?_⟩
  · rw [← hg] at h
    exact Subgroup.map_injective (MulAut.conj g).injective h
  · rw [← hg]
    exact (ARS.Commuting.symm hCE).conjSub g

end Root

section TI

@[expose] def rootGroupsIn (T : Subgroup K) : Set (Subgroup K) :=
  {E | E ∈ rootClass (classD T) ∧ E ≤ T}

theorem rootGroup_mem_rootGroupsIn (hT : IsWC T) {a : K} (ha : a ∈ T) (ha1 : a ≠ 1) :
    rootGroup (classD T) a ∈ rootGroupsIn T :=
  ⟨⟨a, mem_classD_of_mem ha ha1, rfl⟩, rootGroup_le_of_isWC hT ha⟩

theorem rootGroupsIn_nonempty (hyp : Lemma26Hyp K T) : (rootGroupsIn T).Nonempty := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hyp_ne_bot hyp)
  exact ⟨_, rootGroup_mem_rootGroupsIn hyp.1 ha fun e => ha1 (Subtype.ext e)⟩

theorem not_le_rootGroup (hyp : Lemma26Hyp K T) (hars : ARS.Hyp K (rootClass (classD T)))
    {a : K} (ha : a ∈ T) (ha1 : a ≠ 1) : ¬ T ≤ rootGroup (classD T) a := by
  intro hle
  have hA : rootGroup (classD T) a ∈ rootClass (classD T) := ⟨a, mem_classD_of_mem ha ha1, rfl⟩
  have hAT : rootGroup (classD T) a = T := le_antisymm (rootGroup_le_of_isWC hyp.1 ha) hle
  obtain ⟨B, hB, hBA, hcomm⟩ := exists_commuting_ne hars hA
  obtain ⟨g, hg⟩ := hars.root.exists_conjSub_eq hA hB
  have hgT : conjSubgroup g T = B := by rw [← hg, hAT]; rfl
  have h1 : conjSubgroup g T = T := by
    refine (hyp.1.2 a ha ha1).2 g fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    rw [hgT] at hx
    exact (hcomm s (by rw [hAT]; exact ha) x hx).eq
  exact hBA (hgT.symm.trans (h1.trans hAT.symm))

theorem conjSub_inv_le_iff (E T : Subgroup K) (g : K) :
    ARS.conjSub E g⁻¹ ≤ T ↔ E ≤ conjSubgroup g T := by
  constructor
  · intro h
    have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h
    change ARS.conjSub (ARS.conjSub E g⁻¹) g ≤ ARS.conjSub T g at this
    rwa [← ARS.conjSub_mul, mul_inv_cancel, ARS.conjSub_one] at this
  · intro h
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h
    change ARS.conjSub E g⁻¹ ≤ ARS.conjSub (ARS.conjSub T g) g⁻¹ at this
    rwa [← ARS.conjSub_mul, inv_mul_cancel, ARS.conjSub_one] at this

theorem isTI_rootGroupsIn (hyp : Lemma26Hyp K T) (hars : ARS.Hyp K (rootClass (classD T))) :
    ARS.IsTI (rootClass (classD T)) (rootGroupsIn T) := by
  have := hars.finite
  have hR := hars.root
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hyp_ne_bot hyp)
  have ha1' : a ≠ 1 := fun e => ha1 (Subtype.ext e)
  refine ⟨fun E hE => hE.1, ?_, ?_, fun g => ?_⟩
  ·
    obtain ⟨b, hbT, hb⟩ : ∃ b ∈ T, b ∉ rootGroup (classD T) a := by
      by_contra hcon
      push Not at hcon
      exact not_le_rootGroup hyp hars ha ha1' hcon
    have hb1 : b ≠ 1 := fun e => hb (e ▸ one_mem _)
    refine ⟨rootGroup (classD T) a, rootGroup_mem_rootGroupsIn hyp.1 ha ha1', rootGroup
      (classD T) b, rootGroup_mem_rootGroupsIn hyp.1 hbT hb1, fun e => hb ?_⟩
    rw [e]
    exact Subgroup.subset_closure (mem_rootSet_self (mem_classD_of_mem hbT hb1))
  ·
    intro hΔ
    refine hyp_ne_top hyp (eq_top_iff.2 ?_)
    rw [← hyp.2.2.2.2, Subgroup.closure_le]
    intro x hx
    have hmem : rootGroup (classD T) x ∈ rootGroupsIn T := hΔ ▸ ⟨x, hx, rfl⟩
    exact hmem.2 (Subgroup.subset_closure (mem_rootSet_self hx))
  ·
    have hconj : ∀ E : Subgroup K, E ∈ ARS.conjSet (rootGroupsIn T) g ↔
        E ∈ rootClass (classD T) ∧ E ≤ conjSubgroup g T := by
      intro E
      rw [ARS.mem_conjSet]
      constructor
      · rintro ⟨hE, hle⟩
        refine ⟨?_, (conjSub_inv_le_iff E T g).1 hle⟩
        have := hR.conjSub_mem hE g
        rwa [← ARS.conjSub_mul, mul_inv_cancel, ARS.conjSub_one] at this
      · rintro ⟨hE, hle⟩
        exact ⟨hR.conjSub_mem hE g⁻¹, (conjSub_inv_le_iff E T g).2 hle⟩
    by_cases hg : conjSubgroup g T = T
    · right
      refine Set.inter_eq_left.2 fun E hE => (hconj E).2 ⟨hE.1, ?_⟩
      rw [hg]
      exact hE.2
    · left
      refine Set.eq_empty_of_forall_notMem fun E hE => ?_
      obtain ⟨hE1, hE2⟩ := hE
      have hle : E ≤ T ⊓ conjSubgroup g T := le_inf hE1.2 ((hconj E).1 hE2).2
      rw [hyp.1.inf_conj_eq_bot hg, le_bot_iff] at hle
      exact hR.ne_bot E hE1.1 hle

end TI

end CFSG.CGT.T75E
