module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK3Aux4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fa8fin_invDim_blockHom {t : OGroup Q} (htt : t * t = 1)
    {a : OGroup (Q.restrict (fixSp t))} (haa : a * a = 1)
    {b : OGroup (Q.restrict (commSp t))} (hbb : b * b = 1) :
    invDim (blockHom htt (a, b)) = invDim a + invDim b := by
  have hX : (commSp a).map (fixSp t).subtype ≤ fixSp t :=
    Submodule.map_subtype_le (fixSp t) (commSp a)
  have hY : (commSp b).map (commSp t).subtype ≤ commSp t :=
    Submodule.map_subtype_le (commSp t) (commSp b)
  have hdisj : Disjoint ((commSp a).map (fixSp t).subtype)
      ((commSp b).map (commSp t).subtype) :=
    Disjoint.mono hX hY (isCompl_fixSp_commSp htt).disjoint
  have hinf : ((commSp a).map (fixSp t).subtype) ⊓
      ((commSp b).map (commSp t).subtype) = ⊥ := disjoint_iff.mp hdisj
  have hfr := Submodule.finrank_sup_add_finrank_inf_eq
    ((commSp a).map (fixSp t).subtype) ((commSp b).map (commSp t).subtype)
  rw [hinf, finrank_bot, add_zero] at hfr
  simp only [invDim]
  rw [commSp_blockHom htt haa hbb, hfr, Submodule.finrank_map_subtype_eq,
    Submodule.finrank_map_subtype_eq]

theorem fa8fin_refl_split (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    {t : OGroup Q} (htt : t * t = 1) (hts : t * s = s * t) (ht1 : invDim t = 1) :
    (∃ a : OGroup (Q.restrict (fixSp s)), t = blockHom hs (a, 1)) ∨
      invDim (t * s) = Module.finrank (ZMod 3) (commSp s) - 1 := by
  have htmem : t ∈ Subgroup.centralizer ({s} : Set (OGroup Q)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain rfl := Set.mem_singleton_iff.mp hh
    exact hts.symm
  have htmem' : t ∈ (blockHom hs).range := by
    rw [range_blockHom hQ hs]
    exact htmem
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp htmem'
  obtain ⟨a, b⟩ := p
  have hpp : (a, b) * (a, b) = 1 := by
    apply blockHom_injective hs
    rw [map_mul, hp, htt, map_one]
  have haa : a * a = 1 := congrArg Prod.fst hpp
  have hbb : b * b = 1 := congrArg Prod.snd hpp
  have hadd : invDim t = invDim a + invDim b := by
    rw [← hp]
    exact fa8fin_invDim_blockHom hs haa hbb
  have hsum : invDim a + invDim b = 1 := by rw [← hadd, ht1]
  by_cases hb0 : invDim b = 0
  ·
    exact Or.inl ⟨a, by rw [← hp, (invDim_eq_zero_iff hbb).mp hb0]⟩
  ·
    right
    have hb1 : invDim b = 1 := by omega
    have ha0 : invDim a = 0 := by omega
    have ha1 : a = 1 := (invDim_eq_zero_iff haa).mp ha0
    let π : OGroup (Q.restrict (commSp s)) := piOrth (Q.restrict (commSp s))
    have hπcomm : b * π = π * b :=
      Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q.restrict (commSp s))) b
    have hbπ_sq : (b * π) * (b * π) = 1 := by
      rw [hπcomm]
      exact piOrth_mul_mul_self hbb
    have hmul : t * s = blockHom hs (1, b * π) := by
      have ht_eq : t = blockHom hs (1, b) := by rw [← hp, ha1]
      have h1 : t * blockHom hs (1, π) = blockHom hs (1, b * π) := by
        rw [ht_eq, ← map_mul, Prod.mk_mul_mk, one_mul]
      have h2 : t * blockHom hs (1, π) = t * s := by rw [blockHom_one_piOrth hs]
      exact h2.symm.trans h1
    have hfin : invDim (t * s) =
        invDim (1 : OGroup (Q.restrict (fixSp s))) + invDim (b * π) := by
      rw [hmul]
      exact fa8fin_invDim_blockHom hs (a := 1) (by simp) hbπ_sq
    have hone : invDim (1 : OGroup (Q.restrict (fixSp s))) = 0 :=
      (invDim_eq_zero_iff (t := (1 : OGroup (Q.restrict (fixSp s)))) (by simp)).mpr rfl
    have hbπ : invDim (b * π) = Module.finrank (ZMod 3) (commSp s) - 1 := by
      have hpi := congrArg Prod.fst (invType_piOrth_mul
        (Q := Q.restrict (commSp s)) (nondegenerate_restrict_commSp hQ hs) hbb)
      rw [← hπcomm, hb1] at hpi
      exact hpi
    rw [hfin, hone, zero_add, hbπ]

end CFSG.OddStandard.SmallF3.Omega
