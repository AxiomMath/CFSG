module

public import CFSG.LieType.SeitzGeneration.OrthNonsplitCore
public import CFSG.LieType.SeitzGeneration.OrthDfourBig

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.Open OrthBlk OrthNS
open CFSG.RankThree.Classical2 (orthDerived)

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

section Generator

omit [Finite K] in
theorem extU_mem_hyperClosure {U : Submodule K V} (hU : PolarNondegOn Q U)
    (hEU : orthDerived (Q.comp U.subtype) = elementaryGroup (Q.comp U.subtype)) (hp : p.Prime)
    {E : Subgroup (elementaryGroup Q)} (hEab : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3)
    {a X : elementaryGroup Q} (haE : a ∈ E) (hXE : X ∈ E) (ha1 : a ≠ 1)
    (haU : ∀ u ∈ U, (a : V ≃ₗ[K] V) u = u) (hXst : (X : V ≃ₗ[K] V) ∈ stab U)
    {x : orthDerived (Q.comp U.subtype)} (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hXx : res U ⟨(X : V ≃ₗ[K] V), hXst⟩ = (x : U ≃ₗ[K] U))
    {h : orthDerived (Q.comp U.subtype)} (hhx : h * x = x * h) :
    extU hU (h : U ≃ₗ[K] U) ∈ (hyperClosure p ⊤ E).map (elementaryGroup Q).subtype := by
  have : Fact p.Prime := ⟨hp⟩
  set h' := extU hU (h : U ≃ₗ[K] U) with hh'def
  have hh'Ei : h' ∈ eichlerGroupOn Q U := extU_mem_eichlerGroupOn hU (hEU ▸ h.2)
  have hh'E : h' ∈ elementaryGroup Q := eichlerGroupOn_le_elementaryGroup U hh'Ei
  have hast : (a : V ≃ₗ[K] V) ∈ stab U := mem_stab.mpr fun u hu =>
    ⟨by rw [haU u hu]; exact hu,
      by rw [(LinearEquiv.symm_apply_eq _).mpr (haU u hu).symm]; exact hu⟩
  have hXu : ∀ u (hu : u ∈ U), (X : V ≃ₗ[K] V) u = ((x : U ≃ₗ[K] U) ⟨u, hu⟩ : V) := fun u hu => by
    rw [← hXx]
    rfl
  have c1 : Commute h' (a : V ≃ₗ[K] V) := commute_of_mem_eichlerGroupOn hU hh'Ei
    (elementaryGroup_le_orthogonalGroup Q a.2) hast fun u hu => by
      rw [haU u hu, haU _ (eichlerGroupOn_apply_mem hh'Ei hu).1]
  have c2 : Commute h' (X : V ≃ₗ[K] V) := commute_of_mem_eichlerGroupOn hU hh'Ei
    (elementaryGroup_le_orthogonalGroup Q X.2) hXst fun u hu => by
      have hXuU : (X : V ≃ₗ[K] V) u ∈ U := ((mem_stab.mp hXst) u hu).1
      rw [hh'def, extU_apply_mem hU _ hXuU, extU_apply_mem hU _ hu,
        hXu _ ((h : U ≃ₗ[K] U) ⟨u, hu⟩).2]
      have e1 : (⟨(X : V ≃ₗ[K] V) u, hXuU⟩ : U) = (x : U ≃ₗ[K] U) ⟨u, hu⟩ :=
        Subtype.ext (hXu u hu)
      rw [e1]
      exact congrArg (fun y : orthDerived (Q.comp U.subtype) =>
        (((y : U ≃ₗ[K] U) ⟨u, hu⟩ : U) : V)) hhx
  have hind : ∀ s t : ℤ, a ^ s * X ^ t = 1 → (p : ℤ) ∣ s ∧ (p : ℤ) ∣ t := by
    intro s t hst'
    have hst : (a : V ≃ₗ[K] V) ^ s * (X : V ≃ₗ[K] V) ^ t = 1 := by
      have := congrArg Subtype.val hst'
      rwa [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow] at this
    have hxt : x ^ t = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_zpow, ← hXx, ← map_zpow]
      refine LinearEquiv.ext fun u => Subtype.ext ?_
      have hmem : ((X : V ≃ₗ[K] V) ^ t) u ∈ U := ((mem_stab.mp (zpow_mem hXst t)) u u.2).1
      have h1 := DFunLike.congr_fun hst (u : V)
      rw [LinearEquiv.mul_apply, zpow_apply_of_fixed (haU _ hmem)] at h1
      exact h1
    have ht : (p : ℤ) ∣ t := by
      rw [← orderOf_eq_prime hxp hx1]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hxt
    have hXt1 : X ^ t = 1 := by
      obtain ⟨m, rfl⟩ := ht
      rw [zpow_mul, zpow_natCast, hEab.2 X hXE, one_zpow]
    rw [hXt1, mul_one] at hst'
    refine ⟨?_, ht⟩
    rw [← orderOf_eq_prime (hEab.2 _ haE) ha1]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hst'
  have hcomm : Commute a X := congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, haE⟩ ⟨X, hXE⟩)
  have hk : (⟨h', hh'E⟩ : elementaryGroup Q) ∈ hyperClosure p ⊤ E :=
    mem_hyperClosure_of_commute hp hEcard haE hXE hcomm (hEab.2 _ haE) (hEab.2 _ hXE) hind
      (Subtype.ext c1.eq) (Subtype.ext c2.eq)
  exact ⟨⟨h', hh'E⟩, hk, rfl⟩

end Generator

namespace BlockTriple

variable {S : Fin 3 → Submodule K V} {g : Fin 3 → V ≃ₗ[K] V}

theorem exists_restrictedPlane (hB : BlockTriple Q p S g) (hQ : (polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hpKd : ¬ p ∣ Nat.card K)
    (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ P : Subgroup (orthDerived (Q.comp (fixIn (g i) ⊤).subtype)),
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ (∀ x ∈ P, x ^ p = 1) ∧ Nat.card P = p ^ 2 ∧
        ∀ x ∈ P, ∃ (a b : ℤ) (hst : g j ^ a * g k ^ b ∈ stab (fixIn (g i) ⊤)),
          res (fixIn (g i) ⊤) ⟨g j ^ a * g k ^ b, hst⟩ =
            (x : fixIn (g i) ⊤ ≃ₗ[K] fixIn (g i) ⊤) := by
  classical
  set U := fixIn (g i) ⊤ with hUdef
  have hU := hB.reg_fixIn hQ hpK i
  have hQU := nondegenerate_comp_subtype hU
  have hTU := exists_ts_three_comp hU (hB.eight_le_fixIn hQ hp hp2 hpq hpKd hpK hij hik hjk)
  have hst : ∀ l, g l ∈ stab U := fun l => stab_fixIn_of_commute (hB.commute i l)
  let T : Fin 3 → stab U := fun l => ⟨g l, hst l⟩
  have hTp : ∀ l, T l ^ p = 1 := fun l => Subtype.ext (hB.block l).pow
  have hRO : ∀ l, res U (T l) ∈ orthDerived (Q.comp U.subtype) := fun l =>
    mem_orthDerived_of_odd_pow hQU hTU (hp.odd_of_ne_two hp2)
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun u => by
        change Q (g l (u : V)) = Q (u : V)
        exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hB.block l).mem u)
      (by rw [← map_pow, hTp l, map_one])
  let R : Fin 3 → orthDerived (Q.comp U.subtype) := fun l => ⟨res U (T l), hRO l⟩
  have hRc : ∀ a b : ℤ, ((R j ^ a * R k ^ b : orthDerived (Q.comp U.subtype)) : U ≃ₗ[K] U) =
      res U (T j ^ a * T k ^ b) := fun a b => by
    rw [map_mul, map_zpow, map_zpow]
    rfl
  have hRp : ∀ l, R l ^ p = 1 := fun l => Subtype.ext (by
    change res U (T l) ^ p = 1
    rw [← map_pow, hTp l, map_one])
  have hcR : Commute (R j) (R k) :=
    Subtype.ext ((Commute.map (Subtype.ext (hB.commute j k).eq : Commute (T j) (T k))
      (res U)).eq)
  have hRind : ∀ a b : ℤ, R j ^ a * R k ^ b = 1 → (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b := by
    intro a b h
    have hfix : ∀ u (hu : u ∈ U), (g j ^ a * g k ^ b) u = u := fun u hu => by
      have h1 := congrArg (fun y : orthDerived (Q.comp U.subtype) =>
        (((y : U ≃ₗ[K] U) ⟨u, hu⟩ : U) : V)) h
      simp only [hRc] at h1
      exact h1
    have ha : (p : ℤ) ∣ a := hB.dvd_of_fix hp hpK j fun n hn => by
      have h1 := hfix n (hB.normKer_le_fixIn hpK hij
        (OrthBlk.mem_normKer.mpr ⟨Submodule.mem_top, hn⟩))
      rw [LinearEquiv.mul_apply, zpow_apply_of_fixed (hB.fix_of_ne hpK hjk.symm hn)] at h1
      exact h1
    refine ⟨ha, hB.dvd_of_fix hp hpK k fun n hn => ?_⟩
    have h1 := hfix n (hB.normKer_le_fixIn hpK hik
      (OrthBlk.mem_normKer.mpr ⟨Submodule.mem_top, hn⟩))
    rw [hB.zpow_eq_one_of_dvd j ha, one_mul] at h1
    exact h1
  obtain ⟨P, hPc, hPp, hPcard, hPform⟩ := exists_plane_of_two hp hcR (hRp j) (hRp k) hRind
  refine ⟨P, hPc, hPp, hPcard, fun x hx => ?_⟩
  obtain ⟨a, b, rfl⟩ := hPform x hx
  exact ⟨a, b, (T j ^ a * T k ^ b).2, (hRc a b).symm⟩

theorem extU_mem_of_rankLE2 (hB : BlockTriple Q p S g) (hQ : (polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hpKd : ¬ p ∣ Nat.card K)
    (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) {G : Fin 3 → elementaryGroup Q}
    (hG : ∀ i, (G i : V ≃ₗ[K] V) = g i) {E : Subgroup (elementaryGroup Q)}
    (hEab : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3) (hGE : ∀ i, G i ∈ E)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hrank : RankLE2 p (orthDerived (Q.comp (fixIn (g i) ⊤).subtype))) :
    ∀ y ∈ orthDerived (Q.comp (fixIn (g i) ⊤).subtype), extU (hB.reg_fixIn hQ hpK i) y ∈
      (hyperClosure p ⊤ E).map (elementaryGroup Q).subtype := by
  classical
  set U := fixIn (g i) ⊤ with hUdef
  have hU := hB.reg_fixIn hQ hpK i
  have hQU := nondegenerate_comp_subtype hU
  have hTU := exists_ts_three_comp hU (hB.eight_le_fixIn hQ hp hp2 hpq hpKd hpK hij hik hjk)
  have hEU := (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQU hTU).1
  have hpl : p ≠ ringChar K := fun h => hpK (by rw [h]; exact ringChar.Nat.cast_ringChar)
  obtain ⟨P, hPc, hPp, hPcard, hPform⟩ :=
    hB.exists_restrictedPlane hQ hp hp2 hpK hpKd hpq hij hik hjk
  have hgen := orthLowGen_of_residual orthSelfDualTwoBlocks hQU hTU
    (by have := hB.eight_le_fixIn hQ hp hp2 hpq hpKd hpK hij hik hjk; omega) hp hp2 hpl hrank
    P hPc hPp hPcard
  have hGi1 : G i ≠ 1 := fun h1 => (hB.block i).ne (by rw [← hG i, h1]; rfl)
  have hle : Subgroup.closure {h : orthDerived (Q.comp U.subtype) | ∃ x ∈ P, x ≠ 1 ∧
      h * x = x * h} ≤ ((hyperClosure p ⊤ E).map (elementaryGroup Q).subtype).comap
        ((extU hU).comp (orthDerived (Q.comp U.subtype)).subtype) := by
    rw [Subgroup.closure_le]
    rintro h ⟨x, hxP, hx1, hhx⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply, Subgroup.coe_subtype]
    obtain ⟨a, b, hst, hres⟩ := hPform x hxP
    have hXc : ((G j ^ a * G k ^ b : elementaryGroup Q) : V ≃ₗ[K] V) = g j ^ a * g k ^ b := by
      rw [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow, hG, hG]
    have hXst : ((G j ^ a * G k ^ b : elementaryGroup Q) : V ≃ₗ[K] V) ∈ stab U := hXc ▸ hst
    exact extU_mem_hyperClosure hU hEU hp hEab hEcard (hGE i)
      (E.mul_mem (E.zpow_mem (hGE j) a) (E.zpow_mem (hGE k) b)) hGi1
      (fun u hu => by rw [hG i]; exact (mem_fixIn.mp hu).2) hXst hx1 (hPp x hxP)
      (by rw [← hres]; congr 1; exact Subtype.ext hXc) hhx
  intro y hy
  have hmem : (⟨y, hy⟩ : orthDerived (Q.comp U.subtype)) ∈ Subgroup.closure
      {h : orthDerived (Q.comp U.subtype) | ∃ x ∈ P, x ≠ 1 ∧ h * x = x * h} := by
    rw [hgen]
    exact Subgroup.mem_top _
  have := Subgroup.mem_comap.mp (hle hmem)
  rwa [MonoidHom.comp_apply, Subgroup.coe_subtype] at this

theorem eichler_mem_of_rankLE2 (hB : BlockTriple Q p S g) (hQ : (polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hpKd : ¬ p ∣ Nat.card K)
    (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) {G : Fin 3 → elementaryGroup Q}
    (hG : ∀ i, (G i : V ≃ₗ[K] V) = g i) {E : Subgroup (elementaryGroup Q)}
    (hEab : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3) (hGE : ∀ i, G i ∈ E)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hrank : RankLE2 p (orthDerived (Q.comp (fixIn (g i) ⊤).subtype))) :
    ∀ e ∈ fixIn (g i) ⊤, ∀ w ∈ fixIn (g i) ⊤,
      eichler Q e w ∈ (hyperClosure p ⊤ E).map (elementaryGroup Q).subtype := by
  intro e he w hw
  have hU := hB.reg_fixIn hQ hpK i
  have hTU := exists_ts_three_comp hU (hB.eight_le_fixIn hQ hp hp2 hpq hpKd hpK hij hik hjk)
  have hEU := (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure
    (nondegenerate_comp_subtype hU) hTU).1
  have hmem : eichler (Q.comp (fixIn (g i) ⊤).subtype) ⟨e, he⟩ ⟨w, hw⟩ ∈
      orthDerived (Q.comp (fixIn (g i) ⊤).subtype) := by
    rw [hEU]
    exact eichler_mem_elementaryGroup _ _ _
  have := hB.extU_mem_of_rankLE2 hQ hp hp2 hpK hpKd hpq hG hEab hEcard hGE hij hik hjk hrank _
    hmem
  rwa [extU_eichler] at this

theorem hyperClosure_eq_top_of_rankLE2 (hB : BlockTriple Q p S g)
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hpKd : ¬ p ∣ Nat.card K) (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) {G : Fin 3 → elementaryGroup Q}
    (hG : ∀ i, (G i : V ≃ₗ[K] V) = g i) {E : Subgroup (elementaryGroup Q)}
    (hEab : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3) (hGE : ∀ i, G i ∈ E)
    (h0 : RankLE2 p (orthDerived (Q.comp (fixIn (g 0) ⊤).subtype)))
    (h1 : RankLE2 p (orthDerived (Q.comp (fixIn (g 1) ⊤).subtype))) :
    hyperClosure p ⊤ E = ⊤ := by
  set H := (hyperClosure p ⊤ E).map (elementaryGroup Q).subtype with hHdef
  have e0 := hB.eichler_mem_of_rankLE2 hQ hp hp2 hpK hpKd hpq hG hEab hEcard hGE
    (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide) h0
  have e1 := hB.eichler_mem_of_rankLE2 hQ hp hp2 hpK hpKd hpq hG hEab hEcard hGE
    (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide) h1
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨x, -, rfl⟩
    exact elementaryGroup_le_orthogonalGroup Q x.2
  have hroot : ∀ u, g 0 u = u → g 1 u = u → u ≠ 0 → Q u = 0 → IsRootCenter Q H u := by
    intro u hu0 hu1 hu hQu
    refine ⟨hu, hQu, fun w hw => ?_⟩
    obtain ⟨c, hc, b, hb, rfl⟩ := exists_add_fixIn_normKer (hB.block 0).pow hpK (S := ⊤)
      (fun _ _ => Submodule.mem_top) (Submodule.mem_top (x := w))
    have hub : polar Q u b = 0 :=
      polar_fixIn_normKer (hB.block 0).mem hpK hu0 (OrthBlk.mem_normKer.mp hb).2
    have huc : polar Q u c = 0 := by
      rw [polar_add_right, hub, add_zero] at hw
      exact hw
    rw [← eichler_mul huc hub]
    exact H.mul_mem (e0 u (mem_fixIn.mpr ⟨Submodule.mem_top, hu0⟩) c hc)
      (e1 u (mem_fixIn.mpr ⟨Submodule.mem_top, hu1⟩) b
        (hB.normKer_le_fixIn hpK (by decide : (1 : Fin 3) ≠ 0) hb))
  obtain ⟨P, hPe, hPf⟩ := exists_hypPair_in (hB.reg_normKer hQ hpK 2)
    (by have := hB.four_le_normKer hQ hp hp2 hpq hpKd hpK 2; omega)
  have hf0 : ∀ v ∈ OrthBlk.normKer (g 2) p ⊤, g 0 v = v := fun v hv =>
    hB.fix_of_ne hpK (by decide) (OrthBlk.mem_normKer.mp hv).2
  have hf1 : ∀ v ∈ OrthBlk.normKer (g 2) p ⊤, g 1 v = v := fun v hv =>
    hB.fix_of_ne hpK (by decide) (OrthBlk.mem_normKer.mp hv).2
  have hle := elementaryGroup_le_of_hypPair hQ hHO P
    (hroot P.e (hf0 _ hPe) (hf1 _ hPe) P.e_ne_zero P.Q_e)
    (hroot P.f (hf0 _ hPf) (hf1 _ hPf) P.f_ne_zero P.Q_f)
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [show x = y from Subtype.ext hyx.symm]

end BlockTriple

theorem exists_hyperGen_nonsplit {d : TauCeti.ValidLieTypeIndex}
    {π : elementaryGroup Q →* Cat d} (hc : IsOrthogonalCover Q π)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : orthDerived Q = elementaryGroup Q) (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hpKd : ¬ p ∣ Nat.card K) (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) {F : Subgroup (V ≃ₗ[K] V)}
    (hF : ElemAbOrth Q p F) (hFcard : p ^ 3 ≤ Nat.card F) :
    ∃ E' : Subgroup (Cat d), IsElemAbelian p E' ∧ Nat.card E' = p ^ 3 ∧
      HyperGen p (⊤ : Subgroup (Cat d)) E' := by
  have hQ := hc.nondegenerate
  have : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨L, hL, hlen⟩ := exists_blockFamily_top hQ hp hpK hF
  have hL3 : 3 ≤ L.length := by
    by_contra h
    push Not at h
    have : p ^ L.length ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (by omega)
    have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  obtain ⟨S, g, hB⟩ := exists_blockTriple hL hL3
  obtain ⟨G, E, hG, hEab, hEcard, hGE⟩ := hB.exists_cube hQ hT hE hp hp2 hpK
  have hcase : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      ¬ RankLE2 p (orthDerived (Q.comp (fixIn (g i) ⊤).subtype)) →
      ∃ E' : Subgroup (Cat d), IsElemAbelian p E' ∧ Nat.card E' = p ^ 3 ∧
        HyperGen p (⊤ : Subgroup (Cat d)) E' := by
    intro i j k hij hik hjk hr
    have hU := hB.reg_fixIn hQ hpK i
    have hTU := exists_ts_three_comp hU (hB.eight_le_fixIn hQ hp hp2 hpq hpKd hpK hij hik hjk)
    refine exists_hyperGen_of_not_rankLE2 hc hp hp2 hpK hU ?_
      (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure (nondegenerate_comp_subtype hU)
        hTU).1 hr
    have hle : OrthBlk.normKer (g i) p ⊤ ≤ perp Q (fixIn (g i) ⊤) := fun n hn =>
      mem_perp.mpr fun s hs => polar_fixIn_normKer (hB.block i).mem hpK (mem_fixIn.mp hs).2
        (OrthBlk.mem_normKer.mp hn).2
    have := Submodule.finrank_mono hle
    have := hB.four_le_normKer hQ hp hp2 hpq hpKd hpK i
    omega
  by_cases h0 : RankLE2 p (orthDerived (Q.comp (fixIn (g 0) ⊤).subtype))
  · by_cases h1 : RankLE2 p (orthDerived (Q.comp (fixIn (g 1) ⊤).subtype))
    · exact exists_hyperGen_of_hyperClosure_eq_top hc.surjective hp
        (not_dvd_card_ker_of_scalar hc hp hp2) hEab hEcard
        (hB.hyperClosure_eq_top_of_rankLE2 hQ hp hp2 hpK hpKd hpq hG hEab hEcard hGE h0 h1)
    · exact hcase 1 0 2 (by decide) (by decide) (by decide) h1
  · exact hcase 0 1 2 (by decide) (by decide) (by decide) h0

end CFSG.LieType.SeitzGeneration
