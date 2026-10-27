module

public import CFSG.CGT.Timmesfeld75.Sec5FiveEngHelp

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem conjSubgroup_normIn_conj {n h : G} (hn : n ∈ Subgroup.normalizer (T : Set G)) :
    conjSubgroup n (normIn (conjSubgroup h T) T) = normIn (conjSubgroup (n * h) T) T := by
  have hnT : conjSubgroup n T = T := mem_normalizer_iff_conjSubgroup_eq.1 hn
  have := normIn_conj n (conjSubgroup h T) T
  rw [hnT, conjSubgroup_conjSubgroup] at this
  exact this.symm

theorem inv_mul_conj_mem {x : G} (hxN : x ∈ Subgroup.normalizer (T : Set G)) (hxx : x * x = 1)
    (hT : IsElemAbelian 2 T) {t : G} (ht : t ∈ T) :
    t⁻¹ * (x * t * x⁻¹) ∈ T ⊓ Subgroup.centralizer ({x} : Set G) := by
  have hu : x * t * x⁻¹ ∈ T := conj_mem_of_mem_normalizer hxN ht
  have hti : t⁻¹ = t := elemAbelian_inv hT ht
  refine ⟨T.mul_mem (T.inv_mem ht) hu, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  rw [hti]
  have hxut : x * (x * t * x⁻¹) * x⁻¹ = t := by
    calc x * (x * t * x⁻¹) * x⁻¹ = (x * x) * t * (x * x)⁻¹ := by group
      _ = t := by rw [hxx]; group
  have hcomm : x * (t * (x * t * x⁻¹)) * x⁻¹ = t * (x * t * x⁻¹) := by
    calc x * (t * (x * t * x⁻¹)) * x⁻¹ = (x * t * x⁻¹) * (x * (x * t * x⁻¹) * x⁻¹) := by group
      _ = (x * t * x⁻¹) * t := by rw [hxut]
      _ = t * (x * t * x⁻¹) := elemAbelian_mul_comm hT hu ht
  calc (t * (x * t * x⁻¹)) * x = (x * (t * (x * t * x⁻¹)) * x⁻¹) * x := by rw [hcomm]
    _ = x * (t * (x * t * x⁻¹)) := by group

theorem mul_comm_mul_iff {T : Subgroup G} (hT : IsElemAbelian 2 T) {t r : G} (ht : t ∈ T)
    (hr : r ∈ T) (u : G) : t * (u * r) = (u * r) * t ↔ t * u = u * t := by
  have h := elemAbelian_mul_comm hT ht hr
  constructor
  · intro h1
    have h2 : (t * u) * r = (u * t) * r := by
      calc (t * u) * r = t * (u * r) := by rw [mul_assoc]
        _ = (u * r) * t := h1
        _ = u * (r * t) := by rw [mul_assoc]
        _ = u * (t * r) := by rw [h]
        _ = (u * t) * r := by rw [mul_assoc]
    exact mul_right_cancel h2
  · intro h1
    calc t * (u * r) = (t * u) * r := by rw [mul_assoc]
      _ = (u * t) * r := by rw [h1]
      _ = u * (t * r) := by rw [mul_assoc]
      _ = u * (r * t) := by rw [h]
      _ = (u * r) * t := by rw [mul_assoc]

section Eight

variable [Finite G]

theorem sec58_core (h1 : Sec4NoA) (hy : StepHyp T T₁) (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    {h : G} (hh : IsUIdx T T₁ h)
    (hS₂ : IsPGroup 2 ↥(barSub T (normIn T₁ T) ⊔ barSub T (normIn (conjSubgroup h T) T))) :
    ∀ y ∈ normIn (conjSubgroup h T) T, ∀ x ∈ normIn T₁ T, ⁅y, x⁆ ∈ T := by
  intro y hy' x hx
  have hP := hy.pair
  have hcfg₁ : Cfg T T₁ := (hP.sec3 hS).cfg
  have hcfg₂ : Cfg T (conjSubgroup h T) := (hh.sec3 hP hS).cfg
  have hV₁ : IsWC (barSub T (normIn T₁ T)) := sec48_of_noA h1 G T T₁ hy hS hI
  have hV₂ : IsWC (barSub T (normIn (conjSubgroup h T) T)) :=
    sec48_of_noA h1 G T (conjSubgroup h T) (hh.stepHyp hy hS) hS hI
  by_cases hx1 : x = 1
  · rw [hx1]
    simp [T.one_mem]
  by_cases hy1 : y = 1
  · rw [hy1]
    simp [T.one_mem]
  have hxN : x ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hx).2
  have hyN : y ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hy').2
  have hxb : barElt T hxN ∈ barSub T (normIn T₁ T) := barElt_mem_barSub hxN hx
  have hyb : barElt T hyN ∈ barSub T (normIn (conjSubgroup h T) T) := barElt_mem_barSub hyN hy'
  have hN₁ : conjSubgroup (barElt T hyN) (barSub T (normIn T₁ T)) = barSub T (normIn T₁ T) :=
    eq_of_conj_le_pGroup hV₁ hS₂ le_sup_left
      (conjSubgroup_le_of_le_of_mem le_sup_left (Subgroup.mem_sup_right hyb))
  have hN₂ : conjSubgroup (barElt T hxN) (barSub T (normIn (conjSubgroup h T) T)) =
      barSub T (normIn (conjSubgroup h T) T) :=
    eq_of_conj_le_pGroup hV₂ hS₂ le_sup_right
      (conjSubgroup_le_of_le_of_mem le_sup_right (Subgroup.mem_sup_left hxb))
  have hcN : ⁅y, x⁆ ∈ Subgroup.normalizer (T : Set G) := by
    have := (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem hyN hxN)
        ((Subgroup.normalizer (T : Set G)).inv_mem hyN))
      ((Subgroup.normalizer (T : Set G)).inv_mem hxN)
    simpa [commutatorElement_def] using this
  have hcbar : barElt T hcN = ⁅barElt T hyN, barElt T hxN⁆ := barElt_commutator hyN hxN hcN
  have hcbV₁ : barElt T hcN ∈ barSub T (normIn T₁ T) := by
    have h2 : barElt T hyN * barElt T hxN * (barElt T hyN)⁻¹ ∈
        conjSubgroup (barElt T hyN) (barSub T (normIn T₁ T)) := conj_mem_conjSubgroup _ hxb
    rw [hN₁] at h2
    have h3 := (barSub T (normIn T₁ T)).mul_mem h2 ((barSub T (normIn T₁ T)).inv_mem hxb)
    rw [hcbar, commutatorElement_def]
    exact h3
  have hcbV₂ : barElt T hcN ∈ barSub T (normIn (conjSubgroup h T) T) := by
    have h2 : barElt T hxN * (barElt T hyN)⁻¹ * (barElt T hxN)⁻¹ ∈
        conjSubgroup (barElt T hxN) (barSub T (normIn (conjSubgroup h T) T)) :=
      conj_mem_conjSubgroup _ ((barSub T (normIn (conjSubgroup h T) T)).inv_mem hyb)
    rw [hN₂] at h2
    have h3 := (barSub T (normIn (conjSubgroup h T) T)).mul_mem hyb h2
    have e : barElt T hyN * (barElt T hxN * (barElt T hyN)⁻¹ * (barElt T hxN)⁻¹) =
        ⁅barElt T hyN, barElt T hxN⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hcbar, ← e]
    exact h3
  by_cases hc1 : barElt T hcN = 1
  · exact (barElt_eq_one_iff hcN).1 hc1
  exfalso
  obtain ⟨u, huN, huL, hus⟩ := (barElt_mem_barSub_iff hcN).1 hcbV₁
  obtain ⟨u', hu'N, hu'L, hu's⟩ := (barElt_mem_barSub_iff hcN).1 hcbV₂
  have hu1 : u ≠ 1 := fun h' => hc1 ((barElt_eq_one_iff hcN).2 (by
    rw [h', inv_one, one_mul] at hus
    exact hus))
  have hu'1 : u' ≠ 1 := fun h' => hc1 ((barElt_eq_one_iff hcN).2 (by
    rw [h', inv_one, one_mul] at hu's
    exact hu's))
  have hCu := hcfg₁.inf_centralizer_eq_normIn huL hu1
  have hCu' := hcfg₂.inf_centralizer_eq_normIn hu'L hu'1
  have hr : u⁻¹ * u' ∈ T := by
    have h2 := T.mul_mem hus (T.inv_mem hu's)
    have e : u⁻¹ * ⁅y, x⁆ * (u'⁻¹ * ⁅y, x⁆)⁻¹ = u⁻¹ * u' := by group
    rwa [e] at h2
  have hu'eq : u' = u * (u⁻¹ * u') := by group
  have hLL : normIn T T₁ = normIn T (conjSubgroup h T) := by
    rw [← hCu, ← hCu']
    ext t
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, hu'eq]
    constructor
    · rintro ⟨htT, ht⟩
      exact ⟨htT, (mul_comm_mul_iff hcfg₁.wc.1 htT hr u).2 ht⟩
    · rintro ⟨htT, ht⟩
      exact ⟨htT, (mul_comm_mul_iff hcfg₁.wc.1 htT hr u).1 ht⟩
  have hxx : x * x = 1 := elemAbelian_mul_self hcfg₁.wc₁.1 (normIn_le _ _ hx)
  have hyy : y * y = 1 :=
    elemAbelian_mul_self (isElemAbelian_conjSubgroup hcfg₁.wc.1 h) (normIn_le _ _ hy')
  have hxL := hcfg₁.inf_centralizer_eq_normIn hx hx1
  have hyL := hcfg₂.inf_centralizer_eq_normIn hy' hy1
  have hxfix : ∀ l ∈ normIn T T₁, x * l * x⁻¹ = l := fun l hl => by
    have hl' : l ∈ T ⊓ Subgroup.centralizer ({x} : Set G) := by rw [hxL]; exact hl
    have h2 := Subgroup.mem_centralizer_singleton_iff.1 hl'.2
    calc x * l * x⁻¹ = l * x * x⁻¹ := by rw [← h2]
      _ = l := by group
  have hyfix : ∀ l ∈ normIn T (conjSubgroup h T), y * l * y⁻¹ = l := fun l hl => by
    have hl' : l ∈ T ⊓ Subgroup.centralizer ({y} : Set G) := by rw [hyL]; exact hl
    have h2 := Subgroup.mem_centralizer_singleton_iff.1 hl'.2
    calc y * l * y⁻¹ = l * y * y⁻¹ := by rw [← h2]
      _ = l := by group
  have hE : ∀ t ∈ T, x * (y * t * y⁻¹) * x⁻¹ = y * (x * t * x⁻¹) * y⁻¹ := by
    intro t ht
    have hwx := inv_mul_conj_mem hxN hxx hcfg₁.wc.1 ht
    have hwy := inv_mul_conj_mem hyN hyy hcfg₁.wc.1 ht
    rw [hxL] at hwx
    rw [hyL] at hwy
    obtain ⟨wx, hwxdef⟩ : ∃ wx, wx = t⁻¹ * (x * t * x⁻¹) := ⟨_, rfl⟩
    obtain ⟨wy, hwydef⟩ : ∃ wy, wy = t⁻¹ * (y * t * y⁻¹) := ⟨_, rfl⟩
    rw [← hwxdef] at hwx
    rw [← hwydef] at hwy
    have hxt : x * t * x⁻¹ = t * wx := by rw [hwxdef]; group
    have hyt : y * t * y⁻¹ = t * wy := by rw [hwydef]; group
    have hwyL : wy ∈ normIn T T₁ := by rw [hLL]; exact hwy
    have hwxL' : wx ∈ normIn T (conjSubgroup h T) := by rw [← hLL]; exact hwx
    have hwxT : wx ∈ T := normIn_le _ _ hwx
    have hwyT : wy ∈ T := normIn_le _ _ hwy
    calc x * (y * t * y⁻¹) * x⁻¹ = x * (t * wy) * x⁻¹ := by rw [hyt]
      _ = (x * t * x⁻¹) * (x * wy * x⁻¹) := by group
      _ = (t * wx) * wy := by rw [hxt, hxfix wy hwyL]
      _ = t * (wy * wx) := by rw [mul_assoc, elemAbelian_mul_comm hcfg₁.wc.1 hwxT hwyT]
      _ = (t * wy) * wx := (mul_assoc t wy wx).symm
      _ = (y * t * y⁻¹) * wx := by rw [hyt]
      _ = (y * t * y⁻¹) * (y * wx * y⁻¹) := by rw [hyfix wx hwxL']
      _ = y * (t * wx) * y⁻¹ := by group
      _ = y * (x * t * x⁻¹) * y⁻¹ := by rw [hxt]
  have hcT : ∀ t ∈ T, ⁅y, x⁆ * t = t * ⁅y, x⁆ := by
    intro t ht
    have ht'' : y⁻¹ * (x⁻¹ * t * x) * y ∈ T := by
      have h2 : x⁻¹ * t * x ∈ T := by
        have := conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hxN) ht
        simpa using this
      have := conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hyN) h2
      simpa using this
    have h3 := hE _ ht''
    have e1 : x * (y * (y⁻¹ * (x⁻¹ * t * x) * y) * y⁻¹) * x⁻¹ = t := by group
    have e2 : y * (x * (y⁻¹ * (x⁻¹ * t * x) * y) * x⁻¹) * y⁻¹ = ⁅y, x⁆ * t * ⁅y, x⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e1, e2] at h3
    calc ⁅y, x⁆ * t = (⁅y, x⁆ * t * ⁅y, x⁆⁻¹) * ⁅y, x⁆ := by group
      _ = t * ⁅y, x⁆ := by rw [← h3]
  have huT : ∀ t ∈ T, u * t = t * u := by
    intro t ht
    have hs := hus
    obtain ⟨s, hsdef⟩ : ∃ s, s = u⁻¹ * ⁅y, x⁆ := ⟨_, rfl⟩
    rw [← hsdef] at hs
    have hu2 : u = ⁅y, x⁆ * s⁻¹ := by rw [hsdef]; group
    calc u * t = ⁅y, x⁆ * (s⁻¹ * t) := by rw [hu2, mul_assoc]
      _ = ⁅y, x⁆ * (t * s⁻¹) := by rw [elemAbelian_mul_comm hcfg₁.wc.1 (T.inv_mem hs) ht]
      _ = (⁅y, x⁆ * t) * s⁻¹ := by rw [mul_assoc]
      _ = (t * ⁅y, x⁆) * s⁻¹ := by rw [hcT t ht]
      _ = t * (⁅y, x⁆ * s⁻¹) := by rw [mul_assoc]
      _ = t * u := by rw [hu2]
  have hTC : T ≤ Subgroup.centralizer ({u} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.2 (huT t ht).symm
  rw [inf_eq_left.2 hTC] at hCu
  have hlt := hcfg₁.normIn_lt hP.conj
  rw [← hCu] at hlt
  exact lt_irrefl _ hlt

theorem sec58_le (h1 : Sec4NoA) (hy : StepHyp T T₁) (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    {h : G} (hh : IsUIdx T T₁ h)
    (hS₂ : IsPGroup 2 ↥(barSub T (normIn T₁ T) ⊔ barSub T (normIn (conjSubgroup h T) T))) :
    normIn (conjSubgroup h T) T ≤ T ⊔ normIn T₁ T := by
  intro y hy'
  by_cases hy1 : y = 1
  · rw [hy1]
    exact (T ⊔ normIn T₁ T).one_mem
  by_contra hyn
  have hyD : y ∈ normD T :=
    mem_normD_of_mem_conjSubgroup (normIn_le _ _ hy') hy1 (mem_normIn.1 hy').2
  exact h1 G T T₁ hy hS hI y hyD hyn fun l hl => sec58_core h1 hy hS hI hh hS₂ y hy' l hl

theorem sec58 (h1 : Sec4NoA) (hy : StepHyp T T₁) (hS : Sec3Global T) (hI : Sec3IsoGlobal T) :
    hSubU T T₁ = hSub T (normIn T₁ T) := by
  have hP := hy.pair
  obtain ⟨x₀, hx₀⟩ := hP.conj
  have hx₀u : IsUIdx T T₁ x₀ := isUIdx_of_conj hP hS hx₀
  have hcfg := (hP.sec3 hS).cfg
  have hL₁2 : IsPGroup 2 ↥(normIn T₁ T) :=
    (isPGroup_two_of_isElemAbelian hcfg.wc₁.1).to_le (normIn_le _ _)
  apply le_antisymm
  · refine sup_le le_sup_left (iSup₂_le fun h hh => ?_)
    have hL₂2 : IsPGroup 2 ↥(normIn (conjSubgroup h T) T) :=
      (isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup hcfg.wc.1 h)).to_le
        (normIn_le _ _)
    obtain ⟨S₁, hS₁⟩ := (isPGroup_barSub (T := T) hL₁2).exists_le_sylow
    obtain ⟨S₂, hS₂⟩ := (isPGroup_barSub (T := T) hL₂2).exists_le_sylow
    obtain ⟨g, hg⟩ := exists_conjSubgroup_eq_of_sylow S₂ S₁
    obtain ⟨n', rfl⟩ := QuotientGroup.mk_surjective g
    have hn : (n' : G) ∈ Subgroup.normalizer (T : Set G) := n'.2
    have hconj : conjSubgroup (barElt T hn) (barSub T (normIn (conjSubgroup h T) T)) ≤
        (S₁ : Subgroup (NQuot T)) := by
      rw [← hg]
      exact conjSubgroup_mono hS₂
    rw [conjSubgroup_barSub hn, conjSubgroup_normIn_conj hn] at hconj
    have hS₂' : IsPGroup 2 ↥(barSub T (normIn T₁ T) ⊔
        barSub T (normIn (conjSubgroup (n' * h) T) T)) :=
      S₁.isPGroup'.to_le (sup_le hS₁ hconj)
    have hle := sec58_le h1 hy hS hI (hh.mul_normalizer hn) hS₂'
    have hnT : conjSubgroup (n'⁻¹ : G) T = T :=
      mem_normalizer_iff_conjSubgroup_eq.1 ((Subgroup.normalizer (T : Set G)).inv_mem hn)
    have h5 : normIn (conjSubgroup h T) T =
        conjSubgroup (n'⁻¹ : G) (normIn (conjSubgroup (n' * h) T) T) := by
      rw [conjSubgroup_normIn_conj ((Subgroup.normalizer (T : Set G)).inv_mem hn)]
      congr 3
      group
    rw [h5]
    refine (conjSubgroup_mono hle).trans ?_
    rw [conjSubgroup_sup_eq_sup, hnT]
    exact sup_le_sup_left (le_iSup₂ (f := fun (g : G) (_ : g ∈ Subgroup.normalizer (T : Set G)) =>
      conjSubgroup g (normIn T₁ T)) (n'⁻¹ : G)
      ((Subgroup.normalizer (T : Set G)).inv_mem hn)) T
  · refine sup_le left_le_hSubU (iSup₂_le fun g hg => ?_)
    have h6 : conjSubgroup g (normIn T₁ T) = normIn (conjSubgroup (g * x₀) T) T := by
      rw [hx₀]
      exact conjSubgroup_normIn_conj hg
    rw [h6]
    exact le_hSubU_of_isUIdx (hx₀u.mul_normalizer hg)

end Eight

end CFSG.CGT.Timmesfeld75
