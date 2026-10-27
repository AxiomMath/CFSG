module

public import CFSG.CGT.Timmesfeld75.Sec5FiveComm

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

section Seven

variable [Finite G]

theorem commutator_mem_of_central (h1 : Sec4NoA) (h3 : Sec4Nine) (hy : StepHyp T T₁)
    (hS : Sec3Global T) (hI : Sec3IsoGlobal T) (hT4 : 4 < Nat.card T) {h : G}
    (hh : IsUIdx T T₁ h) {b a : G} (hb : b ∈ conjSubgroup h (secA T T₁)) (hb1 : b ≠ 1)
    (haN : a ∈ Subgroup.normalizer (T : Set G)) (hcP : ⁅b, a⁆ ∈ hSubU T T₁)
    (hcT : ∀ t ∈ T, ⁅b, a⁆ * t = t * ⁅b, a⁆) : ⁅b, a⁆ ∈ T := by
  have hP := hy.pair
  have hbN : b ∈ Subgroup.normalizer (T : Set G) := hh.conj_secA_le_normalizer hP hS hb
  have hcN : ⁅b, a⁆ ∈ Subgroup.normalizer (T : Set G) := by
    have := (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem hbN haN)
        ((Subgroup.normalizer (T : Set G)).inv_mem hbN))
      ((Subgroup.normalizer (T : Set G)).inv_mem haN)
    simpa [commutatorElement_def] using this
  have hcen := h3 G T T₁ hy hS hI hT4 ⁅b, a⁆ hcP hcT
  have hWC : IsWC (barSub T (normIn (conjSubgroup h T) T)) :=
    sec48_of_noA h1 G T (conjSubgroup h T) (hh.stepHyp hy hS) hS hI
  have hbL : b ∈ normIn (conjSubgroup h T) T := hh.conj_secA_le hP hS hb
  have hTb : b ∉ T := fun hbT => hb1 (by
    have : b ∈ T ⊓ conjSubgroup h T := ⟨hbT, (mem_normIn.1 hbL).1⟩
    rwa [hP.wc.inf_conj_eq_bot hh.1, Subgroup.mem_bot] at this)
  have hbarmem : barElt T hcN ∈ barSub T (normIn (conjSubgroup h T) T) := by
    rw [barElt_commutator hbN haN hcN]
    refine hWC.commutator_mem_of_commute (barElt_mem_barSub hbN hbL)
      (fun h' => hTb ((barElt_eq_one_iff hbN).1 h')) fun x hx => ?_
    obtain ⟨u, huN, huL, rfl⟩ := exists_eq_barElt_of_mem_barSub hx
    have := bar_comm_of_commutator_mem hcN huN (hcen u (le_hSubU_of_isUIdx hh huL))
    rw [barElt_commutator hbN haN hcN] at this
    exact this.symm
  obtain ⟨u, huN, huL, hus⟩ := (barElt_mem_barSub_iff hcN).1 hbarmem
  obtain ⟨s, hsdef⟩ : ∃ s, s = u⁻¹ * ⁅b, a⁆ := ⟨_, rfl⟩
  rw [← hsdef] at hus
  have hcs : ⁅b, a⁆ = u * s := by rw [hsdef]; group
  have huT : ∀ t ∈ T, u * t = t * u := by
    intro t ht
    have hu' : u = ⁅b, a⁆ * s⁻¹ := by rw [hsdef]; group
    calc u * t = ⁅b, a⁆ * (s⁻¹ * t) := by rw [hu', mul_assoc]
      _ = ⁅b, a⁆ * (t * s⁻¹) := by rw [elemAbelian_mul_comm hP.wc.1 (T.inv_mem hus) ht]
      _ = (⁅b, a⁆ * t) * s⁻¹ := by rw [mul_assoc]
      _ = (t * ⁅b, a⁆) * s⁻¹ := by rw [hcT t ht]
      _ = t * (⁅b, a⁆ * s⁻¹) := by rw [mul_assoc]
      _ = t * u := by rw [hu']
  by_cases hu1 : u = 1
  · rw [hcs, hu1, one_mul]
    exact hus
  · exfalso
    have hcfg := (hh.sec3 hP hS).cfg
    have hTC : T ≤ Subgroup.centralizer ({u} : Set G) := fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.2 (huT t ht).symm
    have heq := hcfg.inf_centralizer_eq_normIn huL hu1
    rw [inf_eq_left.2 hTC] at heq
    have hlt := hcfg.normIn_lt (⟨h, rfl⟩ : ∃ x : G, conjSubgroup h T = conjSubgroup x T)
    rw [← heq] at hlt
    exact lt_irrefl _ hlt

theorem commutator_conj_secA_conj_secA_mem_of_ne (h1 : Sec4NoA) (h3 : Sec4Nine)
    (hy : StepHyp T T₁) (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    (hA4 : secA T T₁ ≠ normIn T T₁) {g h : G} (hh : IsUIdx T T₁ h)
    (hg : conjSubgroup g (secA T T₁) ≤ Subgroup.normalizer (T : Set G))
    (hgne : conjSubgroup g T ≠ T) :
    ∀ b ∈ conjSubgroup h (secA T T₁), ∀ a ∈ conjSubgroup g (secA T T₁), ⁅b, a⁆ ∈ T := by
  intro b hb a ha
  have hP := hy.pair
  by_cases hb1 : b = 1
  · rw [hb1]
    simp [T.one_mem]
  by_cases ha1 : a = 1
  · rw [ha1]
    simp [T.one_mem]
  have hA1 : secA T T₁ ≠ ⊥ := fun h' => hb1 (by
    rw [h', conjSubgroup_bot, Subgroup.mem_bot] at hb
    exact hb)
  have hT4 : 4 < Nat.card T := by
    have hsec := hP.sec3 hS
    have hAL : secA T T₁ < normIn T T₁ := lt_of_le_of_ne secA_le_normIn hA4
    have hLT : normIn T T₁ < T := hsec.cfg.normIn_lt hP.conj
    have hc1 := Subgroup.card_lt_of_lt hAL
    have hc2 := Subgroup.card_lt_of_lt hLT
    have hA2 : 1 < Nat.card (secA T T₁) := (Subgroup.one_lt_card_iff_ne_bot _).2 hA1
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (normIn_le T T₁)
    have hpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
    rcases k with _ | _ | k
    · omega
    · omega
    · rw [hk]
      nlinarith
  have haN : a ∈ Subgroup.normalizer (T : Set G) := hg ha
  have haT : a ∈ conjSubgroup g T := conjSubgroup_mono secA_le_left ha
  have hgL : normIn (conjSubgroup g T) T ≠ ⊥ := by
    intro hbot
    have : a ∈ normIn (conjSubgroup g T) T := mem_normIn.2 ⟨haT, haN⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact ha1 this
  have hbN : b ∈ Subgroup.normalizer (T : Set G) := hh.conj_secA_le_normalizer hP hS hb
  have hbL : b ∈ normIn (conjSubgroup h T) T := hh.conj_secA_le hP hS hb
  have hcT : ∀ t ∈ T, ⁅b, a⁆ * t = t * ⁅b, a⁆ := fun t ht => by
    have := commutator_conj_secA_le_centralizer_of_ne hP hS hI hh.1 (hh.normIn_conj_ne_bot hP)
      hgne hgL (Subgroup.commutator_mem_commutator hb ha)
    exact (Subgroup.mem_centralizer_iff.1 this t ht).symm
  have hcP : ⁅b, a⁆ ∈ hSubU T T₁ := by
    have hbP : b ∈ hSubU T T₁ := le_hSubU_of_isUIdx hh hbL
    have habP : a * b⁻¹ * a⁻¹ ∈ hSubU T T₁ := by
      have h4 : a * b⁻¹ * a⁻¹ ∈ conjSubgroup a (normIn (conjSubgroup h T) T) :=
        conj_mem_conjSubgroup a ((normIn (conjSubgroup h T) T).inv_mem hbL)
      have h5 : conjSubgroup a (normIn (conjSubgroup h T) T) =
          normIn (conjSubgroup (a * h) T) T := by
        have := normIn_conj a (conjSubgroup h T) T
        rw [mem_normalizer_iff_conjSubgroup_eq.1 haN, conjSubgroup_conjSubgroup] at this
        exact this.symm
      rw [h5] at h4
      exact le_hSubU_of_isUIdx (hh.mul_normalizer haN) h4
    have e : ⁅b, a⁆ = b * (a * b⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (hSubU T T₁).mul_mem hbP habP
  exact commutator_mem_of_central h1 h3 hy hS hI hT4 hh hb hb1 haN hcP hcT

omit [Finite G] in
theorem conj_normIn_le_of_commute (h1 : Sec4NoA) (hy : StepHyp T T₁) (hS : Sec3Global T)
    (hI : Sec3IsoGlobal T) {x : G} (hxN : x ∈ Subgroup.normalizer (T : Set G)) {a : G}
    (ha : a ∈ normIn T₁ T) (haT : a ∉ T) (hax : ⁅a, x⁆ ∈ T) :
    ∀ l ∈ normIn T₁ T, x * l * x⁻¹ ∈ normIn T₁ T ⊔ T := by
  have hV : IsWC (barSub T (normIn T₁ T)) := sec48_of_noA h1 G T T₁ hy hS hI
  have haN : a ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 ha).2
  have hcomm : barElt T haN * barElt T hxN = barElt T hxN * barElt T haN :=
    bar_comm_of_commutator_mem haN hxN hax
  have hā1 : barElt T haN ≠ 1 := fun h' => haT ((barElt_eq_one_iff haN).1 h')
  have hāV : barElt T haN ∈ barSub T (normIn T₁ T) := barElt_mem_barSub haN ha
  have hle : conjSubgroup (barElt T hxN) (barSub T (normIn T₁ T)) ≤
      Subgroup.centralizer ({barElt T haN} : Set (NQuot T)) := by
    intro y hy'
    rw [mem_conjSubgroup] at hy'
    have hv : (barElt T hxN)⁻¹ * y * barElt T hxN ∈ barSub T (normIn T₁ T) := hy'
    have hc1 : Commute (barElt T hxN) (barElt T haN) := hcomm.symm
    have hc2 : Commute ((barElt T hxN)⁻¹ * y * barElt T hxN) (barElt T haN) :=
      elemAbelian_mul_comm hV.1 hv hāV
    have e : y = barElt T hxN * ((barElt T hxN)⁻¹ * y * barElt T hxN) * (barElt T hxN)⁻¹ := by
      group
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [e]
    exact (hc1.mul_left hc2).mul_left hc1.inv_left
  have heq := (hV.2 _ hāV hā1).2 _ hle
  rw [conjSubgroup_barSub hxN] at heq
  intro l hl
  have hlN : l ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hl).2
  have hyN : x * l * x⁻¹ ∈ Subgroup.normalizer (T : Set G) := by
    have := (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem hxN hlN)
      ((Subgroup.normalizer (T : Set G)).inv_mem hxN)
    exact this
  have hmem : barElt T hyN ∈ barSub T (conjSubgroup x (normIn T₁ T)) :=
    barElt_mem_barSub hyN (conj_mem_conjSubgroup x hl)
  rw [heq] at hmem
  obtain ⟨u, huN, huL, hu⟩ := (barElt_mem_barSub_iff hyN).1 hmem
  have e : x * l * x⁻¹ = u * (u⁻¹ * (x * l * x⁻¹)) := by group
  rw [e]
  exact (normIn T₁ T ⊔ T).mul_mem (Subgroup.mem_sup_left huL) (Subgroup.mem_sup_right hu)

end Seven

end CFSG.CGT.Timmesfeld75
