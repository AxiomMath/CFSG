module

public import CFSG.CGT.Timmesfeld75.Sec66Three
public import CFSG.CGT.Timmesfeld75.Sec6TwoSetup
public import CFSG.CGT.Timmesfeld75.Sec66Cfg

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G} {m : ℕ}

theorem Sec6Ctx.sec66_build (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ 3 m)
    {x y g : G} (hx : x ∈ T) (hx1 : x ≠ 1) (hyD : y ∈ classD T) (h4 : orderOf (x * y) = 4)
    (hyy : y * y = 1) (hT' : conjSubgroup y T ≠ T) (hg : g ∈ T ⊔ conjSubgroup y T)
    (hfix : conjSubgroup y (conjSubgroup g T) = conjSubgroup g T)
    (hyS : y ∉ conjSubgroup g T) :
    (x * y) ^ 2 ∈ classD T ∨ ∃ (Tb P : Subgroup G) (y' : G),
      Sec66Cfg (conjSubgroup g T) Tb P y y' (2 ^ m) ∧ (x * y) ^ 2 = y * y' := by
  have hwc : IsWC T := hc.hy.pair.wc
  have hxx : x * x = 1 := elemAbelian_mul_self hwc.1 hx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  obtain ⟨-, hcomm, hsq⟩ := sec66_yprime hxx hyy h4
  have hxm := sec66_x_comm hxx hyy h4
  have hm'T' : y * x * y⁻¹ ∈ conjSubgroup y T := conj_mem_conjSubgroup y hx
  have hm'1 : y * x * y⁻¹ ≠ 1 := fun h => hx1 (by
    calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group)
  have hxN' : x ∈ Subgroup.normalizer ((conjSubgroup y T : Subgroup G) : Set G) :=
    (hwc.conj y).centralizer_le_normalizer hm'T' hm'1
      (Subgroup.mem_centralizer_singleton_iff.2 hxm)
  have hxL : x ∈ normIn T (conjSubgroup y T) := mem_normIn.2 ⟨hx, hxN'⟩
  have hbot : normIn T (conjSubgroup y T) ≠ ⊥ := fun h =>
    hx1 (Subgroup.mem_bot.1 (h ▸ hxL))
  have hS3 : Sec3 T (conjSubgroup y T) := hc.hS y hT' hbot
  have hm'L : y * x * y⁻¹ ∈ normIn (conjSubgroup y T) T := conj_mem_normIn_swap hyy hxL
  have hwM : y * (x * y * x⁻¹) ∈ cfgM T (conjSubgroup y T) := by
    have h1 : (x * y) ^ 2 = x * (y * x * y⁻¹) := by rw [pow_two, hyi]; group
    rw [← hsq, h1]
    exact (cfgM T (conjSubgroup y T)).mul_mem (Cfg.normIn_le_cfgM_left _ _ hxL)
      (Cfg.normIn_le_cfgM_right _ _ hm'L)
  have hne1 : (x * y) ^ 2 ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by norm_num) (by rw [h4]; norm_num)
  have hw1 : y * (x * y * x⁻¹) ≠ 1 := by
    rw [← hsq]
    exact hne1
  obtain ⟨hCU, hB⟩ := hc.sec66_loc_card h62 h63 hyD hyy hS3 hg hfix hyS
  have hyN : y ∈ Subgroup.normalizer ((conjSubgroup g T : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSubgroup_eq.2 hfix
  have hxU : x ∈ Subgroup.normalizer ((conjSubgroup g T : Subgroup G) : Set G) :=
    hS3.cfgM_le_normalizer_conj hg (Cfg.normIn_le_cfgM_left _ _ hxL)
  obtain ⟨k, hk⟩ := exists_mem_conj_of_mem_classD hyD
  have hy1 : y ≠ 1 := ne_one_of_mem_classD hyD
  have hy'1 : x * y * x⁻¹ ≠ 1 := fun h => hy1 (by
    calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group)
  have hy'P : x * y * x⁻¹ ∈ conjSubgroup x (conjSubgroup k T) := conj_mem_conjSubgroup x hk
  have hy'U : x * y * x⁻¹ ∈ Subgroup.normalizer ((conjSubgroup g T : Subgroup G) : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hxU hyN)
      ((Subgroup.normalizer _).inv_mem hxU)
  by_cases hBP : conjSubgroup k T = conjSubgroup x (conjSubgroup k T)
  · left
    have hy'B : x * y * x⁻¹ ∈ conjSubgroup k T := hBP ▸ hy'P
    rw [hsq]
    exact mem_classD_of_mem_conjSubgroup ((conjSubgroup k T).mul_mem hk hy'B) hw1
  have hneUB : conjSubgroup g T ≠ conjSubgroup k T := fun h => hyS (h ▸ hk)
  have hneUP : conjSubgroup g T ≠ conjSubgroup x (conjSubgroup k T) := by
    intro h
    apply hyS
    have hy'U' : x * y * x⁻¹ ∈ conjSubgroup g T := h ▸ hy'P
    have h1 := conj_mem_of_mem_normalizer ((Subgroup.normalizer _).inv_mem hxU) hy'U'
    have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rwa [e] at h1
  have hUB : conjSubgroup g T ⊓ conjSubgroup k T = ⊥ :=
    inf_eq_bot_of_conj_conj hwc rfl rfl hneUB
  have hUP : conjSubgroup g T ⊓ conjSubgroup x (conjSubgroup k T) = ⊥ :=
    inf_eq_bot_of_conj_conj hwc (a := g) (b := x * k) rfl (conjSubgroup_conjSubgroup x k T) hneUP
  have hcUB : ∀ a ∈ normIn (conjSubgroup g T) (conjSubgroup k T), a * y = y * a := fun a ha =>
    comm_of_inf_eq_bot hUB (normIn_le _ _ ha) hk (mem_normIn.1 ha).2 hyN
  have hcUP : ∀ a ∈ normIn (conjSubgroup g T) (conjSubgroup x (conjSubgroup k T)),
      a * (x * y * x⁻¹) = (x * y * x⁻¹) * a := fun a ha =>
    comm_of_inf_eq_bot hUP (normIn_le _ _ ha) hy'P (mem_normIn.1 ha).2 hy'U
  by_cases hAM : normIn (conjSubgroup g T) (conjSubgroup k T) ⊓
      normIn (conjSubgroup g T) (conjSubgroup x (conjSubgroup k T)) ≤ cfgM T (conjSubgroup y T)
  · right
    have hNB : Nat.card ↥(normIn (conjSubgroup g T) (conjSubgroup k T)) = (2 ^ m) ^ 2 := by
      apply le_antisymm
      · calc Nat.card ↥(normIn (conjSubgroup g T) (conjSubgroup k T))
            ≤ Nat.card ↥(normIn T T₁) := card_normIn_le_of_conj_conj hc hneUB
          _ = (2 ^ m) ^ 2 := by rw [hc.card_normIn]
      · rw [← hCU]
        refine Subgroup.card_le_of_le (fun z hz => mem_normIn.2 ⟨hz.1, ?_⟩)
        exact (hwc.conj k).centralizer_le_normalizer hk hy1 hz.2
    have hNP : Nat.card ↥(normIn (conjSubgroup g T) (conjSubgroup x (conjSubgroup k T))) =
        (2 ^ m) ^ 2 := by
      have h1 := normIn_conj x (conjSubgroup g T) (conjSubgroup k T)
      rw [mem_normalizer_iff_conjSubgroup_eq.1 hxU] at h1
      rw [h1, card_conjSubgroup, hNB]
    have hAB : normIn (conjSubgroup g T) (conjSubgroup k T) ⊓
        normIn (conjSubgroup g T) (conjSubgroup x (conjSubgroup k T)) ≤
        conjSubgroup g T ⊓ cfgM T (conjSubgroup y T) ⊓ Subgroup.centralizer ({y} : Set G) :=
      fun a ha => ⟨⟨normIn_le _ _ ha.1, hAM ha⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (hcUB a ha.1)⟩
    refine ⟨conjSubgroup k T, conjSubgroup x (conjSubgroup k T), x * y * x⁻¹, ?_, hsq⟩
    exact
      { wc := hwc.conj g
        glob := hc.hS.conj g
        iso := hc.hI.conj g
        hq := by
          have := hc.one_le_m
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) this
        cardU := by rw [card_conjSubgroup, hc.hT]
        conjB := ⟨k * g⁻¹, by rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]⟩
        conjP := ⟨x * k * g⁻¹, by
          rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, inv_mul_cancel_right]⟩
        neUB := hneUB
        neUP := hneUP
        neBP := hBP
        yB := hk
        y'P := hy'P
        y1 := hy1
        y'1 := hy'1
        comm := hcomm
        yU := hyN
        y'U := hy'U
        cardNB := hNB
        cardNP := hNP
        cardA := (Subgroup.card_le_of_le hAB).trans hB }
  · left
    obtain ⟨a, haA, haM⟩ := IsConcreteLE.not_le_iff_exists.1 hAM
    have haU : a ∈ conjSubgroup g T := normIn_le _ _ haA.1
    have hcent := hS3.cfgM_inf_centralizer_conj hg haU haM
    have hwa : y * (x * y * x⁻¹) ∈
        cfgM T (conjSubgroup y T) ⊓ Subgroup.centralizer ({a} : Set G) := by
      refine ⟨hwM, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := hcUB a haA.1
      have h2 := hcUP a haA.2
      calc y * (x * y * x⁻¹) * a = y * ((x * y * x⁻¹) * a) := mul_assoc _ _ _
        _ = y * (a * (x * y * x⁻¹)) := by rw [← h2]
        _ = (y * a) * (x * y * x⁻¹) := (mul_assoc _ _ _).symm
        _ = (a * y) * (x * y * x⁻¹) := by rw [h1]
        _ = a * (y * (x * y * x⁻¹)) := mul_assoc _ _ _
    rw [hcent] at hwa
    rw [hsq]
    exact mem_classD_of_mem_conjSubgroup (conjSubgroup_mono (normIn_le _ _) hwa) hw1

end CFSG.CGT.Timmesfeld75
