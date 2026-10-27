module

public import CFSG.GH74.GLS.IVK.Proofs2.A7Crit

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.A7Fin

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.IVK.A7

@[expose] def Gam7 (W : Subgroup S7) : Subgroup S7 :=
  ⨆ (t : S7) (_ : t ∈ W) (_ : orderOf t = 2), centralizer ({t} : Set S7) ⊓ alternatingGroup (Fin 7)

theorem le_Gam7 {W : Subgroup S7} {t : S7} (ht : t ∈ W) (h : orderOf t = 2) :
    centralizer ({t} : Set S7) ⊓ alternatingGroup (Fin 7) ≤ Gam7 W :=
  le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le h le_rfl))

theorem alt_le_of_good {H : Subgroup S7} {a b : S7} (ha : a ∈ T0list) (ha2 : a ^ 2 = 1)
    (ha1 : a ≠ 1) (hb : b ∈ T0list) (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1)
    (hHa : centralizer ({a} : Set S7) ⊓ alternatingGroup (Fin 7) ≤ H)
    (hHb : centralizer ({b} : Set S7) ⊓ alternatingGroup (Fin 7) ≤ H) (hg : Good a b = true) :
    alternatingGroup (Fin 7) ≤ H := by
  have hL : ∀ g ∈ GC a ++ GC b, g ∈ H := by
    intro g hg'
    rcases List.mem_append.1 hg' with h | h
    · obtain ⟨hs, hc⟩ := GC_ok a ha ha2 ha1 g h
      exact hHa ⟨mem_centralizer_singleton_iff.2 hc, Equiv.Perm.mem_alternatingGroup.2 hs⟩
    · obtain ⟨hs, hc⟩ := GC_ok b hb hb2 hb1 g h
      exact hHb ⟨mem_centralizer_singleton_iff.2 hc, Equiv.Perm.mem_alternatingGroup.2 hs⟩
  simp only [Good, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨c, hc, hc3⟩, hreach⟩ := hg
  have h3 : c.IsThreeCycle := card_support_eq_three_iff.mp hc3
  have htrans : ∀ j : Fin 7, ∃ h ∈ H, h 6 = j := fun j =>
    reach_sound hL 6 j (by
      have : j ∈ reach (GC a ++ GC b) := by rw [hreach]; exact Finset.mem_univ j
      exact this)
  exact jordan7 H htrans h3 (hL c hc)

section T0

theorem exists_involution_outside_bool : T0list.all (fun x =>
    decide (x ∈ V0list) ||
      V0list.any (fun v => decide ((x * v) ^ 2 = 1) && !decide (x * v ∈ V0list))) = true := by
  decide +kernel

theorem exists_involution_outside : ∀ x ∈ T0list, x ∉ V0list →
    ∃ v ∈ V0list, (x * v) ^ 2 = 1 ∧ x * v ∉ V0list := by
  intro x hx hxV
  have h := List.all_eq_true.1 exists_involution_outside_bool x hx
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  rcases h with h | ⟨v, hv, h2, h3⟩
  · exact absurd h hxV
  · exact ⟨v, hv, h2, h3⟩

theorem r_sq_central : ∀ x ∈ T0list, r ^ 2 * x = x * r ^ 2 := by
  intro x hx
  rw [mem_T0list_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide +kernel

theorem V0_props : ∀ x ∈ V0list, sign x = 1 ∧ x ^ 2 = 1 := by
  intro x hx
  simp only [V0list, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel

theorem V0_gen_bool : V0list.all (fun a => V0list.all (fun b => V0list.all (fun v =>
    !(decide (a ≠ 1) && decide (b ≠ 1) && decide (a ≠ b)) ||
      decide (v = 1 ∨ v = a ∨ v = b ∨ v = a * b)))) = true := by
  decide +kernel

theorem V0_gen : ∀ a ∈ V0list, ∀ b ∈ V0list, a ≠ 1 → b ≠ 1 → a ≠ b →
    ∀ v ∈ V0list, v = 1 ∨ v = a ∨ v = b ∨ v = a * b := by
  intro a ha b hb ha1 hb1 hab v hv
  have h := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 V0_gen_bool a ha) b hb) v hv
  simpa [ha1, hb1, hab] using h

theorem V0_nodup : V0list.Nodup := by decide +kernel

theorem r_sq_mem_V0 : r ^ 2 ∈ V0list := by decide +kernel

theorem r_sq_sq : (r ^ 2) ^ 2 = 1 := by decide +kernel

theorem r_sq_ne_one : r ^ 2 ≠ 1 := by decide +kernel

end T0

theorem one_mem_V0 : (1 : S7) ∈ V0list := by decide +kernel

section Main

theorem a7_T0_main {W : Subgroup S7} (hWT : ∀ x ∈ W, x ∈ T0list) {a b : S7} (ha : a ∈ W)
    (hb : b ∈ W) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hcomm : a * b = b * a) (hΓ : ¬ alternatingGroup (Fin 7) ≤ Gam7 W) :
    ∀ x : S7, x ∈ W ↔ x ∈ V0list := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ x ∈ W, ∀ y ∈ W, x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 → y ≠ 1 → x ≠ y → x * y = y * x →
      x ∈ V0list ∧ y ∈ V0list := by
    intro x hx y hy hx2 hy2 hx1 hy1 hxy hxyc
    by_contra hV
    have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
    have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hy1
    have hxT := hWT x hx
    have hyT := hWT y hy
    have hHx := le_Gam7 hx hxo
    have hHy := le_Gam7 hy hyo
    rcases pair_good x hxT y hyT hx2 hy2 hx1 hy1 hxy hxyc hV with h | h
    · exact hΓ (alt_le_of_good hxT hx2 hx1 hyT hy2 hy1 hHx hHy h)
    · have hxy2 : (x * y) ^ 2 = 1 := by
        calc (x * y) ^ 2 = x * y * (x * y) := pow_two _
          _ = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [← hxyc]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [← pow_two, ← pow_two, hx2, hy2, one_mul]
      have hxy1 : x * y ≠ 1 := by
        intro h
        apply hxy
        have hx' : x * x = 1 := by rw [← pow_two]; exact hx2
        have : y = x⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [this]
        exact (inv_eq_of_mul_eq_one_right hx').symm
      have hmem : x * y ∈ W := W.mul_mem hx hy
      have hxyT := hWT _ hmem
      have hHxy := le_Gam7 hmem (orderOf_eq_prime hxy2 hxy1)
      exact hΓ (alt_le_of_good hxT hx2 hx1 hxyT hxy2 hxy1 hHx hHxy h)
  obtain ⟨haV, hbV⟩ := key a ha b hb ha2 hb2 ha1 hb1 hab hcomm
  have hV0W : ∀ v ∈ V0list, v ∈ W := by
    intro v hv
    rcases V0_gen a haV b hbV ha1 hb1 hab v hv with rfl | rfl | rfl | rfl
    · exact W.one_mem
    · exact ha
    · exact hb
    · exact W.mul_mem ha hb
  intro x
  constructor
  · intro hx
    by_contra hxV
    obtain ⟨v, hv, hxv2, hxvV⟩ := exists_involution_outside x (hWT x hx) hxV
    have hs : x * v ∈ W := W.mul_mem hx (hV0W v hv)
    have hs1 : x * v ≠ 1 := fun h => hxvV (by rw [h]; exact one_mem_V0)
    have hz : r ^ 2 ∈ W := hV0W _ r_sq_mem_V0
    have hzs : r ^ 2 ≠ x * v := fun h => hxvV (by rw [← h]; exact r_sq_mem_V0)
    have hc : r ^ 2 * (x * v) = (x * v) * r ^ 2 := r_sq_central _ (hWT _ hs)
    exact hxvV (key _ hz _ hs r_sq_sq hxv2 r_sq_ne_one hs1 hzs hc).2
  · exact hV0W x

end Main

section Conj

theorem Gam7_map_le (g : S7) (W : Subgroup S7) :
    Gam7 (W.map (MulAut.conj g⁻¹).toMonoidHom) ≤ (Gam7 W).map (MulAut.conj g⁻¹).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcx : ∀ x : S7, (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := fun x => by
    simp
  refine iSup_le fun t => iSup_le fun ht => iSup_le fun ho => ?_
  obtain ⟨u, hu, rfl⟩ := ht
  have hu2 : orderOf u = 2 := by
    rw [← ho]
    exact (orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective u).symm
  have hle : centralizer ({(MulAut.conj g⁻¹).toMonoidHom u} : Set S7) ⊓ alternatingGroup (Fin 7) ≤
      (centralizer ({u} : Set S7) ⊓ alternatingGroup (Fin 7)).map (MulAut.conj g⁻¹).toMonoidHom := by
    intro z hz
    rw [Subgroup.mem_inf, mem_centralizer_singleton_iff, hcx] at hz
    obtain ⟨hzc, hza⟩ := hz
    rw [Subgroup.mem_map]
    refine ⟨g * z * g⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_inf, mem_centralizer_singleton_iff]
      refine ⟨?_, ?_⟩
      · calc g * z * g⁻¹ * u = g * (z * (g⁻¹ * u * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * u * g) * z) * g⁻¹ := by rw [hzc]
          _ = u * (g * z * g⁻¹) := by group
      · rw [Equiv.Perm.mem_alternatingGroup] at hza ⊢
        have := sign_conj_eq g⁻¹ z
        rw [inv_inv] at this
        exact this.trans hza
    · rw [hcx]
      group
  exact hle.trans (Subgroup.map_mono (le_Gam7 hu hu2))

theorem a7_concrete {W : Subgroup S7} (hW : IsPGroup 2 ↥W) {a b : S7} (ha : a ∈ W) (hb : b ∈ W)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hcomm : a * b = b * a) (hΓ : ¬ alternatingGroup (Fin 7) ≤ Gam7 W) :
    (∀ x ∈ W, x ∈ alternatingGroup (Fin 7) ∧ x ^ 2 = 1) ∧ Nat.card ↥W = 4 := by
  obtain ⟨T, hWT⟩ := hW.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_T0 T
  set c : MulAut S7 := MulAut.conj g⁻¹ with hc
  have hcx : ∀ x, c x = g⁻¹ * x * g := fun x => by simp [hc]
  set W' : Subgroup S7 := W.map c.toMonoidHom with hW'
  have hW'T : ∀ x ∈ W', x ∈ T0list := by
    rintro _ ⟨y, hy, rfl⟩
    have := (hg y).1 (hWT hy)
    show c y ∈ T0list
    rw [hcx]
    exact this
  have hΓ' : ¬ alternatingGroup (Fin 7) ≤ Gam7 W' := by
    intro hle
    apply hΓ
    intro x hx
    have hx' : c x ∈ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup] at hx ⊢
      rw [hcx]
      exact (sign_conj_eq g x).trans hx
    obtain ⟨y, hy, hyx⟩ := Gam7_map_le g W (hle hx')
    have : y = x := c.injective hyx
    rw [← this]
    exact hy
  have hmain := a7_T0_main hW'T (a := c a) (b := c b) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    (by rw [← map_pow, ha2, map_one]) (by rw [← map_pow, hb2, map_one])
    (fun h => ha1 (c.injective (by rw [h, map_one])))
    (fun h => hb1 (c.injective (by rw [h, map_one])))
    (fun h => hab (c.injective h))
    (by rw [← map_mul, ← map_mul, hcomm]) hΓ'
  refine ⟨fun x hx => ?_, ?_⟩
  · have hxV : c x ∈ V0list := (hmain (c x)).1 ⟨x, hx, rfl⟩
    obtain ⟨hs, hsq⟩ := V0_props _ hxV
    refine ⟨?_, c.injective (by rw [map_pow, hsq, map_one])⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    rw [hcx] at hs
    exact (sign_conj_eq g x).symm.trans hs
  · have h1 : Nat.card ↥W = Nat.card ↥W' := by
      rw [hW', Subgroup.card_map_of_injective c.injective]
    have h2 : Nat.card ↥W' = Nat.card ↥(V0list.toFinset) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => (hmain x).trans List.mem_toFinset.symm))
    rw [h1, h2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup V0_nodup]
    rfl

end Conj

end CFSG.GH74.GLS.IVK.Proofs2.A7Fin
