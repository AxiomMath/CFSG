module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveComm
public import CFSG.CGT.PushingUpLit.CGT6M.FiveLocal

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem exists_mem_commSub_ne {x : MulAut V} (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1)
    (hV : ∀ v : V, v ^ 2 = 1) : ∃ n ∈ commSub x, x n ≠ n := by
  have hne : commSub x ≠ ⊥ := fun h => hx1 (commSub_eq_bot_iff.mp h)
  obtain ⟨⟨n, hn⟩, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  refine ⟨n, hn, fun h => hn1 ?_⟩
  have hmem : n ∈ commSub x ⊓ fixSub x := ⟨hn, h⟩
  rw [commSub_inf_fixSub_eq_bot (by decide : Odd 5) hx5 hV, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

omit [Finite V] in
theorem fixSub_inv_of_mem {x : MulAut V} {n : V} (h : n ∈ fixSub x) : n ∈ fixSub x⁻¹ := by
  rw [mem_fixSub] at h ⊢
  have : x⁻¹ (x n) = x⁻¹ n := by rw [h]
  rw [MulAut.inv_apply_self] at this
  exact this.symm

theorem false_of_invariant_subgroup {a b g : MulAut V} (ha5 : a ^ 5 = 1) (hab : Commute a b)
    (hga : g * a * g⁻¹ = b) (hgb : g * b * g⁻¹ = (a * b)⁻¹) (N : Subgroup V)
    (hV : ∀ v : V, v ^ 2 = 1) (hN : Nat.card N ≤ 2 ^ 8) (ha : ∀ n ∈ N, a n ∈ N)
    (hb : ∀ n ∈ N, b n ∈ N) (hg : ∀ n ∈ N, g n ∈ N) (hna : ∃ n ∈ N, a n ≠ n) : False := by
  let a' : stabAut N := ⟨a, ha⟩
  let b' : stabAut N := ⟨b, hb⟩
  let g' : stabAut N := ⟨g, hg⟩
  have h1 : g' * a' * g'⁻¹ = b' := Subtype.ext (by simpa using hga)
  have h2 : g' * b' * g'⁻¹ = (a' * b')⁻¹ := Subtype.ext (by simpa using hgb)
  have h3 : a' * b' = b' * a' := Subtype.ext hab.eq
  have h4 : a' ^ 5 = 1 := Subtype.ext ha5
  have hA1 : restrictHom N a' ≠ 1 := by
    rw [Ne, restrictHom_eq_one_iff]
    intro h
    obtain ⟨n, hn, hne⟩ := hna
    exact hne (h n hn)
  obtain ⟨d, hd⟩ := exists_card_eq_two_pow hV N
  have hd8 : d ≤ 8 := by
    rw [hd] at hN
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hN
  refine false_of_five_local (V := ↥N) hd hd8 (A := restrictHom N a') (B := restrictHom N b')
    (G := restrictHom N g') hA1 (by rw [← map_pow, h4, map_one]) ?_ ?_ ?_
  · have := congrArg (restrictHom N) h3
    rw [map_mul, map_mul] at this
    exact this
  · have := congrArg (restrictHom N) h1
    rw [map_mul, map_mul, map_inv] at this
    exact this
  · have := congrArg (restrictHom N) h2
    rw [map_mul, map_mul, map_inv, map_inv, map_mul] at this
    exact this

theorem false_of_lines {a b g : MulAut V} (ha1 : a ≠ 1) (ha5 : a ^ 5 = 1) (hab : Commute a b)
    (hga : g * a * g⁻¹ = b) (hgb : g * b * g⁻¹ = (a * b)⁻¹) (hV : ∀ v : V, v ^ 2 = 1)
    (h16 : Nat.card (commSub a) ≤ 16) : False := by
  have hb5 : b ^ 5 = 1 := by rw [← hga, conj_pow, ha5]; group
  set c := (a * b)⁻¹ with hc
  have habc : a * b * c = 1 := by rw [hc]; group
  have hac : Commute a c := ((Commute.refl a).mul_right hab).inv_right
  have hbc : Commute b c := (hab.symm.mul_right (Commute.refl b)).inv_right
  have hbc_inv : (b * c)⁻¹ = a := by
    have : b * c = a⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [← mul_assoc]; exact habc
    rw [this, inv_inv]
  have hgc : g * c * g⁻¹ = a := by
    calc g * c * g⁻¹ = (g * a * g⁻¹ * (g * b * g⁻¹))⁻¹ := by rw [hc]; group
      _ = (b * c)⁻¹ := by rw [hga, hgb]
      _ = a := hbc_inv
  have hNa : Nat.card (commSub a) = 16 := card_commSub_eq_sixteen ha5 ha1 hV h16
  have hNb : Nat.card (commSub b) = 16 := by
    rw [← hga, card_commSub_conj]; exact hNa
  have hNc : Nat.card (commSub c) = 16 := by
    rw [show c = g * b * g⁻¹ from hgb.symm, card_commSub_conj]; exact hNb
  have hmapa : (commSub a).map (g : V ≃* V).toMonoidHom = commSub b := by
    rw [map_commSub_conj, hga]
  have hmapb : (commSub b).map (g : V ≃* V).toMonoidHom = commSub c := by
    rw [map_commSub_conj, show c = g * b * g⁻¹ from hgb.symm]
  have K1 := commSub_dichotomy hab.eq hb5 hV hNa hNb
  have K2 := commSub_dichotomy hbc.symm.eq hb5 hV hNc hNb
  rcases K1 with h1 | h1
  · rcases K2 with h2 | h2
    ·
      have hbfix : commSub b ≤ fixSub b := by
        intro n hn
        have hbeq : b = a⁻¹ * c⁻¹ := by
          calc b = a⁻¹ * (a * b * c) * c⁻¹ := by group
            _ = a⁻¹ * c⁻¹ := by rw [habc, mul_one]
        rw [mem_fixSub, hbeq]
        have hA := fixSub_inv_of_mem (h1 hn)
        have hC := fixSub_inv_of_mem (h2 hn)
        rw [mem_fixSub] at hA hC
        show a⁻¹ (c⁻¹ n) = n
        rw [hC, hA]
      have hle : commSub b ≤ commSub b ⊓ fixSub b := le_inf le_rfl hbfix
      rw [commSub_inf_fixSub_eq_bot (by decide : Odd 5) hb5 hV] at hle
      have hbot : commSub b = ⊥ := le_bot_iff.mp hle
      rw [hbot, Subgroup.card_bot] at hNb
      omega
    ·
      have hgN : (commSub b).map (g : V ≃* V).toMonoidHom = commSub b := by rw [hmapb, h2]
      have hb1 : b ≠ 1 := by
        intro h
        rw [h] at hga
        apply ha1
        simpa using hga
      refine false_of_invariant_subgroup (a := b) (b := c) (g := g) hb5 hbc hgb ?_ (commSub b)
        hV (by rw [hNb]; norm_num) (fun n hn => apply_mem_commSub rfl hn)
        (fun n hn => apply_mem_commSub hbc.eq hn) (fun n hn => ?_)
        (exists_mem_commSub_ne hb5 hb1 hV)
      · rw [hgc, hbc_inv]
      · rw [← hgN]
        exact ⟨n, hn, rfl⟩
  ·
    have hgN : (commSub a).map (g : V ≃* V).toMonoidHom = commSub a := by rw [hmapa, h1]
    refine false_of_invariant_subgroup (a := a) (b := b) (g := g) ha5 hab hga hgb (commSub a)
      hV (by rw [hNa]; norm_num) (fun n hn => apply_mem_commSub rfl hn)
      (fun n hn => apply_mem_commSub hab.eq hn) (fun n hn => ?_)
      (exists_mem_commSub_ne ha5 ha1 hV)
    rw [← hgN]
    exact ⟨n, hn, rfl⟩

theorem mapM_mapM (w : ZMod 5 × ZMod 5) : mapM (mapM w) = -(w + mapM w) := by
  ext <;> simp [mapM] <;> ring

theorem false_of_lines_hom (Φ : C55 →* MulAut V) (G : MulAut V)
    (hM : ∀ u : C55, Φ (AddMonoidHom.toMultiplicative mapM u) = G * Φ u * G⁻¹)
    (hΦ : Function.Injective Φ) {w : ZMod 5 × ZMod 5} (hw : w ≠ 0) (hV : ∀ v : V, v ^ 2 = 1)
    (h16 : Nat.card (commSub (Φ (Multiplicative.ofAdd w))) ≤ 16) : False := by
  have hga : G * Φ (Multiplicative.ofAdd w) * G⁻¹ = Φ (Multiplicative.ofAdd (mapM w)) := by
    rw [← hM]
    rfl
  have hgb : G * Φ (Multiplicative.ofAdd (mapM w)) * G⁻¹ =
      (Φ (Multiplicative.ofAdd w) * Φ (Multiplicative.ofAdd (mapM w)))⁻¹ := by
    rw [← hM, ← map_mul, ← map_inv, ← ofAdd_add, ← ofAdd_neg, ← mapM_mapM]
    rfl
  refine false_of_lines (a := Φ (Multiplicative.ofAdd w)) (b := Φ (Multiplicative.ofAdd (mapM w)))
    (g := G) ?_ ?_ ((Commute.all _ _).map Φ) hga hgb hV h16
  · intro h
    exact hw (by simpa using hΦ (h.trans (map_one Φ).symm))
  · rw [← map_pow, ← ofAdd_nsmul]
    have h5 : (5 : ℕ) • w = 0 := by
      have h5' : (5 : ZMod 5) = 0 := by decide
      ext <;> simp [h5']
    rw [h5]
    exact map_one Φ

end CFSG.CGT.PushingUpLit.CGT6M
