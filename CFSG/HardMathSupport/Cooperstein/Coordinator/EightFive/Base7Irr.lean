module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7NS

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.QuasithinUnique Equiv Equiv.Perm

section Coset

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}

theorem sign_eq_neg_one_of_not_mem_altPre {g : MulAut V} (hg : g ∈ H) (hg' : g ∉ altPre ψ) :
    sign (ψ ⟨g, hg⟩) = -1 := by
  rcases Int.units_eq_one_or (sign (ψ ⟨g, hg⟩)) with h | h
  · exact absurd (mem_altPre_iff.2 ⟨hg, Perm.mem_alternatingGroup.2 h⟩) hg'
  · exact h

theorem inv_mul_mem_altPre {g k : MulAut V} (hg : g ∈ H) (hk : k ∈ H) (hg' : g ∉ altPre ψ)
    (hk' : k ∉ altPre ψ) : g⁻¹ * k ∈ altPre ψ := by
  refine mem_altPre_iff.2 ⟨H.mul_mem (H.inv_mem hg) hk, ?_⟩
  have h1 : (⟨g⁻¹ * k, H.mul_mem (H.inv_mem hg) hk⟩ : ↥H) = (⟨g, hg⟩ : ↥H)⁻¹ * ⟨k, hk⟩ :=
    Subtype.ext rfl
  rw [h1, Perm.mem_alternatingGroup, map_mul, map_inv, map_mul, map_inv,
    sign_eq_neg_one_of_not_mem_altPre hg hg', sign_eq_neg_one_of_not_mem_altPre hk hk']
  decide

theorem mul_mem_altPre {g k : MulAut V} (hg : g ∈ H) (hk : k ∈ H) (hg' : g ∉ altPre ψ)
    (hk' : k ∉ altPre ψ) : k * g ∈ altPre ψ := by
  refine mem_altPre_iff.2 ⟨H.mul_mem hk hg, ?_⟩
  have h1 : (⟨k * g, H.mul_mem hk hg⟩ : ↥H) = (⟨k, hk⟩ : ↥H) * ⟨g, hg⟩ := Subtype.ext rfl
  rw [h1, Perm.mem_alternatingGroup, map_mul, map_mul, sign_eq_neg_one_of_not_mem_altPre hg hg',
    sign_eq_neg_one_of_not_mem_altPre hk hk']
  decide

end Coset

section Numerical

theorem card_mul_card_le_of_inf_eq_bot {G : Type*} [Group G] [Finite G] {P Q : Subgroup G}
    (h : P ⊓ Q = ⊥) : Nat.card P * Nat.card Q ≤ Nat.card G := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun x => (x.1 : G) * x.2) ?_
  rintro ⟨p, q⟩ ⟨p', q'⟩ hpq
  simp only at hpq
  have h1 : (p' : G)⁻¹ * p = q' * (q : G)⁻¹ := by
    calc (p' : G)⁻¹ * p = (p' : G)⁻¹ * (p * q) * (q : G)⁻¹ := by group
      _ = (p' : G)⁻¹ * (p' * q') * (q : G)⁻¹ := by rw [hpq]
      _ = q' * (q : G)⁻¹ := by group
  have h2 : (p' : G)⁻¹ * p ∈ P ⊓ Q :=
    ⟨P.mul_mem (P.inv_mem p'.2) p.2, h1 ▸ Q.mul_mem q'.2 (Q.inv_mem q.2)⟩
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at h2
  have hp : p = p' := Subtype.ext h2.symm
  subst hp
  have hq : (q : G) = q' := mul_left_cancel hpq
  rw [Subtype.ext hq]

variable {V : Type} [CommGroup V] [Finite V]

theorem card_sec_le_index_of_swap {A : Subgroup (MulAut V)} {Y₀ Y' Y₁ : Subgroup V}
    (h0 : Y₀ ≤ Y') (h1 : Y' ≤ Y₁) (hA₀ : A ≤ stabSub Y₀) (hA₁ : A ≤ stabSub Y₁)
    {a : MulAut V} (ha : a ∈ A) (hswap : ∀ y ∈ Y', a y ∈ Y' → y ∈ Y₀) :
    Nat.card (Sec Y' Y₀) ≤ (fixV (autSec A Y₁ Y₀)).index := by
  classical
  set C := fixV (autSec A Y₁ Y₀) with hC
  set X' : Subgroup (Sec Y₁ Y₀) := (Y'.subgroupOf Y₁).map (QuotientGroup.mk' (Y₀.subgroupOf Y₁))
    with hX'
  have hdisj : C ⊓ X' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxC, ⟨y, hy, rfl⟩⟩
    rw [Subgroup.mem_bot]
    have hy' : (y : V) ∈ Y' := Subgroup.mem_subgroupOf.1 hy
    have hfix := (mk_mem_fixV_autSec_iff hA₀ hA₁ y).1 hxC a ha
    have hay : a y ∈ Y' := by
      have h2 := Y'.mul_mem (h0 hfix) hy'
      rwa [inv_mul_cancel_right] at h2
    exact (mk_eq_one_sec_iff y).2 (hswap y hy' hay)
  have hcard1 := card_mul_card_le_of_inf_eq_bot hdisj
  have hcard2 : Nat.card X' = Nat.card (Sec Y' Y₀) := by
    have e1 := B1More.card_map_mul_card_inf_ker (Y'.subgroupOf Y₁)
      (QuotientGroup.mk' (Y₀.subgroupOf Y₁))
    rw [QuotientGroup.ker_mk'] at e1
    have e2 : Y'.subgroupOf Y₁ ⊓ Y₀.subgroupOf Y₁ = Y₀.subgroupOf Y₁ :=
      inf_eq_right.2 fun x hx => Subgroup.mem_subgroupOf.2 (h0 (Subgroup.mem_subgroupOf.1 hx))
    have e3 : Nat.card ↥(Y₀.subgroupOf Y₁) = Nat.card Y₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h0.trans h1)).toEquiv
    have e4 : Nat.card ↥(Y'.subgroupOf Y₁) = Nat.card Y' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h1).toEquiv
    have e5 := card_sec_mul h0
    rw [e2, e3, e4, ← e5] at e1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos e1
  have hidx := C.card_mul_index
  rw [← hcard2]
  rw [← hidx] at hcard1
  exact Nat.le_of_mul_le_mul_left hcard1 Nat.card_pos

omit [Finite V] in
theorem card_le_eight {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 7)}
    (hψ : Function.Injective ψ) {A : Subgroup (MulAut V)} (hA : IsFFStarOffender H A) :
    Nat.card A ≤ 8 := by
  classical
  obtain ⟨hB1, hc, h2, hcard⟩ := B42A57.offender_image hA ψ hψ
  set B := (A.subgroupOf H).map ψ with hB
  obtain ⟨r, f, -, hbound, hcl⟩ := B42A57.gen7 hB1 hc h2
  set σ : Perm (Fin 7) := swap 0 1 * swap 1 2 with hσ
  set τ : Perm (Fin 7) := swap 0 1 * swap 1 3 with hτ
  have hσA : σ ∈ alternatingGroup (Fin 7) := by
    rw [Perm.mem_alternatingGroup, hσ]
    decide
  have hτA : τ ∈ alternatingGroup (Fin 7) := by
    rw [Perm.mem_alternatingGroup, hτ]
    decide
  have hστ : σ * τ ≠ τ * σ := by
    rw [hσ, hτ]
    decide
  set S : Set (Perm (Fin 7)) := {x | ∃ i, ∃ b ∈ B, x = f i * b * (f i)⁻¹} with hS
  have hr : 2 ≤ r := by
    by_contra hr
    push Not at hr
    have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
      rintro x ⟨i, b, hb, rfl⟩ y ⟨j, b', hb', rfl⟩
      have hij : i = j := Fin.ext (by omega)
      subst hij
      calc f i * b * (f i)⁻¹ * (f i * b' * (f i)⁻¹) = f i * (b * b') * (f i)⁻¹ := by group
        _ = f i * (b' * b) * (f i)⁻¹ := by rw [hc b hb b' hb']
        _ = f i * b' * (f i)⁻¹ * (f i * b * (f i)⁻¹) := by group
    have h1 : Subgroup.closure S ≤ Subgroup.centralizer S :=
      (Subgroup.closure_le _).2 fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy =>
        hSc y hy x hx
    have h3 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set (Perm (Fin 7))) :=
      (Subgroup.closure_le _).2 fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy =>
        (Subgroup.mem_centralizer_iff.1 (h1 hy) x hx).symm
    have h4 := Subgroup.mem_centralizer_iff.1 (h3 (hcl hσA)) τ (hcl hτA)
    exact hστ h4.symm
  have hpos : 1 ≤ Nat.card B := Nat.card_pos
  have h5 : Nat.card B ^ 2 ≤ 2 ^ 6 :=
    (Nat.pow_le_pow_right hpos hr).trans hbound
  rw [hcard] at h5
  nlinarith

end Numerical

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}

theorem irr_of_isChiefFac (hV : ∀ v : V, v ^ 2 = 1)
    {ψ : ↥H →* Perm (Fin 7)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 7) ≤ ψ.range) {A : Subgroup (MulAut V)}
    (hAoff : IsFFStarOffender H A) {Y₀ Y₁ : Subgroup V} (hY : IsChiefFac H Y₀ Y₁)
    (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) :
    ∀ Y : Subgroup V, (∀ l ∈ altPre ψ, ∀ y ∈ Y, l y ∈ Y) → Y₀ ≤ Y → Y ≤ Y₁ →
      Y = Y₀ ∨ Y = Y₁ := by
  classical
  set L := altPre ψ with hLdef
  have hH₀ := hY.stab₀
  have hH₁ := hY.stab₁
  intro Y hYinv hY0 hY1
  by_contra hne
  push Not at hne
  set S : Set (Subgroup V) := {Z | (∀ l ∈ L, ∀ z ∈ Z, l z ∈ Z) ∧ Y₀ < Z ∧ Z < Y₁} with hS
  have hYS : Y ∈ S := ⟨hYinv, lt_of_le_of_ne hY0 (Ne.symm hne.1), lt_of_le_of_ne hY1 hne.2⟩
  have : Finite (Subgroup V) := finite_subgroup
  obtain ⟨Y', ⟨hY'inv, hY'0, hY'1⟩, hmin⟩ := WellFounded.has_min wellFounded_lt S ⟨Y, hYS⟩
  have hirr' : ∀ Z : Subgroup V, (∀ l ∈ L, ∀ z ∈ Z, l z ∈ Z) → Y₀ ≤ Z → Z ≤ Y' →
      Z = Y₀ ∨ Z = Y' := by
    intro Z hZ h0 h1
    by_contra hZne
    push Not at hZne
    exact hmin Z ⟨hZ, lt_of_le_of_ne h0 (Ne.symm hZne.1),
      (lt_of_le_of_ne h1 hZne.2).trans hY'1⟩ (lt_of_le_of_ne h1 hZne.2)
  have hLY' : L ≤ stabSub Y' := B1.le_stabSub_of_invariant hY'inv
  have hLY₀ : L ≤ stabSub Y₀ := altPre_le.trans hH₀
  have hLY₁ : L ≤ stabSub Y₁ := altPre_le.trans hH₁
  obtain ⟨g, hgH, hgL⟩ : ∃ g ∈ H, g ∉ L := by
    by_contra hall
    push Not at hall
    rcases hY.eq_or_eq_of_invariant (fun x hx w hw => hY'inv x (hall x hx) w hw) hY'0.le
      hY'1.le with h | h
    · exact (ne_of_gt hY'0) h
    · exact (ne_of_lt hY'1) h
  set Y'' : Subgroup V := Y'.comap (g⁻¹ : MulAut V).toMonoidHom with hY''
  have hmem'' : ∀ x, x ∈ Y'' ↔ g⁻¹ x ∈ Y' := fun x => Iff.rfl
  have hY''₁ : Y'' ≤ Y₁ := fun x hx => by
    have h1 := (hH₁ hgH (g⁻¹ x)).2 (hY'1.le ((hmem'' x).1 hx))
    rwa [MulAut.apply_inv_self] at h1
  have hconjL : ∀ l ∈ L, g⁻¹ * l * g ∈ L := fun l hl => by
    have := conj_mem_altPre (H.inv_mem hgH) hl
    rwa [inv_inv] at this
  have hinvL'' : ∀ l ∈ L, ∀ x ∈ Y'', l x ∈ Y'' := fun l hl x hx => by
    rw [hmem''] at hx ⊢
    have h1 := hY'inv _ (hconjL l hl) _ hx
    simpa [MulAut.mul_apply] using h1
  have hswapY : ∀ k ∈ H, k ∉ L → ∀ y ∈ Y', k y ∈ Y'' := fun k hk hkL y hy => by
    rw [hmem'']
    have h1 := hY'inv _ (inv_mul_mem_altPre hgH hk hgL hkL) y hy
    simpa [MulAut.mul_apply] using h1
  have hswapY'' : ∀ k ∈ H, k ∉ L → ∀ x ∈ Y'', k x ∈ Y' := fun k hk hkL x hx => by
    rw [hmem''] at hx
    have h1 := hY'inv _ (mul_mem_altPre hgH hk hgL hkL) _ hx
    simpa [MulAut.mul_apply] using h1
  have hNinv : ∀ k ∈ H, ∀ x ∈ Y' ⊓ Y'', k x ∈ Y' ⊓ Y'' := by
    intro k hk x hx
    by_cases hkL : k ∈ L
    · exact ⟨hY'inv k hkL x hx.1, hinvL'' k hkL x hx.2⟩
    · exact ⟨hswapY'' k hk hkL x hx.2, hswapY k hk hkL x hx.1⟩
  have hMinv : ∀ k ∈ H, ∀ x ∈ Y' ⊔ Y'', k x ∈ Y' ⊔ Y'' := by
    intro k hk x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    rw [map_mul]
    by_cases hkL : k ∈ L
    · exact Subgroup.mul_mem_sup (hY'inv k hkL y hy) (hinvL'' k hkL z hz)
    · rw [mul_comm]
      exact Subgroup.mul_mem_sup (hswapY'' k hk hkL z hz) (hswapY k hk hkL y hy)
  have hY₀'' : Y₀ ≤ Y'' := fun x hx => by
    rw [hmem'']
    exact hY'0.le ((hH₀ (H.inv_mem hgH) x).2 hx)
  have hN : Y' ⊓ Y'' = Y₀ := by
    rcases hY.eq_or_eq_of_invariant hNinv (le_inf hY'0.le hY₀'') (inf_le_left.trans hY'1.le) with
      h | h
    · exact h
    · exact absurd (h ▸ inf_le_left : Y₁ ≤ Y') (not_le_of_gt hY'1)
  have hM : Y' ⊔ Y'' = Y₁ := by
    rcases hY.eq_or_eq_of_invariant hMinv (hY'0.le.trans le_sup_left) (sup_le hY'1.le hY''₁) with
      h | h
    · exact absurd (h ▸ le_sup_left : Y' ≤ Y₀) (not_le_of_gt hY'0)
    · exact h
  have hswap : ∀ k ∈ H, k ∉ L → ∀ y ∈ Y', k y ∈ Y' → y ∈ Y₀ := by
    intro k hk hkL y hy hky
    have h1 : k y ∈ Y₀ := hN ▸ ⟨hky, hswapY k hk hkL y hy⟩
    have h2 := (hH₀ hk y).1 h1
    exact h2
  have hL₁ : ¬ IsCentralSec L Y₀ Y' := by
    intro hc
    apply hL
    have hc'' : IsCentralSec L Y₀ Y'' := by
      intro l hl x hx
      have h1 := hc _ (hconjL l hl) _ ((hmem'' x).1 hx)
      have h2 := (hH₀ hgH _).2 h1
      simpa [MulAut.mul_apply, map_mul, map_inv] using h2
    intro l hl x hx
    rw [← hM] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    have h1 : l (y * z) * (y * z)⁻¹ = (l y * y⁻¹) * (l z * z⁻¹) := by
      simp only [map_mul, mul_inv_rev]
      simp only [mul_comm, mul_left_comm, mul_assoc]
    rw [h1]
    exact Y₀.mul_mem (hc l hl y hy) (hc'' l hl z hz)
  have hL₂ : ¬ IsCentralSec L Y' Y₁ := by
    intro hc
    apply hL
    intro l hl y hy
    have h2 : l y * y⁻¹ ∈ Y'' := by
      rw [hmem'']
      have h1 := hc _ (hconjL l hl) _ ((hH₁ (H.inv_mem hgH) y).2 hy)
      simpa [MulAut.mul_apply, map_mul, map_inv] using h1
    have h3 : l y * y⁻¹ ∈ Y' ⊓ Y'' := ⟨hc l hl y hy, h2⟩
    rwa [hN] at h3
  have hψ' := altPreRes_injective hψ
  have hA' := le_range_altPreRes hA
  have hpre : altPre (altPreRes ψ) = L := altPre_altPreRes
  by_cases hAL : A ≤ L
  ·
    have h₁ : Nat.card A ≤ (fixV (autSec A Y' Y₀)).index :=
      card_le_index_fixV_autSec_of_irr (H := L) hV hψ' hA' hY'0.le hLY₀ hLY'
        (by rw [hpre]; exact hL₁) (by rw [hpre]; exact hirr') hAL hAoff.2.1 hAoff.2.2.1
    have h₃ : 1 < (fixV (autSec A Y₁ Y')).index :=
      one_lt_index_fixV_autSec (H := L) (by norm_num) hψ' hA' hLY' hLY₁
        (by rw [hpre]; exact hL₂) hAL hAoff.2.1
    exact false_of_index_le_of_one_lt hAoff hY'0.le le_rfl hY'1.le (hAL.trans hLY')
      (hAL.trans hLY₁) h₁ h₃
  ·
    obtain ⟨a, haA, haL⟩ := Set.not_subset.1 hAL
    have haH : a ∈ H := hAoff.1 haA
    have h1 := card_sec_le_index_of_swap hY'0.le hY'1.le (hAoff.1.trans hH₀)
      (hAoff.1.trans hH₁) haA (hswap a haH haL)
    have h2 := card_sec_ge_of_noncentral (H := L) hV hψ' hA' hLY₀ hLY'
      (by rw [hpre]; exact hL₁)
    have h3 := index_fixV_autSec_le hAoff hY.le (hAoff.1.trans hH₁)
    have h4 := card_le_eight hψ hAoff
    omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
