module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Ctx
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Nat
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7Irr
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.EightCycles
import CFSG.Quasithin.Background.SmithB51P2
import CFSG.Quasithin.Background.G64Realize
import CFSG.Holt.General.CommutingSimpleCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Equiv Equiv.Perm

section Split

variable {V : Type} [CommGroup V]

structure SplitFac (H L : Subgroup (MulAut V)) (Y₀ Y' Y₁ : Subgroup V) (g : MulAut V) : Prop where
  le₀ : Y₀ ≤ Y'
  le₁ : Y' ≤ Y₁
  stab : L ≤ stabSub Y'
  irr : ∀ Z : Subgroup V, (∀ l ∈ L, ∀ z ∈ Z, l z ∈ Z) → Y₀ ≤ Z → Z ≤ Y' → Z = Y₀ ∨ Z = Y'
  nc₀ : ¬ IsCentralSec L Y₀ Y'
  nc₁ : ¬ IsCentralSec L Y' Y₁
  memH : g ∈ H
  notL : g ∉ L
  inf_eq : Y' ⊓ Y'.comap (g⁻¹ : MulAut V).toMonoidHom = Y₀
  sup_eq : Y' ⊔ Y'.comap (g⁻¹ : MulAut V).toMonoidHom = Y₁
  swap : ∀ k ∈ H, k ∉ L → ∀ y ∈ Y', k y ∈ Y' → y ∈ Y₀

variable [Finite V]

theorem card_sec_eq_of_split {Y₀ Y' Y₁ : Subgroup V} {g : MulAut V} (h0 : Y₀ ≤ Y')
    (hN : Y' ⊓ Y'.comap (g⁻¹ : MulAut V).toMonoidHom = Y₀)
    (hM : Y' ⊔ Y'.comap (g⁻¹ : MulAut V).toMonoidHom = Y₁) :
    Nat.card (Sec Y₁ Y') = Nat.card (Sec Y' Y₀) := by
  set Y'' := Y'.comap (g⁻¹ : MulAut V).toMonoidHom with hY''
  have hc : Nat.card Y'' = Nat.card Y' := Nat.card_congr
    { toFun := fun x => ⟨g⁻¹ x, x.2⟩
      invFun := fun y => ⟨g y, by
        show (g⁻¹ : MulAut V) (g y) ∈ Y'
        rw [MulAut.inv_apply_self]
        exact y.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  have h0'' : Y₀ ≤ Y'' := hN ▸ inf_le_right
  have e1 : Nat.card (Sec Y₁ Y') = Y'.relIndex Y₁ := rfl
  have e2 : Nat.card (Sec Y' Y₀) = Y₀.relIndex Y' := rfl
  have e3 : Y'.relIndex Y₁ = Y₀.relIndex Y'' := by
    rw [← hM, sup_comm, Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right, hN]
  have e4 := Subgroup.relIndex_mul_card (H := Y₀) (K := Y'')
  have e5 := Subgroup.relIndex_mul_card (H := Y₀) (K := Y')
  rw [inf_eq_left.2 h0''] at e4
  rw [inf_eq_left.2 h0] at e5
  rw [e1, e2, e3]
  have hpos : 0 < Nat.card Y₀ := Nat.card_pos
  rw [hc, ← e5] at e4
  exact Nat.eq_of_mul_eq_mul_right hpos e4

variable {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}

theorem exists_splitFac {Y₀ Y₁ : Subgroup V} (hY : IsChiefFac H Y₀ Y₁)
    (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) {Y : Subgroup V}
    (hYinv : ∀ l ∈ altPre ψ, ∀ y ∈ Y, l y ∈ Y) (hY0 : Y₀ ≤ Y) (hY1 : Y ≤ Y₁)
    (hne : Y ≠ Y₀ ∧ Y ≠ Y₁) : ∃ Y' g, SplitFac H (altPre ψ) Y₀ Y' Y₁ g := by
  classical
  set L := altPre ψ with hLdef
  have hH₀ := hY.stab₀
  have hH₁ := hY.stab₁
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
    exact (hH₀ hk y).1 h1
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
  exact ⟨Y', g, ⟨hY'0.le, hY'1.le, hLY', hirr', hL₁, hL₂, hgH, hgL, hN, hM, hswap⟩⟩

end Split

section Orders

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 8)}

omit [Finite V] in
theorem card_autSec_altPre (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin 8) ≤ ψ.range)
    {Y₀ Y₁ : Subgroup V} (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) : Nat.card (autSec (altPre ψ) Y₁ Y₀) = 20160 := by
  rw [card_autSec_eq_card (by norm_num) hψ hA hH₀ hH₁ hL altPre_le,
    Nat.card_congr (altPreEquiv hψ hA).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem eq_four_of_binaryNaturalSL {X : Type} [CommGroup X] {G : Subgroup (MulAut X)} {m : ℕ}
    (hm : m = 4 ∨ m = 5) (h : BinaryNaturalSL G ⊤ ⊥ m 1) (hG : Nat.card G = 20160) : m = 4 := by
  rcases hm with rfl | rfl
  · rfl
  · exfalso
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv h
    have := Fintype.ofFinite K
    have hK2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK, pow_one]
    have h1 := Nat.card_congr e.toEquiv
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 5 K).toEquiv, Matrix.card_SL_field,
      hK2, hG] at h1
    revert h1
    decide

omit [Finite V] in
theorem card_le_sixteen (hψ : Function.Injective ψ) {B : Subgroup (MulAut V)} (hBH : B ≤ H)
    (hel : IsElemAbelian2 B) : Nat.card B ≤ 16 := by
  have h := CFSG.Holt.General.card_sq_le_two_pow_ncard_of_forall_sq_eq_one
    ((B.subgroupOf H).map ψ) (fun u hu => by rw [pow_two]; exact mul_self_of_mem_map hel u hu)
    Set.univ (fun _ _ y hy => absurd (Set.mem_univ y) hy)
  rw [Set.ncard_univ, Nat.card_fin, card_map_subgroupOf hψ hBH] at h
  by_contra hlt
  push Not at hlt
  nlinarith

theorem sixteen_le_card_sec (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 8) ≤ ψ.range) {Y₀ Y₁ : Subgroup V}
    (hL₀ : altPre ψ ≤ stabSub Y₀) (hL₁ : altPre ψ ≤ stabSub Y₁)
    (hnc : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) : 16 ≤ Nat.card (Sec Y₁ Y₀) := by
  set ι := altPreEquiv hψ hA
  obtain ⟨x, hx, h3⟩ := exists_isThreeCycle_mem (by norm_num) ι
  obtain ⟨s, hs, hs1, hs5, -⟩ := exists_mem_pow_five ι hx h3
  have hfaith : altPre ψ ⊓ centSec Y₁ Y₀ = ⊥ := by
    have h := inf_centSec_eq_bot (H := altPre ψ) (ψ := altPreRes ψ) (by norm_num)
      (altPreRes_injective hψ) (le_range_altPreRes hA) hL₀ hL₁ (by rwa [altPre_altPreRes])
    exact h
  have hinj := secHom_injective hL₀ hL₁ hfaith
  refine B42A57.card_ge_sixteen_of_order_five (fun w => by
    have := sq_eq_one_sec hV Y₁ Y₀ w
    rwa [pow_two] at this) (secHom hL₀ hL₁ ⟨s, hs⟩) ?_ ?_
  · rw [← map_pow, show (⟨s, hs⟩ : ↥(altPre ψ)) ^ 5 = 1 from Subtype.ext hs5, map_one]
  · intro h1
    apply hs1
    have := hinj (h1.trans (map_one _).symm)
    exact congrArg Subtype.val this

end Orders

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 8)}

theorem card_sec_eq_sixteen_of_le (hB42 : B42L42Core) (hV : ∀ v : V, v ^ 2 = 1)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin 8) ≤ ψ.range)
    {A : Subgroup (MulAut V)} (hAoff : IsFFStarOffender H A) (hAL : A ≤ altPre ψ)
    {Y₀ Y' Y₁ : Subgroup V} {g : MulAut V} (hY : IsChiefFac H Y₀ Y₁)
    (hS : SplitFac H (altPre ψ) Y₀ Y' Y₁ g) : Nat.card (Sec Y' Y₀) = 16 := by
  set L := altPre ψ with hLdef
  have hψ' := altPreRes_injective hψ
  have hA' := le_range_altPreRes hA
  have hpre : altPre (altPreRes ψ) = L := altPre_altPreRes
  have hLY₀ : L ≤ stabSub Y₀ := altPre_le.trans hY.stab₀
  have hLY₁ : L ≤ stabSub Y₁ := altPre_le.trans hY.stab₁
  have hlt : Y₀ < Y' := lt_of_le_of_ne hS.le₀ fun h => hS.nc₀ (by
    intro l hl y hy
    rw [← h] at hy
    exact Y₀.mul_mem ((hLY₀ hl y).2 hy) (Y₀.inv_mem hy))
  have h12 := index_mul_index_le hAoff hS.le₀ le_rfl hS.le₁ (hAL.trans hS.stab)
    (hAoff.1.trans hY.stab₁)
  have h2 : 1 < (fixV (autSec A Y₁ Y')).index :=
    one_lt_index_fixV_autSec (H := L) (ψ := altPreRes ψ) (by norm_num) hψ' hA' hS.stab hLY₁
      (by rw [hpre]; exact hS.nc₁) hAL hAoff.2.1
  have hstrong : (fixV (autSec A Y' Y₀)).index < Nat.card A := by
    have : (fixV (autSec A Y' Y₀)).index * 2 ≤ Nat.card A :=
      (Nat.mul_le_mul_left _ h2).trans h12
    have hpos : 0 < (fixV (autSec A Y' Y₀)).index := Nat.pos_of_ne_zero
      Subgroup.index_ne_zero_of_finite
    omega
  obtain ⟨A₀, -, hA₀, hA₀s⟩ := exists_strong_isFFStarOffender_autSec (H := L) (ψ := altPreRes ψ)
    (by norm_num) hψ' hA' hLY₀ hS.stab (by rw [hpre]; exact hS.nc₀) hAL hAoff.2.1 hAoff.2.2.1
    hstrong
  have hcard : Nat.card (autSec L Y' Y₀) = 20160 := by
    have h := card_autSec_altPre (ψ := altPreRes ψ) hψ' hA' hLY₀ hS.stab
      (by rw [hpre]; exact hS.nc₀)
    rwa [hpre] at h
  have hB := b42_autSec (ψ := altPreRes ψ) hB42 hV hψ' hA' hLY₀ hS.stab hlt
    (by rw [hpre]; exact hS.nc₀) (by rw [hpre]; exact hS.irr) hA₀
  rw [hpre] at hB
  rcases hB with ⟨-, m, hm, hnat, -⟩ | ⟨-, ⟨-, -, -, hq⟩ | ⟨-, ⟨e⟩, -⟩⟩
  · rw [G64.BinaryNaturalSL.card_eq hnat, eq_four_of_binaryNaturalSL hm hnat hcard]
    norm_num
  · exfalso
    have h1 := card_le_index_fixV_of_one_le_qOf (sq_eq_one_sec hV Y' Y₀) (hq ▸ le_rfl) hA₀.1
      hA₀.2.1 hA₀.2.2.1
    omega
  · exfalso
    have h1 := Nat.card_congr e.toEquiv
    rw [hcard, Nat.card_perm, Nat.card_fin] at h1
    revert h1
    decide

theorem chief_cases (hB42 : B42L42Core) (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 8) ≤ ψ.range) {A : Subgroup (MulAut V)}
    (hAoff : IsFFStarOffender H A) {Y₀ Y₁ : Subgroup V} (hY : IsChiefFac H Y₀ Y₁)
    (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) :
    (Nat.card (Sec Y₁ Y₀) = 16 ∧ altPre ψ = H) ∨ NatSec ψ Y₀ Y₁ ∨
      ∃ Y' g, SplitFac H (altPre ψ) Y₀ Y' Y₁ g ∧ Nat.card (Sec Y' Y₀) = 16 ∧
        Nat.card (Sec Y₁ Y') = 16 := by
  set L := altPre ψ with hLdef
  by_cases hirr : ∀ Y : Subgroup V, (∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y) → Y₀ ≤ Y → Y ≤ Y₁ →
      Y = Y₀ ∨ Y = Y₁
  · obtain ⟨A₀, -, hA₀, -⟩ := exists_isFFStarOffender_autSec_of_offender (by norm_num) hψ hA
      hY.stab₀ hY.stab₁ hY.le hL hAoff
    have hcard := card_autSec_altPre hψ hA hY.stab₀ hY.stab₁ hL
    rcases b42_autSec hB42 hV hψ hA hY.stab₀ hY.stab₁ hY.lt hL hirr hA₀ with
      ⟨-, m, hm, hnat, -⟩ | ⟨hext, -⟩
    ·
      left
      have h16 : Nat.card (Sec Y₁ Y₀) = 16 := by
        rw [G64.BinaryNaturalSL.card_eq hnat, eq_four_of_binaryNaturalSL hm hnat hcard]
        norm_num
      refine ⟨h16, ?_⟩
      have htop := G64.BinaryNaturalSL.eq_top hnat
      have hcH := card_autSec_eq_card (by norm_num) hψ hA hY.stab₀ hY.stab₁ hL (le_refl H)
      have hcL := card_autSec_eq_card (by norm_num) hψ hA hY.stab₀ hY.stab₁ hL
        (altPre_le (ψ := ψ))
      refine Subgroup.eq_of_le_of_card_ge altPre_le ?_
      rw [← hcH, ← hcL]
      exact Subgroup.card_le_of_le (htop ▸ le_top)
    ·
      right
      left
      exact natSec_of_alternatingNatural (by norm_num) (by norm_num) hψ hA hY.stab₀ hY.stab₁ hL
        (B5.P2.alternatingNatural_eight hext)
  ·
    right
    right
    push Not at hirr
    obtain ⟨Y, hYinv, hY0, hY1, hne⟩ := hirr
    obtain ⟨Y', g, hS⟩ := exists_splitFac hY hL hYinv hY0 hY1 hne
    have hLY₀ : L ≤ stabSub Y₀ := altPre_le.trans hY.stab₀
    have h16 : Nat.card (Sec Y' Y₀) = 16 := by
      by_cases hAL : A ≤ L
      · exact card_sec_eq_sixteen_of_le hB42 hV hψ hA hAoff hAL hY hS
      · obtain ⟨a, haA, haL⟩ := Set.not_subset.1 hAL
        have h1 := card_sec_le_index_of_swap hS.le₀ hS.le₁ (hAoff.1.trans hY.stab₀)
          (hAoff.1.trans hY.stab₁) haA (hS.swap a (hAoff.1 haA) haL)
        have h2 := index_fixV_autSec_le hAoff hY.le (hAoff.1.trans hY.stab₁)
        have h3 := card_le_sixteen hψ hAoff.1 hAoff.2.2.1
        have h4 := sixteen_le_card_sec hV hψ hA hLY₀ hS.stab hS.nc₀
        omega
    exact ⟨Y', g, hS, h16, (card_sec_eq_of_split hS.le₀ hS.inf_eq hS.sup_eq).trans h16⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
