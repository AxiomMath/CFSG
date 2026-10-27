module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.ConsBasic
public import CFSG.CGT.PushingUpLit.CGT6.Diag.Defs

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Cons

open CFSG.Quasithin
open scoped commutatorElement

variable {V : Type} [CommGroup V] {K K' Y : Subgroup (MulAut V)} {t : MulAut V}

theorem exists_ne_one (h : DiagPre K K' Y t) : ∃ g ∈ K, g ≠ 1 := by
  have : Nontrivial (↥K ⧸ Subgroup.center ↥K) := h.quasi.2.toNontrivial
  have : Nontrivial ↥K := (QuotientGroup.mk'_surjective (Subgroup.center ↥K)).nontrivial
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥K)
  exact ⟨g, g.2, fun h1 => hg (Subtype.ext h1)⟩

theorem isPerfect_K (h : DiagPre K K' Y t) : Group.IsPerfect ↥K := ⟨h.quasi.1⟩

theorem card_K' (h : DiagPre K K' Y t) : Nat.card ↥K' = Nat.card ↥K := by
  rw [h.Kconj]
  exact Subgroup.card_map_of_injective (MulAut.conj t).injective

theorem conj_mem_K' (h : DiagPre K K' Y t) {k : MulAut V} (hk : k ∈ K) : t * k * t⁻¹ ∈ K' := by
  rw [h.Kconj]
  exact ⟨k, hk, by simp [MulAut.conj_apply]⟩

theorem top_ne_bot (h : DiagPre K K' Y t) : (⊤ : Subgroup V) ≠ ⊥ := by
  obtain ⟨g, -, hg⟩ := exists_ne_one h
  obtain ⟨v, hv⟩ := exists_apply_ne hg
  intro h0
  have : v ∈ (⊥ : Subgroup V) := h0 ▸ Subgroup.mem_top v
  rw [Subgroup.mem_bot] at this
  exact hv (by rw [this, map_one])

theorem fixV_eq_bot (h : DiagPair K K' Y t) : fixV K = ⊥ := by
  have hinv : GInv (K ⊔ K') (fixV K) := by
    rw [ginv_sup_iff]
    refine ⟨fun g hg a ha => ?_, fun g hg a ha x hx => ?_⟩
    · rw [ha g hg]
      exact ha
    · rw [apply_comm (h.comm x hx g hg), ha x hx]
  rcases h.irr _ hinv with h0 | h0
  · exact h0
  · exfalso
    obtain ⟨g, hg, hg1⟩ := exists_ne_one h.toDiagPre
    have : ∀ v : V, g v = v := fun v => (h0 ▸ (Subgroup.mem_top v : v ∈ (⊤ : Subgroup V))) g hg
    exact hg1 (MulEquiv.ext this)

theorem exists_move (h : DiagPair K K' Y t) {W : Subgroup V} (hW : W ≠ ⊥) :
    ∃ k ∈ K, ∃ w ∈ W, k w ≠ w :=
  exists_move_of_fixV (fixV_eq_bot h) hW

theorem commV_K_eq_top (h : DiagPair K K' Y t) : commV K = ⊤ := by
  have hinv : GInv (K ⊔ K') (commV K) := by
    rw [ginv_sup_iff]
    exact ⟨fun g hg w hw => commV_invariant hg hw,
      fun b hb w hw => apply_mem_commV_of_commute (fun a ha => h.comm a ha b hb) hw⟩
  rcases h.irr _ hinv with h0 | h0
  · exfalso
    obtain ⟨g, hg, hg1⟩ := exists_ne_one h.toDiagPre
    obtain ⟨v, hv⟩ := exists_apply_ne hg1
    have hmem : g v * v⁻¹ ∈ commV K := Subgroup.subset_closure ⟨g, hg, v, rfl⟩
    rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hv hmem
  · exact h0

theorem exists_minInv [Finite V] (K : Subgroup (MulAut V)) (hV : (⊤ : Subgroup V) ≠ ⊥) :
    ∃ W, DiagMinInv K W := by
  obtain ⟨W, ⟨hW0, hWK⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup V))
    {A : Subgroup V | A ≠ ⊥ ∧ GInv K A} ⟨⊤, hV, fun g _ a _ => Subgroup.mem_top _⟩
  refine ⟨W, hW0, hWK, fun A hA hAW => ?_⟩
  by_cases hA0 : A = ⊥
  · exact Or.inl hA0
  · right
    by_contra hne
    exact hmin A ⟨hA0, hA⟩ (lt_of_le_of_ne hAW hne)

theorem mem_diagImg {y : MulAut V} {W : Subgroup V} {x : V} :
    x ∈ diagImg y W ↔ ∃ w ∈ W, y w = x := Subgroup.mem_map

theorem diagImg_mul_eq {W : Subgroup V} (hW : GInv K W) {k k₀ : MulAut V} (hk : k ∈ K)
    (hcomm : ∀ x ∈ K, x * k₀ = k₀ * x) : diagImg (k * k₀) W = diagImg k₀ W := by
  ext x
  rw [mem_diagImg, mem_diagImg]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨k w, hW k hk w hw, ?_⟩
    rw [MulAut.mul_apply, apply_comm (hcomm k hk)]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨k⁻¹ w, hW k⁻¹ (K.inv_mem hk) w hw, ?_⟩
    rw [MulAut.mul_apply, apply_comm (hcomm k hk) (k⁻¹ w)]
    simp

theorem ginv_diagImg {W : Subgroup V} (hW : GInv K W) {k₀ : MulAut V}
    (hcomm : ∀ x ∈ K, x * k₀ = k₀ * x) : GInv K (diagImg k₀ W) := by
  intro g hg _ hx
  obtain ⟨w, hw, rfl⟩ := mem_diagImg.mp hx
  exact mem_diagImg.mpr ⟨g w, hW g hg w hw, (apply_comm (hcomm g hg) w).symm⟩

theorem commV_zpowers_le_sup [Finite V] {y : MulAut V} {W : Subgroup V}
    (hinf : W ⊓ diagImg y W = ⊥)
    (hcard : Nat.card ↥W = Nat.card ↥(commV (Subgroup.zpowers y))) :
    commV (Subgroup.zpowers y) ≤ W ⊔ diagImg y W := by
  let φ : ↥W →* ↥(commV (Subgroup.zpowers y)) :=
    { toFun := fun w => ⟨y (w : V) * (w : V)⁻¹, Subgroup.subset_closure
        ⟨y, Subgroup.mem_zpowers y, (w : V), rfl⟩⟩
      map_one' := by simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : y (w : V) * (w : V)⁻¹ = 1 := congrArg Subtype.val hw
    have h2 : y (w : V) = w := mul_inv_eq_one.mp h1
    have h3 : (w : V) ∈ W ⊓ diagImg y W :=
      ⟨w.2, mem_diagImg.mpr ⟨w, w.2, h2⟩⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le hcard.ge
  intro u hu
  obtain ⟨w, hw⟩ := hbij.2 ⟨u, hu⟩
  have : u = y (w : V) * (w : V)⁻¹ := (congrArg Subtype.val hw).symm
  rw [this, mul_comm]
  exact Subgroup.mul_mem_sup (W.inv_mem w.2) (mem_diagImg.mpr ⟨w, w.2, rfl⟩)

theorem commutator_mul_aux {G : Type*} [Group G] (a k c : G) (hac : a * c = c * a) :
    a * (k * c) * a⁻¹ * (k * c)⁻¹ = a * k * a⁻¹ * k⁻¹ := by
  have hca : c * a⁻¹ = a⁻¹ * c := by
    calc c * a⁻¹ = a⁻¹ * (a * c) * a⁻¹ := by group
      _ = a⁻¹ * (c * a) * a⁻¹ := by rw [hac]
      _ = a⁻¹ * c := by group
  calc a * (k * c) * a⁻¹ * (k * c)⁻¹ = a * k * (c * a⁻¹) * (c⁻¹ * k⁻¹) := by group
    _ = a * k * (a⁻¹ * c) * (c⁻¹ * k⁻¹) := by rw [hca]
    _ = a * k * a⁻¹ * k⁻¹ := by group

theorem commV_le_of_diag_invariant (h : DiagPre K K' Y t) (hZ : Subgroup.center ↥K = ⊥)
    {A : Subgroup V} (hA : GInv K A) {k : MulAut V} (hk : k ∈ K)
    (hy1 : k * (t * k * t⁻¹) ≠ 1) (hyA : ∀ v : V, (k * (t * k * t⁻¹)) v * v⁻¹ ∈ A) :
    commV K ≤ A := by
  have hk₀ : t * k * t⁻¹ ∈ K' := conj_mem_K' h hk
  have hy : k * (t * k * t⁻¹) ∈ actTrivMod A := hyA
  let N : Subgroup ↥K := (K ⊓ actTrivMod A).subgroupOf K
  have hNmem : ∀ n : ↥K, n ∈ N ↔ (n : MulAut V) ∈ actTrivMod A := fun n => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨n.2, h⟩⟩
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hNmem] at hn ⊢
    simpa using conj_mem_actTrivMod hA g.2 hn
  have hcomm : ∀ x : ↥K, (x : MulAut V) * k * (x : MulAut V)⁻¹ * k⁻¹ ∈ actTrivMod A := by
    intro x
    have h1 := conj_mem_actTrivMod hA x.2 hy
    have h3 := (actTrivMod A).mul_mem h1 ((actTrivMod A).inv_mem hy)
    rwa [commutator_mul_aux _ _ _ (h.comm x x.2 _ hk₀)] at h3
  rcases normal_le_center_or_eq_top h.quasi N with h1 | h1
  · exfalso
    apply hy1
    have hkc : (⟨k, hk⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hmem : ⁅x, (⟨k, hk⟩ : ↥K)⁆ ∈ N := (hNmem _).mpr (hcomm x)
      have h2 := h1 hmem
      rw [hZ, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2
    rw [hZ, Subgroup.mem_bot] at hkc
    have hk1 : k = 1 := congrArg Subtype.val hkc
    simp [hk1]
  · rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    have : (⟨x, hx⟩ : ↥K) ∈ N := by rw [h1]; trivial
    exact ((hNmem _).mp this) v

theorem exists_odd_order_ne_one {Y : Subgroup (MulAut V)} {n : ℕ} (hn : 1 ≤ n)
    (θ : ↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    ∃ y ∈ Y, y ≠ 1 ∧ Odd (orderOf y) := by
  have hcard : Nat.card ↥Y = 2 ^ n * (2 ^ (2 * n) - 1) := by
    rw [Nat.card_congr θ.toEquiv, card_sl2_fq hn]
  have h4 : 4 ≤ 2 ^ (2 * n) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq : 2 ^ (2 * n) - 1 ≠ 1 := by omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hq
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := by
    have h2 : 2 ∣ 2 ^ (2 * n) := dvd_pow_self 2 (by omega)
    have hoddq : Odd (2 ^ (2 * n) - 1) := Nat.odd_iff.mpr (by omega)
    exact hoddq.of_dvd_nat hpd
  have hpY : p ∣ Nat.card ↥Y := hcard ▸ Dvd.dvd.mul_left hpd _
  have : Finite ↥Y := Finite.of_equiv _ θ.toEquiv.symm
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpY
  refine ⟨(x : MulAut V), x.2, ?_, ?_⟩
  · intro h1
    have h2 : x = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hx
    exact hp.one_lt.ne hx
  · rw [Subgroup.orderOf_coe, hx]
    exact hodd

end CFSG.CGT.PushingUpLit.CGT6.Diag.Cons
