module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUp

variable {V : Type} [CommGroup V]

section Perm

variable {n : ℕ}

private theorem exists_stab_map (F : Finset (Fin n)) (hF : F.card + 4 ≤ n) {p q : Fin n}
    (hp : p ∉ F) (hq : q ∉ F) :
    ∃ u ∈ altStabilizer n F, (u : Equiv.Perm (Fin n)) p = q := by
  by_cases hpq : p = q
  · exact ⟨1, one_mem _, by simp [hpq]⟩
  · have h1 : (insert p (insert q F)).card ≤ F.card + 2 :=
      (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Finset.card_insert_le _ _))
    have hcard : 1 < (Finset.univ \ insert p (insert q F)).card := by
      rw [Finset.card_univ_sdiff, Fintype.card_fin]
      omega
    obtain ⟨r, hr, s, hs, hrs⟩ := Finset.one_lt_card.mp hcard
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, not_or] at hr hs
    refine ⟨⟨Equiv.swap p q * Equiv.swap r s, ?_⟩, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hpq,
        Equiv.Perm.sign_swap hrs, Int.units_mul_self]
    · rw [mem_altStabilizer_iff]
      intro i hi
      have hip : i ≠ p := fun h => hp (h ▸ hi)
      have hiq : i ≠ q := fun h => hq (h ▸ hi)
      have hir : i ≠ r := fun h => hr.2.2 (h ▸ hi)
      have his : i ≠ s := fun h => hs.2.2 (h ▸ hi)
      simp [Equiv.swap_apply_of_ne_of_ne, hip, hiq, hir, his]
    · simp [Equiv.swap_apply_of_ne_of_ne, Ne.symm hr.1, Ne.symm hs.1]

private theorem exists_mul_of_ne (hn : 6 ≤ n) {a b c : Fin n} (hac : a ≠ c) (hbc : b ≠ c)
    {s : alternatingGroup (Fin n)} (hs : s ∈ altStabilizer n {b})
    (hsc : (s : Equiv.Perm (Fin n)) c ≠ a) :
    ∃ u ∈ altStabilizer n {a, b}, ∃ w ∈ altStabilizer n {b, c}, s = u * w := by
  have hsb : (s : Equiv.Perm (Fin n)) b = b :=
    mem_altStabilizer_iff.mp hs b (Finset.mem_singleton_self b)
  have hse : (s : Equiv.Perm (Fin n)) c ≠ b := fun h => hbc (s.1.injective (h.trans hsb.symm)).symm
  have h2 : ({a, b} : Finset (Fin n)).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  obtain ⟨u, hu, huc⟩ := exists_stab_map {a, b} (by omega) (p := (s : Equiv.Perm (Fin n)) c)
    (q := c) (by simp [hsc, hse]) (by simp [Ne.symm hac, Ne.symm hbc])
  refine ⟨u⁻¹, inv_mem hu, u * s, ?_, (inv_mul_cancel_left u s).symm⟩
  rw [mem_altStabilizer_iff]
  intro i hi
  have hub : (u : Equiv.Perm (Fin n)) b = b := mem_altStabilizer_iff.mp hu b (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with h | h
  · rw [h]
    simp [hsb, hub]
  · rw [h]
    simp [huc]

private theorem exists_double_coset (hn : 6 ≤ n) {a b c : Fin n} (hac : a ≠ c) (hbc : b ≠ c)
    {s : alternatingGroup (Fin n)} (hs : s ∈ altStabilizer n {b}) :
    ∃ u1 ∈ altStabilizer n {a, b}, ∃ w ∈ altStabilizer n {b, c}, ∃ u2 ∈ altStabilizer n {a, b},
      s = u1 * w * u2 := by
  by_cases hsc : (s : Equiv.Perm (Fin n)) c = a
  · have hT : ({a, b, c} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have : ({a, b, c} : Finset (Fin n)).card ≤ 3 :=
        (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
          (by simp)))
      omega
    obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hT
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
    have h2 : ({a, b} : Finset (Fin n)).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    obtain ⟨v, hv, hvc⟩ := exists_stab_map {a, b} (by omega) (p := c) (q := d)
      (by simp [Ne.symm hac, Ne.symm hbc]) (by simp [hd.1, hd.2.1])
    have hvb : (v : Equiv.Perm (Fin n)) b = b := mem_altStabilizer_iff.mp hv b (by simp)
    have hsb : (s : Equiv.Perm (Fin n)) b = b :=
      mem_altStabilizer_iff.mp hs b (Finset.mem_singleton_self b)
    have hsv : s * v ∈ altStabilizer n {b} := by
      rw [mem_altStabilizer_iff]
      intro i hi
      rw [Finset.mem_singleton] at hi
      rw [hi]
      simp [hsb, hvb]
    have hne : ((s * v : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) c ≠ a := by
      intro h
      simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hvc] at h
      exact hd.2.2 (s.1.injective (h.trans hsc.symm))
    obtain ⟨u, hu, w, hw, h⟩ := exists_mul_of_ne hn hac hbc hsv hne
    refine ⟨u, hu, w, hw, v⁻¹, inv_mem hv, ?_⟩
    rw [← h]
    group
  · obtain ⟨u, hu, w, hw, h⟩ := exists_mul_of_ne hn hac hbc hs hsc
    exact ⟨u, hu, w, hw, 1, one_mem _, by simp [h]⟩

private theorem exists_generate (hn : 5 ≤ n) {b c : Fin n} (hbc : b ≠ c)
    {ρ : alternatingGroup (Fin n)} (hρ : (ρ : Equiv.Perm (Fin n)) b = c)
    (s : alternatingGroup (Fin n)) :
    s ∈ altStabilizer n {b} ∨
      ∃ u ∈ altStabilizer n {b}, ∃ v ∈ altStabilizer n {b}, s = u * ρ * v := by
  by_cases hsb : (s : Equiv.Perm (Fin n)) b = b
  · left
    rw [mem_altStabilizer_iff]
    simpa using hsb
  · right
    obtain ⟨u, hu, huc⟩ := exists_stab_map {b} (by simp; omega) (p := (s : Equiv.Perm (Fin n)) b)
      (q := c) (by simpa using hsb) (by simpa using Ne.symm hbc)
    refine ⟨u⁻¹, inv_mem hu, ρ⁻¹ * (u * s), ?_, by group⟩
    rw [mem_altStabilizer_iff]
    intro i hi
    rw [Finset.mem_singleton] at hi
    rw [hi]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, huc]
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hρ.symm

private theorem exists_rho {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ ρ : alternatingGroup (Fin n), (ρ : Equiv.Perm (Fin n)).IsThreeCycle ∧
      (ρ : Equiv.Perm (Fin n)) a = b ∧ (ρ : Equiv.Perm (Fin n)) b = c ∧
      (ρ : Equiv.Perm (Fin n)) c = a ∧
      ∀ s : alternatingGroup (Fin n),
        (s : Equiv.Perm (Fin n)) a = a → (s : Equiv.Perm (Fin n)) b = b →
        (s : Equiv.Perm (Fin n)) c = c → s * ρ = ρ * s := by
  have h3 : (Equiv.swap a c * Equiv.swap a b).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hac hab (Ne.symm hbc)
  refine ⟨⟨_, h3.mem_alternatingGroup⟩, h3, ?_, ?_, ?_, ?_⟩
  · simp [Equiv.swap_apply_of_ne_of_ne, Ne.symm hab, hbc]
  · simp
  · simp [Equiv.swap_apply_of_ne_of_ne, Ne.symm hac, Ne.symm hbc]
  · intro s hsa hsb hsc
    apply Subtype.ext
    have e1 : (s : Equiv.Perm (Fin n)) * Equiv.swap a c = Equiv.swap a c * s := by
      rw [Equiv.mul_swap_eq_swap_mul, hsa, hsc]
    have e2 : (s : Equiv.Perm (Fin n)) * Equiv.swap a b = Equiv.swap a b * s := by
      rw [Equiv.mul_swap_eq_swap_mul, hsa, hsb]
    simp only [Subgroup.coe_mul]
    rw [← mul_assoc, e1, mul_assoc, e2, ← mul_assoc]

private theorem exists_threeCycle_alt {m : ℕ} (hm : 3 ≤ m) :
    ∃ τ : alternatingGroup (Fin m), (τ : Equiv.Perm (Fin m)).IsThreeCycle := by
  have h3 : (Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ *
      Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨2, by omega⟩).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (Fin.ne_of_val_ne (by simp))
      (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))
  exact ⟨⟨_, h3.mem_alternatingGroup⟩, h3⟩

end Perm

section Transport

variable {n : ℕ}

private theorem incl_equiv (F : Finset (Fin n)) (σ : altStabilizer n F) :
    altStabIncl F (altStabilizerEquiv F σ) = (σ : alternatingGroup (Fin n)) :=
  MonoidHom.apply_ofInjective_symm (altStabIncl_injective F) _

private theorem incl_apply_compl {F : Finset (Fin n)} (τ : alternatingGroup (Fin (n - F.card)))
    (j : Fin (n - F.card)) :
    (altStabIncl F τ : Equiv.Perm (Fin n)) ((complEquiv F j : {i : Fin n // i ∉ F}) : Fin n) =
      ((complEquiv F ((τ : Equiv.Perm (Fin (n - F.card))) j) : {i : Fin n // i ∉ F}) : Fin n) := by
  rw [altStabIncl_apply,
    Equiv.Perm.ofSubtype_apply_of_mem (p := fun i : Fin n => i ∉ F) _ (complEquiv F j).2]
  simp [Equiv.permCongr_apply]

private theorem incl_mem_iff {F : Finset (Fin n)} (c : Fin (n - F.card))
    (τ : alternatingGroup (Fin (n - F.card))) :
    altStabIncl F τ ∈ altStabilizer n (insert (complEquiv F c : Fin n) F) ↔
      τ ∈ altStabilizer (n - F.card) {c} := by
  rw [mem_altStabilizer_iff, mem_altStabilizer_iff]
  constructor
  · intro h i hi
    rw [Finset.mem_singleton] at hi
    rw [hi]
    have h1 := h _ (Finset.mem_insert_self _ _)
    rw [incl_apply_compl] at h1
    exact (complEquiv F).injective (Subtype.ext h1)
  · intro h i hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · rw [hi, incl_apply_compl, h c (Finset.mem_singleton_self c)]
    · have hr : altStabIncl F τ ∈ altStabilizer n F := by
        rw [← altStabIncl_range]
        exact ⟨τ, rfl⟩
      exact mem_altStabilizer_iff.mp hr i hi

private theorem isThreeCycle_incl {F : Finset (Fin n)} {τ : alternatingGroup (Fin (n - F.card))}
    (h : (τ : Equiv.Perm (Fin (n - F.card))).IsThreeCycle) :
    (altStabIncl F τ : Equiv.Perm (Fin n)).IsThreeCycle := by
  have h1 : Equiv.Perm.ofSubtype ((complEquiv F).permCongr (τ : Equiv.Perm (Fin (n - F.card)))) =
      (τ : Equiv.Perm (Fin (n - F.card))).extendDomain (complEquiv F) := rfl
  rw [altStabIncl_apply, h1]
  unfold Equiv.Perm.IsThreeCycle at h ⊢
  rw [Equiv.Perm.cycleType_extendDomain]
  exact h

section Group

variable {G : Type*} [Group G]

private noncomputable def stabEquiv {L K : Subgroup G} (θ : L ≃* alternatingGroup (Fin n))
    (hKL : K ≤ L) {F : Finset (Fin n)}
    (hK : (K.subgroupOf L).map θ.toMonoidHom = altStabilizer n F) :
    K ≃* alternatingGroup (Fin (n - F.card)) :=
  (((Subgroup.subgroupOfEquivOfLe hKL).symm.trans (MulEquiv.subgroupMap θ (K.subgroupOf L))).trans
    (MulEquiv.subgroupCongr hK)).trans (altStabilizerEquiv F)

private theorem incl_stabEquiv {L K : Subgroup G} (θ : L ≃* alternatingGroup (Fin n))
    (hKL : K ≤ L) {F : Finset (Fin n)}
    (hK : (K.subgroupOf L).map θ.toMonoidHom = altStabilizer n F) (y : K) :
    altStabIncl F (stabEquiv θ hKL hK y) = θ ⟨(y : G), hKL y.2⟩ :=
  incl_equiv F _

private theorem mem_iff_of_map {L K : Subgroup G} (θ : L ≃* alternatingGroup (Fin n))
    {S : Subgroup (alternatingGroup (Fin n))} (hK : (K.subgroupOf L).map θ.toMonoidHom = S)
    (l : L) : (l : G) ∈ K ↔ θ l ∈ S := by
  rw [← hK]
  constructor
  · intro h
    exact ⟨l, h, rfl⟩
  · rintro ⟨l', hl', he⟩
    rw [← θ.injective he]
    exact hl'

end Group

end Transport

private theorem setup_aux {n m : ℕ} (hn : 6 ≤ n) {L K : Subgroup (MulAut V)}
    (θ : L ≃* alternatingGroup (Fin n)) {a b : Fin n} (hab : a ≠ b) {F : Finset (Fin n)}
    (hF : F = {a, b}) (hKL : K ≤ L)
    (hK : (K.subgroupOf L).map θ.toMonoidHom = altStabilizer n F) (hm : m = n - F.card) :
    ∃ (θK : K ≃* alternatingGroup (Fin m)) (x y' g : MulAut V) (N : Subgroup (MulAut V))
      (c : Fin m) (hy' : y' ∈ K),
      x ∈ L ∧ g ∈ L ∧ x ^ 3 = 1 ∧ N ≤ K ∧
      (N.subgroupOf K).map θK.toMonoidHom = altStabilizer m {c} ∧
      (∀ y ∈ N, x * y = y * x) ∧
      ((θK ⟨y', hy'⟩ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)).IsThreeCycle ∧
      x = g * y' * g⁻¹ ∧ K ⊔ Subgroup.zpowers x = L ∧
      (∀ z : L, θ z ∈ altStabilizer n {b} →
        (z : MulAut V) ∈ K ⊔ K.map (MulAut.conj x).toMonoidHom) ∧
      ∃ c0 : Fin n, c0 ≠ a ∧ c0 ≠ b ∧ ∃ hx : x ∈ L,
        ((θ ⟨x, hx⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).IsThreeCycle ∧
        ((θ ⟨x, hx⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) a = b ∧
        ((θ ⟨x, hx⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) b = c0 ∧
        ((θ ⟨x, hx⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) c0 = a := by
  subst hm
  have haF : a ∈ F := by rw [hF]; simp
  have hbF : b ∈ F := by rw [hF]; simp
  have hFc : F.card ≤ 2 := by rw [hF]; exact (Finset.card_insert_le _ _).trans (by simp)
  have hmem : ∀ σ : alternatingGroup (Fin n), σ ∈ altStabilizer n F ↔
      (σ : Equiv.Perm (Fin n)) a = a ∧ (σ : Equiv.Perm (Fin n)) b = b := by
    intro σ
    rw [mem_altStabilizer_iff, hF]
    simp
  obtain ⟨c, -⟩ : ∃ c : Fin (n - F.card), True := ⟨⟨0, by omega⟩, trivial⟩
  obtain ⟨c0, hc0F, hc0⟩ : ∃ c0 : Fin n, c0 ∉ F ∧ c0 = (complEquiv F c : Fin n) :=
    ⟨_, (complEquiv F c).2, rfl⟩
  have hNiff : ∀ τ : alternatingGroup (Fin (n - F.card)),
      altStabIncl F τ ∈ altStabilizer n (insert c0 F) ↔
        τ ∈ altStabilizer (n - F.card) {c} := by
    intro τ
    rw [hc0]
    exact incl_mem_iff c τ
  have hac : a ≠ c0 := fun h => hc0F (h ▸ haF)
  have hbc : b ≠ c0 := fun h => hc0F (h ▸ hbF)
  obtain ⟨ρ, hρ3, hρa, hρb, hρc, hρcomm⟩ := exists_rho hab hac hbc
  have hKc : ∀ l : L, (l : MulAut V) ∈ K ↔ θ l ∈ altStabilizer n F := mem_iff_of_map θ hK
  obtain ⟨θK, hθK⟩ : ∃ θK : K ≃* alternatingGroup (Fin (n - F.card)),
      ∀ y : K, altStabIncl F (θK y) = θ ⟨(y : MulAut V), hKL y.2⟩ :=
    ⟨stabEquiv θ hKL hK, incl_stabEquiv θ hKL hK⟩
  obtain ⟨xL, hxL⟩ := θ.surjective ρ
  obtain ⟨τ0, hτ0⟩ := exists_threeCycle_alt (m := n - F.card) (by omega)
  obtain ⟨y0, hy0⟩ := θK.surjective τ0
  have hy0L : (y0 : MulAut V) ∈ L := hKL y0.2
  have hθy0 : θ ⟨(y0 : MulAut V), hy0L⟩ = altStabIncl F τ0 := by
    rw [← hy0, hθK]
  obtain ⟨γ, hγ⟩ : ∃ γ : alternatingGroup (Fin n),
      γ * θ ⟨(y0 : MulAut V), hy0L⟩ * γ⁻¹ = ρ := by
    have h5 : 5 ≤ Nat.card (Fin n) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    have h1 : IsConj (θ ⟨(y0 : MulAut V), hy0L⟩) ρ := by
      refine alternatingGroup.isThreeCycle_isConj h5 ?_ hρ3
      rw [hθy0]
      exact isThreeCycle_incl hτ0
    exact isConj_iff.mp h1
  obtain ⟨gL, hgL⟩ := θ.surjective γ
  have hxe : xL = gL * ⟨(y0 : MulAut V), hy0L⟩ * gL⁻¹ :=
    θ.injective (by rw [map_mul, map_mul, map_inv, hxL, hgL, hγ])
  have hρ3' : ρ ^ 3 = 1 := by
    apply Subtype.ext
    have h1 := pow_orderOf_eq_one (ρ : Equiv.Perm (Fin n))
    rwa [hρ3.orderOf] at h1
  have hx3 : (xL : MulAut V) ^ 3 = 1 := by
    have h1 : xL ^ 3 = 1 := θ.injective (by rw [map_pow, hxL, hρ3', map_one])
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  obtain ⟨N, hN⟩ : ∃ N : Subgroup (MulAut V), ∀ y : MulAut V,
      y ∈ N ↔ ∃ hy : y ∈ L, θ ⟨y, hy⟩ ∈ altStabilizer n (insert c0 F) :=
    ⟨((altStabilizer n (insert c0 F)).comap θ.toMonoidHom).map L.subtype, fun y => by
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨l.2, hl⟩
      · rintro ⟨hy, h⟩
        exact ⟨⟨y, hy⟩, h, rfl⟩⟩
  have hNK : N ≤ K := by
    intro y hy
    obtain ⟨hyL, hθ⟩ := (hN y).mp hy
    refine (hKc ⟨y, hyL⟩).mpr (mem_altStabilizer_iff.mpr fun i hi => ?_)
    exact mem_altStabilizer_iff.mp hθ i (Finset.mem_insert_of_mem hi)
  have hNimage : (N.subgroupOf K).map θK.toMonoidHom = altStabilizer (n - F.card) {c} := by
    ext τ
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyL, hθ⟩ := (hN y).mp (Subgroup.mem_subgroupOf.mp hy)
      rw [← hθK y] at hθ
      exact (hNiff _).mp hθ
    · intro hτ
      obtain ⟨y, hy⟩ := θK.surjective τ
      refine ⟨y, Subgroup.mem_subgroupOf.mpr ((hN _).mpr ⟨hKL y.2, ?_⟩), hy⟩
      rw [← hθK y, hy]
      exact (hNiff τ).mpr hτ
  have hcomm : ∀ y ∈ N, (xL : MulAut V) * y = y * (xL : MulAut V) := by
    intro y hy
    obtain ⟨hyL, hθ⟩ := (hN y).mp hy
    have ha := mem_altStabilizer_iff.mp hθ a (Finset.mem_insert_of_mem haF)
    have hb := mem_altStabilizer_iff.mp hθ b (Finset.mem_insert_of_mem hbF)
    have hc := mem_altStabilizer_iff.mp hθ c0 (Finset.mem_insert_self _ _)
    have h1 : xL * ⟨y, hyL⟩ = ⟨y, hyL⟩ * xL :=
      θ.injective (by rw [map_mul, map_mul, hxL]; exact (hρcomm _ ha hb hc).symm)
    exact congrArg Subtype.val h1
  have hconjK : ∀ u : alternatingGroup (Fin n), u ∈ altStabilizer n F →
      ∃ uL : L, θ uL = u ∧ (uL : MulAut V) ∈ K := by
    intro u hu
    obtain ⟨uL, huL⟩ := θ.surjective u
    exact ⟨uL, huL, (hKc uL).mpr (by rw [huL]; exact hu)⟩
  have hconjQ : ∀ w : alternatingGroup (Fin n), w ∈ altStabilizer n {b, c0} →
      ∃ wL : L, θ wL = w ∧
        (wL : MulAut V) ∈ K.map (MulAut.conj (xL : MulAut V)).toMonoidHom := by
    intro w hw
    have hwb : (w : Equiv.Perm (Fin n)) b = b := mem_altStabilizer_iff.mp hw b (by simp)
    have hwc : (w : Equiv.Perm (Fin n)) c0 = c0 := mem_altStabilizer_iff.mp hw c0 (by simp)
    have hw' : ρ⁻¹ * w * ρ ∈ altStabilizer n F := by
      rw [hmem]
      constructor
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hρa, hwb]
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact hρa.symm
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hρb, hwc]
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact hρb.symm
    obtain ⟨w'L, hw'L, hw'K⟩ := hconjK _ hw'
    refine ⟨xL * w'L * xL⁻¹, ?_, ⟨(w'L : MulAut V), hw'K, ?_⟩⟩
    · rw [map_mul, map_mul, map_inv, hxL, hw'L]
      group
    · simp [MulAut.conj_apply]
  have hlast : ∀ z : L, θ z ∈ altStabilizer n {b} →
      (z : MulAut V) ∈ K ⊔ K.map (MulAut.conj (xL : MulAut V)).toMonoidHom := by
    intro z hz
    obtain ⟨u1, hu1, w, hw, u2, hu2, he⟩ := exists_double_coset hn hac hbc hz
    rw [← hF] at hu1 hu2
    obtain ⟨u1L, hu1L, hu1K⟩ := hconjK u1 hu1
    obtain ⟨u2L, hu2L, hu2K⟩ := hconjK u2 hu2
    obtain ⟨wL, hwL, hwK⟩ := hconjQ w hw
    have hz' : z = u1L * wL * u2L :=
      θ.injective (by rw [map_mul, map_mul, hu1L, hwL, hu2L, ← he])
    rw [hz']
    simp only [Subgroup.coe_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hu1K)
      (Subgroup.mem_sup_right hwK)) (Subgroup.mem_sup_left hu2K)
  have hgen : K ⊔ Subgroup.zpowers (xL : MulAut V) = L := by
    have hx : (xL : MulAut V) ∈ K ⊔ Subgroup.zpowers (xL : MulAut V) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hKx : K ⊔ K.map (MulAut.conj (xL : MulAut V)).toMonoidHom ≤
        K ⊔ Subgroup.zpowers (xL : MulAut V) := by
      refine sup_le le_sup_left ?_
      rintro _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx (Subgroup.mem_sup_left hy))
        (Subgroup.inv_mem _ hx)
    refine le_antisymm (sup_le hKL (by rw [Subgroup.zpowers_le]; exact xL.2)) (fun z hz => ?_)
    rcases exists_generate (by omega : 5 ≤ n) hbc hρb (θ ⟨z, hz⟩) with h | ⟨u, hu, v, hv, he⟩
    · exact hKx (hlast ⟨z, hz⟩ h)
    · obtain ⟨uL, huL⟩ := θ.surjective u
      obtain ⟨vL, hvL⟩ := θ.surjective v
      have hz' : (⟨z, hz⟩ : L) = uL * xL * vL :=
        θ.injective (by rw [map_mul, map_mul, huL, hxL, hvL, ← he])
      have h1 := congrArg Subtype.val hz'
      simp only [Subgroup.coe_mul] at h1
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hKx (hlast uL (by rw [huL]; exact hu))) hx)
        (hKx (hlast vL (by rw [hvL]; exact hv)))
  refine ⟨θK, (xL : MulAut V), (y0 : MulAut V), (gL : MulAut V), N, c, y0.2, xL.2, gL.2, hx3, hNK,
    hNimage, hcomm, ?_, ?_, hgen, hlast, c0, hac.symm, hbc.symm, xL.2, ?_⟩
  · show ((θK y0 : alternatingGroup (Fin (n - F.card))) :
      Equiv.Perm (Fin (n - F.card))).IsThreeCycle
    rw [hy0]
    exact hτ0
  · have h1 := congrArg Subtype.val hxe
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  · have hxL' : θ ⟨(xL : MulAut V), xL.2⟩ = ρ := hxL
    rw [hxL']
    exact ⟨hρ3, hρa, hρb, hρc⟩

theorem exists_threeCycle_setup {k : ℕ} (hk : 5 ≤ k) {L K : Subgroup (MulAut V)}
    (θ : L ≃* alternatingGroup (Fin (k + 2))) {a b : Fin (k + 2)} (hab : a ≠ b) (hKL : K ≤ L)
    (hK : (K.subgroupOf L).map θ.toMonoidHom = altStabilizer (k + 2) {a, b}) :
    ∃ (θK : K ≃* alternatingGroup (Fin k)) (x y' g : MulAut V) (N : Subgroup (MulAut V))
      (c : Fin k) (hy' : y' ∈ K),
      x ∈ L ∧ g ∈ L ∧ x ^ 3 = 1 ∧ N ≤ K ∧
      (N.subgroupOf K).map θK.toMonoidHom = altStabilizer k {c} ∧
      (∀ y ∈ N, x * y = y * x) ∧
      ((θK ⟨y', hy'⟩ : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)).IsThreeCycle ∧
      x = g * y' * g⁻¹ ∧ K ⊔ Subgroup.zpowers x = L ∧
      (∀ z : L, θ z ∈ altStabilizer (k + 2) {b} →
        (z : MulAut V) ∈ K ⊔ K.map (MulAut.conj x).toMonoidHom) ∧
      ∃ c0 : Fin (k + 2), c0 ≠ a ∧ c0 ≠ b ∧ ∃ hx : x ∈ L,
        ((θ ⟨x, hx⟩ : alternatingGroup (Fin (k + 2))) : Equiv.Perm (Fin (k + 2))).IsThreeCycle ∧
        ((θ ⟨x, hx⟩ : alternatingGroup (Fin (k + 2))) : Equiv.Perm (Fin (k + 2))) a = b ∧
        ((θ ⟨x, hx⟩ : alternatingGroup (Fin (k + 2))) : Equiv.Perm (Fin (k + 2))) b = c0 ∧
        ((θ ⟨x, hx⟩ : alternatingGroup (Fin (k + 2))) : Equiv.Perm (Fin (k + 2))) c0 = a := by
  have h2 : ({a, b} : Finset (Fin (k + 2))).card = 2 := Finset.card_pair hab
  exact setup_aux (m := k) (by omega) θ hab rfl hKL hK (by rw [h2]; omega)

end CFSG.CGT.PushingUpLit.CGT6
