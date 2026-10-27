module

import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

structure Setting (L E : Subgroup G) (t z : G) : Prop where
  htL : t ∈ centralizer (L : Set G)
  ht2 : orderOf t = 2
  hin : centralizer ({t} : Set G) = L ⊔ zpowers t
  hLC : L ⊓ centralizer (L : Set G) = ⊥
  hEL : E ≤ L
  hEab : IsElemAbelian 2 E
  hE16 : Nat.card E = 16
  hzE : z ∈ E
  hCE : centralizer (E : Set G) ⊓ L = E
  hNE : Nat.card (normalizer (E : Set G) ⊓ L : Subgroup G) = 11520
  htrans : ∀ e ∈ E, e ≠ 1 → ∃ a ∈ normalizer (E : Set G) ⊓ L, a * z * a⁻¹ = e
  hzt : ∀ g : G, g * t * g⁻¹ ≠ z
  hfus : ∀ e ∈ E, ∃ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G), m * t * m⁻¹ = t * e

abbrev Ns (t : G) (E : Subgroup G) : Subgroup G :=
  normalizer ((zpowers t ⊔ E : Subgroup G) : Set G)

abbrev N0s (t : G) (E : Subgroup G) : Subgroup G :=
  normalizer ((zpowers t ⊔ E : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G)

abbrev Ks (t : G) (E : Subgroup G) : Subgroup G :=
  normalizer ((zpowers t ⊔ E : Subgroup G) : Set G) ⊓ centralizer (E : Set G)

theorem mem_sup_zpowers_iff {H : Subgroup G} {t : G} (htt : t * t = 1)
    (hH : ∀ h ∈ H, h * t = t * h) {x : G} :
    x ∈ H ⊔ zpowers t ↔ ∃ h ∈ H, x = h ∨ x = h * t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ h ∈ H, x = h ∨ x = h * t}
        one_mem' := ⟨1, H.one_mem, Or.inl rfl⟩
        mul_mem' := by
          rintro x y ⟨a, ha, h1 | h1⟩ ⟨b, hb, h2 | h2⟩ <;> subst x y
          · exact ⟨a * b, H.mul_mem ha hb, Or.inl rfl⟩
          · exact ⟨a * b, H.mul_mem ha hb, Or.inr (by rw [mul_assoc])⟩
          · refine ⟨a * b, H.mul_mem ha hb, Or.inr ?_⟩
            rw [mul_assoc, ← hH b hb, ← mul_assoc]
          · refine ⟨a * b, H.mul_mem ha hb, Or.inl ?_⟩
            calc a * t * (b * t) = a * (t * b) * t := by simp only [mul_assoc]
              _ = a * (b * t) * t := by rw [hH b hb]
              _ = a * b * (t * t) := by simp only [mul_assoc]
              _ = a * b := by rw [htt, mul_one]
        inv_mem' := by
          rintro x ⟨a, ha, h1 | h1⟩ <;> subst x
          · exact ⟨a⁻¹, H.inv_mem ha, Or.inl rfl⟩
          · refine ⟨a⁻¹, H.inv_mem ha, Or.inr ?_⟩
            rw [mul_inv_rev, htinv]
            exact (Commute.inv_left (show Commute a t from hH a ha)).eq.symm }
    have hle : H ⊔ zpowers t ≤ S := by
      refine sup_le (fun h hh => ⟨h, hh, Or.inl rfl⟩) ?_
      rw [zpowers_le]
      exact ⟨1, H.one_mem, Or.inr (one_mul t).symm⟩
    exact hle hx
  · rintro ⟨h, hh, rfl | rfl⟩
    · exact mem_sup_left hh
    · exact mul_mem (mem_sup_left hh) (mem_sup_right (mem_zpowers t))

theorem card_sup_zpowers {H : Subgroup G} {t : G} (ht2 : orderOf t = 2) (htH : t ∉ H)
    (hH : ∀ h ∈ H, h * t = t * h) : Nat.card ↥(H ⊔ zpowers t) = 2 * Nat.card H := by
  have hcent : zpowers t ≤ centralizer (H : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun h hh => hH h hh
  have hdisj : Disjoint H (zpowers t) := by
    rw [Subgroup.disjoint_def]
    intro y hyK hyx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hyx
    have hn : t ^ n = 1 ∨ t ^ n = t := by
      rw [← zpow_mod_orderOf, ht2]
      rcases Int.emod_two_eq_zero_or_one n with h | h <;> simp [h]
    rcases hn with h | h
    · exact h
    · exact absurd (h ▸ hyK) htH
  rw [← Nat.card_congr (mulEquivProdSup hcent hdisj).toEquiv, Nat.card_prod, Nat.card_zpowers,
    ht2]
  exact mul_comm _ _

@[expose] def conjAut (E M : Subgroup G) (hM : M ≤ normalizer (E : Set G)) : ↥M →* MulAut ↥E where
  toFun m :=
    { toFun := fun e => ⟨m * e * m⁻¹, (mem_normalizer_iff.1 (hM m.2) e).1 e.2⟩
      invFun := fun e => ⟨m⁻¹ * e * m, by
        have := (mem_normalizer_iff.1 (hM (M.inv_mem m.2)) e).1 e.2
        simpa using this⟩
      left_inv := fun e => Subtype.ext (by simp [mul_assoc])
      right_inv := fun e => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

theorem card_mulAut_of_exp_two {A : Type*} [Group A] (hcomm : ∀ a b : A, a * b = b * a)
    (hsq : ∀ x : A, x * x = 1) (hc : Nat.card A = 16) : Nat.card (MulAut A) = 20160 := by
  let _ : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have h2 : ∀ x : Additive A, (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul]
    apply Additive.toMul.injective
    simp only [toMul_add, toMul_zero]
    exact hsq x.toMul
  let _ : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule h2
  have : Finite (Additive A) := hfin
  have hrank : Module.finrank (ZMod 2) (Additive A) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    have h' : Nat.card (Additive A) = 16 := hc
    rw [h', Nat.card_zmod] at h
    have : (2:ℕ) ^ 4 = 2 ^ Module.finrank (ZMod 2) (Additive A) := by rw [← h]; norm_num
    exact (Nat.pow_right_injective (le_refl 2) this).symm
  have e : Additive A ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hrank]; simp)
  have h1 : Nat.card (MulAut A) = Nat.card (Additive A ≃+ Additive A) :=
    Nat.card_congr MulEquiv.toAdditive
  have h3 : Nat.card (Additive A ≃+ Additive A) = Nat.card (Additive A ≃ₗ[ZMod 2] Additive A) :=
    Nat.card_congr
      { toFun := fun f => (AddEquiv.toLinearEquiv f (fun c x => ZMod.map_smul f.toAddMonoidHom c x))
        invFun := fun f => f.toAddEquiv
        left_inv := fun f => rfl
        right_inv := fun f => rfl }
  have h4 : Nat.card (Additive A ≃ₗ[ZMod 2] Additive A) =
      Nat.card ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :=
    Nat.card_congr
      { toFun := fun f => e.symm.trans (f.trans e)
        invFun := fun g => e.trans (g.trans e.symm)
        left_inv := fun f => by ext; simp
        right_inv := fun g => by ext; simp }
  have h5 : Nat.card ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) =
      Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :=
    Nat.card_congr
      ((Matrix.GeneralLinearGroup.toLin.trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 4 → ZMod 2))).toEquiv).symm
  rw [h1, h3, h4, h5, Matrix.card_GL_field]
  simp [Fin.prod_univ_four]

theorem card_mulAut_elemAbelian {H : Subgroup G} (hH : IsElemAbelian 2 H) (hc : Nat.card H = 16) :
    Nat.card (MulAut ↥H) = 20160 := by
  have hcomm := hH.1
  rw [isMulCommutative_iff_of_setLike] at hcomm
  refine card_mulAut_of_exp_two (A := ↥H) (fun a b => Subtype.ext (hcomm a a.2 b b.2))
    (fun x => Subtype.ext ?_) hc
  have := hH.2 x x.2
  simpa [pow_two] using this

theorem card_modEq_centralizer {p : ℕ} [Fact p.Prime] {Q D : Subgroup G} (hQ : IsPGroup p Q)
    [Finite D] (hQD : ∀ q ∈ Q, ∀ d ∈ D, q * d * q⁻¹ ∈ D) :
    Nat.card D ≡ Nat.card ↥(D ⊓ centralizer (Q : Set G)) [MOD p] := by
  have hle : Q ≤ normalizer (D : Set G) := by
    intro q hq
    rw [mem_normalizer_iff]
    intro d
    refine ⟨hQD q hq d, fun h => ?_⟩
    have := hQD q⁻¹ (Q.inv_mem hq) _ h
    simpa [mul_assoc] using this
  let _ : MulAction ↥Q ↥D := MulAction.compHom ↥D (conjAut D Q hle)
  have h := hQ.card_modEq_card_fixedPoints (α := ↥D)
  have hsm : ∀ (q : ↥Q) (d : ↥D), ((q • d : ↥D) : G) = q * d * (q : G)⁻¹ := fun q d => rfl
  have e : ↥(MulAction.fixedPoints ↥Q ↥D) ≃ ↥(D ⊓ centralizer (Q : Set G)) :=
    { toFun := fun x => ⟨x.1.1, mem_inf.2 ⟨x.1.2, mem_centralizer_iff.2 fun q hq => by
        have hx := x.2 ⟨q, hq⟩
        have := congrArg Subtype.val hx
        rw [hsm] at this
        exact mul_inv_eq_iff_eq_mul.1 this⟩⟩
      invFun := fun x => ⟨⟨x.1, (mem_inf.1 x.2).1⟩, fun q => by
        apply Subtype.ext
        rw [hsm]
        have := mem_centralizer_iff.1 (mem_inf.1 x.2).2 q q.2
        exact mul_inv_eq_iff_eq_mul.2 this⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rwa [Nat.card_congr e] at h

theorem eq_one_or_sixteen {n : ℕ} (hd : n ∣ 16) (hm : n ≡ 1 [MOD 5]) : n = 1 ∨ n = 16 := by
  have hle : n ≤ 16 := Nat.le_of_dvd (by norm_num) hd
  interval_cases n <;> simp_all [Nat.ModEq]

theorem eq_sixteen_of_even {n : ℕ} (hd : n ∣ 16) (hm : n ≡ 1 [MOD 5]) (he : 2 ∣ n) : n = 16 := by
  rcases eq_one_or_sixteen hd hm with h | h
  · omega
  · exact h

theorem mem_centralizer_zpowers_iff {y e : G} :
    e ∈ centralizer (zpowers y : Set G) ↔ y * e = e * y := by
  constructor
  · intro h
    exact mem_centralizer_iff.1 h y (mem_zpowers y)
  · intro h
    refine mem_centralizer_iff.2 fun q hq => ?_
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hq
    exact (Commute.zpow_left (show Commute y e from h) n).eq

theorem isPGroup_zpowers {y : G} (hy : orderOf y = 5) : IsPGroup 5 (zpowers y) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])

@[expose] def Ostar (H : Subgroup G) : Subgroup G := closure {x | x ∈ H ∧ Odd (orderOf x)}

@[expose] def O2 (H : Subgroup G) : Subgroup G :=
  sSup {P : Subgroup G | P ≤ H ∧ IsPGroup 2 P ∧ ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P}

@[expose] def Opp2 (H : Subgroup G) : Subgroup G := O2 (Ostar H)

theorem Ostar_le (H : Subgroup G) : Ostar H ≤ H := (closure_le _).2 fun _ hx => hx.1

theorem Ostar_conj {H : Subgroup G} {n x : G} (hn : n ∈ H) (hx : x ∈ Ostar H) :
    n * x * n⁻¹ ∈ Ostar H := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    refine subset_closure ⟨H.mul_mem (H.mul_mem hn hx.1) (H.inv_mem hn), ?_⟩
    have : orderOf (MulAut.conj n x) = orderOf x := MulEquiv.orderOf_eq _ _
    simpa using this ▸ hx.2
  | one => simp
  | mul x y _ _ hx hy =>
    have : n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

namespace Setting

variable {L E : Subgroup G} {t z : G}

theorem tt (hs : Setting L E t z) : t * t = 1 := by
  have h := pow_orderOf_eq_one t
  rw [hs.ht2, pow_two] at h
  exact h

theorem t_comm (hs : Setting L E t z) {l : G} (hl : l ∈ L) : l * t = t * l :=
  mem_centralizer_iff.1 hs.htL l hl

theorem t_comm_E (hs : Setting L E t z) {e : G} (he : e ∈ E) : e * t = t * e :=
  hs.t_comm (hs.hEL he)

theorem E_comm (hs : Setting L E t z) {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  have := hs.hEab.1
  rw [isMulCommutative_iff_of_setLike] at this
  exact this a ha b hb

theorem t_not_mem_L (hs : Setting L E t z) : t ∉ L := by
  intro h
  have h1 : t ∈ L ⊓ centralizer (L : Set G) := ⟨h, hs.htL⟩
  rw [hs.hLC, Subgroup.mem_bot] at h1
  have := hs.ht2
  rw [h1, orderOf_one] at this
  omega

theorem t_not_mem_E (hs : Setting L E t z) : t ∉ E := fun h => hs.t_not_mem_L (hs.hEL h)

theorem t_mem_X (t : G) (E : Subgroup G) : t ∈ zpowers t ⊔ E := mem_sup_left (mem_zpowers t)

theorem mem_X_iff (hs : Setting L E t z) {x : G} :
    x ∈ zpowers t ⊔ E ↔ ∃ e ∈ E, x = e ∨ x = e * t := by
  rw [sup_comm]
  exact mem_sup_zpowers_iff hs.tt fun _ he => hs.t_comm_E he

theorem mem_L_t_iff (hs : Setting L E t z) {x : G} :
    x ∈ L ⊔ zpowers t ↔ ∃ l ∈ L, x = l ∨ x = l * t :=
  mem_sup_zpowers_iff hs.tt fun _ hl => hs.t_comm hl

theorem X_comm (hs : Setting L E t z) {x y : G} (hx : x ∈ zpowers t ⊔ E)
    (hy : y ∈ zpowers t ⊔ E) : x * y = y * x := by
  have hat : ∀ a ∈ E, Commute a t := fun a ha => hs.t_comm_E ha
  have hab : ∀ a ∈ E, ∀ b ∈ E, Commute a b := fun a ha b hb => hs.E_comm ha hb
  obtain ⟨a, ha, h1 | h1⟩ := hs.mem_X_iff.1 hx <;>
    obtain ⟨b, hb, h2 | h2⟩ := hs.mem_X_iff.1 hy <;> subst x y
  · exact hab a ha b hb
  · exact ((hab a ha b hb).mul_right (hat a ha)).eq
  · exact ((hab a ha b hb).mul_left (hat b hb).symm).eq
  · exact (((hab a ha b hb).mul_right (hat a ha)).mul_left
      (((hat b hb).symm).mul_right (Commute.refl t))).eq

theorem conj_t_mem (hs : Setting L E t z) {n : G} (hn : n ∈ Ns t E) :
    ∃ g ∈ E, n * t * n⁻¹ = g * t := by
  have h1 : n * t * n⁻¹ ∈ zpowers t ⊔ E := (mem_normalizer_iff.1 hn t).1 (t_mem_X t E)
  obtain ⟨g, hg, h | h⟩ := hs.mem_X_iff.1 h1
  · exfalso
    by_cases hg1 : g = 1
    · have h' : n * t = n * 1 := by
        rw [mul_one]; exact mul_inv_eq_one.1 (h.trans hg1)
      have := hs.ht2
      rw [mul_left_cancel h', orderOf_one] at this
      omega
    · obtain ⟨a, -, hag⟩ := hs.htrans g hg hg1
      refine hs.hzt (a⁻¹ * n) ?_
      calc a⁻¹ * n * t * (a⁻¹ * n)⁻¹ = a⁻¹ * (n * t * n⁻¹) * a := by group
        _ = a⁻¹ * g * a := by rw [h]
        _ = z := by rw [← hag]; group
  · exact ⟨g, hg, h⟩

theorem conj_mem_E (hs : Setting L E t z) {n : G} (hn : n ∈ Ns t E) {e : G} (he : e ∈ E) :
    n * e * n⁻¹ ∈ E := by
  have h1 : n * e * n⁻¹ ∈ zpowers t ⊔ E := (mem_normalizer_iff.1 hn e).1 (mem_sup_right he)
  obtain ⟨f, hf, h | h⟩ := hs.mem_X_iff.1 h1
  · rw [h]; exact hf
  · exfalso
    obtain ⟨m, hm, hmt⟩ := hs.hfus e he
    obtain ⟨g, hg, hgt⟩ := hs.conj_t_mem hn
    obtain ⟨g', hg', hg't⟩ := hs.conj_t_mem (mul_mem hn hm)
    have h2 : n * m * t * (n * m)⁻¹ = g * f := by
      calc n * m * t * (n * m)⁻¹ = n * (m * t * m⁻¹) * n⁻¹ := by group
        _ = n * (t * e) * n⁻¹ := by rw [hmt]
        _ = (n * t * n⁻¹) * (n * e * n⁻¹) := by group
        _ = (g * t) * (f * t) := by rw [hgt, h]
        _ = g * (t * f) * t := by simp only [mul_assoc]
        _ = g * (f * t) * t := by rw [← hs.t_comm_E hf]
        _ = g * f * (t * t) := by simp only [mul_assoc]
        _ = g * f := by rw [hs.tt, mul_one]
    have h3 : g' * t = g * f := hg't.symm.trans h2
    have h4 : t = g'⁻¹ * (g * f) := by rw [← h3]; group
    exact hs.t_not_mem_E (h4 ▸ mul_mem (inv_mem hg') (mul_mem hg hf))

theorem normalizer_le_normalizer_E (hs : Setting L E t z) :
    Ns t E ≤ normalizer (E : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun he => hs.conj_mem_E hn he, fun h' => ?_⟩
  have := hs.conj_mem_E (inv_mem hn) h'
  simpa [mul_assoc] using this

theorem mem_X_of_centralizer (hs : Setting L E t z) {x : G}
    (hxt : x ∈ centralizer ({t} : Set G)) (hxE : x ∈ centralizer (E : Set G)) :
    x ∈ zpowers t ⊔ E := by
  rw [hs.hin] at hxt
  obtain ⟨l, hl, h1 | h1⟩ := hs.mem_L_t_iff.1 hxt
  · subst x
    have : l ∈ centralizer (E : Set G) ⊓ L := ⟨hxE, hl⟩
    rw [hs.hCE] at this
    exact mem_sup_right this
  · subst x
    have hlE : l ∈ centralizer (E : Set G) := by
      refine mem_centralizer_iff.2 ?_
      intro e he
      have h1 := mem_centralizer_iff.1 hxE e he
      apply mul_right_cancel (b := t)
      calc e * l * t = e * (l * t) := by rw [mul_assoc]
        _ = l * t * e := h1
        _ = l * (t * e) := by rw [mul_assoc]
        _ = l * (e * t) := by rw [← hs.t_comm_E he]
        _ = l * e * t := by rw [mul_assoc]
    have : l ∈ centralizer (E : Set G) ⊓ L := ⟨hlE, hl⟩
    rw [hs.hCE] at this
    exact mul_mem (mem_sup_right this) (t_mem_X t E)

theorem centralizer_X (hs : Setting L E t z) :
    centralizer ((zpowers t ⊔ E : Subgroup G) : Set G) = zpowers t ⊔ E := by
  apply le_antisymm
  · intro x hx
    refine hs.mem_X_of_centralizer ?_ ?_
    · refine mem_centralizer_iff.2 ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact mem_centralizer_iff.1 hx h (t_mem_X h E)
    · refine mem_centralizer_iff.2 ?_
      intro e he
      exact mem_centralizer_iff.1 hx e (mem_sup_right he)
  · intro x hx
    refine mem_centralizer_iff.2 ?_
    intro y hy
    exact hs.X_comm hy hx

theorem conj_mem_X (hs : Setting L E t z) {a : G} (haE : a ∈ normalizer (E : Set G))
    (hat : a * t = t * a) {x : G} (hx : x ∈ zpowers t ⊔ E) : a * x * a⁻¹ ∈ zpowers t ⊔ E := by
  obtain ⟨e, he, h1 | h1⟩ := hs.mem_X_iff.1 hx
  · subst x
    exact mem_sup_right ((mem_normalizer_iff.1 haE e).1 he)
  · subst x
    have : a * (e * t) * a⁻¹ = (a * e * a⁻¹) * t := by
      calc a * (e * t) * a⁻¹ = (a * e * a⁻¹) * (a * t * a⁻¹) := by group
        _ = (a * e * a⁻¹) * t := by rw [hat, mul_inv_cancel_right]
    rw [this]
    exact mul_mem (mem_sup_right ((mem_normalizer_iff.1 haE e).1 he)) (t_mem_X t E)

theorem mem_N_of_normalizer_E (hs : Setting L E t z) {a : G}
    (haE : a ∈ normalizer (E : Set G)) (hat : a * t = t * a) : a ∈ Ns t E := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hs.conj_mem_X haE hat, fun h => ?_⟩
  have hat' : a⁻¹ * t = t * a⁻¹ := (Commute.inv_left (show Commute a t from hat)).eq
  have := hs.conj_mem_X (inv_mem haE) hat' h
  simpa [mul_assoc] using this

theorem A_le_N0 (hs : Setting L E t z) :
    (normalizer (E : Set G) ⊓ L : Subgroup G) ≤ N0s t E := by
  rintro a ⟨haE, haL⟩
  refine ⟨hs.mem_N_of_normalizer_E haE (hs.t_comm haL), ?_⟩
  refine mem_centralizer_iff.2 ?_
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact (hs.t_comm haL).symm

theorem N0_eq (hs : Setting L E t z) :
    N0s t E = (normalizer (E : Set G) ⊓ L : Subgroup G) ⊔ zpowers t := by
  apply le_antisymm
  · rintro x ⟨hxN, hxt⟩
    have hxNE := hs.normalizer_le_normalizer_E hxN
    rw [hs.hin] at hxt
    obtain ⟨l, hl, h1 | h1⟩ := hs.mem_L_t_iff.1 hxt
    · subst x
      exact mem_sup_left ⟨hxNE, hl⟩
    · subst x
      have htN : t ∈ normalizer (E : Set G) :=
        hs.normalizer_le_normalizer_E (le_normalizer (t_mem_X t E))
      have hlN : l ∈ normalizer (E : Set G) := by
        have := mul_mem hxNE (inv_mem htN)
        simpa using this
      exact mul_mem (mem_sup_left ⟨hlN, hl⟩) (mem_sup_right (mem_zpowers t))
  · refine sup_le hs.A_le_N0 ?_
    rw [zpowers_le]
    refine ⟨le_normalizer (t_mem_X t E), ?_⟩
    refine mem_centralizer_iff.2 ?_
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]

theorem card_N0 (hs : Setting L E t z) : Nat.card (N0s t E) = 23040 := by
  have h := card_sup_zpowers (H := (normalizer (E : Set G) ⊓ L : Subgroup G)) hs.ht2
    (fun h => hs.t_not_mem_L h.2) (fun a ha => hs.t_comm ha.2)
  calc Nat.card ↥(N0s t E) = Nat.card ↥((normalizer (E : Set G) ⊓ L : Subgroup G) ⊔ zpowers t) := by
        rw [hs.N0_eq]
    _ = 23040 := by rw [h, hs.hNE]

theorem card_X (hs : Setting L E t z) : Nat.card (zpowers t ⊔ E : Subgroup G) = 32 := by
  have h := card_sup_zpowers (H := E) hs.ht2 hs.t_not_mem_E fun e he => hs.t_comm_E he
  rw [sup_comm, h, hs.hE16]

theorem X_le_K (hs : Setting L E t z) : zpowers t ⊔ E ≤ Ks t E := by
  intro x hx
  refine ⟨le_normalizer hx, ?_⟩
  refine mem_centralizer_iff.2 ?_
  intro e he
  exact hs.X_comm (mem_sup_right he) hx

theorem conj_mem_K (hs : Setting L E t z) {n k : G} (hn : n ∈ Ns t E) (hk : k ∈ Ks t E) :
    n * k * n⁻¹ ∈ Ks t E := by
  refine mem_inf.2 ⟨mul_mem (mul_mem hn (mem_inf.1 hk).1) (inv_mem hn), ?_⟩
  refine mem_centralizer_iff.2 ?_
  intro e he
  have hne : n⁻¹ * e * n ∈ E := by
    have := hs.conj_mem_E (inv_mem hn) he
    simpa using this
  have h1 := mem_centralizer_iff.1 hk.2 _ hne
  calc e * (n * k * n⁻¹) = n * ((n⁻¹ * e * n) * k) * n⁻¹ := by group
    _ = n * (k * (n⁻¹ * e * n)) * n⁻¹ := by rw [h1]
    _ = (n * k * n⁻¹) * e := by group

theorem phi_mem (hs : Setting L E t z) {k : G} (hk : k ∈ Ks t E) : k * t * k⁻¹ * t⁻¹ ∈ E := by
  obtain ⟨g, hg, h⟩ := hs.conj_t_mem hk.1
  rw [h, mul_inv_cancel_right]
  exact hg

theorem phi_mul (hs : Setting L E t z) {k k' : G} (hk : k ∈ Ks t E) (hk' : k' ∈ Ks t E) :
    k * k' * t * (k * k')⁻¹ * t⁻¹ = (k * t * k⁻¹ * t⁻¹) * (k' * t * k'⁻¹ * t⁻¹) := by
  have hb := hs.phi_mem hk'
  have hkb : k * (k' * t * k'⁻¹ * t⁻¹) * k⁻¹ = k' * t * k'⁻¹ * t⁻¹ := by
    have := mem_centralizer_iff.1 hk.2 _ hb
    rw [← this]
    group
  have e1 : k * k' * t * (k * k')⁻¹ * t⁻¹ =
      (k * (k' * t * k'⁻¹ * t⁻¹) * k⁻¹) * (k * t * k⁻¹ * t⁻¹) := by group
  rw [e1, hkb]
  exact hs.E_comm hb (hs.phi_mem hk)

theorem phi_eq_one_iff (hs : Setting L E t z) {k : G} (hk : k ∈ Ks t E) :
    k * t * k⁻¹ * t⁻¹ = 1 ↔ k ∈ zpowers t ⊔ E := by
  constructor
  · intro h
    have h1 : k * t = t * k := mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h)
    refine hs.mem_X_of_centralizer ?_ hk.2
    refine mem_centralizer_iff.2 ?_
    intro h' hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact h1.symm
  · intro hx
    rw [hs.X_comm hx (t_mem_X t E)]
    group

theorem K_inf_t (hs : Setting L E t z) :
    Ks t E ⊓ centralizer ({t} : Set G) = zpowers t ⊔ E := by
  apply le_antisymm
  · rintro x ⟨hxK, hxt⟩
    exact hs.mem_X_of_centralizer hxt hxK.2
  · intro x hx
    refine ⟨hs.X_le_K hx, ?_⟩
    refine mem_centralizer_iff.2 ?_
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hs.X_comm (t_mem_X h E) hx

theorem card_N (hs : Setting L E t z) : Nat.card (Ns t E) = 16 * Nat.card (N0s t E) := by
  let ι : ↥(Ns t E) →* ConjAct G := ConjAct.toConjAct.toMonoidHom.comp (Ns t E).subtype
  let _ : MulAction ↥(Ns t E) G := MulAction.compHom G ι
  have hsmul : ∀ (n : ↥(Ns t E)) (g : G), n • g = (n : G) * g * (n : G)⁻¹ := by
    intro n g
    show (ConjAct.toConjAct (n : G)) • g = _
    rw [ConjAct.smul_def]
    simp
  have hstab : MulAction.stabilizer ↥(Ns t E) t = (N0s t E).subgroupOf (Ns t E) := by
    ext n
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      refine ⟨n.2, ?_⟩
      refine mem_centralizer_iff.2 ?_
      intro h' hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
    · rintro ⟨-, h⟩
      have := mem_centralizer_iff.1 h t rfl
      exact mul_inv_eq_iff_eq_mul.2 this.symm
  have horbit : MulAction.orbit ↥(Ns t E) t = (fun e => e * t) '' (E : Set G) := by
    ext g
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨n, rfl⟩
      obtain ⟨g', hg', h⟩ := hs.conj_t_mem n.2
      exact ⟨g', hg', by rw [hsmul]; exact h.symm⟩
    · rintro ⟨e, he, rfl⟩
      obtain ⟨m, hm, hmt⟩ := hs.hfus e he
      refine ⟨⟨m, hm⟩, ?_⟩
      rw [hsmul]
      show m * t * m⁻¹ = e * t
      rw [hmt, hs.t_comm_E he]
  have hidx : (MulAction.stabilizer ↥(Ns t E) t).index = 16 := by
    rw [MulAction.index_stabilizer, horbit, Set.ncard_image_of_injective _ (mul_left_injective t),
      ← Nat.card_coe_set_eq]
    exact hs.hE16
  have hcard := (MulAction.stabilizer ↥(Ns t E) t).card_mul_index
  rw [hidx, hstab] at hcard
  rw [← hcard, mul_comm]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

@[expose] noncomputable def phi (hs : Setting L E t z) : ↥(Ks t E) →* ↥E where
  toFun k := ⟨k * t * k⁻¹ * t⁻¹, hs.phi_mem k.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' k k' := Subtype.ext (hs.phi_mul k.2 k'.2)

theorem ker_phi (hs : Setting L E t z) :
    hs.phi.ker = (zpowers t ⊔ E).subgroupOf (Ks t E) := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hs.phi_eq_one_iff k.2,
    Subtype.ext_iff]
  rfl

theorem false_of_K_le_X (hs : Setting L E t z) (hK : Ks t E ≤ zpowers t ⊔ E) : False := by
  let ψ := conjAut E (Ns t E) hs.normalizer_le_normalizer_E
  have hker : ψ.ker = (Ks t E).subgroupOf (Ns t E) := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      refine ⟨n.2, ?_⟩
      refine mem_centralizer_iff.2 ?_
      intro e he
      have := congrArg (fun f : MulAut ↥E => ((f ⟨e, he⟩ : ↥E) : G)) h
      simp only [ψ, conjAut, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
        MulAut.one_apply] at this
      have h2 : (n : G) * e * (n : G)⁻¹ = e := this
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    · rintro ⟨-, h⟩
      ext e
      have := mem_centralizer_iff.1 h e e.2
      show (n : G) * e * (n : G)⁻¹ = e
      exact mul_inv_eq_iff_eq_mul.2 this.symm
  have hKX : Ks t E = zpowers t ⊔ E := le_antisymm hK hs.X_le_K
  have hcker : Nat.card ψ.ker = 32 := by
    rw [hker]
    calc Nat.card ↥((Ks t E).subgroupOf (Ns t E)) = Nat.card ↥(Ks t E) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      _ = 32 := by rw [hKX]; exact hs.card_X
  have h1 := Subgroup.card_ker_mul_card_range ψ
  rw [hcker, hs.card_N, hs.card_N0] at h1
  have h2 : Nat.card ψ.range = 11520 := by omega
  have h3 : Nat.card ψ.range ∣ Nat.card (MulAut ↥E) := ψ.range.card_subgroup_dvd_card
  rw [h2, card_mulAut_elemAbelian hs.hEab hs.hE16] at h3
  omega

theorem conj_phi (hs : Setting L E t z) {n : G} (hn : n ∈ N0s t E) (k : ↥(Ks t E)) :
    n * ((hs.phi k : ↥E) : G) * n⁻¹ =
      ((hs.phi ⟨n * k * n⁻¹, hs.conj_mem_K hn.1 k.2⟩ : ↥E) : G) := by
  have hc : Commute n t := (mem_centralizer_iff.1 hn.2 t rfl).symm
  have h1 : n⁻¹ * t = t * n⁻¹ := hc.inv_left.eq
  have h2 : n⁻¹ * t⁻¹ = t⁻¹ * n⁻¹ := hc.inv_left.inv_right.eq
  show n * ((k : G) * t * (k : G)⁻¹ * t⁻¹) * n⁻¹ = n * k * n⁻¹ * t * (n * k * n⁻¹)⁻¹ * t⁻¹
  calc n * ((k : G) * t * (k : G)⁻¹ * t⁻¹) * n⁻¹
        = n * k * t * (k : G)⁻¹ * (t⁻¹ * n⁻¹) := by group
    _ = n * k * t * (k : G)⁻¹ * (n⁻¹ * t⁻¹) := by rw [h2]
    _ = n * k * (t * n⁻¹) * n * (k : G)⁻¹ * n⁻¹ * t⁻¹ := by group
    _ = n * k * (n⁻¹ * t) * n * (k : G)⁻¹ * n⁻¹ * t⁻¹ := by rw [h1]
    _ = _ := by group

theorem phi_surj (hs : Setting L E t z) : ∀ e ∈ E, ∃ k ∈ Ks t E, k * t * k⁻¹ * t⁻¹ = e := by
  let Φ : Subgroup G := hs.phi.range.map E.subtype
  have hΦmem : ∀ e, e ∈ Φ ↔ ∃ k ∈ Ks t E, k * t * k⁻¹ * t⁻¹ = e := by
    intro e
    constructor
    · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨hs.phi ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩, rfl⟩
  have hΦE : ∀ e ∈ Φ, e ∈ E := fun e he => by
    obtain ⟨k, hk, rfl⟩ := (hΦmem e).1 he
    exact hs.phi_mem hk
  have hinv : ∀ n ∈ N0s t E, ∀ e ∈ Φ, n * e * n⁻¹ ∈ Φ := by
    intro n hn e he
    obtain ⟨k, hk, rfl⟩ := (hΦmem e).1 he
    have := hs.conj_phi hn ⟨k, hk⟩
    exact (hΦmem _).2 ⟨n * k * n⁻¹, hs.conj_mem_K hn.1 hk, this.symm⟩
  by_cases hall : ∀ e ∈ Φ, e = 1
  · exfalso
    refine hs.false_of_K_le_X fun k hk => ?_
    have : k * t * k⁻¹ * t⁻¹ ∈ Φ := (hΦmem _).2 ⟨k, hk, rfl⟩
    exact (hs.phi_eq_one_iff hk).1 (hall _ this)
  · push Not at hall
    obtain ⟨e0, he0, he01⟩ := hall
    have hz : z ∈ Φ := by
      obtain ⟨a, ha, haz⟩ := hs.htrans e0 (hΦE e0 he0) he01
      have haN0 : a⁻¹ ∈ N0s t E := inv_mem (hs.A_le_N0 ha)
      have := hinv a⁻¹ haN0 e0 he0
      rw [← haz] at this
      simpa [mul_assoc] using this
    intro e he
    by_cases he1 : e = 1
    · exact ⟨1, one_mem _, by simp [he1]⟩
    · obtain ⟨a, ha, haz⟩ := hs.htrans e he he1
      have := hinv a (hs.A_le_N0 ha) z hz
      rw [haz] at this
      exact (hΦmem e).1 this

theorem phi_surjective (hs : Setting L E t z) : Function.Surjective hs.phi := by
  intro e
  obtain ⟨k, hk, h⟩ := hs.phi_surj e e.2
  exact ⟨⟨k, hk⟩, Subtype.ext h⟩

theorem card_K (hs : Setting L E t z) : Nat.card (Ks t E) = 512 := by
  have h := Subgroup.card_ker_mul_card_of_surjective hs.phi_surjective
  rw [hs.ker_phi] at h
  have h32 : Nat.card ((zpowers t ⊔ E).subgroupOf (Ks t E)) = 32 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs.X_le_K).toEquiv).trans hs.card_X
  rw [h32, hs.hE16] at h
  omega

theorem N_eq (hs : Setting L E t z) :
    ∀ n ∈ Ns t E, ∃ k ∈ Ks t E, ∃ n₀ ∈ N0s t E, n = k * n₀ := by
  intro n hn
  obtain ⟨g, hg, hgt⟩ := hs.conj_t_mem hn
  obtain ⟨k, hk, hkg⟩ := hs.phi_surj g hg
  have hkt : k * t * k⁻¹ = g * t := mul_inv_eq_iff_eq_mul.1 hkg
  refine ⟨k, hk, k⁻¹ * n, ?_, by group⟩
  have hnt : n * t = k * t * k⁻¹ * n := mul_inv_eq_iff_eq_mul.1 (hgt.trans hkt.symm)
  refine mem_inf.2 ⟨mul_mem (inv_mem (mem_inf.1 hk).1) hn, ?_⟩
  refine mem_centralizer_iff.2 fun h hh => ?_
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  calc t * (k⁻¹ * n) = k⁻¹ * (k * t * k⁻¹ * n) := by group
    _ = k⁻¹ * (n * t) := by rw [hnt]
    _ = k⁻¹ * n * t := by group

theorem exists_order5 [Finite G] (hs : Setting L E t z) :
    ∃ y ∈ (normalizer (E : Set G) ⊓ L : Subgroup G), orderOf y = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let A : Subgroup G := normalizer (E : Set G) ⊓ L
  have : Fintype A := Fintype.ofFinite A
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := A) 5
    (by rw [← Nat.card_eq_fintype_card, hs.hNE]; norm_num)
  exact ⟨y, y.2, by rwa [Subgroup.orderOf_coe]⟩

theorem fixed_E_y [Finite G] (hs : Setting L E t z) {y : G}
    (hy : y ∈ (normalizer (E : Set G) ⊓ L : Subgroup G)) (hy5 : orderOf y = 5) :
    ∀ e ∈ E, y * e * y⁻¹ = e → e = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hyN : y ∈ normalizer (E : Set G) := hy.1
  have hQE : ∀ q ∈ zpowers y, ∀ d ∈ E, q * d * q⁻¹ ∈ E := by
    intro q hq d hd
    have : q ∈ normalizer (E : Set G) := (zpowers_le.2 hyN) hq
    exact (mem_normalizer_iff.1 this d).1 hd
  have hfinE : Finite E := Nat.finite_of_card_ne_zero (by rw [hs.hE16]; norm_num)
  have hmod := card_modEq_centralizer (D := E) (isPGroup_zpowers hy5) hQE
  have hCle : E ⊓ centralizer (zpowers y : Set G) ≤ E := inf_le_left
  have hC1 : Nat.card ↥(E ⊓ centralizer (zpowers y : Set G)) ≡ 1 [MOD 5] := by
    refine hmod.symm.trans ?_
    rw [hs.hE16]
    decide
  have hCd : Nat.card ↥(E ⊓ centralizer (zpowers y : Set G)) ∣ 16 := by
    rw [← hs.hE16]; exact Subgroup.card_dvd_of_le hCle
  rcases eq_one_or_sixteen hCd hC1 with h1 | h16
  · have hbot := Subgroup.card_eq_one.1 h1
    intro e he hye
    have : e ∈ E ⊓ centralizer (zpowers y : Set G) :=
      mem_inf.2 ⟨he, mem_centralizer_zpowers_iff.2 (mul_inv_eq_iff_eq_mul.1 hye)⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  · exfalso
    have hEC : E ⊓ centralizer (zpowers y : Set G) = E :=
      Subgroup.eq_of_le_of_card_ge hCle (by rw [h16, hs.hE16])
    have hyC : y ∈ centralizer (E : Set G) := by
      refine mem_centralizer_iff.2 fun e he => ?_
      have : e ∈ E ⊓ centralizer (zpowers y : Set G) := by rw [hEC]; exact he
      exact (mem_centralizer_zpowers_iff.1 (mem_inf.1 this).2).symm
    have hyE : y ∈ E := by
      have : y ∈ centralizer (E : Set G) ⊓ L := ⟨hyC, hy.2⟩
      rwa [hs.hCE] at this
    have h2 : y ^ 2 = 1 := by
      have := hs.hEab.2 y hyE
      exact this
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hy5] at this
    omega

theorem W_mem_E (hs : Setting L E t z) {W : Subgroup G} (hEW : E ≤ W) (htW : t ∉ W) {w : G}
    (hw : w ∈ W) (hwX : w ∈ zpowers t ⊔ E) : w ∈ E := by
  obtain ⟨e, he, h1 | h1⟩ := hs.mem_X_iff.1 hwX
  · exact h1 ▸ he
  · exfalso
    apply htW
    have : t = e⁻¹ * w := by rw [h1]; group
    rw [this]
    exact W.mul_mem (W.inv_mem (hEW he)) hw

theorem W_comm {W : Subgroup G} (hWab : IsElemAbelian 2 W) {a b : G} (ha : a ∈ W) (hb : b ∈ W) :
    a * b = b * a :=
  CFSG.Open.IsElemAbelian.comm hWab ha hb

theorem W_le_Ostar [Finite G] (hs : Setting L E t z) {W : Subgroup G} (hWK : W ≤ Ks t E)
    (hWN : ∀ n ∈ Ns t E, ∀ w ∈ W, n * w * n⁻¹ ∈ W) (hEW : E ≤ W) (htW : t ∉ W)
    (hWab : IsElemAbelian 2 W) {y : G} (hy : y ∈ (normalizer (E : Set G) ⊓ L : Subgroup G))
    (hy5 : orderOf y = 5) : W ≤ Ostar (Ns t E) := by
  have hyN0 : y ∈ N0s t E := hs.A_le_N0 hy
  have hyN : y ∈ Ns t E := hyN0.1
  have hyO : y ∈ Ostar (Ns t E) := subset_closure ⟨hyN, by rw [hy5]; decide⟩
  have hCy := hs.fixed_E_y hy hy5
  let f : ↥W →* ↥W :=
    { toFun := fun w => ⟨w * (y * (w : G)⁻¹ * y⁻¹), W.mul_mem w.2 (hWN y hyN _ (W.inv_mem w.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hu : y * (a : G)⁻¹ * y⁻¹ ∈ W := hWN y hyN _ (W.inv_mem a.2)
        have hv : y * (b : G)⁻¹ * y⁻¹ ∈ W := hWN y hyN _ (W.inv_mem b.2)
        show (a : G) * b * (y * ((a : G) * b)⁻¹ * y⁻¹) =
          ((a : G) * (y * (a : G)⁻¹ * y⁻¹)) * ((b : G) * (y * (b : G)⁻¹ * y⁻¹))
        calc (a : G) * b * (y * ((a : G) * b)⁻¹ * y⁻¹)
            = (a : G) * ((b : G) * ((y * (b : G)⁻¹ * y⁻¹) * (y * (a : G)⁻¹ * y⁻¹))) := by group
          _ = (a : G) * ((b : G) * ((y * (a : G)⁻¹ * y⁻¹) * (y * (b : G)⁻¹ * y⁻¹))) := by
            rw [W_comm hWab hv hu]
          _ = (a : G) * (((y * (a : G)⁻¹ * y⁻¹) * (b : G)) * (y * (b : G)⁻¹ * y⁻¹)) := by
            have key : (b : G) * ((y * (a : G)⁻¹ * y⁻¹) * (y * (b : G)⁻¹ * y⁻¹)) =
                ((y * (a : G)⁻¹ * y⁻¹) * (b : G)) * (y * (b : G)⁻¹ * y⁻¹) := by
              rw [← mul_assoc, ← W_comm hWab b.2 hu]
            rw [key]
          _ = _ := by simp only [mul_assoc] }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h0 : (a : G) * (y * (a : G)⁻¹ * y⁻¹) = 1 := congrArg Subtype.val ha
    have h1 : y * (a : G)⁻¹ * y⁻¹ = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right h0
    have hyfix : y * (a : G) * y⁻¹ = a := by
      calc y * (a : G) * y⁻¹ = (y * (a : G)⁻¹ * y⁻¹)⁻¹ := by group
        _ = a := by rw [h1]; simp
    let aK : ↥(Ks t E) := ⟨a, hWK a.2⟩
    have hconj := hs.conj_phi hyN0 aK
    have hphi : ((hs.phi ⟨y * (aK : G) * y⁻¹, hs.conj_mem_K hyN0.1 aK.2⟩ : ↥E) : G) =
        ((hs.phi aK : ↥E) : G) := by
      rw [show (⟨y * (aK : G) * y⁻¹, hs.conj_mem_K hyN0.1 aK.2⟩ : ↥(Ks t E)) = aK from
        Subtype.ext hyfix]
    have hφ1 : ((hs.phi aK : ↥E) : G) = 1 := hCy _ (hs.phi aK).2 (hconj.trans hphi)
    have haX : (a : G) ∈ zpowers t ⊔ E := (hs.phi_eq_one_iff aK.2).1 hφ1
    have haE : (a : G) ∈ E := hs.W_mem_E hEW htW a.2 haX
    exact Subtype.ext (hCy _ haE hyfix)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hinj
  intro w hw
  obtain ⟨u, hu⟩ := hsurj ⟨w, hw⟩
  have hw' : w = (u : G) * y * (u : G)⁻¹ * y⁻¹ := by
    have := congrArg Subtype.val hu
    rw [← show (f u : G) = w from this]
    show (u : G) * (y * (u : G)⁻¹ * y⁻¹) = _
    group
  rw [hw']
  have huN : (u : G) ∈ Ns t E := (hWK u.2).1
  exact mul_mem (Ostar_conj huN hyO) (inv_mem hyO)

theorem K_cases (hs : Setting L E t z) {W : Subgroup G} (hWK : W ≤ Ks t E)
    (hW : Nat.card W = 256) (htW : t ∉ W) : ∀ x ∈ Ks t E, x ∈ W ∨ x * t ∈ W := by
  have hidx : (W.subgroupOf (Ks t E)).index = 2 := by
    have h := (W.subgroupOf (Ks t E)).card_mul_index
    have h1 : Nat.card ↥(W.subgroupOf (Ks t E)) = 256 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv).trans hW
    rw [h1, hs.card_K] at h
    omega
  obtain ⟨a₀, ha₀⟩ := Subgroup.index_eq_two_iff.1 hidx
  have key : ∀ b : ↥(Ks t E), (b : G) ∉ W → (b : G) * a₀ ∈ W := by
    intro b hb
    rcases ha₀ b with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact Subgroup.mem_subgroupOf.1 h1
    · exact absurd (Subgroup.mem_subgroupOf.1 h1) hb
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hs.tt
  intro x hx
  by_cases hxW : x ∈ W
  · exact Or.inl hxW
  · right
    have h1 := key ⟨x, hx⟩ hxW
    have h2 := key ⟨t, hs.X_le_K (t_mem_X t E)⟩ htW
    have h3 : (x * a₀) * (t * a₀)⁻¹ ∈ W := W.mul_mem h1 (W.inv_mem h2)
    have h4 : (x * a₀) * (t * a₀)⁻¹ = x * t := by
      calc (x * a₀) * (t * a₀)⁻¹ = x * t⁻¹ := by group
        _ = x * t := by rw [htinv]
    rwa [h4] at h3

theorem O2O2_eq [Finite G] (hs : Setting L E t z) {W : Subgroup G} (hWK : W ≤ Ks t E)
    (hWN : ∀ n ∈ Ns t E, ∀ w ∈ W, n * w * n⁻¹ ∈ W) (hEW : E ≤ W) (htW : t ∉ W)
    (hWab : IsElemAbelian 2 W) (hW : Nat.card W = 256) : W = Opp2 (Ns t E) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy, hy5⟩ := hs.exists_order5
  have hyN0 : y ∈ N0s t E := hs.A_le_N0 hy
  have hyN : y ∈ Ns t E := hyN0.1
  have hyO : y ∈ Ostar (Ns t E) := subset_closure ⟨hyN, by rw [hy5]; decide⟩
  have hCy := hs.fixed_E_y hy hy5
  have hWO := hs.W_le_Ostar hWK hWN hEW htW hWab hy hy5
  have hAN : ∀ a ∈ (normalizer (E : Set G) ⊓ L : Subgroup G), a ∈ Ns t E :=
    fun a ha => (hs.A_le_N0 ha).1
  have hatc : ∀ a ∈ (normalizer (E : Set G) ⊓ L : Subgroup G), a * t = t * a :=
    fun a ha => hs.t_comm ha.2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hs.tt
  have htN : t ∈ Ns t E := le_normalizer (t_mem_X t E)
  let M2 : Subgroup G :=
    { carrier := {x | ∃ w ∈ W, ∃ a ∈ (normalizer (E : Set G) ⊓ L : Subgroup G), x = w * a}
      one_mem' := ⟨1, W.one_mem, 1, Subgroup.one_mem _, (mul_one 1).symm⟩
      mul_mem' := by
        rintro x y ⟨w, hw, a, ha, rfl⟩ ⟨w', hw', a', ha', rfl⟩
        refine ⟨w * (a * w' * a⁻¹), W.mul_mem hw (hWN a (hAN a ha) w' hw'), a * a',
          Subgroup.mul_mem _ ha ha', ?_⟩
        group
      inv_mem' := by
        rintro x ⟨w, hw, a, ha, rfl⟩
        refine ⟨a⁻¹ * w⁻¹ * a, ?_, a⁻¹, Subgroup.inv_mem _ ha, ?_⟩
        · have := hWN a⁻¹ (hAN _ (Subgroup.inv_mem _ ha)) w⁻¹ (W.inv_mem hw)
          simpa using this
        · group }
  have hWM : ∀ w ∈ W, w ∈ M2 := fun w hw => ⟨w, hw, 1, Subgroup.one_mem _, (mul_one w).symm⟩
  have htM2 : t ∉ M2 := by
    rintro ⟨w, hw, a, ha, hta⟩
    have hwK := hWK hw
    have hw' : w = t * a⁻¹ := eq_mul_inv_of_mul_eq hta.symm
    have hat' : a⁻¹ * t = t * a⁻¹ := (Commute.inv_left (show Commute a t from hatc a ha)).eq
    have hwt : w * t = t * w := by
      rw [hw']
      calc t * a⁻¹ * t = t * (a⁻¹ * t) := by rw [mul_assoc]
        _ = t * (t * a⁻¹) := by rw [hat']
        _ = t * (t * a⁻¹) := rfl
    have hwX : w ∈ zpowers t ⊔ E := by
      have : w ∈ Ks t E ⊓ centralizer ({t} : Set G) := by
        refine ⟨hwK, mem_centralizer_iff.2 fun h hh => ?_⟩
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hwt.symm
      rwa [hs.K_inf_t] at this
    have hwE := hs.W_mem_E hEW htW hw hwX
    exact hs.t_not_mem_L (by rw [hta]; exact L.mul_mem (hs.hEL hwE) ha.2)
  have htconj : ∀ u ∈ M2, t * u * t ∈ M2 := by
    rintro u ⟨w, hw, a, ha, rfl⟩
    refine ⟨t * w * t, ?_, a, ha, ?_⟩
    · have := hWN t htN w hw
      rwa [htinv] at this
    · calc t * (w * a) * t = t * w * (a * t) := by group
        _ = t * w * (t * a) := by rw [hatc a ha]
        _ = t * w * t * a := by group
  have hNcases : ∀ n ∈ Ns t E, n ∈ M2 ∨ n * t ∈ M2 := by
    intro n hn
    obtain ⟨k, hk, n₀, hn₀, rfl⟩ := hs.N_eq n hn
    have hn₀' : n₀ ∈ (normalizer (E : Set G) ⊓ L : Subgroup G) ⊔ zpowers t := by
      rw [← hs.N0_eq]; exact hn₀
    obtain ⟨a, ha, h1 | h1⟩ := (mem_sup_zpowers_iff hs.tt (fun a ha => hatc a ha)).1 hn₀'
    · rcases hs.K_cases hWK hW htW k hk with hkW | hktW
      · exact Or.inl ⟨k, hkW, a, ha, by rw [h1]⟩
      · refine Or.inr ⟨k * t, hktW, a, ha, ?_⟩
        rw [h1]
        calc k * a * t = k * (a * t) := by rw [mul_assoc]
          _ = k * (t * a) := by rw [hatc a ha]
          _ = k * t * a := by rw [mul_assoc]
    · rcases hs.K_cases hWK hW htW k hk with hkW | hktW
      · refine Or.inr ⟨k, hkW, a, ha, ?_⟩
        rw [h1]
        calc k * (a * t) * t = k * a * (t * t) := by group
          _ = k * a := by rw [hs.tt, mul_one]
      · refine Or.inl ⟨k * t, hktW, a, ha, ?_⟩
        rw [h1]
        calc k * (a * t) = k * (t * a) := by rw [hatc a ha]
          _ = k * t * a := by rw [mul_assoc]
  have hOM : Ostar (Ns t E) ≤ M2 := by
    refine (closure_le _).2 ?_
    rintro x ⟨hxN, m, hm⟩
    rcases hNcases x hxN with h | h
    · exact h
    · have hx2 : x * x ∈ M2 := by
        have h' := M2.mul_mem h (htconj _ h)
        have e : (x * t) * (t * (x * t) * t) = x * x := by
          calc (x * t) * (t * (x * t) * t) = x * (t * t) * x * (t * t) := by group
            _ = x * x := by rw [hs.tt]; group
        rwa [e] at h'
      have hxpow : (x * x) ^ (m + 1) = x := by
        calc (x * x) ^ (m + 1) = x ^ (2 * (m + 1)) := by rw [← pow_two, ← pow_mul]
          _ = x ^ (orderOf x) * x := by rw [hm]; group
          _ = x := by rw [pow_orderOf_eq_one, one_mul]
      rw [← hxpow]
      exact M2.pow_mem hx2 (m + 1)
  apply le_antisymm
  · exact le_sSup ⟨hWO, IsPGroup.of_card (n := 8) (by rw [hW]; norm_num),
      fun h hh w hw => hWN h (Ostar_le _ hh) w hw⟩
  · refine sSup_le ?_
    rintro P ⟨hPO, hP2, hPn⟩ p hp
    have hPN : ∀ q ∈ P, q ∈ Ns t E := fun q hq => Ostar_le _ (hPO hq)
    have hPnormE : ∀ q ∈ P, ∀ e ∈ E, q * e * q⁻¹ ∈ E :=
      fun q hq e he => hs.conj_mem_E (hPN q hq) he
    have hfinE : Finite E := Nat.finite_of_card_ne_zero (by rw [hs.hE16]; norm_num)
    have hmod2 := card_modEq_centralizer (p := 2) (Q := P) (D := E) hP2 hPnormE
    have hD2 : 2 ∣ Nat.card ↥(E ⊓ centralizer (P : Set G)) := by
      rw [hs.hE16] at hmod2
      unfold Nat.ModEq at hmod2
      omega
    have hDinv : ∀ q ∈ zpowers y, ∀ d ∈ (E ⊓ centralizer (P : Set G) : Subgroup G),
        q * d * q⁻¹ ∈ (E ⊓ centralizer (P : Set G) : Subgroup G) := by
      intro q hq d hd
      have hqN : q ∈ normalizer (E : Set G) := (zpowers_le.2 hy.1) hq
      refine mem_inf.2 ⟨(mem_normalizer_iff.1 hqN d).1 (mem_inf.1 hd).1, ?_⟩
      refine mem_centralizer_iff.2 fun p' hp' => ?_
      have hqO : q ∈ Ostar (Ns t E) := (zpowers_le.2 hyO) hq
      have hp'' : q⁻¹ * p' * q ∈ P := by
        have := hPn q⁻¹ (Subgroup.inv_mem _ hqO) p' hp'
        simpa using this
      have h1 := mem_centralizer_iff.1 (mem_inf.1 hd).2 _ hp''
      calc p' * (q * d * q⁻¹) = q * ((q⁻¹ * p' * q) * d) * q⁻¹ := by group
        _ = q * (d * (q⁻¹ * p' * q)) * q⁻¹ := by rw [h1]
        _ = (q * d * q⁻¹) * p' := by group
    have hfinD : Finite ↥(E ⊓ centralizer (P : Set G)) := inferInstance
    have hmod5 := card_modEq_centralizer (p := 5) (Q := zpowers y)
      (D := E ⊓ centralizer (P : Set G)) (isPGroup_zpowers hy5) hDinv
    have hDy : (E ⊓ centralizer (P : Set G) : Subgroup G) ⊓ centralizer (zpowers y : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro d hd
      have hdE : d ∈ E := (mem_inf.1 (mem_inf.1 hd).1).1
      have hyd := mem_centralizer_zpowers_iff.1 (mem_inf.1 hd).2
      exact Subgroup.mem_bot.2 (hCy d hdE (mul_inv_eq_iff_eq_mul.2 hyd))
    rw [hDy, Subgroup.card_bot] at hmod5
    have hDd : Nat.card ↥(E ⊓ centralizer (P : Set G)) ∣ 16 := by
      rw [← hs.hE16]; exact Subgroup.card_dvd_of_le inf_le_left
    have hD16 := eq_sixteen_of_even hDd hmod5 hD2
    have hDE : (E ⊓ centralizer (P : Set G) : Subgroup G) = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hD16, hs.hE16])
    have hpK : p ∈ Ks t E := by
      refine mem_inf.2 ⟨hPN p hp, mem_centralizer_iff.2 fun e he => ?_⟩
      have : e ∈ E ⊓ centralizer (P : Set G) := by rw [hDE]; exact he
      exact (mem_centralizer_iff.1 (mem_inf.1 this).2 p hp).symm
    have hpM := hOM (hPO hp)
    rcases hs.K_cases hWK hW htW p hpK with h | h
    · exact h
    · exfalso
      apply htM2
      have : t = p⁻¹ * (p * t) := by group
      rw [this]
      exact M2.mul_mem (M2.inv_mem hpM) (hWM _ h)

end Setting

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2
