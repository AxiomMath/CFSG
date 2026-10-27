module

public import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

variable {P : Type*} [Group P] [Finite P] {p : ℕ}

omit [Finite P] in
theorem exists_mem_pow_mem (hp : p.Prime) (hP : IsPGroup p P) {A N : Subgroup P} [A.Normal]
    (hlt : A < N) : ∃ c ∈ N, c ∉ A ∧ c ^ p ∈ A := by
  have := Fact.mk hp
  obtain ⟨n, hnN, hnA⟩ : ∃ n ∈ N, n ∉ A := by
    by_contra hcon
    exact hlt.ne (le_antisymm hlt.le (fun x hx => by_contra (fun hxA => hcon ⟨x, hx, hxA⟩)))
  set f : P →* P ⧸ A := QuotientGroup.mk' A with hf
  have hn1 : f n ≠ 1 := by
    intro h
    exact hnA ((QuotientGroup.eq_one_iff n).mp h)
  obtain ⟨s, hs⟩ := (IsPGroup.iff_orderOf.mp (hP.to_quotient A)) (f n)
  have hs1 : s ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hs
    exact hn1 hs
  refine ⟨n ^ (p ^ (s - 1)), N.pow_mem hnN _, ?_, ?_⟩
  · intro h
    have h1 : f n ^ (p ^ (s - 1)) = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr h
    have h2 : orderOf (f n) ∣ p ^ (s - 1) := orderOf_dvd_of_pow_eq_one h1
    rw [hs] at h2
    have h3 := Nat.le_of_dvd (pow_pos hp.pos _) h2
    have h4 : p ^ (s - 1) < p ^ s := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  · have h1 : f ((n ^ (p ^ (s - 1))) ^ p) = 1 := by
      rw [map_pow, map_pow, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ s), ← hs]
      exact pow_orderOf_eq_one _
    exact (QuotientGroup.eq_one_iff _).mp h1

theorem exists_central_mod (hp : p.Prime) (hP : IsPGroup p P) {A N : Subgroup P} [A.Normal]
    [N.Normal] (hlt : A < N) : ∃ c ∈ N, c ∉ A ∧ ∀ g : P, g * c * g⁻¹ * c⁻¹ ∈ A := by
  have := Fact.mk hp
  obtain ⟨n, hnN, hnA⟩ : ∃ n ∈ N, n ∉ A := by
    by_contra hcon
    exact hlt.ne (le_antisymm hlt.le (fun x hx => by_contra (fun hxA => hcon ⟨x, hx, hxA⟩)))
  set f : P →* P ⧸ A := QuotientGroup.mk' A with hf
  have hfs : Function.Surjective f := QuotientGroup.mk'_surjective A
  have hN' : (N.map f).Normal := Subgroup.Normal.map inferInstance f hfs
  have hnil : Group.IsNilpotent (P ⧸ A) := (hP.to_quotient A).isNilpotent
  have hne : N.map f ≠ ⊥ := by
    intro h
    have : f n ∈ N.map f := Subgroup.mem_map_of_mem f hnN
    rw [h, Subgroup.mem_bot] at this
    exact hnA ((QuotientGroup.eq_one_iff n).mp this)
  have h2 := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := N.map f) hne
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h2
  obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨c, hcN, hcx⟩ := Subgroup.mem_map.mp hxN
  refine ⟨c, hcN, ?_, fun g => ?_⟩
  · intro hcA
    apply hx1
    have hx2 : x = 1 := by
      rw [← hcx]
      exact (QuotientGroup.eq_one_iff c).mpr hcA
    exact Subtype.ext hx2
  · rw [← QuotientGroup.eq_one_iff]
    change f (g * c * g⁻¹ * c⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcx]
    have := Subgroup.mem_center_iff.mp hxC (f g)
    calc f g * x * (f g)⁻¹ * x⁻¹ = (f g * x) * (f g)⁻¹ * x⁻¹ := by group
      _ = (x * f g) * (f g)⁻¹ * x⁻¹ := by rw [this]
      _ = 1 := by group

theorem exists_normal_Ep2 (hp : p.Prime) (hP : IsPGroup p P) {W : Subgroup P} [W.Normal]
    (hW : Open.IsElemAbelian p W) (hcard : p ^ 2 ≤ Nat.card W) :
    ∃ E : Subgroup P, E.Normal ∧ E ≤ W ∧ Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have := Fact.mk hp
  have hWel := isElemAbelian_iff.mp hW
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hWne : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have h2 := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := W) hWne
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h2
  obtain ⟨hzW, hzC⟩ := Subgroup.mem_inf.mp hz
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzp : z ^ p = 1 := hWel.2 z hzW
  have hzcent : ∀ g : P, g * z = z * g := Subgroup.mem_center_iff.mp hzC
  have hZ1n : (zpowers z).Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzC)
  have hZ1lt : zpowers z < W := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hzW) (fun h => ?_)
    have h1 : Nat.card ↥(zpowers z) = Nat.card ↥W := by rw [h]
    rw [Nat.card_zpowers, orderOf_eq_prime hzp hz1'] at h1
    have : p < p ^ 2 := by
      have := hp.one_lt
      nlinarith
    omega
  obtain ⟨c, hcW, hcZ, hcc⟩ := exists_central_mod hp hP hZ1lt
  have hcp : c ^ p = 1 := hWel.2 c hcW
  have hc1 : c ≠ 1 := fun h => hcZ (h ▸ one_mem _)
  obtain ⟨hel, hEcard⟩ := isElemAbelian_card_sup_zpowers hp hzp hcp hz1' hcZ
    (hWel.1 z hzW c hcW)
  refine ⟨zpowers z ⊔ zpowers c, ?_, sup_le (Subgroup.zpowers_le.mpr hzW)
    (Subgroup.zpowers_le.mpr hcW), hel, hEcard⟩
  have hconj : ∀ g : P, g * c * g⁻¹ ∈ zpowers z ⊔ zpowers c := by
    intro g
    have h1 : g * c * g⁻¹ = (g * c * g⁻¹ * c⁻¹) * c := by group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hcc g)) (Subgroup.mem_sup_right
      (Subgroup.mem_zpowers c))
  have hle : ∀ g : P, (zpowers z ⊔ zpowers c).map (MulAut.conj g).toMonoidHom ≤
      zpowers z ⊔ zpowers c := by
    intro g
    rw [Subgroup.map_le_iff_le_comap]
    refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨m, rfl⟩ := hx
      rw [Subgroup.mem_comap]
      change g * z ^ m * g⁻¹ ∈ _
      have : g * z ^ m * g⁻¹ = z ^ m := by
        have := (Commute.zpow_right (show Commute g z from hzcent g) m).eq
        rw [this]
        group
      rw [this]
      exact Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers z m)
    · intro x hx
      obtain ⟨m, rfl⟩ := hx
      rw [Subgroup.mem_comap]
      change g * c ^ m * g⁻¹ ∈ _
      have : g * c ^ m * g⁻¹ = (g * c * g⁻¹) ^ m := by rw [conj_zpow]
      rw [this]
      exact zpow_mem (hconj g) m
  refine ⟨fun x hx g => ?_⟩
  exact hle g ⟨x, hx, rfl⟩

omit [Finite P] in
theorem exists_maximal_normal_abelian [Finite P] (Q : Subgroup P) :
    ∃ A : Subgroup P, A ≤ Q ∧ A.Normal ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
      ∀ B : Subgroup P, B ≤ Q → B.Normal → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
        Nat.card B ≤ Nat.card A := by
  let S : Set ℕ := {n | ∃ B : Subgroup P, B ≤ Q ∧ B.Normal ∧
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ Nat.card B = n}
  have hne : S.Nonempty := ⟨1, ⊥, bot_le, inferInstance, fun x hx y hy => by
    rw [Subgroup.mem_bot.mp hx]; simp, by simp⟩
  have hbdd : BddAbove S :=
    ⟨Nat.card P, by rintro n ⟨B, -, -, -, rfl⟩; exact Subgroup.card_le_card_group B⟩
  obtain ⟨A, hAQ, hAn, hAab, hAcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨A, hAQ, hAn, hAab, fun B hBQ hBn hBab => ?_⟩
  rw [hAcard]
  exact le_csSup hbdd ⟨B, hBQ, hBn, hBab, rfl⟩

universe u

theorem isCyclic_of_card_roots_le (hp : p.Prime) :
    ∀ e : ℕ, ∀ (G : Type u) [CommGroup G] [Finite G], Nat.card G = p ^ e →
      Nat.card {x : G // x ^ p = 1} ≤ p → IsCyclic G := by
  intro e
  induction e with
  | zero =>
    intro G _ _ hG _
    have : Subsingleton G := Finite.card_le_one_iff_subsingleton.mp (by simp [hG])
    infer_instance
  | succ e ih =>
    intro G _ _ hG hroots
    have := Fact.mk hp
    rcases Nat.eq_zero_or_pos e with rfl | he
    · exact isCyclic_of_prime_card (by simpa using hG)
    · have hGp : IsPGroup p G := IsPGroup.of_card hG
      let φ : G →* G := powMonoidHom p
      have hkerelem : ∀ x : G, x ∈ φ.ker ↔ x ^ p = 1 := fun x => by
        rw [MonoidHom.mem_ker]; rfl
      have hkercard : Nat.card φ.ker ≤ p := by
        refine le_trans (Nat.card_le_card_of_injective
          (fun x : φ.ker => (⟨(x : G), (hkerelem x).mp x.2⟩ : {x : G // x ^ p = 1}))
          (fun a b h => Subtype.ext (congrArg Subtype.val h))) hroots
      have hpdvd : p ∣ Nat.card G := by rw [hG]; exact dvd_pow_self p (by omega)
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpdvd
      have hgker : g ∈ φ.ker := (hkerelem g).mpr (by rw [← hg]; exact pow_orderOf_eq_one g)
      have hg1 : g ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hg
        exact hp.one_lt.ne hg
      have hkerp : Nat.card φ.ker = p := by
        obtain ⟨t, ht⟩ := IsPGroup.iff_card.mp (hGp.to_subgroup φ.ker)
        have hktp : p ^ t ≤ p := ht ▸ hkercard
        have : t ≠ 0 := by
          rintro rfl
          have h1 : Nat.card φ.ker = 1 := by simpa using ht
          have := Subgroup.eq_bot_of_card_eq _ h1
          exact hg1 (Subgroup.mem_bot.mp (this ▸ hgker))
        have hne : p ^ t ≠ 1 := (Nat.one_lt_pow this hp.one_lt).ne'
        rw [ht]
        refine le_antisymm hktp ?_
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ t := Nat.pow_le_pow_right hp.pos (by omega)
      have hrangecard : Nat.card φ.range = p ^ e := by
        have h1 := Subgroup.card_mul_index φ.ker
        rw [Subgroup.index_ker, hkerp, hG] at h1
        rw [pow_succ'] at h1
        exact Nat.eq_of_mul_eq_mul_left hp.pos h1
      have hrangeCyc : IsCyclic φ.range := by
        refine ih φ.range hrangecard ?_
        refine le_trans (Nat.card_le_card_of_injective
          (fun y : {y : φ.range // y ^ p = 1} =>
            (⟨(y.1 : G), by simpa using congrArg Subtype.val y.2⟩ : {x : G // x ^ p = 1}))
          ?_) hroots
        intro a b h
        have h' : ((a.1 : φ.range) : G) = ((b.1 : φ.range) : G) := by
          have := congrArg (fun z : {x : G // x ^ p = 1} => (z : G)) h
          simpa using this
        exact Subtype.ext (Subtype.ext h')
      obtain ⟨r, hr⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hrangeCyc
      obtain ⟨x, hx⟩ := r.2
      have hxp : x ^ p = (r : G) := hx
      have hord : orderOf (x ^ p) = p ^ e := by
        rw [hxp, Subgroup.orderOf_coe, hr, hrangecard]
      obtain ⟨t, ht⟩ := IsPGroup.iff_orderOf.mp hGp x
      have ht1 : t ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at ht
        rw [ht, one_pow, orderOf_one] at hord
        have : 1 < p ^ e := Nat.one_lt_pow (by omega) hp.one_lt
        omega
      have hdiv : p ∣ orderOf x := by rw [ht]; exact dvd_pow_self p ht1
      have h2 := orderOf_pow_of_dvd hp.ne_zero hdiv
      rw [h2, ht] at hord
      have hpt : p ^ t = p ^ (e + 1) := by
        have h3 : p ^ t / p = p ^ e := hord
        have h4 : p ^ t = p * (p ^ t / p) := (Nat.mul_div_cancel' (dvd_pow_self p ht1)).symm
        rw [pow_succ, h4, h3, mul_comm]
      exact isCyclic_of_orderOf_eq_card x (by rw [ht, hpt, hG])

omit [Finite P] in
@[expose] def torsionSub (p : ℕ) (A : Subgroup P) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Subgroup P where
  carrier := {x | x ∈ A ∧ x ^ p = 1}
  mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
    rw [(show Commute a b from hA a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨A.one_mem, one_pow p⟩
  inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

omit [Finite P] in
theorem torsionSub_normal {A : Subgroup P} [hAn : A.Normal]
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : (torsionSub p A hA).Normal :=
  ⟨fun x hx g => ⟨hAn.conj_mem x hx.1 g, by rw [conj_pow, hx.2]; group⟩⟩

omit [Finite P] in
theorem isElemAbelian_torsionSub {A : Subgroup P} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Open.IsElemAbelian p (torsionSub p A hA) := by
  rw [isElemAbelian_iff]
  exact ⟨fun x hx y hy => hA x hx.1 y hy.1, fun x hx => hx.2⟩

theorem isCyclic_of_no_normal_Ep2 (hp : p.Prime) (hP : IsPGroup p P) {A : Subgroup P} [A.Normal]
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hstar : ∀ E : Subgroup P, E.Normal → E ≤ A → Open.IsElemAbelian p E →
      Nat.card E = p ^ 2 → False) : IsCyclic A := by
  have := Fact.mk hp
  have hWn := torsionSub_normal (p := p) hA
  have hWel := isElemAbelian_torsionSub (p := p) hA
  have hWA : torsionSub p A hA ≤ A := fun x hx => hx.1
  have hW : Nat.card (torsionSub p A hA) ≤ p := by
    by_contra hcon
    obtain ⟨s, hs⟩ := IsElemAbelian.exists_card hp hWel
    rw [hs] at hcon
    have hs2 : 2 ≤ s := by
      by_contra h1
      have : s ≤ 1 := by omega
      have : p ^ s ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos this
      rw [pow_one] at this
      omega
    obtain ⟨E, hEn, hEW, hEel, hEcard⟩ := exists_normal_Ep2 hp hP hWel
      (by rw [hs]; exact Nat.pow_le_pow_right hp.pos hs2)
    exact hstar E hEn (hEW.trans hWA) hEel hEcard
  let _ : CommGroup A := { (inferInstance : Group A) with
    mul_comm := fun a b => Subtype.ext (hA a.1 a.2 b.1 b.2) }
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp (hP.to_subgroup A)
  refine isCyclic_of_card_roots_le hp e A he ?_
  refine le_trans (Nat.card_le_card_of_injective
    (fun x : {x : A // x ^ p = 1} =>
      (⟨(x.1 : P), x.1.2, by simpa using congrArg Subtype.val x.2⟩ : torsionSub p A hA))
    ?_) hW
  intro a b h
  have h' : ((a.1 : A) : P) = ((b.1 : A) : P) := by
    have := congrArg (fun z : torsionSub p A hA => (z : P)) h
    simpa using this
  exact Subtype.ext (Subtype.ext h')

end CFSG.GH74.Uniqueness.SU.SU1
