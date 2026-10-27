module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.Filter.ClassicalOdd.Basic
public import CFSG.GH74.Generic.Certificates
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.Filter.ClassicalOdd CFSG.LocalCores

namespace CFSG.GH74.Generic.S1

theorem exists_lift_q8 {X Y : Type} [Group X] [Finite X] [Group Y] (f : X →* Y)
    (hodd : Odd (Nat.card f.ker)) (ψ : Q8 →* Y) (hψ : ∀ g, ψ g ∈ f.range) :
    ∃ ψ' : Q8 →* X, ∀ g, f (ψ' g) = ψ g := by
  classical
  set R : Subgroup Y := ψ.range with hR
  have hQp : IsPGroup 2 Q8 := IsPGroup.of_card (n := 3) (by rw [Nat.card_eq_fintype_card]; decide)
  have hRp : IsPGroup 2 ↥R := hQp.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  set X' : Subgroup X := R.comap f with hX'
  let g : ↥X' →* ↥R := (f.comp X'.subtype).codRestrict R fun x => x.2
  have hg : Function.Surjective g := by
    rintro ⟨r, hr⟩
    obtain ⟨g', rfl⟩ := hr
    obtain ⟨x, hx⟩ := hψ g'
    exact ⟨⟨x, by rw [hX', mem_comap, hx]; exact ⟨g', rfl⟩⟩, Subtype.ext hx⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥X') := inferInstance
  have hTR : (⊤ : Subgroup ↥R) = (T.mapSurjective hg : Subgroup ↥R) :=
    (T.mapSurjective hg).is_maximal' (hRp.to_subgroup ⊤) le_top
  rw [Sylow.coe_mapSurjective] at hTR
  let gT : ↥(T : Subgroup ↥X') →* ↥R := g.comp (T : Subgroup ↥X').subtype
  have hgT : Function.Surjective gT := by
    intro r
    have : r ∈ (T : Subgroup ↥X').map g := hTR ▸ Subgroup.mem_top r
    obtain ⟨t, ht, rfl⟩ := this
    exact ⟨⟨t, ht⟩, rfl⟩
  have hgTi : Function.Injective gT := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have hf1 : f ((t : ↥X') : X) = 1 := congrArg Subtype.val ht
    have hker : ((t : ↥X') : X) ∈ f.ker := hf1
    have h1 : orderOf (⟨((t : ↥X') : X), hker⟩ : ↥f.ker) ∣ Nat.card f.ker :=
      orderOf_dvd_natCard _
    have h1' : orderOf ((t : ↥X') : X) ∣ Nat.card f.ker := by
      rwa [Subgroup.orderOf_mk] at h1
    obtain ⟨k, hk⟩ := T.2 t
    have h2 : orderOf ((t : ↥X') : X) ∣ 2 ^ k := by
      have : (((t : ↥X') : X)) ^ (2 ^ k) = 1 := by
        have := congrArg (fun z : ↥T => (((z : ↥X')) : X)) hk
        simpa using this
      exact orderOf_dvd_of_pow_eq_one this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card f.ker) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
    have h3 : orderOf ((t : ↥X') : X) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h1'
    have h4 : ((t : ↥X') : X) = 1 := orderOf_eq_one_iff.1 h3
    exact Subtype.ext (Subtype.ext h4)
  let eT : ↥(T : Subgroup ↥X') ≃* ↥R := MulEquiv.ofBijective gT ⟨hgTi, hgT⟩
  refine ⟨(X'.subtype.comp (T : Subgroup ↥X').subtype).comp
    (eT.symm.toMonoidHom.comp ψ.rangeRestrict), fun a => ?_⟩
  have h5 : gT (eT.symm (ψ.rangeRestrict a)) = ψ.rangeRestrict a := eT.apply_symm_apply _
  have h6 := congrArg Subtype.val h5
  exact h6

section Lam

variable {H : Type} [Group H] {M D B : Subgroup H}

theorem mk_eq_of_decomp (hDM : ∀ d ∈ D, ∀ m ∈ M, d * m = m * d) {m m' d d' : H} (hm : m ∈ M)
    (hm' : m' ∈ M) (hd : d ∈ D) (hd' : d' ∈ D) (h : m * d = m' * d') :
    (QuotientGroup.mk (⟨m, hm⟩ : ↥M) : ↥M ⧸ center ↥M) = QuotientGroup.mk ⟨m', hm'⟩ := by
  have h1 : m⁻¹ * m' = d * d'⁻¹ := by
    calc m⁻¹ * m' = m⁻¹ * (m' * d') * d'⁻¹ := by group
      _ = m⁻¹ * (m * d) * d'⁻¹ := by rw [h]
      _ = d * d'⁻¹ := by group
  rw [QuotientGroup.eq]
  rw [Subgroup.mem_center_iff]
  intro g
  have hdd : d * d'⁻¹ ∈ D := D.mul_mem hd (D.inv_mem hd')
  have := hDM _ hdd (g : H) g.2
  apply Subtype.ext
  show (g : H) * (m⁻¹ * m') = m⁻¹ * m' * (g : H)
  rw [h1]
  exact this.symm

noncomputable def lamFun (hdec : ∀ j ∈ B, ∃ m ∈ M, ∃ d ∈ D, j = m * d) (j : ↥B) : ↥M ⧸ center ↥M :=
  QuotientGroup.mk ⟨(hdec j j.2).choose, (hdec j j.2).choose_spec.1⟩

theorem lamFun_eq (hDM : ∀ d ∈ D, ∀ m ∈ M, d * m = m * d)
    (hdec : ∀ j ∈ B, ∃ m ∈ M, ∃ d ∈ D, j = m * d) (j : ↥B) {m d : H} (hm : m ∈ M) (hd : d ∈ D)
    (h : (j : H) = m * d) :
    lamFun hdec j = QuotientGroup.mk ⟨m, hm⟩ := by
  obtain ⟨hm', d', hd', hjd⟩ := (hdec j j.2).choose_spec
  exact mk_eq_of_decomp hDM (m := (hdec j j.2).choose) (m' := m) (d := d') (d' := d) hm'
    hm hd' hd (by rw [← hjd, h])

noncomputable def lamHom (hDM : ∀ d ∈ D, ∀ m ∈ M, d * m = m * d)
    (hdec : ∀ j ∈ B, ∃ m ∈ M, ∃ d ∈ D, j = m * d) : ↥B →* ↥M ⧸ center ↥M where
  toFun := lamFun hdec
  map_one' := by
    have := lamFun_eq hDM hdec 1 (m := 1) (d := 1) M.one_mem D.one_mem (by simp)
    rw [this]
    rfl
  map_mul' j₁ j₂ := by
    obtain ⟨m₁, hm₁, d₁, hd₁, h₁⟩ := hdec j₁ j₁.2
    obtain ⟨m₂, hm₂, d₂, hd₂, h₂⟩ := hdec j₂ j₂.2
    have hc : d₁ * m₂ = m₂ * d₁ := hDM d₁ hd₁ m₂ hm₂
    have hprod : ((j₁ * j₂ : ↥B) : H) = (m₁ * m₂) * (d₁ * d₂) := by
      calc ((j₁ * j₂ : ↥B) : H) = (m₁ * d₁) * (m₂ * d₂) := by
            show (j₁ : H) * j₂ = _
            rw [h₁, h₂]
        _ = m₁ * (d₁ * m₂) * d₂ := by group
        _ = m₁ * (m₂ * d₁) * d₂ := by rw [hc]
        _ = (m₁ * m₂) * (d₁ * d₂) := by group
    have e1 := lamFun_eq hDM hdec (j₁ * j₂) (M.mul_mem hm₁ hm₂) (D.mul_mem hd₁ hd₂) hprod
    have e2 := lamFun_eq hDM hdec j₁ hm₁ hd₁ h₁
    have e3 := lamFun_eq hDM hdec j₂ hm₂ hd₂ h₂
    show lamFun hdec (j₁ * j₂) = lamFun hdec j₁ * lamFun hdec j₂
    rw [e1, e2, e3]
    rfl

theorem lamHom_eq (hDM : ∀ d ∈ D, ∀ m ∈ M, d * m = m * d)
    (hdec : ∀ j ∈ B, ∃ m ∈ M, ∃ d ∈ D, j = m * d) (j : ↥B) {m d : H} (hm : m ∈ M) (hd : d ∈ D)
    (h : (j : H) = m * d) : lamHom hDM hdec j = QuotientGroup.mk ⟨m, hm⟩ :=
  lamFun_eq hDM hdec j hm hd h

theorem mem_of_lamHom_eq_one (hDM : ∀ d ∈ D, ∀ m ∈ M, d * m = m * d)
    (hZD : ∀ z ∈ center ↥M, (z : H) ∈ D)
    (hdec : ∀ j ∈ B, ∃ m ∈ M, ∃ d ∈ D, j = m * d) (j : ↥B) (h1 : lamHom hDM hdec j = 1) :
    (j : H) ∈ D := by
  obtain ⟨m, hm, d, hd, h⟩ := hdec j j.2
  rw [lamHom_eq hDM hdec j hm hd h] at h1
  have hz : (⟨m, hm⟩ : ↥M) ∈ center ↥M := (QuotientGroup.eq_one_iff _).1 h1
  rw [h]
  exact D.mul_mem (hZD _ hz) hd

end Lam


section Core

variable {H : Type} [Group H] [Finite H]

theorem jcentral_of_odd_center (hH : Gen4 H) {M D B A : Subgroup H}
    (hZ : Odd (Nat.card (center ↥M))) (hDM : ∀ d ∈ D, ∀ m ∈ M, d * m = m * d)
    (hdec : ∀ j ∈ B, ∃ m ∈ M, ∃ d ∈ D, j = m * d) (hBq : IsQuasisimple ↥B) {cb : H} (hcbD : cb ∈ D)
    (hcb1 : cb ≠ 1) (hBcen : ∀ z ∈ B, (∀ w ∈ B, z * w = w * z) → z = 1 ∨ z = cb)
    (ψB : Q8 →* H) (hψB : ∀ g, ψB g ∈ B) (hψBi : Function.Injective ψB)
    (hψBc : ψB (QuaternionGroup.a 2) = cb) (hAM : A ≤ M)
    (hAodd : ∀ z ∈ A, (∀ w ∈ A, z * w = w * z) → Odd (orderOf z))
    (ψA : Q8 →* H) (hψAi : Function.Injective ψA) (hψA : ∀ g, ψA g ∈ A)
    (hAB : ∀ a ∈ A, ∀ j ∈ B, a * j = j * a) :
    ∀ j ∈ B, ∀ m ∈ M, j * m = m * j := by
  have hq4 : ∀ g : Q8, g ^ 4 = 1 := by decide
  have hsqQ : ∀ g : Q8, g ^ 2 = 1 ∨ g ^ 2 = QuaternionGroup.a 2 := by decide
  have hoddMD : ∀ x : H, x ∈ M → x ∈ D → Odd (orderOf x) := by
    intro x hxM hxD
    have hz : (⟨x, hxM⟩ : ↥M) ∈ center ↥M := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (hDM x hxD g g.2).symm
    have h1 : orderOf (⟨x, hxM⟩ : ↥M) ∣ Nat.card (center ↥M) := by
      have := Subgroup.orderOf_dvd_natCard (center ↥M) hz
      exact this
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hZ h1
  have h4MD : ∀ x : H, x ∈ M → x ∈ D → x ^ 4 = 1 → x = 1 := by
    intro x hxM hxD hx4
    have h2 : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
    have hodd := hoddMD x hxM hxD
    obtain ⟨k, hk⟩ := hodd
    have hle := Nat.le_of_dvd (by norm_num) h2
    have : k ≤ 1 := by omega
    interval_cases k
    · exact orderOf_eq_one_iff.1 (by omega)
    · exfalso
      rw [hk] at h2
      omega
  have hBnorm : ∀ b ∈ B, ∀ m ∈ M, b * m * b⁻¹ ∈ M := by
    intro b hb m hm
    obtain ⟨mb, hmb, db, hdb, rfl⟩ := hdec b hb
    have hc := hDM db hdb m hm
    have : mb * db * m * (mb * db)⁻¹ = mb * m * mb⁻¹ := by
      calc mb * db * m * (mb * db)⁻¹ = mb * (db * m) * db⁻¹ * mb⁻¹ := by group
        _ = mb * (m * db) * db⁻¹ * mb⁻¹ := by rw [hc]
        _ = mb * m * mb⁻¹ := by group
    rw [this]
    exact M.mul_mem (M.mul_mem hmb hm) (M.inv_mem hmb)
  by_contra hnot
  push Not at hnot
  let φ : ↥M × ↥D →* H := M.subtype.noncommCoprod D.subtype
    (fun m d => (hDM d d.2 m m.2).symm)
  have hφ : ∀ m : ↥M, ∀ d : ↥D, φ (m, d) = (m : H) * d := fun m d => rfl
  have hker : Odd (Nat.card φ.ker) := by
    let κ : ↥φ.ker →* ↥(center ↥M) :=
      { toFun := fun x => ⟨x.1.1, by
          have h1 : (x.1.1 : H) * x.1.2 = 1 := by
            have := x.2
            rw [MonoidHom.mem_ker, hφ] at this
            exact this
          have hmD : (x.1.1 : H) ∈ D := by
            have : (x.1.1 : H) = ((x.1.2 : ↥D) : H)⁻¹ := eq_inv_of_mul_eq_one_left h1
            rw [this]
            exact D.inv_mem x.1.2.2
          rw [Subgroup.mem_center_iff]
          intro g
          apply Subtype.ext
          exact (hDM _ hmD g g.2).symm⟩
        map_one' := rfl
        map_mul' := fun x y => rfl }
    have hκ : Function.Injective κ := by
      intro x y hxy
      have hm : x.1.1 = y.1.1 := congrArg (fun z : ↥(center ↥M) => z.1) hxy
      have hx : (x.1.1 : H) * x.1.2 = 1 := by
        have := x.2
        rw [MonoidHom.mem_ker, hφ] at this
        exact this
      have hy : (y.1.1 : H) * y.1.2 = 1 := by
        have := y.2
        rw [MonoidHom.mem_ker, hφ] at this
        exact this
      have hd : x.1.2 = y.1.2 := by
        apply Subtype.ext
        have e1 : ((x.1.2 : ↥D) : H) = ((x.1.1 : ↥M) : H)⁻¹ := eq_inv_of_mul_eq_one_right hx
        have e2 : ((y.1.2 : ↥D) : H) = ((y.1.1 : ↥M) : H)⁻¹ := eq_inv_of_mul_eq_one_right hy
        rw [e1, e2, hm]
      exact Subtype.ext (Prod.ext hm hd)
    exact Odd.of_dvd_nat hZ (Subgroup.card_dvd_of_injective κ hκ)
  have hrange : ∀ g, ψB g ∈ φ.range := by
    intro g
    obtain ⟨m, hm, d, hd, h⟩ := hdec (ψB g) (hψB g)
    exact ⟨(⟨m, hm⟩, ⟨d, hd⟩), by rw [hφ]; exact h.symm⟩
  obtain ⟨ψ', hψ'⟩ := exists_lift_q8 φ hker ψB hrange
  let ρM : Q8 →* H := (M.subtype.comp (MonoidHom.fst _ _)).comp ψ'
  let ρD : Q8 →* H := (D.subtype.comp (MonoidHom.snd _ _)).comp ψ'
  have hρ : ∀ g, ψB g = ρM g * ρD g := by
    intro g
    have := hψ' g
    rw [← this]
    rfl
  have hρM : ∀ g, ρM g ∈ M := fun g => ((ψ' g).1).2
  have hρD : ∀ g, ρD g ∈ D := fun g => ((ψ' g).2).2
  have hρ2 : ψB (QuaternionGroup.a 2) = ρM (QuaternionGroup.a 2) * ρD (QuaternionGroup.a 2) :=
    hρ _
  have hcb2 : cb * cb = 1 := by
    rw [← hψBc, ← map_mul]
    have : (QuaternionGroup.a 2 : Q8) * QuaternionGroup.a 2 = 1 := by decide
    rw [this, map_one]
  have hcb4 : cb ^ 4 = 1 := by
    have h2 : cb ^ 2 = 1 := by rw [sq]; exact hcb2
    calc cb ^ 4 = (cb ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [h2, one_pow]
  have hBM : ∀ j ∈ B, j ∈ M → j = 1 := by
    have hN : ((B ⊓ M).subgroupOf B).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
      exact ⟨B.mul_mem (B.mul_mem g.2 hn.1) (B.inv_mem g.2), hBnorm g g.2 n hn.2⟩
    have hcbB : cb ∈ B := hψBc ▸ hψB _
    rcases quasisimple_normal_subgroups hBq hN with htop | hcen
    · exfalso
      have hcbM : cb ∈ M := by
        have : (⟨cb, hcbB⟩ : ↥B) ∈ (B ⊓ M).subgroupOf B := by rw [htop]; trivial
        exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 this)).2
      exact hcb1 (h4MD cb hcbM hcbD hcb4)
    · intro j hjB hjM
      have hj : (⟨j, hjB⟩ : ↥B) ∈ (B ⊓ M).subgroupOf B := Subgroup.mem_subgroupOf.2 ⟨hjB, hjM⟩
      have hc := hcen hj
      rcases hBcen j hjB (fun w hw => by
        have := Subgroup.mem_center_iff.1 hc ⟨w, hw⟩
        exact (congrArg Subtype.val this).symm) with h | h
      · exact h
      · exfalso
        apply hcb1
        rw [h] at hjM
        exact h4MD cb hjM hcbD hcb4
  have hρDi : Function.Injective ρD := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : ψB g = ρM g := by rw [hρ g, hg, mul_one]
    have : ψB g = 1 := hBM _ (hψB g) (h1 ▸ hρM g)
    apply hψBi
    rw [this, map_one]
  have hρM2 : ρM (QuaternionGroup.a 2) = 1 := by
    have hD2 : ρM (QuaternionGroup.a 2) ∈ D := by
      have : ρM (QuaternionGroup.a 2) = cb * (ρD (QuaternionGroup.a 2))⁻¹ := by
        rw [← hψBc, hρ2]; group
      rw [this]
      exact D.mul_mem hcbD (D.inv_mem (hρD _))
    refine h4MD _ (hρM _) hD2 ?_
    rw [← map_pow, hq4, map_one]
  have hρMsq : ∀ g, ρM g * ρM g = 1 := by
    intro g
    rw [← map_mul, ← sq]
    rcases hsqQ g with h | h
    · rw [h, map_one]
    · rw [h, hρM2]
  let R : Subgroup H := ρM.range
  have hRsq : ∀ r ∈ R, r * r = 1 := by
    rintro _ ⟨g, rfl⟩
    exact hρMsq g
  have hRcomm : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := by
    intro r hr s hs
    have h1 := hRsq _ (R.mul_mem hr hs)
    have e1 : r⁻¹ = r := by rw [inv_eq_iff_mul_eq_one]; exact hRsq r hr
    have e2 : s⁻¹ = s := by rw [inv_eq_iff_mul_eq_one]; exact hRsq s hs
    have e3 : (r * s)⁻¹ = r * s := by rw [inv_eq_iff_mul_eq_one]; exact h1
    calc r * s = (r * s)⁻¹ := e3.symm
      _ = s⁻¹ * r⁻¹ := by rw [mul_inv_rev]
      _ = s * r := by rw [e1, e2]
  have hRM : ∀ r ∈ R, r ∈ M := by
    rintro _ ⟨g, rfl⟩
    exact hρM g
  have hRA : ∀ r ∈ R, ∀ a ∈ A, a * r = r * a := by
    rintro _ ⟨g, rfl⟩ a ha
    have e : ρM g = ψB g * (ρD g)⁻¹ := by rw [hρ g]; group
    rw [e]
    have h1 : a * ψB g = ψB g * a := hAB a ha _ (hψB g)
    have h2 : a * (ρD g)⁻¹ = (ρD g)⁻¹ * a :=
      (hDM (ρD g)⁻¹ (D.inv_mem (hρD g)) a (hAM ha)).symm
    calc a * (ψB g * (ρD g)⁻¹) = (a * ψB g) * (ρD g)⁻¹ := by group
      _ = (ψB g * a) * (ρD g)⁻¹ := by rw [h1]
      _ = ψB g * (a * (ρD g)⁻¹) := by group
      _ = ψB g * ((ρD g)⁻¹ * a) := by rw [h2]
      _ = ψB g * (ρD g)⁻¹ * a := by group
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hall : ∀ g, ρM g = 1 := by
      intro g
      have : ρM g ∈ R := ⟨g, rfl⟩
      rw [hbot] at this
      exact this
    have hψBD : ∀ g, ψB g ∈ D := fun g => by rw [hρ g, hall g, one_mul]; exact hρD g
    let C : Subgroup ↥B := (centralizer (M : Set H)).comap B.subtype
    have hCn : C.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hn ⊢
      intro m hm
      have hm' : (g : H)⁻¹ * m * (g : H) ∈ M := by
        have := hBnorm ((g : H)⁻¹) (B.inv_mem g.2) m hm
        simpa using this
      have h1 : ((g : H)⁻¹ * m * (g : H)) * (n : H) = (n : H) * ((g : H)⁻¹ * m * (g : H)) := hn _ hm'
      show m * ((g : H) * (n : H) * (g : H)⁻¹) = (g : H) * (n : H) * (g : H)⁻¹ * m
      calc m * ((g : H) * (n : H) * (g : H)⁻¹)
          = (g : H) * (((g : H)⁻¹ * m * (g : H)) * (n : H)) * (g : H)⁻¹ := by group
        _ = (g : H) * ((n : H) * ((g : H)⁻¹ * m * (g : H))) * (g : H)⁻¹ := by rw [h1]
        _ = (g : H) * (n : H) * (g : H)⁻¹ * m := by group
    have hxC : (⟨ψB (QuaternionGroup.xa 0), hψB _⟩ : ↥B) ∈ C := by
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro m hm
      exact (hDM _ (hψBD _) m hm).symm
    rcases quasisimple_normal_subgroups hBq hCn with htop | hcen
    · obtain ⟨j, hj, m, hm, hne⟩ := hnot
      have : (⟨j, hj⟩ : ↥B) ∈ C := by rw [htop]; trivial
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at this
      exact hne (this m hm).symm
    · have hz := hcen hxC
      rcases hBcen _ (hψB (QuaternionGroup.xa 0)) (fun w hw => by
        have := Subgroup.mem_center_iff.1 hz ⟨w, hw⟩
        exact (congrArg Subtype.val this).symm) with h | h
      · have := hψBi (h.trans (map_one ψB).symm)
        exact absurd this (by decide)
      · have := hψBi (h.trans hψBc.symm)
        exact absurd this (by decide)
  have c1 : ∀ (a : Q8) (r : ↥R), Commute (ψA a) (R.subtype r) := fun a r =>
    hRA r r.2 (ψA a) (hψA a)
  let α₁ : Q8 × ↥R →* H := ψA.noncommCoprod R.subtype c1
  have hα₁ : ∀ x : Q8 × ↥R, α₁ x = ψA x.1 * (x.2 : H) := fun x => rfl
  have c2 : ∀ (x : Q8 × ↥R) (b : Q8), Commute (α₁ x) (ρD b) := by
    intro x b
    have hx : α₁ x ∈ M := by
      rw [hα₁]
      exact M.mul_mem (hAM (hψA x.1)) (hRM _ x.2.2)
    exact (hDM _ (hρD b) _ hx).symm
  let α : (Q8 × ↥R) × Q8 →* H := α₁.noncommCoprod ρD c2
  have hα : ∀ k : (Q8 × ↥R) × Q8, α k = ψA k.1.1 * (k.1.2 : H) * ρD k.2 := fun k => rfl
  let β : (Q8 × ↥R) × Q8 →* (V4 × ↥R) × V4 :=
    (q8Frattini.prodMap (MonoidHom.id ↥R)).prodMap q8Frattini
  have hβ : Function.Surjective β := by
    rintro ⟨⟨v₁, r⟩, v₂⟩
    obtain ⟨a₁, ha₁⟩ := q8Frattini_surjective v₁
    obtain ⟨a₂, ha₂⟩ := q8Frattini_surjective v₂
    exact ⟨((a₁, r), a₂), by simp [β, ha₁, ha₂]⟩
  have hAcomm : ∀ a b : (V4 × ↥R) × V4, a * b = b * a := by
    intro a b
    exact Prod.ext (Prod.ext (mul_comm _ _) (Subtype.ext (hRcomm _ a.1.2.2 _ b.1.2.2)))
      (mul_comm _ _)
  have hAsq : ∀ a : (V4 × ↥R) × V4, a ^ 2 = 1 := by
    intro a
    have hv : ∀ v : V4, v ^ 2 = 1 := by decide
    refine Prod.ext (Prod.ext (hv _) (Subtype.ext ?_)) (hv _)
    show ((a.1.2 : ↥R) : H) ^ 2 = 1
    rw [sq]
    exact hRsq _ a.1.2.2
  have hcard : 2 ^ 4 < Nat.card ((V4 × ↥R) × V4) := by
    rw [Nat.card_prod, Nat.card_prod, card_V4]
    have : 1 < Nat.card ↥R := (Subgroup.one_lt_card_iff_ne_bot R).2 hRne
    nlinarith
  have hkerαβ : α.ker ≤ β.ker := by
    rintro ⟨⟨a₁, r⟩, a₃⟩ hk
    rw [MonoidHom.mem_ker] at hk
    have hk' : ψA a₁ * (r : H) * ρD a₃ = 1 := hk
    have e1 : ρD a₃ = (ψA a₁ * (r : H))⁻¹ := eq_inv_of_mul_eq_one_right hk'
    have hM1 : ρD a₃ ∈ M := by
      rw [e1]
      exact M.inv_mem (M.mul_mem (hAM (hψA a₁)) (hRM _ r.2))
    have h1 : ρD a₃ = 1 := h4MD _ hM1 (hρD a₃) (by rw [← map_pow, hq4, map_one])
    have ha₃ : a₃ = 1 := hρDi (by rw [h1, map_one])
    have hk2 : ψA a₁ * (r : H) = 1 := by rw [h1, mul_one] at hk'; exact hk'
    have hrinv : (r : H) = (ψA a₁)⁻¹ := eq_inv_of_mul_eq_one_right hk2
    have hrA : (r : H) ∈ A := by rw [hrinv]; exact A.inv_mem (hψA a₁)
    have hr1 : (r : H) = 1 := by
      have hodd := hAodd _ hrA (fun w hw => (hRA _ r.2 w hw).symm)
      have h2 : orderOf (r : H) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hRsq _ r.2)
      obtain ⟨k, hk3⟩ := hodd
      have hle := Nat.le_of_dvd (by norm_num) h2
      have : k = 0 := by omega
      subst this
      exact orderOf_eq_one_iff.1 (by omega)
    have ha₁ : a₁ = 1 := by
      apply hψAi
      rw [map_one]
      rw [hr1, mul_one] at hk2
      exact hk2
    have hr : r = 1 := Subtype.ext hr1
    rw [MonoidHom.mem_ker]
    simp [β, ha₁, ha₃, hr]
  exact (not_sectionalTwoRankLE_of_surjection 4 α β hβ hAcomm hAsq hcard hkerαβ) hH

end Core

end CFSG.GH74.Generic.S1
