module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrder

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LieType.Seitz
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.Blueprint.Multiplier
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Lift
open scoped commutatorElement


namespace Gen2318E68Aux

@[expose] def IsE62Index : TauCeti.LieTypeIndex → Prop
  | .E6 q => IsTwoPow q 1
  | _ => False

@[expose] def E68FieldFix : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), IsE6EightIndex d.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ∉ (MulAut.conj : S →* MulAut S).range →
      ∃ H : Subgroup S, (∀ s : S, s ∈ H ↔ β s = s) ∧ Subgroup.center ↥H = ⊥ ∧
        CFSG.Open.IsQuasisimple ↥H ∧
        ∃ d₂ : TauCeti.ValidLieTypeIndex, IsE62Index d₂.1 ∧
          Nonempty (↥H ≃* (TauCeti.CFSGIndex.lie d₂).Group)

theorem center_eq_bot_of_E68 (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (hQ : IsLieQuot Y IsE6EightIndex) :
    Subgroup.center Y = ⊥ := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hQ
  cases d with
  | E6 q =>
    obtain ⟨hq2, hqe⟩ := hd
    have hm := CFSG.Models.lieModel_of_namesTag (t := .E6) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩ ⟨rfl, rfl⟩
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group)
    rw [hq2, hqe] at hm
    have h := center_dvd_table hGA (isQuasisimple_of_open_aux hq) e hm
    have h1 : (genericOrders .E6 0 2 3).1 * (genericOrders .E6 0 2 3).2 *
        ((exceptionalOrders .E6 0 2 3).1 * (exceptionalOrders .E6 0 2 3).2) = 1 := by
      decide
    rw [h1] at h
    exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 h)
  | _ => exact absurd hd (by simp [IsE6EightIndex])

theorem conj_eq_one_mem_center {G : Type*} [Group G] {g : G}
    (h : (MulAut.conj g : MulAut G) = 1) : g ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro x
  have hx : g * x * g⁻¹ = x := congrArg (fun φ : MulAut G => φ x) h
  have hx' : g * x = x * g := by
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [hx]
  exact hx'.symm

theorem conj_injective_of_center_eq_bot {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h := conj_eq_one_mem_center hg
  rw [hZ, Subgroup.mem_bot] at h
  exact h

theorem isElemAbelian_sup_of_comm {Ω : Type*} [Group Ω] {p : ℕ} {P Q : Subgroup Ω}
    (hP : IsElemAbelian p P) (hQ : IsElemAbelian p Q)
    (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) : IsElemAbelian p (P ⊔ Q) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx, u, hu, hxu⟩ := i224_mem_sup_of_comm hc a.2
    obtain ⟨x', hx', u', hu', hxu'⟩ := i224_mem_sup_of_comm hc b.2
    apply Subtype.ext
    change (a : Ω) * b = b * a
    rw [hxu, hxu']
    have e1 : ∀ s ∈ P, ∀ t ∈ P, s * t = t * s := fun s hs t ht =>
      congrArg Subtype.val (hP.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
    have e2 : ∀ s ∈ Q, ∀ t ∈ Q, s * t = t * s := fun s hs t ht =>
      congrArg Subtype.val (hQ.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
    calc x * u * (x' * u') = x * (u * x') * u' := by group
      _ = x * (x' * u) * u' := by rw [← hc x' hx' u hu]
      _ = (x * x') * (u * u') := by group
      _ = (x' * x) * (u' * u) := by rw [e1 x hx x' hx', e2 u hu u' hu']
      _ = x' * (x * u') * u := by group
      _ = x' * (u' * x) * u := by rw [hc x hx u' hu']
      _ = x' * u' * (x * u) := by group
  · obtain ⟨x, hx, u, hu, rfl⟩ := i224_mem_sup_of_comm hc hy
    have hxp : x ^ p = 1 := hP.2 x hx
    have hup : u ^ p = 1 := hQ.2 u hu
    have e1 : Commute x u := hc x hx u hu
    rw [e1.mul_pow, hxp, hup, one_mul]

theorem two_local_card_le {X : Type} [Group X] [Finite X] {E D P : Subgroup X} {k₁ k₂ : ℕ}
    (hE : IsElemAbelian 3 E) (hD : IsElemAbelian 3 D)
    (hc : ∀ x ∈ E, ∀ y ∈ D, x * y = y * x) (hd : E ⊓ D = ⊥)
    (hEN : E ≤ Subgroup.normalizer (P : Set X)) (hDN : D ≤ Subgroup.normalizer (P : Set X))
    (hP : P ≠ ⊥) (hP2 : IsPGroup 2 ↥P)
    (h1 : Nat.card E = 3 ^ k₁) (h2 : Nat.card D = 3 ^ k₂) :
    k₁ + k₂ ≤ GLATwoLocalRank 3 X := by
  have hTel : IsElemAbelian 3 (E ⊔ D) := isElemAbelian_sup_of_comm hE hD hc
  have hTcard : Nat.card ↥(E ⊔ D) = 3 ^ (k₁ + k₂) := by
    rw [i224_card_sup hc hd, h1, h2, pow_add]
  have hTN : E ⊔ D ≤ Subgroup.normalizer (P : Set X) := sup_le hEN hDN
  exact le_glaTwoLocalRank_of_le_normalizer (p := 3) (by norm_num) hP hP2 hTel hTN hTcard

theorem three_dvd_of_zpow_mem {X : Type*} [Group X] {K : Subgroup X} {b : X} (hb3 : b ^ 3 = 1)
    (hnot : ∀ k ∈ K, k⁻¹ * b ∉ Subgroup.centralizer (K : Set X))
    {j : ℤ} {k c : X} (hk : k ∈ K) (hc : c ∈ Subgroup.centralizer (K : Set X))
    (h : b ^ j = k * c) : (3 : ℤ) ∣ j := by
  have hkc : k * c = c * k := Subgroup.mem_centralizer_iff.1 hc k hk
  have hb3' : b ^ (3 : ℤ) = 1 := by simpa using hb3
  have hpow : b ^ j = b ^ (j % 3) := by
    have hj : j = j % 3 + 3 * (j / 3) := by
      rw [Int.emod_def]
      ring
    conv_lhs => rw [hj]
    rw [zpow_add, zpow_mul, hb3', one_zpow, mul_one]
  have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exact Int.dvd_of_emod_eq_zero h0
  · exfalso
    rw [hpow, h1, zpow_one] at h
    apply hnot k hk
    rw [h, inv_mul_cancel_left]
    exact hc
  · exfalso
    rw [hpow, h2] at h
    have hbb : b * b = k * c := by
      rw [← h, zpow_two]
    have hb : b = (k * c) * (k * c) := by
      have h4 : b * b * (b * b) = b := by
        calc b * b * (b * b) = b ^ 3 * b := by simp only [pow_three, mul_assoc]
          _ = b := by rw [hb3, one_mul]
      rw [← hbb, h4]
    apply hnot (k * k) (Subgroup.mul_mem _ hk hk)
    have hc2 : k * c * (k * c) = (k * k) * (c * c) := by
      calc k * c * (k * c) = k * (c * k) * c := by group
        _ = k * (k * c) * c := by rw [← hkc]
        _ = (k * k) * (c * c) := by group
    rw [hb, hc2, inv_mul_cancel_left]
    exact Subgroup.mul_mem _ hc hc

theorem zpow_eq_one_of_three_dvd {X : Type*} [Group X] {b : X} (hb3 : b ^ 3 = 1) {j : ℤ}
    (h : (3 : ℤ) ∣ j) : b ^ j = 1 := by
  obtain ⟨m, rfl⟩ := h
  have hb3' : b ^ (3 : ℤ) = 1 := by simpa using hb3
  rw [zpow_mul, hb3', one_zpow]

theorem mem_center_of_mem_centralizer {X : Type*} [Group X] {K : Subgroup X} {x : X}
    (hxK : x ∈ K) (hx : x ∈ Subgroup.centralizer (K : Set X)) :
    (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.1 hx (g : X) g.2

theorem gen2318Index_of_E62 {d : TauCeti.LieTypeIndex} (h : IsE62Index d) : Gen2318Index d := by
  cases d with
  | E6 q => exact Or.inl h
  | _ => exact h.elim

theorem isRankFour_of_E62 {d : TauCeti.LieTypeIndex} (h : IsE62Index d) : IsRankFourIndex d := by
  cases d with
  | E6 q => exact Or.inl h
  | _ => exact h.elim

theorem rho2318_E62 {d : TauCeti.LieTypeIndex} (h : IsE62Index d) : rho2318 d = 4 := by
  cases d with
  | E6 q =>
    obtain ⟨-, hqe⟩ := h
    simp [rho2318, hqe]
  | _ => exact h.elim

theorem evenScope_of_E68 {d : TauCeti.LieTypeIndex} (h : IsE6EightIndex d) :
    Seitz2313Cover.EvenScope d := by
  cases d with
  | E6 q =>
    obtain ⟨hq2, -⟩ := h
    exact hq2
  | _ => exact h.elim

theorem rank_bound_of_fixed {X : Type} [Group X] [Finite X] {K B : Subgroup X} {b : X}
    {eKS : ↥K ≃* (↥K ⧸ Subgroup.center ↥K)} (hεK : ∀ k : ↥K, eKS k = QuotientGroup.mk k)
    (hZ : Subgroup.center ↥K = ⊥) (hBel : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hbB : b ∈ B)
    (hbN : b ∈ Subgroup.normalizer (K : Set X)) (hb3 : b ^ 3 = 1)
    (hbnot : ∀ k ∈ K, k⁻¹ * b ∉ Subgroup.centralizer (K : Set X))
    (hrk : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B)
    {H : Subgroup (↥K ⧸ Subgroup.center ↥K)}
    (hHfix : ∀ s, s ∈ H ↔ actHom K ⟨b, hbN⟩ s = s)
    (hcart : ∃ E P : Subgroup ↥H, IsElemAbelian 3 E ∧ 4 ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧
      IsPGroup 2 ↥P ∧ E ≤ Subgroup.normalizer (P : Set ↥H))
    {r : ℕ} (hr : autOrderIn B K = 3 ^ r) : 5 ≤ r := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, P, hEel, hE4, hP, hP2, hEN⟩ := hcart
  have hπinj : ∀ a c : ↥K, (QuotientGroup.mk a : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk c → a = c :=
    fun a c h => eKS.injective (by rw [hεK, hεK]; exact h)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥H →* X, ∀ h : ↥H, (ψ h : X) = ((eKS.symm h.1 : ↥K) : X) :=
    ⟨K.subtype.comp (eKS.symm.toMonoidHom.comp H.subtype), fun h => rfl⟩
  have hψinj : Function.Injective ψ := by
    intro h h' hh
    have h1 : eKS.symm h.1 = eKS.symm h'.1 := Subtype.ext (by rw [← hψ, ← hψ]; exact hh)
    have h2 : h.1 = h'.1 := by
      have h3 := congrArg eKS h1
      rwa [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h3
    exact Subtype.ext h2
  have hψK : ∀ h : ↥H, ψ h ∈ K := fun h => by
    rw [hψ]
    exact (eKS.symm h.1).2
  have hkH : ∀ h : ↥H, (QuotientGroup.mk (eKS.symm h.1 : ↥K) : ↥K ⧸ Subgroup.center ↥K) = h.1 := by
    intro h
    rw [← hεK]
    exact eKS.apply_symm_apply h.1
  have hψfix : ∀ h : ↥H, b * ψ h * b⁻¹ = ψ h := by
    intro h
    have hs : actHom K ⟨b, hbN⟩ (QuotientGroup.mk (eKS.symm h.1 : ↥K)) =
        QuotientGroup.mk (eKS.symm h.1 : ↥K) := by
      rw [hkH h]
      exact (hHfix h.1).1 h.2
    rw [actHom_mk] at hs
    have hm : K.normalizerMonoidHom ⟨b, hbN⟩ (eKS.symm h.1) = eKS.symm h.1 := hπinj _ _ hs
    have hc := congrArg Subtype.val hm
    rw [coe_normalizerMonoidHom] at hc
    rw [hψ]
    exact hc
  have hbcomm : ∀ h : ↥H, b * ψ h = ψ h * b := by
    intro h
    have h1 := hψfix h
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hbP : ∀ y ∈ P.map ψ, b * y = y * b := by
    intro y hy
    obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact hbcomm p
  have hPK : ∀ y ∈ P.map ψ, y ∈ K := by
    intro y hy
    obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact hψK p
  have hEX_el : IsElemAbelian 3 (E.map ψ) := CFSG.SectionRank.isElemAbelian_map hEel ψ
  have hEX_card : Nat.card (E.map ψ) = Nat.card E := Subgroup.card_map_of_injective hψinj
  have hPX_ne : P.map ψ ≠ ⊥ := fun h0 => hP ((Subgroup.map_eq_bot_iff_of_injective P hψinj).1 h0)
  have hPX2 : IsPGroup 2 ↥(P.map ψ) := hP2.of_equiv (Subgroup.equivMapOfInjective P ψ hψinj)
  have hEX_N : E.map ψ ≤ Subgroup.normalizer ((P.map ψ : Subgroup X) : Set X) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
    exact Subgroup.le_normalizer_map ψ ⟨e, hEN he, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Subgroup X,
      D = Subgroup.zpowers b ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) := ⟨_, rfl⟩
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hBel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hzB : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.2 hbB
  have hDB : D ≤ B := by
    rw [hD]
    exact sup_le hzB inf_le_left
  have hDel : IsElemAbelian 3 D := i271_isElemAbelian_of_le hBel hDB
  have hC'el : IsElemAbelian 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
    i271_isElemAbelian_of_le hBel inf_le_left
  obtain ⟨c₀, hc₀⟩ := i271_exists_card_eq Nat.prime_three hC'el
  have hpc : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) = c₀ :=
    i271_pRank_eq Nat.prime_three hC'el hc₀
  have hb1 : b ≠ 1 := by
    intro h
    apply hbnot 1 K.one_mem
    rw [h, inv_one, one_mul]
    exact Subgroup.one_mem _
  have hzcard : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hcommZC : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ (B ⊓ Subgroup.centralizer (K : Set X)),
      x * y = y * x := fun x hx y hy => hBcomm x (hzB hx) y (Subgroup.mem_inf.1 hy).1
  have hzC : Subgroup.zpowers b ⊓ (B ⊓ Subgroup.centralizer (K : Set X)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx1
    have hcen : b ^ j ∈ Subgroup.centralizer (K : Set X) := (Subgroup.mem_inf.1 hx2).2
    have h3 : (3 : ℤ) ∣ j :=
      three_dvd_of_zpow_mem hb3 hbnot K.one_mem hcen (by rw [one_mul])
    rw [Subgroup.mem_bot]
    exact zpow_eq_one_of_three_dvd hb3 h3
  have hDcard : Nat.card D = 3 ^ (c₀ + 1) := by
    have h := i224_card_sup hcommZC hzC
    rw [hD, h, hzcard, hc₀, pow_succ']
  have hDN : D ≤ Subgroup.normalizer ((P.map ψ : Subgroup X) : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [hD]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro h hh
      exact (hbP h hh).symm
    · intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 h (hPK h hh)
  have hEX_comm : ∀ x ∈ E.map ψ, ∀ y ∈ D, x * y = y * x := by
    intro x hx y hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
    have hcent : D ≤ Subgroup.centralizer ({ψ e} : Set X) := by
      rw [hD]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff.1 hg]
        exact (hbcomm e).symm
      · intro c hc
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff.1 hg]
        exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 (ψ e) (hψK e)
    exact Subgroup.mem_centralizer_iff.1 (hcent hy) (ψ e) (Set.mem_singleton _)
  have hEX_inter : E.map ψ ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxD⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.1 hxE
    rw [hD] at hxD
    obtain ⟨y, hy, c, hc, hyc⟩ := i224_mem_sup_of_comm hcommZC hxD
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hcC : c ∈ Subgroup.centralizer (K : Set X) := (Subgroup.mem_inf.1 hc).2
    have h' : b ^ j = ψ e * c⁻¹ := by rw [hyc, mul_inv_cancel_right]
    have h3 : (3 : ℤ) ∣ j :=
      three_dvd_of_zpow_mem hb3 hbnot (hψK e) (Subgroup.inv_mem _ hcC) h'
    have h1 : b ^ j = 1 := zpow_eq_one_of_three_dvd hb3 h3
    have hpsi : ψ e ∈ Subgroup.centralizer (K : Set X) := by
      rw [hyc, h1, one_mul]
      exact hcC
    have hcentral := mem_center_of_mem_centralizer (hψK e) hpsi
    have h0 := (Subgroup.eq_bot_iff_forall _).1 hZ _ hcentral
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h0
  obtain ⟨k₁, hk₁⟩ := i271_exists_card_eq Nat.prime_three hEel
  have hk₁4 : 4 ≤ k₁ := by
    have h := i271_pRank_eq Nat.prime_three hEel hk₁
    omega
  have hcount := two_local_card_le hEX_el hDel hEX_comm hEX_inter hEX_N hDN hPX_ne hPX2
    (k₁ := k₁) (k₂ := c₀ + 1) (hEX_card.trans hk₁) hDcard
  have hm := pRank_eq_add_autOrderIn Nat.prime_three hBel hBN hr
  rw [hpc] at hm
  omega

theorem gamma_input {S : Type} [Group S] [Finite S] (A : Subgroup (MulAut S))
    (hAel : IsElemAbelian 3 A) (hcenS : Subgroup.center S = ⊥)
    (hA3 : (MulAut.conj : S →* MulAut S).range.relIndex A ≤ 3)
    {r : ℕ} (hAcard : Nat.card A = 3 ^ r) (hr5 : 5 ≤ r)
    {β : MulAut S} (hβA : β ∈ A) {H : Subgroup S} (hHfix : ∀ s : S, s ∈ H ↔ β s = s)
    (hHcen : Subgroup.center ↥H = ⊥) {d₂ : TauCeti.ValidLieTypeIndex}
    (hd₂ : IsRankFourIndex d₂.1) (eH : ↥H ≃* (TauCeti.CFSGIndex.lie d₂).Group)
    (hRank4 : Gen2318RankFour) :
    ∃ E₀ : Subgroup (MulAut S), E₀ ≤ A ∧ IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 3 ^ 4 ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E₀, ∀ u ∈ U, φ u ∈ U := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hιinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_center_eq_bot hcenS
  have hA0el : IsElemAbelian 3 ((MulAut.conj : S →* MulAut S).range ⊓ A) :=
    i271_isElemAbelian_of_le hAel inf_le_right
  obtain ⟨m, hm⟩ := i271_exists_card_eq Nat.prime_three hA0el
  have hmul := Subgroup.relIndex_mul_card ((MulAut.conj : S →* MulAut S).range) A
  rw [hm, hAcard] at hmul
  have hm4 : 4 ≤ m := by
    have hle : 3 ^ r ≤ 3 ^ (m + 1) := by
      rw [← hmul, pow_succ, mul_comm (3 ^ m) 3]
      exact Nat.mul_le_mul_right _ hA3
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hle
    omega
  obtain ⟨E₀, hE₀le, hE₀card⟩ := exists_sub_card_pow Nat.prime_three hm (k := 4) (by omega)
  have hE₀A : E₀ ≤ A := hE₀le.trans inf_le_right
  have hE₀R : E₀ ≤ (MulAut.conj : S →* MulAut S).range := hE₀le.trans inf_le_left
  have hE₀el : IsElemAbelian 3 E₀ := i271_isElemAbelian_of_le hAel hE₀A
  have hE₀comm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₀el.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hE₀exp : ∀ x ∈ E₀, x ^ 3 = 1 := hE₀el.2
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Subgroup S, G₀ = E₀.comap (MulAut.conj : S →* MulAut S) := ⟨_, rfl⟩
  have hG₀mem : ∀ g : S, g ∈ G₀ ↔ MulAut.conj g ∈ E₀ := fun g => by
    rw [hG₀]
    rfl
  have hmapG : G₀.map (MulAut.conj : S →* MulAut S) = E₀ := by
    rw [hG₀, Subgroup.map_comap_eq, inf_eq_right.2 hE₀R]
  have hG₀card : Nat.card G₀ = 3 ^ 4 := by
    rw [← hE₀card, ← hmapG, Subgroup.card_map_of_injective hιinj]
  have hG₀comm : ∀ g ∈ G₀, ∀ g' ∈ G₀, g * g' = g' * g := by
    intro g hg g' hg'
    apply hιinj
    rw [map_mul, map_mul]
    exact hE₀comm _ ((hG₀mem g).1 hg) _ ((hG₀mem g').1 hg')
  have hG₀exp : ∀ g ∈ G₀, g ^ 3 = 1 := by
    intro g hg
    apply hιinj
    rw [map_pow, map_one]
    exact hE₀exp _ ((hG₀mem g).1 hg)
  have hβG : ∀ g ∈ G₀, β g = g := by
    intro g hg
    have hcomm : MulAut.conj g * β = β * MulAut.conj g :=
      congrArg Subtype.val
        (hAel.1.is_comm.comm ⟨MulAut.conj g, hE₀A ((hG₀mem g).1 hg)⟩ ⟨β, hβA⟩)
    have hsyml : ∀ s : S, g * β s * g⁻¹ = β (g * s * g⁻¹) := fun s =>
      congrArg (fun φ : MulAut S => φ s) hcomm
    have hconj : ∀ t : S, β g * t * (β g)⁻¹ = g * t * g⁻¹ := by
      intro t
      have key := hsyml (β.symm t)
      rw [MulEquiv.apply_symm_apply] at key
      rw [key, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have hu : g⁻¹ * β g ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro t
      have h1 : (g⁻¹ * β g) * t * (g⁻¹ * β g)⁻¹ = t := by
        calc (g⁻¹ * β g) * t * (g⁻¹ * β g)⁻¹ = g⁻¹ * (β g * t * (β g)⁻¹) * g := by group
          _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hconj t]
          _ = t := by group
      calc t * (g⁻¹ * β g) = ((g⁻¹ * β g) * t * (g⁻¹ * β g)⁻¹) * (g⁻¹ * β g) := by rw [h1]
        _ = (g⁻¹ * β g) * t := by group
    rw [hcenS, Subgroup.mem_bot] at hu
    exact (inv_mul_eq_one.1 hu).symm
  have hG₀H : G₀ ≤ H := fun g hg => (hHfix g).2 (hβG g hg)
  obtain ⟨G', hG'⟩ : ∃ G' : Subgroup ↥H, G' = G₀.comap H.subtype := ⟨_, rfl⟩
  have hG'mem : ∀ h : ↥H, h ∈ G' ↔ (h : S) ∈ G₀ := fun h => by
    rw [hG']
    rfl
  have hG'mapH : G'.map H.subtype = G₀ := by
    rw [hG', Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.2 hG₀H]
  have hG'card : Nat.card G' = 3 ^ 4 := by
    rw [← hG₀card, ← hG'mapH, Subgroup.card_map_of_injective H.subtype_injective]
  have hG'el : IsElemAbelian 3 G' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      show ((a : ↥H) : S) * ((b : ↥H) : S) = ((b : ↥H) : S) * ((a : ↥H) : S)
      exact hG₀comm _ ((hG'mem (a : ↥H)).1 a.2) _ ((hG'mem (b : ↥H)).1 b.2)
    · apply Subtype.ext
      show ((x : ↥H) : S) ^ 3 = 1
      exact hG₀exp _ ((hG'mem x).1 hx)
  obtain ⟨EH, hEH⟩ : ∃ EH : Subgroup (MulAut ↥H), EH = G'.map (MulAut.conj : ↥H →* MulAut ↥H) :=
    ⟨_, rfl⟩
  have hEHcard : Nat.card EH = 3 ^ 4 := by
    rw [hEH, Subgroup.card_map_of_injective (conj_injective_of_center_eq_bot hHcen), hG'card]
  have hEHel : IsElemAbelian 3 EH := by
    rw [hEH]
    exact CFSG.SectionRank.isElemAbelian_map hG'el MulAut.conj
  have hEHrange : EH ≤ (MulAut.conj : ↥H →* MulAut ↥H).range := by
    intro φ hφ
    rw [hEH] at hφ
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hφ
    exact MonoidHom.mem_range.2 ⟨x, rfl⟩
  obtain ⟨UH, hUH0, hUH2, hUHinv⟩ := hRank4 ↥H d₂ hd₂ ⟨eH⟩ EH hEHel hEHcard hEHrange
  refine ⟨E₀, hE₀A, hE₀el, hE₀card, UH.map H.subtype, ?_, ?_, ?_⟩
  · intro h0
    apply hUH0
    exact (Subgroup.map_eq_bot_iff_of_injective UH H.subtype_injective).1 h0
  · exact hUH2.of_equiv (Subgroup.equivMapOfInjective UH H.subtype H.subtype_injective)
  · intro φ hφ u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hu
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 (hE₀R hφ)
    have hgG : g ∈ G₀ := (hG₀mem g).2 hφ
    have hgH : g ∈ H := (hHfix g).2 (hβG g hgG)
    have hmem : MulAut.conj (⟨g, hgH⟩ : ↥H) ∈ EH := by
      rw [hEH]
      exact Subgroup.mem_map.2 ⟨⟨g, hgH⟩, (hG'mem ⟨g, hgH⟩).2 hgG, rfl⟩
    have hinv := hUHinv _ hmem v hv
    exact Subgroup.mem_map.2 ⟨MulAut.conj (⟨g, hgH⟩ : ↥H) v, hinv, rfl⟩

open CFSG.Blueprint.Chevalley in
theorem E68OutThree_holds :
    ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), IsE6EightIndex d.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ A : Subgroup (MulAut S), IsElemAbelian 3 A →
        (MulAut.conj : S →* MulAut S).range.relIndex A ≤ 3 := by
  intro S _ _ d hd hS A hA
  obtain ⟨d1, hv⟩ := d
  cases d1 with
  | E6 q =>
    obtain ⟨hq2, hqe⟩ := hd
    obtain ⟨e⟩ := hS
    have hKcard : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
    have hqcard : q.card = 2 ^ 3 := by
      rw [TauCeti.PrimePower.card_def, hq2, hqe]
    obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hq2 (GaloisField 2 3)
      (hKcard.trans hqcard.symm)
    obtain ⟨Φ, -, hΦker, -⟩ :=
      CFSG.LieType.Chevalley.exists_outer_hom_E (τ := Tag.E6) (K := GaloisField 2 3) (Or.inl rfl)
    obtain ⟨eG⟩ : Nonempty (S ≃* ↥(adjointGroup Tag.E6 (GaloisField 2 3))) :=
      ⟨(e.trans eB.symm).trans
        (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv Tag.E6 (GaloisField 2 3))⟩
    have hu7 : ∀ u : (GaloisField 2 3)ˣ, u ^ 7 = 1 := by
      intro u
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
      have h8 : Fintype.card (GaloisField 2 3) = 8 := by
        rw [Fintype.card_eq_nat_card, hKcard] <;> norm_num
      have hcard : Fintype.card (GaloisField 2 3) - 1 = 7 := by
        rw [h8] <;> norm_num
      have h := FiniteField.pow_card_sub_one_eq_one (u : GaloisField 2 3) u.ne_zero
      rw [hcard] at h
      exact h
    have hpow7 : ∀ (n : ℕ) (t : Fin n → (GaloisField 2 3)ˣ), t ^ 7 = 1 := by
      intro n t
      funext i
      rw [Pi.pow_apply, Pi.one_apply, hu7]
    have hRing : Nat.card (RingAut (GaloisField 2 3)) = 3 :=
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two
        (GaloisField 2 3) hKcard).1
    have hcod : Nat.card (RingAut (GaloisField 2 3) ×
        Multiplicative (ZMod (CFSG.LieType.Chevalley.exactE Tag.E6))) = 6 := by
      rw [Nat.card_prod, hRing, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      rfl
    let φ : MulAut S →* MulAut ↥(adjointGroup Tag.E6 (GaloisField 2 3)) :=
      (MulAut.congr eG).toMonoidHom
    let π : MulAut ↥(adjointGroup Tag.E6 (GaloisField 2 3)) →*
        CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥(adjointGroup Tag.E6 (GaloisField 2 3)) :=
      QuotientGroup.mk' _
    let Ψ : MulAut S →* RingAut (GaloisField 2 3) ×
        Multiplicative (ZMod (CFSG.LieType.Chevalley.exactE Tag.E6)) := Φ.comp (π.comp φ)
    have hkey : ∀ α ∈ A, Ψ α = 1 → α ∈ (MulAut.conj : S →* MulAut S).range := by
      intro α hα hΨ
      have hmem : π (φ α) ∈ Φ.ker := by
        rw [MonoidHom.mem_ker]
        exact hΨ
      rw [hΦker] at hmem
      obtain ⟨t, ht⟩ := MonoidHom.mem_range.1 hmem
      have h7 : π (φ α) ^ 7 = 1 := by
        rw [← ht, MonoidHom.comp_apply, ← map_pow, ← map_pow, hpow7 _ t, map_one, map_one]
      have h3 : π (φ α) ^ 3 = 1 := by
        have hα3 : α ^ 3 = 1 := hA.2 α hα
        rw [← map_pow, ← map_pow, hα3, map_one, map_one]
      have hord : orderOf (π (φ α)) = 1 := by
        have h1 := orderOf_dvd_of_pow_eq_one h3
        have h2 := orderOf_dvd_of_pow_eq_one h7
        have h12 := Nat.dvd_gcd h1 h2
        have hg : Nat.gcd 3 7 = 1 := by norm_num
        rw [hg] at h12
        exact Nat.dvd_one.1 h12
      have hx1 : π (φ α) = 1 := orderOf_eq_one_iff.1 hord
      have hin : φ α ∈ (MulAut.conj : ↥(adjointGroup Tag.E6 (GaloisField 2 3)) →*
          MulAut ↥(adjointGroup Tag.E6 (GaloisField 2 3))).range :=
        (QuotientGroup.eq_one_iff (φ α)).1 hx1
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 hin
      refine ⟨eG.symm g, MulEquiv.ext fun x => ?_⟩
      have hαx : eG (α x) = g * eG x * g⁻¹ := by
        have h1 : φ α (eG x) = eG (α x) := by
          show eG (α (eG.symm (eG x))) = eG (α x)
          rw [MulEquiv.symm_apply_apply]
        rw [← h1, ← hg]
        rfl
      show eG.symm g * x * (eG.symm g)⁻¹ = α x
      apply eG.injective
      rw [hαx, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    obtain ⟨n, hn⟩ := i271_exists_card_eq Nat.prime_three hA
    let f := Ψ.comp A.subtype
    have hker_le : f.ker ≤ (MulAut.conj : S →* MulAut S).range.subgroupOf A := by
      intro α hα
      rw [MonoidHom.mem_ker] at hα
      rw [Subgroup.mem_subgroupOf]
      exact hkey α.1 α.2 hα
    have hrel : (MulAut.conj : S →* MulAut S).range.relIndex A ∣ f.ker.index := by
      unfold Subgroup.relIndex
      exact Subgroup.index_dvd_of_le hker_le
    have hm1 : f.ker.index ∣ 3 ^ n := by
      have h := Subgroup.card_mul_index f.ker
      rw [hn] at h
      exact Dvd.intro_left _ h
    have hm2 : f.ker.index ∣ 6 := by
      rw [Subgroup.index_ker, ← hcod]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hm1
    have hk1 : k ≤ 1 := by
      by_contra hcon
      push_neg at hcon
      have h9 : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hcon
      have h6 : 3 ^ k ≤ 6 := Nat.le_of_dvd (by norm_num) (hk ▸ hm2)
      norm_num at h9
      omega
    have hm3 : f.ker.index ≤ 3 := by
      rw [hk]
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 3 := by norm_num
    have hpos : f.ker.index ≠ 0 := fun h0 => by
      rw [h0] at hm2
      norm_num at hm2
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hrel).trans hm3
  | _ => exact absurd hd (by simp [IsE6EightIndex])

end Gen2318E68Aux

open Gen2318E68Aux in
theorem gen2318E68Outer_of_inputs (hGA : CFSG.Open.GriessAllModelsStatement)
    (hFix : Gen2318E68Aux.E68FieldFix)
    (hTL : Gen2318TwoLocal) (hRank4 : Gen2318RankFour) : Gen2318E68Outer := by
  classical
  intro X _ _ _hXK K B hKc hBel hBN hrk hC hLie hout
  have hq : CFSG.Open.IsQuasisimple ↥K := hKc.2.2
  have hperf : commutator ↥K = ⊤ := hq.1
  have hZ : Subgroup.center ↥K = ⊥ := Gen2318E68Aux.center_eq_bot_of_E68 hGA hq hLie
  obtain ⟨d, hd, ⟨e⟩⟩ := hLie
  have hπinj : ∀ a c : ↥K, (QuotientGroup.mk a : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk c → a = c := by
    intro a c h
    have h' := QuotientGroup.eq.1 h
    rw [hZ, Subgroup.mem_bot] at h'
    exact inv_mul_eq_one.1 h'
  have hπsurj : Function.Surjective (QuotientGroup.mk : ↥K → ↥K ⧸ Subgroup.center ↥K) :=
    QuotientGroup.mk_surjective
  obtain ⟨eKS, hεK⟩ : ∃ eKS : ↥K ≃* (↥K ⧸ Subgroup.center ↥K),
      ∀ k : ↥K, eKS k = QuotientGroup.mk k :=
    ⟨MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center ↥K))
      ⟨fun a c h => hπinj a c h, hπsurj⟩, fun k => rfl⟩
  have hcenS : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    obtain ⟨k, rfl⟩ := hπsurj z
    have hk : k ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hcomm := Subgroup.mem_center_iff.1 hz (QuotientGroup.mk g)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hcomm
      exact hπinj _ _ hcomm
    have hk1 : k = 1 := by
      rw [hZ, Subgroup.mem_bot] at hk
      exact hk
    rw [hk1, QuotientGroup.mk_one]
  have hbex : ∃ b ∈ B ⊓ Subgroup.normalizer (K : Set X),
      ∀ k ∈ K, k⁻¹ * b ∉ Subgroup.centralizer (K : Set X) := by
    unfold InducesInnerIn at hout
    push_neg at hout
    exact hout
  obtain ⟨b, hbBN, hbnot⟩ := hbex
  have hbB : b ∈ B := (Subgroup.mem_inf.1 hbBN).1
  have hbN : b ∈ Subgroup.normalizer (K : Set X) := (Subgroup.mem_inf.1 hbBN).2
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  have hβ3 : (actHom K ⟨b, hbN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hb3)
    rw [h1, map_one]
  have hβA : actHom K ⟨b, hbN⟩ ∈ autImage B K := mem_autImage.2 ⟨b, hbN, hbB, rfl⟩
  have hβrange : actHom K ⟨b, hbN⟩ ∉ (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →*
      MulAut (↥K ⧸ Subgroup.center ↥K)).range := by
    rintro ⟨s, hs⟩
    obtain ⟨k, rfl⟩ := hπsurj s
    apply hbnot (k : X) k.2
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have key : (k : X) * x * (k : X)⁻¹ = b * x * b⁻¹ := by
      have h1 : MulAut.conj (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K)
          (QuotientGroup.mk (⟨x, hx⟩ : ↥K)) =
          actHom K ⟨b, hbN⟩ (QuotientGroup.mk (⟨x, hx⟩ : ↥K)) := by
        rw [hs]
      rw [actHom_mk] at h1
      have h2 : (QuotientGroup.mk (k * ⟨x, hx⟩ * k⁻¹ : ↥K) : ↥K ⧸ Subgroup.center ↥K) =
          QuotientGroup.mk (K.normalizerMonoidHom ⟨b, hbN⟩ ⟨x, hx⟩) := h1
      have h3 := congrArg Subtype.val (hπinj _ _ h2)
      rw [coe_normalizerMonoidHom] at h3
      exact h3
    calc x * ((k : X)⁻¹ * b) = (k : X)⁻¹ * ((k : X) * x * (k : X)⁻¹) * b := by group
      _ = (k : X)⁻¹ * (b * x * b⁻¹) * b := by rw [key]
      _ = ((k : X)⁻¹ * b) * x := by group
  obtain ⟨r, hr⟩ := exists_pow_autOrderIn Nat.prime_three hBel hBN
  obtain ⟨H, hHfix, hHcen, hHq, d₂, hd₂, ⟨eH⟩⟩ :=
    hFix (↥K ⧸ Subgroup.center ↥K) d hd ⟨e⟩ (actHom K ⟨b, hbN⟩) hβ3 hβrange
  have hHquot : Nonempty ((↥H ⧸ Subgroup.center ↥H) ≃* (TauCeti.CFSGIndex.lie d₂).Group) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hHcen).trans (QuotientGroup.quotientBot.trans eH)⟩
  obtain ⟨E, P, hEel, -, hρ, hPne, hP2, hEN⟩ :=
    hTL ↥H hHq d₂ (Gen2318E68Aux.gen2318Index_of_E62 hd₂) hHquot
  have hcart : ∃ E P : Subgroup ↥H, IsElemAbelian 3 E ∧ 4 ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧
      IsPGroup 2 ↥P ∧ E ≤ Subgroup.normalizer (P : Set ↥H) := by
    refine ⟨E, P, hEel, ?_, hPne, hP2, hEN⟩
    rw [Gen2318E68Aux.rho2318_E62 hd₂] at hρ
    exact hρ
  have hr5 : 5 ≤ r :=
    Gen2318E68Aux.rank_bound_of_fixed hεK hZ hBel hBN hbB hbN hb3 hbnot hrk hHfix hcart hr
  have hAel : IsElemAbelian 3 (autImage B K) := isElemAbelian_autImage hBel
  have hAcard : Nat.card (autImage B K) = 3 ^ r := (card_autImage hperf).trans hr
  have hA3 := Gen2318E68Aux.E68OutThree_holds (↥K ⧸ Subgroup.center ↥K) d hd ⟨e⟩ (autImage B K) hAel
  obtain ⟨E₀, hE₀A, hE₀el, hE₀card, U, hU0, hU2, hUinv⟩ :=
    Gen2318E68Aux.gamma_input (autImage B K) hAel hcenS hA3 hAcard hr5 hβA hHfix hHcen
      (Gen2318E68Aux.isRankFour_of_E62 hd₂) eH hRank4
  have hpc1 : 1 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
    one_le_pRank_centralizer Nat.prime_three hBel hC
  have hpB := pRank_eq_add_autOrderIn Nat.prime_three hBel hBN hr
  have hodd : Odd (Nat.card (Subgroup.center ↥K)) := by
    rw [hZ, Subgroup.card_bot]
    exact odd_one
  have hs : Seitz2313Cover.EvenScope d.1 := Gen2318E68Aux.evenScope_of_E68 hd
  have hgam := le_gammaPrime_of_seitz seitz2313Even_holds hperf hBel hodd hs e hE₀A hE₀el hE₀card
    (by norm_num) (by omega) ⟨U, hU0, hU2, hUinv⟩
  exact ⟨by omega, hgam⟩

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
