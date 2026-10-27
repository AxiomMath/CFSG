module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Quot

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section Tools

variable {P : Type} [Group P] {p : ℕ} {α : MulAut P} {Xh : Subgroup P}

theorem QuotCfg.not_fixed (h : QuotCfg p α Xh) : ¬ ∀ x ∈ Xh, α x = x := by
  intro hfix
  apply h.ne_bot
  rw [eq_bot_iff]
  intro x hx
  have h1 := h.comm x hx
  have h2 : Subgroup.closure {w | ∃ y ∈ Xh, w = y * (α y)⁻¹} ≤ ⊥ := by
    rw [Subgroup.closure_le]
    rintro w ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_bot, hfix y hy, mul_inv_cancel]
  exact h2 h1

theorem QuotCfg.closure_odd_le_normalizer (h : QuotCfg p α Xh) :
    Subgroup.closure {y : P | α y = y ∧ Odd (orderOf y)} ≤ normalizer (Xh : Set P) := by
  rw [Subgroup.closure_le]
  rintro y ⟨hy, hyo⟩
  exact h.hodd y hy hyo

theorem QuotCfg.prime_le_card [Finite P] (h : QuotCfg p α Xh) : p ≤ Nat.card ↥Xh := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨n, hn⟩ := h.pgroup.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply h.ne_bot
    rw [← Subgroup.card_eq_one, hn]; simp
  rw [hn]
  exact Nat.le_self_pow hn0 p

theorem QuotCfg.card_eq_prime [Finite P] (h : QuotCfg p α Xh)
    (hsyl : ∀ Q : Subgroup P, IsPGroup p ↥Q → Nat.card ↥Q ≤ p) : Nat.card ↥Xh = p :=
  le_antisymm (hsyl Xh h.pgroup) h.prime_le_card

theorem QuotCfg.false_of_fixed_prime_elt [Finite P] (h : QuotCfg p α Xh)
    (hsyl : ∀ Q : Subgroup P, IsPGroup p ↥Q → Nat.card ↥Q ≤ p) (s : P) (hs : α s = s)
    (hso : orderOf s = p) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hsodd : Odd (orderOf s) := by rw [hso]; exact hp.odd_of_ne_two h.odd
  have hsN : s ∈ normalizer (Xh : Set P) := h.hodd s hs hsodd
  have hz : zpowers s ≤ normalizer (Xh : Set P) := (Subgroup.zpowers_le).mpr hsN
  have hzcard : Nat.card ↥(zpowers s) = p := by rw [Nat.card_zpowers, hso]
  have hzp : IsPGroup p ↥(zpowers s) := IsPGroup.of_card (n := 1) (by simpa using hzcard)
  have hsup : IsPGroup p ↥(Xh ⊔ zpowers s : Subgroup P) := h.pgroup.to_sup_of_normal_left' hzp hz
  have hcard := hsyl _ hsup
  have hz_eq : zpowers s = Xh ⊔ zpowers s :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hzcard]; exact hcard)
  have hXle : Xh ≤ zpowers s := by rw [hz_eq]; exact le_sup_left
  have hXeq : Xh = zpowers s :=
    Subgroup.eq_of_le_of_card_ge hXle (by rw [hzcard]; exact h.prime_le_card)
  apply h.not_fixed
  intro x hx
  rw [hXeq] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [map_zpow, hs]

theorem mulAut_comm_of_cyclic (G : Type) [Group G] [IsCyclic G] (a b : MulAut G) : a * b = b * a := by
  apply (IsCyclic.mulAutMulEquiv G).injective
  rw [map_mul, map_mul, mul_comm]

theorem QuotCfg.centralizes_of_cyclic_invol (h : QuotCfg p α Xh) (hcyc : IsCyclic ↥Xh) {u : P}
    (hu : u * u = 1) (huC : u ∈ Subgroup.closure {y : P | α y = y ∧ Odd (orderOf y)}) :
    ∀ x ∈ Xh, u * x * u⁻¹ = x := by
  set C₁ := Subgroup.closure {y : P | α y = y ∧ Odd (orderOf y)} with hC₁
  have hle : C₁ ≤ normalizer (Xh : Set P) := h.closure_odd_le_normalizer
  let φ : ↥C₁ →* MulAut ↥Xh := (Xh.normalizerMonoidHom).comp (Subgroup.inclusion hle)
  have hodd : ∀ (c : P) (hc : c ∈ C₁), ∃ m : ℕ, Odd m ∧ (φ ⟨c, hc⟩) ^ m = 1 := by
    intro c hc
    induction hc using Subgroup.closure_induction with
    | mem y hy =>
      refine ⟨orderOf y, hy.2, ?_⟩
      rw [← map_pow]
      have : (⟨y, Subgroup.subset_closure hy⟩ : ↥C₁) ^ orderOf y = 1 := by
        apply Subtype.ext
        simp
      rw [this, map_one]
    | one =>
      refine ⟨1, odd_one, ?_⟩
      have : (⟨1, C₁.one_mem⟩ : ↥C₁) = 1 := rfl
      rw [this, map_one, pow_one]
    | mul x y hx hy ihx ihy =>
      obtain ⟨m₁, hm₁, h₁⟩ := ihx
      obtain ⟨m₂, hm₂, h₂⟩ := ihy
      refine ⟨m₁ * m₂, hm₁.mul hm₂, ?_⟩
      have : (⟨x * y, C₁.mul_mem hx hy⟩ : ↥C₁) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, (show Commute (φ ⟨x, hx⟩) (φ ⟨y, hy⟩) from mulAut_comm_of_cyclic _ _ _).mul_pow]
      have e1 : (φ ⟨x, hx⟩) ^ (m₁ * m₂) = 1 := by rw [pow_mul, h₁, one_pow]
      have e2 : (φ ⟨y, hy⟩) ^ (m₁ * m₂) = 1 := by rw [mul_comm, pow_mul, h₂, one_pow]
      rw [e1, e2, one_mul]
    | inv x hx ih =>
      obtain ⟨m, hm, h1⟩ := ih
      refine ⟨m, hm, ?_⟩
      have : (⟨x⁻¹, C₁.inv_mem hx⟩ : ↥C₁) = (⟨x, hx⟩ : ↥C₁)⁻¹ := rfl
      rw [this, map_inv, inv_pow, h1, inv_one]
  obtain ⟨m, hm, hmu⟩ := hodd u huC
  have hsq : (φ ⟨u, huC⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨u, huC⟩ : ↥C₁) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hu
    rw [this, map_one]
  have hcop : Nat.Coprime m 2 := Nat.coprime_two_right.mpr hm
  have h1 : (φ ⟨u, huC⟩) ^ (Nat.gcd m 2) = 1 := pow_gcd_eq_one.mpr ⟨hmu, hsq⟩
  rw [hcop.gcd_eq_one, pow_one] at h1
  intro x hx
  have h2 := congrArg (fun a : MulAut ↥Xh => ((a ⟨x, hx⟩ : ↥Xh) : P)) h1
  simpa [φ] using h2

end Tools


section OddClosure

theorem exists_involution_in_oddClosure {P : Type} [Group P] [Finite P] (C : Subgroup P)
    (hO : CFSG.oddCore ↥C = ⊥) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqC : q ∣ Nat.card ↥C) :
    ∃ u : P, u ∈ C ∧ u * u = 1 ∧ u ≠ 1 ∧
      u ∈ Subgroup.closure {y : P | y ∈ C ∧ Odd (orderOf y)} := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  set S : Set ↥C := {c : ↥C | Odd (orderOf c)} with hS
  set Codd : Subgroup ↥C := Subgroup.closure S with hCodd
  have hnorm : Codd.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem y hy =>
      apply Subgroup.subset_closure
      show Odd (orderOf (g * y * g⁻¹))
      have h1 : orderOf (g * y * g⁻¹) = orderOf y := by
        have := MulEquiv.orderOf_eq (MulAut.conj g) y
        simpa [MulAut.conj_apply] using this
      rw [h1]; exact hy
    | one => simp
    | mul x y hx hy ihx ihy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]; exact Codd.mul_mem ihx ihy
    | inv x hx ih =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]; exact Codd.inv_mem ih
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' q hqC
  have hsS : s ∈ Codd := Subgroup.subset_closure (by
    show Odd (orderOf s)
    rw [hs]; exact hq.odd_of_ne_two hq2)
  have hev : Even (Nat.card ↥Codd) := by
    by_contra hnev
    rw [Nat.not_even_iff_odd] at hnev
    have hle : Codd ≤ CFSG.oddCore ↥C := le_sSup ⟨hnorm, hnev⟩
    rw [hO] at hle
    have : s = 1 := Subgroup.mem_bot.mp (hle hsS)
    rw [this, orderOf_one] at hs
    exact hq.one_lt.ne hs
  have h2 : 2 ∣ Nat.card ↥Codd := even_iff_two_dvd.mp hev
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hu1 : ((u : ↥C) : P) * ((u : ↥C) : P) = 1 := by
    have : (u : ↥Codd) ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    have h3 := congrArg (fun x : ↥Codd => ((x : ↥C) : P)) this
    simpa [pow_two] using h3
  have hne : ((u : ↥C) : P) ≠ 1 := by
    intro h1
    have : u = 1 := by
      apply Subtype.ext; apply Subtype.ext; simpa using h1
    rw [this, orderOf_one] at hu
    exact absurd hu (by norm_num)
  refine ⟨((u : ↥C) : P), (u : ↥C).2, hu1, hne, ?_⟩
  have key : ∀ (c : ↥C), c ∈ Codd → (c : P) ∈ Subgroup.closure {y : P | y ∈ C ∧ Odd (orderOf y)} := by
    intro c hc
    induction hc using Subgroup.closure_induction with
    | mem y hy =>
      apply Subgroup.subset_closure
      refine ⟨y.2, ?_⟩
      have : orderOf (y : P) = orderOf y := Subgroup.orderOf_coe y
      rw [this]; exact hy
    | one => simp
    | mul x y hx hy ihx ihy => simpa using Subgroup.mul_mem _ ihx ihy
    | inv x hx ih => simpa using Subgroup.inv_mem _ ih
  exact key _ u.2

end OddClosure


section Assembly

variable {P : Type} [Group P] {p : ℕ} {α : MulAut P} {Xh : Subgroup P}

theorem QuotCfg.dvd_card [Finite P] (h : QuotCfg p α Xh) : p ∣ Nat.card P := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨n, hn⟩ := h.pgroup.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply h.ne_bot
    rw [← Subgroup.card_eq_one, hn]; simp
  exact (dvd_pow_self p hn0).trans (hn ▸ Subgroup.card_subgroup_dvd_card Xh)

theorem QuotCfg.false_of_sylow_row [Finite P] (h : QuotCfg p α Xh)
    (hsyl : ∀ Q : Subgroup P, IsPGroup p ↥Q → Nat.card ↥Q ≤ p)
    (hrow : (∃ s : P, α s = s ∧ orderOf s = p) ∨
      (∃ u : P, u * u = 1 ∧ u ≠ 1 ∧
        u ∈ Subgroup.closure {y : P | α y = y ∧ Odd (orderOf y)} ∧
        ¬ p ∣ Nat.card ↥(centralizer ({u} : Set P)))) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  rcases hrow with ⟨s, hs, hso⟩ | ⟨u, hu, hu1, huC, hnd⟩
  · exact h.false_of_fixed_prime_elt hsyl s hs hso
  · have hcard := h.card_eq_prime hsyl
    have hcyc : IsCyclic ↥Xh := isCyclic_of_prime_card hcard
    have hcent := h.centralizes_of_cyclic_invol hcyc hu huC
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.ne_bot
    have hxo : orderOf (x : P) = p := by
      have h1 : (x : ↥Xh) ^ p = 1 := by
        rw [← hcard]; exact pow_card_eq_one'
      have h2 : orderOf (x : ↥Xh) = p := orderOf_eq_prime h1 hx1
      rw [← h2]; exact Subgroup.orderOf_coe x
    have hxC : (x : P) ∈ centralizer ({u} : Set P) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hcent x x.2
      calc (x : P) * u = (u * x * u⁻¹) * u := by rw [this]
        _ = u * x := by group
    apply hnd
    have := orderOf_dvd_natCard (⟨(x : P), hxC⟩ : ↥(centralizer ({u} : Set P)))
    rwa [Subgroup.orderOf_mk, hxo] at this

theorem center_eq_bot_of_simple {Y : Type} [Group Y] (hs : IsSimpleGroup Y)
    (hnab : ∃ a b : Y, a * b ≠ b * a) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have : a ∈ Subgroup.center Y := by rw [h]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp this b).symm)

theorem exists_conj_of_equiv {Y T : Type} [Group Y] [Group T] (e : Y ≃* T)
    (h : ∀ φ : MulAut T, ∃ g : T, φ = MulAut.conj g) (α : MulAut Y) : ∃ t : Y, α = MulAut.conj t := by
  obtain ⟨g, hg⟩ := h (MulAut.congr e α)
  refine ⟨e.symm g, ?_⟩
  ext y
  have h1 := congrArg (fun φ : MulAut T => φ (e y)) hg
  have h2 : (MulAut.congr e α) (e y) = e (α y) := by
    show e (α (e.symm (e y))) = e (α y)
    rw [MulEquiv.symm_apply_apply]
  simp only [h2, MulAut.conj_apply] at h1
  show α y = e.symm g * y * (e.symm g)⁻¹
  apply e.injective
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem sq_eq_one_of_conj_invol {Y : Type} [Group Y] (hZ : Subgroup.center Y = ⊥) {t : Y}
    (hinv : ∀ s, MulAut.conj t (MulAut.conj t s) = s) : t * t = 1 := by
  have h1 : t * t ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := hinv g
    simp only [MulAut.conj_apply] at this
    calc g * (t * t) = (t * (t * g * t⁻¹) * t⁻¹) * (t * t) := by rw [this]
      _ = (t * t) * g := by group
  rw [hZ] at h1
  exact Subgroup.mem_bot.mp h1

end Assembly


section Helpers

theorem sylow_card_le_of_not_sq_dvd {P : Type} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ^ 2 ∣ Nat.card P) : ∀ Q : Subgroup P, IsPGroup p ↥Q → Nat.card ↥Q ≤ p := by
  intro Q hQ
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : p ^ k ∣ Nat.card P := hk ▸ Subgroup.card_subgroup_dvd_card Q
  rw [hk]
  by_contra hlt
  have hlt' : p < p ^ k := not_le.mp hlt
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have h1 : k ≤ 1 := by omega
    have h2 : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos h1
    rw [pow_one] at h2
    omega
  exact h ((pow_dvd_pow p hk2).trans hdvd)

theorem QuotCfg.of_inner {P : Type} [Group P] {p : ℕ} {α : MulAut P} {Xh : Subgroup P}
    (h : QuotCfg p α Xh) {t : P} (hαt : α = MulAut.conj t) :
    orderOf t = 2 ∧ t * t = 1 ∧ (∀ y, α y = y ↔ y ∈ centralizer ({t} : Set P)) ∧
      (∀ x, t * x * t⁻¹ = α x) := by
  have hZ := center_eq_bot_of_simple h.simple h.nonab
  have ht2 : t * t = 1 := by
    apply sq_eq_one_of_conj_invol hZ
    intro s
    have := h.invol s
    rwa [hαt] at this
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply h.not_fixed
    intro x _
    rw [hαt]
    simp
  have hto : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht1
  refine ⟨hto, ht2, ?_, fun x => by rw [hαt, MulAut.conj_apply]⟩
  intro y
  rw [Subgroup.mem_centralizer_singleton_iff, hαt, MulAut.conj_apply]
  constructor
  · intro h1
    calc y * t = (t * y * t⁻¹) * t := by rw [h1]
      _ = t * y := by group
  · intro h1
    calc t * y * t⁻¹ = (y * t) * t⁻¹ := by rw [h1]
      _ = y := by group

theorem fixSub_le_closure_odd_of_perfect_aux {P : Type} [Group P] (E : Subgroup P) (α : MulAut P)
    (hE : ∀ e ∈ E, α e = e) :
    Subgroup.closure {y : P | y ∈ E ∧ Odd (orderOf y)} ≤
      Subgroup.closure {y : P | α y = y ∧ Odd (orderOf y)} := by
  apply Subgroup.closure_mono
  rintro y ⟨hy, hyo⟩
  exact ⟨hE y hy, hyo⟩

end Helpers


section OutAbel

open CFSG.ComponentClassification.OuterAutomorphisms

theorem outAbelian_of_outer_comm {Y : Type} [Group Y] (h : IsMulCommutative (Outer Y)) :
    OutAbelian Y := by
  intro α β
  have h1 : (QuotientGroup.mk (α * β * α⁻¹ * β⁻¹) : Outer Y) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h.is_comm.comm (QuotientGroup.mk α : Outer Y) (QuotientGroup.mk β)]
    group
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem outAbelian_of_inner_top {Y : Type} [Group Y] (h : ∀ φ : MulAut Y, ∃ g : Y, φ = MulAut.conj g) :
    OutAbelian Y := by
  intro α β
  obtain ⟨g, hg⟩ := h (α * β * α⁻¹ * β⁻¹)
  exact ⟨g, hg.symm⟩

end OutAbel

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
