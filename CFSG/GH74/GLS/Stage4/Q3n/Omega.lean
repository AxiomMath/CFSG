module

public import CFSG.GH74.GLS.Stage4.Q3n.Derived
public import CFSG.GH74.GLS.Stage4.Q3n.Counting
public import CFSG.GH74.GLS.Stage4.Q3n.IndexTwo

public section

namespace CFSG.GH74.GLS.Stage4.Q3n

open Subgroup CFSG CFSG.Wreathed.CentralSL2

theorem d12_central_order_two :
    ∀ x : DihedralGroup 6, (∀ g, g * x = x * g) → x ≠ 1 → x = DihedralGroup.r 3 := by decide

theorem d12_order_three :
    ∀ g h : DihedralGroup 6, g ^ 3 = 1 → g ≠ 1 → h ^ 3 = 1 → h ≠ 1 → h = g ∨ h = g⁻¹ := by decide

theorem blocksInnerProduct_add_left {K : Type} [Group K] [Fintype K] (f₁ f₂ g : K → ℂ) :
    BlocksInnerProduct (fun x => f₁ x + f₂ x) g = BlocksInnerProduct f₁ g + BlocksInnerProduct f₂ g := by
  simp only [BlocksInnerProduct, add_mul, Finset.sum_add_distrib, mul_add]

theorem char_sum_inv_eq {K : Type} [Group K] [Fintype K] (χ ψ : K →* ℂˣ)
    (hne : ∃ q, χ q * χ q ≠ 1)
    (h : ∀ q, (χ q : ℂ) + (((χ q)⁻¹ : ℂˣ) : ℂ) = (ψ q : ℂ) + (((ψ q)⁻¹ : ℂˣ) : ℂ)) :
    ψ = χ ∨ ψ = χ⁻¹ := by
  have hχinv : χ⁻¹ ≠ χ := by
    intro heq
    obtain ⟨q, hq⟩ := hne
    apply hq
    have := congrArg (fun φ : K →* ℂˣ => φ q) heq
    simp only [MonoidHom.inv_apply] at this
    calc χ q * χ q = (χ q)⁻¹ * χ q := by rw [this]
      _ = 1 := inv_mul_cancel _
  have h1 : BlocksInnerProduct (fun x => (χ x : ℂ) + (((χ x)⁻¹ : ℂˣ) : ℂ)) (fun x => (χ x : ℂ)) = 1 := by
    rw [blocksInnerProduct_add_left]
    have e1 := blocksInnerProduct_units_hom (K := K) χ χ
    have e2 := blocksInnerProduct_units_hom (K := K) χ⁻¹ χ
    simp only [MonoidHom.inv_apply] at e1 e2
    rw [e1, e2]
    simp [hχinv]
  have h2 : BlocksInnerProduct (fun x => (ψ x : ℂ) + (((ψ x)⁻¹ : ℂˣ) : ℂ)) (fun x => (χ x : ℂ)) = 1 := by
    rw [← h1]
    congr 1
    funext x
    exact (h x).symm
  rw [blocksInnerProduct_add_left] at h2
  have e3 := blocksInnerProduct_units_hom (K := K) ψ χ
  have e4 := blocksInnerProduct_units_hom (K := K) ψ⁻¹ χ
  simp only [MonoidHom.inv_apply] at e3 e4
  rw [e3, e4] at h2
  by_cases hψ : ψ = χ
  · exact Or.inl hψ
  · right
    by_cases hψ' : ψ⁻¹ = χ
    · calc ψ = ψ⁻¹⁻¹ := by ext q; simp
        _ = χ⁻¹ := by rw [hψ']
    · exfalso
      simp [hψ, hψ'] at h2

namespace Q3nSetting

variable {G : Type} [Group G] [Finite G] {n : ℕ} (S : Q3nSetting G n)

@[expose] def conjQ (w : ↥S.W) : MulAut ↥S.Q where
  toFun q := ⟨(w : G) * q * (w : G)⁻¹, S.W_conj_Q w w.2 q q.2⟩
  invFun q := ⟨(w : G)⁻¹ * q * (w : G), by
    simpa using S.W_conj_Q ((w : G)⁻¹) (S.W.inv_mem w.2) q q.2⟩
  left_inv q := by ext; simp [mul_assoc]
  right_inv q := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

@[expose] def rho : ↥S.W →* MulAut ↥S.Q where
  toFun := S.conjQ
  map_one' := by ext q; simp [conjQ]
  map_mul' a b := by ext q; simp [conjQ, mul_assoc]

theorem eq_one_of_odd_sq {q : G} (hq : q ∈ S.Q) (h : q * q = 1) : q = 1 := by
  have hdvd : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have hodd := S.odd_of_mem_Q q hq
  have h1' : orderOf q = 1 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    rcases hodd with ⟨j, hj⟩
    interval_cases hj' : orderOf q <;> omega
  exact orderOf_eq_one_iff.1 h1'

theorem exists_regular_character_of_setting (hn : 3 ≤ n) :
    ∃ χ : ↥S.Q →* ℂˣ, ∀ w : ↥S.W, (∀ q : ↥S.Q, χ (S.rho w q) = χ q) → w = 1 := by
  obtain ⟨e⟩ := S.W_iso
  have hk7 : 7 ≤ S.k := by have := S.k_ge hn; omega
  let w₀' : ↥S.W := ⟨S.w₀, S.w₀_mem_W⟩
  have hw₀ : e w₀' = DihedralGroup.r 3 := by
    apply d12_central_order_two
    · intro g
      obtain ⟨h, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (S.w₀_central h h.2)
    · intro h1
      have h3 : w₀' = 1 := e.injective (by rw [h1, map_one])
      have h2 : orderOf S.w₀ = 2 := S.w₀_ord
      have h4 : S.w₀ = 1 := congrArg Subtype.val h3
      rw [h4, orderOf_one] at h2
      omega
  refine exists_regular_character (fun x y => Subtype.ext
    (S.H_comm x (S.Q_le_H x.2) y (S.Q_le_H y.2))) S.rho e w₀' hw₀ S.k hk7 S.Q_card ?_ ?_ ?_
  · intro q hq
    have h1 : S.w₀ * (q : G) * S.w₀⁻¹ = q := congrArg Subtype.val hq
    have h2 := S.w₀_inv q (S.Q_le_H q.2)
    rw [h1] at h2
    have hsq : (q : G) * q = 1 := by
      calc (q : G) * q = q * (q : G)⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel _
    exact Subtype.ext (S.eq_one_of_odd_sq q.2 hsq)
  · intro w hw q hq
    have hq' : (w : G) * q * (w : G)⁻¹ = q := congrArg Subtype.val hq
    let a' : ↥S.W := ⟨S.a, S.a_mem⟩
    have ha' : orderOf a' = 3 := by rw [← Subgroup.orderOf_coe]; exact S.a_ord
    have ha3 : e a' ^ 3 = 1 := by rw [← map_pow, ← ha', pow_orderOf_eq_one, map_one]
    have ha1 : e a' ≠ 1 := by
      intro h
      have : a' = 1 := e.injective (by rw [h, map_one])
      rw [this, orderOf_one] at ha'
      omega
    have hw3 : e w ^ 3 = 1 := by rw [← map_pow, ← hw, pow_orderOf_eq_one, map_one]
    have hw1 : e w ≠ 1 := by
      intro h
      have : w = 1 := e.injective (by rw [h, map_one])
      rw [this, orderOf_one] at hw
      omega
    have hcase := d12_order_three (e a') (e w) ha3 ha1 hw3 hw1
    have hcase' : w = a' ∨ w = a'⁻¹ := by
      rcases hcase with h | h
      · exact Or.inl (e.injective h)
      · exact Or.inr (e.injective (by rw [map_inv]; exact h))
    rcases hcase' with rfl | rfl
    · have := S.nonsing q (S.Q_le_H q.2) hq'
      exact Subtype.ext this
    · have h5 : S.a * (q : G) * S.a⁻¹ = q := by
        have : ((a'⁻¹ : ↥S.W) : G) * q * ((a'⁻¹ : ↥S.W) : G)⁻¹ = q := hq'
        simp only [Subgroup.coe_inv, inv_inv] at this
        calc S.a * (q : G) * S.a⁻¹ = S.a * (S.a⁻¹ * q * S.a) * S.a⁻¹ := by rw [this]
          _ = q := by group
      exact Subtype.ext (S.nonsing q (S.Q_le_H q.2) h5)
  · intro y hy hyw
    have hy' : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
    have hne : (y : G) ≠ S.w₀ := fun h => hyw (Subtype.ext h)
    have := S.inv_fix (y : G) y.2 hy' hne
    refine le_of_eq (Eq.trans (Nat.card_congr (Equiv.subtypeEquivRight fun q => ?_)) this)
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h

theorem exists_proj_exponent (hk : 2 ≤ S.k) : ∃ r : ℕ, 4 ∣ r ∧ r % (S.k ^ 2) = 1 := by
  have hco : Nat.Coprime 4 (S.k ^ 2) := by
    have h2 : Nat.Coprime 2 S.k := Nat.coprime_two_left.2 S.k_odd
    have : Nat.Coprime (2 ^ 2) (S.k ^ 2) := Nat.Coprime.pow 2 2 h2
    simpa using this
  obtain ⟨r, hr1, hr2⟩ := Nat.chineseRemainder hco 0 1
  refine ⟨r, ?_, ?_⟩
  · exact (Nat.modEq_zero_iff_dvd).1 hr1
  · have hk2 : 1 < S.k ^ 2 := by nlinarith
    rw [Nat.ModEq] at hr2
    rwa [Nat.mod_eq_of_lt hk2] at hr2

theorem pow_mem_Q {r : ℕ} (hr4 : 4 ∣ r) {h : G} (hh : h ∈ S.H) : h ^ r ∈ S.Q := by
  obtain ⟨u, hu, q, hq, rfl⟩ := S.exists_mul_of_mem_H h hh
  have hcomm : u * q = q * u := S.H_comm u (S.U_le_H hu) q (S.Q_le_H hq)
  have hu1 : u ^ r = 1 := by
    obtain ⟨m, rfl⟩ := hr4
    have : u ^ 4 = 1 := by
      have h2 : u ^ 2 = 1 := by rw [pow_two]; exact S.U_exp u hu
      calc u ^ 4 = (u ^ 2) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [h2]; simp
    rw [pow_mul, this, one_pow]
  rw [(show Commute u q from hcomm).mul_pow, hu1, one_mul]
  exact S.Q.pow_mem hq r

theorem pow_eq_self_of_mem_Q {r : ℕ} (hr1 : r % (S.k ^ 2) = 1) {q : G} (hq : q ∈ S.Q) :
    q ^ r = q := by
  have hqN : q ^ (S.k ^ 2) = 1 := by
    have := orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard S.Q hq)
    rwa [S.Q_card] at this
  have hr : r = S.k ^ 2 * (r / S.k ^ 2) + 1 := by
    have := Nat.div_add_mod r (S.k ^ 2)
    omega
  conv_lhs => rw [hr]
  rw [pow_succ, pow_mul, hqN, one_pow, one_mul]

theorem pow_eq_one_of_mem_U {r : ℕ} (hr4 : 4 ∣ r) {u : G} (hu : u ∈ S.U) : u ^ r = 1 := by
  obtain ⟨m, rfl⟩ := hr4
  have : u ^ 4 = 1 := by
    have h2 : u ^ 2 = 1 := by rw [pow_two]; exact S.U_exp u hu
    calc u ^ 4 = (u ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [h2]; simp
  rw [pow_mul, this, one_pow]

@[expose] noncomputable def lamH (χ : ↥S.Q →* ℂˣ) {r : ℕ} (hr4 : 4 ∣ r) : ↥S.H →* ℂˣ :=
  χ.comp (MonoidHom.mk' (fun h : ↥S.H => (⟨(h : G) ^ r, S.pow_mem_Q hr4 h.2⟩ : ↥S.Q))
    (by
      intro a b
      ext
      change ((a : G) * b) ^ r = (a : G) ^ r * (b : G) ^ r
      exact (show Commute (a : G) b from S.H_comm a a.2 b b.2).mul_pow r))

theorem lamH_Q (χ : ↥S.Q →* ℂˣ) {r : ℕ} (hr4 : 4 ∣ r) (hr1 : r % (S.k ^ 2) = 1) (q : ↥S.Q) :
    S.lamH χ hr4 ⟨(q : G), S.Q_le_H q.2⟩ = χ q := by
  unfold lamH
  simp only [MonoidHom.comp_apply, MonoidHom.mk'_apply]
  congr 1
  exact Subtype.ext (S.pow_eq_self_of_mem_Q hr1 q.2)

theorem lamH_U (χ : ↥S.Q →* ℂˣ) {r : ℕ} (hr4 : 4 ∣ r) {u : G} (hu : u ∈ S.U) :
    S.lamH χ hr4 ⟨u, S.U_le_H hu⟩ = 1 := by
  unfold lamH
  simp only [MonoidHom.comp_apply, MonoidHom.mk'_apply]
  have : (⟨u ^ r, S.pow_mem_Q hr4 (S.U_le_H hu)⟩ : ↥S.Q) = 1 := Subtype.ext (S.pow_eq_one_of_mem_U hr4 hu)
  rw [this, map_one]

theorem units_sq_ne_one {χ : ↥S.Q →* ℂˣ} {q : ↥S.Q} (hq : χ q ≠ 1) : χ q * χ q ≠ 1 := by
  intro h
  have hN : (χ q) ^ Nat.card S.Q = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  obtain ⟨m, hm⟩ := S.Q_card_odd
  rw [hm, pow_succ, pow_mul, show χ q ^ 2 = 1 by rw [pow_two]; exact h, one_pow, one_mul] at hN
  exact hq hN

theorem conj_mem_centralizer {g c : G} (hg : g ∈ Subgroup.normalizer S.U)
    (hc : c ∈ Subgroup.centralizer (S.U : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (S.U : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro u hu
  have hu' : g⁻¹ * u * g ∈ S.U := by
    have := (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * u * g)).1
    have h2 : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
    rw [h2] at this
    exact (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * u * g)).2 (by rw [h2]; exact hu)
  have h3 := hc (g⁻¹ * u * g) hu'
  calc u * (g * c * g⁻¹) = g * ((g⁻¹ * u * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * u * g)) * g⁻¹ := by rw [h3]
    _ = g * c * g⁻¹ * u := by group

theorem exists_omega (hn : 3 ≤ n) :
    ∃ ω ∈ BlocksIrr ↥(Subgroup.centralizer (S.U : Set G)),
      (∀ u : ↥(Subgroup.centralizer (S.U : Set G)), (u : G) ∈ S.U → ω u = ω 1) ∧ ω 1 = 2 ∧
      (∀ g ∈ Subgroup.normalizer S.U,
        (∀ c c' : ↥(Subgroup.centralizer (S.U : Set G)), (c' : G) = g * c * g⁻¹ → ω c' = ω c) →
        g ∈ Subgroup.centralizer (S.U : Set G)) := by
  have : Fintype ↥S.Q := Fintype.ofFinite _
  obtain ⟨χ, hχ⟩ := S.exists_regular_character_of_setting hn
  have hk2 : 2 ≤ S.k := by have := S.k_ge hn; omega
  obtain ⟨r, hr4, hr1⟩ := S.exists_proj_exponent hk2
  set C0 : Subgroup G := Subgroup.centralizer (S.U : Set G) with hC0
  have hHC : S.H ≤ C0 := S.H_le_centralizer
  let A : Subgroup ↥C0 := S.H.subgroupOf C0
  let eA : ↥A ≃* ↥S.H := Subgroup.subgroupOfEquivOfLe hHC
  let x : ↥C0 := ⟨S.w₀, S.w₀_mem_centralizer⟩
  have hmemA : ∀ c : ↥C0, c ∈ A ↔ (c : G) ∈ S.H := fun c => Subgroup.mem_subgroupOf
  have hχne : ∃ q : ↥S.Q, χ q ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have := hχ ⟨S.w₀, S.w₀_mem_W⟩ (fun q => by rw [hcon, hcon])
    have h1 : S.w₀ = 1 := congrArg Subtype.val this
    have h2 := S.w₀_ord
    rw [h1, orderOf_one] at h2
    omega
  obtain ⟨q₀, hq₀⟩ := hχne
  let lam : ↥A →* ℂˣ := (S.lamH χ hr4).comp eA.toMonoidHom
  have hAcomm' : ∀ a b : ↥A, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact S.H_comm _ ((hmemA a).1 a.2) _ ((hmemA b).1 b.2)
  let σ : ↥A →* ↥A := MonoidHom.mk' (fun a => a⁻¹) (by
    intro a b
    rw [← mul_inv_rev, hAcomm'])
  have hσ : ∀ a : ↥A, (σ a : ↥C0) = x * (a : ↥C0) * x⁻¹ := by
    intro a
    apply Subtype.ext
    have h1 := S.w₀_inv (a : G) ((hmemA a).1 a.2)
    change ((a⁻¹ : ↥A) : G) = S.w₀ * (a : G) * S.w₀⁻¹
    rw [h1]
    rfl
  have hωQ' : ∀ (q : ↥S.Q) (hqA : (⟨(q : G), hHC (S.Q_le_H q.2)⟩ : ↥C0) ∈ A),
      lam ⟨_, hqA⟩ = χ q := by
    intro q hqA
    change S.lamH χ hr4 (eA ⟨_, hqA⟩) = χ q
    have : eA ⟨_, hqA⟩ = ⟨(q : G), S.Q_le_H q.2⟩ := rfl
    rw [this]
    exact S.lamH_Q χ hr4 hr1 q
  have hne : ∃ a : ↥A, lam (σ a) ≠ lam a := by
    have hqA : (⟨(q₀ : G), hHC (S.Q_le_H q₀.2)⟩ : ↥C0) ∈ A := (hmemA _).2 (S.Q_le_H q₀.2)
    refine ⟨⟨_, hqA⟩, ?_⟩
    rw [hωQ' q₀ hqA]
    change lam ((⟨_, hqA⟩ : ↥A)⁻¹) ≠ _
    rw [map_inv, hωQ' q₀ hqA]
    intro h
    apply S.units_sq_ne_one hq₀
    calc χ q₀ * χ q₀ = (χ q₀)⁻¹ * χ q₀ := by rw [h]
      _ = 1 := inv_mul_cancel _
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    apply Subtype.ext
    exact S.H_comm _ ((hmemA a).1 ha) _ ((hmemA b).1 hb)
  have hxA : x ∉ A := fun h => S.w₀_not_mem_H hk2 ((hmemA x).1 h)
  have hcover : ∀ c : ↥C0, c ∈ A ∨ c * x⁻¹ ∈ A := by
    intro c
    obtain ⟨h, hh, hc⟩ := S.C0_eq (c : G) c.2
    rcases hc with hc | hc
    · left
      exact (hmemA c).2 (hc ▸ hh)
    · right
      refine (hmemA _).2 ?_
      change (c : G) * S.w₀⁻¹ ∈ S.H
      rw [hc]
      simpa using hh
  obtain ⟨ω, hω, hω1, hωA, hωoff⟩ :=
    exists_irr_induced_index_two A hAcomm x hxA hcover lam σ hσ hne
  have hωQ : ∀ (q : ↥S.Q) (c : ↥C0), (c : G) = (q : G) →
      ω c = (χ q : ℂ) + (((χ q)⁻¹ : ℂˣ) : ℂ) := by
    intro q c hc
    have hcA : c ∈ A := (hmemA c).2 (hc ▸ S.Q_le_H q.2)
    have h0 := hωA ⟨c, hcA⟩
    have hceq : c = ⟨(q : G), hHC (S.Q_le_H q.2)⟩ := Subtype.ext hc
    subst hceq
    have h1 := hωQ' q hcA
    have h2 : lam (σ ⟨_, hcA⟩) = (χ q)⁻¹ := by
      change lam ((⟨_, hcA⟩ : ↥A)⁻¹) = _
      rw [map_inv, h1]
    rw [h1, h2] at h0
    exact h0
  refine ⟨ω, hω, ?_, hω1, ?_⟩
  · intro u hu
    have huA : u ∈ A := (hmemA u).2 (S.U_le_H hu)
    have h0 := hωA ⟨u, huA⟩
    have h1 : lam ⟨u, huA⟩ = 1 := by
      change S.lamH χ hr4 (eA ⟨u, huA⟩) = 1
      exact S.lamH_U χ hr4 hu
    have h2 : lam (σ ⟨u, huA⟩) = 1 := by
      change lam ((⟨u, huA⟩ : ↥A)⁻¹) = 1
      rw [map_inv, h1, inv_one]
    rw [h1, h2] at h0
    rw [hω1]
    simp only [Units.val_one] at h0
    rw [h0]
    norm_num
  · intro g hg hinv
    obtain ⟨h, hh, w, hw, rfl⟩ := S.N_eq g hg
    let w' : ↥S.W := ⟨w, hw⟩
    have hgC : ∀ q : ↥S.Q, (h * w) * (q : G) * (h * w)⁻¹ ∈ C0 := fun q =>
      S.conj_mem_centralizer hg (hHC (S.Q_le_H q.2))
    have hcq : ∀ q : ↥S.Q, (h * w) * (q : G) * (h * w)⁻¹ = ((S.rho w' q : ↥S.Q) : G) := by
      intro q
      have hq' : w * (q : G) * w⁻¹ ∈ S.H := S.Q_le_H (S.rho w' q).2
      have hcomm : h * (w * (q : G) * w⁻¹) = (w * (q : G) * w⁻¹) * h := S.H_comm h hh _ hq'
      change h * w * (q : G) * (h * w)⁻¹ = w * (q : G) * w⁻¹
      calc h * w * (q : G) * (h * w)⁻¹ = h * (w * (q : G) * w⁻¹) * h⁻¹ := by group
        _ = w * (q : G) * w⁻¹ := by rw [hcomm]; group
    have key : ∀ q : ↥S.Q, (χ q : ℂ) + (((χ q)⁻¹ : ℂˣ) : ℂ) =
        (χ (S.rho w' q) : ℂ) + (((χ (S.rho w' q))⁻¹ : ℂˣ) : ℂ) := by
      intro q
      let c : ↥C0 := ⟨(q : G), hHC (S.Q_le_H q.2)⟩
      let c' : ↥C0 := ⟨(h * w) * (q : G) * (h * w)⁻¹, hgC q⟩
      have e1 := hωQ q c rfl
      have e2 := hωQ (S.rho w' q) c' (hcq q)
      have := hinv c c' rfl
      rw [← e1, ← e2]
      exact this.symm
    let ψ : ↥S.Q →* ℂˣ := χ.comp (S.rho w').toMonoidHom
    have hψ : ψ = χ ∨ ψ = χ⁻¹ :=
      char_sum_inv_eq χ ψ ⟨q₀, S.units_sq_ne_one hq₀⟩ (fun q => key q)
    rcases hψ with hψ | hψ
    · have hw1 : w' = 1 := hχ w' (fun q => congrArg (fun φ : ↥S.Q →* ℂˣ => φ q) hψ)
      have hw1' : w = 1 := congrArg Subtype.val hw1
      rw [hw1', mul_one]
      exact hHC hh
    · let w₀' : ↥S.W := ⟨S.w₀, S.w₀_mem_W⟩
      have hrho0 : ∀ q : ↥S.Q, S.rho w₀' q = q⁻¹ :=
        fun q => Subtype.ext (S.w₀_inv q (S.Q_le_H q.2))
      have hpt : ∀ q : ↥S.Q, χ (S.rho w' q) = χ (S.rho w₀' q) := by
        intro q
        have := congrArg (fun φ : ↥S.Q →* ℂˣ => φ q) hψ
        simp only [MonoidHom.inv_apply] at this
        rw [hrho0, map_inv]
        exact this
      have hw1 : w' * w₀'⁻¹ = 1 := by
        apply hχ
        intro q
        rw [map_mul, MulAut.mul_apply, hpt, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      have hww : w' = w₀' := mul_inv_eq_one.1 hw1
      have hw0 : w = S.w₀ := congrArg Subtype.val hww
      rw [hw0]
      exact C0.mul_mem (hHC hh) S.w₀_mem_centralizer

end Q3nSetting

end CFSG.GH74.GLS.Stage4.Q3n
