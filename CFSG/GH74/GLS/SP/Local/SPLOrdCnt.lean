module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.LinearCombination
import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

public section

namespace CFSG.GH74.GLS.SP.Local

open CFSG.ShultStronglyClosedTI.InvolutionCounting

namespace OrdCnt

theorem card_subtype_and_add_card_subtype_and_not {α : Type*} [Finite α] (P R : α → Prop) :
    Nat.card {a // P a ∧ R a} + Nat.card {a // P a ∧ ¬ R a} = Nat.card {a // P a} := by
  classical
  rw [← Nat.card_sum]
  exact (Nat.card_congr
    { toFun := fun a => if h : R a.1 then Sum.inl ⟨a.1, a.2, h⟩ else Sum.inr ⟨a.1, a.2, h⟩
      invFun := fun s => Sum.elim (fun x => ⟨x.1, x.2.1⟩) (fun x => ⟨x.1, x.2.1⟩) s
      left_inv := fun a => by by_cases h : R a.1 <;> simp [h]
      right_inv := fun s => by rcases s with ⟨x, hx⟩ | ⟨x, hx⟩ <;> simp [hx.2] }).symm

theorem card_subtype_eq_mul_of_fibres {G α : Type*} [Finite G] [Finite α]
    (f : α → G) (S : α → Prop) (T : G → Prop) (n : ℕ)
    (hT : ∀ a, S a → T (f a)) (hn : ∀ v, T v → Nat.card {a // S a ∧ f a = v} = n) :
    Nat.card {a // S a} = Nat.card {v // T v} * n := by
  classical
  have : Fintype {v // T v} := Fintype.ofFinite _
  let e : {a // S a} ≃ Σ v : {v // T v}, {a // S a ∧ f a = v.1} :=
    { toFun := fun a => ⟨⟨f a.1, hT a.1 a.2⟩, ⟨a.1, a.2, rfl⟩⟩
      invFun := fun x => ⟨x.2.1, x.2.2.1⟩
      left_inv := fun a => rfl
      right_inv := fun x => Sigma.subtype_ext (Subtype.ext x.2.2.2) rfl }
  rw [Nat.card_congr e, Nat.card_sigma,
    Finset.sum_congr rfl (fun v _ => hn v.1 v.2), Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, smul_eq_mul]

theorem card_fibre_eq_of_conj {G α : Type*} [Group G] (f : α → G) (S : α → Prop)
    (σ : G → α ≃ α) (hf : ∀ g a, f (σ g a) = g * f a * g⁻¹) (hS : ∀ g a, S (σ g a) ↔ S a)
    {u v : G} (g : G) (hg : g * u * g⁻¹ = v) :
    Nat.card {a // S a ∧ f a = u} = Nat.card {a // S a ∧ f a = v} := by
  refine Nat.card_congr ((σ g).subtypeEquiv fun a => ?_)
  rw [hS, hf, ← hg, mul_left_inj, mul_right_inj]

theorem card_subtype_eq_mul_of_conj {G α : Type*} [Group G] [Finite G] [Finite α]
    (f : α → G) (S : α → Prop) (σ : G → α ≃ α)
    (hf : ∀ g a, f (σ g a) = g * f a * g⁻¹) (hS : ∀ g a, S (σ g a) ↔ S a)
    (T : G → Prop) (hT : ∀ a, S a → T (f a)) (i₀ : G) (hTconj : ∀ v, T v → ∃ g : G, g * v * g⁻¹ = i₀) :
    Nat.card {a // S a} = Nat.card {v // T v} * Nat.card {a // S a ∧ f a = i₀} :=
  card_subtype_eq_mul_of_fibres f S T _ hT fun v hv => by
    obtain ⟨g, hg⟩ := hTconj v hv
    exact card_fibre_eq_of_conj f S σ hf hS g hg

theorem card_subtype_add_card_subtype_not {α : Type*} [Finite α] (R : α → Prop) :
    Nat.card {a // R a} + Nat.card {a // ¬ R a} = Nat.card α := by
  have h := card_subtype_and_add_card_subtype_and_not (fun _ : α => True) R
  simpa [true_and, Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ : α => trivial))] using h

section Involutions

variable {I : Type} [Group I]

theorem orderOf_conj_eq (g a : I) : orderOf (g * a * g⁻¹) = orderOf a := by
  simpa using (MulAut.conj g).orderOf_eq a

theorem orderOf_pow_half_of_even [Finite I] {x : I} (h : Even (orderOf x)) :
    orderOf (x ^ (orderOf x / 2)) = 2 := by
  refine orderOf_pow_half (d := orderOf x / 2) (Nat.two_mul_div_two_of_even h).symm ?_
  have := orderOf_pos x
  obtain ⟨k, hk⟩ := h
  omega

theorem card_involutions_mul_card_centralizer (i₀ : I) (hi₀ : orderOf i₀ = 2)
    (hconj : ∀ u v : I, orderOf u = 2 → orderOf v = 2 → ∃ g : I, g * u * g⁻¹ = v) :
    Nat.card {u : I // orderOf u = 2} * Nat.card (Subgroup.centralizer ({i₀} : Set I)) =
      Nat.card I := by
  have e : Nat.card (conjugatesOf i₀) = Nat.card {u : I // orderOf u = 2} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun u => by
      constructor
      · intro hu
        exact (orderOf_eq_of_isConj hu).symm.trans hi₀
      · intro hu
        obtain ⟨g, hg⟩ := hconj i₀ u hi₀ hu
        exact isConj_iff.mpr ⟨g, hg⟩)
  rw [← e, mul_comm]
  exact card_centralizer_mul_card_conjugatesOf i₀

theorem card_even_order [Finite I] (i₀ : I) (hi₀ : orderOf i₀ = 2)
    (hconj : ∀ u v : I, orderOf u = 2 → orderOf v = 2 → ∃ g : I, g * u * g⁻¹ = v) :
    Nat.card {x : I // Even (orderOf x)} = Nat.card {u : I // orderOf u = 2} *
      Nat.card {x : I // x ∈ Subgroup.centralizer ({i₀} : Set I) ∧ Even (orderOf x) ∧
        x ^ (orderOf x / 2) = i₀} := by
  have h := card_subtype_eq_mul_of_conj (fun x : I => x ^ (orderOf x / 2))
    (fun x => Even (orderOf x)) (fun g => (MulAut.conj g).toEquiv)
    (fun g a => by simp [orderOf_conj_eq, conj_pow]) (fun g a => by simp [orderOf_conj_eq])
    (fun v => orderOf v = 2) (fun a ha => orderOf_pow_half_of_even ha) i₀
    (fun v hv => hconj v i₀ hv hi₀)
  rw [h]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← h2]
    exact (Commute.self_pow x _).eq
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩

theorem card_pairs_even [Finite I] (i₀ : I) (hi₀ : orderOf i₀ = 2)
    (hconj : ∀ u v : I, orderOf u = 2 → orderOf v = 2 → ∃ g : I, g * u * g⁻¹ = v) :
    Nat.card {p : I × I // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Even (orderOf (p.1 * p.2))} =
      Nat.card {u : I // orderOf u = 2} *
        Nat.card {p : I × I // p.1 ∈ Subgroup.centralizer ({i₀} : Set I) ∧
          p.2 ∈ Subgroup.centralizer ({i₀} : Set I) ∧
          orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ i₀ ∈ Subgroup.zpowers (p.1 * p.2)} := by
  have h := card_subtype_eq_mul_of_conj
    (fun p : I × I => (p.1 * p.2) ^ (orderOf (p.1 * p.2) / 2))
    (fun p => orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Even (orderOf (p.1 * p.2)))
    (fun g => (MulAut.conj g).toEquiv.prodCongr (MulAut.conj g).toEquiv)
    (fun g p => by simp [orderOf_conj_eq, conj_pow])
    (fun g p => by simp [orderOf_conj_eq])
    (fun v => orderOf v = 2) (fun p hp => orderOf_pow_half_of_even hp.2.2) i₀
    (fun v hv => hconj v i₀ hv hi₀)
  rw [h]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun p => ?_)
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    have hv := mul_self_eq_one_of_orderOf_eq_two h1
    have hs := mul_self_eq_one_of_orderOf_eq_two h2
    have hmem : i₀ ∈ Subgroup.zpowers (p.1 * p.2) := h4 ▸ Subgroup.npow_mem_zpowers _ _
    have hi := mul_self_eq_one_of_orderOf_eq_two hi₀
    refine ⟨?_, ?_, h1, h2, hmem⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_of_mem_zpowers (conj_mul_left_eq_inv hv hs) hmem hi).eq
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_of_mem_zpowers (conj_mul_right_eq_inv hv hs) hmem hi).eq
  · rintro ⟨-, -, h1, h2, hmem⟩
    have hev : Even (orderOf (p.1 * p.2)) :=
      even_iff_two_dvd.mpr (hi₀ ▸ orderOf_dvd_of_mem_zpowers hmem)
    have hpos := orderOf_pos (p.1 * p.2)
    obtain ⟨k, hk⟩ := hev
    refine ⟨⟨h1, h2, ⟨k, hk⟩⟩, ?_⟩
    exact ((mem_zpowers_iff_eq_pow_half (d := orderOf (p.1 * p.2) / 2) (by omega) (by omega)
      hi₀).mp hmem).symm

end Involutions

theorem not_mem_zpowers_central_mul {G : Type*} [Group G] {j b : G}
    (hc : j ∈ Subgroup.center G) (hj : orderOf j = 2) (hb : orderOf b = 2) :
    j ∉ Subgroup.zpowers (j * b) := by
  intro hmem
  have hcomm : Commute j b := (Subgroup.mem_center_iff.mp hc b).symm
  have hj2 : j ^ 2 = 1 := by simpa [hj] using pow_orderOf_eq_one j
  have hb2 : b ^ 2 = 1 := by simpa [hb] using pow_orderOf_eq_one b
  have hy : (j * b) ^ 2 = 1 := by rw [hcomm.mul_pow, hj2, hb2, one_mul]
  have hord : orderOf (j * b) = 2 :=
    Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hy) (hj ▸ orderOf_dvd_of_mem_zpowers hmem)
  have h := (mem_zpowers_iff_eq_pow_half (d := 1) (by simpa using hord) one_ne_zero hj).mp hmem
  rw [pow_one, left_eq_mul] at h
  rw [h, orderOf_one] at hb
  omega

section Dihedral

open DihedralGroup

variable {δ : ℕ} [NeZero δ]

omit [NeZero δ] in
theorem r_pow_card (k : ZMod δ) : (r k : DihedralGroup δ) ^ δ = 1 := by
  rw [r_pow, ZMod.natCast_self, mul_zero, r_zero]

theorem dvd_mul_ordCompl_iff (m : ℕ) :
    δ ∣ m * (δ / 2 ^ δ.factorization 2) ↔ 2 ^ δ.factorization 2 ∣ m := by
  have h := Nat.ordProj_mul_ordCompl_eq_self δ 2
  have hpos : 0 < δ / 2 ^ δ.factorization 2 := Nat.ordCompl_pos 2 (NeZero.ne δ)
  have := Nat.mul_dvd_mul_iff_right hpos (a := 2 ^ δ.factorization 2) (b := m)
  rwa [h] at this

theorem odd_orderOf_r_iff (k : ZMod δ) :
    Odd (orderOf (r k : DihedralGroup δ)) ↔ 2 ^ δ.factorization 2 ∣ k.val := by
  have hodd : Odd (δ / 2 ^ δ.factorization 2) :=
    Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (NeZero.ne δ))
  have key : Odd (orderOf (r k : DihedralGroup δ)) ↔
      (r k : DihedralGroup δ) ^ (δ / 2 ^ δ.factorization 2) = 1 := by
    constructor
    · intro ho
      have h1 : orderOf (r k : DihedralGroup δ) ∣
          2 ^ δ.factorization 2 * (δ / 2 ^ δ.factorization 2) := by
        rw [Nat.ordProj_mul_ordCompl_eq_self]
        exact orderOf_dvd_of_pow_eq_one (r_pow_card k)
      have hcop : Nat.Coprime (orderOf (r k : DihedralGroup δ)) (2 ^ δ.factorization 2) :=
        ho.coprime_two_right.pow_right _
      exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left h1)
    · intro h
      exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one h)
  rw [key, r_pow, ← r_zero, r.injEq]
  have h2 : k * ((δ / 2 ^ δ.factorization 2 : ℕ) : ZMod δ) =
      ((k.val * (δ / 2 ^ δ.factorization 2) : ℕ) : ZMod δ) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [h2, ZMod.natCast_eq_zero_iff, dvd_mul_ordCompl_iff]

theorem card_zmod_val_dvd {d : ℕ} (hd : 0 < d) (hdδ : d ∣ δ) :
    Nat.card {k : ZMod δ // d ∣ k.val} = δ / d := by
  obtain ⟨e, he⟩ := hdδ
  have hδd : δ / d = e := by rw [he, Nat.mul_div_cancel_left _ hd]
  rw [hδd]
  have hlt : ∀ m : Fin e, d * m.1 < δ := fun m => by
    rw [he]
    exact (Nat.mul_lt_mul_left hd).mpr m.2
  have hval : ∀ m : Fin e, ((d * m.1 : ℕ) : ZMod δ).val = d * m.1 := fun m =>
    ZMod.val_natCast_of_lt (hlt m)
  refine (Nat.card_eq_of_bijective
    (fun m : Fin e => (⟨((d * m.1 : ℕ) : ZMod δ), by rw [hval m]; exact dvd_mul_right d _⟩ :
      {k : ZMod δ // d ∣ k.val})) ⟨?_, ?_⟩).symm.trans (Nat.card_fin e)
  · intro m m' h
    have := congrArg (fun x : {k : ZMod δ // d ∣ k.val} => x.1.val) h
    simp only [hval] at this
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hd this)
  · rintro ⟨k, m, hm⟩
    have hmlt : m < e := by
      have h1 : k.val < d * e := lt_of_lt_of_eq (ZMod.val_lt k) he
      rw [hm] at h1
      exact (Nat.mul_lt_mul_left hd).mp h1
    refine ⟨⟨m, hmlt⟩, Subtype.ext ?_⟩
    show ((d * m : ℕ) : ZMod δ) = k
    rw [← hm, ZMod.natCast_zmod_val]

theorem card_odd_rot :
    Nat.card {k : ZMod δ // Odd (orderOf (r k : DihedralGroup δ))} = δ / 2 ^ δ.factorization 2 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun k => odd_orderOf_r_iff k)]
  exact card_zmod_val_dvd (Nat.two_pow_pos _) (Nat.ordProj_dvd δ 2)

theorem card_even_rot :
    Nat.card {k : ZMod δ // Even (orderOf (r k : DihedralGroup δ))} =
      δ - δ / 2 ^ δ.factorization 2 := by
  have h := card_subtype_add_card_subtype_not
    (fun k : ZMod δ => Odd (orderOf (r k : DihedralGroup δ)))
  rw [card_odd_rot, Nat.card_zmod] at h
  simp only [Nat.not_odd_iff_even] at h
  omega

theorem card_odd_dihedral :
    Nat.card {x : DihedralGroup δ // Odd (orderOf x)} = δ / 2 ^ δ.factorization 2 := by
  rw [← card_odd_rot]
  refine (Nat.card_eq_of_bijective (fun k => ⟨r k.1, k.2⟩) ⟨?_, ?_⟩).symm
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    simpa using h
  · rintro ⟨x | c, hx⟩
    · exact ⟨⟨x, hx⟩, rfl⟩
    · exfalso
      rw [orderOf_sr] at hx
      exact (by decide : ¬ Odd 2) hx

omit [NeZero δ] in
theorem two_mul_val_of_orderOf_r_eq_two {m : ZMod δ} (h : orderOf (r m : DihedralGroup δ) = 2) :
    2 * m.val = δ := by
  have h1 : (r m : DihedralGroup δ) ^ 2 = 1 := by
    simpa [h] using pow_orderOf_eq_one (r m : DihedralGroup δ)
  rw [r_pow, ← r_zero, r.injEq] at h1
  have h2 : -m = m := by linear_combination (-1 : ZMod δ) * h1
  rcases (ZMod.neg_eq_self_iff m).mp h2 with h0 | h0
  · exfalso
    simp [h0] at h
  · exact h0

theorem eq_of_orderOf_r_eq_two {m m' : ZMod δ} (h : orderOf (r m : DihedralGroup δ) = 2)
    (h' : orderOf (r m' : DihedralGroup δ) = 2) : m = m' :=
  ZMod.val_injective δ (by
    have h1 := two_mul_val_of_orderOf_r_eq_two h
    have h2 := two_mul_val_of_orderOf_r_eq_two h'
    omega)

omit [NeZero δ] in
theorem exists_r_eq_of_central (hδ : 3 ≤ δ) {j : DihedralGroup δ}
    (hc : j ∈ Subgroup.center (DihedralGroup δ)) : ∃ m : ZMod δ, j = r m := by
  rcases j with m | c
  · exact ⟨m, rfl⟩
  · exfalso
    have h := Subgroup.mem_center_iff.mp hc (r 1)
    rw [r_mul_sr, sr_mul_r, sr.injEq] at h
    have h2 : ((2 : ℕ) : ZMod δ) = 0 := by
      push_cast
      linear_combination (-1 : ZMod δ) * h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega

theorem r_pow_half_eq (hδ : 3 ≤ δ) {j : DihedralGroup δ} (hj : orderOf j = 2)
    (hc : j ∈ Subgroup.center (DihedralGroup δ)) (k : ZMod δ)
    (hk : Even (orderOf (r k : DihedralGroup δ))) :
    (r k : DihedralGroup δ) ^ (orderOf (r k : DihedralGroup δ) / 2) = j := by
  obtain ⟨m₀, rfl⟩ := exists_r_eq_of_central hδ hc
  have h1 := orderOf_pow_half_of_even hk
  rw [r_pow] at h1 ⊢
  exact congrArg r (eq_of_orderOf_r_eq_two h1 hj)

theorem card_even_dihedral (hδ : 3 ≤ δ) {j : DihedralGroup δ} (hj : orderOf j = 2)
    (hc : j ∈ Subgroup.center (DihedralGroup δ)) :
    Nat.card {x : DihedralGroup δ // Even (orderOf x) ∧ x ^ (orderOf x / 2) = j} =
      δ - δ / 2 ^ δ.factorization 2 := by
  rw [← card_even_rot]
  refine (Nat.card_eq_of_bijective
    (fun k : {k : ZMod δ // Even (orderOf (r k : DihedralGroup δ))} =>
      (⟨r k.1, k.2, r_pow_half_eq hδ hj hc k.1 k.2⟩ :
        {x : DihedralGroup δ // Even (orderOf x) ∧ x ^ (orderOf x / 2) = j})) ⟨?_, ?_⟩).symm
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    simpa using h
  · rintro ⟨x | c, hx1, hx2⟩
    · exact ⟨⟨x, hx1⟩, rfl⟩
    · exfalso
      obtain ⟨m₀, rfl⟩ := exists_r_eq_of_central hδ hc
      simp at hx2

theorem card_pairs_dihedral (hδ : 3 ≤ δ) {j : DihedralGroup δ} (hj : orderOf j = 2)
    (hc : j ∈ Subgroup.center (DihedralGroup δ)) :
    Nat.card {p : DihedralGroup δ × DihedralGroup δ // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧
      j ∈ Subgroup.zpowers (p.1 * p.2)} = δ * (δ - δ / 2 ^ δ.factorization 2) := by
  have hrot : ∀ m : ZMod δ, orderOf (r m : DihedralGroup δ) = 2 → (r m : DihedralGroup δ) = j := by
    intro m hm
    obtain ⟨m₀, rfl⟩ := exists_r_eq_of_central hδ hc
    exact congrArg r (eq_of_orderOf_r_eq_two hm hj)
  have hmem : ∀ d : ZMod δ, j ∈ Subgroup.zpowers (r d : DihedralGroup δ) ↔
      Even (orderOf (r d : DihedralGroup δ)) := by
    intro d
    constructor
    · intro h
      exact even_iff_two_dvd.mpr (hj ▸ orderOf_dvd_of_mem_zpowers h)
    · intro h
      rw [← r_pow_half_eq hδ hj hc d h]
      exact Subgroup.npow_mem_zpowers _ _
  have h1 : Nat.card {q : ZMod δ × ZMod δ // Even (orderOf (r (q.2 - q.1) : DihedralGroup δ))} =
      Nat.card {p : DihedralGroup δ × DihedralGroup δ // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧
        j ∈ Subgroup.zpowers (p.1 * p.2)} := by
    refine Nat.card_eq_of_bijective
      (fun q => ⟨(sr q.1.1, sr q.1.2), by simp, by simp, ?_⟩) ⟨?_, ?_⟩
    · show j ∈ Subgroup.zpowers (sr q.1.1 * sr q.1.2)
      rw [sr_mul_sr]
      exact (hmem _).mpr q.2
    · rintro ⟨⟨s, t⟩, hq⟩ ⟨⟨s', t'⟩, hq'⟩ h
      simp only [Subtype.mk.injEq, Prod.mk.injEq, sr.injEq] at h
      simp [h.1, h.2]
    · rintro ⟨⟨a, b⟩, ha, hb, hab⟩
      dsimp only at ha hb hab
      rcases a with m | s <;> rcases b with m' | t
      · exact absurd (by rwa [hrot m ha] at hab) (not_mem_zpowers_central_mul hc hj hb)
      · exact absurd (by rwa [hrot m ha] at hab) (not_mem_zpowers_central_mul hc hj hb)
      · have hs := Subgroup.mem_center_iff.mp hc (sr s)
        rw [hrot m' hb, hs] at hab
        exact absurd hab (not_mem_zpowers_central_mul hc hj ha)
      · rw [sr_mul_sr] at hab
        exact ⟨⟨(s, t), (hmem _).mp hab⟩, rfl⟩
  have h2 : Nat.card {q : ZMod δ × ZMod δ //
      Even (orderOf (r (q.2 - q.1) : DihedralGroup δ))} =
      δ * Nat.card {k : ZMod δ // Even (orderOf (r k : DihedralGroup δ))} := by
    refine (Nat.card_eq_of_bijective
      (β := ZMod δ × {k : ZMod δ // Even (orderOf (r k : DihedralGroup δ))})
      (fun q => (q.1.1, ⟨q.1.2 - q.1.1, q.2⟩)) ⟨?_, ?_⟩).trans ?_
    · rintro ⟨⟨s, t⟩, hq⟩ ⟨⟨s', t'⟩, hq'⟩ h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      have : t = t' := sub_left_injective h2
      simp [this]
    · rintro ⟨s, ⟨d, hd⟩⟩
      refine ⟨⟨(s, s + d), by simpa using hd⟩, ?_⟩
      simp
    · rw [Nat.card_prod, Nat.card_zmod]
  rw [← h1, h2, card_even_rot]

end Dihedral

section KleinFour

open DihedralGroup

theorem dihedral_two_mul_self (x : DihedralGroup 2) : x * x = 1 := by
  revert x
  decide

theorem orderOf_eq_two_iff_of_sq {G : Type*} [Group G] (hsq : ∀ x : G, x * x = 1) (x : G) :
    orderOf x = 2 ↔ x ≠ 1 := by
  constructor
  · intro h h1
    rw [h1, orderOf_one] at h
    omega
  · intro h
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq x) h

theorem mem_zpowers_mul_iff_of_sq {G : Type*} [Group G] (hsq : ∀ x : G, x * x = 1) {j : G}
    (hj : orderOf j = 2) (a b : G) : j ∈ Subgroup.zpowers (a * b) ↔ a * b = j := by
  constructor
  · intro hmem
    have hy : (a * b) ^ 2 = 1 := by rw [pow_two]; exact hsq _
    have hord : orderOf (a * b) = 2 :=
      Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hy) (hj ▸ orderOf_dvd_of_mem_zpowers hmem)
    have h := (mem_zpowers_iff_eq_pow_half (d := 1) (by simpa using hord) one_ne_zero hj).mp hmem
    rw [pow_one] at h
    exact h.symm
  · intro h
    rw [h]
    exact Subgroup.mem_zpowers j

theorem two_div_ordProj_two : (2 : ℕ) / 2 ^ (2 : ℕ).factorization 2 = 1 := by
  rw [Nat.Prime.factorization_self Nat.prime_two]
  norm_num

theorem card_even_dihedral_two {j : DihedralGroup 2} (hj : orderOf j = 2) :
    Nat.card {x : DihedralGroup 2 // Even (orderOf x) ∧ x ^ (orderOf x / 2) = j} =
      2 - 2 / 2 ^ (2 : ℕ).factorization 2 := by
  rw [two_div_ordProj_two]
  have e : {x : DihedralGroup 2 // Even (orderOf x) ∧ x ^ (orderOf x / 2) = j} ≃
      {x : DihedralGroup 2 // x = j} :=
    Equiv.subtypeEquivRight fun x => by
      constructor
      · rintro ⟨he, hx⟩
        have hx1 : x ≠ 1 := by
          rintro rfl
          rw [orderOf_one] at he
          exact (by decide : ¬ Even 1) he
        rw [(orderOf_eq_two_iff_of_sq dihedral_two_mul_self x).mpr hx1] at hx
        simpa using hx
      · rintro rfl
        rw [hj]
        exact ⟨by decide, by simp⟩
  have := Unique.subtypeEq j
  rw [Nat.card_congr e, Nat.card_unique]

theorem card_pairs_dihedral_two {j : DihedralGroup 2} (hj : orderOf j = 2) :
    Nat.card {p : DihedralGroup 2 × DihedralGroup 2 // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧
      j ∈ Subgroup.zpowers (p.1 * p.2)} = 2 * (2 - 2 / 2 ^ (2 : ℕ).factorization 2) := by
  rw [two_div_ordProj_two]
  have hsq := dihedral_two_mul_self
  have hj1 : j ≠ 1 := (orderOf_eq_two_iff_of_sq hsq j).mp hj
  have hjj : j * j = 1 := hsq j
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hjj
  have h1 : Nat.card {a : DihedralGroup 2 // a ≠ 1 ∧ a ≠ j} =
      Nat.card {p : DihedralGroup 2 × DihedralGroup 2 // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧
        j ∈ Subgroup.zpowers (p.1 * p.2)} := by
    refine Nat.card_eq_of_bijective (fun a => ⟨(a.1, a.1 * j), ?_, ?_, ?_⟩) ⟨?_, ?_⟩
    · exact (orderOf_eq_two_iff_of_sq hsq _).mpr a.2.1
    · refine (orderOf_eq_two_iff_of_sq hsq _).mpr fun h => a.2.2 ?_
      rw [mul_eq_one_iff_eq_inv, hjinv] at h
      exact h
    · show j ∈ Subgroup.zpowers (a.1 * (a.1 * j))
      rw [← mul_assoc, hsq a.1, one_mul]
      exact Subgroup.mem_zpowers j
    · rintro ⟨a, ha⟩ ⟨a', ha'⟩ h
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
      exact Subtype.ext h.1
    · rintro ⟨⟨a, b⟩, ha, hb, hab⟩
      dsimp only at ha hb hab
      have hab' : a * b = j := (mem_zpowers_mul_iff_of_sq hsq hj a b).mp hab
      have ha1 : a ≠ 1 := (orderOf_eq_two_iff_of_sq hsq a).mp ha
      have hb1 : b ≠ 1 := (orderOf_eq_two_iff_of_sq hsq b).mp hb
      have haj : a ≠ j := by
        rintro rfl
        exact hb1 (mul_eq_left.mp hab')
      have hbe : b = a * j := by
        have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a)
        calc b = a⁻¹ * (a * b) := by rw [inv_mul_cancel_left]
          _ = a * j := by rw [hab', hainv]
      exact ⟨⟨a, ha1, haj⟩, by simp [hbe]⟩
  have h2 : Nat.card {a : DihedralGroup 2 // a ≠ 1 ∧ a ≠ j} = 2 := by
    have h := card_subtype_add_card_subtype_not (fun a : DihedralGroup 2 => a = 1 ∨ a = j)
    have h3 : Nat.card {a : DihedralGroup 2 // a = 1 ∨ a = j} = 2 := by
      rw [Nat.subtype_card ({1, j} : Finset (DihedralGroup 2)) (fun x => by simp)]
      exact Finset.card_pair hj1.symm
    rw [h3, DihedralGroup.nat_card] at h
    have h4 : Nat.card {a : DihedralGroup 2 // a ≠ 1 ∧ a ≠ j} =
        Nat.card {a : DihedralGroup 2 // ¬ (a = 1 ∨ a = j)} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun a => by rw [not_or])
    omega
  rw [← h1, h2]

end KleinFour

section Transport

variable {C D : Type*} [Group C] [Group D]

theorem card_transport_odd (e : C ≃* D) :
    Nat.card {x : C // Odd (orderOf x)} = Nat.card {y : D // Odd (orderOf y)} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by simp [MulEquiv.orderOf_eq])

theorem card_transport_even (e : C ≃* D) (i₀ : C) :
    Nat.card {x : C // Even (orderOf x) ∧ x ^ (orderOf x / 2) = i₀} =
      Nat.card {y : D // Even (orderOf y) ∧ y ^ (orderOf y / 2) = e i₀} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by simp [MulEquiv.orderOf_eq, ← map_pow])

theorem map_mem_zpowers_iff (e : C ≃* D) (a x : C) :
    e x ∈ Subgroup.zpowers (e a) ↔ x ∈ Subgroup.zpowers a := by
  simp only [Subgroup.mem_zpowers_iff, ← map_zpow, EmbeddingLike.apply_eq_iff_eq]

theorem card_transport_pairs (e : C ≃* D) (i₀ : C) :
    Nat.card {p : C × C // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ i₀ ∈ Subgroup.zpowers (p.1 * p.2)} =
      Nat.card {q : D × D // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧
        e i₀ ∈ Subgroup.zpowers (q.1 * q.2)} :=
  Nat.card_congr ((e.toEquiv.prodCongr e.toEquiv).subtypeEquiv fun p => by
    simp [MulEquiv.orderOf_eq, ← map_mul, map_mem_zpowers_iff])

theorem map_mem_center (e : C ≃* D) {x : C} (hx : x ∈ Subgroup.center C) :
    e x ∈ Subgroup.center D := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro g
  calc g * e x = e (e.symm g * x) := by simp
    _ = e (x * e.symm g) := by rw [hx (e.symm g)]
    _ = e x * g := by simp

end Transport

end OrdCnt

open OrdCnt

theorem involution_class_counts {I : Type} [Group I] [Finite I] (i₀ : I) (hi₀ : orderOf i₀ = 2)
    (hconj : ∀ u v : I, orderOf u = 2 → orderOf v = 2 → ∃ g : I, g * u * g⁻¹ = v) :
    Nat.card {u : I // orderOf u = 2} * Nat.card (Subgroup.centralizer ({i₀} : Set I)) = Nat.card I ∧
    Nat.card {x : I // Odd (orderOf x)} + Nat.card {u : I // orderOf u = 2} *
      Nat.card {x : I // x ∈ Subgroup.centralizer ({i₀} : Set I) ∧ Even (orderOf x) ∧
        x ^ (orderOf x / 2) = i₀} =
      Nat.card I ∧
    Nat.card {p : I × I // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} +
      Nat.card {u : I // orderOf u = 2} *
        Nat.card {p : I × I // p.1 ∈ Subgroup.centralizer ({i₀} : Set I) ∧
          p.2 ∈ Subgroup.centralizer ({i₀} : Set I) ∧
          orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ i₀ ∈ Subgroup.zpowers (p.1 * p.2)} =
      Nat.card {u : I // orderOf u = 2} * Nat.card {u : I // orderOf u = 2} := by
  refine ⟨card_involutions_mul_card_centralizer i₀ hi₀ hconj, ?_, ?_⟩
  · rw [← card_even_order i₀ hi₀ hconj]
    have h := card_subtype_add_card_subtype_not (fun x : I => Even (orderOf x))
    simpa only [Nat.not_even_iff_odd, add_comm] using h
  · rw [← card_pairs_even i₀ hi₀ hconj]
    have h := card_subtype_and_add_card_subtype_and_not
      (fun p : I × I => orderOf p.1 = 2 ∧ orderOf p.2 = 2)
      (fun p : I × I => Even (orderOf (p.1 * p.2)))
    have e : Nat.card {p : I × I // orderOf p.1 = 2 ∧ orderOf p.2 = 2} =
        Nat.card {u : I // orderOf u = 2} * Nat.card {u : I // orderOf u = 2} :=
      (Nat.card_congr (Equiv.subtypeProdEquivProd (p := fun u : I => orderOf u = 2)
        (q := fun u : I => orderOf u = 2))).trans (Nat.card_prod _ _)
    rw [← e, ← h]
    simp only [and_assoc, Nat.not_even_iff_odd, add_comm]

theorem dihedral_counts {δ : ℕ} (hδ : 2 ≤ δ) (hev : Even δ) {C : Type} [Group C]
    (eC : C ≃* DihedralGroup δ) (i₀ : C) (hi₀ : orderOf i₀ = 2) (hc : i₀ ∈ Subgroup.center C) :
    Nat.card {x : C // Odd (orderOf x)} = δ / 2 ^ δ.factorization 2 ∧
    Nat.card {x : C // Even (orderOf x) ∧ x ^ (orderOf x / 2) = i₀} = δ - δ / 2 ^ δ.factorization 2 ∧
    Nat.card {p : C × C // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ i₀ ∈ Subgroup.zpowers (p.1 * p.2)} =
      δ * (δ - δ / 2 ^ δ.factorization 2) := by
  have : NeZero δ := ⟨by omega⟩
  have hj : orderOf (eC i₀) = 2 := by rw [MulEquiv.orderOf_eq]; exact hi₀
  have hcD : eC i₀ ∈ Subgroup.center (DihedralGroup δ) := map_mem_center eC hc
  rw [card_transport_odd eC, card_transport_even eC i₀, card_transport_pairs eC i₀]
  refine ⟨card_odd_dihedral, ?_⟩
  obtain rfl | h4 : δ = 2 ∨ 4 ≤ δ := by
    obtain ⟨k, hk⟩ := hev
    omega
  · exact ⟨card_even_dihedral_two hj, card_pairs_dihedral_two hj⟩
  · exact ⟨card_even_dihedral (by omega) hj hcD, card_pairs_dihedral (by omega) hj hcD⟩

end CFSG.GH74.GLS.SP.Local
