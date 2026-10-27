module

public import CFSG.GH74.SectionalRank
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section Coprime

theorem exists_fixed_of_odd_coset {K : Type} [Group K] [Finite K] (N : Subgroup K) [N.Normal]
    (hodd : Odd (Nat.card N)) (t : K) (ht : t * t = 1) (h : K) (hh : t * h * t⁻¹ * h⁻¹ ∈ N) :
    ∃ n ∈ N, t * (h * n) * t⁻¹ = h * n := by
  classical
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let T : Type := {x : K // ∃ n ∈ N, x = h * n}
  have : Fintype T := Fintype.ofFinite T
  have hmem : ∀ x : T, t * x.1 * t⁻¹ ∈ {y : K | ∃ n ∈ N, y = h * n} := by
    intro x
    obtain ⟨n, hn, hx⟩ := x.2
    refine ⟨h⁻¹ * (t * h * t⁻¹ * h⁻¹) * h * (t * n * t⁻¹), ?_, ?_⟩
    · refine N.mul_mem (by simpa using Subgroup.Normal.conj_mem inferInstance _ hh h⁻¹) ?_
      simpa using Subgroup.Normal.conj_mem inferInstance n hn t
    · rw [hx]; group
  let σ : Function.End T := fun x => ⟨t * x.1 * t⁻¹, hmem x⟩
  have hσ : σ ^ 2 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    show t * (t * x.1 * t⁻¹) * t⁻¹ = x.1
    rw [hti]
    calc t * (t * x.1 * t) * t = (t * t) * x.1 * (t * t) := by group
      _ = x.1 := by rw [ht]; group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := T) (f := σ) (p := 2) (n := 1) hσ (hp := ⟨Nat.prime_two⟩)
  have hcard : Fintype.card T = Nat.card N := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.symm (Equiv.ofBijective (fun n : N => (⟨h * n.1, n.1, n.2, rfl⟩ : T)) ⟨?_, ?_⟩))
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (mul_left_cancel this)
    · rintro ⟨x, n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  have hodd' : Fintype.card T % 2 = 1 := by rw [hcard]; exact Nat.odd_iff.mp hodd
  have hfix : Fintype.card (Function.fixedPoints σ) ≠ 0 := by
    intro h0
    have := hmod
    rw [h0] at this
    have h2 : Fintype.card T % 2 = 0 := by
      have := (Nat.modEq_iff_dvd' (Nat.zero_le _)).mp this.symm
      simpa using Nat.mod_eq_zero_of_dvd (by simpa using this)
    omega
  obtain ⟨⟨x, hx⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hfix)
  obtain ⟨n, hn, hxn⟩ := x.2
  refine ⟨n, hn, ?_⟩
  have hx' : σ x = x := hx
  have := congrArg Subtype.val hx'
  simpa [σ, hxn] using this

end Coprime

section Sections

variable {G : Type} [Group G] [Finite G]

theorem csec_of_sig4B {z : G} {H₀ : Subgroup G} (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀)
    (hz2 : z * z = 1) (hodd : Odd (Nat.card ↥H₁)) :
    ∃ (D : Subgroup G) (f : ↥D →* ↥(centralizer ({zSec z H₀ hz H₁} : Set (Sec H₀ H₁)))),
      D ≤ centralizer ({z} : Set G) ∧ Function.Surjective f := by
  classical
  set zb : Sec H₀ H₁ := zSec z H₀ hz H₁ with hzb
  let D : Subgroup G := centralizer ({z} : Set G) ⊓ H₀
  have hDH : D ≤ H₀ := inf_le_right
  let g : ↥D →* Sec H₀ H₁ := (QuotientGroup.mk' H₁).comp (Subgroup.inclusion hDH)
  have hg : ∀ d : ↥D, g d ∈ centralizer ({zb} : Set (Sec H₀ H₁)) := by
    intro d
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hd : (d : G) * z = z * (d : G) := Subgroup.mem_centralizer_singleton_iff.mp d.2.1
    show QuotientGroup.mk (⟨(d : G), hDH d.2⟩ : ↥H₀) * QuotientGroup.mk (⟨z, hz⟩ : ↥H₀) =
      QuotientGroup.mk (⟨z, hz⟩ : ↥H₀) * QuotientGroup.mk (⟨(d : G), hDH d.2⟩ : ↥H₀)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext hd)
  refine ⟨D, g.codRestrict _ hg, inf_le_left, ?_⟩
  rintro ⟨a, ha⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective a
  have hcomm : zb * QuotientGroup.mk h = QuotientGroup.mk h * zb :=
    Subgroup.mem_centralizer_singleton_iff.mp ha |>.symm
  have hz0 : (⟨z, hz⟩ : ↥H₀) * ⟨z, hz⟩ = 1 := Subtype.ext hz2
  have hmem : (⟨z, hz⟩ : ↥H₀) * h * (⟨z, hz⟩ : ↥H₀)⁻¹ * h⁻¹ ∈ H₁ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    have : zb * QuotientGroup.mk h * (zb)⁻¹ * (QuotientGroup.mk h)⁻¹ = 1 := by
      rw [hcomm]; group
    exact this
  obtain ⟨n, hn, hfix⟩ := exists_fixed_of_odd_coset H₁ hodd ⟨z, hz⟩ hz0 h hmem
  have hcomm' : ((h * n : ↥H₀) : G) * z = z * ((h * n : ↥H₀) : G) := by
    have := congrArg Subtype.val hfix
    have hti : (⟨z, hz⟩ : ↥H₀)⁻¹ = ⟨z, hz⟩ := inv_eq_of_mul_eq_one_right hz0
    rw [hti] at this
    have h2 : (z * ((h * n : ↥H₀) : G)) * z = (h * n : ↥H₀) := by simpa using this
    calc ((h * n : ↥H₀) : G) * z = (z * z) * ((h * n : ↥H₀) : G) * z := by rw [hz2]; simp
      _ = z * (z * ((h * n : ↥H₀) : G) * z) := by group
      _ = z * ((h * n : ↥H₀) : G) := by rw [h2]
  refine ⟨⟨((h * n : ↥H₀) : G), Subgroup.mem_centralizer_singleton_iff.mpr hcomm', (h * n).2⟩, ?_⟩
  apply Subtype.ext
  show QuotientGroup.mk (⟨((h * n : ↥H₀) : G), (h * n).2⟩ : ↥H₀) = QuotientGroup.mk h
  have : (⟨((h * n : ↥H₀) : G), (h * n).2⟩ : ↥H₀) = h * n := rfl
  rw [this, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, mul_one]

theorem gen4_sec (hG : Gen4 G) (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] :
    Gen4 (Sec H₀ H₁) :=
  SectionalTwoRankLE.quotient H₁ (SectionalTwoRankLE.subgroup H₀ hG)

end Sections

section InnerAction

variable {A : Type} [Group A] [Finite A]

omit [Finite A] in
theorem normal_centralizer_of_normal (K : Subgroup A) [hK : K.Normal] :
    (centralizer (K : Set A)).Normal := by
  refine ⟨fun d hd g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hd ⊢
  intro k hk
  have h1 : g⁻¹ * k * g ∈ K := by simpa using hK.conj_mem k hk g⁻¹
  have h2 := hd _ h1
  calc k * (g * d * g⁻¹) = g * ((g⁻¹ * k * g) * d) * g⁻¹ := by group
    _ = g * (d * (g⁻¹ * k * g)) * g⁻¹ := by rw [h2]
    _ = g * d * g⁻¹ * k := by group

theorem le_of_le_sup_centralizer {p : ℕ} [hp : Fact p.Prime] (K : Subgroup A) [hK : K.Normal]
    (hop : CFSG.pCore p A = ⊥) {X : Subgroup A} (hXp : IsPGroup p ↥X) (hXn : (K ⊔ X).Normal)
    (hXle : X ≤ K ⊔ centralizer (K : Set A)) : X ≤ K := by
  classical
  set D : Subgroup A := centralizer (K : Set A) with hD
  have hDn : D.Normal := normal_centralizer_of_normal K
  set T : Subgroup A := D ⊓ (K ⊔ X) with hT
  have hTn : T.Normal := inferInstance
  let π : A →* A ⧸ K := QuotientGroup.mk' K
  have hmap : (K ⊔ X).map π = X.map π := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self K, bot_sup_eq]
  have hXmap : IsPGroup p ↥(X.map π) := hXp.map π
  let f : ↥T →* ↥(X.map π) :=
    (π.comp T.subtype).codRestrict (X.map π) fun t => by
      rw [← hmap]; exact Subgroup.mem_map_of_mem π t.2.2
  have hker : f.ker ≤ Subgroup.center ↥T := by
    intro t ht
    have hπ : π (t : A) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp ht)
      simpa [f] using this
    have htK : (t : A) ∈ K := (QuotientGroup.eq_one_iff _).mp hπ
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp s.2.1 (t : A) htK
    exact this.symm
  have hnil : Group.IsNilpotent ↥(X.map π) := hXmap.isNilpotent
  have hTnil : Group.IsNilpotent ↥T := Subgroup.isNilpotent_of_ker_le_center f hker
  obtain ⟨P⟩ : Nonempty (Sylow p ↥T) := inferInstance
  have hPn : (P : Subgroup ↥T).Normal := inferInstance
  have hPc : (P : Subgroup ↥T).Characteristic := Sylow.characteristic_of_normal P hPn
  set Q : Subgroup A := (P : Subgroup ↥T).map T.subtype with hQ
  have hQp : IsPGroup p ↥Q := (P.isPGroup').map T.subtype
  have hQn : Q.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨t, ht, rfl⟩ := hn
    refine ⟨(MulAut.conjNormal g : MulAut ↥T) t, ?_, ?_⟩
    · have hfix := (hPc.fixed (MulAut.conjNormal g : MulAut ↥T).symm).le
      have hmem : (MulAut.conjNormal g : MulAut ↥T) t ∈ (P : Subgroup ↥T) := by
        apply hfix
        rw [Subgroup.mem_comap]
        have e : ((MulAut.conjNormal g : MulAut ↥T).symm.toMonoidHom) ((MulAut.conjNormal g : MulAut ↥T) t) = t :=
          MulEquiv.symm_apply_apply _ t
        rw [e]
        exact ht
      exact hmem
    · simp [MulAut.conjNormal_apply]
  have hQle : Q ≤ CFSG.pCore p A := le_sSup ⟨hQn, hQp⟩
  have hQbot : Q = ⊥ := le_bot_iff.mp (hop ▸ hQle)
  have hPbot : (P : Subgroup ↥T) = ⊥ := by
    rw [hQ] at hQbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective).mp hQbot
  have hPcard : Nat.card ↥(P : Subgroup ↥T) = 1 := by
    rw [hPbot]; simp
  have hcop : ¬ p ∣ Nat.card ↥T := by
    intro hdvd
    have h1 := P.card_eq_multiplicity
    rw [hPcard] at h1
    have hpos : 0 < (Nat.card ↥T).factorization p :=
      (Nat.Prime.factorization_pos_of_dvd hp.out Nat.card_pos.ne' hdvd)
    have : 1 < p ^ (Nat.card ↥T).factorization p := Nat.one_lt_pow hpos.ne' hp.out.one_lt
    omega
  have hTK : T ≤ K := by
    intro t ht
    have hpg : IsPGroup p ↥(X.map π) := hXmap
    let t' : ↥(X.map π) := f ⟨t, ht⟩
    obtain ⟨m, hm⟩ := hpg t'
    have h1 : orderOf t' ∣ orderOf (⟨t, ht⟩ : ↥T) := orderOf_map_dvd f _
    have h2 : orderOf (⟨t, ht⟩ : ↥T) ∣ Nat.card ↥T := orderOf_dvd_natCard _
    have h3 : orderOf t' ∣ p ^ m := orderOf_dvd_of_pow_eq_one hm
    have h4 : orderOf t' = 1 := by
      by_contra hne
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp h3
      have hj0 : j ≠ 0 := by
        rintro rfl
        simp at hj
        exact hne (orderOf_eq_one_iff.mpr hj)
      have : p ∣ orderOf t' := by rw [hj]; exact dvd_pow_self p hj0
      exact hcop (this.trans (h1.trans h2))
    have h5 : t' = 1 := orderOf_eq_one_iff.mp h4
    have h6 : π t = 1 := by
      have := congrArg Subtype.val h5
      simpa [t', f] using this
    exact (QuotientGroup.eq_one_iff _).mp h6
  intro x hx
  have hx' : x ∈ D ⊔ K := by rw [sup_comm]; exact hXle hx
  rw [← SetLike.mem_coe, Subgroup.mul_normal D K] at hx'
  obtain ⟨d, hd, k, hk, rfl⟩ := hx'
  have hdT : d ∈ T := by
    refine ⟨hd, ?_⟩
    have : d = (d * k) * k⁻¹ := by simp
    rw [this]
    exact (K ⊔ X).mul_mem (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_left (K.inv_mem hk))
  exact K.mul_mem (hTK hdT) hk

omit [Finite A] in
theorem z_mem_normalizer_of_sig4A {z : A} {p : ℕ} {X : Subgroup A} (hA : Sig4A z (⊤ : Subgroup A) p X) :
    z ∈ normalizer (X : Set A) :=
  hA.inv z (Subgroup.mem_top z) (Subgroup.mem_centralizer_singleton_iff.mpr rfl)

omit [Finite A] in
theorem normal_sup_of_gen {K X : Subgroup A} [hK : K.Normal] {z : A}
    (hgen : K ⊔ X ⊔ zpowers z = ⊤) (hz : z ∈ normalizer (X : Set A)) : (K ⊔ X).Normal := by
  have key : ∀ g ∈ normalizer (X : Set A), ∀ a ∈ K ⊔ X, g * a * g⁻¹ ∈ K ⊔ X := by
    intro g hg a ha
    rw [sup_comm, ← SetLike.mem_coe, Subgroup.mul_normal X K] at ha
    obtain ⟨x, hx, k, hk, rfl⟩ := ha
    have h1 : g * x * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have h2 : g * k * g⁻¹ ∈ K := hK.conj_mem k hk g
    have : g * (x * k) * g⁻¹ = (g * x * g⁻¹) * (g * k * g⁻¹) := by group
    rw [this]
    exact (K ⊔ X).mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left h2)
  have hzN : z ∈ normalizer ((K ⊔ X : Subgroup A) : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact key z hz a
    · intro ha
      have hz' : z⁻¹ ∈ normalizer (X : Set A) := (normalizer (X : Set A)).inv_mem hz
      have h1 := key z⁻¹ hz' (z * a * z⁻¹) ha
      have e : z⁻¹ * (z * a * z⁻¹) * z⁻¹⁻¹ = a := by group
      rwa [e] at h1
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen]
  exact sup_le (sup_le (le_sup_left.trans Subgroup.le_normalizer) (le_sup_right.trans Subgroup.le_normalizer))
    ((Subgroup.zpowers_le).mpr hzN)

theorem x_le_layer_of_le_sup {z : A} {p : ℕ} {X : Subgroup A} (hA : Sig4A z (⊤ : Subgroup A) p X)
    (hop : CFSG.pCore p A = ⊥) (hgen : layer A ⊔ X ⊔ zpowers z = ⊤)
    (hXle : X ≤ layer A ⊔ centralizer ((layer A : Subgroup A) : Set A)) : X ≤ layer A := by
  have : Fact p.Prime := ⟨hA.prime⟩
  have hc : (layer A).Characteristic := LocalCores.layer_characteristic
  have : (layer A).Normal := inferInstance
  exact le_of_le_sup_centralizer (layer A) hop hA.pgroup
    (normal_sup_of_gen hgen (z_mem_normalizer_of_sig4A hA)) hXle

theorem x_le_layer_of_comm {z : A} (hz2 : z * z = 1) {p : ℕ} {X : Subgroup A}
    (hA : Sig4A z (⊤ : Subgroup A) p X) (hop : CFSG.pCore p A = ⊥)
    (hgen : layer A ⊔ X ⊔ zpowers z = ⊤)
    (hcomm : ∀ x ∈ X, ⁅x, z⁆ ∈ layer A ⊔ centralizer ((layer A : Subgroup A) : Set A)) :
    X ≤ layer A := by
  refine x_le_layer_of_le_sup hA hop hgen ?_
  rw [← hA.comm]
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hz2' : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
  rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [zpow_mul, hz2', one_zpow, commutatorElement_one_right]
    exact Subgroup.one_mem _
  · rw [zpow_add_one, zpow_mul, hz2', one_zpow, one_mul]
    exact hcomm x hx

end InnerAction

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
