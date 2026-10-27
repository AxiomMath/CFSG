module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Axb
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs18
public import CFSG.GH74.GLS.Stage2.Local.Bar
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.L193

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20
open scoped commutatorElement

section Conj

variable {G : Type} [Group G]

theorem mem_conjugate_iff' {H : Subgroup G} {g x : G} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold conjugate
  rw [Subgroup.mem_map_equiv]
  simp

theorem centralizer_conj (z g : G) :
    centralizer ({g⁻¹ * z * g} : Set G) = conjugate (centralizer ({z} : Set G)) g := by
  ext x
  rw [mem_conjugate_iff', Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x * g⁻¹ * z = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by rw [h]
      _ = z * (g * x * g⁻¹) := by group
  · intro h
    calc x * (g⁻¹ * z * g) = g⁻¹ * (g * x * g⁻¹ * z) * g := by group
      _ = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * z * g) * x := by group

end Conj

section Cons

variable {G : Type} [Group G] [Finite G]

structure Cons1813 (z : G) (p : ℕ) : Prop where
  nG : ∀ U : Subgroup G, U ≤ Op p (Cen z) → (U.subgroupOf (Op p (Cen z))).Normal → IsElementaryAbelian p ↥U →
    Nat.card ↥U = p ^ 2 → ∀ X : Subgroup G, X ≤ Fof p (Cen z) U → X ≠ ⊥ →
      (∃ r : ℕ, r.Prime ∧ IsElementaryAbelian r ↥X) → normalizer (X : Set G) ≤ Cen z
  b : ∀ U : Subgroup G, U ≤ Op p (Cen z) → (U.subgroupOf (Op p (Cen z))).Normal → IsElementaryAbelian p ↥U →
    Nat.card ↥U = p ^ 2 → ∀ g : G, ∀ V : Subgroup G, V ≤ Qof p (Cen z) U → IsElementaryAbelian p ↥V →
      p ^ 2 ≤ Nat.card ↥V → zpowers z ⊔ V ≤ conjugate (Cen z) g → conjugate (Cen z) g = Cen z

structure Ab (G : Type) [Group G] [Finite G] (z t g : G) (p : ℕ) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  rank : 3 ≤ pRank p ↥(Op p (Cen z))
  coat : IsCoatom (Cen z)
  simple : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤
  z2 : z * z = 1
  t2 : t * t = 1
  zt : z * t = t * z
  tg : g⁻¹ * z * g = t
  tne : t ≠ z
  cons : Cons1813 z p

variable {z t g : G} {p : ℕ}

theorem Ab.z_ne_one (h : Ab G z t g p) : z ≠ 1 := by
  intro hz
  apply h.tne
  rw [← h.tg, hz]; group

theorem Ab.t_mem_M (h : Ab G z t g p) : t ∈ Cen z := by
  rw [Subgroup.mem_centralizer_singleton_iff]; exact h.zt.symm

theorem Ab.cen_t_eq (h : Ab G z t g p) : centralizer ({t} : Set G) = conjugate (Cen z) g := by
  rw [← h.tg]; exact centralizer_conj z g

theorem Ab.z_mem_N (h : Ab G z t g p) : z ∈ conjugate (Cen z) g := by
  rw [← h.cen_t_eq, Subgroup.mem_centralizer_singleton_iff]; exact h.zt

theorem Ab.N_ne (h : Ab G z t g p) : conjugate (Cen z) g ≠ Cen z := by
  intro hN
  apply h.tne
  have hgN : g ∈ normalizer ((Cen z : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← mem_conjugate_iff' (H := Cen z) (g := g), hN]
  have hg : g ∈ Cen z := by
    have hle : Cen z ≤ normalizer ((Cen z : Subgroup G) : Set G) := Subgroup.le_normalizer
    by_cases heq : normalizer ((Cen z : Subgroup G) : Set G) = Cen z
    · rw [← heq]; exact hgN
    · have hlt : Cen z < normalizer ((Cen z : Subgroup G) : Set G) := lt_of_le_of_ne hle (Ne.symm heq)
      have htop := h.coat.2 _ hlt
      have hnorm : (Cen z).Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases h.simple _ hnorm with hbot | htop'
      · exfalso
        have hz : z ∈ Cen z := mem_Cen_self z
        rw [hbot, Subgroup.mem_bot] at hz
        exact h.z_ne_one hz
      · exact absurd htop' h.coat.1
  have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [← h.tg]
  calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
    _ = g⁻¹ * (g * z) := by rw [hgz]
    _ = z := by group

end Cons

section PGroupLemmas

variable {G : Type} [Group G]

theorem Op_norm (r : ℕ) (M : Subgroup G) {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ Op r M) : m * x * m⁻¹ ∈ Op r M :=
  Op_conj_mem r (fun _ hc _ hb => M.mul_mem (M.mul_mem hc hb) (M.inv_mem hc)) hm hx

theorem exists_pow_order_p {p : ℕ} [hp : Fact p.Prime] {e : G} (hpe : ∃ k : ℕ, orderOf e = p ^ k)
    (he1 : e ≠ 1) : ∃ n : ℕ, (e ^ n) ^ p = 1 ∧ e ^ n ≠ 1 := by
  obtain ⟨k, hk⟩ := hpe
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact he1 (orderOf_eq_one_iff.mp (by simpa using hk))
  refine ⟨p ^ (k - 1), ?_, ?_⟩
  · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0), ← hk]
    exact pow_orderOf_eq_one e
  · refine pow_ne_one_of_lt_orderOf (pow_pos hp.out.pos _).ne' ?_
    rw [hk]
    exact Nat.pow_lt_pow_right hp.out.one_lt (by omega)

theorem inverted_of_no_fixed {p : ℕ} [hp : Fact p.Prime] [Finite G] {K : Subgroup G} {t : G} (hK : IsPGroup p K)
    (ht2 : t * t = 1) (hnorm : ∀ e ∈ K, t * e * t⁻¹ ∈ K)
    (hfix : ∀ e ∈ K, t * e * t⁻¹ = e → e ^ p = 1 → e = 1) : ∀ e ∈ K, t * e * t⁻¹ = e⁻¹ := by
  refine inverted_of_fixed_point_free ht2 hnorm ?_
  intro e he hte
  by_contra hne
  obtain ⟨k, hk⟩ := hK ⟨e, he⟩
  have hpow : e ^ (p ^ k) = 1 := congrArg Subtype.val hk
  have hord : ∃ k : ℕ, orderOf e = p ^ k := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hpow)
    exact ⟨j, hj⟩
  obtain ⟨n, hn1, hn2⟩ := exists_pow_order_p hord hne
  have hfix' : t * e ^ n * t⁻¹ = e ^ n := by rw [← conj_pow, hte]
  exact hn2 (hfix (e ^ n) (K.pow_mem he n) hfix' hn1)

theorem isCoatom_conjugate' {K : Subgroup G} (hK : IsCoatom K) (g : G) : IsCoatom (conjugate K g) := by
  have e : conjugate K g = K.comap (MulAut.conj g).toMonoidHom := by
    ext x; rw [mem_conjugate_iff']; simp
  rw [e]
  exact (Subgroup.isCoatom_comap (MulAut.conj g)).mpr hK

theorem axb_helper {p : ℕ} [hp : Fact p.Prime] [Finite G] (hp2 : p ≠ 2) {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    {D X : Subgroup G} (hD : IsPGroup p D) (hX : IsPGroup p X)
    (hzD : ∀ d ∈ D, z * d * z⁻¹ ∈ D) (hxD : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D)
    (hzx : ∀ x ∈ X, z * x = x * z)
    (hC : ∀ d ∈ D, (∀ x ∈ X, d * x = x * d) → z * d = d * z) : ∀ d ∈ D, z * d = d * z := by
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have hcop : Nat.Coprime p (Nat.card ↥(zpowers z)) := by
    rw [Nat.card_zpowers, hord]
    exact (Nat.coprime_primes hp.out Nat.prime_two).mpr hp2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzN : zpowers z ≤ normalizer (D : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨fun hd => hzD d hd, fun hd => ?_⟩
    have := hzD _ hd
    have e : z * (z * d * z⁻¹) * z⁻¹ = d := by rw [hzi]; calc z * (z * d * z) * z = (z * z) * d * (z * z) := by group
      _ = d := by rw [hz2]; group
    rwa [e] at this
  have hXN : X ≤ normalizer (D : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨fun hd => hxD x hx d hd, fun hd => ?_⟩
    have := hxD x⁻¹ (X.inv_mem hx) _ hd
    have e : x⁻¹ * (x * d * x⁻¹) * x⁻¹⁻¹ = d := by group
    rwa [e] at this
  have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ X, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((Commute.zpow_left (show Commute z b from hzx b hb) k)).eq
  have hcent : zpowers z ≤ centralizer ((D ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro d hd
    have := hC d hd.1 (fun x hx => (Subgroup.mem_centralizer_iff.mp hd.2 x hx).symm)
    exact this.symm
  have h := CFSG.GH74.GLS.Stage2.Bender.Thm1.ig_11_7_thm G p hp.out (zpowers z) X D hD hX hcop hzN hXN hcomm hcent
  intro d hd
  exact (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_zpowers z)) d hd).symm

theorem isPGroup_conjugate {p : ℕ} {H : Subgroup G} (hH : IsPGroup p H) (g : G) : IsPGroup p (conjugate H g) :=
  hH.of_equiv (Subgroup.equivMapOfInjective _ _ (MulAut.conj g⁻¹).injective)

theorem card_conjugate (H : Subgroup G) (g : G) : Nat.card ↥(conjugate H g) = Nat.card ↥H :=
  (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj g⁻¹).injective).toEquiv).symm

theorem conjugate_mono {H K : Subgroup G} (h : H ≤ K) (g : G) : conjugate H g ≤ conjugate K g := by
  intro x hx
  rw [mem_conjugate_iff'] at hx ⊢
  exact h hx

theorem op_conjugate_le [Finite G] (r : ℕ) (M : Subgroup G) (g : G) :
    conjugate (Op r M) g ≤ Op r (conjugate M g) := by
  refine le_Op_of_normalized r (conjugate_mono (Subgroup.map_subtype_le _) g) (fun b hb w hw => ?_)
    (isPGroup_conjugate (isPGroup_Op r M) g)
  rw [mem_conjugate_iff'] at hb hw ⊢
  have e : g * (b * w * b⁻¹) * g⁻¹ = (g * b * g⁻¹) * (g * w * g⁻¹) * (g * b * g⁻¹)⁻¹ := by group
  rw [e]
  exact Op_norm r M hb hw

theorem isElementaryAbelian_zpowers {p : ℕ} {x : G} (hx : x ^ p = 1) : IsElementaryAbelian p ↥(zpowers x) := by
  have hc : IsMulCommutative ↥(zpowers x) := inferInstance
  refine { exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  rfl

theorem exists_pgroup_ge [Finite G] {p : ℕ} [Fact p.Prime] {M D : Subgroup G} (hDM : D ≤ M) (hD : IsPGroup p D) :
    ∃ T : Subgroup G, T ≤ M ∧ IsPGroup p T ∧ D ≤ T ∧ Op p M ≤ T := by
  have hD' : IsPGroup p (D.subgroupOf M) := hD.comap_subtype
  obtain ⟨T₀, hT₀⟩ := hD'.exists_le_sylow
  refine ⟨(T₀ : Subgroup ↥M).map M.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact T₀.isPGroup'.of_equiv (Subgroup.equivMapOfInjective (T₀ : Subgroup ↥M) M.subtype M.subtype_injective)
  · intro x hx
    exact ⟨⟨x, hDM hx⟩, hT₀ hx, rfl⟩
  · have hle : pCore p ↥M ≤ (T₀ : Subgroup ↥M) := IsPGroup.le_sylow_of_normal (pCore_isPGroup (G := ↥M) (p := p)) T₀
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hle hy, rfl⟩

theorem rank_subgroupOf [Finite G] {p : ℕ} (hp : p.Prime) {P T : Subgroup G} (hPT : P ≤ T) {k : ℕ}
    (hk : k ≤ Open.pRank p P) : k ≤ Open.pRank p (P.subgroupOf T) := by
  obtain ⟨E, hEP, hE, hEc⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp hk
  have hET : E ≤ T := hEP.trans hPT
  have hcard : Nat.card ↥(E.subgroupOf T) = p ^ k := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hET).toEquiv
  have hcomm : IsMulCommutative ↥(E.subgroupOf T) := by
    have hc := hE.1
    exact ⟨⟨fun a b => by
      apply Subtype.ext
      apply Subtype.ext
      have h1 := hc.is_comm.comm (⟨a.1, a.2⟩ : ↥E) ⟨b.1, b.2⟩
      exact congrArg (fun w : ↥E => (w : G)) h1⟩⟩
  have hel : Open.IsElemAbelian p (E.subgroupOf T) := ⟨hcomm, fun x hx => by
    apply Subtype.ext
    exact hE.2 x.1 hx⟩
  exact CFSG.SectionRank.le_pRank (G := ↥T) hp.one_lt (H := P.subgroupOf T) (E := E.subgroupOf T)
    (Subgroup.subgroupOf_mono T hEP) hel hcard

end PGroupLemmas


end CFSG.GH74.GLS.Stage2.Final.Thm4.L193
