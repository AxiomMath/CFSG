module

public import CFSG.Monster.Existence.StdOdd.Cert.Base
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowComponent

public section

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68

open Subgroup

section Odd

variable {G : Type*} [Group G]

theorem mem_of_odd_orderOf_of_index_eq_two {K : Subgroup G} (hK : K.index = 2) {y : G}
    (hodd : Odd (orderOf y)) : y ∈ K := by
  have : K.Normal := Subgroup.normal_of_index_eq_two hK
  have h2 : ((y : G) : G ⧸ K) ^ 2 = 1 := by
    have := pow_card_eq_one' (G := G ⧸ K) (x := ((y : G) : G ⧸ K))
    rwa [show Nat.card (G ⧸ K) = 2 by rw [← Subgroup.index_eq_card]; exact hK] at this
  obtain ⟨k, hk⟩ := hodd
  have h1 : ((y : G) : G ⧸ K) ^ (2 * k + 1) = 1 := by
    rw [← QuotientGroup.mk_pow, ← hk, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have h3 : ((y : G) : G ⧸ K) = 1 := by
    calc ((y : G) : G ⧸ K) = ((y : G) : G ⧸ K) ^ (2 * k + 1) := by
          rw [pow_succ, pow_mul, h2, one_pow, one_mul]
      _ = 1 := h1
  exact (QuotientGroup.eq_one_iff y).1 h3

theorem mem_of_odd_orderOf_of_card {H K : Subgroup G} [Finite G] (hKH : K ≤ H)
    (hcard : Nat.card H = 2 * Nat.card K) {x : G} (hxH : x ∈ H) (hodd : Odd (orderOf x)) :
    x ∈ K := by
  have hrel : K.relIndex H = 2 := by
    have h := Subgroup.relIndex_mul_card (H := K) (K := H)
    rw [inf_eq_left.2 hKH] at h
    have hpos : 0 < Nat.card K := Nat.card_pos
    rw [hcard] at h
    exact Nat.eq_of_mul_eq_mul_right hpos h
  have h1 : (K.subgroupOf H).index = 2 := hrel
  have h2 : (⟨x, hxH⟩ : H) ∈ K.subgroupOf H := by
    refine mem_of_odd_orderOf_of_index_eq_two h1 ?_
    rwa [Subgroup.orderOf_mk]
  exact h2

end Odd

section Cap

variable {G : Type*} [Group G]

theorem ncard_le_four_of_pow_four [Finite G] {T : Subgroup G} {x : G} (hxT : x ∈ T)
    (hxc : ∀ t ∈ T, t * x = x * t) (hx : orderOf x = 17) (hT : Nat.card T ≤ 68)
    {S : Set G} (hS : S ⊆ T) (hS4 : ∀ g ∈ S, g ^ 4 = 1) : S.ncard ≤ 4 := by
  let f : S × Fin 17 → T := fun p =>
    ⟨(p.1 : G) * x ^ (p.2 : ℕ), T.mul_mem (hS p.1.2) (T.pow_mem hxT _)⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨g, hg⟩, k⟩ ⟨⟨g', hg'⟩, k'⟩ h
    have h' : g * x ^ (k : ℕ) = g' * x ^ (k' : ℕ) := congrArg Subtype.val h
    have hgx : Commute g x := hxc g (hS hg)
    have hgx' : Commute g' x := hxc g' (hS hg')
    have hc : Commute g (x ^ (k : ℕ)) := hgx.pow_right _
    have hc' : Commute g' (x ^ (k' : ℕ)) := hgx'.pow_right _
    have h4 : x ^ (4 * (k : ℕ)) = x ^ (4 * (k' : ℕ)) := by
      have e1 : (g * x ^ (k : ℕ)) ^ 4 = x ^ (4 * (k : ℕ)) := by
        rw [hc.mul_pow, hS4 g hg, one_mul, ← pow_mul, mul_comm]
      have e2 : (g' * x ^ (k' : ℕ)) ^ 4 = x ^ (4 * (k' : ℕ)) := by
        rw [hc'.mul_pow, hS4 g' hg', one_mul, ← pow_mul, mul_comm]
      rw [← e1, ← e2, h']
    have hk : (k : ℕ) = (k' : ℕ) := by
      have := (pow_eq_pow_iff_modEq (x := x) (n := 4 * (k : ℕ)) (m := 4 * (k' : ℕ))).1 h4
      rw [hx] at this
      have hk17 := k.2
      have hk17' := k'.2
      unfold Nat.ModEq at this
      omega
    have hkk : k = k' := Fin.ext hk
    subst hkk
    have : g = g' := mul_right_cancel h'
    subst this
    rfl
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 17), Fintype.card_fin,
    Nat.card_coe_set_eq] at hcard
  omega

theorem orderOf_conj_eq (y g : G) : orderOf (g * y * g⁻¹) = orderOf y := by
  simpa using CFSG.Monster.Existence.StdOdd.Cert.orderOf_inv_mul_mul y g⁻¹

end Cap

section Orbit

theorem card_inf_centralizer_mul_ncard_of_orbit {G : Type} [Group G] (H : Subgroup G) (s : G)
    (O : Set G) (hst : ∀ h ∈ H, h * s * h⁻¹ ∈ O) (htr : ∀ s' ∈ O, ∃ h ∈ H, h * s * h⁻¹ = s') :
    Nat.card (H ⊓ centralizer ({s} : Set G) : Subgroup G) * O.ncard = Nat.card H := by
  have horb : ({y | ∃ h ∈ H, h * s * h⁻¹ = y} : Set G) = O := by
    ext y
    exact ⟨fun ⟨h, hh, hy⟩ => hy ▸ hst h hh, fun hy => htr y hy⟩
  rw [← horb]
  exact CFSG.EvenSporadicStandard.Solomon78.card_inf_centralizer_mul_ncard_conj H s

end Orbit

section Sylow

variable {G : Type*} [Group G]

theorem exists_conj_commute_of_prime [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : ¬ p ^ 2 ∣ Nat.card G) {x y : G} (hx : orderOf x = p) (hy : orderOf y = p) {z : G}
    (hz : Commute y z) : ∃ g : G, Commute x (g⁻¹ * z * g) := by
  obtain ⟨S, hS⟩ := CFSG.Monster.Existence.StdOdd.Cert.exists_sylow_eq_of_card_eq_prime hp2
    (zpowers x) (by rw [Nat.card_zpowers, hx])
  have hyp : IsPGroup p (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨g, hg⟩ := CFSG.Monster.Existence.StdOdd.Cert.exists_conj_mem_sylow S hyp
  rw [hS] at hg
  have hord : orderOf (g⁻¹ * y * g) = orderOf x := by
    rw [CFSG.Monster.Existence.StdOdd.Cert.orderOf_inv_mul_mul, hx, hy]
  have hcent := CFSG.Monster.Existence.StdOdd.Cert.centralizer_singleton_eq_of_mem_zpowers hg hord
  refine ⟨g, ?_⟩
  have hzz : (g⁻¹ * z * g) ∈ centralizer ({g⁻¹ * y * g} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have : y * z = z * y := hz.eq
    calc g⁻¹ * z * g * (g⁻¹ * y * g) = g⁻¹ * (z * y) * g := by group
      _ = g⁻¹ * (y * z) * g := by rw [this]
      _ = g⁻¹ * y * g * (g⁻¹ * z * g) := by group
  rw [hcent, mem_centralizer_singleton_iff] at hzz
  exact hzz.symm

end Sylow

section Cover

theorem card_centralizer_le_of_cover {E T : Type*} [Group E] [Finite E] [Group T] [Finite T]
    {K Z : Subgroup E} [Z.Normal] (hK : K.index = 2) (hZ : Nat.card Z = 2)
    (e : K ⧸ Z.subgroupOf K ≃* T)
    (hT : ∀ y : T, orderOf y = 17 → Nat.card (centralizer ({y} : Set T)) ≤ 17) {y : E}
    (hy : orderOf y = 17) : Nat.card (centralizer ({y} : Set E)) ≤ 68 := by
  have hyK : y ∈ K := mem_of_odd_orderOf_of_index_eq_two hK (by rw [hy]; decide)
  let y₀ : K := ⟨y, hyK⟩
  have hy₀ : orderOf y₀ = 17 := by rw [← hy]; exact Subgroup.orderOf_mk _ _
  let π : K →* T := e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf K))
  have hπ : ∀ g : K, π g = 1 → (g : E) ∈ Z := by
    intro g hg
    have : QuotientGroup.mk' (Z.subgroupOf K) g = 1 := (MulEquiv.map_eq_one_iff e).1 hg
    exact (QuotientGroup.eq_one_iff g).1 this
  have hπy : orderOf (π y₀) = 17 := by
    have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    refine orderOf_eq_prime (p := 17) ?_ ?_
    · rw [← map_pow, ← hy₀, pow_orderOf_eq_one, map_one]
    · intro h1
      have hz : y ∈ Z := hπ y₀ h1
      have hz2 : y ^ 2 = 1 := by
        have := pow_card_eq_one' (x := (⟨y, hz⟩ : Z))
        rw [hZ] at this
        exact congrArg Subtype.val this
      have := orderOf_dvd_of_pow_eq_one hz2
      rw [hy] at this
      omega
  let ψ : centralizer ({y₀} : Set K) →* T := π.comp (centralizer ({y₀} : Set K)).subtype
  have hrange : ψ.range ≤ centralizer ({π y₀} : Set T) := by
    rintro _ ⟨c, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hc : (c : K) * y₀ = y₀ * c := mem_centralizer_singleton_iff.1 c.2
    show π c * π y₀ = π y₀ * π c
    rw [← map_mul, ← map_mul, hc]
  have hker : Nat.card ψ.ker ≤ 2 := by
    let j : ψ.ker → Z := fun c => ⟨((c.1 : K) : E), hπ c.1 c.2⟩
    have hj : Function.Injective j := by
      intro a b h
      have := congrArg (fun z : Z => (z : E)) h
      exact Subtype.ext (Subtype.ext (Subtype.ext this))
    calc Nat.card ψ.ker ≤ Nat.card Z := Nat.card_le_card_of_injective j hj
      _ = 2 := hZ
  have hCK : Nat.card (centralizer ({y₀} : Set K)) ≤ 34 := by
    have h1 := Subgroup.card_ker_mul_card_range ψ
    have h2 : Nat.card ψ.range ≤ 17 :=
      (Subgroup.card_le_of_le hrange).trans (hT _ hπy)
    rw [← h1]
    calc Nat.card ψ.ker * Nat.card ψ.range ≤ 2 * 17 := Nat.mul_le_mul hker h2
      _ = 34 := by norm_num
  have hKC : Nat.card (K ⊓ centralizer ({y} : Set E) : Subgroup E) ≤ 34 := by
    let m : (K ⊓ centralizer ({y} : Set E) : Subgroup E) → centralizer ({y₀} : Set K) :=
      fun g => ⟨⟨g.1, g.2.1⟩,
        mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 g.2.2))⟩
    have hm : Function.Injective m := by
      intro a b h
      have := congrArg (fun z : centralizer ({y₀} : Set K) => ((z : K) : E)) h
      exact Subtype.ext this
    exact (Nat.card_le_card_of_injective m hm).trans hCK
  have hrel : K.relIndex (centralizer ({y} : Set E)) ∣ 2 := by
    have : K.Normal := Subgroup.normal_of_index_eq_two hK
    exact hK ▸ Subgroup.relIndex_dvd_index_of_normal K (centralizer ({y} : Set E))
  have hrel' := Subgroup.relIndex_mul_card (H := K) (K := centralizer ({y} : Set E))
  have hle : K.relIndex (centralizer ({y} : Set E)) ≤ 2 := Nat.le_of_dvd (by norm_num) hrel
  rw [← hrel']
  calc K.relIndex (centralizer ({y} : Set E)) *
        Nat.card (K ⊓ centralizer ({y} : Set E) : Subgroup E) ≤ 2 * 34 :=
      Nat.mul_le_mul hle hKC
    _ = 68 := by norm_num

theorem card_inf_centralizer_le_of_mulEquiv {G E : Type*} [Group G] [Group E] [Finite E] {u x : G}
    (hxu : x ∈ centralizer ({u} : Set G)) (ψ : ↥(centralizer ({u} : Set G)) ≃* E) :
    Nat.card (centralizer ({u} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) ≤
      Nat.card (centralizer ({ψ ⟨x, hxu⟩} : Set E)) := by
  have hcomm : ∀ g : ↥(centralizer ({u} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G),
      ψ ⟨(g : G), g.2.1⟩ * ψ ⟨x, hxu⟩ = ψ ⟨x, hxu⟩ * ψ ⟨(g : G), g.2.1⟩ := by
    intro g
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (mem_centralizer_singleton_iff.1 g.2.2))
  let m : ↥(centralizer ({u} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) →
      centralizer ({ψ ⟨x, hxu⟩} : Set E) := fun g =>
    ⟨ψ ⟨(g : G), g.2.1⟩, mem_centralizer_singleton_iff.2 (hcomm g)⟩
  have hm : Function.Injective m := by
    intro a b h
    have h1 := ψ.injective (congrArg (fun z : centralizer ({ψ ⟨x, hxu⟩} : Set E) => (z : E)) h)
    exact Subtype.ext (congrArg (fun z : ↥(centralizer ({u} : Set G)) => (z : G)) h1)
  exact Nat.card_le_card_of_injective m hm

end Cover

end CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68
