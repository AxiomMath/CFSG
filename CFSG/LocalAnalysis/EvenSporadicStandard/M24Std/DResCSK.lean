module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSQuasi
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResE81

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open
open scoped commutatorElement

theorem perm6_cent (σ : Equiv.Perm (Fin 6))
    (h : ∀ a ∈ alternatingGroup (Fin 6), σ * a = a * σ) : σ = 1 := by
  refine Equiv.ext fun x => ?_
  by_contra hx
  have hx' : σ x ≠ x := hx
  obtain ⟨p, q, hpq, hpx, hpy, hqx, hqy⟩ : ∃ p q : Fin 6, p ≠ q ∧ p ≠ x ∧ p ≠ σ x ∧ q ≠ x ∧
      q ≠ σ x := by
    have : ∀ x y : Fin 6, ∃ p q : Fin 6, p ≠ q ∧ p ≠ x ∧ p ≠ y ∧ q ≠ x ∧ q ≠ y := by decide
    exact this x (σ x)
  set a : Equiv.Perm (Fin 6) := Equiv.swap x p * Equiv.swap p q with ha
  have ha6 : a ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, ha, map_mul, Equiv.Perm.sign_swap (Ne.symm hpx),
      Equiv.Perm.sign_swap hpq]
    decide
  have hax : a x = p := by
    rw [ha, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hpx) (Ne.symm hqx),
      Equiv.swap_apply_left]
  have hay : a (σ x) = σ x := by
    rw [ha, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hpy) (Ne.symm hqy),
      Equiv.swap_apply_of_ne_of_ne hx' (Ne.symm hpy)]
  have hc := congrArg (fun f : Equiv.Perm (Fin 6) => f x) (h a ha6)
  simp only [Equiv.Perm.mul_apply, hax, hay] at hc
  exact hpx (σ.injective hc)

theorem commutator_mul_central {Y : Type} [Group Y] {a b x x' : Y} (hxb : x * b = b * x)
    (hxx' : x * x' = x' * x) (hx'a : x' * a = a * x') : ⁅a * x, b * x'⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  have h1 : x' * a⁻¹ = a⁻¹ * x' := (Commute.inv_right hx'a).eq
  have h5 : x * x' * x⁻¹ = x' := by
    calc x * x' * x⁻¹ = x' * x * x⁻¹ := by rw [← hxx']
      _ = x' := by group
  calc a * x * (b * x') * (a * x)⁻¹ * (b * x')⁻¹
      = a * (x * b) * x' * x⁻¹ * a⁻¹ * x'⁻¹ * b⁻¹ := by group
    _ = a * (b * x) * x' * x⁻¹ * a⁻¹ * x'⁻¹ * b⁻¹ := by rw [hxb]
    _ = a * b * (x * x' * x⁻¹) * a⁻¹ * x'⁻¹ * b⁻¹ := by group
    _ = a * b * x' * a⁻¹ * x'⁻¹ * b⁻¹ := by rw [h5]
    _ = a * b * (x' * a⁻¹) * x'⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * x') * x'⁻¹ * b⁻¹ := by rw [h1]
    _ = a * b * a⁻¹ * b⁻¹ := by group

section CYHyp

variable {Y : Type} [Group Y]

structure CYHyp (t : Y) (K : Subgroup Y) (φ : K →* Equiv.Perm (Fin 6)) : Prop where
  order : orderOf t = 2
  cent : centralizer ({t} : Set Y) = K ⊔ zpowers t
  comm : ∀ k ∈ K, k * t = t * k
  not_mem : t ∉ K
  surj : Function.Surjective φ
  card_ker : Nat.card φ.ker = 3
  perfect : ⁅(alternatingGroup (Fin 6)).comap φ, (alternatingGroup (Fin 6)).comap φ⁆ =
    (alternatingGroup (Fin 6)).comap φ

variable {t : Y} {K : Subgroup Y} {φ : K →* Equiv.Perm (Fin 6)}

@[expose] def K0 (φ : K →* Equiv.Perm (Fin 6)) : Subgroup Y :=
  ((alternatingGroup (Fin 6)).comap φ).map K.subtype

@[expose] def Zk (φ : K →* Equiv.Perm (Fin 6)) : Subgroup Y := φ.ker.map K.subtype

theorem mem_K0 {y : Y} : y ∈ K0 φ ↔ ∃ k : K, φ k ∈ alternatingGroup (Fin 6) ∧ (k : Y) = y := by
  simp [K0, Subgroup.mem_map]

theorem mem_Zk {y : Y} : y ∈ Zk φ ↔ ∃ k : K, φ k = 1 ∧ (k : Y) = y := by
  simp [Zk, Subgroup.mem_map]

theorem K0_le_K : K0 φ ≤ K := by
  rintro _ hy
  obtain ⟨k, -, rfl⟩ := mem_K0.1 hy
  exact k.2

theorem Zk_le_K0 : Zk φ ≤ K0 φ := by
  rintro _ hy
  obtain ⟨k, hk, rfl⟩ := mem_Zk.1 hy
  exact mem_K0.2 ⟨k, by rw [hk]; exact one_mem _, rfl⟩

theorem Zk_le_K : Zk φ ≤ K := Zk_le_K0.trans K0_le_K

theorem K0_normal_K (φ : K →* Equiv.Perm (Fin 6)) : ∀ k ∈ K, ∀ g ∈ K0 φ, k * g * k⁻¹ ∈ K0 φ := by
  intro k hk g hg
  obtain ⟨k', hk', rfl⟩ := mem_K0.1 hg
  refine mem_K0.2 ⟨⟨k, hk⟩ * k' * ⟨k, hk⟩⁻¹, ?_, rfl⟩
  rw [map_mul, map_mul, map_inv]
  exact (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ hk' _

namespace CYHyp

variable (hY : CYHyp t K φ)
include hY

theorem card_K : Nat.card K = 2160 := by
  have h := Subgroup.card_ker_mul_card_range φ
  rw [MonoidHom.range_eq_top.2 hY.surj, Subgroup.card_top, hY.card_ker, Nat.card_perm,
    Nat.card_fin] at h
  rw [← h]
  decide

theorem card_Zk : Nat.card (Zk φ) = 3 := by
  rw [Zk, Subgroup.card_map_of_injective K.subtype_injective, hY.card_ker]

theorem card_K0 : Nat.card (K0 φ) = 1080 := by
  rw [K0, Subgroup.card_map_of_injective K.subtype_injective]
  have h1 := Subgroup.card_mul_index ((alternatingGroup (Fin 6)).comap φ)
  rw [Subgroup.index_comap_of_surjective _ hY.surj, alternatingGroup.index_eq_two, hY.card_K] at h1
  omega

@[expose] noncomputable def piK0 (φ : K →* Equiv.Perm (Fin 6)) :
    K0 φ →* alternatingGroup (Fin 6) where
  toFun g := ⟨φ ⟨g.1, K0_le_K g.2⟩, by
    obtain ⟨k, hk, hkg⟩ := mem_K0.1 g.2
    have : (⟨g.1, K0_le_K g.2⟩ : K) = k := Subtype.ext hkg.symm
    rw [this]
    exact hk⟩
  map_one' := Subtype.ext (map_one φ)
  map_mul' g h := Subtype.ext (map_mul φ ⟨g.1, K0_le_K g.2⟩ ⟨h.1, K0_le_K h.2⟩)

theorem quasi : QuasiData (K0 φ) (Zk φ) (piK0 φ) where
  perfect := by
    rw [K0, ← Subgroup.map_commutator, hY.perfect]
  Z_le := Zk_le_K0
  card_Z := hY.card_Zk
  surj := by
    intro a
    obtain ⟨k, hk⟩ := hY.surj (a : Equiv.Perm (Fin 6))
    refine ⟨⟨k, mem_K0.2 ⟨k, by rw [hk]; exact a.2, rfl⟩⟩, Subtype.ext hk⟩
  ker := by
    intro g
    constructor
    · intro h
      have h1 : φ ⟨g.1, K0_le_K g.2⟩ = 1 := congrArg Subtype.val h
      exact mem_Zk.2 ⟨⟨g.1, K0_le_K g.2⟩, h1, rfl⟩
    · intro h
      obtain ⟨k, hk, hkg⟩ := mem_Zk.1 h
      have : (⟨g.1, K0_le_K g.2⟩ : K) = k := Subtype.ext hkg.symm
      exact Subtype.ext (by show φ ⟨g.1, K0_le_K g.2⟩ = 1; rw [this]; exact hk)

theorem centralizer_K0 : ∀ k ∈ K, (∀ g ∈ K0 φ, k * g = g * k) → k ∈ Zk φ := by
  intro k hk hc
  refine mem_Zk.2 ⟨⟨k, hk⟩, perm6_cent _ fun a ha => ?_, rfl⟩
  obtain ⟨g, hg⟩ := (hY.quasi).surj ⟨a, ha⟩
  have h1 := hc g.1 g.2
  have h2 : φ ⟨k, hk⟩ * φ ⟨g.1, K0_le_K g.2⟩ = φ ⟨g.1, K0_le_K g.2⟩ * φ ⟨k, hk⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext h1)
  have h3 : φ ⟨g.1, K0_le_K g.2⟩ = a := congrArg Subtype.val hg
  rwa [h3] at h2

theorem eq_one_or_eq_t {x : Y} (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, hY.order, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · exact Or.inl (by rw [h, zpow_zero])
  · exact Or.inr (by rw [h, zpow_one])

theorem comm_zpowers : ∀ a ∈ K, ∀ b ∈ zpowers t, a * b = b * a := by
  intro a ha b hb
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
  exact (Commute.zpow_right (hY.comm a ha) n).eq

theorem K_inf_zpowers : ∀ x ∈ K, x ∈ zpowers t → x = 1 := by
  intro x hx hxt
  rcases hY.eq_one_or_eq_t hxt with h | h
  · exact h
  · exact absurd (h ▸ hx) hY.not_mem

theorem exists_decomp {γ : Y} (hγ : γ ∈ centralizer ({t} : Set Y)) :
    ∃ k ∈ K, γ = k ∨ γ = k * t := by
  rw [hY.cent, ← commProd_eq_sup hY.comm_zpowers] at hγ
  obtain ⟨k, hk, b, hb, rfl⟩ := mem_commProd.1 hγ
  rcases hY.eq_one_or_eq_t hb with h | h
  · exact ⟨k, hk, Or.inl (by rw [h, mul_one])⟩
  · exact ⟨k, hk, Or.inr (by rw [h])⟩

theorem card_Gam : Nat.card (centralizer ({t} : Set Y)) = 4320 := by
  rw [hY.cent, ← commProd_eq_sup hY.comm_zpowers, card_commProd hY.comm_zpowers hY.K_inf_zpowers,
    hY.card_K, Nat.card_zpowers, hY.order]

theorem K0_le_Gam : K0 φ ≤ centralizer ({t} : Set Y) := by
  intro g hg
  rw [mem_centralizer_singleton_iff]
  exact hY.comm g (K0_le_K hg)

theorem K0_normal_Gam : ∀ γ ∈ centralizer ({t} : Set Y), ∀ g ∈ K0 φ, γ * g * γ⁻¹ ∈ K0 φ := by
  intro γ hγ g hg
  obtain ⟨k, hk, h | h⟩ := hY.exists_decomp hγ
  · rw [h]
    exact K0_normal_K φ k hk g hg
  · have htg : t * g * t⁻¹ = g := by
      have := hY.comm g (K0_le_K hg)
      rw [← this]
      group
    have e : γ * g * γ⁻¹ = k * (t * g * t⁻¹) * k⁻¹ := by rw [h]; group
    rw [e, htg]
    exact K0_normal_K φ k hk g hg

@[expose] def Czt (t : Y) (φ : K →* Equiv.Perm (Fin 6)) : Subgroup Y := Zk φ ⊔ zpowers t

theorem comm_Zk_zpowers : ∀ a ∈ Zk φ, ∀ b ∈ zpowers t, a * b = b * a :=
  fun a ha => hY.comm_zpowers a (Zk_le_K ha)

theorem Czt_eq : Czt t φ = commProd (Zk φ) (zpowers t) hY.comm_Zk_zpowers :=
  (commProd_eq_sup hY.comm_Zk_zpowers).symm

theorem mem_Czt {x : Y} : x ∈ Czt t φ ↔ ∃ z0 ∈ Zk φ, x = z0 ∨ x = z0 * t := by
  rw [hY.Czt_eq, mem_commProd]
  constructor
  · rintro ⟨z0, hz0, b, hb, rfl⟩
    rcases hY.eq_one_or_eq_t hb with h | h
    · exact ⟨z0, hz0, Or.inl (by rw [h, mul_one])⟩
    · exact ⟨z0, hz0, Or.inr (by rw [h])⟩
  · rintro ⟨z0, hz0, h | h⟩
    · exact ⟨z0, hz0, 1, one_mem _, by rw [h, mul_one]⟩
    · exact ⟨z0, hz0, t, mem_zpowers t, h.symm⟩

theorem card_Czt : Nat.card (Czt t φ) = 6 := by
  rw [hY.Czt_eq, card_commProd hY.comm_Zk_zpowers (fun x hx hxt => hY.K_inf_zpowers x
    (Zk_le_K hx) hxt), hY.card_Zk, Nat.card_zpowers, hY.order]

theorem dichotomy_Gam {N : Subgroup Y} (hNG : N ≤ centralizer ({t} : Set Y))
    (hN : ∀ γ ∈ centralizer ({t} : Set Y), ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) :
    K0 φ ≤ N ∨ N ≤ Czt t φ := by
  by_cases hK : K0 φ ≤ N
  · exact Or.inl hK
  right
  have hNK : N ⊓ K0 φ ≤ Zk φ := by
    rcases hY.quasi.dichotomy (N := N ⊓ K0 φ) inf_le_right (fun g hg n hn =>
      ⟨hN g (hY.K0_le_Gam hg) n hn.1, (K0 φ).mul_mem ((K0 φ).mul_mem hg hn.2)
        ((K0 φ).inv_mem hg)⟩) with h | h
    · exact h
    · exact absurd (h ▸ inf_le_left) hK
  have hnc : ∀ n ∈ N, ∀ g ∈ K0 φ, n * g = g * n := by
    intro n hn
    have hθ : ∀ g ∈ K0 φ, n * g * n⁻¹ * g⁻¹ ∈ Zk φ := by
      intro g hg
      apply hNK
      refine ⟨?_, (K0 φ).mul_mem (hY.K0_normal_Gam n (hNG hn) g hg) ((K0 φ).inv_mem hg)⟩
      have h1 : g * n⁻¹ * g⁻¹ ∈ N := hN g (hY.K0_le_Gam hg) n⁻¹ (N.inv_mem hn)
      have := N.mul_mem hn h1
      simpa [mul_assoc] using this
    have hcomm : ∀ g ∈ K0 φ, ∀ h ∈ K0 φ, ⁅g, h⁆ * n = n * ⁅g, h⁆ := by
      intro g hg h hh
      have hzg := hθ g hg
      have hzh := hθ h hh
      have e1 : n * g * n⁻¹ = (n * g * n⁻¹ * g⁻¹) * g := by group
      have e2 : n * h * n⁻¹ = (n * h * n⁻¹ * h⁻¹) * h := by group
      have c1 : g * (n * g * n⁻¹ * g⁻¹) = (n * g * n⁻¹ * g⁻¹) * g :=
        hY.quasi.central g hg _ hzg
      have c2 : h * (n * h * n⁻¹ * h⁻¹) = (n * h * n⁻¹ * h⁻¹) * h :=
        hY.quasi.central h hh _ hzh
      have key : n * ⁅g, h⁆ * n⁻¹ = ⁅g, h⁆ := by
        have e3 : n * ⁅g, h⁆ * n⁻¹ = ⁅n * g * n⁻¹, n * h * n⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [e3, e1, e2, ← c1, ← c2]
        exact commutator_mul_central (a := g) (b := h)
          ((hY.quasi.central h hh _ hzg).symm)
          (hY.quasi.central _ (hY.quasi.Z_le hzg) _ hzh)
          ((hY.quasi.central g hg _ hzh).symm)
      calc ⁅g, h⁆ * n = n * ⁅g, h⁆ * n⁻¹ * n := by rw [key]
        _ = n * ⁅g, h⁆ := by group
    have hle : K0 φ ≤ centralizer ({n} : Set Y) := by
      rw [← hY.quasi.perfect]
      refine commutator_le.2 fun g hg h hh => ?_
      rw [mem_centralizer_singleton_iff]
      exact hcomm g hg h hh
    intro g hg
    have := hle hg
    rw [mem_centralizer_singleton_iff] at this
    exact this.symm
  intro n hn
  obtain ⟨k, hk, h | h⟩ := hY.exists_decomp (hNG hn)
  · have hkc : ∀ g ∈ K0 φ, k * g = g * k := fun g hg => by rw [← h]; exact hnc n hn g hg
    rw [hY.mem_Czt]
    exact ⟨k, hY.centralizer_K0 k hk hkc, Or.inl h⟩
  · have hkc : ∀ g ∈ K0 φ, k * g = g * k := by
      intro g hg
      have h1 := hnc n hn g hg
      rw [h] at h1
      have h2 : t * g = g * t := (hY.comm g (K0_le_K hg)).symm
      have h3 : k * g * t = g * k * t := by
        calc k * g * t = k * (g * t) := by group
          _ = k * (t * g) := by rw [← h2]
          _ = k * t * g := by group
          _ = g * (k * t) := h1
          _ = g * k * t := by group
      exact mul_right_cancel h3
    rw [hY.mem_Czt]
    exact ⟨k, hY.centralizer_K0 k hk hkc, Or.inr h⟩

theorem odd_le_Zk {N : Subgroup Y} (hNG : N ≤ centralizer ({t} : Set Y))
    (hN : ∀ γ ∈ centralizer ({t} : Set Y), ∀ n ∈ N, γ * n * γ⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : N ≤ Zk φ := by
  rcases hY.dichotomy_Gam hNG hN with h | h
  · exfalso
    have hd : 1080 ∣ Nat.card N := hY.card_K0 ▸ Subgroup.card_dvd_of_le h
    obtain ⟨m, hm⟩ := hodd
    omega
  · intro n hn
    obtain ⟨z0, hz0, h1 | h1⟩ := hY.mem_Czt.1 (h hn)
    · rw [h1]; exact hz0
    · exfalso
      have hd : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
      obtain ⟨m, hm⟩ := Odd.of_dvd_nat hodd hd
      have hcomm : Commute z0 t := hY.comm z0 (Zk_le_K hz0)
      have htt : t * t = 1 := by rw [← sq, ← hY.order, pow_orderOf_eq_one]
      have htm : t ^ (2 * m + 1) = t := by
        rw [pow_succ, pow_mul, sq, htt, one_pow, one_mul]
      have h2 : (z0 * t) ^ (2 * m + 1) = 1 := by
        rw [← h1, ← hm]
        exact pow_orderOf_eq_one n
      rw [hcomm.mul_pow, htm] at h2
      have : t = (z0 ^ (2 * m + 1))⁻¹ := eq_inv_of_mul_eq_one_right h2
      exact hY.not_mem (this ▸ K.inv_mem (K.pow_mem (Zk_le_K hz0) _))

end CYHyp

end CYHyp

end CFSG.EvenSporadicStandard.M24Std.DRes
