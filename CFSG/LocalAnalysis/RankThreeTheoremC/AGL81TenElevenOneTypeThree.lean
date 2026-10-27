module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneTypeThreeSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneTypeThreeGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

private theorem zpowers_inf_eq_bot {K : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) (hxK : x ∉ K) :
    (zpowers x ⊓ K : Subgroup G) = ⊥ := by
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 (fun h => hxK (h ▸ one_mem K))
  have hdvd : Nat.card (zpowers x ⊓ K : Subgroup G) ∣ 3 := by
    rw [← hxo, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · exfalso
    have heq : (zpowers x ⊓ K : Subgroup G) = zpowers x :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, Nat.card_zpowers, hxo])
    have hx' : x ∈ (zpowers x ⊓ K : Subgroup G) := by
      rw [heq]
      exact mem_zpowers x
    exact hxK hx'.2

theorem exists_commute_of_typeThree {L : Subgroup G} [L.Normal] {z x h f : G}
    (hz : orderOf z = 3) (hLC : L ⊓ centralizer (L : Set G) = zpowers z)
    (hx3 : x ^ 3 = 1) (hxLC : x ∉ L ⊔ centralizer (L : Set G))
    (hCLx : ∀ k ∈ L, k * x = x * k → IsPGroup 3 (zpowers k) → k ∈ zpowers z)
    (hhL : h ∈ L) (hh3 : h ^ 3 = 1) (hxh : ⁅x, h⁆ ∈ zpowers z) (hxh1 : ⁅x, h⁆ ≠ 1)
    (hf3 : f ^ 3 = 1) (hfLC : f ∉ L ⊔ centralizer (L : Set G))
    (hfx : ∃ ℓ ∈ L, ⁅ℓ⁻¹ * f, x⁆ ∈ centralizer (L : Set G))
    (hF1 : ∀ f₁ : G, IsPGroup 3 (zpowers f₁) → f₁ * f⁻¹ ∈ L →
      ⁅f₁, x⁆ ∈ centralizer (L : Set G) → f₁ ^ 3 ∈ centralizer (L : Set G) → False) :
    ∃ w : G, w * x = x * w ∧ w ^ 3 = 1 ∧ w ∉ zpowers x ⊔ zpowers z := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := centralizer (L : Set G) with hC
  have hZn : (zpowers z).Normal := by
    rw [← hLC]
    infer_instance
  have hzLC : z ∈ L ⊓ C := by
    rw [hLC]
    exact mem_zpowers z
  have hZL : zpowers z ≤ L := hLC ▸ inf_le_left
  have hZC : zpowers z ≤ C := hLC ▸ inf_le_right
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz3e : ∀ g : G, IsPGroup 3 (zpowers g) → g * z = z * g := fun g hg =>
    mul_comm_of_conj_mem_zpowers hz (hZn.conj_mem z (mem_zpowers z) g)
      (odd_orderOf_of_isPGroup_three hg)
  have hCz : ∀ q ∈ C, q * z = z * q := fun q hq => (mem_centralizer_iff.1 hq z hzLC.1).symm
  have hxp : IsPGroup 3 (zpowers x) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by simpa using hx3)
  have hxz : x * z = z * x := hz3e x hxp
  have hcommZ : ∀ {g u : G}, g * z = z * g → u ∈ zpowers z → Commute g u := by
    intro g u hg hu
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hu
    exact (show Commute g z from hg).zpow_right j
  by_contra hcon
  push Not at hcon
  have hxLC' := zpowers_inf_eq_bot hx3 hxLC
  have hK1 : ∀ w ∈ zpowers x ⊔ zpowers z, w ∈ L ⊔ C → w ∈ zpowers z := by
    intro w hw hwLC
    rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hw
    have haLC : a ∈ L ⊔ C := by
      have e : a = a * b * b⁻¹ := by group
      rw [e]
      exact mul_mem hwLC (inv_mem (mem_sup_left (hZL hb)))
    have ha1 : a ∈ (zpowers x ⊓ (L ⊔ C) : Subgroup G) := ⟨ha, haLC⟩
    rw [hxLC', mem_bot] at ha1
    rw [ha1, one_mul]
    exact hb
  have hI : ∀ c ∈ C, c ^ 3 = 1 → ⁅x, c⁆ ∈ zpowers z → c ∈ zpowers z := by
    intro c hcC hc3 hxc
    set d := ⁅x, h⁆ with hd
    have hd3 : d ^ 3 = 1 := pow_three_eq_one_of_mem_zpowers hz3 hxh
    have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hxh1
    have hZd : zpowers d = zpowers z :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hxh)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hz, hdo])
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hZd ▸ hxc : ⁅x, c⁆ ∈ zpowers d)
    have hxc' : x * c * x⁻¹ = d ^ k * c := by rw [hk, commutatorElement_def]; group
    have hxh' : x * h * x⁻¹ = d * h := by rw [hd, commutatorElement_def]; group
    have hhp : IsPGroup 3 (zpowers h) :=
      isPGroup_zpowers_of_pow_eq_one (n := 1) (by simpa using hh3)
    have hdh : Commute d h := (hcommZ (hz3e h hhp) hxh).symm
    have hdc : Commute d c := (hcommZ (hCz c hcC) hxh).symm
    have hch : Commute c h := (mem_centralizer_iff.1 hcC h hhL).symm
    set w := c * h ^ (-k) with hw
    have hxw : x * w * x⁻¹ = w := by
      calc x * w * x⁻¹ = (x * c * x⁻¹) * (x * h * x⁻¹) ^ (-k) := by rw [hw, conj_zpow]; group
        _ = d ^ k * c * (d * h) ^ (-k) := by rw [hxc', hxh']
        _ = c * d ^ k * (d ^ (-k) * h ^ (-k)) := by rw [hdh.mul_zpow, (hdc.zpow_left k).eq]
        _ = w := by rw [hw]; group
    have hwx : w * x = x * w := by
      rw [mul_inv_eq_iff_eq_mul] at hxw
      exact hxw.symm
    have hw3 : w ^ 3 = 1 := by
      rw [hw, (hch.zpow_right (-k)).mul_pow, hc3, one_mul, ← zpow_natCast, ← zpow_mul,
        mul_comm, zpow_mul, zpow_natCast, hh3, one_zpow]
    have hwZ := hK1 w (hcon w hwx hw3) (mul_mem (mem_sup_right hcC) (mem_sup_left
      (zpow_mem hhL _)))
    have hcL : c ∈ L := by
      have e : c = w * (h ^ (-k))⁻¹ := by rw [hw]; group
      rw [e]
      exact mul_mem (hZL hwZ) (inv_mem (zpow_mem hhL _))
    rw [← hLC]
    exact ⟨hcL, hcC⟩
  obtain ⟨ℓ, hℓL, hℓC⟩ := hfx
  set g := ℓ⁻¹ * f with hg
  set n := Nat.card G with hn
  set a := n.factorization 3 with ha
  set r := n / 3 ^ a with hr
  have hr3 : ¬ 3 ∣ r := Nat.not_dvd_ordCompl Nat.prime_three Nat.card_pos.ne'
  have hrr : r ^ 2 % 3 = 1 := by
    have : r % 3 = 1 ∨ r % 3 = 2 := by omega
    rcases this with h' | h' <;> simp [Nat.pow_mod, h']
  have hnr : 3 ^ a * r = n := Nat.ordProj_mul_ordCompl_eq_self n 3
  set f₁ := g ^ (r ^ 2) with hf₁
  have hf₁p : IsPGroup 3 (zpowers f₁) := by
    refine isPGroup_zpowers_of_pow_eq_one (n := a) ?_
    have e : r ^ 2 * 3 ^ a = n * r := by rw [← hnr]; ring
    rw [hf₁, ← pow_mul, e, pow_mul, hn, pow_card_eq_one', one_pow]
  let φ := QuotientGroup.mk' L
  have hφ : ∀ y : G, φ y = 1 ↔ y ∈ L := fun y => QuotientGroup.eq_one_iff y
  have hφg : φ g = φ f := by
    rw [hg, map_mul, map_inv, (hφ ℓ).2 hℓL, inv_one, one_mul]
  have hφf3 : φ f ^ 3 = 1 := by rw [← map_pow, hf3, map_one]
  have hφf₁ : φ f₁ = φ f := by
    rw [hf₁, map_pow, hφg, pow_eq_pow_mod _ hφf3, hrr, pow_one]
  have hf₁L : f₁ * f⁻¹ ∈ L := (hφ _).1 (by rw [map_mul, map_inv, hφf₁, mul_inv_cancel])
  let ψ := QuotientGroup.mk' C
  have hψ : ∀ y : G, ψ y = 1 ↔ y ∈ C := fun y => QuotientGroup.eq_one_iff y
  have hψgx : Commute (ψ g) (ψ x) := by
    show ψ g * ψ x = ψ x * ψ g
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    exact (hψ _).2 hℓC
  have hψf₁x : Commute (ψ f₁) (ψ x) := by
    rw [hf₁, map_pow]
    exact hψgx.pow_left _
  have hf₁x : ⁅f₁, x⁆ ∈ C := (hψ _).1 (by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hψf₁x.eq)
  set k₁ := f₁ ^ 3 with hk₁
  have hk₁L : k₁ ∈ L := (hφ _).1 (by rw [hk₁, map_pow, hφf₁, hφf3])
  have hk₁C : k₁ ∉ C := fun hc => hF1 f₁ hf₁p hf₁L hf₁x hc
  have hk₁p : IsPGroup 3 (zpowers k₁) := hf₁p.to_le (zpowers_le.2 (pow_mem (mem_zpowers f₁) 3))
  set d₁ := ⁅x, k₁⁆ with hd₁
  have hd₁L : d₁ ∈ L := by
    rw [hd₁, commutatorElement_def]
    exact mul_mem (‹L.Normal›.conj_mem k₁ hk₁L x) (inv_mem hk₁L)
  have hd₁C : d₁ ∈ C := (hψ _).1 (by
    rw [hd₁, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hk₁, map_pow]
    exact (hψf₁x.pow_left 3).eq.symm)
  have hd₁Z : d₁ ∈ zpowers z := by
    rw [← hLC]
    exact ⟨hd₁L, hd₁C⟩
  have hd₁1 : d₁ ≠ 1 := fun h1 => hk₁C (hZC (hCLx k₁ hk₁L
    (commutatorElement_eq_one_iff_mul_comm.1 h1).symm hk₁p))
  obtain ⟨f₂, hf₂f₁, hf₂p, hf₂x⟩ :=
    exists_mul_inv_mem_commute_pow_three hz (hZC (mem_zpowers z)) hCz hz3e hx3 hI hf₁p hf₁x
  set c'' := k₁⁻¹ * f₂ ^ 3 with hc''
  have hψf₂ : ψ f₂ = ψ f₁ := by
    have := (hψ _).2 hf₂f₁
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    exact this
  have hc''C : c'' ∈ C := (hψ _).1 (by
    rw [hc'', map_mul, map_inv, map_pow ψ f₂ 3, hψf₂, hk₁, map_pow ψ f₁ 3, inv_mul_cancel])
  have hf₂3 : f₂ ^ 3 = k₁ * c'' := by rw [hc'']; group
  have hk₁c : Commute k₁ c'' := (mem_centralizer_iff.1 hc''C k₁ hk₁L)
  have hc''p : IsPGroup 3 (zpowers c'') := by
    obtain ⟨m, hm⟩ := hk₁p ⟨k₁, mem_zpowers _⟩
    obtain ⟨m', hm'⟩ := hf₂p ⟨f₂ ^ 3, pow_mem (mem_zpowers _) 3⟩
    have hm1 : k₁ ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hm2 : (f₂ ^ 3) ^ 3 ^ m' = 1 := by simpa using congrArg Subtype.val hm'
    have hcomm : Commute k₁⁻¹ (f₂ ^ 3) := by
      rw [hf₂3]
      exact ((Commute.refl k₁).mul_right hk₁c).inv_left
    refine isPGroup_zpowers_of_pow_eq_one (n := m + m') ?_
    rw [hc'', hcomm.mul_pow, pow_add, inv_pow, pow_mul, hm1, one_pow, inv_one, one_mul,
      mul_comm, pow_mul, hm2, one_pow]
  have hxk : x * k₁ * x⁻¹ = d₁ * k₁ := by rw [hd₁, commutatorElement_def]; group
  have hxf : x * f₂ ^ 3 * x⁻¹ = f₂ ^ 3 := by rw [← hf₂x, mul_inv_cancel_right]
  have hdk : Commute d₁ k₁ := (hcommZ (hz3e k₁ hk₁p) hd₁Z).symm
  have hxc'' : ⁅x, c''⁆ = d₁⁻¹ := by
    calc ⁅x, c''⁆ = (x * k₁ * x⁻¹)⁻¹ * (x * f₂ ^ 3 * x⁻¹) * c''⁻¹ := by
          rw [hc'', commutatorElement_def]; group
      _ = (d₁ * k₁)⁻¹ * f₂ ^ 3 * (k₁⁻¹ * f₂ ^ 3)⁻¹ := by rw [hxk, hxf]
      _ = k₁⁻¹ * d₁⁻¹ * k₁ := by group
      _ = d₁⁻¹ := by rw [(hdk.inv_inv).eq.symm]; group
  have hxc''Z : ⁅x, c''⁆ ∈ zpowers z := hxc'' ▸ inv_mem hd₁Z
  have hxc''1 : ⁅x, c''⁆ ≠ 1 := by rw [hxc'']; exact inv_ne_one.2 hd₁1
  have hQ := isSylowOf_zpowers_of_commutator hz (hZC (mem_zpowers z)) hCz hxz hx3 hI hc''C
    hc''p hxc''Z hxc''1
  have hNn : (C.map φ).Normal :=
    Subgroup.Normal.map inferInstance φ (QuotientGroup.mk'_surjective L)
  have hφf₂3 : φ f₂ ^ 3 = φ c'' := by
    rw [← map_pow, hf₂3, map_mul, (hφ k₁).2 hk₁L, one_mul]
  refine false_of_isSylowOf_zpowers_pow_three (N := C.map φ) (f := φ f) (w := φ f₂) hφf3 ?_ ?_
    ?_ ?_ ?_
  · intro hm
    have hm' : f ∈ (C.map φ).comap φ := hm
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hm'
    exact hfLC (by rwa [sup_comm] at hm')
  · have e : φ f₂ * (φ f)⁻¹ = φ (f₂ * f₁⁻¹) := by rw [map_mul, map_inv, hφf₁]
    rw [e]
    exact mem_map_of_mem φ hf₂f₁
  · rw [← MonoidHom.map_zpowers]
    exact hf₂p.map φ
  · rw [hφf₂3, ← MonoidHom.map_zpowers]
    obtain ⟨Q, hQ'⟩ := hQ
    rw [← hQ']
    refine ⟨Q.mapSurjective (φ.subgroupMap_surjective C), ?_⟩
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
    rfl
  · rw [hφf₂3]
    intro h1
    have hc''L : c'' ∈ L := (hφ _).1 h1
    have hc''Z : c'' ∈ zpowers z := by
      rw [← hLC]
      exact ⟨hc''L, hc''C⟩
    exact hxc''1 (commutatorElement_eq_one_iff_mul_comm.2 (hcommZ hxz hc''Z).eq)

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27
