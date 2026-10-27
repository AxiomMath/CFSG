module

public import CFSG.GH74.Uniqueness.SU.KI6BLocal

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG CFSG.Blueprint CFSG.ProperTwoGeneratedCore CFSG.GH74.Uniqueness.SU.K.R3
open scoped Pointwise commutatorElement
open CFSG.LocalCores

variable {H : Type} [Group H] [Finite H] {T : Sylow 2 H} {H₀ : Subgroup H}

omit [Finite H] in
theorem mem_normalizer_of_map_eq {K : Subgroup H} {u : H}
    (h : K.map (MulAut.conj u).toMonoidHom = K) : u ∈ normalizer (K : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, by simp⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : u * y * u⁻¹ = u * x * u⁻¹ := by simpa using hyx
      simpa using h1
    rw [← this]; exact hy

theorem Cfg.mem_normalizer_of_mem_T (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K : Subgroup H} (hK : IsComponent K) (hKH : ¬ K ≤ H₀) {u : H}
    (huT : u ∈ (T : Subgroup H)) (hu2 : u * u = 1) : u ∈ normalizer (K : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  set K' : Subgroup H := K.map (MulAut.conj u).toMonoidHom with hK'def
  have hK' : IsComponent K' := isComponent_map_mulEquiv (MulAut.conj u) hK
  have hne : K ≠ K' := fun heq => hnot (mem_normalizer_of_map_eq heq.symm)
  have hdata := component_data F h htc ht2 hK (hr K hK)
  have hu1 : u ≠ 1 := by
    intro h1; apply hnot; rw [h1]; exact (normalizer (K : Set H)).one_mem
  have hut : u ≠ t := fun h1 =>
    hnot (by rw [h1]; exact Subgroup.center_le_normalizer (K : Set H) htc)
  have hu2' : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have huH : u ∈ H₀ := h.sylow_le huT
  have hC := h.centralizer_le_of_involution htc ht2 huH hu2' hut
  obtain ⟨y, hyK, hyT, hy4⟩ := exists_orderFour_mem F h htc ht2 hK (hr K hK)
  have hyH : y ∈ H₀ := h.sylow_le hyT
  have hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := components_commute hK hK' hne
  have hconj : ∀ k ∈ K, k * y * k⁻¹ ∈ H₀ := by
    intro k hk
    have hc : u * k * u⁻¹ ∈ K' := ⟨k, hk, by simp⟩
    set c := u * k * u⁻¹ with hcdef
    have hxk : k * c ∈ centralizer ({u} : Set H) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have huc : u * c * u⁻¹ = k := by
        have : u * (u * k * u⁻¹) * u⁻¹ = (u * u) * k * (u * u)⁻¹ := by group
        rw [hcdef, this, hu2]; simp
      have h1 : u * (k * c) * u⁻¹ = k * c := by
        calc u * (k * c) * u⁻¹ = (u * k * u⁻¹) * (u * c * u⁻¹) := by group
          _ = c * k := by rw [huc]
          _ = k * c := (hcomm k hk c hc).symm
      refine Eq.symm ?_
      calc u * (k * c) = (u * (k * c) * u⁻¹) * u := by group
        _ = (k * c) * u := by rw [h1]
    have hxkH : k * c ∈ H₀ := hC hxk
    have hmem := H₀.mul_mem (H₀.mul_mem hxkH hyH) (H₀.inv_mem hxkH)
    have h3 : k * c * y * (k * c)⁻¹ = k * y * k⁻¹ := by
      have hcy : y * c = c * y := hcomm y hyK c hc
      calc k * c * y * (k * c)⁻¹ = k * (c * y) * c⁻¹ * k⁻¹ := by group
        _ = k * (y * c) * c⁻¹ * k⁻¹ := by rw [hcy]
        _ = k * y * k⁻¹ := by group
    have h4 : k * c * y * (k * c)⁻¹ ∈ H₀ := by simpa [mul_assoc] using hmem
    rwa [h3] at h4
  have hyc : ∃ k ∈ K, k * y ≠ y * k := by
    by_contra hall
    push Not at hall
    exact not_mem_zpowers_of_orderOf_four ht2 hy4
      (hdata.2.2.1 y hyK (fun k hk => (hall k hk).symm))
  exact hKH (quasisimple_le_of_conj_mem K H₀ hK.1 y hyK hyc hconj)


omit [Finite H] in
@[expose] def conjOn (K : Subgroup H) (u : H) (hu : u ∈ normalizer (K : Set H)) : MulAut ↥K where
  toFun x := ⟨u * x * u⁻¹, ((Subgroup.mem_normalizer_iff.mp hu) x).mp x.2⟩
  invFun x := ⟨u⁻¹ * x * u, by
    have h := (Subgroup.mem_normalizer_iff.mp hu) (u⁻¹ * x * u)
    have h2 : u * (u⁻¹ * (x : H) * u) * u⁻¹ = x := by group
    rw [h2] at h
    exact h.mpr x.2⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

omit [Finite H] in
theorem conjOn_apply (K : Subgroup H) (u : H) (hu : u ∈ normalizer (K : Set H)) (x : ↥K) :
    ((conjOn K u hu x : ↥K) : H) = u * x * u⁻¹ := rfl

omit [Finite H] in
theorem mem_normalizer_zpowers_sup {u t x : H} (htc : t ∈ center H)
    (hx : x * u * x⁻¹ ∈ zpowers u ⊔ zpowers t) (hx' : x⁻¹ * u * x ∈ zpowers u ⊔ zpowers t) :
    x ∈ normalizer ((zpowers u ⊔ zpowers t : Subgroup H) : Set H) := by
  have hcommut : ∀ a ∈ zpowers u, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute u t from (Subgroup.mem_center_iff.mp htc u)) m n).eq
  have key : ∀ x : H, x * u * x⁻¹ ∈ zpowers u ⊔ zpowers t →
      ∀ g ∈ zpowers u ⊔ zpowers t, x * g * x⁻¹ ∈ zpowers u ⊔ zpowers t := by
    intro x hx g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := SU1.mem_sup_of_commute hcommut hg
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hbc : x * t ^ n = t ^ n * x :=
      (Commute.zpow_right (show Commute x t from (Subgroup.mem_center_iff.mp htc x)) n).eq
    have h2 : x * t ^ n * x⁻¹ = t ^ n := by rw [hbc]; group
    have h1 : x * (u ^ m * t ^ n) * x⁻¹ = (x * u * x⁻¹) ^ m * t ^ n := by
      calc x * (u ^ m * t ^ n) * x⁻¹ = (x * u ^ m * x⁻¹) * (x * t ^ n * x⁻¹) := by group
        _ = (x * u * x⁻¹) ^ m * t ^ n := by rw [h2, conj_zpow]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hx m)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) n))
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact key x hx g
  · intro hg
    have h3 := key x⁻¹ (by simpa using hx') _ hg
    have h4 : x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g := by group
    rwa [h4] at h3


theorem Cfg.exists_inner (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K : Subgroup H} (hK : IsComponent K) (hKH : ¬ K ≤ H₀) {u : H}
    (huT : u ∈ (T : Subgroup H)) (hu2 : u * u = 1) :
    ∃ k ∈ K, u * k⁻¹ ∈ centralizer (K : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  have hun := h.mem_normalizer_of_mem_T F hr htc ht2 hK hKH huT hu2
  have hdata := component_data F h htc ht2 hK (hr K hK)
  obtain ⟨S, hS⟩ := exists_sylow_component T hK
  have hrk : CFSG.pRank 2 ↥K ≤ 1 := (pRank_coe_eq K).trans_le (hr K hK)
  have hZ := h.isPGroup_center_component hK
  obtain ⟨h5, -⟩ := component_sl25 F h hr htc ht2 hK hKH
  have hu1 : u ≠ 1 := by
    intro h1
    apply hno 1 K.one_mem
    rw [h1]; simp
  have hut : u ≠ t := by
    intro h1
    apply hno 1 K.one_mem
    rw [h1]
    simp only [inv_one, mul_one]
    exact Subgroup.mem_centralizer_iff.mpr (fun g _ => Subgroup.mem_center_iff.mp htc g)
  have hu2' : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have huH : u ∈ H₀ := h.sylow_le huT
  let β : MulAut ↥K := conjOn K u hun
  have hββ : β * β = 1 := by
    ext x
    show ((conjOn K u hun (conjOn K u hun x) : ↥K) : H) = x
    rw [conjOn_apply, conjOn_apply]
    calc u * (u * (x : H) * u⁻¹) * u⁻¹ = (u * u) * (x : H) * (u * u)⁻¹ := by group
      _ = x := by rw [hu2]; simp
  have hout : ∀ k : ↥K, ∃ x : ↥K, β x ≠ k * x * k⁻¹ := by
    intro k
    by_contra hall
    push Not at hall
    apply hno (k : H) k.2
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hall ⟨(k : H)⁻¹ * x * k, K.mul_mem (K.mul_mem (K.inv_mem k.2) hx) k.2⟩
    have h2 : u * ((k : H)⁻¹ * x * k) * u⁻¹ = (k : H) * ((k : H)⁻¹ * x * k) * (k : H)⁻¹ := by
      have := congrArg Subtype.val h1
      simpa [β, conjOn_apply] using this
    have h3 : u * ((k : H)⁻¹ * x * k) * u⁻¹ = x := by rw [h2]; group
    have h4 : u * ((k : H)⁻¹ * x * k) = x * u := by
      calc u * ((k : H)⁻¹ * x * k) = (u * ((k : H)⁻¹ * x * k) * u⁻¹) * u := by group
        _ = x * u := by rw [h3]
    calc x * (u * (k : H)⁻¹) = (x * u) * (k : H)⁻¹ := by group
      _ = (u * ((k : H)⁻¹ * x * k)) * (k : H)⁻¹ := by rw [h4]
      _ = u * (k : H)⁻¹ * x := by group
  have hND : normalizer ((S : Subgroup ↥K) : Set ↥K) ≤ H₀.subgroupOf K := by
    intro k hk
    apply Subgroup.mem_subgroupOf.mpr
    obtain ⟨y, hyK, hyT, hy4⟩ := exists_orderFour_mem F h htc ht2 hK (hr K hK)
    let W : Subgroup H := (S : Subgroup ↥K).map K.subtype
    have hWT : W ≤ (T : Subgroup H) := by
      rintro _ ⟨w, hw, rfl⟩
      exact (hS w).mp hw
    have hWK : W ≤ K := by
      rintro _ ⟨w, hw, rfl⟩
      exact w.2
    have hyW : y ∈ W := ⟨⟨y, hyK⟩, (hS ⟨y, hyK⟩).mpr hyT, rfl⟩
    exact normalizer_le_H₀ F h hr htc ht2 hK hWT hWK ⟨y, hyW, hy4⟩ k.2
      (coe_mem_normalizer_map (S : Subgroup ↥K) hk)
  have hCD : ∀ x : ↥K, β x * x⁻¹ ∈ center ↥K → x ∈ H₀.subgroupOf K := by
    intro x hx
    apply Subgroup.mem_subgroupOf.mpr
    have hz : u * (x : H) * u⁻¹ * (x : H)⁻¹ ∈ zpowers t := by
      have hzK : (((β x * x⁻¹ : ↥K)) : H) ∈ K := (β x * x⁻¹ : ↥K).2
      have := hdata.2.2.1 (((β x * x⁻¹ : ↥K)) : H) hzK (fun k hk => by
        have := Subgroup.mem_center_iff.mp hx ⟨k, hk⟩
        exact (congrArg Subtype.val this).symm)
      simpa [β, conjOn_apply] using this
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp hz
    set c : H := u * (x : H) * u⁻¹ * (x : H)⁻¹ with hc
    have hcV : c ∈ zpowers u ⊔ zpowers t := Subgroup.mem_sup_right hz
    have huV : u ∈ zpowers u ⊔ zpowers t := Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
    have hx1 : (x : H) * u * (x : H)⁻¹ ∈ zpowers u ⊔ zpowers t := by
      have : (x : H) * u * (x : H)⁻¹ = c⁻¹ * u := by rw [hc]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcV) huV
    have hxc : (x : H) * c = c * (x : H) := by
      rw [← he]
      exact (Commute.zpow_right (show Commute (x : H) t from
        (Subgroup.mem_center_iff.mp htc x)) e).eq
    have hx2 : (x : H)⁻¹ * u * (x : H) ∈ zpowers u ⊔ zpowers t := by
      have h1 : (x : H)⁻¹ * u * (x : H) = c * u := by
        have h2 : u * (x : H) = c * (x : H) * u := by rw [hc]; group
        calc (x : H)⁻¹ * u * (x : H) = (x : H)⁻¹ * (u * (x : H)) := by group
          _ = (x : H)⁻¹ * (c * (x : H) * u) := by rw [h2]
          _ = (x : H)⁻¹ * (x * c) * u := by rw [← hxc]; group
          _ = c * u := by group
      rw [h1]
      exact Subgroup.mul_mem _ hcV huV
    have hnorm := mem_normalizer_zpowers_sup htc hx1 hx2
    have hVH : zpowers u ⊔ zpowers t ≤ H₀ :=
      sup_le (Subgroup.zpowers_le.mpr huH) (Subgroup.zpowers_le.mpr (h.center_le htc))
    have hrank : 2 ≤ Open.pRank 2 (zpowers u ⊔ zpowers t) :=
      two_le_pRank_of_commuting_involutions hu2' ht2 hut (Subgroup.mem_center_iff.mp htc u)
        huV (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    exact two_generated_core_subgroup_normalizer_le T H₀ h.sylow_le h.gamma _ hVH hrank hnorm
  have hgen := F.generation ↥K hK.1 hrk hZ h5 S β hββ hout (H₀.subgroupOf K) hND hCD
  apply hKH
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥K) ∈ H₀.subgroupOf K := by rw [hgen]; trivial
  exact Subgroup.mem_subgroupOf.mp hmem

end CFSG.GH74.Uniqueness.SU.K.R6
