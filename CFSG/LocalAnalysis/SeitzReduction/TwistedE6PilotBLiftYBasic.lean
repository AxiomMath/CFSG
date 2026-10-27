module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionRouteBAut

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Quasithin (perfectCore perfectCore_le)

section Step7

variable {G : Type*} [Group G]

theorem exists_coords_eq_map_of_le_conj {C' : Type*} [Group C'] {φ' : C' →* G}
    (hφ' : Function.Injective φ') {J' : Subgroup C'} {X : Subgroup G} {q₀ : G}
    (hq₀ : q₀ ∈ φ'.range) (hX : X ≤ (J'.map φ').map (MulAut.conj q₀).toMonoidHom)
    {W : Subgroup C'}
    (h7 : ∀ X'' : Subgroup C', X'' ≤ J' → Nat.card X'' = Nat.card X →
      ∃ c : C', X'' = W.map (MulAut.conj c).toMonoidHom) :
    ∃ φ'' : C' →* G, Function.Injective φ'' ∧ φ''.range = φ'.range ∧ X = W.map φ'' := by
  set X'' : Subgroup C' := (X.map (MulAut.conj q₀⁻¹).toMonoidHom).comap φ' with hX''def
  have hmemX : ∀ x ∈ X, ∃ j ∈ J', φ' j = q₀⁻¹ * x * q₀ := by
    intro x hx
    obtain ⟨_, ⟨j, hj, rfl⟩, hjx⟩ := hX hx
    refine ⟨j, hj, ?_⟩
    rw [← hjx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hconjmem : ∀ x ∈ X, q₀⁻¹ * x * q₀ ∈ X.map (MulAut.conj q₀⁻¹).toMonoidHom := by
    intro x hx
    exact ⟨x, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hmapX : X''.map φ' = X.map (MulAut.conj q₀⁻¹).toMonoidHom := by
    refine le_antisymm (Subgroup.map_comap_le _ _) ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, -, hj⟩ := hmemX x hx
    refine ⟨j, ?_, ?_⟩
    · show φ' j ∈ X.map (MulAut.conj q₀⁻¹).toMonoidHom
      rw [hj]
      exact hconjmem x hx
    · rw [hj]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hX''J : X'' ≤ J' := by
    intro c hc
    have hc' : φ' c ∈ X.map (MulAut.conj q₀⁻¹).toMonoidHom := hc
    obtain ⟨x, hx, hxc⟩ := hc'
    obtain ⟨j, hj, hjx⟩ := hmemX x hx
    have : φ' j = φ' c := by
      rw [hjx, ← hxc]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hφ' this]
    exact hj
  have hcard : Nat.card X'' = Nat.card X := by
    rw [← card_map_of_injective hφ', hmapX, card_map_of_injective (MulAut.conj q₀⁻¹).injective]
  obtain ⟨c, hc⟩ := h7 X'' hX''J hcard
  obtain ⟨n, rfl⟩ := hq₀
  refine ⟨φ'.comp (MulAut.conj (n * c)).toMonoidHom, hφ'.comp (MulAut.conj (n * c)).injective,
    ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj (n * c)).surjective,
      ← MonoidHom.range_eq_map]
  ·
    have hφconj : ∀ a b : C', φ' (a * b * a⁻¹) = φ' a * φ' b * (φ' a)⁻¹ := fun a b => by
      rw [map_mul, map_mul, map_inv]
    ext x
    constructor
    · intro hx
      have h1 : (φ' n)⁻¹ * x * φ' n ∈ X''.map φ' := by
        rw [hmapX]
        exact hconjmem x hx
      obtain ⟨j, hj, hjx⟩ := h1
      rw [hc] at hj
      obtain ⟨w, hw, rfl⟩ := hj
      refine ⟨w, hw, ?_⟩
      have e1 : x = φ' n * ((φ' n)⁻¹ * x * φ' n) * (φ' n)⁻¹ := by group
      rw [e1, ← hjx]
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply]
      rw [← hφconj]
      congr 1
      group
    · rintro ⟨w, hw, rfl⟩
      have hj : c * w * c⁻¹ ∈ X'' := by
        rw [hc]
        exact ⟨w, hw, rfl⟩
      have h1 : φ' (c * w * c⁻¹) ∈ X.map (MulAut.conj (φ' n)⁻¹).toMonoidHom := by
        rw [← hmapX]
        exact ⟨_, hj, rfl⟩
      obtain ⟨x, hx, hxe⟩ := h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hxe
      have e2 : (φ'.comp (MulAut.conj (n * c)).toMonoidHom) w =
          φ' n * φ' (c * w * c⁻¹) * (φ' n)⁻¹ := by
        simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
          MulAut.conj_apply]
        rw [← hφconj]
        congr 1
        group
      rw [e2, ← hxe]
      have e3 : φ' n * ((φ' n)⁻¹ * x * φ' n) * (φ' n)⁻¹ = x := by group
      rw [e3]
      exact hx

end Step7

section RouteB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_coords_eq_map_of_inner_of_classes (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {κ : Type*} (rep : κ → C) {k : κ} {g : G}
    (hg : g⁻¹ * t * g = (e.symm (rep k) : G) ∨ g⁻¹ * t * g = t * (e.symm (rep k) : G))
    (hne : g⁻¹ * t * g ≠ t)
    (hinner : ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g,
      t * l * t⁻¹ = w' * l * w'⁻¹)
    (Q M : κ → Subgroup C)
    (hF3 : ∀ k, perfectCore (centralizer ({rep k} : Set C)) = Q k ⊔ M k)
    (hQ : ∀ k, IsPGroup 2 (Q k)) (hMN : ∀ k, M k ≤ normalizer (Q k : Set C))
    (hQM : ∀ k, Disjoint (Q k) (M k))
    (hM : ∀ k, ∀ N : Subgroup (M k), N.Normal → IsPGroup 2 N → N = ⊥)
    (hF1 : ∀ x : C, orderOf x = 2 →
      Nonempty (perfectCore (centralizer ({x} : Set C)) ≃* (Q k ⊔ M k : Subgroup C)) →
      ∃ (k' : κ) (c : C), c * x * c⁻¹ = rep k')
    {J : Subgroup C} (hJ : ∀ k, J ≤ M k) {W : Subgroup C}
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (J.map e.symm.toMonoidHom).map L.subtype)
    (hF7 : ∀ (k' : κ) (ι : M k ≃* M k') (X'' : Subgroup C),
      X'' ≤ ((J.subgroupOf (M k)).map ι.toMonoidHom).map (M k').subtype →
      Nat.card X'' = Nat.card X → ∃ c : C, X'' = W.map (MulAut.conj c).toMonoidHom) :
    ∃ φ'' : C →* G, Function.Injective φ'' ∧ φ''.range = CFSG.conjugate L g ∧
      X = W.map φ'' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htC := EPilot.mem_centralizer_of_inf_centralizer_eq_zpowers hKt
  set φ : C →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := EPilot.range_subtype_comp_mulEquiv_symm e
  have hg' : g⁻¹ * t * g = φ (rep k) ∨ g⁻¹ * t * g = t * φ (rep k) := hg
  obtain ⟨w', hw'L, hact⟩ := hinner
  have hw'2 : orderOf w' = 2 :=
    EPilot.orderOf_eq_two_of_inner ht hKt (e.symm (rep k)).2 hg hne hw'L hact
  obtain ⟨x', hx'⟩ := EPilot.exists_eq_conj_of_mem_conjugate e hw'L
  have hx'2 : orderOf x' = 2 := by rw [← EPilot.orderOf_conj_symm e g x', hx', hw'2]
  obtain ⟨φ'₀, hφ'₀, hφ'₀r, hφ'₀x⟩ :=
    EPilot.exists_coords_conjugate e g (x' := x') (c' := 1) (by rw [one_mul, inv_one, mul_one])
  rw [hx'] at hφ'₀x
  have hΛ₀ := EPilot.map_perfectCore_centralizer_eq_of_inner hset hOut htC ht hφ hφr hφ'₀ hφ'₀r
    hg' (by rw [hφ'₀x]; exact hact)
  rw [hF3 k] at hΛ₀
  have hiso : Nonempty (perfectCore (centralizer ({x'} : Set C)) ≃* (Q k ⊔ M k : Subgroup C)) :=
    ⟨((perfectCore (centralizer ({x'} : Set C))).equivMapOfInjective φ'₀ hφ'₀).trans
      ((MulEquiv.subgroupCongr hΛ₀.symm).trans
        ((Q k ⊔ M k).equivMapOfInjective φ hφ).symm)⟩
  obtain ⟨k', c', hc'⟩ := hF1 x' hx'2 hiso
  obtain ⟨φ', hφ', hφ'r, hφ'rep⟩ := EPilot.exists_coords_conjugate e g hc'
  rw [hx'] at hφ'rep
  have hΛ := EPilot.map_perfectCore_centralizer_eq_of_inner hset hOut htC ht hφ hφr hφ' hφ'r
    hg' (by rw [hφ'rep]; exact hact)
  rw [hF3 k, hF3 k'] at hΛ
  have hXJ' : X ≤ J.map φ := by
    rw [hφdef, ← Subgroup.map_map]
    exact hXJ
  have hX2 : ¬ 2 ∣ Nat.card X := fun h => (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h)
  obtain ⟨hQeq, ι, -, q₀, hq₀, hXq⟩ := EPilot.exists_conj_le_map_of_two_decompositions hφ hφ'
    (hQ k) (hQ k') (hM k) (hM k') (hMN k) (hMN k') (hQM k) (hQM k') hΛ (hJ k) hXJ' hX2
  have hq₀' : q₀ ∈ φ'.range := by
    rw [hQeq] at hq₀
    obtain ⟨n, -, rfl⟩ := hq₀
    exact ⟨n, rfl⟩
  obtain ⟨φ'', hφ'', hφ''r, hXW⟩ := exists_coords_eq_map_of_le_conj hφ' hq₀' hXq (hF7 k' ι)
  exact ⟨φ'', hφ'', hφ''r.trans hφ'r, hXW⟩

end RouteB

section Layer

variable {G : Type*} [Group G]

theorem map_symm_ofInjective_map_subtype {C : Type*} [Group C] {φ : C →* G}
    (hφ : Function.Injective φ) {L' : Subgroup G} (hφL : φ.range = L') (H : Subgroup C) :
    (H.map ((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hφL)).symm.symm.toMonoidHom).map
      L'.subtype = H.map φ := by
  rw [Subgroup.map_map]
  rfl

theorem inSubgroup_layer_inf_centralizer_map_eq {C : Type*} [Group C] {φ : C →* G}
    (hφ : Function.Injective φ) {L' : Subgroup G} (hφL : φ.range = L') {W Y D : Subgroup C}
    (hW : centralizer (W : Set C) = Y ⊔ D) (hYD : Y ≤ centralizer (D : Set C))
    (hY : Y ≤ centralizer (Y : Set C)) (hD : CFSG.IsQuasisimple D) :
    inSubgroup layer (L' ⊓ centralizer ((W.map φ : Subgroup G) : Set G)) = D.map φ := by
  rw [← map_symm_ofInjective_map_subtype hφ hφL W, ← map_symm_ofInjective_map_subtype hφ hφL D]
  exact F4Pilot.inSubgroup_layer_inf_centralizer_map_symm _ hW hYD hY hD

theorem mem_of_mem_sup_of_odd_of_pow_two_pow {D Y : Subgroup G} (hYD : Y ≤ centralizer (D : Set G))
    (hY : Odd (Nat.card Y)) {x : G} (hx : x ∈ Y ⊔ D) {n : ℕ} (hxn : x ^ 2 ^ n = 1) : x ∈ D := by
  have hYN : Y ≤ normalizer (D : Set G) := hYD.trans (Subgroup.centralizer_le_normalizer _)
  have hx' : x ∈ ((Y ⊔ D : Subgroup G) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right _ _ hYN] at hx'
  obtain ⟨y, hy, d, hd, rfl⟩ := Set.mem_mul.1 hx'
  have hc : Commute y d := (mem_centralizer_iff.1 (hYD hy) d hd).symm
  have hpow : (y * d) ^ Nat.card Y = d ^ Nat.card Y := by
    rw [hc.mul_pow, orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard Y hy), one_mul]
  have hcop : Nat.Coprime (Nat.card Y) (orderOf (y * d)) := by
    have hdvd : orderOf (y * d) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hxn
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hi]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hY)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm, hpow, ← pow_mul]
  exact pow_mem hd _

theorem mem_layer_of_coords {C : Type*} [Group C] {φ : C →* G} (hφ : Function.Injective φ)
    {L' : Subgroup G} (hφL : φ.range = L') {W Y D : Subgroup C}
    (hW : centralizer (W : Set C) = Y ⊔ D) (hYD : Y ≤ centralizer (D : Set C))
    (hY : Y ≤ centralizer (Y : Set C)) (hYodd : Odd (Nat.card Y)) (hD : CFSG.IsQuasisimple D)
    {z : G} (hzL : z ∈ L') (hzW : z ∈ centralizer ((W.map φ : Subgroup G) : Set G)) {n : ℕ}
    (hzn : z ^ 2 ^ n = 1) :
    z ∈ inSubgroup layer (L' ⊓ centralizer ((W.map φ : Subgroup G) : Set G)) := by
  rw [inSubgroup_layer_inf_centralizer_map_eq hφ hφL hW hYD hY hD]
  rw [← hφL] at hzL
  obtain ⟨c, rfl⟩ := hzL
  have hcW : c ∈ centralizer (W : Set C) := by
    rw [mem_centralizer_iff]
    intro w hw
    apply hφ
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.1 hzW (φ w) ⟨w, hw, rfl⟩
  rw [hW] at hcW
  have hcn : c ^ 2 ^ n = 1 := hφ (by rw [map_pow, hzn, map_one])
  exact ⟨c, mem_of_mem_sup_of_odd_of_pow_two_pow hYD hYodd hcW hcn, rfl⟩

end Layer

end CFSG.SeitzReduction.TwistedE6Pilot
