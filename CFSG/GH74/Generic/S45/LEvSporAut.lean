module

public import CFSG.GH74.Generic.S45.LEvSporCorr
public import CFSG.GH74.Generic.S45.LEvSporGen

public section

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

namespace CFSG.GH74.Generic.S45

section

variable {G : Type*} [Group G]

theorem mul_mem_iff_of_card [Finite G] {N H : Subgroup G} (hHN : H ≤ N)
    (hcard : Nat.card ↥N = 2 * Nat.card ↥H) {a b : G} (ha : a ∈ N) (hb : b ∈ N) :
    a * b ∈ H ↔ (a ∈ H ↔ b ∈ H) := by
  have hrel : H.relIndex N = 2 := by
    have h1 := Subgroup.relIndex_mul_card H N
    rw [inf_eq_left.2 hHN, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥H)) h1
  have hidx : (H.subgroupOf N).index = 2 := hrel
  have := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  simpa [Subgroup.mem_subgroupOf] using this

theorem card_cent_of_outer [Finite G] {N H : Subgroup G} (hHN : H ≤ N)
    (hcard : Nat.card ↥N = 2 * Nat.card ↥H) {t v : G} (hv : v ∈ N) (hvH : v ∉ H)
    (hvt : v * t = t * v) :
    Nat.card ↥(centralizer ({t} : Set G) ⊓ N) = 2 * Nat.card ↥(centralizer ({t} : Set G) ⊓ H) := by
  set C : Subgroup G := centralizer ({t} : Set G) ⊓ N with hC
  set C₀ : Subgroup G := centralizer ({t} : Set G) ⊓ H with hC₀
  have hC₀C : C₀ ≤ C := inf_le_inf_left _ hHN
  have hvC : v ∈ C := ⟨mem_centralizer_singleton_iff.2 hvt, hv⟩
  have hrel : C₀.relIndex C = 2 := by
    have hidx : (C₀.subgroupOf C).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨v, hvC⟩, fun b => ?_⟩
      have hbN : (b : G) ∈ N := b.2.2
      have hiff := mul_mem_iff_of_card hHN hcard hbN hv
      have hbc : (b : G) ∈ centralizer ({t} : Set G) := b.2.1
      have hbvc : (b : G) * v ∈ centralizer ({t} : Set G) :=
        Subgroup.mul_mem _ hbc (mem_centralizer_singleton_iff.2 hvt)
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, hC₀, Subgroup.mem_inf]
      by_cases hbH : (b : G) ∈ H
      · have : (b : G) * v ∉ H := fun h => hvH (hiff.1 h |>.1 hbH)
        exact Or.inr ⟨⟨hbc, hbH⟩, fun h => this h.2⟩
      · have : (b : G) * v ∈ H := hiff.2 (iff_of_false hbH hvH)
        exact Or.inl ⟨⟨hbvc, this⟩, fun h => hbH h.2⟩
    exact hidx
  have h1 := Subgroup.relIndex_mul_card C₀ C
  rw [inf_eq_left.2 hC₀C, hrel] at h1
  exact h1.symm


theorem eq_one_or_eq_of_cent5₂ {H₁ H₂ : Subgroup G} {t : G} (ht2 : t * t = 1)
    (hcent5 : ∀ z ∈ H₁, z ∈ centralizer ({t} : Set G) → orderOf z = 5 →
      ∀ c ∈ H₂, c ∈ centralizer ({t} : Set G) → c * z = z * c → ∃ j : ℕ, c = z ^ j ∨ c = t * z ^ j)
    {K : Subgroup G} (hKH : K ≤ H₁) (hK : K ≤ centralizer ({t} : Set G))
    (e : ↥K ≃* alternatingGroup (Fin 5)) {w : G} (hwH : w ∈ H₂) (hw : w ∈ centralizer ({t} : Set G))
    (hwK : ∀ k ∈ K, k * w = w * k) : w = 1 ∨ w = t := by
  obtain ⟨z, hzK, hz5⟩ := a5_exists_five e
  obtain ⟨j, hj⟩ := hcent5 z (hKH hzK) (hK hzK) hz5 w hwH hw (hwK z hzK).symm
  have hzjK : z ^ j ∈ K := K.pow_mem hzK j
  have htK : ∀ k ∈ K, k * t = t * k := fun k hk => by
    have := hK hk
    rw [mem_centralizer_singleton_iff] at this
    exact this
  rcases hj with hj | hj
  · left
    have : z ^ j = 1 := a5_eq_one_of_forall_comm e hzjK fun k hk => by rw [← hj]; exact hwK k hk
    rw [hj, this]
  · right
    have : z ^ j = 1 := by
      refine a5_eq_one_of_forall_comm e hzjK fun k hk => ?_
      have h1 : t * z ^ j = w := hj.symm
      have h2 : z ^ j = t * w := by
        calc z ^ j = (t * t) * z ^ j := by rw [ht2, one_mul]
          _ = t * (t * z ^ j) := by rw [mul_assoc]
          _ = t * w := by rw [h1]
      rw [h2, ← mul_assoc, htK k hk, mul_assoc, hwK k hk, ← mul_assoc]
    rw [hj, this, mul_one]


theorem conj_setup_N {N H K : Subgroup G} {t g x : G} (hg : g ∈ N)
    (hnorm : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H) (hKH : K ≤ H)
    (e : ↥K ≃* alternatingGroup (Fin 5)) (hx : x = g * t * g⁻¹) (hKx : ∀ k ∈ K, k * x = x * k) :
    ∃ K₁ : Subgroup G, (∀ y, y ∈ K₁ ↔ g * y * g⁻¹ ∈ K) ∧
      Nonempty (↥K₁ ≃* alternatingGroup (Fin 5)) ∧ K₁ ≤ H ∧ K₁ ≤ centralizer ({t} : Set G) := by
  set K₁ : Subgroup G := K.map (MulAut.conj g⁻¹).toMonoidHom with hK₁
  have hmem : ∀ y, y ∈ K₁ ↔ g * y * g⁻¹ ∈ K := fun y => by
    rw [hK₁, mem_map_conj_iff, inv_inv]
  have e₁ : ↥K₁ ≃* alternatingGroup (Fin 5) :=
    (Subgroup.equivMapOfInjective K (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm.trans e
  have hK₁H : K₁ ≤ H := by
    intro y hy
    have : g * y * g⁻¹ ∈ K := (hmem y).1 hy
    have h2 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ ∈ H := hnorm g⁻¹ (N.inv_mem hg) _ (hKH this)
    simpa [mul_assoc] using h2
  have hK₁t : K₁ ≤ centralizer ({t} : Set G) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    have hk := (hmem y).1 hy
    have h1 := hKx _ hk
    rw [hx] at h1
    have h2 : g * (y * t) * g⁻¹ = g * (t * y) * g⁻¹ := by
      calc g * (y * t) * g⁻¹ = g * y * g⁻¹ * (g * t * g⁻¹) := by group
        _ = g * t * g⁻¹ * (g * y * g⁻¹) := h1
        _ = g * (t * y) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  exact ⟨K₁, hmem, ⟨e₁⟩, hK₁H, hK₁t⟩

theorem exists_conj_mem_sylow [Finite G] {C Q : Subgroup G} (hQ : IsSylowOf 2 Q C) {w : G}
    (hw : w ∈ C) (hw2 : orderOf w = 2) : ∃ g ∈ C, g⁻¹ * w * g ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let w' : ↥C := ⟨w, hw⟩
  have hw'2 : orderOf w' = 2 := by rw [← Subgroup.orderOf_coe]; exact hw2
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers w') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw'2]; norm_num)
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  have hS' : IsSylowOf 2 ((S : Subgroup ↥C).map C.subtype) C := ⟨S, rfl⟩
  obtain ⟨k, hk, hconj⟩ := hQ.exists_mem_conj hS'
  refine ⟨k, hk, (hconj w).1 ?_⟩
  exact ⟨w', hS (Subgroup.mem_zpowers w'), rfl⟩


end

section Transfer

variable {G G' : Type*} [Group G] [Group G'] {N : Subgroup G} {W : Subgroup G'} {ψ : ↥N ≃* ↥W}

theorem Corr.exists_of_le' (ψ : ↥N ≃* ↥W) {A : Subgroup G} (h : A ≤ N) :
    ∃ A' : Subgroup G', Corr ψ A A' := by
  obtain ⟨A', hA'⟩ := Corr.exists_of_le ψ.symm h
  exact ⟨A', by simpa using hA'.symm⟩

theorem Corr.isSylowOf_iff [Finite G] [Finite G'] {Q C : Subgroup G} {Q' C' : Subgroup G'}
    (hQ : Corr ψ Q Q') (hC : Corr ψ C C') (hle : Q ≤ C) {p : ℕ} [Fact p.Prime] :
    IsSylowOf p Q C ↔ IsSylowOf p Q' C' := by
  have hle' : Q' ≤ C' := by
    intro q' hq'
    have hqW : q' ∈ W := hQ.le' hq'
    have h1 : ((ψ.symm ⟨q', hqW⟩ : ↥N) : G) ∈ Q := (hQ.mem_iff _).2 (by simpa using hq')
    have h2 := (hC.mem_iff (ψ.symm ⟨q', hqW⟩)).1 (hle h1)
    simpa using h2
  constructor
  · intro h
    refine isSylowOf_of_card hle' ?_
    rw [← hQ.card_eq, ← hC.card_eq]
    exact h.card_eq
  · intro h
    refine isSylowOf_of_card hle ?_
    rw [hQ.card_eq, hC.card_eq]
    exact h.card_eq

theorem Corr.exists_elt (ψ : ↥N ≃* ↥W) {a' : G'} (ha' : a' ∈ W) :
    ∃ (a : G) (ha : a ∈ N), ((ψ ⟨a, ha⟩ : ↥W) : G') = a' :=
  ⟨((ψ.symm ⟨a', ha'⟩ : ↥N) : G), (ψ.symm ⟨a', ha'⟩).2, by simp⟩

end Transfer

section Cfg

variable {G : Type*} [Group G] [Finite G]

structure CfgData (N H K Q E : Subgroup G) (x : G) : Prop where
  hHN : H ≤ N
  hnorm : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H
  hcard : Nat.card ↥N = 2 * Nat.card ↥H
  hKH : K ≤ H
  K5 : Nonempty (↥K ≃* alternatingGroup (Fin 5))
  hQC : Q ≤ centralizer (K : Set G) ⊓ N
  hQs : IsSylowOf 2 Q (centralizer (K : Set G) ⊓ N)
  hEQ : E ≤ Q
  hEa : IsElementaryAbelian 2 ↥E
  hE4 : 4 ≤ Nat.card ↥E
  hxQ : x ∈ Q
  hx2 : orderOf x = 2
  hKx : ∀ k ∈ K, k * x = x * k

end Cfg

section CfgTransfer

variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']

theorem CfgData.of_corr {N H K Q E : Subgroup G} {x : G} {W D : Subgroup G'} (ψ : ↥N ≃* ↥W)
    (hH : Corr ψ H D) (h : CfgData N H K Q E x) :
    ∃ (K' Q' E' : Subgroup G') (x' : G'), CfgData W D K' Q' E' x' ∧ Corr ψ K K' ∧ Corr ψ Q Q' ∧
      Corr ψ E E' ∧ ∃ hx : x ∈ N, ((ψ ⟨x, hx⟩ : ↥W) : G') = x' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : K ≤ N := h.hKH.trans h.hHN
  have hQN : Q ≤ N := h.hQC.trans inf_le_right
  have hEN : E ≤ N := h.hEQ.trans hQN
  have hxN : x ∈ N := hQN h.hxQ
  obtain ⟨K', hK⟩ := Corr.exists_of_le' ψ hKN
  obtain ⟨Q', hQ⟩ := Corr.exists_of_le' ψ hQN
  obtain ⟨E', hE⟩ := Corr.exists_of_le' ψ hEN
  have hC : Corr ψ (centralizer (K : Set G) ⊓ N) (centralizer (K' : Set G') ⊓ W) :=
    hK.scorr.centralizer
  have hTop : Corr ψ N W := Corr.top
  have hx' : ((ψ ⟨x, hxN⟩ : ↥W) : G') ∈ Q' := (hQ.mem_iff ⟨x, hxN⟩).1 h.hxQ
  obtain ⟨e5⟩ := h.K5
  obtain ⟨f⟩ := hK.nonempty_mulEquiv
  refine ⟨K', Q', E', (ψ ⟨x, hxN⟩ : ↥W), ?_, hK, hQ, hE, hxN, rfl⟩
  refine ⟨hH.le', ?_, ?_, ?_, ⟨f.symm.trans e5⟩, ?_, ?_, ?_, ?_, ?_, hx', ?_, ?_⟩
  · intro n' hn' h' hh'
    obtain ⟨n, hn, rfl⟩ := Corr.exists_elt ψ hn'
    obtain ⟨m, hm, rfl⟩ := Corr.exists_elt ψ (hH.le' hh')
    have hmH : m ∈ H := (hH.mem_iff ⟨m, hm⟩).2 hh'
    have h1 : (⟨n * m * n⁻¹, N.mul_mem (N.mul_mem hn hm) (N.inv_mem hn)⟩ : ↥N) =
        ⟨n, hn⟩ * ⟨m, hm⟩ * ⟨n, hn⟩⁻¹ := rfl
    have := (hH.mem_iff ⟨n * m * n⁻¹, N.mul_mem (N.mul_mem hn hm) (N.inv_mem hn)⟩).1
      (h.hnorm n hn m hmH)
    rw [h1] at this
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using this
  · rw [← hTop.card_eq, ← hH.card_eq]
    exact h.hcard
  · intro k' hk'
    obtain ⟨k, hk, rfl⟩ := Corr.exists_elt ψ (hK.le' hk')
    exact (hH.mem_iff ⟨k, hk⟩).1 (h.hKH ((hK.mem_iff ⟨k, hk⟩).2 hk'))
  · intro q' hq'
    obtain ⟨q, hq, rfl⟩ := Corr.exists_elt ψ (hQ.le' hq')
    exact (hC.mem_iff ⟨q, hq⟩).1 (h.hQC ((hQ.mem_iff ⟨q, hq⟩).2 hq'))
  · exact (hQ.isSylowOf_iff hC h.hQC).1 h.hQs
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := Corr.exists_elt ψ (hE.le' he')
    exact (hQ.mem_iff ⟨e, he⟩).1 (h.hEQ ((hE.mem_iff ⟨e, he⟩).2 he'))
  · exact hE.isElementaryAbelian_iff.1 h.hEa
  · rw [← hE.card_eq]
    exact h.hE4
  · exact (orderOf_corr ψ ⟨x, hxN⟩).trans h.hx2
  · intro k' hk'
    obtain ⟨k, hk, rfl⟩ := Corr.exists_elt ψ (hK.le' hk')
    have hkK : k ∈ K := (hK.mem_iff ⟨k, hk⟩).2 hk'
    have := congrArg (fun z : ↥N => ((ψ z : ↥W) : G'))
      (Subtype.ext (h.hKx k hkK) : (⟨k, hk⟩ : ↥N) * ⟨x, hxN⟩ = ⟨x, hxN⟩ * ⟨k, hk⟩)
    simpa only [map_mul, Subgroup.coe_mul] using this

end CfgTransfer

section Pull

variable {G G' : Type*} [Group G] [Group G'] {N H : Subgroup G} {W D : Subgroup G'}

theorem Corr.pull_outer (ψ : ↥N ≃* ↥W) (hH : Corr ψ H D) {x : G} (hx : x ∈ N) {u' : G'}
    (hu'W : u' ∈ W) (hu'D : u' ∉ D) (hu'2 : orderOf u' = 2)
    (hu'x : u' * ((ψ ⟨x, hx⟩ : ↥W) : G') = ((ψ ⟨x, hx⟩ : ↥W) : G') * u') :
    ∃ u ∈ N, u ∉ H ∧ orderOf u = 2 ∧ u * x = x * u := by
  obtain ⟨u, hu, rfl⟩ := Corr.exists_elt ψ hu'W
  refine ⟨u, hu, fun huH => hu'D ((hH.mem_iff ⟨u, hu⟩).1 huH), ?_, ?_⟩
  · rw [← orderOf_corr ψ ⟨u, hu⟩]
    exact hu'2
  · have h1 : ψ (⟨u, hu⟩ * ⟨x, hx⟩) = ψ (⟨x, hx⟩ * ⟨u, hu⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext hu'x
    exact congrArg Subtype.val (ψ.injective h1)

theorem fusion_transport (ψ : ↥N ≃* ↥W) {x y : G} (hx : x ∈ N) (hy : y ∈ N)
    (hynot : ∀ n ∈ N, n * x * n⁻¹ ≠ y)
    (hemb : ∃ f : ↥(centralizer ({y} : Set G) ⊓ N) →* ↥(centralizer ({x} : Set G) ⊓ N),
      Function.Injective f) :
    (∀ n' ∈ W, n' * ((ψ ⟨x, hx⟩ : ↥W) : G') * n'⁻¹ ≠ ((ψ ⟨y, hy⟩ : ↥W) : G')) ∧
      Nat.card ↥(centralizer ({((ψ ⟨y, hy⟩ : ↥W) : G')} : Set G') ⊓ W) ∣
        Nat.card ↥(centralizer ({((ψ ⟨x, hx⟩ : ↥W) : G')} : Set G') ⊓ W) := by
  refine ⟨?_, ?_⟩
  · intro n' hn' h
    obtain ⟨n, hn, rfl⟩ := Corr.exists_elt ψ hn'
    apply hynot n hn
    have h1 : ψ (⟨n, hn⟩ * ⟨x, hx⟩ * ⟨n, hn⟩⁻¹) = ψ ⟨y, hy⟩ := by
      rw [map_mul, map_mul, map_inv]
      exact Subtype.ext h
    exact congrArg Subtype.val (ψ.injective h1)
  · obtain ⟨f, hf⟩ := hemb
    have hdvd := Subgroup.card_dvd_of_injective f hf
    have hx' := (SCorr.singleton hx rfl (ψ := ψ)).centralizer.card_eq
    have hy' := (SCorr.singleton hy rfl (ψ := ψ)).centralizer.card_eq
    rw [hx', hy'] at hdvd
    exact hdvd

theorem Corr.pull_conj {Q : Subgroup G} {Q' : Subgroup G'} (ψ : ↥N ≃* ↥W) (hQ : Corr ψ Q Q')
    {y : G} (hy : y ∈ N) {n' : G'} (hn' : n' ∈ W)
    (h : n' * ((ψ ⟨y, hy⟩ : ↥W) : G') * n'⁻¹ ∈ Q') : ∃ n ∈ N, n * y * n⁻¹ ∈ Q := by
  obtain ⟨n, hn, rfl⟩ := Corr.exists_elt ψ hn'
  refine ⟨n, hn, (hQ.mem_iff ⟨n * y * n⁻¹, N.mul_mem (N.mul_mem hn hy) (N.inv_mem hn)⟩).2 ?_⟩
  have h1 : (⟨n * y * n⁻¹, N.mul_mem (N.mul_mem hn hy) (N.inv_mem hn)⟩ : ↥N) =
      ⟨n, hn⟩ * ⟨y, hy⟩ * ⟨n, hn⟩⁻¹ := rfl
  rw [h1]
  simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h

end Pull

end CFSG.GH74.Generic.S45
