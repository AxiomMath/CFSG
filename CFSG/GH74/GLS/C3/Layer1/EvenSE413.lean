module

public import CFSG.GH74.GLS.Pattern

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG
open scoped Pointwise

section Aux

theorem nonempty_centralizer_equiv_of_isConj' {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Nonempty (↥(centralizer ({a} : Set G)) ≃* ↥(centralizer ({b} : Set G))) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have key : ∀ g : G, g ∈ centralizer ({a} : Set G) → c * g * c⁻¹ ∈ centralizer ({b} : Set G) := by
    intro g hg
    rw [mem_centralizer_singleton_iff] at hg ⊢
    rw [← hc]
    calc c * g * c⁻¹ * (c * a * c⁻¹) = c * (g * a) * c⁻¹ := by group
      _ = c * (a * g) * c⁻¹ := by rw [hg]
      _ = c * a * c⁻¹ * (c * g * c⁻¹) := by group
  have key' : ∀ g : G, g ∈ centralizer ({b} : Set G) → c⁻¹ * g * c ∈ centralizer ({a} : Set G) := by
    intro g hg
    rw [mem_centralizer_singleton_iff] at hg ⊢
    have hg' : g * (c * a * c⁻¹) = (c * a * c⁻¹) * g := by rw [hc]; exact hg
    calc c⁻¹ * g * c * a = c⁻¹ * (g * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * g) * c := by rw [hg']
      _ = a * (c⁻¹ * g * c) := by group
  exact ⟨{
    toFun := fun g => ⟨c * (g : G) * c⁻¹, key g g.2⟩
    invFun := fun g => ⟨c⁻¹ * (g : G) * c, key' g g.2⟩
    left_inv := fun g => Subtype.ext (by
      show c⁻¹ * (c * (g : G) * c⁻¹) * c = (g : G)
      group)
    right_inv := fun g => Subtype.ext (by
      show c * (c⁻¹ * (g : G) * c) * c⁻¹ = (g : G)
      group)
    map_mul' := fun g h => Subtype.ext (by
      show c * ((g : G) * (h : G)) * c⁻¹ = c * (g : G) * c⁻¹ * (c * (h : G) * c⁻¹)
      group) }⟩

theorem card_centralizer_eq_of_isConj' {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Nat.card ↥(centralizer ({a} : Set G)) = Nat.card ↥(centralizer ({b} : Set G)) := by
  obtain ⟨e⟩ := nonempty_centralizer_equiv_of_isConj' h
  exact Nat.card_congr e.toEquiv

theorem eq_of_le_perm {P : Type*} [Finite P] (π : P → P) (hπ : Function.Surjective π) (a : P → ℕ)
    (h : ∀ c, a c ≤ a (π c)) : ∀ c, a (π c) = a c := by
  have hbij : Function.Bijective π := ⟨Finite.injective_iff_surjective.2 hπ, hπ⟩
  have := Fintype.ofFinite P
  have hsum : ∑ c, a (π c) = ∑ c, a c := Equiv.sum_comp (Equiv.ofBijective π hbij) a
  have hle : ∀ c ∈ Finset.univ, a c ≤ a (π c) := fun c _ => h c
  have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum.symm
  intro c
  exact (this c (Finset.mem_univ c)).symm

theorem orderOf_conj_eq' {G : Type*} [Group G] (c g : G) : orderOf (c * g * c⁻¹) = orderOf g := by
  have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective g
  simpa [MulAut.conj_apply] using this

theorem isPGroup_zpowers_of_orderOf_two' {G : Type*} [Group G] {g : G} (hg : orderOf g = 2) :
    IsPGroup 2 (zpowers g) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, hg, pow_one]

end Aux

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_sylow' (P : Sylow 2 G) {g : G} (hg : IsPGroup 2 (zpowers g)) :
    ∃ c : G, c * g * c⁻¹ ∈ (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨c, ?_⟩
  have h1 : g ∈ (Q : Subgroup G) := hQ (mem_zpowers g)
  have h3 : ((c • Q : Sylow 2 G) : Subgroup G) = MulAut.conj c • (Q : Subgroup G) :=
    Sylow.coe_subgroup_smul
  have h4 : c * g * c⁻¹ ∈ ((c • Q : Sylow 2 G) : Subgroup G) := by
    rw [h3, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨g, h1, by simp [MulAut.conj_apply]⟩
  rw [hc] at h4
  exact h4

theorem sylow_of_map (H : Subgroup G) (S : Sylow 2 G) (S' : Sylow 2 ↥H)
    (φ : ↥(S : Subgroup G) ≃* ↥(S' : Subgroup ↥H)) :
    ∃ S2 : Sylow 2 G, (S2 : Subgroup G) = (S' : Subgroup ↥H).map H.subtype := by
  have hcard : Nat.card ↥((S' : Subgroup ↥H).map H.subtype) = Nat.card ↥(S : Subgroup G) := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact (Nat.card_congr φ.toEquiv).symm
  refine ⟨Sylow.ofCard ((S' : Subgroup ↥H).map H.subtype) ?_, rfl⟩
  rw [hcard]
  exact Sylow.card_eq_multiplicity S

theorem samePattern_key (H : Subgroup G) (h : SameCentralizerOfInvolutionPattern G ↥H) :
    (∀ t : G, t ∈ H → orderOf t = 2 → ∀ y : G, y * t = t * y → y ∈ H) ∧
    (∀ s t : G, s ∈ H → t ∈ H → orderOf s = 2 → orderOf t = 2 → IsConj s t →
      ∃ k ∈ H, k * s * k⁻¹ = t) := by
  obtain ⟨S, S', φ, hconj, hcent⟩ := h
  obtain ⟨S2, hS2⟩ := sylow_of_map H S S' φ
  let ψ : ↥(S : Subgroup G) →* G :=
    H.subtype.comp (((S' : Subgroup ↥H)).subtype.comp φ.toMonoidHom)
  have hψ : ∀ u, ψ u = (((φ u : ↥(S' : Subgroup ↥H)) : ↥H) : G) := fun u => rfl
  have hψinj : Function.Injective ψ := by
    intro u v huv
    apply φ.injective
    apply Subtype.ext
    apply Subtype.ext
    exact huv
  have hψord : ∀ u : ↥(S : Subgroup G), orderOf (ψ u) = orderOf u :=
    fun u => orderOf_injective ψ hψinj u
  have hψS2 : ∀ t : G, t ∈ (S2 : Subgroup G) → ∃ u : ↥(S : Subgroup G), ψ u = t := by
    intro t ht
    rw [hS2] at ht
    obtain ⟨y, hy, rfl⟩ := ht
    obtain ⟨u, hu⟩ := φ.surjective ⟨y, hy⟩
    exact ⟨u, by rw [hψ, hu]; rfl⟩
  let Inv : Type := {u : ↥(S : Subgroup G) // orderOf u = 2}
  let e : Inv → ConjClasses G := fun u => ConjClasses.mk ((u.1 : ↥(S : Subgroup G)) : G)
  let f : Inv → ConjClasses G := fun u => ConjClasses.mk (ψ u.1)
  have hef : ∀ u v : Inv, e u = e v → f u = f v := by
    intro u v huv
    have h1 : IsConj (u.1 : G) (v.1 : G) := ConjClasses.mk_eq_mk_iff_isConj.1 huv
    have h2 := (hconj u.1 v.1 u.2 v.2).1 h1
    have h3 := H.subtype.map_isConj h2
    exact ConjClasses.mk_eq_mk_iff_isConj.2 h3
  have hrange : ∀ u : Inv, ∃ v : Inv, f u = e v := by
    intro u
    have hord : orderOf (ψ u.1) = 2 := by rw [hψord]; exact u.2
    obtain ⟨c, hc⟩ := exists_conj_mem_sylow' S (isPGroup_zpowers_of_orderOf_two' hord)
    refine ⟨⟨⟨c * ψ u.1 * c⁻¹, hc⟩, ?_⟩, ?_⟩
    · rw [Subgroup.orderOf_mk, orderOf_conj_eq']; exact hord
    · exact ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨c, rfl⟩)
  let P : Type := {c : ConjClasses G // ∃ u : Inv, e u = c}
  have hPfin : Finite P := inferInstance
  let π : P → P := fun c =>
    ⟨f (Classical.choose c.2), by
      obtain ⟨v, hv⟩ := hrange (Classical.choose c.2)
      exact ⟨v, hv.symm⟩⟩
  have hπspec : ∀ (c : P) (u : Inv), e u = c.1 → (π c).1 = f u := by
    intro c u hu
    exact hef _ _ ((Classical.choose_spec c.2).trans hu.symm)
  have hπsurj : Function.Surjective π := by
    intro c'
    obtain ⟨v, hv⟩ := c'.2
    have hord : orderOf ((v.1 : ↥(S : Subgroup G)) : G) = 2 := by
      rw [Subgroup.orderOf_coe]; exact v.2
    obtain ⟨c, hc⟩ := exists_conj_mem_sylow' S2 (isPGroup_zpowers_of_orderOf_two' hord)
    obtain ⟨u, hu⟩ := hψS2 _ hc
    have huord : orderOf u = 2 := by rw [← hψord, hu, orderOf_conj_eq']; exact hord
    refine ⟨⟨e ⟨u, huord⟩, ⟨⟨u, huord⟩, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    rw [hπspec _ ⟨u, huord⟩ rfl]
    show ConjClasses.mk (ψ u) = c'.1
    rw [← hv, hu]
    exact (ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨c, rfl⟩)).symm
  have hπinj : Function.Injective π := Finite.injective_iff_surjective.2 hπsurj
  have hfe : ∀ u v : Inv, f u = f v → e u = e v := by
    intro u v huv
    have h1 : π ⟨e u, ⟨u, rfl⟩⟩ = π ⟨e v, ⟨v, rfl⟩⟩ := by
      apply Subtype.ext
      rw [hπspec _ u rfl, hπspec _ v rfl]; exact huv
    exact congrArg Subtype.val (hπinj h1)
  let aCl : ConjClasses G → ℕ := fun c =>
    Nat.card ↥(centralizer ({Classical.choose (ConjClasses.exists_rep c)} : Set G))
  have haCl : ∀ g : G, aCl (ConjClasses.mk g) = Nat.card ↥(centralizer ({g} : Set G)) := by
    intro g
    apply card_centralizer_eq_of_isConj'
    exact ConjClasses.mk_eq_mk_iff_isConj.1
      (Classical.choose_spec (ConjClasses.exists_rep (ConjClasses.mk g)))
  let ι : ∀ u : Inv, ↥(centralizer ({((φ u.1 : ↥(S' : Subgroup ↥H)) : ↥H)} : Set ↥H)) →
      ↥(centralizer ({ψ u.1} : Set G)) := fun u x =>
    ⟨(x.1 : G), by
      have hx := x.2
      rw [mem_centralizer_singleton_iff] at hx ⊢
      exact congrArg Subtype.val hx⟩
  have hι : ∀ u : Inv, Function.Injective (ι u) := by
    intro u x y hxy
    have h2 : ((ι u x : ↥(centralizer ({ψ u.1} : Set G))) : G) =
        ((ι u y : ↥(centralizer ({ψ u.1} : Set G))) : G) := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h2)
  have hBC : ∀ u : Inv, Nat.card ↥(centralizer ({((φ u.1 : ↥(S' : Subgroup ↥H)) : ↥H)} : Set ↥H)) ≤
      Nat.card ↥(centralizer ({ψ u.1} : Set G)) := fun u => Nat.card_le_card_of_injective _ (hι u)
  have hineq : ∀ c : P, aCl c.1 ≤ aCl (π c).1 := by
    intro c
    obtain ⟨u, hu⟩ := c.2
    have h1 : aCl c.1 = Nat.card ↥(centralizer ({((u.1 : ↥(S : Subgroup G)) : G)} : Set G)) := by
      rw [← hu]; exact haCl _
    have h2 : aCl (π c).1 = Nat.card ↥(centralizer ({ψ u.1} : Set G)) := by
      rw [hπspec c u hu]; exact haCl _
    obtain ⟨e1⟩ := hcent u.1 u.2
    rw [h1, h2, Nat.card_congr e1.toEquiv]
    exact hBC u
  have heq := eq_of_le_perm π hπsurj (fun c => aCl c.1) hineq
  have hBCeq : ∀ u : Inv, Nat.card ↥(centralizer ({ψ u.1} : Set G)) ≤
      Nat.card ↥(centralizer ({((φ u.1 : ↥(S' : Subgroup ↥H)) : ↥H)} : Set ↥H)) := by
    intro u
    have h0 := heq ⟨e u, ⟨u, rfl⟩⟩
    have h1 : aCl (e u) = Nat.card ↥(centralizer ({((u.1 : ↥(S : Subgroup G)) : G)} : Set G)) :=
      haCl _
    have h2 : aCl (π ⟨e u, ⟨u, rfl⟩⟩).1 = Nat.card ↥(centralizer ({ψ u.1} : Set G)) := by
      rw [hπspec _ u rfl]; exact haCl _
    obtain ⟨e1⟩ := hcent u.1 u.2
    have h3 : aCl (π ⟨e u, ⟨u, rfl⟩⟩).1 = aCl (e u) := h0
    rw [h2, h1, Nat.card_congr e1.toEquiv] at h3
    exact h3.le
  have hιsurj : ∀ u : Inv, Function.Surjective (ι u) := fun u =>
    (Function.Injective.bijective_of_nat_card_le (hι u) (hBCeq u)).2
  have hFi0 : ∀ u : Inv, ∀ y : G, y * ψ u.1 = ψ u.1 * y → y ∈ H := by
    intro u y hy
    have hy' : y ∈ centralizer ({ψ u.1} : Set G) := by
      rw [mem_centralizer_singleton_iff]; exact hy
    obtain ⟨x, hx⟩ := hιsurj u ⟨y, hy'⟩
    have hxy : (x.1 : G) = y := congrArg Subtype.val hx
    rw [← hxy]; exact x.1.2
  have hconjH : ∀ t : G, t ∈ H → orderOf t = 2 →
      ∃ (h1 : ↥H) (u : Inv), ψ u.1 = (h1 : G) * t * (h1 : G)⁻¹ := by
    intro t ht hord
    let t' : ↥H := ⟨t, ht⟩
    have ht'ord : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact hord
    obtain ⟨h1, hh1⟩ := exists_conj_mem_sylow' S' (isPGroup_zpowers_of_orderOf_two' ht'ord)
    have hg : ((h1 * t' * h1⁻¹ : ↥H) : G) ∈ (S2 : Subgroup G) := by
      rw [hS2]; exact ⟨_, hh1, rfl⟩
    obtain ⟨u, hu⟩ := hψS2 _ hg
    have hgeq : ((h1 * t' * h1⁻¹ : ↥H) : G) = (h1 : G) * t * (h1 : G)⁻¹ := rfl
    have huord : orderOf u = 2 := by
      rw [← hψord, hu, hgeq, orderOf_conj_eq']; exact hord
    exact ⟨h1, ⟨u, huord⟩, by rw [hu, hgeq]⟩
  refine ⟨?_, ?_⟩
  · intro t ht hord y hy
    obtain ⟨h1, u, hu⟩ := hconjH t ht hord
    have hy' : ((h1 : G) * y * (h1 : G)⁻¹) * ψ u.1 = ψ u.1 * ((h1 : G) * y * (h1 : G)⁻¹) := by
      rw [hu]
      calc (h1 : G) * y * (h1 : G)⁻¹ * ((h1 : G) * t * (h1 : G)⁻¹)
          = (h1 : G) * (y * t) * (h1 : G)⁻¹ := by group
        _ = (h1 : G) * (t * y) * (h1 : G)⁻¹ := by rw [hy]
        _ = (h1 : G) * t * (h1 : G)⁻¹ * ((h1 : G) * y * (h1 : G)⁻¹) := by group
    have hmem := hFi0 u _ hy'
    have : y = ((h1 : G)⁻¹) * ((h1 : G) * y * (h1 : G)⁻¹) * (h1 : G) := by group
    rw [this]
    exact mul_mem (mul_mem (H.inv_mem h1.2) hmem) h1.2
  · intro s t hs ht hso hto hst
    obtain ⟨h1, u, hu⟩ := hconjH s hs hso
    obtain ⟨h2, v, hv⟩ := hconjH t ht hto
    have hconjuv : IsConj (ψ u.1) (ψ v.1) := by
      rw [hu, hv]
      have h1' : IsConj s ((h1 : G) * s * (h1 : G)⁻¹) := isConj_iff.2 ⟨h1, rfl⟩
      have h2' : IsConj t ((h2 : G) * t * (h2 : G)⁻¹) := isConj_iff.2 ⟨h2, rfl⟩
      exact h1'.symm.trans (hst.trans h2')
    have hfuv : f u = f v := ConjClasses.mk_eq_mk_iff_isConj.2 hconjuv
    have heuv : e u = e v := hfe u v hfuv
    have h3 : IsConj (u.1 : G) (v.1 : G) := ConjClasses.mk_eq_mk_iff_isConj.1 heuv
    have h4 := (hconj u.1 v.1 u.2 v.2).1 h3
    obtain ⟨k, hk⟩ := isConj_iff.1 h4
    have hk' : (k : G) * ψ u.1 * (k : G)⁻¹ = ψ v.1 := by
      have := congrArg Subtype.val hk
      simpa [hψ] using this
    refine ⟨(h2 : G)⁻¹ * (k : G) * (h1 : G), ?_, ?_⟩
    · exact mul_mem (mul_mem (H.inv_mem h2.2) k.2) h1.2
    · rw [hu, hv] at hk'
      calc (h2 : G)⁻¹ * (k : G) * (h1 : G) * s * ((h2 : G)⁻¹ * (k : G) * (h1 : G))⁻¹
          = (h2 : G)⁻¹ * ((k : G) * ((h1 : G) * s * (h1 : G)⁻¹) * (k : G)⁻¹) * (h2 : G) := by group
        _ = (h2 : G)⁻¹ * ((h2 : G) * t * (h2 : G)⁻¹) * (h2 : G) := by rw [hk']
        _ = t := by group

theorem samePattern_even (heven : Even (Nat.card G)) (H : Subgroup G)
    (h : SameCentralizerOfInvolutionPattern G ↥H) : Even (Nat.card H) := by
  obtain ⟨S, S', φ, -, -⟩ := h
  obtain ⟨S2, hS2⟩ := sylow_of_map H S S' φ
  have h2G : 2 ∣ Nat.card G := even_iff_two_dvd.1 heven
  have hpos : 0 < (Nat.card G).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2G
  have hS2le : (S2 : Subgroup G) ≤ H := by
    rw [hS2]
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have h2S : 2 ∣ Nat.card (S2 : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity S2]
    exact dvd_pow_self 2 hpos.ne'
  exact even_iff_two_dvd.2 (h2S.trans (Subgroup.card_dvd_of_le hS2le))

theorem eq_top_or_isStronglyEmbedded_of_samePattern (heven : Even (Nat.card G)) (H : Subgroup G)
    (h : SameCentralizerOfInvolutionPattern G ↥H) : H = ⊤ ∨ IsStronglyEmbedded H := by
  by_cases htop : H = ⊤
  · exact Or.inl htop
  right
  obtain ⟨hFi, hFii⟩ := samePattern_key H h
  refine ⟨htop, samePattern_even heven H h, fun g hg => ?_⟩
  by_contra hodd
  have hev : Even (Nat.card ↥(H ⊓ conjugate H g)) := Nat.not_odd_iff_even.1 hodd
  have h2 : 2 ∣ Nat.card ↥(H ⊓ conjugate H g) := even_iff_two_dvd.1 hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ conjugate H g)) 2 h2
  have htH : (t' : G) ∈ H := t'.2.1
  have htg : (t' : G) ∈ conjugate H g := t'.2.2
  have hto : orderOf (t' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht'
  obtain ⟨y, hyH, hy⟩ := htg
  have hy1 : g⁻¹ * y * g = (t' : G) := by simpa [MulAut.conj_apply] using hy
  have hy' : g * (t' : G) * g⁻¹ = y := by
    rw [← hy1]; group
  have hsH : g * (t' : G) * g⁻¹ ∈ H := by rw [hy']; exact hyH
  have hso : orderOf (g * (t' : G) * g⁻¹) = 2 := by
    rw [orderOf_conj_eq']; exact hto
  have hconj : IsConj (t' : G) (g * (t' : G) * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  obtain ⟨k, hk, hkt⟩ := hFii _ _ htH hsH hto hso hconj
  have hcomm : (g⁻¹ * k) * (t' : G) = (t' : G) * (g⁻¹ * k) := by
    have h3 : k * (t' : G) * k⁻¹ = g * (t' : G) * g⁻¹ := hkt
    calc g⁻¹ * k * (t' : G) = g⁻¹ * (k * (t' : G) * k⁻¹) * k := by group
      _ = g⁻¹ * (g * (t' : G) * g⁻¹) * k := by rw [h3]
      _ = (t' : G) * (g⁻¹ * k) := by group
  have hgk : g⁻¹ * k ∈ H := hFi _ htH hto _ hcomm
  apply hg
  have : g = k * (g⁻¹ * k)⁻¹ := by group
  rw [this]
  exact mul_mem hk (H.inv_mem hgk)

end Main

end CFSG.GH74.GLS
