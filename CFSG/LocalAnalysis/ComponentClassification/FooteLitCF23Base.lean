module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5Fus
public import CFSG.Sporadic.SmallOddCore.Assembly

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def CF23InnerFusionFor (τ : ∀ (Y : Type), [Group Y] → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal →
    centralizer (N : Set G) = ⊥ → τ ↥N →
    ∀ (α : G) (J : Subgroup G), orderOf α = 2 → J ≤ N →
      J ≤ centralizer ({α} : Set G) → IsComponent (J.subgroupOf (centralizer ({α} : Set G))) →
      IsStandardSubgroup J →
      ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 2 p f) ∨
        Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7))) →
      Odd (Nat.card (center ↥J)) → ¬ CF23Exception ↥N (↥J ⧸ center ↥J) →
      ∀ ζ ∈ J, orderOf ζ = 2 → ∃ γ ∈ N, γ⁻¹ * α * γ = α * ζ

theorem cf23InnerFusion_of (h : CF23InnerFusionFor fun Y _ => GSRestricted Y) :
    CF23InnerFusion := h

theorem concl_of_coset {G : Type*} [Group G] {N : Subgroup G} {α : G} {J : Subgroup G}
    (hα : orderOf α = 2) (hJN : J ≤ N) (hJα : J ≤ centralizer ({α} : Set G))
    (hZ : Odd (Nat.card (center ↥J)))
    (hcos : ∀ x : G, orderOf x = 2 → α⁻¹ * x ∈ N → ∃ γ ∈ N, γ⁻¹ * α * γ = x) :
    ∀ ζ ∈ J, orderOf ζ = 2 → ∃ γ ∈ N, γ⁻¹ * α * γ = α * ζ := by
  intro ζ hζ hζ2
  have hc : α * ζ = ζ * α := (mem_centralizer_singleton_iff.mp (hJα hζ)).symm
  have hα2 : α * α = 1 := by rw [← pow_two, ← hα, pow_orderOf_eq_one]
  have hζ2' : ζ * ζ = 1 := by rw [← pow_two, ← hζ2, pow_orderOf_eq_one]
  apply hcos
  · have hne : α * ζ ≠ 1 := by
      intro h1
      have hαζ : ζ = α := by
        rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hα2]
      have hαJ : α ∈ J := hαζ ▸ hζ
      have hαZ : (⟨α, hαJ⟩ : J) ∈ center ↥J := by
        rw [mem_center_iff]
        intro g
        exact Subtype.ext (mem_centralizer_singleton_iff.mp (hJα g.2))
      have h2 : orderOf (⟨⟨α, hαJ⟩, hαZ⟩ : center ↥J) = 2 := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
        exact hα
      have h3 := orderOf_dvd_natCard (⟨⟨α, hαJ⟩, hαZ⟩ : center ↥J)
      rw [h2] at h3
      exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr h3)
    refine orderOf_eq_prime ?_ hne
    rw [sq, mul_assoc, ← mul_assoc ζ, ← hc, mul_assoc, hζ2', mul_one, hα2]
  · rw [← mul_assoc, inv_mul_cancel, one_mul]
    exact hJN hζ

@[expose] def OneClass (X : Type*) [Group X] : Prop :=
  ∀ x y : X, orderOf x = 2 → orderOf y = 2 → ∃ g : X, g⁻¹ * x * g = y

theorem OneClass.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : OneClass Y) :
    OneClass X := by
  intro x y hx hy
  obtain ⟨g, hg⟩ := h (e x) (e y) ((orderOf_injective e.toMonoidHom e.injective x).trans hx)
    ((orderOf_injective e.toMonoidHom e.injective y).trans hy)
  refine ⟨e.symm g, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg]

theorem oneClass_of_rep {M : Type*} [Group M] {Γ : Subgroup M} {t : M}
    (h : ∀ x ∈ Γ, orderOf x = 2 → ∃ g ∈ Γ, g * x * g⁻¹ = t) : OneClass Γ := by
  intro x y hx hy
  obtain ⟨g, hg, hgx⟩ := h x x.2 (by rw [Subgroup.orderOf_coe, hx])
  obtain ⟨k, hk, hky⟩ := h y y.2 (by rw [Subgroup.orderOf_coe, hy])
  refine ⟨⟨g, hg⟩⁻¹ * ⟨k, hk⟩, Subtype.ext ?_⟩
  have e : (y : M) = k⁻¹ * (g * x * g⁻¹) * k := by rw [hgx, ← hky]; group
  simp only [coe_mul, coe_inv, mul_inv_rev, inv_inv]
  rw [e]
  group

theorem coset_of_inner {G : Type*} [Group G] {N : Subgroup G} {α : G} (hα : orderOf α = 2)
    (hαN : α ∈ N) (h : OneClass N) :
    ∀ x : G, orderOf x = 2 → α⁻¹ * x ∈ N → ∃ γ ∈ N, γ⁻¹ * α * γ = x := by
  intro x hx hαx
  have hxN : x ∈ N := by
    have := N.mul_mem hαN hαx
    rwa [mul_inv_cancel_left] at this
  obtain ⟨g, hg⟩ := h ⟨α, hαN⟩ ⟨x, hxN⟩ (by rw [Subgroup.orderOf_mk, hα])
    (by rw [Subgroup.orderOf_mk, hx])
  exact ⟨g, g.2, congrArg Subtype.val hg⟩

theorem coset_of_autModel {M : Type*} [Group M] {P R : Subgroup M}
    (h : Sporadic.SmallOddCore.AutModel P R) {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hC : centralizer (N : Set G) = ⊥) (θ : N ≃* P) {α : G}
    (hcos : ∀ s ∈ P, orderOf (h.embed N θ α * s) = 2 →
      ∃ c ∈ P, c⁻¹ * h.embed N θ α * c = h.embed N θ α * s) :
    ∀ x : G, orderOf x = 2 → α⁻¹ * x ∈ N → ∃ γ ∈ N, γ⁻¹ * α * γ = x := by
  intro x hx hαx
  set ι := h.embed N θ with hι
  have hinj := h.embed_injective N θ hC
  have hxe : x = α * (α⁻¹ * x) := by group
  have hs : ι (α⁻¹ * x) = ((θ ⟨α⁻¹ * x, hαx⟩ : P) : M) := h.embed_coe N θ ⟨α⁻¹ * x, hαx⟩
  have hord : orderOf (ι α * ((θ ⟨α⁻¹ * x, hαx⟩ : P) : M)) = 2 := by
    rw [← hs, ← map_mul, ← hxe, orderOf_injective ι hinj, hx]
  obtain ⟨c, hcP, hc⟩ := hcos _ (θ ⟨α⁻¹ * x, hαx⟩).2 hord
  refine ⟨(θ.symm ⟨c, hcP⟩ : G), (θ.symm ⟨c, hcP⟩).2, hinj ?_⟩
  have hc' : ι (θ.symm ⟨c, hcP⟩ : G) = c := by
    rw [h.embed_coe N θ (θ.symm ⟨c, hcP⟩), MulEquiv.apply_symm_apply]
  rw [map_mul, map_mul, map_inv, hc', hc, ← hs, ← map_mul, ← hxe]

theorem embed_mem_orderOf {M : Type*} [Group M] {P R : Subgroup M}
    (h : Sporadic.SmallOddCore.AutModel P R) {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hC : centralizer (N : Set G) = ⊥) (θ : N ≃* P) {α : G} (hα : orderOf α = 2) :
    h.embed N θ α ∈ R ∧ orderOf (h.embed N θ α) = 2 :=
  ⟨h.embed_mem N θ α, by rw [orderOf_injective _ (h.embed_injective N θ hC), hα]⟩

theorem mem_of_conjNormal_mem_inner {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hC : centralizer (N : Set G) = ⊥) {g : G}
    (h : MulAut.conjNormal g ∈ OuterAutomorphisms.inner N) : g ∈ N := by
  obtain ⟨n, hn⟩ := h
  have hc : (n : G)⁻¹ * g ∈ centralizer (N : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have e := congrArg (fun φ : MulAut N => ((φ ⟨x, hx⟩ : N) : G)) hn
    simp only [MulAut.conj_apply, coe_mul, coe_inv, MulAut.conjNormal_apply] at e
    calc x * ((n : G)⁻¹ * g) = (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * g := by group
      _ = (n : G)⁻¹ * (g * x * g⁻¹) * g := by rw [e]
      _ = (n : G)⁻¹ * g * x := by group
  rw [hC, mem_bot, inv_mul_eq_one] at hc
  rw [← hc]
  exact n.2

theorem mem_inner_of_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {φ : MulAut X}
    (h : MulAut.congr e φ ∈ OuterAutomorphisms.inner Y) : φ ∈ OuterAutomorphisms.inner X := by
  rw [← OuterAutomorphisms.inner_map_congr e] at h
  obtain ⟨ψ, hψ, he⟩ := h
  rwa [(MulAut.congr e).injective he] at hψ

theorem mem_of_inv_inner {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hC : centralizer (N : Set G) = ⊥) {α : G} (hα : orderOf α = 2)
    (h : ∀ φ : MulAut N, φ ^ 2 = 1 → φ ∈ OuterAutomorphisms.inner N) : α ∈ N := by
  apply mem_of_conjNormal_mem_inner hC
  apply h
  rw [← map_pow, ← hα, pow_orderOf_eq_one, map_one]

theorem isComponent_inner {G : Type*} [Group G] {N J : Subgroup G} {α : G} (hαN : α ∈ N)
    (hJN : J ≤ N) (hJα : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G)))) :
    J.subgroupOf N ≤ centralizer ({⟨α, hαN⟩} : Set N) ∧
      IsComponent ((J.subgroupOf N).subgroupOf (centralizer ({⟨α, hαN⟩} : Set N))) := by
  obtain ⟨hq, hs⟩ := hJ
  have hle : J.subgroupOf N ≤ centralizer ({⟨α, hαN⟩} : Set N) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hJα (mem_subgroupOf.mp hx)))
  let f : centralizer ({⟨α, hαN⟩} : Set N) →* centralizer ({α} : Set G) :=
    { toFun := fun x => ⟨((x : N) : G), mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.2))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨hle, ?_, ?_⟩
  · have e : ↥((J.subgroupOf N).subgroupOf (centralizer ({⟨α, hαN⟩} : Set N))) ≃*
        ↥(J.subgroupOf (centralizer ({α} : Set G))) :=
      (subgroupOfEquivOfLe hle).trans
        ((subgroupOfEquivOfLe hJN).trans (subgroupOfEquivOfLe hJα).symm)
    exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hq
  · have he : (J.subgroupOf N).subgroupOf (centralizer ({⟨α, hαN⟩} : Set N)) =
        (J.subgroupOf (centralizer ({α} : Set G))).comap f := by
      ext x
      simp only [mem_subgroupOf, mem_comap]
      rfl
    rw [he]
    exact hs.comap f

theorem card_quotient_center_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (A ⧸ center A) = Nat.card (B ⧸ center B) :=
  Nat.card_congr (QuotientGroup.congr (center A) (center B) e (map_center_eq e)).toEquiv

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card]
  have h := two_mul_card_alternatingGroup (α := Fin 7)
  rw [Fintype.card_perm, Fintype.card_fin] at h
  have : Nat.factorial 7 = 5040 := rfl
  omega

theorem card_small {X : Type} [Group X]
    (h : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel X .PSL 2 p f) ∨
      Nonempty (X ≃* alternatingGroup (Fin 7))) :
    (∃ q : ℕ, Odd q ∧ 5 ≤ q ∧ Nat.card X = q * (q ^ 2 - 1) / 2) ∨ Nat.card X = 2520 := by
  rcases h with ⟨p, f, hp, hp2, -, h5, hm⟩ | ⟨⟨e⟩⟩
  · refine Or.inl ⟨p ^ f, (hp.odd_of_ne_two hp2).pow, h5, ?_⟩
    rw [card_of_lieModel_psl_two hp2 hm]
    have hg : Nat.gcd 2 (p ^ f - 1) = 2 :=
      Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd (hp.odd_of_ne_two hp2).pow odd_one))
    simp only [Open.ordA, show 1 * (1 + 1) / 2 = 1 from rfl, pow_one,
      show Finset.Icc 2 (1 + 1) = {2} from rfl, Finset.prod_singleton, show 1 + 1 = 2 from rfl,
      hg]
  · exact Or.inr (by rw [Nat.card_congr e.toEquiv, card_alternatingGroup_seven])

theorem small_ord_ne_20160 (q : ℕ) : q * (q ^ 2 - 1) / 2 ≠ 20160 := by
  intro h
  have hq : q < 40 := by
    by_contra hq
    push Not at hq
    have h1 : 40 * (40 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    generalize q * (q ^ 2 - 1) = t at h h1
    norm_num at h1
    omega
  interval_cases q <;> simp_all

theorem not_small_of_card_20160 {X : Type} [Group X] (hX : Nat.card X = 20160)
    (h : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel X .PSL 2 p f) ∨
      Nonempty (X ≃* alternatingGroup (Fin 7))) : False := by
  rcases card_small h with ⟨q, -, -, hq⟩ | h7
  · exact small_ord_ne_20160 q (hq ▸ hX)
  · omega

end CFSG.ComponentClassification.GSThmB.CF23I
