module

public import CFSG.Assembly.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.ClassicalInvolution

section Closure

variable {G : Type*} [Group G]

theorem closure_eq_of_right_closed (gens : Set G) (E : Finset G) (h1 : (1 : G) ∈ E)
    (hcl : ∀ x ∈ E, ∀ g ∈ gens, x * g ∈ E) (hsub : ∀ x ∈ E, x ∈ Subgroup.closure gens) :
    (Subgroup.closure gens : Set G) = ↑E := by
  classical
  let R : Subgroup G :=
    { carrier := {y | ∀ x ∈ E, x * y ∈ E}
      one_mem' := fun x hx => by simpa using hx
      mul_mem' := fun {a b} ha hb x hx => by
        have := hb _ (ha x hx)
        simpa [mul_assoc] using this
      inv_mem' := fun {y} hy x hx => by
        have hinj : Function.Injective (fun e : G => e * y) := fun a b h => mul_right_cancel h
        have himg : E.image (fun e => e * y) ⊆ E := by
          intro w hw
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hw
          exact hy e he
        have heq : E.image (fun e => e * y) = E :=
          Finset.eq_of_subset_of_card_le himg (by rw [Finset.card_image_of_injective _ hinj])
        have hx' : x ∈ E.image (fun e => e * y) := by rw [heq]; exact hx
        obtain ⟨e, he, hex⟩ := Finset.mem_image.1 hx'
        have : x * y⁻¹ = e := by rw [← hex]; group
        rw [this]
        exact he }
  have hle : Subgroup.closure gens ≤ R := by
    rw [Subgroup.closure_le]
    intro g hg x hx
    exact hcl x hx g hg
  ext s
  constructor
  · intro hs
    have := hle hs 1 h1
    simpa using this
  · intro hs
    exact hsub s hs

theorem card_closure_of_right_closed (gens : Set G) (E : Finset G) (h1 : (1 : G) ∈ E)
    (hcl : ∀ x ∈ E, ∀ g ∈ gens, x * g ∈ E) (hsub : ∀ x ∈ E, x ∈ Subgroup.closure gens) :
    Nat.card (Subgroup.closure gens) = E.card := by
  have h := closure_eq_of_right_closed gens E h1 hcl hsub
  calc Nat.card (Subgroup.closure gens) = Nat.card ((Subgroup.closure gens : Set G)) := rfl
    _ = Nat.card (↑E : Set G) := by rw [h]
    _ = E.card := by simp

end Closure

section Centralizer

variable {G : Type*} [Group G]

theorem card_mul_centralizer_le [Finite G] (H : Subgroup G) (z : G) (N : ℕ) (f : Fin N → G)
    (hf : Function.Injective f) (hconj : ∀ i, ∃ h ∈ H, f i = h * z * h⁻¹) :
    N * Nat.card (Subgroup.centralizer ({z} : Set G) ⊓ H : Subgroup G) ≤ Nat.card H := by
  classical
  choose h hh hfh using hconj
  let I : Subgroup H := (Subgroup.centralizer ({z} : Set G) ⊓ H).subgroupOf H
  have hcardI : Nat.card I = Nat.card (Subgroup.centralizer ({z} : Set G) ⊓ H : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hinj : Function.Injective
      (fun i : Fin N => (QuotientGroup.mk (⟨h i, hh i⟩ : H) : H ⧸ I)) := by
    intro i j hij
    apply hf
    have hmem := QuotientGroup.eq.1 hij
    have hc : ((⟨h i, hh i⟩ : H)⁻¹ * ⟨h j, hh j⟩ : H) ∈ I := hmem
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hc
    have hcz := Subgroup.mem_centralizer_singleton_iff.1 hc.1
    set c : G := (h i)⁻¹ * h j with hcdef
    have hj : h j = h i * c := by rw [hcdef]; group
    have hcz' : c * z = z * c := hcz
    have key : c * z * c⁻¹ = z := by rw [hcz']; group
    rw [hfh i, hfh j, hj]
    calc h i * z * (h i)⁻¹ = h i * (c * z * c⁻¹) * (h i)⁻¹ := by rw [key]
      _ = h i * c * z * (h i * c)⁻¹ := by group
  have hmain : N ≤ Nat.card (H ⧸ I) := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup I
  calc N * Nat.card (Subgroup.centralizer ({z} : Set G) ⊓ H : Subgroup G)
      = N * Nat.card I := by rw [hcardI]
    _ ≤ Nat.card (H ⧸ I) * Nat.card I := Nat.mul_le_mul_right _ hmain
    _ = Nat.card H := hcard.symm

end Centralizer

section Fixed

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem card_centralizer_le_of_fixed [Finite G] (z : G) (ω : Ω) (hz : z • ω = ω) (F : Finset Ω)
    (hF : ∀ x, z • x = x → x ∈ F) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) ≤
      F.card * Nat.card (Subgroup.centralizer ({z} : Set G) ⊓ MulAction.stabilizer G ω :
        Subgroup G) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have horb : Nat.card (MulAction.orbit C ω) * Nat.card (MulAction.stabilizer C ω) =
      Nat.card C := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup C ω)
  have hsub : MulAction.orbit C ω ⊆ (↑F : Set Ω) := by
    rintro _ ⟨⟨c, hc⟩, rfl⟩
    apply hF
    have hzc : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    show z • (c • ω) = c • ω
    rw [← mul_smul, ← hzc, mul_smul, hz]
  have hle : Nat.card (MulAction.orbit C ω) ≤ F.card := by
    rw [Nat.card_coe_set_eq]
    calc (MulAction.orbit C ω).ncard ≤ (↑F : Set Ω).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet F)
      _ = F.card := Set.ncard_coe_finset F
  have hstab : Nat.card (MulAction.stabilizer C ω) =
      Nat.card (C ⊓ MulAction.stabilizer G ω : Subgroup G) := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← horb, hstab]
  exact Nat.mul_le_mul_right _ hle

end Fixed

section Rho

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem exists_hom_of_equivariant (z : G) {ι : Type*} (k : ι → G) (π : Ω → Finset (Fin 11))
    (σ : ι → Equiv.Perm (Fin 11)) (hcomm : ∀ i, k i * z = z * k i)
    (heq : ∀ (i : ι) (x : Ω), z • x = x → π (k i • x) = (π x).image (σ i))
    (huniq : ∀ τ τ' : Equiv.Perm (Fin 11),
      (∀ x : Ω, z • x = x → (π x).image τ = (π x).image τ') → τ = τ') :
    ∃ ρ : Subgroup.closure (Set.range k ∪ {z}) →* Equiv.Perm (Fin 11),
      (∀ i, ρ ⟨k i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)⟩ = σ i) ∧
      ρ ⟨z, Subgroup.subset_closure (Or.inr rfl)⟩ = 1 ∧
      ∀ (g : Subgroup.closure (Set.range k ∪ {z})) (x : Ω), z • x = x →
        π ((g : G) • x) = (π x).image (ρ g) := by
  classical
  set K : Subgroup G := Subgroup.closure (Set.range k ∪ {z}) with hK
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hK, Subgroup.closure_le]
    rintro g (⟨i, rfl⟩ | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm i)
    · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hfixmem : ∀ g ∈ K, ∀ x : Ω, z • x = x → z • (g • x) = g • x := by
    intro g hg x hx
    have hzc : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.1 (hKC hg)
    rw [← mul_smul, ← hzc, mul_smul, hx]
  have hP : ∀ g ∈ K, ∃ τ : Equiv.Perm (Fin 11),
      ∀ x : Ω, z • x = x → π (g • x) = (π x).image τ := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with ⟨i, rfl⟩ | rfl
      · exact ⟨σ i, heq i⟩
      · exact ⟨1, fun x hx => by rw [hx]; simp⟩
    | one => exact ⟨1, fun x hx => by simp⟩
    | mul g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
      obtain ⟨τ₁, h₁⟩ := ih₁
      obtain ⟨τ₂, h₂⟩ := ih₂
      refine ⟨τ₁ * τ₂, fun x hx => ?_⟩
      rw [mul_smul, h₁ _ (hfixmem g₂ hg₂ x hx), h₂ x hx, Finset.image_image]
      rfl
    | inv g hg ih =>
      obtain ⟨τ, h⟩ := ih
      refine ⟨τ⁻¹, fun x hx => ?_⟩
      have hfix : z • (g⁻¹ • x) = g⁻¹ • x := hfixmem g⁻¹ (K.inv_mem hg) x hx
      have h1 := h (g⁻¹ • x) hfix
      rw [smul_inv_smul g x] at h1
      rw [h1, Finset.image_image]
      ext y
      simp
  choose! τ hτ using hP
  have hτ1 : ∀ (g : G) (hg : g ∈ K) (x : Ω), z • x = x → π (g • x) = (π x).image (τ g) :=
    fun g hg => hτ g hg
  refine ⟨{ toFun := fun g => τ g.1
            map_one' := ?_
            map_mul' := ?_ }, ?_, ?_, ?_⟩
  · apply huniq
    intro x hx
    show (π x).image (τ (1 : G)) = (π x).image (⇑(1 : Equiv.Perm (Fin 11)))
    rw [← hτ1 1 K.one_mem x hx]
    simp
  · intro g h
    apply huniq
    intro x hx
    have hx' : z • ((h : G) • x) = (h : G) • x := hfixmem h h.2 x hx
    show (π x).image (τ ((g : G) * h)) = (π x).image (τ g * τ h)
    rw [← hτ1 _ (K.mul_mem g.2 h.2) x hx, mul_smul, hτ1 g g.2 _ hx', hτ1 h h.2 x hx,
      Finset.image_image]
    rfl
  · intro i
    apply huniq
    intro x hx
    show (π x).image (τ (k i)) = (π x).image (σ i)
    rw [← hτ1 (k i) (Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)) x hx, heq i x hx]
  · apply huniq
    intro x hx
    show (π x).image (τ z) = (π x).image (⇑(1 : Equiv.Perm (Fin 11)))
    rw [← hτ1 z (Subgroup.subset_closure (Or.inr rfl)) x hx, hx]
    simp
  · intro g x hx
    exact hτ1 g g.2 x hx

end Rho

section Alt

open Equiv Equiv.Perm

@[expose] def sig0 : Perm (Fin 11) := swap 1 2 * swap 3 4 * swap 5 6 * swap 9 10

@[expose] def sig1 : Perm (Fin 11) := swap 1 3 * swap 2 4 * swap 6 7 * swap 8 10

@[expose] def sig2 : Perm (Fin 11) := swap 0 1 * swap 3 5 * swap 6 8 * swap 7 9

@[expose] def sigmaOf : Fin 3 → Perm (Fin 11) := ![sig0, sig1, sig2]

theorem sig0_mem : sig0 ∈ alternatingGroup (Fin 11) := by
  unfold sig0
  rw [mem_alternatingGroup]
  decide

theorem sig1_mem : sig1 ∈ alternatingGroup (Fin 11) := by
  unfold sig1
  rw [mem_alternatingGroup]
  decide

theorem sig2_mem : sig2 ∈ alternatingGroup (Fin 11) := by
  unfold sig2
  rw [mem_alternatingGroup]
  decide

theorem sigmaOf_mem (i : Fin 3) : sigmaOf i ∈ alternatingGroup (Fin 11) := by
  fin_cases i
  · exact sig0_mem
  · exact sig1_mem
  · exact sig2_mem

theorem alternatingGroup_le_closure_sigma :
    alternatingGroup (Fin 11) ≤ Subgroup.closure (Set.range sigmaOf) := by
  set G' : Subgroup (Perm (Fin 11)) := Subgroup.closure (Set.range sigmaOf) with hG'
  have h0 : sig0 ∈ G' := Subgroup.subset_closure ⟨0, rfl⟩
  have h1 : sig1 ∈ G' := Subgroup.subset_closure ⟨1, rfl⟩
  have h2 : sig2 ∈ G' := Subgroup.subset_closure ⟨2, rfl⟩
  have htrans : ∀ j : Fin 11, ∃ g ∈ G', g 0 = j := by
    intro j
    fin_cases j
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨sig2, h2, by decide⟩
    · exact ⟨sig0 * sig2, mul_mem h0 h2, by decide⟩
    · exact ⟨sig1 * sig2, mul_mem h1 h2, by decide⟩
    · exact ⟨sig1 * sig0 * sig2, mul_mem (mul_mem h1 h0) h2, by decide⟩
    · exact ⟨sig2 * sig1 * sig2, mul_mem (mul_mem h2 h1) h2, by decide⟩
    · exact ⟨sig0 * sig2 * sig1 * sig2, mul_mem (mul_mem (mul_mem h0 h2) h1) h2, by decide⟩
    · exact ⟨sig1 * sig0 * sig2 * sig1 * sig2,
        mul_mem (mul_mem (mul_mem (mul_mem h1 h0) h2) h1) h2, by decide⟩
    · exact ⟨sig2 * sig0 * sig2 * sig1 * sig2,
        mul_mem (mul_mem (mul_mem (mul_mem h2 h0) h2) h1) h2, by decide⟩
    · exact ⟨sig2 * sig1 * sig0 * sig2 * sig1 * sig2,
        mul_mem (mul_mem (mul_mem (mul_mem (mul_mem h2 h1) h0) h2) h1) h2, by decide⟩
    · exact ⟨sig1 * sig2 * sig0 * sig2 * sig1 * sig2,
        mul_mem (mul_mem (mul_mem (mul_mem (mul_mem h1 h2) h0) h2) h1) h2, by decide⟩
  have : MulAction.IsPretransitive G' (Fin 11) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨gx, hgx, hx⟩ := htrans x
    obtain ⟨gy, hgy, hy⟩ := htrans y
    refine ⟨⟨gy * gx⁻¹, mul_mem hgy (inv_mem hgx)⟩, ?_⟩
    show (gy * gx⁻¹) x = y
    rw [Perm.mul_apply, ← hx]
    simpa using hy
  have : MulAction.IsPreprimitive G' (Fin 11) :=
    MulAction.IsPreprimitive.of_prime_card (by simp; norm_num)
  have hc : [sig0, sig1, sig0, sig2, sig1, sig2, sig0, sig1, sig0, sig2, sig1, sig2].prod =
      swap 0 7 * swap 0 5 := by decide +kernel
  have hcmem : [sig0, sig1, sig0, sig2, sig1, sig2, sig0, sig1, sig0, sig2, sig1, sig2].prod ∈
      G' := by
    refine Subgroup.list_prod_mem G' (fun x hx => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> assumption
  have h3 : IsThreeCycle
      [sig0, sig1, sig0, sig2, sig1, sig2, sig0, sig1, sig0, sig2, sig1, sig2].prod := by
    rw [hc]
    exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem (G := G') this h3 hcmem

end Alt

section Quasisimple

open Equiv Equiv.Perm
open scoped commutatorElement

theorem alt11_nonabelian : ∃ a b : alternatingGroup (Fin 11), a * b ≠ b * a := by
  refine ⟨⟨swap 0 1 * swap 0 2, ?_⟩, ⟨swap 0 3 * swap 0 4, ?_⟩, ?_⟩
  · rw [mem_alternatingGroup]
    decide
  · rw [mem_alternatingGroup]
    decide
  · intro h
    have h' := congrArg Subtype.val h
    revert h'
    decide

theorem alt11_center : Subgroup.center (alternatingGroup (Fin 11)) = ⊥ := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 11)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := alt11_nonabelian
    apply hab
    have ha : a ∈ Subgroup.center (alternatingGroup (Fin 11)) := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem alt11_perfect : commutator (alternatingGroup (Fin 11)) = ⊤ := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 11)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases hs.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 11))) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := alt11_nonabelian
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator (alternatingGroup (Fin 11)) := by
      rw [commutator]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · exact h

theorem isQuasisimple_of_alt_cover {K : Type*} [Group K] [Finite K]
    (φ : K →* alternatingGroup (Fin 11)) (hφ : Function.Surjective φ) (z : K) (hzker : φ z = 1)
    (hz1 : z ≠ 1) (hzc : z ∈ Subgroup.center K)
    (hcard : Nat.card K ≤ 2 * Nat.card (alternatingGroup (Fin 11)))
    (hcomm : z ∈ commutator K) :
    CFSG.Open.IsQuasisimple K ∧ Subgroup.center K = Subgroup.zpowers z ∧
      Nat.card (Subgroup.center K) = 2 := by
  classical
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 11)) :=
    alternatingGroup.isSimpleGroup (by simp)
  let e : K ⧸ φ.ker ≃* alternatingGroup (Fin 11) := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have hKcard : Nat.card K = Nat.card (alternatingGroup (Fin 11)) * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, Nat.card_congr e.toEquiv]
  have hApos : 0 < Nat.card (alternatingGroup (Fin 11)) := Nat.card_pos
  have hkerle : Nat.card φ.ker ≤ 2 := by
    by_contra h
    push Not at h
    have : 2 * Nat.card (alternatingGroup (Fin 11)) < Nat.card K := by rw [hKcard]; nlinarith
    omega
  have hzmem : z ∈ φ.ker := hzker
  have hzord : orderOf z = 2 := by
    have h1 : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.1 h)
    have h2 : orderOf z ≤ Nat.card φ.ker := by
      rw [← Nat.card_zpowers]
      exact Nat.card_le_card_of_injective _
        (Subgroup.inclusion_injective ((Subgroup.zpowers_le).2 hzmem))
    have h3 : 0 < orderOf z := orderOf_pos z
    omega
  have hkerz : φ.ker = Subgroup.zpowers z := by
    symm
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hzmem)
    rw [Nat.card_zpowers, hzord]
    exact hkerle
  have hcen_le : Subgroup.center K ≤ φ.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    have : φ g ∈ Subgroup.center (alternatingGroup (Fin 11)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨k, rfl⟩ := hφ a
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hg k]
    rw [alt11_center] at this
    exact this
  have hcen_eq : Subgroup.center K = φ.ker := by
    apply le_antisymm hcen_le
    rw [hkerz]
    exact (Subgroup.zpowers_le).2 hzc
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have hmap : (commutator K).map φ = ⊤ := by
      rw [commutator, Subgroup.map_commutator, Subgroup.map_top_of_surjective φ hφ]
      exact alt11_perfect
    rw [eq_top_iff]
    intro g _
    have hg : φ g ∈ (commutator K).map φ := by rw [hmap]; trivial
    obtain ⟨n, hn, hng⟩ := Subgroup.mem_map.1 hg
    have hker : g * n⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hng, mul_inv_cancel]
    have hzle : φ.ker ≤ commutator K := by
      rw [hkerz]
      exact (Subgroup.zpowers_le).2 hcomm
    have := mul_mem (hzle hker) hn
    simpa using this
  · have e₂ : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 11) :=
      (QuotientGroup.quotientMulEquivOfEq hcen_eq).trans e
    exact @MulEquiv.isSimpleGroup _ _ _ _ hsimple e₂
  · rw [hcen_eq, hkerz]
  · rw [hcen_eq, hkerz, Nat.card_zpowers, hzord]

theorem two_mul_card_le_of_alt_cover {K : Type*} [Group K] [Finite K]
    (φ : K →* alternatingGroup (Fin 11)) (hφ : Function.Surjective φ) (z : K) (hzker : φ z = 1)
    (hz1 : z ≠ 1) : 2 * Nat.card (alternatingGroup (Fin 11)) ≤ Nat.card K := by
  classical
  let e : K ⧸ φ.ker ≃* alternatingGroup (Fin 11) := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have hKcard : Nat.card K = Nat.card (alternatingGroup (Fin 11)) * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, Nat.card_congr e.toEquiv]
  have hzmem : z ∈ φ.ker := hzker
  have h1 : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.1 h)
  have h3 : 0 < orderOf z := orderOf_pos z
  have h2 : orderOf z ≤ Nat.card φ.ker := by
    rw [← Nat.card_zpowers]
    exact Nat.card_le_card_of_injective _
      (Subgroup.inclusion_injective ((Subgroup.zpowers_le).2 hzmem))
  have hker2 : 2 ≤ Nat.card φ.ker := by omega
  rw [hKcard, Nat.mul_comm 2]
  exact Nat.mul_le_mul_left _ hker2

end Quasisimple

end CFSG.ClassicalInvolution
