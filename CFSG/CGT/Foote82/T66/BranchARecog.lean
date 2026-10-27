module

public import CFSG.CGT.Foote82.T66.BranchAHeart
public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.Main
import CFSG.RankThree.PartTwo.Sec19.SimsItem316SmallModels
import CFSG.GF2Type.Smith1980Orth.W4SigmaGL
import CFSG.CGT.Foote82.T66.Overgroup
public import CFSG.CGT.Foote82.T66.BranchAOdd

public section

namespace CFSG.CGT.Foote82.BranchAAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.RankThree.PartTwo

section Types

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem altNatural_of_omegaPlus {L : Subgroup (GLV V)} (h : IsOmegaPlusModule L 3) :
    IsAltNaturalModule L 8 := by
  obtain ⟨φ, ψ, hψ⟩ := CFSG.RankThree.PartTwo.Sec19.SimsItem316Small.omegaPlusTwo_three_model
  obtain ⟨α, hα, β, hβ, hβk, hR⟩ := h
  refine ⟨φ.toMonoidHom.comp α, φ.surjective.comp hα, ψ.toAddMonoidHom.comp β,
    ψ.surjective.comp hβ, ?_, ?_⟩
  · rw [← hβk]
    ext w
    simp
  · intro ℓ w w' hw x hx
    have h1 := hR ℓ w w' hw
    show ψ (β w') = _
    rw [h1]
    exact hψ (α ℓ) (β w) x hx

theorem evenWeightPerm_one {n : ℕ} (x : evenWeight n) : evenWeightPerm 1 x = x := by
  apply Subtype.ext
  funext i
  rfl

theorem invariant_fixedSpace_self (L : Subgroup (GLV V)) : Invariant L (fixedSpace L) :=
  fun k hk u hu l hl => by rw [hu k hk]; exact hu l hl

theorem invariant_commSpace_self (L : Subgroup (GLV V)) : Invariant L (commSpace L ⊤) :=
  fun _ hk _ hu => apply_mem_commSpace hk hu

theorem injective_of_altNatural {L : Subgroup (GLV V)} (hfaith : FaithfulTildeV L) {n : ℕ}
    (α : ↥L →* alternatingGroup (Fin n)) (β : ↥(commSpace L ⊤) →+ altHeart n)
    (hβk : β.ker = ((fixedSpace L).comap (commSpace L ⊤).subtype).toAddSubgroup)
    (hR : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) (w : V) →
      ∀ x : evenWeight n, β w = (x : altHeart n) →
        β w' = (evenWeightPerm (α ℓ : Equiv.Perm (Fin n)) x : altHeart n)) :
    Function.Injective α := by
  rw [injective_iff_map_eq_one]
  intro ℓ hℓ
  apply Subtype.ext
  refine hfaith ℓ ℓ.2 fun w hw => ?_
  set w₀ : ↥(commSpace L ⊤) := ⟨w, hw⟩
  set w₁ : ↥(commSpace L ⊤) := ⟨(ℓ : GLV V) w, apply_mem_commSpace ℓ.2 hw⟩
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (β w₀)
  have h1 := hR ℓ w₀ w₁ rfl x hx.symm
  rw [hℓ] at h1
  simp only [OneMemClass.coe_one, evenWeightPerm_one] at h1
  have hker : w₁ - w₀ ∈ β.ker := by
    rw [AddMonoidHom.mem_ker, map_sub, h1, hx, sub_self]
  rw [hβk] at hker
  exact hker

theorem card_GLV_four {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (h4 : Module.finrank (ZMod 2) W = 4) :
    Nat.card (W ≃ₗ[ZMod 2] W) = 20160 := by
  rw [CFSG.GF2Type.Smith1980Orth.W4Sigma.card_linearEquiv_eq_prod h4]
  simp [Fin.prod_univ_succ]

theorem injective_of_a7Four {L : Subgroup (GLV V)} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hfaith : FaithfulTildeV L) (hirr : HasIrrTildeV L)
    (α : ↥L →* alternatingGroup (Fin 7)) (hα : Function.Surjective α)
    (h4 : Module.finrank (ZMod 2) (TildeV L) = 4) : Function.Injective α := by
  have hperf : ⁅L, L⁆ = L := commutator_eq_self_of_isQuasisimple hq
  have hLq : CFSG.IsQuasisimple ↥L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥L).1 hq
  let ρ := sectHom L (invariant_fixedSpace_self L) (invariant_commSpace_self L)
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro ℓ hℓ
    apply Subtype.ext
    refine hfaith ℓ ℓ.2 fun w hw => ?_
    have h1 := congrArg (fun f : GLV (Sect (fixedSpace L) (commSpace L ⊤)) =>
      f (Submodule.Quotient.mk ⟨w, hw⟩)) hℓ
    simp only [sectHom_mk, ρ] at h1
    have h2 := (Submodule.Quotient.eq _).1 h1
    exact h2
  have hdvd : Nat.card ↥L ∣ 20160 := by
    have := Subgroup.card_dvd_of_injective ρ hρ
    rwa [card_GLV_four h4] at this
  have hcard : Nat.card ↥L = 2520 * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv,
      nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hk8 : Nat.card α.ker ∣ 8 := by
    rw [hcard, show (20160 : ℕ) = 2520 * 8 from rfl] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hcen : α.ker ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq (MonoidHom.normal_ker α) with h | h
    · exfalso
      have : ∀ ℓ : ↥L, α ℓ = 1 := fun ℓ => by
        have : ℓ ∈ α.ker := by rw [h]; trivial
        exact this
      have h3 := hα ⟨Equiv.swap 0 1 * Equiv.swap 0 2,
        (Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide)
          (by decide)).mem_alternatingGroup⟩
      obtain ⟨ℓ, hℓ⟩ := h3
      rw [this ℓ] at hℓ
      have := congrArg (fun σ : alternatingGroup (Fin 7) => (σ : Equiv.Perm (Fin 7)) 0) hℓ
      simp at this
      exact absurd this (by decide)
    · exact h
  have hnoinv : ∀ t ∈ α.ker, orderOf t ≠ 2 := by
    intro t ht ht2
    have htc : ∀ l ∈ L, l * (t : GLV V) = (t : GLV V) * l := by
      intro l hl
      have := Subgroup.mem_center_iff.1 (hcen ht) ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hp : IsPGroup 2 (Subgroup.zpowers (t : GLV V)) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht2, pow_one]
    have h61 := (CFSG.CGT.Foote82.lemma61 hperf hirr htc hp).2
    have ht1 : t = 1 := by
      apply Subtype.ext
      refine hfaith t t.2 fun w hw => ?_
      have : (t : GLV V) w = w := h61 hw (t : GLV V) (Subgroup.mem_zpowers _)
      rw [this, sub_self]
      exact Submodule.zero_mem _
    rw [ht1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hk1 : Nat.card α.ker = 1 := by
    by_contra hne
    have h2 : 2 ∣ Nat.card α.ker := by
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (show Nat.card α.ker ∣ 2 ^ 3 by simpa using hk8)
      rcases k with _ | k
      · simp at hk; exact absurd hk hne
      · rw [hk, pow_succ]
        exact dvd_mul_left 2 _
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := α.ker) 2 h2
    exact hnoinv t t.2 (by rw [← Subgroup.orderOf_coe] at ht; exact ht)
  rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one]
  exact hk1

end Types

section Recog

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L : Subgroup (GLV V)} {z : GLV V}

open CFSG.EvenSmallLie.OddTranspAlt

theorem isComponentOf_subgroupOf_of {Γ : Type*} [Group Γ] {Q H G : Subgroup Γ}
    (hQ : IsComponentOf Q H) (hQG : Q ≤ G) : IsComponentOf (Q.subgroupOf G) (H.subgroupOf G) :=
  ⟨Subgroup.comap_mono hQ.1, hQ.2.1.comap G.subtype,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQG) hQ.2.2⟩

theorem isComponentOf_map_equiv {Γ Δ : Type*} [Group Γ] [Group Δ] (f : Γ ≃* Δ)
    {Q H : Subgroup Γ} (hQ : IsComponentOf Q H) :
    IsComponentOf (Q.map f.toMonoidHom) (H.map f.toMonoidHom) :=
  ⟨Subgroup.map_mono hQ.1, hQ.2.1.map f.toMonoidHom,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Q.equivMapOfInjective _ f.injective).symm hQ.2.2⟩

theorem centralizer_subgroupOf {z : GLV V} (hz : z ∈ G) :
    (G ⊓ Subgroup.centralizer ({z} : Set (GLV V))).subgroupOf G =
      Subgroup.centralizer ({(⟨z, hz⟩ : ↥G)} : Set ↥G) := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    exact Subtype.ext h
  · intro h
    exact ⟨g.2, congrArg Subtype.val h⟩

theorem closure_cls_eq_top (hc : OddTranspConf G L z) :
    Subgroup.closure (cls (⟨z, z_mem_G hc.std⟩ : ↥G)) = ⊤ := by
  apply Subgroup.map_injective G.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
  conv_rhs => rw [hc.gen]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨e, rfl⟩, rfl⟩
    exact ⟨e, e.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩ * ⟨z, z_mem_G hc.std⟩ * ⟨g, hg⟩⁻¹, ⟨⟨g, hg⟩, rfl⟩, rfl⟩

theorem orderOf_swap01 (n : ℕ) : orderOf (Equiv.swap (0 : Fin (n + 2)) 1) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two, Equiv.swap_mul_self]
  · intro h
    have := congrArg (fun σ : Equiv.Perm (Fin (n + 2)) => σ 0) h
    simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at this
    exact absurd this (by simp [Fin.ext_iff])

theorem fixed_zpowers_swap01 (n : ℕ) :
    {i : Fin (n + 2) | ∀ r ∈ Subgroup.zpowers (Equiv.swap (0 : Fin (n + 2)) 1), r i = i} =
      {k | k ≠ 0 ∧ k ≠ 1} := by
  have h01 : (0 : Fin (n + 2)) ≠ 1 := by simp [Fin.ext_iff]
  ext i
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    have hi := h _ (Subgroup.mem_zpowers _)
    constructor
    · rintro rfl
      rw [Equiv.swap_apply_left] at hi
      exact h01 hi.symm
    · rintro rfl
      rw [Equiv.swap_apply_right] at hi
      exact h01 hi
  · rintro ⟨h0, h1⟩ r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (Equiv.swap_apply_of_ne_of_ne h0 h1) k

theorem exists_perm_equiv (hc : OddTranspConf G L z) {n : ℕ} (hn : 7 ≤ n)
    (ε : ↥L ≃* alternatingGroup (Fin n)) :
    ∃ φ : ↥G ≃* Equiv.Perm (Fin (n + 2)), φ ⟨z, z_mem_G hc.std⟩ = Equiv.swap 0 1 ∧
      (L.subgroupOf G).map φ.toMonoidHom = altOn {k | k ≠ 0 ∧ k ≠ 1} := by
  have h := hc.std
  have hzG := z_mem_G h
  have hLG := L_le_G h
  set t : ↥G := ⟨z, hzG⟩ with ht_def
  have ht : orderOf t = 2 := by rw [Subgroup.orderOf_mk]; exact h.orderOf_s
  have hot : ∀ x ∈ cls t, ∀ y ∈ cls t, Odd (orderOf (x * y)) ∨ orderOf (x * y) = 2 := by
    rintro _ ⟨e₁, rfl⟩ _ ⟨e₂, rfl⟩
    have h1 := hc.oddTransp e₁ e₁.2 e₂ e₂.2
    rw [← Subgroup.orderOf_coe]
    have hpos := orderOf_pos ((e₁ * t * e₁⁻¹ * (e₂ * t * e₂⁻¹) : ↥G) : GLV V)
    have e : ((e₁ * t * e₁⁻¹ * (e₂ * t * e₂⁻¹) : ↥G) : GLV V) =
        (e₁ : GLV V) * z * (e₁ : GLV V)⁻¹ * ((e₂ : GLV V) * z * (e₂ : GLV V)⁻¹) := rfl
    rw [e] at hpos ⊢
    rcases h1 with h1 | h1
    · rcases Nat.lt_or_ge (orderOf ((e₁ : GLV V) * z * (e₁ : GLV V)⁻¹ *
          ((e₂ : GLV V) * z * (e₂ : GLV V)⁻¹))) 2 with h2 | h2
      · left
        rw [show orderOf ((e₁ : GLV V) * z * (e₁ : GLV V)⁻¹ *
          ((e₂ : GLV V) * z * (e₂ : GLV V)⁻¹)) = 1 by omega]
        exact odd_one
      · right
        omega
    · left
      exact h1
  have hY : IsComponentOf (L.subgroupOf G) (Subgroup.centralizer ({t} : Set ↥G)) := by
    rw [← centralizer_subgroupOf hzG]
    exact isComponentOf_subgroupOf_of (h.component_of_inv z hzG h.orderOf_s (z_mem_cent h)) hLG
  have htop := closure_cls_eq_top hc
  have hYle : L.subgroupOf G ≤ Subgroup.closure (cls t) := by
    rw [htop]
    exact le_top
  have hk2 : ∀ e ∈ cls t, e ≠ t → t * e = e * t →
      e ∉ Subgroup.centralizer ((L.subgroupOf G : Subgroup ↥G) : Set ↥G) := by
    intro e he hne hcomm hcen
    have he2 : orderOf e = 2 := orderOf_of_mem_cls_of ht he
    have heK : (e : GLV V) ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)) := by
      refine Subgroup.mem_inf.2 ⟨e.2, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
      have hl' : (⟨l, hLG hl⟩ : ↥G) ∈ L.subgroupOf G := hl
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hcen _ hl')
    have hcomm' : (e : GLV V) * z = z * (e : GLV V) := (congrArg Subtype.val hcomm).symm
    have := eq_of_commute_of_pRank_one hc.rank heK (z_mem_K h)
      (by rw [Subgroup.orderOf_coe]; exact he2) h.orderOf_s hcomm'
    exact hne (Subtype.ext this)
  obtain ⟨φ₀, hφ₀⟩ := oddTranspAlt ht hot hn hY hYle
    ⟨(Subgroup.subgroupOfEquivOfLe hLG).trans ε⟩ hk2
  let θ : ↥G ≃* Subgroup.closure (cls t) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
  have hθ : ∀ g : ↥G, ((θ g : Subgroup.closure (cls t)) : ↥G) = g := fun _ => rfl
  have hswap : (φ₀ (θ t)).IsSwap := (hφ₀ (θ t)).1 (by rw [hθ]; exact self_mem_cls)
  obtain ⟨a, b, hab, hsw⟩ := hswap
  obtain ⟨c, hc'⟩ := isConj_iff.1
    (Equiv.Perm.isConj_swap hab (show (0 : Fin (n + 2)) ≠ 1 by simp [Fin.ext_iff]))
  let φ : ↥G ≃* Equiv.Perm (Fin (n + 2)) := (θ.trans φ₀).trans (MulAut.conj c)
  have hφt : φ t = Equiv.swap 0 1 := by
    show c * φ₀ (θ t) * c⁻¹ = _
    rw [hsw, hc']
  refine ⟨φ, hφt, ?_⟩
  have hR : IsPGroup 2 (Subgroup.zpowers (Equiv.swap (0 : Fin (n + 2)) 1)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_swap01, pow_one])
  have hX : (Subgroup.centralizer ({t} : Set ↥G)).map φ.toMonoidHom =
      Subgroup.centralizer
        ((Subgroup.zpowers (Equiv.swap (0 : Fin (n + 2)) 1) : Subgroup _) : Set _) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    ext σ
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hσ
      have := congrArg φ hσ
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, hφt] at this
    · intro hσ
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hφt]
      exact hσ
  have hK := isComponentOf_map_equiv φ hY
  rw [hX] at hK
  have := (CFSG.CGT.Foote82.eq_altOn_of_isComponentOf hR inf_le_right le_rfl hK).2
  rwa [fixed_zpowers_swap01] at this

end Recog

section ThreeCycle

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L : Subgroup (GLV V)} {z : GLV V}

@[expose] def finShift (n : ℕ) : Fin n ≃ {k : Fin (n + 2) // k ≠ 0 ∧ k ≠ 1} where
  toFun k := ⟨Fin.addNat k 2, by simp [Fin.ext_iff], by simp [Fin.ext_iff]⟩
  invFun k := ⟨k.1.val - 2, by
    have h0 : k.1.val ≠ 0 := fun h => k.2.1 (Fin.ext h)
    have h1 : k.1.val ≠ 1 := fun h => k.2.2 (Fin.ext (by rw [h]; simp))
    have := k.1.isLt
    omega⟩
  left_inv k := by
    apply Fin.ext
    simp
  right_inv k := by
    have h0 : k.1.val ≠ 0 := fun h => k.2.1 (Fin.ext h)
    have h1 : k.1.val ≠ 1 := fun h => k.2.2 (Fin.ext (by rw [h]; simp))
    apply Subtype.ext
    apply Fin.ext
    simp only [Fin.coe_addNat]
    omega

theorem extendDomain_mem_altOn {n : ℕ} (σ : alternatingGroup (Fin n)) :
    (σ : Equiv.Perm (Fin n)).extendDomain (finShift n) ∈ altOn {k : Fin (n + 2) | k ≠ 0 ∧ k ≠ 1} := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_extendDomain]
    exact σ.2
  · rw [mem_fixingSubgroup_iff]
    intro k hk
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hk

theorem exists_threeCycle (hc : OddTranspConf G L z) {n : ℕ} (hn : 7 ≤ n)
    (φ : ↥G ≃* Equiv.Perm (Fin (n + 2)))
    (hφL : (L.subgroupOf G).map φ.toMonoidHom = altOn {k | k ≠ 0 ∧ k ≠ 1})
    (α : ↥L →* alternatingGroup (Fin n)) (hα : Function.Injective α)
    (β : ↥(commSpace L ⊤) →+ altHeart n) (hβs : Function.Surjective β)
    (hβk : β.ker = ((fixedSpace L).comap (commSpace L ⊤).subtype).toAddSubgroup)
    (hR : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) (w : V) →
      ∀ x : evenWeight n, β w = (x : altHeart n) →
        β w' = (evenWeightPerm (α ℓ : Equiv.Perm (Fin n)) x : altHeart n)) :
    ∃ c : Equiv.Perm (Fin (n + 2)), c.IsThreeCycle ∧ c 0 = 0 ∧ c 1 = 1 ∧
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers ((φ.symm c : ↥G) : GLV V)) ⊤) = 2 := by
  have hmem₂ : ∀ c ∈ altOn {k : Fin (n + 2) | k ≠ 0 ∧ k ≠ 1}, ((φ.symm c : ↥G) : GLV V) ∈ L := by
    intro c hc
    rw [← hφL, Subgroup.mem_map_equiv] at hc
    exact hc
  let ψf : alternatingGroup (Fin n) → alternatingGroup (Fin n) := fun σ =>
    α ⟨_, hmem₂ _ (extendDomain_mem_altOn σ)⟩
  have ψ_mul : ∀ σ τ, ψf (σ * τ) = ψf σ * ψf τ := by
    intro σ τ
    simp only [ψf, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← Equiv.Perm.extendDomain_mul, map_mul]
  let ψ : alternatingGroup (Fin n) →* alternatingGroup (Fin n) := MonoidHom.mk' ψf ψ_mul
  have hψi : Function.Injective ψ := by
    intro σ τ hστ
    have h1 := hα hστ
    have h1' := congrArg Subtype.val h1
    have h2 : φ.symm ((σ : Equiv.Perm (Fin n)).extendDomain (finShift n)) =
        φ.symm ((τ : Equiv.Perm (Fin n)).extendDomain (finShift n)) :=
      Subtype.ext h1'
    exact Subtype.ext (Equiv.Perm.extendDomainHom_injective (finShift n) (φ.symm.injective h2))
  have hψb : Function.Bijective ψ := Finite.injective_iff_bijective.1 hψi
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
    (by omega) (by omega)).2 (MulEquiv.ofBijective ψ hψb)
  have hψπ : ∀ σ, ((ψ σ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = π * σ * π⁻¹ := by
    intro σ
    have := congrArg (fun F : MulAut (alternatingGroup (Fin n)) =>
      ((F σ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))) hπ
    simp only [MulAut.conjNormal_apply, MulEquiv.ofBijective_apply] at this
    exact this.symm
  have hn4 : 4 ≤ n := by omega
  have h3 := sigma0_isThreeCycle hn4
  have hσ'mem : π⁻¹ * sigma0 hn4 * π ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul,
      Equiv.Perm.mem_alternatingGroup.1 h3.mem_alternatingGroup, mul_one, map_inv,
      inv_mul_cancel]
  let σ' : alternatingGroup (Fin n) := ⟨π⁻¹ * sigma0 hn4 * π, hσ'mem⟩
  have hψσ' : ((ψ σ' : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = sigma0 hn4 := by
    rw [hψπ]
    show π * (π⁻¹ * sigma0 hn4 * π) * π⁻¹ = sigma0 hn4
    group
  refine ⟨(σ' : Equiv.Perm (Fin n)).extendDomain (finShift n), ?_, ?_, ?_, ?_⟩
  · show Equiv.Perm.cycleType _ = {3}
    rw [Equiv.Perm.cycleType_extendDomain]
    show (π⁻¹ * sigma0 hn4 * π).cycleType = {3}
    have := Equiv.Perm.cycleType_conj (σ := sigma0 hn4) (τ := π⁻¹)
    rw [inv_inv] at this
    rw [this]
    exact h3
  · exact Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp)
  · exact Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp)
  · set c := (σ' : Equiv.Perm (Fin n)).extendDomain (finShift n) with hcdef
    have hxL : ((φ.symm c : ↥G) : GLV V) ∈ L := hmem₂ c (extendDomain_mem_altOn σ')
    have hαx : ((α ⟨_, hxL⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = sigma0 hn4 :=
      hψσ'
    have hc3 : c ^ 3 = 1 := by
      have hco : c.IsThreeCycle := by
        show Equiv.Perm.cycleType _ = {3}
        rw [Equiv.Perm.cycleType_extendDomain]
        show (π⁻¹ * sigma0 hn4 * π).cycleType = {3}
        have := Equiv.Perm.cycleType_conj (σ := sigma0 hn4) (τ := π⁻¹)
        rw [inv_inv] at this
        rw [this]
        exact h3
      rw [← hco.orderOf]
      exact pow_orderOf_eq_one c
    have hx3 : ((φ.symm c : ↥G) : GLV V) ^ 3 = 1 := by
      have : (φ.symm c) ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
      have := congrArg Subtype.val this
      simpa using this
    refine finrank_commSpace_eq_two hn4 β hβs hβk hxL hx3 ?_
    intro w w' hw y hy
    have := hR ⟨_, hxL⟩ w w' hw y hy
    rwa [hαx] at this

theorem layerIn_eq_comap (hc : OddTranspConf G L z) {N : ℕ} (hN : 5 ≤ N)
    (φ : ↥G ≃* Equiv.Perm (Fin N)) :
    ((alternatingGroup (Fin N)).comap φ.toMonoidHom).map G.subtype = layerIn G := by
  rw [← hc.derived, ← alternatingGroup.commutator_perm_eq (by simpa using hN),
    _root_.commutator_def, Subgroup.comap_equiv_eq_map_symm', Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ φ.symm.surjective, ← _root_.commutator_def,
    _root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]

end ThreeCycle

end CFSG.CGT.Foote82.BranchAAux
