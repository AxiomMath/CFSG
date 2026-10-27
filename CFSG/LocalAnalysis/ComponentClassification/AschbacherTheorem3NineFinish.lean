module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3NineQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Multiplier
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCentralCover

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped Pointwise MatrixGroups commutatorElement

variable {X : Type} [Group X] [Finite X]

namespace Core49

variable {A T S Q H : Subgroup X}

theorem not_isPGroup (c : Core49 A T S Q H) : ¬ IsPGroup 2 A := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect A := ⟨c.quasisimple.1⟩
  have : Nontrivial A := Quasisimple.nontrivial c.quasisimple
  exact Group.IsPerfect.not_isNilpotent A h2.isNilpotent

theorem commutator_eq (c : Core49 A T S Q H) : ⁅T, A⁆ = A := by
  have hle : ⁅T, A⁆ ≤ A :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp c.frame.le_normalizer
  have : (⁅T, A⁆.subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_right T A)
  rcases Quasisimple.normal_le_center_or_eq_top c.quasisimple (⁅T, A⁆.subgroupOf A) with
    hZ | htop
  · exfalso
    have : Group.IsPerfect A := ⟨c.quasisimple.1⟩
    have hdouble : ⁅⁅A, T⁆, A⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.commutator_comm] at hx
      have hxZ := hZ (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hle hx⟩ : A) ∈ ⁅T, A⁆.subgroupOf A)
      refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨a, ha⟩)
    have hAT : A ≤ Subgroup.centralizer (T : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (Quasisimple.perfect_double_commutator A T hdouble)
    apply c.R_not_le
    intro r hr
    obtain ⟨k, hk⟩ := c.isPGroup_S ⟨r, hr.1⟩
    exact c.none r hr.2 ⟨k, congrArg Subtype.val hk⟩ (hAT hr.2)
  · apply le_antisymm hle
    intro a ha
    have : (⟨a, ha⟩ : A) ∈ ⁅T, A⁆.subgroupOf A := htop ▸ Subgroup.mem_top _
    exact this

omit [Finite X] in
theorem card_le_two_of_isCyclic {G : Type*} [Group G] [IsCyclic G] (h : ∀ g : G, g ^ 2 = 1) :
    Nat.card G ≤ 2 := by
  have hexp : Monoid.exponent G ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one h
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd two_pos hexp

variable {N : Subgroup X} [N.Normal]

theorem false_of_mulEquiv (c : Core49 A T S Q H)
    (hN : N = S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) {n : ℕ} (hn : 2 ≤ n)
    (e : A.map (QuotientGroup.mk' N) ≃* PSL(2, GaloisField 2 n)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect A := ⟨c.quasisimple.1⟩
  set π := QuotientGroup.mk' N
  set ψ : A →* PSL(2, GaloisField 2 n) := e.toMonoidHom.comp (π.subgroupMap A) with hψ
  have hψs : Function.Surjective ψ := e.surjective.comp (π.subgroupMap_surjective A)
  have hker : ψ.ker = N.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change e (π.subgroupMap A x) = 1 ↔ _
    rw [e.map_eq_one_iff, Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  have hcentral : ψ.ker ≤ Subgroup.center A := by
    rw [hker]
    intro x hx
    rw [Subgroup.mem_subgroupOf, hN] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (c.U_le_center hx).2 g g.2)
  have hp : IsPGroup 2 ψ.ker := by
    rw [hker]
    intro x
    have hx : ((x : A) : X) ∈ S ⊓ A ⊓ Subgroup.centralizer (T : Set X) := hN.le x.2
    obtain ⟨k, hk⟩ := c.isPGroup_S ⟨_, hx.1.1⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact congrArg Subtype.val hk
  obtain ⟨hTel, φ, hφinj, hφU⟩ := c.elem_and_embedding
  have hφA : ∀ t : T, φ t ∈ A := fun t => (hφU t).1.2
  have hφK : ∀ t : T, (⟨φ t, hφA t⟩ : A) ∈ ψ.ker := fun t => by
    rw [hker, Subgroup.mem_subgroupOf, hN]
    exact hφU t
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  ·
    set P : Sylow 2 A := default
    set V := P.mapSurjective hψs
    obtain ⟨hVel, hVcard⟩ := CFSG.Walter.psl2_even_sylow_two (le_refl 2) V
    have hVcomm := hVel.toIsMulCommutative
    have h4 : 4 ≤ Nat.card (V : Subgroup PSL(2, GaloisField 2 2)) := by rw [hVcard]; norm_num
    obtain ⟨u, hu, v, hv, hu1, hv1, hvu⟩ := exists_two_ne_one h4
    have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian u hu
    have hv2 : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian v hv
    have huv : u * v = v * u := congrArg Subtype.val (hVcomm.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    obtain ⟨hcard4, -⟩ := exists_four_of_involutions hu2 hv2 hu1 hv1 (Ne.symm hvu) huv
    have hVeq : Subgroup.zpowers u ⊔ Subgroup.zpowers v = (V : Subgroup _) :=
      Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hu)
        (Subgroup.zpowers_le.mpr hv)) (by rw [hcard4, hVcard]; norm_num)
    have hVmap : (V : Subgroup PSL(2, GaloisField 2 2)) = (P : Subgroup A).map ψ :=
      Sylow.coe_mapSurjective _ _
    obtain ⟨x, hx, rfl⟩ : u ∈ (P : Subgroup A).map ψ := hVmap ▸ hu
    obtain ⟨y, hy, rfl⟩ : v ∈ (P : Subgroup A).map ψ := hVmap ▸ hv
    have hgen : (P : Subgroup A) ≤ Subgroup.closure {x, y} ⊔ ψ.ker := by
      intro p hp
      have hpV : ψ p ∈ (V : Subgroup PSL(2, GaloisField 2 2)) :=
        hVmap ▸ Subgroup.mem_map_of_mem ψ hp
      rw [← hVeq, ← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, ← Subgroup.map_sup] at hpV
      obtain ⟨q, hq, hqp⟩ := hpV
      have hqk : q⁻¹ * p ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hqp, inv_mul_cancel]
      have hqcl : q ∈ Subgroup.closure {x, y} :=
        (sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
          (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))) hq
      have hpq : p = q * (q⁻¹ * p) := by group
      rw [hpq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hqcl) (Subgroup.mem_sup_right hqk)
    have hab : ∀ a ∈ (P : Subgroup A), ∀ b ∈ (P : Subgroup A), ⁅a, b⁆ ∈ ψ.ker := by
      intro a ha b hb
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      have ha' : ψ a ∈ (V : Subgroup PSL(2, GaloisField 2 2)) :=
        hVmap ▸ Subgroup.mem_map_of_mem ψ ha
      have hb' : ψ b ∈ (V : Subgroup PSL(2, GaloisField 2 2)) :=
        hVmap ▸ Subgroup.mem_map_of_mem ψ hb
      exact congrArg Subtype.val (hVcomm.is_comm.comm ⟨ψ a, ha'⟩ ⟨ψ b, hb'⟩)
    have : IsCyclic ψ.ker := central_two_kernel_cyclic_of_sylow_two_generated c.quasisimple.1
      hcentral hp P hx hy hgen hab
    let θ : T →* ψ.ker :=
      { toFun := fun t => ⟨⟨φ t, hφA t⟩, hφK t⟩
        map_one' := Subtype.ext (Subtype.ext (map_one φ))
        map_mul' := fun a b => Subtype.ext (Subtype.ext (map_mul φ a b)) }
    have hθinj : Function.Injective θ := fun a b hab =>
      hφinj (congrArg (fun z : ψ.ker => ((z : A) : X)) hab)
    have : IsCyclic T := isCyclic_of_injective θ hθinj
    have h1 := card_le_two_of_isCyclic (G := T) fun t => Subtype.ext (hTel.2 _ t.2)
    rw [card_eq_two_pow_pRank hTel] at h1
    have h2 : 2 ^ 2 ≤ 2 ^ pRank 2 T := Nat.pow_le_pow_right two_pos c.pRank_lt
    omega
  ·
    set η := (CFSG.ShultStronglyClosedTI.linearCover_pslEquivSL
      (K := GaloisField 2 n)).toMonoidHom.comp ψ
    have hηker : η.ker = ψ.ker := by
      ext x
      exact CFSG.ShultStronglyClosedTI.linearCover_pslEquivSL.map_eq_one_iff
    have hbot := CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_kernel_eq_bot n
      hn3 (GaloisField.card 2 n (by omega)) η
      (CFSG.ShultStronglyClosedTI.linearCover_pslEquivSL.surjective.comp hψs)
      (by rw [hηker]; exact hcentral) (by rw [hηker]; exact hp)
    rw [hηker] at hbot
    apply c.ne_bot
    rw [eq_bot_iff]
    intro t ht
    have h2 := hφK ⟨t, ht⟩
    rw [hbot, Subgroup.mem_bot] at h2
    have h3 : φ ⟨t, ht⟩ = φ 1 := by
      rw [map_one]
      exact congrArg Subtype.val h2
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hφinj h3))

theorem false (c : Core49 A T S Q H) (h48 : Theorem48Statement) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := S ⊓ A ⊓ Subgroup.centralizer (T : Set X) with hU
  have : U.Normal := c.U_normal
  set π := QuotientGroup.mk' U
  obtain ⟨S', hS'⟩ := (c.frame_quotient (N := U) rfl).exists_sylowFrame
  rcases h48 (X ⧸ U) (A.map π) (T.map π) S' _ _ hS' (c.hyp43_quotient rfl)
      (c.relIndex_quotient_le rfl hS') (c.oddCore_quotient rfl) (c.pRank_quotient rfl) with
    hW | ⟨n, hn, -, -, -, -, -, ⟨e⟩⟩
  ·
    apply c.not_isPGroup
    set W := relativeWeakClosure (A.map π) (T.map π) S'
    have hTW : T.map π ≤ W := subgroup_le_relative_weak_closure _ _ _ hS'.le
    have hWS : W ≤ S' := relative_weak_closure_le _ _ _
    have hAW : A.map π ≤ W := by
      have h1 : ⁅A.map π, W⁆ ≤ W := Subgroup.le_normalizer_iff_commutator_le_right.mp hW
      calc A.map π = (⁅T, A⁆ : Subgroup X).map π := by rw [c.commutator_eq]
        _ = ⁅T.map π, A.map π⁆ := by rw [Subgroup.map_commutator]
        _ ≤ ⁅W, A.map π⁆ := Subgroup.commutator_mono hTW le_rfl
        _ = ⁅A.map π, W⁆ := Subgroup.commutator_comm _ _
        _ ≤ W := h1
    intro a
    obtain ⟨k, hk⟩ := hS'.sylow.isPGroup ⟨π a, hWS (hAW (Subgroup.mem_map_of_mem π a.2))⟩
    have hk' : π ((a : X) ^ (2 ^ k)) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have hmem : (a : X) ^ (2 ^ k) ∈ U := (QuotientGroup.eq_one_iff _).mp hk'
    obtain ⟨j, hj⟩ := c.isPGroup_S ⟨_, hmem.1.1⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_add, pow_mul]
    exact congrArg Subtype.val hj
  ·
    have hcomm : ⁅T.map π, A.map π⁆ = A.map π := by
      rw [← Subgroup.map_commutator, c.commutator_eq]
    exact c.false_of_mulEquiv rfl hn ((MulEquiv.subgroupCongr hcomm).symm.trans e)

end Core49

end CFSG.ComponentClassification.AschbacherTheorem3
