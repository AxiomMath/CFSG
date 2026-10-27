module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainRoots

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open scoped Pointwise

section General

variable {X : Type*} [Group X]

theorem eq_map_conj_inv_of_map_conj_eq {H Y : Subgroup X} {a : X}
    (h : H.map (MulAut.conj a).toMonoidHom = Y) : H = Y.map (MulAut.conj a⁻¹).toMonoidHom := by
  rw [← h, map_conj_map_conj_eq_map_conj_mul, inv_mul_cancel, map_one]
  exact (Subgroup.map_id H).symm

theorem mem_normalizer_sup_of_mem_mem {A B : Subgroup X} {g : X}
    (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem mem_normalizer_inf_of_mem_mem {A B : Subgroup X} {g : X}
    (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro h
  simp only [mem_inf] at hA hB ⊢
  rw [hA h, hB h]

theorem le_of_isPGroup_of_le_normalizer_sup {p : ℕ} [Fact p.Prime] {Q M N : Subgroup X}
    (hQ : IsPGroup p Q) (hMQ : M ≤ normalizer (Q : Set X))
    (hM : ∀ P : Subgroup M, P.Normal → IsPGroup p P → P = ⊥) (hN : IsPGroup p N)
    (hNle : N ≤ Q ⊔ M) (hNnorm : Q ⊔ M ≤ normalizer (N : Set X)) : N ≤ Q := by
  have hQMQ : Q ⊔ M ≤ normalizer (Q : Set X) := sup_le le_normalizer hMQ
  have hNQ : IsPGroup p (N ⊔ Q : Subgroup X) :=
    hN.to_sup_of_normal_right' hQ (hNle.trans hQMQ)
  set P : Subgroup X := (N ⊔ Q) ⊓ M with hPdef
  have hPM : P ≤ M := inf_le_right
  have hMP : M ≤ normalizer (P : Set X) := fun m hm =>
    mem_normalizer_inf_of_mem_mem
      (mem_normalizer_sup_of_mem_mem (hNnorm (mem_sup_right hm)) (hMQ hm))
      (le_normalizer hm)
  have hPnormal : (P.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hPM).2 hMP
  have hPp : IsPGroup p (P.subgroupOf M) := (hNQ.to_le inf_le_left).comap_subtype
  have hPbot := hM _ hPnormal hPp
  have hle : N ⊔ Q ≤ Q := by
    intro x hx
    have hxQM : x ∈ ((Q ⊔ M : Subgroup X) : Set X) := sup_le hNle le_sup_left hx
    rw [coe_mul_of_right_le_normalizer_left Q M hMQ] at hxQM
    obtain ⟨q, hq, m, hm, hqm⟩ := hxQM
    have hq' : q ∈ Q := hq
    have hm' : m ∈ M := hm
    have hqm' : q * m = x := hqm
    have hmP : m ∈ P := by
      refine ⟨?_, hm'⟩
      have e : m = q⁻¹ * x := by rw [← hqm']; group
      rw [e]
      have h1 : q ∈ (N ⊔ Q : Subgroup X) := Subgroup.mem_sup_right hq'
      exact (N ⊔ Q).mul_mem ((N ⊔ Q).inv_mem h1) hx
    have hm1 : m = 1 := by
      have h1 : (⟨m, hm'⟩ : M) ∈ P.subgroupOf M := hmP
      rw [hPbot] at h1
      exact congrArg Subtype.val ((mem_bot).1 h1)
    rw [← hqm', hm1, mul_one]
    exact hq'
  exact le_sup_left.trans hle

theorem exists_mulEquiv_of_map_subgroupOf_eq [Finite X] {Q M C : Subgroup X}
    (hC : Q ⊔ M = C) (hMQ : M ≤ normalizer (Q : Set X)) (hQM : Q ⊓ M = ⊥) (θ : C ≃* C)
    (hθQ : (Q.subgroupOf C).map θ.toMonoidHom = Q.subgroupOf C) :
    ∃ ι : M ≃* M, ∀ (m : M) (hm : (m : X) ∈ C),
      ((ι m : M) : X)⁻¹ * (θ ⟨m, hm⟩ : X) ∈ Q := by
  have hQC : Q ≤ C := hC ▸ le_sup_left
  have hMC : M ≤ C := hC ▸ le_sup_right
  have hCN : C ≤ normalizer (Q : Set X) := hC ▸ sup_le le_normalizer hMQ
  set Q' : Subgroup C := Q.subgroupOf C with hQ'def
  have : Q'.Normal := (normal_subgroupOf_iff_le_normalizer hQC).2 hCN
  set ε : M →* C ⧸ Q' := (QuotientGroup.mk' Q').comp (Subgroup.inclusion hMC) with hεdef
  have hε : ∀ m : M, ε m = ((Subgroup.inclusion hMC m : C) : C ⧸ Q') := fun m => rfl
  have hεinj : Function.Injective ε := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h1 : Subgroup.inclusion hMC m ∈ Q' := (QuotientGroup.eq_one_iff _).1 hm
    have h2 : (m : X) ∈ Q ⊓ M := ⟨h1, m.2⟩
    rw [hQM, mem_bot] at h2
    exact Subtype.ext h2
  have hεsurj : Function.Surjective ε := by
    intro y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective Q' y
    have hc : (c : X) ∈ ((Q ⊔ M : Subgroup X) : Set X) := by rw [hC]; exact c.2
    rw [coe_mul_of_right_le_normalizer_left Q M hMQ] at hc
    obtain ⟨q, hq, m, hm, hqm⟩ := hc
    have hq' : q ∈ Q := hq
    have hm' : m ∈ M := hm
    have hqm' : q * m = c := hqm
    refine ⟨⟨m, hm'⟩, ?_⟩
    rw [hε, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    have h1 := (mem_normalizer_iff.1 (hMQ (inv_mem hm')) q).1 hq'
    have e : (((Subgroup.inclusion hMC ⟨m, hm'⟩)⁻¹ * c : C) : X) = m⁻¹ * q * m⁻¹⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, ← hqm', inv_inv]
      group
    rw [e]
    exact h1
  set εe : M ≃* C ⧸ Q' := MulEquiv.ofBijective ε ⟨hεinj, hεsurj⟩ with hεe
  set ι₀ : M →* M := εe.symm.toMonoidHom.comp
    ((QuotientGroup.mk' Q').comp (θ.toMonoidHom.comp (Subgroup.inclusion hMC))) with hι₀def
  have hι₀ : ∀ m : M, ε (ι₀ m) = ((θ (Subgroup.inclusion hMC m) : C) : C ⧸ Q') := fun m =>
    εe.apply_symm_apply _
  have hι₀inj : Function.Injective ι₀ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h1 : ((θ (Subgroup.inclusion hMC m) : C) : C ⧸ Q') = 1 := by rw [← hι₀, hm, map_one]
    have h2 : θ (Subgroup.inclusion hMC m) ∈ Q' := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : θ (Subgroup.inclusion hMC m) ∈ Q'.map θ.toMonoidHom := by rw [hθQ]; exact h2
    obtain ⟨y, hy, hyeq⟩ := h3
    have h4 : y = Subgroup.inclusion hMC m := θ.injective hyeq
    rw [h4] at hy
    have h5 : (m : X) ∈ Q ⊓ M := ⟨hy, m.2⟩
    rw [hQM, mem_bot] at h5
    exact Subtype.ext h5
  refine ⟨MulEquiv.ofBijective ι₀ ⟨hι₀inj, Finite.injective_iff_surjective.1 hι₀inj⟩,
    fun m hm => ?_⟩
  have h1 := hι₀ m
  rw [hε, QuotientGroup.eq, mem_subgroupOf] at h1
  have h2 : ((ι₀ m : M) : X)⁻¹ * (θ (Subgroup.inclusion hMC m) : X) ∈ Q := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] using h1
  exact h2

end General

section RootZ3


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem exists_conj_eq_of_le_rootSL2 (hK : Nat.card K = 2) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ rootSL2 K rootR) (hX₀ : Nat.card X₀ = 3) {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) {Y : Subgroup (adjointGroup .F4 K)} (hYJ : Y ≤ rootSL2 K γ)
    (hY : Nat.card Y = 3) :
    ∃ c : adjointGroup .F4 K, Y = X₀.map (MulAut.conj c).toMonoidHom ∨
      Y = (X₀.map (graphAutF4 K).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
  have hcφ : Nat.card (X₀.map (graphAutF4 K).toMonoidHom) = 3 := by
    rw [card_map_of_injective (f := (graphAutF4 K).toMonoidHom) (graphAutF4 K).injective, hX₀]
  rcases iform_self_eq_two_or_four hγ with hs | hl
  · obtain ⟨w, hw⟩ := exists_smul_eq_rootS hγ hs
    have h1 : Y.map (MulAut.conj (weylRepC K w)).toMonoidHom ≤ rootSL2 K rootS := by
      rw [← hw, ← map_conj_weylRepC_rootSL2 w hγ]
      exact map_mono hYJ
    have h2 : X₀.map (graphAutF4 K).toMonoidHom ≤ rootSL2 K rootS := by
      rw [← map_graphAutF4_rootSL2R]
      exact map_mono hXJ
    have hc1 : Nat.card (Y.map (MulAut.conj (weylRepC K w)).toMonoidHom) = 3 := by
      rw [card_map_of_injective (MulAut.conj (weylRepC K w)).injective, hY]
    have h3 : Y.map (MulAut.conj (weylRepC K w)).toMonoidHom =
        X₀.map (graphAutF4 K).toMonoidHom := by
      have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
      exact eq_of_le_rootSL2 hK isRoot_rootS h1 h2 hc1 hcφ
    exact ⟨(weylRepC K w)⁻¹, Or.inr (eq_map_conj_inv_of_map_conj_eq h3)⟩
  · obtain ⟨w, hw⟩ := exists_smul_eq_rootR hγ hl
    have h1 : Y.map (MulAut.conj (weylRepC K w)).toMonoidHom ≤ rootSL2 K rootR := by
      rw [← hw, ← map_conj_weylRepC_rootSL2 w hγ]
      exact map_mono hYJ
    have hc1 : Nat.card (Y.map (MulAut.conj (weylRepC K w)).toMonoidHom) = 3 := by
      rw [card_map_of_injective (MulAut.conj (weylRepC K w)).injective, hY]
    have h3 : Y.map (MulAut.conj (weylRepC K w)).toMonoidHom = X₀ := by
      have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
      exact eq_of_le_rootSL2 hK isRoot_rootR h1 hXJ hc1 hX₀
    exact ⟨(weylRepC K w)⁻¹, Or.inl (eq_map_conj_inv_of_map_conj_eq h3)⟩

theorem exists_conj_eq_of_le_mem_leviRootSL2s (hK : Nat.card K = 2)
    {X₀ : Subgroup (adjointGroup .F4 K)} (hXJ : X₀ ≤ rootSL2 K rootR) (hX₀ : Nat.card X₀ = 3)
    {κ : TwoCentral} {J Y : Subgroup (adjointGroup .F4 K)} (hJ : J ∈ leviRootSL2s K κ)
    (hYJ : Y ≤ J) (hY : Nat.card Y = 3) :
    ∃ c : adjointGroup .F4 K, Y = X₀.map (MulAut.conj c).toMonoidHom ∨
      Y = (X₀.map (graphAutF4 K).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨γ, hγ, m, -, rfl⟩ := hJ
  obtain ⟨Y', hY'J, rfl⟩ := exists_le_map_eq_of_le_map (MulAut.conj m) hYJ
  have hY' : Nat.card Y' = 3 := by
    rw [← hY, card_map_of_injective (MulAut.conj m).injective]
  obtain ⟨c, h | h⟩ := exists_conj_eq_of_le_rootSL2 hK hXJ hX₀ hγ.1 hY'J hY'
  · exact ⟨m * c, Or.inl (by rw [h, map_conj_map_conj_eq_map_conj_mul])⟩
  · exact ⟨m * c, Or.inr (by rw [h, map_conj_map_conj_eq_map_conj_mul])⟩

theorem isSimpleGroup_levi_of_ne_tu {κ : TwoCentral} (hκ : κ ≠ .tu) :
    IsSimpleGroup (levi K κ) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have := isSimpleGroup_C3Levi (K := K)
  cases κ
  · exact ((leviModelT K).equiv.symm.trans (c3LeviEquiv K)).isSimpleGroup
  · exact ((leviModelU K).equiv.symm.trans (c3LeviEquiv K)).isSimpleGroup
  · exact absurd rfl hκ

theorem exists_conj_of_mulEquiv_of_decomp (hK : Nat.card K = 2) {κ : TwoCentral}
    (hκ : κ ≠ .tu) {X₀ : Subgroup (adjointGroup .F4 K)} (hXJ : X₀ ≤ rootSL2 K rootR)
    (hX₀ : Nat.card X₀ = 3) {C Q : Subgroup (adjointGroup .F4 K)} (hQp : IsPGroup 2 Q)
    (hQM : Q ⊔ levi K κ = C) (hinf : Q ⊓ levi K κ = ⊥)
    (hMQ : levi K κ ≤ normalizer (Q : Set (adjointGroup .F4 K))) (hperf : ⁅C, C⁆ = C)
    (θ : C ≃* C) :
    ∃ c : adjointGroup .F4 K,
      ((X₀.subgroupOf C).map θ.toMonoidHom).map C.subtype = X₀.map (MulAut.conj c).toMonoidHom ∨
      ((X₀.subgroupOf C).map θ.toMonoidHom).map C.subtype =
        (X₀.map (graphAutF4 K).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
  have := finite_adjointGroup_F4 (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF5 : FactF5 K := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact factF5 K
  have hsimple := isSimpleGroup_levi_of_ne_tu (K := K) hκ
  have hperf' : ⁅Q ⊔ levi K κ, Q ⊔ levi K κ⁆ = Q ⊔ levi K κ := by
    rw [hQM]
    exact hperf
  have hO2 := EPilot.forall_normal_isPGroup_eq_bot_of_isSimpleGroup_of_perfect hQp hMQ hsimple
    hperf'
  have hQC : Q ≤ C := hQM ▸ le_sup_left
  have hMC : levi K κ ≤ C := hQM ▸ le_sup_right
  have hθQC : ((Q.subgroupOf C).map θ.toMonoidHom).map C.subtype ≤ C := map_subtype_le _
  have hθQsub : (((Q.subgroupOf C).map θ.toMonoidHom).map C.subtype).subgroupOf C =
      (Q.subgroupOf C).map θ.toMonoidHom :=
    comap_map_eq_self_of_injective C.subtype_injective _
  have hQn : (Q.subgroupOf C).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQC).2 (hQM ▸ sup_le le_normalizer hMQ)
  have hθQn : ((((Q.subgroupOf C).map θ.toMonoidHom).map C.subtype).subgroupOf C).Normal := by
    rw [hθQsub]
    exact hQn.map θ.toMonoidHom θ.surjective
  have hθQnorm : Q ⊔ levi K κ ≤ normalizer
      ((((Q.subgroupOf C).map θ.toMonoidHom).map C.subtype : Subgroup (adjointGroup .F4 K)) :
        Set (adjointGroup .F4 K)) := by
    rw [hQM]
    exact (normal_subgroupOf_iff_le_normalizer hθQC).1 hθQn
  have hθQp : IsPGroup 2 (((Q.subgroupOf C).map θ.toMonoidHom).map C.subtype) :=
    (hQp.comap_subtype.map θ.toMonoidHom).map C.subtype
  have hθQle : ((Q.subgroupOf C).map θ.toMonoidHom).map C.subtype ≤ Q :=
    le_of_isPGroup_of_le_normalizer_sup hQp hMQ hO2 hθQp (hQM ▸ hθQC) hθQnorm
  have hθQcard : Nat.card (((Q.subgroupOf C).map θ.toMonoidHom).map C.subtype) = Nat.card Q := by
    rw [card_map_of_injective C.subtype_injective, card_map_of_injective θ.injective,
      card_subgroupOf_of_le hQC]
  have hθQeq : ((Q.subgroupOf C).map θ.toMonoidHom).map C.subtype = Q :=
    Subgroup.eq_of_le_of_card_ge hθQle hθQcard.ge
  have hθQ' : (Q.subgroupOf C).map θ.toMonoidHom = Q.subgroupOf C := by rw [← hθQsub, hθQeq]
  obtain ⟨ι, hι⟩ := exists_mulEquiv_of_map_subgroupOf_eq hQM hMQ hinf θ hθQ'
  have hJrM : rootSL2 K rootR ≤ levi K κ := rootSL2_rootR_le_levi κ
  set J' : Subgroup (adjointGroup .F4 K) :=
    (((rootSL2 K rootR).subgroupOf (levi K κ)).map ι.toMonoidHom).map (levi K κ).subtype
    with hJ'def
  have hJ' : J' ∈ leviRootSL2s K κ :=
    hF5 κ κ ι (rootSL2 K rootR) (rootSL2_mem_leviRootSL2s (rootR_mem_phi0 κ))
  have hJ'M : J' ≤ levi K κ := map_subtype_le _
  have hSle : ((X₀.subgroupOf C).map θ.toMonoidHom).map C.subtype ≤ J' ⊔ Q := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxX : (x : adjointGroup .F4 K) ∈ X₀ := hx
    have hxM : (x : adjointGroup .F4 K) ∈ levi K κ := hJrM (hXJ hxX)
    have h1 := hι ⟨x, hxM⟩ x.2
    have hm'J : ((ι ⟨x, hxM⟩ : levi K κ) : adjointGroup .F4 K) ∈ J' :=
      ⟨ι ⟨x, hxM⟩, ⟨⟨x, hxM⟩, mem_subgroupOf.2 (hXJ hxX), rfl⟩, rfl⟩
    have e : ((θ x : C) : adjointGroup .F4 K) =
        ((ι ⟨x, hxM⟩ : levi K κ) : adjointGroup .F4 K) *
          (((ι ⟨x, hxM⟩ : levi K κ) : adjointGroup .F4 K)⁻¹ *
            (θ ⟨(x : adjointGroup .F4 K), x.2⟩ : adjointGroup .F4 K)) := by
      rw [mul_inv_cancel_left]
    change ((θ x : C) : adjointGroup .F4 K) ∈ J' ⊔ Q
    rw [e]
    exact mul_mem (mem_sup_left hm'J) (mem_sup_right h1)
  have hJ'Q : J' ≤ normalizer (Q : Set (adjointGroup .F4 K)) := hJ'M.trans hMQ
  have hQJ' : Q ⊓ J' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ Q ⊓ levi K κ := ⟨hx.1, hJ'M hx.2⟩
    rwa [hinf] at h1
  have hScard : Nat.card (((X₀.subgroupOf C).map θ.toMonoidHom).map C.subtype) = 3 := by
    rw [card_map_of_injective C.subtype_injective, card_map_of_injective θ.injective,
      card_subgroupOf_of_le (hXJ.trans (hJrM.trans hMC)), hX₀]
  obtain ⟨u, -, huS⟩ := exists_mem_map_conj_le_of_le_sup (p := 2) hQp hJ'Q hQJ' hSle
    (by rw [hScard]; norm_num)
  have hY : Nat.card ((((X₀.subgroupOf C).map θ.toMonoidHom).map C.subtype).map
      (MulAut.conj u).toMonoidHom) = 3 := by
    rw [card_map_of_injective (MulAut.conj u).injective, hScard]
  obtain ⟨c, h | h⟩ := exists_conj_eq_of_le_mem_leviRootSL2s hK hXJ hX₀ hJ' huS hY
  · refine ⟨u⁻¹ * c, Or.inl ?_⟩
    rw [eq_map_conj_inv_of_map_conj_eq h, map_conj_map_conj_eq_map_conj_mul]
  · refine ⟨u⁻¹ * c, Or.inr ?_⟩
    rw [eq_map_conj_inv_of_map_conj_eq h, map_conj_map_conj_eq_map_conj_mul]

theorem exists_conj_of_mulEquiv_centralizer_yRep (hK : Nat.card K = 2) {κ : TwoCentral}
    (hκ : κ ≠ .tu) {X₀ : Subgroup (adjointGroup .F4 K)} (hXJ : X₀ ≤ rootSL2 K rootR)
    (hX₀ : Nat.card X₀ = 3)
    (θ : centralizer ({yRep K κ} : Set (adjointGroup .F4 K)) ≃*
      centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) :
    ∃ c : adjointGroup .F4 K,
      ((X₀.subgroupOf (centralizer ({yRep K κ} : Set (adjointGroup .F4 K)))).map
          θ.toMonoidHom).map (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))).subtype =
        X₀.map (MulAut.conj c).toMonoidHom ∨
      ((X₀.subgroupOf (centralizer ({yRep K κ} : Set (adjointGroup .F4 K)))).map
          θ.toMonoidHom).map (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))).subtype =
        (X₀.map (graphAutF4 K).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
  have hF3 : FactF3 K := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact factF3
  have hF3p : FactF3PerfectTwo K := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact factF3PerfectTwo hK
  obtain ⟨Q, hQp, hQM, hinf, hMQ⟩ := hF3 κ
  exact exists_conj_of_mulEquiv_of_decomp hK hκ hXJ hX₀ hQp hQM hinf hMQ (hF3p κ hκ) θ

theorem eq_one_of_mem_centralizer_of_commute_C3Levi (hK : Nat.card K = 2)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) {y : adjointGroup .F4 K}
    (hy : y ∈ centralizer (X₀ : Set (adjointGroup .F4 K))) (hy2 : y * y = 1)
    (hyD : ∀ d ∈ C3Levi K, y * d = d * y) : y = 1 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨hcen, hdisj, hX₀D⟩ := centralizer_nonsplit hXJ hcyc (by rw [hX₀, hK])
  have hDN : C3Levi K ≤ normalizer (X₀ : Set (adjointGroup .F4 K)) :=
    (le_centralizer_iff.1 hX₀D).trans (centralizer_le_normalizer _)
  rw [hcen, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left X₀ (C3Levi K) hDN] at hy
  obtain ⟨x, hx, d, hd, hxd⟩ := hy
  have hx' : x ∈ X₀ := hx
  have hd' : d ∈ C3Levi K := hd
  have hxd' : x * d = y := hxd
  have hcomm : d * x = x * d := mem_centralizer_iff.1 (hX₀D hx') d hd'
  have hx2 : x * x = 1 := by
    have e : x * x = (d * d)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hy2, ← hxd']
      calc x * x * (d * d) = x * (x * d) * d := by group
        _ = x * (d * x) * d := by rw [hcomm]
        _ = x * d * (x * d) := by group
    have hdd : (d * d)⁻¹ ∈ C3Levi K := (C3Levi K).inv_mem ((C3Levi K).mul_mem hd' hd')
    have hmem : x * x ∈ X₀ ⊓ C3Levi K := ⟨X₀.mul_mem hx' hx', e ▸ hdd⟩
    rw [hdisj.eq_bot, mem_bot] at hmem
    exact hmem
  have hx1 : x = 1 := by
    have h3 : orderOf (⟨x, hx'⟩ : X₀) ∣ 3 := hX₀ ▸ orderOf_dvd_natCard _
    have h2 : orderOf (⟨x, hx'⟩ : X₀) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [pow_two]
      exact Subtype.ext hx2)
    have h1 : orderOf (⟨x, hx'⟩ : X₀) = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h2 h3
    exact congrArg Subtype.val (orderOf_eq_one_iff.1 h1)
  have hyd : y = d := by rw [← hxd', hx1, one_mul]
  have hZ : (⟨d, hd'⟩ : C3Levi K) ∈ center (C3Levi K) := mem_center_iff.2 fun g => by
    apply Subtype.ext
    have := hyD g g.2
    rw [hyd] at this
    exact this.symm
  rw [center_C3Levi_eq_bot, mem_bot] at hZ
  rw [hyd]
  exact congrArg Subtype.val hZ

end RootZ3

end CFSG.SeitzReduction.F4Pilot
