module

public import CFSG.GH74.GLS.Stage1.Main.BrG2AsmT
public import CFSG.GH74.GLS.Stage1.Main.BrG2NotInner

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.IVK.Lifted

open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Main

section R3

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.r3_data (hcen : Cen2 G z S) (h3 : Nat.card C.F₂ = 3) :
    Group.IsSolvable ↥(centralizer (C.K₁ : Set (CentralizerBar z))) ∧
    ∃ P : Subgroup (CentralizerBar z), P ≤ C.K₂ ∧ IVK.IsQuaternionTwoGroup ↥P 3 ∧
      (∀ x ∈ C.K₂, (∃ m : ℕ, x ^ (2 ^ m) = 1) → x ∈ P) ∧
      fittingSubgroup ↥(centralizer (C.K₁ : Set (CentralizerBar z))) =
        P.subgroupOf (centralizer (C.K₁ : Set (CentralizerBar z))) := by
  obtain ⟨ζ, hζ₁, hζ₂, hζo, -, hT⟩ := C.exists_zeta hcen
  set D := centralizer (C.K₁ : Set (CentralizerBar z)) with hD
  have hK₂D : C.K₂ ≤ D := fun b hb => by
    rw [hD, Subgroup.mem_centralizer_iff]
    intro a ha
    exact C.comm a ha b hb
  have hnormal : (C.K₂.subgroupOf D).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgN : (g : CentralizerBar z) ∈ normalizer (C.K₁ : Set (CentralizerBar z)) := by
      apply Subgroup.centralizer_le_normalizer
      exact g.2
    exact C.conj_K₂ hcen hgN hn
  have hC : ∀ d : ↥D, (∀ k ∈ C.K₂.subgroupOf D, k * d = d * k) → d ∈ C.K₂.subgroupOf D := by
    intro d hd
    have hcomm : ∀ l ∈ C.K₁ ⊔ C.K₂, l * (d : CentralizerBar z) = (d : CentralizerBar z) * l := by
      intro l hl
      obtain ⟨a, ha, b, hb, rfl⟩ := y_mem_sup_of_commute C.comm hl
      have h1 : a * (d : CentralizerBar z) = (d : CentralizerBar z) * a :=
        Subgroup.mem_centralizer_iff.1 d.2 a ha
      have h2 : b * (d : CentralizerBar z) = (d : CentralizerBar z) * b :=
        congrArg Subtype.val (hd ⟨b, hK₂D hb⟩ hb)
      calc a * b * (d : CentralizerBar z) = a * (b * d) := by rw [mul_assoc]
        _ = a * (d * b) := by rw [h2]
        _ = (a * d) * b := by rw [mul_assoc]
        _ = (d * a) * b := by rw [h1]
        _ = d * (a * b) := by rw [mul_assoc]
    have h := C.centralizer_K hcen hζ₁ hζ₂ hζo hT (d : CentralizerBar z) hcomm
    rw [Subgroup.mem_subgroupOf]
    rcases h with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hζ₂
  have e : ↥(C.K₂.subgroupOf D) ≃* StatedSL 2 C.F₂ :=
    (Subgroup.subgroupOfEquivOfLe hK₂D).trans C.e₂
  obtain ⟨hsolv, P', hP'K, hP'n, hP'q, hF, hP'2⟩ := sl2_three_overgroup hnormal h3 e hC
  refine ⟨hsolv, P'.map D.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hP'K hx
  · obtain ⟨h3', ⟨eq⟩⟩ := hP'q
    exact ⟨h3', ⟨(Subgroup.equivMapOfInjective P' D.subtype D.subtype_injective).symm.trans eq⟩⟩
  · intro x hx ⟨m, hm⟩
    have hxD : x ∈ D := hK₂D hx
    have hmem : (⟨x, hxD⟩ : ↥D) ∈ P' := by
      apply hP'2 ⟨x, hxD⟩ hx
      exact ⟨m, Subtype.ext (by simpa using hm)⟩
    exact ⟨⟨x, hxD⟩, hmem, rfl⟩
  · rw [hF]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [← this]

end R3

section R3b

theorem g2_not_solvable_of_quasisimple {Q : Type} [Group Q] (hQ : IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  have := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have := hQ.1
  exact Group.IsPerfect.not_isSolvable Q

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.r3_comps (hcen : Cen2 G z S) (h3 : Nat.card C.F₂ = 3) :
    {K : Subgroup (CentralizerBar z) | IsComponent K} = {C.K₁} := by
  obtain ⟨hsolv, -⟩ := C.r3_data hcen h3
  have hc₁ : IsComponent C.K₁ :=
    ⟨C.quasi₁, isSubnormal_of_comm_normal C.comm (C.normal_K hcen)⟩
  ext K
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hK
    by_contra hne
    have hcomm := (CFSG.LocalCores.distinct_components_commute hK hc₁).resolve_left hne
    have hKD : K ≤ centralizer (C.K₁ : Set (CentralizerBar z)) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hmem : ⁅k, a⁆ ∈ ⁅K, C.K₁⁆ := Subgroup.commutator_mem_commutator hk ha
      rw [hcomm] at hmem
      have h1 : ⁅k, a⁆ = 1 := by simpa using hmem
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    have := hsolv
    have hKs : Group.IsSolvable ↥K :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKD)
    exact g2_not_solvable_of_quasisimple hK.1 hKs
  · rintro rfl
    exact hc₁

include C in
theorem G2Ctx.r3_K₁_normal (hcen : Cen2 G z S) (h3 : Nat.card C.F₂ = 3) : C.K₁.Normal := by
  have hc₁ : IsComponent C.K₁ :=
    ⟨C.quasi₁, isSubnormal_of_comm_normal C.comm (C.normal_K hcen)⟩
  constructor
  intro n hn g
  have hconj : IsComponent (C.K₁.map (MulAut.conj g).toMonoidHom) :=
    isComponent_map_of_isComponent (MulAut.conj g) hc₁
  have hmem : C.K₁.map (MulAut.conj g).toMonoidHom ∈ {K | IsComponent K} := hconj
  rw [C.r3_comps hcen h3] at hmem
  have h2 : g * n * g⁻¹ ∈ C.K₁.map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
  rwa [Set.mem_singleton_iff.1 hmem] at h2

end R3b

section QuatP

theorem quat_isPGroup {Y : Type} [Group Y] {P : Subgroup Y} {m : ℕ}
    (hq : IVK.IsQuaternionTwoGroup ↥P m) : IsPGroup 2 ↥P := by
  obtain ⟨h3, ⟨e⟩⟩ := hq
  have hne : NeZero (2 ^ (m - 2)) := ⟨by positivity⟩
  apply IsPGroup.of_card (n := m)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have : 2 ^ m = 4 * 2 ^ (m - 2) := by
    have : m = (m - 2) + 2 := by omega
    conv_lhs => rw [this]
    rw [pow_add]; ring
  omega

end QuatP

section R3c

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.r3_fitting (hcen : Cen2 G z S) (h3 : Nat.card C.F₂ = 3) {P : Subgroup (CentralizerBar z)}
    (hPK : P ≤ C.K₂) (hq : IVK.IsQuaternionTwoGroup ↥P 3)
    (h2el : ∀ x ∈ C.K₂, (∃ m : ℕ, x ^ (2 ^ m) = 1) → x ∈ P)
    (hF : fittingSubgroup ↥(centralizer (C.K₁ : Set (CentralizerBar z))) =
      P.subgroupOf (centralizer (C.K₁ : Set (CentralizerBar z)))) :
    P.Normal ∧ fittingSubgroup (CentralizerBar z) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₁n := C.r3_K₁_normal hcen h3
  have hPp : IsPGroup 2 ↥P := quat_isPGroup hq
  have hPn : P.Normal := by
    constructor
    intro n hn g
    have hgN : g ∈ normalizer (C.K₁ : Set (CentralizerBar z)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      exact ⟨fun hh => hK₁n.conj_mem h hh g, fun hh => by
        have := hK₁n.conj_mem _ hh g⁻¹
        have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
        rwa [e] at this⟩
    have hmem : g * n * g⁻¹ ∈ C.K₂ := C.conj_K₂ hcen hgN (hPK hn)
    apply h2el _ hmem
    obtain ⟨m, hm⟩ := hPp ⟨n, hn⟩
    refine ⟨m, ?_⟩
    have hm' : n ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
    calc (g * n * g⁻¹) ^ (2 ^ m) = g * n ^ (2 ^ m) * g⁻¹ := by
          rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← map_pow]
      _ = 1 := by rw [hm']; group
  refine ⟨hPn, le_antisymm ?_ (le_sSup ⟨hPn, hPp.isNilpotent⟩)⟩
  have hlayer : layer (CentralizerBar z) = C.K₁ := by
    show sSup {K : Subgroup (CentralizerBar z) | IsComponent K} = _
    rw [C.r3_comps hcen h3, sSup_singleton]
  have hFD : fittingSubgroup (CentralizerBar z) ≤ centralizer (C.K₁ : Set (CentralizerBar z)) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hm : ⁅f, a⁆ ∈ ⁅fittingSubgroup (CentralizerBar z), layer (CentralizerBar z)⁆ :=
      Subgroup.commutator_mem_commutator hf (by rw [hlayer]; exact ha)
    rw [CFSG.LocalCores.fitting_layer_commute] at hm
    have h1 : ⁅f, a⁆ = 1 := by simpa using hm
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  set D := centralizer (C.K₁ : Set (CentralizerBar z)) with hD
  have hn1 : ((fittingSubgroup (CentralizerBar z)).subgroupOf D).Normal := inferInstance
  have hnil : Group.IsNilpotent ↥((fittingSubgroup (CentralizerBar z)).subgroupOf D) :=
    Group.nilpotent_of_mulEquiv (G := ↥(fittingSubgroup (CentralizerBar z)))
      (_h := inferInstance) (Subgroup.subgroupOfEquivOfLe hFD).symm
  have hle : (fittingSubgroup (CentralizerBar z)).subgroupOf D ≤ fittingSubgroup ↥D :=
    le_sSup ⟨hn1, hnil⟩
  rw [hF] at hle
  intro f hf
  exact hle (show (⟨f, hFD hf⟩ : ↥D) ∈ (fittingSubgroup (CentralizerBar z)).subgroupOf D from hf)

end R3c

section R3d

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.r3_WBar {P : Subgroup (CentralizerBar z)} (hPK : P ≤ C.K₂)
    (hPn : P.Normal) (hPp : IsPGroup 2 ↥P) (hF : fittingSubgroup (CentralizerBar z) = P) :
    WBar z = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro w hw
    have hWn : (WBar z).Normal := Stage2.Final.L26.WBar_normal z
    have hWp : IsPGroup 2 ↥(WBar z) := by
      rintro ⟨w, hw⟩
      obtain ⟨a, ha⟩ := Stage2.Final.L26.WBar_two_pow z w hw
      exact ⟨a, Subtype.ext ha⟩
    have hle : WBar z ≤ pCore 2 (CentralizerBar z) := le_sSup ⟨hWn, hWp⟩
    have hf : w ∈ fittingSubgroup (CentralizerBar z) :=
      (pCore_le_fitting (CentralizerBar z) 2) (hle hw)
    rwa [hF] at hf
  · rw [Stage1.Thm6.Prod.WBar_eq z]
    have hK₂O : C.K₂ ≤ oResidual 2 (CentralizerBar z) := hasSL2_le_oResidual C.odd₂ C.e₂
    have hPO : P ≤ oResidual 2 (CentralizerBar z) := hPK.trans hK₂O
    have hnP : (P.subgroupOf (oResidual 2 (CentralizerBar z))).Normal := hPn.subgroupOf _
    have hpP : IsPGroup 2 ↥(P.subgroupOf (oResidual 2 (CentralizerBar z))) :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPO).symm
    have hle : P.subgroupOf (oResidual 2 (CentralizerBar z)) ≤
        pCore 2 ↥(oResidual 2 (CentralizerBar z)) := le_sSup ⟨hnP, hpP⟩
    intro x hx
    exact ⟨⟨x, hPO hx⟩, hle (show (⟨x, hPO hx⟩ : ↥(oResidual 2 (CentralizerBar z))) ∈
      P.subgroupOf (oResidual 2 (CentralizerBar z)) from hx), rfl⟩

include C in
theorem G2Ctx.r3_oPrime (hcen : Cen2 G z S) {P : Subgroup (CentralizerBar z)} (hPK : P ≤ C.K₂)
    (hP2 : ∀ x ∈ C.K₂, (∃ m : ℕ, x ^ (2 ^ m) = 1) → x ∈ P) (hPp : IsPGroup 2 ↥P)
    (hq₁ : IVK.IsQuaternionTwoGroup ↥C.P₁ (C.n + 1)) :
    oPrimeResidualOf 2 (LBar z) = C.K₁ ⊔ P := by
  have hL : LBar z = C.K₁ ⊔ C.K₂ := C.LBar_eq hcen
  rw [hL]
  apply le_antisymm
  ·
    rw [oPrimeResidualOf, Subgroup.map_le_iff_le_comap]
    unfold oPrimeResidual
    rw [Subgroup.closure_le]
    rintro ⟨x, hx⟩ ⟨k, hk⟩
    show x ∈ C.K₁ ⊔ P
    obtain ⟨a, ha, b, hb, rfl⟩ := y_mem_sup_of_commute C.comm hx
    have hk' : (a * b) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hcomm : Commute a b := C.comm a ha b hb
    rw [hcomm.mul_pow] at hk'
    have hmem : a ^ (2 ^ k) ∈ C.K₁ ⊓ C.K₂ := by
      refine ⟨pow_mem ha _, ?_⟩
      have : a ^ (2 ^ k) = (b ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left hk'
      rw [this]
      exact Subgroup.inv_mem C.K₂ (Subgroup.pow_mem C.K₂ hb _)
    have hsq : (⟨a ^ (2 ^ k), hmem⟩ : ↥(C.K₁ ⊓ C.K₂)) ^ 2 = 1 := by
      have := pow_card_eq_one' (G := ↥(C.K₁ ⊓ C.K₂)) (x := ⟨a ^ (2 ^ k), hmem⟩)
      rwa [C.inf_card] at this
    have hsq' : (a ^ (2 ^ k)) ^ 2 = 1 := by simpa using congrArg Subtype.val hsq
    have hb2 : b ^ (2 ^ (k + 1)) = 1 := by
      have e : b ^ (2 ^ (k + 1)) = (b ^ (2 ^ k)) ^ 2 := by rw [pow_succ, pow_mul]
      have e2 : b ^ (2 ^ k) = (a ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_right hk'
      rw [e, e2, inv_pow, hsq', inv_one]
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (hP2 b hb ⟨k + 1, hb2⟩))
  · refine sup_le ?_ ?_
    ·
      have hN : (oPrimeResidual 2 ↥C.K₁).Normal := Stage1.Thm6.Prod.oPrimeResidual_normal 2 _
      have hP₁K : C.P₁ ≤ C.K₁ := inf_le_right
      have hpg : IsPGroup 2 ↥C.P₁ := IsPGroup.of_card (C.card_P₁ hcen)
      have h2el : ∀ (x : CentralizerBar z) (hx : x ∈ C.P₁),
          (⟨x, hP₁K hx⟩ : ↥C.K₁) ∈ oPrimeResidual 2 ↥C.K₁ := by
        intro x hx
        obtain ⟨m, hm⟩ := hpg ⟨x, hx⟩
        apply Subgroup.subset_closure
        exact ⟨m, Subtype.ext (by simpa using congrArg Subtype.val hm)⟩
      have htop : oPrimeResidual 2 ↥C.K₁ = ⊤ := by
        rcases CFSG.LocalCores.quasisimple_normal_subgroups C.quasi₁ hN with h | h
        · exact h
        · exfalso
          apply CFSG.GH74.GLS.IVK.Lifted.quatGroup_not_comm C.P₁ ⟨C.n + 1, hq₁⟩
          intro a ha b hb
          have hac := h (h2el a ha)
          have := Subgroup.mem_center_iff.1 hac ⟨b, hP₁K hb⟩
          exact (congrArg Subtype.val this).symm
      have key : ∀ w : ↥C.K₁, w ∈ oPrimeResidual 2 ↥C.K₁ →
          (w : CentralizerBar z) ∈ oPrimeResidualOf 2 (C.K₁ ⊔ C.K₂) := by
        intro w hw
        unfold oPrimeResidual at hw
        induction hw using Subgroup.closure_induction with
        | mem x hx =>
          obtain ⟨k, hk⟩ := hx
          refine ⟨⟨(x : CentralizerBar z), Subgroup.mem_sup_left x.2⟩, ?_, rfl⟩
          apply Subgroup.subset_closure
          exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
        | one => exact one_mem _
        | mul x y _ _ hx hy => exact mul_mem hx hy
        | inv x _ hx => exact inv_mem hx
      intro y hy
      exact key ⟨y, hy⟩ (by rw [htop]; trivial)
    · intro x hx
      refine ⟨⟨x, Subgroup.mem_sup_right (hPK hx)⟩, ?_, rfl⟩
      apply Subgroup.subset_closure
      obtain ⟨m, hm⟩ := hPp ⟨x, hx⟩
      exact ⟨m, Subtype.ext (by simpa using congrArg Subtype.val hm)⟩

end R3d

section R3e

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.r3_clause (hcen : Cen2 G z S) (h3 : Nat.card C.F₂ = 3)
    (hq₁ : IVK.IsQuaternionTwoGroup ↥C.P₁ (C.n + 1)) :
    Nonempty (↥(WBar z) ≃* QuaternionGroup 2) ∧
      generalizedFitting (CentralizerBar z) = oPrimeResidualOf 2 (LBar z) := by
  obtain ⟨-, P, hPK, hq, h2el, hF⟩ := C.r3_data hcen h3
  obtain ⟨hPn, hFY⟩ := C.r3_fitting hcen h3 hPK hq h2el hF
  have hPp : IsPGroup 2 ↥P := quat_isPGroup hq
  have hW := C.r3_WBar hPK hPn hPp hFY
  refine ⟨?_, ?_⟩
  · obtain ⟨-, ⟨e⟩⟩ := hq
    rw [hW]
    exact ⟨e⟩
  · show fittingSubgroup (CentralizerBar z) ⊔ layer (CentralizerBar z) = _
    have hlayer : layer (CentralizerBar z) = C.K₁ := by
      show sSup {K : Subgroup (CentralizerBar z) | IsComponent K} = _
      rw [C.r3_comps hcen h3, sSup_singleton]
    rw [hFY, hlayer, C.r3_oPrime hcen hPK h2el hPp hq₁, sup_comm]

end R3e

section R3f

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.n_eq_two_of_three (h3 : Nat.card C.F₂ = 3) : C.n = 2 := by
  have hv := C.v₂
  rw [card_statedSL_two', h3, factorization_two_mul_sq_sub_one 3 (Or.inl rfl)] at hv
  omega

include C in
theorem G2Ctx.quat₂_three (hcen : Cen2 G z S) (h3 : Nat.card C.F₂ = 3) :
    IVK.IsQuaternionTwoGroup ↥C.P₂ (C.n + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 := C.n_eq_two_of_three h3
  have hPK : C.P₂ ≤ C.K₂ := inf_le_right
  have hsyl : IsSylowOf 2 (C.P₂.subgroupOf C.K₂) ⊤ := by
    have := (isSylowOf_map_subtype_iff (p := 2) C.K₂ (A := C.P₂.subgroupOf C.K₂) (B := ⊤)).1
    apply this
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPK, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact C.sylow_P₂ hcen
  obtain ⟨-, h3', ⟨e⟩⟩ := sl2_three_sylow h3 C.e₂ hsyl
  rw [hn2]
  exact ⟨h3', ⟨(Subgroup.subgroupOfEquivOfLe hPK).symm.trans e⟩⟩

end R3f

section R3g

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.induced₂_three (hcen : Cen2 G z S) (h3 : Nat.card C.F₂ = 3)
    (hq₁ : IVK.IsQuaternionTwoGroup ↥C.P₁ (C.n + 1))
    (hq₂ : IVK.IsQuaternionTwoGroup ↥C.P₂ (C.n + 1))
    (hnorm : ∀ x ∈ barOf z S, x ∈ normalizer (C.K₂ : Set (CentralizerBar z)))
    (hinv : ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2) :
    InducedPGL2 C.K₂ (barOf z S) 3 := by
  obtain ⟨ζ, hζ₁, hζ₂, hζo, -, -⟩ := C.exists_zeta hcen
  obtain ⟨u, huT, hu2, huK⟩ := C.exists_invol hcen hinv
  have huN : u ∈ normalizer (C.K₂ : Set (CentralizerBar z)) := hnorm u huT
  have hPs : IsSylowOf 2 C.P₂ C.K₂ := C.sylow_P₂ hcen
  have huP' := C.P₂_normalizes hcen huT huN hu2
  have hout : ∀ p ∈ C.P₂, ∃ x ∈ C.K₂, (u * p⁻¹) * x ≠ x * (u * p⁻¹) := by
    intro p hp
    have hpT : p ∈ barOf z S := hp.1.1
    have hg : u * p⁻¹ ∈ barOf z S := (barOf z S).mul_mem huT ((barOf z S).inv_mem hpT)
    have hgK : u * p⁻¹ ∉ C.K₁ ⊔ C.K₂ := by
      intro h
      apply huK
      have e : u = (u * p⁻¹) * p := by group
      rw [e]
      exact mul_mem h (Subgroup.mem_sup_right hp.2)
    have := (C.no_outside hcen hq₁ hq₂ hg hgK).2
    push Not at this
    obtain ⟨p', hp', hne⟩ := this
    exact ⟨p', hp'.2, hne⟩
  have hζsq : ζ * ζ = 1 := by
    have := pow_orderOf_eq_one ζ
    rwa [hζo, pow_two] at this
  have hZ : ∀ c ∈ C.K₂, (∀ x ∈ C.K₂, c * x = x * c) → c * c = 1 := by
    intro c hc hcc
    have hmem : (⟨c, hc⟩ : ↥C.K₂) ∈ Subgroup.center ↥C.K₂ := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcc g g.2).symm
    have hζo' : orderOf (⟨ζ, hζ₂⟩ : ↥C.K₂) = 2 := by rw [orderOf_mk]; exact hζo
    rcases kabs_center_cases C.odd₂ (C.e₂.trans (specialLinearGroupEquivStatedSL 2 C.F₂).symm)
      hζo' hmem with h | h
    · have : c = 1 := congrArg Subtype.val h
      rw [this, one_mul]
    · have : c = ζ := congrArg Subtype.val h
      rw [this]; exact hζsq
  have hnon := not_inner_of_no_centralizer hPs hu2 huP' hZ hout
  exact inducedPGL2_sl2_three h3 C.e₂ (fun x hx => hnorm x hx) huT hnon

end R3g

end CFSG.GH74.GLS.Stage1.Main
