module

public import CFSG.Fischer.Classification.Recognition.Fischer
public import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.Adapters.LieModelSimple
public import CFSG.Fischer.Classification.Pinned

public section

namespace CFSG.Fischer.Classification.Recognition

open CFSG.Blueprint.Fischer CFSG.Open
open scoped commutatorElement Pointwise

@[expose] def ClassicalComponentOrders : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Hyp G D → ClassicalConclusion G D →
    ∀ d ∈ D, ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer ({d} : Set G)) →
      Nat.card (K ⧸ Subgroup.center K) ∉ fischerComponentOrders

variable {G : Type} [Group G]

theorem isQuasisimple_of_isSimpleGroup {L : Type*} [Group L] [IsSimpleGroup L]
    (hL : ∃ a b : L, a * b ≠ b * a) : Open.IsQuasisimple L := by
  have hZ : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hL
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hL
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

theorem exists_not_commute_of_isSimpleGroup {L : Type*} [Group L] [IsSimpleGroup L]
    (hL : ¬ (Nat.card L).Prime) : ∃ a b : L, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let _ : CommGroup L := { (inferInstance : Group L) with mul_comm := h }
  exact hL (IsSimpleGroup.prime_card (α := L))

theorem isSimpleGroup_of_lieModel_PSU_six {Q : Type} [Group Q]
    (h : CFSG.Blueprint.LieModel Q .PSU 6 2 1) : IsSimpleGroup Q :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem card_Fi23_not_prime : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.Fi23).Prime := by
  rw [CFSG.Sporadic.Fi23.card_Fi23]
  exact fun h => by
    have := h.eq_one_or_self_of_dvd 2 (by norm_num)
    omega

theorem centralizer_quasisimple_lieModel_of_fi22
    {D : Set G} (hP : Pair G D) {k : Fin 3}
    (hk : k.val = 0) (ψ : G ≃* Carrier k) {d : G} (hd : d ∈ D) :
    Open.IsQuasisimple (Subgroup.centralizer ({d} : Set G)) ∧
      CFSG.Blueprint.LieModel (Subgroup.centralizer ({d} : Set G) ⧸
        Subgroup.center (Subgroup.centralizer ({d} : Set G))) .PSU 6 2 1 := by
  obtain ⟨hcomm, -, -⟩ := centralizer_perfect_center hP (by omega) ψ hd
  obtain ⟨H, hH, ⟨e⟩⟩ := centralizer_quotient_of_fi22 hP hk ψ hd
  have hL := lieModel_of_mulEquiv_PSU hH e
  exact ⟨⟨hcomm, isSimpleGroup_of_lieModel_PSU_six hL⟩, hL⟩

theorem centralizer_quasisimple_of_fi23
    {D : Set G} (hP : Pair G D) {k : Fin 3}
    (hk : k.val = 1) (ψ : G ≃* Carrier k) {d : G} (hd : d ∈ D) :
    Open.IsQuasisimple (Subgroup.centralizer ({d} : Set G)) ∧
      Nonempty (Subgroup.centralizer ({d} : Set G) ⧸
        Subgroup.center (Subgroup.centralizer ({d} : Set G)) ≃*
          CFSG.Blueprint.NativeSporadic.Fi22) := by
  obtain ⟨hcomm, -, -⟩ := centralizer_perfect_center hP (by omega) ψ hd
  obtain ⟨e⟩ := centralizer_quotient_of_fi23 hP hk ψ hd
  exact ⟨⟨hcomm, @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 e⟩, ⟨e⟩⟩

theorem isQuasisimple_of_mulEquiv_fi23 {L : Subgroup G}
    (e : L ≃* CFSG.Blueprint.NativeSporadic.Fi23) :
    Open.IsQuasisimple L ∧ Nat.card (L ⧸ Subgroup.center L) = 4089470473293004800 := by
  have : IsSimpleGroup L := @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi23.isSimpleGroup_Fi23 e
  have hnc : ∃ a b : L, a * b ≠ b * a := exists_not_commute_of_isSimpleGroup (by
    rw [Nat.card_congr e.toEquiv]
    exact card_Fi23_not_prime)
  refine ⟨isQuasisimple_of_isSimpleGroup hnc, ?_⟩
  have hZ : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).toEquiv, Nat.card_congr e.toEquiv, CFSG.Sporadic.Fi23.card_Fi23]

theorem card_component_of_carrier
    {D : Set G} (hP : Pair G D) (k : Fin 3) (ψ : G ≃* Carrier k)
    {d : G} (hd : d ∈ D) {K : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer ({d} : Set G))) :
    Nat.card (K ⧸ Subgroup.center K) =
      if k.val = 0 then 9196830720 else if k.val = 1 then 64561751654400
        else 4089470473293004800 := by
  rcases k with ⟨_ | _ | _ | k, hk'⟩
  · obtain ⟨hq, hL⟩ := centralizer_quasisimple_lieModel_of_fi22 hP rfl ψ hd
    rw [IsComponentOf.eq_of_isQuasisimple hK hq]
    exact card_of_lieModel_PSU_six hL
  · obtain ⟨hq, ⟨e⟩⟩ := centralizer_quasisimple_of_fi23 hP rfl ψ hd
    rw [IsComponentOf.eq_of_isQuasisimple hK hq, Nat.card_congr e.toEquiv,
      CFSG.Sporadic.Fi22.card_Fi22]
    rfl
  · obtain ⟨L, ⟨e⟩, hC, -, hdL⟩ := centralizer_of_fi24 hP rfl ψ hd
    obtain ⟨hq, hcard⟩ := isQuasisimple_of_mulEquiv_fi23 e
    rw [IsComponentOf.eq_of_sup_zpowers hK hC hdL hq, hcard]
    rfl
  · omega

theorem isComponentOf_self {C : Subgroup G} (hC : Open.IsQuasisimple C) : IsComponentOf C C :=
  ⟨le_rfl, IsSubnormal.refl C, hC⟩

theorem fischerComponentOrders_psu : 9196830720 ∈ fischerComponentOrders := by
  simp [fischerComponentOrders]

theorem fischerComponentOrders_fi22 : 64561751654400 ∈ fischerComponentOrders := by
  simp [fischerComponentOrders]

theorem fischerComponentOrders_fi23 : 4089470473293004800 ∈ fischerComponentOrders := by
  simp [fischerComponentOrders]

theorem recognition_of_statement
    (hcl : ClassicalComponentOrders) (h : Statement) {D : Set G}
    (hH : Hyp G D) {d : G} (hd : d ∈ D) :
    let C := Subgroup.centralizer ({d} : Set G)
    (Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Fi22) ↔
      ∃ K : Subgroup G, IsComponentOf K C ∧
        CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU 6 2 1) ∧
    (Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Fi23) ↔
      ∃ K : Subgroup G, IsComponentOf K C ∧
        Nonempty ((K ⧸ Subgroup.center K) ≃* CFSG.Blueprint.NativeSporadic.Fi22)) ∧
    (Nonempty (G ≃* MulAut CFSG.Blueprint.NativeSporadic.Fi24prime) ↔
      ∃ K : Subgroup G, IsComponentOf K C ∧
        Nonempty ((K ⧸ Subgroup.center K) ≃* CFSG.Blueprint.NativeSporadic.Fi23)) ∧
    (Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Fi22) →
      commutator C = ⊤ ∧ (Subgroup.center C).map C.subtype = Subgroup.zpowers d ∧
        Nat.card (Subgroup.center C) = 2 ∧
        CFSG.Blueprint.LieModel (C ⧸ Subgroup.center C) .PSU 6 2 1) ∧
    (Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Fi23) →
      commutator C = ⊤ ∧ (Subgroup.center C).map C.subtype = Subgroup.zpowers d ∧
        Nat.card (Subgroup.center C) = 2 ∧
        Nonempty ((C ⧸ Subgroup.center C) ≃* CFSG.Blueprint.NativeSporadic.Fi22)) ∧
    (Nonempty (G ≃* MulAut CFSG.Blueprint.NativeSporadic.Fi24prime) →
      ∃ K : Subgroup G, Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Fi23) ∧
        C = Subgroup.zpowers d ⊔ K ∧ Subgroup.zpowers d ⊓ K = ⊥ ∧
        Subgroup.zpowers d ≤ Subgroup.centralizer (K : Set G)) := by
  intro C
  have hP := hH.pair
  have : Finite G := hP.1
  have hcases := pinned_of_statement h hH
  have horder : ∀ K : Subgroup G, IsComponentOf K C →
      (ClassicalConclusion G D → Nat.card (K ⧸ Subgroup.center K) ∉ fischerComponentOrders) ∧
      (∀ ψ : G ≃* Carrier 0, Nat.card (K ⧸ Subgroup.center K) = 9196830720) ∧
      (∀ ψ : G ≃* Carrier 1, Nat.card (K ⧸ Subgroup.center K) = 64561751654400) ∧
      (∀ ψ : G ≃* Carrier 2, Nat.card (K ⧸ Subgroup.center K) = 4089470473293004800) :=
    fun K hK => ⟨fun hc => hcl G D hH hc d hd K hK,
      fun ψ => card_component_of_carrier hP 0 ψ hd hK,
      fun ψ => card_component_of_carrier hP 1 ψ hd hK,
      fun ψ => card_component_of_carrier hP 2 ψ hd hK⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro ⟨ψ⟩
    obtain ⟨hq, hL⟩ := centralizer_quasisimple_lieModel_of_fi22 hP (k := 0) rfl ψ hd
    exact ⟨C, isComponentOf_self hq, hL⟩
  · rintro ⟨K, hK, hL⟩
    have hc := card_of_lieModel_PSU_six hL
    obtain ⟨h1, -, h3, h4⟩ := horder K hK
    rcases hcases with hcl' | ⟨φ, -⟩ | ⟨φ, -⟩ | ⟨φ, -⟩
    · exact absurd (hc ▸ fischerComponentOrders_psu) (h1 hcl')
    · exact ⟨φ⟩
    · exact absurd (h3 φ) (by rw [hc]; norm_num)
    · exact absurd (h4 φ) (by rw [hc]; norm_num)
  · rintro ⟨ψ⟩
    obtain ⟨hq, he⟩ := centralizer_quasisimple_of_fi23 hP (k := 1) rfl ψ hd
    exact ⟨C, isComponentOf_self hq, he⟩
  · rintro ⟨K, hK, ⟨e⟩⟩
    have hc : Nat.card (K ⧸ Subgroup.center K) = 64561751654400 := by
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Fi22.card_Fi22]
    obtain ⟨h1, h2, -, h4⟩ := horder K hK
    rcases hcases with hcl' | ⟨φ, -⟩ | ⟨φ, -⟩ | ⟨φ, -⟩
    · exact absurd (hc ▸ fischerComponentOrders_fi22) (h1 hcl')
    · exact absurd (h2 φ) (by rw [hc]; norm_num)
    · exact ⟨φ⟩
    · exact absurd (h4 φ) (by rw [hc]; norm_num)
  · rintro ⟨ψ⟩
    obtain ⟨L, ⟨e⟩, hC, -, hdL⟩ := centralizer_of_fi24 hP (k := 2) rfl ψ hd
    obtain ⟨hq, -⟩ := isQuasisimple_of_mulEquiv_fi23 e
    have hLC : IsComponentOf L C := by
      have hLle : L ≤ C := by
        show L ≤ Subgroup.centralizer ({d} : Set G)
        rw [hC]
        exact le_sup_right
      refine ⟨hLle, IsSubnormal.step hLle ?_ (IsSubnormal.refl C), hq⟩
      rw [Subgroup.normal_subgroupOf_iff hLle]
      intro l g hl hg
      have hdec : g ∈ ((Subgroup.zpowers d : Set G) * (L : Set G)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
          (hdL.trans (Subgroup.centralizer_le_normalizer _)), ← hC]
        exact hg
      obtain ⟨z, hz, l', hl', rfl⟩ := hdec
      have hzc : ∀ y ∈ L, z * y = y * z := fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (hdL hz) y hy).symm
      rw [show z * l' * l * (z * l')⁻¹ = z * (l' * l * l'⁻¹) * z⁻¹ by group,
        hzc _ (L.mul_mem (L.mul_mem hl' hl) (L.inv_mem hl')), mul_inv_cancel_right]
      exact L.mul_mem (L.mul_mem hl' hl) (L.inv_mem hl')
    have hZ : Nonempty ((L ⧸ Subgroup.center L) ≃* CFSG.Blueprint.NativeSporadic.Fi23) := by
      have : IsSimpleGroup L :=
        @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi23.isSimpleGroup_Fi23 e
      have hZL : Subgroup.center L = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h' | h'
        · exact h'
        · exfalso
          have hnc : ∃ a b : L, a * b ≠ b * a := exists_not_commute_of_isSimpleGroup (by
            rw [Nat.card_congr e.toEquiv]
            exact card_Fi23_not_prime)
          obtain ⟨a, b, hab⟩ := hnc
          exact hab ((Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top b)) a)
      exact ⟨((QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot).trans e⟩
    exact ⟨L, hLC, hZ⟩
  · rintro ⟨K, hK, ⟨e⟩⟩
    have hc : Nat.card (K ⧸ Subgroup.center K) = 4089470473293004800 := by
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Fi23.card_Fi23]
    obtain ⟨h1, h2, h3, -⟩ := horder K hK
    rcases hcases with hcl' | ⟨φ, -⟩ | ⟨φ, -⟩ | ⟨φ, -⟩
    · exact absurd (hc ▸ fischerComponentOrders_fi23) (h1 hcl')
    · exact absurd (h2 φ) (by rw [hc]; norm_num)
    · exact absurd (h3 φ) (by rw [hc]; norm_num)
    · exact ⟨φ⟩
  · rintro ⟨ψ⟩
    obtain ⟨h1, h2, h3⟩ := centralizer_perfect_center hP (k := 0) (by decide) ψ hd
    exact ⟨h1, h2, h3, (centralizer_quasisimple_lieModel_of_fi22 hP (k := 0) rfl ψ hd).2⟩
  · rintro ⟨ψ⟩
    obtain ⟨h1, h2, h3⟩ := centralizer_perfect_center hP (k := 1) (by decide) ψ hd
    exact ⟨h1, h2, h3, centralizer_quotient_of_fi23 hP (k := 1) rfl ψ hd⟩
  · rintro ⟨ψ⟩
    exact centralizer_of_fi24 hP (k := 2) rfl ψ hd

end CFSG.Fischer.Classification.Recognition
