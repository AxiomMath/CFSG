module

public import CFSG.Goldschmidt.Steps.G3aSStar
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
import CFSG.Milestones.OO_odd_order_solvable
import CFSG.Walter.Bender1970.S3.FStar

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace G3a

section FStar

variable {X : Type} [Group X] [Finite X]

abbrev oddFit (X : Type) [Group X] : Subgroup X :=
  (goldschmidtOddCore (CFSG.fittingSubgroup X)).map (CFSG.fittingSubgroup X).subtype

omit [Finite X] in
theorem oddFit_normal : (oddFit X).Normal := by
  have : (goldschmidtOddCore (CFSG.fittingSubgroup X)).Characteristic :=
    CFSG.ComponentClassification.OddCore.characteristic (CFSG.fittingSubgroup X)
  infer_instance

omit [Finite X] in
theorem le_fitting {N : Subgroup X} (hN : N.Normal) (hnil : Group.IsNilpotent N) :
    N ≤ CFSG.fittingSubgroup X :=
  le_sSup ⟨hN, hnil⟩

theorem inf_oddCore_le :
    Subgroup.centralizer (oddFit X : Set X) ⊓ goldschmidtOddCore X ≤ oddFit X := by
  have hOFn := oddFit_normal (X := X)
  set M := Subgroup.centralizer (oddFit X : Set X) ⊓ goldschmidtOddCore X with hM
  have hMn : M.Normal := inferInstance
  have hModd : Odd (Nat.card M) :=
    (CFSG.ComponentClassification.OddCore.odd_card X).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_right)
  have hMsolv : Group.IsSolvable M := CFSG.Milestones.odd_order_solvable hModd
  set FM := (CFSG.fittingSubgroup M).map M.subtype with hFM
  have hFMn : FM.Normal := inferInstance
  have hFMnil : Group.IsNilpotent FM :=
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ M.subtype_injective)
  have hFMF : FM ≤ CFSG.fittingSubgroup X := le_fitting hFMn hFMnil
  have hFModd : Odd (Nat.card FM) := by
    rw [hFM, Subgroup.card_map_of_injective M.subtype_injective]
    exact hModd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hFMO : FM ≤ oddFit X := by
    have hle : FM.subgroupOf (CFSG.fittingSubgroup X) ≤
        goldschmidtOddCore (CFSG.fittingSubgroup X) := by
      refine le_sSup ⟨hFMn.subgroupOf _, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFMF).toEquiv]
      exact hFModd
    intro x hx
    exact ⟨⟨x, hFMF hx⟩, hle hx, rfl⟩
  have hcent : (⊤ : Subgroup M) ≤ Subgroup.centralizer (CFSG.fittingSubgroup M : Set M) := by
    intro m _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hyO : (y : X) ∈ oddFit X := hFMO ⟨y, hy, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp m.2.1 _ hyO
  have htop := hcent.trans (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hMsolv)
  intro x hx
  exact hFMO ⟨⟨x, hx⟩, htop (Subgroup.mem_top _), rfl⟩

omit [Finite X] in
theorem exists_act_of_gen (hgen : CFSG.Open.pCore 2 X ⊔ goldschmidtLayer X = ⊤)
    (hcen : CFSG.Open.pCore 2 X ≤ Subgroup.center X) [Finite X] {L : Subgroup X}
    (hL : IsComponentOf L ⊤) (q : X) : ∃ ℓ ∈ L, ∀ x ∈ L, q⁻¹ * x * q = ℓ⁻¹ * x * ℓ := by
  have h2 : CFSG.Open.pCore 2 X ≤ actsBy L L le_rfl := fun q hq =>
    mem_actsBy.mpr ⟨1, L.one_mem, fun x _ => by
      have := Subgroup.mem_center_iff.1 (hcen hq) x
      calc q⁻¹ * x * q = q⁻¹ * (x * q) := by group
        _ = q⁻¹ * (q * x) := by rw [this]
        _ = 1⁻¹ * x * 1 := by group⟩
  have hE : goldschmidtLayer X ≤ actsBy L L le_rfl := by
    refine sSup_le fun L' hL' => ?_
    by_cases hLL : L' = L
    · intro y hy
      rw [hLL] at hy
      exact mem_actsBy.mpr ⟨y, hy, fun x _ => rfl⟩
    · intro y hy
      refine mem_actsBy.mpr ⟨1, L.one_mem, fun x hx => ?_⟩
      have hcm := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (N8b X L' L hL' hL hLL) hy
      have := Subgroup.mem_centralizer_iff.1 hcm x hx
      calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
        _ = y⁻¹ * (y * x) := by rw [this]
        _ = 1⁻¹ * x * 1 := by group
  have h := sup_le h2 hE
  rw [hgen] at h
  exact mem_actsBy.mp (h (Subgroup.mem_top q))

theorem component_normal_of_gen (hgen : CFSG.Open.pCore 2 X ⊔ goldschmidtLayer X = ⊤)
    (hcen : CFSG.Open.pCore 2 X ≤ Subgroup.center X) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) : L.Normal := ⟨fun x hx g => by
  obtain ⟨ℓ, hℓ, hact⟩ := exists_act_of_gen hgen hcen hL g⁻¹
  have := hact x hx
  rw [inv_inv] at this
  rw [this]
  exact L.mul_mem (L.mul_mem (L.inv_mem hℓ) hx) hℓ⟩

theorem le_pCore_sup_of_normal {Q : Type} [Group Q] [Finite Q] (hodd : goldschmidtOddCore Q = ⊥)
    (hgen : CFSG.Open.pCore 2 Q ⊔ goldschmidtLayer Q = ⊤)
    (hcen : CFSG.Open.pCore 2 Q ≤ Subgroup.center Q) {N : Subgroup Q} [N.Normal] :
    N ≤ CFSG.Open.pCore 2 Q ⊔ sSup {L : Subgroup Q | IsComponentOf L ⊤ ∧ L ≤ N} := by
  have hpn := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal (G := Q) 2
  have hcompn : ∀ L, IsComponentOf L ⊤ → L.Normal := fun L hL =>
    component_normal_of_gen hgen hcen hL
  set E₁ := sSup {L : Subgroup Q | IsComponentOf L ⊤ ∧ L ≤ N} with hE₁
  set E₂ := sSup {L : Subgroup Q | IsComponentOf L ⊤ ∧ ¬ L ≤ N} with hE₂
  have hE₁n : E₁.Normal := Subgroup.sSup_normal _ fun L hL => hcompn L hL.1
  have hE₂n : E₂.Normal := Subgroup.sSup_normal _ fun L hL => hcompn L hL.1
  have hlayer : goldschmidtLayer Q = E₁ ⊔ E₂ := by
    refine le_antisymm (sSup_le fun L hL => ?_) (sup_le (sSup_le fun L hL => le_sSup hL.1)
      (sSup_le fun L hL => le_sSup hL.1))
    by_cases h : L ≤ N
    · exact le_sup_of_le_left (le_sSup ⟨hL, h⟩)
    · exact le_sup_of_le_right (le_sSup ⟨hL, h⟩)
  have hE₂N : E₂ ≤ Subgroup.centralizer (N : Set Q) := sSup_le fun L hL =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes L N
        hL.1).resolve_left hL.2)
  have hE₁E₂ : E₂ ≤ Subgroup.centralizer (E₁ : Set Q) := by
    refine sSup_le fun L₂ hL₂ => ?_
    rw [← Subgroup.le_centralizer_iff]
    refine sSup_le fun L₁ hL₁ => ?_
    have hne : L₁ ≠ L₂ := fun h => hL₂.2 (h ▸ hL₁.2)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (N8b Q L₁ L₂ hL₁.1 hL₂.1 hne)
  intro x hx
  have hxtop : x ∈ CFSG.Open.pCore 2 Q ⊔ goldschmidtLayer Q := by
    rw [hgen]
    exact Subgroup.mem_top x
  obtain ⟨z, hz, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxtop
  rw [hlayer] at he
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp he
  have hzc : ∀ y : Q, z * y = y * z := fun y => (Subgroup.mem_center_iff.mp (hcen hz) y).symm
  have he₂c : ∀ y ∈ E₂, y * e₂ = e₂ * y := by
    intro y hy
    have h1 := Subgroup.mem_centralizer_iff.mp (hE₂N hy) _ hx
    have h2 := Subgroup.mem_centralizer_iff.mp (hE₁E₂ hy) _ he₁
    have h3 : z * e₁ * (y * e₂) = z * e₁ * (e₂ * y) := by
      calc z * e₁ * (y * e₂) = z * (e₁ * y) * e₂ := by group
        _ = z * (y * e₁) * e₂ := by rw [h2]
        _ = (z * y) * e₁ * e₂ := by group
        _ = (y * z) * e₁ * e₂ := by rw [hzc y]
        _ = y * (z * (e₁ * e₂)) := by group
        _ = z * (e₁ * e₂) * y := h1.symm
        _ = z * e₁ * (e₂ * y) := by group
    exact mul_left_cancel h3
  have he₂L : e₂ ∈ goldschmidtLayer Q := by rw [hlayer]; exact Subgroup.mem_sup_right he₂
  have he₂Z : e₂ ∈ CFSG.Open.pCore 2 Q := by
    refine (N8d Q hodd).2.1 ⟨⟨e₂, he₂L⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    have hy : (y : Q) ∈ E₁ ⊔ E₂ := by rw [← hlayer]; exact y.2
    obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    have h1 := Subgroup.mem_centralizer_iff.mp (hE₁E₂ he₂) _ hy₁
    change (y : Q) * e₂ = e₂ * y
    rw [← hy, mul_assoc, he₂c y₂ hy₂, ← mul_assoc, h1, mul_assoc]
  have he₁e₂ : e₁ * e₂ = e₂ * e₁ := Subgroup.mem_centralizer_iff.mp (hE₁E₂ he₂) _ he₁
  rw [he₁e₂, ← mul_assoc]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((CFSG.Open.pCore 2 Q).mul_mem hz he₂Z))
    (Subgroup.mem_sup_right he₁)

theorem layer_sSup_eq_top {Q : Type} [Group Q] [Finite Q] (𝒮 : Set (Subgroup Q))
    (h𝒮 : ∀ L ∈ 𝒮, IsComponentOf L ⊤) : goldschmidtLayer ↥(sSup 𝒮) = ⊤ := by
  have hle : sSup 𝒮 ≤ (goldschmidtLayer ↥(sSup 𝒮)).map (sSup 𝒮).subtype := by
    refine sSup_le fun L hL => ?_
    have hLE : L ≤ sSup 𝒮 := le_sSup hL
    have hc := CFSG.ComponentClassification.LocalComponents.of_overgroup (h𝒮 L hL) hLE
    have h1 : L.subgroupOf (sSup 𝒮) ≤ goldschmidtLayer ↥(sSup 𝒮) :=
      CFSG.ComponentClassification.Layer.component_le hc
    have h2 := Subgroup.map_mono (f := (sSup 𝒮).subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hLE] at h2
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [show y = x from Subtype.ext hyx] at hy

omit [Finite X] in
theorem layer_map_le_of_normal {W : Subgroup X} (hW : W.Normal) :
    (goldschmidtLayer W).map W.subtype ≤ goldschmidtLayer X := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact CFSG.ComponentClassification.Layer.component_le
    (CFSG.ComponentClassification.LocalComponents.of_subnormal_subgroup W
      (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hW.isSubnormal) K hK)

theorem centralizer_oddFit_le
    (hgen : CFSG.Open.pCore 2 (X ⧸ goldschmidtOddCore X) ⊔
      goldschmidtLayer (X ⧸ goldschmidtOddCore X) = ⊤)
    (hcen : CFSG.Open.pCore 2 (X ⧸ goldschmidtOddCore X) ≤
      Subgroup.center (X ⧸ goldschmidtOddCore X)) :
    Subgroup.centralizer (oddFit X : Set X) ≤ CFSG.fittingSubgroup X ⊔ goldschmidtLayer X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOFn := oddFit_normal (X := X)
  set C := Subgroup.centralizer (oddFit X : Set X) with hC
  have hCn : C.Normal := inferInstance
  set π := QuotientGroup.mk' (goldschmidtOddCore X) with hπ
  have hodd : goldschmidtOddCore (X ⧸ goldschmidtOddCore X) = ⊥ :=
    goldschmidtOddCore_quotient_eq_bot X
  have hM : C ⊓ goldschmidtOddCore X ≤ oddFit X := inf_oddCore_le
  have hMF : oddFit X ≤ CFSG.fittingSubgroup X := Subgroup.map_subtype_le _
  have hker : ∀ {x : X}, π x = 1 ↔ x ∈ goldschmidtOddCore X := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hcentral : ∀ {w : X}, w ∈ C → π w = 1 → ∀ {c : X}, c ∈ C → c * w = w * c := by
    intro w hw hw1 c hc
    have hwO : w ∈ oddFit X := hM ⟨hw, hker.mp hw1⟩
    exact Subgroup.mem_centralizer_iff.mp hc w hwO |>.symm
  have hCbn : (C.map π).Normal := hCn.map π (QuotientGroup.mk'_surjective _)
  set E₁ := sSup {L : Subgroup (X ⧸ goldschmidtOddCore X) | IsComponentOf L ⊤ ∧ L ≤ C.map π}
    with hE₁
  have hE₁C : E₁ ≤ C.map π := sSup_le fun L hL => hL.2
  have hcompn : ∀ L : Subgroup (X ⧸ goldschmidtOddCore X), IsComponentOf L ⊤ → L.Normal :=
    fun L hL => component_normal_of_gen hgen hcen hL
  have hE₁n : E₁.Normal := Subgroup.sSup_normal _ fun L hL => hcompn L hL.1
  have hdec := le_pCore_sup_of_normal hodd hgen hcen (N := C.map π)
  have hY : C ⊓ (CFSG.Open.pCore 2 (X ⧸ goldschmidtOddCore X)).comap π ≤
      CFSG.fittingSubgroup X := by
    set Y := C ⊓ (CFSG.Open.pCore 2 (X ⧸ goldschmidtOddCore X)).comap π with hY
    have hpn := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal
      (G := X ⧸ goldschmidtOddCore X) 2
    have hYn : Y.Normal := inferInstance
    let f : Y →* CFSG.Open.pCore 2 (X ⧸ goldschmidtOddCore X) :=
      (π.comp Y.subtype).codRestrict _ fun y => y.2.2
    have hfker : f.ker ≤ Subgroup.center Y := by
      intro y hy
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      have hy1 : π y = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
      exact hcentral y.2.1 hy1 c.2.1
    have : Group.IsNilpotent (CFSG.Open.pCore 2 (X ⧸ goldschmidtOddCore X)) :=
      (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2).isNilpotent
    have hYnil : Group.IsNilpotent Y := Subgroup.isNilpotent_of_ker_le_center f hfker
    exact le_fitting hYn hYnil
  have hW : C ⊓ E₁.comap π ≤ CFSG.fittingSubgroup X ⊔ goldschmidtLayer X := by
    set W := C ⊓ E₁.comap π with hWdef
    have hWn : W.Normal := inferInstance
    let ρ : W →* E₁ := (π.comp W.subtype).codRestrict _ fun w => w.2.2
    have hρ : Function.Surjective ρ := by
      intro e
      obtain ⟨c, hc, hce⟩ := hE₁C e.2
      refine ⟨⟨c, hc, ?_⟩, Subtype.ext hce⟩
      show π c ∈ E₁
      rw [hce]
      exact e.2
    have hρker : ρ.ker ≤ Subgroup.center W := by
      intro w hw
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      have hw1 : π w = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hw)
      exact hcentral w.2.1 hw1 c.2.1
    have hlay := CFSG.ComponentClassification.CentralComponentQuotients.layer_map ρ hρ hρker
    have htop : goldschmidtLayer E₁ = ⊤ := layer_sSup_eq_top _ fun L hL => hL.1
    intro w hw
    have hρw : ρ ⟨w, hw⟩ ∈ (CFSG.ComponentClassification.Layer.subgroup W).map ρ := by
      rw [hlay, show CFSG.ComponentClassification.Layer.subgroup E₁ = ⊤ from htop]
      exact Subgroup.mem_top _
    obtain ⟨w', hw', hw'w⟩ := hρw
    have hdiff : (w' : X)⁻¹ * w ∈ CFSG.fittingSubgroup X := by
      have h1 : π ((w' : X)⁻¹ * w) = 1 := by
        rw [map_mul, map_inv]
        have := congrArg Subtype.val hw'w
        change π w' = π w at this
        rw [this, inv_mul_cancel]
      exact hMF (hM ⟨C.mul_mem (C.inv_mem w'.2.1) hw.1, hker.mp h1⟩)
    have hw'E : (w' : X) ∈ goldschmidtLayer X := layer_map_le_of_normal hWn ⟨w', hw', rfl⟩
    have e : w = (w' : X) * ((w' : X)⁻¹ * w) := by group
    rw [e, sup_comm]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw'E) (Subgroup.mem_sup_right hdiff)
  have hpn := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal
    (G := X ⧸ goldschmidtOddCore X) 2
  intro c hc
  obtain ⟨z, hz, e, he, hze⟩ := Subgroup.mem_sup_of_normal_left.mp (hdec ⟨c, hc, rfl⟩)
  obtain ⟨c₁, hc₁, hc₁e⟩ := hE₁C he
  have hY' : c * c₁⁻¹ ∈ CFSG.fittingSubgroup X := by
    refine hY ⟨C.mul_mem hc (C.inv_mem hc₁), ?_⟩
    show π (c * c₁⁻¹) ∈ CFSG.Open.pCore 2 (X ⧸ goldschmidtOddCore X)
    rw [map_mul, map_inv, hc₁e, ← hze, mul_inv_cancel_right]
    exact hz
  have hW' : c₁ ∈ CFSG.fittingSubgroup X ⊔ goldschmidtLayer X := by
    refine hW ⟨hc₁, ?_⟩
    show π c₁ ∈ E₁
    rw [hc₁e]
    exact he
  have e2 : c = (c * c₁⁻¹) * c₁ := by group
  rw [e2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hY') hW'

end FStar

section Transport

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem gw_isComponentOf_of_open {Y : Type*} [Group Y] {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) : GorensteinWalter.IsComponentOf L ⊤ := by
  refine ⟨le_top, ?_, ⟨CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2, hL.2.2.1,
    hL.2.2.2⟩⟩
  exact (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
    Subgroup.IsSubnormal.top).subgroupOf

omit [Finite G] in
theorem oddCoreOf_fittingSubgroupOf (K : Subgroup G) :
    oddCoreOf (CFSG.fittingSubgroupOf K) = (oddFit K).map K.subtype := by
  set F := CFSG.fittingSubgroup K with hF
  let e : F ≃* (F.map K.subtype : Subgroup G) := F.equivMapOfInjective K.subtype K.subtype_injective
  have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant e
  change ((goldschmidtOddCore (F.map K.subtype : Subgroup G)).map
    (F.map K.subtype).subtype) = ((goldschmidtOddCore F).map F.subtype).map K.subtype
  rw [← show (goldschmidtOddCore F).map e.toMonoidHom =
    goldschmidtOddCore (F.map K.subtype : Subgroup G) from h1, Subgroup.map_map,
    Subgroup.map_map]
  rfl

theorem part_d {H A : Subgroup G} (hS : IsSStarIn H A) :
    normalClosureIn H A ⊓ Subgroup.centralizer
        (oddCoreOf (CFSG.fittingSubgroupOf (normalClosureIn H A)) : Set G) ≤
      GorensteinWalter.generalizedFittingSubgroupOf H := by
  obtain ⟨hAH, -, T, -, -, -, hgen, hcen, -, -⟩ := hS
  have habs := centralizer_oddFit_le hgen hcen
  have hKH : normalClosureIn H A ≤ H := Subgroup.map_subtype_le _
  have hKn : ((normalClosureIn H A).subgroupOf H).Normal := by
    have h : (normalClosureIn H A).subgroupOf H =
        Subgroup.normalClosure ((A.subgroupOf H : Subgroup H) : Set H) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [h]
    infer_instance
  have hKN : H ≤ Subgroup.normalizer ((normalClosureIn H A : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn
  have hF : (CFSG.fittingSubgroup (normalClosureIn H A)).map (normalClosureIn H A).subtype ≤
      CFSG.fittingSubgroupOf H := by
    set FG := (CFSG.fittingSubgroup (normalClosureIn H A)).map (normalClosureIn H A).subtype
      with hFG
    have hFGH : FG ≤ H := (Subgroup.map_subtype_le _).trans hKH
    have hFGn : (FG.subgroupOf H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hFGH]
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact CFSG.Walter.conj_mem_map_of_characteristic (hKN hh) hx
      · intro hx
        have := CFSG.Walter.conj_mem_map_of_characteristic (Subgroup.inv_mem _ (hKN hh)) hx
        rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this
    have hFGnil : Group.IsNilpotent (FG.subgroupOf H) :=
      Group.nilpotent_of_mulEquiv ((Subgroup.equivMapOfInjective _ _
        (normalClosureIn H A).subtype_injective).trans (Subgroup.subgroupOfEquivOfLe hFGH).symm)
    have hle : FG.subgroupOf H ≤ CFSG.fittingSubgroup H := le_fitting hFGn hFGnil
    intro x hx
    exact ⟨⟨x, hFGH hx⟩, hle hx, rfl⟩
  have hE : (goldschmidtLayer (normalClosureIn H A)).map (normalClosureIn H A).subtype ≤
      GorensteinWalter.componentLayerOf H := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    apply le_sSup
    exact CFSG.Walter.isComponentOf_of_isSubnormal hKH hKn.isSubnormal
      (CFSG.Walter.isComponentOf_map_subtype (gw_isComponentOf_of_open hL))
  intro x ⟨hxK, hxC⟩
  have hx' : (⟨x, hxK⟩ : normalClosureIn H A) ∈
      Subgroup.centralizer (oddFit (normalClosureIn H A) : Set (normalClosureIn H A)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hyG : (y : G) ∈ oddCoreOf (CFSG.fittingSubgroupOf (normalClosureIn H A)) := by
      rw [oddCoreOf_fittingSubgroupOf]
      exact ⟨y, hy, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hxC _ hyG
  have h1 : x ∈ (CFSG.fittingSubgroup (normalClosureIn H A) ⊔
      goldschmidtLayer (normalClosureIn H A)).map (normalClosureIn H A).subtype :=
    ⟨_, habs hx', rfl⟩
  rw [Subgroup.map_sup] at h1
  exact sup_le_sup hF hE h1

end Transport

end G3a

open G3a in
theorem G31 : S_G31 := by
  intro G _ _ H A hS
  exact ⟨fun L hL => ⟨(part_ab hS hL).1, (part_ab hS hL).2, part_c hS hL⟩, part_d hS⟩

end CFSG.Goldschmidt
