module

public import CFSG.ClassicalInvolution.Balance.BProperty
public import CFSG.ClassicalInvolution.LBalance
public import CFSG.LocalAnalysis.ComponentClassification.CentralTwoBInclusion
import CFSG.ClassicalInvolution.Balance.Quotient
import CFSG.ClassicalInvolution.LBalance.Main
import CFSG.ClassicalInvolution.PerfectCase.Basic

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.Assembly.Dichotomy
open scoped commutatorElement

section GroupLevel

theorem le_of_perfect_of_le_sup_of_commutator_eq_bot {W : Type*} [Group W] {S Q B : Subgroup W}
    [Q.Normal] (hS : ⁅S, S⁆ = S) (hSQB : S ≤ Q ⊔ B) (hSB : ⁅S, B⁆ = ⊥) : S ≤ Q := by
  set ψ := QuotientGroup.mk' Q with hψ
  have hQ : Q.map ψ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hle : S.map ψ ≤ B.map ψ := by
    refine (Subgroup.map_mono hSQB).trans ?_
    rw [Subgroup.map_sup, hQ, bot_sup_eq]
  have hcomm : ⁅S.map ψ, B.map ψ⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, hSB, Subgroup.map_bot]
  have hself : ⁅S.map ψ, S.map ψ⁆ = ⊥ :=
    le_bot_iff.mp (hcomm ▸ Subgroup.commutator_mono le_rfl hle)
  have hbot : S.map ψ = ⊥ := by
    have := Subgroup.map_commutator S S ψ
    rw [hS, hself] at this
    exact this
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

end GroupLevel

section Layer

variable {W : Type*} [Group W] [Finite W]

theorem commutator_oddCore_eq_bot_of_le_twoLayer {S : Subgroup W} (hS : ⁅S, S⁆ = S)
    (hSle : S ≤ TwoLayer.subgroup W)
    (hB : ∀ M : Subgroup W, TwoComponents.IsTwoComponent M →
      ¬ CFSG.Open.IsQuasisimple M → ⁅M, S⁆ = ⊥) :
    ⁅S, componentClassificationOddCore W⁆ = ⊥ := by
  have hbad : ⁅S, TwoComponents.badSubgroup W⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine sSup_le fun M hM => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hB M hM.1 hM.2)
  have : (TwoLayer.goodSubgroup W).Characteristic := TwoLayer.good_characteristic W
  have hSQ : S ≤ TwoLayer.goodSubgroup W :=
    le_of_perfect_of_le_sup_of_commutator_eq_bot hS (TwoLayer.good_sup_bad W ▸ hSle) hbad
  have hsub : IsSubnormal (componentClassificationOddCore W) ⊤ := by
    refine isSubnormal_of_normal_subgroupOf le_top ?_
    exact Subgroup.normal_subgroupOf
  have : Group.IsSolvable (componentClassificationOddCore W) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (OddCore.odd_card W)
  have hlayer := Layer.commutes_with_solvable_subnormal (componentClassificationOddCore W) hsub
  exact le_bot_iff.mp
    (hlayer ▸ Subgroup.commutator_mono (hSQ.trans (TwoLayer.good_le_layer W)) le_rfl)

end Layer

section Surjection

variable {Y Yb : Type*} [Group Y] [Finite Y] [Group Yb] [Finite Yb]

theorem map_twoLayer_le (ρ : Y →* Yb) (hρ : Function.Surjective ρ)
    (hker : Odd (Nat.card ρ.ker)) :
    (TwoLayer.subgroup Y).map ρ ≤ TwoLayer.subgroup Yb := by
  refine Subgroup.map_le_iff_le_comap.mpr (sSup_le fun M hM => ?_)
  exact Subgroup.map_le_iff_le_comap.mp
    (le_sSup (OddKernelTwoComponents.image ρ hρ hker M hM))

theorem map_commutatorElement_eq_one_of_le_twoLayer (ρ : Y →* Yb) (hρ : Function.Surjective ρ)
    (hker : Odd (Nat.card ρ.ker)) {L : Subgroup Y} (hL : ⁅L, L⁆ = L)
    (hLle : L ≤ TwoLayer.subgroup Y)
    (hB : ∀ M : Subgroup Yb, TwoComponents.IsTwoComponent M →
      CFSG.Open.IsQuasisimple M ∨ ⁅M, L.map ρ⁆ = ⊥)
    {a : Y} (ha : a ∈ componentClassificationOddCore Y) {l : Y} (hl : l ∈ L) :
    ρ ⁅a, l⁆ = 1 := by
  have hS : ⁅L.map ρ, L.map ρ⁆ = L.map ρ := by
    rw [← Subgroup.map_commutator, hL]
  have hSle : L.map ρ ≤ TwoLayer.subgroup Yb :=
    (Subgroup.map_mono hLle).trans (map_twoLayer_le ρ hρ hker)
  have hbot := commutator_oddCore_eq_bot_of_le_twoLayer hS hSle
    (fun M hM hnq => (hB M hM).resolve_left hnq)
  have hN : ((componentClassificationOddCore Y).map ρ).Normal :=
    Subgroup.Normal.map (componentClassificationOddCore_normal Y) ρ hρ
  have hodd : Odd (Nat.card ((componentClassificationOddCore Y).map ρ)) :=
    (OddCore.odd_card Y).of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hρa : ρ a ∈ componentClassificationOddCore Yb :=
    OddCore.maximal Yb _ hN hodd ⟨a, ha, rfl⟩
  have hmem : ⁅ρ l, ρ a⁆ ∈ ⁅L.map ρ, componentClassificationOddCore Yb⁆ :=
    Subgroup.commutator_mem_commutator ⟨l, hl, rfl⟩ hρa
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact hmem.symm

end Surjection

section Placement

theorem le_twoLayer_of_perfect_of_isSubnormal {W : Type*} [Group W] [Finite W] {M : Subgroup W}
    (hM : IsSubnormal M ⊤) (hperf : commutator M = ⊤)
    (hq : CFSG.Open.IsQuasisimple (M ⧸ componentClassificationOddCore M)) :
    M ≤ TwoLayer.subgroup W := by
  obtain ⟨L, hLM, hL, hmap⟩ := exists_isTwoComponent_le M hM hq
  have hres := twoResidual_le_subgroupOf_of_map_eq hLM hL.1 hM hmap
  have htop := twoResidual_eq_top_of_perfect hperf
  have hML : M ≤ L := by
    intro x hx
    have : (⟨x, hx⟩ : M) ∈ L.subgroupOf M := hres (htop ▸ Subgroup.mem_top _)
    exact this
  exact (le_antisymm hLM hML ▸ le_sSup hL : M ≤ TwoLayer.subgroup W)

theorem le_twoLayer_of_l2PrimeBalance (hLB : L2PrimeBalance) {W : Type} [Group W] [Finite W]
    {A L : Subgroup W} (hA : IsPGroup 2 A) (hLA : L ≤ Subgroup.centralizer (A : Set W))
    (hLsub : IsSubnormal L (Subgroup.centralizer (A : Set W))) (hLperf : commutator L = ⊤)
    (hLq : CFSG.Open.IsQuasisimple (L ⧸ componentClassificationOddCore L)) :
    L ≤ TwoLayer.subgroup W := by
  set Z : Subgroup W := Subgroup.centralizer (A : Set W) with hZ
  let e : (L.subgroupOf Z) ≃* L := Subgroup.subgroupOfEquivOfLe hLA
  have hsub : IsSubnormal (L.subgroupOf Z) ⊤ :=
    (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hLA).mpr hLsub
  have hperf : commutator (L.subgroupOf Z) = ⊤ := by
    have : Group.IsPerfect L := ⟨hLperf⟩
    have : Group.IsPerfect (L.subgroupOf Z) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hq : CFSG.Open.IsQuasisimple
      (↥(L.subgroupOf Z) ⧸ componentClassificationOddCore (L.subgroupOf Z)) :=
    Components.quasisimple_of_equiv
      (QuotientGroup.congr (componentClassificationOddCore (L.subgroupOf Z))
        (componentClassificationOddCore L) e (OddCore.equiv_invariant e)) hLq
  have h1 : L.subgroupOf Z ≤ TwoLayer.subgroup ↥Z :=
    le_twoLayer_of_perfect_of_isSubnormal hsub hperf hq
  have h2 : (CFSG.pLayer ↥Z 2).map Z.subtype ≤ CFSG.pLayer W 2 := hLB W A hA
  rw [LocalBFailure.pLayer_two_eq_twoLayer, LocalBFailure.pLayer_two_eq_twoLayer] at h2
  have h3 := Subgroup.map_mono (f := Z.subtype) h1
  rw [Subgroup.map_subgroupOf_eq_of_le hLA] at h3
  exact h3.trans h2

end Placement

section Assembly

variable {G : Type} [Group G] [Finite G]

@[expose] def imageModOddCore (f : G) (Y : Subgroup G) :
    Subgroup (↥(Subgroup.centralizer {f}) ⧸
      componentClassificationOddCore ↥(Subgroup.centralizer {f})) :=
  (Y.subgroupOf (Subgroup.centralizer {f})).map
    (QuotientGroup.mk' (componentClassificationOddCore (Subgroup.centralizer {f})))

theorem commutator_oddCoreIn_le_of_l2PrimeBalance (hLB : L2PrimeBalance) {C E₀ L₀ : Subgroup G}
    {f : G} (hE₀ : IsElemAbelian 2 E₀) (hf : f ∈ E₀) (hE₀C : E₀ ≤ C)
    (hL₀ : L₀ ≤ C ⊓ Subgroup.centralizer (E₀ : Set G))
    (hL₀sub : IsSubnormal L₀ (C ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hL₀perf : commutator L₀ = ⊤)
    (hL₀q : CFSG.Open.IsQuasisimple (L₀ ⧸ componentClassificationOddCore L₀))
    (hB : ∀ M : Subgroup ↥(imageModOddCore f (C ⊓ Subgroup.centralizer {f})),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M ∨
        ⁅M.map (imageModOddCore f (C ⊓ Subgroup.centralizer {f})).subtype,
          imageModOddCore f L₀⁆ = ⊥) :
    ⁅oddCoreIn (C ⊓ Subgroup.centralizer {f}), L₀⁆ ≤ involutionOddCore f := by
  set X : Subgroup G := Subgroup.centralizer {f} with hX
  set Y : Subgroup G := C ⊓ X with hY
  have hYX : Y ≤ X := inf_le_right
  have hE₀X : E₀ ≤ X := fun e he => by
    rw [hX, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hE₀.1.is_comm.comm (⟨e, he⟩ : E₀) ⟨f, hf⟩)
  have hE₀Y : E₀ ≤ Y := le_inf hE₀C hE₀X
  have hcentE : Subgroup.centralizer (E₀ : Set G) ≤ X :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hf)
  have hL₀Y : L₀ ≤ Y := fun l hl => ⟨(hL₀ hl).1, hcentE (hL₀ hl).2⟩
  let A : Subgroup ↥Y := E₀.subgroupOf Y
  let L : Subgroup ↥Y := L₀.subgroupOf Y
  let e : L ≃* L₀ := Subgroup.subgroupOfEquivOfLe hL₀Y
  have hApg : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (Subtype.ext (by
    simpa using hE₀.2 (x : G) x.2))⟩
  have hLA : L ≤ Subgroup.centralizer (A : Set ↥Y) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hL₀ hl).2 (a : G) ha)
  have hcent : (C ⊓ Subgroup.centralizer (E₀ : Set G)).subgroupOf Y =
      Subgroup.centralizer (A : Set ↥Y) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, hy⟩ a ha
      exact Subtype.ext (hy (a : G) ha)
    · intro hy
      refine ⟨y.2.1, fun h hh => ?_⟩
      exact congrArg Subtype.val (hy ⟨h, hE₀Y hh⟩ hh)
  have hLsub : IsSubnormal L (Subgroup.centralizer (A : Set ↥Y)) := by
    have h := CFSG.ComponentClassification.LBalance.subnormal_subgroupOf hL₀sub Y
    rwa [hcent] at h
  have hLperf : commutator L = ⊤ := by
    have : Group.IsPerfect L₀ := ⟨hL₀perf⟩
    have : Group.IsPerfect L :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hLq : CFSG.Open.IsQuasisimple (↥L ⧸ componentClassificationOddCore L) :=
    Components.quasisimple_of_equiv
      (QuotientGroup.congr (componentClassificationOddCore L) (componentClassificationOddCore L₀)
        e (OddCore.equiv_invariant e)) hL₀q
  have h1 : L ≤ TwoLayer.subgroup ↥Y :=
    le_twoLayer_of_l2PrimeBalance hLB hApg hLA hLsub hLperf hLq
  let π : ↥X →* ↥X ⧸ componentClassificationOddCore ↥X := QuotientGroup.mk' _
  let incl : ↥Y →* ↥X := Subgroup.inclusion hYX
  let ρ0 : ↥Y →* ↥X ⧸ componentClassificationOddCore ↥X := π.comp incl
  have hρ0 : ∀ y : ↥Y, ρ0 y ∈ imageModOddCore f Y := fun y =>
    ⟨incl y, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
  let ρ : ↥Y →* ↥(imageModOddCore f Y) := ρ0.codRestrict (imageModOddCore f Y) hρ0
  have hρsurj : Function.Surjective ρ := fun z => by
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp z.2
    exact ⟨⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext hxz⟩
  have hρker : Odd (Nat.card ρ.ker) := by
    have hk : ρ.ker = (componentClassificationOddCore ↥X).comap incl := by
      ext y
      change ρ y = 1 ↔ incl y ∈ componentClassificationOddCore ↥X
      rw [← QuotientGroup.eq_one_iff (N := componentClassificationOddCore ↥X) (incl y)]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hk]
    exact (OddCore.odd_card ↥X).of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective _ incl (Subgroup.inclusion_injective hYX))
  have hLimage : (L.map ρ).map (imageModOddCore f Y).subtype = imageModOddCore f L₀ := by
    rw [Subgroup.map_map]
    have hcomp : (imageModOddCore f Y).subtype.comp ρ = ρ0 := rfl
    rw [hcomp]
    have hLX : L.map incl = L₀.subgroupOf X := by
      ext x
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact hl
      · intro hx
        exact ⟨⟨x.1, hL₀Y hx⟩, hx, rfl⟩
    show L.map (π.comp incl) = _
    rw [← Subgroup.map_map, hLX]
    rfl
  have hB' : ∀ M : Subgroup ↥(imageModOddCore f Y), TwoComponents.IsTwoComponent M →
      CFSG.Open.IsQuasisimple M ∨ ⁅M, L.map ρ⁆ = ⊥ := by
    intro M hM
    rcases hB M hM with hq | hc
    · exact Or.inl hq
    · refine Or.inr ?_
      apply Subgroup.map_injective (imageModOddCore f Y).subtype_injective
      rw [Subgroup.map_commutator, hLimage, hc, Subgroup.map_bot]
  have hLself : ⁅L, L⁆ = L := by
    have : Group.IsPerfect L := ⟨hLperf⟩
    exact Subgroup.commutator_eq_self
  rw [Subgroup.commutator_le]
  rintro _ ⟨a, ha, rfl⟩ l hl
  have hl' : (⟨l, hL₀Y hl⟩ : ↥Y) ∈ L := hl
  have h := map_commutatorElement_eq_one_of_le_twoLayer ρ hρsurj hρker hLself h1 hB' ha hl'
  have h2 : π (incl ⁅a, (⟨l, hL₀Y hl⟩ : ↥Y)⁆) = 1 := congrArg Subtype.val h
  exact ⟨incl ⁅a, (⟨l, hL₀Y hl⟩ : ↥Y)⁆, (QuotientGroup.eq_one_iff _).mp h2, rfl⟩

theorem commutator_oddCoreIn_normalClosureIn_le_of_l2PrimeBalance (hLB : L2PrimeBalance)
    {C E₀ L₀ : Subgroup G} {f : G} (hE₀ : IsElemAbelian 2 E₀) (hf : f ∈ E₀) (hE₀C : E₀ ≤ C)
    (hL₀ : L₀ ≤ C ⊓ Subgroup.centralizer (E₀ : Set G))
    (hL₀sub : IsSubnormal L₀ (C ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hL₀perf : commutator L₀ = ⊤)
    (hL₀q : CFSG.Open.IsQuasisimple (L₀ ⧸ componentClassificationOddCore L₀))
    (hB : ∀ M : Subgroup ↥(imageModOddCore f (C ⊓ Subgroup.centralizer {f})),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M ∨
        ⁅M.map (imageModOddCore f (C ⊓ Subgroup.centralizer {f})).subtype,
          imageModOddCore f L₀⁆ = ⊥) :
    ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
      normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f := by
  have hweak := commutator_oddCoreIn_le_of_l2PrimeBalance hLB hE₀ hf hE₀C hL₀ hL₀sub hL₀perf
    hL₀q hB
  set X : Subgroup G := Subgroup.centralizer {f} with hX
  set Y : Subgroup G := C ⊓ X with hY
  have hYX : Y ≤ X := inf_le_right
  have hcentE : Subgroup.centralizer (E₀ : Set G) ≤ X :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hf)
  have hL₀Y : L₀ ≤ Y := fun l hl => ⟨(hL₀ hl).1, hcentE (hL₀ hl).2⟩
  set N : Subgroup G := involutionOddCore f with hN
  have hNnorm : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn => conj_mem_oddCoreIn hg hn
  let D : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ ∀ t ∈ oddCoreIn Y, ⁅t, y⁆ ∈ N}
      one_mem' := ⟨one_mem Y, fun t _ => by simp⟩
      mul_mem' := fun {y₁ y₂} h₁ h₂ => ⟨Y.mul_mem h₁.1 h₂.1, fun t ht => by
        have : ⁅t, y₁ * y₂⁆ = ⁅t, y₁⁆ * (y₁ * ⁅t, y₂⁆ * y₁⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [this]
        exact N.mul_mem (h₁.2 t ht) (hNnorm y₁ (hYX h₁.1) _ (h₂.2 t ht))⟩
      inv_mem' := fun {y} h => ⟨Y.inv_mem h.1, fun t ht => by
        have : ⁅t, y⁻¹⁆ = y⁻¹ * ⁅t, y⁆⁻¹ * y⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [this]
        exact hNnorm y⁻¹ (hYX (Y.inv_mem h.1)) _ (N.inv_mem (h.2 t ht))⟩ }
  have hLD : L₀ ≤ D := fun l hl => ⟨hL₀Y hl, fun t ht =>
    hweak (Subgroup.commutator_mem_commutator ht hl)⟩
  have hDnorm : ∀ g ∈ Y, ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    intro g hg d hd
    refine ⟨Y.mul_mem (Y.mul_mem hg hd.1) (Y.inv_mem hg), fun t ht => ?_⟩
    have ht' : g⁻¹ * t * g⁻¹⁻¹ ∈ oddCoreIn Y := conj_mem_oddCoreIn (Y.inv_mem hg) ht
    have : ⁅t, g * d * g⁻¹⁆ = g * ⁅g⁻¹ * t * g⁻¹⁻¹, d⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact hNnorm g (hYX hg) _ (hd.2 _ ht')
  have hND : normalClosureIn Y L₀ ≤ D := by
    refine normalClosureIn_le fun g hg => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hDnorm g hg x (hLD hx)
  have hOle : oddCoreIn (normalClosureIn Y L₀) ≤ oddCoreIn Y :=
    oddCoreIn_le_of_isSubnormal (isSubnormal_normalClosureIn hL₀Y)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact (hND hb).2 a (hOle ha)

theorem isQuasisimple_of_deltaTrivial_of_l2PrimeBalance (hLB : L2PrimeBalance)
    {C K E₀ L₀ : Subgroup G} (hKC : IsSubnormal K C) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀K : E₀ ≤ K) (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hL₀sub : IsSubnormal L₀ (C ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hL₀q : CFSG.Open.IsQuasisimple (L₀ ⧸ componentClassificationOddCore L₀))
    (hB : ∀ f ∈ E₀, f ≠ 1 → ∀ M : Subgroup ↥(imageModOddCore f (C ⊓ Subgroup.centralizer {f})),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M ∨
        ⁅M.map (imageModOddCore f (C ⊓ Subgroup.centralizer {f})).subtype,
          imageModOddCore f L₀⁆ = ⊥) :
    CFSG.Open.IsQuasisimple K := by
  have hKC' : K ≤ C := isSubnormal_le hKC
  refine isQuasisimple_of_deltaTrivial hKC hKperf hKq hE₀K hE₀ hE₀card hL₀K hL₀E hL₀ hL₀ne hΔ
    fun f hf hf1 => ?_
  exact commutator_oddCoreIn_normalClosureIn_le_of_l2PrimeBalance hLB hE₀ hf (hE₀K.trans hKC')
    (le_inf (hL₀K.trans hKC') hL₀E) hL₀sub hL₀ hL₀q (hB f hf hf1)

theorem isQuasisimple_of_deltaTrivial_of_kGroup (hLB : L2PrimeBalance)
    {C K E₀ L₀ : Subgroup G} (hKC : IsSubnormal K C) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀K : E₀ ≤ K) (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hL₀sub : IsSubnormal L₀ (C ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hL₀q : CFSG.Open.IsQuasisimple (L₀ ⧸ componentClassificationOddCore L₀))
    (hB : ∀ f ∈ E₀, f ≠ 1 → ∀ M : Subgroup ↥(imageModOddCore f (C ⊓ Subgroup.centralizer {f})),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M) :
    CFSG.Open.IsQuasisimple K :=
  isQuasisimple_of_deltaTrivial_of_l2PrimeBalance hLB hKC hKperf hKq hE₀K hE₀ hE₀card hL₀K hL₀E
    hL₀ hL₀ne hΔ hL₀sub hL₀q fun f hf hf1 M hM => Or.inl (hB f hf hf1 M hM)

omit [Finite G] in
theorem isSubnormal_inf_centralizer_of_isSubnormal {C E₀ L₀ : Subgroup G} {z₀ : G} (hz₀ : z₀ ∈ E₀)
    (hL₀ : L₀ ≤ C ⊓ Subgroup.centralizer (E₀ : Set G))
    (hsub : IsSubnormal L₀ (Subgroup.centralizer {z₀})) :
    IsSubnormal L₀ (C ⊓ Subgroup.centralizer (E₀ : Set G)) := by
  have h := isSubnormal_inf hsub (C ⊓ Subgroup.centralizer (E₀ : Set G))
  rwa [inf_eq_left.mpr hL₀, inf_eq_right.mpr (inf_le_right.trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz₀)))] at h

theorem imageModOddCore_centralizer {f t : G} (ht : t ∈ Subgroup.centralizer {f})
    (h2 : IsPGroup 2 (Subgroup.zpowers t)) :
    imageModOddCore f (Subgroup.centralizer {t} ⊓ Subgroup.centralizer {f}) =
      Subgroup.centralizer {QuotientGroup.mk' (componentClassificationOddCore
        (Subgroup.centralizer {f})) (⟨t, ht⟩ : ↥(Subgroup.centralizer {f}))} := by
  set X : Subgroup G := Subgroup.centralizer {f} with hX
  let t' : ↥X := ⟨t, ht⟩
  have hsub : (Subgroup.centralizer {t} ⊓ X).subgroupOf X = Subgroup.centralizer {t'} := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨h, -⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp h))
    · intro h
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp h)), x.2⟩
  have hpg : IsPGroup 2 (Subgroup.zpowers t') := by
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, ← hk, Nat.card_zpowers, ← Subgroup.orderOf_coe t']
  unfold imageModOddCore
  rw [hsub]
  exact map_centralizer_singleton_eq (OddCore.odd_card ↥X) hpg

theorem isQuasisimple_of_deltaTrivial_of_layer
    {C K E₀ L₀ : Subgroup G} (hKC : IsSubnormal K C) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀K : E₀ ≤ K) (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hL₀sub : IsSubnormal L₀ (C ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hL₀q : CFSG.Open.IsQuasisimple (L₀ ⧸ componentClassificationOddCore L₀))
    (hB : ∀ f ∈ E₀, f ≠ 1 → ∀ M : Subgroup ↥(imageModOddCore f (C ⊓ Subgroup.centralizer {f})),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M ∨
        ⁅M.map (imageModOddCore f (C ⊓ Subgroup.centralizer {f})).subtype,
          imageModOddCore f L₀⁆ = ⊥) :
    CFSG.Open.IsQuasisimple K :=
  isQuasisimple_of_deltaTrivial_of_l2PrimeBalance l2PrimeBalance hKC hKperf hKq hE₀K hE₀ hE₀card
    hL₀K hL₀E hL₀ hL₀ne hΔ hL₀sub hL₀q hB

theorem isQuasisimple_of_isTwoComponent_of_l2PrimeBalance (hLB : L2PrimeBalance)
    {C K E₀ L₀ : Subgroup G} (hKC : K ≤ C) (hK : TwoComponents.IsTwoComponent (K.subgroupOf C))
    (hE₀K : E₀ ≤ K) (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hL₀sub : IsSubnormal L₀ (C ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hL₀q : CFSG.Open.IsQuasisimple (L₀ ⧸ componentClassificationOddCore L₀))
    (hB : ∀ f ∈ E₀, f ≠ 1 → ∀ M : Subgroup ↥(imageModOddCore f (C ⊓ Subgroup.centralizer {f})),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M ∨
        ⁅M.map (imageModOddCore f (C ⊓ Subgroup.centralizer {f})).subtype,
          imageModOddCore f L₀⁆ = ⊥) :
    CFSG.Open.IsQuasisimple K :=
  isQuasisimple_of_isTwoComponent_of_deltaTrivial hKC hK hE₀K hE₀ hE₀card hL₀K hL₀E hL₀ hL₀ne hΔ
    fun f hf hf1 =>
      commutator_oddCoreIn_normalClosureIn_le_of_l2PrimeBalance hLB hE₀ hf (hE₀K.trans hKC)
        (le_inf (hL₀K.trans hKC) hL₀E) hL₀sub hL₀ hL₀q (hB f hf hf1)

end Assembly

section BInclusion

theorem isQuasisimple_of_isTwoComponent_centralizer {X : Type*} [Group X] [Finite X]
    (hcore : componentClassificationOddCore X = ⊥) (hinc : CentralTwoBInclusion.Property X)
    {t : X} (ht : orderOf t = 2) (M : Subgroup (Subgroup.centralizer ({t} : Set X)))
    (hM : TwoComponents.IsTwoComponent M) : CFSG.Open.IsQuasisimple M :=
  (LocalB.ordinary_at_involution (CentralTwoBInclusion.localB_of_corefree hcore hinc) t ht M
    hM).2.2

theorem forall_isTwoComponent_isQuasisimple_of_eq {X : Type*} [Group X] {A B : Subgroup X}
    (h : A = B) (hB : ∀ M : Subgroup ↥B, TwoComponents.IsTwoComponent M →
      CFSG.Open.IsQuasisimple M) :
    ∀ M : Subgroup ↥A, TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M := by
  subst h
  exact hB

theorem orderOf_mk_oddCore_eq_two {X : Type*} [Group X] [Finite X] {x : X} (hx : orderOf x = 2) :
    orderOf (QuotientGroup.mk' (componentClassificationOddCore X) x) = 2 := by
  have h2 : (QuotientGroup.mk' (componentClassificationOddCore X) x) ^ 2 = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have h1 : QuotientGroup.mk' (componentClassificationOddCore X) x ≠ 1 := by
    intro h
    have hmem : x ∈ componentClassificationOddCore X := (QuotientGroup.eq_one_iff x).mp h
    have hdvd := orderOf_dvd_natCard (⟨x, hmem⟩ : componentClassificationOddCore X)
    rw [Subgroup.orderOf_mk, hx] at hdvd
    exact (Nat.not_even_iff_odd.mpr (OddCore.odd_card X)) (even_iff_two_dvd.mpr hdvd)
  exact orderOf_eq_prime h2 h1

theorem mem_centralizer_singleton_of_isElemAbelian {G : Type*} [Group G] {E₀ : Subgroup G}
    (hE₀ : IsElemAbelian 2 E₀) {f t : G} (hf : f ∈ E₀) (ht : t ∈ E₀) :
    t ∈ Subgroup.centralizer {f} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (hE₀.1.is_comm.comm (⟨t, ht⟩ : E₀) ⟨f, hf⟩)

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_imageModOddCore_of_bInclusion {f t : G} (hft : t ∈ Subgroup.centralizer {f})
    (ht : orderOf t = 2)
    (hinc : CentralTwoBInclusion.Property (↥(Subgroup.centralizer {f}) ⧸
      componentClassificationOddCore ↥(Subgroup.centralizer {f})))
    (M : Subgroup ↥(imageModOddCore f (Subgroup.centralizer {t} ⊓ Subgroup.centralizer {f})))
    (hM : TwoComponents.IsTwoComponent M) : CFSG.Open.IsQuasisimple M := by
  have hpg : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using ht)
  have heq := imageModOddCore_centralizer hft hpg
  have hord : orderOf (⟨t, hft⟩ : ↥(Subgroup.centralizer {f})) = 2 := by
    rw [Subgroup.orderOf_mk, ht]
  exact forall_isTwoComponent_isQuasisimple_of_eq heq (fun M' hM' =>
    isQuasisimple_of_isTwoComponent_centralizer (OddCore.quotient_corefree _) hinc
      (orderOf_mk_oddCore_eq_two hord) M' hM') M hM

theorem isQuasisimple_of_deltaTrivial_of_bInclusion
    {K E₀ L₀ : Subgroup G} {z₀ : G} (hz₀E : z₀ ∈ E₀) (hz₀ : z₀ ≠ 1)
    (hKC : IsSubnormal K (Subgroup.centralizer {z₀})) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀K : E₀ ≤ K) (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hL₀sub : IsSubnormal L₀ (Subgroup.centralizer {z₀} ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hL₀q : CFSG.Open.IsQuasisimple (L₀ ⧸ componentClassificationOddCore L₀))
    (hinc : ∀ f ∈ E₀, f ≠ 1 → CentralTwoBInclusion.Property (↥(Subgroup.centralizer {f}) ⧸
      componentClassificationOddCore ↥(Subgroup.centralizer {f}))) :
    CFSG.Open.IsQuasisimple K :=
  isQuasisimple_of_deltaTrivial_of_kGroup l2PrimeBalance hKC hKperf hKq hE₀K hE₀ hE₀card hL₀K hL₀E
    hL₀ hL₀ne hΔ hL₀sub hL₀q fun f hf hf1 M hM =>
      isQuasisimple_imageModOddCore_of_bInclusion (mem_centralizer_singleton_of_isElemAbelian hE₀
        hf hz₀E) (orderOf_eq_prime (hE₀.2 z₀ hz₀E) hz₀) (hinc f hf hf1) M hM

end BInclusion

end CFSG.ClassicalInvolution.Balance
