module

public import CFSG.LocalAnalysis.ABGTheoremB.V4Basic
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ABGTheoremB.V4Inputs

public section

namespace CFSG.ABGTheoremB.V4

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGTheoremB.TotallyInverted
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {J W : Subgroup G}

@[expose] def primesNe (p : ℕ) : Set Nat.Primes := {q | (q : ℕ) ≠ p}

theorem isPiSubgroup_primesNe {K : Type*} [Group K] {p : ℕ} {U : Subgroup K}
    (hU : ¬ p ∣ Nat.card U) : CFSG.IsPiSubgroup (primesNe p) U := by
  intro q hq hqp
  rw [hqp] at hq
  exact hU hq

omit [Finite G] in
theorem commutator_mul_right (a b c : G) :
    a * (b * c) * a⁻¹ * (b * c)⁻¹ = (a * b * a⁻¹ * b⁻¹) * (b * (a * c * a⁻¹ * c⁻¹) * b⁻¹) := by
  group

theorem commutator_mem_pCore_of_mem_C_inf_L₀ (hσ : σ.IsValid) (hJ : σ.IsV21Layer J)
    (h31 : LemmaV31Input σ J) (hW : W ∈ σ.familyW J) {w z : G} (hw : w ∈ W) (hzC : z ∈ σ.C)
    (hzL : z ∈ σ.L₀) : w * z * w⁻¹ * z⁻¹ ∈ pCoreIn σ.p σ.N := by
  obtain ⟨j, hj, o, ho, rfl⟩ := exists_mul_eq_of_mem_C_inf_L₀ hσ hJ hzC hzL
  rw [commutator_mul_right]
  have hwJ : w ∈ J := hW.1 hw
  have hwC : w ∈ σ.C := W_le_C hσ hJ hW hw
  refine Subgroup.mul_mem _ (h31.comm w ⟨hwC, hwJ⟩ j hj) ?_
  refine (Subgroup.mem_normalizer_iff.mp (N_le_normalizer_pCore (J_le_N hσ hJ hj.2)) _).mp ?_
  apply hJ.commutator_le
  exact Subgroup.commutator_mem_commutator hwJ ho

theorem not_dvd_card_of_isHallSubgroup {K : Type*} [Group K] {p : ℕ} (hp : p.Prime)
    {X : Subgroup K} (hX : CFSG.IsHallSubgroup (primesNe p) X) : ¬ p ∣ Nat.card X := by
  intro h
  exact hX.p_in_pi_of_p_dvd_card ⟨p, hp⟩ h rfl

theorem lemmaV42 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hJ : σ.IsV21Layer J)
    (h31 : LemmaV31Input σ J) (hN' : CommutatorInput σ) (h42 : LemmaII42Input σ J)
    (hW : W ∈ σ.familyW J) (i : Fin 3) :
    ∃ g ∈ Subgroup.normalizer (σ.T : Set G), g * σ.x * g⁻¹ = σ.xs i ∧ W ≤ conjSub g σ.L := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  set OC := oddCoreIn σ.C with hOC
  have hsolv : Group.IsSolvable OC := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_oddCoreIn σ.C)
  have hWOC : W ≤ OC := W_le_oddCoreIn_C hσ hJ hW
  have hWpi : CFSG.IsPiSubgroup (primesNe σ.p) (W.subgroupOf OC) := by
    apply isPiSubgroup_primesNe
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWOC).toEquiv]
    exact h31.coprime W hW
  obtain ⟨X₀, hX₀, hWX₀⟩ :=
    CFSG.SolvableHall.solvable_hall_containment hsolv (primesNe σ.p) _ hWpi
  set X : Subgroup G := X₀.map OC.subtype with hXdef
  have hXOC : X ≤ OC := Subgroup.map_subtype_le _
  have hWX : W ≤ X := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hWOC]
    exact Subgroup.map_mono hWX₀
  have hcardX : Nat.card X = Nat.card X₀ :=
    Nat.card_congr (X₀.equivMapOfInjective OC.subtype OC.subtype_injective).toEquiv.symm
  have hXp : ¬ σ.p ∣ Nat.card X := hcardX ▸ not_dvd_card_of_isHallSubgroup hσ.p_prime hX₀
  have hXOp : X ⊓ pCoreIn σ.p σ.N = ⊥ := by
    apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (DataConstruction.isPGroup_pCoreIn σ.p σ.N)
    rw [ha]
    exact (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hσ.p_prime).mpr hXp)).symm
  set Y : Subgroup G := X ⊓ Subgroup.centralizer ((⁅X, X⁆ : Subgroup G) : Set G) with hYdef
  have hXN : X ≤ σ.N := (hXOC.trans (oddCoreIn_le σ.C)).trans σ.C_le_N
  have hXX : ⁅X, X⁆ ≤ X := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)
  have hWY : W ≤ Y := by
    intro w hw
    refine Subgroup.mem_inf.mpr ⟨hWX hw, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzC : z ∈ σ.C := oddCoreIn_le σ.C (hXOC (hXX hz))
    have hzL : z ∈ σ.L₀ := hN' (Subgroup.commutator_mono hXN hXN hz)
    have h1 := commutator_mem_pCore_of_mem_C_inf_L₀ hσ hJ h31 hW hw hzC hzL
    have h2 : w * z * w⁻¹ * z⁻¹ ∈ X := by
      have hzX : z ∈ X := hXX hz
      exact X.mul_mem (X.mul_mem (X.mul_mem (hWX hw) hzX) (X.inv_mem (hWX hw))) (X.inv_mem hzX)
    have h3 : w * z * w⁻¹ * z⁻¹ ∈ X ⊓ pCoreIn σ.p σ.N := ⟨h2, h1⟩
    rw [hXOp, Subgroup.mem_bot] at h3
    calc z * w = (w * z * w⁻¹ * z⁻¹)⁻¹ * w * z := by group
      _ = w * z := by rw [h3, inv_one, one_mul]
  have hYL : Y ≤ σ.L := by
    intro y hy
    refine h42 W hW X hXOC hWX y hy.1 (fun z hz => ?_)
    have hyz : z * y = y * z := Subgroup.mem_centralizer_iff.mp hy.2 z hz
    rw [show y * z * y⁻¹ * z⁻¹ = 1 by rw [← hyz]; group]
    exact σ.ON.one_mem
  obtain ⟨g, hgT, hgi⟩ := exists_conj_x_eq_xs hσ hII i
  have hgOC : conjSub g OC = OC := conjSub_oddCoreIn_C hgT
  set X₁ : Subgroup OC := (conjSub g X).subgroupOf OC with hX₁
  have hgXOC : conjSub g X ≤ OC := hgOC ▸ DataConstruction.conjSub_mono hXOC
  have hcardX₁ : Nat.card X₁ = Nat.card X₀ := by
    rw [hX₁, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hgXOC).toEquiv,
      DataConstruction.card_conjSub, hcardX]
  have hX₁hall : CFSG.IsHallSubgroup (primesNe σ.p) X₁ := by
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · rw [hcardX₁] at hq
      exact hX₀.p_in_pi_of_p_dvd_card q hq
    · apply hX₀.p_in_pi_of_p_dvd_index q
      have e : X₁.index = X₀.index := by
        have h1 := X₁.card_mul_index
        have h2 := X₀.card_mul_index
        rw [hcardX₁] at h1
        exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
      rwa [← e]
  obtain ⟨c, hc⟩ := CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable hsolv hX₀ hX₁hall
  have hgc : conjSub g X = conjSub (c : G) X := by
    have := congrArg (Subgroup.map OC.subtype) hc
    rw [hX₁, Subgroup.map_subgroupOf_eq_of_le hgXOC, Subgroup.map_map] at this
    rw [this, hXdef, TotallyInverted.conjSub, Subgroup.map_map]
    congr 1
  set m : G := (c : G)⁻¹ * g with hmdef
  have hcC : (c : G) ∈ σ.C := oddCoreIn_le σ.C c.2
  have hcT : (c : G) ∈ Subgroup.normalizer (σ.T : Set G) :=
    Subgroup.centralizer_le_normalizer _ hcC
  have hmT : m ∈ Subgroup.normalizer (σ.T : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hcT) hgT
  have hmx : m * σ.x * m⁻¹ = σ.xs i := by
    have hcx : (c : G)⁻¹ * σ.xs i * (c : G) = σ.xs i := by
      rw [show (c : G)⁻¹ * σ.xs i * (c : G) = (c : G)⁻¹ * (σ.xs i * (c : G)) by group,
        (Subgroup.mem_centralizer_iff.mp hcC _ (Conjugacy.xs_mem_T i)), inv_mul_cancel_left]
    rw [hmdef, show (c : G)⁻¹ * g * σ.x * ((c : G)⁻¹ * g)⁻¹ =
      (c : G)⁻¹ * (g * σ.x * g⁻¹) * (c : G) by group, hgi, hcx]
  have hmX : conjSub m X = X := by
    rw [hmdef, ← DataConstruction.conjSub_conjSub, hgc, DataConstruction.conjSub_inv_conjSub]
  have hmY : conjSub m Y = Y := by
    rw [hYdef, DataConstruction.conjSub_inf, DataConstruction.conjSub_centralizer, hmX,
      TotallyInverted.conjSub, Subgroup.map_commutator, ← TotallyInverted.conjSub, hmX]
  refine ⟨m, hmT, hmx, ?_⟩
  calc W ≤ Y := hWY
    _ = conjSub m Y := hmY.symm
    _ ≤ conjSub m σ.L := DataConstruction.conjSub_mono hYL

end CFSG.ABGTheoremB.V4
