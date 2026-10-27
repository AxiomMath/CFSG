module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54GL

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem y7c_isE_of_isElemAbelian {G : Type} [Group G] [Finite G] {W : Subgroup G}
    (hW : IsElemAbelian 2 W) {n : ℕ} (hc : Nat.card W = 2 ^ n) : IsE n ↥W := by
  refine ⟨⟨IsMulCommutative.of_comm ?_, ?_⟩, hc⟩
  · intro x y
    exact Subtype.ext (hW.1.is_comm.comm x.1 y.1)
  · intro x _
    apply Subtype.ext
    have hx := hW.2 (x : G) x.2
    simpa using hx

theorem y7c_mulAut_fix_le_two {F : Type} [Group F] [Finite F] (hF : IsE 3 F)
    (Dh : Subgroup (MulAut F)) (hD : Nat.card Dh = 8) :
    Nat.card {w : F // ∀ φ ∈ Dh, φ w = w} ≤ 2 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  by_contra hleS
  have hS : 2 < Nat.card {w : F // ∀ φ ∈ Dh, φ w = w} := not_le.mp hleS
  haveI : Fintype {w : F // ∀ φ ∈ Dh, φ w = w} := Fintype.ofFinite _
  let oneS : {w : F // ∀ φ ∈ Dh, φ w = w} := ⟨1, fun φ _ => map_one φ⟩
  let S1 := {x : {w : F // ∀ φ ∈ Dh, φ w = w} // x ≠ oneS}
  have hS1card : Nat.card S1 = Nat.card {w : F // ∀ φ ∈ Dh, φ w = w} - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x => x = oneS),
      Nat.card_eq_fintype_card]
    simp
  have hltS1 : 1 < Nat.card S1 := by
    rw [hS1card]
    omega
  have hltS1' : 1 < Fintype.card S1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hltS1
  obtain ⟨a1, b1, hab1⟩ := Fintype.exists_pair_of_one_lt_card hltS1'
  let a : F := a1.1.1
  let b : F := b1.1.1
  have hfixa : ∀ φ ∈ Dh, φ a = a := a1.1.2
  have ha1ne : a ≠ 1 := fun h => a1.2 (Subtype.ext h)
  have hfixb : ∀ φ ∈ Dh, φ b = b := b1.1.2
  have hb1ne : b ≠ 1 := fun h => b1.2 (Subtype.ext h)
  have hab : a ≠ b := fun h => hab1 (Subtype.ext (Subtype.ext h))
  have horbit : MulAction.orbit (MulAut F) (a, b)
      = {p : F × F | p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.1 ≠ p.2} := by
    ext p
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨α, rfl⟩
      change α a ≠ 1 ∧ α b ≠ 1 ∧ α a ≠ α b
      exact ⟨fun h => ha1ne (α.injective (by rw [h, map_one])),
        fun h => hb1ne (α.injective (by rw [h, map_one])),
        fun h => hab (α.injective h)⟩
    · rintro ⟨hp1, hp2, hpne⟩
      obtain ⟨α, hαa, hαb⟩ := gl_trans2 hF ha1ne hb1ne hab hp1 hp2 hpne
      refine ⟨α, ?_⟩
      ext <;> simp [MulAut.smul_def, hαa, hαb]
  have hcardOrbit : Nat.card ↥(MulAction.orbit (MulAut F) (a, b)) = 42 := by
    rw [Nat.card_coe_set_eq, horbit]
    let t : Finset F := Finset.univ.filter (fun x => x ≠ 1)
    have ht : (t : Set F) = {x : F | x ≠ 1} := by ext x; simp [t]
    have hset : ({p : F × F | p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.1 ≠ p.2} : Set (F × F))
        = (t.offDiag : Set (F × F)) := by
      ext p
      rw [Finset.coe_offDiag, ht]
      simp only [Set.mem_offDiag, Set.mem_setOf_eq]
    rw [hset, Set.ncard_coe_finset, Finset.offDiag_card]
    have htcard : t.card = 7 := by
      have hcard_ne1 : ({x : F | x ≠ 1} : Set F).ncard = 7 := by
        have hset2 : ({x : F | x ≠ 1} : Set F) = Set.univ \ {1} := by ext x; simp
        rw [hset2, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ (1 : F)),
          Set.ncard_univ, hF.2]
        norm_num
      rw [← Set.ncard_coe_finset t, ht]
      exact hcard_ne1
    rw [htcard]
  let Stab := MulAction.stabilizer (MulAut F) (a, b)
  have hstab : Nat.card Stab = 4 := by
    have h := Nat.card_congr
      (MulAction.orbitProdStabilizerEquivGroup (G := MulAut F) (a, b))
    rw [Nat.card_prod, hcardOrbit, gl_card hF] at h
    have h42 : 42 * Nat.card Stab = 168 := h
    omega
  have hle : Dh ≤ Stab := by
    intro α hα
    rw [MulAction.mem_stabilizer_iff]
    exact Prod.ext (by simpa [MulAut.smul_def] using hfixa α hα)
      (by simpa [MulAut.smul_def] using hfixb α hα)
  have hcard_le : Nat.card Dh ≤ Nat.card Stab := by
    refine Nat.card_le_card_of_injective
      (fun α : Dh => (⟨α.1, hle α.2⟩ : Stab)) ?_
    intro x y hxy
    exact Subtype.ext (congrArg (Subtype.val : Stab → MulAut F) hxy)
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
