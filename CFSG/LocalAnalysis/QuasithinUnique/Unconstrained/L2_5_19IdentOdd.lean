module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentOrd
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryKernelsRootCenter

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Ch1
open BenderSuzuki.MatrixGroups CFSG.Glauberman.Dickson CFSG.Glauberman.Dickson.MaxUp

section L2Odd

variable {G : Type} [Group G] [Finite G]

theorem tabIdentFor_l2Odd
    : TabIdentFor @Ident.FamL2Odd := by
  intro G _ _ X K t hs hX
  exfalso
  obtain ⟨p, -, hadm, F, _, _, hcard, ⟨e⟩⟩ := hX
  have : Fact p.Prime := ⟨hadm.1⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hadm.2.2.2.1 (by simp)
  let e' : ↥X ≃* PSL2MatrixGroup F :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  let H : Subgroup (PSL2MatrixGroup F) := (K.subgroupOf X).map e'.toMonoidHom
  let eH : ↥K ≃* ↥H := (Subgroup.subgroupOfEquivOfLe hs.K_le).symm.trans
    (Subgroup.equivMapOfInjective _ e'.toMonoidHom e'.injective)
  obtain ⟨hsimple, a, b, hab⟩ := isKType_simple hs.ktype
  have hsimpH : IsSimpleGroup ↥H := eH.symm.isSimpleGroup
  have hncH : ¬ ∀ a b : ↥H, a * b = b * a := by
    intro h
    exact hab (eH.injective (by rw [map_mul, map_mul]; exact h _ _))
  have hHcard : Nat.card ↥H = Nat.card ↥K := (Nat.card_congr eH.toEquiv).symm
  have hXcard : Nat.card ↥X = p ^ 1 * ((p ^ 1) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e'.toEquiv]
    exact card_psl2_odd (f := 1) hcard hp2
  have hlt : Nat.card ↥K < Nat.card ↥X :=
    (hs.card_lt hs.ktype).trans_le
      (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _))
  have h168 : 168 ≤ Nat.card ↥K := isKType_card_ge hs.ktype
  have hsolv : Group.IsSolvable ↥H → False := fun h => hncH (IsSimpleGroup.comm_iff_isSolvable.mpr h)
  rcases dickson_psl2_subgroup_list (p := p) (f := 1) hcard H with
    ⟨m, hm, hmc, hel⟩ | ⟨z, hz, hzc, hcyc⟩ | ⟨z, hz2, hz, ⟨ed⟩⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ |
      ⟨-, ⟨eA5⟩⟩ | ⟨m, t', hm1, hmf, ht1, ht2, E, C, hE, hEel, hEcard, hCcyc, hCcard, hdisj, hsup,
        hfaith, φ, hφ, ⟨eS⟩⟩ | ⟨m, hmf, ⟨eL⟩⟩ | ⟨m, hmf, ⟨eG⟩⟩
  ·
    exact hncH fun a b => Subtype.ext (by
      have := hel.1.is_comm.comm a b
      exact congrArg Subtype.val this)
  ·
    have := hcyc
    exact hncH fun a b => mul_comm a b
  ·
    have : NeZero z := ⟨by omega⟩
    have : Group.IsSolvable (DihedralGroup z) := CFSG.ProperTwoGeneratedCore.UnitaryKernels.isSolvable_dihedralGroup z
    exact hsolv (Group.isSolvable_of_surjective (f := ed.symm.toMonoidHom) ed.symm.surjective)
  ·
    have := hHcard ▸ Nat.card_congr eA4.toEquiv
    rw [card_alternatingFour'] at this
    omega
  ·
    have := hHcard ▸ Nat.card_congr eS4.toEquiv
    rw [card_permFour] at this
    omega
  ·
    have := hHcard ▸ Nat.card_congr eA5.toEquiv
    rw [card_alternatingFive'] at this
    omega
  ·
    have := hE
    have hEne : E ≠ ⊥ := by
      intro h0
      have : Nat.card E = 1 := by rw [h0]; exact Subgroup.card_bot
      rw [hEcard] at this
      have hp1 : p ^ m ≠ 1 := by
        have := Nat.one_lt_pow (by omega : m ≠ 0) (Fact.out : p.Prime).one_lt
        omega
      exact hp1 this
    have hEtop : E = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal E).resolve_left hEne
    refine hncH fun a b => ?_
    have ha : a ∈ E := by rw [hEtop]; exact Subgroup.mem_top a
    have hb : b ∈ E := by rw [hEtop]; exact Subgroup.mem_top b
    have := hEel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  ·
    have hm1 : m = 1 := Nat.dvd_one.mp hmf
    subst hm1
    have h1 : Nat.card ↥H = Nat.card (PSL2MatrixGroup (GaloisField p 1)) :=
      Nat.card_congr eL.toEquiv
    have h2 : Nat.card ↥K = Nat.card ↥X := by
      rw [← hHcard, h1, card_psl2_galoisField hp2 one_ne_zero, hXcard]
      norm_num
    exact hlt.ne h2
  ·
    have := Nat.dvd_one.mp hmf
    omega

end L2Odd

end CFSG.QuasithinUnique.Id2519
