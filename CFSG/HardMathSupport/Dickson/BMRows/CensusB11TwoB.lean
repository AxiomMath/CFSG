module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseCo2Local
public import CFSG.Monster.Existence.BabyW2Classes
public import CFSG.HardMathSupport.Dickson.BMRows.Co2Eleven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenEbarData
public import CFSG.Sporadic.Co1Block.Perm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.BMRows.B11TwoB

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B
  CFSG.Monster.B.Short CFSG.Monster.Existence
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal

theorem card_modEq_card_inf_centralizer {H : Type*} [Group H] (K : Subgroup H) [K.Normal]
    [Finite K] {p : ℕ} [Fact p.Prime] {y : H} (hy : orderOf y = p) :
    Nat.card K ≡ Nat.card ↥(K ⊓ Subgroup.centralizer ({y} : Set H)) [MOD p] := by
  set P : Subgroup (ConjAct H) := Subgroup.zpowers (ConjAct.toConjAct y) with hP
  have hPp : IsPGroup p P := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hP, Nat.card_zpowers, MulEquiv.orderOf_eq, hy, pow_one]
  have hgen : ∀ k : K, ConjAct.toConjAct y • k = k ↔ (k : H) * y = y * k := by
    intro k
    rw [Subtype.ext_iff, ConjAct.Subgroup.val_conj_smul, ConjAct.toConjAct_smul]
    constructor
    · intro h
      calc (k : H) * y = y * k * y⁻¹ * y := by rw [h]
        _ = y * k := by group
    · intro h
      rw [← h]
      group
  have hfix : ∀ k : K, k ∈ MulAction.fixedPoints P K ↔
      (k : H) ∈ Subgroup.centralizer ({y} : Set H) := by
    intro k
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact (hgen k).1 (h ⟨_, Subgroup.mem_zpowers _⟩)
    · intro h g
      have hle : P ≤ MulAction.stabilizer (ConjAct H) k :=
        (Subgroup.zpowers_le).2 (MulAction.mem_stabilizer_iff.2 ((hgen k).2 h))
      exact MulAction.mem_stabilizer_iff.1 (hle g.2)
  have hmod := hPp.card_modEq_card_fixedPoints K
  have heq : Nat.card ↥(MulAction.fixedPoints P K) =
      Nat.card ↥(K ⊓ Subgroup.centralizer ({y} : Set H)) := Nat.card_congr
    { toFun := fun k => ⟨k.1.1, Subgroup.mem_inf.2 ⟨k.1.2, (hfix k.1).1 k.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩, (hfix _).2 (Subgroup.mem_inf.1 x.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rwa [heq] at hmod

theorem card_inf_centralizer_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') (a b : K) :
    Nat.card ↥(Subgroup.centralizer ({e a} : Set K') ⊓ Subgroup.centralizer ({e b} : Set K')) =
      Nat.card ↥(Subgroup.centralizer ({a} : Set K) ⊓ Subgroup.centralizer ({b} : Set K)) := by
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe]
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, e.injective.eq_iff, e.injective.eq_iff]

section Monster


theorem card_pCore_inf_centralizer_eleven_le {x : cent xGmat} (hx : orderOf x = 11) :
    Nat.card ↥(pCore 2 (cent xGmat) ⊓ Subgroup.centralizer ({x} : Set (cent xGmat))) ≤ 32 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, k, hxk⟩ := exists_conj_pow_of_factorization_eq_one factorization_cent_xGmat_eleven
    orderOf_x11H hx
  have hk1 : x11H ^ k ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hxk
    rw [hxk, orderOf_one] at hx
    norm_num at hx
  subst hxk
  have hN : (pCore 2 (cent xGmat)).Normal := inferInstance
  refine le_trans (Nat.card_le_card_of_injective
    (fun u => (⟨g⁻¹ * (u : cent xGmat) * g, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩ :
      ↥(pCore 2 (cent xGmat) ⊓ Subgroup.centralizer ({x11H} : Set (cent xGmat))))) ?_)
    card_pCore_inf_centralizer_x11_le
  · simpa using hN.conj_mem _ (Subgroup.mem_inf.1 u.2).1 g⁻¹
  · rw [← centralizer_pow_eq_of_prime orderOf_x11H hk1, Subgroup.mem_centralizer_singleton_iff]
    have hu := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 u.2).2
    calc g⁻¹ * (u : cent xGmat) * g * x11H ^ k
        = g⁻¹ * ((u : cent xGmat) * (g * x11H ^ k * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x11H ^ k * g⁻¹) * (u : cent xGmat)) * g := by rw [hu]
      _ = x11H ^ k * (g⁻¹ * (u : cent xGmat) * g) := by group
  · intro u v huv
    have h := congrArg Subtype.val huv
    simp only at h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))

theorem rhoCQ_le_rhoQ : rhoCQ ≤ rhoQ := fun f hf => by
  obtain ⟨q, -, rfl⟩ := mem_rhoCQ.1 hf
  exact rhoEquiv_mem_rhoQ q

theorem card_rhoCQ_inf_centralizer_le {w : Cgen} (hwJ : (w : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar)
    (hw : orderOf w = 11) :
    Nat.card ↥(rhoCQ.subgroupOf Cgen ⊓ Subgroup.centralizer ({w} : Set Cgen)) ≤ 32 := by
  have hcoe : ∀ (f : SpaceB ≃ₗ[ℚ] SpaceB) (hf : f ∈ Gvis),
      (((centVisEquiv.symm ⟨f, hf⟩ : cent xGmat) : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = f := by
    intro f hf
    have h := coe_centVisEquiv (centVisEquiv.symm ⟨f, hf⟩)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hGvis : ∀ u : ↥(rhoCQ.subgroupOf Cgen ⊓ Subgroup.centralizer ({w} : Set Cgen)),
      ((u : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := fun u =>
    (rhoCQ_le_Jstar (Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 u.2).1)).1
  set wh : cent xGmat := centVisEquiv.symm ⟨w, hwJ.1⟩ with hwh
  have hwho : orderOf wh = 11 := by
    rw [hwh, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hw]
  refine le_trans (Nat.card_le_card_of_injective
    (fun u => (⟨centVisEquiv.symm ⟨(u : Cgen), hGvis u⟩, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩ :
      ↥(pCore 2 (cent xGmat) ⊓ Subgroup.centralizer ({wh} : Set (cent xGmat))))) ?_)
    (card_pCore_inf_centralizer_eleven_le hwho)
  · rw [mem_pCore_cent_xGmat_iff, hcoe]
    exact rhoCQ_le_rhoQ (Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 u.2).1)
  · rw [Subgroup.mem_centralizer_singleton_iff, hwh, ← map_mul, ← map_mul]
    congr 1
    have hu := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 u.2).2
    have h := congrArg (fun t : Cgen => (t : SpaceB ≃ₗ[ℚ] SpaceB)) hu
    exact Subtype.ext h
  · intro u v huv
    have h := centVisEquiv.symm.injective (congrArg Subtype.val huv)
    have h2 := congrArg (fun t : Gvis => (t : SpaceB ≃ₗ[ℚ] SpaceB)) h
    exact Subtype.ext (Subtype.ext h2)

theorem two_mul_card_Ebar_inf_centralizer_le {yb : Cbar} (hybJ : yb ∈ Jbar)
    (hy : orderOf yb = 11) :
    2 * Nat.card ↥(Ebar ⊓ Subgroup.centralizer ({yb} : Set Cbar)) ≤ 32 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨c, hcJ, hcy⟩ := hybJ
  have hyb11 : yb ^ 11 = 1 := by rw [← hy]; exact pow_orderOf_eq_one yb
  have hyb1 : yb ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    norm_num at hy
  have hZ2 : ∀ z ∈ Zstar, z ^ 2 = 1 := by
    intro z hz
    have h := pow_card_eq_one' (G := Zstar) (x := ⟨z, hz⟩)
    rw [natCard_Zstar] at h
    exact congrArg Subtype.val h
  have hc11 : c ^ 11 ∈ Zstar := by
    rw [← ker_kappa, MonoidHom.mem_ker, map_pow, hcy, hyb11]
  set w := c ^ 12 with hw
  have hwκ : kappa w = yb := by rw [hw, map_pow, hcy, pow_succ, hyb11, one_mul]
  have hw11 : w ^ 11 = 1 := by
    rw [hw, ← pow_mul, show 12 * 11 = 11 * 2 * 6 by norm_num, pow_mul, pow_mul, hZ2 _ hc11,
      one_pow]
  have hw1 : w ≠ 1 := by
    intro h
    apply hyb1
    rw [← hwκ, h, map_one]
  have hwJ : (w : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar :=
    Subgroup.mem_subgroupOf.1 (Subgroup.pow_mem _ hcJ 12)
  set T : Subgroup Cgen := rhoCQ.subgroupOf Cgen ⊓
    (Subgroup.centralizer ({yb} : Set Cbar)).comap kappa with hT
  have hTle : T ≤ rhoCQ.subgroupOf Cgen ⊓ Subgroup.centralizer ({w} : Set Cgen) := by
    intro p hp
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hp).1, ?_⟩
    have hpc : kappa p * yb = yb * kappa p :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hp).2)
    have hz : p * c * p⁻¹ * c⁻¹ ∈ Zstar := by
      rw [← ker_kappa, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcy, hpc]
      group
    have hzc : (p * c * p⁻¹ * c⁻¹) * c = c * (p * c * p⁻¹ * c⁻¹) :=
      (Subgroup.mem_center_iff.1 (Zstar_le_center hz) c).symm
    have hpcp : p * c * p⁻¹ = (p * c * p⁻¹ * c⁻¹) * c := by group
    have key : p * w * p⁻¹ = w := by
      rw [hw, ← conj_pow, hpcp, (Commute.mul_pow hzc 12), show (12 : ℕ) = 2 * 6 by norm_num,
        pow_mul, hZ2 _ hz, one_pow, one_mul]
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc p * w = p * w * p⁻¹ * p := by group
      _ = w * p := by rw [key]
  have hTcard : 2 * Nat.card ↥(Ebar ⊓ Subgroup.centralizer ({yb} : Set Cbar)) ≤ Nat.card T := by
    set f : T →* Cbar := kappa.comp T.subtype with hf
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
    have hZT : ∀ z ∈ Zstar, z ∈ T := by
      intro z hz
      have hz1 : kappa z = 1 := by rw [← MonoidHom.mem_ker, ker_kappa]; exact hz
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have hle : Zstar ≤ rhoCQ.subgroupOf Cgen :=
          (Subgroup.zpowers_le).2 (Subgroup.mem_subgroupOf.2 tStar_mem_rhoCQ)
        exact hle hz
      · rw [Subgroup.mem_comap, hz1]
        exact Subgroup.one_mem _
    have hker : 2 ≤ Nat.card f.ker := by
      rw [← natCard_Zstar]
      refine Nat.card_le_card_of_injective
        (fun z => (⟨⟨z.1, hZT z.1 z.2⟩, ?_⟩ : f.ker)) ?_
      · rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.coe_subtype,
          ← MonoidHom.mem_ker, ker_kappa]
        exact z.2
      · intro a b hab
        exact Subtype.ext (congrArg (fun t : f.ker => ((t : T) : Cgen)) hab)
    have hrange : Nat.card ↥(Ebar ⊓ Subgroup.centralizer ({yb} : Set Cbar)) ≤ Nat.card f.range := by
      apply Subgroup.card_le_of_le
      intro e he
      obtain ⟨heE, heC⟩ := Subgroup.mem_inf.1 he
      obtain ⟨p, hp, rfl⟩ := heE
      exact ⟨⟨p, Subgroup.mem_inf.2 ⟨hp, Subgroup.mem_comap.2 heC⟩⟩, rfl⟩
    calc 2 * Nat.card ↥(Ebar ⊓ Subgroup.centralizer ({yb} : Set Cbar))
        ≤ Nat.card f.ker * Nat.card f.range := Nat.mul_le_mul hker hrange
      _ = Nat.card T := by rw [h1, mul_comm]
  exact hTcard.trans ((Subgroup.card_le_of_le hTle).trans
    (card_rhoCQ_inf_centralizer_le hwJ (orderOf_eq_prime hw11 hw1)))

end Monster

section Jbar


theorem natCard_Ebar_subgroupOf : Nat.card ↥(Ebar.subgroupOf Jbar) = 2 ^ 23 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ebar_le_Jbar).toEquiv, Ebar_extraspecial.2]

theorem card_Ebar_inf_centralizer_eq_eight {yb : Jbar} (hy : orderOf yb = 11) :
    Nat.card ↥(Ebar.subgroupOf Jbar ⊓ Subgroup.centralizer ({yb} : Set Jbar)) = 8 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨f, -, hker⟩ := CFSG.ComponentClassification.BMCase.jbar_exact_sequence
  haveI : (Ebar.subgroupOf Jbar).Normal := hker ▸ f.normal_ker
  have hmod := card_modEq_card_inf_centralizer (Ebar.subgroupOf Jbar) hy
  rw [natCard_Ebar_subgroupOf] at hmod
  have h2 := two_mul_card_Ebar_inf_centralizer_le yb.2 (by rw [Subgroup.orderOf_coe]; exact hy)
  have hinj : Nat.card ↥(Ebar.subgroupOf Jbar ⊓ Subgroup.centralizer ({yb} : Set Jbar)) ≤
      Nat.card ↥(Ebar ⊓ Subgroup.centralizer ({(yb : Cbar)} : Set Cbar)) :=
    Nat.card_le_card_of_injective
      (fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 x.2).1,
        Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val
          (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2))⟩⟩)
      (fun a b h => Subtype.ext (Subtype.ext
        (congrArg (fun t : ↥(Ebar ⊓ Subgroup.centralizer ({(yb : Cbar)} : Set Cbar)) =>
          (t : Cbar)) h)))
  have hpos : 0 < Nat.card ↥(Ebar.subgroupOf Jbar ⊓ Subgroup.centralizer ({yb} : Set Jbar)) :=
    Nat.card_pos
  have h8 : (2 : ℕ) ^ 23 % 11 = 8 := by norm_num
  rw [Nat.ModEq, h8] at hmod
  omega

theorem card_centralizer_Jbar_eleven_le {yb : Jbar} (hy : orderOf yb = 11) :
    Nat.card ↥(Subgroup.centralizer ({yb} : Set Jbar)) ≤ 88 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨f, hf, hker⟩ := CFSG.ComponentClassification.BMCase.jbar_exact_sequence
  have : Finite CFSG.Blueprint.NativeSporadic.Co2 := Finite.of_surjective f hf
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have h := card_centralizer_le_mul f.ker e yb
  have h1 : Nat.card ↥(f.ker ⊓ Subgroup.centralizer ({yb} : Set Jbar)) = 8 := by
    rw [hker]
    exact card_Ebar_inf_centralizer_eq_eight hy
  have hfy : orderOf (f yb) = 11 := by
    refine orderOf_eq_prime (by rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]) ?_
    intro h0
    have hmem : yb ∈ Ebar.subgroupOf Jbar := hker ▸ (MonoidHom.mem_ker.2 h0)
    have hdvd := Subgroup.orderOf_dvd_natCard (Ebar.subgroupOf Jbar) hmem
    rw [hy, natCard_Ebar_subgroupOf] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 11) hdvd
    norm_num at this
  have h2 : Nat.card ↥(Subgroup.centralizer
      ({e (QuotientGroup.mk yb)} : Set CFSG.Blueprint.NativeSporadic.Co2)) = 11 :=
    Co2Eleven.co2_eleven_card_centralizer (f yb) hfy
  rw [h1, h2] at h
  exact h

end Jbar

section B


theorem card_centralizer_inf_le_of_rank_2048 {X y : CFSG.Blueprint.NativeSporadic.B}
    (hX : orderOf X = 2) (hr : Matrix.rank (X.val.val - 1) = 2048) (hy : orderOf y = 11)
    (hXy : X * y = y * X) :
    Nat.card ↥(Subgroup.centralizer ({X} : Set CFSG.Blueprint.NativeSporadic.B) ⊓
      Subgroup.centralizer ({y} : Set CFSG.Blueprint.NativeSporadic.B)) ≤ 88 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_phiB_xBar_of_rank hX hr)
  set y₀ : Cbar := phiB.symm (c * y * c⁻¹) with hy₀def
  have h1 := card_inf_centralizer_mulEquiv (MulAut.conj c) X y
  simp only [MulAut.conj_apply] at h1
  rw [← h1, hc]
  have h2 := @card_inf_centralizer_mulEquiv Cbar CFSG.Blueprint.NativeSporadic.B _ Units.instGroup
    phiB xBar y₀
  rw [hy₀def, MulEquiv.apply_symm_apply, ← hy₀def] at h2
  rw [h2]
  have hy₀J : y₀ ∈ Jbar := by
    rw [← centralizer_xbar, Subgroup.mem_centralizer_singleton_iff]
    show y₀ * xBar = xBar * y₀
    apply phiB.injective
    rw [map_mul, map_mul, hy₀def, MulEquiv.apply_symm_apply, ← hc]
    calc c * y * c⁻¹ * (c * X * c⁻¹) = c * (y * X) * c⁻¹ := by group
      _ = c * (X * y) * c⁻¹ := by rw [hXy]
      _ = c * X * c⁻¹ * (c * y * c⁻¹) := by group
  have hy₀ : orderOf y₀ = 11 := by
    rw [hy₀def, MulEquiv.orderOf_eq, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  have hC : Subgroup.centralizer ({xBar} : Set Cbar) = Jbar := centralizer_xbar
  rw [hC]
  have h3 : Nat.card ↥(Jbar ⊓ Subgroup.centralizer ({y₀} : Set Cbar)) =
      Nat.card ↥(Subgroup.centralizer ({(⟨y₀, hy₀J⟩ : Jbar)} : Set Jbar)) := Nat.card_congr
    { toFun := fun u => ⟨⟨u.1, (Subgroup.mem_inf.1 u.2).1⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext
          (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 u.2).2))⟩
      invFun := fun u => ⟨u.1.1, Subgroup.mem_inf.2 ⟨u.1.2,
        Subgroup.mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 u.2))⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [h3]
  exact card_centralizer_Jbar_eleven_le (by rw [Subgroup.orderOf_mk]; exact hy₀)

end B

end CFSG.HardMathSupport.Dickson.BMRows.B11TwoB
