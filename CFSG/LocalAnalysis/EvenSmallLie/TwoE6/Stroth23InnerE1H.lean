module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerAut

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6.Stroth23Inner

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.GSide
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

instance isSimpleGroup_U : IsSimpleGroup (SUh ⧸ Zh) :=
  have := isSimpleGroup_unitaryPSU
  Unitary.psiQ.isSimpleGroup

theorem natCard_U : Nat.card (SUh ⧸ Zh) = 9196830720 := natCard_quot

theorem natCard_N1P : Nat.card (N1.subgroupOf P1) = 2 ^ 22 := by
  rw [← natCard_N1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe N1_le_P1).toEquiv]

theorem isPGroup_N1Q : IsPGroup 2 ((N1.subgroupOf P1).subgroupOf (commutator P1)) := by
  refine IsPGroup.of_card (n := 22) ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe N1P_le_commutator).toEquiv, natCard_N1P]

theorem mem_N1_alpha (α : MulAut (commutator P1)) {q : commutator P1}
    (hq : (q : P1) ∈ N1.subgroupOf P1) : ((α q : commutator P1) : P1) ∈ N1.subgroupOf P1 := by
  set K : Subgroup (commutator P1) :=
    ((N1.subgroupOf P1).subgroupOf (commutator P1)).map α.toMonoidHom with hK
  have hKn : K.Normal := by
    have : ((N1.subgroupOf P1).subgroupOf (commutator P1)).Normal := by
      rw [show (N1.subgroupOf P1).subgroupOf (commutator P1) = piU.ker by
        ext x; rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, piU_eq_one_iff]]
      infer_instance
    exact this.map _ α.surjective
  have hKp : IsPGroup 2 K := isPGroup_N1Q.map α.toMonoidHom
  have hU := (hKn.map piU piU_surjective).eq_bot_or_eq_top
  rcases hU with hbot | htop
  · rw [← piU_eq_one_iff]
    have hmem : α q ∈ K := ⟨q, Subgroup.mem_subgroupOf.2 hq, rfl⟩
    have h1 : piU (α q) ∈ K.map piU := ⟨_, hmem, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at h1
  · exfalso
    have hp : IsPGroup 2 (K.map piU) := hKp.map piU
    rw [htop] at hp
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 hp)
    rw [Subgroup.card_top, natCard_U] at hk
    have h2 : (9196830720 : ℕ) % 3 = 0 := by norm_num
    rw [hk] at h2
    have : 2 ^ k % 3 ≠ 0 := by
      intro h
      have h3 : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h
      exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h3) (by norm_num)
    exact this h2

theorem mem_ker_piU_iff (q : commutator P1) : q ∈ piU.ker ↔ (q : P1) ∈ N1.subgroupOf P1 := by
  rw [MonoidHom.mem_ker, piU_eq_one_iff]

@[expose] noncomputable def secU (u : SUh ⧸ Zh) : commutator P1 :=
  Function.surjInv piU_surjective u

theorem piU_secU (u : SUh ⧸ Zh) : piU (secU u) = u := Function.surjInv_eq piU_surjective u

theorem ker_piU_le (α : MulAut (commutator P1)) :
    piU.ker ≤ (piU.comp (α : commutator P1 →* commutator P1)).ker := fun q hq =>
  (mem_ker_piU_iff _).2 (mem_N1_alpha α ((mem_ker_piU_iff q).1 hq))

@[expose] noncomputable def alphaBarHom (α : MulAut (commutator P1)) : SUh ⧸ Zh →* SUh ⧸ Zh :=
  MonoidHom.liftOfRightInverse piU secU piU_secU ⟨_, ker_piU_le α⟩

theorem alphaBarHom_piU (α : MulAut (commutator P1)) (q : commutator P1) :
    alphaBarHom α (piU q) = piU (α q) :=
  MonoidHom.liftOfRightInverse_comp_apply piU secU piU_secU ⟨_, ker_piU_le α⟩ q

theorem alphaBarHom_bijective (α : MulAut (commutator P1)) :
    Function.Bijective (alphaBarHom α) := by
  have hs : Function.Surjective (alphaBarHom α) := fun u => by
    obtain ⟨q, rfl⟩ := piU_surjective u
    exact ⟨piU (α⁻¹ q), by rw [alphaBarHom_piU, MulAut.apply_inv_self]⟩
  have : Finite (SUh ⧸ Zh) := Nat.finite_of_card_ne_zero (by rw [natCard_U]; norm_num)
  exact ⟨Finite.injective_iff_surjective.2 hs, hs⟩

@[expose] noncomputable def alphaBar (α : MulAut (commutator P1)) : MulAut (SUh ⧸ Zh) :=
  MulEquiv.ofBijective (alphaBarHom α) (alphaBarHom_bijective α)

theorem alphaBar_piU (α : MulAut (commutator P1)) (q : commutator P1) :
    alphaBar α (piU q) = piU (α q) :=
  alphaBarHom_piU α q

theorem psiN_surjective : Function.Surjective psiN := by
  rintro ⟨x, hx⟩
  obtain ⟨e, rfl⟩ := psiW_surjective x
  have heN : (e : Dfull) ∈ N1 := by
    rw [N1_eq_EU, orth_sigLine_eq_sigmaPerp]
    exact mem_EU_of hx
  exact ⟨⟨⟨e, N1_le_P1 heN⟩, heN⟩, Subtype.ext (congrArg psiW (Subtype.ext rfl))⟩

theorem psiN_eq_zero_iff (n : N1.subgroupOf P1) :
    psiN n = 0 ↔ ((n : P1) : Dfull) = 1 ∨ ((n : P1) : Dfull) = xhat := by
  have h := psiW_eq_zero_iff ⟨((n : P1) : Dfull), N1_le_Ehat (mem_N1_of_mem_N1P n)⟩
  rw [← coe_psiN] at h
  constructor
  · intro h0
    rcases h.1 (by rw [h0]; rfl) with h1 | h1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (congrArg Subtype.val h1)
  · intro h1
    apply Subtype.ext
    refine h.2 ?_
    rcases h1 with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)

@[expose] noncomputable def psiNHom : N1.subgroupOf P1 →* Multiplicative sigmaPerp where
  toFun n := Multiplicative.ofAdd (psiN n)
  map_one' := by rw [psiN_one]; rfl
  map_mul' n m := by rw [psiN_mul]; rfl

@[expose] noncomputable def incN : N1.subgroupOf P1 →* commutator P1 :=
  Subgroup.inclusion N1P_le_commutator

@[expose] noncomputable def alphaN (α : MulAut (commutator P1)) :
    N1.subgroupOf P1 →* N1.subgroupOf P1 :=
  ((commutator P1).subtype.comp ((α : commutator P1 →* commutator P1).comp incN)).codRestrict
    (N1.subgroupOf P1) fun n => mem_N1_alpha α (q := incN n) n.2

@[expose] noncomputable def cN : N1.subgroupOf P1 := ⟨cP1, Subgroup.mem_subgroupOf.2 cQ_mem_N1⟩

@[expose] noncomputable def xN : N1.subgroupOf P1 := ⟨xP1, Subgroup.mem_subgroupOf.2 xhat_mem_N1⟩

@[expose] noncomputable def cPQ : commutator P1 := incN cN

@[expose] noncomputable def xPQ : commutator P1 := incN xN

theorem psiN_cN : psiN cN = sigmaP := Subtype.ext ((coe_psiN cN).trans psiW_cE)

theorem alphaN_eq_of_fix {α : MulAut (commutator P1)} {n : N1.subgroupOf P1}
    (h : α (incN n) = incN n) : alphaN α n = n :=
  Subtype.ext (Subtype.ext (congrArg (fun q : commutator P1 => ((q : P1) : Dfull)) h))

theorem psiN_alphaN_of_eq_zero {α : MulAut (commutator P1)} (hx : α xPQ = xPQ)
    {n : N1.subgroupOf P1} (hn : psiN n = 0) : psiN (alphaN α n) = 0 := by
  rcases (psiN_eq_zero_iff n).1 hn with h1 | h1
  · have : n = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, map_one, psiN_one]
  · have : n = xN := Subtype.ext (Subtype.ext h1)
    rw [this, alphaN_eq_of_fix hx]
    exact (psiN_eq_zero_iff xN).2 (Or.inr rfl)

theorem psiN_alphaN_congr {α : MulAut (commutator P1)} (hx : α xPQ = xPQ)
    {n m : N1.subgroupOf P1} (h : psiN n = psiN m) : psiN (alphaN α n) = psiN (alphaN α m) := by
  have h0 : psiN (n⁻¹ * m) = 0 := by rw [psiN_mul, psiN_inv, h, neg_add_cancel]
  have h1 := psiN_alphaN_of_eq_zero hx h0
  rw [map_mul, map_inv, psiN_mul, psiN_inv, neg_add_eq_zero] at h1
  exact h1

@[expose] noncomputable def alphaPerpAdd (α : MulAut (commutator P1)) (hx : α xPQ = xPQ) :
    sigmaPerp →+ sigmaPerp where
  toFun x := psiN (alphaN α (Function.surjInv psiN_surjective x))
  map_zero' := by
    refine psiN_alphaN_of_eq_zero hx ?_
    exact Function.surjInv_eq psiN_surjective 0
  map_add' x y := by
    rw [← psiN_mul, ← map_mul]
    refine psiN_alphaN_congr hx ?_
    rw [psiN_mul, Function.surjInv_eq psiN_surjective, Function.surjInv_eq psiN_surjective,
      Function.surjInv_eq psiN_surjective]

@[expose] noncomputable def alphaPerp (α : MulAut (commutator P1)) (hx : α xPQ = xPQ) :
    Module.End (ZMod 2) sigmaPerp :=
  (alphaPerpAdd α hx).toZModLinearMap 2

theorem alphaPerp_psiN (α : MulAut (commutator P1)) (hx : α xPQ = xPQ)
    (n : N1.subgroupOf P1) : alphaPerp α hx (psiN n) = psiN (alphaN α n) :=
  psiN_alphaN_congr hx (Function.surjInv_eq psiN_surjective _)

attribute [local irreducible] rhoU alphaPerp piU psiN

theorem incN_conj (q : commutator P1) (n : N1.subgroupOf P1) :
    incN (MulAut.conjNormal ((q : P1)⁻¹) n) = q⁻¹ * incN n * q := by
  apply Subtype.ext
  change (q : P1)⁻¹ * (n : P1) * ((q : P1)⁻¹)⁻¹ = (q : P1)⁻¹ * (n : P1) * (q : P1)
  rw [inv_inv]

theorem alphaN_conj (α : MulAut (commutator P1)) (q : commutator P1) (n : N1.subgroupOf P1) :
    alphaN α (MulAut.conjNormal ((q : P1)⁻¹) n) =
      MulAut.conjNormal (((α q : commutator P1) : P1)⁻¹) (alphaN α n) := by
  apply Subtype.ext
  have h1 : α (incN (MulAut.conjNormal ((q : P1)⁻¹) n)) = (α q)⁻¹ * α (incN n) * α q := by
    rw [incN_conj]
    simp only [MulEquiv.map_mul, MulEquiv.map_inv]
  change (α (incN (MulAut.conjNormal ((q : P1)⁻¹) n)) : P1) =
    ((α q : commutator P1) : P1)⁻¹ * (α (incN n) : P1) * (((α q : commutator P1) : P1)⁻¹)⁻¹
  simp only [h1, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]

theorem rhoU_piU_psiN (q : commutator P1) (n : N1.subgroupOf P1) :
    rhoU (piU q) (psiN n) = psiN (MulAut.conjNormal ((q : P1)⁻¹) n) := by
  rw [rhoU_piU, psiN_conj, inv_inv]

set_option maxHeartbeats 1000000 in
theorem alphaPerp_intertwine {α : MulAut (commutator P1)} (hx : α xPQ = xPQ) :
    ∀ (u : SUh ⧸ Zh) (x : sigmaPerp),
      alphaPerp α hx (rhoU u x) = rhoU (alphaBar α u) (alphaPerp α hx x) := by
  intro u x
  obtain ⟨q, rfl⟩ := piU_surjective u
  obtain ⟨n, rfl⟩ := psiN_surjective x
  calc alphaPerp α hx (rhoU (piU q) (psiN n))
      = alphaPerp α hx (psiN (MulAut.conjNormal ((q : P1)⁻¹) n)) :=
        congrArg (alphaPerp α hx) (rhoU_piU_psiN q n)
    _ = psiN (alphaN α (MulAut.conjNormal ((q : P1)⁻¹) n)) := alphaPerp_psiN α hx _
    _ = psiN (MulAut.conjNormal (((α q : commutator P1) : P1)⁻¹) (alphaN α n)) :=
        congrArg psiN (alphaN_conj α q n)
    _ = rhoU (piU (α q)) (psiN (alphaN α n)) := (rhoU_piU_psiN (α q) (alphaN α n)).symm
    _ = rhoU (alphaBar α (piU q)) (alphaPerp α hx (psiN n)) :=
        congrArg₂ (fun u y => rhoU u y) (alphaBar_piU α q).symm (alphaPerp_psiN α hx n).symm

theorem alphaPerp_sigmaP {α : MulAut (commutator P1)} (hx : α xPQ = xPQ) (hc : α cPQ = cPQ) :
    alphaPerp α hx sigmaP = sigmaP := by
  rw [← psiN_cN, alphaPerp_psiN, alphaN_eq_of_fix hc]

theorem isTwist_alphaBar {α : MulAut (commutator P1)} (hx : α xPQ = xPQ) (hc : α cPQ = cPQ) :
    IsTwist (alphaBar α) :=
  ⟨alphaPerp α hx, alphaPerp_sigmaP hx hc, alphaPerp_intertwine hx⟩

theorem conjU_coe (q : commutator P1) : conjU (q : P1) = MulAut.conj (piU q) :=
  conjU_of_mem q.2

theorem exists_not_mem_commutator_P1 : ∃ j : P1, j ∉ commutator P1 := by
  by_contra h
  push Not at h
  have htop : commutator P1 = ⊤ := eq_top_iff.2 fun x _ => h x
  have hidx := index_commutator_P1
  rw [htop, Subgroup.index_top] at hidx
  exact absurd hidx (by norm_num)

theorem exists_alphaBar_eq_conjU {α : MulAut (commutator P1)} (hx : α xPQ = xPQ)
    (hc : α cPQ = cPQ) : ∃ p : P1, alphaBar α = conjU p := by
  obtain ⟨j, hj⟩ := exists_not_mem_commutator_P1
  have hmem : (QuotientGroup.mk (alphaBar α) : Outer (SUh ⧸ Zh)) ∈ twistOuter :=
    ⟨alphaBar α, rfl, isTwist_alphaBar hx hc⟩
  rcases twistOuter_cases hj hmem with h | h
  · obtain ⟨v, hv⟩ := (QuotientGroup.eq_one_iff _).1 h
    obtain ⟨q, rfl⟩ := piU_surjective v
    exact ⟨q, by rw [← hv, conjU_coe]⟩
  · obtain ⟨v, hv⟩ : (conjU j)⁻¹ * alphaBar α ∈ inner (SUh ⧸ Zh) := QuotientGroup.eq.1 h.symm
    obtain ⟨q, rfl⟩ := piU_surjective v
    refine ⟨j * q, ?_⟩
    rw [map_mul, conjU_coe, hv, mul_inv_cancel_left]

theorem commutator_U : commutator (SUh ⧸ Zh) = ⊤ := by
  have h := map_commutator_of_mulEquiv Unitary.psiQ.symm
  rw [commutator_unitaryPSU] at h
  rw [← h]
  exact Subgroup.map_top_of_surjective _ Unitary.psiQ.symm.surjective

theorem piU_conjNormal (a : P1) (q : commutator P1) :
    piU (MulAut.conjNormal a q) = conjU a (piU q) := by
  have h : (SemidirectProduct.inl (piU (MulAut.conjNormal a q)) : SigmaU6) =
      SemidirectProduct.inl (conjU a (piU q)) := by
    rw [inl_piU, inl_conjU, inl_piU, MulAut.conjNormal_apply]
    simp only [MulEquiv.map_mul, MulEquiv.map_inv, MonoidHom.map_mul, MonoidHom.map_inv]
  exact SemidirectProduct.inl_injective h

theorem conjNormal_xPQ (a : P1) : MulAut.conjNormal a xPQ = xPQ := by
  apply Subtype.ext
  change a * xP1 * a⁻¹ = xP1
  rw [(Subgroup.mem_center_iff.1 xP1_mem_center a), mul_inv_cancel_right]

theorem conjNormal_cPQ (a : P1) : MulAut.conjNormal a cPQ = cPQ := by
  apply Subtype.ext
  change a * cP1 * a⁻¹ = cP1
  rw [(Subgroup.mem_center_iff.1 cP1_mem_center a), mul_inv_cancel_right]

section Generic

variable {N : Type*} [Group N]

@[expose] def centralQuot (f : N →* N) (hf : ∀ n, n⁻¹ * f n ∈ Subgroup.center N) : N →* N where
  toFun n := n⁻¹ * f n
  map_one' := by rw [map_one, inv_one, one_mul]
  map_mul' n m := by
    have h := Subgroup.mem_center_iff.1 (hf n) m⁻¹
    rw [map_mul, mul_inv_rev]
    calc m⁻¹ * n⁻¹ * (f n * f m) = m⁻¹ * (n⁻¹ * f n) * f m := by group
      _ = (n⁻¹ * f n) * m⁻¹ * f m := by rw [h]
      _ = n⁻¹ * f n * (m⁻¹ * f m) := by group

theorem centralQuot_apply (f : N →* N) (hf : ∀ n, n⁻¹ * f n ∈ Subgroup.center N) (n : N) :
    centralQuot f hf n = n⁻¹ * f n := rfl

theorem mul_commutatorElement_eq_conj {xh : N} (hxh2 : xh * xh = 1)
    (hxhZ : xh ∈ Subgroup.center N) (hc : ∀ u v : N, ⁅u, v⁆ = 1 ∨ ⁅u, v⁆ = xh) (n v : N) :
    n * ⁅n, v⁆ = v * n * v⁻¹ := by
  have h1 : ⁅n * n⁻¹, v⁆ = ⁅n⁻¹, v⁆ * ⁅n, v⁆ := commutatorElement_mul_left' hxhZ hc n n⁻¹ v
  rw [mul_inv_cancel, commutatorElement_one_left] at h1
  have h2 : ⁅n⁻¹, v⁆ = ⁅n, v⁆ := by
    have hinv : ⁅n, v⁆⁻¹ = ⁅n, v⁆ := by
      rcases hc n v with h | h <;> rw [h]
      · exact inv_one
      · exact inv_eq_of_mul_eq_one_right hxh2
    rw [← hinv]
    exact eq_inv_of_mul_eq_one_left h1.symm
  rw [← h2, commutatorElement_def]
  group

@[expose] def centralDiff {G H : Type*} [Group G] [Group H] (f g : G →* H)
    (hfg : ∀ x, (g x)⁻¹ * f x ∈ Subgroup.center H) : G →* H where
  toFun x := (g x)⁻¹ * f x
  map_one' := by rw [map_one, map_one, inv_one, one_mul]
  map_mul' x y := by
    have h := Subgroup.mem_center_iff.1 (hfg x) (g y)⁻¹
    rw [map_mul, map_mul, mul_inv_rev]
    calc (g y)⁻¹ * (g x)⁻¹ * (f x * f y) = (g y)⁻¹ * ((g x)⁻¹ * f x) * f y := by group
      _ = ((g x)⁻¹ * f x) * (g y)⁻¹ * f y := by rw [h]
      _ = (g x)⁻¹ * f x * ((g y)⁻¹ * f y) := by group

theorem centralDiff_apply {G H : Type*} [Group G] [Group H] (f g : G →* H)
    (hfg : ∀ x, (g x)⁻¹ * f x ∈ Subgroup.center H) (x : G) :
    centralDiff f g hfg x = (g x)⁻¹ * f x := rfl

end Generic

theorem xN_mul_self : xN * xN = 1 := Subtype.ext (Subtype.ext xhat_mul_self)

theorem xN_ne_one : xN ≠ 1 := fun h => xhat_ne_one (congrArg (fun n : N1.subgroupOf P1 =>
  ((n : P1) : Dfull)) h)

theorem xN_mem_center : xN ∈ Subgroup.center (N1.subgroupOf P1) :=
  (mem_center_N1P_iff xN).2 xhat_mem_EU

theorem commutatorElement_N1P (u v : N1.subgroupOf P1) : ⁅u, v⁆ = 1 ∨ ⁅u, v⁆ = xN := by
  have h : ((⁅u, v⁆ : N1.subgroupOf P1) : P1) ∈ ⁅N1.subgroupOf P1, N1.subgroupOf P1⁆ :=
    Subgroup.commutator_mem_commutator u.2 v.2
  rw [commutator_N1P] at h
  have hx : orderOf xP1 = 2 := orderOf_eq_prime (by
    rw [sq]; exact Subtype.ext xhat_mul_self) (fun h1 => xhat_ne_one (congrArg Subtype.val h1))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · left
    apply Subtype.ext
    rw [← hk, ← zpow_mod_orderOf, hx]
    simp [h0]
  · right
    apply Subtype.ext
    rw [← hk, ← zpow_mod_orderOf, hx]
    simp [h0]
    rfl

theorem alphaN_center {α : MulAut (commutator P1)} (hx : α xPQ = xPQ) (hc : α cPQ = cPQ)
    {z : N1.subgroupOf P1} (hz : z ∈ Subgroup.center (N1.subgroupOf P1)) : alphaN α z = z := by
  have hz' := (mem_center_N1P_iff z).1 hz
  rw [EU_sigLine, closure_xhat_cQ_eq_map] at hz'
  obtain ⟨y, hy, hyz⟩ := hz'
  have hle : Subgroup.closure ({xP1, cP1} : Set P1) ≤
      ((α : commutator P1 →* commutator P1).eqLocus (MonoidHom.id _)).map
        (commutator P1).subtype := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨xPQ, hx, rfl⟩
    · exact ⟨cPQ, hc, rfl⟩
  obtain ⟨w, hw, hwy⟩ := hle hy
  have hwz : w = incN z := Subtype.ext (Subtype.ext (by
    change ((w : P1) : Dfull) = ((z : P1) : Dfull)
    rw [← hyz, ← hwy]
    rfl))
  apply alphaN_eq_of_fix
  rw [← hwz]
  exact hw

section Trivial

variable {α : MulAut (commutator P1)} (hx : α xPQ = xPQ) (hc : α cPQ = cPQ)
  (h1 : ∀ u, alphaBar α u = u)

include hx hc h1

theorem psiN_alphaN_eq (n : N1.subgroupOf P1) : psiN (alphaN α n) = psiN n := by
  have hA : ∀ u x, alphaPerp α hx (rhoU u x) = rhoU u (alphaPerp α hx x) := fun u x =>
    (alphaPerp_intertwine hx u x).trans (congrArg (fun w => rhoU w (alphaPerp α hx x)) (h1 u))
  exact (alphaPerp_psiN α hx n).symm.trans (eq_id_of_intertwine hA (alphaPerp_sigmaP hx hc) _)

theorem inv_mul_alphaN_cases (n : N1.subgroupOf P1) :
    n⁻¹ * alphaN α n = 1 ∨ n⁻¹ * alphaN α n = xN := by
  have h0 : psiN (n⁻¹ * alphaN α n) = 0 := by
    rw [psiN_mul, psiN_inv, psiN_alphaN_eq hx hc h1, neg_add_cancel]
  rcases (psiN_eq_zero_iff _).1 h0 with h | h
  · exact Or.inl (Subtype.ext (Subtype.ext h))
  · exact Or.inr (Subtype.ext (Subtype.ext h))

theorem inv_mul_alphaN_mem_center (n : N1.subgroupOf P1) :
    n⁻¹ * alphaN α n ∈ Subgroup.center (N1.subgroupOf P1) := by
  rcases inv_mul_alphaN_cases hx hc h1 n with h | h <;> rw [h]
  · exact Subgroup.one_mem _
  · exact xN_mem_center

theorem exists_alphaN_eq_conj : ∃ v : N1.subgroupOf P1, ∀ n, alphaN α n = v * n * v⁻¹ := by
  obtain ⟨v, hv⟩ := exists_eq_commutatorElement xN_mul_self xN_ne_one xN_mem_center
    commutatorElement_N1P mul_self_mem_center_N1P
    (centralQuot (alphaN α) (inv_mul_alphaN_mem_center hx hc h1))
    (inv_mul_alphaN_cases hx hc h1)
    (fun z hz => by rw [centralQuot_apply, alphaN_center hx hc hz, inv_mul_cancel])
  refine ⟨v, fun n => ?_⟩
  have e := hv n
  rw [centralQuot_apply] at e
  calc alphaN α n = n * (n⁻¹ * alphaN α n) := (mul_inv_cancel_left n _).symm
    _ = n * ⁅n, v⁆ := congrArg (n * ·) e
    _ = v * n * v⁻¹ :=
      mul_commutatorElement_eq_conj xN_mul_self xN_mem_center commutatorElement_N1P n v

end Trivial

theorem conjNormal_inv_apply (a : P1) (q : commutator P1) :
    (((MulAut.conjNormal a)⁻¹ q : commutator P1) : P1) = a⁻¹ * q * a := by
  rw [← map_inv, MulAut.conjNormal_apply, inv_inv]

theorem mem_center_P1_of_commute {y : P1} (hy : ∀ n ∈ N1, (y : Dfull) * n = n * y) :
    y ∈ Subgroup.center P1 := by
  have h := mem_closure_of_centralizer_N1 y.2 hy
  refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
  change (g : Dfull) * y = y * g
  exact ((Subgroup.mem_centralizer_iff.1 (closure_xhat_cQ_le_centralizer h)) g g.2)

theorem commute_of_conj_eq {G : Type*} [Group G] {a b m : G} (h : b * m * b⁻¹ = a * m * a⁻¹) :
    a⁻¹ * b * m = m * (a⁻¹ * b) := by
  calc a⁻¹ * b * m = a⁻¹ * (b * m * b⁻¹) * b := by group
    _ = a⁻¹ * (a * m * a⁻¹) * b := by rw [h]
    _ = m * (a⁻¹ * b) := by group

set_option maxHeartbeats 1000000 in
theorem eq_self_of_trivial {β : MulAut (commutator P1)} (hβN : ∀ n, β (incN n) = incN n)
    (q : commutator P1) : β q = q := by
  have hcomm : ∀ q : commutator P1, ∀ m ∈ N1,
      (((q : P1)⁻¹ * (β q : P1) : P1) : Dfull) * m = m * (((q : P1)⁻¹ * (β q : P1) : P1)) := by
    intro q m hm
    set mN : N1.subgroupOf P1 := ⟨⟨m, N1_le_P1 hm⟩, hm⟩
    have e1 : β (incN (MulAut.conjNormal (q : P1) mN)) = incN (MulAut.conjNormal (q : P1) mN) :=
      hβN _
    have e2 : incN (MulAut.conjNormal (q : P1) mN) = q * incN mN * q⁻¹ := Subtype.ext rfl
    rw [e2] at e1
    simp only [MulEquiv.map_mul, MulEquiv.map_inv, hβN] at e1
    have e3 := congrArg (fun x : commutator P1 => ((x : P1) : Dfull)) e1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e3
    have h := commute_of_conj_eq e3
    have hm : (((incN mN : commutator P1) : P1) : Dfull) = m := rfl
    rw [hm] at h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hμ : ∀ q : commutator P1,
      ((commutator P1).subtype q)⁻¹ * ((commutator P1).subtype.comp β.toMonoidHom) q ∈
        Subgroup.center P1 := fun q => mem_center_P1_of_commute (hcomm q)
  set μ := centralDiff _ _ hμ
  have hμN : ∀ n, μ (incN n) = 1 := fun n => by
    rw [centralDiff_apply]
    change ((incN n : commutator P1) : P1)⁻¹ * (β (incN n) : P1) = 1
    rw [hβN, inv_mul_cancel]
  have hμC : ∀ c ∈ commutator (commutator P1), μ c = 1 := by
    intro c hc
    have h : (commutator (commutator P1)).map μ ≤ ⊥ := by
      rw [map_commutator_eq, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨x, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, rfl⟩
      exact Subgroup.mem_center_iff.1 (hμ x) (μ y)
    exact (Subgroup.mem_bot.1 (h ⟨c, hc, rfl⟩))
  have htop : (commutator (commutator P1)).map piU = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ piU_surjective,
      ← commutator_def, commutator_U]
  obtain ⟨c, hc, hcq⟩ : piU q ∈ (commutator (commutator P1)).map piU := by
    rw [htop]; exact Subgroup.mem_top _
  have hker : ((c⁻¹ * q : commutator P1) : P1) ∈ N1.subgroupOf P1 := by
    rw [← piU_eq_one_iff, map_mul, map_inv, hcq, inv_mul_cancel]
  have hq : q = c * incN ⟨_, hker⟩ := by
    rw [show incN ⟨_, hker⟩ = c⁻¹ * q from Subtype.ext rfl, mul_inv_cancel_left]
  have hμq : μ q = 1 := by
    rw [hq, map_mul, hμC c hc, hμN, one_mul]
  have h2 : ((q : P1))⁻¹ * (β q : P1) = 1 := hμq
  exact Subtype.ext (inv_mul_eq_one.1 h2).symm

theorem conj_eq_of_inv_conj {a x y : P1} (h : a⁻¹ * x * a = y) : x = a * y * a⁻¹ := by
  rw [← h]; group

set_option maxHeartbeats 2000000 in
theorem exists_conj_of_trivial {α : MulAut (commutator P1)} (hx : α xPQ = xPQ)
    (hc : α cPQ = cPQ) (h1 : ∀ u, alphaBar α u = u) :
    ∃ v : P1, ∀ q : commutator P1, ((α q : commutator P1) : P1) = v * q * v⁻¹ := by
  obtain ⟨v, hv⟩ := exists_alphaN_eq_conj hx hc h1
  set β : MulAut (commutator P1) := (MulAut.conjNormal (v : P1))⁻¹ * α with hβdef
  have hβ : ∀ q, (β q : P1) = (v : P1)⁻¹ * (α q : P1) * v := fun q =>
    conjNormal_inv_apply (v : P1) (α q)
  have hβN : ∀ n, β (incN n) = incN n := fun n => by
    apply Subtype.ext
    rw [hβ]
    change (v : P1)⁻¹ * (alphaN α n : P1) * v = n
    rw [hv n, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  refine ⟨v, fun q => conj_eq_of_inv_conj ?_⟩
  rw [← hβ, eq_self_of_trivial hβN q]

set_option maxHeartbeats 2000000 in
theorem exists_conj_of_mulAut (α : MulAut (commutator P1)) (hx : α xPQ = xPQ)
    (hc : α cPQ = cPQ) :
    ∃ g : P1, ∀ q : commutator P1, ((α q : commutator P1) : P1) = g * q * g⁻¹ := by
  obtain ⟨p, hp⟩ := exists_alphaBar_eq_conjU hx hc
  set α' : MulAut (commutator P1) := (MulAut.conjNormal p)⁻¹ * α with hα'
  have hα'q : ∀ q, (α' q : P1) = p⁻¹ * (α q : P1) * p := fun q => conjNormal_inv_apply p (α q)
  have hα'q' : ∀ q, α' q = MulAut.conjNormal p⁻¹ (α q) := fun q => by
    rw [hα', MulAut.mul_apply, ← map_inv]
  have hx' : α' xPQ = xPQ := by rw [hα'q', hx, conjNormal_xPQ]
  have hc' : α' cPQ = cPQ := by rw [hα'q', hc, conjNormal_cPQ]
  have h1 : ∀ u, alphaBar α' u = u := fun u => by
    obtain ⟨q, rfl⟩ := piU_surjective u
    rw [alphaBar_piU, hα'q', piU_conjNormal, ← alphaBar_piU, hp, map_inv, MulAut.inv_apply_self]
  obtain ⟨v, hv⟩ := exists_conj_of_trivial hx' hc' h1
  refine ⟨p * v, fun q => ?_⟩
  have e := hv q
  rw [hα'q] at e
  rw [conj_eq_of_inv_conj e]
  group

end CFSG.EvenSmallLie.TwoE6.Stroth23Inner
