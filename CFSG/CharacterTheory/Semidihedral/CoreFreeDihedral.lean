module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupAlternatingFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
import CFSG.Adapters.WholeGroupLayer
public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Semidihedral.CoreFreeDihedral

noncomputable section

open CFSG.GorensteinWalter

universe u v

theorem hasDihedralSylowTwo_of_supplied
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (n : ℕ) (hn : 2 ≤ n)
    (e : S ≃* DihedralGroup (2 ^ (n - 1))) :
    HasDihedralSylowTwo G := by
  intro T
  exact ⟨n - 1, by omega, ⟨(Sylow.equiv T S).trans e⟩⟩

theorem center_eq_bot_of_simple_nonabelian
    {H : Type u} [Group H] [IsSimpleGroup H]
    (hnc : ∃ x y : H, x * y ≠ y * x) :
    Subgroup.center H = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
  · exact h
  · obtain ⟨x, y, hxy⟩ := hnc
    have hx : x ∈ Subgroup.center H := by rw [h]; trivial
    exact (hxy (Subgroup.mem_center_iff.mp hx y).symm).elim

theorem isPerfect_of_simple_nonabelian
    {H : Type u} [Group H] [IsSimpleGroup H]
    (hnc : ∃ x y : H, x * y ≠ y * x) : Group.IsPerfect H := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator H) with h | h
  · have hcomm := (commutator_eq_bot_iff H).mp h
    obtain ⟨x, y, hxy⟩ := hnc
    exact (hxy (hcomm.is_comm.comm x y)).elim
  · exact h

theorem isComponent_of_normal_simple_nonabelian
    {G : Type u} [Group G] (N : Subgroup G) [N.Normal] [IsSimpleGroup N]
    (hnc : ∃ x y : N, x * y ≠ y * x) : CFSG.IsComponent N := by
  have hZ := center_eq_bot_of_simple_nonabelian hnc
  have e : (N ⧸ Subgroup.center N) ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot)
  have hqsimple : IsSimpleGroup (N ⧸ Subgroup.center N) := e.isSimpleGroup
  have hqnc : ∃ x y : N ⧸ Subgroup.center N, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨e.symm x, e.symm y, ?_⟩
    intro h
    apply hxy
    simpa using congrArg e h
  exact ⟨⟨isPerfect_of_simple_nonabelian hnc, hqsimple, hqnc⟩,
    (inferInstance : N.Normal).isSubnormal⟩

theorem generalizedFitting_eq_of_normal_simple_centralizer_eq_bot
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [IsSimpleGroup N]
    (hnc : ∃ x y : N, x * y ≠ y * x)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) :
    CFSG.generalizedFitting G = N :=
  CFSG.Adapters.generalizedFitting_eq_of_normal_simple_of_centralizer_eq_bot N hnc hC

def SimpleGeneralizedFittingAlternative (G : Type u) [Group G] : Prop :=
  IsSimpleGroup (CFSG.generalizedFitting G) ∧
    (∃ x y : CFSG.generalizedFitting G, x * y ≠ y * x) ∧
    Subgroup.centralizer (CFSG.generalizedFitting G : Set G) = ⊥ ∧
    ∀ T : Sylow 2 (CFSG.generalizedFitting G),
      ∃ m : ℕ, 2 ≤ m ∧ Nonempty (T ≃* DihedralGroup (2 ^ (m - 1)))

theorem simpleGeneralizedFittingAlternative_of_normal_simple
    {G : Type u} [Group G] [Finite G]
    (hG : HasDihedralSylowTwo G) (hcore : pPrimeCore 2 G = ⊥)
    (N : Subgroup G) [N.Normal] [IsSimpleGroup N]
    (hnc : ∃ x y : N, x * y ≠ y * x) (hN : HasDihedralSylowTwo N) :
    SimpleGeneralizedFittingAlternative G := by
  have hC := centralizer_eq_bot_of_normal_centerless_dihedral_of_pPrimeCore_eq_bot
    hG hcore N inferInstance (center_eq_bot_of_simple_nonabelian hnc) hN
  have heq := generalizedFitting_eq_of_normal_simple_centralizer_eq_bot N hnc hC
  unfold SimpleGeneralizedFittingAlternative
  rw [heq]
  refine ⟨inferInstance, hnc, hC, ?_⟩
  intro T
  obtain ⟨m, hm, e⟩ := hN T
  exact ⟨m + 1, by omega, by simpa using e⟩

theorem sylowThree_action_injective_of_alternatingFour
    {H : Type u} [Group H] [Finite H]
    (e : H ≃* alternatingGroup (Fin 4)) :
    Function.Injective (MulAction.toPermHom H (Sylow 3 H)) := by
  classical
  let P : Sylow 3 H := Classical.choice Sylow.nonempty
  have hcard : Nat.card H = 12 :=
    (Nat.card_congr e.toEquiv).trans
      (alternatingGroup.card_of_card_eq_four (by simp))
  have hPcard : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, hcard]
    have hfac : (Nat.factorization 12) 3 = 1 := by
      rw [show 12 = 3 * 4 by norm_num,
        Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 3 4),
        Nat.prime_three.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 4)]
    rw [hfac]
    norm_num
  let act := MulAction.toPermHom H (Sylow 3 H)
  have hle : act.ker ≤ (P : Subgroup H) := by
    rw [← normalizer_eq_self_of_card_eq_three_of_mulEquiv_alternatingGroup_four
      P hPcard ⟨e⟩]
    intro x hx
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    have h := DFunLike.congr_fun (MonoidHom.mem_ker.mp hx) P
    simpa [act] using h
  have hdvd : Nat.card act.ker ∣ 3 := by
    simpa [hPcard] using Subgroup.card_dvd_of_le hle
  have hp : IsPGroup 3 act.ker := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by simpa using h)
    · exact IsPGroup.of_card (n := 1) (by simpa using h)
  exact (MonoidHom.ker_eq_bot_iff act).mp
    (normal_pSubgroup_eq_bot_of_mulEquiv_alternatingGroup_four ⟨e⟩
      3 Nat.prime_three (by decide) act.ker inferInstance hp)

theorem faithful_four_point_action_of_normal_alternatingFour
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (e : N ≃* alternatingGroup (Fin 4))
    (hC : Subgroup.centralizer (N : Set G) = ⊥) :
    ∃ f : G →* Equiv.Perm (Fin 4), Function.Injective f := by
  classical
  let Ω := Sylow 3 N
  let : MulAction G Ω := MulAction.compHom Ω (MulAut.conjNormal (H := N))
  let act : G →* Equiv.Perm Ω := MulAction.toPermHom G Ω
  have hrestriction : act.comp N.subtype = MulAction.toPermHom N Ω := by
    ext x P
    rfl
  have hinjN := sylowThree_action_injective_of_alternatingFour e
  have hInt : act.ker ⊓ N = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxact : MulAction.toPermHom N Ω ⟨x, hx.2⟩ = 1 := by
      rw [← hrestriction]
      exact MonoidHom.mem_ker.mp hx.1
    have hxone : (⟨x, hx.2⟩ : N) = 1 :=
      hinjN (hxact.trans (map_one (MulAction.toPermHom N Ω)).symm)
    exact congrArg Subtype.val hxone
  have hcomm : ⁅act.ker, N⁆ = ⊥ := by
    apply le_bot_iff.mp
    have h := Subgroup.commutator_le_inf act.ker N
    rwa [hInt] at h
  have hker : act.ker = ⊥ := by
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    rw [hC] at h
    exact le_bot_iff.mp h
  let eΩ : Ω ≃ Fin 4 := Finite.equivFinOfCardEq
    (sylow_three_card_eq_four_of_mulEquiv_alternatingGroup_four ⟨e⟩)
  exact ⟨eΩ.permCongrHom.toMonoidHom.comp act,
    eΩ.permCongrHom.injective.comp ((MonoidHom.ker_eq_bot_iff act).mp hker)⟩

theorem twoGroup_or_fourPoint_of_faithful_action
    {G : Type u} [Group G] [Finite G]
    (hG : HasDihedralSylowTwo G)
    (f : G →* Equiv.Perm (Fin 4)) (hf : Function.Injective f) :
    IsPGroup 2 G ∨ Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  let e : G ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hR : HasDihedralSylowTwo f.range :=
    hasDihedralSylowTwo_of_mulEquiv e.symm hG
  rcases subgroup_S4_dihedral_classification hR with h | h | h
  · exact Or.inl (h.of_equiv e.symm)
  · exact Or.inr (Or.inl ⟨e.trans (MulEquiv.subgroupCongr h)⟩)
  · exact Or.inr (Or.inr ⟨(e.trans (MulEquiv.subgroupCongr h)).trans Subgroup.topEquiv⟩)

theorem exists_noncommuting_of_perfect
    {H : Type u} [Group H] [Nontrivial H] [Group.IsPerfect H] :
    ∃ x y : H, x * y ≠ y * x := by
  classical
  by_contra h
  push Not at h
  exact Group.IsPerfect.not_isMulCommutative H ⟨⟨h⟩⟩

theorem simpleAlternative_of_normal_psl2
    {G : Type u} [Group G] [Finite G]
    (hG : HasDihedralSylowTwo G) (hcore : pPrimeCore 2 G = ⊥)
    (N : Subgroup G) [N.Normal]
    (K : Type v) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hlarge : 3 < Nat.card K)
    (e : N ≃* PSL2 K) : SimpleGeneralizedFittingAlternative G := by
  let : IsSimpleGroup (PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup N := e.isSimpleGroup
  have hperf : Group.IsPerfect N := by
    have hp := psl2_isPerfect_of_card_gt_three K hlarge
    have : Group.IsPerfect (PSL2 K) := hp
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsPerfect N := hperf
  have hN := hasDihedralSylowTwo_of_mulEquiv e (psl2_odd_hasDihedralSylowTwo_model K hK)
  exact simpleGeneralizedFittingAlternative_of_normal_simple hG hcore N
    exists_noncommuting_of_perfect hN

theorem twoGroup_or_fourPoint_of_normal_psl2_card_three
    {G : Type u} [Group G] [Finite G]
    (hG : HasDihedralSylowTwo G) (hcore : pPrimeCore 2 G = ⊥)
    (N : Subgroup G) [N.Normal]
    (K : Type v) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hthree : Nat.card K = 3)
    (e : N ≃* PSL2 K) :
    IsPGroup 2 G ∨ Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three
    (by simpa [Nat.card_eq_fintype_card] using hthree)
  let eA : N ≃* alternatingGroup (Fin 4) :=
    (e.trans (psl2RingEquiv eK).symm).trans psl2_three_equiv_alternatingGroup
  have hN := hasDihedralSylowTwo_of_mulEquiv e (psl2_odd_hasDihedralSylowTwo_model K hK)
  have hZN : Subgroup.center N = ⊥ :=
    center_eq_bot_of_mulEquiv e (psl2_center_eq_bot K)
  have hC := centralizer_eq_bot_of_normal_centerless_dihedral_of_pPrimeCore_eq_bot
    hG hcore N inferInstance hZN hN
  obtain ⟨f, hf⟩ := faithful_four_point_action_of_normal_alternatingFour N eA hC
  exact twoGroup_or_fourPoint_of_faithful_action hG f hf

theorem three_le_card_of_oddPrimePower
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) : 3 ≤ Nat.card K := by
  have hodd : Odd (Nat.card K) := by
    obtain ⟨p, n, _, hpodd, _, hcard⟩ := hK
    rw [hcard]
    exact hpodd.pow
  have hpos : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨n, hn⟩ := hodd
  omega

theorem alternatives_of_normal_linear
    {G : Type u} [Group G] [Finite G]
    (hG : HasDihedralSylowTwo G) (hcore : pPrimeCore 2 G = ⊥)
    (N : Subgroup G) [N.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty (N ≃* PSL2 K) ∨ Nonempty (N ≃* PGL2 K)) :
    IsPGroup 2 G ∨ Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (G ≃* Equiv.Perm (Fin 4)) ∨ SimpleGeneralizedFittingAlternative G := by
  have hge := three_le_card_of_oddPrimePower hK
  by_cases hlarge : 3 < Nat.card K
  · rcases e with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inr (Or.inr (Or.inr
        (simpleAlternative_of_normal_psl2 hG hcore N K hK hlarge e)))
    · obtain ⟨L, hLnormal, _, ⟨eL⟩⟩ :=
        exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three
          N inferInstance K hK hlarge e
      let : L.Normal := hLnormal
      exact Or.inr (Or.inr (Or.inr
        (simpleAlternative_of_normal_psl2 hG hcore L K hK hlarge eL)))
  · have hthree : Nat.card K = 3 := by omega
    have hfour : IsPGroup 2 G ∨ Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
        Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
      rcases e with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
      · exact twoGroup_or_fourPoint_of_normal_psl2_card_three hG hcore N K hK hthree e
      · classical
        let : Fintype K := Fintype.ofFinite K
        let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three
          (by simpa [Nat.card_eq_fintype_card] using hthree)
        let eN : N ≃* PGL2 (ZMod 3) := e.trans (pgl2RingEquiv eK).symm
        obtain ⟨L, hLnormal, _, ⟨eL⟩⟩ :=
          exists_normal_psl2_three_core_of_normal_mulEquiv_pgl2_three N inferInstance eN
        let : L.Normal := hLnormal
        have hK3 : IsOddPrimePower (Nat.card (ZMod 3)) :=
          ⟨3, 1, Nat.prime_three, by decide, by omega, by simp⟩
        exact twoGroup_or_fourPoint_of_normal_psl2_card_three hG hcore L (ZMod 3)
          hK3 (by simp) eL
    rcases hfour with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

theorem exists_noncommuting_of_center_eq_bot
    {H : Type u} [Group H] [Nontrivial H]
    (hZ : Subgroup.center H = ⊥) : ∃ x y : H, x * y ≠ y * x := by
  classical
  by_contra h
  push Not at h
  have htop : Subgroup.center H = ⊤ := Subgroup.center_eq_top_iff.mpr ⟨⟨h⟩⟩
  exact top_ne_bot (htop.symm.trans hZ)

theorem simpleAlternative_of_alternatingSeven
    {G : Type u} [Group G] [Finite G]
    (hG : HasDihedralSylowTwo G) (hcore : pPrimeCore 2 G = ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) :
    SimpleGeneralizedFittingAlternative G := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  let eN : (⊤ : Subgroup G) ≃* alternatingGroup (Fin 7) := Subgroup.topEquiv.trans e
  let : IsSimpleGroup (⊤ : Subgroup G) := eN.isSimpleGroup
  have hZ : Subgroup.center (⊤ : Subgroup G) = ⊥ :=
    center_eq_bot_of_mulEquiv eN (alternatingGroup.center_eq_bot (by norm_num))
  have hN : HasDihedralSylowTwo (⊤ : Subgroup G) :=
    hasDihedralSylowTwo_of_mulEquiv Subgroup.topEquiv hG
  exact simpleGeneralizedFittingAlternative_of_normal_simple hG hcore ⊤
    (exists_noncommuting_of_center_eq_bot hZ) hN

theorem alternatives_of_hasDihedralSylowTwo
    {G : Type u} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥) (hG : HasDihedralSylowTwo G) :
    IsPGroup 2 G ∨ Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (G ≃* Equiv.Perm (Fin 4)) ∨ SimpleGeneralizedFittingAlternative G := by
  let eQ : (G ⧸ pPrimeCore 2 G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  rcases gorensteinWalter G hG with ⟨_, htwo⟩ | ⟨_, ⟨e7⟩⟩ |
      ⟨_, K, hK, N, hNnormal, _, eN⟩
  · exact Or.inl (htwo.of_equiv eQ)
  · exact Or.inr (Or.inr (Or.inr
      (simpleAlternative_of_alternatingSeven hG hcore (eQ.symm.trans e7))))
  · let L : Subgroup G := N.map eQ.toMonoidHom
    have hLnormal : L.Normal := hNnormal.map eQ.toMonoidHom eQ.surjective
    let : L.Normal := hLnormal
    let eL : N ≃* L := N.equivMapOfInjective eQ.toMonoidHom eQ.injective
    have hmodel : Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K) := by
      rcases eN with ⟨⟨eN⟩⟩ | ⟨⟨eN⟩⟩
      · exact Or.inl ⟨eL.symm.trans eN⟩
      · exact Or.inr ⟨eL.symm.trans eN⟩
    exact alternatives_of_normal_linear hG hcore L K hK hmodel

theorem corefree_dihedral_generalized_fitting_alternatives
    {G : Type u} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) (n : ℕ) (hn : 2 ≤ n)
    (e : S ≃* DihedralGroup (2 ^ (n - 1))) :
    IsPGroup 2 G ∨ Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (G ≃* Equiv.Perm (Fin 4)) ∨
      (IsSimpleGroup (CFSG.generalizedFitting G) ∧
        (∃ x y : CFSG.generalizedFitting G, x * y ≠ y * x) ∧
        Subgroup.centralizer (CFSG.generalizedFitting G : Set G) = ⊥ ∧
        ∀ T : Sylow 2 (CFSG.generalizedFitting G),
          ∃ m : ℕ, 2 ≤ m ∧ Nonempty (T ≃* DihedralGroup (2 ^ (m - 1)))) :=
  alternatives_of_hasDihedralSylowTwo hcore
    (hasDihedralSylowTwo_of_supplied S n hn e)

end

end CFSG.Semidihedral.CoreFreeDihedral
