module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallMain
public import CFSG.ClassicalInvolution.Q3.TA3LeafTwistedG2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.LiteratureLocal
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open CFSG.CGT.PushingUpLit.SolKNA.R4
open scoped MatrixGroups commutatorElement

theorem isQuasisimple_of_simple_nonab {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (h : ∃ a b : Q, a * b ≠ b * a) : CFSG.IsQuasisimple Q := by
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h' | h'
    · exact h'
    · obtain ⟨a, b, hab⟩ := h
      exact absurd ((Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top b)) a) hab
  have hperf : Group.IsPerfect Q := by
    refine Group.isPerfect_def.mpr ?_
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h' | h'
    · exfalso
      obtain ⟨a, b, hab⟩ := h
      have h1 : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h']
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp h1)
    · exact h'
  have e : (Q ⧸ Subgroup.center Q) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e.symm a, e.symm b, fun h' => hab ?_⟩
  have := congrArg e h'
  simpa using this


theorem twinCyc4_twistedG2 {X : Type} [Group X] {f : ℕ}
    (hree : ReeTitsModel X .twistedG2 3 f) : TwinCyc4 X := by
  obtain ⟨-, -, -, -, -, h3⟩ := hree.1
  obtain ⟨a, hea, -⟩ := hree.2
  subst hea
  have ha : 1 ≤ a := by omega
  obtain ⟨hfin, -, hcen, -⟩ := ward_kleidman_small_Ree_involution_centralizer_maximal a ha X hree
  haveI := hfin
  intro z hz
  obtain ⟨L, hLC, -, hsup, ⟨eL⟩, hZ⟩ := hcen z hz
  refine ⟨⊥, inferInstance, ?_⟩
  intro N hNs hNsub u huN hu4
  exfalso
  have hE4 : 4 ≤ Nat.card (GaloisField 3 (2 * a + 1)) := by
    rw [GaloisField.card 3 (2 * a + 1) (by omega)]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : IsSimpleGroup PSL(2, GaloisField 3 (2 * a + 1)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hE4
  have : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hLnab : ∃ u v : ↥L, u * v ≠ v * u := CFSG.Walter.exists_mul_ne_mul_of_mulEquiv_psl2 hE4 eL
  set C := Subgroup.centralizer ({z} : Set X) with hCdef
  have hcomm : ∀ x ∈ Subgroup.zpowers z, ∀ l ∈ L, x * l = l * x := by
    intro x hx l hl
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((show Commute z l from
      (Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)).symm).zpow_left n).eq
  have hdec : ∀ c ∈ C, ∃ x ∈ Subgroup.zpowers z, ∃ l ∈ L, c = x * l := by
    intro c hc
    rw [← hsup] at hc
    obtain ⟨x, hx, l, hl, rfl⟩ :=
      (CFSG.QuasithinUnique.ComponentSplitting.mem_sup_iff_of_commute hcomm).mp hc
    exact ⟨x, hx, l, hl, rfl⟩
  have hCL : ∀ c ∈ C, ∀ l ∈ L, c * l * c⁻¹ ∈ L := by
    intro c hc l hl
    obtain ⟨x, hx, l', hl', rfl⟩ := hdec c hc
    have e : x * l' * l * (x * l')⁻¹ = l' * l * l'⁻¹ := by
      have h1 := hcomm x hx (l' * l * l'⁻¹) (L.mul_mem (L.mul_mem hl' hl) (L.inv_mem hl'))
      calc x * l' * l * (x * l')⁻¹ = x * (l' * l * l'⁻¹) * x⁻¹ := by group
        _ = l' * l * l'⁻¹ := by rw [h1, mul_inv_cancel_right]
    rw [e]
    exact L.mul_mem (L.mul_mem hl' hl) (L.inv_mem hl')
  have hLn : (L.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLC]
    intro l c hl hc
    exact hCL c hc l hl
  have hLsub : CFSG.Open.IsSubnormal L C :=
    CFSG.Open.IsSubnormal.step hLC hLn (CFSG.Open.IsSubnormal.refl C)
  have hLq : CFSG.IsQuasisimple ↥L := isQuasisimple_of_simple_nonab hLnab
  have huC : u ∈ C := hNsub.le huN
  have huL := commute_of_solvable_subnormal hLsub hLq hNsub hNs
  have hucent : (⟨u, huC⟩ : ↥C) ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    obtain ⟨x, hx, l, hl, hcx⟩ := hdec c.1 c.2
    have hxu : x * u = u * x := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((show Commute z u from
        (Subgroup.mem_centralizer_singleton_iff.mp huC).symm).zpow_left m).eq
    have hlu : l * u = u * l := huL l hl u huN
    show (c : X) * u = u * (c : X)
    calc (c : X) * u = x * l * u := by rw [hcx]
      _ = x * (l * u) := by rw [mul_assoc]
      _ = x * (u * l) := by rw [hlu]
      _ = (x * u) * l := by rw [mul_assoc]
      _ = (u * x) * l := by rw [hxu]
      _ = u * (x * l) := by rw [mul_assoc]
      _ = u * c := by rw [hcx]
  have hmem : u ∈ Subgroup.zpowers z := by
    have : u ∈ (Subgroup.center C).map C.subtype := ⟨_, hucent, rfl⟩
    rwa [hZ] at this
  have hdvd := orderOf_dvd_of_mem_zpowers hmem
  rw [hu4, hz] at hdvd
  exact absurd hdvd (by norm_num)


theorem false_of_twistedG2 {r n : ℕ} (hr : 4 ≤ r) {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t)
    (hF : SmallTwistedG2 ↥(genFittingFStar Y)) : False := by
  haveI := h.core.simple
  obtain ⟨f, hm⟩ := hF
  rcases hm with ⟨htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, -, hree⟩ | ⟨-, htag, -⟩
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · obtain ⟨-, -, -, -, -, h3⟩ := hree.1
    obtain ⟨a, hea, -⟩ := hree.2
    subst hea
    obtain ⟨-, -, -, -, -, -, hodd⟩ :=
      ward_kleidman_small_Ree_involution_centralizer_maximal a (by omega) _ hree
    exact false_of_twinCyc4 hr h (socleComm2_of_outTwoCyclic (outTwoCyclic_of_odd hodd))
      (twinCyc4_twistedG2 hree)
  · exact absurd htag (by decide)

theorem twinLeafR_twistedG2 {r n : ℕ} (hr : 4 ≤ r) : TwinLeafR r n SmallTwistedG2 :=
  fun _ _ _ _ _ _ hP _ hF => false_of_twistedG2 hr hP hF

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
