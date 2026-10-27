module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentTop2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain
public import CFSG.Sporadic.J4.QTRankInvProof

public section

namespace CFSG.QuasithinUnique.Id2519.J4Row

open CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open scoped commutatorElement

@[expose] def CentralizerCore (c : ℕ) : Prop :=
  ∃ N : Subgroup J, N ≤ Subgroup.centralizer ({eta uJ 11 c} : Set J) ∧
    (∀ q ∈ Subgroup.centralizer ({eta uJ 11 c} : Set J), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧
    IsPGroup 2 ↥N ∧
    ∀ q ∈ Subgroup.centralizer ({eta uJ 11 c} : Set J), (∀ e ∈ N, q * e = e * q) → q ∈ N

theorem noComponent_of_normal_pgroup {M : Type*} [Group M] [Finite M] {K N : Subgroup M}
    (hNK : N ≤ K) (hn : ∀ q ∈ K, ∀ e ∈ N, q * e * q⁻¹ ∈ N) (hp : IsPGroup 2 ↥N)
    (hc : ∀ q ∈ K, (∀ e ∈ N, q * e = e * q) → q ∈ N) (B : Subgroup ↥K) :
    ¬ CFSG.IsComponent B := by
  intro hB
  have hUn : (N.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNK]
    intro e q he hq
    exact hn q hq e he
  have hUp : IsPGroup 2 ↥(N.subgroupOf K) := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNK).symm
  have hUs : Group.IsSolvable ↥(N.subgroupOf K) := by
    have : Group.IsNilpotent ↥(N.subgroupOf K) := hUp.isNilpotent
    infer_instance
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hUs hUn.isSubnormal).1 B hB
  have hBN : ∀ b : ↥B, (((b : ↥K)) : M) ∈ N := by
    intro b
    apply hc _ (b : ↥K).2
    intro e he
    have hmem : ⁅(b : ↥K), (⟨e, hNK he⟩ : ↥K)⁆ ∈ ⁅B, N.subgroupOf K⁆ :=
      Subgroup.commutator_mem_commutator b.2 (Subgroup.mem_subgroupOf.mpr he)
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact congrArg Subtype.val hmem
  have hBle : B ≤ N.subgroupOf K := fun b hb => Subgroup.mem_subgroupOf.2 (hBN ⟨b, hb⟩)
  have hBp : IsPGroup 2 ↥B := hUp.to_le hBle
  have hBs : Group.IsSolvable ↥B := by
    have : Group.IsNilpotent ↥B := hBp.isNilpotent
    infer_instance
  have : Nontrivial ↥B := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
  have : Group.IsPerfect ↥B := hB.1.1
  exact Group.IsPerfect.not_isSolvable ↥B hBs

theorem hasKComponent_centralizer_of_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {a : G} {b : G'} (hab : e a = b) (h : HasKComponent ↥(Subgroup.centralizer ({a} : Set G))) :
    HasKComponent ↥(Subgroup.centralizer ({b} : Set G')) := by
  have heq : (Subgroup.centralizer ({a} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({b} : Set G') := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← hab]
      show e a * e y = e y * e a
      rw [← map_mul, ← map_mul, hy]
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply, hab]
      exact hz
  exact h.of_mulEquiv (((Subgroup.centralizer ({a} : Set G)).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr heq))

theorem hasKComponent_centralizer_of_equiv_sub {G M : Type*} [Group G] [Group M] (H : Subgroup M)
    (e : G ≃* H) {a : G} {b : H} (hab : e a = b)
    (h : HasKComponent ↥(Subgroup.centralizer ({a} : Set G))) :
    HasKComponent ↥(Subgroup.centralizer ({b} : Set ↥H)) :=
  hasKComponent_centralizer_of_equiv e hab h

theorem center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnc : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp this b).symm

theorem noK_centralizer_of_core {c : ℕ} (h : CentralizerCore c) :
    ¬ HasKComponent ↥(Subgroup.centralizer ({eta uJ 11 c} : Set J)) := by
  rintro ⟨B, hB, -⟩
  obtain ⟨N, hNK, hn, hp, hc⟩ := h
  exact noComponent_of_normal_pgroup hNK hn hp hc B hB

theorem noK_centralizer_of_involution
    (h1 : CentralizerCore 1) (h3 : CentralizerCore 3) {r : J}
    (hsq : r * r = 1) (hne : r ≠ 1) :
    ¬ HasKComponent ↥(Subgroup.centralizer ({r} : Set J)) := by
  intro hk
  rcases inv_conj_root CFSG.Sporadic.J4.j4Facts hsq hne with hc | hc
  · obtain ⟨x, hx⟩ := isConj_iff.1 hc
    refine noK_centralizer_of_core h1 (hasKComponent_centralizer_of_equiv (MulAut.conj x).symm
      (a := r) (b := eta uJ 11 1) ?_ hk)
    rw [MulAut.conj_symm_apply, ← hx]
    group
  · obtain ⟨x, hx⟩ := isConj_iff.1 hc
    refine noK_centralizer_of_core h3 (hasKComponent_centralizer_of_equiv (MulAut.conj x).symm
      (a := r) (b := eta uJ 11 3) ?_ hk)
    rw [MulAut.conj_symm_apply, ← hx]
    group

theorem tabIdentFor_j4_of_equiv
    (e : NativeSporadic.Carrier .J4 ≃* J) (hodd : Ch1.J4OutOdd)
    (h1 : CentralizerCore 1) (h3 : CentralizerCore 3) :
    TabIdentFor (@Ident.FamSporadic .J4) := by
  have hsimple : IsSimpleGroup (NativeSporadic.Carrier .J4) :=
    CFSG.Sporadic.J4.fam_j4_simplicity.2.2
  have hnc : ∃ a b : NativeSporadic.Carrier .J4, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : IsSimpleGroup NativeSporadic.J4 := CFSG.Sporadic.J4.fam_j4_simplicity.2.2
    let _ : CommGroup NativeSporadic.J4 :=
      { (inferInstance : Group NativeSporadic.J4) with mul_comm := fun a b => hcon a b }
    have : Finite NativeSporadic.J4 := CFSG.Sporadic.J4.fam_j4_simplicity.1
    have hp := IsSimpleGroup.prime_card (α := NativeSporadic.J4)
    rw [CFSG.Sporadic.J4.card_J4] at hp
    exact absurd hp (by norm_num)
  refine MathNoLayer.tabIdentFor_of_fix hsimple hnc ?_
  intro α hα2 hα1 hk
  have := hsimple
  have hα2' : ∀ x, α (α x) = x := fun x => by
    have := congrArg (fun f : MulAut (NativeSporadic.Carrier .J4) => f x) hα2
    simpa using this
  obtain ⟨l, hl⟩ := Ch1.isInnerAut_of_outer_odd
    (MulEquiv.refl (NativeSporadic.Carrier .J4)) hodd α hα2'
  have hZ : Subgroup.center (NativeSporadic.Carrier .J4) = ⊥ := center_eq_bot_of_simple hnc
  have hl2 : l * l = 1 := by
    have hmem : l * l ∈ Subgroup.center (NativeSporadic.Carrier .J4) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := hα2' x
      rw [hl, hl] at h
      calc x * (l * l) = (l * l) * (l⁻¹ * (l⁻¹ * x * l) * l) := by group
        _ = (l * l) * x := by rw [h]
    rw [hZ] at hmem
    exact hmem
  have hl1 : l ≠ 1 := by
    rintro rfl
    apply hα1
    ext x
    rw [hl]
    simp
  have hfix : fixSubgroup α = Subgroup.centralizer ({l} : Set (NativeSporadic.Carrier .J4)) := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, mem_fixSubgroup, hl]
    constructor
    · intro h
      calc x * l = l * (l⁻¹ * x * l) := by group
        _ = l * x := by rw [h]
    · intro h
      calc l⁻¹ * x * l = l⁻¹ * (x * l) := by group
        _ = l⁻¹ * (l * x) := by rw [h]
        _ = x := by group
  rw [hfix] at hk
  have hk' : HasKComponent ↥(Subgroup.centralizer ({e l} : Set J)) :=
    hasKComponent_centralizer_of_equiv_sub J e rfl hk
  refine noK_centralizer_of_involution h1 h3 (r := e l) ?_ ?_ hk'
  · rw [← map_mul, hl2, map_one]
  · intro h
    exact hl1 (e.injective (by rw [h, map_one]))

theorem tabIdentFor_j4_of
    (hodd : Ch1.J4OutOdd) (h1 : CentralizerCore 1) (h3 : CentralizerCore 3) :
    TabIdentFor (@Ident.FamSporadic .J4) :=
  tabIdentFor_j4_of_equiv (seedEquiv CFSG.Sporadic.J4.j4Facts.mat) hodd h1 h3

theorem tabIdent_of_j4Core
    (hodd : Ch1.J4OutOdd) (h1 : CentralizerCore 1)
    (h3 : CentralizerCore 3) : TabIdent :=
  tabIdent_of_open2 ⟨tabIdentFor_j4_of hodd h1 h3⟩

end CFSG.QuasithinUnique.Id2519.J4Row
