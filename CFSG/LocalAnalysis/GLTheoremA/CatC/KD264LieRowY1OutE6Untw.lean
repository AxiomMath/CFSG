module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutE6Rank
public import CFSG.HardMathSupport.Lang.E6Descent.OuterDescentE
public import CFSG.HardMathSupport.Lang.E6Descent.RankE6
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
  (inner innAutDerived inner_le_innAutDerived commutator_le_innAutDerived inner_map_congr
    mem_innAutDerived_congr)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge
open scoped commutatorElement

theorem y1out_commutator_le_ker_of_comm {G H : Type*} [Group G] [Group H] (Θ : G →* H)
    (hH : ∀ a b : H, a * b = b * a) : commutator G ≤ Θ.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2 (hH _ _)

theorem y1out_innAutDerived_le_ker_of_comm {X H : Type*} [Group X] [Group H] (Θ : MulAut X →* H)
    (hH : ∀ a b : H, a * b = b * a) (hinn : inner X ≤ Θ.ker) : innAutDerived X ≤ Θ.ker :=
  sup_le hinn (y1out_commutator_le_ker_of_comm Θ hH)

theorem y1out_mul_comm_of_isCyclic {G : Type*} [Group G] [IsCyclic G] (a b : G) : a * b = b * a :=
  ((MonoidHom.id G).isMulCommutative_of_isCyclic_of_ker_le_center
    (by rw [MonoidHom.ker_id]; exact bot_le)).is_comm.comm a b

section Certificates


theorem inner_of_pow_three_adjointE6 {K : Type} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ n) (h3 : ¬ 3 ∣ Nat.card K - 1)
    {x : MulAut (adjointGroup Tag.E6 K)} (hx : x ∈ innAutDerived (adjointGroup Tag.E6 K))
    (hx3 : x ^ 3 = 1) : x ∈ inner (adjointGroup Tag.E6 K) := by
  classical
  obtain ⟨Θ, -, -, hker, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  haveI : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic hp K hK).2
  have hH : ∀ a b : RingAut K × Multiplicative (ZMod (exactE Tag.E6)), a * b = b * a := by
    intro a b
    exact Prod.ext (y1out_mul_comm_of_isCyclic a.1 b.1) (mul_comm a.2 b.2)
  have hinn : inner (adjointGroup Tag.E6 K) ≤ Θ.ker := by
    rintro _ ⟨g, rfl⟩
    refine (hker _).2 ⟨g, 1, fun h => ?_⟩
    simp [rootDiagUnit_one, MulAut.conj_apply]
  have hxk : x ∈ Θ.ker := y1out_innAutDerived_le_ker_of_comm Θ hH hinn hx
  obtain ⟨g, a, hga⟩ := (hker x).1 hxk
  have hxeq : x = MulAut.conj g * rootDiagAut Tag.E6 K a := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hga h]
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_rootDiagAut]
    group
  by_contra hxo
  exact h3 (CFSG.HardMathSupport.Lang.E6Descent.prime_dvd_of_diag_noninner Tag.E6 (Or.inl rfl) K
    Nat.prime_three g a x hxeq hx3 hxo).2

end Certificates

section Catalogue


theorem kd264Y1OutE6_untwisted (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
    [Finite (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group]
    (hpR : CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group) ≤ 3)
    {a : MulAut (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group}
    (ha : a ∈ innAutDerived (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group) (ha3 : a ^ 3 = 1) :
    a ∈ inner (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group := by
  classical
  by_cases h3 : 3 ∣ q.card - 1
  · exfalso
    obtain ⟨E, hE, h243⟩ := CFSG.HardMathSupport.Lang.E6Descent.exists_elemAbelian_243_E6 q hv h3
    have := y1out_five_le_pRank_top_of_card_ge hE h243
    omega
  · obtain ⟨K, hfield, hfin, hK, -, ⟨eA⟩⟩ :=
      exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
    letI := hfield
    letI := hfin
    have hK' : Nat.card K = q.p ^ q.exponent := hK.trans q.card_def
    have h3K : ¬ 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
    have ha' : MulAut.congr eA a ∈ innAutDerived (adjointGroup Tag.E6 K) :=
      (mem_innAutDerived_congr eA).2 ha
    have ha3' : (MulAut.congr eA a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
    have hin := inner_of_pow_three_adjointE6 q.prime_p hK' h3K ha' ha3'
    rw [← inner_map_congr eA] at hin
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hin
    have hb' : b = a := (MulAut.congr eA).injective hba
    rw [hb'] at hb
    exact hb

end Catalogue

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
