module

public import CFSG.GH74.Generic.BProg.Cor2Easy
public import CFSG.GH74.Generic.BProg.B2.Lemma82Gen
public import CFSG.GH74.GLS.TwoThin.Basic

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Uniqueness CFSG.ABGLocalTools
  CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

theorem le_of_inU0_of_odd {G : Type} [Group G] [Finite G] {M : Subgroup G} {B X : Subgroup G}
    (hB : InU0 M B) (hX : Odd (Nat.card ↥X)) (hBX : B ≤ normalizer (X : Set G)) : X ≤ M := by
  obtain ⟨⟨-, hBel, hr2⟩, -, hγ⟩ := hB
  refine (le_iSup_centralizer_hyperplanes hBel hr2 hBX hX).trans ?_
  refine iSup_le fun E => iSup_le fun hEB => iSup_le fun hEr => ?_
  have hEγ : normalizer (E : Set G) ≤ gammaK 2 B (pRank 2 ↥B - 1) :=
    le_iSup₂_of_le E hEB (le_iSup_of_le hEr le_rfl)
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans (hEγ.trans hγ))

theorem pPrimeCoreOf_le_of_inU0 {G : Type} [Group G] [Finite G] {M B C : Subgroup G}
    (hB : InU0 M B) (hBC : B ≤ C) : pPrimeCoreOf 2 C ≤ M := by
  refine le_of_inU0_of_odd hB (TwoThin.card_pPrimeCoreOf_odd C) fun b hb => ?_
  have key : ∀ b ∈ C, ∀ n ∈ pPrimeCoreOf 2 C, b * n * b⁻¹ ∈ pPrimeCoreOf 2 C :=
    fun b hb n hn => TwoThin.pPrimeCoreOf_normalized C hb hn
  refine mem_normalizer_iff.2 fun n => ⟨key b (hBC hb) n, fun hn => ?_⟩
  have := key b⁻¹ (C.inv_mem (hBC hb)) _ hn
  rwa [show b⁻¹ * (b * n * b⁻¹) * b⁻¹⁻¹ = n by group] at this

theorem le_M_of_normal_of_inU0 {G : Type} [Group G] [Finite G] {A M : Subgroup G}
    (h2 : Stage2Concl2 M) (hA : InU0 M A) {N X : Subgroup G} (hNX : N ≤ X)
    (hN : (N.subgroupOf X).Normal) (hAN : A ≤ N) (hNM : N ≤ M) : X ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hA.1.2.1
  have hAp : IsPGroup 2 ↥A := IsElementaryAbelian.isPGroup 2 ↥A
  have hAp' : IsPGroup 2 (A.subgroupOf N) := hAp.comap_subtype
  obtain ⟨T, hT⟩ := hAp'.exists_le_sylow
  have hPN : IsSylowOf 2 ((T : Subgroup N).map N.subtype) N := ⟨T, rfl⟩
  have hAP : A ≤ (T : Subgroup N).map N.subtype := fun a ha =>
    ⟨⟨a, hAN ha⟩, hT (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hPM : (T : Subgroup N).map N.subtype ≤ M := cor2_c h2 _ A hPN.isPGroup hA hAP
  have hNP : normalizer (((T : Subgroup N).map N.subtype : Subgroup G) : Set G) ≤ M :=
    cor2_a h2 _ A hPM hA hAP
  have hX : N ⊔ (X ⊓ normalizer (((T : Subgroup N).map N.subtype : Subgroup G) : Set G)) = X :=
    CFSG.Semidihedral.Local.sup_inf_normalizer_eq hNX hN hPN.le (by simpa using hPN.card_eq)
  rw [← hX]
  exact sup_le hNM (inf_le_right.trans hNP)

end CFSG.GH74.Generic.BProg.B2
