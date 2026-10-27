module

public import CFSG.GH74.Generic.BProg.B3.S3T2L291A
public import CFSG.GH74.Generic.BProg.B3.DictS3Adm
public import CFSG.GH74.GLS.Balance.OResidual
public import CFSG.GH74.Generic.BProg.B1.PilotS3

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
  Subgroup CFSG.GH74.Generic.BProg.B1.PilotS3 CFSG.GH74.Generic.BProg.B1.PilotS5
open scoped commutatorElement

namespace S3T2L291

variable {G : Type} [Group G] [Finite G]

theorem exists_split3 {x : G} {K : Subgroup G} (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Split3Like F (imgBar x K) := by
  have hZ := center_trivial_of_shape3 hK h3
  obtain ⟨eK⟩ := hat_equiv_imgBar hK
  obtain ⟨F, _, _, P, _, ⟨e⟩, hP⟩ := exists_equiv_grpS3_of_qShape3 h3
  exact ⟨F, inferInstance, inferInstance,
    Split3Like.of_equiv (eK.symm.trans e) hP (center_trivial_of_equiv eK hZ)⟩

theorem isSplit3_Lbar {F : Type} [Field F] [Finite F] {x e : G} {K : Subgroup G}
    (hKx : K ≤ centralizer ({x} : Set G)) (hY : Split3Like F (imgBar x K)) (heK : e ∈ K)
    (he2 : orderOf e = 2) :
    IsSplit3 F (bar x e) (Lbar x e K)
      (centralizer ({bar x e} : Set (CentralizerBar x)) ⊓ imgBar x K) := by
  obtain ⟨hbmem, -, hb2⟩ := bar_facts hKx heK he2
  obtain ⟨J, -, hJ⟩ := hY.split (bar x e) hbmem hb2
  have hJL : Lbar x e K = J := by
    apply le_antisymm
    · refine sSup_le fun L hL => ?_
      exact hJ.le_of_perfect' hL.1
        (TwoThin.commutator_self_of_isTwoComponent hL.1 (TwoThin.isPCompIn_two_iff.mp hL).2)
    · exact le_sSup hJ.isPCompIn
  rw [hJL]
  exact hJ

theorem isAdmPair_Lbar {F : Type} [Field F] [Finite F] {x e : G} {K A E : Subgroup G}
    (hx : orderOf x = 2) (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hxK : x ∉ K)
    (hY : Split3Like F (imgBar x K)) (hEK : E ≤ K) (hAE : A = E ⊔ zpowers x)
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE4 : Nat.card ↥E = 4) (heE : e ∈ E) (he1 : e ≠ 1) :
    IsAdmPair x K A e (Lbar x e K) := by
  have he2 : orderOf e = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) e heE) he1
  have hS := isSplit3_Lbar hK.1 hY (hEK heE) he2
  exact isAdmPair_of_split3_at hx hK hxK hY hEK hAE hEel hE4 heE he1
    (hS.le_H.trans inf_le_right) hS

omit [Finite G] in
theorem oPrimeResidualOf_le_liftAt {x e : G} {Lb : Subgroup (CentralizerBar x)} {P : Subgroup G}
    (hP : P ≤ centralizer ({x} : Set G) ⊓ centralizer ({e} : Set G))
    (h2 : ∀ g ∈ P, (∃ k : ℕ, g ^ (2 ^ k) = 1) → ∀ hg : g ∈ centralizer ({x} : Set G),
      proj x ⟨g, hg⟩ ∈ Lb) :
    oPrimeResidualOf 2 P ≤ liftAt x e Lb := by
  refine Balance.oPrimeResidualOf_le_of_two_elements fun g hg hg2 => ?_
  obtain ⟨hgx, hge⟩ := Subgroup.mem_inf.1 (hP hg)
  refine Balance.mem_oPrimeResidualOf_of_two_element ?_ hg2
  exact Subgroup.mem_inf.2 ⟨⟨⟨g, hgx⟩, h2 g hg hg2 hgx, rfl⟩, hge⟩

end S3T2L291

end CFSG.GH74.Generic.BProg.B3
