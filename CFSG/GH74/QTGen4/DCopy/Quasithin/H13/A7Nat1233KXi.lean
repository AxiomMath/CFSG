module

public import CFSG.Quasithin.H13.A7Nat1233KXi
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL6

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

theorem oddPre_le_centralizer_F4 (h3214 : Stmt3_2_14_F4) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : QuasithinUnique.quasithinIsQTKECat G)
    {T K : Subgroup G} (hT : quasithinIsSylowTwo T) (hloc : quasithinIsLocal T K)
    (hTK : T ≤ normalizer (K : Set G)) (hnq : ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    oddPre K T ≤ centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ T)) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := oddPre K T with hPdef
  set X := oTwoUpper P with hX
  have hO : pCoreOf 2 (K ⊔ T) ≠ ⊥ := hloc.2.2.2
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hchar : QuasithinUnique.CharTwo (K ⊔ T) :=
    charTwo_of_inH hQ.2.1 S ⟨hS ▸ le_sup_right, hO⟩
  have hR := h3214 G T K hs hnab hQ hT hloc hnq
  have hPK : P ≤ K := oddPre_le K T
  have hKP : K ≤ normalizer (P : Set G) := le_normalizer_oddPre K T
  have hXP : X ≤ P := oTwoUpper_le P
  have hKM : K ≤ K ⊔ T := le_sup_left
  have hMK : K ⊔ T ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hXsub : IsSubnormal X (K ⊔ T) :=
    IsSubnormal.step hXP ((Subgroup.normal_subgroupOf_iff_le_normalizer hXP).mpr
      (le_normalizer_oTwoUpper P)) (IsSubnormal.step hPK
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hPK).mpr hKP)
        (A3.subnormal_of_normal hKM
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMK)))
  have hXR : ⁅twoReducedJoin (K ⊔ T), X⁆ = ⊥ := by
    rw [← primeReducedAggregate_map_subtype_eq_twoReducedJoin,
      Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    exact (hXP.trans (oddPre_le_solvableRadical K T)).trans hR
  have htfae := a4_11 hchar (A4.oTwoUpper_oTwoUpper P).symm hXsub
    (noncentral_oTwoUpper_oddPre K T)
  have h13 : IsXf X ↔ ⁅twoReducedJoin (K ⊔ T), X⁆ ≠ ⊥ := htfae.out 1 3
  have hnXf : ¬ IsXf X := fun hXf => h13.mp hXf hXR
  have hXC : X ≤ centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ T)) : Set G) := by
    by_cases hX1 : X = ⊥
    · rw [hX1]
      exact bot_le
    have hXc : IsXClass X :=
      ⟨hX1, (A4.oTwoUpper_oTwoUpper P).symm, A4.charTwo_of_subnormal hXsub hchar⟩
    have hVY : VY X = ⊥ := by
      by_contra hne
      exact hnXf ⟨hXc, hne⟩
    have hb : ¬ ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ T)), X⁆ ≠ ⊥ := fun hne =>
      ((a4_9 hXc hXsub).mp hne) hVY
    rw [not_not, Subgroup.commutator_eq_bot_iff_le_centralizer] at hb
    exact Subgroup.le_centralizer_iff.mp hb
  intro y hy
  apply mem_of_odd_two_pow (orderOf_pos y).ne'
  · intro m hm
    exact hXC (mem_oTwoUpper_of_odd (P.pow_mem hy m) hm)
  · intro m k hk
    have hmem := mem_pCoreOf_of_mem_oddPre (P.pow_mem hy m) hk
    rw [mem_centralizer_iff]
    intro w hw
    exact (mem_centralizer_iff.1 (A4.centerOf_le_centralizer _
      (A4.omegaOneCenterOf_le_centerOf _ hw)) _ hmem).symm

end CFSG.Quasithin.H13.A7
