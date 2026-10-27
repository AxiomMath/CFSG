module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4Out
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4U1
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4U2
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels
public import CFSG.ClassicalInvolution.Q3.TA3SmallTools
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Gen

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatFactsSp4
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.Blueprint

theorem Q5Sp4.noQ8Datum_psp4 {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) : NoQ8Datum (StatedProj (StatedSp 2 K)) := by
  intro G _ _ N _ ⟨e⟩ hC _ R S t hD _
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  have htN : t ∈ N := TightDatum.mem_of_noQ8Outer hD hC fun φ => Q5Sp4.not_injective_outer h2 e φ
  have hu2 : orderOf (e ⟨t, htN⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hD.order]
  obtain ⟨g, hg⟩ := ComponentClassification.CatFactsSp4.exists_conj_of_orderOf_eq_two hodd hu2
  set e' : ↥N ≃* StatedProj (StatedSp 2 K) := e.trans (MulAut.conj g⁻¹) with he'
  have he't : e' ⟨t, htN⟩ = g⁻¹ * e ⟨t, htN⟩ * g := by simp [he']
  rcases hg with h1 | h1
  · have := Q5Sp4.isPerfect_X0 hodd h4
    exact TightDatum.false_of_model hD hC e' htN (he't.trans h1) (X0 K) X0_le_centralizer
      (fun M hM hp => perfect_le_map_centralizer (T1 K) hM hp) (Q5Sp4.noOddNormal_X0 hodd h4)
      (Q5Sp4.noQ8Fix_X0 hodd h4)
  · have := TA3.Sp4.isPerfect_Lsub (K := K) h4
    have := isSimpleGroup_Lsub (K := K) h4
    have hnab : ∃ a b : ↥(Lsub K), a * b ≠ b * a :=
      exists_ne_comm_of_commutator_eq_top Group.IsPerfect.commutator_eq_top
    exact TightDatum.false_of_model hD hC e' htN (he't.trans h1) (Lsub K) Lsub_le_centralizer
      (fun M hM hp => perfect_le_L h2 hM hp) (noOddNormal_of_isSimpleGroup hnab)
      (Q5Sp4.noQ8Fix_Lsub hodd h4)

theorem NoQ8Datum.of_mulEquiv {F F' : Type} [Group F] [Group F'] (h : NoQ8Datum F)
    (e : F' ≃* F) : NoQ8Datum F' := fun G _ _ N _ ⟨e'⟩ hC hgen R S t hD hS =>
  h G N ⟨e'.trans e⟩ hC hgen R S t hD hS

theorem noQ8Datum_psp4Ne3 : ∀ (F : Type) [Group F], SmallPSp4Ne3 F → NoQ8Datum F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, hq3, hL⟩ := hF
  rcases hL with ⟨-, ⟨-, K, _, _, hK, ⟨e⟩⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have hodd : Odd (Nat.card K) := by
      rw [hK]
      exact (hp.eq_two_or_odd'.resolve_left hp2).pow
    have h3 : 3 ≤ Nat.card K := by
      rw [hK]
      calc 3 ≤ p := by
            rcases hp.eq_two_or_odd' with h | h
            · exact absurd h hp2
            · have := hp.two_le
              obtain ⟨k, hk⟩ := h
              omega
        _ ≤ p ^ f := Nat.le_self_pow (by omega) p
    have h5 : 5 ≤ Nat.card K := by
      obtain ⟨k, hk⟩ := hodd
      rw [hK] at hk
      omega
    exact (Q5Sp4.noQ8Datum_psp4 hodd h5).of_mulEquiv e
  all_goals exact absurd ht (by decide)

theorem smallSimpleLeaf_psp4Ne3 : SmallSimpleLeaf SmallPSp4Ne3 :=
  smallSimpleLeaf_of_noQ8Datum noQ8Datum_psp4Ne3

end CFSG.ClassicalInvolution.Q3.TA3
