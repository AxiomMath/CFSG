module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHNT

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

structure T5NTData {K H : Type} [Group K] [Group H] (ψ : K →* H) (R R' : Subgroup K) (z : H)
    (A : Subgroup H) (x x' : K) : Prop where
  mem : x ∈ R
  mem' : x' ∈ R'
  sq : x * x = 1
  sq' : x' * x' = 1
  comm : x * x' = x' * x
  central : ∀ r ∈ R, x * r = r * x
  central' : ∀ r ∈ R', x' * r = r * x'
  comm_RR' : ∀ r ∈ R, ∀ r' ∈ R', r * r' = r' * r
  map_x : ψ x = z
  map_x'_mem : ψ x' ∈ R'.map ψ
  map_x'_ne_one : ψ x' ≠ 1
  ne : z ≠ ψ x'
  elems : ∀ a ∈ A, a = 1 ∨ a = z ∨ a = ψ x' ∨ a = z * ψ x'

variable {p f : ℕ} [Fact p.Prime]

theorem thm5IH_nt_front {t : StatedLieTag} {k e : ℕ} (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t k p e)
    (hef : e = f) {H : Type} [Group H] [Finite H] (ψ : (modelUniv t k p e Fact.out).K →* H)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    {R R' : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (eK : Nonempty (↥(R.map ψ) ≃* SL(2, GaloisField p f)))
    (eJ : Nonempty (↥(R'.map ψ) ≃* SL(2, GaloisField p f)))
    (hcomm : Commutes (R.map ψ) (R'.map ψ)) {z : H} (hz : IsUniqueInvolution (R.map ψ) z)
    (hzJ : z ∉ R'.map ψ) {A : Subgroup H} (hA : IsElemAbelian2 A 2)
    (hAKJ : A ≤ R.map ψ ⊔ R'.map ψ) :
    ∃ x x' : (modelUniv t k p e Fact.out).K, T5NTData ψ R R' z A x x' := by
  subst hef
  obtain ⟨eK⟩ := eK
  obtain ⟨eJ⟩ := eJ
  have hA2 : ∀ a ∈ A, a * a = 1 := hA.2
  have hf0 : e ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e hf0]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have hperf := CFSG.ClassicalInvolution.RouteD.Gaps.fundPerfect_modelUniv hp2 hfund hadm (by omega)
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2
    (isFundTag_modelFacts hfund) hadm hG2 hD4 hR
  obtain ⟨eR'⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2
    (isFundTag_modelFacts hfund) hadm hG2 hD4 hR'
  have hFinR : Finite ↥R := Finite.of_equiv _ eR.symm.toEquiv
  have hFinR' : Finite ↥R' := Finite.of_equiv _ eR'.symm.toEquiv
  have hinjR : ∀ x ∈ R, ∀ y ∈ R, ψ x = ψ y → x = y := by
    refine thm5IH_injOn_of_card_le ψ ?_
    rw [Nat.card_congr eR.toEquiv, Nat.card_congr eK.toEquiv]
  have hinjR' : ∀ x ∈ R', ∀ y ∈ R', ψ x = ψ y → x = y := by
    refine thm5IH_injOn_of_card_le ψ ?_
    rw [Nat.card_congr eR'.toEquiv, Nat.card_congr eJ.toEquiv]
  have hcommRR' : Commutes R R' := ih8_commutes_of_commutes_map ψ hker (hperf R hR) hcomm
  have hxR : sl2Inv eR ∈ R := sl2Inv_mem eR
  have hx2 : sl2Inv eR * sl2Inv eR = 1 := sl2Inv_mul_self hodd eR
  have hx1 : sl2Inv eR ≠ 1 := sl2Inv_ne_one hodd eR
  have hψx : ψ (sl2Inv eR) = z := by
    have hmem : ψ (sl2Inv eR) ∈ R.map ψ := Subgroup.mem_map_of_mem ψ hxR
    have hsq : ψ (sl2Inv eR) * ψ (sl2Inv eR) = 1 := by rw [← map_mul, hx2, map_one]
    rcases hz.unique _ hmem hsq with h | h
    · exact absurd (hinjR _ hxR 1 R.one_mem (by rw [h, map_one])) hx1
    · exact h
  have hxR' : sl2Inv eR' ∈ R' := sl2Inv_mem eR'
  have hx'2 : sl2Inv eR' * sl2Inv eR' = 1 := sl2Inv_mul_self hodd eR'
  have hx'1 : sl2Inv eR' ≠ 1 := sl2Inv_ne_one hodd eR'
  have hJt : IsUniqueInvolution (R'.map ψ) (ψ (sl2Inv eR')) :=
    { mem := Subgroup.mem_map_of_mem ψ hxR'
      ne_one := fun h => hx'1 (hinjR' _ hxR' 1 R'.one_mem (by rw [h, map_one]))
      sq := by rw [← map_mul, hx'2, map_one]
      unique := by
        rintro _ ⟨r, hr, rfl⟩ hsq
        have hr2 : r * r = 1 := hinjR' _ (R'.mul_mem hr hr) 1 R'.one_mem
          (by rw [map_mul, hsq, map_one])
        by_cases hr1 : r = 1
        · left
          rw [hr1, map_one]
        · right
          have hord : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hr2) hr1
          rw [eq_sl2Inv_of_orderOf_eq_two hodd eR' hr hord] }
  refine ⟨sl2Inv eR, sl2Inv eR', ?_⟩
  exact
    { mem := hxR
      mem' := hxR'
      sq := hx2
      sq' := hx'2
      comm := hcommRR' _ hxR _ hxR'
      central := fun r hr => sl2Inv_commute eR hr
      central' := fun r hr => sl2Inv_commute eR' hr
      comm_RR' := hcommRR'
      map_x := hψx
      map_x'_mem := hJt.mem
      map_x'_ne_one := hJt.ne_one
      ne := fun h => hzJ (h ▸ hJt.mem)
      elems := fun a ha => thm5IH_mem_four_nt hcomm hz hJt hzJ (hAKJ ha) (hA2 a ha) }

end CFSG.ClassicalInvolution.Asc77
