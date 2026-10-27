module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpOrd
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpPl
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpWr
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpWrRank
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinAbs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinSyl

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpSylProof

open CFSG.Open K421MonoProof K421OrbProof K421AbsProof K421SylProof K421LinProof K421SpProof

section Abstract

variable {X : Type} [Group X]

@[expose] def SylowAt (x : X) : Prop :=
  ∃ P : Sylow 3 X, (P : Subgroup X) ≤ Subgroup.centralizer ({x} : Set X)

theorem SylowAt.conj {x y n : X} (hn : n * x * n⁻¹ = y) (h : SylowAt y) : SylowAt x := by
  obtain ⟨P, hP⟩ := h
  refine ⟨n⁻¹ • P, ?_⟩
  rw [sylow_smul_coe]
  have h1 : (MulAut.conj n⁻¹) y = x := by
    rw [← hn]
    simp [MulAut.conj_apply, mul_assoc]
  have h2 := K421TransProof.centralizer_map_singleton (MulAut.conj n⁻¹) y
  rw [h1] at h2
  rw [← h2]
  exact Subgroup.map_mono hP

theorem SylowAt.of_equiv {S : Type} [Group S] [Finite X] [Finite S] (ε : S ≃* X) {x : S}
    (h : SylowAt (ε x)) : SylowAt x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := h
  refine ⟨P.mapSurjective (f := ε.symm.toMonoidHom) ε.symm.surjective, ?_⟩
  show (P : Subgroup X).map ε.symm.toMonoidHom ≤ Subgroup.centralizer ({x} : Set S)
  exact K421SpCWProof.map_symm_le_centralizer ε x hP

variable [Finite X]

theorem sylowShape_of_sylow_le_centralizer {x : X} (hcen : ∀ P : Sylow 3 X,
      IsCyclic ↥(Subgroup.center ↥(P : Subgroup X)))
    (hrk : ∀ P : Sylow 3 X, 3 ≤ CFSG.Open.pRank 3 (P : Subgroup X)) (h : SylowAt x) :
    SylowShape1517 (Subgroup.zpowers x) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR⟩ := h
  set N : Subgroup X := Subgroup.normalizer ((Subgroup.zpowers x : Subgroup X) : Set X) with hN
  have hCN : Subgroup.centralizer ({x} : Set X) ≤ N := by
    rw [← centralizer_zpowers_eq]
    exact Subgroup.centralizer_le_normalizer _
  have hRN : (R : Subgroup X) ≤ N := hR.trans hCN
  have hNpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hXpos : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have h1 : (Nat.card X).factorization 3 ≤ (Nat.card N).factorization 3 := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hNpos]
    have h2 : Nat.card ↥(R : Subgroup X) ∣ Nat.card N := Subgroup.card_dvd_of_le hRN
    rwa [Sylow.card_eq_multiplicity R] at h2
  intro P hP
  obtain ⟨Q, rfl⟩ := hP
  have h3 : (Nat.card N).factorization 3 ≤ (Nat.card X).factorization 3 := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hXpos]
    have h2 : Nat.card ↥((Q : Subgroup N).map N.subtype) ∣ Nat.card X :=
      Subgroup.card_subgroup_dvd_card _
    rwa [Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity Q] at h2
  have hcard : Nat.card ((Q : Subgroup N).map N.subtype) = 3 ^ (Nat.card X).factorization 3 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity Q,
      le_antisymm h3 h1]
  exact ⟨Or.inr (hcen (Sylow.ofCard _ hcard)), hrk (Sylow.ofCard _ hcard)⟩

end Abstract

section Split

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem Rall_le_centralizer_rep2 :
    Rall F ≤ Subgroup.centralizer ({(monoSp F).av (rep 2)} : Set ↥(SpI F)) := by
  have hb : ∀ b ∈ Bsub F, b ∈ Subgroup.centralizer ({(monoSp F).av (rep 2)} : Set ↥(SpI F)) := by
    rintro _ ⟨y, rfl⟩
    refine mem_centralizer_of_bd3 (a := ((y 0 : ↥(Tall F)) : GL (Fin 2) F).val)
      (b := ((y 1 : ↥(Tall F)) : GL (Fin 2) F).val) (c := ((y 2 : ↥(Tall F)) : GL (Fin 2) F).val)
      av_rep2 ?_ (tall_comm_C (y 0)) (tall_comm_C (y 1)) (tall_comm_C (y 2))
    show bd (fun j => (((y j : ↥(Tall F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) = bd3 _ _ _
    unfold bd3
    congr 1
    funext j
    fin_cases j <;> rfl
  have hs : (monoSp F).s ∈ Subgroup.centralizer ({(monoSp F).av (rep 2)} : Set ↥(SpI F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply Subtype.ext
    apply Units.ext
    show ((((monoSp F).av (rep 2) : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F) *
        ((((monoSp F).s : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F) =
      ((((monoSp F).s : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F) *
        ((((monoSp F).av (rep 2) : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F)
    have hd : bd3 (tm F 0 1) (tm F 0 1) (tm F 0 1) = bd (fun _ => tm F 0 1) := by
      unfold bd3
      congr 1
      funext j
      fin_cases j <;> rfl
    have hsm : ((((monoSp F).s : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F) = bc F sMat := rfl
    rw [av_rep2, hd, hsm]
    exact (bc_sMat_mul_bd (fun _ => tm F 0 1)).symm
  rintro _ ⟨b, hbB, k, rfl⟩
  exact Subgroup.mul_mem _ (hb b hbB) (Subgroup.pow_mem _ hs k)

theorem sylowAt_rep2 : SylowAt ((monoSp F).av (rep 2)) := by
  obtain ⟨P, hP⟩ := exists_sylow_le_Rall F
  exact ⟨P, hP.trans Rall_le_centralizer_rep2⟩

theorem isCyclic_center_sylow (hN : Nat.card F % 3 = 1) {X : Type} [Group X] [Finite X]
    (ε : X ≃* CFSG.Open.StatedSp 3 F) (P : Sylow 3 X) :
    IsCyclic ↥(Subgroup.center ↥(P : Subgroup X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := K421RProof.sylow_statedSp hN (P.mapSurjective (f := ε.toMonoidHom) ε.surjective)
  have hk : 1 ≤ padicValNat 3 (Nat.card F - 1) := by
    have hpos : 1 < Nat.card F := Finite.one_lt_card
    exact one_le_padicValNat_of_dvd (by omega) (by omega)
  exact K421SpWrProof.isCyclic_center_of_mulEquiv
    ((Subgroup.equivMapOfInjective (P : Subgroup X) ε.toMonoidHom ε.injective).trans φ)
    (K421SpWrProof.isCyclic_center_wreath_zmod hk)

theorem three_le_pRank_sylow (hN : Nat.card F % 3 = 1) {X : Type} [Group X] [Finite X]
    (ε : X ≃* CFSG.Open.StatedSp 3 F) (P : Sylow 3 X) :
    3 ≤ CFSG.Open.pRank 3 (P : Subgroup X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := K421RProof.sylow_statedSp hN (P.mapSurjective (f := ε.toMonoidHom) ε.surjective)
  have hk : 1 ≤ padicValNat 3 (Nat.card F - 1) := by
    have hpos : 1 < Nat.card F := Finite.one_lt_card
    exact one_le_padicValNat_of_dvd (by omega) (by omega)
  exact K421SpWrProof.three_le_pRank_of_mulEquiv_wreath_zmod hk
    ((Subgroup.equivMapOfInjective (P : Subgroup X) ε.toMonoidHom ε.injective).trans φ)

theorem sylowShape_of_type_two (hN : Nat.card F % 3 = 1) {X : Type} [Group X] [Finite X]
    (ε : X ≃* ↥(SpI F)) {x : X} (hty : IsType (monoSp F) (ε x) 2) :
    SylowShape1517 (Subgroup.zpowers x) := by
  obtain ⟨n, hn⟩ := hty
  have h1 : SylowAt (ε x) := SylowAt.conj hn sylowAt_rep2
  have h2 : SylowAt x := SylowAt.of_equiv ε h1
  exact sylowShape_of_sylow_le_centralizer (isCyclic_center_sylow hN (ε.trans (spIEquiv F)))
    (three_le_pRank_sylow hN (ε.trans (spIEquiv F))) h2

end Split

end K421SpSylProof

end CFSG.LocalAnalysis.RankThreeUC.S15
