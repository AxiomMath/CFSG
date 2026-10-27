module

public import CFSG.Quasithin.Vol2.KGNatSL2
public import CFSG.ClassicalGroups.Symplectic.Sp4LagrangianParabolic

public section

namespace CFSG.ClassicalGroups

open CFSG.Open
open CFSG.Quasithin.Vol2.KGNat
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem exists_orderOf_eq_card_sub_one_mem_normalizer_sylow_sl2
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (U : Sylow 2 (StatedSL 2 K)) :
    ∃ d ∈ Subgroup.normalizer ((U : Subgroup (StatedSL 2 K)) : Set (StatedSL 2 K)),
      orderOf d = Nat.card K - 1 := by
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K
  let U' : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) K) :=
    U.mapSurjective (f := e.symm.toMonoidHom) (by simpa using e.symm.surjective)
  have hU' : (U' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) =
      (U : Subgroup (StatedSL 2 K)).map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.symm.toMonoidHom) (p := 2)
      (hf := by simpa using e.symm.surjective) U
  obtain ⟨g, hg⟩ := exists_conj_utri_eq_of_index (F := K) U'.2 U'.not_dvd_index
  obtain ⟨-, d, hd, hord⟩ := normalizer_conj_utri (F := K) g
  have hdU' : d ∈ Subgroup.normalizer ((U' : Subgroup
      (Matrix.SpecialLinearGroup (Fin 2) K)) : Set (Matrix.SpecialLinearGroup (Fin 2) K)) := by
    rwa [hg] at hd
  have hmap := Subgroup.map_equiv_normalizer_eq
    (U : Subgroup (StatedSL 2 K)) e.symm
  have hdmap : d ∈ (Subgroup.normalizer
      ((U : Subgroup (StatedSL 2 K)) : Set (StatedSL 2 K))).map e.symm.toMonoidHom := by
    rw [hmap]
    exact hdU'
  obtain ⟨d₀, hd₀, hd₀d⟩ := Subgroup.mem_map.mp hdmap
  refine ⟨d₀, hd₀, ?_⟩
  calc
    orderOf d₀ = orderOf (e.symm d₀) := (MulEquiv.orderOf_eq e.symm d₀).symm
    _ = orderOf d := by rw [show e.symm d₀ = d from hd₀d]
    _ = Nat.card K - 1 := hord

theorem exists_orderOf_eq_card_sub_one_mem_normalizer_sylow_sp4
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (U : Sylow 2 (StatedSp 2 K)) :
    ∃ d ∈ Subgroup.normalizer ((U : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K)),
      orderOf d = Nat.card K - 1 := by
  classical
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := K) 2 2
  obtain ⟨β, hβ⟩ := IsCyclic.exists_generator (α := Kˣ)
  let d₀ : StatedSp 2 K :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torusHom (r := 2) (k := K)
      (Pi.mulSingle (0 : Fin 2) β)
  have hd₀n : d₀ ∈ Subgroup.normalizer
      (unipotent 2 K : Set (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.Sp4.torusHom_mem_normalizer_unipotent _
  have hd₀ord : orderOf d₀ = Nat.card K - 1 := by
    dsimp [d₀]
    rw [CFSG.ClassicalGroups.Symplectic.Sp4.orderOf_torusHom_mulSingle,
      orderOf_eq_card_of_forall_mem_zpowers hβ, Nat.card_units]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp 2 K) P U
  have hPmap : (unipotent 2 K).map (MulAut.conj g).toMonoidHom =
      (U : Subgroup (StatedSp 2 K)) := by
    have h := congrArg (fun S : Sylow 2 (StatedSp 2 K) =>
      (S : Subgroup (StatedSp 2 K))) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hP] at h
    exact h
  let d : StatedSp 2 K := (MulAut.conj g) d₀
  refine ⟨d, ?_, ?_⟩
  · have hd : d ∈ (Subgroup.normalizer
        (unipotent 2 K : Set (StatedSp 2 K))).map (MulAut.conj g).toMonoidHom := by
      exact Subgroup.mem_map.mpr ⟨d₀, hd₀n, rfl⟩
    rw [Subgroup.map_equiv_normalizer_eq, hPmap] at hd
    exact hd
  · dsimp [d]
    calc
      orderOf ((MulAut.conj g) d₀) = orderOf d₀ :=
        MulEquiv.orderOf_eq (MulAut.conj g) d₀
      _ = Nat.card K - 1 := hd₀ord

end CFSG.ClassicalGroups
