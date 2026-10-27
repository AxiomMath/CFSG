module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmega

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Data

variable {G : Type} [Group G] {S : Type} [Group S]

@[expose] def CTDataFor (D : UniversalRootDatum S) (G₀ : Subgroup G) : Prop :=
  ∃ φ : ∀ J, D.leviAmalgam J →* G, CFSG.LieType.CurtisTits.IsCompatible D.leviAmalgam φ ∧
    ⨆ J, (φ J).range = G₀

theorem exists_injective_of_ctDataFor {D : UniversalRootDatum S} {τ : StatedLieTag} {n p f : ℕ}
    (hCT : CFSG.LieType.CurtisTits.CurtisTitsConclusion.{0} D τ n p f) (hZ : center S = ⊥)
    {G₀ : Subgroup G} (hG₀ : G₀ ≠ ⊥) (h : CTDataFor D G₀) :
    ∃ ψ : S →* G, Function.Injective ψ ∧ ψ.range = G₀ ∧ LieModel G₀ τ n p f := by
  obtain ⟨φ, hφ, hgen⟩ := h
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => hgen ▸ le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, D.leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J) with hφ'
  have hcomp' : CFSG.LieType.CurtisTits.IsCompatible D.leviAmalgam φ' :=
    fun I J hIJ x y hxy => Subtype.ext (hφ I J hIJ x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hgen
    rw [← MonoidHom.range_comp]
    rfl
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    by_contra hc
    push Not at hc
    apply hG₀
    rw [← hgen, eq_bot_iff]
    refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val (hc J x))
  obtain ⟨-, -, hrec, -⟩ := hCT
  obtain ⟨ψ₀, -, hsurj, hker, -, hZ0, -, hLM⟩ := hrec G₀ φ' hcomp' hgen' hnt
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    have h1 := hker hz
    rw [hZ] at h1
    exact h1
  have hZbot : center G₀ = ⊥ := by rw [hZ0, hZ, Subgroup.map_bot]
  refine ⟨G₀.subtype.comp ψ₀, G₀.subtype_injective.comp hinj₀, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot) hLM

end Data

section Center

variable {K : Type} [Field K] [CharP K 2]

theorem q2Omega_center_spinGroup_quadPlus_eq_bot {n : ℕ} (hn : 3 ≤ n) :
    center (spinGroup (quadPlus n K)) = ⊥ := by
  obtain ⟨-, h1, h2⟩ := spinToStatedProj_quadPlus (n := n) (K := K) hn
  rw [← h2, h1]
  exact CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.comap_statedScalars_quadPlus_eq_bot hn
    CharTwo.two_eq_zero

theorem q2Omega_irreducible_one_one (hK : Nat.card K = 2) :
    ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; omega)
  have : Fintype K := Fintype.ofFinite K
  intro s
  have hs : s ^ 2 = s := by
    have h := FiniteField.pow_card s
    rwa [← Nat.card_eq_fintype_card, hK] at h
  rw [hs, one_mul, CharTwo.add_self_eq_zero, zero_add]
  exact one_ne_zero

end Center

section Global

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem nsGlobal_ne_bot {m : ℕ} (hK : Nat.card K = 2) (hm : 3 ≤ m)
    (e : L ≃* StatedSp (m + 1) K) : nsGlobal e ≠ ⊥ := by
  intro h
  have h1 : ((e.symm (nsElt (K := K) (0 : Fin (m + 1))) : L) : G) ∈ nsGlobal e :=
    le_nsGlobal hK hm e (e.symm _).2
  rw [h, Subgroup.mem_bot] at h1
  apply nsElt_ne_one (K := K) (0 : Fin (m + 1))
  apply e.symm.injective
  rw [map_one]
  exact Subtype.ext h1

@[expose] def NsOmegaCTData {n : ℕ} (e : L ≃* StatedSp (n + 1) K) : Sp2mKind → Prop
  | .omegaMinus => ∃ hn : 3 ≤ n + 1 + 1, CTDataFor (plusDatum (n + 1 + 1) K hn) (nsGlobal e)
  | .omegaPlus => ∃ (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0),
      CTDataFor (Twisted.minusDatum (n + 1 + 1) hirr) (nsGlobal e)
  | _ => False

theorem sp2mKindType_nsGlobal_of_nsOmegaCTData [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2) (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K) {κ : Sp2mKind}
    (h : NsOmegaCTData e κ) : Sp2mKindType (nsGlobal e) (n + 1) 1 (q2GlobalKind κ) := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have hne := nsGlobal_ne_bot hK hn e
  cases κ with
  | omegaMinus =>
    have hadm : StatedLieAdmissible .POmegaPlus (n + 1 + 1) 2 1 :=
      ⟨Nat.prime_two, le_rfl, by omega⟩
    obtain ⟨hn2, hD⟩ := h
    obtain ⟨-, -, -, hLM⟩ := exists_injective_of_ctDataFor
      (CFSG.LieType.CurtisTits.curtisTitsConclusion_spinPlus.{0} (F := K) hadm hK1 hn2)
      (q2Omega_center_spinGroup_quadPlus_eq_bot hn2) hne hD
    exact hLM
  | omegaPlus =>
    obtain ⟨b, c, hirr, hD⟩ := h
    have hadm : StatedLieAdmissible .POmegaMinus (n + 1 + 1) 2 1 :=
      ⟨Nat.prime_two, le_rfl, by omega⟩
    obtain ⟨-, -, -, hLM⟩ := exists_injective_of_ctDataFor
      (CFSG.LieType.CurtisTits.curtisTitsConclusion_spinMinus.{0} (F := K) hirr hadm hK1)
      (CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot (by omega) hirr) hne hD
    exact hLM
  | field => exact h.elim
  | swap => exact h.elim
  | linearEven => exact h.elim
  | unitaryEven => exact h.elim
  | linearOdd => exact h.elim
  | unitaryOdd => exact h.elim

end Global

@[expose] def SpTwoOmegaCTDataInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k κ) → NsOmegaCTData e κ

theorem spTwoOmegaKindInput_of_ctData {κ : Sp2mKind} (h : SpTwoOmegaCTDataInput κ) :
    SpTwoOmegaKindInput κ := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  exact sp2mKindType_nsGlobal_of_nsOmegaCTData hK (by omega) e
    (h G L hset n K hK hn e t ht hKt hroot)

end CFSG.SeitzReduction.SymplecticPilot
