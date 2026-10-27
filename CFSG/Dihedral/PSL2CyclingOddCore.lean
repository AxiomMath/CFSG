module

public import CFSG.Dihedral.NormalOddSubgroupModels
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import all CFSG.Dihedral.BlueprintDefs
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public noncomputable section

namespace CFSG.DihedralBlueprint

open GorensteinWalter
open scoped MatrixGroups Pointwise

@[expose] def dihedralReflectionParity (n : ℕ) :
    DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun
    | .r _ => 1
    | .sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (a | a) (b | b) <;> simp only [DihedralGroup.r_mul_r,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    · rfl
    · exact (one_mul _).symm
    · exact (mul_one _).symm
    · change Multiplicative.ofAdd (0 : ZMod 2) = Multiplicative.ofAdd (1 + 1)
      decide

theorem no_fourgroup_le_odd {G : Type} [Group G] [Finite G]
    (V H : Subgroup G) (hV : IsKleinFour V) (hVH : V ≤ H)
    (hodd : Odd (Nat.card H)) : False := by
  have h := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hVH)
  rw [hV.card_four] at h
  norm_num at h

theorem no_cycles_of_dihedral_model {G : Type} [Group G] [Finite G]
    (H V : Subgroup G) (hV : IsKleinFour V) (hVH : V ≤ H)
    (hc : Cycles H V) {n : ℕ} (hn : n ≠ 0) (e : H ≃* DihedralGroup n) : False := by
  let : NeZero n := ⟨hn⟩
  let f : H →* Multiplicative (ZMod 2) := (dihedralReflectionParity n).comp e.toMonoidHom
  have hker := cycles_le_ker_of_commutative_quotient H V hV hVH hc f
  let R : Subgroup (DihedralGroup n) := Subgroup.zpowers (DihedralGroup.r 1)
  have hrot (v : V) : e (⟨v, hVH v.property⟩ : H) ∈ R := by
    have hfv : f (⟨v, hVH v.property⟩ : H) = 1 := by
      obtain ⟨w, hw, hweq⟩ := Subgroup.mem_map.mp (hker v.property)
      have heq : w = (⟨v, hVH v.property⟩ : H) := Subtype.ext hweq
      exact heq ▸ hw
    rcases dihedralGroup_cases (e (⟨v, hVH v.property⟩ : H)) with ⟨i, hi⟩ | ⟨i, hi⟩
    · rw [hi]
      exact r_mem_zpowers_r_one i
    · change dihedralReflectionParity n (e (⟨v, hVH v.property⟩ : H)) = 1 at hfv
      rw [hi] at hfv
      change Multiplicative.ofAdd (1 : ZMod 2) = Multiplicative.ofAdd 0 at hfv
      exact (by decide : Multiplicative.ofAdd (1 : ZMod 2) ≠ Multiplicative.ofAdd 0) hfv |>.elim
  let i : V →* DihedralGroup n := e.toMonoidHom.comp (Subgroup.inclusion hVH)
  let q : V →* R := i.codRestrict R hrot
  have hq : Function.Injective q := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : H => (z : G)) (e.injective (congrArg Subtype.val hab))
  let : IsCyclic R := inferInstance
  let : IsKleinFour V := hV
  exact IsKleinFour.not_isCyclic (isCyclic_of_injective q hq)

theorem psl2_cycling_local_models (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (H V : Subgroup (PSL2 K))
    (hV : IsKleinFour V) (hVH : V ≤ H) (hc : Cycles H V) :
    Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 5)) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F),
        IsOddPrimePower (Nat.card F) ∧ Nonempty (H ≃* PSL2 F)) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F),
        IsOddPrimePower (Nat.card F) ∧ Nonempty (H ≃* PGL2 F)) := by
  obtain ⟨r, f, hr, hrodd, hf, hcard⟩ := hK
  let : Fact r.Prime := ⟨hr⟩
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := r) (f := f) hcard H with
    helem | hcyclic | hdihedral | hA4 | hS4 | hA5 | hsemi | hPSL | hPGL
  · have hHp : IsPGroup r H := IsElementaryAbelian.isPGroup r H
    obtain ⟨m, hm⟩ := hHp.exists_card_eq
    exact (no_fourgroup_le_odd V H hV hVH (hm ▸ hrodd.pow)).elim
  · obtain ⟨_, _, _, hHcyclic⟩ := hcyclic
    let : IsCyclic H := hHcyclic
    let : IsKleinFour V := hV
    exact (IsKleinFour.not_isCyclic (Subgroup.isCyclic_of_le hVH)).elim
  · obtain ⟨n, _, hHcard, ⟨e⟩⟩ := hdihedral
    have hn : n ≠ 0 := by
      intro hzero
      have hpos := Nat.card_pos (α := H)
      rw [hHcard, hzero] at hpos
      omega
    exact (no_cycles_of_dihedral_model H V hV hVH hc hn e).elim
  · exact Or.inl hA4.2
  · exact Or.inr (Or.inl hS4.2)
  · exact Or.inr (Or.inr (Or.inl hA5.2))
  · obtain ⟨m, t, _, _, N, C, hNnormal, hNelem, hNcard, hCcyclic,
        _, hdisjoint, hjoin⟩ := hsemi
    let : N.Normal := hNnormal
    have hcomp : N.IsComplement' C := by
      refine ⟨Subgroup.mul_injective_of_disjoint hdisjoint, ?_⟩
      intro g
      have hg : (g : H) ∈ (N : Set H) * (C : Set H) := by
        rw [← Subgroup.normal_mul N C, hjoin]
        trivial
      obtain ⟨n, hn, c, hcC, hnc⟩ := hg
      exact ⟨⟨⟨n, hn⟩, ⟨c, hcC⟩⟩, hnc⟩
    let eQ : H ⧸ N ≃* C := hcomp.symm.QuotientMulEquiv
    let : IsCyclic (H ⧸ N) := eQ.isCyclic.mpr hCcyclic
    let : IsMulCommutative (H ⧸ N) := IsCyclic.isMulCommutative
    have hVN := cycles_le_ker_of_commutative_quotient H V hV hVH hc (QuotientGroup.mk' N)
    rw [QuotientGroup.ker_mk'] at hVN
    have hoddN : Odd (Nat.card (N.map H.subtype)) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective, hNcard]
      exact hrodd.pow
    exact (no_fourgroup_le_odd V (N.map H.subtype) hV hVN hoddN).elim
  · obtain ⟨m, hm, _, he⟩ := hPSL
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨GaloisField r m, inferInstance, inferInstance,
      ⟨r, m, hr, hrodd, by omega, GaloisField.card r m hm⟩, he⟩)))
  · obtain ⟨m, hm, _, he⟩ := hPGL
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨GaloisField r m, inferInstance, inferInstance,
      ⟨r, m, hr, hrodd, by omega, GaloisField.card r m hm⟩, he⟩)))

theorem psl2_cycling_oddCore_eq_bot (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (H V : Subgroup (PSL2 K))
    (hV : IsKleinFour V) (hVH : V ≤ H) (hc : Cycles H V) :
    Assembly.oddCore H = ⊥ := by
  have hodd : Odd (Nat.card (Assembly.oddCore H)) :=
    DisconnectedInvolutionGraph.Helpers.oddCore_odd
  rcases psl2_cycling_local_models K hK H V hV hVH hc with hA4 | hS4 | hA5 | hPSL | hPGL
  · exact normal_odd_eq_bot_of_aFour_model hA4 _ inferInstance hodd
  · exact normal_odd_eq_bot_of_sFour_model hS4 _ inferInstance hodd
  · exact normal_odd_eq_bot_of_alternating_model (by decide : 5 ≤ 5) hA5 _ inferInstance hodd
  · obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hPSL
    let : Field F := hfield
    let : Finite F := hfinite
    exact normal_odd_eq_bot_of_psl2_model F hF e _ inferInstance hodd
  · obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hPGL
    let : Field F := hfield
    let : Finite F := hfinite
    exact normal_odd_eq_bot_of_pgl2_model F hF e _ inferInstance hodd

theorem psl2_cycling_oddCoreOf_eq_bot (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (H V : Subgroup (PSL2 K))
    (hV : IsKleinFour V) (hVH : V ≤ H) (hc : Cycles H V) : oddCoreOf H = ⊥ := by
  rw [oddCoreOf, psl2_cycling_oddCore_eq_bot K hK H V hV hVH hc, Subgroup.map_bot]

end CFSG.DihedralBlueprint
