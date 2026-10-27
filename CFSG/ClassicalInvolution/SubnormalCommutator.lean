module

public import CFSG.ClassicalInvolution.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutatorElement_mem_of_mem_normalizer {U : Subgroup G} {u h : G} (hu : u ∈ U)
    (hh : h ∈ Subgroup.normalizer (U : Set G)) : ⁅u, h⁆ ∈ U := by
  rw [commutatorElement_def]
  have : h * u⁻¹ * h⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hh _).mp (U.inv_mem hu)
  simpa [mul_assoc] using U.mul_mem hu this

theorem commutator_le_commutator_commutator_of_coprime (W R : Subgroup G)
    (hRW : R ≤ Subgroup.normalizer (W : Set G)) (hcop : Nat.Coprime (Nat.card R) (Nat.card W)) :
    ⁅W, R⁆ ≤ ⁅⁅W, R⁆, R⁆ := by
  classical
  have : Subgroup.Normalizes R W := ⟨hRW⟩
  have h2 : CFSG.commutatorAction₂ (A := R) (G := W) = CFSG.commutatorAction (A := R) (G := W) :=
    CFSG.commutatorAction₂_eq_commutatorAction_of_coprime (G := W) (A := R) hcop
  have hmap : (CFSG.commutatorAction (A := R) (G := W)).map W.subtype = ⁅W, R⁆ := by
    simpa using CFSG.commutatorAction_subgroup_conj_map_eq_commutator W R hRW
  have hmap2 : (CFSG.commutatorAction₂ (A := R) (G := W)).map W.subtype ≤ ⁅⁅W, R⁆, R⁆ := by
    let C : Subgroup W := CFSG.commutatorAction (A := R) (G := W)
    let S : Set W := {x : W | ∃ a : R, ∃ h : W, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc (CFSG.commutatorAction₂ (A := R) (G := W)).map W.subtype =
          (Subgroup.closure S).map W.subtype := rfl
      _ = Subgroup.closure (W.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := W.subtype) S)
      _ ≤ ⁅⁅W, R⁆, R⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅W, R⁆, R⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : G) ∈ ⁅W, R⁆ := by
          rw [← hmap]
          exact Subgroup.mem_map_of_mem W.subtype hhC
        have hcomm : ⁅(h : G)⁻¹, (a : G)⁆ ∈ ⁅⁅W, R⁆, R⁆ :=
          Subgroup.commutator_mem_commutator ((⁅W, R⁆ : Subgroup G).inv_mem hhcomm) a.2
        simpa [commutatorElement_def, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hRW, mul_assoc] using hcomm
  intro x hx
  rw [← hmap, ← h2] at hx
  exact hmap2 hx

theorem commutator_zpowers_le_of_isSubnormal [Finite G] {H K U : Subgroup G} (hHK : IsSubnormal H K)
    (hUK : U ≤ K) (hKU : K ≤ Subgroup.normalizer (U : Set G)) (hU : IsPGroup 2 U) {g : G}
    (hgH : g ∈ H) (hg : Odd (orderOf g)) :
    ⁅U, Subgroup.zpowers g⁆ ≤ H ⊓ U := by
  induction hHK generalizing g with
  | refl H =>
    rw [Subgroup.commutator_le]
    intro u hu h hh
    have hhK : h ∈ H := (Subgroup.zpowers_le.mpr hgH) hh
    refine ⟨?_, commutatorElement_mem_of_mem_normalizer hu (hKU hhK)⟩
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hUK hu) hhK) (H.inv_mem (hUK hu))) (H.inv_mem hhK)
  | @step H M K hHM hHMn hMK ih =>
    have hgM : g ∈ M := hHM hgH
    have hMK' : M ≤ K := isSubnormal_le hMK
    have hzK : Subgroup.zpowers g ≤ Subgroup.normalizer (U : Set G) :=
      (Subgroup.zpowers_le.mpr (hKU (hMK' hgM)))
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers g)) (Nat.card U) := by
      obtain ⟨k, hk⟩ := hU.exists_card_eq
      rw [Nat.card_zpowers, hk]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hg)
    have hIH : ⁅U, Subgroup.zpowers g⁆ ≤ M ⊓ U := ih hUK hKU hgM hg
    refine (commutator_le_commutator_commutator_of_coprime U (Subgroup.zpowers g) hzK
      hcop).trans ((Subgroup.commutator_mono hIH le_rfl).trans ?_)
    rw [Subgroup.commutator_le]
    intro w hw h hh
    have hhH : h ∈ H := (Subgroup.zpowers_le.mpr hgH) hh
    refine ⟨?_, commutatorElement_mem_of_mem_normalizer hw.2 (hKU (hMK' (hHM hhH)))⟩
    have hconj : w * h * w⁻¹ ∈ H := by
      have hn := hHMn.conj_mem ⟨h, hHM hhH⟩ (by simpa [Subgroup.mem_subgroupOf] using hhH)
        ⟨w, hw.1⟩
      simpa [Subgroup.mem_subgroupOf] using hn
    rw [commutatorElement_def]
    exact H.mul_mem hconj (H.inv_mem hhH)

end CFSG.ClassicalInvolution
