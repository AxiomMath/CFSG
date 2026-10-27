module

public import Certificates.Certificate17351
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Three

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Open CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
  CFSG.RankThree.PartOne CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Sporadic.Co2Cert
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T
  CFSG.HardMathSupport.Dickson.I271.Co2Cent CFSG.HardMathSupport.Dickson.I271.U42Presentation
open scoped commutatorElement

@[expose] def finBase2300 (a : Array ℕ) : List (Fin 2300) :=
  a.toList.map fun v => ⟨v % 2300, Nat.mod_lt _ (by norm_num)⟩

theorem finBase2300_map_eq (a : Array ℕ) (h : ∀ v ∈ a.toList, v < 2300) :
    ((finBase2300 a).map Fin.val).toArray = a := by
  unfold finBase2300
  rw [List.map_map]
  have : (Fin.val ∘ fun v : ℕ => (⟨v % 2300, Nat.mod_lt _ (by norm_num)⟩ : Fin 2300)) =
      fun v => v % 2300 := rfl
  rw [this]
  have h2 : a.toList.map (fun v => v % 2300) = a.toList :=
    (List.map_congr_left fun v hv => Nat.mod_eq_of_lt (h v hv)).trans (List.map_id _)
  rw [h2]

section Perm

theorem co2XA_eq : co2XA = φ (Multiplicative.ofAdd (vec 3)) :=
  CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_dElts (by norm_num))

theorem co2XB_eq : co2XB = φ (Multiplicative.ofAdd (vec 1)) :=
  CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_dElts (by norm_num))

theorem rep_XB : Rep 2300 (dElts ())[1]! co2XB := by
  rw [co2XB_eq]
  exact rep_dElts (by norm_num)

theorem fusion_spec {k : ℕ} (hk1 : k ≠ 0) (hk : k < 81) :
    ∃ h ∈ co2P, ∃ c : Equiv.Perm (Fin 2300), (c = co2XA ∨ c = co2XB) ∧ ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
      h * φ (Multiplicative.ofAdd (vec k)) * h⁻¹ = c ^ e := by
  rw [φ_vec_eq hk]
  exact Certificates.certificate17351.1 k (Nat.pos_of_ne_zero hk1) hk

theorem co2_fuse_d5 : ∃ h ∈ co2P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
    h * φ (Multiplicative.ofAdd (vec 5)) * h⁻¹ = co2XA ^ e := by
  rw [φ_vec_eq (by norm_num)]
  exact Certificates.certificate17351.2.1

theorem co2_fuse_d4 : ∃ h ∈ co2P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
    h * φ (Multiplicative.ofAdd (vec 4)) * h⁻¹ = co2XB ^ e := by
  rw [φ_vec_eq (by norm_num)]
  exact Certificates.certificate17351.2.2.1

theorem co2_exists_conj_classes {s : Equiv.Perm (Fin 2300)} (hs : s ∈ co2P) (hs3 : orderOf s = 3) :
    ∃ k ∈ co2P, ∃ c : Equiv.Perm (Fin 2300), (c = co2XA ∨ c = co2XB) ∧ ∃ e : ℕ,
      (e = 1 ∨ e = 2) ∧ k * c ^ e * k⁻¹ = s := by
  obtain ⟨h, hh, hD⟩ := exists_conj_mem_Dg hs hs3
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hD
  have hhinv : h⁻¹ ∈ co2P := co2P.inv_mem hh
  have hk : idx a.toAdd < 81 := idx_lt _
  have hvec : φ (Multiplicative.ofAdd (vec (idx a.toAdd))) = h * s * h⁻¹ := by
    rw [vec_idx]
    exact ha
  have hk0 : idx a.toAdd ≠ 0 := by
    intro h0
    have ha0 : a.toAdd = 0 := (idx_eq_zero_iff _).1 h0
    have : a = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      exact ha0
    rw [this, map_one] at ha
    have hs1 : s = 1 := by
      have : h * s * h⁻¹ = 1 := ha.symm
      simpa using this
    rw [hs1, orderOf_one] at hs3
    omega
  obtain ⟨h', hh', c, hc, e, he, hfuse⟩ := fusion_spec hk0 hk
  rw [hvec] at hfuse
  have hh'inv : h'⁻¹ ∈ co2P := co2P.inv_mem hh'
  refine ⟨h⁻¹ * h'⁻¹, co2P.mul_mem hhinv hh'inv, c, hc, e, he, ?_⟩
  have hd : h'⁻¹ * c ^ e * h' = h * s * h⁻¹ := by
    rw [← hfuse]
    group
  calc h⁻¹ * h'⁻¹ * c ^ e * (h⁻¹ * h'⁻¹)⁻¹ = h⁻¹ * (h'⁻¹ * c ^ e * h') * h := by group
    _ = h⁻¹ * (h * s * h⁻¹) * h := by rw [hd]
    _ = s := by group

theorem co2CaseA_spec :
    co2XA ^ 3 = 1 ∧ co2XA ≠ 1 ∧ co2XA ∈ co2P ∧ Nat.card (closure (permsA 2300 (co2RGens ()))) = 243 ∧
      closure (permsA 2300 (co2RGens ())) ≤ centralizer {co2XA} ⊓ co2P ∧
      (∀ g ∈ centralizer {co2XA} ⊓ co2P, ∀ r ∈ closure (permsA 2300 (co2RGens ())),
        g * r * g⁻¹ ∈ closure (permsA 2300 (co2RGens ()))) ∧
      centralizer (closure (permsA 2300 (co2RGens ())) : Set (Equiv.Perm (Fin 2300))) ⊓
        (centralizer {co2XA} ⊓ co2P) ≤ closure (permsA 2300 (co2RGens ())) :=
  Certificates.certificate17351.2.2.2.1

theorem co2CaseB_spec :
    co2XB ^ 3 = 1 ∧ co2XB ≠ 1 ∧ co2XB ∈ co2P ∧ Nat.card Lsub = 25920 ∧
      Lsub ≤ centralizer {co2XB} ⊓ co2P ∧
      (∀ g ∈ centralizer {co2XB} ⊓ co2P, ∀ l ∈ Lsub, g * l * g⁻¹ ∈ Lsub) ∧
      (∀ g ∈ centralizer {co2XB} ⊓ co2P, (∀ l ∈ Lsub, l * g = g * l) → g ^ 3 = 1) ∧
      ∀ w ∈ u42Words,
        CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW uvGen w = 1 :=
  Certificates.certificate17351.2.2.2.2.1

theorem co2_mem_Lsub_of_sift {t : Array ℕ} {G : Equiv.Perm (Fin 2300)} (hG : Rep 2300 t G)
    (h : siftA 2300 (rawLevels 2300 (co2LArrs ()) co2LBase) co2LBase 0 t = true) : G ∈ Lsub :=
  Certificates.certificate17351.2.2.2.2.2 t G hG h

end Perm

end CFSG.HardMathSupport.Dickson.I271
