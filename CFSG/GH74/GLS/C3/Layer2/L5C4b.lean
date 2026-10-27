module

public import CFSG.GH74.GLS.C3.Layer2.L5C4a
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import CFSG.GH74.GLS.C3.Layer2.L5C4a
public import CFSG.GH74.GLS.C3.Layer2.L5C4bInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C4bInputs
public import Certificates.Certificate5051
public import Certificates.Certificate5062
public import Certificates.Certificate5063

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Rec1

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def modelExt (H : Subgroup (Perm (Fin 16))) (HL : List (Perm (Fin 16)))
    (hH : ∀ p, p ∈ H ↔ p ∈ HL) (Tr : Fin 16 → Perm (Fin 16)) (τ : Fin 8 → Perm (Fin 16))
    (cc : Fin 8 → Fin 8 → Fin 16) (hTrMem : ∀ v, Tr v ∈ HL) (hτMem : ∀ k, τ k ∈ HL)
    (hTrXor : ∀ u v, Tr (xor16 u v) = Tr u * Tr v) (hτ0 : τ 0 = 1)
    (hConj : ∀ j w, τ j * Tr w = Tr (Dg j w) * τ j)
    (hMul : ∀ j k, τ j * τ k = Tr (cc j k) * τ (mulIdx j k))
    (hDec : ∀ p ∈ HL, ∃ (v : Fin 16) (k : Fin 8), p = Tr v * τ k)
    (hUniq : ∀ (v : Fin 16) (k : Fin 8) (v' : Fin 16) (k' : Fin 8),
      Tr v * τ k = Tr v' * τ k' → v = v' ∧ k = k') : ExtDat ↥H where
  tr v := ⟨Tr v, (hH _).2 (hTrMem v)⟩
  sec k := ⟨τ k, (hH _).2 (hτMem k)⟩
  coc := cc
  tr_xor u v := Subtype.ext (hTrXor u v)
  sec_zero := Subtype.ext hτ0
  conj j w := Subtype.ext (hConj j w)
  sec_mul j k := Subtype.ext (hMul j k)
  decomp g := by
    obtain ⟨v, k, hvk⟩ := hDec g.1 ((hH _).1 g.2)
    exact ⟨v, k, Subtype.ext hvk⟩
  uniq v k v' k' h := hUniq v k v' k' (congrArg Subtype.val h)

theorem sh0_trMem_chk :
    (List.finRange 16).all (fun v => decide (tr16 v ∈ Sh0L)) = true :=
  Certificates.certificate5063.1

theorem sh0_trMem (v : Fin 16) : tr16 v ∈ Sh0L := by
  have h := sh0_trMem_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h v trivial

theorem sh0_secMem_chk :
    (List.finRange 8).all (fun k => decide (Dg k ∈ Sh0L)) = true :=
  Certificates.certificate5063.2.1

theorem sh0_secMem (k : Fin 8) : Dg k ∈ Sh0L := by
  have h := sh0_secMem_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h k trivial

theorem tr16_xor_chk :
    (List.finRange 16).all (fun u => (List.finRange 16).all fun v =>
    decide (tr16 (xor16 u v) = tr16 u * tr16 v)) = true :=
  Certificates.certificate5063.2.2.1

theorem tr16_xor
    (u v : Fin 16) : tr16 (xor16 u v) = tr16 u * tr16 v := by
  have h := tr16_xor_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h u trivial v trivial

theorem tr16_zero : tr16 0 = 1 :=
  Certificates.certificate5063.2.2.2.1

theorem sh0_dec_chk :
    Sh0L.all (fun p => (List.finRange 16).any fun v => (List.finRange 8).any fun k =>
    decide (p = tr16 v * Dg k)) = true :=
  Certificates.certificate5063.2.2.2.2.1

theorem sh0_dec :
    ∀ p ∈ Sh0L, ∃ (v : Fin 16) (k : Fin 8), p = tr16 v * Dg k := by
  have h := sh0_dec_chk
  simp only [List.all_eq_true, List.any_eq_true, List.mem_finRange, decide_eq_true_eq,
    true_and] at h
  exact h

theorem sh0_uniq_chk :
    (List.finRange 16).all (fun v => (List.finRange 8).all fun k =>
    (List.finRange 16).all fun v' => (List.finRange 8).all fun k' =>
      imp (decide (tr16 v * Dg k = tr16 v' * Dg k')) (decide (v = v' ∧ k = k'))) = true :=
  Certificates.certificate5063.2.2.2.2.2.1

theorem sh0_uniq (v : Fin 16) (k : Fin 8) (v' : Fin 16) (k' : Fin 8)
    (h : tr16 v * Dg k = tr16 v' * Dg k') : v = v' ∧ k = k' := by
  have h1 := sh0_uniq_chk
  simp only [List.all_eq_true, List.mem_finRange, imp_eq_true, decide_eq_true_eq] at h1
  exact h1 v trivial k trivial v' trivial k' trivial h

@[expose] def ext0 :
    ExtDat ↥Sh0 :=
  modelExt Sh0 Sh0L (fun _ => Iff.rfl) tr16 Dg (fun _ _ => 0) sh0_trMem sh0_secMem tr16_xor
    Dg_zero Dg_tr16
    (fun j k => by rw [tr16_zero, one_mul, Dg_mul]) sh0_dec sh0_uniq

theorem ext0_tr
    (v : Fin 16) : ((ext0.tr v : ↥Sh0) : Perm (Fin 16)) = tr16 v := rfl

theorem ext0_sec
    (k : Fin 8) : ((ext0.sec k : ↥Sh0) : Perm (Fin 16)) = Dg k := rfl

theorem ext0_coc
    (j k : Fin 8) : ext0.coc j k = 0 := rfl

theorem sh0_yHat :
    ((ext0.tr 0 * ext0.sec 1 : ↥Sh0) : Perm (Fin 16)) = yHat := by
  rw [Subgroup.coe_mul, ext0_tr, ext0_sec, tr16_zero, one_mul, Dg_one]

theorem sh1_L_chk :
    ((List.finRange 16).all (fun v => decide (tr1 v ∈ Sh1L)) &&
    (List.finRange 8).all (fun k => decide (tau1 k ∈ Sh1L)) &&
    Sh1L.all (fun p => (List.finRange 16).any fun v => (List.finRange 8).any fun k =>
      decide (p = tr1 v * tau1 k))) = true :=
  Certificates.certificate5063.2.2.2.2.2.2.1

theorem sh1_trMem (v : Fin 16) : tr1 v ∈ Sh1L := by
  have h := sh1_L_chk
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h.1.1 v trivial

theorem sh1_secMem (k : Fin 8) : tau1 k ∈ Sh1L := by
  have h := sh1_L_chk
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h.1.2 k trivial

theorem sh1_dec :
    ∀ p ∈ Sh1L, ∃ (v : Fin 16) (k : Fin 8), p = tr1 v * tau1 k := by
  have h := sh1_L_chk
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_finRange,
    decide_eq_true_eq, true_and] at h
  exact h.2

theorem tr1_xor_chk :
    (List.finRange 16).all (fun u => (List.finRange 16).all fun v =>
    decide (tr1 (xor16 u v) = tr1 u * tr1 v)) = true :=
  Certificates.certificate5063.2.2.2.2.2.2.2.1

theorem tr1_xor
    (u v : Fin 16) : tr1 (xor16 u v) = tr1 u * tr1 v := by
  have h := tr1_xor_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h u trivial v trivial

theorem tau1_zero : tau1 0 = 1 :=
  Certificates.certificate5063.2.2.2.2.2.2.2.2.1

theorem sh1_conj_chk :
    (List.finRange 8).all (fun j => (List.finRange 16).all fun w =>
    decide (tau1 j * tr1 w = tr1 (Dg j w) * tau1 j)) = true :=
  Certificates.certificate5063.2.2.2.2.2.2.2.2.2.1

theorem sh1_conj
    (j : Fin 8) (w : Fin 16) : tau1 j * tr1 w = tr1 (Dg j w) * tau1 j := by
  have h := sh1_conj_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h j trivial w trivial

theorem sh1_mul_chk :
    (List.finRange 8).all (fun j => (List.finRange 8).all fun k =>
    decide (tau1 j * tau1 k = tr1 (cc1 j k) * tau1 (mulIdx j k))) = true :=
  Certificates.certificate5063.2.2.2.2.2.2.2.2.2.2.1

theorem sh1_mul
    (j k : Fin 8) : tau1 j * tau1 k = tr1 (cc1 j k) * tau1 (mulIdx j k) := by
  have h := sh1_mul_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h j trivial k trivial

theorem sh1_uniq_chk :
    (List.finRange 16).all (fun v => (List.finRange 8).all fun k =>
    (List.finRange 16).all fun v' => (List.finRange 8).all fun k' =>
      imp (decide (tr1 v * tau1 k = tr1 v' * tau1 k')) (decide (v = v' ∧ k = k'))) = true :=
  Certificates.certificate5063.2.2.2.2.2.2.2.2.2.2.2.1

theorem sh1_uniq (v : Fin 16) (k : Fin 8) (v' : Fin 16) (k' : Fin 8)
    (h : tr1 v * tau1 k = tr1 v' * tau1 k') : v = v' ∧ k = k' := by
  have h1 := sh1_uniq_chk
  simp only [List.all_eq_true, List.mem_finRange, imp_eq_true, decide_eq_true_eq] at h1
  exact h1 v trivial k trivial v' trivial k' trivial h

@[expose] def ext1 : ExtDat ↥Sh1 :=
  modelExt Sh1 Sh1L (fun _ => Iff.rfl) tr1 tau1 cc1 sh1_trMem sh1_secMem tr1_xor tau1_zero
    sh1_conj sh1_mul sh1_dec sh1_uniq

theorem ext1_tr
    (v : Fin 16) : ((ext1.tr v : ↥Sh1) : Perm (Fin 16)) = tr1 v := rfl

theorem ext1_sec
    (k : Fin 8) : ((ext1.sec k : ↥Sh1) : Perm (Fin 16)) = tau1 k := rfl

theorem ext1_coc
    (j k : Fin 8) : ext1.coc j k = cc1 j k := rfl

theorem sh1_yHat1_chk :
    (List.finRange 16).any (fun v => decide (yHat1 = tr1 v * tau1 1)) = true :=
  Certificates.certificate5063.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem sh1_yHat1 :
    ∃ v : Fin 16, ((ext1.tr v * ext1.sec 1 : ↥Sh1) : Perm (Fin 16)) = yHat1 := by
  have h := sh1_yHat1_chk
  simp only [List.any_eq_true, List.mem_finRange, decide_eq_true_eq, true_and] at h
  obtain ⟨v, hv⟩ := h
  refine ⟨v, ?_⟩
  rw [Subgroup.coe_mul, ext1_tr, ext1_sec]
  exact hv.symm

theorem yHat1_sq : yHat1 * yHat1 = 1 :=
  Certificates.certificate5063.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem yHat_sq : yHat * yHat = 1 :=
  Certificates.certificate5063.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.GH74.GLS.C3.Layer2.L5.Rec1
