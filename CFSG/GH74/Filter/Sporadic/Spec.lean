module

public import CFSG.GH74.Filter.ElemAbelian
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3
public import Certificates.Data.CFSGNative.Filter.Sec2
import all CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3

public section

namespace CFSG.GH74.Filter

theorem units_of_section {R' : Type*} [Monoid R'] (S : Submonoid R') {r : ℕ} (T : R')
    (x : Fin r → R') (hTS : T ∈ S) (hxS : ∀ i, x i ∈ S) (hTT : T * T = 1)
    (hxT : ∀ i, x i * T = T * x i) (hsq : ∀ i, x i * x i = 1 ∨ x i * x i = T)
    (hcomm : ∀ i j, x i * x j = x j * x i ∨ x i * x j = T * (x j * x i))
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 →
      (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ 1 ∧
        (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ T) :
    ∃ (t : Sˣ) (u : Fin r → Sˣ), t ^ 2 = 1 ∧ (∀ i, u i * t = t * u i) ∧
      (∀ i, u i * u i = 1 ∨ u i * u i = t) ∧
      (∀ i j, u i * u j = u j * u i ∨ u i * u j = t * (u j * u i)) ∧
      ∀ a : Fin r → Fin 2, a ≠ 0 →
        (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1 ∧
          (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ t := by
  have hT2 : (⟨T, hTS⟩ : S) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hTT)
  have hx4 : ∀ i, (⟨x i, hxS i⟩ : S) ^ 4 = 1 := by
    intro i
    have : x i ^ 4 = 1 := by
      have e : x i ^ 4 = (x i * x i) * (x i * x i) := by simp [pow_succ, mul_assoc]
      rcases hsq i with h | h
      · rw [e, h, one_mul]
      · rw [e, h, hTT]
    exact Subtype.ext (by simpa using this)
  let t : Sˣ := Units.ofPowEqOne _ 2 hT2 (by norm_num)
  let u : Fin r → Sˣ := fun i => Units.ofPowEqOne _ 4 (hx4 i) (by norm_num)
  let f : Sˣ →* R' := S.subtype.comp (Units.coeHom S)
  have hft : f t = T := rfl
  have hfu : ∀ i, f (u i) = x i := fun i => rfl
  have hinj : ∀ a b : Sˣ, f a = f b → a = b := fun a b h => Units.ext (Subtype.ext h)
  refine ⟨t, u, ?_, ?_, ?_, ?_, ?_⟩
  · exact hinj _ _ (by rw [map_pow, hft, map_one, pow_two, hTT])
  · intro i
    exact hinj _ _ (by rw [map_mul, map_mul, hft, hfu]; exact hxT i)
  · intro i
    rcases hsq i with h | h
    · left
      exact hinj _ _ (by rw [map_mul, hfu, map_one]; exact h)
    · right
      exact hinj _ _ (by rw [map_mul, hfu, hft]; exact h)
  · intro i j
    rcases hcomm i j with h | h
    · left
      exact hinj _ _ (by rw [map_mul, map_mul, hfu, hfu]; exact h)
    · right
      exact hinj _ _ (by rw [map_mul, map_mul, map_mul, hft, hfu, hfu]; exact h)
  · intro a ha
    obtain ⟨h1, h2⟩ := hker a ha
    have hmap : f (List.ofFn fun i => u i ^ (a i : ℕ)).prod =
        (List.ofFn fun i => x i ^ (a i : ℕ)).prod := by
      rw [map_list_prod, List.map_ofFn]
      congr 1
    constructor
    · intro h
      apply h1
      rw [← hmap, h, map_one]
    · intro h
      apply h2
      rw [← hmap, h, hft]

end CFSG.GH74.Filter

namespace CFSG.SectionRank

open CFSG.Blueprint CFSG.GH74 CFSG.GH74.Filter CFSG.SectionRank.Native
open scoped Matrix

@[expose] def enc2 : (r : ℕ) → (Fin r → Fin 2) → ℕ
  | 0, _ => 0
  | r + 1, a => (a 0 : ℕ) + 2 * enc2 r (Fin.tail a)

theorem enc2_lt : ∀ (r : ℕ) (a : Fin r → Fin 2), enc2 r a < 2 ^ r
  | 0, _ => by simp [enc2]
  | r + 1, a => by
    have := enc2_lt r (Fin.tail a)
    have := (a 0).isLt
    rw [enc2, pow_succ]
    omega

theorem eq_zero_of_enc2_eq_zero : ∀ (r : ℕ) (a : Fin r → Fin 2), enc2 r a = 0 → a = 0
  | 0, a, _ => funext fun i => i.elim0
  | r + 1, a, h => by
    rw [enc2] at h
    have h0 : (a 0 : ℕ) = 0 := by omega
    have ht := eq_zero_of_enc2_eq_zero r (Fin.tail a) (by omega)
    funext i
    refine Fin.cases (Fin.ext h0) (fun j => ?_) i
    exact congrFun ht j

namespace OpsSpec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem appBase2_spec : ∀ (xs : List M), (∀ X ∈ xs, Sp.WF X) →
    ∀ (a : Fin xs.length → Fin 2) {v : V}, Sp.VWF v →
      Sp.VWF (O.appBase 2 xs (enc2 _ a) v) ∧ Sp.toVec (O.appBase 2 xs (enc2 _ a) v) =
        Sp.toVec v ᵥ* (List.ofFn fun i => Sp.toMat xs[i] ^ (a i : ℕ)).prod
  | [], _, a, v, hv => ⟨hv, by simp [Ops.appBase]⟩
  | X :: xs, hxs, a, v, hv => by
    have hX := hxs X List.mem_cons_self
    have h0 := (a 0).isLt
    have hd : (enc2 (xs.length + 1) a) % 2 = (a 0 : ℕ) := by rw [enc2]; omega
    have hq : (enc2 (xs.length + 1) a) / 2 = enc2 xs.length (Fin.tail a) := by rw [enc2]; omega
    obtain ⟨w1, f1⟩ := Sp.app_spec hX (a 0 : ℕ) hv
    obtain ⟨w2, f2⟩ := appBase2_spec xs (fun Y hY => hxs Y (List.mem_cons_of_mem _ hY))
      (Fin.tail a) w1
    change Sp.VWF (O.appBase 2 xs (enc2 (xs.length + 1) a / 2)
        (O.app X (enc2 (xs.length + 1) a % 2) v)) ∧
      Sp.toVec (O.appBase 2 xs (enc2 (xs.length + 1) a / 2)
        (O.app X (enc2 (xs.length + 1) a % 2) v)) = _
    rw [hd, hq, List.ofFn_succ, List.prod_cons]
    refine ⟨w2, ?_⟩
    rw [f2, f1, Matrix.vecMul_vecMul]
    rfl

theorem ne_of_kerModOK {T : M} (hT : Sp.WF T) {xs : List M} (hxs : ∀ X ∈ xs, Sp.WF X)
    {tests : List ℕ} (h : O.kerModOK T xs tests = true) (a : Fin xs.length → Fin 2)
    (ha : a ≠ 0) :
    (List.ofFn fun i => Sp.toMat xs[i] ^ (a i : ℕ)).prod ≠ 1 ∧
      (List.ofFn fun i => Sp.toMat xs[i] ^ (a i : ℕ)).prod ≠ Sp.toMat T := by
  have hlt := enc2_lt _ a
  have hpos : enc2 _ a ≠ 0 := fun h0 => ha (eq_zero_of_enc2_eq_zero _ a h0)
  unfold Ops.kerModOK at h
  rw [List.all_eq_true] at h
  have h1 := h (enc2 _ a - 1) (List.mem_range.2 (by omega))
  rw [show enc2 _ a - 1 + 1 = enc2 _ a by omega] at h1
  unfold Ops.outsideN at h1
  rw [Bool.and_eq_true] at h1
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨k, -, hk⟩ := List.any_eq_true.1 h1a
  obtain ⟨k', -, hk'⟩ := List.any_eq_true.1 h1b
  constructor
  · intro hone
    apply Sp.toVec_ne hk
    rw [(Sp.appBase2_spec xs hxs a (Sp.unit_wf k)).2, hone, Matrix.vecMul_one]
  · intro hT'
    apply Sp.toVec_ne hk'
    rw [(Sp.appBase2_spec xs hxs a (Sp.unit_wf k')).2, hT', Sp.toVec_vmul (Sp.unit_wf k') hT]

theorem pairwise_of_commsModOK {T : M} (hT : Sp.WF T) : ∀ {xs : List M},
    (∀ X ∈ xs, Sp.WF X) → O.commsModOK T xs = true →
    xs.Pairwise fun X Y => Sp.toMat X * Sp.toMat Y = Sp.toMat Y * Sp.toMat X ∨
      Sp.toMat X * Sp.toMat Y = Sp.toMat T * (Sp.toMat Y * Sp.toMat X)
  | [], _, _ => List.Pairwise.nil
  | X :: xs, hxs, h => by
    rw [Ops.commsModOK, Bool.and_eq_true, List.all_eq_true] at h
    have hX := hxs X List.mem_cons_self
    refine List.pairwise_cons.2 ⟨fun Y hY => ?_,
      pairwise_of_commsModOK hT (fun Z hZ => hxs Z (List.mem_cons_of_mem _ hZ)) h.2⟩
    have hY' := hxs Y (List.mem_cons_of_mem _ hY)
    have hc := h.1 Y hY
    unfold Ops.commModOK at hc
    rw [Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · left
      have := Sp.toMat_eq (Sp.mul_wf hX hY') (Sp.mul_wf hY' hX) hc
      rwa [Sp.toMat_mul hX hY', Sp.toMat_mul hY' hX] at this
    · right
      have := Sp.toMat_eq (Sp.mul_wf hX hY') (Sp.mul_wf hT (Sp.mul_wf hY' hX)) hc
      rwa [Sp.toMat_mul hX hY', Sp.toMat_mul hT (Sp.mul_wf hY' hX), Sp.toMat_mul hY' hX] at this

section Regs

variable [Inhabited M] (S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p)))

theorem exists_of_secCheck (D : SecData)
    (hA : Sp.WF (O.decode D.seedA) ∧ Sp.toMat (O.decode D.seedA) ∈ S)
    (hB : Sp.WF (O.decode D.seedB) ∧ Sp.toMat (O.decode D.seedB) ∈ S)
    (h : O.secCheck D = true) :
    ∃ r : ℕ, r = D.outs.length ∧ ∃ (t : Sˣ) (x : Fin r → Sˣ), t ^ 2 = 1 ∧
      (∀ i, x i * t = t * x i) ∧ (∀ i, x i * x i = 1 ∨ x i * x i = t) ∧
      (∀ i j, x i * x j = x j * x i ∨ x i * x j = t * (x j * x i)) ∧
      ∀ a : Fin r → Fin 2, a ≠ 0 →
        (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ 1 ∧
          (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ t := by
  unfold Ops.secCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hn, hprog⟩, houts⟩, htreg⟩, hsec⟩ := h
  obtain ⟨hs0, hok0⟩ := Sp.initRegs_ok S hA hB D.nregs
  obtain ⟨hs, hok⟩ := Sp.run_ok S D.prog hok0 (by rw [hs0]; exact hprog)
  set R := O.run D.prog (O.initRegs (O.decode D.seedA) (O.decode D.seedB) D.nregs)
  rw [hs0] at hs
  set xs := D.outs.map fun r => R[r]! with hxsdef
  set T := R[D.tReg]! with hTdef
  have hTok : Sp.WF T ∧ Sp.toMat T ∈ S := hok D.tReg (by rw [hs]; exact htreg)
  have hxs : ∀ X ∈ xs, Sp.WF X ∧ Sp.toMat X ∈ S := by
    intro X hX
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hX
    exact hok r (by rw [hs]; exact of_decide_eq_true (List.all_eq_true.1 houts r hr))
  have hw : ∀ X ∈ xs, Sp.WF X := fun X hX => (hxs X hX).1
  unfold Ops.secOK at hsec
  simp only [Bool.and_eq_true] at hsec
  obtain ⟨⟨⟨htt, hxT⟩, hcomm⟩, hker⟩ := hsec
  have hpair := Sp.pairwise_of_commsModOK hTok.1 hw hcomm
  have hTT : Sp.toMat T * Sp.toMat T = 1 := by
    have := Sp.toMat_eq (Sp.mul_wf hTok.1 hTok.1) Sp.one_wf htt
    rwa [Sp.toMat_mul hTok.1 hTok.1, Sp.toMat_one] at this
  have hxT' : ∀ X ∈ xs, Sp.toMat X * Sp.toMat T = Sp.toMat T * Sp.toMat X ∧
      (Sp.toMat X * Sp.toMat X = 1 ∨ Sp.toMat X * Sp.toMat X = Sp.toMat T) := by
    intro X hX
    have h1 := List.all_eq_true.1 hxT X hX
    rw [Bool.and_eq_true] at h1
    have wX := hw X hX
    refine ⟨?_, ?_⟩
    · have := Sp.toMat_eq (Sp.mul_wf wX hTok.1) (Sp.mul_wf hTok.1 wX) h1.1
      rwa [Sp.toMat_mul wX hTok.1, Sp.toMat_mul hTok.1 wX] at this
    · have h2 := h1.2
      unfold Ops.inN at h2
      rw [Bool.or_eq_true] at h2
      rcases h2 with h2 | h2
      · left
        have := Sp.toMat_eq (Sp.mul_wf wX wX) Sp.one_wf h2
        rwa [Sp.toMat_mul wX wX, Sp.toMat_one] at this
      · right
        have := Sp.toMat_eq (Sp.mul_wf wX wX) hTok.1 h2
        rwa [Sp.toMat_mul wX wX] at this
  refine ⟨xs.length, List.length_map _, ?_⟩
  refine units_of_section S (Sp.toMat T) (fun i : Fin xs.length => Sp.toMat xs[i]) hTok.2
    (fun i => (hxs _ (List.getElem_mem i.isLt)).2) hTT
    (fun i => (hxT' _ (List.getElem_mem i.isLt)).1)
    (fun i => (hxT' _ (List.getElem_mem i.isLt)).2) (fun i j => ?_)
    (fun a ha => Sp.ne_of_kerModOK hTok.1 hw hker a ha)
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact List.pairwise_iff_getElem.1 hpair i j i.isLt j.isLt hij
  · exact Or.inl rfl
  · rcases List.pairwise_iff_getElem.1 hpair j i j.isLt i.isLt hij with h | h
    · exact Or.inl h.symm
    · right
      have key : ∀ (A B : Matrix (Fin d) (Fin d) (ZMod p)),
          B * A = Sp.toMat T * (A * B) → A * B = Sp.toMat T * (B * A) := by
        intro A B hh
        rw [hh, ← mul_assoc, hTT, one_mul]
      exact key _ _ h

end Regs

theorem not_gen4_of_secCheck [NeZero p] [Inhabited M] (D : SecData)
    (h : O.secCheck D = true) (hr : 5 ≤ D.outs.length) :
    ¬ Gen4 (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  have hA : Sp.WF (O.decode D.seedA) ∧ Sp.toMat (O.decode D.seedA) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
  have hB : Sp.WF (O.decode D.seedB) ∧ Sp.toMat (O.decode D.seedB) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  obtain ⟨r, hrr, t, x, ht, hc, hsq, hcomm, hker⟩ := Sp.exists_of_secCheck S D hA hB h
  exact not_gen4_of_central_section_mul (by omega) t ht x hc hsq hcomm hker

end OpsSpec

end CFSG.SectionRank
