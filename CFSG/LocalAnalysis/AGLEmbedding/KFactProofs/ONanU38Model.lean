module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Vec
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Weak

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open scoped Matrix

@[expose] noncomputable def sigSU : MulAut SU := suField hU sigma2Equiv

theorem coe_sigSU_pow (n : ℕ) (g : SU) :
    (((sigSU ^ n) g : SU) : GL (Fin 3) GF64).val =
      ((fun M : Matrix (Fin 3) (Fin 3) GF64 => M.map sigma2)^[n]) (g : GL (Fin 3) GF64).val := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]
    exact congrArg _ (coe_suField_sigma2 g)

@[expose] def validS (p : Pr3) : Bool := isSUArr p.1 && decide (p.2 < 3)

structure Model (X : Type*) [Group X] where
  ι : SU →* X
  x : X
  x_cube : x ^ 3 = 1
  x_conj : ∀ g : SU, x * ι g * x⁻¹ = ι (sigSU g)
  sc : List GF64
  sc_ker : ∀ s ∈ sc, ∃ z : SU, ((z : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) = s • 1 ∧
    ι z = 1
  inj : ∀ (g : SU) (j : ℕ), j < 3 → ι g * x ^ j = 1 →
    j = 0 ∧ ∃ s ∈ sc, ((g : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) = s • 1

namespace Model

variable {X : Type*} [Group X] (M : Model X)

theorem x_pow_conj (n : ℕ) (g : SU) : M.x ^ n * M.ι g * (M.x ^ n)⁻¹ = M.ι ((sigSU ^ n) g) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    have h1 : M.x ^ (n + 1) * M.ι g * (M.x ^ (n + 1))⁻¹ =
        M.x ^ n * (M.x * M.ι g * M.x⁻¹) * (M.x ^ n)⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      group
    rw [h1, M.x_conj, ih, pow_succ, MulAut.mul_apply]

@[expose] def Rep (p : Pr3) (y : X) : Prop :=
  p.1.size = 9 ∧ p.2 < 3 ∧ ∃ g : SU,
    toMat3 p.1 = ((g : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) ∧ y = M.ι g * M.x ^ p.2

theorem rep_one : M.Rep oneP3 1 :=
  ⟨size_oneArr3, by decide, 1, by simp [oneP3, toMat3_oneArr3], by simp [oneP3]⟩

theorem rep_mul {p q : Pr3} {y y' : X} (hp : M.Rep p y) (hq : M.Rep q y') :
    M.Rep (mulP3 p q) (y * y') := by
  obtain ⟨hps, hpj, g, hg, rfl⟩ := hp
  obtain ⟨hqs, hqj, h, hh, rfl⟩ := hq
  refine ⟨by simp [mulP3, size_mulArr3], by simp [mulP3]; omega, g * (sigSU ^ p.2) h, ?_, ?_⟩
  · simp only [mulP3, toMat3_mulArr3, toMat3_sigPow, hg, hh, Subgroup.coe_mul, Units.val_mul,
      coe_sigSU_pow]
  · have h1 : M.ι g * M.x ^ p.2 * (M.ι h * M.x ^ q.2) =
        M.ι (g * (sigSU ^ p.2) h) * M.x ^ (p.2 + q.2) := by
      rw [map_mul, ← M.x_pow_conj p.2 h, pow_add]
      group
    rw [h1]
    simp only [mulP3]
    rw [pow_eq_pow_mod (p.2 + q.2) M.x_cube]

theorem rep_inv {p : Pr3} {y : X} (hp : M.Rep p y) : M.Rep (invP3 p) y⁻¹ := by
  obtain ⟨hps, hpj, g, hg, rfl⟩ := hp
  have hn : (3 - p.2) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hinv : (((g⁻¹ : SU) : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) =
      ((toMat3 p.1).map barC)ᵀ := by
    obtain ⟨-, hmul⟩ := mem_SU_iff'.1 g.2
    rw [← hg] at hmul
    rw [hg]
    exact Units.inv_eq_of_mul_eq_one_left (by rw [← hg]; exact (hg ▸ hmul))
  refine ⟨by simp [invP3, size_sigPow, size_conjTrArr3], hn, (sigSU ^ ((3 - p.2) % 3)) g⁻¹, ?_, ?_⟩
  · simp only [invP3, toMat3_sigPow, toMat3_conjTrArr3, coe_sigSU_pow, hinv]
  · have h1 : (M.ι g * M.x ^ p.2)⁻¹ = M.x ^ ((3 - p.2) % 3) * M.ι g⁻¹ := by
      have : M.x ^ ((3 - p.2) % 3) = (M.x ^ p.2)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_add, pow_eq_pow_mod _ M.x_cube]
        have : (3 - p.2 + p.2) % 3 = 0 := by omega
        simp [this]
      rw [mul_inv_rev, this, map_inv]
    rw [h1]
    have h2 := M.x_pow_conj ((3 - p.2) % 3) g⁻¹
    simp only [invP3]
    calc M.x ^ ((3 - p.2) % 3) * M.ι g⁻¹
        = (M.x ^ ((3 - p.2) % 3) * M.ι g⁻¹ * (M.x ^ ((3 - p.2) % 3))⁻¹) *
            M.x ^ ((3 - p.2) % 3) := by group
      _ = _ := by rw [h2]

theorem rep_ext {p q : Pr3} {y y' : X} (hp : M.Rep p y) (hq : M.Rep q y')
    (h : eqMod M.sc p q = true) : y = y' := by
  obtain ⟨hps, hpj, g, hg, rfl⟩ := hp
  obtain ⟨hqs, hqj, h', hh, rfl⟩ := hq
  simp only [eqMod, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
  obtain ⟨hj, s, hs, hsq⟩ := h
  obtain ⟨z, hz, hzι⟩ := M.sc_ker s hs
  have hgz : g = h' * z := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, ← hg, hz, ← hh]
    rw [hsq, toMat3_smulArr3, Matrix.mul_smul, Matrix.mul_one]
  rw [hgz, map_mul, hzι, mul_one, hj]

theorem rep_inj {p : Pr3} (hp : M.Rep p 1) : eqMod M.sc p oneP3 = true := by
  obtain ⟨hps, hpj, g, hg, h1⟩ := hp
  obtain ⟨hj, s, hs, hgs⟩ := M.inj g p.2 hpj h1.symm
  simp only [eqMod, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, oneP3]
  refine ⟨hj, s, hs, ?_⟩
  apply eq_of_toMat_eq3 hps (by rw [size_smulArr3]; exact size_oneArr3)
  rw [hg, hgs, toMat3_smulArr3, toMat3_oneArr3]

theorem rep_exists {p : Pr3} (h : validS p = true) :
    ∃ y, M.Rep p y := by
  simp only [validS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨g, hg⟩ := exists_su_of_isSUArr h.1
  exact ⟨M.ι g * M.x ^ p.2, isSUArr_size h.1, h.2, g, hg.symm, rfl⟩

@[expose] noncomputable def repSys : RepSys X where
  Rep := M.Rep
  sc := M.sc
  valid := validS
  rep_exists := fun {_} h => M.rep_exists h
  rep_one := M.rep_one
  rep_mul := fun {_ _ _ _} hp hq => M.rep_mul hp hq
  rep_inv := fun {_ _} hp => M.rep_inv hp
  rep_ext := fun {_ _ _ _} hp hq h => M.rep_ext hp hq h
  rep_inj := fun {_} hp => M.rep_inj hp

end Model

end CFSG.AGLEmbedding.ChevOuter.U38
