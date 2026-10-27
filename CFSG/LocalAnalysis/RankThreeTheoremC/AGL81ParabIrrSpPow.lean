module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrPow
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrSpData
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrSpAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Sp

open Matrix CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr
open SymplecticHigher (flagStabilizer fieldSp)

variable {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {r : ℕ} {K : Type} [Field K]
  [Finite K] [CharP K 2] {I : Set ℕ}

theorem actsAsPow_of_conj_fieldSp (C : SpCover Y P r K I) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 2 ≤ r) (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {t : ℕ} (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t)
    (hbig : 1 ≤ r - t ∨ ∃ b ∈ I, 2 ≤ b - spFlagPrev I b) (hPY : P ≤ Y) {B : Subgroup A}
    (hBM : B ≤ Subgroup.normalizer (Y : Set A)) (hBp : IsPGroup p ↥B)
    (hBP : B ≤ Subgroup.normalizer (P : Set A)) (hW : ∀ b ∈ B, WCent P b)
    {m : ↥(Subgroup.normalizer (Y : Set A))} (hmB : ∀ b ∈ B, (m : A) * b * (m : A)⁻¹ ∈ B)
    {g' : flagStabilizer r K I} {σ : K ≃+* K} {k : ℕ} (hσ : ∀ a, σ a = a ^ 2 ^ k)
    (hm : ∀ x, C.autHom m x = (g' : StatedSp r K) * fieldSp r K σ x * (g' : StatedSp r K)⁻¹) :
    ActsAsPow C.autHom B hBM m (((2 ^ k : ℕ)) : ℤ) := by
  refine actsAsPow_of_two_pow hp hp2 hBM hBp hmB _ fun b hb => ?_
  obtain ⟨j, hj⟩ := hBp ⟨b, hb⟩
  have hbj : b ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
  obtain ⟨g, hg, hcut, hres⟩ := exists_blockData C hr hI htI hmax hbig hPY
    (hp.odd_of_ne_two hp2) ⟨b, hBM hb⟩ hbj (hBP hb) (hW b hb)
  obtain ⟨i, hi⟩ := exists_pow_two_eq_one_conj_fieldSp hI htI hσ g' g hcut hres
  refine ⟨i, ?_⟩
  have e1 : C.autHom m = MulAut.conj (g' : StatedSp r K) * fieldSp r K σ :=
    MulEquiv.ext fun x => by rw [hm x, MulAut.mul_apply, MulAut.conj_apply]
  have e2 : C.autHom ⟨b, hBM hb⟩ = MulAut.conj (g : StatedSp r K) :=
    MulEquiv.ext fun x => by rw [hg x, MulAut.conj_apply]
  rw [e1, e2]
  exact hi

theorem parabIrr_of_three_le (C : SpCover Y P r K I) (hr3 : 3 ≤ r)
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {t : ℕ} (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t)
    (hbig : 1 ≤ r - t ∨ ∃ b ∈ I, 2 ≤ b - spFlagPrev I b) (hPY : P ≤ Y) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {B N : Subgroup A} (hB : IsPGroup p ↥B) (hcyc : ¬ IsCyclic ↥B)
    (hBY : B ≤ Subgroup.normalizer (Y : Set A)) (hBP : B ≤ Subgroup.normalizer (P : Set A))
    (hW : ∀ b ∈ B, WCent P b) (hNY : N ≤ Subgroup.normalizer (Y : Set A))
    (hNP : N ≤ Subgroup.normalizer (P : Set A)) (hNB : N ≤ Subgroup.normalizer (B : Set A))
    (hirr : IrredOn N B) : ∀ b ∈ B, ∀ y ∈ Y, b * y = y * b := by
  have hmB : ∀ x ∈ N, ∀ b ∈ B, x * b * x⁻¹ ∈ B := fun x hx b hb =>
    (Subgroup.mem_normalizer_iff.1 (hNB hx) b).1 hb
  have hpow : ∀ n (hn : n ∈ N), ∃ e : ℤ, ActsAsPow C.autHom B hBY ⟨n, hNY hn⟩ e := by
    intro n hn
    obtain ⟨g', σ, hg'⟩ := exists_conj_fieldSp_flag_of_three_le hr3 hI
      (fun x hx => C.autHom_mem_flagStabilizer ⟨n, hNY hn⟩ (hNP hn) hx)
    obtain ⟨k, hk⟩ := exists_frobenius_two_pow σ
    exact ⟨_, actsAsPow_of_conj_fieldSp C hp hp2 (by omega) hI htI hmax hbig hPY hBY hB hBP hW
      (hmB n hn) hk hg'⟩
  have hall := forall_eq_one_of_actsAsPow (ρ := C.autHom) hBY hNY hcyc hirr hNB hpow
  intro b hb y hy
  exact C.centralizes_of_autHom_eq_one ⟨b, hBY hb⟩ (hall b hb) y hy

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Sp
