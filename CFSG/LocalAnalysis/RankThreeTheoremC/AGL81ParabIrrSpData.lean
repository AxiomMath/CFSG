module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrSpModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpTransfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Sp

open Matrix CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
open SymplecticHigher (flagStabilizer fieldSp)

variable {A : Type} [Group A] {Y P : Subgroup A} {r : ℕ} {K : Type} [Field K] {I : Set ℕ}

theorem autHom_eq_one_of_centralizes (C : SpCover Y P r K I)
    (c : ↥(Subgroup.normalizer (Y : Set A))) (h : ∀ y ∈ Y, (c : A) * y = y * c) :
    C.autHom c = 1 := by
  refine MulEquiv.ext fun x => ?_
  apply C.ρ.injective
  apply Subtype.ext
  rw [C.coe_ρ_autHom, MulAut.one_apply, h _ (C.ρ x).2, mul_inv_cancel_right]

section Data

variable [Finite A] [Finite K] [CharP K 2]

theorem exists_blockData (C : SpCover Y P r K I) (hr : 2 ≤ r) (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r)
    {t : ℕ} (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t)
    (hbig : 1 ≤ r - t ∨ ∃ b ∈ I, 2 ≤ b - spFlagPrev I b) (hPY : P ≤ Y) {p : ℕ} (hp : Odd p)
    (b : ↥(Subgroup.normalizer (Y : Set A))) {k : ℕ} (hbk : (b : A) ^ p ^ k = 1)
    (hbP : (b : A) ∈ Subgroup.normalizer (P : Set A)) (hW : WCent P (b : A)) :
    ∃ g : flagStabilizer r K I,
      (∀ x, C.autHom b x = (g : StatedSp r K) * x * (g : StatedSp r K)⁻¹) ∧
      (∀ (b' : ℕ) (hb' : b' ∈ I), spFlagCutHom (fun i hi => (hI i hi).2) (spFlagPrev_mem I b')
        hb' g ∈ Subgroup.center (GL (Fin (b' - spFlagPrev I b')) K)) ∧
      spFlagResHom (fun i hi => (hI i hi).2) htI g = 1 := by
  have hI₀ : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  have hI₁ : ∀ i ∈ I, 1 ≤ i := fun i hi => (hI i hi).1
  have hn := C.spNormFix_autHom hI htI hmax hPY b hbP hW
  obtain ⟨g, σ, hg⟩ := exists_data hr hI htI (C.odd_orderOf_autHom b hp hbk) hn
  have hσ : σ = 1 := sigma_eq_one hI₀ htI hI₁ hmax hbig hn hg
  subst hσ
  refine ⟨g, fun x => ?_, fun b' hb' => cutHom_mem_center hI₀ htI hI₁ hn hg hb', ?_⟩
  · rw [hg x, map_one, MulAut.one_apply]
  · refine eq_one_of_forall_commute_spResBlock (r - t) fun c hc => ?_
    exact resHom_commute_spResBlock hI₀ htI hmax hn hg hc

theorem exists_lift_hom (C : SpCover Y P r K I) {B : Subgroup A}
    (hBY : B ≤ Subgroup.normalizer (Y : Set A)) {Q : flagStabilizer r K I → Prop}
    (hex : ∀ b (hb : b ∈ B), ∃ g : flagStabilizer r K I,
      (∀ x, C.autHom ⟨b, hBY hb⟩ x = (g : StatedSp r K) * x * (g : StatedSp r K)⁻¹) ∧ Q g) :
    ∃ ψ : ↥B →* flagStabilizer r K I, ∀ b : ↥B,
      (∀ x, C.autHom ⟨b, hBY b.2⟩ x = (ψ b : StatedSp r K) * x * (ψ b : StatedSp r K)⁻¹) ∧
        Q (ψ b) := by
  choose g hg using hex
  refine ⟨MonoidHom.mk' (fun b => g b b.2) fun b₁ b₂ => ?_, fun b => hg b b.2⟩
  apply Subtype.ext
  apply eq_of_forall_conj_eq
  intro x
  have hmul : C.autHom ⟨((b₁ * b₂ : ↥B) : A), hBY (b₁ * b₂).2⟩ x =
      C.autHom ⟨b₁, hBY b₁.2⟩ (C.autHom ⟨b₂, hBY b₂.2⟩ x) := by
    rw [← MulAut.mul_apply, ← map_mul]
    rfl
  rw [← (hg _ (b₁ * b₂).2).1 x, hmul, (hg _ b₁.2).1, (hg _ b₂.2).1]
  simp [mul_assoc]

end Data

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Sp
