module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrPow
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrSpData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Sp

open Matrix CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr
open SymplecticHigher (flagStabilizer fieldSp)

section Comb

variable {I : Set ℕ}

theorem eq_of_mem_of_two {r : ℕ} (hr2 : r = 2) (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {t : ℕ}
    (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t)
    (hbig : 1 ≤ r - t ∨ ∃ b ∈ I, 2 ≤ b - spFlagPrev I b) : ∀ b ∈ I, b = t := by
  intro b hb
  by_contra hne
  have hbt : b < t := lt_of_le_of_ne (hmax b hb) hne
  have hb1 := (hI b hb).1
  have ht2 := (hI t htI).2
  have hb' : b = 1 := by omega
  have ht' : t = 2 := by omega
  have hprev : 1 ≤ spFlagPrev I 2 := by
    have := le_spFlagPrev hb (show b < 2 by omega)
    omega
  rcases hbig with h | ⟨c, hc, h⟩
  · omega
  · have hc1 := (hI c hc).1
    have hc2 := hmax c hc
    have hprevc := spFlagPrev_le I c
    have hc12 : c = 1 ∨ c = 2 := by omega
    rcases hc12 with rfl | rfl <;> omega

end Comb

section Center

variable {K : Type} [Field K] [CharP K 2]

theorem eq_one_of_det_eq_one_of_mem_center {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ 2)
    {z : GL (Fin n) K} (hz : z ∈ Subgroup.center (GL (Fin n) K))
    (hdet : Matrix.GeneralLinearGroup.det z = 1) : z = 1 := by
  obtain ⟨m, hm⟩ : n ∣ 2 := by
    rcases (by omega : n = 1 ∨ n = 2) with h | h <;> subst h <;> simp
  have hz' := hz
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
  obtain ⟨c, rfl⟩ := hz'
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  refine eq_one_of_mem_center_of_pow_two_pow (k := 1) hz ?_
  rw [pow_one, hm, pow_mul, ← map_pow, hdet, map_one, one_pow]

end Center

section Conj

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_one_of_conj_apply {g : StatedSp r K} (h : ∀ x, g * x * g⁻¹ = x) : g = 1 :=
  eq_of_forall_conj_eq fun x => by simpa using h x

theorem pow_eq_one_of_autHom_pow {α : MulAut (StatedSp r K)} {g : StatedSp r K}
    (hg : ∀ x, α x = g * x * g⁻¹) {N : ℕ} (hα : α ^ N = 1) : g ^ N = 1 := by
  have e : α = MulAut.conj g := MulEquiv.ext fun x => by rw [hg x, MulAut.conj_apply]
  rw [e, ← map_pow] at hα
  refine eq_one_of_conj_apply fun x => ?_
  have h2 : (MulAut.conj (g ^ N)) x = (1 : MulAut (StatedSp r K)) x := by rw [hα]
  rwa [MulAut.conj_apply, MulAut.one_apply] at h2

end Conj

section Two

variable {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {r : ℕ} {K : Type} [Field K]
  [Finite K] [CharP K 2] {I : Set ℕ}

theorem parabIrr_of_two (C : SpCover Y P r K I) (hr2 : r = 2) (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r)
    {t : ℕ} (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t)
    (hbig : 1 ≤ r - t ∨ ∃ b ∈ I, 2 ≤ b - spFlagPrev I b) (hPY : P ≤ Y) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {B N : Subgroup A} (hB : IsPGroup p ↥B) (hcyc : ¬ IsCyclic ↥B)
    (hBY : B ≤ Subgroup.normalizer (Y : Set A)) (hBP : B ≤ Subgroup.normalizer (P : Set A))
    (hW : ∀ b ∈ B, WCent P b) (hNY : N ≤ Subgroup.normalizer (Y : Set A))
    (hNB : N ≤ Subgroup.normalizer (B : Set A)) (hirr : IrredOn N B) :
    ∀ b ∈ B, ∀ y ∈ Y, b * y = y * b := by
  have hI₀ : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  have hI₁ : ∀ i ∈ I, 1 ≤ i := fun i hi => (hI i hi).1
  have hIt : ∀ b ∈ I, b = t := eq_of_mem_of_two hr2 hI htI hmax hbig
  obtain ⟨ψ, hψ⟩ := exists_lift_hom C hBY
    (Q := fun g => (∀ (b' : ℕ) (hb' : b' ∈ I), spFlagCutHom hI₀ (spFlagPrev_mem I b') hb' g ∈
        Subgroup.center (GL (Fin (b' - spFlagPrev I b')) K)) ∧ spFlagResHom hI₀ htI g = 1)
    (fun b hb => by
      obtain ⟨j, hj⟩ := hB ⟨b, hb⟩
      have hbj : b ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
      obtain ⟨g, hg, hcut, hres⟩ := exists_blockData C (by omega) hI htI hmax hbig hPY
        (hp.odd_of_ne_two hp2) ⟨b, hBY hb⟩ hbj (hBP hb) (hW b hb)
      exact ⟨g, hg, hcut, hres⟩)
  obtain ⟨θ, hθdef⟩ : ∃ θ : ↥B →* Kˣ, ∀ b, θ b = Matrix.GeneralLinearGroup.det
      (spFlagCutHom hI₀ (spFlagPrev_mem I t) htI (ψ b)) :=
    ⟨Matrix.GeneralLinearGroup.det.comp ((spFlagCutHom hI₀ (spFlagPrev_mem I t) htI).comp ψ),
      fun b => rfl⟩
  have hn1 : 1 ≤ t - spFlagPrev I t := by
    have h1 := spFlagPrev_le I t
    have h2 := hI₁ t htI
    omega
  have hn2 : t - spFlagPrev I t ≤ 2 := by
    have h2 := hI₀ t htI
    omega
  have hθ : ∀ b : ↥B, θ b = 1 ↔ ∀ y ∈ Y, (b : A) * y = y * b := by
    intro b
    obtain ⟨hψb, hcut, hres⟩ := hψ b
    constructor
    · intro h1
      have hz1 : spFlagCutHom hI₀ (spFlagPrev_mem I t) htI (ψ b) = 1 :=
        eq_one_of_det_eq_one_of_mem_center hn1 hn2 (hcut t htI) (by rw [← hθdef]; exact h1)
      have hker : spFlagLeviHom hI₀ htI (ψ b) = 1 := by
        refine leviHom_eq_one_of_blocks hI₀ htI (fun b' hb' => ?_) hres
        obtain rfl := hIt b' hb'
        exact hz1
      obtain ⟨n, hn⟩ := isPGroup_ker_spFlagLeviHom hI₀ htI hI₁ ⟨ψ b, hker⟩
      have hn' : ψ b ^ 2 ^ n = 1 := congrArg Subtype.val hn
      obtain ⟨j, hj⟩ := hB b
      have hbj : (b : A) ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
      have hα := C.autHom_pow_eq_one ⟨b, hBY b.2⟩ hbj
      have hj' : ψ b ^ p ^ j = 1 := Subtype.ext (pow_eq_one_of_autHom_pow hψb hα)
      have hψ1 : ψ b = 1 := eq_one_of_pow_two_pow hp hp2 hj' hn'
      refine C.centralizes_of_autHom_eq_one ⟨b, hBY b.2⟩ (MulEquiv.ext fun x => ?_)
      rw [hψb x, hψ1, MulAut.one_apply]
      simp
    · intro hc
      have h1 : C.autHom ⟨b, hBY b.2⟩ = 1 := autHom_eq_one_of_centralizes C _ hc
      have hψ1 : ψ b = 1 := Subtype.ext (eq_one_of_conj_apply fun x => by
        rw [← hψb x, h1, MulAut.one_apply])
      rw [hθdef, hψ1, map_one, map_one]
  have hall := forall_eq_one_of_irred hcyc hirr hNB θ fun n hn b hb1 hb =>
    ker_invariant_of_eq_centralizer θ hθ (hNY hn) b hb1 hb
  intro b hb
  exact (hθ ⟨b, hb⟩).1 (hall ⟨b, hb⟩)

end Two

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Sp
