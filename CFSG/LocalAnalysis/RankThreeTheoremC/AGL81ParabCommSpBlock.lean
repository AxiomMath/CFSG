module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp

open Matrix CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
open SymplecticHigher (flagStabilizer fieldSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

variable {r : ℕ} {K : Type} [Field K] {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I)

include hI htI in
theorem cutHom_eq_one_of_leviHom_eq_one (hI1 : ∀ i ∈ I, 1 ≤ i) {b : ℕ} (hb : b ∈ I)
    {u : flagStabilizer r K I} (hu : spFlagLeviHom hI htI u = 1) :
    spFlagCutHom hI (spFlagPrev_mem I b) hb u = 1 := by
  have hbr := hI b hb
  have hb1 := hI1 b hb
  have h := congrFun hu ⟨b, by omega⟩
  rw [spFlagLeviHom, MonoidHom.pi_apply,
    spFlagLeviCoord_of_mem hI htI (by simp; omega) hb, MonoidHom.comp_apply, Pi.one_apply,
    ← map_one (spFlagCutEmb (K := K) (spFlagPrev I b) b (hI b hb))] at h
  exact spFlagCutEmb_injective _ _ _ h

include hI htI in
theorem resHom_eq_one_of_leviHom_eq_one {u : flagStabilizer r K I}
    (hu : spFlagLeviHom hI htI u = 1) : spFlagResHom hI htI u = 1 := by
  have h := congrFun hu 0
  rw [spFlagLeviHom, MonoidHom.pi_apply, spFlagLeviCoord_of_eq_zero hI htI rfl,
    MonoidHom.comp_apply, Pi.one_apply, ← map_one (spFlagResEmb (K := K) (r := r) t)] at h
  exact spFlagResEmb_injective t h

include hI htI in
theorem leviHom_eq_one_of_blocks {u : flagStabilizer r K I}
    (hcut : ∀ (b : ℕ) (hb : b ∈ I), spFlagCutHom hI (spFlagPrev_mem I b) hb u = 1)
    (hres : spFlagResHom hI htI u = 1) : spFlagLeviHom hI htI u = 1 := by
  funext j
  rw [spFlagLeviHom, MonoidHom.pi_apply, Pi.one_apply]
  by_cases hj0 : (j : ℕ) = 0
  · rw [spFlagLeviCoord_of_eq_zero hI htI hj0, MonoidHom.comp_apply, hres, map_one]
  by_cases hj : (j : ℕ) ∈ I
  · rw [spFlagLeviCoord_of_mem hI htI hj0 hj, MonoidHom.comp_apply, hcut _ hj, map_one]
  · rw [spFlagLeviCoord_of_not_mem hI htI hj0 hj, MonoidHom.one_apply]

theorem cutHom_fieldSp {a b : ℕ} (ha : a = 0 ∨ a ∈ I) (hb : b ∈ I) (σ : K ≃+* K)
    (x : flagStabilizer r K I) (hx : fieldSp r K σ x ∈ flagStabilizer r K I) :
    ((spFlagCutHom hI ha hb ⟨fieldSp r K σ x, hx⟩ : GL (Fin (b - a)) K) :
        Matrix (Fin (b - a)) (Fin (b - a)) K) =
      ((spFlagCutHom hI ha hb x : GL (Fin (b - a)) K) :
        Matrix (Fin (b - a)) (Fin (b - a)) K).map σ := by
  rw [coe_spFlagCutHom, coe_spFlagCutHom]
  rfl

include htI in
theorem resHom_fieldSp (σ : K ≃+* K) (x : flagStabilizer r K I)
    (hx : fieldSp r K σ x ∈ flagStabilizer r K I) :
    mat (r - t) K (spFlagResHom hI htI ⟨fieldSp r K σ x, hx⟩) =
      (mat (r - t) K (spFlagResHom hI htI x)).map σ := by
  rw [mat_spFlagResHom, mat_spFlagResHom]
  rfl

theorem resHom_fieldSp' (σ : K ≃+* K) (x : flagStabilizer r K I)
    (hx : fieldSp r K σ x ∈ flagStabilizer r K I) :
    spFlagResHom hI htI ⟨fieldSp r K σ x, hx⟩ = fieldSp (r - t) K σ (spFlagResHom hI htI x) :=
  mat_injective (resHom_fieldSp hI htI σ x hx)

theorem cutHom_cutEmb {b : ℕ} (hb : b ∈ I) (A : GL (Fin (b - spFlagPrev I b)) K) :
    spFlagCutHom hI (spFlagPrev_mem I b) hb
      ⟨spFlagCutEmb (spFlagPrev I b) b (hI b hb) A,
        spFlagCutEmb_mem hI _ (fun _ hc => le_spFlagPrev_or_le hc) A⟩ = A :=
  Units.ext (by
    rw [coe_spFlagCutHom]
    exact spFlagCutMat_spFlagCutEmb _ _ _ A)

include htI in
theorem resHom_resEmb (hmax : ∀ c ∈ I, c ≤ t) (c : StatedSp (r - t) K) :
    spFlagResHom hI htI ⟨spFlagResEmb t c, spFlagResEmb_mem hI hmax c⟩ = c :=
  spFlagResHom_resEmb hI htI hmax c

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
