module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113NT
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Out
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Swap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Perm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Seed

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint Equiv

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T : Subgroup G}
  {Alt : Subgroup (Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem sec113_a_interchanges [Finite G] (hp : Asc82Pre11) {R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hm : Sec11Model t L S z K1 K2 T Alt φ) {k : Fin 6}
    (hk : 2 ≤ k) :
    (∀ a ∈ twoCoreIn K1, φ (Pi.single k 1) * a * (φ (Pi.single k 1))⁻¹ ∈ twoCoreIn K2) ∧
      ∀ a ∈ twoCoreIn K2, φ (Pi.single k 1) * a * (φ (Pi.single k 1))⁻¹ ∈ twoCoreIn K1 := by
  have hctx10 := hctx.toSec10Ctx
  have F := sec113_frame hp hctx10
  have hQ := sec113_Q_eq hp hctx10
  have hTst := asc82Step111T_of hp G t L S z K1 K2 T hctx10 hctx.hyp hctx.sylowT hctx.S_le
  have haT : φ (Pi.single k 1) ∈ T := sec113_A_le_T hp hctx (hm.perm.mem _)
  have haz : φ (Pi.single k 1) * z * (φ (Pi.single k 1))⁻¹ = z := sec113_conj_z hp hctx haT
  have haQ : ∀ q ∈ twoCoreIn K1 ⊔ twoCoreIn K2,
      φ (Pi.single k 1) * q * (φ (Pi.single k 1))⁻¹ ∈ twoCoreIn K1 ⊔ twoCoreIn K2 := by
    intro q hq
    rw [← hQ] at hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hTst.2.2.2 haT) q).mp hq
  rcases F.pair.perm haz haQ with ⟨h1, -⟩ | h
  · exfalso
    have hswap := sec113_swap hp hctx hm hk
    have hmain := (sec10KS_main hp.facts.pockets5 hp.facts.centZ5
      (hp.basic G t L S z hctx10.toSec10Z).1 hctx10).2.2
    have hzc : φ (Pi.single k 1) * z = z * φ (Pi.single k 1) :=
      calc φ (Pi.single k 1) * z = (φ (Pi.single k 1) * z * (φ (Pi.single k 1))⁻¹) *
            φ (Pi.single k 1) := by group
        _ = z * φ (Pi.single k 1) := by rw [haz]
    obtain ⟨a, ha, haz'⟩ := F.pair.exists_outside1
    apply haz'
    have hK2 : φ (Pi.single k 1) * a * (φ (Pi.single k 1))⁻¹ ∈ K2 := by
      rw [← hswap, mem_conjugate_iff']
      have e : φ (Pi.single k 1) * (φ (Pi.single k 1) * a * (φ (Pi.single k 1))⁻¹) *
          (φ (Pi.single k 1))⁻¹ = a := by
        calc _ = (φ (Pi.single k 1) * φ (Pi.single k 1)) * a *
              (φ (Pi.single k 1) * φ (Pi.single k 1))⁻¹ := by group
          _ = a := by rw [sec113_a_sq hm k]; group
      rw [e]
      exact F.Q1_le ha
    have hw : φ (Pi.single k 1) * a * (φ (Pi.single k 1))⁻¹ ∈ zpowers z := by
      rw [← hmain]
      exact ⟨F.Q1_le (h1 a ha), hK2⟩
    have hcomm := sec113_conj_zpowers hzc hw
    have e2 : φ (Pi.single k 1) * (φ (Pi.single k 1) * a * (φ (Pi.single k 1))⁻¹) *
        (φ (Pi.single k 1))⁻¹ = a := by
      calc _ = (φ (Pi.single k 1) * φ (Pi.single k 1)) * a *
            (φ (Pi.single k 1) * φ (Pi.single k 1))⁻¹ := by group
        _ = a := by rw [sec113_a_sq hm k]; group
    rw [e2] at hcomm
    rw [hcomm]
    exact hw
  · exact h

theorem sec113_correct [Finite G] (hp : Asc82Pre11) {R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hm : Sec11Model t L S z K1 K2 T Alt φ) {x0 : G}
    (hx0T : x0 ∈ T) (hx02 : x0 * x0 = 1) (hsh : Sec113Shape (hm.perm.rho x0)) :
    ∃ x : G, x ∈ T ∧ x * x = 1 ∧ hm.perm.rho x = hm.perm.rho x0 ∧
      (∀ a ∈ twoCoreIn K1, x * a * x⁻¹ ∈ twoCoreIn K1) ∧
      ∀ a ∈ twoCoreIn K2, x * a * x⁻¹ ∈ twoCoreIn K2 := by
  have hctx10 := hctx.toSec10Ctx
  have F := sec113_frame hp hctx10
  have hQ := sec113_Q_eq hp hctx10
  have hTst := asc82Step111T_of hp G t L S z K1 K2 T hctx10 hctx.hyp hctx.sylowT hctx.S_le
  have hx0z : x0 * z * x0⁻¹ = z := sec113_conj_z hp hctx hx0T
  have hx0Q : ∀ q ∈ twoCoreIn K1 ⊔ twoCoreIn K2,
      x0 * q * x0⁻¹ ∈ twoCoreIn K1 ⊔ twoCoreIn K2 := by
    intro q hq
    rw [← hQ] at hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hTst.2.2.2 hx0T) q).mp hq
  rcases F.pair.perm hx0z hx0Q with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨x0, hx0T, hx02, rfl, h1, h2⟩
  · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc, hxa, hxc⟩ := hsh.ex
    have hcA : φ (Pi.single c 1) ∈ secA t S L := hm.perm.mem _
    have hcT : φ (Pi.single c 1) ∈ T := sec113_A_le_T hp hctx hcA
    have hx0M : x0 ∈ secM t S L := sec113_T_le_M hctx hx0T
    have hcM : φ (Pi.single c 1) ∈ secM t S L := Subgroup.le_normalizer hcA
    have hcomm : x0 * φ (Pi.single c 1) = φ (Pi.single c 1) * x0 := by
      have h := sec113_conj_single hm hx0M c
      rw [hxc] at h
      calc x0 * φ (Pi.single c 1) = (x0 * φ (Pi.single c 1) * x0⁻¹) * x0 := by group
        _ = φ (Pi.single c 1) * x0 := by rw [h]
    obtain ⟨hi1, hi2⟩ := sec113_a_interchanges hp hctx hm hc
    refine ⟨x0 * φ (Pi.single c 1), T.mul_mem hx0T hcT, ?_, ?_, ?_, ?_⟩
    · calc x0 * φ (Pi.single c 1) * (x0 * φ (Pi.single c 1))
          = x0 * (φ (Pi.single c 1) * x0) * φ (Pi.single c 1) := by group
        _ = x0 * (x0 * φ (Pi.single c 1)) * φ (Pi.single c 1) := by rw [← hcomm]
        _ = (x0 * x0) * (φ (Pi.single c 1) * φ (Pi.single c 1)) := by group
        _ = 1 := by rw [hx02, sec113_a_sq hm c]; group
    · rw [hm.perm.rho_mul hx0M hcM, sec113_rho_of_mem_A hm hcA, mul_one]
    · intro q hq
      have e : x0 * φ (Pi.single c 1) * q * (x0 * φ (Pi.single c 1))⁻¹ =
          x0 * (φ (Pi.single c 1) * q * (φ (Pi.single c 1))⁻¹) * x0⁻¹ := by group
      rw [e]
      exact h2 _ (hi1 q hq)
    · intro q hq
      have e : x0 * φ (Pi.single c 1) * q * (x0 * φ (Pi.single c 1))⁻¹ =
          x0 * (φ (Pi.single c 1) * q * (φ (Pi.single c 1))⁻¹) * x0⁻¹ := by group
      rw [e]
      exact h1 _ (hi2 q hq)

theorem sec113_outer [Finite G] (hp : Asc82Pre11) {R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hm : Sec11Model t L S z K1 K2 T Alt φ) {x : G}
    (hxT : x ∈ T) (hx2 : x * x = 1) (hsh : Sec113Shape (hm.perm.rho x))
    (h1 : ∀ a ∈ twoCoreIn K1, x * a * x⁻¹ ∈ twoCoreIn K1)
    (h2 : ∀ a ∈ twoCoreIn K2, x * a * x⁻¹ ∈ twoCoreIn K2) :
    IsOuterOn x (K1 ⊔ oddCoreIn (secK0 t z)) (oddCoreIn (secK0 t z)) ∧
      IsOuterOn x (K2 ⊔ oddCoreIn (secK0 t z)) (oddCoreIn (secK0 t z)) := by
  have hctx10 := hctx.toSec10Ctx
  have F := sec113_frame hp hctx10
  have hQ := sec113_Q_eq hp hctx10
  have hTst := asc82Step111T_of hp G t L S z K1 K2 T hctx10 hctx.hyp hctx.sylowT hctx.S_le
  have hxK0 : x ∈ normalizer (secK0 t z : Set G) := hTst.2.2.1 hxT
  have hxM : x ∈ secM t S L := sec113_T_le_M hctx hxT
  have hxN : ∀ n ∈ oddCoreIn (secK0 t z), x * n * x⁻¹ ∈ oddCoreIn (secK0 t z) :=
    fun n hn => sec11_conj_mem_oddCoreIn hxK0 hn
  have hnt1 := sec113_not_triv hm F.pair hQ hxM h2 hsh
  have hnt2 := sec113_not_triv hm F.pair.symm (hQ.trans (sup_comm _ _)) hxM h1 hsh
  exact ⟨F.isOuterOn hx2 hxK0 hxN h1 h2 hnt1, F.symm.isOuterOn hx2 hxK0 hxN h2 h1 hnt2⟩

end CFSG.OddStandard.SmallF3.Omega
