module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceTransport
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Diag
import CFSG.HardMathSupport.Curtis.Proving.ToralNormalizerCentralizer
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchGlue
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceRank
import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralReduce CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding.LinearThreeKit

section Core

variable {Y : Type} [Group Y] {L : Subgroup Y} {K : Type} [Field K]

theorem map_center_eq_scalars (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K) :
    (Subgroup.center ↥L).map ψ.toMonoidHom = scalars 3 K := by
  rw [scalars_eq_center]; exact Subgroup.map_center_eq ψ

noncomputable def projEquiv (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K) :
    ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL 3 K :=
  QuotientGroup.congr (Subgroup.center ↥L) (scalars 3 K) ψ (map_center_eq_scalars ψ)

theorem censusHom_projEquiv (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K) (l : ↥L) :
    censusHom (projEquiv ψ) l = proj 3 K (ψ l) :=
  QuotientGroup.congr_mk' _ _ _ (map_center_eq_scalars ψ) l

theorem exists_setup [Finite Y] [Finite K] [CharP K 2] {J : Subgroup Y} (hCP : CompParab L J)
    (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K) :
    ∃ (ψ' : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K) (d : ℕ), (d = 1 ∨ d = 2) ∧
      ∀ l : ↥L, (l : Y) ∈ J ↔ ψ' l ∈ stabilizer (flagSpace 3 K d) := by
  obtain ⟨g, d, hd, hJ⟩ := exists_eq_map_conj_projStabilizer (projEquiv ψ) hCP
  obtain ⟨g', rfl⟩ := proj_surjective 3 K g
  refine ⟨ψ.trans (MulAut.conj g'⁻¹), d, hd, fun l => ?_⟩
  rw [← censusHom_mem_map_iff (projEquiv ψ) hCP.parab, hJ, censusHom_projEquiv,
    Subgroup.mem_map_equiv]
  rw [← comap_projStabilizer, Subgroup.mem_comap]
  have : (MulAut.conj (proj 3 K g')).symm (proj 3 K (ψ l)) =
      proj 3 K ((ψ.trans (MulAut.conj g'⁻¹)) l) := by
    simp [MulAut.conj_symm_apply, proj]
  rw [this]

noncomputable def normAut (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K) :
    ↥(Subgroup.normalizer (L : Set Y)) →* MulAut (Matrix.SpecialLinearGroup (Fin 3) K) :=
  (MulAut.congr ψ).toMonoidHom.comp (Subgroup.normalizerMonoidHom L)

theorem normAut_apply (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    (x : ↥(Subgroup.normalizer (L : Set Y))) (l : ↥L) :
    normAut ψ x (ψ l) = ψ ((Subgroup.normalizerMonoidHom L x) l) := by
  simp [normAut, MulAut.congr_apply]

theorem coe_normalizerMonoidHom (x : ↥(Subgroup.normalizer (L : Set Y))) (l : ↥L) :
    (((Subgroup.normalizerMonoidHom L x) l : ↥L) : Y) = (x : Y) * l * (x : Y)⁻¹ := by
  simp

theorem normAut_eq_one_iff (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    (x : ↥(Subgroup.normalizer (L : Set Y))) :
    normAut ψ x = 1 ↔ (x : Y) ∈ Subgroup.centralizer (L : Set Y) := by
  have key : normAut ψ x = 1 ↔ Subgroup.normalizerMonoidHom L x = 1 := by
    constructor
    · intro h
      exact (MulAut.congr ψ).injective (show (MulAut.congr ψ) (L.normalizerMonoidHom x) =
        (MulAut.congr ψ) 1 by rw [map_one]; exact h)
    · intro h
      show (MulAut.congr ψ) (L.normalizerMonoidHom x) = 1
      rw [h, map_one]
  rw [key]
  constructor
  · intro h1
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := congrArg (fun σ : MulAut ↥L => ((σ ⟨l, hl⟩ : ↥L) : Y)) h1
    simp only [coe_normalizerMonoidHom, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  · intro hx
    refine MulEquiv.ext fun l => Subtype.ext ?_
    rw [coe_normalizerMonoidHom, MulAut.one_apply]
    have := Subgroup.mem_centralizer_iff.mp hx l l.2
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm

theorem exists_mul_of_mem_sup_centralizer' {u : Y} (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y)) :
    ∃ (t : ↥L) (c : Y), c ∈ Subgroup.centralizer (L : Set Y) ∧ (t : Y) * c = u := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (ToralCensus.le_normalizer_centralizer L)] at hu
  obtain ⟨t, ht, c, hc, htc⟩ := hu
  exact ⟨⟨t, ht⟩, c, hc, htc⟩

theorem mem_center_iff_mem_centralizer (t : ↥L) :
    t ∈ Subgroup.center ↥L ↔ (t : Y) ∈ Subgroup.centralizer (L : Set Y) := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h l hl
    exact congrArg Subtype.val (h ⟨l, hl⟩)
  · intro h l
    exact Subtype.ext (h l l.2)

section Toral

variable {u : Y} {t : ↥L} {c : Y} (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K)

theorem ψ_mem_scalars_iff (l : ↥L) :
    ψ l ∈ scalars 3 K ↔ l ∈ Subgroup.center ↥L := by
  rw [← map_center_eq_scalars ψ]
  exact Subgroup.mem_map_iff_mem (f := ψ.toMonoidHom) ψ.injective

theorem coe_mul_comm_of_mem_centralizer (hc : c ∈ Subgroup.centralizer (L : Set Y)) :
    (t : Y) * c = c * t :=
  Subgroup.mem_centralizer_iff.mp hc t t.2

theorem psi_not_mem_scalars (hc : c ∈ Subgroup.centralizer (L : Set Y)) (htc : (t : Y) * c = u)
    (huC : u ∉ Subgroup.centralizer (L : Set Y)) : ψ t ∉ scalars 3 K := by
  rw [ψ_mem_scalars_iff, mem_center_iff_mem_centralizer]
  intro h
  apply huC
  rw [← htc]
  exact Subgroup.mul_mem _ h hc

theorem psi_pow_three_mem_scalars (hc : c ∈ Subgroup.centralizer (L : Set Y))
    (htc : (t : Y) * c = u) (hu3 : u ^ 3 = 1) : ψ t ^ 3 ∈ scalars 3 K := by
  rw [← map_pow, ψ_mem_scalars_iff, mem_center_iff_mem_centralizer]
  have h1 : ((t : Y)) ^ 3 * c ^ 3 = 1 := by
    rw [← (show Commute (t : Y) c from coe_mul_comm_of_mem_centralizer hc).mul_pow, htc, hu3]
  have h2 : ((t ^ 3 : ↥L) : Y) = (c ^ 3)⁻¹ := by
    rw [Subgroup.coe_pow]
    exact eq_inv_of_mul_eq_one_left h1
  rw [h2]
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc 3)

theorem coe_mem_J (hc : c ∈ Subgroup.centralizer (L : Set Y)) (htc : (t : Y) * c = u)
    {J : Subgroup Y} (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) : (t : Y) ∈ J := by
  refine hfix t t.2 ?_
  rw [mul_inv_eq_iff_eq_mul, ← htc, mul_assoc, ← coe_mul_comm_of_mem_centralizer hc, ← mul_assoc]

theorem exists_center_of_conj (hc : c ∈ Subgroup.centralizer (L : Set Y)) (htc : (t : Y) * c = u)
    (x : ↥(Subgroup.normalizer (L : Set Y))) (hx : (x : Y) * u * (x : Y)⁻¹ = u) :
    ∃ z ∈ Subgroup.center ↥L, Subgroup.normalizerMonoidHom L x t = t * z := by
  have hc' : (x : Y) * c * (x : Y)⁻¹ ∈ Subgroup.centralizer (L : Set Y) :=
    CFSG.HardMathSupport.Curtis.Proving.conj_mem_centralizer_of_mem_normalizer x.2 hc
  have e : ((x : Y) * t * (x : Y)⁻¹) * ((x : Y) * c * (x : Y)⁻¹) = t * c := by
    calc ((x : Y) * t * (x : Y)⁻¹) * ((x : Y) * c * (x : Y)⁻¹)
        = (x : Y) * (t * c) * (x : Y)⁻¹ := by group
      _ = t * c := by rw [htc, hx]
  have e2 : (x : Y) * t * (x : Y)⁻¹ = t * c * ((x : Y) * c * (x : Y)⁻¹)⁻¹ :=
    eq_mul_inv_of_mul_eq e
  refine ⟨t⁻¹ * Subgroup.normalizerMonoidHom L x t, ?_, by simp⟩
  rw [mem_center_iff_mem_centralizer]
  have : (((t⁻¹ * Subgroup.normalizerMonoidHom L x t : ↥L)) : Y) =
      c * ((x : Y) * c * (x : Y)⁻¹)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_normalizerMonoidHom, e2]
    group
  rw [this]
  exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hc')

end Toral

end Core

section Block

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

theorem blockPL_eq_inf_normalizer (hSM : S ≤ M) (hQS : pCoreOf 2 M ≤ S) :
    blockPL M S L = barM M L ⊓ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  refine le_antisymm (le_inf (barM_mono inf_le_right) ?_) ?_
  ·
    rintro _ ⟨n, hn, rfl⟩
    have hnN : (n : G) ∈ Subgroup.normalizer (S : Set G) := (Subgroup.mem_subgroupOf.mp hn).1
    refine Subgroup.mem_normalizer_fintype fun h hh => ?_
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨n * m * n⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    have := (Subgroup.mem_normalizer_iff.mp hnN m).mp (Subgroup.mem_subgroupOf.mp hm)
    simpa using this
  · rintro j ⟨hjL, hjN⟩
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hjL
    have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
    have hlN : (l : G) ∈ Subgroup.normalizer (S : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun s hs => ?_
      have hsM : s ∈ M := hSM hs
      have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) l * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨s, hsM⟩ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M) l)⁻¹ ∈ barM M S :=
        (Subgroup.mem_normalizer_iff.mp hjN _).mp
          (Subgroup.mem_map.mpr ⟨⟨s, hsM⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩)
      obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp hmem
      have hm' : (m : G) ∈ S := Subgroup.mem_subgroupOf.mp hm
      have hq : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (m⁻¹ * (l * ⟨s, hsM⟩ * l⁻¹)) = 1 := by
        have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (m⁻¹ * (l * ⟨s, hsM⟩ * l⁻¹)) =
            (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m)⁻¹ *
              (QuotientGroup.mk' (CFSG.pCore 2 ↥M) l *
                QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨s, hsM⟩ *
                (QuotientGroup.mk' (CFSG.pCore 2 ↥M) l)⁻¹) := by
          simp only [map_mul, map_inv]
        rw [h1, hme, inv_mul_cancel]
      have hkS : ((m⁻¹ * (l * ⟨s, hsM⟩ * l⁻¹) : ↥M) : G) ∈ S :=
        hQS (coe_mem_pCoreOf_two_of_mk_eq_one _ hq)
      have : (l : G) * s * (l : G)⁻¹ = (m : G) * ((m⁻¹ * (l * ⟨s, hsM⟩ * l⁻¹) : ↥M) : G) := by
        simp
      rw [this]
      exact S.mul_mem hm' hkS
    exact Subgroup.mem_map.mpr ⟨l, Subgroup.mem_subgroupOf.mpr ⟨hlN, hlL⟩, rfl⟩

end Block

section Eigen

variable {K : Type} [Field K]

theorem exists_eigenvalue_cube {d : ℕ} (hd : d = 1 ∨ d = 2) {s : Matrix.SpecialLinearGroup (Fin 3) K}
    (hsJ : s ∈ stabilizer (flagSpace 3 K d)) {c : K}
    (hS3 : (s : Matrix (Fin 3) (Fin 3) K) ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ x : K, x ^ 3 = c := by
  obtain ⟨x, v₀, hv0, hxv⟩ := exists_eigenvector_of_mem_stabilizer hd hsJ
  refine ⟨x, ?_⟩
  have h3 := pow_mulVec_of_mulVec_eq_smul hxv 3
  rw [hS3, Matrix.smul_mulVec, Matrix.one_mulVec] at h3
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have := congrFun h3 i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact (mul_right_cancel₀ hi this).symm

theorem pow_three_eq_one_of_not_nine_dvd [Finite K] (h9 : ¬ 9 ∣ Nat.card K - 1) {d : ℕ}
    (hd : d = 1 ∨ d = 2) {s : Matrix.SpecialLinearGroup (Fin 3) K}
    (hsJ : s ∈ stabilizer (flagSpace 3 K d)) (hs3 : s ^ 3 ∈ scalars 3 K) : s ^ 3 = 1 := by
  obtain ⟨c, hc, hcs⟩ := mem_scalars.mp hs3
  have hS3 : (s : Matrix (Fin 3) (Fin 3) K) ^ 3 = (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hcs, Matrix.smul_one_eq_diagonal,
      Matrix.scalar_apply]
  obtain ⟨x, hx⟩ := exists_eigenvalue_cube hd hsJ hS3
  have hc3 : (c : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  by_cases hc1 : (c : K) = 1
  · refine Subtype.ext ?_
    show (s : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1
    rw [hS3, hc1, one_smul]
  · exfalso
    have hx0 : x ≠ 0 := fun h0 => by
      rw [h0] at hx
      have : (c : K) = 0 := by rw [← hx]; norm_num
      exact c.ne_zero this
    let u : Kˣ := Units.mk0 x hx0
    have hu3 : ¬ u ^ 3 ^ 1 = 1 := fun h => hc1 (by
      rw [← hx]; simpa [u] using congrArg Units.val h)
    have hu9 : u ^ 3 ^ (1 + 1) = 1 := by
      apply Units.ext
      simp only [u, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      calc x ^ 3 ^ (1 + 1) = (x ^ 3) ^ 3 := by
            rw [← pow_mul]; norm_num
        _ = 1 := by rw [hx, hc3]
    have hord : orderOf u = 3 ^ (1 + 1) :=
      orderOf_eq_prime_pow (p := 3) hu3 hu9
    apply h9
    rw [← Nat.card_units]
    have := orderOf_dvd_natCard u
    rw [hord] at this
    simpa using this

end Eigen

end CFSG.HardMathSupport.Curtis.Coordinator
