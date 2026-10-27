module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I148XMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148DownCoset
public import CFSG.HardMathSupport.Solomon.Coordinator.L514T

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K148F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

variable {G : Type} [Group G] [Finite G]

theorem k148f_hker {K I' : Subgroup G} (hI'K : I' ≤ K) (hS : IsSimpleGroup ↥(barX 3 K I'))
    (h3 : 3 ∣ Nat.card ↥(barX 3 K I')) :
    (CFSG.HardMathSupport.Solomon.Coordinator.l514t_barXMap hI'K).ker = GLAPPrimeCore 3 ↥I' := by
  apply le_antisymm (CFSG.HardMathSupport.Solomon.Coordinator.l514t_barXMap_ker_le_core hI'K)
  have hsurj := CFSG.HardMathSupport.Solomon.Coordinator.l514t_barXMap_surjective hI'K
  haveI hNn : ((GLAPPrimeCore 3 ↥I').map
      (CFSG.HardMathSupport.Solomon.Coordinator.l514t_barXMap hI'K)).Normal :=
    Subgroup.Normal.map (GLAPPrimeCore.normal 3 ↥I') _ hsurj
  rcases hS.eq_bot_or_eq_top_of_normal ((GLAPPrimeCore 3 ↥I').map
      (CFSG.HardMathSupport.Solomon.Coordinator.l514t_barXMap hI'K)) with h0 | hT
  · intro x hx
    have hmem := Subgroup.mem_map_of_mem (CFSG.HardMathSupport.Solomon.Coordinator.l514t_barXMap hI'K) hx
    rw [h0, Subgroup.mem_bot] at hmem
    exact hmem
  · exfalso
    have hdvd := Subgroup.card_map_dvd (GLAPPrimeCore 3 ↥I')
      (CFSG.HardMathSupport.Solomon.Coordinator.l514t_barXMap hI'K)
    rw [hT, Subgroup.card_top] at hdvd
    have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥I')) :=
      CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 _
    have h3O : 3 ∣ Nat.card ↥(GLAPPrimeCore 3 ↥I') := dvd_trans h3 hdvd
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3O) (by norm_num)

@[expose] noncomputable def k148f_psi {K I' : Subgroup G} (hI'K : I' ≤ K)
    (hker : (CFSG.HardMathSupport.Solomon.Coordinator.l514t_barXMap hI'K).ker = GLAPPrimeCore 3 ↥I') :
    PQuot 3 I' ≃* ↥(barX 3 K I') :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (CFSG.HardMathSupport.Solomon.Coordinator.l514t_barXMap_surjective hI'K))

theorem k148f_psi_mk {K I' : Subgroup G} (hI'K : I' ≤ K)
    (hker : (CFSG.HardMathSupport.Solomon.Coordinator.l514t_barXMap hI'K).ker = GLAPPrimeCore 3 ↥I')
    (x : ↥I') :
    ((k148f_psi hI'K hker (QuotientGroup.mk x) : ↥(barX 3 K I')) : PQuot 3 K) =
      QuotientGroup.mk (Subgroup.inclusion hI'K x) := by
  simp only [k148f_psi, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem k148f_psi_nat {K I' : Subgroup G} {y : G} (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hyI' : y ∈ Subgroup.normalizer (I' : Set G)) (hI'K : I' ≤ K)
    (hker : (CFSG.HardMathSupport.Solomon.Coordinator.l514t_barXMap hI'K).ker = GLAPPrimeCore 3 ↥I')
    {c : PQuot 3 K} (hc : MulAut.conj c = CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩)
    (z : PQuot 3 I') :
    ((k148f_psi hI'K hker (lemma102_conjQ 3 hyI' z) : ↥(barX 3 K I')) : PQuot 3 K) =
      (MulAut.conj c)⁻¹ ((k148f_psi hI'K hker z : ↥(barX 3 K I')) : PQuot 3 K) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  have hinv : ∀ w : PQuot 3 K, (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩)⁻¹ w =
      lemma102_conjQ 3 hyN w := by
    intro w
    apply (MulEquiv.symm_apply_eq _).2
    exact (barAut_comp_conjQ hyN w).symm
  have hcinv : (MulAut.conj c)⁻¹ = (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩)⁻¹ := by
    rw [hc]
  rw [hcinv, k148f_psi_mk, lemma102_conjQ_mk, k148f_psi_mk, hinv, lemma102_conjQ_mk]
  rfl

theorem k148f_barX_inf {K I' : Subgroup G} {y : G} (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hyI' : y ∈ Subgroup.normalizer (I' : Set G)) (hy3 : y ^ 3 = 1) (hI'K : I' ≤ K)
    (hS : IsSimpleGroup ↥(barX 3 K I')) (h3 : 3 ∣ Nat.card ↥(barX 3 K I'))
    {c : PQuot 3 K} (hc : MulAut.conj c = CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩) :
    barX 3 K (I' ⊓ Subgroup.centralizer ({y} : Set G)) =
      barX 3 K I' ⊓ Subgroup.centralizer ({c} : Set (PQuot 3 K)) := by
  have hker := k148f_hker hI'K hS h3
  have hfix_of_comm : ∀ e : ↥K, (e : G) * y = y * (e : G) →
      CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩ (QuotientGroup.mk e) = QuotientGroup.mk e := by
    intro e he
    have hconj : lemma102_conjQ 3 hyN (QuotientGroup.mk e) = QuotientGroup.mk e := by
      rw [lemma102_conjQ_mk]
      congr 1
      apply Subtype.ext
      show y⁻¹ * (e : G) * y = (e : G)
      rw [mul_assoc, he]
      group
    have := barAut_comp_conjQ hyN (QuotientGroup.mk e)
    rw [hconj] at this
    exact this
  ext u
  constructor
  · intro hu
    obtain ⟨e, he, rfl⟩ := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns.mem_barX_iff' 3 K _ _).1 hu
    obtain ⟨heI, heC⟩ := Subgroup.mem_inf.1 he
    have hCy : (e : G) * y = y * (e : G) := Subgroup.mem_centralizer_singleton_iff.1 heC
    refine Subgroup.mem_inf.2 ⟨(CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns.mem_barX_iff' 3 K I' _).2
      ⟨e, heI, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcu : MulAut.conj c (QuotientGroup.mk e) = QuotientGroup.mk e := by
      rw [hc]
      exact hfix_of_comm e hCy
    have hcu' : c * QuotientGroup.mk e * c⁻¹ = QuotientGroup.mk e := by
      simpa [MulAut.conj_apply] using hcu
    exact (mul_inv_eq_iff_eq_mul.1 hcu').symm
  · intro hu
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
    obtain ⟨e, heI, hmk⟩ := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns.mem_barX_iff' 3 K I' _).1 hu1
    have hu2' : u * c = c * u := Subgroup.mem_centralizer_singleton_iff.1 hu2
    let x₀ : ↥I' := ⟨(e : G), heI⟩
    have hψx₀ : ((k148f_psi hI'K hker (QuotientGroup.mk x₀) : ↥(barX 3 K I')) : PQuot 3 K) = u := by
      rw [k148f_psi_mk]
      exact hmk
    have hfixz : lemma102_conjQ 3 hyI' (QuotientGroup.mk x₀) = QuotientGroup.mk x₀ := by
      apply (k148f_psi hI'K hker).injective
      apply Subtype.ext
      rw [k148f_psi_nat hyN hyI' hI'K hker hc (QuotientGroup.mk x₀), hψx₀]
      have hinv : (MulAut.conj c)⁻¹ u = c⁻¹ * u * c := by
        rfl
      rw [hinv]
      calc c⁻¹ * u * c = c⁻¹ * (u * c) := by group
        _ = c⁻¹ * (c * u) := by rw [hu2']
        _ = u := by group
    obtain ⟨w, hwz, hyw⟩ := CFSG.LocalAnalysis.GLTheoremA.k148_fix_lift hyI' hy3 _ hfixz
    refine (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns.mem_barX_iff' 3 K _ _).2
      ⟨Subgroup.inclusion hI'K w, Subgroup.mem_inf.2 ⟨w.2, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hyw.symm
    · have hw : ((k148f_psi hI'K hker (QuotientGroup.mk w) : ↥(barX 3 K I')) : PQuot 3 K) = u := by
        rw [hwz, hψx₀]
      rw [k148f_psi_mk] at hw
      exact hw

end CFSG.LocalAnalysis.GLTheoremA.K148F

end
