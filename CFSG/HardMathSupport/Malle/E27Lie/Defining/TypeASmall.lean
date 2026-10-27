module

public import CFSG.Quasithin.Background.F6CatRecogOut
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.HardMathSupport.Foote.E27.LocalBound
public import CFSG.HardMathSupport.Foote.E27.Split
public import CFSG.Adapters.LinearCatalog
public import CFSG.HardMathSupport.Malle.E27Lie.Defining.Unitriangular
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 CFSG.LocalAnalysis.ComponentInitial TauCeti Matrix

theorem false_of_typeA_L2_27 {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (q : PrimePower) (hv : (LieTypeIndex.A 1 q).Valid) (hp : q.p = 3)
    (hf : q.exponent = 3) (e : ↥K ≃* (CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) : False := by
  have := h.normal
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := GaloisField q.p q.exponent
  have hFc : Nat.card F = 3 ^ 3 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hp, hf]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h5 := three_pow_five_dvd_card_mulAut K h.faithful R T z h.elem h.card_R h.T_le_R h.card_T
    h.z_mem h.z_not_mem h.fus h.sylow h.central h.dvd81
  let ψ : ↥K ≃* CFSG.GorensteinWalter.PSL2 F :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨3, 3, Nat.prime_three, by decide, by norm_num, hFc⟩
  have hAut := CFSG.Quasithin.F6.card_mulAut_psl2 F (p := 3) (f := 3) hFc hodd
    (by rw [hFc]; norm_num)
  have hPGL := CFSG.GorensteinWalter.pgl2_card_formula F
  have hRing := (card_ringAut_and_isCyclic Nat.prime_three F hFc).1
  have hcard : Nat.card (MulAut ↥K) = 27 * (27 ^ 2 - 1) * 3 := by
    rw [Nat.card_congr (MulAut.congr ψ).toEquiv, hAut, hPGL, hFc]
    rw [show Nat.card (F ≃+* F) = Nat.card (RingAut F) from rfl, hRing]
    norm_num
  rw [hcard] at h5
  norm_num at h5

theorem false_of_typeA_L3_3 {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (q : PrimePower) (hv : (LieTypeIndex.A 2 q).Valid)
    (hp : q.p = 3) (hf : q.exponent = 1) (e : ↥K ≃* (CFSGIndex.lie ⟨.A 2 q, hv⟩).Group) :
    False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := GaloisField q.p q.exponent
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFc : Nat.card F = 3 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hp, hf, pow_one]
  have : CharP F 3 := hp ▸ (inferInstance : CharP F q.p)
  let ψ : ↥K ≃* LinearFlag.projectiveSL 3 F :=
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_projUnitriangular (K := F) 3 (n := 3) (by norm_num)
  have hPcard : Nat.card (P : Subgroup (LinearFlag.projectiveSL 3 F)) = 27 := by
    rw [hP, LinearFlag.card_projUnitriangular, hFc]
    norm_num
  have hRK : R ≤ K := h.le_of_mem hz
  set R' : Subgroup (LinearFlag.projectiveSL 3 F) := (R.subgroupOf K).map ψ.toMonoidHom
  have hR'card : Nat.card R' = 27 := by
    rw [Subgroup.card_map_of_injective ψ.injective, ← h.card_R]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv
  let S' : Sylow 3 (LinearFlag.projectiveSL 3 F) :=
    Sylow.ofCard R' (by rw [hR'card, ← hPcard, P.card_eq_multiplicity])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (LinearFlag.projectiveSL 3 F) S' P
  have hR'ab : ∀ a ∈ R', ∀ b ∈ R', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have hc := congrArg (Subtype.val : R → X) (h.elem.1.is_comm.comm (⟨a, ha⟩ : R) ⟨b, hb⟩)
    exact Subtype.ext hc
  have hPab : ∀ a ∈ (P : Subgroup (LinearFlag.projectiveSL 3 F)),
      ∀ b ∈ (P : Subgroup (LinearFlag.projectiveSL 3 F)), a * b = b * a := by
    intro a ha b hb
    have hPeq : (P : Subgroup (LinearFlag.projectiveSL 3 F)) =
        ((g • S' : Sylow 3 (LinearFlag.projectiveSL 3 F)) : Subgroup _) := by rw [hg]
    rw [hPeq, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    simp only [MulAut.smul_def, MulAut.conj_apply]
    have := hR'ab a' ha' b' hb'
    calc g * a' * g⁻¹ * (g * b' * g⁻¹) = g * (a' * b') * g⁻¹ := by group
      _ = g * (b' * a') * g⁻¹ := by rw [this]
      _ = g * b' * g⁻¹ * (g * a' * g⁻¹) := by group
  have h01 : (⟨0, by norm_num⟩ : Fin 3) < ⟨1, by norm_num⟩ := by decide
  have h12 : (⟨1, by norm_num⟩ : Fin 3) < ⟨2, by norm_num⟩ := by decide
  set a := ofStrict (single (⟨0, by norm_num⟩ : Fin 3) ⟨1, by norm_num⟩ (1 : F))
    (strict_single h01 1)
  set b := ofStrict (single (⟨1, by norm_num⟩ : Fin 3) ⟨2, by norm_num⟩ (1 : F))
    (strict_single h12 1)
  have ha : LinearFlag.proj 3 F a ∈ (P : Subgroup (LinearFlag.projectiveSL 3 F)) :=
    hP ▸ ⟨a, ofStrict_mem _ _, rfl⟩
  have hb : LinearFlag.proj 3 F b ∈ (P : Subgroup (LinearFlag.projectiveSL 3 F)) :=
    hP ▸ ⟨b, ofStrict_mem _ _, rfl⟩
  have hab := hPab _ ha _ hb
  rw [← map_mul, ← map_mul] at hab
  have hU : a * b = b * a := LinearFlag.proj_injOn_unitriangular 3
    ((LinearFlag.unitriangular 3 F).mul_mem (ofStrict_mem _ _) (ofStrict_mem _ _))
    ((LinearFlag.unitriangular 3 F).mul_mem (ofStrict_mem _ _) (ofStrict_mem _ _)) hab
  have h02 := congrArg (fun g : SpecialLinearGroup (Fin 3) F =>
    (g : Matrix (Fin 3) (Fin 3) F) ⟨0, by norm_num⟩ ⟨2, by norm_num⟩) hU
  simp [a, b, coe_ofStrict, Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply,
    Matrix.one_apply, single_apply] at h02

end CFSG.HardMathSupport.Malle.E27Lie
