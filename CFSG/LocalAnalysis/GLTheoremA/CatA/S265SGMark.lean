module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGPin
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGEnd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup PerfectInLayer)

theorem SG.exists_rawDatum_chevAut {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSNL p S B T x D K) {lab : GLALabel}
    (hlab : InnLabelOf B S lab) :
    GLARawDatum lab fun R _ I _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ Φ : PSimple p S ≃* R, ∀ (b : Ω) (hbN : b ∈ Subgroup.normalizer (S : Set Ω)), b ∈ B →
        MulAut.congr Φ (chevAut p S ⟨b, hbN⟩) ∈ I := by
  obtain ⟨-, lab', -, hraw⟩ := hlab
  obtain ⟨_, _, _, _, _, _, _, rfl, _⟩ := rk2_rawDatum_exists hraw
  let ι : ↥S ⧸ Subgroup.center ↥S ≃* PSimple p S := (QuotientGroup.quotientMulEquivOfEq
    (S171.ker_chevQuotHom_eq_center' h.cfg.prime h.cfg.comp h.cfg.quasi).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (chevQuotHom_surjective p S))
  refine rk2_rawDatum_mono (fun R _ I F ⟨hs, hna, θ, _, _, hind⟩ =>
    ⟨hs, hna, ι.symm.trans θ, fun b hbN hb => ?_⟩) hraw
  obtain ⟨φ, hφI, hφ⟩ := hind b⁻¹ (inv_mem hb)
  have hΦ : ∀ l : ↥S, (ι.symm.trans θ) (chevQuotHom p S l) = θ (QuotientGroup.mk l) :=
    fun l => congrArg θ ((MulEquiv.symm_apply_eq ι).2 rfl)
  have heq : MulAut.congr (ι.symm.trans θ) (chevAut p S ⟨b, hbN⟩) = φ := by
    ext r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hφ l (S.normalizerMonoidHom ⟨b, hbN⟩ l) (by rw [inv_inv]; rfl), ← hΦ, ← hΦ,
      ← chevAut_chevQuotHom]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
      MulEquiv.symm_symm, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  rw [heq]
  exact hφI

theorem SG.chevAut_eq_one_iff_mem_zpowers {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSNL p S B T x D K) {b : Ω} (hb : b ∈ B)
    (hbN : b ∈ Subgroup.normalizer (S : Set Ω)) :
    chevAut p S ⟨b, hbN⟩ = 1 ↔ b ∈ Subgroup.zpowers x :=
  (chevAut_eq_one_iff h.cfg.prime h.cfg.comp hbN).trans (h.cfg.centB b hb)

theorem SG.card_map_chevAut {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω}
    {x : Ω} {D K : Subgroup Ω} (h : QSNL p S B T x D K) (hB : Nat.card B = p ^ 4) :
    IsElemAbelian p ((B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut p S)) ∧
      Nat.card ((B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut p S)) = p ^ 3 := by
  have hc := h.cfg
  haveI := Fact.mk hc.prime
  have hSN : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ =>
    (Subgroup.normalizer_eq_top_iff.2 hc.normal) ▸ Subgroup.mem_top g
  refine ⟨(hc.elem.subgroupOf _).map _, ?_⟩
  set φ : ↥B →* MulAut (PSimple p S) := (chevAut p S).comp (Subgroup.inclusion hSN) with hφ
  have hrange : φ.range = (B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut p S) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : φ.ker = (Subgroup.zpowers x).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact SG.chevAut_eq_one_iff_mem_zpowers h b.2 (hSN b.2)
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (Subgroup.zpowers_le.2 hc.xB)).toEquiv, Nat.card_zpowers,
    orderOf_eq_prime (hc.elem.2 x hc.xB) hc.x1, hB, pow_succ' p 3] at hmul
  exact Nat.eq_of_mul_eq_mul_left hc.prime.pos hmul

theorem SG.exists_mem_D_not_zpowers {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSNL p S B T x D K) :
    ∃ d ∈ D, d ∉ Subgroup.zpowers x := by
  have hc := h.cfg
  haveI := Fact.mk hc.prime
  obtain ⟨-, -, hD, -⟩ := hc.std
  by_contra! hcon
  have hle := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers x from hcon)
  rw [hD, Nat.card_zpowers, orderOf_eq_prime (hc.elem.2 x hc.xB) hc.x1] at hle
  nlinarith [hc.prime.two_le]

private theorem map_symm_le_fixSubgroup {R R' : Type} [Group R] [Group R'] (Ψ : R ≃* R')
    {β : MulAut R} {A : Subgroup R'} (hA : A ≤ fixSubgroup (MulAut.congr Ψ β)) :
    A.map Ψ.symm.toMonoidHom ≤ fixSubgroup β := by
  rintro _ ⟨a, ha, rfl⟩
  exact Ψ.eq_symm_apply.2 (hA ha)

theorem SG.false_of_simple_fix_congr {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω}
    {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hcat : catalogIs (PSimple 3 K) (tyF 3))
    (hB : Nat.card B = 3 ^ 4) {R : Type} [Group R] (Ψ : PSimple 3 S ≃* R) {d : Ω} (hdD : d ∈ D)
    (hdx : d ∉ Subgroup.zpowers x) (hdN : d ∈ Subgroup.normalizer (S : Set Ω))
    (hpl : PerfectInLayer (MulAut.congr Ψ (chevAut 3 S ⟨d, hdN⟩))) {A : Subgroup R}
    [IsSimpleGroup ↥A] (hnc : ∃ a b : ↥A, a * b ≠ b * a) (h3 : 3 ∣ Nat.card ↥A)
    (hAd : A ≤ fixSubgroup (MulAut.congr Ψ (chevAut 3 S ⟨d, hdN⟩))) {Y : Subgroup (MulAut R)}
    (hY : Y.relIndex (((B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut 3 S)).map
      (MulAut.congr Ψ).toMonoidHom) ≤ 3) (hYA : ∀ ε ∈ Y, A ≤ fixSubgroup ε) : False := by
  set e := Subgroup.equivMapOfInjective A Ψ.symm.toMonoidHom Ψ.symm.injective
  haveI : IsSimpleGroup ↥(A.map Ψ.symm.toMonoidHom) := e.symm.isSimpleGroup
  have hnc' : ∃ a b : ↥(A.map Ψ.symm.toMonoidHom), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩
  refine SG.false_of_simple_fix_relIndex h hcat hB hdN (SG.glaLayer_fixSubgroup_chevAut h hdD hdx
    hdN) (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_of_congr Ψ _ hpl)
    (A := A.map Ψ.symm.toMonoidHom) (map_symm_le_fixSubgroup Ψ hAd) hnc'
    ((Nat.card_congr e.toEquiv) ▸ h3) (Y := Y.comap (MulAut.congr Ψ).toMonoidHom)
    (by rwa [Subgroup.relIndex_comap]) fun ε hε => map_symm_le_fixSubgroup Ψ (hYA _ hε)

end CFSG.LocalAnalysis.GLTheoremA.S265

end
