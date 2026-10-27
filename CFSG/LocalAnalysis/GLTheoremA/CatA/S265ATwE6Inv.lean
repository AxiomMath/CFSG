module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcDataTw
public import CFSG.LocalAnalysis.StandardType.GGTwE6FixedInv
import CFSG.LocalAnalysis.GLTheoremA.S9.L94Transport
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiag
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.StandardType (ggMulAut_conj_inn_outdiag ggLabelRigidInput_holds)
open CFSG.StandardType.TwE6Delta (RecipeR RecipeI ggOutdiagOdd_twE6 finite_mulAut_recipeR
  center_recipeR_eq_bot)
open CFSG.StandardType.TwE6NormThree (exists_fixed_involution_twE6)

private theorem congr_chevAut_eq_of_induces {Ω : Type} [Group Ω] {S : Subgroup Ω} {R : Type}
    [Group R] (θ : PSimple 3 S ≃* R) {b : Ω} (hb : b ∈ Subgroup.normalizer (S : Set Ω))
    {φ : MulAut R} (hind : GLAInduces θ (S10.indRel 3 S b⁻¹) φ) :
    MulAut.congr θ (chevAut 3 S ⟨b, hb⟩) = φ := by
  ext r
  obtain ⟨s, rfl⟩ := θ.surjective r
  obtain ⟨k, rfl⟩ := chevQuotHom_surjective 3 S s
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    chevAut_chevQuotHom]
  exact (hind (QuotientGroup.mk k) (QuotientGroup.mk (S.normalizerMonoidHom ⟨b, hb⟩ k))
    ⟨k, S.normalizerMonoidHom ⟨b, hb⟩ k, rfl, rfl,
      by rw [chev_coe_normalizerMonoidHom, inv_inv]⟩).symm

private theorem isPGroup_two_le_of_odd_relIndex {G : Type*} [Group G] {N D Q : Subgroup G}
    [N.Normal] (hQD : Q ≤ D) (hQ : IsPGroup 2 Q) (hodd : Odd (N.relIndex D)) : Q ≤ N := by
  intro g hg
  obtain ⟨k, hk⟩ := hQ ⟨g, hg⟩
  have hg1 : (⟨g, hQD hg⟩ : D) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  set x := QuotientGroup.mk' (N.subgroupOf D) ⟨g, hQD hg⟩ with hx
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by rw [hx, ← map_pow, hg1, map_one])
  have h2 : orderOf x ∣ N.relIndex D := by
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard x
  have h3 := Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_right.2 hodd).pow_right k) h2 h1
  rwa [orderOf_eq_one_iff, hx, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h3


private theorem exists_twE6Recipe_of_innDiagOn {Ω : Type} [Group Ω] {S B : Subgroup Ω}
    (hinn : S10.InnDiagOn 3 B S) (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.card = 2)
    (hSd : Nonempty (PSimple 3 S ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (θ : PSimple 3 S ≃* RecipeR K 1),
      Nat.card K = (2 ^ 1) ^ 2 ∧ ∀ b ∈ B, ∀ hb : b ∈ Subgroup.normalizer (S : Set Ω),
        MulAut.congr θ (chevAut 3 S ⟨b, hb⟩) ∈ RecipeI K 1 := by
  obtain ⟨-, hperf, ⟨t, l, n⟩, hlam, hraw⟩ := hinn
  obtain ⟨d, hv⟩ := d
  obtain ⟨q, hdq, hq2⟩ := hd
  dsimp only at hdq
  subst hdq
  obtain ⟨e⟩ := hSd
  have hp2 : q.p = 2 :=
    ((Nat.Prime.pow_eq_iff Nat.prime_two).1 ((TauCeti.PrimePower.card_def q).symm.trans hq2)).1
  have hlab : Y10F.HasLabel (PQuot 3 S) (· = ⟨t, l, n⟩) :=
    ⟨hperf, ⟨t, l, n⟩, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have ht : t = .twE6 := K155X.excTwE6_tag_of_marking hlab ⟨.lie ⟨_, hv⟩, hp2, ⟨e⟩⟩
  subst ht
  have hn : n = 1 := Nat.pow_right_injective le_rfl
    ((CanonSubcomp.two_pow_canonLabel_n_of_lie ggLabelRigidInput_holds hlab ⟨_, hv⟩
      ((TauCeti.LieTypeIndex.characteristic_twistedE6 q).trans hp2) e).trans
      (hq2.trans (pow_one (2 : ℕ)).symm))
  subst hn
  obtain ⟨K, instF, instFin, hK, -, -, θ, hall⟩ := hraw
  refine ⟨K, instF, instFin, θ, hK, fun b hb hbN => ?_⟩
  obtain ⟨φ, hφ, hind⟩ := hall b⁻¹ (B.inv_mem hb)
  rw [congr_chevAut_eq_of_induces θ hbN hind]
  exact hφ

theorem exists_fixed_involution_of_twE6 {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω}
    (hS : S.Normal) (hinn : S10.InnDiagOn 3 B S) (hB : IsElemAbelian 3 B)
    (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.card = 2)
    (hSd : Nonempty (PSimple 3 S ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hX4 : 3 ^ 4 ≤ Nat.card ((B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut 3 S)))
    (hT : IsPGroup 2 T) (hBT : B ≤ Subgroup.normalizer (T : Set Ω))
    (hU : ∃ u ∈ (⁅T, B⁆ : Subgroup Ω), ∃ hu : u ∈ Subgroup.normalizer (S : Set Ω),
      chevAut 3 S ⟨u, hu⟩ ≠ 1) :
    ∃ v : PSimple 3 S, v * v = 1 ∧ v ≠ 1 ∧
      ∀ b ∈ B, ∀ hb : b ∈ Subgroup.normalizer (S : Set Ω), chevAut 3 S ⟨b, hb⟩ v = v := by
  obtain ⟨K, _, _, θ, hK, hI⟩ := exists_twE6Recipe_of_innDiagOn hinn d hd hSd
  haveI := finite_mulAut_recipeR hK
  have hN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 hS]
    exact Subgroup.mem_top g
  let ψ : Ω →* MulAut (RecipeR K 1) := (MulAut.congr θ).toMonoidHom.comp
    ((chevAut 3 S).comp ((MonoidHom.id Ω).codRestrict _ hN))
  have hψ : ∀ g (hg : g ∈ Subgroup.normalizer (S : Set Ω)),
      ψ g = MulAut.congr θ (chevAut 3 S ⟨g, hg⟩) := fun _ _ => rfl
  have hXI : ((B.map ψ : Subgroup _) : Set (MulAut (RecipeR K 1))) ⊆ RecipeI K 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [hψ b (hN b)]
    exact hI b hb (hN b)
  have hX4' : 3 ^ 4 ≤ Nat.card (B.map ψ) := by
    refine hX4.trans ((Subgroup.card_map_of_injective (f := (MulAut.congr θ).toMonoidHom)
      (MulAut.congr θ).injective).symm.le.trans (Subgroup.card_le_of_le ?_))
    rintro _ ⟨_, ⟨⟨b, hbN⟩, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, hψ b hbN⟩
  obtain ⟨-, hTB2, hBTB, -⟩ := S9.l94t_commutator_facts hB hT hBT
  obtain ⟨D, hDn, hID, hodd⟩ := ggOutdiagOdd_twE6 (n := 1) le_rfl hK 3
  have hbD : ∀ b ∈ B, ψ b ∈ D := fun b hb =>
    hID _ (hXI (Subgroup.mem_map_of_mem ψ hb)) (by rw [← map_pow, hB.2 b hb, map_one])
  have hQD : (⁅T, B⁆ : Subgroup Ω).map ψ ≤ D := by
    refine Subgroup.map_le_iff_le_comap.2 (Subgroup.commutator_le.2 fun t _ b hb => ?_)
    rw [Subgroup.mem_comap, map_commutatorElement, commutatorElement_def]
    exact D.mul_mem (hDn.conj_mem _ (hbD b hb) _) (D.inv_mem (hbD b hb))
  haveI : (MulAut.conj : RecipeR K 1 →* MulAut (RecipeR K 1)).range.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨r, rfl⟩ α
    exact ⟨α r, (ggMulAut_conj_inn_outdiag α r).symm⟩
  have hQI := isPGroup_two_le_of_odd_relIndex hQD (hTB2.map ψ) hodd
  have hinj : Function.Injective (MulAut.conj : RecipeR K 1 →* MulAut (RecipeR K 1)) := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have hrZ : r ∈ Subgroup.center (RecipeR K 1) := Subgroup.mem_center_iff.2 fun g => by
      have h1 := congrArg (fun f : MulAut (RecipeR K 1) => f g) hr
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * r = r * g * r⁻¹ * r := by rw [h1]
        _ = r * g := inv_mul_cancel_right _ _
    rwa [center_recipeR_eq_bot le_rfl hK, Subgroup.mem_bot] at hrZ
  obtain ⟨u, huTB, hu, hu1⟩ := hU
  obtain ⟨r, hr⟩ := hQI (Subgroup.mem_map_of_mem ψ huTB)
  have hU1 : ((⁅T, B⁆ : Subgroup Ω).map ψ).comap MulAut.conj ≠ ⊥ := by
    intro hbot
    have hrU : r ∈ ((⁅T, B⁆ : Subgroup Ω).map ψ).comap MulAut.conj := ⟨u, huTB, hr.symm⟩
    rw [hbot, Subgroup.mem_bot] at hrU
    rw [hrU, map_one, hψ u hu] at hr
    exact hu1 ((MulAut.congr θ).map_eq_one_iff.1 hr.symm)
  have hUX : ∀ φ ∈ B.map ψ, ∀ v ∈ ((⁅T, B⁆ : Subgroup Ω).map ψ).comap MulAut.conj,
      φ v ∈ ((⁅T, B⁆ : Subgroup Ω).map ψ).comap MulAut.conj := by
    rintro _ ⟨b, hb, rfl⟩ v ⟨c, hc, hcv⟩
    refine ⟨b * c * b⁻¹, (Subgroup.mem_normalizer_iff.1 (hBTB hb) c).1 hc, ?_⟩
    rw [map_mul, map_mul, map_inv, hcv, ggMulAut_conj_inn_outdiag]
  obtain ⟨w, hw2, hw1, hfix⟩ := exists_fixed_involution_twE6 (n := 1) le_rfl hK (by norm_num)
    (S9.l94t_isElemAbelian_map ψ hB) hXI hX4'
    ⟨_, hU1, (hTB2.map ψ).comap_of_injective _ hinj, hUX⟩
  refine ⟨θ.symm w, by rw [← map_mul, hw2, map_one], θ.symm.map_ne_one_iff.2 hw1,
    fun b hb hbN => ?_⟩
  have h := congrArg θ.symm (hfix _ (Subgroup.mem_map_of_mem ψ hb))
  rwa [hψ b hbN, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
