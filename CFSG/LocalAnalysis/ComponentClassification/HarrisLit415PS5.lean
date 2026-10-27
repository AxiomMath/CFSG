module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PS4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL3U3Inputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem le_layerIn_of_balance {X : Type} [Group X] [Finite X] {a b : X}
    (hab : a ∈ centralizer ({b} : Set X)) (ha : orderOf a = 2)
    (hSch : LBalance.SchreierSections ↥(centralizer ({b} : Set X))) {J : Subgroup X}
    (hJ : IsTwoComponentIn J (centralizer {a} ⊓ centralizer {b})) :
    J ≤ GSThmB.layerIn (centralizer {b}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := centralizer ({b} : Set X)
  let a' : ↥H := ⟨a, hab⟩
  have hCX : (centralizer ({a'} : Set ↥H)).map H.subtype = centralizer {a} ⊓ centralizer {b} :=
    map_subtype_centralizer hab
  let eC : ↥(centralizer ({a'} : Set ↥H)) ≃* ↥(centralizer ({a} : Set X) ⊓ centralizer {b}) :=
    ((centralizer ({a'} : Set ↥H)).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hCX)
  have hJ' : IsPComponent 2 ((J.subgroupOf (centralizer {a} ⊓ centralizer {b})).map
      eC.symm.toMonoidHom) :=
    isPComponent_map_mulEquiv eC.symm ((isTwoComponentIn_iff hJ.1).mp hJ)
  have ha2 : ∃ n : ℕ, a' ^ 2 ^ n = 1 := ⟨1, Subtype.ext (by
    change a ^ 2 ^ 1 = 1
    rw [pow_one, ← ha, pow_orderOf_eq_one])⟩
  have hbal := LBalance.pLayer_centralizer_element_le hSch ha2
  intro x hx
  set y := eC.symm ⟨x, hJ.1 hx⟩ with hy
  have hyJ : y ∈ (J.subgroupOf (centralizer {a} ⊓ centralizer {b})).map eC.symm.toMonoidHom :=
    ⟨⟨x, hJ.1 hx⟩, hx, rfl⟩
  have hyL : (y : ↥H) ∈ pLayer ↥H 2 :=
    hbal ⟨y, (le_sSup (s := {L : Subgroup ↥(centralizer ({a'} : Set ↥H)) | IsPComponent 2 L})
      hJ' : _ ≤ pLayer ↥(centralizer ({a'} : Set ↥H)) 2) hyJ, rfl⟩
  have hyx : ((y : ↥H) : X) = x := by
    have h1 := congrArg Subtype.val (MulEquiv.apply_symm_apply eC ⟨x, hJ.1 hx⟩)
    rw [← hy] at h1
    exact h1
  exact ⟨y, hyL, hyx⟩

end L415

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem seven_le_r : 7 ≤ p ^ (f / 2) := by
  have h16 := hD.hs.sixteen_dvd
  have hp := hD.hs.prime_p
  have hp2 := hD.hs.p_ne_two
  have hm := hD.hs.one_le_half
  rw [pow_mul] at h16
  have h3 : 3 ≤ p ^ (f / 2) :=
    (Nat.lt_of_le_of_ne hp.two_le (Ne.symm hp2)).trans_le (Nat.le_self_pow (by omega) p)
  have hodd : Odd (p ^ (f / 2)) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  by_contra hlt
  push Not at hlt
  rw [show (p ^ 2) ^ (f / 2) = (p ^ (f / 2)) ^ 2 by ring] at h16
  generalize p ^ (f / 2) = r at h3 hodd hlt h16
  interval_cases r <;> simp_all

theorem not_L3U3 [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hL3 : EndB.L3U3InvolutionSL2Fact)
    (hM : IsComponent (layer (MBar z₁))) (hEs : IsSimpleGroup ↥(layer (MBar z₁)))
    (hlt : barOf (centralizer {z₁}) K₂ < layer (MBar z₁))
    (hY : Blueprint.LieModel ↥(layer (MBar z₁)) .PSL 3 p (f / 2) ∨
      Blueprint.LieModel ↥(layer (MBar z₁)) .PSU 3 p (f / 2)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEn : (layer (MBar z₁)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar z₁)
    infer_instance
  have hz₂E : (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ : MBar z₁) ∈ layer (MBar z₁) :=
    hlt.le hD.z₂F_mem
  obtain ⟨Y, hYle, hYsub, hYsl, hzY⟩ := hL3 (MBar z₁) (layer (MBar z₁)) p (f / 2)
    hD.hs.prime_p hD.hs.p_ne_two hD.hs.one_le_half hY _ hz₂E hD.orderOf_z₂F
  obtain ⟨hYq, -, -, hYO⟩ := Lemma47.sl2_facts hD.hs.prime_p hD.hs.p_ne_two hD.hs.one_le_half
    (by have := hD.seven_le_r; omega) hYsl
  have hYq2 : IsTwoQuasisimple ↥Y := ⟨hYq.1, LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hYO.symm)) hYq⟩
  have hYp := (isTwoComponentIn_iff hYle).mp ⟨hYle, hYsub, hYq2⟩
  have hYp' := UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal hYle inf_le_right
    (by rw [inf_subgroupOf_right]; exact Subgroup.Normal.isSubnormal inferInstance) hYp
  have hz₂o : orderOf (t * z₁ * t⁻¹) = 2 := by
    refine orderOf_eq_prime ?_ hD.z₂_ne_one
    rw [sq, show t * z₁ * t⁻¹ * (t * z₁ * t⁻¹) = t * (z₁ * z₁) * t⁻¹ by group, hD.z₁_mul_z₁]
    group
  obtain ⟨J, hJle, hJp, hz₂J, -, -⟩ := Lemma47.exists_lift_two_component hD.z₂_mem_F hz₂o
    (hYle.trans inf_le_right) hYp' hzY
  have hJc : IsTwoComponentIn J (centralizer {z₁} ⊓ centralizer {t * z₁ * t⁻¹}) :=
    (isTwoComponentIn_iff hJle).mpr hJp
  have htt : t * (t * z₁ * t⁻¹) * t⁻¹ = z₁ := by
    rw [show t * (t * z₁ * t⁻¹) * t⁻¹ = (t * t) * z₁ * (t * t)⁻¹ by group, hD.t_mul_t]
    group
  have hCC : (centralizer {z₁} ⊓ centralizer {t * z₁ * t⁻¹}).map (MulAut.conj t).toMonoidHom =
      centralizer {t * z₁ * t⁻¹} ⊓ centralizer {z₁} := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, L415.map_conj_centralizer,
      L415.map_conj_centralizer, htt]
  have hJt := L415.isTwoComponentIn_map_mulEquiv (MulAut.conj t) hJc
  rw [hCC] at hJt
  have hz₁J : z₁ ∈ J.map (MulAut.conj t).toMonoidHom := ⟨_, hz₂J, htt⟩
  have hKF := UnbalancedCorr.isKGroupCat_of_ne_top hK (hD.centralizer_z₁_ne_top hnab)
  have hSchF := GSThmB.schreierSections_of_isKGroupCat hSch hKF
  have hz₁L := L415.le_layerIn_of_balance hD.z₂_mem_F hz₂o hSchF hJt hz₁J
  obtain ⟨y, hyL, hyz⟩ := hz₁L
  have hπ := UnbalancingLocal.Correspondence.map_pLayer_of_coprime_kernel (p := 2)
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z₁} : Set X))))
    (QuotientGroup.mk'_surjective _) GSThmB.OddQuot.not_two_dvd_card_ker
  rw [ClassicalInvolution.LBalanceProof.pLayer_eq_layer_of_pPrimeCore_eq_bot
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2)] at hπ
  have hz₁E : betaBar z₁ ∈ layer (MBar z₁) := by
    rw [← hπ]
    refine ⟨y, hyL, ?_⟩
    change (QuotientGroup.mk y : MBar z₁) = QuotientGroup.mk ⟨z₁, _⟩
    congr 1
    exact Subtype.ext hyz
  have hq : IsQuasisimple ↥(layer (MBar z₁)) := hM.1
  have hEnab : ∃ a b : ↥(layer (MBar z₁)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hZ : center ↥(layer (MBar z₁)) = ⊥ := (LocalCores.isQuasisimple_of_isSimpleGroup hEnab).2
  have hcen : (⟨betaBar z₁, hz₁E⟩ : ↥(layer (MBar z₁))) ∈ center ↥(layer (MBar z₁)) := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp (betaBar_mem_center z₁) g)
  rw [hZ, mem_bot] at hcen
  have h1 := hD.orderOf_z₁F
  rw [show betaBar z₁ = 1 from congrArg Subtype.val hcen, orderOf_one] at h1
  norm_num at h1

end Data415B

end CFSG.ComponentClassification.HarrisLit
