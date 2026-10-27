module

import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5FusionTwoAction
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

theorem closureIn_eq_of_quot {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω]
    {S B N K : Subgroup Ω} {x : Ω} (hSn : S.Normal) (hqs : CFSG.Open.IsQuasisimple ↥S)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) (hB : IsElemAbelian p B)
    (hBx : B = Subgroup.zpowers x ⊔ B ⊓ S) (hxC : x ∈ Subgroup.centralizer (S : Set Ω))
    (hN : N = Subgroup.normalizer (B : Set Ω) ⊓ Subgroup.centralizer ({x} : Set Ω))
    (hKS : K ≤ S)
    (htop : (⨆ g ∈ Subgroup.normalizer
        (modCentreImage S B : Set (↥S ⧸ Subgroup.center ↥S)),
        (modCentreImage S K).map (MulAut.conj g).toMonoidHom) = ⊤) :
    closureIn K N = S := by
  classical
  let Q := ↥S ⧸ Subgroup.center ↥S
  let mk : ↥S →* Q := QuotientGroup.mk' (Subgroup.center ↥S)
  have hH_le_S : closureIn K N ≤ S := by
    refine iSup₂_le fun a _ => ?_
    rintro _ ⟨k, hk, rfl⟩
    exact hSn.conj_mem k (hKS hk) a
  have hxB : x ∈ B := by
    rw [hBx]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hxBle : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.mpr hxB
  have hconjB : ∀ (a : ↥S), mk a ∈ Subgroup.normalizer (modCentreImage S B : Set Q) →
      ∀ b : Ω, b ∈ B → (a : Ω) * b * (a : Ω)⁻¹ ∈ B := by
    intro a haN b hb
    haveI : IsMulCommutative ↥B := hB.1
    have hBsup : (Subgroup.zpowers x).subgroupOf B ⊔ (B ⊓ S).subgroupOf B = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hxBle inf_le_left, ← hBx, Subgroup.subgroupOf_self]
    have hbB : (⟨b, hb⟩ : ↥B) ∈ (⊤ : Subgroup ↥B) := Subgroup.mem_top _
    rw [← hBsup] at hbB
    obtain ⟨u, hu, v, hv, huv⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := (Subgroup.zpowers x).subgroupOf B)
        (t := (B ⊓ S).subgroupOf B)).1 hbB
    have hu' : (u : Ω) ∈ Subgroup.zpowers x := Subgroup.mem_subgroupOf.mp hu
    have hv' : (v : Ω) ∈ B ⊓ S := Subgroup.mem_subgroupOf.mp hv
    have huv' : (u : Ω) * (v : Ω) = b := by
      have := congrArg Subtype.val huv
      simpa using this
    have huB : (u : Ω) ∈ B := hxBle hu'
    have hvB : (v : Ω) ∈ B := hv'.1
    have hvS : (v : Ω) ∈ S := hv'.2
    have hu : (u : Ω) ∈ Subgroup.zpowers x := hu'
    have hv : (v : Ω) ∈ B ⊓ S := hv'
    have huv : (u : Ω) * (v : Ω) = b := huv'
    have hxcomm : (a : Ω) * x = x * (a : Ω) :=
      Subgroup.mem_centralizer_iff.mp hxC (a : Ω) a.2
    have hxcent : x ∈ Subgroup.centralizer ({(a : Ω)} : Set Ω) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hxcomm
    have hu_le : (u : Ω) ∈ Subgroup.centralizer ({(a : Ω)} : Set Ω) :=
      (Subgroup.zpowers_le.mpr hxcent) hu'
    have hucomm : (u : Ω) * (a : Ω) = (a : Ω) * (u : Ω) :=
      (Subgroup.mem_centralizer_iff.mp hu_le (a : Ω) (Set.mem_singleton _)).symm
    have hu_conj : (a : Ω) * (u : Ω) * (a : Ω)⁻¹ = (u : Ω) := by
      rw [← hucomm]
      group
    let vS : ↥S := ⟨v, hvS⟩
    have hvbar : mk vS ∈ modCentreImage S B := by
      rw [modCentreImage]
      exact Subgroup.mem_map.mpr ⟨vS, Subgroup.mem_subgroupOf.mpr hvB, rfl⟩
    have hconjbar : mk (a * vS * a⁻¹) ∈ modCentreImage S B := by
      have h := (Subgroup.mem_normalizer_iff.mp haN (mk vS)).mp hvbar
      rw [show mk (a * vS * a⁻¹) = mk a * mk vS * (mk a)⁻¹ from by
        rw [map_mul, map_mul, map_inv]]
      exact h
    have hconjbar' : mk (a * vS * a⁻¹) ∈ (B.subgroupOf S).map mk := by
      simpa only [modCentreImage] using hconjbar
    obtain ⟨wS, hwsub, hweq⟩ := Subgroup.mem_map.mp hconjbar'
    have hwB : (wS : Ω) ∈ B := Subgroup.mem_subgroupOf.mp hwsub
    have hvp : vS ^ p = 1 := Subtype.ext (by simpa using hB.2 v hvB)
    have hwp : wS ^ p = 1 := Subtype.ext (by simpa using hB.2 (wS : Ω) hwB)
    have hcp : (a * vS * a⁻¹) ^ p = 1 := by
      rw [conj_pow, hvp, mul_one]
      simp
    obtain ⟨z, hz, hwz⟩ :=
      (QuotientGroup.mk'_eq_mk' (N := Subgroup.center ↥S)).mp hweq
    have hzpow : z ^ p = 1 := by
      have hcomm : Commute wS z := Subgroup.mem_center_iff.mp hz wS
      have h1 : (a * vS * a⁻¹) ^ p = (wS * z) ^ p := by rw [hwz]
      rw [hcp, hcomm.mul_pow, hwp, one_mul] at h1
      exact h1.symm
    have hz1 : z = 1 := by
      have hdvd : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzpow
      have hdvd_card : orderOf z ∣ Nat.card (Subgroup.center ↥S) :=
        Subgroup.orderOf_dvd_natCard _ hz
      rcases hp.eq_one_or_self_of_dvd (orderOf z) hdvd with h | h
      · exact orderOf_eq_one_iff.mp h
      · exact absurd (h ▸ hdvd_card) hZ
    have hc_eq : a * vS * a⁻¹ = wS := by
      rw [← hwz, hz1, mul_one]
    have hconjv : (a : Ω) * v * (a : Ω)⁻¹ ∈ B := by
      have hval : (a : Ω) * v * (a : Ω)⁻¹ = (wS : Ω) := by
        simpa using congrArg Subtype.val hc_eq
      rw [hval]
      exact hwB
    have heq : (a : Ω) * b * (a : Ω)⁻¹ =
        (u : Ω) * ((a : Ω) * v * (a : Ω)⁻¹) := by
      rw [← huv]
      rw [show (a : Ω) * ((u : Ω) * v) * (a : Ω)⁻¹ =
          ((a : Ω) * (u : Ω) * (a : Ω)⁻¹) *
            ((a : Ω) * v * (a : Ω)⁻¹) from by group]
      rw [hu_conj]
    rw [heq]
    exact B.mul_mem huB hconjv
  have hkey : ∀ a : ↥S, mk a ∈ Subgroup.normalizer (modCentreImage S B : Set Q) →
      (a : Ω) ∈ N := by
    intro a haN
    have hnorm : (a : Ω) ∈ Subgroup.normalizer (B : Set Ω) := by
      rw [Subgroup.mem_normalizer_iff]
      intro b
      constructor
      · exact hconjB a haN b
      · intro hb
        have haNinv : mk a⁻¹ ∈ Subgroup.normalizer (modCentreImage S B : Set Q) := by
          have := (Subgroup.normalizer (modCentreImage S B : Set Q)).inv_mem haN
          simpa using this
        have hback := hconjB a⁻¹ haNinv ((a : Ω) * b * (a : Ω)⁻¹) hb
        have hbeq : b = (a : Ω)⁻¹ * ((a : Ω) * b * (a : Ω)⁻¹) * ((a : Ω)⁻¹)⁻¹ := by
          group
        rw [hbeq]
        simpa using hback
    have hcent : (a : Ω) ∈ Subgroup.centralizer ({x} : Set Ω) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.mp hxC (a : Ω) a.2).symm
    rw [hN]
    exact Subgroup.mem_inf.mpr ⟨hnorm, hcent⟩
  have hsup_le : (⨆ g ∈ Subgroup.normalizer (modCentreImage S B : Set Q),
      (modCentreImage S K).map (MulAut.conj g).toMonoidHom) ≤
      modCentreImage S (closureIn K N) := by
    refine iSup₂_le fun g hg => ?_
    intro q hq
    rw [Subgroup.mem_map] at hq
    obtain ⟨qk, hqk, rfl⟩ := hq
    rw [modCentreImage, Subgroup.mem_map] at hqk
    obtain ⟨k, hk, hkq⟩ := hqk
    rw [← hkq]
    obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥S) g
    have hsN : (s : Ω) ∈ N := hkey s (by rwa [hs])
    have hkK : (k : Ω) ∈ K := Subgroup.mem_subgroupOf.mp hk
    let cS : ↥S := s * k * s⁻¹
    have hcH : (cS : Ω) ∈ closureIn K N := by
      have hval : (cS : Ω) = (MulAut.conj (s : Ω)) (k : Ω) := by
        simp [cS, MulAut.conj_apply]
      rw [hval]
      exact Subgroup.mem_iSup_of_mem (s : Ω)
        (Subgroup.mem_iSup_of_mem hsN (Subgroup.mem_map_of_mem _ hkK))
    have hcQ : mk cS ∈ modCentreImage S (closureIn K N) := by
      rw [modCentreImage]
      exact Subgroup.mem_map.mpr ⟨cS, Subgroup.mem_subgroupOf.mpr hcH, rfl⟩
    have hcalc : (MulAut.conj g).toMonoidHom (mk k) = mk cS := by
      change (MulAut.conj g) (mk k) = mk cS
      rw [← hs]
      rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
    rw [hcalc]
    exact hcQ
  have hQtop : modCentreImage S (closureIn K N) = ⊤ := by
    apply top_le_iff.mp
    rw [← htop]
    exact hsup_le
  have hsupTop : (closureIn K N).subgroupOf S ⊔ Subgroup.center ↥S = ⊤ := by
    have h := QuotientGroup.comap_map_mk' (Subgroup.center ↥S)
      ((closureIn K N).subgroupOf S)
    have hQtop' : Subgroup.map mk ((closureIn K N).subgroupOf S) = ⊤ := by
      simpa [modCentreImage] using hQtop
    rw [hQtop'] at h
    simpa [sup_comm] using h.symm
  have hcomm : ⁅(closureIn K N).subgroupOf S ⊔ Subgroup.center ↥S,
      (closureIn K N).subgroupOf S ⊔ Subgroup.center ↥S⁆ ≤
      ⁅(closureIn K N).subgroupOf S, (closureIn K N).subgroupOf S⁆ := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨j₁, hj₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hu
    obtain ⟨j₂, hj₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hv
    have h1 : z₁ * (j₂ * z₂) = (j₂ * z₂) * z₁ :=
      (Subgroup.mem_center_iff.1 hz₁ _).symm
    have h2 : z₂ * j₁⁻¹ = j₁⁻¹ * z₂ := (Subgroup.mem_center_iff.1 hz₂ _).symm
    have e : ⁅j₁ * z₁, j₂ * z₂⁆ = ⁅j₁, j₂⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc j₁ * z₁ * (j₂ * z₂) * (j₁ * z₁)⁻¹ * (j₂ * z₂)⁻¹
          = j₁ * (z₁ * (j₂ * z₂)) * z₁⁻¹ * j₁⁻¹ * z₂⁻¹ * j₂⁻¹ := by group
        _ = j₁ * j₂ * (z₂ * j₁⁻¹) * z₂⁻¹ * j₂⁻¹ := by rw [h1]; group
        _ = j₁ * j₂ * j₁⁻¹ * j₂⁻¹ := by rw [h2]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator hj₁ hj₂
  have hH_sub_eq_top : (closureIn K N).subgroupOf S = ⊤ := by
    apply top_le_iff.mp
    have hperf : ⁅(⊤ : Subgroup ↥S), (⊤ : Subgroup ↥S)⁆ = ⊤ := by
      simpa [commutator] using hqs.1
    calc
      (⊤ : Subgroup ↥S) = ⁅(⊤ : Subgroup ↥S), (⊤ : Subgroup ↥S)⁆ := hperf.symm
      _ = ⁅(closureIn K N).subgroupOf S ⊔ Subgroup.center ↥S,
          (closureIn K N).subgroupOf S ⊔ Subgroup.center ↥S⁆ := by rw [← hsupTop]
      _ ≤ ⁅(closureIn K N).subgroupOf S, (closureIn K N).subgroupOf S⁆ := hcomm
      _ ≤ (closureIn K N).subgroupOf S := by
        rw [Subgroup.commutator_le]
        intro u hu v hv
        rw [commutatorElement_def]
        exact (closureIn K N).subgroupOf S |>.mul_mem
          ((closureIn K N).subgroupOf S |>.mul_mem
            ((closureIn K N).subgroupOf S |>.mul_mem hu hv)
            ((closureIn K N).subgroupOf S |>.inv_mem hu))
          ((closureIn K N).subgroupOf S |>.inv_mem hv)
  have hSH : S ≤ closureIn K N := (Subgroup.subgroupOf_eq_top).mp hH_sub_eq_top
  exact le_antisymm hH_le_S hSH

theorem lin_hc_false {Ω : Type} [Group Ω] [Finite Ω] {S B K N : Subgroup Ω}
    (hqs : CFSG.Open.IsQuasisimple ↥S) (hcl : closureIn K N = S)
    (hc : ∃ T : Subgroup Ω, T ≤ S ∧ IsPGroup 2 T ∧
      closureIn K N ⊔ B ≤ Subgroup.normalizer (T : Set Ω) ∧
      (⁅closureIn K N, T⁆ : Subgroup Ω) ≠ ⊥) : False := by
  obtain ⟨T, hTS, hT2, hnorm, hcomm⟩ := hc
  have hSnorm : S ≤ Subgroup.normalizer (T : Set Ω) := by
    rw [← hcl]
    exact le_trans le_sup_left hnorm
  have hTn : (T.subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hSnorm
  have hT2sub : IsPGroup 2 (T.subgroupOf S) := hT2.comap_subtype (K := S)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (T.subgroupOf S).Normal := hTn
  have hsolv : Group.IsSolvable (T.subgroupOf S) := by
    haveI : Group.IsNilpotent (T.subgroupOf S) := hT2sub.isNilpotent
    infer_instance
  have hTcent : T.subgroupOf S ≤ Subgroup.center ↥S :=
    CFSG.ComponentClassification.AschbacherTheorem5.FusionTwo.le_center_of_quasisimple
      hqs (T.subgroupOf S) hsolv
  apply hcomm
  rw [hcl, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have htS : t ∈ S := hTS ht
  have hz : (⟨t, htS⟩ : ↥S) ∈ Subgroup.center ↥S :=
    hTcent (Subgroup.mem_subgroupOf.mpr ht)
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨s, hs⟩)).symm

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
