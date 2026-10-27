module

public import CFSG.Literature.Janko67Setting
public import CFSG.LargeExtraspecial.AS35DHDefs
public import CFSG.GF2Type.Aschbacher1976Full.HSBurnside

public section

namespace CFSG.Literature.Janko67

open CFSG CFSG.RankThree.GF2n.Parrott CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial


theorem exists_isHStar {G : Type} [Group G] [Finite G] (S : Setting G) (f : S.M ≃* C0)
    (hf : f S.zM = tC) (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {g : G} (hgM : g * S.z * g⁻¹ ∈ S.M) (hne : g * S.z * g⁻¹ ≠ S.z) :
    ∃ H : Subgroup G, S.IsHStar H := by
  classical
  let ιf : C0 →* G := S.M.subtype.comp (f.symm : C0 →* S.M)
  let S₁ : Subgroup G := S0.map ιf
  have hιf_inj : Function.Injective ιf := by
    intro a b h
    exact f.symm.injective (Subtype.ext h)
  have htC_mem_S0 : tC ∈ S0 := Subgroup.subset_closure (by simp)
  have huC_mem_S0 : uC ∈ S0 := Subgroup.subset_closure (by simp)
  have hutC_mem_S0 : uC * tC ∈ S0 := S0.mul_mem huC_mem_S0 htC_mem_S0
  have hιt : ιf tC = S.z := by
    have h1 : f.symm tC = S.zM := by rw [← hf, MulEquiv.symm_apply_apply]
    change S.M.subtype (f.symm tC) = S.z
    rw [h1]
    rfl
  have hzS1 : S.z ∈ S₁ :=
    Subgroup.mem_map.mpr ⟨tC, htC_mem_S0, hιt⟩
  have hS1card : Nat.card S₁ = 16 := by
    change Nat.card (S0.map ιf) = 16
    rw [Subgroup.card_map_of_injective hιf_inj, card_S0]
  have hS1sq : ∀ x ∈ S₁, x * x = 1 := by
    intro x hx
    obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
    change ιf x0 * ιf x0 = 1
    rw [← map_mul, mul_self_eq_one_of_mem_S0 hx0, map_one]
  obtain ⟨P, hP, -⟩ := exists_sylow_eq_map_P0 S f hf
  have hP_eq : (P : Subgroup G) = P0.map ιf := by
    rw [hP, Subgroup.map_map]
  have hS1_le_P : S₁ ≤ (P : Subgroup G) := by
    rw [hP_eq]
    exact Subgroup.map_mono S0_le_P0
  have htC_mem_pCore : tC ∈ CFSG.pCore 2 C0 := by
    rw [pCore_C0_eq]
    have h1 : a1C * a1C = tC := by
      apply Subtype.ext
      apply Subtype.ext
      exact alpha1_sq
    rw [← h1]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  have huC_ne_one : uC ≠ 1 := by
    intro h
    have h1 : (⟨u, u_mem_Q⟩ : QP45.originalSubgroup) = 1 :=
      (Subgroup.mk_eq_one (H := C0)).mp h
    exact u_ne_one ((Subgroup.mk_eq_one (H := QP45.originalSubgroup)).mp h1)
  have hutC_ne_tC : uC * tC ≠ tC := by
    intro h
    have h' := congrArg (fun x : C0 => x * tC⁻¹) h
    have hu1 : uC = 1 := by simpa using h'
    exact huC_ne_one hu1
  have huC_ne_tC : uC ≠ tC := by
    intro h
    have huQ : uC ∈ CFSG.pCore 2 C0 := h ▸ htC_mem_pCore
    have hP0le : P0 ≤ CFSG.pCore 2 C0 := P0_le_of_uC_mem huQ
    have hcard := Subgroup.card_le_of_le hP0le
    rw [card_P0, card_pCore_C0] at hcard
    norm_num at hcard
  have hweak : ∀ h : G, CFSG.conjugate S₁ h ≤ (P : Subgroup G) →
      CFSG.conjugate S₁ h = S₁ := by
    intro h hle
    let A : Subgroup C0 := (CFSG.conjugate S₁ h).comap ιf
    have hAle : A ≤ P0 := by
      intro a ha
      have hιa : ιf a ∈ CFSG.conjugate S₁ h := ha
      have hιaP : ιf a ∈ (P : Subgroup G) := hle hιa
      rw [hP_eq] at hιaP
      obtain ⟨p, hp, hfp⟩ := Subgroup.mem_map.mp hιaP
      have hpa : p = a := hιf_inj hfp
      rwa [hpa] at hp
    have hmapA : A.map ιf = CFSG.conjugate S₁ h := by
      apply Subgroup.map_comap_eq_self
      exact hle.trans (by rw [hP_eq]; exact Subgroup.map_le_range ιf P0)
    have hAcard : Nat.card A = 16 := by
      calc Nat.card A = Nat.card (A.map ιf) :=
            (Subgroup.card_map_of_injective hιf_inj).symm
        _ = Nat.card (CFSG.conjugate S₁ h) := by rw [hmapA]
        _ = Nat.card S₁ := Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective
        _ = 16 := hS1card
    have hA2 : ∀ a ∈ A, a * a = 1 := by
      intro a ha
      have hia : ιf a ∈ CFSG.conjugate S₁ h := ha
      obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hia
      obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
      have hx0sq : ιf x0 * ιf x0 = 1 := by
        rw [← map_mul, mul_self_eq_one_of_mem_S0 hx0, map_one]
      have hsq : ιf a * ιf a = 1 := by
        rw [← hxeq]
        change (MulAut.conj h⁻¹) (ιf x0) * (MulAut.conj h⁻¹) (ιf x0) = 1
        rw [← map_mul, hx0sq, map_one]
      apply hιf_inj
      rw [map_mul, hsq, map_one]
    have hAeq : A = S0 := eq_S0_of_le_P0 hAle hAcard hA2
    calc CFSG.conjugate S₁ h = A.map ιf := hmapA.symm
      _ = S0.map ιf := by rw [hAeq]
      _ = S₁ := rfl
  have hab : ∀ a ∈ S₁, ∀ b ∈ S₁, a * b = b * a := by
    intro a ha b hb
    have ha2 : a * a = 1 := hS1sq a ha
    have hb2 : b * b = 1 := hS1sq b hb
    have hab2 : a * b * (a * b) = 1 := hS1sq (a * b) (S₁.mul_mem ha hb)
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have hba : b * a = a * b := by
      calc b * a = a⁻¹ * (a * b * (a * b)) * b⁻¹ := by group
        _ = a⁻¹ * 1 * b⁻¹ := by rw [hab2]
        _ = a * b := by rw [hai, hbi]; group
    exact hba.symm
  let y : G := g * S.z * g⁻¹
  have hyM : y ∈ S.M := hgM
  let yM : S.M := ⟨y, hyM⟩
  have hy2 : orderOf y = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g) S.z
    rw [S.orderOf_z] at h
    simpa [y] using h
  have hyM2 : orderOf yM = 2 := by
    rw [← Subgroup.orderOf_coe yM]
    exact hy2
  have hy0_2 : orderOf (f yM) = 2 := by
    rw [MulEquiv.orderOf_eq f yM, hyM2]
  have hyQ : y ∉ S.QG := fun h => hne (hW g h)
  have hy0Q : f yM ∉ CFSG.pCore 2 C0 := by
    intro h
    rw [← map_Q_eq S f] at h
    obtain ⟨m, hm, hmf⟩ := Subgroup.mem_map.mp h
    have hmy : m = yM := f.injective hmf
    have hyMQ : yM ∈ S.Q := hmy ▸ hm
    exact hyQ ⟨yM, hyMQ, rfl⟩
  have hy_eq : y = ιf (f yM) := by
    simp [ιf, yM, y]
  have hmain : ∃ m : S.M, (m : G) * y * (m : G)⁻¹ ∈ S₁ ∧
      (m : G) * y * (m : G)⁻¹ ≠ S.z := by
    rcases isConj_uC_or_of_not_mem_pCore hy0_2 hy0Q with hconj | hconj
    · obtain ⟨c0, hc0⟩ := isConj_iff.mp hconj
      have hcG : (f.symm c0 : G) = ιf c0 := by simp [ιf]
      have hmy : (f.symm c0 : G) * y * (f.symm c0 : G)⁻¹ = ιf uC := by
        calc (f.symm c0 : G) * y * (f.symm c0 : G)⁻¹
            = ιf c0 * ιf (f yM) * (ιf c0)⁻¹ := by rw [hcG, hy_eq]
          _ = ιf (c0 * f yM * c0⁻¹) := by rw [map_mul, map_mul, map_inv]
          _ = ιf uC := by rw [hc0]
      refine ⟨f.symm c0, ?_, ?_⟩
      · rw [hmy]
        exact Subgroup.mem_map.mpr ⟨uC, huC_mem_S0, rfl⟩
      · intro hw
        apply huC_ne_tC
        apply hιf_inj
        rw [hιt]
        rw [hmy] at hw
        exact hw
    · obtain ⟨c0, hc0⟩ := isConj_iff.mp hconj
      have hcG : (f.symm c0 : G) = ιf c0 := by simp [ιf]
      have hmy : (f.symm c0 : G) * y * (f.symm c0 : G)⁻¹ = ιf (uC * tC) := by
        calc (f.symm c0 : G) * y * (f.symm c0 : G)⁻¹
            = ιf c0 * ιf (f yM) * (ιf c0)⁻¹ := by rw [hcG, hy_eq]
          _ = ιf (c0 * f yM * c0⁻¹) := by rw [map_mul, map_mul, map_inv]
          _ = ιf (uC * tC) := by rw [hc0]
      refine ⟨f.symm c0, ?_, ?_⟩
      · rw [hmy]
        exact Subgroup.mem_map.mpr ⟨uC * tC, hutC_mem_S0, rfl⟩
      · intro hw
        apply hutC_ne_tC
        apply hιf_inj
        rw [hιt]
        rw [hmy] at hw
        exact hw
  obtain ⟨m, hmS1, hmne⟩ := hmain
  have hconjz : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ =
      (m : G) * y * (m : G)⁻¹ := by
    simp only [y, mul_inv_rev]
    group
  have hgw : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ∈ S₁ := by
    rw [hconjz]
    exact hmS1
  obtain ⟨n, hnN, hnconj⟩ :=
    CFSG.GF2Type.Aschbacher1976Full.HS.burnside_fusion (p := 2) (a := S.z)
      (g := (m : G) * g) P S₁ hS1_le_P hab hweak hzS1 hgw
  have hnz : n * S.z * n⁻¹ ≠ S.z := by
    rw [hnconj, hconjz]
    exact hmne
  have hnM : n ∉ S.M := by
    intro hn
    have hcomm : n * S.z = S.z * n := Subgroup.mem_centralizer_singleton_iff.mp hn
    exact hnz (by rw [hcomm]; group)
  let H₁ : Subgroup G := Subgroup.normalizer (S₁ : Set G)
  have hnH : n ∈ H₁ := hnN
  have hQle : S.QG ≤ H₁ := by
    intro q hq
    obtain ⟨qM, hqM, rfl⟩ := Subgroup.mem_map.mp hq
    have hfqQ : f qM ∈ CFSG.pCore 2 C0 := by
      rw [← map_Q_eq S f]
      exact Subgroup.mem_map.mpr ⟨qM, hqM, rfl⟩
    have hfqN : f qM ∈ Subgroup.normalizer (S0 : Set C0) :=
      pCore_C0_le_normalizer_S0 hfqQ
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc S₁.map (MulAut.conj (S.M.subtype qM))
        = (S0.map ιf).map (MulAut.conj (S.M.subtype qM)) := rfl
      _ = S0.map ((MulAut.conj (S.M.subtype qM)).toMonoidHom.comp ιf) :=
            Subgroup.map_map (K := S0) (MulAut.conj (S.M.subtype qM)).toMonoidHom ιf
      _ = S0.map (ιf.comp (MulAut.conj (f qM)).toMonoidHom) := by
            congr 1
            ext a
            simp [ιf, map_mul]
      _ = (S0.map (MulAut.conj (f qM)).toMonoidHom).map ιf :=
            (Subgroup.map_map (K := S0) ιf (MulAut.conj (f qM)).toMonoidHom).symm
      _ = S0.map ιf := by
            have hS0conj : S0.map (MulAut.conj (f qM)).toMonoidHom = S0 :=
              Subgroup.mem_normalizer_iff_map_conj_eq.mp hfqN
            rw [hS0conj]
      _ = S₁ := rfl
  have hHset : S.IsHSet H₁ := by
    refine ⟨hQle, ?_, ?_⟩
    · intro hbot
      have hS1leH : S₁ ≤ H₁ := Subgroup.le_normalizer
      have hKne : S₁.subgroupOf H₁ ≠ ⊥ := by
        intro hKbot
        have hmem : (⟨S.z, hS1leH hzS1⟩ : H₁) ∈ S₁.subgroupOf H₁ := hzS1
        have hmem' : (⟨S.z, hS1leH hzS1⟩ : H₁) ∈ (⊥ : Subgroup H₁) :=
          hKbot ▸ hmem
        have h1 : (⟨S.z, hS1leH hzS1⟩ : H₁) = 1 := by simpa using hmem'
        have hz1 : S.z = 1 := congrArg (fun x : H₁ => (x : G)) h1
        exact S.z_ne_one hz1
      have hKp : IsPGroup 2 (S₁.subgroupOf H₁) := by
        have hKcard : Nat.card (S₁.subgroupOf H₁) = 16 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS1leH).toEquiv, hS1card]
        exact IsPGroup.of_card (n := 4) (by rw [hKcard]; norm_num)
      have hKle : S₁.subgroupOf H₁ ≤ CFSG.pCore 2 H₁ :=
        le_sSup ⟨inferInstance, hKp⟩
      have hKbot : S₁.subgroupOf H₁ = ⊥ :=
        le_bot_iff.mp (by simpa [hbot] using hKle)
      exact hKne hKbot
    · intro hleM
      exact hnM (hleM hnH)
  have hnonempty : ∃ n : ℕ, ∃ H : Subgroup G, S.IsHSet H ∧ Nat.card H = n :=
    ⟨_, H₁, hHset, rfl⟩
  let n₀ : ℕ := Nat.find hnonempty
  obtain ⟨H, hH, hHcard⟩ := Nat.find_spec hnonempty
  refine ⟨H, hH, fun H' hH' hle => ?_⟩
  have hmin : n₀ ≤ Nat.card H' := Nat.find_min' hnonempty ⟨H', hH', rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle (hHcard.trans_le hmin)

end CFSG.Literature.Janko67
