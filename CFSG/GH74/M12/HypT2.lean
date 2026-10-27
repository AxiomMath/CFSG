module

public import CFSG.GH74.M12.HypLocal

public section

namespace CFSG.GH74.M12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.M12.Hyp CFSG.Blueprint

theorem factorization_192_two : Nat.factorization 192 2 = 6 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  have h : (192 : ℕ) = 2 ^ 6 * 3 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem s_M12_asc03Hyp :
    ∀ z : M12Group, IsCentralInvolution z →
      Asc03Hyp M12Group z ∧
        ∀ K ∈ q8Subgroups (CFSG.pCore 2 ↥(centralizer ({z} : Set M12Group))), K.Normal :=
  fun z hz => asc03_of_central_involution z hz

theorem Jelt_mem_bfS' : Jelt ∈ bfS' := bfJ_mem_bfS

theorem Eelt_mem_bfS' : Eelt ∈ bfS' := bfE_mem

theorem Felt_mem_bfS' : Felt ∈ bfS' := bfF_mem

theorem Xelt_eq : Xelt = Eelt⁻¹ * Felt * Eelt * Felt⁻¹ := rfl

theorem bfS'_comm_Jelt
    {s : G12} (hs : s ∈ bfS') : s * Jelt = Jelt * s := by
  obtain ⟨x, hx⟩ := tauC_real (tbl s.1) (BT_sub_HT _ (mem_bfS_iff.1 hs))
  have h1 : x.1.1 = s.1 := tbl_injective hx
  have h2 := mem_CJ.1 x.2
  rw [h1] at h2
  exact Subtype.ext h2.symm

theorem orderOf_conj_Jelt
    (g : G12) : orderOf (g * Jelt * g⁻¹) = 2 := by
  have := MulEquiv.orderOf_eq (MulAut.conj g) Jelt
  simpa [orderOf_Jelt] using this

theorem orderOf_Xelt : orderOf Xelt = 2 := by
  obtain ⟨h, hh⟩ := exists_conj_Jelt_Xelt
  rw [← hh]
  exact orderOf_conj_Jelt h

theorem exists_conj_sylow
    (P'' : Sylow 2 G12) :
    ∃ g : G12, ∀ y : G12, y ∈ (P'' : Subgroup G12) ↔ g⁻¹ * y * g ∈ bfS' := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G12 bfSylow P''
  refine ⟨g, fun y => ?_⟩
  have : y ∈ (P'' : Subgroup G12) ↔ g⁻¹ * y * g ∈ (bfSylow : Subgroup G12) := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp
  rw [this, coe_bfSylow]

theorem conj_X_mem_of_index_two (P'' : Sylow 2 G12) (g : G12)
    (hg : ∀ y : G12, y ∈ (P'' : Subgroup G12) ↔ g⁻¹ * y * g ∈ bfS')
    (R : Subgroup ↥P'') (hR : R.index = 2) : ∃ r ∈ R, (r : G12) = g * Xelt * g⁻¹ := by
  have hE : g * Eelt * g⁻¹ ∈ (P'' : Subgroup G12) := by
    rw [hg]
    have e : g⁻¹ * (g * Eelt * g⁻¹) * g = Eelt := by group
    rw [e]
    exact Eelt_mem_bfS'
  have hF : g * Felt * g⁻¹ ∈ (P'' : Subgroup G12) := by
    rw [hg]
    have e : g⁻¹ * (g * Felt * g⁻¹) * g = Felt := by group
    rw [e]
    exact Felt_mem_bfS'
  let e : ↥P'' := ⟨g * Eelt * g⁻¹, hE⟩
  let f : ↥P'' := ⟨g * Felt * g⁻¹, hF⟩
  have hm : e⁻¹ * f * e * f⁻¹ ∈ R := comm_mem_of_index_two R hR e f
  refine ⟨e⁻¹ * f * e * f⁻¹, hm, ?_⟩
  have h1 : ((e⁻¹ * f * e * f⁻¹ : ↥P'') : G12) =
      (g * Eelt * g⁻¹)⁻¹ * (g * Felt * g⁻¹) * (g * Eelt * g⁻¹) * (g * Felt * g⁻¹)⁻¹ := rfl
  rw [h1, Xelt_eq]
  group

theorem conj_Jelt_central (P'' : Sylow 2 G12) (g : G12)
    (hg : ∀ y : G12, y ∈ (P'' : Subgroup G12) ↔ g⁻¹ * y * g ∈ bfS') :
    ∀ s ∈ (P'' : Subgroup G12), s * (g * Jelt * g⁻¹) = (g * Jelt * g⁻¹) * s := by
  intro s hs
  have h1 := bfS'_comm_Jelt ((hg s).1 hs)
  calc s * (g * Jelt * g⁻¹) = g * ((g⁻¹ * s * g) * Jelt) * g⁻¹ := by group
    _ = g * (Jelt * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
    _ = (g * Jelt * g⁻¹) * s := by group

theorem iso_zElt_eq
    {G : Type*} [Group G] (z : G) (hz : z ≠ 1)
    (ψ : ↥(centralizer ({z} : Set G)) ≃* ↥(centralizer ({Jelt} : Set G12))) :
    ψ (zElt' z) = zElt' Jelt := by
  have hc : ∀ y : ↥(centralizer ({Jelt} : Set G12)), ψ (zElt' z) * y = y * ψ (zElt' z) := by
    intro y
    obtain ⟨y', rfl⟩ := ψ.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.1 y'.2).symm
  have hcJ : tauC (eCJ (ψ (zElt' z))) = tid ∨ tauC (eCJ (ψ (zElt' z))) = JT := by
    refine HT_center _ (tauC_mem _) ?_
    intro s hs
    obtain ⟨y, rfl⟩ := tauC_real s hs
    rw [← tauC_mul, ← tauC_mul]
    congr 1
    have := congrArg eCJ (hc (eCJ.symm y))
    simpa using this
  rcases hcJ with h | h
  · exfalso
    have h1 : eCJ (ψ (zElt' z)) = 1 := tauC_injective (by rw [h, tauC_one])
    have h2 : zElt' z = 1 := ψ.injective (by simpa using eCJ.injective (h1.trans (map_one eCJ).symm))
    exact hz (congrArg Subtype.val h2)
  · have h1 : eCJ (ψ (zElt' z)) = zJ := tauC_injective (by rw [h, tauC_zJ])
    exact eCJ.injective (h1.trans eCJ_zElt.symm)

theorem t2_local_aux
    {G : Type} [Group G] [Finite G] (P : Sylow 2 G) (P'' : Sylow 2 G12)
    (φ : ↥P ≃* ↥P'')
    (hconj : ∀ u v : ↥P, orderOf (u : G) = 2 → orderOf (v : G) = 2 →
      (IsConj (u : G) (v : G) ↔ IsConj ((φ u : ↥P'') : G12) ((φ v : ↥P'') : G12)))
    (hcent : ∀ u : ↥P, orderOf (u : G) = 2 →
      Nonempty (↥(centralizer ({(u : G)} : Set G)) ≃*
        ↥(centralizer ({((φ u : ↥P'') : G12)} : Set G12)))) :
    ∃ z : G, IsCentralInvolution z ∧ Asc03Hyp G z ∧
      ∃ K ∈ q8Subgroups (pCore 2 ↥(centralizer ({z} : Set G))), K.Normal := by
  classical
  obtain ⟨g, hgP⟩ := exists_conj_sylow P''
  have hz'P : g * Jelt * g⁻¹ ∈ (P'' : Subgroup G12) := (hgP _).2 (by
    have e : g⁻¹ * (g * Jelt * g⁻¹) * g = Jelt := by group
    rw [e]; exact Jelt_mem_bfS')
  have hzc := conj_Jelt_central P'' g hgP
  set w' : ↥P'' := ⟨g * Jelt * g⁻¹, hz'P⟩ with hw'
  set w : ↥P := φ.symm w' with hw
  have hw'o : orderOf (w' : G12) = 2 := orderOf_conj_Jelt g
  have hwo : orderOf (w : G) = 2 := by
    rw [Subgroup.orderOf_coe, hw, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hw'o
  have hwc : ∀ s ∈ (P : Subgroup G), s * (w : G) = (w : G) * s := by
    intro s hs
    have h1 : φ ⟨s, hs⟩ * w' = w' * φ ⟨s, hs⟩ := Subtype.ext (hzc _ (φ ⟨s, hs⟩).2)
    have h2 : (⟨s, hs⟩ : ↥P) * w = w * ⟨s, hs⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, hw, MulEquiv.apply_symm_apply]
      exact h1
    exact congrArg Subtype.val h2
  have hcentral : IsCentralInvolution (w : G) := ⟨hwo, P, w.2, hwc⟩
  obtain ⟨ψ₁⟩ := hcent w hwo
  have hφw : (φ w : ↥P'') = w' := φ.apply_symm_apply w'
  have hset : centralizer ({((φ w : ↥P'') : G12)} : Set G12) =
      centralizer ({g * Jelt * g⁻¹} : Set G12) := by rw [hφw]
  let ψ : ↥(centralizer ({(w : G)} : Set G)) ≃* ↥(centralizer ({Jelt} : Set G12)) :=
    ψ₁.trans ((MulEquiv.subgroupCongr hset).trans (conjCentralizerEquiv g Jelt).symm)
  have hz1 : (w : G) ≠ 1 := by
    intro h; rw [h, orderOf_one] at hwo; omega
  have hψz : ψ (zElt' (w : G)) = zElt' Jelt := iso_zElt_eq (w : G) hz1 ψ
  have hloc : LocalHyp ↥(centralizer ({(w : G)} : Set G)) (zElt' (w : G)) :=
    LocalHyp.of_mulEquiv ψ.symm (ψ.symm_apply_eq.2 hψz.symm) localHyp_centralizer_Jelt
  have hcardP'' : Nat.card ↥P'' = 64 := by
    have h := Sylow.card_eq_multiplicity P''
    rw [card_G12, factorization_95040] at h
    exact h.trans (by norm_num)
  have hcardP : Nat.card ↥(P : Subgroup G) = 64 := by
    rw [← hcardP'']
    exact Nat.card_congr φ.toEquiv
  have hPle : (P : Subgroup G) ≤ centralizer ({(w : G)} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (hwc s hs)
  have hcardPC : Nat.card ↥((P : Subgroup G).subgroupOf (centralizer ({(w : G)} : Set G))) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv, hcardP]
  let SylC : Sylow 2 ↥(centralizer ({(w : G)} : Set G)) :=
    Sylow.ofCard ((P : Subgroup G).subgroupOf (centralizer ({(w : G)} : Set G)))
      (by rw [hcardPC, hloc.card_eq, factorization_192_two]; norm_num)
  have hQP : ∀ q ∈ pCore 2 ↥(centralizer ({(w : G)} : Set G)), (q : G) ∈ (P : Subgroup G) := by
    intro q hq
    have h1 := pCore_le_sylow SylC hq
    rw [Sylow.coe_ofCard] at h1
    exact h1
  let ι0 : ↥(pCore 2 ↥(centralizer ({(w : G)} : Set G))) →* ↥(P : Subgroup G) :=
    ((centralizer ({(w : G)} : Set G)).subtype.comp
      (pCore 2 ↥(centralizer ({(w : G)} : Set G))).subtype).codRestrict (P : Subgroup G)
        (fun q => hQP q.1 q.2)
  let ι : ↥(pCore 2 ↥(centralizer ({(w : G)} : Set G))) →* ↥P'' := φ.toMonoidHom.comp ι0
  have hι : Function.Injective ι := by
    intro a b hab
    have h1 : ι0 a = ι0 b := φ.injective hab
    have h2 : (ι0 a).1 = (ι0 b).1 := congrArg Subtype.val h1
    apply Subtype.ext
    apply Subtype.ext
    exact h2
  have hcardR : Nat.card ↥ι.range = 32 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, hloc.card_core]
  have hRidx : ι.range.index = 2 := by
    have h := Subgroup.card_mul_index ι.range
    rw [hcardR, hcardP''] at h
    omega
  obtain ⟨r, hrR, hrX⟩ := conj_X_mem_of_index_two P'' g hgP ι.range hRidx
  obtain ⟨q, hq⟩ := hrR
  have hφu : φ (ι0 q) = r := hq
  have hou : orderOf ((ι0 q : ↥P) : G) = 2 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq φ, hφu, ← Subgroup.orderOf_coe, hrX]
    have := MulEquiv.orderOf_eq (MulAut.conj g) Xelt
    simpa [orderOf_Xelt] using this
  obtain ⟨h, hh⟩ := exists_conj_Jelt_Xelt
  have hIsConj : IsConj ((φ w : ↥P'') : G12) ((φ (ι0 q) : ↥P'') : G12) := by
    rw [hφw, hφu, hrX]
    refine isConj_iff.2 ⟨g * h * g⁻¹, ?_⟩
    show g * h * g⁻¹ * (g * Jelt * g⁻¹) * (g * h * g⁻¹)⁻¹ = g * Xelt * g⁻¹
    rw [← hh]
    group
  obtain ⟨c, hc⟩ := isConj_iff.1 ((hconj w (ι0 q) hwo hou).2 hIsConj)
  have hne : c * (w : G) * c⁻¹ ≠ (w : G) := by
    rw [hc]
    intro heq
    have h1 : ι0 q = w := Subtype.ext heq
    have h2 : r = w' := by rw [← hφu, h1, hφw]
    have h3 : g * Xelt * g⁻¹ = g * Jelt * g⁻¹ := by rw [← hrX, h2]
    have h4 : Xelt = Jelt := by simpa using h3
    exact Xelt_ne_Jelt h4
  have hwc' : ∃ c : G, c * (w : G) * c⁻¹ ≠ (w : G) ∧
      ∃ q ∈ pCore 2 ↥(centralizer ({(w : G)} : Set G)), (q : G) = c * (w : G) * c⁻¹ :=
    ⟨c, hne, q.1, q.2, by rw [hc]; rfl⟩
  exact ⟨(w : G), hcentral, asc03Hyp_of_local (w : G) hwo hloc hwc',
    exists_q8_normal_of_mulEquiv ψ.symm exists_q8_normal_Jelt⟩

theorem s_T2_local : S_T2_local := by
  intro G _ _ _ hpat
  obtain ⟨P, P', φ, hconj, hcent⟩ := hpat
  exact t2_local_aux P P' φ hconj hcent

end CFSG.GH74.M12
