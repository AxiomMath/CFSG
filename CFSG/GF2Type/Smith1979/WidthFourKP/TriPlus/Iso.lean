module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaMinusSchur
public import CFSG.LargeExtraspecial.S14SMKDeltaLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.TriPlus

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.S14
  CFSG.LargeExtraspecial.OrthoF2 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def resK (S : Setting G) (g : G) {t : S.O} (K : Subgroup S.O)
    (hK : ∀ x ∈ K, x * t = t * x)
    (hV : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t) :
    K →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t) :=
  restrictHom (S.O.subtype.comp K.subtype) (Vt S g t) fun c _ hu => by
    rw [← hV] at hu ⊢
    exact apply_mem_commSpace_of_comm (hK c c.2) hu

theorem range_resK_le_orthogonalGroup {S : Setting G} {g : G} (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) {K : Subgroup S.O} (hKM : K ≤ S.Mbar)
    (hK : ∀ x ∈ K, x * t = t * x) (hV : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t)
    {Q : QuadraticForm (ZMod 2) (Vt S g t)}
    (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht))) :
    (resK S g K hK hV).range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  have hcoe : ∀ (c : K) (v : Vt S g t),
      ((resK S g K hK hV c v : Vt S g t) : S.Qt) =
        ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := fun _ _ => rfl
  rintro _ ⟨c, rfl⟩
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  have hD := dtEqConj_of_omegaCase H hNo C hΩ
  have key : ∀ x ∈ K, ∀ v : S.Qt, v ∈ orbit S g t →
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ orbit S g t := fun x hx v hv =>
    apply_mem_orbit_of_comm H ht hD (hKM hx) (hK x hx) hv
  intro v
  by_cases hv0 : v = 0
  · rw [hv0, map_zero]
  have hcv0 : resK S g K hK hV c v ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr hv0
  have hiff : Q (resK S g K hK hV c v) = 0 ↔ Q v = 0 := by
    rw [hsing _ hcv0, hsing _ hv0, mem_orbitOf_RmodN_iff H.conj_mem ht,
      mem_orbitOf_RmodN_iff H.conj_mem ht, hcoe c v]
    constructor
    · intro h
      have := key _ (inv_mem c.2) _ h
      rwa [inv_apply_apply_O] at this
    · exact key _ c.2 v
  rcases zmod2_eq_zero_or_eq_one (Q (resK S g K hK hV c v)) with h1 | h1 <;>
    rcases zmod2_eq_zero_or_eq_one (Q v) with h2 | h2
  · rw [h1, h2]
  · exact absurd (hiff.mp h1) (by rw [h2]; decide)
  · exact absurd (hiff.mpr h2) (by rw [h1]; decide)
  · rw [h1, h2]

theorem mul_self_of_fix_Vt {S : Setting G} {g : G} (hw : S.width = 4) (H : Hyp4 S g)
    {t : S.O} (ht1 : t ≠ 1) (h4 : finrank (ZMod 2) (Vt S g t) = 4) {u : S.O}
    (hu : ∀ v ∈ Vt S g t, (u : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : u * u = 1 :=
  Subtype.ext (S14.SMK.mul_self_of_fix (Q := S.q) u.2 (C := Vt S g t)
    (W4Minus.Wt_eq_Vt_w4 hw H ht1 h4).le hu)

theorem iso_of_normal_line {S : Setting G} (hw : S.width = 4) (hnoAll : S11.NoA2All S) {g : G}
    (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) {D : Subgroup S.O} (hDM : D ≤ S.Mbar)
    (hD3 : Nat.card D = 3) (hDn : ∀ x ∈ S.Mbar, ∀ y ∈ D, x * y * x⁻¹ ∈ D)
    (hcomm : ∀ x ∈ S.Mbar, x * t * x⁻¹ * t⁻¹ ∈ D) :
    ∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
      (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
        Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q)) := by
  have hNo : NoA2 S g := fun α h1 h2 h3 =>
    hnoAll g H.conj_mem H.conj_ne ⟨α, h1, h2, h3⟩
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hnc : ∃ x ∈ S.Mbar, x * t * x⁻¹ ≠ t := exists_conj_ne H ht ht1
  let K : Subgroup S.O := S.Mbar ⊓ centralizer ((D ⊔ zpowers t : Subgroup S.O) : Set S.O)
  have hKM : K ≤ S.Mbar := inf_le_left
  have hKt : ∀ x ∈ K, x * t = t * x := by
    intro x hx
    exact (mem_centralizer_iff.mp hx.2 t (mem_sup_right (mem_zpowers t))).symm
  have hV : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t :=
    (commSpace_t_eq H C ht ht1 hVQ).1
  have hprod : Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × K) :=
    nonempty_mulEquiv_sigma_prod (X := S.O) (M := S.Mbar) (D := D) (t := t)
      hDM hD3 hDn (S.Lbar_le_Mbar g ht) htt ht1 hcomm hnc
  have hinj : Function.Injective (resK S g K hKt hV) := by
    rw [injective_iff_map_eq_one]
    intro c hc
    let P : Subgroup S.O := (resK S g K hKt hV).ker.map K.subtype
    have hPM : P ≤ S.Mbar := by
      rintro _ ⟨k, -, rfl⟩
      exact hKM k.2
    have hP2 : IsPGroup 2 P := by
      rw [IsPGroup.iff_orderOf]
      intro p
      obtain ⟨k, hk, hkp⟩ := Subgroup.mem_map.mp p.2
      have hk1 : resK S g K hKt hV k = 1 := MonoidHom.mem_ker.mp hk
      have hkV : ∀ v ∈ Vt S g t, ((K.subtype k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
        (restrictHom_eq_one_iff _ _ _ k).mp hk1
      have hk2 : (K.subtype k : S.O) * (K.subtype k : S.O) = 1 :=
        mul_self_of_fix_Vt hw H ht1 h4 hkV
      have hp2 : p * p = 1 := by
        refine Subtype.ext ?_
        show (p : S.O) * (p : S.O) = 1
        rw [← hkp]
        exact hk2
      have hdvd : orderOf p ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hp2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact ⟨0, by rw [h, pow_zero]⟩
      · exact ⟨1, by rw [h, pow_one]⟩
    have hnorm : S.Mbar ≤ normalizer (P : Set S.O) := by
      intro x hx
      refine mem_normalizer_of_conj_le fun p hp => ?_
      obtain ⟨k, hk, hkp⟩ := Subgroup.mem_map.mp hp
      have hk1 : resK S g K hKt hV k = 1 := MonoidHom.mem_ker.mp hk
      have hkV : ∀ v ∈ Vt S g t, ((K.subtype k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
        (restrictHom_eq_one_iff _ _ _ k).mp hk1
      obtain ⟨s, hs, c', hc', rfl⟩ :=
        exists_sigma_mul_cent hDM hD3 hDn (S.Lbar_le_Mbar g ht) htt ht1 hcomm hnc hx
      have hcK : c' ∈ K := hc'
      have hc'invt : (c' : S.O)⁻¹ * t = t * (c' : S.O)⁻¹ := by
        calc (c' : S.O)⁻¹ * t
            = (c' : S.O)⁻¹ * (t * c') * (c' : S.O)⁻¹ := by group
          _ = (c' : S.O)⁻¹ * (c' * t) * (c' : S.O)⁻¹ := by rw [hKt c' hcK]
          _ = t * (c' : S.O)⁻¹ := by group
      let k' : K := ⟨c' * (k : S.O) * c'⁻¹,
        K.mul_mem (K.mul_mem hcK k.2) (K.inv_mem hcK)⟩
      have hk'1 : resK S g K hKt hV k' = 1 := by
        change restrictHom (S.O.subtype.comp K.subtype) (Vt S g t) _ k' = 1
        rw [restrictHom_eq_one_iff]
        intro v hv
        have hc'inv : (((c' : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t := by
          rw [← hV] at hv ⊢
          exact apply_mem_commSpace_of_comm hc'invt hv
        have hkv : ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            ((((c' : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
            (((c' : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := hkV _ hc'inv
        change ((c' * (k : S.O) * c'⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
        rw [coe_mul_apply, coe_mul_apply, hkv, apply_inv_apply_O]
      have hsk' : s * (k' : S.O) = (k' : S.O) * s := by
        have hk'K : (k' : S.O) ∈ S.Mbar ⊓
            centralizer ((D ⊔ zpowers t : Subgroup S.O) : Set S.O) := k'.2
        exact mem_centralizer_iff.mp hk'K.2 s hs
      have hpconj : (s * c') * p * (s * c')⁻¹ = (k' : S.O) := by
        calc (s * c') * p * (s * c')⁻¹
            = s * (c' * p * c'⁻¹) * s⁻¹ := by group
          _ = s * (c' * (k : S.O) * c'⁻¹) * s⁻¹ := by
            rw [← hkp]
            rfl
          _ = s * (k' : S.O) * s⁻¹ := rfl
          _ = (k' : S.O) := by rw [hsk']; group
      rw [hpconj]
      exact ⟨k', hk'1, rfl⟩
    have hPbot : P = ⊥ := Setting.s12_noNormalTwo_Mbar S P hPM hP2 hnorm
    have hcP : (c : S.O) ∈ P := ⟨c, MonoidHom.mem_ker.mpr hc, rfl⟩
    rw [hPbot, Subgroup.mem_bot] at hcP
    exact Subtype.ext hcP
  have hRmodN_le : RmodN S g t ≤ (resK S g K hKt hV).range := by
    intro e he
    rw [← range_resV H.conj_mem t] at he
    obtain ⟨⟨r, hr⟩, rfl⟩ := he
    have htV : ∀ v ∈ Vt S g t, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := fun v hv =>
      (S6.self_mem_Nbar H ht).2 v hv
    rcases mem_cent_of_comm_t (X := S.O) (M := S.Mbar) (D := D) (t := t)
      hDM hD3 hDn (S.Lbar_le_Mbar g ht) htt ht1 hcomm hnc
      (Rbar_le_Mbar hr) (commute_of_mem_Rbar H.conj_mem hr) with hc | hc
    · exact ⟨⟨r, hc⟩, LinearEquiv.ext fun v => Subtype.ext rfl⟩
    · refine ⟨⟨t * r, hc⟩, LinearEquiv.ext fun v => Subtype.ext ?_⟩
      change ((t * r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
        (r : S.Qt ≃ₗ[ZMod 2] S.Qt) v
      rw [coe_mul_apply, htV _ (apply_mem_Vt_of_mem_Rbar H.conj_mem hr v.2)]
  obtain ⟨Q, hQ, -, hX, -, hsing⟩ := hΩ.exists_form
  have hleOrth : (resK S g K hKt hV).range ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    range_resK_le_orthogonalGroup H hNo C ht ht1 hVQ hΩ hKM hKt hV hsing
  have hrange : (resK S g K hKt hV).range = omegaGroup Q hQ ∨
      (resK S g K hKt hV).range = TauCeti.QuadraticMap.orthogonalGroup Q := by
    have : Nontrivial (Vt S g t) := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    have h1 : omegaGroup Q hQ ≤ (resK S g K hKt hV).range := hX ▸ hRmodN_le
    have h2 : (resK S g K hKt hV).range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := hleOrth
    have h3 := relIndex_omegaGroup Q hQ
    have h4 := Subgroup.relIndex_mul_relIndex _ _ _ h1 h2
    rw [h3] at h4
    rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ h4) with h5 | h5
    · left
      exact le_antisymm (Subgroup.relIndex_eq_one.mp h5) h1
    · right
      rw [h5] at h4
      exact le_antisymm h2 (Subgroup.relIndex_eq_one.mp (by omega))
  obtain ⟨q, hqnd, -, ⟨eΩ⟩, ⟨eO⟩⟩ := Bridge.exists_fin_form Q h4
  have hQnd : ∀ u, (∀ v, QuadraticMap.polar Q u v = 0) → u = 0 :=
    (Bridge.polarBilin_nondegenerate_iff Q).mp hQ
  obtain ⟨eM⟩ := hprod
  let eK : K ≃* (resK S g K hKt hV).range := MonoidHom.ofInjective hinj
  refine ⟨q, hqnd hQnd, ?_⟩
  rcases hrange with hrange | hrange
  · left
    have eKΩQ : K ≃* timmesfeldOmega (Q : Vt S g t → ZMod 2) :=
      (eK.trans (MulEquiv.subgroupCongr hrange)).trans
        ((MulEquiv.subgroupCongr (timmesfeldOmega_eq Q hQ)).symm)
    have eKΩ : K ≃* timmesfeldOmega (q : (Fin 4 → ZMod 2) → ZMod 2) := eKΩQ.trans eΩ
    exact ⟨eM.trans (MulEquiv.prodCongr (MulEquiv.refl _) eKΩ)⟩
  · right
    have eKOQ : K ≃* timmesfeldIsometries (Q : Vt S g t → ZMod 2) :=
      (eK.trans (MulEquiv.subgroupCongr hrange)).trans
        ((MulEquiv.subgroupCongr (timmesfeldIsometries_eq Q)).symm)
    have eKO : K ≃* timmesfeldIsometries (q : (Fin 4 → ZMod 2) → ZMod 2) := eKOQ.trans eO
    exact ⟨eM.trans (MulEquiv.prodCongr (MulEquiv.refl _) eKO)⟩

end CFSG.GF2Type.Smith1979.TriPlus
