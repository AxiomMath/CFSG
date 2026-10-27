module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38Img

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open

section Split

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def resLE (W : Submodule (ZMod 2) V) {g : V ≃ₗ[ZMod 2] V}
    (h : W.map (g : V →ₗ[ZMod 2] V) = W) : W ≃ₗ[ZMod 2] W :=
  g.ofSubmodules W W h

theorem coe_resLE {W : Submodule (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (h : W.map (g : V →ₗ[ZMod 2] V) = W) (w : W) : (resLE W h w : V) = g w := rfl

theorem map_commSpace_resLE {W : Submodule (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (h : W.map (g : V →ₗ[ZMod 2] V) = W) :
    (commSpace (resLE W h)).map W.subtype = W.map ((g : V →ₗ[ZMod 2] V) - 1) := by
  ext v
  simp only [Submodule.mem_map, mem_commSpace, LinearMap.sub_apply, LinearEquiv.coe_coe,
    Module.End.one_apply, Submodule.subtype_apply]
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, w.2, by rw [Submodule.coe_sub, coe_resLE]⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, ⟨⟨w, hw⟩, rfl⟩, by rw [Submodule.coe_sub, coe_resLE]⟩

theorem map_sub_one_le {W : Submodule (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (h : W.map (g : V →ₗ[ZMod 2] V) = W) : W.map ((g : V →ₗ[ZMod 2] V) - 1) ≤ W := by
  rintro _ ⟨w, hw, rfl⟩
  have hgw : g w ∈ W := by
    rw [← h]
    exact ⟨w, hw, rfl⟩
  exact W.sub_mem hgw hw

theorem finrank_commSpace_resLE {W : Submodule (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (h : W.map (g : V →ₗ[ZMod 2] V) = W) :
    finrank (ZMod 2) (commSpace (resLE W h)) =
      finrank (ZMod 2) (W.map ((g : V →ₗ[ZMod 2] V) - 1)) := by
  rw [← map_commSpace_resLE h, Submodule.finrank_map_subtype_eq]

theorem resLE_mem_orthogonalGroup {Q : QuadraticForm (ZMod 2) V} {W : Submodule (ZMod 2) V}
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h : W.map (g : V →ₗ[ZMod 2] V) = W) :
    resLE W h ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  simp only [QuadraticMap.comp_apply, Submodule.subtype_apply, coe_resLE]
  exact CFSG.ClassicalGroups.Orthogonal.map_of_mem hg w

variable [FiniteDimensional (ZMod 2) V]

theorem finrank_commSpace_split {W₁ W₂ : Submodule (ZMod 2) V} (hsup : W₁ ⊔ W₂ = ⊤)
    (hinf : W₁ ⊓ W₂ = ⊥) {g : V ≃ₗ[ZMod 2] V} (h₁ : W₁.map (g : V →ₗ[ZMod 2] V) = W₁)
    (h₂ : W₂.map (g : V →ₗ[ZMod 2] V) = W₂) :
    finrank (ZMod 2) (commSpace g) = finrank (ZMod 2) (W₁.map ((g : V →ₗ[ZMod 2] V) - 1)) +
      finrank (ZMod 2) (W₂.map ((g : V →ₗ[ZMod 2] V) - 1)) := by
  have hc : commSpace g = W₁.map ((g : V →ₗ[ZMod 2] V) - 1) ⊔
      W₂.map ((g : V →ₗ[ZMod 2] V) - 1) := by
    rw [← Submodule.map_sup, hsup, Submodule.map_top]
  have hi : W₁.map ((g : V →ₗ[ZMod 2] V) - 1) ⊓ W₂.map ((g : V →ₗ[ZMod 2] V) - 1) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf (map_sub_one_le h₁) (map_sub_one_le h₂)).trans hinf.le)
  have h := Submodule.finrank_sup_add_finrank_inf_eq (W₁.map ((g : V →ₗ[ZMod 2] V) - 1))
    (W₂.map ((g : V →ₗ[ZMod 2] V) - 1))
  rw [hi, finrank_bot, add_zero, ← hc] at h
  exact h

theorem polarBilin_restrict_nondegenerate {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {W' W : Submodule (ZMod 2) V} (hsup : W' ⊔ W = ⊤)
    (horth : ∀ v ∈ W', ∀ w ∈ W, polar Q v w = 0) :
    (Q.comp W.subtype).polarBilin.Nondegenerate := by
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun w hw => ?_
  have hall : ∀ u : V, polar Q (w : V) u = 0 := by
    intro u
    have hu : u ∈ W' ⊔ W := hsup ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    have h1 : polar Q (w : V) a = 0 := by
      rw [polar_comm]
      exact horth a ha w w.2
    have h2 : polar Q (w : V) b = 0 := by
      have := hw ⟨b, hb⟩
      rw [polarBilin_apply_apply] at this
      simpa [polar, QuadraticMap.comp_apply] using this
    rw [polar_add_right, h1, h2, add_zero]
  have h0 : (w : V) = 0 := hQ.1 (w : V) fun u => by rw [polarBilin_apply_apply]; exact hall u
  exact Subtype.ext h0

end Split


structure IsTau {G : Type} [Group G] (A₁ V : Subgroup G) (x z τ : G) : Prop where
  normB : τ ∈ normalizer (sec3B A₁ x : Set G)
  normV : τ ∈ normalizer (V : Set G)
  inv_x : τ * x * τ⁻¹ = x⁻¹
  comm_z : τ * z = z * τ
  sq : τ * τ = 1

@[expose] def CentQCommX {G : Type} [Group G] (A₁ Q : Subgroup G) (x : G) : Prop :=
  ∀ c ∈ normalizer (sec3B A₁ x : Set G), c ∈ centralizer (Q : Set G) → c * x = x * c

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem map_ρG_W₀ {n : H.xsub.N} (hn : (n : G) ∈ normalizer (Q₀ : Set G)) :
    (H.xsub.clSub Q₀).map (H.ρG n : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) = H.xsub.clSub Q₀ :=
  H.ρG_mem_glStab hn

theorem map_ρG_W' {n : H.xsub.N} (hn : (n : G) ∈ normalizer (Q : Set G)) :
    (H.xsub.clSub Q).map (H.ρG n : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) = H.xsub.clSub Q := by
  have h := H.xsub.map_ρ_clSub n Q
  have h2 : Q.map (MulAut.conj (n : G)).toMonoidHom = Q := mem_normalizer_iff_map_conj_eq.mp hn
  rw [h2] at h
  exact h

theorem W'_nondegenerate :
    (H.xsub.q.comp (H.xsub.clSub Q).subtype).polarBilin.Nondegenerate :=
  polarBilin_restrict_nondegenerate H.xsub.q_nondegenerate H.W₀_sup_W'
    (fun _ hv _ hw => H.polar_W₀_W' hv hw)

theorem card_omega_W'_le :
    Nat.card (omegaGroup (H.xsub.q.comp (H.xsub.clSub Q).subtype) H.W'_nondegenerate) ≤
      25920 := by
  have hdim : finrank (ZMod 2) (H.xsub.clSub Q) = 2 * (2 + 1) := H.finrank_W'
  have : Nontrivial (H.xsub.clSub Q) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [H.finrank_W']; norm_num)
  have hprod : ∏ i ∈ Finset.Icc 1 2, (((Nat.card (ZMod 2) : ℤ) ^ 2) ^ i - 1) = 45 := by
    rw [Nat.card_zmod]
    decide
  have hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (H.xsub.q.comp (H.xsub.clSub Q).subtype)) ≤ 51840 := by
    by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
        (H.xsub.q.comp (H.xsub.clSub Q).subtype)
    · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 2)
        H.W'_nondegenerate hdim (ε := 1) (Or.inl ⟨rfl, hplus⟩)
      rw [hprod, Nat.card_zmod] at h
      have h1 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
          (H.xsub.q.comp (H.xsub.clSub Q).subtype)) : ℤ) = 40320 := by rw [h]; norm_num
      omega
    · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 2)
        H.W'_nondegenerate hdim (ε := -1) (Or.inr ⟨rfl, hplus⟩)
      rw [hprod, Nat.card_zmod] at h
      have h1 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
          (H.xsub.q.comp (H.xsub.clSub Q).subtype)) : ℤ) = 51840 := by rw [h]; norm_num
      omega
  have hidx := relIndex_omegaGroup (H.xsub.q.comp (H.xsub.clSub Q).subtype) H.W'_nondegenerate
  have hmul := Subgroup.relIndex_mul_card
    (omegaGroup (H.xsub.q.comp (H.xsub.clSub Q).subtype) H.W'_nondegenerate)
    (TauCeti.QuadraticMap.orthogonalGroup (H.xsub.q.comp (H.xsub.clSub Q).subtype))
  rw [hidx, inf_of_le_left (omegaGroup_le _ _)] at hmul
  omega

@[expose] noncomputable def resB₀ :
    ↥B₀ →* (H.xsub.clSub Q ≃ₗ[ZMod 2] H.xsub.clSub Q) where
  toFun b := resLE (H.xsub.clSub Q) (g := H.ρG ⟨b, H.B₀_le_N b.2⟩)
    (H.map_ρG_W' (H.B₀_quot.2 b.2))
  map_one' := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [coe_resLE, show (⟨((1 : B₀) : G), H.B₀_le_N (1 : B₀).2⟩ : H.xsub.N) = 1 from rfl,
      map_one]
    rfl
  map_mul' a b := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [coe_resLE, LinearEquiv.mul_apply, coe_resLE, coe_resLE,
      show (⟨((a * b : B₀) : G), H.B₀_le_N (a * b).2⟩ : H.xsub.N) =
        ⟨a, H.B₀_le_N a.2⟩ * ⟨b, H.B₀_le_N b.2⟩ from rfl, map_mul, LinearEquiv.mul_apply]

theorem coe_resB₀_apply (b : B₀) (w : H.xsub.clSub Q) :
    ((H.resB₀ b w : H.xsub.clSub Q) : H.xsub.Qt) = H.ρG ⟨b, H.B₀_le_N b.2⟩ w := rfl

theorem resB₀_eq_one_iff (b : B₀) : H.resB₀ b = 1 ↔ (b : G) ∈ Q := by
  constructor
  · intro h
    refine H.mem_Q_of_ρ_eq_one b.2 ((H.ρG_eq_one_iff _).mp (LinearEquiv.ext fun v => ?_))
    have hv : v ∈ H.xsub.clSub Q₀ ⊔ H.xsub.clSub Q := H.W₀_sup_W' ▸ Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    have h1 : H.ρG ⟨b, H.B₀_le_N b.2⟩ w = w := by
      rw [← H.coe_resB₀_apply b ⟨w, hw⟩, h]
      rfl
    rw [map_add, H.ρB₀_W₀ b.2 hu, h1]
    rfl
  · intro hb
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [H.coe_resB₀_apply, (H.ρG_eq_one_iff _).mpr
      (H.xsub.ρ_eq_one_of_mem (g := ⟨b, H.B₀_le_N b.2⟩) (H.Q_le hb))]
    rfl

theorem ker_resB₀ : H.resB₀.ker = Q.subgroupOf B₀ := by
  ext b
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  exact H.resB₀_eq_one_iff b

theorem card_range_resB₀ : Nat.card H.resB₀.range = 25920 := by
  have h := Subgroup.card_ker_mul_card_range H.resB₀
  rw [H.ker_resB₀, Nat.card_congr (subgroupOfEquivOfLe H.B₀_quot.1).toEquiv, H.B₀_card] at h
  have hQ : 0 < Nat.card Q := Nat.card_pos
  rw [mul_comm 25920] at h
  exact Nat.eq_of_mul_eq_mul_left hQ h

theorem resB₀_mem_omega (b : B₀) :
    H.resB₀ b ∈ omegaGroup (H.xsub.q.comp (H.xsub.clSub Q).subtype) H.W'_nondegenerate := by
  have hΩ : H.ρG ⟨b, H.B₀_le_N b.2⟩ ∈ omegaGroup H.xsub.q H.xsub.q_nondegenerate :=
    H.ρB₀_le_omega ⟨b, rfl⟩
  have hsplit := finrank_commSpace_split H.W₀_sup_W' H.W₀_inf_W'
    (H.map_ρG_W₀ (n := ⟨b, H.B₀_le_N b.2⟩) (centralizer_le_normalizer _ (H.B₀_le b.2)))
    (H.map_ρG_W' (n := ⟨b, H.B₀_le_N b.2⟩) (H.B₀_quot.2 b.2))
  have h0 : (H.xsub.clSub Q₀).map
      ((H.ρG ⟨b, H.B₀_le_N b.2⟩ : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) - 1) = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, H.ρB₀_W₀ b.2 hw,
      sub_self]
    exact Submodule.zero_mem _
  rw [h0, finrank_bot, zero_add] at hsplit
  rw [mem_omegaGroup]
  refine ⟨resLE_mem_orthogonalGroup (H.xsub.ρ ⟨b, H.B₀_le_N b.2⟩).2 _, ?_⟩
  change Even (finrank (ZMod 2) (commSpace (resLE (H.xsub.clSub Q)
    (H.map_ρG_W' (n := ⟨b, H.B₀_le_N b.2⟩) (H.B₀_quot.2 b.2)))))
  rw [finrank_commSpace_resLE, ← hsplit]
  exact (mem_omegaGroup.mp hΩ).2

theorem range_resB₀ :
    H.resB₀.range = omegaGroup (H.xsub.q.comp (H.xsub.clSub Q).subtype) H.W'_nondegenerate := by
  have : Finite (H.xsub.clSub Q ≃ₗ[ZMod 2] H.xsub.clSub Q) :=
    Finite.of_injective (fun e : H.xsub.clSub Q ≃ₗ[ZMod 2] H.xsub.clSub Q =>
      (e : H.xsub.clSub Q → H.xsub.clSub Q)) DFunLike.coe_injective
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨b, rfl⟩
    exact H.resB₀_mem_omega b
  · rw [H.card_range_resB₀]
    exact H.card_omega_W'_le

theorem K₀_le_centralizer : H.K₀ ≤ centralizer (H.ρX : Set _) := by
  refine sup_le ?_ H.ρB₀_le_centralizer
  rintro _ ⟨k, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨l, rfl⟩
  exact (Commute.zpow_zpow_self _ l k).eq

section Tau

variable {τ : G} (hτ : IsTau A₁ V x z τ)
include hτ

theorem tau_mem_normalizer_Q₀ : τ ∈ normalizer (Q₀ : Set G) := by
  have hφinj : Function.Injective ((MulAut.conj τ : MulAut G) : G →* G) :=
    (MulAut.conj τ).injective
  have e1 : τ * x⁻¹ * τ⁻¹ = x := by
    rw [show τ * x⁻¹ * τ⁻¹ = (τ * x * τ⁻¹)⁻¹ by group, hτ.inv_x, inv_inv]
  rw [mem_normalizer_iff_map_conj_eq]
  obtain ⟨e⟩ := H.q0.Q₀_iso
  refine H.q0.unique _ ?_ ?_ ⟨(Q₀.equivMapOfInjective _ hφinj).symm.trans e⟩ ?_
  · have h := map_mono (f := ((MulAut.conj τ : MulAut G) : G →* G)) H.q0.Q₀_le
    rwa [mem_normalizer_iff_map_conj_eq.mp hτ.normV] at h
  · refine G2.mem_normalizer_of_conj ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      refine ⟨x⁻¹ * q * x, by simpa using (mem_normalizer_iff.mp (inv_mem H.q0.x_Q₀) q).mp hq,
        ?_⟩
      show τ * (x⁻¹ * q * x) * τ⁻¹ = x * (τ * q * τ⁻¹) * x⁻¹
      calc τ * (x⁻¹ * q * x) * τ⁻¹ = (τ * x⁻¹ * τ⁻¹) * (τ * q * τ⁻¹) * (τ * x * τ⁻¹) := by
            group
        _ = x * (τ * q * τ⁻¹) * x⁻¹ := by rw [e1, hτ.inv_x]
    · rintro _ ⟨q, hq, rfl⟩
      refine ⟨x * q * x⁻¹, (mem_normalizer_iff.mp H.q0.x_Q₀ q).mp hq, ?_⟩
      show τ * (x * q * x⁻¹) * τ⁻¹ = x⁻¹ * (τ * q * τ⁻¹) * x
      calc τ * (x * q * x⁻¹) * τ⁻¹ = (τ * x * τ⁻¹) * (τ * q * τ⁻¹) * (τ * x⁻¹ * τ⁻¹) := by
            group
        _ = x⁻¹ * (τ * q * τ⁻¹) * x := by rw [e1, hτ.inv_x]
  · rw [Sec3.centerIn_map_of_injective _ hφinj, H.q0.center_Q₀, H.q0.dData.suz.Q_center,
      MonoidHom.map_zpowers]
    congr 1
    show τ * z * τ⁻¹ = z
    rw [hτ.comm_z, mul_inv_cancel_right]

theorem tau_mem_normalizer_B₀ : τ ∈ normalizer (B₀ : Set G) := by
  have hz : τ ∈ normalizer ((centralizer ({z} : Set G) : Subgroup G) : Set G) :=
    le_normalizer (mem_centralizer_singleton_iff.mpr hτ.comm_z)
  have hK := mem_normalizer_inf hτ.normB hz
  rw [mem_normalizer_iff_map_conj_eq] at hK ⊢
  rw [H.q0.dData.suz.B₀_eq, Subgroup.map_commutator, hK]

theorem tau_mem_normalizer_Q : τ ∈ normalizer (Q : Set G) := by
  have hφinj : Function.Injective ((MulAut.conj τ : MulAut G) : G →* G) :=
    (MulAut.conj τ).injective
  have hB₀ := H.tau_mem_normalizer_B₀ hτ
  have hQ'B₀ : Q.map ((MulAut.conj τ : MulAut G) : G →* G) ≤ B₀ := by
    have h := map_mono (f := ((MulAut.conj τ : MulAut G) : G →* G)) H.B₀_quot.1
    rwa [mem_normalizer_iff_map_conj_eq.mp hB₀] at h
  have key : ∀ b ∈ B₀, ∀ w ∈ Q.map ((MulAut.conj τ : MulAut G) : G →* G),
      b * w * b⁻¹ ∈ Q.map ((MulAut.conj τ : MulAut G) : G →* G) := by
    rintro b hb _ ⟨q, hq, rfl⟩
    have hb' : τ⁻¹ * b * τ ∈ B₀ := by
      simpa using (mem_normalizer_iff.mp (inv_mem hB₀) b).mp hb
    refine ⟨(τ⁻¹ * b * τ) * q * (τ⁻¹ * b * τ)⁻¹,
      (mem_normalizer_iff.mp (H.B₀_quot.2 hb') q).mp hq, ?_⟩
    show τ * ((τ⁻¹ * b * τ) * q * (τ⁻¹ * b * τ)⁻¹) * τ⁻¹ = b * (τ * q * τ⁻¹) * b⁻¹
    group
  have hnorm : B₀ ≤ normalizer
      ((Q.map ((MulAut.conj τ : MulAut G) : G →* G) : Subgroup G) : Set G) := fun b hb =>
    G2.mem_normalizer_of_conj (key b hb) fun w hw => by simpa using key b⁻¹ (inv_mem hb) w hw
  have hcard : Nat.card Q = Nat.card (Q.map ((MulAut.conj τ : MulAut G) : G →* G)) :=
    Nat.card_congr (Q.equivMapOfInjective _ hφinj).toEquiv
  rw [mem_normalizer_iff_map_conj_eq]
  by_cases hle : Q.map ((MulAut.conj τ : MulAut G) : G →* G) ≤ Q
  · exact Subgroup.eq_of_le_of_card_ge hle hcard.le
  · exfalso
    have h := H.B₀_simple _ hQ'B₀ hnorm hle
    have hc : Nat.card B₀ = Nat.card Q := by rw [← h, hcard]
    have hQ : 0 < Nat.card Q := Nat.card_pos
    rw [H.B₀_card] at hc
    omega

theorem tau_mem_N : τ ∈ H.xsub.N :=
  H.mem_normalizer_sup (H.tau_mem_normalizer_Q₀ hτ) (H.tau_mem_normalizer_Q hτ)

theorem ρτ_conj_ρx :
    H.ρG ⟨τ, H.tau_mem_N hτ⟩ * H.ρG ⟨x, H.x_mem_N⟩ * (H.ρG ⟨τ, H.tau_mem_N hτ⟩)⁻¹ =
      (H.ρG ⟨x, H.x_mem_N⟩)⁻¹ := by
  have e : (⟨τ, H.tau_mem_N hτ⟩ : H.xsub.N) * ⟨x, H.x_mem_N⟩ *
      (⟨τ, H.tau_mem_N hτ⟩ : H.xsub.N)⁻¹ = (⟨x, H.x_mem_N⟩ : H.xsub.N)⁻¹ := Subtype.ext hτ.inv_x
  calc H.ρG ⟨τ, H.tau_mem_N hτ⟩ * H.ρG ⟨x, H.x_mem_N⟩ * (H.ρG ⟨τ, H.tau_mem_N hτ⟩)⁻¹ =
        H.ρG ((⟨τ, H.tau_mem_N hτ⟩ : H.xsub.N) * ⟨x, H.x_mem_N⟩ *
          (⟨τ, H.tau_mem_N hτ⟩ : H.xsub.N)⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = (H.ρG ⟨x, H.x_mem_N⟩)⁻¹ := by rw [e, map_inv]

theorem ρτ_not_mem_K₀ : H.ρG ⟨τ, H.tau_mem_N hτ⟩ ∉ H.K₀ := by
  intro h
  have hc : H.ρG ⟨x, H.x_mem_N⟩ * H.ρG ⟨τ, H.tau_mem_N hτ⟩ =
      H.ρG ⟨τ, H.tau_mem_N hτ⟩ * H.ρG ⟨x, H.x_mem_N⟩ :=
    mem_centralizer_iff.mp (H.K₀_le_centralizer h) _ (mem_zpowers _)
  have h1 : H.ρG ⟨x, H.x_mem_N⟩ = (H.ρG ⟨x, H.x_mem_N⟩)⁻¹ := by
    rw [← H.ρτ_conj_ρx hτ, ← hc, mul_inv_cancel_right]
  have h2 : H.ρG ⟨x, H.x_mem_N⟩ ^ 2 = 1 := by
    calc H.ρG ⟨x, H.x_mem_N⟩ ^ 2 = H.ρG ⟨x, H.x_mem_N⟩ * (H.ρG ⟨x, H.x_mem_N⟩)⁻¹ := by
          rw [pow_two, ← h1]
      _ = 1 := mul_inv_cancel _
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [H.orderOf_ρx] at h3
  exact absurd h3 (by norm_num)

theorem finrank_W₀_tau : finrank (ZMod 2) ((H.xsub.clSub Q₀).map
    ((H.ρG ⟨τ, H.tau_mem_N hτ⟩ : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) - 1)) = 1 := by
  have hst := H.map_ρG_W₀ (n := ⟨τ, H.tau_mem_N hτ⟩) (H.tau_mem_normalizer_Q₀ hτ)
  rw [← finrank_commSpace_resLE hst]
  have hτ1 : (⟨τ, H.tau_mem_N hτ⟩ : H.xsub.N) * ⟨τ, H.tau_mem_N hτ⟩ = 1 := Subtype.ext hτ.sq
  have hsq : resLE _ hst * resLE _ hst = 1 := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [LinearEquiv.mul_apply, coe_resLE, coe_resLE, ← LinearEquiv.mul_apply, ← map_mul, hτ1,
      map_one]
    rfl
  have hne : resLE _ hst ≠ 1 := by
    intro h1
    have hfix : ∀ w ∈ H.xsub.clSub Q₀, H.ρG ⟨τ, H.tau_mem_N hτ⟩ w = w := fun w hw => by
      rw [← coe_resLE hst ⟨w, hw⟩, h1]
      rfl
    obtain ⟨a, ha, hne⟩ := H.ρx_sq_W₀
    apply hne
    have hw : H.xsub.cl a ∈ H.xsub.clSub Q₀ := H.xsub.cl_mem_clSub ha (H.Q₀_le ha)
    have hxw : H.ρG ⟨x, H.x_mem_N⟩ (H.xsub.cl a) ∈ H.xsub.clSub Q₀ := by
      rw [← H.map_ρG_W₀ (n := ⟨x, H.x_mem_N⟩) H.q0.x_Q₀]
      exact Submodule.mem_map_of_mem hw
    have e : H.ρG ⟨x, H.x_mem_N⟩ * H.ρG ⟨τ, H.tau_mem_N hτ⟩ * H.ρG ⟨x, H.x_mem_N⟩ =
        H.ρG ⟨τ, H.tau_mem_N hτ⟩ := by
      calc H.ρG ⟨x, H.x_mem_N⟩ * H.ρG ⟨τ, H.tau_mem_N hτ⟩ * H.ρG ⟨x, H.x_mem_N⟩ =
            H.ρG ⟨x, H.x_mem_N⟩ * (H.ρG ⟨τ, H.tau_mem_N hτ⟩ * H.ρG ⟨x, H.x_mem_N⟩ *
              (H.ρG ⟨τ, H.tau_mem_N hτ⟩)⁻¹) * H.ρG ⟨τ, H.tau_mem_N hτ⟩ := by group
        _ = H.ρG ⟨τ, H.tau_mem_N hτ⟩ := by rw [H.ρτ_conj_ρx hτ]; group
    have h2 := LinearEquiv.congr_fun e (H.xsub.cl a)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix _ hxw, hfix _ hw] at h2
    rw [pow_two, LinearEquiv.mul_apply]
    exact h2
  have h1 := one_le_finrank_commSpace hne
  have h2 := two_mul_finrank_commSpace_le hsq
  rw [H.finrank_W₀] at h2
  omega

theorem false_of_agree (hclaim : CentQCommX A₁ Q x) {b : G} (hb : b ∈ B₀)
    (hag : ∀ a ∈ Q, H.xsub.cl (b * a * b⁻¹) = H.xsub.cl (τ * a * τ⁻¹)) : False := by
  let D' : XSub G := ⟨Q, z, H.q0.dData.suz.q8.1, H.q0.dData.suz.Q_center⟩
  have hcN : b⁻¹ * τ ∈ D'.N := mul_mem (inv_mem (H.B₀_quot.2 hb)) (H.tau_mem_normalizer_Q hτ)
  have hzb : b * z = z * b := (mem_centralizer_iff.mp (H.B₀_le hb) z H.z_mem_Q₀).symm
  have hu : ∀ u ∈ zpowers z, b⁻¹ * u⁻¹ * b ∈ zpowers z := by
    intro u hu
    rcases H.xsub.mem_zpowers_z_iff.mp hu with h | h
    · rw [h, inv_one, mul_one, inv_mul_cancel]
      exact one_mem _
    · have h' : u = z := h
      have e2 : b⁻¹ * z * b = z := by
        rw [mul_assoc, ← hzb, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h', show b⁻¹ * z⁻¹ * b = (b⁻¹ * z * b)⁻¹ by group, e2]
      exact inv_mem (mem_zpowers _)
  have hρ : D'.ρ ⟨b⁻¹ * τ, hcN⟩ = 1 := by
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    obtain ⟨a, ha, rfl⟩ := D'.exists_cl v
    rw [D'.ρ_cl _ ha]
    change D'.cl ((b⁻¹ * τ) * a * (b⁻¹ * τ)⁻¹) = D'.cl a
    have h1 := (H.xsub.cl_eq_cl_iff (H.xsub.conj_mem (H.B₀_le_N hb) (H.Q_le ha))
      (H.xsub.conj_mem (H.tau_mem_N hτ) (H.Q_le ha))).mp (hag a ha)
    rw [D'.cl_eq_cl_iff (D'.conj_mem hcN ha) ha,
      show ((b⁻¹ * τ) * a * (b⁻¹ * τ)⁻¹)⁻¹ * a =
        b⁻¹ * ((b * a * b⁻¹)⁻¹ * (τ * a * τ⁻¹))⁻¹ * b by group]
    exact hu _ h1
  obtain ⟨d, hd, hdc⟩ := (D'.ρ_eq_one_iff _).mp hρ
  have hdQ : d ∈ Q := hd
  have hdB : d ∈ sec3B A₁ x := H.q0.dData.suz.T_le (H.q0.dData.suz.Q_le hdQ)
  have hcB : d⁻¹ * (b⁻¹ * τ) ∈ normalizer (sec3B A₁ x : Set G) :=
    mul_mem (inv_mem (le_normalizer hdB)) (mul_mem (inv_mem (le_normalizer (H.B₀_le_B hb)))
      hτ.normB)
  have hc : d⁻¹ * (b⁻¹ * τ) * x = x * (d⁻¹ * (b⁻¹ * τ)) := hclaim _ hcB hdc
  have hτx : τ * x = x⁻¹ * τ := by
    calc τ * x = τ * x * τ⁻¹ * τ := by group
      _ = x⁻¹ * τ := by rw [hτ.inv_x]
  have hbx : b⁻¹ * x⁻¹ = x⁻¹ * b⁻¹ := by
    have h := H.B₀_comm_x hb
    calc b⁻¹ * x⁻¹ = (x * b)⁻¹ := by group
      _ = (b * x)⁻¹ := by rw [h]
      _ = x⁻¹ * b⁻¹ := by group
  have hdx : d⁻¹ * x⁻¹ = x⁻¹ * d⁻¹ := by
    have h : d * x = x * d := mem_centralizer_iff.mp H.x_mem_centralizer_Q d hdQ
    calc d⁻¹ * x⁻¹ = (x * d)⁻¹ := by group
      _ = (d * x)⁻¹ := by rw [h]
      _ = x⁻¹ * d⁻¹ := by group
  have e : d⁻¹ * (b⁻¹ * τ) * x = x⁻¹ * (d⁻¹ * (b⁻¹ * τ)) := by
    calc d⁻¹ * (b⁻¹ * τ) * x = d⁻¹ * (b⁻¹ * (τ * x)) := by group
      _ = d⁻¹ * ((b⁻¹ * x⁻¹) * τ) := by rw [hτx]; group
      _ = (d⁻¹ * x⁻¹) * (b⁻¹ * τ) := by rw [hbx]; group
      _ = x⁻¹ * (d⁻¹ * (b⁻¹ * τ)) := by rw [hdx]; group
  rw [hc] at e
  have hxx : x = x⁻¹ := mul_right_cancel e
  have h2 : x ^ 2 = 1 := by
    calc x ^ 2 = x * x⁻¹ := by rw [pow_two, ← hxx]
      _ = 1 := mul_inv_cancel x
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [H.q0.dData.suz.setting.order_x] at h3
  exact absurd h3 (by norm_num)

theorem not_even_W'_tau (hclaim : CentQCommX A₁ Q x) :
    ¬ Even (finrank (ZMod 2) ((H.xsub.clSub Q).map
      ((H.ρG ⟨τ, H.tau_mem_N hτ⟩ : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) - 1))) := by
  intro hev
  have hst := H.map_ρG_W' (n := ⟨τ, H.tau_mem_N hτ⟩) (H.tau_mem_normalizer_Q hτ)
  have hmem : resLE _ hst ∈
      omegaGroup (H.xsub.q.comp (H.xsub.clSub Q).subtype) H.W'_nondegenerate := by
    rw [mem_omegaGroup]
    refine ⟨resLE_mem_orthogonalGroup (H.xsub.ρ ⟨τ, H.tau_mem_N hτ⟩).2 hst, ?_⟩
    rw [finrank_commSpace_resLE]
    exact hev
  rw [← H.range_resB₀] at hmem
  obtain ⟨b, hb⟩ := hmem
  refine H.false_of_agree hτ hclaim b.2 fun a ha => ?_
  have hw : H.xsub.cl a ∈ H.xsub.clSub Q := H.xsub.cl_mem_clSub ha (H.Q_le ha)
  have h2 : H.ρG ⟨b, H.B₀_le_N b.2⟩ (H.xsub.cl a) = H.ρG ⟨τ, H.tau_mem_N hτ⟩ (H.xsub.cl a) := by
    rw [← H.coe_resB₀_apply b ⟨_, hw⟩, hb, coe_resLE]
  rw [H.ρG_cl _ (H.Q_le ha), H.ρG_cl _ (H.Q_le ha)] at h2
  exact h2

theorem ρτ_mem_omega (hclaim : CentQCommX A₁ Q x) :
    H.ρG ⟨τ, H.tau_mem_N hτ⟩ ∈ omegaGroup H.xsub.q H.xsub.q_nondegenerate := by
  rw [mem_omegaGroup]
  refine ⟨(H.xsub.ρ ⟨τ, H.tau_mem_N hτ⟩).2, ?_⟩
  rw [finrank_commSpace_split H.W₀_sup_W' H.W₀_inf_W'
    (H.map_ρG_W₀ (n := ⟨τ, H.tau_mem_N hτ⟩) (H.tau_mem_normalizer_Q₀ hτ))
    (H.map_ρG_W' (n := ⟨τ, H.tau_mem_N hτ⟩) (H.tau_mem_normalizer_Q hτ)), H.finrank_W₀_tau hτ]
  obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp (H.not_even_W'_tau hτ hclaim)
  exact ⟨k + 1, by omega⟩

noncomputable abbrev K₁ : Subgroup (H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt) :=
  H.K₀ ⊔ zpowers (H.ρG ⟨τ, H.tau_mem_N hτ⟩)

theorem card_K₁ : 155520 ≤ Nat.card (H.K₁ hτ) := by
  have h := Subgroup.relIndex_mul_card H.K₀ (H.K₁ hτ)
  rw [inf_of_le_left le_sup_left, H.card_K₀] at h
  have hne : H.K₀.relIndex (H.K₁ hτ) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    exact H.ρτ_not_mem_K₀ hτ (hle (mem_sup_right (mem_zpowers _)))
  have hpos : 0 < Nat.card (H.K₁ hτ) := Nat.card_pos
  omega

theorem K₁_le_range : H.K₁ hτ ≤ H.ρG.range :=
  sup_le H.K₀_le_range (by rw [zpowers_le]; exact ⟨_, rfl⟩)

theorem K₁_le_omega (hclaim : CentQCommX A₁ Q x) :
    H.K₁ hτ ≤ omegaGroup H.xsub.q H.xsub.q_nondegenerate :=
  sup_le H.K₀_le_omega (by rw [zpowers_le]; exact H.ρτ_mem_omega hτ hclaim)

theorem K₁_le_glStab : H.K₁ hτ ≤ H.glStab (H.xsub.clSub Q₀) :=
  sup_le H.K₀_le_glStab (by rw [zpowers_le]; exact H.ρG_mem_glStab (H.tau_mem_normalizer_Q₀ hτ))

theorem mem_range_of_stab (hclaim : CentQCommX A₁ Q x)
    (hS : Nat.card (MinusLines.omegaStab H.xsub.q_nondegenerate (H.xsub.clSub Q₀)) ≤ 155520)
    {k : H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt} (hk : k ∈ omegaGroup H.xsub.q H.xsub.q_nondegenerate)
    (hkW : (H.xsub.clSub Q₀).map (k : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) = H.xsub.clSub Q₀) :
    k ∈ H.ρG.range := by
  let S := (MinusLines.omegaStab H.xsub.q_nondegenerate (H.xsub.clSub Q₀)).map
    (omegaGroup H.xsub.q H.xsub.q_nondegenerate).subtype
  have hle : H.K₁ hτ ≤ S := fun m hm =>
    ⟨⟨m, H.K₁_le_omega hτ hclaim hm⟩, H.K₁_le_glStab hτ hm, rfl⟩
  have hcard : Nat.card S =
      Nat.card (MinusLines.omegaStab H.xsub.q_nondegenerate (H.xsub.clSub Q₀)) :=
    Subgroup.card_map_of_injective (omegaGroup _ _).subtype_injective
  have heq : H.K₁ hτ = S :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact hS.trans (H.card_K₁ hτ))
  have hkS : k ∈ S := ⟨⟨k, hk⟩, hkW, rfl⟩
  rw [← heq] at hkS
  exact H.K₁_le_range hτ hkS

end Tau

end Sec38Hyp

end CFSG.ComponentClassification.AS81
