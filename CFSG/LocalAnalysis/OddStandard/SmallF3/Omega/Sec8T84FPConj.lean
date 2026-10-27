module

public import Certificates.Certificate442267
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup Matrix Certificates.Asc82NormA6
open Certificates.A5GL42 (Mat4)

@[expose] def sec8t84RhoGL (F : Facts) : Equiv.Perm (Fin 6) →* GL (Fin 4) (ZMod 2) :=
  ({ toFun := rho, map_one' := F.rho_one, map_mul' := F.rho_mul } :
    Equiv.Perm (Fin 6) →* Mat4).toHomUnits

theorem sec8t84RhoGL_coe (F : Facts) (p : Equiv.Perm (Fin 6)) :
    ((sec8t84RhoGL F p : GL (Fin 4) (ZMod 2)) : Mat4) = rho p := rfl

theorem sec8t84RhoGL_injective (F : Facts) : Function.Injective (sec8t84RhoGL F) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  apply F.rho_ker p
  have h : ((sec8t84RhoGL F p : GL (Fin 4) (ZMod 2)) : Mat4) = 1 := by rw [hp]; rfl
  rwa [sec8t84RhoGL_coe] at h

private lemma t84Rel_map {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {x y : M}
    (h : Rel x y) : Rel (f x) (f y) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨by simpa using congrArg f h1, by simpa using congrArg f h2,
    by simpa using congrArg f h3, by simpa using congrArg f h4,
    by simpa using congrArg f h5, by simpa using congrArg f h6⟩

private lemma t84Rel_subtype {G : Type*} [Group G] {H : Subgroup G} {x y : ↥H}
    (h : Rel (x : G) (y : G)) : Rel x y := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨Subtype.ext (by simpa using h1), Subtype.ext (by simpa using h2),
    Subtype.ext (by simpa using h3), Subtype.ext (by simpa using h4),
    Subtype.ext (by simpa using h5), Subtype.ext (by simpa using h6)⟩

private def t84sigmaA (F : Facts) : ↥(alternatingGroup (Fin 6)) :=
  ⟨sigma, Equiv.Perm.mem_alternatingGroup.mpr F.sigma_even⟩

private def t84tauA (F : Facts) : ↥(alternatingGroup (Fin 6)) :=
  ⟨tau, Equiv.Perm.mem_alternatingGroup.mpr F.tau_even⟩

private lemma t84rel_sigmaA_tauA (F : Facts) : Rel (t84sigmaA F) (t84tauA F) :=
  t84Rel_subtype (by simpa [t84sigmaA, t84tauA] using F.rel)

private lemma t84sigma_ne_one : sigma ≠ 1 := by
  intro h
  have h0 : sigma 0 = (1 : Equiv.Perm (Fin 6)) 0 := by rw [h]
  exact absurd h0 (by decide)

private lemma t84closure_sigmaA_tauA_eq_top (F : Facts) :
    Subgroup.closure ({t84sigmaA F, t84tauA F} : Set ↥(alternatingGroup (Fin 6))) = ⊤ := by
  apply le_antisymm le_top
  intro m _
  have hle : Subgroup.closure ({sigma, tau} : Set (Equiv.Perm (Fin 6))) ≤
      (Subgroup.closure ({t84sigmaA F, t84tauA F} : Set ↥(alternatingGroup (Fin 6)))).map
        (alternatingGroup (Fin 6)).subtype := by
    rw [Subgroup.closure_le]
    rintro p (rfl | rfl)
    · exact Subgroup.mem_map.mpr
        ⟨t84sigmaA F, Subgroup.subset_closure (by simp), rfl⟩
    · exact Subgroup.mem_map.mpr
        ⟨t84tauA F, Subgroup.subset_closure (by simp), rfl⟩
  have hgen := F.gen m.1 (Equiv.Perm.mem_alternatingGroup.mp m.2)
  obtain ⟨n, hn, hnm⟩ := Subgroup.mem_map.mp (hle hgen)
  have hnm' : n = m := Subtype.ext hnm
  rwa [hnm'] at hn

private lemma t84exists_conj_rel (F : Facts) {x y : GL (Fin 4) (ZMod 2)}
    (hrel : Rel x y) (hx : x ≠ 1) :
    ∃ g : GL (Fin 4) (ZMod 2), ∃ a b : Equiv.Perm (Fin 6), a.sign = 1 ∧ b.sign = 1 ∧
      g⁻¹ * x * g = sec8t84RhoGL F a ∧ g⁻¹ * y * g = sec8t84RhoGL F b := by
  have hrel' : Rel (x : Mat4) (y : Mat4) := by
    simpa using t84Rel_map (Units.coeHom Mat4) hrel
  have hx' : (x : Mat4) ≠ 1 := fun h => hx (Units.ext h)
  obtain ⟨c, c', hcc', ⟨a, ha, haeq⟩, ⟨b, hb, hbeq⟩⟩ :=
    F.classify (x : Mat4) (y : Mat4) hrel' hx'
  have hc'c : c' * c = 1 := mul_eq_one_comm.mp hcc'
  let g : GL (Fin 4) (ZMod 2) := ⟨c, c', hcc', hc'c⟩
  exact ⟨g, a, b, ha, hb, Units.ext haeq.symm, Units.ext hbeq.symm⟩

private lemma t84H1_le_conj (F : Facts) (H₁ : Subgroup (GL (Fin 4) (ZMod 2)))
    (varphi : ↥(alternatingGroup (Fin 6)) ≃* ↥H₁) (g : GL (Fin 4) (ZMod 2))
    (a b : Equiv.Perm (Fin 6)) (ha : a.sign = 1) (hb : b.sign = 1)
    (hgx : g⁻¹ * ((varphi (t84sigmaA F) : ↥H₁) : GL (Fin 4) (ZMod 2)) * g =
      sec8t84RhoGL F a)
    (hgy : g⁻¹ * ((varphi (t84tauA F) : ↥H₁) : GL (Fin 4) (ZMod 2)) * g =
      sec8t84RhoGL F b) :
    H₁ ≤ ((alternatingGroup (Fin 6)).map (sec8t84RhoGL F)).map
      (MulAut.conj g).toMonoidHom := by
  intro h hh
  obtain ⟨m, hm⟩ := varphi.surjective ⟨h, hh⟩
  have hm' : ((varphi m : ↥H₁) : GL (Fin 4) (ZMod 2)) = h := congrArg Subtype.val hm
  rw [← hm']
  have hmem_clos : m ∈ Subgroup.closure ({t84sigmaA F, t84tauA F} :
      Set ↥(alternatingGroup (Fin 6))) := by
    rw [t84closure_sigmaA_tauA_eq_top F]
    exact Subgroup.mem_top m
  refine Subgroup.closure_induction
    (p := fun t _ => ((varphi t : ↥H₁) : GL (Fin 4) (ZMod 2)) ∈
      ((alternatingGroup (Fin 6)).map (sec8t84RhoGL F)).map (MulAut.conj g).toMonoidHom)
    ?_ ?_ ?_ ?_ hmem_clos
  · intro t ht
    rcases ht with rfl | rfl
    · have hx_eq : ((varphi (t84sigmaA F) : ↥H₁) : GL (Fin 4) (ZMod 2)) =
          g * sec8t84RhoGL F a * g⁻¹ := by
        rw [← hgx]; group
      exact Subgroup.mem_map.mpr ⟨sec8t84RhoGL F a,
        Subgroup.mem_map.mpr ⟨a, Equiv.Perm.mem_alternatingGroup.mpr ha, rfl⟩,
        by simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hx_eq.symm⟩
    · have hy_eq : ((varphi (t84tauA F) : ↥H₁) : GL (Fin 4) (ZMod 2)) =
          g * sec8t84RhoGL F b * g⁻¹ := by
        rw [← hgy]; group
      exact Subgroup.mem_map.mpr ⟨sec8t84RhoGL F b,
        Subgroup.mem_map.mpr ⟨b, Equiv.Perm.mem_alternatingGroup.mpr hb, rfl⟩,
        by simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hy_eq.symm⟩
  · simpa using Subgroup.one_mem _
  · intro x y _ _ ihx ihy
    simpa using Subgroup.mul_mem _ ihx ihy
  · intro x _ ih
    simpa using Subgroup.inv_mem _ ih

private lemma t84H1_eq_conj_map (F : Facts) (H₁ : Subgroup (GL (Fin 4) (ZMod 2)))
    (varphi : ↥(alternatingGroup (Fin 6)) ≃* ↥H₁) (g : GL (Fin 4) (ZMod 2))
    (a b : Equiv.Perm (Fin 6)) (ha : a.sign = 1) (hb : b.sign = 1)
    (hgx : g⁻¹ * ((varphi (t84sigmaA F) : ↥H₁) : GL (Fin 4) (ZMod 2)) * g =
      sec8t84RhoGL F a)
    (hgy : g⁻¹ * ((varphi (t84tauA F) : ↥H₁) : GL (Fin 4) (ZMod 2)) * g =
      sec8t84RhoGL F b) :
    H₁ = ((alternatingGroup (Fin 6)).map (sec8t84RhoGL F)).map
      (MulAut.conj g).toMonoidHom := by
  apply Subgroup.eq_of_le_of_card_ge (t84H1_le_conj F H₁ varphi g a b ha hb hgx hgy)
  rw [Subgroup.card_map_of_injective (K := (alternatingGroup (Fin 6)).map (sec8t84RhoGL F))
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
      Subgroup.card_map_of_injective (K := alternatingGroup (Fin 6))
        (f := sec8t84RhoGL F) (sec8t84RhoGL_injective F)]
  exact le_of_eq (Nat.card_congr varphi.toEquiv)

theorem sec8t84_a6_conj_gl (H : Subgroup (GL (Fin 4) (ZMod 2)))
    (hH : Nonempty (↥H ≃* alternatingGroup (Fin 6))) :
    ∃ g : GL (Fin 4) (ZMod 2), H = ((alternatingGroup (Fin 6)).map
      (sec8t84RhoGL Certificates.certificate442267)).map (MulAut.conj g).toMonoidHom := by
  let varphi : ↥(alternatingGroup (Fin 6)) ≃* ↥H := hH.some.symm
  let x : GL (Fin 4) (ZMod 2) :=
    ((varphi (t84sigmaA Certificates.certificate442267) : ↥H) :
      GL (Fin 4) (ZMod 2))
  let y : GL (Fin 4) (ZMod 2) :=
    ((varphi (t84tauA Certificates.certificate442267) : ↥H) :
      GL (Fin 4) (ZMod 2))
  have hrelx : Rel x y := by
    simpa [x, y] using t84Rel_map H.subtype
      (t84Rel_map varphi.toMonoidHom
        (t84rel_sigmaA_tauA Certificates.certificate442267))
  have hxne : x ≠ 1 := by
    intro hx1
    have h1 : varphi (t84sigmaA Certificates.certificate442267) = 1 :=
      Subtype.ext hx1
    have h2 : t84sigmaA Certificates.certificate442267 = 1 :=
      varphi.injective (by rw [h1, map_one])
    have h3 : sigma = 1 := by
      have := congrArg (fun u : ↥(alternatingGroup (Fin 6)) => (u : Equiv.Perm (Fin 6))) h2
      simpa [t84sigmaA] using this
    exact t84sigma_ne_one h3
  obtain ⟨g, a, b, ha, hb, hgx, hgy⟩ :=
    t84exists_conj_rel Certificates.certificate442267 hrelx hxne
  exact ⟨g, t84H1_eq_conj_map Certificates.certificate442267 H varphi g a b
    ha hb hgx hgy⟩

private lemma t84_alpha_toAdd {α : MulAut (Multiplicative (Fin 4 → ZMod 2))}
    {m : GL (Fin 4) (ZMod 2)}
    (hα : CFSG.SectionRank.Ccomm.mulAutEquivGL (p := 2) 4 α = m) (v : Fin 4 → ZMod 2) :
    Multiplicative.toAdd (α (Multiplicative.ofAdd v)) = (m : Mat4) *ᵥ v := by
  have h := CFSG.SectionRank.Ccomm.mulAutEquivGL_mulVec (p := 2) 4 α v
  rw [hα] at h
  exact h.symm

private lemma t84_unit_mulVec (u v : GL (Fin 4) (ZMod 2)) (w : Fin 4 → ZMod 2) :
    (u : Mat4) *ᵥ ((v : Mat4) *ᵥ w) = ((u * v : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ w := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

private lemma t84_conj_action {W : Type*} [Group W]
    (e₀ : W ≃* Multiplicative (Fin 4 → ZMod 2))
    (α : MulAut (Multiplicative (Fin 4 → ZMod 2))) (g : GL (Fin 4) (ZMod 2))
    (hα : CFSG.SectionRank.Ccomm.mulAutEquivGL (p := 2) 4 α = g⁻¹)
    (h : MulAut W) (M : GL (Fin 4) (ZMod 2))
    (hΦ : CFSG.SectionRank.Ccomm.elemAutEquivGL e₀ h = g * M * g⁻¹) :
    ∀ b : W, Multiplicative.toAdd ((e₀.trans α) (h b)) =
      (M : Mat4) *ᵥ Multiplicative.toAdd ((e₀.trans α) b) := by
  intro b
  let ginv : GL (Fin 4) (ZMod 2) := g⁻¹
  have hα' : CFSG.SectionRank.Ccomm.mulAutEquivGL (p := 2) 4 α = ginv := by
    simpa only [ginv] using hα
  change Multiplicative.toAdd (α (e₀ (h b))) =
    (M : Mat4) *ᵥ Multiplicative.toAdd (α (e₀ b))
  have h1 := t84_alpha_toAdd hα' (Multiplicative.toAdd (e₀ (h b)))
  have h2 := t84_alpha_toAdd hα' (Multiplicative.toAdd (e₀ b))
  simp only [ofAdd_toAdd] at h1 h2
  rw [h1, h2, ← CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e₀ h b]
  rw [t84_unit_mulVec ginv (CFSG.SectionRank.Ccomm.elemAutEquivGL e₀ h)]
  rw [t84_unit_mulVec M ginv]
  have hmul : (ginv * CFSG.SectionRank.Ccomm.elemAutEquivGL e₀ h :
      GL (Fin 4) (ZMod 2)) = M * ginv := by
    rw [show ginv = g⁻¹ from rfl, hΦ]; group
  rw [hmul]

theorem sec8t84_a6_conj {G : Type} [Group G]
    (B : Subgroup G) (hB : IsElemAb2 B 4) (H : Subgroup (MulAut ↥B))
    (hH : Nonempty (↥H ≃* alternatingGroup (Fin 6))) :
    ∃ (e : ↥B ≃* Multiplicative (Fin 4 → ZMod 2)) (ψ : ↥H ≃* alternatingGroup (Fin 6)),
      (∀ (h : ↥H) (b : ↥B), Multiplicative.toAdd (e ((h : MulAut ↥B) b)) =
        rho ((ψ h : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) *ᵥ
          Multiplicative.toAdd (e b)) ∧
      ∀ h : MulAut ↥B, h ∈ H ↔ ∃ a : Equiv.Perm (Fin 6), a.sign = 1 ∧
        ∀ b : ↥B, Multiplicative.toAdd (e (h b)) = rho a *ᵥ Multiplicative.toAdd (e b) := by
  have hcomm : ∀ a b : ↥B, a * b = b * a := fun a b => hB.1.1.is_comm.comm a b
  have hpow : ∀ a : ↥B, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hB.1.2 (a : G) a.2)
  haveI : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [hB.2]; norm_num)
  obtain ⟨e₀⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (W := ↥B) hcomm hpow (n := 4) hB.2
  let Φ : MulAut ↥B ≃* GL (Fin 4) (ZMod 2) := CFSG.SectionRank.Ccomm.elemAutEquivGL e₀
  let H' : Subgroup (GL (Fin 4) (ZMod 2)) :=
    H.map (Φ : MulAut ↥B →* GL (Fin 4) (ZMod 2))
  have hH' : Nonempty (↥H' ≃* alternatingGroup (Fin 6)) :=
    ⟨(Φ.subgroupMap H).symm.trans hH.some⟩
  obtain ⟨g, hg⟩ := sec8t84_a6_conj_gl H' hH'
  let R : Equiv.Perm (Fin 6) →* GL (Fin 4) (ZMod 2) :=
    sec8t84RhoGL Certificates.certificate442267
  let K : Subgroup (GL (Fin 4) (ZMod 2)) :=
    Subgroup.map (MulAut.conj g) (Subgroup.map R (alternatingGroup (Fin 6)))
  have hg' : H' = K := by
    simpa only [K, R, MulEquiv.toMonoidHom_eq_coe] using hg
  let α : MulAut (Multiplicative (Fin 4 → ZMod 2)) :=
    (CFSG.SectionRank.Ccomm.mulAutEquivGL (p := 2) 4).symm g⁻¹
  let e : ↥B ≃* Multiplicative (Fin 4 → ZMod 2) := e₀.trans α
  let ψ : ↥H ≃* alternatingGroup (Fin 6) :=
    (Φ.subgroupMap H).trans
      ((MulEquiv.subgroupCongr hg').trans
        (((MulAut.conj g).subgroupMap ((alternatingGroup (Fin 6)).map R)).symm.trans
          (Subgroup.equivMapOfInjective (alternatingGroup (Fin 6)) R
            (sec8t84RhoGL_injective Certificates.certificate442267)).symm))
  have hΦ_eq : ∀ h : ↥H, Φ (h : MulAut ↥B) = g * R (ψ h) * g⁻¹ := by
    intro h
    have hψ : ψ h = (Subgroup.equivMapOfInjective (alternatingGroup (Fin 6)) R
        (sec8t84RhoGL_injective Certificates.certificate442267)).symm
        (((MulAut.conj g).subgroupMap ((alternatingGroup (Fin 6)).map R)).symm
          (MulEquiv.subgroupCongr hg' (Φ.subgroupMap H h))) := rfl
    have hR : R (ψ h) = g⁻¹ * Φ (h : MulAut ↥B) * g := by
      rw [← Subgroup.coe_equivMapOfInjective_apply (alternatingGroup (Fin 6)) R
        (sec8t84RhoGL_injective Certificates.certificate442267) (ψ h)]
      rw [hψ, MulEquiv.apply_symm_apply]
      simp only [Subtype.coe_mk, MulEquiv.subgroupMap_symm_apply,
        MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply,
        MulAut.conj_symm_apply]
    rw [hR]
    group
  have hα : CFSG.SectionRank.Ccomm.mulAutEquivGL (p := 2) 4 α = g⁻¹ :=
    (CFSG.SectionRank.Ccomm.mulAutEquivGL (p := 2) 4).apply_symm_apply g⁻¹
  have hact : ∀ (h : ↥H) (b : ↥B),
      Multiplicative.toAdd (e ((h : MulAut ↥B) b)) =
        rho (((ψ h : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) *ᵥ
          Multiplicative.toAdd (e b) := by
    intro h b
    have hkey := t84_conj_action e₀ α g hα (h : MulAut ↥B) (R (ψ h)) (hΦ_eq h) b
    simpa [e, R, sec8t84RhoGL_coe] using hkey
  refine ⟨e, ψ, hact, ?_⟩
  intro h
  constructor
  · intro hh
    exact ⟨((ψ ⟨h, hh⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)),
      Equiv.Perm.mem_alternatingGroup.mp (ψ ⟨h, hh⟩).2, hact ⟨h, hh⟩⟩
  · rintro ⟨a, ha, hact_a⟩
    let h₀ : ↥H := ψ.symm ⟨a, Equiv.Perm.mem_alternatingGroup.mpr ha⟩
    have hψh₀ : (ψ h₀ : alternatingGroup (Fin 6)) =
        ⟨a, Equiv.Perm.mem_alternatingGroup.mpr ha⟩ :=
      ψ.apply_symm_apply _
    have h0act : ∀ b : ↥B, Multiplicative.toAdd (e ((h₀ : MulAut ↥B) b)) =
        rho a *ᵥ Multiplicative.toAdd (e b) := by
      intro b
      have h := hact h₀ b
      rw [hψh₀] at h
      simpa using h
    have heq : h = (h₀ : MulAut ↥B) := by
      apply MulEquiv.ext
      intro b
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [hact_a b, h0act b]
    rw [heq]
    exact h₀.2

end CFSG.OddStandard.SmallF3.Omega
