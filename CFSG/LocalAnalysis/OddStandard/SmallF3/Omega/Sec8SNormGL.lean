module

public import Certificates.Data.Asc82NormA6

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup Certificates.Asc82NormA6
open Certificates.A5GL42 (Mat4)

private def Rm (F : Facts) : Equiv.Perm (Fin 6) →* Mat4 where
  toFun := rho
  map_one' := F.rho_one
  map_mul' := F.rho_mul

private def R (F : Facts) : Equiv.Perm (Fin 6) →* GL (Fin 4) (ZMod 2) :=
  (Rm F).toHomUnits

private lemma R_coe (F : Facts) (p : Equiv.Perm (Fin 6)) :
    ((R F p : GL (Fin 4) (ZMod 2)) : Mat4) = rho p := rfl

private lemma R_injective (F : Facts) : Function.Injective (R F) := by
  rw [injective_iff_map_eq_one']
  intro p
  constructor
  · intro hp
    apply F.rho_ker p
    have h : ((R F p : GL (Fin 4) (ZMod 2)) : Mat4) = 1 := by rw [hp]; rfl
    rwa [R_coe] at h
  · intro hp
    rw [hp, map_one]

private lemma Rel.map {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {x y : M}
    (h : Rel x y) : Rel (f x) (f y) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨by simpa using congrArg f h1, by simpa using congrArg f h2,
    by simpa using congrArg f h3, by simpa using congrArg f h4,
    by simpa using congrArg f h5, by simpa using congrArg f h6⟩

private lemma Rel.subtype {G : Type*} [Group G] {H : Subgroup G} {x y : ↥H}
    (h : Rel (x : G) (y : G)) : Rel x y := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨Subtype.ext (by simpa using h1), Subtype.ext (by simpa using h2),
    Subtype.ext (by simpa using h3), Subtype.ext (by simpa using h4),
    Subtype.ext (by simpa using h5), Subtype.ext (by simpa using h6)⟩

private def sigmaA (F : Facts) : ↥(alternatingGroup (Fin 6)) :=
  ⟨sigma, Equiv.Perm.mem_alternatingGroup.mpr F.sigma_even⟩

private def tauA (F : Facts) : ↥(alternatingGroup (Fin 6)) :=
  ⟨tau, Equiv.Perm.mem_alternatingGroup.mpr F.tau_even⟩

private lemma rel_sigmaA_tauA (F : Facts) : Rel (sigmaA F) (tauA F) :=
  Rel.subtype (by simpa [sigmaA, tauA] using F.rel)

private lemma sigma_ne_one : sigma ≠ 1 := by
  intro h
  have h0 : sigma 0 = (1 : Equiv.Perm (Fin 6)) 0 := by rw [h]
  exact absurd h0 (by decide)

private lemma closure_sigmaA_tauA_eq_top (F : Facts) :
    Subgroup.closure ({sigmaA F, tauA F} : Set ↥(alternatingGroup (Fin 6))) = ⊤ := by
  apply le_antisymm le_top
  intro m _
  have hle : Subgroup.closure ({sigma, tau} : Set (Equiv.Perm (Fin 6))) ≤
      (Subgroup.closure ({sigmaA F, tauA F} : Set ↥(alternatingGroup (Fin 6)))).map
        (alternatingGroup (Fin 6)).subtype := by
    rw [Subgroup.closure_le]
    rintro p (rfl | rfl)
    · exact Subgroup.mem_map.mpr ⟨sigmaA F, Subgroup.subset_closure (by simp), rfl⟩
    · exact Subgroup.mem_map.mpr ⟨tauA F, Subgroup.subset_closure (by simp), rfl⟩
  have hgen := F.gen m.1 (Equiv.Perm.mem_alternatingGroup.mp m.2)
  obtain ⟨n, hn, hnm⟩ := Subgroup.mem_map.mp (hle hgen)
  have hnm' : n = m := Subtype.ext hnm
  rwa [hnm'] at hn

private lemma exists_conj_rel (F : Facts) {x y : GL (Fin 4) (ZMod 2)}
    (hrel : Rel x y) (hx : x ≠ 1) :
    ∃ g : GL (Fin 4) (ZMod 2), ∃ a b : Equiv.Perm (Fin 6), a.sign = 1 ∧ b.sign = 1 ∧
      g⁻¹ * x * g = R F a ∧ g⁻¹ * y * g = R F b := by
  have hrel' : Rel (x : Mat4) (y : Mat4) := by
    simpa using Rel.map (Units.coeHom Mat4) hrel
  have hx' : (x : Mat4) ≠ 1 := fun h => hx (Units.ext h)
  obtain ⟨c, c', hcc', ⟨a, ha, haeq⟩, ⟨b, hb, hbeq⟩⟩ :=
    F.classify (x : Mat4) (y : Mat4) hrel' hx'
  have hc'c : c' * c = 1 := mul_eq_one_comm.mp hcc'
  let g : GL (Fin 4) (ZMod 2) := ⟨c, c', hcc', hc'c⟩
  refine ⟨g, a, b, ha, hb, ?_, ?_⟩
  · apply Units.ext
    change c' * (x : Mat4) * c = rho a
    exact haeq.symm
  · apply Units.ext
    change c' * (y : Mat4) * c = rho b
    exact hbeq.symm

private lemma H1_le_conj (F : Facts) (H₁ : Subgroup (GL (Fin 4) (ZMod 2)))
    (varphi : ↥(alternatingGroup (Fin 6)) ≃* ↥H₁) (g : GL (Fin 4) (ZMod 2))
    (a b : Equiv.Perm (Fin 6)) (ha : a.sign = 1) (hb : b.sign = 1)
    (hgx : g⁻¹ * ((varphi (sigmaA F) : ↥H₁) : GL (Fin 4) (ZMod 2)) * g = R F a)
    (hgy : g⁻¹ * ((varphi (tauA F) : ↥H₁) : GL (Fin 4) (ZMod 2)) * g = R F b) :
    H₁ ≤ ((alternatingGroup (Fin 6)).map (R F)).map (MulAut.conj g).toMonoidHom := by
  intro h hh
  obtain ⟨m, hm⟩ := varphi.surjective ⟨h, hh⟩
  have hm' : ((varphi m : ↥H₁) : GL (Fin 4) (ZMod 2)) = h := congrArg Subtype.val hm
  rw [← hm']
  have hmem_clos : m ∈ Subgroup.closure ({sigmaA F, tauA F} : Set ↥(alternatingGroup (Fin 6))) := by
    rw [closure_sigmaA_tauA_eq_top F]
    exact Subgroup.mem_top m
  refine Subgroup.closure_induction
    (p := fun t _ => ((varphi t : ↥H₁) : GL (Fin 4) (ZMod 2)) ∈
      ((alternatingGroup (Fin 6)).map (R F)).map (MulAut.conj g).toMonoidHom)
    ?_ ?_ ?_ ?_ hmem_clos
  · intro t ht
    rcases ht with rfl | rfl
    · have hx_eq : ((varphi (sigmaA F) : ↥H₁) : GL (Fin 4) (ZMod 2)) = g * R F a * g⁻¹ := by
        rw [← hgx]; group
      exact Subgroup.mem_map.mpr ⟨R F a,
        Subgroup.mem_map.mpr ⟨a, Equiv.Perm.mem_alternatingGroup.mpr ha, rfl⟩,
        by simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hx_eq.symm⟩
    · have hy_eq : ((varphi (tauA F) : ↥H₁) : GL (Fin 4) (ZMod 2)) = g * R F b * g⁻¹ := by
        rw [← hgy]; group
      exact Subgroup.mem_map.mpr ⟨R F b,
        Subgroup.mem_map.mpr ⟨b, Equiv.Perm.mem_alternatingGroup.mpr hb, rfl⟩,
        by simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hy_eq.symm⟩
  · simpa using Subgroup.one_mem _
  · intro x y _ _ ihx ihy
    simpa using Subgroup.mul_mem _ ihx ihy
  · intro x _ ih
    simpa using Subgroup.inv_mem _ ih

private lemma H1_eq_conj_map (F : Facts) (H₁ : Subgroup (GL (Fin 4) (ZMod 2)))
    (varphi : ↥(alternatingGroup (Fin 6)) ≃* ↥H₁) (g : GL (Fin 4) (ZMod 2))
    (a b : Equiv.Perm (Fin 6)) (ha : a.sign = 1) (hb : b.sign = 1)
    (hgx : g⁻¹ * ((varphi (sigmaA F) : ↥H₁) : GL (Fin 4) (ZMod 2)) * g = R F a)
    (hgy : g⁻¹ * ((varphi (tauA F) : ↥H₁) : GL (Fin 4) (ZMod 2)) * g = R F b) :
    H₁ = ((alternatingGroup (Fin 6)).map (R F)).map (MulAut.conj g).toMonoidHom := by
  apply Subgroup.eq_of_le_of_card_ge (H1_le_conj F H₁ varphi g a b ha hb hgx hgy)
  rw [Subgroup.card_map_of_injective (K := (alternatingGroup (Fin 6)).map (R F))
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
      Subgroup.card_map_of_injective (K := alternatingGroup (Fin 6))
        (f := R F) (R_injective F)]
  exact le_of_eq (Nat.card_congr varphi.toEquiv)

private lemma S_le_conj_H2 (F : Facts) (H₁ H₂ : Subgroup (GL (Fin 4) (ZMod 2)))
    (h12 : H₁ ≤ H₂) (g : GL (Fin 4) (ZMod 2))
    (hH1 : H₁ = ((alternatingGroup (Fin 6)).map (R F)).map (MulAut.conj g).toMonoidHom) :
    (alternatingGroup (Fin 6)).map (R F) ≤ H₂.map (MulAut.conj g⁻¹).toMonoidHom := by
  intro s hs
  have hKs : MulAut.conj g s ∈ H₁ := by
    rw [hH1]
    exact Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
  have hH₂ : MulAut.conj g s ∈ H₂ := h12 hKs
  have hself : s = MulAut.conj g⁻¹ (MulAut.conj g s) := by
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [hself]
  exact Subgroup.mem_map.mpr ⟨MulAut.conj g s, hH₂, rfl⟩

private lemma conj_H2_le_range (F : Facts) (H₁ H₂ : Subgroup (GL (Fin 4) (ZMod 2)))
    (h12 : H₁ ≤ H₂) (hnorm : ∀ h ∈ H₂, ∀ a ∈ H₁, h * a * h⁻¹ ∈ H₁)
    (g : GL (Fin 4) (ZMod 2))
    (hH1 : H₁ = ((alternatingGroup (Fin 6)).map (R F)).map (MulAut.conj g).toMonoidHom) :
    H₂.map (MulAut.conj g⁻¹).toMonoidHom ≤ (R F).range := by
  have hS : (alternatingGroup (Fin 6)).map (R F) ≤ H₂.map (MulAut.conj g⁻¹).toMonoidHom :=
    S_le_conj_H2 F H₁ H₂ h12 g hH1
  intro h' hh'
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hh'
  rw [MonoidHom.mem_range]
  have hkey : ∀ a : Equiv.Perm (Fin 6), a.sign = 1 →
      ∃ a' : Equiv.Perm (Fin 6), a'.sign = 1 ∧
        (↑(MulAut.conj g⁻¹ h) : Mat4) * rho a = rho a' * (↑(MulAut.conj g⁻¹ h) : Mat4) := by
    intro a ha
    have hRaS : R F a ∈ (alternatingGroup (Fin 6)).map (R F) :=
      Subgroup.mem_map.mpr ⟨a, Equiv.Perm.mem_alternatingGroup.mpr ha, rfl⟩
    have hconjRa : MulAut.conj g (R F a) ∈ H₁ := by
      rw [hH1]
      exact Subgroup.mem_map.mpr ⟨R F a, hRaS, rfl⟩
    have hnormed : h * MulAut.conj g (R F a) * h⁻¹ ∈ H₁ := hnorm h hh _ hconjRa
    have h1 : h * MulAut.conj g (R F a) * h⁻¹ ∈
        ((alternatingGroup (Fin 6)).map (R F)).map (MulAut.conj g).toMonoidHom := by
      rw [← hH1]
      exact hnormed
    obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.mp h1
    have hmemS : MulAut.conj g⁻¹ (h * MulAut.conj g (R F a) * h⁻¹) ∈
        (alternatingGroup (Fin 6)).map (R F) := by
      have h2 : MulAut.conj g⁻¹ (h * MulAut.conj g (R F a) * h⁻¹) = s := by
        rw [← hsg]
        change MulAut.conj g⁻¹ (MulAut.conj g s) = s
        simp only [MulAut.conj_apply]
        group
      rw [h2]
      exact hs
    obtain ⟨a', ha', ha'eq⟩ := Subgroup.mem_map.mp hmemS
    refine ⟨a', Equiv.Perm.mem_alternatingGroup.mp ha', ?_⟩
    have heq_units : MulAut.conj g⁻¹ h * R F a * (MulAut.conj g⁻¹ h)⁻¹ = R F a' := by
      rw [ha'eq]
      simp only [MulAut.conj_apply]
      group
    have hcancel : MulAut.conj g⁻¹ h * R F a = R F a' * MulAut.conj g⁻¹ h := by
      calc MulAut.conj g⁻¹ h * R F a
          = (MulAut.conj g⁻¹ h * R F a * (MulAut.conj g⁻¹ h)⁻¹) * (MulAut.conj g⁻¹ h) := by
            group
        _ = R F a' * MulAut.conj g⁻¹ h := by rw [heq_units]
    have hmat := congrArg (fun u : GL (Fin 4) (ZMod 2) => (u : Mat4)) hcancel
    simpa [R_coe] using hmat
  obtain ⟨p, hp⟩ := F.complete (↑(MulAut.conj g⁻¹ h) : Mat4)
    ⟨↑((MulAut.conj g⁻¹ h)⁻¹), by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]⟩ hkey
  refine ⟨p, ?_⟩
  apply Units.ext
  rw [R_coe]
  exact hp

theorem gl_normA6_of_facts (F : Facts) (H₁ H₂ : Subgroup (GL (Fin 4) (ZMod 2))) (h12 : H₁ ≤ H₂)
    (hA : Nonempty (↥H₁ ≃* alternatingGroup (Fin 6)))
    (hnorm : ∀ h ∈ H₂, ∀ a ∈ H₁, h * a * h⁻¹ ∈ H₁) :
    Nonempty (↥H₂ ≃* alternatingGroup (Fin 6)) ∨ Nonempty (↥H₂ ≃* Equiv.Perm (Fin 6)) := by
  let varphi : ↥(alternatingGroup (Fin 6)) ≃* ↥H₁ := hA.some.symm
  let x : GL (Fin 4) (ZMod 2) := ((varphi (sigmaA F) : ↥H₁) : GL (Fin 4) (ZMod 2))
  let y : GL (Fin 4) (ZMod 2) := ((varphi (tauA F) : ↥H₁) : GL (Fin 4) (ZMod 2))
  have hrelx : Rel x y := by
    simpa [x, y] using Rel.map H₁.subtype (Rel.map varphi.toMonoidHom (rel_sigmaA_tauA F))
  have hxne : x ≠ 1 := by
    intro hx1
    have h1 : varphi (sigmaA F) = 1 := Subtype.ext hx1
    have h2 : sigmaA F = 1 := varphi.injective (by rw [h1, map_one])
    have h3 : sigma = 1 := by
      have := congrArg (fun u : ↥(alternatingGroup (Fin 6)) => (u : Equiv.Perm (Fin 6))) h2
      simpa [sigmaA] using this
    exact sigma_ne_one h3
  obtain ⟨g, a, b, ha, hb, hgx, hgy⟩ := exists_conj_rel F hrelx hxne
  have hH1 : H₁ = ((alternatingGroup (Fin 6)).map (R F)).map (MulAut.conj g).toMonoidHom :=
    H1_eq_conj_map F H₁ varphi g a b ha hb hgx hgy
  have hS : (alternatingGroup (Fin 6)).map (R F) ≤ H₂.map (MulAut.conj g⁻¹).toMonoidHom :=
    S_le_conj_H2 F H₁ H₂ h12 g hH1
  have hH2' : H₂.map (MulAut.conj g⁻¹).toMonoidHom ≤ (R F).range :=
    conj_H2_le_range F H₁ H₂ h12 hnorm g hH1
  let H₂' : Subgroup (GL (Fin 4) (ZMod 2)) := H₂.map (MulAut.conj g⁻¹).toMonoidHom
  let T : Subgroup (Equiv.Perm (Fin 6)) := H₂'.comap (R F)
  have hTmap : T.map (R F) = H₂' := Subgroup.map_comap_eq_self hH2'
  have hAT : alternatingGroup (Fin 6) ≤ T := (Subgroup.map_le_iff_le_comap).mp hS
  have hindex_dvd : T.index ∣ (alternatingGroup (Fin 6)).index := Subgroup.index_dvd_of_le hAT
  have hAindex : (alternatingGroup (Fin 6)).index = 2 := alternatingGroup.index_eq_two
  have hindex : T.index = 1 ∨ T.index = 2 := by
    have h := hindex_dvd
    rw [hAindex] at h
    exact (Nat.dvd_prime Nat.prime_two).mp h
  let e1 : ↥H₂ ≃* ↥H₂' := MulEquiv.subgroupMap (MulAut.conj g⁻¹) H₂
  let e2 : ↥H₂' ≃* ↥T :=
    (MulEquiv.subgroupCongr hTmap.symm).trans
      (Subgroup.equivMapOfInjective T (R F) (R_injective F)).symm
  rcases hindex with hidx | hidx
  · refine Or.inr ⟨e1.trans (e2.trans
      ((MulEquiv.subgroupCongr (Subgroup.index_eq_one.mp hidx)).trans Subgroup.topEquiv))⟩
  · refine Or.inl ⟨e1.trans (e2.trans
      (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx)))⟩

end CFSG.OddStandard.SmallF3.Omega
