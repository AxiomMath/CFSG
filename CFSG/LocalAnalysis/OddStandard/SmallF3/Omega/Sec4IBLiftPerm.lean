module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem sec4ILift_rho_injOn_P (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {P : Subgroup G}
    (hP : IsSylow2Of P L) {x y : ↥L} (hx : (x : G) ∈ P) (hy : (y : G) ∈ P)
    (h : sec4IRho e x = sec4IRho e y) : x = y := by
  have hS : IsPGroup 2 ↥(P.subgroupOf L) :=
    hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  refine sec4IRho_injOn hL e hS ?_ ?_ h
  · exact (Subgroup.mem_subgroupOf (H := P) (K := L) (h := x)).mpr hx
  · exact (Subgroup.mem_subgroupOf (H := P) (K := L) (h := y)).mpr hy

private theorem sec4ILift_conj_phi (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {P : Subgroup G}
    (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) {h : G} (hh : h ∈ L)
    (hnormB : h ∈ Subgroup.normalizer (sec4ILiftB e fr P : Set G))
    {σ : Equiv.Perm (Fin 7)}
    (hconj : ∀ v : Fin 7 → ZMod 2, sec4IRho e ⟨h, hh⟩ * sec4IPsi fr v
      * (sec4IRho e ⟨h, hh⟩)⁻¹ = sec4IPsi fr (permVec σ v))
    {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) :
    h * sec4ILiftPhi e fr P v * h⁻¹ = sec4ILiftPhi e fr P (permVec σ v) := by
  obtain ⟨hvL, _, hvρ⟩ := sec4ILiftPhi_spec hL e hP hfr hv
  obtain ⟨hpL, hpP, hpρ⟩ :=
    sec4ILiftPhi_spec hL e hP hfr (sec4I_isEvenVec_permVec σ hv)
  have hconjB : h * sec4ILiftPhi e fr P v * h⁻¹ ∈ sec4ILiftB e fr P :=
    (Subgroup.mem_normalizer_iff.mp hnormB (sec4ILiftPhi e fr P v)).mp
      (sec4ILiftPhi_mem hL e hP hfr hv)
  let c : ↥L := ⟨h, hh⟩ * ⟨sec4ILiftPhi e fr P v, hvL⟩ * ⟨h, hh⟩⁻¹
  have hcval : (c : G) = h * sec4ILiftPhi e fr P v * h⁻¹ := rfl
  have hcB : (c : G) ∈ sec4ILiftB e fr P := by rw [hcval]; exact hconjB
  have hcρ : sec4IRho e c
      = sec4IRho e ⟨sec4ILiftPhi e fr P (permVec σ v), hpL⟩ := by
    have h1 : sec4IRho e c = sec4IRho e ⟨h, hh⟩
        * sec4IRho e ⟨sec4ILiftPhi e fr P v, hvL⟩ * (sec4IRho e ⟨h, hh⟩)⁻¹ := by
      simp only [c, map_mul, map_inv]
    rw [h1, hvρ, hconj v, hpρ]
  have heq : c = ⟨sec4ILiftPhi e fr P (permVec σ v), hpL⟩ :=
    sec4ILift_rho_injOn_P hL e hP (x := c) (y := ⟨_, hpL⟩)
      (by rw [hcval]; exact sec4ILiftB_le e fr P hconjB) hpP hcρ
  simpa [hcval] using congrArg Subtype.val heq

theorem sec4ILift_conj_mem (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {P : Subgroup G} (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) {h : G} (hh : h ∈ L)
    (hn : ∀ y ∈ sec4IB0 fr,
      sec4IRho e ⟨h, hh⟩ * y * (sec4IRho e ⟨h, hh⟩)⁻¹ ∈ sec4IB0 fr)
    {b : G} (hb : b ∈ sec4ILiftB e fr P) : h * b * h⁻¹ ∈ sec4ILiftB e fr P := by
  obtain ⟨hbL, _hbP, hbρ⟩ := (mem_sec4ILiftB_iff e fr P).mp hb
  have hB2 : ∀ x ∈ sec4ILiftB e fr P, x * x = 1 := by
    intro x hx
    have := (sec4ILift_isMax hL e hP hfr).2.1.2 x hx
    rwa [pow_two] at this
  let c : ↥L := ⟨h, hh⟩ * ⟨b, hbL⟩ * ⟨h, hh⟩⁻¹
  have hcval : (c : G) = h * b * h⁻¹ := rfl
  have hcρ : sec4IRho e c ∈ sec4IB0 fr := by
    have h1 : sec4IRho e c = sec4IRho e ⟨h, hh⟩ * sec4IRho e ⟨b, hbL⟩
        * (sec4IRho e ⟨h, hh⟩)⁻¹ := by simp only [c, map_mul, map_inv]
    rw [h1]
    exact hn _ hbρ
  have hmem : sec4IRho e c ∈ ((sec4ILiftB e fr P).subgroupOf L).map (sec4IRho e) := by
    rw [sec4ILift_map_eq hL e hP hfr]
    exact hcρ
  obtain ⟨b', hb'sub, hb'eq⟩ := Subgroup.mem_map.mp hmem
  have hb'B : (b' : G) ∈ sec4ILiftB e fr P := Subgroup.mem_subgroupOf.mp hb'sub
  have hb'2 : b' * b' = 1 := Subtype.ext (by simpa using hB2 (b' : G) hb'B)
  have hb2 : (⟨b, hbL⟩ : ↥L) * ⟨b, hbL⟩ = 1 :=
    Subtype.ext (by simpa using hB2 b hb)
  have hc2 : c * c = 1 := by
    have hcdef : c = ⟨h, hh⟩ * ⟨b, hbL⟩ * ⟨h, hh⟩⁻¹ := rfl
    rw [hcdef]
    calc ((⟨h, hh⟩ : ↥L) * ⟨b, hbL⟩ * ⟨h, hh⟩⁻¹)
          * ((⟨h, hh⟩ : ↥L) * ⟨b, hbL⟩ * ⟨h, hh⟩⁻¹)
        = (⟨h, hh⟩ : ↥L) * (⟨b, hbL⟩ * ⟨b, hbL⟩) * ⟨h, hh⟩⁻¹ := by group
      _ = (⟨h, hh⟩ : ↥L) * 1 * ⟨h, hh⟩⁻¹ := by rw [hb2]
      _ = 1 := by group
  have hCover : sec4ICover e c = sec4ICover e b' := by
    apply Subtype.ext
    change sec4IRho e c = sec4IRho e b'
    exact hb'eq.symm
  have heq : c = b' := (sec4ICover_odd hL e).eq_of_mul_self_eq_one hc2 hb'2 hCover
  have hmemB : (c : G) ∈ sec4ILiftB e fr P := by rw [heq]; exact hb'B
  rw [← hcval]
  exact hmemB

theorem sec4ILift_perm (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {P : Subgroup G} (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) :
    IsPermModuleVia IsEvenVec (sec4ILiftPhi e fr P) (sec4ILiftB e fr P)
      (L ⊓ normalizer (sec4ILiftB e fr P : Set G)) (alternatingGroup (Fin 7)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v w hv hw
    obtain ⟨hvL, hvP, hvρ⟩ := sec4ILiftPhi_spec hL e hP hfr hv
    obtain ⟨hwL, hwP, hwρ⟩ := sec4ILiftPhi_spec hL e hP hfr hw
    obtain ⟨hvwL, hvwP, hvwρ⟩ :=
      sec4ILiftPhi_spec hL e hP hfr (sec4I_isEvenVec_add hv hw)
    have hkey : sec4IRho e ⟨sec4ILiftPhi e fr P (v + w), hvwL⟩
        = sec4IRho e (⟨sec4ILiftPhi e fr P v, hvL⟩ * ⟨sec4ILiftPhi e fr P w, hwL⟩) := by
      rw [map_mul, hvwρ, hvρ, hwρ, sec4IPsi_add]
    have heq := sec4ILift_rho_injOn_P hL e hP (x := ⟨sec4ILiftPhi e fr P (v + w), hvwL⟩)
      (y := ⟨sec4ILiftPhi e fr P v, hvL⟩ * ⟨sec4ILiftPhi e fr P w, hwL⟩)
      hvwP (P.mul_mem hvP hwP) hkey
    exact congrArg Subtype.val heq
  · intro v w hv hw hφ
    obtain ⟨hvL, _, hvρ⟩ := sec4ILiftPhi_spec hL e hP hfr hv
    obtain ⟨hwL, _, hwρ⟩ := sec4ILiftPhi_spec hL e hP hfr hw
    refine sec4IPsi_injOn fr hv hw ?_
    have hρ : sec4IRho e ⟨sec4ILiftPhi e fr P v, hvL⟩
        = sec4IRho e ⟨sec4ILiftPhi e fr P w, hwL⟩ :=
      congrArg (sec4IRho e) (Subtype.ext hφ)
    rwa [hvρ, hwρ] at hρ
  · intro x
    constructor
    · intro hx
      obtain ⟨hxL, hxP, hxρ⟩ := (mem_sec4ILiftB_iff e fr P).mp hx
      obtain ⟨v, hv, hψ⟩ := (mem_sec4IB0_iff fr).mp hxρ
      obtain ⟨hvL, hvP, hvρ⟩ := sec4ILiftPhi_spec hL e hP hfr hv
      refine ⟨v, hv, ?_⟩
      have hρeq : sec4IRho e ⟨sec4ILiftPhi e fr P v, hvL⟩ = sec4IRho e ⟨x, hxL⟩ := by
        rw [hvρ, hψ]
      exact congrArg Subtype.val
        (sec4ILift_rho_injOn_P hL e hP (x := ⟨sec4ILiftPhi e fr P v, hvL⟩)
          (y := ⟨x, hxL⟩) hvP hxP hρeq)
    · rintro ⟨v, hv, rfl⟩
      exact sec4ILiftPhi_mem hL e hP hfr hv
  · intro h hH
    have hhL : h ∈ L := hH.1
    have hnormB : h ∈ normalizer (sec4ILiftB e fr P : Set G) := hH.2
    have hn : ∀ y, y ∈ sec4IB0 fr ↔
        sec4IRho e ⟨h, hhL⟩ * y * (sec4IRho e ⟨h, hhL⟩)⁻¹ ∈ sec4IB0 fr := by
      intro y
      constructor
      · intro hy
        have hy' : y ∈ ((sec4ILiftB e fr P).subgroupOf L).map (sec4IRho e) := by
          rw [sec4ILift_map_eq hL e hP hfr]
          exact hy
        obtain ⟨b₀, hb₀sub, hb₀eq⟩ := Subgroup.mem_map.mp hy'
        have hb₀B : (b₀ : G) ∈ sec4ILiftB e fr P := Subgroup.mem_subgroupOf.mp hb₀sub
        have hconjB : h * (b₀ : G) * h⁻¹ ∈ sec4ILiftB e fr P :=
          (Subgroup.mem_normalizer_iff.mp hnormB (b₀ : G)).mp hb₀B
        let c : ↥L := ⟨h, hhL⟩ * b₀ * ⟨h, hhL⟩⁻¹
        have hcval : (c : G) = h * (b₀ : G) * h⁻¹ := rfl
        have hcB : (c : G) ∈ sec4ILiftB e fr P := by rw [hcval]; exact hconjB
        have hcρ : sec4IRho e c = sec4IRho e ⟨h, hhL⟩ * y * (sec4IRho e ⟨h, hhL⟩)⁻¹ := by
          have h1 : sec4IRho e c = sec4IRho e ⟨h, hhL⟩ * sec4IRho e b₀
              * (sec4IRho e ⟨h, hhL⟩)⁻¹ := by simp only [c, map_mul, map_inv]
          rw [h1, hb₀eq]
        rw [← hcρ]
        exact ((mem_sec4ILiftB_iff e fr P).mp hcB).2.2
      · intro hy
        have hy' : sec4IRho e ⟨h, hhL⟩ * y * (sec4IRho e ⟨h, hhL⟩)⁻¹
            ∈ ((sec4ILiftB e fr P).subgroupOf L).map (sec4IRho e) := by
          rw [sec4ILift_map_eq hL e hP hfr]
          exact hy
        obtain ⟨b₀, hb₀sub, hb₀eq⟩ := Subgroup.mem_map.mp hy'
        have hb₀B : (b₀ : G) ∈ sec4ILiftB e fr P := Subgroup.mem_subgroupOf.mp hb₀sub
        have hconjB : h⁻¹ * (b₀ : G) * h ∈ sec4ILiftB e fr P := by
          have hmem := (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (sec4ILiftB e fr P : Set G)).inv_mem hnormB)
            (b₀ : G)).mp hb₀B
          simpa using hmem
        have hcB : ((⟨h, hhL⟩⁻¹ * b₀ * ⟨h, hhL⟩ : ↥L) : G) ∈ sec4ILiftB e fr P := by
          show h⁻¹ * (b₀ : G) * h ∈ sec4ILiftB e fr P
          exact hconjB
        have hcρ : sec4IRho e (⟨h, hhL⟩⁻¹ * b₀ * ⟨h, hhL⟩) = y := by
          have h1 : sec4IRho e (⟨h, hhL⟩⁻¹ * b₀ * ⟨h, hhL⟩)
              = (sec4IRho e ⟨h, hhL⟩)⁻¹ * sec4IRho e b₀ * sec4IRho e ⟨h, hhL⟩ := by
            simp only [map_mul, map_inv]
          rw [h1, hb₀eq]
          group
        rw [← hcρ]
        exact ((mem_sec4ILiftB_iff e fr P).mp hcB).2.2
    have hxIN : sec4IRho e ⟨h, hhL⟩ ∈ sec4IN sec4IQ_nondegenerate fr := by
      show sec4IRho e ⟨h, hhL⟩ ∈ omegaProj sec4IQ_nondegenerate
        ⊓ Subgroup.normalizer (sec4IB0 fr : Set (ProjOrth Sec4IQ))
      exact ⟨sec4IRho_mem e ⟨h, hhL⟩, Subgroup.mem_normalizer_iff.mpr hn⟩
    obtain ⟨σ, hσsign, hσconj⟩ := sec4I_conj_of_mem_sec4IN sec4IQ_nondegenerate fr hxIN
    exact ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσsign,
      fun v hv => sec4ILift_conj_phi hL e hP hfr hhL hnormB hσconj hv⟩
  · intro σ hσ
    have hsign : Equiv.Perm.sign σ = 1 := Equiv.Perm.mem_alternatingGroup.mp hσ
    obtain ⟨x, hxIN, hxconj⟩ := sec4I_exists_mem_sec4IN_of_perm sec4IQ_nondegenerate fr hsign
    have hxIN' : x ∈ omegaProj sec4IQ_nondegenerate
        ⊓ Subgroup.normalizer (sec4IB0 fr : Set (ProjOrth Sec4IQ)) := hxIN
    have hxmem : x ∈ Sec4IOmega := hxIN'.1
    obtain ⟨h, hρh⟩ := exists_sec4IRho_eq e hxmem
    have hsub : (⟨(h : G), h.2⟩ : ↥L) = h := Subtype.ext rfl
    have hn : ∀ y ∈ sec4IB0 fr,
        sec4IRho e ⟨(h : G), h.2⟩ * y * (sec4IRho e ⟨(h : G), h.2⟩)⁻¹ ∈ sec4IB0 fr := by
      intro y hy
      have hx : sec4IRho e ⟨(h : G), h.2⟩ = x := by rw [hsub, hρh]
      rw [hx]
      exact (Subgroup.mem_normalizer_iff.mp hxIN'.2 y).mp hy
    have hnormB : (h : G) ∈ normalizer (sec4ILiftB e fr P : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro b
      constructor
      · intro hb
        exact sec4ILift_conj_mem hL e hP hfr h.2 hn hb
      · intro hb
        have hn' : ∀ y ∈ sec4IB0 fr,
            sec4IRho e ⟨(h : G)⁻¹, L.inv_mem h.2⟩ * y
              * (sec4IRho e ⟨(h : G)⁻¹, L.inv_mem h.2⟩)⁻¹ ∈ sec4IB0 fr := by
          intro y hy
          have hxinv : sec4IRho e (⟨(h : G)⁻¹, L.inv_mem h.2⟩ : ↥L) = x⁻¹ := by
            have hsub' : (⟨(h : G)⁻¹, L.inv_mem h.2⟩ : ↥L) = h⁻¹ := Subtype.ext rfl
            rw [hsub', map_inv, hρh]
          rw [hxinv]
          simpa using (Subgroup.mem_normalizer_iff''.mp hxIN'.2 y).mp hy
        have hb' := sec4ILift_conj_mem hL e hP hfr (L.inv_mem h.2) hn' hb
        rw [show b = (h : G)⁻¹ * ((h : G) * b * (h : G)⁻¹) * ((h : G)⁻¹)⁻¹ from by group]
        exact hb'
    refine ⟨(h : G), ⟨h.2, hnormB⟩, ?_⟩
    have hconj : ∀ v : Fin 7 → ZMod 2, sec4IRho e ⟨(h : G), h.2⟩ * sec4IPsi fr v
        * (sec4IRho e ⟨(h : G), h.2⟩)⁻¹ = sec4IPsi fr (permVec σ v) := by
      intro v
      have hx : sec4IRho e ⟨(h : G), h.2⟩ = x := by rw [hsub, hρh]
      rw [hx]
      exact hxconj v
    intro v hv
    exact sec4ILift_conj_phi hL e hP hfr h.2 hnormB hconj hv

end CFSG.OddStandard.SmallF3.Omega
