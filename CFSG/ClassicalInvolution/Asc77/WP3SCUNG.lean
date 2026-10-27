module

public import CFSG.ClassicalInvolution.Asc77.WP3SCUNGa
public import CFSG.ClassicalInvolution.Asc77.WP3SCUConj
import CFSG.ClassicalInvolution.Asc77.AscE187Img

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Graph

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {z t z' : G}

theorem false_of_graph_type (hs : ChainFrameSetting p f Ω K J K' z t z') (C : ChainCtx p f Ω z)
    {g a b : G} {M : Subgroup G} (hd : ChainConjData hs C g a b M)
    (hgeom : BlockGeom4 (fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D))
    {R_M R'' : Subgroup (compModel C.D C.i₁).K}
    (hRM : R_M ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D)
    (hmodM : modOdd z (exactCore z M) = R_M.map (C.psi C.i₁)) {x : (compModel C.D C.i₁).K}
    (hxR : x ∈ R_M) (hx1 : x ≠ 1)
    (hR'' : R'' ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D)
    (hcomm : ∀ r ∈ R_M, ∀ s ∈ R'', r * s = s * r) (hbC : b ∈ Subgroup.centralizer ({z} : Set G))
    (hb : ∀ s ∈ R'', oddQuotMk z ⟨b, hbC⟩ * C.psi C.i₁ s = C.psi C.i₁ s * oddQuotMk z ⟨b, hbC⟩) :
    False := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hfd := hs.frame
  have hT := hs.noTwins
  set B' : Subgroup G := conjSub g (Subgroup.closure ({z, t, z'} : Set G)) with hB'
  have hBel : IsElemAbelian 2 B' := hd.isElemAbelian
  have hB'eq : B' = Subgroup.closure ({a, z, b} : Set G) := hd.closure_eq
  have haB : a ∈ B' := by
    rw [hB'eq]; exact Subgroup.subset_closure (by simp)
  have hzB : z ∈ B' := by
    rw [hB'eq]; exact Subgroup.subset_closure (by simp)
  have hbB : b ∈ B' := by
    rw [hB'eq]; exact Subgroup.subset_closure (by simp)
  have hBC : B' ≤ Subgroup.centralizer ({z} : Set G) := Lemma52Proof.le_centralizer_of_mem hBel hzB
  have haC := hBC haB
  have hz1 := C.hKz.ne_one
  obtain ⟨r_M, hrM, hrMc, hrM1, hamk⟩ := C.exists_central_lift hd.mem hd.cls C.i₁ C.tag₁ hRM hmodM
  obtain ⟨L'', hL''mem, hL''img⟩ := C.exists_member_of_fund C.i₁ C.tag₁ hR''
  have hψ : ∀ x ∈ B', ∀ hx : x ∈ Subgroup.centralizer ({z} : Set G), ∀ y ∈ R''.map (C.psi C.i₁),
      oddQuotMk z ⟨x, hx⟩ * y = y * oddQuotMk z ⟨x, hx⟩ := by
    let Y : Subgroup (OddQuot z) := R''.map (C.psi C.i₁)
    let Tg : Subgroup G := ((Subgroup.centralizer (Y : Set (OddQuot z))).comap
      (oddQuotMk z)).map (Subgroup.centralizer ({z} : Set G)).subtype
    have hmemTg : ∀ (x : G) (hx : x ∈ Subgroup.centralizer ({z} : Set G)),
        (∀ y ∈ Y, oddQuotMk z ⟨x, hx⟩ * y = y * oddQuotMk z ⟨x, hx⟩) → x ∈ Tg := by
      intro x hx h
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      show oddQuotMk z ⟨x, hx⟩ ∈ Subgroup.centralizer (Y : Set (OddQuot z))
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (h y hy).symm
    have hTg : B' ≤ Tg := by
      rw [hB'eq, Subgroup.closure_le]
      intro u hu
      rcases hu with rfl | rfl | rfl
      · refine hmemTg u haC fun y hy => ?_
        obtain ⟨s, hs, rfl⟩ := hy
        rw [hamk, ← map_mul, ← map_mul, hcomm r_M hrM s hs]
      · refine hmemTg u ChainLift.hzC fun y hy => ?_
        exact oddQuotMk_central ChainLift.hzC y
      · refine hmemTg u hbC fun y hy => ?_
        obtain ⟨s, hs, rfl⟩ := hy
        exact hb s hs
    intro x hx hxC y hy
    obtain ⟨u, hu, hux⟩ := hTg hx
    have hu' : u = ⟨x, hxC⟩ := Subtype.ext hux
    rw [hu'] at hu
    have hu2 : oddQuotMk z ⟨x, hxC⟩ ∈ Subgroup.centralizer (Y : Set (OddQuot z)) := hu
    rw [Subgroup.mem_centralizer_iff] at hu2
    exact (hu2 y hy).symm
  obtain ⟨L₁, hL₁mem, hL₁img, hNorm⟩ := C.exists_member_normalized hT hBel hBC hL''mem
    (fun x hx y hy => hψ x hx (hBC hx) y (by rw [← hL''img]; exact hy))
  obtain ⟨w₁, hw₁⟩ := hΩ.classical L₁ hL₁mem.1
  have hct : ∀ x ∈ B', x ∈ trivialOnQuot L₁ := fun x hx =>
    mem_trivialOnQuot_of_centralizes_modOdd hw₁ C.hc2 hL₁mem.2 (hBC hx) (hNorm hx)
      (fun y hy => hψ x hx (hBC hx) y (by rw [hL₁img, hL''img] at hy; exact hy))
  have hzcl : z ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  have htcl : t ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  have hz'cl : z' ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  set L : Subgroup G := conjSub g⁻¹ L₁ with hLdef
  have hLΩ : L ∈ Ω := hΩ.conjInvariant g⁻¹ L₁ hL₁mem.1
  have hLtq : ∀ x ∈ Subgroup.closure ({z, t, z'} : Set G), x ∈ trivialOnQuot L := by
    intro x hx
    have h1 := hct (g * x * g⁻¹) (conj_mem_conjSub hx)
    have h2 := trivialOnQuot_conjSub h1 g⁻¹
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at h2
  have hLmem : L ∈ tqMembers Ω z := ⟨hLΩ, hLtq z hzcl⟩
  have hLK : L ≠ C.K := by
    intro hLK
    have hL1M : L₁ = M := by
      have h1 : conjSub g L = L₁ := conjSub_conjSub_inv g L₁
      rw [hLK, hd.hCK, ← hd.hM] at h1
      exact h1.symm
    apply false_of_same_image (C.psi C.i₁) (C.psi_ker C.i₁) (C.fund_perfect C.i₁ C.tag₁ hRM) hxR
      hx1 hcomm
    rw [← hmodM, ← hL''img, ← hL₁img, hL1M]
  have hJmem : J ∈ tqMembers Ω z := ⟨hfd.memJ, hfd.tq_z_J hp hq hΩ⟩
  have hK'mem : K' ∈ tqMembers Ω z := ⟨hfd.memK', hfd.tq_z_K' hp hq hΩ⟩
  have hJK : J ≠ C.K := by
    intro h
    apply hfd.t_ne_z hp hq hΩ
    have h1 : IsUniqueInvolution K t := by rw [← hd.hCK, ← h]; exact hfd.ht
    exact h1.eq hfd.hz
  have hK'K : K' ≠ C.K := by
    intro h
    apply hfd.z'_ne_z hp hq hΩ
    have h1 : IsUniqueInvolution K z' := by rw [← hd.hCK, ← h]; exact hfd.hz'
    exact h1.eq hfd.hz
  obtain ⟨R_J, hRJ, hmodJ⟩ := C.exists_fund_big hT hJmem hJK
  obtain ⟨R_K', hRK', hmodK'⟩ := C.exists_fund_big hT hK'mem hK'K
  obtain ⟨R_L, hRL, hmodL⟩ := C.exists_fund_big hT hLmem hLK
  have hJcl : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hfd.memJ hfd.ht
  have hK'cl : IsClassicalMember p f K' z' := isClassicalMember_of_twin hΩ hfd.memK' hfd.hz'
  obtain ⟨w_L, hwL⟩ := hΩ.classical L hLΩ
  have htC : t ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hfd.comm_zt hp hΩ).symm
  have hz'C : z' ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hfd.comm_zz' hp hΩ).symm
  obtain ⟨r_J, hrJ, hrJc, hrJ1, hrJk⟩ := C.exists_central_lift hJmem hJcl C.i₁ C.tag₁ hRJ hmodJ
  obtain ⟨r_K', hrK', hrK'c, hrK'1, hrK'k⟩ :=
    C.exists_central_lift hK'mem hK'cl C.i₁ C.tag₁ hRK' hmodK'
  have hquasiL : CFSG.Open.IsQuasisimple ↥(modOdd z (exactCore z L)) := by
    rw [hmodL]
    exact isQuasisimple_map_of_ker_le_center _ (C.psi_ker C.i₁)
      (fundQuasisimple_core C.hp (C.D.isFundTag C.i₁) (C.D.admissible C.i₁)
        (C.four_le C.i₁ C.tag₁) R_L hRL)
  have htL := oddQuotMk_centralizes_modOdd_exactCore hwL C.hc2 hLmem.2 (hLtq t htcl) htC hquasiL
  have hz'L := oddQuotMk_centralizes_modOdd_exactCore hwL C.hc2 hLmem.2 (hLtq z' hz'cl) hz'C
    hquasiL
  have hcenJ : ∀ s ∈ R_L, r_J * s * r_J⁻¹ * s⁻¹ ∈ Subgroup.center (compModel C.D C.i₁).K := by
    intro s hs
    apply C.psi_ker C.i₁
    rw [MonoidHom.mem_ker]
    have hsmem : C.psi C.i₁ s ∈ modOdd z (exactCore z L) := by rw [hmodL]; exact ⟨s, hs, rfl⟩
    have h := htL _ hsmem
    rw [hrJk] at h
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hcenK' : ∀ s ∈ R_L, r_K' * s * r_K'⁻¹ * s⁻¹ ∈ Subgroup.center (compModel C.D C.i₁).K := by
    intro s hs
    apply C.psi_ker C.i₁
    rw [MonoidHom.mem_ker]
    have hsmem : C.psi C.i₁ s ∈ modOdd z (exactCore z L) := by rw [hmodL]; exact ⟨s, hs, rfl⟩
    have h := hz'L _ hsmem
    rw [hrK'k] at h
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hRJcases := hgeom.centralizes R_J hRJ R_L hRL r_J hrJ hrJc hrJ1 hcenJ
  have hRK'cases := hgeom.centralizes R_K' hRK' R_L hRL r_K' hrK' hrK'c hrK'1 hcenK'
  have hne : R_J ≠ R_K' := by
    intro hRR
    have hU1 := C.isUniqueInvolution_modOdd hJmem hJcl
    have hU2 := C.isUniqueInvolution_modOdd hK'mem hK'cl
    have himg : modOdd z (exactCore z J) = modOdd z (exactCore z K') := by
      rw [hmodJ, hmodK', hRR]
    rw [himg] at hU1
    have heq := hU1.eq hU2
    exact hfd.z'_ne_t hΩ (eq_of_oddQuotMk_eq' hz'C htC (isCentralInvolution_of_isClassicalMember
      hK'cl).sq (isCentralInvolution_of_isClassicalMember hJcl).sq hfd.htz'.symm heq.symm)
  have hnc : ¬ ∀ r ∈ R_J, ∀ s ∈ R_K', r * s = s * r := by
    intro hcomm'
    have htK'N : t ∈ Subgroup.normalizer (K' : Set G) :=
      mem_normalizer_of_commutes_involution hΩ.conjInvariant hT hfd.memK' hfd.hz' hfd.htz'
    have htq : t ∈ trivialOnQuot K' := by
      refine mem_trivialOnQuot_of_centralizes_modOdd hK'cl C.hc2 hK'mem.2 htC htK'N ?_
      intro y hy
      rw [hmodK'] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      rw [hrJk, ← map_mul, ← map_mul, hcomm' r_J hrJ s hs]
    have hK'J : K' ≠ J := by
      intro h
      apply hfd.z'_ne_t hΩ
      have h1 : IsUniqueInvolution J z' := by rw [← h]; exact hfd.hz'
      exact h1.eq hfd.ht
    exact hfd.hperp (Set.mem_insert_of_mem _
      (mem_omegaNbr_of_trivialOnQuot hp hq hΩ hfd.memJ hfd.ht hfd.memK' hK'J htq))
  rcases hRJcases with hLJ | hLJc
  · rcases hRK'cases with hLK' | hLK'c
    · exact hne (hLJ.symm.trans hLK')
    · exact hnc fun r hr s hs => hLK'c r (by rw [hLJ]; exact hr) s hs
  · rcases hRK'cases with hLK' | hLK'c
    · exact hnc fun r hr s hs => (hLJc s (by rw [hLK']; exact hs) r hr).symm
    · exact hne (hgeom.uniq R_L hRL R_J hRJ R_K' hRK' hLJc hLK'c)

end Graph

end CFSG.ClassicalInvolution.Asc77
