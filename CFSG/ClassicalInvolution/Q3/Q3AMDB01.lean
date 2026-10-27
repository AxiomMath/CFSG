module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadNbhd
public import CFSG.ClassicalInvolution.Q3.Q3AMBadDouble

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Elementary

variable {G : Type} [Group G]

theorem exists_conj_of_inv_mul_mem_odd [Finite G] {N : Subgroup G} (hN : Odd (Nat.card N)) {s w : G}
    (hs : s * s = 1) (hw : w * w = 1) (ho : s⁻¹ * w ∈ N) : ∃ x ∈ N, w = x * s * x⁻¹ := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  obtain ⟨o, ho_def⟩ : ∃ o : G, o = s⁻¹ * w := ⟨_, rfl⟩
  rw [← ho_def] at ho
  obtain ⟨j, hj⟩ : Odd (orderOf o) := hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N ho)
  have e1 : o = s * w := by rw [ho_def, hs']
  have e2 : o⁻¹ = w * s := by rw [e1, mul_inv_rev, hw', hs']
  have hso : s * o * s⁻¹ = o⁻¹ := by
    rw [e2, e1, hs']
    calc s * (s * w) * s = (s * s) * w * s := by group
      _ = w * s := by rw [hs, one_mul]
  have hy : o ^ (j + 1) * o ^ (j + 1) = o := by
    rw [← pow_add, show j + 1 + (j + 1) = orderOf o + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hsy : s * o ^ (j + 1) * s⁻¹ = (o ^ (j + 1))⁻¹ := by
    rw [← conj_pow, hso, inv_pow]
  have h1 : s * o ^ (j + 1) = (o ^ (j + 1))⁻¹ * s := by
    calc s * o ^ (j + 1) = (s * o ^ (j + 1) * s⁻¹) * s := by group
      _ = (o ^ (j + 1))⁻¹ * s := by rw [hsy]
  refine ⟨(o ^ (j + 1))⁻¹, N.inv_mem (N.pow_mem ho _), ?_⟩
  rw [inv_inv]
  calc w = (w * s) * s := by rw [mul_assoc, hs, mul_one]
    _ = o⁻¹ * s := by rw [e2]
    _ = (o ^ (j + 1) * o ^ (j + 1))⁻¹ * s := by rw [hy]
    _ = (o ^ (j + 1))⁻¹ * ((o ^ (j + 1))⁻¹ * s) := by group
    _ = (o ^ (j + 1))⁻¹ * (s * o ^ (j + 1)) := by rw [h1]
    _ = (o ^ (j + 1))⁻¹ * s * o ^ (j + 1) := by group

theorem mk'_ne_one_of_involution [Finite G] {Y : Subgroup G} {v : G} (hv : v ∈ Y)
    (hv2 : v * v = 1) (hv1 : v ≠ 1) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨v, hv⟩ ≠ 1 := by
  intro h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  exact hv1 (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard Y)
    (mem_oddCoreOf_iff.mpr ⟨hv, h⟩) (isPGroup_zpowers_of_mul_self_eq_one hv2 hv1))

theorem conj_eq_self_of_mem_two_group [Finite G] {Y P : Subgroup G} (hP : IsPGroup 2 P) {x s : G}
    (hx : x ∈ oddCoreOf Y) (hsY : s ∈ Y) (hsP : s ∈ P) (hxsP : x * s * x⁻¹ ∈ P) :
    x * s * x⁻¹ = s := by
  have h1 : s⁻¹ * (x * s * x⁻¹) ∈ oddCoreOf Y := by
    have h2 := conj_mem_oddCoreOf_of_mem_normalizer (g := s⁻¹) (Y := Y)
      (fun y hy => Y.mul_mem (Y.mul_mem (Y.inv_mem hsY) hy) (by simpa using hsY))
      (fun y hy => Y.mul_mem (Y.mul_mem (by simpa using hsY) hy) (Y.inv_mem hsY)) hx
    have e : s⁻¹ * x * s⁻¹⁻¹ * x⁻¹ = s⁻¹ * (x * s * x⁻¹) := by group
    rw [← e]
    exact (oddCoreOf Y).mul_mem h2 ((oddCoreOf Y).inv_mem hx)
  have h3 : s⁻¹ * (x * s * x⁻¹) ∈ P := P.mul_mem (P.inv_mem hsP) hxsP
  have h4 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard Y) h1
    (hP.to_le (Subgroup.zpowers_le.mpr h3))
  exact (inv_mul_eq_one.mp h4).symm

end Elementary

section Cover

theorem eq_or_eq_of_mem_pair {M : Type} {a b c ζ₁ ζ₂ : M} (ha : a = ζ₁ ∨ a = ζ₂)
    (hb : b = ζ₁ ∨ b = ζ₂) (hc : c = ζ₁ ∨ c = ζ₂) (hbc : b ≠ c) : a = b ∨ a = c := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp_all

end Cover

section Basic


variable {G : Type} [Group G] [Finite G]

theorem PspSetting.mul_comm_zt {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {S : Sylow 2 G}
    {R T W : Subgroup G} {z t : G} (hset : PspSetting Ω K J S R T W z t K') : z * t = t * z :=
  Q3CL.T8.mul_comm_of_mem_omegaNbr hset.bad.std.stand.hyp hset.bad.std.hz hset.bad.std.hJ
    hset.bad.std.ht

theorem PspSetting.exists_conj_of_uniq {Ω : Set (Subgroup G)} {K J K' : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hset : PspSetting Ω K J S R T W z t K') {M : Subgroup G} (hM : M ∈ Ω) {m : G}
    (hm : IsUniqueInvolution M m) : ∃ g : G, m = g * z * g⁻¹ := by
  obtain ⟨g, hg⟩ := hset.bad.std.stand.trans M hM
  have h : IsUniqueInvolution M (g * z * g⁻¹) := hg ▸ hset.bad.std.hz.conj g
  exact ⟨g, hm.eq h⟩

end Basic

section Double


variable {G : Type} [Group G] [Finite G]

theorem pspNbhdDouble_involutions {Ω : Set (Subgroup G)} {M : Subgroup G} {a : G}
    (hD : PspNbhdDouble Ω M a) :
    ∃ (hay : a ∈ nbrLayer Ω M a)
      (ζ₁ ζ₂ : ↥(nbrLayer Ω M a) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω M a)),
      ζ₁ ≠ ζ₂ ∧ ζ₁ * ζ₁ = 1 ∧ ζ₂ * ζ₂ = 1 ∧
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω M a)) ⟨a, hay⟩ = ζ₁ * ζ₂ ∧
        ∀ N ∈ omegaNbr Ω M, ∀ y : ↥(nbrLayer Ω M a), (y : G) ∈ exactCore3 a N → y * y = 1 →
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω M a)) y = 1 ∨
            QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω M a)) y = ζ₁ ∨
              QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω M a)) y = ζ₂ := by
  obtain ⟨ι, -, D, ha, i, j, -, hk, hi, hj, ζi, ζj, -, -, hne, h2i, h2j, -, -, -, -, hui, huj,
    hz⟩ := hD
  refine ⟨ha, ζi, ζj, hne, h2i, h2j, hz, ?_⟩
  intro N hN y hyN hy2
  have hmem : Subgroup.map (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(nbrLayer Ω M a))) ((exactCore3 a N).subgroupOf (nbrLayer Ω M a)) ∈
      oddQuotientFamily (restrictFamily (centralizingMembers (nbrCoreFam Ω M a) {a})
        (nbrLayer Ω M a)) :=
    ⟨(exactCore3 a N).subgroupOf (nbrLayer Ω M a), ⟨exactCore3 a N,
      ⟨⟨N, hN, rfl⟩, exactCore3_le_centralizer a N⟩, exactCore3_le_nbrLayer hN, rfl⟩, rfl⟩
  obtain ⟨k, R, hR, hkR⟩ := D.fundamental _ hmem
  have hyim : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω M a)) y ∈
      Subgroup.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω M a)))
        ((exactCore3 a N).subgroupOf (nbrLayer Ω M a)) :=
    ⟨y, Subgroup.mem_subgroupOf.mpr hyN, rfl⟩
  have hsq : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω M a)) y *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω M a)) y = 1 := by
    rw [← map_mul, hy2, map_one]
  rcases hk k with rfl | rfl
  · rw [hkR, Q3Y.eq_top_of_mem_fund_sl23 hi hR, ← MonoidHom.range_eq_map] at hyim
    rcases hui _ hyim hsq with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rw [hkR, Q3Y.eq_top_of_mem_fund_sl23 hj hR, ← MonoidHom.range_eq_map] at hyim
    rcases huj _ hyim hsq with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

theorem PspSetting.uniq_mul [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J K' : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (hset : PspSetting Ω K J S R T W z t K') :
    IsUniqueInvolution K' (z * t) := by
  have hΩ : HypOmegaMod Ω := hset.bad.std.stand.hyp
  obtain ⟨u, hu⟩ := hΩ.exists_uniqueInvolution hset.nbrK.1
  rw [← hset.bad.eq_mul_of_nbr_nbr hset.nbrK hset.nbrJ hu]
  exact hu

theorem PspSetting.t_mem_nbrLayer {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {S : Sylow 2 G}
    {R T W : Subgroup G} {z t : G} (hset : PspSetting Ω K J S R T W z t K') :
    t ∈ nbrLayer Ω K z :=
  exactCore3_le_nbrLayer hset.bad.std.hJ (Subgroup.mem_inf.mpr ⟨hset.bad.std.ht.mem,
    Subgroup.mem_centralizer_singleton_iff.mpr hset.mul_comm_zt.symm⟩)

theorem PspSetting.mul_mem_nbrLayer [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hset : PspSetting Ω K J S R T W z t K') : z * t ∈ nbrLayer Ω K z := by
  have hztc : z * (z * t) = (z * t) * z := by rw [mul_assoc, ← hset.mul_comm_zt]
  exact exactCore3_le_nbrLayer hset.nbrK (Subgroup.mem_inf.mpr ⟨hset.uniq_mul.mem,
    Subgroup.mem_centralizer_singleton_iff.mpr hztc.symm⟩)

theorem PspSetting.nbr_involution_conj [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hset : PspSetting Ω K J S R T W z t K') (hD : PspNbhdDouble Ω K z)
    {N : Subgroup G} (hN : N ∈ omegaNbr Ω K) {w : G} (hw : IsUniqueInvolution N w) :
    ∃ x ∈ oddCoreOf (nbrLayer Ω K z), w = x * t * x⁻¹ ∨ w = x * (z * t) * x⁻¹ := by
  have hstd := hset.bad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hu := hset.uniq_mul
  have hzt := hset.mul_comm_zt
  have hzw : z * w = w * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hN hw
  have hztc : z * (z * t) = (z * t) * z := by rw [mul_assoc, ← hzt]
  have hcen : ∀ v : G, z * v = v * z → v ∈ Subgroup.centralizer ({z} : Set G) := fun v h =>
    Subgroup.mem_centralizer_singleton_iff.mpr h.symm
  have hwY : w ∈ nbrLayer Ω K z :=
    exactCore3_le_nbrLayer hN (Subgroup.mem_inf.mpr ⟨hw.mem, hcen w hzw⟩)
  have htY := hset.t_mem_nbrLayer
  have hztY := hset.mul_mem_nbrLayer
  obtain ⟨hay, ζ₁, ζ₂, hne, h1, h2, hzb, hmain⟩ := pspNbhdDouble_involutions hD
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) with hπ
  have hinv : ∀ {N' : Subgroup G}, N' ∈ omegaNbr Ω K → ∀ {v : G}, IsUniqueInvolution N' v →
      z * v = v * z → ∀ hvY : v ∈ nbrLayer Ω K z, π ⟨v, hvY⟩ = ζ₁ ∨ π ⟨v, hvY⟩ = ζ₂ := by
    intro N' hN' v hv' hvz hvY
    have hvmem : v ∈ exactCore3 z N' := Subgroup.mem_inf.mpr ⟨hv'.mem, hcen v hvz⟩
    have hv2 : (⟨v, hvY⟩ : ↥(nbrLayer Ω K z)) * ⟨v, hvY⟩ = 1 := Subtype.ext hv'.sq
    rcases hmain N' hN' ⟨v, hvY⟩ hvmem hv2 with h | h | h
    · exact absurd h (mk'_ne_one_of_involution hvY hv'.sq hv'.ne_one)
    · exact Or.inl h
    · exact Or.inr h
  have hwc := hinv hN hw hzw hwY
  have htc := hinv hstd.hJ hstd.ht hzt htY
  have huc := hinv hset.nbrK hu hztc hztY
  have hneq : π ⟨t, htY⟩ ≠ π ⟨z * t, hztY⟩ := by
    intro h
    have e : (⟨z * t, hztY⟩ : ↥(nbrLayer Ω K z)) = ⟨t, htY⟩ * ⟨z, hay⟩ := Subtype.ext hzt
    rw [e, map_mul] at h
    have h3 : π ⟨t, htY⟩ * π ⟨z, hay⟩ = π ⟨t, htY⟩ * 1 := by rw [mul_one]; exact h.symm
    have h4 : π ⟨z, hay⟩ = 1 := mul_left_cancel h3
    rw [hzb] at h4
    exact hne (mul_left_cancel (h1.trans h4.symm))
  rcases eq_or_eq_of_mem_pair hwc htc huc hneq with h | h
  · obtain ⟨x, hx, hxw⟩ := exists_conj_of_inv_mul_mem_odd (oddCoreOf_odd_natCard _) hstd.ht.sq
      hw.sq (inv_mul_mem_of_mk'_eq htY hwY h.symm)
    exact ⟨x, hx, Or.inl hxw⟩
  · obtain ⟨x, hx, hxw⟩ := exists_conj_of_inv_mul_mem_odd (oddCoreOf_odd_natCard _) hu.sq
      hw.sq (inv_mul_mem_of_mk'_eq hztY hwY h.symm)
    exact ⟨x, hx, Or.inr hxw⟩

theorem PspSetting.nbr_involution_eq [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hset : PspSetting Ω K J S R T W z t K') (hD : PspNbhdDouble Ω K z)
    {N : Subgroup G} (hN : N ∈ omegaNbr Ω K) {w : G} (hw : IsUniqueInvolution N w)
    {P : Subgroup G} (hP : IsPGroup 2 P) (htP : t ∈ P) (hztP : z * t ∈ P) (hwP : w ∈ P) :
    w = t ∨ w = z * t := by
  obtain ⟨x, hx, h | h⟩ := hset.nbr_involution_conj hD hN hw
  · exact Or.inl (h ▸ conj_eq_self_of_mem_two_group hP hx hset.t_mem_nbrLayer htP (h ▸ hwP))
  · exact Or.inr (h ▸ conj_eq_self_of_mem_two_group hP hx hset.mul_mem_nbrLayer hztP (h ▸ hwP))

end Double

end CFSG.ClassicalInvolution.Q3.Q3AM
