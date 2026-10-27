module

public import CFSG.Holt.H78.Sec4FinalA

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open CFSG.GH74.Uniqueness.Bender (rootCenter)
open scoped Pointwise

namespace FinConfig

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

theorem exists_lift (hS : Sec4Setting G Ω) {d : Equiv.Perm C.Psi} (hdN : d ∈ C.N)
    (hdb : d C.bγ = C.bγ) :
    ∃ h : G, ∃ hJ : h ∈ Subgroup.closure (longInvSwap G Ω α β),
      h ∈ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω) ∧
        C.psi ⟨h, closure_longInvSwap_le_stabilizer_pair α β hJ⟩ = d := by
  obtain ⟨l, hl, rfl⟩ := C.D.mem_M.mp hdN
  have hlγ : (l : twoPointSection G Ω α β) • C.γ ∈
      orbit (jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β)) C.γ := by
    rw [← C.coord_i₀_eq_iff, C.D.coord_smul l C.γ C.i₀]
    exact hdb.symm
  obtain ⟨o, ho⟩ := hlγ
  have ho' : (o : twoPointSection G Ω α β) • C.γ = (l : twoPointSection G Ω α β) • C.γ := ho
  have hoH : (o : twoPointSection G Ω α β) ∈ jHull (twoPointSection G Ω α β)
      (holtDelta G Ω α β) := jOddCore_le_jHull o.2
  set l' : jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) := ⟨_, hoH⟩⁻¹ * l with hl'
  have hl'L : (l' : twoPointSection G Ω α β) ∈ C.D.L C.i₀ :=
    mul_mem (inv_mem (C.D.oddCore_le C.i₀ o.2)) hl
  have hl'γ : (l' : twoPointSection G Ω α β) • C.γ = C.γ := by
    change ((o : twoPointSection G Ω α β)⁻¹ * l) • C.γ = C.γ
    rw [mul_smul, ← ho', ← mul_smul, inv_mul_cancel, one_smul]
  have hl'ρ : C.D.ρ C.i₀ l' = C.D.ρ C.i₀ l := by
    rw [hl', map_mul, map_inv, C.D.rho_eq_one_of_mem_jOddCore (h := ⟨_, hoH⟩) o.2, inv_one,
      one_mul]
  have hl'J : ((l' : twoPointSection G Ω α β) : Equiv.Perm (holtDelta G Ω α β)) ∈
      twoPointJ G Ω α β := by
    rw [hS.twoPointJ_eq_map_jHull]
    exact ⟨l', l'.2, rfl⟩
  obtain ⟨g, hgJ, hgl⟩ := mem_twoPointJ.mp hl'J
  have hgl' : twoPointElt (closure_longInvSwap_le_stabilizer_pair α β hgJ) =
      (l' : twoPointSection G Ω α β) :=
    Subtype.ext (Equiv.ext fun δ => Subtype.ext (hgl δ).symm)
  have hgα : g • α = α := by
    rw [C.smul_eq_iff_mem_socPre hS hgJ, hgl']
    exact C.D.L_le_socPre C.i₀ hl'L
  have hgβ : g • β = β := by
    rcases smul_pair_of_mem_stabilizer_pair (closure_longInvSwap_le_stabilizer_pair α β hgJ)
      with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd (hgα.symm.trans h) C.ne
  have hgγ : g • (C.γ : Ω) = C.γ := (hgl C.γ).symm.trans (congrArg Subtype.val hl'γ)
  refine ⟨g, hgJ, Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hgα, hgβ⟩, hgγ⟩, ?_⟩
  rw [C.psi_eq_rho hS hgJ, ← hl'ρ]
  exact congrArg (C.D.ρ C.i₀) (Subtype.ext hgl')

end Lift

section YZ

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem fusionIsSylowIn_inf_of_conj_mem {p : ℕ} [Fact p.Prime] {S H N : Subgroup G}
    (hS : fusionIsSylowIn p S H) (hNH : N ≤ H) (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) :
    fusionIsSylowIn p (S ⊓ N) N := by
  refine ⟨inf_le_right, hS.2.1.to_le inf_le_left, fun P hPN hP hle => ?_⟩
  obtain ⟨R, hPR, hR⟩ := exists_fusionIsSylowIn_ge hP (hPN.trans hNH)
  obtain ⟨k, hk, hkR⟩ := exists_mem_conj_of_fusionIsSylowIn hS hR
  have hconj : ∀ x ∈ P, k⁻¹ * x * k ∈ S ⊓ N := fun x hx => ⟨(hkR x).mp (hPR hx), by
    simpa using hN k⁻¹ (inv_mem hk) x (hPN hx)⟩
  have hcard : Nat.card P ≤ Nat.card ↥(S ⊓ N) := Nat.card_le_card_of_injective
    (fun x : P => (⟨k⁻¹ * x * k, hconj x x.2⟩ : ↥(S ⊓ N))) (fun x y h => by
      have h' := congrArg Subtype.val h
      simp only [mul_left_inj, mul_right_inj] at h'
      exact Subtype.ext h')
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_mem_closure_longInvSwap {g : G} (hg : g ∈ stabilizer G α ⊓ stabilizer G β) {x : G}
    (hx : x ∈ Subgroup.closure (longInvSwap G Ω α β)) :
    g * x * g⁻¹ ∈ Subgroup.closure (longInvSwap G Ω α β) := by
  have hle : Subgroup.closure (longInvSwap G Ω α β) ≤
      (Subgroup.closure (longInvSwap G Ω α β)).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr fun j hj => Subgroup.subset_closure ?_
    obtain ⟨hgα, hgβ⟩ := Subgroup.mem_inf.mp hg
    rw [mem_stabilizer_iff] at hgα hgβ
    refine ⟨conj_mem_longInv hj.1 g, ?_⟩
    change (g * j * g⁻¹) • α = β
    rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hgα.symm, hj.2, hgβ]
  exact hle hx

noncomputable def X : Subgroup G :=
  Subgroup.closure (longInvSwap G Ω α β) ⊓
    (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω)) ⊓ C.psiPre C.Rhat

noncomputable def Y : Subgroup G := C.S ⊓ C.X

noncomputable def Z : Subgroup G := C.Y ⊓ C.psiPre C.Zhat

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_X {g : G} : g ∈ C.X ↔ g ∈ Subgroup.closure (longInvSwap G Ω α β) ∧
    g ∈ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω) ∧ g ∈ C.psiPre C.Rhat := by
  simp only [X, Subgroup.mem_inf, and_assoc]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem X_le_stabilizer_inf : C.X ≤ stabilizer G α ⊓ stabilizer G β := fun _ hg =>
  (Subgroup.mem_inf.mp (C.mem_X.mp hg).2.1).1

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem X_le_stabilizer_pair : C.X ≤ stabilizer G ({α, β} : Set Ω) :=
  C.X_le_stabilizer_inf.trans (stabilizer_inf_le_stabilizer_pair α β)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem X_le : C.X ≤ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω) := fun _ hg =>
  (C.mem_X.mp hg).2.1

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem psi_mem_Rhat_of_mem_X {g : G} (hg : g ∈ C.X) :
    C.psi ⟨g, C.X_le_stabilizer_pair hg⟩ ∈ C.Rhat := by
  obtain ⟨hg', h⟩ := C.mem_psiPre.mp (C.mem_X.mp hg).2.2
  exact h

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_mem_X {g : G} (hg : g ∈ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω))
    {x : G} (hx : x ∈ C.X) : g * x * g⁻¹ ∈ C.X := by
  obtain ⟨hxJ, hxs, hxR⟩ := C.mem_X.mp hx
  have hgαβ := (Subgroup.mem_inf.mp hg).1
  have hgγ : g • (C.γ : Ω) = C.γ := (Subgroup.mem_inf.mp hg).2
  have hgp := stabilizer_inf_le_stabilizer_pair α β hgαβ
  have hxp := C.X_le_stabilizer_pair hx
  refine C.mem_X.mpr ⟨conj_mem_closure_longInvSwap hgαβ hxJ, mul_mem (mul_mem hg hxs) (inv_mem hg),
    C.mem_psiPre.mpr ⟨mul_mem (mul_mem hgp hxp) (inv_mem hgp), ?_⟩⟩
  have h := conj_mem_seRadical (C.psi_mem_normalizer ⟨g, hgp⟩)
    (C.psi_apply_bγ (g := ⟨g, hgp⟩) hgγ) (C.psi_mem_Rhat_of_mem_X hx)
  rwa [← map_inv, ← map_mul, ← map_mul] at h

omit [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem fusionIsSylowIn_Y : fusionIsSylowIn 2 C.Y C.X :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  fusionIsSylowIn_inf_of_conj_mem C.sylow C.X_le fun _ hg _ hx => C.conj_mem_X hg hx

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem Y_le_S : C.Y ≤ C.S := inf_le_left

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem Y_le_X : C.Y ≤ C.X := inf_le_right

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem Z_le_Y : C.Z ≤ C.Y := inf_le_left

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_pow_eq_one_of_mem_S {g : G} (hg : g ∈ C.S) : ∃ k : ℕ, g ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := C.sylow.2.1 ⟨g, hg⟩
  exact ⟨k, congrArg Subtype.val hk⟩

end YZ

section Images

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

include C in
theorem v_mem_closure (hS : Sec4Setting G Ω) : v ∈ Subgroup.closure (longInvSwap G Ω α β) := by
  obtain ⟨t, ht, u, hu, -, htu, htuv, -⟩ := C.isTypeL
  have htv : Commute t v := htuv ▸ (Commute.refl t).mul_right htu
  have htC : t ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (htv.symm.zpow_left k).eq
  have hV := C.isPGroup_zpowers
  have h3 := three_le_card_fixSet_of_isTypeL hS.star C.isTypeL
  have htΦ : centralizerImageElt (Ω := Ω) htC ∈ longInv (typeLSection G Ω v)
      (fixSet Ω (Subgroup.zpowers v)) :=
    (hS.mem_longInv_centralizerImage_iff hV h3 _).mpr ⟨t, ht.1, htC, fun ω => rfl⟩
  obtain ⟨y, hy⟩ := longInvSwap_nonempty (hS.star_typeLSection C.isTypeL) C.a C.b
  obtain ⟨g, hg⟩ := exists_conj_eq_of_mem_longInv (hS.star_typeLSection C.isTypeL)
    (hS.holtTheorem1Below_typeLSection C.isTypeL) htΦ hy.1
  obtain ⟨c, hcC, hcg⟩ := mem_centralizerImage.mp g.2
  have hcv : c * v = v * c :=
    (Subgroup.mem_centralizer_iff.mp hcC v (Subgroup.mem_zpowers v)).symm
  set w₀ := c * t * c⁻¹ with hw₀
  have hga : ((((g⁻¹ : typeLSection G Ω v) : Equiv.Perm (fixSet Ω (Subgroup.zpowers v)))
      C.a : fixSet Ω (Subgroup.zpowers v)) : Ω) = c⁻¹ • α := by
    rw [eq_inv_smul_iff, ← hcg]
    change ((((g * g⁻¹ : typeLSection G Ω v) : Equiv.Perm (fixSet Ω (Subgroup.zpowers v)))
      C.a : fixSet Ω (Subgroup.zpowers v)) : Ω) = α
    rw [mul_inv_cancel]
    rfl
  have hw₀α : w₀ • α = β := by
    have h1 := congrArg (fun π : typeLSection G Ω v =>
      (((π : Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) C.a : fixSet Ω _) : Ω)) hg
    rw [show ((((y : typeLSection G Ω v) : Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) C.a :
      fixSet Ω (Subgroup.zpowers v)) : Ω) = β from congrArg Subtype.val hy.2] at h1
    rw [← h1, hw₀, mul_smul, mul_smul, ← hga]
    change c • t • ((((g⁻¹ : typeLSection G Ω v) : Equiv.Perm (fixSet Ω (Subgroup.zpowers v)))
      C.a : fixSet Ω (Subgroup.zpowers v)) : Ω) =
      ((((g : typeLSection G Ω v) : Equiv.Perm (fixSet Ω (Subgroup.zpowers v)))
        (((centralizerImageElt (Ω := Ω) htC : typeLSection G Ω v) :
          Equiv.Perm (fixSet Ω (Subgroup.zpowers v)))
        (((g⁻¹ : typeLSection G Ω v) : Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) C.a)) :
          fixSet Ω (Subgroup.zpowers v)) : Ω)
    rw [hcg]
    rfl
  have hw₀v : w₀ * v = c * u * c⁻¹ := by
    have hu' : u = t * v := by rw [← htuv, ← mul_assoc, mul_self_eq_one_of_mem_longInv ht.1,
      one_mul]
    have hcv' : c⁻¹ * v = v * c⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcv, mul_assoc, mul_inv_cancel, mul_one]
    rw [hw₀, hu', mul_assoc (c * t) c⁻¹ v, hcv']
    group
  have hw₀J : w₀ ∈ longInvSwap G Ω α β := ⟨conj_mem_longInv ht.1 c, hw₀α⟩
  have hw₀vJ : w₀ * v ∈ longInvSwap G Ω α β := ⟨hw₀v ▸ conj_mem_longInv hu.1 c, by
    rw [mul_smul, C.isTypeL.smul_eq, hw₀α]⟩
  have hv : v = w₀ * (w₀ * v) := by
    rw [← mul_assoc, mul_self_eq_one_of_mem_longInv hw₀J.1, one_mul]
  rw [hv]
  exact mul_mem (Subgroup.subset_closure hw₀J) (Subgroup.subset_closure hw₀vJ)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem psi_mul {g h : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    (hh : h ∈ stabilizer G ({α, β} : Set Ω)) :
    C.psi ⟨g * h, mul_mem hg hh⟩ = C.psi ⟨g, hg⟩ * C.psi ⟨h, hh⟩ :=
  map_mul C.psi ⟨g, hg⟩ ⟨h, hh⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem psi_inv {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)) :
    C.psi ⟨g⁻¹, inv_mem hg⟩ = (C.psi ⟨g, hg⟩)⁻¹ :=
  map_inv C.psi ⟨g, hg⟩

theorem exists_mem_X_of_mem_Rhat (hS : Sec4Setting G Ω) {r : Equiv.Perm C.Psi}
    (hr : r ∈ C.Rhat) : ∃ x, ∃ hx : x ∈ C.X, C.psi ⟨x, C.X_le_stabilizer_pair hx⟩ = r := by
  obtain ⟨h, hJ, hst, hψ⟩ := C.exists_lift hS (seRadical_le hr) (apply_eq_of_mem_seRadical hr)
  exact ⟨h, C.mem_X.mpr ⟨hJ, hst, C.mem_psiPre.mpr ⟨_, hψ ▸ hr⟩⟩, hψ⟩

theorem exists_mem_Y_of_mem_Rhat (hS : Sec4Setting G Ω) {r : Equiv.Perm C.Psi}
    (hr : r ∈ C.Rhat) :
    ∃ y, ∃ hy : y ∈ C.Y, C.psi ⟨y, C.X_le_stabilizer_pair (C.Y_le_X hy)⟩ = r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : C.X →* Equiv.Perm C.Psi := C.psi.comp (Subgroup.inclusion C.X_le_stabilizer_pair)
  have hfr : f.range = C.Rhat := by
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      exact C.psi_mem_Rhat_of_mem_X x.2
    · intro hr
      obtain ⟨x, hx, hxr⟩ := C.exists_mem_X_of_mem_Rhat hS hr
      exact ⟨⟨x, hx⟩, hxr⟩
  obtain ⟨T, hT⟩ := exists_sylow_map_eq_of_fusionIsSylowIn C.fusionIsSylowIn_Y
  set T' := T.mapSurjective f.rangeRestrict_surjective
  have hp : IsPGroup 2 f.range := by
    rw [hfr]
    exact C.isNaturalSE_N.isPGroup_seRadical C.bγ
  have htop : (T' : Subgroup f.range) = ⊤ := (T'.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  have hmem : (⟨r, hfr ▸ hr⟩ : f.range) ∈ (T' : Subgroup f.range) := htop ▸ Subgroup.mem_top _
  rw [Sylow.coe_mapSurjective] at hmem
  obtain ⟨t, htT, hft⟩ := hmem
  exact ⟨t, hT ▸ ⟨t, htT, rfl⟩, congrArg Subtype.val hft⟩

theorem eq_of_psi_eq (hS : Sec4Setting G Ω) {y₁ y₂ : G} (h₁ : y₁ ∈ C.Y) (h₂ : y₂ ∈ C.Y)
    (h : C.psi ⟨y₁, C.X_le_stabilizer_pair (C.Y_le_X h₁)⟩ =
      C.psi ⟨y₂, C.X_le_stabilizer_pair (C.Y_le_X h₂)⟩) : y₁ = y₂ := by
  have h₁₂ : y₁ * y₂⁻¹ ∈ C.Y := mul_mem h₁ (inv_mem h₂)
  obtain ⟨k, hk⟩ := C.exists_pow_eq_one_of_mem_S (C.Y_le_S h₁₂)
  have hX := C.mem_X.mp (C.Y_le_X h₁₂)
  have hψ : C.psi ⟨y₁ * y₂⁻¹, closure_longInvSwap_le_stabilizer_pair α β hX.1⟩ = 1 := by
    rw [C.psi_mul (C.X_le_stabilizer_pair (C.Y_le_X h₁))
      (inv_mem (C.X_le_stabilizer_pair (C.Y_le_X h₂))),
      C.psi_inv (C.X_le_stabilizer_pair (C.Y_le_X h₂)), h, mul_inv_cancel]
  have h1 := C.eq_one_of_psi_eq_one' hS hk hX.1
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hX.2.1).1).1 hψ
  exact mul_inv_eq_one.mp h1

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_Z {z : G} : z ∈ C.Z ↔ ∃ hz : z ∈ C.Y,
    C.psi ⟨z, C.X_le_stabilizer_pair (C.Y_le_X hz)⟩ ∈ C.Zhat := by
  refine ⟨fun h => ⟨h.1, ?_⟩, fun ⟨hz, h⟩ => ⟨hz, C.mem_psiPre.mpr ⟨_, h⟩⟩⟩
  obtain ⟨_, h'⟩ := C.mem_psiPre.mp h.2
  exact h'

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem Zhat_le_Rhat : C.Zhat ≤ C.Rhat := inf_le_left

theorem exists_mem_Z_of_mem_Zhat (hS : Sec4Setting G Ω) {r : Equiv.Perm C.Psi}
    (hr : r ∈ C.Zhat) :
    ∃ z, ∃ hz : z ∈ C.Z, C.psi ⟨z, C.X_le_stabilizer_pair (C.Y_le_X (C.Z_le_Y hz))⟩ = r := by
  obtain ⟨y, hy, hyr⟩ := C.exists_mem_Y_of_mem_Rhat hS (C.Zhat_le_Rhat hr)
  exact ⟨y, C.mem_Z.mpr ⟨hy, hyr ▸ hr⟩, hyr⟩

theorem v_mem_Z (hS : Sec4Setting G Ω) : v ∈ C.Z := by
  have hvJ := C.v_mem_closure hS
  have hvst : v ∈ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨C.isTypeL.smul_eq, ?_⟩, ?_⟩
    · have h := C.mem_fixSet
      rw [fixSet_zpowers, mem_fixedBy] at h
      exact h
    · have h := C.γ_mem
      rw [fixSet_zpowers, mem_fixedBy] at h
      exact h
  have hvp := closure_longInvSwap_le_stabilizer_pair α β hvJ
  have hvZ : C.psi ⟨v, hvp⟩ ∈ C.Zhat := by
    refine C.isNaturalSE_N.mem_rootCenter_seRadical (C.psi_mem_N hS hvJ)
      (C.psi_apply_bγ (Subgroup.mem_inf.mp hvst).2) ?_
    rw [← C.psi_mul hvp hvp]
    have hv2 : v * v = 1 := by
      rw [← sq, ← C.isTypeL.orderOf_eq_two, pow_orderOf_eq_one]
    rw [show (⟨v * v, mul_mem hvp hvp⟩ : stabilizer G ({α, β} : Set Ω)) = 1 from
      Subtype.ext hv2, map_one]
  have hvY : v ∈ C.Y := ⟨C.v_mem, C.mem_X.mpr ⟨hvJ, hvst,
    C.mem_psiPre.mpr ⟨hvp, C.Zhat_le_Rhat hvZ⟩⟩⟩
  exact C.mem_Z.mpr ⟨hvY, hvZ⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem psi_mem_Zhat_of_mem_Z {z : G} (hz : z ∈ C.Z) :
    C.psi ⟨z, C.X_le_stabilizer_pair (C.Y_le_X (C.Z_le_Y hz))⟩ ∈ C.Zhat :=
  (C.mem_Z.mp hz).2

theorem mul_self_eq_one_of_mem_Z (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) :
    z * z = 1 := by
  have hzY := C.Z_le_Y hz
  have hzp := C.X_le_stabilizer_pair (C.Y_le_X hzY)
  refine C.eq_of_psi_eq hS (mul_mem hzY hzY) (one_mem _) ?_
  rw [C.psi_mul hzp hzp,
    C.isNaturalSE_N.mul_self_eq_one_of_mem_rootCenter (C.psi_mem_Zhat_of_mem_Z hz)]
  exact (map_one C.psi).symm

theorem commute_of_mem_Z (hS : Sec4Setting G Ω) {z y : G} (hz : z ∈ C.Z) (hy : y ∈ C.Y) :
    z * y = y * z := by
  have hzY := C.Z_le_Y hz
  have hzp := C.X_le_stabilizer_pair (C.Y_le_X hzY)
  have hyp := C.X_le_stabilizer_pair (C.Y_le_X hy)
  refine C.eq_of_psi_eq hS (mul_mem hzY hy) (mul_mem hy hzY) ?_
  rw [C.psi_mul hzp hyp, C.psi_mul hyp hzp]
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp
    (C.psi_mem_Zhat_of_mem_Z hz)).2 _ (C.psi_mem_Rhat_of_mem_X (C.Y_le_X hy))).symm

end Images

section Normalizing

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

theorem exists_lift_normalizer (hS : Sec4Setting G Ω) {d : Equiv.Perm C.Psi} (hdN : d ∈ C.N)
    (hdb : d C.bγ = C.bγ) :
    ∃ h : G, ∃ hJ : h ∈ Subgroup.closure (longInvSwap G Ω α β),
      h ∈ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω) ∧
        (∀ y ∈ C.Y, h * y * h⁻¹ ∈ C.Y) ∧
          C.psi ⟨h, closure_longInvSwap_le_stabilizer_pair α β hJ⟩ = d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h₀, hJ₀, hst₀, hψ₀⟩ := C.exists_lift hS hdN hdb
  set Y' := C.Y.map (MulAut.conj h₀).toMonoidHom
  have hY := C.fusionIsSylowIn_Y
  have hY' : fusionIsSylowIn 2 Y' C.X := by
    refine fusionIsSylowIn_of_card_eq ?_ (hY.2.1.map _) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact C.conj_mem_X hst₀ (C.Y_le_X hy)
    · rw [Subgroup.card_map_of_injective (MulAut.conj h₀).injective]
      exact card_eq_of_fusionIsSylowIn hY
  obtain ⟨o, hoX, ho⟩ := exists_mem_conj_of_fusionIsSylowIn hY hY'
  obtain ⟨y₀, hy₀, hy₀o⟩ := C.exists_mem_Y_of_mem_Rhat hS (C.psi_mem_Rhat_of_mem_X hoX)
  set κ := o * y₀⁻¹
  have hκX : κ ∈ C.X := mul_mem hoX (inv_mem (C.Y_le_X hy₀))
  have hκJ := (C.mem_X.mp hκX).1
  have hψκ : C.psi ⟨κ, C.X_le_stabilizer_pair hκX⟩ = 1 := by
    rw [C.psi_mul (C.X_le_stabilizer_pair hoX) (inv_mem (C.X_le_stabilizer_pair (C.Y_le_X hy₀))),
      C.psi_inv (C.X_le_stabilizer_pair (C.Y_le_X hy₀)), hy₀o, mul_inv_cancel]
  refine ⟨κ⁻¹ * h₀, mul_mem (inv_mem hκJ) hJ₀, mul_mem (inv_mem (C.X_le hκX)) hst₀,
    fun y hy => ?_, ?_⟩
  · have h1 : o⁻¹ * (h₀ * y * h₀⁻¹) * o ∈ C.Y := (ho _).mp ⟨y, hy, rfl⟩
    have h2 : κ⁻¹ * h₀ * y * (κ⁻¹ * h₀)⁻¹ = y₀ * (o⁻¹ * (h₀ * y * h₀⁻¹) * o) * y₀⁻¹ := by
      simp only [κ]
      group
    rw [h2]
    exact mul_mem (mul_mem hy₀ h1) (inv_mem hy₀)
  · rw [C.psi_mul (inv_mem (C.X_le_stabilizer_pair hκX))
      (closure_longInvSwap_le_stabilizer_pair α β hJ₀), C.psi_inv (C.X_le_stabilizer_pair hκX),
      hψκ, inv_one, one_mul, hψ₀]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_mem_B {g : G} (hg : g ∈ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω))
    {δ : Ω} (hδΔ : δ ∈ holtDelta G Ω α β) (hδΦ : δ ∈ fixSet Ω (Subgroup.zpowers v)) :
    g • δ ∈ holtDelta G Ω α β ∧ g • δ ∈ fixSet Ω (Subgroup.zpowers v) := by
  have hgαβ := (Subgroup.mem_inf.mp hg).1
  have hgp := stabilizer_inf_le_stabilizer_pair α β hgαβ
  have hgδ := smul_mem_holtDelta_of_mem_inf hgαβ hδΔ
  refine ⟨hgδ, ?_⟩
  have h := (C.coord_eq_bγ_iff ⟨δ, hδΔ⟩).mpr hδΦ
  have h' : C.D.coord ⟨g • δ, hgδ⟩ C.i₀ = C.bγ := by
    have h1 := C.psi_coord ⟨g, hgp⟩ ⟨δ, hδΔ⟩
    rw [h, C.psi_apply_bγ (g := ⟨g, hgp⟩) (Subgroup.mem_inf.mp hg).2] at h1
    exact h1.symm
  exact (C.coord_eq_bγ_iff ⟨g • δ, hgδ⟩).mp h'

theorem exists_conj_eq_of_mem_Z (hS : Sec4Setting G Ω) {z z' : G} (hz : z ∈ C.Z) (hz1 : z ≠ 1)
    (hz' : z' ∈ C.Z) (hz'1 : z' ≠ 1) :
    ∃ h ∈ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω),
      (∀ y ∈ C.Y, h * y * h⁻¹ ∈ C.Y) ∧ h * z * h⁻¹ = z' := by
  have hzY := C.Z_le_Y hz
  have hz'Y := C.Z_le_Y hz'
  have hne : ∀ {g : G} (hg : g ∈ C.Y), g ≠ 1 →
      C.psi ⟨g, C.X_le_stabilizer_pair (C.Y_le_X hg)⟩ ≠ 1 := fun hg hg1 h =>
    hg1 (C.eq_of_psi_eq hS hg (one_mem _) (h.trans (map_one C.psi).symm))
  have : Nontrivial (C.D.Ψc C.i₀) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by have := C.D.five_le_card C.i₀; omega)
  obtain ⟨c, hc⟩ := exists_ne C.bγ
  obtain ⟨d, hdN, hdb, -, hdz⟩ := C.isNaturalSE_N.exists_conj_eq hc.symm
    (C.psi_mem_Zhat_of_mem_Z hz) (hne hzY hz1) (C.psi_mem_Zhat_of_mem_Z hz') (hne hz'Y hz'1)
  obtain ⟨h, hJ, hst, hY, hψ⟩ := C.exists_lift_normalizer hS hdN hdb
  refine ⟨h, hst, hY, C.eq_of_psi_eq hS (hY z hzY) hz'Y ?_⟩
  have hhp := closure_longInvSwap_le_stabilizer_pair α β hJ
  have hzp := C.X_le_stabilizer_pair (C.Y_le_X hzY)
  rw [C.psi_mul (mul_mem hhp hzp) (inv_mem hhp), C.psi_mul hhp hzp, C.psi_inv hhp, hψ, hdz]

theorem smul_eq_of_mem_Z (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) {δ : Ω}
    (hδΔ : δ ∈ holtDelta G Ω α β) (hδΦ : δ ∈ fixSet Ω (Subgroup.zpowers v)) : z • δ = δ := by
  rcases eq_or_ne z 1 with rfl | hz1
  · exact one_smul G δ
  have hv1 : v ≠ 1 := fun h => by
    have h2 := C.isTypeL.orderOf_eq_two
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨h, hst, -, rfl⟩ := C.exists_conj_eq_of_mem_Z hS (C.v_mem_Z hS) hv1 hz hz1
  obtain ⟨-, hΦ⟩ := C.smul_mem_B (inv_mem hst) hδΔ hδΦ
  rw [fixSet_zpowers, mem_fixedBy] at hΦ
  rw [mul_smul, mul_smul, hΦ, smul_inv_smul]

end Normalizing

section Xelt

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem w_mem_closure : C.w ∈ Subgroup.closure (longInvSwap G Ω α β) :=
  Subgroup.subset_closure C.w_mem

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem w_mem_stabilizer_pair : C.w ∈ stabilizer G ({α, β} : Set Ω) :=
  closure_longInvSwap_le_stabilizer_pair α β C.w_mem_closure

omit [FaithfulSMul G Ω] in
theorem psi_w_mem_Zhat (hS : Sec4Setting G Ω) :
    C.psi ⟨C.w, C.w_mem_stabilizer_pair⟩ ∈ C.Zhat := by
  refine C.isNaturalSE_N.mem_rootCenter_seRadical (C.psi_mem_N hS C.w_mem_closure)
    (C.psi_apply_bγ C.w_fix) ?_
  rw [← C.psi_mul C.w_mem_stabilizer_pair C.w_mem_stabilizer_pair,
    show (⟨C.w * C.w, _⟩ : stabilizer G ({α, β} : Set Ω)) = 1 from
      Subtype.ext (mul_self_eq_one_of_mem_longInv C.w_mem.1), map_one]

open Classical in
noncomputable def x : G :=
  C.w * if h : ∃ z, ∃ hz : z ∈ C.Z, C.psi ⟨z, C.X_le_stabilizer_pair (C.Y_le_X (C.Z_le_Y hz))⟩ =
      C.psi ⟨C.w, C.w_mem_stabilizer_pair⟩ then h.choose else 1

theorem x_spec (hS : Sec4Setting G Ω) : ∃ z₀, ∃ hz₀ : z₀ ∈ C.Z, C.x = C.w * z₀ ∧
    C.psi ⟨z₀, C.X_le_stabilizer_pair (C.Y_le_X (C.Z_le_Y hz₀))⟩ =
      C.psi ⟨C.w, C.w_mem_stabilizer_pair⟩ := by
  have h := C.exists_mem_Z_of_mem_Zhat hS (C.psi_w_mem_Zhat hS)
  obtain ⟨hz, hψ⟩ := h.choose_spec
  refine ⟨h.choose, hz, ?_, hψ⟩
  rw [x, dite_eq_left h]

theorem x_mem_closure (hS : Sec4Setting G Ω) : C.x ∈ Subgroup.closure (longInvSwap G Ω α β) := by
  obtain ⟨z₀, hz₀, hx, -⟩ := C.x_spec hS
  rw [hx]
  exact mul_mem C.w_mem_closure (C.mem_X.mp (C.Y_le_X (C.Z_le_Y hz₀))).1

theorem x_mem_stabilizer_pair (hS : Sec4Setting G Ω) : C.x ∈ stabilizer G ({α, β} : Set Ω) :=
  closure_longInvSwap_le_stabilizer_pair α β (C.x_mem_closure hS)

theorem x_smul (hS : Sec4Setting G Ω) :
    C.x • α = β ∧ C.x • β = α ∧ C.x • (C.γ : Ω) = C.γ := by
  obtain ⟨z₀, hz₀, hx, -⟩ := C.x_spec hS
  have hst := C.X_le (C.Y_le_X (C.Z_le_Y hz₀))
  obtain ⟨⟨hα, hβ⟩, hγ⟩ := Subgroup.mem_inf.mp hst
  obtain ⟨hα, hβ⟩ := Subgroup.mem_inf.mp hst |>.1 |> Subgroup.mem_inf.mp
  rw [mem_stabilizer_iff] at hα hβ hγ
  rw [hx, mul_smul, mul_smul, mul_smul, hα, hβ, hγ, C.w_mem.2, C.w_fix,
    smul_eq_of_orderOf_eq_two C.w_mem.1.1 C.w_mem.2]
  exact ⟨rfl, rfl, rfl⟩

theorem commute_x (hS : Sec4Setting G Ω) {y : G} (hy : y ∈ C.Y) : C.x * y = y * C.x := by
  obtain ⟨z₀, hz₀, hx, -⟩ := C.x_spec hS
  have hwy : C.w * y = y * C.w :=
    (Subgroup.mem_centralizer_iff.mp C.w_comm y (C.Y_le_S hy)).symm
  rw [hx, mul_assoc, C.commute_of_mem_Z hS hz₀ hy, ← mul_assoc, hwy, mul_assoc]

theorem x_mul_self (hS : Sec4Setting G Ω) : C.x * C.x = 1 := by
  obtain ⟨z₀, hz₀, hx, -⟩ := C.x_spec hS
  have hz₀Y := C.Z_le_Y hz₀
  have hwz : C.w * z₀ = z₀ * C.w :=
    (Subgroup.mem_centralizer_iff.mp C.w_comm z₀ (C.Y_le_S hz₀Y)).symm
  rw [hx, mul_assoc, ← mul_assoc z₀, ← hwz, mul_assoc, C.mul_self_eq_one_of_mem_Z hS hz₀,
    mul_one, mul_self_eq_one_of_mem_longInv C.w_mem.1]

theorem psi_x (hS : Sec4Setting G Ω) : C.psi ⟨C.x, C.x_mem_stabilizer_pair hS⟩ = 1 := by
  obtain ⟨z₀, hz₀, hx, hψ⟩ := C.x_spec hS
  have hz₀p := C.X_le_stabilizer_pair (C.Y_le_X (C.Z_le_Y hz₀))
  have h : C.psi ⟨C.x, C.x_mem_stabilizer_pair hS⟩ =
      C.psi ⟨C.w * z₀, mul_mem C.w_mem_stabilizer_pair hz₀p⟩ := by
    congr 2
  rw [h, C.psi_mul C.w_mem_stabilizer_pair hz₀p, hψ,
    ← C.psi_mul C.w_mem_stabilizer_pair C.w_mem_stabilizer_pair,
    show (⟨C.w * C.w, _⟩ : stabilizer G ({α, β} : Set Ω)) = 1
      from Subtype.ext (mul_self_eq_one_of_mem_longInv C.w_mem.1), map_one]

end Xelt

section XJ

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

theorem x_not_mem_longInv (hS : Sec4Setting G Ω) : C.x ∉ longInv G Ω := by
  intro hxJ
  have h3 := three_le_card_holtDelta_of_holtData hS.star C.D
  have hxu : twoPointElt (C.x_mem_stabilizer_pair hS) ∈
      longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    (hS.mem_longInv_twoPointSection_iff C.ne h3 _).mpr ⟨C.x, ⟨hxJ, (C.x_smul hS).1⟩, fun δ => rfl⟩
  have hρ := C.D.rho_mem_longInv hxu C.i₀
  have hψ := C.psi_x hS
  rw [C.psi_eq_rho hS (C.x_mem_closure hS)] at hψ
  have h1 : C.D.ρ C.i₀ ⟨twoPointElt (C.x_mem_stabilizer_pair hS),
      mem_jHull_of_mem_longInv hxu⟩ = 1 := hψ
  rw [h1] at hρ
  have h2 := hρ.1
  rw [orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem mul_mem_longInvAt (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) (hz1 : z ≠ 1) :
    C.x * z ∈ longInvAt G Ω (C.γ : Ω) := by
  have h3 := three_le_card_holtDelta_of_holtData hS.star C.D
  have hzY := C.Z_le_Y hz
  have hzX := C.Y_le_X hzY
  have hzJ := (C.mem_X.mp hzX).1
  have hzp := C.X_le_stabilizer_pair hzX
  obtain ⟨⟨hzα, hzβ⟩, hzγ⟩ := Subgroup.mem_inf.mp (C.X_le hzX) |> fun h =>
    (⟨Subgroup.mem_inf.mp h.1, h.2⟩ : _ ∧ _)
  rw [mem_stabilizer_iff] at hzα hzγ
  obtain ⟨hxα, -, hxγ⟩ := C.x_smul hS
  have hxzJ : C.x * z ∈ Subgroup.closure (longInvSwap G Ω α β) :=
    mul_mem (C.x_mem_closure hS) hzJ
  have hxzp := closure_longInvSwap_le_stabilizer_pair α β hxzJ
  have hxzα : (C.x * z) • α = β := by rw [mul_smul, hzα, hxα]
  have hxzγ : (C.x * z) • (C.γ : Ω) = C.γ := by rw [mul_smul, hzγ, hxγ]
  have hxz2 : C.x * z * (C.x * z) = 1 := by
    rw [mul_assoc, ← mul_assoc z, ← C.commute_x hS hzY, mul_assoc,
      C.mul_self_eq_one_of_mem_Z hS hz, mul_one, C.x_mul_self hS]
  have hord : orderOf (C.x * z) = 2 := orderOf_eq_prime (by rw [sq]; exact hxz2) fun h => C.ne
    (by rw [h, one_smul] at hxzα; exact hxzα)
  set X := twoPointElt hxzp with hXdef
  have hXH := twoPointElt_mem_jHull hS.star hxzJ
  have hXnot : X ∉ C.D.socPre := fun h =>
    C.ne (((C.smul_eq_iff_mem_socPre hS hxzJ).mpr h).symm.trans hxzα)
  have hψxz : C.psi ⟨C.x * z, hxzp⟩ = C.psi ⟨z, hzp⟩ := by
    rw [C.psi_mul (C.x_mem_stabilizer_pair hS) hzp, C.psi_x hS, one_mul]
  have hnZ := C.psi_mem_Zhat_of_mem_Z hz
  have hnN : C.psi ⟨z, hzp⟩ ∈ C.N := seRadical_le (C.Zhat_le_Rhat hnZ)
  have hn1 : C.psi ⟨z, hzp⟩ ≠ 1 := fun h =>
    hz1 (C.eq_of_psi_eq hS hzY (one_mem _) (h.trans (map_one C.psi).symm))
  have hn2 := C.isNaturalSE_N.mul_self_eq_one_of_mem_rootCenter hnZ
  have hρt := C.D.rho_mem_longInv C.D.t_mem C.i₀
  have hρtN := C.D.rho_mem_M_of_isNaturalSE C.isNaturalSE_N C.D.tHull
  obtain ⟨m, hm⟩ := isConj_iff.mp (C.isNaturalSE_N.isConj (x := ⟨_, hρtN⟩)
    (y := ⟨_, hnN⟩) (by rw [Subgroup.orderOf_mk]; exact hρt.1)
    (by rw [Subgroup.orderOf_mk]; exact orderOf_eq_prime (by rw [sq]; exact hn2) hn1))
  obtain ⟨l, -, hlm⟩ := C.D.mem_M.mp m.2
  set u : twoPointSection G Ω α β := (l : twoPointSection G Ω α β) * C.D.t * (l : _)⁻¹
  have huJ : u ∈ longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    conj_mem_longInv C.D.t_mem _
  have huH := mem_jHull_of_mem_longInv huJ
  have hρu : C.D.ρ C.i₀ ⟨u, huH⟩ = C.psi ⟨z, hzp⟩ := by
    rw [show (⟨u, huH⟩ : jHull (twoPointSection G Ω α β) (holtDelta G Ω α β)) =
      l * C.D.tHull * l⁻¹ from rfl, map_mul, map_mul, map_inv, hlm]
    exact congrArg Subtype.val hm
  have hk : X * u⁻¹ ∈ jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) := by
    rw [← C.D.socPre_inf_jOrbitKernel]
    refine ⟨(C.mul_mem_socPre_iff hS hXH (inv_mem huH)).mpr
      (iff_of_false hXnot fun h => C.not_mem_socPre_of_mem_longInv hS huJ (by
        simpa using inv_mem h)), ?_⟩
    refine (C.D.mem_jOrbitKernel_iff_rho (h := ⟨X, hXH⟩ * ⟨u, huH⟩⁻¹)).mpr fun j => ?_
    rcases C.eq_i₀ j with rfl
    rw [map_mul, map_inv, hρu, ← hψxz, C.psi_eq_rho hS hxzJ, mul_inv_cancel]
  have hu2 := mul_self_eq_one_of_mem_longInv huJ
  have hX2 : X * X = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, hXdef, ← map_mul]
    exact (congrArg (twoPointHom G Ω α β) (Subtype.ext hxz2 :
      (⟨C.x * z, hxzp⟩ : stabilizer G ({α, β} : Set Ω)) * ⟨C.x * z, hxzp⟩ = 1)).trans
        (map_one _))
  have hodd : Odd (orderOf (X * u)) := by
    rw [show X * u = X * u⁻¹ by rw [inv_eq_of_mul_eq_one_right hu2]]
    exact odd_card_jOddCore.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hk)
  obtain ⟨g, -, hg⟩ := exists_mem_zpowers_conj_eq_of_odd hX2 hu2 hodd
  have hXJ : X ∈ longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) := by
    have h := conj_mem_longInv huJ g⁻¹
    rwa [← hg, show g⁻¹ * (g * X * g⁻¹) * g⁻¹⁻¹ = X by group] at h
  obtain ⟨δ₀, hδ₀, huniq⟩ := hXJ.2
  refine ⟨(hS.mem_longInv_iff_of_odd_twoPointKernel C.ne C.odd_twoPointKernel h3 hord
    hxzα).mpr ⟨δ₀, ⟨δ₀.2, congrArg Subtype.val hδ₀⟩, fun δ ⟨hδ, hδf⟩ =>
      congrArg Subtype.val (huniq ⟨δ, hδ⟩ (Subtype.ext hδf))⟩, hxzγ⟩

end XJ

section Phi

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_centralizer_zpowers {g : G} (h : Commute v g) :
    g ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hh => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (h.zpow_left k).eq

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem v_smul_eq (ω : fixSet Ω (Subgroup.zpowers v)) : v • (ω : Ω) = ω :=
  ω.2 v (Subgroup.mem_zpowers v)

theorem mem_centralizer_of_mem_Z (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) :
    z ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
  mem_centralizer_zpowers (C.commute_of_mem_Z hS hz (C.Z_le_Y (C.v_mem_Z hS))).symm

theorem x_mem_centralizer (hS : Sec4Setting G Ω) :
    C.x ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
  mem_centralizer_zpowers (C.commute_x hS (C.Z_le_Y (C.v_mem_Z hS))).symm

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
include C in
theorem v_ne_one : v ≠ 1 := fun h => by
  have h2 := C.isTypeL.orderOf_eq_two
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem x_phi_mem_longInv (hS : Sec4Setting G Ω) :
    centralizerImageElt (Ω := Ω) (C.x_mem_centralizer hS) ∈
      longInv (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) := by
  have hv := C.v_mem_Z hS
  refine (hS.mem_longInv_centralizerImage_iff C.isPGroup_zpowers
    (three_le_card_fixSet_of_isTypeL hS.star C.isTypeL) _).mpr
    ⟨C.x * v, (C.mul_mem_longInvAt hS hv C.v_ne_one).1,
      mul_mem (C.x_mem_centralizer hS) (C.mem_centralizer_of_mem_Z hS hv), fun ω => ?_⟩
  rw [coe_centralizerImageElt_apply, mul_smul, v_smul_eq]

theorem xz_phi_mem_longInv (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) (hz1 : z ≠ 1) :
    centralizerImageElt (Ω := Ω)
      (mul_mem (C.x_mem_centralizer hS) (C.mem_centralizer_of_mem_Z hS hz)) ∈
        longInv (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
  (hS.mem_longInv_centralizerImage_iff C.isPGroup_zpowers
    (three_le_card_fixSet_of_isTypeL hS.star C.isTypeL) _).mpr
    ⟨C.x * z, (C.mul_mem_longInvAt hS hz hz1).1,
      mul_mem (C.x_mem_centralizer hS) (C.mem_centralizer_of_mem_Z hS hz), fun _ => rfl⟩

theorem z_phi_eq (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) :
    centralizerImageElt (Ω := Ω) (C.mem_centralizer_of_mem_Z hS hz) =
      (centralizerImageElt (Ω := Ω) (C.x_mem_centralizer hS))⁻¹ * centralizerImageElt (Ω := Ω)
        (mul_mem (C.x_mem_centralizer hS) (C.mem_centralizer_of_mem_Z hS hz)) := by
  refine Subtype.ext (Equiv.ext fun ω => ?_)
  change _ = ((centralizerImageElt (Ω := Ω) (C.x_mem_centralizer hS) :
    Equiv.Perm (fixSet Ω (Subgroup.zpowers v)))⁻¹
      ((centralizerImageElt (Ω := Ω) (mul_mem (C.x_mem_centralizer hS)
        (C.mem_centralizer_of_mem_Z hS hz)) : Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) ω))
  rw [eq_comm, Equiv.Perm.inv_eq_iff_eq]
  exact Subtype.ext (mul_smul _ _ _)

theorem z_phi_mem_jHull (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) :
    centralizerImageElt (Ω := Ω) (C.mem_centralizer_of_mem_Z hS hz) ∈
      jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) := by
  rcases eq_or_ne z 1 with rfl | hz1
  · rw [show centralizerImageElt (Ω := Ω) (C.mem_centralizer_of_mem_Z hS hz) = 1 from
      Subtype.ext (by ext ω; simp)]
    exact one_mem _
  rw [C.z_phi_eq hS hz]
  exact mul_mem (inv_mem (mem_jHull_of_mem_longInv (C.x_phi_mem_longInv hS)))
    (mem_jHull_of_mem_longInv (C.xz_phi_mem_longInv hS hz hz1))

noncomputable abbrev zH (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) :
    jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
  ⟨_, C.z_phi_mem_jHull hS hz⟩

noncomputable abbrev xH (hS : Sec4Setting G Ω) :
    jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
  ⟨_, mem_jHull_of_mem_longInv (C.x_phi_mem_longInv hS)⟩

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem rho_mem_rootCenter_of_mem_longInv {π : typeLSection G Ω v}
    (hπ : π ∈ longInv (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) (hπab : π • C.a = C.b)
    {k : C.Dv.ι} (hk : k ≠ C.i) :
    C.Dv.ρ k ⟨π, mem_jHull_of_mem_longInv hπ⟩ ∈
        rootCenter (seRadical (C.Dv.M k) (C.Dv.coord C.a k)) ∧
      C.Dv.ρ k ⟨π, mem_jHull_of_mem_longInv hπ⟩ ≠ 1 := by
  have hρ := C.Dv.rho_mem_longInv hπ k
  refine ⟨(C.isNaturalSE_Dv k).mem_rootCenter_seRadical
    (C.Dv.rho_mem_M_of_isNaturalSE (C.isNaturalSE_Dv k) _) ?_
    (mul_self_eq_one_of_mem_longInv hρ), fun h => ?_⟩
  · rw [← C.Dv.coord_smul, show (π : typeLSection G Ω v) • C.a = C.b from hπab, C.coord_eq k hk]
  · have h2 := hρ.1
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)

theorem x_phi_smul_a (hS : Sec4Setting G Ω) :
    centralizerImageElt (Ω := Ω) (C.x_mem_centralizer hS) • C.a = C.b :=
  Subtype.ext (C.x_smul hS).1

theorem xz_phi_smul_a (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) :
    centralizerImageElt (Ω := Ω)
      (mul_mem (C.x_mem_centralizer hS) (C.mem_centralizer_of_mem_Z hS hz)) • C.a = C.b := by
  have hzα : z • α = α := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp
    (C.X_le (C.Y_le_X (C.Z_le_Y hz)))).1).1
  exact Subtype.ext (by
    change (C.x * z) • α = β
    rw [mul_smul, hzα, (C.x_smul hS).1])

end Phi

end FinConfig

end CFSG.Holt.H78
