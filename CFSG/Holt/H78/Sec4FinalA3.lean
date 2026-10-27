module

public import CFSG.Holt.H78.Sec4FinalA2

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open CFSG.GH74.Uniqueness.Bender (rootCenter)
open scoped Pointwise

noncomputable def hvPre {G : Type} [Group G] (Ω : Type) [MulAction G Ω] (v : G) : Subgroup G :=
  ((jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))).comap
    (MulAction.toPermHom (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
      (fixSet Ω (Subgroup.zpowers v))).rangeRestrict).map
    (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)).subtype

theorem mem_hvPre {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {v g : G} :
    g ∈ hvPre Ω v ↔
      ∃ hg : g ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G),
        centralizerImageElt (Ω := Ω) hg ∈
          jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) := by
  refine ⟨?_, fun ⟨hg, h⟩ => ⟨⟨g, hg⟩, h, rfl⟩⟩
  rintro ⟨⟨g, hg⟩, h, rfl⟩
  exact ⟨hg, h⟩

namespace FinConfig

section Coord3

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem centralizerImageElt_mul {g h : G}
    (hg : g ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (hh : h ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    centralizerImageElt (Ω := Ω) (mul_mem hg hh) =
      centralizerImageElt (Ω := Ω) hg * centralizerImageElt (Ω := Ω) hh :=
  Subtype.ext (map_mul (MulAction.toPermHom (Subgroup.centralizer
    ((Subgroup.zpowers v : Subgroup G) : Set G)) (fixSet Ω (Subgroup.zpowers v))) ⟨g, hg⟩ ⟨h, hh⟩)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem centralizerImageElt_inv {g : G}
    (hg : g ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    centralizerImageElt (Ω := Ω) (inv_mem hg) = (centralizerImageElt (Ω := Ω) hg)⁻¹ :=
  Subtype.ext (map_inv (MulAction.toPermHom (Subgroup.centralizer
    ((Subgroup.zpowers v : Subgroup G) : Set G)) (fixSet Ω (Subgroup.zpowers v))) ⟨g, hg⟩)

theorem zH_eq (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) (hz1 : z ≠ 1) :
    C.zH hS hz = (C.xH hS)⁻¹ * ⟨_, mem_jHull_of_mem_longInv (C.xz_phi_mem_longInv hS hz hz1)⟩ :=
  Subtype.ext (C.z_phi_eq hS hz)

theorem zH_one (hS : Sec4Setting G Ω) : C.zH hS (one_mem C.Z) = 1 :=
  Subtype.ext (Subtype.ext (by ext ω; simp))

theorem rho_zH_mem (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) {k : C.Dv.ι} (hk : k ≠ C.i) :
    C.Dv.ρ k (C.zH hS hz) ∈ rootCenter (seRadical (C.Dv.M k) (C.Dv.coord C.a k)) := by
  rcases eq_or_ne z 1 with rfl | hz1
  · rw [C.zH_one hS, map_one]
    exact one_mem _
  rw [C.zH_eq hS hz hz1, map_mul, map_inv]
  exact mul_mem (inv_mem (C.rho_mem_rootCenter_of_mem_longInv (C.x_phi_mem_longInv hS)
    (C.x_phi_smul_a hS) hk).1) (C.rho_mem_rootCenter_of_mem_longInv
      (C.xz_phi_mem_longInv hS hz hz1) (C.xz_phi_smul_a hS hz) hk).1

theorem rho_zH_ne_rho_xH (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) {k : C.Dv.ι}
    (hk : k ≠ C.i) : C.Dv.ρ k (C.zH hS hz) ≠ C.Dv.ρ k (C.xH hS) := by
  have hx := C.rho_mem_rootCenter_of_mem_longInv (C.x_phi_mem_longInv hS) (C.x_phi_smul_a hS) hk
  rcases eq_or_ne z 1 with rfl | hz1
  · rw [C.zH_one hS, map_one]
    exact hx.2.symm
  intro h
  have hxz := C.rho_mem_rootCenter_of_mem_longInv (C.xz_phi_mem_longInv hS hz hz1)
    (C.xz_phi_smul_a hS hz) hk
  refine hxz.2 ?_
  have h1 : (⟨_, mem_jHull_of_mem_longInv (C.xz_phi_mem_longInv hS hz hz1)⟩ :
      jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) = C.xH hS * C.zH hS hz := by
    rw [C.zH_eq hS hz hz1, mul_inv_cancel_left]
  rw [h1, map_mul, h, (C.isNaturalSE_Dv k).mul_self_eq_one_of_mem_rootCenter hx.1]

theorem rho_zH_i (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) :
    C.Dv.ρ C.i (C.zH hS hz) = 1 := by
  have hst := C.X_le (C.Y_le_X (C.Z_le_Y hz))
  have hzα : z • α = α := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hst).1).1
  have hzβ : z • β = β := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hst).1).2
  have hM := C.isNaturalSE_Dv C.i
  have hfix : ∀ ω : fixSet Ω (Subgroup.zpowers v), z • (ω : Ω) = ω →
      C.Dv.ρ C.i (C.zH hS hz) (C.Dv.coord ω C.i) = C.Dv.coord ω C.i := fun ω h => by
    rw [← C.Dv.coord_smul]
    exact congrArg (fun p => C.Dv.coord p C.i) (Subtype.ext h)
  have h2 : C.Dv.ρ C.i (C.zH hS hz) ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq, ← map_mul]
    have : C.zH hS hz * C.zH hS hz = 1 := by
      refine Subtype.ext (Subtype.ext (Equiv.ext fun ω => Subtype.ext ?_))
      change z • z • (ω : Ω) = ω
      rw [← mul_smul, C.mul_self_eq_one_of_mem_Z hS hz, one_smul]
    rw [this, map_one]
  have hR := mem_seRadical_of_pow_eq_one (C.Dv.rho_mem_M_of_isNaturalSE hM _) (hfix C.a hzα) h2
  exact hM.eq_one_of_mem_seRadical hR (Ne.symm C.coord_ne) (hfix C.b hzβ)

end Coord3

section F2

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem eq_one_of_pow_two_pow_of_pow_odd {H : Type*} [Group H] {y : H} {j m : ℕ}
    (h1 : y ^ 2 ^ j = 1) (hm : Odd m) (h2 : y ^ m = 1) : y = 1 := by
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  have h3 : 2 ^ e ∣ m := he ▸ orderOf_dvd_of_pow_eq_one h2
  rcases e with _ | e
  · rwa [pow_zero, orderOf_eq_one_iff] at he
  · exact absurd (hm.of_dvd_nat h3) (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two,
      by omega⟩))

omit [FaithfulSMul G Ω] in
theorem odd_orderOf_of_psi_eq_one (hS : Sec4Setting G Ω) {g : G}
    (hg : g ∈ stabilizer G α ⊓ stabilizer G β)
    (hψ : C.psi ⟨g, stabilizer_inf_le_stabilizer_pair α β hg⟩ = 1)
    (hB : ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω (Subgroup.zpowers v) → g • δ = δ) :
    Odd (orderOf g) := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hgm : g ^ m ∈ stabilizer G α ⊓ stabilizer G β := pow_mem hg m
  have hψm : C.psi ⟨g ^ m, stabilizer_inf_le_stabilizer_pair α β hgm⟩ = 1 := by
    rw [show (⟨g ^ m, stabilizer_inf_le_stabilizer_pair α β hgm⟩ :
      stabilizer G ({α, β} : Set Ω)) = ⟨g, stabilizer_inf_le_stabilizer_pair α β hg⟩ ^ m
        from rfl, map_pow, hψ, one_pow]
  have hBm : ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω (Subgroup.zpowers v) → g ^ m • δ = δ :=
    fun δ hδ hδ' => mem_stabilizer_iff.mp (pow_mem (mem_stabilizer_iff.mpr (hB δ hδ hδ')) m)
  have h2 : (g ^ m) ^ 2 ^ a = 1 := by rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one (C.eq_one_of_psi_eq_one hS h2 hgm hψm hBm))

theorem exists_lift_coord (hS : Sec4Setting G Ω) {k : C.Dv.ι} (hk : k ≠ C.i)
    {l : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))}
    (hl : (l : typeLSection G Ω v) ∈ C.Dv.L k)
    (hla : C.Dv.ρ k l (C.Dv.coord C.a k) = C.Dv.coord C.a k) :
    ∃ c, ∃ hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G),
      centralizerImageElt (Ω := Ω) hc = (l : typeLSection G Ω v) ∧
        c ∈ stabilizer G α ⊓ stabilizer G β ∧
          ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω (Subgroup.zpowers v) → c • δ = δ := by
  obtain ⟨c, hc, hcl⟩ := mem_centralizerImage.mp ((l : typeLSection G Ω v)).2
  have hfix : ∀ ω : fixSet Ω (Subgroup.zpowers v), C.Dv.coord ω k = C.Dv.coord C.a k →
      c • (ω : Ω) = ω := fun ω hω => by
    rw [← hcl ω]
    refine congrArg Subtype.val (C.coord_Dv_injective (funext fun j => ?_))
    change C.Dv.coord ((l : typeLSection G Ω v) • ω) j = C.Dv.coord ω j
    rw [C.Dv.coord_smul]
    rcases eq_or_ne j k with rfl | hj
    · rw [hω, hla]
    · rw [C.Dv.rho_eq_one_of_mem_L (Ne.symm hj) hl, Equiv.Perm.one_apply]
  refine ⟨c, hc, Subtype.ext (Equiv.ext fun ω => Subtype.ext (hcl ω).symm),
    Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr (hfix C.a rfl),
      mem_stabilizer_iff.mpr (hfix C.b (C.coord_eq k hk).symm)⟩, fun δ hδ hδΦ => ?_⟩
  exact hfix ⟨δ, hδΦ⟩ ((C.coord_of_mem_B hS hδ hδΦ).1 k hk)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem centralizerImageElt_pow {g : G}
    (hg : g ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) (n : ℕ) :
    centralizerImageElt (Ω := Ω) (pow_mem hg n) = (centralizerImageElt (Ω := Ω) hg) ^ n :=
  Subtype.ext (map_pow (MulAction.toPermHom (Subgroup.centralizer
    ((Subgroup.zpowers v : Subgroup G) : Set G)) (fixSet Ω (Subgroup.zpowers v))) ⟨g, hg⟩ n)

end F2

section Qt

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

noncomputable def Qt : Subgroup G :=
  hvPre Ω v ⊓ (stabilizer G α ⊓ stabilizer G β) ⊓
    fixingSubgroup G (holtDelta G Ω α β ∩ fixSet Ω (Subgroup.zpowers v)) ⊓ C.psiPre C.Zhat

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_Qt {g : G} : g ∈ C.Qt ↔ g ∈ hvPre Ω v ∧ g ∈ stabilizer G α ⊓ stabilizer G β ∧
    (∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω (Subgroup.zpowers v) → g • δ = δ) ∧
      g ∈ C.psiPre C.Zhat := by
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, fun δ hδ hδ' => (mem_fixingSubgroup_iff G).mp h3 δ ⟨hδ, hδ'⟩, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, (mem_fixingSubgroup_iff G).mpr fun δ hδ => h3 δ hδ.1 hδ.2⟩, h4⟩

theorem Z_le_Qt (hS : Sec4Setting G Ω) : C.Z ≤ C.Qt := fun z hz => by
  have hst := C.X_le (C.Y_le_X (C.Z_le_Y hz))
  refine C.mem_Qt.mpr ⟨mem_hvPre.mpr ⟨C.mem_centralizer_of_mem_Z hS hz,
    C.z_phi_mem_jHull hS hz⟩, (Subgroup.mem_inf.mp hst).1, fun δ hδ hδ' =>
      C.smul_eq_of_mem_Z hS hz hδ hδ', C.mem_psiPre.mpr ⟨_, C.psi_mem_Zhat_of_mem_Z hz⟩⟩

theorem fusionIsSylowIn_Z_Qt (hS : Sec4Setting G Ω) : fusionIsSylowIn 2 C.Z C.Qt := by
  refine ⟨C.Z_le_Qt hS, C.sylow.2.1.to_le (C.Z_le_Y.trans C.Y_le_S), fun P hPQ hP hZP => ?_⟩
  refine le_antisymm (fun p hp => ?_) hZP
  obtain ⟨hpH, hpst, hpB, hpψ⟩ := C.mem_Qt.mp (hPQ hp)
  obtain ⟨hpp, hpZ⟩ := C.mem_psiPre.mp hpψ
  obtain ⟨z, hz, hzp⟩ := C.exists_mem_Z_of_mem_Zhat hS hpZ
  have hzst := (Subgroup.mem_inf.mp (C.X_le (C.Y_le_X (C.Z_le_Y hz)))).1
  have hq : p * z⁻¹ ∈ P := mul_mem hp (inv_mem (hZP hz))
  obtain ⟨k, hk⟩ := hP ⟨_, hq⟩
  have hk' : (p * z⁻¹) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hqst : p * z⁻¹ ∈ stabilizer G α ⊓ stabilizer G β := mul_mem hpst (inv_mem hzst)
  have h1 := C.eq_one_of_psi_eq_one hS hk' hqst (by
    rw [C.psi_mul hpp (inv_mem (stabilizer_inf_le_stabilizer_pair α β hzst)),
      C.psi_inv (stabilizer_inf_le_stabilizer_pair α β hzst)]
    exact mul_inv_eq_one.mpr hzp.symm) (fun δ hδ hδ' => by
      rw [mul_smul, inv_smul_eq_iff.mpr (C.smul_eq_of_mem_Z hS hz hδ hδ').symm, hpB δ hδ hδ'])
  rw [mul_inv_eq_one.mp h1]
  exact hz

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_mem_Qt {c : G} (hcH : c ∈ hvPre Ω v) (hcst : c ∈ stabilizer G α ⊓ stabilizer G β)
    (hcB : ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω (Subgroup.zpowers v) → c • δ = δ) {q : G}
    (hq : q ∈ C.Qt) : c * q * c⁻¹ ∈ C.Qt := by
  obtain ⟨hqH, hqst, hqB, hqψ⟩ := C.mem_Qt.mp hq
  have hcp := stabilizer_inf_le_stabilizer_pair α β hcst
  have hqp := stabilizer_inf_le_stabilizer_pair α β hqst
  refine C.mem_Qt.mpr ⟨mul_mem (mul_mem hcH hqH) (inv_mem hcH),
    mul_mem (mul_mem hcst hqst) (inv_mem hcst), fun δ hδ hδ' => ?_,
    C.mem_psiPre.mpr ⟨mul_mem (mul_mem hcp hqp) (inv_mem hcp), ?_⟩⟩
  · rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr (hcB δ hδ hδ').symm, hqB δ hδ hδ', hcB δ hδ hδ']
  · obtain ⟨hqp', hqZ⟩ := C.mem_psiPre.mp hqψ
    have h := conj_mem_rootCenter_seRadical (C.psi_mem_normalizer ⟨c, hcp⟩)
      (C.psi_apply_bγ (g := ⟨c, hcp⟩) (hcB _ C.γ.2 C.γ_mem)) hqZ
    rwa [← map_inv, ← map_mul, ← map_mul] at h

theorem exists_normalizer_Z (hS : Sec4Setting G Ω) {c : G} (hcH : c ∈ hvPre Ω v)
    (hcst : c ∈ stabilizer G α ⊓ stabilizer G β)
    (hcB : ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω (Subgroup.zpowers v) → c • δ = δ) :
    ∃ κ, ∃ hκ : κ ∈ C.Qt, C.psi ⟨κ, stabilizer_inf_le_stabilizer_pair α β
      (C.mem_Qt.mp hκ).2.1⟩ = 1 ∧ ∀ z ∈ C.Z, κ⁻¹ * c * z * (κ⁻¹ * c)⁻¹ ∈ C.Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := C.fusionIsSylowIn_Z_Qt hS
  have hZ' : fusionIsSylowIn 2 (C.Z.map (MulAut.conj c).toMonoidHom) C.Qt := by
    refine fusionIsSylowIn_of_card_eq ?_ (hZ.2.1.map _) ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact C.conj_mem_Qt hcH hcst hcB (C.Z_le_Qt hS hz)
    · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
      exact card_eq_of_fusionIsSylowIn hZ
  obtain ⟨o, hoQ, ho⟩ := exists_mem_conj_of_fusionIsSylowIn hZ hZ'
  obtain ⟨-, -, -, hoψ⟩ := C.mem_Qt.mp hoQ
  obtain ⟨hop, hoZ⟩ := C.mem_psiPre.mp hoψ
  obtain ⟨z', hz', hz'o⟩ := C.exists_mem_Z_of_mem_Zhat hS hoZ
  have hz'p := C.X_le_stabilizer_pair (C.Y_le_X (C.Z_le_Y hz'))
  refine ⟨o * z'⁻¹, mul_mem hoQ (inv_mem (C.Z_le_Qt hS hz')), ?_, fun z hz => ?_⟩
  · rw [C.psi_mul hop (inv_mem hz'p), C.psi_inv hz'p, hz'o, mul_inv_cancel]
  · have h1 : o⁻¹ * (c * z * c⁻¹) * o ∈ C.Z := (ho _).mp ⟨z, hz, rfl⟩
    have h2 : (o * z'⁻¹)⁻¹ * c * z * ((o * z'⁻¹)⁻¹ * c)⁻¹ =
        z' * (o⁻¹ * (c * z * c⁻¹) * o) * z'⁻¹ := by group
    rw [h2]
    exact mul_mem (mul_mem hz' h1) (inv_mem hz')

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem rho_pow_orderOf {g : G}
    (hg : g ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (hgH : centralizerImageElt (Ω := Ω) hg ∈
      jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) (k : C.Dv.ι) :
    C.Dv.ρ k ⟨_, hgH⟩ ^ orderOf g = 1 := by
  have hpow : (⟨_, hgH⟩ : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) ^
      orderOf g = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow]
    show (centralizerImageElt (Ω := Ω) hg) ^ orderOf g = 1
    rw [← centralizerImageElt_pow hg]
    refine Subtype.ext (Equiv.ext fun ω => Subtype.ext ?_)
    change g ^ orderOf g • (ω : Ω) = ω
    rw [pow_orderOf_eq_one, one_smul]
  rw [← map_pow, hpow, map_one]

theorem rho_eq_one_of_mem_Qt (hS : Sec4Setting G Ω) {κ : G} (hκ : κ ∈ C.Qt)
    (hψ : C.psi ⟨κ, stabilizer_inf_le_stabilizer_pair α β (C.mem_Qt.mp hκ).2.1⟩ = 1)
    {k : C.Dv.ι} (hk : k ≠ C.i)
    (hκC : κ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (hκH : centralizerImageElt (Ω := Ω) hκC ∈
      jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) :
    C.Dv.ρ k ⟨_, hκH⟩ = 1 := by
  obtain ⟨-, hκst, hκB, -⟩ := C.mem_Qt.mp hκ
  set p := C.Dv.ρ k ⟨_, hκH⟩ with hp
  have hM := C.isNaturalSE_Dv k
  have hpN : p ∈ Subgroup.normalizer (C.Dv.M k : Set (Equiv.Perm (C.Dv.Ψc k))) :=
    Subgroup.le_normalizer (C.Dv.rho_mem_M_of_isNaturalSE hM _)
  have hpa : p (C.Dv.coord C.a k) = C.Dv.coord C.a k := by
    rw [hp, ← C.Dv.coord_smul]
    exact congrArg (fun ω => C.Dv.coord ω k)
      (Subtype.ext (mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hκst).1))
  have hodd := C.odd_orderOf_of_psi_eq_one hS hκst hψ hκB
  have hcomm : ∀ r ∈ seRadical (C.Dv.M k) (C.Dv.coord C.a k), p * r = r * p := by
    intro r hr
    obtain ⟨l, hlL, hlr⟩ := C.Dv.mem_M.mp (seRadical_le hr)
    obtain ⟨c, hc, hcl, hcst, hcB⟩ := C.exists_lift_coord hS hk hlL
      (by rw [hlr]; exact apply_eq_of_mem_seRadical hr)
    have hcH : centralizerImageElt (Ω := Ω) hc ∈
        jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) := hcl ▸ l.2
    have hcρ : C.Dv.ρ k ⟨_, hcH⟩ = r := by rw [← hlr]; exact congrArg _ (Subtype.ext hcl)
    have hqC := mul_mem (mul_mem (mul_mem hκC hc) (inv_mem hκC)) (inv_mem hc)
    have hqst := mul_mem (mul_mem (mul_mem hκst hcst) (inv_mem hκst)) (inv_mem hcst)
    have hκp := stabilizer_inf_le_stabilizer_pair α β hκst
    have hcp := stabilizer_inf_le_stabilizer_pair α β hcst
    have hqψ : C.psi ⟨κ * c * κ⁻¹ * c⁻¹, stabilizer_inf_le_stabilizer_pair α β hqst⟩ = 1 := by
      rw [C.psi_mul (mul_mem (mul_mem hκp hcp) (inv_mem hκp)) (inv_mem hcp),
        C.psi_mul (mul_mem hκp hcp) (inv_mem hκp), C.psi_mul hκp hcp, C.psi_inv hκp,
        C.psi_inv hcp, hψ]
      group
    have hqB : ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω (Subgroup.zpowers v) →
        (κ * c * κ⁻¹ * c⁻¹) • δ = δ := fun δ hδ hδ' => by
      have h1 := hκB δ hδ hδ'
      have h2 := hcB δ hδ hδ'
      rw [mul_smul, mul_smul, mul_smul, inv_smul_eq_iff.mpr h2.symm,
        inv_smul_eq_iff.mpr h1.symm, h2, h1]
    have hqodd := C.odd_orderOf_of_psi_eq_one hS hqst hqψ hqB
    have hqΦ : centralizerImageElt (Ω := Ω) hqC = centralizerImageElt (Ω := Ω) hκC *
        centralizerImageElt (Ω := Ω) hc * (centralizerImageElt (Ω := Ω) hκC)⁻¹ *
          (centralizerImageElt (Ω := Ω) hc)⁻¹ := by
      rw [centralizerImageElt_mul (mul_mem (mul_mem hκC hc) (inv_mem hκC)) (inv_mem hc),
        centralizerImageElt_mul (mul_mem hκC hc) (inv_mem hκC), centralizerImageElt_mul hκC hc,
        centralizerImageElt_inv hκC, centralizerImageElt_inv hc]
    have hqH : centralizerImageElt (Ω := Ω) hqC ∈
        jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) := by
      rw [hqΦ]
      exact mul_mem (mul_mem (mul_mem hκH hcH) (inv_mem hκH)) (inv_mem hcH)
    have hρq : C.Dv.ρ k ⟨_, hqH⟩ = p * r * p⁻¹ * r⁻¹ := by
      rw [← hcρ, hp, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hqΦ)
    have hmem : p * r * p⁻¹ * r⁻¹ ∈ seRadical (C.Dv.M k) (C.Dv.coord C.a k) :=
      mul_mem (conj_mem_seRadical hpN hpa hr) (inv_mem hr)
    obtain ⟨j, hj⟩ := (hM.isPGroup_seRadical (C.Dv.coord C.a k)) ⟨_, hmem⟩
    have hj' : (p * r * p⁻¹ * r⁻¹) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have h1 := eq_one_of_pow_two_pow_of_pow_odd hj' hqodd
      (by rw [← hρq]; exact C.rho_pow_orderOf hqC hqH k)
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hpZ := hM.mem_rootCenter_seRadical_of_commute hpN hcomm
  obtain ⟨j, hj⟩ := (hM.isPGroup_seRadical (C.Dv.coord C.a k))
    ⟨p, CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hpZ⟩
  have hj' : p ^ 2 ^ j = 1 := congrArg Subtype.val hj
  exact eq_one_of_pow_two_pow_of_pow_odd hj' hodd (C.rho_pow_orderOf hκC hκH k)

theorem exists_normalizer_Z_rho (hS : Sec4Setting G Ω) {k : C.Dv.ι} (hk : k ≠ C.i)
    {d : Equiv.Perm (C.Dv.Ψc k)} (hdM : d ∈ C.Dv.M k)
    (hda : d (C.Dv.coord C.a k) = C.Dv.coord C.a k) :
    ∃ n, ∃ hn : n ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G),
      ∃ hnH : centralizerImageElt (Ω := Ω) hn ∈
        jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)),
        (∀ z ∈ C.Z, n * z * n⁻¹ ∈ C.Z) ∧ C.Dv.ρ k ⟨_, hnH⟩ = d := by
  obtain ⟨l, hlL, hld⟩ := C.Dv.mem_M.mp hdM
  obtain ⟨c, hc, hcl, hcst, hcB⟩ := C.exists_lift_coord hS hk hlL (by rw [hld]; exact hda)
  have hcH : centralizerImageElt (Ω := Ω) hc ∈
      jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) := hcl ▸ l.2
  obtain ⟨κ, hκ, hψκ, hN⟩ := C.exists_normalizer_Z hS (mem_hvPre.mpr ⟨hc, hcH⟩) hcst hcB
  obtain ⟨hκC, hκH⟩ := mem_hvPre.mp (C.mem_Qt.mp hκ).1
  have hnC := mul_mem (inv_mem hκC) hc
  have hnΦ : centralizerImageElt (Ω := Ω) hnC =
      (centralizerImageElt (Ω := Ω) hκC)⁻¹ * centralizerImageElt (Ω := Ω) hc := by
    rw [centralizerImageElt_mul (inv_mem hκC) hc, centralizerImageElt_inv hκC]
  have hnH : centralizerImageElt (Ω := Ω) hnC ∈
      jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) := by
    rw [hnΦ]
    exact mul_mem (inv_mem hκH) hcH
  refine ⟨κ⁻¹ * c, hnC, hnH, hN, ?_⟩
  have h1 : (⟨_, hnH⟩ : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) =
      (⟨_, hκH⟩ : jHull _ _)⁻¹ * ⟨_, hcH⟩ := Subtype.ext hnΦ
  rw [h1, map_mul, map_inv, C.rho_eq_one_of_mem_Qt hS hκ hψκ hk hκC hκH, inv_one, one_mul,
    ← hld]
  exact congrArg _ (Subtype.ext hcl)

noncomputable def zRho (hS : Sec4Setting G Ω) (k : C.Dv.ι) : C.Z →* Equiv.Perm (C.Dv.Ψc k) where
  toFun z := C.Dv.ρ k (C.zH hS z.2)
  map_one' := by
    rw [show C.zH hS (1 : C.Z).2 = 1 from Subtype.ext (Subtype.ext (by ext ω; simp)), map_one]
  map_mul' z₁ z₂ := by
    rw [← map_mul]
    exact congrArg _ (Subtype.ext (centralizerImageElt_mul _ _))

theorem rho_zH_eq_one (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) (k : C.Dv.ι) :
    C.Dv.ρ k (C.zH hS hz) = 1 := by
  rcases eq_or_ne k C.i with rfl | hk
  · exact C.rho_zH_i hS hz
  have hM := C.isNaturalSE_Dv k
  have hWle : (C.zRho hS k).range ≤ rootCenter (seRadical (C.Dv.M k) (C.Dv.coord C.a k)) := by
    rintro _ ⟨z', rfl⟩
    exact C.rho_zH_mem hS z'.2 hk
  have : Nontrivial (C.Dv.Ψc k) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by have := C.Dv.five_le_card k; omega)
  obtain ⟨c', hc'⟩ := exists_ne (C.Dv.coord C.a k)
  have hinv : ∀ d ∈ C.Dv.M k, d (C.Dv.coord C.a k) = C.Dv.coord C.a k → d c' = c' →
      ∀ w ∈ (C.zRho hS k).range, d * w * d⁻¹ ∈ (C.zRho hS k).range := by
    rintro d hdM hda - _ ⟨z', rfl⟩
    obtain ⟨n, hn, hnH, hnZ, hnd⟩ := C.exists_normalizer_Z_rho hS hk hdM hda
    refine ⟨⟨n * z' * n⁻¹, hnZ z' z'.2⟩, ?_⟩
    have hz'C := C.mem_centralizer_of_mem_Z hS z'.2
    have e : C.zH hS (hnZ z' z'.2) = ⟨_, hnH⟩ * C.zH hS z'.2 * (⟨_, hnH⟩ : jHull _ _)⁻¹ :=
      Subtype.ext (by
        change centralizerImageElt (Ω := Ω) (mul_mem (mul_mem hn hz'C) (inv_mem hn)) = _
        rw [centralizerImageElt_mul (mul_mem hn hz'C) (inv_mem hn),
          centralizerImageElt_mul hn hz'C, centralizerImageElt_inv hn]
        rfl)
    change C.Dv.ρ k (C.zH hS (hnZ z' z'.2)) = d * C.Dv.ρ k (C.zH hS z'.2) * d⁻¹
    rw [e, map_mul, map_mul, map_inv, hnd]
  rcases hM.eq_bot_or_eq_rootCenter hc'.symm hWle hinv with hW | hW
  · have h : C.zRho hS k ⟨z, hz⟩ ∈ (C.zRho hS k).range := ⟨⟨z, hz⟩, rfl⟩
    rw [hW, Subgroup.mem_bot] at h
    exact h
  · obtain ⟨z', hz'⟩ : C.Dv.ρ k (C.xH hS) ∈ (C.zRho hS k).range := by
      rw [hW]
      exact (C.rho_mem_rootCenter_of_mem_longInv (C.x_phi_mem_longInv hS)
        (C.x_phi_smul_a hS) hk).1
    exact absurd hz' (C.rho_zH_ne_rho_xH hS z'.2 hk)

theorem smul_eq_of_mem_Z_of_mem_fixSet (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z)
    {ω : Ω} (hω : ω ∈ fixSet Ω (Subgroup.zpowers v)) : z • ω = ω := by
  have hK : ((C.zH hS hz : jHull _ _) : typeLSection G Ω v) ∈
      jOrbitKernel (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    (C.Dv.mem_jOrbitKernel_iff_rho (h := C.zH hS hz)).mpr fun k => C.rho_zH_eq_one hS hz k
  rw [jOrbitKernel_eq_bot C.jOddCore_Dv_eq_bot, Subgroup.mem_bot] at hK
  exact congrArg (fun π : typeLSection G Ω v =>
    (((π : Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) ⟨ω, hω⟩ : fixSet Ω _) : Ω)) hK

theorem Z_le_fixingSubgroup (hS : Sec4Setting G Ω) :
    C.Z ≤ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := fun _ hz =>
  (mem_fixingSubgroup_iff G).mpr fun _ hω => C.smul_eq_of_mem_Z_of_mem_fixSet hS hz hω

theorem fixSet_eq_of_mem_Z (hS : Sec4Setting G Ω) {z : G} (hz : z ∈ C.Z) (hz1 : z ≠ 1) :
    fixSet Ω (Subgroup.zpowers z) = fixSet Ω (Subgroup.zpowers v) := by
  obtain ⟨h, -, -, rfl⟩ := C.exists_conj_eq_of_mem_Z hS (C.v_mem_Z hS) C.v_ne_one hz hz1
  rw [fixSet_zpowers, fixSet_zpowers, ← smul_fixedBy]
  symm
  refine Set.eq_of_subset_of_ncard_le (fun ω hω => ?_) ?_ (Set.toFinite _)
  · rw [← fixSet_zpowers] at hω
    rw [smul_fixedBy, mem_fixedBy]
    have := C.smul_eq_of_mem_Z_of_mem_fixSet hS hz hω
    exact this
  · rw [Set.ncard_smul_set]

end Qt

section F3

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_mem_rootCenter_ne {Δ : Type} [Finite Δ] {L : Subgroup (Equiv.Perm Δ)}
    (hL : IsNaturalSE L) (b : Δ) (x : Equiv.Perm Δ) :
    ∃ m ∈ rootCenter (seRadical L b), m ≠ 1 ∧ m ≠ x := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  by_contra! h
  have hsub : ((rootCenter (seRadical L b) : Subgroup (Equiv.Perm Δ)) : Set (Equiv.Perm Δ)) ⊆
      {1, x} := fun m hm => by
    by_cases hm1 : m = 1
    · exact Or.inl hm1
    · exact Or.inr (h m hm hm1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_insert_le (1 : Equiv.Perm Δ) {x}
  rw [Set.ncard_singleton] at h2
  have h3 := hA.card_rootCenter_seRadical b
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq] at h3
  have := hA.four_le_q
  omega

theorem eq_i (hS : Sec4Setting G Ω) (k : C.Dv.ι) : k = C.i := by
  by_contra hk
  have hM := C.isNaturalSE_Dv k
  have hV := C.isPGroup_zpowers
  have h3Φ := three_le_card_fixSet_of_isTypeL hS.star C.isTypeL
  have hxJ := C.x_phi_mem_longInv hS
  obtain ⟨hxk, hxk1⟩ := C.rho_mem_rootCenter_of_mem_longInv hxJ (C.x_phi_smul_a hS) hk
  set xk := C.Dv.ρ k (C.xH hS) with hxk_def
  obtain ⟨m, hmZ, hm1, hmx⟩ := exists_mem_rootCenter_ne hM (C.Dv.coord C.a k) xk
  have hm2 := hM.mul_self_eq_one_of_mem_rootCenter hmZ
  have hxk2 := hM.mul_self_eq_one_of_mem_rootCenter hxk
  have hxkM : xk ∈ C.Dv.M k := seRadical_le (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hxk)
  have hmM : m ∈ C.Dv.M k := seRadical_le (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hmZ)
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp (hM.isConj (x := ⟨xk, hxkM⟩) (y := ⟨m, hmM⟩)
    (by rw [Subgroup.orderOf_mk]; exact orderOf_eq_prime (by rw [sq]; exact hxk2) hxk1)
    (by rw [Subgroup.orderOf_mk]; exact orderOf_eq_prime (by rw [sq]; exact hm2) hm1))
  obtain ⟨l, hlL, hlg⟩ := C.Dv.mem_M.mp g₀.2
  set y' : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) := l * C.xH hS * l⁻¹
  have hy'J : (y' : typeLSection G Ω v) ∈ longInv (typeLSection G Ω v)
      (fixSet Ω (Subgroup.zpowers v)) := conj_mem_longInv hxJ _
  have hy'k : C.Dv.ρ k y' = m := by
    simp only [y', map_mul, map_inv]
    rw [hlg]
    exact congrArg Subtype.val hg₀
  have hy'j : ∀ j, j ≠ k → C.Dv.ρ j y' = C.Dv.ρ j (C.xH hS) := fun j hj => by
    simp only [y', map_mul, map_inv]
    rw [C.Dv.rho_eq_one_of_mem_L (Ne.symm hj) hlL, one_mul, inv_one, mul_one]
  have hy'B : ∀ ω : fixSet Ω (Subgroup.zpowers v),
      (∀ j, j ≠ C.i → C.Dv.coord ω j = C.Dv.coord C.a j) →
        (y' : typeLSection G Ω v) • ω = (C.xH hS : typeLSection G Ω v) • ω := fun ω hω =>
    C.coord_Dv_injective (funext fun j => by
      rw [C.Dv.coord_smul y', C.Dv.coord_smul (C.xH hS)]
      rcases eq_or_ne j k with rfl | hjk
      · rw [hy'k, hω j hk, apply_eq_of_mem_seRadical
          (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hmZ)]
        exact (apply_eq_of_mem_seRadical (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hxk)).symm
      · rw [hy'j j hjk])
  obtain ⟨c, hcJ, hcC, hcy⟩ :=
    (hS.mem_longInv_centralizerImage_iff hV h3Φ (y' : typeLSection G Ω v)).mp hy'J
  have hca : c • α = β := by
    rw [← hcy C.a]
    exact congrArg Subtype.val ((hy'B C.a fun _ _ => rfl).trans (C.x_phi_smul_a hS))
  set γ' : fixSet Ω (Subgroup.zpowers v) := ⟨C.γ, C.γ_mem⟩
  have hxγ' : (C.xH hS : typeLSection G Ω v) • γ' = γ' := Subtype.ext (C.x_smul hS).2.2
  have hcγ : c • (C.γ : Ω) = C.γ := by
    rw [← hcy γ']
    exact congrArg Subtype.val ((hy'B γ' (C.coord_of_mem_B hS C.γ.2 C.γ_mem).1).trans hxγ')
  have hZ2 : IsPGroup 2 C.Z := C.sylow.2.1.to_le (C.Z_le_Y.trans C.Y_le_S)
  obtain ⟨j, hjJ, hjZ, hjc⟩ := hS.frattini h3Φ hZ2 (C.Z_le_fixingSubgroup hS) hcJ
    (centralizer_le_stabilizer_fixSet _ hcC)
  have hjC : j ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    mem_centralizer_zpowers (Subgroup.mem_centralizer_iff.mp hjZ v (C.v_mem_Z hS))
  have hjα : j • α = β := (hjc α C.isTypeL.mem_fixSet).trans hca
  have hjγ : j • (C.γ : Ω) = C.γ := (hjc _ C.γ_mem).trans hcγ
  have hjS : j ∈ longInvSwap G Ω α β := ⟨hjJ, hjα⟩
  have hjp := closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hjS)
  have hjZh : C.psi ⟨j, hjp⟩ ∈ C.Zhat := by
    refine C.isNaturalSE_N.mem_rootCenter_seRadical (C.psi_mem_N hS (Subgroup.subset_closure hjS))
      (C.psi_apply_bγ hjγ) ?_
    rw [← C.psi_mul hjp hjp, show (⟨j * j, _⟩ : stabilizer G ({α, β} : Set Ω)) = 1 from
      Subtype.ext (mul_self_eq_one_of_mem_longInv hjJ), map_one]
  obtain ⟨zj, hzj, hzjψ⟩ := C.exists_mem_Z_of_mem_Zhat hS hjZh
  have hzjp := C.X_le_stabilizer_pair (C.Y_le_X (C.Z_le_Y hzj))
  have hzjst := (Subgroup.mem_inf.mp (C.X_le (C.Y_le_X (C.Z_le_Y hzj)))).1
  obtain ⟨hxα, hxβ, -⟩ := C.x_smul hS
  have hjβ : j • β = α := smul_eq_of_orderOf_eq_two hjJ.1 hjα
  have hgst : C.x * (j * zj) ∈ stabilizer G α ⊓ stabilizer G β := by
    refine Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr ?_, mem_stabilizer_iff.mpr ?_⟩
    · rw [mul_smul, mul_smul, mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hzjst).1, hjα, hxβ]
    · rw [mul_smul, mul_smul, mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hzjst).2, hjβ, hxα]
  have hψg : C.psi ⟨C.x * (j * zj), stabilizer_inf_le_stabilizer_pair α β hgst⟩ = 1 := by
    rw [C.psi_mul (C.x_mem_stabilizer_pair hS) (mul_mem hjp hzjp), C.psi_x hS, one_mul,
      C.psi_mul hjp hzjp, hzjψ, ← C.psi_mul hjp hjp, show (⟨j * j, _⟩ :
        stabilizer G ({α, β} : Set Ω)) = 1 from
      Subtype.ext (mul_self_eq_one_of_mem_longInv hjJ), map_one]
  have hgB : ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω (Subgroup.zpowers v) →
      (C.x * (j * zj)) • δ = δ := fun δ hδ hδ' => by
    have h1 : j • δ = C.x • δ := by
      rw [hjc δ hδ', ← hcy ⟨δ, hδ'⟩]
      exact congrArg Subtype.val (hy'B ⟨δ, hδ'⟩ (C.coord_of_mem_B hS hδ hδ').1)
    rw [mul_smul, mul_smul, C.smul_eq_of_mem_Z hS hzj hδ hδ', h1, ← mul_smul, C.x_mul_self hS,
      one_smul]
  have hgodd := C.odd_orderOf_of_psi_eq_one hS hgst hψg hgB
  have hgC := mul_mem (C.x_mem_centralizer hS) (mul_mem hjC (C.mem_centralizer_of_mem_Z hS hzj))
  have hgΦ : centralizerImageElt (Ω := Ω) hgC =
      ((C.xH hS : typeLSection G Ω v)) * (y' : typeLSection G Ω v) := by
    refine Subtype.ext (Equiv.ext fun ω => Subtype.ext ?_)
    show (C.x * (j * zj)) • (ω : Ω) = C.x • ((((y' : typeLSection G Ω v) :
      Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) ω : fixSet Ω _) : Ω)
    rw [mul_smul, mul_smul, C.smul_eq_of_mem_Z_of_mem_fixSet hS hzj ω.2, hjc _ ω.2, hcy ω]
  have hgH : centralizerImageElt (Ω := Ω) hgC ∈
      jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) := by
    rw [hgΦ]
    exact mul_mem (C.xH hS).2 y'.2
  have hρg : C.Dv.ρ k ⟨_, hgH⟩ = xk * m := by
    rw [← hy'k, ← map_mul]
    exact congrArg _ (Subtype.ext hgΦ)
  have hmem : xk * m ∈ rootCenter (seRadical (C.Dv.M k) (C.Dv.coord C.a k)) := mul_mem hxk hmZ
  obtain ⟨e, he⟩ := (hM.isPGroup_seRadical (C.Dv.coord C.a k))
    ⟨_, CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hmem⟩
  have he' : (xk * m) ^ 2 ^ e = 1 := congrArg Subtype.val he
  have h1 := eq_one_of_pow_two_pow_of_pow_odd he' hgodd
    (by rw [← hρg]; exact C.rho_pow_orderOf hgC hgH k)
  refine hmx ?_
  rw [← mul_left_cancel_iff (a := xk), hxk2, h1]

end F3

section F45

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

noncomputable def piM (hS : Sec4Setting G Ω) :
    Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) →*
      Equiv.Perm (C.Dv.Ψc C.i) :=
  (C.Dv.extRho (C.eq_i hS)).comp (MulAction.toPermHom (Subgroup.centralizer
    ((Subgroup.zpowers v : Subgroup G) : Set G)) (fixSet Ω (Subgroup.zpowers v))).rangeRestrict

theorem piM_coord (hS : Sec4Setting G Ω)
    (g : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (ω : fixSet Ω (Subgroup.zpowers v)) :
    C.piM hS g (C.Dv.coord ω C.i) = C.Dv.coord (centralizerImageElt (Ω := Ω) g.2 • ω) C.i :=
  C.Dv.extRho_coord (C.eq_i hS) _ ω

theorem piM_mem_normalizer (hS : Sec4Setting G Ω)
    (g : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    C.piM hS g ∈ Subgroup.normalizer (C.Dv.M C.i : Set (Equiv.Perm (C.Dv.Ψc C.i))) :=
  C.Dv.extRho_mem_normalizer (C.eq_i hS) _

theorem piM_eq_one_iff (hS : Sec4Setting G Ω)
    (g : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    C.piM hS g = 1 ↔ ∀ ω ∈ fixSet Ω (Subgroup.zpowers v), (g : G) • ω = ω := by
  constructor
  · intro h ω hω
    have h1 : C.Dv.coord (centralizerImageElt (Ω := Ω) g.2 • (⟨ω, hω⟩ : fixSet Ω _)) =
        C.Dv.coord ⟨ω, hω⟩ := funext fun j => by
      rcases C.eq_i hS j with rfl
      rw [← C.piM_coord hS, h, Equiv.Perm.one_apply]
    exact congrArg Subtype.val (C.coord_Dv_injective h1)
  · intro h
    ext c
    obtain ⟨ω, rfl⟩ := C.Dv.exists_coord_apply_eq C.i c
    rw [C.piM_coord, Equiv.Perm.one_apply]
    exact congrArg (fun p => C.Dv.coord p C.i) (Subtype.ext (h ω ω.2))

theorem isCyclic_map_piM (hS : Sec4Setting G Ω) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPst : P ≤ stabilizer G α ⊓ stabilizer G β) :
    IsCyclic ((P.subgroupOf (Subgroup.centralizer
      ((Subgroup.zpowers v : Subgroup G) : Set G))).map (C.piM hS)) := by
  have hfix : ∀ (g : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)),
      (g : G) ∈ P → ∀ ω : fixSet Ω (Subgroup.zpowers v), (g : G) • (ω : Ω) = ω →
        C.piM hS g (C.Dv.coord ω C.i) = C.Dv.coord ω C.i := fun g _ ω hω => by
    rw [C.piM_coord]
    exact congrArg (fun p => C.Dv.coord p C.i) (Subtype.ext hω)
  refine (C.isNaturalSE_Dv C.i).isCyclic_of_isPGroup C.coord_ne
    ((hP.comap_of_injective _ (Subgroup.subtype_injective _) |>.to_le le_rfl).map _ |> fun h =>
      h.to_le le_rfl) ?_ ?_ ?_
  · rintro _ ⟨g, -, rfl⟩
    exact C.piM_mem_normalizer hS g
  · rintro _ ⟨g, hg, rfl⟩
    exact hfix g hg C.a (Subgroup.mem_inf.mp (hPst hg)).1
  · rintro _ ⟨g, hg, rfl⟩
    exact hfix g hg C.b (Subgroup.mem_inf.mp (hPst hg)).2

theorem smul_fixSet_eq_of_normalizes_Z (hS : Sec4Setting G Ω) {h : G}
    (hh : ∀ z ∈ C.Z, h * z * h⁻¹ ∈ C.Z) :
    h • fixSet Ω (Subgroup.zpowers v) = fixSet Ω (Subgroup.zpowers v) := by
  have hv := C.v_mem_Z hS
  have hhv1 : h * v * h⁻¹ ≠ 1 := fun h1 => C.v_ne_one (by
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact h1)
  have h1 := C.fixSet_eq_of_mem_Z hS (hh v hv) hhv1
  rw [fixSet_zpowers, ← smul_fixedBy, ← fixSet_zpowers] at h1
  exact h1

theorem card_Y (hS : Sec4Setting G Ω) : Nat.card C.Y = Nat.card C.Rhat :=
  Nat.card_eq_of_bijective (fun y : C.Y => (⟨C.psi ⟨y, C.X_le_stabilizer_pair (C.Y_le_X y.2)⟩,
    C.psi_mem_Rhat_of_mem_X (C.Y_le_X y.2)⟩ : C.Rhat))
    ⟨fun y₁ y₂ h => Subtype.ext (C.eq_of_psi_eq hS y₁.2 y₂.2 (congrArg Subtype.val h)),
      fun r => by
        obtain ⟨y, hy, hyr⟩ := C.exists_mem_Y_of_mem_Rhat hS r.2
        exact ⟨⟨y, hy⟩, Subtype.ext hyr⟩⟩

theorem card_Z (hS : Sec4Setting G Ω) : Nat.card C.Z = Nat.card C.Zhat :=
  Nat.card_eq_of_bijective (fun z : C.Z => (⟨C.psi ⟨z, C.X_le_stabilizer_pair
    (C.Y_le_X (C.Z_le_Y z.2))⟩, C.psi_mem_Zhat_of_mem_Z z.2⟩ : C.Zhat))
    ⟨fun z₁ z₂ h => Subtype.ext (C.eq_of_psi_eq hS (C.Z_le_Y z₁.2) (C.Z_le_Y z₂.2)
      (congrArg Subtype.val h)),
      fun r => by
        obtain ⟨z, hz, hzr⟩ := C.exists_mem_Z_of_mem_Zhat hS r.2
        exact ⟨⟨z, hz⟩, Subtype.ext hzr⟩⟩

theorem Y_le_centralizer (hS : Sec4Setting G Ω) :
    C.Y ≤ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := fun _ hy =>
  mem_centralizer_zpowers (C.commute_of_mem_Z hS (C.v_mem_Z hS) hy)

theorem Y_le_fixingSubgroup (hS : Sec4Setting G Ω) :
    C.Y ≤ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := by
  classical
  have hN := C.isNaturalSE_N
  obtain ⟨n, ii, e, hA⟩ := hN.exists_isBenderAction
  set W : Subgroup G := C.Y ⊓ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) with hWdef
  set WΨ : Subgroup (Equiv.Perm C.Psi) :=
    (W.subgroupOf (stabilizer G ({α, β} : Set Ω))).map C.psi with hWΨ
  have hZW : C.Zhat ≤ WΨ := fun r hr => by
    obtain ⟨z, hz, hzr⟩ := C.exists_mem_Z_of_mem_Zhat hS hr
    exact ⟨⟨z, _⟩, Subgroup.mem_subgroupOf.mpr ⟨C.Z_le_Y hz, C.Z_le_fixingSubgroup hS hz⟩, hzr⟩
  have hWR : WΨ ≤ C.Rhat := by
    rintro _ ⟨⟨g, hgp⟩, hgW, rfl⟩
    exact C.psi_mem_Rhat_of_mem_X (C.Y_le_X (Subgroup.mem_subgroupOf.mp hgW).1)
  have : Nontrivial (C.D.Ψc C.i₀) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by have := C.D.five_le_card C.i₀; omega)
  obtain ⟨c, hc⟩ := exists_ne C.bγ
  have hinv : ∀ d ∈ C.N, d C.bγ = C.bγ → d c = c → ∀ w ∈ WΨ, d * w * d⁻¹ ∈ WΨ := by
    rintro d hdN hdb - _ ⟨⟨g, hgp⟩, hgW, rfl⟩
    obtain ⟨hgY, hgF⟩ := Subgroup.mem_subgroupOf.mp hgW
    obtain ⟨h, hJ, hst, hY, hψ⟩ := C.exists_lift_normalizer hS hdN hdb
    have hhp := closure_longInvSwap_le_stabilizer_pair α β hJ
    have hZ : ∀ z ∈ C.Z, h * z * h⁻¹ ∈ C.Z := fun z hz => by
      have hzp := C.X_le_stabilizer_pair (C.Y_le_X (C.Z_le_Y hz))
      refine C.mem_Z.mpr ⟨hY z (C.Z_le_Y hz), ?_⟩
      rw [C.psi_mul (mul_mem hhp hzp) (inv_mem hhp), C.psi_mul hhp hzp, C.psi_inv hhp, hψ]
      exact conj_mem_rootCenter_seRadical (hψ ▸ C.psi_mem_normalizer ⟨h, hhp⟩) hdb
        (C.psi_mem_Zhat_of_mem_Z hz)
    have hΦ := C.smul_fixSet_eq_of_normalizes_Z hS hZ
    refine ⟨⟨h * g * h⁻¹, mul_mem (mul_mem hhp hgp) (inv_mem hhp)⟩,
      Subgroup.mem_subgroupOf.mpr ⟨hY g hgY, (mem_fixingSubgroup_iff G).mpr fun ω hω => ?_⟩, ?_⟩
    · have hω' : h⁻¹ • ω ∈ fixSet Ω (Subgroup.zpowers v) := by
        rw [← hΦ] at hω
        obtain ⟨ω', hω', rfl⟩ := hω
        rwa [inv_smul_smul]
      rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp hgF _ hω', smul_inv_smul]
    · change C.psi (⟨h, hhp⟩ * ⟨g, hgp⟩ * ⟨h, hhp⟩⁻¹) = d * C.psi ⟨g, hgp⟩ * d⁻¹
      rw [map_mul, map_mul, map_inv, hψ]
  have hYW : ∀ y (hy : y ∈ C.Y), C.psi ⟨y, C.X_le_stabilizer_pair (C.Y_le_X hy)⟩ ∈ WΨ →
      y ∈ W := by
    intro y hy hyW
    obtain ⟨⟨g, hgp⟩, hgW, hgy⟩ := hyW
    obtain ⟨hgY, hgF⟩ := Subgroup.mem_subgroupOf.mp hgW
    rw [← C.eq_of_psi_eq hS hgY hy hgy]
    exact ⟨hgY, hgF⟩
  rcases hN.eq_rootCenter_or_eq_seRadical hc.symm hZW hWR hinv with hW | hW
  ·
    have hRZ : C.Rhat = C.Zhat := by
      by_contra hne
      have hii : ii ≠ 1 := fun h1 => hne (hA.rootCenter_seRadical_eq_self h1 C.bγ).symm
      have hpar := hA.params
      have h4 := hA.four_le_q
      have hYC := C.Y_le_centralizer hS
      set Y' := C.Y.subgroupOf (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
      set f := (C.piM hS).comp Y'.subtype
      have hcY' : Nat.card Y' = Nat.card C.Y :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYC).toEquiv
      have hker : Nat.card f.ker ≤ Nat.card C.Z := by
        refine Nat.card_le_card_of_injective (fun y => (⟨((y : Y') : G), ?_⟩ : C.Z)) ?_
        · obtain ⟨⟨⟨g, hgC⟩, hgY⟩, hy⟩ := y
          have hg1 : C.piM hS ⟨g, hgC⟩ = 1 := hy
          have hgW : g ∈ W := ⟨hgY, (mem_fixingSubgroup_iff G).mpr fun ω hω =>
            (C.piM_eq_one_iff hS ⟨g, hgC⟩).mp hg1 ω hω⟩
          have hψ : C.psi ⟨g, C.X_le_stabilizer_pair (C.Y_le_X hgY)⟩ ∈ C.Zhat := by
            have h1 : C.psi ⟨g, C.X_le_stabilizer_pair (C.Y_le_X hgY)⟩ ∈ WΨ :=
              ⟨⟨g, _⟩, Subgroup.mem_subgroupOf.mpr hgW, rfl⟩
            rw [hW] at h1
            exact h1
          exact C.mem_Z.mpr ⟨hgY, hψ⟩
        · intro y₁ y₂ h
          have h' := congrArg Subtype.val h
          simp only at h'
          exact Subtype.ext (Subtype.ext (Subtype.ext h'))
      have hrange : Nat.card f.range ≤ 2 := by
        have hcyc : IsCyclic f.range := by
          rw [MonoidHom.range_comp, Subgroup.range_subtype]
          exact C.isCyclic_map_piM hS (C.sylow.2.1.to_le C.Y_le_S)
            (C.Y_le_X.trans C.X_le_stabilizer_inf)
        have hsq : ∀ r : f.range, r ^ 2 = 1 := by
          rintro ⟨_, ⟨⟨⟨g, hgC⟩, hgY⟩, rfl⟩⟩
          refine Subtype.ext ?_
          change (C.piM hS ⟨g, hgC⟩) ^ 2 = 1
          rw [← map_pow]
          refine (C.piM_eq_one_iff hS _).mpr fun ω hω => ?_
          have hg2 : g ^ 2 ∈ C.Z := by
            have hgY' : g ∈ C.Y := hgY
            refine C.mem_Z.mpr ⟨pow_mem hgY' 2, ?_⟩
            rw [show (⟨g ^ 2, _⟩ : stabilizer G ({α, β} : Set Ω)) =
              ⟨g, C.X_le_stabilizer_pair (C.Y_le_X hgY')⟩ ^ 2 from rfl, map_pow, sq]
            exact hN.mul_self_mem_rootCenter_seRadical (C.psi_mem_Rhat_of_mem_X (C.Y_le_X hgY'))
          exact C.smul_eq_of_mem_Z_of_mem_fixSet hS hg2 hω
        have : Fintype f.range := Fintype.ofFinite _
        have h1 := IsCyclic.card_pow_eq_one_le (α := f.range) (n := 2) two_pos
        rw [show ({a | a ^ 2 = 1} : Finset f.range) = Finset.univ from
          Finset.eq_univ_of_forall fun a => by simp [hsq a], Finset.card_univ] at h1
        rwa [Nat.card_eq_fintype_card]
      have hcard := Subgroup.card_mul_index f.ker
      rw [Subgroup.index_ker, hcY', C.card_Y hS, hA.card_seRadical] at hcard
      have hZc : Nat.card C.Z = 2 ^ n := by rw [C.card_Z hS, hA.card_rootCenter_seRadical]
      have h5 : (2 ^ n) ^ ii ≤ 2 ^ n * 2 := by
        rw [← hcard, ← hZc]
        exact Nat.mul_le_mul hker hrange
      have h6 : (2 ^ n) ^ 2 ≤ (2 ^ n) ^ ii := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
    intro y hy
    have hψ := C.psi_mem_Rhat_of_mem_X (C.Y_le_X hy)
    rw [hRZ] at hψ
    exact C.Z_le_fixingSubgroup hS (C.mem_Z.mpr ⟨hy, hψ⟩)
  · intro y hy
    exact (hYW y hy (hW ▸ C.psi_mem_Rhat_of_mem_X (C.Y_le_X hy))).2

end F45

end FinConfig

end CFSG.Holt.H78
