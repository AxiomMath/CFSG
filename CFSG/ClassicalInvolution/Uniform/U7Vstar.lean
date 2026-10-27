module

public import CFSG.ClassicalInvolution.AschTight.S1916F1
public import CFSG.ClassicalInvolution.Uniform.U7Inv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement MatrixGroups


section Aut

variable {G : Type} [Group G]

@[expose] def conjAutOfNormalizer (M : Subgroup G) {c : G}
    (hc : c ∈ Subgroup.normalizer (M : Set G)) : MulAut M where
  toFun x := ⟨c * x * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc x).mp x.2⟩
  invFun x := ⟨c⁻¹ * x * c, (Subgroup.mem_normalizer_iff.mp hc (c⁻¹ * x * c)).mpr (by
    have : c * (c⁻¹ * (x : G) * c) * c⁻¹ = x := by group
    rw [this]
    exact x.2)⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjAutOfNormalizer_apply (M : Subgroup G) {c : G}
    (hc : c ∈ Subgroup.normalizer (M : Set G)) (x : M) :
    ((conjAutOfNormalizer M hc x : M) : G) = c * x * c⁻¹ := rfl

theorem centralizes_of_centralizes_sylow {M Q : Subgroup G}
    (e : M ≃* SL(2, GaloisField 3 1)) (hQM : Q ≤ M) (hQ8 : Nat.card Q = 8) {c : G}
    (hcM : c ∈ Subgroup.normalizer (M : Set G)) (hcQ : ∀ q ∈ Q, c * q = q * c) :
    ∀ y ∈ M, c * y = y * c := by
  have hM24 : Nat.card M = 24 := (Nat.card_congr e.toEquiv).trans natCard_sl2_galoisField_three
  have hfin : Finite M := Nat.finite_of_card_ne_zero (by rw [hM24]; norm_num)
  have hQ'8 : Nat.card (Q.subgroupOf M) = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv).trans hQ8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P₀ : Sylow 2 M := Sylow.ofCard (Q.subgroupOf M) (by
    rw [hQ'8, hM24, two_pow_factorization_24])
  let P : Sylow 2 SL(2, GaloisField 3 1) := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P₀
  let β : MulAut SL(2, GaloisField 3 1) :=
    (e.symm.trans (conjAutOfNormalizer M hcM)).trans e
  have hβ : β = 1 := by
    refine S1916.mulAut_eq_one_of_fixes_sylow_three P β ?_
    intro x hx
    have hx' : x ∈ Subgroup.map e.toMonoidHom (P₀ : Subgroup M) := by
      rw [← Sylow.coe_mapSurjective e.surjective P₀]
      exact hx
    obtain ⟨y, hy, rfl⟩ := hx'
    have hyQ : (y : G) ∈ Q := Subgroup.mem_subgroupOf.mp hy
    change e ((conjAutOfNormalizer M hcM) (e.symm (e y))) = e y
    rw [MulEquiv.symm_apply_apply]
    congr 1
    refine Subtype.ext ?_
    rw [conjAutOfNormalizer_apply]
    have := hcQ _ hyQ
    calc c * (y : G) * c⁻¹ = (y : G) * c * c⁻¹ := by rw [this]
      _ = y := by group
  intro y hy
  have h1 : β (e ⟨y, hy⟩) = e ⟨y, hy⟩ := by rw [hβ]; rfl
  change e ((conjAutOfNormalizer M hcM) (e.symm (e ⟨y, hy⟩))) = e ⟨y, hy⟩ at h1
  rw [MulEquiv.symm_apply_apply] at h1
  have h2 := congrArg Subtype.val (e.injective h1)
  rw [conjAutOfNormalizer_apply] at h2
  calc c * y = c * y * c⁻¹ * c := by group
    _ = y * c := by rw [h2]

end Aut

section Twin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def G2CentralizerInvolution3 : Prop :=
  ∀ R ∈ G2Fund, ∀ c : G2Model, IsUniqueInvolution R c → ∀ x : G2Model, x * x = 1 →
    (∀ r ∈ R, x * r = r * x) → x = 1 ∨ x = c

theorem twin_of_mem_omegaNbr_g2 (hF : G2CentralizerInvolution3) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hex : ExactMembers Ω) (C : G2Comp Ω) {K M : Subgroup G} (hK : K ∈ C.members)
    (hM : M ∈ C.members) (hMK : M ∈ omegaNbr Ω K) : M ∈ twinSet Ω K := by
  obtain ⟨Q, hQM, hQ8, hQN⟩ := exists_sylow_of_omegaNbr hΩ hex hMK
  obtain ⟨hKΩ, RK, hRK, rfl⟩ := hK
  obtain ⟨hMΩ, RM, hRM, rfl⟩ := hM
  obtain ⟨zK, hzK0⟩ := hΩ.classical _ hKΩ
  obtain ⟨zM, hzM0⟩ := hΩ.classical _ hMΩ
  have hzK := hzK0.isUniqueInvolution_sl2
  have hzM := hzM0.isUniqueInvolution_sl2
  have hQc : ∀ q ∈ Q, zK * q = q * zK := by
    intro q hq
    have h := conj_eq_of_mem_normalizer hzK (hQN hq)
    calc zK * q = q * zK * q⁻¹ * q := by rw [h]
      _ = q * zK := by group
  have h2Q : 2 ∣ Nat.card Q := by rw [hQ8]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 h2Q
  have hx2 : (x : G) * (x : G) = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx, pow_two] at h
    exact congrArg (fun y : Q => (y : G)) h
  have hx1 : (x : G) ≠ 1 := by
    intro h
    have h' : x = 1 := Subtype.ext h
    rw [h', orderOf_one] at hx
    omega
  have hxzM : (x : G) = zM := (hzM.unique _ (hQM x.2) hx2).resolve_left hx1
  have hzMQ : zM ∈ Q := hxzM ▸ x.2
  obtain ⟨cK, hcKz, hcK⟩ := isUniqueInvolution_of_map C.inj hzK
  obtain ⟨cM, hcMz, hcM⟩ := isUniqueInvolution_of_map C.inj hzM
  have hcKM : cK * cM = cM * cK := by
    apply C.inj
    rw [map_mul, map_mul, hcKz, hcMz]
    exact hQc _ hzMQ
  have hcKN : cK ∈ Subgroup.normalizer (RM : Set G2Model) :=
    g2_centralizer_le_normalizer hRM hcM (Subgroup.mem_centralizer_singleton_iff.mpr hcKM)
  have hzKN : zK ∈ Subgroup.normalizer ((RM.map C.ψ : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, ← hcKz, ← AscQuot.map_conjSub,
      mem_normalizer_iff_conjSub_eq.mp hcKN]
  obtain ⟨eM⟩ := hzM0.nonempty_equiv_sl2_of_exact (hex _ hMΩ)
  have hcenM : ∀ y ∈ RM.map C.ψ, zK * y = y * zK :=
    centralizes_of_centralizes_sylow eM hQM hQ8 hzKN hQc
  have hcKR : ∀ r ∈ RM, cK * r = r * cK := by
    intro r hr
    apply C.inj
    rw [map_mul, map_mul, hcKz]
    exact hcenM _ (Subgroup.mem_map_of_mem _ hr)
  rcases hF RM hRM cM hcM cK hcK.sq hcKR with h1 | h1
  · exact absurd h1 hcK.ne_one
  · have hzz : zK = zM := by rw [← hcKz, ← hcMz, h1]
    refine ⟨hMΩ, zK, hzK, ?_⟩
    rw [hzz]
    exact hzM

namespace G2Comp

variable (C : G2Comp Ω)

theorem mem_omegaOfSet_twinSet_iff (hF : G2CentralizerInvolution3)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hex : ExactMembers Ω) {J : Subgroup G}
    (hJ : J ∈ C.members) {M : Subgroup G} :
    M ∈ omegaOfSet Ω (twinSet Ω J) ↔ M ∈ Ω ∧ M ∉ C.members := by
  constructor
  · rintro ⟨hMΩ, hall⟩
    refine ⟨hMΩ, fun hMi => ?_⟩
    obtain ⟨z, hz0⟩ := hΩ.classical _ hJ.1
    have hz := hz0.isUniqueInvolution_sl2
    have hMJ : M ∈ omegaNbr Ω J := hall J ⟨hJ.1, z, hz, hz⟩
    have hMt : M ∈ twinSet Ω J := twin_of_mem_omegaNbr_g2 hF hΩ hex C hJ hMi hMJ
    exact (hall M hMt).2.1 rfl
  · rintro ⟨hMΩ, hMi⟩
    refine ⟨hMΩ, fun K' hK' => ?_⟩
    have hK'i := C.twin_mem_members hJ hK'
    exact mem_omegaNbr_of_commutes hMΩ (fun h => hMi (h ▸ hK'i))
      (C.commutes_of_not_mem hMΩ hMi hK'i)

theorem vStar_eq_members (hF : G2CentralizerInvolution3) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ C.members) :
    vStar Ω K = C.members := by
  ext J
  constructor
  · rintro ⟨hJΩ, heq⟩
    by_contra hJi
    have h1 : J ∈ omegaOfSet Ω (twinSet Ω K) :=
      (C.mem_omegaOfSet_twinSet_iff hF hΩ hex hK).mpr ⟨hJΩ, hJi⟩
    rw [heq] at h1
    obtain ⟨z, hz0⟩ := hΩ.classical _ hJΩ
    have hz := hz0.isUniqueInvolution_sl2
    exact (h1.2 J ⟨hJΩ, z, hz, hz⟩).2.1 rfl
  · intro hJ
    refine ⟨hJ.1, ?_⟩
    ext M
    rw [C.mem_omegaOfSet_twinSet_iff hF hΩ hex hK, C.mem_omegaOfSet_twinSet_iff hF hΩ hex hJ]

end G2Comp

end Twin

end CFSG.ClassicalInvolution.Uniform
