module

public import CFSG.GH74.GLS.Stage2.Signalizer.L53Reduce
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.MinimalNormalPSubgroupGLAction
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.MinimalNormalPCoreCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Subgroup Module
open scoped commutatorElement IsMulCommutative

variable {p : ℕ} [Fact p.Prime]

theorem conj_quad {R : Type*} [Ring R] {x y y' : R} (hy : y * y' = 1) (hy' : y' * y = 1)
    (h : (x - 1) * (x - 1) = 0) : (y * x * y' - 1) * (y * x * y' - 1) = 0 := by
  have e : y * x * y' - 1 = y * (x - 1) * y' := by
    rw [mul_sub, sub_mul, mul_one, hy]
  rw [e]
  calc y * (x - 1) * y' * (y * (x - 1) * y') = y * (x - 1) * (y' * y) * (x - 1) * y' := by
        noncomm_ring
    _ = 0 := by rw [hy', mul_one, mul_assoc y, h]; simp


theorem prop110_Q (hp2 : p ≠ 2) {Q : Type} [Group Q] [Finite Q]
    (H : Subgroup Q) [H.Normal] [IsMinimalNormal H] (hHne : H ≠ ⊥) (hHp : IsPGroup p ↥H)
    {g : Q} (hgp : IsPGroup p ↥(zpowers g))
    (hq : ∀ v ∈ H, ⁅g, ⁅g, v⁆⁆ = 1) (hn : ∃ v ∈ H, ⁅g, v⁆ ≠ 1) :
    ∃ m : Q, Sl2Quot p ↥(closure ({g, m * g * m⁻¹} : Set Q))
      ((centralizer (H : Set Q)).subgroupOf (closure ({g, m * g * m⁻¹} : Set Q))) := by
  classical
  let _ : IsElementaryAbelian p H :=
    CFSG.Glauberman.minimalNormal_pSubgroup_isElementaryAbelian H hHne hHp
  let _ : IsMulCommutative H := (inferInstance : IsElementaryAbelian p H).toIsMulCommutative
  let _ : Module (ZMod p) (Additive H) := IsElementaryAbelian.isVectorSpace p
  obtain ⟨ρ, hρinj, hρirr, hρeval⟩ :=
    CFSG.Glauberman.exists_minimalNormal_pSubgroup_GL_faithful_irreducible_action
      (p := p) H hHne hHp
  let ρ' : Q →* Module.End (ZMod p) (Additive H) :=
    (Units.coeHom (Module.End (ZMod p) (Additive H))).comp
      (ρ.comp (QuotientGroup.mk' (centralizer (H : Set Q))))
  have hev : ∀ (q : Q) (h : H), ρ' q (Additive.ofMul h) = Additive.ofMul (MulAut.conjNormal q h) := by
    intro q h
    apply Additive.toMul.injective
    exact hρeval q (Additive.ofMul h)
  let cm : Q → H → H := fun q h =>
    ⟨⁅q, (h : Q)⁆, by
      have e : ⁅q, (h : Q)⁆ = (q * (h : Q) * q⁻¹) * (h : Q)⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact H.mul_mem (Normal.conj_mem inferInstance _ h.2 q) (H.inv_mem h.2)⟩
  have hcm : ∀ (q : Q) (h : H), (ρ' q - 1) (Additive.ofMul h) = Additive.ofMul (cm q h) := by
    intro q h
    rw [LinearMap.sub_apply, hev, Module.End.one_apply, ← ofMul_div]
    congr 1
    apply Subtype.ext
    have h1 : ((MulAut.conjNormal q h : H) : Q) = q * (h : Q) * q⁻¹ := MulAut.conjNormal_apply q h
    show ((MulAut.conjNormal q h / h : H) : Q) = ⁅q, (h : Q)⁆
    rw [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, h1, commutatorElement_def]
  have hquad : ∀ q : Q, (∀ v ∈ H, ⁅q, ⁅q, v⁆⁆ = 1) → (ρ' q - 1) * (ρ' q - 1) = 0 := by
    intro q hq'
    ext v
    obtain ⟨h, rfl⟩ := Additive.ofMul.surjective v
    simp only [Module.End.mul_apply, LinearMap.zero_apply]
    rw [hcm, hcm]
    have : cm q (cm q h) = 1 := by
      apply Subtype.ext
      exact hq' (h : Q) h.2
    rw [this]; rfl
  have hγp : IsPGroup p ↥(zpowers (QuotientGroup.mk g : Q ⧸ centralizer (H : Set Q))) := by
    obtain ⟨k, hk⟩ := hgp ⟨g, mem_zpowers g⟩
    have hk' : g ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hγk : (QuotientGroup.mk g : Q ⧸ centralizer (H : Set Q)) ^ (p ^ k) = 1 := by
      rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
    have hdvd : orderOf (QuotientGroup.mk g : Q ⧸ centralizer (H : Set Q)) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one hγk
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
    rw [IsPGroup.iff_card]
    exact ⟨i, by rw [Nat.card_zpowers, hi]⟩
  have hBS : ∃ m' : Q ⧸ centralizer (H : Set Q), ¬ IsPGroup p ↥(closure
      ({(QuotientGroup.mk g : Q ⧸ centralizer (H : Set Q)),
        m' * QuotientGroup.mk g * m'⁻¹} : Set (Q ⧸ centralizer (H : Set Q)))) := by
    by_contra hcon
    push Not at hcon
    have h1 := CFSG.BaerSuzuki.baer_suzuki (p := p) _ hγp hcon
    have hbot :=
      CFSG.Glauberman.pCore_quotient_centralizer_eq_bot_of_minimalNormal_pSubgroup (p := p) H hHne hHp
    rw [hbot] at h1
    have hg1 : g ∈ centralizer (H : Set Q) :=
      (QuotientGroup.eq_one_iff g).mp (Subgroup.mem_bot.mp h1)
    obtain ⟨v, hv, hnv⟩ := hn
    apply hnv
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact ((Subgroup.mem_centralizer_iff.mp hg1) v hv).symm
  obtain ⟨m', hm'⟩ := hBS
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective m'
  refine ⟨m, ?_⟩
  set J : Subgroup Q := closure ({g, m * g * m⁻¹} : Set Q) with hJ
  have hgJ : g ∈ J := subset_closure (by simp)
  have hmgJ : m * g * m⁻¹ ∈ J := subset_closure (by simp)
  let a : ↥J := ⟨g, hgJ⟩
  let b : ↥J := ⟨m * g * m⁻¹, hmgJ⟩
  have hgen : Subgroup.closure ({a, b} : Set ↥J) = ⊤ := by
    have h1 := Subgroup.closure_closure_coe_preimage (k := ({g, m * g * m⁻¹} : Set Q))
    convert h1 using 2
    ext x
    simp [a, b, Subtype.ext_iff]
  let ρJ : ↥J →* Module.End (ZMod p) (Additive H) := ρ'.comp J.subtype
  have hqa : (ρJ a - 1) * (ρJ a - 1) = 0 := hquad g hq
  have hqb : (ρJ b - 1) * (ρJ b - 1) = 0 := by
    have h1 : ρJ b = ρ' m * ρ' g * ρ' m⁻¹ := by
      show ρ' (m * g * m⁻¹) = _
      rw [map_mul, map_mul]
    rw [h1]
    refine conj_quad ?_ ?_ (hquad g hq)
    · rw [← map_mul, mul_inv_cancel, map_one]
    · rw [← map_mul, inv_mul_cancel, map_one]
  have hnon : ∃ j : ↥J, ∀ k : ℕ, ρJ j ^ (p ^ k) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hm'
    have hmap : closure ({(QuotientGroup.mk g : Q ⧸ centralizer (H : Set Q)),
        (QuotientGroup.mk m) * QuotientGroup.mk g * (QuotientGroup.mk m)⁻¹} :
          Set (Q ⧸ centralizer (H : Set Q))) =
        J.map (QuotientGroup.mk' (centralizer (H : Set Q))) := by
      rw [hJ, MonoidHom.map_closure, Set.image_pair]
      simp
    rw [hmap]
    intro y
    obtain ⟨j, hj, hjy⟩ := Subgroup.mem_map.mp y.2
    obtain ⟨k, hk⟩ := hcon ⟨j, hj⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h2 : (ρ (QuotientGroup.mk j) ^ (p ^ k) : LinearMap.GeneralLinearGroup (ZMod p) (Additive H))
        = 1 := by
      apply Units.ext
      simpa [ρJ, ρ'] using hk
    have h3 : (QuotientGroup.mk j : Q ⧸ centralizer (H : Set Q)) ^ (p ^ k) = 1 := by
      apply hρinj
      rw [map_pow, map_one]
      exact h2
    show (y : Q ⧸ centralizer (H : Set Q)) ^ (p ^ k) = 1
    rw [← hjy]
    exact h3
  have hsl := exists_sl2_quotient hp2 hgen _ (Additive H) ρJ rfl hqa hqb hnon
  refine Sl2Quot.mono ?_ hsl
  intro j hj
  rw [mem_repKer]
  refine LinearMap.ext fun v => ?_
  obtain ⟨h, rfl⟩ := Additive.ofMul.surjective v
  show ρ' (j : Q) (Additive.ofMul h) = Additive.ofMul h
  rw [hev]
  congr 1
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  have hjc : (j : Q) ∈ centralizer (H : Set Q) := hj
  have := (Subgroup.mem_centralizer_iff.mp hjc) (h : Q) h.2
  rw [← this]; group

end CFSG.GH74.GLS.Stage2.Signalizer.L53
