module

public import CFSG.Holt.H78.Sec4FinalA4
public import CFSG.Holt.H78.Sec4Bender
public import CFSG.Holt.H78.Sec4SEAutFix
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.Timmesfeld.Bridge.SchurNarrow

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open CFSG.GH74.Uniqueness.Bender (rootCenter)
open scoped Pointwise

section Conj

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem fixSet_zpowers_conj (g v : G) :
    fixSet Ω (Subgroup.zpowers (g * v * g⁻¹)) = g • fixSet Ω (Subgroup.zpowers v) := by
  rw [fixSet_zpowers, fixSet_zpowers, smul_fixedBy]

theorem fixSet_eq_of_isConj_of_subset [Finite Ω] {v s : G} (hs : IsConj v s)
    (h : fixSet Ω (Subgroup.zpowers v) ⊆ fixSet Ω (Subgroup.zpowers s)) :
    fixSet Ω (Subgroup.zpowers s) = fixSet Ω (Subgroup.zpowers v) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hs
  refine (Set.eq_of_subset_of_ncard_le h ?_ (Set.toFinite _)).symm
  rw [fixSet_zpowers_conj, Set.ncard_smul_set]

theorem mul_self_eq_one_of_isConj {v s : G} (hv : v * v = 1) (hs : IsConj v s) : s * s = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hs
  rw [show g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ by group, hv, mul_one,
    mul_inv_cancel]

theorem normal_closure_of_isNormalSet {D : Set G}
    (hD : CFSG.Timmesfeld.Connectivity.IsNormalSet D) : (Subgroup.closure D).Normal := by
  constructor
  intro n hn g
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hD g x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem isPGroup_zpowers_sup_of_commute {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : Commute a b) : IsPGroup 2 ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
  refine (isPGroup_zpowers_of_orderOf_eq_two ha).to_sup_of_normal_right'
    (isPGroup_zpowers_of_orderOf_eq_two hb) ?_
  refine (Subgroup.zpowers_le.mpr ?_).trans
    (Subgroup.centralizer_le_normalizer (Subgroup.zpowers b : Set G))
  refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact ((hab.zpow_right k).eq).symm

end Conj

namespace FinConfig

section Claim

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
include C in
theorem v_mul_self : v * v = 1 := by
  rw [← sq, ← C.isTypeL.orderOf_eq_two, pow_orderOf_eq_one]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
include C in
theorem fixingSubgroup_le_stabilizer_inf :
    fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) ≤ stabilizer G α ⊓ stabilizer G β :=
  fun _ hg => Subgroup.mem_inf.mpr ⟨(mem_fixingSubgroup_iff G).mp hg α C.isTypeL.mem_fixSet,
    (mem_fixingSubgroup_iff G).mp hg β C.mem_fixSet⟩

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem psi_mem_N_of_isConj {s : G} (hs : IsConj v s)
    (hsΦ : s ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) :
    C.psi ⟨s, stabilizer_inf_le_stabilizer_pair α β
      (C.fixingSubgroup_le_stabilizer_inf hsΦ)⟩ ∈ C.N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set hsp := stabilizer_inf_le_stabilizer_pair α β (C.fixingSubgroup_le_stabilizer_inf hsΦ)
  have hs2 : s * s = 1 := mul_self_eq_one_of_isConj C.v_mul_self hs
  have hψ2 : C.psi ⟨s, hsp⟩ * C.psi ⟨s, hsp⟩ = 1 := by
    rw [← C.psi_mul hsp hsp, show (⟨s * s, mul_mem hsp hsp⟩ : stabilizer G ({α, β} : Set Ω)) = 1
      from Subtype.ext hs2, map_one]
  by_contra hN
  have h3 := C.isNaturalSE_N.three_le_ncard_fixedBy (C.psi_mem_normalizer _) hψ2 hN
  obtain ⟨c, hcF, hcb⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := fixedBy C.Psi (C.psi ⟨s, hsp⟩)) (by omega) C.bγ
  obtain ⟨δ₀, hδ₀⟩ := C.D.exists_coord_apply_eq C.i₀ c
  set O := jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β)
  set ŝ : twoPointSection G Ω α β := twoPointElt hsp with hŝ
  have hs2' : s ^ 2 ^ 1 = 1 := by rw [pow_one, sq, hs2]
  have hŝ2 : ŝ ^ 2 ^ 1 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hŝ, ← map_pow]
    exact (congrArg (twoPointHom G Ω α β) (Subtype.ext hs2' :
      (⟨s, hsp⟩ : stabilizer G ({α, β} : Set Ω)) ^ 2 ^ 1 = 1)).trans (map_one _))
  have hP : IsPGroup 2 (Subgroup.zpowers ŝ) := isPGroup_zpowers_of_pow_eq_one hŝ2
  have hstab : Subgroup.zpowers ŝ ≤ stabilizer (twoPointSection G Ω α β) (orbit O δ₀) := by
    rw [Subgroup.zpowers_le, mem_stabilizer_iff, smul_orbit_eq_orbit_smul, orbit_eq_iff]
    refine (C.coord_i₀_eq_iff _ _).mp ?_
    change C.D.coord δ₀ C.i₀ = C.D.coord (twoPointHom G Ω α β ⟨s, hsp⟩ δ₀) C.i₀
    rw [← C.psi_coord, hδ₀]
    exact hcF.symm
  obtain ⟨ε, hεO, hεF⟩ := exists_mem_fixSet_of_le_stabilizer hP (odd_card_orbit_jOddCore δ₀) hstab
  have hεs : s • (ε : Ω) = ε := by
    rw [fixSet_zpowers, mem_fixedBy] at hεF
    exact congrArg Subtype.val hεF
  have hεc : C.D.coord ε C.i₀ = c := by
    rw [← hδ₀]
    exact ((C.coord_i₀_eq_iff _ _).mpr hεO).symm
  have hεΦ : (ε : Ω) ∈ fixSet Ω (Subgroup.zpowers v) := by
    have hFs := fixSet_eq_of_isConj_of_subset (Ω := Ω) hs fun ω hω => by
      rw [fixSet_zpowers, mem_fixedBy]
      exact (mem_fixingSubgroup_iff G).mp hsΦ ω hω
    rw [← hFs, fixSet_zpowers, mem_fixedBy]
    exact hεs
  exact hcb (hεc ▸ (C.coord_eq_bγ_iff ε).mpr hεΦ)

theorem mem_Z_of_psi_mem_N (hS : Sec4Setting G Ω) {P₂ : Subgroup G} (hP₂ : IsPGroup 2 P₂)
    (hP₂Φ : P₂ ≤ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) (hZ : C.Z ≤ P₂) {s : G}
    (hsP : s ∈ P₂) (hs2 : s * s = 1)
    (hN : C.psi ⟨s, stabilizer_inf_le_stabilizer_pair α β
      (C.fixingSubgroup_le_stabilizer_inf (hP₂Φ hsP))⟩ ∈ C.N) : s ∈ C.Z := by
  have hsΦ := hP₂Φ hsP
  have hst := C.fixingSubgroup_le_stabilizer_inf hsΦ
  set hsp := stabilizer_inf_le_stabilizer_pair α β hst
  have hψ2 : C.psi ⟨s, hsp⟩ * C.psi ⟨s, hsp⟩ = 1 := by
    rw [← C.psi_mul hsp hsp, show (⟨s * s, mul_mem hsp hsp⟩ : stabilizer G ({α, β} : Set Ω)) = 1
      from Subtype.ext hs2, map_one]
  have hsγ : s • (C.γ : Ω) = C.γ := (mem_fixingSubgroup_iff G).mp hsΦ _ C.γ_mem
  have hZh : C.psi ⟨s, hsp⟩ ∈ C.Zhat :=
    C.isNaturalSE_N.mem_rootCenter_seRadical hN (C.psi_apply_bγ hsγ) hψ2
  obtain ⟨z, hz, hzψ⟩ := C.exists_mem_Z_of_mem_Zhat hS hZh
  have hzP := hZ hz
  have hzst : z ∈ stabilizer G α ⊓ stabilizer G β := C.X_le_stabilizer_inf (C.Y_le_X (C.Z_le_Y hz))
  have hzp := stabilizer_inf_le_stabilizer_pair α β hzst
  obtain ⟨k, hk⟩ := hP₂ ⟨z⁻¹ * s, mul_mem (inv_mem hzP) hsP⟩
  have hk' : (z⁻¹ * s) ^ 2 ^ k = 1 := by
    simpa only [Subgroup.coe_pow, Subgroup.coe_mk, OneMemClass.coe_one] using
      congrArg Subtype.val hk
  have h1 := C.eq_one_of_psi_eq_one hS hk' (mul_mem (inv_mem hzst) hst) (by
      rw [C.psi_mul (inv_mem hzp) hsp, C.psi_inv hzp, hzψ, inv_mul_cancel])
    fun δ _ hδΦ => by
      rw [mul_smul, (mem_fixingSubgroup_iff G).mp hsΦ δ hδΦ, inv_smul_eq_iff,
        C.smul_eq_of_mem_Z_of_mem_fixSet hS hz hδΦ]
  rw [inv_mul_eq_one] at h1
  exact h1 ▸ hz

theorem mem_Z_of_isConj_of_mem (hS : Sec4Setting G Ω) {P₂ : Subgroup G} (hP₂ : IsPGroup 2 P₂)
    (hP₂Φ : P₂ ≤ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) (hZ : C.Z ≤ P₂) {s : G}
    (hs : IsConj v s) (hsP : s ∈ P₂) : s ∈ C.Z :=
  C.mem_Z_of_psi_mem_N hS hP₂ hP₂Φ hZ hsP (mul_self_eq_one_of_isConj C.v_mul_self hs)
    (C.psi_mem_N_of_isConj hs (hP₂Φ hsP))

end Claim

section Prop52

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

theorem exists_conj_mem_Z_mul (hS : Sec4Setting G Ω) {t : G} (ht : IsConj v t)
    (htP : t ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) (hvt : Commute v t)
    (hne : v ≠ t) : ∃ k ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)),
      k⁻¹ * (v * t) * k ∈ C.Z ∧ k⁻¹ * (v * t) * k ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Φ := fixSet Ω (Subgroup.zpowers v)
  have hvP : v ∈ fixingSubgroup G Φ :=
    (mem_fixingSubgroup_iff G).mpr fun ω hω => FinConfig.v_smul_eq ⟨ω, hω⟩
  have hZ2 : IsPGroup 2 C.Z := C.sylow.2.1.to_le (C.Z_le_Y.trans C.Y_le_S)
  obtain ⟨P₂, hZP₂, hP₂⟩ := exists_fusionIsSylowIn_ge hZ2 (C.Z_le_fixingSubgroup hS)
  have ht2 : orderOf t = 2 := by
    obtain ⟨c, hc⟩ := ht
    exact (SemiconjBy.orderOf_eq _ hc).symm.trans C.isTypeL.orderOf_eq_two |>.symm ▸ rfl
  have hA : IsPGroup 2 ↥(Subgroup.zpowers v ⊔ Subgroup.zpowers t) :=
    isPGroup_zpowers_sup_of_commute C.isTypeL.orderOf_eq_two ht2 hvt
  obtain ⟨T, hAT, hT⟩ := exists_fusionIsSylowIn_ge hA
    (sup_le (Subgroup.zpowers_le.mpr hvP) (Subgroup.zpowers_le.mpr htP))
  obtain ⟨k, hkP, hk⟩ := exists_mem_conj_of_fusionIsSylowIn hP₂ hT
  have hconj : ∀ {g : G}, IsConj v g → g ∈ T → k⁻¹ * g * k ∈ C.Z := fun {g} hg hgT =>
    C.mem_Z_of_isConj_of_mem hS hP₂.2.1 hP₂.1 hZP₂
      (hg.trans (isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]⟩)) ((hk g).mp hgT)
  have hv' := hconj (IsConj.refl v) (hAT (Subgroup.mem_sup_left (Subgroup.mem_zpowers v)))
  have ht' := hconj ht (hAT (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
  refine ⟨k, hkP, ?_, fun h => hne ?_⟩
  · rw [show k⁻¹ * (v * t) * k = (k⁻¹ * v * k) * (k⁻¹ * t * k) by group]
    exact mul_mem hv' ht'
  · have h1 : v * t = 1 := by
      calc v * t = k * (k⁻¹ * (v * t) * k) * k⁻¹ := by group
        _ = 1 := by rw [h]; group
    calc v = v * (v * t) := by rw [h1, mul_one]
      _ = t := by rw [← mul_assoc, C.v_mul_self, one_mul]

include C in
theorem isConj_mul_of_mem_fixingSubgroup (hS : Sec4Setting G Ω) {t : G} (ht : IsConj v t)
    (htP : t ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) (hvt : Commute v t)
    (hne : v ≠ t) : IsConj v (v * t) ∧
      fixSet Ω (Subgroup.zpowers (v * t)) = fixSet Ω (Subgroup.zpowers v) := by
  obtain ⟨k, hkP, hZ, h1⟩ := C.exists_conj_mem_Z_mul hS ht htP hvt hne
  obtain ⟨h, -, -, hh⟩ := C.exists_conj_eq_of_mem_Z hS (C.v_mem_Z hS) C.v_ne_one hZ h1
  refine ⟨(isConj_iff.mpr ⟨h, hh⟩).trans (isConj_iff.mpr ⟨k, by group⟩), ?_⟩
  have hF := C.fixSet_eq_of_mem_Z hS hZ h1
  rw [show k⁻¹ * (v * t) * k = k⁻¹ * (v * t) * k⁻¹⁻¹ by rw [inv_inv], fixSet_zpowers_conj,
    inv_smul_eq_iff] at hF
  rw [hF]
  ext ω
  refine ⟨fun ⟨ω', hω', hω'e⟩ => ?_, fun hω => ⟨ω, hω, (mem_fixingSubgroup_iff G).mp hkP ω hω⟩⟩
  have h2 : k • ω' = ω' := (mem_fixingSubgroup_iff G).mp hkP ω' hω'
  simp only at hω'e
  rw [← hω'e, h2]
  exact hω'

include C in
theorem isConj_mul_of_forall_fixSet_eq (hS : Sec4Setting G Ω)
    (hH : ∀ s : G, IsConj v s → Commute v s →
      fixSet Ω (Subgroup.zpowers s) = fixSet Ω (Subgroup.zpowers v))
    {t : G} (ht : IsConj v t) (hvt : Commute v t) (hne : v ≠ t) : IsConj v (v * t) :=
  (C.isConj_mul_of_mem_fixingSubgroup hS ht ((mem_fixingSubgroup_iff G).mpr fun ω hω => by
    rw [← hH t ht hvt, fixSet_zpowers, mem_fixedBy] at hω
    exact hω) hvt hne).1

end Prop52

section TwoTransitive

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

theorem smul_eq_iff_piM_apply (hS : Sec4Setting G Ω)
    (g : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (ω ω' : fixSet Ω (Subgroup.zpowers v)) :
    (g : G) • (ω : Ω) = ω' ↔ C.piM hS g (C.Dv.coord ω C.i) = C.Dv.coord ω' C.i := by
  rw [C.piM_coord]
  constructor
  · intro h
    exact congrArg (fun p => C.Dv.coord p C.i) (Subtype.ext h)
  · intro h
    exact congrArg Subtype.val (C.coord_Dv_injective
      (show C.Dv.coord (centralizerImageElt (Ω := Ω) g.2 • ω) = C.Dv.coord ω' from
        funext fun j => by rcases C.eq_i hS j with rfl; exact h))

theorem exists_piM_eq (hS : Sec4Setting G Ω) {m : Equiv.Perm (C.Dv.Ψc C.i)}
    (hm : m ∈ C.Dv.M C.i) :
    ∃ c : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G), C.piM hS c = m := by
  obtain ⟨l, -, rfl⟩ := mem_factorImage.mp hm
  obtain ⟨c, hc, hcl⟩ := mem_centralizerImage.mp ((l : typeLSection G Ω v)).2
  have he : centralizerImageElt (Ω := Ω) hc = (l : typeLSection G Ω v) :=
    Subtype.ext (Equiv.ext fun ω => Subtype.ext (hcl ω).symm)
  refine ⟨⟨c, hc⟩, ?_⟩
  rw [C.piM_eq_rho hS ⟨c, hc⟩ (he ▸ l.2)]
  exact congrArg (C.Dv.ρ C.i) (Subtype.ext he)

include C in
theorem exists_centralizer_smul_eq (hS : Sec4Setting G Ω) {a b a' b' : Ω}
    (ha : a ∈ fixSet Ω (Subgroup.zpowers v)) (hb : b ∈ fixSet Ω (Subgroup.zpowers v))
    (hab : a ≠ b) (ha' : a' ∈ fixSet Ω (Subgroup.zpowers v))
    (hb' : b' ∈ fixSet Ω (Subgroup.zpowers v)) (hab' : a' ≠ b') :
    ∃ c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G),
      c • a = a' ∧ c • b = b' := by
  have hM := C.isNaturalSE_Dv C.i
  obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
  have := hA.isPretransitive
  set A := C.Dv.coord ⟨a, ha⟩ C.i
  set B := C.Dv.coord ⟨b, hb⟩ C.i
  set A' := C.Dv.coord ⟨a', ha'⟩ C.i
  set B' := C.Dv.coord ⟨b', hb'⟩ C.i
  have hinj : ∀ {ω ω' : fixSet Ω (Subgroup.zpowers v)}, ω ≠ ω' →
      C.Dv.coord ω C.i ≠ C.Dv.coord ω' C.i := fun {ω ω'} hne h => hne (C.coord_Dv_injective
        (funext fun j => by rcases C.eq_i hS j with rfl; exact h))
  have hAB : A ≠ B := hinj fun h => hab (congrArg Subtype.val h)
  have hAB' : A' ≠ B' := hinj fun h => hab' (congrArg Subtype.val h)
  obtain ⟨m₁, hm₁⟩ := exists_smul_eq (C.Dv.M C.i) A A'
  have hm₁A : (m₁ : Equiv.Perm _) A = A' := hm₁
  have hm₁B : (m₁ : Equiv.Perm _) B ≠ A' := fun h =>
    hAB ((m₁ : Equiv.Perm _).injective (h.trans hm₁A.symm)).symm
  obtain ⟨r, hr, hrB⟩ := hM.exists_mem_seRadical_apply_eq (b := A') hm₁B hAB'.symm
  obtain ⟨c, hc⟩ := C.exists_piM_eq hS (mul_mem (seRadical_le hr) m₁.2)
  refine ⟨c, c.2, (C.smul_eq_iff_piM_apply hS c ⟨a, ha⟩ ⟨a', ha'⟩).mpr ?_,
    (C.smul_eq_iff_piM_apply hS c ⟨b, hb⟩ ⟨b', hb'⟩).mpr ?_⟩
  · rw [hc, Equiv.Perm.mul_apply, hm₁A]
    exact apply_eq_of_mem_seRadical hr
  · rw [hc, Equiv.Perm.mul_apply, hrB]

end TwoTransitive


section Lemma60

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_Y_of_mem_S_of_mem_X {y : G} (hyS : y ∈ C.S) (hyX : y ∈ C.X) : y ∈ C.Y := by
  have hP : IsPGroup 2 ↥(C.Y ⊔ Subgroup.zpowers y) :=
    C.sylow.2.1.to_le (sup_le C.Y_le_S (Subgroup.zpowers_le.mpr hyS))
  have h := C.fusionIsSylowIn_Y.2.2 _ (sup_le C.Y_le_X (Subgroup.zpowers_le.mpr hyX)) hP
    le_sup_left
  exact h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

include C in
theorem v_mem_stabilizer_inf (hS : Sec4Setting G Ω) : v ∈ stabilizer G α ⊓ stabilizer G β :=
  C.X_le_stabilizer_inf (C.Y_le_X (C.Z_le_Y (C.v_mem_Z hS)))

theorem psi_v_spec (hS : Sec4Setting G Ω) :
    C.psi ⟨v, stabilizer_inf_le_stabilizer_pair α β (C.v_mem_stabilizer_inf hS)⟩ ∈ C.N ∧
      C.psi ⟨v, stabilizer_inf_le_stabilizer_pair α β (C.v_mem_stabilizer_inf hS)⟩ *
        C.psi ⟨v, stabilizer_inf_le_stabilizer_pair α β (C.v_mem_stabilizer_inf hS)⟩ = 1 ∧
      ∀ c : C.Psi, C.psi ⟨v, stabilizer_inf_le_stabilizer_pair α β
        (C.v_mem_stabilizer_inf hS)⟩ c = c → c = C.bγ := by
  set hvp := stabilizer_inf_le_stabilizer_pair α β (C.v_mem_stabilizer_inf hS)
  have hvZ := C.v_mem_Z hS
  have hN : C.psi ⟨v, hvp⟩ ∈ C.N := seRadical_le (C.Zhat_le_Rhat (C.psi_mem_Zhat_of_mem_Z hvZ))
  have h2 : C.psi ⟨v, hvp⟩ * C.psi ⟨v, hvp⟩ = 1 := by
    rw [← C.psi_mul hvp hvp, show (⟨v * v, mul_mem hvp hvp⟩ : stabilizer G ({α, β} : Set Ω)) = 1
      from Subtype.ext C.v_mul_self, map_one]
  have h1 : C.psi ⟨v, hvp⟩ ≠ 1 := fun h => C.v_ne_one (C.eq_one_of_psi_eq_one hS (k := 1)
    (by rw [pow_one, sq, C.v_mul_self]) (C.v_mem_stabilizer_inf hS) h
    fun δ _ hδΦ => FinConfig.v_smul_eq ⟨δ, hδΦ⟩)
  refine ⟨hN, h2, fun c hc => ?_⟩
  obtain ⟨δ, -, hu⟩ := C.isNaturalSE_N.existsUnique_fixed (x := ⟨_, hN⟩)
    (by rw [Subgroup.orderOf_mk]; exact orderOf_eq_prime (by rw [sq, h2]) h1)
  have hγ : C.psi ⟨v, hvp⟩ C.bγ = C.bγ := C.psi_apply_bγ (FinConfig.v_smul_eq ⟨_, C.γ_mem⟩)
  exact (hu c hc).trans (hu C.bγ hγ).symm

include C in
theorem fixSet_conj_eq_of_commute (hS : Sec4Setting G Ω) {h : G}
    (hh : h ∈ stabilizer G α ⊓ stabilizer G β) (hc : Commute v (h * v * h⁻¹)) :
    fixSet Ω (Subgroup.zpowers (h * v * h⁻¹)) = fixSet Ω (Subgroup.zpowers v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s := h * v * h⁻¹ with hs_def
  have hhp := stabilizer_inf_le_stabilizer_pair α β hh
  have hvst := C.v_mem_stabilizer_inf hS
  have hvp := stabilizer_inf_le_stabilizer_pair α β hvst
  have hsp : s ∈ stabilizer G ({α, β} : Set Ω) := mul_mem (mul_mem hhp hvp) (inv_mem hhp)
  have hψs : C.psi ⟨s, hsp⟩ = C.psi ⟨h, hhp⟩ * C.psi ⟨v, hvp⟩ * (C.psi ⟨h, hhp⟩)⁻¹ := by
    rw [C.psi_mul (mul_mem hhp hvp) (inv_mem hhp), C.psi_mul hhp hvp, C.psi_inv hhp]
  obtain ⟨hvN, hv2, hvfix⟩ := C.psi_v_spec hS
  have hcomm : C.psi ⟨v, hvp⟩ * C.psi ⟨s, hsp⟩ = C.psi ⟨s, hsp⟩ * C.psi ⟨v, hvp⟩ := by
    rw [← C.psi_mul hvp hsp, ← C.psi_mul hsp hvp]
    exact congrArg C.psi (Subtype.ext hc.eq)
  set ψh := C.psi ⟨h, hhp⟩
  set ψv := C.psi ⟨v, hvp⟩
  have e1 : ψh⁻¹ (ψh C.bγ) = C.bγ := Equiv.Perm.inv_eq_iff_eq.mpr rfl
  have e2 : ∀ c, ψh (ψh⁻¹ c) = c := fun c => Equiv.Perm.eq_inv_iff_eq.mp rfl
  have hsb : C.psi ⟨s, hsp⟩ (ψh C.bγ) = ψh C.bγ := by
    rw [hψs, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, e1,
      C.psi_apply_bγ (FinConfig.v_smul_eq ⟨_, C.γ_mem⟩)]
  have hsfix : ∀ c, C.psi ⟨s, hsp⟩ c = c → c = ψh C.bγ := fun c hc' => by
    rw [hψs, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← Equiv.Perm.eq_inv_iff_eq] at hc'
    rw [← hvfix _ hc', e2]
  have hvb : ψv (ψh C.bγ) = ψh C.bγ := hsfix _ (by
    rw [← Equiv.Perm.mul_apply, ← hcomm, Equiv.Perm.mul_apply, hsb])
  have hb : ψh C.bγ = C.bγ := hvfix _ hvb
  have hsB : ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω (Subgroup.zpowers v) → s • δ = δ := by
    intro δ hδΔ hδΦ
    have hδ' := smul_mem_holtDelta_of_mem_inf (inv_mem hh) hδΔ
    have hcoord : C.D.coord ⟨h⁻¹ • δ, hδ'⟩ C.i₀ = C.bγ := by
      have h1 := C.psi_coord ⟨h⁻¹, inv_mem hhp⟩ ⟨δ, hδΔ⟩
      have e : twoPointHom G Ω α β ⟨h⁻¹, inv_mem hhp⟩ ⟨δ, hδΔ⟩ = ⟨h⁻¹ • δ, hδ'⟩ := Subtype.ext rfl
      rw [e, (C.coord_eq_bγ_iff ⟨δ, hδΔ⟩).mpr hδΦ, C.psi_inv hhp] at h1
      rw [← h1, Equiv.Perm.inv_eq_iff_eq, hb]
    have hΦ' := (C.coord_eq_bγ_iff ⟨h⁻¹ • δ, hδ'⟩).mp hcoord
    rw [hs_def, mul_smul, mul_smul, FinConfig.v_smul_eq ⟨_, hΦ'⟩, smul_inv_smul]
  have hs2 : s * s = 1 := mul_self_eq_one_of_isConj C.v_mul_self (isConj_iff.mpr ⟨h, rfl⟩)
  have hsγ : s • (C.γ : Ω) = C.γ := hsB _ C.γ.2 C.γ_mem
  have hsN : C.psi ⟨s, hsp⟩ ∈ C.N := by
    rw [hψs]
    exact (Subgroup.mem_normalizer_iff.mp (C.psi_mem_normalizer ⟨h, hhp⟩) _).mp hvN
  have hψs2 : C.psi ⟨s, hsp⟩ * C.psi ⟨s, hsp⟩ = 1 := by
    rw [← C.psi_mul hsp hsp, show (⟨s * s, mul_mem hsp hsp⟩ : stabilizer G ({α, β} : Set Ω)) = 1
      from Subtype.ext hs2, map_one]
  have hsZh : C.psi ⟨s, hsp⟩ ∈ C.Zhat :=
    C.isNaturalSE_N.mem_rootCenter_seRadical hsN (C.psi_apply_bγ hsγ) hψs2
  have hsα : s • α = α := by
    rw [hs_def, mul_smul, mul_smul, (Subgroup.mem_inf.mp (inv_mem hh)).1,
      (Subgroup.mem_inf.mp hvst).1, (Subgroup.mem_inf.mp hh).1]
  have hsβ : s • β = β := by
    rw [hs_def, mul_smul, mul_smul, (Subgroup.mem_inf.mp (inv_mem hh)).2,
      (Subgroup.mem_inf.mp hvst).2, (Subgroup.mem_inf.mp hh).2]
  have hsst : s ∈ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hsα, hsβ⟩, hsγ⟩
  have hvst3 : v ∈ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω) :=
    C.X_le (C.Y_le_X (C.Z_le_Y (C.v_mem_Z hS)))
  have hso : orderOf s = 2 := by
    obtain ⟨c, hc'⟩ := (isConj_iff.mpr ⟨h, rfl⟩ : IsConj v s)
    exact (SemiconjBy.orderOf_eq _ hc').symm.trans C.isTypeL.orderOf_eq_two
  have hA := isPGroup_zpowers_sup_of_commute C.isTypeL.orderOf_eq_two hso hc
  obtain ⟨S', hAS', hS'⟩ := exists_fusionIsSylowIn_ge hA
    (sup_le (Subgroup.zpowers_le.mpr hvst3) (Subgroup.zpowers_le.mpr hsst))
  obtain ⟨k, hk, hkS⟩ := exists_mem_conj_of_fusionIsSylowIn C.sylow hS'
  set g := k⁻¹ with hg_def
  have hg : g ∈ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω) := inv_mem hk
  have hgS : ∀ y ∈ S', g * y * g⁻¹ ∈ C.S := fun y hy => by
    rw [hg_def, inv_inv]
    exact (hkS y).mp hy
  have hgp := stabilizer_inf_le_stabilizer_pair α β (Subgroup.mem_inf.mp hg).1
  have hconjZ : ∀ {y : G} (hyX : y ∈ C.X), C.psi ⟨y, C.X_le_stabilizer_pair hyX⟩ ∈ C.Zhat →
      y ∈ S' → g * y * g⁻¹ ∈ C.Z := by
    intro y hyX hyZ hyS'
    have hyX' := C.conj_mem_X hg hyX
    refine C.mem_Z.mpr ⟨C.mem_Y_of_mem_S_of_mem_X (hgS y hyS') hyX', ?_⟩
    have h := conj_mem_rootCenter_seRadical (C.psi_mem_normalizer ⟨g, hgp⟩)
      (C.psi_apply_bγ (g := ⟨g, hgp⟩) (Subgroup.mem_inf.mp hg).2) hyZ
    rwa [← map_inv, ← map_mul, ← map_mul] at h
  have hvX : v ∈ C.X := C.Y_le_X (C.Z_le_Y (C.v_mem_Z hS))
  have hsX : s ∈ C.X := C.mem_X.mpr ⟨conj_mem_closure_longInvSwap hh (C.v_mem_closure hS),
    hsst, C.mem_psiPre.mpr ⟨hsp, C.Zhat_le_Rhat hsZh⟩⟩
  have hvZ := hconjZ hvX (C.psi_mem_Zhat_of_mem_Z (C.v_mem_Z hS))
    (hAS' (Subgroup.mem_sup_left (Subgroup.mem_zpowers v)))
  have hsZ := hconjZ hsX hsZh (hAS' (Subgroup.mem_sup_right (Subgroup.mem_zpowers s)))
  have hne : ∀ {y : G}, y ≠ 1 → g * y * g⁻¹ ≠ 1 := fun {y} hy h => hy (by
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  have hs1 : s ≠ 1 := fun h' => C.v_ne_one (by
    calc v = h⁻¹ * s * h := by rw [hs_def]; group
      _ = 1 := by rw [h']; group)
  have h1 := C.fixSet_eq_of_mem_Z hS hvZ (hne C.v_ne_one)
  have h2 := C.fixSet_eq_of_mem_Z hS hsZ (hne hs1)
  rw [fixSet_zpowers_conj] at h1 h2
  calc fixSet Ω (Subgroup.zpowers s) = g⁻¹ • g • fixSet Ω (Subgroup.zpowers s) :=
        (inv_smul_smul g _).symm
    _ = g⁻¹ • g • fixSet Ω (Subgroup.zpowers v) := by rw [h2, h1]
    _ = fixSet Ω (Subgroup.zpowers v) := inv_smul_smul g _


omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_eq_self_of_mem_centralizer_zpowers {c : G}
    (hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    c * v * c⁻¹ = v := by
  rw [← Subgroup.mem_centralizer_iff.mp hc v (Subgroup.mem_zpowers v)]
  group

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_fixSet_zpowers_of_mem_centralizer {c : G}
    (hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    c • fixSet Ω (Subgroup.zpowers v) = fixSet Ω (Subgroup.zpowers v) := by
  rw [← fixSet_zpowers_conj, conj_eq_self_of_mem_centralizer_zpowers hc]

include C in
theorem fixSet_eq_of_isConj_of_commute (hS : Sec4Setting G Ω) {s : G} (hs : IsConj v s)
    (hvs : Commute v s) {a b : Ω} (hab : a ≠ b) (ha : a ∈ fixSet Ω (Subgroup.zpowers s))
    (haΦ : a ∈ fixSet Ω (Subgroup.zpowers v)) (hb : b ∈ fixSet Ω (Subgroup.zpowers s))
    (hbΦ : b ∈ fixSet Ω (Subgroup.zpowers v)) :
    fixSet Ω (Subgroup.zpowers s) = fixSet Ω (Subgroup.zpowers v) := by
  have hαΦ := C.isTypeL.mem_fixSet
  have hβΦ := C.mem_fixSet
  obtain ⟨c₁, hc₁, hc₁a, hc₁b⟩ := C.exists_centralizer_smul_eq hS haΦ hbΦ hab hαΦ hβΦ C.ne
  set s₁ := c₁ * s * c₁⁻¹ with hs₁_def
  have hs₁ : IsConj v s₁ := hs.trans (isConj_iff.mpr ⟨c₁, rfl⟩)
  have hvs₁ : Commute v s₁ := by
    have h1 := conj_eq_self_of_mem_centralizer_zpowers hc₁
    show v * s₁ = s₁ * v
    calc v * s₁ = (c₁ * v * c₁⁻¹) * s₁ := by rw [h1]
      _ = c₁ * (v * s) * c₁⁻¹ := by rw [hs₁_def]; group
      _ = c₁ * (s * v) * c₁⁻¹ := by rw [hvs.eq]
      _ = s₁ * (c₁ * v * c₁⁻¹) := by rw [hs₁_def]; group
      _ = s₁ * v := by rw [h1]
  have hFs₁ : fixSet Ω (Subgroup.zpowers s₁) = c₁ • fixSet Ω (Subgroup.zpowers s) :=
    fixSet_zpowers_conj c₁ s
  obtain ⟨g, hg⟩ := isConj_iff.mp hs₁
  have hgΦ : fixSet Ω (Subgroup.zpowers s₁) = g • fixSet Ω (Subgroup.zpowers v) := by
    rw [← hg, fixSet_zpowers_conj]
  have hα' : g⁻¹ • α ∈ fixSet Ω (Subgroup.zpowers v) := by
    have h : α ∈ fixSet Ω (Subgroup.zpowers s₁) := by rw [hFs₁]; exact ⟨a, ha, hc₁a⟩
    rw [hgΦ] at h
    exact Set.mem_smul_set_iff_inv_smul_mem.mp h
  have hβ' : g⁻¹ • β ∈ fixSet Ω (Subgroup.zpowers v) := by
    have h : β ∈ fixSet Ω (Subgroup.zpowers s₁) := by rw [hFs₁]; exact ⟨b, hb, hc₁b⟩
    rw [hgΦ] at h
    exact Set.mem_smul_set_iff_inv_smul_mem.mp h
  have hne' : g⁻¹ • α ≠ g⁻¹ • β := fun h => C.ne (smul_left_cancel _ h)
  obtain ⟨c₂, hc₂, hc₂a, hc₂b⟩ := C.exists_centralizer_smul_eq hS hαΦ hβΦ C.ne hα' hβ' hne'
  have hh : g * c₂ ∈ stabilizer G α ⊓ stabilizer G β := Subgroup.mem_inf.mpr
    ⟨by rw [mem_stabilizer_iff, mul_smul, hc₂a, smul_inv_smul],
      by rw [mem_stabilizer_iff, mul_smul, hc₂b, smul_inv_smul]⟩
  have hhv : g * c₂ * v * (g * c₂)⁻¹ = s₁ := by
    rw [show g * c₂ * v * (g * c₂)⁻¹ = g * (c₂ * v * c₂⁻¹) * g⁻¹ by group,
      conj_eq_self_of_mem_centralizer_zpowers hc₂, hg]
  have key := C.fixSet_conj_eq_of_commute hS hh (hhv ▸ hvs₁)
  rw [hhv] at key
  calc fixSet Ω (Subgroup.zpowers s) = c₁⁻¹ • c₁ • fixSet Ω (Subgroup.zpowers s) :=
        (inv_smul_smul c₁ _).symm
    _ = c₁⁻¹ • fixSet Ω (Subgroup.zpowers v) := by rw [← hFs₁, key]
    _ = fixSet Ω (Subgroup.zpowers v) := by
        rw [inv_smul_eq_iff, smul_fixSet_zpowers_of_mem_centralizer hc₁]

end Lemma60


section Prop52Main


variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

open CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge in
include C in
theorem exists_isConj_commute_fixSet_ne (hS : Sec4Setting G Ω) :
    ∃ s : G, IsConj v s ∧ Commute v s ∧
      fixSet Ω (Subgroup.zpowers s) ≠ fixSet Ω (Subgroup.zpowers v) := by
  by_contra hcon
  have hH : ∀ s : G, IsConj v s → Commute v s →
      fixSet Ω (Subgroup.zpowers s) = fixSet Ω (Subgroup.zpowers v) := fun s h1 h2 => by
    by_contra h3
    exact hcon ⟨s, h1, h2, h3⟩
  have := hS.preprimitive
  have := hS.star.isPretransitive
  set D : Set G := {s | IsConj v s} with hD
  have hDn : IsNormalSet D := fun g x hx => hx.trans (isConj_iff.mpr ⟨g, rfl⟩)
  have hD2 : IsInvolutionSet D := fun d hd => by
    obtain ⟨c, hc⟩ := hd
    exact (SemiconjBy.orderOf_eq _ hc).symm.trans C.isTypeL.orderOf_eq_two
  have hback : ∀ (g s' : G), IsConj v s' → Commute (g * v * g⁻¹) s' →
      IsConj v (g⁻¹ * s' * g) ∧ Commute v (g⁻¹ * s' * g) := fun g s' hs' hc => by
    refine ⟨hs'.trans (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩), ?_⟩
    have h := hc.eq
    show v * (g⁻¹ * s' * g) = g⁻¹ * s' * g * v
    calc v * (g⁻¹ * s' * g) = g⁻¹ * (g * v * g⁻¹ * s') * g := by group
      _ = g⁻¹ * (s' * (g * v * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * s' * g * v := by group
  have hFix : ∀ s ∈ D, ∀ s' ∈ D, Commute s s' →
      fixSet Ω (Subgroup.zpowers s') = fixSet Ω (Subgroup.zpowers s) := by
    intro s hs s' hs' hss'
    obtain ⟨g, rfl⟩ := isConj_iff.mp hs
    obtain ⟨ht, hc⟩ := hback g s' hs' hss'
    have h := fixSet_zpowers_conj (Ω := Ω) g (g⁻¹ * s' * g)
    rwa [show g * (g⁻¹ * s' * g) * g⁻¹ = s' by group, hH _ ht hc, ← fixSet_zpowers_conj] at h
  have hReach : ∀ y, Reach D v y →
      fixSet Ω (Subgroup.zpowers y) = fixSet Ω (Subgroup.zpowers v) := by
    intro y hy
    induction hy with
    | refl => rfl
    | tail _ hbc ih => exact (hFix _ hbc.1 _ hbc.2.1 hbc.2.2).trans ih
  have hdisc : Disconnected D := by
    obtain ⟨ω, hω⟩ : ∃ ω : Ω, v • ω ≠ ω := by
      by_contra h
      push Not at h
      exact C.v_ne_one (eq_of_smul_eq_smul fun ω => by rw [h ω, one_smul])
    obtain ⟨g, hg⟩ := exists_smul_eq G α ω
    refine ⟨v, IsConj.refl v, g * v * g⁻¹, isConj_iff.mpr ⟨g, rfl⟩, fun hr => hω ?_⟩
    have h1 := hReach _ hr
    have h2 : ω ∈ g • fixSet Ω (Subgroup.zpowers v) := ⟨α, C.isTypeL.mem_fixSet, hg⟩
    rw [← fixSet_zpowers_conj, h1, fixSet_zpowers, mem_fixedBy] at h2
    exact h2
  have hnp : CFSG.Timmesfeld.Moufang.NoPolar D := by
    intro s hs s' hs' hss' hne
    obtain ⟨g, rfl⟩ := isConj_iff.mp hs
    obtain ⟨ht, hc⟩ := hback g s' hs' hss'
    have hne' : v ≠ g⁻¹ * s' * g := fun h => hne (by rw [h]; group)
    exact (C.isConj_mul_of_forall_fixSet_eq hS hH ht hc hne').trans
      (isConj_iff.mpr ⟨g, by group⟩)
  obtain ⟨M, hM⟩ := exists_fusionStronglyEmbedded_closure
    CFSG.ShultStronglyClosedTI.theoremTwo schurNarrowInput hDn hD2 hnp hdisc
  have hv := mem_longInv_of_mem_of_fusionStronglyEmbedded hS.star hS.pPrimeCore_eq_bot
    (normal_closure_of_isNormalSet hDn) ⟨M, hM⟩ (Subgroup.subset_closure (IsConj.refl v))
    C.isTypeL.orderOf_eq_two
  obtain ⟨-, -, -, -, -, -, -, hvJ⟩ := C.isTypeL
  exact hvJ hv

end Prop52Main



end FinConfig

end CFSG.Holt.H78
