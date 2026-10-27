module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Sylow
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Diag
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Torus
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusCentralizers
public import CFSG.RankThree.PartTwo.KFacts.AutG2
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.RankThree.Chevalley

section Pure

theorem exists_pow_eq_of_pow_eq {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] {n m : ℕ}
    (hcard : Nat.card G = n * m) {x : G} (hx : x ^ m = 1) : ∃ t : G, t ^ n = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf g = n * m := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hcard
  have hm : m ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card G := Nat.card_pos
    rw [hcard] at this
    simp at this
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  have h1 : (orderOf g : ℤ) ∣ j * m := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_mul, zpow_natCast]
    exact hx
  rw [hord] at h1
  push_cast at h1
  have h2 : (n : ℤ) ∣ j := by
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm
    rw [mul_comm (n : ℤ) m, mul_comm j m] at h1
    exact (mul_dvd_mul_iff_left hm').1 h1
  obtain ⟨k, rfl⟩ := h2
  exact ⟨g ^ k, by rw [← zpow_natCast, ← zpow_mul, mul_comm]⟩

theorem exists_pow_succ_eq_of_pow_eq_self {K₂ : Type} [Field K₂] [Finite K₂] {q : ℕ}
    (hq : Nat.card K₂ = q ^ 2) (hq1 : 1 ≤ q) {a : K₂ˣ} (ha : a ^ q = a) :
    ∃ t : K₂ˣ, t ^ (q + 1) = a := by
  refine exists_pow_eq_of_pow_eq (m := q - 1) ?_ ?_
  · rw [Nat.card_units, hq]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have : (q' + 1) ^ 2 = (q' + 1 + 1) * (q' + 1 - 1) + 1 := by
      rw [Nat.add_sub_cancel]
      ring
    omega
  · have h : a ^ (q - 1) * a = a ^ q := by
      rw [← pow_succ, Nat.sub_add_cancel hq1]
    rw [ha] at h
    exact mul_right_cancel (h.trans (one_mul a).symm)



end Pure

section Basic


variable {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂]

@[expose] noncomputable def twistEmb (g : ModGL .G2 K₂) : ↥(adjointGroup .G2 K) →* ModGL .G2 K₂ :=
  ((MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K K₂))).comp
    (adjointGroup .G2 K).subtype

theorem twistEmb_apply (g : ModGL .G2 K₂) (y : ↥(adjointGroup .G2 K)) :
    twistEmb g y = g * baseChangeGL (algebraMap K K₂) (y : ModGL .G2 K) * g⁻¹ := rfl

theorem map_twistEmb_top (g : ModGL .G2 K₂) :
    (⊤ : Subgroup ↥(adjointGroup .G2 K)).map (twistEmb g) = conjEntrywiseImage K g := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, conjEntrywiseImage, twistEmb,
    MonoidHom.comp_apply, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩



theorem twistEmb_injective (g : ModGL .G2 K₂) : Function.Injective (twistEmb (K := K) g) :=
  fun _ _ h =>
  Subtype.val_injective (baseChangeGL_injective (τ := .G2) (algebraMap K K₂)
    ((MulAut.conj g).injective h))


theorem entrywise_baseChangeGL_fixed [Finite K] {σ : K₂ ≃+* K₂} (hσ : ∀ c, σ c = c ^ Nat.card K)
    (w : ModGL .G2 K) :
    Units.map (entrywiseHom (σ : K₂ →+* K₂)) (baseChangeGL (algebraMap K K₂) w) =
      baseChangeGL (algebraMap K K₂) w := by
  have hfix : (σ : K₂ →+* K₂).comp (algebraMap K K₂) = algebraMap K K₂ := by
    ext c
    have : Fintype K := Fintype.ofFinite K
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [hσ, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self,
    baseChangeGL_baseChangeGL, hfix]


end Basic

section Adj

variable {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂]

theorem twistedEntrywise_mem_adjointGroup {σ : K₂ ≃+* K₂} {z : ModGL .G2 K₂}
    (hz : z ∈ adjointGroup .G2 K₂) {y : ModGL .G2 K₂} (hy : y ∈ adjointGroup .G2 K₂) :
    twistedEntrywise z (σ : K₂ →+* K₂) y ∈ adjointGroup .G2 K₂ := by
  rw [twistedEntrywise_apply]
  have h := (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K₂ σ ⟨y, hy⟩).2
  rw [CFSG.RankThree.PartTwo.KFacts.coe_g2FieldHom] at h
  exact mul_mem (mul_mem hz h) (inv_mem hz)


end Adj

section Lang

variable {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂]

theorem exists_planeImage_conj_le {g : ModGL .G2 K₂}
    (hΓY : conjEntrywiseImage K g ≤ adjointGroup .G2 K₂) [Finite K₂]
    (h3₂ : 3 ∣ Nat.card K₂ - 1)
    (E : Subgroup ↥(adjointGroup .G2 K)) [hE : CFSG.IsElementaryAbelian 3 E] :
    ∃ y : ↥(adjointGroup .G2 K₂), ∀ e ∈ E,
      (y : ModGL .G2 K₂) * twistEmb g e * (y : ModGL .G2 K₂)⁻¹ ∈ torusTorsion K₂ 3 := by
  classical
  obtain ⟨ω, hω1, hω3⟩ : ∃ ω : K₂, ω ≠ 1 ∧ ω ^ 3 = 1 := by
    have h3' : 3 ∣ Nat.card K₂ˣ := by
      rw [Nat.card_units]
      exact h3₂
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3'
    refine ⟨(x : K₂), ?_, ?_⟩
    · intro h
      have : x = 1 := Units.ext h
      rw [this, orderOf_one] at hx
      omega
    · have := pow_orderOf_eq_one x
      rw [hx] at this
      exact congrArg Units.val this |>.trans (by simp)
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h0 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hω1)
  obtain ⟨ι, hι, hιx⟩ := exists_a2Hom_injective (K := K₂)
  have hψmem : ∀ y : ↥(adjointGroup .G2 K), twistEmb g y ∈ adjointGroup .G2 K₂ := fun y =>
    hΓY (by rw [← map_twistEmb_top]; exact ⟨y, trivial, rfl⟩)
  let ψ' : ↥(adjointGroup .G2 K) →* ↥(adjointGroup .G2 K₂) :=
    (twistEmb g).codRestrict _ hψmem
  have hψ'val : ∀ y, ((ψ' y : ↥(adjointGroup .G2 K₂)) : ModGL .G2 K₂) = twistEmb g y :=
    fun y => rfl
  have hEp : IsPGroup 3 E := IsElementaryAbelian.isPGroup 3 E
  have hE2p : IsPGroup 3 (E.map ψ') :=
    hEp.of_surjective (ψ'.subgroupMap E) (ψ'.subgroupMap_surjective E)
  obtain ⟨y1, hy1⟩ := exists_conj_le_range_of_three_dvd_sub_one h3₂ ι hι (E.map ψ') hE2p
  have hcube : ∀ e ∈ E, e ^ 3 = 1 := fun e he =>
    elemPow_eq_one_of_isElementaryAbelian (A := E) (p := 3) e he
  have hcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := fun e he e' he' => by
    have := hE.is_comm.comm (⟨e, he⟩ : E) ⟨e', he'⟩
    exact congrArg Subtype.val this
  have hrange : ∀ e ∈ E, ∃ x : Matrix.SpecialLinearGroup (Fin 3) K₂,
      ι x = y1 * ψ' e * y1⁻¹ := fun e he =>
    hy1 ⟨ψ' e, ⟨e, he, rfl⟩, rfl⟩
  set Et : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K₂) :=
    ((E.map ψ').map (MulAut.conj y1).toMonoidHom).comap ι with hEt
  have hEtmem : ∀ x, x ∈ Et ↔ ι x ∈ (E.map ψ').map (MulAut.conj y1).toMonoidHom :=
    fun x => Iff.rfl
  have hEtdesc : ∀ x ∈ Et, ∃ e ∈ E, ι x = y1 * ψ' e * y1⁻¹ := by
    intro x hx
    obtain ⟨_, ⟨e, he, rfl⟩, h⟩ := (hEtmem x).1 hx
    exact ⟨e, he, h.symm⟩
  have hEt3 : ∀ x ∈ Et, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := hEtdesc x hx
    apply hι
    rw [map_pow, map_one, hxe]
    have : (y1 * ψ' e * y1⁻¹) ^ 3 = y1 * ψ' (e ^ 3) * y1⁻¹ := by
      rw [conj_pow, map_pow]
    rw [this, hcube e he, map_one]
    group
  have hEtc : ∀ x ∈ Et, ∀ x' ∈ Et, x * x' = x' * x := by
    intro x hx x' hx'
    obtain ⟨e, he, hxe⟩ := hEtdesc x hx
    obtain ⟨e', he', hxe'⟩ := hEtdesc x' hx'
    apply hι
    rw [map_mul, map_mul, hxe, hxe']
    have : y1 * ψ' e * y1⁻¹ * (y1 * ψ' e' * y1⁻¹) = y1 * ψ' (e * e') * y1⁻¹ := by
      rw [map_mul]
      group
    have h2 : y1 * ψ' e' * y1⁻¹ * (y1 * ψ' e * y1⁻¹) = y1 * ψ' (e' * e) * y1⁻¹ := by
      rw [map_mul]
      group
    rw [this, h2, hcomm e he e' he']
  obtain ⟨y2, hy2⟩ := exists_diagonalizing_of_commuting_cube_one ω hω hω1 Et hEt3 hEtc
  refine ⟨ι y2 * y1, fun e he => ?_⟩
  obtain ⟨x, hx⟩ := hrange e he
  have hxEt : x ∈ Et := by
    rw [hEtmem, hx]
    exact ⟨ψ' e, ⟨e, he, rfl⟩, rfl⟩
  have hd := hy2 x hxEt
  have htor := phi_diag_mem_torusGroup ι hιx (y2 * x * y2⁻¹) hd
  have hX : (ι y2 * y1 : ↥(adjointGroup .G2 K₂)) * ψ' e * (ι y2 * y1)⁻¹ =
      ι (y2 * x * y2⁻¹) := by
    calc (ι y2 * y1 : ↥(adjointGroup .G2 K₂)) * ψ' e * (ι y2 * y1)⁻¹ =
        ι y2 * (y1 * ψ' e * y1⁻¹) * (ι y2)⁻¹ := by group
      _ = ι (y2 * x * y2⁻¹) := by rw [← hx, map_mul, map_mul, map_inv]
  have hconj : ((ι y2 * y1 : ↥(adjointGroup .G2 K₂)) : ModGL .G2 K₂) * twistEmb g e *
      ((ι y2 * y1 : ↥(adjointGroup .G2 K₂)) : ModGL .G2 K₂)⁻¹ =
        ((ι (y2 * x * y2⁻¹) : ↥(adjointGroup .G2 K₂)) : ModGL .G2 K₂) := by
    have h := congrArg (fun w : ↥(adjointGroup .G2 K₂) => (w : ModGL .G2 K₂)) hX
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, hψ'val] using h
  rw [hconj]
  refine mem_torusTorsion_iff.2 ⟨htor, ?_⟩
  have hc3 : (y2 * x * y2⁻¹) ^ 3 = 1 := by
    have : (y2 * x * y2⁻¹) ^ 3 = y2 * x ^ 3 * y2⁻¹ := conj_pow
    rw [this, hEt3 x hxEt]
    group
  rw [← Subgroup.coe_pow, ← map_pow, hc3, map_one]
  rfl


theorem exists_fixed_conj_planeToTorsion [Finite K]
    (h3 : 3 ∣ Nat.card K + 1) [Finite K₂] (hq2 : Nat.card K₂ = Nat.card K ^ 2)
    (F : ModGL .G2 K₂ →* ModGL .G2 K₂)
    (hFY : ∀ x ∈ adjointGroup .G2 K₂, F x ∈ adjointGroup .G2 K₂)
    (hinv : ∀ y, F (F y) = y)
    (hrd : ∀ c : Fin Tag.G2.rank → K₂ˣ, F (rootDiagUnit .G2 c) =
      rootDiagUnit .G2 (c ^ Nat.card K)⁻¹)
    (hcent : ∀ x ∈ adjointGroup .G2 K₂, (∀ v ∈ torusTorsion K₂ 3, x * v = v * x) →
      x ∈ torusGroup .G2 K₂)
    {g : ModGL .G2 K₂}
    (hΓ : conjEntrywiseImage K g = adjointGroup .G2 K₂ ⊓ F.eqLocus (MonoidHom.id _))
    (E : Subgroup ↥(adjointGroup .G2 K)) [hE : CFSG.IsElementaryAbelian 3 E]
    (hcard : Nat.card E = 3 ^ 2) :
    ∃ y' : ModGL .G2 K₂, y' ∈ adjointGroup .G2 K₂ ∧ F y' = y' ∧
      (E.map (twistEmb g)).map (MulAut.conj y').toMonoidHom = torusTorsion K₂ 3 := by
  classical
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have h3₂ : 3 ∣ Nat.card K₂ - 1 := by
    refine h3.trans ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  have hΓY : conjEntrywiseImage K g ≤ adjointGroup .G2 K₂ := hΓ.le.trans inf_le_left
  obtain ⟨y, hy⟩ := exists_planeImage_conj_le hΓY h3₂ E
  let W : Subgroup (ModGL .G2 K₂) :=
    (E.map (twistEmb g)).map (MulAut.conj (y : ModGL .G2 K₂)).toMonoidHom
  have hWle : W ≤ torusTorsion K₂ 3 := by
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact hy e he
  have hWcard : Nat.card W = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (y : ModGL .G2 K₂)).injective,
      Subgroup.card_map_of_injective (twistEmb_injective (K := K) g), hcard]
  have hTfin : Finite (torusTorsion K₂ 3) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_torusTorsion h3₂]; norm_num)
  have hWeq : W = torusTorsion K₂ 3 :=
    Subgroup.eq_of_le_of_card_ge hWle (by rw [natCard_torusTorsion h3₂, hWcard])
  have hFfix : ∀ x ∈ conjEntrywiseImage K g, F x = x := fun x hx => (hΓ.le hx).2
  have hψΓ : ∀ e ∈ E, twistEmb g e ∈ conjEntrywiseImage K g := fun e _ => by
    rw [← map_twistEmb_top]
    exact Subgroup.mem_map.2 ⟨e, Subgroup.mem_top e, rfl⟩
  have hvfix : ∀ v ∈ torusTorsion K₂ 3, F v = v := by
    intro v hv
    obtain ⟨hvT, hv3⟩ := mem_torusTorsion_iff.1 hv
    obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hvT
    have hc3 : c ^ 3 = 1 := by
      apply rootDiagUnit_injective (τ := .G2) (K := K₂)
      rw [← rootDiagUnit_pow, hv3, rootDiagUnit_one]
    rw [hrd c]
    congr 1
    funext i
    have h3i : (c i) ^ 3 = 1 := by
      have := congrFun hc3 i
      simpa using this
    obtain ⟨m, hm⟩ := h3
    have h1 : (c i) ^ (Nat.card K + 1) = 1 := by
      rw [hm, pow_mul, h3i, one_pow]
    have h2 : (c i) ^ Nat.card K * c i = 1 := by rw [← pow_succ]; exact h1
    simp only [Pi.inv_apply, Pi.pow_apply]
    exact inv_eq_iff_eq_inv.2 (eq_inv_of_mul_eq_one_left h2)
  have hyY : (y : ModGL .G2 K₂) ∈ adjointGroup .G2 K₂ := y.2
  set h : ModGL .G2 K₂ := F (y : ModGL .G2 K₂) * (y : ModGL .G2 K₂)⁻¹ with hh
  have hhY : h ∈ adjointGroup .G2 K₂ := mul_mem (hFY _ hyY) (inv_mem hyY)
  have hhcomm : ∀ v ∈ torusTorsion K₂ 3, h * v = v * h := by
    intro v hv
    have hv0 := hv
    rw [← hWeq] at hv
    obtain ⟨_, ⟨e, he, rfl⟩, hv'⟩ := hv
    have hv'' : v = (y : ModGL .G2 K₂) * twistEmb g e * (y : ModGL .G2 K₂)⁻¹ := hv'.symm
    have e1 : F v = F y * twistEmb g e * (F y)⁻¹ := by
      rw [hv'', map_mul, map_mul, map_inv, hFfix _ (hψΓ e he)]
    have e2 : F y * twistEmb g e = v * F y := by
      have h0 := hvfix v hv0
      rw [e1] at h0
      exact mul_inv_eq_iff_eq_mul.1 h0
    calc h * v = F y * twistEmb g e * (y : ModGL .G2 K₂)⁻¹ := by rw [hh, hv'']; group
      _ = v * F y * (y : ModGL .G2 K₂)⁻¹ := by rw [e2]
      _ = v * h := by rw [hh]; group
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hcent h hhY hhcomm)
  have hFh : F h = h⁻¹ := by
    rw [hh, map_mul, map_inv, hinv]
    simp [mul_inv_rev]
  have haq : ∀ i, (a i) ^ Nat.card K = a i := by
    intro i
    have h1 : F (rootDiagUnit .G2 a) = (rootDiagUnit .G2 a)⁻¹ := by rw [← ha]; exact hFh
    rw [hrd a, rootDiagUnit_inv] at h1
    have h2 := rootDiagUnit_injective h1
    have h3' := congrFun h2 i
    simp only [Pi.inv_apply, Pi.pow_apply, inv_inj] at h3'
    exact h3'
  have hex : ∀ i, ∃ t : K₂ˣ, t ^ (Nat.card K + 1) = a i := fun i =>
    exists_pow_succ_eq_of_pow_eq_self hq2 hq1 (haq i)
  choose t ht using hex
  have htT : rootDiagUnit .G2 t ∈ torusGroup .G2 K₂ := rootDiagUnit_mem_torusGroup_G2 t
  have htY : rootDiagUnit .G2 t ∈ adjointGroup .G2 K₂ :=
    monomialSubgroup_le_adjointGroup' (torusGroup_le_monomialSubgroup htT)
  refine ⟨rootDiagUnit .G2 t * (y : ModGL .G2 K₂), mul_mem htY hyY, ?_, ?_⟩
  · have hFy : F (y : ModGL .G2 K₂) = h * y := by rw [hh]; group
    rw [map_mul, hFy, hrd t, ha, ← mul_assoc, ← rootDiagUnit_mul]
    congr 2
    funext i
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
    rw [← ht i, pow_succ, inv_mul_cancel_left]
  · have hconj : ∀ e ∈ E, (MulAut.conj (rootDiagUnit .G2 t * (y : ModGL .G2 K₂))).toMonoidHom
        (twistEmb g e) = (MulAut.conj (y : ModGL .G2 K₂)).toMonoidHom (twistEmb g e) := by
      intro e he
      have hvT : (y : ModGL .G2 K₂) * twistEmb g e * (y : ModGL .G2 K₂)⁻¹ ∈ torusGroup .G2 K₂ :=
        (mem_torusTorsion_iff.1 (hy e he)).1
      have hcm := (triangular_borel_structure.{0, 0} .G2 K₂).1 _ htT _ hvT
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
      calc rootDiagUnit .G2 t * ↑y * twistEmb g e * (↑y⁻¹ * (rootDiagUnit .G2 t)⁻¹) =
          rootDiagUnit .G2 t * (↑y * twistEmb g e * (y : ModGL .G2 K₂)⁻¹) *
            (rootDiagUnit .G2 t)⁻¹ := by simp [mul_assoc]
        _ = ↑y * twistEmb g e * (y : ModGL .G2 K₂)⁻¹ := by
          rw [hcm]; group
        _ = _ := by simp [mul_assoc]
    rw [← hWeq]
    ext x
    constructor
    · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨_, ⟨e, he, rfl⟩, (hconj e he).symm⟩
    · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨_, ⟨e, he, rfl⟩, hconj e he⟩



theorem exists_g_planeToTorsion [Finite K]
    (h3 : 3 ∣ Nat.card K + 1) [Finite K₂] (hdeg : Module.finrank K K₂ = 2)
    (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K)
    {g z : ModGL .G2 K₂} (hg : g ∈ adjointGroup .G2 K₂) (hzC : z ∈ adjointGroup .G2 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hzN : z ∈ monomialSubgroup .G2 K₂)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hzN⟩ • v = -v)
    (hΓ : conjEntrywiseImage K g = adjointGroup .G2 K₂ ⊓
      (twistedEntrywise z (σ : K₂ →+* K₂)).eqLocus (MonoidHom.id _))
    (hinv : ∀ y, twistedEntrywise z (σ : K₂ →+* K₂) (twistedEntrywise z (σ : K₂ →+* K₂) y) = y)
    (hcent : ∀ x ∈ adjointGroup .G2 K₂, (∀ v ∈ torusTorsion K₂ 3, x * v = v * x) →
      x ∈ torusGroup .G2 K₂)
    (E : Subgroup ↥(adjointGroup .G2 K)) [hE : CFSG.IsElementaryAbelian 3 E]
    (hcard : Nat.card E = 3 ^ 2) :
    ∃ g' : ModGL .G2 K₂, g' ∈ adjointGroup .G2 K₂ ∧
      z = g' * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g')⁻¹ ∧
      E.map (twistEmb g') = torusTorsion K₂ 3 := by
  classical
  obtain ⟨y', hy'Y, hFy', hW⟩ := exists_fixed_conj_planeToTorsion h3
    (natCard_eq_sq_of_finrank_eq_two hdeg) (twistedEntrywise z (σ : K₂ →+* K₂))
    (fun x hx => twistedEntrywise_mem_adjointGroup hzC hx) hinv
    (fun c => twistedEntrywise_rootDiagUnit hzN hw (σ : K₂ →+* K₂) hσ c) hcent hΓ E hcard
  have hy'Γ : y' ∈ conjEntrywiseImage K g := by
    rw [hΓ]
    exact ⟨hy'Y, hFy'⟩
  rw [← map_twistEmb_top] at hy'Γ
  obtain ⟨w, -, hw'⟩ := hy'Γ
  have hy'eq : y' = g * baseChangeGL (algebraMap K K₂) (w : ModGL .G2 K) * g⁻¹ := by
    rw [← hw', twistEmb_apply]
  have hg'Y : g * baseChangeGL (algebraMap K K₂) (w : ModGL .G2 K) ∈ adjointGroup .G2 K₂ := by
    have : g * baseChangeGL (algebraMap K K₂) (w : ModGL .G2 K) = y' * g := by
      rw [hy'eq]
      group
    rw [this]
    exact mul_mem hy'Y hg
  refine ⟨_, hg'Y, ?_, ?_⟩
  · rw [map_mul, entrywise_baseChangeGL_fixed hσ, hzdef]
    group
  · have hcomp : twistEmb (K := K) (g * baseChangeGL (algebraMap K K₂) (w : ModGL .G2 K)) =
        (MulAut.conj y').toMonoidHom.comp (twistEmb (K := K) g) := by
      ext e
      simp only [twistEmb_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, hy'eq]
      group
    rw [hcomp, ← Subgroup.map_map]
    exact hW


end Lang

end CFSG.GH74.GLS.Stage2.Bender.Thm1
