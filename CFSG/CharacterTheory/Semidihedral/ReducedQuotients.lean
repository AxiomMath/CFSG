module

public import CFSG.CharacterTheory.Semidihedral.CoreResidual
public import CFSG.CharacterTheory.Semidihedral.OddCoreQuotient
public import CFSG.CharacterTheory.Semidihedral.CentralQuotients

public section

namespace CFSG.Semidihedral.ReducedQuotients

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.CentralizerResidual
open CFSG.Semidihedral.CoreResidual

variable {H : Type*} [Group H]

@[expose] noncomputable def quotientSubgroupEquiv (N K : Subgroup H) [N.Normal] :
    K ⧸ N.subgroupOf K ≃* K.map (QuotientGroup.mk' N) := by
  let f := (QuotientGroup.mk' N).subgroupMap K
  have hf : N.subgroupOf K = f.ker := by
    ext x
    change (x : H) ∈ N ↔ f x = 1
    constructor
    · intro hx
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := N) (x := (x : H))).mpr hx
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := N) (x := (x : H))).mp
        (congrArg Subtype.val hx)
  exact QuotientGroup.liftEquiv (N.subgroupOf K) ((QuotientGroup.mk' N).subgroupMap_surjective K) hf

theorem quotientSubgroupEquiv_coe (N K : Subgroup H) [N.Normal] (x : K) :
    (quotientSubgroupEquiv N K (QuotientGroup.mk' (N.subgroupOf K) x) : H ⧸ N) =
      QuotientGroup.mk' N (x : H) := rfl

variable [Finite H]

theorem primeResidual_core_eq_subgroupOf (p : ℕ) [Fact p.Prime] :
    pPrimeCore p (primeResidual p H) =
      (pPrimeCore p H).subgroupOf (primeResidual p H) := by
  apply Subgroup.map_injective (primeResidual p H).subtype_injective
  rw [pPrimeCore_primeResidual_map,
    Subgroup.map_subgroupOf_eq_of_le (pPrimeCore_le_primeResidual p)]

@[expose] noncomputable def primeResidualCoreQuotientEquiv (p : ℕ) [Fact p.Prime] :
    primeResidual p H ⧸ pPrimeCore p (primeResidual p H) ≃*
      (primeResidual p H).map (QuotientGroup.mk' (pPrimeCore p H)) :=
  (QuotientGroup.quotientMulEquivOfEq (primeResidual_core_eq_subgroupOf p)).trans
    (quotientSubgroupEquiv (pPrimeCore p H) (primeResidual p H))

theorem primeResidualCoreQuotientEquiv_coe (p : ℕ) [Fact p.Prime]
    (x : primeResidual p H) :
    (primeResidualCoreQuotientEquiv p (QuotientGroup.mk' (pPrimeCore p (primeResidual p H)) x) :
      H ⧸ pPrimeCore p H) = QuotientGroup.mk' (pPrimeCore p H) (x : H) := rfl

@[expose] noncomputable def successiveCentralQuotientEquiv (N : Subgroup H)
    [N.Normal] (t : H) (ht : t ∈ Subgroup.center H) :
    let Z := Subgroup.zpowers t
    let : Z.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr ht)
    let : (N ⊔ Z).Normal := Subgroup.sup_normal N Z
    let : (Subgroup.zpowers (QuotientGroup.mk' N t)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr
        (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N)
          (Subgroup.mem_map_of_mem _ ht)))
    (H ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N t) ≃* H ⧸ (N ⊔ Z) := by
  let Z := Subgroup.zpowers t
  let : Z.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr ht)
  let : (N ⊔ Z).Normal := Subgroup.sup_normal N Z
  let : (Subgroup.zpowers (QuotientGroup.mk' N t)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr
      (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N)
        (Subgroup.mem_map_of_mem _ ht)))
  have hNmap : N.map (QuotientGroup.mk' N) = ⊥ :=
    (Subgroup.map_eq_bot_iff (H := N) (f := QuotientGroup.mk' N)).mpr
      (by rw [QuotientGroup.ker_mk'])
  have hz : (N ⊔ Z).map (QuotientGroup.mk' N) =
      Subgroup.zpowers (QuotientGroup.mk' N t) := by
    rw [Subgroup.map_sup, hNmap, bot_sup_eq, MonoidHom.map_zpowers]
  exact (QuotientGroup.quotientMulEquivOfEq hz.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient N (N ⊔ Z) le_sup_left)

theorem oddCore_and_central_involution_quotient_core (t : H)
    (ht : t ∈ Subgroup.center H) (hto : orderOf t = 2) :
    let Z := Subgroup.zpowers t
    let : Z.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr ht)
    let : (pPrimeCore 2 H ⊔ Z).Normal := Subgroup.sup_normal _ _
    pPrimeCore 2 (H ⧸ (pPrimeCore 2 H ⊔ Z)) = ⊥ := by
  let N := pPrimeCore 2 H
  let q := QuotientGroup.mk' N
  let Z := Subgroup.zpowers t
  let : Z.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr ht)
  let : (N ⊔ Z).Normal := Subgroup.sup_normal _ _
  let Zbar := Subgroup.zpowers (q t)
  have htbar : q t ∈ Subgroup.center (H ⧸ N) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N)
      (Subgroup.mem_map_of_mem _ ht)
  have hZbar : Zbar ≤ Subgroup.center (H ⧸ N) := Subgroup.zpowers_le.mpr htbar
  let : Zbar.Normal := Subgroup.normal_of_le_center hZbar
  have hZp : IsPGroup 2 Z :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto]; norm_num)
  have hZbarp : IsPGroup 2 Zbar := by
    have h := hZp.of_surjective (q.subgroupMap Z) (q.subgroupMap_surjective Z)
    change IsPGroup 2 ((Subgroup.zpowers t).map q) at h
    rw [q.map_zpowers t] at h
    exact h
  have hcore : pPrimeCore 2 ((H ⧸ N) ⧸ Zbar) = ⊥ :=
    OddCoreQuotient.pPrimeCore_quotient_eq_bot_of_central 2 Zbar hZbar hZbarp
      (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  let e := successiveCentralQuotientEquiv N t ht
  have h := pPrimeCore_map_iso 2 e
  rw [hcore, Subgroup.map_bot] at h
  exact h.symm

theorem pSubgroup_disjoint_primeCore (p : ℕ) [Fact p.Prime]
    (P : Subgroup H) (hP : IsPGroup p P) : Disjoint P (pPrimeCore p H) := by
  apply Subgroup.disjoint_of_coprime_natCard
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk]
  exact (pPrimeCore_coprime_card (p := p)).pow_left k

theorem pSubgroup_inf_core_sup (p : ℕ) [Fact p.Prime]
    (P Z : Subgroup H) (hP : IsPGroup p P) (hZ : Z ≤ P) :
    P ⊓ (pPrimeCore p H ⊔ Z) = Z := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hx.2
    have haP : a ∈ P := by
      have heq : a = x * b⁻¹ := by rw [← hab]; simp
      rw [heq]
      exact P.mul_mem hx.1 (P.inv_mem (hZ hb))
    have ha1 : a = 1 := (pSubgroup_disjoint_primeCore p P hP).le_bot ⟨haP, ha⟩
    rw [ha1, one_mul] at hab
    exact hab ▸ hb
  · exact le_inf hZ le_sup_right

theorem pSubgroup_core_sup_subgroupOf (p : ℕ) [Fact p.Prime]
    (P Z : Subgroup H) (hP : IsPGroup p P) (hZ : Z ≤ P) :
    (pPrimeCore p H ⊔ Z).subgroupOf P = Z.subgroupOf P :=
  Subgroup.subgroupOf_inj.mpr
    (by rw [inf_comm, pSubgroup_inf_core_sup p P Z hP hZ, inf_eq_left.mpr hZ])

@[expose] noncomputable def coreCentralQuotientSylowEquiv (p : ℕ) [Fact p.Prime]
    (P : Sylow p H) (Z : Subgroup H) [Z.Normal] (hZ : Z ≤ (P : Subgroup H)) :
    P ⧸ Z.subgroupOf P ≃*
      P.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore p H ⊔ Z)) :=
  (QuotientGroup.quotientMulEquivOfEq
    (pSubgroup_core_sup_subgroupOf p (P : Subgroup H) Z P.isPGroup' hZ).symm).trans
      ((quotientSubgroupEquiv (pPrimeCore p H ⊔ Z) (P : Subgroup H)).trans
        (MulEquiv.subgroupCongr
          (Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore p H ⊔ Z)) P).symm))

theorem coreCentralQuotientSylowEquiv_coe (p : ℕ) [Fact p.Prime]
    (P : Sylow p H) (Z : Subgroup H) [Z.Normal] (hZ : Z ≤ (P : Subgroup H)) (x : P) :
    (coreCentralQuotientSylowEquiv p P Z hZ (QuotientGroup.mk' (Z.subgroupOf P) x) :
      H ⧸ (pPrimeCore p H ⊔ Z)) = QuotientGroup.mk' (pPrimeCore p H ⊔ Z) (x : H) := rfl

@[expose] noncomputable def coreCentralDihedralEquiv (S : Sylow 2 H)
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    DihedralGroup (half n) ≃*
      S.mapSurjective (QuotientGroup.mk'_surjective
        (pPrimeCore 2 H ⊔ CentralQuotients.ambientZ t htc)) :=
  (CentralQuotients.suppliedCenterQuotientEquiv S n hn f t htc ht).trans
    (coreCentralQuotientSylowEquiv 2 S (CentralQuotients.ambientZ t htc)
      (CentralQuotients.ambientZ_le_sylow S t htc ht))

theorem coreCentralDihedralEquiv_rotation (S : Sylow 2 H)
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    (coreCentralDihedralEquiv S n hn f t htc ht (DihedralGroup.r 1) :
      H ⧸ (pPrimeCore 2 H ⊔ CentralQuotients.ambientZ t htc)) =
      QuotientGroup.mk' (pPrimeCore 2 H ⊔ CentralQuotients.ambientZ t htc) (f (r n) : H) := by
  change ((coreCentralQuotientSylowEquiv 2 S (CentralQuotients.ambientZ t htc)
    (CentralQuotients.ambientZ_le_sylow S t htc ht))
    (CentralQuotients.suppliedCenterQuotientEquiv S n hn f t htc ht (DihedralGroup.r 1)) :
      H ⧸ (pPrimeCore 2 H ⊔ CentralQuotients.ambientZ t htc)) = _
  rw [CentralQuotients.suppliedCenterQuotientEquiv_rotation]
  exact coreCentralQuotientSylowEquiv_coe 2 S _ _ (f (r n))

theorem coreCentralDihedralEquiv_reflection (S : Sylow 2 H)
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    (coreCentralDihedralEquiv S n hn f t htc ht (DihedralGroup.sr 0) :
      H ⧸ (pPrimeCore 2 H ⊔ CentralQuotients.ambientZ t htc)) =
      QuotientGroup.mk' (pPrimeCore 2 H ⊔ CentralQuotients.ambientZ t htc) (f (s n) : H) := by
  change ((coreCentralQuotientSylowEquiv 2 S (CentralQuotients.ambientZ t htc)
    (CentralQuotients.ambientZ_le_sylow S t htc ht))
    (CentralQuotients.suppliedCenterQuotientEquiv S n hn f t htc ht (DihedralGroup.sr 0)) :
      H ⧸ (pPrimeCore 2 H ⊔ CentralQuotients.ambientZ t htc)) = _
  rw [CentralQuotients.suppliedCenterQuotientEquiv_reflection]
  exact coreCentralQuotientSylowEquiv_coe 2 S _ _ (f (s n))

theorem nativeQuaternion_half_order (q : ℕ) [NeZero q] :
    orderOf (QuaternionGroup.a (q : ZMod (2 * q))) = 2 := by
  have h := orderOf_pow (QuaternionGroup.xa (0 : ZMod (2 * q))) (n := 2)
  rw [QuaternionGroup.xa_sq, QuaternionGroup.orderOf_xa] at h
  norm_num at h
  exact h

omit [Finite H] in
theorem involution_zpowers_mem_iff (t x : H) (ht : orderOf t = 2) :
    x ∈ Subgroup.zpowers t ↔ x = 1 ∨ x = t := by
  classical
  have hfin : IsOfFinOrder t := orderOf_pos_iff.mp (by omega)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, ht]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, he⟩
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · exact Or.inl (by simpa only [pow_zero] using he.symm)
    · exact Or.inr (by simpa only [pow_one] using he.symm)
  · intro hx
    rcases hx with hx | hx
    · exact ⟨0, by decide, (pow_zero t).trans hx.symm⟩
    · exact ⟨1, by decide, (pow_one t).trans hx.symm⟩

omit [Finite H] in
theorem supplied_quaternion_involution (S : Sylow 2 H)
    (q : ℕ) (hq : 2 ≤ q) (f : QuaternionGroup q ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    f (QuaternionGroup.a (q : ZMod (2 * q))) =
      CentralQuotients.sylowInvolution S t htc ht := by
  let : NeZero q := ⟨by omega⟩
  let tS := CentralQuotients.sylowInvolution S t htc ht
  have hoS : orderOf tS = 2 := by
    change orderOf (CentralQuotients.sylowInvolution S t htc ht) = 2
    rw [← Subgroup.orderOf_coe]
    exact ht
  have hc : f.symm tS ∈ Subgroup.center (QuaternionGroup q) := by
    rw [← Subgroup.map_center_eq f.symm]
    exact ⟨tS, CentralQuotients.sylowInvolution_mem_center S t htc ht, rfl⟩
  rw [CentralQuotients.nativeQuaternion_center q hq] at hc
  have ho : orderOf (f.symm tS) = 2 := (equiv_orderOf f.symm tS).trans hoS
  rcases (involution_zpowers_mem_iff (QuaternionGroup.a (q : ZMod (2 * q)))
    (f.symm tS) (nativeQuaternion_half_order q)).mp hc with h | h
  · rw [h, orderOf_one] at ho
    omega
  · apply f.symm.injective
    simpa only [MulEquiv.symm_apply_apply] using h.symm

omit [Finite H] in
theorem map_nativeQuaternionZ_to_sylowZ (S : Sylow 2 H)
    (q : ℕ) (hq : 2 ≤ q) (f : QuaternionGroup q ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    (CentralQuotients.nativeQuaternionZ q).map f.toMonoidHom =
      CentralQuotients.sylowZ S t htc := by
  rw [CentralQuotients.nativeQuaternionZ, MonoidHom.map_zpowers]
  change Subgroup.zpowers (f (QuaternionGroup.a (q : ZMod (2 * q)))) = _
  rw [supplied_quaternion_involution S q hq f t htc ht,
    CentralQuotients.sylowZ_eq_zpowers S t htc ht]

@[expose] noncomputable def suppliedQuaternionCenterQuotientEquiv (S : Sylow 2 H)
    (q : ℕ) (hq : 2 ≤ q) (f : QuaternionGroup q ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    DihedralGroup q ≃* S ⧸ CentralQuotients.sylowZ S t htc := by
  let : NeZero q := ⟨by omega⟩
  exact (CentralQuotients.nativeQuaternionQuotientEquiv q).trans
    (QuotientGroup.congr (CentralQuotients.nativeQuaternionZ q)
      (CentralQuotients.sylowZ S t htc) f
        (map_nativeQuaternionZ_to_sylowZ S q hq f t htc ht))

omit [Finite H] in
theorem suppliedQuaternionCenterQuotientEquiv_rotation (S : Sylow 2 H)
    (q : ℕ) (hq : 2 ≤ q) (f : QuaternionGroup q ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    suppliedQuaternionCenterQuotientEquiv S q hq f t htc ht (DihedralGroup.r 1) =
      QuotientGroup.mk' (CentralQuotients.sylowZ S t htc) (f (QuaternionGroup.a 1)) := by
  let : NeZero q := ⟨by omega⟩
  rw [suppliedQuaternionCenterQuotientEquiv, MulEquiv.trans_apply,
    CentralQuotients.nativeQuaternionQuotientEquiv_rotation]
  rfl

omit [Finite H] in
theorem suppliedQuaternionCenterQuotientEquiv_reflection (S : Sylow 2 H)
    (q : ℕ) (hq : 2 ≤ q) (f : QuaternionGroup q ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    suppliedQuaternionCenterQuotientEquiv S q hq f t htc ht (DihedralGroup.sr 0) =
      QuotientGroup.mk' (CentralQuotients.sylowZ S t htc) (f (QuaternionGroup.xa 0)) := by
  let : NeZero q := ⟨by omega⟩
  rw [suppliedQuaternionCenterQuotientEquiv, MulEquiv.trans_apply,
    CentralQuotients.nativeQuaternionQuotientEquiv_generator]
  rfl

@[expose] noncomputable def coreCentralQuaternionDihedralEquiv (S : Sylow 2 H)
    (q : ℕ) (hq : 2 ≤ q) (f : QuaternionGroup q ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    DihedralGroup q ≃*
      S.mapSurjective (QuotientGroup.mk'_surjective
        (pPrimeCore 2 H ⊔ CentralQuotients.ambientZ t htc)) :=
  (suppliedQuaternionCenterQuotientEquiv S q hq f t htc ht).trans
    (coreCentralQuotientSylowEquiv 2 S (CentralQuotients.ambientZ t htc)
      (CentralQuotients.ambientZ_le_sylow S t htc ht))

theorem coreCentralQuaternionDihedralEquiv_rotation (S : Sylow 2 H)
    (q : ℕ) (hq : 2 ≤ q) (f : QuaternionGroup q ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    (coreCentralQuaternionDihedralEquiv S q hq f t htc ht (DihedralGroup.r 1) :
      H ⧸ (pPrimeCore 2 H ⊔ CentralQuotients.ambientZ t htc)) =
      QuotientGroup.mk' (pPrimeCore 2 H ⊔ CentralQuotients.ambientZ t htc)
        (f (QuaternionGroup.a 1) : H) := by
  change ((coreCentralQuotientSylowEquiv 2 S (CentralQuotients.ambientZ t htc)
    (CentralQuotients.ambientZ_le_sylow S t htc ht))
    (suppliedQuaternionCenterQuotientEquiv S q hq f t htc ht (DihedralGroup.r 1)) :
      H ⧸ (pPrimeCore 2 H ⊔ CentralQuotients.ambientZ t htc)) = _
  rw [suppliedQuaternionCenterQuotientEquiv_rotation]
  exact coreCentralQuotientSylowEquiv_coe 2 S _ _ (f (QuaternionGroup.a 1))

theorem coreCentralQuaternionDihedralEquiv_reflection (S : Sylow 2 H)
    (q : ℕ) (hq : 2 ≤ q) (f : QuaternionGroup q ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    (coreCentralQuaternionDihedralEquiv S q hq f t htc ht (DihedralGroup.sr 0) :
      H ⧸ (pPrimeCore 2 H ⊔ CentralQuotients.ambientZ t htc)) =
      QuotientGroup.mk' (pPrimeCore 2 H ⊔ CentralQuotients.ambientZ t htc)
        (f (QuaternionGroup.xa 0) : H) := by
  change ((coreCentralQuotientSylowEquiv 2 S (CentralQuotients.ambientZ t htc)
    (CentralQuotients.ambientZ_le_sylow S t htc ht))
    (suppliedQuaternionCenterQuotientEquiv S q hq f t htc ht (DihedralGroup.sr 0)) :
      H ⧸ (pPrimeCore 2 H ⊔ CentralQuotients.ambientZ t htc)) = _
  rw [suppliedQuaternionCenterQuotientEquiv_reflection]
  exact coreCentralQuotientSylowEquiv_coe 2 S _ _ (f (QuaternionGroup.xa 0))

variable {G : Type*} [Group G] [Finite G]

@[expose] def centralizerZ (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : Subgroup (involutionCentralizer n S f) :=
  Subgroup.zpowers (centralInvolution n S f)

instance centralizerZ_normal (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : (centralizerZ n S f).Normal :=
  Subgroup.normal_of_le_center
    (Subgroup.zpowers_le.mpr (centralInvolution_mem_center n S f))

@[expose] def centralizerFullKernel (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : Subgroup (involutionCentralizer n S f) :=
  pPrimeCore 2 (involutionCentralizer n S f) ⊔ centralizerZ n S f

instance centralizerFullKernel_normal (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : (centralizerFullKernel n S f).Normal :=
  Subgroup.sup_normal _ _

theorem centralizerFullKernel_le_residual (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    centralizerFullKernel n S f ≤ oddResidual n S f :=
  sup_le (centralizerCore_le_residual n S f)
    (Subgroup.zpowers_le.mpr (centralInvolution_mem_oddResidual n hn S f hG))

@[expose] def reducedCentralizerSylow (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    Sylow 2 (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) :=
  (centralizerSylow n hn S f).mapSurjective
    (QuotientGroup.mk'_surjective (centralizerFullKernel n S f))

@[expose] noncomputable def reducedCentralizerDihedralEquiv (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    DihedralGroup (half n) ≃* reducedCentralizerSylow n hn S f :=
  coreCentralDihedralEquiv (centralizerSylow n hn S f) n hn
    (centralizerCoordinates n hn S f) (centralInvolution n S f)
    (centralInvolution_mem_center n S f) (centralInvolution_order n hn S f)

theorem reducedCentralizerDihedralEquiv_rotation (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    (reducedCentralizerDihedralEquiv n hn S f (DihedralGroup.r 1) :
      involutionCentralizer n S f ⧸ centralizerFullKernel n S f) =
      QuotientGroup.mk' (centralizerFullKernel n S f)
        (centralizerCoordinates n hn S f (r n) : involutionCentralizer n S f) :=
  coreCentralDihedralEquiv_rotation _ n hn _ _ _ _

theorem reducedCentralizerDihedralEquiv_reflection (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    (reducedCentralizerDihedralEquiv n hn S f (DihedralGroup.sr 0) :
      involutionCentralizer n S f ⧸ centralizerFullKernel n S f) =
      QuotientGroup.mk' (centralizerFullKernel n S f)
        (centralizerCoordinates n hn S f (s n) : involutionCentralizer n S f) :=
  coreCentralDihedralEquiv_reflection _ n hn _ _ _ _

theorem reducedCentralizerSylow_card (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    Nat.card (reducedCentralizerSylow n hn S f) = 2 ^ (n - 1) := by
  rw [← Nat.card_congr (reducedCentralizerDihedralEquiv n hn S f).toEquiv,
    DihedralGroup.nat_card]
  exact (modulus_eq_two_mul_half (by omega)).symm

@[expose] def reducedResidual (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    Subgroup (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) :=
  (oddResidual n S f).map (QuotientGroup.mk' (centralizerFullKernel n S f))

instance reducedResidual_normal (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : (reducedResidual n S f).Normal :=
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

theorem reducedResidual_index (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) : (reducedResidual n S f).index = 2 := by
  have hk : (QuotientGroup.mk' (centralizerFullKernel n S f)).ker ≤ oddResidual n S f := by
    simpa only [QuotientGroup.ker_mk'] using centralizerFullKernel_le_residual n hn S f hG
  exact (Subgroup.index_map_eq (oddResidual n S f)
    (QuotientGroup.mk'_surjective _) hk).trans (oddResidual_index n hn S f hG)

theorem reducedCentralizer_oddCore_eq_bot (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    pPrimeCore 2 (involutionCentralizer n S f ⧸ centralizerFullKernel n S f) = ⊥ :=
  oddCore_and_central_involution_quotient_core (centralInvolution n S f)
    (centralInvolution_mem_center n S f) (centralInvolution_order n hn S f)

theorem centralizerZ_subgroupOf_residual (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    (centralizerZ n S f).subgroupOf (oddResidual n S f) =
      Subgroup.zpowers (residualInvolution n hn S f hG) := by
  apply Subgroup.map_injective (oddResidual n S f).subtype_injective
  rw [centralizerZ, Subgroup.map_subgroupOf_eq_of_le
    (Subgroup.zpowers_le.mpr (centralInvolution_mem_oddResidual n hn S f hG)),
    MonoidHom.map_zpowers]
  rfl

theorem centralizerFullKernel_subgroupOf_residual (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    (centralizerFullKernel n S f).subgroupOf (oddResidual n S f) =
      pPrimeCore 2 (oddResidual n S f) ⊔ Subgroup.zpowers (residualInvolution n hn S f hG) := by
  have hz : centralizerZ n S f ≤ oddResidual n S f :=
    Subgroup.zpowers_le.mpr (centralInvolution_mem_oddResidual n hn S f hG)
  have hcore : (pPrimeCore 2 (involutionCentralizer n S f)).subgroupOf (oddResidual n S f) =
      pPrimeCore 2 (oddResidual n S f) := (primeResidual_core_eq_subgroupOf 2).symm
  rw [centralizerFullKernel, Subgroup.subgroupOf_sup
    (centralizerCore_le_residual n S f) hz, hcore,
    centralizerZ_subgroupOf_residual n hn S f hG]

theorem reducedResidual_oddCore_eq_bot (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) : pPrimeCore 2 (reducedResidual n S f) = ⊥ := by
  let K := oddResidual n S f
  let z := residualInvolution n hn S f hG
  have hz : z ∈ Subgroup.center K := residualInvolution_mem_center n hn S f hG
  let : (Subgroup.zpowers z).Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz)
  let : (pPrimeCore 2 K ⊔ Subgroup.zpowers z).Normal := Subgroup.sup_normal _ _
  let e := (QuotientGroup.quotientMulEquivOfEq
    (centralizerFullKernel_subgroupOf_residual n hn S f hG).symm).trans
      (quotientSubgroupEquiv (centralizerFullKernel n S f) K)
  have h := pPrimeCore_map_iso 2 e
  have hcore : pPrimeCore 2 (K ⧸ (pPrimeCore 2 K ⊔ Subgroup.zpowers z)) = ⊥ :=
    oddCore_and_central_involution_quotient_core z hz (residualInvolution_order n hn S f hG)
  rw [hcore, Subgroup.map_bot] at h
  exact h.symm

@[expose] noncomputable def reducedResidualQuotientEquiv (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    oddResidual n S f ⧸ (centralizerFullKernel n S f).subgroupOf (oddResidual n S f) ≃*
      reducedResidual n S f :=
  quotientSubgroupEquiv _ _

omit [Finite G] in
theorem reducedResidualQuotientEquiv_coe (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (x : oddResidual n S f) :
    (reducedResidualQuotientEquiv n S f
      (QuotientGroup.mk' ((centralizerFullKernel n S f).subgroupOf (oddResidual n S f)) x) :
      involutionCentralizer n S f ⧸ centralizerFullKernel n S f) =
    QuotientGroup.mk' (centralizerFullKernel n S f) (x : involutionCentralizer n S f) := rfl

abbrev residualFullKernel (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) : Subgroup (oddResidual n S f) :=
  pPrimeCore 2 (oddResidual n S f) ⊔
    CentralQuotients.ambientZ (residualInvolution n hn S f hG)
      (residualInvolution_mem_center n hn S f hG)

instance residualFullKernel_normal (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) : (residualFullKernel n hn S f hG).Normal :=
  Subgroup.sup_normal _ _

theorem residualFullKernel_eq_subgroupOf (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    residualFullKernel n hn S f hG =
      (centralizerFullKernel n S f).subgroupOf (oddResidual n S f) :=
  (centralizerFullKernel_subgroupOf_residual n hn S f hG).symm

@[expose] noncomputable def residualCentralQuotientEquiv (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    oddResidual n S f ⧸ residualFullKernel n hn S f hG ≃* reducedResidual n S f :=
  (QuotientGroup.quotientMulEquivOfEq (M := residualFullKernel n hn S f hG)
    (N := (centralizerFullKernel n S f).subgroupOf (oddResidual n S f))
    (residualFullKernel_eq_subgroupOf n hn S f hG)).trans
      (reducedResidualQuotientEquiv n S f)

theorem residualCentralQuotientEquiv_coe (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) (x : oddResidual n S f) :
    (residualCentralQuotientEquiv n hn S f hG
      (QuotientGroup.mk' (residualFullKernel n hn S f hG) x) :
      involutionCentralizer n S f ⧸ centralizerFullKernel n S f) =
      QuotientGroup.mk' (centralizerFullKernel n S f) (x : involutionCentralizer n S f) := by
  change ((reducedResidualQuotientEquiv n S f)
    ((QuotientGroup.quotientMulEquivOfEq
      (M := residualFullKernel n hn S f hG)
      (N := (centralizerFullKernel n S f).subgroupOf (oddResidual n S f))
      (residualFullKernel_eq_subgroupOf n hn S f hG))
        (QuotientGroup.mk x)) :
    involutionCentralizer n S f ⧸ centralizerFullKernel n S f) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  exact reducedResidualQuotientEquiv_coe n S f x

@[expose] noncomputable def sylowEquivMap {p : ℕ} [Fact p.Prime]
    {E : Type*} [Group E] [Finite E] {E' : Type*} [Group E']
    (P : Sylow p E) (e : E ≃* E') :
    P ≃* P.mapSurjective (f := e.toMonoidHom) e.surjective :=
  (e.subgroupMap (P : Subgroup E)).trans
    (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective P).symm)

theorem sylowEquivMap_coe {p : ℕ} [Fact p.Prime]
    {E : Type*} [Group E] [Finite E] {E' : Type*} [Group E']
    (P : Sylow p E) (e : E ≃* E') (x : P) :
    (sylowEquivMap P e x : E') = e x := rfl

@[expose] noncomputable def reducedResidualSylow (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) : Sylow 2 (reducedResidual n S f) :=
  ((residualSylow n hn S f hG).mapSurjective
    (QuotientGroup.mk'_surjective (residualFullKernel n hn S f hG))).mapSurjective
      (f := (residualCentralQuotientEquiv n hn S f hG).toMonoidHom)
      (residualCentralQuotientEquiv n hn S f hG).surjective

theorem residualQuaternionParameter_ge_two (n : ℕ) (hn : 4 ≤ n) : 2 ≤ 2 ^ (n - 3) := by
  have h := Nat.pow_le_pow_right (n := 2) (by omega) (show 1 ≤ n - 3 by omega)
  simpa only [pow_one] using h

@[expose] noncomputable def reducedResidualDihedralEquiv (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    DihedralGroup (2 ^ (n - 3)) ≃* reducedResidualSylow n hn S f hG :=
  (coreCentralQuaternionDihedralEquiv (residualSylow n hn S f hG)
    (2 ^ (n - 3)) (residualQuaternionParameter_ge_two n hn)
    (residualQuaternionEquiv n hn S f hG) (residualInvolution n hn S f hG)
    (residualInvolution_mem_center n hn S f hG) (residualInvolution_order n hn S f hG)).trans
      (sylowEquivMap _ (residualCentralQuotientEquiv n hn S f hG))

theorem reducedResidualDihedralEquiv_rotation (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    ((reducedResidualDihedralEquiv n hn S f hG (DihedralGroup.r 1) :
      reducedResidual n S f) : involutionCentralizer n S f ⧸ centralizerFullKernel n S f) =
      QuotientGroup.mk' (centralizerFullKernel n S f)
        ((centralizerCoordinates n hn S f (r n) : involutionCentralizer n S f) ^ 2) := by
  change (residualCentralQuotientEquiv n hn S f hG
    (coreCentralQuaternionDihedralEquiv (residualSylow n hn S f hG)
      (2 ^ (n - 3)) (residualQuaternionParameter_ge_two n hn)
      (residualQuaternionEquiv n hn S f hG) (residualInvolution n hn S f hG)
      (residualInvolution_mem_center n hn S f hG) (residualInvolution_order n hn S f hG)
      (DihedralGroup.r 1) : oddResidual n S f ⧸ residualFullKernel n hn S f hG) :
    involutionCentralizer n S f ⧸ centralizerFullKernel n S f) = _
  rw [coreCentralQuaternionDihedralEquiv_rotation, residualCentralQuotientEquiv_coe,
    residualQuaternionEquiv_coe, centralizerQuaternionEquiv_rotation]

theorem reducedResidualDihedralEquiv_reflection (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    ((reducedResidualDihedralEquiv n hn S f hG (DihedralGroup.sr 0) :
      reducedResidual n S f) : involutionCentralizer n S f ⧸ centralizerFullKernel n S f) =
      QuotientGroup.mk' (centralizerFullKernel n S f)
        ((centralizerCoordinates n hn S f (r n) : involutionCentralizer n S f) *
          (centralizerCoordinates n hn S f (s n) : involutionCentralizer n S f)) := by
  change (residualCentralQuotientEquiv n hn S f hG
    (coreCentralQuaternionDihedralEquiv (residualSylow n hn S f hG)
      (2 ^ (n - 3)) (residualQuaternionParameter_ge_two n hn)
      (residualQuaternionEquiv n hn S f hG) (residualInvolution n hn S f hG)
      (residualInvolution_mem_center n hn S f hG) (residualInvolution_order n hn S f hG)
      (DihedralGroup.sr 0) : oddResidual n S f ⧸ residualFullKernel n hn S f hG) :
    involutionCentralizer n S f ⧸ centralizerFullKernel n S f) = _
  rw [coreCentralQuaternionDihedralEquiv_reflection, residualCentralQuotientEquiv_coe,
    residualQuaternionEquiv_coe, centralizerQuaternionEquiv_generator]

theorem reducedResidualSylow_card (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    Nat.card (reducedResidualSylow n hn S f hG) = 2 ^ (n - 2) := by
  rw [← Nat.card_congr (reducedResidualDihedralEquiv n hn S f hG).toEquiv,
    DihedralGroup.nat_card, show n - 2 = (n - 3) + 1 by omega, pow_succ]
  omega

theorem every_reducedCentralizerSylow_dihedral (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (P : Sylow 2 (involutionCentralizer n S f ⧸ centralizerFullKernel n S f)) :
    Nonempty (P ≃* DihedralGroup (2 ^ (n - 2))) :=
  ⟨(P.equiv (reducedCentralizerSylow n hn S f)).trans
    (reducedCentralizerDihedralEquiv n hn S f).symm⟩

theorem every_reducedResidualSylow_dihedral (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) (P : Sylow 2 (reducedResidual n S f)) :
    Nonempty (P ≃* DihedralGroup (2 ^ (n - 3))) :=
  ⟨(P.equiv (reducedResidualSylow n hn S f hG)).trans
    (reducedResidualDihedralEquiv n hn S f hG).symm⟩

omit [Finite G] in
theorem reducedResidual_hom_eq_one (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) {P : Type*} [Group P]
    (hP : IsPGroup 2 P) (φ : reducedResidual n S f →* P) : φ = 1 := by
  let q := (QuotientGroup.mk' (centralizerFullKernel n S f)).subgroupMap (oddResidual n S f)
  have h := oddResidual_hom_eq_one n S f hP (φ.comp q)
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := (QuotientGroup.mk' (centralizerFullKernel n S f)).subgroupMap_surjective
    (oddResidual n S f) x
  exact DFunLike.congr_fun h y

theorem every_residualCoreQuotientSylow_quaternion (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2)
    (P : Sylow 2 (oddResidual n S f ⧸ pPrimeCore 2 (oddResidual n S f))) :
    Nonempty (P ≃* QuaternionGroup (2 ^ (n - 3))) :=
  ⟨(P.equiv ((residualSylow n hn S f hG).mapSurjective
    (QuotientGroup.mk'_surjective (pPrimeCore 2 (oddResidual n S f))))).trans
      (residualCoreQuotientQuaternionEquiv n hn S f hG).symm⟩

@[expose] def OddCoreFreeQuotientData (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) : Prop :=
  let C := involutionCentralizer n S f
  let K := oddResidual n S f
  let N := pPrimeCore 2 C
  let Z := centralizerZ n S f
  let Γ := C ⧸ centralizerFullKernel n S f
  let J := reducedResidual n S f
  K = Subgroup.closure {x : C | Odd (orderOf x)} ∧
  K.Characteristic ∧ N ≤ K ∧ N.subgroupOf K = pPrimeCore 2 K ∧
  Disjoint N Z ∧ centralizerFullKernel n S f = N ⊔ Z ∧
  (∀ x : K ⧸ pPrimeCore 2 K,
    orderOf x = 2 ↔ x = QuotientGroup.mk' (pPrimeCore 2 K) (residualInvolution n hn S f hG)) ∧
  (∀ P : Sylow 2 (K ⧸ pPrimeCore 2 K),
    Nonempty (P ≃* QuaternionGroup (2 ^ (n - 3)))) ∧
  Nonempty (K ⧸ (centralizerFullKernel n S f).subgroupOf K ≃* J) ∧
  J.Normal ∧ pPrimeCore 2 Γ = ⊥ ∧ pPrimeCore 2 J = ⊥ ∧ J.index = 2 ∧
  (∀ (A : Type*) [Group A] [Finite A], IsPGroup 2 A → ∀ φ : J →* A, φ = 1) ∧
  (∀ P : Sylow 2 Γ,
    Nonempty (P ≃* DihedralGroup (2 ^ (n - 2))) ∧ Nat.card P = 2 ^ (n - 1)) ∧
  (∀ P : Sylow 2 J,
    Nonempty (P ≃* DihedralGroup (2 ^ (n - 3))) ∧ Nat.card P = 2 ^ (n - 2))

theorem centered_oddCore_free_dihedral_quotients (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) : OddCoreFreeQuotientData n hn S f hG := by
  refine ⟨oddResidual_eq_odd_order_closure n S f, oddResidual_characteristic n S f,
    centralizerCore_le_residual n S f, (primeResidual_core_eq_subgroupOf 2).symm,
    centralizerCore_disjoint_involution n hn S f, rfl,
    residualCoreQuotient_involution_iff n hn S f hG,
    every_residualCoreQuotientSylow_quaternion n hn S f hG,
    ⟨reducedResidualQuotientEquiv n S f⟩, inferInstance,
    reducedCentralizer_oddCore_eq_bot n hn S f, reducedResidual_oddCore_eq_bot n hn S f hG,
    reducedResidual_index n hn S f hG, ?_, ?_, ?_⟩
  · intro A _ _ hA φ
    exact reducedResidual_hom_eq_one n S f hA φ
  · intro P
    exact ⟨every_reducedCentralizerSylow_dihedral n hn S f P,
      (Nat.card_congr (P.equiv (reducedCentralizerSylow n hn S f)).toEquiv).trans
        (reducedCentralizerSylow_card n hn S f)⟩
  · intro P
    exact ⟨every_reducedResidualSylow_dihedral n hn S f hG P,
      (Nat.card_congr (P.equiv (reducedResidualSylow n hn S f hG)).toEquiv).trans
        (reducedResidualSylow_card n hn S f hG)⟩

theorem involution_centralizer_oddCore_free_dihedral_quotients (n : ℕ) (hn : 4 ≤ n)
    (S₀ : Sylow 2 G) (f₀ : SemidihedralGroup n ≃* S₀)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    ∀ t : G, orderOf t = 2 →
      (∃ (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S), centeredInvolution n S f = t) ∧
      (∀ (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S), centeredInvolution n S f = t →
        involutionCentralizer n S f = Subgroup.centralizer {t} ∧
        (centralInvolution n S f : G) = t ∧ OddCoreFreeQuotientData n hn S f hG) := by
  intro t ht
  obtain ⟨S, f, hz, _⟩ :=
    (InvolutionFusion.involution_centered_sylow_existence n hn S₀ f₀ hG t ht).2
  refine ⟨⟨S, f, hz⟩, ?_⟩
  intro S f hz
  refine ⟨?_, hz, centered_oddCore_free_dihedral_quotients n hn S f hG⟩
  change Subgroup.centralizer {centeredInvolution n S f} = Subgroup.centralizer {t}
  rw [hz]

end CFSG.Semidihedral.ReducedQuotients
