module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.ComponentClassification.CentralCover

open Subgroup

variable {H : Type*} [Group H] {L : Subgroup H} {Q : Type*} [Group Q]

private theorem mem_fixedSubgroup_iff {α : MulAut Q} {q : Q} :
    q ∈ FixedCommutingProduct.fixedSubgroup α ↔ α q = q :=
  Iff.rfl

section Action

@[expose] noncomputable def quotientEquivOfKerEqCenter (π : L →* Q) (hπ : Function.Surjective π)
    (hker : π.ker = center L) : L ⧸ center L ≃* Q :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)

noncomputable def fullAction [L.Normal] (π : L →* Q) (hπ : Function.Surjective π)
    (hker : π.ker = center L) : H →* MulAut Q :=
  (MulAut.congr (quotientEquivOfKerEqCenter π hπ hker)).toMonoidHom.comp
    ((PerfectAutomorphisms.centerQuotientHom L).comp MulAut.conjNormal)

variable (π : L →* Q) (hπ : Function.Surjective π) (hker : π.ker = center L)

theorem quotientEquivOfKerEqCenter_mk (l : L) :
    quotientEquivOfKerEqCenter π hπ hker (QuotientGroup.mk' (center L) l) = π l :=
  rfl

variable [L.Normal]

theorem fullAction_apply (h : H) (l : L) :
    fullAction π hπ hker h (π l) = π (MulAut.conjNormal h l) := by
  have hsymm : (quotientEquivOfKerEqCenter π hπ hker).symm (π l) =
      QuotientGroup.mk' (center L) l := by
    rw [MulEquiv.symm_apply_eq, quotientEquivOfKerEqCenter_mk]
  change quotientEquivOfKerEqCenter π hπ hker (PerfectAutomorphisms.onCenterQuotient
    (MulAut.conjNormal h) ((quotientEquivOfKerEqCenter π hπ hker).symm (π l))) = _
  rw [hsymm, PerfectAutomorphisms.onCenterQuotient_apply_mk, quotientEquivOfKerEqCenter_mk]

theorem fullAction_unique (θ : H →* MulAut Q)
    (hθ : ∀ (h : H) (l : L), θ h (π l) = π (MulAut.conjNormal h l)) :
    θ = fullAction π hπ hker := by
  ext h q
  obtain ⟨l, rfl⟩ := hπ q
  rw [hθ, fullAction_apply]

theorem fullAction_coe (l : L) : fullAction π hπ hker (l : H) = MulAut.conj (π l) := by
  ext q
  obtain ⟨m, rfl⟩ := hπ q
  rw [fullAction_apply, MulAut.conjNormal_val, MulAut.conj_apply, MulAut.conj_apply, map_mul,
    map_mul, map_inv]

theorem mem_ker_fullAction_iff [Group.IsPerfect L] (h : H) :
    h ∈ (fullAction π hπ hker).ker ↔ h ∈ centralizer (L : Set H) := by
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  change MulAut.congr (quotientEquivOfKerEqCenter π hπ hker)
    (PerfectAutomorphisms.centerQuotientHom L (MulAut.conjNormal h)) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff,
    map_eq_one_iff _ (PerfectAutomorphisms.centerQuotientHom_injective L)]
  constructor
  · intro h1 x hx
    have hval := congrArg (fun σ : MulAut L => ((σ ⟨x, hx⟩ : L) : H)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at hval
    calc x * h = h * x * h⁻¹ * h := by rw [hval]
      _ = h * x := by group
  · intro h1
    ext x
    rw [MulAut.conjNormal_apply, MulAut.one_apply, ← h1 x x.2, mul_inv_cancel_right]

theorem ker_fullAction [Group.IsPerfect L] :
    (fullAction π hπ hker).ker = centralizer (L : Set H) := by
  ext h
  exact mem_ker_fullAction_iff π hπ hker h

theorem comap_inner_fullAction [Group.IsPerfect L] (hCL : centralizer (L : Set H) ≤ L) :
    (OuterAutomorphisms.inner Q).comap (fullAction π hπ hker) = L := by
  apply le_antisymm
  · intro h hh
    obtain ⟨q, hq⟩ := hh
    obtain ⟨l, rfl⟩ := hπ q
    have hk : h * (l : H)⁻¹ ∈ (fullAction π hπ hker).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, fullAction_coe, hq, mul_inv_cancel]
    rw [ker_fullAction] at hk
    simpa using L.mul_mem (hCL hk) l.2
  · intro l hl
    exact ⟨π ⟨l, hl⟩, (fullAction_coe π hπ hker ⟨l, hl⟩).symm⟩

theorem fullAction_notMem_inner [Group.IsPerfect L] (hCL : centralizer (L : Set H) ≤ L)
    {p : H} (hpL : p ∉ L) : fullAction π hπ hker p ∉ OuterAutomorphisms.inner Q := by
  intro hp
  apply hpL
  rw [← comap_inner_fullAction π hπ hker hCL]
  exact hp

theorem orderOf_fullAction [Group.IsPerfect L] (hCL : centralizer (L : Set H) ≤ L) {p : H}
    (hpL : p ∉ L) (hp : orderOf p = 2) : orderOf (fullAction π hπ hker p) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, ← hp, pow_orderOf_eq_one, map_one]
  · intro h1
    apply fullAction_notMem_inner π hπ hker hCL hpL
    rw [h1]
    exact one_mem _

end Action

section Obstruction

theorem coe_mem_center_of_center_eq_zpowers [L.Normal] {t : L} (hZ : center L = zpowers t)
    (ht : t ^ 2 = 1) : (t : H) ∈ center H := by
  rw [mem_center_iff]
  intro h
  have htZ : t ∈ center L := by rw [hZ]; exact mem_zpowers t
  have hσ : MulAut.conjNormal h t ∈ center L := by
    rw [mem_center_iff]
    intro m
    obtain ⟨m', rfl⟩ := (MulAut.conjNormal h).surjective m
    rw [← map_mul, ← map_mul, mem_center_iff.mp htZ m']
  rw [hZ, mem_zpowers_iff] at hσ
  obtain ⟨k, hk⟩ := hσ
  rw [zpow_eq_zpow_emod k (n := 2) (by rw [zpow_ofNat, ht])] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero] at hk
    have ht1 : t = 1 := (MulAut.conjNormal h).injective (by rw [← hk, map_one])
    rw [ht1, OneMemClass.coe_one, mul_one, one_mul]
  · rw [h1, zpow_one] at hk
    have hval := congrArg Subtype.val hk
    rw [MulAut.conjNormal_apply] at hval
    calc h * (t : H) = h * t * h⁻¹ * h := by group
      _ = t * h := by rw [← hval]

private theorem displacement_mem_zpowers [L.Normal] (π : L →* Q) {t : L}
    (hkert : π.ker = zpowers t) {p : H} {l : L} (hl : π (MulAut.conjNormal p l) = π l) :
    (l : H)⁻¹ * p * l * p⁻¹ ∈ zpowers (t : H) := by
  have hmem : l⁻¹ * MulAut.conjNormal p l ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hl, inv_mul_cancel]
  rw [hkert] at hmem
  have hmap := mem_map_of_mem L.subtype hmem
  rw [MonoidHom.map_zpowers] at hmap
  simpa [mul_assoc] using hmap

private theorem map_conjNormal_eq_of_displacement_mem [L.Normal] (π : L →* Q) {t : L}
    (hkert : π.ker = zpowers t) {p : H} {l : L}
    (hl : (l : H)⁻¹ * p * l * p⁻¹ ∈ zpowers (t : H)) :
    π (MulAut.conjNormal p l) = π l := by
  have hmem : l⁻¹ * MulAut.conjNormal p l ∈ zpowers t := by
    rw [← mem_map_iff_mem L.subtype_injective, MonoidHom.map_zpowers]
    simpa [mul_assoc] using hl
  rw [← hkert, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hmem
  exact hmem.symm

private theorem displacement_eq_of_map_eq (π : L →* Q) {t : L} (hkert : π.ker = zpowers t)
    (htH : (t : H) ∈ center H) (p : H) {l m : L} (hlm : π l = π m) :
    (l : H)⁻¹ * p * l * p⁻¹ = (m : H)⁻¹ * p * m * p⁻¹ := by
  have hz : l⁻¹ * m ∈ zpowers t := by
    rw [← hkert, MonoidHom.mem_ker, map_mul, map_inv, hlm, inv_mul_cancel]
  have hzH : ((l⁻¹ * m : L) : H) ∈ center H := by
    apply (zpowers_le (G := H)).mpr htH
    have hmap := mem_map_of_mem L.subtype hz
    rwa [MonoidHom.map_zpowers] at hmap
  set z : H := ((l⁻¹ * m : L) : H) with hzdef
  have hm : (m : H) = l * z := by simp [hzdef]
  have hzc := mem_center_iff.mp hzH
  have hpz : p * z * p⁻¹ = z := by rw [hzc p, mul_inv_cancel_right]
  rw [hm]
  symm
  calc ((l : H) * z)⁻¹ * p * (l * z) * p⁻¹
      = z⁻¹ * (((l : H)⁻¹ * p * l * p⁻¹) * (p * z * p⁻¹)) := by group
    _ = (l : H)⁻¹ * p * l * p⁻¹ := by rw [hpz, hzc, inv_mul_cancel_left]

private theorem displacement_mul_of_mem_center {p : H} (l m : L)
    (hl : (l : H)⁻¹ * p * l * p⁻¹ ∈ center H) :
    ((l * m : L) : H)⁻¹ * p * (l * m : L) * p⁻¹ =
      ((l : H)⁻¹ * p * l * p⁻¹) * ((m : H)⁻¹ * p * m * p⁻¹) := by
  set u : H := (l : H)⁻¹ * p * l * p⁻¹ with hudef
  have hu := mem_center_iff.mp hl
  have hlpl : (l : H)⁻¹ * p * l = u * p := by rw [hudef]; group
  calc ((l * m : L) : H)⁻¹ * p * (l * m : L) * p⁻¹
      = (m : H)⁻¹ * ((l : H)⁻¹ * p * l) * m * p⁻¹ := by rw [Subgroup.coe_mul]; group
    _ = ((m : H)⁻¹ * u) * p * m * p⁻¹ := by rw [hlpl]; group
    _ = (u * (m : H)⁻¹) * p * m * p⁻¹ := by rw [hu]
    _ = u * ((m : H)⁻¹ * p * m * p⁻¹) := by group

noncomputable def fixedLiftObstruction [L.Normal] (π : L →* Q)
    (hπ : Function.Surjective π) {t : L} (hkert : π.ker = zpowers t)
    (htH : (t : H) ∈ center H) (p : H) (α : MulAut Q)
    (hα : ∀ l : L, α (π l) = π (MulAut.conjNormal p l)) :
    FixedCommutingProduct.fixedSubgroup α →* zpowers (t : H) where
  toFun q := ⟨((Function.surjInv hπ q : L) : H)⁻¹ * p * (Function.surjInv hπ q : L) * p⁻¹,
    displacement_mem_zpowers π hkert (by rw [← hα, Function.surjInv_eq hπ]; exact q.2)⟩
  map_one' := by
    apply Subtype.ext
    dsimp only
    rw [displacement_eq_of_map_eq π hkert htH p (m := 1)
      (by rw [Function.surjInv_eq hπ, map_one, OneMemClass.coe_one])]
    simp
  map_mul' q r := by
    apply Subtype.ext
    have hmem : ((Function.surjInv hπ q : L) : H)⁻¹ * p * (Function.surjInv hπ q : L) * p⁻¹ ∈
        center H :=
      (zpowers_le (G := H)).mpr htH (displacement_mem_zpowers π hkert
        (by rw [← hα, Function.surjInv_eq hπ]; exact q.2))
    simp only [Subgroup.coe_mul]
    rw [displacement_eq_of_map_eq π hkert htH p
      (m := Function.surjInv hπ q * Function.surjInv hπ r)
      (by simp only [map_mul, Function.surjInv_eq hπ]),
      displacement_mul_of_mem_center _ _ hmem]

theorem fixedLiftObstruction_apply [L.Normal] (π : L →* Q) (hπ : Function.Surjective π)
    {t : L} (hkert : π.ker = zpowers t) (htH : (t : H) ∈ center H) (p : H) (α : MulAut Q)
    (hα : ∀ l : L, α (π l) = π (MulAut.conjNormal p l))
    (q : FixedCommutingProduct.fixedSubgroup α) (l : L) (hl : π l = q) :
    (fixedLiftObstruction π hπ hkert htH p α hα q : H) = (l : H)⁻¹ * p * l * p⁻¹ :=
  displacement_eq_of_map_eq π hkert htH p (by rw [Function.surjInv_eq hπ, hl])

theorem map_ker_fixedLiftObstruction [L.Normal] (π : L →* Q) (hπ : Function.Surjective π)
    {t : L} (hkert : π.ker = zpowers t) (htH : (t : H) ∈ center H) (p : H) (α : MulAut Q)
    (hα : ∀ l : L, α (π l) = π (MulAut.conjNormal p l)) :
    (fixedLiftObstruction π hπ hkert htH p α hα).ker.map
        (FixedCommutingProduct.fixedSubgroup α).subtype =
      ((centralizer {p}).subgroupOf L).map π := by
  ext q
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨l, hl⟩ := hπ q
    refine ⟨l, ?_, hl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hq
    have h1 := congrArg Subtype.val hq
    rw [fixedLiftObstruction_apply π hπ hkert htH p α hα q l hl, OneMemClass.coe_one] at h1
    rw [SetLike.mem_coe, mem_subgroupOf, mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    calc p * l = l * ((l : H)⁻¹ * p * l * p⁻¹) * p := by group
      _ = l * p := by rw [h1, mul_one]
  · rintro ⟨l, hl, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, mem_centralizer_iff] at hl
    simp only [Set.mem_singleton_iff, forall_eq] at hl
    have hdisp : (l : H)⁻¹ * p * l * p⁻¹ = 1 := by
      rw [mul_assoc (l : H)⁻¹, hl]
      group
    have hfix : π l ∈ FixedCommutingProduct.fixedSubgroup α := by
      rw [mem_fixedSubgroup_iff, hα]
      exact map_conjNormal_eq_of_displacement_mem π hkert (hdisp ▸ one_mem _)
    refine ⟨⟨π l, hfix⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Subtype.ext
    rw [fixedLiftObstruction_apply π hπ hkert htH p α hα _ l rfl, hdisp, OneMemClass.coe_one]

private theorem ker_inf_centralizer_eq (π : L →* Q) {t : L} (hkert : π.ker = zpowers t)
    (htH : (t : H) ∈ center H) (p : H) :
    π.ker ⊓ (centralizer {p}).subgroupOf L = zpowers t := by
  rw [hkert, inf_eq_left, zpowers_le, mem_subgroupOf, mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  exact mem_center_iff.mp htH p

theorem fixedLiftObstruction_surjective_of_conj [L.Normal] (π : L →* Q)
    (hπ : Function.Surjective π) {t : L} (hkert : π.ker = zpowers t)
    (htH : (t : H) ∈ center H) (p : H) (α : MulAut Q)
    (hα : ∀ l : L, α (π l) = π (MulAut.conjNormal p l)) {l : L}
    (hl : (l : H) * p * (l : H)⁻¹ = t * p) :
    Function.Surjective (fixedLiftObstruction π hπ hkert htH p α hα) := by
  have htinv : ((t : H))⁻¹ ∈ center H := inv_mem htH
  have hdisp : (l : H)⁻¹ * p * l * p⁻¹ = (t : H)⁻¹ := by
    calc (l : H)⁻¹ * p * l * p⁻¹ = (l : H)⁻¹ * ((t : H)⁻¹ * (t * p)) * l * p⁻¹ := by group
      _ = (l : H)⁻¹ * ((t : H)⁻¹ * (l * p * (l : H)⁻¹)) * l * p⁻¹ := by rw [hl]
      _ = (l : H)⁻¹ * ((t : H)⁻¹ * l) := by group
      _ = (t : H)⁻¹ := by rw [← mem_center_iff.mp htinv l, inv_mul_cancel_left]
  have hfix : π l ∈ FixedCommutingProduct.fixedSubgroup α := by
    rw [mem_fixedSubgroup_iff, hα]
    exact map_conjNormal_eq_of_displacement_mem π hkert (hdisp ▸ inv_mem (mem_zpowers _))
  intro y
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp y.2
  refine ⟨⟨π l, hfix⟩ ^ (-k), Subtype.ext ?_⟩
  rw [map_zpow, SubgroupClass.coe_zpow,
    fixedLiftObstruction_apply π hπ hkert htH p α hα _ l rfl, hdisp, inv_zpow', neg_neg, hk]

private theorem exists_conj_eq_of_index_eq_two (hidx : L.index = 2) {p g y : H} (hpL : p ∉ L)
    (hg : g * p * g⁻¹ = y) : ∃ l : L, (l : H) * p * (l : H)⁻¹ = y := by
  by_cases hgL : g ∈ L
  · exact ⟨⟨g, hgL⟩, hg⟩
  · have hmem : g * p⁻¹ ∈ L := by
      rw [mul_mem_iff_of_index_two hidx]
      simp [hgL, hpL]
    refine ⟨⟨g * p⁻¹, hmem⟩, ?_⟩
    rw [← hg]
    group

end Obstruction

theorem central_double_cover_full_action_kernel_and_fixed_lift_obstruction [L.Normal]
    (hLq : CFSG.IsQuasisimple L) {t : L} (hZ : center L = zpowers t) (ht : orderOf t = 2)
    (hCL : centralizer (L : Set H) = zpowers (t : H)) (π : L →* Q)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) :
    ∃ θ : H →* MulAut Q, (∀ (h : H) (l : L), θ h (π l) = π (MulAut.conjNormal h l)) ∧
      (∀ θ' : H →* MulAut Q, (∀ (h : H) (l : L), θ' h (π l) = π (MulAut.conjNormal h l)) →
        θ' = θ) ∧
      θ.ker = zpowers (t : H) ∧ (OuterAutomorphisms.inner Q).comap θ = L ∧
      ∀ p : H, p ∉ L → orderOf p = 2 →
        θ p ∉ OuterAutomorphisms.inner Q ∧ orderOf (θ p) = 2 ∧
        ∃ δ : FixedCommutingProduct.fixedSubgroup (θ p) →* zpowers (t : H),
          (∀ (q : FixedCommutingProduct.fixedSubgroup (θ p)) (l : L), π l = q →
            (δ q : H) = (l : H)⁻¹ * p * l * p⁻¹) ∧
          δ.ker.map (FixedCommutingProduct.fixedSubgroup (θ p)).subtype =
            ((centralizer {p}).subgroupOf L).map π ∧
          π.ker ⊓ (centralizer {p}).subgroupOf L = zpowers t ∧
          (L.index = 2 → IsConj p ((t : H) * p) → Function.Surjective δ) := by
  have hperf : Group.IsPerfect L := hLq.1
  have hkerZ : π.ker = center L := hker.trans hZ.symm
  have htH : (t : H) ∈ center H :=
    coe_mem_center_of_center_eq_zpowers hZ (by rw [← ht, pow_orderOf_eq_one])
  have hCL' : centralizer (L : Set H) ≤ L := by
    rw [hCL, zpowers_le]
    exact t.2
  refine ⟨fullAction π hπ hkerZ, fullAction_apply π hπ hkerZ,
    fun θ' hθ' => fullAction_unique π hπ hkerZ θ' hθ', by rw [ker_fullAction, hCL],
    comap_inner_fullAction π hπ hkerZ hCL', fun p hpL hp2 => ?_⟩
  refine ⟨fullAction_notMem_inner π hπ hkerZ hCL' hpL,
    orderOf_fullAction π hπ hkerZ hCL' hpL hp2,
    fixedLiftObstruction π hπ hker htH p _ (fullAction_apply π hπ hkerZ p),
    fixedLiftObstruction_apply π hπ hker htH p _ (fullAction_apply π hπ hkerZ p),
    map_ker_fixedLiftObstruction π hπ hker htH p _ (fullAction_apply π hπ hkerZ p),
    ker_inf_centralizer_eq π hker htH p, fun hidx hconj => ?_⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  obtain ⟨l, hl⟩ := exists_conj_eq_of_index_eq_two hidx hpL hg
  exact fixedLiftObstruction_surjective_of_conj π hπ hker htH p _
    (fullAction_apply π hπ hkerZ p) hl

end CFSG.ComponentClassification.CentralCover
