module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListCongr
import CFSG.Quasithin.EmptyFaithful.S1421QA5Fix
import CFSG.RankThree.GroupTheory.SteinbergBMExtraspecialThirtyTwoFive
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY

@[reducible] private def quaternionDihedralDFintype : Fintype QuaternionDihedralD :=
  Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

attribute [local instance] quaternionDihedralDFintype

private def dihedralToQDDHom : DihedralGroup 4 →* QuaternionDihedralD where
  toFun
    | .r i => ⟨Multiplicative.ofAdd i, Multiplicative.ofAdd 0⟩
    | .sr i => ⟨Multiplicative.ofAdd (-i), Multiplicative.ofAdd 1⟩
  map_one' := by decide
  map_mul' := by decide

theorem nonempty_quaternionDihedralD_mulEquiv :
    Nonempty (QuaternionDihedralD ≃* DihedralGroup 4) :=
  ⟨(MulEquiv.ofBijective dihedralToQDDHom (by decide)).symm⟩

private def qd32OfQ : QuaternionGroup 2 →* QD32 :=
  (QuotientGroup.mk' quaternionDihedralDiagonal).comp (MonoidHom.inl _ _)

private def qd32OfD : QuaternionDihedralD →* QD32 :=
  (QuotientGroup.mk' quaternionDihedralDiagonal).comp (MonoidHom.inr _ _)

private def qd32Qsub : Subgroup QD32 := qd32OfQ.range

private def qd32Esub : Subgroup QD32 := qd32OfD.range

private theorem qd32OfQ_injective : Function.Injective qd32OfQ := by
  intro a b hab
  have hmem : ((a, 1) : QuaternionGroup 2 × QuaternionDihedralD)⁻¹ * (b, 1) ∈
      quaternionDihedralDiagonal := QuotientGroup.eq.mp hab
  rw [quaternionDihedralDiagonal, mem_zpowers_of_orderOf_eq_two orderOf_quaternionDihedralZ]
    at hmem
  rcases hmem with h | h
  · have h1 : a⁻¹ * b = 1 := by simpa using congrArg Prod.fst h
    exact inv_mul_eq_one.mp h1
  · exfalso
    have h2 : (1 : QuaternionDihedralD) = quaternionDihedralZD := by
      simpa using congrArg Prod.snd h
    exact (by decide : quaternionDihedralZD ≠ 1) h2.symm

private theorem qd32OfD_injective : Function.Injective qd32OfD := by
  intro a b hab
  have hmem : ((1, a) : QuaternionGroup 2 × QuaternionDihedralD)⁻¹ * (1, b) ∈
      quaternionDihedralDiagonal := QuotientGroup.eq.mp hab
  rw [quaternionDihedralDiagonal, mem_zpowers_of_orderOf_eq_two orderOf_quaternionDihedralZ]
    at hmem
  rcases hmem with h | h
  · have h1 : a⁻¹ * b = 1 := by simpa using congrArg Prod.snd h
    exact inv_mul_eq_one.mp h1
  · exfalso
    have h1 : (1 : QuaternionGroup 2) = quaternionDihedralZQ := by
      simpa using congrArg Prod.fst h
    exact (by decide : quaternionDihedralZQ ≠ 1) h1.symm

private theorem qd32OfQ_zQ : qd32OfQ quaternionDihedralZQ = qd32Z := by
  rw [qd32Z_eq]
  rfl

private theorem qd32OfD_zD : qd32OfD quaternionDihedralZD = qd32Z := by
  rw [qd32Z_eq]
  show QuotientGroup.mk ((1, quaternionDihedralZD) :
    QuaternionGroup 2 × QuaternionDihedralD) =
    QuotientGroup.mk ((QuaternionGroup.a 2, 1) :
      QuaternionGroup 2 × QuaternionDihedralD)
  rw [QuotientGroup.eq]
  rw [quaternionDihedralDiagonal, mem_zpowers_of_orderOf_eq_two orderOf_quaternionDihedralZ]
  right
  decide

private theorem sup_qd32Qsub_qd32Esub : qd32Qsub ⊔ qd32Esub = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨a, b⟩, rfl⟩ := QuotientGroup.mk_surjective x
  have hx : ((a, b) : QD32) = qd32OfQ a * qd32OfD b := by
    simp only [qd32OfQ, qd32OfD, MonoidHom.comp_apply, ← map_mul]
    congr 1
    ext <;> simp
  rw [hx]
  exact mul_mem (Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨a, rfl⟩))
    (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨b, rfl⟩))

private theorem inf_qd32Qsub_qd32Esub : qd32Qsub ⊓ qd32Esub = Subgroup.zpowers qd32Z := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxQ, hxE⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hxQ
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hxE
    have hmem : ((a, 1) : QuaternionGroup 2 × QuaternionDihedralD)⁻¹ * (1, b) ∈
        quaternionDihedralDiagonal := QuotientGroup.eq.mp (ha.trans hb.symm)
    rw [quaternionDihedralDiagonal,
      mem_zpowers_of_orderOf_eq_two orderOf_quaternionDihedralZ] at hmem
    rcases hmem with h | h
    · have ha1 : a = 1 := by simpa using congrArg Prod.fst h
      have hb1 : b = 1 := by simpa using congrArg Prod.snd h
      have hx1 : x = 1 := by rw [← ha, ha1]; simp
      rw [hx1]
      exact one_mem _
    · have ha' : a = quaternionDihedralZQ := by
        have h1 : a⁻¹ = quaternionDihedralZQ := by
          simpa using congrArg Prod.fst h
        calc a = (a⁻¹)⁻¹ := (inv_inv a).symm
          _ = quaternionDihedralZQ⁻¹ := by rw [h1]
          _ = quaternionDihedralZQ := by decide
      rw [← ha, ha', qd32OfQ_zQ]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact MonoidHom.mem_range.mpr ⟨quaternionDihedralZQ, qd32OfQ_zQ⟩
    · exact MonoidHom.mem_range.mpr ⟨quaternionDihedralZD, qd32OfD_zD⟩

theorem isQ8D8Type_QD32 : IsQ8D8Type QD32 := by
  refine ⟨qd32Qsub, qd32Esub, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(MonoidHom.ofInjective qd32OfQ_injective).symm⟩
  · obtain ⟨e⟩ := nonempty_quaternionDihedralD_mulEquiv
    exact ⟨(MonoidHom.ofInjective qd32OfD_injective).symm.trans e⟩
  · rintro q hq r hr
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hq
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hr
    simp only [qd32OfQ, qd32OfD, MonoidHom.comp_apply, ← map_mul]
    congr 1
    ext <;> simp
  · exact sup_qd32Qsub_qd32Esub
  · rw [inf_qd32Qsub_qd32Esub, Nat.card_zpowers, orderOf_qd32Z]

private theorem eq_eight_of_dvd_eight_of_modEq_five {n : ℕ} (hdvd : n ∣ 8) (hmod : n ≡ 8 [MOD 5]) :
    n = 8 := by
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (h8 ▸ hdvd)
  have hmod' : 2 ^ j % 5 = 2 ^ 3 % 5 := by
    have h := hmod
    rw [hj] at h
    simpa [Nat.ModEq, h8] using h
  have key : ∀ j : Fin 4, 2 ^ j.val % 5 = 2 ^ 3 % 5 → j.val = 3 := by decide
  have hj3 : j = 3 := key ⟨j, by omega⟩ hmod'
  rw [hj, hj3, h8]

private theorem mem_normalizer_of_pow_five {X : Type*} [Group X] {Q : Subgroup X} {x : X}
    (hx : x ^ 5 = 1) (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) :
    x ∈ Subgroup.normalizer (Q : Set X) := by
  have hx4 : x ^ 4 = x⁻¹ := by
    have h : x ^ 4 * x = 1 := by rw [← pow_succ, hx]
    exact eq_inv_of_mul_eq_one_left h
  have hxQinv : ∀ q ∈ Q, x⁻¹ * q * x ∈ Q := by
    intro q hq
    have hxpow : ∀ k : ℕ, x ^ k * q * (x ^ k)⁻¹ ∈ Q := by
      intro k
      induction k with
      | zero => simpa using hq
      | succ k ih =>
          have hstep : x ^ (k + 1) * q * (x ^ (k + 1))⁻¹ =
              x * (x ^ k * q * (x ^ k)⁻¹) * x⁻¹ := by
            rw [pow_succ]
            group
          rw [hstep]
          exact hxQ _ ih
    have h4 : x ^ 4 * q * (x ^ 4)⁻¹ ∈ Q := hxpow 4
    have h4' : (x ^ 4)⁻¹ = x := by rw [hx4, inv_inv]
    rw [h4', hx4] at h4
    exact h4
  rw [Subgroup.mem_normalizer_iff]
  intro q
  exact ⟨fun hq => hxQ q hq, fun hq => by
    have h := hxQinv (x * q * x⁻¹) hq
    have hq' : x⁻¹ * (x * q * x⁻¹) * x = q := by group
    rwa [hq'] at h⟩

private theorem card_fixedPoints_eq_card_inf_centralizer {X : Type*} [Group X] {Q : Subgroup X}
    {x : X} [MulAction ↥(Subgroup.zpowers x) ↥Q]
    (hsmul : ∀ (s : ↥(Subgroup.zpowers x)) (q : ↥Q),
      (((s • q : ↥Q)) : X) = (s : X) * (q : X) * (s : X)⁻¹) :
    Nat.card ↑(MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥Q) =
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set X)) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun q => ⟨(q.1 : X), q.1.2, ?_⟩
      invFun := fun y => ⟨⟨(y : X), y.2.1⟩, ?_⟩
      left_inv := fun q => by rfl
      right_inv := fun y => by rfl }
  · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h := q.2 ⟨x, Subgroup.mem_zpowers x⟩
    have := congrArg (fun z : ↥Q => (z : X)) h
    rw [hsmul] at this
    simp only at this
    calc (q.1 : X) * x = ((x * q.1 * x⁻¹) * x) := by rw [this]
      _ = x * (q.1 : X) := by group
  · intro s
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 s.2
    show s • (⟨(y : X), y.2.1⟩ : ↥Q) = ⟨(y : X), y.2.1⟩
    apply Subtype.ext
    rw [hsmul, ← hk]
    have h1 : x * (y : X) = (y : X) * x :=
      (Subgroup.mem_centralizer_singleton_iff.1 y.2.2).symm
    have h2 : (y : X) * x ^ k = x ^ k * (y : X) := by
      have hc : Commute (y : X) x := h1.symm
      exact (hc.zpow_right k).eq
    calc x ^ k * (y : X) * (x ^ k)⁻¹ = ((y : X) * x ^ k) * (x ^ k)⁻¹ := by rw [h2]
      _ = (y : X) := by group

theorem commute_of_card_eight {X : Type*} [Group X] {Q : Subgroup X} (hQ : Nat.card ↥Q = 8)
    {x : X} (hx : x ^ 5 = 1) (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) : ∀ q ∈ Q, x * q = q * x := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  haveI : Finite ↥Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  by_cases hx1 : x = 1
  · intro q _
    subst hx1
    simp
  have hxord : orderOf x = 5 := orderOf_eq_prime hx hx1
  have hxN : x ∈ Subgroup.normalizer (Q : Set X) := mem_normalizer_of_pow_five hx hxQ
  let c : ↥(Subgroup.zpowers x) →* MulAut ↥Q :=
    (Q.normalizerMonoidHom).comp (Subgroup.inclusion ((Subgroup.zpowers_le).2 hxN))
  let _ : MulAction ↥(Subgroup.zpowers x) ↥Q := MulAction.compHom ↥Q c
  have hsmul : ∀ (s : ↥(Subgroup.zpowers x)) (q : ↥Q),
      (((s • q : ↥Q)) : X) = (s : X) * (q : X) * (s : X)⁻¹ := fun s q => by
    show ((c s) q : X) = _
    simp [c]
  have hP : IsPGroup 5 ↥(Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hxord]
    norm_num
  have hmod : Nat.card ↥Q ≡
      Nat.card ↑(MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥Q) [MOD 5] :=
    hP.card_modEq_card_fixedPoints ↥Q
  have hfix : Nat.card ↑(MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥Q) =
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set X)) :=
    card_fixedPoints_eq_card_inf_centralizer hsmul
  rw [hQ, hfix] at hmod
  have hdvd : Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set X)) ∣ 8 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : Q ⊓ Subgroup.centralizer ({x} : Set X) ≤ Q)
    rwa [hQ] at h
  have hF8 : Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set X)) = 8 :=
    eq_eight_of_dvd_eight_of_modEq_five hdvd hmod.symm
  have hFtop : Q ⊓ Subgroup.centralizer ({x} : Set X) = Q :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hF8, hQ])
  intro q hq
  have hqF : q ∈ Q ⊓ Subgroup.centralizer ({x} : Set X) := by rw [hFtop]; exact hq
  exact (Subgroup.mem_centralizer_singleton_iff.1 hqF.2).symm

private theorem fixedPoints_subgroup_eq_center {Q : Type} [Group Q] [Finite Q]
    (hcard : Nat.card Q = 32) (hZcard : Nat.card (Subgroup.center Q) = 2)
    (β : MulAut Q) (hβ : orderOf β = 5)
    (hβZ : ∀ z ∈ Subgroup.center Q, β z = z) :
    FixedPoints.subgroup ↥(Subgroup.zpowers β) Q = Subgroup.center Q := by
  have hβ1 : β ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hβ
    norm_num at hβ
  have hcardFixSub : Nat.card (CFSG.Quasithin.AutQ8D8.fixSub β) = 2 :=
    CFSG.Quasithin.AutQ8D8.card_fixSub_eq_two hcard hβ1 ⟨1, hβ⟩
  have hset : (FixedPoints.subgroup ↥(Subgroup.zpowers β) Q : Set Q) =
      (CFSG.Quasithin.AutQ8D8.fixSub β : Set Q) :=
    CFSG.Quasithin.AutQ8D8.fixedPoints_zpowers β
  have hmem : ∀ x : Q, x ∈ FixedPoints.subgroup ↥(Subgroup.zpowers β) Q ↔
      x ∈ CFSG.Quasithin.AutQ8D8.fixSub β := fun x => by
    simpa using congrArg (fun s : Set Q => x ∈ s) hset
  have hcardFix : Nat.card ↥(FixedPoints.subgroup ↥(Subgroup.zpowers β) Q) = 2 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hmem), hcardFixSub]
  have hcenter_le : Subgroup.center Q ≤ FixedPoints.subgroup ↥(Subgroup.zpowers β) Q := by
    intro z hz
    rw [FixedPoints.mem_subgroup]
    intro m
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 m.2
    have hstab : β ∈ MulAction.stabilizer (MulAut Q) z := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hβZ z hz
    have hpow : β ^ k ∈ MulAction.stabilizer (MulAut Q) z :=
      Subgroup.zpow_mem (MulAction.stabilizer (MulAut Q) z) hstab k
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hpow
    change ((m : MulAut Q) • z) = z
    rw [← hk, MulAut.smul_def]
    exact hpow
  exact (Subgroup.eq_of_le_of_card_ge hcenter_le (by rw [hcardFix, hZcard])).symm

private theorem exists_center_eq_zpowers_of_card_two {Q : Type} [Group Q]
    (hZcard : Nat.card (Subgroup.center Q) = 2) :
    ∃ z : Q, Subgroup.center Q = Subgroup.zpowers z ∧ orderOf z = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(Subgroup.center Q) :=
    Nat.finite_of_card_ne_zero (by rw [hZcard]; norm_num)
  haveI : Fintype ↥(Subgroup.center Q) := Fintype.ofFinite _
  have hZcard' : Fintype.card ↥(Subgroup.center Q) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hZcard
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card (G := ↥(Subgroup.center Q)) 2
    (by rw [hZcard'])
  refine ⟨(z : Q), ?_, ?_⟩
  · have hle : Subgroup.zpowers (z : Q) ≤ Subgroup.center Q := Subgroup.zpowers_le.mpr z.2
    have hcardz : Nat.card ↥(Subgroup.zpowers (z : Q)) = 2 := by
      rw [Nat.card_zpowers]
      rw [Subgroup.orderOf_coe z]
      exact hzord
    have hcardc : Nat.card ↥(Subgroup.center Q) = 2 := hZcard
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardc, hcardz])).symm
  · rw [Subgroup.orderOf_coe z]
    exact hzord

private theorem mulAut_apply_eq_of_mem_center {Q : Type} [Group Q] {z : Q}
    (hz : Subgroup.center Q = Subgroup.zpowers z) (hzord : orderOf z = 2)
    (α : MulAut Q) {w : Q} (hw : w ∈ Subgroup.center Q) : α w = w := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    norm_num at hzord
  have hαZmem : α z ∈ Subgroup.center Q := by
    have hcomap : Subgroup.comap α.toMonoidHom (Subgroup.center Q) = Subgroup.center Q :=
      Subgroup.centerCharacteristic.fixed α
    have hzmem : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    have hzc : z ∈ Subgroup.center Q := hz ▸ hzmem
    have : z ∈ Subgroup.comap α.toMonoidHom (Subgroup.center Q) := by rwa [hcomap]
    exact Subgroup.mem_comap.mp this
  have hzfix : α z = z := by
    have hne : α z ≠ 1 := by
      intro h
      have h1 : z = 1 := by
        have h' := congrArg (fun x => α.symm x) h
        simpa using h'
      exact hz1 h1
    rcases (mem_zpowers_of_orderOf_eq_two hzord).mp (hz ▸ hαZmem) with h | h
    · exact absurd h hne
    · exact h
  rcases (mem_zpowers_of_orderOf_eq_two hzord).mp (hz ▸ hw) with h | h
  · rw [h]; simp
  · rw [h]; exact hzfix

private theorem sq_apply_eq_self_of_quotient_eq {Q : Type} [Group Q] {Z : Subgroup Q} [Z.Normal]
    {α : MulAut Q} (hZ2 : ∀ w ∈ Z, w * w = 1) (hαZ : ∀ w ∈ Z, α w = w) {s : Q}
    (hs : ((α s : Q) : Q ⧸ Z) = (s : Q ⧸ Z)) : (α ^ 2) s = s := by
  set w : Q := (α s)⁻¹ * s with hwdef
  have hwmem : w ∈ Z := by
    rw [hwdef]
    exact QuotientGroup.eq.mp hs
  have hwas : α s = s * w⁻¹ := by
    have h1 : s = α s * w := by rw [hwdef]; group
    calc α s = (α s * w) * w⁻¹ := by group
      _ = s * w⁻¹ := by rw [← h1]
  have hw2 : w * w = 1 := hZ2 w hwmem
  have hwinv : w⁻¹ * w⁻¹ = 1 := by
    rw [← mul_inv_rev, hw2, inv_one]
  have hαw : α w⁻¹ = w⁻¹ := hαZ _ (Subgroup.inv_mem _ hwmem)
  calc (α ^ 2) s = α (α s) := rfl
    _ = α (s * w⁻¹) := by rw [hwas]
    _ = α s * α w⁻¹ := map_mul α _ _
    _ = (s * w⁻¹) * w⁻¹ := by rw [hwas, hαw]
    _ = s * (w⁻¹ * w⁻¹) := by group
    _ = s * 1 := by rw [hwinv]
    _ = s := by group

theorem isQ8D8Type_of_extraspecial {Q : Type} [Group Q] (hQ : CFSG.IsExtraspecialPGroup 2 Q)
    (hcard : Nat.card Q = 32) (α : MulAut Q) (hα : orderOf α = 5) : IsQ8D8Type Q := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hZcard : Nat.card (Subgroup.center Q) = 2 := hQ.2.2.2
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨z0, hZ, hz0ord⟩ := exists_center_eq_zpowers_of_card_two hZcard
  have hαZ : ∀ w ∈ Subgroup.center Q, α w = w :=
    fun w hw => mulAut_apply_eq_of_mem_center hZ hz0ord α hw
  have hα2ord : orderOf (α ^ 2) = 5 := by
    rw [orderOf_pow, hα]
    norm_num
  have hα2Z : ∀ w ∈ Subgroup.center Q, (α ^ 2) w = w := by
    intro w hw
    rw [pow_two]
    show α (α w) = w
    rw [hαZ w hw, hαZ w hw]
  have hFix : FixedPoints.subgroup ↥(Subgroup.zpowers (α ^ 2)) Q = Subgroup.center Q :=
    fixedPoints_subgroup_eq_center hcard hZcard (α ^ 2) hα2ord hα2Z
  have hZ2 : ∀ w ∈ Subgroup.center Q, w * w = 1 := by
    intro w hw
    rcases (mem_zpowers_of_orderOf_eq_two hz0ord).mp (hZ ▸ hw) with h | h
    · rw [h]; simp
    · rw [h]
      have := pow_orderOf_eq_one z0
      rwa [hz0ord, pow_two] at this
  have hfix : ∀ s : Q, ((α s : Q) : Q ⧸ Subgroup.center Q) =
      (s : Q ⧸ Subgroup.center Q) → s ∈ Subgroup.center Q := by
    intro s hs
    have h2 : (α ^ 2) s = s := sq_apply_eq_self_of_quotient_eq hZ2 hαZ hs
    have hmem : s ∈ FixedPoints.subgroup ↥(Subgroup.zpowers (α ^ 2)) Q := by
      rw [FixedPoints.mem_subgroup]
      intro m
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 m.2
      change ((m : MulAut Q) • s) = s
      rw [← hk, MulAut.smul_def]
      have hstab : (α ^ 2) ∈ MulAction.stabilizer (MulAut Q) s := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact h2
      have hpow : (α ^ 2) ^ k ∈ MulAction.stabilizer (MulAut Q) s :=
        Subgroup.zpow_mem (MulAction.stabilizer (MulAut Q) s) hstab k
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hpow
      exact hpow
    rwa [hFix] at hmem
  obtain ⟨⟨e⟩, -⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.extraspecial_thirty_two_five_recognition
      hQ hcard hZ α hα hfix
  exact IsQ8D8Type.of_mulEquiv e.symm isQ8D8Type_QD32

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
