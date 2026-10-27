module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2G2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2F4
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2E6
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Main
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2E8

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.Burgoyne.X10
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def FamInnerNoPSL2 (t : StatedLieTag) : Prop :=
  ∀ (J : Type) [Group J] (n p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible t n p f →
    LieModel J t n p f → ∀ g : J, orderOf (MulAut.conj g) = 2 →
      ∀ L : Subgroup (fixedSubgroup (MulAut.conj g)), IsComponent L → NoPSL2Odd L

theorem famInnerNoPSL2_of_explicit
    {t : StatedLieTag} {τ : Tag} (ht : t ∈ chevalleyExceptionalTags)
    (hmodel : ∀ (J : Type) [Group J] (p f : ℕ), ChevalleyExceptionalModel J t p f →
      UntwistedChevalleyModel J τ (p ^ f))
    (hinner : ExcInnerNoPSL2 τ) : FamInnerNoPSL2 t := by
  intro J _ n p f hp hp2 hadm hm g hg L hL
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ
    (hmodel J p f (GH74.chevalleyExceptionalModel_of_lieModel ht hm))
  have hβ : orderOf (MulAut.congr e (MulAut.conj g)) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _).trans hg
  have hβg : ∀ h : adjointGroup τ F, ((MulAut.congr e (MulAut.conj g)) h : ModGL τ F) =
      ((e g : adjointGroup τ F) : ModGL τ F) * rootDiagUnit τ 1 * (h : ModGL τ F) *
        (rootDiagUnit τ 1)⁻¹ * ((e g : adjointGroup τ F) : ModGL τ F)⁻¹ := by
    intro h
    rw [rootDiagUnit_one, mul_one, inv_one, mul_one]
    change ((e (g * e.symm h * g⁻¹) : adjointGroup τ F) : ModGL τ F) = _
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  exact noPSL2Odd_of_component_equiv (fixedSubgroupCongrEquiv e (MulAut.conj g))
    (hinner F p f hp hp2 hF _ (e g) 1 hβg hβ) hL

theorem famInnerNoPSL2_G2
    : FamInnerNoPSL2 .G2 :=
  famInnerNoPSL2_of_explicit (τ := .G2) (by decide) (fun _ _ _ _ h => h.2) excInnerNoPSL2_G2

theorem famInnerNoPSL2_F4
    (hO : LieOrderFormulasInput) : FamInnerNoPSL2 .F4 :=
  famInnerNoPSL2_of_explicit (τ := .F4) (by decide) (fun _ _ _ _ h => h.2) (excInnerNoPSL2_F4 hO)

theorem famInnerNoPSL2_E6
    (hO : LieOrderFormulasInput) : FamInnerNoPSL2 .E6 :=
  famInnerNoPSL2_of_explicit (τ := .E6) (by decide) (fun _ _ _ _ h => h.2) (excInnerNoPSL2_E6 hO)

theorem famInnerNoPSL2_E8
    (hO : LieOrderFormulasInput) : FamInnerNoPSL2 .E8 :=
  famInnerNoPSL2_of_explicit (τ := .E8) (by decide) (fun _ _ _ _ h => h.2) (excInnerNoPSL2_E8 hO)

theorem not_lieModel_psl_two_of_famInner
    (hO : LieOrderFormulasInput) {t : StatedLieTag} (ht : t ∈ chevalleyExceptionalTags)
    (hfam : FamInnerNoPSL2 t) {S : Type} [Group S] [Finite S] {r e : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hadm : StatedLieAdmissible t 0 r e) (hS : LieModel S t 0 r e) {s : S}
    (hs2 : s * s = 1) (hs1 : s ≠ 1) {L : Subgroup ↥(fixedSubgroup (MulAut.conj s))}
    (hL : IsPComponent 2 L) {p f : ℕ} (hp : p.Prime) (h5 : 5 ≤ p ^ f) :
    ¬ LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSL 2 p f := by
  intro hLm
  obtain ⟨hsimple, hna⟩ := simple_nonabelian_of_lieModel_exc hO (Or.inl ht) hadm hS
  have hZS : center S = ⊥ := by
    obtain ⟨a, b, hab⟩ := hna
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
    · exact h
    · exact absurd ((mem_center_iff.mp (h ▸ mem_top a)) b).symm hab
  have hc1 : MulAut.conj s ≠ 1 := fun h => by
    apply hs1
    have hz : s ∈ center S := mem_center_iff.mpr fun y => by
      have h' := congrArg (fun φ : MulAut S => φ y) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at h'
      calc y * s = s * y * s⁻¹ * s := by rw [h']
        _ = s * y := by group
    rw [hZS] at hz
    exact mem_bot.mp hz
  have hc2 : MulAut.conj s * MulAut.conj s = 1 := by rw [← map_mul, hs2, map_one]
  have hq : IsQuasisimple L := fixedTwoComponentsQuasisimple_of_oddLieType hna
    ⟨t, 0, r, e, hr, hr2, hadm, hS⟩ (MulAut.conj s) hc2 hc1 L hL
  obtain ⟨-, -, hsub, -, -⟩ := hL
  have hord : orderOf (MulAut.conj s) = 2 := orderOf_eq_prime (by rw [sq]; exact hc2) hc1
  have hs := FooteLit.isSimpleGroup_of_lieModel_psl_two hLm
  have hZ := GSThmB.X10Rec.center_eq_pPrimeCore hq hs
  have hLZ : LieModel (↥L ⧸ center ↥L) .PSL 2 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZ).symm hLm
  have hodd : Odd (Nat.card (center ↥L)) := by
    rw [hZ]
    exact Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥L))
  exact hfam S 0 r e hr hr2 hadm hS s hord L ⟨hq, hsub⟩ p f hp h5 hodd hLZ

theorem primeResidual_eq_top_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {p : ℕ}
    (h : CatalogueBPrimeJoin.primeResidual p G = ⊤) :
    CatalogueBPrimeJoin.primeResidual p H = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  have hy : e.symm y ∈ CatalogueBPrimeJoin.primeResidual p G := h ▸ mem_top _
  have hle : CatalogueBPrimeJoin.primeResidual p G ≤
      (CatalogueBPrimeJoin.primeResidual p H).comap e.toMonoidHom := by
    refine (sSup_le fun P hP => ?_ : sSup {P : Subgroup G | IsPGroup p P} ≤ _)
    rw [← Subgroup.map_le_iff_le_comap]
    exact CatalogueBPrimeJoin.pSubgroup_le_residual p _ (IsPGroup.map hP e.toMonoidHom)
  have hy' := hle hy
  rw [Subgroup.mem_comap] at hy'
  simpa using hy'

theorem conj_mem_centralizer_of_comm_mem_center {M : Type*} [Group M] {x m c : M}
    (hz : x * m * x⁻¹ * m⁻¹ ∈ center M) (hc : c ∈ centralizer ({x} : Set M)) :
    m * c * m⁻¹ ∈ centralizer ({x} : Set M) := by
  set z := x * m * x⁻¹ * m⁻¹ with hzdef
  have hzc : ∀ g : M, g * z = z * g := mem_center_iff.mp hz
  have hcx : c * x = x * c := mem_centralizer_singleton_iff.mp hc
  have hmx : m * x * m⁻¹ = z⁻¹ * x := by rw [hzdef]; group
  have h1 : m * c * m⁻¹ * (m * x * m⁻¹) = m * x * m⁻¹ * (m * c * m⁻¹) := by
    calc m * c * m⁻¹ * (m * x * m⁻¹) = m * (c * x) * m⁻¹ := by group
      _ = m * (x * c) * m⁻¹ := by rw [hcx]
      _ = m * x * m⁻¹ * (m * c * m⁻¹) := by group
  rw [hmx] at h1
  have h2 : m * c * m⁻¹ * z⁻¹ = z⁻¹ * (m * c * m⁻¹) := by
    have := hzc (m * c * m⁻¹)
    calc m * c * m⁻¹ * z⁻¹ = z⁻¹ * (z * (m * c * m⁻¹)) * z⁻¹ := by group
      _ = z⁻¹ * (m * c * m⁻¹ * z) * z⁻¹ := by rw [this]
      _ = z⁻¹ * (m * c * m⁻¹) := by group
  rw [mem_centralizer_singleton_iff]
  calc m * c * m⁻¹ * x = z * (m * c * m⁻¹ * (z⁻¹ * x)) := by
        rw [← mul_assoc (m * c * m⁻¹), h2]; group
    _ = z * (z⁻¹ * x * (m * c * m⁻¹)) := by rw [h1]
    _ = x * (m * c * m⁻¹) := by group

theorem false_of_quasisimple_of_famInner
    (hO : LieOrderFormulasInput) {t : StatedLieTag} (ht : t ∈ chevalleyExceptionalTags)
    (hfam : FamInnerNoPSL2 t) {M : Type} [Group M] [Finite M]
    (hZ2 : IsPGroup 2 (center M)) {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hadm : StatedLieAdmissible t 0 r e) (hS : LieModel (M ⧸ center M) t 0 r e) {x : M}
    (hx : x * x = 1) (hxZ : x ∉ center M) {J : Subgroup ↥(centralizer ({x} : Set M))}
    (hJ : IsPComponent 2 J) {p f : ℕ} (hp : p.Prime) (h5 : 5 ≤ p ^ f)
    (hJm : LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p f) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center M) with hπ
  set s : M ⧸ center M := π x with hs
  have hs2 : s * s = 1 := by rw [hs, ← map_mul, hx, map_one]
  have hs1 : s ≠ 1 := fun h => hxZ ((QuotientGroup.eq_one_iff x).1 h)
  have hmem : ∀ c : ↥(centralizer ({x} : Set M)), π c ∈ fixedSubgroup (MulAut.conj s) := by
    intro c
    have hcx : (c : M) * x = x * c := mem_centralizer_singleton_iff.mp c.2
    change s * π c * s⁻¹ = π c
    rw [hs, ← map_mul, ← map_inv, ← map_mul, ← hcx, mul_inv_cancel_right]
  let φ : ↥(centralizer ({x} : Set M)) →* ↥(fixedSubgroup (MulAut.conj s)) :=
    (π.comp (centralizer ({x} : Set M)).subtype).codRestrict _ hmem
  have hφ : ∀ c, ((φ c : ↥(fixedSubgroup (MulAut.conj s))) : M ⧸ center M) = π c := fun _ => rfl
  have hnorm : φ.range.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨c, rfl⟩ y
    obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (center M) (y : M ⧸ center M)
    have hy : s * (y : M ⧸ center M) * s⁻¹ = y := y.2
    have hz : x * m * x⁻¹ * m⁻¹ ∈ center M := by
      rw [← QuotientGroup.eq_one_iff]
      change π (x * m * x⁻¹ * m⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hm, ← hs, hy, mul_inv_cancel]
    refine ⟨⟨m * c * m⁻¹, conj_mem_centralizer_of_comm_mem_center hz c.2⟩, ?_⟩
    apply Subtype.ext
    rw [hφ]
    change π (m * c * m⁻¹) = (y : M ⧸ center M) * π c * (y : M ⧸ center M)⁻¹
    rw [map_mul, map_mul, map_inv, hm]
  have hJq := (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 J).1 hJ
  obtain ⟨hJsn, hJres, hJqq⟩ := hJq
  have hJs : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J) := FooteLit.isSimpleGroup_of_lieModel_psl_two hJm
  have hZJ : center (↥J ⧸ pPrimeCore 2 ↥J) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (↥J ⧸ pPrimeCore 2 ↥J)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hJqq.2.2
      obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (center (↥J ⧸ pPrimeCore 2 ↥J)) a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (center (↥J ⧸ pPrimeCore 2 ↥J)) b
      apply hab
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, h]
      exact mem_top _
  have hinj : Function.Injective (φ.domRestrict J) := by
    refine (injective_iff_map_eq_one _).mpr fun j hj => ?_
    have hjZ : ((j : ↥(centralizer ({x} : Set M))) : M) ∈ center M := by
      have h1 := congrArg Subtype.val hj
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hjc : j ∈ center ↥J := mem_center_iff.mpr fun y =>
      Subtype.ext (Subtype.ext ((mem_center_iff.mp hjZ) _))
    have hjO : j ∈ pPrimeCore 2 ↥J := by
      have hcen : (QuotientGroup.mk' (pPrimeCore 2 ↥J) j) ∈ center (↥J ⧸ pPrimeCore 2 ↥J) := by
        refine mem_center_iff.mpr fun w => ?_
        obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) w
        rw [← map_mul, ← map_mul, (mem_center_iff.mp hjc w')]
      rw [hZJ] at hcen
      exact (QuotientGroup.eq_one_iff j).1 (mem_bot.mp hcen)
    have hodd : Odd (orderOf j) := by
      have h1 : orderOf (⟨j, hjO⟩ : pPrimeCore 2 ↥J) ∣ Nat.card (pPrimeCore 2 ↥J) :=
        orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat (Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2)
        (G := ↥J))) h1
    obtain ⟨k, hk⟩ := hZ2 ⟨_, hjZ⟩
    have hdvd : orderOf j ∣ 2 ^ k := by
      have h1 := orderOf_dvd_of_pow_eq_one hk
      rw [Subgroup.orderOf_mk] at h1
      rwa [Subgroup.orderOf_coe, Subgroup.orderOf_coe] at h1
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hi0 : i = 0 := by
      rcases Nat.eq_zero_or_pos i with h | h
      · exact h
      · rw [hi] at hodd
        exact absurd (Nat.even_pow.mpr ⟨even_two, h.ne'⟩) (Nat.not_even_iff_odd.mpr hodd)
    rw [hi0, pow_zero] at hi
    exact orderOf_eq_one_iff.mp hi
  let eJ : ↥J ≃* ↥(J.map φ) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range J φ))
  have hsn : (J.map φ).IsSubnormal := by
    have h1 : (J.map φ.rangeRestrict).IsSubnormal := hJsn.map φ.rangeRestrict_surjective
    have h2 := h1.trans' hnorm.isSubnormal
    rwa [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] at h2
  have hJ₁ : IsPComponent 2 (J.map φ) := by
    refine (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).2
      ⟨hsn, primeResidual_eq_top_of_mulEquiv eJ hJres, ?_⟩
    exact LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)) hJqq
  have hJm₁ : LieModel (↥(J.map φ) ⧸ pPrimeCore 2 ↥(J.map φ)) .PSL 2 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ))
      hJm
  exact not_lieModel_psl_two_of_famInner hO ht hfam hr hr2 hadm hS hs2 hs1 hJ₁ hp h5 hJm₁

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
