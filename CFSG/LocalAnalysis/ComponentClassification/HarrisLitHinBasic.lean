module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp
public import CFSG.GH74.SectionalRank
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankProjectiveAction

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup

@[expose] def HinConcl (Y : Type) [Group Y] (p m : ℕ) (τ : MulAut Y) : Prop :=
  (GH74.SectionalTwoRankLE ↥(fixedPoints τ) 3 → τ ∉ innAut Y) ∧
    (τ ∉ innAut Y → GH74.SectionalTwoRankLE ↥(fixedPoints τ) 2 →
      Nonempty (Y ≃* Blueprint.NativeSporadic.J2) ∨
        Nonempty (Y ≃* Blueprint.NativeSporadic.J3) ∨
        Blueprint.LieModel Y .PSL 3 2 2 ∨ Blueprint.LieModel Y .PSL 3 p m ∨
        Blueprint.LieModel Y .PSU 3 p m ∨ Blueprint.LieModel Y .PSL 2 p (2 * m))

@[expose] def HinFor (C : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup Y], C Y → (∃ a b : Y, a * b ≠ b * a) →
    ∀ p m : ℕ, p.Prime → p ≠ 2 → 1 ≤ m → 16 ∣ p ^ (2 * m) - 1 →
    (∀ k : ℕ, 1 ≤ k → ¬ Blueprint.LieModel Y .PSL 4 p k ∧ ¬ Blueprint.LieModel Y .PSU 4 p k) →
    ∀ τ : MulAut Y, orderOf τ = 2 →
      Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m → HinConcl Y p m τ

theorem HinFor.mono {C D : (Y : Type) → [Group Y] → Prop}
    (hDC : ∀ (Y : Type) [Group Y], D Y → C Y) (h : HinFor C) : HinFor D :=
  fun Y _ _ _ hY => h Y (hDC Y hY)

theorem HinFor.or {C D : (Y : Type) → [Group Y] → Prop} (hC : HinFor C) (hD : HinFor D) :
    HinFor fun Y _ => C Y ∨ D Y :=
  fun Y _ _ _ hY => hY.elim (hC Y) (hD Y)

theorem hinConcl_of_not_inner {Y : Type} [Group Y] {p m : ℕ} {τ : MulAut Y}
    (hτ : τ ∉ innAut Y) (h2 : ¬ GH74.SectionalTwoRankLE ↥(fixedPoints τ) 2) : HinConcl Y p m τ :=
  ⟨fun _ => hτ, fun _ h => (h2 h).elim⟩

theorem hinConcl_of_list {Y : Type} [Group Y] {p m : ℕ} {τ : MulAut Y} (hτ : τ ∉ innAut Y)
    (hY : Nonempty (Y ≃* Blueprint.NativeSporadic.J2) ∨
      Nonempty (Y ≃* Blueprint.NativeSporadic.J3) ∨
      Blueprint.LieModel Y .PSL 3 2 2 ∨ Blueprint.LieModel Y .PSL 3 p m ∨
      Blueprint.LieModel Y .PSU 3 p m ∨ Blueprint.LieModel Y .PSL 2 p (2 * m)) :
    HinConcl Y p m τ :=
  ⟨fun _ => hτ, fun _ _ => hY⟩

theorem hinConcl_of_not_inner_of_rank {Y : Type} [Group Y] {p m : ℕ} {τ : MulAut Y}
    (hτ : τ ∉ innAut Y)
    (hY : GH74.SectionalTwoRankLE ↥(fixedPoints τ) 2 →
      Nonempty (Y ≃* Blueprint.NativeSporadic.J2) ∨
      Nonempty (Y ≃* Blueprint.NativeSporadic.J3) ∨
      Blueprint.LieModel Y .PSL 3 2 2 ∨ Blueprint.LieModel Y .PSL 3 p m ∨
      Blueprint.LieModel Y .PSU 3 p m ∨ Blueprint.LieModel Y .PSL 2 p (2 * m)) :
    HinConcl Y p m τ :=
  ⟨fun _ => hτ, fun _ h => hY h⟩

theorem hinConcl_of_rank {Y : Type} [Group Y] {p m : ℕ} {τ : MulAut Y}
    (hin : τ ∈ innAut Y → ¬ GH74.SectionalTwoRankLE ↥(fixedPoints τ) 3)
    (hout : τ ∉ innAut Y → ¬ GH74.SectionalTwoRankLE ↥(fixedPoints τ) 2) :
    HinConcl Y p m τ :=
  ⟨fun h3 hτ => hin hτ h3, fun hτ h2 => (hout hτ h2).elim⟩

section Layer

variable {Y : Type} [Group Y]

noncomputable def layerInEquiv (C : Subgroup Y) : ↥(GSThmB.layerIn C) ≃* ↥(pLayer ↥C 2) :=
  ((pLayer ↥C 2).equivMapOfInjective C.subtype C.subtype_injective).symm

theorem pLayer_two_normal [Finite Y] (C : Subgroup Y) : (pLayer ↥C 2).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CatalogueBPrimeJoin.pLayer_characteristic (G := ↥C) (p := 2)
  infer_instance

variable {C : Subgroup Y} {p m : ℕ}

theorem isSimpleGroup_pLayer (h : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    IsSimpleGroup ↥(pLayer ↥C 2) :=
  have := isSimpleGroup_of_lieModel_psl2 h
  (layerInEquiv C).symm.isSimpleGroup

theorem nonabelian_pLayer (h : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    ∃ a b : ↥(pLayer ↥C 2), a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := nonabelian_of_lieModel_psl2 h
  refine ⟨layerInEquiv C a, layerInEquiv C b, fun hc => hab ?_⟩
  apply (layerInEquiv C).injective
  rw [map_mul, map_mul, hc]

theorem center_pLayer_eq_bot (h : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    center ↥(pLayer ↥C 2) = ⊥ := by
  have := isSimpleGroup_pLayer h
  exact (LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_pLayer h)).2

theorem isComponent_pLayer [Finite Y]
    (h : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    IsComponent (pLayer ↥C 2) := by
  have := isSimpleGroup_pLayer h
  exact ⟨(LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_pLayer h)).1,
    (pLayer_two_normal C).isSubnormal⟩

theorem ne_bot_of_isPComponent {X : Type*} [Group X] {K : Subgroup X} (hK : IsPComponent 2 K) :
    K ≠ ⊥ := by
  rintro rfl
  obtain ⟨K', ⟨⟨-, -, a, b, hab⟩, -⟩, -, hmap, -⟩ := hK
  rw [Subgroup.map_bot] at hmap
  subst hmap
  have hsub : Subsingleton (↥(⊥ : Subgroup (X ⧸ pPrimeCore 2 X)) ⧸
      center ↥(⊥ : Subgroup (X ⧸ pPrimeCore 2 X))) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [Subsingleton.elim x y]
  exact hab (Subsingleton.elim _ _)

theorem isPComponent_pLayer (h : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    IsPComponent 2 (pLayer ↥C 2) := by
  have hs := isSimpleGroup_pLayer h
  obtain ⟨K, hK⟩ : ∃ K : Subgroup ↥C, IsPComponent 2 K := by
    by_contra hno
    push Not at hno
    have hbot : pLayer ↥C 2 = ⊥ := by
      refine le_antisymm (sSup_le fun K hK => (hno K hK).elim) bot_le
    have : Nontrivial ↥(pLayer ↥C 2) := hs.toNontrivial
    rw [hbot] at this
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) this
  have hKL : K ≤ pLayer ↥C 2 := le_sSup hK
  have hsn : (K.subgroupOf (pLayer ↥C 2)).IsSubnormal := by
    obtain ⟨-, -, hKs, -⟩ := hK
    exact hKs.subgroupOf
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hs hsn with hb | ht
  · exact ((ne_bot_of_isPComponent hK) (by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hKL hx⟩ : ↥(pLayer ↥C 2)) ∈ K.subgroupOf (pLayer ↥C 2) := hx
      rw [hb, mem_bot] at this
      simpa using congrArg Subtype.val this)).elim
  · have hLK : pLayer ↥C 2 ≤ K := subgroupOf_eq_top.mp ht
    rwa [le_antisymm hKL hLK] at hK

end Layer

section Inner

variable {Y : Type} [Group Y] {p m : ℕ}

theorem mem_fixedPoints_conj (t : Y) : t ∈ fixedPoints (MulAut.conj t) := by
  rw [mem_fixedPoints, MulAut.conj_apply, mul_inv_cancel_right]

theorem commute_of_mem_fixedPoints_conj {t c : Y} (hc : c ∈ fixedPoints (MulAut.conj t)) :
    t * c = c * t := by
  rw [mem_fixedPoints, MulAut.conj_apply] at hc
  calc t * c = t * c * t⁻¹ * t := by group
    _ = c * t := by rw [hc]

theorem not_mem_layerIn_of_conj {τ : MulAut Y} (hτ : τ ≠ 1) {t : Y} (ht : MulAut.conj t = τ)
    (h : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    t ∉ GSThmB.layerIn (fixedPoints τ) := by
  subst ht
  intro htL
  obtain ⟨c, hcL, hc⟩ := Subgroup.mem_map.mp htL
  have hc' : (c : Y) = t := hc
  have hcen : (⟨c, hcL⟩ : ↥(pLayer ↥(fixedPoints (MulAut.conj t)) 2)) ∈ center _ := by
    refine mem_center_iff.mpr fun x => Subtype.ext (Subtype.ext ?_)
    simp only [Subgroup.coe_mul]
    rw [hc']
    exact (commute_of_mem_fixedPoints_conj (x : ↥(fixedPoints (MulAut.conj t))).2).symm
  rw [center_pLayer_eq_bot h, mem_bot] at hcen
  have hc1 : c = 1 := by simpa using congrArg Subtype.val hcen
  have ht1 : t = 1 := by rw [← hc', hc1]; rfl
  exact hτ (by rw [ht1, map_one])

theorem exists_conj_of_mem_innAut {τ : MulAut Y} (hτ : orderOf τ = 2) (hinn : τ ∈ innAut Y)
    (h : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    ∃ t : Y, MulAut.conj t = τ ∧ t ∈ fixedPoints τ ∧ t ∉ GSThmB.layerIn (fixedPoints τ) := by
  obtain ⟨t, rfl⟩ := hinn
  have hτ1 : (MulAut.conj : Y →* MulAut Y) t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  exact ⟨t, rfl, mem_fixedPoints_conj t, not_mem_layerIn_of_conj hτ1 rfl h⟩

end Inner

theorem centralizer_eq_fixedPoints_conj {G : Type} [Group G] (t : G) :
    centralizer ({t} : Set G) = fixedPoints (MulAut.conj t) := by
  ext y
  rw [mem_centralizer_singleton_iff, mem_fixedPoints, MulAut.conj_apply]
  constructor
  · intro h
    rw [← h, mul_inv_cancel_right]
  · intro h
    calc y * t = t * y * t⁻¹ * t := by rw [h]
      _ = t * y := by group

theorem exists_isComponent_of_eq {Y : Type} [Group Y] [Finite Y] {τ : MulAut Y} {p m : ℕ}
    {H : Subgroup Y} (hH : H = fixedPoints τ)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    ∃ B : Subgroup ↥H, IsComponent B ∧ Nonempty (↥B ≃* ↥(GSThmB.layerIn (fixedPoints τ))) := by
  let ι : ↥(fixedPoints τ) ≃* ↥H := MulEquiv.subgroupCongr hH.symm
  refine ⟨(pLayer ↥(fixedPoints τ) 2).map ι.toMonoidHom,
    LocalCores.isComponent_map_mulEquiv ι (isComponent_pLayer hL), ⟨?_⟩⟩
  exact ((pLayer ↥(fixedPoints τ) 2).equivMapOfInjective _ ι.injective).symm.trans
    (layerInEquiv _).symm

theorem not_sectionalTwoRankLE_of_le {Y : Type*} [Group Y] {E C : Subgroup Y} (hEC : E ≤ C)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a ^ 2 = 1) {r : ℕ}
    (hcard : 2 ^ r < Nat.card E) : ¬ GH74.SectionalTwoRankLE ↥C r := by
  intro h
  have hE : Open.IsElemAbelian 2 (E.subgroupOf C) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · exact hcomm _ (mem_subgroupOf.mp a.2) _ (mem_subgroupOf.mp b.2)
    · simpa using hsq _ (mem_subgroupOf.mp hx)
  have hle := h.card_le_of_elementary (E.subgroupOf C) hE
  rw [Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv] at hle
  omega

theorem seven_le_of_sixteen_dvd {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h16 : 16 ∣ p ^ (2 * m) - 1) : 7 ≤ p ^ m := by
  have hq2 : p ^ (2 * m) = (p ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hq2] at h16
  have hodd : Odd (p ^ m) := (hp.odd_of_ne_two hp2).pow
  have h3 : 3 ≤ p ^ m := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      rcases hp.eq_two_or_odd' with h | ⟨k, hk⟩
      · exact (hp2 h).elim
      · omega
    exact hp3.trans (Nat.le_self_pow (by omega) p)
  obtain ⟨j, hj⟩ := hodd
  by_contra hlt
  push Not at hlt
  have hq : p ^ m = 3 ∨ p ^ m = 5 := by omega
  rcases hq with hq | hq <;> rw [hq] at h16 <;> norm_num at h16

theorem le_card_of_lieModel_psl2_sixteen {Z : Type} [Group Z] {p m : ℕ} (hp2 : p ≠ 2)
    (h16 : 16 ∣ p ^ (2 * m) - 1) (h : Blueprint.LieModel Z .PSL 2 p m) : 168 ≤ Nat.card Z := by
  obtain ⟨hp, -, h4, F', _, _, hF', ⟨e⟩⟩ := exists_psl2_of_lieModel h
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F') :=
    AutL2Facts.isOddPrimePower_of hp hp2 (by
      by_contra h0
      push Not at h0
      rw [Nat.lt_one_iff.mp h0, pow_zero] at h4
      omega) hF'
  rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula F' hodd, hF']
  set q := p ^ m with hq
  have hq2 : p ^ (2 * m) = q ^ 2 := by rw [hq, ← pow_mul, mul_comm]
  rw [hq2] at h16
  have hqodd : Odd q := (hp.odd_of_ne_two hp2).pow
  have hq7 : 7 ≤ q := by
    obtain ⟨j, hj⟩ := hqodd
    by_contra hlt
    push Not at hlt
    have hq5 : q = 5 := by omega
    rw [hq5] at h16
    norm_num at h16
  have hmono : 7 * (7 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by
    apply Nat.mul_le_mul hq7
    have : 7 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq7 2
    omega
  omega

end CFSG.ComponentClassification.HarrisLit.Hin
