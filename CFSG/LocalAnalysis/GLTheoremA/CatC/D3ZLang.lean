module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZW
public import CFSG.LieType.Chevalley.LangQuadraticFieldCosetConjugacy
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutTorus

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three

section Lang

variable {K : Type} [Field K] [Finite K]

theorem exists_lang_conj {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = (p ^ e) ^ 2)
    (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e)) (c : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (z : MulAut (adjointGroup Tag.D4 K))
    (hz : z = MulAut.conj c * exactNormalAut Tag.D4 K a δ 0) (hz2 : z * z = 1) :
    ∃ ψ : MulAut (adjointGroup Tag.D4 K), ∀ u : adjointGroup Tag.D4 K,
      ((ψ * z * ψ⁻¹) u : ModGL Tag.D4 K) =
        Units.map (entrywiseHom δ.toRingHom) (u : ModGL Tag.D4 K) := by
  obtain ⟨β, hβ, hg⟩ := (exceptional_Lang_quadratic_field_coset_conjugacy hp he K hK δ.toRingHom
    (fun c => hδ c)).1 Tag.D4
  obtain ⟨-, hdesc⟩ := hg c a
  obtain ⟨ψ, hψ, -⟩ := hdesc z (fun u => by
    rw [hz]
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_exactNormalAut]
    change (c : ModGL Tag.D4 K) * (rootDiagUnit Tag.D4 a * (1 : ModGL Tag.D4 K) *
      Units.map (entrywiseHom δ.toRingHom) (u : ModGL Tag.D4 K) * (1 : ModGL Tag.D4 K)⁻¹ *
        (rootDiagUnit Tag.D4 a)⁻¹) * (c : ModGL Tag.D4 K)⁻¹ = _
    group) hz2
  exact ⟨ψ, hψ⟩

end Lang

section Torsion

variable {K : Type} [Field K] [Finite K]

theorem pow_card_sub_one_eq_one_of_mem_torusGroup {h : ModGL Tag.D4 K}
    (hh : h ∈ torusGroup Tag.D4 K) : h ^ (Nat.card K - 1) = 1 := by
  obtain ⟨c, rfl⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.mem_torusGroup_iff_cartanChar.1 hh
  have hhom : ∀ c' : Fin Tag.D4.rank → Kˣ, rootDiagUnit Tag.D4 (cartanChar c') =
      rootDiagUnitHom Tag.D4 K (CFSG.GH74.GLS.Stage2.Bender.Thm1.cartanCharHom Tag.D4 K c') :=
    fun _ => rfl
  rw [hhom, ← map_pow, ← map_pow]
  have : c ^ (Nat.card K - 1) = 1 := by
    funext i
    simp only [Pi.pow_apply, Pi.one_apply]
    have hcard : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
    rw [← hcard]
    exact pow_card_eq_one'
  rw [this, map_one, map_one]

theorem mem_fixedFieldImage_of_cube {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 3 ^ n)
    (σ : K ≃+* K) {g : ModGL Tag.D4 K} (hg : g ∈ entrywiseFixedGroup Tag.D4 σ) (hg3 : g ^ 3 = 1) :
    g ∈ fixedFieldImage Tag.D4 σ := by
  have hmul := coe_entrywiseFixedGroup_eq_mul (τ := Tag.D4) (σ := σ)
  have hgmem : g ∈ (entrywiseFixedGroup Tag.D4 σ : Set (ModGL Tag.D4 K)) := hg
  rw [hmul] at hgmem
  obtain ⟨h, hh, j, hj, rfl⟩ := hgmem
  have hhΓ : h ∈ entrywiseFixedGroup Tag.D4 σ := entrywiseFixedTorus_le hh
  have hjΓ : j ∈ entrywiseFixedGroup Tag.D4 σ := fixedFieldImage_le hj
  have hm : h ^ (Nat.card K - 1) = 1 :=
    pow_card_sub_one_eq_one_of_mem_torusGroup (Subgroup.mem_inf.1 hh).1
  set G := entrywiseFixedGroup Tag.D4 σ
  haveI : (fixedFieldImage Tag.D4 σ).subgroupOf G |>.Normal := inferInstance
  let h' : G := ⟨h, hhΓ⟩
  let j' : G := ⟨j, hjΓ⟩
  have hj1 : (QuotientGroup.mk j' : G ⧸ (fixedFieldImage Tag.D4 σ).subgroupOf G) = 1 :=
    (QuotientGroup.eq_one_iff j').2 (Subgroup.mem_subgroupOf.2 hj)
  have hq3 : ((QuotientGroup.mk (h' * j') : G ⧸ (fixedFieldImage Tag.D4 σ).subgroupOf G)) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (h' * j') ^ 3 = 1 := Subtype.ext (by simpa using hg3)
    rw [this]; rfl
  have hqm : ((QuotientGroup.mk h' : G ⧸ (fixedFieldImage Tag.D4 σ).subgroupOf G)) ^ (Nat.card K - 1) = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : h' ^ (Nat.card K - 1) = 1 := Subtype.ext (by simpa using hm)
    rw [this]; rfl
  have hqe : (QuotientGroup.mk (h' * j') : G ⧸ (fixedFieldImage Tag.D4 σ).subgroupOf G) =
      QuotientGroup.mk h' := by
    rw [QuotientGroup.mk_mul, hj1, mul_one]
  rw [hqe] at hq3
  have hcop : Nat.Coprime 3 (Nat.card K - 1) := by
    rw [hK]
    have h3 : 3 ∣ 3 ^ n := dvd_pow_self 3 (by omega)
    have h1 : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (fun hd => ?_)
    obtain ⟨q, hq⟩ := hd
    obtain ⟨r, hr⟩ := h3
    omega
  have hq1 : (QuotientGroup.mk h' : G ⧸ (fixedFieldImage Tag.D4 σ).subgroupOf G) = 1 := by
    have d1 : orderOf (QuotientGroup.mk h' : G ⧸ (fixedFieldImage Tag.D4 σ).subgroupOf G) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one hq3
    have d2 : orderOf (QuotientGroup.mk h' : G ⧸ (fixedFieldImage Tag.D4 σ).subgroupOf G) ∣
        Nat.card K - 1 := orderOf_dvd_of_pow_eq_one hqm
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop d1 d2)
  have : h' ∈ (fixedFieldImage Tag.D4 σ).subgroupOf G := (QuotientGroup.eq_one_iff h').1 hq1
  exact mul_mem (Subgroup.mem_subgroupOf.1 this) hj

end Torsion

section Restrict

theorem exists_mulAut_restrict {G H : Type*} [Group G] [Group H] (ι : H →* G)
    (hι : Function.Injective ι) (α : MulAut G) (hα : ι.range.map α.toMonoidHom = ι.range) :
    ∃ β : MulAut H, ∀ h, ι (β h) = α (ι h) := by
  have hmem : ∀ h, ∃ h', ι h' = α (ι h) := fun h => by
    have : α (ι h) ∈ ι.range.map α.toMonoidHom := ⟨ι h, ⟨h, rfl⟩, rfl⟩
    rw [hα] at this
    exact this
  choose f hf using hmem
  have hmul : ∀ a b, f (a * b) = f a * f b := fun a b => by
    apply hι
    rw [hf, map_mul, map_mul, map_mul, hf, hf]
  let φ : H →* H := MonoidHom.mk' f hmul
  have hbij : Function.Bijective φ := by
    constructor
    · intro a b hab
      have h1 : α (ι a) = α (ι b) := by rw [← hf, ← hf]; exact congrArg ι hab
      exact hι (α.injective h1)
    · intro h'
      have : ι h' ∈ ι.range.map α.toMonoidHom := by rw [hα]; exact ⟨h', rfl⟩
      obtain ⟨_, ⟨h, rfl⟩, hh⟩ := this
      refine ⟨h, hι ?_⟩
      change ι (f h) = ι h'
      rw [hf]; exact hh
  exact ⟨MulEquiv.ofBijective φ hbij, fun h => hf h⟩

theorem map_commutator_fixed {G : Type*} [Group G] (e α : MulAut G) (hc : α * e = e * α) :
    (⁅e.toMonoidHom.eqLocus (MonoidHom.id G), e.toMonoidHom.eqLocus (MonoidHom.id G)⁆).map
      α.toMonoidHom =
    ⁅e.toMonoidHom.eqLocus (MonoidHom.id G), e.toMonoidHom.eqLocus (MonoidHom.id G)⁆ := by
  set F := e.toMonoidHom.eqLocus (MonoidHom.id G) with hF
  have key : ∀ β : MulAut G, β * e = e * β → F.map β.toMonoidHom ≤ F := by
    intro β hβ
    rintro _ ⟨x, hx, rfl⟩
    have hx' : e x = x := hx
    have : e (β x) = β x := by
      have := congrArg (fun γ : MulAut G => γ x) hβ
      simp only [MulAut.mul_apply] at this
      rw [← this, hx']
    exact this
  have h1 : F.map α.toMonoidHom ≤ F := key α hc
  have hc' : α⁻¹ * e = e * α⁻¹ := by
    have : α⁻¹ * (α * e) * α⁻¹ = α⁻¹ * (e * α) * α⁻¹ := by rw [hc]
    simpa [mul_assoc] using this.symm
  have h2 : F.map α⁻¹.toMonoidHom ≤ F := key α⁻¹ hc'
  have hFα : F.map α.toMonoidHom = F := by
    refine le_antisymm h1 ?_
    intro x hx
    refine ⟨α⁻¹ x, h2 ⟨x, hx, rfl⟩, ?_⟩
    simp
  rw [Subgroup.map_commutator, hFα]

end Restrict

section Embed

variable {K : Type} [Field K] [Finite K]

@[expose] def fixE (σ : K ≃+* K) : MulAut (adjointGroup Tag.D4 K) :=
  exactNormalAut Tag.D4 K 1 σ 0

theorem coe_fixE (σ : K ≃+* K) (x : adjointGroup Tag.D4 K) :
    (fixE σ x : ModGL Tag.D4 K) = Units.map (entrywiseHom σ.toRingHom) (x : ModGL Tag.D4 K) := by
  rw [fixE, coe_exactNormalAut, rootDiagUnit_one]
  change (1 : ModGL Tag.D4 K) * 1 * _ * (1 : ModGL Tag.D4 K)⁻¹ * (1 : ModGL Tag.D4 K)⁻¹ = _
  simp

@[expose] def embedSub (σ : K ≃+* K) :
    adjointGroup Tag.D4 ↥(fixSubfield σ) →* adjointGroup Tag.D4 K :=
  ((baseChangeGL (τ := Tag.D4) (fixSubfield σ).subtype).comp
    (adjointGroup Tag.D4 ↥(fixSubfield σ)).subtype).codRestrict (adjointGroup Tag.D4 K)
    (fun x => baseChangeGL_mem_adjointGroup _ x.2)

theorem embedSub_injective (σ : K ≃+* K) : Function.Injective (embedSub σ) := by
  intro a b hab
  apply Subtype.ext
  apply baseChangeGL_injective (τ := Tag.D4) (fixSubfield σ).subtype
  exact congrArg Subtype.val hab

theorem range_embedSub (σ : K ≃+* K) :
    (embedSub σ).range = (fixedFieldImage Tag.D4 σ).subgroupOf (adjointGroup Tag.D4 K) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x : ModGL Tag.D4 ↥(fixSubfield σ)), x.2, rfl⟩
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_subgroupOf.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem embedSub_adjX (σ : K ≃+* K) (i : Fin Tag.D4.rank) (c : fixSubfield σ) :
    embedSub σ (adjX Tag.D4 ↥(fixSubfield σ) i c) = adjX Tag.D4 K i (c : K) :=
  Subtype.ext (baseChangeGL_xUnit _ i c)

theorem embedSub_adjY (σ : K ≃+* K) (i : Fin Tag.D4.rank) (c : fixSubfield σ) :
    embedSub σ (adjY Tag.D4 ↥(fixSubfield σ) i c) = adjY Tag.D4 K i (c : K) :=
  Subtype.ext (baseChangeGL_yUnit _ i c)

end Embed

section Stable

variable {K : Type} [Field K] [Finite K]

theorem fixE_eqLocus_map (σ : K ≃+* K) :
    ((fixE σ).toMonoidHom.eqLocus (MonoidHom.id _)).map (adjointGroup Tag.D4 K).subtype =
      entrywiseFixedGroup Tag.D4 σ := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    have := congrArg (fun y : adjointGroup Tag.D4 K => (y : ModGL Tag.D4 K)) hx
    simpa [coe_fixE] using this
  · intro hg
    obtain ⟨hgC, hgf⟩ := hg
    refine ⟨⟨g, hgC⟩, ?_, rfl⟩
    exact Subtype.ext (by simpa [coe_fixE] using hgf)

theorem commutator_fixE (hK : ringChar K ≠ 2) (σ : K ≃+* K) :
    ⁅(fixE σ).toMonoidHom.eqLocus (MonoidHom.id _), (fixE σ).toMonoidHom.eqLocus (MonoidHom.id _)⁆ =
      (fixedFieldImage Tag.D4 σ).subgroupOf (adjointGroup Tag.D4 K) := by
  apply Subgroup.map_injective (adjointGroup Tag.D4 K).subtype_injective
  rw [Subgroup.map_commutator, fixE_eqLocus_map,
    (Chevalley_coordinate_field_fixed_structure Tag.D4 K hK σ).2.2.2.2.2.2.2,
    Subgroup.map_subgroupOf_eq_of_le (le_trans fixedFieldImage_le inf_le_left)]

theorem map_range_embedSub (hK : ringChar K ≠ 2) (σ : K ≃+* K)
    (t : MulAut (adjointGroup Tag.D4 K)) (hc : t * fixE σ = fixE σ * t) :
    (embedSub σ).range.map t.toMonoidHom = (embedSub σ).range := by
  rw [range_embedSub, ← commutator_fixE hK σ]
  exact map_commutator_fixed (fixE σ) t hc

theorem exists_restrict_sub (hK : ringChar K ≠ 2) (σ : K ≃+* K)
    (t : MulAut (adjointGroup Tag.D4 K)) (hc : t * fixE σ = fixE σ * t) :
    ∃ β : MulAut (adjointGroup Tag.D4 ↥(fixSubfield σ)), ∀ x, embedSub σ (β x) = t (embedSub σ x) :=
  exists_mulAut_restrict (embedSub σ) (embedSub_injective σ) t (map_range_embedSub hK σ t hc)

theorem embedSub_pow {σ : K ≃+* K} {t : MulAut (adjointGroup Tag.D4 K)}
    {β : MulAut (adjointGroup Tag.D4 ↥(fixSubfield σ))} (hβ : ∀ x, embedSub σ (β x) = t (embedSub σ x))
    (n : ℕ) (x : adjointGroup Tag.D4 ↥(fixSubfield σ)) :
    embedSub σ ((β ^ n) x) = (t ^ n) (embedSub σ x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply, ih, hβ]

end Stable

section FieldBound

variable {K : Type} [Field K] [Finite K]

theorem card_fixSubfield_sq {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 3 ^ n) {σ : K ≃+* K}
    (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    Even n ∧ (∀ c, σ c = c ^ (3 ^ (n / 2))) ∧ Nat.card (fixSubfield σ) = 3 ^ (n / 2) ∧
      Nat.card (fixSubfield σ) ^ 2 = Nat.card K := by
  obtain ⟨hev, hfr, hcard⟩ := ringEquiv_sq_eq_one_facts Nat.prime_three hn hK hσ2 hσ1
  have hcard' : Nat.card (fixSubfield σ) = 3 ^ (n / 2) := by
    rw [← hcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c => mem_fixSubfield σ)
  refine ⟨hev, hfr, hcard', ?_⟩
  obtain ⟨m, hm⟩ := hev
  rw [hcard', hK, ← pow_mul]
  congr 1
  omega

theorem not_inner_sub [CharP K 3] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 3 ^ n) {σ : K ≃+* K}
    (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) (t : MulAut (adjointGroup Tag.D4 K)) (ht3 : t ^ 3 = 1)
    (hnot : ∀ x : adjointGroup Tag.D4 K, t ≠ MulAut.conj x)
    (β : MulAut (adjointGroup Tag.D4 ↥(fixSubfield σ)))
    (hβ : ∀ x, embedSub σ (β x) = t (embedSub σ x)) :
    ∀ y : adjointGroup Tag.D4 ↥(fixSubfield σ), β ≠ MulAut.conj y := by
  intro j₀ hj₀
  obtain ⟨-, -, -, hkk⟩ := card_fixSubfield_sq hn hK hσ2 hσ1
  set g : adjointGroup Tag.D4 K := embedSub σ j₀ with hg
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun x => embedSub_injective σ ?_
    rw [embedSub_pow hβ, ht3]
    rfl
  have hj3 : j₀ ^ 3 = 1 := by
    have h1 : (MulAut.conj j₀) ^ 3 = 1 := by rw [← hj₀]; exact hβ3
    have h2 : MulAut.conj (j₀ ^ 3) = 1 := by rw [map_pow]; exact h1
    have hc : j₀ ^ 3 ∈ Subgroup.center (adjointGroup Tag.D4 ↥(fixSubfield σ)) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := congrArg (fun γ : MulAut (adjointGroup Tag.D4 ↥(fixSubfield σ)) => γ x) h2
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * j₀ ^ 3 = (j₀ ^ 3 * x * (j₀ ^ 3)⁻¹) * j₀ ^ 3 := by rw [this]
        _ = j₀ ^ 3 * x := by group
    rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hc
    exact hc
  have htg : t g = g := by
    rw [hg, ← hβ, hj₀]
    simp [MulAut.conj_apply]
  have hcomm : t * (MulAut.conj g)⁻¹ = (MulAut.conj g)⁻¹ * t := by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_inv_apply, map_mul, map_inv, htg]
  set w : MulAut (adjointGroup Tag.D4 K) := (MulAut.conj g)⁻¹ * t with hw
  have hw3 : w ^ 3 = 1 := by
    have : w ^ 3 = (MulAut.conj g)⁻¹ ^ 3 * t ^ 3 := by
      rw [hw]
      exact (Commute.mul_pow (show Commute ((MulAut.conj g)⁻¹) t from hcomm.symm) 3)
    rw [this, ht3, mul_one, inv_pow, ← map_pow, hg, ← map_pow, hj3, map_one, map_one, inv_one]
  have hwfix : ∀ x, w (embedSub σ x) = embedSub σ x := by
    intro x
    rw [hw, MulAut.mul_apply, ← hβ, MulAut.conj_inv_apply, hg, ← map_inv, ← map_mul, ← map_mul, hj₀]
    simp only [MulAut.conj_apply, map_mul, map_inv]
    group
  have hwx : ∀ (i : Fin Tag.D4.rank) (c : K), c ∈ fixSubfield σ →
      w (adjX Tag.D4 K i c) = adjX Tag.D4 K i c := by
    intro i c hc
    have := hwfix (adjX Tag.D4 ↥(fixSubfield σ) i ⟨c, hc⟩)
    rwa [embedSub_adjX] at this
  have hwy : ∀ (i : Fin Tag.D4.rank) (c : K), c ∈ fixSubfield σ →
      w (adjY Tag.D4 K i c) = adjY Tag.D4 K i c := by
    intro i c hc
    have := hwfix (adjY Tag.D4 ↥(fixSubfield σ) i ⟨c, hc⟩)
    rwa [embedSub_adjY] at this
  have hw1 : w = 1 := claimW hn hK (fixSubfield σ) hkk w hw3 hwx hwy
  apply hnot g
  have : t = MulAut.conj g * w := by rw [hw]; group
  rw [this, hw1, mul_one]

theorem mulAut_conj_conj {G : Type*} [Group G] (ψ : MulAut G) (x : G) :
    ψ * MulAut.conj x * ψ⁻¹ = MulAut.conj (ψ x) := by
  ext y
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem field_case_card_le [CharP K 3] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 3 ^ n) (σ : K ≃+* K)
    (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) (z : MulAut (adjointGroup Tag.D4 K))
    (c : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (hz : z = MulAut.conj c * exactNormalAut Tag.D4 K a σ 0) (hz2 : z * z = 1)
    (t : MulAut (adjointGroup Tag.D4 K)) (ht3 : t ^ 3 = 1)
    (hnot : ∀ x : adjointGroup Tag.D4 K, t ≠ MulAut.conj x) (hzt : z * t = t * z)
    (A : Subgroup (adjointGroup Tag.D4 K)) (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAz : ∀ x ∈ A, z x = x) (hAt : ∀ x ∈ A, t x = x) : Nat.card A ≤ 3 ^ (2 * n) := by
  obtain ⟨hev, hfr, hcardfix, hkk⟩ := card_fixSubfield_sq hn hK hσ2 hσ1
  set m := n / 2 with hm
  obtain ⟨m', hm'⟩ := hev
  have hm1 : 1 ≤ m := by omega
  have hK' : Nat.card K = (3 ^ m) ^ 2 := by rw [← hkk, hcardfix]
  have hrc : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  obtain ⟨ψ, hψ⟩ := exists_lang_conj Nat.prime_three hm1 hK' σ hfr c a z hz hz2
  have hψe : ψ * z * ψ⁻¹ = fixE σ :=
    MulEquiv.ext fun u => Subtype.ext (by rw [hψ u, coe_fixE])
  set t'' : MulAut (adjointGroup Tag.D4 K) := ψ * t * ψ⁻¹ with ht''
  have hc : t'' * fixE σ = fixE σ * t'' := by
    rw [← hψe, ht'']
    have h1 : t * z = z * t := hzt.symm
    calc ψ * t * ψ⁻¹ * (ψ * z * ψ⁻¹) = ψ * (t * z) * ψ⁻¹ := by group
      _ = ψ * (z * t) * ψ⁻¹ := by rw [h1]
      _ = ψ * z * ψ⁻¹ * (ψ * t * ψ⁻¹) := by group
  have ht''3 : t'' ^ 3 = 1 := by
    rw [ht'', conj_pow, ht3]; group
  have hnot'' : ∀ x : adjointGroup Tag.D4 K, t'' ≠ MulAut.conj x := by
    intro x hx
    apply hnot (ψ⁻¹ x)
    have : t = ψ⁻¹ * t'' * ψ := by rw [ht'']; group
    rw [this, hx]
    have h2 := mulAut_conj_conj ψ⁻¹ x
    rw [← h2]; group
  obtain ⟨β, hβ⟩ := exists_restrict_sub hrc σ t'' hc
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun x => embedSub_injective σ ?_
    rw [embedSub_pow hβ, ht''3]
    rfl
  have hβnot : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (adjointGroup Tag.D4 ↥(fixSubfield σ)) := by
    rintro ⟨y, hy⟩
    exact not_inner_sub hn hK hσ2 hσ1 t'' ht''3 hnot'' β hβ y hy.symm
  set A' : Subgroup (adjointGroup Tag.D4 K) := A.map ψ.toMonoidHom with hA'
  have hA'ab : CFSG.Open.IsElemAbelian 3 A' := d3f_isElemAbelian_map ψ hA
  have hA'fix : ∀ y ∈ A', t'' y = y := by
    rintro _ ⟨x, hx, rfl⟩
    change t'' (ψ x) = ψ x
    rw [ht'']
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [hAt x hx]
  have hA'fixE : ∀ y ∈ A', fixE σ y = y := by
    rintro _ ⟨x, hx, rfl⟩
    change fixE σ (ψ x) = ψ x
    rw [← hψe]
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [hAz x hx]
  have hA'range : A' ≤ (embedSub σ).range := by
    intro y hy
    rw [range_embedSub]
    refine Subgroup.mem_subgroupOf.2 ?_
    refine mem_fixedFieldImage_of_cube hn hK σ ⟨y.2, ?_⟩ ?_
    · have := congrArg (fun u : adjointGroup Tag.D4 K => (u : ModGL Tag.D4 K)) (hA'fixE y hy)
      simpa [coe_fixE] using this
    · have := hA'ab.2 y hy
      simpa using congrArg (fun u : adjointGroup Tag.D4 K => (u : ModGL Tag.D4 K)) this
  set A₀ : Subgroup (adjointGroup Tag.D4 ↥(fixSubfield σ)) := A'.comap (embedSub σ) with hA₀
  have hA₀map : A₀.map (embedSub σ) = A' := Subgroup.map_comap_eq_self hA'range
  have hcard : Nat.card A₀ = Nat.card A := by
    have h1 := Subgroup.card_map_of_injective (embedSub_injective σ) (K := A₀)
    rw [hA₀map] at h1
    have h2 := Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective (K := A)
    exact h1.symm.trans h2
  have hA₀ab : CFSG.Open.IsElemAbelian 3 A₀ := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply embedSub_injective σ
      have := d3f_commute hA'ab x.2 y.2
      simpa [map_mul] using this
    · apply embedSub_injective σ
      rw [map_pow, map_one]
      exact hA'ab.2 _ hx
  have hA₀fix : ∀ x ∈ A₀, β x = x := by
    intro x hx
    apply embedSub_injective σ
    rw [hβ]
    exact hA'fix _ hx
  haveI : Finite ↥(fixSubfield σ) := inferInstance
  haveI : CharP ↥(fixSubfield σ) 3 := charP_three_of_card hcardfix
  have hbound := chev_card_le β hβ3 hβnot A₀ hA₀ab hA₀fix
  rw [hcard] at hbound
  calc Nat.card A ≤ Nat.card ↥(fixSubfield σ) ^ 4 := hbound
    _ = 3 ^ (2 * n) := by
      rw [hcardfix, ← pow_mul]
      congr 1
      omega

end FieldBound

end CFSG.LocalAnalysis.GLTheoremA
