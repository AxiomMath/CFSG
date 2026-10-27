module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcData
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Datum
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTriD4Conj
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTriDiag
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.RecipeExcLang
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open scoped commutatorElement

@[expose] def l154ExcTwE6 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedE6 q => q.p = 2 | _ => False

@[expose] def l154ExcTriD4 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .trialityD4 q => q.p = 2 | _ => False

section Centerless

theorem excTw_mk_injective {M : Type} [Group M] {H : Subgroup M} (hZ : Subgroup.center H = ⊥) :
    Function.Injective (LargeEvenCenterMk H) := fun a b hab => by
  simpa only [centerQuotEquivOfBot_mk] using congrArg (centerQuotEquivOfBot hZ) hab

theorem excTw_conj_injective {H : Type} [Group H] (hZ : Subgroup.center H = ⊥) :
    Function.Injective (MulAut.conj : H →* MulAut H) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  have hc : a ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut H => φ g) (MonoidHom.mem_ker.1 ha)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * a = (a * g * a⁻¹) * a := by rw [h1]
      _ = a * g := by group
  rwa [hZ, Subgroup.mem_bot] at hc

end Centerless

section LieModel

theorem excTwE6_exists_lieModel {X : Type} [Group X] (hQ : catalogIs X l154ExcTwE6) :
    ∃ f : ℕ, LieModel X .twistedE6 0 2 f := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | cyclic p hp => simp [l154ExcTwE6, onLie] at hi
  | alternating n hn => simp [l154ExcTwE6, onLie] at hi
  | sporadic s => simp [l154ExcTwE6, onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | twistedE6 q =>
      have hp : q.p = 2 := by simpa [l154ExcTwE6, onLie] using hi
      exact ⟨q.exponent, hp ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_twistedE6 q hv e⟩
    | _ => simp [l154ExcTwE6, onLie] at hi

theorem excTriD4_exists_lieModel {X : Type} [Group X] (hQ : catalogIs X l154ExcTriD4) :
    ∃ f : ℕ, LieModel X .trialityD4 0 2 f := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | cyclic p hp => simp [l154ExcTriD4, onLie] at hi
  | alternating n hn => simp [l154ExcTriD4, onLie] at hi
  | sporadic s => simp [l154ExcTriD4, onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | trialityD4 q =>
      have hp : q.p = 2 := by simpa [l154ExcTriD4, onLie] using hi
      exact ⟨q.exponent, hp ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_trialityD4 q hv e⟩
    | _ => simp [l154ExcTriD4, onLie] at hi

end LieModel

theorem excTwE6_tag_of_markTag {lab : GLALabel} (h : markTag lab = .twistedE6) :
    lab.tag = .twE6 := by
  obtain ⟨tg, r, n⟩ := lab
  unfold CFSG.StandardType.markTag at h
  cases tg <;> simp only at h ⊢ <;> (try split_ifs at h) <;> simp_all

theorem excTriD4_tag_of_markTag {lab : GLALabel} (h : markTag lab = .trialityD4) :
    lab.tag = .triD4 := by
  obtain ⟨tg, r, n⟩ := lab
  unfold CFSG.StandardType.markTag at h
  cases tg <;> simp only at h ⊢ <;> (try split_ifs at h) <;> simp_all

section LabelR

theorem excTw_tag_of_hasLabel (hR : GGLabelRigidInput) {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) {t : StatedLieTag} {tg : LargeEvenLieTag}
    (hexc : K1419E.ExcStated t) (htg : ∀ lab : GLALabel, markTag lab = t → lab.tag = tg)
    (hm : ∃ f, LieModel X t 0 2 f) {labK : GLALabel} (hK : Y10F.HasLabel X (· = labK)) :
    labK.tag = tg := by
  have hcen : Subgroup.center X = ⊥ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.center_eq_bot_of_isSimpleGroup_of_noncomm hs hnab
  have hperf : commutator X = ⊤ := (K144I.openQuasisimple_of_simple hs hnab).1
  obtain ⟨f, hm'⟩ := hm
  have hmark := Canonical.largeEvenMarking_of_lieModel_centerQuot hperf
    (LieModel.of_mulEquiv (CanonInn.quotCenterEquivOfBot hcen).symm hm')
  obtain ⟨lab, ⟨hlt, -, -, -⟩, hlab⟩ := K144I.exists_label_of_hasLabel hmark
  have hE := K1419E.excGLATag_of_markTag hexc hlt
  obtain ⟨hlam, -, hGlab⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hlab
  obtain ⟨hlamK, -, hGlabK⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hK
  have heq := K1419E.eq_of_ggLabelIso_exc
    (hR lab labK (X ⧸ Subgroup.center X) hlam hlamK hGlab hGlabK) hE
  rw [heq]
  exact htg lab hlt

end LabelR

section LabelRG

theorem excTw_tag_of_marking {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω} {lab : GLALabel}
    {t : StatedLieTag} {tg : LargeEvenLieTag} (hlab : Y10F.HasLabel (PQuot p S) (· = lab))
    (hexc : K1419E.ExcStated t) (htg : ∀ lab : GLALabel, markTag lab = t → lab.tag = tg)
    (hm : ∃ f, LieModel (PSimple p S) t 0 2 f) : lab.tag = tg := by
  obtain ⟨hperf, hsimple⟩ := Y10F.hasLabel_isQuasisimple hlab
  haveI : IsSimpleGroup (PSimple p S) := hsimple
  exact excTw_tag_of_hasLabel ggLabelRigidInput_holds this
    (exists_mul_ne_mul_centerQuot_of_perfect hperf inferInstance) hexc htg hm
    (Y10F.hasLabel_centerQuot hlab)

end LabelRG

section LabelRGTw

theorem excTwE6_tag_of_marking {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω} {lab : GLALabel}
    (hlab : Y10F.HasLabel (PQuot p S) (· = lab)) (hQ : catalogIs (PSimple p S) l154ExcTwE6) :
    lab.tag = .twE6 :=
  excTw_tag_of_marking hlab (by simp [K1419E.ExcStated]) (fun _ => excTwE6_tag_of_markTag)
    (excTwE6_exists_lieModel hQ)

theorem excTriD4_tag_of_marking {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω} {lab : GLALabel}
    (hlab : Y10F.HasLabel (PQuot p S) (· = lab)) (hQ : catalogIs (PSimple p S) l154ExcTriD4) :
    lab.tag = .triD4 :=
  excTw_tag_of_marking hlab (by simp [K1419E.ExcStated]) (fun _ => excTriD4_tag_of_markTag)
    (excTriD4_exists_lieModel hQ)

end LabelRGTw

section Transport


theorem excTw_transport {t : TwistTag} {K : Type} [Field K] {n : ℕ} (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hperf : ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ =
      graphFixedRootGroup t K σ.toRingHom) {Q : LargeEvenRawCont}
    (h : Q (LargeEvenCenterQuot (LargeEvenTwistedH t.tag.cartan K t.perm n))
      (LargeEvenChevIDImage t.tag.cartan K _) (LargeEvenChevFieldImage t.tag.cartan K _)) :
    Q (LargeEvenCenterQuot (graphFixedRootGroup t K σ.toRingHom))
      (markIDImage (IsRoot t.tag) K (graphFixedRootGroup t K σ.toRingHom))
      (RecipeFieldExcInn.markFieldImage (IsRoot t.tag) K
        (graphFixedRootGroup t K σ.toRingHom)) := by
  have hH : MarkChev.twistedH t.tag.cartan (IsRoot t.tag) K t.perm n =
      graphFixedRootGroup t K σ.toRingHom :=
    (twistedH_eq_commutator K t n σ.toRingHom hσ).trans hperf
  have h1 : ∀ H : Subgroup (LargeEvenChevGL t.tag.cartan K),
      H = MarkChev.twistedH t.tag.cartan (LargeEvenIsRoot t.tag.cartan) K t.perm n →
      Q (LargeEvenCenterQuot H) (LargeEvenChevIDImage t.tag.cartan K H)
        (LargeEvenChevFieldImage t.tag.cartan K H) →
      Q (LargeEvenCenterQuot (MarkChev.twistedH t.tag.cartan (LargeEvenIsRoot t.tag.cartan) K
        t.perm n))
        (markIDImage (LargeEvenIsRoot t.tag.cartan) K
          (MarkChev.twistedH t.tag.cartan (LargeEvenIsRoot t.tag.cartan) K t.perm n))
        (RecipeFieldExcInn.markFieldImage (LargeEvenIsRoot t.tag.cartan) K
          (MarkChev.twistedH t.tag.cartan (LargeEvenIsRoot t.tag.cartan) K t.perm n)) := by
    intro H hH' hQ
    subst hH'
    rw [largeEvenChevIDImage_eq] at hQ
    exact hQ
  have h2 := h1 _ (largeEvenTwistedH_eq t.tag.cartan K t.perm n) h
  have h3 : ∀ S : (Fin t.tag.rank → ℤ) → Prop, LargeEvenIsRoot t.tag.cartan = S →
      Q (LargeEvenCenterQuot (MarkChev.twistedH t.tag.cartan S K t.perm n))
        (markIDImage S K (MarkChev.twistedH t.tag.cartan S K t.perm n))
        (RecipeFieldExcInn.markFieldImage S K (MarkChev.twistedH t.tag.cartan S K t.perm n)) := by
    intro S hS
    subst hS
    exact h2
  have h4 := h3 _ (largeEvenIsRoot_eq_isRoot t.tag)
  suffices key : ∀ A : Subgroup (MarkChev.GLS (IsRoot t.tag) K),
      A = MarkChev.twistedH t.tag.cartan (IsRoot t.tag) K t.perm n →
      Q (LargeEvenCenterQuot A) (markIDImage (IsRoot t.tag) K A)
        (RecipeFieldExcInn.markFieldImage (IsRoot t.tag) K A) from key _ hH.symm
  intro A hA
  subst hA
  exact h4

end Transport

section FieldAut

variable {K : Type} [Field K] [Finite K]

theorem excTw_pow_sq_apply {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ 2) (k : ℕ) (c : K) :
    (φ ^ k) c = c ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', RingAut.mul_apply, ih, hφ, ← pow_mul, ← pow_succ]

theorem excTw_frob_root {n m a p : ℕ} (hp : p.Prime) (hmp : ¬ p ∣ m) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hK : Nat.card K = (2 ^ n) ^ m) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hap : m ∣ a * p + 1) (δ : K ≃+* K) (hδ : orderOf δ = p) :
    ∃ (e k : ℕ) (T : K ≃+* K), e * p = n ∧ 1 ≤ e ∧ (∀ c, T c = c ^ (2 ^ e)) ∧
      δ ^ k = σ ^ a * T ∧ Nat.Coprime k p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hK2 : Nat.card K = 2 ^ (n * m) := by rw [hK, ← pow_mul]
  obtain ⟨φ, hφ, hφord, hφtop, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (Nat.mul_pos hn hm) hK2
  have hφ2 : ∀ c, φ c = c ^ 2 := hφ
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hφtop⟩
  have : Finite (K ≃+* K) :=
    Nat.finite_of_card_ne_zero (by rw [hcardAut]; exact (Nat.mul_pos hn hm).ne')
  have hpnm : p ∣ n * m := by
    rw [← hδ, ← hcardAut]
    exact orderOf_dvd_natCard δ
  have hpn : p ∣ n := ((Nat.Prime.coprime_iff_not_dvd hp).2 hmp).dvd_of_dvd_mul_right hpnm
  obtain ⟨e, he⟩ := hpn
  have hep : e * p = n := by rw [he, mul_comm]
  have he1 : 1 ≤ e := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hep
    omega
  have hen : e < n := by
    have := Nat.mul_le_mul_left e hp.two_le
    omega
  have hσφ : σ = φ ^ n := RingEquiv.ext fun c => by rw [hσ, excTw_pow_sq_apply hφ2]
  have hφnm : φ ^ (n * m) = 1 := by rw [← hφord]; exact pow_orderOf_eq_one φ
  have hτφ : σ ^ a * φ ^ e = φ ^ (n * a + e) := by rw [hσφ, ← pow_mul, ← pow_add]
  have hτp : (σ ^ a * φ ^ e) ^ p = 1 := by
    obtain ⟨k', hk'⟩ := hap
    have hm' : (n * a + e) * p = n * m * k' := by
      calc (n * a + e) * p = n * (a * p) + e * p := by ring
        _ = n * (a * p + 1) := by rw [hep]; ring
        _ = n * m * k' := by rw [hk']; ring
    rw [hτφ, ← pow_mul, hm', pow_mul, hφnm, one_pow]
  have hτ1 : σ ^ a * φ ^ e ≠ 1 := by
    intro h1
    rw [hτφ] at h1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hφord] at hdvd
    have hne : n ∣ e := (Nat.dvd_add_right (dvd_mul_right n a)).1 ((dvd_mul_right n m).trans hdvd)
    exact absurd (Nat.le_of_dvd he1 hne) (by omega)
  have hτord : orderOf (σ ^ a * φ ^ e) = p := orderOf_eq_prime hτp hτ1
  have hzz : Subgroup.zpowers (σ ^ a * φ ^ e) = Subgroup.zpowers δ :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hτord, hδ])
  obtain ⟨k, hk⟩ : ∃ k : ℕ, δ ^ k = σ ^ a * φ ^ e := by
    have h : σ ^ a * φ ^ e ∈ Subgroup.zpowers δ := hzz ▸ Subgroup.mem_zpowers _
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  refine ⟨e, k, φ ^ e, hep, he1, excTw_pow_sq_apply hφ2 e, hk, ?_⟩
  refine ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => hτ1 ?_).symm
  exact hk.symm.trans (orderOf_dvd_iff_pow_eq_one.1 (by rw [hδ]; exact hdvd))

end FieldAut

section Model

variable {K : Type} [Field K] [Finite K]

theorem excTw_exists_fieldActor_of_mem_markField {t : TwistTag} (σ : K ≃+* K)
    {f : MulAut (LargeEvenCenterQuot (graphFixedRootGroup t K σ.toRingHom))}
    (hf : f ∈ RecipeFieldExcInn.markFieldImage (IsRoot t.tag) K
      (graphFixedRootGroup t K σ.toRingHom)) :
    ∃ δ : K ≃+* K,
      MulAut.congr (centerQuotEquivOfBot (exceptional_fixed_center_trivial t K σ)) f =
        fieldActor σ δ := by
  have hZ := exceptional_fixed_center_trivial t K σ
  obtain ⟨δ, hG⟩ := hf
  refine ⟨δ, MulEquiv.ext fun h => excTw_mk_injective hZ ?_⟩
  rw [← congr_centerQuotEquivOfBot_mk hZ f h]
  exact hG h (fieldActor σ δ h) rfl

theorem excTwE6_exists_twConj_of_mem_markID (σ : K ≃+* K)
    {u : MulAut (LargeEvenCenterQuot (twistedE6RootGroup K σ))}
    (hu : u ∈ markIDImage (IsRoot TwistTag.E6.tag) K (twistedE6RootGroup K σ)) :
    ∃ w : twInndiagGroup K σ,
      MulAut.congr (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)) u =
        twConj K σ w := by
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hle : Subgroup.closure (LargeEvenInnSet _ ∪
      markDiagImage (IsRoot TwistTag.E6.tag) K (twistedE6RootGroup K σ)) ≤
        (twConj K σ).range.comap (MulAut.congr (centerQuotEquivOfBot hZ)).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro φ (⟨x, rfl⟩ | ⟨a, ha, -, hG⟩)
    · refine ⟨⟨(centerQuotEquivOfBot hZ x : ModGL TwistTag.E6.tag K),
        graphFixedRootGroup_le_twInndiag σ (centerQuotEquivOfBot hZ x).2⟩, ?_⟩
      rw [twConj_of_mem_C0]
      exact (CFSG.StandardType.mulAut_congr_conj (centerQuotEquivOfBot hZ) x).symm
    · have hconj : ∀ g ∈ twistedE6RootGroup K σ, rootDiagUnit TwistTag.E6.tag a * g *
          (rootDiagUnit TwistTag.E6.tag a)⁻¹ ∈ twistedE6RootGroup K σ := by
        intro g hg
        obtain ⟨h', hh'⟩ := ha ⟨g, hg⟩
        rw [← (markDiag_rel_iff a g h').1 hh']
        exact h'.2
      have hb : IsCompatE6 σ.toRingHom a := TableB.TwE6.compat_of_forall_conj_mem hconj
      refine ⟨⟨rootDiagUnit TwistTag.E6.tag a, rootDiagUnit_mem_twInndiag hb⟩,
        MulEquiv.ext fun h => excTw_mk_injective hZ ?_⟩
      rw [MulEquiv.coe_toMonoidHom, ← congr_centerQuotEquivOfBot_mk hZ φ h]
      exact (hG h _ ((markDiag_rel_iff a _ _).2 rfl)).symm
  obtain ⟨w, hw⟩ := hle hu
  exact ⟨w, hw.symm⟩

theorem excTwE6_fieldActor_injective {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) :
    Function.Injective (fieldActorHom (t := TwistTag.E6) σ) := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  have hΘ' : ∀ δ : K ≃+* K, Θ (fieldActor σ δ) = δ := fun δ =>
    hΘ _ 1 1 δ (by rw [map_one, map_one, one_mul, one_mul])
  intro a b hab
  rw [← hΘ' a, ← hΘ' b]
  exact congrArg Θ hab

theorem excTwE6_orderOf_fieldActor {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (δ : K ≃+* K) :
    orderOf (fieldActor (t := TwistTag.E6) σ δ) = orderOf δ :=
  orderOf_injective (fieldActorHom (t := TwistTag.E6) σ)
    (excTwE6_fieldActor_injective hn hK σ hσ) δ

theorem excTwE6_normalize {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) {Ω : Type} [Group Ω] {S : Subgroup Ω} {x y : Ω}
    (θ₀ : PSimple p S ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ))
    {φx f u : MulAut (LargeEvenCenterQuot (twistedE6RootGroup K σ))}
    (hφx : φx ∈ markIDImage (IsRoot TwistTag.E6.tag) K (twistedE6RootGroup K σ))
    (hf : f ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K
      (twistedE6RootGroup K σ))
    (hu : u ∈ markIDImage (IsRoot TwistTag.E6.tag) K (twistedE6RootGroup K σ))
    (hord : orderOf f = p) (hix : LargeEvenInduces θ₀ (indRel p S x) φx)
    (hiy : LargeEvenInduces θ₀ (indRel p S y) (u * f * u⁻¹)) :
    ∃ (θ : PSimple p S ≃* ↥(twistedE6RootGroup K σ)) (w : twInndiagGroup K σ) (δ : K ≃+* K),
      orderOf δ = p ∧ LargeEvenInduces θ (indRel p S x) (twConj K σ w) ∧
      LargeEvenInduces θ (indRel p S y) (fieldActor σ δ) := by
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  obtain ⟨wx, hwx⟩ := excTwE6_exists_twConj_of_mem_markID σ hφx
  obtain ⟨wu, hwu⟩ := excTwE6_exists_twConj_of_mem_markID σ hu
  obtain ⟨δ, hδ⟩ := excTw_exists_fieldActor_of_mem_markField σ hf
  have hδp : orderOf δ = p := by
    rw [← excTwE6_orderOf_fieldActor hn hK σ hσ δ, ← hδ, MulEquiv.orderOf_eq, hord]
  have h1x := excUntw_induces_trans θ₀ (centerQuotEquivOfBot hZ) hix
  have h1y := excUntw_induces_trans θ₀ (centerQuotEquivOfBot hZ) hiy
  rw [hwx] at h1x
  rw [map_mul, map_mul, map_inv, hwu, hδ] at h1y
  have h2x := excUntw_induces_conj _ (twConj K σ wu)⁻¹ h1x
  have h2y := excUntw_induces_conj _ (twConj K σ wu)⁻¹ h1y
  have e2x : (twConj K σ wu)⁻¹ * twConj K σ wx * ((twConj K σ wu)⁻¹)⁻¹ =
      twConj K σ (wu⁻¹ * wx * wu) := by
    rw [map_mul, map_mul, map_inv, inv_inv]
  have e2y : (twConj K σ wu)⁻¹ * (twConj K σ wu * fieldActor σ δ * (twConj K σ wu)⁻¹) *
      ((twConj K σ wu)⁻¹)⁻¹ = fieldActor σ δ := by group
  rw [e2x] at h2x
  rw [e2y] at h2y
  exact ⟨_, wu⁻¹ * wx * wu, δ, hδp, h2x, h2y⟩

theorem excTwE6_fieldActor_mul_twConj (σ δ : K ≃+* K) (w : twInndiagGroup K σ) :
    fieldActor σ δ * twConj K σ w = twConj K σ (twInndiagFieldAut K σ δ w) * fieldActor σ δ := by
  refine MulEquiv.ext fun c => Subtype.ext ?_
  simp only [MulAut.mul_apply, coe_fieldActor, coe_twConj, coe_twInndiagFieldAut, map_mul, map_inv]

theorem excTwE6_fix_of_commute {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (τ : K ≃+* K) (w : twInndiagGroup K σ)
    (hc : twConj K σ w * fieldActor σ τ = fieldActor σ τ * twConj K σ w) :
    twInndiagFieldAut K σ τ w = w := by
  have h1 := excTwE6_fieldActor_mul_twConj σ τ w
  have h2 : twConj K σ (twInndiagFieldAut K σ τ w) = twConj K σ w := by
    refine mul_right_cancel (b := fieldActor σ τ) ?_
    rw [← h1, ← hc]
  exact NoOffTwE6Three.twConj_injective hn hK σ hσ h2

theorem excTwE6_coe_fieldActor_mul {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (T : K ≃+* K) (c : twistedE6RootGroup K σ) :
    ((fieldActor σ (σ * T) c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * Units.map (entrywiseHom T.toRingHom)
        (c : ModGL TwistTag.E6.tag K) * (diagramMap TwistTag.E6 K)⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hP, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  rw [fieldActor_mul, MulAut.mul_apply, hP, coe_fieldActor]

theorem excTwE6_data_of_induces {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {Ω : Type} [Group Ω] {S : Subgroup Ω} {x y : Ω}
    (hxN : x ∈ Subgroup.normalizer (S : Set Ω)) (hyN : y ∈ Subgroup.normalizer (S : Set Ω))
    (hxp : x ^ p = 1) (hxy : x * y = y * x) (θ : PSimple p S ≃* ↥(twistedE6RootGroup K σ))
    (w : twInndiagGroup K σ) (δ : K ≃+* K) (hδ : orderOf δ = p)
    (hix : LargeEvenInduces θ (indRel p S x) (twConj K σ w))
    (hiy : LargeEvenInduces θ (indRel p S y) (fieldActor σ δ)) :
    ∃ (e k : ℕ) (φx φy : MulAut ↥(twistedE6RootGroup K σ)) (h : ModGL TwistTag.E6.tag K)
      (T : K →+* K), 1 ≤ e ∧ e * p = n ∧ (∀ c, T c = c ^ (2 ^ e)) ∧
      h ∈ twistedE6InndiagGL K σ ∧ h ^ p = 1 ∧
      diagramMap TwistTag.E6 K * Units.map (entrywiseHom T) h * (diagramMap TwistTag.E6 K)⁻¹ = h ∧
      Nat.Coprime k p ∧ (∀ c, (φx c : ModGL TwistTag.E6.tag K) = h * c * h⁻¹) ∧
      (∀ c, (φy c : ModGL TwistTag.E6.tag K) = diagramMap TwistTag.E6 K *
        Units.map (entrywiseHom T) c * (diagramMap TwistTag.E6 K)⁻¹) ∧
      LargeEvenInduces θ (indRel p S x) φx ∧ LargeEvenInduces θ (indRel p S (y ^ k)) φy := by
  have hp2' : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  obtain ⟨e, k, T, hep, he1, hT, hk, hcop⟩ := excTw_frob_root (m := 2) (a := 1) hp
    (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)) hn (by norm_num) hK σ hσ
    (by omega) δ hδ
  rw [pow_one] at hk
  have hyk : y ^ k ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.pow_mem _ hyN k
  have hiy' : LargeEvenInduces θ (indRel p S (y ^ k)) (fieldActor σ (σ * T)) := by
    rw [← hk, ← fieldActorHom_apply (t := TwistTag.E6), map_pow]
    exact excUntw_induces_pow hyN θ hiy k
  have hcomm := excUntw_induces_commute hxN hyk
    (Commute.pow_right (show Commute x y from hxy) k).eq θ hix hiy'
  have hfix := excTwE6_fix_of_commute hn hK σ hσ (σ * T) w hcomm
  have hwp : w ^ p = 1 := by
    have h1 := excUntw_induces_pow_eq_one hxN hxp θ hix
    rw [← map_pow] at h1
    exact NoOffTwE6Three.twConj_injective hn hK σ hσ (h1.trans (map_one _).symm)
  refine ⟨e, k, twConj K σ w, fieldActor σ (σ * T), (w : ModGL TwistTag.E6.tag K), T.toRingHom,
    he1, hep, fun c => hT c, NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ w.2, ?_, ?_,
    hcop, fun c => coe_twConj σ w c, fun c => excTwE6_coe_fieldActor_mul hn hK σ hσ T c, hix,
    hiy'⟩
  · rw [← Subgroup.coe_pow, hwp]
    rfl
  · have h1 := congrArg Subtype.val hfix
    rw [coe_twInndiagFieldAut] at h1
    rw [diagramMap_conj_E6 hK hσ (entrywise_mem_twInndiag T w.2), units_map_entrywiseHom_comp]
    exact h1

theorem excTriD4_fieldActor_injective {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) :
    Function.Injective (fieldActorHom (t := TwistTag.D4) σ) := by
  obtain ⟨-, -, ⟨Θ, hΘ, -⟩, -⟩ := even_triality_exact_automorphism_normal_form hn K hK σ hσ
  have hΘ' : ∀ δ : K ≃+* K, Θ (fieldActor σ δ) = δ := fun δ =>
    hΘ _ 1 δ (by rw [map_one, one_mul])
  intro a b hab
  rw [← hΘ' a, ← hΘ' b]
  exact congrArg Θ hab

theorem excTriD4_orderOf_fieldActor {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (δ : K ≃+* K) :
    orderOf (fieldActor (t := TwistTag.D4) σ δ) = orderOf δ :=
  orderOf_injective (fieldActorHom (t := TwistTag.D4) σ)
    (excTriD4_fieldActor_injective hn hK σ hσ) δ

theorem excTriD4_normalize {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) {Ω : Type} [Group Ω] {S : Subgroup Ω} {x y : Ω}
    (θ₀ : PSimple p S ≃* LargeEvenCenterQuot (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {rx ru : LargeEvenCenterQuot (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    {f : MulAut (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (hf : f ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.D4.tag) K
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hord : orderOf f = p) (hix : LargeEvenInduces θ₀ (indRel p S x) (MulAut.conj rx))
    (hiy : LargeEvenInduces θ₀ (indRel p S y) (MulAut.conj ru * f * (MulAut.conj ru)⁻¹)) :
    ∃ (θ : PSimple p S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (c : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (δ : K ≃+* K),
      orderOf δ = p ∧ LargeEvenInduces θ (indRel p S x) (MulAut.conj c) ∧
      LargeEvenInduces θ (indRel p S y) (fieldActor σ δ) := by
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  obtain ⟨δ, hδ⟩ := excTw_exists_fieldActor_of_mem_markField σ hf
  have hδp : orderOf δ = p := by
    rw [← excTriD4_orderOf_fieldActor hn hK σ hσ δ, ← hδ, MulEquiv.orderOf_eq, hord]
  have h1x := excUntw_induces_trans θ₀ (centerQuotEquivOfBot hZ) hix
  have h1y := excUntw_induces_trans θ₀ (centerQuotEquivOfBot hZ) hiy
  rw [CFSG.StandardType.mulAut_congr_conj] at h1x
  rw [map_mul, map_mul, map_inv, CFSG.StandardType.mulAut_congr_conj, hδ] at h1y
  have h2x := excUntw_induces_conj _ (MulAut.conj (centerQuotEquivOfBot hZ ru))⁻¹ h1x
  have h2y := excUntw_induces_conj _ (MulAut.conj (centerQuotEquivOfBot hZ ru))⁻¹ h1y
  have e2x : (MulAut.conj (centerQuotEquivOfBot hZ ru))⁻¹ *
      MulAut.conj (centerQuotEquivOfBot hZ rx) * ((MulAut.conj (centerQuotEquivOfBot hZ ru))⁻¹)⁻¹ =
        MulAut.conj ((centerQuotEquivOfBot hZ ru)⁻¹ * centerQuotEquivOfBot hZ rx *
          centerQuotEquivOfBot hZ ru) := by
    rw [map_mul, map_mul, map_inv, inv_inv]
  have e2y : (MulAut.conj (centerQuotEquivOfBot hZ ru))⁻¹ *
      (MulAut.conj (centerQuotEquivOfBot hZ ru) * fieldActor σ δ *
        (MulAut.conj (centerQuotEquivOfBot hZ ru))⁻¹) *
      ((MulAut.conj (centerQuotEquivOfBot hZ ru))⁻¹)⁻¹ = fieldActor σ δ := by group
  rw [e2x] at h2x
  rw [e2y] at h2y
  exact ⟨_, _, δ, hδp, h2x, h2y⟩

theorem excTriD4_coe_fieldActor_mul {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (j : ℕ) (T : K ≃+* K)
    (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ((fieldActor σ (σ ^ (2 * j) * T) c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) =
      diagramMap TwistTag.D4 K ^ j * Units.map (entrywiseHom T.toRingHom)
        (c : ModGL TwistTag.D4.tag K) * (diagramMap TwistTag.D4 K ^ j)⁻¹ := by
  have hX : Units.map (entrywiseHom T.toRingHom) (c : ModGL TwistTag.D4.tag K) ∈
      twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    entrywise_mem_twistedFixedGroup_D4 σ T (graphFixedRootGroup_le _ _ _ c.2)
  rw [diagramMap_pow_conj_D4 hK σ hσ j hX, units_map_entrywiseHom_comp]
  rfl

theorem excTriD4_data_of_induces {n p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {Ω : Type} [Group Ω] {S : Subgroup Ω} {x y : Ω}
    (hxN : x ∈ Subgroup.normalizer (S : Set Ω)) (hyN : y ∈ Subgroup.normalizer (S : Set Ω))
    (hxp : x ^ p = 1) (hxy : x * y = y * x)
    (θ : PSimple p S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (c : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (δ : K ≃+* K) (hδ : orderOf δ = p)
    (hix : LargeEvenInduces θ (indRel p S x) (MulAut.conj c))
    (hiy : LargeEvenInduces θ (indRel p S y) (fieldActor σ δ)) :
    ∃ (e j k : ℕ) (φx φy : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (h : ModGL TwistTag.D4.tag K) (T : K →+* K), 1 ≤ e ∧ e * p = n ∧ j * p % 3 = 1 ∧
      (∀ c, T c = c ^ (2 ^ e)) ∧ h ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧ h ^ p = 1 ∧
      diagramMap TwistTag.D4 K ^ j * Units.map (entrywiseHom T) h *
        (diagramMap TwistTag.D4 K ^ j)⁻¹ = h ∧
      Nat.Coprime k p ∧ (∀ c, (φx c : ModGL TwistTag.D4.tag K) = h * c * h⁻¹) ∧
      (∀ c, (φy c : ModGL TwistTag.D4.tag K) = diagramMap TwistTag.D4 K ^ j *
        Units.map (entrywiseHom T) c * (diagramMap TwistTag.D4 K ^ j)⁻¹) ∧
      LargeEvenInduces θ (indRel p S x) φx ∧ LargeEvenInduces θ (indRel p S (y ^ k)) φy := by
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hp0 : p % 3 ≠ 0 := fun h0 =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h0)).symm
  have hjp : p % 3 * p % 3 = 1 := by
    rw [Nat.mul_mod, Nat.mod_mod]
    have h1 : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> rw [h1]
  obtain ⟨e, k, T, hep, he1, hT, hk, hcop⟩ := excTw_frob_root (m := 3) (a := 2 * (p % 3)) hp
    (fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)) hn (by norm_num) hK σ hσ
    (by rw [mul_assoc]; omega) δ hδ
  have hyk : y ^ k ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.pow_mem _ hyN k
  have hiy' : LargeEvenInduces θ (indRel p S (y ^ k)) (fieldActor σ (σ ^ (2 * (p % 3)) * T)) := by
    rw [← hk, ← fieldActorHom_apply (t := TwistTag.D4), map_pow]
    exact excUntw_induces_pow hyN θ hiy k
  have hcomm := excUntw_induces_commute hxN hyk
    (Commute.pow_right (show Commute x y from hxy) k).eq θ hix hiy'
  have hfix : fieldActor σ (σ ^ (2 * (p % 3)) * T) c = c := by
    have h1 : MulAut.conj (fieldActor σ (σ ^ (2 * (p % 3)) * T) c) =
        MulAut.conj c := by
      refine mul_right_cancel (b := fieldActor σ (σ ^ (2 * (p % 3)) * T)) ?_
      rw [← CFSG.LieType.Chevalley.mulAut_mul_conj, ← hcomm]
    exact excTw_conj_injective hZ h1
  have hcp : c ^ p = 1 := by
    have h1 := excUntw_induces_pow_eq_one hxN hxp θ hix
    rw [← map_pow] at h1
    exact excTw_conj_injective hZ (h1.trans (map_one _).symm)
  refine ⟨e, p % 3, k, MulAut.conj c, fieldActor σ (σ ^ (2 * (p % 3)) * T),
    (c : ModGL TwistTag.D4.tag K), T.toRingHom, he1, hep, hjp, fun c => hT c, c.2, ?_, ?_, hcop,
    fun c' => ?_, fun c' => excTriD4_coe_fieldActor_mul hK σ hσ (p % 3) T c', hix, hiy'⟩
  · rw [← Subgroup.coe_pow, hcp]
    rfl
  · rw [← excTriD4_coe_fieldActor_mul hK σ hσ (p % 3) T c, hfix]
  · rfl

end Model

section RawLabel

theorem excTwE6_raw_of_label {lab : GLALabel} (htag : lab.tag = .twE6) (hn : 1 ≤ lab.n)
    {Q : LargeEvenRawCont} (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (2 ^ lab.n) ^ 2 ∧ (∀ c, σ c = c ^ (2 ^ lab.n)) ∧
      Q (LargeEvenCenterQuot (twistedE6RootGroup K σ))
        (markIDImage (IsRoot TwistTag.E6.tag) K (twistedE6RootGroup K σ))
        (RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K (twistedE6RootGroup K σ)) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn
  subst htag
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h ⊢
  obtain ⟨K, instF, instFin, hK, hQ⟩ := h
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcomm, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  exact ⟨K, instF, instFin, σ, hK, hσ, excTw_transport (t := TwistTag.E6) σ hσ hcomm hQ⟩

theorem excTriD4_raw_of_label {lab : GLALabel} (htag : lab.tag = .triD4) (hn : 1 ≤ lab.n)
    {Q : LargeEvenRawCont} (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (2 ^ lab.n) ^ 3 ∧ (∀ c, σ c = c ^ (2 ^ lab.n)) ∧
      markIDImage (IsRoot TwistTag.D4.tag) K (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊆
        LargeEvenInnSet _ ∧
      Q (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
        (markIDImage (IsRoot TwistTag.D4.tag) K (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
        (RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.D4.tag) K
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn
  subst htag
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h ⊢
  obtain ⟨K, instF, instFin, hK, hQ⟩ := h
  haveI : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨-, -, -, -, -, hcomm, -⟩ := even_triality_exact_automorphism_normal_form hn K hK σ hσ
  obtain ⟨hQ', hsub⟩ := excTw_transport (t := TwistTag.D4)
    (Q := fun R _ I F => Q R I F ∧ I ⊆ LargeEvenInnSet R) σ hσ hcomm
    ⟨hQ, TableBExcSmallRest.chevIDImage_subset_inn_triD4 hn K hK⟩
  exact ⟨K, instF, instFin, σ, hK, hσ, hsub, hQ'⟩

end RawLabel

section Marking

theorem excTwE6_raw_marking {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x y : Ω}
    (hQ : catalogIs (PSimple p S) l154ExcTwE6) (hInn : InnDiagOn p (Subgroup.zpowers x) S)
    (hF : FieldOn p y S) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ) (σ : K ≃+* K)
      (θ : PSimple p S ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ))
      (φx f u : MulAut (LargeEvenCenterQuot (twistedE6RootGroup K σ))),
      1 ≤ n ∧ Nat.card K = (2 ^ n) ^ 2 ∧ (∀ c, σ c = c ^ (2 ^ n)) ∧
      φx ∈ markIDImage (IsRoot TwistTag.E6.tag) K (twistedE6RootGroup K σ) ∧
      f ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K (twistedE6RootGroup K σ) ∧
      u ∈ markIDImage (IsRoot TwistTag.E6.tag) K (twistedE6RootGroup K σ) ∧ orderOf f = p ∧
      LargeEvenInduces θ (indRel p S x) φx ∧ LargeEvenInduces θ (indRel p S y) (u * f * u⁻¹) := by
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p S)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p S x) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh x (Subgroup.mem_zpowers x)) hInn.2
  obtain ⟨hperf, lab, hΛ, hraw⟩ := MI.marking_transport (indRel p S x) hdiag hF.2
  have hlab : Y10F.HasLabel (PQuot p S) (fun l : GLALabel => l = lab) :=
    ⟨hperf, lab, hΛ, Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨K, instF, instFin, σ, hK, hσ, hQ'⟩ :=
    excTwE6_raw_of_label (excTwE6_tag_of_marking hlab hQ) hΛ.1 hraw
  obtain ⟨-, -, θ, ⟨-, f, hf, u, hu, hord, hiy⟩, φ, hφ, hix⟩ := hQ'
  exact ⟨K, instF, instFin, lab.n, σ, θ, φ, f, u, hΛ.1, hK, hσ, hφ, hf, hu, hord, hix, hiy⟩

theorem excTriD4_raw_marking {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x y : Ω}
    (hQ : catalogIs (PSimple p S) l154ExcTriD4) (hInn : InnDiagOn p (Subgroup.zpowers x) S)
    (hF : FieldOn p y S) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ) (σ : K ≃+* K)
      (θ : PSimple p S ≃* LargeEvenCenterQuot (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (rx ru : LargeEvenCenterQuot (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (f : MulAut (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))),
      1 ≤ n ∧ Nat.card K = (2 ^ n) ^ 3 ∧ (∀ c, σ c = c ^ (2 ^ n)) ∧ p ≠ 3 ∧
      f ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.D4.tag) K
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧ orderOf f = p ∧
      LargeEvenInduces θ (indRel p S x) (MulAut.conj rx) ∧
      LargeEvenInduces θ (indRel p S y) (MulAut.conj ru * f * (MulAut.conj ru)⁻¹) := by
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p S)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p S x) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh x (Subgroup.mem_zpowers x)) hInn.2
  obtain ⟨hperf, lab, hΛ, hraw⟩ := MI.marking_transport (indRel p S x) hdiag hF.2
  have hlab : Y10F.HasLabel (PQuot p S) (fun l : GLALabel => l = lab) :=
    ⟨hperf, lab, hΛ, Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have htag := excTriD4_tag_of_marking hlab hQ
  obtain ⟨K, instF, instFin, σ, hK, hσ, hsub, hQ'⟩ := excTriD4_raw_of_label htag hΛ.1 hraw
  obtain ⟨-, -, θ, ⟨hp3, f, hf, u, hu, hord, hiy⟩, φ, hφ, hix⟩ := hQ'
  obtain ⟨rx, rfl⟩ := hsub hφ
  obtain ⟨ru, rfl⟩ := hsub hu
  exact ⟨K, instF, instFin, lab.n, σ, θ, rx, ru, f, hΛ.1, hK, hσ,
    hp3.resolve_left fun h => h htag, hf, hord, hix, hiy⟩

theorem excTwE6_marking_data {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x y : Ω} (hQ : catalogIs (PSimple p S) l154ExcTwE6)
    (hxp : x ^ p = 1) (_hyp : y ^ p = 1) (hxy : x * y = y * x)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (e k : ℕ) (σ : K ≃+* K)
      (θ : PSimple p S ≃* ↥(twistedE6RootGroup K σ)) (φx φy : MulAut ↥(twistedE6RootGroup K σ))
      (h : ModGL TwistTag.E6.tag K) (T : K →+* K),
      CharP K 2 ∧ 1 ≤ e ∧ Nat.card K = (2 ^ (e * p)) ^ 2 ∧ (∀ c, σ c = c ^ (2 ^ (e * p))) ∧
      (∀ c, T c = c ^ (2 ^ e)) ∧ h ∈ twistedE6InndiagGL K σ ∧ h ^ p = 1 ∧
      diagramMap TwistTag.E6 K * Units.map (entrywiseHom T) h * (diagramMap TwistTag.E6 K)⁻¹ = h ∧
      Nat.Coprime k p ∧ (∀ c, (φx c : ModGL TwistTag.E6.tag K) = h * c * h⁻¹) ∧
      (∀ c, (φy c : ModGL TwistTag.E6.tag K) = diagramMap TwistTag.E6 K *
        Units.map (entrywiseHom T) c * (diagramMap TwistTag.E6 K)⁻¹) ∧
      LargeEvenInduces θ (indRel p S x) φx ∧ LargeEvenInduces θ (indRel p S (y ^ k)) φy := by
  obtain ⟨K, instF, instFin, n, σ, θ₀, φx₀, f, u, hn, hK, hσ, hφx, hf, hu, hord, hix, hiy⟩ :=
    excTwE6_raw_marking hQ hInn hF
  obtain ⟨θ, w, δ, hδ, hwx, hδy⟩ := excTwE6_normalize hn hK σ hσ θ₀ hφx hf hu hord hix hiy
  obtain ⟨e, k, φx, φy, h, T, he, hep, hT, hh, hhp, hfix, hk, hφx', hφy, hindx, hindy⟩ :=
    excTwE6_data_of_induces hp hp2 hn hK σ hσ (hInn.1 (Subgroup.mem_zpowers x)) hF.1 hxp hxy θ w
      δ hδ hwx hδy
  subst hep
  exact ⟨K, instF, instFin, e, k, σ, θ, φx, φy, h, T,
    charP_two_of_card (m := e * p * 2) (by rw [hK, ← pow_mul]), he, hK, hσ, hT, hh, hhp, hfix, hk,
    hφx', hφy, hindx, hindy⟩

theorem excTriD4_marking_data {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x y : Ω} (hQ : catalogIs (PSimple p S) l154ExcTriD4)
    (hxp : x ^ p = 1) (_hyp : y ^ p = 1) (hxy : x * y = y * x)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (e j k : ℕ) (σ : K ≃+* K)
      (θ : PSimple p S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (φx φy : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (h : ModGL TwistTag.D4.tag K) (T : K →+* K),
      CharP K 2 ∧ 1 ≤ e ∧ j * p % 3 = 1 ∧ Nat.card K = (2 ^ (e * p)) ^ 3 ∧
      (∀ c, σ c = c ^ (2 ^ (e * p))) ∧ (∀ c, T c = c ^ (2 ^ e)) ∧
      h ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧ h ^ p = 1 ∧
      diagramMap TwistTag.D4 K ^ j * Units.map (entrywiseHom T) h *
        (diagramMap TwistTag.D4 K ^ j)⁻¹ = h ∧
      Nat.Coprime k p ∧ (∀ c, (φx c : ModGL TwistTag.D4.tag K) = h * c * h⁻¹) ∧
      (∀ c, (φy c : ModGL TwistTag.D4.tag K) = diagramMap TwistTag.D4 K ^ j *
        Units.map (entrywiseHom T) c * (diagramMap TwistTag.D4 K ^ j)⁻¹) ∧
      LargeEvenInduces θ (indRel p S x) φx ∧ LargeEvenInduces θ (indRel p S (y ^ k)) φy := by
  obtain ⟨K, instF, instFin, n, σ, θ₀, rx, ru, f, hn, hK, hσ, hp3, hf, hord, hix, hiy⟩ :=
    excTriD4_raw_marking hQ hInn hF
  obtain ⟨θ, c, δ, hδ, hcx, hδy⟩ := excTriD4_normalize hn hK σ hσ θ₀ hf hord hix hiy
  obtain ⟨e, j, k, φx, φy, h, T, he, hep, hjp, hT, hh, hhp, hfix, hk, hφx', hφy, hindx, hindy⟩ :=
    excTriD4_data_of_induces hp hp3 hn hK σ hσ (hInn.1 (Subgroup.mem_zpowers x)) hF.1 hxp hxy θ c
      δ hδ hcx hδy
  subst hep
  exact ⟨K, instF, instFin, e, j, k, σ, θ, φx, φy, h, T,
    charP_two_of_card (m := e * p * 3) (by rw [hK, ← pow_mul]), he, hjp, hK, hσ, hT, hh, hhp, hfix,
    hk, hφx', hφy, hindx, hindy⟩

end Marking

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
