module

public import CFSG.LocalAnalysis.ComponentClassification.HeldBalStatements
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceTypes
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem isPComponent_image_fixed_centralQuotient {A : Type*} [Group A] [Finite A]
    (c : MulAut A) (hc : ∀ x, c (c x) = x) {T : Subgroup A}
    (hTC : T ≤ fixedSubgroup c) (hT : IsPComponent 2 (T.subgroupOf (fixedSubgroup c))) :
    ∃ σ : MulAut (A ⧸ center A), (∀ y, σ (σ y) = y) ∧
      (∀ x : A, σ (QuotientGroup.mk x) = QuotientGroup.mk (c x)) ∧
      T.map (QuotientGroup.mk' (center A)) ≤ fixedSubgroup σ ∧
      IsPComponent 2 ((T.map (QuotientGroup.mk' (center A))).subgroupOf (fixedSubgroup σ)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := center A with hZ
  set π₂ := QuotientGroup.mk' Z with hπ₂
  have hZmap : Z.map c.toMonoidHom = Z := Subgroup.characteristic_iff_map_eq.mp inferInstance c
  set σ : MulAut (A ⧸ Z) := QuotientGroup.congr Z Z c hZmap with hσdef
  have hσ : ∀ y, σ (π₂ y) = π₂ (c y) := fun y => rfl
  have hσ2 : ∀ q, σ (σ q) = q := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z q
    rw [hσ, hσ, hc]
  set C := fixedSubgroup c with hCdef
  set F := fixedSubgroup σ with hFdef
  set I := C.map π₂ with hIdef
  have hIF : I ≤ F := by
    rintro _ ⟨y, hy, rfl⟩
    change σ (π₂ y) = π₂ y
    rw [hσ]
    exact congrArg π₂ hy
  have hInormal : (I.subgroupOf F).Normal :=
    LocalAnalysis.ComponentInitial.fixedImage_normal (π := π₂) (a := c) (α := σ)
      (by rw [hπ₂, QuotientGroup.ker_mk']) (QuotientGroup.mk'_surjective Z) hc hσ
  set P := T.map π₂ with hPdef
  have hPI : P ≤ I := map_mono hTC
  let r₂ : C →* I := (π₂.comp C.subtype).codRestrict I fun y => mem_map_of_mem π₂ y.2
  have hr₂s : Function.Surjective r₂ := by
    rintro ⟨q, hq⟩
    obtain ⟨y, hy, rfl⟩ := hq
    exact ⟨⟨y, hy⟩, rfl⟩
  have hr₂k : r₂.ker ≤ center C := by
    intro y hy
    have h1 : r₂ y = 1 := hy
    have h2 : (y : A) ∈ Z := (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
    rw [mem_center_iff]
    intro w
    exact Subtype.ext (mem_center_iff.mp h2 w)
  have hPI' : IsPComponent 2 (P.subgroupOf I) := by
    have h1 := CatalogueBCentralQuotient.pComponent_map 2 r₂ hr₂s hr₂k _ hT
    have h2 : (T.subgroupOf C).map r₂ = P.subgroupOf I := by
      ext q
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · intro hq
        obtain ⟨y, hy, hyq⟩ := mem_subgroupOf.mp hq
        exact ⟨⟨y, hTC hy⟩, hy, Subtype.ext hyq⟩
    rwa [h2] at h1
  have hPF : P ≤ F := hPI.trans hIF
  have hP : IsPComponent 2 (P.subgroupOf F) := by
    have h1 := (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := P) hIF 2
      Nat.prime_two).mpr hPI'
    exact (CatalogueBPrimeJoin.pComponent_subnormal_overgroup_iff 2 (P.subgroupOf F)
      (I.subgroupOf F) (fun x hx => hPI hx) hInormal.isSubnormal).mp h1
  exact ⟨σ, hσ2, hσ, hPF, hP⟩

@[expose] def CentreTwoPartLe (X : Type) [Group X] (n : ℕ) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
    ∀ S : Sylow 2 (Subgroup.center L), Nat.card S ≤ n

theorem sq_eq_one_of_mem_inf_center {H : Type} [Group H] {M T : Subgroup H} (hTM : T ≤ M)
    (hT : IsHeldKType ↥T) {x : H} (hxT : x ∈ T) (hxZ : x ∈ (center ↥M).map M.subtype) :
    x * x = 1 := by
  obtain ⟨z, hz, rfl⟩ := hxZ
  have hzT : (⟨(z : H), hxT⟩ : ↥T) ∈ center ↥T := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (congrArg (Subtype.val : ↥M → H)
      (Subgroup.mem_center_iff.mp hz ⟨y, hTM y.2⟩))
  exact congrArg Subtype.val (hT.2.2.1 _ hzT)

theorem card_le_of_isPGroup_of_sylow_le {Z : Type*} [Group Z] [Finite Z] {n : ℕ}
    (hZ : ∀ S : Sylow 2 Z, Nat.card S ≤ n) {Q : Subgroup Z} (hQ : IsPGroup 2 Q) :
    Nat.card Q ≤ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  exact (Subgroup.card_le_of_le hS).trans (hZ S)

theorem inf_center_eq_bot_of_sylow_le_one {H : Type} [Group H] [Finite H] {M T : Subgroup H}
    (hTM : T ≤ M) (hT : IsHeldKType ↥T)
    (h1 : ∀ S : Sylow 2 (Subgroup.center ↥M), Nat.card S ≤ 1) :
    T ⊓ (center ↥M).map M.subtype = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxT, hxZ⟩
  have hsq := sq_eq_one_of_mem_inf_center hTM hT hxT hxZ
  obtain ⟨z, hz, rfl⟩ := hxZ
  have hz2 : (⟨z, hz⟩ : ↥(center ↥M)) ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [sq] using hsq
  have hdvd : orderOf (⟨z, hz⟩ : ↥(center ↥M)) ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
  have hp : IsPGroup 2 (Subgroup.zpowers (⟨z, hz⟩ : ↥(center ↥M))) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, by rw [h]; rfl⟩
  have hle := card_le_of_isPGroup_of_sylow_le h1 hp
  rw [Nat.card_zpowers] at hle
  have hone : orderOf (⟨z, hz⟩ : ↥(center ↥M)) = 1 :=
    le_antisymm hle (Nat.pos_of_dvd_of_pos hdvd two_pos)
  rw [orderOf_eq_one_iff] at hone
  have : z = 1 := congrArg (fun w : ↥(center ↥M) => ((w : ↥M) : ↥M)) hone
  rw [Subgroup.mem_bot]
  simp [this]

theorem false_of_centre_le_centre {H : Type} [Group H] [Finite H] {M T : Subgroup H}
    (hTM : T ≤ M) (hT : IsHeldKType ↥T)
    (hZ : (center ↥T).map T.subtype ≤ (center ↥M).map M.subtype)
    (h2 : ∀ S : Sylow 2 (Subgroup.center ↥M), Nat.card S ≤ 2) : False := by
  have hQle : (center ↥T).map (Subgroup.inclusion hTM) ≤ center ↥M := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨w, hw, hwy⟩ := hZ ⟨y, hy, rfl⟩
    have : w = Subgroup.inclusion hTM y := Subtype.ext hwy
    exact this ▸ hw
  have hcard : Nat.card ((center ↥T).map (Subgroup.inclusion hTM)) = 4 := by
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hTM)]
    exact hT.2.1
  set Q : Subgroup ↥(center ↥M) :=
    ((center ↥T).map (Subgroup.inclusion hTM)).subgroupOf (center ↥M) with hQ
  have hQcard : Nat.card Q = 4 := by
    rw [hQ, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv
  have hp : IsPGroup 2 Q := IsPGroup.of_card (n := 2) (by rw [hQcard]; norm_num)
  have := card_le_of_isPGroup_of_sylow_le h2 hp
  rw [hQcard] at this
  omega

theorem center_le_fusionZStar (H : Type*) [Group H] : center H ≤ Open.fusionZStar H := by
  intro x hx
  show QuotientGroup.mk' _ x ∈ center _
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]

theorem ker_eq_bot_of_card_center_four {T P : Type} [Group T] [Group P] [Finite T] [Finite P]
    (hcard : ∀ (K : Type) [Group K], IsL34Type K → Nat.card K = 20160) (hT : IsHeldKType T)
    (hP34 : IsL34Type (P ⧸ Open.fusionZStar P)) (hZP : Nat.card (center P) = 4) (f : T →* P)
    (hf : Function.Surjective f) : f.ker = ⊥ := by
  have hTc : Nat.card T = 20160 * 4 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center T), hcard _ hT.2.2.2, hT.2.1]
  have hPc : 20160 * 4 ≤ Nat.card P := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.fusionZStar P), hcard _ hP34,
      ← hZP]
    exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (center_le_fusionZStar P))
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, hTc] at h1
  refine Subgroup.eq_bot_of_card_le _ (not_lt.mp fun hk => ?_)
  have h2 := Nat.mul_le_mul hPc (show 2 ≤ Nat.card f.ker by omega)
  rw [← h1] at h2
  omega

@[expose] def L34Source (S : Type) [Group S] (P : Subgroup S) : Prop :=
  Blueprint.LieModel S .PSL 3 2 4 ∨
    (Nonempty (S ≃* Blueprint.NativeSporadic.Suz) ∧ Nat.card (center ↥P) = 1) ∨
    (Nonempty (S ≃* Blueprint.NativeSporadic.ON) ∧ Nat.card (center ↥P) = 4) ∨
    Nonempty (S ≃* Blueprint.NativeSporadic.He)

@[expose] def L34ProperFixedRows : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    Blueprint.Catalog S → ∀ (σ : MulAut S) (P : Subgroup S), CatLeaf.ProperFixedComponent σ P →
      IsL34Type (P ⧸ Open.fusionZStar P) → L34Source S P

@[expose] def L34CentreRow (S : Type) [Group S] (P : Subgroup S) : Prop :=
  CentreTwoPartLe S 1 ∨ (Nat.card (center ↥P) = 1 ∧ CentreTwoPartLe S 2) ∨
    Nat.card (center ↥P) = 4

@[expose] def L34CentreRows : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    Blueprint.Catalog S → ∀ (σ : MulAut S) (P : Subgroup S), CatLeaf.ProperFixedComponent σ P →
      IsL34Type (P ⧸ Open.fusionZStar P) → L34CentreRow S P

theorem heldKStableCentre_of_centreRows (hRows : L34CentreRows)
    (hcard : ∀ (K : Type) [Group K], IsL34Type K → Nat.card K = 20160) : HeldKStableCentre := by
  intro H _ _ hK hO t ht M T hM hMt hTM hTp hlt hTtype
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM' : T ≤ M := hTM.trans inf_le_left
  have hMsub : M.IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).1
  have hMO : pPrimeCore 2 ↥M = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hO hMsub
  have hMq : IsQuasisimple ↥M := by
    have h := ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
    exact LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hMO).trans QuotientGroup.quotientBot) h
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htN : t ∈ normalizer (M : Set H) := by
    rw [mem_normalizer_iff]
    intro y
    rw [← UnbalancedLayer.mem_conjugate_iff, hMt]
  set c : MulAut ↥M := M.normalizerMonoidHom ⟨t, htN⟩ with hcdef
  have hcapp : ∀ x : M, ((c x : M) : H) = t * x * t⁻¹ := fun x => rfl
  have hc : ∀ x, c (c x) = x := by
    intro x
    apply Subtype.ext
    rw [hcapp, hcapp]
    calc t * (t * (x : H) * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [htt]; group
  have hfixC : fixedSubgroup c = (M ⊓ centralizer ({t} : Set H)).subgroupOf M := by
    ext x
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf, mem_inf,
      mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hcapp] at h1
      refine ⟨x.2, ?_⟩
      calc (x : H) * t = t * x * t⁻¹ * t := by rw [h1]
        _ = t * x := by group
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      rw [hcapp]
      calc t * (x : H) * t⁻¹ = x * t * t⁻¹ := by rw [hx]
        _ = x := by group
  set T' := T.subgroupOf M with hT'def
  have hT'C : T' ≤ fixedSubgroup c := by
    rw [hfixC]
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact hTM hx
  have hT'p : IsPComponent 2 (T'.subgroupOf (fixedSubgroup c)) := by
    rw [hfixC]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) inf_le_left 2
      Nat.prime_two).mpr hTp
  obtain ⟨σ, hσ2, hσc, hPF, hP⟩ := isPComponent_image_fixed_centralQuotient c hc hT'C hT'p
  set P := T'.map (QuotientGroup.mk' (center ↥M)) with hPdef
  have hPne : P ≠ ⊤ := by
    intro htop
    have hsup : T' ⊔ center ↥M = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : QuotientGroup.mk' (center ↥M) y ∈ P := htop ▸ mem_top _
      obtain ⟨t', ht', hty⟩ := hy
      have hz : t'⁻¹ * y ∈ center ↥M := (QuotientGroup.eq (s := center ↥M)).mp hty
      have : y = t' * (t'⁻¹ * y) := by group
      rw [this]
      exact mul_mem (mem_sup_left ht') (mem_sup_right hz)
    have hT'top : T' = ⊤ := eq_top_of_sup_center_eq_top hMq.1.commutator_eq_top hsup
    have hMT : M ≤ T := fun x hx => by
      have : (⟨x, hx⟩ : ↥M) ∈ T' := hT'top ▸ mem_top _
      exact mem_subgroupOf.mp this
    have hTMeq : T = M := le_antisymm hTM' hMT
    subst hTMeq
    exact lt_irrefl _ hlt
  let f : ↥T →* ↥P :=
    ((QuotientGroup.mk' (center ↥M)).comp (Subgroup.inclusion hTM')).codRestrict P fun x =>
      ⟨⟨x, hTM' x.2⟩, mem_subgroupOf.mpr x.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨y, hy, rfl⟩ := hq
    exact ⟨⟨y, mem_subgroupOf.mp hy⟩, rfl⟩
  obtain ⟨-, -, hTq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 T
    (M ⊓ centralizer ({t} : Set H)) hTM).mp hTp
  obtain ⟨-, -, hPq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 P (fixedSubgroup σ)
    hPF).mp hP
  have hPO : pPrimeCore 2 ↥P ≠ ⊤ := by
    intro htop
    obtain ⟨-, hs, -⟩ := hPq
    have hsub : Subsingleton (↥P ⧸ pPrimeCore 2 ↥P) := QuotientGroup.subsingleton_iff.mpr htop
    have : Nontrivial ((↥P ⧸ pPrimeCore 2 ↥P) ⧸ center (↥P ⧸ pPrimeCore 2 ↥P)) :=
      hs.toNontrivial
    have : Subsingleton ((↥P ⧸ pPrimeCore 2 ↥P) ⧸ center (↥P ⧸ pPrimeCore 2 ↥P)) := by
      constructor
      intro x y
      obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
      obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective _ y
      rw [Subsingleton.elim x' y']
    exact false_of_nontrivial_of_subsingleton ((↥P ⧸ pPrimeCore 2 ↥P) ⧸
      center (↥P ⧸ pPrimeCore 2 ↥P))
  have : Group.IsPerfect ↥T := hTtype.1
  obtain ⟨eZ⟩ := nonempty_fusionZStar_equiv_of_surjective' f hf hTq hPO
  have hP34 : IsL34Type (↥P ⧸ Open.fusionZStar ↥P) :=
    LieType.CurtisTits.lieModel_of_mulEquiv eZ hTtype.isL34_fusionZStar
  have hsimple : IsSimpleGroup (↥M ⧸ center ↥M) := hMq.2.1
  have hcat : Blueprint.Catalog (↥M ⧸ center ↥M) :=
    SectionRank.catalog_of_isKGroupCat_of_surjective hK M (QuotientGroup.mk' (center ↥M))
      (QuotientGroup.mk'_surjective _)
  have hrow := hRows (↥M ⧸ center ↥M) hsimple hMq.2.2 hcat σ P ⟨hσ2, hPF, hP, hPne⟩ hP34
  rcases hrow with h1 | ⟨hZP, h2⟩ | hZP4
  · exact inf_center_eq_bot_of_sylow_le_one hTM' hTtype (h1 ↥M hMq ⟨MulEquiv.refl _⟩)
  ·
    exfalso
    refine false_of_centre_le_centre hTM' hTtype ?_ (h2 ↥M hMq ⟨MulEquiv.refl _⟩)
    rintro _ ⟨z, hz, rfl⟩
    have hfz : f z ∈ center ↥P := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨y, rfl⟩ := hf q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    have hfz1 : f z = 1 := by
      have hbot : center ↥P = ⊥ := Subgroup.eq_bot_of_card_eq _ hZP
      rw [hbot, Subgroup.mem_bot] at hfz
      exact hfz
    have h1 : (QuotientGroup.mk' (center ↥M)) (Subgroup.inclusion hTM' z) = 1 :=
      congrArg Subtype.val hfz1
    exact ⟨Subgroup.inclusion hTM' z, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
  ·
    have hker := ker_eq_bot_of_card_center_four hcard hTtype hP34 hZP4 f hf
    rw [eq_bot_iff]
    rintro x ⟨hxT, ⟨z, hz, hzx⟩⟩
    have hfx : (⟨x, hxT⟩ : ↥T) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show (QuotientGroup.mk' (center ↥M)) (Subgroup.inclusion hTM' ⟨x, hxT⟩) = 1
      have : Subgroup.inclusion hTM' ⟨x, hxT⟩ = z := Subtype.ext hzx.symm
      exact (QuotientGroup.eq_one_iff _).mpr (this ▸ hz)
    rw [hker, Subgroup.mem_bot] at hfx
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hfx

end CFSG.ComponentClassification.GrSLit
