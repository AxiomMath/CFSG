module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolMoved
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedSimple

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_le_coreActionKernel_self {X P : Subgroup G} (hP : IsTwoComponentIn P X) :
    ¬ P ≤ coreActionKernel P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hPq : IsQuasisimple (↥P ⧸ pPrimeCore 2 ↥P) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 P X hP.1).1 hP.2).2.2
  obtain ⟨-, hsimple, -⟩ := hPq
  have hcomm : ∀ x y : ↥P ⧸ pPrimeCore 2 ↥P, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    obtain ⟨o, ho, hoe⟩ := (h a.2).2 b b.2
    have h2 : (a * b)⁻¹ * (b * a) = o := by
      apply Subtype.ext
      have h3 : (o : G) = (b : G)⁻¹ * (a : G)⁻¹ * b * a := hoe
      rw [h3]
      simp only [coe_mul, coe_inv]
      group
    rw [h2]
    exact ho
  have htop : center (↥P ⧸ pPrimeCore 2 ↥P) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => mem_center_iff.mpr fun y => hcomm y x
  have := hsimple.toNontrivial
  obtain ⟨u, v, huv⟩ := exists_pair_ne ((↥P ⧸ pPrimeCore 2 ↥P) ⧸ center (↥P ⧸ pPrimeCore 2 ↥P))
  apply huv
  induction u using QuotientGroup.induction_on with
  | H u =>
  induction v using QuotientGroup.induction_on with
  | H v =>
  rw [QuotientGroup.eq, htop]
  exact mem_top _

theorem eq_of_le_of_isTwoComponentIn {X P F : Subgroup G} (hP : IsTwoComponentIn P X)
    (hF : IsTwoComponentIn F X) (hPF : P ≤ F) : P = F := by
  by_contra hne
  exact not_le_coreActionKernel_self hP (hPF.trans (le_coreActionKernel_of_ne hP hF hne))

omit [Finite G] in
theorem commutator_mem_pPrimeCore {X : Subgroup G} {a b : G} (ha : a ∈ X) (hb : b ∈ X)
    (h : Commute (QuotientGroup.mk' (pPrimeCore 2 ↥X) (⟨a, ha⟩ : ↥X))
      (QuotientGroup.mk' (pPrimeCore 2 ↥X) (⟨b, hb⟩ : ↥X))) :
    (⟨a⁻¹ * b⁻¹ * a * b, mul_mem (mul_mem (mul_mem (inv_mem ha) (inv_mem hb)) ha) hb⟩ : ↥X) ∈
      pPrimeCore 2 ↥X := by
  rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥X), MonoidHom.mem_ker]
  have e : (⟨a⁻¹ * b⁻¹ * a * b, mul_mem (mul_mem (mul_mem (inv_mem ha) (inv_mem hb)) ha) hb⟩ :
      ↥X) = (⟨a, ha⟩ : ↥X)⁻¹ * (⟨b, hb⟩ : ↥X)⁻¹ * ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ _ (QuotientGroup.mk' _ _),
    h.eq]
  group

theorem moved_facts {X R V : Subgroup G} (hRX : R ≤ twoLayerIn X) (hR : ⁅R, R⁆ = R)
    (hRq : IsQuasisimple (↥R ⧸ pPrimeCore 2 ↥R)) (hV : IsTwoComponentIn V X)
    (hmove : ¬ R ≤ coreActionKernel V) :
    Nat.card (↥R ⧸ Open.fusionZStar ↥R) ≤ Nat.card (↥V ⧸ Open.fusionZStar ↥V) ∧
    (Nat.card (↥R ⧸ Open.fusionZStar ↥R) = Nat.card (↥V ⧸ Open.fusionZStar ↥V) →
      Nonempty (↥R ⧸ Open.fusionZStar ↥R ≃* ↥V ⧸ Open.fusionZStar ↥V) ∧
      ∀ g ∈ X, (∀ r ∈ R, Commute g r) → g ∈ normalizer (V : Set G) →
        g ∈ coreActionKernel V) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRX' : R ≤ X := hRX.trans (map_subtype_le _)
  have hRperf : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hR
  obtain ⟨hVX, hVp⟩ := hV
  set O := pPrimeCore 2 ↥X with hO
  have hOn : O.Normal := pPrimeCore_normal
  set π := QuotientGroup.mk' O with hπ
  let ρ : ↥R →* ↥X ⧸ O := π.comp (Subgroup.inclusion hRX')
  have hρ : ∀ r : ↥R, ρ r = π ⟨r, hRX' r.2⟩ := fun _ => rfl
  set Rb := ρ.range with hRb
  have hRE : Rb ≤ layer (↥X ⧸ O) := by
    refine le_trans ?_ (LBalance.Quot.map_pLayer_eq_layer_quotient (H := ↥X) (p := 2)).le
    rintro _ ⟨r, rfl⟩
    refine mem_map_of_mem π ?_
    obtain ⟨y, hy, hyr⟩ := hRX r.2
    have : Subgroup.inclusion hRX' r = y := Subtype.ext hyr.symm
    rw [this]
    exact hy
  obtain ⟨K, hK, -, hKmap, -⟩ := id hVp
  set E := layer (↥X ⧸ O) with hE
  set Z := E ⊓ centralizer (K : Set (↥X ⧸ O)) with hZ
  have hKE : K ≤ E := component_le_layer hK
  have hEK : E ≤ normalizer (K : Set (↥X ⧸ O)) := layer_le_normalizer hK
  have hZE : Z ≤ E := inf_le_left
  have hZn : (Z.subgroupOf E).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hZE]
    refine Sol76.le_normalizer_of_forall_conj_mem fun c hc x hx => ?_
    obtain ⟨hxE, hxC⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨mul_mem (mul_mem hc hxE) (inv_mem hc), ?_⟩
    rw [mem_centralizer_iff]
    intro k hk
    have hk' : c⁻¹ * k * c ∈ K := by
      have := (mem_normalizer_iff.mp (hEK (inv_mem hc)) k).mp hk
      simpa using this
    have h1 : c⁻¹ * k * c * x = x * (c⁻¹ * k * c) := (mem_centralizer_iff.mp hxC) _ hk'
    calc k * (c * x * c⁻¹) = c * (c⁻¹ * k * c * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * k * c)) * c⁻¹ := by rw [h1]
      _ = c * x * c⁻¹ * k := by group
  set φ := QuotientGroup.mk' (Z.subgroupOf E) with hφ
  let φK : ↥K →* ↥E ⧸ Z.subgroupOf E := φ.comp (Subgroup.inclusion hKE)
  have hφKsurj : Function.Surjective φK := by
    intro q
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf E) q
    obtain ⟨u, hu, huc⟩ := Sol76.exists_mem_mul_centralizer hK e.2
    refine ⟨⟨u, hu⟩, ?_⟩
    change φ ⟨u, hKE hu⟩ = φ e
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    refine mem_inf.mpr ⟨mul_mem (inv_mem (hKE hu)) e.2, ?_⟩
    rw [mem_centralizer_iff]
    intro k hk
    exact (huc k hk).eq
  have hφKker : φK.ker = center ↥K := by
    ext k
    rw [MonoidHom.mem_ker, mem_center_iff]
    change φ ⟨k, hKE k.2⟩ = 1 ↔ _
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    constructor
    · intro h l
      exact Subtype.ext ((mem_centralizer_iff.mp (mem_inf.mp h).2) l l.2)
    · intro h
      refine mem_inf.mpr ⟨hKE k.2, ?_⟩
      rw [mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (h ⟨l, hl⟩)
  have hQcard : Nat.card (↥E ⧸ Z.subgroupOf E) = (center ↥K).index := by
    rw [← hφKker, index_ker, (MonoidHom.range_eq_top_of_surjective _ hφKsurj), card_top]
  let ρE : ↥R →* ↥E := ρ.codRestrict E fun r => hRE ⟨r, rfl⟩
  let ψ : ↥R →* ↥E ⧸ Z.subgroupOf E := φ.comp ρE
  have hψ : ∀ r : ↥R, ψ r = φ ⟨ρ r, hRE ⟨r, rfl⟩⟩ := fun _ => rfl
  have hRN : ∀ r ∈ R, r ∈ normalizer (V : Set G) := by
    intro r hr
    obtain ⟨y, hy, rfl⟩ := hRX hr
    exact mem_normalizer_of_subgroupOf hVX (GrSLit.pLayer_le_normalizer_of_isPComponent hVp hy)
  have hcV : ∀ g ∈ normalizer (V : Set G), ∀ v ∈ V, v⁻¹ * g⁻¹ * v * g ∈ V := by
    intro g hg v hv
    have h2 : g⁻¹ * v * g ∈ V := by
      have := (mem_normalizer_iff.mp (inv_mem hg) v).mp hv
      simpa [mul_assoc] using this
    rw [show v⁻¹ * g⁻¹ * v * g = v⁻¹ * (g⁻¹ * v * g) by group]
    exact mul_mem (inv_mem hv) h2
  have hvK : ∀ v (hv : v ∈ V), π ⟨v, hVX hv⟩ ∈ K := fun v hv =>
    hKmap ▸ mem_map_of_mem π (mem_subgroupOf.mpr hv)
  have hRK : ¬ Rb ≤ centralizer (K : Set (↥X ⧸ O)) := by
    intro hc
    apply hmove
    intro r hr
    refine ⟨hRN r hr, fun v hv => ?_⟩
    refine mem_oddCoreIn_of_mem_pPrimeCore hVX (hcV r (hRN r hr) v hv) ?_
    have hrc : π ⟨r, hRX' hr⟩ ∈ centralizer (K : Set (↥X ⧸ O)) := hc ⟨⟨r, hr⟩, rfl⟩
    exact commutator_mem_pPrimeCore (hVX hv) (hRX' hr)
      ((mem_centralizer_iff.mp hrc) _ (hvK v hv))
  have hkerψ : ψ.ker ≠ ⊤ := by
    intro h
    apply hRK
    rintro _ ⟨r, rfl⟩
    have h1 : ψ r = 1 := MonoidHom.mem_ker.mp (by rw [h]; exact mem_top r)
    rw [hψ, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    exact (mem_inf.mp h1).2
  have hleZ : ψ.ker ≤ Open.fusionZStar ↥R :=
    Sol76.le_fusionZStar_of_normal hRperf hRq ψ.normal_ker hkerψ
  have hVcard : Nat.card (↥V ⧸ Open.fusionZStar ↥V) = (center ↥K).index := by
    have h1 := Sol76.index_fusionZStar_eq_index_center hK.2 hKmap
    have h2 : Nat.card (↥V ⧸ Open.fusionZStar ↥V) =
        Nat.card (↥(V.subgroupOf X) ⧸ Open.fusionZStar ↥(V.subgroupOf X)) :=
      Nat.card_congr (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hVX)).symm.toEquiv
    rw [h2]
    exact h1
  have hrange_le : Nat.card (↥R ⧸ Open.fusionZStar ↥R) ≤ Nat.card ψ.range := by
    change (Open.fusionZStar ↥R).index ≤ _
    rw [← index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (index_dvd_of_le hleZ)
  have hrange_card : Nat.card ψ.range ≤ Nat.card (↥E ⧸ Z.subgroupOf E) :=
    (card_le_of_le le_top).trans (by rw [card_top])
  refine ⟨?_, fun heq => ?_⟩
  · rw [hVcard, ← hQcard]
    exact hrange_le.trans hrange_card
  have hrange : ψ.range = ⊤ := by
    apply eq_top_of_card_eq
    apply le_antisymm hrange_card
    rw [hQcard, ← hVcard, ← heq]
    exact hrange_le
  have hψsurj : Function.Surjective ψ := MonoidHom.range_eq_top.mp hrange
  have hQne : pPrimeCore 2 (↥E ⧸ Z.subgroupOf E) ≠ ⊤ := by
    intro htop
    have hodd : Odd (Nat.card (↥E ⧸ Z.subgroupOf E)) := by
      have h1 := pPrimeCore_coprime_card (p := 2) (G := ↥E ⧸ Z.subgroupOf E)
      rw [htop, card_top] at h1
      exact Nat.coprime_two_left.mp h1
    have hsolv : Group.IsSolvable (↥E ⧸ Z.subgroupOf E) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hperf : Group.IsPerfect (↥E ⧸ Z.subgroupOf E) :=
      Group.IsPerfect.ofSurjective (f := ψ) hψsurj
    obtain ⟨r, hr⟩ : ∃ r : ↥R, ψ r ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hkerψ (eq_top_iff.mpr fun r _ => MonoidHom.mem_ker.mpr (hall r))
    have : Nontrivial (↥E ⧸ Z.subgroupOf E) := ⟨⟨ψ r, 1, hr⟩⟩
    exact Group.IsPerfect.not_isSolvable (G := ↥E ⧸ Z.subgroupOf E) hsolv
  obtain ⟨e₁⟩ := GrSLit.nonempty_fusionZStar_equiv_of_surjective' ψ hψsurj hRq hQne
  let fVK : ↥V →* ↥K := (π.comp (Subgroup.inclusion hVX)).codRestrict K fun v => hvK v v.2
  have hfVK : Function.Surjective fVK := by
    rintro ⟨k, hk⟩
    rw [← hKmap] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    exact ⟨⟨x, mem_subgroupOf.mp hx⟩, rfl⟩
  have hVperf : Group.IsPerfect ↥V :=
    Subgroup.isPerfect_iff.mpr (UnbalancedCorr.commutator_eq_of_isPComponent hVX hVp)
  have hVq : IsQuasisimple (↥V ⧸ pPrimeCore 2 ↥V) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 V X hVX).1 hVp).2.2
  obtain ⟨e₂⟩ := GrSLit.nonempty_fusionZStar_equiv_of_surjective' (φK.comp fVK)
    (hφKsurj.comp hfVK) hVq hQne
  refine ⟨⟨e₁.trans e₂.symm⟩, fun g hgX hgR hgV => ?_⟩
  set gb : ↥X ⧸ O := π ⟨g, hgX⟩ with hgb
  have hgK : K.map (MulAut.conj gb).toMonoidHom = K := by
    have h1 : ∀ x ∈ K, gb * x * gb⁻¹ ∈ K := by
      intro x hx
      rw [← hKmap] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨⟨g, hgX⟩ * y * ⟨g, hgX⟩⁻¹, mem_subgroupOf.mpr ?_,
        by simp [hgb, hπ, QuotientGroup.mk'_apply]; rfl⟩
      have := (mem_normalizer_iff.mp hgV (y : G)).mp (mem_subgroupOf.mp hy)
      simpa using this
    have h2 : ∀ x ∈ K, gb⁻¹ * x * gb ∈ K := by
      intro x hx
      rw [← hKmap] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨⟨g, hgX⟩⁻¹ * y * ⟨g, hgX⟩, mem_subgroupOf.mpr ?_,
        by simp [hgb, hπ, QuotientGroup.mk'_apply]; rfl⟩
      have := (mem_normalizer_iff.mp (inv_mem hgV) (y : G)).mp (mem_subgroupOf.mp hy)
      simpa using this
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact h1 x hx
    · intro x hx
      refine ⟨gb⁻¹ * x * gb, h2 x hx, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hRg : ∀ j ∈ Rb, Commute gb j := by
    rintro _ ⟨r, rfl⟩
    rw [hρ, hgb]
    exact Commute.map (Subtype.ext (hgR r r.2).eq) π
  have hcov : ∀ k ∈ K, ∃ j ∈ Rb, ∀ x ∈ K, Commute x (j⁻¹ * k) := by
    intro k hk
    obtain ⟨j, hj⟩ : φ ⟨k, hKE hk⟩ ∈ ψ.range := hrange ▸ mem_top _
    refine ⟨ρ j, ⟨j, rfl⟩, fun x hx => ?_⟩
    rw [hψ, hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_subgroupOf] at hj
    exact mem_centralizer_iff.mp (mem_inf.mp hj).2 x hx
  have hfix := Sol76.commute_of_forall_mul (Subgroup.isPerfect_iff.mp hK.1.1) hgK hRg hcov
  refine ⟨hgV, fun v hv => ?_⟩
  refine mem_oddCoreIn_of_mem_pPrimeCore hVX (hcV g hgV v hv) ?_
  exact commutator_mem_pPrimeCore (hVX hv) hgX (hfix _ (hvK v hv)).symm

end CFSG.ComponentClassification.Foote5.SolMax
