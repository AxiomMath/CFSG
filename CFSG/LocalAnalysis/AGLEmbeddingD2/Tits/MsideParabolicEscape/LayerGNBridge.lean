module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerGN
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.LayerOfNotConstrained

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
open scoped commutatorElement

theorem isPSolvable_of_isSolvable' {Y : Type*} [Group Y] {p : ℕ} (hp : p.Prime)
    (hY : Group.IsSolvable Y) : CFSG.HallHigman.IsPSolvable p Y := by
  intro H _ T _ hs
  have := hY
  have := hs
  have hcomm : ∀ a b : ↥H ⧸ T, a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance
  have : IsMulCommutative (↥H ⧸ T) := ⟨⟨hcomm⟩⟩
  have hq : (Nat.card (↥H ⧸ T)).Prime := Group.is_simple_iff_prime_card.mp hs
  change Nat.card (↥H ⧸ T) = p ∨ Nat.Coprime p (Nat.card (↥H ⧸ T))
  by_cases hpq : Nat.card (↥H ⧸ T) = p
  · exact Or.inl hpq
  · exact Or.inr ((Nat.coprime_primes hp hq).mpr (Ne.symm hpq))

theorem ker_eq_top_of_isPSolvable_range {P H : Type} [Group P] [Finite P] [Group H]
    (hP : CFSG.IsQuasisimple P) (hns : ¬ CFSG.HallHigman.IsPSolvable 3 P) (φ : P →* H)
    (hφ : CFSG.HallHigman.IsPSolvable 3 ↥φ.range) : φ.ker = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hP φ.normal_ker with h | h
  · exact h
  · exfalso
    apply hns
    have hk : CFSG.HallHigman.IsPSolvable 3 ↥φ.ker := by
      refine isPSolvable_of_isSolvable' Nat.prime_three (Group.isSolvable_of_comm fun a b => ?_)
      exact Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact Subgroup.mem_center_iff.mp (h b.2) a)
    have hq : CFSG.HallHigman.IsPSolvable 3 (P ⧸ φ.ker) :=
      QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
        (QuotientGroup.quotientKerEquivRange φ).symm hφ
    exact PSolvableClosure.isPSolvable_of_normal φ.ker hk hq

section Frattini

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

@[expose] def jHat (T : Subgroup X) : Subgroup X :=
  (Subgroup.normalClosure ((gnImg T (thompsonJ T) : Subgroup (X ⧸ gnC T)) :
    Set (X ⧸ gnC T))).comap (QuotientGroup.mk' (gnC T))

instance jHat_normal (T : Subgroup X) : (jHat T).Normal :=
  Subgroup.Normal.comap (Subgroup.normalClosure_normal) _

omit [Finite X] in
theorem thompsonJ_le_jHat (T : Subgroup X) : thompsonJ T ≤ jHat T := fun j hj =>
  Subgroup.subset_normalClosure ⟨j, hj, rfl⟩

theorem jHat_sup_normalizer (hT : IsSylowTwoOf T ⊤) :
    jHat T ⊔ Subgroup.normalizer (thompsonJ T : Set X) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowTwoOf (T ⊓ jHat T) (jHat T) :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hT le_top
      (inferInstance : ((jHat T).subgroupOf ⊤).Normal).isSubnormal
  obtain ⟨P, hP⟩ := RankOneRecog.isSylowTwoOf_iff_exists.mp hS
  have hfr := Sylow.normalizer_sup_eq_top P
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hJS : thompsonJ (T ⊓ jHat T) = thompsonJ T :=
    Lin2.thompsonJ_eq_of_le (le_inf hJT (thompsonJ_le_jHat T)) inf_le_left
  have hN : Subgroup.normalizer ((T ⊓ jHat T : Subgroup X) : Set X) ≤
      Subgroup.normalizer (thompsonJ T : Set X) := by
    have hJle : thompsonJ (T ⊓ jHat T) ≤ T ⊓ jHat T := iSup₂_le fun _ hA => hA.1
    have h := normalizer_le_normalizer_of_char hJle (Setup.characteristic_thompsonJ (T ⊓ jHat T))
    rwa [hJS] at h
  rw [hP] at hfr
  rw [eq_top_iff, ← hfr, sup_comm]
  exact sup_le_sup_left hN _

theorem isPSolvable_quotient_of_jHat_le (hX : GNSetting X T) (hloc : GNLocal T) (hT1 : T ≠ ⊥)
    {R : Subgroup X} [R.Normal] (hR : jHat T ≤ R) : CFSG.HallHigman.IsPSolvable 3 (X ⧸ R) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ1 : thompsonJ T ≠ ⊥ := Setup.thompsonJ_ne_bot hX.sylow.2.1 hT1
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hs := PSolvableClosure.isPSolvable_map (QuotientGroup.mk' R)
    (hloc.solv (thompsonJ T) hJ1 hJT (Setup.characteristic_thompsonJ T))
  have htop : (Subgroup.normalizer (thompsonJ T : Set X)).map (QuotientGroup.mk' R) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R x
    have hg : g ∈ jHat T ⊔ Subgroup.normalizer (thompsonJ T : Set X) := by
      rw [jHat_sup_normalizer hX.sylow]
      exact Subgroup.mem_top g
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    refine ⟨z, hz, ?_⟩
    have hy1 : QuotientGroup.mk' R y = 1 := (QuotientGroup.eq_one_iff y).mpr (hR hy)
    rw [map_mul, hy1, one_mul]
  rw [htop] at hs
  exact QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv Subgroup.topEquiv hs

end Frattini

section Image

theorem isPSolvable_quotient' {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    (N : Subgroup Y) [N.Normal] (h : CFSG.HallHigman.IsPSolvable p Y) :
    CFSG.HallHigman.IsPSolvable p (Y ⧸ N) := by
  have h1 := PSolvableClosure.isPSolvable_map (QuotientGroup.mk' N)
    (QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      Subgroup.topEquiv.symm h)
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
  exact QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv Subgroup.topEquiv h1

theorem isPSolvable_subgroup' {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    (h : CFSG.HallHigman.IsPSolvable p Y) (H : Subgroup Y) : CFSG.HallHigman.IsPSolvable p ↥H :=
  PSolvableClosure.isPSolvable_of_le (QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
    Subgroup.topEquiv.symm h) le_top

noncomputable def mulEquivOfKerEq {K A B : Type*} [Group K] [Group A] [Group B]
    (a : K →* A) (b : K →* B) (ha : Function.Surjective a) (hb : Function.Surjective b)
    (h : a.ker = b.ker) : A ≃* B :=
  (QuotientGroup.quotientKerEquivOfSurjective a ha).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientKerEquivOfSurjective b hb))

variable {X : Type} [Group X] [Finite X]

theorem isComponent_map_of_centralizes {Q C K : Subgroup X} [Q.Normal] [C.Normal]
    (hK : ⁅K, K⁆ = K) (hKs : K.IsSubnormal)
    (hq : CFSG.IsQuasisimple ↥(K.map (QuotientGroup.mk' Q)))
    (hns : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(K.map (QuotientGroup.mk' Q)))
    (hC : CFSG.HallHigman.IsPSolvable 3 ↥C)
    (hcomm : ∀ x ∈ K, ∀ q ∈ Q, QuotientGroup.mk' C x * QuotientGroup.mk' C q =
      QuotientGroup.mk' C q * QuotientGroup.mk' C x) :
    CFSG.IsComponent (K.map (QuotientGroup.mk' C)) ∧
      ¬ CFSG.HallHigman.IsPSolvable 3 ↥(K.map (QuotientGroup.mk' C)) ∧
      ∀ k ∈ K, k ∈ C → QuotientGroup.mk' Q k ∈
        (Subgroup.center ↥(K.map (QuotientGroup.mk' Q))).map
          (K.map (QuotientGroup.mk' Q)).subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' Q with hπ
  set f := QuotientGroup.mk' C with hf
  set a : ↥K →* ↥(K.map f) := f.subgroupMap K with ha_def
  set b : ↥K →* ↥(K.map π) := π.subgroupMap K with hb_def
  have ha : Function.Surjective a := f.subgroupMap_surjective K
  have hb : Function.Surjective b := π.subgroupMap_surjective K
  set A₀ : Subgroup ↥(K.map f) := (Q.subgroupOf K).map a with hA₀
  set B₀ : Subgroup ↥(K.map π) := (C.subgroupOf K).map b with hB₀
  have hA₀n : A₀.Normal := Subgroup.Normal.map inferInstance a ha
  have hB₀n : B₀.Normal := Subgroup.Normal.map inferInstance b hb
  have hKC : CFSG.HallHigman.IsPSolvable 3 ↥(C.subgroupOf K) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
      (PSolvableClosure.isPSolvable_of_le hC inf_le_left)
  have hB₀z : B₀ ≤ Subgroup.center ↥(K.map π) :=
    QuasisimpleSolvableNormal.le_center_of_isPSolvable hq hns hB₀n
      (PSolvableClosure.isPSolvable_map b hKC)
  have hA₀z : A₀ ≤ Subgroup.center ↥(K.map f) := by
    rintro _ ⟨q, hq', rfl⟩
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    obtain ⟨x, hx, hxy⟩ := y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hxy]
    exact hcomm x hx q.1 hq'
  have hker : ((QuotientGroup.mk' A₀).comp a).ker = ((QuotientGroup.mk' B₀).comp b).ker := by
    ext k
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨q, hqQ, hqk⟩
      have hqk' : ((q : X) : X ⧸ C) = ((k : X) : X ⧸ C) := congrArg Subtype.val hqk
      have hqQ' : (q : X) ∈ Q := hqQ
      refine ⟨q⁻¹ * k, ?_, ?_⟩
      · show ((q⁻¹ * k : ↥K) : X) ∈ C
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        exact QuotientGroup.eq.mp hqk'
      · apply Subtype.ext
        show π ((q⁻¹ * k : ↥K) : X) = π (k : X)
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
          show π (q : X) = 1 from (QuotientGroup.eq_one_iff (q : X)).mpr hqQ', inv_one, one_mul]
    · rintro ⟨c, hcC, hck⟩
      have hck' : ((c : X) : X ⧸ Q) = ((k : X) : X ⧸ Q) := congrArg Subtype.val hck
      have hcC' : (c : X) ∈ C := hcC
      refine ⟨c⁻¹ * k, ?_, ?_⟩
      · show ((c⁻¹ * k : ↥K) : X) ∈ Q
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        exact QuotientGroup.eq.mp hck'
      · apply Subtype.ext
        show f ((c⁻¹ * k : ↥K) : X) = f (k : X)
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
          show f (c : X) = 1 from (QuotientGroup.eq_one_iff (c : X)).mpr hcC', inv_one, one_mul]
  let e : ↥(K.map f) ⧸ A₀ ≃* ↥(K.map π) ⧸ B₀ :=
    mulEquivOfKerEq _ _
      (by rw [MonoidHom.coe_comp]; exact (QuotientGroup.mk'_surjective A₀).comp ha)
      (by rw [MonoidHom.coe_comp]; exact (QuotientGroup.mk'_surjective B₀).comp hb) hker
  have hqB : CFSG.IsQuasisimple (↥(K.map π) ⧸ B₀) :=
    (CFSG.LocalCores.quasisimple_central_quotient hq B₀ hB₀z).1
  have hqA : CFSG.IsQuasisimple (↥(K.map f) ⧸ A₀) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqB
  have hperf : Group.IsPerfect ↥(K.map f) := by
    refine Subgroup.isPerfect_iff.mpr ?_
    rw [← Subgroup.map_commutator, hK]
  have hqs : CFSG.IsQuasisimple ↥(K.map f) :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperf (QuotientGroup.mk' A₀)
      (QuotientGroup.mk'_surjective A₀) (by rw [QuotientGroup.ker_mk']; exact hA₀z)).mpr hqA
  refine ⟨⟨hqs, hKs.map (QuotientGroup.mk'_surjective C)⟩, fun h => ?_,
    fun k hk hkC => ⟨b ⟨k, hk⟩, hB₀z ⟨⟨k, hk⟩, hkC, rfl⟩, rfl⟩⟩
  set φ : ↥(K.map π) →* ↥(K.map f) ⧸ A₀ := e.symm.toMonoidHom.comp (QuotientGroup.mk' B₀)
  have hφ := ker_eq_top_of_isPSolvable_range hq hns φ
    (isPSolvable_subgroup' (isPSolvable_quotient' A₀ h) _)
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hqA
  obtain ⟨y, hy⟩ := exists_ne (1 : ↥(K.map f) ⧸ A₀)
  obtain ⟨x, rfl⟩ : ∃ x, φ x = y := by
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective B₀ (e y)
    refine ⟨x, ?_⟩
    show e.symm (QuotientGroup.mk' B₀ x) = y
    rw [hx, MulEquiv.symm_apply_apply]
  exact hy ((MonoidHom.mem_ker).mp (hφ ▸ Subgroup.mem_top x))

end Image

section Core

theorem exists_not_comm_of_isQuasisimple {P : Type*} [Group P] (hP : CFSG.IsQuasisimple P) :
    ∃ a b : P, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hP
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨x, y, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

theorem center_map_congr {Y : Type*} [Group Y] {H₁ H₂ : Subgroup Y} (h : H₁ = H₂) :
    (Subgroup.center ↥H₁).map H₁.subtype = (Subgroup.center ↥H₂).map H₂.subtype := by
  subst h
  rfl

theorem isRankTwoLayerType_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsRankTwoLayerType Y) : IsRankTwoLayerType Y' := by
  rcases h with ⟨⟨e'⟩⟩ | ⟨hadm, K, hK, hKf, hc, ⟨e'⟩⟩ | ⟨hadm, K, hK, hKf, hc, ⟨e'⟩⟩
  · exact Or.inl ⟨e.symm.trans e'⟩
  · exact Or.inr (Or.inl ⟨hadm, K, hK, hKf, hc, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨hadm, K, hK, hKf, hc, ⟨e.symm.trans e'⟩⟩)

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem GNLocal.isPSolvable_gnC (hloc : GNLocal T) (hZ1 : omegaOneCenterOf T ≠ ⊥) :
    CFSG.HallHigman.IsPSolvable 3 ↥(gnC T) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine PSolvableClosure.isPSolvable_of_le (hloc.solv _ hZ1 (Setup.omegaOneCenterOf_le T)
    (Setup.characteristic_omegaOneCenterOf T)) ?_
  exact (Subgroup.centralizer_le Subgroup.subset_normalClosure).trans
    (Subgroup.centralizer_le_normalizer _)

theorem jHat_commute (h3J : ThreePrimeJCentral) (hX : GNSetting X T)
    {N : Subgroup (X ⧸ gnC T)} (hN : N.Normal) (hN3 : Nat.Coprime 3 (Nat.card N)) {x : X}
    (hx : x ∈ jHat T) {n : X ⧸ gnC T} (hn : n ∈ N) :
    QuotientGroup.mk' (gnC T) x * n = n * QuotientGroup.mk' (gnC T) x := by
  have hc := h3J X T hX N hN hN3
  have hJ : gnImg T (thompsonJ T) ≤ Subgroup.centralizer (N : Set (X ⧸ gnC T)) := by
    rw [Subgroup.commutator_comm] at hc
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hY := Subgroup.normalClosure_le_normal (N := Subgroup.centralizer (N : Set (X ⧸ gnC T)))
    (s := (gnImg T (thompsonJ T) : Set (X ⧸ gnC T))) hJ
  exact (Subgroup.mem_centralizer_iff.mp (hY hx) n hn).symm

theorem map_inf_comap' {Y Z : Type*} [Group Y] [Group Z] (φ : Y →* Z) (A : Subgroup Y)
    (B : Subgroup Z) : (A ⊓ B.comap φ).map φ = A.map φ ⊓ B := by
  refine le_antisymm (le_inf (Subgroup.map_mono inf_le_left) ?_) ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact hy.2
  · rintro _ ⟨⟨y, hy, rfl⟩, hyB⟩
    exact ⟨y, ⟨hy, hyB⟩, rfl⟩

theorem exists_rankTwo_normal_of_rankTwo (hGN : GlaubermanNilesInput)
    (h3J : ThreePrimeJCentral) (hZ : KFactOddCentreE9) (hX : GNSetting X T) (hloc : GNLocal T)
    (hnc : ¬ CFSG.ABGLocalTools.IsPConstrained 3 X)
    (hrk : ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ → ⁅L, gnImg T (thompsonJ T)⁆ = L →
      ¬ CFSG.HallHigman.IsPSolvable 3 ↥L →
        Subgroup.center ↥L = ⊥ ∧ IsRankTwoLayerType (↥L ⧸ Subgroup.center ↥L)) :
    ∃ K : Subgroup (X ⧸ RankThreeCoreUniqueness.Helpers.primeComplementCore (G := X) 3),
      K.Normal ∧ IsSimpleGroup ↥K ∧ ¬ IsMulCommutative ↥K ∧ IsRankTwoLayerType ↥K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTne : T ≠ ⊥ := by
    intro hT
    apply hnc
    have := hX.subsingleton_of_eq_bot hT
    intro P _ x _
    rw [Subsingleton.elim x 1]
    exact Subgroup.one_mem _
  obtain ⟨T₁, T₂, hpair, -, hthree, -⟩ := hGN X T hX hTne
  have hT₁ := le_of_isGNPair hpair
  have hZ1 : omegaOneCenterOf T ≠ ⊥ := fun h =>
    hpair.ne_bot₁ (le_bot_iff.mp (h ▸ hpair.le_center))
  have hT1 : T ≠ ⊥ := fun h => hpair.ne_bot₁ (le_bot_iff.mp (h ▸ hT₁))
  have hCs := hloc.isPSolvable_gnC hZ1
  set Q : Subgroup X := RankThreeCoreUniqueness.Helpers.primeComplementCore (G := X) 3 with hQ
  set π : X →* X ⧸ Q := QuotientGroup.mk' Q with hπ
  set f : X →* X ⧸ gnC T := QuotientGroup.mk' (gnC T) with hf
  obtain ⟨Kt, hKt⟩ : ∃ K : Subgroup (X ⧸ Q), CFSG.IsComponent K := by
    by_contra h
    push Not at h
    apply OrdinaryProofs.layer_ne_bot_of_not_isPConstrained hnc
    simp only [CFSG.layer.eq_sSup]
    rw [sSup_eq_bot]
    intro K hK
    exact absurd hK (h K)
  have hO3 := OrdinaryProofs.pPrimeCore_three_quotient_eq_bot X
  have hKtns := GNQuotient.not_isPSolvable_of_isComponent hO3 hKt
  have hKtY : Kt ≤ (jHat T).map π := by
    have hR := isPSolvable_quotient_of_jHat_le hX hloc hT1 (R := Q ⊔ jHat T) le_sup_right
    set ρ : X ⧸ Q →* X ⧸ (Q ⊔ jHat T) :=
      QuotientGroup.map Q (Q ⊔ jHat T) (MonoidHom.id X) (fun x hx => le_sup_left (a := Q) hx)
    have hker := ker_eq_top_of_isPSolvable_range hKt.1 hKtns (ρ.comp Kt.subtype)
      (isPSolvable_subgroup' hR _)
    intro k hk
    have hk1 : ρ k = 1 := by
      have : (⟨k, hk⟩ : ↥Kt) ∈ (ρ.comp Kt.subtype).ker := hker ▸ Subgroup.mem_top _
      exact this
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q k
    have hxR : x ∈ Q ⊔ jHat T := (QuotientGroup.eq_one_iff x).mp hk1
    obtain ⟨q, hq, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxR
    refine ⟨y, hy, ?_⟩
    rw [map_mul, show π q = 1 from (QuotientGroup.eq_one_iff q).mpr hq, one_mul]
  set K : Subgroup X := Quasithin.perfectCore (jHat T ⊓ Kt.comap π) with hKdef
  have hKperf : ⁅K, K⁆ = K := Quasithin.perfectCore_perfect _
  have hKY : K ≤ jHat T := (Quasithin.perfectCore_le _).trans inf_le_left
  have hKmap : K.map π = Kt := by
    rw [hKdef, Quasithin.map_perfectCore, map_inf_comap', inf_eq_right.mpr hKtY,
      Quasithin.perfectCore_eq_self_of_perfect (Subgroup.isPerfect_iff.mp hKt.1.1)]
  have hKsn : K.IsSubnormal := by
    have h1 : (jHat T ⊓ Kt.comap π).IsSubnormal :=
      (jHat_normal T).isSubnormal.inf (hKt.2.comap _)
    exact Subgroup.IsSubnormal.trans (Quasithin.perfectCore_le _)
      (Quasithin.perfectCore_normal _).isSubnormal h1
  have hQn : (Q.map f).Normal :=
    Subgroup.Normal.map inferInstance f (QuotientGroup.mk'_surjective _)
  have hQ3 : Nat.Coprime 3 (Nat.card (Q.map f)) :=
    (RankThreeCoreUniqueness.Helpers.primeComplementCore_coprime (G := X) 3).coprime_dvd_right
      (Subgroup.card_map_dvd Q f)
  have hcomm : ∀ x ∈ K, ∀ q ∈ Q, f x * f q = f q * f x := fun x hx q hq =>
    jHat_commute h3J hX hQn hQ3 (hKY hx) ⟨q, hq, rfl⟩
  obtain ⟨hKsc, hKsns, hKC⟩ := isComponent_map_of_centralizes hKperf hKsn (hKmap ▸ hKt.1)
    (hKmap ▸ hKtns) hCs hcomm
  have hKsO : IsComponentOf (K.map f) ⊤ := (CFSG.isComponent_iff_open _).1 hKsc
  set Ks := K.map f with hKs
  set J := gnImg T (thompsonJ T) with hJdef
  have hKsN : Ks.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hns' : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(Ks.map (MulAut.conj g).toMonoidHom) :=
      fun h => hKsns (QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
        (Ks.equivMapOfInjective _ (MulAut.conj g).injective).symm h)
    have heq := eq_of_gn hGN hX hloc (isComponentOf_map_conj hKsO g) hKsO hns' hKsns
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  have hJ : ⁅Ks, J⁆ = Ks := by
    have hle : ⁅Ks, J⁆ ≤ Ks := Subgroup.commutator_le_left Ks J
    have hnorm : (⁅Ks, J⁆.subgroupOf Ks).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
        (Subgroup.normalizer_commutator_ge_left Ks J)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKsc.1 hnorm with h | h
    · refine le_antisymm hle fun x hx => ?_
      have : (⟨x, hx⟩ : ↥Ks) ∈ ⁅Ks, J⁆.subgroupOf Ks := h ▸ Subgroup.mem_top _
      exact this
    · exfalso
      have h1 : ⁅⁅Ks, J⁆, Ks⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro d hd
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hc := Subgroup.mem_center_iff.mp
          (h (show (⟨d, hle hd⟩ : ↥Ks) ∈ ⁅Ks, J⁆.subgroupOf Ks from hd)) ⟨y, hy⟩
        exact congrArg Subtype.val hc
      have h2 : ⁅Ks, J⁆ = ⊥ := CFSG.LocalCores.perfect_double_commutator hKsc.1.1 h1
      have hJc : J ≤ Subgroup.centralizer (Ks : Set (X ⧸ gnC T)) := by
        rw [Subgroup.commutator_comm] at h2
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
      have hYc := Subgroup.normalClosure_le_normal
        (N := Subgroup.centralizer (Ks : Set (X ⧸ gnC T))) (s := (J : Set (X ⧸ gnC T))) hJc
      obtain ⟨a, b, hab⟩ := exists_not_comm_of_isQuasisimple hKsc.1
      apply hab
      obtain ⟨x, hx, hxa⟩ := a.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hxa]
      exact (Subgroup.mem_centralizer_iff.mp (hYc (hKY hx)) b b.2).symm
  obtain ⟨hZs, hrt⟩ := hrk _ hKsO hJ hKsns
  set Ct : Subgroup (X ⧸ Q) := (gnC T).map π with hCt
  have hCtn : Ct.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Q)
  have hCts : CFSG.HallHigman.IsPSolvable 3 ↥Ct := PSolvableClosure.isPSolvable_map π hCs
  have hKtN : Kt.Normal := by
    refine ⟨fun x hx g => ?_⟩
    by_contra hgx
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective Q g
    set Ktg := Kt.map (MulAut.conj (π g₀)).toMonoidHom with hKtg
    have hKtgc : CFSG.IsComponent Ktg :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (π g₀)) hKt
    have hne : Ktg ≠ Kt := fun h => hgx (h ▸ ⟨x, hx, rfl⟩)
    have hcomm' : ∀ a ∈ Kt, ∀ b ∈ Ktg, a * b = b * a := by
      rcases CFSG.LocalCores.distinct_components_commute hKt hKtgc with h | h
      · exact absurd h.symm hne
      · intro a ha b hb
        have hc : ⁅a, b⁆ ∈ ⁅Kt, Ktg⁆ := Subgroup.commutator_mem_commutator ha hb
        rw [h, Subgroup.mem_bot] at hc
        exact commutatorElement_eq_one_iff_mul_comm.mp hc
    have hle : Ktg ≤ Kt ⊔ Ct := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← hKmap] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      have hfk : f (g₀ * k * g₀⁻¹) ∈ Ks := by
        rw [map_mul, map_mul, map_inv]
        exact hKsN.conj_mem _ ⟨k, hk, rfl⟩ (f g₀)
      obtain ⟨k', hk', hk'e⟩ := hfk
      have hk'e' : ((k' : X) : X ⧸ gnC T) = ((g₀ * k * g₀⁻¹ : X) : X ⧸ gnC T) := hk'e
      have hc : k'⁻¹ * (g₀ * k * g₀⁻¹) ∈ gnC T := QuotientGroup.eq.mp hk'e'
      have hid : (MulAut.conj (π g₀)).toMonoidHom (π k) =
          π k' * π (k'⁻¹ * (g₀ * k * g₀⁻¹)) := by
        show π g₀ * π k * (π g₀)⁻¹ = π k' * π (k'⁻¹ * (g₀ * k * g₀⁻¹))
        rw [← map_mul, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        group
      rw [hid, ← hKmap]
      exact Subgroup.mul_mem_sup ⟨k', hk', rfl⟩ ⟨_, hc, rfl⟩
    have hKtgCt : Ktg ≤ Ct := by
      have hperf : ⁅Ktg, Ktg⁆ = Ktg := Subgroup.isPerfect_iff.mp hKtgc.1.1
      rw [← hperf]
      refine (Subgroup.commutator_mono hle le_rfl).trans ?_
      rw [Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
      have hub' : u⁻¹ * b⁻¹ = b⁻¹ * u⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hcomm' u hu b hb]
      have hid : ⁅u * c, b⁆ = u * (c * (b * c⁻¹ * b⁻¹)) * u⁻¹ := by
        rw [commutatorElement_def]
        calc u * c * b * (u * c)⁻¹ * b⁻¹ = u * c * b * c⁻¹ * (u⁻¹ * b⁻¹) := by group
          _ = u * c * b * c⁻¹ * (b⁻¹ * u⁻¹) := by rw [hub']
          _ = u * (c * (b * c⁻¹ * b⁻¹)) * u⁻¹ := by group
      rw [hid]
      exact hCtn.conj_mem _ (Ct.mul_mem hc (hCtn.conj_mem _ (Ct.inv_mem hc) b)) u
    exact hKtns (QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Kt.equivMapOfInjective _ (MulAut.conj (π g₀)).injective).symm
      (PSolvableClosure.isPSolvable_of_le hCts hKtgCt))
  set Zt : Subgroup (X ⧸ Q) := (Subgroup.center ↥Kt).map Kt.subtype with hZt
  have hKQ : ∀ c ∈ K, c ∈ Q → f c = 1 := by
    intro c hc hcQ
    have hz : (⟨f c, c, hc, rfl⟩ : ↥Ks) ∈ Subgroup.center ↥Ks := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨_, x, hx, rfl⟩
      exact Subtype.ext (hcomm x hx c hcQ)
    rw [hZs, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  have hF1 : ∀ k ∈ K, π k ∈ Zt → f k = 1 := by
    intro k hk hkZ
    have hkc := (mem_center_map_iff.mp hkZ).2
    have hz : (⟨f k, k, hk, rfl⟩ : ↥Ks) ∈ Subgroup.center ↥Ks := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨_, x, hx, rfl⟩
      apply Subtype.ext
      show f x * f k = f k * f x
      have hxkt : π x ∈ Kt := hKmap ▸ ⟨x, hx, rfl⟩
      have hc : π (k * x * k⁻¹ * x⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hkc (π x) hxkt]
        group
      have h1 := hKQ _ (K.mul_mem (K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk)) (K.inv_mem hx))
        ((QuotientGroup.eq_one_iff _).mp hc)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← commutatorElement_def] at h1
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    rw [hZs, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  have hKC' : ∀ k ∈ K, k ∈ gnC T → π k ∈ Zt := fun k hk hkC => by
    have := hKC k hk hkC
    rwa [center_map_congr hKmap] at this
  set bK : ↥K →* ↥Kt := (MulEquiv.subgroupCongr hKmap).toMonoidHom.comp (π.subgroupMap K)
    with hbK
  have hbKs : Function.Surjective bK :=
    (MulEquiv.subgroupCongr hKmap).surjective.comp (π.subgroupMap_surjective K)
  have hker2 : ((QuotientGroup.mk' (Subgroup.center ↥Kt)).comp bK).ker =
      (f.subgroupMap K).ker := by
    ext k
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hk
      exact Subtype.ext (hF1 k k.2 ⟨bK k, hk, rfl⟩)
    · intro hk
      have hfk : f k = 1 := congrArg Subtype.val hk
      obtain ⟨z, hz, hze⟩ := hKC' k k.2 ((QuotientGroup.eq_one_iff (k : X)).mp hfk)
      have : z = bK k := Subtype.ext hze
      rw [← this]
      exact hz
  let eZ : (↥Kt ⧸ Subgroup.center ↥Kt) ≃* ↥Ks :=
    mulEquivOfKerEq _ _ (by
      rw [MonoidHom.coe_comp]; exact (QuotientGroup.mk'_surjective _).comp hbKs)
      (f.subgroupMap_surjective K) hker2
  let eKs : (↥Ks ⧸ Subgroup.center ↥Ks) ≃* ↥Ks :=
    (QuotientGroup.quotientMulEquivOfEq hZs).trans QuotientGroup.quotientBot
  have hrtKt : IsRankTwoLayerType (↥Kt ⧸ Subgroup.center ↥Kt) :=
    isRankTwoLayerType_of_mulEquiv (eKs.trans eZ.symm) hrt
  have hO2 : CFSG.pCore 2 (X ⧸ Q) = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine (CFSG.pPrimeCore_eq_bot_iff.mp hO3) _ CFSG.pCore_normal ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := X ⧸ Q))
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hodd := GNQuotient.not_two_dvd_card_center_of_isComponentOf hO2
    ((CFSG.isComponent_iff_open Kt).1 hKt)
  have hKtq : CFSG.Open.IsQuasisimple ↥Kt := ⟨hKt.1.1.commutator_eq_top, hKt.1.2.1⟩
  have hZ1t : Subgroup.center ↥Kt = ⊥ := by
    rcases hZ ↥Kt hKtq hodd (Or.inl hrtKt) with h | ⟨h3, -, h9⟩
    · exact h
    exfalso
    have hCN : gnC T ≤ Subgroup.normalizer (T₁ : Set X) := by
      refine (Subgroup.centralizer_le ?_).trans (Subgroup.centralizer_le_normalizer _)
      exact fun t ht => Subgroup.subset_normalClosure (hpair.le_center ht)
    obtain ⟨v, hvA, hv3, hvZ⟩ :=
      exists_three_elem_of_not_le (hthree Ks (hloc.gnYComponent hpair hKsO hKsns)).1
    have hv1 : v ≠ 1 := fun h => hvZ (h ▸ Subgroup.one_mem _)
    have hvK : v ∈ (K ⊓ Subgroup.normalizer (T₁ : Set X)).map f := by
      obtain ⟨n, hn, hnv⟩ := hvA.1
      obtain ⟨k, hk, hkv⟩ := hvA.2
      refine ⟨k, ⟨hk, ?_⟩, hkv⟩
      have hnk : ((n : X) : X ⧸ gnC T) = ((k : X) : X ⧸ gnC T) := hnv.trans hkv.symm
      have := (Subgroup.normalizer _).mul_mem hn (hCN (QuotientGroup.eq.mp hnk))
      simpa using this
    have hv3' : IsPGroup 3 ↥(Subgroup.zpowers v) := by
      obtain ⟨j, hj⟩ := hv3
      refine IsPGroup.of_card (n := j) ?_
      rw [Nat.card_zpowers, hj]
    obtain ⟨U₁, hU₁le, hU₁3, hU₁e⟩ :=
      GNLift.exists_isPGroup_map_eq hv3' (Subgroup.zpowers_le.mpr hvK)
    obtain ⟨u, huU, huv⟩ : v ∈ U₁.map f := hU₁e ▸ Subgroup.mem_zpowers v
    have huK : u ∈ K := (hU₁le huU).1
    have huN : u ∈ Subgroup.normalizer (T₁ : Set X) := (hU₁le huU).2
    have huZ : π u ∉ Zt := fun h => hv1 (huv ▸ hF1 u huK h)
    have huKt : π u ∈ Kt := hKmap ▸ ⟨u, huK, rfl⟩
    have hu1 : π u ≠ 1 := fun h => huZ (h ▸ Zt.one_mem)
    have hord : orderOf (π u) = 3 := by
      obtain ⟨k, hk⟩ := hU₁3 ⟨u, huU⟩
      have hk' : (π u) ^ (3 ^ k) = 1 := by
        rw [← map_pow]
        have := congrArg Subtype.val hk
        simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
        rw [this, map_one]
      obtain ⟨b, hb, hbo⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk')
      rcases (by omega : b = 0 ∨ b = 1 ∨ 2 ≤ b) with h0 | h1 | h2
      · rw [h0, pow_zero, orderOf_eq_one_iff] at hbo
        exact absurd hbo hu1
      · rw [hbo, h1, pow_one]
      · exfalso
        obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
        have hdvd : 3 ^ c ∣ orderOf (π u) := hbo ▸ Nat.pow_dvd_pow 3 (by omega)
        have h9' : orderOf ((π u) ^ (3 ^ c)) = 9 := by
          rw [orderOf_pow_of_dvd (by positivity) hdvd, hbo, pow_add,
            Nat.mul_div_cancel_left _ (by positivity)]
          norm_num
        exact h9 ⟨_, Kt.pow_mem huKt _⟩ (by rw [Subgroup.orderOf_mk]; exact h9')
    have hZtc : Nat.card Zt = 3 := by
      rw [hZt, Subgroup.card_map_of_injective Kt.subtype_injective, h3]
    obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Zt, z ≠ 1 := by
      by_contra hne
      push Not at hne
      have : Zt = ⊥ := (Subgroup.eq_bot_iff_forall Zt).mpr hne
      rw [this, Subgroup.card_bot] at hZtc
      omega
    have hz3 : orderOf z = 3 := by
      have hdvd := Subgroup.orderOf_dvd_natCard Zt hzZ
      rw [hZtc] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hz1
      · exact h
    have hzu : Commute z (π u) := (mem_center_map_iff.mp hzZ).2 (π u) huKt
    set E : Subgroup (X ⧸ Q) := Subgroup.closure ({z, π u} : Set (X ⧸ Q)) with hE
    have hzE : z ∈ E := Subgroup.subset_closure (by simp)
    have huE : π u ∈ E := Subgroup.subset_closure (by simp)
    have hE3 : IsPGroup 3 E :=
      GNLift.isPGroup_closure_pair hzu ⟨1, by rw [hz3, pow_one]⟩ ⟨1, by rw [hord, pow_one]⟩
    have hEc : ¬ IsCyclic E := by
      intro hc
      rcases GNLift.mem_zpowers_or_mem_zpowers ⟨1, by rw [hz3, pow_one]⟩
        ⟨1, by rw [hord, pow_one]⟩ hc with h | h
      · apply huZ
        have hle : Subgroup.zpowers z ≤ Subgroup.zpowers (π u) := Subgroup.zpowers_le.mpr h
        have heq : Subgroup.zpowers z = Subgroup.zpowers (π u) :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hz3, hord])
        exact (Subgroup.zpowers_le.mpr hzZ) (heq ▸ Subgroup.mem_zpowers (π u))
      · exact huZ ((Subgroup.zpowers_le.mpr hzZ) h)
    have hEle : E ≤ (K ⊓ Subgroup.normalizer (T₁ : Set X)).map π := by
      rw [hE, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · have hzK : x ∈ K.map π := hKmap.symm ▸ (mem_center_map_iff.mp hzZ).1
        obtain ⟨k, hk, rfl⟩ := hzK
        exact ⟨k, ⟨hk, hCN ((QuotientGroup.eq_one_iff k).mp (hF1 k hk hzZ))⟩, rfl⟩
      · exact ⟨u, ⟨huK, huN⟩, rfl⟩
    obtain ⟨U, hUle, hU3, hUE⟩ := GNLift.exists_isPGroup_map_eq hE3 hEle
    have hUc : ¬ IsCyclic U := by
      intro hc
      apply hEc
      rw [← hUE]
      exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ U)
    obtain ⟨-, -, htr⟩ := hloc.e9 T₁ hpair.ne_bot₁ hT₁ hpair.char₁ U (fun x hx => (hUle hx).2)
      hU3 hUc
    obtain ⟨u₁, hu₁, hu₁z⟩ : z ∈ U.map π := hUE ▸ hzE
    obtain ⟨u₂, hu₂, hu₂u⟩ : π u ∈ U.map π := hUE ▸ huE
    have hu₁C : u₁ ∈ gnC T :=
      (QuotientGroup.eq_one_iff u₁).mp (hF1 u₁ (hUle hu₁).1 (hu₁z ▸ hzZ))
    have hu₂C : u₂ ∉ gnC T := fun h => huZ (hu₂u ▸ hKC' u₂ (hUle hu₂).1 h)
    have hu₁1 : u₁ ≠ 1 := fun h => hz1 (by rw [← hu₁z, h, map_one])
    have hu₂1 : u₂ ≠ 1 := fun h => hu1 (by rw [← hu₂u, h, map_one])
    obtain ⟨n, -, hn⟩ := htr u₁ hu₁ u₂ hu₂ hu₁1 hu₂1
    exact hu₂C (hn ▸ (gnC_normal T).conj_mem u₁ hu₁C n)
  let eKt : ↥Kt ≃* ↥Ks :=
    ((QuotientGroup.quotientMulEquivOfEq hZ1t).trans QuotientGroup.quotientBot).symm.trans eZ
  have : IsSimpleGroup (↥Ks ⧸ Subgroup.center ↥Ks) := hKsc.1.2.1
  have hKss : IsSimpleGroup ↥Ks := eKs.symm.isSimpleGroup
  refine ⟨Kt, hKtN, eKt.isSimpleGroup, fun hc => ?_,
    isRankTwoLayerType_of_mulEquiv eKt.symm (isRankTwoLayerType_of_mulEquiv eKs hrt)⟩
  obtain ⟨a, b, hab⟩ := exists_not_comm_of_isQuasisimple hKt.1
  exact hab (hc.is_comm.comm a b)

theorem exists_rankTwo_normal_of_gn (hGN : GlaubermanNilesInput)
    (hFFT : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (h3J : ThreePrimeJCentral) (h56 : AGL81I56) (hRT : KFactParabolicCoverRankTwo)
    (hA7 : KFactAltSevenE9) (hZ : KFactOddCentreE9) (hX : GNSetting X T) (hloc : GNLocal T)
    (hnc : ¬ CFSG.ABGLocalTools.IsPConstrained 3 X) :
    ∃ K : Subgroup (X ⧸ RankThreeCoreUniqueness.Helpers.primeComplementCore (G := X) 3),
      K.Normal ∧ IsSimpleGroup ↥K ∧ ¬ IsMulCommutative ↥K ∧ IsRankTwoLayerType ↥K :=
  exists_rankTwo_normal_of_rankTwo hGN h3J hZ hX hloc hnc fun _ hL hJ hns =>
    rankTwo_of_gn hGN hFFT h56 hRT hA7 hZ hX hloc hL hJ hns

end Core

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
