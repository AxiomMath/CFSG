module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSetting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedSylow
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderNilpotent
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.B6 CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

section FrattiniImage

variable {H : Type*} [Group H] [Finite H]

theorem frattini_image_in_odd_residual_quotient (L : Subgroup H) [L.Normal]
    (hL : ∀ x : H ⧸ L, ∃ k : ℕ, x ^ 2 ^ k = 1) {D : Subgroup H}
    (hD : D.map (QuotientGroup.mk' (CFSG.pCore 2 H)) ≤ frattini (H ⧸ CFSG.pCore 2 H)) :
    (D.subgroupOf L).map (QuotientGroup.mk' ((CFSG.pCore 2 H).subgroupOf L)) ≤
      frattini (L ⧸ (CFSG.pCore 2 H).subgroupOf L) := by
  classical
  have hQn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  set Q : Subgroup H := CFSG.pCore 2 H with hQ
  set φ := QuotientGroup.mk' Q with hφ
  set Nb : Subgroup (H ⧸ Q) := L.map φ with hNb
  have hNbn : Nb.Normal := Subgroup.Normal.map inferInstance φ (QuotientGroup.mk'_surjective Q)
  have hNbq : IsPGroup 2 ((H ⧸ Q) ⧸ Nb) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hL (QuotientGroup.mk h)
    refine ⟨k, ?_⟩
    have hmem : h ^ 2 ^ k ∈ L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hk
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨h ^ 2 ^ k, hmem, rfl⟩
  have hO : CFSG.pCore 2 (H ⧸ Q) = ⊥ := pCore_quotient_pCore_eq_bot' 2
  have hfr := frattini_eq_of_pCore_eq_bot (p := 2) hO Nb hNbq
  let f : L →* Nb := φ.subgroupMap L
  have hf : Function.Surjective f := φ.subgroupMap_surjective L
  have hker : f.ker = Q.subgroupOf L := by
    have := Subgroup.ker_subgroupMap L φ
    rw [this, hφ, QuotientGroup.ker_mk']
  let e : (L ⧸ Q.subgroupOf L) ≃* Nb :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he : ∀ x : L, e (QuotientGroup.mk x) = f x := fun x => rfl
  have hfe := frattini_map_equiv e
  rintro _ ⟨x, hx, rfl⟩
  have hxD : (x : H) ∈ D := hx
  have h1 : φ (x : H) ∈ frattini (H ⧸ Q) := hD ⟨x, hxD, rfl⟩
  rw [← hfr] at h1
  obtain ⟨y, hy, hyx⟩ := h1
  have hyfx : y = f x := Subtype.ext hyx
  rw [hyfx] at hy
  have h2 : e (QuotientGroup.mk x) ∈ frattini Nb := by rw [he]; exact hy
  rw [← hfe] at h2
  obtain ⟨z, hz, hze⟩ := h2
  have : z = QuotientGroup.mk x := e.injective hze
  rw [this] at hz
  exact hz

theorem frattini_image_in_odd_residual_quotient' (L : Subgroup H) [L.Normal]
    (hL : ∀ x : H ⧸ L, ∃ k : ℕ, x ^ 2 ^ k = 1) {D : Subgroup H}
    (hD : D.map (QuotientGroup.mk' (CFSG.pCore 2 H)) ≤ frattini (H ⧸ CFSG.pCore 2 H))
    (Pn : Subgroup L) [Pn.Normal] (hPn : Pn = (CFSG.pCore 2 H).subgroupOf L) :
    (D.subgroupOf L).map (QuotientGroup.mk' Pn) ≤ frattini (L ⧸ Pn) := by
  subst hPn
  exact frattini_image_in_odd_residual_quotient L hL hD

theorem le_sup_pCore_of_le_sup (L : Subgroup H) [L.Normal]
    (hL : ∀ x : H ⧸ L, ∃ k : ℕ, x ^ 2 ^ k = 1) {I N : Subgroup H} [N.Normal]
    (hN : N.map (QuotientGroup.mk' (CFSG.pCore 2 H)) ≤ frattini (H ⧸ CFSG.pCore 2 H))
    (hLIN : L ≤ I ⊔ N) : L ≤ I ⊔ CFSG.pCore 2 H := by
  classical
  have hQn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  set Q : Subgroup H := CFSG.pCore 2 H with hQ
  set φ := QuotientGroup.mk' Q with hφ
  set Nb : Subgroup (H ⧸ Q) := L.map φ with hNb
  have hNbn : Nb.Normal := Subgroup.Normal.map inferInstance φ (QuotientGroup.mk'_surjective Q)
  have hNbq : IsPGroup 2 ((H ⧸ Q) ⧸ Nb) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hL (QuotientGroup.mk h)
    refine ⟨k, ?_⟩
    have hmem : h ^ 2 ^ k ∈ L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hk
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨h ^ 2 ^ k, hmem, rfl⟩
  have hO : CFSG.pCore 2 (H ⧸ Q) = ⊥ := pCore_quotient_pCore_eq_bot' 2
  have hfr := frattini_eq_of_pCore_eq_bot (p := 2) hO Nb hNbq
  set T : Subgroup Nb := (I.map φ).subgroupOf Nb with hT
  have hTtop : T ⊔ frattini Nb = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨z, hz⟩ -
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨y, hy, n, hn, hyn⟩ := Subgroup.mem_sup_of_normal_right.mp (hLIN hx)
    have hφn : φ n ∈ frattini (H ⧸ Q) := hN ⟨n, hn, rfl⟩
    rw [← hfr] at hφn
    obtain ⟨fn, hfn, hfnv⟩ := hφn
    have hφy : φ y = φ x * (φ n)⁻¹ := by
      rw [← hyn, map_mul]; group
    have hφyNb : φ y ∈ Nb := by
      rw [hφy]
      exact mul_mem (Subgroup.mem_map_of_mem φ hx) (inv_mem (hfnv ▸ fn.2))
    have hzeq : (⟨φ x, Subgroup.mem_map_of_mem φ hx⟩ : Nb) = ⟨φ y, hφyNb⟩ * fn := by
      apply Subtype.ext
      show φ x = φ y * (fn : H ⧸ Q)
      have : (fn : H ⧸ Q) = φ n := hfnv
      rw [this, hφy]; group
    rw [hzeq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem φ hy)) hfn
  have hTt : T = ⊤ := frattini_nongenerating hTtop
  intro x hx
  have hmem : (⟨φ x, Subgroup.mem_map_of_mem φ hx⟩ : Nb) ∈ T := hTt ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_subgroupOf.mp hmem
  have hq : y⁻¹ * x ∈ Q := by
    rw [hQ, ← QuotientGroup.ker_mk' (CFSG.pCore 2 H), MonoidHom.mem_ker, map_mul, map_inv]
    have : φ y = φ x := hyx
    rw [this, inv_mul_cancel]
  have hxy : x = y * (y⁻¹ * x) := by group
  rw [hxy]
  exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hq)

omit [Finite H] in
theorem mem_frattini_quotient_of_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (N : Subgroup X) [N.Normal] (M : Subgroup Y) [M.Normal]
    (hNM : N.map e.toMonoidHom = M) {x : X}
    (hx : QuotientGroup.mk' M (e x) ∈ frattini (Y ⧸ M)) :
    QuotientGroup.mk' N x ∈ frattini (X ⧸ N) := by
  let ec : X ⧸ N ≃* Y ⧸ M := QuotientGroup.congr N M e hNM
  have hec : ec (QuotientGroup.mk' N x) = QuotientGroup.mk' M (e x) := rfl
  have h1 := frattini_map_equiv ec
  rw [← h1] at hx
  rw [← hec] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  have : z = QuotientGroup.mk' N x := ec.injective hzx
  rwa [this] at hz

theorem frattini_image_in_odd_residual_quotient_sub (L H₀ : Subgroup H) [L.Normal]
    (hLH₀ : L ≤ H₀) (hL : ∀ x : H ⧸ L, ∃ k : ℕ, x ^ 2 ^ k = 1) {D : Subgroup H}
    (hD : D.map (QuotientGroup.mk' (CFSG.pCore 2 H)) ≤ frattini (H ⧸ CFSG.pCore 2 H))
    (Q₁ : Subgroup H₀) [Q₁.Normal] (hQ₁ : ∀ x : H₀, x ∈ Q₁ ↔ (x : H) ∈ CFSG.pCore 2 H) :
    ((D.subgroupOf H₀).subgroupOf (L.subgroupOf H₀)).map
        (QuotientGroup.mk' (Q₁.subgroupOf (L.subgroupOf H₀))) ≤
      frattini ((L.subgroupOf H₀) ⧸ Q₁.subgroupOf (L.subgroupOf H₀)) := by
  classical
  have hQn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  have hfj := frattini_image_in_odd_residual_quotient L hL hD
  let e : (L.subgroupOf H₀) ≃* L := Subgroup.subgroupOfEquivOfLe hLH₀
  rintro _ ⟨x, hx, rfl⟩
  refine mem_frattini_quotient_of_equiv e (Q₁.subgroupOf (L.subgroupOf H₀))
    ((CFSG.pCore 2 H).subgroupOf L) ?_ ?_
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      show ((z : H₀) : H) ∈ CFSG.pCore 2 H
      exact (hQ₁ _).mp (Subgroup.mem_subgroupOf.mp hz)
    · intro hy
      refine ⟨⟨⟨y, hLH₀ y.2⟩, y.2⟩, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr ((hQ₁ _).mpr (Subgroup.mem_subgroupOf.mp hy))
  · have hxD : (e x : H) ∈ D := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx)
    exact hfj ⟨e x, hxD, rfl⟩

omit [Finite H] in
theorem isSubnormal_of_pGroup_quotient {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (L : Subgroup G) [L.Normal] (hL : IsPGroup p (G ⧸ L)) {X : Subgroup G} (hLX : L ≤ X) :
    X.IsSubnormal := by
  have : Group.IsNilpotent (G ⧸ L) := hL.isNilpotent
  have h := (CFSG.QuasithinUnique.Setup.Offender.isSubnormal_of_isNilpotent
    (X.map (QuotientGroup.mk' L))).comap (QuotientGroup.mk' L)
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hLX] at h

end FrattiniImage

section Kernel

variable {H : Type*} [Group H] [Finite H] {R M V : Subgroup H}

theorem minimal_parabolic_reduced_module_Frattini_kernel_production
    (hT : IsSylowTwoOf R (⊤ : Subgroup H)) (hRn : ¬ R.Normal) (hRM : R ≤ M) (hMH : M < ⊤)
    (hmax : ∀ Y : Subgroup H, R ≤ Y → Y < ⊤ → Y ≤ M)
    (hV : IsTwoReducedIn (⊤ : Subgroup H) V)
    (hVH : ¬ (⊤ : Subgroup H) ≤ Subgroup.centralizer (V : Set H)) :
    oddOrderSubgroup (⊤ : Subgroup H) ⊔ R = ⊤ ∧
      R ⊓ Subgroup.centralizer (V : Set H) = CFSG.pCore 2 H ∧
      CFSG.pCore 2 H ≤ Subgroup.centralizer (V : Set H) ∧
      Subgroup.centralizer (V : Set H) ≤ kerIn M ⊤ ∧
      (CFSG.pCore 2 (oddOrderSubgroup (⊤ : Subgroup H))).map
          (oddOrderSubgroup (⊤ : Subgroup H)).subtype =
        oddOrderSubgroup (⊤ : Subgroup H) ⊓ CFSG.pCore 2 H ∧
      (kerIn M ⊤).map (QuotientGroup.mk' (CFSG.pCore 2 H)) =
        frattini (H ⧸ CFSG.pCore 2 H) ∧
      (∀ D : Subgroup H, D ≤ kerIn M ⊤ →
        (D.subgroupOf (oddOrderSubgroup (⊤ : Subgroup H))).map
            (QuotientGroup.mk' (CFSG.pCore 2 (oddOrderSubgroup (⊤ : Subgroup H)))) ≤
          frattini (oddOrderSubgroup (⊤ : Subgroup H) ⧸
            CFSG.pCore 2 (oddOrderSubgroup (⊤ : Subgroup H)))) := by
  classical
  have hTn : ¬ (⊤ : Subgroup H) ≤ Subgroup.normalizer (R : Set H) := fun h =>
    hRn (Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h))
  obtain ⟨hHLR, -, hCX, hCR, -⟩ := reduced_detects_commutator hT hTn hRM hMH hmax hV hVH
  have hQ : CFSG.pCore 2 H = CFSG.Open.pCore 2 H :=
    CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 H
  have hQeq : R ⊓ Subgroup.centralizer (V : Set H) = CFSG.pCore 2 H := by
    rw [hCR, pCoreOf_top]
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hV.2.1)
  have hQn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  have hLn : (oddOrderSubgroup (⊤ : Subgroup H)).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    refine top_le_iff.mp fun g _ => normalizer_le_normalizer_oddOrderSubgroup (⊤ : Subgroup H)
      (?_ : g ∈ Subgroup.normalizer ((⊤ : Subgroup H) : Set H)) 
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp
  have hQC : CFSG.pCore 2 H ≤ Subgroup.centralizer (V : Set H) := hQeq ▸ inf_le_right
  have hCJ : Subgroup.centralizer (V : Set H) ≤ kerIn M ⊤ := by
    refine le_kerIn_of_le_normalizer (by simpa using hCX) ?_
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      have h1 := Subgroup.mem_centralizer_iff.mp hc (g⁻¹ * v * g) (by
        simpa [mul_assoc] using hVn.conj_mem v hv g⁻¹)
      calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
        _ = (g * c * g⁻¹) * v := by group
    · intro hc
      refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      have h1 := Subgroup.mem_centralizer_iff.mp hc (g * v * g⁻¹) (hVn.conj_mem v hv g)
      calc v * c = g⁻¹ * ((g * v * g⁻¹) * (g * c * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * c * g⁻¹) * (g * v * g⁻¹)) * g := by rw [h1]
        _ = c * v := by group
  have hmp : MinParabolic (⊤ : Subgroup H) R M := minParabolic_of_uniqueMax hT hTn hRM hMH hmax
  have hfr : (kerIn M ⊤).map (QuotientGroup.mk' (CFSG.pCore 2 H)) =
      frattini (H ⧸ CFSG.pCore 2 H) := by
    have key : ∀ (N : Subgroup H) [N.Normal], N = CFSG.Open.pCore 2 H →
        (kerIn M ⊤).map (QuotientGroup.mk' N) = frattini (H ⧸ N) := by
      intro N _ hN
      subst hN
      exact hmp.map_kerIn_eq_frattini
    exact key _ hQ
  have hP : (CFSG.pCore 2 (oddOrderSubgroup (⊤ : Subgroup H))).map
      (oddOrderSubgroup (⊤ : Subgroup H)).subtype =
        oddOrderSubgroup (⊤ : Subgroup H) ⊓ CFSG.pCore 2 H := by
    have h1 : pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup H)) ≤ pCoreOf 2 (⊤ : Subgroup H) :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _ le_top
        (by infer_instance)
    rw [pCoreOf_top] at h1
    have h2 : oddOrderSubgroup (⊤ : Subgroup H) ⊓ CFSG.pCore 2 H ≤
        pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup H)) := by
      refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
        inf_le_left ?_ ?_
      · rw [inf_comm, inf_subgroupOf_right]
        infer_instance
      · exact (CFSG.pCore_isPGroup (p := 2) (G := H)).to_le inf_le_right
    have h3 : (CFSG.pCore 2 (oddOrderSubgroup (⊤ : Subgroup H))).map
        (oddOrderSubgroup (⊤ : Subgroup H)).subtype =
          pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup H)) := by
      unfold pCoreOf
      try with_reducible rfl
    rw [h3]
    exact le_antisymm (le_inf (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 _) h1) h2
  have hL2 : ∀ x : H ⧸ oddOrderSubgroup (⊤ : Subgroup H), ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := exists_pow_mem_oddOrderSubgroup (H := (⊤ : Subgroup H)) (h := h) trivial
    exact ⟨k, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).mpr hk⟩
  have hPn : CFSG.pCore 2 (oddOrderSubgroup (⊤ : Subgroup H)) =
      (CFSG.pCore 2 H).subgroupOf (oddOrderSubgroup (⊤ : Subgroup H)) := by
    have h1 := congrArg (Subgroup.comap (oddOrderSubgroup (⊤ : Subgroup H)).subtype) hP
    rw [Subgroup.comap_map_eq_self_of_injective (oddOrderSubgroup (⊤ : Subgroup H)).subtype_injective]
      at h1
    rw [h1, inf_comm]
    exact Subgroup.inf_subgroupOf_right _ _
  refine ⟨hHLR.symm, hQeq, hQC, hCJ, hP, hfr, fun D hD => ?_⟩
  have hD' : D.map (QuotientGroup.mk' (CFSG.pCore 2 H)) ≤ frattini (H ⧸ CFSG.pCore 2 H) :=
    hfr ▸ Subgroup.map_mono hD
  exact frattini_image_in_odd_residual_quotient' _ hL2 hD' _ hPn

end Kernel

end CFSG.QuasithinUnique.Setup.Campbell
