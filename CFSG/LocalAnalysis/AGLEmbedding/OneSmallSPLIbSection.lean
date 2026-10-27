module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbCover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbPerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
public import CFSG.GroupTheory.SuzukiTwoGroupsKernel
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGlue
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalCoprimePreimages

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.exists_component_mem_of_notIa (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z) (hnIa : ¬ D1SmallIa p H K) :
    ∃ L' : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L' ⊤ ∧
      L' ≤ d1X0 p M H ∧ L' ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ∧
      ∀ hzH : z ∈ H, QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩ ∈ L' := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  unfold D1SmallIa at hnIa
  push Not at hnIa
  obtain ⟨L', hL', hne⟩ := hnIa
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  have hL'C : L' ≤ C := le_centralizer_of_component_ne hL' hd.comp hne
  obtain ⟨zs, hzsR, hzsK, hzsp, hzsc⟩ := hd.z
  have hCX : C ≤ d1X0 p M H :=
    hd.cfg.red.centralizer_le_of_rankOne hd.noncyclic hzsR hzsK hzsp hzsc
  obtain ⟨-, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzsR hzsK hzsp hzsc
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  refine ⟨L', hL', hL'C.trans hCX, hL'C, fun hzH => ?_⟩
  obtain ⟨t, ⟨htR, htL⟩, htp, -⟩ := exists_mem_sylow_inf_component hp hp2
    hd.cfg.red.core_eq_bot Rbar hL'
  set zb := QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩
  have hzbR : zb ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hd.cfg.rbar]
    exact ⟨⟨z, hzH⟩, hz.1, rfl⟩
  have hzbC : zb ∈ C := hz.2.2.2
  set W := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ C with hW
  have hWcyc : IsCyclic W := hd.cfg.red.isCyclic_of_le_centralizer hd.comp hKX₀
    (Rbar.isPGroup'.to_le inf_le_left) inf_le_right
  have hzbp : orderOf zb = p := by
    have h1 : orderOf zb ∣ p := by
      have h0 := orderOf_map_dvd (QuotientGroup.mk' (primeComplementCore (G := H) p))
        (⟨z, hzH⟩ : H)
      rw [Subgroup.orderOf_mk, hz.2.1] at h0
      exact h0
    rcases (Nat.dvd_prime hp).mp h1 with h1 | h1
    · exfalso
      have hz1 : zb = 1 := orderOf_eq_one_iff.mp h1
      have hzO := (mk'_primeComplementCore_eq_one_iff p _).mp hz1
      have hdvd : orderOf z ∣ Nat.card (GLBPrimeCore p H) := Subgroup.orderOf_dvd_natCard _ hzO
      rw [hz.2.1] at hdvd
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp (glbPrimeCore_coprime p H) hdvd
    · exact h1
  have hmem : (⟨zb, hzbR, hzbC⟩ : W) ∈ Subgroup.zpowers (⟨t, htR, hL'C htL⟩ : W) := by
    refine CFSG.GroupTheory.SuzukiTwoGroup.mem_zpowers_of_orderOf_eq ?_
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    show orderOf zb = orderOf t
    rw [hzbp, htp]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : t ^ k = zb := by simpa using congrArg Subtype.val hk
  rw [← hk']
  exact L'.zpow_mem htL k

omit [Finite G] in
theorem map_le_centralizer_of_map {B Z : Type*} [Group B] [Group Z] (θ : B →* Z)
    {V A : Subgroup B} (h : V.map θ ≤ Subgroup.centralizer ((A.map θ : Subgroup Z) : Set Z)) :
    V.map (QuotientGroup.mk' θ.ker) ≤ Subgroup.centralizer
      ((A.map (QuotientGroup.mk' θ.ker) : Subgroup (B ⧸ θ.ker)) : Set (B ⧸ θ.ker)) := by
  rintro _ ⟨v, hv, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨a, ha, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp (h ⟨v, hv, rfl⟩) (θ a) ⟨a, ha, rfl⟩
  have h1 : a * v * a⁻¹ * v⁻¹ ∈ θ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hc]
    group
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have e : (a * v)⁻¹ * (v * a) = a⁻¹ * (v⁻¹ * (a * v * a⁻¹ * v⁻¹)⁻¹ * v) * a := by group
  rw [e]
  have := θ.ker.inv_mem h1
  exact (Subgroup.Normal.conj_mem inferInstance _ ((Subgroup.Normal.conj_mem inferInstance _
    this v⁻¹)) a⁻¹) |> fun h => by simpa [mul_assoc] using h

theorem D1OneSmallData.exists_perfect_section (hd : D1OneSmallData p P M H R Rbar K)
    (hph : D1PhaseThree p P M H R) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    (hUP : KFactUPrime p K) (hout : Group.IsSolvable (Outer K))
    (hs : Group.IsSolvable (GLBCore p 1 (T₁ : Subgroup K))) {z : G}
    (hz : D1SmallCZElt p H R K z) (hnIa : ¬ D1SmallIa p H K)
    (hXz : d1LiftX p H R K ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅D, D⁆ = D ∧ D ≤ barM M (H ⊓ M) ∧
      barM M (d1LiftX p H R K) ≤ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      (∀ hzM : z ∈ M, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈ D) ∧
      ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
        ∀ k : ℕ, p ^ k ∣ Nat.card V → p ^ k ∣ Nat.card D := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmkM
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set X := d1LiftX p H R K with hXdef
  obtain ⟨θ, hθk, hθ⟩ := exists_barM_hom_of hph
  have hRHM : R ≤ H ⊓ M := hph.le_inf
  have hXHM : X ≤ H ⊓ M := (d1LiftX_le p H R K).trans hRHM
  have hXM : X ≤ M := hXHM.trans inf_le_right
  have hzR := hz.1
  have hzHM : z ∈ H ⊓ M := hRHM hzR
  have hXB : barM M X ≤ (barM M (H ⊓ M)) := barM_mono hXHM
  set A : Subgroup (barM M (H ⊓ M)) := (barM M X).subgroupOf (barM M (H ⊓ M)) with hA
  have hXp : IsPGroup p X := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)
  have hAp : IsPGroup p A := ((isPGroup_barM hXp).comap_subtype)
  have hN : ¬ p ∣ Nat.card θ.ker := (Nat.Prime.coprime_iff_not_dvd hp).mp hθk
  obtain ⟨D', hD'p, hD'A, hcov, hpel⟩ := exists_perfect_centralizer_cover θ.ker hN A hAp
  have hθA : A.map θ ≤ K := by
    rintro _ ⟨⟨a, haB⟩, ha, rfl⟩
    have haX : a ∈ barM M X := Subgroup.mem_subgroupOf.mp ha
    obtain ⟨⟨x, hxM⟩, hxX, rfl⟩ := haX
    have hxX' : x ∈ X := Subgroup.mem_subgroupOf.mp hxX
    have hxH : x ∈ H := (hXHM hxX').1
    rw [hθ ⟨x, hxM⟩ hxH haB]
    have h1 : π ⟨x, hxH⟩ ∈ (X.subgroupOf H).map π :=
      ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxX', rfl⟩
    rw [hXdef, hd.cfg.map_d1LiftX_eq_inf] at h1
    exact h1.2
  have hθV : ∀ V : Subgroup (barM M (H ⊓ M)), ⁅V, V⁆ = V →
      V.map θ ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
    intro V hV
    refine D1OneSmallData.le_centralizer_of_perfect hd hT₁ hUP hout hs ?_
      (by rw [← Subgroup.map_commutator, hV])
    rintro _ ⟨b, -, rfl⟩
    obtain ⟨m, hm, hmb⟩ := b.2
    have hmA := Subgroup.mem_subgroupOf.mp hm
    have hb : b = ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hmb ▸ b.2⟩ := Subtype.ext hmb.symm
    rw [hb, hθ m hmA.1]
    exact ⟨⟨m, hmA.1⟩, Subgroup.mem_subgroupOf.mpr hmA, rfl⟩
  have hθVA : ∀ V : Subgroup (barM M (H ⊓ M)), ⁅V, V⁆ = V →
      V.map θ ≤ Subgroup.centralizer ((A.map θ : Subgroup _) : Set _) := by
    intro V hV v hv
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp (hθV V hV hv) a (hθA ha)
  refine ⟨D'.map (barM M (H ⊓ M)).subtype, ?_, Subgroup.map_subtype_le _, ?_, fun hzM => ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hD'p]
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, hd', rfl⟩
    have hxA : (⟨x, hXB hx⟩ : (barM M (H ⊓ M))) ∈ A := Subgroup.mem_subgroupOf.mpr hx
    have := Subgroup.mem_centralizer_iff.mp (hD'A hd') _ hxA
    exact (congrArg Subtype.val this).symm
  ·
    have hzB : mkM ⟨z, hzM⟩ ∈ (barM M (H ⊓ M)) := ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr hzHM, rfl⟩
    set zB : (barM M (H ⊓ M)) := ⟨mkM ⟨z, hzM⟩, hzB⟩ with hzBdef
    have hzA : zB ∈ Subgroup.centralizer (A : Set (barM M (H ⊓ M))) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro ⟨a, haB⟩ ha
      have haX : a ∈ barM M X := Subgroup.mem_subgroupOf.mp ha
      obtain ⟨⟨x, hxM⟩, hxX, hxa⟩ := haX
      have hxz : x * z = z * x := by
        have := Subgroup.mem_centralizer_iff.mp (hXz (Subgroup.mem_subgroupOf.mp hxX)) z rfl
        exact this.symm
      apply Subtype.ext
      show a * mkM ⟨z, hzM⟩ = mkM ⟨z, hzM⟩ * a
      rw [← hxa, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxz
    have hzp : zB ^ p = 1 := by
      apply Subtype.ext
      show (mkM ⟨z, hzM⟩) ^ p = 1
      rw [← map_pow]
      have : (⟨z, hzM⟩ : M) ^ p = 1 := Subtype.ext (by simp [← hz.2.1, pow_orderOf_eq_one])
      rw [this, map_one]
    obtain ⟨L', hL', hL'X, -, hzL'⟩ := hd.exists_component_mem_of_notIa hz hnIa
    have hrange : θ.range = d1X0 p M H := by
      apply le_antisymm
      · rintro _ ⟨b, rfl⟩
        obtain ⟨m, hm, hmb⟩ := b.2
        have hmA := Subgroup.mem_subgroupOf.mp hm
        have hb : b = ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hmb ▸ b.2⟩ := Subtype.ext hmb.symm
        rw [hb, hθ m hmA.1]
        exact ⟨⟨m, hmA.1⟩, Subgroup.mem_subgroupOf.mpr hmA, rfl⟩
      · rintro _ ⟨⟨h, hhH⟩, hh, rfl⟩
        have hhA := Subgroup.mem_subgroupOf.mp hh
        have hhB : mkM ⟨h, hhA.2⟩ ∈ (barM M (H ⊓ M)) :=
          ⟨⟨h, hhA.2⟩, Subgroup.mem_subgroupOf.mpr hhA, rfl⟩
        exact ⟨⟨mkM ⟨h, hhA.2⟩, hhB⟩, hθ ⟨h, hhA.2⟩ hhA.1 hhB⟩
    set θ' : (barM M (H ⊓ M)) →* θ.range := θ.rangeRestrict with hθ'
    have hθ's : Function.Surjective θ' := θ.rangeRestrict_surjective
    set L'' : Subgroup θ.range := L'.subgroupOf θ.range with hL''
    have hL''p : Group.IsPerfect L'' := by
      apply Subgroup.isPerfect_iff.mpr
      apply Subgroup.map_injective θ.range.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (hrange ▸ hL'X),
        commutator_eq_self_of_component hL']
    set V' := perfectResidualOf (L''.comap θ') with hV'
    have hV'map : V'.map θ' = L'' := finite_canonical_perfect_preimage_image_eq θ' hθ's L'' hL''p
    have hV'p : ⁅V', V'⁆ = V' :=
      Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect (L''.comap θ'))
    have hzV' : QuotientGroup.mk' θ.ker zB ∈ V'.map (QuotientGroup.mk' θ.ker) := by
      have hθz : θ zB = π ⟨z, hzHM.1⟩ := hθ ⟨z, hzM⟩ hzHM.1 hzB
      have hθzL : (⟨θ zB, ⟨zB, rfl⟩⟩ : θ.range) ∈ L'' := by
        rw [hL'', Subgroup.mem_subgroupOf]
        show θ zB ∈ L'
        rw [hθz]
        exact hzL' hzHM.1
      rw [← hV'map] at hθzL
      obtain ⟨v, hv, hvz⟩ := hθzL
      refine ⟨v, hv, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, MonoidHom.mem_ker,
        map_mul, map_inv]
      have : θ v = θ zB := congrArg Subtype.val hvz
      rw [this, inv_mul_cancel]
    have hV'A := map_le_centralizer_of_map θ (hθVA V' hV'p)
    have hmem := hpel zB hzA hzp V' hV'p hV'A hzV'
    exact ⟨zB, hmem, rfl⟩
  · intro V hVB hVp k hk
    set V' : Subgroup (barM M (H ⊓ M)) := V.subgroupOf (barM M (H ⊓ M)) with hV'
    have hV'p : ⁅V', V'⁆ = V' := by
      apply Subgroup.map_injective (barM M (H ⊓ M)).subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hVB, hVp]
    have hV'le := hcov V' hV'p (map_le_centralizer_of_map θ (hθVA V' hV'p))
    have hcard : Nat.card V' = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVB).toEquiv
    have h1 := pow_dvd_card_of_le_sup (D := D') (N := θ.ker) hθk hV'le (hcard ▸ hk)
    rwa [Subgroup.card_map_of_injective (barM M (H ⊓ M)).subtype_injective]

end CFSG.AGLEmbedding
