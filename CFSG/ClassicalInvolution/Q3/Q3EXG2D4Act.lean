module

public import CFSG.ClassicalInvolution.Q3.Q3EXG2D4Pt
public import CFSG.ClassicalInvolution.Asc77.AscS24G2A

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.RouteD.Gaps (locMk)
open scoped commutatorElement


section Gen3

variable {G : Type} [Group G]

theorem gen3_iSup₂ {s : Set (Subgroup G)} (h : ∀ N ∈ s, ModelFacts.Gen3 N) :
    ModelFacts.Gen3 (⨆ N ∈ s, N) := by
  classical
  choose! S hS using h
  refine ⟨⋃ N ∈ s, S N, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨N, hN, hxN⟩ := Set.mem_iUnion₂.mp hx
    exact le_iSup₂ (f := fun N (_ : N ∈ s) => N) N hN ((hS N hN).1 hxN)
  · intro x hx
    obtain ⟨N, hN, hxN⟩ := Set.mem_iUnion₂.mp hx
    exact (hS N hN).2.1 x hxN
  · refine iSup₂_le fun N hN => ?_
    exact (hS N hN).2.2.trans (Subgroup.closure_mono
      (Set.subset_iUnion₂ (s := fun N (_ : N ∈ s) => S N) N hN))

theorem centralizes_of_gen3 {P Y Z : Subgroup G} (hPY : P ≤ Y)
    (hZ : ∀ z ∈ Z, ∀ g ∈ Y, z * g = g * z) (hZ3 : ¬ 3 ∣ Nat.card Z) (hP : ModelFacts.Gen3 P)
    {n : G} (hn : ∀ x ∈ P, n * x * n⁻¹ * x⁻¹ ∈ Z) : ∀ x ∈ P, n * x * n⁻¹ = x := by
  obtain ⟨S, hSP, hS3, hPS⟩ := hP
  have hS : ∀ s ∈ S, s * n = n * s := by
    intro s hs
    have hsP := hSP hs
    have hcZ : n * s * n⁻¹ * s⁻¹ ∈ Z := hn s hsP
    set c := n * s * n⁻¹ * s⁻¹ with hc
    have hns : n * s * n⁻¹ = c * s := by rw [hc]; group
    have hcs : c * s = s * c := hZ c hcZ s (hPY hsP)
    have h1 : (n * s * n⁻¹) ^ 3 = 1 := by
      have := map_pow (MulAut.conj n) s 3
      simp only [MulAut.conj_apply] at this
      rw [← this, hS3 s hs]
      simp
    rw [hns, (Commute.mul_pow (show Commute c s from hcs)), hS3 s hs, mul_one] at h1
    have hord : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h1
    have hord2 : orderOf c ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hcZ
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h3 | h3
    · have hc1 : c = 1 := orderOf_eq_one_iff.mp h3
      have : n * s * n⁻¹ = s := by rw [hns, hc1, one_mul]
      calc s * n = (n * s * n⁻¹) * n := by rw [this]
        _ = n * s := by group
    · exfalso
      rw [h3] at hord2
      exact hZ3 hord2
  have hle : P ≤ Subgroup.centralizer ({n} : Set G) := by
    refine hPS.trans ((Subgroup.closure_le _).mpr fun s hs => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hS s hs)
  intro x hx
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

end Gen3

section LayerX

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {w : G} {a : ℕ}
  {t : StatedLieTag} {n : ℕ}

theorem gen3_member (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {N : Subgroup G} (hN : N ∈ Ω) :
    ModelFacts.Gen3 N := by
  obtain ⟨z₀, hz⟩ := hΩ.classical N hN
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 (hex N hN)
  exact ModelFacts.gen3_of_equiv_sl2 e

theorem gen3_layerX (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) :
    ModelFacts.Gen3 (layerX Ω w) :=
  gen3_iSup₂ fun _ hN => gen3_member hΩ hex hN.1.1

theorem oddCore_central3 (hP1 : LocalOddCentral Ω {w}) :
    ∀ z ∈ Asc77.oddCoreOf (locLayer Ω w), ∀ g ∈ locLayer Ω w, z * g = g * z := by
  intro z hz g hg
  obtain ⟨hzY, hzO⟩ := Asc77.mem_oddCoreOf_iff.mp hz
  have := Subgroup.mem_center_iff.mp (hP1 hzO) ⟨g, hg⟩
  exact (congrArg Subtype.val this).symm

theorem not_three_dvd_oddCoreOf (hO3 : LocalOddThreeFree3 Ω w) :
    ¬ 3 ∣ Nat.card ↥(Asc77.oddCoreOf (locLayer Ω w)) := by
  have : Nat.card ↥(Asc77.oddCoreOf (locLayer Ω w)) =
      Nat.card ↥(classicalInvolutionOddCore ↥(locLayer Ω w)) :=
    Subgroup.card_map_of_injective (locLayer Ω w).subtype_injective
  rw [this]
  exact hO3

theorem mem_oddCoreOf_of_mk_eq3 {x : G} {u v : G} (hu : u ∈ locLayer Ω x)
    (hv : v ∈ locLayer Ω x)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨v, hv⟩) :
    u * v⁻¹ ∈ Asc77.oddCoreOf (locLayer Ω x) := by
  have h1 := QuotientGroup.eq_iff_div_mem.mp h
  have hm : u * v⁻¹ ∈ locLayer Ω x := Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hv)
  refine Asc77.mem_oddCoreOf_iff.mpr ⟨hm, ?_⟩
  have e : (⟨u * v⁻¹, hm⟩ : ↥(locLayer Ω x)) = ⟨u, hu⟩ / ⟨v, hv⟩ :=
    Subtype.ext (by simp [div_eq_mul_inv])
  rw [e]
  exact h1

theorem lift_trivial3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) (hP1 : LocalOddCentral Ω {w})
    (hO3 : LocalOddThreeFree3 Ω w) {n : G}
    (hn : ∀ x ∈ layerX Ω w, n * x * n⁻¹ * x⁻¹ ∈ Asc77.oddCoreOf (locLayer Ω w)) :
    ∀ x ∈ layerX Ω w, n * x = x * n := by
  intro x hx
  have := centralizes_of_gen3 (layerX_le_locLayer Ω w)
    (oddCore_central3 hP1) (not_three_dvd_oddCoreOf hO3) (gen3_layerX hΩ hex) hn x hx
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem locImg_ne_bot3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G} {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) : locImg Ω x L ≠ ⊥ := by
  intro h
  have hc := card_locImg3 hΩ hex hL
  rw [h, Subgroup.card_bot] at hc
  omega

theorem Pkg3.range_eq (P : Pkg3 a t n Ω w) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (F : G2D4Facts3 (CompData.model t n)) :
    (P.D.hom P.i₁).range = ⨆ N ∈ {N | Fb Ω w N}, locImg Ω w N := by
  classical
  have hF := P.facts F
  have hinj := P.inj F
  apply le_antisymm
  · set S₀ : Subgroup (locQuot Ω w) := ⨆ N ∈ {N | Fb Ω w N}, locImg Ω w N with hS₀
    obtain ⟨M₀, hM₀⟩ := exists_mem_compMembers3 (D := P.D) P.i₁
    obtain ⟨R₀, hR₀⟩ := exists_corr_left3 hΩ hex P.p1 P.o3 P.D hM₀
    have hbot : R₀ ≠ ⊥ := by
      intro h
      apply locImg_ne_bot3 hΩ hex hM₀.1
      rw [hR₀.2.2, h, Subgroup.map_bot]
    have htop : Subgroup.normalClosure (SetLike.coe R₀) = ⊤ := by
      rcases hF.simple.eq_bot_or_eq_top_of_normal
        (Subgroup.normalClosure (SetLike.coe R₀)) with h | h
      · exfalso
        apply hbot
        rw [eq_bot_iff]
        intro x hx
        have hx' : x ∈ Subgroup.normalClosure (SetLike.coe R₀) :=
          Subgroup.subset_normalClosure hx
        rw [h] at hx'
        exact hx'
      · exact h
    rintro _ ⟨g, rfl⟩
    have hg : g ∈ Subgroup.normalClosure (SetLike.coe R₀) := htop ▸ Subgroup.mem_top g
    have hsub : Group.conjugatesOfSet (SetLike.coe R₀) ⊆
        (SetLike.coe (S₀.comap (P.D.hom P.i₁))) := by
      intro c hc
      obtain ⟨b, hb, hbc⟩ := Group.mem_conjugatesOfSet_iff.mp hc
      obtain ⟨x, hx⟩ := isConj_iff.mp hbc
      obtain ⟨xh, hxh⟩ := QuotientGroup.mk_surjective (P.D.hom P.i₁ x)
      have hN' : conjSub (xh : G) M₀ ∈ compMembers3 Ω w P.D P.i₁ :=
        conjSub_mem_compMembers_of_mem_layer3 hΩ.conjInvariant hM₀ xh.2
      have himg : locImg Ω w (conjSub (xh : G) M₀) = (conjSub x R₀).map (P.D.hom P.i₁) := by
        rw [Gaps.locImg_conjSub_layer M₀ xh, hR₀.2.2,
          show locMk Ω w xh = P.D.hom P.i₁ x from hxh]
        unfold conjSub
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext a'
        simp
      have hcmem : c ∈ conjSub x R₀ := by
        rw [mem_conjSub_iff, ← hx]
        simpa [mul_assoc] using hb
      have hcm : P.D.hom P.i₁ c ∈ locImg Ω w (conjSub (xh : G) M₀) := by
        rw [himg]
        exact Subgroup.mem_map_of_mem _ hcmem
      exact le_iSup₂ (f := fun N (_ : N ∈ {N | Fb Ω w N}) => locImg Ω w N) (conjSub (xh : G) M₀)
        ((P.fb_iff hΩ hex F).mpr hN') hcm
    exact (Subgroup.closure_le (S₀.comap (P.D.hom P.i₁))).mpr hsub hg
  · exact iSup₂_le fun N hN => ((P.fb_iff hΩ hex F).mp hN).2

theorem Pkg3.range_le_map_layerX (P : Pkg3 a t n Ω w) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (F : G2D4Facts3 (CompData.model t n)) {u : locQuot Ω w}
    (hu : u ∈ (P.D.hom P.i₁).range) :
    ∃ x : ↥(locLayer Ω w), (x : G) ∈ layerX Ω w ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) x = u := by
  rw [P.range_eq hΩ hex F] at hu
  have hle : (⨆ N ∈ {N | Fb Ω w N}, locImg Ω w N) ≤
      ((layerX Ω w).subgroupOf (locLayer Ω w)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w))) := by
    refine iSup₂_le fun N hN v hv => ?_
    obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨y, Subgroup.mem_subgroupOf.mpr (le_layerX hN (Subgroup.mem_subgroupOf.mp hy)), rfl⟩
  obtain ⟨x, hx, hxu⟩ := hle hu
  exact ⟨x, Subgroup.mem_subgroupOf.mp hx, hxu⟩

theorem Pkg3.mk_mem_range_of_mem_layerX (P : Pkg3 a t n Ω w) (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) (F : G2D4Facts3 (CompData.model t n)) {x : G}
    (hx : x ∈ layerX Ω w) (hxY : x ∈ locLayer Ω w) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) ⟨x, hxY⟩ ∈
      (P.D.hom P.i₁).range := by
  set T : Subgroup G := ((P.D.hom P.i₁).range.comap
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)))).map
      (locLayer Ω w).subtype with hT
  have hle : layerX Ω w ≤ T := by
    refine iSup₂_le fun N hN x hx => ?_
    have hxY' : x ∈ locLayer Ω w := le_centralizingLayer hN.1 hx
    refine ⟨⟨x, hxY'⟩, ?_, rfl⟩
    exact ((P.fb_iff hΩ hex F).mp hN).2 ⟨⟨x, hxY'⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = ⟨x, hxY⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

end LayerX

section Action

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {w : G} {a : ℕ}
  {t : StatedLieTag} {n : ℕ}

theorem mem_normalizer_of_cent3 (hΩ : ConjInvariant Ω) {s : G} (hs : s * w * s⁻¹ = w) :
    s ∈ Subgroup.normalizer (locLayer Ω w : Set G) := by
  have h1 : conjSub s (centralizingLayer Ω {w}) = centralizingLayer Ω {w} := by
    have := centralizingLayer_conj hΩ s w
    rw [hs] at this
    exact this.symm
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1

@[expose] noncomputable def actQuot3 (Ω : Set (Subgroup G)) (w s : G)
    (hs : s ∈ Subgroup.normalizer (locLayer Ω w : Set G)) : MulAut (locQuot Ω w) :=
  Asc77.S24.quotAct (locLayer Ω w) ⟨s, hs⟩

theorem actQuot3_mk (Ω : Set (Subgroup G)) (w : G) {s : G}
    (hs : s ∈ Subgroup.normalizer (locLayer Ω w : Set G)) (y : ↥(locLayer Ω w)) :
    actQuot3 Ω w s hs (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) y) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w))
        ⟨s * y * s⁻¹, Asc77.S24.conj_mem_of_mem_normalizer _ hs y.2⟩ :=
  Asc77.S24.quotAct_mk (locLayer Ω w) ⟨s, hs⟩ y

theorem actQuot3_sq (Ω : Set (Subgroup G)) (w : G) {s : G}
    (hs : s ∈ Subgroup.normalizer (locLayer Ω w : Set G)) (hs2 : s * s = 1)
    (x : locQuot Ω w) : actQuot3 Ω w s hs (actQuot3 Ω w s hs x) = x := by
  have h1 : (⟨s, hs⟩ : ↥(Subgroup.normalizer (locLayer Ω w : Set G))) * ⟨s, hs⟩ = 1 :=
    Subtype.ext hs2
  have h2 := map_mul (Asc77.S24.quotAct (locLayer Ω w)) ⟨s, hs⟩ ⟨s, hs⟩
  rw [h1, map_one] at h2
  have h3 := DFunLike.congr_fun h2 x
  unfold actQuot3
  simpa [MulAut.one_apply, MulAut.mul_apply] using h3.symm

theorem actQuot3_mk_of_comm (Ω : Set (Subgroup G)) (w : G) {s : G}
    (hs : s ∈ Subgroup.normalizer (locLayer Ω w : Set G)) {y : G} (hy : y ∈ locLayer Ω w)
    (hsy : s * y = y * s) :
    actQuot3 Ω w s hs (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) ⟨y, hy⟩) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) ⟨y, hy⟩ := by
  rw [actQuot3_mk]
  congr 1
  apply Subtype.ext
  show s * y * s⁻¹ = y
  rw [mul_inv_eq_iff_eq_mul]
  exact hsy

theorem Pkg3.lemmaA (P : Pkg3 a t n Ω w) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (F : G2D4Facts3 (CompData.model t n)) {A : Subgroup G} (hA : Fb Ω w A) {aa : G}
    (ha : IsClassicalMember3 A aa) {s : G} (hs2 : s * s = 1) (hsw : s * w = w * s)
    (hsA : ∀ x ∈ A, s * x = x * s) :
    (∀ x ∈ layerX Ω w, s * x = x * s) ∨ (∀ x ∈ layerX Ω w, (s * aa) * x = x * (s * aa)) := by
  classical
  have hF := P.facts F
  have hψ := P.inj F
  have hsw' : s * w * s⁻¹ = w := mul_inv_eq_iff_eq_mul.mpr hsw
  have hsN := mem_normalizer_of_cent3 hΩ.conjInvariant hsw'
  obtain ⟨R, r, haY, hRf, hAR, hu, hr⟩ := P.partner_data hΩ hex F hA ha
  have ha2 : aa * aa = 1 := mul_self_eq_one_of_isClassicalMember3 ha
  set mk := QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) with hmk
  set φ := actQuot3 Ω w s hsN with hφ
  have hrange : ∀ q ∈ (P.D.hom P.i₁).range, φ q ∈ (P.D.hom P.i₁).range := by
    intro q hq
    rw [P.range_eq hΩ hex F] at hq
    have hle : (⨆ N ∈ {N | Fb Ω w N}, locImg Ω w N) ≤
        (P.D.hom P.i₁).range.comap φ.toMonoidHom := by
      refine iSup₂_le fun N hN u hu' => ?_
      obtain ⟨y, hy, rfl⟩ := hu'
      have hN' : Fb Ω w (conjSub s N) := by
        have := (fb_conj_iff hΩ.conjInvariant s).mpr hN
        rwa [hsw'] at this
      have hmem : (⟨s * (y : G) * s⁻¹, Asc77.S24.conj_mem_of_mem_normalizer _ hsN y.2⟩ :
          ↥(locLayer Ω w)) ∈ (conjSub s N).subgroupOf (locLayer Ω w) :=
        Subgroup.mem_subgroupOf.mpr (conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hy))
      rw [Subgroup.mem_comap]
      show φ (mk y) ∈ (P.D.hom P.i₁).range
      rw [hφ, actQuot3_mk]
      exact ((P.fb_iff hΩ hex F).mp hN').2 ⟨_, hmem, rfl⟩
    exact hle hq
  have hfix : ∀ y ∈ R, φ (P.D.hom P.i₁ y) = P.D.hom P.i₁ y := by
    intro y hy
    have hmem : P.D.hom P.i₁ y ∈ locImg Ω w A := hAR ▸ Subgroup.mem_map_of_mem _ hy
    obtain ⟨x', hx', hxeq⟩ := hmem
    rw [← hxeq]
    exact actQuot3_mk_of_comm Ω w hsN x'.2 (hsA x' (Subgroup.mem_subgroupOf.mp hx'))
  have hZ : ∀ g : (P.D.kind P.i₁).G, (∀ x, g * x = x * g) → g = 1 := by
    intro g hg
    have : g ∈ Subgroup.center (P.D.kind P.i₁).G :=
      Subgroup.mem_center_iff.mpr fun x => (hg x).symm
    rw [hF.center_bot] at this
    exact this
  have hZR : ∀ g ∈ R, (∀ y ∈ R, g * y = y * g) → g * g = 1 → g = 1 ∨ g = r :=
    fun g hg _ hsq => hu.unique g hg hsq
  have hdich := NDB.G2S.dichotomy_of_fg0 (P.D.hom P.i₁) hψ hZ (hF.fg0 R hRf) hZR φ
    (actQuot3_sq Ω w hsN hs2) (fun g => hrange _ ⟨g, rfl⟩) hfix
  have hxmem : ∀ x ∈ layerX Ω w, ∃ hxY : x ∈ locLayer Ω w, ∃ g, P.D.hom P.i₁ g = mk ⟨x, hxY⟩ :=
    fun x hx => ⟨layerX_le_locLayer Ω w hx,
      P.mk_mem_range_of_mem_layerX hΩ hex F hx (layerX_le_locLayer Ω w hx)⟩
  rcases hdich with h1 | h2
  · left
    refine lift_trivial3 hΩ hex P.p1 P.o3 ?_
    intro x hx
    obtain ⟨hxY, g, hg⟩ := hxmem x hx
    have hφx : φ (mk ⟨x, hxY⟩) = mk ⟨x, hxY⟩ := by rw [← hg]; exact h1 g
    rw [hφ, actQuot3_mk] at hφx
    exact mem_oddCoreOf_of_mk_eq3 (Asc77.S24.conj_mem_of_mem_normalizer _ hsN hxY) hxY hφx
  · right
    refine lift_trivial3 hΩ hex P.p1 P.o3 ?_
    intro x hx
    obtain ⟨hxY, g, hg⟩ := hxmem x hx
    have hax : aa * x * aa⁻¹ ∈ locLayer Ω w :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ haY hxY) (Subgroup.inv_mem _ haY)
    have hu' : s * (aa * x * aa⁻¹) * s⁻¹ ∈ locLayer Ω w :=
      Asc77.S24.conj_mem_of_mem_normalizer _ hsN hax
    have hmka2 : mk ⟨aa, haY⟩ * mk ⟨aa, haY⟩ = 1 := by
      rw [← map_mul]
      have : (⟨aa, haY⟩ : ↥(locLayer Ω w)) * ⟨aa, haY⟩ = 1 := Subtype.ext ha2
      rw [this, map_one]
    have e1 : mk ⟨s * (aa * x * aa⁻¹) * s⁻¹, hu'⟩ = φ (mk ⟨aa * x * aa⁻¹, hax⟩) :=
      (actQuot3_mk Ω w hsN ⟨aa * x * aa⁻¹, hax⟩).symm
    have e2 : mk ⟨aa * x * aa⁻¹, hax⟩ = mk ⟨aa, haY⟩ * mk ⟨x, hxY⟩ * (mk ⟨aa, haY⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have e3 : φ (mk ⟨aa, haY⟩) = mk ⟨aa, haY⟩ :=
      actQuot3_mk_of_comm Ω w hsN haY (hsA aa ha.mem)
    have e4 : φ (mk ⟨x, hxY⟩) = mk ⟨aa, haY⟩ * mk ⟨x, hxY⟩ * (mk ⟨aa, haY⟩)⁻¹ := by
      rw [← hg, h2 g, hr]
    have key : mk ⟨s * (aa * x * aa⁻¹) * s⁻¹, hu'⟩ = mk ⟨x, hxY⟩ := by
      calc mk ⟨s * (aa * x * aa⁻¹) * s⁻¹, hu'⟩
          = φ (mk ⟨aa, haY⟩ * mk ⟨x, hxY⟩ * (mk ⟨aa, haY⟩)⁻¹) := by rw [e1, e2]
        _ = mk ⟨aa, haY⟩ * (mk ⟨aa, haY⟩ * mk ⟨x, hxY⟩ * (mk ⟨aa, haY⟩)⁻¹) *
            (mk ⟨aa, haY⟩)⁻¹ := by rw [map_mul, map_mul, map_inv, e3, e4]
        _ = (mk ⟨aa, haY⟩ * mk ⟨aa, haY⟩) * mk ⟨x, hxY⟩ *
            (mk ⟨aa, haY⟩ * mk ⟨aa, haY⟩)⁻¹ := by group
        _ = mk ⟨x, hxY⟩ := by rw [hmka2]; group
    have h3 := mem_oddCoreOf_of_mk_eq3 hu' hxY key
    have e : (s * aa) * x * (s * aa)⁻¹ * x⁻¹ = s * (aa * x * aa⁻¹) * s⁻¹ * x⁻¹ := by group
    rw [e]
    exact h3

end Action

end CFSG.ClassicalInvolution.Q3.Q3W.EX
