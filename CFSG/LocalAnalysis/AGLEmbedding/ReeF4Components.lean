module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4MSideOdd
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBlockInner
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorLayer
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4CompPerfect
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4CompThree
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4CompOrbit

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Comp3

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M H R X : Subgroup G}


omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {Y : Type*} [Group Y] {L : Subgroup Y} {a b : Y}
    (h : L.map (MulAut.conj a).toMonoidHom = L.map (MulAut.conj b).toMonoidHom) :
    a⁻¹ * b ∈ Subgroup.normalizer (L : Set Y) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have e : ∀ c d : Y, (L.map (MulAut.conj d).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      L.map (MulAut.conj (c * d)).toMonoidHom := by
    intro c d
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  change L.map (MulAut.conj (a⁻¹ * b)).toMonoidHom = L
  rw [← e, ← h, e, inv_mul_cancel]
  ext x
  simp

theorem D1ReeF4Data.le_centralizer_component (h : D1ReeF4Data P M H R X)
    (hind : ∀ q ∈ GLBBetaFour G, q < 5 → D1At G q) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hB3 : StmtBlockThree) (hb : StmtBlockInnerNormalizer) (hα : KFactThreeOrFiveDvd)
    (hP5 : KFactBlockFiveParabolic) (hO5 : KFactOutFiveCyclic) (hRank : StmtComponentRank)
    (hLift : StmtBarPRankLift) {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hLb : IsComponentOf Lb ⊤) :
    barM M X ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have h3 := h.surv.ph3
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Kb := barM M (H ⊓ M) with hKb
  obtain ⟨L, hL2, hbar, hcase⟩ := h3.exists_weakSBlock_or_le_inf hLb
  subst hbar
  obtain ⟨y, hyL, hyK, hy3, l, hlL, hyl⟩ := h.exists_three_element hB3 hα hL2 hcase
  have horb := fun m g hg hinj => h.orbit_le hind hRank hLift hLb hyL hyK hy3 hlL hyl
    (m := m) g hg hinj
  have hXR : X ≤ R := h.surv.le_R
  have hXM : X ≤ M := hXR.trans h3.le_M
  have hXK : X ≤ H ⊓ M := hXR.trans h3.le_inf
  have hX5 : IsPGroup 5 X := fun x => ⟨1, Subtype.ext (by simpa using h.elem.2 x x.2)⟩
  have hXN : barM M X ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro xb hxb
    by_contra hxbN
    obtain ⟨⟨x, hxM⟩, hxX, rfl⟩ := hxb
    have hxX' : x ∈ X := Subgroup.mem_subgroupOf.mp hxX
    have hxbK : mk ⟨x, hxM⟩ ∈ Kb :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hXK hxX'))
    have hxp : IsPGroup 5 (Subgroup.zpowers (mk ⟨x, hxM⟩)) := by
      refine isPGroup_zpowers_of_pow_eq_one (k := 1) ?_
      have hx1 : x ^ 5 = 1 := h.elem.2 x hxX'
      have : (⟨x, hxM⟩ : M) ^ 5 = 1 := Subtype.ext (by simpa using hx1)
      rw [pow_one, ← map_pow, this, map_one]
    have hinj := injective_conj_pow_of_not_mem_normalizer hxp hxbN
    have := horb 5 (fun j => (mk ⟨x, hxM⟩) ^ (j : ℕ)) (fun j => Kb.pow_mem hxbK _) hinj
    omega
  set B := H ⊓ M ⊓ Subgroup.normalizer (R : Set G) with hB
  set Y₁ := B ⊓ preM M (Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) with hY₁
  have hidx : Y₁.relIndex B ≤ 3 := relIndex_le_of_forall_fin 3 fun g => by
    by_contra hall
    push Not at hall
    have hgM : ∀ j, ((g j : B) : G) ∈ M := fun j => (g j).2.1.2
    set gb : Fin 4 → ↥M ⧸ CFSG.pCore 2 ↥M := fun j => mk ⟨g j, hgM j⟩ with hgb
    have hinj : Function.Injective fun j => (barM M L).map (MulAut.conj (gb j)).toMonoidHom := by
      intro i j hij
      by_contra hne
      apply hall i j hne
      rw [Subgroup.mem_subgroupOf]
      refine ⟨((g i)⁻¹ * g j : B).2, ?_⟩
      have hN := mem_normalizer_of_map_conj_eq hij
      have hmem : ((((g i)⁻¹ * g j : B) : G)) ∈ M := ((g i)⁻¹ * g j : B).2.1.2
      refine (mem_preM hmem).mpr ?_
      have e : mk ⟨(((g i)⁻¹ * g j : B) : G), hmem⟩ = (gb i)⁻¹ * gb j := by
        rw [hgb, ← map_inv, ← map_mul]
        rfl
      rw [e]
      exact hN
    exact absurd (horb 4 gb (fun j => Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr (g j).2.1)) hinj) (by norm_num)
  have hXB : X ≤ B := le_inf hXK fun x hx => Subgroup.le_normalizer (hXR hx)
  have hXY : X ≤ Y₁ := le_inf hXB (le_preM hXM hXN)
  have hY₁M : Y₁ ≤ M := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hY₁N : ∀ g ∈ Y₁, ∃ hgM : g ∈ M, mk ⟨g, hgM⟩ ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun g hg =>
    ⟨hY₁M hg, (mem_preM (hY₁M hg)).mp hg.2⟩
  have hCn : Y₁ ≤ Subgroup.normalizer ((X ⊓ blockCentralizer M L : Subgroup G) : Set G) := by
    intro g hg
    obtain ⟨hgM, hgN⟩ := hY₁N g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h.normalizer_le hg.1,
      mem_normalizer_blockCentralizer' hgM hgN⟩
  rcases h.irred Y₁ inf_le_left hidx _ inf_le_left hCn with hC | hC
  swap
  ·
    rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
    have hxX : x ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hxC : x ∈ X ⊓ blockCentralizer M L := by rw [hC]; exact hxX
    exact (mem_blockCentralizer_iff ⟨x, hxM⟩).mp hxC.2
  set Lb := barM M L with hLbdef
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  set Xb := barM M X with hXbdef
  have hXbC : Xb ⊓ Cb = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨⟨x, hxM⟩, hx, rfl⟩, hxC⟩
    have hx' : x ∈ X ⊓ blockCentralizer M L :=
      ⟨Subgroup.mem_subgroupOf.mp hx, (mem_blockCentralizer_iff ⟨x, hxM⟩).mpr hxC⟩
    rw [hC, Subgroup.mem_bot] at hx'
    subst hx'
    exact Subgroup.mem_bot.mpr (map_one mk)
  set I := Xb ⊓ (Lb ⊔ Cb) with hI
  have hIC : I ⊓ Cb = ⊥ := le_bot_iff.mp ((inf_le_inf_right _ inf_le_left).trans hXbC.le)
  have hLbN : Lb ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := Subgroup.le_normalizer
  have hXbK : Xb ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    Subgroup.map_mono (Subgroup.comap_mono (hXK.trans (hKeq ▸ inf_le_right)))
  have hX5b : IsPGroup 5 Xb := (hX5.comap_subtype (K := M)).map _
  obtain ⟨J, hJN, hJ5, hIJ⟩ : ∃ J : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      J ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ Nat.Coprime 5 (Nat.card J) ∧
      ∀ x ∈ I, ∃ l ∈ J, x * l⁻¹ ∈ Cb := by
    rcases hcase with hLw | hLK
    ·
      have hPLK : blockParabolic M (pCoreOf 2 H) L ≤ Kb :=
        Subgroup.map_mono (Subgroup.comap_mono (fun x hx => hKeq ▸ ⟨hL2.le hx.2, hx.1⟩))
      refine ⟨blockParabolic M (pCoreOf 2 H) L,
        (Subgroup.map_mono (Subgroup.comap_mono inf_le_right)).trans hLbN, ?_, fun x hx =>
          h3.exists_mem_blockParabolic h84 h86 hD2 hb hLw (hXbK hx.1) hx.2⟩
      exact hP5 G M (pCoreOf 2 H) L h3.isKGroup.1 h3.asc81bHyp hLw (h3.nineThree h93 hLw)
        (h3.nineThree_not_one h85 hD2 hLw).1 (h3.not_isSylowTwoOf_inf h85 hD2 hLw)
        (fun l hl hcond => hb h3 h84 h86 hD2 hLw l hl hcond)
        (fun W hW hWW => h.coprime_of_perfect (hW.trans hPLK) hWW)
    ·
      refine ⟨Lb, hLbN, ?_, fun x hx => ?_⟩
      · exact Nat.Coprime.coprime_dvd_right ((card_barM_dvd hL2.le).trans
          (Subgroup.card_dvd_of_le (h.perfect_le L hLK hL2.perfect))) (glbPrimeCore_coprime 5 H)
      · have hLC : Lb ≤ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
          Subgroup.le_normalizer.trans
            ((Subgroup.normal_subgroupOf_iff_le_normalizer
              (Subgroup.centralizer_le_normalizer _)).mp
              (Subgroup.normal_subgroupOf_centralizer_normalizer _))
        have hx2 : x ∈ Lb ⊔ Cb := hx.2
        rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Lb Cb hLC] at hx2
        obtain ⟨l', hl', c, hc, rfl⟩ := hx2
        refine ⟨l', hl', ?_⟩
        have : l' * c * l'⁻¹ ∈ Cb := (Subgroup.mem_normalizer_iff.mp (hLC hl') c).mp hc
        simpa [mul_assoc] using this
  have hI1 : I = ⊥ := by
    have hdvd := card_dvd_of_faithful_inner (inf_le_left.trans hXN) hJN hIC hIJ
    obtain ⟨a, ha⟩ := (hX5b.to_le (inf_le_left : I ≤ Xb)).exists_card_eq
    rw [ha] at hdvd
    have hc := Nat.Coprime.coprime_dvd_right hdvd hJ5
    have ha0 : a = 0 := by
      by_contra ha0
      have := Nat.Coprime.coprime_dvd_right (dvd_pow_self 5 ha0) hc
      norm_num at this
    rw [ha0, pow_zero] at ha
    exact Subgroup.card_eq_one.mp ha
  exfalso
  have hMtop : M ≠ ⊤ := fun hM => h3.not_le (hM ▸ le_top)
  have hcat : CatalogSimpleSections (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (catalogSimpleSections_of_isKProper h3.glob.kProper M hMtop).quotient _
  have hXbc : Nat.card Xb = 5 ^ 2 := by
    rw [hXbdef, card_barM_of_isPGroup (by norm_num) (by norm_num) hXM hX5, h.card_X]
  set Qb := barM M Y₁ with hQb
  have hQN : Qb ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨g, hgM⟩, hg, rfl⟩
    exact (hY₁N g (Subgroup.mem_subgroupOf.mp hg)).2
  have hQX : Qb ≤ Subgroup.normalizer (Xb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨g, hgM⟩, hg, rfl⟩
    exact mem_normalizer_barM hgM (h.normalizer_le (Subgroup.mem_subgroupOf.mp hg).1)
  refine hO5 _ Lb Xb Qb hLb (hcat.isCatalogGroup_center_quotient hLb) hXN
    (isElemAbelian_barM h.elem) hXbc hI1 hQN hQX fun F hF hQF => ?_
  set F₀ := X ⊓ preM M F with hF₀
  have hF₀n : Y₁ ≤ Subgroup.normalizer (F₀ : Set G) := by
    intro g hg
    have hgM := hY₁M hg
    have hgF : mk ⟨g, hgM⟩ ∈ Subgroup.normalizer (F : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      hQF (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hg))
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h.normalizer_le hg.1,
      mem_normalizer_preM hgM hgF⟩
  have hbarF : barM M F₀ = F := barM_inf_preimage hF
  rcases h.irred Y₁ inf_le_left hidx F₀ inf_le_left hF₀n with h0 | h0
  · left
    rw [← hbarF, h0]
    simp [barM]
  · right
    rw [← hbarF, h0]

end Comp3

end CFSG.AGLEmbedding
