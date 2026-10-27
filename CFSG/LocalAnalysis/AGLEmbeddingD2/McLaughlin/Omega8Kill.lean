module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Omega8Sylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Omega8Cited
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieBuild
import CFSG.GroupTheory.BaerSuzuki.Helpers

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeTheoremC

section Generic

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem eq_one_of_isTwoElement_of_abelian_normal (hO : CFSG.pCore 2 Q = ⊥) {Z : Subgroup Q}
    [hZn : Z.Normal] (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) {z : Q} (hz : z ∈ Z)
    (hz2 : ∃ k : ℕ, z ^ (2 ^ k) = 1) : z = 1 := by
  let P2 : Subgroup Q :=
    { carrier := {x | x ∈ Z ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1}
      mul_mem' := by
        rintro a b ⟨ha, k, hk⟩ ⟨hb, l, hl⟩
        refine ⟨Z.mul_mem ha hb, k + l, ?_⟩
        rw [(Commute.mul_pow (hZc a ha b hb) _), pow_add, pow_mul, hk, one_pow, one_mul,
          mul_comm (2 ^ k), pow_mul, hl, one_pow]
      one_mem' := ⟨Z.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, k, hk⟩
        exact ⟨Z.inv_mem ha, k, by rw [inv_pow, hk, inv_one]⟩ }
  have hP2n : P2.Normal := by
    refine ⟨fun x ⟨hx, k, hk⟩ g => ⟨hZn.conj_mem x hx g, k, ?_⟩⟩
    rw [conj_pow, hk]
    group
  have hP2p : IsPGroup 2 P2 := by
    intro x
    obtain ⟨-, k, hk⟩ := x.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hle : P2 ≤ CFSG.pCore 2 Q :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hP2n hP2p
  rw [hO] at hle
  exact Subgroup.mem_bot.mp (hle ⟨hz, hz2⟩)

omit [Finite Q] in
theorem le_of_le_sup_centralizer (hO : CFSG.pCore 2 Q = ⊥) {Lb Sb : Subgroup Q} [hLn : Lb.Normal]
    (hLC : Lb ⊓ Subgroup.centralizer (Lb : Set Q) = ⊥)
    (hCS : Subgroup.centralizer (Lb : Set Q) ≤ Subgroup.centralizer (Sb : Set Q))
    (hS2 : IsPGroup 2 Sb) (hSle : Sb ≤ Lb ⊔ Subgroup.centralizer (Lb : Set Q)) : Sb ≤ Lb := by
  set C := Subgroup.centralizer (Lb : Set Q) with hCdef
  have hCn : C.Normal := inferInstance
  intro x hx
  obtain ⟨l, hl, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hSle hx)
  have hcZ : ∀ c' ∈ C, c * c' = c' * c := by
    intro c' hc'
    have h1 : (l * c) * c' = c' * (l * c) :=
      Subgroup.mem_centralizer_iff.mp (hCS hc') _ hx
    have h2 : l * c' = c' * l := Subgroup.mem_centralizer_iff.mp hc' l hl
    have : l * (c * c') = l * (c' * c) := by
      calc l * (c * c') = (l * c) * c' := by group
        _ = c' * (l * c) := h1
        _ = (c' * l) * c := by group
        _ = (l * c') * c := by rw [h2]
        _ = l * (c' * c) := by group
    exact mul_left_cancel this
  have hlc : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc l hl
  obtain ⟨k, hk⟩ := hS2 ⟨l * c, hx⟩
  have hk' : (l * c) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hc2 : c ^ (2 ^ k) = 1 := by
    rw [(Commute.mul_pow hlc _)] at hk'
    have hmem : c ^ (2 ^ k) ∈ Lb ⊓ C := by
      refine ⟨?_, C.pow_mem hc _⟩
      have : c ^ (2 ^ k) = (l ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_right hk'
      rw [this]
      exact Lb.inv_mem (Lb.pow_mem hl _)
    rw [hLC] at hmem
    exact Subgroup.mem_bot.mp hmem
  set Z := C ⊓ Subgroup.centralizer (C : Set Q) with hZ
  have hZn : Z.Normal := inferInstance
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 a ha.1
  have hcZ' : c ∈ Z := ⟨hc, Subgroup.mem_centralizer_iff.mpr fun c' hc' => (hcZ c' hc').symm⟩
  have hc1 : c = 1 := eq_one_of_isTwoElement_of_abelian_normal hO hZc hcZ' ⟨k, hc2⟩
  rw [hc1, mul_one]
  exact hl

omit [Finite Q] in
theorem two_dvd_relIndex_of_not_mem {B N : Subgroup Q} [hNn : N.Normal] {s : Q} (hsB : s ∈ B)
    (hsN : s ∉ N) (hs2 : ∃ k : ℕ, s ^ (2 ^ k) = 1) : 2 ∣ (B ⊓ N).relIndex B := by
  classical
  set N' : Subgroup ↥B := (B ⊓ N).subgroupOf B with hN'
  have hN'n : N'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hN', Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨B.mul_mem (B.mul_mem g.2 hx.1) (B.inv_mem g.2), hNn.conj_mem _ hx.2 g⟩
  have hrel : (B ⊓ N).relIndex B = Nat.card (↥B ⧸ N') := rfl
  set q : ↥B ⧸ N' := QuotientGroup.mk' N' ⟨s, hsB⟩ with hq
  have hq1 : q ≠ 1 := by
    intro h
    apply hsN
    have := (QuotientGroup.eq_one_iff (N := N') _).mp h
    rw [hN', Subgroup.mem_subgroupOf] at this
    exact this.2
  obtain ⟨k, hk⟩ := hs2
  have hqk : q ^ (2 ^ k) = 1 := by
    rw [hq, ← map_pow]
    have : (⟨s, hsB⟩ : ↥B) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hord : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hqk
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hq1 (orderOf_eq_one_iff.mp (by simpa using hj'))
  rw [hrel]
  refine (dvd_pow_self 2 hj0).trans ?_
  rw [← hj']
  exact orderOf_dvd_natCard q

omit [Finite Q] in
theorem exists_pow_pElement_not_mem {N : Subgroup Q} [hNn : N.Normal] {x : Q} {p : ℕ}
    (hp : p.Prime) (hfin : 0 < orderOf x) (hdvd : p ∣ orderOf (QuotientGroup.mk' N x)) :
    ∃ k : ℕ, x ^ k ∉ N ∧ ∃ e : ℕ, (x ^ k) ^ (p ^ e) = 1 := by
  obtain ⟨e, m, hm, ho⟩ := Nat.exists_eq_pow_mul_and_not_dvd hfin.ne' p hp.ne_one
  refine ⟨m, fun hmem => ?_, e, ?_⟩
  · apply hm
    have h1 : (QuotientGroup.mk' N x) ^ m = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    exact hdvd.trans (orderOf_dvd_of_pow_eq_one h1)
  · rw [← pow_mul, mul_comm, ← ho, pow_orderOf_eq_one]

omit [Finite Q] in
theorem isPGroup_zpowers_of_pow_pow_eq_one {x : Q} {p : ℕ} {e : ℕ}
    (h : x ^ (p ^ e) = 1) : IsPGroup p (Subgroup.zpowers x) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨e, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

end Generic

section Config

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowTwoOf_barM_of_isSylowTwoOf {M K T : Subgroup G} (hKM : K ≤ M)
    (hT : IsSylowTwoOf T K) : IsSylowTwoOf (barM M T) (barM M K) := by
  have := isSylowTwoOf_map_hom' hT (rhoX M K hKM)
  rwa [map_subgroupOf_rhoX hKM hT.1, MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self (H := K),
    map_subgroupOf_rhoX hKM le_rfl] at this

omit [Finite G] in
theorem barM_self_eq_top (M : Subgroup G) : barM M M = ⊤ := by
  unfold barM
  rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']

omit [Finite G] in
theorem isSylowTwoOf_of_barM_top {M T : Subgroup G} (hTM : T ≤ M) (hQT : pCoreOf 2 M ≤ T)
    (hT2 : IsPGroup 2 T) (h : IsSylowTwoOf (barM M T) ⊤) : IsSylowTwoOf T M := by
  refine ⟨hTM, hT2, ?_⟩
  have e := relIndex_barM_eq hTM le_rfl hQT
  rw [barM_self_eq_top] at e
  have h2 := h.2.2
  change ¬ 2 ∣ (barM M T).relIndex ⊤ at h2
  change ¬ 2 ∣ T.relIndex M
  rwa [← e]

omit [Finite G] in
theorem barM_inf_barM_eq {M S L : Subgroup G} (hQS : pCoreOf 2 M ≤ S) :
    barM M L ⊓ barM M S ≤ barM M (S ⊓ L) := by
  rintro b ⟨hbL, hbS⟩
  obtain ⟨a, haL, rfl⟩ := mem_barM_iff'.mp hbL
  obtain ⟨a', ha'S, ha'b⟩ := mem_barM_iff'.mp hbS
  have hq : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (a'⁻¹ * a) = 1 := by
    rw [map_mul, map_inv, ha'b, inv_mul_cancel]
  have hqS : ((a'⁻¹ * a : ↥M) : G) ∈ S := hQS (coe_mem_pCoreOf_two_of_mk_eq_one _ hq)
  have haS : (a : G) ∈ S := by
    have : (a : G) = (a' : G) * ((a'⁻¹ * a : ↥M) : G) := by simp
    rw [this]
    exact S.mul_mem ha'S hqS
  exact mem_barM_iff'.mpr ⟨a, ⟨haS, haL⟩, rfl⟩

omit [Finite G] in
theorem inf_centralizer_eq_bot_of_center_eq_bot {Q : Type} [Group Q] {Lb : Subgroup Q}
    (hZ : Subgroup.center ↥Lb = ⊥) : Lb ⊓ Subgroup.centralizer (Lb : Set Q) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxC⟩
  have hmem : (⟨x, hxL⟩ : ↥Lb) ∈ Subgroup.center ↥Lb := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
  rw [hZ] at hmem
  have := congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  simpa using this

omit [Finite G] in
theorem not_two_dvd_relIndex_of_isParabolicTwo {Q : Type} [Group Q] {Lb P : Subgroup Q}
    (h : IsParabolicTwo Lb P) : ¬ 2 ∣ P.relIndex Lb := by
  obtain ⟨-, T₀, hT₀, hN⟩ := h
  have hT₀P : T₀ ≤ P := fun x hx => hN ⟨hT₀.1 hx, Subgroup.le_normalizer hx⟩
  intro hd
  exact hT₀.2.2 (hd.trans (Subgroup.relIndex_dvd_of_le_left Lb hT₀P))

theorem PairStrongCtx.isSylowTwoOf_M_of_cases (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) (hOut : KFactOmega8Out)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (h2 : NineThreeTwo M (pCoreOf 2 H) L) [hLn : (barM M L).Normal]
    (hZ1 : Subgroup.center ↥(barM M L) = ⊥) (hΩ : IsOmegaEightPlus ↥(barM M L))
    (hcase : 2 ∣ (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) ⊓
        (barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))).relIndex
          (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G))) ∨
      ∀ m : ↥M ⧸ CFSG.pCore 2 ↥M, ∃ ℓ ∈ barM M L,
        (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)).map
            (MulAut.conj m).toMonoidHom =
          (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)).map
            (MulAut.conj ℓ).toMonoidHom)
    {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) (hQT : pCoreOf 2 M ≤ T) :
    IsSylowTwoOf T M := by
  have hpr := hctx.pair
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  set S := pCoreOf 2 H with hS
  set Q := ↥M ⧸ CFSG.pCore 2 ↥M
  set Lb := barM M L with hLb
  set C := Subgroup.centralizer (Lb : Set Q) with hC
  set Bb := barM M (Subgroup.normalizer (S : Set G)) with hBb
  set PL := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hPL
  have hcw : ∀ c ∈ C, ∀ L' : Subgroup G, IsWeakSBlock M S L' →
      c ∈ Subgroup.centralizer (barM M L' : Set Q) := fun c hc L' hL' => by
    rw [hk1 L' hL']; exact hc
  have hCB : C ≤ Bb := fun c hc =>
    hpr.mem_barM_normalizer_of_centralizes_weakSBlocks h84 h86 hX (hcw c hc)
  have hCS : C ≤ Subgroup.centralizer (barM M S : Set Q) := fun c hc =>
    hpr.mem_centralizer_of_centralizes_weakSBlocks h84 h86 hX (hcw c hc)
  have hLC : Lb ⊓ C = ⊥ := inf_centralizer_eq_bot_of_center_eq_bot hZ1
  have hQS : pCoreOf 2 M ≤ S := hpr.twoCore_M_le
  have hSM : S ≤ M := hpr.twoCore_le
  have hPLeq : Lb ⊓ Bb = PL :=
    le_antisymm (barM_inf_barM_eq (hQS.trans Subgroup.le_normalizer))
      (le_inf (barM_mono inf_le_right) (barM_mono inf_le_left))
  have hodd : ¬ 2 ∣ (Lb ⊓ Bb).relIndex Lb := by
    rw [hPLeq]; exact not_two_dvd_relIndex_of_isParabolicTwo h2.2.1
  have hBbHM : Bb = barM M (H ⊓ M) := by
    rw [hBb, hS, hpr.normalizer_twoCore_H]
    simp only [barM, Subgroup.inf_subgroupOf_right]
  have hTb : IsSylowTwoOf (barM M T) Bb := by
    rw [hBbHM]; exact isSylowTwoOf_barM_of_isSylowTwoOf inf_le_right hT
  have hTM : T ≤ M := hT.1.trans inf_le_right
  apply isSylowTwoOf_of_barM_top hTM hQT hT.2.1
  have hO : CFSG.pCore 2 Q = ⊥ := pCore_quotient_pCore_eq_bot' 2
  have hD6 := hOut.1 Q Lb hΩ hLn
  rcases hcase with heven | hstab
  · exact isSylowTwoOf_top_of_even hD6 hCB hLC hodd heven hTb
  have hS2 : IsPGroup 2 (barM M S) :=
    ((pCoreOf_isPGroup 2 H).comap_subtype.map _)
  have hSB : barM M S ≤ Bb := barM_mono Subgroup.le_normalizer
  by_cases hSle : barM M S ≤ Lb ⊔ C
  ·
    have hSL : barM M S ≤ Lb := le_of_le_sup_centralizer hO hLC hCS hS2 hSle
    have hSeq : barM M S = pCoreOf 2 PL := by
      rw [← h2.2.2]
      exact le_antisymm (fun x hx => barM_inf_barM_eq hQS ⟨hSL hx, hx⟩)
        (barM_mono inf_le_left)
    have hsup : Lb ⊔ Bb = ⊤ := by
      rw [eq_top_iff]
      intro m _
      obtain ⟨ℓ, hℓ, hmℓ⟩ := hstab m
      have hm' : ℓ⁻¹ * m ∈ Subgroup.normalizer (PL : Set Q) := by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        constructor
        · intro hh
          have hx : m * h * m⁻¹ ∈ PL.map (MulAut.conj ℓ).toMonoidHom := by
            rw [← hmℓ]
            exact ⟨h, hh, by simp⟩
          obtain ⟨y, hy, hyx⟩ := hx
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
          have : ℓ⁻¹ * m * h * (ℓ⁻¹ * m)⁻¹ = y := by
            rw [show ℓ⁻¹ * m * h * (ℓ⁻¹ * m)⁻¹ = ℓ⁻¹ * (m * h * m⁻¹) * ℓ by group, ← hyx]
            group
          rw [this]; exact hy
        · intro hh
          have hx : ℓ * (ℓ⁻¹ * m * h * (ℓ⁻¹ * m)⁻¹) * ℓ⁻¹ ∈
              PL.map (MulAut.conj m).toMonoidHom := by
            rw [hmℓ]
            exact ⟨_, hh, by simp⟩
          obtain ⟨y, hy, hyx⟩ := hx
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
          have : y = h := by
            have e : m * y * m⁻¹ = m * h * m⁻¹ := by
              rw [hyx]; group
            simpa using e
          rw [← this]; exact hy
      have hm'S : ℓ⁻¹ * m ∈ Subgroup.normalizer (barM M S : Set Q) := by
        rw [hSeq]
        exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 PL hm'
      have hm'B : ℓ⁻¹ * m ∈ Bb := mem_barM_normalizer_of_mem_normalizer_barM hSM hQS hm'S
      have : m = ℓ * (ℓ⁻¹ * m) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hℓ hm'B
    exact isSylowTwoOf_top_of_sup_eq_top hsup hodd hTb
  ·
    obtain ⟨s, hs, hsN⟩ := Set.not_subset.mp hSle
    obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
    have hk' : s ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have heven := two_dvd_relIndex_of_not_mem (N := Lb ⊔ C) (hSB hs) hsN ⟨k, hk'⟩
    exact isSylowTwoOf_top_of_even hD6 hCB hLC hodd heven hTb

theorem PairStrongCtx.isSylowTwoOf_M_of_outer (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) (hOut : KFactOmega8Out) (hTri : KFactOmega8Triality)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (h2 : NineThreeTwo M (pCoreOf 2 H) L) [hLn : (barM M L).Normal]
    (hZ1 : Subgroup.center ↥(barM M L) = ⊥) (hΩ : IsOmegaEightPlus ↥(barM M L))
    (hsolv : BlockPLThreeSolv M (pCoreOf 2 H) L)
    (hnot2 : ¬ IsSylowTwoOf (barM M (pCoreOf 2 H ⊓ L)) (barM M L))
    (hLp : ⁅barM M L, barM M L⁆ = barM M L) (h3L : 3 ∣ Nat.card (barM M L))
    {u : ↥M ⧸ CFSG.pCore 2 ↥M} (hu : u ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)))
    (hu3 : IsPGroup 3 (Subgroup.zpowers u))
    (huC : u ∉ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) (hQT : pCoreOf 2 M ≤ T) :
    IsSylowTwoOf T M := by
  obtain ⟨n, hnS, rfl⟩ := mem_barM_iff'.mp hu
  have hun := (mk_mem_normalizer_blocks hL hk1 n.2 hnS).2
  have hne : barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ≠ barM M L := by
    intro h
    exact hsolv (barM M L) h.ge hLp h3L
  have hnotSyl : ¬ IsSylowTwoOf (pCoreOf 2 (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)))
      (barM M L) := by
    rw [← h2.2.2]; exact hnot2
  have hstab := hTri _ (barM M L) _ hΩ hLn h2.2.1 hne hnotSyl ⟨_, hun, hu3, huC⟩
  exact hctx.isSylowTwoOf_M_of_cases h84 h86 hD2 hOut hk1 h2 hZ1 hΩ (Or.inr hstab) hT hQT

omit [Finite G] in
theorem mk_mem_normalizer_barM {M R : Subgroup G} {n : ↥M}
    (hn : (n : G) ∈ Subgroup.normalizer (R : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) n ∈
      Subgroup.normalizer (barM M R : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) y
  constructor
  · rintro hy
    obtain ⟨r, hr, hry⟩ := mem_barM_iff'.mp hy
    refine mem_barM_iff'.mpr ⟨n * r * n⁻¹, ?_, by rw [map_mul, map_mul, map_inv, hry]⟩
    exact (Subgroup.mem_normalizer_iff.mp hn r).mp hr
  · rintro hy
    obtain ⟨r, hr, hry⟩ := mem_barM_iff'.mp hy
    refine mem_barM_iff'.mpr ⟨n⁻¹ * r * n, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) r).mp hr
      simpa using this
    · rw [map_mul, map_mul, map_inv, hry]; group

theorem PairStrongCtx.isSylowTwoOf_M_of_swap (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) (hOut : KFactOmega8Out) (hTri : KFactOmega8Triality)
    (hPar : KFactOmega8Parabolic)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (h2 : NineThreeTwo M (pCoreOf 2 H) L) [hLn : (barM M L).Normal]
    (hZ1 : Subgroup.center ↥(barM M L) = ⊥) (hΩ : IsOmegaEightPlus ↥(barM M L))
    (hsolv : BlockPLThreeSolv M (pCoreOf 2 H) L)
    (hnot2 : ¬ IsSylowTwoOf (barM M (pCoreOf 2 H ⊓ L)) (barM M L))
    (hLp : ⁅barM M L, barM M L⁆ = barM M L) (h3L : 3 ∣ Nat.card (barM M L))
    (hRel : IsElemAbelian 3 (barM M R)) (hR9 : Nat.card (barM M R) = 9)
    (hRPL : barM M R ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))
    (hirr : IrreducibleOn (barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G))) (barM M R))
    {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) (hQT : pCoreOf 2 M ≤ T) :
    IsSylowTwoOf T M := by
  set Q := ↥M ⧸ CFSG.pCore 2 ↥M
  set S := pCoreOf 2 H with hS
  set Lb := barM M L with hLb
  set C := Subgroup.centralizer (Lb : Set Q) with hC
  set PL := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hPL
  set Rb := barM M R with hRb
  have hpr := hctx.pair
  have hCn : C.Normal := inferInstance
  have hPL2 : Open.pRank 3 PL ≤ 2 :=
    (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three (barM_mono inf_le_left)).trans
      ((hpr.pRank_barM_normalizer_le Nat.prime_three (by decide)).trans hctx.esc.pRank_H.le)
  have hnotSyl : ¬ IsSylowTwoOf (pCoreOf 2 PL) Lb := by
    rw [← h2.2.2]; exact hnot2
  obtain ⟨hself, -, -, hlines⟩ := hPar Q Lb PL hΩ h2.2.1
  obtain ⟨E₁, hE₁, hc₁, hnormE₁⟩ := hlines hnotSyl hsolv hPL2 Rb hRPL hRel hR9
  set Nb := barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) with hNb
  have hmove : ¬ Nb ≤ Subgroup.normalizer (E₁ : Set Q) := by
    intro hle
    rcases hirr E₁ hE₁ hle with h | h
    · rw [h, Subgroup.card_bot] at hc₁; omega
    · rw [h, hR9] at hc₁; omega
  obtain ⟨x, hxN, hxE⟩ := Set.not_subset.mp hmove
  obtain ⟨n, hn, rfl⟩ := mem_barM_iff'.mp hxN
  have hnH : (n : G) ∈ H := hn.1.1
  have hnS : (n : G) ∈ Subgroup.normalizer (S : Set G) := by
    rw [hS, hpr.normalizer_twoCore_H]; exact hnH
  have hnPL := (mk_mem_normalizer_blocks hL hk1 n.2 hnS).2
  have hnR := mk_mem_normalizer_barM (M := M) hn.2
  have hnC : QuotientGroup.mk' (CFSG.pCore 2 ↥M) n ∉ Lb ⊔ C := by
    intro hmem
    obtain ⟨ℓ, hℓ, c, hc, hlc⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    have hcPL : c ∈ Subgroup.centralizer (PL : Set Q) := fun y hy =>
      Subgroup.mem_centralizer_iff.mp hc y (barM_mono inf_le_right hy)
    have hcR : c ∈ Subgroup.centralizer (Rb : Set Q) := fun y hy =>
      Subgroup.mem_centralizer_iff.mp hc y (barM_mono inf_le_right (hRPL hy))
    have hcE : c ∈ Subgroup.centralizer (E₁ : Set Q) := fun y hy => hcR y (hE₁ hy)
    have hℓ_eq : ℓ = QuotientGroup.mk' (CFSG.pCore 2 ↥M) n * c⁻¹ := by
      rw [← hlc]; group
    have hcinvN : ∀ K : Subgroup Q, c ∈ Subgroup.centralizer (K : Set Q) →
        c⁻¹ ∈ Subgroup.normalizer (K : Set Q) := fun K hK =>
      Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hK)
    have hℓPL : ℓ ∈ Subgroup.normalizer (PL : Set Q) := by
      rw [hℓ_eq]; exact Subgroup.mul_mem _ hnPL (hcinvN _ hcPL)
    have hℓR : ℓ ∈ Subgroup.normalizer (Rb : Set Q) := by
      rw [hℓ_eq]; exact Subgroup.mul_mem _ hnR (hcinvN _ hcR)
    have hℓP : ℓ ∈ PL := hself ⟨hℓ, hℓPL⟩
    have hℓE : ℓ ∈ Subgroup.normalizer (E₁ : Set Q) := hnormE₁ ⟨hℓP, hℓR⟩
    apply hxE
    rw [← hlc]
    exact Subgroup.mul_mem _ hℓE (Subgroup.centralizer_le_normalizer _ hcE)
  set D := Lb ⊔ C with hD
  have hDn : D.Normal := inferInstance
  set y := QuotientGroup.mk' (CFSG.pCore 2 ↥M) n with hy
  have hord1 : orderOf (QuotientGroup.mk' D y) ≠ 1 := by
    intro h
    exact hnC ((QuotientGroup.eq_one_iff y).mp (orderOf_eq_one_iff.mp h))
  have hord6 : orderOf (QuotientGroup.mk' D y) ∣ 6 :=
    (orderOf_dvd_natCard _).trans (hOut.1 Q Lb hΩ hLn)
  have hyB : y ∈ barM M (Subgroup.normalizer (S : Set G)) :=
    mem_barM_iff'.mpr ⟨n, hnS, rfl⟩
  have hfin : 0 < orderOf y := orderOf_pos y
  have h23 : 2 ∣ orderOf (QuotientGroup.mk' D y) ∨ 3 ∣ orderOf (QuotientGroup.mk' D y) := by
    have h6 : orderOf (QuotientGroup.mk' D y) ∈ Nat.divisors 6 :=
      Nat.mem_divisors.mpr ⟨hord6, by norm_num⟩
    have : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [this] at h6
    simp only [Finset.mem_insert, Finset.mem_singleton] at h6
    rcases h6 with h | h | h | h
    · exact absurd h hord1
    · left; rw [h]
    · right; rw [h]
    · left; rw [h]; norm_num
  rcases h23 with h2d | h3d
  · obtain ⟨k, hk, e, he⟩ := exists_pow_pElement_not_mem Nat.prime_two hfin h2d
    have heven := two_dvd_relIndex_of_not_mem (N := D)
      (Subgroup.pow_mem _ hyB k) hk ⟨e, he⟩
    exact hctx.isSylowTwoOf_M_of_cases h84 h86 hD2 hOut hk1 h2 hZ1 hΩ (Or.inl heven) hT hQT
  · obtain ⟨k, hk, e, he⟩ := exists_pow_pElement_not_mem Nat.prime_three hfin h3d
    exact hctx.isSylowTwoOf_M_of_outer h84 h86 hD2 hOut hTri hL hk1 h2 hZ1 hΩ hsolv hnot2 hLp h3L
      (Subgroup.pow_mem _ hyB k) (isPGroup_zpowers_of_pow_pow_eq_one he) hk hT hQT

end Config

end CFSG.AGLEmbeddingD2.McLaughlin
