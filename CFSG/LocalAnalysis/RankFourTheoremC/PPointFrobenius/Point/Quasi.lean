module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.LemmaA
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.LocalAnalysis.RankThreeTheoremC.PSLTwoPElements

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.LocalAnalysis.RankFourTheoremC CFSG.RankThreeCoreUniqueness.Helpers CFSG.Open
  CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.RankThreeTheoremC (eq_one_of_commute_of_mulEquiv_psl_two)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

@[expose] def PtSchurBound : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p n : ℕ) [Fact p.Prime], 5 ≤ p → 2 ≤ n →
    Group.IsPerfect L → Nonempty (L ⧸ Subgroup.center L ≃* PSL(2, GaloisField p n)) →
      Nat.card (Subgroup.center L) ≤ 2

private theorem pt_K_perfect [Fact p.Prime] {R : Sylow p (RedCent p x)}
    {K : Subgroup (RedCent p x)} (hK : PPointReduced p M x R K) : ⁅K, K⁆ = K :=
  Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hK.component.2.2.1)

private theorem pt_restrict [Fact p.Prime] {K : Subgroup (RedCent p x)} (hK : ⁅K, K⁆ = K) :
    ∃ ψ : ptKx p x K →* K, Function.Surjective ψ ∧
      ψ.ker = (ptKx p x K ⊓ GLBPrimeCore p (centralizer ({x} : Set G))).subgroupOf
        (ptKx p x K) := by
  have hmapK := ptKx_map p x hK
  have hJC : ptKx p x K ≤ centralizer ({x} : Set G) := ptKx_le_centralizer p x K
  let ψ₀ : ptKx p x K →* RedCent p x :=
    (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)).comp
      (Subgroup.inclusion hJC)
  have hψ₀ : ∀ j : ptKx p x K, ψ₀ j ∈ K := by
    intro j
    have hmem : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
        (Subgroup.inclusion hJC j) ∈ ((ptKx p x K).subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr j.2)
    rw [hmapK] at hmem
    exact hmem
  let ψ : ptKx p x K →* K := ψ₀.codRestrict K hψ₀
  have hψsurj : Function.Surjective ψ := by
    intro k
    have hk : (k : RedCent p x) ∈ ((ptKx p x K).subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) := by
      rw [hmapK]
      exact k.2
    obtain ⟨c, hc, hck⟩ := Subgroup.mem_map.mp hk
    refine ⟨⟨(c : G), Subgroup.mem_subgroupOf.mp hc⟩, Subtype.ext ?_⟩
    exact hck
  have hN : primeComplementCore (G := centralizer ({x} : Set G)) p =
      (GLBPrimeCore p (centralizer ({x} : Set G))).subgroupOf (centralizer ({x} : Set G)) :=
    (glbPrimeCore_subgroupOf p _).symm
  have hker : ψ.ker = (ptKx p x K ⊓ GLBPrimeCore p (centralizer ({x} : Set G))).subgroupOf
      (ptKx p x K) := by
    ext j
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hj : (j : G) ∈ ptKx p x K := j.2
    constructor
    · intro h
      have h' : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
          (Subgroup.inclusion hJC j) = 1 := congrArg Subtype.val h
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf,
        Subgroup.coe_inclusion] at h'
      exact ⟨hj, h'⟩
    · rintro ⟨-, h⟩
      apply Subtype.ext
      show QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
          (Subgroup.inclusion hJC j) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf,
        Subgroup.coe_inclusion]
      exact h
  exact ⟨ψ, hψsurj, hker⟩

private theorem pt_primeCore_odd [Fact p.Prime] (hG : FrobGlobal G) (hl : PtPoint p P M x) :
    Odd (Nat.card (GLBPrimeCore p (centralizer ({x} : Set G)))) := by
  have hD1 : CFSG.AGLEmbedding.D1Global G :=
    ⟨hG.simple, hG.nonab, hG.kProper, hG.charTwo, hG.rank, hG.pre⟩
  have hcore2 := IsPPoint.not_two_dvd_card_primeCore hD1 hG.d1 hl.loc hl.point
  exact Nat.not_even_iff_odd.mp (fun h2 => hcore2 (even_iff_two_dvd.mp h2))

theorem pt_center_Kx [Fact p.Prime] (hG : FrobGlobal G) (hl : PtPoint p P M x) {n : ℕ}
    {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)} (hD : PtData p n P M x R K) :
    ptKx p x K ⊓ centralizer ((ptKx p x K : Subgroup G) : Set G) =
      ptKx p x K ⊓ GLBPrimeCore p (centralizer ({x} : Set G)) := by
  obtain ⟨e⟩ := hD.equiv
  have hmapK := ptKx_map p x (pt_K_perfect hD.red)
  have hJC : ptKx p x K ≤ centralizer ({x} : Set G) := ptKx_le_centralizer p x K
  refine le_antisymm ?_ (le_inf inf_le_left (pt_Kx_central hG hl hD))
  rintro z ⟨hzJ, hzZ⟩
  refine ⟨hzJ, ?_⟩
  have hzC : z ∈ centralizer ({x} : Set G) := hJC hzJ
  have hzK : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
      ⟨z, hzC⟩ ∈ K := by
    rw [← hmapK]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hzJ)
  have hc : ∀ k ∈ K, k * QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
      ⟨z, hzC⟩ = QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
      ⟨z, hzC⟩ * k := by
    intro k hk
    rw [← hmapK] at hk
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hk
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_iff.mp hzZ (c : G) (Subgroup.mem_subgroupOf.mp hc)
  have h1 := eq_one_of_commute_of_mulEquiv_psl_two e hzK hc
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    (glbPrimeCore_subgroupOf p _).symm, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem pt_Kx_center_eq_bot [Fact p.Prime] (hs : PtSchurBound) (hG : FrobGlobal G)
    (hl : PtPoint p P M x) {n : ℕ} {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)}
    (hD : PtData p n P M x R K) :
    ptKx p x K ⊓ centralizer ((ptKx p x K : Subgroup G) : Set G) = ⊥ := by
  have hp5 := hl.p5
  have hn3 := hD.three_le
  obtain ⟨e⟩ := hD.equiv
  obtain ⟨ψ, hψs, hker⟩ := pt_restrict (p := p) (x := x) (pt_K_perfect hD.red)
  have hZ := pt_center_Kx hG hl hD
  have hcen : Subgroup.center ↥(ptKx p x K) = ψ.ker := by
    ext z
    rw [hker, Subgroup.mem_subgroupOf, ← hZ, Subgroup.mem_inf, Subgroup.mem_center_iff]
    constructor
    · intro h
      refine ⟨z.2, ?_⟩
      rw [mem_centralizer_iff]
      intro j hj
      exact congrArg Subtype.val (h ⟨j, hj⟩)
    · rintro ⟨-, h⟩ g
      apply Subtype.ext
      exact mem_centralizer_iff.mp h (g : G) g.2
  have hperf : Group.IsPerfect ↥(ptKx p x K) := Subgroup.isPerfect_iff.mpr (ptKx_perfect p x K)
  have hq : Nonempty (↥(ptKx p x K) ⧸ Subgroup.center ↥(ptKx p x K) ≃*
      PSL(2, GaloisField p n)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)).trans e⟩
  have hle2 := hs ↥(ptKx p x K) p n hp5 (by omega) hperf hq
  have hodd := pt_primeCore_odd hG hl
  have hcard : Nat.card (Subgroup.center ↥(ptKx p x K)) =
      Nat.card ↥(ptKx p x K ⊓ GLBPrimeCore p (centralizer ({x} : Set G))) := by
    rw [hcen, hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hoddZ : Odd (Nat.card (Subgroup.center ↥(ptKx p x K))) := by
    rw [hcard]
    exact hodd.of_dvd_nat (card_dvd_of_le inf_le_right)
  have hpos : 0 < Nat.card (Subgroup.center ↥(ptKx p x K)) := Nat.card_pos
  have h1 : Nat.card (Subgroup.center ↥(ptKx p x K)) = 1 := by
    obtain ⟨k, hk⟩ := hoddZ
    omega
  have hbot : Subgroup.center ↥(ptKx p x K) = ⊥ := Subgroup.card_eq_one.mp h1
  rw [eq_bot_iff]
  intro z hz
  have hzc : (⟨z, hz.1⟩ : ↥(ptKx p x K)) ∈ Subgroup.center ↥(ptKx p x K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact mem_centralizer_iff.mp hz.2 (g : G) g.2
  rw [hbot, Subgroup.mem_bot] at hzc
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hzc)

private theorem pt_Kx_equiv [Fact p.Prime] (hs : PtSchurBound) (hG : FrobGlobal G)
    (hl : PtPoint p P M x) {n : ℕ} {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)}
    (hD : PtData p n P M x R K) : Nonempty (↥(ptKx p x K) ≃* ↥K) := by
  obtain ⟨ψ, hψs, hker⟩ := pt_restrict (p := p) (x := x) (pt_K_perfect hD.red)
  have hbot := pt_Kx_center_eq_bot hs hG hl hD
  have hZ := pt_center_Kx hG hl hD
  have hinj : Function.Injective ψ := by
    refine (MonoidHom.ker_eq_bot_iff ψ).mp ?_
    rw [hker, ← hZ, hbot]
    exact Subgroup.bot_subgroupOf (G := G) (H := ptKx p x K)
  exact ⟨MulEquiv.ofBijective ψ ⟨hinj, hψs⟩⟩

theorem pt_Kx_isComponent [Fact p.Prime] (hs : PtSchurBound) (hG : FrobGlobal G)
    (hl : PtPoint p P M x) {n : ℕ} {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)}
    (hD : PtData p n P M x R K) : IsComponentOf (ptKx p x K) (centralizer ({x} : Set G)) := by
  have hle : ptKx p x K ≤ centralizer ({x} : Set G) := ptKx_le_centralizer p x K
  refine ⟨hle, ?_, ?_⟩
  ·
    have hnorm : ((ptKx p x K).subgroupOf (centralizer ({x} : Set G))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (ptKx_normal p x hD.red.normal)
    exact IsSubnormal.step hle hnorm (IsSubnormal.refl _)
  ·
    obtain ⟨φ⟩ := pt_Kx_equiv hs hG hl hD
    exact CFSG.Open.IsQuasisimple.of_mulEquiv φ hD.red.component.2.2

private theorem pt_isComponent_subgroupOf {L C : Subgroup G} (h : IsComponentOf L C) :
    CFSG.IsComponent (L.subgroupOf C) := by
  rw [CFSG.isComponent_iff_open]
  refine ⟨le_top, ?_, ?_⟩
  · have h1 := h.2.1.comap C.subtype
    rwa [show C.comap C.subtype = ⊤ from Subgroup.subgroupOf_self (H := C)] at h1
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.2

theorem pt_component_eq [Fact p.Prime] (hs : PtSchurBound) (hG : FrobGlobal G)
    (hl : PtPoint p P M x) {n : ℕ} {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)}
    (hD : PtData p n P M x R K) {J : Subgroup G}
    (hJ : IsComponentOf J (centralizer ({x} : Set G))) : J = ptKx p x K := by
  have hKp : ⁅K, K⁆ = K := pt_K_perfect hD.red
  have hmapK := ptKx_map p x hKp
  have hJC : J ≤ centralizer ({x} : Set G) := hJ.1
  have hJxC : ptKx p x K ≤ centralizer ({x} : Set G) := ptKx_le_centralizer p x K
  have hcJ := pt_isComponent_subgroupOf hJ
  have hcX := pt_isComponent_subgroupOf (pt_Kx_isComponent hs hG hl hD)
  rcases CFSG.LocalCores.distinct_components_commute hcJ hcX with heq | hcomm
  · have h := Subgroup.subgroupOf_inj.mp heq
    rwa [inf_of_le_left hJC, inf_of_le_left hJxC] at h
  · exfalso
    haveI : IsCyclic ↥(centralizer (K : Set (RedCent p x))) := hD.isCyclic
    let φ : ↥J →* RedCent p x :=
      (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)).comp
        (Subgroup.inclusion hJC)
    have hφcen : ∀ g : ↥J, ∀ k ∈ K, k * φ g = φ g * k := by
      intro g k hk
      rw [← hmapK] at hk
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hk
      have e1 : φ g = QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
          (Subgroup.inclusion hJC g) := rfl
      rw [e1, ← map_mul, ← map_mul]
      congr 1
      have hg' : Subgroup.inclusion hJC g ∈ J.subgroupOf (centralizer ({x} : Set G)) :=
        Subgroup.mem_subgroupOf.mpr g.2
      have h := Subgroup.commutator_mem_commutator hg' hc
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
      exact h.symm
    have hφ1 : ∀ g : ↥J, φ g = 1 := by
      have hker : commutator ↥J ≤ φ.ker := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        intro g _ h _
        rw [MonoidHom.mem_ker, map_commutatorElement]
        have hg : φ g ∈ centralizer (K : Set (RedCent p x)) :=
          mem_centralizer_iff.mpr fun k hk => hφcen g k hk
        have hh : φ h ∈ centralizer (K : Set (RedCent p x)) :=
          mem_centralizer_iff.mpr fun k hk => hφcen h k hk
        have hc := (inferInstance : IsMulCommutative ↥(centralizer (K : Set (RedCent p x)))).is_comm.comm
          ⟨φ g, hg⟩ ⟨φ h, hh⟩
        exact commutatorElement_eq_one_iff_mul_comm.mpr (congrArg Subtype.val hc)
      intro g
      exact hker (hJ.2.2.1 ▸ Subgroup.mem_top g)
    have hJO : J ≤ GLBPrimeCore p (centralizer ({x} : Set G)) := by
      intro g hg
      have h1 := hφ1 ⟨g, hg⟩
      have h2 : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
          (Subgroup.inclusion hJC ⟨g, hg⟩) = 1 := h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        (glbPrimeCore_subgroupOf p _).symm, Subgroup.mem_subgroupOf] at h2
      exact h2
    have hsolO : Group.IsSolvable ↥(GLBPrimeCore p (centralizer ({x} : Set G))) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (pt_primeCore_odd hG hl)
    have : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJO)
    haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
    have : Nontrivial ↥J := (QuotientGroup.mk_surjective (s := Subgroup.center ↥J)).nontrivial
    have : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
    exact Group.IsPerfect.not_isSolvable ↥J inferInstance

theorem pt_layer_eq_Kx [Fact p.Prime] (hs : PtSchurBound) (hG : FrobGlobal G)
    (hl : PtPoint p P M x) {n : ℕ} {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)}
    (hD : PtData p n P M x R K) : layerOf x = ptKx p x K := by
  rw [layerOf_eq]
  unfold CFSG.Open.GLBLayer
  have h : {L : Subgroup G | IsComponentOf L (centralizer ({x} : Set G))} = {ptKx p x K} :=
    Set.ext fun J => ⟨fun hJ => pt_component_eq hs hG hl hD hJ,
      fun hJ => (Set.mem_singleton_iff.mp hJ) ▸ pt_Kx_isComponent hs hG hl hD⟩
  rw [h, sSup_singleton]

theorem pt_layer_not_le [Fact p.Prime] (hs : PtSchurBound) (hG : FrobGlobal G)
    (hl : PtPoint p P M x) {n : ℕ} {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)}
    (hD : PtData p n P M x R K) : ¬ layerOf x ≤ M := by
  rw [pt_layer_eq_Kx hs hG hl hD]
  exact ptKx_not_le hD.red

theorem pt_layer_equiv [Fact p.Prime] (hs : PtSchurBound) (hG : FrobGlobal G)
    (hl : PtPoint p P M x) {n : ℕ} {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)}
    (hD : PtData p n P M x R K) : Nonempty (layerOf x ≃* PSL(2, GaloisField p n)) := by
  rw [pt_layer_eq_Kx hs hG hl hD]
  obtain ⟨φ⟩ := pt_Kx_equiv hs hG hl hD
  obtain ⟨e⟩ := hD.equiv
  exact ⟨φ.trans e⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
