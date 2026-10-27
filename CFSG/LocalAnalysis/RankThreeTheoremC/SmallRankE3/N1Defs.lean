module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5Large
import CFSG.LocalAnalysis.RankThreeTheoremC.D2FusionFocal3
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

structure Sit (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) :
    Prop where
  setting : Setting G
  u0 : FullCoreLocal G
  situation : SmallRankSituation G p P M
  five_le : 5 ≤ p

namespace Sit

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem prime (hS : Sit G p P M) : p.Prime := sigmaA_prime p hS.situation.mem_sigmaA

theorem p_ge (hS : Sit G p P M) : 5 ≤ p := hS.five_le

theorem ne_two (hS : Sit G p P M) : p ≠ 2 := by
  have := hS.p_ge
  omega

theorem simple (hS : Sit G p P M) : IsSimpleGroup G := hS.setting.simple

theorem nonab (hS : Sit G p P M) : ∃ a b : G, a * b ≠ b * a := hS.setting.nonab

theorem isTwoLocal (hS : Sit G p P M) : IsTwoLocal M := hS.situation.isCoreMaxLocal.1.1

theorem charTwo (hS : Sit G p P M) : M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
  hS.setting.charTwo M hS.isTwoLocal

theorem sylow_le_and_pRank (hS : Sit G p P M) :
    (P : Subgroup G) ≤ M ∧ Open.pRank p (P : Subgroup G) = 3 :=
  sylow_le_of_isCoreMaxLocal hS.setting hS.situation.mem_sigmaA hS.situation.isCoreMaxLocal

theorem sylow_le (hS : Sit G p P M) : (P : Subgroup G) ≤ M := hS.sylow_le_and_pRank.1

theorem pRank_eq (hS : Sit G p P M) : Open.pRank p (P : Subgroup G) = 3 :=
  hS.sylow_le_and_pRank.2

theorem three_le_pRank (hS : Sit G p P M) : 3 ≤ Open.pRank p (P : Subgroup G) :=
  hS.pRank_eq.ge

theorem normalizer_le (hS : Sit G p P M) {S : Subgroup G} (hSp : IsPGroup p S) (hSM : S ≤ M)
    (hS2 : 2 ≤ Open.pRank p S) : normalizer (S : Set G) ≤ M :=
  normalizer_le_of_le_of_two_le_pRank hS.setting hS.u0 hS.situation.mem_sigmaA
    hS.situation.isCoreMaxLocal hSp hSM hS2

theorem centralizer_le_of_pRank (hS : Sit G p P M) {y : G} (hy : y ∈ M) (hyp : orderOf y = p)
    (h3 : 3 ≤ Open.pRank p (M ⊓ centralizer ({y} : Set G))) :
    centralizer ({y} : Set G) ≤ M := by
  have hprime := hS.prime
  by_contra h
  refine hS.situation.largeObstruction_empty y ⟨hy, ?_, ?_, ?_, h⟩
  · intro h1
    rw [h1, orderOf_one] at hyp
    exact hprime.one_lt.ne hyp
  · rw [← hyp]
    exact pow_orderOf_eq_one y
  · exact h3.trans (CFSG.SectionRank.pRank_mono hprime.one_lt inf_le_right)

theorem plane (hS : Sit G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) : SmallRankPlane p (P : Subgroup G) x z :=
  SmallRankPlane.of_situation hS.setting hS.situation hx hz

theorem orderOf_point (hS : Sit G p P M) {x : G} (hx : SmallRankPoint P M x) : orderOf x = p := by
  haveI : Fact p.Prime := ⟨hS.prime⟩
  exact orderOf_eq_prime hx.pow_eq_one hx.ne_one

theorem pRank_centralizer_le (hS : Sit G p P M) {x : G} (hx : SmallRankPoint P M x) :
    Open.pRank p (centralizer ({x} : Set G)) ≤ 2 := by
  by_contra h
  push Not at h
  exact hS.situation.largeObstruction_empty x
    ⟨hS.sylow_le hx.mem, hx.ne_one, hx.pow_eq_one, by omega, hx.not_centralizer_le⟩

theorem le_of_plane_le (hS : Sit G p P M) {B : Subgroup G} (hBP : B ≤ (P : Subgroup G))
    (hBC : centralizer (B : Set G) ≤ M) {Q : Subgroup G} (hQ : IsPGroup p Q) (hBQ : B ≤ Q) :
    Q ≤ M :=
  fail614G_le_of_plane_le hS.setting hS.situation hBP hBC hQ hBQ

theorem centralizer_plane_le (hS : Sit G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) :
    centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) ≤ M :=
  CFSG.LocalAnalysis.RankThreeTheoremC.centralizer_plane_le hS.setting hS.situation hx hz

theorem normalizer_plane_le (hS : Sit G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) :
    normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) ≤ M :=
  CFSG.LocalAnalysis.RankThreeTheoremC.normalizer_plane_le hS.setting hS.u0 hS.situation hx hz

theorem pRank_centralizer_le_of_mem_plane (hS : Sit G p P M) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {y : G}
    (hyB : y ∈ zpowers x ⊔ zpowers z) (hyZ : y ∉ zpowers z) :
    Open.pRank p (centralizer ({y} : Set G)) ≤ 2 := by
  have hprime := hS.prime
  obtain ⟨g, -, hconj⟩ :=
    exists_mem_normalizer_conj_zpowers hS.setting hS.situation hx hz hyB hyZ
  have hcz : ∀ w : G,
      centralizer ({w} : Set G) = centralizer ((zpowers w : Subgroup G) : Set G) := fun w => by
    rw [zpowers_eq_closure, centralizer_closure]
  have hC : centralizer ({y} : Set G) =
      (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by
    calc centralizer ({y} : Set G)
        = centralizer ((zpowers y : Subgroup G) : Set G) := hcz _
      _ = centralizer (((zpowers x).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
        rw [hconj]
      _ = (centralizer ((zpowers x : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom :=
        (centralizer_map_automorphism _ _).symm
      _ = (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by rw [hcz x]
  rw [hC, pRank_map_automorphism p hprime.one_lt]
  exact hS.pRank_centralizer_le hx

theorem mem_zpowers_of_conj_mem_plane (hS : Sit G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {g : G} (hg : g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z) :
    g * z * g⁻¹ ∈ zpowers z := by
  have hprime := hS.prime
  by_contra hgz
  have h2 := hS.pRank_centralizer_le_of_mem_plane hx hz hg hgz
  have hPz' : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
      centralizer ({g * z * g⁻¹} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hqz : q * z = z * q := mem_centralizer_iff.mp hz.centralizes q hq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * q * g⁻¹ * (g * z * g⁻¹) = g * (q * z) * g⁻¹ := by group
      _ = g * (z * q) * g⁻¹ := by rw [hqz]
      _ = g * z * g⁻¹ * (g * q * g⁻¹) := by group
  have h4 := CFSG.SectionRank.pRank_mono hprime.one_lt hPz'
  rw [pRank_map_automorphism p hprime.one_lt] at h4
  have := hS.three_le_pRank
  omega

theorem three_rank_le (hS : Sit G p P M) :
    ∀ Q : Subgroup G, Q ≤ M → Q ≠ ⊥ → IsPGroup 2 Q →
      Open.pRank 3 (M ⊓ normalizer (Q : Set G)) ≤ 3 := by
  intro Q _ hQ hQ2
  have hloc : IsTwoLocal (normalizer (Q : Set G)) := ⟨Q, hQ, hQ2, rfl⟩
  have h1 := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) _ hloc
  have h2 := CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3)
    (inf_le_right : M ⊓ normalizer (Q : Set G) ≤ normalizer (Q : Set G))
  have h3 := hS.setting.rank
  omega

theorem eq_top_of_isPGroup_quotient (hS : Sit G p P M) (N : Subgroup M) [N.Normal]
    (hN : IsPGroup p (M ⧸ N)) : N = ⊤ := by
  haveI : Fact p.Prime := ⟨hS.prime⟩
  by_contra hNtop
  have hidx : 1 < N.index := by
    have h0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : N.index ≠ 1 := fun h => hNtop (Subgroup.index_eq_one.mp h)
    omega
  haveI hnt : Nontrivial (M ⧸ N) := Finite.one_lt_card_iff_nontrivial.mp hidx
  set π := QuotientGroup.mk' N with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  set P' : Sylow p M := P.subtype hS.sylow_le with hP'
  have himg : (P' : Subgroup M).map π = ⊤ := by
    have h := (Sylow.mapSurjective hπ P').3 (hN.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have hPcomm : (P' : Subgroup M) ≤ _root_.commutator M := by
    have h1 : (_root_.commutator M).map M.subtype = ⁅M, M⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    intro y hy
    have hyP : (y : G) ∈ (P : Subgroup G) := hy
    have := CFSG.LocalAnalysis.RankThreeTheoremC.sylow_le_commutator_of_gamma_two hS.setting hS.situation.mem_sigmaA
      hS.situation.isCoreMaxLocal hS.situation.gamma_two_le hyP
    rw [← h1] at this
    obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp this
    exact (Subtype.ext hyy) ▸ hy'
  have hperfQ : _root_.commutator (M ⧸ N) = ⊤ := by
    have h2 : (_root_.commutator M).map π = _root_.commutator (M ⧸ N) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr hπ]
    rw [← h2, eq_top_iff, ← himg]
    exact Subgroup.map_mono hPcomm
  haveI : Group.IsPerfect (M ⧸ N) := Group.isPerfect_def.mpr hperfQ
  exact Group.IsPerfect.not_isNilpotent (M ⧸ N) hN.isNilpotent

end Sit

structure Plane65E3 {A : Type} [Group A] [Finite A] (p : ℕ) (P : Sylow p A) (X : Subgroup A)
    (x z : A) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections ↥X
  plane : SmallRankPlane p (P : Subgroup A) x z
  sylow_le : (P : Subgroup A) ≤ X
  z_central : z ∈ centralizer ((P : Subgroup A) : Set A)
  pRank_eq : Open.pRank p (P : Subgroup A) = 3
  rank_centralizer : Open.pRank p (centralizer ({x} : Set A)) ≤ 2
  sylow_centralizer : CFSG.ABGLocalTools.IsSylowOf p
    ((P : Subgroup A) ⊓ centralizer ({x} : Set A)) (centralizer ({x} : Set A))
  perfect : ∀ (N : Subgroup ↥X) [N.Normal], IsPGroup p (↥X ⧸ N) → N = ⊤

theorem Sit.plane65E3 {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hS : Sit G p P M) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) : Plane65E3 p P M x z where
  prime := hS.prime
  five_le := hS.p_ge
  catalog := CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.setting.kProper M
    (fun h => hx.not_centralizer_le (h ▸ le_top))
  plane := hS.plane hx hz
  sylow_le := hS.sylow_le
  z_central := hz.centralizes
  pRank_eq := hS.pRank_eq
  rank_centralizer := hS.pRank_centralizer_le hx
  sylow_centralizer := by
    haveI : Fact p.Prime := ⟨hS.prime⟩
    exact CFSG.ABGLocalTools.isSylowOf_iff.mpr
      ⟨inf_le_right, (P.isPGroup').to_le inf_le_left, hx.sylow_centralizer⟩
  perfect := fun N _ hN => hS.eq_top_of_isPGroup_quotient N hN

@[expose] def KFactP65SingleE3 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (P : Sylow p A) (X : Subgroup A) (x z : A),
    Plane65E3 p P X x z → p = 5 →
    X ⊓ centralizer (pCoreOf 2 X : Set A) ≤ pCoreOf 2 X →
    (∀ Q : Subgroup A, Q ≤ X → Q ≠ ⊥ → IsPGroup 2 Q →
      Open.pRank 3 (X ⊓ normalizer (Q : Set A)) ≤ 3) →
    (∃ L : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p), IsComponentOf L ⊤ ∧ p ∣ Nat.card L ∧
      ∀ K : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p), IsComponentOf K ⊤ →
        p ∣ Nat.card K → K = L) →
    ∀ W : Subgroup A, W ≤ X → Nat.Coprime (Nat.card W) (2 * p) →
      zpowers x ⊔ zpowers z ≤ normalizer (W : Set A) → W ≤ rankThreePrimeCore p X

@[expose] def NoTwoComponentsE3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → ∀ (P : Sylow 5 G) (M : Subgroup G),
    SmallRankSituation G 5 P M → ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
    ¬ ∃ L K : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) 5),
      IsComponentOf L ⊤ ∧ 5 ∣ Nat.card L ∧ IsComponentOf K ⊤ ∧ 5 ∣ Nat.card K ∧ L ≠ K

@[expose] def KFactP65SingleAt (p : ℕ) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (P : Sylow p A) (X : Subgroup A) (x z : A),
    Plane65E3 p P X x z →
    X ⊓ centralizer (pCoreOf 2 X : Set A) ≤ pCoreOf 2 X →
    (∀ Q : Subgroup A, Q ≤ X → Q ≠ ⊥ → IsPGroup 2 Q →
      Open.pRank 3 (X ⊓ normalizer (Q : Set A)) ≤ 3) →
    (∃ L : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p), IsComponentOf L ⊤ ∧ p ∣ Nat.card L ∧
      ∀ K : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p), IsComponentOf K ⊤ →
        p ∣ Nat.card K → K = L) →
    ∀ W : Subgroup A, W ≤ X → Nat.Coprime (Nat.card W) (2 * p) →
      zpowers x ⊔ zpowers z ≤ normalizer (W : Set A) → W ≤ rankThreePrimeCore p X

theorem KFactP65SingleE3.toAt (h : KFactP65SingleE3) : KFactP65SingleAt 5 :=
  fun A _ _ P X x z hpl hX hrank huniq W hWX hcop hBW =>
    h A 5 P X x z hpl rfl hX hrank huniq W hWX hcop hBW

@[expose] def NoTwoComponentsAt (p : ℕ) : Prop :=
  5 ≤ p → ∀ (G : Type) [Group G] [Finite G], Setting G → ∀ (P : Sylow p G) (M : Subgroup G),
    SmallRankSituation G p P M → ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
    ¬ ∃ L K : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p),
      IsComponentOf L ⊤ ∧ p ∣ Nat.card L ∧ IsComponentOf K ⊤ ∧ p ∣ Nat.card K ∧ L ≠ K

theorem NoTwoComponentsE3.toAt (h : NoTwoComponentsE3) : NoTwoComponentsAt 5 :=
  fun _ G _ _ hS P M hsit x z hx hz => h G hS P M hsit x z hx hz

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1
