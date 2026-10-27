module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Claim1
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Setup
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.LocalAnalysis.GLTheoremB.Prop95NonAbCore
public import CFSG.LocalAnalysis.GLTheoremB.Prop95NonAbLift

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB Subgroup
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M D X W : Subgroup G}

theorem chief_W_le_M (h : Lemma97Chief p M D X W) : W ≤ M :=
  h.le_core.trans (Subgroup.map_subtype_le _)

theorem chief_X_le_W (h : Lemma97Chief p M D X W) : X ≤ W := h.lt.le

theorem chief_X_le_M (h : Lemma97Chief p M D X W) : X ≤ M := (chief_X_le_W h).trans (chief_W_le_M h)

theorem chief_M_le_normalizer_X (h : Lemma97Chief p M D X W) :
    M ≤ Subgroup.normalizer (X : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (chief_X_le_M h)).1 h.normalX

theorem chief_not_dvd_card_W (hp : p.Prime) (h : Lemma97Chief p M D X W) :
    ¬ p ∣ Nat.card W := fun hd =>
  not_dvd_card_glaPPrimeCoreOf hp M (hd.trans (Subgroup.card_dvd_of_le h.le_core))

theorem chief_not_dvd_card_X (hp : p.Prime) (h : Lemma97Chief p M D X W) :
    ¬ p ∣ Nat.card X := fun hd =>
  chief_not_dvd_card_W hp h (hd.trans (Subgroup.card_dvd_of_le (chief_X_le_W h)))

theorem twoLocal_ne_top {m : ℕ} (hS : GLStanding G m p) (hM : IsTwoLocal M) : M ≠ ⊤ := by
  intro htop
  obtain ⟨P, hP1, hP2, hMP⟩ := hM
  have hPn : P.Normal := Subgroup.normalizer_eq_top_iff.1 (hMP ▸ htop)
  haveI := hS.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
  · exact hP1 h
  · rw [h] at hP2
    exact not_isPGroup_two hS.nonabelian (hP2.of_equiv Subgroup.topEquiv)


end Basic

section Quot

variable {G : Type} [Group G] [Finite G]

abbrev QM (M X : Subgroup G) : Type := ↥M ⧸ X.subgroupOf M

variable {p : ℕ} {M D X W : Subgroup G} [(X.subgroupOf M).Normal]

abbrev piQ (M X : Subgroup G) [(X.subgroupOf M).Normal] : ↥M →* QM M X :=
  QuotientGroup.mk' (X.subgroupOf M)

abbrev NQ (M X W : Subgroup G) [(X.subgroupOf M).Normal] : Subgroup (QM M X) :=
  (W.subgroupOf M).map (piQ M X)

abbrev HQ (M X : Subgroup G) [(X.subgroupOf M).Normal] (d : G) : Subgroup (QM M X) :=
  ((pCoreOf 2 (Subgroup.centralizer ({d} : Set G))).subgroupOf M).map (piQ M X)

abbrev GQ (M X D : Subgroup G) [(X.subgroupOf M).Normal] : Subgroup (QM M X) :=
  ((gammaD D).subgroupOf M).map (piQ M X)

theorem piQ_eq_one_iff {x : ↥M} : piQ M X x = 1 ↔ (x : G) ∈ X := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem piQ_surjective : Function.Surjective (piQ M X) := QuotientGroup.mk'_surjective _

theorem mem_NQ {y : QM M X} : y ∈ NQ M X W ↔ ∃ w : ↥M, (w : G) ∈ W ∧ piQ M X w = y := by
  simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem mem_HQ {d : G} {y : QM M X} :
    y ∈ HQ M X d ↔ ∃ w : ↥M, (w : G) ∈ pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) ∧
      piQ M X w = y := by
  simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem mem_GQ {y : QM M X} : y ∈ GQ M X D ↔ ∃ w : ↥M, (w : G) ∈ gammaD D ∧ piQ M X w = y := by
  simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem NQ_normal (h : Lemma97Chief p M D X W) : (NQ M X W).Normal :=
  h.normalW.map _ piQ_surjective

theorem NQ_ne_bot (h : Lemma97Chief p M D X W) : NQ M X W ≠ ⊥ := by
  intro hbot
  obtain ⟨w, hwW, hwX⟩ := Set.exists_of_ssubset h.lt
  have hwM : w ∈ M := chief_W_le_M h hwW
  have : piQ M X ⟨w, hwM⟩ ∈ NQ M X W := mem_NQ.2 ⟨⟨w, hwM⟩, hwW, rfl⟩
  rw [hbot, Subgroup.mem_bot, piQ_eq_one_iff] at this
  exact hwX this

theorem NQ_nonab (h : Lemma97Chief p M D X W) (hnab : ¬ ⁅W, W⁆ ≤ X) :
    ∃ a ∈ NQ M X W, ∃ b ∈ NQ M X W, a * b ≠ b * a := by
  rw [Subgroup.commutator_le] at hnab
  push Not at hnab
  obtain ⟨w₁, hw₁, w₂, hw₂, hc⟩ := hnab
  have hw₁M : w₁ ∈ M := chief_W_le_M h hw₁
  have hw₂M : w₂ ∈ M := chief_W_le_M h hw₂
  refine ⟨piQ M X ⟨w₁, hw₁M⟩, mem_NQ.2 ⟨_, hw₁, rfl⟩, piQ M X ⟨w₂, hw₂M⟩,
    mem_NQ.2 ⟨_, hw₂, rfl⟩, fun heq => hc ?_⟩
  have h1 : piQ M X ⁅(⟨w₁, hw₁M⟩ : ↥M), ⟨w₂, hw₂M⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact heq
  exact (piQ_eq_one_iff.1 h1)

theorem NQ_minimal (h : Lemma97Chief p M D X W) :
    ∀ V : Subgroup (QM M X), V.Normal → V ≤ NQ M X W → V = ⊥ ∨ V = NQ M X W := by
  intro V hVn hVN
  have hXM := chief_X_le_M h
  have hWM := chief_W_le_M h
  let V' : Subgroup G := (V.comap (piQ M X)).map M.subtype
  have hV'M : V' ≤ M := Subgroup.map_subtype_le _
  have hmem : ∀ v : G, v ∈ V' ↔ ∃ hv : v ∈ M, piQ M X ⟨v, hv⟩ ∈ V := by
    intro v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hv, hV⟩
      exact ⟨⟨v, hv⟩, hV, rfl⟩
  have hV'n : (V'.subgroupOf M).Normal := by
    have : V'.subgroupOf M = V.comap (piQ M X) := by
      ext x
      rw [Subgroup.mem_subgroupOf, hmem]
      exact ⟨fun ⟨_, hV⟩ => hV, fun hV => ⟨x.2, hV⟩⟩
    rw [this]
    exact hVn.comap _
  have hXV' : X ≤ V' := by
    intro x hx
    refine (hmem x).2 ⟨hXM hx, ?_⟩
    rw [(piQ_eq_one_iff (x := ⟨x, hXM hx⟩)).2 hx]
    exact V.one_mem
  have hV'W : V' ≤ W := by
    intro v hv
    obtain ⟨hvM, hV⟩ := (hmem v).1 hv
    obtain ⟨w, hwW, hw⟩ := mem_NQ.1 (hVN hV)
    have h1 : piQ M X (w⁻¹ * ⟨v, hvM⟩) = 1 := by rw [map_mul, map_inv, hw, inv_mul_cancel]
    have h2 : ((w⁻¹ * ⟨v, hvM⟩ : ↥M) : G) ∈ X := piQ_eq_one_iff.1 h1
    have h3 : ((w⁻¹ * ⟨v, hvM⟩ : ↥M) : G) = (w : G)⁻¹ * v := rfl
    have h4 : v = (w : G) * ((w : G)⁻¹ * v) := by group
    rw [h4]
    exact W.mul_mem hwW (chief_X_le_W h (h3 ▸ h2))
  rcases h.chief V' hV'M hV'n hXV' hV'W with h1 | h1
  · left
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨m, rfl⟩ := piQ_surjective (X := X) y
    have hm : (m : G) ∈ V' := (hmem m).2 ⟨m.2, by simpa using hy⟩
    rw [h1] at hm
    rw [Subgroup.mem_bot]
    exact piQ_eq_one_iff.2 hm
  · right
    refine le_antisymm hVN fun y hy => ?_
    obtain ⟨w, hwW, rfl⟩ := mem_NQ.1 hy
    have : (w : G) ∈ V' := by rw [h1]; exact hwW
    exact ((hmem w).1 this).2 |> fun h => by simpa using h


theorem isPGroup_zpowers_of_pow_eq_one {d : G} (hp : p.Prime) (hd : d ^ p = 1) :
    IsPGroup p (Subgroup.zpowers d) := by
  have h1 : orderOf d ∣ p ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one hd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 h1
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem piQ_pow_eq_one {d : G} (hdM : d ∈ M) {n : ℕ} (hd : d ^ n = 1) :
    piQ M X ⟨d, hdM⟩ ^ n = 1 := by
  rw [← map_pow (piQ M X)]
  have : (⟨d, hdM⟩ : ↥M) ^ n = 1 := Subtype.ext (by simpa using hd)
  rw [this, map_one]

theorem HQ_isPGroup (d : G) : IsPGroup 2 (HQ M X d) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPGroup 2 (pCoreOf 2 (Subgroup.centralizer ({d} : Set G))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  exact (h1.comap_of_injective M.subtype M.subtype_injective).map (piQ M X)

theorem HQ_comm {d : G} (hdM : d ∈ M) :
    ∀ h ∈ HQ M X d, piQ M X ⟨d, hdM⟩ * h = h * piQ M X ⟨d, hdM⟩ := by
  intro h hh
  obtain ⟨w, hw, rfl⟩ := mem_HQ.1 hh
  have hwC : (w : G) ∈ Subgroup.centralizer ({d} : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ hw
  have hc : (w : G) * d = d * (w : G) := Subgroup.mem_centralizer_singleton_iff.1 hwC
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hc.symm

theorem HQ_normalized (hp : p.Prime) (h : Lemma97Chief p M D X W) {d : G} (hdM : d ∈ M)
    (hd : d ^ p = 1) :
    ∀ y : QM M X, piQ M X ⟨d, hdM⟩ * y = y * piQ M X ⟨d, hdM⟩ →
      ∀ x ∈ HQ M X d, y * x * y⁻¹ ∈ HQ M X d := by
  intro y hy x hx
  obtain ⟨m, rfl⟩ := piQ_surjective (X := X) y
  obtain ⟨w, hw, rfl⟩ := mem_HQ.1 hx
  have hdm : d * (m : G) * d⁻¹ * (m : G)⁻¹ ∈ X := by
    have h1 : piQ M X (⟨d, hdM⟩ * m * ⟨d, hdM⟩⁻¹ * m⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy]
      group
    exact piQ_eq_one_iff.1 h1
  haveI : Fact p.Prime := ⟨hp⟩
  have hdN : d ∈ Subgroup.normalizer (X : Set G) := chief_M_le_normalizer_X h hdM
  have hmN : (m : G) ∈ Subgroup.normalizer (X : Set G) := chief_M_le_normalizer_X h m.2
  obtain ⟨v, hvX, hvc⟩ := exists_mul_mem_centralizer (isPGroup_zpowers_of_pow_eq_one hp hd)
    (chief_not_dvd_card_X hp h) hdN hmN hdm
  have hvM : v ∈ M := chief_X_le_M h hvX
  have hπ : piQ M X (m * ⟨v, hvM⟩) = piQ M X m := by
    rw [map_mul, piQ_eq_one_iff.2 (show ((⟨v, hvM⟩ : ↥M) : G) ∈ X from hvX), mul_one]
  rw [← hπ]
  refine mem_HQ.2 ⟨(m * ⟨v, hvM⟩) * w * (m * ⟨v, hvM⟩)⁻¹, ?_, by simp [map_mul, map_inv]⟩
  have hnorm : (m : G) * v ∈ Subgroup.normalizer
      (pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (Subgroup.le_normalizer hvc)
  have := (Subgroup.mem_normalizer_iff.1 hnorm w).1 hw
  simpa using this

theorem GQ_le_iSup (hD : Prop95Hyp p M D) :
    GQ M X D ≤ ⨆ (d : G) (_ : d ∈ D) (_ : d ≠ 1), HQ M X d := by
  intro y hy
  obtain ⟨w, hw, rfl⟩ := mem_GQ.1 hy
  let Hall : Subgroup G := ((⨆ (d : G) (_ : d ∈ D) (_ : d ≠ 1), HQ M X d).comap (piQ M X)).map
    M.subtype
  have hle : sigmaStar D ≤ Hall := by
    refine iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => ?_
    intro x hx
    have hxM : x ∈ M := hD.clause_a d hd hd1 hx
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    exact Subgroup.mem_iSup_of_mem d (Subgroup.mem_iSup_of_mem hd
      (Subgroup.mem_iSup_of_mem hd1 (mem_HQ.2 ⟨⟨x, hxM⟩, hx, rfl⟩)))
  obtain ⟨w', hw', hww'⟩ := hle (gammaD_le_sigmaStar D hw)
  have : w' = w := Subtype.ext hww'
  rw [this] at hw'
  exact hw'

theorem GQ_not_centralizes (h : Lemma97Chief p M D X W) (hc : ¬ ⁅gammaD D, W⁆ ≤ X)
    (hΓM : gammaD D ≤ M) : ¬ ∀ g ∈ GQ M X D, ∀ n ∈ NQ M X W, g * n = n * g := by
  intro hcen
  apply hc
  rw [Subgroup.commutator_le]
  intro γ hγ w hw
  have hγM := hΓM hγ
  have hwM := chief_W_le_M h hw
  have := hcen (piQ M X ⟨γ, hγM⟩) (mem_GQ.2 ⟨_, hγ, rfl⟩) (piQ M X ⟨w, hwM⟩)
    (mem_NQ.2 ⟨_, hw, rfl⟩)
  have h1 : piQ M X ⁅(⟨γ, hγM⟩ : ↥M), ⟨w, hwM⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact this
  exact piQ_eq_one_iff.1 h1

theorem not_dvd_card_NQ (hp : p.Prime) (h : Lemma97Chief p M D X W) :
    ¬ p ∣ Nat.card (NQ M X W) := fun hd => by
  apply chief_not_dvd_card_W hp h
  refine hd.trans ?_
  have h1 : Nat.card (NQ M X W) ∣ Nat.card (W.subgroupOf M) :=
    Subgroup.card_dvd_of_surjective (MonoidHom.subgroupMap_surjective (piQ M X) (W.subgroupOf M))
  have h2 : Nat.card (W.subgroupOf M) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (chief_W_le_M h)).toEquiv
  rw [← h2]
  exact h1

theorem isCatalogGroup_of_simple {m : ℕ} (hS : GLStanding G m p) (hD : Prop95Hyp p M D)
    (Sg : Subgroup (QM M X)) [IsSimpleGroup Sg] (hnab : ∃ a b : Sg, a * b ≠ b * a) :
    IsCatalogGroup ↥Sg := by
  have hC : CFSG.KCore.IsoInvariant @IsCatalogGroup := fun e ⟨i, ⟨φ⟩⟩ => ⟨i, ⟨e.trans φ⟩⟩
  have hM := twoLocal_ne_top hS hD.twoLocal
  have hKM := CFSG.KCore.KProperNonab.kGroupNonab hC hS.kProper M hM
  have hKQ := CFSG.KCore.KGroupNonab.quotient hC hKM (X.subgroupOf M)
  have hKS := CFSG.KCore.KGroupNonab.subgroup hC hKQ Sg
  exact CFSG.KCore.KGroupNonab.catalogue_self hC hKS hnab


end Quot

open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion ffChevConclusion_of_mulEquiv)

theorem mem_pCoreOf_iff' {G : Type} [Group G] [Finite G] {M : Subgroup G} {x : ↥M} :
    (x : G) ∈ pCoreOf 2 M ↔ x ∈ CFSG.pCore 2 ↥M := by
  unfold pCoreOf
  exact Subgroup.mem_map_iff_mem M.subtype_injective

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb Subgroup
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion ffChevConclusion_of_mulEquiv)
open scoped commutatorElement

theorem lemma97NonAb_of (h96 : Lemma96) (hodd : FixedOddFact) (htwo : FixedTwoFacts) :
    Lemma97NonAb := by
  intro G _ _ m p hS M D hD X W h hnab
  classical
  have hp : p.Prime := prime_of_standing hS
  have hp2 : p ≠ 2 := ne_two_of_standing hS
  haveI : (X.subgroupOf M).Normal := h.normalX
  have hΓM : gammaD D ≤ M := gammaD_le hD
  have hclaim : ¬ ⁅gammaD D, W⁆ ≤ X := (L97.claim1 hD h).1
  have hNn := NQ_normal h
  obtain ⟨r, S, hF⟩ := exists_factorization hNn (NQ_ne_bot h) (NQ_minimal h) (NQ_nonab h hnab)
  have hex : ∃ i, ¬ ∀ g ∈ GQ M X D, ∀ s ∈ S i, g * s = s * g := by
    by_contra hno
    push Not at hno
    refine GQ_not_centralizes h hclaim hΓM fun g hg n hn => ?_
    have hle : NQ M X W ≤ Subgroup.centralizer ({g} : Set (QM M X)) := by
      rw [← hF.iSup_eq]
      refine iSup_le fun i s hs => Subgroup.mem_centralizer_singleton_iff.2 ?_
      exact (hno i g hg s hs).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hn)).symm
  obtain ⟨i, hi⟩ := hex
  haveI := hF.simple i
  have hcat : IsCatalogGroup ↥(S i) := isCatalogGroup_of_simple hS hD (S i) (hF.nonab i)
  have hpS : ¬ p ∣ Nat.card ↥(S i) := fun hd =>
    not_dvd_card_NQ hp h (hd.trans (Subgroup.card_dvd_of_le (hF.le i)))
  have hdM : ∀ d ∈ D, d ∈ M := fun d hd => hD.le hd
  have hdp : ∀ d ∈ D, d ^ p = 1 := fun d hd => hD.plane.1.2 d hd
  have hnormAll : ∀ d ∈ D, d ≠ 1 → ∀ x ∈ HQ M X d, x ∈ Subgroup.normalizer (S i : Set (QM M X)) := by
    intro d hd hd1
    exact normalizes hF hodd hp hp2 i hcat hpS (d := piQ M X ⟨d, hdM d hd⟩)
      (piQ_pow_eq_one (hdM d hd) (hdp d hd)) (HQ_isPGroup d)
      (HQ_comm (hdM d hd)) (HQ_normalized hp h (hdM d hd) (hdp d hd))
  have hΓn : GQ M X D ≤ Subgroup.normalizer (S i : Set (QM M X)) :=
    (GQ_le_iSup hD).trans (iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 x hx =>
      hnormAll d hd hd1 x hx)
  have hle2 : CFSG.pCore 2 ↥M ≤ (X.subgroupOf M).comap (MonoidHom.id ↥M) := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact h.two_le (mem_pCoreOf_iff'.2 hx)
  let piT : Mt M →* QM M X := QuotientGroup.map (CFSG.pCore 2 ↥M) (X.subgroupOf M)
    (MonoidHom.id ↥M) hle2
  have hpiT : ∀ x : ↥M, piT (QuotientGroup.mk' (CFSG.pCore 2 ↥M) x) = piQ M X x := fun x => by
    simp [piT]
  have hpiTsurj : Function.Surjective piT := by
    intro y
    obtain ⟨m, rfl⟩ := piQ_surjective (X := X) y
    exact ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hpiT m⟩
  have hmap : (tl M (gammaD D)).map piT = GQ M X D := by
    ext y
    constructor
    · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hpiT x).symm ▸ rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) x, ⟨x, hx, rfl⟩, hpiT x⟩
  have hΓker : ⁅tl M (gammaD D), piT.ker⁆ = ⊥ := by
    refine eq_bot_iff.2 (Subgroup.commutator_le.2 fun a ha b hb => ?_)
    obtain ⟨γ', hγ', rfl⟩ := ha
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) b
    have hmX : (m : G) ∈ X := by
      have : piQ M X m = 1 := by rw [← hpiT]; exact hb
      exact piQ_eq_one_iff.1 this
    rw [Subgroup.mem_bot, ← map_commutatorElement]
    refine (QuotientGroup.eq_one_iff _).2 (mem_pCoreOf_iff'.1 ?_)
    exact h.commX (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 hγ') hmX)
  have hΓn' : (tl M (gammaD D)).map piT ≤ Subgroup.normalizer (S i : Set (QM M X)) := by
    rw [hmap]; exact hΓn
  have hΓS' : ⁅(tl M (gammaD D)).map piT, S i⁆ ≠ ⊥ := by
    intro hbot
    apply hi
    intro g hg s hs
    rw [← hmap] at hg
    have : ⁅g, s⁆ ∈ ⁅(tl M (gammaD D)).map piT, S i⁆ := Subgroup.commutator_mem_commutator hg hs
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  obtain ⟨K, hK, hKΓ, ⟨e⟩⟩ := exists_component_lift piT hpiTsurj (tl M (gammaD D)) hΓker (NQ M X W)
    (S i) (hF.nonab i) (hF.le i) (hF.normal i) hΓn' hΓS'
  have hFF : FFChevConclusion ↥(S i) :=
    ffChevConclusion_of_mulEquiv e (h96 G m p hS M D hD K hK hKΓ).2
  have hcentAll : ∀ d ∈ D, d ≠ 1 → ∀ x ∈ HQ M X d, ∀ s ∈ S i, x * s = s * x := by
    intro d hd hd1
    exact centralizes hF htwo hp hp2 i hcat hpS hFF (d := piQ M X ⟨d, hdM d hd⟩)
      (piQ_pow_eq_one (hdM d hd) (hdp d hd)) (HQ_isPGroup d) (HQ_comm (hdM d hd))
      (HQ_normalized hp h (hdM d hd) (hdp d hd)) (hnormAll d hd hd1)
  have hΓc : ∀ g ∈ GQ M X D, ∀ s ∈ S i, g * s = s * g := by
    intro g hg s hs
    have hle : (⨆ (d : G) (_ : d ∈ D) (_ : d ≠ 1), HQ M X d) ≤
        Subgroup.centralizer ({s} : Set (QM M X)) := by
      refine iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcentAll d hd hd1 x hx s hs)
    have := hle (GQ_le_iSup hD hg)
    exact (Subgroup.mem_centralizer_singleton_iff.1 this)
  exact hi hΓc

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
