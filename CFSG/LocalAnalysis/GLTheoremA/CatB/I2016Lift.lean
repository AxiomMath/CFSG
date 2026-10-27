module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016Core
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


@[expose] noncomputable def Mset (J : Subgroup G) (R' : Subgroup (PQ 3 J)) : Subgroup G :=
  (R'.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J))).map J.subtype

theorem mem_Mset {J : Subgroup G} {R' : Subgroup (PQ 3 J)} {h : G} :
    h ∈ Mset J R' ↔ ∃ hJ : h ∈ J, (QuotientGroup.mk ⟨h, hJ⟩ : PQ 3 J) ∈ R' := by
  constructor
  · intro hh
    obtain ⟨m, hm, hmv⟩ := Subgroup.mem_map.1 hh
    have hmJ : h = m.1 := hmv.symm
    refine ⟨hmv ▸ m.2, ?_⟩
    have : (⟨h, hmv ▸ m.2⟩ : ↥J) = m := Subtype.ext hmv.symm
    rw [this]
    exact hm
  · rintro ⟨hJ, hr⟩
    exact Subgroup.mem_map.2 ⟨⟨h, hJ⟩, hr, rfl⟩

theorem mem_iff_of_map_eq {Q : Type} [Group Q] (R : Subgroup Q) (α : MulAut Q)
    (hα : R.map α.toMonoidHom = R) (q : Q) : α q ∈ R ↔ q ∈ R := by
  constructor
  · intro hq
    have : α q ∈ R.map α.toMonoidHom := by rw [hα]; exact hq
    obtain ⟨r, hr, hrq⟩ := Subgroup.mem_map.1 this
    have : r = q := α.injective hrq
    rw [← this]
    exact hr
  · intro hq
    have : α q ∈ R.map α.toMonoidHom := Subgroup.mem_map_of_mem _ hq
    rwa [hα] at this

theorem map_conj_eq_of_mem_normalizer {Q : Type} [Group Q] {R : Subgroup Q} {x : Q}
    (hx : x ∈ Subgroup.normalizer (R : Set Q)) : R.map (MulAut.conj x).toMonoidHom = R := by
  apply le_antisymm
  · rintro _ ⟨r, hr, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 hx r).1 hr
    simpa [MulAut.conj_apply] using this
  · intro r hr
    refine Subgroup.mem_map.2 ⟨x⁻¹ * r * x, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * r * x)).2
      apply this
      simpa [mul_assoc] using hr
    · simp [MulAut.conj_apply, mul_assoc]

theorem normalizer_Mset {J : Subgroup G} {R' : Subgroup (PQ 3 J)} {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G))
    (hinv : R'.map (sigmaHom 3 J ⟨g, hg⟩).toMonoidHom = R') :
    g ∈ Subgroup.normalizer ((Mset J R' : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  by_cases hhJ : h ∈ J
  · have hghJ : g * h * g⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hg h).1 hhJ
    have hkey : (QuotientGroup.mk ⟨g * h * g⁻¹, hghJ⟩ : PQ 3 J) =
        sigmaHom 3 J ⟨g, hg⟩ (QuotientGroup.mk ⟨h, hhJ⟩) := by
      show _ = sigmaQ 3 J g hg (QuotientGroup.mk ⟨h, hhJ⟩)
      rw [sigmaQ_mk]
      rfl
    rw [mem_Mset, mem_Mset]
    constructor
    · rintro ⟨_, hr⟩
      refine ⟨hghJ, ?_⟩
      rw [hkey]
      exact (mem_iff_of_map_eq R' _ hinv _).2 hr
    · rintro ⟨_, hr⟩
      refine ⟨hhJ, ?_⟩
      apply (mem_iff_of_map_eq R' _ hinv _).1
      rw [← hkey]
      exact hr
  · have hghJ : g * h * g⁻¹ ∉ J := fun hc => hhJ ((Subgroup.mem_normalizer_iff.1 hg h).2 hc)
    constructor
    · intro hh
      exact absurd (mem_Mset.1 hh).1 hhJ
    · intro hh
      exact absurd (mem_Mset.1 hh).1 hghJ

theorem exists_lift_two (J : Subgroup G) {R' : Subgroup (PQ 3 J)} (hR1 : R' ≠ ⊥)
    (hR2 : IsPGroup 2 R') :
    ∃ W : Subgroup G, W ≤ J ∧ IsPGroup 2 W ∧ ¬ W ≤ GLAPPrimeCoreOf 3 J ∧
      W ⊔ GLAPPrimeCoreOf 3 J = Mset J R' := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hNn : (CFSG.pPrimeCore 3 ↥J).Normal := Subgroup.sSup_normal _ fun _ hN => hN.1
  set N : Subgroup ↥J := CFSG.pPrimeCore 3 ↥J with hN
  set mkJ : ↥J →* PQ 3 J := QuotientGroup.mk' N with hmkJ
  set M : Subgroup ↥J := R'.comap mkJ with hM
  haveI : (N.subgroupOf M).Normal := inferInstance
  let φM : ↥M →* ↥R' := MonoidHom.codRestrict (mkJ.comp M.subtype) R' (fun m => m.2)
  have hφM : Function.Surjective φM := by
    intro r
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N r.1
    have hxM : x ∈ M := by
      show mkJ x ∈ R'
      rw [hx]
      exact r.2
    exact ⟨⟨x, hxM⟩, Subtype.ext hx⟩
  have hker : φM.ker = N.subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : mkJ m.1 = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).1 h'
    · intro h
      apply Subtype.ext
      show mkJ m.1 = 1
      exact (QuotientGroup.eq_one_iff _).2 h
  have hcard : Nat.card (↥M ⧸ N.subgroupOf M) = Nat.card R' := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φM hφM).toEquiv
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card R' = 2 ^ k := IsPGroup.iff_card.1 hR2
  obtain ⟨W₀, hW₀2, hW₀⟩ := exists_two_sup_eq_top (N.subgroupOf M) (k := k) (by rw [hcard, hk])
  let ι : ↥M →* G := J.subtype.comp M.subtype
  have hWJ : (W₀.map ι) ≤ J := by
    rintro _ ⟨w, _, rfl⟩
    exact w.1.2
  have hW2 : IsPGroup 2 (W₀.map ι) := hW₀2.map ι
  have hnot : ¬ (W₀.map ι) ≤ GLAPPrimeCoreOf 3 J := by
    intro hle
    have hW₀N : W₀ ≤ N.subgroupOf M := by
      intro w hw
      have hm : ι w ∈ GLAPPrimeCoreOf 3 J := hle (Subgroup.mem_map_of_mem ι hw)
      obtain ⟨n, hn, hnv⟩ := Subgroup.mem_map.1 hm
      have hnw : n = w.1 := Subtype.ext hnv
      rw [Subgroup.mem_subgroupOf]
      rw [← hnw]
      exact hn
    have htop : (N.subgroupOf M) = ⊤ := by
      rw [← hW₀, sup_eq_right.2 hW₀N]
    apply hR1
    rw [eq_bot_iff]
    intro r hr
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N r
    have hxM : x ∈ M := by
      show mkJ x ∈ R'
      rw [hx]
      exact hr
    have hxN : (⟨x, hxM⟩ : ↥M) ∈ N.subgroupOf M := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at hxN
    rw [Subgroup.mem_bot, ← hx]
    exact (QuotientGroup.eq_one_iff _).2 hxN
  have hsup : (W₀.map ι) ⊔ GLAPPrimeCoreOf 3 J = Mset J R' := by
    have hN' : GLAPPrimeCoreOf 3 J = (N.subgroupOf M).map ι := by
      ext g
      constructor
      · intro hg
        obtain ⟨n, hn, hnv⟩ := Subgroup.mem_map.1 hg
        have hnM : n ∈ M := by
          show mkJ n ∈ R'
          have h1 : mkJ n = 1 := (QuotientGroup.eq_one_iff n).2 hn
          rw [h1]
          exact Subgroup.one_mem _
        refine Subgroup.mem_map.2 ⟨⟨n, hnM⟩, ?_, hnv⟩
        rw [Subgroup.mem_subgroupOf]
        exact hn
      · intro hg
        obtain ⟨m, hm, hmv⟩ := Subgroup.mem_map.1 hg
        rw [Subgroup.mem_subgroupOf] at hm
        exact Subgroup.mem_map.2 ⟨m.1, hm, hmv⟩
    have hMs : Mset J R' = (⊤ : Subgroup ↥M).map ι := by
      ext g
      rw [mem_Mset]
      constructor
      · rintro ⟨hJ, hr⟩
        exact Subgroup.mem_map.2 ⟨⟨⟨g, hJ⟩, hr⟩, Subgroup.mem_top _, rfl⟩
      · intro hg
        obtain ⟨m, _, hmv⟩ := Subgroup.mem_map.1 hg
        have hJ : g ∈ J := by
          rw [← hmv]
          exact m.1.2
        refine ⟨hJ, ?_⟩
        have hm' : mkJ m.1 ∈ R' := m.2
        have : (⟨g, hJ⟩ : ↥J) = m.1 := Subtype.ext hmv.symm
        rw [this]
        exact hm'
    rw [hN', hMs, ← Subgroup.map_sup, hW₀]
  exact ⟨W₀.map ι, hWJ, hW2, hnot, hsup⟩

end CFSG.LocalAnalysis.GLTheoremA.I2016
