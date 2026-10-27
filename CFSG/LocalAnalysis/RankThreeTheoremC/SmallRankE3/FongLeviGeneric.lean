module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongGammaDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3SectionTransport
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup
open CFSG.Open (pCoreOf)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)

@[expose] def leviY {X : Type*} [Group X] (P : Subgroup X) : Subgroup X :=
  CFSG.Quasithin.perfectCore P

@[expose] def leviW {X : Type*} [Group X] (P : Subgroup X) : Subgroup X :=
  pCoreOf 2 (leviY P)

theorem pCoreOf_map_injective {G G' : Type*} [Group G] [Group G'] (r : ℕ) (f : G →* G')
    (hf : Function.Injective f) (H : Subgroup G) :
    pCoreOf r (H.map f) = (pCoreOf r H).map f := by
  unfold pCoreOf
  let φ : ↥H ≃* ↥(H.map f) := H.equivMapOfInjective f hf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv r φ, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem leviY_map {X X' : Type*} [Group X] [Group X'] [Finite X] [Finite X'] (f : X →* X')
    (P : Subgroup X) : leviY (P.map f) = (leviY P).map f :=
  (CFSG.Quasithin.map_perfectCore f P).symm

theorem leviW_map {X X' : Type*} [Group X] [Group X'] [Finite X] [Finite X'] (f : X →* X')
    (hf : Function.Injective f) (P : Subgroup X) : leviW (P.map f) = (leviW P).map f := by
  unfold leviW
  rw [leviY_map, pCoreOf_map_injective 2 f hf]

theorem leviW_le_leviY {X : Type*} [Group X] (P : Subgroup X) : leviW P ≤ leviY P :=
  Subgroup.map_subtype_le _

theorem leviY_le {X : Type*} [Group X] (P : Subgroup X) : leviY P ≤ P :=
  CFSG.Quasithin.perfectCore_le P

theorem leviY_eq_map_perfectResidual {X : Type*} [Group X] (P : Subgroup X) :
    leviY P = (CFSG.perfectResidual ↥P).map P.subtype := by
  unfold leviY CFSG.Quasithin.perfectCore CFSG.perfectResidual
  rw [Subgroup.map_iInf P.subtype P.subtype_injective]
  exact iInf_congr fun n => CFSG.Quasithin.derivedSeriesOf_eq_map_derivedSeries P n

@[expose] def LeviSec (p : ℕ) {X : Type} [Group X] (P : Subgroup X) (z : X) : Prop :=
  z ∈ leviY P ∧ S622IsSimpleSection (leviY P) (leviW P) ∧ p ∣ (leviW P).relIndex (leviY P) ∧
  ¬ p ∣ Nat.card (leviW P)

@[expose] def LeviHom {X : Type*} [Group X] (P : Subgroup X) (L : Type*) [Group L] : Prop :=
  ∃ φ : ↥(leviY P) →* L, Function.Surjective φ ∧ φ.ker = (leviW P).subgroupOf (leviY P)

@[expose] def LeviPkg (p : ℕ) (d : TauCeti.ValidLieTypeIndex) {X : Type} [Group X] (P : Subgroup X)
    (z : X) : Prop :=
  LeviSec p P z ∧ LeviHom P (TauCeti.CFSGIndex.lie d).Group

theorem LeviHom.of_mulEquiv {X : Type*} [Group X] {P : Subgroup X} {L L' : Type*} [Group L]
    [Group L'] (h : LeviHom P L) (e : L ≃* L') : LeviHom P L' := by
  obtain ⟨φ, hφs, hφk⟩ := h
  refine ⟨e.toMonoidHom.comp φ, e.surjective.comp hφs, ?_⟩
  rw [MonoidHom.ker_comp_of_injective φ e.toMonoidHom e.injective, hφk]

theorem LeviSec.map {p : ℕ} {X X' : Type} [Group X] [Group X'] [Finite X] [Finite X']
    {P : Subgroup X} {z : X} (f : X →* X') (hf : Function.Injective f) (h : LeviSec p P z) :
    LeviSec p (P.map f) (f z) := by
  obtain ⟨hz, hsec, hrel, hpW⟩ := h
  unfold LeviSec
  rw [leviY_map, leviW_map f hf]
  refine ⟨Subgroup.mem_map_of_mem f hz, isSimpleSection_map_injective f hf hsec, ?_, ?_⟩
  · rw [Subgroup.relIndex_map_map_of_injective (f := f) _ _ hf]
    exact hrel
  · rw [Subgroup.card_map_of_injective hf]
    exact hpW

theorem LeviHom.map {X X' : Type*} [Group X] [Group X'] [Finite X] [Finite X'] {P : Subgroup X}
    {L : Type*} [Group L] (f : X →* X') (hf : Function.Injective f) (h : LeviHom P L) :
    LeviHom (P.map f) L := by
  obtain ⟨φ, hφs, hφk⟩ := h
  unfold LeviHom
  rw [leviY_map, leviW_map f hf]
  let ψ : ↥((leviY P).map f) ≃* ↥(leviY P) := ((leviY P).equivMapOfInjective f hf).symm
  refine ⟨φ.comp ψ.toMonoidHom, hφs.comp ψ.surjective, ?_⟩
  ext ⟨y, hy⟩
  obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
  have hψ : ψ ⟨f y₀, hy⟩ = ⟨y₀, hy₀⟩ := by
    apply ((leviY P).equivMapOfInjective f hf).injective
    simp only [ψ, MulEquiv.apply_symm_apply]
    exact Subtype.ext rfl
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hψ,
    Subgroup.mem_subgroupOf, Subgroup.mem_map_iff_mem hf]
  constructor
  · intro h0
    have : (⟨y₀, hy₀⟩ : ↥(leviY P)) ∈ φ.ker := h0
    rw [hφk, Subgroup.mem_subgroupOf] at this
    exact this
  · intro h0
    have : (⟨y₀, hy₀⟩ : ↥(leviY P)) ∈ φ.ker := by
      rw [hφk, Subgroup.mem_subgroupOf]
      exact h0
    exact this

theorem mem_of_orderOf_prime_of_coprime_relIndex {A : Type*} [Group A] {Y X : Subgroup A}
    (hYX : Y ≤ X) (hn : (Y.subgroupOf X).Normal) {p : ℕ} (hp : p.Prime)
    (hidx : ¬ p ∣ Y.relIndex X) {z : A} (hzX : z ∈ X) (hz : orderOf z = p) : z ∈ Y := by
  haveI := hn
  have hzp : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
  have hzP : (⟨z, hzX⟩ : ↥X) ^ p = 1 := Subtype.ext hzp
  have hmk : (QuotientGroup.mk (⟨z, hzX⟩ : ↥X) : ↥X ⧸ Y.subgroupOf X) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hzP]
    rfl
  have h1 : orderOf (QuotientGroup.mk (⟨z, hzX⟩ : ↥X) : ↥X ⧸ Y.subgroupOf X) ∣ p :=
    orderOf_dvd_of_pow_eq_one hmk
  have hcard : Nat.card (↥X ⧸ Y.subgroupOf X) = Y.relIndex X :=
    (Subgroup.index_eq_card (Y.subgroupOf X)).symm
  have h2 : orderOf (QuotientGroup.mk (⟨z, hzX⟩ : ↥X) : ↥X ⧸ Y.subgroupOf X) ∣ Y.relIndex X :=
    hcard ▸ orderOf_dvd_natCard _
  have hcop : Nat.Coprime p (Y.relIndex X) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hidx
  have hone : orderOf (QuotientGroup.mk (⟨z, hzX⟩ : ↥X) : ↥X ⧸ Y.subgroupOf X) = 1 :=
    Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2)
  have hmk1 : (QuotientGroup.mk (⟨z, hzX⟩ : ↥X) : ↥X ⧸ Y.subgroupOf X) = 1 :=
    orderOf_eq_one_iff.mp hone
  have hmem : (⟨z, hzX⟩ : ↥X) ∈ Y.subgroupOf X := (QuotientGroup.eq_one_iff _).mp hmk1
  exact Subgroup.mem_subgroupOf.mp hmem

theorem normalizes_of_normalizes {X : Type*} [Group X] {P : Subgroup X} {b : X}
    (hb : b ∈ normalizer (P : Set X)) :
    b ∈ normalizer (leviY P : Set X) ∧ b ∈ normalizer (leviW P : Set X) := by
  have h1 : b ∈ normalizer (leviY P : Set X) :=
    CFSG.Quasithin.normalizer_le_normalizer_perfectCore P hb
  exact ⟨h1, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ h1⟩

theorem conclusion_of_pkg {A : Type} [Group A] {K₀ B : Subgroup A} {z : A} {p : ℕ}
    (hB : B ≤ normalizer (K₀ : Set A)) {d : TauCeti.ValidLieTypeIndex}
    (hc : d.1.characteristic = 2) (hs : d.1 ≠ .suzuki 2) (hE : IsE3LeviIndex d.1)
    (h : LeviPkg p d K₀ z) :
    ∃ H N : Subgroup A, H ≤ K₀ ∧ S622IsSimpleSection H N ∧
      B ≤ normalizer (H : Set A) ∧ B ≤ normalizer (N : Set A) ∧ z ∈ H ∧ ¬ p ∣ Nat.card N ∧
      p ∣ N.relIndex H ∧
      ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧ d.1 ≠ .suzuki 2 ∧
        IsE3LeviIndex d.1 ∧
        ∃ φ : ↥H →* (TauCeti.CFSGIndex.lie d).Group, Function.Surjective φ ∧
          φ.ker = N.subgroupOf H := by
  obtain ⟨⟨hz, hsec, hrel, hpW⟩, φ, hφs, hφk⟩ := h
  exact ⟨leviY K₀, leviW K₀, leviY_le K₀, hsec,
    fun b hb => (normalizes_of_normalizes (hB hb)).1,
    fun b hb => (normalizes_of_normalizes (hB hb)).2, hz, hpW, hrel, d, hc, hs, hE, φ, hφs, hφk⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
