module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviGeneric
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.GroupTheory.PCore.RelPPrimeCoreMap

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (relPPrimeCore_le relPPrimeCore_normal coprime_card_relPPrimeCore)

theorem normalizer_le_normalizer_relPPrimeCore {X : Type*} [Group X] (p : ℕ) (P : Subgroup X)
    {b : X} (hb : b ∈ normalizer (P : Set X)) : b ∈ normalizer (relPPrimeCore p P : Set X) := by
  have hmap : P.map (MulAut.conj b).toMonoidHom = P := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hb x).mp hx
    · intro hy
      refine ⟨b⁻¹ * y * b, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have hb' : b⁻¹ ∈ normalizer (P : Set X) := (Subgroup.normalizer (P : Set X)).inv_mem hb
      have := (Subgroup.mem_normalizer_iff.mp hb' y).mp hy
      simpa using this
  have h := relPPrimeCore_map_mulEquiv (MulAut.conj b) P p
  rw [hmap] at h
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : (MulAut.conj b).toMonoidHom x ∈ (relPPrimeCore p P).map (MulAut.conj b).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [← h] at this
    simpa [MulAut.conj_apply] using this
  · intro hx
    have h2 : b * x * b⁻¹ ∈ (relPPrimeCore p P).map (MulAut.conj b).toMonoidHom := by
      rw [← h]
      simpa [MulAut.conj_apply] using hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h2
    have hyx' : b * y * b⁻¹ = b * x * b⁻¹ := hyx
    have : y = x := by simpa using hyx'
    rw [← this]
    exact hy

@[expose] def LeviSurj (p : ℕ) {X : Type} [Group X] (P : Subgroup X) (z : X) (L : Type)
    [Group L] : Prop :=
  z ∈ leviY P ∧
    ∃ φ : ↥(leviY P) →* L, Function.Surjective φ ∧ ¬ p ∣ Nat.card φ.ker ∧ IsSimpleGroup L ∧
      (∃ a b : L, a * b ≠ b * a) ∧ p ∣ Nat.card L

theorem LeviSurj.conclusion {A : Type} [Group A] [Finite A] {K₀ B : Subgroup A} {z : A} {p : ℕ}
    (hp : p.Prime) (hB : B ≤ normalizer (K₀ : Set A)) {d : TauCeti.ValidLieTypeIndex}
    (hc : d.1.characteristic = 2) (hs : d.1 ≠ .suzuki 2)
    (hE : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex d.1)
    (h : LeviSurj p K₀ z (TauCeti.CFSGIndex.lie d).Group) :
    ∃ H N : Subgroup A, H ≤ K₀ ∧ S622IsSimpleSection H N ∧
      B ≤ normalizer (H : Set A) ∧ B ≤ normalizer (N : Set A) ∧ z ∈ H ∧ ¬ p ∣ Nat.card N ∧
      p ∣ N.relIndex H ∧
      ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧ d.1 ≠ .suzuki 2 ∧
        CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex d.1 ∧
        ∃ φ : ↥H →* (TauCeti.CFSGIndex.lie d).Group, Function.Surjective φ ∧
          φ.ker = N.subgroupOf H := by
  set H := leviY K₀ with hH
  obtain ⟨hz, φ, hφs, hker, hsimple, hnab, hpL⟩ := h
  set N := relPPrimeCore p H with hN
  have hNH : N ≤ H := relPPrimeCore_le H
  haveI hNn : (N.subgroupOf H).Normal := relPPrimeCore_normal hp H
  have hcop : Nat.Coprime p (Nat.card N) := coprime_card_relPPrimeCore hp H
  have hpN : ¬ p ∣ Nat.card N := fun hd => (Nat.Prime.coprime_iff_not_dvd hp).mp hcop hd
  have hle1 : φ.ker ≤ N.subgroupOf H := by
    set K := φ.ker.map H.subtype with hK
    have hKsub : K.subgroupOf H = φ.ker :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have hKN : K ≤ N := by
      refine le_sSup ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
      · rw [hKsub]
        infer_instance
      · rw [Subgroup.card_map_of_injective H.subtype_injective]
        exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hker
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hKN (Subgroup.mem_map_of_mem _ hx)
  have hle2 : N.subgroupOf H ≤ φ.ker := by
    haveI hmn : ((N.subgroupOf H).map φ).Normal := hNn.map φ hφs
    rcases hsimple.eq_bot_or_eq_top_of_normal ((N.subgroupOf H).map φ) with h0 | h0
    · exact (Subgroup.map_eq_bot_iff _).mp h0
    · exfalso
      apply hpN
      have h1 : Nat.card (TauCeti.CFSGIndex.lie d).Group ∣ Nat.card (N.subgroupOf H) := by
        have h2 := Subgroup.card_map_dvd (H := N.subgroupOf H) φ
        rwa [h0, Subgroup.card_top] at h2
      have h3 : Nat.card (N.subgroupOf H) = Nat.card N :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
      rw [← h3]
      exact hpL.trans h1
  have hNker : N.subgroupOf H = φ.ker := le_antisymm hle2 hle1
  let e : ↥H ⧸ N.subgroupOf H ≃* (TauCeti.CFSGIndex.lie d).Group :=
    (QuotientGroup.quotientMulEquivOfEq hNker).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hsec : S622IsSimpleSection H N :=
    isSimpleSection_of_quotient_equiv hNH e hsimple hnab
  refine ⟨H, N, leviY_le K₀, hsec,
    fun b hb => (normalizes_of_normalizes (hB hb)).1,
    fun b hb => normalizer_le_normalizer_relPPrimeCore p H (normalizes_of_normalizes (hB hb)).1,
    hz, hpN, ?_, d, hc, hs, hE, φ, hφs, hNker.symm⟩
  rw [Subgroup.relIndex, hNker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs,
    Subgroup.card_top]
  exact hpL

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
