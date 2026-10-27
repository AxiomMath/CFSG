module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Config
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T)

variable {G : Type} [Group G] [Finite G]

theorem spw_sylow_data {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {u : G}
    (hgen : IsGenericPoint p P M u) {J : Subgroup G}
    (hJC : J ≤ Subgroup.centralizer ({u} : Set G))
    (hCJ : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G))
    {Q : Type} [Group Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) :
    ∃ Tsyl' : Sylow p Q, (Tsyl' : Subgroup Q) = ((u3T P u J).subgroupOf J).map ψ ∧
      (∀ t ∈ (u3T P u J).subgroupOf J, ψ t = 1 → t = 1) ∧
      Nat.card (Tsyl' : Subgroup Q) = Nat.card (u3T P u J) := by
  have hp : p.Prime := Fact.out
  have hOJ : rankThreePrimeCore p J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hOcop : p.Coprime (Nat.card (rankThreePrimeCore p J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hkcop : ¬ p ∣ Nat.card ψ.ker := by
    rw [hker]
    have : Nat.card ((rankThreePrimeCore p J).subgroupOf J) = Nat.card (rankThreePrimeCore p J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
    rw [this]
    exact (hp.coprime_iff_not_dvd).mp hOcop
  have hSylJ : IsSylowOf p (u3T P u J) J := hgen.2.2.1.inf_of_le_normalizer hJC hCJ
  obtain ⟨Tsyl, hTsyl⟩ := hSylJ.exists_sylow_eq_subgroupOf
  have hTinj : ∀ t ∈ (u3T P u J).subgroupOf J, ψ t = 1 → t = 1 := by
    rw [← hTsyl]
    exact u3main_eq_one_of_ker ψ hkcop Tsyl.isPGroup'
  have hTsyl' : ((Tsyl.mapSurjective hψ : Sylow p Q) : Subgroup Q) =
      ((u3T P u J).subgroupOf J).map ψ := by
    rw [← hTsyl]
    exact Sylow.coe_mapSurjective hψ Tsyl
  refine ⟨Tsyl.mapSurjective hψ, hTsyl', hTinj, ?_⟩
  have hTJ : u3T P u J ≤ J := inf_le_right
  have hinjT0 : Function.Injective (ψ.comp ((u3T P u J).subgroupOf J).subtype) :=
    (injective_iff_map_eq_one _).mpr fun a ha => Subtype.ext (hTinj a a.2 ha)
  have hmapcard : Nat.card (((u3T P u J).subgroupOf J).map ψ) =
      Nat.card ((u3T P u J).subgroupOf J) := by
    have e1 : (ψ.comp ((u3T P u J).subgroupOf J).subtype).range =
        ((u3T P u J).subgroupOf J).map ψ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective hinjT0).toEquiv]
  rw [hTsyl', hmapcard]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv

private theorem spw_transfer {p : ℕ} {T J : Subgroup G} (hTJ : T ≤ J) {Q : Type} [Group Q]
    (ψ : ↥J →* Q) (Ts : Subgroup Q) (hTs : Ts = (T.subgroupOf J).map ψ)
    (hTinj : ∀ t ∈ T.subgroupOf J, ψ t = 1 → t = 1) :
    ((∀ s ∈ Ts, s ^ p = 1) → ∀ t ∈ T, t ^ p = 1) ∧ (IsMulCommutative Ts → IsMulCommutative T) := by
  set T0 : Subgroup J := T.subgroupOf J with hT0
  have hmem : ∀ t : G, ∀ ht : t ∈ T, (⟨t, hTJ ht⟩ : J) ∈ T0 := fun t ht => ht
  have himg : ∀ t : G, ∀ ht : t ∈ T, ψ ⟨t, hTJ ht⟩ ∈ Ts := by
    intro t ht
    rw [hTs]
    exact ⟨⟨t, hTJ ht⟩, hmem t ht, rfl⟩
  refine ⟨?_, ?_⟩
  · intro h t ht
    have h1 : (ψ ⟨t, hTJ ht⟩) ^ p = 1 := h _ (himg t ht)
    have h2 : (⟨t, hTJ ht⟩ : J) ^ p = 1 := by
      apply hTinj _ (T0.pow_mem (hmem t ht) p)
      rw [map_pow]
      exact h1
    exact congrArg Subtype.val h2
  · intro hc
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 := hc.is_comm.comm ⟨ψ ⟨a, hTJ a.2⟩, himg a a.2⟩ ⟨ψ ⟨b, hTJ b.2⟩, himg b b.2⟩
    have h2 : ψ (⟨a, hTJ a.2⟩ * ⟨b, hTJ b.2⟩) = ψ (⟨b, hTJ b.2⟩ * ⟨a, hTJ a.2⟩) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val h1
    have h4 : ψ ((⟨a, hTJ a.2⟩ * ⟨b, hTJ b.2⟩ : J) * (⟨b, hTJ b.2⟩ * ⟨a, hTJ a.2⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    have h5 := hTinj _ (T0.mul_mem (T0.mul_mem (hmem a a.2) (hmem b b.2))
      (T0.inv_mem (T0.mul_mem (hmem b b.2) (hmem a a.2)))) h4
    have h3 : (⟨a, hTJ a.2⟩ * ⟨b, hTJ b.2⟩ : J) = ⟨b, hTJ b.2⟩ * ⟨a, hTJ a.2⟩ :=
      mul_inv_eq_one.mp h5
    have h6 : (a : G) * b = b * a := congrArg (fun z : J => (z : G)) h3
    exact Subtype.ext h6

theorem spw_T_structure_plane {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {u : G}
    (hgen : IsGenericPoint p P M u) {J : Subgroup G}
    (hJC : J ≤ Subgroup.centralizer ({u} : Set G))
    (hCJ : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G))
    {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) (hpl : SylowIsPlane p Q) :
    Nat.card (u3T P u J) = p ^ 2 ∧ IsElemAbelian p (u3T P u J) := by
  obtain ⟨Tsyl', hTsyl', hTinj, hcardS⟩ := spw_sylow_data hgen hJC hCJ ψ hψ hker
  obtain ⟨hexp, hcomm⟩ := spw_transfer (p := p) (inf_le_right : u3T P u J ≤ J) ψ (Tsyl' : Subgroup Q)
    hTsyl' hTinj
  obtain ⟨hel, hc2⟩ := hpl Tsyl'
  exact ⟨hcardS ▸ hc2, ⟨hcomm hel.1, hexp hel.2⟩⟩

theorem spw_T_structure_heis {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {u : G}
    (hgen : IsGenericPoint p P M u) {J : Subgroup G}
    (hJC : J ≤ Subgroup.centralizer ({u} : Set G))
    (hCJ : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G))
    {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) (hh : SylowIsHeisenberg p Q) :
    Nat.card (u3T P u J) = p ^ 3 ∧ (∀ t ∈ u3T P u J, t ^ p = 1) ∧
      ¬ IsMulCommutative (u3T P u J) := by
  obtain ⟨Tsyl', hTsyl', hTinj, hcardS⟩ := spw_sylow_data hgen hJC hCJ ψ hψ hker
  obtain ⟨hexp, hcomm⟩ := spw_transfer (p := p) (inf_le_right : u3T P u J ≤ J) ψ (Tsyl' : Subgroup Q)
    hTsyl' hTinj
  obtain ⟨hc3, hnab', hexp'⟩ := hh Tsyl'
  refine ⟨hcardS ▸ hc3, hexp hexp', fun hTc => ?_⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hnab'
  have hnab : ¬ IsMulCommutative (Tsyl' : Subgroup Q) := by
    intro hc
    exact hab (congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  apply hnab
  rw [hTsyl'] at ha hb ⊢
  refine ⟨⟨fun a' b' => ?_⟩⟩
  obtain ⟨a0, ha0, ha0'⟩ := a'.2
  obtain ⟨b0, hb0, hb0'⟩ := b'.2
  have ha1 : (a0 : G) ∈ u3T P u J := ha0
  have hb1 : (b0 : G) ∈ u3T P u J := hb0
  have h1 := hTc.is_comm.comm ⟨(a0 : G), ha1⟩ ⟨(b0 : G), hb1⟩
  have h2 : a0 * b0 = b0 * a0 := Subtype.ext (congrArg (fun z : u3T P u J => (z : G)) h1)
  apply Subtype.ext
  show (a' : Q) * b' = b' * a'
  rw [← ha0', ← hb0', ← map_mul, ← map_mul, h2]

theorem spw_T_structure {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {u : G}
    (hgen : IsGenericPoint p P M u) {J : Subgroup G}
    (hJC : J ≤ Subgroup.centralizer ({u} : Set G))
    (hCJ : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G))
    {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) (hQ : SecondPointFacts p Q) :
    (Nat.card (u3T P u J) = p ^ 2 ∧ IsElemAbelian p (u3T P u J)) ∨
      (Nat.card (u3T P u J) = p ^ 3 ∧ (∀ t ∈ u3T P u J, t ^ p = 1) ∧
        ¬ IsMulCommutative (u3T P u J)) := by
  rcases hQ.shape with ⟨hpl, -⟩ | ⟨hh, -⟩
  · exact Or.inl (spw_T_structure_plane hgen hJC hCJ ψ hψ hker hpl)
  · exact Or.inr (spw_T_structure_heis hgen hJC hCJ ψ hψ hker hh)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
