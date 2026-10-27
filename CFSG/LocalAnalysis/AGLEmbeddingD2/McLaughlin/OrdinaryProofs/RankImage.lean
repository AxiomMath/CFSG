module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PerfectCore
public import CFSG.RankThree.PartOne.S11d.OutCentral

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open CFSG.Open

theorem pRank_le_one_of_open {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {N : Subgroup G} (hN : Open.pRank p N ≤ 1) : CFSG.pRank p N ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  unfold CFSG.pRank
  refine csSup_le' ?_
  rintro r ⟨A, hel, hcard⟩
  have hAel : CFSG.IsElementaryAbelian p (A.map N.subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  have hB : Open.IsElemAbelian p (A.map N.subtype) :=
    ⟨hAel.toIsMulCommutative, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩
  have hle : r ≤ Open.pRank p N := by
    refine le_csSup ?_ ⟨A.map N.subtype, Subgroup.map_subtype_le A, hB, ?_⟩
    · refine ⟨Nat.card G, ?_⟩
      rintro k ⟨E, -, -, hk⟩
      have h1 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
      have h2 : k < p ^ k := Nat.lt_pow_self hp.one_lt
      omega
    · rw [Subgroup.card_map_of_injective N.subtype_injective, hcard]
  omega

theorem pRank_map_le_one {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G'] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (f : G →* G') {N : Subgroup G} (hN : Open.pRank p N ≤ 1) :
    Open.pRank p (N.map f) ≤ 1 := by
  have hNr : CFSG.pRank p N ≤ 1 := pRank_le_one_of_open hp hN
  unfold Open.pRank
  refine csSup_le' ?_
  rintro r ⟨E, hEM, hEel, hcard⟩
  have hEp : Nat.card E ≤ p := by
    have : Fact p.Prime := ⟨hp⟩
    let M : Subgroup G' := N.map f
    let φ : N →* M :=
      (f.comp N.subtype).codRestrict M (fun x => Subgroup.mem_map_of_mem f x.2)
    have hφ : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
    let E₁ : Subgroup M := E.subgroupOf M
    have hE₁ : IsPGroup p E₁ := by
      intro g
      refine ⟨1, ?_⟩
      rw [Nat.pow_one]
      have hg : ((g : M) : G') ∈ E := Subgroup.mem_subgroupOf.mp g.2
      apply Subtype.ext
      apply Subtype.ext
      simpa using hEel.2 _ hg
    obtain ⟨Q', hQ'⟩ := IsPGroup.exists_le_sylow hE₁
    obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective (p := p) hφ Q'
    have hQ1 : Q'.1 = Q.1.map φ := by rw [← hQ]; rfl
    have hSN : Q.1.map N.subtype ≤ N := Subgroup.map_subtype_le Q.1
    have hSp : IsPGroup p (Q.1.map N.subtype) := Q.2.map N.subtype
    have hScyc : IsCyclic (Q.1.map N.subtype) :=
      CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one hp hp2 hSN hSp hNr
    have hES : E ≤ (Q.1.map N.subtype).map f := by
      intro x hx
      have hxM : x ∈ M := hEM hx
      have hy : (⟨x, hxM⟩ : M) ∈ Q'.1 := hQ' (Subgroup.mem_subgroupOf.mpr hx)
      rw [hQ1] at hy
      obtain ⟨z, hz, hzφ⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map.mpr
        ⟨(z : G), Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, congrArg Subtype.val hzφ⟩
    have hSf : IsCyclic ((Q.1.map N.subtype).map f) := by
      let ψ : (Q.1.map N.subtype) →* ((Q.1.map N.subtype).map f) :=
        (f.comp (Q.1.map N.subtype).subtype).codRestrict ((Q.1.map N.subtype).map f)
          (fun x => Subgroup.mem_map_of_mem f x.2)
      have hψ : Function.Surjective ψ := by
        rintro ⟨y, hy⟩
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
        exact ⟨⟨x, hx⟩, rfl⟩
      exact isCyclic_of_surjective ψ hψ
    have hcardE : Nat.card (E.subgroupOf ((Q.1.map N.subtype).map f)) = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv
    have hexp : Monoid.exponent (E.subgroupOf ((Q.1.map N.subtype).map f)) ∣ p := by
      refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
      rintro ⟨⟨g, hgK⟩, hg⟩
      apply Subtype.ext
      simpa using hEel.2 g (Subgroup.mem_subgroupOf.mp hg)
    have hexpeq : Monoid.exponent (E.subgroupOf ((Q.1.map N.subtype).map f))
        = Nat.card (E.subgroupOf ((Q.1.map N.subtype).map f)) :=
      IsCyclic.exponent_eq_card
    have hle : Nat.card (E.subgroupOf ((Q.1.map N.subtype).map f)) ≤ p := by
      rw [← hexpeq]
      exact Nat.le_of_dvd hp.pos hexp
    omega
  rcases Nat.lt_or_ge r 2 with h | h
  · omega
  · exfalso
    have h3 : p ^ r ≤ p := hcard ▸ hEp
    have h1 : p ^ 2 ≤ p ^ r := Nat.pow_le_pow_right hp.pos h
    have h2 : p ^ 2 = p * p := by ring
    nlinarith [hp.two_le]

theorem iterCommutator_of_perfect {X : Type*} [Group X] {L : Subgroup X}
    (hL : ⁅L, L⁆ = L) (n : ℕ) : CFSG.AGLEmbeddingD2.iterCommutator L n = L :=
  le_antisymm (CFSG.AGLEmbeddingD2.iterCommutator_le L n)
    (CFSG.AGLEmbeddingD2.le_iterCommutator_of_commutator_eq hL le_rfl n)

theorem exists_perfect_of_le_map {G G' : Type*} [Group G] [Group G'] [Finite G] {p : ℕ}
    (f : G →* G') {N : Subgroup G} {L' : Subgroup G'} (hL' : L' ≤ N.map f)
    (hperf : ⁅L', L'⁆ = L') (hp : p ∣ Nat.card L') :
    ∃ D : Subgroup G, D ≤ N ∧ ⁅D, D⁆ = D ∧ p ∣ Nat.card D := by
  have hD₀map : (L'.comap f ⊓ N).map f = L' := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact (Subgroup.mem_inf.mp hx).1
    · intro y hy
      obtain ⟨x, hxN, rfl⟩ := Subgroup.mem_map.mp (hL' hy)
      exact Subgroup.mem_map.mpr
        ⟨x, Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr hy, hxN⟩, rfl⟩
  obtain ⟨n, hn⟩ := CFSG.AGLEmbeddingD2.exists_iterCommutator_perfect (L'.comap f ⊓ N)
  refine ⟨CFSG.AGLEmbeddingD2.iterCommutator (L'.comap f ⊓ N) n,
    (CFSG.AGLEmbeddingD2.iterCommutator_le _ n).trans inf_le_right, hn, ?_⟩
  have hmap : (CFSG.AGLEmbeddingD2.iterCommutator (L'.comap f ⊓ N) n).map f = L' := by
    rw [CFSG.AGLEmbeddingD2.iterCommutator_map, hD₀map, iterCommutator_of_perfect hperf n]
  have h1 := Subgroup.card_map_dvd (f := f)
    (H := CFSG.AGLEmbeddingD2.iterCommutator (L'.comap f ⊓ N) n)
  rw [hmap] at h1
  exact hp.trans h1

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
