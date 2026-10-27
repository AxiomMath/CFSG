module

public import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G'] {p : ℕ}

theorem isPGroup_zpowers_of_pow_eq_one {y : G} (hy : y ^ p = 1) : IsPGroup p (zpowers y) := by
  rintro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]

theorem exists_conj_sylow_between (hp : p.Prime) (ι : G →* G') (hι : Function.Injective ι)
    (hidx : ¬ p ∣ ι.range.index) {R A : Subgroup G'} (hAR : A ≤ R)
    (hRN : R ≤ normalizer (A : Set G')) (hRidx : ¬ p ∣ R.index) (hAp : IsPGroup p A)
    (P : Sylow p G) :
    ∃ g : G', A ≤ ((P : Subgroup G).map ((MulAut.conj g).toMonoidHom.comp ι)) ∧
      ((P : Subgroup G).map ((MulAut.conj g).toMonoidHom.comp ι)) ≤ R := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQp : IsPGroup p ((P : Subgroup G).map ι) := P.isPGroup'.map ι
  have hQi : ¬ p ∣ ((P : Subgroup G).map ι).index := by
    rw [(P : Subgroup G).index_map_of_injective hι]
    exact fun h => (hp.dvd_mul.1 h).elim P.not_dvd_index hidx
  obtain ⟨S⟩ : Nonempty (Sylow p R) := inferInstance
  set S' : Subgroup G' := (S : Subgroup R).map R.subtype with hS'
  have hS'p : IsPGroup p S' := S.isPGroup'.map R.subtype
  have hS'i : ¬ p ∣ S'.index := by
    rw [hS', Subgroup.index_map_subtype]
    exact fun h => (hp.dvd_mul.1 h).elim S.not_dvd_index hRidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G' (hQp.toSylow hQi) (hS'p.toSylow hS'i)
  have hconj : ((P : Subgroup G).map ι).map (MulAut.conj g).toMonoidHom = S' := by
    have h := congrArg (fun T : Sylow p G' => (T : Subgroup G')) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h
    rw [← h, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g, ?_, ?_⟩
  · rw [← Subgroup.map_map, hconj]
    haveI : (A.subgroupOf R).Normal := by
      refine ⟨fun a ha r => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      have h1 := (Subgroup.mem_normalizer_iff.1 (hRN r.2) a).1 ha
      simpa using h1
    have hAp' : IsPGroup p (A.subgroupOf R) := hAp.comap_of_injective R.subtype R.subtype_injective
    have hle := hAp'.le_sylow_of_normal S
    intro a ha
    exact ⟨⟨a, hAR ha⟩, hle (by simpa [Subgroup.mem_subgroupOf] using ha), rfl⟩
  · rw [← Subgroup.map_map, hconj]
    exact Subgroup.map_subtype_le _

theorem three_le_pRank_centralizer_of_overgroup (hp : p.Prime) (ι : G →* G')
    (hι : Function.Injective ι) (hidx : ¬ p ∣ ι.range.index) {R A : Subgroup G'} (hAR : A ≤ R)
    (hRN : R ≤ normalizer (A : Set G')) (hRidx : ¬ p ∣ R.index) (hA : IsElemAbelian p A)
    {n : ℕ} (hAc : Nat.card A = p ^ n) (hn : p + 1 ≤ n) {y : G} (hy : y ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hyP⟩ := (isPGroup_zpowers_of_pow_eq_one hy).exists_le_sylow
  have hyP' : y ∈ (P : Subgroup G) := hyP (mem_zpowers y)
  have hAp : IsPGroup p A := fun a => ⟨1, Subtype.ext (by simpa using hA.2 a a.2)⟩
  obtain ⟨g, hAS, hSR⟩ := exists_conj_sylow_between hp ι hι hidx hAR hRN hRidx hAp P
  set ψ : G →* G' := (MulAut.conj g).toMonoidHom.comp ι with hψ
  have hψi : Function.Injective ψ := (MulAut.conj g).injective.comp hι
  set S : Subgroup G' := (P : Subgroup G).map ψ with hS
  have hSN : S ≤ normalizer (A : Set G') := hSR.trans hRN
  have hvS : ψ y ∈ S := Subgroup.mem_map_of_mem ψ hyP'
  have hvp : ψ y ^ p = 1 := by rw [← map_pow, hy, map_one]
  have h3 := CFSG.AGLEmbedding.three_le_pRank_centralizer_of_normal_elemAbelian hp hAS hSN hA hAc
    hn hvS hvp
  obtain ⟨E, hEC, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (S ⊓ centralizer ({ψ y} : Set G'))
  have hErange : E ≤ ψ.range := fun e he => by
    obtain ⟨x, -, hx⟩ := (hEC he).1
    exact ⟨x, hx⟩
  have hmap : (E.comap ψ).map ψ = E := Subgroup.map_comap_eq_self hErange
  have hE' : IsElemAbelian p (E.comap ψ) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hψi ?_)⟩⟩, fun x hx => hψi ?_⟩
    · have := congrArg Subtype.val (hE.1.is_comm.comm ⟨ψ a, a.2⟩ ⟨ψ b, b.2⟩)
      simpa using this
    · rw [map_pow, map_one]
      exact hE.2 _ hx
  have hcard : Nat.card (E.comap ψ) = p ^ CFSG.Open.pRank p (S ⊓ centralizer ({ψ y} : Set G')) := by
    have h1 : Nat.card ((E.comap ψ).map ψ) = Nat.card (E.comap ψ) :=
      Subgroup.card_map_of_injective hψi
    rw [hmap] at h1
    rw [← h1, hEc]
  have hle : E.comap ψ ≤ centralizer ({y} : Set G) := by
    intro x hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hEC hx).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hψi
    simpa only [map_mul] using h1
  have := CFSG.SectionRank.le_pRank hp.one_lt hle hE' hcard
  omega

theorem le_pRank_of_overgroup (hp : p.Prime) (ι : G →* G') (hι : Function.Injective ι)
    (hidx : ¬ p ∣ ι.range.index) {R A : Subgroup G'} (hAR : A ≤ R)
    (hRN : R ≤ normalizer (A : Set G')) (hRidx : ¬ p ∣ R.index) (hA : IsElemAbelian p A)
    {n : ℕ} (hAc : Nat.card A = p ^ n) : n ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hAp : IsPGroup p A := fun a => ⟨1, Subtype.ext (by simpa using hA.2 a a.2)⟩
  obtain ⟨g, hAS, -⟩ := exists_conj_sylow_between hp ι hι hidx hAR hRN hRidx hAp P
  set ψ : G →* G' := (MulAut.conj g).toMonoidHom.comp ι with hψ
  have hψi : Function.Injective ψ := (MulAut.conj g).injective.comp hι
  have hArange : A ≤ ψ.range := fun a ha => by
    obtain ⟨x, -, hx⟩ := hAS ha
    exact ⟨x, hx⟩
  have hmap : (A.comap ψ).map ψ = A := Subgroup.map_comap_eq_self hArange
  have hA' : IsElemAbelian p (A.comap ψ) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hψi ?_)⟩⟩, fun x hx => hψi ?_⟩
    · have := congrArg Subtype.val (hA.1.is_comm.comm ⟨ψ a, a.2⟩ ⟨ψ b, b.2⟩)
      simpa using this
    · rw [map_pow, map_one]
      exact hA.2 _ hx
  have hcard : Nat.card (A.comap ψ) = p ^ n := by
    have h1 : Nat.card ((A.comap ψ).map ψ) = Nat.card (A.comap ψ) :=
      Subgroup.card_map_of_injective hψi
    rw [hmap] at h1
    rw [← h1, hAc]
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hA' hcard

end CFSG.LocalAnalysis.RankFourTheoremC
