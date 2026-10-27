module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeHub
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeEscape
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeFix

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.ToralCensus
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg

@[expose] def HubWitnesses {K : Type*} [Group K] (D : UniversalRootDatum K) : Prop :=
  ∀ (I : Set (Fin D.rank)) (i : Fin D.rank), i ∈ I → (∃ k, k ∉ I) →
    (I = {i} ∨ ∃ j : Fin D.rank, j ≠ i ∧ I = {i, j} ∧ D.cartan i j * D.cartan j i = 1) →
    ∃ (x : K) (w : (coxeterMatrix D.isFiniteType).Group) (m k : Fin D.rank),
      ActsAs D x w ∧ k ∉ I ∧ 0 < weylAction D.isFiniteType w (Pi.single m 1) k ∧
      Commutes (rankOne D.rootGroup i) ((rankOne D.rootGroup m).map (MulAut.conj x).toMonoidHom)

theorem centralizerEscapes_of_hubWitnesses {K Y : Type} [Group K] [Group Y] [Finite K]
    [Finite Y] {D : UniversalRootDatum K} {nW : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    {π : K →* Y} {M q : ℕ} (h : BorelQuotient D nW H π M) (hD : D.divisible = ∅) (hq4 : 4 ≤ q)
    (hrank : ∀ i, RankOneNode D i q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : ∀ i, ∃ x ∈ (rankOne D.rootGroup i).map π, orderOf x = p) (hW : HubWitnesses D) :
    CentralizerEscapes p Y := by
  intro S J hNJ hJN hJtop hcyc u hu hup huZ
  obtain ⟨π', hπ', hker, hT, i, hi, ⟨g, hg, hgu⟩, hI⟩ :=
    hubSingleNode h hD hq4 hrank p hp hp2 hord S J hNJ hJN hJtop hcyc u hu hup huZ
  have hQ : BorelQuotient D nW H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel D H).map π' ≤ J := by
    rw [← hNπ]
    exact hNJ
  obtain ⟨x, w, m, k, hx, hk, hpos, hcomm⟩ :=
    hW _ i hi (LieOut.exists_node_not_mem_negIndices hQ hBJ hJtop) hI
  obtain ⟨P, hP, hPc, hPJ⟩ :=
    exists_escape_of_witness hQ hBJ hk hx hpos ((hrank m).perfect hq4) hcomm hgu
  exact ⟨g, hg, P, hP, hPc, hPJ⟩

section Witnesses

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem hubWitness_of_cartan_eq_zero (hext : SteinbergExtras D n H) {I : Set (Fin D.rank)}
    {i k : Fin D.rank} (hik : i ≠ k) (hk : k ∉ I) (h0 : D.cartan i k = 0) :
    ∃ (x : K) (w : (coxeterMatrix D.isFiniteType).Group) (m k' : Fin D.rank),
      ActsAs D x w ∧ k' ∉ I ∧ 0 < weylAction D.isFiniteType w (Pi.single m 1) k' ∧
      Commutes (rankOne D.rootGroup i)
        ((rankOne D.rootGroup m).map (MulAut.conj x).toMonoidHom) := by
  refine ⟨1, 1, k, k, ActsAs.one, hk, by simp, ?_⟩
  have e : (rankOne D.rootGroup k).map (MulAut.conj (1 : K)).toMonoidHom =
      rankOne D.rootGroup k := by
    rw [map_one]
    exact Subgroup.map_id _
  rw [e]
  exact commutes_rankOne_of_cartan_eq_zero hext hik h0

theorem hubWitness_of_three
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {I : Set (Fin D.rank)} {a i b k : Fin D.rank} (hab : a ≠ b)
    (h1 : D.cartan a i = -1) (h2 : D.cartan i a = -1) (h3 : D.cartan a b = 0) (hk : k ∉ I)
    (hpos : 0 < (Pi.single b 1 - D.cartan i b • Pi.single i 1 -
      D.cartan i b • Pi.single a 1 : Fin D.rank → ℤ) k) :
    ∃ (x : K) (w : (coxeterMatrix D.isFiniteType).Group) (m k' : Fin D.rank),
      ActsAs D x w ∧ k' ∉ I ∧ 0 < weylAction D.isFiniteType w (Pi.single m 1) k' ∧
      Commutes (rankOne D.rootGroup i)
        ((rankOne D.rootGroup m).map (MulAut.conj x).toMonoidHom) :=
  ⟨n a * n i, _, b, k, (actsAs_n hct a).mul (actsAs_n hct i), hk,
    by rwa [weylAction_three_single h1 h3], commutes_rankOne_three hct hext hab h1 h2 h3⟩

theorem hubWitness_of_bTwo
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hD : D.divisible = ∅) {I : Set (Fin D.rank)}
    {l s : Fin D.rank} (hls : l ≠ s) (h1 : D.cartan l s = -1) (h2 : D.cartan s l = -2)
    (hs : s ∉ I) :
    ∃ (x : K) (w : (coxeterMatrix D.isFiniteType).Group) (m k' : Fin D.rank),
      ActsAs D x w ∧ k' ∉ I ∧ 0 < weylAction D.isFiniteType w (Pi.single m 1) k' ∧
      Commutes (rankOne D.rootGroup l)
        ((rankOne D.rootGroup m).map (MulAut.conj x).toMonoidHom) :=
  ⟨n s, _, l, s, actsAs_n hct s, hs, by rw [weylAction_bTwo h2, pair_apply_right hls]; norm_num,
    commutes_rankOne_bTwo hct hext hD hls h1 h2⟩

end Witnesses

end CFSG.AGLEmbedding
