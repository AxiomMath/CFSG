module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

private theorem markTransport_indAut_zpow {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {b : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (k : ℤ) :
    MI.indAut p L (b ^ k) (Subgroup.zpow_mem _ hbN k) = MI.indAut p L b hbN ^ k := by
  unfold MI.indAut
  rw [← map_zpow]
  congr 1
  exact Subtype.ext (by simp [zpow_neg, inv_zpow])

private theorem markTransport_congr_indAut {G G' : Type} [Group G] [Group G']
    {p : ℕ} {J : Subgroup G} {J' : Subgroup G'} {b : G} {b' : G'}
    (e : PSimple p J ≃* PSimple p J')
    (hbN : b ∈ Subgroup.normalizer (J : Set G))
    (hb'N : b' ∈ Subgroup.normalizer (J' : Set G'))
    (hIso : ∀ s s' : PSimple p J, indRelS p J b s s' →
      indRelS p J' b' (e s) (e s')) :
    MulAut.congr e (MI.indAut p J b hbN) = MI.indAut p J' b' hb'N := by
  ext s
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (e.symm s)
  have hs : s = e (QuotientGroup.mk q) := by rw [hq, MulEquiv.apply_symm_apply]
  obtain ⟨q', hq'⟩ := MI.indRel_total hbN q
  have hrelS : indRelS p J b (QuotientGroup.mk q) (QuotientGroup.mk q') :=
    ⟨q, q', hq', rfl, rfl⟩
  obtain ⟨r, r', hr, hrq, hrq'⟩ := hIso _ _ hrelS
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, ← hq,
    MI.indAut_apply_mk hbN hq', ← hrq', ← MI.indAut_apply_mk hb'N hr, hrq, ← hs]

private theorem markTransport_congr_indAut_zpow {G G' : Type} [Group G] [Group G']
    {p : ℕ} {J : Subgroup G} {J' : Subgroup G'} {b : G} {b' : G'}
    (e : PSimple p J ≃* PSimple p J')
    (hbN : b ∈ Subgroup.normalizer (J : Set G))
    (hb'N : b' ∈ Subgroup.normalizer (J' : Set G'))
    (hIso : ∀ s s' : PSimple p J, indRelS p J b s s' →
      indRelS p J' b' (e s) (e s')) (k : ℤ) :
    MulAut.congr e (MI.indAut p J (b ^ k) (Subgroup.zpow_mem _ hbN k)) =
      MI.indAut p J' (b' ^ k) (Subgroup.zpow_mem _ hb'N k) := by
  rw [markTransport_indAut_zpow hbN k, markTransport_indAut_zpow hb'N k, map_zpow,
    markTransport_congr_indAut e hbN hb'N hIso]

theorem markTransport_holds : MarkTransport := by
  intro G G' _ _ _ _ p J J' b b' e hcomm hbN hIso hdiag'
  obtain ⟨hb'N, hmark'⟩ := hdiag'
  have hb'norm : b' ∈ Subgroup.normalizer (J' : Set G') := hb'N (Subgroup.mem_zpowers b')
  refine ⟨Subgroup.zpowers_le.2 hbN, ?_⟩
  refine lemma102_marking_transport hcomm e ?_ hmark'
  intro lab R _ I F θ hP
  intro a ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hbk : b ^ k ∈ Subgroup.normalizer (J : Set G) := Subgroup.zpow_mem _ hbN k
  have hb'k : b' ^ k ∈ Subgroup.normalizer (J' : Set G') := Subgroup.zpow_mem _ hb'norm k
  obtain ⟨φ, hφI, hφ⟩ := hP (b' ^ k) (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b') k)
  refine ⟨φ, hφI, ?_⟩
  have h1 : φ = MulAut.congr θ (MI.indAut p J' (b' ^ k) hb'k) :=
    (MI.induces_indRel_iff hb'k θ).1 hφ
  have h2 : MulAut.congr e (MI.indAut p J (b ^ k) hbk) =
      MI.indAut p J' (b' ^ k) hb'k :=
    markTransport_congr_indAut_zpow e hbN hb'norm hIso k
  have h3 : MulAut.congr (e.trans θ) (MI.indAut p J (b ^ k) hbk) =
      MulAut.congr θ (MI.indAut p J' (b' ^ k) hb'k) := by
    rw [← h2]
    ext y
    simp [MulAut.congr_apply]
  exact (MI.induces_indRel_iff hbk (e.trans θ)).2 (h1.trans h3.symm)

end CFSG.LocalAnalysis.GLTheoremA.F151

end
