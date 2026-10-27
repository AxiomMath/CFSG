module

public import CFSG.CGT.Foote82.Lemma62Tools
import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Basic
import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem le_normalizer_of_le_centralizer {S L : Subgroup (GLV V)}
    (h : L ≤ Subgroup.centralizer (S : Set (GLV V))) :
    S ≤ Subgroup.normalizer (L : Set (GLV V)) := by
  intro s hs
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  exact fun l hl => ((Subgroup.mem_centralizer_iff.mp (h hl)) s hs).symm

private theorem mem_normalizer_commutator {X Y : Subgroup (GLV V)} {g : GLV V}
    (hX : g ∈ Subgroup.normalizer (X : Set (GLV V)))
    (hY : g ∈ Subgroup.normalizer (Y : Set (GLV V))) :
    g ∈ Subgroup.normalizer ((⁅X, Y⁆ : Subgroup (GLV V)) : Set (GLV V)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hX hY ⊢
  rw [Subgroup.map_commutator, hX, hY]

private theorem normalizer_le_normalizer_map {K : Subgroup (GLV V)} (N : Subgroup ↥K)
    [N.Characteristic] :
    Subgroup.normalizer (K : Set (GLV V)) ≤
      Subgroup.normalizer (N.map K.subtype : Set (GLV V)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hcomp : ((MulAut.conj g : MulAut (GLV V)) : GLV V →* GLV V).comp K.subtype =
      K.subtype.comp (Subgroup.normalizerMonoidHom K ⟨g, hg⟩ : ↥K →* ↥K) := by
    ext k
    simp
  have hN : N.map (Subgroup.normalizerMonoidHom K ⟨g, hg⟩ : ↥K →* ↥K) = N :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance _
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hN]

private theorem le_centralizer_of_commutator_eq {K L N : Subgroup (GLV V)} (hKL : ⁅K, L⁆ = K)
    (hNK : K ≤ Subgroup.normalizer (N : Set (GLV V))) (hNL : ⁅N, L⁆ = ⊥) :
    N ≤ Subgroup.centralizer (K : Set (GLV V)) := by
  have h1 : ⁅⁅L, N⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_comm L N, hNL]
    exact Subgroup.commutator_bot_left K
  have h2 : ⁅⁅N, K⁆, L⁆ = ⊥ := le_bot_iff.mp
    ((Subgroup.commutator_mono_left (Subgroup.le_normalizer_iff_commutator_le_left.mp hNK)).trans
      hNL.le)
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hKL] at h3
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp ((Subgroup.commutator_comm N K).trans h3)

private theorem Conf62.commutator_eq {G S L K : Subgroup (GLV V)} (hc : Conf62 G S L K)
    (hmin : Min62 S L K) (hne : ⁅K, L⁆ ≠ ⊥) : ⁅K, L⁆ = K := by
  have hL := hc.setup.component
  have hperf : ⁅L, L⁆ = L :=
    CFSG.ComponentClassification.Asc76.Sec5.commutator_self_of_isQuasisimple hL.2.2
  have hle : ⁅K, L⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hc.L_le
  refine hle.eq_of_not_lt fun hlt => hne ?_
  refine CFSG.ComponentClassification.Asc76.Sec5.commutator_eq_bot_of_commutator_commutator_eq_bot
    hperf (hmin _ hlt ?_ ?_)
  · exact fun s hs => mem_normalizer_commutator (hc.S_le hs)
      (le_normalizer_of_le_centralizer (fun l hl => (Subgroup.mem_inf.mp (hL.1 hl)).2) hs)
  · exact Subgroup.normalizer_commutator_ge_right K L

private theorem Conf62.exists_pGroup {G S L K : Subgroup (GLV V)} (hc : Conf62 G S L K)
    (hmin : Min62 S L K) (hKL : ⁅K, L⁆ = K) (hne : ⁅K, L⁆ ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p K := by
  by_contra hcon
  push Not at hcon
  have hsolv : Group.IsSolvable ↥K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hc.odd
  have hPlt : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥K → (CFSG.pCore q ↥K).map K.subtype < K := by
    intro q hq hqd
    refine lt_of_le_of_ne (Subgroup.map_subtype_le _) fun heq => ?_
    have htop : CFSG.pCore q ↥K = ⊤ := by
      apply Subgroup.map_injective K.subtype_injective
      rw [heq, Subgroup.map_top, Subgroup.range_subtype]
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hc.odd) (even_iff_two_dvd.mpr hqd)
    refine hcon q hq hq2 ?_
    have hp := CFSG.pCore_isPGroup (p := q) (G := ↥K)
    rw [htop] at hp
    exact hp.of_equiv Subgroup.topEquiv
  have hcent : ∀ p : (Nat.card ↥K).primeFactors.attach,
      (CFSG.pCore p.1.1 ↥K).map K.subtype ≤ Subgroup.centralizer (K : Set (GLV V)) ∧
      (CFSG.pCore p.1.1 ↥K).map K.subtype ≤ Subgroup.centralizer (L : Set (GLV V)) := by
    intro p
    have hlt := hPlt p.1.1 (Nat.prime_of_mem_primeFactors p.1.2)
      (Nat.dvd_of_mem_primeFactors p.1.2)
    have hnorm := normalizer_le_normalizer_map (CFSG.pCore p.1.1 ↥K)
    have hL0 : ⁅(CFSG.pCore p.1.1 ↥K).map K.subtype, L⁆ = ⊥ :=
      hmin _ hlt (hc.S_le.trans hnorm) (hc.L_le.trans hnorm)
    exact ⟨le_centralizer_of_commutator_eq hKL (Subgroup.le_normalizer.trans hnorm) hL0,
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hL0⟩
  have hF : (CFSG.fittingSubgroup ↥K).map K.subtype =
      ⨆ p : (Nat.card ↥K).primeFactors.attach, (CFSG.pCore p.1.1 ↥K).map K.subtype := by
    rw [CFSG.fitting_eq_sup_pCore, Subgroup.map_iSup]
  have hFK : CFSG.fittingSubgroup ↥K = ⊤ := by
    refine top_le_iff.mp fun c _ => ?_
    refine CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hfF : (f : GLV V) ∈ (CFSG.fittingSubgroup ↥K).map K.subtype :=
      Subgroup.mem_map_of_mem _ hf
    rw [hF] at hfF
    have hfC : (f : GLV V) ∈ Subgroup.centralizer (K : Set (GLV V)) :=
      (iSup_le fun p => (hcent p).1) hfF
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hfC (c : GLV V) c.2).symm
  have hKF : K = ⨆ p : (Nat.card ↥K).primeFactors.attach,
      (CFSG.pCore p.1.1 ↥K).map K.subtype := by
    rw [← hF, hFK, Subgroup.map_top, Subgroup.range_subtype]
  refine hne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_)
  calc K = ⨆ p : (Nat.card ↥K).primeFactors.attach, (CFSG.pCore p.1.1 ↥K).map K.subtype := hKF
    _ ≤ Subgroup.centralizer (L : Set (GLV V)) := iSup_le fun p => (hcent p).2

theorem Conf62.min_structure {G S L K : Subgroup (GLV V)} (hc : Conf62 G S L K)
    (hmin : Min62 S L K) (hne : ⁅K, L⁆ ≠ ⊥) :
    ⁅K, L⁆ = K ∧ (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p K) ∧ ⁅frat K, L⁆ = ⊥ ∧
      frat K ≤ Subgroup.centralizer (K : Set (GLV V)) := by
  have hKL := hc.commutator_eq hmin hne
  obtain ⟨p, hp, hp2, hpK⟩ := hc.exists_pGroup hmin hKL hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hKbot : K ≠ ⊥ := fun h => hne (by rw [h]; exact Subgroup.commutator_bot_left L)
  have hnorm := normalizer_le_normalizer_frat K
  have hfrat : ⁅frat K, L⁆ = ⊥ :=
    hmin _ (frat_lt hpK hKbot) (hc.S_le.trans hnorm) (hc.L_le.trans hnorm)
  exact ⟨hKL, ⟨p, hp, hp2, hpK⟩, hfrat,
    le_centralizer_of_commutator_eq hKL (Subgroup.le_normalizer.trans hnorm) hfrat⟩

theorem Conf62.fixes_fixedSpace {G S L K : Subgroup (GLV V)} (hc : Conf62 G S L K)
    (hne : ⁅K, L⁆ ≠ ⊥) : ∀ l ∈ L, ∀ v ∈ fixedSpace K, l v = v := by
  have hperf : ⁅L, L⁆ = L :=
    CFSG.ComponentClassification.Asc76.Sec5.commutator_self_of_isQuasisimple
      hc.setup.component.2.2
  have hLK : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K := fun l hl k hk =>
    (Subgroup.mem_normalizer_iff.mp (hc.L_le hl) k).mp hk
  have hKK : ∀ k' ∈ K, ∀ k ∈ K, k' * k * k'⁻¹ ∈ K := fun k' hk' k hk =>
    K.mul_mem (K.mul_mem hk' hk) (K.inv_mem hk')
  have hcompl := isCompl_fixedSpace_commSpace hc.odd
  rcases trivial_on_summand hperf hc.setup.irrTilde hcompl (invariant_fixedSpace hLK)
    (invariant_commSpace hLK fun _ _ _ _ => Submodule.mem_top) with h | h
  · exact h
  · refine absurd (le_bot_iff.mp ?_) hne
    have hY := fixes_of_commutator
      (invariant_commSpace hKK fun _ _ _ _ => Submodule.mem_top) h
    have hle : ⁅K, L⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hc.L_le
    intro g hg
    rw [Subgroup.mem_bot]
    ext v
    have hv : v ∈ fixedSpace K ⊔ commSpace K ⊤ := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hx g (hle hg), hY g hg y hy]
    rfl

end CFSG.CGT.Foote82
