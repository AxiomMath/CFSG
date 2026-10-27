module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511D
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512E
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526LN
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding Subgroup

variable {X : Type} [Group X] [Finite X]

theorem exists_conj_eq_of_le_normalizer {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} (hinv : gnImg T T ≤ normalizer (Ls : Set (X ⧸ gnC T))) (m : X)
    (hT : ∀ t ∈ T, (Ls.map (MulAut.conj (toStar T m)).toMonoidHom).map
      (MulAut.conj (toStar T t)).toMonoidHom = Ls.map (MulAut.conj (toStar T m)).toMonoidHom) :
    ∃ x ∈ normalizer (T : Set X), Ls.map (MulAut.conj (toStar T x)).toMonoidHom =
      Ls.map (MulAut.conj (toStar T m)).toMonoidHom := by
  set N : Subgroup X := (normalizer (Ls : Set (X ⧸ gnC T))).comap (toStar T)
  have hTN : T ≤ N := fun t ht => hinv ⟨t, ht, rfl⟩
  have hT'N : T.map (MulAut.conj m⁻¹).toMonoidHom ≤ N := by
    rintro _ ⟨t, ht, rfl⟩
    show toStar T ((MulAut.conj m⁻¹).toMonoidHom t) ∈ normalizer (Ls : Set (X ⧸ gnC T))
    refine mem_normalizer_of_map_conj_eq_s15 ?_
    have hel : toStar T ((MulAut.conj m⁻¹).toMonoidHom t) =
        (toStar T m)⁻¹ * toStar T t * toStar T m := by
      simp [MulAut.conj_apply]
    rw [hel]
    calc Ls.map (MulAut.conj ((toStar T m)⁻¹ * toStar T t * toStar T m)).toMonoidHom
        = ((Ls.map (MulAut.conj (toStar T m)).toMonoidHom).map
            (MulAut.conj (toStar T t)).toMonoidHom).map
            (MulAut.conj (toStar T m)⁻¹).toMonoidHom := by
          rw [ystar_normal_aux1, ystar_normal_aux1]
      _ = (Ls.map (MulAut.conj (toStar T m)).toMonoidHom).map
            (MulAut.conj (toStar T m)⁻¹).toMonoidHom := by rw [hT t ht]
      _ = Ls := by rw [ystar_normal_aux1, inv_mul_cancel, ystar_normal_aux2]
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.2 hX.sylow
  obtain ⟨n, hnN, hn⟩ := normalizer_inf_le_of_sylow_aux2
    ((ystar_normal_aux7 hSyl m⁻¹).of_le hT'N le_top) (hSyl.of_le hTN le_top)
  rw [ystar_normal_aux1] at hn
  have hy : n * m⁻¹ ∈ normalizer (T : Set X) := mem_normalizer_of_map_conj_eq_s15 hn.symm
  have hx : m * n⁻¹ ∈ normalizer (T : Set X) := by
    simpa [mul_inv_rev] using Subgroup.inv_mem _ hy
  have hnLs : toStar T n ∈ normalizer (Ls : Set (X ⧸ gnC T)) := hnN
  refine ⟨m * n⁻¹, hx, ?_⟩
  calc Ls.map (MulAut.conj (toStar T (m * n⁻¹))).toMonoidHom
      = (Ls.map (MulAut.conj (toStar T n)⁻¹).toMonoidHom).map
          (MulAut.conj (toStar T m)).toMonoidHom := by
        rw [ystar_normal_aux1, map_mul, map_inv]
    _ = Ls.map (MulAut.conj (toStar T m)).toMonoidHom := by
        rw [ystar_normal_aux3 (Subgroup.inv_mem _ hnLs)]

theorem ystar_normal_of_others {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hg : IsGNPair T T₁ T₂) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h₁ : CFSG.Open.pRank q (normalizer (T₁ : Set X)) ≤ 1)
    (h₂ : CFSG.Open.pRank q (normalizer (T₂ : Set X)) ≤ 1)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls)
    (hinv : gnImg T T ≤ normalizer (Ls : Set (X ⧸ gnC T)))
    (hoth : ∀ Is, GNYComponent T T₁ T₂ Is → Is ≠ Ls → ¬ q ∣ Nat.card ↥Is)
    (hZ : ¬ q ∣ Nat.card (Subgroup.center ↥Ls)) (hd : q ∣ Nat.card ↥Ls) :
    Ls.Normal := by
  have hcard : ∀ g : X ⧸ gnC T,
      Nat.card ↥(Ls.map (MulAut.conj g).toMonoidHom) = Nat.card ↥Ls :=
    fun g => Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcen : ∀ g : X ⧸ gnC T, Nat.card (Subgroup.center ↥(Ls.map (MulAut.conj g).toMonoidHom)) =
      Nat.card (Subgroup.center ↥Ls) :=
    fun g => (Nat.card_congr (Subgroup.centerCongr (Ls.equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)).toEquiv).symm
  have huniq : ∀ g : X ⧸ gnC T, GNYComponent T T₁ T₂ (Ls.map (MulAut.conj g).toMonoidHom) →
      Ls.map (MulAut.conj g).toMonoidHom = Ls := by
    intro g hc
    by_contra hne
    exact hoth _ hc hne (by rw [hcard]; exact hd)
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (gnC T) g
  have key : Ls.map (MulAut.conj (toStar T m)).toMonoidHom = Ls := by
    by_contra hne
    have hL' : CFSG.Open.IsComponentOf (Ls.map (MulAut.conj (toStar T m)).toMonoidHom) ⊤ :=
      isComponentOf_conj_aux hLs.1 _
    have hcov : Ls.map (MulAut.conj (toStar T m)).toMonoidHom ≤
          gnImg T (centralizer (T₁ : Set X)) ∨
        Ls.map (MulAut.conj (toStar T m)).toMonoidHom ≤ gnImg T (normalizer (T₂ : Set X)) := by
      by_contra hcon
      rw [not_or] at hcon
      exact hne (huniq _ ⟨hL', hcon.1, hcon.2⟩)
    have hZ' :
        ¬ q ∣ Nat.card (Subgroup.center ↥(Ls.map (MulAut.conj (toStar T m)).toMonoidHom)) := by
      rw [hcen]
      exact hZ
    have hd' : q ∣ Nat.card ↥(Ls.map (MulAut.conj (toStar T m)).toMonoidHom) := by
      rw [hcard]
      exact hd
    by_cases hmove : ∀ t ∈ T, (Ls.map (MulAut.conj (toStar T m)).toMonoidHom).map
        (MulAut.conj (toStar T t)).toMonoidHom = Ls.map (MulAut.conj (toStar T m)).toMonoidHom
    · obtain ⟨x, hx, hxeq⟩ := exists_conj_eq_of_le_normalizer hX hinv m hmove
      have hx' := ystar_normal_aux5 hg hx
      exact hne (hxeq.symm.trans (huniq _ (gnYComponent_conj_of_mem hLs hx'.1 hx'.2)))
    · push Not at hmove
      obtain ⟨t, ht, htne⟩ := hmove
      rcases hcov with hc | hc
      · have h2 := ystar_normal_aux6 (gnYComponent_conj_of_mem_aux1
          (IsGNPair.le_normalizer₁ hg ht)) hq hq2 hL' hc htne hZ' hd'
        have h3 := CFSG.SectionRank.pRank_mono (p := q) hq.one_lt
          (Subgroup.centralizer_le_normalizer (T₁ : Set X))
        omega
      · have h2 := ystar_normal_aux6 (gnYComponent_conj_of_mem_aux2
          (IsGNPair.le_normalizer₂ hg ht)) hq hq2 hL' hc htne hZ' hd'
        omega
  have hmem : (MulAut.conj (toStar T m)) n ∈ Ls.map (MulAut.conj (toStar T m)).toMonoidHom :=
    ⟨n, hn, rfl⟩
  rw [key] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem normal_of_k518Y_hyps {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hg : GNGood T T₁ T₂) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : GNYComponent T T₁ T₂ Ls) (hinv : gnImg T T ≤ normalizer (Ls : Set (X ⧸ gnC T)))
    (m1 : mS T T₁ p Ls = 1) (m2 : mS T T₂ p Ls = 1) (n1 : mN T₁ p = 1) (n2 : mN T₂ p = 1)
    (hoth : ∀ Is, GNYComponent T T₁ T₂ Is → Is ≠ Ls → ¬ p ∣ Nat.card ↥Is) : Ls.Normal := by
  have m1' : CFSG.Open.pRank p (gnA T T₁ Ls) = 1 := m1
  have m2' : CFSG.Open.pRank p (gnA T T₂ Ls) = 1 := m2
  have hd : p ∣ Nat.card ↥Ls := by
    obtain ⟨F, hF, -, hFcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (gnA T T₁ Ls)
    have hpF : p ∣ Nat.card F := by
      rw [hFcard]
      exact dvd_pow_self p (by omega)
    exact hpF.trans (Subgroup.card_dvd_of_le (hF.trans inf_le_right))
  have hZ : ¬ p ∣ Nat.card (Subgroup.center ↥Ls) := fun h => by
    rcases hg.centre Ls hLs hinv p hp h with h' | h' <;> omega
  exact ystar_normal_of_others hX hg.pair hp hp2 n1.le n2.le hLs hinv hoth hZ hd

end CFSG.LocalAnalysis.RankThreeUC.S15
