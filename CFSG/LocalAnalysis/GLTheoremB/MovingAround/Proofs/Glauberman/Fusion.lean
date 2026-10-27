module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Glauberman.Basic
public import CFSG.GH74.GLS.Stage2.Signalizer.L53Kfam
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

open Subgroup
open CFSG.GH74.GLS.Bg (kLowInfty Kfam Klow classTwo zOf gen)
open scoped commutatorElement

section KInfty

variable {G : Type} [Group G]

theorem zOf_le_kLowInfty (T : Subgroup G) : T ⊓ centralizer (T : Set G) ≤ kLowInfty T := by
  have hmem : T ⊓ centralizer (T : Set G) ∈ Kfam T 1 := by
    rw [CFSG.GH74.GLS.Stage2.Signalizer.L53.Kfam_succ_even T (by decide : Even 0)]
    refine ⟨⟨inf_le_left, ?_⟩, ?_, ?_⟩
    · have : ⁅T ⊓ centralizer (T : Set G), T ⊓ centralizer (T : Set G)⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact (Subgroup.mem_centralizer_iff.mp hw.2 z hz.1).symm
      rw [this, Subgroup.commutator_bot_left]
    · intro x hx
      have hxT : x ∈ T := CFSG.GH74.GLS.Stage2.Signalizer.L53.gen_le
        (fun B hB => (CFSG.GH74.GLS.Stage2.Signalizer.L53.Kfam_subset_classTwo T 0 hB).1) hx
      have hfix : ∀ w ∈ T ⊓ centralizer (T : Set G), ∀ y ∈ T, y * w * y⁻¹ = w := by
        intro w hw y hy
        rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2 y hy]
        group
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        rw [hfix z hz x hxT]
        exact hz
      · intro hz
        have e : z = x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ := by group
        rw [e, hfix _ hz x⁻¹ (T.inv_mem hxT)]
        exact hz
    · intro A hA _ _ _ _
      have : ⁅T ⊓ centralizer (T : Set G), A⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 a (hA.1 ha)
      rw [this]; exact bot_le
  intro x hx
  exact Subgroup.subset_closure (Set.mem_iUnion₂.mpr ⟨_, Set.mem_iUnion.mpr ⟨0, hmem⟩, hx⟩)

theorem kLowInfty_le' (T : Subgroup G) : kLowInfty T ≤ T :=
  CFSG.GH74.GLS.Stage2.Signalizer.L53.gen_le fun B hB => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hB
    exact (CFSG.GH74.GLS.Stage2.Signalizer.L53.Kfam_subset_classTwo T _ hi).1

theorem kLowInfty_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {T : Subgroup G} (hT : IsPGroup p T)
    (hT1 : T ≠ ⊥) : kLowInfty T ≠ ⊥ := by
  haveI : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
  haveI := hT.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : center T)
  intro h
  apply hz
  have hzK : ((z : T) : G) ∈ kLowInfty T := by
    refine zOf_le_kLowInfty T (Subgroup.mem_inf.mpr ⟨(z : T).2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := Subgroup.mem_center_iff.mp z.2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  rw [h, Subgroup.mem_bot] at hzK
  exact Subtype.ext (Subtype.ext hzK)

theorem le_nK (T : Subgroup G) : T ≤ nK T :=
  le_normalizer.trans (CFSG.GH74.GLS.Stage2.Signalizer.L53.normalizer_le_kLowInfty T)

end KInfty

section NormalizerGrowth

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem lt_inf_normalizer {S T : Subgroup G} (hS : IsPGroup p S) (hTS : T < S) :
    T < S ⊓ normalizer (T : Set G) := by
  haveI : Group.IsNilpotent S := hS.isNilpotent
  have hlt : T.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hTS.not_ge (subgroupOf_eq_top.mp h)
  have h2 := Group.normalizerCondition_of_isNilpotent _ hlt
  obtain ⟨x, hxN, hxT⟩ := SetLike.exists_of_lt h2
  refine lt_of_le_of_ne (le_inf hTS.le le_normalizer) fun h => hxT ?_
  have hx : (x : G) ∈ S ⊓ normalizer (T : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have := (Subgroup.mem_normalizer_iff.mp hxN ⟨y, hTS.le hy⟩).mp hy
      exact this
    · intro hy
      have hyS : y ∈ S := by
        have h1 : (x : G) * y * (x : G)⁻¹ ∈ S := hTS.le hy
        have : y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * x := by group
        rw [this]
        exact S.mul_mem (S.mul_mem (S.inv_mem x.2) h1) x.2
      exact (Subgroup.mem_normalizer_iff.mp hxN ⟨y, hyS⟩).mpr hy
  rw [← h] at hx
  exact hx

end NormalizerGrowth

section Fusion

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

@[expose] def FusIn (D T H : Subgroup G) : Prop :=
  ∀ y ∈ T, ∀ h ∈ H, h⁻¹ * y * h ∈ T → y⁻¹ * (h⁻¹ * y * h) ∈ D

theorem inf_commutator_le_of_fusIn {D T H : Subgroup G} (hT : IsSylowOf p H T)
    (hF : FusIn D T H) : T ⊓ ⁅H, H⁆ ≤ D := by
  rintro x ⟨hxT, hxc⟩
  rw [← map_subtype_commutator] at hxc
  obtain ⟨x', hx', rfl⟩ := hxc
  have hfoc := Subgroup.commutator_inf_eq_focalSubgroup hT.toSylow
  have hmem : x' ∈ commutator ↥H ⊓ (hT.toSylow : Subgroup ↥H) := by
    refine Subgroup.mem_inf.mpr ⟨hx', ?_⟩
    rw [IsSylowOf.coe_toSylow]
    exact hxT
  rw [hfoc, focalSubgroup_def] at hmem
  have hle : closure {g : ↥H | g ∈ (hT.toSylow : Subgroup ↥H) ∧
      ∃ x ∈ (hT.toSylow : Subgroup ↥H), ∃ u : ↥H, g = ⁅x, u⁆} ≤ D.comap H.subtype := by
    rw [closure_le]
    rintro g ⟨hg, a, ha, u, rfl⟩
    have haT : (a : G) ∈ T := by
      rw [IsSylowOf.coe_toSylow] at ha
      exact ha
    have hgT : ((⁅a, u⁆ : ↥H) : G) ∈ T := by
      rw [IsSylowOf.coe_toSylow] at hg
      exact hg
    have e0 : ((⁅a, u⁆ : ↥H) : G) = ⁅(a : G), (u : G)⁆ := rfl
    rw [e0] at hgT
    show ⁅(a : G), (u : G)⁆ ∈ D
    have e1 : ⁅(a : G), (u : G)⁆ = (a : G)⁻¹⁻¹ * ((u : G)⁻¹⁻¹ * (a : G)⁻¹ * (u : G)⁻¹) := by
      simp only [commutatorElement_def, inv_inv]
      group
    rw [e1]
    refine hF _ (T.inv_mem haT) _ (H.inv_mem u.2) ?_
    have e2 : (u : G)⁻¹⁻¹ * (a : G)⁻¹ * (u : G)⁻¹ = (a : G)⁻¹ * ⁅(a : G), (u : G)⁆ := by
      simp only [commutatorElement_def, inv_inv]
      group
    rw [e2]
    exact T.mul_mem (T.inv_mem haT) hgT
  exact hle hmem

theorem fusIn_of_le {D T H : Subgroup G} (hTH : T ≤ H) (h : T ⊓ ⁅H, H⁆ ≤ D) : FusIn D T H := by
  intro y hy k hk hyk
  refine h ⟨T.mul_mem (T.inv_mem hy) hyk, ?_⟩
  have e : y⁻¹ * (k⁻¹ * y * k) = ⁅y⁻¹, k⁻¹⁆ := by
    simp only [commutatorElement_def, inv_inv]; group
  rw [e]
  exact Subgroup.commutator_mem_commutator (H.inv_mem (hTH hy)) (H.inv_mem hk)

theorem fusIn_alperin (S : Sylow p G) {D P : Subgroup G} (hP : P ≤ S) {g : G}
    (hg : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ S)
    (hQ : ∀ Q : Subgroup G, CFSG.RankTwoShapes.IsAlperinSubgroup p (S : Subgroup G) Q →
      Nat.card P ≤ Nat.card Q → ∀ y ∈ Q, ∀ n ∈ normalizer (Q : Set G), y⁻¹ * (n⁻¹ * y * n) ∈ D) :
    ∀ y ∈ P, y⁻¹ * (g⁻¹ * y * g) ∈ D := by
  have hdec : ∀ c : G, CFSG.RankTwoShapes.AlperinDecomposition p (S : Subgroup G) P c →
      ∀ y ∈ P, y⁻¹ * (c⁻¹ * y * c) ∈ D := by
    intro c hc
    induction hc with
    | one => intro y _; simp
    | @step c n Q hc hQ' hPQ hn ih =>
      intro y hy
      have hyc : c⁻¹ * y * c ∈ Q := by
        apply hPQ
        refine ⟨y, hy, ?_⟩
        simp [MulAut.conj_apply]
      have hcard : Nat.card P ≤ Nat.card Q := by
        calc Nat.card P = Nat.card (P.map (MulAut.conj c⁻¹).toMonoidHom) :=
              (Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective).symm
          _ ≤ Nat.card Q := Subgroup.card_le_of_le hPQ
      have h1 := ih y hy
      have h2 := hQ Q hQ' hcard _ hyc n hn
      have e : y⁻¹ * ((c * n)⁻¹ * y * (c * n)) =
          (y⁻¹ * (c⁻¹ * y * c)) * ((c⁻¹ * y * c)⁻¹ * (n⁻¹ * (c⁻¹ * y * c) * n)) := by group
      rw [e]
      exact D.mul_mem h1 h2
  obtain ⟨c, hc, hcg⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S hP hg
  intro y hy
  rw [← hcg y hy]
  exact hdec c hc y hy

theorem map_conj_ne_top {H : Subgroup G} (hH : H ≠ ⊤) (g : G) :
    H.map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
  intro h
  apply hH
  rw [eq_top_iff]
  intro x _
  have hx : (MulAut.conj g) x ∈ H.map (MulAut.conj g).toMonoidHom := by rw [h]; exact mem_top _
  obtain ⟨y, hy, e⟩ := hx
  have : y = x := (MulAut.conj g).injective e
  rw [← this]; exact hy

theorem le_of_no_normal_pSubgroup (S : Sylow p G)
    (hnp : ∀ Q : Subgroup G, IsPGroup p Q → Q ≠ ⊥ → normalizer (Q : Set G) ≠ ⊤)
    (hind : ∀ H T : Subgroup G, H ≠ ⊤ → IsSylowOf p H T → T ⊓ ⁅H, H⁆ ≤ ⁅H ⊓ nK T, H ⊓ nK T⁆) :
    (S : Subgroup G) ⊓ commutator G ≤ ⁅nK (S : Subgroup G), nK (S : Subgroup G)⁆ := by
  set D := ⁅nK (S : Subgroup G), nK (S : Subgroup G)⁆ with hD
  by_cases hS1 : (S : Subgroup G) = ⊥
  · rw [hS1]; exact inf_le_left.trans bot_le
  have hSp : IsPGroup p (S : Subgroup G) := S.isPGroup'
  have hAlpQ : ∀ Q : Subgroup G, CFSG.RankTwoShapes.IsAlperinSubgroup p (S : Subgroup G) Q →
      normalizer (Q : Set G) ≠ ⊤ ∧
        IsSylowOf p (normalizer (Q : Set G)) ((S : Subgroup G) ⊓ normalizer (Q : Set G)) := by
    intro Q hQ
    have hQ1 : Q ≠ ⊥ := by
      rintro rfl
      apply hS1
      rw [eq_bot_iff]
      intro s hs
      refine hQ.2.2.1 (Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, hs⟩)
      intro h hh
      rw [SetLike.mem_coe, mem_bot] at hh
      rw [hh, one_mul, mul_one]
    refine ⟨hnp Q (hSp.to_le hQ.1) hQ1, inf_le_right, hSp.to_le inf_le_left, ?_⟩
    have := hQ.2.1
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out] at this
    exact this
  have key : ∀ k : ℕ, ∀ T : Subgroup G, T ≤ S → Nat.card S - Nat.card T = k →
      ∀ H : Subgroup G, H ≠ ⊤ → IsSylowOf p H T → FusIn D T H := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro T hTS hk H hH hT
    have hcardTS : Nat.card T ≤ Nat.card (S : Subgroup G) := Subgroup.card_le_of_le hTS
    have hAlp : ∀ Q : Subgroup G, CFSG.RankTwoShapes.IsAlperinSubgroup p (S : Subgroup G) Q →
        Nat.card T < Nat.card Q → ∀ y ∈ Q, ∀ n ∈ normalizer (Q : Set G),
          y⁻¹ * (n⁻¹ * y * n) ∈ D := by
      intro Q hQ hcard y hy n hn
      obtain ⟨hNQ, hsyl⟩ := hAlpQ Q hQ
      have hQT' : Q ≤ (S : Subgroup G) ⊓ normalizer (Q : Set G) := le_inf hQ.1 le_normalizer
      have hc1 : Nat.card Q ≤ Nat.card ((S : Subgroup G) ⊓ normalizer (Q : Set G) : Subgroup G) :=
        Subgroup.card_le_of_le hQT'
      have hc2 : Nat.card ((S : Subgroup G) ⊓ normalizer (Q : Set G) : Subgroup G) ≤
          Nat.card (S : Subgroup G) := Subgroup.card_le_of_le inf_le_left
      have hF := ih (Nat.card (S : Subgroup G) -
          Nat.card ((S : Subgroup G) ⊓ normalizer (Q : Set G) : Subgroup G)) (by omega) _
        inf_le_left rfl _ hNQ hsyl
      have hyn : n⁻¹ * y * n ∈ Q := (Subgroup.mem_normalizer_iff''.mp hn y).mp hy
      exact hF y (hQT' hy) n hn (hQT' hyn)
    by_cases hTS' : T = S
    ·
      subst hTS'
      refine fusIn_of_le hT.1 ((hind H _ hH hT).trans ?_)
      exact Subgroup.commutator_mono inf_le_right inf_le_right
    have hTlt : T < S := lt_of_le_of_ne hTS hTS'
    by_cases hT1 : T = ⊥
    · intro y hy h _ _
      rw [hT1, mem_bot] at hy
      subst hy
      simp
    have hTp : IsPGroup p T := hT.2.1
    have hK1 : kLowInfty T ≠ ⊥ := kLowInfty_ne_bot hTp hT1
    have hKp : IsPGroup p (kLowInfty T) := hTp.to_le (kLowInfty_le' T)
    have hH2 : nK T ≠ ⊤ := hnp _ hKp hK1
    have hTH1 : T ≤ H ⊓ nK T := le_inf hT.1 (le_nK T)
    have hT1syl : IsSylowOf p (H ⊓ nK T) T := hT.mono hTH1 inf_le_left
    suffices hF1 : FusIn D T (H ⊓ nK T) by
      have h1 := hind H T hH hT
      have h2 := inf_commutator_le_of_fusIn hT1syl hF1
      exact fusIn_of_le hT.1 fun x hx => h2 ⟨hx.1, h1 hx⟩
    have hTP0 : T < (S : Subgroup G) ⊓ nK T := by
      refine lt_of_lt_of_le (lt_inf_normalizer hSp hTlt) (inf_le_inf_left _ ?_)
      exact CFSG.GH74.GLS.Stage2.Signalizer.L53.normalizer_le_kLowInfty T
    obtain ⟨T2, hT2, hP0T2⟩ := exists_isSylowOf_le (hSp.to_le (inf_le_left :
      (S : Subgroup G) ⊓ nK T ≤ S)) (inf_le_right : (S : Subgroup G) ⊓ nK T ≤ nK T)
    obtain ⟨g, -, hg⟩ := (IsSylowOf.top S).exists_conj_le le_top hT2.2.1
    have hT2g : T2.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
      rintro _ ⟨y, hy, rfl⟩
      have := hg y hy
      simpa [MulAut.conj_apply] using this
    have hcard1 : Nat.card T < Nat.card ((S : Subgroup G) ⊓ nK T : Subgroup G) :=
      Subgroup.card_lt_of_lt hTP0
    have hcard2 : Nat.card ((S : Subgroup G) ⊓ nK T : Subgroup G) ≤
        Nat.card (T2.map (MulAut.conj g⁻¹).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
      exact Subgroup.card_le_of_le hP0T2
    have hcard3 : Nat.card (T2.map (MulAut.conj g⁻¹).toMonoidHom) ≤ Nat.card (S : Subgroup G) :=
      Subgroup.card_le_of_le hT2g
    have hi : ∀ y ∈ (S : Subgroup G) ⊓ nK T, y⁻¹ * (g⁻¹ * y * g) ∈ D := by
      refine fusIn_alperin S inf_le_left ?_ fun Q hQ hcQ => hAlp Q hQ (lt_of_lt_of_le hcard1 hcQ)
      exact (map_mono hP0T2).trans hT2g
    have hii := ih (Nat.card (S : Subgroup G) - Nat.card (T2.map (MulAut.conj g⁻¹).toMonoidHom))
      (by omega) _ hT2g rfl _ (map_conj_ne_top hH2 g⁻¹) (hT2.map_conj g⁻¹)
    intro z hz c hc hcz
    have hz0 : z ∈ (S : Subgroup G) ⊓ nK T := hTP0.le hz
    have hcz0 : c⁻¹ * z * c ∈ (S : Subgroup G) ⊓ nK T := hTP0.le hcz
    have h1 := hi z hz0
    have h2 := hi _ hcz0
    have h3 : (g⁻¹ * z * g)⁻¹ * ((g⁻¹ * c * g)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * c * g)) ∈ D := by
      refine hii _ ⟨z, hP0T2 hz0, by simp [MulAut.conj_apply]⟩ _
        ⟨c, hc.2, by simp [MulAut.conj_apply]⟩ ?_
      refine ⟨c⁻¹ * z * c, hP0T2 hcz0, ?_⟩
      simp [MulAut.conj_apply]; group
    have e : z⁻¹ * (c⁻¹ * z * c) = (z⁻¹ * (g⁻¹ * z * g)) *
        ((g⁻¹ * z * g)⁻¹ * ((g⁻¹ * c * g)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * c * g))) *
        ((c⁻¹ * z * c)⁻¹ * (g⁻¹ * (c⁻¹ * z * c) * g))⁻¹ := by group
    rw [e]
    exact D.mul_mem (D.mul_mem h1 h3) (D.inv_mem h2)
  have hFS : FusIn D S ⊤ := by
    intro y hy h _ hyh
    refine fusIn_alperin S (P := zpowers y) (zpowers_le.mpr hy) ?_ ?_ y (mem_zpowers y)
    · rw [MonoidHom.map_zpowers, zpowers_le]
      simpa [MulAut.conj_apply] using hyh
    · intro Q hQ _ y hy n hn
      obtain ⟨hNQ, hsyl⟩ := hAlpQ Q hQ
      have hQT' : Q ≤ (S : Subgroup G) ⊓ normalizer (Q : Set G) := le_inf hQ.1 le_normalizer
      have hF := key _ _ inf_le_left rfl _ hNQ hsyl
      have hyn : n⁻¹ * y * n ∈ Q := (Subgroup.mem_normalizer_iff''.mp hn y).mp hy
      exact hF y (hQT' hy) n hn (hQT' hyn)
  have := inf_commutator_le_of_fusIn (IsSylowOf.top S) hFS
  rwa [← _root_.commutator_def] at this

end Fusion

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

end
