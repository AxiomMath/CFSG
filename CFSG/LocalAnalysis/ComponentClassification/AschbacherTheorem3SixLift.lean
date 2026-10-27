module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixDefs
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixNormal

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem IsBenderType.fusion {B : Subgroup X} {n : ℕ} (h : IsBenderType B n) :
    fusionIsBenderGroup B := by
  rcases h with ⟨hn, he⟩ | ⟨m, hm, -, he⟩ | ⟨hn, he⟩
  · exact Or.inl ⟨n, hn, he⟩
  · exact Or.inr (Or.inr ⟨m, hm, he⟩)
  · exact Or.inr (Or.inl ⟨n, hn, he⟩)

theorem IsBenderType.isSimpleGroup {B : Subgroup X} {n : ℕ} (h : IsBenderType B n) :
    IsSimpleGroup B :=
  CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup h.fusion

theorem not_isPGroup_of_fusionBenderBorel {M : Type*} [Group M] [Finite M] {q k : ℕ}
    (hB : fusionBenderBorel M q k) : ¬ IsPGroup 2 M := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 M))
  have hQ : (Q : Subgroup M) = ⊤ := (Q.is_maximal' (h2.to_subgroup ⊤) le_top).symm
  apply (hB Q).1.1
  rw [hQ]
  exact (Subgroup.normalizer_eq_top_iff (H := (⊤ : Subgroup M))).mpr inferInstance

theorem IsBenderType.not_isPGroup {B : Subgroup X} {n : ℕ} (h : IsBenderType B n) :
    ¬ IsPGroup 2 B := by
  intro h2
  rcases h with ⟨hn, ⟨e⟩⟩ | ⟨m, hm, -, ⟨e⟩⟩ | ⟨hn, ⟨e⟩⟩
  · have : Finite PSL(2, GaloisField 2 n) := Finite.of_equiv _ e.toEquiv
    exact not_isPGroup_of_fusionBenderBorel (CFSG.Open.bender_psl2_borel_full n hn)
      (h2.of_equiv e)
  · have : Finite (Sz m) := Finite.of_equiv _ e.toEquiv
    exact not_isPGroup_of_fusionBenderBorel (CFSG.Open.bender_suzuki_borel_full m hm)
      (h2.of_equiv e)
  · have : Finite (PSU3 2 n) := Finite.of_equiv _ e.toEquiv
    exact not_isPGroup_of_fusionBenderBorel (CFSG.Open.bender_psu3_borel_full n hn)
      (h2.of_equiv e)

theorem IsBenderType.ne_bot {B : Subgroup X} {n : ℕ} (h : IsBenderType B n) : B ≠ ⊥ := by
  have : IsSimpleGroup B := h.isSimpleGroup
  intro hbot
  have : Nontrivial B := IsSimpleGroup.toNontrivial
  rw [hbot] at this
  exact (not_nontrivial_iff_subsingleton.mpr (by infer_instance)) this

theorem le_of_isSylowOf_of_le_normalizer {E S K : Subgroup X} (hS : IsSylowOf 2 S K)
    (hE : IsPGroup 2 E) (hEK : E ≤ K) (hN : K ≤ Subgroup.normalizer (E : Set X)) : E ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : IsPGroup 2 (S ⊔ E : Subgroup X) :=
    IsPGroup.to_sup_of_normal_right' hS.isPGroup hE (hS.le.trans hN)
  have heq := hS.eq_of_le le_sup_left (sup_le hS.le hEK) hsup
  rw [← heq]
  exact le_sup_right

namespace Conf46

variable {G T S Q H : Subgroup X} {g : X}

theorem le_normalizer_of_forall (c : Conf46 G T S Q H g)
    (h : ∀ x ∈ G, rightConjugate T x ≤ S) :
    G ≤ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) := by
  have hmem : ∀ x ∈ G, rightConjugate T x ≤ T ⊔ rightConjugate T g := fun x hx => by
    rw [← c.weakClosure]
    exact rightConjugate_le_relativeWeakClosure hx (h x hx)
  intro y hy
  rw [← rightConjugate_eq_self_iff]
  apply Subgroup.eq_of_le_of_card_ge _ (by rw [rightConjugate_card])
  unfold rightConjugate
  rw [Subgroup.map_sup]
  refine sup_le (hmem y hy) ?_
  change rightConjugate (rightConjugate T g) y ≤ _
  rw [rightConjugate_mul]
  exact hmem _ (G.mul_mem c.mem hy)

theorem normalizer_W_of_omegaOne (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤)
    (hO : CFSG.oddCore G = ⊥) (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hV : G ≤ Subgroup.normalizer
      ((omegaOne (T ⊔ rightConjugate T g) : Subgroup X) : Set X)) :
    G ⊔ T ≤ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := T ⊔ rightConjugate T g with hWdef
  set V := omegaOne W with hVdef
  have hWab := c.isMulCommutative_W
  have hWw : relativeWeakClosure G T S = W := c.weakClosure
  have hTW : T ≤ W := le_sup_left
  have hWV : W ≤ Subgroup.centralizer (V : Set X) := fun w hw =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      congrArg Subtype.val (hWab.is_comm.comm ⟨v, omegaOne_le W hv⟩ ⟨w, hw⟩)
  have hTV : T ≤ Subgroup.centralizer (V : Set X) := hTW.trans hWV
  have hGn : G.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer c.frame.le_normalizer
  have hVn : V.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le hV (hTV.trans (Subgroup.centralizer_le_normalizer _))
  set C := Subgroup.centralizer (V : Set X) with hCdef
  have hCn : C.Normal := inferInstance
  set CG := G ⊓ C with hCGdef
  have hCGn : CG.Normal := inferInstance
  obtain ⟨⟨u, huU⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp c.omegaOne_ne_bot
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huV : u ∈ V := omegaOne_mono hTW huU
  have hCH : C ≤ H := fun x hx =>
    c.hyp43.centralizer_le c.frame (omegaOne_le T huU) hu1'
      ⟨htop ▸ Subgroup.mem_top x,
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huV) hx⟩
  have hgH : g ∉ H := c.hyp45.facts.1
  have hCGlt : CG < G :=
    lt_of_le_of_ne inf_le_left fun h => hgH (hCH (h ▸ c.mem : g ∈ CG).2)
  have hcard := card_sup_lt c.frame hCGlt (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hCeq : CG ⊔ T = C := by
    apply le_antisymm (sup_le inf_le_right hTV)
    intro x hx
    obtain ⟨t, ht, h, hh, rfl⟩ := c.frame.mem_sup_iff.mp (htop ▸ Subgroup.mem_top x)
    have hhC : h ∈ C := by simpa using C.mul_mem (C.inv_mem (hTV ht)) hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left ⟨hh, hhC⟩)
  have hS₁ := c.sylowFrame.restrict (inf_le_left : CG ≤ G)
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have h43₁ := c.hyp43.restrict (inf_le_left : CG ≤ G)
  have hO₁ : CFSG.oddCore CG = ⊥ :=
    oddCore_eq_bot_of_le inf_le_left (by rw [Subgroup.normalizer_eq_top]; exact le_top) hO
  set S₁ := S ⊓ (CG ⊔ T)
  set W₁ := relativeWeakClosure CG T S₁ with hW₁def
  have hTS₁ : T ≤ S₁ := le_inf c.le_S le_sup_right
  have hW₁W : W₁ ≤ W := by
    rw [hW₁def, relativeWeakClosure_le_iff]
    intro x hx hle
    rw [← hWw]
    exact rightConjugate_le_relativeWeakClosure hx.1 (hle.trans inf_le_left)
  have hWN : W ≤ Subgroup.normalizer (T : Set X) :=
    sup_le Subgroup.le_normalizer c.le_normalizer
  obtain ⟨g₁, hg₁, hW₁eq⟩ : ∃ g₁ ∈ CG, W₁ = T ⊔ rightConjugate T g₁ := by
    by_cases hall : ∀ x ∈ CG, rightConjugate T x ≤ S₁ → rightConjugate T x = T
    · refine ⟨1, CG.one_mem, ?_⟩
      rw [rightConjugate_one, sup_idem]
      apply le_antisymm
      · rw [hW₁def, relativeWeakClosure_le_iff]
        exact fun x hx hle => (hall x hx hle).le
      · exact subgroup_le_relative_weak_closure _ _ _ hTS₁
    · push Not at hall
      obtain ⟨x, hx, hle, hne⟩ := hall
      refine ⟨x, hx, ?_⟩
      have hxW : rightConjugate T x ≤ W := by
        rw [← hWw]
        exact rightConjugate_le_relativeWeakClosure hx.1 (hle.trans inf_le_left)
      have hxSH : rightConjugate T x ≤ S ⊓ H := le_inf (hxW.trans c.W_le_S)
        (hxW.trans (c.hyp45.W_le.trans inf_le_left))
      have hinf := (lemma_4_4_two c.frame c.hyp43 c.isPGroup_S c.le_S hx.1 hxSH hne).2.1
      have hsup : T ⊔ rightConjugate T x = W := by
        apply Subgroup.eq_of_le_of_card_ge (sup_le hTW hxW)
        rw [c.hyp45.card_W, card_sup_of_le_normalizer (hxW.trans hWN) hinf,
          rightConjugate_card]
      apply le_antisymm (hW₁W.trans hsup.ge)
      exact sup_le (subgroup_le_relative_weak_closure _ _ _ hTS₁)
        (rightConjugate_le_relativeWeakClosure hx hle)
  have hg₁N : rightConjugate T g₁ ≤ Subgroup.normalizer (T : Set X) :=
    (le_sup_right.trans hW₁eq.ge).trans (hW₁W.trans hWN)
  have hconcl := IH X CG T S₁ (Q ⊓ (CG ⊔ T)) (H ⊓ (CG ⊔ T)) g₁ hcard hS₁ h43₁ c.ne_bot hO₁ hg₁
    hW₁eq hg₁N
  rcases hconcl with hm | hN | hB
  · have := c.pRank_lt
    omega
  ·
    rw [hCeq] at hN
    have hW₁C : W₁ ≤ C := hW₁W.trans hWV
    have hW₁2 : IsPGroup 2 W₁ := c.isPGroup_S.to_le (hW₁W.trans c.W_le_S)
    have hSC : IsSylowOf 2 (S ⊓ C) C := c.sylowFrame.sylow.inf_of_le_normalizer
      (by rw [htop]; exact le_top) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    have hconj : ∀ x ∈ G, rightConjugate T x ≤ S := by
      intro x _
      have hle : rightConjugate W₁ x ≤ S ⊓ C := by
        refine le_of_isSylowOf_of_le_normalizer hSC (hW₁2.map _) ?_ ?_
        · intro y hy
          have h1 := rightConjugate_le_rightConjugate hW₁C x hy
          rwa [(rightConjugate_eq_self_iff C x).mpr
            (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x)] at h1
        · intro y hy
          rw [← rightConjugate_normalizer]
          have h1 := rightConjugate_le_rightConjugate hN x
          rw [(rightConjugate_eq_self_iff C x).mpr
            (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x)] at h1
          exact h1 hy
      exact (rightConjugate_le_rightConjugate (le_sup_left.trans hW₁eq.ge) x).trans
        (hle.trans inf_le_left)
    exact sup_le (c.le_normalizer_of_forall hconj) (hTW.trans Subgroup.le_normalizer)
  · exfalso
    obtain ⟨n, -, -, -, -, -, hBen, hTel, -⟩ := hB
    have hTV' : T ≤ V := (le_omegaOne hTel.2).trans (omegaOne_mono hTW)
    have hcomm : ⁅T, CG⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTV'))
    exact hBen.ne_bot hcomm

end Conf46

end CFSG.ComponentClassification.AschbacherTheorem3
