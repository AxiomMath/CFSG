module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15VertexTwin
public import CFSG.ClassicalInvolution.ModelFacts.Orth15SylowFrame
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
import CFSG.ClassicalInvolution.Asc77.WP3FrameChain
import CFSG.ClassicalInvolution.Asc77.AscE187Img

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore)

section Residual

variable (p : ℕ) [Fact p.Prime]

structure TwinSmallInner : Prop where
  psp : p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSp 2 p e → TwinInnerAlpha p e .PSp 2
  psl : p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSL 4 p e → TwinInnerAlpha p e .PSL 4
  psu : p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSU 4 p e → TwinInnerAlpha p e .PSU 4
  d4 : p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .POmegaPlus 4 p e →
    TwinInnerAlpha p e .POmegaPlus 4

structure TwinSmallOuter : Prop where
  psp : p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSp 2 p e → TwinOuterAlpha p e .PSp 2
  psl : p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSL 4 p e → TwinOuterAlpha p e .PSL 4
  psu : p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSU 4 p e → TwinOuterAlpha p e .PSU 4
  d4 : p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .POmegaPlus 4 p e →
    TwinOuterAlpha p e .POmegaPlus 4

variable {p}

theorem twinInnerAlpha_of_shape (hres : TwinSmallInner p) (hp2 : p ≠ 2) {e : ℕ}
    (hq : 5 ≤ p ^ e) {t : StatedLieTag} {n : ℕ} (hadm : StatedLieAdmissible t n p e)
    (hsh : TwinShape t n) : TwinInnerAlpha p e t n := by
  rcases hsh with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact twinInnerAlpha_odd hp2 hq hadm
  · rcases Nat.lt_or_ge n 5 with h | h
    · obtain rfl : n = 4 := by omega
      exact hres.d4 hp2 e hq hadm
    · exact twinInnerAlpha_plus hp2 hq hadm h
  · exact twinInnerAlpha_minus hp2 hq hadm
  · exact hres.psp hp2 e hq hadm
  · exact hres.psl hp2 e hq hadm
  · exact hres.psu hp2 e hq hadm

theorem twinOuterAlpha_of_shape (hres : TwinSmallOuter p) (hp2 : p ≠ 2) {e : ℕ}
    (hq : 5 ≤ p ^ e) {t : StatedLieTag} {n : ℕ} (hadm : StatedLieAdmissible t n p e)
    (hsh : TwinShape t n) : TwinOuterAlpha p e t n := by
  rcases hsh with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact twinOuterAlpha_odd hp2 hq hadm
  · rcases Nat.lt_or_ge n 5 with h | h
    · obtain rfl : n = 4 := by omega
      exact hres.d4 hp2 e hq hadm
    · exact twinOuterAlpha_plus hp2 hq hadm h
  · exact twinOuterAlpha_minus hp2 hq hadm
  · exact hres.psp hp2 e hq hadm
  · exact hres.psl hp2 e hq hadm
  · exact hres.psu hp2 e hq hadm

end Residual

@[expose] def G2D4VertexExcl (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (hΩ : HypOmegaMod p f Ω),
    (∀ M ∈ Ω, AEmpty Ω M) → ∀ c : G, IsPGroup 2 (Subgroup.zpowers c) →
      ∀ (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card),
        (D.tag j = .G2 ∨ D.tag j = .trialityD4) →
          ∀ (M M' : Subgroup G) (b : G), M ∈ tqMembers Ω c → M' ∈ tqMembers Ω c →
            IsClassicalMember p f M b → IsClassicalMember p f M' b → M' ≠ M →
              modOdd c (exactCore c M) ≤
                (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range →
              modOdd c (exactCore c M') ≤
                (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range →
                False


section Induced

variable {G : Type} [Group G] [Finite G] {c : G}

theorem eq_of_oddQuotMk_eq {B : Subgroup G} (hB : IsElemAbelian 2 B) {d₁ d₂ : G} (hd₁ : d₁ ∈ B)
    (hd₂ : d₂ ∈ B) (h₁ : d₁ ∈ Subgroup.centralizer ({c} : Set G))
    (h₂ : d₂ ∈ Subgroup.centralizer ({c} : Set G))
    (h : oddQuotMk c ⟨d₁, h₁⟩ = oddQuotMk c ⟨d₂, h₂⟩) : d₁ = d₂ := by
  have hsq : (⟨d₁, h₁⟩ * ⟨d₂, h₂⟩ : ↥(Subgroup.centralizer ({c} : Set G))) *
      (⟨d₁, h₁⟩ * ⟨d₂, h₂⟩) = 1 :=
    Subtype.ext (Lemma52Proof.mul_self_eq_one_of_mem hB (B.mul_mem hd₁ hd₂))
  have hd2 : d₂ * d₂ = 1 := Lemma52Proof.mul_self_eq_one_of_mem hB hd₂
  have h1 : oddQuotMk c (⟨d₁, h₁⟩ * ⟨d₂, h₂⟩) = 1 := by
    rw [map_mul, h, ← map_mul]
    have : (⟨d₂, h₂⟩ * ⟨d₂, h₂⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 := Subtype.ext hd2
    rw [this, map_one]
  have h3 : d₁ * d₂ = 1 := congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h1)
  rw [eq_inv_of_mul_eq_one_left h3]
  exact inv_eq_of_mul_eq_one_right hd2

omit [Finite G] in
theorem inducedImage_modOdd_closure_le {S : Set G} (hS : S ⊆ Subgroup.centralizer ({c} : Set G))
    (L : Subgroup (OddQuot c)) (T : Subgroup ↥(inducedAutOn L))
    (hgen : ∀ (s : G) (hs : s ∈ S),
      ∃ hn : oddQuotMk c ⟨s, hS hs⟩ ∈ Subgroup.normalizer (L : Set (OddQuot c)),
        toInducedAutOn L ⟨oddQuotMk c ⟨s, hS hs⟩, hn⟩ ∈ T) :
    inducedImage L (modOdd c (Subgroup.closure S)) ≤ T := by
  have hCl : Subgroup.closure S ≤ Subgroup.centralizer ({c} : Set G) :=
    (Subgroup.closure_le _).mpr hS
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨k, hk, hkm⟩ := mem_modOdd_iff.mp (Subgroup.mem_subgroupOf.mp hm)
  have key : ∀ (g : G) (hg : g ∈ Subgroup.closure S),
      ∃ hn : oddQuotMk c ⟨g, hCl hg⟩ ∈ Subgroup.normalizer (L : Set (OddQuot c)),
        toInducedAutOn L ⟨oddQuotMk c ⟨g, hCl hg⟩, hn⟩ ∈ T := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact hgen s hs
    | one =>
      have h1 : oddQuotMk c ⟨1, hCl (Subgroup.one_mem _)⟩ = 1 := map_one _
      refine ⟨by rw [h1]; exact Subgroup.one_mem _, ?_⟩
      have h2 : (⟨oddQuotMk c ⟨1, hCl (Subgroup.one_mem _)⟩, by rw [h1]; exact Subgroup.one_mem _⟩ :
          ↥(Subgroup.normalizer (L : Set (OddQuot c)))) = 1 := Subtype.ext h1
      rw [h2, map_one]
      exact T.one_mem
    | mul a b ha hb iha ihb =>
      obtain ⟨hna, hTa⟩ := iha
      obtain ⟨hnb, hTb⟩ := ihb
      have hab : oddQuotMk c ⟨a * b, hCl (Subgroup.mul_mem _ ha hb)⟩ =
          oddQuotMk c ⟨a, hCl ha⟩ * oddQuotMk c ⟨b, hCl hb⟩ := map_mul (oddQuotMk c)
            (⟨a, hCl ha⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ⟨b, hCl hb⟩
      have hn : oddQuotMk c ⟨a * b, hCl (Subgroup.mul_mem _ ha hb)⟩ ∈
          Subgroup.normalizer (L : Set (OddQuot c)) := by
        rw [hab]
        exact Subgroup.mul_mem _ hna hnb
      refine ⟨hn, ?_⟩
      have h2 : (⟨oddQuotMk c ⟨a * b, hCl (Subgroup.mul_mem _ ha hb)⟩, hn⟩ :
          ↥(Subgroup.normalizer (L : Set (OddQuot c)))) =
            ⟨oddQuotMk c ⟨a, hCl ha⟩, hna⟩ * ⟨oddQuotMk c ⟨b, hCl hb⟩, hnb⟩ := Subtype.ext hab
      rw [h2, map_mul]
      exact T.mul_mem hTa hTb
    | inv a ha iha =>
      obtain ⟨hna, hTa⟩ := iha
      have hab : oddQuotMk c ⟨a⁻¹, hCl (Subgroup.inv_mem _ ha)⟩ =
          (oddQuotMk c ⟨a, hCl ha⟩)⁻¹ :=
        map_inv (oddQuotMk c) (⟨a, hCl ha⟩ : ↥(Subgroup.centralizer ({c} : Set G)))
      have hn : oddQuotMk c ⟨a⁻¹, hCl (Subgroup.inv_mem _ ha)⟩ ∈
          Subgroup.normalizer (L : Set (OddQuot c)) := by
        rw [hab]
        exact Subgroup.inv_mem _ hna
      refine ⟨hn, ?_⟩
      have h2 : (⟨oddQuotMk c ⟨a⁻¹, hCl (Subgroup.inv_mem _ ha)⟩, hn⟩ :
          ↥(Subgroup.normalizer (L : Set (OddQuot c)))) = ⟨oddQuotMk c ⟨a, hCl ha⟩, hna⟩⁻¹ :=
        Subtype.ext hab
      rw [h2, map_inv]
      exact T.inv_mem hTa
  obtain ⟨hn, hT⟩ := key (k : G) hk
  have h2 : m = ⟨oddQuotMk c ⟨(k : G), hCl hk⟩, hn⟩ := Subtype.ext hkm.symm
  rw [h2]
  exact hT

end Induced


section Vertex

variable {p f : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem oddQuotSelf_induced {G : Type} [Group G] [Finite G] (c : G)
    (L : Subgroup (OddQuot c)) :
    ∃ hn : Lemma52Proof.oddQuotSelf c ∈ Subgroup.normalizer (L : Set (OddQuot c)),
      toInducedAutOn L ⟨Lemma52Proof.oddQuotSelf c, hn⟩ = 1 := by
  have hcomm : ∀ y ∈ L, Lemma52Proof.oddQuotSelf c * y = y * Lemma52Proof.oddQuotSelf c :=
    fun y _ => (Lemma52Proof.oddQuotSelf_central c y).symm
  have hn : Lemma52Proof.oddQuotSelf c ∈ Subgroup.normalizer (L : Set (OddQuot c)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : Lemma52Proof.oddQuotSelf c * y * (Lemma52Proof.oddQuotSelf c)⁻¹ = y := by
      rw [← Lemma52Proof.oddQuotSelf_central c y]
      group
    rw [h1]
  exact ⟨hn, Lemma52Proof.toInducedAutOn_eq_one_of_commute L hn hcomm⟩

theorem TwinFrameSettingCore.hyp51At_t_of {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {Ω : Set (Subgroup G)} {K K' J : Subgroup G} {z u t c : G}
    (hs : TwinFrameSettingCore p f Ω K K' J z u t) (hc : c = t ∨ c = t * z)
    (hv : ∀ (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card),
      modOdd c (exactCore c K) ≤
        (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range →
      modOdd c (exactCore c K') ≤
        (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range →
      MovedByAll (Subgroup.closure ({z, u, t} : Set G)) c
        (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range →
      ∃ (hzC : z ∈ Subgroup.centralizer ({c} : Set G)) (R R' : Subgroup (compModel D j).K)
        (x x' : (compModel D j).K),
        TwinPairOn (D.tag j) (compModel D j)
          (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) R R' x x' ∧
        R.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
          modOdd c (exactCore c K) ∧
        R'.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
          modOdd c (exactCore c K') ∧
        secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j x =
          oddQuotMk c ⟨z, hzC⟩ ∧
        TwinInnerAlpha p (D.exp j) (D.tag j) (D.rank j)) :
    Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := by
  have hp : p ≠ 2 := hs.odd
  have hq : 5 ≤ p ^ f := hs.five
  have hΩ := hs.hyp
  have hd := hs.frame
  have hK : K ∈ Ω := hd.mem
  have hK'Ω : K' ∈ Ω := hd.hK'.1
  have hz := hd.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hd.hK'
  have hcK : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hK hz
  have hcK' : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ hK'Ω hzK'
  have hBab := twinFrame_isElemAbelian hp hΩ hd
  have hzB : z ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hcB : c ∈ Subgroup.closure ({z, u, t} : Set G) := mem_closure_of_eq_or_eq_mul hc
  have hc2 := hs.isPGroup_zpowers_c hc
  have hc1 := hs.c_ne_one hc
  have hzc : z ≠ c := hs.z_ne_c hc
  have hnonab : ∃ x y : G, x * y ≠ y * x := exists_noncomm_of_isClassicalMember hcK
  have hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hnonab hc1
  have hMK : K ∈ tqMembers Ω c := ⟨hK, hs.tq_c_K hc⟩
  have hMK' : K' ∈ tqMembers Ω c := ⟨hK'Ω, hs.tq_c_K' hc⟩
  have hne : K' ≠ K := hd.hne
  refine FrameVertex.hyp51At_of_witness_alpha hp hq hΩ.conjInvariant hΩ.classical hs.below hc2
    hnc hBab hcB hc1 hzB hz.ne_one hzc hMK hcK ?_
  intro D j hMj hmov
  have hM'j := vertexTwin_mem hΩ hc2 hBab hcB hc1 hzB hz.ne_one hzc hMK hMK' hcK' D j hmov
  obtain ⟨hzC, R, R', x, x', hpair, hRM, hR'M, hψx, hTI⟩ := hv D j hMj hM'j hmov
  set ψ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j with hψdef
  have huC : u ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hs.comm_u_c hc)
  have htC : t ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hs.comm_t_c hc)
  have hsup : oddQuotMk c ⟨u, huC⟩ ∈ R.map ψ ⊔ R'.map ψ := by
    rw [hRM, hR'M]
    exact TwinVertex.oddQuotMk_mem_sup (exactCore_le_centralizer c K)
      (exactCore_le_centralizer c K') (hs.u_mem_exactCore_sup hc) huC
  have hun : oddQuotMk c ⟨u, huC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
    Subgroup.le_normalizer (sup_le (Subgroup.map_le_range ψ R) (Subgroup.map_le_range ψ R') hsup)
  have hu2 : oddQuotMk c ⟨u, huC⟩ * oddQuotMk c ⟨u, huC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨u, huC⟩ * ⟨u, huC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 :=
      Subtype.ext hd.hu2
    rw [this, map_one]
  have hu1 : oddQuotMk c ⟨u, huC⟩ ≠ 1 := by
    intro h
    have h' : oddQuotMk c ⟨u, huC⟩ = oddQuotMk c ⟨1, Subgroup.one_mem _⟩ := by
      rw [h]
      exact (map_one _).symm
    exact hd.hu1 (eq_of_oddQuotMk_eq hBab huB (Subgroup.one_mem _) huC (Subgroup.one_mem _) h')
  have huz : oddQuotMk c ⟨u, huC⟩ ≠ ψ x := by
    rw [hψx]
    intro h
    exact hd.huz (eq_of_oddQuotMk_eq hBab huB hzB huC hzC h)
  have key := hTI (OddQuot c) ψ R R' x x' hpair (oddQuotMk c ⟨u, huC⟩) hun hsup hu2 hu1 huz
  have hψnorm : ∀ y : (compModel D j).K, ψ y ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
    FrameVertex.mem_normalizer_range ψ
  set T : Subgroup ↥(inducedAutOn ψ.range) := Subgroup.closure
    ({toInducedAutOn ψ.range ⟨oddQuotMk c ⟨u, huC⟩, hun⟩,
      toInducedAutOn ψ.range ⟨ψ x, hψnorm x⟩} : Set ↥(inducedAutOn ψ.range)) with hT
  have hS : ({z, u, t} : Set G) ⊆ Subgroup.centralizer ({c} : Set G) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg
    · rw [hg]; exact hzC
    · rw [hg]; exact huC
    · rw [hg]; exact htC
  have hzbar : oddQuotMk c ⟨z, hzC⟩ = ψ x := hψx.symm
  have hgen : ∀ s : G, s ∈ ({z, u, t} : Set G) → ∀ hs' : s ∈ Subgroup.centralizer ({c} : Set G),
      ∃ hn : oddQuotMk c ⟨s, hs'⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)),
        toInducedAutOn ψ.range ⟨oddQuotMk c ⟨s, hs'⟩, hn⟩ ∈ T := by
    intro s hs hs'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with hs | hs | hs
    · subst s
      refine ⟨by rw [hzbar]; exact hψnorm x, ?_⟩
      have h2 : (⟨oddQuotMk c ⟨z, hs'⟩, by rw [hzbar]; exact hψnorm x⟩ :
          ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) = ⟨ψ x, hψnorm x⟩ :=
        Subtype.ext hzbar
      rw [h2]
      exact Subgroup.subset_closure (by simp)
    · subst s
      exact ⟨hun, Subgroup.subset_closure (by simp)⟩
    · subst s
      obtain ⟨hcn, hc1'⟩ := oddQuotSelf_induced c ψ.range
      rcases hc with hc | hc
      · have h1 : oddQuotMk c ⟨t, hs'⟩ = Lemma52Proof.oddQuotSelf c :=
          congrArg (oddQuotMk c) (Subtype.ext hc.symm)
        refine ⟨by rw [h1]; exact hcn, ?_⟩
        have h2 : (⟨oddQuotMk c ⟨t, hs'⟩, by rw [h1]; exact hcn⟩ :
            ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) =
              ⟨Lemma52Proof.oddQuotSelf c, hcn⟩ := Subtype.ext h1
        rw [h2, hc1']
        exact T.one_mem
      · have h1 : oddQuotMk c ⟨t, hs'⟩ = Lemma52Proof.oddQuotSelf c * ψ x := by
          have : (⟨t, hs'⟩ : ↥(Subgroup.centralizer ({c} : Set G))) =
              ⟨c, Lemma52Proof.self_mem_centralizer_singleton c⟩ * ⟨z, hzC⟩ := by
            apply Subtype.ext
            show t = c * z
            rw [hc, mul_assoc, hz.sq, mul_one]
          rw [this, map_mul, ← hzbar]
          rfl
        have hn : oddQuotMk c ⟨t, hs'⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) := by
          rw [h1]
          exact Subgroup.mul_mem _ hcn (hψnorm x)
        refine ⟨hn, ?_⟩
        have h2 : (⟨oddQuotMk c ⟨t, hs'⟩, hn⟩ :
            ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) =
              ⟨Lemma52Proof.oddQuotSelf c, hcn⟩ * ⟨ψ x, hψnorm x⟩ := Subtype.ext h1
        rw [h2, map_mul, hc1', one_mul]
        exact Subgroup.subset_closure (by simp)
  have hψxB : ψ x ∈ modOdd c (Subgroup.closure ({z, u, t} : Set G)) := by
    rw [hψx]
    exact oddQuotMk_mem_modOdd hzB hzC
  refine (congrArg alphaOf (le_antisymm ?_ ?_)).trans key
  · exact inducedImage_modOdd_closure_le hS ψ.range T (fun s hs => hgen s hs (hS hs))
  · refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact ⟨⟨oddQuotMk c ⟨u, huC⟩, hun⟩,
        Subgroup.mem_subgroupOf.mpr (oddQuotMk_mem_modOdd huB huC), rfl⟩
    · rw [hg]
      exact ⟨⟨ψ x, hψnorm x⟩, Subgroup.mem_subgroupOf.mpr hψxB, rfl⟩

theorem twinFrameHyp51t_of (hres : TwinSmallInner p) (hex : G2D4VertexExcl p f) :
    TwinFrameHyp51t p f := by
  intro G _ _ _ Ω K K' J z u t hs
  have main : ∀ c : G, (c = t ∨ c = t * z) →
      Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := by
    intro c hc
    have hp : p ≠ 2 := hs.odd
    have hq : 5 ≤ p ^ f := hs.five
    have hΩ := hs.hyp
    have hd := hs.frame
    have hK : K ∈ Ω := hd.mem
    have hK'Ω : K' ∈ Ω := hd.hK'.1
    have hz := hd.hz
    have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hd.hK'
    have hcK : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hK hz
    have hcK' : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ hK'Ω hzK'
    have hBab := twinFrame_isElemAbelian hp hΩ hd
    have hzB : z ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
    have hcB : c ∈ Subgroup.closure ({z, u, t} : Set G) := mem_closure_of_eq_or_eq_mul hc
    have hc2 := hs.isPGroup_zpowers_c hc
    have hc1 := hs.c_ne_one hc
    have hzc : z ≠ c := hs.z_ne_c hc
    have hMK : K ∈ tqMembers Ω c := ⟨hK, hs.tq_c_K hc⟩
    have hMK' : K' ∈ tqMembers Ω c := ⟨hK'Ω, hs.tq_c_K' hc⟩
    have hne : K' ≠ K := hd.hne
    refine hs.toCore.hyp51At_t_of hc fun D j hMj hM'j hmov => ?_
    have hG2 : D.tag j ≠ .G2 := fun h =>
      hex G Ω hΩ hs.aEmpty c hc2 D j (Or.inl h) K K' z hMK hMK' hcK hcK' hne hMj hM'j
    have hD4 : D.tag j ≠ .trialityD4 := fun h =>
      hex G Ω hΩ hs.aEmpty c hc2 D j (Or.inr h) K K' z hMK hMK' hcK hcK' hne hMj hM'j
    obtain ⟨hzC, R, R', x, x', hpair, hshape, hRM, hR'M, hψx⟩ := vertexTwin hp hq hΩ hc2 hBab
      hcB hc1 hzB hz.ne_one hzc hMK hMK' hcK hcK' hne D j hMj hmov hG2 hD4
    have hexp : D.exp j = f := (D.exp_eq j).resolve_right fun h => hD4 h.1
    have hq' : 5 ≤ p ^ D.exp j := by rw [hexp]; exact hq
    exact ⟨hzC, R, R', x, x', hpair, hRM, hR'M, hψx,
      twinInnerAlpha_of_shape hres hp hq' (D.admissible j) hshape⟩
  exact ⟨main t (Or.inl rfl), main (t * z) (Or.inr rfl)⟩

end Vertex

end CFSG.ClassicalInvolution.Asc77
