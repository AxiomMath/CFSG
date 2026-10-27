module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7Model
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

namespace L257

variable (N : Notation25 hs)

theorem S_le_M : N.S ≤ M := N.tuple.sylow_inf.le.trans inf_le_right

theorem SK_le_S : N.SK ≤ N.S := inf_le_left

theorem SK_le_K : N.SK ≤ N.K := inf_le_right

theorem x_conj_S {s : G} (hs' : s ∈ N.S) : N.x * s * N.x⁻¹ ∈ N.S :=
  (Subgroup.mem_normalizer_iff.mp N.x_mem.2 s).mp hs'

theorem x_conj_S' {s : G} (hs' : s ∈ N.S) : N.x⁻¹ * s * N.x ∈ N.S := by
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ N.x_mem.2) s).mp hs'
  simpa using this

end L257

structure Setup257 (N : Notation25 hs) (n : ℕ) (K₁ K₂ V V' : Subgroup G) (s : G) : Prop where
  K0_eq : N.K0 = N.K
  quasi : CFSG.IsQuasisimple ↥N.K
  model : IsRank2Model257 N.K n
  list : IsRankTwoEvenType N.K
  borel : M ⊓ N.K = N.K ⊓ Subgroup.normalizer (N.SK : Set G)
  pair : IsParabolicPair257 N.K N.SK K₁ K₂
  hV : V = pCoreOf 2 K₁
  hV' : V' = pCoreOf 2 K₂
  s_mem : s ∈ N.S
  swap : CFSG.conjugate K₁ s = K₂

namespace Notation25

variable (N : Notation25 hs)

theorem case2_of_rank2 (hNI : NonIso257) {n : ℕ} (hn : IsRank2Model257 N.K n)
    (hL : ComponentList M N.S N.z N.K) :
    IsRankTwoEvenType N.K ∧ NontrivialOnDynkin M N.S N.K ∧ IsBorelIn (M ⊓ N.K) N.K := by
  obtain ⟨h3, hM11, hL2, -, -⟩ := hNI ↥N.K n hn.1 hn.2
  obtain ⟨-, -, -, -, h⟩ := hL
  rcases h with ⟨hB, -⟩ | h2 | ⟨hm, -⟩ | ⟨⟨p, hp, -, hpm⟩, -⟩
  · exact absurd hB N.nonBender
  · exact h2
  · rcases hm with hm | hm
    · exact absurd hm h3
    · exact absurd hm hM11
  · exact absurd hpm (hL2 p hp)

theorem K0_eq_K_of_rank2 (hNI : NonIso257) (h3 : Id2519.Prop121Three) (hlv : Lv254 N) {n : ℕ}
    (hn : IsRank2Model257 N.K n) : N.K0 = N.K := by
  rcases hlv.facts254.shape with h | ⟨s, hsS, hne, -, -⟩
  · exact h
  · exfalso
    have hcore : pCoreOf 2 N.H ≠ ⊥ := hlv.facts254.SC_eq ▸ hlv.facts254.SC_ne_bot
    have hc : N.K ∈ cComp N.H := Vol2Native.mem_cComp_of_isComponentIn N.isComp
    rcases h3 G hs.setting.simple hs.setting.nonabelian hs.setting.qtke N.H hcore N.K hc with
      hnorm | ⟨-, hlist⟩
    · apply hne
      ext y
      rw [CFSG.QuasithinUnique.mem_conjugate_iff]
      exact (Subgroup.mem_normalizer_iff.mp (hnorm (N.S_le_H hsS)) y).symm
    · exact (hNI ↥N.K n hn.1 hn.2).2.2.2.1 hlist

theorem borel_eq_257 (hB : IsBorelIn (M ⊓ N.K) N.K) :
    M ⊓ N.K = N.K ⊓ Subgroup.normalizer (N.SK : Set G) := by
  obtain ⟨P, hP, hBP⟩ := hB
  have hSKsyl := N.SK_sylow
  have hSKB : N.SK ≤ N.K ⊓ Subgroup.normalizer (P : Set G) := by
    rw [← hBP]
    exact le_inf (inf_le_left.trans (L257.S_le_M N)) inf_le_right
  have hPB : P ≤ N.K ⊓ Subgroup.normalizer (P : Set G) := le_inf hP.le Subgroup.le_normalizer
  have hPsyl : IsSylowTwoOf P (N.K ⊓ Subgroup.normalizer (P : Set G)) := by
    refine isSylowTwoOf_of_card_eq hPB hP.isPGroup ?_
    have h1 : twoPart (N.K ⊓ Subgroup.normalizer (P : Set G)) ≤ twoPart N.K :=
      twoPart_mono inf_le_left
    have h2 : Nat.card P ≤ twoPart (N.K ⊓ Subgroup.normalizer (P : Set G)) :=
      card_le_twoPart hPB hP.isPGroup
    have h3 : Nat.card P = twoPart N.K := hP.card_eq
    omega
  obtain ⟨S', hSKS', hS'⟩ := exists_isSylowTwoOf_of_le hSKB hSKsyl.isPGroup
  obtain ⟨h, hh, hconj⟩ := hS'.exists_conj hPsyl
  have hS'P : S' ≤ P := by
    intro x hx
    have h1 : h * x * h⁻¹ ∈ P := by
      rw [hconj]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    exact (Subgroup.mem_normalizer_iff.mp hh.2 x).mpr h1
  have hSKP : N.SK = P := by
    refine Subgroup.eq_of_le_of_card_ge (hSKS'.trans hS'P) ?_
    rw [hP.card_eq, hSKsyl.card_eq]
  rw [hSKP]
  exact hBP

theorem exists_swapper_257 (hRB : RankTwoBorelFacts) (hlist : IsRankTwoEvenType N.K)
    (hdyn : NontrivialOnDynkin M N.S N.K) (hbor : IsBorelIn (M ⊓ N.K) N.K) :
    ∃ K₁ K₂ : Subgroup G, ∃ s ∈ N.S, IsParabolicPair257 N.K N.SK K₁ K₂ ∧
      CFSG.conjugate K₁ s = K₂ := by
  have hq : CFSG.IsQuasisimple ↥N.K := BenderBranch.isQuasisimple_of_isComponentIn N.isComp
  have hB := N.borel_eq_257 hbor
  obtain ⟨-, K₁, K₂, hlt₁, hlt₁', hlt₂, hlt₂', hne, hsup, honly, -, -⟩ :=
    hRB G N.K N.SK hq hlist N.SK_sylow
  have hpair : IsParabolicPair257 N.K N.SK K₁ K₂ :=
    ⟨N.SK_sylow, hlt₁, hlt₂, hlt₁', hlt₂', hne, hsup, honly⟩
  have hsw : ∃ s ∈ N.S, CFSG.conjugate K₁ s = K₂ := by
    by_contra hno
    have hno' : ∀ s ∈ N.S, CFSG.conjugate K₁ s ≠ K₂ := fun s hs h => hno ⟨s, hs, h⟩
    have hnorm : N.S ⊓ Subgroup.normalizer (N.K : Set G) ≤ Subgroup.normalizer (K₁ : Set G) := by
      intro s hs
      have hsS : s ∈ N.S := hs.1
      have hsK : s ∈ Subgroup.normalizer (N.K : Set G) := hs.2
      have hsM : s ∈ M := L257.S_le_M N hsS
      have hKs : CFSG.conjugate N.K s = N.K :=
        BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hsK
      have hsB : CFSG.conjugate (N.K ⊓ Subgroup.normalizer (N.SK : Set G)) s =
          N.K ⊓ Subgroup.normalizer (N.SK : Set G) := by
        rw [← hB, BenderBranch.conjugate_inf, hKs]
        have hM : CFSG.conjugate M s = M := by
          rw [BenderBranch.conjugate_eq_iff_mem_normalizer]
          exact Subgroup.le_normalizer hsM
        rw [hM]
      have hlt : CFSG.conjugate (N.K ⊓ Subgroup.normalizer (N.SK : Set G)) s <
          CFSG.conjugate K₁ s :=
        lt_of_le_of_ne (BenderBranch.conjugate_mono hlt₁.le s)
          (fun e => hlt₁.ne (BenderBranch.conjugate_inj.mp e))
      rw [hsB] at hlt
      have hlt' : CFSG.conjugate K₁ s < N.K := by
        have h1 : CFSG.conjugate K₁ s < CFSG.conjugate N.K s :=
          lt_of_le_of_ne (BenderBranch.conjugate_mono hlt₁'.le s)
            (fun e => hlt₁'.ne (BenderBranch.conjugate_inj.mp e))
        rwa [hKs] at h1
      rcases honly _ hlt hlt' with h1 | h1
      · exact BenderBranch.conjugate_eq_iff_mem_normalizer.mp h1
      · exact absurd h1 (hno' s hsS)
    rcases hdyn K₁ (hB ▸ hlt₁.le) hlt₁'.le hnorm with h | h
    · exact hlt₁.ne (h.trans hB).symm
    · exact hlt₁'.ne h
  obtain ⟨s, hsS, hs⟩ := hsw
  exact ⟨K₁, K₂, s, hsS, hpair, hs⟩

theorem setup257 (hRB : RankTwoBorelFacts) (hNI : NonIso257) (h3 : Id2519.Prop121Three)
    (hlv : Lv256 N) {n : ℕ} (hn : IsRank2Model257 N.K n) :
    ∃ K₁ K₂ : Subgroup G, ∃ s : G,
      Setup257 N n K₁ K₂ (pCoreOf 2 K₁) (pCoreOf 2 K₂) s := by
  obtain ⟨hlist, hdyn, hbor⟩ := N.case2_of_rank2 hNI hn hlv.list252
  obtain ⟨K₁, K₂, s, hsS, hpair, hsw⟩ := N.exists_swapper_257 hRB hlist hdyn hbor
  exact ⟨K₁, K₂, s, ⟨N.K0_eq_K_of_rank2 hNI h3 hlv.toLv254 hn,
    BenderBranch.isQuasisimple_of_isComponentIn N.isComp, hn, hlist, N.borel_eq_257 hbor, hpair, rfl,
    rfl, hsS, hsw⟩⟩

end Notation25

end CFSG.QuasithinUnique
