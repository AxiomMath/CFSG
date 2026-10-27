module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1NextCentral
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1NextHKS

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

section HKS

theorem SzC1Next.exists_next {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G}
    {T : Subgroup G} {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K]
    [CharP K 2] {u v : G → K} {κ : K} (H : SzC1Next G L f a t T d V U U₁ k K u v κ)
    (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) :
    ∃ U' U₁' : Subgroup G,
      SzC1Stage G L f a t T d (U₁ ⊓ centralizer (szT₁ L T : Set G)) U' U₁' (k + 1) := by
  obtain ⟨E, hEle, hEn, hEab, hE2, hEc, hreg, htr⟩ := H.exists_regular hU
  have hE : H.RegData E := ⟨hEle, hEn, hEab, hE2, hEc, hreg, htr⟩
  obtain ⟨U₁', -, hle, hN, htU₁, hsup, hd, hinf⟩ := H.exists_U₁' hE
  obtain ⟨hV₁C, hV₁comm, hV₁card, hV₁Ω, hV₁pow, hV₁le, hV₁inv, hV₁d⟩ :=
    H.stage.nextConf H.mu H.lam H.nu
  have hR := H.stage.szR_V₁_eq H.lam
  refine ⟨H.nextU E, U₁',
    { start := H.stage.start
      hfa := H.stage.hfa
      ha := H.stage.ha
      coords := H.stage.coords
      d_mem_L := H.stage.d_mem_L
      d_odd := H.stage.d_odd
      le_centralizer := hV₁C
      comm := hV₁comm
      card := hV₁card
      omega := hV₁Ω
      pow := hV₁pow
      le := hV₁le
      inv := hV₁inv
      d_norm := hV₁d
      U_le := by rw [hR]; exact H.nextU_le hE
      U_normal := by rw [hR]; exact H.normalizer_le_normalizer_nextU hE
      isSylowOf := by rw [hR]; exact H.isSylowOf_nextU hE
      card_U := H.card_nextU hE
      szR_le := by rw [hR]; exact H.U_le_nextU hE
      conj_t_not_mem := by
        rw [hR]
        exact fun x hx hxU => H.conj_t_not_mem_of_mem_nextU hE hx hxU
      conj_szA₁ := fun x hx => H.conj_szA₁_of_mem_nextU hE hx
      conj_T₁ := fun x hx y hy => H.conj_T₁_of_mem_nextU hE hx hy
      conj_V₁ := H.conj_V₁_of_mem_U₁' hE hle hN hsup hd hinf
      inf_centralizer := H.inf_centralizer_nextU hE
      U₁_le := hle
      U₁_normal := hN
      sup_eq := hsup
      t_not_mem := htU₁
      inf_eq := by rw [hR, hinf]; exact H.lam
      d_mem_U₁ := hd }⟩

theorem SzC1Stage.next {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G}
    {T : Subgroup G} {d : G} {V U U₁ : Subgroup G} {k : ℕ}
    (h : SzC1Stage G L f a t T d V U U₁ k) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) :
    ∃ U' U₁' : Subgroup G,
      SzC1Stage G L f a t T d (U₁ ⊓ centralizer (szT₁ L T : Set G)) U' U₁' (k + 1) := by
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, hκ⟩ := h.coords
  exact (SzC1Next.mk h hK hc hκ hμ hlam hν).exists_next fun hS => h.false_of_isSylow hS

end HKS

end CFSG.SeitzReduction.RankOne
