module

public import CFSG.GH74.KGroups.L3EpsBlockAut
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.KGroups.L3Eps

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups commutatorElement

structure InvData (q : ℕ) (K : Type*) [Group K] (t : K) (S : Subgroup K) : Prop where
  card : Nat.card ↥S = q * (q ^ 2 - 1)
  quasisimple : CFSG.IsQuasisimple ↥S
  mem : t ∈ S
  le_centralizer : S ≤ Subgroup.centralizer ({t} : Set K)
  conj_mem : ∀ x ∈ Subgroup.centralizer ({t} : Set K), ∀ s ∈ S, x * s * x⁻¹ ∈ S
  commutator_mem : ∀ x ∈ Subgroup.centralizer ({t} : Set K), ∀ y ∈ Subgroup.centralizer ({t} : Set K),
    ⁅x, y⁆ ∈ S
  involution : ∀ s ∈ S, s * s = 1 → s = 1 ∨ s = t
  center : ∀ s : ↥S, s ∈ Subgroup.center ↥S → (s : K) = 1 ∨ (s : K) = t
  aut_fixing : ∀ σ : MulAut K, σ * σ = 1 → (∀ s ∈ S, σ s = s) → σ = 1 ∨ σ = MulAut.conj t
  graph_solvable : ∀ σ : MulAut K, σ * σ = 1 → σ ∉ inner K → σ t = t → ∀ P : Subgroup K, P ≤ S →
    (∀ s ∈ P, σ s * s⁻¹ ∈ Subgroup.zpowers t) → Group.IsSolvable ↥P

structure GraphData (K : Type*) [Group K] (c : MulAut K) (N : Subgroup K) : Prop where
  quasisimple : CFSG.IsQuasisimple ↥N
  fixed : ∀ n ∈ N, c n = n
  conj_mem : ∀ x, c x = x → ∀ n ∈ N, x * n * x⁻¹ ∈ N
  commutator_mem : ∀ x y, c x = x → c y = y → ⁅x, y⁆ ∈ N

section Transport

variable {K : Type*} [Group K] {F : Type} [Field F]

def conjAutEquiv {X : Type*} [Group X] (e : K ≃* X) (σ : MulAut K) : MulAut X :=
  (e.symm.trans σ).trans e

theorem conjAutEquiv_apply {X : Type*} [Group X] (e : K ≃* X) (σ : MulAut K) (x : K) :
    conjAutEquiv e σ (e x) = e (σ x) := by
  simp [conjAutEquiv]

theorem conjAutEquiv_mul {X : Type*} [Group X] (e : K ≃* X) (σ τ : MulAut K) :
    conjAutEquiv e (σ * τ) = conjAutEquiv e σ * conjAutEquiv e τ := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  simp [conjAutEquiv_apply]

theorem conjAutEquiv_one {X : Type*} [Group X] (e : K ≃* X) : conjAutEquiv e (1 : MulAut K) = 1 := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  simp [conjAutEquiv_apply]

theorem conjAutEquiv_eq_one_iff {X : Type*} [Group X] (e : K ≃* X) (σ : MulAut K) :
    conjAutEquiv e σ = 1 ↔ σ = 1 := by
  constructor
  · intro h
    ext x
    have := congrArg (fun τ : MulAut X => τ (e x)) h
    simp only [conjAutEquiv_apply, MulAut.one_apply] at this
    exact e.injective this
  · rintro rfl
    exact conjAutEquiv_one e

theorem conjAutEquiv_conj {X : Type*} [Group X] (e : K ≃* X) (t : K) :
    conjAutEquiv e (MulAut.conj t) = MulAut.conj (e t) := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  simp [conjAutEquiv_apply, MulAut.conj_apply]

theorem conjAutEquiv_mem_inner {X : Type*} [Group X] (e : K ≃* X) {σ : MulAut K}
    (h : conjAutEquiv e σ ∈ inner X) : σ ∈ inner K := by
  obtain ⟨x, hx⟩ := h
  refine ⟨e.symm x, ?_⟩
  ext y
  have := congrArg (fun τ : MulAut X => τ (e y)) hx
  simp only [conjAutEquiv_apply, MulAut.conj_apply] at this ⊢
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact this

def subgroupOfEquiv {X : Type*} [Group X] (e : K ≃* X) (S : Subgroup X) : Subgroup K :=
  S.map (e.symm : X →* K)

theorem mem_subgroupOfEquiv {X : Type*} [Group X] (e : K ≃* X) (S : Subgroup X) (x : K) :
    x ∈ subgroupOfEquiv e S ↔ e x ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨e x, h, by simp⟩


theorem invData_of_equiv [Finite F] {p f : ℕ} (hp : p.Prime) (hFc : Nat.card F = p ^ f) (hf : Odd f)
    (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) (e : K ≃* projectiveSL 3 F) {t : K} (ht : e t = tInv) :
    InvData (p ^ f) K t (subgroupOfEquiv e blockSub) := by
  have hF2 : ringChar F ≠ 2 := fun h => h2 (by
    have : CharP F 2 := h ▸ ringChar.charP F
    exact CharTwo.two_eq_zero)
  have hcen : ∀ x : K, x ∈ Subgroup.centralizer ({t} : Set K) ↔
      e x ∈ Subgroup.centralizer ({tInv} : Set (projectiveSL 3 F)) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← ht, ← map_mul,
      ← map_mul]
    exact ⟨fun h => by rw [h], fun h => e.injective h⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : ↥(subgroupOfEquiv e blockSub) ≃* ↥(blockSub : Subgroup (projectiveSL 3 F)) :=
      (MulEquiv.subgroupMap e.symm blockSub).symm
    have e2 : SL(2, F) ≃* ↥(blockSub : Subgroup (projectiveSL 3 F)) :=
      MonoidHom.ofInjective (blockEmb_injective (F := F))
    rw [Nat.card_congr e1.toEquiv, ← Nat.card_congr e2.toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFc]
  · exact LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap e.symm blockSub)
      (isQuasisimple_blockSub h4)
  · rw [mem_subgroupOfEquiv, ht]
    exact tInv_mem_blockSub
  · intro s hs
    rw [mem_subgroupOfEquiv] at hs
    rw [hcen]
    exact blockSub_le_centralizer hs
  · intro x hx s hs
    rw [hcen] at hx
    rw [mem_subgroupOfEquiv] at hs ⊢
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_blockSub h2 hx hs
  · intro x hx y hy
    rw [hcen] at hx hy
    rw [mem_subgroupOfEquiv, map_commutatorElement]
    exact commutator_mem_blockSub h2 hx hy
  · intro s hs hs2
    rw [mem_subgroupOfEquiv] at hs
    have h1 : e s * e s = 1 := by rw [← map_mul, hs2, map_one]
    rcases blockSub_involution hF2 hs h1 with h | h
    · left
      exact e.injective (h.trans (map_one e).symm)
    · right
      exact e.injective (h.trans ht.symm)
  · intro s hs
    have hs' : (⟨e s, (mem_subgroupOfEquiv e blockSub s).1 s.2⟩ : ↥(blockSub : Subgroup (projectiveSL 3 F))) ∈
        Subgroup.center ↥(blockSub : Subgroup (projectiveSL 3 F)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy : e.symm y ∈ subgroupOfEquiv e blockSub := by
        rw [mem_subgroupOfEquiv, MulEquiv.apply_symm_apply]
        exact y.2
      have := Subgroup.mem_center_iff.1 hs ⟨e.symm y, hy⟩
      apply Subtype.ext
      have h' := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at h'
      show (y : projectiveSL 3 F) * e s = e s * (y : projectiveSL 3 F)
      have := congrArg e h'
      simpa [map_mul] using this
    rcases blockSub_center hs' with h | h
    · left
      exact e.injective (h.trans (map_one e).symm)
    · right
      exact e.injective (h.trans ht.symm)
  · intro σ hσ2 hfix
    have hfix' : ∀ s ∈ (blockSub : Subgroup (projectiveSL 3 F)), conjAutEquiv e σ s = s := by
      intro s hs
      obtain ⟨x, rfl⟩ := e.surjective s
      rw [conjAutEquiv_apply]
      congr 1
      exact hfix x ((mem_subgroupOfEquiv e blockSub x).2 hs)
    have hσ2' : conjAutEquiv e σ * conjAutEquiv e σ = 1 := by
      rw [← conjAutEquiv_mul, hσ2, conjAutEquiv_one]
    rcases aut_fixing_blockSub hp hFc hf h2 h4 hσ2' hfix' with h | h
    · left
      exact (conjAutEquiv_eq_one_iff e σ).1 h
    · right
      have : conjAutEquiv e σ = conjAutEquiv e (MulAut.conj t) := by rw [h, conjAutEquiv_conj, ht]
      ext x
      have := congrArg (fun τ : MulAut (projectiveSL 3 F) => τ (e x)) this
      simp only [conjAutEquiv_apply] at this
      exact e.injective this
  · intro σ hσ2 hout hσt P hPS hP
    have hσ2' : conjAutEquiv e σ * conjAutEquiv e σ = 1 := by
      rw [← conjAutEquiv_mul, hσ2, conjAutEquiv_one]
    have hout' : conjAutEquiv e σ ∉ (inner (projectiveSL 3 F) : Subgroup (MulAut (projectiveSL 3 F))) :=
      fun h => hout (conjAutEquiv_mem_inner e h)
    have hσt' : conjAutEquiv e σ tInv = tInv := by
      rw [← ht, conjAutEquiv_apply, hσt]
    have hsolv := graph_fixing_solvable hp hFc hf h2 hσ2' hout' hσt' (P := P.map (e : K →* projectiveSL 3 F))
      (by
        rintro _ ⟨s, hs, rfl⟩
        exact (mem_subgroupOfEquiv e blockSub s).1 (hPS hs))
      (by
        rintro _ ⟨s, hs, rfl⟩
        show conjAutEquiv e σ (e s) * (e s)⁻¹ ∈ _
        rw [conjAutEquiv_apply, ← map_inv, ← map_mul, ← ht]
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hP s hs)
        exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← hk, map_zpow]⟩)
    have := hsolv
    exact Group.isSolvable_of_isSolvable_injective (f := (MulEquiv.subgroupMap e P).toMonoidHom)
      (MulEquiv.subgroupMap e P).injective


theorem graphData_of_equiv [Finite F] {p f : ℕ} (hp : p.Prime) (hFc : Nat.card F = p ^ f) (hf : Odd f)
    (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F) (e : K ≃* projectiveSL 3 F) {c : MulAut K}
    (hc2 : c * c = 1) (hout : c ∉ inner K) : ∃ N : Subgroup K, GraphData K c N := by
  have hF2 : ringChar F ≠ 2 := fun h => h2 (by
    have : CharP F 2 := h ▸ ringChar.charP F
    exact CharTwo.two_eq_zero)
  have hc2' : conjAutEquiv e c * conjAutEquiv e c = 1 := by
    rw [← conjAutEquiv_mul, hc2, conjAutEquiv_one]
  have hout' : conjAutEquiv e c ∉ (inner (projectiveSL 3 F) : Subgroup (MulAut (projectiveSL 3 F))) :=
    fun h => hout (conjAutEquiv_mem_inner e h)
  obtain ⟨A, hAs, hA⟩ := lin_involution_form hp hFc hf h2 hc2' hout'
  obtain ⟨N, hq, hfix, hconj, hcomm⟩ := lin_graph_centralizer hF2 (by omega) hAs
  rw [← hA] at hfix hconj hcomm
  have hfixK : ∀ x : K, c x = x → conjAutEquiv e c (e x) = e x := fun x hx => by
    rw [conjAutEquiv_apply, hx]
  refine ⟨subgroupOfEquiv e N, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap e.symm N) hq
  · intro n hn
    rw [mem_subgroupOfEquiv] at hn
    apply e.injective
    rw [← conjAutEquiv_apply]
    exact hfix _ hn
  · intro x hx n hn
    rw [mem_subgroupOfEquiv] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact hconj _ (hfixK x hx) _ hn
  · intro x y hx hy
    rw [mem_subgroupOfEquiv, map_commutatorElement]
    exact hcomm _ _ (hfixK x hx) (hfixK y hy)

end Transport

end CFSG.GH74.KGroups.L3Eps
