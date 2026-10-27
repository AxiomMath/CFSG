module

import CFSG.ClassicalInvolution.Asc77.AscT8T12Eng
public import CFSG.ClassicalInvolution.Asc77.AscT3SConfEng
public import CFSG.ClassicalInvolution.Asc77.AscT8T9

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace T8T

section Triangle

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


omit [Finite G] in
theorem le_centralizer_of_uniqueInvolution {K : Subgroup G} {z : G} (h : IsUniqueInvolution K z) :
    K ≤ Subgroup.centralizer ({z} : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : g * z * g⁻¹ ∈ K := K.mul_mem (K.mul_mem hg h.mem) (K.inv_mem hg)
  have hsq : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    have : (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
    rw [this, h.sq]
    group
  rcases h.unique _ hmem hsq with h1 | h1
  · exfalso
    apply h.ne_one
    have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [this, h1]
    group
  · calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [h1]

theorem exists_sylow_cent_pair {M : Subgroup G} {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (haM : a ∈ trivialOnQuot M) (hbM : b ∈ trivialOnQuot M) :
    ∃ T : Subgroup G, IsSylow2In T M ∧ T ≤ Subgroup.centralizer ({a} : Set G) ∧
      T ≤ Subgroup.centralizer ({b} : Set G) :=
  exists_sylow_cent_pair_gen ha hb hab haM hbM

theorem exists_triFrame_of_nbrs (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K J₁ J₂ : Subgroup G} {z t₁ t₂ : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (h1 : IsUniqueInvolution J₁ t₁) (h2 : IsUniqueInvolution J₂ t₂) (hJ₁ : J₁ ∈ omegaNbr Ω K)
    (hJ₂ : J₂ ∈ omegaNbr Ω K) (h12 : J₂ ∈ omegaNbr Ω J₁) :
    ∃ R : Fin 3 → Subgroup G, TriFrame Ω ![K, J₁, J₂] ![z, t₁, t₂] R := by
  exact exists_triFrame_of_nbrsE
    (fun hA hB h => T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hA hB h)
    (fun hx hJ hy => T8.mul_comm_of_mem_omegaNbr hp hΩ hx hJ hy)
    (fun hA hR hRA => hΩ.isSylow2In_of_mem_RSet_of_le hp hA hR hRA)
    (fun hc2 hA => mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hc2 hA)
    hK hz h1 h2 hJ₁ hJ₂ h12

end Triangle

section Alpha

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K : Subgroup G}


omit [IsSimpleGroup G] in
theorem closure_pair_eq_of_mul {z t₁ t₂ : G} (hz : z * z = 1) (h : t₂ = z * t₁) :
    Subgroup.closure ({t₂, z} : Set G) = Subgroup.closure ({t₁, z} : Set G) := by
  exact closure_pair_eq_of_mulE hz h

theorem alphaOf_eq_of_nbrs (hst : AscStand p f Ω K) (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M)
    {J₁ J₂ : Subgroup G} {z t₁ t₂ : G} (hz : IsUniqueInvolution K z)
    (h1 : IsUniqueInvolution J₁ t₁) (h2 : IsUniqueInvolution J₂ t₂) (hJ₁ : J₁ ∈ omegaNbr Ω K)
    (hJ₂ : J₂ ∈ omegaNbr Ω K) (h12 : J₂ ∈ omegaNbr Ω J₁) :
    alphaOf (Subgroup.closure ({t₂, z} : Set G)) =
      alphaOf (Subgroup.closure ({t₁, z} : Set G)) := by
  classical
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  by_cases hmem : t₂ ∈ Subgroup.closure ({z, t₁} : Set G)
  · have hzt : z * t₁ = t₁ * z := T8.mul_comm_of_mem_omegaNbr hp hΩ hz hJ₁ h1
    rcases T3CII.closure_pair_cases hz.sq h1.sq hzt hmem with h | h | h | h
    · exact absurd h h2.ne_one
    · exact absurd (hnt K hst.mem J₂ ⟨hJ₂.1, z, hz, h ▸ h2⟩) hJ₂.2.1
    · exact absurd (hnt J₁ hJ₁.1 J₂ ⟨hJ₂.1, t₁, h1, h ▸ h2⟩) h12.2.1
    · rw [closure_pair_eq_of_mul hz.sq h]
  · obtain ⟨R, hF⟩ := exists_triFrame_of_nbrs hp hq hΩ hst.mem hz h1 h2 hJ₁ hJ₂ h12
    have hHyp : Hyp51 (Subgroup.closure ({z, t₁, t₂} : Set G)) :=
      hyp51Tri_proved p f G Ω ![K, J₁, J₂] ![z, t₁, t₂] R hst hnt hF hmem
    have hzt : z * t₁ = t₁ * z := hF.comm hp hΩ 0 1
    have hz1 : z ≠ 1 := hz.ne_one
    have ht1 : t₁ ≠ 1 := h1.ne_one
    have ht2 : t₂ ≠ 1 := h2.ne_one
    have hzt' : t₁ ≠ z := (hF.x_ne hnt (i := 0) (j := 1) (by decide)).symm
    have hzt2 : t₂ ≠ z := (hF.x_ne hnt (i := 0) (j := 2) (by decide)).symm
    have hDB : Subgroup.closure ({t₁, z} : Set G) ≤ Subgroup.closure ({z, t₁, t₂} : Set G) := by
      apply Subgroup.closure_mono
      intro y hy
      rcases hy with rfl | rfl <;> simp
    have hD : IsElemAbelian2 (Subgroup.closure ({t₁, z} : Set G)) 2 :=
      T7A.isElemAbelian2_closure_pair h1.sq hz.sq ht1 hz1 hzt' hzt.symm
    have hAB : Subgroup.closure ({t₂, z} : Set G) ≤ Subgroup.closure ({z, t₁, t₂} : Set G) := by
      apply Subgroup.closure_mono
      intro y hy
      rcases hy with rfl | rfl <;> simp
    have hA : IsElemAbelian2 (Subgroup.closure ({t₂, z} : Set G)) 2 :=
      T7A.isElemAbelian2_closure_pair h2.sq hz.sq ht2 hz1 hzt2 (hF.comm hp hΩ 2 0)
    exact (lemma54_odd_and_eq hHyp hDB hD).2 _ hAB hA

end Alpha

section Conn

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C27_LinkConn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand p f Ω K → (∀ K' ∈ twinSet Ω K, K' = K) → ¬ DConnected Ω →
      (∃ W ∈ WSet Ω, (∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) ∧
        ¬ MuIsoE4 Ω W) →
      ∀ J₁ ∈ omegaNbr Ω K, ∀ J₂ ∈ omegaNbr Ω K,
        Relation.ReflTransGen (fun N N' => N' ∈ omegaNbr Ω N ∧ N' ∈ omegaNbr Ω K) J₁ J₂


theorem c27_alphaConst_of_linkConn (hL : C27_LinkConn p f) : C27_AlphaConst p f := by
  intro G _ _ _ Ω K hst hnt hdisc hμ z hz J₁ hJ₁ J₂ hJ₂ t₁ t₂ h1 h2
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hnt' : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hst.trans hnt hM
  have hchain := hL G Ω K hst hnt hdisc hμ J₁ hJ₁ J₂ hJ₂
  have key : ∀ N, Relation.ReflTransGen
      (fun N N' => N' ∈ omegaNbr Ω N ∧ N' ∈ omegaNbr Ω K) J₁ N →
      N ∈ omegaNbr Ω K ∧ ∀ t, IsUniqueInvolution N t →
        alphaOf (Subgroup.closure ({t, z} : Set G)) =
          alphaOf (Subgroup.closure ({t₁, z} : Set G)) := by
    intro N hN
    induction hN with
    | refl => exact ⟨hJ₁, fun t ht => by rw [h1.eq ht]⟩
    | tail hb hbc ih =>
      obtain ⟨hbK, hα⟩ := ih
      obtain ⟨hcb, hcK⟩ := hbc
      refine ⟨hcK, fun t ht => ?_⟩
      obtain ⟨tb, htb⟩ := hΩ.exists_uniqueInvolution hp hq hbK.1
      rw [← hα tb htb]
      exact alphaOf_eq_of_nbrs hst hnt' hz htb ht hbK hcK hcb
  exact ((key J₂ hchain).2 t₂ h2).symm

end Conn

end T8T

end CFSG.ClassicalInvolution.Asc77
