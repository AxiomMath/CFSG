module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneEmbed

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

theorem inv_mul_mem_normalizer_of_map_eq {X : Type*} [Group X] {J : Subgroup X} {m m' : X}
    (hmm : J.map (MulAut.conj m).toMonoidHom = J.map (MulAut.conj m').toMonoidHom) :
    m'⁻¹ * m ∈ Subgroup.normalizer (J : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : m * x * m⁻¹ ∈ J.map (MulAut.conj m').toMonoidHom :=
      hmm ▸ Subgroup.mem_map_of_mem _ hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h1
    have : m'⁻¹ * m * x * (m'⁻¹ * m)⁻¹ = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      rw [show y = m'⁻¹ * (m' * y * m'⁻¹) * m' by group, hyx]
      group
    rw [this]
    exact hy
  · intro hx
    have h1 : m' * (m'⁻¹ * m * x * (m'⁻¹ * m)⁻¹) * m'⁻¹ ∈ J.map (MulAut.conj m).toMonoidHom :=
      hmm.symm ▸ Subgroup.mem_map_of_mem (MulAut.conj m').toMonoidHom hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : x = y := by
      have h2 : m * y * m⁻¹ = m * x * m⁻¹ := by rw [hyx]; group
      exact (mul_left_cancel (mul_right_cancel h2)).symm
    rw [this]
    exact hy

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J)
include h

theorem eq_of_mem_inf_of_ne {L L' : Subgroup (EscapingQuotient z)} (hL : CFSG.IsComponent L)
    (hL' : CFSG.IsComponent L') (hne : L ≠ L') {x : EscapingQuotient z} (hxL : x ∈ L)
    (hxL' : x ∈ L') : x = 1 ∨ x = escapingBar z := by
  have hcomm : L' ≤ Subgroup.centralizer (L : Set (EscapingQuotient z)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hL' hL).resolve_left (Ne.symm hne))
  exact h.eq_of_mem_centralizer_component hL hxL (hcomm hxL')

theorem component_eq_of_ne {L₁ L₂ : Subgroup (EscapingQuotient z)} (hL₁ : CFSG.IsComponent L₁)
    (hL₂ : CFSG.IsComponent L₂) (h₁ : L₁ ≠ J) (h₂ : L₂ ≠ J) : L₁ = L₂ := by
  by_contra h12
  have hq := h.quotientData
  obtain ⟨a₁, ha₁S, ha₁L, ha₁⟩ := h.exists_sq_eq_bar hL₁
  obtain ⟨a₂, ha₂S, ha₂L, ha₂⟩ := h.exists_sq_eq_bar hL₂
  have hc12 : L₂ ≤ Subgroup.centralizer (L₁ : Set (EscapingQuotient z)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hL₂ hL₁).resolve_left (Ne.symm h12))
  have hcomm : Commute a₁ a₂ := Subgroup.mem_centralizer_iff.mp (hc12 ha₂L) a₁ ha₁L
  have hJ1 : L₁ ≤ Subgroup.centralizer (J : Set (EscapingQuotient z)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hL₁ h.component).resolve_left h₁)
  have hJ2 : L₂ ≤ Subgroup.centralizer (J : Set (EscapingQuotient z)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hL₂ h.component).resolve_left h₂)
  have he2 : (a₁ * a₂) ^ 2 = 1 := by rw [hcomm.mul_pow, ha₁, ha₂, ← pow_two, h.bar_sq]
  obtain ⟨h1, h2⟩ := h.ne_of_sq_eq_bar ha₁
  have hinv : a₂⁻¹ ∈ L₂ := L₂.inv_mem ha₂L
  have he1 : a₁ * a₂ ≠ 1 := fun he => by
    rcases h.eq_of_mem_inf_of_ne hL₁ hL₂ h12 ha₁L (by rw [eq_inv_of_mul_eq_one_left he]; exact hinv)
      with h3 | h3
    · exact h1 h3
    · exact h2 h3
  have hez : a₁ * a₂ ≠ escapingBar z := fun he => by
    have ha : a₁ = escapingBar z * a₂⁻¹ := by rw [← he, mul_inv_cancel_right]
    rcases h.eq_of_mem_inf_of_ne hL₁ hL₂ h12 ha₁L
      (by rw [ha]; exact L₂.mul_mem (h.square.caseTwo L₂ hL₂) hinv) with h3 | h3
    · exact h1 h3
    · exact h2 h3
  exact hez (h.eq_bar_of_mem_centralizer ((escapingSylowImage S z).mul_mem ha₁S ha₂S)
    (Subgroup.mul_mem _ (hJ1 ha₁L) (hJ2 ha₂L)) (orderOf_eq_prime he2 he1))

theorem normal_of_le_normalizer
    (hSN : escapingSylowImage S z ≤ Subgroup.normalizer (J : Set (EscapingQuotient z))) :
    J.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (J : Set (EscapingQuotient z)) with hN
  suffices hNtop : N = ⊤ by
    rw [← Subgroup.normalizer_eq_top_iff, ← hN, hNtop]
  by_contra hNtop
  obtain ⟨m, hm⟩ : ∃ m, m ∉ N := by
    by_contra hall
    push Not at hall
    exact hNtop (eq_top_iff.mpr fun x _ => hall x)
  have hcomp : ∀ m', m' ∉ N → J.map (MulAut.conj m').toMonoidHom ≠ J := fun m' hm' heq =>
    hm' (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
  have hsame : ∀ m', m' ∉ N → m'⁻¹ * m ∈ N := fun m' hm' =>
    inv_mul_mem_normalizer_of_map_eq (h.component_eq_of_ne
      (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj m) h.component)
      (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj m') h.component)
      (hcomp m hm) (hcomp m' hm'))
  have hindex : N.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨m, fun b => ?_⟩
    by_cases hb : b ∈ N
    · refine Or.inr ⟨hb, fun hbm => hm ?_⟩
      have := N.mul_mem (N.inv_mem hb) hbm
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨?_, hb⟩
      have := hsame b⁻¹ (fun hb' => hb (by simpa using N.inv_mem hb'))
      rwa [inv_inv] at this
  have hdvd : N.index ∣ (sylowBarSylow h.square.central : Subgroup (EscapingQuotient z)).index :=
    Subgroup.index_dvd_of_le (h.coe_sylow ▸ hSN)
  rw [hindex] at hdvd
  exact (sylowBarSylow h.square.central).not_dvd_index hdvd

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
