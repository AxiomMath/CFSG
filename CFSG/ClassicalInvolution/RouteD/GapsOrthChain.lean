module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthModel
public import CFSG.ClassicalInvolution.RouteD.GapsOrthTransfer

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic (Commutes conjSub)
open scoped commutatorElement

section Abstract

variable {KY : Type} [Group KY]

structure IsChain (Z : Subgroup KY) (𝓕 : Set (Subgroup KY)) (r : ℕ) (c : ℕ → Subgroup KY) :
    Prop where
  mem : ∀ a < r, c a ∈ 𝓕
  adj : ∀ a, a + 1 < r → ModelAdj Z (c a) (c (a + 1))
  comm : ∀ a b, a + 1 < b → b < r → Commutes (c a) (c b)

@[expose] def ChainBound (Z : Subgroup KY) (𝓕 : Set (Subgroup KY)) (d : ℕ) : Prop :=
  ∀ r, 4 ≤ r → ∀ c, IsChain Z 𝓕 r c → ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, ModelAdj Z A B →
    (∀ a < r, Commutes A (c a)) → (∀ a < r, Commutes B (c a)) → 2 * (r + 1) + 6 ≤ d

theorem ModelInvComm.of_adj {Z : Subgroup KY} {R₁ R₂ : Subgroup KY} (h : ModelAdj Z R₁ R₂) :
    ModelInvComm Z R₁ R₂ := by
  obtain ⟨-, -, r₁, r₂, hr₁, hr₂, hc, -⟩ := h
  exact ⟨r₁, r₂, hr₁, hr₂, hc⟩

theorem ModelInvComm.symm' {Z : Subgroup KY} {R₁ R₂ : Subgroup KY} (h : ModelInvComm Z R₁ R₂) :
    ModelInvComm Z R₂ R₁ := by
  obtain ⟨r₁, r₂, h1, h2, hc⟩ := h
  refine ⟨r₂, r₁, h2, h1, ?_⟩
  rw [← commutatorElement_inv]
  exact Z.inv_mem hc

end Abstract

section Geometry

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
theorem polar_pos_neg (hodd : Odd (Nat.card K)) {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V}
    (h : IsFundamental Q L i) : ∀ x ∈ posSpace i, ∀ y ∈ negSpace i, polar Q x y = 0 := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F, rfl, rfl⟩ := h
  rw [posSpace_La_neg_one h2, negSpace_La_neg_one h2]
  rintro x hx _ ⟨Y, rfl⟩
  exact (Frame.mem_perp_iff_forall_incl F).mp hx Y

omit [FiniteDimensional K V] in
theorem modelInvComm_of_commutes (hodd : Odd (Nat.card K)) {R S : Subgroup (V ≃ₗ[K] V)}
    {i j : V ≃ₗ[K] V} (hR : IsFundamental Q R i) (hS : IsFundamental Q S j) (hc : Commutes R S) :
    ModelInvComm (scalars K V) R S := by
  refine ⟨i, j, ⟨hR.mem, hR.orderOf_eq_two hodd⟩, ⟨hS.mem, hS.orderOf_eq_two hodd⟩, ?_⟩
  have : i * j = j * i := hc i hR.mem j hS.mem
  rw [commutatorElement_eq_one_iff_mul_comm.mpr this]
  exact (scalars K V).one_mem

theorem ne_of_distinguish (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V)
    {Li Lj D : Subgroup (V ≃ₗ[K] V)} {ii ij id : V ≃ₗ[K] V} (hi : IsFundamental Q Li ii)
    (hj : IsFundamental Q Lj ij) (hd : IsFundamental Q D id) (hne_i : D ≠ Li) (hne_j : D ≠ Lj)
    (hinv_i : ModelInvComm (scalars K V) D Li) (hinv_j : ModelInvComm (scalars K V) D Lj)
    (hdist : ¬ (Commutes D Li ↔ Commutes D Lj)) : ij ≠ ii := by
  intro heq
  have hne : Li ≠ Lj := fun h => hdist (by rw [h])
  have hind := indist_of_eq hodd hdim hi hj hne heq
  exact hdist (hind.2 D ⟨id, hd⟩ hne_i hne_j hinv_i hinv_j)

theorem chain_orth (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V) {r : ℕ} (hr : 4 ≤ r)
    {c : ℕ → Subgroup (V ≃ₗ[K] V)} (hc : IsChain (scalars K V) (fundSet Q) r c)
    {i : ℕ → V ≃ₗ[K] V} (hi : ∀ a < r, IsFundamental Q (c a) (i a)) {a b : ℕ} (hab : a + 1 < b)
    (hb : b < r) : ∀ x ∈ negSpace (i a), ∀ y ∈ negSpace (i b), polar Q x y = 0 := by
  have har : a < r := by omega
  rcases orth_or_twin hodd (hi a har) (hi b hb) (hc.comm a b hab hb) with h | h
  · exact h
  · exfalso
    have nc : ∀ a', a' + 1 < r → ¬ Commutes (c a') (c (a' + 1)) := fun a' h' => (hc.adj a' h').2.1
    by_cases h1 : a + 2 < b
    ·
      refine ne_of_distinguish hodd hdim (hi a har) (hi b hb) (hi (a + 1) (by omega)) ?_ ?_ ?_ ?_ ?_ h
      · exact fun e => (hc.adj a (by omega)).1 e.symm
      · intro e
        apply nc a (by omega)
        have := hc.comm a b hab hb
        rwa [← e] at this
      · exact (ModelInvComm.of_adj (hc.adj a (by omega))).symm'
      · exact modelInvComm_of_commutes hodd (hi (a + 1) (by omega)) (hi b hb)
          (hc.comm (a + 1) b (by omega) hb)
      · intro hiff
        exact nc a (by omega) (hiff.mpr (hc.comm (a + 1) b (by omega) hb)).symm
    · by_cases h2 : 1 ≤ a
      ·
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        refine ne_of_distinguish hodd hdim (hi (a' + 1) har) (hi b hb) (hi a' (by omega)) ?_ ?_ ?_
          ?_ ?_ h
        · exact fun e => (hc.adj a' (by omega)).1 e
        · intro e
          apply nc a' (by omega)
          have := hc.comm (a' + 1) b hab hb
          rw [← e] at this
          exact this.symm
        · exact ModelInvComm.of_adj (hc.adj a' (by omega))
        · exact modelInvComm_of_commutes hodd (hi a' (by omega)) (hi b hb)
            (hc.comm a' b (by omega) hb)
        · intro hiff
          exact nc a' (by omega) (hiff.mpr (hc.comm a' b (by omega) hb))
      ·
        obtain rfl : a = 0 := by omega
        obtain rfl : b = 2 := by omega
        refine ne_of_distinguish hodd hdim (hi 0 har) (hi 2 hb) (hi 3 (by omega)) ?_ ?_ ?_ ?_ ?_ h
        · intro e
          apply nc 2 (by omega)
          have := hc.comm 0 2 hab hb
          rw [← e] at this
          exact this.symm
        · exact fun e => (hc.adj 2 (by omega)).1 e.symm
        · exact (modelInvComm_of_commutes hodd (hi 0 har) (hi 3 (by omega))
            (hc.comm 0 3 (by omega) (by omega))).symm'
        · exact (ModelInvComm.of_adj (hc.adj 2 (by omega))).symm'
        · intro hiff
          exact nc 2 (by omega) (hiff.mp (hc.comm 0 3 (by omega) (by omega)).symm).symm

omit [Finite K] [FiniteDimensional K V] in
theorem exists_chain_inv {r : ℕ} {c : ℕ → Subgroup (V ≃ₗ[K] V)}
    (hc : IsChain (scalars K V) (fundSet Q) r c) :
    ∃ i : ℕ → V ≃ₗ[K] V, ∀ a < r, IsFundamental Q (c a) (i a) := by
  have hex : ∀ a : ℕ, ∃ i : V ≃ₗ[K] V, a < r → IsFundamental Q (c a) i := fun a => by
    by_cases h : a < r
    · obtain ⟨i, hi⟩ := hc.mem a h
      exact ⟨i, fun _ => hi⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose i hi using hex
  exact ⟨i, hi⟩

def chainSpan (i : ℕ → V ≃ₗ[K] V) : ℕ → Submodule K V
  | 0 => ⊥
  | s + 1 => chainSpan i s ⊔ negSpace (i s)

omit [Finite K] [FiniteDimensional K V] in
theorem le_chainSpan (i : ℕ → V ≃ₗ[K] V) : ∀ {s a : ℕ}, a < s → negSpace (i a) ≤ chainSpan i s := by
  intro s
  induction s with
  | zero => intro a ha; omega
  | succ s ih =>
    intro a ha
    rcases Nat.lt_succ_iff_lt_or_eq.mp ha with h | h
    · exact (ih h).trans le_sup_left
    · subst h
      exact le_sup_right

omit [Finite K] [FiniteDimensional K V] in
theorem polar_chainSpan {i : ℕ → V ≃ₗ[K] V} {x : V} :
    ∀ {s : ℕ}, (∀ a < s, ∀ y ∈ negSpace (i a), polar Q x y = 0) →
      ∀ y ∈ chainSpan i s, polar Q x y = 0 := by
  intro s
  induction s with
  | zero =>
    intro _ y hy
    have : y = 0 := by simpa [chainSpan] using hy
    rw [this, polar_zero_right]
  | succ s ih =>
    intro h y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    rw [polar_add_right, ih (fun a ha => h a (by omega)) u hu, h s (by omega) v hv, add_zero]

theorem finrank_chainSpan (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V) {r : ℕ}
    (hr : 4 ≤ r) {c : ℕ → Subgroup (V ≃ₗ[K] V)} (hc : IsChain (scalars K V) (fundSet Q) r c)
    {i : ℕ → V ≃ₗ[K] V} (hi : ∀ a < r, IsFundamental Q (c a) (i a)) :
    ∀ s, 1 ≤ s → s ≤ r → 2 * (s + 1) ≤ Module.finrank K ↥(chainSpan i s) := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    intro _
    have h0 : chainSpan i 1 = negSpace (i 0) := by simp [chainSpan]
    rw [h0, finrank_negSpace hodd (hi 0 (by omega))]
  | succ s hs ih =>
    intro hsr
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have ih := ih (by omega)
    obtain ⟨cm, N, C⟩ := adj_data hodd hdim (hi s' (by omega)) (hi (s' + 1) (by omega))
      (hc.adj s' (by omega))
    have pd := (lemma_6_10 hodd (hi s' (by omega)) (hi (s' + 1) (by omega)) cm N C).1
    set U : Submodule K V := posSpace (i s') ⊓ negSpace (i (s' + 1)) with hU
    have hUorth : ∀ x ∈ U, ∀ y ∈ chainSpan i (s' + 1), polar Q x y = 0 := by
      intro x hx
      refine polar_chainSpan (fun a ha => ?_)
      rcases Nat.lt_succ_iff_lt_or_eq.mp ha with h | h
      · intro y hy
        rw [polar_comm]
        exact chain_orth hodd hdim hr hc hi (a := a) (b := s' + 1) (by omega) (by omega) y hy x
          (Submodule.mem_inf.mp hx).2
      · subst h
        exact fun y hy => polar_pos_neg hodd (hi a (by omega)) x (Submodule.mem_inf.mp hx).1 y hy
    have hdisj : U ⊓ chainSpan i (s' + 1) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      refine pd.nondeg₃ x hx.1 fun y hy => ?_
      rw [polar_comm]
      exact hUorth y hy x hx.2
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (chainSpan i (s' + 1)) U
    rw [inf_comm, hdisj, finrank_bot, pd.finrank_U₃] at hsup
    have hle : chainSpan i (s' + 1) ⊔ U ≤ chainSpan i (s' + 1 + 1) :=
      sup_le le_sup_left ((inf_le_right : U ≤ negSpace (i (s' + 1))).trans le_sup_right)
    have := Submodule.finrank_mono hle
    omega

theorem chainBound_model (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) :
    ChainBound (scalars K V) (fundSet Q) (Module.finrank K V) := by
  intro r hr c hc A hA B hB hAB hAc hBc
  obtain ⟨i, hi⟩ := exists_chain_inv hc
  obtain ⟨iA, hiA⟩ := hA
  obtain ⟨iB, hiB⟩ := hB
  have nc : ∀ a', a' + 1 < r → ¬ Commutes (c a') (c (a' + 1)) := fun a' h' => (hc.adj a' h').2.1
  have horthX : ∀ (X : Subgroup (V ≃ₗ[K] V)) (iX : V ≃ₗ[K] V), IsFundamental Q X iX →
      (∀ a < r, Commutes X (c a)) → ∀ x ∈ negSpace iX, ∀ y ∈ chainSpan i r, polar Q x y = 0 := by
    intro X iX hX hXc x hx
    refine polar_chainSpan (fun a ha => ?_)
    rcases orth_or_twin hodd hX (hi a ha) (hXc a ha) with h | h
    · exact h x hx
    · exfalso
      by_cases h1 : a + 1 < r
      · refine ne_of_distinguish hodd hdim hX (hi a ha) (hi (a + 1) h1) ?_ ?_ ?_ ?_ ?_ h
        · intro e
          apply nc a h1
          have := hXc a ha
          rw [← e] at this
          exact this.symm
        · exact fun e => (hc.adj a h1).1 e.symm
        · exact modelInvComm_of_commutes hodd (hi (a + 1) h1) hX (hXc (a + 1) h1).symm
        · exact (ModelInvComm.of_adj (hc.adj a h1)).symm'
        · intro hiff
          exact nc a h1 (hiff.mp (hXc (a + 1) h1).symm).symm
      · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        refine ne_of_distinguish hodd hdim hX (hi (a' + 1) ha) (hi a' (by omega)) ?_ ?_ ?_ ?_ ?_ h
        · intro e
          have := hXc (a' + 1) ha
          rw [← e] at this
          exact nc a' (by omega) this
        · exact fun e => (hc.adj a' (by omega)).1 e
        · exact modelInvComm_of_commutes hodd (hi a' (by omega)) hX (hXc a' (by omega)).symm
        · exact ModelInvComm.of_adj (hc.adj a' (by omega))
        · intro hiff
          exact nc a' (by omega) (hiff.mp (hXc a' (by omega)).symm)
  have hspan := finrank_chainSpan hodd hdim hr hc hi r (by omega) le_rfl
  obtain ⟨cm, N, C⟩ := adj_data hodd hdim hiA hiB hAB
  have pd := (lemma_6_10 hodd hiA hiB cm N C).1
  have hAB6 : Module.finrank K ↥(negSpace iA ⊔ negSpace iB) = 6 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (negSpace iA) (negSpace iB)
    rw [pd.finrank_U₂, finrank_negSpace hodd hiA, finrank_negSpace hodd hiB] at this
    omega
  have hle : negSpace iA ⊔ negSpace iB ≤ LinearMap.BilinForm.orthogonal (polarBilin Q)
      (chainSpan i r) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      show polarBilin Q y x = 0
      rw [polarBilin_apply_apply, polar_comm]
      exact horthX A iA hiA hAc x hx y hy
    · rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      show polarBilin Q y x = 0
      rw [polarBilin_apply_apply, polar_comm]
      exact horthX B iB hiB hBc x hx y hy
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal hQ (chainSpan i r)
  have h3 : Module.finrank K ↥(chainSpan i r) ≤ Module.finrank K V := Submodule.finrank_le _
  omega

end Geometry

section Transfer

variable {KY X : Type} [Group KY] [Group X] {π : KY →* X} {𝓕 : Set (Subgroup KY)}
  {𝓕' : Set (Subgroup X)} {Z' : Subgroup X}

theorem CentralQuot.chainBound (h : CentralQuot π 𝓕 𝓕' Z') {d : ℕ} (hb : ChainBound Z' 𝓕' d) :
    ChainBound (Subgroup.center KY) 𝓕 d := by
  intro r hr c hc A hA B hB hAB hAc hBc
  refine hb r hr (fun a => (c a).map π) ⟨?_, ?_, ?_⟩ (A.map π) (h.map_mem A hA) (B.map π)
    (h.map_mem B hB) (h.modelAdj hA hB hAB) ?_ ?_
  · intro a ha
    exact h.map_mem _ (hc.mem a ha)
  · intro a ha
    exact h.modelAdj (hc.mem a (by omega)) (hc.mem (a + 1) ha) (hc.adj a ha)
  · intro a b hab hb'
    exact (h.commutes_iff (hc.mem a (by omega))).mpr (hc.comm a b hab hb')
  · intro a ha
    exact (h.commutes_iff hA).mpr (hAc a ha)
  · intro a ha
    exact (h.commutes_iff hB).mpr (hBc a ha)

end Transfer

end CFSG.ClassicalInvolution.RouteD.Gaps
