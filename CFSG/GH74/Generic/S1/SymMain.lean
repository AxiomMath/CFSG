module

public import CFSG.GH74.Generic.S1.SymFrame
public import CFSG.GH74.Generic.S1.SymOpsLin
public import CFSG.GH74.Generic.S1.SymOpsUni
public import CFSG.GH74.Generic.S1.SymClass
public import CFSG.GH74.Generic.S1.SymProd

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sym_hyps {x : G} {K : Subgroup (CentralizerBar x)} (hxK : xbar x ∈ K) (hx : orderOf x = 2)
    {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu)
    (i : Fin 5) :
    IsConj x (symX x u i) ∧
      (∀ j, symX x u (i.succAbove j) ∈ centralizer ({symX x u i} : Set G)) ∧
        (∀ j, symX x u (i.succAbove j) * symX x u (i.succAbove j) = 1) ∧
          (∀ j k, symX x u (i.succAbove j) * symX x u (i.succAbove k) =
            symX x u (i.succAbove k) * symX x u (i.succAbove j)) ∧
            (∀ j, IsConj (symX x u i) (symX x u (i.succAbove j))) ∧
              (∀ j, symX x u (i.succAbove j) ≠ symX x u i) ∧
                (∀ j k, j ≠ k → symX x u (i.succAbove j) * symX x u (i.succAbove k) ≠ 1) ∧
                  (∀ j k, j ≠ k → symX x u (i.succAbove j) * symX x u (i.succAbove k) *
                    symX x u i ≠ 1) ∧
                    symX x u (i.succAbove 0) * symX x u (i.succAbove 1) * symX x u (i.succAbove 2) *
                      symX x u (i.succAbove 3) = symX x u i := by
  obtain ⟨hconj, hX2, hXc, hX1, hXd⟩ := symX_facts hxK hx hf
  refine ⟨hconj i, fun j => mem_centralizer_singleton_iff.2 (hXc _ _), fun j => hX2 _,
    fun j k => hXc _ _, fun j => (hconj i).symm.trans (hconj _),
    fun j => hXd _ _ (Fin.succAbove_ne i j), ?_, ?_, five_prod_succAbove _ hXc hX2 hX1 i⟩
  · intro j k hjk h1
    apply hXd _ _ (fun h => hjk (Fin.succAbove_right_injective h))
    calc symX x u (i.succAbove j) = symX x u (i.succAbove j) * (symX x u (i.succAbove k) *
          symX x u (i.succAbove k)) := by rw [hX2, mul_one]
      _ = (symX x u (i.succAbove j) * symX x u (i.succAbove k)) * symX x u (i.succAbove k) :=
          (mul_assoc _ _ _).symm
      _ = symX x u (i.succAbove k) := by rw [h1, one_mul]
  · intro j k hjk
    exact five_triple_ne_one _ hXc hX2 hX1 hXd
      (fun h => hjk (Fin.succAbove_right_injective h)) (Fin.succAbove_ne i j).symm.symm
      (Fin.succAbove_ne i k).symm.symm

theorem s1_symFrame_lin (hExo : S1ExoticExcludedExplicit) {x : G}
    {K : Subgroup (CentralizerBar x)} [K.Normal] (hset : S1Setup G x K) (hfront : S1Front G x K)
    {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3) (e : ↥K ≃* ↥(StatedSL 4 F)) :
    S1SymFrameLin x u F := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd
  intro i
  obtain ⟨hy, hw, hw2, hwc, hwconj, hwne, hind2, hind3, hprod⟩ :=
    sym_hyps hset.shape.2 hset.inv hf i
  obtain ⟨K', hset', hfront', h1, h2', h3, h4, e'', he''⟩ :=
    sym_at hset hfront (linOps h2) e
      (fun y K' _ hs hfr e' v hv hc hvy hv2 hvK => outer_reflection_lin hExo hs hfr hv hc hvy hv2 hvK hF e')
      hy (fun j => symX x u (i.succAbove j)) hw hw2 hwc hwconj hwne hind2 hind3 hprod
  exact ⟨K', hw, hset', hfront', ⟨h1, h2', h3, h4, Or.inl ⟨F, inferInstance, inferInstance, e'', hF,
    he''⟩⟩, e'', he''⟩

theorem s1_symFrame_uni (hExo : S1ExoticExcludedExplicit) {x : G}
    {K : Subgroup (CentralizerBar x)} [K.Normal] (hset : S1Setup G x K) (hfront : S1Front G x K)
    {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu)
    {q : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1)
    (e : ↥K ≃* ↥(StatedSU 4 q F)) : S1SymFrameUni x u q F := by
  intro i
  obtain ⟨hy, hw, hw2, hwc, hwconj, hwne, hind2, hind3, hprod⟩ :=
    sym_hyps hset.shape.2 hset.inv hf i
  obtain ⟨K', hset', hfront', h1, h2', h3, h4, e'', he''⟩ :=
    sym_at hset hfront (uniOps hF hq) e
      (fun y K' _ hs hfr e' v hv hc hvy hv2 hvK => outer_reflection_uni hExo hs hfr hv hc hvy hv2 hvK hF hq e')
      hy (fun j => symX x u (i.succAbove j)) hw hw2 hwc hwconj hwne hind2 hind3 hprod
  exact ⟨K', hw, hset', hfront', ⟨h1, h2', h3, h4, Or.inr ⟨q, F, inferInstance, inferInstance, e'', hF,
    hq, he''⟩⟩, e'', he''⟩

theorem s1_symFrame (hExo : S1ExoticExcludedExplicit) {x : G} {K : Subgroup (CentralizerBar x)}
    [K.Normal] (hset : S1Setup G x K) (hfront : S1Front G x K) {u : Fin 4 → G}
    {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu) : S1SymFrame x u := by
  have hmodel := hf.2.2.2.2
  rcases hmodel with ⟨F, _, _, e, hF, -⟩ | ⟨q, F, _, _, e, hF, hq, -⟩
  · exact Or.inl ⟨F, inferInstance, inferInstance, hF, s1_symFrame_lin hExo hset hfront hf hF e⟩
  · exact Or.inr ⟨q, F, inferInstance, inferInstance, hF, hq,
      s1_symFrame_uni hExo hset hfront hf hF hq e⟩

@[expose] def S1NbhdSym : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → S1SymFrame x u → ∃ J : Fin 4 → Subgroup G, IsS1A4 x K J

theorem s1Nbhd_of_sym (hExo : S1ExoticExcludedExplicit) (h : S1NbhdSym) : S1Nbhd := by
  intro G _ _ x K hset hfront u hu hf
  have : K.Normal := normal_of_layer_eq hfront.layer_eq
  exact h G x K hset hfront u hu hf (s1_symFrame hExo hset hfront hf)

end CFSG.GH74.Generic.S1
