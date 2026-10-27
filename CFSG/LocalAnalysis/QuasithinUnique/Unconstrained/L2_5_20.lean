module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Delta
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20A6Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Small

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Helpers

variable {G : Type} [Group G]

theorem isComponentIn_centralizer_conj {A : Subgroup G} {i j : G} (g : G) (hij : g⁻¹ * i * g = j)
    (h : IsComponentIn A (Subgroup.centralizer ({i} : Set G))) :
    IsComponentIn (CFSG.conjugate A g) (Subgroup.centralizer ({j} : Set G)) := by
  have h1 := BenderBranch.isComponentIn_map (MulAut.conj g⁻¹) h
  have hf : ∀ y : G, (MulAut.conj g⁻¹).toMonoidHom y = g⁻¹ * y * g := fun y => by
    simp
  have hC : (Subgroup.centralizer ({i} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
      Subgroup.centralizer ({j} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hiy := Subgroup.mem_centralizer_iff.mp hy i (Set.mem_singleton i)
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      rw [Set.mem_singleton_iff] at hz
      rw [hz, hf, ← hij]
      calc (g⁻¹ * i * g) * (g⁻¹ * y * g) = g⁻¹ * (i * y) * g := by group
        _ = g⁻¹ * (y * i) * g := by rw [hiy]
        _ = (g⁻¹ * y * g) * (g⁻¹ * i * g) := by group
    · intro hx
      refine ⟨g * x * g⁻¹, ?_, ?_⟩
      · have hx' := Subgroup.mem_centralizer_iff.mp hx j (Set.mem_singleton j)
        refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        have hj_eq : j = g⁻¹ * i * g := hij.symm
        rw [hj_eq] at hx'
        calc i * (g * x * g⁻¹) = g * ((g⁻¹ * i * g) * x) * g⁻¹ := by group
          _ = g * (x * (g⁻¹ * i * g)) * g⁻¹ := by rw [hx']
          _ = (g * x * g⁻¹) * i := by group
      · rw [hf]; group
  rw [hC] at h1
  exact h1

theorem orderOf_ne_one_of_two {i : G} (hi : orderOf i = 2) : i ≠ 1 ∧ i ^ 2 = 1 :=
  ⟨fun e => by rw [e] at hi; simp at hi, by rw [← hi]; exact pow_orderOf_eq_one i⟩

end Helpers

theorem lemma2520_of_facts (hL2p : L2pFacts) (hA6 : A6RankFacts) : Lemma2520 := by
  intro G _ _ T M hs N t zK h
  by_contra hne
  have hne' : ¬ N.K0 = N.K := hne
  obtain ⟨s₀, hs₀S, hne₁, hK0, hcomm⟩ := (h.facts254.shape).resolve_left hne'
  set K₂ : Subgroup G := CFSG.conjugate N.K s₀ with hK₂
  have he : CFSG.Assembly.evenRank G ≤ 2 := hs.setting.qtke.2.2
  have hAB : ∀ a ∈ N.K, ∀ b ∈ K₂, a * b = b * a := fun a ha b hb =>
    BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
  let e : ↥N.K ≃* ↥K₂ := Subgroup.equivMapOfInjective N.K (MulAut.conj s₀⁻¹).toMonoidHom
    (MulAut.conj s₀⁻¹).injective
  have hs₀inv : s₀⁻¹ ∈ N.S := N.S.inv_mem hs₀S
  have main : IsL2pType ↥N.K → False := by
    intro hKtype
    have hK₂type : IsL2pType ↥K₂ := by
      rcases hKtype with ⟨p, hp, h7, hm⟩ | hm
      · exact Or.inl ⟨p, hp, h7, Unc25Small.statedClassicalModel_psl_of_mulEquiv e.symm hm⟩
      · exact Or.inr (Unc25Small.statedClassicalModel_psl_of_mulEquiv e.symm hm)
    have hA : L2pAmb N.K := L2pAmb.of_data _ (hL2p _ hKtype)
    have hB : L2pAmb K₂ := L2pAmb.of_data _ (hL2p _ hK₂type)
    have hSA : IsSylowTwoOf (N.S ⊓ N.K) N.K := N.SK_sylow
    have hSB : IsSylowTwoOf (N.S ⊓ K₂) K₂ := by
      have h1 := N.SK_sylow.map_equiv (MulAut.conj s₀⁻¹)
      have hS : CFSG.conjugate N.S s₀ = N.S :=
        BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hs₀S)
      have h2 : IsSylowTwoOf (CFSG.conjugate (N.S ⊓ N.K) s₀) (CFSG.conjugate N.K s₀) := h1
      rwa [BenderBranch.conjugate_inf, hS] at h2
    have hcomp0 : ∀ i ∈ N.S ⊓ Subgroup.centralizer (N.K : Set G), i ≠ 1 → i ^ 2 = 1 →
        IsComponentIn N.K (Subgroup.centralizer ({i} : Set G)) := by
      intro i hi hi1 hi2
      by_contra hnc
      exact hne' (h.concl2519 i hi hi1 hi2 hnc).1
    have hcompAB : ∀ i ∈ K₂, orderOf i = 2 →
        IsComponentIn N.K (Subgroup.centralizer ({i} : Set G)) := by
      intro i hiB hi
      refine isComponentIn_of_conj_into_sylow (A := N.K) (B := K₂) (S := N.S) hSB hAB ?_ hiB hi
      intro j hj hjo
      refine hcomp0 j ⟨hj.1, ?_⟩ (orderOf_ne_one_of_two hjo).1 (orderOf_ne_one_of_two hjo).2
      exact Subgroup.mem_centralizer_iff.mpr fun k hk => hAB k hk j hj.2
    have hcompBA : ∀ j ∈ N.K, orderOf j = 2 →
        IsComponentIn K₂ (Subgroup.centralizer ({j} : Set G)) := by
      intro i hiB hi
      refine isComponentIn_of_conj_into_sylow (A := K₂) (B := N.K) (S := N.S)
        hSA (fun a ha b hb => (hAB b hb a ha).symm) ?_ hiB hi
      intro j hj hjo
      have hjK : j ∈ N.K := hj.2
      have hio : orderOf (s₀ * j * s₀⁻¹) = 2 := by rw [orderOf_conj_mul]; exact hjo
      have hmem : s₀ * j * s₀⁻¹ ∈ N.S ⊓ Subgroup.centralizer (N.K : Set G) := by
        refine ⟨N.S.mul_mem (N.S.mul_mem hs₀S hj.1) hs₀inv, ?_⟩
        refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
        have hx : s₀⁻¹ * k * s₀ ∈ K₂ := by
          rw [hK₂, BenderBranch.mem_conjugate_iff]
          have : s₀ * (s₀⁻¹ * k * s₀) * s₀⁻¹ = k := by group
          rw [this]; exact hk
        have hcj := hAB j hjK _ hx
        calc k * (s₀ * j * s₀⁻¹) = s₀ * ((s₀⁻¹ * k * s₀) * j) * s₀⁻¹ := by group
          _ = s₀ * (j * (s₀⁻¹ * k * s₀)) * s₀⁻¹ := by rw [← hcj]
          _ = (s₀ * j * s₀⁻¹) * k := by group
      have hc := hcomp0 _ hmem (orderOf_ne_one_of_two hio).1 (orderOf_ne_one_of_two hio).2
      exact isComponentIn_centralizer_conj s₀ (by group) hc
    have hs₀N : s₀ ∈ Subgroup.normalizer ((N.K ⊔ K₂ : Subgroup G) : Set G) := by
      rw [← hK0]
      exact N.H_le_normalizer_K0 (N.S_le_H hs₀S)
    have hT : IsPGroup 2 T := hs.setting.sylow.isPGroup
    have hTN := T_le_normalizer he hs₀S hs₀N rfl hA hB hAB hcompAB hcompBA hSA hSB hT N.S_le_T
    rw [← hK0] at hTN
    set D : Subgroup G := T ⊓ Subgroup.centralizer (N.K0 : Set G) with hD
    have hDbot : D ≠ ⊥ := by
      intro e'
      apply N.SC_ne_bot
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ D := ⟨N.S_le_T hx.1, hx.2⟩
      rw [e'] at this
      exact this
    have hDp : IsPGroup 2 D := hT.to_le inf_le_left
    have hTD : T ≤ Subgroup.normalizer (D : Set G) := fun t ht => by
      rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
      have h1 : CFSG.conjugate T t = T :=
        BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer ht)
      have h2 : CFSG.conjugate (Subgroup.centralizer (N.K0 : Set G)) t =
          Subgroup.centralizer (N.K0 : Set G) := by
        rw [BenderBranch.conjugate_centralizer]
        have : CFSG.conjugate N.K0 t = N.K0 :=
          BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (hTN ht)
        rw [this]
      rw [hD, BenderBranch.conjugate_inf, h1, h2]
    have hK0D : N.K0 ≤ Subgroup.normalizer (D : Set G) := fun k hk =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun d hd =>
        (Subgroup.mem_centralizer_iff.mp hd.2 k hk).symm)
    have hloc : IsTwoLocal (Subgroup.normalizer (D : Set G)) := ⟨D, hDbot, hDp, rfl⟩
    have hLM := hs.setting.le_of_isTwoLocal_of_isSylowTwoOf_M hs.setting.isSylowTwoOf_M hloc hTD
    apply N.tuple.gamma0.isGamma.not_le
    rw [N.H_eq_K0_sup_S]
    exact sup_le (hK0D.trans hLM) (N.S_le_T.trans (hTD.trans hLM))
  rcases h.concl2516 with h1 | ⟨h2, -⟩ | ⟨h3, -⟩
  · exact main (Or.inl h1)
  · exact main (Or.inr h2)
  · exact false_of_A6_pair he hA6 (A := N.K) (B := K₂) h3 ⟨e.symm.trans h3.some⟩ hAB

theorem lemma2520 (hL2p : L2pFacts) : Lemma2520 :=
  lemma2520_of_facts hL2p a6RankFacts

end CFSG.QuasithinUnique
