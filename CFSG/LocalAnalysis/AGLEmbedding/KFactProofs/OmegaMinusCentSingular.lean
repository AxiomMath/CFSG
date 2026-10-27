module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentBasic

public section

namespace CFSG.AGLEmbedding.OmegaMinusCent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

namespace AnisoPair

variable {P P' : AnisoPair Q}

def sing (P P' : AnisoPair Q) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {P.a + P'.a, P.b + P'.b}

theorem Orth.map_a_add (h : P.Orth P') : Q (P.a + P'.a) = 0 := by
  rw [QuadraticMap.map_add Q, P.Q_a, P'.Q_a, h.aa]
  decide

theorem Orth.map_b_add (h : P.Orth P') : Q (P.b + P'.b) = 0 := by
  rw [QuadraticMap.map_add Q, P.Q_b, P'.Q_b, h.bb]
  decide

theorem Orth.polar_add (h : P.Orth P') : polar Q (P.a + P'.a) (P.b + P'.b) = 0 := by
  have hba : polar Q P'.a P.b = 0 := by rw [polar_comm]; exact h.ba
  rw [polar_add_left, polar_add_right, polar_add_right, P.polar_ab, h.ab, hba, P'.polar_ab]
  decide

theorem Orth.map_eq_zero_of_mem_sing (h : P.Orth P') {y : V} (hy : y ∈ P.sing P') : Q y = 0 := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hy
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, h.map_a_add,
    h.map_b_add, polar_smul_left_eq, polar_smul_right_eq, h.polar_add]
  simp

theorem polar_eq_zero_of_mem_sing {y w : V} (hy : y ∈ P.sing P')
    (h1 : polar Q P.a w = 0) (h2 : polar Q P.b w = 0) (h3 : polar Q P'.a w = 0)
    (h4 : polar Q P'.b w = 0) : polar Q y w = 0 := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hy
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_add_left, polar_add_left, h1,
    h2, h3, h4]
  simp

theorem Orth.polar_sing_coords (h : P.Orth P') (s t : ZMod 2) :
    polar Q (s • (P.a + P'.a) + t • (P.b + P'.b)) P.b = s ∧
      polar Q (s • (P.a + P'.a) + t • (P.b + P'.b)) P.a = t := by
  have h1 : polar Q P'.a P.b = 0 := by rw [polar_comm]; exact h.ba
  have h2 : polar Q P'.b P.b = 0 := by rw [polar_comm]; exact h.bb
  have h3 : polar Q P'.a P.a = 0 := by rw [polar_comm]; exact h.aa
  have h4 : polar Q P'.b P.a = 0 := by rw [polar_comm]; exact h.ab
  constructor
  · simp only [polar_add_left, polar_smul_left_eq, P.polar_ab, h1, P.polar_bb, h2]
    simp
  · simp only [polar_add_left, polar_smul_left_eq, P.polar_aa, h3, P.polar_ba, h4]
    simp

theorem Orth.eq_zero_of_mem_sing (h : P.Orth P') {y : V} (hy : y ∈ P.sing P')
    (h1 : polar Q P.a y = 0) (h2 : polar Q P.b y = 0) : y = 0 := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hy
  obtain ⟨hs, ht⟩ := h.polar_sing_coords s t
  rw [polar_comm] at h1 h2
  rw [h1] at ht
  rw [h2] at hs
  rw [← hs, ← ht]
  simp

theorem Orth.linearIndependent_sing (h : P.Orth P') :
    LinearIndependent (ZMod 2) ![P.a + P'.a, P.b + P'.b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  obtain ⟨hs, ht⟩ := h.polar_sing_coords s t
  rw [hst] at hs ht
  rw [polar_zero_left] at hs ht
  exact ⟨hs.symm, ht.symm⟩

theorem Orth.finrank_sing (h : P.Orth P') : finrank (ZMod 2) (P.sing P') = 2 := by
  rw [AnisoPair.sing, ← Matrix.range_cons_cons_empty (P.a + P'.a) (P.b + P'.b) ![],
    finrank_span_eq_card h.linearIndependent_sing, Fintype.card_fin]

theorem Orth.totSing_sup_sing [FiniteDimensional (ZMod 2) V] (h : P.Orth P')
    {T₀ : Submodule (ZMod 2) V} (hT₀ : ∀ y ∈ T₀, Q y = 0)
    (hP : ∀ y ∈ T₀, polar Q P.a y = 0 ∧ polar Q P.b y = 0)
    (hP' : ∀ y ∈ T₀, polar Q P'.a y = 0 ∧ polar Q P'.b y = 0) :
    (∀ y ∈ T₀ ⊔ P.sing P', Q y = 0) ∧
      finrank (ZMod 2) ↥(T₀ ⊔ P.sing P') = finrank (ZMod 2) T₀ + 2 := by
  constructor
  · intro y hy
    obtain ⟨t, ht, s, hs, rfl⟩ := Submodule.mem_sup.1 hy
    have hst : polar Q s t = 0 :=
      polar_eq_zero_of_mem_sing hs (hP t ht).1 (hP t ht).2 (hP' t ht).1 (hP' t ht).2
    rw [QuadraticMap.map_add Q, hT₀ t ht, h.map_eq_zero_of_mem_sing hs, polar_comm, hst]
    simp
  · have hinf : T₀ ⊓ P.sing P' = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      exact (Submodule.mem_bot _).2 (h.eq_zero_of_mem_sing hy2 (hP y hy1).1 (hP y hy1).2)
    have := Submodule.finrank_sup_add_finrank_inf_eq T₀ (P.sing P')
    rw [hinf, finrank_bot, h.finrank_sing] at this
    omega

end AnisoPair

theorem exists_totSing_of_pairs [FiniteDimensional (ZMod 2) V] :
    ∀ (Ps : List (AnisoPair Q)) (T₀ : Submodule (ZMod 2) V), (∀ y ∈ T₀, Q y = 0) →
      Ps.Pairwise AnisoPair.Orth →
      (∀ y ∈ T₀, ∀ P ∈ Ps, polar Q P.a y = 0 ∧ polar Q P.b y = 0) →
      ∃ T : Submodule (ZMod 2) V, (∀ y ∈ T, Q y = 0) ∧
        finrank (ZMod 2) T₀ + 2 * (Ps.length / 2) ≤ finrank (ZMod 2) T
  | [], T₀, hT₀, _, _ => ⟨T₀, hT₀, by simp⟩
  | [_], T₀, hT₀, _, _ => ⟨T₀, hT₀, by simp⟩
  | P :: P' :: Ps, T₀, hT₀, hpw, hT => by
    obtain ⟨hPR, hpw₁⟩ := List.pairwise_cons.1 hpw
    obtain ⟨hP'R, hpw₂⟩ := List.pairwise_cons.1 hpw₁
    have hPP' : P.Orth P' := hPR P' List.mem_cons_self
    obtain ⟨hQ, hrk⟩ := hPP'.totSing_sup_sing hT₀
      (fun y hy => hT y hy P List.mem_cons_self)
      (fun y hy => hT y hy P' (List.mem_cons_of_mem _ List.mem_cons_self))
    have hperp : ∀ y ∈ T₀ ⊔ P.sing P', ∀ R ∈ Ps, polar Q R.a y = 0 ∧ polar Q R.b y = 0 := by
      intro y hy R hR
      obtain ⟨t, ht, s, hs, rfl⟩ := Submodule.mem_sup.1 hy
      have hPR' := hPR R (List.mem_cons_of_mem _ hR)
      have hP'R' := hP'R R hR
      have ht' := hT t ht R (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR))
      constructor
      · have := AnisoPair.polar_eq_zero_of_mem_sing hs hPR'.aa hPR'.ba hP'R'.aa hP'R'.ba
        rw [polar_add_right, ht'.1, polar_comm, this]
        simp
      · have := AnisoPair.polar_eq_zero_of_mem_sing hs hPR'.ab hPR'.bb hP'R'.ab hP'R'.bb
        rw [polar_add_right, ht'.2, polar_comm, this]
        simp
    obtain ⟨T, hTs, hle⟩ := exists_totSing_of_pairs Ps (T₀ ⊔ P.sing P') hQ hpw₂ hperp
    refine ⟨T, hTs, ?_⟩
    simp only [List.length_cons]
    omega

end CFSG.AGLEmbedding.OmegaMinusCent
