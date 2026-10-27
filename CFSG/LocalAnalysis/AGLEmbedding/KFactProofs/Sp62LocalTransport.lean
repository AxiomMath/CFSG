module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Data

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Klingen

variable {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] {p : ℕ} [Fact p.Prime]

theorem hasKlingenData_of_mulEquiv (f : X ≃* Y) {T : Sylow p X} {T' : Sylow p Y}
    (hT : (T' : Subgroup Y) = (T : Subgroup X).map f.toMonoidHom) {X₀ : Subgroup X}
    (h : HasKlingenData p T X₀) : HasKlingenData p T' (X₀.map f.toMonoidHom) := by
  obtain ⟨E, D, L, hET, hEcard, hEexp, hZE, hDE, hDel, hDcard, hDC, hDN, hLC, hLX₀, e, hSL⟩ := h
  have hinj : Function.Injective f.toMonoidHom := f.injective
  let φ : E ≃* E.map f.toMonoidHom := Subgroup.equivMapOfInjective E f.toMonoidHom hinj
  have hφ : ∀ u : E, ((φ u : E.map f.toMonoidHom) : Y) = f.toMonoidHom (u : X) := fun _ => rfl
  have hZmap : ∀ w : Subgroup.center (E.map f.toMonoidHom), ∃ z : Subgroup.center E,
      ((w : E.map f.toMonoidHom) : Y) = f.toMonoidHom ((z : E) : X) := by
    intro w
    refine ⟨(Subgroup.centerCongr φ).symm w, ?_⟩
    rw [← hφ]
    congr 2
    exact (congrArg Subtype.val ((Subgroup.centerCongr φ).apply_symm_apply w)).symm
  refine ⟨E.map f.toMonoidHom, D.map f.toMonoidHom, L.map f.toMonoidHom,
    (Subgroup.map_mono hET).trans hT.ge, ?_, ?_, ?_, Subgroup.map_mono hDE,
    PreuniquenessRankFour.Helpers.elementary_abelian_map p hDel f.toMonoidHom, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hEcard]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hEexp x hx, map_one]
  · rw [← hZE]
    exact (Nat.card_congr (Subgroup.centerCongr φ).toEquiv).symm
  · rw [Subgroup.card_map_of_injective hinj, hDcard]
  · rintro _ ⟨d, hd, rfl⟩ hdT
    have hdT' : d ∈ Subgroup.centralizer ((T : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      apply hinj
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hdT (f.toMonoidHom t) (hT.ge ⟨t, ht, rfl⟩)
    obtain ⟨z, hz, hzd⟩ := hDC d hd hdT'
    refine ⟨Subgroup.centerCongr φ ⟨z, hz⟩, (Subgroup.centerCongr φ ⟨z, hz⟩).2, ?_⟩
    show (((Subgroup.centerCongr φ ⟨z, hz⟩ : Subgroup.center (E.map f.toMonoidHom)) :
        E.map f.toMonoidHom) : Y) = f.toMonoidHom d
    rw [← hzd]
    rfl
  · intro hle
    apply hDN
    intro x hx
    have h1 : f.toMonoidHom x ∈ (Subgroup.normalizer (D : Set X)).map f.toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    have h2 := hle (Subgroup.le_normalizer_map _ h1)
    exact (Subgroup.mem_map_iff_mem hinj).1 h2
  · rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨z, hz⟩ := hZmap ⟨w, hw⟩
    have hlz := Subgroup.mem_centralizer_iff.mp (hLC hl) ((z : E) : X) ⟨z, z.2, rfl⟩
    show ((w : E.map f.toMonoidHom) : Y) * f.toMonoidHom l =
      f.toMonoidHom l * ((w : E.map f.toMonoidHom) : Y)
    have hz' : ((w : E.map f.toMonoidHom) : Y) = f.toMonoidHom ((z : E) : X) := hz
    rw [hz', ← map_mul, ← map_mul, hlz]
  · intro hle
    apply hLX₀
    intro x hx
    exact (Subgroup.mem_map_iff_mem hinj).1 (hle (Subgroup.mem_map_of_mem _ hx))
  · refine ⟨_, statedSL_le_map_centerQuotientAction_of_mulEquiv φ e hSL ?_⟩
    intro g hgL hgN
    refine ⟨f.toMonoidHom g, Subgroup.mem_map_of_mem _ hgL,
      Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hgN), ?_⟩
    intro u v huv
    rw [hφ, hφ, huv, map_mul, map_mul, map_inv]

end Klingen

section InSitu

variable {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]

theorem Sp62InSitu.of_mulEquiv (f : X ≃* Y) {T Y₀ V₀ : Subgroup X}
    (h : Sp62InSitu (T.map f.toMonoidHom) (Y₀.map f.toMonoidHom) (V₀.map f.toMonoidHom)) :
    Sp62InSitu T Y₀ V₀ := by
  have hinj : Function.Injective f.toMonoidHom := f.injective
  have hmap_le : ∀ {A B : Subgroup X}, A.map f.toMonoidHom ≤ B.map f.toMonoidHom → A ≤ B :=
    fun h => (Subgroup.map_le_map_iff_of_injective hinj).1 h
  have hnorm : ∀ {A B : Subgroup X}, A ≤ Subgroup.normalizer (B : Set X) ↔
      A.map f.toMonoidHom ≤ Subgroup.normalizer ((B.map f.toMonoidHom : Subgroup Y) : Set Y) := by
    intro A B
    constructor
    · intro hA y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
      exact Subgroup.le_normalizer_map f.toMonoidHom (Subgroup.mem_map_of_mem _ (hA ha))
    · intro hA a ha
      have h1 := hA (Subgroup.mem_map_of_mem f.toMonoidHom ha)
      rw [Subgroup.mem_normalizer_iff] at h1 ⊢
      intro b
      have h2 := h1 (f.toMonoidHom b)
      rw [Subgroup.mem_map_iff_mem hinj, ← map_inv, ← map_mul, ← map_mul,
        Subgroup.mem_map_iff_mem hinj] at h2
      exact h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective hinj]
    exact h.card_T
  · exact hmap_le h.T_le
  · exact hmap_le h.V_le
  · apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator]
    exact h.V_perfect
  · exact (hnorm).2 h.V_normal
  · have := h.V_index
    rwa [Subgroup.relIndex_map_map_of_injective _ _ hinj] at this
  · obtain ⟨d, ψ, hd, hψ⟩ := h.V_iso
    exact ⟨d, ψ.comp (Subgroup.equivMapOfInjective V₀ f.toMonoidHom hinj).toMonoidHom, hd,
      hψ.comp (Subgroup.equivMapOfInjective V₀ f.toMonoidHom hinj).bijective⟩
  · intro W hW hN
    rcases h.V_quasi (W.map f.toMonoidHom) (Subgroup.map_mono hW) ((hnorm).1 hN) with h1 | h1
    · exact Or.inl (hmap_le h1)
    · right
      apply Subgroup.map_injective hinj
      rw [Subgroup.map_commutator, Subgroup.map_bot]
      exact h1
  · have h1 := h.V_centralizer
    rw [eq_bot_iff] at h1 ⊢
    intro x hx
    have hx' : f.toMonoidHom x ∈ Y₀.map f.toMonoidHom ⊓
        Subgroup.centralizer ((V₀.map f.toMonoidHom : Subgroup Y) : Set Y) := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.1 hx).1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 v hv)
    have := h1 hx'
    rw [Subgroup.mem_bot] at this ⊢
    exact hinj (this.trans (map_one _).symm)
  · intro W hW hN
    rcases h.dichotomy (W.map f.toMonoidHom) (Subgroup.map_mono hW) ((hnorm).1 hN) with h1 | h1
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h1
    · exact Or.inr (hmap_le h1)
  · intro x hx
    have hx' : f.toMonoidHom x ∈ Y₀.map f.toMonoidHom ⊓
        Subgroup.centralizer ((T.map f.toMonoidHom : Subgroup Y) : Set Y) := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.1 hx).1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 v hv)
    exact (Subgroup.mem_map_iff_mem hinj).1 (h.centralizer_le hx')

end InSitu

end CFSG.AGLEmbedding
