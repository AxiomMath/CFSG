module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableFam
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4Transport

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Transport

theorem k32_congr_conj {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (k : K) :
    MulAut.congr e (MulAut.conj k) = MulAut.conj (e k) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem k32_isSylowTwoOf_map_mulEquiv {Γ Γ' : Type} [Group Γ] [Group Γ'] [Finite Γ] [Finite Γ']
    (g : Γ ≃* Γ') {S X : Subgroup Γ} (h : IsSylowTwoOf S X) :
    IsSylowTwoOf (S.map g.toMonoidHom) (X.map g.toMonoidHom) := by
  rw [isSylowTwoOf_iff] at h ⊢
  obtain ⟨hSX, hS, hc⟩ := h
  refine ⟨Subgroup.map_mono hSX, ?_, ?_⟩
  · exact hS.of_equiv (Subgroup.equivMapOfInjective S g.toMonoidHom g.injective)
  · have h1 : Nat.card ↥(S.map g.toMonoidHom) = Nat.card ↥S :=
      Subgroup.card_map_of_injective g.injective
    have h2 : Nat.card ↥(X.map g.toMonoidHom) = Nat.card ↥X :=
      Subgroup.card_map_of_injective g.injective
    rw [h1, hc]
    unfold twoPart
    rw [h2]

variable {K K' : Type} [Group K] [Group K'] [Finite K] [Finite K']

theorem K32Datum.of_mulEquiv {X P R A V : Subgroup (MulAut K)} (e : K ≃* K')
    (h : K32Datum K X P R A V) :
    K32Datum K' (X.map (MulAut.congr e).toMonoidHom) (P.map (MulAut.congr e).toMonoidHom)
      (R.map (MulAut.congr e).toMonoidHom) (A.map (MulAut.congr e).toMonoidHom)
      (V.map (MulAut.congr e).toMonoidHom) := by
  set f : MulAut K ≃* MulAut K' := MulAut.congr e with hf
  have hnorm : ∀ {Y Z : Subgroup (MulAut K)}, Y ≤ Subgroup.normalizer (Z : Set (MulAut K)) →
      Y.map f.toMonoidHom ≤ Subgroup.normalizer ((Z.map f.toMonoidHom : Subgroup (MulAut K')) :
        Set (MulAut K')) := by
    intro Y Z hYZ
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨y₀, rfl⟩ : ∃ y₀, f y₀ = y := ⟨f.symm y, by simp⟩
    have h1 := Subgroup.mem_normalizer_iff.mp (hYZ hr) y₀
    constructor
    · rintro ⟨a, ha, hay⟩
      have hay' : a = y₀ := f.injective hay
      subst hay'
      exact ⟨r * a * r⁻¹, h1.mp ha, by simp⟩
    · rintro ⟨a, ha, hay⟩
      have : a = r * y₀ * r⁻¹ := by
        apply f.injective
        simpa using hay
      subst this
      exact ⟨y₀, h1.mpr ha, rfl⟩
  refine ⟨?_, k32_isSylowTwoOf_map_mulEquiv f h.sylow, ?_, Subgroup.map_mono h.A_le,
    Subgroup.map_mono h.V_le, Subgroup.map_mono h.R_le, hnorm h.R_norm, hnorm h.R_normV, ?_, ?_⟩
  ·
    rintro _ ⟨k', rfl⟩
    refine ⟨MulAut.conj (e.symm k'), h.inn_le ⟨e.symm k', rfl⟩, ?_⟩
    show MulAut.congr e (MulAut.conj (e.symm k')) = MulAut.conj k'
    rw [k32_congr_conj]
    simp
  · exact IsA4Block.map_of_injective h.a4 f.toMonoidHom f.injective
  · rw [Subgroup.relIndex_map_map_of_injective R P f.injective]
    exact h.idx
  · intro hcon
    apply h.moves
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := Subgroup.mem_centralizer_iff.mp (hcon ⟨r, hr, rfl⟩) (f v) ⟨v, hv, rfl⟩
    apply f.injective
    simpa using this

theorem k32NoDatum_of_mulEquiv (e : K ≃* K') (h : K32NoDatum K') : K32NoDatum K := by
  intro X P R A V hd
  exact h _ _ _ _ _ (hd.of_mulEquiv e)

end Transport

end CFSG.QuasithinUnique.DoubleA3
