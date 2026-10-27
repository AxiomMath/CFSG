module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn

open CFSG.ComponentClassification.Burgoyne.U
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def IsDiagU (N : ℕ) (g : GL (Fin N) xunK) : Prop :=
  ∀ i j : Fin N, i ≠ j → (g : Matrix (Fin N) (Fin N) xunK) i j = 0

@[expose] def KD264XUnTorusStruct : Prop :=
  ∀ (N : ℕ) (hN : 9 ≤ N), 3 ∣ N → ∀ A : Subgroup (MulAut (xunM N)), IsElemAbelian 3 A →
    N - 2 ≤ CFSG.Open.pRank 3 A →
    ∃ c : uU xunH N, ∀ g : uU xunH N, xunConj N (by omega) g ∈ A →
      IsDiagU N ((c * g * c⁻¹ : uU xunH N) : GL (Fin N) xunK)

@[expose] def KD264XUnTorusGood : Prop :=
  ∀ (N : ℕ) (hN : 9 ≤ N), 3 ∣ N → ∀ A : Subgroup (MulAut (xunM N)), IsElemAbelian 3 A →
    N - 2 ≤ CFSG.Open.pRank 3 A →
    (∀ g : uU xunH N, xunConj N (by omega) g ∈ A → IsDiagU N (g : GL (Fin N) xunK)) →
    ∃ F ≤ A, IsElemAbelian 3 F ∧ 2 ≤ CFSG.Open.pRank 3 F ∧ IsGood 3 F

theorem mem_map_mulAut_congr {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (A : Subgroup (MulAut S)) (x : MulAut T) :
    x ∈ A.map (MulAut.congr e).toMonoidHom ↔ MulAut.congr e.symm x ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h : MulAut.congr e.symm (MulAut.congr e a) = a := by
      ext s
      simp [MulAut.congr_apply]
    change MulAut.congr e.symm (MulAut.congr e a) ∈ A
    rw [h]
    exact ha
  · intro hx
    refine ⟨MulAut.congr e.symm x, hx, ?_⟩
    ext t
    simp [MulAut.congr_apply]

theorem mulAut_congr_congr_symm {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (x : MulAut T) : MulAut.congr e (MulAut.congr e.symm x) = x := by
  ext t
  simp [MulAut.congr_apply]

theorem mulAut_congr_eq_conj {S : Type} [Group S] (ϕ f : MulAut S) :
    MulAut.congr ϕ f = ϕ * f * ϕ⁻¹ := by
  ext s
  rfl

theorem kd264XUnRow_of_pieces (hS : KD264XUnTorusStruct) (hG : KD264XUnTorusGood) :
    KD264XUnRow := by
  unfold KD264XUnRow
  intro d _ n q _ _ _ hd hq h3 h8 A hA hrank
  obtain ⟨idx, hv⟩ := d
  have hd' : idx = .twistedA n q := hd
  subst hd'
  obtain ⟨e0⟩ := nonempty_mulEquiv_xunM n q hv hq
  have hN9 : 9 ≤ n + 1 := by omega
  have hA' : IsElemAbelian 3 (A.map (MulAut.congr e0).toMonoidHom) :=
    isElemAbelian_map_of_injective (MulAut.congr e0).injective hA
  have hrank' : CFSG.Open.pRank 3 (A.map (MulAut.congr e0).toMonoidHom) =
      CFSG.Open.pRank 3 A :=
    pRank_map_of_injective Nat.prime_three (MulAut.congr e0).injective hA
  obtain ⟨c, hc⟩ := hS (n + 1) hN9 h3 _ hA' (by rw [hrank']; omega)
  set γ : MulAut (xunM (n + 1)) := xunConj (n + 1) (by omega) c with hγ
  set A' := A.map (MulAut.congr e0).toMonoidHom with hA'def
  set A'' := A'.map (MulAut.congr γ).toMonoidHom with hA''def
  have hA'' : IsElemAbelian 3 A'' :=
    isElemAbelian_map_of_injective (MulAut.congr γ).injective hA'
  have hrank'' : CFSG.Open.pRank 3 A'' = CFSG.Open.pRank 3 A' :=
    pRank_map_of_injective Nat.prime_three (MulAut.congr γ).injective hA'
  have hdiag : ∀ g : uU xunH (n + 1), xunConj (n + 1) (by omega) g ∈ A'' →
      IsDiagU (n + 1) (g : GL (Fin (n + 1)) xunK) := by
    intro g hg
    rw [hA''def, mem_map_mulAut_congr] at hg
    have hg' : xunConj (n + 1) (by omega) (c⁻¹ * g * c) ∈ A' := by
      have heq : xunConj (n + 1) (by omega) (c⁻¹ * g * c) =
          MulAut.congr γ.symm (xunConj (n + 1) (by omega) g) := by
        rw [mulAut_congr_eq_conj, map_mul, map_mul, map_inv, hγ]
        rfl
      rw [heq]
      exact hg
    have := hc (c⁻¹ * g * c) hg'
    have hcg : c * (c⁻¹ * g * c) * c⁻¹ = g := by group
    rw [hcg] at this
    exact this
  obtain ⟨F'', hF''A'', hF''el, hF''rank, hF''good⟩ :=
    hG (n + 1) hN9 h3 A'' hA'' (by rw [hrank'', hrank']; omega) hdiag
  have hF'A' : F''.map (MulAut.congr γ.symm).toMonoidHom ≤ A' := by
    intro x hx
    rw [mem_map_mulAut_congr] at hx
    have hx' := hF''A'' hx
    rw [hA''def, mem_map_mulAut_congr, mulAut_congr_congr_symm] at hx'
    exact hx'
  have hF'el : IsElemAbelian 3 (F''.map (MulAut.congr γ.symm).toMonoidHom) :=
    isElemAbelian_map_of_injective (MulAut.congr γ.symm).injective hF''el
  have hF'rank : CFSG.Open.pRank 3 (F''.map (MulAut.congr γ.symm).toMonoidHom) =
      CFSG.Open.pRank 3 F'' :=
    pRank_map_of_injective Nat.prime_three (MulAut.congr γ.symm).injective hF''el
  have hF'good : IsGood 3 (F''.map (MulAut.congr γ.symm).toMonoidHom) :=
    (isGood_iff_map_mulEquiv γ.symm F'').1 hF''good
  have hFA : (F''.map (MulAut.congr γ.symm).toMonoidHom).map (MulAut.congr e0.symm).toMonoidHom ≤
      A := by
    intro x hx
    rw [mem_map_mulAut_congr] at hx
    have hx' := hF'A' hx
    rw [hA'def, mem_map_mulAut_congr, mulAut_congr_congr_symm] at hx'
    exact hx'
  refine ⟨(F''.map (MulAut.congr γ.symm).toMonoidHom).map (MulAut.congr e0.symm).toMonoidHom,
    hFA, ?_, ?_, ?_⟩
  · exact isElemAbelian_map_of_injective (MulAut.congr e0.symm).injective hF'el
  · rw [pRank_map_of_injective Nat.prime_three (MulAut.congr e0.symm).injective hF'el, hF'rank]
    exact hF''rank
  · exact (isGood_iff_map_mulEquiv e0.symm _).1 hF'good

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn

end
