module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421LQ1

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

namespace Lin2Hyp0

section LQ2

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem centralizer_S_Z_le_R (hc : centerOf L = ⊥) {s : G} (hs : s ∈ S)
    (hsC : ∀ z ∈ centerOf (thompsonJ S), s * z = z * s) : s ∈ thompsonJ S := by
  have hZR : lin2Z L (thompsonJ S) = centerOf (thompsonJ S) :=
    ((lin2Z_cases (Z := lin2Z L (thompsonJ S)) rfl).resolve_right fun h => h.1 hc).2
  obtain ⟨h17a, -⟩ := E.h17 G T M H S L D n hcfg (lin2Z L (thompsonJ S)) rfl
  rw [hZR] at h17a
  have hsT : s ∈ T := hcfg.S_le_T hs
  have hsCT : s ∈ T ⊓ Subgroup.centralizer (centerOf (thompsonJ S) : Set G) :=
    ⟨hsT, Subgroup.mem_centralizer_iff.2 fun z hz => (hsC z hz).symm⟩
  rcases h17a with h | ⟨-, t, htT, htS, ht2, hCT, -, -⟩
  · rw [h] at hsCT; exact hsCT
  · rw [hCT] at hsCT
    rcases mem_sup_zpowers_of_sq_eq_one (E.TnR hcfg htT) ht2 hsCT with h | ⟨r, hr, hsr⟩
    · exact h
    · exfalso
      apply htS
      have : t = r⁻¹ * s := by rw [hsr]; group
      rw [this]
      exact S.mul_mem (S.inv_mem ((thompsonJ_le_self S) hr)) hs

theorem isSylowTwoOf_R_inf (hc : centerOf L = ⊥) :
    IsSylowTwoOf (thompsonJ S)
      (Subgroup.normalizer (blockU L : Set G) ⊓
        Subgroup.centralizer (centerOf (thompsonJ S) : Set G)) := by
  have hRC : thompsonJ S ≤ Subgroup.centralizer (centerOf (thompsonJ S) : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.1 hh.2 y hy).symm
  have hR_le : thompsonJ S ≤ Subgroup.normalizer (blockU L : Set G) ⊓
      Subgroup.centralizer (centerOf (thompsonJ S) : Set G) :=
    le_inf (E.R_le_normalizer_U hcfg) hRC
  have hR2 : IsPGroup 2 (thompsonJ S) :=
    hcfg.sylowT.isPGroup.to_le ((thompsonJ_le_self S).trans hcfg.S_le_T)
  obtain ⟨P₁, hRP₁, hP₁⟩ := exists_isSylowTwoOf_of_le hR_le hR2
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  have hUne : blockU L ≠ ⊥ := by
    intro h
    have h1 := E.card_U' hcfg
    rw [h, Subgroup.card_bot] at h1
    have hpos : 0 < Nat.card (centerOf L) := Nat.card_pos
    have h5 : 2 ^ 2 ≤ 2 ^ (2 * n) :=
      Nat.pow_le_pow_right (by norm_num) (by have := hcfg.one_lt; omega)
    have h6 : 2 ^ (2 * n) ≤ 2 ^ (2 * n) * Nat.card (centerOf L) :=
      Nat.le_mul_of_pos_right _ hpos
    omega
  have hUS : blockU L ≤ S := by
    rw [E.UQ hcfg]; exact hcfg.Q_le_S
  have hSyl : IsSylowTwoOf S (Subgroup.normalizer (blockU L : Set G)) :=
    hcfg.cs.isSylowTwoOf_normalizer hUne hUS (by
      rw [E.UQ hcfg]; exact hcfg.H_le_normalizer_Q)
  obtain ⟨c, hcN, hP₁c⟩ := exists_le_conjR_of_isSylowTwoOf hSyl (hP₁.le.trans inf_le_left)
    hP₁.isPGroup
  have hRc : conjR (thompsonJ S) c⁻¹ ≤ T := by
    have h1 : thompsonJ S ≤ conjR S c := hRP₁.trans hP₁c
    have : conjR (thompsonJ S) c⁻¹ ≤ S := by rw [conjR_le_iff, inv_inv]; exact h1
    exact this.trans hcfg.S_le_T
  have hRceq := E.conjR_R_eq_of_le_T hcfg hRc
  have hcR : conjR (thompsonJ S) c = thompsonJ S := by
    have := congrArg (fun X => conjR X c) hRceq
    simp only [conjR_inv_conjR] at this
    exact this.symm
  have hcN' : c ∈ Subgroup.normalizer (centerOf (thompsonJ S) : Set G) := by
    rw [← conjR_eq_self_iff, conjR_centerOf, hcR]
  have hP₁R : P₁ ≤ thompsonJ S := by
    intro y hy
    have h1 : c * y * c⁻¹ ∈ S := mem_conjR.1 (hP₁c hy)
    have h2 : ∀ z ∈ centerOf (thompsonJ S), (c * y * c⁻¹) * z = z * (c * y * c⁻¹) := by
      intro z hz
      have hz' : c⁻¹ * z * c ∈ centerOf (thompsonJ S) := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hcN') z).1 hz
        simpa using this
      have h3 := Subgroup.mem_centralizer_iff.1 (hP₁.le hy).2 _ hz'
      calc c * y * c⁻¹ * z = c * (y * (c⁻¹ * z * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * z * c) * y) * c⁻¹ := by rw [← h3]
        _ = z * (c * y * c⁻¹) := by group
    have h4 := E.centralizer_S_Z_le_R hcfg hc h1 (fun z hz => (h2 z hz))
    rw [← hcR]
    exact mem_conjR.2 h4
  have hP₁eq : P₁ = thompsonJ S := le_antisymm hP₁R hRP₁
  rw [hP₁eq] at hP₁
  exact hP₁

theorem isSylowTwoOf_conjR_R_inf (hc : centerOf L = ⊥) {m : G} (hm : m ∈ M) :
    IsSylowTwoOf (conjR (thompsonJ S) m)
      (Subgroup.normalizer (conjR (blockU L) m : Set G) ⊓
        Subgroup.centralizer (centerOf (thompsonJ S) : Set G)) := by
  have hZR : lin2Z L (thompsonJ S) = centerOf (thompsonJ S) :=
    ((lin2Z_cases (Z := lin2Z L (thompsonJ S)) rfl).resolve_right fun h => h.1 hc).2
  have hmZ : m ∈ Subgroup.normalizer (centerOf (thompsonJ S) : Set G) := by
    have := E.N_Z_eq_M hcfg (Z := lin2Z L (thompsonJ S)) rfl hc
    rw [hZR] at this
    rw [this]; exact hm
  have h1 := (E.isSylowTwoOf_R_inf hcfg hc).map_equiv (MulAut.conj m⁻¹)
  have e1 : (thompsonJ S).map (MulAut.conj m⁻¹).toMonoidHom = conjR (thompsonJ S) m := rfl
  have e2 : (Subgroup.normalizer (blockU L : Set G) ⊓
      Subgroup.centralizer (centerOf (thompsonJ S) : Set G)).map (MulAut.conj m⁻¹).toMonoidHom =
        Subgroup.normalizer (conjR (blockU L) m : Set G) ⊓
          Subgroup.centralizer (centerOf (thompsonJ S) : Set G) := by
    change conjR (Subgroup.normalizer (blockU L : Set G) ⊓
      Subgroup.centralizer (centerOf (thompsonJ S) : Set G)) m = _
    rw [conjR_inf, ← conjR_normalizer, ← conjR_centralizer, conjR_eq_of_mem_normalizer hmZ]
  rw [e1, e2] at h1
  exact h1

end LQ2

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2
