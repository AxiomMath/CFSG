module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.GroupLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Orbit

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

structure DiagData (T W W' M K : Subgroup H) (s : H) : Prop where
  W_le_normalizer : W ≤ normalizer (T : Set H)
  W'_le : W' ≤ W
  s_mem : s ∈ W
  s_not_mem : s ∉ W'
  sq_mem : s ^ 2 ∈ W'
  conj_mem : ∀ g ∈ W, ∀ u ∈ W', g * u * g⁻¹ ∈ W'
  cover : ∀ g ∈ W, g ∈ W' ∨ s⁻¹ * g ∈ W'
  isComp_M : IsCompIn M (centralizer (T : Set H))
  normalizer_le : ∀ g ∈ W, g ∈ normalizer (M : Set H) → g ∈ W'
  isComp_K : IsCompIn K (centralizer ((W ⊔ T : Subgroup H) : Set H))
  K_le : K ≤ conjClosure M W

@[expose] def diagP₂ (M W' : Subgroup H) (s : H) : Subgroup H :=
  (conjClosure M W').map (MulAut.conj s).toMonoidHom

section Setup

variable {T W W' M K : Subgroup H} {s : H}

theorem DiagData.isComp_conj (h : DiagData T W W' M K s) {g : H} (hg : g ∈ W) :
    IsCompIn (M.map (MulAut.conj g).toMonoidHom) (centralizer (T : Set H)) :=
  isCompIn_map_conj_of_mem_normalizer h.isComp_M
    (mem_normalizer_centralizer_of_mem_normalizer (h.W_le_normalizer hg))

theorem DiagData.conj_ne (h : DiagData T W W' M K s) {g g' : H} (hg : g ∈ W') (hg' : g' ∈ W') :
    M.map (MulAut.conj g').toMonoidHom ≠ M.map (MulAut.conj (s * g)).toMonoidHom := by
  intro heq
  have h1 : M = M.map (MulAut.conj (g'⁻¹ * (s * g))).toMonoidHom := by
    have := congrArg (fun A : Subgroup H => A.map (MulAut.conj g'⁻¹).toMonoidHom) heq
    simp only [map_conj_map_conj, inv_mul_cancel, map_conj_one] at this
    exact this
  have hmem : g'⁻¹ * (s * g) ∈ normalizer (M : Set H) :=
    Solomon78.mem_normalizer_iff_map_conj_eq.2 h1.symm
  have hW : g'⁻¹ * (s * g) ∈ W :=
    W.mul_mem (W.inv_mem (h.W'_le hg')) (W.mul_mem h.s_mem (h.W'_le hg))
  have hW' := h.normalizer_le _ hW hmem
  apply h.s_not_mem
  have : s = g' * (g'⁻¹ * (s * g)) * g⁻¹ := by group
  rw [this]
  exact W'.mul_mem (W'.mul_mem hg' hW') (W'.inv_mem hg)

theorem diagP₂_eq (M W' : Subgroup H) (s : H) :
    diagP₂ M W' s = ⨆ g ∈ W', M.map (MulAut.conj (s * g)).toMonoidHom := by
  unfold diagP₂ conjClosure
  rw [Subgroup.map_iSup]
  refine iSup_congr fun g => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun _ => map_conj_map_conj M g s

theorem DiagData.commute [Finite H] (h : DiagData T W W' M K s) :
    ∀ a ∈ conjClosure M W', ∀ b ∈ diagP₂ M W' s, a * b = b * a := by
  have key : ∀ g ∈ W', ∀ g' ∈ W', ∀ a ∈ M.map (MulAut.conj g).toMonoidHom,
      ∀ b ∈ M.map (MulAut.conj (s * g')).toMonoidHom, a * b = b * a := by
    intro g hg g' hg' a ha b hb
    exact (h.isComp_conj (h.W'_le hg)).commute_of_ne
      (h.isComp_conj (W.mul_mem h.s_mem (h.W'_le hg'))) (h.conj_ne hg' hg) a ha b hb
  have h2 : ∀ g ∈ W', diagP₂ M W' s ≤ centralizer ((M.map (MulAut.conj g).toMonoidHom : Subgroup H)
      : Set H) := by
    intro g hg
    rw [diagP₂_eq]
    refine iSup₂_le fun g' hg' b hb => ?_
    exact mem_centralizer_iff.2 fun a ha => key g hg g' hg' a ha b hb
  have h1 : conjClosure M W' ≤ centralizer ((diagP₂ M W' s : Subgroup H) : Set H) := by
    refine iSup₂_le fun g hg a ha => ?_
    exact mem_centralizer_iff.2 fun b hb =>
      (mem_centralizer_iff.1 (h2 g hg hb) a ha).symm
  intro a ha b hb
  exact (mem_centralizer_iff.1 (h1 ha) b hb).symm

theorem DiagData.map_conj_P₁ (_h : DiagData T W W' M K s) {u : H} (hu : u ∈ W') :
    (conjClosure M W').map (MulAut.conj u).toMonoidHom = conjClosure M W' :=
  Solomon78.mem_normalizer_iff_map_conj_eq.1 (le_normalizer_conjClosure M W' hu)

theorem DiagData.map_conj_P₂ (h : DiagData T W W' M K s) {u : H} (hu : u ∈ W') :
    (diagP₂ M W' s).map (MulAut.conj u).toMonoidHom = diagP₂ M W' s := by
  have hv : s⁻¹ * u * s ∈ W' := by
    have := h.conj_mem s⁻¹ (W.inv_mem h.s_mem) u hu
    simpa using this
  unfold diagP₂
  rw [map_conj_map_conj, show u * s = s * (s⁻¹ * u * s) by group,
    ← map_conj_map_conj (conjClosure M W') (s⁻¹ * u * s) s, h.map_conj_P₁ hv]

theorem DiagData.map_conj_P₂_s (h : DiagData T W W' M K s) :
    (diagP₂ M W' s).map (MulAut.conj s).toMonoidHom = conjClosure M W' := by
  unfold diagP₂
  rw [map_conj_map_conj, ← pow_two]
  exact h.map_conj_P₁ h.sq_mem

theorem DiagData.P₁_le_centralizer (h : DiagData T W W' M K s) :
    conjClosure M W' ≤ centralizer (T : Set H) :=
  iSup₂_le fun _ hg => (h.isComp_conj (h.W'_le hg)).1

theorem DiagData.P₂_le_centralizer (h : DiagData T W W' M K s) :
    diagP₂ M W' s ≤ centralizer (T : Set H) := by
  rw [diagP₂_eq]
  exact iSup₂_le fun _ hg => (h.isComp_conj (W.mul_mem h.s_mem (h.W'_le hg))).1

theorem DiagData.conjClosure_le_sup (h : DiagData T W W' M K s) :
    conjClosure M W ≤ conjClosure M W' ⊔ diagP₂ M W' s := by
  refine iSup₂_le fun g hg => ?_
  rcases h.cover g hg with h1 | h1
  · exact le_sup_of_le_left (map_conj_le_conjClosure h1)
  · refine le_sup_of_le_right ?_
    rw [diagP₂_eq]
    exact le_iSup₂_of_le (s⁻¹ * g) h1 (by rw [show s * (s⁻¹ * g) = g by group])

theorem DiagData.K_le_sup (h : DiagData T W W' M K s) :
    K ≤ conjClosure M W' ⊔ diagP₂ M W' s :=
  h.K_le.trans h.conjClosure_le_sup

theorem DiagData.exists_mul [Finite H] (h : DiagData T W W' M K s) {x : H}
    (hx : x ∈ conjClosure M W' ⊔ diagP₂ M W' s) :
    ∃ a ∈ conjClosure M W', ∃ b ∈ diagP₂ M W' s, x = a * b := by
  have hle : conjClosure M W' ≤ normalizer (diagP₂ M W' s : Set H) := fun a ha =>
    Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun b hb => (h.commute a ha b hb).symm)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨a, ha, b, hb, rfl⟩

theorem DiagData.inf_central [Finite H] (h : DiagData T W W' M K s) {z : H}
    (hz : z ∈ conjClosure M W' ⊓ diagP₂ M W' s) {x : H}
    (hx : x ∈ conjClosure M W' ⊔ diagP₂ M W' s) : z * x = x * z := by
  have : conjClosure M W' ⊔ diagP₂ M W' s ≤ centralizer ({z} : Set H) := sup_le
    (fun a ha => mem_centralizer_singleton_iff.2 (h.commute a ha z hz.2))
    (fun b hb => mem_centralizer_singleton_iff.2 (h.commute z hz.1 b hb).symm)
  exact (mem_centralizer_singleton_iff.1 (this hx)).symm

theorem DiagData.subnormal_P₁ [Finite H] (h : DiagData T W W' M K s) :
    ((conjClosure M W').subgroupOf (centralizer (T : Set H))).IsSubnormal := by
  rw [conjClosure_eq_iSup_subtype]
  exact isSubnormal_subgroupOf_iSup (fun g => (h.isComp_conj (h.W'_le g.2)).1)
    fun g => (h.isComp_conj (h.W'_le g.2)).2.2

end Setup

end CFSG.EvenSporadicStandard.Induction.Junction
