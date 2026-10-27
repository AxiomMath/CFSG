module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LAutDer
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NIn

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup Matrix CFSG.Open CFSG.LocalAnalysis.SteinbergBV.ThreeInvolutions

variable {X : Type} [Group X]

theorem y2l_finite_mulAut [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun α : MulAut X => (α : X → X)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem y2l_inn_normal : ((MulAut.conj : X →* MulAut X).range).Normal := by
  constructor
  rintro _ ⟨y, rfl⟩ α
  refine ⟨α y, ?_⟩
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

variable {M : Subgroup X} [M.Normal]

theorem y2l_sup_eq_top (hchar : ∀ α : MulAut X, ∀ m ∈ M, α m ∈ M)
    (hρ : (MulAut.conjNormal : X →* MulAut M).range = ⊤) :
    (MulAut.conj : X →* MulAut X).range ⊔ fixingSubgroup (MulAut X) (M : Set X) = ⊤ := by
  rw [eq_top_iff]
  intro α _
  let αM : MulAut M :=
    { toFun := fun m => ⟨α m, hchar α m m.2⟩
      invFun := fun m => ⟨α⁻¹ m, hchar α⁻¹ m m.2⟩
      left_inv := fun m => Subtype.ext (MulAut.inv_apply_self X α m)
      right_inv := fun m => Subtype.ext (MulAut.apply_inv_self X α m)
      map_mul' := fun m m' => Subtype.ext (map_mul α (m : X) (m' : X)) }
  have hαM : αM ∈ (MulAut.conjNormal : X →* MulAut M).range := by
    rw [hρ]
    exact Subgroup.mem_top αM
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hαM
  have hβ : (MulAut.conj x)⁻¹ * α ∈ fixingSubgroup (MulAut X) (M : Set X) := by
    refine (mem_fixingSubgroup_iff (MulAut X)).mpr fun m hm => ?_
    have h1 : α m = x * m * x⁻¹ := by
      have := congrArg Subtype.val (DFunLike.congr_fun hx ⟨m, hm⟩)
      rw [MulAut.conjNormal_apply] at this
      exact this.symm
    rw [MulAut.smul_def, MulAut.mul_apply, h1, MulAut.conj_inv_apply]
    group
  rw [← mul_inv_cancel_left (MulAut.conj x) α]
  exact mul_mem (Subgroup.mem_sup_left ⟨x, rfl⟩) (Subgroup.mem_sup_right hβ)

theorem y2l_card_inn_fix_ge [Finite X] (eM : M ≃* (Fin 3 → Multiplicative (ZMod 2)))
    (hC : centralizer (M : Set X) = M) {x : Fin 2 → X}
    (hx : ∀ l, MulAut.conjNormal (x l) = y2l_psiAut eM (![T01, pGL] l)) :
    8 ≤ Nat.card
      ↥((MulAut.conj : X →* MulAut X).range ⊓ fixingSubgroup (MulAut X) (M : Set X)) := by
  haveI : Finite (MulAut X) := y2l_finite_mulAut
  have hinj : Function.Injective ((MulAut.conj : X →* MulAut X).comp M.subtype) := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have hc : ∀ y : X, y * (m : X) * y⁻¹ = m := by
      intro y
      have h1 : (m : X) * y * (m : X)⁻¹ = y := by
        have := DFunLike.congr_fun hm y
        simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply,
          MulAut.one_apply] using this
      calc y * (m : X) * y⁻¹ = ((m : X) * y * (m : X)⁻¹) * (m : X) * y⁻¹ := by rw [h1]
        _ = m := by group
    have hv : ∀ l, ![t01, pMat] l *ᵥ (y2l_toW eM m).toAdd = (y2l_toW eM m).toAdd := by
      intro l
      have h1 : MulAut.conjNormal (x l) m = m :=
        Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hc (x l))
      rw [hx l] at h1
      have h2 := congrArg (fun z => (y2l_toW eM z).toAdd) h1
      simp only [y2l_toW_psiAut] at h2
      fin_cases l
      · exact h2
      · exact h2
    have h0 := y2l_fixed_zero _ (hv 0) (hv 1)
    apply (y2l_toW eM).injective
    rw [map_one]
    exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
  have hK : Nat.card ((MulAut.conj : X →* MulAut X).comp M.subtype).range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_congr eM.toEquiv,
      Nat.card_pi]
    simp
  have hle : ((MulAut.conj : X →* MulAut X).comp M.subtype).range ≤
      (MulAut.conj : X →* MulAut X).range ⊓ fixingSubgroup (MulAut X) (M : Set X) := by
    rintro _ ⟨m, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨(m : X), rfl⟩, (mem_fixingSubgroup_iff (MulAut X)).mpr ?_⟩
    intro y hy
    have hm : (m : X) ∈ centralizer (M : Set X) := by
      rw [hC]
      exact m.2
    rw [Subgroup.mem_centralizer_iff] at hm
    simp only [MulAut.smul_def, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply]
    rw [← hm y hy]
    group
  rw [← hK]
  exact Subgroup.card_le_of_le hle

theorem y2l_index_inn_le [Finite X] (eM : M ≃* (Fin 3 → Multiplicative (ZMod 2)))
    (hC : centralizer (M : Set X) = M) (hidx : M.index = 168)
    (hchar : ∀ α : MulAut X, ∀ m ∈ M, α m ∈ M) :
    (MulAut.conj : X →* MulAut X).range.index ≤ 2 := by
  have hρ := y2l_range_conjNormal eM hC hidx
  have hsurj : ∀ φ : MulAut M, ∃ y : X, MulAut.conjNormal y = φ := fun φ => by
    have h : φ ∈ (MulAut.conjNormal : X →* MulAut M).range := by
      rw [hρ]
      exact Subgroup.mem_top φ
    exact MonoidHom.mem_range.mp h
  obtain ⟨xa, ha⟩ := hsurj (y2l_psiAut eM T01)
  obtain ⟨xb, hb⟩ := hsurj (y2l_psiAut eM pGL)
  have hx : ∀ l, MulAut.conjNormal (![xa, xb] l) = y2l_psiAut eM (![T01, pGL] l) := by
    intro l
    fin_cases l
    · exact ha
    · exact hb
  haveI : Finite (MulAut X) := y2l_finite_mulAut
  haveI := y2l_inn_normal (X := X)
  have h16 := y2l_card_fix_le eM hC hx
  have h8 := y2l_card_inn_fix_ge eM hC hx
  have hI : (MulAut.conj : X →* MulAut X).range.index =
      (MulAut.conj : X →* MulAut X).range.relIndex (fixingSubgroup (MulAut X) (M : Set X)) := by
    rw [← Subgroup.relIndex_top_right, ← y2l_sup_eq_top hchar hρ, Subgroup.relIndex_sup_left]
  rw [hI]
  by_contra hlt
  have h3 : 3 * 8 ≤ (MulAut.conj : X →* MulAut X).range.relIndex
      (fixingSubgroup (MulAut X) (M : Set X)) * Nat.card ↥((MulAut.conj : X →* MulAut X).range ⊓
        fixingSubgroup (MulAut X) (M : Set X)) :=
    Nat.mul_le_mul (by omega) h8
  rw [Subgroup.relIndex_mul_card] at h3
  omega

theorem y2l_pCoreOf_char (α : MulAut X) {m : X} (hm : m ∈ pCoreOf 2 (⊤ : Subgroup X)) :
    α m ∈ pCoreOf 2 (⊤ : Subgroup X) := by
  obtain ⟨m', hm', rfl⟩ := hm
  let α' : MulAut (⊤ : Subgroup X) := (Subgroup.topEquiv.trans α).trans Subgroup.topEquiv.symm
  exact Subgroup.mem_map.mpr ⟨α' m', Subgroup.characteristic_iff_le_comap.mp
    (inferInstance : (CFSG.pCore 2 (⊤ : Subgroup X)).Characteristic) α' hm', rfl⟩

theorem aut29Idx_holds : YamadaG23.Aut29Idx := by
  intro X _ _ hX _
  obtain ⟨⟨eM⟩, ⟨hN, ⟨eQ⟩⟩, hC⟩ := hX
  have hchar : ∀ α : MulAut X, ∀ m ∈ pCoreOf 2 (⊤ : Subgroup X),
      α m ∈ pCoreOf 2 (⊤ : Subgroup X) := fun α _ hm => y2l_pCoreOf_char α hm
  haveI : (pCoreOf 2 (⊤ : Subgroup X)).Normal :=
    ⟨fun m hm g => by
      have := hchar (MulAut.conj g) m hm
      rwa [MulAut.conj_apply] at this⟩
  have hidx : (pCoreOf 2 (⊤ : Subgroup X)).index = 168 := by
    rw [← Subgroup.relIndex_top_right]
    exact (Nat.card_congr eQ.toEquiv).trans y2l_card_GL
  exact y2l_index_inn_le eM hC hidx hchar

end CFSG.OddStandard.HigherRank.G2Three.Sec2
