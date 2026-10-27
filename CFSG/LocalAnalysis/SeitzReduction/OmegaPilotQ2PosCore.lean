module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNotLongRootQTwo
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Count

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)

section Core

variable {G : Type*} [Group G] {H : Subgroup G}

theorem commutatorElement_mem_perfectCore_left {p x : G} (hp : p ∈ perfectCore H)
    (hx : x ∈ H) : ⁅p, x⁆ ∈ perfectCore H := by
  have h := mul_mem hp (conj_mem_perfectCore hx (inv_mem hp))
  rw [commutatorElement_def]
  simpa only [mul_assoc] using h

theorem commutatorElement_mem_perfectCore_right {p x : G} (hp : p ∈ perfectCore H)
    (hx : x ∈ H) : ⁅x, p⁆ ∈ perfectCore H := by
  rw [commutatorElement_def]
  exact mul_mem (conj_mem_perfectCore hx hp) (inv_mem hp)

theorem perfectCore_le_ker_of_isSolvable_codomain [Finite G] {S : Type*} [Group S] [Finite S]
    [Group.IsSolvable S] (C : Subgroup G) (φ : C →* S) :
    perfectCore C ≤ φ.ker.map C.subtype := by
  have h1 : (perfectCore (⊤ : Subgroup C)).map C.subtype = perfectCore C := by
    rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h2 : (perfectCore (⊤ : Subgroup C)).map φ = ⊥ := by
    rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map]
    exact (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot _).1 inferInstance
  rw [← h1]
  refine map_mono fun x hx => ?_
  rw [MonoidHom.mem_ker]
  have h3 : φ x ∈ (perfectCore (⊤ : Subgroup C)).map φ := mem_map_of_mem φ hx
  rwa [h2, mem_bot] at h3

end Core

section Eichler

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  (hQ : (polarBilin Q).Nondegenerate)
  (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)

include hQ hT

theorem projHom_commutatorElement_eichler (g : orthDerived Q) {u v : Fin d → K}
    (hgu : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) u = u) (hv : polar Q u v = 0) :
    ⁅projHom Q g, projHom Q ⟨eichler Q u v, eichler_mem_orthDerived hQ hT u v⟩⁆ =
      projHom Q ⟨eichler Q u ((g : (Fin d → K) ≃ₗ[K] (Fin d → K)) v - v),
        eichler_mem_orthDerived hQ hT _ _⟩ := by
  rw [← map_commutatorElement]
  congr 1
  apply Subtype.ext
  exact commutatorElement_eichler (Subgroup.commutator_le_self _ g.2) hgu hv

theorem projHom_eichler_mul {u v w : Fin d → K} (hv : polar Q u v = 0) (hw : polar Q u w = 0) :
    projHom Q ⟨eichler Q u v, eichler_mem_orthDerived hQ hT u v⟩ *
        projHom Q ⟨eichler Q u w, eichler_mem_orthDerived hQ hT u w⟩ =
      projHom Q ⟨eichler Q u (v + w), eichler_mem_orthDerived hQ hT _ _⟩ := by
  rw [← map_mul]
  congr 1
  exact Subtype.ext (eichler_mul hv hw)

theorem projHom_eichler_congr {u v v' : Fin d → K} (h : v = v') :
    projHom Q ⟨eichler Q u v, eichler_mem_orthDerived hQ hT u v⟩ =
      projHom Q ⟨eichler Q u v', eichler_mem_orthDerived hQ hT u v'⟩ := by
  subst h
  rfl

theorem projHom_eichler_add_smul_self {u : Fin d → K} (hu : Q u = 0) (v : Fin d → K) (s : K) :
    projHom Q ⟨eichler Q u (v + s • u), eichler_mem_orthDerived hQ hT _ _⟩ =
      projHom Q ⟨eichler Q u v, eichler_mem_orthDerived hQ hT u v⟩ := by
  congr 1
  exact Subtype.ext (eichler_add_smul_self hu v s)

theorem projHom_eichler_mem_perfectCore_left {H : Subgroup (matrixProjectiveDerived Q)}
    {g : orthDerived Q} (hg : projHom Q g ∈ perfectCore H) {u v v' : Fin d → K}
    (hgu : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) u = u) (hv : polar Q u v = 0)
    (hvH : projHom Q ⟨eichler Q u v, eichler_mem_orthDerived hQ hT u v⟩ ∈ H)
    (hv' : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) v - v = v') :
    projHom Q ⟨eichler Q u v', eichler_mem_orthDerived hQ hT u v'⟩ ∈ perfectCore H := by
  subst hv'
  rw [← projHom_commutatorElement_eichler hQ hT g hgu hv]
  exact commutatorElement_mem_perfectCore_left hg hvH

theorem projHom_eichler_mem_perfectCore_right {H : Subgroup (matrixProjectiveDerived Q)}
    {g : orthDerived Q} (hg : projHom Q g ∈ H) {u v v' : Fin d → K}
    (hgu : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) u = u) (hv : polar Q u v = 0)
    (hvH : projHom Q ⟨eichler Q u v, eichler_mem_orthDerived hQ hT u v⟩ ∈ perfectCore H)
    (hv' : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) v - v = v') :
    projHom Q ⟨eichler Q u v', eichler_mem_orthDerived hQ hT u v'⟩ ∈ perfectCore H := by
  subst hv'
  rw [← projHom_commutatorElement_eichler hQ hT g hgu hv]
  exact commutatorElement_mem_perfectCore_right hvH hg

theorem projHom_eichler_mem_stabPairsBar {a a' b b' : Fin d} (hi : IsHypCoord Q a a')
    (hj : IsHypCoord Q b b') {u w : Fin d → K} (hu : u ∈ subW K a a' b b')
    (hw : w ∈ subW K a a' b b') :
    projHom Q ⟨eichler Q u w, eichler_mem_orthDerived hQ hT u w⟩ ∈ stabPairsBar Q a a' b b' := by
  obtain ⟨⟨hua, hua'⟩, hub, hub'⟩ := hu
  obtain ⟨⟨hwa, hwa'⟩, hwb, hwb'⟩ := hw
  refine ⟨⟨_, eichler_mem_orthDerived hQ hT u w⟩, mem_subgroupOf.mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩, rfl⟩
  · exact eichler_apply_of_polar_eq_zero (by rw [hi.polar_left]; exact hua')
      (by rw [hi.polar_left]; exact hwa')
  · exact eichler_apply_of_polar_eq_zero (by rw [hi.polar_right]; exact hua)
      (by rw [hi.polar_right]; exact hwa)
  · exact eichler_apply_of_polar_eq_zero (by rw [hj.polar_left]; exact hub')
      (by rw [hj.polar_left]; exact hwb')
  · exact eichler_apply_of_polar_eq_zero (by rw [hj.polar_right]; exact hub)
      (by rw [hj.polar_right]; exact hwb)

end Eichler

section Lower

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  (hQ : (polarBilin Q).Nondegenerate)
  (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  {a a' b b' c c' : Fin d}

include hQ hT

omit [CharP K 2] in
theorem projHom_eichler_mem_perfectCore_of_mem_subW (hi : IsHypCoord Q a a')
    (hj : IsHypCoord Q b b') (hk : IsHypCoord Q c c') (hik : PairDisjoint a a' c c')
    (hjk : PairDisjoint b b' c c') {H : Subgroup (matrixProjectiveDerived Q)}
    (hB : stabPairsBar Q a a' b b' ≤ perfectCore H) {x y : Fin d → K}
    (hx : x ∈ subW K a a' b b') (hy : y ∈ subW K a a' b b') (hxc : x c = 0) (hxc' : x c' = 0)
    (hyc : y c = 0) (hyc' : y c' = 0) (hxy : polar Q y x = 1) {u : Fin d → K}
    (huW : ∀ w ∈ subW K a a' b b', polar Q u w = 0)
    (hH : ∀ w ∈ subW K a a' b b',
      projHom Q ⟨eichler Q u w, eichler_mem_orthDerived hQ hT u w⟩ ∈ H)
    {w : Fin d → K} (hw : w ∈ subW K a a' b b') :
    projHom Q ⟨eichler Q u w, eichler_mem_orthDerived hQ hT u w⟩ ∈ perfectCore H := by
  obtain ⟨e₃, he₃⟩ : ∃ e : Fin d → K, e = Pi.single c 1 := ⟨_, rfl⟩
  obtain ⟨f₃, hf₃⟩ : ∃ f : Fin d → K, f = Pi.single c' 1 := ⟨_, rfl⟩
  have hQe : Q e₃ = 0 := by rw [he₃]; exact hk.map_left
  have hQf : Q f₃ = 0 := by rw [hf₃]; exact hk.map_right
  have hpe : ∀ v, polar Q e₃ v = v c' := fun v => by rw [he₃]; exact hk.polar_left v
  have hpf : ∀ v, polar Q f₃ v = v c := fun v => by rw [hf₃]; exact hk.polar_right v
  have he₃W : e₃ ∈ subW K a a' b b' := by
    rw [he₃]
    exact ⟨⟨Pi.single_eq_of_ne hik.left_ne_left.symm _,
      Pi.single_eq_of_ne hik.left_ne_right.symm _⟩,
      Pi.single_eq_of_ne hjk.left_ne_left.symm _, Pi.single_eq_of_ne hjk.left_ne_right.symm _⟩
  have hf₃W : f₃ ∈ subW K a a' b b' := by
    rw [hf₃]
    exact ⟨⟨Pi.single_eq_of_ne hik.right_ne_left.symm _,
      Pi.single_eq_of_ne hik.right_ne_right.symm _⟩,
      Pi.single_eq_of_ne hjk.right_ne_left.symm _, Pi.single_eq_of_ne hjk.right_ne_right.symm _⟩
  have he₃c : e₃ c = 1 := by rw [he₃, Pi.single_eq_same]
  have hf₃c' : f₃ c' = 1 := by rw [hf₃, Pi.single_eq_same]
  have hye : polar Q y e₃ = 0 := by rw [polar_comm, hpe]; exact hyc'
  have hyf : polar Q y f₃ = 0 := by rw [polar_comm, hpf]; exact hyc
  have hAe : ∀ s : K,
      projHom Q ⟨eichler Q u (s • e₃), eichler_mem_orthDerived hQ hT _ _⟩ ∈ perfectCore H := by
    intro s
    refine projHom_eichler_mem_perfectCore_left hQ hT
      (g := ⟨eichler Q e₃ x, eichler_mem_orthDerived hQ hT _ _⟩)
      (hB (projHom_eichler_mem_stabPairsBar hQ hT hi hj he₃W hx))
      (eichler_apply_of_polar_eq_zero (huW e₃ he₃W) (huW x hx)) (v := (-s) • y)
      (by rw [polar_smul_right_eq, huW y hy, mul_zero]) (hH _ (Submodule.smul_mem _ (-s) hy)) ?_
    change eichler Q e₃ x ((-s) • y) - (-s) • y = s • e₃
    rw [map_smul, eichler_apply hQe (by rw [hpe]; exact hxc'), hye, hxy]
    module
  have hAf : ∀ s : K,
      projHom Q ⟨eichler Q u (s • f₃), eichler_mem_orthDerived hQ hT _ _⟩ ∈ perfectCore H := by
    intro s
    refine projHom_eichler_mem_perfectCore_left hQ hT
      (g := ⟨eichler Q f₃ x, eichler_mem_orthDerived hQ hT _ _⟩)
      (hB (projHom_eichler_mem_stabPairsBar hQ hT hi hj hf₃W hx))
      (eichler_apply_of_polar_eq_zero (huW f₃ hf₃W) (huW x hx)) (v := (-s) • y)
      (by rw [polar_smul_right_eq, huW y hy, mul_zero]) (hH _ (Submodule.smul_mem _ (-s) hy)) ?_
    change eichler Q f₃ x ((-s) • y) - (-s) • y = s • f₃
    rw [map_smul, eichler_apply hQf (by rw [hpf]; exact hxc), hyf, hxy]
    module
  have hBw : ∀ w' ∈ subW K a a' b b', w' c' = 0 →
      projHom Q ⟨eichler Q u w', eichler_mem_orthDerived hQ hT _ _⟩ ∈ perfectCore H := by
    intro w' hw' hw'c'
    have h1 : projHom Q ⟨eichler Q u (w' - (w' c + Q w') • e₃),
        eichler_mem_orthDerived hQ hT _ _⟩ ∈ perfectCore H := by
      refine projHom_eichler_mem_perfectCore_left hQ hT
        (g := ⟨eichler Q e₃ w', eichler_mem_orthDerived hQ hT _ _⟩)
        (hB (projHom_eichler_mem_stabPairsBar hQ hT hi hj he₃W hw'))
        (eichler_apply_of_polar_eq_zero (huW e₃ he₃W) (huW w' hw')) (v := f₃)
        (huW f₃ hf₃W) (hH f₃ hf₃W) ?_
      change eichler Q e₃ w' f₃ - f₃ = w' - (w' c + Q w') • e₃
      rw [eichler_apply hQe (by rw [hpe]; exact hw'c'), hpf, hpf, he₃c]
      module
    have h3 := mul_mem h1 (hAe (w' c + Q w'))
    rwa [projHom_eichler_mul hQ hT (huW _ (sub_mem hw' (Submodule.smul_mem _ _ he₃W)))
      (huW _ (Submodule.smul_mem _ _ he₃W)), sub_add_cancel] at h3
  have hw1 : w - (w c') • f₃ ∈ subW K a a' b b' := sub_mem hw (Submodule.smul_mem _ _ hf₃W)
  have hw1c' : (w - (w c') • f₃) c' = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hf₃c', mul_one, sub_self]
  have h4 := mul_mem (hBw _ hw1 hw1c') (hAf (w c'))
  rwa [projHom_eichler_mul hQ hT (huW _ hw1) (huW _ (Submodule.smul_mem _ _ hf₃W)),
    sub_add_cancel] at h4

theorem rootRadicalBar_sup_stabPairsBar_le_perfectCore (hi : IsHypCoord Q a a')
    (hj : IsHypCoord Q b b') (hk : IsHypCoord Q c c') (hij : PairDisjoint a a' b b')
    (hik : PairDisjoint a a' c c') (hjk : PairDisjoint b b' c c')
    (hS : ⁅stabPairsBar Q a a' b b', stabPairsBar Q a a' b b'⁆ = stabPairsBar Q a a' b b')
    {x y : Fin d → K} (hx : x ∈ subW K a a' b b') (hy : y ∈ subW K a a' b b') (hxc : x c = 0)
    (hxc' : x c' = 0) (hyc : y c = 0) (hyc' : y c' = 0) (hxy : polar Q y x = 1) :
    rootRadicalBar Q hi.hypPair hj.hypPair ⊔ stabPairsBar Q a a' b b' ≤
      perfectCore (centralizer
        {rootPairElt hQ (hi.orth hj hij) (hi.orth hk hik) (hj.orth hk hjk)}) := by
  have h₁₂ := hi.orth hj hij
  set C := centralizer {rootPairElt hQ h₁₂ (hi.orth hk hik) (hj.orth hk hjk)} with hC
  have hCeq := centralizer_rootPairElt hQ h₁₂ (hi.orth hk hik) (hj.orth hk hjk)
  have hRC : ∀ X : orthDerived Q, (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈
      rootRadical Q hi.hypPair hj.hypPair → projHom Q X ∈ C := fun X hX => by
    rw [hC, hCeq]
    exact mem_sup_left ⟨X, mem_subgroupOf.mpr hX, rfl⟩
  have hBC : stabPairsBar Q a a' b b' ≤ perfectCore C := by
    refine le_perfectCore_of_perfect ?_ hS
    rw [hC, hCeq]
    exact (stabPairsBar_le_rootLeviBar hi hj).trans le_sup_right
  have hpa : ∀ v, polar Q hi.hypPair.e v = v a' := fun v => hi.polar_left v
  have hpb : ∀ v, polar Q hj.hypPair.e v = v b' := fun v => hj.polar_left v
  have haW : ∀ w ∈ subW K a a' b b', polar Q hi.hypPair.e w = 0 := fun w hw => by
    rw [hpa]; exact hw.1.2
  have hbW : ∀ w ∈ subW K a a' b b', polar Q hj.hypPair.e w = 0 := fun w hw => by
    rw [hpb]; exact hw.2.2
  have hEa : ∀ w ∈ subW K a a' b b', projHom Q ⟨eichler Q hi.hypPair.e w,
      eichler_mem_orthDerived hQ hT _ _⟩ ∈ perfectCore C := fun w hw =>
    projHom_eichler_mem_perfectCore_of_mem_subW hQ hT hi hj hk hik hjk hBC hx hy hxc hxc' hyc
      hyc' hxy haW (fun w' hw' => hRC _ (eichler_mem_rootRadical_left h₁₂ (haW w' hw')
        (hbW w' hw'))) hw
  have hEb : ∀ w ∈ subW K a a' b b', projHom Q ⟨eichler Q hj.hypPair.e w,
      eichler_mem_orthDerived hQ hT _ _⟩ ∈ perfectCore C := fun w hw =>
    projHom_eichler_mem_perfectCore_of_mem_subW hQ hT hi hj hk hik hjk hBC hx hy hxc hxc' hyc
      hyc' hxy hbW (fun w' hw' => hRC _ (eichler_mem_rootRadical_right h₁₂ (haW w' hw')
        (hbW w' hw'))) hw
  have he₃W : hk.hypPair.e ∈ subW K a a' b b' :=
    ⟨⟨Pi.single_eq_of_ne hik.left_ne_left.symm _, Pi.single_eq_of_ne hik.left_ne_right.symm _⟩,
      Pi.single_eq_of_ne hjk.left_ne_left.symm _, Pi.single_eq_of_ne hjk.left_ne_right.symm _⟩
  have hf₃W : hk.hypPair.f ∈ subW K a a' b b' :=
    ⟨⟨Pi.single_eq_of_ne hik.right_ne_left.symm _, Pi.single_eq_of_ne hik.right_ne_right.symm _⟩,
      Pi.single_eq_of_ne hjk.right_ne_left.symm _, Pi.single_eq_of_ne hjk.right_ne_right.symm _⟩
  have hDa : ∀ β : K, projHom Q ⟨eichler Q hi.hypPair.e (β • hj.hypPair.e),
      eichler_mem_orthDerived hQ hT _ _⟩ ∈ perfectCore C := by
    intro β
    refine projHom_eichler_mem_perfectCore_right hQ hT
      (g := ⟨eichler Q hj.hypPair.e ((-β) • hk.hypPair.f), eichler_mem_orthDerived hQ hT _ _⟩)
      (hRC _ (eichler_mem_rootRadical_right h₁₂ (haW _ (Submodule.smul_mem _ _ hf₃W))
        (hbW _ (Submodule.smul_mem _ _ hf₃W))))
      (eichler_apply_of_polar_eq_zero h₁₂.ee (haW _ (Submodule.smul_mem _ _ hf₃W)))
      (v := hk.hypPair.e) (haW _ he₃W) (hEa _ he₃W) ?_
    change eichler Q hj.hypPair.e ((-β) • hk.hypPair.f) hk.hypPair.e - hk.hypPair.e =
      β • hj.hypPair.e
    rw [eichler_apply hj.hypPair.Q_e (hbW _ (Submodule.smul_mem _ _ hf₃W)),
      polar_comm Q hk.hypPair.e hj.hypPair.e, (hj.orth hk hjk).ee, polar_smul_right_eq,
      hk.hypPair.polar_ef]
    module
  have hDb : ∀ α : K, projHom Q ⟨eichler Q hj.hypPair.e (α • hi.hypPair.e),
      eichler_mem_orthDerived hQ hT _ _⟩ ∈ perfectCore C := by
    intro α
    refine projHom_eichler_mem_perfectCore_right hQ hT
      (g := ⟨eichler Q hi.hypPair.e ((-α) • hk.hypPair.f), eichler_mem_orthDerived hQ hT _ _⟩)
      (hRC _ (eichler_mem_rootRadical_left h₁₂ (haW _ (Submodule.smul_mem _ _ hf₃W))
        (hbW _ (Submodule.smul_mem _ _ hf₃W))))
      (eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact h₁₂.ee)
        (hbW _ (Submodule.smul_mem _ _ hf₃W)))
      (v := hk.hypPair.e) (hbW _ he₃W) (hEb _ he₃W) ?_
    change eichler Q hi.hypPair.e ((-α) • hk.hypPair.f) hk.hypPair.e - hk.hypPair.e =
      α • hi.hypPair.e
    rw [eichler_apply hi.hypPair.Q_e (haW _ (Submodule.smul_mem _ _ hf₃W)),
      polar_comm Q hk.hypPair.e hi.hypPair.e, (hi.orth hk hik).ee, polar_smul_right_eq,
      hk.hypPair.polar_ef]
    module
  have hya' : ∀ y, polar Q hi.hypPair.e y = 0 → y a' = 0 := fun y h => by rw [← hpa y]; exact h
  have hyb' : ∀ y, polar Q hj.hypPair.e y = 0 → y b' = 0 := fun y h => by rw [← hpb y]; exact h
  have hwW : ∀ y, polar Q hi.hypPair.e y = 0 → polar Q hj.hypPair.e y = 0 →
      y - (y a) • hi.hypPair.e - (y b) • hj.hypPair.e ∈ subW K a a' b b' := by
    intro y hya hyb
    simp only [IsHypCoord.hypPair_e]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    · rw [Pi.single_eq_same, Pi.single_eq_of_ne hij.left_ne_left.symm]
      ring
    · rw [Pi.single_eq_of_ne hi.ne.symm, Pi.single_eq_of_ne hij.left_ne_right.symm,
        hya' y hya]
      ring
    · rw [Pi.single_eq_same, Pi.single_eq_of_ne hij.left_ne_left]
      ring
    · rw [Pi.single_eq_of_ne hij.right_ne_left, Pi.single_eq_of_ne hj.ne.symm, hyb' y hyb]
      ring
  have hEa' : ∀ y, polar Q hi.hypPair.e y = 0 → polar Q hj.hypPair.e y = 0 →
      projHom Q ⟨eichler Q hi.hypPair.e y, eichler_mem_orthDerived hQ hT _ _⟩ ∈
        perfectCore C := by
    intro y hya hyb
    have hy : y = ((y - (y a) • hi.hypPair.e - (y b) • hj.hypPair.e) + (y b) • hj.hypPair.e) +
        (y a) • hi.hypPair.e := by abel
    rw [projHom_eichler_congr hQ hT hy, projHom_eichler_add_smul_self hQ hT hi.hypPair.Q_e,
      ← projHom_eichler_mul hQ hT (haW _ (hwW y hya hyb))
        (by rw [polar_smul_right_eq, h₁₂.ee, mul_zero])]
    exact mul_mem (hEa _ (hwW y hya hyb)) (hDa (y b))
  have hEb' : ∀ y, polar Q hi.hypPair.e y = 0 → polar Q hj.hypPair.e y = 0 →
      projHom Q ⟨eichler Q hj.hypPair.e y, eichler_mem_orthDerived hQ hT _ _⟩ ∈
        perfectCore C := by
    intro y hya hyb
    have hy : y = ((y - (y a) • hi.hypPair.e - (y b) • hj.hypPair.e) + (y a) • hi.hypPair.e) +
        (y b) • hj.hypPair.e := by abel
    rw [projHom_eichler_congr hQ hT hy, projHom_eichler_add_smul_self hQ hT hj.hypPair.Q_e,
      ← projHom_eichler_mul hQ hT (hbW _ (hwW y hya hyb))
        (by rw [polar_smul_right_eq, polar_comm, h₁₂.ee, mul_zero])]
    exact mul_mem (hEb _ (hwW y hya hyb)) (hDb (y a))
  refine sup_le ?_ hBC
  rintro _ ⟨X, hX, rfl⟩
  have hXR : (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootRadical Q hi.hypPair hj.hypPair :=
    mem_subgroupOf.mp hX
  obtain ⟨y₁, y₂, hy11, hy21, hy12, hy22, hf1, hf2⟩ :=
    exists_eichler_mul_apply_f h₁₂ hXR.1 hXR.2.1 hXR.2.2.1
  set q := eichler Q hi.hypPair.e y₁ * eichler Q hj.hypPair.e y₂ with hqdef
  have hqR : q ∈ rootRadical Q hi.hypPair hj.hypPair :=
    mul_mem (eichler_mem_rootRadical_left h₁₂ hy11 hy21)
      (eichler_mem_rootRadical_right h₁₂ hy12 hy22)
  have hqi : ∀ v, q v = v → q⁻¹ v = v := fun v hv => by
    apply q.injective
    rw [LinearEquiv.apply_inv_apply', hv]
  have hqi' : ∀ v, q⁻¹ (q v) = v := fun v => by
    apply q.injective
    rw [LinearEquiv.apply_inv_apply']
  have hM : q⁻¹ * (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootLevi Q hi.hypPair hj.hypPair := by
    refine mem_rootLevi_of_fix (mul_mem (inv_mem hqR.1) hXR.1) ?_ ?_ ?_ ?_
    · rw [LinearEquiv.mul_apply, hXR.2.1, hqi _ hqR.2.1]
    · rw [LinearEquiv.mul_apply, ← hf1, hqi']
    · rw [LinearEquiv.mul_apply, hXR.2.2.1, hqi _ hqR.2.2.1]
    · rw [LinearEquiv.mul_apply, ← hf2, hqi']
  have h1 : q⁻¹ * (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈
      rootRadical Q hi.hypPair hj.hypPair ⊓ rootLevi Q hi.hypPair hj.hypPair :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hqR) hXR, hM⟩
  rw [rootRadical_inf_rootLevi h₁₂, mem_bot] at h1
  have hXq : (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) = q := by
    rw [← mul_inv_cancel_left q (X : (Fin d → K) ≃ₗ[K] (Fin d → K)), h1, mul_one]
  have hXeq : X = ⟨eichler Q hi.hypPair.e y₁, eichler_mem_orthDerived hQ hT _ _⟩ *
      ⟨eichler Q hj.hypPair.e y₂, eichler_mem_orthDerived hQ hT _ _⟩ := Subtype.ext hXq
  rw [hXeq, map_mul]
  exact mul_mem (hEa' y₁ hy11 hy21) (hEb' y₂ hy12 hy22)

end Lower

section Plane

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

variable (P₁ P₂) in
@[expose] def planeMatrix (g : V ≃ₗ[K] V) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => polar Q (g (![P₁.e, P₂.e] j)) (![P₁.f, P₂.f] i)

theorem planeMatrix_apply (g : V ≃ₗ[K] V) (i j : Fin 2) :
    planeMatrix P₁ P₂ g i j = polar Q (g (![P₁.e, P₂.e] j)) (![P₁.f, P₂.f] i) := rfl

theorem apply_e_eq_planeMatrix_of_commute (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g) (j : Fin 2) :
    g (![P₁.e, P₂.e] j) = planeMatrix P₁ P₂ g 0 j • P₁.e + planeMatrix P₁ P₂ g 1 j • P₂.e := by
  obtain ⟨h1, h2⟩ := apply_e_of_commute h₁₂ hc
  have he₂f₁ : polar Q P₂.e P₁.f = 0 := by rw [polar_comm]; exact h₁₂.fe
  fin_cases j
  · simp only [planeMatrix_apply, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [h1]
    simp only [polar_sub_left, polar_smul_left_eq, P₁.polar_ef, he₂f₁, h₁₂.ef, P₂.polar_ef]
    module
  · simp only [planeMatrix_apply, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [h2]
    simp only [polar_sub_left, polar_smul_left_eq, P₁.polar_ef, he₂f₁, h₁₂.ef, P₂.polar_ef]
    module

theorem planeMatrix_mul (h₁₂ : P₁.Orth P₂) (g : V ≃ₗ[K] V) {h : V ≃ₗ[K] V}
    (hh : h * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * h) :
    planeMatrix P₁ P₂ (g * h) = planeMatrix P₁ P₂ g * planeMatrix P₁ P₂ h := by
  ext i j
  change polar Q ((g * h) (![P₁.e, P₂.e] j)) (![P₁.f, P₂.f] i) = _
  rw [LinearEquiv.mul_apply, apply_e_eq_planeMatrix_of_commute h₁₂ hh j, map_add, map_smul,
    map_smul, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, Matrix.mul_apply,
    Fin.sum_univ_two]
  simp only [planeMatrix_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem det_planeMatrix (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g) :
    (planeMatrix P₁ P₂ g).det = 1 := by
  have hdet := det_eq_one_of_commute h₁₂ hg hc
  obtain ⟨h1, h2⟩ := apply_e_of_commute h₁₂ hc
  have he₂f₁ : polar Q P₂.e P₁.f = 0 := by rw [polar_comm]; exact h₁₂.fe
  rw [Matrix.det_fin_two]
  simp only [planeMatrix_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h1, h2]
  simp only [polar_sub_left, polar_smul_left_eq, P₁.polar_ef, he₂f₁, h₁₂.ef, P₂.polar_ef]
  linear_combination hdet

end Plane

section Upper

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' b b' : Fin d}

omit [CharP K 2] in
theorem isSolvable_specialLinearGroup_two_of_card_eq_two (hK : Nat.card K = 2) :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K
      (Or.inl hK)
  exact Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective

theorem perfectCore_centralizer_rootPairElt_le_two (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hij : PairDisjoint a a' b b') {P₃ : HypPair Q} (h₁₃ : hi.hypPair.Orth P₃)
    (h₂₃ : hj.hypPair.Orth P₃) :
    perfectCore (centralizer {rootPairElt hQ (hi.orth hj hij) h₁₃ h₂₃}) ≤
      rootRadicalBar Q hi.hypPair hj.hypPair ⊔ stabPairsBar Q a a' b b' := by
  have h₁₂ := hi.orth hj hij
  have hT := exists_totallySingular_of_hypPairs h₁₂ h₁₃ h₂₃
  set ψ : orthDerived Q ≃* matrixProjectiveDerived Q := MulEquiv.ofBijective (projHom Q)
    ⟨projHom_injective hi.exists_ne_zero, projHom_surjective Q⟩ with hψ
  set C := centralizer {rootPairElt hQ h₁₂ h₁₃ h₂₃} with hC
  have hcomm : ∀ x : C, ((ψ.symm x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) *
      eichler Q hi.hypPair.e hj.hypPair.e =
      eichler Q hi.hypPair.e hj.hypPair.e *
        ((ψ.symm x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) := by
    intro x
    have hx := mem_centralizer_singleton_iff.mp x.2
    have h' : ψ.symm x * ⟨eichler Q hi.hypPair.e hj.hypPair.e,
        eichler_mem_orthDerived hQ hT _ _⟩ = ⟨eichler Q hi.hypPair.e hj.hypPair.e,
        eichler_mem_orthDerived hQ hT _ _⟩ * ψ.symm x := by
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx
    exact congrArg Subtype.val h'
  have hO : ∀ x : C, ((ψ.symm x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun x => Subgroup.commutator_le_self _ (ψ.symm x).2
  let φ : C →* Matrix.SpecialLinearGroup (Fin 2) K := MonoidHom.mk'
    (fun x => (⟨planeMatrix hi.hypPair hj.hypPair
      ((ψ.symm x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)),
      det_planeMatrix h₁₂ (hO x) (hcomm x)⟩ : Matrix.SpecialLinearGroup (Fin 2) K))
    (fun x y => by
      apply Subtype.ext
      change planeMatrix hi.hypPair hj.hypPair
          ((ψ.symm ((x : matrixProjectiveDerived Q) * y) : orthDerived Q) :
            (Fin d → K) ≃ₗ[K] (Fin d → K)) =
        planeMatrix hi.hypPair hj.hypPair
          ((ψ.symm x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) *
        planeMatrix hi.hypPair hj.hypPair
          ((ψ.symm y : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K))
      rw [map_mul, Subgroup.coe_mul]
      exact planeMatrix_mul h₁₂ _ (hcomm y))
  have := isSolvable_specialLinearGroup_two_of_card_eq_two hK
  refine (perfectCore_le_ker_of_isSolvable_codomain C φ).trans ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : planeMatrix hi.hypPair hj.hypPair
      ((ψ.symm x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = 1 := by
    have h : ((φ x : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [MonoidHom.mem_ker.mp hx, Matrix.SpecialLinearGroup.coe_one]
    exact h
  set X := ψ.symm x with hXdef
  have hX1 : (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) hi.hypPair.e = hi.hypPair.e := by
    have h := apply_e_eq_planeMatrix_of_commute h₁₂ (hcomm x) 0
    rw [hx1] at h
    simpa using h
  have hX2 : (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) hj.hypPair.e = hj.hypPair.e := by
    have h := apply_e_eq_planeMatrix_of_commute h₁₂ (hcomm x) 1
    rw [hx1] at h
    simpa using h
  obtain ⟨y₁, y₂, hy11, hy21, hy12, hy22, hf1, hf2⟩ :=
    exists_eichler_mul_apply_f h₁₂ (hO x) hX1 hX2
  set q := eichler Q hi.hypPair.e y₁ * eichler Q hj.hypPair.e y₂ with hqdef
  have hqR : q ∈ rootRadical Q hi.hypPair hj.hypPair :=
    mul_mem (eichler_mem_rootRadical_left h₁₂ hy11 hy21)
      (eichler_mem_rootRadical_right h₁₂ hy12 hy22)
  have hqΩ : q ∈ orthDerived Q :=
    mul_mem (eichler_mem_orthDerived hQ hT _ _) (eichler_mem_orthDerived hQ hT _ _)
  have hqi' : ∀ v, q⁻¹ (q v) = v := fun v => by
    apply q.injective
    rw [LinearEquiv.apply_inv_apply']
  have hqi : ∀ v, q v = v → q⁻¹ v = v := fun v hv => by
    conv_lhs => rw [← hv]
    exact hqi' v
  have hm : q⁻¹ * (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈
      stabSub (K := K) a a' ⊓ stabSub b b' := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · change q⁻¹ ((X : (Fin d → K) ≃ₗ[K] (Fin d → K)) hi.hypPair.e) = hi.hypPair.e
      rw [hX1, hqi _ hqR.2.1]
    · change q⁻¹ ((X : (Fin d → K) ≃ₗ[K] (Fin d → K)) hi.hypPair.f) = hi.hypPair.f
      rw [← hf1, hqi']
    · change q⁻¹ ((X : (Fin d → K) ≃ₗ[K] (Fin d → K)) hj.hypPair.e) = hj.hypPair.e
      rw [hX2, hqi _ hqR.2.2.1]
    · change q⁻¹ ((X : (Fin d → K) ≃ₗ[K] (Fin d → K)) hj.hypPair.f) = hj.hypPair.f
      rw [← hf2, hqi']
  have hXeq : X = ⟨q, hqΩ⟩ * ⟨q⁻¹ * (X : (Fin d → K) ≃ₗ[K] (Fin d → K)),
      mul_mem (inv_mem hqΩ) X.2⟩ := Subtype.ext (by simp)
  have hx' : (x : matrixProjectiveDerived Q) = projHom Q X := (ψ.apply_symm_apply x).symm
  change (x : matrixProjectiveDerived Q) ∈ _
  rw [hx', hXeq, map_mul]
  exact mul_mem (mem_sup_left ⟨⟨q, hqΩ⟩, mem_subgroupOf.mpr hqR, rfl⟩)
    (mem_sup_right ⟨_, mem_subgroupOf.mpr hm, rfl⟩)

end Upper

section A7

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' b b' c c' : Fin d}

theorem perfectCore_centralizer_rootPairElt_two (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hk : IsHypCoord Q c c') (hij : PairDisjoint a a' b b') (hik : PairDisjoint a a' c c')
    (hjk : PairDisjoint b b' c c')
    (hS : ⁅stabPairsBar Q a a' b b', stabPairsBar Q a a' b b'⁆ = stabPairsBar Q a a' b b')
    {x y : Fin d → K} (hx : x ∈ subW K a a' b b') (hy : y ∈ subW K a a' b b') (hxc : x c = 0)
    (hxc' : x c' = 0) (hyc : y c = 0) (hyc' : y c' = 0) (hxy : polar Q y x = 1) :
    perfectCore (centralizer
        {rootPairElt hQ (hi.orth hj hij) (hi.orth hk hik) (hj.orth hk hjk)}) =
      rootRadicalBar Q hi.hypPair hj.hypPair ⊔ stabPairsBar Q a a' b b' :=
  le_antisymm (perfectCore_centralizer_rootPairElt_le_two hK hQ hi hj hij _ _)
    (rootRadicalBar_sup_stabPairsBar_le_perfectCore hQ
      (exists_totallySingular_of_hypPairs (hi.orth hj hij) (hi.orth hk hik) (hj.orth hk hjk))
      hi hj hk hij hik hjk hS hx hy hxc hxc' hyc hyc' hxy)

omit [Finite K] [CharP K 2] in
theorem normal_isPGroup_eq_bot_of_isQuasisimple {G : Type*} [Group G] {H : Subgroup G}
    (hH : CFSG.IsQuasisimple H) (hZ : center H = ⊥) (N : Subgroup H) (hN : N.Normal)
    (h2 : IsPGroup 2 N) [Finite H] : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hH hN with htop | hcen
  · exfalso
    have h2H : IsPGroup 2 H := fun s => by
      have hs : s ∈ N := htop ▸ mem_top s
      obtain ⟨k, hk⟩ := h2 ⟨s, hs⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hnt : Nontrivial H := by
      obtain ⟨-, -, a, b, hab⟩ := hH
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact hab (Subsingleton.elim _ _)
    have hc := h2H.center_nontrivial
    rw [hZ] at hc
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hc rfl
  · exact le_bot_iff.mp (hZ ▸ hcen)

theorem rootRadicalBar_stabPairsBar_facts (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hij : PairDisjoint a a' b b')
    (hS : CFSG.IsQuasisimple (stabPairsBar Q a a' b b') ∧ center (stabPairsBar Q a a' b b') = ⊥) :
    IsPGroup 2 (rootRadicalBar Q hi.hypPair hj.hypPair) ∧
      stabPairsBar Q a a' b b' ≤ normalizer (rootRadicalBar Q hi.hypPair hj.hypPair :
        Set (matrixProjectiveDerived Q)) ∧
      Disjoint (rootRadicalBar Q hi.hypPair hj.hypPair) (stabPairsBar Q a a' b b') ∧
      ∀ N : Subgroup (stabPairsBar Q a a' b b'), N.Normal → IsPGroup 2 N → N = ⊥ := by
  have h₁₂ := hi.orth hj hij
  exact ⟨isPGroup_rootRadicalBar _ _,
    (stabPairsBar_le_rootLeviBar hi hj).trans (rootLeviBar_le_normalizer h₁₂),
    (disjoint_rootRadicalBar_rootLeviBar h₁₂).mono_right (stabPairsBar_le_rootLeviBar hi hj),
    fun N hN h2 => normal_isPGroup_eq_bot_of_isQuasisimple hS.1 hS.2 N hN h2⟩

end A7

end CFSG.SeitzReduction.OmegaPilot
