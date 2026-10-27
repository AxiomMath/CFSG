module

public import CFSG.Fischer.F4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57M5Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Real
import all CFSG.Fischer.F4
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin CFSG.Fischer CFSG.Assembly.LowTwoRank Multiplicative

@[expose] def G1 : Matrix (Fin 2) (Fin 2) F4 := !![0, 1; 1, F4.ω]

@[expose] def G1inv : Matrix (Fin 2) (Fin 2) F4 := !![F4.ω, 1; 1, 0]

@[expose] def G2 : Matrix (Fin 2) (Fin 2) F4 := !![1, 1; 1, 0]

@[expose] def G2inv : Matrix (Fin 2) (Fin 2) F4 := !![0, 1; 1, 1]

@[expose] def g1GL : Matrix.GeneralLinearGroup (Fin 2) F4 :=
  ⟨G1, G1inv, by decide +kernel, by decide +kernel⟩

@[expose] def g2GL : Matrix.GeneralLinearGroup (Fin 2) F4 :=
  ⟨G2, G2inv, by decide +kernel, by decide +kernel⟩

theorem mem_stSL (A : Matrix.GeneralLinearGroup (Fin 2) F4)
    (h : (A : Matrix (Fin 2) (Fin 2) F4).det = 1) : A ∈ StatedSL 2 F4 := by
  rw [statedSL_eq_range_toGL, MonoidHom.mem_range]
  exact ⟨⟨A, h⟩, Units.ext rfl⟩

theorem det_of_mem_stSL (A : Matrix.GeneralLinearGroup (Fin 2) F4) (h : A ∈ StatedSL 2 F4) :
    (A : Matrix (Fin 2) (Fin 2) F4).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL h

@[expose] def g1 : ↥(StatedSL 2 F4) :=
  ⟨g1GL, mem_stSL _ (by
    show G1.det = 1
    rw [Matrix.det_fin_two]
    decide +kernel)⟩

@[expose] def g2 : ↥(StatedSL 2 F4) :=
  ⟨g2GL, mem_stSL _ (by
    show G2.det = 1
    rw [Matrix.det_fin_two]
    decide +kernel)⟩

@[expose] def uN : Fin 4 → (Fin 2 → F4) :=
  ![![1, 0], ![0, 1], ![1, F4.ω], ![F4.ω, F4.ω]]

@[expose] def psiN (c : V4) : Fin 2 → F4 :=
  (if c 0 = 0 then 0 else uN 0) + (if c 1 = 0 then 0 else uN 1) +
    (if c 2 = 0 then 0 else uN 2) + (if c 3 = 0 then 0 else uN 3)

theorem psiN_zero : psiN 0 = 0 := by decide +kernel

theorem psiN_add : ∀ c c' : V4, psiN (c + c') = psiN c + psiN c' := by decide +kernel

theorem psiN_inj : ∀ c c' : V4, psiN c = psiN c' → c = c' := by decide +kernel

theorem psiN_surj : ∀ v : Fin 2 → F4, ∃ c : V4, psiN c = v := by decide +kernel

@[expose] def PsiNHom : Multiplicative V4 →* ↥(⊤ : Subgroup (Multiplicative (Fin 2 → F4))) where
  toFun c := ⟨ofAdd (psiN (toAdd c)), trivial⟩
  map_one' := by
    apply Subtype.ext
    show ofAdd (psiN 0) = 1
    rw [psiN_zero]
    rfl
  map_mul' c c' := by
    apply Subtype.ext
    show ofAdd (psiN (toAdd c + toAdd c')) = ofAdd (psiN (toAdd c)) * ofAdd (psiN (toAdd c'))
    rw [psiN_add]
    rfl

theorem PsiNHom_bijective : Function.Bijective PsiNHom := by
  constructor
  · intro a b h
    have h1 : ((PsiNHom a : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → F4)))) :
        Multiplicative (Fin 2 → F4)) = (PsiNHom b : Multiplicative (Fin 2 → F4)) :=
      congrArg Subtype.val h
    have h2 : ofAdd (psiN (toAdd a)) = ofAdd (psiN (toAdd b)) := h1
    exact toAdd.injective (psiN_inj _ _ (ofAdd.injective h2))
  · intro z
    obtain ⟨c, hc⟩ := psiN_surj (toAdd (z : Multiplicative (Fin 2 → F4)))
    refine ⟨ofAdd c, Subtype.ext ?_⟩
    show ofAdd (psiN c) = (z : Multiplicative (Fin 2 → F4))
    rw [hc]
    rfl

@[expose] noncomputable def PsiN : Multiplicative V4 ≃* ↥(⊤ : Subgroup (Multiplicative (Fin 2 → F4))) :=
  MulEquiv.ofBijective PsiNHom PsiNHom_bijective

theorem PsiN_apply (c : V4) :
    ((PsiN (ofAdd c) : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → F4)))) :
      Multiplicative (Fin 2 → F4)) = ofAdd (psiN c) := rfl

theorem act_g1_psi (c : V4) :
    natAct (StatedSL 2 F4) g1 (ofAdd (psiN c)) = ofAdd (psiN (lin wC c)) := by
  have key : ∀ c : V4, G1.mulVec (psiN c) = psiN (lin wC c) := by decide +kernel
  exact congrArg ofAdd (key c)

theorem act_g2_psi (c : V4) :
    natAct (StatedSL 2 F4) g2 (ofAdd (psiN c)) = ofAdd (psiN (lin wN c)) := by
  have key : ∀ c : V4, G2.mulVec (psiN c) = psiN (lin wN c) := by decide +kernel
  exact congrArg ofAdd (key c)

theorem card_det_one_F4 : Nat.card {A : Fin 2 → Fin 2 → F4 // A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1} =
    60 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_statedSL_two_F4_le : Nat.card ↥(StatedSL 2 F4) ≤ 60 := by
  rw [← card_det_one_F4]
  refine Nat.card_le_card_of_injective
    (fun γ => ⟨fun i j => ((γ : Matrix.GeneralLinearGroup (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4) i j,
      by
        have := det_of_mem_stSL _ γ.2
        rw [Matrix.det_fin_two] at this
        exact this⟩) ?_
  intro a b hab
  have h1 : ((a : Matrix.GeneralLinearGroup (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4) =
      ((b : Matrix.GeneralLinearGroup (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4) := by
    ext i j
    exact congrFun (congrFun (congrArg Subtype.val hab) i) j
  exact Subtype.ext (Units.ext h1)

theorem binaryNaturalSL_two_two_of_data {S : Type} [CommGroup S] (L : Subgroup (MulAut S))
    (hL60 : Nat.card ↥L = 60) (x y : MulAut S)
    (hL : L = Subgroup.closure ({x, y} : Set (MulAut S)))
    (θ : S ≃* Multiplicative V4) (w : Fin 4 → V4)
    (hθx : ∀ s, θ (x s) = ofAdd (lin wC (toAdd (θ s))))
    (hθy : ∀ s, θ (y s) = ofAdd (lin w (toAdd (θ s))))
    (c : V4) (hc : ∀ u, Tc c u = 0 → u = 0) (hN : ∀ u, Tc c (lin w u) = lin wN (Tc c u)) :
    BinaryNaturalSL L ⊤ ⊥ 2 2 := by
  let β : S ≃* ↥(⊤ : Subgroup (Multiplicative (Fin 2 → F4))) :=
    (θ.trans (TcEquiv c hc)).trans PsiN
  have hβ : ∀ s, ((β s : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → F4)))) :
      Multiplicative (Fin 2 → F4)) = ofAdd (psiN (Tc c (toAdd (θ s)))) := fun s => by
    show ((PsiN (TcEquiv c hc (θ s)) : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → F4)))) :
      Multiplicative (Fin 2 → F4)) = _
    rw [← ofAdd_toAdd (θ s), TcEquiv_apply, PsiN_apply, toAdd_ofAdd]
  have hx : ∀ s, ((β (x s) : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → F4)))) :
      Multiplicative (Fin 2 → F4)) = natAct (StatedSL 2 F4) g1 (β s) := by
    intro s
    rw [hβ, hβ, hθx, toAdd_ofAdd, Tc_comm, act_g1_psi]
  have hy : ∀ s, ((β (y s) : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → F4)))) :
      Multiplicative (Fin 2 → F4)) = natAct (StatedSL 2 F4) g2 (β s) := by
    intro s
    rw [hβ, hβ, hθy, toAdd_ofAdd, hN, act_g2_psi]
  refine ⟨F4, inferInstance, inferInstance, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, F4.card]
    norm_num
  · have : Finite (FFModel.nat (StatedSL 2 F4)).Gam :=
      (inferInstance : Finite ↥(StatedSL 2 F4))
    exact realizesMod_of_two_generators (FFModel.nat_isActionModel (StatedSL 2 F4)) rfl
      (FFModel.nat_faithful (StatedSL 2 F4)) L
      (by show Nat.card ↥(StatedSL 2 F4) ≤ Nat.card ↥L; rw [hL60]; exact card_statedSL_two_F4_le)
      β x y g1 g2 hx hy hL

end CFSG.QuasithinUnique.B42A57
