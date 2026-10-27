module

public import CFSG.GH74.QTGen4.U42.ModelFrameB
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5 CFSG.Quasithin.H13.F431.U42 U42F431

@[expose] noncomputable def psiM : Vsub →* W5 where
  toFun := psiF
  map_one' := psiF_one
  map_mul' := psiF_mul

theorem psiM_apply (v : Vsub) : psiM v = psiF v := rfl

theorem psiM_injective : Function.Injective psiM := by
  intro v w h
  have hvw : psiF v = psiF w := h
  have hv := sOf_spec v
  have hw := sOf_spec w
  rw [psiF_eq v hv.1 hv.2, psiF_eq w hw.1 hw.2] at hvw
  have hFV : FV (sOf v) = FV (sOf w) :=
    congrArg Subtype.val (Multiplicative.ofAdd.injective hvw)
  have hlist : subProdL L0 (sOf v) = subProdL L0 (sOf w) :=
    (chkFVsub _ hv.1 _ hw.1).2 hFV
  have hw' : RepL (subProdL L0 (sOf v)) (w : P45) := by
    rw [hlist]
    exact hw.2
  exact Subtype.ext (Subtype.ext (eq_of_repL hv.2 hw'))

@[expose] noncomputable def psiEq : Vsub ≃* W5 :=
  MulEquiv.ofBijective psiM
    ((Nat.bijective_iff_injective_and_card psiM).2
      ⟨psiM_injective, card_Vsub_eq.trans card_W5.symm⟩)

theorem two_pow_lt (k : Fin 5) : 2 ^ (k : ℕ) < 32 := by
  have h : ∀ j < 5, 2 ^ j < 32 := by decide
  exact h k k.isLt

theorem mem_sV_gen (j : Fin 5) : sY (ptL j) ∈ Vsub :=
  Subgroup.subset_closure ⟨ptL j, (mem_L0S_ptL _).2 ⟨j, rfl⟩, rfl⟩

theorem chkSingle_repL (k : Fin 5) :
    RepL (subProdL L0 (2 ^ (k : ℕ))) ((sY (ptL k) : Y) : P45) := by
  rw [chkSingle (k : ℕ) k.isLt, ← ptL_val k]
  exact repL_sY (ptL k)

theorem psiF_gen (j : Fin 5) (h : sY (ptL j) ∈ Vsub) :
    psiF ⟨sY (ptL j), h⟩ = Multiplicative.ofAdd ⟨FV (2 ^ (j : ℕ)), FV_mem _⟩ :=
  psiF_eq ⟨sY (ptL j), h⟩ (two_pow_lt j) (chkSingle_repL j)

theorem FV_pow_apply (j i : Fin 5) :
    FV (2 ^ (j : ℕ)) i = if i = j then 0 else 1 := by
  revert j i
  decide +kernel

theorem pw_FV (σ : Equiv.Perm (Fin 5)) (j : Fin 5) :
    ((pw σ ⟨FV (2 ^ (j : ℕ)), FV_mem _⟩ : ↥Ev) : Fin 5 → ZMod 2) =
      FV (2 ^ ((σ j : Fin 5) : ℕ)) := by
  funext i
  rw [pw_coe]
  simp only [FV_pow_apply, Equiv.Perm.inv_eq_iff_eq]

theorem psiF_inv (v : Vsub) :
    psiF v⁻¹ = (psiF v)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← psiF_mul, mul_inv_cancel, psiF_one])

theorem psiF_conj_key
    (a : ↥P2) {x : Y} (hx : x ∈ Vsub) : ∀ h : x ∈ Vsub,
      psiF ⟨(a : Y) * x * (a : Y)⁻¹, P2_conj_V a.2 h⟩ = pact (permOf a) (psiF ⟨x, h⟩) := by
  refine Subgroup.closure_induction
    (p := fun (x : Y) _ => ∀ h : x ∈ Vsub,
      psiF ⟨(a : Y) * x * (a : Y)⁻¹, P2_conj_V a.2 h⟩ = pact (permOf a) (psiF ⟨x, h⟩))
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨p, hp, rfl⟩ h
    obtain ⟨j, rfl⟩ := (mem_L0S_ptL p).1 hp
    have e : (a : Y) * sY (ptL j) * (a : Y)⁻¹ = sY (ptL (permOf a j)) := by
      rw [sY_conj, ptL_permOf]
    have h1 : psiF ⟨(a : Y) * sY (ptL j) * (a : Y)⁻¹, P2_conj_V a.2 h⟩ =
        psiF ⟨sY (ptL (permOf a j)), mem_sV_gen _⟩ := congrArg psiF (Subtype.ext e)
    rw [h1, psiF_gen, psiF_gen, pact_ofAdd]
    exact congrArg Multiplicative.ofAdd (Subtype.ext (pw_FV (permOf a) j).symm)
  · intro h
    have e : (⟨(a : Y) * 1 * (a : Y)⁻¹, P2_conj_V a.2 h⟩ : Vsub) = 1 := Subtype.ext (by simp)
    have e' : (⟨(1 : Y), h⟩ : Vsub) = 1 := Subtype.ext rfl
    rw [e, e', psiF_one, map_one]
  · intro x y hx hy hPx hPy h
    have hxa : (a : Y) * x * (a : Y)⁻¹ ∈ Vsub := P2_conj_V a.2 hx
    have hya : (a : Y) * y * (a : Y)⁻¹ ∈ Vsub := P2_conj_V a.2 hy
    have e : (⟨(a : Y) * (x * y) * (a : Y)⁻¹, P2_conj_V a.2 h⟩ : Vsub) =
        ⟨(a : Y) * x * (a : Y)⁻¹, hxa⟩ * ⟨(a : Y) * y * (a : Y)⁻¹, hya⟩ :=
      Subtype.ext (by
        show (a : Y) * (x * y) * (a : Y)⁻¹ = ((a : Y) * x * (a : Y)⁻¹) * ((a : Y) * y * (a : Y)⁻¹)
        group)
    have e2 : (⟨x * y, h⟩ : Vsub) = ⟨x, hx⟩ * ⟨y, hy⟩ := Subtype.ext rfl
    rw [e, e2, psiF_mul, psiF_mul, hPx hx, hPy hy, map_mul]
  · intro x hx hPx h
    have hxa : (a : Y) * x * (a : Y)⁻¹ ∈ Vsub := P2_conj_V a.2 hx
    have e : (⟨(a : Y) * x⁻¹ * (a : Y)⁻¹, P2_conj_V a.2 h⟩ : Vsub) =
        (⟨(a : Y) * x * (a : Y)⁻¹, hxa⟩ : Vsub)⁻¹ :=
      Subtype.ext (by
        show (a : Y) * x⁻¹ * (a : Y)⁻¹ = ((a : Y) * x * (a : Y)⁻¹)⁻¹
        group)
    have e2 : (⟨x⁻¹, h⟩ : Vsub) = (⟨x, hx⟩ : Vsub)⁻¹ := Subtype.ext rfl
    rw [e, e2, psiF_inv, psiF_inv, hPx hx, map_inv]

theorem psiF_conj
    (a : ↥P2) {x : Y} (hx : x ∈ Vsub) :
    psiF ⟨(a : Y) * x * (a : Y)⁻¹, P2_conj_V a.2 hx⟩ = pact (permOf a) (psiF ⟨x, hx⟩) :=
  psiF_conj_key a hx hx

theorem psiEq_apply (v : Vsub) : psiEq v = psiM v := rfl

theorem conjAct_val (a : Subgroup.normalizer (Vsub : Set Y))
    (v : Vsub) : ((conjAct Vsub a v : Vsub) : Y) = (a : Y) * v * (a : Y)⁻¹ := rfl

theorem hN_le :
    P2 ≤ Subgroup.normalizer (Vsub : Set Y) :=
  normalizer_V.symm.le

theorem psiM_conj
    (a : ↥P2) (v : Vsub) :
    psiM (conjAct Vsub ⟨(a : Y), hN_le a.2⟩ v) = pact (permOf a) (psiM v) := by
  rw [psiM_apply, psiM_apply]
  have e : (conjAct Vsub ⟨(a : Y), hN_le a.2⟩ v) =
      ⟨(a : Y) * (v : Y) * (a : Y)⁻¹, P2_conj_V a.2 v.2⟩ :=
    Subtype.ext (conjAct_val _ _)
  rw [e]
  exact psiF_conj a v.2

end CFSG.GH74.QTGen4.U42
