module

public import CFSG.CGT.PushingUpLit.BHS5.FiveFive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS5 CFSG.Quasithin.G6

section SL

variable (F : Type) [Field F] [CharP F 2]

@[expose] noncomputable def sl2Three : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 1], by
    rw [Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]⟩

theorem sl2Three_pow_three : sl2Three F ^ 3 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow]
  fin_cases i <;> fin_cases j <;>
    simp [sl2Three, pow_succ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem sl2Three_ne_one : sl2Three F ≠ 1 := by
  intro h
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [sl2Three] at this

theorem orderOf_sl2Three : orderOf (sl2Three F) = 3 :=
  orderOf_eq_prime (sl2Three_pow_three F) (sl2Three_ne_one F)

theorem eq_zero_of_sl2Three_mulVec {v : Fin 2 → F}
    (hv : ((sl2Three F : Matrix (Fin 2) (Fin 2) F)).mulVec v = v) : v = 0 := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [sl2Three, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have ha : v 0 = 0 := by linear_combination h1
  have hb : v 1 = 0 := by linear_combination h0 + ha
  ext i
  fin_cases i
  · exact ha
  · exact hb

end SL

section Natural

variable {W : Type} [CommGroup W]

theorem isL2Natural_of_slNat {E : Subgroup (MulAut W)} {C : Subgroup W} {n : ℕ} (hn : n ≠ 0)
    (hnat : IsSLNatSection E (commV E) (commV E ⊓ fixV E) n)
    (hC : commV E ⊓ C = commV E ⊓ fixV E) : E2.IsL2Natural E C n := by
  obtain ⟨-, θ, β, hsurj, hker, hequiv⟩ := hnat
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  refine ⟨Nat.one_le_iff_ne_zero.2 hn, GaloisField 2 n, inferInstance, inferInstance, ?_, θ, β,
    hsurj, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 n hn
  · rw [hker, hC]
  · intro h u hu
    rw [hequiv h u hu, toAdd_ofAdd]

variable [Finite W]

omit [Finite W] in
theorem mem_fixV_iSup {ℰ : Set (Subgroup (MulAut W))} {v : W}
    (hv : ∀ E ∈ ℰ, v ∈ fixV E) : v ∈ fixV (⨆ E ∈ ℰ, E) := by
  have hle : (⨆ E ∈ ℰ, E) ≤ MulAction.stabilizer (MulAut W) v :=
    iSup₂_le fun E hE x hx => MulAction.mem_stabilizer_iff.2 (hv E hE x hx)
  intro x hx
  exact MulAction.mem_stabilizer_iff.1 (hle hx)

variable {P T M : Subgroup (MulAut W)} {ℰ : Set (Subgroup (MulAut W))}

omit [Finite W] in
theorem commV_inf_fixV_le_fixV_genD (hF : FiveFive P T M ℰ) {E : Subgroup (MulAut W)}
    (hE : E ∈ ℰ) : commV E ⊓ fixV E ≤ fixV (genD P) := by
  intro v hv
  rw [← hF.iSup_eq]
  refine mem_fixV_iSup fun E' hE' => ?_
  by_cases hne : E = E'
  · rw [← hne]
    exact hv.2
  · exact hF.commV_le E hE E' hE' hne hv.1

theorem commV_inf_fixV_eq_of_slType2 (h : Hyp51 P T M) (hV : ∀ v : W, v ^ 2 = 1)
    (hF : FiveFive P T M ℰ) {E : Subgroup (MulAut W)} (hE : E ∈ ℰ)
    {n : ℕ} (hnat : IsSLNatSection E (commV E) (commV E ⊓ fixV E) n)
    {K : Subgroup (MulAut W)} (hKD : K ≤ genD P) (hK3 : ∀ x ∈ P, orderOf x = 3 → x ∈ K) :
    commV E ⊓ fixV K = commV E ⊓ fixV E := by
  refine le_antisymm (fun v hv => ⟨hv.1, ?_⟩) fun v hv =>
    ⟨hv.1, fun x hx => commV_inf_fixV_le_fixV_genD hF hE hv x (hKD hx)⟩
  obtain ⟨hinv, θ, β, -, hker, hequiv⟩ := hnat
  set g : ↥E := θ.symm (sl2Three (GaloisField 2 n)) with hg
  have hgo : orderOf (g : MulAut W) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_sl2Three]
  have hgK : (g : MulAut W) ∈ K := hK3 _ (hF.le_P h hV hE g.2) hgo
  have hgv : (g : MulAut W) v = v := hv.2 _ hgK
  have hp : (g : MulAut W) (⟨v, hv.1⟩ : ↥(commV E)) ∈ commV E := by
    rw [hgv]
    exact hv.1
  have he := hequiv g ⟨v, hv.1⟩ hp
  have hθg : θ g = sl2Three (GaloisField 2 n) := by rw [hg, MulEquiv.apply_symm_apply]
  have hsub : (⟨(g : MulAut W) v, hp⟩ : ↥(commV E)) = ⟨v, hv.1⟩ := Subtype.ext hgv
  rw [hsub, hθg] at he
  have hfix : ((sl2Three (GaloisField 2 n) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n))).mulVec
      (Multiplicative.toAdd (β ⟨v, hv.1⟩)) = Multiplicative.toAdd (β ⟨v, hv.1⟩) := by
    have := congrArg Multiplicative.toAdd he
    rw [toAdd_ofAdd] at this
    exact this.symm
  have h0 := eq_zero_of_sl2Three_mulVec (GaloisField 2 n) hfix
  have hk : (⟨v, hv.1⟩ : ↥(commV E)) ∈ β.ker := by
    rw [MonoidHom.mem_ker]
    exact Multiplicative.toAdd.injective h0
  rw [hker] at hk
  exact (Subgroup.mem_subgroupOf.1 hk).2

end Natural

section Sym

variable {W : Type} [CommGroup W]

@[expose] def coreModEquivEven (m : ℕ) : ↥(coreMod m) ≃* Multiplicative (evenWeight m) where
  toFun x := Multiplicative.ofAdd ⟨Multiplicative.toAdd (x : PermMod m), x.2⟩
  invFun y := ⟨Multiplicative.ofAdd
    ((Multiplicative.toAdd y : evenWeight m) : Fin m → ZMod 2), (Multiplicative.toAdd y).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem isSymCoreModule_of_data {E : Subgroup (MulAut W)} {m : ℕ}
    (θ : ↥E ≃* Equiv.Perm (Fin m)) (β : ↥(commV E) →* coreMod m)
    (hsurj : Function.Surjective β) (hker : β.ker = ⊥)
    (hequiv : ∀ (x : ↥E) (p : ↥(commV E)) (hp : (x : MulAut W) p ∈ commV E),
      β ⟨(x : MulAut W) p, hp⟩ = coreAct m (θ x) (β p)) :
    CFSG.AGLEmbeddingD2.GN.IsSymCoreModule E m := by
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).1 hker
  refine ⟨θ, (MulEquiv.ofBijective β ⟨hinj, hsurj⟩).trans (coreModEquivEven m),
    fun h u hu i => ?_⟩
  show Multiplicative.toAdd ((β ⟨(h : MulAut W) u, hu⟩ : ↥(coreMod m)) : PermMod m) i =
    Multiplicative.toAdd ((β u : ↥(coreMod m)) : PermMod m) ((θ h)⁻¹ i)
  rw [hequiv h u hu]
  exact permAct_apply m (θ h) (β u) i

end Sym

end CFSG.AGLEmbeddingD2.Tits.E23
