module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46NClass
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NAut

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {R : Subgroup X}

namespace Inst

variable (I : Inst S)

theorem μ_two_eq_one (hO : Fus S) (n : normalizer (I.E : Set X)) {p : V4}
    (hp : p.2.2.1 = 1) : (I.μ n p).2.2.1 = 1 := by
  rw [← I.conjTo_wV_iff hO, ← I.conj_wV, conjTo_conj_iff, I.conjTo_wV_iff hO]
  exact hp

theorem μ_ki (H : Hyp S R) (n : normalizer (I.E : Set X)) : I.μ n (bas 3) = bas 3 :=
  I.μ_eq_of (by rw [I.wV_bas_three]; exact I.k_fixed H n.2)

@[expose] noncomputable def βf (n : normalizer (I.E : Set X)) (j : Fin 2 × Fin 2) : Fin 2 × Fin 2 :=
  blk (I.μ n (pt j))

theorem βf_mul (H : Hyp S R) (n m : normalizer (I.E : Set X)) (j : Fin 2 × Fin 2) :
    I.βf (n * m) j = I.βf n (I.βf m j) := by
  show blk (I.μ (n * m) (pt j)) = blk (I.μ n (pt (blk (I.μ m (pt j)))))
  rw [I.μ_mul]
  have h2 := I.μ_two_eq_one H.fus m (p := pt j) rfl
  generalize I.μ m (pt j) = P at h2 ⊢
  obtain ⟨p, q, r, s'⟩ := P
  simp only at h2
  subst h2
  rw [I.μ_eq_lin n (p, q, 1, s'), I.μ_eq_lin n (pt (blk (p, q, 1, s'))),
    blk_lin_ki _ (I.μ_ki H n)]
  rfl

theorem βf_one (j : Fin 2 × Fin 2) : I.βf 1 j = j := by
  simp [βf, I.μ_one, blk, pt]

@[expose] noncomputable def blockHom (H : Hyp S R) :
    normalizer (I.E : Set X) →* Perm (Fin 2 × Fin 2) where
  toFun n :=
    { toFun := I.βf n
      invFun := I.βf n⁻¹
      left_inv := fun j => by rw [← I.βf_mul H, inv_mul_cancel, I.βf_one]
      right_inv := fun j => by rw [← I.βf_mul H, mul_inv_cancel, I.βf_one] }
  map_one' := Equiv.ext fun j => I.βf_one j
  map_mul' n m := Equiv.ext fun j => I.βf_mul H n m j

theorem blockHom_apply (H : Hyp S R) (n : normalizer (I.E : Set X)) (j : Fin 2 × Fin 2) :
    I.blockHom H n j = blk (I.μ n (pt j)) := rfl

theorem exists_setup (H : Hyp S R) : ∃ ε : Fin 2, (ε = 0 ↔ I.CaseI) ∧
    (∃ v, ∃ hv : v ∈ R, ∃ w, ∃ hw : w ∈ R, ∃ w', ∃ hw' : w' ∈ normalizer (I.E : Set X),
      (∀ i, I.μ ⟨v, I.R_le H hv⟩ (bas i) = vC i) ∧
      (∀ i, I.μ ⟨w, I.R_le H hw⟩ (bas i) = wC ε i) ∧ (∀ i, I.μ ⟨w', hw'⟩ (bas i) = w'C ε i)) ∧
    ∀ n : normalizer (I.E : Set X), ∃ a b c : Fin 2, ∃ σ₁ ∈ three, ∃ σ₂ ∈ three, σ₁ ≠ σ₂ ∧
      ∀ i, I.μ n (bas i) = HSFLit.cls ε a b c σ₁ σ₂ i := by
  obtain ⟨ε, hε, hvww⟩ := I.exists_vww H
  obtain ⟨ε', hε', hcl⟩ := I.classify H
  have : ε' = ε := by
    by_cases hI : I.CaseI
    · rw [hε.mpr hI, hε'.mpr hI]
    · have h1 : ε ≠ 0 := fun h => hI (hε.mp h)
      have h2 : ε' ≠ 0 := fun h => hI (hε'.mp h)
      rcases Fin.exists_fin_two.mp ⟨ε, rfl⟩ with rfl | rfl
      · exact absurd rfl h1
      · rcases Fin.exists_fin_two.mp ⟨ε', rfl⟩ with rfl | rfl
        · exact absurd rfl h2
        · rfl
  subst this
  exact ⟨ε', hε, hvww, hcl⟩

@[expose] noncomputable def chiHom (H : Hyp S R) (ε : Fin 2)
    (hcl : ∀ n : normalizer (I.E : Set X), ∃ a b c : Fin 2, ∃ σ₁ ∈ three, ∃ σ₂ ∈ three,
      σ₁ ≠ σ₂ ∧ ∀ i, I.μ n (bas i) = HSFLit.cls ε a b c σ₁ σ₂ i) :
    normalizer (I.E : Set X) →* Multiplicative (Fin 2) where
  toFun n := Multiplicative.ofAdd (ind ε (I.μ n (bas 2)))
  map_one' := by
    rw [I.μ_one]
    simp [ind, bas]
  map_mul' n m := by
    rw [I.μ_mul]
    obtain ⟨a, b, c, σ₁, h₁, σ₂, h₂, h12, hn⟩ := hcl n
    have h2 := I.μ_two_eq_one H.fus m (p := bas 2) rfl
    generalize I.μ m (bas 2) = P at h2 ⊢
    obtain ⟨p, q, r, s'⟩ := P
    simp only at h2
    subst h2
    rw [I.μ_eq_lin n (p, q, 1, s'), (show (fun i => I.μ n (bas i)) = HSFLit.cls ε a b c σ₁ σ₂ from
      funext hn), ((ind_cls ε a b c σ₁ h₁ σ₂ h₂).resolve_left h12) p q s', hn 2, ← ofAdd_add,
      add_comm]

theorem lin_bas_self (p : V4) : lin bas p = p := by
  obtain ⟨a, b, c, d⟩ := p
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> rfl

theorem ker_prod (H : Hyp S R) (ε : Fin 2)
    (hcl : ∀ n : normalizer (I.E : Set X), ∃ a b c : Fin 2, ∃ σ₁ ∈ three, ∃ σ₂ ∈ three,
      σ₁ ≠ σ₂ ∧ ∀ i, I.μ n (bas i) = HSFLit.cls ε a b c σ₁ σ₂ i) :
    ((I.blockHom H).prod (I.chiHom H ε hcl)).ker =
      (centralizer (I.E : Set X)).subgroupOf (normalizer (I.E : Set X)) := by
  ext n
  rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.prod_apply, Prod.mk_eq_one]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨a, b, c, σ₁, h₁, σ₂, h₂, h12, hn⟩ := hcl n
    have hcols : (fun i => I.μ n (bas i)) = HSFLit.cls ε a b c σ₁ σ₂ := funext hn
    have hb : ∀ j, blk (lin (HSFLit.cls ε a b c σ₁ σ₂) (pt j)) = j := fun j => by
      have := congrArg (fun e : Perm (Fin 2 × Fin 2) => e j) h1
      simp only [Perm.coe_one, id_eq] at this
      rw [I.blockHom_apply, I.μ_eq_lin, hcols] at this
      exact this
    have hi : ind ε (HSFLit.cls ε a b c σ₁ σ₂ 2) = 0 := by
      have : Multiplicative.ofAdd (ind ε (I.μ n (bas 2))) = 1 := h2
      rw [hn 2] at this
      exact this
    have := (((cls_eq_bas ε a b c σ₁ h₁ σ₂ h₂).resolve_left h12).resolve_left
      (not_not.mpr hb)).resolve_left (not_not.mpr hi)
    exact (I.μ_eq_id_iff n).mp fun i => (hn i).trans (this i)
  · intro hn
    have hμ : ∀ i, I.μ n (bas i) = bas i := (I.μ_eq_id_iff n).mpr hn
    have hcols : (fun i => I.μ n (bas i)) = bas := funext hμ
    refine ⟨Equiv.ext fun j => ?_, ?_⟩
    · rw [I.blockHom_apply, I.μ_eq_lin, hcols, lin_bas_self]
      rfl
    · show Multiplicative.ofAdd (ind ε (I.μ n (bas 2))) = 1
      rw [hμ 2]
      rfl

theorem exists_d_cols : ∃ d, ∃ hd : d ∈ normalizer (I.E : Set X) ⊓ centralizer ({t} : Set X),
    ∀ i, I.μ ⟨d, hd.1⟩ (bas i) = dCols i := by
  obtain ⟨d, hd, hdz, hdy, -⟩ := I.exists_d
  have hdt : d * t * d⁻¹ = t := by rw [mem_centralizer_singleton_iff.mp hd.2]; group
  refine ⟨d, hd, I.μ_bas_of ?_ ?_ ?_ ?_⟩
  · show d * S.z * d⁻¹ = _
    rw [hdz]; simp [dCols, sigCols, wV]
  · show d * I.yi * d⁻¹ = _
    rw [hdy]; simp [dCols, sigCols, wV]
  · show d * t * d⁻¹ = _
    rw [hdt]; simp [dCols, sigCols, wV]
  · show d * I.ki * d⁻¹ = _
    rw [I.conj_ki_of_mem_NC hd]; simp [dCols, sigCols, wV]

theorem μ_pw3 {n : normalizer (I.E : Set X)} {c : Fin 4 → V4} (hc : ∀ i, I.μ n (bas i) = c i)
    (e : Fin 3) (i : Fin 4) : I.μ (n ^ (e : ℕ)) (bas i) = pw3 c e i := by
  fin_cases e
  · simp [pw3, idCols, I.μ_one]
  · simp [pw3, hc]
  · show I.μ (n ^ 2) (bas i) = pw3 c 2 i
    rw [pow_two, I.μ_comp hc hc]
    rfl

@[expose] def multFinZMod : Multiplicative (Fin 2) ≃* Multiplicative (ZMod 2) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem exists_prod_surjective (H : Hyp S R) : ∃ ε : Fin 2, (ε = 0 ↔ I.CaseI) ∧
    ∃ hcl : (∀ n : normalizer (I.E : Set X), ∃ a b c : Fin 2, ∃ σ₁ ∈ three, ∃ σ₂ ∈ three,
      σ₁ ≠ σ₂ ∧ ∀ i, I.μ n (bas i) = HSFLit.cls ε a b c σ₁ σ₂ i),
      Function.Surjective ((I.blockHom H).prod (I.chiHom H ε hcl)) := by
  obtain ⟨ε, hε, ⟨v, hv, w, hw, w', hw', hvc, hwc, hw'c⟩, hcl⟩ := I.exists_setup H
  obtain ⟨d, hd, hdc⟩ := I.exists_d_cols
  have hxN : S.x ∈ normalizer (I.E : Set X) := I.R_le H (H.le (x_mem_TE S))
  set Φ := (I.blockHom H).prod (I.chiHom H ε hcl) with hΦ
  set V : normalizer (I.E : Set X) := ⟨v, I.R_le H hv⟩
  set W : normalizer (I.E : Set X) := ⟨w, I.R_le H hw⟩
  set W' : normalizer (I.E : Set X) := ⟨w', hw'⟩
  set D : normalizer (I.E : Set X) := ⟨d, hd.1⟩
  set Xn : normalizer (I.E : Set X) := ⟨S.x, hxN⟩
  have hxc := I.x_cols hxN
  let g : Fin 2 × Fin 2 × Fin 2 × Fin 3 × Fin 2 → normalizer (I.E : Set X) := fun p =>
    V ^ (p.2.2.1 : ℕ) * (W ^ (p.1 : ℕ) * W' ^ (p.2.1 : ℕ)) *
      (D ^ (p.2.2.2.1 : ℕ) * Xn ^ (p.2.2.2.2 : ℕ))
  have hgc : ∀ p i, I.μ (g p) (bas i) = eCols ε p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 i := by
    intro p i
    rw [I.μ_comp (fun j => I.μ_comp (I.μ_pw hvc _) (fun k => I.μ_comp (I.μ_pw hwc _)
      (I.μ_pw hw'c _) k) j) (fun j => I.μ_comp (I.μ_pw3 hdc _) (I.μ_pw hxc _) j)]
    rfl
  have hinj : Function.Injective (fun p => Φ (g p)) := by
    intro p p' h
    have h1 : I.blockHom H (g p) = I.blockHom H (g p') := congrArg Prod.fst h
    have h2 : I.chiHom H ε hcl (g p) = I.chiHom H ε hcl (g p') := congrArg Prod.snd h
    have hb : ∀ k, blk (lin (eCols ε p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) (pt k)) =
        blk (lin (eCols ε p'.1 p'.2.1 p'.2.2.1 p'.2.2.2.1 p'.2.2.2.2) (pt k)) := fun k => by
      have h3 : I.blockHom H (g p) k = I.blockHom H (g p') k := by rw [h1]
      rw [I.blockHom_apply, I.blockHom_apply, I.μ_eq_lin (g p) (pt k),
        I.μ_eq_lin (g p') (pt k)] at h3
      rwa [show (fun i => I.μ (g p) (bas i)) = _ from funext (hgc p),
        show (fun i => I.μ (g p') (bas i)) = _ from funext (hgc p')] at h3
    have hi : ind ε (eCols ε p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 2) =
        ind ε (eCols ε p'.1 p'.2.1 p'.2.2.1 p'.2.2.2.1 p'.2.2.2.2 2) := by
      have : Multiplicative.ofAdd (ind ε (I.μ (g p) (bas 2))) =
          Multiplicative.ofAdd (ind ε (I.μ (g p') (bas 2))) := h2
      rw [hgc p, hgc p'] at this
      exact Multiplicative.ofAdd.injective this
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := eCols_injective ε _ _ _ _ _ _ _ _ _ _ ⟨hb, hi⟩
    obtain ⟨a, b, c, i, j⟩ := p
    obtain ⟨a', b', c', i', j'⟩ := p'
    simp only at h₁ h₂ h₃ h₄ h₅
    subst h₁ h₂ h₃ h₄ h₅
    rfl
  refine ⟨ε, hε, hcl, ?_⟩
  have hcard : Fintype.card (Fin 2 × Fin 2 × Fin 2 × Fin 3 × Fin 2) =
      Fintype.card (Perm (Fin 2 × Fin 2) × Multiplicative (Fin 2)) := by
    simp [Fintype.card_prod, Fintype.card_perm, Nat.factorial]
  have hbij := (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩
  intro y
  obtain ⟨p, hp⟩ := hbij.2 y
  exact ⟨g p, hp⟩

theorem automizer (H : Hyp S R) :
    Nonempty (normalizer (S.E I.yi : Set X) ⧸
      (centralizer (S.E I.yi : Set X)).subgroupOf (normalizer (S.E I.yi : Set X)) ≃*
        Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)) := by
  obtain ⟨ε, -, hcl, hsurj⟩ := I.exists_prod_surjective H
  have hker := I.ker_prod H ε hcl
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective _ hsurj).trans
      (MulEquiv.prodCongr (finProdFinEquiv.permCongrHom) multFinZMod))⟩

theorem blockHom_surjective (H : Hyp S R) : Function.Surjective (I.blockHom H) := by
  obtain ⟨ε, -, hcl, hsurj⟩ := I.exists_prod_surjective H
  intro π
  obtain ⟨n, hn⟩ := hsurj (π, 1)
  exact ⟨n, congrArg Prod.fst hn⟩

end Inst

end CFSG.ComponentClassification.HSFLit.KD46
