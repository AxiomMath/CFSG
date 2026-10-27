module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8WrModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSA6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TS8Wr

open Equiv Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X3Aut
  CFSG.EvenSporadicStandard.M24Std

abbrev Alt6 : Type := alternatingGroup (Fin 6)

theorem alt6_nontrivial : ∃ s : Alt6, s ≠ 1 := by
  have : Nontrivial Alt6 :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [CFSG.EvenSporadicStandard.M24Std.DRes.card_alt6]; norm_num)
  exact exists_ne 1

@[expose] noncomputable def rho (f : MulAut Alt6) : Equiv.Perm (Fin 10) :=
  ((thetaEquiv.symm f : AutA6) : Equiv.Perm (Fin 10))

theorem rho_mul (f g : MulAut Alt6) : rho (f * g) = rho f * rho g := by
  simp [rho, map_mul]

theorem rho_one : rho 1 = 1 := by
  simp [rho]

theorem rho_injective : Function.Injective rho := by
  intro f g h
  have h' : (thetaEquiv.symm f : AutA6) = (thetaEquiv.symm g : AutA6) := Subtype.ext h
  exact thetaEquiv.symm.injective h'

theorem rho_mem (f : MulAut Alt6) : rho f ∈ A6Models.autA6 := (thetaEquiv.symm f).2

@[expose] noncomputable def wEl (ε : Bool) (f₁ f₂ : MulAut Alt6) : Pt :=
  Equiv.Perm.sumCongr (rho f₁) (rho f₂) * (if ε then sw else 1)

theorem wEl_mem (ε : Bool) (f₁ f₂ : MulAut Alt6) : wEl ε f₁ f₂ ∈ Wfull := by
  refine ⟨rho f₁, rho_mem f₁, rho f₂, rho_mem f₂, ?_⟩
  cases ε
  · exact Or.inl (by simp [wEl])
  · exact Or.inr (by simp [wEl])

@[expose] def Pres (τ : MulAut (Alt6 × Alt6)) (f₁ f₂ : MulAut Alt6) : Prop :=
  ∀ a b, τ (a, b) = (f₁ a, f₂ b)

@[expose] def Swp (τ : MulAut (Alt6 × Alt6)) (f₁ f₂ : MulAut Alt6) : Prop :=
  ∀ a b, τ (a, b) = (f₁ b, f₂ a)

@[expose] def Dec (τ : MulAut (Alt6 × Alt6)) (d : Bool × MulAut Alt6 × MulAut Alt6) : Prop :=
  if d.1 then Swp τ d.2.1 d.2.2 else Pres τ d.2.1 d.2.2

theorem dec_false_iff (τ : MulAut (Alt6 × Alt6)) (f₁ f₂ : MulAut Alt6) :
    Dec τ (false, f₁, f₂) ↔ Pres τ f₁ f₂ := Iff.rfl

theorem dec_true_iff (τ : MulAut (Alt6 × Alt6)) (f₁ f₂ : MulAut Alt6) :
    Dec τ (true, f₁, f₂) ↔ Swp τ f₁ f₂ := Iff.rfl

theorem exists_dec (τ : MulAut (Alt6 × Alt6)) : ∃ d, Dec τ d := by
  have hnt : ∃ s : Alt6, s ≠ 1 := alt6_nontrivial
  rcases ProdAut.mulAut_prod_cases (fun N hN => DRes.alt6_hsimple N hN)
      (fun a h => DRes.alt6_central h) hnt τ with ⟨hp1, hp2⟩ | ⟨hs1, hs2⟩
  · obtain ⟨f₁, f₂, hf⟩ := ProdAut.exists_prod_preserve τ hp1 hp2
    exact ⟨(false, f₁, f₂), (dec_false_iff τ f₁ f₂).2 hf⟩
  · obtain ⟨f₁, f₂, hf⟩ := ProdAut.exists_prod_swap τ hs1 hs2
    exact ⟨(true, f₁, f₂), (dec_true_iff τ f₁ f₂).2 hf⟩

theorem pres_unique {τ : MulAut (Alt6 × Alt6)} {f₁ f₂ g₁ g₂ : MulAut Alt6}
    (h : Pres τ f₁ f₂) (h' : Pres τ g₁ g₂) : f₁ = g₁ ∧ f₂ = g₂ := by
  constructor
  · refine MulEquiv.ext fun a => ?_
    exact congrArg Prod.fst ((h a 1).symm.trans (h' a 1))
  · refine MulEquiv.ext fun b => ?_
    exact congrArg Prod.snd ((h 1 b).symm.trans (h' 1 b))

theorem swp_unique {τ : MulAut (Alt6 × Alt6)} {f₁ f₂ g₁ g₂ : MulAut Alt6}
    (h : Swp τ f₁ f₂) (h' : Swp τ g₁ g₂) : f₁ = g₁ ∧ f₂ = g₂ := by
  constructor
  · refine MulEquiv.ext fun b => ?_
    exact congrArg Prod.fst ((h 1 b).symm.trans (h' 1 b))
  · refine MulEquiv.ext fun a => ?_
    exact congrArg Prod.snd ((h a 1).symm.trans (h' a 1))

theorem pres_not_swp {τ : MulAut (Alt6 × Alt6)} {f₁ f₂ g₁ g₂ : MulAut Alt6}
    (h : Pres τ f₁ f₂) (h' : Swp τ g₁ g₂) : False := by
  obtain ⟨s, hs⟩ := alt6_nontrivial
  have h1 : f₁ s = g₁ 1 := congrArg Prod.fst ((h s 1).symm.trans (h' s 1))
  rw [map_one] at h1
  exact hs (f₁.injective (h1.trans (map_one f₁).symm))

theorem dec_unique {τ : MulAut (Alt6 × Alt6)} {d d' : Bool × MulAut Alt6 × MulAut Alt6}
    (h : Dec τ d) (h' : Dec τ d') : d = d' := by
  obtain ⟨ε, f₁, f₂⟩ := d
  obtain ⟨ε', g₁, g₂⟩ := d'
  cases ε <;> cases ε'
  · rw [dec_false_iff] at h h'
    obtain ⟨rfl, rfl⟩ := pres_unique h h'
    rfl
  · rw [dec_false_iff] at h
    rw [dec_true_iff] at h'
    exact (pres_not_swp h h').elim
  · rw [dec_true_iff] at h
    rw [dec_false_iff] at h'
    exact (pres_not_swp h' h).elim
  · rw [dec_true_iff] at h h'
    obtain ⟨rfl, rfl⟩ := swp_unique h h'
    rfl

@[expose] noncomputable def decOf (τ : MulAut (Alt6 × Alt6)) : Bool × MulAut Alt6 × MulAut Alt6 :=
  Classical.choose (exists_dec τ)

theorem decOf_spec (τ : MulAut (Alt6 × Alt6)) : Dec τ (decOf τ) :=
  Classical.choose_spec (exists_dec τ)

@[expose] noncomputable def Psi (τ : MulAut (Alt6 × Alt6)) : Pt :=
  wEl (decOf τ).1 (decOf τ).2.1 (decOf τ).2.2

theorem Psi_eq {τ : MulAut (Alt6 × Alt6)} {d : Bool × MulAut Alt6 × MulAut Alt6}
    (h : Dec τ d) : Psi τ = wEl d.1 d.2.1 d.2.2 := by
  have hd : decOf τ = d := dec_unique (decOf_spec τ) h
  rw [Psi, hd]

theorem Psi_mem (τ : MulAut (Alt6 × Alt6)) : Psi τ ∈ Wfull := by
  unfold Psi
  exact wEl_mem _ _ _

theorem dec_mul {τ τ' : MulAut (Alt6 × Alt6)} {d d' : Bool × MulAut Alt6 × MulAut Alt6}
    (h : Dec τ d) (h' : Dec τ' d') :
    Dec (τ * τ') (xor d.1 d'.1, d.2.1 * (if d.1 then d'.2.2 else d'.2.1),
      d.2.2 * (if d.1 then d'.2.1 else d'.2.2)) := by
  obtain ⟨ε, f₁, f₂⟩ := d
  obtain ⟨ε', g₁, g₂⟩ := d'
  cases ε <;> cases ε'
  · rw [dec_false_iff] at h h'
    show Pres (τ * τ') (f₁ * g₁) (f₂ * g₂)
    intro a b
    simp only [MulAut.mul_apply, h' a b, h (g₁ a) (g₂ b)]
  · rw [dec_false_iff] at h
    rw [dec_true_iff] at h'
    show Swp (τ * τ') (f₁ * g₁) (f₂ * g₂)
    intro a b
    simp only [MulAut.mul_apply, h' a b, h (g₁ b) (g₂ a)]
  · rw [dec_true_iff] at h
    rw [dec_false_iff] at h'
    show Swp (τ * τ') (f₁ * g₂) (f₂ * g₁)
    intro a b
    simp only [MulAut.mul_apply, h' a b, h (g₁ a) (g₂ b)]
  · rw [dec_true_iff] at h h'
    show Pres (τ * τ') (f₁ * g₂) (f₂ * g₁)
    intro a b
    simp only [MulAut.mul_apply, h' a b, h (g₁ b) (g₂ a)]

theorem wEl_FF (f₁ f₂ g₁ g₂ : MulAut Alt6) :
    wEl false (f₁ * g₁) (f₂ * g₂) = wEl false f₁ f₂ * wEl false g₁ g₂ := by
  simp [wEl, rho_mul, Equiv.Perm.sumCongr_mul]

theorem wEl_FT (f₁ f₂ g₁ g₂ : MulAut Alt6) :
    wEl true (f₁ * g₁) (f₂ * g₂) = wEl false f₁ f₂ * wEl true g₁ g₂ := by
  simp only [wEl, rho_mul, if_true, if_false, mul_one, Bool.false_eq_true]
  rw [← mul_assoc, Equiv.Perm.sumCongr_mul]

theorem wEl_TF (f₁ f₂ g₁ g₂ : MulAut Alt6) :
    wEl true (f₁ * g₂) (f₂ * g₁) = wEl true f₁ f₂ * wEl false g₁ g₂ := by
  simp only [wEl, rho_mul, if_true, if_false, mul_one, Bool.false_eq_true]
  rw [sumCongr_sw_sumCongr]

theorem wEl_TT (f₁ f₂ g₁ g₂ : MulAut Alt6) :
    wEl false (f₁ * g₂) (f₂ * g₁) = wEl true f₁ f₂ * wEl true g₁ g₂ := by
  simp only [wEl, rho_mul, if_true, if_false, mul_one, Bool.false_eq_true]
  rw [← mul_assoc, sumCongr_sw_sumCongr, mul_assoc, sw_mul_sw, mul_one]

theorem wEl_mul (ε ε' : Bool) (f₁ f₂ g₁ g₂ : MulAut Alt6) :
    wEl (xor ε ε') (f₁ * (if ε then g₂ else g₁)) (f₂ * (if ε then g₁ else g₂)) =
      wEl ε f₁ f₂ * wEl ε' g₁ g₂ := by
  cases ε <;> cases ε'
  · exact wEl_FF f₁ f₂ g₁ g₂
  · exact wEl_FT f₁ f₂ g₁ g₂
  · exact wEl_TF f₁ f₂ g₁ g₂
  · exact wEl_TT f₁ f₂ g₁ g₂

theorem Psi_mul (τ τ' : MulAut (Alt6 × Alt6)) : Psi (τ * τ') = Psi τ * Psi τ' := by
  have hE := dec_mul (decOf_spec τ) (decOf_spec τ')
  rw [Psi_eq hE]
  unfold Psi
  exact wEl_mul _ _ _ _ _ _

@[expose] noncomputable def PsiHom : MulAut (Alt6 × Alt6) →* Pt where
  toFun := Psi
  map_one' := by
    have h1 : Dec (1 : MulAut (Alt6 × Alt6)) (false, 1, 1) := by
      rw [dec_false_iff]
      intro a b
      simp
    rw [Psi_eq h1]
    simp [wEl, rho_one]
  map_mul' := Psi_mul

theorem psi_eq_one {τ : MulAut (Alt6 × Alt6)} (h : Psi τ = 1) : τ = 1 := by
  obtain ⟨d, hd⟩ : ∃ d, Dec τ d := exists_dec τ
  rw [Psi_eq hd] at h
  obtain ⟨ε, f₁, f₂⟩ := d
  cases ε
  · have hw : Equiv.Perm.sumCongr (rho f₁) (rho f₂) = 1 := by simpa [wEl] using h
    obtain ⟨h1, h2⟩ := sumCongr_inj (hw.trans sumCongr_one_one.symm)
    have hf1 : f₁ = 1 := rho_injective (h1.trans rho_one.symm)
    have hf2 : f₂ = 1 := rho_injective (h2.trans rho_one.symm)
    subst hf1
    subst hf2
    refine MulEquiv.ext fun x => ?_
    obtain ⟨a, b⟩ := x
    have := (dec_false_iff τ 1 1).1 hd a b
    simpa using this
  · exfalso
    have hw : Equiv.Perm.sumCongr (rho f₁) (rho f₂) * sw = 1 := by simpa [wEl] using h
    have := congrArg (fun g : Pt => g (Sum.inl 0)) hw
    simp [sw] at this

section Embedding

variable {X : Type*} [Group X]

@[expose] noncomputable def kappa (N : Subgroup X) [N.Normal] (e0 : ↥N ≃* (Alt6 × Alt6)) :
    X →* MulAut (Alt6 × Alt6) :=
  (MulAut.congr e0).toMonoidHom.comp MulAut.conjNormal

@[expose] noncomputable def Phi (N : Subgroup X) [N.Normal] (e0 : ↥N ≃* (Alt6 × Alt6)) : X →* Wfull :=
  MonoidHom.codRestrict (PsiHom.comp (kappa N e0)) Wfull fun x => Psi_mem _

theorem Phi_apply (N : Subgroup X) [N.Normal] (e0 : ↥N ≃* (Alt6 × Alt6)) (x : X) :
    ((Phi N e0 x : Wfull) : Pt) = Psi (kappa N e0 x) := rfl

theorem Phi_injective (N : Subgroup X) [N.Normal] (e0 : ↥N ≃* (Alt6 × Alt6))
    (hC : Subgroup.centralizer (N : Set X) = ⊥) : Function.Injective (Phi N e0) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : Psi (kappa N e0 x) = 1 := by
    have := congrArg (fun g : Wfull => (g : Pt)) hx
    simpa [Phi_apply] using this
  have h2 : kappa N e0 x = 1 := psi_eq_one h1
  have h3 : MulAut.conjNormal x = 1 :=
    (MulAut.congr e0).injective (h2.trans (map_one _).symm)
  have hmem : x ∈ Subgroup.centralizer (N : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hc := congrArg (fun f : MulAut N => ((f ⟨h, hh⟩ : N) : X)) h3
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at hc
    rw [mul_inv_eq_iff_eq_mul] at hc
    exact hc.symm
  rw [hC, Subgroup.mem_bot] at hmem
  exact hmem

end Embedding

end CFSG.EvenSporadicStandard.Fin76b.TS8Wr
