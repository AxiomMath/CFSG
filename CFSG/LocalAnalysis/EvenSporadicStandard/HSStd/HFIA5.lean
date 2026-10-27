module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIA5Fix
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Action
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHAut2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open Equiv Equiv.Perm Subgroup CFSG.EvenSporadicStandard.HSStd.HL34
  CFSG.EvenSporadicStandard.HSStd.HOv CFSG.EvenSporadicStandard.TwoHS

@[expose] noncomputable def swapHom :
    MulAut (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) →* Multiplicative (ZMod 2) :=
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  SAFyHAut.phi (alternatingGroup.center_eq_bot (by simp))

theorem swapHom_eq_one_iff {α : MulAut (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))} :
    swapHom α = 1 ↔ α ∈ SAFyHAut.presSubgroup (alternatingGroup (Fin 5)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact SAFyHAut.phi_eq_one_iff (alternatingGroup.center_eq_bot (by simp))

theorem exists_factors {α : MulAut (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))}
    (h : swapHom α = 1) :
    ∃ e₁ e₂ : MulAut (alternatingGroup (Fin 5)),
      (∀ a, α (a, 1) = (e₁ a, 1)) ∧ ∀ b, α (1, b) = (1, e₂ b) := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hpres := (swapHom_eq_one_iff).1 h
  refine ⟨SAFyHAut.restr α hpres, (SAFyHAut.kk (alternatingGroup.center_eq_bot (by simp)) α).left
    (Multiplicative.ofAdd 1), SAFyHAut.apply_one_eq_restr α hpres, ?_⟩
  exact (SAFyHAut.kk_left_ofAdd_one_eq_iff (alternatingGroup.center_eq_bot (by simp)) h _).1 rfl

theorem card_fixed_prod {α : MulAut (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))}
    {e₁ e₂ : MulAut (alternatingGroup (Fin 5))} (h₁ : ∀ a, α (a, 1) = (e₁ a, 1))
    (h₂ : ∀ b, α (1, b) = (1, e₂ b)) :
    Nat.card {p : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) // α p = p} =
      Nat.card {a : alternatingGroup (Fin 5) // e₁ a = a} *
        Nat.card {b : alternatingGroup (Fin 5) // e₂ b = b} := by
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun p => (⟨p.1.1, ?_⟩, ⟨p.1.2, ?_⟩)
      invFun := fun q => ⟨(q.1.1, q.2.1), ?_⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  · have hp : α p.1 = (e₁ p.1.1, e₂ p.1.2) := by
      have : p.1 = (p.1.1, 1) * (1, p.1.2) := by simp
      rw [this, map_mul, h₁, h₂]
      simp
    have := p.2
    rw [hp] at this
    exact (Prod.ext_iff.1 this).1
  · have hp : α p.1 = (e₁ p.1.1, e₂ p.1.2) := by
      have : p.1 = (p.1.1, 1) * (1, p.1.2) := by simp
      rw [this, map_mul, h₁, h₂]
      simp
    have := p.2
    rw [hp] at this
    exact (Prod.ext_iff.1 this).2
  · have hp : α (q.1.1, q.2.1) = (e₁ q.1.1, e₂ q.2.1) := by
      have : ((q.1.1, q.2.1) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) =
          (q.1.1, 1) * (1, q.2.1) := by simp
      rw [this, map_mul, h₁, h₂]
      simp
    rw [hp, q.1.2, q.2.2]

theorem card_inf_centralizer_eq_fixed {D : Type*} [Group D] (H : Subgroup D) [H.Normal]
    {B : Type*} [Group B] (ψ : ↥H ≃* B) (x : D) :
    Nat.card ↥(H ⊓ centralizer ({x} : Set D)) = Nat.card {p : B // actionHom H ψ x p = p} := by
  let e1 : ↥(H ⊓ centralizer ({x} : Set D)) ≃ {h : ↥H // (h : D) ∈ centralizer ({x} : Set D)} :=
    ⟨fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩, fun y => ⟨y.1.1, y.1.2, y.2⟩, fun _ => rfl, fun _ => rfl⟩
  let e2 : {h : ↥H // (h : D) ∈ centralizer ({x} : Set D)} ≃
      {p : B // actionHom H ψ x p = p} :=
    ψ.toEquiv.subtypeEquiv (fun h => by
      show (h : D) ∈ centralizer ({x} : Set D) ↔ actionHom H ψ x (ψ h) = ψ h
      rw [actionHom_apply, mem_centralizer_singleton_iff]
      constructor
      · intro hc
        exact congrArg ψ (Subtype.ext (by
          rw [MulAut.conjNormal_apply]
          exact mul_inv_eq_iff_eq_mul.2 hc.symm))
      · intro hc
        have h1 := congrArg Subtype.val (ψ.injective hc)
        rw [MulAut.conjNormal_apply] at h1
        exact (mul_inv_eq_iff_eq_mul.1 h1).symm)
  exact Nat.card_congr (e1.trans e2)

theorem swapHom_ne_one_of_good {D : Type} [Group D] [Finite D] (E : Subgroup D) [E.Normal]
    (e : ↥E ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) {x : D}
    (hx : orderOf x = 2)
    (ex : Nonempty (↥(centralizer ({x} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5))) :
    swapHom (actionHom E e x) ≠ 1 := by
  intro hph
  obtain ⟨e₁, e₂, h₁, h₂⟩ := exists_factors hph
  have hx2 : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hφ2 : actionHom E e x * actionHom E e x = 1 := by rw [← map_mul, hx2, map_one]
  have he₁2 : e₁ * e₁ = 1 := by
    refine MulEquiv.ext fun a => ?_
    have := congrArg (fun f : MulAut (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) =>
      (f (a, 1)).1) hφ2
    simpa [MulAut.mul_apply, h₁] using this
  have he₂2 : e₂ * e₂ = 1 := by
    refine MulEquiv.ext fun a => ?_
    have := congrArg (fun f : MulAut (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) =>
      (f (1, a)).2) hφ2
    simpa [MulAut.mul_apply, h₂] using this
  obtain ⟨ex'⟩ := ex
  obtain ⟨J, hC, hd, ⟨eJ⟩⟩ := exists_complement hx ex'
  have hTcard : Nat.card ↥(centralizer ({x} : Set D)) = 240 := card_centralizer_of_good ⟨ex'⟩
  have hXcard : Nat.card ↥(E ⊓ centralizer ({x} : Set D)) =
      Nat.card {a : alternatingGroup (Fin 5) // e₁ a = a} *
        Nat.card {b : alternatingGroup (Fin 5) // e₂ b = b} := by
    rw [card_inf_centralizer_eq_fixed E e x, card_fixed_prod h₁ h₂]
  obtain ⟨hf₁, hf₁'⟩ := fixed_card_cases e₁ he₁2
  obtain ⟨hf₂, hf₂'⟩ := fixed_card_cases e₂ he₂2
  have hnotle : ¬ (E ⊓ centralizer ({x} : Set D)) ≤ zpowers x := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hx, hXcard] at h1
    have := Nat.mul_le_mul hf₁ hf₂
    omega
  have hXn : ∀ τ ∈ centralizer ({x} : Set D), ∀ y ∈ E ⊓ centralizer ({x} : Set D),
      τ * y * τ⁻¹ ∈ E ⊓ centralizer ({x} : Set D) := by
    intro τ hτ y hy
    refine ⟨Normal.conj_mem inferInstance y hy.1 τ, ?_⟩
    exact (centralizer ({x} : Set D)).mul_mem
      ((centralizer ({x} : Set D)).mul_mem hτ hy.2) ((centralizer ({x} : Set D)).inv_mem hτ)
  have h60 := sixty_le_card_of_not_le_zpowers hC eJ hXn inf_le_right hnotle
  have hdvd : Nat.card ↥(E ⊓ centralizer ({x} : Set D)) ∣ 240 := by
    rw [← hTcard]
    exact Subgroup.card_dvd_of_le inf_le_right
  rw [hXcard] at h60 hdvd
  have hnum := prod_eq_of_dvd _ _ hf₁ hf₂ hf₁' hf₂' h60 hdvd
  have hXT : E ⊓ centralizer ({x} : Set D) = centralizer ({x} : Set D) :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hTcard, ← hXcard] at *; omega)
  have hJE : J ≤ E := by
    intro j hj
    have h1 : j ∈ zpowers x ⊔ J := mem_sup_right hj
    rw [← hC, ← hXT] at h1
    exact h1.1
  exact not_injective_perm_five_to_A5A5
    ((e : ↥E →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)).comp
      ((Subgroup.inclusion hJE).comp eJ.symm.toMonoidHom))
    (e.injective.comp ((Subgroup.inclusion_injective hJE).comp eJ.symm.injective))

theorem false_of_good_triple_A5A5 {D : Type} [Group D] [Finite D] {a b : D}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hcomm : a * b = b * a)
    (ea : Nonempty (↥(centralizer ({a} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (eb : Nonempty (↥(centralizer ({b} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (eab : Nonempty (↥(centralizer ({a * b} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (hE : Nonempty (↥(GorensteinWalter.componentLayerOf (⊤ : Subgroup D)) ≃*
      alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) : False := by
  obtain ⟨e⟩ := hE
  have hEn : (GorensteinWalter.componentLayerOf (⊤ : Subgroup D)).Normal :=
    ⟨fun n hn g => (GorensteinWalter.componentLayerOf_isNormalIn (⊤ : Subgroup D)).2 g
      (mem_top g) n hn⟩
  have h1 := swapHom_ne_one_of_good _ e ha ea
  have h2 := swapHom_ne_one_of_good _ e hb eb
  have h3 := swapHom_ne_one_of_good _ e (orderOf_mul_eq_two ha hb hab hcomm) eab
  apply h3
  rw [map_mul, map_mul]
  have hall : ∀ g k : Multiplicative (ZMod 2), g ≠ 1 → k ≠ 1 → g * k = 1 := by decide
  exact hall _ _ h1 h2

end CFSG.EvenSporadicStandard.HSStd.HFI
