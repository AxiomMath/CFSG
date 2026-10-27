module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTLinkA
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenAct
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrLift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

section Lemmas

variable {A Γ₀ Γ : Type*} [Group A] [Group Γ₀] [Group Γ]

theorem mem_normalizer_subgroupOf {C B : Subgroup A} {h : ↥B}
    (hh : (h : A) ∈ normalizer (C : Set A)) :
    h ∈ normalizer ((C.subgroupOf B : Subgroup ↥B) : Set ↥B) := by
  rw [mem_normalizer_iff]
  intro x
  show (x : A) ∈ C ↔ ((h * x * h⁻¹ : ↥B) : A) ∈ C
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact mem_normalizer_iff.mp hh (x : A)

theorem mem_normalizer_of_map {ι : Γ →* Γ₀} (hι : Function.Injective ι) {γ : Γ}
    {Q : Subgroup Γ} (h : ι γ ∈ normalizer ((Q.map ι : Subgroup Γ₀) : Set Γ₀)) :
    γ ∈ normalizer (Q : Set Γ) := by
  rw [mem_normalizer_iff]
  intro x
  have h1 := mem_normalizer_iff.mp h (ι x)
  have e : ι γ * ι x * (ι γ)⁻¹ = ι (γ * x * γ⁻¹) := by rw [map_mul, map_mul, map_inv]
  rw [e, Subgroup.mem_map_iff_mem hι, Subgroup.mem_map_iff_mem hι] at h1
  exact h1

end Lemmas

variable {G : Type} [Group G] [Finite G] {H P : Subgroup G} {g : G} {Γ : Type} [Group Γ]
  {K : Subgroup Γ} {a : Γ} {P' : Subgroup Γ} {J : Subgroup (HBar H)}

theorem LinkB.exists_equiv (hq : IsQuasisimple ↥K) [K.Normal] (hL : LinkB H P g K a P' J) :
    ∃ e : (↥J ⧸ center ↥J) ≃* (↥K ⧸ center ↥K),
      ∀ (h : ↥H) (hh : QuotientGroup.mk' (pPrimeCore 2 ↥H) h ∈ normalizer (J : Set (HBar H))),
        ∃ γ : Γ, ((h : G) ∈ normalizer (P : Set G) → γ ∈ normalizer (P' : Set Γ)) ∧
          ((h : G) = g → γ = a) ∧
          ∀ y : ↥J ⧸ center ↥J, e (actJ J ⟨_, hh⟩ y) = actYHom (K := K) γ (e y) := by
  obtain ⟨Γ₀, _, _, π, ι, hg, hι, -, -, -, hιN, hιa, hP'ι, hJ, -, Dl, -, -, hDlJ, hDlK,
    hDln⟩ := hL
  set ν : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hν
  set Dh : Subgroup ↥H := Dl.subgroupOf H with hDh
  have hmem₁ : ∀ d : ↥Dh, ν d ∈ J := fun d => hDlJ ▸ Subgroup.mem_map_of_mem ν d.2
  have hmem₂ : ∀ d : ↥Dh, π d ∈ K.map ι := fun d => hDlK ▸ Subgroup.mem_map_of_mem π d.2
  set ψ₁ : ↥Dh →* ↥J := (ν.comp Dh.subtype).codRestrict J hmem₁ with hψ₁
  set eK : ↥K ≃* ↥(K.map ι) := K.equivMapOfInjective ι hι with heK
  set ψ₂ : ↥Dh →* ↥K :=
    eK.symm.toMonoidHom.comp ((π.comp Dh.subtype).codRestrict _ hmem₂) with hψ₂
  have hψ₂ι : ∀ d : ↥Dh, ι (ψ₂ d) = π d := by
    intro d
    have h1 := Subgroup.coe_equivMapOfInjective_apply K ι hι (eK.symm ⟨π d, hmem₂ d⟩)
    rw [← heK, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hψ₁s : Function.Surjective ψ₁ := by
    rintro ⟨j, hj⟩
    have hj' : j ∈ Dh.map ν := by rw [hDlJ]; exact hj
    obtain ⟨d, hd, hdj⟩ := hj'
    exact ⟨⟨d, hd⟩, Subtype.ext hdj⟩
  have hψ₂s : Function.Surjective ψ₂ := by
    intro k
    have hk' : ι k ∈ Dh.map π := by rw [hDlK]; exact Subgroup.mem_map_of_mem ι k.2
    obtain ⟨d, hd, hdk⟩ := hk'
    exact ⟨⟨d, hd⟩, Subtype.ext (hι (by rw [hψ₂ι]; exact hdk))⟩
  set f₁ : ↥Dh →* ↥J ⧸ center ↥J := (QuotientGroup.mk' (center ↥J)).comp ψ₁ with hf₁
  set f₂ : ↥Dh →* ↥K ⧸ center ↥K := (QuotientGroup.mk' (center ↥K)).comp ψ₂ with hf₂
  have hf₁s : Function.Surjective f₁ := (QuotientGroup.mk'_surjective _).comp hψ₁s
  have hf₂s : Function.Surjective f₂ := (QuotientGroup.mk'_surjective _).comp hψ₂s
  have hsol : Group.IsSolvable ↥f₁.ker := by
    have hker₁ : ∀ d : ↥f₁.ker, ψ₁ d ∈ center ↥J := fun d => (QuotientGroup.eq_one_iff _).mp d.2
    let g₁ : ↥f₁.ker →* ↥(center ↥J) := (ψ₁.comp f₁.ker.subtype).codRestrict _ hker₁
    have hO : Group.IsSolvable ↥(pPrimeCore 2 ↥H) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    have hmemO : ∀ x : ↥g₁.ker, (((x : ↥f₁.ker) : ↥Dh) : ↥H) ∈ pPrimeCore 2 ↥H := by
      intro x
      have h1 : g₁ x = 1 := x.2
      have h2 : ν (((x : ↥f₁.ker) : ↥Dh) : ↥H) = 1 :=
        congrArg (fun y : ↥(center ↥J) => ((y : ↥J) : HBar H)) h1
      exact (QuotientGroup.eq_one_iff _).mp h2
    let k₁ : ↥g₁.ker →* ↥(pPrimeCore 2 ↥H) :=
      ((Dh.subtype.comp f₁.ker.subtype).comp g₁.ker.subtype).codRestrict _ hmemO
    have hk₁ : Function.Injective k₁ := by
      intro x y hxy
      have h1 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext h1))
    have : Group.IsSolvable ↥g₁.ker := Group.isSolvable_of_isSolvable_injective hk₁
    have : Group.IsSolvable ↥(center ↥J) :=
      Group.isSolvable_of_comm fun x y => Subtype.ext (Subgroup.mem_center_iff.mp y.2 x)
    exact Group.isSolvable_of_ker_le_range g₁.ker.subtype g₁ (by rw [Subgroup.range_subtype])
  have : IsSimpleGroup (↥J ⧸ center ↥J) := hJ.1.2.1
  have : IsSimpleGroup (↥K ⧸ center ↥K) := hq.2.1
  obtain ⟨e, he⟩ := exists_equiv_of_solvable hq.2.2 hf₁s hf₂s hsol
  refine ⟨e, fun h hh => ?_⟩
  have hhD : h ∈ normalizer (Dh : Set ↥H) := mem_normalizer_subgroupOf (hDln h hh)
  have hπh : π h ∈ normalizer ((K.map ι : Subgroup Γ₀) : Set Γ₀) := by
    rw [← hDlK]
    exact mem_normalizer_map_br π hhD
  obtain ⟨γ, hγ⟩ := hιN (π h) hπh
  refine ⟨γ, fun hP => ?_, fun hhg => ?_, fun y => ?_⟩
  · apply mem_normalizer_of_map hι
    rw [hγ, hP'ι]
    exact mem_normalizer_map_br π (mem_normalizer_subgroupOf hP)
  · apply hι
    rw [hγ, hιa]
    exact congrArg π (Subtype.ext hhg)
  · obtain ⟨d, rfl⟩ := hf₁s y
    let d' : ↥Dh := ⟨h * d * h⁻¹, (mem_normalizer_iff.mp hhD d).mp d.2⟩
    have h1 : actJ J ⟨_, hh⟩ (f₁ d) = f₁ d' := by
      show actJ J ⟨_, hh⟩ (QuotientGroup.mk (ψ₁ d)) = QuotientGroup.mk (ψ₁ d')
      rw [actJ_mk]
      congr 1
    have h2 : f₂ d' = actYHom (K := K) γ (f₂ d) := by
      show QuotientGroup.mk (ψ₂ d') = actYHom (K := K) γ (QuotientGroup.mk (ψ₂ d))
      rw [actYHom_mk]
      congr 1
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      apply hι
      have hd' : ((d' : ↥Dh) : ↥H) = h * d * h⁻¹ := rfl
      rw [hψ₂ι, hd', map_mul, map_mul, map_inv, map_mul ι, map_mul ι, map_inv ι, hγ, hψ₂ι]
    rw [h1, he, he, h2]

theorem actYHom_eq_actJ {A : Type} [Group A] {J : Subgroup A} [J.Normal] (x : A)
    (hx : x ∈ normalizer (J : Set A)) (y : ↥J ⧸ center ↥J) :
    actYHom (K := J) x y = actJ J ⟨x, hx⟩ y := by
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
  rw [actYHom_mk, actJ_mk]
  congr 1

@[expose] def LinkTr {G : Type} [Group G] (H P : Subgroup G) (J : Subgroup (HBar H)) [J.Normal]
    {Γ : Type} [Group Γ] (K : Subgroup Γ) [K.Normal] (P' : Subgroup Γ) : Prop :=
  ∃ e : (↥J ⧸ center ↥J) ≃* (↥K ⧸ center ↥K), ∀ h : ↥H, (h : G) ∈ normalizer (P : Set G) →
    ∃ γ ∈ normalizer (P' : Set Γ), ∀ y : ↥J ⧸ center ↥J,
      e (actYHom (K := J) (QuotientGroup.mk' (pPrimeCore 2 ↥H) h) y) = actYHom (K := K) γ (e y)

theorem linkTr_of {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} (hM : Mod55 p ρ K a P') (hL : LinkB H P g K a P' J)
    [J.Normal] [K.Normal] : LinkTr H P J K P' := by
  obtain ⟨e, he⟩ := hL.exists_equiv hM.quasi
  refine ⟨e, fun h hP => ?_⟩
  have hh : QuotientGroup.mk' (pPrimeCore 2 ↥H) h ∈ normalizer (J : Set (HBar H)) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact mem_top _
  obtain ⟨γ, hγP, -, hγ⟩ := he h hh
  refine ⟨γ, hγP hP, fun y => ?_⟩
  rw [actYHom_eq_actJ _ hh, hγ]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
