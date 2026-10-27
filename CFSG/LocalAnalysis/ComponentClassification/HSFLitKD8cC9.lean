module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cCharB
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cMod

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

omit [Finite X] in
theorem mem_normalizer_of_conj {H : Subgroup X} {g : X} (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ normalizer (H : Set X) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

namespace Conf

variable (K : Conf S T₁)

theorem Zx_sq {z : X} (hz : z ∈ K.Zx) : z * z = 1 := by
  obtain ⟨a, ha, rfl⟩ := hz
  rw [← map_mul, Zl_sq a (inZ_zl ha), map_one]

theorem card_le_two_mul_of_normalizes {C₁ : Subgroup X} (hC : IsPGroup 2 C₁)
    (hN : C₁ ≤ normalizer (K.Zx : Set X)) :
    Nat.card C₁ ≤ 2 * Nat.card (C₁ ⊓ centralizer (K.Zx : Set X) : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let α := {y : X // y ∈ K.Zx ∧ y ≠ 1}
  have hα : Nat.card α = 3 := by
    have h4 := K.card_Zx
    have : Nat.card α = ((K.Zx : Set X) \ {1}).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_congr
        { toFun := fun y => ⟨y.1, y.2.1, y.2.2⟩
          invFun := fun y => ⟨y.1, y.2.1, y.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [this, Set.ncard_sdiff_singleton_of_mem (one_mem K.Zx), ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, h4]
  have hconj : ∀ (a : C₁) (y : α), (a : X) * y.1 * (a : X)⁻¹ ∈ K.Zx ∧
      (a : X) * y.1 * (a : X)⁻¹ ≠ 1 := fun a y =>
    ⟨(mem_normalizer_iff.mp (hN a.2) y.1).mp y.2.1, fun h => y.2.2 (by
      have := congrArg (fun x => (a : X)⁻¹ * x * a) h
      simpa [mul_assoc] using this)⟩
  let act : MulAction C₁ α :=
    { smul := fun a y => ⟨(a : X) * y.1 * (a : X)⁻¹, hconj a y⟩
      one_smul := fun y => Subtype.ext (by
        show ((1 : C₁) : X) * y.1 * ((1 : C₁) : X)⁻¹ = y.1
        simp)
      mul_smul := fun a b y => Subtype.ext (by
        show (a : X) * b * y.1 * ((a : X) * b)⁻¹ = a * (b * y.1 * (b : X)⁻¹) * (a : X)⁻¹
        group) }
  let φ := MulAction.toPermHom C₁ α
  have hcard : Nat.card C₁ = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hrange : Nat.card φ.range ≤ 2 := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp
      (hC.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)
    have hdvd : Nat.card φ.range ∣ 6 := by
      have := Subgroup.card_subgroup_dvd_card φ.range
      rwa [Nat.card_perm, hα] at this
    rw [hm] at hdvd ⊢
    rcases m with _ | _ | m
    · norm_num
    · norm_num
    · exfalso
      have h4 : 4 ∣ 6 := (pow_dvd_pow 2 (by omega : 2 ≤ m + 2)).trans hdvd
      omega
  have hker : Nat.card φ.ker ≤ Nat.card (C₁ ⊓ centralizer (K.Zx : Set X) : Subgroup X) := by
    refine Nat.card_le_card_of_injective (fun a => ⟨(a.1 : X), a.1.2,
      mem_centralizer_iff.mpr fun y hy => ?_⟩) ?_
    · by_cases hy1 : y = 1
      · rw [hy1]; group
      · have h := congrArg (fun p : Equiv.Perm α => (p ⟨y, hy, hy1⟩).1) a.2
        simp only [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply] at h
        change (a.1 : X) * y * (a.1 : X)⁻¹ = y at h
        calc y * (a.1 : X) = (a.1 : X) * y * (a.1 : X)⁻¹ * a.1 := by rw [h]
          _ = a.1 * y := by group
    · intro a b hab
      have := congrArg Subtype.val hab
      simp only at this
      exact Subtype.ext (Subtype.ext this)
  rw [hcard]
  exact Nat.mul_le_mul hrange hker

namespace T2

namespace Lift

variable {K} {T : K.T2} (W : T.Lift)

include W in
theorem card_le_of_centralizer {A₀ : Subgroup X} (hA : T.P ≤ normalizer (A₀ : Set X))
    {P : Subgroup X} (hP : IsPGroup 2 P) (hPC : P ≤ centralizer (A₀ : Set X)) :
    Nat.card P ≤ Nat.card (T.P ⊓ centralizer (A₀ : Set X) : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (A₀ : Set X) with hNdef
  have hPN : P ≤ N := hPC.trans (centralizer_le_normalizer _)
  let Ts : Sylow 2 N :=
    { toSubgroup := T.P.subgroupOf N
      isPGroup' := T.isPGroup.comap_of_injective _ (subtype_injective _)
      is_maximal' := fun {Q} hQ hle => by
        have h := W.maximal_X (Q := Q.map N.subtype) (hQ.map _)
          (fun x hx => ⟨⟨x, hA hx⟩, hle hx, rfl⟩)
        rw [← h]
        exact (comap_map_eq_self_of_injective (subtype_injective _) Q).symm }
  have hP' : IsPGroup 2 (P.subgroupOf N) := hP.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N Q Ts
  refine Nat.card_le_card_of_injective (fun y : P =>
    (⟨(g : X) * y * (g : X)⁻¹, ?_, ?_⟩ : (T.P ⊓ centralizer (A₀ : Set X) : Subgroup X))) ?_
  · have hy : (⟨(y : X), hPN y.2⟩ : N) ∈ (Q : Subgroup N) := hQ y.2
    have : g * ⟨(y : X), hPN y.2⟩ * g⁻¹ ∈ (Ts : Subgroup N) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact ⟨_, hy, rfl⟩
    exact this
  · show (g : X) * y * (g : X)⁻¹ ∈ centralizer (A₀ : Set X)
    rw [mem_centralizer_iff]
    intro a ha
    have hga : (g : X)⁻¹ * a * g ∈ A₀ := by
      have := (mem_normalizer_iff.mp (inv_mem g.2) a).mp ha
      rwa [inv_inv] at this
    have hc := mem_centralizer_iff.mp (hPC y.2) _ hga
    calc a * ((g : X) * y * (g : X)⁻¹) = g * ((g : X)⁻¹ * a * g * y) * (g : X)⁻¹ := by group
      _ = g * (y * ((g : X)⁻¹ * a * g)) * (g : X)⁻¹ := by rw [hc]
      _ = (g : X) * y * (g : X)⁻¹ * a := by group
  · intro a b hab
    have := congrArg (fun y : (T.P ⊓ centralizer (A₀ : Set X) : Subgroup X) =>
      (g : X)⁻¹ * (y : X) * g) hab
    simp only at this
    exact Subtype.ext (by simpa [mul_assoc] using this)

omit W in
theorem mem_normalizer_closure {R : X} (hnorm : ∀ g ∈ T.P, R⁻¹ * (g * R * g⁻¹) ∈ K.Zx)
    {g : X} (hg : g ∈ T.P) : g ∈ normalizer (closure (insert R (K.Zx : Set X)) : Set X) := by
  have key : ∀ g ∈ T.P, ∀ x ∈ closure (insert R (K.Zx : Set X)),
      g * x * g⁻¹ ∈ closure (insert R (K.Zx : Set X)) := by
    intro g hg x hx
    have hle : closure (insert R (K.Zx : Set X)) ≤
        (closure (insert R (K.Zx : Set X))).comap (MulAut.conj g).toMonoidHom := by
      rw [closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, SetLike.mem_coe] at hy
      simp only [coe_comap, MulEquiv.coe_toMonoidHom, Set.mem_preimage, MulAut.conj_apply,
        SetLike.mem_coe]
      rcases hy with rfl | hy
      · rw [show g * y * g⁻¹ = y * (y⁻¹ * (g * y * g⁻¹)) by group]
        exact mul_mem (subset_closure (Set.mem_insert _ _))
          (subset_closure (Set.mem_insert_of_mem _ (hnorm g hg)))
      · exact subset_closure (Set.mem_insert_of_mem _ (T.conj_Zx hg hy))
    exact hle hx
  refine mem_normalizer_of_conj (key g hg) fun x hx => ?_
  have := key g⁻¹ (inv_mem hg) x hx
  rwa [inv_inv] at this

include W in
theorem not_conj_of_large {R : X} (hR : R ∈ T.P)
    (hRc : Nat.card (T.P ⊓ centralizer ({R} : Set X) : Subgroup X) = 128)
    (hnorm : ∀ g ∈ T.P, R⁻¹ * (g * R * g⁻¹) ∈ K.Zx)
    (hcA : Nat.card (T.P ⊓ centralizer (insert R (K.Zx : Set X)) : Subgroup X) = 64)
    (hsq : ∀ x ∈ T.P ⊓ centralizer ({R} : Set X), x * x * (x * x) = 1 → x * x ∈ K.Zx)
    (hwit : ∀ z ∈ K.Zx, ∃ x ∈ T.P ⊓ centralizer ({R} : Set X), x * x = z)
    {g : X} (hgc : 128 < Nat.card (T.P ⊓ centralizer ({g} : Set X) : Subgroup X))
    {x : X} (hx : x * R * x⁻¹ = g) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := centralizer ({R} : Set X) with hNdef
  set CR := T.P ⊓ centralizer ({R} : Set X) with hCR
  have hCRN : CR ≤ N := inf_le_right
  have hCRp : IsPGroup 2 CR := T.isPGroup.to_le inf_le_left
  set P₁ := (T.P ⊓ centralizer ({g} : Set X)).map (MulAut.conj x⁻¹).toMonoidHom with hP₁
  have hP₁N : P₁ ≤ N := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hyg := mem_centralizer_singleton_iff.mp hy.2
    rw [← hx] at hyg
    calc x⁻¹ * y * x * R = x⁻¹ * (y * (x * R * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * R * x⁻¹) * y) * x := by rw [hyg]
      _ = R * (x⁻¹ * y * x) := by group
  have hP₁p : IsPGroup 2 P₁ := (T.isPGroup.to_le inf_le_left).map _
  have hP₁c : Nat.card P₁ = Nat.card (T.P ⊓ centralizer ({g} : Set X) : Subgroup X) :=
    card_map_of_injective (MulAut.conj x⁻¹).injective
  obtain ⟨Sy, hSy⟩ := (hCRp.comap_of_injective N.subtype (subtype_injective _) :
    IsPGroup 2 (CR.subgroupOf N)).exists_le_sylow
  obtain ⟨Sy', hSy'⟩ := (hP₁p.comap_of_injective N.subtype (subtype_injective _) :
    IsPGroup 2 (P₁.subgroupOf N)).exists_le_sylow
  have hSycard : Nat.card Sy = Nat.card Sy' := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  set SyX := (Sy : Subgroup N).map N.subtype with hSyX
  have hSyXc : Nat.card SyX = Nat.card Sy := card_map_of_injective (subtype_injective _)
  have hP₁le : Nat.card P₁ ≤ Nat.card SyX := by
    rw [hSyXc, hSycard]
    have h1 : Nat.card (P₁.subgroupOf N) = Nat.card P₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₁N).toEquiv
    rw [← h1]
    exact Subgroup.card_le_of_le hSy'
  have hCRSy : CR ≤ SyX := fun y hy => ⟨⟨y, hCRN hy⟩, hSy hy, rfl⟩
  have hSyXN : SyX ≤ N := map_subtype_le _
  have hSyXp : IsPGroup 2 SyX := Sy.isPGroup'.map _
  obtain ⟨c, hcSy, hcN, hcC⟩ : ∃ c ∈ SyX, c ∈ normalizer (CR : Set X) ∧ c ∉ CR := by
    set I := CR.subgroupOf SyX with hI
    have hIne : I ≠ ⊤ := by
      intro htop
      have hle : SyX ≤ CR := fun y hy => by
        have : (⟨y, hy⟩ : SyX) ∈ I := by rw [htop]; trivial
        exact this
      have := Subgroup.card_le_of_le hle
      omega
    have hnil : Group.IsNilpotent SyX := hSyXp.isNilpotent
    have hlt : I < normalizer (I : Set SyX) :=
      Group.normalizerCondition_of_isNilpotent I (lt_of_le_of_ne le_top hIne)
    obtain ⟨y, hyN, hyI⟩ := IsConcreteLE.exists_of_lt hlt
    refine ⟨y, y.2, ?_, fun h => hyI h⟩
    have hysub : y ∈ (normalizer (CR : Set X)).subgroupOf SyX := by
      rw [subgroupOf_normalizer_eq hCRSy]
      exact hyN
    exact mem_subgroupOf.mp hysub
  have hcR : c ∈ N := hSyXN hcSy
  have hcZ : ∀ z ∈ K.Zx, c * z * c⁻¹ ∈ K.Zx := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hwit z hz
    have hy' : c * y * c⁻¹ ∈ CR := (mem_normalizer_iff.mp hcN y).mp hy
    have h4 : c * y * c⁻¹ * (c * y * c⁻¹) * (c * y * c⁻¹ * (c * y * c⁻¹)) = 1 := by
      rw [show c * y * c⁻¹ * (c * y * c⁻¹) * (c * y * c⁻¹ * (c * y * c⁻¹)) =
        c * (y * y * (y * y)) * c⁻¹ by group, hyz, K.Zx_sq hz]
      group
    have := hsq _ hy' h4
    rwa [show c * y * c⁻¹ * (c * y * c⁻¹) = c * (y * y) * c⁻¹ by group, hyz] at this
  have hcNZ : c ∈ normalizer (K.Zx : Set X) := by
    refine Sec7.mem_normalizer_of_map_eq (eq_of_le_of_card_ge ?_ ?_)
    · rintro _ ⟨z, hz, rfl⟩
      exact hcZ z hz
    · rw [card_map_of_injective (MulAut.conj c).injective]
  set C₁ := CR ⊔ zpowers c with hC₁
  have hC₁Sy : C₁ ≤ SyX := sup_le hCRSy (zpowers_le.mpr hcSy)
  have hC₁p : IsPGroup 2 C₁ := hSyXp.to_le hC₁Sy
  have hC₁N : C₁ ≤ N := hC₁Sy.trans hSyXN
  have hC₁Z : C₁ ≤ normalizer (K.Zx : Set X) := by
    refine sup_le (fun y hy => ?_) (zpowers_le.mpr hcNZ)
    exact mem_normalizer_of_conj (fun z hz => T.conj_Zx hy.1 hz) fun z hz => by
      have := T.conj_Zx (inv_mem hy.1) hz
      rwa [inv_inv] at this
  have hC₁c : 256 ≤ Nat.card C₁ := by
    have hdvd : 128 ∣ Nat.card C₁ := hRc ▸ Subgroup.card_dvd_of_le le_sup_left
    have hne : Nat.card C₁ ≠ 128 := by
      intro h
      have := eq_of_le_of_card_ge (le_sup_left : CR ≤ C₁) (by rw [h, hRc])
      exact hcC (this ▸ mem_sup_right (mem_zpowers c))
    obtain ⟨m, hm⟩ := hdvd
    have hpos : 0 < Nat.card C₁ := Nat.card_pos
    rcases m with _ | _ | m
    · omega
    · omega
    · omega
  have h2 := K.card_le_two_mul_of_normalizes hC₁p hC₁Z
  have hK₁ : Nat.card (C₁ ⊓ centralizer (K.Zx : Set X) : Subgroup X) ≤ 64 := by
    have hcl : centralizer ((closure (insert R (K.Zx : Set X)) : Subgroup X) : Set X) =
        centralizer (insert R (K.Zx : Set X)) := centralizer_closure _
    have hle := W.card_le_of_centralizer (A₀ := closure (insert R (K.Zx : Set X)))
      (P := C₁ ⊓ centralizer (K.Zx : Set X))
      (fun y hy => mem_normalizer_closure (T := T) hnorm hy) (hC₁p.to_le inf_le_left) (by
        rw [hcl]
        intro y hy
        rw [mem_centralizer_iff]
        intro a ha
        simp only [Set.mem_insert_iff, SetLike.mem_coe] at ha
        rcases ha with rfl | ha
        · exact (mem_centralizer_singleton_iff.mp (hC₁N hy.1)).symm
        · exact (mem_centralizer_iff.mp hy.2 a ha))
    rw [hcl, hcA] at hle
    exact hle
  omega

include W in
theorem not_conjTo_of_C9 {R : X} (hR : R ∈ T.P) (hR2 : R * R = 1) (hR1 : R ≠ 1)
    (hRc : Nat.card (T.P ⊓ centralizer ({R} : Set X) : Subgroup X) = 128)
    (hnorm : ∀ g ∈ T.P, R⁻¹ * (g * R * g⁻¹) ∈ K.Zx)
    (hcA : Nat.card (T.P ⊓ centralizer (insert R (K.Zx : Set X)) : Subgroup X) = 64)
    (hsq : ∀ x ∈ T.P ⊓ centralizer ({R} : Set X), x * x * (x * x) = 1 → x * x ∈ K.Zx)
    (hwit : ∀ z ∈ K.Zx, ∃ x ∈ T.P ⊓ centralizer ({R} : Set X), x * x = z)
    (hu64 : 64 ≤ Nat.card (T.P ⊓ centralizer ({W.ψ W.uh} : Set X) : Subgroup X))
    (hU : ∀ g ∈ T.P ⊓ centralizer ({W.ψ W.uh} : Set X), g * g = 1 → g ≠ 1 →
      16 < Nat.card ((T.P ⊓ centralizer ({W.ψ W.uh} : Set X)) ⊓ centralizer ({g} : Set X) :
        Subgroup X) →
      128 < Nat.card (T.P ⊓ centralizer ({g} : Set X) : Subgroup X) ∨ ConjTo t g)
    {h : X} (hh64 : 64 ≤ Nat.card (T.P ⊓ centralizer ({h} : Set X) : Subgroup X))
    {c : X} (hc : c ∈ T.P) (hR'h : c * R * c⁻¹ ∈ centralizer ({h} : Set X))
    (h16 : 16 < Nat.card ((T.P ⊓ centralizer ({h} : Set X)) ⊓
      centralizer ({c * R * c⁻¹} : Set X) : Subgroup X)) :
    ¬ ConjTo t h := by
  intro hconj
  set U := W.ψ W.uh with hU'
  obtain ⟨c₁, hc₁, hP₁⟩ := exists_conj_eq_T C hconj (P := T.P ⊓ centralizer ({h} : Set X))
    (T.isPGroup.to_le inf_le_left) inf_le_right hh64
  obtain ⟨c₂, hc₂, hP₂⟩ := exists_conj_eq_T C W.conjTo_u
    (P := T.P ⊓ centralizer ({U} : Set X)) (T.isPGroup.to_le inf_le_left) inf_le_right hu64
  set γ := c₂⁻¹ * c₁ with hγ
  have hγP : ∀ y ∈ T.P ⊓ centralizer ({h} : Set X),
      γ * y * γ⁻¹ ∈ T.P ⊓ centralizer ({U} : Set X) := by
    intro y hy
    have h1 : c₁ * y * c₁⁻¹ ∈ A.T := hP₁ ▸ ⟨y, hy, rfl⟩
    rw [← hP₂] at h1
    obtain ⟨p, hp, hpy⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hpy
    rw [show γ * y * γ⁻¹ = c₂⁻¹ * (c₁ * y * c₁⁻¹) * c₂ by rw [hγ]; group, ← hpy]
    rw [show c₂⁻¹ * (c₂ * p * c₂⁻¹) * c₂ = p by group]
    exact hp
  have hγh : γ * h * γ⁻¹ = U := by
    rw [hγ, show c₂⁻¹ * c₁ * h * (c₂⁻¹ * c₁)⁻¹ = c₂⁻¹ * (c₁ * h * c₁⁻¹) * c₂ by group, hc₁,
      ← hc₂]
    rw [hU']
    group
  set R' := c * R * c⁻¹ with hR'
  have hR'P : R' ∈ T.P ⊓ centralizer ({h} : Set X) :=
    Subgroup.mem_inf.mpr ⟨T.P.mul_mem (T.P.mul_mem hc hR) (T.P.inv_mem hc), hR'h⟩
  set G := γ * R' * γ⁻¹ with hG
  have hGP := hγP R' hR'P
  have hG2 : G * G = 1 := by
    rw [hG, hR', show γ * (c * R * c⁻¹) * γ⁻¹ * (γ * (c * R * c⁻¹) * γ⁻¹) =
      γ * c * (R * R) * (γ * c)⁻¹ by group, hR2]
    group
  have hG1 : G ≠ 1 := by
    intro h1
    apply hR1
    have := congrArg (fun y => (γ * c)⁻¹ * y * (γ * c)) h1
    simp only [hG, hR'] at this
    rw [show (γ * c)⁻¹ * (γ * (c * R * c⁻¹) * γ⁻¹) * (γ * c) = R by group] at this
    rw [this]
    group
  have hcard : 16 < Nat.card ((T.P ⊓ centralizer ({U} : Set X)) ⊓
      centralizer ({G} : Set X) : Subgroup X) := by
    refine lt_of_lt_of_le h16 (Nat.card_le_card_of_injective (fun y =>
      ⟨γ * y * γ⁻¹, hγP y y.2.1, mem_centralizer_singleton_iff.mpr ?_⟩) ?_)
    · have hy := mem_centralizer_singleton_iff.mp y.2.2
      rw [hG]
      calc γ * y * γ⁻¹ * (γ * R' * γ⁻¹) = γ * (y * R') * γ⁻¹ := by group
        _ = γ * (R' * y) * γ⁻¹ := by rw [hy]
        _ = γ * R' * γ⁻¹ * (γ * y * γ⁻¹) := by group
    · intro a b hab
      have := congrArg Subtype.val hab
      simp only at this
      exact Subtype.ext (by simpa [mul_assoc] using this)
  have hRG : (γ * c) * R * (γ * c)⁻¹ = G := by rw [hG, hR']; group
  rcases hU G hGP hG2 hG1 hcard with hbig | htG
  · exact W.not_conj_of_large hR hRc hnorm hcA hsq hwit hbig hRG
  · have hRt : ConjTo t R := by
      have := (conjTo_conj_iff (γ * c) R).mp (hRG ▸ htG)
      exact this
    exact not_conjTo_of_card_gt C (P := T.P ⊓ centralizer ({R} : Set X))
      (T.isPGroup.to_le inf_le_left) inf_le_right (by rw [hRc]; norm_num) hRt

end Lift

end T2

end Conf

end KD8c

end CFSG.ComponentClassification.HSFLit
