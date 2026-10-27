module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Sq

variable {G : Type*} [Group G]

@[expose] def sqHom {A : Subgroup G} (hA : IsElemAbelian 2 A) {f : G}
    (hfA : f ∈ Subgroup.normalizer (A : Set G)) : A →* G where
  toFun a := (a : G) * (f * a * f⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have hX : f * (a : G) * f⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hfA a).mp a.2
    have hcm : (b : G) * (f * a * f⁻¹) = (f * a * f⁻¹) * b := IsElemAbelian.comm hA b.2 hX
    calc ((a * b : A) : G) * (f * ((a * b : A) : G) * f⁻¹)
        = a * (b * (f * a * f⁻¹)) * (f * b * f⁻¹) := by simp only [Subgroup.coe_mul]; group
      _ = (a * (f * a * f⁻¹)) * (b * (f * b * f⁻¹)) := by rw [hcm]; group

theorem sqHom_mem {A : Subgroup G} (hA : IsElemAbelian 2 A) {f : G}
    (hfA : f ∈ Subgroup.normalizer (A : Set G)) (a : A) : sqHom hA hfA a ∈ A := by
  have hX : f * (a : G) * f⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hfA a).mp a.2
  exact A.mul_mem a.2 hX

theorem sqHom_ker {A : Subgroup G} (hA : IsElemAbelian 2 A) {f : G}
    (hfA : f ∈ Subgroup.normalizer (A : Set G)) :
    (sqHom hA hfA).ker = (A ⊓ Subgroup.centralizer ({f} : Set G)).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  have ha2 : (a : G) ^ 2 = 1 := hA.2 a a.2
  have hainv : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha2)
  constructor
  · intro h
    have h' : (a : G) * (f * a * f⁻¹) = 1 := h
    have h1 : f * a * f⁻¹ = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right h'
    rw [hainv] at h1
    refine ⟨a.2, ?_⟩
    calc (a : G) * f = f * a * f⁻¹ * f := by rw [h1]
      _ = f * a := by group
  · rintro ⟨-, h⟩
    have h' : (a : G) * f = f * a := h
    show (a : G) * (f * a * f⁻¹) = 1
    have h1 : f * (a : G) * f⁻¹ = a := by rw [← h']; group
    rw [h1]
    simpa [pow_two] using ha2

theorem sqHom_range_le {A : Subgroup G} (hA : IsElemAbelian 2 A) {f : G}
    (hfA : f ∈ Subgroup.normalizer (A : Set G)) (hf2 : f ^ 2 = 1) :
    (sqHom hA hfA).range ≤ A ⊓ Subgroup.centralizer ({f} : Set G) := by
  rintro _ ⟨a, rfl⟩
  have hX : f * (a : G) * f⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hfA a).mp a.2
  refine ⟨A.mul_mem a.2 hX, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hcm : (a : G) * (f * a * f⁻¹) = (f * a * f⁻¹) * a := IsElemAbelian.comm hA a.2 hX
  have hfX : f * (f * (a : G) * f⁻¹) * f⁻¹ = a := by
    have hff : f * f = 1 := by simpa [pow_two] using hf2
    calc f * (f * (a : G) * f⁻¹) * f⁻¹ = (f * f) * a * (f * f)⁻¹ := by group
      _ = a := by rw [hff]; simp
  have hθ : f * ((a : G) * (f * a * f⁻¹)) * f⁻¹ = (a : G) * (f * a * f⁻¹) := by
    calc f * ((a : G) * (f * a * f⁻¹)) * f⁻¹
        = (f * a * f⁻¹) * (f * (f * a * f⁻¹) * f⁻¹) := by group
      _ = (f * a * f⁻¹) * a := by rw [hfX]
      _ = (a : G) * (f * a * f⁻¹) := hcm.symm
  show (a : G) * (f * a * f⁻¹) * f = f * ((a : G) * (f * a * f⁻¹))
  calc (a : G) * (f * a * f⁻¹) * f = (f * ((a : G) * (f * a * f⁻¹)) * f⁻¹) * f := by rw [hθ]
    _ = f * ((a : G) * (f * a * f⁻¹)) := by group

theorem exists_sq_card_inf_centralizer_sq [Finite G] {Z : Subgroup G} (hZ : IsElemAbelian 2 Z)
    {f : G} (hf : f ∈ Subgroup.normalizer (Z : Set G)) (hf4 : f ^ 4 = 1)
    (hcard : Nat.card Z = Nat.card (Z ⊓ Subgroup.centralizer ({f ^ 2} : Set G) : Subgroup G) ^ 2) :
    ∃ d : ℕ, Nat.card (Z ⊓ Subgroup.centralizer ({f ^ 2} : Set G) : Subgroup G) = d ^ 2 := by
  have hf₀ : f ^ 2 ∈ Subgroup.normalizer (Z : Set G) := Subgroup.pow_mem _ hf 2
  have hf₀2 : (f ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hf4
  set C₀ : Subgroup G := Z ⊓ Subgroup.centralizer ({f ^ 2} : Set G) with hC₀
  set θ := sqHom hZ hf with hθ
  set θ₀ := sqHom hZ hf₀ with hθ₀
  have hθmem : ∀ a : Z, θ a ∈ Z := sqHom_mem hZ hf
  have hθθ : ∀ a : Z, θ ⟨θ a, hθmem a⟩ = θ₀ a := by
    intro a
    have hb : f * (a : G) * f⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hf a).mp a.2
    have hbb : (f * (a : G) * f⁻¹) * (f * (a : G) * f⁻¹) = 1 := by
      have := hZ.2 _ hb
      simpa [pow_two] using this
    have hc : f ^ 2 * (a : G) * (f ^ 2)⁻¹ = f * (f * a * f⁻¹) * f⁻¹ := by
      rw [pow_two, mul_inv_rev]; group
    show ((a : G) * (f * a * f⁻¹)) * (f * ((a : G) * (f * a * f⁻¹)) * f⁻¹) =
      (a : G) * (f ^ 2 * a * (f ^ 2)⁻¹)
    rw [hc]
    calc ((a : G) * (f * a * f⁻¹)) * (f * ((a : G) * (f * a * f⁻¹)) * f⁻¹)
        = (a : G) * ((f * a * f⁻¹) * (f * a * f⁻¹)) * (f * (f * a * f⁻¹) * f⁻¹) := by group
      _ = (a : G) * (f * (f * a * f⁻¹) * f⁻¹) := by rw [hbb]; group
  have hker₀ : Nat.card θ₀.ker = Nat.card C₀ := by
    rw [hθ₀, sqHom_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hker : Nat.card θ.ker =
      Nat.card (Z ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) := by
    rw [hθ, sqHom_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hpos : 0 < Nat.card C₀ := Nat.card_pos
  have hrcard₀ : Nat.card θ₀.range = Nat.card C₀ := by
    have h := Subgroup.card_ker_mul_card_range θ₀
    rw [hker₀, hcard, pow_two] at h
    exact Nat.eq_of_mul_eq_mul_left hpos h
  have hrange₀ : θ₀.range = C₀ :=
    Subgroup.eq_of_le_of_card_ge (sqHom_range_le hZ hf₀ hf₀2) (le_of_eq hrcard₀.symm)
  have hker_le : ∀ a : Z, θ a = 1 → (a : G) ∈ θ.range := by
    intro a ha
    have haK : (a : G) ∈ Z ⊓ Subgroup.centralizer ({f} : Set G) := by
      have h : a ∈ θ.ker := ha
      rw [hθ, sqHom_ker] at h
      exact h
    have haC₀ : (a : G) ∈ C₀ := by
      refine ⟨haK.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : (a : G) * f = f * a := Subgroup.mem_centralizer_singleton_iff.mp haK.2
      calc (a : G) * f ^ 2 = (a * f) * f := by rw [pow_two, mul_assoc]
        _ = (f * a) * f := by rw [h1]
        _ = f * (a * f) := by rw [mul_assoc]
        _ = f * (f * a) := by rw [h1]
        _ = f ^ 2 * a := by rw [pow_two, mul_assoc]
    rw [← hrange₀] at haC₀
    obtain ⟨b, hb⟩ := haC₀
    exact ⟨⟨θ b, hθmem b⟩, by rw [hθθ b]; exact hb⟩
  have hImZ : θ.range ≤ Z := by
    rintro _ ⟨a, rfl⟩
    exact hθmem a
  let W : Subgroup Z := θ.range.subgroupOf Z
  have hkerW : θ.ker ≤ W := fun a ha => hker_le a ha
  have hmapW : W.map θ = θ₀.range := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.mp hw
      refine ⟨a, ?_⟩
      rw [← hθθ a]
      congr 1
      exact Subtype.ext ha
    · rintro ⟨a, rfl⟩
      exact ⟨⟨θ a, hθmem a⟩, Subgroup.mem_subgroupOf.mpr ⟨a, rfl⟩, hθθ a⟩
  have h2 := Subgroup.card_ker_mul_card_range (θ.domRestrict W)
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, hmapW, hrcard₀] at h2
  have e1 : Nat.card (θ.ker.subgroupOf W) = Nat.card θ.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerW).toEquiv
  have e2 : Nat.card W = Nat.card θ.range :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hImZ).toEquiv
  rw [e1, e2] at h2
  have h1 := Subgroup.card_ker_mul_card_range θ
  rw [hcard, pow_two] at h1
  refine ⟨Nat.card θ.ker, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left hpos
  have h3 : Nat.card θ.ker * (Nat.card θ.ker * Nat.card C₀) = Nat.card C₀ * Nat.card C₀ := by
    rw [h2]; exact h1
  calc Nat.card C₀ * Nat.card C₀ = Nat.card θ.ker * (Nat.card θ.ker * Nat.card C₀) := h3.symm
    _ = Nat.card C₀ * Nat.card θ.ker ^ 2 := by ring

end Sq

end CFSG.QuasithinUnique.Lin2
