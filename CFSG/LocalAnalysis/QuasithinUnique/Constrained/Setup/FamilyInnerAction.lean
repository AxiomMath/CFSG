module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
public import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.SectionRank

section CentralDiff

variable {X Y : Type*} [Group X] [Group Y]

theorem hom_eq_of_central_diff (hX : Group.IsPerfect X) (f₁ f₂ : X →* Y)
    (h : ∀ x, (f₁ x)⁻¹ * f₂ x ∈ Subgroup.center Y) : f₁ = f₂ := by
  refine MonoidHom.eq_of_eqOn_dense (s := commutatorSet X) ?_ ?_
  · rw [← commutator_eq_closure, hX.commutator_eq_top]
  · rintro _ ⟨x, y, rfl⟩
    rw [map_commutatorElement, map_commutatorElement,
      show f₂ x = f₁ x * ((f₁ x)⁻¹ * f₂ x) by group,
      show f₂ y = f₁ y * ((f₁ y)⁻¹ * f₂ y) by group,
      commutatorElement_mul_mem_center _ _ (h x) (h y)]

end CentralDiff

section NormConj

variable {X : Type*} [Group X] {L : Subgroup X}

@[expose] def normConj {g : X} (hg : g ∈ Subgroup.normalizer (L : Set X)) : MulAut ↥L where
  toFun y := ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg _).1 y.2⟩
  invFun y := ⟨g⁻¹ * y * g, by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) _).1 y.2
    simpa using this⟩
  left_inv y := by apply Subtype.ext; simp [mul_assoc]
  right_inv y := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

theorem normConj_apply {g : X} (hg : g ∈ Subgroup.normalizer (L : Set X)) (y : ↥L) :
    ((normConj hg y : ↥L) : X) = g * y * g⁻¹ := rfl

@[expose] noncomputable def normConjQ {g : X} (hg : g ∈ Subgroup.normalizer (L : Set X)) :
    MulAut (↥L ⧸ Subgroup.center ↥L) :=
  QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) (normConj hg)
    (Subgroup.map_center_eq (normConj hg))

theorem normConjQ_mk {g : X} (hg : g ∈ Subgroup.normalizer (L : Set X)) (y : ↥L) :
    normConjQ hg (QuotientGroup.mk y) = QuotientGroup.mk (normConj hg y) :=
  QuotientGroup.congr_mk' _ _ _ _ y

theorem normConj_mul {g h : X} (hg : g ∈ Subgroup.normalizer (L : Set X))
    (hh : h ∈ Subgroup.normalizer (L : Set X)) :
    normConj (Subgroup.mul_mem _ hg hh) = normConj hg * normConj hh := by
  ext y
  simp [normConj_apply, mul_assoc]

theorem normConj_sq {g : X} (hg : g ∈ Subgroup.normalizer (L : Set X)) (hg2 : g * g = 1) :
    normConj hg * normConj hg = 1 := by
  ext y
  simp only [MulAut.mul_apply, normConj_apply, MulAut.one_apply]
  have : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  rw [this]
  calc g * (g * (y : X) * g) * g = (g * g) * (y : X) * (g * g) := by group
    _ = y := by rw [hg2]; group

theorem normConjQ_mul {g h : X} (hg : g ∈ Subgroup.normalizer (L : Set X))
    (hh : h ∈ Subgroup.normalizer (L : Set X)) :
    normConjQ (Subgroup.mul_mem _ hg hh) = normConjQ hg * normConjQ hh := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [normConjQ_mk, normConj_mul, MulAut.mul_apply, MulAut.mul_apply, normConjQ_mk,
    normConjQ_mk]

theorem normConjQ_sq {g : X} (hg : g ∈ Subgroup.normalizer (L : Set X)) (hg2 : g * g = 1) :
    normConjQ hg * normConjQ hg = 1 := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [MulAut.mul_apply, normConjQ_mk, MulAut.one_apply]
  have := congrArg (fun f : MulAut ↥L => f y) (normConj_sq hg hg2)
  simpa using congrArg QuotientGroup.mk this

end NormConj


section Inner

variable {W : Type} [CommGroup W]

theorem mem_of_inner_action (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (hL : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {b l : MulAut W} (hl : l ∈ L)
    (hb2 : b * b = 1) (hbl : ∀ y ∈ L, b * y * b⁻¹ = l * y * l⁻¹) : b ∈ L := by
  obtain ⟨z, hz⟩ : ∃ z : MulAut W, z = l⁻¹ * b := ⟨_, rfl⟩
  have hzc : ∀ y ∈ L, z * y = y * z := by
    intro y hy
    have h1 : b * y = l * y * l⁻¹ * b := (mul_inv_eq_iff_eq_mul).1 (hbl y hy)
    calc z * y = l⁻¹ * (b * y) := by rw [hz, mul_assoc]
      _ = l⁻¹ * (l * y * l⁻¹ * b) := by rw [h1]
      _ = y * z := by rw [hz]; group
  have hbz : b = l * z := by rw [hz]; group
  have hzl : z * l = l * z := hzc l hl
  have hz2 : z * z = (l * l)⁻¹ := by
    have h1 : l * l * (z * z) = 1 := by
      calc l * l * (z * z) = (l * z) * (l * z) := by
            calc l * l * (z * z) = l * (l * z) * z := by group
              _ = l * (z * l) * z := by rw [hzl]
              _ = (l * z) * (l * z) := by group
        _ = b * b := by rw [← hbz]
        _ = 1 := hb2
    exact eq_inv_of_mul_eq_one_right h1 |>.trans rfl
  have hz2L : z * z ∈ L := by rw [hz2]; exact L.inv_mem (L.mul_mem hl hl)
  have hz2c : (⟨z * z, hz2L⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    show (y : MulAut W) * (z * z) = (z * z) * (y : MulAut W)
    have hy := hzc y y.2
    calc (y : MulAut W) * (z * z) = ((y : MulAut W) * z) * z := by rw [mul_assoc]
      _ = (z * (y : MulAut W)) * z := by rw [← hy]
      _ = z * ((y : MulAut W) * z) := by rw [mul_assoc]
      _ = z * (z * (y : MulAut W)) := by rw [← hy]
      _ = (z * z) * (y : MulAut W) := by rw [mul_assoc]
  set k := Nat.card (Subgroup.center ↥L) with hk
  have hzk2 : (z * z) ^ k = 1 := by
    have h1 : (⟨⟨z * z, hz2L⟩, hz2c⟩ : Subgroup.center ↥L) ^ k = 1 := pow_card_eq_one'
    exact congrArg (fun x : Subgroup.center ↥L => ((x : ↥L) : MulAut W)) h1
  have hzk : z ^ k = 1 := by
    have hsq : z ^ k * z ^ k = 1 := by
      calc z ^ k * z ^ k = z ^ (k + k) := (pow_add z k k).symm
        _ = z ^ (2 * k) := by rw [two_mul]
        _ = (z ^ 2) ^ k := pow_mul z 2 k
        _ = (z * z) ^ k := by rw [pow_two]
        _ = 1 := hzk2
    refine eq_one_of_centralizes_irreducible hW hL (fun y hy => ?_) hsq
    exact (Commute.pow_left (show Commute z y from hzc y hy) k).eq
  have hzL : z ∈ L := by
    obtain ⟨m, hm⟩ := hodd
    have : z = (z * z) ^ (m + 1) := by
      calc z = z ^ (k + 1) := by rw [pow_succ, hzk, one_mul]
        _ = z ^ (2 * (m + 1)) := by rw [hm]; ring_nf
        _ = (z ^ 2) ^ (m + 1) := pow_mul z 2 _
        _ = (z * z) ^ (m + 1) := by rw [pow_two]
    rw [this]
    exact L.pow_mem hz2L _
  rw [hbz]
  exact L.mul_mem hl hzL

end Inner

end CFSG.QuasithinUnique.Setup.Family
