module

public import CFSG.CGT.Foote82.T66.Steps
public import CFSG.CGT.Foote82.T66.Cited
public import CFSG.CGT.Foote82.T66.Overgroup
public import CFSG.CGT.PushingUpLit.CGT6.Nine7Main
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidPlusFacts
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusFacts

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11
open scoped commutatorElement Pointwise

section GroupTheory

variable {Γ : Type*} [Group Γ]

private theorem isComponentOf_map_conj {L X : Subgroup Γ} (hL : IsComponentOf L X) (k : Γ) :
    IsComponentOf (L.map (MulAut.conj k).toMonoidHom) (X.map (MulAut.conj k).toMonoidHom) :=
  ⟨Subgroup.map_mono hL.1, hL.2.1.map _,
    CFSG.Open.IsQuasisimple.of_mulEquiv
      (L.equivMapOfInjective _ (MulAut.conj k).injective).symm hL.2.2⟩

private theorem map_conj_eq_of_mem_centralizer {L : Subgroup Γ} {k : Γ}
    (hk : k ∈ Subgroup.centralizer (L : Set Γ)) : L.map (MulAut.conj k).toMonoidHom = L := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [(Subgroup.mem_centralizer_iff.mp hk y hy).symm, mul_inv_cancel_right]
    exact hy
  · intro hx
    exact ⟨x, hx, by rw [(Subgroup.mem_centralizer_iff.mp hk x hx).symm, mul_inv_cancel_right]⟩

private theorem map_conj_inf_centralizer {G : Subgroup Γ} {k : Γ} (hk : k ∈ G) (t : Γ) :
    (G ⊓ Subgroup.centralizer ({t} : Set Γ)).map (MulAut.conj k).toMonoidHom =
      G ⊓ Subgroup.centralizer ({k * t * k⁻¹} : Set Γ) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, ⟨hyG, hyt⟩, rfl⟩
    refine ⟨G.mul_mem (G.mul_mem hk hyG) (G.inv_mem hk), ?_⟩
    calc k * y * k⁻¹ * (k * t * k⁻¹) = k * (y * t) * k⁻¹ := by group
      _ = k * (t * y) * k⁻¹ := by rw [hyt]
      _ = k * t * k⁻¹ * (k * y * k⁻¹) := by group
  · rintro ⟨hxG, hxt⟩
    refine ⟨k⁻¹ * x * k, ⟨G.mul_mem (G.mul_mem (G.inv_mem hk) hxG) hk, ?_⟩, by group⟩
    calc k⁻¹ * x * k * t = k⁻¹ * (x * (k * t * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * t * k⁻¹) * x) * k := by rw [hxt]
      _ = t * (k⁻¹ * x * k) := by group

private theorem centralizer_zpowers_eq (s : Γ) :
    Subgroup.centralizer ((Subgroup.zpowers s : Subgroup Γ) : Set Γ) =
      Subgroup.centralizer ({s} : Set Γ) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

private theorem isPGroup_zpowers_of_orderOf {s : Γ} (hs : orderOf s = 2) :
    IsPGroup 2 (Subgroup.zpowers s) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])

private theorem inf_centralizer_singleton_subgroupOf {G : Subgroup Γ} (a : ↥G) :
    (G ⊓ Subgroup.centralizer ({(a : Γ)} : Set Γ)).subgroupOf G =
      Subgroup.centralizer ({a} : Set ↥G) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, hx⟩
    exact Subtype.ext hx
  · intro hx
    exact ⟨x.2, congrArg Subtype.val hx⟩

private theorem map_subtype_map_conj {G : Subgroup Γ} (A : Subgroup ↥G) (g : ↥G) :
    (A.map (MulAut.conj g).toMonoidHom).map G.subtype =
      (A.map G.subtype).map (MulAut.conj (g : Γ)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem map_conj_eq_self_of_mem_normalizer {L : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (L : Set Γ)) : L.map (MulAut.conj g).toMonoidHom = L := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr ?_, by group⟩
    rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
    exact hx

private theorem mem_normalizer_of_map_conj_eq {L : Subgroup Γ} {g : Γ}
    (h : L.map (MulAut.conj g).toMonoidHom = L) : g ∈ Subgroup.normalizer (L : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at hyx
    rwa [← hyx]

private theorem mem_normalizer_inf_centralizer {Γ : Type} [Group Γ] {G L : Subgroup Γ} {g : Γ}
    (hgG : g ∈ G) (hgN : g ∈ Subgroup.normalizer (L : Set Γ)) :
    g ∈ Subgroup.normalizer
      ((G ⊓ Subgroup.centralizer (L : Set Γ) : Subgroup Γ) : Set Γ) := by
  apply CFSG.CGT.PushingUpLit.CGT6.Nine7.mem_normalizer_of_conjugate_eq
  have hinf : CFSG.conjugate (G ⊓ Subgroup.centralizer (L : Set Γ)) g =
      CFSG.conjugate G g ⊓ CFSG.conjugate (Subgroup.centralizer (L : Set Γ)) g :=
    Subgroup.map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective
  rw [hinf, CFSG.CGT.PushingUpLit.CGT6.Nine7.conjugate_centralizer,
    CFSG.CGT.PushingUpLit.CGT6.Nine7.conjugate_eq_of_mem_normalizer hgN,
    CFSG.CGT.PushingUpLit.CGT6.Nine7.conjugate_eq_of_mem_normalizer (Subgroup.le_normalizer hgG)]

private theorem le_of_perfect_of_le_sup {A B J : Subgroup Γ} [hBn : B.Normal] (hJ : ⁅J, J⁆ = J)
    (hle : J ≤ A ⊔ B) (hAB : A ≤ Subgroup.centralizer (B : Set Γ))
    (hJA : J ≤ Subgroup.centralizer (A : Set Γ)) : J ≤ B := by
  rw [← hJ, Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hle hx)
  obtain ⟨a', ha', b', hb', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hle hy)
  have hbA : b ∈ Subgroup.centralizer (A : Set Γ) := (Subgroup.le_centralizer_iff.mp hAB) hb
  have haA : a ∈ Subgroup.centralizer (A : Set Γ) := by
    have := (Subgroup.centralizer (A : Set Γ)).mul_mem (hJA hx)
      ((Subgroup.centralizer (A : Set Γ)).inv_mem hbA)
    rwa [mul_inv_cancel_right] at this
  have h1 : a' * a = a * a' := Subgroup.mem_centralizer_iff.mp haA a' ha'
  have h2 : b' * a = a * b' := Subgroup.mem_centralizer_iff.mp (hAB ha) b' hb'
  have hay : a * (a' * b') = (a' * b') * a := by
    calc a * (a' * b') = (a * a') * b' := by group
      _ = (a' * a) * b' := by rw [h1]
      _ = a' * (a * b') := by group
      _ = a' * (b' * a) := by rw [h2]
      _ = (a' * b') * a := by group
  have hinv : a⁻¹ * (a' * b')⁻¹ = (a' * b')⁻¹ * a⁻¹ := by
    rw [← mul_inv_rev, ← hay, mul_inv_rev]
  have key : ⁅a * b, a' * b'⁆ = a * (b * ((a' * b') * b⁻¹ * (a' * b')⁻¹)) * a⁻¹ := by
    rw [commutatorElement_def]
    calc a * b * (a' * b') * (a * b)⁻¹ * (a' * b')⁻¹
        = a * b * (a' * b') * b⁻¹ * (a⁻¹ * (a' * b')⁻¹) := by group
      _ = a * b * (a' * b') * b⁻¹ * ((a' * b')⁻¹ * a⁻¹) := by rw [hinv]
      _ = a * (b * ((a' * b') * b⁻¹ * (a' * b')⁻¹)) * a⁻¹ := by group
  rw [key]
  exact hBn.conj_mem _ (B.mul_mem hb (hBn.conj_mem _ (B.inv_mem hb) _)) a

private theorem mem_sup_centralizer_of_commute {K : Subgroup Γ} [hKn : K.Normal]
    (hKC : K ⊔ Subgroup.centralizer (K : Set Γ) = ⊤)
    (hZ : ∀ z ∈ Subgroup.center Γ, Odd (orderOf z)) {t x : Γ} (ht : t * t = 1)
    (hx : x * t = t * x) :
    x ∈ (K ⊓ Subgroup.centralizer ({t} : Set Γ)) ⊔ Subgroup.centralizer (K : Set Γ) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hxmem : x ∈ K ⊔ Subgroup.centralizer (K : Set Γ) := hKC ▸ Subgroup.mem_top x
  obtain ⟨k, hk, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxmem
  set z : Γ := k⁻¹ * (t * k * t⁻¹) with hz
  have hzK : z ∈ K := K.mul_mem (K.inv_mem hk) (hKn.conj_mem k hk t)
  have hz' : z = c * (t * c⁻¹ * t⁻¹) := by
    have e1 : t * (k * c) * t⁻¹ = k * c := by
      calc t * (k * c) * t⁻¹ = (k * c) * t * t⁻¹ := by rw [← hx]
        _ = k * c := by group
    calc z = k⁻¹ * (t * (k * c) * t⁻¹) * (t * c⁻¹ * t⁻¹) := by rw [hz]; group
      _ = k⁻¹ * (k * c) * (t * c⁻¹ * t⁻¹) := by rw [e1]
      _ = c * (t * c⁻¹ * t⁻¹) := by group
  have hzC : z ∈ Subgroup.centralizer (K : Set Γ) := by
    rw [hz']
    exact (Subgroup.centralizer (K : Set Γ)).mul_mem hc
      ((Subgroup.normal_centralizer).conj_mem _ ((Subgroup.centralizer _).inv_mem hc) t)
  have hcomm : ∀ k₁ ∈ K, ∀ c₁ ∈ Subgroup.centralizer (K : Set Γ), k₁ * c₁ = c₁ * k₁ :=
    fun k₁ hk₁ c₁ hc₁ => Subgroup.mem_centralizer_iff.mp hc₁ k₁ hk₁
  have hzZ : z ∈ Subgroup.center Γ := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k₁, hk₁, c₁, hc₁, rfl⟩ :=
      Subgroup.mem_sup_of_normal_right.mp (hKC ▸ Subgroup.mem_top g : g ∈ _)
    have e1 : k₁ * z = z * k₁ := Subgroup.mem_centralizer_iff.mp hzC k₁ hk₁
    have e2 : z * c₁ = c₁ * z := hcomm z hzK c₁ hc₁
    calc k₁ * c₁ * z = k₁ * (c₁ * z) := by group
      _ = k₁ * (z * c₁) := by rw [e2]
      _ = (k₁ * z) * c₁ := by group
      _ = (z * k₁) * c₁ := by rw [e1]
      _ = z * (k₁ * c₁) := by group
  obtain ⟨m, hm⟩ := hZ z hzZ
  have htz : t * z * t⁻¹ = z⁻¹ := by
    rw [hz, htinv]
    have e : t * t = 1 := ht
    calc t * (k⁻¹ * (t * k * t)) * t = t * k⁻¹ * t * k * (t * t) := by group
      _ = t * k⁻¹ * t * k := by rw [e, mul_one]
      _ = (k⁻¹ * (t * k * t))⁻¹ := by
        simp only [mul_inv_rev, inv_inv, htinv]
        group
  set w : Γ := z ^ (m + 1) with hw
  have htw : t * w * t⁻¹ = w⁻¹ := by rw [hw, ← conj_pow, htz, inv_pow]
  have hzw : z = w * w := by
    rw [hw, ← pow_add, show m + 1 + (m + 1) = orderOf z + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hwK : w ∈ K := K.pow_mem hzK _
  have hwC : w ∈ Subgroup.centralizer (K : Set Γ) := (Subgroup.centralizer _).pow_mem hzC _
  have htk : t * k * t⁻¹ = k * z := by rw [hz]; group
  have hkw : k * w ∈ K ⊓ Subgroup.centralizer ({t} : Set Γ) := by
    refine Subgroup.mem_inf.2 ⟨K.mul_mem hk hwK, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hwk : w * k = k * w := (hcomm k hk w hwC).symm
    have e : t * (k * w) * t⁻¹ = k * w := by
      calc t * (k * w) * t⁻¹ = (t * k * t⁻¹) * (t * w * t⁻¹) := by group
        _ = k * z * w⁻¹ := by rw [htk, htw]
        _ = k * w := by rw [hzw]; group
    calc k * w * t = (t * (k * w) * t⁻¹) * t := by rw [e]
      _ = t * (k * w) := by group
  have : k * c = (k * w) * (w⁻¹ * c) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hkw ((Subgroup.centralizer _).mul_mem
    ((Subgroup.centralizer _).inv_mem hwC) hc)

end GroupTheory

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem eq_one_of_mem_centralizer_of_mul_self {L : Subgroup (GLV V)} (hperf : ⁅L, L⁆ = L)
    (hirr : HasIrrTildeV L) (hf : FaithfulTildeV L) {z : GLV V} (hzL : z ∈ L)
    (hzc : z ∈ Subgroup.centralizer (L : Set (GLV V))) (hz2 : z * z = 1) : z = 1 := by
  let U : Submodule (ZMod 2) V := LinearMap.ker ((z : V →ₗ[ZMod 2] V) - LinearMap.id)
  have hmemU : ∀ v, v ∈ U ↔ z v = v := by
    intro v
    simp [U, sub_eq_zero]
  have hU : Invariant L U := by
    intro k hk u hu
    rw [hmemU] at hu ⊢
    have hkz : k * z = z * k := Subgroup.mem_centralizer_iff.mp hzc k hk
    calc z (k u) = (z * k) u := rfl
      _ = (k * z) u := by rw [hkz]
      _ = k (z u) := rfl
      _ = k u := by rw [hu]
  have hzz : ∀ v, z (z v) = v := fun v => by
    have := congrArg (fun f : GLV V => f v) hz2
    simpa using this
  apply hf z hzL
  intro w hw
  rcases trivial_or_commSpace_le hperf hirr hU with htriv | hle
  · have hzw : z w - w ∈ U := by
      rw [hmemU, map_sub, hzz, ← neg_sub, ZModModule.neg_eq_self]
    intro k hk
    exact htriv k hk _ hzw
  · have : z w = w := (hmemU w).1 (hle hw)
    rw [this, sub_self]
    exact (fixedSpace L).zero_mem

private theorem nonempty_center_quotient_mulEquiv {P X : Type*} [Group P] [Group X]
    (hP : CFSG.Open.IsQuasisimple P) [hX : IsSimpleGroup X] (α : P →* X)
    (hα : Function.Surjective α) : Nonempty (P ⧸ Subgroup.center P ≃* X) := by
  have hQ : CFSG.IsQuasisimple P :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.2 hP
  obtain ⟨x₀, hx₀⟩ := exists_ne (1 : X)
  have hker : α.ker = Subgroup.center P := by
    apply le_antisymm
    · rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ (α.normal_ker) with h | h
      · exfalso
        obtain ⟨p, rfl⟩ := hα x₀
        exact hx₀ (h ▸ Subgroup.mem_top p : p ∈ α.ker)
      · exact h
    · intro z hz
      by_contra hne
      have hcen : α z ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨p, rfl⟩ := hα y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz p]
      have hctop : Subgroup.center X = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
        · exfalso
          rw [h, Subgroup.mem_bot] at hcen
          exact hne hcen
        · exact h
      have hcomm : commutator X = ⊥ := by
        rw [commutator_def, Subgroup.commutator_top_left_eq_bot_iff_le_center, hctop]
      have hperf : commutator X = ⊤ := by
        rw [commutator_def, ← Subgroup.map_top_of_surjective α hα, ← Subgroup.map_commutator,
          ← commutator_def, hP.1, Subgroup.map_top_of_surjective α hα]
      have : x₀ ∈ (⊥ : Subgroup X) := hcomm ▸ hperf ▸ Subgroup.mem_top x₀
      exact hx₀ ((Subgroup.mem_bot).1 this)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)⟩

open CFSG.ComponentClassification.RankTwoClassical.ORigid
  (isSimpleGroup_statedOmega_quadPlus_of_three_le isSimpleGroup_statedOmega_quadMinus_of_two_le) in
private theorem glaubermanAt_of_isFModule (hgl : GlaubermanF) {L : Subgroup (GLV V)} (hfm : IsFModule L)
    {P : Type} [Group P] [Finite P] (hP : CFSG.Open.IsQuasisimple P) (e : P ≃* ↥L) :
    CFSG.CGT.PushingUpLit.CGT6.Nine7.GlaubermanAt (P ⧸ Subgroup.center P) := by
  apply hgl
  rcases hfm with ⟨n, hn, α, hα, -⟩ | ⟨⟨α, hα⟩, -⟩ | ⟨m, hm, α, hα, -⟩ | ⟨m, hm, α, hα, -⟩ |
    ⟨⟨α, hα⟩, -⟩
  · have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    exact Or.inl ⟨n, hn, nonempty_center_quotient_mulEquiv hP (α.comp e.toMonoidHom)
      (hα.comp e.surjective)⟩
  · have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    exact Or.inl ⟨7, by norm_num, nonempty_center_quotient_mulEquiv hP (α.comp e.toMonoidHom)
      (hα.comp e.surjective)⟩
  · have : IsSimpleGroup ↥(CFSG.RankThree.PartTwo.omegaPlusTwo m) :=
      isSimpleGroup_statedOmega_quadPlus_of_three_le (K := ZMod 2) hm
    exact Or.inr (Or.inl ⟨m, hm, nonempty_center_quotient_mulEquiv hP (α.comp e.toMonoidHom)
      (hα.comp e.surjective)⟩)
  · have : IsSimpleGroup ↥(CFSG.RankThree.PartTwo.omegaMinusTwo m) :=
      isSimpleGroup_statedOmega_quadMinus_of_two_le (K := ZMod 2) (m := m + 1) (by omega)
        CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.irreducible_one_one
    exact Or.inr (Or.inr ⟨m, hm, nonempty_center_quotient_mulEquiv hP (α.comp e.toMonoidHom)
      (hα.comp e.surjective)⟩)
  · have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    exact Or.inl ⟨6, le_rfl, nonempty_center_quotient_mulEquiv hP (α.comp e.toMonoidHom)
      (hα.comp e.surjective)⟩

private theorem Extremal.component_of_inv (hclimb : Climb66) {G S L : Subgroup (GLV V)}
    (h : Extremal G S L) {s : GLV V} (hsG : s ∈ G) (hs2 : orderOf s = 2)
    (hsL : s ∈ Subgroup.centralizer (L : Set (GLV V)))
    (hs : IsComponentOf L (G ⊓ Subgroup.centralizer ({s} : Set (GLV V)))) :
    ∀ t ∈ G, orderOf t = 2 → t ∈ Subgroup.centralizer (L : Set (GLV V)) →
      IsComponentOf L (G ⊓ Subgroup.centralizer ({t} : Set (GLV V))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup (GLV V) := G ⊓ Subgroup.centralizer (L : Set (GLV V)) with hK
  have hconj : ∀ k ∈ K, ∀ t : GLV V,
      IsComponentOf L (G ⊓ Subgroup.centralizer ({t} : Set (GLV V))) →
      IsComponentOf L (G ⊓ Subgroup.centralizer ({k * t * k⁻¹} : Set (GLV V))) := by
    intro k hk t ht
    have := isComponentOf_map_conj ht k
    rwa [map_conj_eq_of_mem_centralizer hk.2, map_conj_inf_centralizer hk.1] at this
  have hres : ∀ R : Subgroup (GLV V), R ≤ K → ∀ t ∈ R,
      IsComponentOf L (G ⊓ Subgroup.centralizer ({t} : Set (GLV V))) →
      IsComponentOf L (G ⊓ Subgroup.centralizer (R : Set (GLV V))) := by
    intro R hRK t htR ht
    refine isComponentOf_of_le_of_le ht ?_ ?_
    · refine le_inf (ht.1.trans inf_le_left) ?_
      rw [Subgroup.le_centralizer_iff]
      exact hRK.trans inf_le_right
    · exact inf_le_inf_left G (Subgroup.centralizer_le (Set.singleton_subset_iff.2 htR))
  have hRG : ∀ R : Subgroup (GLV V), R ≤ K → R ≤ G := fun R hR => hR.trans inf_le_left
  intro u huG hu2 huL
  let u' : ↥K := ⟨u, huG, huL⟩
  let s' : ↥K := ⟨s, hsG, hsL⟩
  have hu'2 : orderOf u' = 2 := by rw [← Subgroup.orderOf_coe]; exact hu2
  have hs'2 : orderOf s' = 2 := by rw [← Subgroup.orderOf_coe]; exact hs2
  obtain ⟨T, hT⟩ := (isPGroup_zpowers_of_orderOf hu'2).exists_le_sylow
  obtain ⟨T', hT'⟩ := (isPGroup_zpowers_of_orderOf hs'2).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥K T' T
  have hks : k * s' * k⁻¹ ∈ (T : Subgroup ↥K) := by
    have h1 : MulAut.conj k • s' ∈ MulAut.conj k • (T' : Subgroup ↥K) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hT' (Subgroup.mem_zpowers s'))
    rw [← Sylow.coe_subgroup_smul, hk] at h1
    simpa [MulAut.smul_def, MulAut.conj_apply] using h1
  set RT : Subgroup (GLV V) := (T : Subgroup ↥K).map K.subtype with hRT
  have hRTK : RT ≤ K := Subgroup.map_subtype_le _
  have hRTp : IsPGroup 2 RT := T.isPGroup'.map K.subtype
  have hsT : (k : GLV V) * s * (k : GLV V)⁻¹ ∈ RT := ⟨_, hks, rfl⟩
  have hcompT : IsComponentOf L (G ⊓ Subgroup.centralizer (RT : Set (GLV V))) :=
    hres RT hRTK _ hsT (hconj k k.2 s hs)
  have hks2 : orderOf ((k : GLV V) * s * (k : GLV V)⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj (k : GLV V)) s
    rw [MulAut.conj_apply] at this
    rw [this, hs2]
  have h2RT : 2 ∣ Nat.card RT := by
    have := orderOf_dvd_natCard (⟨_, hsT⟩ : ↥RT)
    rwa [← Subgroup.orderOf_coe, Subgroup.coe_mk, hks2] at this
  have : Group.IsNilpotent ↥RT := hRTp.isNilpotent
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥RT)) 2
    (Group.IsNilpotent.prime_dvd_card_center h2RT)
  set z : GLV V := ((z₀ : ↥RT) : GLV V) with hzdef
  have hzRT : z ∈ RT := (z₀ : ↥RT).2
  have hzc : z ∈ Subgroup.centralizer (RT : Set (GLV V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z₀.2 ⟨y, hy⟩)
  have hz2 : orderOf z = 2 := by
    rw [hzdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz₀
  have hcompz := hclimb V G S L RT z h hRTp (hRG RT hRTK) hcompT hzRT hzc hz2
  set R : Subgroup (GLV V) := RT ⊓ Subgroup.centralizer ({u} : Set (GLV V)) with hR
  have hRK : R ≤ K := inf_le_left.trans hRTK
  have hRp : IsPGroup 2 R := hRTp.to_le inf_le_left
  have huRT : u ∈ RT := ⟨u', hT (Subgroup.mem_zpowers u'), rfl⟩
  have hzR : z ∈ R := by
    refine Subgroup.mem_inf.2 ⟨hzRT, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hzc u huRT).symm
  have hcompR := hres R hRK z hzR hcompz
  have huR : u ∈ R := Subgroup.mem_inf.2 ⟨huRT, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have huc : u ∈ Subgroup.centralizer (R : Set (GLV V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.1 hy).2
  exact hclimb V G S L R u h hRp (hRG R hRK) hcompR huR huc hu2

private theorem Extremal.commutator_ne_bot
    (h5 : CFSG.ComponentClassification.GSThmB.AschbacherTheorem5Input)
    (hKG : CFSG.ComponentClassification.AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hgl : GlaubermanF) {G S L : Subgroup (GLV V)} (h : Extremal G S L)
    (hstar : ∀ t ∈ G, orderOf t = 2 → t ∈ Subgroup.centralizer (L : Set (GLV V)) →
      IsComponentOf L (G ⊓ Subgroup.centralizer ({t} : Set (GLV V)))) :
    ∀ g ∈ G, ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  have hLG : L ≤ G := h.toConf66.L_le
  have hLq : CFSG.Open.IsQuasisimple ↥L := h.setup.component.2.2
  set A : Subgroup ↥G := L.subgroupOf G with hAdef
  let e : ↥A ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLG
  have hAq : CFSG.CGT.PushingUpLit.CGT6.Nine7.QS A := CFSG.Open.IsQuasisimple.of_mulEquiv e hLq
  have hAL : A.map G.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLG
  have hmemA : ∀ x : ↥G, x ∈ A ↔ (x : GLV V) ∈ L := fun x => Subgroup.mem_subgroupOf
  have hcentL : ∀ a : ↥G, (∀ x ∈ A, x * a = a * x) →
      (a : GLV V) ∈ Subgroup.centralizer (L : Set (GLV V)) := by
    intro a hAa
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (hAa ⟨l, hLG hl⟩ ((hmemA ⟨l, hLG hl⟩).2 hl))
  have hs : CFSG.CGT.PushingUpLit.CGT6.Nine7.Star A := by
    intro a ha hAa
    have ha2 : orderOf (a : GLV V) = 2 := by rw [Subgroup.orderOf_coe]; exact ha
    have hc := hstar _ a.2 ha2
      (hcentL a fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hAa hx))
    have hsub := hc.2.1.comap G.subtype
    have hcomap : (G ⊓ Subgroup.centralizer ({(a : GLV V)} : Set (GLV V))).comap G.subtype =
        Subgroup.centralizer ({a} : Set ↥G) := inf_centralizer_singleton_subgroupOf a
    rw [hcomap] at hsub
    exact hsub.subgroupOf
  have hglaub := glaubermanAt_of_isFModule hgl h.fmod.isFModule hAq e
  rcases CFSG.CGT.PushingUpLit.CGT6.Nine7.nine_seven_star h5 hKG hAq hs hglaub with
    ⟨-, -, hne⟩ | ⟨x, -, -, hrank, -⟩ | hsub
  · intro g hg hbot
    apply hne ⟨g, hg⟩⁻¹
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_bot]
    show ⁅A.map G.subtype,
      (A.map (MulAut.conj (⟨g, hg⟩⁻¹ : ↥G)⁻¹).toMonoidHom).map G.subtype⁆ = ⊥
    rw [inv_inv, map_subtype_map_conj, hAL]
    exact hbot
  · exfalso
    have h2 := CFSG.CGT.PushingUpLit.CGT6.Nine7.two_le_pRank_of_no_central_involution hAq
      (fun u hu hu2 huc => by
        have huL : (u : GLV V) ∈ L := (hmemA u).1 hu
        have hucL : (u : GLV V) ∈ Subgroup.centralizer (L : Set (GLV V)) :=
          hcentL u fun x hx => Subgroup.mem_centralizer_iff.mp huc x hx
        have hu' : u * u = 1 := by
          have := pow_orderOf_eq_one u
          rwa [hu2, pow_two] at this
        have hu1 := eq_one_of_mem_centralizer_of_mul_self
          (commutator_eq_self_of_isQuasisimple hLq) h.setup.irrTilde h.faithful huL hucL
          (by rw [← Subgroup.coe_mul, hu', Subgroup.coe_one])
        have : u = 1 := Subtype.ext hu1
        rw [this, orderOf_one] at hu2
        exact absurd hu2 (by norm_num))
    omega
  · exfalso
    have hsubG : IsSubnormal L G := by
      have := (CFSG.Open.IsSubnormal.of_mathlib hsub).map G.subtype
      rwa [hAL, Subgroup.map_top, Subgroup.range_subtype] at this
    have hAcomp : CFSG.IsComponent A :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLG).1
        (CFSG.Assembly.isComponentOf_iff_open.2 ⟨hLG, hsubG, hLq⟩)
    have hnorm := CFSG.LocalCores.layer_le_normalizer hAcomp
    have hcl : normalClosure (layerIn G) L ≤ L := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨γ, ⟨γ', hγ', rfl⟩, l, hl, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp (hnorm hγ') ⟨l, hLG hl⟩).mp ((hmemA _).2 hl)
      exact (hmemA _).1 this
    apply h.layerIn_ne
    exact le_antisymm (h.setup.normalClosure_layerIn ▸ hcl) h.setup.toSetup6.le_layerIn

private theorem tight_of_component_of_inv {G L : Subgroup (GLV V)}
    (hstar : ∀ t ∈ G, orderOf t = 2 → t ∈ Subgroup.centralizer (L : Set (GLV V)) →
      IsComponentOf L (G ⊓ Subgroup.centralizer ({t} : Set (GLV V))))
    (hcomm : ∀ g ∈ G, ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∀ g ∈ G, g ∉ Subgroup.normalizer (L : Set (GLV V)) →
      Odd (Nat.card ↥((G ⊓ Subgroup.centralizer (L : Set (GLV V))) ⊓
        (G ⊓ Subgroup.centralizer (L : Set (GLV V))).map (MulAut.conj g).toMonoidHom)) := by
  intro g hg hgN
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hodd)
  have ht2 : orderOf (t : GLV V) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  obtain ⟨htK, htKg⟩ := Subgroup.mem_inf.1 t.2
  obtain ⟨t₀, ht₀K, ht₀⟩ := Subgroup.mem_map.1 htKg
  have ht₀' : g * t₀ * g⁻¹ = (t : GLV V) := by
    rw [← ht₀]
    simp [MulAut.conj_apply]
  have ht₀2 : orderOf t₀ = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) t₀
    rw [MulAut.conj_apply, ht₀', ht2] at this
    exact this.symm
  have h1 := hstar _ htK.1 ht2 htK.2
  have h2 := isComponentOf_map_conj (hstar t₀ ht₀K.1 ht₀2 ht₀K.2) g
  rw [map_conj_inf_centralizer hg, ht₀'] at h2
  have hne : L ≠ L.map (MulAut.conj g).toMonoidHom := fun heq =>
    hgN (mem_normalizer_of_map_conj_eq heq.symm)
  exact hcomm g hg (CFSG.CGT.PushingUpLit.CGT6.Nine7.commute_of_isCompIn_ne
    ⟨h1.1, h1.2.1.subgroupOf, h1.2.2⟩ ⟨h2.1, h2.2.1.subgroupOf, h2.2.2⟩ hne)

private theorem normalizer_eq_of_tight {G L : Subgroup (GLV V)} {s : GLV V} (hsG : s ∈ G)
    (hs2 : orderOf s = 2) (hsL : s ∈ Subgroup.centralizer (L : Set (GLV V)))
    (htight : ∀ g ∈ G, g ∉ Subgroup.normalizer (L : Set (GLV V)) →
      Odd (Nat.card ↥((G ⊓ Subgroup.centralizer (L : Set (GLV V))) ⊓
        (G ⊓ Subgroup.centralizer (L : Set (GLV V))).map (MulAut.conj g).toMonoidHom))) :
    G ⊓ Subgroup.normalizer
        ((G ⊓ Subgroup.centralizer (L : Set (GLV V)) : Subgroup (GLV V)) : Set (GLV V)) =
      G ⊓ Subgroup.normalizer (L : Set (GLV V)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgG, hgK⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨hgG, ?_⟩
    by_contra hgN
    have hodd := htight g hgG hgN
    rw [map_conj_eq_self_of_mem_normalizer hgK, inf_idem] at hodd
    have hdvd := orderOf_dvd_natCard
      (⟨s, Subgroup.mem_inf.2 ⟨hsG, hsL⟩⟩ : ↥(G ⊓ Subgroup.centralizer (L : Set (GLV V))))
    rw [Subgroup.orderOf_mk, hs2] at hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  · intro g hg
    obtain ⟨hgG, hgN⟩ := Subgroup.mem_inf.1 hg
    exact Subgroup.mem_inf.2 ⟨hgG, mem_normalizer_inf_centralizer hgG hgN⟩

private theorem Extremal.quasisimple_of_four_dvd {G L : Subgroup (GLV V)} {s : GLV V}
    (h : Extremal G (Subgroup.zpowers s) L) (hs2 : orderOf s = 2)
    (hstar : ∀ t ∈ G, orderOf t = 2 → t ∈ Subgroup.centralizer (L : Set (GLV V)) →
      IsComponentOf L (G ⊓ Subgroup.centralizer ({t} : Set (GLV V))))
    (h4 : 4 ∣ Nat.card ↥(G ⊓ Subgroup.centralizer (L : Set (GLV V)))) :
    G = layerIn G ∧ CFSG.IsQuasisimple ↥G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGE : G = layerIn G ⊔ Subgroup.zpowers s := h.setup.eq_layerIn_sup
  have hsG : s ∈ G := h.setup.S_le (Subgroup.mem_zpowers s)
  set K : Subgroup (GLV V) := G ⊓ Subgroup.centralizer (L : Set (GLV V)) with hKdef
  have hne0 : ∀ H J : Subgroup (GLV V), H.relIndex J ≠ 0 := fun H J hzero => by
    have := Subgroup.relIndex_mul_card (H := H) (K := J)
    rw [hzero, zero_mul] at this
    exact Nat.card_pos.ne' this.symm
  have hidx : (layerIn G).relIndex G ≤ 2 := by
    have : (CFSG.layer ↥G).Characteristic := CFSG.LocalCores.layer_characteristic
    let σ : ↥G := ⟨s, hsG⟩
    have htop : Subgroup.zpowers σ ⊔ CFSG.layer ↥G = ⊤ := by
      apply Subgroup.map_injective G.subtype_injective
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top, Subgroup.range_subtype,
        sup_comm]
      exact hGE.symm
    rw [Subgroup.relIndex, layerIn_subgroupOf, ← Subgroup.relIndex_top_right, ← htop,
      Subgroup.relIndex_sup_right]
    calc (CFSG.layer ↥G).relIndex (Subgroup.zpowers σ) ≤ Nat.card (Subgroup.zpowers σ) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _)
      _ = 2 := by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hs2]
  have hrel : (layerIn G).relIndex K ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right inf_le_left (hne0 _ _)).trans hidx
  have hcardK := Subgroup.relIndex_mul_card (H := layerIn G) (K := K)
  have h2 : 2 ∣ Nat.card ↥(layerIn G ⊓ K) := by
    rcases (show (layerIn G).relIndex K = 1 ∨ (layerIn G).relIndex K = 2 by
        have := hne0 (layerIn G) K; omega) with hr | hr
    · rw [hr, one_mul] at hcardK
      rw [hcardK]
      exact dvd_trans (by norm_num) h4
    · rw [hr] at hcardK
      rw [← hcardK] at h4
      omega
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set t : GLV V := (t₀ : GLV V) with htdef
  have ht2 : orderOf t = 2 := by rw [htdef, Subgroup.orderOf_coe]; exact ht₀
  obtain ⟨htE, htK⟩ := Subgroup.mem_inf.1 t₀.2
  have hcompt := hstar t htK.1 ht2 htK.2
  have hZt : Subgroup.zpowers t ≤ layerIn G := Subgroup.zpowers_le.2 htE
  have hLE : L ≤ layerIn G := h.setup.toSetup6.le_layerIn
  have hEG : layerIn G = G := by
    refine h.eq_of_le (layerIn_le G) le_rfl (isPGroup_zpowers_of_orderOf ht2) hZt ?_
      (sup_eq_left.2 hZt).symm
    rw [centralizer_zpowers_eq]
    exact isComponentOf_of_le_of_le hcompt (le_inf hLE (hcompt.1.trans inf_le_right))
      (inf_le_inf_right _ (layerIn_le G))
  refine ⟨hEG.symm, ?_⟩
  have hlayer : CFSG.layer ↥G = ⊤ := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact hEG
  have hLG : L ≤ G := h.toConf66.L_le
  have hLq : CFSG.Open.IsQuasisimple ↥L := h.setup.component.2.2
  set L' : Subgroup ↥G := L.subgroupOf G with hL'def
  have hL'L : L'.map G.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLG
  have hmemL' : ∀ x : ↥G, x ∈ L' ↔ (x : GLV V) ∈ L := fun x => Subgroup.mem_subgroupOf
  set t' : ↥G := ⟨t, htK.1⟩ with ht'def
  set C' : Subgroup ↥G := Subgroup.centralizer ({t'} : Set ↥G) with hC'def
  have hL'C' : L' ≤ C' := by
    intro x hx
    rw [hC'def, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp htK.2 x ((hmemL' x).1 hx))
  have hL'perf : ⁅L', L'⁆ = L' := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_commutator, hL'L]
    exact commutator_eq_self_of_isQuasisimple hLq
  have hL'comp : CFSG.IsComponent (L'.subgroupOf C') := by
    have hq : CFSG.Open.IsQuasisimple ↥(L'.subgroupOf C') :=
      CFSG.Open.IsQuasisimple.of_mulEquiv
        ((Subgroup.subgroupOfEquivOfLe hL'C').trans (Subgroup.subgroupOfEquivOfLe hLG)) hLq
    refine ⟨CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.2 hq, ?_⟩
    have hsub := hcompt.2.1.comap G.subtype
    have hcomap : (G ⊓ Subgroup.centralizer ({t} : Set (GLV V))).comap G.subtype = C' :=
      inf_centralizer_singleton_subgroupOf t'
    rw [hcomap] at hsub
    exact hsub.subgroupOf
  have hZodd : ∀ z ∈ Subgroup.center ↥G, Odd (orderOf z) := by
    intro z hz
    have hzc : (z : GLV V) ∈ G ⊓ Subgroup.centralizer (G : Set (GLV V)) := by
      refine Subgroup.mem_inf.2 ⟨z.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
    have hdvd := orderOf_dvd_natCard
      (⟨_, hzc⟩ : ↥(G ⊓ Subgroup.centralizer (G : Set (GLV V))))
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at hdvd
    exact h.setup.odd_card_center.of_dvd_nat hdvd
  have ht'2 : t' * t' = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one t
    rw [ht2, pow_two] at this
    exact this
  have hdich : ∀ Q : Subgroup ↥G, CFSG.IsComponent Q →
      L' ≤ Q ∨ L' ≤ Subgroup.centralizer (Q : Set ↥G) := by
    intro Q hQ
    haveI hQn : Q.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hlayer hQ
    rcases CFSG.LocalCores.component_normal_subgroup hL'comp (hQn.subgroupOf C') with h1 | h1
    · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hL'C' h1)
    · right
      have hcomm := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hL'C' h1
      have hQC : Q ⊔ Subgroup.centralizer (Q : Set ↥G) = ⊤ := by
        rw [eq_top_iff, ← hlayer, CFSG.layer.eq_sSup]
        refine sSup_le fun Q' hQ' => ?_
        rcases CFSG.LocalCores.distinct_components_commute hQ' hQ with rfl | h2
        · exact le_sup_left
        · exact le_sup_of_le_right (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2)
      refine le_of_perfect_of_le_sup hL'perf (fun x hx => ?_) ?_
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
      · exact mem_sup_centralizer_of_commute hQC hZodd ht'2
          (Subgroup.mem_centralizer_singleton_iff.mp (hL'C' hx))
      · exact inf_le_left.trans (Subgroup.le_centralizer_iff.mpr le_rfl)
  by_cases hex : ∃ Q : Subgroup ↥G, CFSG.IsComponent Q ∧ L' ≤ Q
  · obtain ⟨Q, hQ, hLQ⟩ := hex
    have hQn : Q.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hlayer hQ
    have hQtop : Q = ⊤ := by
      have hcl : normalClosure G L ≤ Q.map G.subtype := by
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨γ, hγ, l, hl, rfl⟩
        have hlQ : (⟨l, hLG hl⟩ : ↥G) ∈ Q := hLQ ((hmemL' _).2 hl)
        exact ⟨⟨γ, hγ⟩ * ⟨l, hLG hl⟩ * ⟨γ, hγ⟩⁻¹, hQn.conj_mem _ hlQ _, rfl⟩
      have hGQ : G ≤ Q.map G.subtype := by
        calc G = layerIn G := hEG.symm
          _ = normalClosure (layerIn G) L := h.setup.normalClosure_layerIn.symm
          _ = normalClosure G L := by rw [hEG]
          _ ≤ Q.map G.subtype := hcl
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, hy, hyx⟩ := hGQ x.2
      rwa [← Subtype.ext hyx]
    subst hQtop
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv hQ.1
  · push Not at hex
    exfalso
    have hcent : ∀ Q : Subgroup ↥G, CFSG.IsComponent Q →
        Q ≤ Subgroup.centralizer (L' : Set ↥G) := by
      intro Q hQ
      rcases hdich Q hQ with h1 | h1
      · exact absurd h1 (hex Q hQ)
      · exact Subgroup.le_centralizer_iff.mp h1
    have htop : (⊤ : Subgroup ↥G) ≤ Subgroup.centralizer (L' : Set ↥G) := by
      rw [← hlayer, CFSG.layer.eq_sSup]
      exact sSup_le fun Q hQ => hcent Q hQ
    have hbot : ⁅L', L'⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_top.trans htop)
    rw [hL'perf] at hbot
    have hnt : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial
      (CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.2 hLq)
    apply (Subgroup.nontrivial_iff_ne_bot L).mp hnt
    rw [← hL'L, hbot, Subgroup.map_bot]

theorem Extremal.exists_stdForm (hclimb : Climb66)
    (h5 : CFSG.ComponentClassification.GSThmB.AschbacherTheorem5Input)
    (hKG : CFSG.ComponentClassification.AschbacherKnownGroup.AschbacherKnownGroupFacts) (hgl : GlaubermanF)
    {G S L : Subgroup (GLV V)} (h : Extremal G S L) : ∃ s : GLV V, StdForm G L s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsPGroup 2 S := h.setup.isPGroup
  have hnt : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).2 h.S_ne_bot
  have h2S : 2 ∣ Nat.card ↥S := by
    obtain ⟨n, hn0, hn⟩ := hS.nontrivial_iff_card.mp hnt
    rw [hn]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn0)
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥S)) 2
    (Group.IsNilpotent.prime_dvd_card_center h2S)
  set s : GLV V := ((z₀ : ↥S) : GLV V) with hsdef
  have hsS : s ∈ S := (z₀ : ↥S).2
  have hsc : s ∈ Subgroup.centralizer (S : Set (GLV V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z₀.2 ⟨y, hy⟩)
  have hs2 : orderOf s = 2 := by
    rw [hsdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz₀
  have hsG : s ∈ G := h.setup.S_le hsS
  have hcomps : IsComponentOf L (G ⊓ Subgroup.centralizer ({s} : Set (GLV V))) :=
    hclimb V G S L S s h hS h.setup.S_le h.setup.component hsS hsc hs2
  have hsL : s ∈ Subgroup.centralizer (L : Set (GLV V)) :=
    Subgroup.le_centralizer_iff.mp (h.setup.component.1.trans inf_le_right) hsS
  have hZp : IsPGroup 2 (Subgroup.zpowers s) := isPGroup_zpowers_of_orderOf hs2
  have hZG : Subgroup.zpowers s ≤ G := Subgroup.zpowers_le.2 hsG
  have hcompZ : IsComponentOf L
      (G ⊓ Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (GLV V)) : Set (GLV V))) := by
    rw [centralizer_zpowers_eq]
    exact hcomps
  have hext : Extremal G (Subgroup.zpowers s) L := h.of_isComponentOf hZp hZG hcompZ
  have hb := h.component_of_inv hclimb hsG hs2 hsL hcomps
  have ha := h.commutator_ne_bot h5 hKG hgl hb
  have htight := tight_of_component_of_inv hb ha
  exact ⟨s,
    { extremal := hext
      orderOf_s := hs2
      eq_layerIn_sup := h.eq_layerIn_sup_of_isComponentOf hZp hZG hcompZ
      component_of_inv := hb
      quasisimple := hext.quasisimple_of_four_dvd hs2 hb
      commutator_ne_bot := ha
      tight := htight
      normalizer_eq := normalizer_eq_of_tight hsG hs2 hsL htight }⟩

end CFSG.CGT.Foote82
