module

public import CFSG.GH74.Generic.S3.L3Class
public import CFSG.GH74.KGroups.L3EpsInvLin
public import CFSG.GH74.KGroups.BalanceLift
public import CFSG.GH74.KGroups.L3EpsOrder

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.KGroups.L3Eps (InvData GraphData invData_of_equiv graphData_of_equiv tInv tInv_mul_self tInv_ne_one
  exists_projectiveSL_equiv odd_of_pow_mod_four_eq_three sl2c_center_eq)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.QuasithinUnique.Setup.X5 (normalizerAct normalizerAct_of_mem normalizerAct_apply_mk conjOn coe_conjOn
  mem_centralizer_of_normalizerAct_eq_one eq_one_of_involution_mem_odd)
open CFSG.GH74.KGroups.Bal (commutator_induction commutator_self_of_quasisimple)
open scoped MatrixGroups commutatorElement

@[expose] def LibData (t : StatedLieTag) (p f : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], StatedClassicalModel K t 3 p f →
    (∀ x : K, x * x = 1 → x ≠ 1 → ∃ S : Subgroup K, InvData (p ^ f) K x S) ∧
    (∀ c : MulAut K, c * c = 1 → c ∉ (inner K : Subgroup (MulAut K)) →
      ∃ N : Subgroup K, GraphData K c N)

theorem singleInv_projectiveSL {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    SingleInv (projectiveSL 3 F) :=
  SingleInv.of_mulEquiv
    ((projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 F)).symm) (singleInv_psl h2)

theorem two_ne_zero_of_odd_card {F : Type} [Field F] [Finite F] (h : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  have : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F ≠ 2 := fun h2 => by
    have h' := (FiniteField.even_card_iff_char_two (F := F)).1 h2
    rw [Nat.card_eq_fintype_card] at h
    obtain ⟨k, hk⟩ := h
    omega
  exact Ring.two_ne_zero hF2

theorem libData_lin {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (h3 : p ^ f % 4 = 3) :
    LibData .PSL p f := by
  intro K _ _ hX
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hf : Odd f := odd_of_pow_mod_four_eq_three hpodd h3
  have hodd : Odd (Nat.card F) := by rw [hF]; exact hpodd.pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h5' : 5 ≤ Nat.card F := by rw [hF]; exact h5
  refine ⟨fun x hx2 hx1 => ?_, fun c hc2 hout => graphData_of_equiv hp hF hf h2 h5' e hc2 hout⟩
  have hex2 : e x * e x = 1 := by rw [← map_mul, hx2, map_one]
  have hex1 : e x ≠ 1 := fun h => hx1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g, hg⟩ := singleInv_projectiveSL h2 (e x) tInv hex2 hex1 tInv_mul_self (tInv_ne_one h2)
  let e' : K ≃* projectiveSL 3 F := e.trans (MulAut.conj g)
  have he' : e' x = tInv := by
    show MulAut.conj g (e x) = tInv
    rw [MulAut.conj_apply]
    exact hg
  exact ⟨_, invData_of_equiv hp hF hf h2 (by omega) e' he'⟩


section IvFacts

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {v w : G} {Iv Iw Ivw P : Subgroup G}

theorem Conf2A.v_sq (C : Conf2A G t p f v w Iv Iw Ivw P) : v * v = 1 := by
  have := pow_orderOf_eq_one v
  rwa [C.v_inv, pow_two] at this

theorem Conf2A.v_ne_one (C : Conf2A G t p f v w Iv Iw Ivw P) : v ≠ 1 := fun h => by
  have := C.v_inv
  rw [h, orderOf_one] at this
  omega

theorem Conf2A.w_sq (C : Conf2A G t p f v w Iv Iw Ivw P) : w * w = 1 := by
  have := pow_orderOf_eq_one w
  rwa [C.w_inv, pow_two] at this

theorem Conf2A.w_ne_one (C : Conf2A G t p f v w Iv Iw Ivw P) : w ≠ 1 := fun h => by
  have := C.w_inv
  rw [h, orderOf_one] at this
  omega

theorem Conf2A.center_Iv (C : Conf2A G t p f v w Iv Iw Ivw P) :
    ∀ z ∈ Iv, (∀ x ∈ Iv, z * x = x * z) → z = 1 ∨ z = v := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := C.iso_v
  have hcent : ∀ z : ↥Iv, (∀ x : ↥Iv, z * x = x * z) → (e.symm z = 1 ∨ e.symm z = -1) := by
    intro z hz
    apply sl2c_center_eq
    rw [Subgroup.mem_center_iff]
    intro B
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (hz (e B)).symm
  have hv : (⟨v, C.v_mem⟩ : ↥Iv) ∈ Subgroup.center ↥Iv := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (C.comp_v.1 x.2))
  have hvc := hcent ⟨v, C.v_mem⟩ (fun x => (Subgroup.mem_center_iff.1 hv x).symm)
  have hvne : e.symm ⟨v, C.v_mem⟩ ≠ 1 := fun h => C.v_ne_one (by
    have := congrArg Subtype.val (e.symm.injective (h.trans (map_one e.symm).symm))
    exact this)
  have hv' : e.symm ⟨v, C.v_mem⟩ = -1 := hvc.resolve_left hvne
  intro z hz hzc
  rcases hcent ⟨z, hz⟩ (fun x => Subtype.ext (hzc x x.2)) with h | h
  · left
    exact congrArg Subtype.val (e.symm.injective (h.trans (map_one e.symm).symm))
  · right
    exact congrArg Subtype.val (e.symm.injective (h.trans hv'.symm))

theorem Conf2A.card_Iv (C : Conf2A G t p f v w Iv Iw Ivw P) :
    Nat.card ↥Iv = p ^ f * ((p ^ f) ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := C.iso_v
  rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]

end IvFacts

section Image

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {v w : G} {Iv Iw Ivw P : Subgroup G}
  {L : Subgroup G}

theorem Conf2A.injOn_Iv (C : Conf2A G t p f v w Iv Iw Ivw P) (hIL : Iv ≤ L)
    (hodd : Odd (Nat.card ↥(center ↥L))) :
    ∀ x ∈ Iv, ∀ y ∈ Iv, ∀ (hx : x ∈ L) (hy : y ∈ L),
      (QuotientGroup.mk (⟨x, hx⟩ : ↥L) : ↥L ⧸ center ↥L) = QuotientGroup.mk ⟨y, hy⟩ → x = y := by
  intro x hx y hy hxL hyL h
  have hz : (⟨x, hxL⟩ : ↥L)⁻¹ * ⟨y, hyL⟩ ∈ center ↥L := QuotientGroup.eq.1 h
  have hzIv : x⁻¹ * y ∈ Iv := mul_mem (inv_mem hx) hy
  have hzc : ∀ i ∈ Iv, (x⁻¹ * y) * i = i * (x⁻¹ * y) := by
    intro i hi
    have := Subgroup.mem_center_iff.1 hz ⟨i, hIL hi⟩
    exact (congrArg Subtype.val this).symm
  rcases C.center_Iv _ hzIv hzc with h1 | h1
  · calc x = x * (x⁻¹ * y) := by rw [h1, mul_one]
      _ = y := by group
  · exfalso
    have hvL : v ∈ L := hIL C.v_mem
    have hvZ : (⟨v, hvL⟩ : ↥L) ∈ center ↥L := by
      have : (⟨v, hvL⟩ : ↥L) = (⟨x, hxL⟩ : ↥L)⁻¹ * ⟨y, hyL⟩ := Subtype.ext h1.symm
      rw [this]
      exact hz
    have := eq_one_of_involution_mem_odd (C := center ↥L) hodd hvZ (Subtype.ext C.v_sq)
    exact C.v_ne_one (congrArg Subtype.val this)


theorem Conf2A.image_Iv (C : Conf2A G t p f v w Iv Iw Ivw P) (hIL : Iv ≤ L)
    (hodd : Odd (Nat.card ↥(center ↥L))) {S : Subgroup (↥L ⧸ center ↥L)}
    (hS : InvData (p ^ f) (↥L ⧸ center ↥L) (QuotientGroup.mk ⟨v, hIL C.v_mem⟩) S) :
    ∀ s : ↥L ⧸ center ↥L, s ∈ S ↔
      ∃ x : ↥L, (x : G) ∈ Iv ∧ (QuotientGroup.mk x : ↥L ⧸ center ↥L) = s := by
  classical
  have hvL : v ∈ L := hIL C.v_mem
  set π : ↥L →* ↥L ⧸ center ↥L := QuotientGroup.mk' (center ↥L) with hπ
  set t' : ↥L ⧸ center ↥L := QuotientGroup.mk ⟨v, hvL⟩ with ht'
  have hle : ∀ x : ↥L, (x : G) ∈ Iv → π x ∈ S := by
    intro x hx
    have hperf : ⁅Iv, Iv⁆ = Iv := commutator_self_of_quasisimple C.comp_v.isQuasisimple
    have hx' : (x : G) ∈ ⁅Iv, Iv⁆ := by rw [hperf]; exact hx
    have key : ∀ y ∈ ⁅Iv, Iv⁆, ∃ hyL : y ∈ L, π ⟨y, hyL⟩ ∈ S := by
      intro y hy
      refine commutator_induction (C := fun y => ∃ hyL : y ∈ L, π ⟨y, hyL⟩ ∈ S) hy ?_ ?_ ?_ ?_
      · intro a ha b hb
        have haL : a ∈ L := hIL ha
        have hbL : b ∈ L := hIL hb
        refine ⟨mul_mem (mul_mem (mul_mem haL hbL) (inv_mem haL)) (inv_mem hbL), ?_⟩
        have hsub : (⟨⁅a, b⁆, mul_mem (mul_mem (mul_mem haL hbL) (inv_mem haL)) (inv_mem hbL)⟩ : ↥L) =
            ⁅(⟨a, haL⟩ : ↥L), ⟨b, hbL⟩⁆ := rfl
        rw [hsub, map_commutatorElement]
        have hca : π ⟨a, haL⟩ ∈ Subgroup.centralizer ({t'} : Set (↥L ⧸ center ↥L)) := by
          rw [Subgroup.mem_centralizer_singleton_iff, ht']
          show (QuotientGroup.mk (⟨a, haL⟩ * ⟨v, hvL⟩) : ↥L ⧸ center ↥L) = QuotientGroup.mk (⟨v, hvL⟩ * ⟨a, haL⟩)
          congr 1
          exact Subtype.ext (mem_centralizer_singleton_iff.1 (C.comp_v.1 ha))
        have hcb : π ⟨b, hbL⟩ ∈ Subgroup.centralizer ({t'} : Set (↥L ⧸ center ↥L)) := by
          rw [Subgroup.mem_centralizer_singleton_iff, ht']
          show (QuotientGroup.mk (⟨b, hbL⟩ * ⟨v, hvL⟩) : ↥L ⧸ center ↥L) = QuotientGroup.mk (⟨v, hvL⟩ * ⟨b, hbL⟩)
          congr 1
          exact Subtype.ext (mem_centralizer_singleton_iff.1 (C.comp_v.1 hb))
        exact hS.commutator_mem _ hca _ hcb
      · refine ⟨one_mem _, ?_⟩
        show π 1 ∈ S
        rw [map_one]
        exact one_mem S
      · rintro y₁ y₂ ⟨h1L, h1S⟩ ⟨h2L, h2S⟩
        refine ⟨mul_mem h1L h2L, ?_⟩
        have hsub : (⟨y₁ * y₂, mul_mem h1L h2L⟩ : ↥L) = ⟨y₁, h1L⟩ * ⟨y₂, h2L⟩ := rfl
        rw [hsub, map_mul]
        exact mul_mem h1S h2S
      · rintro y₁ ⟨h1L, h1S⟩
        refine ⟨inv_mem h1L, ?_⟩
        have hsub : (⟨y₁⁻¹, inv_mem h1L⟩ : ↥L) = (⟨y₁, h1L⟩ : ↥L)⁻¹ := rfl
        rw [hsub, map_inv]
        exact inv_mem h1S
    obtain ⟨hxL, h⟩ := key (x : G) hx'
    exact h
  intro s
  constructor
  · intro hs
    let g : ↥(Iv.subgroupOf L) →* ↥L ⧸ center ↥L := π.comp (Iv.subgroupOf L).subtype
    have hginj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact C.injOn_Iv hIL hodd x.1.1 x.2 y.1.1 y.2 x.1.2 y.1.2 hxy
    have hrange_le : g.range ≤ S := by
      rintro _ ⟨x, rfl⟩
      exact hle x.1 x.2
    have hcard : Nat.card ↥S ≤ Nat.card ↥g.range := by
      rw [hS.card, ← Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIL).toEquiv, C.card_Iv]
    have heq : g.range = S := Subgroup.eq_of_le_of_card_ge hrange_le hcard
    rw [← heq] at hs
    obtain ⟨x, hx⟩ := hs
    exact ⟨x.1, x.2, hx⟩
  · rintro ⟨x, hx, rfl⟩
    exact hle x hx

end Image


end CFSG.GH74.Generic.S3
