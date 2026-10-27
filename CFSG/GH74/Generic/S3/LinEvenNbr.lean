module

public import CFSG.GH74.Generic.S3.LinEvenInv
public import CFSG.GH74.Generic.S3.V1InnerUni
public import CFSG.GH74.Generic.S3.NoFus1

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.KGroups.L3Eps (InvData InvDataB4)
open CFSG.QuasithinUnique.Setup.X5 (eq_one_of_involution_mem_odd)
open CFSG.GH74.KGroups.Bal (commutator_induction commutator_self_of_quasisimple)
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.mk_y_sq (hnd : NbrData G t p f x y Iw Iv) :
    (QuotientGroup.mk (⟨y, hnd.y_Iw⟩ : ↥Iw) : ↥Iw ⧸ center ↥Iw) * QuotientGroup.mk ⟨y, hnd.y_Iw⟩ = 1 := by
  show (QuotientGroup.mk (⟨y, hnd.y_Iw⟩ * ⟨y, hnd.y_Iw⟩ : ↥Iw) : ↥Iw ⧸ center ↥Iw) = 1
  rw [show (⟨y, hnd.y_Iw⟩ * ⟨y, hnd.y_Iw⟩ : ↥Iw) = 1 from Subtype.ext hnd.y_sq]
  rfl

theorem NbrData.mk_y_ne_one (hnd : NbrData G t p f x y Iw Iv) :
    (QuotientGroup.mk (⟨y, hnd.y_Iw⟩ : ↥Iw) : ↥Iw ⧸ center ↥Iw) ≠ 1 := by
  intro h
  have hz : (⟨y, hnd.y_Iw⟩ : ↥Iw) ∈ center ↥Iw := (QuotientGroup.eq_one_iff _).1 h
  exact hnd.y_ne_one (congrArg Subtype.val (eq_one_of_involution_mem_odd (C := center ↥Iw) hnd.odd_w hz
    (Subtype.ext hnd.y_sq)))

theorem NbrData.exists_S_B4 (hnd : NbrData G t p f x y Iw Iv) :
    ∃ S : Subgroup (↥Iw ⧸ center ↥Iw),
      InvDataB4 (p ^ f) (↥Iw ⧸ center ↥Iw) (QuotientGroup.mk ⟨y, hnd.y_Iw⟩) S := by
  rcases hnd.tag with rfl | rfl
  · exact exists_invDataB4_lin hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2
      (stated_of_lieModel_PSL hnd.model_w) hnd.mk_y_sq hnd.mk_y_ne_one
  · obtain ⟨S, hS⟩ := hnd.exists_S (libData_uni hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2)
    exact ⟨S, hS.toB4⟩

theorem NbrData.image_Iv_B4 (hnd : NbrData G t p f x y Iw Iv) {S : Subgroup (↥Iw ⧸ center ↥Iw)}
    (hS : InvDataB4 (p ^ f) (↥Iw ⧸ center ↥Iw) (QuotientGroup.mk ⟨y, hnd.y_Iw⟩) S) :
    ∀ s : ↥Iw ⧸ center ↥Iw, s ∈ S ↔
      ∃ i : ↥Iw, (i : G) ∈ Iv ∧ (QuotientGroup.mk i : ↥Iw ⧸ center ↥Iw) = s := by
  classical
  have hvL : y ∈ Iw := hnd.y_Iw
  set π : ↥Iw →* ↥Iw ⧸ center ↥Iw := QuotientGroup.mk' (center ↥Iw) with hπ
  set t' : ↥Iw ⧸ center ↥Iw := QuotientGroup.mk ⟨y, hvL⟩ with ht'
  have hIL : Iv ≤ Iw := hnd.Iv_le
  have hle : ∀ i : ↥Iw, (i : G) ∈ Iv → π i ∈ S := by
    intro i hi
    have hperf : ⁅Iv, Iv⁆ = Iv := commutator_self_of_quasisimple hnd.Iv_quasisimple
    have hi' : (i : G) ∈ ⁅Iv, Iv⁆ := by rw [hperf]; exact hi
    have key : ∀ w ∈ ⁅Iv, Iv⁆, ∃ hwL : w ∈ Iw, π ⟨w, hwL⟩ ∈ S := by
      intro w hw
      refine commutator_induction (C := fun w => ∃ hwL : w ∈ Iw, π ⟨w, hwL⟩ ∈ S) hw ?_ ?_ ?_ ?_
      · intro a ha b hb
        have haL : a ∈ Iw := hIL ha
        have hbL : b ∈ Iw := hIL hb
        refine ⟨mul_mem (mul_mem (mul_mem haL hbL) (inv_mem haL)) (inv_mem hbL), ?_⟩
        have hsub : (⟨⁅a, b⁆, mul_mem (mul_mem (mul_mem haL hbL) (inv_mem haL)) (inv_mem hbL)⟩ : ↥Iw) =
            ⁅(⟨a, haL⟩ : ↥Iw), ⟨b, hbL⟩⁆ := rfl
        rw [hsub, map_commutatorElement]
        have hca : π ⟨a, haL⟩ ∈ Subgroup.centralizer ({t'} : Set (↥Iw ⧸ center ↥Iw)) := by
          rw [Subgroup.mem_centralizer_singleton_iff, ht']
          show (QuotientGroup.mk (⟨a, haL⟩ * ⟨y, hvL⟩) : ↥Iw ⧸ center ↥Iw) =
            QuotientGroup.mk (⟨y, hvL⟩ * ⟨a, haL⟩)
          congr 1
          exact Subtype.ext (hnd.Iv_central a ha)
        have hcb : π ⟨b, hbL⟩ ∈ Subgroup.centralizer ({t'} : Set (↥Iw ⧸ center ↥Iw)) := by
          rw [Subgroup.mem_centralizer_singleton_iff, ht']
          show (QuotientGroup.mk (⟨b, hbL⟩ * ⟨y, hvL⟩) : ↥Iw ⧸ center ↥Iw) =
            QuotientGroup.mk (⟨y, hvL⟩ * ⟨b, hbL⟩)
          congr 1
          exact Subtype.ext (hnd.Iv_central b hb)
        exact hS.commutator_mem _ hca _ hcb
      · refine ⟨one_mem _, ?_⟩
        show π 1 ∈ S
        rw [map_one]
        exact one_mem S
      · rintro y₁ y₂ ⟨h1L, h1S⟩ ⟨h2L, h2S⟩
        refine ⟨mul_mem h1L h2L, ?_⟩
        have hsub : (⟨y₁ * y₂, mul_mem h1L h2L⟩ : ↥Iw) = ⟨y₁, h1L⟩ * ⟨y₂, h2L⟩ := rfl
        rw [hsub, map_mul]
        exact mul_mem h1S h2S
      · rintro y₁ ⟨h1L, h1S⟩
        refine ⟨inv_mem h1L, ?_⟩
        have hsub : (⟨y₁⁻¹, inv_mem h1L⟩ : ↥Iw) = (⟨y₁, h1L⟩ : ↥Iw)⁻¹ := rfl
        rw [hsub, map_inv]
        exact inv_mem h1S
    obtain ⟨hxL, h⟩ := key (i : G) hi'
    exact h
  intro s
  constructor
  · intro hs
    let g : ↥(Iv.subgroupOf Iw) →* ↥Iw ⧸ center ↥Iw := π.comp (Iv.subgroupOf Iw).subtype
    have hginj : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact hnd.injOn_Iv a.1.1 a.2 b.1.1 b.2 a.1.2 b.1.2 hab
    have hrange_le : g.range ≤ S := by
      rintro _ ⟨a, rfl⟩
      exact hle a.1 a.2
    have hcard : Nat.card ↥S ≤ Nat.card ↥g.range := by
      rw [hS.card, ← Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIL).toEquiv, hnd.card_Iv]
    have heq : g.range = S := Subgroup.eq_of_le_of_card_ge hrange_le hcard
    rw [← heq] at hs
    obtain ⟨a, ha⟩ := hs
    exact ⟨a.1, a.2, ha⟩
  · rintro ⟨i, hi, rfl⟩
    exact hle i hi

end CFSG.GH74.Generic.S3
