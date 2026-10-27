module

public import CFSG.GH74.Generic.S3.LyTrans
public import CFSG.GH74.Generic.S3.L3Sylow
public import CFSG.GH74.Generic.S3.Local
public import CFSG.GH74.Generic.S3.V1InnerLib
public import CFSG.GH74.KGroups.L3EpsFour
public import CFSG.GH74.Generic.S3.V1InnerEps
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.Sporadic.Th.Max3.Packet

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.KGroups.L3Eps (InvData sl2c_center_eq)
open CFSG.QuasithinUnique.Setup.X5 (eq_one_of_involution_mem_odd)
open CFSG.GH74.KGroups.Bal (commutator_induction commutator_self_of_quasisimple)
open scoped MatrixGroups commutatorElement

section Involutions

theorem exists_involution_comm_ne {L : Type} [Group L] [Finite L] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (hp2 : p ≠ 2) (hodd : Odd (Nat.card (center L)))
    (hX : StatedClassicalModel (L ⧸ center L) t 3 p f) {a : L} (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    ∃ b : L, b * b = 1 ∧ b ≠ 1 ∧ b ≠ a ∧ b * a = a * b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  obtain ⟨Q, hQ⟩ := (isPGroup_zpowers_of_involution ha2).exists_le_sylow
  have haQ : a ∈ (Q : Subgroup L) := hQ (Subgroup.mem_zpowers a)
  have hQne : (Q : Subgroup L) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at haQ
    exact ha1 haQ
  obtain ⟨z, hzQ, hz2, hz1, hzc⟩ := exists_central_involution Q.isPGroup' hQne
  have hza : z = a := by
    by_contra hne
    exact hno z hz2 hz1 hne (hzc a haQ).symm
  have hinvQ : ∀ b ∈ (Q : Subgroup L), b * b = 1 → b ≠ 1 → b = a := by
    intro b hbQ hb2 hb1
    by_contra hne
    apply hno b hb2 hb1 hne
    have := hzc b hbQ
    rwa [hza] at this
  obtain ⟨hS2, hSmax⟩ := isMax_map_center Q hodd
  obtain ⟨a', ha'S, b', hb'S, ha'2, hb'2, hab', ha'1, hb'1, hne'⟩ :=
    KGroups.L3Eps.l3eps_sylow_four ht hp2 hX hS2 hSmax
  obtain ⟨a₀, ha₀Q, rfl⟩ := ha'S
  obtain ⟨b₀, hb₀Q, rfl⟩ := hb'S
  have hsq : ∀ c : L, c ∈ (Q : Subgroup L) →
      (QuotientGroup.mk' (center L)) c * (QuotientGroup.mk' (center L)) c = 1 → c * c = 1 := by
    intro c hcQ hc
    have h1 : c * c ∈ center L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
      exact hc
    exact eq_one_of_mem_pGroup_of_mem_center_odd Q.isPGroup' hodd (Q.mul_mem hcQ hcQ) h1
  have ha₀2 : a₀ * a₀ = 1 := hsq a₀ ha₀Q ha'2
  have hb₀2 : b₀ * b₀ = 1 := hsq b₀ hb₀Q hb'2
  have ha₀1 : a₀ ≠ 1 := fun h => ha'1 (by rw [h, map_one])
  have hb₀1 : b₀ ≠ 1 := fun h => hb'1 (by rw [h, map_one])
  have h1 := hinvQ a₀ ha₀Q ha₀2 ha₀1
  have h2 := hinvQ b₀ hb₀Q hb₀2 hb₀1
  exact hne' (by rw [h1, h2])

end Involutions

section Image

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.center_Iv (hnd : NbrData G t p f x y Iw Iv) :
    ∀ z ∈ Iv, (∀ i ∈ Iv, z * i = i * z) → z = 1 ∨ z = y := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hnd.Iv_iso
  have hcent : ∀ z : ↥Iv, (∀ i : ↥Iv, z * i = i * z) → (e.symm z = 1 ∨ e.symm z = -1) := by
    intro z hz
    apply sl2c_center_eq
    rw [Subgroup.mem_center_iff]
    intro B
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (hz (e B)).symm
  have hv : (⟨y, hnd.y_Iv⟩ : ↥Iv) ∈ Subgroup.center ↥Iv := by
    rw [Subgroup.mem_center_iff]
    intro i
    exact Subtype.ext (hnd.Iv_central i i.2)
  have hvc := hcent ⟨y, hnd.y_Iv⟩ (fun i => (Subgroup.mem_center_iff.1 hv i).symm)
  have hvne : e.symm ⟨y, hnd.y_Iv⟩ ≠ 1 := fun h => hnd.y_ne_one (by
    have := congrArg Subtype.val (e.symm.injective (h.trans (map_one e.symm).symm))
    exact this)
  have hv' : e.symm ⟨y, hnd.y_Iv⟩ = -1 := hvc.resolve_left hvne
  intro z hz hzc
  rcases hcent ⟨z, hz⟩ (fun i => Subtype.ext (hzc i i.2)) with h | h
  · left
    exact congrArg Subtype.val (e.symm.injective (h.trans (map_one e.symm).symm))
  · right
    exact congrArg Subtype.val (e.symm.injective (h.trans hv'.symm))

theorem NbrData.card_Iv (hnd : NbrData G t p f x y Iw Iv) :
    Nat.card ↥Iv = p ^ f * ((p ^ f) ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hnd.Iv_iso
  rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]

theorem NbrData.injOn_Iv (hnd : NbrData G t p f x y Iw Iv) :
    ∀ a ∈ Iv, ∀ b ∈ Iv, ∀ (ha : a ∈ Iw) (hb : b ∈ Iw),
      (QuotientGroup.mk (⟨a, ha⟩ : ↥Iw) : ↥Iw ⧸ center ↥Iw) = QuotientGroup.mk ⟨b, hb⟩ → a = b := by
  intro a ha b hb haL hbL h
  have hz : (⟨a, haL⟩ : ↥Iw)⁻¹ * ⟨b, hbL⟩ ∈ center ↥Iw := QuotientGroup.eq.1 h
  have hzIv : a⁻¹ * b ∈ Iv := mul_mem (inv_mem ha) hb
  have hzc : ∀ i ∈ Iv, (a⁻¹ * b) * i = i * (a⁻¹ * b) := by
    intro i hi
    have := Subgroup.mem_center_iff.1 hz ⟨i, hnd.Iv_le hi⟩
    exact (congrArg Subtype.val this).symm
  rcases hnd.center_Iv _ hzIv hzc with h1 | h1
  · calc a = a * (a⁻¹ * b) := by rw [h1, mul_one]
      _ = b := by group
  · exfalso
    have hvL : y ∈ Iw := hnd.y_Iw
    have hvZ : (⟨y, hvL⟩ : ↥Iw) ∈ center ↥Iw := by
      have : (⟨y, hvL⟩ : ↥Iw) = (⟨a, haL⟩ : ↥Iw)⁻¹ * ⟨b, hbL⟩ := Subtype.ext h1.symm
      rw [this]
      exact hz
    have := eq_one_of_involution_mem_odd (C := center ↥Iw) hnd.odd_w hvZ (Subtype.ext hnd.y_sq)
    exact hnd.y_ne_one (congrArg Subtype.val this)

theorem NbrData.image_Iv (hnd : NbrData G t p f x y Iw Iv) {S : Subgroup (↥Iw ⧸ center ↥Iw)}
    (hS : InvData (p ^ f) (↥Iw ⧸ center ↥Iw) (QuotientGroup.mk ⟨y, hnd.y_Iw⟩) S) :
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

theorem NbrData.exists_S (hnd : NbrData G t p f x y Iw Iv) (hlib : LibData t p f) :
    ∃ S : Subgroup (↥Iw ⧸ center ↥Iw),
      InvData (p ^ f) (↥Iw ⧸ center ↥Iw) (QuotientGroup.mk ⟨y, hnd.y_Iw⟩) S := by
  have hX : StatedClassicalModel (↥Iw ⧸ center ↥Iw) t 3 p f := by
    rcases hnd.tag with rfl | rfl
    · exact stated_of_lieModel_PSL hnd.model_w
    · exact stated_of_lieModel_PSU hnd.model_w
  obtain ⟨hinv, -⟩ := hlib _ hX
  have hvL : y ∈ Iw := hnd.y_Iw
  refine hinv _ ?_ ?_
  · show (QuotientGroup.mk (⟨y, hvL⟩ * ⟨y, hvL⟩) : ↥Iw ⧸ center ↥Iw) = 1
    rw [show (⟨y, hvL⟩ * ⟨y, hvL⟩ : ↥Iw) = 1 from Subtype.ext hnd.y_sq]
    rfl
  · intro h
    have hz : (⟨y, hvL⟩ : ↥Iw) ∈ center ↥Iw := (QuotientGroup.eq_one_iff _).1 h
    exact hnd.y_ne_one (congrArg Subtype.val (eq_one_of_involution_mem_odd (C := center ↥Iw) hnd.odd_w hz
      (Subtype.ext hnd.y_sq)))

end Image

end CFSG.GH74.Generic.S3
