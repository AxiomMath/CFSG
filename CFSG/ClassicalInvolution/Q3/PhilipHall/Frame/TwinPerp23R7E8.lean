module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Orb
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E8G
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Fus
import CFSG.ClassicalInvolution.Q3.TL4AE286None
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmBase
import CFSG.ClassicalInvolution.AschTight.Sec7L714F
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7TwoWTr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Transport217

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7I

section Gen

variable {Y : Type} [Group Y] [Finite Y] {C : Subgroup Y}

abbrev piC (C : Subgroup Y) : ↥C →* ↥C ⧸ classicalInvolutionOddCore ↥C :=
  QuotientGroup.mk' (classicalInvolutionOddCore ↥C)

theorem piC_eq_one_iff (c : ↥C) : piC C c = 1 ↔ (c : Y) ∈ oddCoreOf C := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨c, h, rfl⟩
  · rintro ⟨c', hc', h⟩
    rwa [Subtype.ext h] at hc'

theorem piC_eq_iff (c d : ↥C) : piC C c = piC C d ↔ ((c⁻¹ * d : ↥C) : Y) ∈ oddCoreOf C := by
  rw [← piC_eq_one_iff, map_mul, map_inv, inv_mul_eq_one, eq_comm]

theorem piC_inj {P : Subgroup Y} (hP2 : IsPGroup 2 P) {x y : ↥C} (hx : (x : Y) ∈ P)
    (hy : (y : Y) ∈ P) (h : piC C x = piC C y) : x = y := by
  rw [piC_eq_iff] at h
  have hP : ((x⁻¹ * y : ↥C) : Y) ∈ P := by
    show (x : Y)⁻¹ * y ∈ P
    exact P.mul_mem (P.inv_mem hx) hy
  have h1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard C) h
    (hP2.to_le (Subgroup.zpowers_le.mpr hP))
  have h2 : x⁻¹ * y = 1 := Subtype.ext h1
  exact (inv_mul_eq_one.mp h2)

theorem map_le_of_le_sup {H P : Subgroup Y} (hPC : P ≤ C) (hH : H ≤ oddCoreOf C ⊔ P) :
    (H.subgroupOf C).map (piC C) ≤ (P.subgroupOf C).map (piC C) := by
  rintro _ ⟨x, hx, rfl⟩
  have hPN : P ≤ Subgroup.normalizer (oddCoreOf C : Set Y) :=
    hPC.trans (Sec7.le_normalizer_oddCoreOf C)
  have hx' : (x : Y) ∈ ((oddCoreOf C ⊔ P : Subgroup Y) : Set Y) :=
    hH (Subgroup.mem_subgroupOf.mp hx)
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hPN] at hx'
  obtain ⟨o, ho, p, hp, hop⟩ := hx'
  refine ⟨⟨p, hPC hp⟩, Subgroup.mem_subgroupOf.mpr hp, ?_⟩
  rw [piC_eq_iff]
  have : ((⟨p, hPC hp⟩⁻¹ * x : ↥C) : Y) = p⁻¹ * o * p⁻¹⁻¹ := by
    show p⁻¹ * (x : Y) = _
    rw [← hop]
    group
  rw [this]
  exact (Subgroup.mem_normalizer_iff.mp (hPN (P.inv_mem hp)) o).mp ho

theorem map_eq_of_le_sup {H P : Subgroup Y} (hPH : P ≤ H) (hHC : H ≤ C)
    (hH : H ≤ oddCoreOf C ⊔ P) :
    (H.subgroupOf C).map (piC C) = (P.subgroupOf C).map (piC C) :=
  le_antisymm (map_le_of_le_sup (hPH.trans hHC) hH)
    (Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr (hPH (Subgroup.mem_subgroupOf.mp hx)))

theorem mem_map_piC {H : Subgroup Y} {q : ↥C ⧸ classicalInvolutionOddCore ↥C} :
    q ∈ (H.subgroupOf C).map (piC C) ↔ ∃ x : ↥C, (x : Y) ∈ H ∧ piC C x = q := by
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem q8_image {P : Subgroup Y} (hPC : P ≤ C) {t : Y} (htC : t ∈ C)
    (hP : IsUniqueInvolution P t) (h8 : Nat.card P = 8) (hnab : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) :
    IsUniqueInvolution ((P.subgroupOf C).map (piC C)) (piC C ⟨t, htC⟩) ∧
      Nat.card ((P.subgroupOf C).map (piC C)) = 8 ∧
      ∃ x ∈ (P.subgroupOf C).map (piC C), ∃ y ∈ (P.subgroupOf C).map (piC C), x * y ≠ y * x := by
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  have hinj : ∀ x y : ↥C, (x : Y) ∈ P → (y : Y) ∈ P → piC C x = piC C y → x = y :=
    fun x y hx hy h => piC_inj hP2 hx hy h
  refine ⟨⟨mem_map_piC.mpr ⟨_, hP.mem, rfl⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro h
    rw [← map_one (piC C)] at h
    have := hinj _ _ hP.mem P.one_mem h
    exact hP.ne_one (congrArg Subtype.val this)
  · rw [← map_mul]
    rw [piC_eq_one_iff]
    show t * t ∈ oddCoreOf C
    rw [hP.sq]
    exact (oddCoreOf C).one_mem
  · intro q hq hq2
    obtain ⟨x, hx, rfl⟩ := mem_map_piC.mp hq
    rw [← map_mul, ← map_one (piC C)] at hq2
    have h1 := hinj _ _ (P.mul_mem hx hx) P.one_mem hq2
    rcases hP.unique _ hx (congrArg Subtype.val h1) with h | h
    · left
      rw [show x = 1 from Subtype.ext h, map_one]
    · right
      rw [show x = ⟨t, htC⟩ from Subtype.ext h]
  · have hinj' : Function.Injective ((piC C).comp (P.subgroupOf C).subtype) := by
      intro x y h
      exact Subtype.ext (hinj _ _ x.2 y.2 h)
    have hr : ((piC C).comp (P.subgroupOf C).subtype).range = (P.subgroupOf C).map (piC C) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr, Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv.symm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv, h8]
  · obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    refine ⟨_, mem_map_piC.mpr ⟨⟨x, hPC hx⟩, hx, rfl⟩, _, mem_map_piC.mpr ⟨⟨y, hPC hy⟩, hy, rfl⟩, ?_⟩
    intro h
    rw [← map_mul, ← map_mul] at h
    have := hinj _ _ (P.mul_mem hx hy) (P.mul_mem hy hx) h
    exact hxy (congrArg Subtype.val this)

theorem conjSub_map_piC {H : Subgroup Y} (c : ↥C) :
    conjSub (piC C c) ((H.subgroupOf C).map (piC C)) =
      ((conjSub (c : Y) H).subgroupOf C).map (piC C) := by
  ext q
  rw [mem_conjSub_iff, mem_map_piC, mem_map_piC]
  constructor
  · rintro ⟨x, hx, hxq⟩
    refine ⟨c * x * c⁻¹, ?_, ?_⟩
    · show (c : Y) * x * (c : Y)⁻¹ ∈ conjSub (c : Y) H
      exact conj_mem_conjSub hx
    · rw [map_mul, map_mul, map_inv, hxq]
      group
  · rintro ⟨x, hx, rfl⟩
    refine ⟨c⁻¹ * x * c, ?_, ?_⟩
    · have := mem_conjSub_iff.mp hx
      simpa using this
    · rw [map_mul, map_mul, map_inv]

theorem frattini_W {W : Subgroup Y} (hWC : W ≤ C) (hW2 : IsPGroup 2 W) {c : Y}
    (h : conjSub c W ⊔ oddCoreOf C = W ⊔ oddCoreOf C) :
    ∃ o ∈ oddCoreOf C, o * c ∈ Subgroup.normalizer (W : Set Y) := by
  set O := oddCoreOf C with hO
  set E := W ⊔ O with hEdef
  have hON : C ≤ Subgroup.normalizer (O : Set Y) := Sec7.le_normalizer_oddCoreOf C
  have hOC : O ≤ C := oddCoreOf_le_self C
  have hEN : E ≤ Subgroup.normalizer (O : Set Y) := sup_le (hWC.trans hON) (hOC.trans hON)
  have hOE : O ≤ oddCoreOf E :=
    AscFusion.le_oddCoreOf_of_normal_odd le_sup_right hEN (oddCoreOf_odd_natCard C)
  have hE : E ≤ oddCoreOf E ⊔ (E ⊓ W) :=
    sup_le (fun w hw => Subgroup.mem_sup_right ⟨Subgroup.mem_sup_left hw, hw⟩)
      (hOE.trans le_sup_left)
  have hA2 : IsPGroup 2 (conjSub c W) := hW2.map (MulAut.conj c).toMonoidHom
  have hAE : conjSub c W ≤ E := le_sup_left.trans h.le
  obtain ⟨o, ho, hoA⟩ := TwinPerp23.exists_oddCore_conj_le hE hA2 hAE
  have hEO : oddCoreOf E ≤ O := by
    intro x hx
    have hxE : x ∈ E := oddCoreOf_le_self E hx
    have hWN : W ≤ Subgroup.normalizer (O : Set Y) := hWC.trans hON
    have hxE' : x ∈ ((O ⊔ W : Subgroup Y) : Set Y) := by rw [sup_comm]; exact hxE
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hWN] at hxE'
    obtain ⟨o', ho', w, hw, hxw⟩ := hxE'
    have hw' : w ∈ oddCoreOf E := by
      have := (oddCoreOf E).mul_mem ((oddCoreOf E).inv_mem (hOE ho')) hx
      rwa [← hxw, show o'⁻¹ * (o' * w) = w by group] at this
    have hw1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard E) hw'
      (hW2.to_le (Subgroup.zpowers_le.mpr hw))
    rw [← hxw, hw1]
    simpa using ho'
  refine ⟨o⁻¹, O.inv_mem (hEO ho), ?_⟩
  have hle : conjSub (o⁻¹ * c) W ≤ W := by
    intro x hx
    rw [conjSub_mul, mem_conjSub_iff, inv_inv] at hx
    have := hoA _ hx
    rwa [show o⁻¹ * (o * x * o⁻¹) * o = x by group] at this
  have hcard : Nat.card W ≤ Nat.card (conjSub (o⁻¹ * c) W) :=
    (Subgroup.card_map_of_injective (MulAut.conj (o⁻¹ * c)).injective).ge
  exact mem_normalizer_iff_conjSub_eq.mpr (Subgroup.eq_of_le_of_card_ge hle hcard)

theorem sup_le_of_map_le {H H' : Subgroup Y} (hHC : H ≤ C)
    (h : (H.subgroupOf C).map (piC C) ≤ (H'.subgroupOf C).map (piC C)) :
    H ≤ H' ⊔ oddCoreOf C := by
  intro x hx
  obtain ⟨x', hx', hxx⟩ := mem_map_piC.mp (h (mem_map_piC.mpr ⟨⟨x, hHC hx⟩, hx, rfl⟩))
  rw [piC_eq_iff] at hxx
  have e : x = (x' : Y) * ((x'⁻¹ * ⟨x, hHC hx⟩ : ↥C) : Y) := by
    show x = (x' : Y) * ((x' : Y)⁻¹ * x)
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx') (Subgroup.mem_sup_right hxx)

theorem sup_eq_of_map_eq {H H' : Subgroup Y} (hHC : H ≤ C) (hH'C : H' ≤ C)
    (h : (H.subgroupOf C).map (piC C) = (H'.subgroupOf C).map (piC C)) :
    H ⊔ oddCoreOf C = H' ⊔ oddCoreOf C :=
  le_antisymm (sup_le (sup_le_of_map_le hHC h.le) le_sup_right)
    (sup_le (sup_le_of_map_le hH'C h.ge) le_sup_right)

theorem modZ_of_conjSub_eq {W : Subgroup Y} (hWC : W ≤ C) (hW2 : IsPGroup 2 W) {t : Y}
    (htC : t ∈ C) (htc : ∀ c ∈ C, c * t = t * c) {x : ↥C}
    (hx : ∀ n ∈ C, n ∈ Subgroup.normalizer (W : Set Y) →
      n * x * n⁻¹ = x ∨ n * x * n⁻¹ = x * t)
    (q d : ↥C ⧸ classicalInvolutionOddCore ↥C)
    (h : conjSub q ((W.subgroupOf C).map (piC C)) = conjSub d ((W.subgroupOf C).map (piC C))) :
    F7E.ModZ (piC C ⟨t, htC⟩) (q * piC C x * q⁻¹) (d * piC C x * d⁻¹) := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
  obtain ⟨c', rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) d
  change conjSub (piC C c) _ = conjSub (piC C c') _ at h
  change F7E.ModZ _ (piC C c * piC C x * (piC C c)⁻¹) (piC C c' * piC C x * (piC C c')⁻¹)
  have h1 : conjSub (piC C (c'⁻¹ * c)) ((W.subgroupOf C).map (piC C)) =
      (W.subgroupOf C).map (piC C) := by
    rw [map_mul, map_inv, conjSub_mul, h, conjSub_inv_conjSub]
  rw [conjSub_map_piC] at h1
  have hcW : conjSub ((c'⁻¹ * c : ↥C) : Y) W ≤ C :=
    (conjSub_mono hWC).trans (conjSub_eq_self_of_mem (c'⁻¹ * c).2).le
  obtain ⟨o, ho, hon⟩ := frattini_W hWC hW2 (sup_eq_of_map_eq hcW hWC h1)
  have hoC : o ∈ C := oddCoreOf_le_self C ho
  have hnC : o * ((c'⁻¹ * c : ↥C) : Y) ∈ C := C.mul_mem hoC (c'⁻¹ * c).2
  have hpn : piC C ⟨_, hnC⟩ = piC C (c'⁻¹ * c) := by
    have e : (⟨_, hnC⟩ : ↥C) = ⟨o, hoC⟩ * (c'⁻¹ * c) := rfl
    rw [e, map_mul, (piC_eq_one_iff ⟨o, hoC⟩).mpr ho, one_mul]
  have hz : ∀ a : ↥C, piC C a * piC C ⟨t, htC⟩ = piC C ⟨t, htC⟩ * piC C a := by
    intro a
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (htc _ a.2))
  have key : piC C (c'⁻¹ * c) * piC C x * (piC C (c'⁻¹ * c))⁻¹ = piC C x ∨
      piC C (c'⁻¹ * c) * piC C x * (piC C (c'⁻¹ * c))⁻¹ = piC C x * piC C ⟨t, htC⟩ := by
    rw [← hpn, ← map_mul, ← map_inv, ← map_mul]
    rcases hx _ hnC hon with h2 | h2
    · left
      exact congrArg _ (Subtype.ext h2)
    · right
      rw [← map_mul]
      exact congrArg _ (Subtype.ext h2)
  rw [map_mul, map_inv] at key
  have e2 : piC C c * piC C x * (piC C c)⁻¹ =
      piC C c' * ((piC C c')⁻¹ * piC C c * piC C x * ((piC C c')⁻¹ * piC C c)⁻¹) *
        (piC C c')⁻¹ := by group
  rcases key with k | k
  · left
    rw [e2, k]
  · right
    rw [e2, k]
    have h3 : (piC C c')⁻¹ * piC C ⟨t, htC⟩ = piC C ⟨t, htC⟩ * (piC C c')⁻¹ := by
      rw [← map_inv]; exact hz _
    calc piC C c' * (piC C x * piC C ⟨t, htC⟩) * (piC C c')⁻¹
        = piC C c' * piC C x * (piC C ⟨t, htC⟩ * (piC C c')⁻¹) := by group
      _ = _ := by rw [← h3]; group

end Gen

section Elem

variable {Q : Type} [Group Q]

theorem closure_sq_of_comm {X : Set Q} (hX2 : ∀ x ∈ X, x * x = 1)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : ∀ a ∈ Subgroup.closure X, a * a = 1 := by
  have hc : X.Pairwise Commute := fun x hx y hy _ => hXc x hx y hy
  have hab := Subgroup.isMulCommutative_closure hc
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem t ht => exact hX2 t ht
  | one => simp
  | mul a b ha hb iha ihb =>
    have hcomm : a * b = b * a := by
      have := hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hcomm]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha =>
    rw [← _root_.mul_inv_rev, iha, inv_one]

theorem card_closure_le_eight [Finite Q] {X : Set Q} {z g₀ g₁ g₂ : Q}
    (hz : ∀ q : Q, q * z = z * q) (hz2 : z * z = 1)
    (hX2 : ∀ x ∈ X, x * x = 1) (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hg₀ : g₀ ∈ X) (hg₁ : g₁ ∈ X)
    (hcov : ∀ x ∈ X, F7E.ModZ z x g₀ ∨ F7E.ModZ z x g₁ ∨ F7E.ModZ z x g₂)
    (hprod : F7E.ModZ z (g₀ * g₁ * g₂) 1) :
    Nat.card (Subgroup.closure X) ≤ 8 := by
  set H := Subgroup.closure (insert z (insert g₀ (insert g₁ (∅ : Set Q)))) with hH
  have hzH : z ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have h0H : g₀ ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have h1H : g₁ ∈ H := Subgroup.subset_closure
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have h2H : g₂ ∈ H := by
    have h01 : (g₀ * g₁)⁻¹ ∈ H := H.inv_mem (H.mul_mem h0H h1H)
    have e : g₂ = (g₀ * g₁)⁻¹ * (g₀ * g₁ * g₂) := by group
    rcases hprod with h | h <;> rw [e, h]
    · simpa using h01
    · simpa using H.mul_mem h01 hzH
  have hmod : ∀ x g : Q, g ∈ H → F7E.ModZ z x g → x ∈ H := by
    rintro x g hg (rfl | rfl)
    · exact hg
    · exact H.mul_mem hg hzH
  have hle : Subgroup.closure X ≤ H := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hcov x hx with h | h | h
    · exact hmod _ _ h0H h
    · exact hmod _ _ h1H h
    · exact hmod _ _ h2H h
  have c1 := Balance.Theorem5.card_closure_insert_le (S := insert g₀ (insert g₁ (∅ : Set Q)))
    hz2 (fun s _ => (hz s).symm)
  have c2 := Balance.Theorem5.card_closure_insert_le (S := insert g₁ (∅ : Set Q)) (c := g₀)
    (hX2 g₀ hg₀) (by
      rintro s (rfl | hs)
      · exact hXc _ hg₀ _ hg₁
      · exact absurd hs (Set.notMem_empty _))
  have c3 := Balance.Theorem5.card_closure_insert_le (S := (∅ : Set Q)) (c := g₁)
    (hX2 g₁ hg₁) (by simp)
  rw [Subgroup.closure_empty, Subgroup.card_bot] at c3
  calc Nat.card (Subgroup.closure X) ≤ Nat.card H := Subgroup.card_le_of_le hle
    _ ≤ 8 := by rw [hH]; omega

theorem elem_card [Finite Q] {A B : Subgroup Q} {z a b eb s r g₂ q₁ q₂ : Q}
    (hz : ∀ q : Q, q * z = z * q) (hsA : IsUniqueInvolution A z) (hsB : IsUniqueInvolution B z)
    (h8A : Nat.card A = 8) (h8B : Nat.card B = 8)
    (hnabA : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) (hnabB : ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x)
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hperm : ∀ q : Q, (conjSub q A = A ∧ conjSub q B = B) ∨ (conjSub q A = B ∧ conjSub q B = A))
    (ha : a ∈ A) (hb : b ∈ B) (ha1 : a ≠ 1) (haz : a ≠ z) (hb1 : b ≠ 1) (hbz : b ≠ z)
    (hsAB : conjSub s A = B) (hsBA : conjSub s B = A)
    (hsp : F7E.ModZ z (s * (a * b) * s⁻¹) (a * b))
    (horb : ∀ q : Q, ∃ d : Q, (d = 1 ∨ d = q₁ ∨ d = q₂) ∧
      F7E.ModZ z (q * (a * b) * q⁻¹) (d * (a * b) * d⁻¹))
    (he2 : eb * eb = 1) (heA : ∀ x ∈ A, eb * x = x * eb) (heB : ∀ x ∈ B, eb * x = x * eb)
    (hMB : ∀ m : Q, (∀ x ∈ A, m * x = x * m) → (∀ x ∈ B, m * x = x * m) → m * eb = eb * m)
    (hcov : ∀ γ : Q, F7E.ModZ z (γ * (a * b * eb) * γ⁻¹) (a * b * eb) ∨
      F7E.ModZ z (γ * (a * b * eb) * γ⁻¹) (r * (a * b * eb) * r⁻¹) ∨
      F7E.ModZ z (γ * (a * b * eb) * γ⁻¹) g₂)
    (hprod : F7E.ModZ z ((a * b * eb) * (r * (a * b * eb) * r⁻¹) * g₂) 1 ∨
      g₂ = (a * b * eb) * (r * (a * b * eb) * r⁻¹)) :
    (∀ x ∈ Subgroup.closure {q | ∃ γ : Q, q = γ * (a * b * eb) * γ⁻¹}, x * x = 1) ∧
      Nat.card (Subgroup.closure {q | ∃ γ : Q, q = γ * (a * b * eb) * γ⁻¹}) ≤ 8 := by
  have hz2 : z * z = 1 := hsA.sq
  have hinf : ∀ w ∈ A, w ∈ B → w = 1 ∨ w = z := fun w hwA hwB =>
    F7E.mem_inf_q8 hz hsA h8A hnabA hcomm hwA hwB
  have hcu : ∀ c : Q, (c * (a * b) * c⁻¹) * (a * b) = (a * b) * (c * (a * b) * c⁻¹) :=
    F7E.comm_conj_of_orbit hz hsA hsB h8A h8B hnabA hnabB hcomm hinf hperm ha hb ha1 haz hb1 hbz
      hsAB hsBA hsp horb
  have hconjAB : ∀ m : Q, (∀ x ∈ A, m * x = x * m) → (∀ x ∈ B, m * x = x * m) → ∀ γ : Q,
      (∀ x ∈ A, γ * m * γ⁻¹ * x = x * (γ * m * γ⁻¹)) ∧
        (∀ x ∈ B, γ * m * γ⁻¹ * x = x * (γ * m * γ⁻¹)) := by
    intro m hmA hmB γ
    have key : ∀ x : Q, (γ⁻¹ * x * γ ∈ A ∨ γ⁻¹ * x * γ ∈ B) →
        γ * m * γ⁻¹ * x = x * (γ * m * γ⁻¹) := by
      intro x hx
      have h1 : m * (γ⁻¹ * x * γ) = (γ⁻¹ * x * γ) * m := by
        rcases hx with hx | hx
        · exact hmA _ hx
        · exact hmB _ hx
      calc γ * m * γ⁻¹ * x = γ * (m * (γ⁻¹ * x * γ)) * γ⁻¹ := by group
        _ = γ * ((γ⁻¹ * x * γ) * m) * γ⁻¹ := by rw [h1]
        _ = x * (γ * m * γ⁻¹) := by group
    have hmem : ∀ (H : Subgroup Q) (x : Q), x ∈ H → γ⁻¹ * x * γ ∈ conjSub γ⁻¹ H := by
      intro H x hx
      rw [mem_conjSub_iff]
      have e : γ⁻¹⁻¹ * (γ⁻¹ * x * γ) * γ⁻¹ = x := by group
      rw [e]
      exact hx
    constructor
    · intro x hx
      apply key
      rcases hperm γ⁻¹ with ⟨h1, -⟩ | ⟨h1, -⟩
      · left; rw [← h1]; exact hmem A x hx
      · right; rw [← h1]; exact hmem A x hx
    · intro x hx
      apply key
      rcases hperm γ⁻¹ with ⟨-, h1⟩ | ⟨-, h1⟩
      · right; rw [← h1]; exact hmem B x hx
      · left; rw [← h1]; exact hmem B x hx
  have hcAB : ∀ m : Q, (∀ x ∈ A, m * x = x * m) → (∀ x ∈ B, m * x = x * m) →
      ∀ x : Q, (x ∈ A ∨ x ∈ B) → ∀ γ : Q, m * (γ * x * γ⁻¹) = (γ * x * γ⁻¹) * m := by
    intro m hmA hmB x hx γ
    have : γ * x * γ⁻¹ ∈ A ∨ γ * x * γ⁻¹ ∈ B := by
      rcases hx with hx | hx <;> rcases hperm γ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [← h1]; exact conj_mem_conjSub hx
      · right; rw [← h1]; exact conj_mem_conjSub hx
      · right; rw [← h2]; exact conj_mem_conjSub hx
      · left; rw [← h2]; exact conj_mem_conjSub hx
    rcases this with h | h
    · exact hmA _ h
    · exact hmB _ h
  have hcU : ∀ m : Q, (∀ x ∈ A, m * x = x * m) → (∀ x ∈ B, m * x = x * m) →
      ∀ γ : Q, m * (γ * (a * b) * γ⁻¹) = (γ * (a * b) * γ⁻¹) * m := by
    intro m hmA hmB γ
    have e : γ * (a * b) * γ⁻¹ = (γ * a * γ⁻¹) * (γ * b * γ⁻¹) := by group
    rw [e, ← mul_assoc, hcAB m hmA hmB a (Or.inl ha) γ, mul_assoc,
      hcAB m hmA hmB b (Or.inr hb) γ, ← mul_assoc]
  have hee : ∀ γ : Q, (γ * eb * γ⁻¹) * eb = eb * (γ * eb * γ⁻¹) := fun γ =>
    hMB _ (hconjAB eb heA heB γ).1 (hconjAB eb heA heB γ).2
  set U := a * b with hU
  set gb := U * eb with hgb
  have hgcomm : ∀ ρ : Q, gb * (ρ * gb * ρ⁻¹) = (ρ * gb * ρ⁻¹) * gb := by
    intro ρ
    have e : ρ * gb * ρ⁻¹ = (ρ * U * ρ⁻¹) * (ρ * eb * ρ⁻¹) := by rw [hgb]; group
    rw [e]
    set U' := ρ * U * ρ⁻¹
    set E' := ρ * eb * ρ⁻¹
    have h1 : eb * U' = U' * eb := hcU eb heA heB ρ
    have h2 : E' * U = U * E' := by
      have ha' := (hconjAB eb heA heB ρ).1 a ha
      have hb' := (hconjAB eb heA heB ρ).2 b hb
      rw [hU, ← mul_assoc, ha', mul_assoc, hb', ← mul_assoc]
    have h3 : U' * U = U * U' := hcu ρ
    have h4 : E' * eb = eb * E' := hee ρ
    calc U * eb * (U' * E') = U * (eb * U') * E' := by group
      _ = U * (U' * eb) * E' := by rw [h1]
      _ = (U * U') * (eb * E') := by group
      _ = (U' * U) * (E' * eb) := by rw [h3, h4]
      _ = U' * (E' * U) * eb := by rw [h2]; group
      _ = U' * E' * (U * eb) := by group
  have hg2 : gb * gb = 1 := by
    have heU : eb * U = U * eb := by
      rw [hU, ← mul_assoc, heA a ha, mul_assoc, heB b hb, ← mul_assoc]
    have hU2 : U * U = 1 := by
      have haa := F94.mul_self_eq_q8 hsA h8A hnabA ha ha1 haz
      have hbb := F94.mul_self_eq_q8 hsB h8B hnabB hb hb1 hbz
      calc U * U = a * (b * a) * b := by rw [hU]; group
        _ = a * (a * b) * b := by rw [hcomm a ha b hb]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [haa, hbb, hz2]
    calc gb * gb = U * (eb * U) * eb := by rw [hgb]; group
      _ = (U * U) * (eb * eb) := by rw [heU]; group
      _ = 1 := by rw [hU2, he2, one_mul]
  set X := {q | ∃ γ : Q, q = γ * gb * γ⁻¹} with hX
  have hX2 : ∀ x ∈ X, x * x = 1 := by
    rintro _ ⟨γ, rfl⟩
    calc γ * gb * γ⁻¹ * (γ * gb * γ⁻¹) = γ * (gb * gb) * γ⁻¹ := by group
      _ = 1 := by rw [hg2]; group
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    rintro _ ⟨γ, rfl⟩ _ ⟨δ, rfl⟩
    have h := (F7E.conj_comm_iff γ gb ((γ⁻¹ * δ) * gb * (γ⁻¹ * δ)⁻¹)).mpr (hgcomm _)
    have e : γ * ((γ⁻¹ * δ) * gb * (γ⁻¹ * δ)⁻¹) * γ⁻¹ = δ * gb * δ⁻¹ := by group
    rwa [e] at h
  have hg₀ : gb ∈ X := ⟨1, by group⟩
  have hg₁ : r * gb * r⁻¹ ∈ X := ⟨r, rfl⟩
  refine ⟨closure_sq_of_comm hX2 hXc, card_closure_le_eight (g₂ := g₂) hz hz2 hX2 hXc hg₀ hg₁ ?_ ?_⟩
  · rintro _ ⟨γ, rfl⟩
    exact hcov γ
  · rcases hprod with h | h
    · exact h
    · left
      rw [h]
      have hc := hXc _ hg₀ _ hg₁
      calc gb * (r * gb * r⁻¹) * (gb * (r * gb * r⁻¹))
          = gb * ((r * gb * r⁻¹) * gb) * (r * gb * r⁻¹) := by group
        _ = gb * gb * ((r * gb * r⁻¹) * (r * gb * r⁻¹)) := by rw [← hc]; group
        _ = 1 := by rw [hX2 _ hg₀, hX2 _ hg₁, one_mul]

end Elem

end F7I

section E7E

variable {n : ℕ}

theorem p23_conj_twins {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K' W : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g) {c : Y}
    (hcC : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    (conjSub c (tightCore R) = tightCore R ∧ conjSub c K' = K') ∨
      (conjSub c (tightCore R) = K' ∧ conjSub c K' = tightCore R) := by
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hct : c * t * c⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hcC]; group
  have hpair := twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne
  have hmem : ∀ J : Subgroup Y, J ∈ Om R → IsUniqueInvolution J t →
      conjSub c J = tightCore R ∨ conjSub c J = K' := by
    intro J hJ hJt
    have h1 : conjSub c J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
      refine ⟨?_, t, hz, ?_⟩
      · obtain ⟨a, rfl⟩ := hJ
        exact ⟨c * a, conjSub_mul c a _⟩
      · have := hJt.conj c
        rwa [hct] at this
    rw [hpair] at h1
    simpa using h1
  have hK0 : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  rcases hmem _ hK0 hz with h1 | h1 <;> rcases hmem _ hc.std.hK'.1 hz' with h2 | h2
  · exact absurd (conjSub_injective c (h1.trans h2.symm)) hc.std.hne.symm
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (conjSub_injective c (h1.trans h2.symm)) hc.std.hne.symm

theorem p23_swap_conj {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K' W : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g) {c : Y}
    (hcC : c ∈ Subgroup.centralizer ({t} : Set Y)) (h : conjSub c (tightCore R) = K') :
    conjSub c K' = tightCore R := by
  rcases p23_conj_twins hc hcC with h' | h'
  · exact absurd (h'.1.symm.trans h) hc.std.hne.symm
  · exact h'.2

theorem p23_exists_swap {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K' W : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ s ∈ Subgroup.centralizer ({t} : Set Y), s ∈ Subgroup.normalizer (W : Set Y) ∧
      conjSub s (tightCore R) = K' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hPG : Q3CL.PartIHypG (Om R) := hC.partIHypG
  have hd := hc.data
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have htr : ∀ K₁ ∈ Om R, ∀ J ∈ Om R, ∃ a : Y, conjSub a K₁ = J := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  obtain ⟨S₀, hWS₀, hwc, -⟩ := exists_weaklyClosed_conj_of_muIsoS4 hPG htr hd.hW hd.hS4
  have hW2 : IsPGroup 2 W := Asc77.Thompson.isPGroup_of_mem_WSet hd.hW
  have hWt : W ≤ Subgroup.centralizer ({t} : Set Y) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
  obtain ⟨S₂, hS₂, hWS₂⟩ := IsSylow2In.exists_ge hW2 hWt
  obtain ⟨S₁, hSS₁⟩ := hS₂.2.1.exists_le_sylow
  obtain ⟨a, ha⟩ := exists_conjSub_eq_of_sylow S₀ S₁
  have e2 : conjSub a⁻¹ W = W := hwc a⁻¹ (by
    rw [conjSub_le_iff, inv_inv, ha]
    exact hWS₂.trans hSS₁)
  have e3 : conjSub a W = W := by
    conv_lhs => rw [← e2]
    exact conjSub_conjSub_inv a W
  have hS₂N : S₂ ≤ Subgroup.normalizer (W : Set Y) := by
    intro s hs
    have hs₀ : a⁻¹ * s * a ∈ (S₀ : Subgroup Y) := by
      have := hSS₁ hs
      rw [← ha] at this
      exact mem_conjSub_iff.mp this
    have e4 : conjSub (a⁻¹ * s * a) W = W :=
      hwc _ ((conjSub_mono hWS₀).trans (conjSub_eq_self_of_mem hs₀).le)
    have e5 : conjSub s W = W := by
      have : s = a * (a⁻¹ * s * a) * a⁻¹ := by group
      conv_lhs => rw [this]
      rw [conjSub_mul, conjSub_mul, e2, e4, e3]
    exact mem_normalizer_iff_conjSub_eq.mpr e5
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  obtain ⟨h, hh⟩ := hc.std.hK'.1
  replace hh : conjSub h (tightCore R) = K' := hh
  have hhC : h ∈ C := by
    have h1 := hz.conj h
    rw [hh] at h1
    have h2 : h * t * h⁻¹ = t := h1.eq hz'
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h * t = h * t * h⁻¹ * h := by group
      _ = t * h := by rw [h2]
  have hodd : ∀ j : ℕ, conjSub (h ^ (2 * j + 1)) (tightCore R) = K' := by
    have hsq : conjSub (h * h) (tightCore R) = tightCore R := by
      rw [conjSub_mul, hh, p23_swap_conj hc hhC hh]
    intro j
    induction j with
    | zero => simpa using hh
    | succ j ih =>
      rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring, pow_add, sq, conjSub_mul, hsq, ih]
  have hn : orderOf h ≠ 0 := (orderOf_pos h).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  obtain ⟨j, rfl⟩ := hm
  set d := h ^ (2 * j + 1) with hd'
  have hdC : d ∈ C := C.pow_mem hhC _
  have hpow : d ^ (2 ^ k) = 1 := by
    rw [hd', ← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  let d' : ↥C := ⟨d, hdC⟩
  have hd2 : IsPGroup 2 (Subgroup.zpowers d') := by
    have hpow' : d' ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hpow)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow')
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
  obtain ⟨P', hP'⟩ := hd2.exists_le_sylow
  let P₂ : Sylow 2 ↥C := Asc77.AscP1Nine3.sylowOfIsSylow2In₉ hS₂
  obtain ⟨b, hb⟩ := exists_conjSub_eq_of_sylow P₂ P'
  have hdP' : d' ∈ (P' : Subgroup ↥C) := hP' (Subgroup.mem_zpowers _)
  rw [← hb, mem_conjSub_iff] at hdP'
  have hsS : ((b⁻¹ * d' * b : ↥C) : Y) ∈ S₂ := by
    have : b⁻¹ * d' * b ∈ S₂.subgroupOf C := hdP'
    exact Subgroup.mem_subgroupOf.mp this
  refine ⟨(b⁻¹ * d' * b : ↥C), (b⁻¹ * d' * b : ↥C).2, hS₂N hsS, ?_⟩
  show conjSub ((b : Y)⁻¹ * d * b) (tightCore R) = K'
  have hdK : conjSub d (tightCore R) = K' := hodd j
  have hdK' : conjSub d K' = tightCore R := p23_swap_conj hc hdC hdK
  rw [conjSub_mul, conjSub_mul]
  rcases p23_conj_twins hc b.2 with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
  · have hbi : conjSub (b : Y)⁻¹ K' = K' := by
      conv_lhs => rw [← hb2]
      exact conjSub_inv_conjSub _ _
    rw [hb1, hdK, hbi]
  · have hbi : conjSub (b : Y)⁻¹ (tightCore R) = K' := by
      conv_lhs => rw [← hb2]
      exact conjSub_inv_conjSub _ _
    rw [hb1, hdK', hbi]

@[expose] def P23E7MBar (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
      ∀ x : ↥(Subgroup.centralizer ({t} : Set Y)), (x : Y) = e → ∀ m : ↥(Subgroup.centralizer ({t} : Set Y)) ⧸ classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)),
        (∀ a ∈ ((tightCore R).subgroupOf (Subgroup.centralizer ({t} : Set Y))).map (F7I.piC (Subgroup.centralizer ({t} : Set Y))), m * a = a * m) →
        (∀ a ∈ (K'.subgroupOf (Subgroup.centralizer ({t} : Set Y))).map (F7I.piC (Subgroup.centralizer ({t} : Set Y))), m * a = a * m) →
        m * F7I.piC (Subgroup.centralizer ({t} : Set Y)) x = F7I.piC (Subgroup.centralizer ({t} : Set Y)) x * m

theorem p23_twin_q8 {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K' W : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g) {C : Subgroup Y}
    (hCdef : C = Subgroup.centralizer ({t} : Set Y)) (htC : t ∈ C) (heC : e ∈ C) :
    IsUniqueInvolution (((tightCore R).subgroupOf C).map (F7I.piC C)) (F7I.piC C ⟨t, htC⟩) ∧
    IsUniqueInvolution ((K'.subgroupOf C).map (F7I.piC C)) (F7I.piC C ⟨t, htC⟩) ∧
    Nat.card (((tightCore R).subgroupOf C).map (F7I.piC C)) = 8 ∧
    Nat.card ((K'.subgroupOf C).map (F7I.piC C)) = 8 ∧
    (∃ x ∈ ((tightCore R).subgroupOf C).map (F7I.piC C),
      ∃ y ∈ ((tightCore R).subgroupOf C).map (F7I.piC C), x * y ≠ y * x) ∧
    (∃ x ∈ (K'.subgroupOf C).map (F7I.piC C), ∃ y ∈ (K'.subgroupOf C).map (F7I.piC C),
      x * y ≠ y * x) ∧
    (∀ x ∈ ((tightCore R).subgroupOf C).map (F7I.piC C), ∀ y ∈ (K'.subgroupOf C).map (F7I.piC C),
      x * y = y * x) ∧
    (∀ x ∈ ((tightCore R).subgroupOf C).map (F7I.piC C),
      F7I.piC C ⟨e, heC⟩ * x = x * F7I.piC C ⟨e, heC⟩) ∧
    (∀ x ∈ (K'.subgroupOf C).map (F7I.piC C), F7I.piC C ⟨e, heC⟩ * x = x * F7I.piC C ⟨e, heC⟩) ∧
    ∃ b₁ b' : ↥C, (b₁ : Y) * b' = u ∧ F7I.piC C b₁ ∈ ((tightCore R).subgroupOf C).map (F7I.piC C) ∧
      F7I.piC C b' ∈ (K'.subgroupOf C).map (F7I.piC C) ∧ F7I.piC C b₁ ≠ 1 ∧
      F7I.piC C b₁ ≠ F7I.piC C ⟨t, htC⟩ ∧ F7I.piC C b' ≠ 1 ∧ F7I.piC C b' ≠ F7I.piC C ⟨t, htC⟩ := by
  subst hCdef
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hR₁D, hR₁'D, hcomm, hb₁R, hb'R', ob₁, ob', hub, -⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hKC : tightCore R ≤ C := le_centralizer_of_unique hz
  have hK'C : K' ≤ C := le_centralizer_of_unique hz'
  have hR₁C : R₁ ≤ C := hR₁.1.trans hKC
  have hR₁'C : R₁' ≤ C := hR₁'.1.trans hK'C
  have hK0 : tightCore R ≤ oddCoreOf C ⊔ R₁ := by
    have h1 := TL4.le_sup_oddCoreOf_of_isSylow2In (h2 _ hK) hR₁
    have h3 : oddCoreOf (tightCore R) ≤ oddCoreOf C := Small.oddCoreOf_core_le hc.std.perp
    rw [sup_comm]
    exact h1.trans (sup_le_sup_left h3 _)
  have hK1 : K' ≤ oddCoreOf C ⊔ R₁' := by
    have h1 := TL4.le_sup_oddCoreOf_of_isSylow2In (h2 _ hc.std.hK'.1) hR₁'
    obtain ⟨h, hh⟩ := hc.std.hK'.1
    replace hh : conjSub h (tightCore R) = K' := hh
    have hhC : h ∈ C := by
      have h1 := hz.conj h
      rw [hh] at h1
      have h2 : h * t * h⁻¹ = t := h1.eq hz'
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc h * t = h * t * h⁻¹ * h := by group
        _ = t * h := by rw [h2]
    have h3 : oddCoreOf K' ≤ oddCoreOf C := by
      rw [← hh, Thompson.oddCoreOf_conjSub_eq]
      calc conjSub h (oddCoreOf (tightCore R)) ≤ conjSub h (oddCoreOf C) :=
            conjSub_mono (Small.oddCoreOf_core_le hc.std.perp)
        _ = oddCoreOf C := by
            rw [← Thompson.oddCoreOf_conjSub_eq, conjSub_eq_self_of_mem hhC]
    rw [sup_comm]
    exact h1.trans (sup_le_sup_left h3 _)
  have hA := F7I.map_eq_of_le_sup hR₁.1 hKC hK0
  have hB := F7I.map_eq_of_le_sup hR₁'.1 hK'C hK1
  rw [hA, hB]
  have h8 : Nat.card R₁ = 8 :=
    (CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC).card8 _ hK R₁ hR₁
  have h8' : Nat.card R₁' = 8 :=
    (CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC).card8 _ hc.std.hK'.1 R₁' hR₁'
  have hP2 : IsPGroup 2 R₁ := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  have hP2' : IsPGroup 2 R₁' := IsPGroup.of_card (n := 3) (by rw [h8']; norm_num)
  have hu1 : IsUniqueInvolution R₁ t :=
    ⟨ob₁ ▸ R₁.mul_mem hb₁R hb₁R, hz.ne_one, hz.sq, fun y hy h => hz.unique y (hR₁.1 hy) h⟩
  have hu1' : IsUniqueInvolution R₁' t :=
    ⟨ob' ▸ R₁'.mul_mem hb'R' hb'R', hz.ne_one, hz.sq, fun y hy h => hz'.unique y (hR₁'.1 hy) h⟩
  have hnab : ∀ (P : Subgroup Y) (b : Y), IsSylow2In P (tightCore R) ∨ IsSylow2In P K' →
      b ∈ P → b * b = t → ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
    intro P b hP hbP hbb
    obtain ⟨φ⟩ : Nonempty (↥P ≃* QuaternionGroup 2) := by
      rcases hP with hP | hP
      · exact members_sylow_q8 hc.std.perp _ hK P hP
      · exact members_sylow_q8 hc.std.perp _ hc.std.hK'.1 P hP
    obtain ⟨y, hyP, hyb⟩ := F7O.q8_exists_inv_conj φ hbP (by rw [hbb]; exact hz.ne_one)
    refine ⟨y, hyP, b, hbP, fun h => hz.ne_one ?_⟩
    have : b⁻¹ = b := by rw [← hyb, h, mul_inv_cancel_right]
    rw [← hbb]
    calc b * b = b⁻¹ * b := by rw [this]
      _ = 1 := inv_mul_cancel b
  obtain ⟨qA, h8A, nA⟩ := F7I.q8_image hR₁C (le_centralizer_of_unique hz hz.mem) hu1 h8
    (hnab R₁ b₁ (Or.inl hR₁) hb₁R ob₁)
  obtain ⟨qB, h8B, nB⟩ := F7I.q8_image hR₁'C (le_centralizer_of_unique hz hz.mem) hu1' h8'
    (hnab R₁' b' (Or.inr hR₁') hb'R' ob')
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hR₁D.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR₁'D.2.trans hNe
  have hecomm : ∀ P : Subgroup Y, P ≤ Subgroup.centralizer ({e} : Set Y) →
      ∀ x ∈ (P.subgroupOf C).map (F7I.piC C), F7I.piC C ⟨e, heC⟩ * x = x * F7I.piC C ⟨e, heC⟩ := by
    intro P hP x hx
    obtain ⟨y, hy, rfl⟩ := F7I.mem_map_piC.mp hx
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hP hy)).symm
  have hne : ∀ (P : Subgroup Y) (b : Y) (hb : b ∈ P) (hbC : b ∈ C), IsPGroup 2 P → t ∈ P →
      b * b = t → F7I.piC C ⟨b, hbC⟩ ≠ 1 ∧ F7I.piC C ⟨b, hbC⟩ ≠ F7I.piC C ⟨t, htC⟩ := by
    intro P b hb hbC hP htP hbb
    constructor
    · intro h
      rw [← map_one (F7I.piC C)] at h
      have := congrArg Subtype.val (F7I.piC_inj hP hb P.one_mem h)
      apply hz.ne_one
      rw [← hbb]
      simp only [OneMemClass.coe_one] at this
      rw [this, one_mul]
    · intro h
      have := congrArg Subtype.val (F7I.piC_inj hP hb htP h)
      apply hz.ne_one
      simp only at this
      have h' : t * t = t := by rw [← this] at hbb ⊢; exact hbb
      calc t = t * t * t⁻¹ := by group
        _ = 1 := by rw [h', mul_inv_cancel]
  obtain ⟨n1, n2⟩ := hne R₁ b₁ hb₁R (hR₁C hb₁R) hP2 hu1.mem ob₁
  obtain ⟨n1', n2'⟩ := hne R₁' b' hb'R' (hR₁'C hb'R') hP2' hu1'.mem ob'
  refine ⟨qA, qB, h8A, h8B, nA, nB, ?_, hecomm R₁ hR₁e, hecomm R₁' hR₁'e,
    ⟨b₁, hR₁C hb₁R⟩, ⟨b', hR₁'C hb'R'⟩, hub.symm, F7I.mem_map_piC.mpr ⟨_, hb₁R, rfl⟩,
    F7I.mem_map_piC.mpr ⟨_, hb'R', rfl⟩, n1, n2, n1', n2'⟩
  intro x hx y hy
  obtain ⟨x', hx', rfl⟩ := F7I.mem_map_piC.mp hx
  obtain ⟨y', hy', rfl⟩ := F7I.mem_map_piC.mp hy
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcomm _ hx' _ hy')

end E7E

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
