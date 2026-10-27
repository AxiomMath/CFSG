module

public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrTri
public import CFSG.ClassicalInvolution.Q3.TL4OddFrLinkP
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Lay

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AlphaFr

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)
open CFSG.ClassicalInvolution.Q3.TL4

section Gen

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_lift_centralizer (hcl : ConjInvariant Ω) {c : G} (hc : c ∈ layerY Ω x)
    (hc2 : c * c = 1) {u : SecQuot Ω x}
    (hu : u ∈ Subgroup.centralizer
      ({QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨c, hc⟩} :
        Set (SecQuot Ω x))) :
    ∃ w : ↥(layerY Ω x), (w : G) ∈ Subgroup.centralizer ({c} : Set G) ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) w = u := by
  have hcx : c ∈ Subgroup.centralizer ({x} : Set G) := layerY_le_centralizer hc
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective u
  have hyk : c * (w₀ : G) * c⁻¹ ∈ layerY Ω x :=
    (layerY Ω x).mul_mem ((layerY Ω x).mul_mem hc w₀.2) ((layerY Ω x).inv_mem hc)
  have hfix : secAct hcl hcx (w₀ : SecQuot Ω x) = (w₀ : SecQuot Ω x) := by
    have e := s26Act_mk (layerY Ω x) ⟨c, mem_normalizer_layerY hcl hcx⟩ w₀
      ⟨c * (w₀ : G) * c⁻¹, hyk⟩ rfl
    refine e.trans ?_
    have e2 : (⟨c * (w₀ : G) * c⁻¹, hyk⟩ : ↥(layerY Ω x)) = ⟨c, hc⟩ * w₀ * ⟨c, hc⟩⁻¹ := rfl
    rw [e2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hu' := Subgroup.mem_centralizer_singleton_iff.mp hu
    rw [QuotientGroup.mk'_apply] at hu'
    rw [← hu', mul_inv_cancel_right]
  obtain ⟨w, hw, hwe⟩ := exists_fixed_lift_sec hcl hcx hc2 _ hfix
  refine ⟨w, ?_, hwe⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc (w : G) * c = (c * (w : G) * c⁻¹) * c := by rw [hw]
    _ = c * w := by group

theorem layerY_le_of_linkGen (hcl : ConjInvariant Ω) {H : Subgroup G}
    (hO : oddCoreOf (layerY Ω x) ≤ H) {a b : G} (ha : a ∈ layerY Ω x) (hb : b ∈ layerY Ω x)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (hHa : Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ≤ H)
    (hHb : Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ≤ H)
    (hHab : Subgroup.centralizer ({a * b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ≤ H)
    (hgen : Subgroup.centralizer
        ({QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨a, ha⟩} :
          Set (SecQuot Ω x)) ⊔
      Subgroup.centralizer
        ({QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨b, hb⟩} :
          Set (SecQuot Ω x)) ⊔
      Subgroup.centralizer
        ({QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨a, ha⟩ *
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨b, hb⟩} :
          Set (SecQuot Ω x)) = ⊤) :
    layerY Ω x ≤ H := by
  have key : ∀ (c : G) (hc : c ∈ layerY Ω x), c * c = 1 →
      Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ≤ H →
      (Subgroup.centralizer
        ({QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨c, hc⟩} :
          Set (SecQuot Ω x)) : Set (SecQuot Ω x)) ⊆ (secImage Ω x H : Set (SecQuot Ω x)) := by
    intro c hc hc2 hcH u hu
    obtain ⟨w, hw, rfl⟩ := exists_lift_centralizer hcl hc hc2 hu
    refine ⟨w, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact hcH ⟨hw, layerY_le_centralizer w.2⟩
  have hab2 : (a * b) * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have habY : a * b ∈ layerY Ω x := (layerY Ω x).mul_mem ha hb
  have e : QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨a * b, habY⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨a, ha⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨b, hb⟩ := by
    rw [← map_mul]
    rfl
  refine layerY_le_of_closure hO
    ((Subgroup.centralizer
        ({QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨a, ha⟩} :
          Set (SecQuot Ω x)) : Set (SecQuot Ω x)) ∪
      (Subgroup.centralizer
        ({QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨b, hb⟩} :
          Set (SecQuot Ω x)) : Set (SecQuot Ω x)) ∪
      (Subgroup.centralizer
        ({QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨a, ha⟩ *
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨b, hb⟩} :
          Set (SecQuot Ω x)) : Set (SecQuot Ω x))) ?_ ?_
  · rintro u ((hu | hu) | hu)
    · exact key a ha ha2 hHa hu
    · exact key b hb hb2 hHb hu
    · rw [← e] at hu
      exact key (a * b) habY hab2 hHab hu
  · rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq,
      Subgroup.closure_eq]
    exact hgen

theorem t4Hyp_secFam {r : ℕ} (h : TypeRFam r Ω) : T4Hyp r (SecQuot Ω x) (secFam Ω x) where
  hyp := (h.secFam (x := x)).hyp
  twoGroup := (h.secFam (x := x)).twoGroup
  quat := (h.secFam (x := x)).quat
  tight := (h.secFam (x := x)).tight
  noTwins := fun J hJ J' hJ' u hu hu' =>
    ((h.secFam (x := x)).noTwins J hJ J' ⟨hJ', u, hu, hu'⟩).symm
  aEmpty := aEmpty_secFam h
  odd := secQuot_oddCore_eq_bot

end Gen

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}

theorem oddCoreOf_layerY_le_normalizer (hH : TightHyp51TriR r n)
    (hL : TightLargeHypR r n Y Rd Sd z) {A B : Subgroup Y} {a b : Y}
    (hA : A ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hB : B ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hAB : B ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) A)
    (ha : IsUniqueInvolution A a) (hb : IsUniqueInvolution B b)
    (hind : b ∉ Subgroup.closure ({z, a} : Set Y)) :
    oddCoreOf (layerY (CoreAssembly.conjClass (tightCore Rd)) z) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({a, z} : Set Y)) : Set Y) := by
  obtain ⟨-, hnorm⟩ := alpha_of_triangle hH hL hA hB hAB ha hb hind
  have hzB : z ∈ Subgroup.closure ({z, a, b} : Set Y) := Subgroup.subset_closure (by simp)
  exact (oddCoreOf_layerY_le hL.datum.hypOmegaGen.conjInvariant).trans (hnorm z hzB)

theorem natCard_secQuot_lt_of_large (hL : TightLargeHypR r n Y Rd Sd z) :
    Nat.card (SecQuot (CoreAssembly.conjClass (tightCore Rd)) z) < n := by
  have hz := hL.datum.isUniqueInvolution_core
  have hx : ∃ g : Y, g * z ≠ z * g := by
    by_contra hcon
    have hzc : z ∈ Subgroup.center Y :=
      Subgroup.mem_center_iff.mpr fun g => by
        by_contra h
        exact hcon ⟨g, h⟩
    rw [hL.center, Subgroup.mem_bot] at hzc
    exact hz.ne_one hzc
  exact (natCard_secQuot_lt (Ω := CoreAssembly.conjClass (tightCore Rd)) hx).trans_eq hL.card

theorem exists_conj_of_not_dConnected (h4 : Thm4RBelow r n) (hL : TightLargeHypR r n Y Rd Sd z)
    (hnc : ¬ DConnected (coreLinkFam Rd z))
    {Jb Mb : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) z)}
    (hJ : Jb ∈ coreLinkFam Rd z) (hM : Mb ∈ coreLinkFam Rd z) :
    ∃ g, conjSub g Jb = Mb := by
  have h := TightLargeHypR.typeRFam hL
  have hT := t4Hyp_secFam (x := z) h
  have hn := natCard_secQuot_lt_of_large hL
  have hadj : ∀ {P Q}, P ∈ coreLinkFam Rd z → Q ∈ coreLinkFam Rd z →
      (¬ ∃ g, conjSub g P = Q) → dAdj (coreLinkFam Rd z) P Q := by
    intro P Q hP hQ hPQ
    have hc := h4 _ hn _ hT P (coreLinkFam_subset hL hP) Q (coreLinkFam_subset hL hQ) hPQ
    have hne : Q ≠ P := fun e => hPQ ⟨1, by rw [conjSub_one, e]⟩
    exact Or.inl (mem_omegaNbr_of_commutes hQ hne hc)
  have hsymm : ∀ {P Q : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) z)},
      (∃ g, conjSub g P = Q) → ∃ g, conjSub g Q = P := by
    rintro P Q ⟨g, rfl⟩
    exact ⟨g⁻¹, by rw [conjSub_inv_conjSub]⟩
  have htrans : ∀ {P Q R : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) z)},
      (∃ g, conjSub g P = Q) → (∃ g, conjSub g Q = R) → ∃ g, conjSub g P = R := by
    rintro P Q R ⟨g, rfl⟩ ⟨g', rfl⟩
    exact ⟨g' * g, by rw [conjSub_mul]⟩
  by_contra hne
  apply hnc
  have step : ∀ {P}, P ∈ coreLinkFam Rd z → Relation.ReflTransGen
      (fun M N => N ∈ coreLinkFam Rd z ∧ dAdj (coreLinkFam Rd z) M N) Jb P := by
    intro P hP
    by_cases hc : ∃ g, conjSub g Jb = P
    · have hMP : ¬ ∃ g, conjSub g Mb = P := fun h' => hne (htrans hc (hsymm h'))
      exact (Relation.ReflTransGen.single ⟨hM, hadj hJ hM hne⟩).tail ⟨hP, hadj hM hP hMP⟩
    · exact Relation.ReflTransGen.single ⟨hP, hadj hJ hP hc⟩
  have step' : ∀ {P}, P ∈ coreLinkFam Rd z → Relation.ReflTransGen
      (fun M N => N ∈ coreLinkFam Rd z ∧ dAdj (coreLinkFam Rd z) M N) P Jb := by
    intro P hP
    by_cases hc : ∃ g, conjSub g P = Jb
    · have hPM : ¬ ∃ g, conjSub g P = Mb := fun h' => hne (htrans (hsymm hc) h')
      have hMJ : ¬ ∃ g, conjSub g Mb = Jb := fun h' => hne (hsymm h')
      exact (Relation.ReflTransGen.single ⟨hM, hadj hP hM hPM⟩).tail ⟨hJ, hadj hM hJ hMJ⟩
    · exact Relation.ReflTransGen.single ⟨hJ, hadj hP hJ hc⟩
  exact fun P hP Q hQ => (step' hP).trans (step hQ)

theorem conjClass_secImg_eq (hL : TightLargeHypR r n Y Rd Sd z) {A : Subgroup Y}
    (hA : A ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hone : ∀ Mb ∈ coreLinkFam Rd z,
      ∃ g, conjSub g (secImg (CoreAssembly.conjClass (tightCore Rd)) z A) = Mb) :
    CoreAssembly.conjClass (secImg (CoreAssembly.conjClass (tightCore Rd)) z A) =
      coreLinkFam Rd z := by
  ext Mb
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨conjSub (g' : Y) A, conjSub_mem_omegaNbr_core hL hA (layerY_le_centralizer g'.2),
      ?_⟩
    exact (conjSub_secImg g' A).symm
  · intro hMb
    obtain ⟨g, hg⟩ := hone Mb hMb
    exact ⟨g, hg⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.AlphaFr
