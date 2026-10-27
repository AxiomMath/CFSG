module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1245
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1111b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL34
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma119
public import CFSG.LocalAnalysis.GLTheoremB.PlaneAction
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Fix
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Main
import CFSG.LargeExtraspecial.S12TriG2
import CFSG.CharacterTheory.Burnside
import CFSG.GroupTheory.SmallOrderNotSimple
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FIa
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FCover
public import CFSG.HardMathSupport.Solomon.Proving.L34Cover
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate41501
public import Certificates.Certificate7233Base

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL34b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

section Conn

variable {G : Type} [Group G] [Finite G]

theorem cent_symm {A B : Subgroup G} (h : A ≤ Subgroup.centralizer (B : Set G)) :
    B ≤ Subgroup.centralizer (A : Set G) :=
  fun b hb => Subgroup.mem_centralizer_iff.2 fun a ha =>
    (Subgroup.mem_centralizer_iff.1 (h ha) b hb).symm

theorem cent_of_le_elem {A B E : Subgroup G} (hE : IsElemAbelian 3 E) (hA : A ≤ E) (hB : B ≤ E) :
    A ≤ Subgroup.centralizer (B : Set G) :=
  fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => hE.comm (hB hb) (hA ha)

theorem exists_ek3 {X W : Subgroup G} (hWX : W ≤ X) (hW : IsElemAbelian 3 W)
    (h27 : 27 ≤ Nat.card W) : ∃ V : Subgroup G, IsEkIn 3 3 X V ∧ V ≤ W := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hW.isPGroup
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 3 ^ 3 ∣ Nat.card W := hk ▸ pow_dvd_pow 3 hk3
  obtain ⟨V, hVW, hVel, hVc⟩ := exists_le_isElemAbelian_card hW hdvd
  exact ⟨V, ⟨hVW.trans hWX, hVel, hVc⟩, hVW⟩

theorem kc_of_comm {X A B : Subgroup G} (hAX : A ≤ X) (hA : IsElemAbelian 3 A)
    (hA27 : 27 ≤ Nat.card A) (hBX : B ≤ X) (hB : IsElemAbelian 3 B) (hB27 : 27 ≤ Nat.card B)
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) : IsKConnectedIn 3 3 X A B :=
  ⟨hAX, hA, by norm_num; exact hA27, hBX, hB, by norm_num; exact hB27, Or.inl hAB⟩

theorem kc_of_le_elem {X A B E : Subgroup G} (hEX : E ≤ X) (hE : IsElemAbelian 3 E) (hAE : A ≤ E)
    (hBE : B ≤ E) (hA27 : 27 ≤ Nat.card A) (hB27 : 27 ≤ Nat.card B) : IsKConnectedIn 3 3 X A B :=
  kc_of_comm (hAE.trans hEX) (isElemAbelian_mono hE hAE) hA27 (hBE.trans hEX)
    (isElemAbelian_mono hE hBE) hB27 (cent_of_le_elem hE hAE hBE)

theorem step_symm {X U V : Subgroup G} (h : IsKConnStep 3 3 X U V) : IsKConnStep 3 3 X V U :=
  ⟨h.2.1, h.1, cent_symm h.2.2⟩

theorem kc_symm {X A B : Subgroup G} (h : IsKConnectedIn 3 3 X A B) : IsKConnectedIn 3 3 X B A := by
  obtain ⟨hAX, hA, hA27, hBX, hB, hB27, hc⟩ := h
  refine ⟨hBX, hB, hB27, hAX, hA, hA27, ?_⟩
  rcases hc with hc | ⟨U, V, hU, hV, hAU, hUV, hVB⟩
  · exact Or.inl (cent_symm hc)
  · exact Or.inr ⟨V, U, hV, hU, cent_symm hVB, input31_reflTransGen_symm (fun _ _ => step_symm) hUV,
      cent_symm hAU⟩

theorem kc_trans {X A B C : Subgroup G} (h₁ : IsKConnectedIn 3 3 X A B)
    (h₂ : IsKConnectedIn 3 3 X B C) : IsKConnectedIn 3 3 X A C := by
  obtain ⟨hAX, hA, hA27, hBX, hB, hB27, h1⟩ := h₁
  obtain ⟨-, -, -, hCX, hC, hC27, h2⟩ := h₂
  have hB27' : 27 ≤ Nat.card B := by norm_num at hB27; exact hB27
  obtain ⟨W, hW, hWB⟩ := exists_ek3 hBX hB hB27'
  refine ⟨hAX, hA, hA27, hCX, hC, hC27, Or.inr ?_⟩
  have hWC : ∀ {Y : Subgroup G}, B ≤ Subgroup.centralizer (Y : Set G) →
      W ≤ Subgroup.centralizer (Y : Set G) := fun h => hWB.trans h
  have hCW : ∀ {Y : Subgroup G}, Y ≤ Subgroup.centralizer (B : Set G) →
      Y ≤ Subgroup.centralizer (W : Set G) := fun h => h.trans (Subgroup.centralizer_le hWB)
  rcases h1 with h1 | ⟨U, V, hU, hV, hAU, hUV, hVB⟩ <;>
    rcases h2 with h2 | ⟨U', V', hU', hV', hBU', hUV', hVC'⟩
  · exact ⟨W, W, hW, hW, hCW h1, Relation.ReflTransGen.refl, hWC h2⟩
  · exact ⟨W, V', hW, hV', hCW h1, Relation.ReflTransGen.head ⟨hW, hU', hWC hBU'⟩ hUV', hVC'⟩
  · exact ⟨U, W, hU, hW, hAU, Relation.ReflTransGen.tail hUV ⟨hV, hW, hCW hVB⟩, hWC h2⟩
  · refine ⟨U, V', hU, hV', hAU, ?_, hVC'⟩
    exact (Relation.ReflTransGen.tail hUV ⟨hV, hW, hCW hVB⟩).trans
      (Relation.ReflTransGen.head ⟨hW, hU', hWC hBU'⟩ hUV')

end Conn

section Plane

variable {G : Type} [Group G] [Finite G]

theorem card_sup_mul_inf {A B : Subgroup G} (h : A ≤ Subgroup.centralizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B :=
  input31_card_sup_mul_card_inf h

theorem card_inf_le_three {U W : Subgroup G} (hU : Nat.card U = 9) (hUW : ¬ U ≤ W) :
    Nat.card (U ⊓ W : Subgroup G) ≤ 3 := by
  have hdvd : Nat.card (U ⊓ W : Subgroup G) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hU]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  interval_cases i
  · rw [he]; norm_num
  · rw [he]; norm_num
  · exfalso
    apply hUW
    have heq : U ⊓ W = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hU, he]; norm_num)
    exact heq ▸ inf_le_right

theorem kc_plane_pair {X P U₁ U₂ A : Subgroup G} (hPX : P ≤ X) (hP : IsPGroup 3 P)
    (hU₁ : IsPPlane 3 U₁) (hU₂ : IsPPlane 3 U₂) (hU₁P : U₁ ≤ P) (hU₂P : U₂ ≤ P)
    (hN₁ : P ≤ Subgroup.normalizer (U₁ : Set G)) (hN₂ : P ≤ Subgroup.normalizer (U₂ : Set G))
    (hne : U₁ ≠ U₂) (hc : U₁ ≤ Subgroup.centralizer (U₂ : Set G)) (hA : IsEkIn 3 4 P A) :
    IsKConnectedIn 3 3 X A (U₁ ⊔ U₂) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hAP, hAel, hAc⟩ := hA
  have hU₁c : Nat.card U₁ = 9 := by rw [hU₁.2]; norm_num
  have hU₂c : Nat.card U₂ = 9 := by rw [hU₂.2]; norm_num
  rw [show (3 : ℕ) ^ 4 = 81 by norm_num] at hAc
  set C₁ : Subgroup G := A ⊓ Subgroup.centralizer (U₁ : Set G) with hC₁
  have hC₁le : Nat.card A ≤ 3 * Nat.card C₁ := card_le_mul_card_inf_centralizer hP hU₁ hU₁P hN₁ hAP
  have hC₁el : IsElemAbelian 3 C₁ := isElemAbelian_mono hAel inf_le_left
  have hC₁27 : 27 ≤ Nat.card C₁ := by omega
  have hC₁U : C₁ ≤ Subgroup.centralizer (U₁ : Set G) := inf_le_right
  set B₁ : Subgroup G := U₁ ⊔ C₁ with hB₁
  have hB₁el : IsElemAbelian 3 B₁ := isElemAbelian_sup_of_commute hU₁.1 hC₁el (cent_symm hC₁U)
  have hB₁P : B₁ ≤ P := sup_le hU₁P (inf_le_left.trans hAP)
  have hB₁81 : 81 ≤ Nat.card B₁ := by
    have h := card_sup_mul_inf (cent_symm hC₁U)
    rw [hU₁c] at h
    have hpos : 0 < Nat.card (U₁ ⊓ C₁ : Subgroup G) := Nat.card_pos
    by_cases hUC : U₁ ≤ C₁
    · have hAC : Nat.card C₁ = 81 := by
        have hCA : C₁ = A := by
          refine le_antisymm inf_le_left fun a ha => ⟨ha, ?_⟩
          exact Subgroup.mem_centralizer_iff.2 fun u hu => hAel.comm (hUC hu).1 ha
        rw [hCA, hAc]
      have hle : Nat.card (U₁ ⊓ C₁ : Subgroup G) ≤ 9 := hU₁c ▸ Subgroup.card_le_of_le inf_le_left
      rw [hAC] at h
      nlinarith
    · have hle := card_inf_le_three hU₁c hUC
      nlinarith
  set C₂ : Subgroup G := B₁ ⊓ Subgroup.centralizer (U₂ : Set G) with hC₂
  have hC₂le : Nat.card B₁ ≤ 3 * Nat.card C₂ :=
    card_le_mul_card_inf_centralizer hP hU₂ hU₂P hN₂ hB₁P
  have hC₂el : IsElemAbelian 3 C₂ := isElemAbelian_mono hB₁el inf_le_left
  have hC₂27 : 27 ≤ Nat.card C₂ := by omega
  have hC₂U : C₂ ≤ Subgroup.centralizer (U₂ : Set G) := inf_le_right
  set B₂ : Subgroup G := U₂ ⊔ C₂ with hB₂
  have hB₂el : IsElemAbelian 3 B₂ := isElemAbelian_sup_of_commute hU₂.1 hC₂el (cent_symm hC₂U)
  have hB₂P : B₂ ≤ P := sup_le hU₂P (inf_le_left.trans hB₁P)
  have hU₁C₂ : U₁ ≤ C₂ := le_inf le_sup_left hc
  have hUU : U₁ ⊔ U₂ ≤ B₂ := sup_le (hU₁C₂.trans le_sup_right) le_sup_left
  have hUU27 : 27 ≤ Nat.card (U₁ ⊔ U₂ : Subgroup G) := by
    have h := card_sup_mul_inf hc
    rw [hU₁c, hU₂c] at h
    have hnle : ¬ U₁ ≤ U₂ := fun hle =>
      hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hU₁c, hU₂c]))
    have hle := card_inf_le_three hU₁c hnle
    have hpos : 0 < Nat.card (U₁ ⊓ U₂ : Subgroup G) := Nat.card_pos
    nlinarith
  have hA27 : 27 ≤ Nat.card A := by omega
  have hB₁27 : 27 ≤ Nat.card B₁ := by omega
  have hB₂27 : 27 ≤ Nat.card B₂ := le_trans hC₂27 (Subgroup.card_le_of_le le_sup_right)
  have h1 : IsKConnectedIn 3 3 X A C₁ :=
    kc_of_le_elem (hAP.trans hPX) hAel le_rfl inf_le_left hA27 hC₁27
  have h2 : IsKConnectedIn 3 3 X C₁ B₁ :=
    kc_of_le_elem (hB₁P.trans hPX) hB₁el le_sup_right le_rfl hC₁27 hB₁27
  have h3 : IsKConnectedIn 3 3 X B₁ C₂ :=
    kc_of_le_elem (hB₁P.trans hPX) hB₁el le_rfl inf_le_left hB₁27 hC₂27
  have h4 : IsKConnectedIn 3 3 X C₂ B₂ :=
    kc_of_le_elem (hB₂P.trans hPX) hB₂el le_sup_right le_rfl hC₂27 hB₂27
  have h5 : IsKConnectedIn 3 3 X B₂ (U₁ ⊔ U₂) :=
    kc_of_le_elem (hB₂P.trans hPX) hB₂el le_rfl hUU hB₂27 hUU27
  exact kc_trans h1 (kc_trans h2 (kc_trans h3 (kc_trans h4 h5)))

theorem kc_of_plane_pair {X P U₁ U₂ : Subgroup G} (hPX : P ≤ X) (hP : IsPGroup 3 P)
    (hU₁ : IsPPlane 3 U₁) (hU₂ : IsPPlane 3 U₂) (hU₁P : U₁ ≤ P) (hU₂P : U₂ ≤ P)
    (hN₁ : P ≤ Subgroup.normalizer (U₁ : Set G)) (hN₂ : P ≤ Subgroup.normalizer (U₂ : Set G))
    (hne : U₁ ≠ U₂) (hc : U₁ ≤ Subgroup.centralizer (U₂ : Set G)) {A B : Subgroup G}
    (hA : IsEkIn 3 4 P A) (hB : IsEkIn 3 4 P B) : IsKConnectedIn 3 3 X A B :=
  kc_trans (kc_plane_pair hPX hP hU₁ hU₂ hU₁P hU₂P hN₁ hN₂ hne hc hA)
    (kc_symm (kc_plane_pair hPX hP hU₁ hU₂ hU₁P hU₂P hN₁ hN₂ hne hc hB))

end Plane

section Jordan

variable {G : Type} [Group G] [Finite G]

theorem card_range_le_ker_mul {A B C : Type*} [Group A] [Group B] [Group C] [Finite B]
    (f : A →* B) (g : B →* C) : Nat.card f.range ≤ Nat.card g.ker * Nat.card (g.comp f).range := by
  set h : ↥f.range →* C := g.comp f.range.subtype with hh
  have h1 : Nat.card f.range = Nat.card h.ker * Nat.card h.range :=
    CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range h
  have h2 : h.range = (g.comp f).range := by
    ext c
    constructor
    · rintro ⟨⟨b, ⟨a, rfl⟩⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨f a, ⟨a, rfl⟩⟩, rfl⟩
  have h3 : Nat.card h.ker ≤ Nat.card g.ker := by
    have hle : h.ker.map f.range.subtype ≤ g.ker := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy
    calc Nat.card h.ker = Nat.card (h.ker.map f.range.subtype) :=
          (Subgroup.card_map_of_injective f.range.subtype_injective).symm
      _ ≤ Nat.card g.ker := Subgroup.card_le_of_le hle
  rw [h1, h2]
  exact Nat.mul_le_mul_right _ h3

theorem card_le_cube_cent {E : Subgroup G} (hE : IsElemAbelian 3 E) {x : G} (hx3 : x ^ 3 = 1)
    (hxN : x ∈ Subgroup.normalizer (E : Set G)) :
    Nat.card E ≤ Nat.card (E ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ^ 3 := by
  have hconj : ∀ e ∈ E, x * e * x⁻¹ ∈ E := fun e he => (Subgroup.mem_normalizer_iff.1 hxN e).1 he
  let ψ : ↥E →* ↥E :=
    { toFun := fun e => ⟨(e : G)⁻¹ * (x * e * x⁻¹), E.mul_mem (E.inv_mem e.2) (hconj _ e.2)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have ha' := hconj _ a.2
        have hc : (b : G)⁻¹ * ((a : G)⁻¹ * (x * a * x⁻¹)) = ((a : G)⁻¹ * (x * a * x⁻¹)) * (b : G)⁻¹ :=
          hE.comm (E.inv_mem b.2) (E.mul_mem (E.inv_mem a.2) ha')
        calc ((a : G) * b)⁻¹ * (x * (a * b) * x⁻¹)
            = (b : G)⁻¹ * ((a : G)⁻¹ * (x * a * x⁻¹)) * (x * b * x⁻¹) := by group
          _ = ((a : G)⁻¹ * (x * a * x⁻¹)) * (b : G)⁻¹ * (x * b * x⁻¹) := by rw [hc]
          _ = (a : G)⁻¹ * (x * a * x⁻¹) * ((b : G)⁻¹ * (x * b * x⁻¹)) := by group }
  have hψ : ∀ e : ↥E, ((ψ e : ↥E) : G) = (e : G)⁻¹ * (x * e * x⁻¹) := fun _ => rfl
  have hker : ψ.ker.map E.subtype = E ⊓ Subgroup.centralizer ({x} : Set G) := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨e, he, rfl⟩
      have h1 := congrArg Subtype.val he
      rw [hψ, OneMemClass.coe_one] at h1
      refine ⟨e.2, ?_⟩
      have h2 : x * (e : G) * x⁻¹ = e := by
        calc x * (e : G) * x⁻¹ = (e : G) * ((e : G)⁻¹ * (x * e * x⁻¹)) := by group
          _ = e := by rw [h1, mul_one]
      have h3 : x * (e : G) = (e : G) * x := by
        calc x * (e : G) = (x * (e : G) * x⁻¹) * x := by group
          _ = e * x := by rw [h2]
      exact h3.symm
    · rintro ⟨hgE, hgx⟩
      refine ⟨⟨g, hgE⟩, Subtype.ext ?_, rfl⟩
      rw [hψ, OneMemClass.coe_one]
      show g⁻¹ * (x * g * x⁻¹) = 1
      rw [← hgx]
      group
  have hkc : Nat.card ψ.ker = Nat.card (E ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
    rw [← hker, Subgroup.card_map_of_injective E.subtype_injective]
  have hψ2 : (ψ.comp ψ).range ≤ ψ.ker := by
    rintro _ ⟨e, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [OneMemClass.coe_one, hψ, MonoidHom.comp_apply, hψ, hψ]
    set a : G := (e : G)
    have haE : a ∈ E := e.2
    set b : G := x * a * x⁻¹
    have hbE : b ∈ E := hconj a haE
    set c : G := x * b * x⁻¹
    have hcE : c ∈ E := hconj b hbE
    have hxc : x * c * x⁻¹ = a := by
      have h3 : x * (x * x) = 1 := by rw [← pow_three]; exact hx3
      calc x * c * x⁻¹ = (x * (x * x)) * a * (x * (x * x))⁻¹ := by simp only [c, b]; group
        _ = a := by rw [h3]; group
    have hb3 : b ^ 3 = 1 := hE.2 b hbE
    have hc3 : c ^ 3 = 1 := hE.2 c hcE
    have hbb : b⁻¹ * b⁻¹ = b := by
      calc b⁻¹ * b⁻¹ = b⁻¹ * b⁻¹ * b ^ 3 := by rw [hb3, mul_one]
        _ = b := by group
    have hcc : c⁻¹ * c⁻¹ = c := by
      calc c⁻¹ * c⁻¹ = c⁻¹ * c⁻¹ * c ^ 3 := by rw [hc3, mul_one]
        _ = c := by group
    have h1 : b⁻¹ * a = a * b⁻¹ := hE.comm (E.inv_mem hbE) haE
    have h2 : c⁻¹ * b = b * c⁻¹ := hE.comm (E.inv_mem hcE) hbE
    have h3 : (b * c) * a = a * (b * c) := hE.comm (E.mul_mem hbE hcE) haE
    have hL : (a⁻¹ * b)⁻¹ * (x * (a⁻¹ * b) * x⁻¹) = a * b * c := by
      have e1 : x * (a⁻¹ * b) * x⁻¹ = b⁻¹ * c := by simp only [c, b]; group
      rw [e1]
      calc (a⁻¹ * b)⁻¹ * (b⁻¹ * c) = b⁻¹ * a * b⁻¹ * c := by group
        _ = a * (b⁻¹ * b⁻¹) * c := by rw [h1]; group
        _ = a * b * c := by rw [hbb]
    have hR : x * (a * b * c) * x⁻¹ = a * b * c := by
      have e2 : x * (a * b * c) * x⁻¹ = b * c * (x * c * x⁻¹) := by simp only [c, b]; group
      rw [e2, hxc]
      calc b * c * a = a * (b * c) := h3
        _ = a * b * c := by group
    have hxe : x * ((a⁻¹ * b)⁻¹ * (x * (a⁻¹ * b) * x⁻¹)) * x⁻¹ =
        (a⁻¹ * b)⁻¹ * (x * (a⁻¹ * b) * x⁻¹) := by rw [hL, hR]
    calc ((a⁻¹ * b)⁻¹ * (x * (a⁻¹ * b) * x⁻¹))⁻¹ *
          (x * ((a⁻¹ * b)⁻¹ * (x * (a⁻¹ * b) * x⁻¹)) * x⁻¹)
        = ((a⁻¹ * b)⁻¹ * (x * (a⁻¹ * b) * x⁻¹))⁻¹ * ((a⁻¹ * b)⁻¹ * (x * (a⁻¹ * b) * x⁻¹)) := by
          rw [hxe]
      _ = 1 := inv_mul_cancel _
  have hc1 : Nat.card ↥E = Nat.card ψ.ker * Nat.card ψ.range :=
    CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range ψ
  have hc2 := card_range_le_ker_mul ψ ψ
  have hc3 : Nat.card (ψ.comp ψ).range ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hψ2
  have hEc : Nat.card E = Nat.card ↥E := rfl
  rw [hEc, hc1, ← hkc]
  calc Nat.card ψ.ker * Nat.card ψ.range ≤ Nat.card ψ.ker * (Nat.card ψ.ker * Nat.card ψ.ker) :=
        Nat.mul_le_mul_left _ (hc2.trans (Nat.mul_le_mul_left _ hc3))
    _ = Nat.card ψ.ker ^ 3 := by ring

theorem exists_central_of_normalized {T N : Subgroup G} (hT : IsPGroup 3 T) (hNT : N ≤ T)
    (hN : T ≤ Subgroup.normalizer (N : Set G)) (hne : N ≠ ⊥) :
    ∃ z ∈ N, z ≠ 1 ∧ z ^ 3 = 1 ∧ ∀ t ∈ T, t * z = z * t := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnil : Group.IsNilpotent T := hT.isNilpotent
  set H := N.subgroupOf T with hH
  have hHn : H.Normal := ⟨fun r hr t => by
    rw [hH, Subgroup.mem_subgroupOf] at hr ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hN t.2) r).1 hr⟩
  have hH0 : H ≠ ⊥ := by
    intro h0
    apply hne
    rw [eq_bot_iff]
    intro r hr
    have : (⟨r, hNT hr⟩ : T) ∈ H := Subgroup.mem_subgroupOf.mpr hr
    rw [h0, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  have hHZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hH0
  have hHZp : IsPGroup 3 ↥(H ⊓ Subgroup.center T) := hT.to_subgroup _
  haveI : Nontrivial ↥(H ⊓ Subgroup.center T) := (Subgroup.nontrivial_iff_ne_bot _).2 hHZ
  obtain ⟨n, hn, hcard⟩ := hHZp.nontrivial_iff_card.1 inferInstance
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ Subgroup.center T)) 3
    (by rw [hcard]; exact dvd_pow_self 3 (by omega))
  have hwH : ((w : ↥T) : G) ∈ N := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 w.2).1
  have hwZ := (Subgroup.mem_inf.1 w.2).2
  have hword : orderOf ((w : ↥T) : G) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  refine ⟨((w : ↥T) : G), hwH, fun h => ?_, by rw [← hword]; exact pow_orderOf_eq_one _, fun t ht => ?_⟩
  · rw [h, orderOf_one] at hword
    norm_num at hword
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hwZ ⟨t, ht⟩)

theorem le_of_cube_ge {n m k : ℕ} (hn : n = 3 ^ k) (h : 3 ^ m ≤ n ^ 3) : 3 ^ ((m + 2) / 3) ≤ n := by
  subst hn
  rw [← pow_mul] at h
  have h' : m ≤ k * 3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem kc_of_big_normal {X R E A : Subgroup G} (hRX : R ≤ X) (hR : IsPGroup 3 R) (hER : E ≤ R)
    (hEN : R ≤ Subgroup.normalizer (E : Set G)) (hE : IsElemAbelian 3 E)
    (hE10 : 3 ^ 10 ≤ Nat.card E) (hA : IsEkIn 3 4 R A) : IsKConnectedIn 3 3 X A E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hAR, hAel, hAc⟩ := hA
  rw [show (3 : ℕ) ^ 4 = 81 by norm_num] at hAc
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE10
    norm_num at hE10
  obtain ⟨z, hzE, hz1, hz3, hzc⟩ := exists_central_of_normalized hR hER hEN hEne
  have hzA : ∀ y ∈ A, y * z = z * y := fun y hy => hzc y (hAR hy)
  set A' : Subgroup G := A ⊔ Subgroup.zpowers z with hA'
  have hzel := Claims1245.isElemAbelian_zpowers_of_pow_three hz3
  have hAzc : A ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact ((Commute.zpow_left (hzA y hy).symm i)).eq
  have hA'el : IsElemAbelian 3 A' := isElemAbelian_sup_of_commute hAel hzel hAzc
  have hA'R : A' ≤ R := sup_le hAR (Subgroup.zpowers_le.2 (hER hzE))
  have hz' : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz3 hz1
  obtain ⟨a, haA, haZ⟩ : ∃ a ∈ A, a ∉ Subgroup.zpowers z := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show A ≤ Subgroup.zpowers z from h)
    omega
  set Z1 : Subgroup G := Subgroup.zpowers z ⊔ Subgroup.zpowers a with hZ1
  have hZ1A' : Z1 ≤ A' :=
    sup_le le_sup_right (Subgroup.zpowers_le.2 (le_sup_left (a := A) haA))
  have ha3 : a ^ 3 = 1 := hAel.2 a haA
  have hZ1c : Nat.card Z1 = 9 := by
    have := CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (Subgroup.zpowers z)
      ha3 haZ (fun e he => hA'el.comm (le_sup_right (a := A) he) (le_sup_left (a := A) haA))
    rw [this, hz']
  obtain ⟨b, hbA, hbZ⟩ : ∃ b ∈ A, b ∉ Z1 := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show A ≤ Z1 from h)
    omega
  set A₁ : Subgroup G := Z1 ⊔ Subgroup.zpowers b with hA₁
  have hb3 : b ^ 3 = 1 := hAel.2 b hbA
  have hA₁A' : A₁ ≤ A' := sup_le hZ1A' (Subgroup.zpowers_le.2 (le_sup_left (a := A) hbA))
  have hA₁c : Nat.card A₁ = 27 := by
    have := CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three Z1 hb3 hbZ
      (fun e he => hA'el.comm (hZ1A' he) (le_sup_left (a := A) hbA))
    rw [this, hZ1c]
  have hA₁el : IsElemAbelian 3 A₁ := isElemAbelian_mono hA'el hA₁A'
  have haN : a ∈ Subgroup.normalizer (E : Set G) := hEN (hAR haA)
  have hbN : b ∈ Subgroup.normalizer (E : Set G) := hEN (hAR hbA)
  set Ea : Subgroup G := E ⊓ Subgroup.centralizer ({a} : Set G) with hEa
  have hEael : IsElemAbelian 3 Ea := isElemAbelian_mono hE inf_le_left
  have hJa := card_le_cube_cent hE ha3 haN
  have hab : a * b = b * a := hAel.comm haA hbA
  have hbNa : b ∈ Subgroup.normalizer (Ea : Set G) := by
    have hbC : b ∈ Subgroup.normalizer
        ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2 hab.symm)
    rw [Subgroup.mem_normalizer_iff] at hbN hbC ⊢
    intro h
    rw [hEa, Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (hbN h) (hbC h)
  have hJb := card_le_cube_cent hEael hb3 hbNa
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hEael.isPGroup)
  have hEa4 : 3 ^ 4 ≤ Nat.card Ea := by
    have := le_of_cube_ge hk (hE10.trans hJa)
    simpa using this
  set Eab : Subgroup G := Ea ⊓ Subgroup.centralizer ({b} : Set G) with hEab
  have hEabel : IsElemAbelian 3 Eab := isElemAbelian_mono hEael inf_le_left
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (hEabel.isPGroup)
  have hEab2 : 3 ^ 2 ≤ Nat.card Eab := by
    have := le_of_cube_ge hj (hEa4.trans hJb)
    simpa using this
  obtain ⟨W, hWEab, hWel, hWc⟩ := exists_le_isElemAbelian_card hEabel
    (show 3 ^ 2 ∣ Nat.card Eab by rw [hj]; exact pow_dvd_pow 3 (by
      by_contra hlt
      have : 3 ^ j < 3 ^ 2 := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega))
  have hWE : W ≤ E := hWEab.trans (inf_le_left.trans inf_le_left)
  have hWA₁ : A₁ ≤ Subgroup.centralizer (W : Set G) := by
    have hzW : z ∈ Subgroup.centralizer (W : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun w hw => hE.comm (hWE hw) hzE
    have haW : a ∈ Subgroup.centralizer (W : Set G) := Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hWEab hw).1.2)
    have hbW : b ∈ Subgroup.centralizer (W : Set G) := Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hWEab hw).2)
    exact sup_le (sup_le (Subgroup.zpowers_le.2 hzW) (Subgroup.zpowers_le.2 haW))
      (Subgroup.zpowers_le.2 hbW)
  obtain ⟨x, hxA₁, hxW⟩ : ∃ x ∈ A₁, x ∉ W := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show A₁ ≤ W from h)
    rw [hA₁c, hWc] at this
    norm_num at this
  have hx3 : x ^ 3 = 1 := hA₁el.2 x hxA₁
  set A₂ : Subgroup G := W ⊔ Subgroup.zpowers x with hA₂
  have hxWc : ∀ w ∈ W, w * x = x * w := fun w hw =>
    Subgroup.mem_centralizer_iff.1 (hWA₁ hxA₁) w hw
  have hA₂c : Nat.card A₂ = 27 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three W hx3 hxW hxWc, hWc]
    norm_num
  have hWzx : W ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (hxWc w hw).symm i).eq
  have hA₂el : IsElemAbelian 3 A₂ :=
    isElemAbelian_sup_of_commute hWel (Claims1245.isElemAbelian_zpowers_of_pow_three hx3) hWzx
  have hA₂R : A₂ ≤ R := sup_le (hWE.trans hER) (Subgroup.zpowers_le.2 (hA'R (hA₁A' hxA₁)))
  set Ex : Subgroup G := E ⊓ Subgroup.centralizer ({x} : Set G) with hEx
  have hExel : IsElemAbelian 3 Ex := isElemAbelian_mono hE inf_le_left
  have hJx := card_le_cube_cent hE hx3 (hEN (hA'R (hA₁A' hxA₁)))
  obtain ⟨l, hl⟩ := IsPGroup.iff_card.1 (hExel.isPGroup)
  have hEx27 : 27 ≤ Nat.card Ex := by
    have := le_of_cube_ge hl (hE10.trans hJx)
    have h4 : (3 : ℕ) ^ ((10 + 2) / 3) = 81 := by norm_num
    rw [h4] at this
    omega
  have h1 : IsKConnectedIn 3 3 X A A₁ :=
    kc_of_le_elem (hA'R.trans hRX) hA'el le_sup_left hA₁A' (by omega) (by omega)
  have h2 : IsKConnectedIn 3 3 X A₁ A₂ := by
    refine kc_of_comm ((hA₁A'.trans hA'R).trans hRX) hA₁el (by omega) (hA₂R.trans hRX) hA₂el
      (by omega) ?_
    refine cent_symm (sup_le ?_ ?_)
    · exact fun w hw => Subgroup.mem_centralizer_iff.2 fun y hy =>
        (Subgroup.mem_centralizer_iff.1 (hWA₁ hy) w hw).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      exact fun y hy => hA₁el.comm hy hxA₁
  have h3 : IsKConnectedIn 3 3 X A₂ Ex := by
    refine kc_of_comm (hA₂R.trans hRX) hA₂el (by omega) ((inf_le_left.trans hER).trans hRX) hExel
      hEx27 ?_
    refine sup_le ?_ ?_
    · exact cent_of_le_elem hE hWE inf_le_left
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      exact fun y hy => Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).2
  have h4 : IsKConnectedIn 3 3 X Ex E :=
    kc_of_le_elem (hER.trans hRX) hE inf_le_left le_rfl hEx27 (by omega)
  exact kc_trans h1 (kc_trans h2 (kc_trans h3 h4))

end Jordan

section ZBound

variable {Y : Type} [Group Y] [Finite Y]

open scoped commutatorElement

theorem pow_index_mem_comm (hperf : commutator Y = ⊤) (H : Subgroup Y) {z : Y}
    (hz : z ∈ Subgroup.center Y) : z ^ H.index ∈ ⁅H, H⁆ := by
  have key : ∀ (k : ℕ) (g₀ : Y), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    rw [Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hz k) g₀⁻¹, inv_mul_cancel_right]
  have h1 := MonoidHom.transfer_eq_pow (Abelianization.of : H →* Abelianization H) z key
  have h2 : z ∈ (Abelianization.of : H →* Abelianization H).transfer.ker :=
    Abelianization.commutator_subset_ker _ (by rw [hperf]; exact Subgroup.mem_top z)
  rw [MonoidHom.mem_ker, h1, ← MonoidHom.mem_ker, Abelianization.ker_of] at h2
  have h3 := Subgroup.mem_map_of_mem H.subtype h2
  rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h3

theorem comm_mul_left {x₁ x₂ w : Y} (h : ⁅x₂, w⁆ ∈ Subgroup.center Y) :
    ⁅x₁ * x₂, w⁆ = ⁅x₂, w⁆ * ⁅x₁, w⁆ := by
  have hc := Subgroup.mem_center_iff.1 h
  have e : x₂ * w * x₂⁻¹ = ⁅x₂, w⁆ * w := by rw [commutatorElement_def]; group
  calc ⁅x₁ * x₂, w⁆ = x₁ * (x₂ * w * x₂⁻¹) * x₁⁻¹ * w⁻¹ := by rw [commutatorElement_def]; group
    _ = x₁ * (⁅x₂, w⁆ * w) * x₁⁻¹ * w⁻¹ := by rw [e]
    _ = (x₁ * ⁅x₂, w⁆) * w * x₁⁻¹ * w⁻¹ := by group
    _ = (⁅x₂, w⁆ * x₁) * w * x₁⁻¹ * w⁻¹ := by rw [hc x₁]
    _ = ⁅x₂, w⁆ * ⁅x₁, w⁆ := by rw [commutatorElement_def x₁ w]; group

theorem comm_mul_right {x w₁ w₂ : Y} (h₂ : ⁅x, w₂⁆ ∈ Subgroup.center Y) :
    ⁅x, w₁ * w₂⁆ = ⁅x, w₁⁆ * ⁅x, w₂⁆ := by
  have hc₂ := Subgroup.mem_center_iff.1 h₂
  have e₁ : x * w₁ * x⁻¹ = ⁅x, w₁⁆ * w₁ := by rw [commutatorElement_def]; group
  have e₂ : x * w₂ * x⁻¹ = ⁅x, w₂⁆ * w₂ := by rw [commutatorElement_def]; group
  calc ⁅x, w₁ * w₂⁆ = (x * w₁ * x⁻¹) * (x * w₂ * x⁻¹) * w₂⁻¹ * w₁⁻¹ := by
        rw [commutatorElement_def]; group
    _ = ⁅x, w₁⁆ * w₁ * (⁅x, w₂⁆ * w₂) * w₂⁻¹ * w₁⁻¹ := by rw [e₁, e₂]
    _ = ⁅x, w₁⁆ * (w₁ * ⁅x, w₂⁆) * w₁⁻¹ := by group
    _ = ⁅x, w₁⁆ * (⁅x, w₂⁆ * w₁) * w₁⁻¹ := by rw [hc₂ w₁]
    _ = ⁅x, w₁⁆ * ⁅x, w₂⁆ := by group

theorem exists_comm_le_zpowers {P : Subgroup Y}
    (hcZ : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ Subgroup.center Y)
    (h9 : Nat.card (P.map (QuotientGroup.mk' (Subgroup.center Y))) ≤ 9)
    (h3 : ∀ x ∈ P, x ^ 3 ∈ Subgroup.center Y) :
    ∃ c : Y, c ^ 3 = 1 ∧ ⁅P, P⁆ ≤ Subgroup.zpowers c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.center Y with hZ
  set π := QuotientGroup.mk' Z with hπ
  by_cases hall : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ = 1
  · refine ⟨1, one_pow 3, ?_⟩
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [hall x hx y hy]
    exact Subgroup.one_mem _
  push Not at hall
  obtain ⟨a, haP, b, hbP, hab⟩ := hall
  set c := ⁅a, b⁆ with hc
  have hzc' : ∀ z ∈ Z, ∀ y : Y, ⁅y, z⁆ = 1 := fun z hz y => by
    rw [commutatorElement_def, Subgroup.mem_center_iff.1 hz y]; group
  have hzc : ∀ z ∈ Z, ∀ y : Y, ⁅z, y⁆ = 1 := fun z hz y => by
    rw [commutatorElement_def, ← Subgroup.mem_center_iff.1 hz y]; group
  have hpa : π a ≠ 1 := by
    intro h
    have haZ : a ∈ Z := (QuotientGroup.eq_one_iff a).1 h
    exact hab (hzc a haZ b)
  have hpb : π b ∉ Subgroup.zpowers (π a) := by
    rintro ⟨k, hk⟩
    have hk' : π (a ^ k) = π b := by rw [map_zpow]; exact hk
    have hz : (a ^ k)⁻¹ * b ∈ Z := QuotientGroup.eq.1 hk'
    apply hab
    have e : b = a ^ k * ((a ^ k)⁻¹ * b) := by group
    rw [hc, e, comm_mul_right (hcZ a haP _ (P.mul_mem (P.inv_mem (P.zpow_mem haP k)) hbP)),
      hzc' _ hz a, mul_one, commutatorElement_def]
    have : a * a ^ k = a ^ k * a := (Commute.self_zpow a k).eq
    rw [this]
    group
  set H : Subgroup Y := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hH
  have hHP : H ≤ P := sup_le (Subgroup.zpowers_le.2 haP) (Subgroup.zpowers_le.2 hbP)
  have hmapP : IsPGroup 3 (P.map π) := by
    intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hxg, ← map_pow, OneMemClass.coe_one,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h3 x hx
  have hHmap : H.map π = P.map π := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hHP) ?_
    have hp3 : IsPGroup 3 (H.map π) := hmapP.to_le (Subgroup.map_mono hHP)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp3
    have hza : Subgroup.zpowers (π a) ≤ H.map π :=
      Subgroup.zpowers_le.2 ⟨a, Subgroup.mem_sup_left (Subgroup.mem_zpowers a), rfl⟩
    have hzac : Nat.card (Subgroup.zpowers (π a)) = 3 := by
      rw [Nat.card_zpowers]
      refine orderOf_eq_prime ?_ hpa
      rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h3 a haP
    have hlt : Subgroup.zpowers (π a) < H.map π := by
      refine lt_of_le_of_ne hza fun heq => hpb ?_
      rw [heq]
      exact ⟨b, Subgroup.mem_sup_right (Subgroup.mem_zpowers b), rfl⟩
    have hcl : 3 < Nat.card (H.map π) := by
      rw [← hzac]
      exact Subgroup.card_lt_of_lt hlt
    rw [hn] at hcl ⊢
    have h2 : 2 ≤ n := by
      by_contra hn2
      have : 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc Nat.card (P.map π) ≤ 9 := h9
      _ = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h2
  have hdecomp : ∀ x ∈ P, ∃ w ∈ H, w⁻¹ * x ∈ Z := by
    intro x hx
    have : π x ∈ H.map π := hHmap ▸ Subgroup.mem_map_of_mem π hx
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.1 this
    exact ⟨w, hw, QuotientGroup.eq.1 hwx⟩
  have hright : ∀ u ∈ P, ⁅u, a⁆ ∈ Subgroup.zpowers c → ⁅u, b⁆ ∈ Subgroup.zpowers c →
      ∀ y ∈ P, ⁅u, y⁆ ∈ Subgroup.zpowers c := by
    intro u hu hua hub
    let T : Subgroup Y :=
      { carrier := {y | y ∈ P ∧ ⁅u, y⁆ ∈ Subgroup.zpowers c}
        mul_mem' := fun {y₁ y₂} h₁ h₂ => ⟨P.mul_mem h₁.1 h₂.1, by
          rw [comm_mul_right (hcZ u hu y₂ h₂.1)]
          exact Subgroup.mul_mem _ h₁.2 h₂.2⟩
        one_mem' := ⟨P.one_mem, by rw [commutatorElement_one_right]; exact Subgroup.one_mem _⟩
        inv_mem' := fun {y} hy => ⟨P.inv_mem hy.1, by
          have e := comm_mul_right (x := u) (w₁ := y) (w₂ := y⁻¹) (hcZ u hu _ (P.inv_mem hy.1))
          rw [mul_inv_cancel, commutatorElement_one_right] at e
          rw [eq_inv_of_mul_eq_one_right e.symm]
          exact Subgroup.inv_mem _ hy.2⟩ }
    have hT : ∀ y, y ∈ T ↔ y ∈ P ∧ ⁅u, y⁆ ∈ Subgroup.zpowers c := fun _ => Iff.rfl
    have hHT : H ≤ T := sup_le (Subgroup.zpowers_le.2 ((hT a).2 ⟨haP, hua⟩))
      (Subgroup.zpowers_le.2 ((hT b).2 ⟨hbP, hub⟩))
    intro y hy
    obtain ⟨w, hwH, hwy⟩ := hdecomp y hy
    have hwT := (hT w).1 (hHT hwH)
    have e : y = w * (w⁻¹ * y) := by group
    rw [e, comm_mul_right (hcZ u hu _ (P.mul_mem (P.inv_mem hwT.1) hy)), hzc' _ hwy u, mul_one]
    exact hwT.2
  have hca : ⁅a, b⁆ ∈ Subgroup.zpowers c := Subgroup.mem_zpowers c
  have haa : ⁅a, a⁆ ∈ Subgroup.zpowers c := by
    rw [commutatorElement_self]; exact Subgroup.one_mem _
  have hbb : ⁅b, b⁆ ∈ Subgroup.zpowers c := by
    rw [commutatorElement_self]; exact Subgroup.one_mem _
  have hba : ⁅b, a⁆ ∈ Subgroup.zpowers c := by
    rw [← commutatorElement_inv]; exact Subgroup.inv_mem _ hca
  have hA := hright a haP haa hca
  have hB := hright b hbP hba hbb
  refine ⟨c, ?_, ?_⟩
  · have h2 : ⁅a * a, b⁆ = c * c := comm_mul_left (hcZ a haP b hbP)
    have h3' : ⁅a * a * a, b⁆ = c * (c * c) := by
      rw [comm_mul_left (hcZ a haP b hbP), h2]
    rw [pow_three, ← h3', show a * a * a = a ^ 3 by rw [pow_three, mul_assoc]]
    exact hzc _ (h3 a haP) b
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [← commutatorElement_inv]
    refine Subgroup.inv_mem _ (hright y hy ?_ ?_ x hx)
    · rw [← commutatorElement_inv]; exact Subgroup.inv_mem _ (hA y hy)
    · rw [← commutatorElement_inv]; exact Subgroup.inv_mem _ (hB y hy)

theorem card_center_le_three (hperf : commutator Y = ⊤) (hL : IsLThreeFour (Y ⧸ Subgroup.center Y))
    (hZ : IsPGroup 3 (Subgroup.center Y)) : Nat.card (Subgroup.center Y) ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hZP⟩ := hZ.exists_le_sylow
  set Z := Subgroup.center Y with hZdef
  set π := QuotientGroup.mk' Z with hπ
  have hPmap : IsPGroup 3 ((P : Subgroup Y).map π) := P.isPGroup'.map π
  have h9 := InputsL34.card_le_nine_of_isPGroup hL hPmap
  have h3 : ∀ x ∈ (P : Subgroup Y), x ^ 3 ∈ Z := by
    intro x hx
    have : (π x) ^ 3 = 1 := InputsL34.pow_three_of_isPGroup hL
      (hPmap.to_le (Subgroup.zpowers_le.2 ⟨x, hx, rfl⟩))
    rw [← map_pow] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  have hcZ : ∀ x ∈ (P : Subgroup Y), ∀ y ∈ (P : Subgroup Y), ⁅x, y⁆ ∈ Z := by
    intro x hx y hy
    haveI := InputsL34.finite_of_isLThreeFour hL
    obtain ⟨S, hS⟩ := hPmap.exists_le_sylow
    have hS9 := InputsL34.card_sylow_of_isLThreeFour hL S
    have hxy : π x * π y = π y * π x :=
      InputsL34.commute_of_card_nine hS9 (hS ⟨x, hx, rfl⟩) (hS ⟨y, hy, rfl⟩)
    have : π ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_def, hxy]; group
    exact (QuotientGroup.eq_one_iff _).1 this
  obtain ⟨c, hc3, hle⟩ := exists_comm_le_zpowers hcZ h9 h3
  have hZle : Z ≤ ⁅(P : Subgroup Y), (P : Subgroup Y)⁆ := by
    intro z hz
    have h1 := pow_index_mem_comm hperf P hz
    obtain ⟨k, hk⟩ := hZ ⟨z, hz⟩
    have hzk : z ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hcop : (P : Subgroup Y).index.Coprime (orderOf z) := by
      have h3i : Nat.Coprime 3 (P : Subgroup Y).index :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 P.not_dvd_index
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hzk)
        (Nat.Coprime.pow_right k h3i.symm)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Subgroup.pow_mem _ h1 m
  calc Nat.card Z ≤ Nat.card (Subgroup.zpowers c) := Subgroup.card_le_of_le (hZle.trans hle)
    _ = orderOf c := Nat.card_zpowers c
    _ ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc3)

end ZBound

section Comp

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)

theorem barOf_perfect {X L : Subgroup G} (hL : GLAPComponent 3 X L) :
    commutator (barOf 3 L) = ⊤ :=
  (CFSG.HardMathSupport.Solomon.UniquenessMaximal.isQuasisimple_quotient_of_glaPComponent
    Nat.prime_three hL).1

theorem card_center_barOf_le {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hLL : IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L))) :
    Nat.card (Subgroup.center (barOf 3 L)) ≤ 3 :=
  card_center_le_three (barOf_perfect hL) hLL
    (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.isPGroup_center_barOf L)

theorem mem_centBar_iff' {p : ℕ} {X L : Subgroup G} {g : G} :
    g ∈ centBar p X L ↔ g ∈ X ∧ ∃ h : g ∈ Subgroup.normalizer (L : Set G), barAut p L ⟨g, h⟩ = 1 := by
  unfold centBar
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨n, hn, hng⟩, hX⟩
    subst hng
    exact ⟨hX, n.2, MonoidHom.mem_ker.1 hn⟩
  · rintro ⟨hX, h, hb⟩
    exact ⟨⟨⟨g, h⟩, MonoidHom.mem_ker.2 hb, rfl⟩, hX⟩

theorem card_le_nine_mul_centBar {L A : Subgroup G}
    (hLL : IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L))) (hperf : commutator (barOf 3 L) = ⊤)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA : IsElemAbelian 3 A) :
    Nat.card A ≤ 9 * Nat.card (centBar 3 A L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ι : ↥A →* ↥(Subgroup.normalizer (L : Set G)) :=
    { toFun := fun a => ⟨a.1, hAN a.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let f : ↥A →* MulAut (barOf 3 L) := (barAut 3 L).comp ι
  have hker : f.ker.map A.subtype = centBar 3 A L := by
    ext g
    rw [Subgroup.mem_map, mem_centBar_iff']
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hAN x.2, MonoidHom.mem_ker.1 hx⟩
    · rintro ⟨hX, h, hb⟩
      exact ⟨⟨g, hX⟩, MonoidHom.mem_ker.2 hb, rfl⟩
  have hkc : Nat.card (centBar 3 A L) = Nat.card f.ker := by
    rw [← hker, Subgroup.card_map_of_injective A.subtype_injective]
  have hel : IsElemAbelian 3 f.range := by
    refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a, ha⟩ := u.2
      obtain ⟨b, hb⟩ := v.2
      show (u : MulAut (barOf 3 L)) * v = v * u
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hA.comm a.2 b.2)
    · obtain ⟨a, rfl⟩ := hy
      rw [← map_pow]
      have : a ^ 3 = 1 := Subtype.ext (by simpa using hA.2 a.1 a.2)
      rw [this, map_one]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hel.isPGroup
  have hk2 : k ≤ 2 :=
    (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (le_top : f.range ≤ ⊤) hel hk).trans
      (Claims1245.pRank_mulAut_le_two_of_modCenter hperf hLL)
  have hr : Nat.card f.range ≤ 9 := by
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  have hA' : Nat.card A = Nat.card ↥A := rfl
  rw [hA', CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range f, hkc, mul_comm]
  exact Nat.mul_le_mul_right _ hr

theorem barOf_injOn {L U : Subgroup G} (hUL : U ≤ L) (hU : IsPGroup 3 U) {u v : G} (hu : u ∈ U)
    (hv : v ∈ U)
    (h : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨u, hUL hu⟩ : barOf 3 L) =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨v, hUL hv⟩) : u = v := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : (⟨u, hUL hu⟩ : ↥L)⁻¹ * ⟨v, hUL hv⟩ ∈ GLAPPrimeCore 3 ↥L := QuotientGroup.eq.1 h
  have h2 : u⁻¹ * v ∈ U ⊓ GLAPPrimeCoreOf 3 L :=
    ⟨U.mul_mem (U.inv_mem hu) hv, ⟨_, h1, rfl⟩⟩
  rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.pgroup_inf_core_eq_bot L hU,
    Subgroup.mem_bot] at h2
  calc u = u * (u⁻¹ * v) := by rw [h2, mul_one]
    _ = v := by group

theorem card_le_three_of_le_centBar {X L U : Subgroup G} (hL : GLAPComponent 3 X L)
    (hLL : IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L))) (hUL : U ≤ L) (hU : IsPGroup 3 U)
    (hUC : U ≤ centBar 3 ⊤ L) : Nat.card U ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set f : ↥L →* barOf 3 L := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) with hf
  let g : ↥U →* barOf 3 L := f.comp (Subgroup.inclusion hUL)
  have hginj : Function.Injective g := by
    intro u v huv
    exact Subtype.ext (barOf_injOn hUL hU u.2 v.2 huv)
  have hcen : g.range ≤ Subgroup.center (barOf 3 L) := by
    rintro _ ⟨u, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) w
    obtain ⟨-, -, hcomm⟩ := Inputs1114.mem_centBar_iff_forall.1 (hUC u.2)
    have h1 := hcomm l l.2
    obtain ⟨y, hy, hyc⟩ := h1
    have hy' : (⟨u, hUL u.2⟩ : ↥L) * l * (⟨u, hUL u.2⟩ : ↥L)⁻¹ * l⁻¹ ∈ GLAPPrimeCore 3 ↥L := by
      have : y = (⟨u, hUL u.2⟩ : ↥L) * l * (⟨u, hUL u.2⟩ : ↥L)⁻¹ * l⁻¹ := Subtype.ext (by simpa using hyc)
      rw [← this]
      exact hy
    have h2 : f ((⟨u, hUL u.2⟩ : ↥L) * l * (⟨u, hUL u.2⟩ : ↥L)⁻¹ * l⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hy'
    simp only [map_mul, map_inv] at h2
    have h3 : g u = f ⟨u, hUL u.2⟩ := rfl
    rw [h3]
    calc f l * f ⟨u, hUL u.2⟩ = (f ⟨u, hUL u.2⟩ * f l * (f ⟨u, hUL u.2⟩)⁻¹ * (f l)⁻¹)⁻¹ *
          (f ⟨u, hUL u.2⟩ * f l) := by group
      _ = f ⟨u, hUL u.2⟩ * f l := by rw [h2, inv_one, one_mul]
  calc Nat.card U = Nat.card g.range := Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv
    _ ≤ Nat.card (Subgroup.center (barOf 3 L)) := Subgroup.card_le_of_le hcen
    _ ≤ 3 := card_center_barOf_le hL hLL

theorem not_isCyclic_of_isSylowIn {L T : Subgroup G}
    (hLL : IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L))) (hT : IsSylowIn 3 L T) :
    ¬ IsCyclic T := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hcyc
  obtain ⟨P', hP'⟩ := Claims1245.exists_sylow_of_isSylowIn hT
  let ψ : ↥L →* (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) :=
    (QuotientGroup.mk' _).comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  set S := P'.mapSurjective hψ with hS
  have hS9 := InputsL34.card_sylow_of_isLThreeFour hLL S
  have hTc : IsCyclic ↥(T.subgroupOf L) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hT.1).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hScyc : IsCyclic ↥(S : Subgroup (barOf 3 L ⧸ Subgroup.center (barOf 3 L))) := by
    rw [hS, Sylow.coe_mapSurjective, hP']
    exact isCyclic_of_surjective (ψ.subgroupMap (T.subgroupOf L)) (ψ.subgroupMap_surjective _)
  obtain ⟨g, hg⟩ := hScyc.exists_generator
  have hord : orderOf g = 9 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hS9]
  have h3 : ((g : _) : barOf 3 L ⧸ Subgroup.center (barOf 3 L)) ^ 3 = 1 :=
    InputsL34.pow_three_of_card_nine hLL hS9 g.2
  have hdvd : orderOf ((g : _) : barOf 3 L ⧸ Subgroup.center (barOf 3 L)) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one h3
  rw [Subgroup.orderOf_coe, hord] at hdvd
  norm_num at hdvd

theorem comm_of_centBar {L P : Subgroup G} (hP : IsPGroup 3 P) {c l : G} (hcP : c ∈ P)
    (hc : c ∈ centBar 3 ⊤ L) (hlP : l ∈ P) (hlL : l ∈ L) : c * l = l * c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hcomm⟩ := Inputs1114.mem_centBar_iff_forall.1 hc
  have h1 := hcomm l hlL
  have h2 : c * l * c⁻¹ * l⁻¹ ∈ P := P.mul_mem (P.mul_mem (P.mul_mem hcP hlP) (P.inv_mem hcP))
    (P.inv_mem hlP)
  have h3 : c * l * c⁻¹ * l⁻¹ ∈ P ⊓ GLAPPrimeCoreOf 3 L := ⟨h2, h1⟩
  rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.pgroup_inf_core_eq_bot L hP,
    Subgroup.mem_bot] at h3
  calc c * l = (c * l * c⁻¹ * l⁻¹) * (l * c) := by group
    _ = l * c := by rw [h3, one_mul]

theorem centBar_normal {L P : Subgroup G} (hPN : P ≤ Subgroup.normalizer (L : Set G)) :
    ((centBar 3 P L).subgroupOf P).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnP, hnN, hcomm⟩ := Inputs1114.mem_centBar_iff_forall.1 hn
  have hgN := hPN g.2
  refine Inputs1114.mem_centBar_iff_forall.2 ⟨P.mul_mem (P.mul_mem g.2 hnP) (P.inv_mem g.2),
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hgN hnN)
      ((Subgroup.normalizer _).inv_mem hgN), fun l hl => ?_⟩
  have hl' : (g : G)⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hgN) l).1 hl
    simpa using this
  have h1 := hcomm _ hl'
  have h2 := CFSG.HardMathSupport.Solomon.Coordinator.conj_mem_gLAPPrimeCoreOf_of_mem_normalizer hgN h1
  have e : (g : G) * (↑n * ((g : G)⁻¹ * l * ↑g) * (↑n)⁻¹ * ((g : G)⁻¹ * l * ↑g)⁻¹) * (g : G)⁻¹ =
      (g : G) * n * (g : G)⁻¹ * l * ((g : G) * n * (g : G)⁻¹)⁻¹ * l⁻¹ := by group
  rw [e] at h2
  exact h2

theorem kc_of_normalizes {X L P : Subgroup G} (hL : GLAPComponent 3 X L)
    (hLL : IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L)))
    (hPX : P ≤ X) (hP : IsPGroup 3 P) (hPN : P ≤ Subgroup.normalizer (L : Set G))
    (hT : IsSylowIn 3 L (P ⊓ L)) {A B : Subgroup G} (hA : IsEkIn 3 4 P A) (hB : IsEkIn 3 4 P B) :
    IsKConnectedIn 3 3 X A B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf := barOf_perfect hL
  have hTn : ((P ⊓ L).subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨P.mul_mem (P.mul_mem g.2 hn.1) (P.inv_mem g.2),
      (Subgroup.mem_normalizer_iff.1 (hPN g.2) n).1 hn.2⟩⟩
  obtain ⟨U₂, hU₂T, hU₂, hU₂N⟩ := Claims1111b.input31_5_holds G 3 Nat.prime_three (by norm_num) P
    (P ⊓ L) hP inf_le_left hTn (not_isCyclic_of_isSylowIn hLL hT)
  set D := centBar 3 P L with hD
  have hDP : D ≤ P := inf_le_right
  have hAD : 9 ≤ Nat.card (A ⊓ D : Subgroup G) := by
    obtain ⟨hAP, hAel, hAc⟩ := hA
    have h := card_le_nine_mul_centBar hLL hperf (hAP.trans hPN) hAel
    have he : centBar 3 A L = A ⊓ D := by
      ext g
      rw [mem_centBar_iff', Subgroup.mem_inf, mem_centBar_iff']
      exact ⟨fun h' => ⟨h'.1, hAP h'.1, h'.2⟩, fun h' => ⟨h'.1, h'.2.2⟩⟩
    rw [he, hAc] at h
    omega
  have hDnc : ¬ IsCyclic D := by
    intro hcyc
    have hAel := hA.2.1
    have hADel : IsElemAbelian 3 (A ⊓ D) := isElemAbelian_mono hAel inf_le_left
    have hnc := not_isCyclic_of_isElemAbelian hADel (by norm_num; exact hAD)
    apply hnc
    exact isCyclic_of_injective (Subgroup.inclusion (inf_le_right : A ⊓ D ≤ D))
      (Subgroup.inclusion_injective _)
  obtain ⟨U₁, hU₁D, hU₁, hU₁N⟩ := Claims1111b.input31_5_holds G 3 Nat.prime_three (by norm_num) P D
    hP hDP (centBar_normal hPN) hDnc
  have hU₁C : U₁ ≤ centBar 3 ⊤ L := fun u hu => by
    obtain ⟨-, h, hb⟩ := mem_centBar_iff'.1 (hU₁D hu)
    exact mem_centBar_iff'.2 ⟨Subgroup.mem_top u, h, hb⟩
  have hU₁P : U₁ ≤ P := hU₁D.trans hDP
  have hU₂P : U₂ ≤ P := hU₂T.trans inf_le_left
  have hU₂L : U₂ ≤ L := hU₂T.trans inf_le_right
  have hcomm : U₁ ≤ Subgroup.centralizer (U₂ : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun v hv =>
      (comm_of_centBar hP (hU₁P hu) (hU₁C hu) (hU₂P hv) (hU₂L hv)).symm
  have hne : U₁ ≠ U₂ := by
    intro heq
    have h3 := card_le_three_of_le_centBar hL hLL hU₂L (hP.to_le hU₂P) (heq ▸ hU₁C)
    rw [hU₂.2] at h3
    norm_num at h3
  exact kc_of_plane_pair hPX hP hU₁ hU₂ hU₁P hU₂P hU₁N hU₂N hne hcomm hA hB

end Comp

section Conjugates

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.Coordinator (conj_mem_gLAPPrimeCoreOf_of_mem_normalizer)

def modCent (X L : Subgroup G) : Subgroup G where
  carrier := {m | m ∈ X ∧ ∀ l ∈ L, m * l * m⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf 3 X}
  mul_mem' := by
    rintro m₁ m₂ ⟨h₁X, h₁⟩ ⟨h₂X, h₂⟩
    refine ⟨X.mul_mem h₁X h₂X, fun l hl => ?_⟩
    have e : m₁ * m₂ * l * (m₁ * m₂)⁻¹ * l⁻¹ =
        (m₁ * (m₂ * l * m₂⁻¹ * l⁻¹) * m₁⁻¹) * (m₁ * l * m₁⁻¹ * l⁻¹) := by group
    rw [e]
    exact (GLAPPrimeCoreOf 3 X).mul_mem
      (conj_mem_gLAPPrimeCoreOf_of_mem_normalizer (Subgroup.le_normalizer h₁X) (h₂ l hl)) (h₁ l hl)
  one_mem' := ⟨X.one_mem, fun l _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact Subgroup.one_mem _⟩
  inv_mem' := by
    rintro m ⟨hX, h⟩
    refine ⟨X.inv_mem hX, fun l hl => ?_⟩
    have e : m⁻¹ * l * m⁻¹⁻¹ * l⁻¹ = m⁻¹ * (m * l * m⁻¹ * l⁻¹)⁻¹ * m⁻¹⁻¹ := by group
    rw [e]
    exact conj_mem_gLAPPrimeCoreOf_of_mem_normalizer (Subgroup.le_normalizer (X.inv_mem hX))
      ((GLAPPrimeCoreOf 3 X).inv_mem (h l hl))

theorem mem_modCent {X L : Subgroup G} {m : G} :
    m ∈ modCent X L ↔ m ∈ X ∧ ∀ l ∈ L, m * l * m⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf 3 X := Iff.rfl

theorem le_modCent {X L L' : Subgroup G} (hL : GLAPComponent 3 X L) (hL' : GLAPComponent 3 X L')
    (hne : L' ≠ L) : L' ≤ modCent X L := fun m hm =>
  ⟨hL'.1 hm, fun l hl => by
    have := CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne
      Nat.prime_three hL' hL hne (Subgroup.commutator_mem_commutator hm hl)
    rwa [commutatorElement_def] at this⟩

theorem mem_centBar_of_modCent {X L : Subgroup G} (hL : GLAPComponent 3 X L) {t : G} (htL : t ∈ L)
    (ht : t ∈ modCent X L) : t ∈ centBar 3 ⊤ L := by
  refine Inputs1114.mem_centBar_iff_forall.2
    ⟨Subgroup.mem_top t, Subgroup.le_normalizer htL, fun l hl => ?_⟩
  have h1 : t * l * t⁻¹ * l⁻¹ ∈ L ⊓ GLAPPrimeCoreOf 3 X :=
    ⟨L.mul_mem (L.mul_mem (L.mul_mem htL hl) (L.inv_mem htL)) (L.inv_mem hl), ht.2 l hl⟩
  rwa [glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hL.2.1] at h1

theorem comp_conj {X L : Subgroup G} (hL : GLAPComponent 3 X L) {g : G} (hg : g ∈ X) :
    GLAPComponent 3 X (GLBConj g L) := by
  have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL g
  rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at h

theorem exists_mem_second_center {T M Z₀ : Subgroup G} (hT : IsPGroup 3 T) (hMT : M ≤ T)
    (hZM : Z₀ ≤ M) (hMN : T ≤ Subgroup.normalizer (M : Set G))
    (hZN : T ≤ Subgroup.normalizer (Z₀ : Set G)) (hne : Z₀ ≠ M) :
    ∃ u ∈ M, u ∉ Z₀ ∧ ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ Z₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z' : Subgroup ↥T := Z₀.subgroupOf T with hZ'
  haveI hZ'n : Z'.Normal := ⟨fun n hn g => by
    rw [hZ', Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hZN g.2) n).1 hn⟩
  have hQ : IsPGroup 3 (↥T ⧸ Z') := hT.to_quotient Z'
  haveI : Group.IsNilpotent (↥T ⧸ Z') := hQ.isNilpotent
  set q : ↥T →* ↥T ⧸ Z' := QuotientGroup.mk' Z' with hq
  obtain ⟨m, hmM, hmZ⟩ : ∃ m ∈ M, m ∉ Z₀ := by
    by_contra h
    push Not at h
    exact hne (le_antisymm hZM h)
  have hMn : (M.subgroupOf T).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hMN g.2) n).1 hn⟩
  set M' : Subgroup (↥T ⧸ Z') := (M.subgroupOf T).map q with hM'
  haveI : M'.Normal := hMn.map q (QuotientGroup.mk'_surjective Z')
  have hM'ne : M' ≠ ⊥ := by
    intro h
    have hmem : q ⟨m, hMT hmM⟩ ∈ M' := ⟨⟨m, hMT hmM⟩, Subgroup.mem_subgroupOf.2 hmM, rfl⟩
    rw [h, Subgroup.mem_bot, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hmZ (Subgroup.mem_subgroupOf.1 hmem)
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hM'ne)
  obtain ⟨hwM', hwZ⟩ := Subgroup.mem_inf.1 w.2
  obtain ⟨u, huM, huw⟩ := Subgroup.mem_map.1 hwM'
  refine ⟨u, Subgroup.mem_subgroupOf.1 huM, fun huZ => hw1 ?_, fun t ht => ?_⟩
  · apply Subtype.ext
    rw [← huw, OneMemClass.coe_one, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 huZ
  · have hc := Subgroup.mem_center_iff.1 hwZ (q ⟨t, ht⟩)
    have h1 : q (⟨t, ht⟩ * u * ⟨t, ht⟩⁻¹ * u⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      have huw' : q u = (w : ↥T ⧸ Z') := huw
      rw [huw', hc]
      group
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.1 h1

theorem cube_mem_centBar {L : Subgroup G}
    (hLL : IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L))) {u : G} (huL : u ∈ L) {k : ℕ}
    (hu : u ^ (3 ^ k) = 1) : u ^ 3 ∈ centBar 3 ⊤ L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set f : ↥L →* barOf 3 L := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) with hf
  set π : barOf 3 L →* barOf 3 L ⧸ Subgroup.center (barOf 3 L) := QuotientGroup.mk' _ with hπ
  set u' : ↥L := ⟨u, huL⟩ with hu'
  have hu'k : u' ^ (3 ^ k) = 1 := Subtype.ext (by simpa [hu'] using hu)
  have hp : IsPGroup 3 (Subgroup.zpowers (π (f u'))) := by
    intro g
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      ← map_pow, ← map_pow, hu'k, map_one, map_one, one_zpow, OneMemClass.coe_one]
  have h3 := InputsL34.pow_three_of_isPGroup hLL hp
  rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  refine Inputs1114.mem_centBar_iff_forall.2
    ⟨Subgroup.mem_top _, Subgroup.le_normalizer (L.pow_mem huL 3), fun l hl => ?_⟩
  have hc := Subgroup.mem_center_iff.1 h3 (f ⟨l, hl⟩)
  have h1 : f (u' ^ 3 * ⟨l, hl⟩ * (u' ^ 3)⁻¹ * ⟨l, hl⟩⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [map_pow, ← hc]
    group
  rw [hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, by simp [hu']⟩

theorem conj_mem_centBar {L : Subgroup G} {g c : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hc : c ∈ centBar 3 ⊤ L) : g * c * g⁻¹ ∈ centBar 3 ⊤ L := by
  obtain ⟨-, hcN, hcomm⟩ := Inputs1114.mem_centBar_iff_forall.1 hc
  refine Inputs1114.mem_centBar_iff_forall.2 ⟨Subgroup.mem_top _,
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hg hcN)
      ((Subgroup.normalizer _).inv_mem hg), fun l hl => ?_⟩
  have hl' : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hg) l).1 hl
    simpa using this
  have h2 := conj_mem_gLAPPrimeCoreOf_of_mem_normalizer hg (hcomm _ hl')
  have e : g * (c * (g⁻¹ * l * g) * c⁻¹ * (g⁻¹ * l * g)⁻¹) * g⁻¹ =
      g * c * g⁻¹ * l * (g * c * g⁻¹)⁻¹ * l⁻¹ := by group
  rwa [e] at h2

theorem false_of_sc3 {X L R Y : Subgroup G} {a : G} (hL : GLAPComponent 3 X L)
    (hLL : IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L))) (hRX : R ≤ X)
    (hR : IsPGroup 3 R) (hT : IsSylowIn 3 L (R ⊓ L))
    (hNn : ∀ r ∈ R, ∀ n ∈ R ⊓ Subgroup.normalizer (L : Set G),
      r * n * r⁻¹ ∈ R ⊓ Subgroup.normalizer (L : Set G))
    (hYN : Y ≤ R ⊓ Subgroup.normalizer (L : Set G))
    (haR : a ∈ R) (haN : a ∉ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1)
    (haY : ∀ y ∈ Y, a * y = y * a)
    (hsc : ∀ w ∈ R ⊓ Subgroup.normalizer (L : Set G), w ^ 3 = 1 → (∀ y ∈ Y, w * y = y * w) →
      w ∈ Y) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := R ⊓ Subgroup.normalizer (L : Set G) with hN
  set T₁ := R ⊓ L with hT₁
  set Z₀ := T₁ ⊓ centBar 3 ⊤ L with hZ₀
  have hT₁N : T₁ ≤ N := fun t ht => ⟨ht.1, Subgroup.le_normalizer ht.2⟩
  have hNT₁ : N ≤ Subgroup.normalizer (T₁ : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [hT₁, Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr ((Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hn.1)) t)
      ((Subgroup.mem_normalizer_iff.1 hn.2) t)
  have hNZ₀ : N ≤ Subgroup.normalizer (Z₀ : Set G) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hNT₁ hn) z).1 hz.1, conj_mem_centBar hn.2 hz.2⟩
  have haX : a⁻¹ ∈ X := X.inv_mem (hRX haR)
  set La := GLBConj a⁻¹ L with hLadef
  set La2 := GLBConj a⁻¹ La with hLa2def
  have hLa : GLAPComponent 3 X La := comp_conj hL haX
  have hLa2 : GLAPComponent 3 X La2 := comp_conj hLa haX
  have hconjLa : ∀ {H : Subgroup G} {u : G}, u ∈ H → a * u * a⁻¹ ∈ GLBConj a⁻¹ H := by
    intro H u hu
    rw [mem_gLBConj]
    simpa [mul_assoc] using hu
  have hneLa : La ≠ L := by
    intro h
    apply haN
    have h1 : a⁻¹ ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_iff_gLBConj_eq.2 h
    simpa using (Subgroup.normalizer _).inv_mem h1
  have ha2 : a⁻¹ * a⁻¹ = a := by
    calc a⁻¹ * a⁻¹ = a⁻¹ * a⁻¹ * a ^ 3 := by rw [ha3, mul_one]
      _ = a := by group
  have hneLa2 : La2 ≠ L := by
    intro h
    rw [hLa2def, hLadef, gLBConj_gLBConj, ha2] at h
    exact haN (mem_normalizer_iff_gLBConj_eq.2 h)
  have hneLa12 : La2 ≠ La := by
    intro h
    apply hneLa
    have h1 : GLBConj a La2 = GLBConj a La := by rw [h]
    rwa [hLa2def, gLBConj_gLBConj, inv_mul_cancel, gLBConj_one, hLadef, gLBConj_gLBConj,
      inv_mul_cancel, gLBConj_one] at h1
  have hΩ : ∀ t ∈ T₁, t ^ 3 = 1 → (∀ y ∈ Y, t * y = y * t) → t ∈ Z₀ ∧ t ∈ Y ∧ a * t = t * a := by
    intro t ht ht3 htY
    have htY' := hsc t (hT₁N ht) ht3 htY
    have hta := haY t htY'
    have htLa : t ∈ La := by
      have := hconjLa (H := L) ht.2
      rwa [hta, mul_inv_cancel_right] at this
    exact ⟨⟨ht, mem_centBar_of_modCent hL ht.2 (le_modCent hL hLa hneLa htLa)⟩, htY', hta⟩
  set TY := Y ⊔ T₁ with hTY
  have hTYN : TY ≤ N := sup_le hYN hT₁N
  have hTYp : IsPGroup 3 TY := hR.to_le (hTYN.trans inf_le_left)
  have hT₁ne : T₁ ≠ ⊥ := by
    intro h
    apply not_isCyclic_of_isSylowIn hLL hT
    rw [h]
    infer_instance
  obtain ⟨ζ, hζT, hζ1, hζ3, hζc⟩ := exists_central_of_normalized hTYp le_sup_right
    (hTYN.trans hNT₁) hT₁ne
  obtain ⟨hζZ, -, hζa⟩ := hΩ ζ hζT hζ3 fun y hy => (hζc y (le_sup_left (a := Y) hy)).symm
  have hZ₀3 : Nat.card Z₀ ≤ 3 := card_le_three_of_le_centBar hL hLL (inf_le_left.trans inf_le_right)
    (hR.to_le (inf_le_left.trans inf_le_left)) inf_le_right
  have hZ₀eq : Z₀ = Subgroup.zpowers ζ := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hζZ) ?_).symm
    rw [Nat.card_zpowers, orderOf_eq_prime hζ3 hζ1]
    exact hZ₀3
  have hZa : ∀ c ∈ Z₀, a * c = c * a := by
    intro c hc
    rw [hZ₀eq] at hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact (Commute.zpow_right hζa i).eq
  have hne : Z₀ ≠ T₁ := by
    intro h
    apply not_isCyclic_of_isSylowIn hLL hT
    rw [← h, hZ₀eq]
    infer_instance
  obtain ⟨u, huT, huZ, huc⟩ := exists_mem_second_center hTYp le_sup_right inf_le_left
    (hTYN.trans hNT₁) (hTYN.trans hNZ₀) hne
  have huR : u ∈ R := huT.1
  have huL : u ∈ L := huT.2
  set v := a * u * a⁻¹ with hv
  have hvR : v ∈ R := R.mul_mem (R.mul_mem haR huR) (R.inv_mem haR)
  have hvLa : v ∈ La := hconjLa huL
  have hvN : v ∈ N := hNn a haR u (hT₁N huT)
  have huv : u * v = v * u :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.comm_of_inf hR hL hLa hneLa.symm ⟨huR, huL⟩
      ⟨hvR, hvLa⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hR) ⟨u, huR⟩
  have huk : u ^ (3 ^ k) = 1 := by
    rw [← hk]
    simpa using pow_orderOf_eq_one (⟨u, huR⟩ : ↥R)
  have hu3 : u ^ 3 ∈ Z₀ := ⟨⟨R.pow_mem huR 3, L.pow_mem huL 3⟩, cube_mem_centBar hLL huL huk⟩
  have hv3 : v ^ 3 = u ^ 3 := by
    rw [hv, conj_pow, hZa _ hu3, mul_inv_cancel_right]
  set x := u * v⁻¹ with hx
  have hxN : x ∈ N := N.mul_mem (hT₁N huT) (N.inv_mem hvN)
  have hx3 : x ^ 3 = 1 := by
    have hcomm : Commute u v⁻¹ := (Commute.inv_right huv)
    rw [hx, hcomm.mul_pow, inv_pow, hv3, mul_inv_cancel]
  have hxY : ∀ y ∈ Y, x * y = y * x := by
    intro y hy
    set c := y * u * y⁻¹ * u⁻¹ with hc
    have hcZ : c ∈ Z₀ := huc y (le_sup_left (a := Y) hy)
    have hca : a * c = c * a := hZa c hcZ
    have hya : a * y = y * a := haY y hy
    have hcu : c * u = u * c :=
      comm_of_centBar hR hcZ.1.1 hcZ.2 huR huL
    have hcv : y * v * y⁻¹ * v⁻¹ = c := by
      have e : y * v * y⁻¹ * v⁻¹ = a * c * a⁻¹ := by
        rw [hv, hc]
        have hy' : a⁻¹ * y * a = y := by
          calc a⁻¹ * y * a = a⁻¹ * (y * a) := by group
            _ = a⁻¹ * (a * y) := by rw [hya]
            _ = y := by group
        calc y * (a * u * a⁻¹) * y⁻¹ * (a * u * a⁻¹)⁻¹
            = a * ((a⁻¹ * y * a) * u * (a⁻¹ * y * a)⁻¹ * u⁻¹) * a⁻¹ := by group
          _ = a * (y * u * y⁻¹ * u⁻¹) * a⁻¹ := by rw [hy']
      rw [e, hca, mul_inv_cancel_right]
    have hcv' : c * v = v * c := by
      have e : c * v = a * (c * u) * a⁻¹ := by
        calc c * v = (a * c * a⁻¹) * v := by rw [hca, mul_inv_cancel_right]
          _ = a * (c * u) * a⁻¹ := by rw [hv]; group
      rw [e, hcu]
      calc a * (u * c) * a⁻¹ = (a * u * a⁻¹) * (a * c * a⁻¹) := by group
        _ = v * c := by rw [hca, mul_inv_cancel_right]
    have e1 : y * u = c * u * y := by rw [hc]; group
    have e2 : y * v⁻¹ = c⁻¹ * v⁻¹ * y := by
      have : c⁻¹ * v⁻¹ = v⁻¹ * c⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hcv']
      rw [this, ← hcv]
      group
    calc x * y = u * v⁻¹ * y := rfl
      _ = c * u * c⁻¹ * v⁻¹ * y := by
          rw [show c * u * c⁻¹ = u by rw [hcu]; group]
      _ = c * u * (c⁻¹ * v⁻¹ * y) := by group
      _ = c * u * (y * v⁻¹) := by rw [e2]
      _ = y * u * v⁻¹ := by rw [← mul_assoc, ← e1]
      _ = y * x := by rw [hx]; group
  have hxa : a * x = x * a := haY x (hsc x hxN hx3 hxY)
  set w := a * v * a⁻¹ with hw
  have hwR : w ∈ R := R.mul_mem (R.mul_mem haR hvR) (R.inv_mem haR)
  have hwLa2 : w ∈ La2 := hconjLa hvLa
  have hvw : v * w = w * v :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.comm_of_inf hR hLa hLa2 hneLa12.symm
      ⟨hvR, hvLa⟩ ⟨hwR, hwLa2⟩
  have huvw : u = v * v * w⁻¹ := by
    have e : a * x * a⁻¹ = v * w⁻¹ := by rw [hx, hw, hv]; group
    rw [hxa, mul_inv_cancel_right, hx] at e
    have hwv : w⁻¹ * v = v * w⁻¹ := by
      calc w⁻¹ * v = w⁻¹ * (v * w) * w⁻¹ := by group
        _ = w⁻¹ * (w * v) * w⁻¹ := by rw [hvw]
        _ = v * w⁻¹ := by group
    calc u = u * v⁻¹ * v := by group
      _ = v * w⁻¹ * v := by rw [e]
      _ = v * (w⁻¹ * v) := by group
      _ = v * (v * w⁻¹) := by rw [hwv]
      _ = v * v * w⁻¹ := by group
  have hum : u ∈ modCent X L := by
    rw [huvw]
    exact (modCent X L).mul_mem ((modCent X L).mul_mem (le_modCent hL hLa hneLa hvLa)
      (le_modCent hL hLa hneLa hvLa)) ((modCent X L).inv_mem (le_modCent hL hLa2 hneLa2 hwLa2))
  exact huZ ⟨huT, mem_centBar_of_modCent hL huL hum⟩

theorem kc_index_three {X L R : Subgroup G} (hL : GLAPComponent 3 X L)
    (hLL : IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L))) (hRX : R ≤ X) (hR : IsPGroup 3 R)
    (hT : IsSylowIn 3 L (R ⊓ L)) (hn : (Subgroup.normalizer (L : Set G)).relIndex R = 3)
    {A B : Subgroup G} (hA : IsEkIn 3 4 R A) (hB : IsEkIn 3 4 R B) : IsKConnectedIn 3 3 X A B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := R ⊓ Subgroup.normalizer (L : Set G) with hN
  have hnorm : ((Subgroup.normalizer (L : Set G)).subgroupOf R).Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 hR
    have hidx : ((Subgroup.normalizer (L : Set G)).subgroupOf R).index = 3 := hn
    rw [hidx, hr]
    have hr0 : r ≠ 0 := by
      rintro rfl
      have h1 := ((Subgroup.normalizer (L : Set G)).subgroupOf R).index_dvd_card
      rw [hidx, hr, pow_zero] at h1
      norm_num at h1
    have hp := Nat.minFac_prime (show 3 ^ r ≠ 1 by
      intro h; exact hr0 (by simpa using (Nat.pow_eq_one.1 h)))
    exact ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
      (hp.dvd_of_dvd_pow (Nat.minFac_dvd _))).symm
  have hNn : ∀ r ∈ R, ∀ m ∈ N, r * m * r⁻¹ ∈ N := by
    intro r hr m hm
    have := hnorm.conj_mem ⟨m, hm.1⟩ (Subgroup.mem_subgroupOf.2 hm.2) ⟨r, hr⟩
    exact ⟨R.mul_mem (R.mul_mem hr hm.1) (R.inv_mem hr), Subgroup.mem_subgroupOf.1 this⟩
  have hNX : N ≤ X := inf_le_left.trans hRX
  have hNp : IsPGroup 3 N := hR.to_le inf_le_left
  have hNN : N ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hTN : IsSylowIn 3 L (N ⊓ L) := by
    have : N ⊓ L = R ⊓ L := by
      rw [hN, inf_assoc, inf_eq_right.2 (Subgroup.le_normalizer : L ≤ Subgroup.normalizer (L : Set G))]
    rw [this]
    exact hT
  have hred : ∀ A : Subgroup G, IsEkIn 3 4 R A →
      ∃ A' : Subgroup G, IsEkIn 3 4 N A' ∧ IsKConnectedIn 3 3 X A A' := by
    intro A hA
    obtain ⟨hAR, hAel, hAc⟩ := hA
    have hA81 : Nat.card A = 81 := by rw [hAc]; norm_num
    by_cases hAN : A ≤ Subgroup.normalizer (L : Set G)
    · exact ⟨A, ⟨le_inf hAR hAN, hAel, hAc⟩,
        kc_of_le_elem (hAR.trans hRX) hAel le_rfl le_rfl (by omega) (by omega)⟩
    · obtain ⟨a, haA, haN⟩ := Set.not_subset.1 hAN
      set Y := A ⊓ Subgroup.normalizer (L : Set G) with hY
      have hY27 : Nat.card Y = 27 := by
        have h1 := Subgroup.relIndex_mul_card (H := Subgroup.normalizer (L : Set G)) (K := A)
        have h2 : (Subgroup.normalizer (L : Set G)).relIndex A ≤ 3 :=
          hn ▸ Subgroup.relIndex_le_of_le_right hAR (by rw [hn]; norm_num)
        have h3 : (Subgroup.normalizer (L : Set G)).relIndex A ≠ 1 := fun h =>
          hAN (Subgroup.relIndex_eq_one.1 h)
        rw [hA81, inf_comm] at h1
        rw [← hY] at h1
        have h0 : (Subgroup.normalizer (L : Set G)).relIndex A ≠ 0 := by
          intro h; rw [h, zero_mul] at h1; norm_num at h1
        interval_cases h : (Subgroup.normalizer (L : Set G)).relIndex A <;> omega
      have hYN : Y ≤ N := fun y hy => ⟨hAR hy.1, hy.2⟩
      have hYel : IsElemAbelian 3 Y := isElemAbelian_mono hAel inf_le_left
      by_cases hw : ∃ w ∈ N, w ^ 3 = 1 ∧ (∀ y ∈ Y, w * y = y * w) ∧ w ∉ Y
      · obtain ⟨w, hwN, hw3, hwY, hwnY⟩ := hw
        set A' : Subgroup G := Y ⊔ Subgroup.zpowers w with hA'
        have hA'c : Nat.card A' = 81 := by
          rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three Y hw3 hwnY
            (fun e he => (hwY e he).symm), hY27]
        have hYz : Y ≤ Subgroup.centralizer (Subgroup.zpowers w : Set G) := by
          intro y hy
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
          exact (Commute.zpow_left (hwY y hy) i).eq
        have hA'el : IsElemAbelian 3 A' := isElemAbelian_sup_of_commute hYel
          (Claims1245.isElemAbelian_zpowers_of_pow_three hw3) hYz
        have hA'N : A' ≤ N := sup_le hYN (Subgroup.zpowers_le.2 hwN)
        refine ⟨A', ⟨hA'N, hA'el, by rw [hA'c]; norm_num⟩, ?_⟩
        exact kc_trans (kc_of_le_elem (hAR.trans hRX) hAel le_rfl (show Y ≤ A from inf_le_left)
            (by omega) (by omega))
          (kc_of_le_elem (hA'N.trans hNX) hA'el (show Y ≤ A' from le_sup_left) le_rfl (by omega)
            (by omega))
      · exfalso
        push Not at hw
        exact false_of_sc3 hL hLL hRX hR hT hNn hYN (hAR haA) haN (hAel.2 a haA)
          (fun y hy => hAel.comm haA hy.1) (fun w hwN hw3 hwY => hw w hwN hw3 hwY)
  obtain ⟨A', hA', hAA'⟩ := hred A hA
  obtain ⟨B', hB', hBB'⟩ := hred B hB
  exact kc_trans hAA' (kc_trans (kc_of_normalizes hL hLL hNX hNp hNN hTN hA' hB') (kc_symm hBB'))

end Conjugates

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem gLBConj_eq_of_eq {L R U : Subgroup G} (hUN : R ⊓ Subgroup.normalizer (L : Set G) ≤
    Subgroup.normalizer (U : Set G)) {r r' : G} (hr : r ∈ R) (hr' : r' ∈ R)
    (h : GLBConj r L = GLBConj r' L) : GLBConj r U = GLBConj r' U := by
  have h1 : GLBConj r'⁻¹ (GLBConj r L) = GLBConj r'⁻¹ (GLBConj r' L) := by rw [h]
  rw [gLBConj_gLBConj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at h1
  have hm : r * r'⁻¹ ∈ R ⊓ Subgroup.normalizer (L : Set G) :=
    ⟨R.mul_mem hr (R.inv_mem hr'), mem_normalizer_iff_gLBConj_eq.2 h1⟩
  have h2 : GLBConj (r * r'⁻¹) U = U := mem_normalizer_iff_gLBConj_eq.1 (hUN hm)
  calc GLBConj r U = GLBConj r' (GLBConj (r * r'⁻¹) U) := by
        rw [gLBConj_gLBConj, show r * r'⁻¹ * r' = r by group]
    _ = GLBConj r' U := by rw [h2]

def conjProd (R U : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ r ∈ R, x ∈ GLBConj r U}

theorem gLBConj_le_conjProd {R U : Subgroup G} {r : G} (hr : r ∈ R) :
    GLBConj r U ≤ conjProd R U := fun x hx => Subgroup.subset_closure ⟨r, hr, hx⟩

theorem conjProd_props {X L R U : Subgroup G} (hL : GLAPComponent 3 X L) (hRX : R ≤ X)
    (hR : IsPGroup 3 R) (hUR : U ≤ R) (hUL : U ≤ L) (hU : IsElemAbelian 3 U)
    (hUN : R ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (U : Set G)) :
    conjProd R U ≤ R ∧ IsElemAbelian 3 (conjProd R U) ∧
      R ≤ Subgroup.normalizer ((conjProd R U : Subgroup G) : Set G) := by
  have hUr : ∀ r ∈ R, GLBConj r U ≤ R ⊓ GLBConj r L := fun r hr =>
    le_inf ((gLBConj_mono r hUR).trans (gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hr)).le)
      (gLBConj_mono r hUL)
  refine ⟨?_, ?_, ?_⟩
  · rw [conjProd, Subgroup.closure_le]
    rintro x ⟨r, hr, hx⟩
    exact ((hUr r hr) hx).1
  · refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro x ⟨r, hr, hx⟩ y ⟨r', hr', hy⟩
      by_cases h : GLBConj r L = GLBConj r' L
      · rw [gLBConj_eq_of_eq hUN hr hr' h] at hx
        exact (Lemma1112b.isElemAbelian_glbConj hU r').comm hx hy
      · exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.comm_of_inf hR
          (comp_conj hL (hRX hr)) (comp_conj hL (hRX hr')) h (hUr r hr hx) (hUr r' hr' hy)
    · rintro x ⟨r, hr, hx⟩
      exact (Lemma1112b.isElemAbelian_glbConj hU r).2 x hx
  · intro g hg
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hle : (conjProd R U).map (MulAut.conj g).toMonoidHom ≤ conjProd R U := by
      rw [conjProd, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, ⟨r, hr, hy⟩, rfl⟩
      refine Subgroup.subset_closure ⟨r * g⁻¹, R.mul_mem hr (R.inv_mem hg), ?_⟩
      rw [mem_gLBConj] at hy ⊢
      simpa [mul_assoc] using hy
    exact hle ⟨x, hx, rfl⟩

theorem card_iSup_conj_ge {X L R U : Subgroup G} (hL : GLAPComponent 3 X L)
    (hLL : IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L))) (hRX : R ≤ X)
    (hR : IsPGroup 3 R) (hUR : U ≤ R) (hUL : U ≤ L) (hU : IsPPlane 3 U) :
    ∀ S : Finset G, (∀ g ∈ S, g ∈ R) →
      (∀ g ∈ S, ∀ g' ∈ S, GLBConj g L = GLBConj g' L → g = g') → S.Nonempty →
      3 ^ (S.card + 1) ≤ Nat.card ↥(⨆ (g : G) (_ : g ∈ S), GLBConj g U : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUc : Nat.card U = 9 := by rw [hU.2]; norm_num
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ _ h; exact absurd h Finset.not_nonempty_empty
  | @insert g S hgS ih =>
    intro hSR hinj _
    rw [Finset.iSup_insert]
    have hgR : g ∈ R := hSR g (Finset.mem_insert_self g S)
    set V := GLBConj g U with hV
    have hVc : Nat.card V = 9 := by rw [hV, Lemma1112b.card_glbConj, hUc]
    by_cases hS0 : S = ∅
    · subst hS0
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, sup_bot_eq, insert_empty_eq,
        Finset.card_singleton]
      rw [hVc]
      norm_num
    have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hS0
    have ih' := ih (fun g' hg' => hSR g' (Finset.mem_insert_of_mem hg'))
      (fun g₁ h₁ g₂ h₂ h => hinj g₁ (Finset.mem_insert_of_mem h₁) g₂ (Finset.mem_insert_of_mem h₂) h)
      hSne
    set W := ⨆ (g' : G) (_ : g' ∈ S), GLBConj g' U with hW
    have hne : ∀ g' ∈ S, GLBConj g' L ≠ GLBConj g L := fun g' hg' h =>
      hgS (hinj g' (Finset.mem_insert_of_mem hg') g (Finset.mem_insert_self g S) h ▸ hg')
    have hUr : ∀ r ∈ R, GLBConj r U ≤ R ⊓ GLBConj r L := fun r hr =>
      le_inf ((gLBConj_mono r hUR).trans
        (gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hr)).le) (gLBConj_mono r hUL)
    have hcomm : V ≤ Subgroup.centralizer (W : Set G) := by
      refine cent_symm (iSup₂_le fun g' hg' => ?_)
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hg'R := hSR g' (Finset.mem_insert_of_mem hg')
      exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.comm_of_inf hR
        (comp_conj hL (hRX hgR)) (comp_conj hL (hRX hg'R)) (hne g' hg').symm (hUr g hgR hz)
        (hUr g' hg'R hy)
    have hint : Nat.card (V ⊓ W : Subgroup G) ≤ 3 := by
      have hconjV : GLBConj g⁻¹ V = U := by
        rw [hV, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one]
      have hconjW : GLBConj g⁻¹ W ≤ modCent X L := by
        change W.map (MulAut.conj g⁻¹⁻¹).toMonoidHom ≤ _
        rw [Subgroup.map_le_iff_le_comap]
        refine iSup₂_le fun g' hg' => ?_
        rw [← Subgroup.map_le_iff_le_comap]
        change GLBConj g⁻¹ (GLBConj g' U) ≤ _
        rw [gLBConj_gLBConj]
        have hg'R := hSR g' (Finset.mem_insert_of_mem hg')
        have hc : GLAPComponent 3 X (GLBConj (g' * g⁻¹) L) :=
          comp_conj hL (hRX (R.mul_mem hg'R (R.inv_mem hgR)))
        have hneL : GLBConj (g' * g⁻¹) L ≠ L := by
          intro h
          apply hne g' hg'
          have h1 : GLBConj g (GLBConj (g' * g⁻¹) L) = GLBConj g L := by rw [h]
          rwa [gLBConj_gLBConj, show g' * g⁻¹ * g = g' by group] at h1
        exact (gLBConj_mono _ hUL).trans (le_modCent hL hc hneL)
      have hle : GLBConj g⁻¹ (V ⊓ W) ≤ U ⊓ modCent X L := by
        rw [← hconjV]
        exact le_inf (gLBConj_mono _ inf_le_left) ((gLBConj_mono _ inf_le_right).trans hconjW)
      have h3 : Nat.card (U ⊓ modCent X L : Subgroup G) ≤ 3 :=
        card_le_three_of_le_centBar hL hLL (inf_le_left.trans hUL)
          (hR.to_le (inf_le_left.trans hUR))
          (fun t ht => mem_centBar_of_modCent hL (hUL ht.1) ht.2)
      calc Nat.card (V ⊓ W : Subgroup G) = Nat.card (GLBConj g⁻¹ (V ⊓ W)) :=
            (Lemma1112b.card_glbConj _ _).symm
        _ ≤ Nat.card (U ⊓ modCent X L : Subgroup G) := Subgroup.card_le_of_le hle
        _ ≤ 3 := h3
    have hcard := card_sup_mul_inf hcomm
    rw [hVc] at hcard
    rw [Finset.card_insert_of_notMem hgS]
    have hpos : 0 < Nat.card (V ⊓ W : Subgroup G) := Nat.card_pos
    have h3S : 3 ^ (S.card + 1 + 1) = 3 * 3 ^ (S.card + 1) := by ring
    rw [h3S]
    nlinarith

theorem kc_index_ge_nine {X L R : Subgroup G} (hL : GLAPComponent 3 X L)
    (hLL : IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L))) (hRX : R ≤ X) (hR : IsPGroup 3 R)
    (hT : IsSylowIn 3 L (R ⊓ L)) (hn : 9 ≤ (Subgroup.normalizer (L : Set G)).relIndex R)
    {A B : Subgroup G} (hA : IsEkIn 3 4 R A) (hB : IsEkIn 3 4 R B) : IsKConnectedIn 3 3 X A B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := R ⊓ Subgroup.normalizer (L : Set G) with hN
  have hTn : ((R ⊓ L).subgroupOf N).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨R.mul_mem (R.mul_mem g.2.1 hx.1) (R.inv_mem g.2.1),
      (Subgroup.mem_normalizer_iff.1 g.2.2 x).1 hx.2⟩⟩
  obtain ⟨U, hUT, hU, hUN⟩ := Claims1111b.input31_5_holds G 3 Nat.prime_three (by norm_num) N
    (R ⊓ L) (hR.to_le inf_le_left) (fun x hx => ⟨hx.1, Subgroup.le_normalizer hx.2⟩) hTn
    (not_isCyclic_of_isSylowIn hLL hT)
  have hUR : U ≤ R := hUT.trans inf_le_left
  have hUL : U ≤ L := hUT.trans inf_le_right
  obtain ⟨hER, hEel, hEN⟩ := conjProd_props hL hRX hR hUR hUL hU.1 hUN
  set Q := ↥R ⧸ (Subgroup.normalizer (L : Set G)).subgroupOf R with hQ
  haveI : Fintype Q := Fintype.ofFinite Q
  have hQc : 9 ≤ (Finset.univ : Finset Q).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hn
  obtain ⟨F, -, hF⟩ := Finset.exists_subset_card_eq hQc
  set S : Finset G := F.image (fun q : Q => ((q.out : ↥R) : G)⁻¹) with hS
  have hSR : ∀ g ∈ S, g ∈ R := by
    intro g hg
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hg
    exact R.inv_mem (q.out).2
  have hinj : ∀ g ∈ S, ∀ g' ∈ S, GLBConj g L = GLBConj g' L → g = g' := by
    intro g hg g' hg' h
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hg'
    have h1 : GLBConj (q'.out : G) (GLBConj ((q.out : ↥R) : G)⁻¹ L) =
        GLBConj (q'.out : G) (GLBConj ((q'.out : ↥R) : G)⁻¹ L) := by rw [h]
    rw [gLBConj_gLBConj, gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h1
    have hmem : ((q.out : ↥R) : G)⁻¹ * (q'.out : G) ∈ Subgroup.normalizer (L : Set G) :=
      mem_normalizer_iff_gLBConj_eq.2 h1
    have hqq : q = q' := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (by simpa using hmem))
    rw [hqq]
  have hScard : S.card = 9 := by
    rw [hS, Finset.card_image_of_injOn, hF]
    intro q _ q' _ h
    have h1 : (q.out : ↥R) = q'.out := Subtype.ext (inv_injective h)
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', h1]
  have hSne : S.Nonempty := Finset.card_pos.1 (by rw [hScard]; norm_num)
  have hbound := card_iSup_conj_ge hL hLL hRX hR hUR hUL hU S hSR hinj hSne
  rw [hScard] at hbound
  have hE10 : 3 ^ 10 ≤ Nat.card (conjProd R U) := by
    refine hbound.trans (Subgroup.card_le_of_le (iSup₂_le fun g hg => ?_))
    exact gLBConj_le_conjProd (hSR g hg)
  exact kc_trans (kc_of_big_normal hRX hR hER hEN hEel hE10 hA)
    (kc_symm (kc_of_big_normal hRX hR hER hEN hEel hE10 hB))

theorem input31_10L34_holds : Claims1245.Input31_10L34 := by
  intro G _ _ X L hL hLL R hR U V hU hV
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : IsSylowIn 3 L (R ⊓ L) := Claims1245.isSylowIn_inf_of_isSubnormal hR hL.2.1
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 hR.2.1
  have hdvd : (Subgroup.normalizer (L : Set G)).relIndex R ∣ 3 ^ r := by
    rw [← hr]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  rcases k with _ | _ | k
  · rw [pow_zero] at hk
    exact kc_of_normalizes hL hLL hR.1 hR.2.1 (Subgroup.relIndex_eq_one.1 hk) hT hU hV
  · rw [zero_add, pow_one] at hk
    exact kc_index_three hL hLL hR.1 hR.2.1 hT hk hU hV
  · refine kc_index_ge_nine hL hLL hR.1 hR.2.1 hT ?_ hU hV
    rw [hk]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Assembly

section L34Fix

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34 CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.HardMathSupport.Solomon.Coordinator (c25Fix)

theorem card_fix_conjAut_mul_three {k : Type} [Field k] (hk : Nat.card k = 4) {A z : GL (Fin 3) k}
    (hz : z ∈ StatedScalars (Fin 3) k) :
    Nat.card (c25Fix (Subgroup.zpowers (conjAut 3 k A))) * 3 =
      Nat.card (centMod (slPi true 3 (2 ^ 2) k) (A * z)) := by
  haveI := LinearFieldFour.finite_of_card_eq_four hk
  set C := centMod (slPi true 3 (2 ^ 2) k) (A * z) with hC
  set M : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k) := C.comap Matrix.SpecialLinearGroup.toGL
    with hM
  obtain ⟨c₀, rfl⟩ := hz
  have hzc : ∀ g : GL (Fin 3) k, g * Matrix.GeneralLinearGroup.scalar (Fin 3) c₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c₀ * g := fun g =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c₀ g).eq
  have hfix : c25Fix (Subgroup.zpowers (conjAut 3 k A)) = M.map (proj 3 k) := by
    ext p
    rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.mem_c25Fix_zpowers_iff]
    constructor
    · intro hp
      obtain ⟨s, rfl⟩ := proj_surjective 3 k p
      obtain ⟨c, hc⟩ :=
        CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.exists_smul_of_conjAut_fix A s hp
      refine ⟨s, ?_, rfl⟩
      rw [hM, SetLike.mem_coe, Subgroup.mem_comap, hC, mem_centMod_iff_scalar]
      refine ⟨(mem_slPi_true _).2 s.2, Matrix.GeneralLinearGroup.scalar (Fin 3) c⁻¹,
        ⟨c⁻¹, rfl⟩, ?_⟩
      have key : Matrix.SpecialLinearGroup.toGL s * A =
          Matrix.GeneralLinearGroup.scalar (Fin 3) c⁻¹ * A * Matrix.SpecialLinearGroup.toGL s := by
        apply Units.ext
        simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
          Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
        rw [Matrix.mul_assoc, hc, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, smul_smul,
          Units.inv_mul, one_smul]
      calc Matrix.SpecialLinearGroup.toGL s * (A * Matrix.GeneralLinearGroup.scalar (Fin 3) c₀) *
            (Matrix.SpecialLinearGroup.toGL s)⁻¹
          = (Matrix.SpecialLinearGroup.toGL s * A) * Matrix.GeneralLinearGroup.scalar (Fin 3) c₀ *
            (Matrix.SpecialLinearGroup.toGL s)⁻¹ := by group
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) c⁻¹ * A *
            (Matrix.SpecialLinearGroup.toGL s * Matrix.GeneralLinearGroup.scalar (Fin 3) c₀) *
            (Matrix.SpecialLinearGroup.toGL s)⁻¹ := by rw [key]; group
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) c⁻¹ *
            (A * Matrix.GeneralLinearGroup.scalar (Fin 3) c₀) := by rw [hzc]; group
    · rintro ⟨s, hs, rfl⟩
      exact InputsL34.conjAut_fix_of_mem_centMod hk ⟨c₀, rfl⟩ hs rfl
  have hMC : M.map Matrix.SpecialLinearGroup.toGL = C := by
    refine le_antisymm (Subgroup.map_comap_le _ _) fun l hl => ?_
    have hdet : (l : Matrix (Fin 3) (Fin 3) k).det = 1 :=
      (mem_slPi_true _).1 (mem_centMod_iff_scalar.1 hl).1
    refine ⟨⟨l, hdet⟩, ?_, Units.ext rfl⟩
    show Matrix.SpecialLinearGroup.toGL ⟨(l : Matrix (Fin 3) (Fin 3) k), hdet⟩ ∈ C
    convert hl using 1
    exact Units.ext rfl
  have hMcard : Nat.card M = Nat.card C := by
    rw [← hMC, Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective]
  set f : ↥M →* projectiveSL 3 k := (proj 3 k).comp M.subtype with hf
  have hrange : f.range = M.map (proj 3 k) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hsc : scalars 3 k ≤ M := by
    intro s hs
    rw [hM, Subgroup.mem_comap, hC, mem_centMod_iff_scalar]
    refine ⟨(mem_slPi_true _).2 s.2, 1, Subgroup.one_mem _, ?_⟩
    obtain ⟨c, -, hc⟩ := mem_scalars.1 hs
    have hs' : Matrix.SpecialLinearGroup.toGL s = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hc, Matrix.GeneralLinearGroup.coe_scalar]
    rw [one_mul, hs', ← (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c _).eq,
      mul_inv_cancel_right]
  have hker : Nat.card f.ker = 3 := by
    have he : f.ker.map M.subtype = scalars 3 k := by
      ext s
      constructor
      · rintro ⟨m, hm, rfl⟩
        rw [← ker_proj]
        exact hm
      · intro hs
        exact ⟨⟨s, hsc hs⟩, MonoidHom.mem_ker.2 (proj_eq_one_iff.2 hs), rfl⟩
    rw [← Subgroup.card_map_of_injective M.subtype_injective, he,
      LinearThreeFourFixedNine.card_scalars hk]
  have h1 := CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range f
  rw [hfix, ← hrange, ← hMcard]
  change Nat.card f.range * 3 = Nat.card ↥M
  rw [h1, hker, mul_comm]

theorem card_fix_proj {k : Type} [Field k] (hk : Nat.card k = 4) {φ : MulAut (projectiveSL 3 k)}
    (hφ : φ ^ 3 = 1) (hφ1 : φ ≠ 1) :
    Nat.card (c25Fix (Subgroup.zpowers φ)) ∣ 9 ∨ Nat.card (c25Fix (Subgroup.zpowers φ)) = 60 ∨
      Nat.card (c25Fix (Subgroup.zpowers φ)) ∣ 21 := by
  haveI := LinearFieldFour.finite_of_card_eq_four hk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlin : φ ∈ linearAutGroup 3 k := by
    by_contra hD
    obtain ⟨σ, hσ, -⟩ := CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent
      (n := 3) le_rfl φ hφ hD
    have := (CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three
      (p := 2) (f := 2) Nat.prime_two (by norm_num) (by rw [hk]; norm_num) hσ).1
    omega
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 hlin
  have hAs : A ∉ StatedScalars (Fin 3) k := by
    rintro ⟨c, rfl⟩
    exact hφ1 (conjAut_scalar c)
  have hA3 : A ^ 3 ∈ StatedScalars (Fin 3) k := by
    have h : conjAut 3 k (A ^ 3) = 1 := by rw [map_pow, hφ]
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) le_rfl (A ^ 3) 1
      (by rw [map_one, mul_one, h])
    exact ⟨c, hc⟩
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have hu3 : (u : k) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, Inputs1114.units_pow_three_of_card_four hk u, Units.val_one]
  have hτ1 : (u : k) ≠ 1 := val_ne_one hu
  have hK : PiField true 2 2 k := ⟨Nat.prime_two, by norm_num, by rw [hk]; rfl⟩
  have hq : ModThree true (2 ^ 2) := by change 2 ^ 2 % 3 = 1; norm_num
  have hπ : true = false → UnitaryFieldData 2 2 k := fun h => absurd h (by decide)
  have hπ' : true = false → ModThree false (2 ^ 2) := fun h => absurd h (by decide)
  have hzPi : zPi true 3 (2 ^ 2) k = glPi true 3 (2 ^ 2) k ⊓ StatedScalars (Fin 3) k :=
    zPi_eq hπ hπ' hu3 hτ1
  have hxZ : A ∉ zPi true 3 (2 ^ 2) k := by rw [hzPi]; exact fun h => hAs h.2
  have hx3 : A ^ 3 ∈ zPi true 3 (2 ^ 2) k := by rw [hzPi]; exact ⟨mem_glPi_true _ _, hA3⟩
  obtain ⟨y, ⟨z, hz, rfl⟩, hcase⟩ := rank3II_4_10_one hK hq hu3 hτ1 (mem_glPi_true _ A) hxZ hx3
  have hzs : z ∈ StatedScalars (Fin 3) k := by rw [hzPi] at hz; exact hz.2
  have hmain := card_fix_conjAut_mul_three hk (A := A) hzs
  set C := slPi true 3 (2 ^ 2) k ⊓ Subgroup.centralizer {A * z} with hC
  have hCc : C ≤ centMod (slPi true 3 (2 ^ 2) k) (A * z) := centralizer_le_centMod _ _
  rcases hcase with ⟨-, ⟨e⟩, hrel⟩ | ⟨-, ⟨e⟩, hcm⟩ | ⟨-, -, -, -, hcard, w, hwL, hw3, -, hcm, -⟩
  ·
    left
    have hC9 : Nat.card C = 9 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod]
      have : Nat.card (Multiplicative (ZMod (qSubPi true (2 ^ 2)))) = 3 := by
        rw [Nat.card_congr Multiplicative.toAdd]
        change Nat.card (ZMod 3) = 3
        rw [Nat.card_zmod]
      rw [this]
    have h1 := Subgroup.relIndex_mul_card (H := C) (K := centMod (slPi true 3 (2 ^ 2) k) (A * z))
    rw [hrel, inf_eq_left.2 hCc, hC9] at h1
    rw [← h1] at hmain
    have : Nat.card (c25Fix (Subgroup.zpowers (conjAut 3 k A))) = 9 := by omega
    rw [this]
  ·
    right; left
    haveI : Fintype k := Fintype.ofFinite k
    have hk' : Fintype.card k = 4 := by rw [← Nat.card_eq_fintype_card, hk]
    have h180 : Nat.card C = 180 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (⊤ : Subgroup (GL (Fin 2) k)) = 180
      rw [Subgroup.card_top, Matrix.card_GL_field, hk', Fin.prod_univ_two]
      norm_num
    have h180' : Nat.card (centMod (slPi true 3 (2 ^ 2) k) (A * z)) = 180 := by
      rw [hcm]; exact h180
    rw [h180'] at hmain
    omega
  ·
    right; right
    have h21 : Nat.card C = 21 := by rw [hcard]; rfl
    have hwM : w ∈ centMod (slPi true 3 (2 ^ 2) k) (A * z) := by
      rw [hcm]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    obtain ⟨-, z', ⟨c', rfl⟩, hz'⟩ := mem_centMod_iff_scalar.1 hwM
    set Z' := Matrix.GeneralLinearGroup.scalar (Fin 3) c' with hZ'
    have hZi : ∀ g : GL (Fin 3) k, g * Z'⁻¹ = Z'⁻¹ * g := fun g =>
      ((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c' g).inv_right).eq
    set yy := A * z with hyy
    have hwy : w⁻¹ * yy * w = Z'⁻¹ * yy := by
      calc w⁻¹ * yy * w = w⁻¹ * (Z'⁻¹ * (Z' * yy)) * w := by group
        _ = w⁻¹ * (Z'⁻¹ * (w * yy * w⁻¹)) * w := by rw [hz']
        _ = w⁻¹ * (Z'⁻¹ * w) * yy := by group
        _ = w⁻¹ * (w * Z'⁻¹) * yy := by rw [hZi w]
        _ = Z'⁻¹ * yy := by group
    have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (C : Set (GL (Fin 3) k)) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_normalizer_fintype fun l hl => ?_
      obtain ⟨hlL, hly⟩ := Subgroup.mem_inf.1 hl
      rw [Subgroup.mem_centralizer_singleton_iff] at hly
      refine Subgroup.mem_inf.2 ⟨(slPi true 3 (2 ^ 2) k).mul_mem
        ((slPi true 3 (2 ^ 2) k).mul_mem hwL hlL) ((slPi true 3 (2 ^ 2) k).inv_mem hwL), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc w * l * w⁻¹ * yy = w * l * (w⁻¹ * yy * w) * w⁻¹ := by group
        _ = w * l * (Z'⁻¹ * yy) * w⁻¹ := by rw [hwy]
        _ = w * (Z'⁻¹ * l) * yy * w⁻¹ := by rw [← hZi l]; group
        _ = w * Z'⁻¹ * (l * yy) * w⁻¹ := by group
        _ = w * Z'⁻¹ * (yy * l) * w⁻¹ := by rw [hly]
        _ = w * (Z'⁻¹ * yy) * l * w⁻¹ := by group
        _ = w * (w⁻¹ * yy * w) * l * w⁻¹ := by rw [hwy]
        _ = yy * (w * l * w⁻¹) := by group
    have hcardM : Nat.card (centMod (slPi true 3 (2 ^ 2) k) yy) ∣ 63 := by
      have h := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hwN
      rw [sup_comm, ← hcm, Nat.card_zpowers, hw3, h21] at h
      exact Dvd.intro _ h
    rw [← hmain] at hcardM
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 3) (by simpa using hcardM)

theorem exists_sylow_of_commute {k : Type} [Field k] (hk : Nat.card k = 4) {t : projectiveSL 3 k}
    (ht1 : t ≠ 1) (ht3 : t ^ 3 = 1) :
    ∃ S : Subgroup (projectiveSL 3 k), Nat.card S = 9 ∧ ∀ c, c * t = t * c → c ∈ S := by
  haveI := LinearFieldFour.finite_of_card_eq_four hk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX := InputsL34.isLThreeFour_projectiveSL hk
  have hp : IsPGroup 3 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime ht3 ht1, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hS9 := InputsL34.card_sylow_of_isLThreeFour hX S
  exact ⟨S, hS9, fun c hc =>
    Inputs1114.l34_mem_of_commute hX hS9 (hS (Subgroup.mem_zpowers t)) ht1 hc⟩

theorem exists_inner_of_card_nine {k : Type} [Field k] (hk : Nat.card k = 4)
    {A : Subgroup (MulAut (projectiveSL 3 k))} (hA : Nat.card A = 9) :
    ∃ p : projectiveSL 3 k, p ≠ 1 ∧ MulAut.conj p ∈ A := by
  haveI := LinearFieldFour.finite_of_card_eq_four hk
  haveI : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  set I := (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range with hIdef
  haveI hIn : I.Normal := ⟨fun n hn g => by
    obtain ⟨p, rfl⟩ := hn
    refine ⟨g p, MulEquiv.ext fun x => ?_⟩
    simp only [MulAut.conj_apply, MulAut.mul_apply]
    rw [map_mul, map_mul, map_inv]
    simp⟩
  have hI : Nat.card I = 20160 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (conj_injective hk)).toEquiv, card_projectiveSL hk]
  have hq : Nat.card (MulAut (projectiveSL 3 k) ⧸ I) = 12 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup I
    rw [card_mulAut hk, hI] at this
    omega
  set f : ↥A →* MulAut (projectiveSL 3 k) ⧸ I := (QuotientGroup.mk' I).comp A.subtype with hf
  have h1 := CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range f
  have hA' : Nat.card ↥A = 9 := hA
  have hr12 : Nat.card f.range ∣ 12 := hq ▸ Subgroup.card_subgroup_dvd_card f.range
  have hr9 : Nat.card f.range ∣ 9 := by rw [← hA', h1]; exact Dvd.intro_left _ rfl
  have hr3 : Nat.card f.range ≤ 3 := by
    have := Nat.dvd_gcd hr9 hr12
    have h3 : Nat.gcd 9 12 = 3 := by norm_num
    rw [h3] at this
    exact Nat.le_of_dvd (by norm_num) this
  have hk3 : 1 < Nat.card f.ker := by
    rw [hA'] at h1
    by_contra h
    have : Nat.card f.ker ≤ 1 := by omega
    nlinarith
  haveI : Nontrivial f.ker := Finite.one_lt_card_iff_nontrivial.1 hk3
  obtain ⟨⟨a, ha⟩, ha1⟩ := exists_ne (1 : f.ker)
  have haI : (a : MulAut (projectiveSL 3 k)) ∈ I := by
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    exact ha
  obtain ⟨p, hp⟩ := haI
  refine ⟨p, fun h => ha1 ?_, hp ▸ a.2⟩
  apply Subtype.ext
  apply Subtype.ext
  change (a : MulAut (projectiveSL 3 k)) = 1
  rw [← hp, h, map_one]

end L34Fix

section Small

theorem isSolvable_of_card_dvd' {H : Type} [Group H] [Finite H] {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card H ∣ p ^ a * q ^ b) : IsSolvable H := by
  have := Fintype.ofFinite H
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hk₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hq).1 hk₂
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact hk.symm)

theorem not_isSolvable_of_simple {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hperf : commutator S = ⊤) : ¬ IsSolvable S := fun hsol => by
  haveI : Group.IsPerfect S := ⟨hperf⟩
  exact Group.IsPerfect.not_isSolvable S hsol

theorem isAltType_five_of_card_dvd {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hperf : commutator S = ⊤) (h : Nat.card S ∣ 60) : IsAltType 5 S := by
  have hns := not_isSolvable_of_simple hperf
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hle : Nat.card S ≤ 60 := Nat.le_of_dvd (by norm_num) h
  have hcases : Nat.card S ∣ 2 ^ 2 * 3 ^ 1 ∨ Nat.card S ∣ 2 ^ 2 * 5 ^ 1 ∨ Nat.card S ∣ 3 ^ 1 * 5 ^ 1 ∨
      Nat.card S = 30 ∨ Nat.card S = 60 := by
    interval_cases hc : Nat.card S <;> omega
  rcases hcases with h1 | h1 | h1 | h1 | h1
  · exact absurd (isSolvable_of_card_dvd' Nat.prime_two Nat.prime_three (by norm_num) h1) hns
  · exact absurd (isSolvable_of_card_dvd' Nat.prime_two (by norm_num) (by norm_num) h1) hns
  · exact absurd (isSolvable_of_card_dvd' Nat.prime_three (by norm_num) (by norm_num) h1) hns
  · exfalso
    obtain ⟨N, hN, hN1, hNT⟩ := CFSG.GroupTheory.order_thirty_not_simple h1
    rcases hN.eq_bot_or_eq_top with h' | h'
    · exact hN1 h'
    · exact hNT h'
  · exact CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h1

theorem not_card_dvd_63 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hperf : commutator S = ⊤) (h : Nat.card S ∣ 3 ^ 2 * 7 ^ 1) : False :=
  not_isSolvable_of_simple hperf (isSolvable_of_card_dvd' Nat.prime_three (by norm_num) (by norm_num) h)

end Small

section Section

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.Coordinator (conj_mem_gLAPPrimeCoreOf_of_mem_normalizer)

noncomputable def psiK (K : Subgroup G) : ↥K →* barOf 3 K ⧸ Subgroup.center (barOf 3 K) :=
  (QuotientGroup.mk' (Subgroup.center (barOf 3 K))).comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K))

theorem psiK_surjective (K : Subgroup G) : Function.Surjective (psiK K) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem comm_mem_core_of_psiK {K : Subgroup G} {q : ↥K} (hq : psiK K q = 1) (k : ↥K) :
    (q : G) * k * (q : G)⁻¹ * (k : G)⁻¹ ∈ GLAPPrimeCoreOf 3 K := by
  have hc : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) q : barOf 3 K) ∈ Subgroup.center (barOf 3 K) :=
    (QuotientGroup.eq_one_iff _).1 hq
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) (q * k * q⁻¹ * k⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [(Subgroup.mem_center_iff.1 hc _).symm]
    group
  exact ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩

theorem card_dvd_card_image {X K Y Q : Subgroup G} (hK : GLAPComponent 3 X K) (hYK : Y ≤ K)
    (hQ : GLAPComponent 3 Y Q) :
    Nat.card (barOf 3 Q ⧸ Subgroup.center (barOf 3 Q)) ∣
      Nat.card ((Q.subgroupOf K).map (psiK K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQK : Q ≤ K := hQ.1.trans hYK
  set θ : ↥Q →* barOf 3 K ⧸ Subgroup.center (barOf 3 K) := (psiK K).comp (Subgroup.inclusion hQK)
    with hθ
  set χ : ↥Q →* barOf 3 Q ⧸ Subgroup.center (barOf 3 Q) := psiK Q with hχ
  have hrange : θ.range = (Q.subgroupOf K).map (psiK K) := by
    ext w
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨Subgroup.inclusion hQK q, Subgroup.mem_subgroupOf.2 q.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, Subgroup.mem_subgroupOf.1 hk⟩, rfl⟩
  have hle : θ.ker ≤ χ.ker := by
    intro q hq
    rw [MonoidHom.mem_ker] at hq ⊢
    have hcK := comm_mem_core_of_psiK (K := K) hq
    have hNP : CFSG.HardMathSupport.Solomon.UniquenessMaximal.NormalPrime Q
        (GLAPPrimeCoreOf 3 K ⊓ Q) := by
      refine ⟨inf_le_right, fun y hy n hn => ⟨conj_mem_gLAPPrimeCoreOf_of_mem_normalizer
        (Subgroup.le_normalizer (hQK hy)) hn.1, Q.mul_mem (Q.mul_mem hy hn.2) (Q.inv_mem hy)⟩, ?_⟩
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hd => ?_
      exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
        (hd.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hcore := CFSG.HardMathSupport.Solomon.UniquenessMaximal.le_glaPPrimeCoreOf_of_normalPrime hNP
    have hcen : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Q) q : barOf 3 Q) ∈
        Subgroup.center (barOf 3 Q) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨q', rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥Q) w
      have h1 : (q : G) * q' * (q : G)⁻¹ * (q' : G)⁻¹ ∈ GLAPPrimeCoreOf 3 Q :=
        hcore ⟨hcK (Subgroup.inclusion hQK q'), Q.mul_mem (Q.mul_mem (Q.mul_mem q.2 q'.2)
          (Q.inv_mem q.2)) (Q.inv_mem q'.2)⟩
      obtain ⟨y, hy, hyq⟩ := h1
      have hyeq : y = q * q' * q⁻¹ * q'⁻¹ := Subtype.ext (by simpa using hyq)
      have h2 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥Q) (q * q' * q⁻¹ * q'⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (hyeq ▸ hy)
      simp only [map_mul, map_inv] at h2
      calc QuotientGroup.mk' (GLAPPrimeCore 3 ↥Q) q' * QuotientGroup.mk' (GLAPPrimeCore 3 ↥Q) q =
          (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Q) q * QuotientGroup.mk' (GLAPPrimeCore 3 ↥Q) q' *
            (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Q) q)⁻¹ *
            (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Q) q')⁻¹)⁻¹ *
          (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Q) q * QuotientGroup.mk' (GLAPPrimeCore 3 ↥Q) q') := by
            group
        _ = QuotientGroup.mk' (GLAPPrimeCore 3 ↥Q) q * QuotientGroup.mk' (GLAPPrimeCore 3 ↥Q) q' := by
            rw [h2, inv_one, one_mul]
    rw [hχ, psiK, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hcen
  have hθc := CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range θ
  have hχc := CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range χ
  have hχr : χ.range = ⊤ := MonoidHom.range_eq_top.2 (psiK_surjective Q)
  rw [hχr, Subgroup.card_top] at hχc
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  rw [← hrange]
  rw [hθc, hm, mul_assoc] at hχc
  have hpos : 0 < Nat.card θ.ker := Nat.card_pos
  have := Nat.eq_of_mul_eq_mul_left hpos hχc
  exact Dvd.intro_left _ this.symm

end Section

section I2320

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open CFSG.HardMathSupport.Solomon.Coordinator (c25Fix conj_mem_gLAPPrimeCoreOf_of_mem_normalizer)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (dQ gammaClBelow)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

noncomputable def phiK (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) :=
  (quotientCenterAut' (barOf 3 K)).comp (barAut 3 K)

theorem phiK_psiK {K : Subgroup G} (b : ↥(Subgroup.normalizer (K : Set G))) (y : ↥K) :
    phiK K b (psiK K y) = psiK K (K.normalizerMonoidHom b y) := by
  simp only [phiK, psiK, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [InputsL34.quotientCenterAut'_mk, barAut_mk]

theorem mem_dQ_of_phiK {X K : Subgroup G} (hK : GLAPComponent 3 X K)
    {b : ↥(Subgroup.normalizer (K : Set G))} (h : phiK K b = 1) : (b : G) ∈ dQ K := by
  have h1 : barAut 3 K b = 1 :=
    quotientCenterAut'_injective (barOf_perfect hK) (by rw [map_one]; exact h)
  exact (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns.mem_centralizerQuot_iff_barAut' 3
    (J := K) b).2 h1

theorem centralizer_zpowers' (x : G) :
    Subgroup.centralizer (Subgroup.zpowers x : Set G) = Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem perfect_quot {S : Type} [Group S] (hS : commutator S = ⊤) (N : Subgroup S) [N.Normal] :
    commutator (S ⧸ N) = ⊤ := by
  have hsurj := QuotientGroup.mk'_surjective N
  rw [_root_.commutator_def, ← Subgroup.map_top_of_surjective _ hsurj, ← Subgroup.map_commutator,
    ← _root_.commutator_def, hS]

theorem moreover_clause {X K Q : Subgroup G} {x : G} (hK : GLAPComponent 3 X K)
    (hL : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx3 : x ^ 3 = 1)
    (hQ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) Q) :
    IsLThreeFour (barOf 3 Q ⧸ Subgroup.center (barOf 3 Q)) ∨
      IsAltType 5 (barOf 3 Q ⧸ Subgroup.center (barOf 3 Q)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hqQ := CFSG.HardMathSupport.Solomon.UniquenessMaximal.isQuasisimple_quotient_of_glaPComponent
    Nat.prime_three hQ
  haveI : IsSimpleGroup (barOf 3 Q ⧸ Subgroup.center (barOf 3 Q)) := hqQ.2
  have hperf : commutator (barOf 3 Q ⧸ Subgroup.center (barOf 3 Q)) = ⊤ := perfect_quot hqQ.1 _
  set b : ↥(Subgroup.normalizer (K : Set G)) := ⟨x, hxN⟩ with hb
  by_cases hφ : phiK K b = 1
  ·
    left
    have hxd : x ∈ dQ K := mem_dQ_of_phiK hK hφ
    have hzd : Subgroup.zpowers x ≤ dQ K := Subgroup.zpowers_le.2 hxd
    have hz3 : IsPGroup 3 (Subgroup.zpowers x) := by
      by_cases hx1 : x = 1
      · rw [hx1, Subgroup.zpowers_one_eq_bot]; exact IsPGroup.of_bot
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, pow_one])
    obtain ⟨J, hJ, -, huniq, -, -, ⟨e⟩⟩ :=
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.ia_cover
        CFSG.HardMathSupport.Solomon.UniquenessMaximal.coverStmt hK hz3 hzd
    rw [centralizer_zpowers'] at hJ huniq
    have hQJ : Q = J := huniq Q hQ
    subst hQJ
    exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsLThreeFour.of_mulEquiv
      (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hL
  ·
    right
    obtain ⟨k, _, hk, ⟨e⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hL
    haveI := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
    set φ' : MulAut (projectiveSL 3 k) := MulAut.congr e (phiK K b) with hφ'
    have hφ'3 : φ' ^ 3 = 1 := by
      rw [hφ', ← map_pow, ← map_pow]
      have : b ^ 3 = 1 := Subtype.ext (by simp [hb, hx3])
      rw [this, map_one, map_one]
    have hφ'1 : φ' ≠ 1 := by
      intro h
      apply hφ
      have := congrArg (MulAut.congr e).symm h
      rwa [hφ', MulEquiv.symm_apply_apply, map_one] at this
    have himg : ((Q.subgroupOf K).map (psiK K)).map e.toMonoidHom ≤ c25Fix (Subgroup.zpowers φ') := by
      rintro _ ⟨w, ⟨q, hq, rfl⟩, rfl⟩
      rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.mem_c25Fix_zpowers_iff, hφ']
      show e (phiK K b (e.symm (e (psiK K q)))) = e (psiK K q)
      rw [MulEquiv.symm_apply_apply, phiK_psiK]
      congr 2
      apply Subtype.ext
      have hqx : (q : G) * x = x * q :=
        Subgroup.mem_centralizer_singleton_iff.1 (hQ.1 (Subgroup.mem_subgroupOf.1 hq)).2
      show x * (q : G) * x⁻¹ = q
      rw [← hqx, mul_inv_cancel_right]
    have hdvd1 := card_dvd_card_image hK (inf_le_left : K ⊓ Subgroup.centralizer ({x} : Set G) ≤ K) hQ
    have hdvd2 : Nat.card ((Q.subgroupOf K).map (psiK K)) ∣ Nat.card (c25Fix (Subgroup.zpowers φ')) := by
      rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom)
        (by rw [MulEquiv.coe_toMonoidHom]; exact e.injective)]
      exact Subgroup.card_dvd_of_le himg
    have hdvd := hdvd1.trans hdvd2
    rcases card_fix_proj hk hφ'3 hφ'1 with h9 | h60 | h21
    · exact absurd (not_card_dvd_63 hperf (hdvd.trans (h9.trans (by norm_num)))) id
    · exact isAltType_five_of_card_dvd hperf (h60 ▸ hdvd)
    · exact absurd (not_card_dvd_63 hperf (hdvd.trans (h21.trans (by norm_num)))) id

theorem bTerm_le {X K B : Subgroup G} (hK : GLAPComponent 3 X K)
    (hL : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K))) (hBel : IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (hfaith : ∀ x ∈ B, x ∈ dQ K → x = 1) :
    GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer (B : Set G)) ⊔
      GLAPLayer 3 (K ⊓ Subgroup.centralizer (B : Set G)) ≤ GLAPPrimeCoreOf 3 K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, _, hk, ⟨e⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hL
  haveI := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  set Θ : ↥B →* MulAut (projectiveSL 3 k) :=
    (MulAut.congr e).toMonoidHom.comp ((phiK K).comp (Subgroup.inclusion hBN)) with hΘ
  have hΘinj : Function.Injective Θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have h1 : phiK K (Subgroup.inclusion hBN b) = 1 := by
      have := congrArg (MulAut.congr e).symm hb
      rwa [hΘ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        map_one] at this
    have h2 := mem_dQ_of_phiK hK h1
    exact Subgroup.mem_bot.2 (Subtype.ext (hfaith b b.2 h2))
  have hA9 : Nat.card Θ.range = 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΘinj).toEquiv]
    exact hB9
  obtain ⟨p, hp1, hpA⟩ := exists_inner_of_card_nine hk hA9
  obtain ⟨b, hb⟩ := hpA
  have hp3 : p ^ 3 = 1 := by
    apply CFSG.RankThree.PartTwo.KFacts.L34.conj_injective hk
    rw [map_pow, ← hb, ← map_pow]
    have : b ^ 3 = 1 := Subtype.ext (by simpa using hBel.2 b.1 b.2)
    rw [this, map_one, map_one]
  obtain ⟨S, hS9, hS⟩ := exists_sylow_of_commute hk hp1 hp3
  set Y := K ⊓ Subgroup.centralizer (B : Set G) with hY
  have hYK : Y ≤ K := inf_le_left
  have himg : ∀ y : ↥K, (y : G) ∈ Y → e (psiK K y) ∈ S := by
    intro y hy
    refine hS _ ?_
    have hfix : MulAut.conj p (e (psiK K y)) = e (psiK K y) := by
      rw [← hb]
      show e (phiK K (Subgroup.inclusion hBN b) (e.symm (e (psiK K y)))) = e (psiK K y)
      rw [MulEquiv.symm_apply_apply, phiK_psiK]
      congr 2
      apply Subtype.ext
      have hyb : (y : G) * b = b * y :=
        (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 b b.2).symm
      show (b : G) * y * (b : G)⁻¹ = y
      rw [← hyb, mul_inv_cancel_right]
    rw [MulAut.conj_apply] at hfix
    calc e (psiK K y) * p = p * e (psiK K y) * p⁻¹ * p := by rw [hfix]
      _ = p * e (psiK K y) := by group
  have hcore : ∀ y : ↥K, (y : G) ∈ Y → Nat.Coprime (orderOf y) 3 → (y : G) ∈ GLAPPrimeCoreOf 3 K := by
    intro y hy hcop
    have h1 : e (psiK K y) = 1 := by
      have hdvd1 : orderOf (e (psiK K y)) ∣ orderOf y := by
        rw [MulEquiv.orderOf_eq]
        exact orderOf_map_dvd _ _
      have hdvd2 : orderOf (e (psiK K y)) ∣ 9 := by
        have := orderOf_dvd_natCard (⟨e (psiK K y), himg y hy⟩ : ↥S)
        rw [hS9] at this
        simpa using this
      have hc : Nat.Coprime (orderOf (e (psiK K y))) 3 := Nat.Coprime.coprime_dvd_left hdvd1 hcop
      have h9 : Nat.Coprime (orderOf (e (psiK K y))) 9 := by
        rw [show (9 : ℕ) = 3 ^ 2 by norm_num]; exact Nat.Coprime.pow_right 2 hc
      exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h9 hdvd2)
    have h2 : psiK K y = 1 := by
      have := congrArg e.symm h1
      rwa [MulEquiv.symm_apply_apply, map_one] at this
    have hc : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) y : barOf 3 K) ∈ Subgroup.center (barOf 3 K) :=
      (QuotientGroup.eq_one_iff _).1 h2
    obtain ⟨n, hn⟩ := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.isPGroup_center_barOf K)
      ⟨_, hc⟩
    have hn' : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) y) ^ (3 ^ n) = 1 := by
      simpa using congrArg Subtype.val hn
    have hdvd1 : orderOf (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) y) ∣ orderOf y :=
      orderOf_map_dvd _ _
    have hdvd2 := orderOf_dvd_of_pow_eq_one hn'
    have hc3 : Nat.Coprime (orderOf (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) y)) (3 ^ n) :=
      Nat.Coprime.pow_right n (Nat.Coprime.coprime_dvd_left hdvd1 hcop)
    have h3 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) y = 1 :=
      orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hc3 hdvd2)
    exact ⟨y, (QuotientGroup.eq_one_iff _).1 h3, rfl⟩
  refine sup_le ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    have hyK : (y : G) ∈ K := hYK y.2
    refine hcore ⟨y, hyK⟩ y.2 ?_
    have hcard : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥Y) := by
      have h := not_dvd_card_glaPPrimeCoreOf Nat.prime_three Y
      rwa [GLAPPrimeCoreOf, Subgroup.card_map_of_injective Y.subtype_injective] at h
    have hdvd : orderOf (⟨y, hy⟩ : ↥(GLAPPrimeCore 3 ↥Y)) ∣ Nat.card (GLAPPrimeCore 3 ↥Y) :=
      orderOf_dvd_natCard _
    have hord : orderOf (⟨y, hyK⟩ : ↥K) = orderOf (⟨y, hy⟩ : ↥(GLAPPrimeCore 3 ↥Y)) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    rw [hord]
    exact (Nat.Coprime.coprime_dvd_left hdvd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hcard).symm)
  · refine sSup_le fun Q hQ => ?_
    exfalso
    have hqQ := CFSG.HardMathSupport.Solomon.UniquenessMaximal.isQuasisimple_quotient_of_glaPComponent
      Nat.prime_three hQ
    haveI : IsSimpleGroup (barOf 3 Q ⧸ Subgroup.center (barOf 3 Q)) := hqQ.2
    have hperf : commutator (barOf 3 Q ⧸ Subgroup.center (barOf 3 Q)) = ⊤ := perfect_quot hqQ.1 _
    have hdvd1 := card_dvd_card_image hK hYK hQ
    have hle : ((Q.subgroupOf K).map (psiK K)).map e.toMonoidHom ≤ S := by
      rintro _ ⟨w, ⟨q, hq, rfl⟩, rfl⟩
      exact himg q (hQ.1 (Subgroup.mem_subgroupOf.1 hq))
    have hdvd2 : Nat.card ((Q.subgroupOf K).map (psiK K)) ∣ 9 := by
      rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom)
        (by rw [MulEquiv.coe_toMonoidHom]; exact e.injective), ← hS9]
      exact Subgroup.card_dvd_of_le hle
    exact not_card_dvd_63 hperf (hdvd1.trans (hdvd2.trans (by norm_num)))

theorem input23_20_W_of_cover
    (hcov : CFSG.HardMathSupport.Solomon.UniquenessMaximal.InputL34Cover) : Input23_20_W := by
  intro G _ _ X K B hK hL hBX hBel hB2 hBN hnot
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB9 : Nat.card B = 9 := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hBel.isPGroup
    have h1 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (le_refl B) hBel hm
    obtain ⟨F, hFB, hFel, hFc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) B
    rw [hB2] at h1 hFc
    have h2 : Nat.card F ≤ Nat.card B := Subgroup.card_le_of_le hFB
    rw [hm] at h2 ⊢
    rw [hFc] at h2
    have hm2 : m = 2 := by
      have : 2 ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
      omega
    rw [hm2]; norm_num
  refine ⟨?_, fun x hx _ Q hQ => moreover_clause hK hL (hBN hx) (hBel.2 x hx) hQ⟩
  set W := ⨆ (x : G) (_ : x ∈ B ∧ x ≠ 1),
    (GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) ⊔
      GLAPLayer 3 (K ⊓ Subgroup.centralizer ({x} : Set G))) with hW
  have hterm : ∀ x ∈ B, x ≠ 1 → GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) ⊔
      GLAPLayer 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) ≤ W := fun x hx hx1 =>
    le_iSup₂_of_le (f := fun (x : G) (_ : x ∈ B ∧ x ≠ 1) =>
      (GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) ⊔
        GLAPLayer 3 (K ⊓ Subgroup.centralizer ({x} : Set G)))) x ⟨hx, hx1⟩ le_rfl
  have hz3 : ∀ x ∈ B, IsPGroup 3 (Subgroup.zpowers x) := fun x hx => by
    by_cases hx1 : x = 1
    · rw [hx1, Subgroup.zpowers_one_eq_bot]; exact IsPGroup.of_bot
    · exact IsPGroup.of_card (n := 1)
        (by rw [Nat.card_zpowers, orderOf_eq_prime (hBel.2 x hx) hx1, pow_one])
  by_cases hd : ∃ x₀ ∈ B, x₀ ≠ 1 ∧ x₀ ∈ dQ K
  · obtain ⟨x₀, hx₀B, hx₀1, hx₀d⟩ := hd
    obtain ⟨J, hJ, hKJ, -, -⟩ := CFSG.HardMathSupport.Solomon.UniquenessMaximal.coverStmt G X K
      (Subgroup.zpowers x₀) hK (hz3 x₀ hx₀B) (Subgroup.zpowers_le.2 hx₀d)
    rw [centralizer_zpowers'] at hJ
    have hJW : J ≤ W := (le_sSup hJ : J ≤ GLAPLayer 3 _).trans (le_sup_right.trans (hterm x₀ hx₀B hx₀1))
    exact hKJ.trans (sup_le_sup_right hJW _)
  · push Not at hd
    have hfaith : ∀ x ∈ B, x ∈ dQ K → x = 1 := fun x hx hxd => by
      by_contra h
      exact hd x hx h hxd
    have hKbar := Lemma1111.barOf_L34_or_SL34 hcov hK hL
    rcases CFSG.HardMathSupport.Solomon.UniquenessMaximal.input23_20_proved G X K B hK hKbar hBX hBel
      hBN with h | ⟨hin, -⟩
    · refine h.trans (sup_le ?_ le_sup_right)
      refine iSup₂_le fun E hE => ?_
      obtain ⟨hEB, hrk⟩ := hE
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank, CFSG.SectionRank.pRank_coe_eq_openPRank, hB2] at hrk
      by_cases hEeq : E = B
      · rw [hEeq]
        exact (bTerm_le hK hL hBel hB9 hBN hfaith).trans le_sup_right
      ·
        obtain ⟨F, hFE, -, hFc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) E
        have hE1 : E ≠ ⊥ := by
          intro hbot
          rw [hbot, le_bot_iff] at hFE
          rw [hFE, Subgroup.card_bot] at hFc
          have : 3 ^ 1 ≤ 3 ^ CFSG.Open.pRank 3 E := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
        have hxB : (x : G) ∈ B := hEB x.2
        have hEx : E = Subgroup.zpowers (x : G) := by
          have hdvd : Nat.card E ∣ 9 := hB9 ▸ Subgroup.card_dvd_of_le hEB
          have hne9 : Nat.card E ≠ 9 := fun h9 =>
            hEeq (Subgroup.eq_of_le_of_card_ge hEB (by rw [hB9, h9]))
          have hzx : Nat.card (Subgroup.zpowers (x : G)) = 3 := by
            rw [Nat.card_zpowers]
            exact orderOf_eq_prime (hBel.2 x hxB) (fun h => hx1 (Subtype.ext h))
          have hle : Subgroup.zpowers (x : G) ≤ E := Subgroup.zpowers_le.2 x.2
          have h3 : 3 ∣ Nat.card E := hzx ▸ Subgroup.card_dvd_of_le hle
          have hE3 : Nat.card E = 3 := by
            obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
              (show Nat.card E ∣ 3 ^ 2 by simpa using hdvd)
            interval_cases i
            · rw [he] at h3; norm_num at h3
            · rw [he]; norm_num
            · exact absurd (he.trans (by norm_num)) hne9
          exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hE3, hzx])).symm
        rw [hEx, centralizer_zpowers']
        exact (hterm x hxB (fun h => hx1 (Subtype.ext h))).trans le_sup_left
    · exfalso
      refine hnot fun x hx => ?_
      obtain ⟨k, hk, hy⟩ := hin x hx
      refine ⟨k, hk, Inputs1114.mem_centBar_iff_forall.2 ⟨Subgroup.mem_top _,
        (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer hk))
          (hBN hx), fun l hl => ?_⟩⟩
      have h1 := conj_mem_gLAPPrimeCoreOf_of_mem_normalizer
        (Subgroup.le_normalizer (K.inv_mem hk)) (hy l hl)
      have e : k⁻¹ * (x * l * x⁻¹ * (k * l * k⁻¹)⁻¹) * k⁻¹⁻¹ = k⁻¹ * x * l * (k⁻¹ * x)⁻¹ * l⁻¹ := by
        group
      rwa [e] at h1

theorem input23_20_W_holds :
    Input23_20_W :=
  input23_20_W_of_cover CFSG.HardMathSupport.Solomon.Proving.inputL34Cover_holds

end I2320

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL34b

end
