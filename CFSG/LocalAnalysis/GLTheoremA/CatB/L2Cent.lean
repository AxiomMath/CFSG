module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.L2CentRed
public import CFSG.LocalAnalysis.GLTheoremA.CatB.L2CentField
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldAut3
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldFixed
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldHolds
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510
public import CFSG.HardMathSupport.Solomon.Coordinator.L3ALayer
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AFix
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha
public import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.GLTheoremA.S10
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem l2c_catalog_transport {S S' : Type} [Group S] [Group S'] {Q : TauCeti.CFSGIndex → Prop}
    (e : S ≃* S') (h : catalogIs S Q) : catalogIs S' Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem l2c_fixed (h0 : L2CentreThree) (h1 : L2Aut3Classification)
    (h2 : L2FieldFixed) {Y L K : Subgroup G} {x : G} {m : ℕ} (hL : GLAPComponent 3 Y L)
    (hLc : catalogIs (PSimple 3 L) (isL2n m)) (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (hx3 : x ^ 3 = 1) (hKL : K ≤ L) (hK : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) K) :
    ∃ k, catalogIs (PSimple 3 K) (isL2n k) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 L) := isQuasisimple_pQuot_of_glaPComponent hp hL
  have hO : GLAPPrimeCore 3 (PQuot 3 L) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  obtain ⟨hm1, F, hFf, hFfin, hF, ⟨e⟩⟩ := l2c_isTypeL2_of_catalog hLc
  obtain ⟨J₁, hJ₁, hJmap⟩ := exists_comp_subgroupOf
    (inf_le_left : L ⊓ Subgroup.centralizer ({x} : Set G) ≤ L) hK
  have hS := comp_map_fixSub hxN hx3 hJ₁
  have ha3 := barAut_pow_three hxN hx3
  set a := CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L ⟨x, hxN⟩ with ha
  set S := J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) with hSdef
  let f₁ : ↥K →* PQuot 3 L := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp (Subgroup.inclusion hKL)
  have hf₁S : ∀ k : ↥K, f₁ k ∈ S := by
    intro k
    have hk : (k : G) ∈ J₁.map L.subtype := hJmap ▸ k.2
    obtain ⟨j, hj, hjk⟩ := Subgroup.mem_map.1 hk
    refine Subgroup.mem_map.2 ⟨j, hj, ?_⟩
    show QuotientGroup.mk' _ j = QuotientGroup.mk' _ (Subgroup.inclusion hKL k)
    congr 1
    exact Subtype.ext hjk
  have hsurjS : ∀ s ∈ S, ∃ k : ↥K, f₁ k = s := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hs
    have hjK : (L.subtype j) ∈ K := by
      rw [← hJmap]
      exact Subgroup.mem_map.2 ⟨j, hj, rfl⟩
    exact ⟨⟨(j : G), hjK⟩, rfl⟩
  by_cases ha1 : a = 1
  ·
    have hST : S = ⊤ := by
      rw [ha1, fixSub_one] at hS
      have hOt := glaPPrimeCore_top_eq_bot hO
      have hq' : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup (PQuot 3 L)) :=
        isQuasisimple_open_of_mulEquiv Subgroup.topEquiv hQ
      obtain ⟨-, comp, -⟩ := layer_of_normal_quasisimple (F := (⊤ : Subgroup (PQuot 3 L)))
        (S := (⊤ : Subgroup (PQuot 3 L))) le_rfl (commutator_le_self _)
        (fun x _ => ⟨0, by simp⟩) hq' hOt
      exact (comp S).1 hS
    have hf₁ : Function.Surjective f₁ := fun q => by
      have hqS : q ∈ S := by rw [hST]; exact Subgroup.mem_top q
      exact hsurjS q hqS
    have hA : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore 3 ↥K) :=
      isQuasisimple_pQuot_of_glaPComponent hp hK
    let eB : (PQuot 3 L ⧸ GLAPPrimeCore 3 (PQuot 3 L)) ≃* PQuot 3 L :=
      (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
    have hB : CFSG.Open.IsQuasisimple (PQuot 3 L ⧸ GLAPPrimeCore 3 (PQuot 3 L)) :=
      CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eB.symm hQ
    obtain ⟨φ⟩ := nonempty_pSimple_equiv_of_surjective hp f₁ hf₁ hA hB
    have hPS : PSimple 3 K ≃* PSimple 3 L :=
      φ.trans (QuotientGroup.congr _ _ eB (Subgroup.map_center_eq eB))
    exact ⟨m, l2c_catalog_transport hPS.symm hLc⟩
  ·
    obtain ⟨k, F₀, hF₀f, hF₀fin, hk2, hk, ⟨ψS⟩⟩ :=
      l2c_field_case h0 h1 h2 hQ hO hF hm1 e ha3 ha1 hS
    let g : ↥K →* ↥S := f₁.codRestrict S hf₁S
    let f : ↥K →* PQuot 3 S := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥S)).comp g
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥S) y
      obtain ⟨k', hk'⟩ := hsurjS s.1 s.2
      refine ⟨k', ?_⟩
      show QuotientGroup.mk' _ (g k') = QuotientGroup.mk' _ s
      congr 1
      exact Subtype.ext hk'
    have hqS : CFSG.Open.IsQuasisimple (PQuot 3 S) := isQuasisimple_pQuot_of_glaPComponent hp hS
    have hOS : GLAPPrimeCore 3 (PQuot 3 S) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
    let eBS : (PQuot 3 S ⧸ GLAPPrimeCore 3 (PQuot 3 S)) ≃* PQuot 3 S :=
      (QuotientGroup.quotientMulEquivOfEq hOS).trans QuotientGroup.quotientBot
    have hBS : CFSG.Open.IsQuasisimple (PQuot 3 S ⧸ GLAPPrimeCore 3 (PQuot 3 S)) :=
      CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eBS.symm hqS
    have hA : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore 3 ↥K) :=
      isQuasisimple_pQuot_of_glaPComponent hp hK
    obtain ⟨φ⟩ := nonempty_pSimple_equiv_of_surjective hp f hf hA hBS
    have hPS : PSimple 3 K ≃* PSimple 3 S :=
      φ.trans (QuotientGroup.congr _ _ eBS (Subgroup.map_center_eq eBS))
    exact ⟨k, l2c_catalog_of_iso hk2 hk (hPS.trans ψS)⟩

theorem l2CentAt_holds (G : Type) [Group G] [Finite G] :
    L2CentAt G := by
  have h0 : L2CentreThree := l2CentreThree_holds
  have h1 : L2Aut3Classification := l2Aut3Classification_holds
  have h2 : L2FieldFixed := l2FieldFixed_holds
  unfold L2CentAt
  intro Y W 𝒞 x m h𝒞 hW hxN hx3 K hK
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨L, hL𝒞, hLV, hKV, hcase⟩ :=
    l2c_orbit Y W 𝒞 x (fun M hM => (h𝒞 M hM).1) hW hxN hx3 K hK
  have hLc : catalogIs (PSimple 3 L) (isL2n m) := (h𝒞 L hL𝒞).2
  have hxV : x ∈ W ⊔ Subgroup.zpowers x := le_sup_right (a := W) (Subgroup.mem_zpowers x)
  rcases hcase with ⟨hfix, hKL⟩ | ⟨h1, h2, hKd⟩
  · have hxN' : x ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_iff_gLBConj_eq.2 hfix
    have hKLC : K ≤ L ⊓ Subgroup.centralizer ({x} : Set G) :=
      le_inf hKL (hKV.1.trans inf_le_right)
    have hKc : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) K :=
      glaPComponent_of_le hp hKV hKLC (inf_le_inf_right _ hLV.1)
    obtain ⟨k, hk⟩ := l2c_fixed h0 h1 h2 (h𝒞 L hL𝒞).1 hLc hxN' hx3 hKL hKc
    exact ⟨k, hk⟩
  · obtain ⟨φ⟩ := l2c_diag hx3 hxV hLV hKV h1 h2 hKd
    exact ⟨m, l2c_catalog_transport φ.symm hLc⟩

end CFSG.LocalAnalysis.GLTheoremA
