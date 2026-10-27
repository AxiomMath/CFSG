module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44DataComp
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44Data (card_barX_eq_sixty)

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434

section General

variable {K : Type} [Group K]

theorem component_perfect {C J : Subgroup K} (hJ : GLAPComponent 5 C J) : ⁅J, J⁆ = J :=
  CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ

theorem primeComplementCore_ne_top {H : Type} [Group H] [Finite H] (h5 : 5 ∣ Nat.card H) :
    primeComplementCore (G := H) 5 ≠ ⊤ := by
  intro htop
  have hcop : Nat.Coprime 5 (Nat.card (primeComplementCore (G := H) 5)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_coprime (G := H) 5
  rw [htop, Subgroup.card_top] at hcop
  have := Nat.Coprime.eq_one_of_dvd hcop h5
  omega

variable [Finite K]

theorem barX_sup_le {C A B : Subgroup K} (hA : A ≤ C) (hB : B ≤ C) :
    barX 5 C (A ⊔ B) ≤ barX 5 C A ⊔ barX 5 C B := by
  unfold barX
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem card_quotient_eq_sixty_of_subnormal_quasisimple {C J₁ J₂ H : Subgroup K}
    (hF : FiveLayerData C J₁ J₂) (hHC : IsSubnormal H C) (hq : CFSG.Open.IsQuasisimple ↥H)
    (h5 : 5 ∣ Nat.card H) :
    Nat.card (↥H ⧸ primeComplementCore (G := ↥H) 5) = 60 := by
  have hp5 : Nat.Prime 5 := Nat.prime_five
  haveI : (primeComplementCore (G := ↥H) 5).Normal :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_normal 5
  have hcen : primeComplementCore (G := ↥H) 5 ≤ Subgroup.center ↥H :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hq _
      (primeComplementCore_ne_top h5)
  have hQbar : CFSG.Open.IsQuasisimple (barOf 5 H) :=
    CFSG.ComponentClassification.Quasisimple.central_quotient hq _ hcen
  have hQX : CFSG.Open.IsQuasisimple ↥(barX 5 C H) := (isQuasisimple_barX_iff hp5 hHC).2 hQbar
  have hcomp : IsComponentOf (barX 5 C H) ⊤ := ⟨le_top, barX_isSubnormal_top 5 hHC, hQX⟩
  obtain ⟨L, hL, hbarL⟩ := exists_glaPComponent_barX_eq C hcomp
  have hLle : L ≤ J₁ ⊔ J₂ := by
    rw [← hF.layer]
    exact le_sSup hL
  have hHle : barX 5 C H ≤ barX 5 C J₁ ⊔ barX 5 C J₂ := by
    rw [← hbarL]
    exact (Subgroup.map_mono (Subgroup.subgroupOf_mono C hLle)).trans
      (barX_sup_le hF.comp₁.1 hF.comp₂.1)
  have hs₁ : IsSubnormal (barX 5 C J₁) ⊤ := barX_isSubnormal_top 5 hF.comp₁.2.1
  have hs₂ : IsSubnormal (barX 5 C J₂) ⊤ := barX_isSubnormal_top 5 hF.comp₂.2.1
  have hc₁ : IsComponentOf (barX 5 C J₁) ⊤ := hF.comp₁.2.2.1
  have hc₂ : IsComponentOf (barX 5 C J₂) ⊤ := hF.comp₂.2.2.1
  have hcardH : Nat.card (↥H ⧸ primeComplementCore (G := ↥H) 5) = Nat.card ↥(barX 5 C H) :=
    Nat.card_congr (barXEquiv hp5 hHC).toEquiv
  rw [hcardH]
  rcases CFSG.ComponentClassification.LocalComponents.subnormal_contains_or_commutes _ _
      hcomp hs₁ with h1 | h1
  · rw [CFSG.ComponentClassification.LocalComponents.eq_of_le _ _ hcomp hc₁ h1]
    exact card_barX_eq_sixty hF.comp₁ hF.quot₁
  rcases CFSG.ComponentClassification.LocalComponents.subnormal_contains_or_commutes _ _
      hcomp hs₂ with h2 | h2
  · rw [CFSG.ComponentClassification.LocalComponents.eq_of_le _ _ hcomp hc₂ h2]
    exact card_barX_eq_sixty hF.comp₂ hF.quot₂
  exfalso
  have e₁ : barX 5 C J₁ ≤ Subgroup.centralizer (barX 5 C H : Set _) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h1
  have e₂ : barX 5 C J₂ ≤ Subgroup.centralizer (barX 5 C H : Set _) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h2
  have hab : barX 5 C H ≤ Subgroup.centralizer (barX 5 C H : Set _) :=
    hHle.trans (sup_le e₁ e₂)
  haveI : IsMulCommutative ↥(barX 5 C H) := Subgroup.le_centralizer_iff_isMulCommutative.1 hab
  have hperf : commutator ↥(barX 5 C H) = ⊤ := hQX.1
  have hbot : commutator ↥(barX 5 C H) = ⊥ := by
    rw [commutator_eq_bot_iff_center_eq_top]
    exact Subgroup.center_eq_top
  rw [hbot] at hperf
  haveI := CFSG.ComponentClassification.Quasisimple.nontrivial hQX
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥(barX 5 C H))
  have : a ∈ (⊤ : Subgroup ↥(barX 5 C H)) := Subgroup.mem_top a
  rw [← hperf, Subgroup.mem_bot] at this
  exact ha this

theorem sixty_dvd_card_of_component {C J : Subgroup K} (hJ : GLAPComponent 5 C J)
    (hA : Nonempty (↥J ⧸ primeComplementCore (G := ↥J) 5 ≃* alternatingGroup (Fin 5))) :
    60 ∣ Nat.card ↥J := by
  have h60 := card_barX_eq_sixty hJ hA
  have h1 : Nat.card ↥(barX 5 C J) ∣ Nat.card ↥(J.subgroupOf C) := Subgroup.card_map_dvd _ _
  have h2 : Nat.card ↥(J.subgroupOf C) = Nat.card ↥J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ.1).toEquiv
  rw [h60, h2] at h1
  exact h1

namespace FiveLayerData

variable {C J₁ J₂ : Subgroup K} (hF : FiveLayerData C J₁ J₂)

include hF

theorem perfect₁ : ⁅J₁, J₁⁆ = J₁ := component_perfect hF.comp₁

theorem perfect₂ : ⁅J₂, J₂⁆ = J₂ := component_perfect hF.comp₂

theorem sixty_dvd_card₁ : 60 ∣ Nat.card ↥J₁ := sixty_dvd_card_of_component hF.comp₁ hF.quot₁

theorem sixty_dvd_card₂ : 60 ∣ Nat.card ↥J₂ := sixty_dvd_card_of_component hF.comp₂ hF.quot₂

theorem le₁ : J₁ ≤ C := hF.comp₁.1

theorem le₂ : J₂ ≤ C := hF.comp₂.1

end FiveLayerData

theorem three_thousand_six_hundred_dvd_card_of_two_components {X J₁ J₂ : Subgroup K}
    (h₁ : GLAPComponent 5 X J₁) (h₂ : GLAPComponent 5 X J₂) (hne : J₁ ≠ J₂)
    (hA₁ : Nonempty (↥J₁ ⧸ primeComplementCore (G := ↥J₁) 5 ≃* alternatingGroup (Fin 5)))
    (hA₂ : Nonempty (↥J₂ ⧸ primeComplementCore (G := ↥J₂) 5 ≃* alternatingGroup (Fin 5))) :
    3600 ∣ Nat.card ↥X := by
  have hne' : barX 5 X J₁ ≠ barX 5 X J₂ := fun h => hne (glaPComponent_uniqueAux h₁ h₂ h)
  have hcomm : ⁅barX 5 X J₁, barX 5 X J₂⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ h₁.2.2.1 h₂.2.2.1 hne'
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hc : ∀ (m : ↥(barX 5 X J₁)) (n : ↥(barX 5 X J₂)),
      Commute ((barX 5 X J₁).subtype m) ((barX 5 X J₂).subtype n) := by
    intro m n
    have := Subgroup.mem_centralizer_iff.mp (hle m.2) n n.2
    exact this.symm
  have hinj := (MonoidHom.noncommCoprod_injective (barX 5 X J₁).subtype (barX 5 X J₂).subtype
    hc).mpr ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, by
      rw [Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.disjoint_def]
      intro z hz₁ hz₂
      have hz : (⟨z, hz₁⟩ : ↥(barX 5 X J₁)) ∈ Subgroup.center ↥(barX 5 X J₁) := by
        rw [Subgroup.mem_center_iff]
        intro w
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hle w.2) z hz₂).symm
      rw [CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44Data.barX_center_trivial h₁ hA₁,
        Subgroup.mem_bot] at hz
      exact congrArg Subtype.val hz⟩
  have h3600 := Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_prod, card_barX_eq_sixty h₁ hA₁, card_barX_eq_sixty h₂ hA₂] at h3600
  have h4 := Subgroup.card_quotient_dvd_card (GLAPPrimeCore 5 ↥X)
  exact (show 3600 = 60 * 60 by norm_num) ▸ h3600.trans h4

theorem three_thousand_six_hundred_dvd_card_sup {C J₁ J₂ : Subgroup K}
    (hF : FiveLayerData C J₁ J₂) : 3600 ∣ Nat.card ↥(J₁ ⊔ J₂) := by
  have hle₁ : J₁ ≤ J₁ ⊔ J₂ := le_sup_left
  have hle₂ : J₂ ≤ J₁ ⊔ J₂ := le_sup_right
  have hXC : J₁ ⊔ J₂ ≤ C := sup_le hF.comp₁.1 hF.comp₂.1
  exact three_thousand_six_hundred_dvd_card_of_two_components
    (glaPComponent_down Nat.prime_five hF.comp₁ hle₁ hXC)
    (glaPComponent_down Nat.prime_five hF.comp₂ hle₂ hXC) hF.ne hF.quot₁ hF.quot₂

theorem three_thousand_six_hundred_dvd_card {C J₁ J₂ R : Subgroup K}
    (hF : FiveLayerData C J₁ J₂) (hR : ∀ P : Subgroup K, P ≤ C → ⁅P, P⁆ = P → P ≤ R) :
    3600 ∣ Nat.card ↥R := by
  have h₁ : J₁ ≤ R := hR J₁ hF.comp₁.1 (component_perfect hF.comp₁)
  have h₂ : J₂ ≤ R := hR J₂ hF.comp₂.1 (component_perfect hF.comp₂)
  exact (three_thousand_six_hundred_dvd_card_sup hF).trans
    (Subgroup.card_dvd_of_le (sup_le h₁ h₂))

theorem exists_conj_mem_sylow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (Q : Sylow p X) {S : Subgroup X} (hS : IsPGroup p S) :
    ∃ g : X, ∀ s ∈ S, g * s * g⁻¹ ∈ (Q : Subgroup X) := by
  obtain ⟨Q', hSQ'⟩ := hS.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q' Q
  refine ⟨g, fun s hs => ?_⟩
  have hgQ : ((g • Q' : Sylow p X) : Subgroup X) =
      (Q' : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [← hg, hgQ]
  exact ⟨s, hSQ' hs, rfl⟩

theorem card_le_of_isElemAbelian {Q : Sylow 5 K} (hQ : CFSG.Open.pRank 5 (Q : Subgroup K) = 3)
    {E : Subgroup K} (hE : IsElemAbelian 5 E) : Nat.card ↥E ≤ 5 ^ 3 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hEp : IsPGroup 5 E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE.2 g g.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow Q hEp
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hmap : Nat.card ↥(E.map (MulAut.conj g).toMonoidHom) = 5 ^ k := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hk]
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup K) := by
    rintro _ ⟨s, hs, rfl⟩
    exact hg s hs
  have hk3 : k ≤ 3 :=
    (CFSG.SectionRank.le_pRank (by norm_num : 1 < 5) hle
      (CFSG.SectionRank.isElemAbelian_map hE _) hmap).trans hQ.le
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk3

theorem isMulCommutative_of_isPGroup {Q : Sylow 5 K} (hQ : IsMulCommutative (Q : Subgroup K))
    {P : Subgroup K} (hP : IsPGroup 5 P) : IsMulCommutative P := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow Q hP
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  have h := mul_comm' (⟨g * (a : K) * g⁻¹, hg a a.2⟩ : (Q : Subgroup K))
    ⟨g * (b : K) * g⁻¹, hg b b.2⟩
  have h' := congrArg Subtype.val h
  simp only [Subgroup.coe_mul] at h'
  have h'' : g * ((a : K) * b) * g⁻¹ = g * ((b : K) * a) * g⁻¹ := by
    calc g * ((a : K) * b) * g⁻¹ = (g * (a : K) * g⁻¹) * (g * (b : K) * g⁻¹) := by group
      _ = (g * (b : K) * g⁻¹) * (g * (a : K) * g⁻¹) := h'
      _ = g * ((b : K) * a) * g⁻¹ := by group
  simpa using h''

theorem commute_of_mem_isPGroup {Q : Sylow 5 K} (hQ : IsMulCommutative (Q : Subgroup K))
    {P : Subgroup K} (hP : IsPGroup 5 P) {a b : K} (ha : a ∈ P) (hb : b ∈ P) : a * b = b * a := by
  haveI := isMulCommutative_of_isPGroup hQ hP
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : P) ⟨b, hb⟩)

end General

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434
