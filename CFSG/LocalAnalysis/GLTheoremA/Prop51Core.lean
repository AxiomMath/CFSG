module

public import CFSG.LocalAnalysis.GLTheoremA.Prop51
public import CFSG.LocalAnalysis.GLTheoremA.I32One
public import CFSG.LocalAnalysis.GLTheoremA.P51.Conj
public import CFSG.LocalAnalysis.GLTheoremA.P51.CentMod
public import CFSG.LocalAnalysis.GLTheoremA.P51.Cover
public import CFSG.LocalAnalysis.GLTheoremA.P51.Generation
public import CFSG.LocalAnalysis.GLTheoremA.P51.SCp
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P51.Final
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_commutator {H₁ H₂ : Subgroup G} {g : G}
    (h₁ : g ∈ Subgroup.normalizer (H₁ : Set G)) (h₂ : g ∈ Subgroup.normalizer (H₂ : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H₁, H₂⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at h₁ h₂ ⊢
  unfold GLBConj at h₁ h₂ ⊢
  rw [Subgroup.map_commutator, h₁, h₂]

theorem commutator_le_left_of_le_normalizer {A H : Subgroup G}
    (h : H ≤ Subgroup.normalizer (A : Set G)) : (⁅A, H⁆ : Subgroup G) ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha g hg
  rw [commutatorElement_def]
  have : g * a⁻¹ * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (h hg) a⁻¹).1 (A.inv_mem ha)
  simpa [mul_assoc] using A.mul_mem ha this

theorem le_sup_inf_of_le_sup {A C N : Subgroup G} (hAC : A ≤ C) (hCAN : C ≤ A ⊔ N)
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) : C ≤ A ⊔ (C ⊓ N) := by
  intro c hc
  have hc' : c ∈ (A ⊔ N : Subgroup G) := hCAN hc
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A N hAN] at hc'
  obtain ⟨x, hx, n, hn, rfl⟩ := Set.mem_mul.mp hc'
  have hnC : n ∈ C := by
    have : x⁻¹ * (x * n) ∈ C := C.mul_mem (C.inv_mem (hAC hx)) hc
    simpa using this
  exact Subgroup.mul_mem_sup hx ⟨hnC, hn⟩

theorem le_glaPPrimeCoreOf_of_le_normalizer {p : ℕ} {N K : Subgroup G} (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime p (Nat.card N)) :
    N ≤ GLAPPrimeCoreOf p K := by
  haveI hn : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  have hcard : Nat.card (N.subgroupOf K) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hle : N.subgroupOf K ≤ GLAPPrimeCore p ↥K := le_sSup ⟨hn, hcard ▸ hcop⟩
  intro n hn'
  exact ⟨⟨n, hNK hn'⟩, hle hn', rfl⟩

theorem mem_normalizer_sup_of_mem {A C : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hC : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hA hC ⊢
  unfold GLBConj at hA hC ⊢
  rw [Subgroup.map_sup, hA, hC]

theorem prop51Core_cover {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B J D Q : Subgroup G} {a : G}
    (hBaJ : IsS0Max p B a J) (hDB : D ≤ B) (hDJ : ∀ d ∈ D, CentMod p J d)
    (hDinv : ∀ K : Subgroup G, GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K →
      Nonempty (PQuot p K ≃* PQuot p J) → D ≤ Subgroup.normalizer (K : Set G))
    (hQ2 : IsPGroup 2 Q) (hBQ : B ≤ Subgroup.normalizer (Q : Set G))
    (hQa : Q ≤ Subgroup.centralizer ({a} : Set G)) (hR : (⁅D, Q⁆ : Subgroup G) ≠ ⊥) :
    ∃ S Y : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧ B ≤ Subgroup.normalizer (S : Set G) ∧
      GLAPComponent p Y (GLAPLayer p Y) ∧ GLAPLayer p Y ≤ Subgroup.normalizer (S : Set G) ∧
      GLAPLayer p Y ≤ Subgroup.centralizer (D : Set G) ∧ GLAPLayer p Y ≤ J ∧
      GLAPLayer p Y ⊔ GLAPPrimeCoreOf p J = J ∧
      B ≤ Subgroup.normalizer (GLAPLayer p Y : Set G) := by
  classical
  have hS : IsSTriple p B a J := hBaJ.1.1
  have hB : GLAIsBmax p B := hS.1
  have hJc : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) J := hS.2.2
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := hBaJ.2.2
  have haB : a ∈ B := hS.2.1.1
  have hBCa : B ≤ Subgroup.centralizer ({a} : Set G) := isElemAbelian_le_centralizer hB.1 haB
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hB.1
  have hDQ : D ≤ Subgroup.normalizer (Q : Set G) := hDB.trans hBQ
  have hBD : B ≤ Subgroup.centralizer (D : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun d hd => isElemAbelian_commute hB.1 (hDB hd) hb
  have hBND : B ≤ Subgroup.normalizer (D : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer _ (hBD hb)
  have hDJ' : D ≤ centModSubgroup p J := fun d hd => centMod_iff.1 (hDJ d hd)
  have hRJ : (⁅D, Q⁆ : Subgroup G) ≤ centModSubgroup p J :=
    P51.commutator_le_centModSubgroup_of_coprime hp hp2 (hBp.to_le hDB) hQ2 hDQ
      (P51.commutator_le_normalizer_of_forall hJc hQa hDinv) hDJ'
  have hRQ : (⁅D, Q⁆ : Subgroup G) ≤ Q := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer hDQ
  have hOJ : GLAPPrimeCoreOf p J ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hJc.2.1]
    exact inf_le_right
  have hRC : (⁅D, Q⁆ : Subgroup G) ≤ P51.cent0 p (Subgroup.centralizer ({a} : Set G)) J :=
    fun r hr => ⟨hQa (hRQ hr), fun j hj => hOJ ((hRJ hr).2 j hj)⟩
  have hBR : B ≤ Subgroup.normalizer ((⁅D, Q⁆ : Subgroup G) : Set G) := fun b hb =>
    mem_normalizer_commutator (hBND hb) (hBQ hb)
  obtain ⟨S, ⟨hS2, hSC, hBS, hRS⟩, hSmax⟩ := Set.exists_max_image
    {T : Subgroup G | IsPGroup 2 T ∧ T ≤ P51.cent0 p (Subgroup.centralizer ({a} : Set G)) J ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅D, Q⁆ : Subgroup G) ≤ T}
    (fun T => Nat.card T) (Set.toFinite _) ⟨_, hQ2.to_le hRQ, hRC, hBR, le_rfl⟩
  have hSmax' : ∀ T : Subgroup G, IsPGroup 2 T →
      T ≤ P51.cent0 p (Subgroup.centralizer ({a} : Set G)) J →
      B ≤ Subgroup.normalizer (T : Set G) → S ≤ T → T = S := fun T h1 h2 h3 h4 =>
    (Subgroup.eq_of_le_of_card_ge h4 (hSmax T ⟨h1, h2, h3, hRS.trans h4⟩)).symm
  have hSne : S ≠ ⊥ := fun h => hR (eq_bot_iff.2 (h ▸ hRS))
  have hcov := P51.le_sup_of_isMaxInvariant hp hp2 hJc hBp hBCa hBJ hDB hDJ' hS2 hSC hBS hSmax'
  obtain ⟨hHc, hHJ, hHsupJ⟩ := P51.glaPLayer_cover hp hJc (inf_le_left.trans inf_le_right) hcov
  refine ⟨S, _, hSne, hS2, hBS, hHc, hHc.1.trans (inf_le_left.trans inf_le_left),
    hHc.1.trans inf_le_right, hHJ, hHsupJ, fun b hb => mem_normalizer_glaPLayer ?_⟩
  have h1 : GLBConj b (Subgroup.normalizer (S : Set G)) = Subgroup.normalizer (S : Set G) :=
    mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hBS hb))
  have h2 : GLBConj b (J ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G))) =
      J ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) :=
    mem_normalizer_iff_gLBConj_eq.1 (mem_normalizer_sup_of_mem (hBJ hb)
      (normalizer_le_normalizer_glaPPrimeCoreOf p _ (Subgroup.le_normalizer (hBCa hb))))
  have h3 : GLBConj b (Subgroup.centralizer (D : Set G)) = Subgroup.centralizer (D : Set G) :=
    mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hBD hb))
  rw [mem_normalizer_iff_gLBConj_eq, gLBConj_inf, gLBConj_inf, h1, h2, h3]

theorem prop51Core_essential {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hchar : IsCharTwoType G)
    {B D S X H : Subgroup G} (hB : GLAIsBmax p B) (hDB : D ≤ B) (hDnc : ¬ IsCyclic D)
    (hSne : S ≠ ⊥) (hS2 : IsPGroup 2 S) (hBS : B ≤ Subgroup.normalizer (S : Set G))
    (hHc : GLAPComponent p X H) (hHN : H ≤ Subgroup.normalizer (S : Set G))
    (hHD : H ≤ Subgroup.centralizer (D : Set G)) (hBH : B ≤ Subgroup.normalizer (H : Set G)) :
    ∃ a' ∈ D, IsEssential p B a' ∧ ∃ W : Subgroup G, W ≠ ⊥ ∧ IsPGroup 2 W ∧
      W ≤ Subgroup.centralizer ({a'} : Set G) ∧ H ≤ Subgroup.normalizer (W : Set G) ∧
      (⁅W, H⁆ : Subgroup G) = W := by
  have hBD : B ≤ Subgroup.centralizer (D : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun d hd => isElemAbelian_commute hB.1 (hDB hd) hb
  have hHperf : (⁅H, H⁆ : Subgroup G) = H := glaPComponent_perfect hHc
  have hH2 : ¬ IsPGroup 2 H :=
    P51.not_isPGroup_of_glaPComponent hp Nat.prime_two (Ne.symm hp2) hHc
  obtain ⟨a', ha'D, ha'1, hHV⟩ := P51.exists_ne_one_not_le_centralizer hp hp2 hchar hSne hS2 hHN
    (hDB.trans hBS) (isElemAbelian_mono hB.1 hDB) hDnc hHD hH2
  set N := Subgroup.normalizer (S : Set G)
  set V : Subgroup G := pCoreOf 2 N ⊓ Subgroup.centralizer ({a'} : Set G)
  have hNV : ∀ g ∈ N, g ∈ Subgroup.centralizer (D : Set G) →
      g ∈ Subgroup.normalizer (V : Set G) := fun g hgN hgD => by
    have h1 := mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_pCoreOf 2 N hgN)
    have h2 : GLBConj g (Subgroup.centralizer ({a'} : Set G)) =
        Subgroup.centralizer ({a'} : Set G) :=
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer
        (Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hgD a' ha'D).symm))
    rw [mem_normalizer_iff_gLBConj_eq, gLBConj_inf, h1, h2]
  have hHNV : H ≤ Subgroup.normalizer (V : Set G) := fun h hh => hNV h (hHN hh) (hHD hh)
  have hBNV : B ≤ Subgroup.normalizer (V : Set G) := fun b hb => hNV b (hBS hb) (hBD hb)
  have hV2 : IsPGroup 2 V := (isPGroup_pCoreOf 2 N).to_le inf_le_left
  have hW : (⁅⁅V, H⁆, H⁆ : Subgroup G) = ⁅V, H⁆ :=
    commutator_commutator_eq_of_perfect hV2 hHperf hHNV
  have hWV : (⁅V, H⁆ : Subgroup G) ≤ V := commutator_le_left_of_le_normalizer hHNV
  have hW2 : IsPGroup 2 (⁅V, H⁆ : Subgroup G) := hV2.to_le hWV
  have hWne : (⁅V, H⁆ : Subgroup G) ≠ ⊥ := fun h => hHV (by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h)
  have hHW : H ≤ Subgroup.normalizer ((⁅V, H⁆ : Subgroup G) : Set G) := fun h hh =>
    mem_normalizer_commutator (hHNV hh) (Subgroup.le_normalizer hh)
  have hBW : B ≤ Subgroup.normalizer ((⁅V, H⁆ : Subgroup G) : Set G) := fun b hb =>
    mem_normalizer_commutator (hBNV hb) (hBH hb)
  have hHB : H ≤ (⁅H, B⁆ : Subgroup G) := P51.le_commutator_of_maximal hp hp2 hHc hB.1 hBH
    fun E hE hBE hEHB => GLAIsBmax.eq_of_le hp hB hBE hE hSne hS2 (hEHB.trans (sup_le hHN hBS))
  have hWB : (⁅⁅V, H⁆, B⁆ : Subgroup G) ≠ ⊥ := by
    intro hWB
    have hBC : B ≤ Subgroup.centralizer ((⁅V, H⁆ : Subgroup G) : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hWB
    have hHBC : (⁅H, B⁆ : Subgroup G) ≤ Subgroup.centralizer ((⁅V, H⁆ : Subgroup G) : Set G) := by
      rw [Subgroup.commutator_le]
      intro h hh b hb
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : h⁻¹ * w * h ∈ (⁅V, H⁆ : Subgroup G) := by
        have := (Subgroup.mem_normalizer_iff.1 (hHW (H.inv_mem hh)) w).1 hw
        simpa using this
      have e1 : (h⁻¹ * w * h) * b = b * (h⁻¹ * w * h) :=
        Subgroup.mem_centralizer_iff.1 (hBC hb) _ hw'
      have e2 : b⁻¹ * w = w * b⁻¹ := by
        have e3 : w * b = b * w := Subgroup.mem_centralizer_iff.1 (hBC hb) w hw
        calc b⁻¹ * w = b⁻¹ * (w * b) * b⁻¹ := by group
          _ = b⁻¹ * (b * w) * b⁻¹ := by rw [e3]
          _ = w * b⁻¹ := by group
      rw [commutatorElement_def]
      calc w * (h * b * h⁻¹ * b⁻¹) = h * (h⁻¹ * w * h) * b * h⁻¹ * b⁻¹ := by group
        _ = h * (b * (h⁻¹ * w * h)) * h⁻¹ * b⁻¹ := by rw [mul_assoc h (h⁻¹ * w * h) b, e1]
        _ = h * b * h⁻¹ * (w * b⁻¹) := by group
        _ = h * b * h⁻¹ * (b⁻¹ * w) := by rw [e2]
        _ = h * b * h⁻¹ * b⁻¹ * w := by group
    apply hWne
    rw [← hW, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hHB.trans hHBC
  exact ⟨a', ha'D, ⟨hDB ha'D, ha'1, _, hWV.trans inf_le_right, hW2, hBW, hWB,
    fun _ => P51.isEmpty_mulEquiv_quaternionGroup hHW hHperf hW hWne⟩,
    _, hWne, hW2, hWV.trans inf_le_right, hHW, hW⟩

theorem prop51Core {p : ℕ} (hc : Sec5Ctx G p) (hchar : IsCharTwoType G) : Prop51CoreAt G p := by
  intro B J D Q a hBaJ hDB hDnc _ hDJ hDinv hQ2 hBQ hQa hR
  classical
  have hp := hc.prime
  have hp2 := hc.odd
  have hB : GLAIsBmax p B := hBaJ.1.1.1
  have hJc : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) J := hBaJ.1.1.2.2
  obtain ⟨S, Y, hSne, hS2, hBS, hHc, hHN, hHD, hHJ, hHsupJ, hBH⟩ :=
    prop51Core_cover hp hp2 hBaJ hDB hDJ hDinv hQ2 hBQ hQa hR
  obtain ⟨a', ha'D, ha'E, W, hWne, hW2, hWa', hHW, hW⟩ :=
    prop51Core_essential hp hp2 hchar hB hDB hDnc hSne hS2 hBS hHc hHN hHD hBH
  have ha'J : CentMod p J a' := hDJ a' ha'D
  obtain ⟨K, -, hKc, hrel, -, -, -, hJ₀K, hJ₀sup, -, -⟩ :=
    pump_step hc.input18_3_4 hp hc.stage4Order hc.kProper hc.simple hc.nonabelian hBaJ.2.1
      hBaJ.2.2 hB hBaJ.1.1.2.1.1
      (fun b hb => ⟨b, ⟨hb, hb⟩, 1, B.one_mem, centMod_one p J, (mul_one b).symm⟩) ha'E ha'J
  have hodd := hc.stage4.1 B a' K
    ((hc.stage4Order.2.2.2.2.2.2.1 _ _
      (pumpLe_of_reflTransGen hBaJ.1.1 (Relation.ReflTransGen.single hrel))).1 hBaJ.1)
  obtain ⟨hJ₀c, -, hJ₀norm, -, hJ₀supJ, -⟩ :=
    glaPLayer_inf_centralizer hp hJc (isPGroup_zpowers_of_mem hB.1 (hDB ha'D)) ha'J
  have hHa' : GLAPLayer p Y ≤ Subgroup.centralizer ({a'} : Set G) := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hHD hh) a' ha'D).symm
  have hHJ₀ : GLAPLayer p Y ≤ GLAPLayer p (J ⊓ Subgroup.centralizer ({a'} : Set G)) := by
    have hY₂ := le_sup_inf_of_le_sup hJ₀c.1 (inf_le_left.trans hJ₀supJ.symm.le)
      (hJ₀c.1.trans (inf_le_left.trans (le_normalizer_glaPPrimeCoreOf p J)))
    refine CFSG.HardMathSupport.Solomon.Coordinator.i183_le_of_le_sup hp hHc ?_
      (inf_le_left.trans hJ₀norm) ((le_inf hHJ hHa').trans hY₂)
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp J)
  have hJ₀H : GLAPLayer p (J ⊓ Subgroup.centralizer ({a'} : Set G)) ≤
      GLAPLayer p Y ⊔ GLAPPrimeCoreOf p (GLAPLayer p (J ⊓ Subgroup.centralizer ({a'} : Set G))) := by
    refine (le_sup_inf_of_le_sup hHJ₀ (hJ₀c.1.trans (inf_le_left.trans hHsupJ.symm.le))
      (hHJ.trans (le_normalizer_glaPPrimeCoreOf p J))).trans (sup_le_sup_left ?_ _)
    refine le_glaPPrimeCoreOf_of_le_normalizer inf_le_left
      (fun j hj => Prop53.mem_normalizer_inf_of_mem (Subgroup.le_normalizer hj)
        (le_normalizer_glaPPrimeCoreOf p J (hJ₀c.1.trans inf_le_left hj))) ?_
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp J)
  obtain ⟨hOJ₀, -⟩ := cover_facts hp hJ₀K hJ₀sup
  have hOK : GLAPPrimeCoreOf p (GLAPLayer p (J ⊓ Subgroup.centralizer ({a'} : Set G))) ≤
      GLAPPrimeCoreOf p K := by
    rw [hOJ₀]
    exact inf_le_right
  have hKH : K ≤ GLAPLayer p Y ⊔ GLAPPrimeCoreOf p K :=
    hJ₀sup.symm.le.trans (sup_le (hJ₀H.trans (sup_le_sup_left hOK _)) le_sup_right)
  have hWK : W ≤ K := P51.le_of_commutator_eq_of_isSubnormal hKc.2.1 hWa' (hHJ₀.trans hJ₀K) hW
  exact hWne (P51.eq_bot_of_le_sup_glaPPrimeCoreOf hp hp2 hKc (hHJ₀.trans hJ₀K) hKH hWK hW2 hHW
    hW hodd)

theorem prop51_of {p : ℕ} (hc : Sec5Ctx G p) (hchar : IsCharTwoType G)
    {Exc Club : Subgroup G → Prop} (hEC : ExcClubHyp G p Exc Club) (h113 : I113UsedAt G p) :
    Prop51At G p :=
  prop51 hc hEC h113 (prop51Core hc hchar)

end CFSG.LocalAnalysis.GLTheoremA
