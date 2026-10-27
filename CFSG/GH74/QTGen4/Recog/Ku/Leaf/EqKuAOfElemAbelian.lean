module

public import CFSG.GH74.QTGen4.Recog.Ku.OpenLeaves
public import CFSG.GH74.QTGen4.Recog.Ku.HStruct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative
open scoped commutatorElement

variable {G : Type} [Group G]

attribute [local instance] IsMulCommutative.instCommGroup

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem card_le_eight_of_isMulCommutative_le_P (h : KuHyp G T M H P z) {B : Subgroup G}
    (hBP : B ≤ P) (hB : IsMulCommutative B) : Nat.card B ≤ 8 := by
  haveI := h.isEA_quot_P
  haveI : Module.Finite (ZMod 2) (Additive (↥P ⧸ Subgroup.center ↥P)) := Module.Finite.of_finite
  let S : Submodule (ZMod 2) (Additive (↥P ⧸ Subgroup.center ↥P)) :=
    { carrier := {v | ∃ b : G, ∃ hb : b ∈ B, psi (⟨b, hBP hb⟩ : ↥P) = v}
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, B.mul_mem ha hb, (psi_mul (⟨a, hBP ha⟩ : ↥P) ⟨b, hBP hb⟩).symm⟩
      zero_mem' := ⟨1, B.one_mem, rfl⟩
      smul_mem' := by
        rintro c _ ⟨a, ha, rfl⟩
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · exact ⟨1, B.one_mem, by rw [zero_smul]; rfl⟩
        · exact ⟨a, ha, by rw [one_smul]⟩ }
  have hmemS : ∀ v, v ∈ S ↔ ∃ b : G, ∃ hb : b ∈ B, psi (⟨b, hBP hb⟩ : ↥P) = v :=
    fun v => Iff.rfl
  have hpairB : ∀ a b : G, (ha : a ∈ B) → (hb : b ∈ B) →
      h.kuZCore_P.commForm (psi (⟨a, hBP ha⟩ : ↥P)) (psi (⟨b, hBP hb⟩ : ↥P)) = 0 := by
    intro a b ha hb
    have hGeq : a * b = b * a := by
      have := hB.is_comm.comm (⟨a, ha⟩ : ↥B) ⟨b, hb⟩
      exact congrArg Subtype.val this
    have hcomm : (⟨a, hBP ha⟩ : ↥P) * ⟨b, hBP hb⟩ = ⟨b, hBP hb⟩ * ⟨a, hBP ha⟩ :=
      Subtype.ext hGeq
    have e1 : ⁅(⟨a, hBP ha⟩ : ↥P), (⟨b, hBP hb⟩ : ↥P)⁆ = 1 :=
      Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr (congrArg Subtype.val hcomm))
    have hBpsi : h.kuZCore_P.commForm (psi (⟨a, hBP ha⟩ : ↥P)) (psi (⟨b, hBP hb⟩ : ↥P)) =
        KuZCore.pairQ (⟨a, hBP ha⟩ : ↥P) ⟨b, hBP hb⟩ := by
      rw [h.kuZCore_P.commForm_apply]
      exact h.kuZCore_P.pairV_mk _ _
    rw [hBpsi]
    exact sgn_eq_zero_iff_gen.mpr e1
  have hSS : S ≤ h.kuZCore_P.commForm.orthogonal S := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := (hmemS v).mp hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨b, hb, rfl⟩ := (hmemS n).mp hn
    exact hpairB b a hb ha
  have hdim := LinearMap.BilinForm.finrank_orthogonal h.kuZCore_P.commForm_nondegenerate S
  have hmono := Submodule.finrank_mono hSS
  have hV4 := h.finrank_quotP
  have hS2 : Module.finrank (ZMod 2) S ≤ 2 := by omega
  have hcardS : Nat.card S ≤ 4 := by
    have hpow : Nat.card S = 2 ^ Module.finrank (ZMod 2) S := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2)] <;> simp [ZMod.card]
    rw [hpow]
    calc 2 ^ Module.finrank (ZMod 2) S ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hS2
      _ = 4 := by norm_num
  have hBle : B ≤ psiPre S :=
    fun b hb => mem_psiPre_iff.mpr ⟨hBP hb, (hmemS _).mpr ⟨b, hb, rfl⟩⟩
  have hle := Subgroup.card_le_of_le hBle
  have hpre := card_psiPre S
  rw [h.card_center_P] at hpre
  omega

end KuHyp

theorem leafEqKuAOfElemAbelian
    [KuLeaf LeafCardKuA]
    : LeafEqKuAOfElemAbelian := by
  intro G _ _ T M H P z h E' hE' hel hc
  haveI := h.isEA_quot_P
  haveI : Module.Finite (ZMod 2) (Additive (↥P ⧸ Subgroup.center ↥P)) := Module.Finite.of_finite
  have hA : Nat.card (kuA P H) = 16 := KuLeaf.holds (L := LeafCardKuA) h
  obtain ⟨u, huQ, hcos⟩ := h.exists_u_coset
  have hnu : u ∉ P := fun hup =>
    (hcos 1 (pCoreOf 2 H).one_mem).mp (by rwa [one_mul]) P.one_mem
  have huu : u * u ∈ P := (hcos u huQ).mpr hnu
  have hun : u ∈ Subgroup.normalizer (P : Set G) :=
    h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H huQ)
  have hPE : E' ⊓ P ≤ pCoreOf 2 H := inf_le_left.trans hE'
  have h1 := Subgroup.relIndex_mul_card (E' ⊓ P) (pCoreOf 2 H)
  rw [inf_eq_left.mpr hPE, h.card_pCore_H] at h1
  have h2 := Subgroup.relIndex_mul_card E' (pCoreOf 2 H)
  rw [inf_eq_left.mpr hE', hc, h.card_pCore_H] at h2
  have h3 := Subgroup.relIndex_inf_le (H := E') (K := P) (L := pCoreOf 2 H)
  rw [h.relIndex_P_pCore] at h3
  have hEidx : E'.relIndex (pCoreOf 2 H) = 4 := by omega
  rw [hEidx] at h3
  have hr8 : (E' ⊓ P).relIndex (pCoreOf 2 H) ≤ 8 := by omega
  have hcard8 : 8 ≤ Nat.card ↥(E' ⊓ P) := by
    by_contra hlt
    push Not at hlt
    have hmul : (E' ⊓ P).relIndex (pCoreOf 2 H) * Nat.card ↥(E' ⊓ P) ≤ 8 * 7 :=
      Nat.mul_le_mul hr8 (by omega)
    omega
  obtain ⟨u', hu'E, hu'P⟩ : ∃ u' ∈ E', u' ∉ P := by
    by_contra hcon
    push Not at hcon
    have hle8 := h.card_le_eight_of_isMulCommutative_le_P (B := E')
      (fun x hx => hcon x hx) hel.1
    omega
  have hEcomm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := fun a ha b hb => by
    have := hel.1.is_comm.comm (⟨a, ha⟩ : ↥E') ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hu'Q : u' ∈ pCoreOf 2 H := hE' hu'E
  have hu'N : u' ∈ Subgroup.normalizer (P : Set G) :=
    h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H hu'Q)
  have hu'u : u' * u ∈ P := (hcos u' hu'Q).mpr hu'P
  have hact : actV hu'N = actV hun := actV_eq_of_mul_mem hu'N hun hu'u huu
  have hγ : ∀ v, actV hun (actV hun v) = v := fun v => actV_involutive hun huu v
  have hWR : kuW P H = psiPre (LinearMap.range (kuDeltaLin (actV hun))) :=
    h.kuW_eq_psiPre huQ hcos
  have hRfin : Module.finrank (ZMod 2) (LinearMap.range (kuDeltaLin (actV hun))) = 2 := by
    have hc8 := h.card_kuW
    rw [hWR, card_psiPre, h.card_center_P] at hc8
    have h4 : Nat.card (LinearMap.range (kuDeltaLin (actV hun))) = 4 := by omega
    have hpow : Nat.card (LinearMap.range (kuDeltaLin (actV hun))) =
        2 ^ Module.finrank (ZMod 2) (LinearMap.range (kuDeltaLin (actV hun))) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2)] <;> simp [ZMod.card]
    have h16 : 2 ^ Module.finrank (ZMod 2) (LinearMap.range (kuDeltaLin (actV hun))) = 2 ^ 2 :=
      (hpow.symm.trans h4).trans (by norm_num)
    exact Nat.pow_right_injective (le_refl 2) h16
  have hV4 := h.finrank_quotP
  have hrn := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) (kuDeltaLin (actV hun))
  have hle : LinearMap.range (kuDeltaLin (actV hun)) ≤ LinearMap.ker (kuDeltaLin (actV hun)) := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    exact kuDeltaLin_delta _ hγ v
  have hkerfin : Module.finrank (ZMod 2) (LinearMap.ker (kuDeltaLin (actV hun))) = 2 := by
    rw [hV4, hRfin] at hrn
    omega
  have hkerEq : LinearMap.range (kuDeltaLin (actV hun)) = LinearMap.ker (kuDeltaLin (actV hun)) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hRfin, hkerfin])
  have hW_le : E' ⊓ P ≤ kuW P H := by
    intro w hw
    obtain ⟨hwE, hwP⟩ := Subgroup.mem_inf.mp hw
    have hconj : conjP hu'N (⟨w, hwP⟩ : ↥P) = ⟨w, hwP⟩ := Subtype.ext (by
      show u' * w * u'⁻¹ = w
      rw [hEcomm u' hu'E w hwE]
      group)
    have hfix : actV hun (psi (⟨w, hwP⟩ : ↥P)) = psi (⟨w, hwP⟩ : ↥P) :=
      calc actV hun (psi (⟨w, hwP⟩ : ↥P)) = actV hu'N (psi (⟨w, hwP⟩ : ↥P)) := by rw [hact]
        _ = psi (conjP hu'N (⟨w, hwP⟩ : ↥P)) := actV_mk hu'N (⟨w, hwP⟩ : ↥P)
        _ = psi (⟨w, hwP⟩ : ↥P) := by rw [hconj]
    have hker_mem : psi (⟨w, hwP⟩ : ↥P) ∈ LinearMap.ker (kuDeltaLin (actV hun)) := by
      rw [LinearMap.mem_ker, kuDeltaLin_apply, hfix, add_self_eq_zero_V]
    have hrange : psi (⟨w, hwP⟩ : ↥P) ∈ LinearMap.range (kuDeltaLin (actV hun)) := by
      rw [hkerEq]
      exact hker_mem
    rw [hWR]
    exact mem_psiPre_iff.mpr ⟨hwP, hrange⟩
  have hEW : E' ⊓ P = kuW P H :=
    Subgroup.eq_of_le_of_card_ge hW_le (by rw [h.card_kuW]; omega)
  have hWE : kuW P H ≤ E' := by
    rw [← hEW]
    exact inf_le_left
  have hE'A : E' ≤ kuA P H := by
    intro e he
    refine Subgroup.mem_inf.mpr ⟨hE' he, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact hEcomm w (hWE hw) e he
  exact Subgroup.eq_of_le_of_card_ge hE'A (by omega)

end CFSG.GH74.QTGen4.Ku
