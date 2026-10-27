module

public import CFSG.CGT.PushingUpLit.T2K.FourFourC
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_map_conj (X : Subgroup G) (g : G) :
    Nat.card ↥(X.map (MulAut.conj g).toMonoidHom) = Nat.card ↥X :=
  (Nat.card_congr (Subgroup.equivMapOfInjective X _ (MulAut.conj g).injective).toEquiv).symm

omit [Finite G] in
theorem isElemAbelian_map_conj {X : Subgroup G} (hX : IsElemAbelian 2 X) (g : G) :
    IsElemAbelian 2 (X.map (MulAut.conj g).toMonoidHom) := CFSG.Open.IsElemAbelian.map hX _

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {X : Subgroup G} {g : G}
    (hg : X.map (MulAut.conj g).toMonoidHom = X) : g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← hg]
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  · intro hy
    rw [← hg] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    have h1 : g * x * g⁻¹ = g * y * g⁻¹ := by simpa [MulAut.conj_apply] using hxy
    have : x = y := mul_left_cancel (mul_right_cancel h1)
    rwa [← this]

omit [Finite G] in
theorem isMaxElemAbelian_map_conj {Q A : Subgroup G} (hA : IsMaxElemAbelian Q A) {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    IsMaxElemAbelian Q (A.map (MulAut.conj g).toMonoidHom) := by
  have hQ : Q.map (MulAut.conj g).toMonoidHom = Q := map_conj_eq_of_mem_normalizer hg
  refine ⟨?_, isElemAbelian_map_conj hA.2.1 g, fun B hB hBe => ?_⟩
  · rw [← hQ]
    exact Subgroup.map_mono hA.1
  · rw [card_map_conj]
    exact hA.2.2 B hB hBe

theorem normalizer_le_normalizer_thompsonJ (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (thompsonJ Q : Set G) := by
  intro g hg
  have h1 : (thompsonJ Q).map (MulAut.conj g).toMonoidHom ≤ thompsonJ Q := by
    unfold thompsonJ
    rw [Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hA => ?_
    exact le_iSup₂_of_le _ (isMaxElemAbelian_map_conj hA hg) le_rfl
  have h2 : (thompsonJ Q).map (MulAut.conj g).toMonoidHom = thompsonJ Q :=
    Subgroup.eq_of_le_of_card_ge h1 (by rw [card_map_conj])
  exact mem_normalizer_of_map_conj_eq h2

omit [Finite G] in
theorem le_thompsonJ' {Q A : Subgroup G} (hA : IsMaxElemAbelian Q A) : A ≤ thompsonJ Q :=
  le_iSup₂_of_le A hA le_rfl

omit [Finite G] in
theorem thompsonJ_le {Q : Subgroup G} : thompsonJ Q ≤ Q :=
  iSup_le fun _ => iSup_le fun hA => hA.1

theorem mem_normalizer_thompsonJ_of_forall {Q : Subgroup G} {g : G}
    (hg : ∀ D, IsMaxElemAbelian Q D → IsMaxElemAbelian Q (D.map (MulAut.conj g).toMonoidHom)) :
    g ∈ Subgroup.normalizer (thompsonJ Q : Set G) := by
  have h1 : (thompsonJ Q).map (MulAut.conj g).toMonoidHom ≤ thompsonJ Q := by
    unfold thompsonJ
    rw [Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hA => ?_
    exact le_iSup₂_of_le _ (hg A hA) le_rfl
  exact mem_normalizer_of_map_conj_eq
    (Subgroup.eq_of_le_of_card_ge h1 (by rw [card_map_conj]))

namespace T2Hyp

variable {L M T : Subgroup G} {n : ℕ}
variable (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple)
  (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
include h hE1 hT

theorem le_normalizer_P :
    L ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (blockU L : Set G) : Subgroup G) : Set G) := by
  have hMN := h.normal hE1
  have key : ∀ l ∈ L, ∀ p ∈ T ⊓ Subgroup.centralizer (blockU L : Set G),
      l * p * l⁻¹ ∈ T ⊓ Subgroup.centralizer (blockU L : Set G) := by
    intro l hl p hp
    have hpM : p ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨hT.le hp.1, hp.2⟩
    have h1 := h.natBlock.comm_centralizer_mem_blockU hMN hpM l hl
    have hVP : blockU L ≤ T ⊓ Subgroup.centralizer (blockU L : Set G) :=
      le_inf (NatBlock.blockU_le_sylow h.le hMN hT) (fun v hv =>
        Subgroup.mem_centralizer_iff.2 fun w hw => h.natBlock.blockU_comm w hw v hv)
    have e : l * p * l⁻¹ = (⁅p, l⁆)⁻¹ * p := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (inv_mem (hVP h1)) hp
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro p
  exact ⟨fun hp => key l hl p hp, fun hp => by
    have := key l⁻¹ (L.inv_mem hl) _ hp
    simpa [mul_assoc] using this⟩

theorem exists_max_le_P :
    ∃ A, IsMaxElemAbelian T A ∧ A ≤ T ⊓ Subgroup.centralizer (blockU L : Set G) := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
  by_cases hAV : A ≤ Subgroup.centralizer (blockU L : Set G)
  · exact ⟨A, hA, le_inf hA.1 hAV⟩
  · have H : Hyp45 L M T A n := ⟨h.natBlock, h.le, h.normal hE1, hT, hA, hAV⟩
    exact ⟨Hyp45.bGrp L A, H.isMaxElemAbelian_B, H.B_le_P⟩

theorem isMaxElemAbelian_T_of_P {D : Subgroup G}
    (hD : IsMaxElemAbelian (T ⊓ Subgroup.centralizer (blockU L : Set G)) D) :
    IsMaxElemAbelian T D := by
  obtain ⟨A, hA, hAP⟩ := h.exists_max_le_P hE1 hT
  refine ⟨hD.1.trans inf_le_left, hD.2.1, fun B hB hBe => ?_⟩
  exact (hA.2.2 B hB hBe).trans (hD.2.2 A hAP hA.2.1)

omit [Finite G] h hE1 hT in
theorem isMaxElemAbelian_P_of_le {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hAP : A ≤ T ⊓ Subgroup.centralizer (blockU L : Set G)) :
    IsMaxElemAbelian (T ⊓ Subgroup.centralizer (blockU L : Set G)) A :=
  ⟨hAP, hA.2.1, fun B hB hBe => hA.2.2 B (hB.trans inf_le_left) hBe⟩

theorem blockU_le_of_isMaxElemAbelian_P {D : Subgroup G}
    (hD : IsMaxElemAbelian (T ⊓ Subgroup.centralizer (blockU L : Set G)) D) : blockU L ≤ D := by
  have hMN := h.normal hE1
  have hVT : blockU L ≤ T := NatBlock.blockU_le_sylow h.le hMN hT
  have hVP : blockU L ≤ T ⊓ Subgroup.centralizer (blockU L : Set G) :=
    le_inf hVT (fun v hv => Subgroup.mem_centralizer_iff.2 fun w hw =>
      h.natBlock.blockU_comm w hw v hv)
  have hcomm : ∀ v ∈ blockU L, ∀ d ∈ D, v * d = d * v := fun v hv d hd =>
    Subgroup.mem_centralizer_iff.1 (hD.1 hd).2 v hv
  have hsup := isElemAbelian_sup' h.natBlock.isElemAbelian_blockU hD.2.1 hcomm
  have hle : blockU L ⊔ D ≤ T ⊓ Subgroup.centralizer (blockU L : Set G) := sup_le hVP hD.1
  have hcard := hD.2.2 _ hle hsup
  have heq : D = blockU L ⊔ D := Subgroup.eq_of_le_of_card_ge le_sup_right hcard
  exact le_sup_left.trans heq.ge

theorem thompsonJ_P_ne_bot : thompsonJ (T ⊓ Subgroup.centralizer (blockU L : Set G)) ≠ ⊥ := by
  obtain ⟨A, hA, hAP⟩ := h.exists_max_le_P hE1 hT
  have hAP' := isMaxElemAbelian_P_of_le hA hAP
  intro hbot
  have h1 : blockU L ≤ ⊥ := hbot ▸ (h.blockU_le_of_isMaxElemAbelian_P hE1 hT hAP').trans
    (le_thompsonJ' hAP')
  exact h.blockU_ne_bot (le_bot_iff.1 h1)

theorem normalizer_thompsonJ_P_le :
    Subgroup.normalizer (thompsonJ (T ⊓ Subgroup.centralizer (blockU L : Set G)) : Set G) ≤ M := by
  set P : Subgroup G := T ⊓ Subgroup.centralizer (blockU L : Set G) with hP
  have hJ2 : IsPGroup 2 (thompsonJ P) := hT.isPGroup.to_le (thompsonJ_le.trans inf_le_left)
  have hloc : IsPLocal 2 (Subgroup.normalizer (thompsonJ P : Set G)) :=
    ⟨thompsonJ P, h.thompsonJ_P_ne_bot hE1 hT, hJ2, rfl⟩
  obtain ⟨N, hle, hNmax⟩ := Sec15Final.exists_isMaximalTwoLocal_ge hloc
  have hL : L ≤ Subgroup.normalizer (thompsonJ P : Set G) :=
    fun l hl => normalizer_le_normalizer_thompsonJ P (h.le_normalizer_P hE1 hT hl)
  have hNM : N = M := by
    have : N ∈ maximalTwoLocalsContaining (L : Set G) := ⟨hNmax, fun x hx => hle (hL hx)⟩
    rw [h.unique] at this
    exact this
  rw [← hNM]
  exact hle

theorem isMaxElemAbelian_T_map_conj {g : G} (hgJ : g ∈ Subgroup.normalizer (thompsonJ T : Set G))
    {D : Subgroup G} (hD : IsMaxElemAbelian (T ⊓ Subgroup.centralizer (blockU L : Set G)) D) :
    IsMaxElemAbelian T (D.map (MulAut.conj g).toMonoidHom) := by
  have hJ : (thompsonJ T).map (MulAut.conj g).toMonoidHom = thompsonJ T :=
    map_conj_eq_of_mem_normalizer hgJ
  have hDT := h.isMaxElemAbelian_T_of_P hE1 hT hD
  have hle : D.map (MulAut.conj g).toMonoidHom ≤ T := by
    calc D.map (MulAut.conj g).toMonoidHom ≤ (thompsonJ T).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono (le_thompsonJ' hDT)
      _ = thompsonJ T := hJ
      _ ≤ T := thompsonJ_le
  refine ⟨hle, isElemAbelian_map_conj hDT.2.1 g, fun B hB hBe => ?_⟩
  rw [card_map_conj]
  exact hDT.2.2 B hB hBe

theorem exists_member_conj_not_le {g : G} (hgJ : g ∈ Subgroup.normalizer (thompsonJ T : Set G))
    (hgM : g ∉ M) :
    ∃ D, IsMaxElemAbelian (T ⊓ Subgroup.centralizer (blockU L : Set G)) D ∧
      IsMaxElemAbelian T (D.map (MulAut.conj g).toMonoidHom) ∧
      ¬ D.map (MulAut.conj g).toMonoidHom ≤ T ⊓ Subgroup.centralizer (blockU L : Set G) := by
  set P : Subgroup G := T ⊓ Subgroup.centralizer (blockU L : Set G) with hP
  have hDg : ∀ D, IsMaxElemAbelian P D → IsMaxElemAbelian T (D.map (MulAut.conj g).toMonoidHom) :=
    fun D hD => h.isMaxElemAbelian_T_map_conj hE1 hT hgJ hD
  by_contra hcon
  push Not at hcon
  have hall : ∀ D, IsMaxElemAbelian P D →
      IsMaxElemAbelian P (D.map (MulAut.conj g).toMonoidHom) := fun D hD =>
    isMaxElemAbelian_P_of_le (hDg D hD) (hcon D hD (hDg D hD))
  have hgP := mem_normalizer_thompsonJ_of_forall hall
  exact hgM (h.normalizer_thompsonJ_P_le hE1 hT hgP)

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
