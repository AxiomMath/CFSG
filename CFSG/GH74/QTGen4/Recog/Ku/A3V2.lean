module

public import CFSG.GH74.QTGen4.Recog.Ku.O2M
public import CFSG.Quasithin.Vol2.Ch6NatSemi
public import CFSG.GH74.QTGen4.Recog.Ku.TCent

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

def kuFix {L V R : Subgroup G} {n : ℕ} (D : NatL2Data L V n) (hRL : R ≤ L) :
    Submodule D.K (Fin 2 → D.K) where
  carrier := {w | ∀ g : Subgroup.normalizer (V : Set G), (g : G) ∈ R → D.conj g w = w}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    intro g hg
    rw [map_add, ha g hg, hb g hg]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    intro g _
    exact map_zero _
  smul_mem' := by
    intro c w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    intro g hg
    obtain ⟨A, hA⟩ := D.exists_matrix_of_mem g (hRL hg)
    rw [hA, Matrix.mulVec_smul, ← hA w, hw g hg]

theorem mem_kuFix {L V R : Subgroup G} {n : ℕ} {D : NatL2Data L V n} {hRL : R ≤ L}
    {w : Fin 2 → D.K} :
    w ∈ kuFix D hRL ↔ ∀ g : Subgroup.normalizer (V : Set G), (g : G) ∈ R → D.conj g w = w :=
  Iff.rfl

def fixOne {L V : Subgroup G} {n : ℕ} (D : NatL2Data L V n) {a : G}
    (ha : a ∈ Subgroup.normalizer (V : Set G)) (haL : a ∈ L) : Submodule D.K (Fin 2 → D.K) where
  carrier := {w | D.conj ⟨a, ha⟩ w = w}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_add, hx, hy]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    exact map_zero _
  smul_mem' := by
    intro c w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    obtain ⟨A, hA⟩ := D.exists_matrix_of_mem ⟨a, ha⟩ haL
    rw [hA, Matrix.mulVec_smul, ← hA w, hw]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem kuR_le : kuR T M ≤ oTwoUpper M := inf_le_right

theorem mem_normalizer_V_of_mem_M (h : KuHyp G T M H P z) {g : G} (hg : g ∈ M) :
    g ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
  rw [← h.mNorm]; exact hg

theorem oTwoUpper_le_normalizer_V (h : KuHyp G T M H P z) :
    oTwoUpper M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
  intro g hg
  exact h.mem_normalizer_V_of_mem_M (oTwoUpper_le M hg)

theorem mem_kuV2_iff_fix (h : KuHyp G T M H P z) (v : ↥(pCoreOf 2 M)) :
    (v : G) ∈ kuV2 T M ↔
      Multiplicative.toAdd (h.mNat.data.E v) ∈ kuFix h.mNat.data (kuR_le (T := T) (M := M)) := by
  constructor
  · intro hv
    rw [mem_kuFix]
    intro g hg
    have hc : (v : G) ∈ Subgroup.centralizer (kuR T M : Set G) := hv.2
    have hcomm : (g : G) * (v : G) = (v : G) * (g : G) :=
      Subgroup.mem_centralizer_iff.mp hc (g : G) hg
    have hconj : conjAct (pCoreOf 2 M) g v = v := Subtype.ext (by
      rw [conjAct_apply_coe, hcomm, mul_inv_cancel_right])
    rw [h.mNat.data.conj_apply, hconj]
  · intro hfix
    have hE := mem_kuFix.mp hfix
    refine ⟨v.2, ?_⟩
    show (v : G) ∈ Subgroup.centralizer (kuR T M : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrL : r ∈ oTwoUpper M := (show r ∈ kuR T M from hr).2
    have hgN : r ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      h.oTwoUpper_le_normalizer_V hrL
    have h1 := hE ⟨r, hgN⟩ hr
    rw [h.mNat.data.conj_apply] at h1
    have h2 : conjAct (pCoreOf 2 M) ⟨r, hgN⟩ v = v :=
      h.mNat.data.E.injective (Multiplicative.toAdd.injective h1)
    have h3 := congrArg Subtype.val h2
    rw [conjAct_apply_coe] at h3
    exact mul_inv_eq_iff_eq_mul.mp h3

theorem kuFix_ne_top (h : KuHyp G T M H P z) : kuFix h.mNat.data (kuR_le (T := T) (M := M)) ≠ ⊤ := by
  intro htop
  have hall : ∀ w, w ∈ kuFix h.mNat.data (kuR_le (T := T) (M := M)) := fun w => by
    rw [htop]; exact Submodule.mem_top
  have hRV : kuR T M ≤ pCoreOf 2 M := by
    intro r hr
    have hrL : r ∈ oTwoUpper M := (show r ∈ kuR T M from hr).2
    have hrM : r ∈ M := oTwoUpper_le M hrL
    have hgN : r ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      h.mem_normalizer_V_of_mem_M hrM
    have hc : r ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 := mem_kuFix.mp (hall (Multiplicative.toAdd (h.mNat.data.E ⟨v, hv⟩))) ⟨r, hgN⟩ hr
      rw [h.mNat.data.conj_apply] at h1
      have h2 : conjAct (pCoreOf 2 M) ⟨r, hgN⟩ ⟨v, hv⟩ = ⟨v, hv⟩ :=
        h.mNat.data.E.injective (Multiplicative.toAdd.injective h1)
      have h3 := congrArg Subtype.val h2
      rw [conjAct_apply_coe] at h3
      exact (mul_inv_eq_iff_eq_mul.mp h3).symm
    have hrV : r ∈ M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) := ⟨hrM, hc⟩
    rw [h.mCent] at hrV
    exact hrV
  have hcard := Subgroup.card_le_of_le hRV
  rw [h.card_kuR, h.vCard] at hcard
  omega

theorem z_ne_zero_vec (h : KuHyp G T M H P z) :
    Multiplicative.toAdd (h.mNat.data.E ⟨z, h.z_mem_pCoreOf⟩) ≠ 0 := by
  intro h0
  have h1 : h.mNat.data.E ⟨z, h.z_mem_pCoreOf⟩ = 1 :=
    Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
  have h2 := congrArg Subtype.val ((MulEquiv.map_eq_one_iff h.mNat.data.E).mp h1)
  exact h.z_ne_one (by simpa using h2)

theorem finrank_kuFix (h : KuHyp G T M H P z) :
    Module.finrank h.mNat.data.K (kuFix h.mNat.data (kuR_le (T := T) (M := M))) = 1 := by
  have hne_bot : kuFix h.mNat.data (kuR_le (T := T) (M := M)) ≠ ⊥ := by
    intro hb
    apply h.z_ne_zero_vec
    have hm := (h.mem_kuV2_iff_fix ⟨z, h.z_mem_pCoreOf⟩).mp h.z_mem_kuV2
    rw [hb, Submodule.mem_bot] at hm
    exact hm
  have hlt : Module.finrank h.mNat.data.K (kuFix h.mNat.data (kuR_le (T := T) (M := M))) < 2 := by
    have := Submodule.finrank_lt h.kuFix_ne_top
    rwa [Module.finrank_fin_fun] at this
  have hpos : 0 < Module.finrank h.mNat.data.K
      (kuFix h.mNat.data (kuR_le (T := T) (M := M))) :=
    Nat.pos_of_ne_zero (fun h0 => hne_bot (Submodule.finrank_eq_zero.mp h0))
  omega

theorem card_kuFix (h : KuHyp G T M H P z) :
    Nat.card (kuFix h.mNat.data (kuR_le (T := T) (M := M))) = 4 := by
  rw [Module.natCard_eq_pow_finrank (K := h.mNat.data.K), h.finrank_kuFix, pow_one]
  exact h.mNat.data.card.trans (by norm_num)

theorem card_kuV2 (h : KuHyp G T M H P z) : Nat.card (kuV2 T M) = 4 := by
  rw [← h.card_kuFix]
  refine Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd (h.mNat.data.E ⟨x.1, x.2.1⟩),
        (h.mem_kuV2_iff_fix ⟨x.1, x.2.1⟩).mp x.2⟩
      invFun := fun w => ⟨((h.mNat.data.E.symm (Multiplicative.ofAdd w.1) :
          ↥(pCoreOf 2 M)) : G), (h.mem_kuV2_iff_fix _).mpr (by simp)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }

theorem fixOne_ne_top (h : KuHyp G T M H P z) {a : G}
    (haN : a ∈ Subgroup.normalizer (pCoreOf 2 M : Set G)) (haL : a ∈ oTwoUpper M)
    (haV : a ∉ pCoreOf 2 M) : fixOne h.mNat.data haN haL ≠ ⊤ := by
  intro htop
  have hall : ∀ w, h.mNat.data.conj ⟨a, haN⟩ w = w := fun w => by
    have hw : w ∈ fixOne h.mNat.data haN haL := by
      rw [htop]; exact Submodule.mem_top
    exact hw
  have haC : a ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := hall (Multiplicative.toAdd (h.mNat.data.E ⟨v, hv⟩))
    rw [h.mNat.data.conj_apply] at h1
    have h2 : conjAct (pCoreOf 2 M) ⟨a, haN⟩ ⟨v, hv⟩ = ⟨v, hv⟩ :=
      h.mNat.data.E.injective (Multiplicative.toAdd.injective h1)
    have h3 := congrArg Subtype.val h2
    rw [conjAct_apply_coe] at h3
    exact (mul_inv_eq_iff_eq_mul.mp h3).symm
  have haV' : a ∈ M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    ⟨oTwoUpper_le M haL, haC⟩
  rw [h.mCent] at haV'
  exact haV haV'

theorem centralizer_pCore_eq_kuV2 (h : KuHyp G T M H P z) {a : G} (ha : a ∈ kuR T M)
    (haV : a ∉ pCoreOf 2 M) :
    pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G) = kuV2 T M := by
  have haL : a ∈ oTwoUpper M := (show a ∈ kuR T M from ha).2
  have haN : a ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    h.mem_normalizer_V_of_mem_M (oTwoUpper_le M haL)
  have hsub : kuFix h.mNat.data (kuR_le (T := T) (M := M)) ≤ fixOne h.mNat.data haN haL := by
    intro w hw
    exact mem_kuFix.mp hw ⟨a, haN⟩ ha
  have hfin1 : Module.finrank h.mNat.data.K (fixOne h.mNat.data haN haL) ≤ 1 := by
    have hlt := Submodule.finrank_lt (h.fixOne_ne_top haN haL haV)
    rw [Module.finrank_fin_fun] at hlt
    omega
  have hfin2 : Module.finrank h.mNat.data.K
      (kuFix h.mNat.data (kuR_le (T := T) (M := M))) ≤
      Module.finrank h.mNat.data.K (fixOne h.mNat.data haN haL) := Submodule.finrank_mono hsub
  have heq : fixOne h.mNat.data haN haL = kuFix h.mNat.data (kuR_le (T := T) (M := M)) := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq hsub
    have := h.finrank_kuFix
    omega
  apply le_antisymm
  · rintro v ⟨hvV, hvc⟩
    have hav : a * v = v * a := Subgroup.mem_centralizer_iff.mp hvc a (Set.mem_singleton a)
    have hconj : conjAct (pCoreOf 2 M) ⟨a, haN⟩ ⟨v, hvV⟩ = ⟨v, hvV⟩ := by
      apply Subtype.ext
      rw [conjAct_apply_coe]
      show a * v * a⁻¹ = v
      rw [hav, mul_inv_cancel_right]
    have hfix : Multiplicative.toAdd (h.mNat.data.E ⟨v, hvV⟩) ∈
        kuFix h.mNat.data (kuR_le (T := T) (M := M)) := by
      rw [← heq]
      show h.mNat.data.conj ⟨a, haN⟩ _ = _
      rw [h.mNat.data.conj_apply, hconj]
    exact (h.mem_kuV2_iff_fix ⟨v, hvV⟩).mpr hfix
  · intro v hv
    refine ⟨hv.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact Subgroup.mem_centralizer_iff.mp hv.2 a ha

theorem centralizer_kuV2_T (h : KuHyp G T M H P z) :
    T ⊓ Subgroup.centralizer (kuV2 T M : Set G) = kuR T M := by
  have hRC : kuR T M ≤ Subgroup.centralizer (kuV2 T M : Set G) := fun r hr =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_iff.mp hv.2 r hr).symm
  have hRX : kuR T M ≤ T ⊓ Subgroup.centralizer (kuV2 T M : Set G) :=
    le_inf inf_le_left hRC
  have hXT : T ⊓ Subgroup.centralizer (kuV2 T M : Set G) ≤ T := inf_le_left
  have hd1 : Nat.card (kuR T M) ∣ Nat.card ↥(T ⊓ Subgroup.centralizer (kuV2 T M : Set G)) :=
    Subgroup.card_dvd_of_le hRX
  have hXle : Nat.card ↥(T ⊓ Subgroup.centralizer (kuV2 T M : Set G)) ≤ Nat.card T :=
    Subgroup.card_le_of_le hXT
  have hRle : Nat.card (kuR T M) ≤ Nat.card ↥(T ⊓ Subgroup.centralizer (kuV2 T M : Set G)) :=
    Subgroup.card_le_of_le hRX
  rw [h.card_kuR] at hd1 hRle
  rw [h.card_T] at hXle
  rcases (by omega : Nat.card ↥(T ⊓ Subgroup.centralizer (kuV2 T M : Set G)) = 64 ∨
      Nat.card ↥(T ⊓ Subgroup.centralizer (kuV2 T M : Set G)) = 128) with h64 | h128
  · exact (Subgroup.eq_of_le_of_card_ge hRX (by rw [h.card_kuR]; omega)).symm
  · exfalso
    have hTX : T ⊓ Subgroup.centralizer (kuV2 T M : Set G) = T :=
      Subgroup.eq_of_le_of_card_ge hXT (by rw [h.card_T]; omega)
    have hsub : kuV2 T M ≤ Subgroup.zpowers z := by
      intro v hv
      have hvT : v ∈ T := h.pCore_le_T hv.1
      refine h.center_T_le_zpowers v hvT (fun y hy => ?_)
      have hyX : y ∈ T ⊓ Subgroup.centralizer (kuV2 T M : Set G) := by
        rw [hTX]; exact hy
      exact (Subgroup.mem_centralizer_iff.mp hyX.2 v hv).symm
    have hc := Subgroup.card_le_of_le hsub
    rw [h.card_kuV2, h.card_zpowers] at hc
    omega

end KuHyp

end CFSG.GH74.QTGen4.Ku
