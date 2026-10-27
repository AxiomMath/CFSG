module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaNoOddCover
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeData
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLModels
public import CFSG.LieType.ChevTwo.OutData
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreBasic
import CFSG.LocalAnalysis.GLTheoremB.I2810.Step0
import CFSG.LocalAnalysis.GLTheoremB.I2810.Induced
import CFSG.LocalAnalysis.GLTheoremB.I2810.StronglyReal
import CFSG.LocalAnalysis.GLTheoremB.I2810.LayerM
import CFSG.LocalAnalysis.GLTheoremB.I2810.Blocks
import CFSG.LocalAnalysis.GLTheoremB.I2810.Hyp3
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5Block
import CFSG.LocalAnalysis.GLTheoremB.I2810.Core
import CFSG.LocalAnalysis.GLTheoremB.I2810.Heart
import CFSG.LocalAnalysis.GLTheoremB.I2810.Omega
import CFSG.LocalAnalysis.GLTheoremB.I2810.Alt
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannA5
import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss18A5
public import CFSG.HardMathSupport.Cooperstein.StructureLie.McLaughlinShape
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.LieType.ChevTwo
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section Step0
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem step0 (h : Setup28 W K S) (hd : ¬ Concl28d K S) :
    Red28 W K S ∧ ∃ A, Off28 W K S A := by
  have hq := s0_quasi h
  have hnt : ¬ K ≤ Subgroup.centralizer (vOf W K S : Set X) := fun hK => hd (s0_concl28d_of_cent h hK)
  obtain ⟨hve, hvl, hvn⟩ := s0_v_props h
  have hw1le : W ≤ kerAct W K S := fun w hw =>
    ⟨h.hWS hw, fun k _ => by
      have h1 : ⁅w, k⁆ = w * (k * w⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
      rw [h1]
      exact W.mul_mem hw (Subgroup.Normal.conj_mem inferInstance _ (W.inv_mem hw) k)⟩
  have hw1S : kerAct W K S ≤ S := fun s hs => hs.1
  refine ⟨⟨hq, s0_o2K h, hw1le, hw1S, s0_w1_nrm h, ?_, s0_k_w1 h, hve, hvl, hvn, hnt,
    s0_cent_comm h hq hnt⟩, ?_⟩
  · exact fun c hc => hw1le (h.hC (Subgroup.centralizer_le (fun w hw => hw1le hw) hc))
  · obtain ⟨A, hAm, hAn⟩ := s0_exists_offender h hd
    exact ⟨A, hAm, hAn, s0_off h hq hnt hAm⟩

end Step0

section Induced
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem card_two_or_four (h : Setup28 W K S) {A : Subgroup X} (hA : Off28 W K S A)
    (hle : Nat.card ↥(indAut W K A) ≤ 4) :
    Nat.card ↥(indAut W K A) = 2 ∨ Nat.card ↥(indAut W K A) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAS : A ≤ S := hA.isMax.1
  have hc := c_card_indAut h hAS
  have hpg : IsPGroup 2 ↥A := hA.isMax.2.1.isPGroup
  obtain ⟨m, hm⟩ := hpg.index ((kerAct W K S).subgroupOf A)
  have hne : Nat.card ↥(indAut W K A) ≠ 1 := by
    intro h1
    rw [hc, Subgroup.relIndex_eq_one] at h1
    exact hA.not_le h1
  rw [hc] at hne hle ⊢
  have hm' : (kerAct W K S).relIndex A = 2 ^ m := hm
  rw [hm'] at hne hle ⊢
  have hm1 : m ≠ 0 := by rintro rfl; simp at hne
  have hm2 : m ≤ 2 := by
    by_contra hcon
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases (by omega : m = 1 ∨ m = 2) with rfl | rfl <;> simp

end Induced

section ActionOnV
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem vOf_comm (hR : Red28 W K S) (a b : ↥(vOf W K S)) : a * b = b * a :=
  Subtype.ext (hR.v_elem.comm a.2 b.2)

theorem vOf_sq (hR : Red28 W K S) (v : ↥(vOf W K S)) : v * v = 1 :=
  Subtype.ext (by simpa [pow_two] using hR.v_elem.2 v v.2)

end ActionOnV

section CaseFour
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem case_four (h : Setup28 W K S) (hR : Red28 W K S) {A : Subgroup X} (hA : Off28 W K S A)
    (h4 : Hyp28Four W K S) : False := by
  have hS2 : Nat.card ↥(indAut W K S) = 2 := h4.2.1
  have hle : Nat.card ↥(indAut W K A) ≤ 2 :=
    hS2 ▸ Subgroup.card_le_of_le (indAut_mono hA.isMax.1)
  have hc : Nat.card ↥(indAut W K A) = 2 := by
    rcases card_two_or_four h hA (by omega) with h | h <;> omega
  obtain ⟨a, haA, hna, ha2, htr⟩ := transv_of_card_two h hR hA hc
  exact inverts_five_contra h hR (hA.isMax.1 haA) ha2 htr
    (hyp4_inverts_five h h4 (hA.isMax.1 haA) hna)

end CaseFour

section CaseOneRank
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem inverts_big_contra (h : Setup28 W K S)
    (hR : Red28 W K S) {A : Subgroup X}
    (hA : Off28 W K S A) (hc : Nat.card ↥(indAut W K A) = 4) {a : X} (haA : a ∈ A)
    (hinv : Inverts W K a (fun m => 5 < m)) : False := by
  have haS : a ∈ S := hA.isMax.1 haA
  have ha2 : a ^ 2 = 1 := hA.isMax.2.1.2 a haA
  obtain ⟨y, hyodd, ⟨m, -, hm5, hmy⟩, hyinv⟩ := inverts_to_aut h hR haS ha2 hinv
  have hτ := vAct_sq hR (Subgroup.mem_sup_right haS) ha2
  have hidx := offender_fix_index h hR hA hc haA
  have hfin : Finite (MulAut ↥(vOf W K S)) :=
    Finite.of_injective (fun f : MulAut ↥(vOf W K S) => (f : ↥(vOf W K S) → ↥(vOf W K S)))
      DFunLike.coe_injective
  have hord := strongly_real_small (vOf_comm hR) (vOf_sq hR) hτ hyinv hyodd hidx
  have hle : m ≤ orderOf y := Nat.le_of_dvd (orderOf_pos y) hmy
  omega

theorem hyp1_card_two (hOut : Chev2OutTwoRank)
    (hInv : Chev2RankTwoInverts) (h : Setup28 W K S)
    (h1 : Hyp28One W K S) {A : Subgroup X} (hR : Red28 W K S) (hA : Off28 W K S A) :
    Nat.card ↥(indAut W K A) = 2 := by
  have hle : Nat.card ↥(indAut W K A) ≤ 4 :=
    c_le_four_one hOut h h1 (indAut_mono hA.isMax.1) (c_indAut_elemAbelian h hA.isMax.1 hA.isMax.2.1)
  rcases card_two_or_four h hA hle with h2 | h4
  · exact h2
  · obtain ⟨a, haA, -, hinv⟩ := hyp1_inverts_big hInv h h1 hA h4
    exact (inverts_big_contra h hR hA h4 haA hinv).elim

end CaseOneRank

section LayerM
variable {V : Type} [Group V] [Finite V]
variable {Kh Eh : Subgroup (MulAut V)} {n : ℕ} {π : ↥Kh →* ↥(alternatingGroup (Fin n))}
  {Vv V₄ : Subgroup ↥(alternatingGroup (Fin n))}

theorem a7_structure
    (hc : ∀ a b : V, a * b = b * a) (h2 : ∀ v : V, v * v = 1)
    {π7 : ↥Kh →* ↥(alternatingGroup (Fin 7))} {Vv7 V₇ : Subgroup ↥(alternatingGroup (Fin 7))}
    (d : ASData Kh Eh 7 π7 Vv7 V₇) (hidx : (fixV' Kh).index ≤ 16) : A7Struct Kh := by
  obtain ⟨hZ, hi⟩ := a7_center_index hc h2 d hidx
  obtain ⟨h16, hirr⟩ := a7_comm_irred hc h2 d hZ hi
  exact ⟨hZ, h16, hirr⟩

theorem as_four
    (hc : ∀ a b : V, a * b = b * a) (h2 : ∀ v : V, v * v = 1)
    (d : ASData Kh Eh n π Vv V₄) (hE : Nat.card ↥Eh = 4) (h5 : n ≠ 5) (h6 : n ≠ 6) (h8 : n ≠ 8) :
    n = 7 ∧ A7Struct Kh := by
  obtain ⟨hV₄, hVv⟩ := d.root
  have hcard := card_Vv_eq d
  have hVv4 : Nat.card ↥Vv = 4 := hcard.trans hE
  have hn := d.hn
  by_cases h7 : n = 7
  · subst h7
    obtain ⟨s, xs, hs, -, hgen⟩ := perm_gen_seven hV₄ hVv (Or.inr hVv4)
    obtain ⟨J, hJi, hJK, hJ⟩ := lift_core d xs
    have hKJ : Kh ≤ J := kh_le_J d hgen hJK hJ
    have hidx : (fixV' Kh).index ≤ 16 := by
      have h1 : (fixV' Kh).index ∣ (fixV' J).index :=
        Subgroup.index_dvd_of_le (fixV'_le_of_le hKJ)
      have h2' : (fixV' Kh).index ≤ (fixV' J).index :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
      rw [hE] at hJi
      rw [hVv4] at hs
      exact h2'.trans (hJi.trans hs)
    exact ⟨rfl, a7_structure hc h2 d hidx⟩
  · exfalso
    have h9 : 9 ≤ n := by omega
    obtain ⟨s, xs, hs, F, hFG, hF⟩ := perm_gen_nine h9 hV₄ hVv (Or.inr hVv4)
    obtain ⟨J, hJi, hJK, hJ⟩ := lift_core d xs
    obtain ⟨Y, hYJ, π, hπ, hker⟩ := cover_A9 d hFG hF hJK hJ
    rw [hE] at hJi
    rw [hVv4] at hs
    exact a9_exclusion hc h2 (hJi.trans hs) hYJ π hπ hker

theorem as_two (hc : ∀ a b : V, a * b = b * a) (h2 : ∀ v : V, v * v = 1)
    (d : ASData Kh Eh n π Vv V₄) (hE : Nat.card ↥Eh = 2) (h5 : n ≠ 5) (h6 : n ≠ 6) (h8 : n ≠ 8) :
    False := by
  obtain ⟨hV₄, hVv⟩ := d.root
  have hcard := card_Vv_eq d
  have hVv2 : Nat.card ↥Vv = 2 := hcard.trans hE
  have hn := d.hn
  by_cases h7 : n = 7
  · subst h7
    obtain ⟨s, xs, -, hs8, hgen⟩ := perm_gen_seven hV₄ hVv (Or.inl hVv2)
    obtain ⟨J, hJi, hJK, hJ⟩ := lift_core d xs
    have hKJ : Kh ≤ J := kh_le_J d hgen hJK hJ
    have hidx : (fixV' Kh).index ≤ 8 := by
      have h1 : (fixV' Kh).index ∣ (fixV' J).index :=
        Subgroup.index_dvd_of_le (fixV'_le_of_le hKJ)
      have h2' : (fixV' Kh).index ≤ (fixV' J).index :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
      have hs8' := hs8 hVv2
      rw [hE] at hJi
      rw [hVv2] at hs8'
      exact h2'.trans (hJi.trans hs8')
    exact a7_small_false hc h2 d hidx
  · have h9 : 9 ≤ n := by omega
    obtain ⟨s, xs, hs, F, hFG, hF⟩ := perm_gen_nine h9 hV₄ hVv (Or.inl hVv2)
    obtain ⟨J, hJi, hJK, hJ⟩ := lift_core d xs
    obtain ⟨Y, hYJ, π, hπ, hker⟩ := cover_A9 d hFG hF hJK hJ
    rw [hE] at hJi
    rw [hVv2] at hs
    exact a9_exclusion hc h2 (hJi.trans hs) hYJ π hπ hker

end LayerM

section Shared
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem block_unique (h : Setup28 W K S) (hR : Red28 W K S) {U₁ U₂ : Subgroup X}
    (sf : SingleFactor K (vOf W K S) U₁ U₂)
    (hE : ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S) :
    ∀ (n : ℕ) (T : Fin (n + 1) → Subgroup X), IsChiefSeriesIn K (pCoreOf 2 K) T →
      ∃! i : Fin n, ¬ ⁅T i.succ, K⁆ ≤ T i.castSucc := by
  intro n T hT
  obtain ⟨i, hi⟩ := block_exists_noncentral h hR sf hE n T hT
  exact ⟨i, hi, fun j hj => block_unique_noncentral h hR sf hE n T hT j i hj hi⟩

theorem isGLBlock_of (h : Setup28 W K S) (hR : Red28 W K S) {U₁ U₂ : Subgroup X}
    (sf : SingleFactor K (vOf W K S) U₁ U₂)
    (hE : ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S)
    (hZ : Subgroup.center ↥(bar W K) = ⊥) : IsGLBlock (⊤ : Subgroup X) K where
  le := le_top
  subnormal := h.hK.1
  residual := fun N _ hN => block_residual h N hN
  simple := block_simple h hR hZ
  commutator_le := block_commutator_le h hR hE
  unique_noncentral := block_unique h hR sf hE

end Shared

section CaseThree
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem n_ne_small (hq : IsQuasisimple ↥(bar W K)) (hnc : ¬ InChevTwo ↥(bar W K)) {n : ℕ}
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))) :
    n ≠ 5 ∧ n ≠ 6 ∧ n ≠ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro hn <;> subst hn <;>
    exact hnc ⟨hq, Or.inr (Or.inl ⟨_, by omega, ⟨e⟩⟩)⟩

theorem glue_in (h : Setup28 W K S) (hR : Red28 W K S) {A : Subgroup X} (hA : Off28 W K S A)
    {n : ℕ} (hn : 5 ≤ n)
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n)))
    (hact : ActsLikeSubRootFourCQ (bar W S) (bar W K) n e) :
    ∃ (π : ↥(khOf hR) →* ↥(alternatingGroup (Fin n))) (Vv V₄ : Subgroup ↥(alternatingGroup (Fin n))),
      ASData (khOf hR) (ehOf hR A) n π Vv V₄ := by
  obtain ⟨hperf, hnt, ho2⟩ := glue_basic h hR
  obtain ⟨π, hsurj, hker, hπ⟩ := glue_pi h hR e
  obtain ⟨Vv, V₄, hroot, hVv, a1, a2⟩ := glue_act h hR hA e hact π hπ
  obtain ⟨hab, hnorm, hfaith, hoff⟩ := glue_misc h hR hA
  exact ⟨π, Vv, V₄, ⟨hn, hperf, hnt, ho2, hsurj, hker, ⟨hroot, hVv⟩, hab, hnorm, hfaith, a1, a2, hoff⟩⟩

section A5Leaves
variable {e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin 7))}
  {V₄ B : Subgroup ↥(alternatingGroup (Fin 7))} {Ik : Subgroup X}

theorem a5_I_o2_quot (h : Setup28 W K S) (hR : Red28 W K S) (d : A5Data W K S e V₄ B Ik) :
    pCoreOf 2 (Ik ⊔ S) = kerAct W K S ∧
      Nonempty (↥(Ik ⊔ S) ⧸ CFSG.pCore 2 ↥(Ik ⊔ S) ≃* ↥(alternatingGroup (Fin 5))) := by
  obtain ⟨φ, hφ, hker⟩ := a5_I_hom h hR d
  exact oTwo_of_hom (le_sup_of_le_right hR.w1_S) (h.hS.to_le hR.w1_S) φ hφ hker

theorem a5_frame_of_data (h : Setup28 W K S) (hR : Red28 W K S) (d : A5Data W K S e V₄ B Ik) :
    A5Frame W K S (Ik ⊔ S) := by
  have hq := a5_I_o2_quot h hR d
  have hdz := a5_I_dec_zker h hR d
  exact ⟨le_sup_of_le_right hR.w1_S, sup_le (d.Ik_le.trans le_sup_left) le_sup_right, le_sup_right,
    a5_I_sylow h hR d, hq.2, hq.1, hdz.1, hdz.2, a5_I_gen h hR d⟩

end A5Leaves

theorem a5_frame (h : Setup28 W K S) (hR : Red28 W K S)
    {e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin 7))}
    (hroot : ActsLikeRootFourCQ (bar W S) (bar W K) 7 e)
    (hS4 : Nat.card ↥(bar W S ⊓ bar W K) = 4) (hind : Nat.card ↥(indAut W K S) = 4) :
    ∃ I, A5Frame W K S I := by
  obtain ⟨V₄, hV₄, hsv⟩ := a5_S_dec h hR hroot hS4 hind
  obtain ⟨B, hVB, hBq, hBgen⟩ := a7_gen_A5 hV₄
  obtain ⟨Ik, hle, hinto, honto, hker⟩ := a5_lift h e hBq
  have d : A5Data W K S e V₄ B Ik :=
    ⟨hV₄, hsv, a5_NK h hR hsv, hVB, hBq, hBgen, hle, hinto, honto, hker⟩
  exact ⟨Ik ⊔ S, a5_frame_of_data h hR d⟩

theorem a5_cent (hR : Red28 W K S) {I : Subgroup X} (hI : A5Frame W K S I) :
    I ⊓ Subgroup.centralizer (vOf W K S : Set X) = kerAct W K S := by
  apply le_antisymm
  · rintro i ⟨hiI, hiC⟩
    obtain ⟨k, hkK, hkI, hik⟩ := hI.dec i hiI
    have hkC : ∀ v ∈ vOf W K S, k * v = v * k := by
      intro v hv
      have hw : (i * k⁻¹) * v = v * (i * k⁻¹) := (hv.2.1 (i * k⁻¹) hik).symm
      have hi : v * i = i * v := Subgroup.mem_centralizer_iff.1 hiC v hv
      have h3 : k⁻¹ * v = v * k⁻¹ := by
        have h4 : i * (k⁻¹ * v) = i * (v * k⁻¹) :=
          calc i * (k⁻¹ * v) = (i * k⁻¹) * v := by group
            _ = v * (i * k⁻¹) := hw
            _ = (v * i) * k⁻¹ := by group
            _ = (i * v) * k⁻¹ := by rw [hi]
            _ = i * (v * k⁻¹) := by group
        exact mul_left_cancel h4
      calc k * v = k * (v * k⁻¹) * k := by group
        _ = k * (k⁻¹ * v) * k := by rw [h3]
        _ = v * k := by group
    have hzk : k ∈ zPre W K := ⟨hkK, hR.cent_comm k (Subgroup.mem_sup_left hkK) hkC⟩
    have hkW : k ∈ kerAct W K S := hI.zker ⟨hkI, hzk⟩
    have h5 : (i * k⁻¹) * k ∈ kerAct W K S := (kerAct W K S).mul_mem hik hkW
    simpa using h5
  · intro w hw
    refine ⟨hI.w1_le hw, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
    exact hv.2.1 w hw

theorem a5_pushHyp (hR : Red28 W K S) {I : Subgroup X} (hI : A5Frame W K S I) :
    CFSG.Quasithin.F53Push.PushHyp I S (vOf W K S) := by
  refine ⟨hI.sylow, hI.I_le.trans (N_le_normalizer_V hR), hR.v_elem, ?_, ?_⟩
  · rw [hI.o2]; exact hR.v_le
  · rw [hI.o2]; exact a5_cent hR hI

theorem a5_J_not_le {A : Subgroup X} (hA : Off28 W K S A) {I : Subgroup X} (hI : A5Frame W K S I) :
    ¬ Quasithin.thompsonJ S ≤ pCoreOf 2 I := by
  intro hJ
  apply hA.not_le
  rw [← hI.o2]
  have h1 : A ≤ Quasithin.thompsonJ S :=
    le_iSup₂ (f := fun (B : Subgroup X) (_ : Quasithin.IsMaxElemAbelian S B) => B) A hA.isMax
  exact h1.trans hJ

theorem a5_apply (h : Setup28 W K S) (hR : Red28 W K S) (hd : ¬ Concl28d K S) {A : Subgroup X}
    (hA : Off28 W K S A) {I : Subgroup X} (hI : A5Frame W K S I) :
    ∃ p ∈ K, p ∉ zPre W K ∧ ∀ w ∈ kerAct W K S, ⁅p, w⁆ ∈ vOf W K S := by
  have hPH := a5_pushHyp hR hI
  have hnat := CFSG.Quasithin.F53Push.hss18A5_holds X I S (vOf W K S) hPH hI.quot (a5_J_not_le hA hI)
  have hB := CFSG.Quasithin.F53Push.baumann_c_a5 hPH hI.quot hnat (a5_nochar h hR hd hI)
  obtain ⟨p, hpK, hpz, hpI⟩ := a5_pick h hR hI
  refine ⟨p, hpK, hpz, fun w hw => ?_⟩
  have hw' : w ∈ pCoreOf 2 I := hI.o2 ▸ hw
  have h1 := hB (Subgroup.commutator_mem_commutator hw' hpI)
  rw [← commutatorElement_inv]
  exact (vOf W K S).inv_mem h1

theorem case_three
    (h : Setup28 W K S) (hR : Red28 W K S) (hd : ¬ Concl28d K S) {A : Subgroup X}
    (hA : Off28 W K S A) (h3 : Hyp28Three W K S) : Concl28c W K S := by
  obtain ⟨n, e, hn5, hact⟩ := hyp3_n h h3
  obtain ⟨hne5, hne6, hne8⟩ := n_ne_small hR.quasi h3.2.1 e
  have hAS : Nat.card ↥(indAut W K A) ≤ Nat.card ↥(indAut W K S) :=
    Subgroup.card_le_of_le (indAut_mono hA.isMax.1)
  have hle : Nat.card ↥(indAut W K A) ≤ 4 := hAS.trans (c_le_four_three h h3)
  obtain ⟨π, Vv, V₄, d⟩ := glue_in h hR hA hn5 e hact
  have hVc := vOf_comm hR
  have hV2 := vOf_sq hR
  have hcardE := glue_card h hR hA
  rcases card_two_or_four h hA hle with h2 | h4
  · exact (as_two hVc hV2 d (hcardE.trans h2) hne5 hne6 hne8).elim
  · obtain ⟨hn7, hstruct⟩ := as_four hVc hV2 d (hcardE.trans h4) hne5 hne6 hne8
    subst hn7
    have hge : 4 ≤ Nat.card ↥(indAut W K S) := h4 ▸ hAS
    have hroot := rootFour_of_card h hact hge
    have hind : Nat.card ↥(indAut W K S) = 4 := le_antisymm (c_le_four_three h h3) hge
    refine ⟨e, hroot, fun hS4 => ?_⟩
    have hA7 := glue_a7 h hR hstruct
    obtain ⟨I, hI⟩ := a5_frame h hR hroot hS4 hind
    obtain ⟨p, hpK, hpz, hpE⟩ := a5_apply h hR hd hA hI
    have hE := normal_closure_K h hR hpK hpz hpE
    have hZ := centre_trivial h hR hE hA7.ztriv
    refine ⟨isGLBlock_of h hR hA7.sf hE hZ, ⟨isoOfCenterBot hZ e⟩, fun V' U hU => ?_⟩
    have := chief_card_transfer h hR hA7.sf hE hU
    simpa [hA7.card16] using this

end CaseThree

section Core
open CFSG.ComponentClassification.OutcomeLocal CFSG.HardMathSupport.Cooperstein.StructureLie
  CFSG.LocalAnalysis.ComponentInitial
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem trans_sectionM (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) (ha2 : a ^ 2 = 1) (htr : TransvOn (vOf W K S) a) :
    ∃ U₁ U₂ : Subgroup X, TransSectionM K (vOf W K S) U₁ U₂ a := by
  obtain ⟨u, U₁, U₂, hl⟩ := trans_lattice h hR haS hna ha2 htr
  exact ⟨U₁, U₂, trans_sectionM_of_lattice h hR haS hna ha2 hl⟩

theorem omega_of_orth {a : X} {U₁ U₂ : Subgroup X} {P : Type} [AddCommGroup P] [Module (ZMod 2) P]
    [Finite P] {ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P}
    {φ : ↥U₁ →* Multiplicative P} (hd : SecRepData (Mof K a) U₁ U₂ ρ φ)
    (htriv : ∀ k : ↥K, (k : X) ∈ W → ρ ⟨k, Subgroup.mem_sup_left k.2⟩ = 1)
    (htr : IsF2Transvection (ρ (aM K a))) {Q : QuadraticForm (ZMod 2) P}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hH : ρ.range = orthGL Q)
    (hL : (K.subgroupOf (Mof K a)).map ρ = ⁅orthGL Q, orthGL Q⁆)
    (hperf : ⁅(K.subgroupOf (Mof K a)).map ρ, (K.subgroupOf (Mof K a)).map ρ⁆ =
      (K.subgroupOf (Mof K a)).map ρ)
    (hnt : (K.subgroupOf (Mof K a)).map ρ ≠ ⊥) : OmegaModel W K a U₁ U₂ := by
  have hnt' : ⁅orthGL Q, orthGL Q⁆ ≠ ⊥ := hL ▸ hnt
  have hperf' : ⁅⁅orthGL Q, orthGL Q⁆, ⁅orthGL Q, orthGL Q⁆⁆ = ⁅orthGL Q, orthGL Q⁆ := by
    rw [← hL]; exact hperf
  obtain ⟨n, hn, hplus | hminus⟩ := orth_coords Q hQ hperf' hnt'
  · obtain ⟨φc, hφc⟩ := hplus
    exact ⟨n, hn, Or.inl (omega_model_of_coords _ hd htriv htr φc hφc hH hL)⟩
  · obtain ⟨φc, hφc⟩ := hminus
    exact ⟨n, hn, Or.inr (omega_model_of_coords _ hd htriv htr φc hφc hH hL)⟩

theorem isAlt_transv_swap {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]
    {L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)} {m : ℕ} (hm : 5 ≤ m)
    (hA : IsAltModel L m) {τ : LinearMap.GeneralLinearGroup (ZMod 2) P} (hτ : IsF2Transvection τ)
    (hτn : τ ∈ Subgroup.normalizer (L : Set (LinearMap.GeneralLinearGroup (ZMod 2) P))) :
    AltSwapConcl L m τ := by
  by_cases h6 : m = 6
  · subst h6; exact isAlt_transv_swap_six hA hτ hτn
  · exact isAlt_transv_swap_ne6 hm h6 hA hτ hτn

theorem alt_of_sym {a : X} {U₁ U₂ : Subgroup X} {P : Type} [AddCommGroup P] [Module (ZMod 2) P]
    [Finite P] {ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P}
    {φ : ↥U₁ →* Multiplicative P} (hd : SecRepData (Mof K a) U₁ U₂ ρ φ)
    (htriv : ∀ k : ↥K, (k : X) ∈ W → ρ ⟨k, Subgroup.mem_sup_left k.2⟩ = 1)
    (htr : IsF2Transvection (ρ (aM K a)))
    (htn : ρ (aM K a) ∈ Subgroup.normalizer
      (((K.subgroupOf (Mof K a)).map ρ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)) :
        Set (LinearMap.GeneralLinearGroup (ZMod 2) P)))
    (hsym : SymSpShape ρ.range)
    (hL : (K.subgroupOf (Mof K a)).map ρ = ⁅ρ.range, ρ.range⁆)
    (hperf : ⁅(K.subgroupOf (Mof K a)).map ρ, (K.subgroupOf (Mof K a)).map ρ⁆ =
      (K.subgroupOf (Mof K a)).map ρ)
    (hnt : (K.subgroupOf (Mof K a)).map ρ ≠ ⊥) : AltModel W K a U₁ U₂ := by
  obtain ⟨m, hm, hA⟩ := sym_isAlt hsym hL hperf hnt
  obtain ⟨σ, φa, θ, hσ, hφ, hσθ⟩ := isAlt_transv_swap hm hA htr htn
  exact altModel_of_isAlt hd htriv hm σ φa θ hσ hφ hσθ

theorem core (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) (ha2 : a ^ 2 = 1) (htr : TransvOn (vOf W K S) a)
    (hout : ¬ IndInner W K a) :
    ∃ U₁ U₂ : Subgroup X, TransSection K (vOf W K S) U₁ U₂ a ∧
      (OmegaModel W K a U₁ U₂ ∨ AltModel W K a U₁ U₂) := by
  obtain ⟨U₁, U₂, htsM⟩ := trans_sectionM h hR haS hna ha2 htr
  have hKa : ∀ x ∈ K, a * x * a⁻¹ ∈ K := fun x hx =>
    ((Subgroup.mem_normalizer_iff.1 (h.hN haS) x).1 hx)
  have hts : TransSection K (vOf W K S) U₁ U₂ a :=
    ⟨kirred_of_irredM hKa hR.v_elem htsM, htsM.asec⟩
  have hel : IsElemAbelian 2 U₁ := hR.v_elem.mono htsM.le.2
  obtain ⟨P, _, _, _, ρ, φ, hd⟩ := secRep_exists K a ha2 hKa U₁ U₂ hel htsM.le.1 htsM.inv₁
    htsM.inv₂ htsM.asec.inv₁ htsM.asec.inv₂
  obtain ⟨hsh, htr', htn⟩ := shape_hyps h hR haS hna ha2 hts ρ φ hd
    (outer_rho h hR haS hna hts hout ρ φ hd)
  obtain ⟨hn1, hgen, hirr, hLH, hidx, hperf, hL1⟩ := hsh
  obtain ⟨hLeq, hcases⟩ := shape_of_perfect_index_two hn1 _ _ hgen hirr hLH hidx hperf hL1
  have htriv := rho_triv_of_W h hR htsM.le.2 hd
  refine ⟨U₁, U₂, hts, ?_⟩
  rcases hcases with hsp | ⟨Q, hQ, hH⟩ | hsym
  · exact Or.inr (alt_of_sym hd htriv htr' htn (Or.inl hsp) hLeq hperf hL1)
  · exact Or.inl (omega_of_orth hd htriv htr' hQ hH (by rw [hLeq]; congr 1) hperf hL1)
  · exact Or.inr (alt_of_sym hd htriv htr' htn (Or.inr hsym) hLeq hperf hL1)

end Core

section CaseOneTwo
open CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem heart (h : Setup28 W K S) (hR : Red28 W K S) (hd : ¬ Concl28d K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) (hS2 : ∀ s ∈ S, s ∈ kerAct W K S ∨ a⁻¹ * s ∈ kerAct W K S)
    (hcm : CentMax W K S a) (hp : ThreeElt W K S a) :
    ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S := by
  obtain ⟨p, hpK, hp3, hpn, hpa, hpas, hpz⟩ := hp
  rcases heart_s3 h hR haS hna hS2 hpK hp3 hpn hpa with ⟨C, hC0, hCc, hpC⟩ | hE
  · exfalso
    apply hd
    refine ⟨C, hC0, hCc, ?_⟩
    have key := hcm (K ⊓ Subgroup.normalizer (C : Set X)) inf_le_left
      (fun k hk hkS => ⟨hk, IsCharIn.normalizer_le hCc (ccent_normalizes h hkS)⟩)
      ⟨p, ⟨hpK, hpC⟩, hpas⟩
    exact fun k hk => (key hk).2
  · exact normal_closure_K h hR hpK hpz hE

theorem case_one
    (hOut : Chev2OutTwoRank) (hInv : Chev2RankTwoInverts) (hL1 : OmegaTwoAutTwoPart)
    (h : Setup28 W K S) (hR : Red28 W K S) (hd : ¬ Concl28d K S) {A : Subgroup X}
    (hA : Off28 W K S A) (h1 : Hyp28One W K S) : Concl28a W K S := by
  have hc2 := hyp1_card_two hOut hInv h h1 hR hA
  obtain ⟨a, haA, hna, ha2, htr⟩ := transv_of_card_two h hR hA hc2
  have haS : a ∈ S := hA.isMax.1 haA
  obtain ⟨U₁, U₂, hts, hmod⟩ := core h hR haS hna ha2 htr (c1_outer h h1 haS hna)
  rcases hmod with hm | hAlt
  · obtain ⟨n, hn2, hΩ⟩ := omega_n_two h hR h1 hm
    have hS2 := c1_cardS_of_one_le hL1 h hR h1 hA hc2 (by omega) hΩ
    have hZ := OmegaCentre.centre_trivial_of_cover OmegaCentre.omegaNoOddCover_holds h hR hn2 hΩ
    have hE := heart h hR hd haS hna (S_cases h haS hna hS2)
      (centMax_of_omega_of_centre h hR hts hZ haS hna hS2 hn2 hΩ)
      (threeElt_of_omega_of_centre h hR hts hZ haS hn2 hΩ)
    have hblock := isGLBlock_of h hR hts.toSingleFactor hE hZ
    exact ⟨h1, n, hn2, omega_final h hR hts.toSingleFactor hE hZ hS2 hblock haS hna hΩ⟩
  · exact (alt_not_hyp1 h hR h1 hAlt).elim

theorem omega_alt_degree (h : Setup28 W K S) (hR : Red28 W K S) {a : X} {U₁ U₂ : Subgroup X}
    (hts : TransSection K (vOf W K S) U₁ U₂ a) (hAlt : InAlt ↥(bar W K)) {n : ℕ} (hn : 1 ≤ n)
    (hΩ : OmegaAny W K a U₁ U₂ n) :
    (n = 1 ∧ OmegaMinus W K a U₁ U₂ 1) ∨ (n = 2 ∧ OmegaPlus W K a U₁ U₂ 2) := by
  rcases hΩ with hp | hm
  · obtain ⟨n₀, hn₀, ⟨e⟩⟩ := omega_alt_iso _ h hR hts hAlt hp
    have h2 := alt_omega_plus_degree hn₀ hn e
    subst h2
    exact Or.inr ⟨rfl, hp⟩
  · obtain ⟨n₀, hn₀, ⟨e⟩⟩ := omega_alt_iso _ h hR hts hAlt hm
    have h1 := alt_omega_minus_degree hn₀ hn e
    subst h1
    exact Or.inl ⟨rfl, hm⟩

theorem omega_to_alt (h : Setup28 W K S) (hR : Red28 W K S) {a : X} {U₁ U₂ : Subgroup X}
    (hts : TransSection K (vOf W K S) U₁ U₂ a) (hAlt : InAlt ↥(bar W K))
    (hm : OmegaModel W K a U₁ U₂) : AltModel W K a U₁ U₂ := by
  obtain ⟨n, hn, hΩ⟩ := hm
  rcases omega_alt_degree h hR hts hAlt hn hΩ with ⟨-, hm1⟩ | ⟨-, hp2⟩
  · exact omega_to_alt_five hm1
  · exact omega_to_alt_eight hp2

theorem case_two (h : Setup28 W K S) (hR : Red28 W K S)
    (hd : ¬ Concl28d K S) {A : Subgroup X} (hA : Off28 W K S A) (h2 : Hyp28Two W K S) :
    Concl28b W K S := by
  have hZ := hyp28Two_center h h2
  have hS2 : Nat.card ↥(indAut W K S) = 2 := by
    obtain ⟨-, -, -, -, n, e, hact⟩ := h2
    exact hact.1
  have hle : Nat.card ↥(indAut W K A) ≤ 2 :=
    hS2 ▸ Subgroup.card_le_of_le (indAut_mono hA.isMax.1)
  have hc2 : Nat.card ↥(indAut W K A) = 2 := by
    rcases card_two_or_four h hA (by omega) with h | h <;> omega
  obtain ⟨a, haA, hna, ha2, htr⟩ := transv_of_card_two h hR hA hc2
  have haS : a ∈ S := hA.isMax.1 haA
  obtain ⟨U₁, U₂, hts, hmod⟩ := core h hR haS hna ha2 htr (c2_outer h h2 haS hna)
  have hAlt : AltModel W K a U₁ U₂ := by
    rcases hmod with hm | hAlt
    · exact omega_to_alt h hR hts h2.1 hm
    · exact hAlt
  have hE := heart h hR hd haS hna (S_cases h haS hna hS2)
    (centMax_of_alt_center h hR hts haS hna hS2 hAlt hZ)
    (threeElt_of_alt_center h hR hts haS hna hS2 hAlt hZ)
  have hblock := isGLBlock_of h hR hts.toSingleFactor hE hZ
  exact ⟨h2, alt_final h hR hts.toSingleFactor hE hS2 hblock haS hna hAlt⟩

end CaseOneTwo

section Final

theorem input28_10_of_leaves
    (hOut : Chev2OutTwoRank) (hInv : Chev2RankTwoInverts)
    (hL1 : OmegaTwoAutTwoPart) : Input28_10 := by
  intro X _ _ W _ K S hW hC hK hO hS hN hWS hyp
  have h : Setup28 W K S := ⟨hW, hC, hK, hO, hS, hN, hWS⟩
  by_cases hd : Concl28d K S
  · exact Or.inr (Or.inr (Or.inr hd))
  obtain ⟨hR, A, hA⟩ := step0 h hd
  rcases hyp with h1 | h2 | h3 | h4
  · exact Or.inl (case_one hOut hInv hL1 h hR hd hA h1)
  · exact Or.inr (Or.inl (case_two h hR hd hA h2))
  · exact Or.inr (Or.inr (Or.inl (case_three h hR hd hA h3)))
  · exact (case_four h hR hA h4).elim

end Final

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
