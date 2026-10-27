module

public import CFSG.HardMathSupport.Solomon.Coordinator.WeakBalance
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise commutatorElement

section Commutators

variable {G : Type} [Group G]

theorem le_normalizer_commutator_left (P X : Subgroup G) :
    P ≤ Subgroup.normalizer ((⁅P, X⁆ : Subgroup G) : Set G) := by
  have key : ∀ h ∈ P, ∀ y ∈ ⁅P, X⁆, h * y * h⁻¹ ∈ ⁅P, X⁆ := by
    intro h hh y hy
    have hle : ⁅P, X⁆ ≤ (⁅P, X⁆ : Subgroup G).comap (MulAut.conj h).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha x hx
      show h * ⁅a, x⁆ * h⁻¹ ∈ ⁅P, X⁆
      rw [show h * ⁅a, x⁆ * h⁻¹ = ⁅h * a, x⁆ * ⁅h, x⁆⁻¹ by
        simp only [commutatorElement_def]; group]
      exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (P.mul_mem hh ha) hx)
        (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hh hx))
    exact hle hy
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key h hh y, fun hy => ?_⟩
  have := key h⁻¹ (P.inv_mem hh) _ hy
  simpa [mul_assoc] using this

theorem le_normalizer_commutator_right' (P X : Subgroup G) :
    X ≤ Subgroup.normalizer ((⁅P, X⁆ : Subgroup G) : Set G) := by
  have key : ∀ x ∈ X, ∀ y ∈ ⁅P, X⁆, x * y * x⁻¹ ∈ ⁅P, X⁆ := by
    intro x hx y hy
    have hle : ⁅P, X⁆ ≤ (⁅P, X⁆ : Subgroup G).comap (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      show x * ⁅a, b⁆ * x⁻¹ ∈ ⁅P, X⁆
      rw [show x * ⁅a, b⁆ * x⁻¹ = ⁅a, x⁆⁻¹ * ⁅a, x * b⁆ by
        simp only [commutatorElement_def]; group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator ha hx))
        (Subgroup.commutator_mem_commutator ha (X.mul_mem hx hb))
    exact hle hy
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun hy => ?_⟩
  have := key x⁻¹ (X.inv_mem hx) _ hy
  simpa [mul_assoc] using this

theorem commutator_sup_le_sup_commutator {N C E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (N : Set G)) (hCN : C ≤ Subgroup.normalizer (N : Set G)) :
    ⁅N ⊔ C, E⁆ ≤ N ⊔ ⁅C, E⁆ := by
  have hmul : ((N ⊔ C : Subgroup G) : Set G) = (N : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left N C hCN
  refine Subgroup.commutator_le.2 fun x hx e he => ?_
  have hx' : x ∈ (N : Set G) * (C : Set G) := hmul ▸ hx
  obtain ⟨n, hn, c, hc, rfl⟩ := hx'
  have h1 : e * n⁻¹ * e⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 (hEN he) n⁻¹).1 (N.inv_mem hn)
  have e1 : ⁅n * c, e⁆ = n * ⁅c, e⁆ * (e * n⁻¹ * e⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e1]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hn)
    (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hc he))) (Subgroup.mem_sup_left h1)

variable [Finite G]

omit [Finite G] in
theorem coprime_commutator_commutator_eq' {P X : Subgroup G}
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    ⁅⁅P, X⁆, X⁆ = ⁅P, X⁆ := by
  classical
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have h2 : CFSG.commutatorAction₂ (A := ↥X) (G := ↥P) =
      CFSG.commutatorAction (A := ↥X) (G := ↥P) :=
    CFSG.commutatorAction₂_eq_commutatorAction_of_coprime (G := ↥P) (A := ↥X) hcop
  have hmap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hmap2 : (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype ≤ ⁅⁅P, X⁆, X⁆ := by
    let C : Subgroup ↥P := CFSG.commutatorAction (A := ↥X) (G := ↥P)
    let S : Set ↥P := {x : ↥P | ∃ a : ↥X, ∃ h : ↥P, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype =
          (Subgroup.closure S).map P.subtype := rfl
      _ = Subgroup.closure (P.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := P.subtype) S)
      _ ≤ ⁅⁅P, X⁆, X⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅P, X⁆, X⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : G) ∈ ⁅P, X⁆ := by
          rw [← hmap]
          exact Subgroup.mem_map_of_mem P.subtype hhC
        have hcomm : ⁅(h : G)⁻¹, (a : G)⁆ ∈ ⁅⁅P, X⁆, X⁆ :=
          Subgroup.commutator_mem_commutator ((⁅P, X⁆ : Subgroup G).inv_mem hhcomm) a.2
        simpa [commutatorElement_def, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hXP, mul_assoc] using hcomm
  refine le_antisymm ?_ fun x hx => ?_
  · exact (Subgroup.le_normalizer_iff_commutator_le_left).mp (le_normalizer_commutator_right' P X)
  · rw [← hmap, ← h2] at hx
    exact hmap2 hx

end Commutators

section AlphaOne

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_glaDelta_inf_centralizer_le {p k : ℕ} {A D₀ D' : Subgroup G}
    (hwb : IsWeaklyBalancedWrt p k A) (hD₀ : IsEkIn p k A D₀) (hD'A : D' ≤ A) :
    ⁅GLADelta p D₀ ⊓ Subgroup.centralizer (D' : Set G), A⁆ ≤ GLADelta p D' := by
  simp only [GLADelta]
  refine le_iInf fun x => le_iInf fun hx => le_iInf fun hx1 => ?_
  refine le_trans (Subgroup.commutator_mono (inf_le_inf_left _ (Subgroup.centralizer_le ?_)) le_rfl)
    (hwb D₀ hD₀ x (hD'A hx) hx1)
  simpa using hx

omit [Finite G] in
theorem le_normalizer_glaDelta_inf_centralizer {p : ℕ} {A D D' : Subgroup G}
    (hA : IsElemAbelian p A) (hDA : D ≤ A) (hD'A : D' ≤ A) :
    A ≤ Subgroup.normalizer
      ((GLADelta p D ⊓ Subgroup.centralizer (D' : Set G) : Subgroup G) : Set G) := by
  have h1 := le_normalizer_glaDelta hA hDA
  have h2 : A ≤ Subgroup.normalizer
      ((Subgroup.centralizer (D' : Set G) : Subgroup G) : Set G) :=
    (le_centralizer_of_le_of_isElemAbelian hA hD'A).trans Subgroup.le_normalizer
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr ((Subgroup.mem_normalizer_iff.1 (h1 ha)) x)
    ((Subgroup.mem_normalizer_iff.1 (h2 ha)) x)

theorem coprime_card_of_isPGroup {p : ℕ} (hp : p.Prime) {E Y : Subgroup G} (hE : IsPGroup p E)
    (hY : ¬ p ∣ Nat.card Y) : Nat.Coprime (Nat.card E) (Nat.card Y) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hE.exists_card_eq
  rw [ha]
  exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hY)

omit [Finite G] in
theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem commutator_glaDelta_le_alphaE {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) {A D₀ E : Subgroup G}
    (hA : IsElemAbelian p A) (hwb : IsWeaklyBalancedWrt p k A)
    (hgen : ⁅GLADelta p D₀, E⁆ ≤
      ⨆ (D : Subgroup G) (_ : IsEkIn p k E D), ⁅GLADelta p D₀ ⊓ Subgroup.centralizer (D : Set G), E⁆)
    (hD₀ : IsEkIn p k A D₀) (hE : IsEkIn p (k + 1) A E) :
    ⁅GLADelta p D₀, E⁆ ≤ alphaE p k E := by
  refine hgen.trans (iSup₂_le fun D hD => ?_)
  have hDA : D ≤ A := hD.1.trans hE.1
  set X := GLADelta p D₀ ⊓ Subgroup.centralizer (D : Set G)
  have hEX : E ≤ Subgroup.normalizer (X : Set G) :=
    hE.1.trans (le_normalizer_glaDelta_inf_centralizer hA hD₀.1 hDA)
  have hXp : ¬ p ∣ Nat.card X := fun h =>
    not_dvd_card_glaDelta hp (hD₀.ne_bot hp hk) (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hcop := coprime_card_of_isPGroup hp (isPGroup_of_isElemAbelian (isElemAbelian_mono hA hE.1))
    hXp
  have hXE : ⁅X, E⁆ ≤ GLADelta p D :=
    (Subgroup.commutator_mono le_rfl hE.1).trans (commutator_glaDelta_inf_centralizer_le hwb hD₀ hDA)
  rw [← coprime_commutator_commutator_eq' hEX hcop]
  exact (Subgroup.commutator_mono hXE le_rfl).trans
    (le_sup_of_le_left (le_iSup₂_of_le D hD le_rfl))

theorem alphaE_le_alphaE {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) {A E F : Subgroup G}
    (hA : IsElemAbelian p A) (hbal : IsBalancedWrt p (k + 1) A) (hwb : IsWeaklyBalancedWrt p k A)
    (hgen : ∀ D₀ : Subgroup G, IsEkIn p k A D₀ → ∀ E' : Subgroup G, IsEkIn p (k + 1) A E' →
      ⁅GLADelta p D₀, E'⁆ ≤ ⨆ (D : Subgroup G) (_ : IsEkIn p k E' D),
        ⁅GLADelta p D₀ ⊓ Subgroup.centralizer (D : Set G), E'⁆)
    (hE : IsEkIn p (k + 1) A E) (hF : IsEkIn p (k + 1) A F) :
    alphaE p k E ≤ alphaE p k F := by
  have hFel : IsElemAbelian p F := isElemAbelian_mono hA hF.1
  have hFp : IsPGroup p F := isPGroup_of_isElemAbelian hFel
  have hEF : F ≤ Subgroup.normalizer (E : Set G) :=
    (hF.1.trans (le_centralizer_of_le_of_isElemAbelian hA hE.1)).trans
      (Subgroup.centralizer_le_normalizer _)
  refine sup_le (iSup₂_le fun D hD => ?_) ?_
  ·
    have hDA : D ≤ A := hD.1.trans hE.1
    have hD' : IsEkIn p k A D := ⟨hDA, hD.2⟩
    set Y := ⁅GLADelta p D, E⁆ with hY
    have hFΔ : F ≤ Subgroup.normalizer (GLADelta p D : Set G) :=
      hF.1.trans (le_normalizer_glaDelta hA hDA)
    have hFY : F ≤ Subgroup.normalizer (Y : Set G) :=
      CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer F _ _ hFΔ hEF
    have hYΔ : Y ≤ GLADelta p D :=
      (Subgroup.le_normalizer_iff_commutator_le_left).mp (hE.1.trans (le_normalizer_glaDelta hA hDA))
    have hYp : ¬ p ∣ Nat.card Y := fun h =>
      not_dvd_card_glaDelta hp (hD'.ne_bot hp hk) (h.trans (Subgroup.card_dvd_of_le hYΔ))
    have hEΔ : E ≤ Subgroup.normalizer (GLADelta p D : Set G) :=
      hE.1.trans (le_normalizer_glaDelta hA hDA)
    have hcopE := coprime_card_of_isPGroup hp
      (isPGroup_of_isElemAbelian (isElemAbelian_mono hA hE.1))
      (not_dvd_card_glaDelta hp (hD'.ne_bot hp hk))
    have hYY : ⁅Y, E⁆ = Y := coprime_commutator_commutator_eq' hEΔ hcopE
    have hdec := le_commutator_sup_inf_centralizer_of_isPGroup hp hFp hFY hYp
    have hEN : E ≤ Subgroup.normalizer ((⁅Y, F⁆ : Subgroup G) : Set G) := by
      have hEF' : E ≤ Subgroup.normalizer (F : Set G) :=
        (hE.1.trans (le_centralizer_of_le_of_isElemAbelian hA hF.1)).trans
          (Subgroup.centralizer_le_normalizer _)
      exact CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer E _ _
        (le_normalizer_commutator_right' (GLADelta p D) E) hEF'
    have hCN : Y ⊓ Subgroup.centralizer (F : Set G) ≤
        Subgroup.normalizer ((⁅Y, F⁆ : Subgroup G) : Set G) :=
      inf_le_left.trans (le_normalizer_commutator_left Y F)
    calc Y = ⁅Y, E⁆ := hYY.symm
      _ ≤ ⁅⁅Y, F⁆ ⊔ (Y ⊓ Subgroup.centralizer (F : Set G)), E⁆ :=
          Subgroup.commutator_mono hdec le_rfl
      _ ≤ ⁅Y, F⁆ ⊔ ⁅Y ⊓ Subgroup.centralizer (F : Set G), E⁆ :=
          commutator_sup_le_sup_commutator hEN hCN
      _ ≤ alphaE p k F := by
        refine sup_le ?_ ?_
        · exact (Subgroup.commutator_mono hYΔ le_rfl).trans
            (commutator_glaDelta_le_alphaE hp hk hA hwb (hgen D hD' F hF) hD' hF)
        · refine le_trans ?_ (le_sup_right : GLADelta p F ≤ alphaE p k F)
          exact (Subgroup.commutator_mono (inf_le_inf_right _ hYΔ) hE.1).trans
            (commutator_glaDelta_inf_centralizer_le hwb hD' hF.1)
  ·
    obtain ⟨D₀, hD₀E, hD₀el, hD₀card⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Proving.exists_elemAbelian_subgroup_card_pow hp hE.2.1
        (Nat.le_succ k) hE.2.2
    have hD₀ : IsEkIn p k A D₀ := ⟨hD₀E.trans hE.1, hD₀el, hD₀card⟩
    have hEne : E ≠ ⊥ := hE.ne_bot hp (by omega)
    have hFE : F ≤ Subgroup.normalizer (GLADelta p E : Set G) :=
      hF.1.trans (le_normalizer_glaDelta hA hE.1)
    have hdec := le_commutator_sup_inf_centralizer_of_isPGroup hp hFp hFE
      (not_dvd_card_glaDelta hp hEne)
    refine hdec.trans (sup_le ?_ ?_)
    · exact (Subgroup.commutator_mono (glaDelta_anti hD₀E) le_rfl).trans
        (commutator_glaDelta_le_alphaE hp hk hA hwb (hgen D₀ hD₀ F hF) hD₀ hF)
    · exact (glaDelta_inf_centralizer_le hbal hE hF).trans le_sup_right

theorem alphaE_eq_alphaE {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) {A E F : Subgroup G}
    (hA : IsElemAbelian p A) (hbal : IsBalancedWrt p (k + 1) A) (hwb : IsWeaklyBalancedWrt p k A)
    (hgen : ∀ D₀ : Subgroup G, IsEkIn p k A D₀ → ∀ E' : Subgroup G, IsEkIn p (k + 1) A E' →
      ⁅GLADelta p D₀, E'⁆ ≤ ⨆ (D : Subgroup G) (_ : IsEkIn p k E' D),
        ⁅GLADelta p D₀ ⊓ Subgroup.centralizer (D : Set G), E'⁆)
    (hE : IsEkIn p (k + 1) A E) (hF : IsEkIn p (k + 1) A F) :
    alphaE p k E = alphaE p k F :=
  le_antisymm (alphaE_le_alphaE hp hk hA hbal hwb hgen hE hF)
    (alphaE_le_alphaE hp hk hA hbal hwb hgen hF hE)

end AlphaOne

section AlphaThree

variable {G : Type} [Group G]

theorem alphaE_gLBConj (p k : ℕ) (g : G) (E : Subgroup G) :
    alphaE p k (GLBConj g E) = GLBConj g (alphaE p k E) := by
  apply le_antisymm
  · refine sup_le (iSup₂_le fun F hF => ?_) ?_
    · have hF' : IsEkIn p k E (GLBConj g⁻¹ F) := by
        rw [← isEkIn_gLBConj_iff g, gLBConj_gLBConj_inv]
        exact hF
      calc ⁅GLADelta p F, GLBConj g E⁆
          = ⁅GLADelta p (GLBConj g (GLBConj g⁻¹ F)), GLBConj g E⁆ := by rw [gLBConj_gLBConj_inv]
        _ = GLBConj g ⁅GLADelta p (GLBConj g⁻¹ F), E⁆ := by
            rw [glaDelta_gLBConj]
            simp only [GLBConj, Subgroup.map_commutator]
        _ ≤ GLBConj g (alphaE p k E) :=
            gLBConj_mono g (le_sup_of_le_left (le_iSup₂_of_le _ hF' le_rfl))
    · rw [glaDelta_gLBConj]
      exact gLBConj_mono g le_sup_right
  · refine Subgroup.map_le_iff_le_comap.2 (sup_le (iSup₂_le fun D hD => ?_) ?_)
    · refine Subgroup.map_le_iff_le_comap.1 ?_
      change GLBConj g ⁅GLADelta p D, E⁆ ≤ _
      have e : GLBConj g ⁅GLADelta p D, E⁆ = ⁅GLADelta p (GLBConj g D), GLBConj g E⁆ := by
        rw [glaDelta_gLBConj]
        simp only [GLBConj, Subgroup.map_commutator]
      rw [e]
      exact le_sup_of_le_left (le_iSup₂_of_le (GLBConj g D) ((isEkIn_gLBConj_iff g).2 hD) le_rfl)
    · refine Subgroup.map_le_iff_le_comap.1 ?_
      change GLBConj g (GLADelta p E) ≤ _
      rw [← glaDelta_gLBConj]
      exact le_sup_right

variable [Finite G]

theorem glbCore_le_normalizer_alphaE {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) {A E : Subgroup G}
    (hA : IsElemAbelian p A) (hbal : IsBalancedWrt p (k + 1) A) (hwb : IsWeaklyBalancedWrt p k A)
    (hgen : ∀ D₀ : Subgroup G, IsEkIn p k A D₀ → ∀ E' : Subgroup G, IsEkIn p (k + 1) A E' →
      ⁅GLADelta p D₀, E'⁆ ≤ ⨆ (D : Subgroup G) (_ : IsEkIn p k E' D),
        ⁅GLADelta p D₀ ⊓ Subgroup.centralizer (D : Set G), E'⁆)
    (hE : IsEkIn p (k + 1) A E) :
    GLBCore p (k + 1) A ≤ Subgroup.normalizer (alphaE p k E : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  refine sSup_le ?_
  rintro N ⟨Q, hQA, hQrank, rfl⟩
  have hQel : IsElemAbelian p Q := isElemAbelian_mono hA hQA
  obtain ⟨E₁, hE₁Q, hE₁el, hE₁card⟩ := CFSG.SectionRank.exists_pRank (p := p) hp.one_lt Q
  obtain ⟨E', hE'E₁, hE'el, hE'card⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.exists_elemAbelian_subgroup_card_pow hp hE₁el
      hQrank hE₁card
  have hE' : IsEkIn p (k + 1) A E' := ⟨(hE'E₁.trans hE₁Q).trans hQA, hE'el, hE'card⟩
  intro g hg
  have hgQ : GLBConj g Q = Q := mem_normalizer_iff_gLBConj_eq.1 hg
  have hE'g : IsEkIn p (k + 1) A (GLBConj g E') := by
    refine ⟨?_, ?_, ?_⟩
    · have := gLBConj_mono g (hE'E₁.trans hE₁Q)
      rw [hgQ] at this
      exact this.trans hQA
    · exact (isEkIn_gLBConj_iff (k := k + 1) (E := E') g).2 ⟨le_rfl, hE'el, hE'card⟩ |>.2.1
    · exact ((isEkIn_gLBConj_iff (k := k + 1) (E := E') g).2 ⟨le_rfl, hE'el, hE'card⟩).2.2
  rw [mem_normalizer_iff_gLBConj_eq, alphaE_eq_alphaE hp hk hA hbal hwb hgen hE hE',
    ← alphaE_gLBConj, alphaE_eq_alphaE hp hk hA hbal hwb hgen hE'g hE']

end AlphaThree

end CFSG.HardMathSupport.Solomon.Coordinator
