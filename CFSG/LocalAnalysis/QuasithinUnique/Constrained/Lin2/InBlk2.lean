module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_20b
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups commutatorElement

section SL2

variable {F : Type} [Field F]

theorem sl2_eq_one_of_fix {g : SL(2, F)}
    (h : ∀ w : Fin 2 → F, (g : Matrix (Fin 2) (Fin 2) F).mulVec w = w) : g = 1 := by
  apply Subtype.ext
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this

theorem eq_zero_of_fixed_by_sl2 {w : Fin 2 → F}
    (h : ∀ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F).mulVec w = w) : w = 0 := by
  by_contra hw
  obtain ⟨w', hw'0, hw'⟩ : ∃ w' : Fin 2 → F, w' ≠ 0 ∧ w' ≠ w := by
    by_cases h1 : w = ![1, 0]
    · refine ⟨![0, 1], fun e => ?_, fun e => ?_⟩
      · have := congrFun e 1
        simp at this
      · have := congrFun (e.trans h1) 0
        simp at this
    · refine ⟨![1, 0], fun e => ?_, fun e => h1 e.symm⟩
      have := congrFun e 0
      simp at this
  obtain ⟨g, hg⟩ := exists_sl2_mulVec_eq hw hw'0
  exact hw' (hg.symm.trans (h g))

theorem isSimpleGroup_sl2_of_charTwo [Fintype F] (hF2 : (2 : F) = 0) (h4 : 4 ≤ Fintype.card F) :
    IsSimpleGroup SL(2, F) := by
  have : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast hF2)
  have h4' : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (show 4 ≤ (Finset.univ : Finset F).card by rwa [Finset.card_univ])
    exact ⟨s, hs⟩
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl (Or.inr h4')
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm.isSimpleGroup

theorem not_isPGroup_sl2 (hF2 : (2 : F) = 0) : ¬ IsPGroup 2 SL(2, F) := by
  intro h
  let M : SL(2, F) := ⟨!![0, 1; 1, 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : F) * hF2⟩
  have hMc : (M : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 1] := rfl
  have hM3 : M * M * M = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hMc,
      Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination hF2
  have hM1 : M ≠ 1 := by
    intro e
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) e
    simp [M] at this
  obtain ⟨k, hk⟩ := h M
  have h1 : orderOf M ∣ 3 := orderOf_dvd_of_pow_eq_one (by simpa [pow_succ] using hM3)
  have h2 : orderOf M ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h3 : orderOf M = 1 := by
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  exact hM1 (orderOf_eq_one_iff.1 h3)

theorem exists_noncomm_sl2 : ∃ x y : SL(2, F), x * y ≠ y * x := by
  let x : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let y : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hx : (x : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl
  have hy : (y : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := rfl
  refine ⟨x, y, fun h => ?_⟩
  have h00 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, hx, hy] at h00
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem eq_bot_of_normal_isPGroup_sl2 [Fintype F] (hF2 : (2 : F) = 0) (h4 : 4 ≤ Fintype.card F)
    (N : Subgroup SL(2, F)) [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  have := isSimpleGroup_sl2_of_charTwo hF2 h4
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    apply not_isPGroup_sl2 hF2
    have : IsPGroup 2 (⊤ : Subgroup SL(2, F)) := h ▸ hN
    exact this.of_surjective (Subgroup.topEquiv (G := SL(2, F))).toMonoidHom
      (Subgroup.topEquiv (G := SL(2, F))).surjective

end SL2

section Data

variable {G : Type} [Group G] [Finite G] {C V Zf : Subgroup G} {F : Type} [Field F] [Fintype F]

omit [Finite G] in
theorem mem_pCoreOf_iff_mem_pCore {X : Subgroup G} (x : X) :
    (x : G) ∈ pCoreOf 2 X ↔ x ∈ CFSG.pCore 2 ↥X := CFSG.mem_openPCoreOf_iff x

omit [Finite G] in
theorem lin2_of_data {m : ℕ} (hm : 2 ≤ m) (hcard : Fintype.card F = 2 ^ m) (hF2 : (2 : F) = 0)
    (hVC : V ≤ C) (hVel : IsElemAbelian 2 V) (hVn : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (α : ↥C →* SL(2, F)) (hα : Function.Surjective α) (hαk : ∀ c : ↥C, α c = 1 ↔ (c : G) ∈ V)
    (β : ↥V →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hZV : Zf ≤ V) (hZc : ∀ c ∈ C, ∀ z ∈ Zf, c * z = z * c)
    (hβk : ∀ v : ↥V, β v = 1 ↔ (v : G) ∈ Zf)
    (hβe : ∀ c : ↥C, ∀ u v : ↥V, (v : G) = c * u * c⁻¹ →
      Multiplicative.toAdd (β v) =
        (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hns : V ≤ ⁅V, C⁆) :
    pCoreOf 2 C = V ∧ blockU C = V ∧ blockZ C = Zf ∧ IsShort2 C ∧ IsLin2Type C m := by
  have h4 : 4 ≤ Fintype.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hVel.2 x x.2)⟩
  have hCN : C ≤ Subgroup.normalizer (V : Set G) := le_normalizer_of_conj_mem hVn
  have hVP : V ≤ pCoreOf 2 C := le_pCoreOf_of_normalizes hVC hCN hV2
  have hPV : pCoreOf 2 C ≤ V := by
    have hPC : pCoreOf 2 C ≤ C := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 C
    have hCP : C ≤ Subgroup.normalizer (pCoreOf 2 C : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 C
    have hPn : ((pCoreOf 2 C).subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPC).2 hCP
    have hP2 : IsPGroup 2 ((pCoreOf 2 C).subgroupOf C) :=
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 C).of_equiv
        (Subgroup.subgroupOfEquivOfLe hPC).symm
    have : (((pCoreOf 2 C).subgroupOf C).map α).Normal := Subgroup.Normal.map hPn α hα
    have hbot := eq_bot_of_normal_isPGroup_sl2 hF2 h4 _ (hP2.map α)
    intro x hx
    have hxC : x ∈ C := hPC hx
    have : α ⟨x, hxC⟩ ∈ ((pCoreOf 2 C).subgroupOf C).map α := ⟨⟨x, hxC⟩, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact (hαk ⟨x, hxC⟩).1 this
  have hP : pCoreOf 2 C = V := le_antisymm hPV hVP
  have hQ : blockQ C = V := hP
  have hU : blockU C = V := by
    show ⁅blockQ C, C⁆ = V
    rw [hQ]
    refine le_antisymm ?_ hns
    rw [Subgroup.commutator_le]
    intro v hv c hc
    have e : ⁅v, c⁆ = v * (c * v⁻¹ * c⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact V.mul_mem hv (hVn c hc v⁻¹ (V.inv_mem hv))
  have hZ : blockZ C = Zf := by
    show blockU C ⊓ Subgroup.centralizer (C : Set G) = Zf
    rw [hU]
    apply le_antisymm
    · rintro v ⟨hvV, hvC⟩
      have hfix : ∀ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F).mulVec
          (Multiplicative.toAdd (β ⟨v, hvV⟩)) = Multiplicative.toAdd (β ⟨v, hvV⟩) := by
        intro g
        obtain ⟨c, rfl⟩ := hα g
        have hcomm : (c : G) * v = v * c := Subgroup.mem_centralizer_iff.1 hvC c c.2
        exact (hβe c ⟨v, hvV⟩ ⟨v, hvV⟩ (by
          show v = (c : G) * v * (c : G)⁻¹
          rw [hcomm]
          group)).symm
      have h0 := eq_zero_of_fixed_by_sl2 hfix
      have h1 : β ⟨v, hvV⟩ = 1 := Multiplicative.toAdd.injective (by rw [h0]; rfl)
      exact (hβk ⟨v, hvV⟩).1 h1
    · intro z hz
      exact ⟨hZV hz, Subgroup.mem_centralizer_iff.2 fun c hc => hZc c hc z hz⟩
  have hker : α.ker = CFSG.pCore 2 ↥C := by
    ext c
    rw [MonoidHom.mem_ker, hαk, ← hP, mem_pCoreOf_iff_mem_pCore]
  have hLin : IsLin2Type C m := by
    refine ⟨F, inferInstance, inferInstance, hcard, α, hα, hker,
      β.comp (Subgroup.inclusion hU.le), ?_, ?_, ?_⟩
    · intro y
      obtain ⟨v, hv⟩ := hβ y
      exact ⟨⟨v, by rw [hU]; exact v.2⟩, hv⟩
    · ext u
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hβk, Subgroup.mem_subgroupOf, hZ]
      rfl
    · intro ℓ u v hv
      exact hβe ℓ (Subgroup.inclusion hU.le u) (Subgroup.inclusion hU.le v) hv
  refine ⟨hP, hU, hZ, ?_, hLin⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro N hN hq
    have := hN
    have := isSimpleGroup_sl2_of_charTwo hF2 h4
    have hNα : N.map α = ⊤ := by
      have : (N.map α).Normal := Subgroup.Normal.map hN α hα
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map α) with h | h
      · exfalso
        have hle : N ≤ α.ker := fun n hn => by
          have : α n ∈ N.map α := ⟨n, hn, rfl⟩
          rw [h, Subgroup.mem_bot] at this
          exact this
        apply not_isPGroup_sl2 hF2
        exact hq.of_surjective (QuotientGroup.lift N α hle) (by
          intro g
          obtain ⟨c, rfl⟩ := hα g
          exact ⟨QuotientGroup.mk c, rfl⟩)
      · exact h
    have hdec : ∀ x : ↥C, ∃ n ∈ N, ∃ d : ↥C, (d : G) ∈ V ∧ x = n * d := by
      intro x
      have : α x ∈ N.map α := by rw [hNα]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := this
      exact ⟨n, hn, n⁻¹ * x, (hαk _).1 (by rw [map_mul, map_inv, hnx, inv_mul_cancel]), by group⟩
    have hQ : ∀ x y : ↥C, (QuotientGroup.mk x : ↥C ⧸ N) * QuotientGroup.mk y =
        QuotientGroup.mk y * QuotientGroup.mk x := by
      intro x y
      obtain ⟨n₁, hn₁, d₁, hd₁, rfl⟩ := hdec x
      obtain ⟨n₂, hn₂, d₂, hd₂, rfl⟩ := hdec y
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n₁).2 hn₁,
        (QuotientGroup.eq_one_iff n₂).2 hn₂, one_mul, one_mul, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact IsElemAbelian.comm hVel hd₁ hd₂
    have hCC : ∀ x y : ↥C, ⁅x, y⁆ ∈ N := by
      intro x y
      have h1 : (QuotientGroup.mk' N) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_commute.2 (hQ x y)
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hVN : V ≤ N.map C.subtype := by
      refine hns.trans ?_
      rw [Subgroup.commutator_le]
      intro v hv c hc
      refine ⟨⁅(⟨v, hVC hv⟩ : ↥C), ⟨c, hc⟩⁆, hCC _ _, ?_⟩
      simp [commutatorElement_def]
    rw [eq_top_iff]
    intro x _
    obtain ⟨n, hn, d, hd, rfl⟩ := hdec x
    have hdN : d ∈ N := by
      obtain ⟨y, hy, hyd⟩ := hVN hd
      have : y = d := Subtype.ext hyd
      rwa [this] at hy
    exact N.mul_mem hn hdN
  ·
    show C ⊓ Subgroup.centralizer (pCoreOf 2 C : Set G) ≤ pCoreOf 2 C
    rw [hP]
    rintro c ⟨hcC, hcV⟩
    have hfix : ∀ w : Fin 2 → F, (α ⟨c, hcC⟩ : Matrix (Fin 2) (Fin 2) F).mulVec w = w := by
      intro w
      obtain ⟨v, hv⟩ := hβ (Multiplicative.ofAdd w)
      have hw : Multiplicative.toAdd (β v) = w := by rw [hv]; rfl
      have hcomm : (v : G) * c = c * v := Subgroup.mem_centralizer_iff.1 hcV v v.2
      have := hβe ⟨c, hcC⟩ v v (by
        show (v : G) = c * v * c⁻¹
        rw [← hcomm]
        group)
      rw [hw] at this
      exact this.symm
    exact (hαk ⟨c, hcC⟩).1 (sl2_eq_one_of_fix hfix)
  · rw [hU, hQ]
    exact ⟨fun x hx => ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy =>
      IsElemAbelian.comm hVel hy hx⟩, hVel.2⟩
  · left
    have e : (↥C ⧸ CFSG.pCore 2 ↥C) ≃* SL(2, F) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    have : IsSimpleGroup SL(2, F) := isSimpleGroup_sl2_of_charTwo hF2 h4
    have : IsSimpleGroup (↥C ⧸ CFSG.pCore 2 ↥C) := e.isSimpleGroup
    have hnc : ∃ a b : (↥C ⧸ CFSG.pCore 2 ↥C), a * b ≠ b * a := by
      obtain ⟨x, y, hxy⟩ := exists_noncomm_sl2 (F := F)
      exact ⟨e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h)⟩
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  · rw [hZ, hU]
    refine ⟨?_, ?_⟩
    · refine lt_of_le_of_ne hZV (fun e => ?_)
      obtain ⟨v, hv⟩ := hβ (Multiplicative.ofAdd ![1, 0])
      have hvZ : (v : G) ∈ Zf := by rw [e]; exact v.2
      have h1 := (hβk v).2 hvZ
      rw [hv] at h1
      have h2 := congrFun (congrArg Multiplicative.toAdd h1) 0
      simp at h2
    · intro W hZW hWV hCW
      by_cases hW : W ≤ Zf
      · exact Or.inl (le_antisymm hW hZW)
      · right
        apply le_antisymm hWV
        obtain ⟨x, hxW, hxZ⟩ : ∃ x ∈ W, x ∉ Zf := by
          by_contra hcon
          apply hW
          intro x hx
          by_contra hxZ
          exact hcon ⟨x, hx, hxZ⟩
        have hxV : x ∈ V := hWV hxW
        intro v hv
        by_cases hvZ : v ∈ Zf
        · exact hZW hvZ
        · have hbx : Multiplicative.toAdd (β ⟨x, hxV⟩) ≠ 0 := by
            intro h0
            exact hxZ ((hβk ⟨x, hxV⟩).1 (Multiplicative.toAdd.injective (by rw [h0]; rfl)))
          have hbv : Multiplicative.toAdd (β ⟨v, hv⟩) ≠ 0 := by
            intro h0
            exact hvZ ((hβk ⟨v, hv⟩).1 (Multiplicative.toAdd.injective (by rw [h0]; rfl)))
          obtain ⟨g, hg⟩ := exists_sl2_mulVec_eq hbx hbv
          obtain ⟨c, rfl⟩ := hα g
          have hcx : (c : G) * x * (c : G)⁻¹ ∈ W :=
            (Subgroup.mem_normalizer_iff.1 (hCW c.2) x).1 hxW
          have hcxV : (c : G) * x * (c : G)⁻¹ ∈ V := hWV hcx
          have h1 := hβe c ⟨x, hxV⟩ ⟨_, hcxV⟩ rfl
          have h2 : β ⟨_, hcxV⟩ = β ⟨v, hv⟩ := Multiplicative.toAdd.injective (h1.trans hg)
          have h3 : β ((⟨(c : G) * x * (c : G)⁻¹, hcxV⟩ : ↥V)⁻¹ * ⟨v, hv⟩) = 1 := by
            rw [map_mul, map_inv, h2, inv_mul_cancel]
          have h4 := (hβk _).1 h3
          have h5 : ((c : G) * x * (c : G)⁻¹)⁻¹ * v ∈ W := hZW h4
          have := W.mul_mem hcx h5
          rwa [mul_inv_cancel_left] at this

end Data

end CFSG.QuasithinUnique.Lin2
