module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43Defs
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.GL83PartI.I_6_10
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

variable {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x t₁ t₂ : Y} {J₁ J₂ F : Subgroup Y}

structure A10YCaseC (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x t₁ t₂ : Y)
    (J₁ J₂ F A₁ A₂ : Subgroup Y) : Prop where
  data : A10YData Y P x t₁ t₂ J₁ J₂ F
  comp₁ : IsComponentOf A₁ ⊤
  comp₂ : IsComponentOf A₂ ⊤
  le₁ : J₁ ≤ A₁
  le₂ : J₂ ≤ A₂
  not₁ : ¬ IsComponentOf J₁ ⊤
  not₂ : ¬ IsComponentOf J₂ ⊤

theorem a10y_glaCore (h : A10YData Y P x t₁ t₂ J₁ J₂ F) : GLAPPrimeCore 5 Y = ⊥ := by
  exact h.core

theorem a10y_isKGroup (h : A10YData Y P x t₁ t₂ J₁ J₂ F) : CFSG.Open.IsKGroup ↥(⊤ : Subgroup Y) := by
  exact (catalogSimpleSections_iff_isKGroup.mp h.catalog).subgroup ⊤

theorem a10y_sylow_pow (h : A10YData Y P x t₁ t₂ J₁ J₂ F) {q : Y} (hq : q ∈ P) :
    ∃ k : ℕ, q ^ (5 ^ k) = 1 := by
  obtain ⟨S, hS⟩ := h.sylow
  rw [← hS] at hq
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨q, hq⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem a10y_mem_normalizer_of_pow_coprime {H : Subgroup Y} {y : Y} {n : ℕ}
    (hy : y ^ n = 1) {m : ℕ} (hm : Nat.Coprime m n) (hym : y ^ m ∈ normalizer (H : Set Y)) :
    y ∈ normalizer (H : Set Y) := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm hn
    have h1 : y = (y ^ m) ^ k := by
      rw [← pow_mul, pow_eq_pow_mod (m * k) hy, hk, pow_one]
    rw [h1]
    exact pow_mem hym k
  · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · have hm1 : m = 1 := by simpa using hm
      subst hm1
      simpa using hym
    · have hy1 : y = 1 := by simpa using hy
      subst hy1
      exact one_mem _

theorem a10y_mem_normalizer_of_pElement (h : A10YData Y P x t₁ t₂ J₁ J₂ F) {q : Y}
    (hq : ∃ k : ℕ, q ^ (5 ^ k) = 1) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    q ∈ Subgroup.normalizer (L : Set Y) := by
  classical
  obtain ⟨k, hk⟩ := hq
  by_contra hyL
  set f : ℕ → Subgroup Y := fun i => L.map (MulAut.conj (q ^ i)).toMonoidHom with hf
  have hfK : ∀ i, IsComponentOf (f i) ⊤ := fun i =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (q ^ i)) L).mpr hL
  have hinj : Set.InjOn f (Finset.range 4 : Set ℕ) := by
    have key : ∀ i j : ℕ, i < j → j < 4 → f i ≠ f j := by
      intro i j hij hj hfij
      apply hyL
      refine a10y_mem_normalizer_of_pow_coprime hk (m := j - i) ?_ ?_
      · have hcop : Nat.Coprime (j - i) 5 :=
          (Nat.coprime_of_lt_prime (by omega) (by omega) Nat.prime_five).symm
        exact Nat.Coprime.pow_right k hcop
      · rw [mem_normalizer_iff_map_conj_eq]
        have h1 : f j = (f (j - i)).map (MulAut.conj (q ^ i)).toMonoidHom := by
          simp only [hf]
          rw [← CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, ← pow_add,
            Nat.add_sub_cancel' hij.le]
        rw [h1] at hfij
        exact (map_injective (MulAut.conj (q ^ i)).injective hfij).symm
    intro i hi j hj hfij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with hlt | heq | hlt
    · exact absurd hfij (key i j hlt hj)
    · exact heq
    · exact absurd hfij.symm (key j i hlt hi)
  have hcard := CFSG.LocalAnalysis.RankThreeTheoremC.card_le_pRank_of_isComponentOf Nat.prime_five
    (by omega) h.core ((Finset.range 4).image f) (fun K' hK' => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hK'
      exact hfK i)
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
  have hrank := h.rank
  omega

theorem a10y_V_elem_sup (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {E : Subgroup Y} (hEP : E ≤ P)
    (hE : IsElemAbelian 5 E) {f : Y} (hfP : f ∈ P) (hf5 : f ^ 5 = 1) (hfE : f ∉ E) :
    IsElemAbelian 5 (E ⊔ zpowers f) ∧ E ⊔ zpowers f ≤ P ∧
      Nat.card ↥(E ⊔ zpowers f) = Nat.card ↥E * 5 := by
  have hfz : zpowers f ≤ P := zpowers_le.mpr hfP
  refine ⟨hE.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hf5)
    fun a ha b hb => hPc a (hEP ha) b (hfz hb), sup_le hEP hfz, ?_⟩
  exact CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_five E hf5 hfE
    fun e he => hPc e (hEP he) f hfP

theorem a10y_V (h : A10YData Y P x t₁ t₂ J₁ J₂ F) :
    IsElemAbelian 5 (zpowers t₁ ⊔ zpowers t₂ ⊔ zpowers x) ∧
    Nat.card ↥(zpowers t₁ ⊔ zpowers t₂ ⊔ zpowers x) = 5 ^ 3 ∧
    (zpowers t₁ ⊔ zpowers t₂ ⊔ zpowers x ≤ P) ∧
    ∀ u ∈ P, u ^ 5 = 1 → u ∈ zpowers t₁ ⊔ zpowers t₂ ⊔ zpowers x := by
  have hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.P_comm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have ht₁5 : t₁ ^ 5 = 1 := by
    have := pow_orderOf_eq_one t₁
    rwa [h.t₁_ord] at this
  have ht₂5 : t₂ ^ 5 = 1 := by
    have := pow_orderOf_eq_one t₂
    rwa [h.t₂_ord] at this
  have hx5 : x ^ 5 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.x_ord] at this
  have hE₁ : IsElemAbelian 5 (zpowers t₁) := CFSG.Open.isElemAbelian_zpowers ht₁5
  have hc₁ : Nat.card ↥(zpowers t₁) = 5 := by rw [Nat.card_zpowers, h.t₁_ord]
  have hc₂ : Nat.card ↥(zpowers t₂) = 5 := by rw [Nat.card_zpowers, h.t₂_ord]
  have ht₂E₁ : t₂ ∉ zpowers t₁ := by
    intro hmem
    have heq : zpowers t₂ = zpowers t₁ :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hmem) (hc₁.trans hc₂.symm).le
    exact h.t₁_not_mem (by rw [heq]; exact mem_zpowers t₁)
  obtain ⟨hE₂, hP₂, hc₂'⟩ :=
    a10y_V_elem_sup hPc (zpowers_le.mpr h.t₁_mem.1) hE₁ h.t₂_mem.1 ht₂5 ht₂E₁
  obtain ⟨hE₃, hP₃, hc₃⟩ := a10y_V_elem_sup hPc hP₂ hE₂ h.x_mem hx5 h.x_not_mem
  have hcard₃ : Nat.card ↥(zpowers t₁ ⊔ zpowers t₂ ⊔ zpowers x) = 5 ^ 3 := by
    rw [hc₃, hc₂', hc₁]
    norm_num
  refine ⟨hE₃, hcard₃, hP₃, ?_⟩
  intro u huP hu5
  by_contra huV
  obtain ⟨hE₄, -, hc₄⟩ := a10y_V_elem_sup hPc hP₃ hE₃ huP hu5 huV
  have h4 : 4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Y) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hE₄ (k := 4) (by rw [hc₄, hcard₃]; norm_num)
  exact absurd (h4.trans h.rank) (by norm_num)

theorem a10y_sylow_comm (h : A10YData Y P x t₁ t₂ J₁ J₂ F) (H : Subgroup Y) (S : Sylow 5 ↥H) :
    IsMulCommutative (S : Subgroup ↥H) := by
  obtain ⟨S₀, hS₀⟩ := h.sylow
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := (S.isPGroup'.map H.subtype).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S₀ Q
  have hmem : ∀ y ∈ (Q : Subgroup Y), ∃ s ∈ P, g * s * g⁻¹ = y := by
    intro y hy
    rw [← hg] at hy
    obtain ⟨s, hs, hsy⟩ := hy
    exact ⟨s, hS₀ ▸ hs, hsy⟩
  refine IsMulCommutative.of_comm ?_
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨s, hs, hsa⟩ := hmem (a : Y) (hQ ⟨a, ha, rfl⟩)
  obtain ⟨s', hs', hsb⟩ := hmem (b : Y) (hQ ⟨b, hb, rfl⟩)
  have hss : s * s' = s' * s := by
    have := h.P_comm.is_comm.comm (⟨s, hs⟩ : ↥P) ⟨s', hs'⟩
    exact congrArg Subtype.val this
  apply Subtype.ext
  apply Subtype.ext
  show (a : Y) * b = b * a
  rw [← hsa, ← hsb]
  calc g * s * g⁻¹ * (g * s' * g⁻¹) = g * (s * s') * g⁻¹ := by group
    _ = g * (s' * s) * g⁻¹ := by rw [hss]
    _ = g * s' * g⁻¹ * (g * s * g⁻¹) := by group

theorem a10y_no_central_five (h : A10YData Y P x t₁ t₂ J₁ J₂ F) {H : Subgroup Y} (hH : ⁅H, H⁆ = H)
    {z : Y} (hz : z ∈ H) (hc : ∀ a ∈ H, z * a = a * z) (h5 : z ^ 5 = 1) : z = 1 := by
  by_contra hz1
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.2 hH
  have hperf : commutator ↥H = ⊤ := Group.IsPerfect.commutator_eq_top
  have hzc : (⟨z, hz⟩ : ↥H) ∈ Subgroup.center ↥H := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  have hord : orderOf (⟨z, hz⟩ : ↥H) = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime h5 hz1
  have hdvd : 5 ∣ Nat.card (Subgroup.center ↥H) := by
    have hle : Subgroup.zpowers (⟨z, hz⟩ : ↥H) ≤ Subgroup.center ↥H := Subgroup.zpowers_le.2 hzc
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hord] at this
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 5 ↥H))
  exact GL83.not_isMulCommutative_sylow_of_perfect hperf hdvd S (a10y_sylow_comm h H S)

theorem a10y_comp_simple (h : A10YData Y P x t₁ t₂ J₁ J₂ F) {A : Subgroup Y} (hA : IsComponentOf A ⊤) :
    center ↥A = ⊥ ∧ IsSimpleGroup ↥A ∧ (∃ a b : ↥A, a * b ≠ b * a) ∧ IsCatalogGroup ↥A := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hperf : ⁅A, A⁆ = A := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hA.2.2.1)
  have hcop : Nat.Coprime 5 (Nat.card (center ↥A)) := by
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num)]
    intro hd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 5 hd
    have hzA : orderOf (z : ↥A) = 5 := (Subgroup.orderOf_coe z).trans hz
    have hzc : (z : ↥A) ∈ center ↥A := z.2
    have hz5 : (z : ↥A) ^ 5 = 1 := by rw [← hzA]; exact pow_orderOf_eq_one _
    have h5 : ((z : ↥A) : Y) ^ 5 = 1 := by
      have := congrArg (fun u : ↥A => (u : Y)) hz5
      simpa using this
    have h1 : ((z : ↥A) : Y) = 1 :=
      a10y_no_central_five h hperf (z := ((z : ↥A) : Y)) (z : ↥A).2
        (fun a ha => congrArg Subtype.val ((Subgroup.mem_center_iff.1 hzc ⟨a, ha⟩).symm)) h5
    have h2 : (z : ↥A) = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hzA
    exact absurd hzA (by norm_num)
  have hZle : center ↥A ≤ GLAPPrimeCore 5 ↥A := le_sSup ⟨inferInstance, hcop⟩
  have hcoreTop : GLAPPrimeCore 5 ↥(⊤ : Subgroup Y) = ⊥ := by
    have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCore_map_iso 5
      (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y)
    rw [a10y_glaCore h] at h1
    exact Subgroup.map_injective (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y).injective
      (by simpa using h1)
  have hle : (center ↥A).map A.subtype ≤ GLAPPrimeCoreOf 5 (⊤ : Subgroup Y) :=
    (Subgroup.map_mono hZle).trans
      (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal (by norm_num) hA.2.1)
  have hbot : GLAPPrimeCoreOf 5 (⊤ : Subgroup Y) = ⊥ := by
    unfold GLAPPrimeCoreOf
    rw [hcoreTop]
    exact Subgroup.map_bot _
  have hZ : center ↥A = ⊥ := by
    rw [hbot, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ A.subtype_injective] at hle
    exact hle
  obtain ⟨hsimple, hnonab⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.isSimpleGroup_of_isComponentOf_of_center_eq_bot hA hZ
  exact ⟨hZ, hsimple, hnonab, h.catalog.simple_subgroup A hsimple hnonab⟩

theorem a10y_comp_eq_of_perfect_le {A A' J : Subgroup Y} (hA : IsComponentOf A ⊤)
    (hA' : IsComponentOf A' ⊤) (hJ : ⁅J, J⁆ = J) (hJ1 : J ≠ ⊥) (hJA : J ≤ A) (hJA' : J ≤ A') :
    A = A' := by
  by_contra hne
  have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne A A' hA hA' hne
  apply hJ1
  rw [← hJ]
  exact le_bot_iff.mp (hc ▸ Subgroup.commutator_mono hJA hJA')

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

