module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43YBasic
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux8
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

variable {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x t₁ t₂ : Y} {J₁ J₂ F : Subgroup Y}

theorem a10y_not_le_centralizer (h : A10YData Y P x t₁ t₂ J₁ J₂ F) {J A : Subgroup Y} {t : Y}
    (hJ : GLAPComponent 5 (Subgroup.centralizer ({x} : Set Y)) J) (ht : t ∈ J) (ht5 : orderOf t = 5)
    (hA : IsComponentOf A ⊤) (hJA : J ≤ A) (hJn : ¬ IsComponentOf J ⊤) :
    ¬ A ≤ Subgroup.centralizer ({x} : Set Y) := by
  intro hAC
  obtain ⟨-, hsimple, hnab, -⟩ := a10y_comp_simple h hA
  have h5A : 5 ∣ Nat.card ↥A := by
    have hzA : Subgroup.zpowers t ≤ A := (Subgroup.zpowers_le).2 (hJA ht)
    have h1 : Nat.card ↥(Subgroup.zpowers t) = 5 := by
      rw [Nat.card_zpowers, ht5]
    exact h1 ▸ Subgroup.card_dvd_of_le hzA
  have hAsn : IsSubnormal A (Subgroup.centralizer ({x} : Set Y)) :=
    CFSG.LocalAnalysis.GLTheoremB.isSubnormal_of_le_of_le hA.2.1 hAC le_top
  have hAcomp : GLAPComponent 5 (Subgroup.centralizer ({x} : Set Y)) A :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.glaPComponent_of_simple (by norm_num) hAC
      hAsn hsimple hnab h5A
  have hbar : CFSG.LocalAnalysis.GLTheoremB.barX 5 (Subgroup.centralizer ({x} : Set Y)) J ≤
      CFSG.LocalAnalysis.GLTheoremB.barX 5 (Subgroup.centralizer ({x} : Set Y)) A :=
    CFSG.LocalAnalysis.GLTheoremB.barX_mono 5 hJA
  have heq : CFSG.LocalAnalysis.GLTheoremB.barX 5 (Subgroup.centralizer ({x} : Set Y)) J =
      CFSG.LocalAnalysis.GLTheoremB.barX 5 (Subgroup.centralizer ({x} : Set Y)) A :=
    CFSG.ComponentClassification.LocalComponents.eq_of_le _ _ hJ.2.2.1 hAcomp.2.2.1 hbar
  have hJA' : J = A := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_unique hJ hAcomp heq
  exact hJn (hJA' ▸ hA)

theorem a10y_inner_action (hInn : KFactInnerAction) (h : A10YData Y P x t₁ t₂ J₁ J₂ F)
    {A : Subgroup Y} (hA : IsComponentOf A ⊤) (hPA : P ⊓ A ≠ ⊥) {q : Y} (hq : q ∈ P) :
    ∃ g ∈ P ⊓ A, ∀ a ∈ A, q * a * q⁻¹ = g * a * g⁻¹ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI hPc : IsMulCommutative P := h.P_comm
  obtain ⟨_, hSimple, hNonab, hCat⟩ := a10y_comp_simple h hA
  obtain ⟨S, hSP⟩ := h.sylow
  have hsub : A.IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hA.2.1
      Subgroup.IsSubnormal.top
  obtain ⟨SA, hSA⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hsub
  rw [hSP] at hSA
  have hSAne : (SA : Subgroup ↥A) ≠ ⊥ := by
    intro hbot
    apply hPA
    rw [← hSA, hbot, Subgroup.map_bot]
  have hSAmem : ∀ a : ↥A, a ∈ (SA : Subgroup ↥A) → (a : Y) ∈ P ⊓ A := by
    intro a ha
    have hmem : (a : Y) ∈ (SA : Subgroup ↥A).map A.subtype := Subgroup.mem_map_of_mem _ ha
    rwa [hSA] at hmem
  haveI hSAc : IsMulCommutative (SA : Subgroup ↥A) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    exact setLike_mul_comm (hSAmem a.1 a.2).1 (hSAmem b.1 b.2).1
  obtain ⟨k, hk⟩ := a10y_sylow_pow h hq
  have hqN : q ∈ Subgroup.normalizer (A : Set Y) :=
    a10y_mem_normalizer_of_pElement h ⟨k, hk⟩ hA
  have hφ : ∀ a : ↥A, ((Subgroup.normalizerMonoidHom A ⟨q, hqN⟩ a : ↥A) : Y) = q * a * q⁻¹ := by
    intro a
    exact Subgroup.normalizerMonoidHom_apply_apply_coe A ⟨q, hqN⟩ a
  have hφpow : (Subgroup.normalizerMonoidHom A ⟨q, hqN⟩) ^ (5 ^ k) = 1 := by
    rw [← map_pow]
    have hpow : (⟨q, hqN⟩ : ↥(Subgroup.normalizer (A : Set Y))) ^ (5 ^ k) = 1 := by
      apply Subtype.ext
      simpa using hk
    rw [hpow, map_one]
  have hcomm : ∀ g ∈ (SA : Subgroup ↥A),
      Subgroup.normalizerMonoidHom A ⟨q, hqN⟩ * MulAut.conj g =
        MulAut.conj g * Subgroup.normalizerMonoidHom A ⟨q, hqN⟩ := by
    intro g hg
    have hqg : q * (g : Y) = (g : Y) * q := setLike_mul_comm hq (hSAmem g hg).1
    have h1 : q * (g : Y) * q⁻¹ = (g : Y) := by
      rw [hqg]
      group
    ext a
    simp only [MulAut.mul_apply, MulAut.conj_apply, hφ, Subgroup.coe_mul, Subgroup.coe_inv]
    calc q * ((g : Y) * (a : Y) * (g : Y)⁻¹) * q⁻¹
        = (q * (g : Y) * q⁻¹) * (q * (a : Y) * q⁻¹) * (q * (g : Y) * q⁻¹)⁻¹ := by group
      _ = (g : Y) * (q * (a : Y) * q⁻¹) * (g : Y)⁻¹ := by rw [h1]
  obtain ⟨g, hgS, hgφ⟩ := hInn 5 (by norm_num) (by norm_num) ↥A hSimple hNonab hCat SA hSAne hSAc
    (Subgroup.normalizerMonoidHom A ⟨q, hqN⟩) ⟨k, hφpow⟩ hcomm
  refine ⟨(g : Y), hSAmem g hgS, ?_⟩
  intro a ha
  have hev := congrArg (fun ψ : MulAut ↥A => ((ψ ⟨a, ha⟩ : ↥A) : Y)) hgφ
  simp only [hφ] at hev
  simpa using hev

theorem a10y_g_exists (hInn : KFactInnerAction) (h : A10YData Y P x t₁ t₂ J₁ J₂ F) {J A : Subgroup Y}
    {t : Y} (hJ : GLAPComponent 5 (Subgroup.centralizer ({x} : Set Y)) J) (ht : t ∈ P ⊓ J)
    (ht5 : orderOf t = 5) (hA : IsComponentOf A ⊤) (hJA : J ≤ A) (hJn : ¬ IsComponentOf J ⊤) :
    ∃ g ∈ P ⊓ A, g ≠ 1 ∧ g ∉ J ∧ g ^ 5 = 1 ∧ ∀ a ∈ A, x * a * x⁻¹ = g * a * g⁻¹ := by
  have htA : t ∈ A := hJA ht.2
  have hPA : P ⊓ A ≠ ⊥ := by
    intro hbot
    have hmem : t ∈ P ⊓ A := ⟨ht.1, htA⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at ht5
    exact absurd ht5 (by norm_num)
  obtain ⟨g, hgPA, hg⟩ := a10y_inner_action hInn h hA hPA h.x_mem
  have hgA : g ∈ A := hgPA.2
  have hJC : ∀ a ∈ J, a * x = x * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (hJ.1 ha)
  have hg1 : g ≠ 1 := by
    rintro rfl
    refine a10y_not_le_centralizer h hJ ht.2 ht5 hA hJA hJn (fun a ha => ?_)
    have h1 := hg a ha
    simp only [one_mul, inv_one, mul_one] at h1
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hpow : ∀ n : ℕ, ∀ a ∈ A, x ^ n * a * (x ^ n)⁻¹ = g ^ n * a * (g ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro a _; simp
    | succ n ih =>
      intro a ha
      have hxa : x * a * x⁻¹ = g * a * g⁻¹ := hg a ha
      have hmem : g * a * g⁻¹ ∈ A := A.mul_mem (A.mul_mem hgA ha) (A.inv_mem hgA)
      calc x ^ (n + 1) * a * (x ^ (n + 1))⁻¹ = x ^ n * (x * a * x⁻¹) * (x ^ n)⁻¹ := by
            rw [pow_succ, mul_inv_rev]; simp only [mul_assoc]
        _ = x ^ n * (g * a * g⁻¹) * (x ^ n)⁻¹ := by rw [hxa]
        _ = g ^ n * (g * a * g⁻¹) * (g ^ n)⁻¹ := ih _ hmem
        _ = g ^ (n + 1) * a * (g ^ (n + 1))⁻¹ := by
            rw [pow_succ, mul_inv_rev]; simp only [mul_assoc]
  have hx5 : x ^ 5 = 1 := by rw [← h.x_ord]; exact pow_orderOf_eq_one x
  have hg5 : g ^ 5 = 1 := by
    have hmemA : g ^ 5 ∈ A := A.pow_mem hgA 5
    have hcent : (⟨g ^ 5, hmemA⟩ : ↥A) ∈ Subgroup.center ↥A := by
      rw [Subgroup.mem_center_iff]
      intro b
      apply Subtype.ext
      have h5 := hpow 5 b b.2
      rw [hx5] at h5
      simp only [one_mul, inv_one, mul_one] at h5
      exact eq_mul_inv_iff_mul_eq.mp h5
    rw [(a10y_comp_simple h hA).1, Subgroup.mem_bot] at hcent
    exact congrArg Subtype.val hcent
  have hgJ : g ∉ J := by
    intro hgJ
    refine hg1 (a10y_no_central_five h (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
      hgJ ?_ hg5)
    intro a ha
    have h1 : x * a * x⁻¹ = g * a * g⁻¹ := hg a (hJA ha)
    have h2 : x * a * x⁻¹ = a := mul_inv_eq_iff_eq_mul.mpr (hJC a ha).symm
    rw [h2] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1.symm
  exact ⟨g, hgPA, hg1, hgJ, hg5, hg⟩

theorem a10y_P_comm (h : A10YData Y P x t₁ t₂ J₁ J₂ F) {a b : Y} (ha : a ∈ P) (hb : b ∈ P) :
    a * b = b * a :=
  isMulCommutative_iff_of_setLike.mp h.P_comm a ha b hb

theorem a10y_card_zpowers_sup (h : A10YData Y P x t₁ t₂ J₁ J₂ F) {t g : Y} (htP : t ∈ P) (hgP : g ∈ P)
    (ht5 : orderOf t = 5) (hg5 : g ^ 5 = 1) (hgt : g ∉ zpowers t) :
    Nat.card ↥(zpowers t ⊔ zpowers g) = 25 := by
  have hcomm : ∀ e ∈ zpowers t, e * g = g * e := by
    intro e he
    have hle : zpowers t ≤ Subgroup.centralizer ({g} : Set Y) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (a10y_P_comm h htP hgP))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers (by norm_num) (zpowers t) hg5 hgt hcomm,
    Nat.card_zpowers, ht5]

theorem a10y_A_eq (hInn : KFactInnerAction) {A₁ A₂ : Subgroup Y}
    (c : A10YCaseC Y P x t₁ t₂ J₁ J₂ F A₁ A₂) : A₁ = A₂ := by
  by_contra hne
  have h := c.data
  obtain ⟨g₁, hg₁PA, -, hg₁J, hg₁5, -⟩ :=
    a10y_g_exists hInn h h.comp₁ h.t₁_mem h.t₁_ord c.comp₁ c.le₁ c.not₁
  obtain ⟨g₂, hg₂PA, -, hg₂J, hg₂5, -⟩ :=
    a10y_g_exists hInn h h.comp₂ h.t₂_mem h.t₂_ord c.comp₂ c.le₂ c.not₂
  obtain ⟨-, hVcard, -, hVall⟩ := a10y_V h
  have ht₁J : zpowers t₁ ≤ J₁ := Subgroup.zpowers_le.mpr h.t₁_mem.2
  have ht₂J : zpowers t₂ ≤ J₂ := Subgroup.zpowers_le.mpr h.t₂_mem.2
  have hg₁t : g₁ ∉ zpowers t₁ := fun hh => hg₁J (ht₁J hh)
  have hg₂t : g₂ ∉ zpowers t₂ := fun hh => hg₂J (ht₂J hh)
  have hE₁card : Nat.card ↥(zpowers t₁ ⊔ zpowers g₁) = 25 :=
    a10y_card_zpowers_sup h h.t₁_mem.1 hg₁PA.1 h.t₁_ord hg₁5 hg₁t
  have hE₂card : Nat.card ↥(zpowers t₂ ⊔ zpowers g₂) = 25 :=
    a10y_card_zpowers_sup h h.t₂_mem.1 hg₂PA.1 h.t₂_ord hg₂5 hg₂t
  have hE₁A : zpowers t₁ ⊔ zpowers g₁ ≤ A₁ :=
    sup_le (ht₁J.trans c.le₁) (Subgroup.zpowers_le.mpr hg₁PA.2)
  have hE₂A : zpowers t₂ ⊔ zpowers g₂ ≤ A₂ :=
    sup_le (ht₂J.trans c.le₂) (Subgroup.zpowers_le.mpr hg₂PA.2)
  have hE₁P : zpowers t₁ ⊔ zpowers g₁ ≤ P :=
    sup_le (Subgroup.zpowers_le.mpr h.t₁_mem.1) (Subgroup.zpowers_le.mpr hg₁PA.1)
  have hE₂P : zpowers t₂ ⊔ zpowers g₂ ≤ P :=
    sup_le (Subgroup.zpowers_le.mpr h.t₂_mem.1) (Subgroup.zpowers_le.mpr hg₂PA.1)
  have hE₁V : zpowers t₁ ⊔ zpowers g₁ ≤ zpowers t₁ ⊔ zpowers t₂ ⊔ zpowers x :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (Subgroup.mem_zpowers t₁))))
      (Subgroup.zpowers_le.mpr (hVall g₁ hg₁PA.1 hg₁5))
  have hE₂V : zpowers t₂ ⊔ zpowers g₂ ≤ zpowers t₁ ⊔ zpowers t₂ ⊔ zpowers x :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_sup_right
      (Subgroup.mem_zpowers t₂))))
      (Subgroup.zpowers_le.mpr (hVall g₂ hg₂PA.1 hg₂5))
  have hA₁C : A₁ ≤ Subgroup.centralizer (A₂ : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne A₁ A₂ c.comp₁ c.comp₂ hne)
  have hdisj : Disjoint (zpowers t₁ ⊔ zpowers g₁) (zpowers t₂ ⊔ zpowers g₂) := by
    rw [Subgroup.disjoint_def]
    intro u hu₁ hu₂
    have hu₁A : u ∈ A₁ := hE₁A hu₁
    have hu₂A : u ∈ A₂ := hE₂A hu₂
    have hcen : (⟨u, hu₁A⟩ : ↥A₁) ∈ Subgroup.center ↥A₁ := by
      rw [Subgroup.mem_center_iff]
      intro b
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hA₁C b.2) u hu₂A).symm
    rw [(a10y_comp_simple h c.comp₁).1, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hnorm : zpowers t₂ ⊔ zpowers g₂ ≤
      Subgroup.normalizer ((zpowers t₁ ⊔ zpowers g₁ : Subgroup Y) : Set Y) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact a10y_P_comm h (hE₁P he) (hE₂P hu)
  have hcard :
      Nat.card ↥((zpowers t₁ ⊔ zpowers g₁) ⊔ (zpowers t₂ ⊔ zpowers g₂)) = 25 * 25 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
      hE₁card, hE₂card]
  have hle := Subgroup.card_le_of_le (sup_le hE₁V hE₂V)
  rw [hcard, hVcard] at hle
  exact absurd hle (by norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
