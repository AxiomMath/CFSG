module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Claim1A4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Claim1Assembly
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A8Table
import Mathlib.Tactic.Group
public import Certificates.Certificate1
public import Certificates.Certificate2
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Subgroup

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem A3A3K.conjR_le_cent₁ (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hK : A3A3K T M H S L s x z₁ z₂ K) : conjR K s ≤ centralizerElem z₁ := by
  have hz₁s : s⁻¹ * z₂ * s = z₁ := hK.z₁_eq hD h27_1
  have hD3 : s * z₁ * s⁻¹ = z₂ := by rw [← hz₁s]; group
  intro a ha
  have hκ : s * a * s⁻¹ ∈ K := mem_conjR.mp ha
  have h1 : (s * a * s⁻¹) * z₂ = z₂ * (s * a * s⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hK.K_comp.1 hκ)
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  refine (comm_iff_conj s a z₁).mpr ?_
  rw [hD3]
  exact h1

theorem A3A3K.cent₁_le_normalizer (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hK : A3A3K T M H S L s x z₁ z₂ K) :
    centralizerElem z₁ ≤ normalizer (conjR K s : Set G) := by
  have hz₁s : s⁻¹ * z₂ * s = z₁ := hK.z₁_eq hD h27_1
  have hD3 : s * z₁ * s⁻¹ = z₂ := by rw [← hz₁s]; group
  intro g hg
  have hgz : g * z₁ = z₁ * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hg₂ : (s * g * s⁻¹) ∈ centralizerElem z₂ := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h1 := (comm_iff_conj s g z₁).mp hgz
    rwa [hD3] at h1
  have hg₂N : (s * g * s⁻¹) ∈ normalizer (K : Set G) := hK.K_norm hg₂
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_conjR, mem_conjR]
  have e : s * (g * y * g⁻¹) * s⁻¹ = (s * g * s⁻¹) * (s * y * s⁻¹) * (s * g * s⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp hg₂N (s * y * s⁻¹)

theorem A3A3K.false_of_A8_core
    (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (h34 : Lemma2_4_34_used) (hK : A3A3K T M H S L s x z₁ z₂ K) {Λ Λ₂ Λr V V₂ W : Subgroup G}
    (hΛ : IsA4Block Λ V) (hΛ₂ : IsA4Block Λ₂ V₂) (hz₁Λ : z₁ ∈ Λ) (hΛ₂A : Λ₂ ≤ conjR K s)
    (hz₂Λ₂ : z₂ ∈ Λ₂) (hcomm₂ : ∀ l ∈ Λ, ∀ y ∈ Λ₂, l * y = y * l) (hΛr : IsA4Block Λr W)
    (hcommr : ∀ l ∈ Λ, ∀ y ∈ Λr, l * y = y * l) (hz₂N : z₂ ∈ normalizer (Λr : Set G))
    (hz₂Λr : z₂ ∉ Λr) : False := by
  have hcs := hK.cs
  have he : CFSG.Assembly.evenRank G ≤ 2 := hcs.setting.qtke.2.2
  obtain ⟨e₀⟩ := hK.nonempty_alt6 h34
  obtain ⟨ι, -⟩ := exists_conjR_equiv K s
  have heA : ↥(conjR K s) ≃* alternatingGroup (Fin 6) := ι.symm.trans e₀
  have hz₁1 : z₁ ≠ 1 := hK.z₁_ne
  have hz₁2' : z₁ ^ 2 = 1 := hK.toA3A3x.sq₁
  have hz₂2 : z₂ * z₂ = 1 := by simpa [pow_two] using hK.toA3A3x.sq₂
  have hAG₁ := hK.conjR_le_cent₁ hD h27_1
  have hG₁N := hK.cent₁_le_normalizer hD h27_1
  have hrank : ∀ E : Subgroup G, E ≤ centralizerElem z₁ → IsElemAbelian 3 E → Nat.card E ≤ 9 :=
    fun E hE hEa => card_isElemAbelian_three_le he (isTwoLocal_centralizerElem hz₁1 hz₁2') hE hEa
  have hΛrG₁ : Λr ≤ centralizerElem z₁ := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcommr z₁ hz₁Λ y hy).symm
  have hΛrA : Λr ≤ conjR K s :=
    hΛr.le_of_forall_order_three fun y hy hy3 =>
      mem_of_orderThree_normalizing heA hAG₁ hG₁N hrank (hΛrG₁ hy) hy3
  set C : Subgroup G := conjR K s ⊓ Subgroup.centralizer (Λ : Set G) with hC
  have hΛrC : Λr ≤ C := fun y hy =>
    ⟨hΛrA hy, Subgroup.mem_centralizer_iff.mpr fun l hl => hcommr l hl y hy⟩
  have hΛ₂C : Λ₂ ≤ C := fun y hy =>
    ⟨hΛ₂A hy, Subgroup.mem_centralizer_iff.mpr fun l hl => hcomm₂ l hl y hy⟩
  have hCA : C = conjR K s :=
    eq_of_two_A4 heA inf_le_left hΛrC hΛ₂C hΛr.card_L hΛ₂ hz₂Λ₂ hz₂Λr hz₂2 hz₂N
  have hAΛ : ∀ a ∈ conjR K s, ∀ l ∈ Λ, l * a = a * l := by
    intro a ha l hl
    have : a ∈ C := by rw [hCA]; exact ha
    exact Subgroup.mem_centralizer_iff.mp this.2 l hl
  obtain ⟨c, hcΛ, hc, hcN, -, -⟩ := hΛ.exists_c
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    omega
  have hV1 : V ≠ ⊥ := by
    intro h
    have := hΛ.card_U
    rw [h, Subgroup.card_bot] at this
    omega
  have hNloc : IsTwoLocal (normalizer (V : Set G)) := ⟨V, hV1, hΛ.isPGroup_U, rfl⟩
  have hAN : conjR K s ≤ normalizer (V : Set G) := by
    apply C5.le_normalizer_of_commute
    intro a ha v hv
    exact (hAΛ a ha v (hΛ.le hv)).symm
  have hrank' : ∀ E : Subgroup G, E ≤ normalizer (V : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 9 :=
    fun E hE hEa => card_isElemAbelian_three_le he hNloc hE hEa
  exact false_of_centralizing_order_three heA hAN hrank' hcN hc3 hc1
    (fun a ha => (hAΛ a ha c hcΛ).symm)

theorem A3A3K.false_of_A8
    (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (h34 : Lemma2_4_34_used)
    (hK : A3A3K T M H S L s x z₁ z₂ K) {J : Subgroup G}
    (hKcomp : IsComponentIn K (J ⊓ Subgroup.centralizer ({z₂} : Set G)))
    (hpat : Id2519.PatA8 J K z₂) : False := by
  have hcs := hK.cs
  obtain ⟨e₀⟩ := hK.nonempty_alt6 h34
  have hB := basic31 hD h27_1 hK.toA3A3
  have hxN : x ∈ normalizer (baum S : Set G) := hK.toA3A3x.x_mem_normalizer_baum hB
  have hxG₂ : x ∈ centralizerElem z₂ := Subgroup.mem_centralizer_singleton_iff.mpr hK.x_comm₂
  have hxK : x ∈ normalizer (K : Set G) := hK.K_norm hxG₂
  have hxG₁ : x ∈ centralizerElem z₁ := Subgroup.mem_centralizer_singleton_iff.mpr hK.x_comm₁
  have hxA : x ∈ normalizer (conjR K s : Set G) := hK.cent₁_le_normalizer hD h27_1 hxG₁
  have hA := hK.isA4
  have hAs := hK.isA4s
  have hUK : blockU L ≤ K := hA.le.trans hK.L_le_K
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hK.a3
  have hLxK : conjR L x ≤ K :=
    (C5.conjSubgroup_mono hK.L_le_K x).trans (le_of_eq (C5.conjSubgroup_eq_self hxK))
  have hUxK : conjR (blockU L) x ≤ K :=
    (C5.conjSubgroup_mono hUK x).trans (le_of_eq (C5.conjSubgroup_eq_self hxK))
  have hUxB : conjR (blockU L) x ≤ baum S :=
    (C5.conjSubgroup_mono hUB x).trans (le_of_eq (C5.conjSubgroup_eq_self hxN))
  obtain ⟨-, hR8⟩ := hK.rK_eq hD h27_1 e₀
  have hUne : blockU L ≠ conjR (blockU L) x := by
    intro h
    apply hK.x_good
    rw [← h]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mpr fun v hv => hA.comm_U v hv y hy
  obtain ⟨Λ, Λr, W, hΛcase, -, hΛr, hcommr, hz₂N, hz₂Λr⟩ := tabA8 G J K z₂ L (conjR L x)
    (blockU L) (conjR (blockU L) x) (baum S ⊓ K) hpat hKcomp hA (hA.conj x) hK.L_le_K hLxK hUne
    inf_le_right hR8 (le_inf hUB hUK) (le_inf hUxB hUxK)
  rcases hΛcase with hΛL | hΛL
  ·
    rw [hΛL] at hcommr
    have hz₁U : z₁ ∈ blockU L := hK.toA3A3x.z₁_mem.1
    exact hK.false_of_A8_core hD h27_1 h34 hA hAs (hA.le hz₁U)
      (Subgroup.map_mono hK.L_le_K : conjR L s ≤ conjR K s)
      (hAs.le hK.toA3A3x.z₂_mem.1) (fun l hl y hy => hK.comm_elem l hl y hy) hΛr hcommr hz₂N hz₂Λr
  ·
    rw [hΛL] at hcommr
    have hz₁U : z₁ ∈ blockU L := hK.toA3A3x.z₁_mem.1
    have hz₁x : z₁ ∈ conjR L x := by
      refine mem_conjR.mpr ?_
      have : x * z₁ * x⁻¹ = z₁ := by
        calc x * z₁ * x⁻¹ = (z₁ * x) * x⁻¹ := by rw [hK.x_comm₁]
          _ = z₁ := by group
      rw [this]
      exact hA.le hz₁U
    have hz₂x : z₂ ∈ conjR (conjR L s) x := by
      refine mem_conjR.mpr ?_
      have : x * z₂ * x⁻¹ = z₂ := by
        calc x * z₂ * x⁻¹ = (z₂ * x) * x⁻¹ := by rw [hK.x_comm₂]
          _ = z₂ := by group
      rw [this]
      exact hAs.le hK.toA3A3x.z₂_mem.1
    have hΛ₂A : conjR (conjR L s) x ≤ conjR K s :=
      ((C5.conjSubgroup_mono (Subgroup.map_mono hK.L_le_K : conjR L s ≤ conjR K s) x).trans
        (le_of_eq (C5.conjSubgroup_eq_self hxA)))
    have hcomm₂ : ∀ l ∈ conjR L x, ∀ y ∈ conjR (conjR L s) x, l * y = y * l := by
      intro l hl y hy
      refine (comm_iff_conj x l y).mpr ?_
      exact hK.comm_elem _ (mem_conjR.mp hl) _ (mem_conjR.mp hy)
    exact hK.false_of_A8_core hD h27_1 h34 (hA.conj x) (hAs.conj x) hz₁x hΛ₂A hz₂x hcomm₂ hΛr
      hcommr hz₂N hz₂Λr

end CFSG.QuasithinUnique.DoubleA3
