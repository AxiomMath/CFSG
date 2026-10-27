module

public import CFSG.ClassicalInvolution.Balance.Delta

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification
open scoped commutatorElement

section StepOne

variable {G : Type*} [Group G] [Finite G]

theorem le_centralizer_oddCoreIn_inf_centralizer {C K E₀ L₀ F : Subgroup G}
    (hKC : IsSubnormal K C) (hFE : F ≤ E₀) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤)
    (hΔ : deltaCore F = ⊥)
    (hB : ∀ f ∈ F, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f) :
    L₀ ≤ Subgroup.centralizer ((oddCoreIn K ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) :
      Set G) := by
  set V : Subgroup G := oddCoreIn K ⊓ Subgroup.centralizer (F : Set G) with hV
  have hVodd : Odd (Nat.card V) :=
    (odd_card_oddCoreIn K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hKC' : K ≤ C := isSubnormal_le hKC
  have hOC : IsSubnormal (oddCoreIn K) C := isSubnormal_trans (isSubnormal_oddCoreIn K) hKC
  have hconj : ∀ q ∈ L₀, ∀ v ∈ V, q * v * q⁻¹ ∈ V := by
    intro q hq v hv
    refine ⟨conj_mem_oddCoreIn (hL₀K hq) hv.1, ?_⟩
    show q * v * q⁻¹ ∈ Subgroup.centralizer (F : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhq : Commute h q := Subgroup.mem_centralizer_iff.mp (hL₀E hq) h (hFE hh)
    have hhv : Commute h v := Subgroup.mem_centralizer_iff.mp hv.2 h hh
    exact ((hhq.mul_right hhv).mul_right hhq.inv_right).eq
  refine le_of_perfect_of_forall_isPGroup_le hL₀ fun P hPL hP => ?_
  have hPnorm : P ≤ Subgroup.normalizer (V : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconj p (hPL hp) y hy, fun hy => ?_⟩
    have h2 := hconj p⁻¹ (inv_mem (hPL hp)) _ hy
    have h3 : p⁻¹ * (p * y * p⁻¹) * (p⁻¹)⁻¹ = y := by group
    rwa [h3] at h2
  have hcomm : ⁅V, P⁆ = ⊥ := by
    have h1 : ⁅⁅V, P⁆, P⁆ = ⁅V, P⁆ := commutator_commutator_eq_of_isPGroup hP hVodd hPnorm
    rw [eq_bot_iff, ← hΔ]
    refine le_deltaCore fun f hf hf1 => ?_
    set Nf := normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀ with hNf
    have hL₀le : L₀ ≤ C ⊓ Subgroup.centralizer {f} := by
      refine le_inf (hL₀K.trans hKC') fun l hl => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hL₀E hl) f (hFE hf)).symm
    have hNfle : Nf ≤ C ⊓ Subgroup.centralizer {f} := normalClosureIn_le_of_le hL₀le
    have hsub : IsSubnormal (oddCoreIn K ⊓ Nf) Nf := by
      have := isSubnormal_inf hOC Nf
      rwa [inf_eq_right.mpr (hNfle.trans inf_le_left)] at this
    have hle := le_oddCoreIn_of_isSubnormal hsub
      ((odd_card_oddCoreIn K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    have hVNf : ⁅V, P⁆ ≤ oddCoreIn Nf := by
      refine le_trans ?_ hle
      rw [Subgroup.commutator_le]
      intro v hv p hp
      have hpK : p ∈ K := hL₀K (hPL hp)
      have hvC : v ∈ C ⊓ Subgroup.centralizer {f} := by
        refine ⟨hKC' (oddCoreIn_le K hv.1), ?_⟩
        show v ∈ Subgroup.centralizer {f}
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hv.2 f hf).symm
      have hpNf : p ∈ Nf := le_normalClosureIn _ _ (hPL hp)
      refine ⟨?_, ?_⟩
      · have : ⁅v, p⁆ = v * (p * v⁻¹ * p⁻¹) := by simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact (oddCoreIn K).mul_mem hv.1 (conj_mem_oddCoreIn hpK ((oddCoreIn K).inv_mem hv.1))
      · exact Nf.mul_mem (conj_mem_normalClosureIn hvC hpNf) (Nf.inv_mem hpNf)
    calc ⁅V, P⁆ = ⁅⁅V, P⁆, P⁆ := h1.symm
      _ ≤ ⁅oddCoreIn Nf, Nf⁆ :=
        Subgroup.commutator_mono hVNf (hPL.trans (le_normalClosureIn _ _))
      _ ≤ involutionOddCore f := hB f hf hf1
  have hcomm' : ⁅P, V⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hcomm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'

end StepOne

section StepTwo

variable {G : Type*} [Group G] [Finite G]

theorem le_centralizer_oddCoreIn {C K E₀ L₀ : Subgroup G} (hKC : IsSubnormal K C)
    (hE₀K : E₀ ≤ K) (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hB : ∀ f ∈ E₀, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f) :
    L₀ ≤ Subgroup.centralizer (oddCoreIn K : Set G) := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two E₀ (oddCoreIn K) hE₀ (by rw [hE₀card]; norm_num)
    (hE₀K.trans (normalizer_oddCoreIn K))
    (Nat.coprime_two_left.mpr (odd_card_oddCoreIn K))
  have h1 : oddCoreIn K ≤ Subgroup.centralizer (L₀ : Set G) := by
    refine hgen.symm.le.trans (iSup₂_le fun F hF => ?_)
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlv := le_centralizer_oddCoreIn_inf_centralizer hKC hF.1 hL₀K hL₀E hL₀ (hΔ F hF)
      (fun f hf hf1 => hB f (hF.1 hf) hf1) hl
    exact (Subgroup.mem_centralizer_iff.mp hlv v hv).symm
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  exact (Subgroup.mem_centralizer_iff.mp (h1 ho) l hl).symm

end StepTwo

section StepThree

variable {G : Type*} [Group G] [Finite G]

theorem oddCoreIn_le_centralizer_of_deltaTrivial {C K E₀ L₀ : Subgroup G}
    (hKC : IsSubnormal K C) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀K : E₀ ≤ K) (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hB : ∀ f ∈ E₀, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f) :
    oddCoreIn K ≤ Subgroup.centralizer (K : Set G) := by
  have h2 := le_centralizer_oddCoreIn hKC hE₀K hE₀ hE₀card hL₀K hL₀E hL₀ hΔ hB
  set O := oddCoreIn K with hO
  set OK := componentClassificationOddCore K with hOK
  set N := normalClosureIn K L₀ with hN
  have hNK : N ≤ K := normalClosureIn_le_of_le hL₀K
  have hN1 : N ≤ Subgroup.centralizer (O : Set G) := by
    refine normalClosureIn_le fun g hg => ?_
    rintro _ ⟨l, hl, rfl⟩
    change g * l * g⁻¹ ∈ Subgroup.centralizer (O : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have ho' : g⁻¹ * o * g ∈ O := by
      have := conj_mem_oddCoreIn (X := K) (inv_mem hg) ho
      simpa using this
    have hcl : (g⁻¹ * o * g) * l = l * (g⁻¹ * o * g) :=
      Subgroup.mem_centralizer_iff.mp (h2 hl) _ ho'
    calc o * (g * l * g⁻¹) = g * ((g⁻¹ * o * g) * l) * g⁻¹ := by group
      _ = g * (l * (g⁻¹ * o * g)) * g⁻¹ := by rw [hcl]
      _ = g * l * g⁻¹ * o := by group
  have hfact : ∀ k : K, ∃ n : K, n ∈ N.subgroupOf K ∧ n⁻¹ * k ∈ OK := by
    have hNnormal : (N.subgroupOf K).Normal := normal_subgroupOf_normalClosureIn hL₀K
    have hN'normal : ((N.subgroupOf K).map (QuotientGroup.mk' OK)).Normal :=
      Subgroup.Normal.map hNnormal (QuotientGroup.mk' OK) (QuotientGroup.mk'_surjective OK)
    rcases Quasisimple.normal_le_center_or_eq_top hKq
      ((N.subgroupOf K).map (QuotientGroup.mk' OK)) with hcent | htop
    · exfalso
      have hLperf : Group.IsPerfect (L₀.subgroupOf K) := by
        have : Group.IsPerfect L₀ := ⟨hL₀⟩
        exact Group.IsPerfect.ofSurjective
          (f := (Subgroup.subgroupOfEquivOfLe hL₀K).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hL₀K).symm.surjective
      have hLperf' : Group.IsPerfect ((L₀.subgroupOf K).map (QuotientGroup.mk' OK)) :=
        Group.IsPerfect.map (QuotientGroup.mk' OK)
      have hLc : (L₀.subgroupOf K).map (QuotientGroup.mk' OK) ≤ Subgroup.center (K ⧸ OK) :=
        le_trans (Subgroup.map_mono fun x hx => le_normalClosureIn K L₀ hx) hcent
      have hbot := Quasisimple.perfect_le_center_eq_bot _ hLc
      have hLO : L₀ ≤ O := by
        intro l hl
        have hmem : (QuotientGroup.mk' OK) (⟨l, hL₀K hl⟩ : K) ∈
            (L₀.subgroupOf K).map (QuotientGroup.mk' OK) := ⟨_, hl, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact ⟨_, (QuotientGroup.eq_one_iff _).mp hmem, rfl⟩
      have hodd : Odd (Nat.card L₀) :=
        (odd_card_oddCoreIn K).of_dvd_nat (Subgroup.card_dvd_of_le hLO)
      exact hL₀ne (eq_bot_of_perfect_of_odd hL₀ hodd)
    · intro k
      have hmem : (QuotientGroup.mk' OK) k ∈ (N.subgroupOf K).map (QuotientGroup.mk' OK) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnk⟩ := hmem
      exact ⟨n, hn, QuotientGroup.eq.mp hnk⟩
  have hKN : K ≤ N := by
    have hNnormal : (N.subgroupOf K).Normal := normal_subgroupOf_normalClosureIn hL₀K
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' (N.subgroupOf K)).comp OK.subtype) := by
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf K) q
      obtain ⟨n, hn, hnk⟩ := hfact k
      refine ⟨⟨n⁻¹ * k, hnk⟩, ?_⟩
      change (QuotientGroup.mk' (N.subgroupOf K)) (n⁻¹ * k) = (QuotientGroup.mk' (N.subgroupOf K)) k
      have h1 : QuotientGroup.mk' (N.subgroupOf K) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [map_mul, map_inv, h1, inv_one, one_mul]
    have hodd : Odd (N.subgroupOf K).index := by
      rw [Subgroup.index_eq_card]
      exact (OddCore.odd_card K).of_dvd_nat (Subgroup.card_dvd_of_surjective hsurj)
    exact Subgroup.subgroupOf_eq_top.mp (eq_top_of_perfect_of_odd_index hKperf _ hodd)
  intro o ho
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (Subgroup.mem_centralizer_iff.mp (hN1 (hKN hk)) o ho).symm

theorem isQuasisimple_of_deltaTrivial {C K E₀ L₀ : Subgroup G}
    (hKC : IsSubnormal K C) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀K : E₀ ≤ K) (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hB : ∀ f ∈ E₀, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f) :
    CFSG.Open.IsQuasisimple K := by
  have hc := oddCoreIn_le_centralizer_of_deltaTrivial hKC hKperf hKq hE₀K hE₀ hE₀card hL₀K hL₀E
    hL₀ hL₀ne hΔ hB
  have : Group.IsPerfect K := ⟨hKperf⟩
  refine CentralExtensions.quasisimple_of_surjective hKq (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) ?_
  rw [QuotientGroup.ker_mk']
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro k
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hc ⟨o, ho, rfl⟩) k k.2)

end StepThree

section Chain

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_of_twoBalancedWrt {A C K E₀ L₀ : Subgroup G} (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hB2 : TwoBalancedWrt A)
    (hO : componentClassificationOddCore G = ⊥) (hGen : FusionGenerated A)
    (hKC : IsSubnormal K C) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀A : E₀ ≤ A) (hE₀K : E₀ ≤ K) (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8)
    (hL₀K : L₀ ≤ K) (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤)
    (hL₀ne : L₀ ≠ ⊥)
    (hB : ∀ f ∈ E₀, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f) :
    CFSG.Open.IsQuasisimple K :=
  isQuasisimple_of_deltaTrivial hKC hKperf hKq hE₀K hE₀ hE₀card hL₀K hL₀E hL₀ hL₀ne
    (fun F hF => deltaCore_eq_bot_of_fusionGenerated hA h16 hB2 hO hGen F ⟨hF.1.trans hE₀A, hF.2⟩)
    hB

end Chain

end CFSG.ClassicalInvolution.Balance
