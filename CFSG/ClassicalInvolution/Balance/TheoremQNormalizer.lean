module

public import CFSG.ClassicalInvolution.Balance.Layer
import CFSG.ClassicalInvolution.LBalance.Main

public section
public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification
open scoped commutatorElement

section Normalizer

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_oddCoreIn_of_mem_normalizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (oddCoreIn K : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ y ∈ oddCoreIn K,
      g * y * g⁻¹ ∈ oddCoreIn K := by
    intro g hg y hy
    set S : Subgroup G := (oddCoreIn K).map (MulAut.conj g).toMonoidHom with hS
    have hmemS : ∀ x, x ∈ S ↔ g⁻¹ * x * g ∈ oddCoreIn K := fun x => by
      rw [hS, Subgroup.mem_map_equiv (f := MulAut.conj g)]
      rfl
    have hSK : S ≤ K := by
      intro x hx
      have hx' : g⁻¹ * x * g ∈ K := oddCoreIn_le K ((hmemS x).mp hx)
      have := (Subgroup.mem_normalizer_iff.mp hg _).mp hx'
      simpa [mul_assoc] using this
    have hSnorm : K ≤ Subgroup.normalizer (S : Set G) := by
      intro k hk
      have hk' : g⁻¹ * k * g ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hg) k).mp
          hk
        simpa using this
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [hmemS, hmemS]
      have e : g⁻¹ * (k * x * k⁻¹) * g =
          (g⁻¹ * k * g) * (g⁻¹ * x * g) * (g⁻¹ * k * g)⁻¹ := by group
      rw [e]
      refine ⟨fun h => conj_mem_oddCoreIn hk' h, fun h => ?_⟩
      have := conj_mem_oddCoreIn (inv_mem hk') h
      simpa [mul_assoc] using this
    have hodd : Odd (Nat.card S) := by
      rw [hS, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact odd_card_oddCoreIn K
    refine le_oddCoreIn_of_normalizes hSK hSnorm hodd ((hmemS _).mpr ?_)
    simpa [mul_assoc] using hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key g hg y hy, fun hy => ?_⟩
  have := key g⁻¹ ((Subgroup.normalizer (K : Set G)).inv_mem hg) _ hy
  simpa [mul_assoc] using this

theorem le_centralizer_oddCoreIn_of_normalizes {C K E₀ L₀ : Subgroup G}
    (hKC : IsSubnormal K C) (hE₀N : E₀ ≤ Subgroup.normalizer (K : Set G))
    (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hB : ∀ f ∈ E₀, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f) :
    L₀ ≤ Subgroup.centralizer (oddCoreIn K : Set G) := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two E₀ (oddCoreIn K) hE₀ (by rw [hE₀card]; norm_num)
    (fun g hg => mem_normalizer_oddCoreIn_of_mem_normalizer (hE₀N hg))
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

theorem oddCoreIn_le_centralizer_of_le_centralizer {K L₀ : Subgroup G} (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K)) (hL₀K : L₀ ≤ K)
    (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (h2 : L₀ ≤ Subgroup.centralizer (oddCoreIn K : Set G)) :
    oddCoreIn K ≤ Subgroup.centralizer (K : Set G) := by
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

omit [Finite G] in
theorem isQuasisimple_of_oddCoreIn_le_centralizer {K : Subgroup G} (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hc : oddCoreIn K ≤ Subgroup.centralizer (K : Set G)) : CFSG.Open.IsQuasisimple K := by
  have : Group.IsPerfect K := ⟨hKperf⟩
  refine CentralExtensions.quasisimple_of_surjective hKq (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) ?_
  rw [QuotientGroup.ker_mk']
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro k
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hc ⟨o, ho, rfl⟩) k k.2)

theorem oddCoreIn_le_centralizer_of_deltaTrivial_of_normalizes {C K E₀ L₀ : Subgroup G}
    (hKC : IsSubnormal K C) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀N : E₀ ≤ Subgroup.normalizer (K : Set G)) (hE₀ : IsElemAbelian 2 E₀)
    (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hB : ∀ f ∈ E₀, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f) :
    oddCoreIn K ≤ Subgroup.centralizer (K : Set G) :=
  oddCoreIn_le_centralizer_of_le_centralizer hKperf hKq hL₀K hL₀ hL₀ne
    (le_centralizer_oddCoreIn_of_normalizes hKC hE₀N hE₀ hE₀card hL₀K hL₀E hL₀ hΔ hB)

theorem isQuasisimple_of_deltaTrivial_of_normalizes {C K E₀ L₀ : Subgroup G}
    (hKC : IsSubnormal K C) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀N : E₀ ≤ Subgroup.normalizer (K : Set G)) (hE₀ : IsElemAbelian 2 E₀)
    (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hB : ∀ f ∈ E₀, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f) :
    CFSG.Open.IsQuasisimple K :=
  isQuasisimple_of_oddCoreIn_le_centralizer hKperf hKq
    (oddCoreIn_le_centralizer_of_deltaTrivial_of_normalizes hKC hKperf hKq hE₀N hE₀ hE₀card hL₀K
      hL₀E hL₀ hL₀ne hΔ hB)

end Normalizer

section TwoComponent

variable {G : Type*} [Group G] [Finite G]

theorem twoComponent_data {C K : Subgroup G} (hKC : K ≤ C)
    (hK : TwoComponents.IsTwoComponent (K.subgroupOf C)) :
    IsSubnormal K C ∧ commutator K = ⊤ ∧
      CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K) := by
  let e : (K.subgroupOf C) ≃* K := Subgroup.subgroupOfEquivOfLe hKC
  refine ⟨(CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hKC).mp hK.1, ?_, ?_⟩
  · have : Group.IsPerfect (K.subgroupOf C) := ⟨TwoComponents.perfect hK⟩
    have : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact Group.IsPerfect.commutator_eq_top
  · have h := OddCore.equiv_invariant e
    exact Components.quasisimple_of_equiv
      (QuotientGroup.congr (componentClassificationOddCore (K.subgroupOf C))
        (componentClassificationOddCore K) e h).symm (TwoComponents.quasisimple_quotient hK)

theorem conj_mem_of_isTwoComponent {C K L₀ : Subgroup G} (hKC : K ≤ C)
    (hK : TwoComponents.IsTwoComponent (K.subgroupOf C)) (hL₀K : L₀ ≤ K)
    (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥) {e : G} (heC : e ∈ C)
    (he : ∀ l ∈ L₀, e * l = l * e) {k : G} (hk : k ∈ K) : e * k * e⁻¹ ∈ K := by
  set c : ↥C := ⟨e, heC⟩ with hc
  set σ : ↥C ≃* ↥C := MulAut.conj c with hσ
  set K₁ : Subgroup ↥C := K.subgroupOf C with hK₁
  set K₂ : Subgroup ↥C := K₁.map σ.toMonoidHom with hK₂
  have hK₂c : TwoComponents.IsTwoComponent K₂ :=
    (TwoComponentTransport.equiv_iff σ K₁).mpr hK
  have hL₀C : L₀ ≤ C := hL₀K.trans hKC
  have hkC : k ∈ C := hKC hk
  have hmem : (⟨k, hkC⟩ : ↥C) ∈ K₁ := Subgroup.mem_subgroupOf.mpr hk
  by_cases heq : K₁ = K₂
  · have h2 : σ ⟨k, hkC⟩ ∈ K₂ := Subgroup.mem_map_of_mem _ hmem
    rw [← heq] at h2
    have h3 := Subgroup.mem_subgroupOf.mp h2
    simpa [hσ, hc] using h3
  · exfalso
    obtain ⟨-, -, hcomm⟩ := TwoComponentInteraction.mutual_normalization_core_commutation K₁ K₂
      hK hK₂c heq
    set L₁ : Subgroup ↥C := L₀.subgroupOf C with hL₁
    have hL₁K₁ : L₁ ≤ K₁ := fun x hx => hL₀K hx
    have hL₁K₂ : L₁ ≤ K₂ := by
      intro x hx
      have hxK₁ : x ∈ K₁ := hL₁K₁ hx
      have hfix : σ x = x := by
        apply Subtype.ext
        have hx' : (x : G) ∈ L₀ := Subgroup.mem_subgroupOf.mp hx
        change e * (x : G) * e⁻¹ = x
        rw [he _ hx', mul_assoc, mul_inv_cancel, mul_one]
      rw [← hfix]
      exact Subgroup.mem_map_of_mem _ hxK₁
    have hperf : Group.IsPerfect L₁ := by
      have : Group.IsPerfect L₀ := ⟨hL₀⟩
      exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hL₀C).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hL₀C).symm.surjective
    have hself : ⁅L₁, L₁⁆ = L₁ := Subgroup.commutator_eq_self
    have hle : L₁ ≤ (componentClassificationOddCore K₁).map K₁.subtype := by
      calc L₁ = ⁅L₁, L₁⁆ := hself.symm
        _ ≤ ⁅K₁, K₂⁆ := Subgroup.commutator_mono hL₁K₁ hL₁K₂
        _ ≤ _ := hcomm.trans inf_le_left
    have hodd : Odd (Nat.card L₁) := by
      have h1 : Odd (Nat.card ((componentClassificationOddCore K₁).map K₁.subtype)) := by
        rw [Subgroup.card_map_of_injective K₁.subtype_injective]
        exact OddCore.odd_card K₁
      exact h1.of_dvd_nat (Subgroup.card_dvd_of_le hle)
    have hbot : L₁ = ⊥ := eq_bot_of_perfect_of_odd (Group.IsPerfect.commutator_eq_top) hodd
    apply hL₀ne
    rw [eq_bot_iff]
    intro x hx
    have hxL₁ : (⟨x, hL₀C hx⟩ : ↥C) ∈ L₁ := Subgroup.mem_subgroupOf.mpr hx
    rw [hbot, Subgroup.mem_bot] at hxL₁
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxL₁)

theorem le_normalizer_of_isTwoComponent {C K E₀ L₀ : Subgroup G} (hKC : K ≤ C)
    (hK : TwoComponents.IsTwoComponent (K.subgroupOf C)) (hL₀K : L₀ ≤ K)
    (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥) (hE₀C : E₀ ≤ C)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) :
    E₀ ≤ Subgroup.normalizer (K : Set G) := by
  intro e he
  have hcent : ∀ x ∈ E₀, ∀ l ∈ L₀, x * l = l * x := fun x hx l hl =>
    (Subgroup.mem_centralizer_iff.mp (hL₀E hl) x hx)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_of_isTwoComponent hKC hK hL₀K hL₀ hL₀ne (hE₀C he)
    (hcent e he) hh, fun hh => ?_⟩
  have := conj_mem_of_isTwoComponent hKC hK hL₀K hL₀ hL₀ne (hE₀C (E₀.inv_mem he))
    (hcent e⁻¹ (E₀.inv_mem he)) hh
  simpa [mul_assoc] using this

theorem isQuasisimple_of_isTwoComponent_of_deltaTrivial_of_centralizes {C K E₀ L₀ : Subgroup G}
    (hKC : K ≤ C) (hK : TwoComponents.IsTwoComponent (K.subgroupOf C)) (hE₀C : E₀ ≤ C)
    (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hB : ∀ f ∈ E₀, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f) :
    CFSG.Open.IsQuasisimple K := by
  obtain ⟨hKsub, hKperf, hKq⟩ := twoComponent_data hKC hK
  exact isQuasisimple_of_deltaTrivial_of_normalizes hKsub hKperf hKq
    (le_normalizer_of_isTwoComponent hKC hK hL₀K hL₀ hL₀ne hE₀C hL₀E) hE₀ hE₀card hL₀K hL₀E hL₀
    hL₀ne hΔ hB

theorem isQuasisimple_of_deltaTrivial_of_image_of_normalizes {C K E₀ L₀ : Subgroup G}
    (hKC : IsSubnormal K C) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀N : E₀ ≤ Subgroup.normalizer (K : Set G)) (hE₀ : IsElemAbelian 2 E₀)
    (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hB : ∀ f ∈ E₀, f ≠ 1 → ∃ P : Subgroup G,
      normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀ ≤ P ∧ P ≤ C ⊓ Subgroup.centralizer {f} ∧
        componentClassificationOddCore ((P.subgroupOf (Subgroup.centralizer {f})).map
            (QuotientGroup.mk' (componentClassificationOddCore (Subgroup.centralizer {f})))) ≤
          Subgroup.center ((P.subgroupOf (Subgroup.centralizer {f})).map
            (QuotientGroup.mk' (componentClassificationOddCore (Subgroup.centralizer {f}))))) :
    CFSG.Open.IsQuasisimple K := by
  refine isQuasisimple_of_deltaTrivial_of_normalizes hKC hKperf hKq hE₀N hE₀ hE₀card hL₀K hL₀E hL₀
    hL₀ne hΔ fun f hf hf1 => ?_
  obtain ⟨P, hLP, hPH, hc⟩ := hB f hf hf1
  exact commutator_oddCoreIn_normalClosureIn_le_of_le hLP hPH
    (commutator_oddCoreIn_le_of_oddCore_map_le_center (hPH.trans inf_le_right) hc)

end TwoComponent

section Chain

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem deltaCore_eq_bot_of_le {A E₀ : Subgroup G}
    (hE₀A : E₀ ≤ A) (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥) :
    ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥ :=
  fun F hF => hΔ F ⟨hF.1.trans hE₀A, hF.2⟩

theorem isQuasisimple_of_twoBalancedWrt_of_normalizes {A C K E₀ L₀ : Subgroup G}
    (hA : IsElemAbelian 2 A) (h16 : 16 ≤ Nat.card A) (hB2 : TwoBalancedWrt A)
    (hO : componentClassificationOddCore G = ⊥) (hGen : FusionGenerated A)
    (hKC : IsSubnormal K C) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀A : E₀ ≤ A) (hE₀N : E₀ ≤ Subgroup.normalizer (K : Set G))
    (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hB : ∀ f ∈ E₀, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f) :
    CFSG.Open.IsQuasisimple K :=
  isQuasisimple_of_deltaTrivial_of_normalizes hKC hKperf hKq hE₀N
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hA hE₀A) hE₀card hL₀K hL₀E hL₀
    hL₀ne (deltaCore_eq_bot_of_le hE₀A
      (fun F hF => deltaCore_eq_bot_of_fusionGenerated hA h16 hB2 hO hGen F hF)) hB

theorem isQuasisimple_of_isTwoComponent_of_twoBalancedWrt_of_centralizes
    {A C K E₀ L₀ : Subgroup G}
    (hA : IsElemAbelian 2 A) (h16 : 16 ≤ Nat.card A) (hB2 : TwoBalancedWrt A)
    (hO : componentClassificationOddCore G = ⊥) (hGen : FusionGenerated A)
    (hKC : K ≤ C) (hK : TwoComponents.IsTwoComponent (K.subgroupOf C))
    (hE₀A : E₀ ≤ A) (hE₀C : E₀ ≤ C)
    (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hB : ∀ f ∈ E₀, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f) :
    CFSG.Open.IsQuasisimple K :=
  isQuasisimple_of_isTwoComponent_of_deltaTrivial_of_centralizes hKC hK hE₀C
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hA hE₀A) hE₀card hL₀K hL₀E hL₀
    hL₀ne (deltaCore_eq_bot_of_le hE₀A
      (fun F hF => deltaCore_eq_bot_of_fusionGenerated hA h16 hB2 hO hGen F hF)) hB

end Chain

section Layer

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_of_deltaTrivial_of_l2PrimeBalance_of_normalizes (hLB : L2PrimeBalance)
    {C K E₀ L₀ : Subgroup G} (hKC : IsSubnormal K C) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀N : E₀ ≤ Subgroup.normalizer (K : Set G)) (hE₀C : E₀ ≤ C) (hE₀ : IsElemAbelian 2 E₀)
    (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hL₀sub : IsSubnormal L₀ (C ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hL₀q : CFSG.Open.IsQuasisimple (L₀ ⧸ componentClassificationOddCore L₀))
    (hB : ∀ f ∈ E₀, f ≠ 1 → ∀ M : Subgroup ↥(imageModOddCore f (C ⊓ Subgroup.centralizer {f})),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M ∨
        ⁅M.map (imageModOddCore f (C ⊓ Subgroup.centralizer {f})).subtype,
          imageModOddCore f L₀⁆ = ⊥) :
    CFSG.Open.IsQuasisimple K := by
  have hKC' : K ≤ C := isSubnormal_le hKC
  refine isQuasisimple_of_deltaTrivial_of_normalizes hKC hKperf hKq hE₀N hE₀ hE₀card hL₀K hL₀E hL₀
    hL₀ne hΔ fun f hf hf1 => ?_
  exact commutator_oddCoreIn_normalClosureIn_le_of_l2PrimeBalance hLB hE₀ hf hE₀C
    (le_inf (hL₀K.trans hKC') hL₀E) hL₀sub hL₀ hL₀q (hB f hf hf1)

theorem isQuasisimple_of_deltaTrivial_of_kGroup_of_normalizes (hLB : L2PrimeBalance)
    {C K E₀ L₀ : Subgroup G} (hKC : IsSubnormal K C) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀N : E₀ ≤ Subgroup.normalizer (K : Set G)) (hE₀C : E₀ ≤ C) (hE₀ : IsElemAbelian 2 E₀)
    (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hL₀sub : IsSubnormal L₀ (C ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hL₀q : CFSG.Open.IsQuasisimple (L₀ ⧸ componentClassificationOddCore L₀))
    (hB : ∀ f ∈ E₀, f ≠ 1 → ∀ M : Subgroup ↥(imageModOddCore f (C ⊓ Subgroup.centralizer {f})),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M) :
    CFSG.Open.IsQuasisimple K :=
  isQuasisimple_of_deltaTrivial_of_l2PrimeBalance_of_normalizes hLB hKC hKperf hKq hE₀N hE₀C hE₀
    hE₀card hL₀K hL₀E hL₀ hL₀ne hΔ hL₀sub hL₀q fun f hf hf1 M hM => Or.inl (hB f hf hf1 M hM)

theorem isQuasisimple_of_deltaTrivial_of_layer_of_normalizes
    {C K E₀ L₀ : Subgroup G} (hKC : IsSubnormal K C) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀N : E₀ ≤ Subgroup.normalizer (K : Set G)) (hE₀C : E₀ ≤ C) (hE₀ : IsElemAbelian 2 E₀)
    (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hL₀sub : IsSubnormal L₀ (C ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hL₀q : CFSG.Open.IsQuasisimple (L₀ ⧸ componentClassificationOddCore L₀))
    (hB : ∀ f ∈ E₀, f ≠ 1 → ∀ M : Subgroup ↥(imageModOddCore f (C ⊓ Subgroup.centralizer {f})),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M ∨
        ⁅M.map (imageModOddCore f (C ⊓ Subgroup.centralizer {f})).subtype,
          imageModOddCore f L₀⁆ = ⊥) :
    CFSG.Open.IsQuasisimple K :=
  isQuasisimple_of_deltaTrivial_of_l2PrimeBalance_of_normalizes l2PrimeBalance hKC hKperf hKq hE₀N
    hE₀C hE₀ hE₀card hL₀K hL₀E hL₀ hL₀ne hΔ hL₀sub hL₀q hB

theorem isQuasisimple_of_isTwoComponent_of_layer_of_centralizes
    {C K E₀ L₀ : Subgroup G} (hKC : K ≤ C) (hK : TwoComponents.IsTwoComponent (K.subgroupOf C))
    (hE₀C : E₀ ≤ C) (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hL₀sub : IsSubnormal L₀ (C ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hL₀q : CFSG.Open.IsQuasisimple (L₀ ⧸ componentClassificationOddCore L₀))
    (hB : ∀ f ∈ E₀, f ≠ 1 → ∀ M : Subgroup ↥(imageModOddCore f (C ⊓ Subgroup.centralizer {f})),
      TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M ∨
        ⁅M.map (imageModOddCore f (C ⊓ Subgroup.centralizer {f})).subtype,
          imageModOddCore f L₀⁆ = ⊥) :
    CFSG.Open.IsQuasisimple K := by
  obtain ⟨hKsub, hKperf, hKq⟩ := twoComponent_data hKC hK
  exact isQuasisimple_of_deltaTrivial_of_layer_of_normalizes hKsub hKperf hKq
    (le_normalizer_of_isTwoComponent hKC hK hL₀K hL₀ hL₀ne hE₀C hL₀E) hE₀C hE₀ hE₀card hL₀K hL₀E
    hL₀ hL₀ne hΔ hL₀sub hL₀q hB

theorem isQuasisimple_of_deltaTrivial_of_bInclusion_of_normalizes
    {K E₀ L₀ : Subgroup G} {z₀ : G} (hz₀E : z₀ ∈ E₀) (hz₀ : z₀ ≠ 1)
    (hKC : IsSubnormal K (Subgroup.centralizer {z₀})) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀N : E₀ ≤ Subgroup.normalizer (K : Set G)) (hE₀ : IsElemAbelian 2 E₀)
    (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hL₀sub : IsSubnormal L₀ (Subgroup.centralizer {z₀} ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hL₀q : CFSG.Open.IsQuasisimple (L₀ ⧸ componentClassificationOddCore L₀))
    (hinc : ∀ f ∈ E₀, f ≠ 1 → CentralTwoBInclusion.Property (↥(Subgroup.centralizer {f}) ⧸
      componentClassificationOddCore ↥(Subgroup.centralizer {f}))) :
    CFSG.Open.IsQuasisimple K :=
  isQuasisimple_of_deltaTrivial_of_kGroup_of_normalizes l2PrimeBalance hKC hKperf hKq hE₀N
    (fun _ he => mem_centralizer_singleton_of_isElemAbelian hE₀ hz₀E he) hE₀ hE₀card hL₀K hL₀E hL₀
    hL₀ne hΔ hL₀sub hL₀q fun f hf hf1 M hM =>
      isQuasisimple_imageModOddCore_of_bInclusion (mem_centralizer_singleton_of_isElemAbelian hE₀
        hf hz₀E) (orderOf_eq_prime (hE₀.2 z₀ hz₀E) hz₀) (hinc f hf hf1) M hM

theorem isQuasisimple_of_isTwoComponent_of_bInclusion_of_centralizes
    {K E₀ L₀ : Subgroup G} {z₀ : G} (hz₀E : z₀ ∈ E₀) (hz₀ : z₀ ≠ 1)
    (hKC : K ≤ Subgroup.centralizer {z₀})
    (hK : TwoComponents.IsTwoComponent (K.subgroupOf (Subgroup.centralizer {z₀})))
    (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hL₀sub : IsSubnormal L₀ (Subgroup.centralizer {z₀} ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hL₀q : CFSG.Open.IsQuasisimple (L₀ ⧸ componentClassificationOddCore L₀))
    (hinc : ∀ f ∈ E₀, f ≠ 1 → CentralTwoBInclusion.Property (↥(Subgroup.centralizer {f}) ⧸
      componentClassificationOddCore ↥(Subgroup.centralizer {f}))) :
    CFSG.Open.IsQuasisimple K := by
  obtain ⟨hKsub, hKperf, hKq⟩ := twoComponent_data hKC hK
  exact isQuasisimple_of_deltaTrivial_of_bInclusion_of_normalizes hz₀E hz₀ hKsub hKperf hKq
    (le_normalizer_of_isTwoComponent hKC hK hL₀K hL₀ hL₀ne
      (fun _ he => mem_centralizer_singleton_of_isElemAbelian hE₀ hz₀E he) hL₀E) hE₀ hE₀card hL₀K
    hL₀E hL₀ hL₀ne hΔ hL₀sub hL₀q hinc

end Layer

end CFSG.ClassicalInvolution.Balance
