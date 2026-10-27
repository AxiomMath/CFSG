module

public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Transport

variable {G : Type*} [Group G]

theorem isQuasisimple_of_simple_perfect {H : Type*} [Group H] [IsSimpleGroup H]
    (hperf : commutator H = ⊤) : CFSG.Open.IsQuasisimple H := by
  refine ⟨hperf, ?_⟩
  have hc : Subgroup.center H = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
    · exact h
    · exfalso
      have h1 : commutator H = ⊥ := by
        rw [commutator, eq_bot_iff, Subgroup.commutator_le]
        intro a _ b _
        have : a ∈ Subgroup.center H := h ▸ Subgroup.mem_top a
        have hab : b * a = a * b := Subgroup.mem_center_iff.1 this b
        rw [Subgroup.mem_bot, commutatorElement_def, ← hab]
        group
      obtain ⟨x, hx⟩ := exists_ne (1 : H)
      have hx' : x ∈ commutator H := by rw [hperf]; exact Subgroup.mem_top x
      rw [h1, Subgroup.mem_bot] at hx'
      exact hx hx'
  exact MulEquiv.isSimpleGroup
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)

theorem eq_of_isSubnormal_of_simple {K N : Subgroup G} [IsSimpleGroup ↥N]
    (h : IsSubnormal K N) (hK : K ≠ ⊥) : K = N := by
  by_contra hne
  obtain ⟨M, hKM, hMN, hMne, hn, _⟩ := isSubnormal_exists_normal h hne
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf N) with h1 | h1
  · have hM : M = ⊥ := (Subgroup.subgroupOf_eq_bot.1 h1).eq_bot_of_le hMN
    exact hK (le_bot_iff.1 (hM ▸ hKM))
  · exact hMne (le_antisymm hMN (Subgroup.subgroupOf_eq_top.1 h1))

variable [Finite G]

theorem inf_primeCore_eq_one {p : ℕ} (hp : p.Prime) {C N : Subgroup G} (hNC : N ≤ C)
    (hs : IsSimpleGroup ↥N) (hdvd : p ∣ Nat.card N) {x : ↥C}
    (hx : x ∈ N.subgroupOf C) (hxO : x ∈ GLAPPrimeCore p ↥C) : x = 1 := by
  have : IsSimpleGroup ↥(N.subgroupOf C) :=
    MulEquiv.isSimpleGroup (Subgroup.subgroupOfEquivOfLe hNC)
  have hnorm : ((GLAPPrimeCore p ↥C).subgroupOf (N.subgroupOf C)).Normal :=
    inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((GLAPPrimeCore p ↥C).subgroupOf (N.subgroupOf C)) with h | h
  · have hmem : (⟨x, hx⟩ : ↥(N.subgroupOf C)) ∈
        (GLAPPrimeCore p ↥C).subgroupOf (N.subgroupOf C) := hxO
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    have hle : N.subgroupOf C ≤ GLAPPrimeCore p ↥C := Subgroup.subgroupOf_eq_top.1 h
    have h1 : p ∣ Nat.card (GLAPPrimeCore p ↥C) := by
      refine (?_ : p ∣ Nat.card (N.subgroupOf C)).trans (Subgroup.card_dvd_of_le hle)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
    apply not_dvd_card_glaPPrimeCoreOf hp C
    unfold GLAPPrimeCoreOf
    rwa [Subgroup.card_map_of_injective C.subtype_injective]

theorem glaPLayer_eq_of_central_product {p : ℕ} (hp : p.Prime) {C N : Subgroup G}
    (hs : IsSimpleGroup ↥N) (hperf : ⁅N, N⁆ = N) (hNC : N ≤ C) (hdvd : p ∣ Nat.card N)
    (hCN : ∀ c ∈ C, ∃ n ∈ N, ∃ y : G, (∀ d ∈ C, y * d = d * y) ∧ c = n * y) :
    GLAPLayer p C = N := by
  have hnorm : (N.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNC]
    intro n c hn hc
    obtain ⟨m, hm, y, hy, rfl⟩ := hCN c hc
    have h1 : y * n * y⁻¹ = n := by rw [hy n (hNC hn)]; group
    have h2 : m * y * n * (m * y)⁻¹ = m * n * m⁻¹ := by
      calc m * y * n * (m * y)⁻¹ = m * (y * n * y⁻¹) * m⁻¹ := by group
        _ = m * n * m⁻¹ := by rw [h1]
    rw [h2]
    exact N.mul_mem (N.mul_mem hm hn) (N.inv_mem hm)
  have hcomm : ⁅C, C⁆ ≤ N := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨m, hm, y, hy, rfl⟩ := hCN a ha
    obtain ⟨m', hm', y', hy', rfl⟩ := hCN b hb
    have hyb : y * (m' * y') = (m' * y') * y := hy _ hb
    have hy'm : y' * m⁻¹ = m⁻¹ * y' := by
      have := hy' m (hNC hm)
      calc y' * m⁻¹ = m⁻¹ * (m * y') * m⁻¹ := by group
        _ = m⁻¹ * (y' * m) * m⁻¹ := by rw [this]
        _ = m⁻¹ * y' := by group
    have k1 : y * (m' * y') * y⁻¹ = m' * y' := by rw [hyb]; group
    have k2 : y' * m⁻¹ * y'⁻¹ = m⁻¹ := by rw [hy'm]; group
    rw [commutatorElement_def]
    have h3 : m * y * (m' * y') * (m * y)⁻¹ * (m' * y')⁻¹ = m * m' * m⁻¹ * m'⁻¹ := by
      calc m * y * (m' * y') * (m * y)⁻¹ * (m' * y')⁻¹
          = m * (y * (m' * y') * y⁻¹) * m⁻¹ * (m' * y')⁻¹ := by group
        _ = m * (m' * y') * m⁻¹ * (m' * y')⁻¹ := by rw [k1]
        _ = m * m' * (y' * m⁻¹ * y'⁻¹) * m'⁻¹ := by group
        _ = m * m' * m⁻¹ * m'⁻¹ := by rw [k2]
    rw [h3]
    exact N.mul_mem (N.mul_mem (N.mul_mem hm hm') (N.inv_mem hm)) (N.inv_mem hm')
  have hperfN : commutator ↥N = ⊤ := by
    have h := Subgroup.isPerfect_iff.2 hperf
    exact h.1
  have hqN : CFSG.Open.IsQuasisimple ↥N := isQuasisimple_of_simple_perfect hperfN
  have hker := fun x (hx : x ∈ N.subgroupOf C) (hxO : x ∈ GLAPPrimeCore p ↥C) =>
    inf_primeCore_eq_one hp hNC hs hdvd hx hxO
  have hcompN : GLAPComponent p C N := by
    set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
    have hinj : Function.Injective (π.comp (N.subgroupOf C).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have h1 : π (x : ↥C) = 1 := hx
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have := hker x.1 x.2 h1
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    have hrange : (π.comp (N.subgroupOf C).subtype).range = barX p C N := by
      ext z
      simp only [MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype, barX, Subgroup.mem_map]
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨x.1, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
    let e : ↥(N.subgroupOf C) ≃* ↥(barX p C N) :=
      (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
    have hqN' : CFSG.Open.IsQuasisimple ↥(N.subgroupOf C) :=
      CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (Subgroup.subgroupOfEquivOfLe hNC) hqN
    refine ⟨hNC, IsSubnormal.step hNC hnorm (IsSubnormal.refl C), ⟨le_top, ?_, ?_⟩, ?_⟩
    · have hn : (barX p C N).Normal := by
        have := hnorm.map π (QuotientGroup.mk'_surjective _)
        exact this
      exact IsSubnormal.step le_top (hn.subgroupOf ⊤) (IsSubnormal.refl ⊤)
    · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm hqN'
    · intro J hJ _ hbar
      apply hJ.not_ge
      intro n hn
      have hn' : (⟨n, hNC hn⟩ : ↥C) ∈ N.subgroupOf C := hn
      have h1 : π ⟨n, hNC hn⟩ ∈ Subgroup.map π (N.subgroupOf C) := ⟨_, hn', rfl⟩
      rw [← hbar] at h1
      obtain ⟨j, hj, hjn⟩ := h1
      have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.1 hj
      have hjN : j ∈ N.subgroupOf C := Subgroup.mem_subgroupOf.2 (hJ.le hjJ)
      have h2 : j⁻¹ * ⟨n, hNC hn⟩ ∈ GLAPPrimeCore p ↥C := QuotientGroup.eq.1 hjn
      have h3 := hker (j⁻¹ * ⟨n, hNC hn⟩) ((N.subgroupOf C).mul_mem
        ((N.subgroupOf C).inv_mem hjN) hn') h2
      have h4 : j = ⟨n, hNC hn⟩ := inv_mul_eq_one.1 h3
      rw [h4] at hjJ
      exact hjJ
  have huniq : ∀ K, GLAPComponent p C K → K = N := by
    intro K hK
    have hKC : K ≤ C := hK.1
    have hKN : K ≤ N := by
      calc K = ⁅K, K⁆ := (glaPComponent_perfect hK).symm
        _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hKC hKC
        _ ≤ N := hcomm
    have hKne : K ≠ ⊥ := by
      intro hKb
      have hnt : Nontrivial (barX p C K) :=
        CFSG.ComponentClassification.Quasisimple.nontrivial hK.2.2.1.2.2
      apply (Subgroup.nontrivial_iff_ne_bot _).1 hnt
      rw [hKb]
      unfold barX
      rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
    exact eq_of_isSubnormal_of_simple (isSubnormal_of_le_of_le hK.2.1 hKN hNC) hKne
  have hset : {K | GLAPComponent p C K} = {N} := by
    ext K
    exact ⟨fun h => huniq K h, fun h => by rw [Set.mem_singleton_iff.1 h]; exact hcompN⟩
  unfold GLAPLayer
  rw [hset, sSup_singleton]

end Transport

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
