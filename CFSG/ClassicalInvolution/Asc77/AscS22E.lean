module

public import CFSG.ClassicalInvolution.Asc77.AscS22D
public import CFSG.ClassicalInvolution.Asc77.AscT7S22Sigma

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S22

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

section Const

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)}

theorem const_on_family (h2 : C22_2S p f) {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}
    (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hb : Big Ω K)
    {M₀ : Set (Subgroup G)} (hM₀ : M₀ ⊆ twinSet Ω K) (hKM : K ∈ M₀) (hK'M : K' ∈ M₀)
    (hK₃M : K₃ ∈ M₀) {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hSyl : ∀ M ∈ M₀, IsSylow2In (Q ⊓ M) M) :
    ∀ M₁ ∈ M₀, ∀ M₂ ∈ M₀, ∀ N₁ ∈ M₀, ∀ N₂ ∈ M₀, M₁ ≠ M₂ → N₁ ≠ N₂ →
      ∀ x ∈ Q ⊓ M₁, ∀ y ∈ Q ⊓ M₂, ∀ x' ∈ Q ⊓ N₁, ∀ y' ∈ Q ⊓ N₂,
        orderOf x = 4 → orderOf y = 4 → orderOf x' = 4 → orderOf y' = 4 →
        alphaOf (Subgroup.closure ({x * y, z} : Set G)) =
          alphaOf (Subgroup.closure ({x' * y', z} : Set G)) := by
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hp : p ≠ 2 := h.stand.odd
  have hq : 5 ≤ p ^ f := h.stand.five
  have hz : IsUniqueInvolution K z := h.hz
  have hKe : K' ≠ K := h.hne
  have hzM : ∀ M ∈ M₀, IsUniqueInvolution M z := fun M hM =>
    isUniqueInvolution_of_mem_twinSet hz (hM₀ hM)
  have hcomm : ∀ M ∈ M₀, ∀ M' ∈ M₀, M ≠ M' → Commutes (Q ⊓ M) (Q ⊓ M') := by
    intro M hM M' hM' hne
    exact hΩ.commutes_of_twin_of_isPGroup (hM₀ hM).1 (hM₀ hM').1 hne (hzM M hM) (hzM M' hM')
      inf_le_right inf_le_right
      (hQ.to_le (sup_le inf_le_left inf_le_left))
  let E : Type := Subgroup G × G
  let valid : E → Prop := fun a => a.1 ∈ M₀ ∧ a.2 ∈ Q ⊓ a.1 ∧ orderOf a.2 = 4
  let F : E → E → Subgroup G := fun a b => alphaOf (Subgroup.closure ({a.2 * b.2, z} : Set G))
  have key := T7B.const_of_triple (m := fun a : E => a.1) valid F
    (by
      intro a b ha hb' hne
      show alphaOf _ = alphaOf _
      rw [hcomm a.1 ha.1 b.1 hb'.1 hne a.2 ha.2.1 b.2 hb'.2.1])
    (by
      intro a b c ha hb' hc hab hbc hac
      have hLa : a.1 ∈ twinSet Ω K := hM₀ ha.1
      have hLb : b.1 ∈ twinSet Ω K := hM₀ hb'.1
      have hLc : c.1 ∈ twinSet Ω K := hM₀ hc.1
      have hperp' : KPerp Ω a.1 = twinSet Ω a.1 := T7S22.perp_of_twin h hLa
      have hLb' : b.1 ∈ twinSet Ω a.1 := by
        rw [twinSet_eq_of_mem_twinSet hz hLa]; exact hLb
      have hLc' : c.1 ∈ twinSet Ω a.1 := by
        rw [twinSet_eq_of_mem_twinSet hz hLa]; exact hLc
      have hd := hyp22Setting_of_sylows (h.stand.of_mem hLa.1)
        (isUniqueInvolution_of_mem_twinSet hz hLa) hLb' (Ne.symm hab) hperp' hLc' (Ne.symm hac)
        (Ne.symm hbc) (hSyl a.1 ha.1) (hSyl b.1 hb'.1) (hSyl c.1 hc.1)
        (hcomm a.1 ha.1 b.1 hb'.1 hab) (hcomm a.1 ha.1 c.1 hc.1 hac)
        (hcomm b.1 hb'.1 c.1 hc.1 hbc) ha.2.1 hb'.2.1 hc.2.1 ha.2.2 hb'.2.2 hc.2.2
      exact (alpha_23 h2 hd (hb.of_twin hz hLa)).symm)
    (by
      intro a b ha hb'
      obtain ⟨M, hM, hMa, hMb⟩ : ∃ M ∈ M₀, M ≠ a.1 ∧ M ≠ b.1 := by
        rcases T7B.exists_ne_of_three (a := a.1) (b := b.1) hKe h.hK₃K h.hK₃K' with h | h | h
        · exact ⟨K, hKM, h.1, h.2⟩
        · exact ⟨K', hK'M, h.1, h.2⟩
        · exact ⟨K₃, hK₃M, h.1, h.2⟩
      obtain ⟨w, hw, o⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hp
        (mem_RSet_of_isSylow2In (hM₀ hM).1 (hSyl M hM))
      exact ⟨(M, w), ⟨hM, hw, o⟩, hMa, hMb⟩)
  intro M₁ hM₁ M₂ hM₂ N₁ hN₁ N₂ hN₂ hne hne' x hx y hy x' hx' y' hy' ox oy ox' oy'
  exact key (M₁, x) (M₂, y) (N₁, x') (N₂, y') ⟨hM₁, hx, ox⟩ ⟨hM₂, hy, oy⟩ ⟨hN₁, hx', ox'⟩
    ⟨hN₂, hy', oy'⟩ hne hne'

end Const

section Alpha

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)}

theorem alpha_eq_of_datum (h2 : C22_2S p f) {K K' K₃ L L' L₃ : Subgroup G}
    {z u₁ u₂ u₃ x₁ x₂ x₃ : G} (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (h' : Hyp22Setting p f Ω L L' L₃ z x₁ x₂ x₃) (hb : Big Ω K) :
    alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) =
      alphaOf (Subgroup.closure ({x₁ * x₂, z} : Set G)) := by
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hz : IsUniqueInvolution K z := h.hz
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self h.stand.mem hz
  have hK'V : K' ∈ twinSet Ω K := h.hK'
  have hK₃V : K₃ ∈ twinSet Ω K := h.hK₃
  have hLV : L ∈ twinSet Ω K := ⟨h'.stand.mem, z, hz, h'.hz⟩
  have hL'V : L' ∈ twinSet Ω K := ⟨h'.hK'.1, z, hz, h'.hzK'⟩
  have hL₃V : L₃ ∈ twinSet Ω K := ⟨h'.hK₃.1, z, hz, h'.hzK₃⟩
  have hVL : twinSet Ω L = twinSet Ω K := twinSet_eq_of_mem_twinSet hz hLV
  have hbL : Big Ω L := hb.of_twin hz hLV
  set X : Subgroup G := ⨆ M ∈ twinSet Ω K, M with hX
  have hXM : ∀ M ∈ twinSet Ω K, M ≤ X := fun M hM => le_iSup₂_of_le M hM le_rfl
  have hzV : ∀ M ∈ twinSet Ω K, IsUniqueInvolution M z := fun M hM =>
    isUniqueInvolution_of_mem_twinSet hz hM
  have hXz : X ≤ Subgroup.centralizer ({z} : Set G) := iSup₂_le fun M hM m hm =>
    Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem (hzV M hM) hm).symm
  have hXN : ∀ M ∈ twinSet Ω K, X ≤ Subgroup.normalizer (M : Set G) := by
    intro M hM
    refine iSup₂_le fun M' hM' => ?_
    by_cases hMM : M' = M
    · rw [hMM]
      exact Subgroup.le_normalizer
    · exact hΩ.le_normalizer_of_twin hM'.1 hM.1 hMM (hzV M' hM') (hzV M hM)
  have hXα : X ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
    iSup₂_le fun M hM => twin_le_normalizer_alpha h2 h hb hM
  have hXα' : X ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({x₁ * x₂, z} : Set G)) : Set G) :=
    iSup₂_le fun M hM => twin_le_normalizer_alpha h2 h' hbL (by rw [hVL]; exact hM)
  obtain ⟨R, R', R₃, hR, hR', hR₃, h₁, h₂, h₃, c12, c13, c23⟩ := T7J.exists_sylow_triple h
  obtain ⟨S, S', S₃, hS, hS', hS₃, k₁, k₂, k₃, d12, d13, d23⟩ := T7J.exists_sylow_triple h'
  have hT2 := T7B.isPGroup_sup_three hR.2.1 hR'.2.1 hR₃.2.1 c12 c13 c23
  have hT2' := T7B.isPGroup_sup_three hS.2.1 hS'.2.1 hS₃.2.1 d12 d13 d23
  obtain ⟨Q, hQ, hTQ⟩ := IsSylow2In.exists_ge hT2
    (sup_le (sup_le (hR.1.trans (hXM K hKV)) (hR'.1.trans (hXM K' hK'V)))
      (hR₃.1.trans (hXM K₃ hK₃V)))
  obtain ⟨Q', hQ', hTQ'⟩ := IsSylow2In.exists_ge hT2'
    (sup_le (sup_le (hS.1.trans (hXM L hLV)) (hS'.1.trans (hXM L' hL'V)))
      (hS₃.1.trans (hXM L₃ hL₃V)))
  obtain ⟨g, hgX, hgQ⟩ := exists_conjSub_eq_of_isSylow2In hQ' hQ
  have hgz : g * z * g⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hXz hgX)
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [this]
      _ = z := by group
  have hgM : ∀ M ∈ twinSet Ω K, conjSub g M = M := fun M hM =>
    mem_normalizer_iff_conjSub_eq.mp (hXN M hM hgX)
  have h'' := conj h' hgz
  rw [hgM L hLV, hgM L' hL'V, hgM L₃ hL₃V] at h''
  have hαg : alphaOf (Subgroup.closure ({(g * x₁ * g⁻¹) * (g * x₂ * g⁻¹), z} : Set G)) =
      alphaOf (Subgroup.closure ({x₁ * x₂, z} : Set G)) := by
    have e : (g * x₁ * g⁻¹) * (g * x₂ * g⁻¹) = g * (x₁ * x₂) * g⁻¹ := by group
    have e2 := T7A.conjSub_closure_pair g (x₁ * x₂) z
    rw [hgz] at e2
    rw [e, ← e2, alphaOf_conjSub]
    exact mem_normalizer_iff_conjSub_eq.mp (hXα' hgX)
  have hQ2 : IsPGroup 2 ↥Q := hQ.2.1
  have hSylK : ∀ {M R₀ : Subgroup G}, IsSylow2In R₀ M → R₀ ≤ Q → IsSylow2In (Q ⊓ M) M := by
    intro M R₀ hR₀ hRQ
    have : Q ⊓ M = R₀ := hR₀.eq_of_le (hQ2.to_le inf_le_left) inf_le_right (le_inf hRQ hR₀.1)
    rw [this]
    exact hR₀
  have hSylL : ∀ {M R₀ : Subgroup G}, M ∈ twinSet Ω K → IsSylow2In R₀ M → R₀ ≤ Q' →
      IsSylow2In (conjSub g R₀) M ∧ conjSub g R₀ ≤ Q ⊓ M := by
    intro M R₀ hM hR₀ hRQ
    have h1 : IsSylow2In (conjSub g R₀) M := by
      have := hR₀.conj g
      rwa [hgM M hM] at this
    refine ⟨h1, le_inf ?_ h1.1⟩
    rw [← hgQ]
    exact conjSub_mono hRQ
  have hQL : ∀ {M R₀ : Subgroup G}, M ∈ twinSet Ω K → IsSylow2In R₀ M → R₀ ≤ Q' →
      IsSylow2In (Q ⊓ M) M := by
    intro M R₀ hM hR₀ hRQ
    obtain ⟨h1, h2'⟩ := hSylL hM hR₀ hRQ
    have : Q ⊓ M = conjSub g R₀ :=
      h1.eq_of_le (hQ2.to_le inf_le_left) inf_le_right h2'
    rw [this]
    exact h1
  have hRQ : ∀ {M₁ : Subgroup G}, M₁ ≤ (R ⊔ R') ⊔ R₃ → M₁ ≤ Q := fun hM => hM.trans hTQ
  have hSQ : ∀ {M₁ : Subgroup G}, M₁ ≤ (S ⊔ S') ⊔ S₃ → M₁ ≤ Q' := fun hM => hM.trans hTQ'
  have hRK : R ≤ Q := hRQ (le_sup_left.trans le_sup_left)
  have hRK' : R' ≤ Q := hRQ (le_sup_right.trans le_sup_left)
  have hRK₃ : R₃ ≤ Q := hRQ le_sup_right
  have hSL : S ≤ Q' := hSQ (le_sup_left.trans le_sup_left)
  have hSL' : S' ≤ Q' := hSQ (le_sup_right.trans le_sup_left)
  have hSL₃ : S₃ ≤ Q' := hSQ le_sup_right
  set M₀ : Set (Subgroup G) := {K, K', K₃, L, L', L₃} with hM₀
  have hM₀V : M₀ ⊆ twinSet Ω K := by
    intro M hM
    rcases hM with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hKV
    · exact hK'V
    · exact hK₃V
    · exact hLV
    · exact hL'V
    · exact hL₃V
  have hSyl : ∀ M ∈ M₀, IsSylow2In (Q ⊓ M) M := by
    intro M hM
    rcases hM with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hSylK hR hRK
    · exact hSylK hR' hRK'
    · exact hSylK hR₃ hRK₃
    · exact hQL hLV hS hSL
    · exact hQL hL'V hS' hSL'
    · exact hQL hL₃V hS₃ hSL₃
  have hconj₁ : g * x₁ * g⁻¹ ∈ Q ⊓ L := (hSylL hLV hS hSL).2 (conj_mem_conjSub k₁)
  have hconj₂ : g * x₂ * g⁻¹ ∈ Q ⊓ L' := (hSylL hL'V hS' hSL').2 (conj_mem_conjSub k₂)
  have hu₁ : u₁ ∈ Q ⊓ K := ⟨hRK h₁, hR.1 h₁⟩
  have hu₂ : u₂ ∈ Q ⊓ K' := ⟨hRK' h₂, hR'.1 h₂⟩
  have ho₁ : orderOf (g * x₁ * g⁻¹) = 4 := by rw [T7B.orderOf_conj']; exact h'.hu₁.2
  have ho₂ : orderOf (g * x₂ * g⁻¹) = 4 := by rw [T7B.orderOf_conj']; exact h'.hu₂.2
  have hmain := const_on_family h2 h hb hM₀V
    (by simp [hM₀]) (by simp [hM₀]) (by simp [hM₀]) hQ2 hSyl K (by simp [hM₀]) K'
    (by simp [hM₀]) L (by simp [hM₀]) L' (by simp [hM₀]) h.hne.symm h'.hne.symm u₁ hu₁
    u₂ hu₂ _ hconj₁ _ hconj₂ h.hu₁.2 h.hu₂.2 ho₁ ho₂
  rw [hmain, hαg]

theorem centralizer_le_normalizer_alpha (h2 : C22_2S p f) {K K' K₃ : Subgroup G}
    {z u₁ u₂ u₃ : G} (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hb : Big Ω K) :
    Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  intro c hc
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have hd := conj h hcz
  have heq := (alpha_eq_of_datum h2 h hd hb).symm
  have e : (c * u₁ * c⁻¹) * (c * u₂ * c⁻¹) = c * (u₁ * u₂) * c⁻¹ := by group
  have e2 := T7A.conjSub_closure_pair c (u₁ * u₂) z
  rw [hcz] at e2
  rw [e, ← e2, alphaOf_conjSub] at heq
  exact mem_normalizer_iff_conjSub_eq.mpr heq

end Alpha

end S22

end CFSG.ClassicalInvolution.Asc77
