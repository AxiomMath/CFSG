module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24A02
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2207

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S22
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Const
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)}

theorem const_on_family
    (h2 : Q3T8.Asc77.S22.C22_2S) {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hb : Big Ω K)
    {M₀ : Set (Subgroup G)} (hM₀ : M₀ ⊆ twinSet Ω K) (hKM : K ∈ M₀) (hK'M : K' ∈ M₀)
    (hK₃M : K₃ ∈ M₀) {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hSyl : ∀ M ∈ M₀, IsSylow2In (Q ⊓ M) M) :
    ∀ M₁ ∈ M₀, ∀ M₂ ∈ M₀, ∀ N₁ ∈ M₀, ∀ N₂ ∈ M₀, M₁ ≠ M₂ → N₁ ≠ N₂ →
      ∀ x ∈ Q ⊓ M₁, ∀ y ∈ Q ⊓ M₂, ∀ x' ∈ Q ⊓ N₁, ∀ y' ∈ Q ⊓ N₂,
        orderOf x = 4 → orderOf y = 4 → orderOf x' = 4 → orderOf y' = 4 →
        alphaOf (Subgroup.closure ({x * y, z} : Set G)) =
          alphaOf (Subgroup.closure ({x' * y', z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
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
      have hperp' : KPerp Ω a.1 = twinSet Ω a.1 := Q3T8.Asc77.T7S22.perp_of_twin h hLa
      have hLb' : b.1 ∈ twinSet Ω a.1 := by
        rw [twinSet_eq_of_mem_twinSet hz hLa]; exact hLb
      have hLc' : c.1 ∈ twinSet Ω a.1 := by
        rw [twinSet_eq_of_mem_twinSet hz hLa]; exact hLc
      have hd := Q3T8.Asc77.S22.hyp22Setting_of_sylows (h.stand.of_mem hLa.1)
        (isUniqueInvolution_of_mem_twinSet hz hLa) hLb' (Ne.symm hab) hperp' hLc' (Ne.symm hac)
        (Ne.symm hbc) (hSyl a.1 ha.1) (hSyl b.1 hb'.1) (hSyl c.1 hc.1)
        (hcomm a.1 ha.1 b.1 hb'.1 hab) (hcomm a.1 ha.1 c.1 hc.1 hac)
        (hcomm b.1 hb'.1 c.1 hc.1 hbc) ha.2.1 hb'.2.1 hc.2.1 ha.2.2 hb'.2.2 hc.2.2
      exact (Q3T8.Asc77.S22.alpha_23 h2 hd (hb.of_twin hz hLa)).symm)
    (by
      intro a b ha hb'
      obtain ⟨M, hM, hMa, hMb⟩ : ∃ M ∈ M₀, M ≠ a.1 ∧ M ≠ b.1 := by
        rcases T7B.exists_ne_of_three (a := a.1) (b := b.1) hKe h.hK₃K h.hK₃K' with h | h | h
        · exact ⟨K, hKM, h.1, h.2⟩
        · exact ⟨K', hK'M, h.1, h.2⟩
        · exact ⟨K₃, hK₃M, h.1, h.2⟩
      obtain ⟨w, hw, o⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet
        (mem_RSet_of_isSylow2In (hM₀ hM).1 (hSyl M hM))
      exact ⟨(M, w), ⟨hM, hw, o⟩, hMa, hMb⟩)
  intro M₁ hM₁ M₂ hM₂ N₁ hN₁ N₂ hN₂ hne hne' x hx y hy x' hx' y' hy' ox oy ox' oy'
  exact key (M₁, x) (M₂, y) (N₁, x') (N₂, y') ⟨hM₁, hx, ox⟩ ⟨hM₂, hy, oy⟩ ⟨hN₁, hx', ox'⟩
    ⟨hN₂, hy', oy'⟩ hne hne'
end Const
section Alpha
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)}

theorem alpha_eq_of_datum
    (h2 : Q3T8.Asc77.S22.C22_2S) {K K' K₃ L L' L₃ : Subgroup G}
    {z u₁ u₂ u₃ x₁ x₂ x₃ : G} (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (h' : Q3T8.Asc77.Hyp22Setting Ω L L' L₃ z x₁ x₂ x₃) (hb : Big Ω K) :
    alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) =
      alphaOf (Subgroup.closure ({x₁ * x₂, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
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
    iSup₂_le fun M hM => Q3T8.Asc77.S22.twin_le_normalizer_alpha h2 h hb hM
  have hXα' : X ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({x₁ * x₂, z} : Set G)) : Set G) :=
    iSup₂_le fun M hM => Q3T8.Asc77.S22.twin_le_normalizer_alpha h2 h' hbL (by rw [hVL]; exact hM)
  obtain ⟨R, R', R₃, hR, hR', hR₃, h₁, h₂, h₃, c12, c13, c23⟩ := Q3T8.Asc77.T7J.exists_sylow_triple
      h
  obtain ⟨S, S', S₃, hS, hS', hS₃, k₁, k₂, k₃, d12, d13, d23⟩ := Q3T8.Asc77.T7J.exists_sylow_triple
      h'
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
  have h'' := Q3T8.Asc77.S22.conj h' hgz
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
  have hmain := Q3T8.Asc77.S22.const_on_family h2 h hb hM₀V
    (by simp [hM₀]) (by simp [hM₀]) (by simp [hM₀]) hQ2 hSyl K (by simp [hM₀]) K'
    (by simp [hM₀]) L (by simp [hM₀]) L' (by simp [hM₀]) h.hne.symm h'.hne.symm u₁ hu₁
    u₂ hu₂ _ hconj₁ _ hconj₂ h.hu₁.2 h.hu₂.2 ho₁ ho₂
  rw [hmain, hαg]

theorem centralizer_le_normalizer_alpha
    (h2 : Q3T8.Asc77.S22.C22_2S) {K K' K₃ : Subgroup G}
    {z u₁ u₂ u₃ : G} (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hb : Big Ω K) :
    Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  intro c hc
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have hd := Q3T8.Asc77.S22.conj h hcz
  have heq := (Q3T8.Asc77.S22.alpha_eq_of_datum h2 h hd hb).symm
  have e : (c * u₁ * c⁻¹) * (c * u₂ * c⁻¹) = c * (u₁ * u₂) * c⁻¹ := by group
  have e2 := T7A.conjSub_closure_pair c (u₁ * u₂) z
  rw [hcz] at e2
  rw [e, ← e2, alphaOf_conjSub] at heq
  exact mem_normalizer_iff_conjSub_eq.mpr heq
end Alpha
end S22
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
section Inputs

@[expose] def Hyp22FourTwins
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ →
      ∃ K₄ ∈ twinSet Ω K, K₄ ≠ K ∧ K₄ ≠ K' ∧ K₄ ≠ K₃ ∧
        ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃ ∨ M = K₄

@[expose] def Hyp22Fuse
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ K₄ ∈ twinSet Ω K, K₄ ≠ K → K₄ ≠ K' → K₄ ≠ K₃ →
        ∃ (R R' : Subgroup G) (b b' y : G),
          IsSylow2In R (Q3T8.Asc77.ExactLayer.exactCore (u₁ * u₂) K₃) ∧
          IsSylow2In R' (Q3T8.Asc77.ExactLayer.exactCore (u₁ * u₂) K₄) ∧ Commutes R R' ∧
          b ∈ Q3T8.Asc77.ExactLayer.exactCore (u₁ * u₂) K₃ ∧ b' ∈ Q3T8.Asc77.ExactLayer.exactCore
              (u₁ * u₂) K₄ ∧
          b * b = z ∧ b' * b' = z ∧ y ∈ Subgroup.centralizer ({u₁ * u₂} : Set G) ∧
          y * z * y⁻¹ = b * b' * (u₁ * u₂) ∧ b * b' * (u₁ * u₂) ≠ z ∧
          z * (b * b' * (u₁ * u₂)) = (b * b' * (u₁ * u₂)) * z

@[expose] def C22_8Gen
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ →
      (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤
end Inputs
namespace T7J
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7J
section Layer
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem not_mem_tqMembers_of_mul
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω)
    {K : Subgroup G} (hK : K ∈ Ω) {z u v c : G} (hz : IsUniqueInvolution K z) (huK : u ∈ K)
    (hu4 : orderOf u = 4) (hv : v ∈ trivialOnQuot K) (hc : c = u * v) : K ∉
        Q3T8.Asc77.ExactLayer.tqMembers Ω c := by
  intro hKt
  have hcK : c ∈ trivialOnQuot K := hKt.2
  have hu : u ∈ trivialOnQuot K := by
    have : u = c * v⁻¹ := by rw [hc]; group
    rw [this]
    exact Subgroup.mul_mem _ hcK (Subgroup.inv_mem _ hv)
  have hcomm : ∀ y ∈ K, ⁅u, y⁆ ∈ oddCoreOf K := fun y hy =>
    (mem_trivialOnQuot_iff.mp hu).2 y hy
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) := T7A.isPGroup_zpowers_of_orderOf_four hu4
  rcases hΩ.center_two hK hz u huK hu2 hcomm with h | h
  · rw [h, orderOf_one] at hu4
    omega
  · rw [h] at hu4
    have : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
    omega
end Layer
end T7J
section Reduction

theorem c22_8X_layer_of_inputs
    (h4 : Q3T8.Asc77.Hyp22FourTwins) (hF : Q3T8.Asc77.Hyp22Fuse)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G} (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    Q3T8.Asc77.LayerOrthType Ω (u₁ * u₂) 6 (piSign 3 1) := by
  have hs := h.setting
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hBelow : Q3T8.Generic.CITBelowU (Nat.card G) := hs.stand.below
  obtain ⟨K₄, hK₄, hK₄K, hK₄K', hK₄K₃, hV⟩ := h4 G Ω K K' K₃ z u₁ u₂ u₃ hs
  obtain ⟨R, R', b, b', y, hR, hR', hRR', hb, hb', ob, ob', hyc, hyz, htz, hzt⟩ :=
    hF G Ω K K' K₃ z u₁ u₂ u₃ h K₄ hK₄ hK₄K hK₄K' hK₄K₃
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := hs.hzK'
  have hzK₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hzK₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  
  have hu₁K₃ : u₁ ∈ trivialOnQuot K₃ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hKΩ hK₃Ω hs.hK₃K.symm hz hzK₃ hs.hu₁.1
  have hu₂K₃ : u₂ ∈ trivialOnQuot K₃ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK'Ω hK₃Ω hs.hK₃K'.symm hzK' hzK₃ hs.hu₂.1
  have hu₁K₄ : u₁ ∈ trivialOnQuot K₄ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hKΩ hK₄Ω hK₄K.symm hz hzK₄ hs.hu₁.1
  have hu₂K₄ : u₂ ∈ trivialOnQuot K₄ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK'Ω hK₄Ω hK₄K'.symm hzK' hzK₄ hs.hu₂.1
  have hK₃t : K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂) := ⟨hK₃Ω, Subgroup.mul_mem _ hu₁K₃
      hu₂K₃⟩
  have hK₄t : K₄ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂) := ⟨hK₄Ω, Subgroup.mul_mem _ hu₁K₄
      hu₂K₄⟩
  
  have hu₂K : u₂ ∈ trivialOnQuot K :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK'Ω hKΩ hs.hne hzK' hz hs.hu₂.1
  have hu₁K' : u₁ ∈ trivialOnQuot K' :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hKΩ hK'Ω hs.hne.symm hz hzK' hs.hu₁.1
  have hnotK : K ∉ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂) :=
    Q3T8.Asc77.T7J.not_mem_tqMembers_of_mul hΩ hKΩ hz hs.hu₁.1 hs.hu₁.2 hu₂K rfl
  have hnotK' : K' ∉ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂) :=
    Q3T8.Asc77.T7J.not_mem_tqMembers_of_mul hΩ hK'Ω hzK' hs.hu₂.1 hs.hu₂.2 hu₁K' hs.comm₁₂
  
  have hperp₃ : ∀ J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂), J ∈ KPerp Ω K₃ → J = K₃ ∨ J = K₄
      := by
    intro J hJt hJperp
    rw [Q3T8.Asc77.T7S22.perp_of_twin hs hs.hK₃, twinSet_eq_of_mem_twinSet hz hs.hK₃] at hJperp
    rcases hV J hJperp with rfl | rfl | rfl | rfl
    · exact absurd hJt hnotK
    · exact absurd hJt hnotK'
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hperp₄ : ∀ J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂), J ∈ KPerp Ω K₄ → J = K₄ ∨ J = K₃
      := by
    intro J hJt hJperp
    rw [Q3T8.Asc77.T7S22.perp_of_twin hs hK₄, twinSet_eq_of_mem_twinSet hz hK₄] at hJperp
    rcases hV J hJperp with rfl | rfl | rfl | rfl
    · exact absurd hJt hnotK
    · exact absurd hJt hnotK'
    · exact Or.inr rfl
    · exact Or.inl rfl
  
  have hc2 : (u₁ * u₂) * (u₁ * u₂) = 1 := hs.sq_12
  have hc1 : u₁ * u₂ ≠ 1 :=
    (Q3T8.Asc77.T7S22.mul_ne_one_of_twins hΩ hKΩ hK'Ω hs.hne.symm hz hs.hu₁.1 hs.hu₂.1 hs.hu₂.2).1
  have hMz : Q3T8.Generic.IsClassicalMember K₃ z := Q3T8.Asc77.isClassicalMember_of_twin hΩ hK₃Ω
      hzK₃
  have hnc : ¬ ({u₁ * u₂} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one (Q3T8.Asc77.exists_noncomm_of_isClassicalMember hMz) hc1
  have hL : conjSub y K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂) :=
    Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hyc hK₃t
  have htL : IsUniqueInvolution (conjSub y K₃) (b * b' * (u₁ * u₂)) := by
    rw [← hyz]
    exact hzK₃.conj y
  exact Q3T8.Asc77.T7J.layer_orth_six_weak_proved hΩ hBelow hc2 hnc hK₃t hK₄t hL hzK₃ hzK₄ hperp₃
    hperp₄ htL hzt htz hR hR' hRR' hb hb' ob ob' rfl

theorem hyp22FourthTwin_of_fourTwins
    (h4 : Q3T8.Asc77.Hyp22FourTwins) : Q3T8.Asc77.Hyp22FourthTwin
    := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  obtain ⟨K₄, hK₄, h1, h2, h3, -⟩ := h4 G Ω K K' K₃ z u₁ u₂ u₃ h
  exact ⟨K₄, hK₄, h1, h2, h3⟩
end Reduction
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.rep_le_centralizer
    (ρ : Rep Ω W) {y :
    G} (hy : y ∈ W) (hr : ρ.r * y = y * ρ.r) :
    ρ.R ≤ Subgroup.centralizer ({y} : Set G) := by
  obtain ⟨-, -, -, -, hcard⟩ := Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW ρ.hR ρ.hK ρ.hRK
  have hidx : ((ρ.R ⊓ W).subgroupOf ρ.R).index = 2 :=
    relIndex_eq_two_of_card inf_le_left hcard
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hidx
  have : ((ρ.R ⊓ W).subgroupOf ρ.R).Normal := Subgroup.normal_of_index_eq_two hidx
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hxW : x ∈ W
  · exact c.comm_W x hxW y hy
  · have hb : (⟨x, hx⟩ : ↥ρ.R) ∉ (ρ.R ⊓ W).subgroupOf ρ.R := fun h =>
      hxW (Subgroup.mem_subgroupOf.mp h).2
    have hb' : (⟨ρ.r, ρ.hr⟩ : ↥ρ.R) ∉ (ρ.R ⊓ W).subgroupOf ρ.R := fun h =>
      ρ.hrW (Subgroup.mem_subgroupOf.mp h).2
    have h1 : (⟨x, hx⟩ : ↥ρ.R) * a ∈ (ρ.R ⊓ W).subgroupOf ρ.R := by
      rcases ha ⟨x, hx⟩ with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hb
    have h2 : (⟨ρ.r, ρ.hr⟩ : ↥ρ.R) * a ∈ (ρ.R ⊓ W).subgroupOf ρ.R := by
      rcases ha ⟨ρ.r, ρ.hr⟩ with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hb'
    have h3 : (⟨ρ.r, ρ.hr⟩ : ↥ρ.R)⁻¹ * ⟨x, hx⟩ ∈ (ρ.R ⊓ W).subgroupOf ρ.R := by
      have h4 : (a⁻¹ * (⟨ρ.r, ρ.hr⟩ : ↥ρ.R)⁻¹ * ⟨x, hx⟩ * a) ∈ (ρ.R ⊓ W).subgroupOf ρ.R := by
        have := ((ρ.R ⊓ W).subgroupOf ρ.R).mul_mem (((ρ.R ⊓ W).subgroupOf ρ.R).inv_mem h2) h1
        simpa [mul_assoc] using this
      have h5 := ‹((ρ.R ⊓ W).subgroupOf ρ.R).Normal›.conj_mem _ h4 a
      simpa [mul_assoc] using h5
    have hW3 : ρ.r⁻¹ * x ∈ W := (Subgroup.mem_subgroupOf.mp h3).2
    have hcomm : (ρ.r⁻¹ * x) * y = y * (ρ.r⁻¹ * x) := c.comm_W _ hW3 y hy
    calc x * y = ρ.r * ((ρ.r⁻¹ * x) * y) := by group
      _ = ρ.r * (y * (ρ.r⁻¹ * x)) := by rw [hcomm]
      _ = (ρ.r * y) * (ρ.r⁻¹ * x) := by group
      _ = (y * ρ.r) * (ρ.r⁻¹ * x) := by rw [hr]
      _ = y * x := by group

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.conjRep_braid
    (hclC :
    Q3CL.ClassicalClause Ω) (ρ σ : Rep Ω W) (hnc : ρ.img * σ.img ≠ σ.img * ρ.img)
    (hn : ρ.r * σ.r * ρ.r⁻¹ ∈ Subgroup.normalizer (W : Set G)) :
    (Q3T8.Asc77.T7D.conjRep c.hΩ hn ρ).img = σ.img := by
  have hP : Q3T8.Asc77.PartIHyp Ω := ⟨c.hΩ, hclC, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    Q3T8.Asc77.Thompson.isTT_muDelta c.hΩ c.hW (Q3CL.thompsonCube hP W c.hW)
  have hdΔ := T7D.imgQ_mem ρ
  have hsΔ := T7D.imgQ_mem σ
  have hdd := hTT.mul_self _ hdΔ
  have hss := hTT.mul_self _ hsΔ
  have hbr := hTT.braid hdΔ hsΔ (fun e => hnc (congrArg Subtype.val e))
  have hdi := hTT.inv_eq hdΔ
  have hsi := hTT.inv_eq hsΔ
  set d : ↥(muGroup Ω W) := T7D.imgQ ρ with hd
  set s : ↥(muGroup Ω W) := T7D.imgQ σ with hs
  have key : (d * s * d⁻¹) * d * (d * s * d⁻¹)⁻¹ = s := by
    have hinv : (d * s * d⁻¹)⁻¹ = d * s * d := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, hdi, hsi]
      group
    rw [hinv, hdi]
    calc d * s * d * d * (d * s * d) = d * s * (d * d) * (d * s * d) := by group
      _ = (d * s * d) * (s * d) := by rw [hdd]; group
      _ = (s * d * s) * (s * d) := by rw [hbr]
      _ = s * d * (s * s) * d := by group
      _ = s := by rw [hss]; calc s * d * 1 * d = s * (d * d) := by group
                                _ = s := by rw [hdd]; group
  have hρr := ρ.r_mem_normalizer
  have hσr := σ.r_mem_normalizer
  have hpn : Thompson.piG W (ρ.r * σ.r * ρ.r⁻¹) = ((d * s * d⁻¹ : ↥(muGroup Ω W)) :
      NQuot (W ⊔ OCW W)) := by
    rw [Thompson.piG_mul (Subgroup.mul_mem _ hρr hσr) (Subgroup.inv_mem _ hρr),
      Thompson.piG_mul hρr hσr, Thompson.piG_inv hρr]
    rfl
  rw [Q3T8.Asc77.T7D.conjRep_img, hpn]
  exact congrArg Subtype.val key

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.far_conj
    (hclC : Q3CL.ClassicalClause
    Ω) (hnc : ¬ DbarConnected Ω W) (ρ : Fin 4 → Rep Ω W)
    (hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) (σ : Rep Ω W)
    (hfar : ∀ i, σ.img * (ρ i).img ≠ (ρ i).img * σ.img)
    (hn : (ρ 0).r ∈ Subgroup.normalizer (W : Set G)) :
    ∀ i, (Q3T8.Asc77.T7D.conjRep c.hΩ hn σ).img * (ρ i).img ≠
      (ρ i).img * (Q3T8.Asc77.T7D.conjRep c.hΩ hn σ).img := by
  have hP : Q3T8.Asc77.PartIHyp Ω := ⟨c.hΩ, hclC, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    Q3T8.Asc77.Thompson.isTT_muDelta c.hΩ c.hW (Q3CL.thompsonCube hP W c.hW)
  obtain ⟨hcl, hAON⟩ := c.clique_dichotomy hclC hnc (T7D.imgQ_mem (ρ 0))
  have hxC : ∀ i, T7D.imgQ (ρ i) ∈ Star3T.cent (muDelta Ω W) (T7D.imgQ (ρ 0)) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact Star3T.self_mem_cent (T7D.imgQ_mem (ρ 0))
    · exact ⟨T7D.imgQ_mem (ρ i), (Subtype.ext (c.comm_of_omega (ρ 0) (ρ i)
        (hnbr 0 i (Ne.symm hi)))).symm⟩
  intro i hcomm
  set x₀ : ↥(muGroup Ω W) := T7D.imgQ (ρ 0) with hx₀
  set s : ↥(muGroup Ω W) := T7D.imgQ σ with hs
  have hx₀Δ := T7D.imgQ_mem (ρ 0)
  have hsΔ := T7D.imgQ_mem σ
  have hx₀₀ := hTT.mul_self _ hx₀Δ
  have hx₀i := hTT.inv_eq hx₀Δ
  have hs'Δ : x₀ * s * x₀⁻¹ ∈ muDelta Ω W := hTT.conj_mem s hsΔ x₀
  have hs'img : (Q3T8.Asc77.T7D.conjRep c.hΩ hn σ).img = ((x₀ * s * x₀⁻¹ : ↥(muGroup Ω W)) :
      NQuot (W ⊔ OCW W)) := by
    rw [Q3T8.Asc77.T7D.conjRep_img]
    have : Thompson.piG W (ρ 0).r = (x₀ : NQuot (W ⊔ OCW W)) := rfl
    rw [this]
    rfl
  have hcomm' : (x₀ * s * x₀⁻¹) * T7D.imgQ (ρ i) = T7D.imgQ (ρ i) * (x₀ * s * x₀⁻¹) := by
    apply Subtype.ext
    rw [hs'img] at hcomm
    exact hcomm
  have hin : x₀ * s * x₀⁻¹ ∈ Star3T.cent (muDelta Ω W) x₀ :=
    hAON _ hs'Δ _ (hxC i) hcomm'
  have h1 : (x₀ * s * x₀⁻¹) * x₀ = x₀ * (x₀ * s * x₀⁻¹) := hin.2
  apply hfar 0
  have h2 : s * x₀ = x₀ * s := by
    have h3 : x₀ * s = x₀ * x₀ * s * x₀⁻¹ := by
      calc x₀ * s = (x₀ * s * x₀⁻¹) * x₀ := by group
        _ = x₀ * (x₀ * s * x₀⁻¹) := h1
        _ = x₀ * x₀ * s * x₀⁻¹ := by group
    rw [hx₀₀, one_mul] at h3
    rw [hx₀i] at h3
    exact h3.symm
  exact congrArg Subtype.val h2

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.fuse_frame
    (hclC :
    Q3CL.ClassicalClause Ω) (hnc : ¬ DbarConnected Ω W) (ρ : Fin 4 → Rep Ω W) {z : G}
    (hz : ∀ i, IsUniqueInvolution (ρ i).K z)
    (hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K)
    (hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) :
    ∃ (σ : Rep Ω W) (t : G) (g : Fin 4 → G), IsUniqueInvolution σ.K t ∧
      (∀ i, σ.img * (ρ i).img ≠ (ρ i).img * σ.img) ∧
      (∀ i, g i ∈ (ρ i).K ⊓ W ∧ orderOf (g i) = 4) ∧ t = g 0 * g 1 * g 2 * g 3 ∧
      σ.R ≤ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
  classical
  obtain ⟨σ, t, g, ht, hfar, hg, hrel⟩ := c.exists_relation hclC hnc ρ hne hnbr
  have hgsq : ∀ i, g i * g i = z := fun i =>
    sq_eq_involution_of_orderOf_four (hz i) (hg i).1.1 (hg i).2
  have hgW : ∀ i, g i ∈ W := fun i => (hg i).1.2
  have hz2 : z * z = 1 := (hz 0).sq
  have hzW : z ∈ W := c.mem_W_of_isUniqueInvolution (ρ 0) (hz 0)
  have htW : t ∈ W := c.mem_W_of_isUniqueInvolution σ ht
  have hKσ : ∀ i, σ.K ≠ (ρ i).K := fun i h => hfar i (by rw [c.img_eq_of_K_eq σ (ρ i) h])
  have hnot : ∀ i, (ρ i).K ∉ omegaNbr Ω σ.K := fun i h => hfar i (c.comm_of_omega σ (ρ i) h)
  have hnot' : ∀ i, σ.K ∉ omegaNbr Ω (ρ i).K := fun i h => hfar i
    (c.comm_of_omega (ρ i) σ h).symm
  have hτz : σ.r * z * σ.r⁻¹ = t * z := c.conj_involution σ (ρ 0) (hKσ 0) (hnot 0) ht (hz 0)
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => c.comm_W x hx y hy
  have hrW : ∀ x ∈ W, σ.r * x * σ.r⁻¹ ∈ W := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp σ.r_mem_normalizer x).mp hx
  obtain ⟨e, he⟩ : ∃ e : Fin 4 → G, ∀ i, e i = σ.r * g i * σ.r⁻¹ * (g i)⁻¹ := ⟨_, fun _ => rfl⟩
  have heW : ∀ i, e i ∈ σ.K ⊓ W := fun i => by
    rw [he]; exact c.comm_mem σ (ρ i) (hKσ i) (hg i).1
  have hegi : ∀ i, σ.r * g i * σ.r⁻¹ = e i * g i := fun i => by rw [he]; group
  have hesq : ∀ i, e i * e i = t := by
    intro i
    have hw : σ.r * g i * σ.r⁻¹ ∈ W := hrW _ (hgW i)
    have h1 : (σ.r * g i * σ.r⁻¹) * (σ.r * g i * σ.r⁻¹) = t * z := by
      calc (σ.r * g i * σ.r⁻¹) * (σ.r * g i * σ.r⁻¹) = σ.r * (g i * g i) * σ.r⁻¹ := by group
        _ = t * z := by rw [hgsq i, hτz]
    have hgi : (g i)⁻¹ ∈ W := W.inv_mem (hgW i)
    have h2 : (g i)⁻¹ * (g i)⁻¹ = z := by
      have : (g i)⁻¹ * (g i)⁻¹ = (g i * g i)⁻¹ := by group
      rw [this, hgsq i]
      exact inv_eq_of_mul_eq_one_right hz2
    calc e i * e i = (σ.r * g i * σ.r⁻¹) * (σ.r * g i * σ.r⁻¹) * ((g i)⁻¹ * (g i)⁻¹) := by
          rw [he]
          have := hcomm _ hw _ hgi
          calc σ.r * g i * σ.r⁻¹ * (g i)⁻¹ * (σ.r * g i * σ.r⁻¹ * (g i)⁻¹)
              = σ.r * g i * σ.r⁻¹ * ((g i)⁻¹ * (σ.r * g i * σ.r⁻¹)) * (g i)⁻¹ := by group
            _ = σ.r * g i * σ.r⁻¹ * ((σ.r * g i * σ.r⁻¹) * (g i)⁻¹) * (g i)⁻¹ := by rw [this]
            _ = _ := by group
      _ = t := by rw [h1, h2, mul_assoc, hz2, mul_one]
  have hht : t * t = 1 := ht.sq
  have hcase : e 1 = e 0 ∨ e 1 = (e 0)⁻¹ := by
    have hsq : (e 1 * (e 0)⁻¹) * (e 1 * (e 0)⁻¹) = 1 := by
      have hc := hcomm _ (heW 1).2 _ (W.inv_mem (heW 0).2)
      calc (e 1 * (e 0)⁻¹) * (e 1 * (e 0)⁻¹) = e 1 * ((e 0)⁻¹ * e 1) * (e 0)⁻¹ := by group
        _ = e 1 * (e 1 * (e 0)⁻¹) * (e 0)⁻¹ := by rw [← hc]
        _ = (e 1 * e 1) * ((e 0)⁻¹ * (e 0)⁻¹) := by group
        _ = t * t := by
            rw [hesq 1]
            congr 1
            have : (e 0)⁻¹ * (e 0)⁻¹ = (e 0 * e 0)⁻¹ := by group
            rw [this, hesq 0]
            exact inv_eq_of_mul_eq_one_right hht
        _ = 1 := hht
    have hmem : e 1 * (e 0)⁻¹ ∈ σ.K := σ.K.mul_mem (heW 1).1 (σ.K.inv_mem (heW 0).1)
    rcases ht.unique _ hmem hsq with h | h
    · left
      calc e 1 = (e 1 * (e 0)⁻¹) * e 0 := by group
        _ = e 0 := by rw [h, one_mul]
    · right
      have hinv : (e 0)⁻¹ = e 0 * t := by
        have : e 0 * (e 0 * t) = 1 := by
          rw [← mul_assoc, hesq 0, hht]
        exact inv_eq_of_mul_eq_one_right this
      calc e 1 = (e 1 * (e 0)⁻¹) * e 0 := by group
        _ = t * e 0 := by rw [h]
        _ = e 0 * t := hcomm _ htW _ (heW 0).2
        _ = (e 0)⁻¹ := hinv.symm
  rcases hcase with hB | hA
  ·
    have hr₀ : (ρ 0).r ∈ Subgroup.normalizer (W : Set G) := (ρ 0).r_mem_normalizer
    have hne0 : (ρ 0).K ≠ σ.K := fun h => hKσ 0 h.symm
    have hτ' : (ρ 0).r * t * (ρ 0).r⁻¹ = z * t :=
      c.conj_involution (ρ 0) σ hne0 (hnot' 0) (hz 0) ht
    refine ⟨Q3T8.Asc77.T7D.conjRep c.hΩ hr₀ σ, (ρ 0).r * t * (ρ 0).r⁻¹,
      fun i => if i = 2 then (g 2)⁻¹ else g i, ht.conj _,
      c.far_conj hclC hnc ρ hnbr σ hfar hr₀, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = 2
      · subst hi
        simp only [ite_true]
        exact ⟨⟨(ρ 2).K.inv_mem (hg 2).1.1, W.inv_mem (hgW 2)⟩, by rw [orderOf_inv]; exact (hg 2).2⟩
      · simp only [hi, ite_false]
        exact hg i
    · have h20 : ¬ ((0 : Fin 4) = 2) := by decide
      have h21 : ¬ ((1 : Fin 4) = 2) := by decide
      have h23 : ¬ ((3 : Fin 4) = 2) := by decide
      simp only [h20, h21, h23, ite_false, ite_true]
      rw [hτ', hrel]
      have hWc : ∀ x y : ↥W, x * y = y * x := fun x y => Subtype.ext (hcomm x x.2 y y.2)
      let _ : CommGroup ↥W := { (inferInstance : Group ↥W) with mul_comm := hWc }
      have h2 : (⟨g 2, hgW 2⟩ : ↥W)⁻¹ = ⟨g 2, hgW 2⟩ * ⟨z, hzW⟩ := by
        apply inv_eq_of_mul_eq_one_right
        rw [← mul_assoc]
        apply Subtype.ext
        show g 2 * g 2 * z = 1
        rw [hgsq 2, hz2]
      have hgoal : (⟨z, hzW⟩ : ↥W) * (⟨g 0, hgW 0⟩ * ⟨g 1, hgW 1⟩ * ⟨g 2, hgW 2⟩ * ⟨g 3, hgW 3⟩) =
          ⟨g 0, hgW 0⟩ * ⟨g 1, hgW 1⟩ * (⟨g 2, hgW 2⟩)⁻¹ * ⟨g 3, hgW 3⟩ := by
        rw [h2]
        ac_rfl
      exact congrArg Subtype.val hgoal
    · have h20 : ¬ ((0 : Fin 4) = 2) := by decide
      have h21 : ¬ ((1 : Fin 4) = 2) := by decide
      simp only [h20, h21, ite_false]
      have hy : g 0 * g 1 ∈ W := W.mul_mem (hgW 0) (hgW 1)
      refine c.rep_le_centralizer (Q3T8.Asc77.T7D.conjRep c.hΩ hr₀ σ) hy ?_
      have hr₀g₀ : (ρ 0).r * g 0 * (ρ 0).r⁻¹ = (g 0)⁻¹ := c.conj_inv (ρ 0) (hg 0).1
      have hr₀g₁ : (ρ 0).r * g 1 = g 1 * (ρ 0).r :=
        c.centralizes (ρ 0) (ρ 1) (hnbr 0 1 (by decide)) (hg 1).1
      have hr₀g₁' : (ρ 0).r * g 1 * (ρ 0).r⁻¹ = g 1 := by rw [hr₀g₁]; group
      have hinv₀ : (ρ 0).r⁻¹ * g 0 * (ρ 0).r = (g 0)⁻¹ := by
        have h3 : (ρ 0).r⁻¹ * (g 0)⁻¹ * (ρ 0).r = g 0 := by
          calc (ρ 0).r⁻¹ * (g 0)⁻¹ * (ρ 0).r = (ρ 0).r⁻¹ * ((ρ 0).r * g 0 * (ρ 0).r⁻¹) *
              (ρ 0).r := by rw [hr₀g₀]
            _ = g 0 := by group
        calc (ρ 0).r⁻¹ * g 0 * (ρ 0).r = ((ρ 0).r⁻¹ * (g 0)⁻¹ * (ρ 0).r)⁻¹ := by group
          _ = (g 0)⁻¹ := by rw [h3]
      have hinv₁ : (ρ 0).r⁻¹ * g 1 * (ρ 0).r = g 1 := by
        calc (ρ 0).r⁻¹ * g 1 * (ρ 0).r = (ρ 0).r⁻¹ * (g 1 * (ρ 0).r) := by group
          _ = (ρ 0).r⁻¹ * ((ρ 0).r * g 1) := by rw [hr₀g₁]
          _ = g 1 := by group
      have h1 : ((ρ 0).r * σ.r * (ρ 0).r⁻¹) * (g 0 * g 1) * ((ρ 0).r * σ.r * (ρ 0).r⁻¹)⁻¹ =
          g 0 * g 1 := by
        calc ((ρ 0).r * σ.r * (ρ 0).r⁻¹) * (g 0 * g 1) * ((ρ 0).r * σ.r * (ρ 0).r⁻¹)⁻¹
            = (ρ 0).r * (σ.r * ((ρ 0).r⁻¹ * g 0 * (ρ 0).r) * ((ρ 0).r⁻¹ * g 1 * (ρ 0).r) *
                σ.r⁻¹) * (ρ 0).r⁻¹ := by group
          _ = (ρ 0).r * ((σ.r * g 0 * σ.r⁻¹)⁻¹ * (σ.r * g 1 * σ.r⁻¹)) * (ρ 0).r⁻¹ := by
              rw [hinv₀, hinv₁]; group
          _ = (ρ 0).r * ((e 0 * g 0)⁻¹ * (e 1 * g 1)) * (ρ 0).r⁻¹ := by rw [hegi 0, hegi 1]
          _ = (ρ 0).r * ((e 0 * g 0)⁻¹ * (e 0 * g 1)) * (ρ 0).r⁻¹ := by rw [hB]
          _ = (ρ 0).r * ((g 0)⁻¹ * g 1) * (ρ 0).r⁻¹ := by group
          _ = ((ρ 0).r * g 0 * (ρ 0).r⁻¹)⁻¹ * ((ρ 0).r * g 1 * (ρ 0).r⁻¹) := by group
          _ = g 0 * g 1 := by rw [hr₀g₀, hr₀g₁', inv_inv]
      exact mul_inv_eq_iff_eq_mul.mp h1
  ·
    refine ⟨σ, t, g, ht, hfar, hg, hrel, ?_⟩
    have hy : g 0 * g 1 ∈ W := W.mul_mem (hgW 0) (hgW 1)
    refine c.rep_le_centralizer σ hy ?_
    have h1 : σ.r * (g 0 * g 1) * σ.r⁻¹ = g 0 * g 1 := by
      calc σ.r * (g 0 * g 1) * σ.r⁻¹ = (σ.r * g 0 * σ.r⁻¹) * (σ.r * g 1 * σ.r⁻¹) := by group
        _ = (e 0 * g 0) * (e 1 * g 1) := by rw [hegi 0, hegi 1]
        _ = (e 0 * g 0) * ((e 0)⁻¹ * g 1) := by rw [hA]
        _ = (g 0 * e 0) * ((e 0)⁻¹ * g 1) := by rw [hcomm _ (heW 0).2 _ (hgW 0)]
        _ = g 0 * (e 0 * (e 0)⁻¹) * g 1 := by group
        _ = g 0 * g 1 := by group
    exact (mul_inv_eq_iff_eq_mul.mp h1)
end Ctx
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace C22G
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22G
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem comm_sq
    (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W) {z t g : G}
    (hz : IsUniqueInvolution ρ.K z) (hK : σ.K ≠ ρ.K) (hg : g ∈ ρ.K ⊓ W) (hg4 : orderOf g = 4)
    (hτz : σ.r * z * σ.r⁻¹ = t * z) :
    σ.r * g * σ.r⁻¹ * g⁻¹ ∈ σ.K ⊓ W ∧
      (σ.r * g * σ.r⁻¹ * g⁻¹) * (σ.r * g * σ.r⁻¹ * g⁻¹) = t := by
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => c.comm_W x hx y hy
  have hgsq : g * g = z := sq_eq_involution_of_orderOf_four hz hg.1 hg4
  have hgW : g ∈ W := hg.2
  have hz2 : z * z = 1 := hz.sq
  have hxW : σ.r * g * σ.r⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp σ.r_mem_normalizer g).mp hgW
  refine ⟨c.comm_mem σ ρ hK hg, ?_⟩
  have h1 : (σ.r * g * σ.r⁻¹) * (σ.r * g * σ.r⁻¹) = t * z := by
    calc (σ.r * g * σ.r⁻¹) * (σ.r * g * σ.r⁻¹) = σ.r * (g * g) * σ.r⁻¹ := by group
      _ = t * z := by rw [hgsq, hτz]
  have hgi : g⁻¹ ∈ W := W.inv_mem hgW
  have h2 : g⁻¹ * g⁻¹ = z := by
    have : g⁻¹ * g⁻¹ = (g * g)⁻¹ := by group
    rw [this, hgsq]
    exact inv_eq_of_mul_eq_one_right hz2
  have hc : (σ.r * g * σ.r⁻¹) * g⁻¹ = g⁻¹ * (σ.r * g * σ.r⁻¹) := hcomm _ hxW _ hgi
  calc σ.r * g * σ.r⁻¹ * g⁻¹ * (σ.r * g * σ.r⁻¹ * g⁻¹)
      = (σ.r * g * σ.r⁻¹) * (g⁻¹ * (σ.r * g * σ.r⁻¹)) * g⁻¹ := by group
    _ = (σ.r * g * σ.r⁻¹) * ((σ.r * g * σ.r⁻¹) * g⁻¹) * g⁻¹ := by rw [← hc]
    _ = ((σ.r * g * σ.r⁻¹) * (σ.r * g * σ.r⁻¹)) * (g⁻¹ * g⁻¹) := by group
    _ = (t * z) * z := by rw [h1, h2]
    _ = t := by rw [mul_assoc, hz2, mul_one]

theorem exists_centralized_pair
    (c : Q3CL.Thompson.Ctx Ω W) (ρ₀ ρ₁ σ : Rep Ω W) {z t g₀ g₁ : G}
    (hz₀ : IsUniqueInvolution ρ₀.K z) (hz₁ : IsUniqueInvolution ρ₁.K z)
    (ht : IsUniqueInvolution σ.K t) (hK₀ : σ.K ≠ ρ₀.K) (hK₁ : σ.K ≠ ρ₁.K)
    (hn₀ : ρ₀.K ∉ omegaNbr Ω σ.K) (hg₀ : g₀ ∈ ρ₀.K ⊓ W) (ho₀ : orderOf g₀ = 4)
    (hg₁ : g₁ ∈ ρ₁.K ⊓ W) (ho₁ : orderOf g₁ = 4) :
    ∃ g₁' : G, g₁' ∈ ρ₁.K ⊓ W ∧ orderOf g₁' = 4 ∧
      σ.R ≤ Subgroup.centralizer ({g₀ * g₁'} : Set G) := by
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => c.comm_W x hx y hy
  have hτz : σ.r * z * σ.r⁻¹ = t * z := c.conj_involution σ ρ₀ hK₀ hn₀ ht hz₀
  have hzW : z ∈ W := c.mem_W_of_isUniqueInvolution ρ₀ hz₀
  have htW : t ∈ W := c.mem_W_of_isUniqueInvolution σ ht
  have hz2 : z * z = 1 := hz₀.sq
  have hht : t * t = 1 := ht.sq
  obtain ⟨he₀W, he₀sq⟩ := Q3T8.Asc77.C22G.comm_sq c ρ₀ σ hz₀ hK₀ hg₀ ho₀ hτz
  obtain ⟨he₁W, he₁sq⟩ := Q3T8.Asc77.C22G.comm_sq c ρ₁ σ hz₁ hK₁ hg₁ ho₁ hτz
  set e₀ : G := σ.r * g₀ * σ.r⁻¹ * g₀⁻¹ with he₀
  set e₁ : G := σ.r * g₁ * σ.r⁻¹ * g₁⁻¹ with he₁
  have hg₀W : g₀ ∈ W := hg₀.2
  have hg₁W : g₁ ∈ W := hg₁.2
  have hge₀ : σ.r * g₀ * σ.r⁻¹ = e₀ * g₀ := by rw [he₀]; group
  have hge₁ : σ.r * g₁ * σ.r⁻¹ = e₁ * g₁ := by rw [he₁]; group
  have hcase : e₁ = e₀ ∨ e₁ = e₀⁻¹ := by
    have hsq : (e₁ * e₀⁻¹) * (e₁ * e₀⁻¹) = 1 := by
      have hc := hcomm _ he₁W.2 _ (W.inv_mem he₀W.2)
      calc (e₁ * e₀⁻¹) * (e₁ * e₀⁻¹) = e₁ * (e₀⁻¹ * e₁) * e₀⁻¹ := by group
        _ = e₁ * (e₁ * e₀⁻¹) * e₀⁻¹ := by rw [← hc]
        _ = (e₁ * e₁) * (e₀⁻¹ * e₀⁻¹) := by group
        _ = t * t := by
            rw [he₁sq]
            congr 1
            have : e₀⁻¹ * e₀⁻¹ = (e₀ * e₀)⁻¹ := by group
            rw [this, he₀sq]
            exact inv_eq_of_mul_eq_one_right hht
        _ = 1 := hht
    have hmem : e₁ * e₀⁻¹ ∈ σ.K := σ.K.mul_mem he₁W.1 (σ.K.inv_mem he₀W.1)
    rcases ht.unique _ hmem hsq with h | h
    · left
      calc e₁ = (e₁ * e₀⁻¹) * e₀ := by group
        _ = e₀ := by rw [h, one_mul]
    · right
      have hinv : e₀⁻¹ = e₀ * t := by
        have : e₀ * (e₀ * t) = 1 := by
          rw [← mul_assoc, he₀sq, hht]
        exact inv_eq_of_mul_eq_one_right this
      calc e₁ = (e₁ * e₀⁻¹) * e₀ := by group
        _ = t * e₀ := by rw [h]
        _ = e₀ * t := hcomm _ htW _ he₀W.2
        _ = e₀⁻¹ := hinv.symm
  have hrW : ∀ x ∈ W, σ.r * x * σ.r⁻¹ ∈ W := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp σ.r_mem_normalizer x).mp hx
  rcases hcase with hB | hA
  ·
    refine ⟨g₁⁻¹, ⟨ρ₁.K.inv_mem hg₁.1, W.inv_mem hg₁W⟩, by rw [orderOf_inv]; exact ho₁, ?_⟩
    have hy : g₀ * g₁⁻¹ ∈ W := W.mul_mem hg₀W (W.inv_mem hg₁W)
    refine c.rep_le_centralizer σ hy ?_
    have h1 : σ.r * (g₀ * g₁⁻¹) * σ.r⁻¹ = g₀ * g₁⁻¹ := by
      have hinv₁ : σ.r * g₁⁻¹ * σ.r⁻¹ = (e₁ * g₁)⁻¹ := by rw [← hge₁]; group
      calc σ.r * (g₀ * g₁⁻¹) * σ.r⁻¹ = (σ.r * g₀ * σ.r⁻¹) * (σ.r * g₁⁻¹ * σ.r⁻¹) := by group
        _ = (e₀ * g₀) * (e₁ * g₁)⁻¹ := by rw [hge₀, hinv₁]
        _ = (e₀ * g₀) * (e₀ * g₁)⁻¹ := by rw [hB]
        _ = (e₀ * g₀) * (g₁⁻¹ * e₀⁻¹) := by group
        _ = g₀ * g₁⁻¹ * (e₀ * e₀⁻¹) := by
            have h3 := hcomm _ he₀W.2 _ hg₀W
            have h4 := hcomm _ he₀W.2 _ (W.inv_mem hg₁W)
            calc (e₀ * g₀) * (g₁⁻¹ * e₀⁻¹) = (g₀ * e₀) * (g₁⁻¹ * e₀⁻¹) := by rw [h3]
              _ = g₀ * (e₀ * g₁⁻¹) * e₀⁻¹ := by group
              _ = g₀ * (g₁⁻¹ * e₀) * e₀⁻¹ := by rw [h4]
              _ = g₀ * g₁⁻¹ * (e₀ * e₀⁻¹) := by group
        _ = g₀ * g₁⁻¹ := by group
    exact mul_inv_eq_iff_eq_mul.mp h1
  ·
    refine ⟨g₁, hg₁, ho₁, ?_⟩
    have hy : g₀ * g₁ ∈ W := W.mul_mem hg₀W hg₁W
    refine c.rep_le_centralizer σ hy ?_
    have h1 : σ.r * (g₀ * g₁) * σ.r⁻¹ = g₀ * g₁ := by
      calc σ.r * (g₀ * g₁) * σ.r⁻¹ = (σ.r * g₀ * σ.r⁻¹) * (σ.r * g₁ * σ.r⁻¹) := by group
        _ = (e₀ * g₀) * (e₁ * g₁) := by rw [hge₀, hge₁]
        _ = (e₀ * g₀) * (e₀⁻¹ * g₁) := by rw [hA]
        _ = (g₀ * e₀) * (e₀⁻¹ * g₁) := by rw [hcomm _ he₀W.2 _ hg₀W]
        _ = g₀ * (e₀ * e₀⁻¹) * g₁ := by group
        _ = g₀ * g₁ := by group
    exact mul_inv_eq_iff_eq_mul.mp h1

theorem exists_orderOf_four_mem_inf_W
    (c : Q3CL.Thompson.Ctx Ω W) (ρ : Rep Ω W) :
    ∃ g : G, g ∈ ρ.K ⊓ W ∧ orderOf g = 4 := by
  obtain ⟨hKW, -, hcyc, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW ρ.hR ρ.hK ρ.hRK
  have hp2 : IsPGroup 2 ↥(ρ.K ⊓ W) := by
    rw [← hKW]
    exact ρ.hRK.2.1.to_le inf_le_left
  have hcyc' : IsCyclic ↥(ρ.K ⊓ W) := hKW ▸ hcyc
  have h4' : 4 ≤ Nat.card ↥(ρ.K ⊓ W) := hKW ▸ h4
  obtain ⟨x, hx, hx4⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic hp2 hcyc' h4'
  exact ⟨x, hx, hx4⟩
end C22G
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
