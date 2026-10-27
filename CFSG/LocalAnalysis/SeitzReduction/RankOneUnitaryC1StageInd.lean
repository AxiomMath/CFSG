module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageBranchNu

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

structure U3C1LevelData (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G)
    (T : Subgroup G) (d : G) (V U U₁ : Subgroup G) (k : ℕ) : Prop where
  U_le : U ≤ normalizer (szR (szT₁ L T) V t : Set G)
  U_normal : normalizer (szR (szT₁ L T) V t : Set G) ≤ normalizer (U : Set G)
  isSylowOf : IsSylowOf 2 U (normalizer (szR (szT₁ L T) V t : Set G))
  card_U : Nat.card U = 2 * (2 ^ f) ^ (k + 4)
  szR_le : szR (szT₁ L T) V t ≤ U
  conj_t_not_mem : ∀ u ∈ U, u ∉ szR (szT₁ L T) V t → u * t * u⁻¹ ∉ szA L T t
  conj_szA₁ : ∀ u ∈ U, ∀ b ∈ szA₁ (szT₁ L T), u * b * u⁻¹ = b
  conj_T₁ : ∀ u ∈ U, ∀ y ∈ szT₁ L T, y⁻¹ * (u * y * u⁻¹) ∈ szA₁ (szT₁ L T)
  conj_V₁ : ∀ u ∈ U₁, ∀ r ∈ V, r⁻¹ * (u * r * u⁻¹) ∈ szA₁ (szT₁ L T)
  inf_centralizer : U ⊓ centralizer ({t} : Set G) = szT₁ L T ⊔ zpowers t
  U₁_le : U₁ ≤ U
  U₁_normal : U ≤ normalizer (U₁ : Set G)
  sup_eq : U₁ ⊔ zpowers t = U
  t_not_mem : t ∉ U₁
  inf_eq : U₁ ⊓ szR (szT₁ L T) V t = szT₁ L T ⊔ V
  d_mem_U₁ : d ∈ normalizer (U₁ : Set G)

@[expose] def U3C1NuInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (k : ℕ), U3C1Stage G L f t T d V U U₁ k → U3C1TorusFpf L T d →
    U3C1TorusScalar L T f d →
    U₁ ≤ centralizer (V : Set G) → U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) →
    (∃ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 ≠ 1) →
    ¬ (∃ S : Sylow 2 G, (S : Subgroup G) = U) → False

@[expose] def U3C1NextInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (k : ℕ), U3C1Stage G L f t T d V U U₁ k → U3C1TorusFpf L T d →
    U3C1TorusScalar L T f d →
    U₁ ≤ centralizer (V : Set G) → U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) →
    (∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) →
    ¬ (∃ S : Sylow 2 G, (S : Subgroup G) = U) →
    ∃ U' U₁' : Subgroup G,
      U3C1LevelData G L f t T d (U₁ ⊓ centralizer (szT₁ L T : Set G)) U' U₁' (k + 1)

namespace U3C1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

theorem next (h : U3C1Stage G L f t T d V U U₁ k)
    (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) {U' U₁' : Subgroup G}
    (hD : U3C1LevelData G L f t T d (U₁ ⊓ centralizer (szT₁ L T : Set G)) U' U₁' (k + 1)) :
    U3C1Stage G L f t T d (U₁ ⊓ centralizer (szT₁ L T : Set G)) U' U₁' (k + 1) := by
  obtain ⟨hC, hcomm, hcard, hΩ, hpow, hle, hinv, hd⟩ := h.nextConf hμV hlam hν
  exact
    { start := h.start
      card_sylow := h.card_sylow
      T_le := h.T_le
      one_le := by omega
      coords := h.coords
      d_odd := h.d_odd
      d_norm := hd
      le_centralizer := hC
      comm := hcomm
      card := hcard
      omega := hΩ
      pow := hpow
      le := hle
      inv := hinv
      U_le := hD.U_le
      U_normal := hD.U_normal
      isSylowOf := hD.isSylowOf
      card_U := hD.card_U
      szR_le := hD.szR_le
      conj_t_not_mem := hD.conj_t_not_mem
      conj_szA₁ := hD.conj_szA₁
      conj_T₁ := hD.conj_T₁
      conj_V₁ := hD.conj_V₁
      inf_centralizer := hD.inf_centralizer
      U₁_le := hD.U₁_le
      U₁_normal := hD.U₁_normal
      sup_eq := hD.sup_eq
      t_not_mem := hD.t_not_mem
      inf_eq := hD.inf_eq
      d_mem_U₁ := hD.d_mem_U₁ }

theorem false_of_inputs (hnu : U3C1NuInput)
    (hnext : U3C1NextInput) (h : U3C1Stage G L f t T d V U U₁ k)
    (hfpf : U3C1TorusFpf L T d) (hsc : U3C1TorusScalar L T f d) : False := by
  suffices key : ∀ (m : ℕ) (V U U₁ : Subgroup G) (k : ℕ), Nat.card G - Nat.card V = m →
      U3C1Stage G L f t T d V U U₁ k → False from key _ V U U₁ k rfl h
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro V U U₁ k hm h
    obtain ⟨hU, hμV, hlam, hν | ⟨hν, -⟩⟩ := h.reduction_nu hfpf
    · obtain ⟨U', U₁', hD⟩ := hnext G L f t T d V U U₁ k h hfpf hsc hμV hlam hν hU
      have h' := h.next hμV hlam hν hD
      refine ih _ ?_ _ _ _ _ rfl h'
      have h1 : Nat.card V < Nat.card (U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) := by
        rw [h.card, h'.card]
        exact Nat.pow_lt_pow_right h.one_lt_q (by omega)
      have h2 := Subgroup.card_le_card_group (U₁ ⊓ centralizer (szT₁ L T : Set G))
      omega
    · exact hnu G L f t T d V U U₁ k h hfpf hsc hμV hlam hν hU

end U3C1Stage

section Certificates

theorem u3C1InnerExclusion_of_inputs (hreg : U3C1RegularInput) (htor : U3C1TorusFullInput)
    (hnu : U3C1NuInput) (hnext : U3C1NextInput) : U3C1InnerExclusion := by
  intro G _ _ L f t T R₂ h hS2 hR hinv hne hT
  obtain ⟨E, hEY, hEn, -, hEA, -, htr⟩ := hreg G L f t T R₂ h hS2 hR hinv hne hT
  obtain ⟨d, hdodd, hdR, hdT, hdt, hfpf, hsc, K, _, _, _, v, μ, hK, hc, hμ⟩ :=
    htor G L f t T R₂ h hS2 hR
  obtain ⟨U₁, hst⟩ := U3C1Stage.of_data h hS2 hR hinv hne hT hEY hEn hEA htr hdodd hdR hdT hdt
    hK hc hμ
  exact hst.false_of_inputs hnu hnext hfpf hsc

end Certificates

end CFSG.SeitzReduction.RankOne
