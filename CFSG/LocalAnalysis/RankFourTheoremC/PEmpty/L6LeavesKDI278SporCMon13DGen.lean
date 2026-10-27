module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.NonabelianCube
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13

open Subgroup

theorem exists_conj_mem_of_elemAbelian_sq {G : Type*} [Group G] [Finite G] {S₀ : Subgroup G}
    {c : G} (hSp : IsPGroup 13 S₀)
    (hSmax : ∀ T : Subgroup G, IsPGroup 13 T → S₀ ≤ T → T = S₀)
    (hScard : Nat.card S₀ = 13 ^ 3)
    (hSnab : ∃ a ∈ S₀, ∃ b ∈ S₀, a * b ≠ b * a)
    (hcS : c ∈ S₀) (hcc : ∀ s ∈ S₀, c * s = s * c)
    {R : Subgroup G} (hR : CFSG.Open.IsElemAbelian 13 R) (hR2 : Nat.card R = 13 ^ 2) :
    ∃ g : G, g * c * g⁻¹ ∈ R := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨Q, hRQ⟩ := IsPGroup.exists_le_sylow hR.isPGroup
  let T₀ : Sylow 13 G := ⟨S₀, hSp, fun hT hle => hSmax _ hT hle⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T₀ Q
  have hR' : ∀ r ∈ R, g⁻¹ * r * g ∈ S₀ := by
    intro r hr
    have h1 : r ∈ (↑(g • T₀) : Set G) := by
      rw [hg]
      exact hRQ hr
    rw [Sylow.coe_smul, Set.mem_smul_set] at h1
    obtain ⟨s, hs, hsr⟩ := h1
    have hsr' : g * s * g⁻¹ = r := hsr
    have hs' : s = g⁻¹ * r * g := by
      rw [← hsr']
      group
    rw [← hs']
    exact hs
  let φ : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  have hφinj : Function.Injective φ := (MulAut.conj g⁻¹).injective
  set R' : Subgroup G := R.map φ with hR'def
  have hR'S : R' ≤ S₀ := by
    rintro x ⟨r, hr, rfl⟩
    show g⁻¹ * r * g⁻¹⁻¹ ∈ S₀
    rw [inv_inv]
    exact hR' r hr
  have hR'card : Nat.card R' = 13 ^ 2 := by
    rw [hR'def, ← Nat.card_congr (R.equivMapOfInjective φ hφinj).toEquiv, hR2]
  have hT2 : Nat.card (R'.subgroupOf S₀) = 13 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR'S).toEquiv, hR'card]
  have hnab' : ∃ a b : S₀, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hSnab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  obtain ⟨-, -, -, -, -, hT, -⟩ :=
    CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure (p := 13) hScard hnab'
  have hz : (⟨c, hcS⟩ : S₀) ∈ Subgroup.center S₀ :=
    Subgroup.mem_center_iff.2 fun w => Subtype.ext (hcc w.1 w.2).symm
  have hcT := (hT (R'.subgroupOf S₀) hT2).1 hz
  have hcR' : c ∈ R' := Subgroup.mem_subgroupOf.1 hcT
  obtain ⟨r, hr, hrc⟩ := Subgroup.mem_map.1 hcR'
  refine ⟨g, ?_⟩
  have hrc' : g⁻¹ * r * g⁻¹⁻¹ = c := hrc
  rw [inv_inv] at hrc'
  have hrgc : r = g * c * g⁻¹ := by
    rw [← hrc']
    group
  rw [← hrgc]
  exact hr

theorem mem_normalizer_of_orderOf_thirteen {Γ : Type*} [Group Γ] {Y : Subgroup Γ} {d : Γ}
    (hd : orderOf d = 13) (hdY : ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) :
    d ∈ normalizer (Y : Set Γ) := by
  have hd13 : d ^ 13 = 1 := by
    rw [← hd]
    exact pow_orderOf_eq_one d
  have hdinv : d⁻¹ = d ^ 12 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hd13
  have hpow : ∀ n : ℕ, ∀ y ∈ Y, d ^ n * y * (d ^ n)⁻¹ ∈ Y := by
    intro n
    induction n with
    | zero =>
      intro y hy
      simpa using hy
    | succ n ih =>
      intro y hy
      have h := hdY _ (ih y hy)
      rw [pow_succ']
      convert h using 1
      group
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hdY h hh, fun hh => ?_⟩
  have h2 := hpow 12 _ hh
  convert h2 using 1
  rw [← hdinv]
  group

theorem card_modEq_one_of_fixed {Γ : Type*} [Group Γ] [Finite Γ] {Y : Subgroup Γ} {d : Γ}
    (hd : orderOf d = 13) (hdY : ∀ y ∈ Y, d * y * d⁻¹ ∈ Y)
    (hfix : ∀ y ∈ Y, d * y = y * d → y = 1) :
    Nat.card Y ≡ 1 [MOD 13] := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hdN : d ∈ normalizer (Y : Set Γ) := mem_normalizer_of_orderOf_thirteen hd hdY
  have hN : zpowers d ≤ normalizer (Y : Set Γ) := Subgroup.zpowers_le.2 hdN
  letI act : MulAction (zpowers d) Y :=
    { smul := fun k y => ⟨(k : Γ) * (y : Γ) * (k : Γ)⁻¹,
        (mem_normalizer_iff.1 (hN k.2) y).1 y.2⟩
      one_smul := fun y => Subtype.ext (by
        show ((1 : zpowers d) : Γ) * (y : Γ) * ((1 : zpowers d) : Γ)⁻¹ = (y : Γ)
        simp)
      mul_smul := fun k₁ k₂ y => Subtype.ext (by
        show ((k₁ * k₂ : zpowers d) : Γ) * (y : Γ) * ((k₁ * k₂ : zpowers d) : Γ)⁻¹ =
          (k₁ : Γ) * ((k₂ : Γ) * (y : Γ) * (k₂ : Γ)⁻¹) * (k₁ : Γ)⁻¹
        rw [Subgroup.coe_mul]
        group) }
  have hp : IsPGroup 13 (zpowers d) :=
    IsPGroup.of_card (p := 13) (n := 1) (by rw [Nat.card_zpowers, hd, pow_one])
  have hfixcard : Nat.card (MulAction.fixedPoints (zpowers d) Y) = 1 := by
    have hsub : ∀ a : MulAction.fixedPoints (zpowers d) Y, a.1 = 1 := by
      rintro ⟨a, ha⟩
      have h1 : (⟨d, Subgroup.mem_zpowers d⟩ : zpowers d) • a = a :=
        (MulAction.mem_fixedPoints.1 ha) _
      have h2 : d * (a : Γ) * d⁻¹ = a := congrArg Subtype.val h1
      have h4 : d * (a : Γ) = (a : Γ) * d := by
        calc d * (a : Γ) = d * (a : Γ) * d⁻¹ * d := by group
          _ = (a : Γ) * d := by rw [h2]
      exact Subtype.ext (hfix a a.2 h4)
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ((hsub a).trans (hsub b).symm)⟩,
      ⟨⟨⟨1, Y.one_mem⟩, MulAction.mem_fixedPoints.2 fun k => Subtype.ext (by
        show (k : Γ) * 1 * (k : Γ)⁻¹ = 1
        simp)⟩⟩⟩
  have h1 := hp.card_modEq_card_fixedPoints Y
  rw [hfixcard] at h1
  exact h1

theorem false_of_index_le_three {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hcard : 6 < Nat.card Q) {M : Subgroup Q} (hM : M ≠ ⊤) (hidx : M.index ≤ 3) : False := by
  rcases Subgroup.Normal.eq_bot_or_eq_top M.normalCore with h | h
  · have h1 := M.index_normalCore_le_factorial_index
    rw [h, Subgroup.index_bot] at h1
    have h2 : M.index.factorial ≤ (3 : ℕ).factorial := Nat.factorial_le hidx
    have h3 : (3 : ℕ).factorial = 6 := rfl
    omega
  · exact hM (top_le_iff.1 (h ▸ M.normalCore_le))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13
