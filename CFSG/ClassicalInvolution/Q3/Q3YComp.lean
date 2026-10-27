module

public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.ClassicalInvolution.Q3.Q3YAbs

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank

@[expose] def ModelPairOrCenterless3 : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t →
    StatedLieAdmissible t n 3 1 →
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D,
    Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K = ⊥ ∨
      ∃ R' ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D,
        ∃ S ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D,
          ∀ a ∈ R', ∀ b ∈ S, a * b = b * a

namespace Q3Y

section Excluded

theorem false_of_comp_model_centerless {c : CompData} {X : Type} [Group X] (hom : c.G →* X)
    (hker : hom.ker ≤ Subgroup.center c.G) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n 3 1)
    (hc : c = CompData.model t n)
    (hcen : Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K = ⊥)
    (heven : Even (Nat.card c.G)) {z : X} (hz1 : z ≠ 1) (hzc : ∀ x : X, x * z = z * x)
    (hF : ∀ F : Subgroup X, IsElemAbelian 2 F → Nat.card F = 4 → z ∈ F) : False := by
  subst hc
  have hfin : Finite (CompData.model t n).G :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three hfund hadm
  have hq : CFSG.Open.IsQuasisimple (CompData.model t n).G :=
    ModelFacts.isQuasisimple_modelUniv t n 3 1 Nat.prime_three hfund hadm
  exact false_of_central_component hom hker hcen (isSimpleGroup_of_center_eq_bot hq hcen)
    (exists_noncomm_of_isQuasisimple hq) heven hz1 hzc hF

theorem false_of_comp_m11 {c : CompData} {X : Type} [Group X] (hom : c.G →* X)
    (hker : hom.ker ≤ Subgroup.center c.G) (hc : c = CompData.m11) (heven : Even (Nat.card c.G))
    {z : X} (hz1 : z ≠ 1) (hzc : ∀ x : X, x * z = z * x)
    (hF : ∀ F : Subgroup X, IsElemAbelian 2 F → Nat.card F = 4 → z ∈ F) : False := by
  subst hc
  have hs : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M11 := isSimpleGroup_m11_kernel
  have hfin : Finite ↥CFSG.Blueprint.NativeSporadic.M11 :=
    Nat.finite_of_card_ne_zero (by rw [card_m11_kernel]; norm_num)
  have hnab : ∃ a b : ↥CFSG.Blueprint.NativeSporadic.M11, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let _ : CommGroup ↥CFSG.Blueprint.NativeSporadic.M11 :=
      { (inferInstance : Group ↥CFSG.Blueprint.NativeSporadic.M11) with mul_comm := hcon }
    have := IsSimpleGroup.prime_card (α := ↥CFSG.Blueprint.NativeSporadic.M11)
    rw [card_m11_kernel] at this
    exact absurd this (by norm_num)
  have hcen : Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  exact false_of_central_component hom hker hcen hs hnab heven hz1 hzc hF

end Excluded

section Pair

theorem eq_top_of_mem_fund_sl23 {c : CompData} (hc : c = CompData.sl23) {R : Subgroup c.G}
    (hR : R ∈ c.fund) : R = ⊤ := by
  subst hc
  exact Set.mem_singleton_iff.mp hR

theorem exists_conj_commuting_of_pair {c : CompData}
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ} (hc : c = CompData.model t n)
    (hpair : ∃ R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D,
      ∃ R' ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D,
        ∀ a ∈ R, ∀ b ∈ R', a * b = b * a)
    (hSC : c.SingleClass) {R₂ : Subgroup c.G} (hR₂ : R₂ ∈ c.fund) :
    ∃ h : c.G, ∀ a ∈ R₂, ∀ b ∈ conjSub h R₂, a * b = b * a := by
  subst hc
  obtain ⟨R, hR, R', hR', hcomm⟩ := hpair
  obtain ⟨g₁, hg₁⟩ := hSC R hR R₂ hR₂
  obtain ⟨g₂, hg₂⟩ := hSC R hR R' hR'
  refine ⟨g₁ * g₂ * g₁⁻¹, ?_⟩
  intro a ha b hb
  rw [hg₁, mem_conjSub_iff] at ha
  rw [hg₁, mem_conjSub_iff, mem_conjSub_iff] at hb
  have hb' : g₁⁻¹ * b * g₁ ∈ R' := by
    rw [hg₂, mem_conjSub_iff]
    have : g₂⁻¹ * (g₁⁻¹ * b * g₁) * g₂ =
        g₁⁻¹ * ((g₁ * g₂ * g₁⁻¹)⁻¹ * b * (g₁ * g₂ * g₁⁻¹)) * g₁ := by group
    rw [this]
    exact hb
  have h1 := hcomm _ ha _ hb'
  have h2 := congrArg (fun x => g₁ * x * g₁⁻¹) h1
  simp only at h2
  calc a * b = g₁ * ((g₁⁻¹ * a * g₁) * (g₁⁻¹ * b * g₁)) * g₁⁻¹ := by group
    _ = g₁ * ((g₁⁻¹ * b * g₁) * (g₁⁻¹ * a * g₁)) * g₁⁻¹ := h2
    _ = b * a := by group

theorem comp_centerless_or_conj_pair {c : CompData}
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ} (hc : c = CompData.model t n)
    (hM : ModelPairOrCenterless3) (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hSC : c.SingleClass) {R₂ : Subgroup c.G}
    (hR₂ : R₂ ∈ c.fund) :
    Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K = ⊥ ∨
      ∃ h : c.G, ∀ a ∈ R₂, ∀ b ∈ conjSub h R₂, a * b = b * a := by
  have hM' := hM t n hfund hadm
  subst hc
  rcases hM' R₂ hR₂ with hcen | ⟨R, hR, R', hR', hcomm⟩
  · exact Or.inl hcen
  · exact Or.inr (exists_conj_commuting_of_pair rfl ⟨R, hR, R', hR', hcomm⟩ hSC hR₂)

end Pair

end Q3Y

section Main

variable {ι : Type} {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem LieSystemData3.exists_commuting_member (hM : ModelPairOrCenterless3)
    (D : LieSystemData3 ι X Φ) (hD : SingleClassComponents3 D) {z z₂ : X} (hz1 : z ≠ 1)
    (hz2 : z * z = 1) (hzc : ∀ x : X, x * z = z * x)
    (hF : ∀ F : Subgroup X, IsElemAbelian 2 F → Nat.card F = 4 → z ∈ F)
    (hconj : ∀ g : X, ∀ L ∈ Φ, conjSub g L ∈ Φ) {K : Subgroup X} (hK : K ∈ Φ)
    (hKcl : IsClassicalMember3 K z₂) (hne : z ≠ z₂) :
    ∃ L ∈ Φ, ∀ a ∈ L, ∀ b ∈ K, a * b = b * a := by
  obtain ⟨i₀, R₂, hR₂, hKeq⟩ := D.fundamental K hK
  by_cases hmulti : ∃ j, j ≠ i₀
  · obtain ⟨j, hj⟩ := hmulti
    obtain ⟨R, -, hRΦ⟩ := D.meets j
    refine ⟨R.map (D.hom j), hRΦ, ?_⟩
    rintro _ ⟨r, -, rfl⟩ b hb
    rw [hKeq] at hb
    obtain ⟨r₂, -, rfl⟩ := hb
    exact D.commute j i₀ hj r r₂
  · push Not at hmulti
    have hrange : (D.hom i₀).range = ⊤ := by
      have h1 : (⨆ i, (D.hom i).range) = (D.hom i₀).range :=
        le_antisymm (iSup_le fun i => by rw [hmulti i]) (le_iSup (fun i => (D.hom i).range) i₀)
      rw [← h1]
      exact D.generate
    have heven : Even (Nat.card (D.kind i₀).G) := by
      obtain ⟨R, -, hRΦ⟩ := D.meets i₀
      have h24 := D.card_eq _ hRΦ
      have h1 : Nat.card (R.map (D.hom i₀)) ∣ Nat.card R := Subgroup.card_map_dvd R (D.hom i₀)
      have h2 : Nat.card R ∣ Nat.card (D.kind i₀).G := Subgroup.card_subgroup_dvd_card R
      have h3 : 24 ∣ Nat.card (D.kind i₀).G := h24 ▸ h1.trans h2
      exact even_iff_two_dvd.mpr (dvd_trans (by norm_num) h3)
    rcases D.valid i₀ with ⟨t, n, hfund, hadm, hc⟩ | hc | hc
    · rcases Q3Y.comp_centerless_or_conj_pair hc hM hfund hadm (hD i₀) hR₂ with hcen | ⟨h, hh⟩
      · exact (Q3Y.false_of_comp_model_centerless (D.hom i₀) (D.ker_le_center i₀) hfund hadm hc
          hcen heven hz1 hzc hF).elim
      · have hL : (conjSub h R₂).map (D.hom i₀) ∈ Φ := by
          rw [← conjSub_map (D.hom i₀) h R₂, ← hKeq]
          exact hconj _ K hK
        refine ⟨(conjSub h R₂).map (D.hom i₀), hL, ?_⟩
        rintro _ ⟨a₀, ha₀, rfl⟩ b hb
        rw [hKeq] at hb
        obtain ⟨b₀, hb₀, rfl⟩ := hb
        rw [← map_mul, ← map_mul, hh b₀ hb₀ a₀ ha₀]
    · exfalso
      have hKtop : K = ⊤ := by
        rw [hKeq, Q3Y.eq_top_of_mem_fund_sl23 hc hR₂, ← MonoidHom.range_eq_map]
        exact hrange
      have hcz : Subgroup.centralizer ({z} : Set X) = ⊤ :=
        eq_top_iff.mpr fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr (hzc x)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hord : orderOf z = 2 :=
        orderOf_eq_prime_iff.mpr ⟨by rw [pow_two]; exact hz2, hz1⟩
      have hKz : IsClassicalMember3 K z :=
        { orderOf_eq_two := hord
          mem := by rw [hKtop]; exact Subgroup.mem_top z
          subnormal := by rw [hKtop, hcz]; exact IsSubnormal.refl _
          nonempty_equiv := hKcl.nonempty_equiv }
      exact hne (involution_unique3 hKz hKcl)
    · exact (Q3Y.false_of_comp_m11 (D.hom i₀) (D.ker_le_center i₀) hc heven hz1 hzc hF).elim

end Main

end CFSG.ClassicalInvolution.Q3
