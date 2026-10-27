module

public import CFSG.LargeExtraspecial.AS35CS64Shape

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Literature.FSmith

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem false_of_sq_eq [IsSimpleGroup G] (hn : 3 ≤ S.width)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {g y : G} (hgy : g * S.z * g⁻¹ = y) (hyM : y ∈ S.M) (hyz : y ≠ S.z)
    {t : G} (htQ : t ∈ S.QG) (hty : t ∈ S.Qa g) (ht1 : t ≠ 1)
    {a : G} (haM : a ∈ S.M) (hat : a * t = t * a) (ha2 : a ^ 2 = y)
    (hD : ∀ b ∈ S.QG, b * y = y * b → a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = t) :
    False := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set τ : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ ⟨y, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hτ
  set κ : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ ⟨a, haM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hκ
  have hy2 : y * y = 1 := by rw [← hgy]; exact S.conj_mul_self g
  have hτ2 : τ * τ = 1 := S.ρ_mul_self hyM (by rw [pow_two]; exact hy2)
  have hOτ : τ ∈ TauCeti.QuadraticMap.orthogonalGroup S.q := (S.ρ ⟨y, hyM⟩).2
  have hOκ : κ ∈ TauCeti.QuadraticMap.orthogonalGroup S.q := (S.ρ ⟨a, haM⟩).2
  have hlam := S.conj_ne_mul_z_of_mem_Qa hn hW hgy hyM hyz htQ hty ht1
  obtain ⟨s, hs⟩ := S.exists_commSpace_cases hn hW hgy hyM hyz htQ hty ht1
  have hq : ∀ u ∈ commSpace τ, S.q u = 0 := fun u hu => S.q_commSpace_eq_zero hyM hy2 hlam hu
  have hne : g * S.z * g⁻¹ ≠ S.z := by rw [hgy]; exact hyz
  have ht2 : t * t = 1 := S.mul_self_eq_one_of_mem_Qa hne htQ hty
  have htz : t ≠ S.z := fun h => S.z_not_mem_Qa hW hne (h ▸ hty)
  have hκt : κ (S.cl t) = S.cl t := by
    rw [hκ, S.ρ_cl ⟨a, haM⟩ htQ]
    congr 1
    change a * t * a⁻¹ = t
    rw [hat, mul_inv_cancel_right]
  have caseA : ∀ b ∈ S.QG, b * y = y * b → κ (S.cl b) = S.cl b ∨ κ (S.cl b) = S.cl b + S.cl t := by
    intro b hbQ hby
    have hkQ : a * b * a⁻¹ * b⁻¹ ∈ S.QG := mul_mem (S.conj_mem_QG haM hbQ) (inv_mem hbQ)
    have e : κ (S.cl b) = S.cl (a * b * a⁻¹ * b⁻¹) + S.cl b := by
      rw [hκ, S.ρ_cl ⟨a, haM⟩ hbQ, ← S.cl_mul hkQ hbQ]
      congr 1
      change a * b * a⁻¹ = a * b * a⁻¹ * b⁻¹ * b
      group
    rcases hD b hbQ hby with h | h
    · left
      rw [e, h, S.cl_one, zero_add]
    · right
      rw [e, h, add_comm]
  have key : ∀ f ∈ S.QG, f * t = t * f →
      κ (S.cl f) = S.cl f ∨ κ (S.cl f) = S.cl f + S.cl t := by
    intro f hfQ hft
    by_cases hfix : τ (S.cl f) = S.cl f
    · exact caseA f hfQ (S.commute_of_fix hyM hlam hfQ hfix)
    have hvt : polar S.q (S.cl f) (S.cl t) = 0 := (S.polar_cl_eq_zero_iff hfQ htQ).mpr hft
    have hr : κ (S.cl f) - S.cl f ∈ commSpace τ := by
      rw [S.commSpace_eq_orthogonal hOτ hτ2, LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      rw [polarBilin_apply_apply]
      obtain ⟨b, hbQ, rfl⟩ := S.exists_cl w
      have hby := S.commute_of_fix hyM hlam hbQ (mem_fixSpace.mp hw)
      have h1 : polar S.q (κ (S.cl b)) (κ (S.cl f)) = polar S.q (S.cl b) (S.cl f) :=
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hOκ _ _
      have h2 : polar S.q (S.cl t) (κ (S.cl f)) = 0 := by
        rw [← hκt, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hOκ, polar_comm, hvt]
      have h3 : polar S.q (S.cl b) (κ (S.cl f)) = polar S.q (S.cl b) (S.cl f) := by
        rcases caseA b hbQ hby with h | h
        · rwa [h] at h1
        · rwa [h, polar_add_left, h2, add_zero] at h1
      rw [polar_sub_right, h3, sub_self]
    have hvr : polar S.q (S.cl f) (κ (S.cl f) - S.cl f) = 0 := by
      have h1 : S.q (κ (S.cl f)) = S.q (S.cl f) :=
        TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hOκ _
      have h2 : κ (S.cl f) = S.cl f + (κ (S.cl f) - S.cl f) := by abel
      rw [h2, map_add_eq, hq _ hr, add_zero] at h1
      simpa using h1
    have hκf : κ (S.cl f) = S.cl f + (κ (S.cl f) - S.cl f) := by abel
    have hfix' : polar S.q (S.cl f) s = 0 → τ (S.cl f) = S.cl f := by
      intro hvs
      have hmem : S.cl f ∈ fixSpace τ := by
        rw [fixSpace_eq_orthogonal_commSpace S.q_nondegenerate hOτ hτ2,
          LinearMap.BilinForm.mem_orthogonal_iff]
        intro u hu
        rw [polarBilin_apply_apply]
        rcases hs u hu with h | h | h | h <;> rw [h]
        · exact polar_zero_left S.q (S.cl f)
        · rw [polar_comm, hvt]
        · rw [polar_comm, hvs]
        · rw [polar_add_left, polar_comm, hvt, polar_comm, hvs, add_zero]
      exact mem_fixSpace.mp hmem
    rcases hs _ hr with h | h | h | h
    · left
      rw [hκf, h, add_zero]
    · right
      rw [hκf, h]
    · exact absurd (hfix' (by rw [← h]; exact hvr)) hfix
    · have h' : polar S.q (S.cl f) (S.cl t + s) = 0 := by rw [← h]; exact hvr
      rw [polar_add_right, hvt, zero_add] at h'
      exact absurd (hfix' h') hfix
  have hz : ∀ f ∈ S.QG, f * t = t * f → y * f = f * y := by
    intro f hfQ hft
    have hafQ : a * f * a⁻¹ ∈ S.QG := S.conj_mem_QG haM hfQ
    obtain ⟨m, hm1, hm2, hm3⟩ : ∃ m : G, a * f * a⁻¹ = f * m ∧ a * m = m * a ∧ m * m = 1 := by
      have htzc : t * S.z = S.z * t := S.z_comm_QG htQ
      rcases key f hfQ hft with h | h
      · rw [hκ, S.ρ_cl ⟨a, haM⟩ hfQ] at h
        rcases (S.cl_eq_cl_iff hfQ hafQ).mp h.symm with h' | h'
        · exact ⟨1, by rw [h', mul_one], by group, by group⟩
        · exact ⟨S.z, h', S.z_comm haM, S.z_mul_z⟩
      · rw [hκ, S.ρ_cl ⟨a, haM⟩ hfQ, ← S.cl_mul hfQ htQ] at h
        rcases (S.cl_eq_cl_iff (mul_mem hfQ htQ) hafQ).mp h.symm with h' | h'
        · exact ⟨t, h', hat, ht2⟩
        · refine ⟨t * S.z, by rw [h', mul_assoc], ?_, ?_⟩
          · rw [← mul_assoc, hat, mul_assoc, S.z_comm haM, mul_assoc]
          · calc t * S.z * (t * S.z) = t * t * (S.z * S.z) := by
                  rw [mul_assoc t S.z, ← mul_assoc S.z t, ← htzc]; group
              _ = 1 := by rw [ht2, S.z_mul_z, mul_one]
    have hconj : y * f * y⁻¹ = f := by
      rw [← ha2, pow_two]
      calc a * a * f * (a * a)⁻¹ = a * (a * f * a⁻¹) * a⁻¹ := by group
        _ = a * (f * m) * a⁻¹ := by rw [hm1]
        _ = (a * f * a⁻¹) * (a * m * a⁻¹) := by group
        _ = f * m * m := by rw [hm1, hm2, mul_inv_cancel_right, mul_assoc]
        _ = f := by rw [mul_assoc, hm3, mul_one]
    calc y * f = y * f * y⁻¹ * y := by group
      _ = f * y := by rw [hconj]
  have hfixsup : LinearMap.BilinForm.orthogonal S.q.polarBilin
      (Submodule.span (ZMod 2) {S.cl t}) ≤ fixSpace τ := by
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw
    have hwt := hw (S.cl t) (Submodule.mem_span_singleton_self _)
    rw [polarBilin_apply_apply] at hwt
    obtain ⟨f, hfQ, rfl⟩ := S.exists_cl w
    have hft : f * t = t * f :=
      (S.polar_cl_eq_zero_iff hfQ htQ).mp (by rw [polar_comm]; exact hwt)
    rw [mem_fixSpace, hτ, S.ρ_cl ⟨y, hyM⟩ hfQ]
    congr 1
    change y * f * y⁻¹ = f
    rw [hz f hfQ hft, mul_inv_cancel_right]
  have hle : commSpace τ ≤ Submodule.span (ZMod 2) {S.cl t} := by
    rw [S.commSpace_eq_orthogonal hOτ hτ2]
    calc LinearMap.BilinForm.orthogonal S.q.polarBilin (fixSpace τ) ≤
        LinearMap.BilinForm.orthogonal S.q.polarBilin (LinearMap.BilinForm.orthogonal
          S.q.polarBilin (Submodule.span (ZMod 2) {S.cl t})) :=
          LinearMap.BilinForm.orthogonal_le hfixsup
      _ = Submodule.span (ZMod 2) {S.cl t} :=
          LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl _
  have hcl0 : S.cl t ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff htQ).mp h with h' | h'
    · exact ht1 h'
    · exact htz h'
  have h1 : finrank (ZMod 2) (commSpace τ) ≤ 1 := by
    have := Submodule.finrank_mono hle
    rwa [finrank_span_singleton hcl0] at this
  have hyQ : (⟨y, hyM⟩ : S.M) ∉ S.Q := fun h =>
    S.conj_not_mem_QG hW (g := g) hne (by rw [hgy]; exact ⟨_, h, rfl⟩)
  have h2 : 2 ≤ finrank (ZMod 2) (commSpace τ) := S.two_le_finrank_commSpace hn hyQ
  omega

theorem four_le_card_inf_Qa [IsSimpleGroup G] (hn : 3 ≤ S.width)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {g x : G} (hgx : g * S.z * g⁻¹ = x) (hxM : x ∈ S.M) (hxz : x ≠ S.z)
    {t : G} (htQ : t ∈ S.QG) (htx : t ∈ S.Qa g) (ht1 : t ≠ 1) :
    4 ≤ Nat.card ↥(S.QG ⊓ S.Qa g) := by
  by_contra hlt
  push Not at hlt
  have hne : g * S.z * g⁻¹ ≠ S.z := by rw [hgx]; exact hxz
  have hD : ∀ d ∈ S.QG ⊓ S.Qa g, d = 1 ∨ d = t := by
    intro d hd
    by_contra hcon
    push Not at hcon
    obtain ⟨hd1, hdt⟩ := hcon
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥(S.QG ⊓ S.Qa g) := S.isPGroup_QG.to_le inf_le_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    have hsub : ({1, t, d} : Set G) ⊆ ((S.QG ⊓ S.Qa g : Subgroup G) : Set G) := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · exact one_mem _
      · exact mem_inf.mpr ⟨htQ, htx⟩
      · exact hd
    have hcard : ({1, t, d} : Set G).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair hdt.symm]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ht1.symm, hd1.symm⟩
    have h3 : 3 ≤ Nat.card ↥(S.QG ⊓ S.Qa g) := by
      have hc : Nat.card ↥(S.QG ⊓ S.Qa g) = ((S.QG ⊓ S.Qa g : Subgroup G) : Set G).ncard :=
        Nat.card_coe_set_eq ((S.QG ⊓ S.Qa g : Subgroup G) : Set G)
      rw [hc, ← hcard]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hk] at h3 hlt
    rcases k with _ | _ | k
    · rw [pow_zero] at h3
      omega
    · rw [pow_one] at h3
      omega
    · have h4 : 4 ≤ 2 ^ (k + 2) := by
        rw [pow_add]
        have := Nat.one_le_two_pow (n := k)
        omega
      omega
  obtain ⟨a, haQ, hax, ha2⟩ := S.exists_sq_eq_z_of_mem_Qa hn hW hgx hxM hxz htQ htx ht1
  set T := S.conjBy g with hT
  have hTz : T.z = x := by rw [hT, conjBy_z, hgx]
  have hTn : 3 ≤ T.width := by rw [hT, S.width_conjBy]; exact hn
  have hWT := S.weaklyClosed_conjBy hW g
  have hzT : g⁻¹ * T.z * g⁻¹⁻¹ = S.z := by rw [hTz, ← hgx]; group
  have hzMT : S.z ∈ T.M := by rw [T.mem_M_iff, hTz]; exact (S.z_comm hxM).symm
  have hzneT : S.z ≠ T.z := by rw [hTz]; exact hxz.symm
  have htT : t ∈ T.QG := htx
  have htTa : t ∈ T.Qa g⁻¹ := by rw [hT, S.Qa_conjBy, inv_mul_cancel, S.Qa_one]; exact htQ
  have haT : a ∈ T.M := by rw [T.mem_M_iff, hTz]; exact hax
  have hzQa : S.z ∉ S.Qa g := S.z_not_mem_Qa hW hne
  have hat : a * t = t * a := by
    rcases S.commutator_eq_one_or_z haQ htQ with h | h
    · calc a * t = a * t * a⁻¹ * t⁻¹ * (t * a) := by group
        _ = t * a := by rw [h, one_mul]
    · exfalso
      apply hzQa
      rw [← h]
      exact mul_mem (T.conj_mem_QG haT htT) (inv_mem htT)
  refine T.false_of_sq_eq hTn hWT hzT hzMT hzneT htT htTa ht1 haT hat ha2 ?_
  intro b hbQ hbz
  have hbM : b ∈ S.M := S.mem_M_iff.mpr hbz
  have hkQ : a * b * a⁻¹ * b⁻¹ ∈ S.QG := by
    have := mul_mem haQ (S.conj_mem_QG hbM (inv_mem haQ))
    simpa [mul_assoc] using this
  have hkT : a * b * a⁻¹ * b⁻¹ ∈ S.Qa g := mul_mem (T.conj_mem_QG haT hbQ) (inv_mem hbQ)
  exact hD _ (mem_inf.mpr ⟨hkQ, hkT⟩)

end Setting

end CFSG.LargeExtraspecial
