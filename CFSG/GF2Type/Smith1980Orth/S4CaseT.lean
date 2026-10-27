module

public import CFSG.GF2Type.Smith1980Orth.S4Common
public import CFSG.GF2Type.Smith1980Orth.S4Kbar
public import CFSG.GF2Type.Smith1980Orth.S4SiegelD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem rho_ne_of_orderOf_eq_three {a b : G} (ha : IsConj S.z a) (haM : a ∈ S.M)
    (hbM : b ∈ S.M) (h3 : orderOf (a * b) = 3) : S.ρ ⟨a, haM⟩ ≠ S.ρ ⟨b, hbM⟩ := by
  intro e
  have haa : a * a = 1 := S14.SmithQ.mul_self_eq_one_of_isConj S ha
  have h1 : S.ρ ⟨a * b, S.M.mul_mem haM hbM⟩ = 1 := by
    have : (⟨a * b, S.M.mul_mem haM hbM⟩ : S.M) = ⟨a, haM⟩ * ⟨b, hbM⟩ := rfl
    rw [this, map_mul, ← e, ← map_mul]
    have : (⟨a, haM⟩ : S.M) * ⟨a, haM⟩ = 1 := Subtype.ext haa
    rw [this, map_one]
  have hQ := (S.ρ_eq_one_iff _).mp h1
  have h4 := S.pow_four_eq_one hQ
  have := orderOf_dvd_of_pow_eq_one h4
  rw [h3] at this
  norm_num at this

namespace S2Data

variable (D : S2Data S)

local notation "ρV" => D.resC

theorem exists_fix_not_comm (hw6 : 6 ≤ S.width) {c : D.Cbar} (hc : IsTypeA D.QV (ρV c) 2) :
    ∃ a ∈ fixSpace (ρV c), a ∉ commSpace (ρV c) := by
  by_contra h
  push Not at h
  have hle : fixSpace (ρV c) ≤ commSpace (ρV c) := h
  have h1 := finrank_commSpace_add_finrank_fixSpace (ρV c)
  have h2 := Submodule.finrank_mono hle
  rw [D.finrank_Vt, hc.2.2.2.1] at h1
  rw [hc.2.2.2.1] at h2
  omega

theorem false_of_isTInv_at (h0 : SixAt S) {x w kv : G} (hxM : x ∈ S.M) (hwM : w ∈ S.M)
    (hxT : D.IsTInv (S.ρ ⟨x, hxM⟩)) (hwT : D.IsTInv (S.ρ ⟨w, hwM⟩)) (h3 : (x * w) ^ 3 = 1)
    (hvM : kv * S.z * kv⁻¹ ∈ S.M) (hvC : S.ρ ⟨_, hvM⟩ ∈ D.Cbar)
    (hvU : IsTypeA D.QV (ρV ⟨_, hvC⟩) 2) (hθv : Commute (x * w) (kv * S.z * kv⁻¹))
    (hTv : ∀ q ∈ S.Qa kv, (x * w) * q = q * (x * w) → q = 1 ∨ q = kv * S.z * kv⁻¹) :
    False := by
  have hθM : x * w ∈ S.M := S.M.mul_mem hxM hwM
  have hvQ : kv * S.z * kv⁻¹ ∉ S.QG := by
    intro hQ
    apply hvU.2.1
    have h1 : S.ρ ⟨_, hvM⟩ = 1 := (S.ρ_eq_one_iff _).mpr hQ
    have h2 : (⟨_, hvC⟩ : D.Cbar) = 1 := Subtype.ext h1
    rw [h2, map_one]
  have hvz := h0.e34a _ (isConj_iff.mpr ⟨kv, rfl⟩) hvM hvQ
  have hfix := SMK.fixQt_eq_of_not_isConj S hvM hvz
  have hΔle := SMK.clSub_Dl_le_commQt S hvM hvQ hvz
  obtain ⟨a₀, ha₀, ha₀P⟩ := D.exists_fix_not_comm h0.six_le hvU
  have hKC := D.lbar_mem_Cbar hvM hvC hfix hΔle ha₀ ha₀P
  have hθρ : S.ρ ⟨x * w, hθM⟩ = S.ρ ⟨x, hxM⟩ * S.ρ ⟨w, hwM⟩ := by
    rw [← map_mul]
    rfl
  have hcommC : ∀ c ∈ D.Cbar, S.ρ ⟨x * w, hθM⟩ * c = c * S.ρ ⟨x * w, hθM⟩ := by
    intro c hc
    rw [hθρ, mul_assoc, D.comm_of_isTInv_of_mem_Cbar hwT hc, ← mul_assoc,
      D.comm_of_isTInv_of_mem_Cbar hxT hc, mul_assoc]
  have hsub : ∀ ℓ ∈ S.Lbar kv, ℓ = 1 ∨ ℓ = S.ρ ⟨_, hvM⟩ := by
    rintro ℓ hℓ
    obtain ⟨m, hm, rfl⟩ := hℓ
    have hmL : (m : G) ∈ S.L0 kv := mem_subgroupOf.mp hm
    obtain ⟨hmC, -⟩ := hKC _ ⟨m, hm, rfl⟩
    have hc := hcommC _ hmC
    have hmΔ : (m : G)⁻¹ * ((x * w) * m * (x * w)⁻¹) ∈ S.QG ⊓ S.Qa kv := by
      refine ⟨S.inv_mul_conj_mem_QG m.2 hθM hc, ?_⟩
      have hθT : x * w ∈ (S.conjBy kv).M := mem_centralizer_singleton_iff.mpr hθv.eq
      exact (S.conjBy kv).QG.mul_mem ((S.conjBy kv).QG.inv_mem hmL.1)
        ((S.conjBy kv).conj_mem_QG hθT hmL.1)
    have hΔp : IsPGroup 2 (S.QG ⊓ S.Qa kv : Subgroup G) :=
      (Setting.isPGroup_QG S).to_le inf_le_left
    obtain ⟨h, hh, hfixh⟩ := exists_fixed_mem_coset hΔp h3
      (fun d hd => SMK.conj_mem_Dl S hθM hθv hd) hmΔ
    have hgh : (m : G) * h ∈ S.Qa kv := (S.Qa kv).mul_mem hmL.1 hh.2
    have hgh' : (x * w) * ((m : G) * h) = ((m : G) * h) * (x * w) := by
      calc (x * w) * ((m : G) * h) = (x * w) * ((m : G) * h) * (x * w)⁻¹ * (x * w) := by group
        _ = ((m : G) * h) * (x * w) := by rw [hfixh]
    have hhM : h ∈ S.M := S.QG_le_M hh.1
    have hρh : S.ρ ⟨h, hhM⟩ = 1 := (S.ρ_eq_one_iff _).mpr hh.1
    have hρm : S.ρ m = S.ρ ⟨(m : G) * h, S.M.mul_mem m.2 hhM⟩ := by
      have : (⟨(m : G) * h, S.M.mul_mem m.2 hhM⟩ : S.M) = m * ⟨h, hhM⟩ := rfl
      rw [this, map_mul, hρh, mul_one]
    rcases hTv _ hgh hgh' with e | e
    · left
      rw [hρm]
      have : (⟨(m : G) * h, S.M.mul_mem m.2 hhM⟩ : S.M) = 1 := Subtype.ext e
      rw [this, map_one]
    · right
      rw [hρm]
      exact congrArg S.ρ (Subtype.ext e)
  have hcard : Nat.card (S.Lbar kv) ≤ 2 := by
    have hle : ((S.Lbar kv : Subgroup S.O) : Set S.O) ⊆ {1, S.ρ ⟨_, hvM⟩} := fun ℓ hℓ => by
      rcases hsub ℓ hℓ with e | e <;> simp [e]
    calc Nat.card (S.Lbar kv) = ((S.Lbar kv : Subgroup S.O) : Set S.O).ncard :=
          Nat.card_coe_set_eq _
      _ ≤ ({1, S.ρ ⟨_, hvM⟩} : Set S.O).ncard := Set.ncard_le_ncard hle (Set.toFinite _)
      _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have hmul := S.card_Lbar_mul kv
  have hL0 := SMK.card_L0_ge_succ S hvM hvQ hvz
  have hΔ := D.card_Dl_of_isUInv hvM hvQ hvz (h0.Dl_ne_bot hvM hvQ) ⟨hvC, hvU⟩
  rw [hΔ] at hmul
  have h6 := h0.six_le
  have h64 : 2 ^ 7 ≤ 2 ^ (S.width + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Nat.card (S.L0 kv) ≤ 2 * 2 ^ 4 := by
    rw [← hmul]
    exact Nat.mul_le_mul_right _ hcard
  omega

end S2Data

end CFSG.GF2Type.Smith1980Orth
