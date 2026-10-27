module

public import CFSG.GF2Type.Smith1980Orth.S4CaseT
public import CFSG.GF2Type.Smith1980Orth.S4Siegel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

variable (D : S2Data S)

local notation "ρV" => D.resC

theorem eq_one_of_mem_Dl_of_commute {kv θ : G} (hvM : kv * S.z * kv⁻¹ ∈ S.M)
    (hvC : S.ρ ⟨_, hvM⟩ ∈ D.Cbar) (hvQ : kv * S.z * kv⁻¹ ∉ S.QG)
    (hΔle : S.clSub (S.QG ⊓ S.Qa kv) ≤ S.commQt (kv * S.z * kv⁻¹))
    (hθM : θ ∈ S.M) (hθC : S.ρ ⟨θ, hθM⟩ ∈ D.Cbar)
    (hfpf : ∀ v ∈ commSpace (ρV ⟨_, hvC⟩), ρV ⟨_, hθC⟩ v = v → v = 0)
    {d : G} (hd : d ∈ S.QG ⊓ S.Qa kv) (hdθ : d * θ = θ * d) : d = 1 := by
  have hcl : S.cl d ∈ commSpace ((S.ρ ⟨_, hvM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    have := hΔle (S.cl_mem_clSub hd hd.1)
    rwa [S.commQt_of_mem hvM] at this
  obtain ⟨p, p', hp, hp', e⟩ := (D.mem_commSpace_iff_coord_of_mem_Cbar hvC).mp hcl
  have hfixθ : (S.ρ ⟨θ, hθM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl d) = S.cl d := by
    rw [S.ρ_cl ⟨θ, hθM⟩ hd.1]
    show S.cl (θ * d * θ⁻¹) = S.cl d
    rw [← hdθ, mul_inv_cancel_right]
  have h2 : ((S.ρ ⟨θ, hθM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (p, p')) =
      D.coord (ρV ⟨_, hθC⟩ p, ρV ⟨_, hθC⟩ p') := D.Cbar_apply_coord ⟨_, hθC⟩ p p'
  rw [e, h2] at hfixθ
  obtain ⟨h3, h4⟩ := Prod.mk.inj (D.coord.injective hfixθ)
  have hp0 := hfpf p hp h3
  have hp'0 := hfpf p' hp' h4
  rw [hp0, hp'0, Prod.mk_zero_zero, map_zero] at e
  rcases (S.cl_eq_zero_iff hd.1).mp e with h | h
  · exact h
  · exact absurd (h ▸ hd) (SMK.z_not_mem_Dl S hvQ)

theorem eq_one_or_eq_of_mem_of_commute (h0 : SixAt S) {kv θ : G}
    (hvM : kv * S.z * kv⁻¹ ∈ S.M) (hvC : S.ρ ⟨_, hvM⟩ ∈ D.Cbar)
    (hvU : IsTypeA D.QV (ρV ⟨_, hvC⟩) 2) (hθM : θ ∈ S.M) (hθC : S.ρ ⟨θ, hθM⟩ ∈ D.Cbar)
    (hθ3 : θ ^ 3 = 1) (hθv : Commute θ (kv * S.z * kv⁻¹))
    (hfpf : ∀ v ∈ commSpace (ρV ⟨_, hvC⟩), ρV ⟨_, hθC⟩ v = v → v = 0)
    (hfix : fixSpace (ρV ⟨_, hθC⟩) ≤ fixSpace (ρV ⟨_, hvC⟩))
    (hdim : finrank (ZMod 2) (fixSpace (ρV ⟨_, hθC⟩)) + 4 = finrank (ZMod 2) (Vt S D.g D.t))
    {q : G} (hq : q ∈ S.Qa kv) (hqθ : q * θ = θ * q) (hqz : q * S.z = S.z * q) :
    q = 1 ∨ q = kv * S.z * kv⁻¹ := by
  have hvQ : kv * S.z * kv⁻¹ ∉ S.QG := by
    intro hQ
    apply hvU.2.1
    have h1 : S.ρ ⟨_, hvM⟩ = 1 := (S.ρ_eq_one_iff _).mpr hQ
    have h2 : (⟨_, hvC⟩ : D.Cbar) = 1 := Subtype.ext h1
    rw [h2, map_one]
  have hvz := h0.e34a _ (isConj_iff.mpr ⟨kv, rfl⟩) hvM hvQ
  have hfixv := SMK.fixQt_eq_of_not_isConj S hvM hvz
  have hΔle := SMK.clSub_Dl_le_commQt S hvM hvQ hvz
  obtain ⟨a₀, ha₀, ha₀P⟩ := D.exists_fix_not_comm h0.six_le hvU
  have hKC := D.lbar_mem_Cbar hvM hvC hfixv hΔle ha₀ ha₀P
  have hqM : q ∈ S.M := mem_centralizer_singleton_iff.mpr hqz
  have hqL : S.ρ ⟨q, hqM⟩ ∈ S.Lbar kv := ⟨⟨q, hqM⟩, mem_subgroupOf.mpr ⟨hq, hqM⟩, rfl⟩
  obtain ⟨hqC, hqP⟩ := hKC _ hqL
  have hqv : q * (kv * S.z * kv⁻¹) = (kv * S.z * kv⁻¹) * q :=
    mem_centralizer_singleton_iff.mp (SMK.mem_centralizer_of_mem_Qa S hq)
  have hcσ : ρV ⟨_, hqC⟩ * ρV ⟨_, hvC⟩ = ρV ⟨_, hvC⟩ * ρV ⟨_, hqC⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    show S.ρ ⟨q, hqM⟩ * S.ρ ⟨_, hvM⟩ = S.ρ ⟨_, hvM⟩ * S.ρ ⟨q, hqM⟩
    rw [← map_mul, ← map_mul]
    exact congrArg S.ρ (Subtype.ext hqv)
  have hcθ : ρV ⟨_, hqC⟩ * ρV ⟨_, hθC⟩ = ρV ⟨_, hθC⟩ * ρV ⟨_, hqC⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    show S.ρ ⟨q, hqM⟩ * S.ρ ⟨θ, hθM⟩ = S.ρ ⟨θ, hθM⟩ * S.ρ ⟨q, hqM⟩
    rw [← map_mul, ← map_mul]
    exact congrArg S.ρ (Subtype.ext hqθ)
  have hθσ : ρV ⟨_, hθC⟩ * ρV ⟨_, hvC⟩ = ρV ⟨_, hvC⟩ * ρV ⟨_, hθC⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    show S.ρ ⟨θ, hθM⟩ * S.ρ ⟨_, hvM⟩ = S.ρ ⟨_, hvM⟩ * S.ρ ⟨θ, hθM⟩
    rw [← map_mul, ← map_mul]
    exact congrArg S.ρ (Subtype.ext hθv.eq)
  have hθ3' : ρV ⟨_, hθC⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨_, hθC⟩ : D.Cbar) ^ 3 = 1 := Subtype.ext (by
      show S.ρ ⟨θ, hθM⟩ ^ 3 = 1
      rw [← map_pow]
      have : (⟨θ, hθM⟩ : S.M) ^ 3 = 1 := Subtype.ext hθ3
      rw [this, map_one])
    rw [this, map_one]
  obtain ⟨n, hn⟩ := (Setting.isPGroup_QG (S.conjBy kv)) ⟨q, hq⟩
  have hc2 : ρV ⟨_, hqC⟩ ^ (2 ^ n) = 1 := by
    rw [← map_pow]
    have : (⟨_, hqC⟩ : D.Cbar) ^ (2 ^ n) = 1 := Subtype.ext (by
      show S.ρ ⟨q, hqM⟩ ^ (2 ^ n) = 1
      rw [← map_pow]
      have hq2 : q ^ (2 ^ n) = 1 := by
        have := congrArg Subtype.val hn
        rwa [SubgroupClass.coe_pow] at this
      have : (⟨q, hqM⟩ : S.M) ^ (2 ^ n) = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow]
        exact hq2)
      rw [this, map_one])
    rw [this, map_one]
  rcases eq_one_or_eq_of_commute D.QV_nondegenerate hvU (D.QV_resC _) hθ3' hθσ hfpf hfix hdim
    (D.QV_resC _) hcσ hcθ hc2 hqP with h | h
  ·
    left
    have h1 : (⟨_, hqC⟩ : D.Cbar) = 1 := D.resC_injective (h.trans (map_one _).symm)
    have h2 : S.ρ ⟨q, hqM⟩ = 1 := congrArg Subtype.val h1
    exact D.eq_one_of_mem_Dl_of_commute hvM hvC hvQ hΔle hθM hθC hfpf
      ⟨(S.ρ_eq_one_iff _).mp h2, hq⟩ hqθ
  ·
    right
    have h1 : (⟨_, hqC⟩ : D.Cbar) = ⟨_, hvC⟩ := D.resC_injective h
    have h2 : S.ρ ⟨q, hqM⟩ = S.ρ ⟨_, hvM⟩ := congrArg Subtype.val h1
    have hvQv : kv * S.z * kv⁻¹ ∈ S.Qa kv := (S.conjBy kv).z_mem_QG
    have hmemM : q * (kv * S.z * kv⁻¹)⁻¹ ∈ S.M := S.M.mul_mem hqM (S.M.inv_mem hvM)
    have h3 : S.ρ ⟨q * (kv * S.z * kv⁻¹)⁻¹, hmemM⟩ = 1 := by
      have : (⟨q * (kv * S.z * kv⁻¹)⁻¹, hmemM⟩ : S.M) = ⟨q, hqM⟩ * (⟨_, hvM⟩ : S.M)⁻¹ := rfl
      rw [this, map_mul, map_inv, h2, mul_inv_cancel]
    have hd : q * (kv * S.z * kv⁻¹)⁻¹ ∈ S.QG ⊓ S.Qa kv :=
      ⟨(S.ρ_eq_one_iff _).mp h3, (S.Qa kv).mul_mem hq ((S.Qa kv).inv_mem hvQv)⟩
    have hdθ : q * (kv * S.z * kv⁻¹)⁻¹ * θ = θ * (q * (kv * S.z * kv⁻¹)⁻¹) := by
      have hvθ : (kv * S.z * kv⁻¹)⁻¹ * θ = θ * (kv * S.z * kv⁻¹)⁻¹ := hθv.inv_right.eq.symm
      rw [mul_assoc, hvθ, ← mul_assoc, hqθ, mul_assoc]
    have := D.eq_one_of_mem_Dl_of_commute hvM hvC hvQ hΔle hθM hθC hfpf hd hdθ
    rw [mul_inv_eq_one] at this
    exact this

theorem false_of_isUInv_at (h0 : SixAt S) {kv θ : G}
    (hvM : kv * S.z * kv⁻¹ ∈ S.M) (hvC : S.ρ ⟨_, hvM⟩ ∈ D.Cbar)
    (hvU : IsTypeA D.QV (ρV ⟨_, hvC⟩) 2) (hθM : θ ∈ S.M) (hθC : S.ρ ⟨θ, hθM⟩ ∈ D.Cbar)
    (hθ3 : θ ^ 3 = 1) (hθv : Commute θ (kv * S.z * kv⁻¹))
    (hfpf : ∀ v ∈ commSpace (ρV ⟨_, hvC⟩), ρV ⟨_, hθC⟩ v = v → v = 0)
    (hfix : fixSpace (ρV ⟨_, hθC⟩) ≤ fixSpace (ρV ⟨_, hvC⟩))
    (hdim : finrank (ZMod 2) (fixSpace (ρV ⟨_, hθC⟩)) + 4 = finrank (ZMod 2) (Vt S D.g D.t))
    (hUv : 2 ^ (S.width - 4) ≤
      Nat.card {q : G // q ∈ S.Qa kv ∧ q * θ = θ * q ∧ q * S.z = S.z * q}) : False := by
  have hle : Nat.card {q : G // q ∈ S.Qa kv ∧ q * θ = θ * q ∧ q * S.z = S.z * q} ≤ 2 := by
    have hinj : Function.Injective (fun q : {q : G // q ∈ S.Qa kv ∧ q * θ = θ * q ∧
        q * S.z = S.z * q} => (⟨q.1, by
          rcases D.eq_one_or_eq_of_mem_of_commute h0 hvM hvC hvU hθM hθC hθ3 hθv hfpf hfix hdim
            q.2.1 q.2.2.1 q.2.2.2 with h | h
          · rw [h]; exact Set.mem_insert _ _
          · rw [h]; exact Set.mem_insert_of_mem _ rfl⟩ :
            ({1, kv * S.z * kv⁻¹} : Set G))) := fun a b e => by
      have := congrArg (fun u : ({1, kv * S.z * kv⁻¹} : Set G) => (u : G)) e
      exact Subtype.ext this
    refine (Nat.card_le_card_of_injective _ hinj).trans ?_
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have h6 := h0.six_le
  have h4 : 2 ^ 2 ≤ 2 ^ (S.width - 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end S2Data

end CFSG.GF2Type.Smith1980Orth
