module

public import CFSG.LargeExtraspecial.GLW4RhoCard
public import CFSG.LargeExtraspecial.GLW4RhoSyl
public import CFSG.LargeExtraspecial.GLW4Sym

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module Matrix QuadraticMap CFSG.LargeExtraspecial.GLR CFSG.GH74.GLS.Bg.Thompson

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

theorem card_le_of_sylowIn_N (e : Basis (Fin 4) (ZMod 2) C.At) {τ : G} (hτM : τ ∈ S.M)
    (hτX : τ ∉ C.X) (hττ : τ * τ = 1) (hN : gram C e (S.ρ ⟨τ, hτM⟩) = N) {T : Subgroup G}
    (hT : IsSylowIn 2 T (centralizer {τ} ⊓ S.M)) : Nat.card T ≤ 2 ^ 10 := by
  set s := S.ρ ⟨τ, hτM⟩
  have hTM : T ≤ S.M := fun t ht => (SylowIn.le hT ht).2
  have hTC : T ≤ centralizer {τ} := fun t ht => (SylowIn.le hT ht).1
  have hτT := Levi.mem_of_sylowIn hτM hττ hT
  have hidx := C.relIndex_inf_X hTM hτT hτX
  have hcardT : Nat.card T = 2 * Nat.card (T ⊓ C.X : Subgroup G) := by
    have := relIndex_mul_card (T ⊓ C.X) T
    rw [hidx, inf_right_comm, inf_idem] at this
    exact this.symm
  set T₀ : Subgroup G := T ⊓ C.X with hT₀
  let f : T₀ →* (C.At ≃ₗ[ZMod 2] C.At) :=
    C.resAt.comp (C.xbarHom.comp (inclusion (inf_le_right : T₀ ≤ C.X)))
  have hcard0 : Nat.card T₀ = Nat.card f.range * Nat.card f.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hker : Nat.card f.ker ≤ Nat.card (S.QG ⊓ centralizer {τ} : Subgroup G) := by
    refine Nat.card_le_card_of_injective (fun x => ⟨((x : T₀) : G), ?_, ?_⟩) ?_
    · have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      have h1 : C.xbarHom (inclusion (inf_le_right : T₀ ≤ C.X) x) = 1 :=
        C.resAt_injective (by rw [map_one]; exact hx)
      exact (S.ρ_eq_one_iff _).mp (congrArg Subtype.val h1)
    · exact hTC (x : T₀).2.1
    · intro a b hab
      have h : ((a : T₀) : G) = ((b : T₀) : G) :=
        congrArg (fun y : (S.QG ⊓ centralizer {τ} : Subgroup G) => (y : G)) hab
      exact Subtype.ext (Subtype.ext h)
  have hrange : Nat.card f.range ≤ 32 := by
    have hT₀2 : IsPGroup 2 T₀ := (SylowIn.isPGroup hT).to_le inf_le_left
    have h2 : IsPGroup 2 f.range := hT₀2.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have hiso : f.range ≤ TauCeti.BilinForm.isometryGroup (C.formOf s) := by
      rintro _ ⟨x, rfl⟩
      rw [TauCeti.BilinForm.mem_isometryGroup_iff]
      intro a a'
      have hxM := hTM (x : T₀).2.1
      have hxτ : S.ρ ⟨(x : G), hxM⟩ * s = s * S.ρ ⟨(x : G), hxM⟩ := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.mp (hTC (x : T₀).2.1))
      change polar S.q ((S.ρ ⟨(x : G), hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) a)
        ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.ρ ⟨(x : G), hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) a')) =
          polar S.q a ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) a')
      rw [← Config.mul_apply s, ← hxτ, Config.mul_apply, Config.polar_apply_apply]
    exact card_le_of_isPGroup_N e hN h2 hiso
  have hCQ := Levi.card_centralizer_QG_le hτM hτX hττ
  have hW := card_W₀_le e hN
  calc Nat.card T = 2 * (Nat.card f.range * Nat.card f.ker) := by rw [hcardT, hcard0]
    _ ≤ 2 * (32 * (2 * 8)) := by
        gcongr
        exact hker.trans (hCQ.trans (Nat.mul_le_mul_left 2 hW))
    _ = 2 ^ 10 := by norm_num

theorem false_of_involution_N [IsSimpleGroup G] (h4 : S.width = 4) {τ₀ : G} (hτ₀M : τ₀ ∈ S.M)
    (hτ₀X : τ₀ ∉ C.X) (hτ₀ : τ₀ * τ₀ = 1)
    (hna : ∃ a, C.formOf (S.ρ ⟨τ₀, hτ₀M⟩) a a ≠ 0) : False := by
  have hss : S.ρ ⟨τ₀, hτ₀M⟩ * S.ρ ⟨τ₀, hτ₀M⟩ = 1 := by
    rw [← ρ_mul hτ₀M hτ₀M]
    exact (S.ρ_eq_one_iff ⟨τ₀ * τ₀, S.M.mul_mem hτ₀M hτ₀M⟩).mpr
      (show τ₀ * τ₀ ∈ S.QG by rw [hτ₀]; exact S.QG.one_mem)
  obtain ⟨e, hN⟩ := exists_basis_gram_N h4 (Config.ρ_mem_Mbar _)
    (Config.ρ_not_mem_Xbar hτ₀M hτ₀X) hss hna
  obtain ⟨τ, σ, hτM, hσM, hτX, hττ, hτN, hσX, hστ, hσσ, halt⟩ :=
    exists_tau_sigma e hτ₀M hτ₀X hτ₀ hN
  rcases hσσ with h1 | hz
  · exact false_of_involution_alt h4 hσM hσX h1 halt
  · have hW : zpowers σ ≤ centralizer {τ} ⊓ S.M :=
      zpowers_le.mpr ⟨mem_centralizer_singleton_iff.mpr hστ, hσM⟩
    have hW2 : IsPGroup 2 (zpowers σ) := by
      have h4' : σ ^ 4 = 1 := by
        rw [show σ ^ 4 = σ * σ * (σ * σ) by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
          hz, S.z_mul_z]
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (show orderOf σ ∣ 2 ^ 2 from orderOf_dvd_of_pow_eq_one h4')
      exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
    obtain ⟨T, hWT, hT⟩ := exists_isSylowIn_le hW hW2
    exact false_of_sylowIn_le C h4 hτM hτX hττ hT
      (sylowIn_centralizer_N e hτM hτX hττ hτN hT (hWT (mem_zpowers σ)) hz)
      (card_le_of_sylowIn_N e hτM hτX hττ hτN hT)

end CFSG.LargeExtraspecial.GLW4
