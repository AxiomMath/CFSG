module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29B7Aut

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Sec29B7Abs

open CFSG Subgroup CFSG.LocalCores CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS
  CFSG.GH74.Generic.BProg.B3.S3Sec29B7Aut
open scoped commutatorElement

variable {H : Type} [Group H] {Iabs : Type} [Group Iabs]

theorem exists_noncomm (ρ : Iabs →* H) (O : Subgroup Iabs) [O.Normal] (hker : ρ.ker ≤ O)
    (hQ : ¬ Group.IsSolvable (Iabs ⧸ O)) : ∃ i₁ i₂ : Iabs, ρ i₁ * ρ i₂ ≠ ρ i₂ * ρ i₁ := by
  by_contra hcomm
  push Not at hcomm
  apply hQ
  refine Group.isSolvable_of_comm (fun a b => ?_)
  obtain ⟨i₁, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨i₂, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hcomm i₁ i₂]
  group

theorem exists_noncomm_of_isQuasisimple {Q : Type} [Group Q] (hQ : IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

theorem inv_eq_of_mul_self {d : H} (hd : d * d = 1) : d⁻¹ = d :=
  inv_eq_of_mul_eq_one_right hd

theorem mem_conjSub' {n x : H} {Q : Subgroup H} : x ∈ conjSub n Q ↔ n⁻¹ * x * n ∈ Q := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro h
    exact ⟨n⁻¹ * x * n, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem contra_vertical [Finite H] {M : Subgroup H} (hM : IsComponent M) {r : ℕ}
    (hr : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ r = p ^ f)
    (hMsl : HasSL2Model ↥M (fun q => q = r))
    (ρ : Iabs →* H) (O : Subgroup Iabs) [O.Normal] (hker : ρ.ker ≤ O)
    (hQ : ¬ Group.IsSolvable (Iabs ⧸ O)) (hρM : ∀ i, ρ i ∈ M)
    (D : Subgroup H) (hD4 : Nat.card D = 4) (hD2 : ∀ d ∈ D, d * d = 1)
    (hDI : ∀ d ∈ D, ∀ i, ∃ j, d * ρ i * d⁻¹ = ρ j)
    (hcov : ∀ d ∈ D, ∀ i, ∃ i', d * ρ i' = ρ i' * d ∧ i⁻¹ * i' ∈ O)
    (hfaith : ∀ d ∈ D, (∀ m ∈ M, d * m = m * d) → d = 1) : False := by
  classical
  have hperf : Group.IsPerfect ↥M := hM.1.1
  have hDN : D ≤ normalizer (M : Set H) := by
    intro d hd
    have hdinv : d⁻¹ = d := inv_eq_of_mul_self (hD2 d hd)
    have hN₂ : IsComponent (conjSub d M) := isComponent_conjSub hM d
    rcases distinct_components_commute hM hN₂ with heq | hbot
    · rw [Subgroup.mem_normalizer_iff]
      intro z
      have h1 : z ∈ M ↔ z ∈ conjSub d M := by rw [← heq]
      rw [h1, mem_conjSub', hdinv]
    · exfalso
      obtain ⟨i₁, i₂, hne⟩ := exists_noncomm ρ O hker hQ
      apply hne
      have hm₂ : ρ i₂ ∈ conjSub d M := by
        rw [mem_conjSub']
        obtain ⟨j, hj⟩ := hDI d hd i₂
        have h3 : d⁻¹ * ρ i₂ * d = ρ j := by rw [← hj, hdinv]
        rw [h3]
        exact hρM j
      have := Subgroup.commutator_mem_commutator (hρM i₁) hm₂
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
  let ψ : ↥D →* MulAut ↥M := (normalizerConjHom M).comp (Subgroup.inclusion hDN)
  have hψapp : ∀ (d : ↥D) (m : ↥M), ((ψ d m : ↥M) : H) = (d : H) * m * (d : H)⁻¹ :=
    fun d m => rfl
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro d hd
    rw [MonoidHom.mem_ker] at hd
    have h1 : (d : H) = 1 := hfaith d d.2 (fun m hm => by
      have h2 := congrArg Subtype.val (DFunLike.congr_fun hd ⟨m, hm⟩)
      rw [hψapp] at h2
      simp only [MulAut.one_apply] at h2
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm.symm)
    exact Subtype.ext h1
  have hD'4 : Nat.card ↥ψ.range = 4 := by
    rw [← hD4]
    exact Nat.card_congr (MonoidHom.ofInjective hψinj).symm.toEquiv
  have hD'2 : ∀ d' ∈ ψ.range, d' * d' = 1 := by
    rintro _ ⟨δ, rfl⟩
    rw [← map_mul]
    have : δ * δ = 1 := Subtype.ext (hD2 δ δ.2)
    rw [this, map_one]
  obtain ⟨_, ⟨δ, rfl⟩, hδ1, hsolv⟩ := exists_solvable_fix_sl2 hr hMsl ψ.range hD'2 hD'4
  let Cd : Subgroup Iabs := (centralizer ({(δ : H)} : Set H)).comap ρ
  have hCd : ∀ i : Iabs, i ∈ Cd ↔ (δ : H) * ρ i = ρ i * δ := fun i => by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact eq_comm
  have hθmem : ∀ c : ↥Cd, (⟨ρ c, hρM c⟩ : ↥M) ∈ fixSub (ψ δ) := by
    intro c
    rw [mem_fixSub]
    apply Subtype.ext
    rw [hψapp]
    exact (mul_inv_eq_iff_eq_mul.2 ((hCd c).1 c.2))
  let θ : ↥Cd →* ↥(fixSub (ψ δ)) :=
    ((ρ.codRestrict M hρM).comp Cd.subtype).codRestrict _ hθmem
  let Φ₀ : ↥Cd →* Iabs ⧸ O := (QuotientGroup.mk' O).comp Cd.subtype
  have hΦ₀s : Function.Surjective Φ₀ := by
    intro q
    obtain ⟨i₀, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨i', hi'c, hi'O⟩ := hcov δ δ.2 i₀
    refine ⟨⟨i', (hCd i').2 hi'c⟩, ?_⟩
    change (QuotientGroup.mk i' : Iabs ⧸ O) = QuotientGroup.mk i₀
    rw [QuotientGroup.eq]
    have := O.inv_mem hi'O
    rwa [mul_inv_rev, inv_inv] at this
  have hθker : θ.ker ≤ Φ₀.ker := by
    intro c hc
    rw [MonoidHom.mem_ker] at hc ⊢
    have h1 : ρ (c : Iabs) = 1 := congrArg (fun z : ↥(fixSub (ψ δ)) => ((z : ↥M) : H)) hc
    have h2 : (c : Iabs) ∈ O := hker (MonoidHom.mem_ker.2 h1)
    exact (QuotientGroup.eq_one_iff _).2 h2
  have hR : Group.IsSolvable ↥θ.range := inferInstance
  have hCq : Group.IsSolvable (↥Cd ⧸ θ.ker) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.quotientKerEquivRange θ).toMonoidHom) (MulEquiv.injective _)
  let Ψ : ↥Cd ⧸ θ.ker →* Iabs ⧸ O := QuotientGroup.lift θ.ker Φ₀ hθker
  have hΨs : Function.Surjective Ψ := by
    intro q
    obtain ⟨c, rfl⟩ := hΦ₀s q
    exact ⟨QuotientGroup.mk c, rfl⟩
  exact hQ (Group.isSolvable_of_surjective hΨs)

end S3Sec29B7Abs

end CFSG.GH74.Generic.BProg.B3
