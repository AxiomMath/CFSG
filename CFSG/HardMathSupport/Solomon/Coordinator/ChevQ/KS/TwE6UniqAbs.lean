module

public import CFSG.HardMathSupport.Dickson.I271.Support.OuterKData
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoIn

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Chevalley
open scoped commutatorElement

namespace TwE6UniqAbs

@[expose] def TwE6UniqModel : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
    ∀ β : MulAut (twistedE6RootGroup K σ), β ^ 3 = 1 → β ≠ 1 →
      ∀ J J' : Subgroup (twistedE6RootGroup K σ), GLAPComponent 3 (fixSubgroup β) J →
        GLAPComponent 3 (fixSubgroup β) J' → J = J'

theorem eq_of_map_eq_of_perfect {K Q : Type*} [Group K] [Group Q] (π : K →* Q)
    (hker : π.ker ≤ Subgroup.center K) {J₁ J₂ : Subgroup K} (h₁ : ⁅J₁, J₁⁆ = J₁)
    (h₂ : ⁅J₂, J₂⁆ = J₂) (h : J₁.map π = J₂.map π) : J₁ = J₂ := by
  have key : ∀ {A B : Subgroup K}, ⁅A, A⁆ = A → ⁅B, B⁆ = B → A.map π ≤ B.map π → A ≤ B := by
    intro A B hA hB hle
    conv_lhs => rw [← hA]
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨xb, hxb, hxe⟩ := hle ⟨x, hx, rfl⟩
    obtain ⟨yb, hyb, hye⟩ := hle ⟨y, hy, rfl⟩
    have hz₁ : xb⁻¹ * x ∈ Subgroup.center K := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxe, inv_mul_cancel])
    have hz₂ : yb⁻¹ * y ∈ Subgroup.center K := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hye, inv_mul_cancel])
    have hx' : x = xb * (xb⁻¹ * x) := by group
    have hy' : y = yb * (yb⁻¹ * y) := by group
    have hc := commutatorElement_mul_mul' (a := xb) (b := yb) (z₁ := xb⁻¹ * x) (z₂ := yb⁻¹ * y)
      (Commute.symm (Subgroup.mem_center_iff.1 hz₁ yb))
      (Commute.symm (Subgroup.mem_center_iff.1 hz₁ _))
      (Commute.symm (Subgroup.mem_center_iff.1 hz₂ xb))
    rw [← hx', ← hy'] at hc
    rw [hc]
    have : ⁅xb, yb⁆ ∈ ⁅B, B⁆ := Subgroup.commutator_mem_commutator hxb hyb
    rwa [hB] at this
  exact le_antisymm (key h₁ h₂ h.le) (key h₂ h₁ h.ge)

theorem alpha_eq_one_of_beta_eq_one {K Q : Type*} [Group K] [Group Q] (π : K →* Q)
    (hker : π.ker ≤ Subgroup.center K) (α : MulAut K) (β : MulAut Q)
    (hαβ : ∀ k, π (α k) = β (π k)) (hperf : commutator K = ⊤) (hβ : β = 1) : α = 1 := by
  have hfix : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ fixSubgroup α := by
    rw [Subgroup.commutator_le]
    intro k₁ _ k₂ _
    exact comm_mem_fixSubgroup π hker α β hαβ (by rw [mem_fixSubgroup, hβ]; rfl)
      (by rw [mem_fixSubgroup, hβ]; rfl)
  rw [← _root_.commutator_def, hperf] at hfix
  refine MulEquiv.ext fun k => ?_
  exact mem_fixSubgroup.1 (hfix (Subgroup.mem_top k))

section Main


set_option linter.unusedSectionVars false

theorem bal209TwoUniq_of_model (hM : TwE6UniqModel) : Bal209TwoUniq := by
  classical
  intro X _ _ K a hKq hLie haN ha3 haC J J' hJ hJ'
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨a, haN⟩ with hαdef
  have hα3 : α ^ 3 = 1 := by
    rw [hαdef, ← map_pow, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker,
      Subgroup.mem_subgroupOf]
    simpa using ha3
  have hα1 : α ≠ 1 := by
    intro h
    apply haC
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg Subtype.val (DFunLike.congr_fun h ⟨k, hk⟩)
    have h2 : a * k * a⁻¹ = k := by simpa [hαdef] using h1
    calc k * a = (a * k * a⁻¹) * a := by rw [h2]
      _ = a * k := by group
  set Z := Subgroup.center ↥K with hZ
  set π : ↥K →* ↥K ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker ≤ Subgroup.center ↥K := by rw [hπ, QuotientGroup.ker_mk']
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  set β : MulAut (↥K ⧸ Z) := QuotientGroup.congr Z Z α (Subgroup.map_center_eq α) with hβdef
  have hαβ : ∀ k, π (α k) = β (π k) := fun k => (QuotientGroup.congr_mk Z Z α _ k).symm
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨k, rfl⟩ := hπs q
    have h1 : ∀ n : ℕ, ∀ k : ↥K, (β ^ n) (π k) = π ((α ^ n) k) := by
      intro n
      induction n with
      | zero => intro k; rfl
      | succ n ih =>
        intro k
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ← hαβ, ih]
    rw [h1 3 k, hα3]
    rfl
  have hβ1 : β ≠ 1 := fun h => hα1 (alpha_eq_one_of_beta_eq_one π hker α β hαβ hKq.1 h)
  have hJ₁ := glaPComponent_fixSubgroup Nat.prime_three haN hJ
  have hJ₁' := glaPComponent_fixSubgroup Nat.prime_three haN hJ'
  rw [← hαdef] at hJ₁ hJ₁'
  have hJ₂ := glaPComponent_map_fixSubgroup π hker α β hαβ hπs Nat.prime_three hJ₁
  have hJ₂' := glaPComponent_map_fixSubgroup π hker α β hαβ hπs Nat.prime_three hJ₁'
  obtain ⟨d, hd, ⟨e0⟩⟩ := hLie
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedE6 q =>
    have hq2 : q.p = 2 ∧ q.exponent = 1 := hd
    obtain ⟨K', hKf, σ, hcard, hσ, ⟨eC⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    have hcard4 : Nat.card K' = 4 := by
      rw [hcard, hq2.1, hq2.2]; norm_num
    haveI : Finite K' := Nat.finite_of_card_ne_zero (by rw [hcard4]; norm_num)
    have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by
      have := hσ c
      rwa [hq2.1, hq2.2, pow_one] at this
    set e : (↥K ⧸ Z) ≃* ↥(twistedE6RootGroup K' σ) := e0.trans eC with he
    have hβ' : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
    have hβ1' : MulAut.congr e β ≠ 1 := fun h =>
      hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
    have hmap : ∀ {J₀ : Subgroup ↥K},
        GLAPComponent 3 (fixSubgroup β) (J₀.map π) →
          GLAPComponent 3 (fixSubgroup (MulAut.congr e β)) ((J₀.map π).map e.toMonoidHom) := by
      intro J₀ hJ₀
      have h1 := glaPComponent_map Nat.prime_three e.toMonoidHom (coprime_ker_mulEquiv e _) hJ₀
      rwa [← fixSubgroup_congr e β] at h1
    have heq := hM K' hcard4 σ hσ2 (MulAut.congr e β) hβ' hβ1' _ _ (hmap hJ₂) (hmap hJ₂')
    have heq' : (J.subgroupOf K).map π = (J'.subgroupOf K).map π :=
      Subgroup.map_injective e.injective heq
    have hperf := fun {J₀ : Subgroup ↥K} (h : GLAPComponent 3 (fixSubgroup α) J₀) =>
      glaPComponent_perfect h
    have hsub : J.subgroupOf K = J'.subgroupOf K :=
      eq_of_map_eq_of_perfect π hker (hperf hJ₁) (hperf hJ₁') heq'
    have hJK : J ≤ K := hJ.1.trans inf_le_left
    have hJ'K : J' ≤ K := hJ'.1.trans inf_le_left
    have := (Subgroup.subgroupOf_inj).1 hsub
    rwa [inf_of_le_left hJK, inf_of_le_left hJ'K] at this
  | _ => exact absurd hd (by simp [Bal209TwoIndex])

end Main

end TwE6UniqAbs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
