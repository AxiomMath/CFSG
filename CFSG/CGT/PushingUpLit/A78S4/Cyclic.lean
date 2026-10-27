module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.A78Sp4.F410Two
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.A78S4

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V V₂ Z Z₂ J T S M M₂ : Subgroup G} {e : ℕ}

theorem sp4_isCyclic_quot (hB : Sp4Base G V V₂ J T S M M₂ e)
    (hC : Sp4Coords G J V V₂ Z Z₂ (GaloisField 2 e)) (hTZ : ∀ t ∈ T, cj t Z = Z)
    (hsZ : ∀ s ∈ S, s ∉ T → cj s Z = Z₂) :
    haveI := hB.normal_J
    IsCyclic (↥S ⧸ J.subgroupOf S) := by
  classical
  haveI := hB.normal_J
  obtain ⟨c, hV, hV₂, hZc, hZ₂c⟩ := exists_cls2 hC
  have hconjJ : ∀ g ∈ S, ∀ x ∈ J, g * x * g⁻¹ ∈ J := fun g hg x hx => hB.conj_J hg hx
  have hconjJ' : ∀ g ∈ S, ∀ x ∈ J, g⁻¹ * x * g ∈ J := fun g hg x hx => by
    simpa using hB.conj_J (inv_mem hg) hx
  have hact : ∀ g : ↥S, ∃ gb Γ : GaloisField 2 e × GaloisField 2 e →+
      GaloisField 2 e × GaloisField 2 e, ActsAs c (g : G) gb Γ := fun g =>
    c.exists_actsAs (hconjJ g g.2) (hconjJ' g g.2)
  choose gb Γ hA using hact
  have huniq : ∀ (g : G) (f f' : GaloisField 2 e × GaloisField 2 e →+
      GaloisField 2 e × GaloisField 2 e), (∀ x ∈ J, c.π (g * x * g⁻¹) = f (c.π x)) →
      (∀ x ∈ J, c.π (g * x * g⁻¹) = f' (c.π x)) → f = f' := by
    intro g f f' hf hf'
    refine AddMonoidHom.ext fun w => ?_
    obtain ⟨x, hx, rfl⟩ := c.π_surj w
    rw [← hf x hx, ← hf' x hx]
  let θ₀ : ↥S →* AddMonoid.End (GaloisField 2 e × GaloisField 2 e) :=
    { toFun := fun g => gb g
      map_one' := huniq ((1 : ↥S) : G) _ _ (hA 1).π_conj fun x _ => by
        show c.π (1 * x * 1⁻¹) = c.π x
        simp
      map_mul' := fun g h => huniq ((g * h : ↥S) : G) _ _ (hA (g * h)).π_conj fun x hx => by
        have e1 : ((g * h : ↥S) : G) * x * ((g * h : ↥S) : G)⁻¹ =
            g * (h * x * (h : G)⁻¹) * (g : G)⁻¹ := by
          rw [Subgroup.coe_mul]; group
        rw [e1, (hA g).π_conj _ (hconjJ h h.2 x hx), (hA h).π_conj x hx]
        rfl }
  have hθ₀ : ∀ g, θ₀ g = gb g := fun _ => rfl
  have hker : J.subgroupOf S ≤ θ₀.ker := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    rw [MonoidHom.mem_ker, hθ₀]
    refine huniq (g : G) _ _ (hA g).π_conj fun x hx => ?_
    have e1 : (g : G) * x * (g : G)⁻¹ = ⁅(g : G), x⁆ * x := by
      simp only [commutatorElement_def]; group
    have hcJ : ⁅(g : G), x⁆ ∈ J := by
      rw [commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem hg hx) (J.inv_mem hg)) (J.inv_mem hx)
    rw [e1, c.π_mul _ hcJ _ hx, (c.comm _ hg x hx).1, zero_add]
    rfl
  let θ : ↥S ⧸ J.subgroupOf S →* AddMonoid.End (GaloisField 2 e × GaloisField 2 e) :=
    QuotientGroup.lift (J.subgroupOf S) θ₀ hker
  have hθ : ∀ g : ↥S, θ (g : ↥S ⧸ J.subgroupOf S) = gb g := fun g => by
    rw [QuotientGroup.lift_mk]
    rfl
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hθ] at hq
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    refine hB.cent_S g g.2 fun j hj => ?_
    have hcJ : ⁅(g : G), j⁆ ∈ J := by
      rw [commutatorElement_def]
      exact J.mul_mem (hconjJ g g.2 j hj) (J.inv_mem hj)
    have h0 : c.π ⁅(g : G), j⁆ = 0 := by
      have e1 : ⁅(g : G), j⁆ = ((g : G) * j * (g : G)⁻¹) * j⁻¹ := by
        simp only [commutatorElement_def]
      rw [e1, c.π_mul _ (hconjJ g g.2 j hj) _ (J.inv_mem hj), (hA g).π_conj j hj, hq,
        c.π_inv hj]
      show c.π j + -c.π j = 0
      rw [add_neg_cancel]
    exact Subgroup.mem_inf.2 ⟨(hV _ hcJ).2 (by rw [h0]; rfl), (hV₂ _ hcJ).2 (by rw [h0]; rfl)⟩
  have hform : ∀ q, IsDiagForm (θ q : GaloisField 2 e × GaloisField 2 e →+
      GaloisField 2 e × GaloisField 2 e) ∨ IsSwapForm (θ q : GaloisField 2 e × GaloisField 2 e →+
      GaloisField 2 e × GaloisField 2 e) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hθ]
    have hbij := (hA g).bijective (hA g⁻¹) (hconjJ g g.2) (hconjJ' g g.2)
    have hcomp := (hA g).hcomp (hconjJ g g.2)
    by_cases hgT : (g : G) ∈ T
    · left
      refine isDiagForm_of_axes hcomp ((hA g).axes_diag (hB.wdiag c hV hV₂ hgT)) ?_ hbij.1
      intro w
      obtain ⟨z, hz, hzπ, hzζ⟩ := c.ζ_surj (0, w)
      have hzZ : z ∈ Z := (hZc z hz).2 ⟨hzπ, by rw [hzζ]⟩
      have hgz : (g : G) * z * (g : G)⁻¹ ∈ Z := hTZ g hgT ▸ mul_mem_cj' (g : G) hzZ
      have h1 := ((hZc _ (hconjJ g g.2 z hz)).1 hgz).2
      rw [(hA g).ζ_conj z hz hzπ, hzζ] at h1
      exact h1
    · right
      refine isSwapForm_of_axes hcomp ((hA g).axes_swap (hB.wswap c hV hV₂ g.2 hgT)) ?_ hbij.1
      intro w
      obtain ⟨z, hz, hzπ, hzζ⟩ := c.ζ_surj (0, w)
      have hzZ : z ∈ Z := (hZc z hz).2 ⟨hzπ, by rw [hzζ]⟩
      have hgz : (g : G) * z * (g : G)⁻¹ ∈ Z₂ := hsZ g g.2 hgT ▸ mul_mem_cj' (g : G) hzZ
      have h1 := ((hZ₂c _ (hconjJ g g.2 z hz)).1 hgz).2
      rw [(hA g).ζ_conj z hz hzπ, hzζ] at h1
      exact h1
  have hp : IsPGroup 2 (↥S ⧸ J.subgroupOf S) := hB.sylow.isPGroup.to_quotient _
  exact isCyclic_of_forms hp θ hinj hform

theorem sp4_S_cyclic (hB : Sp4Base G V V₂ J T S M M₂ e)
    (hC : Sp4Coords G J V V₂ Z Z₂ (GaloisField 2 e)) (hTZ : ∀ t ∈ T, cj t Z = Z)
    (hsZ : ∀ s ∈ S, s ∉ T → cj s Z = Z₂) :
    ∃ s ∈ S, ∀ x ∈ S, ∃ k : ℤ, (s ^ k)⁻¹ * x ∈ J := by
  haveI := hB.normal_J
  have hcyc := sp4_isCyclic_quot hB hC hTZ hsZ
  obtain ⟨q₀, hq₀⟩ := hcyc.exists_generator
  obtain ⟨s₀, rfl⟩ := QuotientGroup.mk_surjective q₀
  refine ⟨s₀, s₀.2, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hq₀ ((⟨x, hx⟩ : ↥S) : ↥S ⧸ J.subgroupOf S))
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hk
  simpa using hk

theorem sp4_no_inv (hB : Sp4Base G V V₂ J T S M M₂ e)
    (hC : Sp4Coords G J V V₂ Z Z₂ (GaloisField 2 e)) (hTZ : ∀ t ∈ T, cj t Z = Z)
    (hsZ : ∀ s ∈ S, s ∉ T → cj s Z = Z₂) (hinv : T ≠ J → ∃ f ∈ T, f ∉ J ∧ f * f = 1) :
    T ≠ J → ∀ x ∈ S, x ∉ T → x * x ≠ 1 := by
  classical
  intro hTJ x hx hxT hxx
  haveI := hB.normal_J
  have hcyc := sp4_isCyclic_quot hB hC hTZ hsZ
  have : Fintype (↥S ⧸ J.subgroupOf S) := Fintype.ofFinite _
  obtain ⟨f, hf, hfJ, hff⟩ := hinv hTJ
  set qf : ↥S ⧸ J.subgroupOf S := ((⟨f, hB.T_le hf⟩ : ↥S) : ↥S ⧸ J.subgroupOf S) with hqf
  set qx : ↥S ⧸ J.subgroupOf S := ((⟨x, hx⟩ : ↥S) : ↥S ⧸ J.subgroupOf S) with hqx
  have hqf1 : qf ≠ 1 := by
    rw [hqf, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hfJ
  have hqx1 : qx ≠ 1 := by
    rw [hqx, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact fun h => hxT (hB.J_le h)
  have hqfx : qf ≠ qx := by
    rw [hqf, hqx, Ne, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    intro h
    apply hxT
    have h1 : f⁻¹ * x ∈ T := hB.J_le h
    have e1 : x = f * (f⁻¹ * x) := by group
    rw [e1]
    exact mul_mem hf h1
  have hsq : ∀ q : ↥S ⧸ J.subgroupOf S, q = 1 ∨ q = qf ∨ q = qx → q ^ 2 = 1 := by
    rintro q (rfl | rfl | rfl)
    · exact one_pow 2
    · rw [hqf, ← QuotientGroup.mk_pow, pow_two]
      have : (⟨f, hB.T_le hf⟩ : ↥S) * ⟨f, hB.T_le hf⟩ = 1 := Subtype.ext hff
      rw [this, QuotientGroup.mk_one]
    · rw [hqx, ← QuotientGroup.mk_pow, pow_two]
      have : (⟨x, hx⟩ : ↥S) * ⟨x, hx⟩ = 1 := Subtype.ext hxx
      rw [this, QuotientGroup.mk_one]
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥S ⧸ J.subgroupOf S) (n := 2) (by norm_num)
  have hsub : ({1, qf, qx} : Finset (↥S ⧸ J.subgroupOf S)) ⊆
      Finset.univ.filter fun a : ↥S ⧸ J.subgroupOf S => a ^ 2 = 1 := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hsq q hq
  have h3 : ({1, qf, qx} : Finset (↥S ⧸ J.subgroupOf S)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hqfx
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hqf1 h.symm, fun h => hqx1 h.symm⟩
  have h4 := Finset.card_le_card hsub
  rw [h3] at h4
  omega

end CFSG.CGT.PushingUpLit.A78S4
