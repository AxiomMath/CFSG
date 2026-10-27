module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.AutModelPlane

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise

section Outer

variable {X : Type*} [Group X]

theorem finite_mulAut_of_finite [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun σ : MulAut X => (σ : X → X)) DFunLike.coe_injective

theorem mem_range_conj_of_pow_prime [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hout : Nat.card (Outer X) ≤ 2) {φ : MulAut X} (hφ : φ ^ p = 1) :
    φ ∈ (MulAut.conj : X →* MulAut X).range := by
  haveI : Finite (MulAut X) := finite_mulAut_of_finite
  set q := QuotientGroup.mk' (inner X) φ with hq
  have hq3 : q ^ p = 1 := by rw [hq, ← map_pow, hφ, map_one]
  have hpos : 0 < Nat.card (Outer X) := Nat.card_pos
  have hcop : Nat.Coprime p (Nat.card (Outer X)) := by
    rcases (by omega : Nat.card (Outer X) = 1 ∨ Nat.card (Outer X) = 2) with h | h
    · rw [h]
      exact Nat.coprime_one_right _
    · rw [h]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)
  have hd : orderOf q ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hq3) (orderOf_dvd_natCard q)
  have hq1 : q = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq1
  exact hq1

theorem exists_plane_of_aut [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center X = ⊥) (hout : Nat.card (Outer X) ≤ 2)
    {Ê : Subgroup (MulAut X)} (hE : IsElemAbelian p Ê) (hE2 : Nat.card Ê = p ^ 2) :
    ∃ E₀ : Subgroup X, IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 2 ∧
      Ê = E₀.map (MulAut.conj : X →* MulAut X) := by
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    conj_injective_of_center_bot_sg hcen
  have hle : Ê ≤ (MulAut.conj : X →* MulAut X).range := fun φ hφ =>
    mem_range_conj_of_pow_prime hp hp2 hout (hE.2 φ hφ)
  have heq : (Ê.comap (MulAut.conj : X →* MulAut X)).map (MulAut.conj : X →* MulAut X) = Ê := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hle
  refine ⟨Ê.comap (MulAut.conj : X →* MulAut X), ?_, ?_, heq.symm⟩
  · exact isElemAbelian_of_map_injective' hinj (by rw [heq]; exact hE)
  · rw [← Subgroup.card_map_of_injective hinj, heq]
    exact hE2

theorem mulAut_conj_conj (σ : MulAut X) (f : X) :
    σ * (MulAut.conj f : MulAut X) * σ⁻¹ = MulAut.conj (σ f) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply]
  congr 2
  exact σ.apply_symm_apply y

theorem noSig_of_inner_outer [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center X = ⊥) (hout : Nat.card (Outer X) ≤ 2)
    {E₀ : Subgroup X} (hE : IsElemAbelian p E₀) (hE2 : Nat.card E₀ = p ^ 2)
    (hB : ∀ e ∈ E₀, e ≠ 1 → ∀ q : ℕ, q.Prime → q ≠ p → ∀ V : Subgroup X,
      V ≤ Subgroup.centralizer ({e} : Set X) → IsElemAbelian q V → V ≠ ⊥ →
        Nat.card V % p ≠ 1)
    (hO : ∀ σ : MulAut X, Nat.Coprime (orderOf σ) p → (∀ f ∈ E₀, σ f = f) → σ = 1) :
    NoSig p (E₀.map (MulAut.conj : X →* MulAut X)) := by
  haveI : Finite (MulAut X) := finite_mulAut_of_finite
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    conj_injective_of_center_bot_sg hcen
  intro T hTcop hET
  set T₀ : Subgroup X := T.comap (MulAut.conj : X →* MulAut X) with hT₀
  have hT₀le : T₀.map (MulAut.conj : X →* MulAut X) ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hT₀cop : Nat.Coprime p (Nat.card T₀) := by
    refine Nat.Coprime.coprime_dvd_right ?_ hTcop
    rw [← Subgroup.card_map_of_injective hinj]
    exact Subgroup.card_dvd_of_le hT₀le
  have hnorm : E₀ ≤ Subgroup.normalizer (T₀ : Set X) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have hconj : (MulAut.conj (e * t * e⁻¹) : MulAut X) =
        MulAut.conj e * MulAut.conj t * (MulAut.conj e)⁻¹ := by
      simp only [map_mul, map_inv]
    have h1 := Subgroup.mem_normalizer_iff.1 (hET ⟨e, he, rfl⟩) (MulAut.conj t)
    rw [hT₀, Subgroup.mem_comap, Subgroup.mem_comap, hconj]
    exact h1
  have hA : ∀ u : X, Nat.Coprime (orderOf u) p → (∀ f ∈ E₀, u * f = f * u) → u = 1 := by
    intro u hu hcomm
    have h1 : (MulAut.conj u : MulAut X) = 1 := by
      refine hO _ ?_ fun f hf => ?_
      · rw [orderOf_injective _ hinj u]
        exact hu
      · rw [MulAut.conj_apply]
        calc u * f * u⁻¹ = f * u * u⁻¹ := by rw [hcomm f hf]
          _ = f := by group
    exact hinj (by rw [h1, map_one])
  have hT₀bot : T₀ = ⊥ :=
    noSig_of_rank hp hE hE2 hA hB T₀ hT₀cop hnorm
  have hTinner : ∀ x : X, MulAut.conj x ∈ T → x = 1 := by
    intro x hx
    have : x ∈ T₀ := hx
    rw [hT₀bot] at this
    exact this
  let f : T →* Outer X := (QuotientGroup.mk' (inner X)).comp T.subtype
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have ht' : (t : MulAut X) ∈ inner X := (QuotientGroup.eq_one_iff _).1 ht
    obtain ⟨x, hx⟩ := ht'
    have : x = 1 := hTinner x (by rw [show (MulAut.conj : X →* MulAut X) x = t from hx]; exact t.2)
    apply Subtype.ext
    rw [← hx, this, map_one]
    rfl
  have hTcard : Nat.card T ≤ 2 :=
    (Nat.card_le_card_of_injective f hfinj).trans hout
  by_contra hTne
  have hTc2 : Nat.card T = 2 := by
    have h1 : 1 < Nat.card T := by
      rw [Nat.one_lt_iff_ne_zero_and_ne_one]
      refine ⟨Nat.card_pos.ne', fun h => hTne ?_⟩
      exact (Subgroup.card_eq_one).1 h
    omega
  obtain ⟨σ', hσ'⟩ : ∃ σ' : T, σ' ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hTne ((Subgroup.eq_bot_iff_forall T).2 fun x hx => congrArg Subtype.val (hall ⟨x, hx⟩))
  have huniq := (Nat.card_eq_two_iff' (1 : T)).1 hTc2
  obtain ⟨σ₁, hσ₁, hσ₁u⟩ := huniq
  have hσeq : ∀ t : T, t ≠ 1 → t = σ₁ := fun t ht => hσ₁u t ht
  have hσ₁sq : σ₁ * σ₁ = 1 := by
    by_contra hne
    have := hσeq (σ₁ * σ₁) hne
    exact hσ₁ (mul_left_cancel (a := σ₁) (by rw [mul_one]; exact this))
  have hord : orderOf (σ₁ : MulAut X) = 2 := by
    have h2 : (σ₁ : MulAut X) ^ 2 = 1 := by
      have := congrArg Subtype.val hσ₁sq
      simpa [pow_two] using this
    have hne : (σ₁ : MulAut X) ≠ 1 := fun h => hσ₁ (Subtype.ext h)
    exact orderOf_eq_prime h2 hne
  have hcomm : ∀ g ∈ E₀, (σ₁ : MulAut X) g = g := by
    intro g hg
    have hmem : (MulAut.conj g : MulAut X) ∈ Subgroup.normalizer (T : Set (MulAut X)) :=
      hET ⟨g, hg, rfl⟩
    have h1 : MulAut.conj g * (σ₁ : MulAut X) * (MulAut.conj g)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.1 hmem _).1 σ₁.2
    have h2 : (⟨MulAut.conj g * (σ₁ : MulAut X) * (MulAut.conj g)⁻¹, h1⟩ : T) = σ₁ := by
      by_cases hone : (⟨MulAut.conj g * (σ₁ : MulAut X) * (MulAut.conj g)⁻¹, h1⟩ : T) = 1
      · exfalso
        have := congrArg Subtype.val hone
        have h3 : (σ₁ : MulAut X) = 1 := by
          have h4 : MulAut.conj g * (σ₁ : MulAut X) * (MulAut.conj g)⁻¹ = 1 := this
          calc (σ₁ : MulAut X) = (MulAut.conj g)⁻¹ * (MulAut.conj g * (σ₁ : MulAut X) *
              (MulAut.conj g)⁻¹) * MulAut.conj g := by group
            _ = 1 := by rw [h4]; group
        exact hσ₁ (Subtype.ext h3)
      · exact hσeq _ hone
    have h5 : MulAut.conj g * (σ₁ : MulAut X) * (MulAut.conj g)⁻¹ = σ₁ := congrArg Subtype.val h2
    have h6 : (σ₁ : MulAut X) * MulAut.conj g * (σ₁ : MulAut X)⁻¹ = MulAut.conj g := by
      have h7 : MulAut.conj g * (σ₁ : MulAut X) = (σ₁ : MulAut X) * MulAut.conj g := by
        calc MulAut.conj g * (σ₁ : MulAut X) = (MulAut.conj g * (σ₁ : MulAut X) *
            (MulAut.conj g)⁻¹) * MulAut.conj g := by group
          _ = (σ₁ : MulAut X) * MulAut.conj g := by rw [h5]
      calc (σ₁ : MulAut X) * MulAut.conj g * (σ₁ : MulAut X)⁻¹ =
          MulAut.conj g * (σ₁ : MulAut X) * (σ₁ : MulAut X)⁻¹ := by rw [h7]
        _ = MulAut.conj g := by group
    rw [mulAut_conj_conj] at h6
    exact hinj h6
  have hcop2 : Nat.Coprime (orderOf (σ₁ : MulAut X)) p := by
    rw [hord]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun hd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hd).symm
  exact hσ₁ (Subtype.ext (hO _ hcop2 hcomm))

theorem noSig_planes_of_sylow [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center X = ⊥) (hout : Nat.card (Outer X) ≤ 2)
    {Q : Subgroup X} (hsyl : ∃ S : Sylow p X, (S : Subgroup X) = Q)
    (h : ∀ E₀ : Subgroup X, E₀ ≤ Q → IsElemAbelian p E₀ → Nat.card E₀ = p ^ 2 →
      NoSig p (E₀.map (MulAut.conj : X →* MulAut X))) :
    ∀ Ê : Subgroup (MulAut X), IsElemAbelian p Ê → Nat.card Ê = p ^ 2 → NoSig p Ê := by
  intro Ê hÊ hÊ2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E₀, hE₀el, hE₀2, hÊeq⟩ := exists_plane_of_aut hp hp2 hcen hout hÊ hÊ2
  obtain ⟨S1, hS1⟩ := hsyl
  obtain ⟨S', hS'⟩ := hE₀el.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S' S1
  set E' : Subgroup X := MulAut.conj g • E₀ with hE'
  have hE'map : E' = E₀.map (MulAut.conj g).toMonoidHom := rfl
  have hE'Q : E' ≤ Q := by
    rw [← hS1, ← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hS'
  have hE'card : Nat.card E' = p ^ 2 := by
    rw [hE'map, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hE₀2
  have hE'el : IsElemAbelian p E' := by
    rw [hE'map]
    exact hE₀el.map _
  have hN := h E' hE'Q hE'el hE'card
  have hcc : ∀ a0 : X, (MulAut.conj (MulAut.conj g : MulAut X)).toMonoidHom (MulAut.conj a0) =
      MulAut.conj (g * a0 * g⁻¹) := by
    intro a0
    simp only [MulEquiv.coe_toMonoidHom]
    rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  have hconj : E'.map (MulAut.conj : X →* MulAut X) =
      Ê.map (MulAut.conj (MulAut.conj g : MulAut X)).toMonoidHom := by
    ext β
    constructor
    · rintro ⟨a, ha, rfl⟩
      have ha' : a ∈ (MulAut.conj g • E₀ : Subgroup X) := ha
      rw [Subgroup.mem_smul_pointwise_iff_exists] at ha'
      obtain ⟨a0, ha0, rfl⟩ := ha'
      refine ⟨MulAut.conj a0, ?_, ?_⟩
      · rw [hÊeq]
        exact ⟨a0, ha0, rfl⟩
      · rw [hcc]
        rfl
    · rintro ⟨_, hmem, rfl⟩
      rw [hÊeq] at hmem
      obtain ⟨a0, ha0, rfl⟩ := hmem
      refine ⟨g * a0 * g⁻¹, ?_, (hcc a0).symm⟩
      have : g * a0 * g⁻¹ ∈ (MulAut.conj g • E₀ : Subgroup X) :=
        (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨a0, ha0, rfl⟩
      exact this
  rw [hconj] at hN
  exact (noSig_conj_iff (MulAut.conj g)).1 hN

end Outer

end CFSG.HardMathSupport.Dickson.I271
