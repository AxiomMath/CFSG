module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.ClassicalInvolution.SmallCases.NobqTransfer

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def OutTwoCyclic (F : Type*) [Group F] : Prop :=
  ∀ P : Subgroup (Outer F), IsPGroup 2 P → IsCyclic P

theorem isCyclic_of_injective_hom {G G' : Type*} [Group G] [Group G'] [IsCyclic G']
    (f : G →* G') (hf : Function.Injective f) : IsCyclic G :=
  isCyclic_of_surjective (MonoidHom.ofInjective hf).symm.toMonoidHom
    (MonoidHom.ofInjective hf).symm.surjective

theorem OutTwoCyclic.of_mulEquiv {F F' : Type*} [Group F] [Group F'] (e : F ≃* F')
    (h : OutTwoCyclic F') : OutTwoCyclic F := by
  intro P hP
  let ε : Outer F ≃* Outer F' := equivalence e
  have hP' : IsPGroup 2 (P.map ε.toMonoidHom) := hP.map _
  have := h _ hP'
  exact isCyclic_of_injective_hom (Subgroup.equivMapOfInjective P ε.toMonoidHom
    ε.injective).toMonoidHom (Subgroup.equivMapOfInjective P ε.toMonoidHom ε.injective).injective

theorem finite_mulAut_of_finite (F : Type*) [Group F] [Finite F] : Finite (MulAut F) :=
  Finite.of_injective (fun f : MulAut F => (f : F → F)) DFunLike.coe_injective

theorem OutTwoCyclic.of_card_le_two {F : Type*} [Group F] [Finite F]
    (h : Nat.card (Outer F) ≤ 2) : OutTwoCyclic F := by
  intro P _
  have : Finite (MulAut F) := finite_mulAut_of_finite F
  have hP : Nat.card P ≤ 2 := (Subgroup.card_le_card_group P).trans h
  have hpos : 0 < Nat.card P := Nat.card_pos
  interval_cases hc : Nat.card P
  · have : Subsingleton P := Nat.card_eq_one_iff_unique.mp hc |>.1
    infer_instance
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card hc

theorem card_outer_le_two_of_card_mulAut_le {F : Type*} [Group F] [Finite F]
    (hC : Subgroup.center F = ⊥) (h : Nat.card (MulAut F) ≤ 2 * Nat.card F) :
    Nat.card (Outer F) ≤ 2 := by
  have hinj : Function.Injective (MulAut.conj : F →* MulAut F) := by
    intro a b hab
    have h1 : b⁻¹ * a ∈ Subgroup.center F := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 : a * g * a⁻¹ = b * g * b⁻¹ := by
        have := congrArg (fun φ : MulAut F => φ g) hab
        simpa [MulAut.conj_apply] using this
      calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
        _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h2]
        _ = (b⁻¹ * a) * g := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  have hInn : Nat.card (inner F) = Nat.card F :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hcard := (inner F).card_eq_card_quotient_mul_card_subgroup
  rw [hInn] at hcard
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hle : Nat.card (Outer F) * Nat.card F ≤ 2 * Nat.card F := by
    rw [← hcard]
    exact h
  exact Nat.le_of_mul_le_mul_right hle hpos

theorem isCyclic_of_outTwoCyclic {G : Type*} [Group G] (F : Subgroup G) [F.Normal]
    (hC : Subgroup.centralizer (F : Set G) = ⊥) (h : OutTwoCyclic F) :
    ∀ P : Subgroup (G ⧸ F), IsPGroup 2 P → IsCyclic P := by
  intro P hP
  let ψ : G →* Outer F := (QuotientGroup.mk'
    (CFSG.ComponentClassification.OuterAutomorphisms.inner F)).comp
    (MulAut.conjNormal : G →* MulAut F)
  have hψF : ∀ x ∈ F, ψ x = 1 := by
    intro x hx
    show (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner F))
      (MulAut.conjNormal x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨⟨x, hx⟩, ?_⟩
    ext y
    simp [MulAut.conjNormal_apply]
  let ψ' : G ⧸ F →* Outer F := QuotientGroup.lift F ψ hψF
  have hinj : Function.Injective ψ' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker] at hq
    have h1 : ψ g = 1 := hq
    have h2 : (MulAut.conjNormal g : MulAut F) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner F :=
      (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨f, hf⟩ := h2
    have hg : g⁻¹ * (f : G) ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have key := congrArg (fun α : MulAut F => ((α ⟨y, hy⟩ : F) : G)) hf
      simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
        InvMemClass.coe_inv] at key
      calc y * (g⁻¹ * (f : G)) = g⁻¹ * (g * y * g⁻¹) * f := by group
        _ = g⁻¹ * ((f : G) * y * (f : G)⁻¹) * f := by rw [key]
        _ = g⁻¹ * f * y := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hg
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, hg]
    exact f.2
  have hP' : IsPGroup 2 (P.map ψ') := hP.map _
  have := h _ hP'
  exact isCyclic_of_injective_hom (Subgroup.equivMapOfInjective P ψ' hinj).toMonoidHom
    (Subgroup.equivMapOfInjective P ψ' hinj).injective

@[expose] def NoDatum (F : Type) [Group F] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], Nonempty (↥N ≃* F) →
    Subgroup.centralizer (N : Set G) = ⊥ →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (r : ℕ), 3 ≤ r →
      Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) →
      ∀ t : G, t ∈ (S : Subgroup R).map R.subtype → orderOf t = 2 →
        R ≤ Subgroup.centralizer ({t} : Set G) →
        (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal → False

theorem NoDatum.of_mulEquiv {F F' : Type} [Group F] [Group F'] (e : F ≃* F') (h : NoDatum F') :
    NoDatum F := by
  intro G _ _ N _ ⟨eN⟩ hC R S r hr eS t ht hto hRC hRn
  exact h G N ⟨eN.trans e⟩ hC R S r hr eS t ht hto hRC hRn

theorem noDatum_of_noUniqueInvNormal {F : Type} [Group F] (hN : NoUniqueInvNormal F)
    (hO : OutTwoCyclic F) : NoDatum F := by
  intro G _ _ N _ ⟨e⟩ hC R S r hr ⟨eS⟩ t ht ht2 hRC hRn
  have hOutN : OutTwoCyclic N := OutTwoCyclic.of_mulEquiv e hO
  obtain ⟨htN, hU⟩ := exists_uniqueInvNormal_of_datum N (isCyclic_of_outTwoCyclic N hC hOutN) S hr
    eS ht ht2 hRC hRn
  exact NoUniqueInvNormal.of_mulEquiv e hN ⟨t, htN⟩ _ (by rw [Subgroup.orderOf_mk]; exact ht2) hU

end CFSG.ClassicalInvolution.Nobq
