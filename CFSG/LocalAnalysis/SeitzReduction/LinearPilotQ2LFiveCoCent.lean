module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCoMain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped Pointwise

section Central

variable {G : Type} [Group G]

@[expose] def HOneTrivialMod (u : G) (Q Z : Subgroup G) : Prop :=
  ∀ q ∈ Q, q * (u * q * u⁻¹) = 1 → ∃ p ∈ Q, ∃ z ∈ Z, q = p⁻¹ * (u * p * u⁻¹) * z

theorem hOneTrivialMod_sup_of_swap {W₁ W₂ : Subgroup G} {u : G}
    (hW₂c : ∀ a ∈ W₂, ∀ b ∈ W₂, a * b = b * a) (hN : W₁ ≤ normalizer (W₂ : Set G))
    (h12 : ∀ w ∈ W₁, u * w * u⁻¹ ∈ W₂) (h21 : ∀ w ∈ W₂, u * w * u⁻¹ ∈ W₁) :
    HOneTrivialMod u (W₁ ⊔ W₂) (W₁ ⊓ W₂) := by
  intro q hq hcoc
  have hq' : q ∈ ((W₁ : Set G) * (W₂ : Set G)) := by
    rw [← coe_mul_of_left_le_normalizer_right W₁ W₂ hN]
    exact hq
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hq'
  set a := u * w₁ * u⁻¹ with ha
  set b := u * w₂ * u⁻¹ with hb
  have haW : a ∈ W₂ := h12 w₁ hw₁
  have hbW : b ∈ W₁ := h21 w₂ hw₂
  have hcoc' : w₁ * w₂ * (a * b) = 1 := by
    rw [ha, hb, ← hcoc]
    group
  have hz1 : w₂ * a = w₁⁻¹ * b⁻¹ := by
    calc w₂ * a = w₁⁻¹ * (w₁ * w₂ * (a * b)) * b⁻¹ := by group
      _ = w₁⁻¹ * b⁻¹ := by rw [hcoc']; group
  have hzZ : w₂ * a ∈ W₁ ⊓ W₂ :=
    mem_inf.2 ⟨hz1 ▸ mul_mem (inv_mem hw₁) (inv_mem hbW), mul_mem hw₂ haW⟩
  refine ⟨w₁⁻¹, mem_sup_left (inv_mem hw₁), w₂ * a, hzZ, ?_⟩
  have hcomm : w₂ * a = a * w₂ := hW₂c _ hw₂ _ haW
  calc w₁ * w₂ = w₁ * a⁻¹ * (a * w₂) := by group
    _ = w₁ * a⁻¹ * (w₂ * a) := by rw [hcomm]
    _ = (w₁⁻¹)⁻¹ * (u * w₁⁻¹ * u⁻¹) * (w₂ * a) := by rw [ha]; group

theorem card_eqLocus_dvd_card_centralizer_mul_card {X Q Z : Subgroup G} {H : Type*} [Group H]
    (φ : X →* H) (hφ : Function.Surjective φ) (hQ : ∀ x : X, φ x = 1 ↔ (x : G) ∈ Q)
    (hQX : Q ≤ X) (hZQ : Z ≤ Q) (hXZ : ∀ x ∈ X, ∀ z ∈ Z, x * z = z * x) {u : G}
    (hu2 : u * u = 1) (huX : ∀ x ∈ X, u * x * u⁻¹ ∈ X) (α : H →* H)
    (hα : ∀ x : X, φ ⟨u * x * u⁻¹, huX x x.2⟩ = α (φ x)) (hH1 : HOneTrivialMod u Q Z) :
    Nat.card (α.eqLocus (MonoidHom.id H)) ∣
      Nat.card (centralizer ({u} : Set G)) * Nat.card Z := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  let Y : Subgroup G :=
    { carrier := {y | y ∈ X ∧ y⁻¹ * (u * y * u⁻¹) ∈ Z}
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁X, hy₁Z⟩ ⟨hy₂X, hy₂Z⟩
        refine ⟨mul_mem hy₁X hy₂X, ?_⟩
        have h1 := hXZ _ (inv_mem hy₂X) _ hy₁Z
        have h2 : (y₁ * y₂)⁻¹ * (u * (y₁ * y₂) * u⁻¹) =
            (y₂⁻¹ * (y₁⁻¹ * (u * y₁ * u⁻¹))) * (u * y₂ * u⁻¹) := by group
        rw [h2, h1, mul_assoc]
        exact mul_mem hy₁Z hy₂Z
      one_mem' := ⟨one_mem X, by simp⟩
      inv_mem' := by
        rintro y ⟨hyX, hyZ⟩
        refine ⟨inv_mem hyX, ?_⟩
        have h1 := hXZ _ hyX _ (inv_mem hyZ)
        have h2 : y⁻¹⁻¹ * (u * y⁻¹ * u⁻¹) = y * (y⁻¹ * (u * y * u⁻¹))⁻¹ * y⁻¹ := by group
        rw [h2, h1, mul_assoc, mul_inv_cancel, mul_one]
        exact inv_mem hyZ }
  have hYX : Y ≤ X := fun y hy => hy.1
  let ψ : Y →* Z :=
    { toFun := fun y => ⟨(y : G)⁻¹ * (u * y * u⁻¹), y.2.2⟩
      map_one' := by ext; simp
      map_mul' := fun y₁ y₂ => by
        ext
        have h1 := hXZ _ (inv_mem y₂.2.1) _ y₁.2.2
        simp only [Subgroup.coe_mul]
        calc ((y₁ : G) * y₂)⁻¹ * (u * (y₁ * y₂) * u⁻¹) =
            ((y₂ : G)⁻¹ * ((y₁ : G)⁻¹ * (u * y₁ * u⁻¹))) * (u * y₂ * u⁻¹) := by group
          _ = ((y₁ : G)⁻¹ * (u * y₁ * u⁻¹)) * ((y₂ : G)⁻¹ * (u * y₂ * u⁻¹)) := by
            rw [h1, mul_assoc] }
  have hψker : Nat.card ψ.ker = Nat.card (X ⊓ centralizer ({u} : Set G) : Subgroup G) := by
    have hker : ∀ y : Y, ψ y = 1 ↔ (y : G) ∈ centralizer ({u} : Set G) := by
      intro y
      rw [mem_centralizer_singleton_iff]
      constructor
      · intro h
        have h1 : (y : G)⁻¹ * (u * y * u⁻¹) = 1 := congrArg Subtype.val h
        calc (y : G) * u = y * ((y : G)⁻¹ * (u * y * u⁻¹)) * u := by rw [h1, mul_one]
          _ = u * y := by group
      · intro h
        apply Subtype.ext
        change (y : G)⁻¹ * (u * y * u⁻¹) = 1
        rw [← h]
        group
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, mem_inf.2 ⟨y.1.2.1, (hker y.1).1 y.2⟩⟩
        invFun := fun x => ⟨⟨x.1, (mem_inf.1 x.2).1, by
            rw [← mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).2]
            simp⟩, (hker _).2 (mem_inf.1 x.2).2⟩
        left_inv := fun y => rfl
        right_inv := fun x => rfl }
  have hYcard : Nat.card Y ∣ Nat.card (centralizer ({u} : Set G)) * Nat.card Z := by
    rw [← Subgroup.card_ker_mul_card_range ψ, hψker]
    exact Nat.mul_dvd_mul (Subgroup.card_dvd_of_le inf_le_right)
      (Subgroup.card_subgroup_dvd_card ψ.range)
  let φY : Y →* H := φ.comp (Subgroup.inclusion hYX)
  have hrange : φY.range = α.eqLocus (MonoidHom.id H) := by
    ext h
    constructor
    · rintro ⟨y, rfl⟩
      have hzQ : (y : G)⁻¹ * (u * y * u⁻¹) ∈ Q := hZQ y.2.2
      change α (φ ⟨y, y.2.1⟩) = φ ⟨y, y.2.1⟩
      calc α (φ ⟨y, y.2.1⟩) = φ ⟨u * y * u⁻¹, huX _ y.2.1⟩ := (hα ⟨y, y.2.1⟩).symm
        _ = φ (⟨y, y.2.1⟩ * ⟨(y : G)⁻¹ * (u * y * u⁻¹), hQX hzQ⟩) := by
          congr 1
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          group
        _ = φ ⟨y, y.2.1⟩ := by
          rw [map_mul, (hQ ⟨(y : G)⁻¹ * (u * y * u⁻¹), hQX hzQ⟩).2 hzQ, mul_one]
    · intro hh
      obtain ⟨x, rfl⟩ := hφ h
      have hx : α (φ x) = φ x := hh
      have hcX : (x : G)⁻¹ * (u * x * u⁻¹) ∈ X := mul_mem (inv_mem x.2) (huX _ x.2)
      have hcQ : (x : G)⁻¹ * (u * x * u⁻¹) ∈ Q := by
        have h1 : (⟨(x : G)⁻¹ * (u * x * u⁻¹), hcX⟩ : X) = x⁻¹ * ⟨u * x * u⁻¹, huX x x.2⟩ := rfl
        refine (hQ ⟨_, hcX⟩).1 ?_
        rw [h1, map_mul, map_inv, hα, hx, inv_mul_cancel]
      have hcoc : (x : G)⁻¹ * (u * x * u⁻¹) * (u * ((x : G)⁻¹ * (u * x * u⁻¹)) * u⁻¹) = 1 := by
        have key : ∀ g : G, u * (u * g) = g := fun g => by rw [← mul_assoc, hu2, one_mul]
        rw [hu']
        simp only [mul_assoc, key, mul_inv_cancel_left, inv_mul_cancel_left, hu2]
      obtain ⟨p, hpQ, z, hzZ, hp⟩ := hH1 _ hcQ hcoc
      have hpX : p ∈ X := hQX hpQ
      have hupX : u * p * u⁻¹ ∈ X := huX p hpX
      have hyX : (x : G) * p⁻¹ ∈ X := mul_mem x.2 (inv_mem hpX)
      have hyZ : ((x : G) * p⁻¹)⁻¹ * (u * ((x : G) * p⁻¹) * u⁻¹) ∈ Z := by
        have h1 : ((x : G) * p⁻¹)⁻¹ * (u * ((x : G) * p⁻¹) * u⁻¹) =
            p * ((x : G)⁻¹ * (u * x * u⁻¹)) * (u * p * u⁻¹)⁻¹ := by group
        rw [h1, hp]
        have h2 := hXZ _ (inv_mem hupX) _ hzZ
        have h3 : p * (p⁻¹ * (u * p * u⁻¹) * z) * (u * p * u⁻¹)⁻¹ =
            (u * p * u⁻¹) * (z * (u * p * u⁻¹)⁻¹) := by group
        rw [h3, ← h2, ← mul_assoc, mul_inv_cancel, one_mul]
        exact hzZ
      refine ⟨⟨(x : G) * p⁻¹, hyX, hyZ⟩, ?_⟩
      change φ ⟨(x : G) * p⁻¹, hyX⟩ = φ x
      have h1 : (⟨(x : G) * p⁻¹, hyX⟩ : X) = x * (⟨p, hpX⟩ : X)⁻¹ := rfl
      rw [h1, map_mul, map_inv, (hQ ⟨p, hpX⟩).2 hpQ, inv_one, mul_one]
  rw [← hrange]
  exact (Subgroup.card_range_dvd φY).trans hYcard

end Central

section CoreCentral

variable {G : Type} [Group G] [Finite G]

theorem twentySeven_dvd_card_centralizer_of_central (hSL : SLThreeGraphFieldFixInput)
    {F : Type} [Field F] [CharP F 2] (hF : Nat.card F = 4) {W₁ W₂ X : Subgroup G}
    (φ : X →* Matrix.SpecialLinearGroup (Fin 3) F) (hφ : Function.Surjective φ)
    (hker : ∀ x : X, φ x = 1 ↔ (x : G) ∈ W₁ ⊔ W₂) (hQX : W₁ ⊔ W₂ ≤ X)
    (hW₂2 : ∀ w ∈ W₂, w * w = 1) (hN : W₁ ≤ normalizer (W₂ : Set G))
    (hZp : IsPGroup 2 (W₁ ⊓ W₂ : Subgroup G))
    (hXZ : X ≤ centralizer ((W₁ ⊓ W₂ : Subgroup G) : Set G))
    {u : G} (hu2 : u * u = 1) (huX : ∀ x ∈ X, u * x * u⁻¹ ∈ X)
    (h12 : ∀ w ∈ W₁, u * w * u⁻¹ ∈ W₂) (h21 : ∀ w ∈ W₂, u * w * u⁻¹ ∈ W₁)
    (B : Matrix.SpecialLinearGroup (Fin 3) F)
    (hB : ∀ x : X, φ ⟨u * x * u⁻¹, huX x x.2⟩ = B * graphFieldSL F (φ x) * B⁻¹) :
    27 ∣ Nat.card (centralizer ({u} : Set G)) := by
  have hH1 : HOneTrivialMod u (W₁ ⊔ W₂) (W₁ ⊓ W₂) :=
    hOneTrivialMod_sup_of_swap (fun a ha b hb => mul_comm_of_mul_self_eq_one hW₂2 ha hb) hN
      h12 h21
  have hXZ' : ∀ x ∈ X, ∀ z ∈ W₁ ⊓ W₂, x * z = z * x := fun x hx z hz =>
    ((mem_centralizer_iff.1 (hXZ hx)) z hz).symm
  have hα : ∀ x : X, φ ⟨u * x * u⁻¹, huX x x.2⟩ =
      ((MulAut.conj B).toMonoidHom.comp (graphFieldSL F)) (φ x) := fun x => by
    rw [hB x]
    rfl
  have hdvd := card_eqLocus_dvd_card_centralizer_mul_card φ hφ hker hQX
    (inf_le_left.trans le_sup_left) hXZ' hu2 huX _ hα hH1
  have hinv : ∀ y, B * graphFieldSL F (B * graphFieldSL F y * B⁻¹) * B⁻¹ = y :=
    involutive_of_surjective_of_conj φ hφ hu2 huX (fun y => B * graphFieldSL F y * B⁻¹) hB
  have h27 := (hSL F hF B hinv).trans hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hZp
  rw [hk] at h27
  exact (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 27 2)).dvd_of_dvd_mul_right h27

end CoreCentral

@[expose] def LFiveGraphXCentralInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ (S₀ : Subgroup G) (d : G), IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d →
      ∃ d₁ : G, (d₁ = d ∨ d₁ = d * t) ∧
      ∃ (F : Type) (_ : Field F) (_ : CharP F 2), Nat.card F = 4 ∧
      ∃ (X : Subgroup G) (φ : X →* Matrix.SpecialLinearGroup (Fin 3) F)
        (A : Matrix.SpecialLinearGroup (Fin 3) F) (hd₁X : ∀ x ∈ X, d₁ * x * d₁⁻¹ ∈ X),
        Function.Surjective φ ∧
        (∀ x : X, φ x = 1 ↔ (x : G) ∈ W₁ ⊔ W₁.map (MulAut.conj d).toMonoidHom) ∧
        S₀ ≤ X ∧
        (∀ x : X, φ ⟨d₁ * x * d₁⁻¹, hd₁X x x.2⟩ = A * graphFieldSL F (φ x) * A⁻¹) ∧
        X ≤ centralizer ((W₁ ⊓ W₁.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G)

theorem lFiveGraphCosetThreeInput_of_XCentral (hX : LFiveGraphXCentralInput)
    (hSL : SLThreeGraphFieldFixInput) : LFiveGraphCosetThreeInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  obtain ⟨d₁, hd₁, F, _, _, hF, X, φ, A, hd₁X, hφ, hker, hS₀X, hφd₁, hXZ⟩ :=
    hX G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  refine ⟨d₁, hd₁, fun s hs hinv => ?_⟩
  obtain ⟨hW₁S₀, hW₂S₀, hN, hW₂2, h12, h21⟩ :=
    swap_facts_of_graphSylowData hW₁c hW₁2 htN hdata hd₁ hs
  obtain ⟨huX, hB⟩ := conj_facts_of_X φ A hd₁X hφd₁ (hS₀X hs)
  have hZp : IsPGroup 2 (W₁ ⊓ W₁.map (MulAut.conj d).toMonoidHom : Subgroup G) :=
    (IsPGroup.of_card hW₁c).to_le inf_le_left
  exact twentySeven_dvd_card_centralizer_of_central hSL hF φ hφ hker
    (sup_le (hW₁S₀.trans hS₀X) (hW₂S₀.trans hS₀X)) hW₂2 hN hZp hXZ hinv huX h12 h21 _ hB

end CFSG.SeitzReduction.LinearPilot
