module

public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCentralSeriesSplittingAlt
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesCoverTrivialPrime
public import CFSG.RankThree.CentralLiftU.PerfectSplit

public section

namespace CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree

open Subgroup CFSG.LocalAnalysis.ComponentInitial

universe u v

theorem exists_invariant_lift_of_coprime_series {p : ℕ} [Fact p.Prime]
    {M : Type*} [Group M] {E : Type*} [Group E] [Finite E] (η : E →* M)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (hp : IsPGroup p η.ker)
    {U : Subgroup M} (hUp : IsPGroup p U)
    {T : Type*} [Group T] [Finite T] (hT : p.Coprime (Nat.card T)) (τ : T →* M)
    (hτU : ∀ t, ∀ x ∈ U, τ t * x * (τ t)⁻¹ ∈ U)
    (m : ℕ) (S : ℕ → Subgroup M) (hS0 : S 0 = ⊥) (hSm : S m = U)
    (hmono : ∀ i < m, S i ≤ S (i + 1))
    (hinv : ∀ i ≤ m, ∀ (t : T), ∀ x ∈ S i, τ t * x * (τ t)⁻¹ ∈ S i)
    (hcent : ∀ i < m, ∀ x ∈ S (i + 1), ∀ g ∈ U, x⁻¹ * g⁻¹ * x * g ∈ S i)
    (hsq : ∀ i < m, ∀ x ∈ S (i + 1), x ^ p ∈ S i)
    (hfix : ∀ i < m, ∀ x ∈ S (i + 1), (∀ t : T, (τ t * x * (τ t)⁻¹)⁻¹ * x ∈ S i) → x ∈ S i)
    (hbil : ∀ i < m, ∀ j < m, ∀ b : M → M → ZMod p,
      (∀ x ∈ S (i + 1), ∀ x' ∈ S (i + 1), ∀ y ∈ S (j + 1), b (x * x') y = b x y + b x' y) →
      (∀ x ∈ S (i + 1), ∀ y ∈ S (j + 1), ∀ y' ∈ S (j + 1), b x (y * y') = b x y + b x y') →
      (∀ x ∈ S i, ∀ y ∈ S (j + 1), b x y = 0) → (∀ x ∈ S (i + 1), ∀ y ∈ S j, b x y = 0) →
      (i = j → ∀ x ∈ S (i + 1), b x x = 0) →
      (∀ (t : T), ∀ x ∈ S (i + 1), ∀ y ∈ S (j + 1),
        b (τ t * x * (τ t)⁻¹) (τ t * y * (τ t)⁻¹) = b x y) →
      ∀ x ∈ S (i + 1), ∀ y ∈ S (j + 1), b x y = 0) :
    ∃ K : Subgroup E, (∀ k ∈ K, η k ∈ U) ∧ (∀ k ∈ K, η k = 1 → k = 1) ∧
      (∀ u ∈ U, ∃ k ∈ K, η k = u) ∧ ∀ (t : T) (e : E), η e = τ t → ∀ k ∈ K, e * k * e⁻¹ ∈ K := by
  classical
  have : Finite M := Finite.of_surjective η hη
  have hSU : ∀ i ≤ m, S i ≤ U := by
    have key : ∀ k i, i + k = m → S i ≤ U := by
      intro k
      induction k with
      | zero =>
        intro i hi
        rw [add_zero] at hi
        rw [hi, hSm]
      | succ k ih =>
        intro i hi
        exact (hmono i (by omega)).trans (ih (i + 1) (by omega))
    intro i hi
    exact key (m - i) i (by omega)
  let actU : MulDistribMulAction T U :=
    { smul := fun t x => ⟨τ t * x * (τ t)⁻¹, hτU t x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change τ 1 * (x : M) * (τ 1)⁻¹ = x
        rw [map_one, one_mul, inv_one, mul_one])
      mul_smul := fun s t x => Subtype.ext (by
        change τ (s * t) * (x : M) * (τ (s * t))⁻¹ = τ s * (τ t * x * (τ t)⁻¹) * (τ s)⁻¹
        rw [map_mul]
        group)
      smul_mul := fun t x y => Subtype.ext (by
        change τ t * ((x : M) * y) * (τ t)⁻¹ = τ t * x * (τ t)⁻¹ * (τ t * y * (τ t)⁻¹)
        group)
      smul_one := fun t => Subtype.ext (by
        change τ t * 1 * (τ t)⁻¹ = 1
        group) }
  let ℓ : T → E := fun t => Function.surjInv hη (τ t)
  have hℓ : ∀ t, η (ℓ t) = τ t := fun t => Function.surjInv_eq hη _
  have hcen : ∀ c ∈ η.ker, ∀ g : E, c * g = g * c := fun c hc g =>
    ((mem_center_iff.1 (hC hc)) g).symm
  have hconj : ∀ c ∈ η.ker, ∀ x : E, c * x * c⁻¹ = x := fun c hc x => by
    rw [hcen c hc x, mul_inv_cancel_right]
  have hℓone : ∀ x : E, ℓ 1 * x * (ℓ 1)⁻¹ = x := fun x =>
    hconj _ (by rw [MonoidHom.mem_ker, hℓ, map_one]) x
  have hℓmul : ∀ (s t : T) (x : E),
      ℓ (s * t) * x * (ℓ (s * t))⁻¹ = ℓ s * (ℓ t * x * (ℓ t)⁻¹) * (ℓ s)⁻¹ := by
    intro s t x
    have hc : (ℓ s * ℓ t)⁻¹ * ℓ (s * t) ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hℓ, hℓ, hℓ, map_mul, inv_mul_cancel]
    obtain ⟨c, hc', hcdef⟩ : ∃ c ∈ η.ker, ℓ (s * t) = ℓ s * ℓ t * c := ⟨_, hc, by group⟩
    rw [hcdef]
    calc ℓ s * ℓ t * c * x * (ℓ s * ℓ t * c)⁻¹ =
        ℓ s * ℓ t * (c * x * c⁻¹) * (ℓ t)⁻¹ * (ℓ s)⁻¹ := by group
      _ = ℓ s * (ℓ t * x * (ℓ t)⁻¹) * (ℓ s)⁻¹ := by rw [hconj c hc' x]; group
  set P : Subgroup E := U.comap η with hPdef
  have hηℓ : ∀ t (x : E), η (ℓ t * x * (ℓ t)⁻¹) = τ t * η x * (τ t)⁻¹ := by
    intro t x
    rw [map_mul, map_mul, map_inv, hℓ]
  have hℓP : ∀ t, ∀ x ∈ P, ℓ t * x * (ℓ t)⁻¹ ∈ P := fun t x hx => by
    change η (ℓ t * x * (ℓ t)⁻¹) ∈ U
    rw [hηℓ]
    exact hτU t _ hx
  let actP : MulDistribMulAction T P :=
    { smul := fun t x => ⟨ℓ t * x * (ℓ t)⁻¹, hℓP t x x.2⟩
      one_smul := fun x => Subtype.ext (hℓone x)
      mul_smul := fun s t x => Subtype.ext (hℓmul s t x)
      smul_mul := fun t x y => Subtype.ext (by
        change ℓ t * ((x : E) * y) * (ℓ t)⁻¹ = ℓ t * x * (ℓ t)⁻¹ * (ℓ t * y * (ℓ t)⁻¹)
        group)
      smul_one := fun t => Subtype.ext (by
        change ℓ t * 1 * (ℓ t)⁻¹ = 1
        group) }
  let ηP : P →* U :=
    { toFun := fun x => ⟨η x, x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hηP : Function.Surjective ηP := by
    intro u
    obtain ⟨e, he⟩ := hη u
    have heP : e ∈ P := by
      change η e ∈ U
      rw [he]
      exact u.2
    exact ⟨⟨e, heP⟩, Subtype.ext he⟩
  have hkerP : ∀ c : P, c ∈ ηP.ker → (c : E) ∈ η.ker := fun c hc => by
    rw [MonoidHom.mem_ker] at hc ⊢
    exact congrArg (Subtype.val : U → M) hc
  have hCP : ηP.ker ≤ center P := fun c hc =>
    mem_center_iff.2 fun g => Subtype.ext (hcen _ (hkerP c hc) g).symm
  have hpP : IsPGroup p ηP.ker := by
    let φ : ηP.ker →* η.ker :=
      (P.subtype.comp ηP.ker.subtype).codRestrict η.ker fun c => hkerP c c.2
    refine hp.of_injective φ fun c c' hcc' => ?_
    exact Subtype.ext (Subtype.ext (congrArg (Subtype.val : η.ker → E) hcc'))
  have hTC : ∀ (t : T), ∀ c ∈ ηP.ker, t • c = c := fun t c hc =>
    Subtype.ext (by
      change ℓ t * (c : E) * (ℓ t)⁻¹ = c
      rw [← hcen _ (hkerP c hc) (ℓ t), mul_inv_cancel_right])
  have hequiv : ∀ (t : T) (x : P), ηP (t • x) = t • ηP x := fun t x =>
    Subtype.ext (hηℓ t x)
  let SU : ℕ → Subgroup U := fun i => (S i).subgroupOf U
  have hSU0 : SU 0 = ⊥ := by
    change (S 0).subgroupOf U = ⊥
    rw [hS0]
    exact bot_subgroupOf U
  have hSUm : SU m = ⊤ := by
    change (S m).subgroupOf U = ⊤
    rw [hSm]
    exact subgroupOf_self U
  have hSUmono : ∀ i < m, SU i ≤ SU (i + 1) := fun i hi x hx => hmono i hi hx
  have hSUinv : ∀ i ≤ m, ∀ (t : T), ∀ x ∈ SU i, t • x ∈ SU i := fun i hi t x hx =>
    hinv i hi t x hx
  have hSUcent : ∀ i < m, ∀ x ∈ SU (i + 1), ∀ g : U, x⁻¹ * g⁻¹ * x * g ∈ SU i :=
    fun i hi x hx g => hcent i hi x hx g g.2
  have hSUsq : ∀ i < m, ∀ x ∈ SU (i + 1), x ^ p ∈ SU i := fun i hi x hx => by
    change ((x ^ p : U) : M) ∈ S i
    rw [SubgroupClass.coe_pow]
    exact hsq i hi x hx
  have hSUfix : ∀ i < m, ∀ x ∈ SU (i + 1), (∀ t : T, (t • x)⁻¹ * x ∈ SU i) → x ∈ SU i :=
    fun i hi x hx hfx => hfix i hi x hx fun t => hfx t
  have hSUbil : ∀ i < m, ∀ j < m, ∀ b : U → U → ZMod p,
      (∀ x ∈ SU (i + 1), ∀ x' ∈ SU (i + 1), ∀ y ∈ SU (j + 1),
        b (x * x') y = b x y + b x' y) →
      (∀ x ∈ SU (i + 1), ∀ y ∈ SU (j + 1), ∀ y' ∈ SU (j + 1),
        b x (y * y') = b x y + b x y') →
      (∀ x ∈ SU i, ∀ y ∈ SU (j + 1), b x y = 0) → (∀ x ∈ SU (i + 1), ∀ y ∈ SU j, b x y = 0) →
      (i = j → ∀ x ∈ SU (i + 1), b x x = 0) →
      (∀ (t : T), ∀ x ∈ SU (i + 1), ∀ y ∈ SU (j + 1), b (t • x) (t • y) = b x y) →
      ∀ x ∈ SU (i + 1), ∀ y ∈ SU (j + 1), b x y = 0 := by
    intro i hi j hj b h₁ h₂ h₃ h₄ halt h₅ x hx y hy
    let bM : M → M → ZMod p := fun x y =>
      if hx : x ∈ U then if hy : y ∈ U then b ⟨x, hx⟩ ⟨y, hy⟩ else 0 else 0
    have hbM : ∀ x y : U, bM x y = b x y := fun x y => by
      simp only [bM, x.2, y.2, dite_true]
    have hmem : ∀ k ≤ m, ∀ z ∈ S k, z ∈ U := fun k hk z hz => hSU k hk hz
    have key := hbil i hi j hj bM ?_ ?_ ?_ ?_ ?_ ?_ x hx y hy
    · rwa [hbM] at key
    · intro z hz z' hz' w hw
      have e := h₁ ⟨z, hmem _ (by omega) z hz⟩ hz ⟨z', hmem _ (by omega) z' hz'⟩ hz'
        ⟨w, hmem _ (by omega) w hw⟩ hw
      rw [← hbM, ← hbM, ← hbM] at e
      exact e
    · intro z hz w hw w' hw'
      have e := h₂ ⟨z, hmem _ (by omega) z hz⟩ hz ⟨w, hmem _ (by omega) w hw⟩ hw
        ⟨w', hmem _ (by omega) w' hw'⟩ hw'
      rw [← hbM, ← hbM, ← hbM] at e
      exact e
    · intro z hz w hw
      have e := h₃ ⟨z, hmem _ (by omega) z hz⟩ hz ⟨w, hmem _ (by omega) w hw⟩ hw
      rw [← hbM] at e
      exact e
    · intro z hz w hw
      have e := h₄ ⟨z, hmem _ (by omega) z hz⟩ hz ⟨w, hmem _ (by omega) w hw⟩ hw
      rw [← hbM] at e
      exact e
    · intro hij z hz
      have e := halt hij ⟨z, hmem _ (by omega) z hz⟩ hz
      rw [← hbM] at e
      exact e
    · intro t z hz w hw
      have e := h₅ t ⟨z, hmem _ (by omega) z hz⟩ hz ⟨w, hmem _ (by omega) w hw⟩ hw
      rw [← hbM, ← hbM] at e
      exact e
  obtain ⟨K, hKinv, -, hKcompl, hKbij⟩ := coprime_central_series_central_p_extension_splitting_alt
    hT hUp m SU hSU0 hSUm hSUmono hSUinv hSUcent hSUsq hSUfix hSUbil ηP hηP hCP hpP hTC hequiv
  refine ⟨K.map P.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · rintro _ ⟨k, hk, rfl⟩ h1
    have hk' : k ∈ ηP.ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h1
    rw [(disjoint_def.1 hKcompl.disjoint) hk' hk]
    rfl
  · intro u hu
    obtain ⟨k, hk⟩ := hKbij.2 ⟨u, hu⟩
    exact ⟨(k : P), ⟨k, k.2, rfl⟩, congrArg (Subtype.val : U → M) hk⟩
  · rintro t e he _ ⟨k, hk, rfl⟩
    have hc : (ℓ t)⁻¹ * e ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hℓ, he, inv_mul_cancel]
    obtain ⟨c, hc', rfl⟩ : ∃ c ∈ η.ker, e = ℓ t * c := ⟨_, hc, by group⟩
    have h1 : ℓ t * c * (k : E) * (ℓ t * c)⁻¹ = ℓ t * k * (ℓ t)⁻¹ := by
      calc ℓ t * c * (k : E) * (ℓ t * c)⁻¹ = ℓ t * (c * k * c⁻¹) * (ℓ t)⁻¹ := by group
        _ = ℓ t * k * (ℓ t)⁻¹ := by rw [hconj c hc' k]
    rw [coe_subtype, h1]
    exact ⟨t • k, hKinv t k hk, rfl⟩

theorem invariant_lift_unique {M E : Type*} [Group M] [Group E] (η : E →* M)
    (hC : η.ker ≤ center E) {U : Subgroup M} {e₀ : E}
    (hU : ∀ φ : M → E, (∀ x ∈ U, φ x ∈ η.ker) → (∀ x ∈ U, ∀ y ∈ U, φ (x * y) = φ x * φ y) →
      (∀ x ∈ U, φ (η e₀ * x * (η e₀)⁻¹) = φ x) → ∀ x ∈ U, φ x = 1)
    {K₁ K₂ : Subgroup E} (h₁U : ∀ k ∈ K₁, η k ∈ U) (h₂U : ∀ k ∈ K₂, η k ∈ U)
    (h₁C : ∀ k ∈ K₁, η k = 1 → k = 1) (h₂C : ∀ k ∈ K₂, η k = 1 → k = 1)
    (h₁s : ∀ u ∈ U, ∃ k ∈ K₁, η k = u) (h₂s : ∀ u ∈ U, ∃ k ∈ K₂, η k = u)
    (h₁e : ∀ k ∈ K₁, e₀ * k * e₀⁻¹ ∈ K₁) (h₂e : ∀ k ∈ K₂, e₀ * k * e₀⁻¹ ∈ K₂) : K₁ = K₂ := by
  classical
  have huniq : ∀ {K : Subgroup E}, (∀ k ∈ K, η k = 1 → k = 1) → ∀ k ∈ K, ∀ k' ∈ K,
      η k = η k' → k = k' := fun hKC k hk k' hk' h => by
    have h1 := hKC _ (mul_mem (inv_mem hk) hk') (by rw [map_mul, map_inv, h, inv_mul_cancel])
    rw [← mul_left_cancel_iff (a := k⁻¹), inv_mul_cancel, h1]
  have hcen : ∀ c ∈ η.ker, ∀ g : E, c * g = g * c := fun c hc g =>
    ((mem_center_iff.1 (hC hc)) g).symm
  choose f₁ hf₁ using h₁s
  choose f₂ hf₂ using h₂s
  let φ : M → E := fun u => if hu : u ∈ U then (f₁ u hu)⁻¹ * f₂ u hu else 1
  have hφ : ∀ u (hu : u ∈ U), φ u = (f₁ u hu)⁻¹ * f₂ u hu := fun u hu => dite_eq_left hu
  have hφC : ∀ x ∈ U, φ x ∈ η.ker := fun x hx => by
    rw [hφ x hx, MonoidHom.mem_ker, map_mul, map_inv, (hf₁ x hx).2, (hf₂ x hx).2,
      inv_mul_cancel]
  have hmul₁ : ∀ x (hx : x ∈ U) y (hy : y ∈ U),
      f₁ (x * y) (mul_mem hx hy) = f₁ x hx * f₁ y hy := fun x hx y hy =>
    huniq h₁C _ (hf₁ _ _).1 _ (mul_mem (hf₁ x hx).1 (hf₁ y hy).1)
      (by rw [(hf₁ _ _).2, map_mul, (hf₁ x hx).2, (hf₁ y hy).2])
  have hmul₂ : ∀ x (hx : x ∈ U) y (hy : y ∈ U),
      f₂ (x * y) (mul_mem hx hy) = f₂ x hx * f₂ y hy := fun x hx y hy =>
    huniq h₂C _ (hf₂ _ _).1 _ (mul_mem (hf₂ x hx).1 (hf₂ y hy).1)
      (by rw [(hf₂ _ _).2, map_mul, (hf₂ x hx).2, (hf₂ y hy).2])
  have hφmul : ∀ x ∈ U, ∀ y ∈ U, φ (x * y) = φ x * φ y := fun x hx y hy => by
    rw [hφ _ (mul_mem hx hy), hφ x hx, hφ y hy, hmul₁ x hx y hy, hmul₂ x hx y hy]
    have hc := hcen _ (hφC x hx) (f₁ y hy)⁻¹
    rw [hφ x hx] at hc
    calc (f₁ x hx * f₁ y hy)⁻¹ * (f₂ x hx * f₂ y hy) =
        (f₁ y hy)⁻¹ * ((f₁ x hx)⁻¹ * f₂ x hx) * f₂ y hy := by group
      _ = (f₁ x hx)⁻¹ * f₂ x hx * ((f₁ y hy)⁻¹ * f₂ y hy) := by rw [← hc]; group
  have hconjU : ∀ x ∈ U, η e₀ * x * (η e₀)⁻¹ ∈ U := fun x hx => by
    have h := h₁U _ (h₁e _ (hf₁ x hx).1)
    rwa [map_mul, map_mul, map_inv, (hf₁ x hx).2] at h
  have hconj₁ : ∀ x (hx : x ∈ U), f₁ (η e₀ * x * (η e₀)⁻¹) (hconjU x hx) =
      e₀ * f₁ x hx * e₀⁻¹ := fun x hx =>
    huniq h₁C _ (hf₁ _ _).1 _ (h₁e _ (hf₁ x hx).1)
      (by rw [(hf₁ _ _).2, map_mul, map_mul, map_inv, (hf₁ x hx).2])
  have hconj₂ : ∀ x (hx : x ∈ U), f₂ (η e₀ * x * (η e₀)⁻¹) (hconjU x hx) =
      e₀ * f₂ x hx * e₀⁻¹ := fun x hx =>
    huniq h₂C _ (hf₂ _ _).1 _ (h₂e _ (hf₂ x hx).1)
      (by rw [(hf₂ _ _).2, map_mul, map_mul, map_inv, (hf₂ x hx).2])
  have hφconj : ∀ x ∈ U, φ (η e₀ * x * (η e₀)⁻¹) = φ x := fun x hx => by
    rw [hφ _ (hconjU x hx), hconj₁ x hx, hconj₂ x hx, hφ x hx]
    have hc := hcen _ (hφC x hx) e₀
    rw [hφ x hx] at hc
    calc (e₀ * f₁ x hx * e₀⁻¹)⁻¹ * (e₀ * f₂ x hx * e₀⁻¹) =
        e₀ * ((f₁ x hx)⁻¹ * f₂ x hx) * e₀⁻¹ := by group
      _ = (f₁ x hx)⁻¹ * f₂ x hx := by rw [← hc, mul_inv_cancel_right]
  have hφ1 := hU φ hφC hφmul hφconj
  have heq : ∀ x (hx : x ∈ U), f₁ x hx = f₂ x hx := fun x hx => by
    have h := hφ1 x hx
    rw [hφ x hx] at h
    exact (inv_mul_eq_one.1 h)
  refine le_antisymm (fun k hk => ?_) (fun k hk => ?_)
  · have h1 := huniq h₁C _ hk _ (hf₁ _ (h₁U k hk)).1 (hf₁ _ (h₁U k hk)).2.symm
    rw [h1, heq]
    exact (hf₂ _ _).1
  · have h1 := huniq h₂C _ hk _ (hf₂ _ (h₂U k hk)).1 (hf₂ _ (h₂U k hk)).2.symm
    rw [h1, ← heq]
    exact (hf₁ _ _).1

theorem exists_section_of_cover_trivial {G : Type v} [Group G] [Group.IsPerfect G] {p : ℕ}
    (htriv : ∀ (P : Type u) [Group P] [Finite P] [Group.IsPerfect P] (η : P →* G),
      Function.Surjective η → η.ker ≤ center P → IsPGroup p η.ker → η.ker = ⊥)
    {H : Type u} [Group H] [Finite H] (ρ : H →* G) (hρ : Function.Surjective ρ)
    (hcen : ρ.ker ≤ center H) (hp : IsPGroup p ρ.ker) : ∃ s : G →* H, ∀ g, ρ (s g) = g := by
  obtain ⟨hperf, hsurj, hker⟩ := CFSG.RankThree.CentralLiftU.derived_restrict_facts ρ hρ hcen
  exact CFSG.RankThree.CentralLiftU.exists_section_of_ker_comp_eq_bot ρ (commutator H) hsurj
    (htriv (commutator H) (ρ.comp (commutator H).subtype) hsurj hker
      (CFSG.RankThree.CentralLiftU.isPGroup_ker_comp_subtype ρ hp _))

theorem ker_eq_bot_of_levi_lift {p : ℕ} [Fact p.Prime] {M G E : Type*} [Group M] [Group G]
    [Group E] [Finite E] [Group.IsPerfect E] (η : E →* M) (hη : Function.Surjective η)
    (hC : η.ker ≤ center E) (hp : IsPGroup p η.ker) {Q : Subgroup M} (L : G →* M)
    (hL : Function.Injective L) (hQL : ∀ x ∈ Q, x ∈ L.range → x = 1) {K : Subgroup E}
    (hKQ : ∀ k ∈ K, η k ∈ Q) (hKC : ∀ k ∈ K, η k = 1 → k = 1)
    (hKs : ∀ u ∈ Q, ∃ k ∈ K, η k = u) (s : G →* E) (hs : ∀ g, η (s g) = L g)
    (hsK : ∀ g, ∀ k ∈ K, s g * k * (s g)⁻¹ ∈ K) (S' : Subgroup G) (P : Sylow p M)
    (hP : (P : Subgroup M) ≤ Q ⊔ S'.map L) : η.ker = ⊥ := by
  have hN : S'.map s ≤ normalizer (K : Set E) := by
    rintro _ ⟨g, -, rfl⟩
    refine mem_normalizer_iff.2 fun k => ⟨hsK g k, fun hk => ?_⟩
    have h1 := hsK g⁻¹ _ hk
    rwa [map_inv, inv_inv, show (s g)⁻¹ * (s g * k * (s g)⁻¹) * s g = k by group] at h1
  have hmap : (P : Subgroup M) ≤ (K ⊔ S'.map s).map η := by
    refine hP.trans (sup_le ?_ ?_)
    · intro u hu
      obtain ⟨k, hk, rfl⟩ := hKs u hu
      exact ⟨k, mem_sup_left hk, rfl⟩
    · rintro _ ⟨g, hg, rfl⟩
      exact ⟨s g, mem_sup_right ⟨g, hg, rfl⟩, hs g⟩
  have hle := ker_le_of_sylow_le_map_prime η hη hC hp P (K ⊔ S'.map s) hmap
  refine eq_bot_iff.2 fun z hz => ?_
  have hz' : z ∈ ((K ⊔ S'.map s : Subgroup E) : Set E) := hle hz
  rw [coe_mul_of_right_le_normalizer_left K (S'.map s) hN] at hz'
  obtain ⟨k, hk, _, ⟨g, -, rfl⟩, rfl⟩ := Set.mem_mul.1 hz'
  have h1 : η k * L g = 1 := by rw [← hs, ← map_mul]; exact hz
  have h2 : η k = L g⁻¹ := by rw [map_inv]; exact eq_inv_of_mul_eq_one_left h1
  have h3 : η k = 1 := hQL _ (hKQ k hk) ⟨g⁻¹, h2.symm⟩
  have hLg : L g = 1 := by
    rw [h3, one_mul] at h1
    exact h1
  have hg1 : g = 1 := hL (by rw [hLg, map_one])
  rw [mem_bot, hKC k hk h3, hg1, map_one, one_mul]

end CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree
