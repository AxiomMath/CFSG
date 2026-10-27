module

public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesSplittingCommuting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLift

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem ker_eq_bot_of_coprime_central_series_of_commute {M : Type*} [Group M] {Γ : Subgroup M}
    [Finite Γ] {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (η : E →* Γ)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker)
    {U : Subgroup M} (hUΓ : U ≤ Γ) (hUp : IsPGroup 2 (U.subgroupOf Γ))
    (hUi : ¬ 2 ∣ (U.subgroupOf Γ).index)
    {T : Type*} [Group T] [Finite T] (hT : Odd (Nat.card T)) (τ : T →* M)
    (hτΓ : ∀ t, τ t ∈ Γ) (hτU : ∀ t, ∀ x ∈ U, τ t * x * (τ t)⁻¹ ∈ U)
    (m : ℕ) (S : ℕ → Subgroup M) (hS0 : S 0 = ⊥) (hSm : S m = U)
    (hmono : ∀ i < m, S i ≤ S (i + 1))
    (hinv : ∀ i ≤ m, ∀ (t : T), ∀ x ∈ S i, τ t * x * (τ t)⁻¹ ∈ S i)
    (hcent : ∀ i < m, ∀ x ∈ S (i + 1), ∀ g ∈ U, x⁻¹ * g⁻¹ * x * g ∈ S i)
    (hsq : ∀ i < m, ∀ x ∈ S (i + 1), x ^ 2 ∈ S i)
    (hfix : ∀ i < m, ∀ x ∈ S (i + 1), (∀ t : T, (τ t * x * (τ t)⁻¹)⁻¹ * x ∈ S i) → x ∈ S i)
    {ι : Type*} (Zs Ys : ι → Set M) (hZsU : ∀ k, Zs k ⊆ U) (hYsU : ∀ k, Ys k ⊆ U)
    (hbil : ∀ i < m, ∀ j < m, ∀ b : M → M → ZMod 2,
      (∀ x ∈ S (i + 1), ∀ x' ∈ S (i + 1), ∀ y ∈ S (j + 1), b (x * x') y = b x y + b x' y) →
      (∀ x ∈ S (i + 1), ∀ y ∈ S (j + 1), ∀ y' ∈ S (j + 1), b x (y * y') = b x y + b x y') →
      (∀ x ∈ S i, ∀ y ∈ S (j + 1), b x y = 0) → (∀ x ∈ S (i + 1), ∀ y ∈ S j, b x y = 0) →
      (∀ (t : T), ∀ x ∈ S (i + 1), ∀ y ∈ S (j + 1),
        b (τ t * x * (τ t)⁻¹) (τ t * y * (τ t)⁻¹) = b x y) →
      (∀ k, ∀ z ∈ Zs k, ∀ y ∈ Ys k, b z y = 0) →
      ∀ x ∈ S (i + 1), ∀ y ∈ S (j + 1), b x y = 0)
    (hlift : ∀ k, ∀ a y : E, ((η a : Γ) : M) ∈ Zs k → ((η y : Γ) : M) ∈ Ys k → a * y = y * a) :
    η.ker = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  have : Finite U := Finite.of_equiv _ (subgroupOfEquivOfLe hUΓ).toEquiv
  have hU2 : IsPGroup 2 U := hUp.of_equiv (subgroupOfEquivOfLe hUΓ)
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
  let τG : T →* Γ := τ.codRestrict Γ hτΓ
  let ℓ : T → E := fun t => Function.surjInv hη (τG t)
  have hℓ : ∀ t, η (ℓ t) = τG t := fun t => Function.surjInv_eq hη _
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
  set P : Subgroup E := (U.subgroupOf Γ).comap η with hPdef
  have hηℓ : ∀ t (x : E), ((η (ℓ t * x * (ℓ t)⁻¹) : Γ) : M) = τ t * (η x : M) * (τ t)⁻¹ := by
    intro t x
    rw [map_mul, map_mul, map_inv, hℓ]
    rfl
  have hℓP : ∀ t, ∀ x ∈ P, ℓ t * x * (ℓ t)⁻¹ ∈ P := fun t x hx => by
    change ((η (ℓ t * x * (ℓ t)⁻¹) : Γ) : M) ∈ U
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
    { toFun := fun x => ⟨(η x : M), x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hηP : Function.Surjective ηP := by
    intro u
    obtain ⟨e, he⟩ := hη ⟨u, hUΓ u.2⟩
    have heP : e ∈ P := by
      change ((η e : Γ) : M) ∈ U
      rw [he]
      exact u.2
    exact ⟨⟨e, heP⟩, Subtype.ext (by
      change ((η e : Γ) : M) = u
      rw [he])⟩
  have hkerP : ∀ c : P, c ∈ ηP.ker → (c : E) ∈ η.ker := fun c hc => by
    rw [MonoidHom.mem_ker] at hc ⊢
    exact Subtype.ext (congrArg (Subtype.val : U → M) hc)
  have hCP : ηP.ker ≤ center P := fun c hc =>
    mem_center_iff.2 fun g => Subtype.ext (hcen _ (hkerP c hc) g).symm
  have h2P : IsPGroup 2 ηP.ker := by
    let φ : ηP.ker →* η.ker :=
      (P.subtype.comp ηP.ker.subtype).codRestrict η.ker fun c => hkerP c c.2
    refine h2.of_injective φ fun c c' hcc' => ?_
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
  have hSUsq : ∀ i < m, ∀ x ∈ SU (i + 1), x ^ 2 ∈ SU i := fun i hi x hx => by
    change ((x ^ 2 : U) : M) ∈ S i
    rw [SubgroupClass.coe_pow]
    exact hsq i hi x hx
  have hSUfix : ∀ i < m, ∀ x ∈ SU (i + 1), (∀ t : T, (t • x)⁻¹ * x ∈ SU i) → x ∈ SU i :=
    fun i hi x hx hfx => hfix i hi x hx fun t => hfx t
  let ZsU : ι → Set U := fun k => {u | (u : M) ∈ Zs k}
  let YsU : ι → Set U := fun k => {u | (u : M) ∈ Ys k}
  have hZY : ∀ k, ∀ a y : P, ηP a ∈ ZsU k → ηP y ∈ YsU k → a * y = y * a := fun k a y ha hy =>
    Subtype.ext (hlift k a y ha hy)
  have hSUbil : ∀ i < m, ∀ j < m, ∀ b : U → U → ZMod 2,
      (∀ x ∈ SU (i + 1), ∀ x' ∈ SU (i + 1), ∀ y ∈ SU (j + 1),
        b (x * x') y = b x y + b x' y) →
      (∀ x ∈ SU (i + 1), ∀ y ∈ SU (j + 1), ∀ y' ∈ SU (j + 1),
        b x (y * y') = b x y + b x y') →
      (∀ x ∈ SU i, ∀ y ∈ SU (j + 1), b x y = 0) → (∀ x ∈ SU (i + 1), ∀ y ∈ SU j, b x y = 0) →
      (∀ (t : T), ∀ x ∈ SU (i + 1), ∀ y ∈ SU (j + 1), b (t • x) (t • y) = b x y) →
      (∀ k, ∀ z ∈ ZsU k, ∀ y ∈ YsU k, b z y = 0) →
      ∀ x ∈ SU (i + 1), ∀ y ∈ SU (j + 1), b x y = 0 := by
    intro i hi j hj b h₁ h₂ h₃ h₄ h₅ h₆ x hx y hy
    let bM : M → M → ZMod 2 := fun x y =>
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
    · intro t z hz w hw
      have e := h₅ t ⟨z, hmem _ (by omega) z hz⟩ hz ⟨w, hmem _ (by omega) w hw⟩ hw
      rw [← hbM, ← hbM] at e
      exact e
    · intro k z hz w hw
      have e := h₆ k ⟨z, hZsU k hz⟩ hz ⟨w, hYsU k hw⟩ hw
      rw [← hbM] at e
      exact e
  obtain ⟨K, -, -, hKcompl, hKbij⟩ :=
    coprime_central_series_central_two_extension_splitting_of_commute hT hU2 m SU hSU0 hSUm
      hSUmono hSUinv hSUcent hSUsq hSUfix ZsU YsU hSUbil ηP hηP hCP h2P hTC hequiv hZY
  set Syl : Sylow 2 Γ := hUp.toSylow hUi
  have hSyl : (U.subgroupOf Γ) ≤ (K.map P.subtype).map η := by
    intro y hy
    obtain ⟨k, hk⟩ := hKbij.2 ⟨y, hy⟩
    refine ⟨((k : P) : E), ⟨k, k.2, rfl⟩, Subtype.ext ?_⟩
    exact congrArg (Subtype.val : U → M) hk
  have hle := OrthogonalSplit.ker_le_of_sylow_le_map η hη hC h2 Syl (K.map P.subtype)
    (by rw [IsPGroup.toSylow_coe]; exact hSyl)
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨k, hkK, rfl⟩ := hle hz
  have hz' : η (k : E) = 1 := hz
  have hk : k ∈ ηP.ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (congrArg (Subtype.val : Γ → M) hz')
  have hk1 : k = 1 := (disjoint_def.1 hKcompl.disjoint) hk hkK
  rw [hk1]
  exact one_mem _

end CFSG.LocalAnalysis.ComponentInitial
