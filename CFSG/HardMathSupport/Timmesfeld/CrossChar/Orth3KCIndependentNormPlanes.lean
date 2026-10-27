module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3KCNormPlaneAssembly
public import CFSG.RankThree.PartOne.KC.OrthogonalDerivedCentralizer
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneAssembly
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneInvolution

public section


namespace CFSG.RankThree.PartOne
open Polynomial Module QuadraticMap CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
theorem independent_orthogonal_norm_planes_split_four_local_layer_generation_full3
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hpne : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K) (hpq : p ∣
        Nat.card K + 1)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (Atil : Subgroup (orthDerived Q)) (hAtil : Assembly.IsElemAbelian p Atil)
    (hAcard : Nat.card Atil = p ^ 2) {E : Type*} [Field E] [Algebra K E]
    (hE : finrank K E = 2) {ζ : E} (hζ : orderOf ζ = p) (U₁ U₂ : Submodule K V)
    (hU₁ : finrank K U₁ = 2) (hU₂ : finrank K U₂ = 2)
    (hU₁reg : (polarBilin (Q.comp U₁.subtype)).Nondegenerate)
    (hU₂reg : (polarBilin (Q.comp U₂.subtype)).Nondegenerate)
    (hU₁₂ : ∀ x ∈ U₁, ∀ y ∈ U₂, polar Q x y = 0)
    (hU₁inv : ∀ y ∈ Atil, ∀ x ∈ U₁, ((y : orthDerived Q) : V ≃ₗ[K] V) x ∈ U₁)
    (hU₂inv : ∀ y ∈ Atil, ∀ x ∈ U₂, ((y : orthDerived Q) : V ≃ₗ[K] V) x ∈ U₂)
    (φ₁ : E →ₗ[K] U₁) (φ₂ : E →ₗ[K] U₂)
    (hφ₁ : ∀ z, algebraMap K E (Q (φ₁ z : V)) = z * z ^ Nat.card K)
    (hφ₂ : ∀ z, algebraMap K E (Q (φ₂ z : V)) = z * z ^ Nat.card K)
    (χ₁ χ₂ : Atil →* Multiplicative (ZMod p))
    (hχ : ∀ m n : ZMod p, (∀ y : Atil, m * (χ₁ y).toAdd + n * (χ₂ y).toAdd = 0) → m = 0 ∧ n = 0)
    (hy₁ : ∀ (y : Atil) (z : E), ((y : orthDerived Q) : V ≃ₗ[K] V) (φ₁ z : V) =
      (φ₁ (ζ ^ (χ₁ y).toAdd.val * z) : V))
    (hy₂ : ∀ (y : Atil) (z : E), ((y : orthDerived Q) : V ≃ₗ[K] V) (φ₂ z : V) =
      (φ₂ (ζ ^ (χ₂ y).toAdd.val * z) : V))
    (a : Atil) (ha1 : a ≠ 1) (ha : χ₁ a = χ₂ a)
    (b : Atil) (hb1 : b ≠ 1) (hb : χ₁ b * χ₂ b = 1) :
    (Group.IsPerfect ↥(supportedOrthDerived Q (U₁ ⊔ U₂)) ∧
      supportedOrthDerived Q (U₁ ⊔ U₂) ≤ orthDerived Q) ∧
    (((supportedOrthDerived Q (U₁ ⊔ U₂)).subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).map
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤
      inSubgroup layer (D ⊓ Subgroup.centralizer
        ({MulAut.conj (QuotientGroup.mk (a : orthDerived Q) : ProjOrthDerived Q)} :
          Set (MulAut (ProjOrthDerived Q)))) ⊔
      inSubgroup layer (D ⊓ Subgroup.centralizer
        ({MulAut.conj (QuotientGroup.mk (b : orthDerived Q) : ProjOrthDerived Q)} :
          Set (MulAut (ProjOrthDerived Q)))) ∧
    (finrank K ↥(U₁ ⊔ U₂) = 4 ∧ (polarBilin (Q.comp (U₁ ⊔ U₂).subtype)).Nondegenerate ∧
      ∃ S : Submodule K V, S ≤ U₁ ⊔ U₂ ∧ finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) ∧
    (∃ ι₁ ι₂ : Matrix.SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V),
      Function.Injective ι₁ ∧ Function.Injective ι₂ ∧
      (∀ g h, ι₁ g * ι₂ h = ι₂ h * ι₁ g) ∧
      ι₁.range ⊔ ι₂.range = supportedOrthDerived Q (U₁ ⊔ U₂) ∧
      (∃ h ∈ primaryFactors (((b : orthDerived Q) : V ≃ₗ[K] V)).toLinearMap, h ≠ X - 1 ∧
        h = reciprocalPolynomial h ∧
        2 ≤ primaryMultiplicity (((b : orthDerived Q) : V ≃ₗ[K] V)).toLinearMap h ∧
        ι₁.range ≤ specialBlock Q ((b : orthDerived Q) : V ≃ₗ[K] V) h ∧
        specialBlock Q ((b : orthDerived Q) : V ≃ₗ[K] V) h ≤ orthDerived Q ⊓
          Subgroup.centralizer ({((b : orthDerived Q) : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) ∧
        specialBlock Q ((b : orthDerived Q) : V ≃ₗ[K] V) h ≠ ⊥ ∧
        IsComponent (((componentImage Q ((b : orthDerived Q) : V ≃ₗ[K] V) h).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
          (D ⊓ Subgroup.centralizer
            ({MulAut.conj (QuotientGroup.mk (b : orthDerived Q) : ProjOrthDerived Q)} :
              Set (MulAut (ProjOrthDerived Q)))))) ∧
      (∃ h ∈ primaryFactors (((a : orthDerived Q) : V ≃ₗ[K] V)).toLinearMap, h ≠ X - 1 ∧
        h = reciprocalPolynomial h ∧
        2 ≤ primaryMultiplicity (((a : orthDerived Q) : V ≃ₗ[K] V)).toLinearMap h ∧
        ι₂.range ≤ specialBlock Q ((a : orthDerived Q) : V ≃ₗ[K] V) h ∧
        specialBlock Q ((a : orthDerived Q) : V ≃ₗ[K] V) h ≤ orthDerived Q ⊓
          Subgroup.centralizer ({((a : orthDerived Q) : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) ∧
        specialBlock Q ((a : orthDerived Q) : V ≃ₗ[K] V) h ≠ ⊥ ∧
        IsComponent (((componentImage Q ((a : orthDerived Q) : V ≃ₗ[K] V) h).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
          (D ⊓ Subgroup.centralizer
            ({MulAut.conj (QuotientGroup.mk (a : orthDerived Q) : ProjOrthDerived Q)} :
              Set (MulAut (ProjOrthDerived Q))))))) ∧
    (Q (φ₁ 1 : V) = 1 ∧ Q (φ₂ 1 : V) = 1 ∧ polar Q (φ₁ 1 : V) (φ₂ 1 : V) = 0 ∧
      reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V) ∈ supportedOrthDerived Q (U₁ ⊔ U₂) ∧
      orderOf (reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V)) = 2 ∧
      ((2 : K) = 0 → reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V) =
        eichler Q ((φ₁ 1 : V) + (φ₂ 1 : V)) (φ₁ 1 : V)) ∧
      ∃ hg : reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V) ∈ orthDerived Q,
        orderOf (QuotientGroup.mk (⟨reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V), hg⟩ :
          orthDerived Q) : ProjOrthDerived Q) = 2 ∧
        orderOf (MulAut.conj (QuotientGroup.mk (⟨reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V), hg⟩ :
          orthDerived Q) : ProjOrthDerived Q)) = 2) := by
  classical
  have _hU₂reg := hU₂reg
  have _hU₁inv := hU₁inv
  have _hU₂inv := hU₂inv
  have : Fact p.Prime := ⟨hp⟩
  have hp2le := hp.two_le
  have hp5 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq : p ≤ Nat.card K + 1 := Nat.le_of_dvd (Nat.succ_pos _) hpq
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  have : Module.Finite K E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨DE, c, hbar, hc0, hNc⟩ := exists_quadData_norm hE
  have hN : NormPlanes DE Q U₁ U₂ φ₁ φ₂ :=
    ⟨hU₁, hU₂, fun v hv hv' => by
        have h0 := hU₁reg.1 ⟨v, hv⟩ (fun n => by
          rw [polarBilin_apply_apply]
          show polar Q v n = 0
          rw [polar_comm]
          exact hv' n n.2)
        simpa using congrArg Subtype.val h0,
      hU₁₂,
      fun z => (algebraMap K E).injective (by rw [hφ₁ z, DE.algebraMap_Nm, hbar]),
      fun z => (algebraMap K E).injective (by rw [hφ₂ z, DE.algebraMap_Nm, hbar])⟩
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ0 : ζ ≠ 0 := fun h0 => by
    rw [h0, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  have hζq : ζ ^ (Nat.card K + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hζ]; exact hpq)
  have hζbar : DE.bar ζ = ζ⁻¹ := by
    rw [hbar]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hζq)
  have hbarpow : ∀ k : ℕ, DE.bar (ζ ^ k) = (ζ ^ k)⁻¹ := fun k => by
    rw [map_pow, hζbar, inv_pow]
  have hpow_ne : ∀ k : ZMod p, k ≠ 0 → ζ ^ k.val ≠ 1 := by
    intro k hk h1
    have h2 : p ∣ k.val := by
      have := orderOf_dvd_of_pow_eq_one h1
      rwa [hζ] at this
    have h3 : k.val < p := ZMod.val_lt k
    have h4 : k.val = 0 := Nat.eq_zero_of_dvd_of_lt h2 h3
    exact hk ((ZMod.val_eq_zero k).mp h4)
  have ha_ne : (χ₁ a).toAdd ≠ 0 := by
    intro h0
    have h1 : χ₁ a = 1 := by simpa using h0
    have h2 : χ₂ a = 1 := by rw [← ha]; exact h1
    exact ha1 (eq_one_of_chars_ker hAcard χ₁ χ₂ hχ h1 h2)
  have hb_ne : (χ₁ b).toAdd ≠ 0 := by
    intro h0
    have h1 : χ₁ b = 1 := by simpa using h0
    have h2 : χ₂ b = 1 := by
      rw [h1, one_mul] at hb
      exact hb
    exact hb1 (eq_one_of_chars_ker hAcard χ₁ χ₂ hχ h1 h2)
  have hb_neg : (χ₂ b).toAdd = -(χ₁ b).toAdd := by
    have := congrArg Multiplicative.toAdd hb
    rw [toAdd_mul, toAdd_one] at this
    exact eq_neg_of_add_eq_zero_right this
  have hlam0 : ζ ^ (χ₁ a).toAdd.val ≠ 0 := pow_ne_zero _ hζ0
  have hlam1 : ζ ^ (χ₁ a).toAdd.val ≠ 1 := hpow_ne _ ha_ne
  have hη0 : ζ ^ (χ₁ b).toAdd.val ≠ 0 := pow_ne_zero _ hζ0
  have hη1 : ζ ^ (χ₁ b).toAdd.val ≠ 1 := hpow_ne _ hb_ne
  have hbarη : DE.bar (ζ ^ (χ₁ b).toAdd.val) = (ζ ^ (χ₁ b).toAdd.val)⁻¹ := hbarpow _
  have hbarη0 : DE.bar (ζ ^ (χ₁ b).toAdd.val) ≠ 0 := by rw [hbarη]; exact inv_ne_zero hη0
  have hx₁a : ∀ z, ((a : orthDerived Q) : V ≃ₗ[K] V) (φ₁ z : V) =
      (φ₁ (ζ ^ (χ₁ a).toAdd.val * z) : V) := hy₁ a
  have hx₂a : ∀ z, ((a : orthDerived Q) : V ≃ₗ[K] V) (φ₂ z : V) =
      (φ₂ (ζ ^ (χ₁ a).toAdd.val * z) : V) := fun z => by rw [hy₂ a z, ← ha]
  have hx₁b : ∀ z, ((b : orthDerived Q) : V ≃ₗ[K] V) (φ₁ z : V) =
      (φ₁ (ζ ^ (χ₁ b).toAdd.val * z) : V) := hy₁ b
  have hx₂b : ∀ z, ((b : orthDerived Q) : V ≃ₗ[K] V) (φ₂ z : V) =
      (φ₂ (DE.bar (ζ ^ (χ₁ b).toAdd.val) * z) : V) := fun z => by
    have hneg : ζ ^ (χ₂ b).toAdd.val = (ζ ^ (χ₁ b).toAdd.val)⁻¹ := by
      rw [hb_neg]
      exact zetaPow_neg hζp _
    rw [hy₂ b z, hbarη, hneg]
  have hxa : orderOf (a : orthDerived Q) = p :=
    orderOf_eq_prime (hAtil.2 (a : orthDerived Q) a.2) (fun h => ha1 (Subtype.ext h))
  have hxb : orderOf (b : orthDerived Q) = p :=
    orderOf_eq_prime (hAtil.2 (b : orthDerived Q) b.2) (fun h => hb1 (Subtype.ext h))
  have hxaO : ((a : orthDerived Q) : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup (a : orthDerived Q).2
  have hxbO : ((b : orthDerived Q) : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup (b : orthDerived Q).2
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl
      (Or.inr hK2) (Or.inr hK3)).1
  obtain ⟨ha_h, ha_mem, ha_ne1, ha_self, ha_mult, ha_rng, ha_le, ha_bot, ha_comp, ha_layer⟩ :=
    exists_special_component3 hQ hT hp hpne hK4 hpl D hD (a : orthDerived Q) hxa DE hlam0 hlam1
      (hbarpow _) (minpoly.aeval K _) hN hx₁a hx₂a hperf (hN.iota₂ hc0 hNc)
      (fun g => hN.factorHom_mem hc0 hNc _)
      (fun g => hN.iota₂_commute_left hc0 hNc hxaO hlam0 hx₁a hx₂a g)
      (fun g w hw => hN.factorHom_fix hc0 hNc _ hw)
  have hrootb : aeval (DE.bar (ζ ^ (χ₁ b).toAdd.val)) (minpoly K (ζ ^ (χ₁ b).toAdd.val)) = 0 := by
    have := Polynomial.aeval_algHom_apply (DE.bar : E →ₐ[K] E) (ζ ^ (χ₁ b).toAdd.val)
      (minpoly K (ζ ^ (χ₁ b).toAdd.val))
    rw [minpoly.aeval, map_zero] at this
    exact this
  obtain ⟨hb_h, hb_mem, hb_ne1, hb_self, hb_mult, hb_rng, hb_le, hb_bot, hb_comp, hb_layer⟩ :=
    exists_special_component3 hQ hT hp hpne hK4 hpl D hD (b : orthDerived Q) hxb DE hη0 hη1 hbarη
      hrootb hN hx₁b hx₂b hperf (hN.iota₁ hc0 hNc)
      (fun g => hN.factorHom_mem hc0 hNc _)
      (fun g => hN.iota₁_commute_right hc0 hNc hxbO hη0 hbarη0 hx₁b hx₂b g)
      (fun g w hw => hN.factorHom_fix hc0 hNc _ hw)
  have hrange := hN.range_sup hc0 hNc hK2 hK3
  have hleΩ := hN.supported_le_orthDerived hc0 hNc hK2 hK3
  have hFa : specialBlock Q ((a : orthDerived Q) : V ≃ₗ[K] V) ha_h ≤ orthDerived Q :=
    fun g hg => (Subgroup.mem_inf.mp (ha_le hg)).1
  have hFb : specialBlock Q ((b : orthDerived Q) : V ≃ₗ[K] V) hb_h ≤ orthDerived Q :=
    fun g hg => (Subgroup.mem_inf.mp (hb_le hg)).1
  have hlayer :
      (((supportedOrthDerived Q (U₁ ⊔ U₂)).subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).map
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤
      inSubgroup layer (D ⊓ Subgroup.centralizer
        ({MulAut.conj (QuotientGroup.mk (a : orthDerived Q) : ProjOrthDerived Q)} :
          Set (MulAut (ProjOrthDerived Q)))) ⊔
      inSubgroup layer (D ⊓ Subgroup.centralizer
        ({MulAut.conj (QuotientGroup.mk (b : orthDerived Q) : ProjOrthDerived Q)} :
          Set (MulAut (ProjOrthDerived Q)))) := by
    have hle_sup : supportedOrthDerived Q (U₁ ⊔ U₂) ≤
        specialBlock Q ((b : orthDerived Q) : V ≃ₗ[K] V) hb_h ⊔
          specialBlock Q ((a : orthDerived Q) : V ≃ₗ[K] V) ha_h := by
      rw [← hrange]
      exact sup_le_sup hb_rng ha_rng
    have hsup : (specialBlock Q ((b : orthDerived Q) : V ≃ₗ[K] V) hb_h ⊔
        specialBlock Q ((a : orthDerived Q) : V ≃ₗ[K] V) ha_h).subgroupOf (orthDerived Q) =
        (specialBlock Q ((b : orthDerived Q) : V ≃ₗ[K] V) hb_h).subgroupOf (orthDerived Q) ⊔
          (specialBlock Q ((a : orthDerived Q) : V ≃ₗ[K] V) ha_h).subgroupOf (orthDerived Q) :=
      (Subgroup.comap_sup_eq_of_le_range (orthDerived Q).subtype
        (by rw [Subgroup.range_subtype]; exact hFb)
        (by rw [Subgroup.range_subtype]; exact hFa)).symm
    calc _ ≤ ((((specialBlock Q ((b : orthDerived Q) : V ≃ₗ[K] V) hb_h ⊔
            specialBlock Q ((a : orthDerived Q) : V ≃ₗ[K] V) ha_h).subgroupOf (orthDerived Q)).map
          (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))) :=
        Subgroup.map_mono (Subgroup.map_mono (Subgroup.comap_mono hle_sup))
      _ = (componentImage Q ((b : orthDerived Q) : V ≃ₗ[K] V) hb_h).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ⊔
          (componentImage Q ((a : orthDerived Q) : V ≃ₗ[K] V) ha_h).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) := by
        rw [hsup, Subgroup.map_sup, Subgroup.map_sup]
        rfl
      _ ≤ _ := by
        rw [sup_comm]
        exact sup_le_sup ha_layer hb_layer
  have hsplit : ∃ S : Submodule K V, S ≤ U₁ ⊔ U₂ ∧ finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0 := by
    let ι₀ : E →ₗ[K] E × E := LinearMap.prod LinearMap.id (LinearMap.mulLeft K c)
    have hι₀ : Function.Injective ι₀ := fun z z' h => congrArg Prod.fst h
    refine ⟨LinearMap.range ((pairMap φ₁ φ₂).comp ι₀), ?_, ?_, ?_⟩
    · rintro _ ⟨z, rfl⟩
      exact pairMap_mem φ₁ φ₂ _
    · rw [LinearMap.finrank_range_of_inj (f := (pairMap φ₁ φ₂).comp ι₀)
        (hN.pairMap_injective.comp hι₀), DE.finrank_eq_two]
    · rintro _ ⟨z, rfl⟩
      show Q (pairMap φ₁ φ₂ (z, c * z)) = 0
      rw [hN.Q_pairMap]
      simp only
      rw [DE.Nm_mul, hNc]
      ring
  have hu : Q (φ₁ 1 : V) = 1 := hN.Q_one₁
  have hv : Q (φ₂ 1 : V) = 1 := hN.Q_one₂
  have huv : polar Q (φ₁ 1 : V) (φ₂ 1 : V) = 0 := hN.polar_one
  have hgmem := hN.reflectPair_mem_supported hc0 hNc hK2 hK3
  have hgΩ : reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V) ∈ orthDerived Q := hleΩ hgmem
  have hu0 : (φ₁ 1 : V) ≠ 0 := fun h0 => by
    rw [h0, QuadraticMap.map_zero] at hu
    exact zero_ne_one hu
  have hli : ∀ a' b' : K, a' • (φ₁ 1 : V) + b' • (φ₂ 1 : V) = 0 → a' = 0 ∧ b' = 0 := by
    intro a' b' hab
    have hv0 : (φ₂ 1 : V) ≠ 0 := fun h0 => by
      rw [h0, QuadraticMap.map_zero] at hv
      exact zero_ne_one hv
    have h1 : a' • (φ₁ 1 : V) ∈ U₁ ⊓ U₂ := by
      refine ⟨U₁.smul_mem _ (φ₁ 1).2, ?_⟩
      have : a' • (φ₁ 1 : V) = -(b' • (φ₂ 1 : V)) := eq_neg_of_add_eq_zero_left hab
      rw [this]
      exact U₂.neg_mem (U₂.smul_mem _ (φ₂ 1).2)
    rw [hN.inf_eq_bot, Submodule.mem_bot] at h1
    have ha' : a' = 0 := (smul_eq_zero.mp h1).resolve_right hu0
    rw [ha', zero_smul, zero_add] at hab
    exact ⟨ha', (smul_eq_zero.mp hab).resolve_right hv0⟩
  have hxne : ∃ x, polar Q (φ₁ 1 : V) x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (hQ.1 _ fun w => by rw [polarBilin_apply_apply]; exact hcon w)
  have hg1 : reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V) ≠ 1 :=
    reflectPair_ne_one hu hv huv hli hxne
  have hg2 : (reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V)) ^ 2 = 1 := reflectPair_sq hu hv huv
  have hgord : orderOf (reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V)) = 2 :=
    orderOf_eq_prime hg2 hg1
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenterT : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with h | h
    · exact h
    · exfalso
      obtain ⟨c', d', hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d') c')
  have hinj : Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    conj_injective_of_center_eq_bot hcenterT
  have hρne : (QuotientGroup.mk (⟨reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V), hgΩ⟩ :
      orthDerived Q) : ProjOrthDerived Q) ≠ 1 := by
    intro h1
    have hZ : (⟨reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V), hgΩ⟩ : orthDerived Q) ∈
        (scalars K V).subgroupOf (orthDerived Q) := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨c', hc'⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp hZ)
    obtain ⟨w, hw, hw0⟩ := exists_ne_zero_orthPerp (hN.isCompl hc0 hNc) hN.finrank_sup
      (six_le_finrank hQ hT)
    have hfix : (reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V)) w = w :=
      reflectPair_fix hu hv huv (mem_orthPerp.mp hw _ (Submodule.mem_sup_left (φ₁ 1).2))
        (mem_orthPerp.mp hw _ (Submodule.mem_sup_right (φ₂ 1).2))
    have h2 : c' • w = w := by rw [← hc' w]; exact hfix
    have h3 : c' = 1 := by
      have : (c' - 1) • w = 0 := by rw [sub_smul, h2, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hw0)
    apply hg1
    refine LinearEquiv.ext fun v => ?_
    rw [hc' v, h3, one_smul]
    rfl
  have hρord : orderOf (QuotientGroup.mk (⟨reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V), hgΩ⟩ :
      orthDerived Q) : ProjOrthDerived Q) = 2 := by
    refine orderOf_eq_prime ?_ hρne
    rw [← QuotientGroup.mk_pow]
    have : (⟨reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V), hgΩ⟩ : orthDerived Q) ^ 2 = 1 :=
      Subtype.ext hg2
    rw [this, QuotientGroup.mk_one]
  refine ⟨⟨hN.isPerfect_supported hc0 hNc hK2 hK3, hleΩ⟩, hlayer,
    ⟨hN.finrank_sup, hN.nondegenerate_sup hc0 hNc, hsplit⟩,
    ⟨hN.iota₁ hc0 hNc, hN.iota₂ hc0 hNc, hN.iota₁_injective hc0 hNc, hN.iota₂_injective hc0 hNc,
      hN.iota_commute hc0 hNc, hrange,
      ⟨hb_h, hb_mem, hb_ne1, hb_self, hb_mult, hb_rng, hb_le, hb_bot, hb_comp⟩,
      ⟨ha_h, ha_mem, ha_ne1, ha_self, ha_mult, ha_rng, ha_le, ha_bot, ha_comp⟩⟩,
    hu, hv, huv, hgmem, hgord, fun h2 => reflectPair_eq_eichler h2 hu hv huv, hgΩ, hρord, ?_⟩
  rw [orderOf_injective _ hinj]
  exact hρord
theorem independent_orthogonal_norm_planes_split_four_local_layer_generation3
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hpne : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K) (hpq : p ∣
        Nat.card K + 1)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (Atil : Subgroup (orthDerived Q)) (hAtil : Assembly.IsElemAbelian p Atil)
    (hAcard : Nat.card Atil = p ^ 2) {E : Type*} [Field E] [Algebra K E]
    (hE : finrank K E = 2) {ζ : E} (hζ : orderOf ζ = p) (U₁ U₂ : Submodule K V)
    (hU₁ : finrank K U₁ = 2) (hU₂ : finrank K U₂ = 2)
    (hU₁reg : (polarBilin (Q.comp U₁.subtype)).Nondegenerate)
    (hU₂reg : (polarBilin (Q.comp U₂.subtype)).Nondegenerate)
    (hU₁₂ : ∀ x ∈ U₁, ∀ y ∈ U₂, polar Q x y = 0)
    (hU₁inv : ∀ y ∈ Atil, ∀ x ∈ U₁, ((y : orthDerived Q) : V ≃ₗ[K] V) x ∈ U₁)
    (hU₂inv : ∀ y ∈ Atil, ∀ x ∈ U₂, ((y : orthDerived Q) : V ≃ₗ[K] V) x ∈ U₂)
    (φ₁ : E →ₗ[K] U₁) (φ₂ : E →ₗ[K] U₂)
    (hφ₁ : ∀ z, algebraMap K E (Q (φ₁ z : V)) = z * z ^ Nat.card K)
    (hφ₂ : ∀ z, algebraMap K E (Q (φ₂ z : V)) = z * z ^ Nat.card K)
    (χ₁ χ₂ : Atil →* Multiplicative (ZMod p))
    (hχ : ∀ m n : ZMod p, (∀ y : Atil, m * (χ₁ y).toAdd + n * (χ₂ y).toAdd = 0) → m = 0 ∧ n = 0)
    (hy₁ : ∀ (y : Atil) (z : E), ((y : orthDerived Q) : V ≃ₗ[K] V) (φ₁ z : V) =
      (φ₁ (ζ ^ (χ₁ y).toAdd.val * z) : V))
    (hy₂ : ∀ (y : Atil) (z : E), ((y : orthDerived Q) : V ≃ₗ[K] V) (φ₂ z : V) =
      (φ₂ (ζ ^ (χ₂ y).toAdd.val * z) : V))
    (a : Atil) (ha1 : a ≠ 1) (ha : χ₁ a = χ₂ a)
    (b : Atil) (hb1 : b ≠ 1) (hb : χ₁ b * χ₂ b = 1) :
    (Group.IsPerfect ↥(supportedOrthDerived Q (U₁ ⊔ U₂)) ∧
      supportedOrthDerived Q (U₁ ⊔ U₂) ≤ orthDerived Q) ∧
    (((supportedOrthDerived Q (U₁ ⊔ U₂)).subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).map
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤
      inSubgroup layer (D ⊓ Subgroup.centralizer
        ({MulAut.conj (QuotientGroup.mk (a : orthDerived Q) : ProjOrthDerived Q)} :
          Set (MulAut (ProjOrthDerived Q)))) ⊔
      inSubgroup layer (D ⊓ Subgroup.centralizer
        ({MulAut.conj (QuotientGroup.mk (b : orthDerived Q) : ProjOrthDerived Q)} :
          Set (MulAut (ProjOrthDerived Q)))) ∧
    (finrank K ↥(U₁ ⊔ U₂) = 4 ∧ (polarBilin (Q.comp (U₁ ⊔ U₂).subtype)).Nondegenerate ∧
      ∃ S : Submodule K V, S ≤ U₁ ⊔ U₂ ∧ finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) ∧
    (∃ ι₁ ι₂ : Matrix.SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V),
      Function.Injective ι₁ ∧ Function.Injective ι₂ ∧
      (∀ g h, ι₁ g * ι₂ h = ι₂ h * ι₁ g) ∧
      ι₁.range ⊔ ι₂.range = supportedOrthDerived Q (U₁ ⊔ U₂) ∧
      (∃ h ∈ primaryFactors (((b : orthDerived Q) : V ≃ₗ[K] V)).toLinearMap, h ≠ X - 1 ∧
        2 ≤ primaryMultiplicity (((b : orthDerived Q) : V ≃ₗ[K] V)).toLinearMap h ∧
        ι₁.range ≤ specialBlock Q ((b : orthDerived Q) : V ≃ₗ[K] V) h ∧
        specialBlock Q ((b : orthDerived Q) : V ≃ₗ[K] V) h ≤ orthDerived Q ⊓
          Subgroup.centralizer ({((b : orthDerived Q) : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) ∧
        specialBlock Q ((b : orthDerived Q) : V ≃ₗ[K] V) h ≠ ⊥ ∧
        IsComponent (((componentImage Q ((b : orthDerived Q) : V ≃ₗ[K] V) h).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
          (D ⊓ Subgroup.centralizer
            ({MulAut.conj (QuotientGroup.mk (b : orthDerived Q) : ProjOrthDerived Q)} :
              Set (MulAut (ProjOrthDerived Q)))))) ∧
      (∃ h ∈ primaryFactors (((a : orthDerived Q) : V ≃ₗ[K] V)).toLinearMap, h ≠ X - 1 ∧
        2 ≤ primaryMultiplicity (((a : orthDerived Q) : V ≃ₗ[K] V)).toLinearMap h ∧
        ι₂.range ≤ specialBlock Q ((a : orthDerived Q) : V ≃ₗ[K] V) h ∧
        specialBlock Q ((a : orthDerived Q) : V ≃ₗ[K] V) h ≤ orthDerived Q ⊓
          Subgroup.centralizer ({((a : orthDerived Q) : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) ∧
        specialBlock Q ((a : orthDerived Q) : V ≃ₗ[K] V) h ≠ ⊥ ∧
        IsComponent (((componentImage Q ((a : orthDerived Q) : V ≃ₗ[K] V) h).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
          (D ⊓ Subgroup.centralizer
            ({MulAut.conj (QuotientGroup.mk (a : orthDerived Q) : ProjOrthDerived Q)} :
              Set (MulAut (ProjOrthDerived Q))))))) ∧
    (Q (φ₁ 1 : V) = 1 ∧ Q (φ₂ 1 : V) = 1 ∧ polar Q (φ₁ 1 : V) (φ₂ 1 : V) = 0 ∧
      reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V) ∈ supportedOrthDerived Q (U₁ ⊔ U₂) ∧
      orderOf (reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V)) = 2 ∧
      ((2 : K) = 0 → reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V) =
        eichler Q ((φ₁ 1 : V) + (φ₂ 1 : V)) (φ₁ 1 : V)) ∧
      ∃ hg : reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V) ∈ orthDerived Q,
        orderOf (QuotientGroup.mk (⟨reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V), hg⟩ :
          orthDerived Q) : ProjOrthDerived Q) = 2 ∧
        orderOf (MulAut.conj (QuotientGroup.mk (⟨reflect Q (φ₁ 1 : V) * reflect Q (φ₂ 1 : V), hg⟩ :
          orthDerived Q) : ProjOrthDerived Q)) = 2) := by
  obtain ⟨h₁, h₂, h₃, ⟨ι₁, ι₂, hι₁, hι₂, hιc, hιr, ⟨hbh, hbm, hbn, -, hbu, hbg, hbl, hbo, hbc⟩,
      ⟨hah, ham, han, -, hau, hag, hal, hao, hac⟩⟩, h₅⟩ :=
    independent_orthogonal_norm_planes_split_four_local_layer_generation_full3 hQ hT hp hpne hK4 hpl
        hpq
      D hD Atil hAtil hAcard hE hζ U₁ U₂ hU₁ hU₂ hU₁reg hU₂reg hU₁₂ hU₁inv hU₂inv φ₁ φ₂ hφ₁ hφ₂
      χ₁ χ₂ hχ hy₁ hy₂ a ha1 ha b hb1 hb
  exact ⟨h₁, h₂, h₃, ⟨ι₁, ι₂, hι₁, hι₂, hιc, hιr, ⟨hbh, hbm, hbn, hbu, hbg, hbl, hbo, hbc⟩,
    ⟨hah, ham, han, hau, hag, hal, hao, hac⟩⟩, h₅⟩
end CFSG.RankThree.PartOne