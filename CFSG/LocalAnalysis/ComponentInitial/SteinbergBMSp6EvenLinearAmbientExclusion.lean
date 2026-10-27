module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSp6EvenLinearLayerSelector
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSp6EvenLinearAmbientCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSp6EvenLinearAmbientTools
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSp6EvenLinearFieldFour
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSp6EvenLinearModule
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSp6EvenLinearLifts
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearFlag GL3TwoFixedModel FieldFourCover
open _root_.CFSG.LocalAnalysis.ComponentInitial.SteinbergBM
open LinearMap (BilinForm)

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e) (z : G)

theorem SteinbergBM.glTrans_sq :
    glTransTwoOne ^ 2 = 1 ∧ glTransThreeOne ^ 2 = 1 ∧ glTransThreeTwo ^ 2 = 1 := by
  refine ⟨Units.ext ?_, Units.ext ?_, Units.ext ?_⟩ <;>
    · rw [Units.val_pow_eq_pow_val]
      decide

theorem SteinbergBM.mult_zmod_two_cases :
    ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  decide

include φ he in
theorem SteinbergBM.card_L : Nat.card L = 1451520 := by
  rw [Nat.card_congr φ.toEquiv, Nat.card_congr (BinarySymplecticSix.spCoord he).toEquiv,
    (symplectic_higher_order_and_Sylow (K := ZMod 2) 2 2 (Nat.card_zmod 2) (r := 3)
      (by norm_num)).1]
  decide

theorem sp6_even_linear_ambient_core [Finite G] (hGs : IsSimpleGroup G)
    (hGnab : ∃ x y : G, x * y ≠ y * x) (hzL : z ∈ centralizer (L : Set G))
    (hLz : L ⊔ zpowers z = centralizer ({z} : Set G)) (hz : orderOf z = 2)
    (hC₂el : ∀ c ∈ sp6C₂ φ he z, c ^ 2 = 1)
    (hC₂ab : ∀ c ∈ sp6C₂ φ he z, ∀ d ∈ sp6C₂ φ he z, c * d = d * c)
    (hC₂card : Nat.card (sp6C₂ φ he z) = 2 ^ 12) (hA₂card : Nat.card (sp6A₂ φ e) = 2 ^ 6)
    (hA₂C₂ : sp6A₂ φ e ≤ sp6C₂ φ he z)
    (hfixz : ∀ c ∈ sp6C₂ φ he z, c * z = z * c ↔ c ∈ sp6A₂ φ e)
    (hcommz : ∀ c ∈ sp6C₂ φ he z, z⁻¹ * c⁻¹ * z * c ∈ sp6A₂ φ e)
    {V₁ : Subgroup G} (hconc : Sp6LagrangianLayerConclusion φ he z V₁)
    (hsimple : Sp6LayerSimple φ he z) {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) {k : Type}
    [Field k] (hk : Nat.card k = 2 ^ f) (η : sp6Dstar φ he z ≃* projectiveSL n k) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmz2 := SteinbergBM.mult_zmod_two_cases
  obtain ⟨-, hsec⟩ := sp6_even_linear_psl_sector φ he z hconc hsimple
  obtain ⟨hn3, hf2, -, -, -, -, haD, hn3', hchar, σ, -, hσ, -, -, χ, -, -, hint, hlab, -, -⟩ :=
    hsec n f hn hf k hk η
  subst hn3
  have hk4 : Nat.card k = 4 := by rw [hk, hf2]; norm_num
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk4]; norm_num)
  obtain ⟨-, -, ⟨hzX, hadef⟩, ⟨hLX, hLevi⟩, ⟨ι, hιdef, hιinj, hιrange⟩, -, -, -, -, hRoinv, -,
    -, -, -, ha2, hJLCa, -, hCa, hāo, hJCā, -, hCā, -, -, -, -, -, -, -, -, -, -, -, hCD, -, -,
    -, -, hQn, -, hQmap, hQcomap, hQcen, -⟩ := hconc
  set C₂ := sp6C₂ φ he z with hC₂def
  set A₂ := sp6A₂ φ e with hA₂def
  set θ := sp6θ φ he z with hθdef
  set Q := sp6Qstar φ he z with hQdef
  set Ro := sp6Ro φ he z with hRodef
  set a := sp6a φ he z with hadef'
  set ā := sp6aBar φ he z with hādef
  set JL := sp6JL φ he z with hJLdef
  have hθsurj : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hθker : θ.ker = Ro := QuotientGroup.ker_mk' _
  have hπsurj : Function.Surjective (sp6πX φ he z) := QuotientGroup.mk'_surjective _
  have hπker : (sp6πX φ he z).ker = C₂.subgroupOf (sp6X φ he z) := QuotientGroup.ker_mk' _
  have hRodd : Nat.Coprime 2 (Nat.card θ.ker) := by
    rw [hθker]
    exact CFSG.pPrimeCore_coprime_card
  have hZ : ∀ c ∈ Q, θ c = 1 → ∀ q ∈ Q, q * c = c * q := by
    intro c hc hθc q hq
    have hcR : c ∈ Ro := by
      rw [← hθker]
      exact hθc
    have hcZ : c ∈ (center Q).map Q.subtype := by
      rw [hQcen]
      exact mem_inf.2 ⟨hc, hcR⟩
    obtain ⟨c', hc', rfl⟩ := hcZ
    exact congrArg Subtype.val (mem_center_iff.1 hc' ⟨q, hq⟩)
  have hDn : (sp6Dstar φ he z).Normal := Subgroup.normalClosure_normal
  have : Q.Normal := hQn
  have hQcomap' : (sp6Dstar φ he z).comap θ = θ.ker ⊔ Q := by rw [hθker]; exact hQcomap
  have hā2 : ā * ā = 1 := by
    have h := pow_orderOf_eq_one ā
    rwa [hāo, pow_two] at h
  have hāinv : ā⁻¹ = ā := inv_eq_of_mul_eq_one_right hā2
  have hθa : θ a = ā := rfl
  have ha2' : a ^ 2 = 1 := by rw [← ha2]; exact pow_orderOf_eq_one a
  have hJD : sp6JLBar φ he z ≤ sp6Dstar φ he z := le_normalClosure
  have hJLQ : JL ≤ Q := le_normalClosure
  have hRinv : ∀ r ∈ θ.ker, a⁻¹ * r * a = r⁻¹ := fun r hr => hRoinv r (by rw [← hθker]; exact hr)
  have hιX : ∀ g, ι g = sp6πX φ he z ⟨leviHom φ he g, hLX g⟩ := fun g => (hιdef g).trans (hLevi g)
  have hιJL : ∀ g, ι g ∈ JL := fun g => by
    rw [← hιrange]
    exact ⟨g, rfl⟩
  have hιD : ∀ g, θ (ι g) ∈ sp6Dstar φ he z := fun g => hJD ⟨ι g, hιJL g, rfl⟩
  have hlabι : ∀ g, χ ⟨θ (ι g), hιD g⟩ = binaryEmbed k rfl g := by
    intro g
    have hmem : θ (sp6Levi φ he z g) ∈ sp6Dstar φ he z := by
      rw [← hιdef]
      exact hιD g
    have e1 : (⟨θ (ι g), hιD g⟩ : sp6Dstar φ he z) = ⟨θ (sp6Levi φ he z g), hmem⟩ :=
      Subtype.ext (congrArg θ (hιdef g))
    rw [e1, hlab g hmem]
  obtain ⟨hsq1, hsq2, hsq3⟩ := SteinbergBM.glTrans_sq
  have htQ : ι glTransThreeOne ∈ Q := hJLQ (hιJL _)
  have ht2 : ι glTransThreeOne ^ 2 = 1 := by rw [← map_pow, hsq2, map_one]
  have hχt : χ ⟨θ (ι glTransThreeOne), hιD _⟩ = proj 3 k (unipU k 0 0 1) := by
    rw [hlabι, binaryEmbed_glTransThreeOne]
  have hχint : ∀ d : sp6Dstar φ he z, χ (MulAut.conjNormal ā d) = fieldAut 3 k σ (χ d) := by
    intro d
    have hda : ā⁻¹ * (d : Sp6Y φ he z) * ā ∈ sp6Dstar φ he z := by
      have := hDn.conj_mem _ d.2 ā⁻¹
      rwa [inv_inv] at this
    have h1 := hint d d.2 hda
    have h2 : MulAut.conjNormal ā d = ⟨_, hda⟩ := Subtype.ext (by
      rw [MulAut.conjNormal_apply]
      change ā * (d : Sp6Y φ he z) * ā⁻¹ = ā⁻¹ * d * ā
      rw [hāinv])
    rw [h2, h1]
  have hCa' : centralizer {ā} ≤ zpowers ā ⊔ sp6Dstar φ he z := by
    rw [← hCā]
    exact sup_le_sup_left hJD _
  obtain ⟨ηY, -, -, hηker, hηconj, -⟩ :=
    SteinbergBM.even_linear_layer_extension_core hk4 hσ χ hχint hCD hCa'
  have hθ1' : ∀ x : Sp6F φ he z, x ^ 2 = 1 → θ x = 1 → x = 1 := fun x hx h =>
    eq_one_of_mem_ker_of_pow hRodd h (m := 1) (by rw [pow_one]; exact hx)
  have hinner : ∀ x : Sp6F φ he z, x ^ 2 = 1 → θ x ∈ sp6Dstar φ he z → θ x ≠ 1 →
      ∃ q ∈ Q, q * x * q⁻¹ = ι glTransThreeOne := by
    intro x hx2 hxD hx1
    have hord : orderOf (χ ⟨θ x, hxD⟩) = 2 := by
      apply orderOf_eq_prime
      · rw [← map_pow]
        have : (⟨θ x, hxD⟩ : sp6Dstar φ he z) ^ 2 = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow, ← map_pow, hx2, map_one]
          rfl)
        rw [this, map_one]
      · intro h
        apply hx1
        have h' := χ.injective (h.trans (map_one χ).symm)
        exact congrArg Subtype.val h'
    obtain ⟨p, hp⟩ := exists_conj_eq_projW hk4 hord
    have hd : χ.symm p * ⟨θ x, hxD⟩ * (χ.symm p)⁻¹ = ⟨θ (ι glTransThreeOne), hιD _⟩ :=
      χ.injective (by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hp, hχt])
    exact exists_conj_eq_of_conj_map hRodd hZ hQmap hQcomap' hx2 htQ ht2 hxD (χ.symm p).2
      (congrArg Subtype.val hd)
  have houter : ∀ x : Sp6F φ he z, x ^ 2 = 1 → θ x ∉ sp6Dstar φ he z →
      ∃ w, w * x * w⁻¹ = a := by
    intro x hx2 hxD
    have hθx2 : θ x ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
    rcases hmz2 (ηY (θ x)) with h | h
    · exact absurd (hηker _ hθx2 h) hxD
    · obtain ⟨y, hy⟩ := hηconj _ hθx2 h
      exact exists_conj_eq_of_inverts hRodd hθsurj hRinv hy
  have hzC : ∀ c ∈ C₂, z⁻¹ * c * z ∈ C₂ := fun c hc => (mem_set_normalizer_iff''.1 hzX c).1 hc
  have hMz : ∀ S : Set (GL (Fin 3) (ZMod 2)), ∀ m ∈ leviHom φ he '' S, m * z = z * m := by
    rintro S _ ⟨g, -, rfl⟩
    exact RadicalLabels.leviHom_mul_z φ he hzL g
  have hlev : ∀ (S : Set (GL (Fin 3) (ZMod 2))) (m : ℕ),
      Nat.card {B : ↥(binarySymMatrices 3) // ∀ g ∈ S, symThreeCongr g B = B} ≤ 2 ^ m →
      Nat.card ↥(C₂ ⊓ centralizer (leviHom φ he '' S)) ≤ 2 ^ (2 * m) := by
    intro S m hS
    have h1 := card_inf_centralizer_le_sq hC₂ab hzC hfixz hcommz (hMz S)
    have h2 := card_tauHom_fixed_le φ he hS
    calc _ ≤ _ := h1
      _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h2 2
      _ = 2 ^ (2 * m) := by rw [← pow_mul, mul_comm]
  have hlev0 : Nat.card ↥(C₂ ⊓ centralizer ({leviHom φ he glTransThreeOne} : Set G)) ≤ 2 ^ 8 := by
    have h := hlev {glTransThreeOne} 4 (by
      have e : {B : ↥(binarySymMatrices 3) //
          ∀ g ∈ ({glTransThreeOne} : Set (GL (Fin 3) (ZMod 2))), symThreeCongr g B = B} ≃
          {B : ↥(binarySymMatrices 3) // symThreeCongr glTransThreeOne B = B} :=
        Equiv.subtypeEquivRight fun B => by simp
      rw [Nat.card_congr e]
      exact card_fix_glTransThreeOne_le)
    rwa [Set.image_singleton] at h
  have hlevW : ∀ i : Fin 2, ∃ s : GL (Fin 3) (ZMod 2), s ^ 2 = 1 ∧
      binaryEmbed k rfl s ∈ projRad k i ∧
      Nat.card ↥(C₂ ⊓ centralizer (leviHom φ he '' {s, glTransThreeOne})) ≤ 2 ^ 6 := by
    intro i
    fin_cases i
    · refine ⟨glTransTwoOne, hsq1, ?_, hlev _ 3 ?_⟩
      · rw [binaryEmbed_glTransTwoOne]
        exact mem_projRad_zero.2 ⟨1, 0, rfl⟩
      · have e : {B : ↥(binarySymMatrices 3) // ∀ g ∈ ({glTransTwoOne, glTransThreeOne} :
            Set (GL (Fin 3) (ZMod 2))), symThreeCongr g B = B} ≃
            {B : ↥(binarySymMatrices 3) // symThreeCongr glTransTwoOne B = B ∧
              symThreeCongr glTransThreeOne B = B} :=
          Equiv.subtypeEquivRight fun B => by simp
        rw [Nat.card_congr e]
        exact card_fix_glTransTwoOne_le
    · refine ⟨glTransThreeTwo, hsq3, ?_, hlev _ 3 ?_⟩
      · rw [binaryEmbed_glTransThreeTwo]
        exact mem_projRad_one.2 ⟨1, 0, rfl⟩
      · have e : {B : ↥(binarySymMatrices 3) // ∀ g ∈ ({glTransThreeTwo, glTransThreeOne} :
            Set (GL (Fin 3) (ZMod 2))), symThreeCongr g B = B} ≃
            {B : ↥(binarySymMatrices 3) // symThreeCongr glTransThreeTwo B = B ∧
              symThreeCongr glTransThreeOne B = B} :=
          Equiv.subtypeEquivRight fun B => by simp
        rw [Nat.card_congr e]
        exact card_fix_glTransThreeTwo_le
  have hzA : C₂ ⊓ centralizer ({z} : Set G) = A₂ := by
    ext c
    rw [mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun ⟨hc, h⟩ => (hfixz c hc).1 h, fun h => ⟨hA₂C₂ h, (hfixz c (hA₂C₂ h)).2 h⟩⟩
  have hEout : ∀ x : sp6X φ he z, sp6πX φ he z x ^ 2 = 1 →
      θ (sp6πX φ he z x) ∉ sp6Dstar φ he z →
      Nat.card ↥(C₂ ⊓ centralizer ({(x : G)} : Set G)) ≤ 2 ^ 6 := by
    intro x hx2 hD
    obtain ⟨w, hw⟩ := houter _ hx2 hD
    obtain ⟨xw, rfl⟩ := hπsurj w
    have hker : (⟨z, hzX⟩ : sp6X φ he z)⁻¹ * (xw * x * xw⁻¹) ∈ (sp6πX φ he z).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hadef, map_mul, map_mul, map_inv, hw,
        inv_mul_cancel]
    rw [hπker, mem_subgroupOf] at hker
    have hc : z⁻¹ * ((xw : G) * x * (xw : G)⁻¹) ∈ C₂ := hker
    calc Nat.card ↥(C₂ ⊓ centralizer ({(x : G)} : Set G))
        = Nat.card ↥(C₂ ⊓ centralizer ((fun m => (xw : G) * m * (xw : G)⁻¹) '' {(x : G)})) :=
          (card_inf_centralizer_conj xw.2 _).symm
      _ = Nat.card ↥(C₂ ⊓ centralizer ({z * (z⁻¹ * ((xw : G) * x * (xw : G)⁻¹))} : Set G)) := by
          rw [Set.image_singleton, mul_inv_cancel_left]
      _ = Nat.card ↥(C₂ ⊓ centralizer ({z} : Set G)) := by
          rw [inf_centralizer_mul hC₂ab hc]
      _ = 2 ^ 6 := by rw [hzA, hA₂card]
      _ ≤ 2 ^ 6 := le_rfl
  have hE8 : ∀ x : sp6X φ he z, sp6πX φ he z x ≠ 1 → sp6πX φ he z x ^ 2 = 1 →
      Nat.card ↥(C₂ ⊓ centralizer ({(x : G)} : Set G)) ≤ 2 ^ 8 := by
    intro x hx1 hx2
    by_cases hD : θ (sp6πX φ he z x) ∈ sp6Dstar φ he z
    · have hθx1 : θ (sp6πX φ he z x) ≠ 1 := fun h => hx1 (hθ1' _ hx2 h)
      obtain ⟨q, -, hq⟩ := hinner _ hx2 hD hθx1
      obtain ⟨xq, rfl⟩ := hπsurj q
      have hker : (⟨leviHom φ he glTransThreeOne, hLX _⟩ : sp6X φ he z)⁻¹ * (xq * x * xq⁻¹) ∈
          (sp6πX φ he z).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ← hιX, map_mul, map_mul, map_inv, hq,
          inv_mul_cancel]
      rw [hπker, mem_subgroupOf] at hker
      have hc : (leviHom φ he glTransThreeOne)⁻¹ * ((xq : G) * x * (xq : G)⁻¹) ∈ C₂ := hker
      calc Nat.card ↥(C₂ ⊓ centralizer ({(x : G)} : Set G))
          = Nat.card ↥(C₂ ⊓ centralizer ((fun m => (xq : G) * m * (xq : G)⁻¹) '' {(x : G)})) :=
            (card_inf_centralizer_conj xq.2 _).symm
        _ = Nat.card ↥(C₂ ⊓ centralizer ({leviHom φ he glTransThreeOne *
              ((leviHom φ he glTransThreeOne)⁻¹ * ((xq : G) * x * (xq : G)⁻¹))} : Set G)) := by
            rw [Set.image_singleton, mul_inv_cancel_left]
        _ = Nat.card ↥(C₂ ⊓ centralizer ({leviHom φ he glTransThreeOne} : Set G)) := by
            rw [inf_centralizer_mul hC₂ab hc]
        _ ≤ 2 ^ 8 := hlev0
    · exact (hEout x hx2 hD).trans (by norm_num)
  have hJLcard : Nat.card JL = 168 := by
    rw [← hιrange, ← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv,
      GL3TwoFixedModel.card_GL_three_two]
  have huniq : ∀ U : Subgroup G, U ≤ normalizer (C₂ : Set G) → (∀ u ∈ U, u ^ 2 = 1) →
      (∀ u ∈ U, ∀ v ∈ U, u * v = v * u) → Nat.card U = Nat.card C₂ → U = C₂ := by
    intro U hUX' hU2 hUab hUcard
    have hUX : U ≤ sp6X φ he z := hUX'
    by_contra hne
    have hUC : ¬ U ≤ C₂ := fun h => hne (Subgroup.eq_of_le_of_card_ge h (by rw [hUcard]))
    obtain ⟨x₀, hx₀U, hx₀C⟩ := Set.not_subset.1 hUC
    set ρ := (sp6πX φ he z).comp (U.subgroupOf (sp6X φ he z)).subtype with hρ
    have hρker : ∀ u : U.subgroupOf (sp6X φ he z),
        u ∈ ρ.ker ↔ ((u : sp6X φ he z) : G) ∈ C₂ := by
      intro u
      rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπker,
        mem_subgroupOf]
      rfl
    have hUcard' : Nat.card (U.subgroupOf (sp6X φ he z)) = 2 ^ 12 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hUX).toEquiv, hUcard, hC₂card]
    have hcard := Subgroup.card_ker_mul_card_range ρ
    rw [hUcard'] at hcard
    have hkerle : ∀ M : Set G, (∀ c ∈ C₂, (∀ u ∈ U, u * c = c * u) → c ∈ centralizer M) →
        Nat.card ρ.ker ≤ Nat.card ↥(C₂ ⊓ centralizer M) := by
      intro M hM
      refine Nat.card_le_card_of_injective
        (fun u => ⟨(((u : U.subgroupOf (sp6X φ he z)) : sp6X φ he z) : G), ?_⟩) ?_
      · have hu := (hρker _).1 u.2
        exact mem_inf.2 ⟨hu, hM _ hu fun v hv =>
          hUab v hv _ (mem_subgroupOf.1 (u : U.subgroupOf (sp6X φ he z)).2)⟩
      · intro u v h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext (Subtype.ext h'))
    have hB2 : ∀ y ∈ ρ.range, y ^ 2 = 1 := by
      rintro _ ⟨u, rfl⟩
      have hu : u ^ 2 = 1 := Subtype.ext (Subtype.ext (hU2 _ (mem_subgroupOf.1 u.2)))
      rw [← map_pow, hu, map_one]
    have hρ1 : ∀ u : U.subgroupOf (sp6X φ he z), ((u : sp6X φ he z) : G) ∉ C₂ → ρ u ≠ 1 :=
      fun u hu h => hu ((hρker u).1 h)
    have hx₀X := hUX hx₀U
    have hk8 : Nat.card ρ.ker ≤ 2 ^ 8 := by
      refine (hkerle {x₀} fun c _ h => mem_centralizer_singleton_iff.2 (h x₀ hx₀U).symm).trans ?_
      exact hE8 ⟨x₀, hx₀X⟩ (hρ1 ⟨⟨x₀, hx₀X⟩, hx₀U⟩ hx₀C) (hB2 _ ⟨⟨⟨x₀, hx₀X⟩, hx₀U⟩, rfl⟩)
    have hBdvd : Nat.card ρ.range ∣ 2 ^ 12 := Dvd.intro_left _ hcard
    obtain ⟨j, -, hBj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hBdvd
    by_cases hj3 : j ≤ 3
    · have h1 : 2 ^ 12 ≤ 2 ^ 8 * 2 ^ 3 := by
        rw [← hcard, hBj]
        exact Nat.mul_le_mul hk8 (Nat.pow_le_pow_right (by norm_num) hj3)
      norm_num at h1
    push Not at hj3
    by_cases hout : ∃ u : U.subgroupOf (sp6X φ he z), θ (ρ u) ∉ sp6Dstar φ he z
    ·
      obtain ⟨u, hu⟩ := hout
      have hu2 : ρ u ^ 2 = 1 := hB2 _ ⟨u, rfl⟩
      obtain ⟨w, hw⟩ := houter _ hu2 hu
      have hBC : ρ.range ≤ centralizer ({ρ u} : Set (Sp6F φ he z)) := by
        rintro _ ⟨v, rfl⟩
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subtype.ext
          (hUab _ (mem_subgroupOf.1 v.2) _ (mem_subgroupOf.1 u.2)))
      have hCF : Nat.card (centralizer ({ρ u} : Set (Sp6F φ he z))) ∣ 336 := by
        rw [← card_centralizer_conj w, hw, ← hCa]
        have h1 := card_sup_dvd_of_commute (H := zpowers a) (K := JL) (by
          intro h hh k hk
          obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hh
          exact (Commute.zpow_left (mem_centralizer_singleton_iff.1 (hJLCa hk)).symm m).eq)
        rwa [Nat.card_zpowers, ha2, hJLcard] at h1
      have hBd : Nat.card ρ.range ∣ 336 := (Subgroup.card_dvd_of_le hBC).trans hCF
      rw [hBj] at hBd
      have hj4 : j ≤ 4 := by
        by_contra h
        push Not at h
        have h5 : 2 ^ 5 ∣ 336 := (pow_dvd_pow 2 h).trans hBd
        norm_num at h5
      have hk6 : Nat.card ρ.ker ≤ 2 ^ 6 := by
        refine (hkerle {((u : sp6X φ he z) : G)} fun c _ h =>
          mem_centralizer_singleton_iff.2 (h _ (mem_subgroupOf.1 u.2)).symm).trans ?_
        exact hEout _ hu2 hu
      have h1 : 2 ^ 12 ≤ 2 ^ 6 * 2 ^ 4 := by
        rw [← hcard, hBj]
        exact Nat.mul_le_mul hk6 (Nat.pow_le_pow_right (by norm_num) hj4)
      norm_num at h1
    ·
      push Not at hout
      have hBQ : ∀ y ∈ ρ.range, y ∈ Q := by
        rintro _ ⟨u, rfl⟩
        exact mem_of_pow_two_pow_eq_one hRodd hQcomap' (hout u) (m := 1)
          (by rw [pow_one]; exact hB2 _ ⟨u, rfl⟩)
      set Eθ := ρ.range.map θ with hEθ
      have hEθD : Eθ ≤ sp6Dstar φ he z := by
        rintro _ ⟨y, hy, rfl⟩
        rw [← hQmap]
        exact mem_map_of_mem θ (hBQ y hy)
      set E := (Eθ.subgroupOf (sp6Dstar φ he z)).map χ.toMonoidHom with hE
      have hEcard : Nat.card E = Nat.card ρ.range := by
        rw [hE, Subgroup.card_map_of_injective χ.injective,
          Nat.card_congr (subgroupOfEquivOfLe hEθD).toEquiv]
        have hinj : Function.Injective (θ.comp ρ.range.subtype) := by
          rw [injective_iff_map_eq_one]
          intro y hy
          exact Subtype.ext (hθ1' y (hB2 y y.2) hy)
        have hr : (θ.comp ρ.range.subtype).range = Eθ := by
          rw [hEθ, MonoidHom.range_comp, range_subtype]
        rw [← hr]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      have hE2 : ∀ y ∈ E, y ^ 2 = 1 := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨b, hb, hby⟩ := mem_subgroupOf.1 hy
        have hy2 : y ^ 2 = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow, ← hby, ← map_pow, hB2 b hb, map_one]
          rfl)
        rw [← map_pow, hy2, map_one]
      obtain ⟨hE16, p, i, hpi⟩ := exists_conj_projRad_le hk4 hE2 (by
        rw [hEcard, hBj]
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj3)
      obtain ⟨q, hqQ, hqd⟩ : ((χ.symm p : sp6Dstar φ he z) : Sp6Y φ he z) ∈ Q.map θ := by
        rw [hQmap]
        exact (χ.symm p).2
      obtain ⟨s, hs2, hsR, hsC⟩ := hlevW i
      have hgen : ∀ g : GL (Fin 3) (ZMod 2), g ^ 2 = 1 → binaryEmbed k rfl g ∈ projRad k i →
          ∃ ug : U.subgroupOf (sp6X φ he z), ρ ug = q * ι g * q⁻¹ := by
        intro g hg2 hgR
        obtain ⟨y, hy, hyeq⟩ := hpi _ hgR
        obtain ⟨b, ⟨ug, rfl⟩, hby⟩ := mem_subgroupOf.1 hy
        refine ⟨ug, eq_of_sq_eq_one_of_map_eq hRodd hZ (hBQ _ ⟨ug, rfl⟩)
          (‹Q.Normal›.conj_mem _ (hJLQ (hιJL g)) _) (hB2 _ ⟨ug, rfl⟩)
          (conj_sq_eq_one (by rw [← map_pow, hg2, map_one]) q) ?_⟩
        have h1 : y = χ.symm p * ⟨θ (ι g), hιD g⟩ * (χ.symm p)⁻¹ := χ.injective (by
          rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hlabι]
          exact hyeq)
        rw [map_mul, map_mul, map_inv, hqd, hby, h1]
        rfl
      obtain ⟨us, hus⟩ := hgen s hs2 hsR
      obtain ⟨ut, hut⟩ := hgen glTransThreeOne hsq2
        (projCenterW_le_projRad i (by
          rw [binaryEmbed_glTransThreeOne]
          exact mem_projCenterW.2 ⟨1, rfl⟩))
      obtain ⟨xq, rfl⟩ := hπsurj q
      have hlift : ∀ (g : GL (Fin 3) (ZMod 2)) (ug : U.subgroupOf (sp6X φ he z)),
          ρ ug = sp6πX φ he z xq * ι g * (sp6πX φ he z xq)⁻¹ →
          ((xq : G) * leviHom φ he g * (xq : G)⁻¹)⁻¹ * ((ug : sp6X φ he z) : G) ∈ C₂ := by
        intro g ug hug
        have hker : (xq * ⟨leviHom φ he g, hLX g⟩ * xq⁻¹)⁻¹ * (ug : sp6X φ he z) ∈
            (sp6πX φ he z).ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, ← hιX]
          change _ * ρ ug = 1
          rw [hug, inv_mul_cancel]
        rw [hπker, mem_subgroupOf] at hker
        exact hker
      have hk6 : Nat.card ρ.ker ≤ 2 ^ 6 := by
        refine (hkerle ((fun m => (xq : G) * m * (xq : G)⁻¹) ''
          (leviHom φ he '' {s, glTransThreeOne})) ?_).trans ?_
        · intro c hc hcU
          rw [mem_centralizer_iff]
          have key : ∀ (g : GL (Fin 3) (ZMod 2)) (ug : U.subgroupOf (sp6X φ he z)),
              ρ ug = sp6πX φ he z xq * ι g * (sp6πX φ he z xq)⁻¹ →
              (xq : G) * leviHom φ he g * (xq : G)⁻¹ * c =
                c * ((xq : G) * leviHom φ he g * (xq : G)⁻¹) := by
            intro g ug hug
            have h1 := hlift g ug hug
            set m := (xq : G) * leviHom φ he g * (xq : G)⁻¹ with hm
            have hmu : m = ((ug : sp6X φ he z) : G) * (m⁻¹ * ((ug : sp6X φ he z) : G))⁻¹ := by
              group
            have hc1 : Commute c ((ug : sp6X φ he z) : G) :=
              Commute.symm (hcU _ (mem_subgroupOf.1 ug.2))
            have hc2 : Commute c (m⁻¹ * ((ug : sp6X φ he z) : G)) := hC₂ab c hc _ h1
            have hcm : Commute c m := by
              rw [hmu]
              exact hc1.mul_right hc2.inv_right
            exact hcm.eq.symm
          rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
          rcases hg with rfl | hg
          · exact key _ us hus
          · rw [Set.mem_singleton_iff] at hg
            subst hg
            exact key _ ut hut
        · rw [card_inf_centralizer_conj xq.2]
          exact hsC
      have h1 : 2 ^ 12 ≤ 2 ^ 6 * 2 ^ 4 := by
        rw [← hcard, ← hEcard, hE16]
        exact Nat.mul_le_mul hk6 le_rfl
      norm_num at h1
  have hindex : ¬ 2 ∣ (sp6X φ he z).index := not_two_dvd_index_normalizer hC₂el hC₂ab huniq
  have hCz11 : ¬ 2 ^ 11 ∣ Nat.card (centralizer ({z} : Set G)) := by
    intro h
    have h1 := card_sup_dvd_of_commute (H := L) (K := zpowers z) (by
      intro l hl m hm
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hm
      exact (Commute.zpow_right (mem_centralizer_iff.1 hzL l hl) j).eq)
    rw [hLz, SteinbergBM.card_L φ he, Nat.card_zpowers, hz] at h1
    have h2 := h.trans h1
    norm_num at h2
  set ξ : sp6X φ he z →* Multiplicative (ZMod 2) := ηY.comp (θ.comp (sp6πX φ he z)) with hξ
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hξz : ∀ (g : G) (h : g⁻¹ * z * g ∈ sp6X φ he z), ξ ⟨_, h⟩ = Multiplicative.ofAdd 1 := by
    intro g hg
    set u : sp6X φ he z := ⟨_, hg⟩ with hu
    have hCu : Nat.card (centralizer ({(u : G)} : Set G)) =
        Nat.card (centralizer ({z} : Set G)) := by
      have h := card_centralizer_conj g⁻¹ z
      rwa [inv_inv] at h
    have hu2 : (u : G) ^ 2 = 1 := by
      have h := conj_sq_eq_one hz2 g⁻¹
      rwa [inv_inv] at h
    rcases hmz2 (ξ u) with hξu | hξu
    · exfalso
      by_cases huC : (u : G) ∈ C₂
      · have hle : C₂ ≤ centralizer ({(u : G)} : Set G) := fun c hc =>
          mem_centralizer_singleton_iff.2 (hC₂ab c hc _ huC)
        have h := Subgroup.card_dvd_of_le hle
        rw [hC₂card, hCu] at h
        exact hCz11 ((pow_dvd_pow 2 (by norm_num)).trans h)
      · have hf1 : sp6πX φ he z u ≠ 1 := by
          intro h
          apply huC
          have h' : u ∈ (sp6πX φ he z).ker := h
          rw [hπker, mem_subgroupOf] at h'
          exact h'
        have hf2 : sp6πX φ he z u ^ 2 = 1 := by
          rw [← map_pow, show u ^ 2 = 1 from Subtype.ext hu2, map_one]
        have hθf2 : θ (sp6πX φ he z u) ^ 2 = 1 := by rw [← map_pow, hf2, map_one]
        have hθfD : θ (sp6πX φ he z u) ∈ sp6Dstar φ he z := hηker _ hθf2 hξu
        have hθf1 : θ (sp6πX φ he z u) ≠ 1 := fun h => hf1 (hθ1' _ hf2 h)
        obtain ⟨q, -, hq⟩ := hinner _ hf2 hθfD hθf1
        set Uθ := ((projUnip k).map χ.symm.toMonoidHom).map (sp6Dstar φ he z).subtype with hUθ
        have hUθD : Uθ ≤ sp6Dstar φ he z := map_subtype_le _
        have hUθcard : Nat.card Uθ = 64 := by
          rw [hUθ, Subgroup.card_map_of_injective (sp6Dstar φ he z).subtype_injective,
            Subgroup.card_map_of_injective χ.symm.injective, card_projUnip, hk4]
        have hUθt : ∀ y ∈ Uθ, y * θ (ι glTransThreeOne) = θ (ι glTransThreeOne) * y := by
          rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
          have hvw := mem_centralizer_singleton_iff.1 (projUnip_le_centralizer_projW hv)
          have h1 : χ.symm v * ⟨θ (ι glTransThreeOne), hιD _⟩ =
              ⟨θ (ι glTransThreeOne), hιD _⟩ * χ.symm v := χ.injective (by
            rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hχt]
            exact hvw)
          exact congrArg Subtype.val h1
        have hat : a * ι glTransThreeOne = ι glTransThreeOne * a :=
          (mem_centralizer_singleton_iff.1 (hJLCa (hιJL _))).symm
        have h128 : 2 ^ 7 ∣ Nat.card (centralizer ({sp6πX φ he z u} : Set (Sp6F φ he z))) := by
          rw [← card_centralizer_conj q, hq]
          have h1 := two_mul_card_dvd_card_centralizer hRodd hZ hQmap htQ ht2 hUθD hUθt ha2'
            hat haD
          rw [hUθcard] at h1
          exact h1
        obtain ⟨P', hP'⟩ := Sylow.exists_subgroup_card_pow_prime 2 h128
        set P₁ := (P'.map (centralizer ({sp6πX φ he z u} : Set (Sp6F φ he z))).subtype).comap
          (sp6πX φ he z) with hP₁
        have hC₂X : C₂ ≤ sp6X φ he z := le_normalizer
        have hP₁card : Nat.card P₁ = 2 ^ 19 := by
          rw [hP₁, card_comap_of_surjective hπsurj, Subgroup.card_map_of_injective
            (Subgroup.subtype_injective _), hP', hπker,
            Nat.card_congr (subgroupOfEquivOfLe hC₂X).toEquiv, hC₂card]
          norm_num
        have hPcard : Nat.card (P₁.map (sp6X φ he z).subtype) = 2 ^ 19 := by
          rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hP₁card]
        have hPu : ∀ x ∈ P₁.map (sp6X φ he z).subtype, (u : G)⁻¹ * (x * u * x⁻¹) ∈ C₂ := by
          rintro _ ⟨x, hx, rfl⟩
          obtain ⟨y, -, hy⟩ := hx
          have hyc := mem_centralizer_singleton_iff.1 y.2
          have hker : u⁻¹ * (x * u * x⁻¹) ∈ (sp6πX φ he z).ker := by
            rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv]
            have hy' : (y : Sp6F φ he z) = sp6πX φ he z x := hy
            rw [← hy', hyc, mul_inv_cancel_right, inv_mul_cancel]
          rw [hπker, mem_subgroupOf] at hker
          exact hker
        have h11 := two_pow_dvd_card_centralizer hu2 hC₂el hPcard hPu (hE8 u hf1 hf2)
        rw [hCu] at h11
        exact hCz11 h11
    · exact hξu
  exact false_of_transfer_of_not_two_dvd_index hGs hGnab hindex ξ hz hξz

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
