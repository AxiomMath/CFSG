module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorAltFusion
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorAltLayer
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorAltModel
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorLayer
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBKSp6LagrangianAlternatingExclusion
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSp6EvenLinearAmbientExclusion

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.Child3

open Subgroup Module Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.RadicalLabels
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (Mat3)
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModel
open CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor
open LinearMap (BilinForm)
open scoped Pointwise IsMulCommutative

section Core

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e) (z : G)

theorem exists_tauEquiv' {C : Subgroup G} (hA₂C : sp6A₂ φ e ≤ C) :
    ∃ τ : Multiplicative Sym3 ≃* ((sp6A₂ φ e).subgroupOf C),
      ∀ B : Multiplicative Sym3, (((τ B : (sp6A₂ φ e).subgroupOf C) : C) : G) = tauHom φ he B := by
  have hmemA : ∀ B, tauHom φ he B ∈ sp6A₂ φ e := fun B => by
    rw [SteinbergBK.sp6A₂_eq_range_tauHom φ he]
    exact ⟨B, rfl⟩
  let f : Multiplicative Sym3 →* ((sp6A₂ φ e).subgroupOf C) :=
    { toFun := fun B => ⟨⟨tauHom φ he B, hA₂C (hmemA B)⟩, hmemA B⟩
      map_one' := Subtype.ext (Subtype.ext (map_one _))
      map_mul' := fun B B' => Subtype.ext (Subtype.ext (map_mul _ B B')) }
  have hbij : Function.Bijective f := by
    constructor
    · intro B B' h
      exact tauHom_injective φ he (congrArg (fun x : (sp6A₂ φ e).subgroupOf C =>
        ((x : C) : G)) h)
    · rintro ⟨c, hc⟩
      have hc' : (c : G) ∈ (tauHom φ he).range := by
        rw [← SteinbergBK.sp6A₂_eq_range_tauHom φ he]
        exact hc
      obtain ⟨B, hB⟩ := hc'
      exact ⟨B, Subtype.ext (Subtype.ext hB)⟩
  exact ⟨MulEquiv.ofBijective f hbij, fun B => rfl⟩

theorem alt8_two_factor_false [Finite G] (hGs : IsSimpleGroup G)
    (hGnab : ∃ x y : G, x * y ≠ y * x) (hzL : z ∈ centralizer (L : Set G))
    (hLz : L ⊔ zpowers z = centralizer ({z} : Set G)) (hinf : L ⊓ zpowers z = ⊥)
    (hz : orderOf z = 2) [FiniteDimensional (ZMod 2) V] (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) {C : Subgroup G} (hCel : IsElementaryAbelian 2 C)
    (hCcard : Nat.card C = 512) (hA₂C : sp6A₂ φ e ≤ C)
    (hfixz : ∀ c ∈ C, c * z = z * c ↔ c ∈ sp6A₂ φ e)
    (hzX : z ∈ layX C) (hLX : ∀ g, leviHom φ he g ∈ layX C)
    (hιrange : (layLeviHom C (leviHom φ he) hLX).range = layJL C (leviHom φ he))
    (ha2 : orderOf (laya C z) = 2)
    (hθ2 : ∀ P : Subgroup (LayF C), IsPGroup 2 P → Set.InjOn (layθ C) P)
    (hāo : orderOf (layaBar C z) = 2)
    (hJCā : layJLBar C (leviHom φ he) ≤ centralizer {layaBar C z})
    (hCā : zpowers (layaBar C z) ⊔ layJLBar C (leviHom φ he) = centralizer {layaBar C z})
    (hCD : centralizer (layDstar C (leviHom φ he) : Set (LayY C)) = ⊥)
    (hcommR : ∀ x ∈ (layDstar C (leviHom φ he)).comap (layθ C), ∀ r ∈ layRo C, x * r = r * x)
    (hQperf : ⁅normalClosure (layJL C (leviHom φ he) : Set (LayF C)),
      normalClosure (layJL C (leviHom φ he) : Set (LayF C))⁆ =
        normalClosure (layJL C (leviHom φ he) : Set (LayF C)))
    (hQmap : (normalClosure (layJL C (leviHom φ he) : Set (LayF C))).map (layθ C) =
      layDstar C (leviHom φ he))
    (hQcomap : (layDstar C (leviHom φ he)).comap (layθ C) =
      layRo C ⊔ normalClosure (layJL C (leviHom φ he) : Set (LayF C)))
    (hQcen : (center (normalClosure (layJL C (leviHom φ he) : Set (LayF C)))).map
      (normalClosure (layJL C (leviHom φ he) : Set (LayF C))).subtype =
        normalClosure (layJL C (leviHom φ he) : Set (LayF C)) ⊓ layRo C)
    (hCK : C ⊓ layK C = ⊥) (hKodd : Odd (Nat.card (layK C)))
    (hKn : ∀ g ∈ layX C, ∀ k ∈ layK C, g * k * g⁻¹ ∈ layK C)
    (κF : LayF C →* MulAut C)
    (hκF1 : ∀ (x : layX C) (c : C), ((κF (layπ C x) c : C) : G) = x * c * (x : G)⁻¹)
    (hκFker : κF.ker = layKBar C) (hKBR : layKBar C ≤ layRo C)
    (Ψ : layDstar C (leviHom φ he) ≃* K)
    (hΨlev : ∀ (g : GL (Fin 3) (ZMod 2))
      (h : layθ C (layLeviHom C (leviHom φ he) hLX g) ∈ layDstar C (leviHom φ he)),
      Ψ ⟨_, h⟩ = (g, g))
    (hΨa : ∀ (d : LayY C) (hd : d ∈ layDstar C (leviHom φ he))
      (hda : (layaBar C z)⁻¹ * d * layaBar C z ∈ layDstar C (leviHom φ he)),
      Ψ ⟨_, hda⟩ = (Ψ ⟨d, hd⟩).swap) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := layX C with hXdef
  set θ := layθ C with hθdef
  set πX := layπ C with hπXdef
  set Q := normalClosure (layJL C (leviHom φ he) : Set (LayF C)) with hQdef
  set Ro := layRo C with hRodef
  set a := laya C z with hadef
  set ā := layaBar C z with hādef
  set ι := layLeviHom C (leviHom φ he) hLX with hιdef
  have : (layDstar C (leviHom φ he)).Normal := Subgroup.normalClosure_normal
  have : Q.Normal := Subgroup.normalClosure_normal
  have : IsElementaryAbelian 2 C := hCel
  have hθker : θ.ker = Ro := QuotientGroup.ker_mk' _
  have hπker : πX.ker = C.subgroupOf X := QuotientGroup.ker_mk' _
  have hπsurj : Function.Surjective πX := QuotientGroup.mk'_surjective _
  have hθsurj : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hRodd : Nat.Coprime 2 (Nat.card Ro) := CFSG.pPrimeCore_coprime_card
  have hadef2 : a = πX ⟨z, hzX⟩ := laya_eq C z hzX
  have ha2' : a * a = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha2, pow_two] at h
  have hā2 : ā * ā = 1 := by
    have h := pow_orderOf_eq_one ā
    rwa [hāo, pow_two] at h
  have hJD : layJLBar C (leviHom φ he) ≤ (layDstar C (leviHom φ he)) := le_normalClosure
  have hJLQ : layJL C (leviHom φ he) ≤ Q := le_normalClosure
  have hιJL : ∀ g, ι g ∈ layJL C (leviHom φ he) := fun g => by
    rw [← hιrange]
    exact ⟨g, rfl⟩
  have hιD : ∀ g, θ (ι g) ∈ layDstar C (leviHom φ he) := fun g =>
    hJD ⟨_, hιJL g, rfl⟩
  obtain ⟨χ, hχa, hχker⟩ := exists_layer_character (layDstar C (leviHom φ he)) Ψ hCD hā2 hΨa
    (J := layJLBar C (leviHom φ he))
    (fun j hj => by
      obtain ⟨f, hf, rfl⟩ := hj
      rw [← hιrange] at hf
      obtain ⟨g, rfl⟩ := hf
      refine ⟨g, ?_⟩
      rw [← hΨlev g (hιD g), MulEquiv.symm_apply_apply])
    hJCā hCā
  obtain ⟨η, hη⟩ := exists_layer_mulEquiv_Q θ hθker hRodd hQperf hQmap (hQcen ▸ le_rfl) Ψ
  have hηLevi : ∀ g, η.symm (g, g) = ⟨ι g, hJLQ (hιJL g)⟩ := fun g => by
    rw [MulEquiv.symm_apply_eq, hη _ (hιD g), hΨlev g (hιD g)]
  obtain ⟨τ, hτ⟩ := exists_tauEquiv' φ he hA₂C
  have hκz : ∀ c : C, ((κF a c : C) : G) = z * c * z⁻¹ := fun c => by
    have h := hκF1 ⟨z, hzX⟩ c
    rw [← hadef2] at h
    exact h
  have hA : ∀ c : C, κF a c = c ↔ c ∈ (sp6A₂ φ e).subgroupOf C := fun c => by
    rw [mem_subgroupOf, ← hfixz c c.2, Subtype.ext_iff, hκz]
    constructor
    · intro h
      calc (c : G) * z = z * c * z⁻¹ * z := by rw [h]
        _ = z * c := by group
    · intro h
      rw [← h]
      group
  have hτLevi : ∀ (g : S) (B : Sym3), κF ((η.symm (g, g) : Q) : LayF C)
      ((τ (Multiplicative.ofAdd B) : (sp6A₂ φ e).subgroupOf C) : C) =
      ((τ (Multiplicative.ofAdd (symThreeCongr g B)) : (sp6A₂ φ e).subgroupOf C) : C) :=
    fun g B => by
      apply Subtype.ext
      rw [hηLevi]
      change ((κF (πX ⟨(leviHom φ he) g, hLX g⟩) ((τ (Multiplicative.ofAdd B) :
        (sp6A₂ φ e).subgroupOf C) : C) : C) : G) = _
      rw [hκF1, hτ, hτ]
      exact leviHom_conj_tauHom' φ he g B
  obtain ⟨Ω, Φ, hΩright, hΩa, hRtriv, hint⟩ := exists_model_of_two_factor9 (C := C)
    (by rw [hCcard]; norm_num) κF θ hθker Ψ ha2' hΨa χ hχa hχker hQmap hQcomap hcommR η hη
    hA τ hτLevi
  have hRoK : Ro ≤ layKBar C := fun r hr => by
    rw [← hκFker, MonoidHom.mem_ker]
    exact MulEquiv.ext (hRtriv r hr)
  set ΩX : X →* Ehat := Ω.toMonoidHom.comp (θ.comp πX) with hΩX
  have hΩXsurj : Function.Surjective ΩX := fun e' => by
    obtain ⟨y, rfl⟩ := Ω.surjective e'
    obtain ⟨f, rfl⟩ := hθsurj y
    obtain ⟨x, rfl⟩ := hπsurj f
    exact ⟨x, rfl⟩
  have hCX : C ≤ X := le_normalizer
  have hKX : layK C ≤ X := (map_subtype_le _).trans (centralizer_le_normalizer _)
  have hΩXker : ΩX.ker = (C.subgroupOf X) ⊔ ((layK C).subgroupOf X) := by
    ext x
    rw [MonoidHom.mem_ker]
    change Ω (θ (πX x)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hθker]
    constructor
    · intro hx
      obtain ⟨k, hk, hkx⟩ := hRoK hx
      have hk' : (k : G) ∈ layK C := mem_subgroupOf.1 hk
      have h1 : k⁻¹ * x ∈ πX.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
      rw [hπker] at h1
      rw [show x = k * (k⁻¹ * x) by group]
      exact mul_mem (mem_sup_right hk) (mem_sup_left h1)
    · intro hx
      rw [← SetLike.mem_coe] at hx
      have hKn' : ((layK C).subgroupOf X).Normal := ⟨fun n hn g => by
        rw [mem_subgroupOf] at hn ⊢
        exact hKn g g.2 n hn⟩
      rw [Subgroup.mul_normal] at hx
      obtain ⟨c, hc, k, hk, rfl⟩ := hx
      have hπc : πX c = 1 := by
        rw [← MonoidHom.mem_ker, hπker]
        exact hc
      rw [map_mul, hπc, one_mul]
      exact hKBR ⟨k, hk, rfl⟩
  have hint' : ∀ (x : X) (c : C), Φ.symm (Additive.ofMul (κF (πX x) c)) =
      repE (ΩX x) (Φ.symm (Additive.ofMul c)) := fun x c => by
    rw [← conjRep_ofMul, ← LinearEquiv.apply_symm_apply Φ (Additive.ofMul c), hint,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rfl
  have hfixiff : ∀ (x : X) (c : C), (x : G) * c = c * x ↔
      repE (ΩX x) (Φ.symm (Additive.ofMul c)) = Φ.symm (Additive.ofMul c) := by
    intro x c
    rw [← hint', Φ.symm.injective.eq_iff, EmbeddingLike.apply_eq_iff_eq, Subtype.ext_iff, hκF1]
    constructor
    · intro h
      rw [h]
      group
    · intro h
      calc (x : G) * c = x * c * (x : G)⁻¹ * x := by group
        _ = c * x := by rw [h]
  have hC2 : ∀ c ∈ C, c ^ 2 = 1 := fun c hc =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (A := C) c hc
  have hCab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c := fun c hc d hd =>
    congrArg Subtype.val (hCel.toIsMulCommutative.is_comm.comm ⟨c, hc⟩ ⟨d, hd⟩)
  have huniq : ∀ U : Subgroup G, U ≤ normalizer (C : Set G) → (∀ u ∈ U, u ^ 2 = 1) →
      (∀ u ∈ U, ∀ v ∈ U, u * v = v * u) → Nat.card U = Nat.card C → U = C := by
    intro U hUX' hU2 hUab hUcard
    have hUX : U ≤ X := hUX'
    set ρU := πX.comp (U.subgroupOf X).subtype with hρU
    have hρker : ∀ u : U.subgroupOf X, u ∈ ρU.ker ↔ ((u : X) : G) ∈ C := by
      intro u
      rw [MonoidHom.mem_ker, hρU, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπker,
        mem_subgroupOf]
      rfl
    have hUcard' : Nat.card (U.subgroupOf X) = 512 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hUX).toEquiv, hUcard, hCcard]
    have hcard := Subgroup.card_ker_mul_card_range ρU
    rw [hUcard'] at hcard
    have hR2 : ∀ y ∈ ρU.range, y * y = 1 := by
      rintro _ ⟨u, rfl⟩
      have hu : u * u = 1 := Subtype.ext (Subtype.ext (by
        have := hU2 _ (mem_subgroupOf.1 u.2)
        rwa [pow_two] at this))
      rw [← map_mul, hu, map_one]
    have hRcomm : ∀ y ∈ ρU.range, ∀ y' ∈ ρU.range, y * y' = y' * y := by
      rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subtype.ext (hUab _ (mem_subgroupOf.1 u.2) _ (mem_subgroupOf.1 v.2)))
    have hR2grp : IsPGroup 2 ρU.range := fun y => ⟨1, Subtype.ext (by
      rw [pow_one, pow_two]
      exact hR2 _ y.2)⟩
    set Ω' : LayF C →* Ehat := Ω.toMonoidHom.comp θ with hΩ'
    have hinjR : Set.InjOn Ω' ρU.range := fun y hy y' hy' h =>
      hθ2 _ hR2grp hy hy' (Ω.injective h)
    set B := ρU.range.map Ω' with hB
    have hBcard : Nat.card B = Nat.card ρU.range := by
      rw [hB, ← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn hinjR,
        SetLike.coe_sort_coe]
    have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hRcomm x hx y hy]
    have hBsq : ∀ x ∈ B, x * x = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hR2 x hx, map_one]
    have hker : Nat.card ρU.ker ≤ Nat.card (FixM B) := by
      refine Nat.card_le_card_of_injective (fun u => ⟨Φ.symm (Additive.ofMul
        ⟨(((u : U.subgroupOf X) : X) : G), (hρker _).1 u.2⟩), ?_⟩) ?_
      · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
        exact (hfixiff (v : X) ⟨_, (hρker _).1 u.2⟩).1 (hUab _ (mem_subgroupOf.1 v.2) _
          (mem_subgroupOf.1 (u : U.subgroupOf X).2))
      · intro u v h
        have h1 := congrArg (fun x : FixM B => Additive.toMul (Φ x.1)) h
        change Additive.toMul (Φ (Φ.symm _)) = Additive.toMul (Φ (Φ.symm _)) at h1
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, toMul_ofMul,
          toMul_ofMul] at h1
        have h2 := congrArg Subtype.val h1
        exact Subtype.ext (Subtype.ext (Subtype.ext h2))
    by_cases hR0 : ρU.range = ⊥
    · have hle : U ≤ C := fun u hu => by
        have h1 : ρU ⟨⟨u, hUX hu⟩, hu⟩ = 1 := by
          have : ρU ⟨⟨u, hUX hu⟩, hu⟩ ∈ ρU.range := ⟨_, rfl⟩
          rw [hR0] at this
          exact this
        exact (hρker _).1 h1
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hUcard])
    · exfalso
      have hBne : B ≠ ⊥ := by
        intro h
        apply hR0
        rw [eq_bot_iff]
        intro y hy
        have h1 : Ω' y ∈ B := ⟨y, hy, rfl⟩
        rw [h, Subgroup.mem_bot] at h1
        exact hinjR hy (one_mem _) (h1.trans (map_one Ω').symm)
      have hlt := card_fixM_mul_card_lt B hBcomm hBsq hBne
      rw [hBcard] at hlt
      have hle : Nat.card ρU.ker * Nat.card ρU.range ≤ Nat.card (FixM B) * Nat.card ρU.range :=
        Nat.mul_le_mul_right _ hker
      omega
  have hindex : ¬ 2 ∣ X.index := SteinbergBM.not_two_dvd_index_normalizer hC2 hCab huniq
  have hCzcard : Nat.card (centralizer ({z} : Set G)) = 2903040 := by
    rw [← hLz, BinarySymplecticSix.card_sup_eq_mul (zpowers_le.2 hzL) hinf, Nat.card_zpowers, hz,
      SteinbergBM.card_L φ he]
  have hrank : ∀ P : Subgroup G, P ≤ centralizer ({z} : Set G) →
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → (∀ x ∈ P, x * x = 1) → Nat.card P ≤ 128 :=
    fun P hP hc hs => card_le_of_le_centralizer hzL hLz hinf hz
      (fun P' hP' hc' hs' => card_le_sixtyFour_of_le hb hnd hV φ hP' hc' hs') hP hc hs
  have hzz : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz, pow_two] at h
  have hKn' : ((layK C).subgroupOf X).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact hKn g g.2 n hn⟩
  have hCn' : (C.subgroupOf X).Normal := Subgroup.normal_in_normalizer
  have hC2' : ∀ c ∈ C.subgroupOf X, c * c = 1 := fun c hc => Subtype.ext (by
    have := hC2 _ (mem_subgroupOf.1 hc)
    rwa [pow_two] at this)
  have hCcard' : Nat.card (C.subgroupOf X) = 512 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCX).toEquiv, hCcard]
  have hKodd' : Odd (Nat.card ((layK C).subgroupOf X)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hKX).toEquiv]
  have hCK' : C.subgroupOf X ⊓ (layK C).subgroupOf X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : G) ∈ C ⊓ layK C :=
      mem_inf.2 ⟨mem_subgroupOf.1 (mem_inf.1 hx).1, mem_subgroupOf.1 (mem_inf.1 hx).2⟩
    rw [hCK, mem_bot] at h1
    exact (mem_bot).2 (Subtype.ext h1)
  set μ : C.subgroupOf X → Mat3 := fun c =>
    Φ.symm (Additive.ofMul ⟨((c : X) : G), mem_subgroupOf.1 c.2⟩) with hμ
  have hμinj : Function.Injective μ := fun c d h => by
    have h1 := Φ.symm.injective h
    have h2 : ((c : X) : G) = ((d : X) : G) :=
      congrArg (fun w => ((Additive.toMul w : C) : G)) h1
    exact Subtype.ext (Subtype.ext h2)
  have hμadd : ∀ c d : C.subgroupOf X, μ (c * d) = μ c + μ d := fun c d => by
    rw [hμ]
    simp only
    rw [← map_add]
    rfl
  have hμeq : ∀ (x : X) (c : C.subgroupOf X),
      μ ⟨x * c * x⁻¹, hCn'.conj_mem _ c.2 x⟩ = repE (ΩX x) (μ c) := fun x c => by
    rw [hμ]
    simp only
    rw [← hint']
    congr 2
    apply Subtype.ext
    rw [hκF1]
    rfl
  set χX : X →* Multiplicative (ZMod 2) := χ.comp (θ.comp πX) with hχX
  have hfus : ∀ x : G, x * z * x⁻¹ ∈ X → Odd (X.relIndex (centralizer {x * z * x⁻¹})) →
      DegreeEight.subVal χX (x * z * x⁻¹) = Multiplicative.ofAdd 1 := by
    intro x hu hodd
    rw [DegreeEight.subVal_of_mem χX hu]
    set u : X := ⟨_, hu⟩ with hudef
    rcases mult_two_cases (χX u) with h | h
    · exfalso
      have hu2 : u * u = 1 := Subtype.ext (by
        change x * z * x⁻¹ * (x * z * x⁻¹) = 1
        rw [show x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ by group, hzz, mul_one,
          mul_inv_cancel])
      have hCu : Nat.card (centralizer ({(u : G)} : Set G)) = 2903040 := by
        rw [SteinbergBM.card_centralizer_conj, hCzcard]
      by_cases huC : (u : G) ∈ C
      ·
        set E := C.map (MulAut.conj x⁻¹).toMonoidHom with hE
        have hEcard : Nat.card E = 512 := by
          rw [hE, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hCcard]
        have hEz : E ≤ centralizer ({z} : Set G) := by
          rintro _ ⟨c, hc, rfl⟩
          have hcu : c * (x * z * x⁻¹) = x * z * x⁻¹ * c := hCab c hc _ huC
          rw [mem_centralizer_singleton_iff]
          change x⁻¹ * c * x⁻¹⁻¹ * z = z * (x⁻¹ * c * x⁻¹⁻¹)
          calc x⁻¹ * c * x⁻¹⁻¹ * z = x⁻¹ * (c * (x * z * x⁻¹)) * x := by group
            _ = x⁻¹ * (x * z * x⁻¹ * c) * x := by rw [hcu]
            _ = z * (x⁻¹ * c * x⁻¹⁻¹) := by group
        have hEab : ∀ y ∈ E, ∀ y' ∈ E, y * y' = y' * y := by
          rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
          rw [← map_mul, ← map_mul, hCab c hc d hd]
        have hEsq : ∀ y ∈ E, y * y = 1 := by
          rintro _ ⟨c, hc, rfl⟩
          rw [← map_mul, ← pow_two, hC2 c hc, map_one]
        have := hrank E hEz hEab hEsq
        omega
      ·
        have huC' : u ∉ C.subgroupOf X := fun h' => huC (mem_subgroupOf.1 h')
        have hur : (ΩX u).right = 1 := by
          change (Ω (θ (πX u))).right = 1
          rw [hΩright]
          exact h
        have hne := exact_two_part_ne_ten_of_odd_kernel hC2' hCcard' hKodd' hCK' ΩX hΩXsurj
          hΩXker μ hμinj hμadd hμeq hu2 huC' hur
        have hcent : Nat.card (centralizer ({u} : Set X)) =
            Nat.card (X ⊓ centralizer ({(u : G)} : Set G) : Subgroup G) := by
          have heq : centralizer ({u} : Set X) =
              (centralizer ({(u : G)} : Set G)).subgroupOf X := by
            ext y
            rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_centralizer_singleton_iff,
              Subtype.ext_iff]
            rfl
          rw [heq, ← inf_subgroupOf_left]
          exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
        have hrel := relIndex_mul_card X (centralizer ({(u : G)} : Set G))
        rw [hCu] at hrel
        apply hne
        rw [hcent]
        have hodd' : Odd (X.relIndex (centralizer ({(u : G)} : Set G))) := hodd
        have hcop : Nat.Coprime (2 ^ 10) (X.relIndex (centralizer ({(u : G)} : Set G))) :=
          Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd')
        refine ⟨hcop.dvd_of_dvd_mul_left ⟨2835, hrel.trans (by norm_num)⟩, fun h11 => ?_⟩
        have h' := h11.mul_left (X.relIndex (centralizer ({(u : G)} : Set G)))
        rw [hrel] at h'
        norm_num at h'
    · exact h
  have hXodd : Odd X.index := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hindex)
  obtain ⟨ν, hν⟩ := SteinbergBX.TwoFactor.exists_hom_ne_one_of_odd_index hzz hXodd χX hfus
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hGs ν.ker (MonoidHom.normal_ker _)
    with h | h
  · obtain ⟨x, y, hxy⟩ := hGnab
    apply hxy
    have hinj : Function.Injective ν := (MonoidHom.ker_eq_bot_iff _).1 h
    apply hinj
    rw [map_mul, map_mul, mul_comm]
  · have hz1 : z ∈ ν.ker := by
      rw [h]
      exact mem_top z
    have hz2 : ν z = 1 := hz1
    rw [hν] at hz2
    exact absurd (ofAdd_eq_one.mp hz2) one_ne_zero

end Core

end CFSG.EvenSmallLie.Child3
