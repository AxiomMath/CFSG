module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorAction
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSp6EvenLinearAmbientNode
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBKSp6LagrangianAlternatingExclusion
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorLayer

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModel
open CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor
open LinearMap (BilinForm)
open scoped Pointwise IsMulCommutative

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e) (z : G)

namespace ChevTwoFactorLag

theorem exists_tauEquiv (hA₂C₂ : sp6A₂ φ e ≤ sp6C₂ φ he z) :
    ∃ τ : Multiplicative Sym3 ≃* ((sp6A₂ φ e).subgroupOf (sp6C₂ φ he z)),
      ∀ B : Multiplicative Sym3, (((τ B : (sp6A₂ φ e).subgroupOf (sp6C₂ φ he z)) :
        sp6C₂ φ he z) : G) = tauHom φ he B := by
  have hmemA : ∀ B, tauHom φ he B ∈ sp6A₂ φ e := fun B => by
    rw [SteinbergBK.sp6A₂_eq_range_tauHom φ he]
    exact ⟨B, rfl⟩
  let f : Multiplicative Sym3 →* ((sp6A₂ φ e).subgroupOf (sp6C₂ φ he z)) :=
    { toFun := fun B => ⟨⟨tauHom φ he B, hA₂C₂ (hmemA B)⟩, hmemA B⟩
      map_one' := Subtype.ext (Subtype.ext (map_one _))
      map_mul' := fun B B' => Subtype.ext (Subtype.ext (map_mul _ B B')) }
  have hbij : Function.Bijective f := by
    constructor
    · intro B B' h
      exact tauHom_injective φ he (congrArg (fun x : (sp6A₂ φ e).subgroupOf (sp6C₂ φ he z) =>
        ((x : sp6C₂ φ he z) : G)) h)
    · rintro ⟨c, hc⟩
      have hc' : (c : G) ∈ (tauHom φ he).range := by
        rw [← SteinbergBK.sp6A₂_eq_range_tauHom φ he]
        exact hc
      obtain ⟨B, hB⟩ := hc'
      exact ⟨B, Subtype.ext (Subtype.ext hB)⟩
  exact ⟨MulEquiv.ofBijective f hbij, fun B => rfl⟩

end ChevTwoFactorLag

theorem sp6_two_factor_false [Finite G] (hGs : IsSimpleGroup G)
    (hGnab : ∃ x y : G, x * y ≠ y * x) (hzL : z ∈ centralizer (L : Set G))
    (hLz : L ⊔ zpowers z = centralizer ({z} : Set G)) (hinf : L ⊓ zpowers z = ⊥)
    (hz : orderOf z = 2) [FiniteDimensional (ZMod 2) V] (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (hC₂el : IsElementaryAbelian 2 (sp6C₂ φ he z))
    (hC₂card : Nat.card (sp6C₂ φ he z) = 4096) (hA₂C₂ : sp6A₂ φ e ≤ sp6C₂ φ he z)
    (hfixz : ∀ c ∈ sp6C₂ φ he z, c * z = z * c ↔ c ∈ sp6A₂ φ e)
    {V₁ : Subgroup G} (hconc : Sp6LagrangianLayerConclusion φ he z V₁)
    (htwo : Sp6LayerTwoFactor φ he z) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C₂ := sp6C₂ φ he z with hC₂def
  set A₂ := sp6A₂ φ e with hA₂def
  set X := sp6X φ he z with hXdef
  set θ := sp6θ φ he z with hθdef
  set πX := sp6πX φ he z with hπXdef
  set Q := sp6Qstar φ he z with hQdef
  set Ro := sp6Ro φ he z with hRodef
  set a := sp6a φ he z with hadef'
  set ā := sp6aBar φ he z with hādef
  set D := sp6Dstar φ he z with hDdef
  obtain ⟨-, -, ⟨hzX, hadef⟩, ⟨hLX, hLevi⟩, ⟨ι, hιdef, -, hιrange⟩, -, -, -, -, -, -, -, -,
    hθ2, ha2, -, -, -, hāo, hJCā, -, hCā, -, -, -, -, -, -, -, -, -, -, -, hCD, -, -,
    hcommR, -, hQn, hQperf, hQmap, hQcomap, hQcen, -, -, -, -, -, -, -, -, ⟨κF, hκF1, -⟩,
    -⟩ := hconc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Ψ, hΨlev, hΨa⟩ := htwo
  have : D.Normal := Subgroup.normalClosure_normal
  have : Q.Normal := hQn
  have : IsElementaryAbelian 2 C₂ := hC₂el
  have hθker : θ.ker = Ro := QuotientGroup.ker_mk' _
  have hπker : πX.ker = C₂.subgroupOf X := QuotientGroup.ker_mk' _
  have hπsurj : Function.Surjective πX := QuotientGroup.mk'_surjective _
  have hRodd : Nat.Coprime 2 (Nat.card Ro) := CFSG.pPrimeCore_coprime_card
  have ha2' : a * a = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha2, pow_two] at h
  have hā2 : ā * ā = 1 := by
    have h := pow_orderOf_eq_one ā
    rwa [hāo, pow_two] at h
  have hJD : sp6JLBar φ he z ≤ D := le_normalClosure
  have hJLQ : sp6JL φ he z ≤ Q := le_normalClosure
  have hLeviJL : ∀ g, sp6Levi φ he z g ∈ sp6JL φ he z := fun g => by
    rw [← hιrange, ← hιdef]
    exact ⟨g, rfl⟩
  have hLeviD : ∀ g, θ (sp6Levi φ he z g) ∈ D := fun g => hJD ⟨_, hLeviJL g, rfl⟩
  obtain ⟨χ, hχa, hχker⟩ := exists_layer_character D Ψ hCD hā2 hΨa (J := sp6JLBar φ he z)
    (fun j hj => by
      obtain ⟨f, hf, rfl⟩ := hj
      rw [← hιrange] at hf
      obtain ⟨g, rfl⟩ := hf
      refine ⟨g, ?_⟩
      rw [hιdef, ← hΨlev g (hLeviD g), MulEquiv.symm_apply_apply])
    hJCā hCā
  obtain ⟨η, hη⟩ := exists_layer_mulEquiv_Q θ hθker hRodd hQperf hQmap (hQcen ▸ le_rfl) Ψ
  have hηLevi : ∀ g, η.symm (g, g) = ⟨sp6Levi φ he z g, hJLQ (hLeviJL g)⟩ := fun g => by
    rw [MulEquiv.symm_apply_eq, hη _ (hLeviD g), hΨlev g (hLeviD g)]
  obtain ⟨τ, hτ⟩ := ChevTwoFactorLag.exists_tauEquiv φ he z hA₂C₂
  have hκz : ∀ c : C₂, ((κF a c : C₂) : G) = z * c * z⁻¹ := fun c => by
    have h := hκF1 ⟨z, hzX⟩ c
    rw [← hadef] at h
    exact h
  have hA : ∀ c : C₂, κF a c = c ↔ c ∈ A₂.subgroupOf C₂ := fun c => by
    rw [mem_subgroupOf, ← hfixz c c.2, Subtype.ext_iff, hκz]
    constructor
    · intro h
      calc (c : G) * z = z * c * z⁻¹ * z := by rw [h]
        _ = z * c := by group
    · intro h
      rw [← h]
      group
  have hτLevi : ∀ (g : S) (B : Sym3), κF ((η.symm (g, g) : Q) : Sp6F φ he z)
      ((τ (Multiplicative.ofAdd B) : A₂.subgroupOf C₂) : C₂) =
      ((τ (Multiplicative.ofAdd (symThreeCongr g B)) : A₂.subgroupOf C₂) : C₂) := fun g B => by
    apply Subtype.ext
    rw [hηLevi]
    change ((κF (sp6Levi φ he z g) ((τ (Multiplicative.ofAdd B) : A₂.subgroupOf C₂) : C₂) :
      C₂) : G) = _
    rw [hLevi g, hκF1, hτ, hτ]
    exact leviHom_conj_tauHom' φ he g B
  obtain ⟨Ω, Φ, hΩD, hΩa, hint⟩ := exists_model_of_two_factor (C := C₂)
    (by rw [hC₂card]; norm_num) κF θ hθker Ψ ha2' hΨa χ hχa hχker hQmap hQcomap hcommR η hη
    hA τ hτLevi
  set Ω' : Sp6F φ he z →* Ehat := Ω.toMonoidHom.comp θ with hΩ'
  have hint' : ∀ (f : Sp6F φ he z) (x : Sym3 × Sym3),
      rep12 (Ω' f) x = Φ.symm (conjRep κF f (Φ x)) := fun f x => by
    change rep12 (Ω (θ f)) x = _
    rw [hint, LinearEquiv.symm_apply_apply]
  have hfixiff : ∀ (x : X) (c : C₂), (x : G) * c = c * x ↔
      rep12 (Ω' (πX x)) (Φ.symm (Additive.ofMul c)) = Φ.symm (Additive.ofMul c) := by
    intro x c
    rw [hint', LinearEquiv.apply_symm_apply, Φ.symm.injective.eq_iff, conjRep_ofMul,
      EmbeddingLike.apply_eq_iff_eq, Subtype.ext_iff]
    change (x : G) * c = c * x ↔ ((κF (sp6πX φ he z x) c : C₂) : G) = c
    rw [hκF1]
    constructor
    · intro h
      rw [h]
      group
    · intro h
      calc (x : G) * c = x * c * (x : G)⁻¹ * x := by group
        _ = c * x := by rw [h]
  have hC₂2 : ∀ c ∈ C₂, c ^ 2 = 1 := fun c hc =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (A := C₂) c hc
  have hC₂ab : ∀ c ∈ C₂, ∀ d ∈ C₂, c * d = d * c := fun c hc d hd =>
    congrArg Subtype.val (hC₂el.toIsMulCommutative.is_comm.comm ⟨c, hc⟩ ⟨d, hd⟩)
  have huniq : ∀ U : Subgroup G, U ≤ normalizer (C₂ : Set G) → (∀ u ∈ U, u ^ 2 = 1) →
      (∀ u ∈ U, ∀ v ∈ U, u * v = v * u) → Nat.card U = Nat.card C₂ → U = C₂ := by
    intro U hUX' hU2 hUab hUcard
    have hUX : U ≤ X := hUX'
    set ρU := πX.comp (U.subgroupOf X).subtype with hρU
    have hρker : ∀ u : U.subgroupOf X, u ∈ ρU.ker ↔ ((u : X) : G) ∈ C₂ := by
      intro u
      rw [MonoidHom.mem_ker, hρU, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπker,
        mem_subgroupOf]
      rfl
    have hUcard' : Nat.card (U.subgroupOf X) = 4096 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hUX).toEquiv, hUcard, hC₂card]
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
    have hker : Nat.card ρU.ker ≤ Nat.card (Fix12 B) := by
      refine Nat.card_le_card_of_injective (fun u => ⟨Φ.symm (Additive.ofMul
        ⟨(((u : U.subgroupOf X) : X) : G), (hρker _).1 u.2⟩), ?_⟩) ?_
      · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
        exact (hfixiff (v : X) ⟨_, (hρker _).1 u.2⟩).1 (hUab _ (mem_subgroupOf.1 v.2) _
          (mem_subgroupOf.1 (u : U.subgroupOf X).2))
      · intro u v h
        have h1 := congrArg (fun x : Fix12 B => Additive.toMul (Φ x.1)) h
        change Additive.toMul (Φ (Φ.symm _)) = Additive.toMul (Φ (Φ.symm _)) at h1
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, toMul_ofMul,
          toMul_ofMul] at h1
        have h2 := congrArg Subtype.val h1
        exact Subtype.ext (Subtype.ext (Subtype.ext h2))
    by_cases hR0 : ρU.range = ⊥
    ·
      have hle : U ≤ C₂ := fun u hu => by
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
      have hlt := card_fix12_mul_card_lt B hBcomm hBsq hBne
      rw [hBcard] at hlt
      have hle : Nat.card ρU.ker * Nat.card ρU.range ≤ Nat.card (Fix12 B) * Nat.card ρU.range :=
        Nat.mul_le_mul_right _ hker
      omega
  have hindex : ¬ 2 ∣ X.index := SteinbergBM.not_two_dvd_index_normalizer hC₂2 hC₂ab huniq
  have hΩright : ∀ y : Sp6Y φ he z, (Ω y).right = χ y := by
    intro y
    rcases mult_two_cases (χ y) with h | h
    · have hy : y ∈ D := by rw [← hχker]; exact h
      rw [h, show y = ((⟨y, hy⟩ : D) : Sp6Y φ he z) from rfl, hΩD]
      rfl
    · have hy : y * ā⁻¹ ∈ D := by
        rw [← hχker, MonoidHom.mem_ker, map_mul, map_inv, h, hχa, mul_inv_cancel]
      have e1 : y = ((⟨y * ā⁻¹, hy⟩ : D) : Sp6Y φ he z) * ā := by
        change y = y * ā⁻¹ * ā
        group
      rw [h, e1, map_mul, hΩD]
      change (SemidirectProduct.inl _ * Ω (θ a)).right = _
      rw [hΩa]
      rfl
  have hrank : ∀ P : Subgroup G, P ≤ centralizer ({z} : Set G) →
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → (∀ x ∈ P, x * x = 1) → Nat.card P ≤ 128 :=
    fun P hP hc hs => card_le_of_le_centralizer hzL hLz hinf hz
      (fun P' hP' hc' hs' => card_le_sixtyFour_of_le hb hnd hV φ hP' hc' hs') hP hc hs
  set ξ : X →* Multiplicative (ZMod 2) := χ.comp (θ.comp πX) with hξ
  have hξz : ∀ (g : G) (h : g⁻¹ * z * g ∈ X), ξ ⟨_, h⟩ = Multiplicative.ofAdd 1 := by
    intro g hg
    set u : X := ⟨_, hg⟩ with hu
    rcases mult_two_cases (ξ u) with hξu | hξu
    · exfalso
      have hC8 : 256 ≤ Nat.card ↥(C₂ ⊓ centralizer ({(u : G)} : Set G)) := by
        have hu2 : u * u = 1 := Subtype.ext (by
          change g⁻¹ * z * g * (g⁻¹ * z * g) = 1
          have hz2 : z * z = 1 := by
            have h := pow_orderOf_eq_one z
            rwa [hz, pow_two] at h
          rw [show g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group, hz2]
          group)
        have hright : (Ω' (πX u)).right = 1 := by
          rw [hΩ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hΩright]
          exact hξu
        set k := (Ω' (πX u)).left with hk
        have hinl : Ω' (πX u) = SemidirectProduct.inl k :=
          SemidirectProduct.ext rfl hright
        have hk2 : k * k = 1 := by
          have h1 : Ω' (πX u) * Ω' (πX u) = 1 := by rw [← map_mul, ← map_mul, hu2, map_one,
            map_one]
          rw [hinl, ← map_mul] at h1
          exact SemidirectProduct.inl_injective (h1.trans (map_one _).symm)
        have h256 := card_fix12_inl_ge k hk2
        rw [← hinl] at h256
        refine h256.trans (le_of_eq (Nat.card_congr ?_))
        exact
          { toFun := fun x => ⟨(Additive.toMul (Φ x.1) : C₂), mem_inf.2 ⟨(Additive.toMul (Φ x.1)).2,
              mem_centralizer_singleton_iff.2 (by
                have h1 := (hfixiff u (Additive.toMul (Φ x.1))).2 (by
                  rw [ofMul_toMul, LinearEquiv.symm_apply_apply]
                  exact x.2 _ rfl)
                exact h1.symm)⟩⟩
            invFun := fun c => ⟨Φ.symm (Additive.ofMul ⟨c, (mem_inf.1 c.2).1⟩), fun b hb => by
              rw [Set.mem_singleton_iff] at hb
              subst hb
              exact (hfixiff u _).1 (mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).2).symm⟩
            left_inv := fun x => Subtype.ext (by
              change Φ.symm (Additive.ofMul (Additive.toMul (Φ x.1))) = x.1
              rw [ofMul_toMul, LinearEquiv.symm_apply_apply])
            right_inv := fun c => Subtype.ext (by
              change ((Additive.toMul (Φ (Φ.symm (Additive.ofMul _))) : C₂) : G) = c
              rw [LinearEquiv.apply_symm_apply]
              rfl) }
      set E := (C₂ ⊓ centralizer ({(u : G)} : Set G)).map (MulAut.conj g).toMonoidHom with hE
      have hEcard : Nat.card E = Nat.card ↥(C₂ ⊓ centralizer ({(u : G)} : Set G)) :=
        Subgroup.card_map_of_injective (MulAut.conj g).injective
      have hEz : E ≤ centralizer ({z} : Set G) := by
        rintro _ ⟨c, hc, rfl⟩
        have hcu := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
        rw [mem_centralizer_singleton_iff]
        change g * c * g⁻¹ * z = z * (g * c * g⁻¹)
        change (c : G) * (g⁻¹ * z * g) = g⁻¹ * z * g * c at hcu
        calc g * c * g⁻¹ * z = g * (c * (g⁻¹ * z * g)) * g⁻¹ := by group
          _ = g * (g⁻¹ * z * g * c) * g⁻¹ := by rw [hcu]
          _ = z * (g * c * g⁻¹) := by group
      have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
        rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
        rw [← map_mul, ← map_mul, hC₂ab c (mem_inf.1 hc).1 d (mem_inf.1 hd).1]
      have hEsq : ∀ x ∈ E, x * x = 1 := by
        rintro _ ⟨c, hc, rfl⟩
        rw [← map_mul, ← pow_two, hC₂2 c (mem_inf.1 hc).1, map_one]
      have h128 := hrank E hEz hEab hEsq
      omega
    · exact hξu
  exact SteinbergBM.false_of_transfer_of_not_two_dvd_index hGs hGnab hindex ξ hz hξz

theorem standard_binary_symplectic_six_elementary_lagrangian_two_factor_ambient_exclusion
    [Finite G] (hF : Sp6LagrangianFullOddCoreStmt) (hGs : IsSimpleGroup G)
    (hGnab : ∃ x y : G, x * y ≠ y * x) (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hodd : ∀ t : G, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set G)) = ⊥)
    (_hcyc : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (_htype : CFSG.Blueprint.Recognition.Exact.EvenStandardType (L ⧸ center L))
    (_hexc : ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException (L ⧸ center L))
    (_hres : CFSG.Blueprint.Recognition.Exact.EvenStandardResidual L)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel (L ⧸ center L) .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) [FiniteDimensional (ZMod 2) V] (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6)
    (hfull : conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G)) :
    (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype = zpowers z ∧
    z ∈ centralizer (L : Set G) ∧ L ⊔ zpowers z = centralizer ({z} : Set G) ∧
    L ⊓ zpowers z = ⊥ ∧
    (∃! E₂ : Subgroup G, (E₂ : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative E₂ ∧
      Nat.card E₂ = 512) ∧
    IsElementaryAbelian 2 (sp6E₂ φ he z) ∧
    (∀ m ∈ sp6N₂ φ e z, ∀ c ∈ sp6C₂ φ he z, m * c * m⁻¹ ∈ sp6C₂ φ he z) ∧
    Nat.card (sp6C₂ φ he z) = 4096 ∧
    (IsElementaryAbelian 2 (sp6C₂ φ he z) →
      sp6Dstar φ he z = CFSG.layer (Sp6Y φ he z) ∧ Sp6LayerSimple φ he z ∧
        ¬ Sp6LayerTwoFactor φ he z) := by
  obtain ⟨hTz, hzC, hsup, hinf, hE₂F, hE₂ab, hE₂card, hE₂uniq, hE₂el, hC₂N, hC₂card, hrest⟩ :=
    SteinbergBM.sp6_even_linear_branch φ he z hF hGs hGnab hKP hL hodd hZ hmodel T hT hzT hz hb
      hnd hV hfull
  refine ⟨hTz, hzC, hsup, hinf, ⟨sp6E₂ φ he z, ⟨hE₂F, hE₂ab, hE₂card⟩,
    fun E' ⟨h1, h2, h3⟩ => hE₂uniq E' h1 h2 h3⟩, hE₂el, hC₂N, hC₂card, fun hC₂el => ?_⟩
  obtain ⟨-, hA₂C₂, hfix, -, V₁, hconc⟩ := hrest hC₂el
  have hntwo : ¬ Sp6LayerTwoFactor φ he z := fun htwo =>
    sp6_two_factor_false φ he z hGs hGnab hzC hsup hinf hz hb hnd hV hC₂el hC₂card hA₂C₂ hfix
      hconc htwo
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, hlayer, -, hxor, -⟩ := hconc
  refine ⟨hlayer, ?_, hntwo⟩
  rcases hxor with ⟨hs, -⟩ | ⟨htwo, -⟩
  · exact hs
  · exact absurd htwo hntwo

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
