module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankArith
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankFix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankProj
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineLin
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus

public section

namespace CFSG.QuasithinUnique.Lin2.OddRank

open CFSG.Assembly.LowTwoRank CFSG.SectionRank CFSG.SectionRank.ClassicalEven Matrix
open CFSG.Open (IsElemAbelian)
open CFSG.QuasithinUnique.Id2519

section Group

theorem sq_eq_one_of_mul_comm {G : Type*} [Group G] {g h c : G} (hh : h ^ 2 = 1)
    (hc : c ∈ Subgroup.center G) (hgh : h * g = g * h * c) : c ^ 2 = 1 := by
  have hc' : ∀ x : G, c * x = x * c := fun x => Subgroup.mem_center_iff.mp hc x |>.symm
  have hh' : h * h = 1 := by rwa [← sq]
  have hhi : h⁻¹ * h⁻¹ = 1 := by rw [← _root_.mul_inv_rev, hh', inv_one]
  have e1 : h * g * h⁻¹ = g * c := by
    calc h * g * h⁻¹ = g * h * c * h⁻¹ := by rw [hgh]
      _ = g * (h * (c * h⁻¹)) := by group
      _ = g * (h * (h⁻¹ * c)) := by rw [hc' h⁻¹]
      _ = g * c := by group
  have e2 : h * (h * g * h⁻¹) * h⁻¹ = g := by
    calc h * (h * g * h⁻¹) * h⁻¹ = (h * h) * g * (h⁻¹ * h⁻¹) := by group
      _ = g := by rw [hh', hhi]; group
  have e3 : h * (g * c) * h⁻¹ = g * c * c := by
    calc h * (g * c) * h⁻¹ = (h * g * h⁻¹) * c := by
          calc h * (g * c) * h⁻¹ = h * g * (c * h⁻¹) := by group
            _ = h * g * (h⁻¹ * c) := by rw [hc' h⁻¹]
            _ = (h * g * h⁻¹) * c := by group
      _ = g * c * c := by rw [e1]
  rw [e1] at e2
  have e4 : g * c * c = g := by rw [← e3]; exact e2
  have e5 : c * c = 1 := by
    have := congrArg (fun z => g⁻¹ * z) e4
    simpa [mul_assoc] using this
  rwa [sq]

end Group

section Plumbing

variable {F : Type} [Field F]

theorem scalar_pow_three {z : GL (Fin 3) F} (hz : z ∈ StatedScalars (Fin 3) F)
    (hdet : (z : Matrix (Fin 3) (Fin 3) F).det = 1) : z ^ 3 = 1 :=
  CFSG.Open.StatedAPI.pow_three_eq_one_of_mem_statedScalars hz hdet

theorem det_eq_one_of_mem_sl {x : GL (Fin 3) F} (hx : x ∈ StatedSL 3 F) :
    (x : Matrix (Fin 3) (Fin 3) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hx

end Plumbing

section PSL3

variable {F : Type} [Field F] [Finite F]

theorem dvd_of_normalizes_proj {H : Subgroup (GL (Fin 3) F)}
    (hdet : ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) F).det = 1) {m : ℕ} (hq : Nat.card F = 2 ^ m)
    (hm : 1 ≤ m) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) {x : StatedProj H}
    (hx : orderOf x = ℓ) {Ub : Subgroup (StatedProj H)} (hU1 : Ub ≠ ⊥) (hU : IsElemAbelian 2 Ub)
    (hxn : x ∈ Subgroup.normalizer (Ub : Set (StatedProj H))) : ℓ ∣ 2 ^ (2 * m) - 1 := by
  let N : Subgroup H := (StatedScalars (Fin 3) F).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  have hπ1 : ∀ g : H, π g = 1 ↔ (g : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F := fun g => by
    change QuotientGroup.mk' N g = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπeq : ∀ u v : H, π u = π v → ((u : GL (Fin 3) F)⁻¹ * v) ∈ StatedScalars (Fin 3) F :=
    fun u v h => by
      change QuotientGroup.mk' N u = QuotientGroup.mk' N v at h
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf] at h
      simpa using h
  have hcube : ∀ g : H, π g = 1 → (g : GL (Fin 3) F) ^ 3 = 1 := fun g hg =>
    scalar_pow_three ((hπ1 g).mp hg) (hdet g g.2)
  have hcube' : ∀ g : H, π g = 1 → g ^ 3 = 1 := fun g hg =>
    Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hcube g hg)
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective N x
  have hx₀' : π x₀ = x := hx₀
  set y₀ : H := x₀ ^ 3 with hy₀
  have hy₀ℓ : y₀ ^ ℓ = 1 := by
    have h1 : π (x₀ ^ ℓ) = 1 := by
      rw [map_pow, hx₀', ← hx]
      exact pow_orderOf_eq_one x
    have h2 := hcube' _ h1
    have : y₀ ^ ℓ = (x₀ ^ ℓ) ^ 3 := by rw [hy₀, ← pow_mul, ← pow_mul, mul_comm]
    rw [this]
    exact h2
  have hπy₀ : π y₀ = x ^ 3 := by rw [hy₀, map_pow, hx₀']
  have hy₀1 : y₀ ≠ 1 := by
    intro h
    have h3 : x ^ 3 = 1 := by rw [← hπy₀, h, map_one]
    have hd : ℓ ∣ 3 := hx ▸ orderOf_dvd_of_pow_eq_one h3
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp hd)
  have hcomm : ∀ g h : H, g ^ 2 = 1 → h ^ 2 = 1 → π g ∈ Ub → π h ∈ Ub → g * h = h * g := by
    intro g h hg hh hgU hhU
    have hπc : π (g * h) = π (h * g) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hU.1.is_comm.comm ⟨π g, hgU⟩ ⟨π h, hhU⟩)
    have hc := hπeq _ _ hπc
    set c : H := (g * h)⁻¹ * (h * g) with hcdef
    have hcGL : (c : GL (Fin 3) F) =
        ((g * h : H) : GL (Fin 3) F)⁻¹ * ((h * g : H) : GL (Fin 3) F) := rfl
    have hcs : (c : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F := by rw [hcGL]; exact hc
    have hπc1 : π c = 1 := (hπ1 c).mpr hcs
    have hcen : c ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      have hz : (c : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) := by
        have : StatedScalars (Fin 3) F = Subgroup.center (GL (Fin 3) F) := by
          rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
        rw [← this]; exact hcs
      exact Subgroup.mem_center_iff.mp hz k
    have hhg : h * g = g * h * c := by rw [hcdef]; group
    have hc2 : c ^ 2 = 1 := sq_eq_one_of_mul_comm hh hcen hhg
    have hc3 : c ^ 3 = 1 := hcube' c hπc1
    have hc1 : c = 1 := by
      calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
        _ = 1 := by rw [hc3, hc2]; group
    rw [hc1, mul_one] at hhg
    exact hhg.symm
  let T : Subgroup (GL (Fin 3) F) :=
    { carrier := {g | ∃ hg : g ∈ H, g ^ 2 = 1 ∧ π ⟨g, hg⟩ ∈ Ub}
      mul_mem' := by
        rintro a b ⟨ha, ha2, haU⟩ ⟨hb, hb2, hbU⟩
        have ha2' : (⟨a, ha⟩ : H) ^ 2 = 1 := Subtype.ext ha2
        have hb2' : (⟨b, hb⟩ : H) ^ 2 = 1 := Subtype.ext hb2
        have hab := congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩ ha2' hb2' haU hbU)
        refine ⟨H.mul_mem ha hb, ?_, ?_⟩
        · have hc : Commute a b := hab
          rw [hc.mul_pow, ha2, hb2, mul_one]
        · have : (⟨a * b, H.mul_mem ha hb⟩ : H) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
          rw [this, map_mul]
          exact Ub.mul_mem haU hbU
      one_mem' := ⟨H.one_mem, one_pow 2, by
        have : (⟨1, H.one_mem⟩ : H) = 1 := rfl
        rw [this, map_one]
        exact Ub.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha2, haU⟩
        refine ⟨H.inv_mem ha, by rw [inv_pow, ha2, inv_one], ?_⟩
        have : (⟨a⁻¹, H.inv_mem ha⟩ : H) = (⟨a, ha⟩ : H)⁻¹ := rfl
        rw [this, map_inv]
        exact Ub.inv_mem haU }
  have hT2 : IsPGroup 2 T := fun g => by
    obtain ⟨hg, hg2, -⟩ := g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hg2
  have hT1 : T ≠ ⊥ := by
    obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU1
    obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective N (u : StatedProj H)
    have hg₀' : π g₀ = u := hg₀
    have hu2 : (u : StatedProj H) ^ 2 = 1 := hU.2 u u.2
    have hg₀2 : π (g₀ ^ 2) = 1 := by rw [map_pow, hg₀']; exact hu2
    set g : H := g₀ ^ 3 with hgdef
    have hgsq : g ^ 2 = 1 := by
      have : g ^ 2 = (g₀ ^ 2) ^ 3 := by rw [hgdef, ← pow_mul, ← pow_mul, mul_comm]
      rw [this]
      exact hcube' _ hg₀2
    have hπg : π g = u := by
      rw [hgdef, map_pow, hg₀', pow_succ, hu2, one_mul]
    have hgT : (g : GL (Fin 3) F) ∈ T := by
      refine ⟨g.2, ?_, ?_⟩
      · rw [← SubgroupClass.coe_pow, hgsq]; rfl
      · have : (⟨(g : GL (Fin 3) F), g.2⟩ : H) = g := rfl
        rw [this, hπg]
        exact u.2
    refine (Subgroup.ne_bot_iff_exists_ne_one).mpr ⟨⟨(g : GL (Fin 3) F), hgT⟩, ?_⟩
    intro h
    have hg1 : g = 1 := Subtype.ext (congrArg (fun z : T => (z : GL (Fin 3) F)) h)
    apply hu1
    apply Subtype.ext
    rw [← hπg, hg1, map_one]
    rfl
  have hn' : ∀ g ∈ T, (y₀ : GL (Fin 3) F)⁻¹ * g * y₀ ∈ T := by
    rintro g ⟨hg, hg2, hgU⟩
    have hy : (y₀ : GL (Fin 3) F) ∈ H := y₀.2
    refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hy) hg) hy, ?_, ?_⟩
    · calc ((y₀ : GL (Fin 3) F)⁻¹ * g * y₀) ^ 2
          = (y₀ : GL (Fin 3) F)⁻¹ * g ^ 2 * y₀ := by rw [sq, sq]; group
        _ = 1 := by rw [hg2]; group
    · have : (⟨(y₀ : GL (Fin 3) F)⁻¹ * g * y₀, H.mul_mem (H.mul_mem (H.inv_mem hy) hg) hy⟩ : H) =
          y₀⁻¹ * ⟨g, hg⟩ * y₀ := rfl
      rw [this, map_mul, map_mul, map_inv, hπy₀]
      have hxn3 : (x ^ 3)⁻¹ ∈ Subgroup.normalizer (Ub : Set (StatedProj H)) :=
        Subgroup.inv_mem _ (Subgroup.pow_mem _ hxn 3)
      have := (Subgroup.mem_normalizer_iff.mp hxn3 (π ⟨g, hg⟩)).mp hgU
      simpa using this
  exact dvd_two_pow_sub_one_of_normalizes hq hm hℓ hℓ2 hT2 hT1
    (y := (y₀ : GL (Fin 3) F)) (fun h => hy₀1 (Subtype.ext h))
    (by rw [← SubgroupClass.coe_pow, hy₀ℓ]; rfl) hn'

theorem dvd_of_normalizes_psl3 {m : ℕ} (hq : Nat.card F = 2 ^ m) (hm : 1 ≤ m) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) {x : StatedProj (StatedSL 3 F)}
    (hx : orderOf x = ℓ) {Ub : Subgroup (StatedProj (StatedSL 3 F))} (hU1 : Ub ≠ ⊥)
    (hU : IsElemAbelian 2 Ub)
    (hxn : x ∈ Subgroup.normalizer (Ub : Set (StatedProj (StatedSL 3 F)))) :
    ℓ ∣ 2 ^ (2 * m) - 1 :=
  dvd_of_normalizes_proj (fun _ hg => det_eq_one_of_mem_sl hg) hq hm hℓ hℓ2 hℓ3 hx hU1 hU hxn

end PSL3

section Torus

variable {F : Type} [Field F] [Finite F]

theorem two_le_pRank_psl3_of_ne_three {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≠ 3)
    (hdvd : p ∣ Nat.card F - 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL 3 F))) := by
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rw [Nat.card_units]; exact hdvd)
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hp.out.one_lt.ne hζ
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have hpow (j : Fin 3) : torusDiag (torusVec ζ j 2) ^ p = 1 := by
    rw [← map_pow, torusVec_pow, ← hζ, pow_orderOf_eq_one, torusVec_one, map_one]
  have hent {d d' : Fin 3 → Fˣ} (h : torusDiag d = torusDiag d') (i : Fin 3) : d i = d' i :=
    congrFun (torusDiag_injective h) i
  refine two_le_pRank_statedProj (H := StatedSL 3 F) (x := torusDiag (torusVec ζ 0 2))
    (y := torusDiag (torusVec ζ 1 2)) (torusDiag_mem_SL (prod_torusVec ζ _ _))
    (torusDiag_mem_SL (prod_torusVec ζ _ _)) (hpow 0) (hpow 1)
    ((Commute.all _ _).map torusDiag) ?_ ?_
  · rintro ⟨c, hc⟩
    rw [scalar_eq_torusDiag] at hc
    have e0 := hent hc 0
    have e1 := hent hc 1
    rw [torusVec_apply_left ζ h02] at e0
    rw [torusVec_apply_of_ne ζ h01.symm h12] at e1
    exact hζ1 (e0.symm.trans e1)
  · rintro n c ⟨c', rfl⟩ h
    rw [← map_pow, torusVec_pow, scalar_eq_torusDiag, ← map_mul] at h
    have e0 := hent h 0
    have e1 := hent h 1
    have e2 := hent h 2
    simp only [Pi.mul_apply, torusVec_apply_left _ h02, torusVec_apply_right _ h02,
      torusVec_apply_of_ne _ h01.symm h12, torusVec_apply_of_ne _ h01 h02,
      torusVec_apply_right _ h12, torusVec_apply_left _ h12, one_mul] at e0 e1 e2
    rw [e1] at e0 e2
    have hn1 : ζ ^ n = ζ⁻¹ := eq_inv_of_mul_eq_one_left e0
    rw [hn1, inv_inv] at e2
    have h3 : ζ ^ 3 = 1 := by
      calc ζ ^ 3 = (ζ * ζ) * ζ := by simp only [pow_succ, pow_zero, one_mul]
        _ = ζ⁻¹ * ζ := by rw [e2]
        _ = 1 := inv_mul_cancel ζ
    have hd3 : p ∣ 3 := hζ ▸ orderOf_dvd_of_pow_eq_one h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp hd3)

theorem hasElemAb_nine_psl_three_of_dvd (h : 3 ∣ Nat.card F - 1) :
    HasElemAb 3 9 (StatedProj (StatedSL 3 F)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rw [Nat.card_units]; exact h)
  have h3 : ((ω : Fˣ) : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
  have h1 : ((ω : Fˣ) : F) ≠ 1 := by
    intro h
    have : ω = 1 := Units.ext h
    rw [this, orderOf_one] at hω
    omega
  refine hasElemAb_nine_statedProj (x := tGL ((ω : Fˣ) : F) h3) (y := pGL)
    (Subgroup.subset_closure (det_tMat h3)) (Subgroup.subset_closure det_pMat)
    (tGL_pow_three _ _) pGL_pow_three
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2), ⟨ω ^ 2, rfl⟩, tGL_mul_pGL ω h3⟩
    (tGL_not_scalar ω h3 h1) (fun n c hc => by
      obtain ⟨u, rfl⟩ := hc
      exact tGL_pow_mul_scalar_ne _ h3 n u)

theorem two_le_pRank_psl3 {p : ℕ} [hp : Fact p.Prime] (hdvd : p ∣ Nat.card F - 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL 3 F))) := by
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨A, hA, hc⟩ := hasElemAb_nine_psl_three_of_dvd hdvd
    exact le_pRank hp.out.one_lt le_top hA (k := 2) (by rw [hc]; norm_num)
  · exact two_le_pRank_psl3_of_ne_three hp3 hdvd

end Torus

section Interface

theorem mem_normalizer_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {x : X} {U : Subgroup X}
    (h : x ∈ Subgroup.normalizer (U : Set X)) :
    e x ∈ Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro y
  obtain ⟨y', rfl⟩ := e.surjective y
  have hmem : ∀ z : X, e z ∈ (U.map e.toMonoidHom : Subgroup Y) ↔ z ∈ U := fun z =>
    ⟨fun hz => by
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
      exact (e.injective hwz) ▸ hw, fun hz => Subgroup.mem_map.mpr ⟨z, hz, rfl⟩⟩
  rw [hmem y', ← map_inv, ← map_mul, ← map_mul, hmem]
  exact h y'

theorem exists_prime_pRank_psl3 {X : Type} [Group X] [Finite X] {m n : ℕ} (hm : 1 ≤ m) (hn : 2 ≤ n)
    (hX : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
      Nonempty (X ≃* StatedProj (StatedSL 3 F)))
    (hnorm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ (2 * n) - 1 →
      ∃ (x : X) (Ub : Subgroup X), orderOf x = ℓ ∧ Ub ≠ ⊥ ∧ IsElemAbelian 2 Ub ∧
        x ∈ Subgroup.normalizer (Ub : Set X)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hX
  obtain ⟨ℓ, hℓ, hℓ3, hℓd⟩ := exists_prime_ne_three_dvd hn
  have hℓ2 : ℓ ≠ 2 := ne_two_of_dvd_two_pow_sub_one (by omega) hℓd
  obtain ⟨x, Ub, hx, hU1, hU, hxn⟩ := hnorm ℓ hℓ hℓd
  have hd : ℓ ∣ 2 ^ (2 * m) - 1 :=
    dvd_of_normalizes_psl3 hF hm hℓ hℓ2 hℓ3 (x := e x) (Ub := Ub.map e.toMonoidHom)
      (by rw [MulEquiv.orderOf_eq]; exact hx)
      (fun h => hU1 ((Subgroup.map_eq_bot_iff_of_injective Ub e.injective).mp h))
      (isElemAbelian_map hU e.toMonoidHom) (mem_normalizer_map e hxn)
  have hg := two_le_gcd_sq (by omega : 0 < n) hℓ hℓ3 hℓd hd
  obtain ⟨p, hp, hpd⟩ := exists_prime_dvd_of_two_le hg
  refine ⟨p, hp, hpd.trans (pow_sub_one_dvd (Nat.gcd_dvd_left n m)), ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hpm : p ∣ Nat.card F - 1 := by
    rw [hF]
    exact hpd.trans (pow_sub_one_dvd (Nat.gcd_dvd_right n m))
  rw [pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact two_le_pRank_psl3 hpm

end Interface




end CFSG.QuasithinUnique.Lin2.OddRank
