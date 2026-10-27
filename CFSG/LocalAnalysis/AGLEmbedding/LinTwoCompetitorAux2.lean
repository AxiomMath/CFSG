module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section Image

variable {G : Type} [Group G] {Y : Type*} [Group Y]

theorem nclIn_map_eq {H' J X : Subgroup G} (f : H' →* Y) (hXJ : X ≤ J) (hJH' : J ≤ H')
    (hJ : nclIn J X = J) :
    nclIn ((J.subgroupOf H').map f) ((X.subgroupOf H').map f) = (J.subgroupOf H').map f := by
  set Jt := (J.subgroupOf H').map f
  set Xt := (X.subgroupOf H').map f
  have hXtJt : Xt ≤ Jt := Subgroup.map_mono (Subgroup.comap_mono hXJ)
  refine le_antisymm (nclIn_le_self Jt Xt) ?_
  set W : Subgroup H' := (nclIn Jt Xt).comap f
  have hJW : J ≤ Subgroup.normalizer ((W.map H'.subtype : Subgroup G) : Set G) := by
    have h1 : J.subgroupOf H' ≤ Subgroup.normalizer (W : Set H') :=
      (show J.subgroupOf H' ≤ (Subgroup.normalizer (nclIn Jt Xt : Set Y)).comap f from
        fun j hj => le_normalizer_nclIn Jt Xt (Subgroup.mem_map_of_mem f hj)).trans
        (Subgroup.le_normalizer_comap f)
    have h2 := (Subgroup.map_mono (f := H'.subtype) h1).trans
      (Subgroup.le_normalizer_map H'.subtype)
    rwa [Subgroup.map_subgroupOf_eq_of_le hJH'] at h2
  have hXV : X ≤ J ⊓ W.map H'.subtype := le_inf hXJ fun x hx =>
    ⟨⟨x, hJH' (hXJ hx)⟩, le_nclIn hXtJt (Subgroup.mem_map_of_mem f
      (show (⟨x, hJH' (hXJ hx)⟩ : H') ∈ X.subgroupOf H' from hx)), rfl⟩
  have hJV : J ≤ J ⊓ W.map H'.subtype := by
    have hle := nclIn_le hXV inf_le_left
      ((le_inf Subgroup.le_normalizer hJW).trans Subgroup.inf_normalizer_le_normalizer_inf)
    rwa [hJ] at hle
  rintro _ ⟨j, hj, rfl⟩
  obtain ⟨w, hw, hwj⟩ := (hJV hj).2
  rw [← Subtype.ext hwj]
  exact hw

theorem map_le_normalizer_map {H' J A : Subgroup G} (f : H' →* Y) (hJH' : J ≤ H')
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    (A.subgroupOf H').map f ≤
      Subgroup.normalizer (((J.subgroupOf H').map f : Subgroup Y) : Set Y) :=
  (Subgroup.map_mono ((Subgroup.comap_mono hAJ).trans
    (Subgroup.subgroupOf_normalizer_eq hJH').le)).trans (Subgroup.le_normalizer_map f)

theorem exists_surjective_comp_eq {A B L : Type*} [Group A] [Group B] [Group L] (ρ : A →* B)
    (hρ : Function.Surjective ρ) (ψ : A →* L) (hψ : Function.Surjective ψ)
    (hker : ρ.ker ≤ ψ.ker) :
    ∃ φ : B →* L, (∀ a, φ (ρ a) = ψ a) ∧ Function.Surjective φ ∧ φ.ker = ψ.ker.map ρ := by
  set φ : B →* L := ρ.liftOfSurjective hρ ⟨ψ, hker⟩
  have hφ : ∀ a, φ (ρ a) = ψ a := fun a =>
    MonoidHom.liftOfRightInverse_comp_apply ρ _ (Function.rightInverse_surjInv hρ) ⟨ψ, hker⟩ a
  refine ⟨φ, hφ, fun l => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := hψ l
    exact ⟨ρ a, hφ a⟩
  · ext b
    constructor
    · intro hb
      obtain ⟨a, rfl⟩ := hρ b
      exact ⟨a, MonoidHom.mem_ker.mpr ((hφ a).symm.trans (MonoidHom.mem_ker.mp hb)), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact MonoidHom.mem_ker.mpr ((hφ a).trans (MonoidHom.mem_ker.mp ha))

end Image

section Competitor

variable {G : Type} [Group G] {p : ℕ}

theorem exists_competitorHom_of_map_nclIn_eq [Finite G] {H X : Subgroup G} {Y : Type*} [Group Y]
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hπJ : ((nclIn H X).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      K) (e : K ≃* Y) {H' : Subgroup G} (hJH' : nclIn H X ≤ H') :
    ∃ φ : ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) →*
        Y,
      Function.Surjective φ ∧ p.Coprime (Nat.card φ.ker) ∧
      (∀ j : H', (j : G) ∈ nclIn H X →
        (QuotientGroup.mk' (primeComplementCore (G := H') p) j ∈
            φ.ker.map (((nclIn H X).subgroupOf H').map
              (QuotientGroup.mk' (primeComplementCore (G := H') p))).subtype ↔
          (j : G) ∈ GLBPrimeCore p H)) ∧
      ∀ (j : H') (hj : j ∈ (nclIn H X).subgroupOf H'),
        ((e.symm (φ ⟨QuotientGroup.mk' (primeComplementCore (G := H') p) j,
            Subgroup.mem_map_of_mem _ hj⟩) : K) : H ⧸ primeComplementCore (G := H) p) =
          QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H X hj⟩ := by
  have hJH : nclIn H X ≤ H := nclIn_le_self H X
  set ρ := (QuotientGroup.mk' (primeComplementCore (G := H') p)).subgroupMap
    ((nclIn H X).subgroupOf H')
  let θ₀ : (nclIn H X).subgroupOf H' →* H :=
    MonoidHom.codRestrict (H'.subtype.comp ((nclIn H X).subgroupOf H').subtype) H
      (fun a => hJH a.2)
  let θ : (nclIn H X).subgroupOf H' →* H ⧸ primeComplementCore (G := H) p :=
    (QuotientGroup.mk' (primeComplementCore (G := H) p)).comp θ₀
  have hθK : ∀ a, θ a ∈ K := fun a =>
    hπJ ▸ Subgroup.mem_map_of_mem _ (show θ₀ a ∈ (nclIn H X).subgroupOf H from a.2)
  let ψ : (nclIn H X).subgroupOf H' →* Y := e.toMonoidHom.comp (θ.codRestrict K hθK)
  have hψker : ∀ a, a ∈ ψ.ker ↔ ((a : H') : G) ∈ GLBPrimeCore p H := by
    intro a
    have h1 : ψ a = 1 ↔ θ a = 1 := by
      simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff]
      rw [← OneMemClass.coe_eq_one, MonoidHom.codRestrict_apply]
    rw [MonoidHom.mem_ker, h1]
    exact mk'_primeComplementCore_eq_one_iff p (θ₀ a)
  have hψ : Function.Surjective ψ := by
    intro l
    obtain ⟨j, hj, hjl⟩ : ((e.symm l : K) : H ⧸ primeComplementCore (G := H) p) ∈
        ((nclIn H X).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
      hπJ.symm ▸ (e.symm l).2
    refine ⟨⟨⟨(j : G), hJH' hj⟩, hj⟩, ?_⟩
    have h1 : θ.codRestrict K hθK ⟨⟨(j : G), hJH' hj⟩, hj⟩ = e.symm l := Subtype.ext hjl
    simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, h1, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
  have hker : ρ.ker ≤ ψ.ker := by
    intro a ha
    have ha' : ((a : H') : G) ∈ GLBPrimeCore p H' := by
      rw [← mk'_primeComplementCore_eq_one_iff]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
    have hN := inf_glbPrimeCore_le_glbPrimeCore p hJH' ⟨a.2, ha'⟩
    rw [glbPrimeCore_nclIn] at hN
    exact (hψker a).mpr hN.2
  obtain ⟨φ, hφ, hφs, hφker⟩ := exists_surjective_comp_eq ρ
    ((QuotientGroup.mk' _).subgroupMap_surjective _) ψ hψ hker
  refine ⟨φ, hφs, ?_, fun j hj => ⟨fun hmem => ?_, fun hN => ?_⟩, fun j hj => ?_⟩
  ·
    have hι : Function.Injective (H'.subtype.comp ((nclIn H X).subgroupOf H').subtype) :=
      H'.subtype_injective.comp (Subgroup.subtype_injective _)
    refine Nat.Coprime.coprime_dvd_right ?_ ((glbPrimeCore_coprime p H).coprime_dvd_right
      (Subgroup.card_dvd_of_le (H := ψ.ker.map (H'.subtype.comp
        ((nclIn H X).subgroupOf H').subtype)) ?_))
    · rw [hφker, Subgroup.card_map_of_injective hι]
      exact Subgroup.card_map_dvd _ _
    · rintro _ ⟨a, ha, rfl⟩
      exact (hψker a).mp ha
  · obtain ⟨y, hy, hyj⟩ := hmem
    have hya : y = ρ ⟨j, hj⟩ := Subtype.ext hyj
    rw [hya] at hy
    exact (hψker ⟨j, hj⟩).mp (MonoidHom.mem_ker.mpr ((hφ _).symm.trans (MonoidHom.mem_ker.mp hy)))
  · exact ⟨ρ ⟨j, hj⟩, MonoidHom.mem_ker.mpr ((hφ _).trans
      (MonoidHom.mem_ker.mp ((hψker ⟨j, hj⟩).mpr hN))), rfl⟩
  ·
    rw [show (⟨QuotientGroup.mk' (primeComplementCore (G := H') p) j,
      Subgroup.mem_map_of_mem _ hj⟩ : ((nclIn H X).subgroupOf H').map
        (QuotientGroup.mk' (primeComplementCore (G := H') p))) = ρ ⟨j, hj⟩ from rfl, hφ]
    simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, MonoidHom.codRestrict_apply]
    rfl

theorem faithful_of_mem_ker_iff_of {H R X : Subgroup G} (hRH : R ≤ H)
    (hcomm : ∀ {r : G}, r ∈ R →
      (∀ j ∈ nclIn H X, r * j * r⁻¹ * j⁻¹ ∈ GLBPrimeCore p H) → r = 1)
    {Y : Type*} [Group Y] {H' : Subgroup G} (hJH' : nclIn H X ≤ H')
    {φ : ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) →*
      Y}
    (hker : ∀ j : H', (j : G) ∈ nclIn H X →
      (QuotientGroup.mk' (primeComplementCore (G := H') p) j ∈
          φ.ker.map (((nclIn H X).subgroupOf H').map
            (QuotientGroup.mk' (primeComplementCore (G := H') p))).subtype ↔
        (j : G) ∈ GLBPrimeCore p H)) :
    ∀ z ∈ (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)),
      (∀ y ∈ ((nclIn H X).subgroupOf H').map
          (QuotientGroup.mk' (primeComplementCore (G := H') p)),
        z * y * z⁻¹ * y⁻¹ ∈ φ.ker.map (((nclIn H X).subgroupOf H').map
          (QuotientGroup.mk' (primeComplementCore (G := H') p))).subtype) → z = 1 := by
  rintro _ ⟨r, hr, rfl⟩ hz
  have hrR : (r : G) ∈ R := hr
  have hrH : (r : G) ∈ H := hRH hrR
  suffices hr1 : (r : G) = 1 by
    rw [show r = 1 from Subtype.ext hr1, map_one]
  refine hcomm hrR fun j hj => ?_
  have hcJ : (r : G) * j * (r : G)⁻¹ * j⁻¹ ∈ nclIn H X :=
    (nclIn H X).mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_nclIn H X hrH) j).mp hj)
      ((nclIn H X).inv_mem hj)
  refine (hker (r * ⟨j, hJH' hj⟩ * r⁻¹ * (⟨j, hJH' hj⟩ : H')⁻¹) hcJ).mp ?_
  have hy := hz _ (Subgroup.mem_map_of_mem (QuotientGroup.mk' (primeComplementCore (G := H') p))
    (show (⟨j, hJH' hj⟩ : H') ∈ (nclIn H X).subgroupOf H' from hj))
  rwa [map_mul, map_mul, map_mul, map_inv, map_inv]

theorem map_eq_inf_of_card_eq [Finite G] [Fact p.Prime] {H R X : Subgroup G} (hXR : X ≤ R)
    (hXH : X ≤ H) (hX : IsPGroup p X) {H' : Subgroup G} (hJH' : nclIn H X ≤ H')
    (hcard : Nat.card ((R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) ⊓
        ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) :
      Subgroup (H' ⧸ primeComplementCore (G := H') p)) = Nat.card X) :
    (X.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) =
      (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) ⊓
        ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) := by
  have hp : p.Prime := Fact.out
  have hXH' : X ≤ H' := (le_nclIn hXH).trans hJH'
  have hle : (X.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) ≤
      (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) ⊓
        ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) :=
    le_inf (Subgroup.map_mono (Subgroup.comap_mono hXR))
      (Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hXH)))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hXp : IsPGroup p (X.subgroupOf H') := hX.comap_subtype
  rw [hcard, card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hXp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH').toEquiv]

end Competitor

namespace D1L2Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n : ℕ} {P : Sylow p G}
  {M H R X : Subgroup G}

theorem exists_competitorHom_of_mulEquiv (h : D1L2Config p n P M H R X)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKn : K.Normal) (e : K ≃* PSL2GF p n)
    (hXK : (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K)
    {H' : Subgroup G} (hJH' : nclIn H X ≤ H') :
    ∃ φ : ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) →*
        PSL2GF p n,
      Function.Surjective φ ∧ p.Coprime (Nat.card φ.ker) ∧
      (∀ j : H', (j : G) ∈ nclIn H X →
        (QuotientGroup.mk' (primeComplementCore (G := H') p) j ∈
            φ.ker.map (((nclIn H X).subgroupOf H').map
              (QuotientGroup.mk' (primeComplementCore (G := H') p))).subtype ↔
          (j : G) ∈ GLBPrimeCore p H)) ∧
      ∀ (j : H') (hj : j ∈ (nclIn H X).subgroupOf H'),
        ((e.symm (φ ⟨QuotientGroup.mk' (primeComplementCore (G := H') p) j,
            Subgroup.mem_map_of_mem _ hj⟩) : K) : H ⧸ primeComplementCore (G := H) p) =
          QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H X hj⟩ :=
  exists_competitorHom_of_map_nclIn_eq (h.map_nclIn_eq hKn ⟨e⟩ hXK) e hJH'

theorem exists_competitorHom (h : D1L2Config p n P M H R X) {H' : Subgroup G}
    (hJH' : nclIn H X ≤ H') :
    ∃ φ : ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) →*
        PSL2GF p n,
      Function.Surjective φ ∧ p.Coprime (Nat.card φ.ker) ∧
      ∀ j : H', (j : G) ∈ nclIn H X →
        (QuotientGroup.mk' (primeComplementCore (G := H') p) j ∈
            φ.ker.map (((nclIn H X).subgroupOf H').map
              (QuotientGroup.mk' (primeComplementCore (G := H') p))).subtype ↔
          (j : G) ∈ GLBPrimeCore p H) := by
  obtain ⟨K, hKn, ⟨e⟩, -, hXK⟩ := h.socle
  obtain ⟨φ, hs, hc, hk, -⟩ := h.exists_competitorHom_of_mulEquiv hKn e hXK hJH'
  exact ⟨φ, hs, hc, hk⟩

theorem nclIn_map_eq (h : D1L2Config p n P M H R X) {H' : Subgroup G}
    (hJH' : nclIn H X ≤ H') :
    nclIn (((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)))
        ((X.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p))) =
      ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) :=
  CFSG.AGLEmbedding.nclIn_map_eq _ (le_nclIn h.le_H) hJH' h.nclIn_nclIn

theorem map_le_normalizer_map (h : D1L2Config p n P M H R X) {H' : Subgroup G}
    (hJH' : nclIn H X ≤ H') :
    (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) ≤
      Subgroup.normalizer ((((nclIn H X).subgroupOf H').map
        (QuotientGroup.mk' (primeComplementCore (G := H') p)) : Subgroup _) : Set _) :=
  CFSG.AGLEmbedding.map_le_normalizer_map _ hJH' (h.ext.le_H.trans (le_normalizer_nclIn H X))

theorem faithful_of_mem_ker_iff (h : D1L2Config p n P M H R X) {H' : Subgroup G}
    (hJH' : nclIn H X ≤ H')
    {φ : ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) →*
      PSL2GF p n}
    (hker : ∀ j : H', (j : G) ∈ nclIn H X →
      (QuotientGroup.mk' (primeComplementCore (G := H') p) j ∈
          φ.ker.map (((nclIn H X).subgroupOf H').map
            (QuotientGroup.mk' (primeComplementCore (G := H') p))).subtype ↔
        (j : G) ∈ GLBPrimeCore p H)) :
    ∀ z ∈ (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)),
      (∀ y ∈ ((nclIn H X).subgroupOf H').map
          (QuotientGroup.mk' (primeComplementCore (G := H') p)),
        z * y * z⁻¹ * y⁻¹ ∈ φ.ker.map (((nclIn H X).subgroupOf H').map
          (QuotientGroup.mk' (primeComplementCore (G := H') p))).subtype) → z = 1 :=
  faithful_of_mem_ker_iff_of h.ext.le_H h.eq_one_of_forall_commutator_mem hJH' hker

end D1L2Config

end CFSG.AGLEmbedding
