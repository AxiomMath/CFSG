module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.TypeBound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverCentral
public import CFSG.LieType.Chevalley.ExactNormalFormE

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CoxeterSystem
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_of_isPElt {x y : ↥(e6Data_valid.minGroup K)} (hx : IsPElt 2 x) (hy : IsPElt 2 y)
    (h : Isogeny.e6IsogenyT K x = Isogeny.e6IsogenyT K y) : x = y := by
  have hker : x * y⁻¹ ∈ (Isogeny.e6IsogenyT K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have hz := Isogeny.ker_e6IsogenyT_le_center K hker
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  set z := x * y⁻¹ with hzdef
  have hxz : x = z * y := by rw [hzdef]; group
  have hc : Commute z y := (Subgroup.mem_center_iff.1 hz y).symm
  have hN : z ^ (2 ^ (a + b)) = 1 := by
    have h1 : x ^ (2 ^ (a + b)) = 1 := by
      rw [pow_add, pow_mul, ha, one_pow]
    have h2 : y ^ (2 ^ (a + b)) = 1 := by
      rw [add_comm, pow_add, pow_mul, hb, one_pow]
    have h3 : x ^ (2 ^ (a + b)) = z ^ (2 ^ (a + b)) * y ^ (2 ^ (a + b)) := by
      rw [hxz]; exact hc.mul_pow _
    rw [h3, h2, mul_one] at h1
    exact h1
  have hz1 : z = 1 :=
    (e6CoverData K).cover.eq_one_of_isPElt hker ⟨a + b, hN⟩
  rw [hxz, hz1, one_mul]

theorem isPElt_map (N : MulAut ↥(e6Data_valid.minGroup K)) {x : ↥(e6Data_valid.minGroup K)}
    (hx : IsPElt 2 x) : IsPElt 2 (N x) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

theorem pi_xm (i : N6) (c : K) :
    Isogeny.e6IsogenyT K (e6Data_valid.xm K (Pi.single i 1) c) = adjX .E6 K i c :=
  Subtype.ext (coe_e6IsogenyT_xm_single i c)

theorem pi_ym (i : N6) (c : K) :
    Isogeny.e6IsogenyT K (e6Data_valid.xm K (-Pi.single i 1) c) = adjY .E6 K i c :=
  Subtype.ext (coe_e6IsogenyT_xm_neg_single i c)

section Hat

variable (a : N6 → Kˣ) (σ : K ≃+* K) (ε : ℕ) (N : MulAut ↥(e6Data_valid.minGroup K))
  (hπ : ∀ x, Isogeny.e6IsogenyT K (N x) =
    exactNormalAut .E6 K a σ ε (Isogeny.e6IsogenyT K x))

include hπ

theorem hat_x (i : N6) (c : K) :
    N (e6Data_valid.xm K (Pi.single i 1) c) =
      e6Data_valid.xm K (Pi.single (exactPerm .E6 ε i) 1) ((a (exactPerm .E6 ε i) : K) * σ c) := by
  apply eq_of_isPElt (isPElt_map N (isPElt_xm _ _)) (isPElt_xm _ _)
  rw [hπ, pi_xm, exactNormalAut_adjX, pi_xm]

theorem hat_y (i : N6) (c : K) :
    N (e6Data_valid.xm K (-Pi.single i 1) c) =
      e6Data_valid.xm K (-Pi.single (exactPerm .E6 ε i) 1)
        ((((a (exactPerm .E6 ε i))⁻¹ : Kˣ) : K) * σ c) := by
  apply eq_of_isPElt (isPElt_map N (isPElt_xm _ _)) (isPElt_xm _ _)
  rw [hπ, pi_ym, exactNormalAut_adjY, pi_ym]

@[expose] def sU (σ : K ≃+* K) (u : Kˣ) : Kˣ := Units.map σ.toRingHom.toMonoidHom u

theorem hat_nt (i : N6) (t : Kˣ) :
    N (e6Data_valid.nt K i t) =
      e6Data_valid.nt K (exactPerm .E6 ε i) (a (exactPerm .E6 ε i) * sU σ t) := by
  unfold MinData.Valid.nt
  rw [map_mul, map_mul, hat_x a σ ε N hπ, hat_y a σ ε N hπ]
  have e1 : ((a (exactPerm .E6 ε i) * sU σ t : Kˣ) : K) = (a (exactPerm .E6 ε i) : K) * σ t := rfl
  have e2 : -((((a (exactPerm .E6 ε i) * sU σ t)⁻¹ : Kˣ)) : K) =
      (((a (exactPerm .E6 ε i))⁻¹ : Kˣ) : K) * σ (-(((t⁻¹ : Kˣ)) : K)) := by
    rw [mul_inv, Units.val_mul, map_neg]
    have : (((sU σ t)⁻¹ : Kˣ) : K) = σ (((t⁻¹ : Kˣ)) : K) := rfl
    rw [this]; ring
  rw [e1, e2]

theorem hat_hm (i : N6) (t : Kˣ) :
    N (e6Data_valid.hm K i t) = e6Data_valid.hm K (exactPerm .E6 ε i) (sU σ t) := by
  have hh : ∀ (j : N6) (u : Kˣ), e6Data_valid.hm K j u =
      e6Data_valid.nt K j u * (e6Data_valid.nt K j 1)⁻¹ := fun _ _ => rfl
  rw [hh i t, map_mul, map_inv, hat_nt a σ ε N hπ, hat_nt a σ ε N hπ]
  have e1 : sU σ (1 : Kˣ) = 1 := map_one (Units.map σ.toRingHom.toMonoidHom)
  rw [e1, mul_one, e6Data_valid.nt_eq_hm_mul K, e6Data_valid.nt_eq_hm_mul K]
  have e2 : (e6Data_valid.hm K (exactPerm .E6 ε i) (a (exactPerm .E6 ε i) * sU σ t) *
      e6Data_valid.nm K (exactPerm .E6 ε i)) *
        (e6Data_valid.hm K (exactPerm .E6 ε i) (a (exactPerm .E6 ε i)) *
          e6Data_valid.nm K (exactPerm .E6 ε i))⁻¹ =
      e6Data_valid.hm K (exactPerm .E6 ε i) (a (exactPerm .E6 ε i) * sU σ t) *
        (e6Data_valid.hm K (exactPerm .E6 ε i) (a (exactPerm .E6 ε i)))⁻¹ := by group
  rw [e2, hm_inv, ← e6Data_valid.hm_mul]
  simp

end Hat

theorem N_mem_U (a : N6 → Kˣ) (σ : K ≃+* K) (ε : ℕ) (y : ↥(adjointGroup .E6 K))
    (hy : (y : ModGL .E6 K) ∈ posUnipotent .E6 K) :
    ((exactNormalAut .E6 K a σ ε y : ↥(adjointGroup .E6 K)) : ModGL .E6 K) ∈
      posUnipotent .E6 K := by
  rw [coe_exactNormalAut, ← exactNormalAutGL_apply,
    ← map_exactNormalAutGL (τ := .E6) (K := K) a σ ε (Or.inr (Or.inl rfl))]
  exact Subgroup.mem_map_of_mem _ hy

section Preserve

variable (a : N6 → Kˣ) (σ : K ≃+* K) (ε : ℕ) (N : MulAut ↥(e6Data_valid.minGroup K))
  (hπ : ∀ x, Isogeny.e6IsogenyT K (N x) =
    exactNormalAut .E6 K a σ ε (Isogeny.e6IsogenyT K x))

include hπ

theorem hat_mem_H {h : ↥(e6Data_valid.minGroup K)} (hh : h ∈ (e6CoverData K).datum.H) :
    N h ∈ (e6CoverData K).datum.H := by
  obtain ⟨t, ht, z, hz, rfl⟩ := exists_torus_mul_center hh
  rw [map_mul]
  have hNt : N t ∈ ⨆ i, e6Data_valid.torus K i := by
    refine Subgroup.iSup_induction _ (C := fun t => N t ∈ ⨆ i, e6Data_valid.torus K i) ht
      (fun i t hti => ?_) (by rw [map_one]; exact one_mem _) (fun x y hx hy => ?_)
    · obtain ⟨u, rfl⟩ := (e6Data_valid.mem_torus K).1 hti
      rw [hat_hm a σ ε N hπ]
      exact Subgroup.mem_iSup_of_mem _ (e6Data_valid.hm_mem_torus K _ _)
    · rw [map_mul]; exact mul_mem hx hy
  have hle : (⨆ i, e6Data_valid.torus K i) ≤ (e6CoverData K).datum.H := by
    refine iSup_le fun i => ?_
    rintro _ ⟨u, rfl⟩
    exact e6_hm_mem_H i u
  have hNz : N z ∈ (Isogeny.e6IsogenyT K).ker := by
    have hc : N z ∈ Subgroup.center ↥(e6Data_valid.minGroup K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := Subgroup.mem_center_iff.1 hz (N.symm g)
      calc g * N z = N (N.symm g * z) := by simp
        _ = N (z * N.symm g) := by rw [this]
        _ = N z * g := by simp
    exact (CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := K)).ge hc
  exact mul_mem (hle hNt) (ker_le_comap_H _ hNz)

theorem hat_mem_U {x : ↥(e6Data_valid.minGroup K)} (hx : x ∈ (e6CoverData K).lU) :
    N x ∈ (e6CoverData K).lU := by
  refine ⟨?_, isPElt_map N hx.2⟩
  have h1 : ((Isogeny.e6Isogeny K x : ↥(adjointGroup .E6 K)) : ModGL .E6 K) ∈
      posUnipotent .E6 K := hx.1
  have h2 := N_mem_U a σ ε (Isogeny.e6Isogeny K x) h1
  have h3 : Isogeny.e6IsogenyT K (N x) =
      exactNormalAut .E6 K a σ ε (Isogeny.e6Isogeny K x) := hπ x
  show ((Isogeny.e6Isogeny K (N x) : ↥(adjointGroup .E6 K)) : ModGL .E6 K) ∈ posUnipotent .E6 K
  rw [show Isogeny.e6Isogeny K (N x) = Isogeny.e6IsogenyT K (N x) from rfl, h3]
  exact h2

end Preserve

theorem hm_mul_nm_comm (j : N6) (b : Kˣ) :
    e6Data_valid.hm K j b * e6Data_valid.nm K j = e6Data_valid.nm K j * e6Data_valid.hm K j b⁻¹ := by
  have h := e6Data_valid.nm_conj_hm K j j b⁻¹
  rw [nm_inv, Tag.cartan_self] at h
  have e : b⁻¹ ^ (-(2 : ℤ)) = b ^ 2 := by
    rw [zpow_neg, zpow_ofNat, inv_pow, inv_inv]
  rw [e, ← e6Data_valid.hm_mul] at h
  have e2 : b⁻¹ * b ^ 2 = b := by group
  rw [e2] at h
  calc e6Data_valid.hm K j b * e6Data_valid.nm K j
      = (e6Data_valid.nm K j * e6Data_valid.hm K j b⁻¹ * e6Data_valid.nm K j) *
        e6Data_valid.nm K j := by rw [h]
    _ = e6Data_valid.nm K j * e6Data_valid.hm K j b⁻¹ *
        (e6Data_valid.nm K j * e6Data_valid.nm K j) := by group
    _ = _ := by rw [nm_mul_nm, mul_one]

section Main

variable {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem outer_type {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J)
    (a : N6 → Kˣ) (σ : K ≃+* K) (ε : ℕ) (N : MulAut ↥(e6Data_valid.minGroup K))
    (hπ : ∀ x, Isogeny.e6IsogenyT K (N x) =
      exactNormalAut .E6 K a σ ε (Isogeny.e6IsogenyT K x))
    (B : V ≃ₗ[k] V) (hB : ∀ x v, ρ (N x) (B v) = B (ρ x v)) :
    (∀ (i : N6) (u : Kˣ), χ (e6Data_valid.hm K (exactPerm .E6 ε i) (sU σ u)) =
        χ (e6Data_valid.hm K i u)) ∧
      ∀ i : N6, i ∈ J ↔ exactPerm .E6 ε i ∈ J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (e6Cover_split k)
  set ρ' : Representation k ↥(e6Data_valid.minGroup K) V := ρ.comp N.toMonoidHom with hρ'
  have hρ'a : ∀ x v, ρ' x v = ρ (N x) v := fun _ _ => rfl
  have hρ's : IsSimpleRep ρ' := by
    refine ⟨hρ.1, fun W hW => ?_⟩
    have hW' : ∀ g : ↥(e6Data_valid.minGroup K), ∀ w ∈ W.comap B.toLinearMap,
        ρ g w ∈ W.comap B.toLinearMap := by
      intro g w hw
      show B (ρ g w) ∈ W
      rw [← hB]
      exact hW g _ hw
    have hm := Submodule.map_comap_eq_of_surjective B.surjective W
    rcases hρ.2 (W.comap B.toLinearMap) hW' with h | h
    · left; rw [← hm, h]; simp
    · right; rw [← hm, h]; simp
  let j : N6 → N6 := fun s => exactPerm .E6 ε s
  let χ' : ↥(e6Data_valid.minGroup K) → k := fun h => χ (N h)
  let J' : Finset N6 := Finset.univ.filter fun s => j s ∈ J
  have hfix1 : y ∈ (e6CoverData K).datum.fixU ρ' := fun x hx => by
    rw [hρ'a]; exact ht.1 _ (hat_mem_U a σ ε N hπ hx)
  have hchar1 : ∀ h ∈ (e6CoverData K).datum.H, ρ' h y = χ' h • y := fun h hh => by
    rw [hρ'a]; exact ht.2.2.1 _ (hat_mem_H a σ ε N hπ hh)
  have hχne : ∀ s u, χ (e6Data_valid.hm K s u) ≠ 0 := by
    intro s u h0
    have h1 := hμ.chi_mul (e6_hm_mem_H s u) (e6_hm_mem_H s u⁻¹)
    rw [← e6Data_valid.hm_mul, mul_inv_cancel, e6Data_valid.hm_one, hμ.chi_one, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hsU : Function.Bijective (sU σ) := by
    refine ⟨fun u v h => ?_, fun u => ⟨sU σ.symm u, ?_⟩⟩
    · exact Units.ext (σ.injective (congrArg Units.val h))
    · exact Units.ext (σ.apply_symm_apply (u : K))
  have hT : ∀ s, (e6CoverData K).datum.heckeT ρ' s y =
      χ (e6Data_valid.hm K (j s) (a (j s))⁻¹) • (e6CoverData K).datum.heckeT ρ (j s) y := by
    intro s
    have hbij : Function.Bijective (fun c : K => (a (j s) : K) * σ c) := by
      refine ⟨fun c d h => σ.injective (mul_left_cancel₀ (a (j s)).ne_zero h), fun d => ?_⟩
      refine ⟨σ.symm ((((a (j s))⁻¹ : Kˣ) : K) * d), ?_⟩
      show (a (j s) : K) * σ (σ.symm ((((a (j s))⁻¹ : Kˣ) : K) * d)) = d
      rw [σ.apply_symm_apply, ← mul_assoc, Units.mul_inv, one_mul]
    refine ((e6CoverRankOne K).heckeT_datum ρ' s y).trans ?_
    refine Eq.trans ?_ (congrArg (fun v => χ (e6Data_valid.hm K (j s) (a (j s))⁻¹) • v)
      ((e6CoverRankOne K).heckeT_datum ρ (j s) y).symm)
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.ofBijective _ hbij) _ _ fun c => ?_
    show ρ' ((e6CoverRankOne K).x s c * (e6CoverData K).nhat s) y =
      χ (e6Data_valid.hm K (j s) (a (j s))⁻¹) •
        ρ ((e6CoverRankOne K).x (j s) ((a (j s) : K) * σ c) * (e6CoverData K).nhat (j s)) y
    have hn1 : (e6CoverData K).nhat s = e6Data_valid.nm K s := nhat_e6 s
    have hn2 : (e6CoverData K).nhat (j s) = e6Data_valid.nm K (j s) := nhat_e6 (j s)
    rw [hn1, hn2, hρ'a, map_mul]
    have hNm : N (e6Data_valid.nm K s) = e6Data_valid.hm K (j s) (a (j s)) *
        e6Data_valid.nm K (j s) := by
      have h1 : e6Data_valid.nm K s = e6Data_valid.nt K s 1 := rfl
      have h2 := hat_nt a σ ε N hπ s 1
      have e1 : sU σ (1 : Kˣ) = 1 := map_one (Units.map σ.toRingHom.toMonoidHom)
      rw [h1, h2, e1, mul_one, e6Data_valid.nt_eq_hm_mul K]
    have hx : N ((e6CoverRankOne K).x s c) =
        (e6CoverRankOne K).x (j s) ((a (j s) : K) * σ c) := hat_x a σ ε N hπ s c
    rw [hNm, hx, hm_mul_nm_comm, ← mul_assoc, map_mul, Module.End.mul_apply,
      ht.2.2.1 _ (e6_hm_mem_H (j s) (a (j s))⁻¹), map_smul]
  have hJ' : ∀ s, s ∈ J' ↔ (∀ u : Kˣ, χ' (e6Data_valid.hm K s u) = 1) ∧
      (e6CoverData K).datum.heckeT ρ' s y = 0 := by
    intro s
    have hc0 : χ (e6Data_valid.hm K (j s) (a (j s))⁻¹) ≠ 0 := hχne _ _
    have hχs : ∀ u, χ' (e6Data_valid.hm K s u) = χ (e6Data_valid.hm K (j s) (sU σ u)) := by
      intro u; exact congrArg χ (hat_hm a σ ε N hπ s u)
    have hk : (∀ u : Kˣ, χ (e6Data_valid.hm K (j s) (sU σ u)) = 1) ↔
        ∀ u : Kˣ, χ (e6Data_valid.hm K (j s) u) = 1 :=
      ⟨fun h u => by obtain ⟨v, rfl⟩ := hsU.2 u; exact h v, fun h u => h _⟩
    have hjt := ht.2.2.2 (j s)
    have hmemJ' : s ∈ J' ↔ j s ∈ J := by
      simp only [J', Finset.mem_filter, Finset.mem_univ, true_and]
    refine hmemJ'.trans (hjt.trans (and_congr ?_ ?_))
    · simp only [hχs]; exact hk.symm
    · rw [hT s, smul_eq_zero]; simp [hc0]
  have ht1 : IsCoverType (e6CoverRankOne K) ρ' y χ' J' := ⟨hfix1, ht.2.1, hchar1, hJ'⟩
  have ht2 : IsCoverType (e6CoverRankOne K) ρ' (B y) χ J := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [hρ'a, hB]
      exact congrArg B (ht.1 _ (hat_mem_U a σ ε N hπ hx |> fun _ => hx))
    · intro h0
      exact ht.2.1 (B.injective (by rw [h0, map_zero]))
    · intro h hh
      rw [hρ'a, hB, ht.2.2.1 h hh, map_smul]
    · intro s
      rw [ht.2.2.2 s]
      have hTB : (e6CoverData K).datum.heckeT ρ' s (B y) =
          B ((e6CoverData K).datum.heckeT ρ s y) := by
        refine ((e6CoverRankOne K).heckeT_datum ρ' s _).trans ?_
        refine Eq.trans ?_ (congrArg B ((e6CoverRankOne K).heckeT_datum ρ s y).symm)
        rw [map_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hρ'a, hB]
      rw [hTB]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2, map_zero]⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, B.injective (by rw [h2, map_zero])⟩
  obtain ⟨hχeq, hJeq⟩ := e6_isCoverType_unique hρ's ht1 ht2
  refine ⟨fun i u => ?_, fun i => ?_⟩
  · have h1 := hχeq (e6Data_valid.hm K i u) (e6_hm_mem_H i u)
    have h2 : χ' (e6Data_valid.hm K i u) = χ (e6Data_valid.hm K (j i) (sU σ u)) :=
      congrArg χ (hat_hm a σ ε N hπ i u)
    rw [h2] at h1
    exact h1
  · have := Finset.ext_iff.1 hJeq i
    simp only [J', Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.symm

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
