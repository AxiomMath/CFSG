module

public import CFSG.LieType.Steinberg.TwistedE6.Weyl
public import CFSG.LieType.Steinberg.Minuscule.RankOne
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.CurtisTits MinData.Valid

variable {k : Type*} [Field k] (θ : k →+* k)

variable (k) in
@[expose] def slFixed : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k) :=
  MonoidHom.eqLocus (Matrix.SpecialLinearGroup.map θ) (MonoidHom.id _)

theorem mem_slFixed {M : Matrix.SpecialLinearGroup (Fin 2) k} :
    M ∈ slFixed k θ ↔
      ∀ p q, θ ((M : Matrix (Fin 2) (Fin 2) k) p q) = (M : Matrix (Fin 2) (Fin 2) k) p q := by
  constructor
  · intro h p q
    exact congrArg (fun N : Matrix.SpecialLinearGroup (Fin 2) k =>
      (N : Matrix (Fin 2) (Fin 2) k) p q) h
  · intro h
    refine Subtype.ext ?_
    ext p q
    exact h p q

theorem slUpper_mem {c : k} (hc : θ c = c) : slUpper k c ∈ slFixed k θ := by
  rw [mem_slFixed, slUpper_val]
  intro p q
  fin_cases p <;> fin_cases q <;> simp [hc]

theorem slLower_mem {c : k} (hc : θ c = c) : slLower k c ∈ slFixed k θ := by
  rw [mem_slFixed, slLower_val]
  intro p q
  fin_cases p <;> fin_cases q <;> simp [hc]

omit θ in
theorem sl_eq_of_lower_eq_zero' (M : Matrix.SpecialLinearGroup (Fin 2) k)
    (h : (M : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) (h0 : (M : Matrix (Fin 2) (Fin 2) k) 0 0 ≠ 0) :
    (M : Matrix (Fin 2) (Fin 2) k) =
      !![((Units.mk0 _ h0 : kˣ) : k), 0; 0, (((Units.mk0 _ h0)⁻¹ : kˣ) : k)] *
        !![1, (M : Matrix (Fin 2) (Fin 2) k) 0 1 / (M : Matrix (Fin 2) (Fin 2) k) 0 0; 0, 1] := by
  have hdet := M.det_coe
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  have h11 : (M : Matrix (Fin 2) (Fin 2) k) 1 1 = ((M : Matrix (Fin 2) (Fin 2) k) 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdet
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h, h11, mul_div_cancel₀ _ h0]

omit θ in
theorem sl_eq_of_lower_ne_zero' (M : Matrix.SpecialLinearGroup (Fin 2) k)
    (h : (M : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0) :
    (M : Matrix (Fin 2) (Fin 2) k) =
      !![1, (M : Matrix (Fin 2) (Fin 2) k) 0 0 / (M : Matrix (Fin 2) (Fin 2) k) 1 0; 0, 1] *
        !![0, 1; -1, 0] *
        !![((Units.mk0 _ (neg_ne_zero.2 h) : kˣ) : k), 0;
          0, (((Units.mk0 _ (neg_ne_zero.2 h))⁻¹ : kˣ) : k)] *
        !![1, (M : Matrix (Fin 2) (Fin 2) k) 1 1 / (M : Matrix (Fin 2) (Fin 2) k) 1 0; 0, 1] := by
  have hdet := M.det_coe
  rw [Matrix.det_fin_two] at hdet
  ext x y
  fin_cases x <;> fin_cases y <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
  · field_simp
    linear_combination -hdet
  · field_simp

theorem exists_sl_of_mem_rankOne_fixed {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a)
    {g : fixedGroup k θ} (hg : g ∈ rankOne (twistedRootGroup k θ) (orbitMap a)) :
    ∃ M ∈ slFixed k θ, e6Data_valid.endo k g = e6Data_valid.blockOp k a M := by
  let S : Subgroup (e6Data_valid.minGroup k) :=
    ((e6Data_valid.slHom k a).comp (slFixed k θ).subtype).range.comap
      (e6Data_valid.minGroup k).subtype
  have h1 : rho (Pi.single a 1) = Pi.single a 1 := by rw [rho_single, ha]
  have h2 : rho (-Pi.single a 1) = -Pi.single a 1 := by rw [rho_neg_single, ha]
  have hS : rankOne (twistedRootGroup k θ) (orbitMap a) ≤ S.comap (fixedGroup k θ).subtype := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [← proj_single] at hx
      obtain ⟨c, hc, hxc⟩ :=
        (mem_twistedRootGroup_iff_of_fixed θ (isRoot_single _ a) rfl h1 x).1 hx
      refine ⟨⟨slUpper k c, slUpper_mem θ hc⟩, Units.ext ?_⟩
      change ((e6Data_valid.slHom k a (slUpper k c) : (Module.End k (Fin e6Data.d →₀ k))ˣ) :
        Module.End k (Fin e6Data.d →₀ k)) = e6Data_valid.endo k (x : e6Data_valid.minGroup k)
      rw [hxc, slHom_val, slUpper_val, e6Data_valid.blockOp_upper, e6Data_valid.endo_xm]
    · intro x hx
      rw [← proj_neg_single] at hx
      obtain ⟨c, hc, hxc⟩ :=
        (mem_twistedRootGroup_iff_of_fixed θ (isRoot_neg_single _ a) rfl h2 x).1 hx
      refine ⟨⟨slLower k c, slLower_mem θ hc⟩, Units.ext ?_⟩
      change ((e6Data_valid.slHom k a (slLower k c) : (Module.End k (Fin e6Data.d →₀ k))ˣ) :
        Module.End k (Fin e6Data.d →₀ k)) = e6Data_valid.endo k (x : e6Data_valid.minGroup k)
      rw [hxc, slHom_val, slLower_val, e6Data_valid.blockOp_lower, e6Data_valid.endo_xm]
  obtain ⟨⟨M, hM⟩, hMg⟩ := hS hg
  refine ⟨M, hM, ?_⟩
  rw [← slHom_val]
  exact (congrArg Units.val hMg).symm

theorem bruhat_fixed (hθ : ∀ c, θ (θ c) = c) {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a)
    {i : Fin (Tag.rank .F4)} (hi : orbitMap a = i) (hn : nHatE k i = e6Data_valid.nm k a)
    (hH : hHatE k θ i = (hFixE θ a).range) {g : fixedGroup k θ}
    (hg : g ∈ rankOne (twistedRootGroup k θ) i) :
    (∃ h ∈ hHat k θ i, ∃ u ∈ twistedRootGroup k θ (Pi.single i 1), g = h * u) ∨
      ∃ u ∈ twistedRootGroup k θ (Pi.single i 1), ∃ h ∈ hHat k θ i,
        ∃ v ∈ twistedRootGroup k θ (Pi.single i 1), g = u * nHat θ i * h * v := by
  subst hi
  obtain ⟨M, hM, hgM⟩ := exists_sl_of_mem_rankOne_fixed θ ha hg
  have hfix := (mem_slFixed θ).1 hM
  have hU : ∀ c, θ c = c → ∃ u ∈ twistedRootGroup k θ (Pi.single (orbitMap a) 1),
      (u : e6Data_valid.minGroup k) = e6Data_valid.xm k (Pi.single a 1) c := fun c hc => by
    have h1 : rho (Pi.single a 1) = Pi.single a 1 := by rw [rho_single, ha]
    have hmem := xFixed_mem θ (isRoot_single _ a) h1 c hc
    rw [proj_single] at hmem
    exact ⟨_, hmem, rfl⟩
  have hT : ∀ t : kˣ, θ (t : k) = t → ∃ h ∈ hHat k θ (orbitMap a),
      (h : e6Data_valid.minGroup k) = e6Data_valid.hm k a t := fun t ht => by
    have hmem : e6Data_valid.hm k a t ∈ hHatE k θ (orbitMap a) := by
      rw [hH]
      exact ⟨⟨t, (mem_fixedUnits θ).2 ht⟩, rfl⟩
    refine ⟨⟨_, hHatE_le_fixedGroup θ hθ _ hmem⟩, ?_, rfl⟩
    rw [hHat, Subgroup.mem_subgroupOf]
    exact hmem
  by_cases h0 : (M : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · left
    have hdet := M.det_coe
    rw [Matrix.det_fin_two, h0, mul_zero, sub_zero] at hdet
    have h00 : (M : Matrix (Fin 2) (Fin 2) k) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    obtain ⟨h, hh, hhv⟩ := hT (Units.mk0 _ h00) (by rw [Units.val_mk0]; exact hfix 0 0)
    obtain ⟨u, hu, huv⟩ := hU ((M : Matrix (Fin 2) (Fin 2) k) 0 1 /
      (M : Matrix (Fin 2) (Fin 2) k) 0 0) (by rw [map_div₀, hfix, hfix])
    refine ⟨h, hh, u, hu, Subtype.ext (e6Data_valid.endo_injective k ?_)⟩
    rw [hgM, sl_eq_of_lower_eq_zero' M h0 h00, e6Data_valid.blockOp_mul,
      e6Data_valid.blockOp_diag, e6Data_valid.blockOp_upper, Subgroup.coe_mul,
      e6Data_valid.endo_mul, hhv, huv, e6Data_valid.endo_hm, e6Data_valid.endo_xm]
  · right
    have hγ : -(M : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := neg_ne_zero.2 h0
    obtain ⟨u, hu, huv⟩ := hU ((M : Matrix (Fin 2) (Fin 2) k) 0 0 /
      (M : Matrix (Fin 2) (Fin 2) k) 1 0) (by rw [map_div₀, hfix, hfix])
    obtain ⟨h, hh, hhv⟩ := hT (Units.mk0 _ hγ) (by rw [Units.val_mk0, map_neg, hfix])
    obtain ⟨v, hv, hvv⟩ := hU ((M : Matrix (Fin 2) (Fin 2) k) 1 1 /
      (M : Matrix (Fin 2) (Fin 2) k) 1 0) (by rw [map_div₀, hfix, hfix])
    refine ⟨u, hu, h, hh, v, hv, Subtype.ext (e6Data_valid.endo_injective k ?_)⟩
    rw [hgM, sl_eq_of_lower_ne_zero' M h0, e6Data_valid.blockOp_mul, e6Data_valid.blockOp_mul,
      e6Data_valid.blockOp_mul, e6Data_valid.blockOp_diag, e6Data_valid.blockOp_upper,
      e6Data_valid.blockOp_upper, e6Data_valid.blockOp_weyl, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_mul, e6Data_valid.endo_mul, e6Data_valid.endo_mul, e6Data_valid.endo_mul, huv,
      hhv, hvv, nHat_val, hn, e6Data_valid.endo_hm, e6Data_valid.endo_xm, e6Data_valid.endo_xm,
      e6Data_valid.endo_nm]

theorem eq_zero_of_conj_xm (a : Fin (Tag.rank .E6)) {c s : k}
    (h : e6Data_valid.xm k (Pi.single a 1) c * e6Data_valid.xm k (-Pi.single a 1) 1 *
      (e6Data_valid.xm k (Pi.single a 1) c)⁻¹ = e6Data_valid.xm k (-Pi.single a 1) s) :
    c = 0 := by
  have he := congrArg (e6Data_valid.endo k) h
  simp only [e6Data_valid.endo_mul, e6Data_valid.xm_neg, e6Data_valid.endo_xm] at he
  rw [← e6Data_valid.blockOp_lower, ← e6Data_valid.blockOp_upper, ← e6Data_valid.blockOp_upper,
    ← e6Data_valid.blockOp_lower, ← e6Data_valid.blockOp_mul, ← e6Data_valid.blockOp_mul] at he
  have he' := congrFun (congrFun (e6Data_valid.blockOp_injective k a he) 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at he'
  exact he'

theorem eq_one_of_mem_normalizer_fixed {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a)
    {i : Fin (Tag.rank .F4)} (hi : orbitMap a = i) {u : fixedGroup k θ}
    (hu : u ∈ twistedRootGroup k θ (Pi.single i 1))
    (hn : u ∈ Subgroup.normalizer
      (twistedRootGroup k θ (-Pi.single i 1) : Set (fixedGroup k θ))) :
    u = 1 := by
  subst hi
  have h1 : rho (Pi.single a 1) = Pi.single a 1 := by rw [rho_single, ha]
  have h2 : rho (-Pi.single a 1) = -Pi.single a 1 := by rw [rho_neg_single, ha]
  rw [← proj_single] at hu
  obtain ⟨c, -, huc⟩ := (mem_twistedRootGroup_iff_of_fixed θ (isRoot_single _ a) rfl h1 u).1 hu
  have hy := xFixed_mem θ (isRoot_neg_single _ a) h2 1 (map_one θ)
  rw [proj_neg_single] at hy
  have hmem := (hn _).1 hy
  rw [← proj_neg_single] at hmem
  obtain ⟨s, -, hs⟩ :=
    (mem_twistedRootGroup_iff_of_fixed θ (isRoot_neg_single _ a) rfl h2 _).1 hmem
  have h' : e6Data_valid.xm k (Pi.single a 1) c * e6Data_valid.xm k (-Pi.single a 1) 1 *
      (e6Data_valid.xm k (Pi.single a 1) c)⁻¹ = e6Data_valid.xm k (-Pi.single a 1) s := by
    rw [← huc]
    exact hs
  have hc0 := eq_zero_of_conj_xm a h'
  refine Subtype.ext ?_
  rw [huc, hc0, e6Data_valid.xm_zero]
  rfl

theorem commute_rankOne_orbit {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {x y : e6Data_valid.minGroup k}
    (hx : x ∈ rankOne (e6Data_valid.rootGroup k) a)
    (hy : y ∈ rankOne (e6Data_valid.rootGroup k) b) : Commute x y := by
  have key := fun (s s' : ℤ) (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) (c d : k) =>
    commute_xm_orbit (k := k) hab hs hs' c d
  have pp := key 1 1 (Or.inl rfl) (Or.inl rfl)
  have pn := key 1 (-1) (Or.inl rfl) (Or.inr rfl)
  have np := key (-1) 1 (Or.inr rfl) (Or.inl rfl)
  have nn := key (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  simp only [one_smul, neg_one_smul] at pp pn np nn
  have cen : ∀ {γ δ : Fin (Tag.rank .E6) → ℤ},
      (∀ c d : k, Commute (e6Data_valid.xm k δ c) (e6Data_valid.xm k γ d)) →
      e6Data_valid.rootGroup k γ ≤
        Subgroup.centralizer (e6Data_valid.rootGroup k δ : Set (e6Data_valid.minGroup k)) := by
    intro γ δ h z hz
    obtain ⟨d, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hw
    exact (h c d).eq
  have hle : rankOne (e6Data_valid.rootGroup k) a ≤ Subgroup.centralizer
      (rankOne (e6Data_valid.rootGroup k) b : Set (e6Data_valid.minGroup k)) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le (cen pp) (cen pn)
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le (cen np) (cen nn)
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

theorem sigma_mem_rankOne {a : Fin (Tag.rank .E6)} {x : e6Data_valid.minGroup k}
    (hx : x ∈ rankOne (e6Data_valid.rootGroup k) a) :
    sigma k θ x ∈ rankOne (e6Data_valid.rootGroup k) (rhoPerm a) := by
  have hle : rankOne (e6Data_valid.rootGroup k) a ≤
      (rankOne (e6Data_valid.rootGroup k) (rhoPerm a)).comap (sigma k θ) := by
    refine sup_le ?_ ?_
    · intro z hz
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hz
      rw [Subgroup.mem_comap, sigma_xm_single]
      exact Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup k _ _)
    · intro z hz
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hz
      rw [Subgroup.mem_comap, sigma_xm_neg_single]
      exact Subgroup.mem_sup_right (e6Data_valid.xm_mem_rootGroup k _ _)
  exact hle hx

theorem rhoPerm_of_orbit {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) : rhoPerm a = b := by
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

@[expose] def phiOrbit {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) :
    rankOne (e6Data_valid.rootGroup k) a →* e6Data_valid.minGroup k where
  toFun y := y * sigma k θ y
  map_one' := by rw [OneMemClass.coe_one, map_one, mul_one]
  map_mul' y y' := by
    have hc : Commute (y' : e6Data_valid.minGroup k) (sigma k θ y) :=
      commute_rankOne_orbit hab y'.2 (rhoPerm_of_orbit hab ▸ sigma_mem_rankOne θ y.2)
    rw [Subgroup.coe_mul, map_mul]
    calc (y : e6Data_valid.minGroup k) * y' * (sigma k θ y * sigma k θ y') =
        y * (y' * sigma k θ y) * sigma k θ y' := by group
      _ = y * (sigma k θ y * y') * sigma k θ y' := by rw [hc.eq]
      _ = _ := by group

theorem phiOrbit_apply {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5))
    (y : rankOne (e6Data_valid.rootGroup k) a) :
    phiOrbit θ hab y = (y : e6Data_valid.minGroup k) * sigma k θ y := rfl

theorem bruhat_pair (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {i : Fin (Tag.rank .F4)}
    (hi : orbitMap a = i) (hn : nHatE k i = e6Data_valid.nm k a * e6Data_valid.nm k b)
    (hH : hHatE k θ i = (hPairE θ a b).range) {g : fixedGroup k θ}
    (hg : g ∈ rankOne (twistedRootGroup k θ) i) :
    (∃ h ∈ hHat k θ i, ∃ u ∈ twistedRootGroup k θ (Pi.single i 1), g = h * u) ∨
      ∃ u ∈ twistedRootGroup k θ (Pi.single i 1), ∃ h ∈ hHat k θ i,
        ∃ v ∈ twistedRootGroup k θ (Pi.single i 1), g = u * nHat θ i * h * v := by
  subst hi
  have hρ := rhoPerm_of_orbit hab
  have hne1 : rho (Pi.single a 1) ≠ Pi.single a 1 := by
    rw [rho_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hne2 : rho (-Pi.single a 1) ≠ -Pi.single a 1 := by
    rw [rho_neg_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hmemU : ∀ c : k, e6Data_valid.xm k (Pi.single a 1) c ∈
      rankOne (e6Data_valid.rootGroup k) a := fun c =>
    Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup k _ _)
  have hrange : rankOne (twistedRootGroup k θ) (orbitMap a) ≤
      (phiOrbit θ hab).range.comap (fixedGroup k θ).subtype := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [← proj_single] at hx
      obtain ⟨c, hc⟩ :=
        (mem_twistedRootGroup_iff_of_pair θ (isRoot_single _ a) rfl hne1 x).1 hx
      refine ⟨⟨_, hmemU c⟩, ?_⟩
      rw [phiOrbit_apply, Subgroup.coe_subtype, hc, sigma_xm_single, rho_single,
        twistSign_single, Int.cast_one, one_mul]
    · intro x hx
      rw [← proj_neg_single] at hx
      obtain ⟨c, hc⟩ :=
        (mem_twistedRootGroup_iff_of_pair θ (isRoot_neg_single _ a) rfl hne2 x).1 hx
      refine ⟨⟨_, Subgroup.mem_sup_right (e6Data_valid.xm_mem_rootGroup k _ c)⟩, ?_⟩
      rw [phiOrbit_apply, Subgroup.coe_subtype, hc, sigma_xm_neg_single, rho_neg_single,
        twistSign_neg_single, Int.cast_one, one_mul]
  obtain ⟨y, hy⟩ := hrange hg
  rw [Subgroup.coe_subtype] at hy
  have hU : ∀ c : k, ∃ u ∈ twistedRootGroup k θ (Pi.single (orbitMap a) 1),
      (u : e6Data_valid.minGroup k) = phiOrbit θ hab ⟨_, hmemU c⟩ := fun c => by
    have hmem := xPair_mem θ hθ (isRoot_single _ a) hne1 c
    rw [proj_single] at hmem
    refine ⟨_, hmem, ?_⟩
    rw [xPair_val, phiOrbit_apply, sigma_xm_single, rho_single, twistSign_single, Int.cast_one,
      one_mul]
  have hT : ∀ t : kˣ, ∃ h ∈ hHat k θ (orbitMap a), (h : e6Data_valid.minGroup k) =
      phiOrbit θ hab ⟨_, e6Data_valid.torus_le_rankOne k a (e6Data_valid.hm_mem_torus k a t)⟩ :=
    fun t => by
      have hmem : e6Data_valid.hm k a t * e6Data_valid.hm k b (Units.map (θ : k →* k) t) ∈
          hHatE k θ (orbitMap a) := by
        rw [hH]
        exact ⟨t, rfl⟩
      refine ⟨⟨_, hHatE_le_fixedGroup θ hθ _ hmem⟩, ?_, ?_⟩
      · rw [hHat, Subgroup.mem_subgroupOf]
        exact hmem
      · rw [phiOrbit_apply, sigma_hm, hρ]
  have hN : (nHat θ (orbitMap a) : e6Data_valid.minGroup k) =
      phiOrbit θ hab ⟨_, e6Data_valid.nm_mem_rankOne k a⟩ := by
    rw [nHat_val, hn, phiOrbit_apply, sigma_nm, hρ]
  rcases e6Data_valid.bruhat k a y.2 with ⟨h, hh, u, hu, he⟩ | ⟨u, hu, h, hh, v, hv, he⟩
  · left
    obtain ⟨t, rfl⟩ := (e6Data_valid.mem_torus k).1 hh
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hu
    obtain ⟨h', hh', hh'v⟩ := hT t
    obtain ⟨u', hu', hu'v⟩ := hU c
    refine ⟨h', hh', u', hu', Subtype.ext ?_⟩
    rw [← hy, Subgroup.coe_mul, hh'v, hu'v, ← map_mul]
    congr 1
    exact Subtype.ext he
  · right
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hu
    obtain ⟨t, rfl⟩ := (e6Data_valid.mem_torus k).1 hh
    obtain ⟨d, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hv
    obtain ⟨u', hu', hu'v⟩ := hU c
    obtain ⟨h', hh', hh'v⟩ := hT t
    obtain ⟨v', hv', hv'v⟩ := hU d
    refine ⟨u', hu', h', hh', v', hv', Subtype.ext ?_⟩
    rw [← hy, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, hu'v,
      hh'v, hv'v, hN, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext he

theorem endo_single_of_mem_rankOne {b : Fin (Tag.rank .E6)} {w : Fin e6Data.d}
    (hw : e6Data.wt w b = 0) {x : e6Data_valid.minGroup k}
    (hx : x ∈ rankOne (e6Data_valid.rootGroup k) b) :
    e6Data_valid.endo k x (Finsupp.single w 1) = Finsupp.single w 1 := by
  obtain ⟨M, hM⟩ := e6Data_valid.exists_of_mem_rankOne k b hx
  rw [hM, e6Data_valid.blockOp_single_of_eq_zero k hw]

theorem blockOp_single_apply_self {a : Fin (Tag.rank .E6)} {w : Fin e6Data.d}
    (hw : e6Data.wt w a = 1) (M : Matrix (Fin 2) (Fin 2) k) :
    e6Data_valid.blockOp k a M (Finsupp.single w 1) w = M 0 0 := by
  have hne : e6Data_valid.sRefl a w ≠ w := e6Data_valid.sRefl_ne_self (by omega)
  rw [e6Data_valid.blockOp_single_of_eq_one k hw]
  simp [hne]

theorem eq_one_of_mem_normalizer_pair (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {i : Fin (Tag.rank .F4)}
    (hi : orbitMap a = i) {u : fixedGroup k θ}
    (hu : u ∈ twistedRootGroup k θ (Pi.single i 1))
    (hn : u ∈ Subgroup.normalizer
      (twistedRootGroup k θ (-Pi.single i 1) : Set (fixedGroup k θ))) :
    u = 1 := by
  subst hi
  have hρ := rhoPerm_of_orbit hab
  have hne1 : rho (Pi.single a 1) ≠ Pi.single a 1 := by
    rw [rho_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hne2 : rho (-Pi.single a 1) ≠ -Pi.single a 1 := by
    rw [rho_neg_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain ⟨w, hwa, hwb⟩ : ∃ w : Fin e6Data.d, e6Data.wt w a = 1 ∧ e6Data.wt w b = 0 := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨1, by decide⟩, by decide, by decide⟩
    · exact ⟨⟨0, by decide⟩, by decide, by decide⟩
  rw [← proj_single] at hu
  obtain ⟨c, hc⟩ := (mem_twistedRootGroup_iff_of_pair θ (isRoot_single _ a) rfl hne1 u).1 hu
  have hy := xPair_mem θ hθ (isRoot_neg_single _ a) hne2 1
  rw [proj_neg_single] at hy
  have hmem := (hn _).1 hy
  rw [← proj_neg_single] at hmem
  obtain ⟨s, hs⟩ := (mem_twistedRootGroup_iff_of_pair θ (isRoot_neg_single _ a) rfl hne2 _).1 hmem
  let φ := phiOrbit θ hab
  let A : rankOne (e6Data_valid.rootGroup k) a :=
    ⟨_, Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup k (Pi.single a 1) c)⟩
  let A' : rankOne (e6Data_valid.rootGroup k) a :=
    ⟨_, Subgroup.mem_sup_right (e6Data_valid.xm_mem_rootGroup k (-Pi.single a 1) 1)⟩
  let W : rankOne (e6Data_valid.rootGroup k) a :=
    ⟨_, Subgroup.mem_sup_right (e6Data_valid.xm_mem_rootGroup k (-Pi.single a 1) s)⟩
  have hA : (u : e6Data_valid.minGroup k) = φ A := by
    rw [hc, phiOrbit_apply, sigma_xm_single, rho_single, twistSign_single, Int.cast_one, one_mul]
  have hA' : (xPair θ hθ (isRoot_neg_single _ a) hne2 1 : e6Data_valid.minGroup k) = φ A' := by
    rw [xPair_val, phiOrbit_apply, sigma_xm_neg_single, rho_neg_single, twistSign_neg_single,
      Int.cast_one, one_mul]
  have hW : ((u * xPair θ hθ (isRoot_neg_single _ a) hne2 1 * u⁻¹ : fixedGroup k θ) :
      e6Data_valid.minGroup k) = φ W := by
    rw [hs, phiOrbit_apply, sigma_xm_neg_single, rho_neg_single, twistSign_neg_single,
      Int.cast_one, one_mul]
  have key : φ (A * A' * A⁻¹) = φ W := by
    rw [map_mul, map_mul, map_inv, ← hA, ← hA', ← hW]
    rfl
  rw [phiOrbit_apply, phiOrbit_apply] at key
  have hσ : ∀ z : rankOne (e6Data_valid.rootGroup k) a,
      e6Data_valid.endo k (sigma k θ z) (Finsupp.single w 1) = Finsupp.single w 1 := fun z =>
    endo_single_of_mem_rankOne hwb (hρ ▸ sigma_mem_rankOne θ z.2)
  have e := congrArg (fun x => e6Data_valid.endo k x (Finsupp.single w 1)) key
  simp only [e6Data_valid.endo_mul, Module.End.mul_apply, hσ] at e
  have eA : e6Data_valid.endo k ((A * A' * A⁻¹ : rankOne (e6Data_valid.rootGroup k) a) :
      e6Data_valid.minGroup k) = e6Data_valid.blockOp k a (!![1, c; 0, 1] * !![1, 0; 1, 1] *
        !![1, -c; 0, 1]) := by
    rw [e6Data_valid.blockOp_mul, e6Data_valid.blockOp_mul, e6Data_valid.blockOp_upper,
      e6Data_valid.blockOp_lower, e6Data_valid.blockOp_upper]
    change e6Data_valid.endo k (e6Data_valid.xm k (Pi.single a 1) c *
      e6Data_valid.xm k (-Pi.single a 1) 1 * (e6Data_valid.xm k (Pi.single a 1) c)⁻¹) = _
    rw [e6Data_valid.xm_neg, e6Data_valid.endo_mul, e6Data_valid.endo_mul, e6Data_valid.endo_xm,
      e6Data_valid.endo_xm, e6Data_valid.endo_xm]
  have eW : e6Data_valid.endo k (W : e6Data_valid.minGroup k) =
      e6Data_valid.blockOp k a !![1, 0; s, 1] := by
    rw [e6Data_valid.blockOp_lower]
    exact e6Data_valid.endo_xm k _ s
  rw [eA, eW] at e
  have e' := congrArg (fun v => v w) e
  simp only [blockOp_single_apply_self hwa] at e'
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e'
  refine Subtype.ext ?_
  rw [hc, e', map_zero, mul_zero, e6Data_valid.xm_zero, e6Data_valid.xm_zero, mul_one]
  rfl

end CFSG.LieType.Steinberg.TwistedE6
