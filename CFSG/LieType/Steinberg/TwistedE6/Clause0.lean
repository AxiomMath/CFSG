module

public import CFSG.LieType.Steinberg.TwistedE6.Datum
public import CFSG.LieType.Steinberg.TwistedE6.Generation
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras
public import CFSG.LieType.Steinberg.Minuscule.ChevExtras
public import CFSG.LieType.CurtisTits.Perfect
public import CFSG.LieType.TitsSimplicity
public import CFSG.Adapters.SpecialLinearPerfect
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.CurtisTits CFSG.LieType.Universal CFSG.LieType.TitsSimplicity
open MinData.Valid
open scoped commutatorElement

variable {k : Type*} [Field k] (θ : k →+* k)

theorem borel_twisted_le : borel (twistedDatum k θ) (hHat k θ) ≤
    (borel (e6Datum k) (e6Data_valid.torus k)).comap (fixedGroup k θ).subtype := by
  refine sup_le (iSup_le fun i x hx => ?_) fun x hx => ?_
  · have hx' : (x : e6Data_valid.minGroup k) ∈ hHatE k θ i := hx
    exact Subgroup.mem_sup_left (hHatE_le_iSup_torus θ i hx')
  · rw [posUnipotent, twisted_setOf_pos_eq] at hx
    have h := iSup_twistedRootGroup_le θ (fun h => 0 < h) hx
    rw [Subgroup.mem_comap] at h ⊢
    refine Subgroup.mem_sup_right ?_
    rw [posUnipotent, e6Data_valid.setOf_pos_eq isFiniteType_cartan_E6 k]
    exact h

theorem negUnipotent_twisted_le : negUnipotent (twistedDatum k θ) ≤
    (negUnipotent (e6Datum k)).comap (fixedGroup k θ).subtype := by
  intro x hx
  rw [negUnipotent, twisted_setOf_neg_eq] at hx
  have h := iSup_twistedRootGroup_le θ (fun h => h < 0) hx
  rw [Subgroup.mem_comap] at h ⊢
  rw [negUnipotent, e6Data_valid.setOf_neg_eq isFiniteType_cartan_E6 k]
  exact h

theorem twistedDatum_bruhatExtras : BruhatExtras (twistedDatum k θ) (hHat k θ) where
  borel_inf_negUnipotent := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    have h : (g : e6Data_valid.minGroup k) ∈
        borel (e6Datum k) (e6Data_valid.torus k) ⊓ negUnipotent (e6Datum k) :=
      Subgroup.mem_inf.2 ⟨borel_twisted_le θ hg.1, negUnipotent_twisted_le θ hg.2⟩
    rw [(e6Datum_bruhatExtras k).borel_inf_negUnipotent, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)

theorem commute_xm_self (γ : Fin (Tag.rank .E6) → ℤ) (c d : k) :
    Commute (e6Data_valid.xm k γ c) (e6Data_valid.xm k γ d) := by
  change e6Data_valid.xm k γ c * e6Data_valid.xm k γ d =
    e6Data_valid.xm k γ d * e6Data_valid.xm k γ c
  rw [← e6Data_valid.xm_add, ← e6Data_valid.xm_add, add_comm]

theorem commute_of_mem_sup_rootGroup_rho {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    {x y : e6Data_valid.minGroup k}
    (hx : x ∈ e6Data_valid.rootGroup k α ⊔ e6Data_valid.rootGroup k (rho α))
    (hy : y ∈ e6Data_valid.rootGroup k α ⊔ e6Data_valid.rootGroup k (rho α)) : Commute x y := by
  by_cases hfix : rho α = α
  · rw [hfix, sup_idem] at hx hy
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hx
    obtain ⟨d, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hy
    exact commute_xm_self α c d
  · obtain ⟨c, d, rfl⟩ := (mem_sup_rootGroup_of_commute (commute_xm_rho hα hfix)).1 hx
    obtain ⟨c', d', rfl⟩ := (mem_sup_rootGroup_of_commute (commute_xm_rho hα hfix)).1 hy
    exact ((commute_xm_self α c c').mul_right (commute_xm_rho hα hfix c d')).mul_left
      ((commute_xm_rho hα hfix c' d).symm.mul_right (commute_xm_self _ d d'))

theorem twistedDatum_rootGroupCommutators : RootGroupCommutators (twistedDatum k θ) := by
  refine .of_divisible_eq_empty rfl fun β hβ x hx y hy => ?_
  obtain ⟨α, hα, hp⟩ := exists_proj_eq (isRoot_of_mem_twistedDatum_roots θ hβ)
  have hx' := (mem_twistedRootGroup_iff θ hα hp x).1 hx
  have hy' := (mem_twistedRootGroup_iff θ hα hp y).1 hy
  exact Subtype.ext (commute_of_mem_sup_rootGroup_rho hα hx' hy')

theorem twistedRootGroup_fixed_le_commutator {a c : Fin (Tag.rank .E6)} (ha : rhoPerm a = a)
    (hc : rhoPerm c = c) (hac : IsRoot .E6 (Pi.single a 1 + Pi.single c 1))
    {i : Fin (Tag.rank .F4)} (hi : orbitMap a = i) :
    twistedRootGroup k θ (Pi.single i 1) ≤ commutator (fixedGroup k θ) := by
  subst hi
  intro x hx
  have h1 : rho (Pi.single a 1) = Pi.single a 1 := by rw [rho_single, ha]
  rw [← proj_single] at hx
  obtain ⟨u, hu, hxu⟩ :=
    (mem_twistedRootGroup_iff_of_fixed θ (isRoot_single _ a) rfl h1 x).1 hx
  have hδ : IsRoot .E6 (-Pi.single c 1) := isRoot_neg_single _ c
  have hsum : (Pi.single a 1 + Pi.single c 1 + -Pi.single c 1 : Fin (Tag.rank .E6) → ℤ) =
      Pi.single a 1 := add_neg_cancel_right _ _
  have hne : (Pi.single a 1 + Pi.single c 1 + -Pi.single c 1 : Fin (Tag.rank .E6) → ℤ) ≠ 0 := by
    rw [hsum]
    exact (isRoot_single _ a).ne_zero
  have hroot : IsRoot .E6 (Pi.single a 1 + Pi.single c 1 + -Pi.single c 1) := by
    rw [hsum]
    exact isRoot_single _ a
  obtain ⟨σ, hσ, hcomm⟩ := (e6Data_valid.commutator_xm k hac hδ hne).1 hroot
  have hrγ : rho (Pi.single a 1 + Pi.single c 1) = Pi.single a 1 + Pi.single c 1 := by
    change rho (Pi.single a 1) + rho (Pi.single c 1) = _
    rw [rho_single, rho_single, ha, hc]
  have hrδ : rho (-Pi.single c 1) = -Pi.single c 1 := by rw [rho_neg_single, hc]
  have hσθ : θ σ = σ := by rcases hσ with rfl | rfl <;> simp
  let y := xFixed θ hac hrγ (σ * u) (by rw [map_mul, hσθ, hu])
  let z := xFixed θ hδ hrδ 1 (map_one θ)
  have e : x = ⁅y, z⁆ := by
    apply Subtype.ext
    change (x : e6Data_valid.minGroup k) =
      ⁅e6Data_valid.xm k (Pi.single a 1 + Pi.single c 1) (σ * u),
        e6Data_valid.xm k (-Pi.single c 1) 1⁆
    rw [hxu, hcomm, hsum]
    congr 1
    rcases hσ with rfl | rfl <;> ring
  rw [e]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top z)

theorem slHom_mem_rankOne (a : Fin (Tag.rank .E6)) (M : Matrix.SpecialLinearGroup (Fin 2) k) :
    (⟨_, e6Data_valid.slHom_mem k a M⟩ : e6Data_valid.minGroup k) ∈
      rankOne (e6Data_valid.rootGroup k) a := by
  have hX : ∀ c : k, e6Data_valid.xm k (Pi.single a 1) c ∈
      rankOne (e6Data_valid.rootGroup k) a := fun c =>
    Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup k _ _)
  have hH : ∀ t : kˣ, e6Data_valid.hm k a t ∈ rankOne (e6Data_valid.rootGroup k) a := fun t =>
    e6Data_valid.torus_le_rankOne k a (e6Data_valid.hm_mem_torus k a t)
  by_cases h0 : (M : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · obtain ⟨t, c, hc⟩ := sl_eq_of_lower_eq_zero k M h0
    have e : (⟨_, e6Data_valid.slHom_mem k a M⟩ : e6Data_valid.minGroup k) =
        e6Data_valid.hm k a t * e6Data_valid.xm k (Pi.single a 1) c := by
      refine Subtype.ext (Units.ext ?_)
      change _ = e6Data_valid.endo k (e6Data_valid.hm k a t * e6Data_valid.xm k (Pi.single a 1) c)
      rw [slHom_val, hc, e6Data_valid.blockOp_mul, e6Data_valid.blockOp_diag,
        e6Data_valid.blockOp_upper, e6Data_valid.endo_mul, e6Data_valid.endo_hm,
        e6Data_valid.endo_xm]
    rw [e]
    exact mul_mem (hH t) (hX c)
  · obtain ⟨u, t, v, hc⟩ := sl_eq_of_lower_ne_zero k M h0
    have e : (⟨_, e6Data_valid.slHom_mem k a M⟩ : e6Data_valid.minGroup k) =
        e6Data_valid.xm k (Pi.single a 1) u * e6Data_valid.nm k a * e6Data_valid.hm k a t *
          e6Data_valid.xm k (Pi.single a 1) v := by
      refine Subtype.ext (Units.ext ?_)
      change _ = e6Data_valid.endo k (e6Data_valid.xm k (Pi.single a 1) u * e6Data_valid.nm k a *
        e6Data_valid.hm k a t * e6Data_valid.xm k (Pi.single a 1) v)
      rw [slHom_val, hc, e6Data_valid.blockOp_mul, e6Data_valid.blockOp_mul,
        e6Data_valid.blockOp_mul, e6Data_valid.blockOp_diag, e6Data_valid.blockOp_upper,
        e6Data_valid.blockOp_upper, e6Data_valid.blockOp_weyl, e6Data_valid.endo_mul,
        e6Data_valid.endo_mul, e6Data_valid.endo_mul, e6Data_valid.endo_hm, e6Data_valid.endo_xm,
        e6Data_valid.endo_xm, e6Data_valid.endo_nm]
    rw [e]
    exact mul_mem (mul_mem (mul_mem (hX u) (e6Data_valid.nm_mem_rankOne k a)) (hH t)) (hX v)

variable (k) in
@[expose] def slRankOne (a : Fin (Tag.rank .E6)) :
    Matrix.SpecialLinearGroup (Fin 2) k →* rankOne (e6Data_valid.rootGroup k) a :=
  ((e6Data_valid.slHom k a).codRestrict _ (e6Data_valid.slHom_mem k a)).codRestrict _
    (slHom_mem_rankOne a)

theorem slRankOne_upper (a : Fin (Tag.rank .E6)) (c : k) :
    (slRankOne k a (slUpper k c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (Pi.single a 1) c :=
  Subtype.ext (Units.ext (by
    change e6Data_valid.blockOp k a (slUpper k c : Matrix (Fin 2) (Fin 2) k) = _
    rw [slUpper_val, e6Data_valid.blockOp_upper]
    rfl))

theorem phiOrbit_mem_fixedGroup (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5))
    (y : rankOne (e6Data_valid.rootGroup k) a) : phiOrbit θ hab y ∈ fixedGroup k θ := by
  rw [mem_fixedGroup, phiOrbit_apply, map_mul, sigma_sigma θ hθ]
  exact (commute_rankOne_orbit hab y.2
    (rhoPerm_of_orbit hab ▸ sigma_mem_rankOne θ y.2)).eq.symm

@[expose] def slOrbitHom (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) :
    Matrix.SpecialLinearGroup (Fin 2) k →* fixedGroup k θ :=
  ((phiOrbit θ hab).comp (slRankOne k a)).codRestrict _
    fun _ => phiOrbit_mem_fixedGroup θ hθ hab _

theorem slOrbitHom_upper (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) (c : k) :
    (slOrbitHom θ hθ hab (slUpper k c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (Pi.single a 1) c * e6Data_valid.xm k (Pi.single b 1) (θ c) := by
  change phiOrbit θ hab (slRankOne k a (slUpper k c)) = _
  rw [phiOrbit_apply, slRankOne_upper, sigma_xm_single, rhoPerm_of_orbit hab]

theorem twistedRootGroup_pair_le_commutator (hθ : ∀ c, θ (θ c) = c)
    (hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) k)) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {i : Fin (Tag.rank .F4)}
    (hi : orbitMap a = i) :
    twistedRootGroup k θ (Pi.single i 1) ≤ commutator (fixedGroup k θ) := by
  subst hi
  have hρ := rhoPerm_of_orbit hab
  have hne1 : rho (Pi.single a 1) ≠ Pi.single a 1 := by
    rw [rho_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  intro x hx
  rw [← proj_single] at hx
  obtain ⟨c, hc⟩ := (mem_twistedRootGroup_iff_of_pair θ (isRoot_single _ a) rfl hne1 x).1 hx
  have e : x = slOrbitHom θ hθ hab (slUpper k c) := by
    apply Subtype.ext
    rw [slOrbitHom_upper, hc, rho_single, hρ, twistSign_single, Int.cast_one, one_mul]
  have hmem : slUpper k c ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) k) := by
    rw [Group.isPerfect_def.1 hSL]
    exact Subgroup.mem_top _
  have hle : (commutator (Matrix.SpecialLinearGroup (Fin 2) k)).map (slOrbitHom θ hθ hab) ≤
      commutator (fixedGroup k θ) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  rw [e]
  exact hle (Subgroup.mem_map_of_mem _ hmem)

theorem isRoot_single_add_single_one_three :
    IsRoot .E6 (Pi.single (nd 1) 1 + Pi.single (nd 3) 1) := by
  have h := (IsRoot.basis (τ := .E6) (nd 1)).reflect (nd 3)
  rwa [show reflect .E6 (nd 3) (Pi.single (nd 1) 1) = Pi.single (nd 1) 1 + Pi.single (nd 3) 1 by
    decide] at h

theorem isRoot_single_add_single_three_one :
    IsRoot .E6 (Pi.single (nd 3) 1 + Pi.single (nd 1) 1) := by
  rw [add_comm]
  exact isRoot_single_add_single_one_three

theorem twistedRootGroup_single_le_commutator (hθ : ∀ c, θ (θ c) = c)
    (hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) k)) (i : Fin (Tag.rank .F4)) :
    twistedRootGroup k θ (Pi.single i 1) ≤ commutator (fixedGroup k θ) := by
  fin_cases i
  · exact twistedRootGroup_fixed_le_commutator θ (a := nd 1) (c := nd 3) rfl rfl
      isRoot_single_add_single_one_three (i := nf 0) rfl
  · exact twistedRootGroup_fixed_le_commutator θ (a := nd 3) (c := nd 1) rfl rfl
      isRoot_single_add_single_three_one (i := nf 1) rfl
  · exact twistedRootGroup_pair_le_commutator θ hθ hSL (a := nd 2) (b := nd 4)
      (Or.inl ⟨rfl, rfl⟩) (i := nf 2) rfl
  · exact twistedRootGroup_pair_le_commutator θ hθ hSL (a := nd 0) (b := nd 5)
      (Or.inr ⟨rfl, rfl⟩) (i := nf 3) rfl

theorem fixedGroup_isPerfect (hθ : ∀ c, θ (θ c) = c)
    (hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) k)) :
    Group.IsPerfect (fixedGroup k θ) :=
  isPerfect_of_rootGroup_single_le_commutator
    (twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ))
    (twistedDatum_steinbergExtras θ hθ).two_smul_le
    fun i => twistedRootGroup_single_le_commutator θ hθ hSL i

theorem fixedGroup_isPerfect_of_four_le_card (hθ : ∀ c, θ (θ c) = c) [Finite k]
    (hk : 4 ≤ Nat.card k) : Group.IsPerfect (fixedGroup k θ) :=
  fixedGroup_isPerfect θ hθ (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card k hk)

theorem fixedGroup_nontrivial (hθ : ∀ c, θ (θ c) = c) : Nontrivial (fixedGroup k θ) := by
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (twistedRootGroup_ne_bot θ hθ (β := Pi.single (nf 0) 1) (IsRoot.basis _))
  exact nontrivial_of_ne (x : fixedGroup k θ) 1 fun h => hx (Subtype.ext h)

theorem fixedGroup_isQuasisimple (hθ : ∀ c, θ (θ c) = c)
    (hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) k)) :
    IsQuasisimple (fixedGroup k θ) := by
  have := fixedGroup_nontrivial θ hθ
  exact TitsSimplicity.isQuasisimple
    (twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ))
    (twistedDatum_steinbergExtras θ hθ) (twistedDatum_bruhatExtras θ)
    (twistedDatum_rootGroupCommutators θ)
    (by change IsIndecomposable (Tag.cartan .F4); decide +kernel) (fixedGroup_isPerfect θ hθ hSL)

theorem fixedGroup_isQuasisimple_of_four_le_card (hθ : ∀ c, θ (θ c) = c) [Finite k]
    (hk : 4 ≤ Nat.card k) : IsQuasisimple (fixedGroup k θ) :=
  fixedGroup_isQuasisimple θ hθ
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card k hk)

end CFSG.LieType.Steinberg.TwistedE6
