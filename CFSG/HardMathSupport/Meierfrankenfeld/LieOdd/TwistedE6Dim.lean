module

public import CFSG.SignalizerFunctorTheorem.NonLocal.E6Heis
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisRootInj

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SignalizerFunctorTheorem.NonLocal CFSG.SignalizerFunctorTheorem.NonLocalExc

section Prod

variable {k : Type} [Field k] {Γ : Type} [Group Γ] (H : HeisFam Γ (Fin 3) (fun _ => k) k)
  (hadd : ∀ j c d, H.xa j (c + d) = H.xa j c * H.xa j d)

@[expose] def famXa (j : Fin 3) : Multiplicative k →* Γ where
  toFun c := H.xa j c.toAdd
  map_one' := by
    have h := hadd j 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  map_mul' c d := hadd j c.toAdd d.toAdd

@[expose] noncomputable def famProd : Multiplicative (Fin 3 → k) →* Γ :=
  (MonoidHom.noncommPiCoprod (famXa H hadd)
    (by intro s t _ x y; exact H.xa_comm s t x.toAdd y.toAdd)).comp
    (MulEquiv.piMultiplicative (fun _ : Fin 3 => k)).toMonoidHom

theorem famProd_single (j : Fin 3) (d : k) :
    famProd H hadd (Multiplicative.ofAdd (Pi.single j d)) = H.xa j d := by
  have h : (MulEquiv.piMultiplicative (fun _ : Fin 3 => k)).toMonoidHom
      (Multiplicative.ofAdd (Pi.single j d)) = Pi.mulSingle j (Multiplicative.ofAdd d) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp [MulEquiv.piMultiplicative]
    · simp [MulEquiv.piMultiplicative, hi]
  rw [famProd, MonoidHom.comp_apply, h, MonoidHom.noncommPiCoprod_mulSingle]
  rfl

theorem z_comm_famProd (w : k) (u : Fin 3 → k) :
    H.z w * famProd H hadd (Multiplicative.ofAdd u) =
      famProd H hadd (Multiplicative.ofAdd u) * H.z w := by
  have hu : u = ∑ j, Pi.single j (u j) := (Finset.univ_sum_single u).symm
  rw [hu]
  refine Finset.sum_induction _ (fun x => H.z w * famProd H hadd (Multiplicative.ofAdd x) =
      famProd H hadd (Multiplicative.ofAdd x) * H.z w) ?_ ?_ ?_
  · intro x y hx hy
    rw [ofAdd_add, map_mul, ← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  · simp
  · intro j _
    rw [famProd_single]
    exact H.z_comm_a w j _

theorem famProd_conj (η : Fin 3 → k) (he : ∀ j c d, H.e j c d = η j * c * d) (u v : Fin 3 → k) :
    (H.yElt v)⁻¹ * famProd H hadd (Multiplicative.ofAdd u) * ((H.yElt v)⁻¹)⁻¹ =
      famProd H hadd (Multiplicative.ofAdd u) * H.z (∑ j, η j * v j * u j) := by
  have hu : u = ∑ j, Pi.single j (u j) := (Finset.univ_sum_single u).symm
  rw [hu]
  refine Finset.sum_induction _ (fun x => (H.yElt v)⁻¹ * famProd H hadd (Multiplicative.ofAdd x) *
      ((H.yElt v)⁻¹)⁻¹ = famProd H hadd (Multiplicative.ofAdd x) * H.z (∑ j, η j * v j * x j))
    ?_ ?_ ?_
  · intro x y hx hy
    have hzc : ∀ w : k, H.z w * famProd H hadd (Multiplicative.ofAdd y) =
        famProd H hadd (Multiplicative.ofAdd y) * H.z w := fun w => z_comm_famProd H hadd w y
    have hsum : ∑ j, η j * v j * (x + y) j = ∑ j, η j * v j * x j + ∑ j, η j * v j * y j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [Pi.add_apply]; ring
    calc (H.yElt v)⁻¹ * famProd H hadd (Multiplicative.ofAdd (x + y)) * ((H.yElt v)⁻¹)⁻¹
        = ((H.yElt v)⁻¹ * famProd H hadd (Multiplicative.ofAdd x) * ((H.yElt v)⁻¹)⁻¹) *
          ((H.yElt v)⁻¹ * famProd H hadd (Multiplicative.ofAdd y) * ((H.yElt v)⁻¹)⁻¹) := by
          rw [ofAdd_add, map_mul]; group
      _ = famProd H hadd (Multiplicative.ofAdd x) * H.z (∑ j, η j * v j * x j) *
          (famProd H hadd (Multiplicative.ofAdd y) * H.z (∑ j, η j * v j * y j)) := by
          rw [hx, hy]
      _ = famProd H hadd (Multiplicative.ofAdd x) *
          (H.z (∑ j, η j * v j * x j) * famProd H hadd (Multiplicative.ofAdd y)) *
          H.z (∑ j, η j * v j * y j) := by simp only [mul_assoc]
      _ = famProd H hadd (Multiplicative.ofAdd x) *
          (famProd H hadd (Multiplicative.ofAdd y) * H.z (∑ j, η j * v j * x j)) *
          H.z (∑ j, η j * v j * y j) := by rw [hzc]
      _ = famProd H hadd (Multiplicative.ofAdd (x + y)) * H.z (∑ j, η j * v j * (x + y) j) := by
          rw [ofAdd_add, map_mul, hsum, H.z_add]
          simp only [mul_assoc]
  · simp [H.z_zero]
  · intro j _
    rw [famProd_single]
    have h1 := H.comm_yElt_xa v j (u j)
    rw [commutatorElement_def, inv_inv] at h1
    have h2 : (H.yElt v)⁻¹ * H.xa j (u j) * ((H.yElt v)⁻¹)⁻¹ =
        H.z (H.e j (v j) (u j)) * H.xa j (u j) := by
      rw [inv_inv]
      calc (H.yElt v)⁻¹ * H.xa j (u j) * H.yElt v
          = ((H.yElt v)⁻¹ * H.xa j (u j) * H.yElt v * (H.xa j (u j))⁻¹) * H.xa j (u j) := by
            group
        _ = _ := by rw [h1]
    rw [h2]
    have h3 : ∑ i, η i * v i * (Pi.single j (u j) : Fin 3 → k) i = η j * v j * u j := by
      rw [Finset.sum_eq_single j]
      · simp only [Pi.single_eq_same]
      · intro i _ hi
        simp [hi]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [h3, ← he]
    exact H.z_comm_a _ j _

end Prod

theorem mul_mul_mul_comm_of_comm {G : Type*} [Group G] (a b c d : G) (h : b * c = c * b) :
    a * b * (c * d) = a * c * (b * d) := by
  rw [mul_assoc a b, ← mul_assoc b c d, h, mul_assoc c b d, ← mul_assoc a c]

theorem perm_e6B_mem (j : Fin 3) : permLattice TwistTag.E6.perm (e6B j) ∈ heisS TwistTag.E6.tag := by
  rw [permLattice_e6B]
  exact e6R_mem j


section Fam

variable {k : Type} [Field k] (σ : k →+* k)

theorem orb_add_of_comm2 {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hc : Comm2 (k := k) α) (c d : k) : orb σ α (c + d) = orb σ α c * orb σ α d := by
  obtain ⟨ε, -, hF⟩ := twist_pinnedX σ hα
  unfold orb
  rw [hF (c + d), hF c, hF d, pinnedX_add, map_add, mul_add, pinnedX_add]
  exact mul_mul_mul_comm_of_comm _ _ _ _ (hc d (ε * σ c))

variable (hσ2 : ∀ c, σ (σ c) = c) {ε₀ : k} (hε₀ : ε₀ * ε₀ = 1)
  (hF₀ : ∀ w : k, twistHom TwistTag.E6 k σ
      (pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) w) =
    pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (ε₀ * σ w))
  (η : Fin 3 → k) (hη1 : ∀ j, η j * η j = 1)
  (hη : ∀ (j : Fin 3) (c d : k),
    ⁅(orb σ (heisα0 TwistTag.E6.tag - e6B j) c)⁻¹, orb σ (e6B j) d⁆ =
      pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (η j * c * d + ε₀ * σ (η j * c * d)))

@[expose] noncomputable def heisFamE6 :
    HeisFam ↥(graphFixedRootGroup TwistTag.E6 k σ) (Fin 3) (fun _ => k) k where
  xa j d := ⟨orb σ (e6B j) d, orb_mem σ (hF6.isRoot_of_mem _ (e6B_mem j))
    (hF6.pos_of_mem _ (e6B_mem j)) hσ2 (comm2_B j) d⟩
  xb j c := ⟨orb σ (heisα0 TwistTag.E6.tag - e6B j) c, orb_mem σ (hF6.isRoot_sub _ (e6B_mem j))
    (heis_gamma_pos (hF := hF6) (e6B_mem j)) hσ2 (comm2_T j) c⟩
  z w := ⟨pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (w + ε₀ * σ w),
    z_mem σ hσ2 hε₀ hF₀ w⟩
  e j c d := η j * c * d
  Rg := ⊤
  z_add w w' := Subtype.ext (by
    show pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (w + w' + ε₀ * σ (w + w')) =
      pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (w + ε₀ * σ w) *
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (w' + ε₀ * σ w')
    rw [← pinnedX_add, map_add]
    congr 1
    ring)
  e_add_left s c c' d := by
    show η s * (c + c') * d = η s * c * d + η s * c' * d
    ring
  e_mem _ _ _ := AddSubgroup.mem_top _
  e_surj s c hc w _ := ⟨w / (η s * c), by
    show η s * c * (w / (η s * c)) = w
    have h0 : η s ≠ 0 := fun h => by
      have := hη1 s
      rw [h, zero_mul] at this
      exact zero_ne_one this
    field_simp⟩
  xa_comm s t c d := Subtype.ext
    (commute_orb_S σ (e6B_mem s) (perm_e6B_mem s) (e6B_mem t) (perm_e6B_mem t) c d)
  xb_comm s t c d := Subtype.ext
    (commute_orb_T σ (e6B_mem s) (perm_e6B_mem s) (e6B_mem t) (perm_e6B_mem t) c d)
  z_comm_a w s d := Subtype.ext (commute_α0_orb_S σ (e6B_mem s) (perm_e6B_mem s) _ d)
  z_comm_b w s d := Subtype.ext (commute_α0_orb_T σ (e6B_mem s) (perm_e6B_mem s) _ d)
  xab_comm s t hst c d := Subtype.ext (by
    obtain ⟨h11, h12, h21, h22⟩ := e6_distinct s t hst
    rw [← permLattice_e6B s, ← permLattice_e6B t] at *
    exact commute_orb_T_S σ (e6B_mem s) (perm_e6B_mem s) (e6B_mem t) (perm_e6B_mem t) h11 h12
      h21 h22 c d)
  comm_ss s c d := Subtype.ext (hη s c d)

theorem heisFamE6_xa_add (j : Fin 3) (c d : k) :
    (heisFamE6 σ hσ2 hε₀ hF₀ η hη1 hη).xa j (c + d) =
      (heisFamE6 σ hσ2 hε₀ hF₀ η hη1 hη).xa j c * (heisFamE6 σ hσ2 hε₀ hF₀ η hη1 hη).xa j d :=
  Subtype.ext (orb_add_of_comm2 σ (hF6.isRoot_of_mem _ (e6B_mem j)) (comm2_B j) c d)

theorem heisFamE6_z_eq {w w' : k} (h : w + ε₀ * σ w = w' + ε₀ * σ w') :
    (heisFamE6 σ hσ2 hε₀ hF₀ η hη1 hη).z w = (heisFamE6 σ hσ2 hε₀ hF₀ η hη1 hη).z w' :=
  Subtype.ext (by
    show pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (w + ε₀ * σ w) =
      pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (w' + ε₀ * σ w')
    rw [h])

theorem heisFamE6_z_eq_one {w : k} (h : (heisFamE6 σ hσ2 hε₀ hF₀ η hη1 hη).z w = 1) :
    w + ε₀ * σ w = 0 := by
  have h1 := congrArg Subtype.val h
  exact pinnedX_injective TwistTag.E6.tag k (heisα0 TwistTag.E6.tag)
    (h1.trans (pinnedX_zero _ _ _).symm)

end Fam

theorem two_pow_le_card_of_graphFixedE6 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {k : Type} [Field k] [Finite k] {p : ℕ} [Fact p.Prime]
    [CharP k p] (hp2 : p ≠ 2) (σ : k →+* k) (hσ2 : ∀ c, σ (σ c) = c) (hne : ∃ u, σ u ≠ u)
    {L : Subgroup (MulAut W)} (π : ↥L →* ↥(graphFixedRootGroup TwistTag.E6 k σ))
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hZ : ¬ p ∣ Nat.card π.ker) :
    2 ^ (orderOf (2 : ZMod p) * (Nat.card k ^ 3 / (p - 1))) ≤ Nat.card W := by
  classical
  obtain ⟨ε₀, hε₀, hF₀'⟩ := twist_pinnedX σ (hF6.isRoot_α0 (τ := TwistTag.E6.tag))
  have hF₀ : ∀ w : k, twistHom TwistTag.E6 k σ
      (pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) w) =
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (ε₀ * σ w) := fun w => by
    rw [hF₀' w, permLattice_heisα0]
  choose η hη1 hη using pair_comm σ hσ2 hne hε₀ hF₀
  set H := heisFamE6 σ hσ2 hε₀ hF₀ η hη1 hη with hH
  have hadd := heisFamE6_xa_add σ hσ2 hε₀ hF₀ η hη1 hη
  have hε0 : ε₀ ≠ 0 := fun h => by
    rw [h, zero_mul] at hε₀
    exact zero_ne_one hε₀
  have hσε : σ ε₀ = ε₀ := map_sign σ hε₀
  obtain ⟨w₀, hw₀⟩ : ∃ w : k, w + ε₀ * σ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu⟩ := hne
    have h1 := hcon 1
    rw [map_one, mul_one] at h1
    have h2 := hcon u
    have hε : ε₀ = -1 := by linear_combination h1
    rw [hε] at h2
    exact hu (by linear_combination -h2)
  set ω := w₀ + ε₀ * σ w₀ with hω
  have hσω : σ ω = ε₀ * ω := by
    rw [hω, map_add, map_mul, hσε, hσ2]
    linear_combination (-σ w₀) * hε₀
  set F : Subfield k := RingHom.eqLocusField σ (RingHom.id k) with hF
  have : CharP F p := (RingHom.charP_iff_charP (algebraMap F k) p).2 inferInstance
  have hσF : ∀ c : F, σ (c : k) = c := fun c => c.2
  have hlmem : ∀ x : k, (x + ε₀ * σ x) * ω⁻¹ ∈ F := fun x => by
    show σ ((x + ε₀ * σ x) * ω⁻¹) = (x + ε₀ * σ x) * ω⁻¹
    have hω0 : ω ≠ 0 := hw₀
    have h1 : σ x + ε₀ * x = ε₀ * (x + ε₀ * σ x) := by linear_combination (-σ x) * hε₀
    rw [map_mul, map_inv₀, hσω, map_add, map_mul, hσε, hσ2, h1, mul_inv]
    calc ε₀ * (x + ε₀ * σ x) * (ε₀⁻¹ * ω⁻¹) = (ε₀ * ε₀⁻¹) * ((x + ε₀ * σ x) * ω⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hε0, one_mul]
  let lam : k →ₗ[F] F :=
    { toFun := fun x => ⟨(x + ε₀ * σ x) * ω⁻¹, hlmem x⟩
      map_add' := fun x y => Subtype.ext (by
        show (x + y + ε₀ * σ (x + y)) * ω⁻¹ =
          (x + ε₀ * σ x) * ω⁻¹ + (y + ε₀ * σ y) * ω⁻¹
        rw [map_add]
        ring)
      map_smul' := fun c x => Subtype.ext (by
        show ((c : k) * x + ε₀ * σ ((c : k) * x)) * ω⁻¹ = (c : k) * ((x + ε₀ * σ x) * ω⁻¹)
        rw [map_mul, hσF c]
        ring) }
  have hlam : ∀ x : k, ((lam x : F) : k) = (x + ε₀ * σ x) * ω⁻¹ := fun _ => rfl
  have hlam1 : lam w₀ = 1 := Subtype.ext (by
    rw [hlam]
    exact mul_inv_cancel₀ hw₀)
  let β : (Fin 3 → k) →ₗ[F] (Fin 3 → k) →ₗ[F] F :=
    LinearMap.mk₂ F (fun u v => ∑ j, lam (η j * v j * u j))
      (fun u u' v => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by
          rw [← map_add]
          congr 1
          simp only [Pi.add_apply]
          ring)
      (fun c u v => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by
          rw [← map_smul]
          congr 1
          show η j * v j * ((c : k) * u j) = (c : k) * (η j * v j * u j)
          ring)
      (fun u v v' => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by
          rw [← map_add]
          congr 1
          simp only [Pi.add_apply]
          ring)
      (fun c u v => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by
          rw [← map_smul]
          congr 1
          show η j * ((c : k) * v j) * u j = (c : k) * (η j * v j * u j)
          ring)
  have hβ_apply : ∀ u v, β u v = ∑ j, lam (η j * v j * u j) := fun _ _ => rfl
  have hη0 : ∀ j, η j ≠ 0 := fun j h => by
    have := hη1 j
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have hβsingle : ∀ (j : Fin 3) (x y : k),
      β (Pi.single j x) (Pi.single j y) = lam (η j * y * x) := by
    intro j x y
    rw [hβ_apply, Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same]
    · intro i _ hi
      simp [hi]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hβr : ∀ v : Fin 3 → k, v ≠ 0 → ∃ u, β u v ≠ 0 := by
    intro v hv
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    have hj' : v j ≠ 0 := hj
    refine ⟨Pi.single j (w₀ / (η j * v j)), ?_⟩
    rw [hβ_apply, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
      have e : η j * v j * (w₀ / (η j * v j)) = w₀ := by
        have := hη0 j
        field_simp
      rw [e, hlam1]
      exact one_ne_zero
    · intro i _ hi
      simp [hi]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hβl : ∀ u : Fin 3 → k, u ≠ 0 → ∃ v, β u v ≠ 0 := by
    intro u hu
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hu
    have hj' : u j ≠ 0 := hj
    refine ⟨Pi.single j (w₀ / (η j * u j)), ?_⟩
    rw [hβ_apply, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
      have e : η j * (w₀ / (η j * u j)) * u j = w₀ := by
        have := hη0 j
        field_simp
      rw [e, hlam1]
      exact one_ne_zero
    · intro i _ hi
      simp [hi]
    · intro h
      exact absurd (Finset.mem_univ j) h
  let z : Multiplicative F →* ↥(graphFixedRootGroup TwistTag.E6 k σ) :=
    { toFun := fun c => H.z ((c.toAdd : k) * w₀)
      map_one' := by
        show H.z (((0 : F) : k) * w₀) = 1
        rw [Subfield.coe_zero, zero_mul]
        exact H.z_zero
      map_mul' := fun c d => by
        show H.z (((c.toAdd + d.toAdd : F) : k) * w₀) =
          H.z ((c.toAdd : k) * w₀) * H.z ((d.toAdd : k) * w₀)
        rw [Subfield.coe_add, add_mul]
        exact H.z_add _ _ }
  have hzval : ∀ c : F, (c : k) * w₀ + ε₀ * σ ((c : k) * w₀) = (c : k) * ω := fun c => by
    rw [map_mul, hσF c, hω]
    ring
  have hz : ∀ c : F, z (Multiplicative.ofAdd c) = 1 → c = 0 := by
    intro c hc
    have h1 := heisFamE6_z_eq_one σ hσ2 hε₀ hF₀ η hη1 hη hc
    rw [toAdd_ofAdd, hzval c] at h1
    exact Subtype.ext ((mul_eq_zero.1 h1).resolve_right hw₀)
  let A := famProd H hadd
  let B : (Fin 3 → k) → ↥(graphFixedRootGroup TwistTag.E6 k σ) := fun v => (H.yElt v)⁻¹
  have hza : ∀ (c : Multiplicative F) (u : Multiplicative (Fin 3 → k)), z c * A u = A u * z c :=
    fun c u => z_comm_famProd H hadd _ u.toAdd
  have hbz : ∀ (c : Multiplicative F) (v : Fin 3 → k), B v * z c = z c * B v :=
    fun c v => (Commute.inv_left (H.yElt_comm_z v _)).eq
  have hab : ∀ u v, B v * A (Multiplicative.ofAdd u) * (B v)⁻¹ =
      A (Multiplicative.ofAdd u) * z (Multiplicative.ofAdd (β u v)) := by
    intro u v
    have hω0 : ω ≠ 0 := hw₀
    have hzβ : z (Multiplicative.ofAdd (β u v)) = H.z (∑ j, η j * v j * u j) := by
      show H.z (((β u v : F) : k) * w₀) = H.z (∑ j, η j * v j * u j)
      apply heisFamE6_z_eq σ hσ2 hε₀ hF₀ η hη1 hη
      rw [hzval, hβ_apply, AddSubmonoidClass.coe_finsetSum, Finset.sum_mul, map_sum,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => inv_mul_cancel_right₀ hω0 _
    rw [hzβ]
    exact famProd_conj H hadd η (fun _ _ _ => rfl) u v
  have key := FFToolkit.two_pow_le_card_of_heis_root_of_inj_one hW hp2 π hπ hker hZ
    (K := F) (V := Fin 3 → k) z A B β hβr hβl hz hza hab hbz
  rwa [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at key

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
