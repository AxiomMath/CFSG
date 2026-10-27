module

public import CFSG.LieType.Chevalley.ExceptionalFieldFourCoverArith
public import CFSG.LieType.Chevalley.RootCharacterKernelProduct
public import CFSG.LieType.Ree.LargeReeRootInvolution
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesSplittingCommuting

public noncomputable section

namespace CFSG.LieType.Chevalley.ExceptionalCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem commutator_shear {G : Type*} [Group G] {x x' z z' : G}
    (hxz' : Commute x z') (hx'z : Commute x' z) (hc : ∀ g : G, Commute ⁅x, x'⁆ g) :
    ⁅z * x, z' * x'⁆ = ⁅x, x'⁆ * ⁅z, z'⁆ := by
  have hxz'' : x * z' = z' * x := hxz'.eq
  have hx'z'' : x' * z⁻¹ = z⁻¹ * x' := (hx'z.inv_right).eq
  have hc' : x * x' * x⁻¹ = ⁅x, x'⁆ * x' := by
    rw [commutatorElement_def]
    group
  calc ⁅z * x, z' * x'⁆ = z * (x * z') * x' * x⁻¹ * z⁻¹ * x'⁻¹ * z'⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = z * z' * (x * x' * x⁻¹) * z⁻¹ * x'⁻¹ * z'⁻¹ := by
        rw [hxz'']
        group
    _ = z * z' * ⁅x, x'⁆ * (x' * z⁻¹) * x'⁻¹ * z'⁻¹ := by
        rw [hc']
        group
    _ = ⁅x, x'⁆ * ⁅z, z'⁆ := by
        rw [hx'z'', ← (hc (z * z')).eq]
        simp only [commutatorElement_def]
        group

theorem commute_mul_central {G : Type*} [Group G] {a b u v : G} (h : Commute a b)
    (hu : ∀ g : G, Commute u g) (hv : ∀ g : G, Commute v g) : Commute (a * u) (b * v) :=
  (h.mul_right (hv a).symm).mul_left (hu (b * v))

variable {τ : Tag} {K : Type} [Field K] [CharP K 2]

theorem two_eq_zero_of_charTwo : (2 : K) = 0 :=
  CharTwo.two_eq_zero

theorem pinnedX_sq
    (α : Fin τ.rank → ℤ) (c : K) : pinnedX τ K α c ^ 2 = 1 := by
  rw [sq, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

theorem pinnedX_inv_charTwo
    (α : Fin τ.rank → ℤ) (c : K) :
    (pinnedX τ K α c)⁻¹ = pinnedX τ K α c := by
  rw [pinnedX_neg, CharTwo.neg_eq]

variable {E : Type*} [Group E] {η : E →* adjointGroup τ K}

omit [CharP K 2] in
theorem coe_map_mul_inv (a b : E) :
    ((η (a * b * a⁻¹) : adjointGroup τ K) : ModGL τ K) =
      (η a : ModGL τ K) * (η b : ModGL τ K) * (η a : ModGL τ K)⁻¹ := by
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

variable [Finite K]

variable (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E)
include hη hC

theorem lift_commute_roots
    (hK : Nat.card K = 2 ^ 2) {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hcomm : ∀ c d : K, Commute (pinnedX τ K α c) (pinnedX τ K β d))
    (harith : ∀ i j : ℕ, i < 2 → j < 2 →
      ¬ ∀ k, (2 ^ 2 - 1 : ℤ) ∣ 2 ^ i * cartanCoord α k + 2 ^ j * cartanCoord β k)
    (a y : E) (ha : ∃ c : K, ((η a : adjointGroup τ K) : ModGL τ K) = pinnedX τ K α c)
    (hy : ∃ d : K, ((η y : adjointGroup τ K) : ModGL τ K) = pinnedX τ K β d) :
    a * y = y * a := by
  have hmem : ∀ (γ : Fin τ.rank → ℤ) (c : K), pinnedX τ K γ c ∈ adjointGroup τ K :=
    fun γ c => pinnedX_mem_adjointGroup γ c
  let A : Subgroup (adjointGroup τ K) := (rootSubgroup τ K α).subgroupOf (adjointGroup τ K)
  let B : Subgroup (adjointGroup τ K) := (rootSubgroup τ K β).subgroupOf (adjointGroup τ K)
  have hA : ∀ x : adjointGroup τ K, x ∈ A ↔ ∃ c : K, (x : ModGL τ K) = pinnedX τ K α c :=
    fun x => by
      rw [Subgroup.mem_subgroupOf, mem_rootSubgroup]
      exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
  have hB : ∀ x : adjointGroup τ K, x ∈ B ↔ ∃ c : K, (x : ModGL τ K) = pinnedX τ K β c :=
    fun x => by
      rw [Subgroup.mem_subgroupOf, mem_rootSubgroup]
      exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
  have hAeq : ∀ {x : adjointGroup τ K}, x ∈ A → ∃ c : K, x = ⟨pinnedX τ K α c, hmem α c⟩ :=
    fun hx => by
      obtain ⟨c, hc⟩ := (hA _).1 hx
      exact ⟨c, Subtype.ext hc⟩
  have hBeq : ∀ {x : adjointGroup τ K}, x ∈ B → ∃ c : K, x = ⟨pinnedX τ K β c, hmem β c⟩ :=
    fun hx => by
      obtain ⟨c, hc⟩ := (hB _).1 hx
      exact ⟨c, Subtype.ext hc⟩
  have hAc : ∀ c : K, (⟨pinnedX τ K α c, hmem α c⟩ : adjointGroup τ K) ∈ A :=
    fun c => (hA _).2 ⟨c, rfl⟩
  have hBc : ∀ c : K, (⟨pinnedX τ K β c, hmem β c⟩ : adjointGroup τ K) ∈ B :=
    fun c => (hB _).2 ⟨c, rfl⟩
  let τΓ : (Fin τ.rank → Kˣ) → adjointGroup τ K := fun t =>
    ⟨torusVec τ K t, torusVec_mem_adjointGroup t⟩
  have hτ : ∀ (t : Fin τ.rank → Kˣ) (γ : Fin τ.rank → ℤ) (hγ : IsRoot τ γ) (c : K),
      τΓ t * ⟨pinnedX τ K γ c, hmem γ c⟩ * (τΓ t)⁻¹ =
        ⟨pinnedX τ K γ ((rootChar K γ t : K) * c), hmem γ _⟩ := fun t γ hγ c =>
    Subtype.ext (torusVec_conj_pinnedX hγ t c)
  refine lift_commute_of_form_eq_zero η hη hC τΓ A B (fun x hx x' hx' => ?_)
    (fun x hx => ?_) (fun b hb₁ hb₂ hbT x hx x' hx' => ?_) a y ((hA _).2 ha) ((hB _).2 hy)
  · obtain ⟨c, rfl⟩ := hAeq hx
    obtain ⟨d, rfl⟩ := hBeq hx'
    exact Subtype.ext (hcomm c d).eq
  · obtain ⟨c, rfl⟩ := hAeq hx
    exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, pinnedX_sq])
  · obtain ⟨c, rfl⟩ := hAeq hx
    obtain ⟨d, rfl⟩ := hBeq hx'
    refine rootChar_form_eq_zero (by norm_num) hK harith
      (fun c d => b ⟨pinnedX τ K α c, hmem α c⟩ ⟨pinnedX τ K β d, hmem β d⟩)
      (fun c₁ c₂ d => ?_) (fun c d₁ d₂ => ?_) (fun t c d => ?_) c d
    · have e : (⟨pinnedX τ K α (c₁ + c₂), hmem α _⟩ : adjointGroup τ K) =
          ⟨pinnedX τ K α c₁, hmem α c₁⟩ * ⟨pinnedX τ K α c₂, hmem α c₂⟩ :=
        Subtype.ext (pinnedX_add τ K α c₁ c₂)
      change b _ _ = b _ _ + b _ _
      rw [e]
      exact hb₁ _ (hAc c₁) _ (hAc c₂) _ (hBc d)
    · have e : (⟨pinnedX τ K β (d₁ + d₂), hmem β _⟩ : adjointGroup τ K) =
          ⟨pinnedX τ K β d₁, hmem β d₁⟩ * ⟨pinnedX τ K β d₂, hmem β d₂⟩ :=
        Subtype.ext (pinnedX_add τ K β d₁ d₂)
      change b _ _ = b _ _ + b _ _
      rw [e]
      exact hb₂ _ (hAc c) _ (hBc d₁) _ (hBc d₂)
    · rw [← hτ t α hα c, ← hτ t β hβ d]
      exact hbT t _ (hAc c) _ (hBc d)

theorem lift_commute_edge
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : Nat.card K = 2 ^ 2) {i j : Fin τ.rank} (hij : τ.cartan i j = -1)
    (hji : τ.cartan j i = -1) (z z' : E)
    (hz : ∃ c : K, ((η z : adjointGroup τ K) : ModGL τ K) =
      pinnedX τ K (Pi.single i 1 + Pi.single j 1) c)
    (hz' : ∃ c : K, ((η z' : adjointGroup τ K) : ModGL τ K) =
      pinnedX τ K (Pi.single i 1 + Pi.single j 1) c) :
    z * z' = z' * z := by
  obtain ⟨c, hc⟩ := hz
  obtain ⟨c', hc'⟩ := hz'
  set α : Fin τ.rank → ℤ := Pi.single i 1 with hαdef
  set γ : Fin τ.rank → ℤ := Pi.single i 1 + Pi.single j 1 with hγdef
  have hne : i ≠ j := fun h => by
    subst h
    rw [τ.cartan_self] at hij
    exact absurd hij (by decide)
  have hα : IsRoot τ α := isRoot_single τ i
  have hrefl : reflect τ i (Pi.single j 1) = γ := by
    funext l
    simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hγdef, Pi.add_apply]
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one, hij]
    ring
  have hγ : IsRoot τ γ := hrefl ▸ (isRoot_single τ j).reflect i
  have hαp : 0 < height α := by rw [hαdef, height_single]; exact one_pos
  have hγh : height γ = 2 := by
    have e : height γ = height (Pi.single i (1 : ℤ)) + height (Pi.single j (1 : ℤ)) := by
      simp only [hγdef, height, Pi.add_apply, Finset.sum_add_distrib]
    rw [e, height_single, height_single]
    norm_num
  have hγp : 0 < height γ := by omega
  have hαγ : α ≠ γ := fun h => by
    have h1 := congrArg height h
    rw [hγh, hαdef, height_single] at h1
    exact absurd h1 (by decide)
  have hαγ' : α ≠ -γ := fun h => by
    have h1 := congrArg height h
    have h2 : height (-γ) = -height γ := by simp [height]
    rw [h2] at h1
    omega
  have hcommαγ : ∀ d d' : K, Commute (pinnedX τ K α d) (pinnedX τ K γ d') := fun d d' =>
    commute_of_forall_not_isRoot hα hγ hαγ hαγ' (fun a b ha hb => not_isRoot_edge hτ hij hji ha hb)
      K _ (Subgroup.subset_closure ⟨d, rfl⟩) _ (Subgroup.subset_closure ⟨d', rfl⟩)
  have hlift : ∀ x y : E, (∃ d : K, ((η x : adjointGroup τ K) : ModGL τ K) = pinnedX τ K α d) →
      (∃ d : K, ((η y : adjointGroup τ K) : ModGL τ K) = pinnedX τ K γ d) → Commute x y :=
    fun x y hx hy => lift_commute_roots hη hC hK hα hγ hcommαγ
      (fun i' j' hi' hj' => cross_not_dvd hτ hα hαp hγ hγp hαγ i' j' hi' hj') x y hx hy
  have hcen : ∀ g ∈ η.ker, ∀ h : E, Commute g h := fun g hg h =>
    ((Subgroup.mem_center_iff.1 (hC hg)) h).symm
  have hker : ∀ g : E, ((η g : adjointGroup τ K) : ModGL τ K) = 1 → g ∈ η.ker :=
    fun g hg => (MonoidHom.mem_ker).2 (Subtype.ext hg)
  have hshear : ∀ d : K, xUnit τ K j 1 * pinnedX τ K α d * (xUnit τ K j 1)⁻¹ =
      pinnedX τ K γ d * pinnedX τ K α d := by
    intro d
    have hcomm := (a2_simple_root_commutatorElement K hij hji d 1).1
    rw [mul_one, ← pinnedX_single τ K j d,
      CFSG.LieType.Ree.weylElt_conj_pinnedX_of_two_eq_zero two_eq_zero_of_charTwo i
        (isRoot_single τ j) d, hrefl] at hcomm
    rw [hαdef, pinnedX_single]
    calc xUnit τ K j 1 * xUnit τ K i d * (xUnit τ K j 1)⁻¹ =
        ⁅xUnit τ K i d, xUnit τ K j 1⁆⁻¹ * xUnit τ K i d := by
          rw [commutatorElement_def]
          group
      _ = pinnedX τ K γ d * xUnit τ K i d := by
          rw [hcomm, pinnedX_inv_charTwo]
  obtain ⟨x, hx⟩ := hη ⟨pinnedX τ K α c, pinnedX_mem_adjointGroup α c⟩
  obtain ⟨x', hx'⟩ := hη ⟨pinnedX τ K α c', pinnedX_mem_adjointGroup α c'⟩
  obtain ⟨n, hn⟩ := hη ⟨xUnit τ K j 1, xUnit_mem_adjointGroup j 1⟩
  have hxM : ((η x : adjointGroup τ K) : ModGL τ K) = pinnedX τ K α c := by rw [hx]
  have hx'M : ((η x' : adjointGroup τ K) : ModGL τ K) = pinnedX τ K α c' := by rw [hx']
  have hnM : ((η n : adjointGroup τ K) : ModGL τ K) = xUnit τ K j 1 := by rw [hn]
  set z₀ := n * x * n⁻¹ * x⁻¹ with hz₀
  set z₀' := n * x' * n⁻¹ * x'⁻¹ with hz₀'
  have hz₀M : ((η z₀ : adjointGroup τ K) : ModGL τ K) = pinnedX τ K γ c := by
    rw [hz₀, map_mul, Subgroup.coe_mul, coe_map_mul_inv, hnM, hxM, map_inv, Subgroup.coe_inv,
      hxM, hshear]
    group
  have hz₀'M : ((η z₀' : adjointGroup τ K) : ModGL τ K) = pinnedX τ K γ c' := by
    rw [hz₀', map_mul, Subgroup.coe_mul, coe_map_mul_inv, hnM, hx'M, map_inv, Subgroup.coe_inv,
      hx'M, hshear]
    group
  have hc₀ : ⁅x, x'⁆ ∈ η.ker := hker _ (by
    simp only [commutatorElement_def, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hxM,
      hx'M]
    rw [pinnedX_neg, pinnedX_neg, ← pinnedX_add, ← pinnedX_add, ← pinnedX_add]
    rw [show c + c' + -c + -c' = 0 by ring, pinnedX_zero])
  have key : ⁅x, x'⁆ = ⁅x, x'⁆ * ⁅z₀, z₀'⁆ := by
    have e1 : n * ⁅x, x'⁆ * n⁻¹ = ⁅x, x'⁆ := by
      rw [(hcen _ hc₀ n).eq.symm, mul_inv_cancel_right]
    have e2 : n * ⁅x, x'⁆ * n⁻¹ = ⁅z₀ * x, z₀' * x'⁆ := by
      rw [hz₀, hz₀']
      simp only [commutatorElement_def]
      group
    calc ⁅x, x'⁆ = n * ⁅x, x'⁆ * n⁻¹ := e1.symm
      _ = ⁅z₀ * x, z₀' * x'⁆ := e2
      _ = ⁅x, x'⁆ * ⁅z₀, z₀'⁆ := commutator_shear (hlift x z₀' ⟨c, hxM⟩ ⟨c', hz₀'M⟩)
          (hlift x' z₀ ⟨c', hx'M⟩ ⟨c, hz₀M⟩) (hcen _ hc₀)
  have hz₀z₀' : Commute z₀ z₀' := by
    have h1 : ⁅z₀, z₀'⁆ = 1 := by
      have := key
      rwa [left_eq_mul] at this
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1)
  have hu : z₀⁻¹ * z ∈ η.ker := hker _ (by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hz₀M, hc, inv_mul_cancel])
  have hu' : z₀'⁻¹ * z' ∈ η.ker := hker _ (by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hz₀'M, hc', inv_mul_cancel])
  have h := commute_mul_central hz₀z₀' (hcen _ hu) (hcen _ hu')
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at h
  exact h.eq

theorem lift_commute_simple
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : Nat.card K = 2 ^ 2) (j : Fin τ.rank) (y y' : E)
    (hy : ∃ c : K, ((η y : adjointGroup τ K) : ModGL τ K) = pinnedX τ K (Pi.single j 1) c)
    (hy' : ∃ c : K, ((η y' : adjointGroup τ K) : ModGL τ K) = pinnedX τ K (Pi.single j 1) c) :
    y * y' = y' * y := by
  obtain ⟨c, hc⟩ := hy
  obtain ⟨c', hc'⟩ := hy'
  obtain ⟨i, hij, hji⟩ := exists_single_edge hτ j
  have hrefl : reflect τ i (Pi.single j 1) = Pi.single i 1 + Pi.single j 1 := by
    funext l
    simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one, hij]
    ring
  obtain ⟨m, hm⟩ := hη ⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩
  have hmM : ((η m : adjointGroup τ K) : ModGL τ K) = weylElt τ K i 1 := by rw [hm]
  have hconj : ∀ (g : E) (d : K),
      ((η g : adjointGroup τ K) : ModGL τ K) = pinnedX τ K (Pi.single j 1) d →
        ∃ e : K, ((η (m * g * m⁻¹) : adjointGroup τ K) : ModGL τ K) =
          pinnedX τ K (Pi.single i 1 + Pi.single j 1) e := fun g d hg =>
    ⟨d, by rw [coe_map_mul_inv, hmM, hg,
      CFSG.LieType.Ree.weylElt_conj_pinnedX_of_two_eq_zero two_eq_zero_of_charTwo i
        (isRoot_single τ j) d, hrefl]⟩
  have h := lift_commute_edge hη hC hτ hK hij hji (m * y * m⁻¹) (m * y' * m⁻¹)
    (hconj y c hc) (hconj y' c' hc')
  have h' := congrArg (fun g => m⁻¹ * g * m) h
  simp only [mul_assoc, inv_mul_cancel_left] at h'
  simpa [mul_assoc] using h'

theorem lift_commute_root
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : Nat.card K = 2 ^ 2) (δ : Fin τ.rank → ℤ) (y y' : E)
    (hy : ∃ c : K, ((η y : adjointGroup τ K) : ModGL τ K) = pinnedX τ K δ c)
    (hy' : ∃ c : K, ((η y' : adjointGroup τ K) : ModGL τ K) = pinnedX τ K δ c) :
    y * y' = y' * y := by
  obtain ⟨c, hc⟩ := hy
  obtain ⟨c', hc'⟩ := hy'
  obtain ⟨m, hm⟩ := hη ⟨pinnedWeyl τ K δ, pinnedWeyl_mem_adjointGroup δ⟩
  have hmM : ((η m : adjointGroup τ K) : ModGL τ K) = pinnedWeyl τ K δ := by rw [hm]
  have hconj : ∀ (g : E) (d : K),
      ((η g : adjointGroup τ K) : ModGL τ K) = pinnedX τ K δ d →
        ∃ e : K, ((η (m⁻¹ * g * m⁻¹⁻¹) : adjointGroup τ K) : ModGL τ K) =
          pinnedX τ K (Pi.single (pinnedData τ δ).1 1) e := fun g d hg =>
    ⟨(pinnedData τ δ).2.2 • d, by
      rw [coe_map_mul_inv, map_inv, Subgroup.coe_inv, hmM, hg, pinnedX, pinnedX_single]
      group⟩
  have h := lift_commute_simple hη hC hτ hK (pinnedData τ δ).1 (m⁻¹ * y * m⁻¹⁻¹)
    (m⁻¹ * y' * m⁻¹⁻¹) (hconj y c hc) (hconj y' c' hc')
  have h' := congrArg (fun g => m * g * m⁻¹) h
  simp only [inv_inv, mul_assoc, mul_inv_cancel_left] at h'
  simpa [mul_assoc] using h'

end CFSG.LieType.Chevalley.ExceptionalCover
