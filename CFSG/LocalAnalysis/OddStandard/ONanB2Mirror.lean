module

public import CFSG.LocalAnalysis.OddStandard.ONanB2Three
public import CFSG.LocalAnalysis.OddStandard.ONanB2MirrorCM
public import CFSG.LocalAnalysis.OddStandard.ONanB2A6Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut

public section

namespace CFSG.OddStandard.ONanRec.B2

open Subgroup CM CFSG.GorensteinWalter CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
open CFSG.OddStandard.ONanRec.A6C

section Gen

variable {G : Type} [Group G] [Finite G]

theorem threeLocal_gen
    (hone : OneClass G) {i : G} (hi : orderOf i = 2)
    (ψ : centralizer ({i} : Set G) ≃* M480) {R : Subgroup G}
    (hRi : R ≤ centralizer ({i} : Set G)) (hR9 : Nat.card R = 9) :
    centralizer (R : Set G) = R ⊔ ⁅centralizer (R : Set G), centralizer (R : Set G)⁆ ∧
      R ⊓ ⁅centralizer (R : Set G), centralizer (R : Set G)⁆ = ⊥ ∧
      Nonempty (↥⁅centralizer (R : Set G), centralizer (R : Set G)⁆ ≃*
        alternatingGroup (Fin 6)) := by
  obtain ⟨hdec, hinf, ⟨eA⟩, -⟩ := threeLocal_R1 hone hi ψ
  have hQC : R1G ψ ≤ centralizer ({i} : Set G) := R1G_le ψ
  obtain ⟨c, hc⟩ := exists_conj_of_card_nine (H := centralizer ({i} : Set G))
    (by rw [card_centralizer_of_psi ψ]; decide)
    (P := R.subgroupOf (centralizer ({i} : Set G)))
    (Q := (R1G ψ).subgroupOf (centralizer ({i} : Set G)))
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hRi).toEquiv, hR9])
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, card_R1G ψ])
  set σ := (MulAut.conj (c : G)).toMonoidHom with hσ
  have hRmap : R = (R1G ψ).map σ := by
    ext x
    constructor
    · intro hx
      have h1 := (hc ⟨x, hRi hx⟩).1 ((mem_subgroupOf).2 hx)
      rw [mem_subgroupOf] at h1
      refine ⟨_, h1, ?_⟩
      show (c : G) * ((c⁻¹ * ⟨x, hRi hx⟩ * c : centralizer ({i} : Set G)) : G) * (c : G)⁻¹ = x
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · rintro ⟨y, hy, rfl⟩
      have hyC : σ y ∈ centralizer ({i} : Set G) :=
        mul_mem (mul_mem c.2 (hQC hy)) (inv_mem c.2)
      have h1 := (hc ⟨σ y, hyC⟩).2 (by
        rw [mem_subgroupOf]
        show ((c⁻¹ * ⟨σ y, hyC⟩ * c : centralizer ({i} : Set G)) : G) ∈ R1G ψ
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have e1 : (c : G)⁻¹ * σ y * (c : G) = y := by
          show (c : G)⁻¹ * ((c : G) * y * (c : G)⁻¹) * c = y
          group
        rw [e1]
        exact hy)
      rwa [mem_subgroupOf] at h1
  have hinj : Function.Injective σ := (MulAut.conj (c : G)).injective
  have hC : centralizer (R : Set G) = (CG ψ).map σ := by
    rw [hRmap, centralizer_map_conj, ← hσ]
  have hK : ⁅centralizer (R : Set G), centralizer (R : Set G)⁆ = (KG ψ).map σ := by
    rw [hC, KG, Subgroup.map_commutator]
  rw [hK]
  refine ⟨?_, ?_, ⟨((KG ψ).equivMapOfInjective σ hinj).symm.trans eA⟩⟩
  · rw [hC, hdec, Subgroup.map_sup, ← hRmap]
  · rw [hRmap, ← Subgroup.map_inf_eq _ _ σ hinj, hinf, Subgroup.map_bot]

end Gen

section Model

variable {K : Type} [Group K]

theorem nonempty_psl29 (eA : K ≃* alternatingGroup (Fin 6)) :
    Nonempty (K ≃* ↥A6Models.psl29) := by
  obtain ⟨ψ, -⟩ := CFSG.QuasithinUnique.DoubleA3.exists_psl_equiv
  exact ⟨eA.trans ψ.symm⟩

theorem ord4_of (φ : K ≃* ↥A6Models.psl29) {u : K} (h4 : u ^ 4 = 1) (h2 : u ^ 2 ≠ 1) :
    Ord4 ((φ u : ↥A6Models.psl29) : P10) := by
  refine ⟨?_, fun h => h2 ?_⟩
  · rw [← SubgroupClass.coe_pow, ← map_pow, h4, map_one, OneMemClass.coe_one]
  · apply φ.injective
    rw [map_pow, map_one]
    exact Subtype.ext (by rw [SubgroupClass.coe_pow, h, OneMemClass.coe_one])

theorem coe_phi_mul (φ : K ≃* ↥A6Models.psl29) (x y : K) :
    ((φ (x * y) : ↥A6Models.psl29) : P10) = (φ x : P10) * (φ y : P10) := by
  rw [map_mul, Subgroup.coe_mul]

theorem coe_phi_pow (φ : K ≃* ↥A6Models.psl29) (x : K) (n : ℕ) :
    ((φ (x ^ n) : ↥A6Models.psl29) : P10) = (φ x : P10) ^ n := by
  rw [map_pow, SubgroupClass.coe_pow]

theorem coe_phi_eq_one (φ : K ≃* ↥A6Models.psl29) {x : K} :
    ((φ x : ↥A6Models.psl29) : P10) = 1 ↔ x = 1 := by
  rw [OneMemClass.coe_eq_one, map_eq_one_iff φ φ.injective]

theorem coe_phi_inj (φ : K ≃* ↥A6Models.psl29) {x y : K} :
    ((φ x : ↥A6Models.psl29) : P10) = (φ y : P10) ↔ x = y := by
  rw [Subtype.coe_inj, φ.injective.eq_iff]

end Model

section Transport

variable {K : Type} [Group K] (φ : K ≃* ↥A6Models.psl29)

theorem pc_iff (u k : K) :
    PC ((φ u : ↥A6Models.psl29) : P10) ((φ k : ↥A6Models.psl29) : P10) ↔
      k ≠ 1 ∧ k ^ 3 = 1 ∧ u * k * u ^ 3 * k = k * (u * k * u ^ 3) ∧
        u ^ 2 * k * u ^ 2 = k ^ 2 := by
  simp only [PC, ← coe_phi_pow φ, ← coe_phi_mul φ, coe_phi_inj φ, ne_eq, coe_phi_eq_one φ]

theorem dc_iff (u k : K) :
    DC ((φ u : ↥A6Models.psl29) : P10) ((φ k : ↥A6Models.psl29) : P10) ↔
      k ^ 2 = 1 ∧ k ≠ 1 ∧ k * u * k * u = 1 := by
  simp only [DC, ← coe_phi_pow φ, ← coe_phi_mul φ, coe_phi_eq_one φ, ne_eq]

theorem pElt_phi (u r : K) (i j : ℕ) :
    pEltP ((φ u : ↥A6Models.psl29) : P10) ((φ r : ↥A6Models.psl29) : P10) i j =
      ((φ (r ^ i * (u * r * u ^ 3) ^ j) : ↥A6Models.psl29) : P10) := by
  simp only [pEltP, coe_phi_mul φ, coe_phi_pow φ]

theorem eOf_phi (u r : K) :
    eOfP ((φ u : ↥A6Models.psl29) : P10) ((φ r : ↥A6Models.psl29) : P10) =
      ((φ (r * u ^ 2 * r ^ 2) : ↥A6Models.psl29) : P10) := by
  simp only [eOfP, coe_phi_mul φ, coe_phi_pow φ]

end Transport

section Steps

variable {G : Type} [Group G] {f : G} (ψ : centralizer ({f} : Set G) ≃* M480)

theorem emb_zM_four :
    emb ψ zM ^ 4 = 1 := by
  rw [← map_pow, zM_four, map_one]

theorem emb_zM_sq_ne :
    emb ψ zM ^ 2 ≠ 1 := by
  rw [← map_pow, sq]
  intro h
  exact zM_sq_ne ((emb_injective ψ) (by rw [h, map_one]))

theorem exists_rho
    (hdec : CG ψ = R1G ψ ⊔ KG ψ) (hinf : R1G ψ ⊓ KG ψ = ⊥)
    (eA : KG ψ ≃* alternatingGroup (Fin 6)) :
    ∃ ρ : G, ρ ∈ KG ψ ∧ ρ ≠ 1 ∧ ρ ^ 3 = 1 ∧
      emb ψ zM * ρ * emb ψ zM ^ 3 * ρ = ρ * (emb ψ zM * ρ * emb ψ zM ^ 3) ∧
      emb ψ zM ^ 2 * ρ * emb ψ zM ^ 2 = ρ ^ 2 ∧
      ∀ i j i' j' : ℕ, i < 3 → j < 3 → i' < 3 → j' < 3 →
        ρ ^ i * (emb ψ zM * ρ * emb ψ zM ^ 3) ^ j =
          ρ ^ i' * (emb ψ zM * ρ * emb ψ zM ^ 3) ^ j' → i = i' ∧ j = j' := by
  obtain ⟨φ⟩ := nonempty_psl29 eA
  set zK : KG ψ := ⟨emb ψ zM, zG_mem_KG ψ hdec hinf⟩ with hzK
  have hz4 : zK ^ 4 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact emb_zM_four ψ)
  have hz2 : zK ^ 2 ≠ 1 := fun h => emb_zM_sq_ne ψ (by
    have := congrArg Subtype.val h
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at this)
  have h4 := ord4_of φ hz4 hz2
  obtain ⟨r, hr, hpc⟩ := exists_PC (φ zK).2 h4
  set ρK : KG ψ := φ.symm ⟨r, hr⟩ with hρK
  have hφρ : ((φ ρK : ↥A6Models.psl29) : P10) = r := by rw [hρK, MulEquiv.apply_symm_apply]
  rw [← hφρ] at hpc
  obtain ⟨h1, h3, hc, hinv⟩ := (pc_iff φ zK ρK).1 hpc
  refine ⟨ρK, ρK.2, fun h => h1 (Subtype.ext h), ?_, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val h3
    simpa using this
  · have := congrArg Subtype.val hc
    simpa [hzK] using this
  · have := congrArg Subtype.val hinv
    simpa [hzK] using this
  · intro i j i' j' hi hj hi' hj' he
    have hpc' := hpc
    rw [hφρ] at hpc'
    refine pElt_injective (φ zK).2 hr h4 hpc' hi hj hi' hj' ?_
    rw [← hφρ, pElt_phi, pElt_phi, coe_phi_inj]
    exact Subtype.ext (by simpa [hzK] using he)

theorem aG_comm_KG
    {l : ℕ}
    (hw : ∀ k ∈ KG ψ, emb ψ (yM * fM ^ l) * k = k * emb ψ (yM * fM ^ l)) :
    ∀ k ∈ KG ψ, emb ψ aM * k = k * emb ψ aM := by
  have ha : emb ψ aM = emb ψ (yM * fM ^ l) * emb ψ (yM * fM ^ l) := by
    rw [← map_mul, ← sq, yfM_pow, pow_mul', fM_pow_two, one_pow, mul_one, sq,
      mirrorFacts_cert.y_sq]
  intro k hk
  rw [ha]
  calc emb ψ (yM * fM ^ l) * emb ψ (yM * fM ^ l) * k =
      emb ψ (yM * fM ^ l) * (emb ψ (yM * fM ^ l) * k) := by group
    _ = emb ψ (yM * fM ^ l) * (k * emb ψ (yM * fM ^ l)) := by rw [hw k hk]
    _ = (emb ψ (yM * fM ^ l) * k) * emb ψ (yM * fM ^ l) := by group
    _ = k * emb ψ (yM * fM ^ l) * emb ψ (yM * fM ^ l) := by rw [hw k hk]
    _ = k * (emb ψ (yM * fM ^ l) * emb ψ (yM * fM ^ l)) := by group

theorem aM_eq : aM = yM ^ 2 := by
  rw [sq, mirrorFacts_cert.y_sq]

theorem orderOf_aG :
    orderOf (emb ψ aM) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, aM_eq, ← pow_mul, yM_four, map_one]
  · intro h
    apply yM_sq_ne
    apply emb_injective ψ
    rw [← sq, ← aM_eq, h, map_one]

theorem emb_pow_eq_one_iff (m : M480) (n : ℕ) : emb ψ m ^ n = 1 ↔ m ^ n = 1 := by
  rw [← map_pow, map_eq_one_iff _ (emb_injective ψ)]

theorem emb_comm (u m : M480) :
    emb ψ (u * m * u⁻¹ * m⁻¹) = emb ψ u * emb ψ m * (emb ψ u)⁻¹ * (emb ψ m)⁻¹ := by
  simp only [map_mul, map_inv]

theorem emb_evalM_mem {K : Subgroup G} {u t : M480}
    (h1 : emb ψ r1M ∈ K) (h2 : emb ψ r2M ∈ K) (hu : emb ψ u ∈ K) (ht : emb ψ t ∈ K)
    (w : List ℕ) : emb ψ (evalM u t w) ∈ K := by
  unfold evalM
  rw [map_list_prod, List.map_map]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  simp only [Function.comp_apply]
  split_ifs
  exacts [h1, h2, hu, ht]

theorem emb_aM_eq
    (l : ℕ) :
    emb ψ aM = emb ψ (yM * fM ^ l) * emb ψ (yM * fM ^ l) := by
  rw [← map_mul, ← sq, yfM_pow, pow_mul', fM_pow_two, one_pow, mul_one, sq,
    mirrorFacts_cert.y_sq]

end Steps

section Rels

theorem lift_eq_one_of_coe {Pm : Fin 6 → M480} {P : Fin 6 → Equiv.Perm (Fin 480)}
    (hP : ∀ j, (Pm j : Equiv.Perm (Fin 480)) = P j) {r : FreeGroup (Fin 6)}
    (hr : FreeGroup.lift P r = 1) : FreeGroup.lift Pm r = 1 := by
  apply Subtype.ext
  rw [OneMemClass.coe_one, ← hr]
  exact FreeGroup.lift_unique (M480.subtype.comp (FreeGroup.lift Pm)) fun x => by simp [hP]

theorem lift_comp_eq_one {H K : Type*} [Group H] [Group K] (θ : H →* K) {Γ : Fin 6 → H}
    (hΓ : ∀ r ∈ relsM, FreeGroup.lift Γ r = 1) :
    ∀ r ∈ relsM, FreeGroup.lift (fun j => θ (Γ j)) r = 1 := by
  intro r hr
  rw [← FreeGroup.lift_unique (θ.comp (FreeGroup.lift Γ)) fun x => by simp,
    MonoidHom.comp_apply, hΓ r hr, map_one]

theorem relsM_genM :
    ∀ r ∈ relsM, FreeGroup.lift ![aM, bM, cM, dM, fM, gM] r = 1 := fun r hr =>
  lift_eq_one_of_coe (P := genPerm) (fun j => by
      fin_cases j <;> simp [genPerm, aW, bW, cW, dP, dW, fP, fW, gP, gW, wordPerm])
    (rels_ok lettersOK_cert (relOK_of cmModelCheck_cert) r hr)

theorem relsM_gen2M :
    ∀ r ∈ relsM, FreeGroup.lift ![aM, bM, cM, dM, fM, g2M] r = 1 := fun r hr =>
  lift_eq_one_of_coe (P := gen2Perm) (fun j => by
      fin_cases j <;> simp [gen2Perm_eq, genPerm, aW, bW, cW, dP, dW, fP, fW, wordPerm])
    (lift_gen2_relsM r hr)

theorem relsM_facts {H : Type*} [Group H] {Γ : Fin 6 → H}
    (hΓ : ∀ r ∈ relsM, FreeGroup.lift Γ r = 1) :
    Γ 0 * Γ 0 = 1 ∧ Γ 1 * Γ 1 = 1 ∧ Γ 2 * Γ 2 = 1 ∧ Γ 3 * Γ 3 = 1 ∧ Γ 4 * Γ 4 = 1 ∧
      Γ 0 * Γ 3 = Γ 3 * Γ 0 ∧ Γ 1 * Γ 3 = Γ 3 * Γ 1 ∧ Γ 5 ^ 4 = 1 ∧ Γ 5 ^ 2 = Γ 0 * Γ 4 := by
  have h0 := hΓ (FreeGroup.of 0 ^ 2) (by unfold relsM; exact Or.inl rfl)
  have h1 := hΓ (FreeGroup.of 1 ^ 2) (by unfold relsM; exact Or.inr (Or.inl rfl))
  have h2 := hΓ (FreeGroup.of 2 ^ 2) (by unfold relsM; exact Or.inr (Or.inr (Or.inl rfl)))
  have h3 := hΓ (FreeGroup.of 3 ^ 2) (by unfold relsM; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 := hΓ (FreeGroup.of 4 ^ 2) (by unfold relsM; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h03 := hΓ ((FreeGroup.of 0 * FreeGroup.of 3) ^ 2)
    (by unfold relsM; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h13 := hΓ ((FreeGroup.of 1 * FreeGroup.of 3) ^ 2)
    (by unfold relsM; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))
  have h5 := hΓ (FreeGroup.of 5 ^ 4)
    (by unfold relsM; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))
  have h54 := hΓ ((FreeGroup.of 0 * FreeGroup.of 4)⁻¹ * FreeGroup.of 5 ^ 2)
    (by unfold relsM; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))
  simp only [map_pow, map_mul, map_inv, FreeGroup.lift_apply_of] at h0 h1 h2 h3 h4 h03 h13 h5 h54
  rw [sq] at h0 h1 h2 h3 h4
  have hcomm : ∀ {x y : H}, x * x = 1 → y * y = 1 → (x * y) ^ 2 = 1 → x * y = y * x := by
    intro x y hx hy hxy
    rw [sq] at hxy
    calc x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left hxy
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]
  exact ⟨h0, h1, h2, h3, h4, hcomm h0 h3 h03, hcomm h1 h3 h13, h5, (inv_mul_eq_one.1 h54).symm⟩

theorem aM_sq : aM * aM = 1 := (relsM_facts relsM_genM).1
theorem aM_dM : aM * dM = dM * aM :=
  (relsM_facts relsM_genM).2.2.2.2.2.1
theorem bM_dM : bM * dM = dM * bM :=
  (relsM_facts relsM_genM).2.2.2.2.2.2.1
theorem gM_four : gM ^ 4 = 1 :=
  (relsM_facts relsM_genM).2.2.2.2.2.2.2.1
theorem gM_sq : gM ^ 2 = aM * fM :=
  (relsM_facts relsM_genM).2.2.2.2.2.2.2.2
theorem g2M_four : g2M ^ 4 = 1 :=
  (relsM_facts relsM_gen2M).2.2.2.2.2.2.2.1

theorem r1M_eq : r1M = aM * bM := by
  apply Subtype.ext
  simp only [coe_r1M, Subgroup.coe_mul, coe_aM, coe_bM, r1P]
  rw [show r1W = aW ++ bW from rfl, wordPerm_append]

theorem bM_eq : bM = aM * r1M := by
  rw [r1M_eq, ← mul_assoc, aM_sq, one_mul]

theorem conj_yfM (l : ℕ)
    (m : M480) : (yM * fM ^ l) * m * (yM * fM ^ l)⁻¹ = yM * m * yM⁻¹ := by
  have hc : Commute (fM ^ l) m := Commute.pow_left (show Commute fM m from (fM_comm m).symm) l
  calc (yM * fM ^ l) * m * (yM * fM ^ l)⁻¹ = yM * (fM ^ l * m) * (fM ^ l)⁻¹ * yM⁻¹ := by group
    _ = yM * (m * fM ^ l) * (fM ^ l)⁻¹ * yM⁻¹ := by rw [hc.eq]
    _ = yM * m * yM⁻¹ := by group

theorem zM_comm_yfM
    (l : ℕ) : zM * (yM * fM ^ l) = (yM * fM ^ l) * zM := by
  have hc : Commute (fM ^ l) zM := Commute.pow_left (show Commute fM zM from (fM_comm zM).symm) l
  rw [← mul_assoc, ← mirrorFacts_cert.y_z, mul_assoc, mul_assoc, hc.eq]

theorem r1M_ne_one : r1M ≠ 1 := by
  intro h
  have := rM_inj (i := 1) (j := 0) (i' := 0) (j' := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by simp [h])
  exact absurd this.1 (by norm_num)

theorem u_r1_u3 (l : ℕ) :
    (yM * fM ^ l) * r1M * (yM * fM ^ l) ^ 3 = r2M ^ 2 := by
  have h3 : (yM * fM ^ l) ^ 3 = (yM * fM ^ l)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, yfM_four])
  rw [h3, conj_yfM, yM_r1M]

theorem u2_r1_u2 (l : ℕ) :
    (yM * fM ^ l) ^ 2 * r1M * (yM * fM ^ l) ^ 2 = r1M ^ 2 := by
  have hu2 : (yM * fM ^ l) ^ 2 = yM ^ 2 := by rw [yfM_pow, pow_mul', fM_pow_two, one_pow, mul_one]
  rw [hu2]
  have hy2 : yM ^ 2 = (yM ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_add, yM_four])
  calc yM ^ 2 * r1M * yM ^ 2 = yM ^ 2 * r1M * (yM ^ 2)⁻¹ := by rw [← hy2]
    _ = yM * (yM * r1M * yM⁻¹) * yM⁻¹ := by rw [sq, mul_inv_rev]; simp only [mul_assoc]
    _ = yM * r2M ^ 2 * yM⁻¹ := by rw [yM_r1M]
    _ = (yM * r2M * yM⁻¹) ^ 2 := by rw [conj_pow]
    _ = r1M ^ 2 := by rw [yM_r2M]

theorem r2M_sq_comm :
    r2M ^ 2 * r1M = r1M * r2M ^ 2 :=
  ((show Commute r1M r2M from rM_comm).pow_right 2).symm.eq

theorem dcd_conj :
    dM * (dM * cM * dM) * dM = cM := by
  calc dM * (dM * cM * dM) * dM = (dM * dM) * cM * (dM * dM) := by group
    _ = cM := by rw [dM_sq, one_mul, mul_one]

end Rels

section GroupLemmas

variable {G : Type} [Group G]

theorem card_closure_pair {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a)
    (hinj : ∀ i j i' j' : ℕ, i < 3 → j < 3 → i' < 3 → j' < 3 →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j') :
    Nat.card (closure ({a, b} : Set G)) = 9 := by
  let F : Fin 3 × Fin 3 → closure ({a, b} : Set G) := fun p =>
    ⟨a ^ p.1.val * b ^ p.2.val, (mem_closure_pair_iff ha hb hab _).2 ⟨_, _, p.1.2, p.2.2, rfl⟩⟩
  have hF : Function.Bijective F := by
    refine ⟨fun p q hpq => ?_, fun x => ?_⟩
    · obtain ⟨h1, h2⟩ := hinj _ _ _ _ p.1.2 p.2.2 q.1.2 q.2.2 (congrArg Subtype.val hpq)
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · obtain ⟨i, j, hi, hj, he⟩ := (mem_closure_pair_iff ha hb hab x).1 x.2
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), Subtype.ext he.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF)]
  simp

theorem mem_normalizer_commutator {R : Subgroup G} {g : G} (hg : g ∈ normalizer (R : Set G)) :
    g ∈ normalizer ((⁅centralizer (R : Set G), centralizer (R : Set G)⁆ : Subgroup G) :
      Set G) := by
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_commutator_centralizer hg hh, fun hh => ?_⟩
  have := conj_mem_commutator_centralizer (inv_mem hg) hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

theorem conj_inv_eq_sq {z ρ : G} (hz4 : z ^ 4 = 1) (hi : z ^ 2 * ρ * z ^ 2 = ρ ^ 2) :
    z⁻¹ * ρ * z = (z * ρ * z⁻¹) ^ 2 := by
  rw [conj_pow, ← hi]
  calc z⁻¹ * ρ * z = z ^ 4 * (z⁻¹ * ρ * z) := by rw [hz4, one_mul]
    _ = z * (z ^ 2 * ρ * z ^ 2) * z⁻¹ := by group

theorem conj_inv_of_inv {s a b : G} (hs : s * s = 1) (ha : s * a * s = a⁻¹) (hb : s * b * s = b⁻¹)
    (hab : a * b = b * a) (i j : ℕ) : s * (a ^ i * b ^ j) * s = (a ^ i * b ^ j)⁻¹ := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hai : s * a ^ i * s = (a ^ i)⁻¹ :=
    calc s * a ^ i * s = s * a ^ i * s⁻¹ := by rw [hs']
      _ = (s * a * s⁻¹) ^ i := conj_pow.symm
      _ = (a ^ i)⁻¹ := by rw [hs', ha, inv_pow]
  have hbj : s * b ^ j * s = (b ^ j)⁻¹ :=
    calc s * b ^ j * s = s * b ^ j * s⁻¹ := by rw [hs']
      _ = (s * b * s⁻¹) ^ j := conj_pow.symm
      _ = (b ^ j)⁻¹ := by rw [hs', hb, inv_pow]
  have hc : Commute (a ^ i) (b ^ j) := (Commute.pow_pow (hab : Commute a b) i j)
  calc s * (a ^ i * b ^ j) * s = (s * a ^ i * s) * (s * b ^ j * s) := by
        rw [show (s * a ^ i * s) * (s * b ^ j * s) = s * a ^ i * (s * s) * b ^ j * s by group, hs]
        group
    _ = (a ^ i * b ^ j)⁻¹ := by rw [hai, hbj, ← mul_inv_rev, ← hc.eq]

open CFSG.GroupTheory.WielandtProduct in
theorem coe_normalizerConj_pow (V : Subgroup G) (g : normalizer (V : Set G)) (n : ℕ) (w : V) :
    (((normalizerConj V g ^ n) w : V) : G) = (g : G) ^ n * w * ((g : G) ^ n)⁻¹ := by
  rw [← map_pow, coe_normalizerConj_apply, SubgroupClass.coe_pow]

theorem phi_pow_conj {K : Type*} [Group K] (φ : K ≃* ↥A6Models.psl29) (γ : MulAut K) {b : P10}
    (hb : ∀ k, ((φ (γ k) : ↥A6Models.psl29) : P10) = b * (φ k : P10) * b⁻¹) (n : ℕ) (k : K) :
    ((φ ((γ ^ n) k) : ↥A6Models.psl29) : P10) = b ^ n * (φ k : P10) * (b ^ n)⁻¹ := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, hb, pow_succ]
    group

open CFSG.GroupTheory.WielandtProduct in
theorem rel_of_relP {K : Subgroup G} (φ : K ≃* ↥A6Models.psl29) {h : G}
    (hh : h⁻¹ ∈ normalizer (K : Set G)) (h4 : h ^ 4 = 1) {b : P10} (hb120 : b ^ 120 = 1)
    (hrep : ∀ k : K, ((φ (normalizerConj K ⟨h⁻¹, hh⟩ k) : ↥A6Models.psl29) : P10) =
      b * (φ k : P10) * b⁻¹)
    {d e : K} (hR : RelP b ((φ d : ↥A6Models.psl29) : P10) ((φ e : ↥A6Models.psl29) : P10)) :
    h * e * d * h * d * e * h * e * d * h * d = 1 := by
  have hb119 : b ^ 119 = b⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hb120]
  have hc : ∀ (n : ℕ) (k : K), conjP b n ((φ k : ↥A6Models.psl29) : P10) =
      ((φ ((normalizerConj K ⟨h⁻¹, hh⟩ ^ n) k) : ↥A6Models.psl29) : P10) := by
    intro n k
    rw [conjP, hb119, inv_pow, phi_pow_conj φ _ hrep]
  unfold RelP at hR
  rw [← coe_phi_mul φ e d, ← coe_phi_mul φ d e, hc, hc, hc, ← coe_phi_mul φ, ← coe_phi_mul φ,
    ← coe_phi_mul φ, coe_phi_eq_one φ] at hR
  have hG : ((((normalizerConj K ⟨h⁻¹, hh⟩ ^ 3) (e * d) * (normalizerConj K ⟨h⁻¹, hh⟩ ^ 2) (d * e) *
      (normalizerConj K ⟨h⁻¹, hh⟩ ^ 1) (e * d) * d : K)) : G) = 1 := by
    rw [hR]
    rfl
  simp only [Subgroup.coe_mul, coe_normalizerConj_pow] at hG
  calc h * e * d * h * d * e * h * e * d * h * d =
      h ^ 4 * ((h⁻¹) ^ 3 * (e * d) * ((h⁻¹) ^ 3)⁻¹ * ((h⁻¹) ^ 2 * (d * e) * ((h⁻¹) ^ 2)⁻¹) *
        ((h⁻¹) ^ 1 * (e * d) * ((h⁻¹) ^ 1)⁻¹) * d) := by group
    _ = 1 := by rw [h4, one_mul]; exact hG

theorem pc_iff_coe {K : Subgroup G} (φ : K ≃* ↥A6Models.psl29) (u k : K) :
    PC ((φ u : ↥A6Models.psl29) : P10) ((φ k : ↥A6Models.psl29) : P10) ↔
      (k : G) ≠ 1 ∧ (k : G) ^ 3 = 1 ∧
        (u : G) * k * (u : G) ^ 3 * k = k * ((u : G) * k * (u : G) ^ 3) ∧
          (u : G) ^ 2 * k * (u : G) ^ 2 = (k : G) ^ 2 := by
  rw [pc_iff φ]
  simp only [ne_eq, Subtype.ext_iff, Subgroup.coe_mul, SubgroupClass.coe_pow,
    OneMemClass.coe_one]

theorem dc_iff_coe {K : Subgroup G} (φ : K ≃* ↥A6Models.psl29) (u k : K) :
    DC ((φ u : ↥A6Models.psl29) : P10) ((φ k : ↥A6Models.psl29) : P10) ↔
      (k : G) ^ 2 = 1 ∧ (k : G) ≠ 1 ∧ (k : G) * u * k * u = 1 := by
  rw [dc_iff φ]
  simp only [ne_eq, Subtype.ext_iff, Subgroup.coe_mul, SubgroupClass.coe_pow,
    OneMemClass.coe_one]

theorem psl29_le_autA6' : A6Models.psl29 ≤ A6Models.autA6 := by
  unfold A6Models.psl29 A6Models.autA6
  refine closure_mono fun x hx => ?_
  rcases hx with rfl | rfl | rfl <;> simp

theorem not_bad_order {K : Subgroup G}
    (φ : K ≃* ↥A6Models.psl29) {x : G} (hx : x ∈ K)
    (h : (x ^ 6 = 1 ∧ x ^ 2 ≠ 1 ∧ x ^ 3 ≠ 1) ∨ (x ^ 8 = 1 ∧ x ^ 4 ≠ 1)) : False := by
  have hp : ∀ n : ℕ, ((φ ⟨x, hx⟩ : ↥A6Models.psl29) : P10) ^ n = 1 ↔ x ^ n = 1 := by
    intro n
    rw [← coe_phi_pow φ, coe_phi_eq_one φ, Subtype.ext_iff, SubgroupClass.coe_pow,
      OneMemClass.coe_one]
  obtain ⟨h6, h8⟩ := no_order_six_eight (φ ⟨x, hx⟩).2
  rcases h with ⟨a, b, c⟩ | ⟨a, b⟩
  · rcases h6 ((hp 6).2 a) with h | h
    · exact b ((hp 2).1 h)
    · exact c ((hp 3).1 h)
  · exact b ((hp 4).1 (h8 ((hp 8).2 a)))

theorem comm_of_fix {K : Subgroup G} (φ : K ≃* ↥A6Models.psl29)
    {z : G} (hz : z ∈ normalizer (K : Set G)) {u r : K}
    (h4 : Ord4 ((φ u : ↥A6Models.psl29) : P10))
    (hpc : PC ((φ u : ↥A6Models.psl29) : P10) ((φ r : ↥A6Models.psl29) : P10))
    (hzu : z * u = u * z) (hzr : z * r = r * z) : ∀ k ∈ K, z * k = k * z := by
  set τ := CFSG.GroupTheory.WielandtProduct.normalizerConj K ⟨z, hz⟩ with hτ
  obtain ⟨b, hbA, hb⟩ := DoubleA3.exists_aut_model φ τ
  have hfix : ∀ v : K, z * v = v * z → τ v = v := by
    intro v hv
    apply Subtype.ext
    rw [hτ, CFSG.GroupTheory.WielandtProduct.coe_normalizerConj_apply]
    show z * v * z⁻¹ = v
    rw [hv, mul_inv_cancel_right]
  have hbu := hb u
  rw [hfix u hzu] at hbu
  have hbr := hb r
  rw [hfix r hzr] at hbr
  have hb1 : b = 1 := eq_one_of_comm hbA (φ u).2 (φ r).2 h4 hpc
    (by rw [mul_inv_eq_iff_eq_mul.1 hbu.symm]) (by rw [mul_inv_eq_iff_eq_mul.1 hbr.symm])
  intro k hk
  have hk' := hb ⟨k, hk⟩
  rw [hb1, one_mul, inv_one, mul_one, coe_phi_inj φ] at hk'
  have := congrArg Subtype.val hk'
  rw [hτ, CFSG.GroupTheory.WielandtProduct.coe_normalizerConj_apply] at this
  have e : z * k * z⁻¹ = k := this
  calc z * k = z * k * z⁻¹ * z := by group
    _ = k * z := by rw [e]

theorem mk_pow_eq_one {K : Subgroup G} {x : G} (hx : x ∈ K) (n : ℕ) :
    (⟨x, hx⟩ : K) ^ n = 1 ↔ x ^ n = 1 := by
  rw [Subtype.ext_iff, SubgroupClass.coe_pow, OneMemClass.coe_one]

theorem mem_of_comm_conj {K C : Subgroup G} (hKC : ∀ s ∈ C, ∀ k ∈ K, s * k * s⁻¹ ∈ K) {y s : G}
    (hy : y ∈ K) (hs : s ∈ C) : y * s * y⁻¹ * s⁻¹ ∈ K := by
  have := hKC s hs y⁻¹ (inv_mem hy)
  rw [show y * s * y⁻¹ * s⁻¹ = y * (s * y⁻¹ * s⁻¹) by group]
  exact mul_mem hy this

theorem dconj_facts {z d ρ a b c c' : G} (hz4 : z ^ 4 = 1) (hd : d * d = 1)
    (hdz : d * z * d = z⁻¹) (hda : a * d = d * a) (hdb : b * d = d * b) (hdc : d * c' * d = c)
    (hρ3 : ρ ^ 3 = 1) (hρ1 : ρ ≠ 1) (hc : z * ρ * z ^ 3 * ρ = ρ * (z * ρ * z ^ 3))
    (hi : z ^ 2 * ρ * z ^ 2 = ρ ^ 2)
    (hcomm : ∀ i j : ℕ, Commute (ρ ^ i * ((z * ρ * z ^ 3) ^ 2) ^ j) a ∧
      Commute (ρ ^ i * ((z * ρ * z ^ 3) ^ 2) ^ j) b ∧
        Commute (ρ ^ i * ((z * ρ * z ^ 3) ^ 2) ^ j) c') :
    d * ρ * d ≠ 1 ∧ (d * ρ * d) ^ 3 = 1 ∧
      z * (d * ρ * d) * z ^ 3 * (d * ρ * d) = (d * ρ * d) * (z * (d * ρ * d) * z ^ 3) ∧
      z ^ 2 * (d * ρ * d) * z ^ 2 = (d * ρ * d) ^ 2 ∧
      ∀ i j : ℕ, Commute ((d * ρ * d) ^ i * (z * (d * ρ * d) * z ^ 3) ^ j) a ∧
        Commute ((d * ρ * d) ^ i * (z * (d * ρ * d) * z ^ 3) ^ j) b ∧
        Commute ((d * ρ * d) ^ i * (z * (d * ρ * d) * z ^ 3) ^ j) c := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have hz3 : z ^ 3 = z⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hz4])
  have hz2 : (z ^ 2)⁻¹ = z ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_add, hz4])
  have hσ' : ∀ x, MulAut.conj d x = d * x * d := fun x => by rw [MulAut.conj_apply, hdi]
  have hσz : MulAut.conj d z = z⁻¹ := by rw [hσ', hdz]
  have hσa : MulAut.conj d a = a := by rw [hσ', ← hda, mul_assoc, hd, mul_one]
  have hσb : MulAut.conj d b = b := by rw [hσ', ← hdb, mul_assoc, hd, mul_one]
  have hσc : MulAut.conj d c' = c := by rw [hσ', hdc]
  have hρ₀ : d * ρ * d = MulAut.conj d ρ := (hσ' ρ).symm
  have hs : z * (MulAut.conj d ρ) * z ^ 3 = MulAut.conj d (z⁻¹ * ρ * z) := by
    rw [map_mul, map_mul, map_inv, hσz, inv_inv, hz3]
  have hsq : z⁻¹ * ρ * z = (z * ρ * z ^ 3) ^ 2 := by
    rw [hz3]
    exact conj_inv_eq_sq hz4 hi
  have hcρ : Commute ((z * ρ * z ^ 3) ^ 2) ρ := (show Commute (z * ρ * z ^ 3) ρ from hc).pow_left 2
  rw [hρ₀, hs, hsq]
  refine ⟨fun h => hρ1 ((MulAut.conj d).injective (by rw [h, map_one])), ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hρ3, map_one]
  · exact (hcρ.map (MulAut.conj d)).eq
  · have h := congrArg (MulAut.conj d) hi
    simp only [map_mul, map_pow, hσz] at h
    rw [inv_pow, hz2] at h
    exact h
  · intro i j
    obtain ⟨h1, h2, h3⟩ := hcomm i j
    rw [← map_pow, ← map_pow, ← map_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hσa]
      exact h1.map (MulAut.conj d)
    · rw [← hσb]
      exact h2.map (MulAut.conj d)
    · rw [← hσc]
      exact h3.map (MulAut.conj d)

@[expose] def mirR (z ρ : G) (i j : ℕ) : G := ρ ^ i * (z * ρ * z ^ 3) ^ j

@[expose] def mirE (z r : G) : G := r * z ^ 2 * r ^ 2

@[expose] def MirRel (g d e : G) : Prop := g * e * d * g * d * e * g * e * d * g * d = 1

theorem mirR_facts {z ρ : G} (hz4 : z ^ 4 = 1) (h3 : ρ ^ 3 = 1)
    (hc : z * ρ * z ^ 3 * ρ = ρ * (z * ρ * z ^ 3)) (hi : z ^ 2 * ρ * z ^ 2 = ρ ^ 2) (i j : ℕ) :
    mirR z ρ i j ^ 3 = 1 ∧ z ^ 2 * mirR z ρ i j * z ^ 2 = (mirR z ρ i j)⁻¹ := by
  have hz3 : z ^ 3 = z⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hz4])
  have hρ2 : ρ ^ 2 = ρ⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h3])
  have h13 : (z * ρ * z ^ 3) ^ 3 = 1 := by rw [hz3, conj_pow, h3, mul_one, mul_inv_cancel]
  have h12 : (z * ρ * z ^ 3) ^ 2 = (z * ρ * z ^ 3)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h13])
  have hcm : Commute ρ (z * ρ * z ^ 3) := hc.symm
  unfold mirR
  refine ⟨?_, ?_⟩
  · rw [(hcm.pow_pow i j).mul_pow, ← pow_mul, mul_comm i 3, pow_mul, h3, one_pow, one_mul,
      ← pow_mul, mul_comm j 3, pow_mul, h13, one_pow]
  · refine conj_inv_of_inv (by rw [← pow_add]; exact hz4) (by rw [hi, hρ2]) ?_ hcm.eq i j
    rw [← h12, hz3]
    calc z ^ 2 * (z * ρ * z⁻¹) * z ^ 2 = z * (z ^ 2 * ρ * z ^ 2) * z⁻¹ := by group
      _ = z * ρ ^ 2 * z⁻¹ := by rw [hi]
      _ = (z * ρ * z⁻¹) ^ 2 := conj_pow.symm

theorem mirE_facts {z r : G} (hz4 : z ^ 4 = 1) (hr3 : r ^ 3 = 1)
    (hzr : z ^ 2 * r * z ^ 2 = r⁻¹) :
    mirE z r * mirE z r = 1 ∧ (mirE z r * z ^ 2) ^ 3 = 1 := by
  have hr2 : r ^ 2 = r⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hr3])
  have hz2i : (z ^ 2)⁻¹ = z ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact hz4)
  unfold mirE
  rw [hr2]
  refine ⟨?_, ?_⟩
  · calc r * z ^ 2 * r⁻¹ * (r * z ^ 2 * r⁻¹) = r * (z ^ 2 * z ^ 2) * r⁻¹ := by group
      _ = 1 := by rw [← pow_add]; rw [show 2 + 2 = 4 from rfl, hz4, mul_one, mul_inv_cancel]
  · have h : r * z ^ 2 * r⁻¹ * z ^ 2 = r * r := by
      calc r * z ^ 2 * r⁻¹ * z ^ 2 = r * (z ^ 2 * r * z ^ 2)⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, hz2i]; simp only [mul_assoc]
        _ = r * r := by rw [hzr, inv_inv]
    rw [h, ← sq, ← pow_mul, mul_comm 2 3, pow_mul, hr3, one_pow]

end GroupLemmas

section Relators

open CFSG.Sporadic.Bridge

@[expose] def onLabel (j : Fin 6) : ℕ := if j.val < 4 then j.val else j.val + 1

@[expose] def seven {H : Type*} [One H] (A B C D E F Gg : H) : ℕ → H := fun n =>
  [A, B, C, D, E, F, Gg].getD n 1

set_option maxRecDepth 20000 in
theorem relatorLetters_split : ∀ v ∈ TauCeti.Sporadic.onanPresentation.relatorLetters,
    (∃ w ∈ cmRelWords, v = w.map fun l => (onLabel l.1, l.2)) ∨
      v = [(4, true), (4, true)] ∨
      v = [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)] ∨
      v = [(4, true), (5, true), (4, true), (5, true), (4, true), (5, true)] ∨
      v = [(0, true), (4, true), (0, true), (4, true)] ∨
      v = [(1, true), (4, true), (1, true), (4, true)] ∨
      v = [(2, true), (4, true), (2, true), (4, true)] ∨
      v = [(6, true), (4, true), (3, false), (6, true), (3, true), (4, false), (6, true),
        (4, true), (3, false), (6, true), (3, true)] := by
  rw [TauCeti.Sporadic.onanPresentation_relatorLetters]
  decide

theorem wordProd_onLabel {H : Type*} [Group H] (Γ : Fin 6 → H) (x : ℕ → H)
    (hx : ∀ j, x (onLabel j) = Γ j) (w : List (Fin 6 × Bool)) :
    wordProd x (w.map fun l => (onLabel l.1, l.2)) = FreeGroup.lift Γ (FreeGroup.mk w) := by
  rw [FreeGroup.lift_mk, wordProd, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun l _ => ?_)
  obtain ⟨j, b⟩ := l
  cases b <;> simp [hx]

theorem relators_of {H : Type*} [Group H] (Γ : Fin 6 → H)
    (hΓ : ∀ r ∈ relsM, FreeGroup.lift Γ r = 1) (E : H) (h1 : E * E = 1)
    (h2 : (Γ 3 * E) ^ 3 = 1) (h3 : (E * Γ 4) ^ 3 = 1) (h4 : Γ 0 * E = E * Γ 0)
    (h5 : Γ 1 * E = E * Γ 1) (h6 : Γ 2 * E = E * Γ 2)
    (h7 : Γ 5 * E * Γ 3 * Γ 5 * Γ 3 * E * Γ 5 * E * Γ 3 * Γ 5 * Γ 3 = 1) :
    ∀ v ∈ TauCeti.Sporadic.onanPresentation.relatorLetters,
      wordProd (seven (Γ 0) (Γ 1) (Γ 2) (Γ 3) E (Γ 4) (Γ 5)) v = 1 := by
  obtain ⟨ha, hb, hc, hd, -, -, -, -, -⟩ := relsM_facts hΓ
  have hx : ∀ j, seven (Γ 0) (Γ 1) (Γ 2) (Γ 3) E (Γ 4) (Γ 5) (onLabel j) = Γ j := by
    intro j
    fin_cases j <;> rfl
  have hdi : (Γ 3)⁻¹ = Γ 3 := inv_eq_of_mul_eq_one_right hd
  have hei : E⁻¹ = E := inv_eq_of_mul_eq_one_right h1
  intro v hv
  rcases relatorLetters_split v hv with ⟨w, hw, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [wordProd_onLabel Γ _ hx]
    exact hΓ _ (by rw [relsM_eq]; exact List.mem_map_of_mem hw)
  · simpa [wordProd, seven] using h1
  · simpa [wordProd, seven, pow_succ, mul_assoc] using h2
  · simpa [wordProd, seven, pow_succ, mul_assoc] using h3
  · simp only [wordProd, seven, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, List.getD_cons_zero, List.getD_cons_succ, ite_true]
    rw [h4, ← mul_assoc E E, h1, one_mul, ha]
  · simp only [wordProd, seven, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, List.getD_cons_zero, List.getD_cons_succ, ite_true]
    rw [h5, ← mul_assoc E E, h1, one_mul, hb]
  · simp only [wordProd, seven, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, List.getD_cons_zero, List.getD_cons_succ, ite_true]
    rw [h6, ← mul_assoc E E, h1, one_mul, hc]
  · simp only [wordProd, seven, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, List.getD_cons_zero, List.getD_cons_succ, ite_true, Bool.false_eq_true,
      ite_false, hdi, hei]
    simpa [mul_assoc] using h7

end Relators

section Mirror

variable {G : Type} [Group G] [Finite G] {f : G} (ψ : centralizer ({f} : Set G) ≃* M480)

theorem mirror_K2
    (hone : OneClass G) (hf : orderOf f = 2) (hdec : CG ψ = R1G ψ ⊔ KG ψ)
    (hinf : R1G ψ ⊓ KG ψ = ⊥) {l : ℕ} (hl : l < 2)
    (hw : ∀ k ∈ KG ψ, emb ψ (yM * fM ^ l) * k = k * emb ψ (yM * fM ^ l))
    {ρ : G} (hρK : ρ ∈ KG ψ) (hρ3 : ρ ^ 3 = 1)
    (hρc : emb ψ zM * ρ * emb ψ zM ^ 3 * ρ = ρ * (emb ψ zM * ρ * emb ψ zM ^ 3))
    (hρi : emb ψ zM ^ 2 * ρ * emb ψ zM ^ 2 = ρ ^ 2)
    (hinj : ∀ i j i' j' : ℕ, i < 3 → j < 3 → i' < 3 → j' < 3 →
      ρ ^ i * (emb ψ zM * ρ * emb ψ zM ^ 3) ^ j =
        ρ ^ i' * (emb ψ zM * ρ * emb ψ zM ^ 3) ^ j' → i = i' ∧ j = j') :
    l = 0 ∧ ∃ K₂ : Subgroup G,
      (∀ k ∈ K₂, ∀ r ∈ closure ({ρ, emb ψ zM * ρ * emb ψ zM ^ 3} : Set G), r * k = k * r) ∧
        emb ψ aM ∈ K₂ ∧ emb ψ bM ∈ K₂ ∧ (emb ψ cM ∈ K₂ ∨ emb ψ (dM * cM * dM) ∈ K₂) := by
  have hz4 : emb ψ zM ^ 4 = 1 := emb_zM_four ψ
  have hzK : emb ψ zM ∈ KG ψ := zG_mem_KG ψ hdec hinf
  have hzu : emb ψ zM * emb ψ (yM * fM ^ l) = emb ψ (yM * fM ^ l) * emb ψ zM := by
    rw [← map_mul, ← map_mul, zM_comm_yfM]
  have hzr : emb ψ zM * emb ψ r1M = emb ψ r1M * emb ψ zM := by
    rw [← map_mul, ← map_mul, zM_r.1]
  have hy4 : emb ψ (yM * fM ^ l) ^ 4 = 1 := by rw [emb_pow_eq_one_iff, yfM_four]
  have hy2 : emb ψ (yM * fM ^ l) ^ 2 ≠ 1 := by
    rw [ne_eq, emb_pow_eq_one_iff, sq]
    exact yfM_sq_ne l
  have hr1 : emb ψ r1M ≠ 1 := fun h => r1M_ne_one ((map_eq_one_iff _ (emb_injective ψ)).1 h)
  have hr13 : emb ψ r1M ^ 3 = 1 := by rw [emb_pow_eq_one_iff, r1M_cube]
  have hur : emb ψ (yM * fM ^ l) * emb ψ r1M * emb ψ (yM * fM ^ l) ^ 3 = emb ψ (r2M ^ 2) := by
    rw [← map_pow, ← map_mul, ← map_mul, u_r1_u3]
  have hu2r : emb ψ (yM * fM ^ l) ^ 2 * emb ψ r1M * emb ψ (yM * fM ^ l) ^ 2 = emb ψ r1M ^ 2 := by
    rw [← map_pow, ← map_mul, ← map_mul, u2_r1_u2, map_pow]
  have hr2r1 : emb ψ (r2M ^ 2) * emb ψ r1M = emb ψ r1M * emb ψ (r2M ^ 2) := by
    rw [← map_mul, ← map_mul, r2M_sq_comm]
  have hc1 : emb ψ r1M = emb ψ (yM * fM ^ l) * emb ψ (r1M * r2M * r2M) *
      (emb ψ (yM * fM ^ l))⁻¹ * (emb ψ (r1M * r2M * r2M))⁻¹ := by
    rw [← emb_comm, conj_yfM, mirrorFacts_cert.comm1]
  have hc2 : emb ψ r2M = emb ψ (yM * fM ^ l) * emb ψ (r1M * r2M) *
      (emb ψ (yM * fM ^ l))⁻¹ * (emb ψ (r1M * r2M))⁻¹ := by
    rw [← emb_comm, conj_yfM, mirrorFacts_cert.comm2]
  have hs1 : emb ψ (r1M * r2M * r2M) ∈ R1G ψ :=
    ⟨_, mul_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
      (subset_closure (by simp)), rfl⟩
  have hs2 : emb ψ (r1M * r2M) ∈ R1G ψ :=
    ⟨_, mul_mem (subset_closure (by simp)) (subset_closure (by simp)), rfl⟩
  have hfz : emb ψ fM = emb ψ zM * emb ψ zM := by rw [← map_mul, zM_sq]
  have hfG : emb ψ fM = f := emb_fM ψ hf
  set zG := emb ψ zM with hzG
  set y' := emb ψ (yM * fM ^ l) with hy'
  set ρ' := zG * ρ * zG ^ 3 with hρ'
  set R₂ := closure ({ρ, ρ'} : Set G) with hR₂
  have hz3 : zG ^ 3 = zG⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hz4])
  have hρ'K : ρ' ∈ KG ψ := mul_mem (mul_mem hzK hρK) (pow_mem hzK 3)
  have hρ'3 : ρ' ^ 3 = 1 := by rw [hρ', hz3, conj_pow, hρ3, mul_one, mul_inv_cancel]
  have hR₂K : R₂ ≤ KG ψ := by
    rw [hR₂, closure_le]
    rintro x (rfl | rfl)
    · exact hρK
    · exact hρ'K
  have hR₂9 : Nat.card R₂ = 9 := card_closure_pair hρ3 hρ'3 hρc.symm hinj
  have ha2 : orderOf (emb ψ aM) = 2 := orderOf_aG ψ
  have hR₂a : R₂ ≤ centralizer ({emb ψ aM} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact (aG_comm_KG ψ hw x (hR₂K hx)).symm
  obtain ⟨ψa⟩ := nonempty_psi_of_oneClass hone hf ψ ha2
  obtain ⟨hdec₂, hinf₂, ⟨eA₂⟩⟩ := threeLocal_gen hone ha2 ψa hR₂a hR₂9
  set K₂ := ⁅centralizer (R₂ : Set G), centralizer (R₂ : Set G)⁆ with hK₂
  have hK₂C : K₂ ≤ centralizer (R₂ : Set G) := Subgroup.commutator_le_self _
  have hcomm₂ : ∀ r ∈ R₂, ∀ k ∈ K₂, r * k = k * r := fun r hr k hk =>
    mem_centralizer_iff.1 (hK₂C hk) r hr
  have hconj : ∀ s ∈ centralizer (R₂ : Set G), ∀ k ∈ K₂, s * k * s⁻¹ ∈ K₂ := fun s hs k hk =>
    conj_mem_commutator_centralizer (centralizer_le_normalizer _ hs) hk
  have hy'C : y' ∈ centralizer (R₂ : Set G) :=
    mem_centralizer_iff.2 fun r hr => (hw r (hR₂K hr)).symm
  have hy'K₂ : y' ∈ K₂ := mem_right_of_pow_two hcomm₂ hinf₂ (by rw [hR₂9]; decide)
    (by rw [← hdec₂]; exact hy'C) (n := 2) (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hy4)
  have hR1C : ∀ x ∈ R1G ψ, x ∈ centralizer (R₂ : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun r hr => (comm_R1G_KG ψ hx (hR₂K hr)).symm
  have hr1K₂ : emb ψ r1M ∈ K₂ := by
    rw [hc1]
    exact mem_of_comm_conj hconj hy'K₂ (hR1C _ hs1)
  have hr2K₂ : emb ψ r2M ∈ K₂ := by
    rw [hc2]
    exact mem_of_comm_conj hconj hy'K₂ (hR1C _ hs2)
  have haK₂ : emb ψ aM ∈ K₂ := by
    rw [emb_aM_eq ψ l]
    exact mul_mem hy'K₂ hy'K₂
  have hbK₂ : emb ψ bM ∈ K₂ := by
    rw [bM_eq, map_mul]
    exact mul_mem haK₂ hr1K₂
  have hzρ : zG * ρ * zG⁻¹ = ρ' := by rw [hρ', hz3]
  have hz2i : zG ^ 2 = zG⁻¹ * zG⁻¹ := by
    rw [← mul_inv_rev, ← sq]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_add, hz4])
  have hzρ' : zG * ρ' * zG⁻¹ = ρ ^ 2 := by
    rw [hρ', hz3]
    calc zG * (zG * ρ * zG⁻¹) * zG⁻¹ = zG ^ 2 * ρ * (zG⁻¹ * zG⁻¹) := by
          rw [sq]; simp only [mul_assoc]
      _ = zG ^ 2 * ρ * zG ^ 2 := by rw [← hz2i]
      _ = ρ ^ 2 := hρi
  have hzN : zG ∈ normalizer (R₂ : Set G) := by
    rw [hR₂]
    refine mem_normalizer_closure_of_conj ?_ ?_
    · rintro x (rfl | rfl)
      · rw [hzρ]
        exact subset_closure (by simp)
      · rw [hzρ']
        exact pow_mem (subset_closure (by simp)) 2
    · rintro x (rfl | rfl)
      · rw [conj_inv_eq_sq hz4 hρi, hzρ]
        exact pow_mem (subset_closure (by simp)) 2
      · rw [show zG⁻¹ * ρ' * zG = ρ by rw [hρ', hz3]; group]
        exact subset_closure (by simp)
  have hzN₂ : zG ∈ normalizer (K₂ : Set G) := mem_normalizer_commutator hzN
  obtain ⟨φ₂⟩ := nonempty_psl29 eA₂
  have h4 : Ord4 ((φ₂ ⟨y', hy'K₂⟩ : ↥A6Models.psl29) : P10) :=
    ord4_of φ₂ ((mk_pow_eq_one hy'K₂ 4).2 hy4) fun h => hy2 ((mk_pow_eq_one hy'K₂ 2).1 h)
  have hpc : PC ((φ₂ ⟨y', hy'K₂⟩ : ↥A6Models.psl29) : P10)
      ((φ₂ ⟨emb ψ r1M, hr1K₂⟩ : ↥A6Models.psl29) : P10) := by
    rw [pc_iff_coe]
    refine ⟨hr1, hr13, ?_, hu2r⟩
    show y' * emb ψ r1M * y' ^ 3 * emb ψ r1M = emb ψ r1M * (y' * emb ψ r1M * y' ^ 3)
    rw [hur, hr2r1]
  have hzK₂ := comm_of_fix φ₂ hzN₂ h4 hpc hzu hzr
  have hK₂f : ∀ k ∈ K₂, k ∈ centralizer ({f} : Set G) := by
    intro k hk
    rw [mem_centralizer_singleton_iff, ← hfG, hfz]
    have e := hzK₂ k hk
    calc k * (zG * zG) = (k * zG) * zG := by group
      _ = (zG * k) * zG := by rw [e]
      _ = zG * (k * zG) := by group
      _ = zG * (zG * k) := by rw [e]
      _ = zG * zG * k := by group
  obtain ⟨w, hw', hdc⟩ := exists_DC (φ₂ ⟨y', hy'K₂⟩).2 h4
  have hφw : ((φ₂ (φ₂.symm ⟨w, hw'⟩) : ↥A6Models.psl29) : P10) = w := by
    rw [MulEquiv.apply_symm_apply]
  rw [← hφw] at hdc
  obtain ⟨hw2, hw1, hwu⟩ := (dc_iff_coe φ₂ _ _).1 hdc
  set wK : K₂ := φ₂.symm ⟨w, hw'⟩ with hwK
  obtain ⟨m, hm⟩ : ∃ m : M480, emb ψ m = wK := ⟨ψ ⟨wK, hK₂f wK wK.2⟩, emb_psi ψ _⟩
  have hm1 : m * m = 1 := emb_injective ψ (by rw [map_mul, hm, map_one, ← sq]; exact hw2)
  have hm2 : m ≠ 1 := fun h => hw1 (by rw [← hm, h, map_one])
  have hmz : m * zM = zM * m := emb_injective ψ (by
    rw [map_mul, map_mul, hm]
    exact (hzK₂ wK wK.2).symm)
  have hmu : m * (yM * fM ^ l) * m = (yM * fM ^ l)⁻¹ := emb_injective ψ (by
    rw [map_mul, map_mul, hm, map_inv]
    exact eq_inv_of_mul_eq_one_left hwu)
  have hcomm' : ∀ k ∈ K₂, ∀ r ∈ R₂, r * k = k * r := fun k hk r hr => hcomm₂ r hr k hk
  rcases mirror_chain hl m hm1 hm2 hmz hmu with ⟨hl0, k, -, hc | hc⟩ | ⟨w', -, hbad⟩
  · refine ⟨hl0, K₂, hcomm', haK₂, hbK₂, Or.inl ?_⟩
    rw [← hc, map_mul, hm, map_pow]
    exact mul_mem wK.2 (pow_mem hy'K₂ k)
  · refine ⟨hl0, K₂, hcomm', haK₂, hbK₂, Or.inr ?_⟩
    rw [← hc, map_mul, hm, map_pow]
    exact mul_mem wK.2 (pow_mem hy'K₂ k)
  · exfalso
    refine not_bad_order φ₂ (emb_evalM_mem ψ hr1K₂ hr2K₂ hy'K₂ (by rw [hm]; exact wK.2) w') ?_
    simp only [ne_eq, emb_pow_eq_one_iff]
    exact hbad

end Mirror

section Final

variable {G : Type} [Group G] [Finite G] {f : G} (ψ : centralizer ({f} : Set G) ≃* M480)

theorem exists_rho0
    (hone : OneClass G) (hf : orderOf f = 2) (hdec : CG ψ = R1G ψ ⊔ KG ψ)
    (hinf : R1G ψ ⊓ KG ψ = ⊥) (eA : KG ψ ≃* alternatingGroup (Fin 6)) {l : ℕ} (hl : l < 2)
    (hw : ∀ k ∈ KG ψ, emb ψ (yM * fM ^ l) * k = k * emb ψ (yM * fM ^ l)) :
    l = 0 ∧ ∃ ρ₀ : G, ρ₀ ∈ KG ψ ∧ ρ₀ ≠ 1 ∧ ρ₀ ^ 3 = 1 ∧
      emb ψ zM * ρ₀ * emb ψ zM ^ 3 * ρ₀ = ρ₀ * (emb ψ zM * ρ₀ * emb ψ zM ^ 3) ∧
      emb ψ zM ^ 2 * ρ₀ * emb ψ zM ^ 2 = ρ₀ ^ 2 ∧
      ∀ i j : ℕ, Commute (ρ₀ ^ i * (emb ψ zM * ρ₀ * emb ψ zM ^ 3) ^ j) (emb ψ aM) ∧
        Commute (ρ₀ ^ i * (emb ψ zM * ρ₀ * emb ψ zM ^ 3) ^ j) (emb ψ bM) ∧
        Commute (ρ₀ ^ i * (emb ψ zM * ρ₀ * emb ψ zM ^ 3) ^ j) (emb ψ cM) := by
  obtain ⟨ρ, hρK, hρ1, hρ3, hρc, hρi, hinj⟩ := exists_rho ψ hdec hinf eA
  obtain ⟨hl0, K₂, hcomm, haK, hbK, hcK | hdcK⟩ :=
    mirror_K2 ψ hone hf hdec hinf hl hw hρK hρ3 hρc hρi hinj
  · refine ⟨hl0, ρ, hρK, hρ1, hρ3, hρc, hρi, fun i j => ?_⟩
    have hr : ρ ^ i * (emb ψ zM * ρ * emb ψ zM ^ 3) ^ j ∈
        closure ({ρ, emb ψ zM * ρ * emb ψ zM ^ 3} : Set G) :=
      mul_mem (pow_mem (subset_closure (by simp)) i) (pow_mem (subset_closure (by simp)) j)
    exact ⟨hcomm _ haK _ hr, hcomm _ hbK _ hr, hcomm _ hcK _ hr⟩
  · have hdK : emb ψ dM ∈ KG ψ := dG_mem_KG ψ hdec hinf
    obtain ⟨h1, h3, hc, hi, hcm⟩ := dconj_facts (d := emb ψ dM) (a := emb ψ aM)
      (b := emb ψ bM) (c := emb ψ cM) (c' := emb ψ (dM * cM * dM)) (emb_zM_four ψ)
      (by rw [← map_mul, dM_sq, map_one]) (by rw [← map_mul, ← map_mul, dM_zM, map_inv])
      (by rw [← map_mul, ← map_mul, aM_dM]) (by rw [← map_mul, ← map_mul, bM_dM])
      (by rw [← map_mul, ← map_mul, dcd_conj]) hρ3 hρ1 hρc hρi (fun i j => by
        have hr : ρ ^ i * ((emb ψ zM * ρ * emb ψ zM ^ 3) ^ 2) ^ j ∈
            closure ({ρ, emb ψ zM * ρ * emb ψ zM ^ 3} : Set G) :=
          mul_mem (pow_mem (subset_closure (by simp)) i)
            (pow_mem (pow_mem (subset_closure (by simp)) 2) j)
        exact ⟨hcomm _ haK _ hr, hcomm _ hbK _ hr, hcomm _ hdcK _ hr⟩)
    exact ⟨hl0, _, mul_mem (mul_mem hdK hρK) hdK, h1, h3, hc, hi, hcm⟩

omit [Finite G] in
open CFSG.GroupTheory.WielandtProduct in
theorem exists_e
    (hdec : CG ψ = R1G ψ ⊔ KG ψ) (hinf : R1G ψ ⊓ KG ψ = ⊥)
    (eA : KG ψ ≃* alternatingGroup (Fin 6))
    (hw : ∀ k ∈ KG ψ, emb ψ (yM * fM ^ 0) * k = k * emb ψ (yM * fM ^ 0))
    {ρ₀ : G} (hρK : ρ₀ ∈ KG ψ) (h1 : ρ₀ ≠ 1) (h3 : ρ₀ ^ 3 = 1)
    (hc : emb ψ zM * ρ₀ * emb ψ zM ^ 3 * ρ₀ = ρ₀ * (emb ψ zM * ρ₀ * emb ψ zM ^ 3))
    (hi : emb ψ zM ^ 2 * ρ₀ * emb ψ zM ^ 2 = ρ₀ ^ 2) :
    ∃ i j : ℕ, (emb ψ dM * mirE (emb ψ zM) (mirR (emb ψ zM) ρ₀ i j)) ^ 3 = 1 ∧
      (MirRel (emb ψ gM) (emb ψ dM) (mirE (emb ψ zM) (mirR (emb ψ zM) ρ₀ i j)) ∨
        MirRel (emb ψ g2M) (emb ψ dM) (mirE (emb ψ zM) (mirR (emb ψ zM) ρ₀ i j))) := by
  obtain ⟨φ⟩ := nonempty_psl29 eA
  have hzK : emb ψ zM ∈ KG ψ := zG_mem_KG ψ hdec hinf
  have hdK : emb ψ dM ∈ KG ψ := dG_mem_KG ψ hdec hinf
  have hfK : emb ψ fM ∈ KG ψ := fG_mem_KG ψ hdec hinf
  have hz4 : emb ψ zM ^ 4 = 1 := emb_zM_four ψ
  have h4 : Ord4 ((φ ⟨_, hzK⟩ : ↥A6Models.psl29) : P10) :=
    ord4_of φ ((mk_pow_eq_one hzK 4).2 hz4) fun h => emb_zM_sq_ne ψ ((mk_pow_eq_one hzK 2).1 h)
  have hdc : DC ((φ ⟨_, hzK⟩ : ↥A6Models.psl29) : P10)
      ((φ ⟨_, hdK⟩ : ↥A6Models.psl29) : P10) := by
    rw [dc_iff_coe]
    refine ⟨?_, ?_, ?_⟩
    · show emb ψ dM ^ 2 = 1
      rw [emb_pow_eq_one_iff, sq, dM_sq]
    · show emb ψ dM ≠ 1
      intro h
      exact dM_ne_zM_pow (k := 0) (by norm_num)
        (by rw [pow_zero]; exact (map_eq_one_iff _ (emb_injective ψ)).1 h)
    · show emb ψ dM * emb ψ zM * emb ψ dM * emb ψ zM = 1
      rw [← map_mul, ← map_mul, ← map_mul, dM_zM, inv_mul_cancel, map_one]
  have hpc : PC ((φ ⟨_, hzK⟩ : ↥A6Models.psl29) : P10)
      ((φ ⟨ρ₀, hρK⟩ : ↥A6Models.psl29) : P10) :=
    (pc_iff_coe φ _ _).2 ⟨h1, h3, hc, hi⟩
  obtain ⟨i, j, hi3, hj3, hde⟩ := exists_rel (φ _).2 (φ _).2 (φ _).2 h4 hdc hpc
  have heq : eOfP ((φ ⟨_, hzK⟩ : ↥A6Models.psl29) : P10)
      (pEltP ((φ ⟨_, hzK⟩ : ↥A6Models.psl29) : P10) ((φ ⟨ρ₀, hρK⟩ : ↥A6Models.psl29) : P10) i j) =
      ((φ ((⟨ρ₀, hρK⟩ ^ i * (⟨_, hzK⟩ * ⟨ρ₀, hρK⟩ * ⟨_, hzK⟩ ^ 3) ^ j) * ⟨_, hzK⟩ ^ 2 *
        (⟨ρ₀, hρK⟩ ^ i * (⟨_, hzK⟩ * ⟨ρ₀, hρK⟩ * ⟨_, hzK⟩ ^ 3) ^ j) ^ 2 : KG ψ) :
          ↥A6Models.psl29) : P10) := by
    rw [pElt_phi, eOf_phi]
  refine ⟨i, j, ?_, ?_⟩
  · have h := hde
    rw [heq, ← coe_phi_mul, ← coe_phi_pow, coe_phi_eq_one] at h
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow, OneMemClass.coe_one] at h'
    exact h'
  have hgT : emb ψ gM ∈ TG ψ := ⟨gM, gM_mem_T0M, rfl⟩
  have hgN : (emb ψ gM)⁻¹ ∈ normalizer (KG ψ : Set G) := inv_mem (TG_le_normalizer_KG ψ hgT)
  obtain ⟨b, hbA, hb⟩ := DoubleA3.exists_aut_model φ (normalizerConj (KG ψ) ⟨_, hgN⟩)
  have hδ : ∀ k : KG ψ, ((normalizerConj (KG ψ) ⟨_, hgN⟩ k : KG ψ) : G) =
      (emb ψ gM)⁻¹ * k * emb ψ gM := by
    intro k
    rw [coe_normalizerConj_apply]
    show (emb ψ gM)⁻¹ * k * ((emb ψ gM)⁻¹)⁻¹ = _
    rw [inv_inv]
  have hgz : (emb ψ gM)⁻¹ * emb ψ zM * emb ψ gM = emb ψ zM ^ 3 := by
    rw [← map_inv, ← map_mul, ← map_mul, mirrorFacts_cert.g_z, map_pow]
  have hgd : (emb ψ gM)⁻¹ * emb ψ dM * emb ψ gM = emb ψ zM * emb ψ dM := by
    rw [← map_inv, ← map_mul, ← map_mul, mirrorFacts_cert.g_d, map_mul]
  have hw0 : emb ψ (yM * fM ^ 0) = emb ψ yM := by rw [pow_zero, mul_one]
  rw [hw0] at hw
  have haK : ∀ k ∈ KG ψ, emb ψ aM * k = k * emb ψ aM := by
    refine aG_comm_KG ψ (l := 0) ?_
    rw [hw0]
    exact hw
  have hfz : emb ψ fM = emb ψ zM ^ 2 := by rw [← map_pow, sq, zM_sq]
  have hai : (emb ψ aM)⁻¹ = emb ψ aM :=
    inv_eq_of_mul_eq_one_right (by rw [← map_mul, aM_sq, map_one])
  have hfi : (emb ψ fM)⁻¹ = emb ψ fM :=
    inv_eq_of_mul_eq_one_right (by rw [← map_mul, fM_sq, map_one])
  have hg2 : emb ψ gM ^ 2 = emb ψ aM * emb ψ fM := by rw [← map_pow, gM_sq, map_mul]
  have hδ2 : ∀ k ∈ KG ψ, ((emb ψ gM)⁻¹) ^ 2 * k * (((emb ψ gM)⁻¹) ^ 2)⁻¹ =
      emb ψ zM ^ 2 * k * emb ψ zM ^ 2 := by
    intro k hk
    rw [inv_pow, inv_inv, hg2, mul_inv_rev, hai, hfi, ← hfz]
    calc emb ψ fM * emb ψ aM * k * (emb ψ aM * emb ψ fM) =
        emb ψ fM * (emb ψ aM * k) * emb ψ aM * emb ψ fM := by simp only [mul_assoc]
      _ = emb ψ fM * (k * emb ψ aM) * emb ψ aM * emb ψ fM := by rw [haK k hk]
      _ = emb ψ fM * k * (emb ψ aM * emb ψ aM) * emb ψ fM := by simp only [mul_assoc]
      _ = emb ψ fM * k * emb ψ fM := by rw [← map_mul, aM_sq, map_one, mul_one]
  have hbc : BC ((φ ⟨_, hzK⟩ : ↥A6Models.psl29) : P10) ((φ ⟨_, hdK⟩ : ↥A6Models.psl29) : P10)
      b := by
    refine ⟨?_, ?_, ?_⟩
    · have h := hb ⟨_, hzK⟩
      have e : normalizerConj (KG ψ) ⟨_, hgN⟩ ⟨_, hzK⟩ = ⟨_, hzK⟩ ^ 3 :=
        Subtype.ext (by rw [hδ, SubgroupClass.coe_pow]; exact hgz)
      rw [e, coe_phi_pow] at h
      exact mul_inv_eq_iff_eq_mul.1 h.symm
    · have h := hb ⟨_, hdK⟩
      have e : normalizerConj (KG ψ) ⟨_, hgN⟩ ⟨_, hdK⟩ = ⟨_, hzK⟩ * ⟨_, hdK⟩ :=
        Subtype.ext (by rw [hδ, Subgroup.coe_mul]; exact hgd)
      rw [e, coe_phi_mul] at h
      exact mul_inv_eq_iff_eq_mul.1 h.symm
    · intro x hx
      have hx' : x ∈ A6Models.psl29 := by
        rw [CFSG.QuasithinUnique.A6Facts.psl29_eq]
        exact subset_closure hx
      have hk : ((φ (φ.symm ⟨x, hx'⟩) : ↥A6Models.psl29) : P10) = x := by
        rw [MulEquiv.apply_symm_apply]
      have h := phi_pow_conj φ _ hb 2 (φ.symm ⟨x, hx'⟩)
      have e : (normalizerConj (KG ψ) ⟨_, hgN⟩ ^ 2) (φ.symm ⟨x, hx'⟩) =
          ⟨_, hzK⟩ ^ 2 * φ.symm ⟨x, hx'⟩ * ⟨_, hzK⟩ ^ 2 :=
        Subtype.ext (by
          rw [coe_normalizerConj_pow, Subgroup.coe_mul, Subgroup.coe_mul, SubgroupClass.coe_pow]
          exact hδ2 _ (φ.symm ⟨x, hx'⟩).2)
      rw [e, coe_phi_mul, coe_phi_mul, coe_phi_pow, hk] at h
      exact mul_inv_eq_iff_eq_mul.1 h.symm
  rcases relP_or hbA (φ _).2 (φ _).2 (φ _).2 h4 hdc hpc hbc hi3 hj3 hde with hR | hR
  · left
    rw [heq] at hR
    have hR' := rel_of_relP φ hgN (by rw [← map_pow, gM_four, map_one]) (pow_120_eq_one hbA) hb hR
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow] at hR'
    unfold MirRel mirE mirR
    exact hR'
  · right
    rw [heq] at hR
    have hg2M : emb ψ g2M = emb ψ gM * emb ψ fM * emb ψ yM ^ 3 := by
      rw [g2M_eq, map_mul, map_mul, map_pow]
    have hg2T : emb ψ g2M ∈ TG ψ :=
      ⟨g2M, by rw [g2M_eq]; exact mul_mem (mul_mem gM_mem_T0M fM_mem_T0M) (pow_mem yM_mem_T0M 3),
        rfl⟩
    have hg2N : (emb ψ g2M)⁻¹ ∈ normalizer (KG ψ : Set G) :=
      inv_mem (TG_le_normalizer_KG ψ hg2T)
    have hu2i : (((φ ⟨_, hzK⟩ : ↥A6Models.psl29) : P10) ^ 2)⁻¹ =
        ((φ ⟨_, hzK⟩ : ↥A6Models.psl29) : P10) ^ 2 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact h4.1)
    have hrep2 : ∀ k : KG ψ, ((φ (normalizerConj (KG ψ) ⟨_, hg2N⟩ k) : ↥A6Models.psl29) : P10) =
        (((φ ⟨_, hzK⟩ : ↥A6Models.psl29) : P10) ^ 2 * b) * (φ k : P10) *
          (((φ ⟨_, hzK⟩ : ↥A6Models.psl29) : P10) ^ 2 * b)⁻¹ := by
      intro k
      have hδk : (emb ψ gM)⁻¹ * k * emb ψ gM ∈ KG ψ := by
        rw [← hδ k]
        exact (normalizerConj (KG ψ) ⟨_, hgN⟩ k).2
      have hX : emb ψ fM * ((emb ψ gM)⁻¹ * k * emb ψ gM) * emb ψ fM ∈ KG ψ :=
        mul_mem (mul_mem hfK hδk) hfK
      have hyX : Commute (emb ψ yM ^ 3)
          (emb ψ fM * ((emb ψ gM)⁻¹ * k * emb ψ gM) * emb ψ fM) :=
        (show Commute (emb ψ yM) _ from hw _ hX).pow_left 3
      have e : normalizerConj (KG ψ) ⟨_, hg2N⟩ k =
          ⟨_, hzK⟩ ^ 2 * normalizerConj (KG ψ) ⟨_, hgN⟩ k * ⟨_, hzK⟩ ^ 2 := by
        apply Subtype.ext
        rw [coe_normalizerConj_apply, Subgroup.coe_mul, Subgroup.coe_mul, hδ,
          SubgroupClass.coe_pow]
        show (emb ψ g2M)⁻¹ * k * ((emb ψ g2M)⁻¹)⁻¹ =
          emb ψ zM ^ 2 * ((emb ψ gM)⁻¹ * k * emb ψ gM) * emb ψ zM ^ 2
        rw [inv_inv, hg2M, ← hfz]
        calc (emb ψ gM * emb ψ fM * emb ψ yM ^ 3)⁻¹ * k * (emb ψ gM * emb ψ fM * emb ψ yM ^ 3) =
            (emb ψ yM ^ 3)⁻¹ * ((emb ψ fM)⁻¹ * ((emb ψ gM)⁻¹ * k * emb ψ gM) * emb ψ fM) *
              emb ψ yM ^ 3 := by group
          _ = (emb ψ yM ^ 3)⁻¹ * ((emb ψ fM * ((emb ψ gM)⁻¹ * k * emb ψ gM) * emb ψ fM) *
              emb ψ yM ^ 3) := by rw [hfi, mul_assoc]
          _ = (emb ψ yM ^ 3)⁻¹ * (emb ψ yM ^ 3 *
              (emb ψ fM * ((emb ψ gM)⁻¹ * k * emb ψ gM) * emb ψ fM)) := by rw [hyX.eq]
          _ = emb ψ fM * ((emb ψ gM)⁻¹ * k * emb ψ gM) * emb ψ fM := by rw [inv_mul_cancel_left]
      rw [e, coe_phi_mul, coe_phi_mul, coe_phi_pow, hb k, mul_inv_rev, hu2i]
      simp only [mul_assoc]
    have hb2A : ((φ ⟨_, hzK⟩ : ↥A6Models.psl29) : P10) ^ 2 * b ∈ A6Models.autA6 :=
      mul_mem (psl29_le_autA6' (pow_mem (φ _).2 2)) hbA
    have hR' := rel_of_relP φ hg2N (by rw [← map_pow, g2M_four, map_one]) (pow_120_eq_one hb2A)
      hrep2 hR
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow] at hR'
    unfold MirRel mirE mirR
    exact hR'

omit [Finite G] in
theorem relators_final {g' : M480}
    (hrel : ∀ r ∈ relsM, FreeGroup.lift ![aM, bM, cM, dM, fM, g'] r = 1) (E : G)
    (h1 : E * E = 1) (h2 : (emb ψ dM * E) ^ 3 = 1) (h3 : (E * emb ψ fM) ^ 3 = 1)
    (h4 : Commute (emb ψ aM) E) (h5 : Commute (emb ψ bM) E) (h6 : Commute (emb ψ cM) E)
    (h7 : MirRel (emb ψ g') (emb ψ dM) E) :
    ∀ v ∈ TauCeti.Sporadic.onanPresentation.relatorLetters,
      CFSG.Sporadic.Bridge.wordProd (seven (emb ψ aM) (emb ψ bM) (emb ψ cM) (emb ψ dM) E
        (emb ψ fM) (emb ψ g')) v = 1 :=
  relators_of (fun j => emb ψ (![aM, bM, cM, dM, fM, g'] j)) (lift_comp_eq_one (emb ψ) hrel) E
    h1 h2 h3 h4 h5 h6 h7

theorem stageB2Loc_holds :
    StageB2Loc CModel := by
  intro G _ _ _ _ hone f hf ⟨e⟩
  set ψ : centralizer ({f} : Set G) ≃* M480 := e.trans CM.equivM480_cert with hψ
  obtain ⟨hdec, hinf, ⟨eA⟩, l, hl, hw⟩ := threeLocal_R1 hone hf ψ
  obtain ⟨hl0, ρ₀, hρK, h1, h3, hc, hi, hcm⟩ := exists_rho0 ψ hone hf hdec hinf eA hl hw
  subst hl0
  obtain ⟨i, j, hde, hR⟩ := exists_e ψ hdec hinf eA hw hρK h1 h3 hc hi
  have hz4 : emb ψ zM ^ 4 = 1 := emb_zM_four ψ
  obtain ⟨hr3, hzr⟩ := mirR_facts hz4 h3 hc hi i j
  obtain ⟨hE2, hEf⟩ := mirE_facts hz4 hr3 hzr
  have hfz : emb ψ fM = emb ψ zM ^ 2 := by rw [← map_pow, sq, zM_sq]
  rw [← hfz] at hEf
  have hcf : ∀ m : M480, Commute (emb ψ m) (emb ψ fM) := fun m => by
    show emb ψ m * emb ψ fM = emb ψ fM * emb ψ m
    rw [← map_mul, ← map_mul, fM_comm]
  have hcE : ∀ m : M480, Commute (mirR (emb ψ zM) ρ₀ i j) (emb ψ m) →
      Commute (emb ψ m) (mirE (emb ψ zM) (mirR (emb ψ zM) ρ₀ i j)) := by
    intro m hm
    unfold mirE
    rw [← hfz]
    exact (hm.symm.mul_right (hcf m)).mul_right (hm.symm.pow_right 2)
  obtain ⟨ha, hb, hc'⟩ := hcm i j
  have hEa := hcE aM ha
  have hEb := hcE bM hb
  have hEc := hcE cM hc'
  rcases hR with hR | hR
  · exact ⟨_, relators_final ψ relsM_genM _ hE2 hde hEf hEa hEb hEc hR, emb_fM ψ hf⟩
  · exact ⟨_, relators_final ψ relsM_gen2M _ hE2 hde hEf hEa hEb hEc hR, emb_fM ψ hf⟩

end Final

end CFSG.OddStandard.ONanRec.B2
