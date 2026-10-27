module

public import CFSG.CGT.Stroth76.PassageX

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77 CFSG.CGT.Stroth77.Arch76

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

theorem frame_coe_eq_of_mk'_eq (O : Subgroup (Subgroup.normalizer (F.A : Set G))) [O.Normal]
    (hO : ¬ 2 ∣ Nat.card O) {x y : Subgroup.normalizer (F.A : Set G)}
    (hx : x ∈ (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))))
    (hy : y ∈ (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))))
    (h : QuotientGroup.mk' O x = QuotientGroup.mk' O y) : (x : G) = (y : G) :=
  congrArg Subtype.val (frame_injOn_sylowN F O hO hx hy h)

theorem frame_map_eq_of_mk'_map_eq (O : Subgroup (Subgroup.normalizer (F.A : Set G)))
    [O.Normal] (hO : ¬ 2 ∣ Nat.card O) {R R' : Subgroup (Subgroup.normalizer (F.A : Set G))}
    (hR : R ≤ (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))))
    (hR' : R' ≤ (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))))
    (h : R.map (QuotientGroup.mk' O) = R'.map (QuotientGroup.mk' O)) :
    R.map (Subgroup.normalizer (F.A : Set G)).subtype =
      R'.map (Subgroup.normalizer (F.A : Set G)).subtype := by
  rw [eq_of_map_eq_of_le_isPGroup hO (frameSylowN F).isPGroup' hR hR' h]

theorem frame_arch76Lemma1 (h11 : ¬ 2 ^ 11 ∣ Nat.card G)
    (hne : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) ≠ F.A) :
    IsMulCommutative (Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) : Subgroup G) ∧
    ((∃ a b : G, Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) =
          Subgroup.closure {F.dA.toConfig.w, a, b} ∧
        a ^ 2 = F.dA.toConfig.x ∧ b ^ 2 = F.dA.toConfig.y ∧
        F.dA.toConfig.uv⁻¹ * a * F.dA.toConfig.uv = F.dA.toConfig.w * a * b ^ 2 ∧
        F.dA.toConfig.uv⁻¹ * b * F.dA.toConfig.uv = F.dA.toConfig.w * b * a ^ 2 ∧
        F.dA.toConfig.t⁻¹ * a * F.dA.toConfig.t = a⁻¹ ∧
        F.dA.toConfig.t⁻¹ * b * F.dA.toConfig.t = F.dA.toConfig.w * b⁻¹ * a⁻¹ ^ 2 ∧
        F.dA.toConfig.u⁻¹ * a * F.dA.toConfig.u = b) ∨
      (∃ a b : G, Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) =
          Subgroup.closure {F.dA.toConfig.w, a, b} ∧
        a ^ 2 = F.dA.toConfig.x ∧ b ^ 2 = F.dA.toConfig.y ∧
        F.dA.toConfig.uv⁻¹ * a * F.dA.toConfig.uv = F.dA.toConfig.w * a ^ 5 * b ^ 2 ∧
        F.dA.toConfig.uv⁻¹ * b * F.dA.toConfig.uv = F.dA.toConfig.w * b ^ 5 * a ^ 2 ∧
        F.dA.toConfig.t⁻¹ * a * F.dA.toConfig.t = a⁻¹ ∧
        F.dA.toConfig.t⁻¹ * b * F.dA.toConfig.t = F.dA.toConfig.w * b ^ 3 * a⁻¹ ^ 2 ∧
        F.dA.toConfig.u⁻¹ * a * F.dA.toConfig.u = b) ∨
      (∃ c : G, Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) =
          Subgroup.closure {c, F.dA.toConfig.x, F.dA.toConfig.y} ∧ c ^ 2 = F.dA.toConfig.w ∧
        F.dA.toConfig.uv⁻¹ * c * F.dA.toConfig.uv =
          c * F.dA.toConfig.x⁻¹ * F.dA.toConfig.y⁻¹ ∧
        F.dA.toConfig.t⁻¹ * c * F.dA.toConfig.t = c * F.dA.toConfig.x ∧
        F.dA.toConfig.u⁻¹ * c * F.dA.toConfig.u = c) ∨
      (∃ c : G, Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) =
          Subgroup.closure {c, F.dA.toConfig.x, F.dA.toConfig.y} ∧ c ^ 2 = F.dA.toConfig.w ∧
        F.dA.toConfig.uv⁻¹ * c * F.dA.toConfig.uv = c * F.dA.toConfig.x * F.dA.toConfig.y⁻¹ ∧
        F.dA.toConfig.t⁻¹ * c * F.dA.toConfig.t =
          c * F.dA.toConfig.x * F.dA.toConfig.y ^ 2 ∧
        F.dA.toConfig.u⁻¹ * c * F.dA.toConfig.u = c⁻¹)) := by
  obtain ⟨O, hON, -, hOodd, hZ⟩ := frame_exists_oddComplement F h11
  haveI := hON
  have hinj := frame_injOn_configN_A F O hOodd
  obtain ⟨-, hshape⟩ := arch76Lemma1 (F.configN.map (QuotientGroup.mk' O) hinj)
    (frame_odd_orderOf_configX_ρ F O hinj) (frame_centralizer_configX F O hOodd hZ hinj)
    (frame_card_map_centralizerN_dvd F O h11 hOodd) (frame_map_centralizerN_ne F O hOodd hne hinj)
    (frame_hE_centralizerX F O hOodd hinj)
  refine ⟨frame_isMulCommutative_centralizer_inf F h11, ?_⟩
  set P := (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))) with hP
  set QN := Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓ P
    with hQN
  have hlift : ∀ {x y : Subgroup.normalizer (F.A : Set G)}, x ∈ P → y ∈ P →
      QuotientGroup.mk' O x = QuotientGroup.mk' O y → (x : G) = (y : G) :=
    fun hx hy h => frame_coe_eq_of_mk'_eq F O hOodd hx hy h
  have hTP : F.configN.A ⊔ Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u} ≤ P :=
    frame_T_le_sylowN F
  have hAP : F.configN.A ≤ P := le_sup_left.trans hTP
  have hwP := hAP F.configN.w_mem
  have hxP := hAP F.configN.x_mem
  have hyP := hAP F.configN.y_mem
  have huvP := hTP F.configN.uv_mem_T
  have htP := hTP F.configN.t_mem_T
  have huP := hTP F.configN.u_mem_T
  have hQP : QN ≤ P := inf_le_right
  have hQG : QN.map (Subgroup.normalizer (F.A : Set G)).subtype =
      Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) :=
    frame_map_centralizer_inf_sylowN F
  have hclosure : ∀ {s : Set (Subgroup.normalizer (F.A : Set G))},
      s ⊆ (QN : Set (Subgroup.normalizer (F.A : Set G))) →
      QN.map (QuotientGroup.mk' O) = Subgroup.closure (QuotientGroup.mk' O '' s) →
      Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) =
        Subgroup.closure ((Subgroup.normalizer (F.A : Set G)).subtype '' s) := by
    intro s hs h
    rw [← MonoidHom.map_closure] at h
    have hsQ : Subgroup.closure s ≤ QN := (Subgroup.closure_le QN).mpr hs
    rw [← hQG, frame_map_eq_of_mk'_map_eq F O hOodd hQP (hsQ.trans hQP) h,
      MonoidHom.map_closure]
  have hwQ : F.configN.w ∈ QN := ⟨F.configN.A_le_centralizer F.configN.w_mem, hwP⟩
  have hxQ : F.configN.x ∈ QN := ⟨F.configN.A_le_centralizer F.configN.x_mem, hxP⟩
  have hyQ : F.configN.y ∈ QN := ⟨F.configN.A_le_centralizer F.configN.y_mem, hyP⟩
  have hmem3 : ∀ {g₁ g₂ g₃ : Subgroup.normalizer (F.A : Set G) ⧸ O},
      QN.map (QuotientGroup.mk' O) = Subgroup.closure {g₁, g₂, g₃} →
      g₁ ∈ QN.map (QuotientGroup.mk' O) ∧ g₂ ∈ QN.map (QuotientGroup.mk' O) ∧
        g₃ ∈ QN.map (QuotientGroup.mk' O) := by
    intro g₁ g₂ g₃ h
    rw [h]
    exact ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
      Subgroup.subset_closure (by simp)⟩
  have hsub3 : ∀ {z₁ z₂ z₃ : Subgroup.normalizer (F.A : Set G)}, z₁ ∈ QN → z₂ ∈ QN → z₃ ∈ QN →
      ({z₁, z₂, z₃} : Set (Subgroup.normalizer (F.A : Set G))) ⊆ QN := by
    intro z₁ z₂ z₃ h₁ h₂ h₃ z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    exacts [h₁, h₂, h₃]
  rcases hshape with ⟨a, b, hC, ha2, hb2, h1, h2, h3, h4, h5, -, -⟩ |
      ⟨a, b, hC, ha2, hb2, h1, h2, h3, h4, h5, -, -⟩ |
      ⟨c, hC, hc2, h1, h2, h3, -⟩ | ⟨c, hC, hc2, h1, h2, h3, -⟩
  · obtain ⟨-, haC, hbC⟩ := hmem3 hC
    obtain ⟨a', ha'Q, rfl⟩ := Subgroup.mem_map.mp haC
    obtain ⟨b', hb'Q, rfl⟩ := Subgroup.mem_map.mp hbC
    have ha'P := hQP ha'Q
    have hb'P := hQP hb'Q
    left
    refine ⟨a', b', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hclosure (hsub3 hwQ ha'Q hb'Q) (by
        rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
        exact hC)
      rw [this, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
      rfl
    · simpa using hlift (pow_mem ha'P 2) hxP (by rw [map_pow]; exact ha2)
    · simpa using hlift (pow_mem hb'P 2) hyP (by rw [map_pow]; exact hb2)
    · simpa using hlift (mul_mem (mul_mem (inv_mem huvP) ha'P) huvP)
        (mul_mem (mul_mem hwP ha'P) (pow_mem hb'P 2))
        (by simp only [map_mul, map_inv, map_pow]; exact h1)
    · simpa using hlift (mul_mem (mul_mem (inv_mem huvP) hb'P) huvP)
        (mul_mem (mul_mem hwP hb'P) (pow_mem ha'P 2))
        (by simp only [map_mul, map_inv, map_pow]; exact h2)
    · simpa using hlift (mul_mem (mul_mem (inv_mem htP) ha'P) htP) (inv_mem ha'P)
        (by simp only [map_mul, map_inv]; exact h3)
    · simpa using hlift (mul_mem (mul_mem (inv_mem htP) hb'P) htP)
        (mul_mem (mul_mem hwP (inv_mem hb'P)) (pow_mem (inv_mem ha'P) 2))
        (by simp only [map_mul, map_inv, map_pow]; exact h4)
    · simpa using hlift (mul_mem (mul_mem (inv_mem huP) ha'P) huP) hb'P
        (by simp only [map_mul, map_inv]; exact h5)
  · obtain ⟨-, haC, hbC⟩ := hmem3 hC
    obtain ⟨a', ha'Q, rfl⟩ := Subgroup.mem_map.mp haC
    obtain ⟨b', hb'Q, rfl⟩ := Subgroup.mem_map.mp hbC
    have ha'P := hQP ha'Q
    have hb'P := hQP hb'Q
    right; left
    refine ⟨a', b', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hclosure (hsub3 hwQ ha'Q hb'Q) (by
        rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
        exact hC)
      rw [this, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
      rfl
    · simpa using hlift (pow_mem ha'P 2) hxP (by rw [map_pow]; exact ha2)
    · simpa using hlift (pow_mem hb'P 2) hyP (by rw [map_pow]; exact hb2)
    · simpa using hlift (mul_mem (mul_mem (inv_mem huvP) ha'P) huvP)
        (mul_mem (mul_mem hwP (pow_mem ha'P 5)) (pow_mem hb'P 2))
        (by simp only [map_mul, map_inv, map_pow]; exact h1)
    · simpa using hlift (mul_mem (mul_mem (inv_mem huvP) hb'P) huvP)
        (mul_mem (mul_mem hwP (pow_mem hb'P 5)) (pow_mem ha'P 2))
        (by simp only [map_mul, map_inv, map_pow]; exact h2)
    · simpa using hlift (mul_mem (mul_mem (inv_mem htP) ha'P) htP) (inv_mem ha'P)
        (by simp only [map_mul, map_inv]; exact h3)
    · simpa using hlift (mul_mem (mul_mem (inv_mem htP) hb'P) htP)
        (mul_mem (mul_mem hwP (pow_mem hb'P 3)) (pow_mem (inv_mem ha'P) 2))
        (by simp only [map_mul, map_inv, map_pow]; exact h4)
    · simpa using hlift (mul_mem (mul_mem (inv_mem huP) ha'P) huP) hb'P
        (by simp only [map_mul, map_inv]; exact h5)
  · obtain ⟨hcC, -, -⟩ := hmem3 hC
    obtain ⟨c', hc'Q, rfl⟩ := Subgroup.mem_map.mp hcC
    have hc'P := hQP hc'Q
    right; right; left
    refine ⟨c', ?_, ?_, ?_, ?_, ?_⟩
    · have := hclosure (hsub3 hc'Q hxQ hyQ) (by
        rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
        exact hC)
      rw [this, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
      rfl
    · simpa using hlift (pow_mem hc'P 2) hwP (by rw [map_pow]; exact hc2)
    · simpa using hlift (mul_mem (mul_mem (inv_mem huvP) hc'P) huvP)
        (mul_mem (mul_mem hc'P (inv_mem hxP)) (inv_mem hyP))
        (by simp only [map_mul, map_inv]; exact h1)
    · simpa using hlift (mul_mem (mul_mem (inv_mem htP) hc'P) htP) (mul_mem hc'P hxP)
        (by simp only [map_mul, map_inv]; exact h2)
    · simpa using hlift (mul_mem (mul_mem (inv_mem huP) hc'P) huP) hc'P
        (by simp only [map_mul, map_inv]; exact h3)
  · obtain ⟨hcC, -, -⟩ := hmem3 hC
    obtain ⟨c', hc'Q, rfl⟩ := Subgroup.mem_map.mp hcC
    have hc'P := hQP hc'Q
    right; right; right
    refine ⟨c', ?_, ?_, ?_, ?_, ?_⟩
    · have := hclosure (hsub3 hc'Q hxQ hyQ) (by
        rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
        exact hC)
      rw [this, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
      rfl
    · simpa using hlift (pow_mem hc'P 2) hwP (by rw [map_pow]; exact hc2)
    · simpa using hlift (mul_mem (mul_mem (inv_mem huvP) hc'P) huvP)
        (mul_mem (mul_mem hc'P hxP) (inv_mem hyP))
        (by simp only [map_mul, map_inv]; exact h1)
    · simpa using hlift (mul_mem (mul_mem (inv_mem htP) hc'P) htP)
        (mul_mem (mul_mem hc'P hxP) (pow_mem hyP 2))
        (by simp only [map_mul, map_inv, map_pow]; exact h2)
    · simpa using hlift (mul_mem (mul_mem (inv_mem huP) hc'P) huP) (inv_mem hc'P)
        (by simp only [map_mul, map_inv]; exact h3)

end CFSG.CGT.Stroth76
