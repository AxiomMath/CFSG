module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_FinalAux

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance

section Omega

theorem i112f_exists_omega {A : Type*} [CommGroup A] [Finite A] {G : Type*} [Group G]
    (φ : A →* G) (p : ℕ) (hker : ∀ a ∈ φ.ker, ∃ b : A, b ^ p = a) :
    ∃ F : Subgroup G, F ≤ φ.range ∧ (∀ x ∈ F, x ^ p = 1) ∧
      Nat.card F = Nat.card (powMonoidHom p : A →* A).ker := by
  set c : A →* A := powMonoidHom p with hc
  set E : Subgroup A := φ.ker.comap c with hE
  refine ⟨E.map φ, Subgroup.map_le_range φ E, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    have h : φ (a ^ p) = 1 := ha
    rwa [map_pow] at h
  · have hkE : φ.ker ≤ E := fun a ha => by
      show φ (a ^ p) = 1
      rw [map_pow, (MonoidHom.mem_ker).1 ha, one_pow]
    have hcE : c.ker ≤ E := fun a ha => by
      show φ (a ^ p) = 1
      have h : a ^ p = 1 := ha
      rw [h, map_one]
    have h1 := Subgroup.card_ker_mul_card_range (φ.domRestrict E)
    have h2 := Subgroup.card_ker_mul_card_range (c.domRestrict E)
    rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range] at h1 h2
    have e1 : Nat.card (φ.ker.subgroupOf E) = Nat.card φ.ker :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkE).toEquiv
    have e2 : Nat.card (c.ker.subgroupOf E) = Nat.card c.ker :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcE).toEquiv
    have e3 : E.map c = φ.ker := by
      refine le_antisymm ?_ fun a ha => ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact ha
      · obtain ⟨b, rfl⟩ := hker a ha
        exact ⟨b, ha, rfl⟩
    rw [e1] at h1
    rw [e2, e3] at h2
    have hpos : 0 < Nat.card φ.ker := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [h1, ← h2, mul_comm]

end Omega

section Nine

abbrev I112fA : Type :=
  Multiplicative (ZMod 9) × Multiplicative (ZMod 9 × ZMod 9) × Multiplicative (ZMod 9 × ZMod 9)

theorem i112f_cube_one (u : Multiplicative (ZMod 9)) (h : u ^ 3 = 1) : ∃ b, b ^ 3 = u := by
  revert u
  decide

theorem i112f_cube_two (u : Multiplicative (ZMod 9 × ZMod 9)) (h : u ^ 3 = 1) :
    ∃ b, b ^ 3 = u := by
  revert u
  decide

theorem i112f_card_ker_pow : Nat.card (powMonoidHom 3 : I112fA →* I112fA).ker = 3 ^ 5 := by
  have hmem : ∀ x : I112fA, x ∈ (powMonoidHom 3 : I112fA →* I112fA).ker ↔
      x.1 ^ 3 = 1 ∧ x.2.1 ^ 3 = 1 ∧ x.2.2 ^ 3 = 1 := by
    intro x
    rw [MonoidHom.mem_ker, powMonoidHom_apply, Prod.ext_iff, Prod.ext_iff]
    simp only [Prod.pow_fst, Prod.pow_snd, Prod.fst_one, Prod.snd_one]
  have e1 : Nat.card {u : Multiplicative (ZMod 9) // u ^ 3 = 1} = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have e2 : Nat.card {u : Multiplicative (ZMod 9 × ZMod 9) // u ^ 3 = 1} = 9 := by
    rw [Nat.card_eq_fintype_card]
    decide
  calc Nat.card (powMonoidHom 3 : I112fA →* I112fA).ker
      = Nat.card {x : I112fA // x.1 ^ 3 = 1 ∧ x.2.1 ^ 3 = 1 ∧ x.2.2 ^ 3 = 1} :=
        Nat.card_congr (Equiv.subtypeEquivRight hmem)
    _ = Nat.card ({u : Multiplicative (ZMod 9) // u ^ 3 = 1} ×
          ({v : Multiplicative (ZMod 9 × ZMod 9) // v ^ 3 = 1} ×
            {w : Multiplicative (ZMod 9 × ZMod 9) // w ^ 3 = 1})) :=
        Nat.card_congr ((Equiv.subtypeProdEquivProd
          (p := fun u : Multiplicative (ZMod 9) => u ^ 3 = 1)
          (q := fun d : Multiplicative (ZMod 9 × ZMod 9) × Multiplicative (ZMod 9 × ZMod 9) =>
            d.1 ^ 3 = 1 ∧ d.2 ^ 3 = 1)).trans
          (Equiv.prodCongr (Equiv.refl _) (Equiv.subtypeProdEquivProd
            (p := fun v : Multiplicative (ZMod 9 × ZMod 9) => v ^ 3 = 1)
            (q := fun w : Multiplicative (ZMod 9 × ZMod 9) => w ^ 3 = 1))))
    _ = 3 ^ 5 := by
        rw [Nat.card_prod, Nat.card_prod, e1, e2]
        norm_num

theorem i112f_exists_rank_five {X : Type*} [Group X] {L₁ L₂ L₃ P Q₂ Q₃ : Subgroup X}
    (h12 : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h13 : ∀ a ∈ L₁, ∀ b ∈ L₃, a * b = b * a)
    (h23 : ∀ a ∈ L₂, ∀ b ∈ L₃, a * b = b * a)
    (hZ₁ : ∀ z ∈ L₁, (∀ g ∈ L₁, g * z = z * g) → z ^ 3 = 1)
    (hZ₂ : ∀ z ∈ L₂, (∀ g ∈ L₂, g * z = z * g) → z ^ 3 = 1)
    (hZ₃ : ∀ z ∈ L₃, (∀ g ∈ L₃, g * z = z * g) → z ^ 3 = 1)
    (hP : P ≤ L₁) (hQ₂ : Q₂ ≤ L₂) (hQ₃ : Q₃ ≤ L₃)
    (eP : Multiplicative (ZMod 9) ≃* P) (e₂ : Multiplicative (ZMod 9 × ZMod 9) ≃* Q₂)
    (e₃ : Multiplicative (ZMod 9 × ZMod 9) ≃* Q₃) :
    ∃ F : Subgroup X, IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 5 ∧
      ∀ f ∈ F, ∃ a ∈ P, ∃ b ∈ Q₂, ∃ c ∈ Q₃, f = a * b * c := by
  set φ₁ : Multiplicative (ZMod 9) →* X := P.subtype.comp eP.toMonoidHom with hφ₁
  set φ₂ : Multiplicative (ZMod 9 × ZMod 9) →* X := Q₂.subtype.comp e₂.toMonoidHom with hφ₂
  set φ₃ : Multiplicative (ZMod 9 × ZMod 9) →* X := Q₃.subtype.comp e₃.toMonoidHom with hφ₃
  have m₁ : ∀ u, φ₁ u ∈ P := fun u => (eP u).2
  have m₂ : ∀ v, φ₂ v ∈ Q₂ := fun v => (e₂ v).2
  have m₃ : ∀ w, φ₃ w ∈ Q₃ := fun w => (e₃ w).2
  have i₁ : Function.Injective φ₁ := Subtype.val_injective.comp eP.injective
  have i₂ : Function.Injective φ₂ := Subtype.val_injective.comp e₂.injective
  have i₃ : Function.Injective φ₃ := Subtype.val_injective.comp e₃.injective
  have c23 : ∀ v w, Commute (φ₂ v) (φ₃ w) := fun v w => h23 _ (hQ₂ (m₂ v)) _ (hQ₃ (m₃ w))
  set φ₂₃ := φ₂.noncommCoprod φ₃ c23 with hφ₂₃
  have c1 : ∀ u vw, Commute (φ₁ u) (φ₂₃ vw) := by
    intro u vw
    rw [hφ₂₃, MonoidHom.noncommCoprod_apply]
    exact Commute.mul_right (h12 _ (hP (m₁ u)) _ (hQ₂ (m₂ vw.1)))
      (h13 _ (hP (m₁ u)) _ (hQ₃ (m₃ vw.2)))
  set φ : I112fA →* X := φ₁.noncommCoprod φ₂₃ c1 with hφ
  have hφapp : ∀ x : I112fA, φ x = φ₁ x.1 * (φ₂ x.2.1 * φ₃ x.2.2) := fun x => by
    rw [hφ, MonoidHom.noncommCoprod_apply, hφ₂₃, MonoidHom.noncommCoprod_apply]
  have hker : ∀ a ∈ φ.ker, ∃ b : I112fA, b ^ 3 = a := by
    rintro ⟨u, v, w⟩ ha
    have ha' : φ₁ u * (φ₂ v * φ₃ w) = 1 := (hφapp (u, v, w)).symm.trans (MonoidHom.mem_ker.1 ha)
    have hbc : φ₂ v * φ₃ w = (φ₁ u)⁻¹ := eq_inv_of_mul_eq_one_right ha'
    have hu : φ₁ u = (φ₂ v * φ₃ w)⁻¹ := eq_inv_of_mul_eq_one_left ha'
    have hv : φ₂ v = (φ₁ u)⁻¹ * (φ₃ w)⁻¹ := eq_mul_inv_of_mul_eq hbc
    have hw : φ₃ w = (φ₂ v)⁻¹ * (φ₁ u)⁻¹ := eq_inv_mul_of_mul_eq hbc
    have hu3 : φ₁ u ^ 3 = 1 := hZ₁ _ (hP (m₁ u)) fun g hg => by
      have c₂ : Commute g (φ₂ v) := h12 g hg _ (hQ₂ (m₂ v))
      have c₃ : Commute g (φ₃ w) := h13 g hg _ (hQ₃ (m₃ w))
      rw [hu]
      exact (c₂.mul_right c₃).inv_right.eq
    have hv3 : φ₂ v ^ 3 = 1 := hZ₂ _ (hQ₂ (m₂ v)) fun g hg => by
      have c₁ : Commute g (φ₁ u) := (show Commute (φ₁ u) g from h12 _ (hP (m₁ u)) g hg).symm
      have c₃ : Commute g (φ₃ w) := h23 g hg _ (hQ₃ (m₃ w))
      rw [hv]
      exact (c₁.inv_right.mul_right c₃.inv_right).eq
    have hw3 : φ₃ w ^ 3 = 1 := hZ₃ _ (hQ₃ (m₃ w)) fun g hg => by
      have c₁ : Commute g (φ₁ u) := (show Commute (φ₁ u) g from h13 _ (hP (m₁ u)) g hg).symm
      have c₂ : Commute g (φ₂ v) := (show Commute (φ₂ v) g from h23 _ (hQ₂ (m₂ v)) g hg).symm
      rw [hw]
      exact (c₂.inv_right.mul_right c₁.inv_right).eq
    obtain ⟨u', hu'⟩ := i112f_cube_one u (i₁ (by rw [map_pow, hu3, map_one]))
    obtain ⟨v', hv'⟩ := i112f_cube_two v (i₂ (by rw [map_pow, hv3, map_one]))
    obtain ⟨w', hw'⟩ := i112f_cube_two w (i₃ (by rw [map_pow, hw3, map_one]))
    exact ⟨(u', v', w'), by rw [Prod.pow_mk, Prod.pow_mk, hu', hv', hw']⟩
  obtain ⟨F, hFr, hF3, hFc⟩ := i112f_exists_omega φ 3 hker
  refine ⟨F, isElemAbelian_of_forall (fun a ha b hb => ?_) hF3, by rw [hFc, i112f_card_ker_pow],
    fun f hf => ?_⟩
  · obtain ⟨s, rfl⟩ := hFr ha
    obtain ⟨t, rfl⟩ := hFr hb
    rw [← map_mul, ← map_mul, mul_comm]
  · obtain ⟨⟨u, v, w⟩, rfl⟩ := hFr hf
    exact ⟨φ₁ u, m₁ u, φ₂ v, m₂ v, φ₃ w, m₃ w, by rw [hφapp, mul_assoc]⟩

end Nine

section Situ

variable {X : Type} [Group X] [Finite X] {B L : Subgroup X}

theorem i112f_three_commute (hB : IsElemAbelian 3 B) (hL : CFSG.Open.IsComponentOf L ⊤) {x : X}
    (hxB : x ∈ B) (hxn : x ∉ Subgroup.normalizer (L : Set X)) :
    (∀ a ∈ L, ∀ b ∈ GLBConj x L, a * b = b * a) ∧
      (∀ a ∈ L, ∀ b ∈ GLBConj (x ^ 2) L, a * b = b * a) ∧
      (∀ a ∈ GLBConj x L, ∀ b ∈ GLBConj (x ^ 2) L, a * b = b * a) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have h0 : GLBConj (x ^ 0) L = L := by rw [pow_zero, gLBConj_one]
  have h1 : GLBConj (x ^ 1) L = GLBConj x L := by rw [pow_one]
  have hm : ∀ i : ℕ, GLBConj (x ^ i) L ∈ i112Orbit B L := fun i =>
    i112_gLBConj_mem_orbit (B.pow_mem hxB i)
  have hne : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → GLBConj (x ^ i) L ≠ GLBConj (x ^ j) L :=
    fun i j hi hj hij h => hij (i112_conj_pow_injOn hp hB hxB hxn hi hj h)
  have hc : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j →
      ∀ a ∈ GLBConj (x ^ i) L, ∀ b ∈ GLBConj (x ^ j) L, a * b = b * a := by
    intro i j hi hj hij
    exact (i112_conj_eq_or_commute hL (hm i) (hm j)).resolve_left (hne i j hi hj hij)
  refine ⟨?_, ?_, ?_⟩
  · have := hc 0 1 (by norm_num) (by norm_num) (by norm_num)
    rwa [h0, h1] at this
  · have := hc 0 2 (by norm_num) (by norm_num) (by norm_num)
    rwa [h0] at this
  · have := hc 1 2 (by norm_num) (by norm_num) (by norm_num)
    rwa [h1] at this

theorem i112f_central_pow (hL : CFSG.Open.IsComponentOf L ⊤)
    (hZ3 : Nat.card ↥(Subgroup.center ↥L) = 3)
    {M : Subgroup X} (hM : M ∈ i112Orbit B L) {z : X} (hz : z ∈ M)
    (hc : ∀ g ∈ M, g * z = z * g) : z ^ 3 = 1 :=
  (i112_isElemAbelian_Z (B := B) hL (Or.inr hZ3)).2 z
    (i112_centreIn_le_Z hL hM (mem_centreIn.2 ⟨hz, hc⟩))

omit [Finite X] in
theorem i112f_mem_normalizer_of_commute {T : Subgroup ↥L} {y : X}
    (hy : ∀ l ∈ L, l * y = y * l) :
    y ∈ Subgroup.normalizer ((T.map L.subtype : Subgroup X) : Set X) := by
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact hy t (Subgroup.map_subtype_le T ht)

theorem i112f_exists_rank_five_J (hB : IsElemAbelian 3 B) (hL : CFSG.Open.IsComponentOf L ⊤)
    (hZ3 : Nat.card ↥(Subgroup.center ↥L) = 3) {x : X} (hxB : x ∈ B)
    (hxn : x ∉ Subgroup.normalizer (L : Set X)) {T P Q : Subgroup ↥L}
    (hPT : P ≤ Subgroup.normalizer (T : Set ↥L))
    (eP : Multiplicative (ZMod 9) ≃* P) (eQ : Multiplicative (ZMod 9 × ZMod 9) ≃* Q) :
    ∃ F : Subgroup X, IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 5 ∧ F ≤ i112J B L ∧
      F ≤ Subgroup.normalizer ((T.map L.subtype : Subgroup X) : Set X) ∧
      ∀ f ∈ F, ∃ a ∈ P.map L.subtype, ∃ b ∈ GLBConj x (Q.map L.subtype),
        ∃ c ∈ GLBConj (x ^ 2) (Q.map L.subtype), Commute a b ∧ Commute a c ∧ Commute b c ∧
          f = a * b * c := by
  obtain ⟨h12, h13, h23⟩ := i112f_three_commute hB hL hxB hxn
  have m1 : L ∈ i112Orbit B L := i112_self_mem_orbit
  have m2 : GLBConj x L ∈ i112Orbit B L := i112_gLBConj_mem_orbit hxB
  have m3 : GLBConj (x ^ 2) L ∈ i112Orbit B L := i112_gLBConj_mem_orbit (B.pow_mem hxB 2)
  have hP1 : P.map L.subtype ≤ L := Subgroup.map_subtype_le P
  have hQ2 : GLBConj x (Q.map L.subtype) ≤ GLBConj x L :=
    gLBConj_mono x (Subgroup.map_subtype_le Q)
  have hQ3 : GLBConj (x ^ 2) (Q.map L.subtype) ≤ GLBConj (x ^ 2) L :=
    gLBConj_mono (x ^ 2) (Subgroup.map_subtype_le Q)
  let eQL : Multiplicative (ZMod 9 × ZMod 9) ≃* ↥(Q.map L.subtype) :=
    eQ.trans (Q.equivMapOfInjective L.subtype L.subtype_injective)
  let eP' : Multiplicative (ZMod 9) ≃* ↥(P.map L.subtype) :=
    eP.trans (P.equivMapOfInjective L.subtype L.subtype_injective)
  let eQ2 : Multiplicative (ZMod 9 × ZMod 9) ≃* ↥(GLBConj x (Q.map L.subtype)) :=
    eQL.trans ((Q.map L.subtype).equivMapOfInjective (MulAut.conj x⁻¹).toMonoidHom
      (MulAut.conj x⁻¹).injective)
  let eQ3 : Multiplicative (ZMod 9 × ZMod 9) ≃* ↥(GLBConj (x ^ 2) (Q.map L.subtype)) :=
    eQL.trans ((Q.map L.subtype).equivMapOfInjective (MulAut.conj (x ^ 2)⁻¹).toMonoidHom
      (MulAut.conj (x ^ 2)⁻¹).injective)
  obtain ⟨F, hFa, hFc, hF⟩ := i112f_exists_rank_five h12 h13 h23
    (fun z hz hc => i112f_central_pow hL hZ3 m1 hz hc)
    (fun z hz hc => i112f_central_pow hL hZ3 m2 hz hc)
    (fun z hz hc => i112f_central_pow hL hZ3 m3 hz hc) hP1 hQ2 hQ3 eP' eQ2 eQ3
  refine ⟨F, hFa, hFc, fun f hf => ?_, fun f hf => ?_, fun f hf => ?_⟩
  · obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hF f hf
    exact mul_mem (mul_mem (i112_orbit_le_J m1 (hP1 ha)) (i112_orbit_le_J m2 (hQ2 hb)))
      (i112_orbit_le_J m3 (hQ3 hc))
  · obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hF f hf
    refine mul_mem (mul_mem ?_ ?_) ?_
    · obtain ⟨a₀, ha₀, rfl⟩ := ha
      exact mem_normalizer_map_subtype (hPT ha₀)
    · exact i112f_mem_normalizer_of_commute fun l hl => h12 l hl b (hQ2 hb)
    · exact i112f_mem_normalizer_of_commute fun l hl => h13 l hl c (hQ3 hc)
  · obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hF f hf
    exact ⟨a, ha, b, hb, c, hc, h12 a (hP1 ha) b (hQ2 hb), h13 a (hP1 ha) c (hQ3 hc),
      h23 b (hQ2 hb) c (hQ3 hc), rfl⟩

omit [Finite X] in
theorem i112f_commute_of_powerMap (hB : IsElemAbelian 3 B) {x : X} (hxB : x ∈ B)
    {y : ↥(i112A B L)} {P Q : Subgroup ↥L} (hPQ : P ≤ Q) {k : ℕ}
    (hk : ∀ q ∈ Q, i112Act B L y q = q ^ k) (hk3 : k % 3 = 1) {a b c : X}
    (ha : a ∈ P.map L.subtype) (hb : b ∈ GLBConj x (Q.map L.subtype))
    (hc : c ∈ GLBConj (x ^ 2) (Q.map L.subtype)) (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (hf3 : (a * b * c) ^ 3 = 1) :
    (a * b * c) * (y : X) = (y : X) * (a * b * c) := by
  have hyB : (y : X) ∈ B := i112A_le_B y.2
  have hQk : ∀ q ∈ Q.map L.subtype, (y : X) * q * (y : X)⁻¹ = q ^ k := by
    rintro _ ⟨q, hq, rfl⟩
    have h := congrArg Subtype.val (hk q hq)
    rw [i112Act_apply] at h
    change (y : X) * (q : X) * (y : X)⁻¹ = (q : X) ^ k
    simpa using h
  have hconj : ∀ g ∈ B, ∀ d ∈ GLBConj g (Q.map L.subtype),
      (y : X) * d * (y : X)⁻¹ = d ^ k := by
    intro g hg d hd
    have h1 := hQk _ (mem_gLBConj.1 hd)
    have hyg : (y : X) * g = g * (y : X) := i116pI_comm hB hyB hg
    have hyg' : g⁻¹ * (y : X)⁻¹ = (y : X)⁻¹ * g⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hyg]
    have h2 : (y : X) * (g * d * g⁻¹) * (y : X)⁻¹ = g * ((y : X) * d * (y : X)⁻¹) * g⁻¹ := by
      calc (y : X) * (g * d * g⁻¹) * (y : X)⁻¹
          = ((y : X) * g) * d * (g⁻¹ * (y : X)⁻¹) := by group
        _ = (g * (y : X)) * d * ((y : X)⁻¹ * g⁻¹) := by rw [hyg, hyg']
        _ = g * ((y : X) * d * (y : X)⁻¹) * g⁻¹ := by group
    rw [h2, conj_pow] at h1
    simpa using h1
  have hya : (y : X) * a * (y : X)⁻¹ = a ^ k := by
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    exact hQk _ ⟨a₀, hPQ ha₀, rfl⟩
  have hyb := hconj x hxB b hb
  have hyc := hconj (x ^ 2) (B.pow_mem hxB 2) c hc
  have hf : (y : X) * (a * b * c) * (y : X)⁻¹ = (a * b * c) ^ k := by
    calc (y : X) * (a * b * c) * (y : X)⁻¹
        = ((y : X) * a * (y : X)⁻¹) * ((y : X) * b * (y : X)⁻¹) *
            ((y : X) * c * (y : X)⁻¹) := by group
      _ = a ^ k * b ^ k * c ^ k := by rw [hya, hyb, hyc]
      _ = (a * b * c) ^ k := by rw [(hac.mul_left hbc).mul_pow, hab.mul_pow]
  rw [pow_eq_pow_mod k hf3, hk3, pow_one, mul_inv_eq_iff_eq_mul] at hf
  exact hf.symm

theorem i112f_mod_three {M : Type*} [Group M] {Q : Subgroup M}
    (eQ : Multiplicative (ZMod 9 × ZMod 9) ≃* Q) {ψ : MulAut M} (hψ : ψ ^ 3 = 1) {k : ℕ}
    (hk : ∀ q ∈ Q, ψ q = q ^ k) : k % 3 = 1 := by
  set q₀ : M := (eQ (Multiplicative.ofAdd ((3 : ZMod 9), (0 : ZMod 9))) : M) with hq₀
  have hq₀Q : q₀ ∈ Q := (eQ _).2
  have hq₀3 : q₀ ^ 3 = 1 := by
    have h : (Multiplicative.ofAdd ((3 : ZMod 9), (0 : ZMod 9))) ^ 3 = 1 := by decide
    rw [hq₀, ← Subgroup.coe_pow, ← map_pow, h, map_one, Subgroup.coe_one]
  have hq₀1 : q₀ ≠ 1 := by
    intro h
    have h1 : eQ (Multiplicative.ofAdd ((3 : ZMod 9), (0 : ZMod 9))) = 1 := Subtype.ext h
    rw [← map_one eQ] at h1
    exact absurd (eQ.injective h1) (by decide)
  have hpow : ∀ n : ℕ, ∀ q ∈ Q, (ψ ^ n) q = q ^ k ^ n := by
    intro n
    induction n with
    | zero => intro q _; simp
    | succ n ih =>
      intro q hq
      rw [pow_succ', MulAut.mul_apply, ih q hq, map_pow, hk q hq, ← pow_mul, ← pow_succ']
  have h3 := hpow 3 q₀ hq₀Q
  rw [hψ, MulAut.one_apply, pow_eq_pow_mod _ hq₀3] at h3
  have hk3 : k ^ 3 % 3 = k % 3 := by
    rw [Nat.pow_mod]
    have : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases (k % 3) <;> rfl
  rw [hk3] at h3
  have : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hkk : (k % 3)
  · exact absurd (by simpa using h3) hq₀1
  · rfl
  · exfalso
    apply hq₀1
    have h4 : q₀ * q₀ = q₀ * 1 := by rw [mul_one, ← sq]; exact h3.symm
    exact mul_left_cancel h4

theorem i112f_count_five (hB : IsElemAbelian 3 B) (hL : CFSG.Open.IsComponentOf L ⊤)
    (hZ3 : Nat.card ↥(Subgroup.center ↥L) = 3) (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X))
    {T P Q : Subgroup ↥L} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hPT : P ≤ Subgroup.normalizer (T : Set ↥L))
    (eP : Multiplicative (ZMod 9) ≃* P) (eQ : Multiplicative (ZMod 9 × ZMod 9) ≃* Q) :
    5 + CFSG.Open.pRank 3 (i112Bc B L) ≤ GLATwoLocalRank 3 X +
      CFSG.Open.pRank 3 ((i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓ B) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨x, hxB, hxn⟩ := IsConcreteLE.not_le_iff_exists.1 hnL
  obtain ⟨F, hFa, hFc, hFJ, hFN, -⟩ := i112f_exists_rank_five_J hB hL hZ3 hxB hxn hPT eP eQ
  set T₁ : Subgroup X := T.map L.subtype with hT₁def
  have hT₁ : T₁ ≠ ⊥ := fun h =>
    hT ((Subgroup.map_eq_bot_iff_of_injective T L.subtype_injective).1 h)
  have hT₁2 : IsPGroup 2 T₁ := hT2.map _
  have hBc : IsElemAbelian 3 (i112Bc B L) := isElemAbelian_of_le hB i112Bc_le_B
  obtain ⟨b, hb⟩ := exists_card_eq_of_isElemAbelian hp hBc
  have hBcJ : i112Bc B L ≤ Subgroup.centralizer (i112J B L : Set X) := inf_le_right
  have hcomm : ∀ u ∈ F, ∀ v ∈ i112Bc B L, u * v = v * u := fun u hu v hv =>
    Subgroup.mem_centralizer_iff.1 (hBcJ hv) u (hFJ hu)
  have hW : F ⊓ i112Bc B L ≤ (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓ B := by
    intro u hu
    obtain ⟨huF, huC⟩ := Subgroup.mem_inf.1 hu
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hFJ huF, hBcJ huC⟩, i112Bc_le_B huC⟩
  have hJT : Subgroup.centralizer (i112J B L : Set X) ≤ Subgroup.centralizer (T₁ : Set X) :=
    Subgroup.centralizer_le fun u hu =>
      i112_orbit_le_J (M := L) i112_self_mem_orbit (Subgroup.map_subtype_le T hu)
  have hN : F ⊔ i112Bc B L ≤ Subgroup.normalizer (T₁ : Set X) :=
    sup_le hFN (hBcJ.trans (hJT.trans (Subgroup.centralizer_le_normalizer _)))
  have h := rank_combine hp hT₁ hT₁2 hFa hBc hcomm hW le_rfl hN hFc hb
  rw [pRank_eq_of_card hp.one_lt hBc hb]
  exact h

theorem i112f_count_six (hB : IsElemAbelian 3 B) (hL : CFSG.Open.IsComponentOf L ⊤)
    (hZ3 : Nat.card ↥(Subgroup.center ↥L) = 3) (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X))
    {T P Q : Subgroup ↥L} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hPT : P ≤ Subgroup.normalizer (T : Set ↥L))
    (eP : Multiplicative (ZMod 9) ≃* P) (eQ : Multiplicative (ZMod 9 × ZMod 9) ≃* Q)
    (hPQ : P ≤ Q) {y : ↥(i112A B L)} (hy : ¬ IsInnerAut (i112Act B L y))
    (hyT : T.map (i112Act B L y).toMonoidHom = T) {k : ℕ}
    (hk : ∀ q ∈ Q, i112Act B L y q = q ^ k) :
    6 + CFSG.Open.pRank 3 (i112Bc B L) ≤ GLATwoLocalRank 3 X +
      CFSG.Open.pRank 3 ((i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓ B) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hyB : (y : X) ∈ B := i112A_le_B y.2
  have hy3 : (y : X) ^ 3 = 1 := hB.2 y hyB
  have hψ3 : (i112Act B L y) ^ 3 = 1 := by
    rw [← map_pow]
    have : y ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hk3 := i112f_mod_three eQ hψ3 hk
  obtain ⟨x, hxB, hxn⟩ := IsConcreteLE.not_le_iff_exists.1 hnL
  obtain ⟨F, hFa, hFc, hFJ, hFN, hF⟩ := i112f_exists_rank_five_J hB hL hZ3 hxB hxn hPT eP eQ
  have hFy : ∀ f ∈ F, f * (y : X) = (y : X) * f := by
    intro f hf
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, rfl⟩ := hF f hf
    exact i112f_commute_of_powerMap hB hxB hPQ hk hk3 ha hb hc hab hac hbc (hFa.2 _ hf)
  set T₁ : Subgroup X := T.map L.subtype with hT₁def
  have hT₁ : T₁ ≠ ⊥ := fun h =>
    hT ((Subgroup.map_eq_bot_iff_of_injective T L.subtype_injective).1 h)
  have hT₁2 : IsPGroup 2 T₁ := hT2.map _
  have hyN : (y : X) ∈ Subgroup.normalizer (T₁ : Set X) := i112_mem_normalizer_map hyT
  have hzp : IsElemAbelian 3 (Subgroup.zpowers (y : X)) := by
    refine isElemAbelian_of_forall (fun a ha b hb => ?_) (fun u hu => ?_)
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow_self (y : X) i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hF'a : IsElemAbelian 3 (F ⊔ Subgroup.zpowers (y : X)) :=
    isElemAbelian_sup_of_commute hFa hzp (fun f hf b hb => by
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (hFy f hf : Commute f (y : X)) z).eq)
  have hLc := hL
  have hF'card : Nat.card ↥(F ⊔ Subgroup.zpowers (y : X)) = 3 ^ (5 + 1) := by
    rw [i112_card_sup_zpowers hp hB hLc hy hFJ hFy, hFc]
    norm_num
  have hF'N : F ⊔ Subgroup.zpowers (y : X) ≤ Subgroup.normalizer (T₁ : Set X) :=
    sup_le hFN (Subgroup.zpowers_le.2 hyN)
  have hBc : IsElemAbelian 3 (i112Bc B L) := isElemAbelian_of_le hB i112Bc_le_B
  obtain ⟨b, hb⟩ := exists_card_eq_of_isElemAbelian hp hBc
  have hBcJ : i112Bc B L ≤ Subgroup.centralizer (i112J B L : Set X) := inf_le_right
  have hF'cent : F ⊔ Subgroup.zpowers (y : X) ≤ Subgroup.centralizer (i112Bc B L : Set X) := by
    refine sup_le (fun f hf => ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (Subgroup.mem_centralizer_iff.1 (hBcJ hc) f (hFJ hf)).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact i116pI_comm hB (i112Bc_le_B hc) hyB
  have hcomm : ∀ u ∈ F ⊔ Subgroup.zpowers (y : X), ∀ c ∈ i112Bc B L, u * c = c * u :=
    fun u hu c hc => (Subgroup.mem_centralizer_iff.1 (hF'cent hu) c hc).symm
  have hW : (F ⊔ Subgroup.zpowers (y : X)) ⊓ i112Bc B L ≤
      (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓ B := by
    intro u hu
    have huF := i112_inf_Bc_le hp hB hLc hy hFJ hFy hu
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hFJ huF, hBcJ (Subgroup.mem_inf.1 hu).2⟩,
      i112Bc_le_B (Subgroup.mem_inf.1 hu).2⟩
  have hJT : Subgroup.centralizer (i112J B L : Set X) ≤ Subgroup.centralizer (T₁ : Set X) :=
    Subgroup.centralizer_le fun u hu =>
      i112_orbit_le_J (M := L) i112_self_mem_orbit (Subgroup.map_subtype_le T hu)
  have hN : (F ⊔ Subgroup.zpowers (y : X)) ⊔ i112Bc B L ≤ Subgroup.normalizer (T₁ : Set X) :=
    sup_le hF'N (hBcJ.trans (hJT.trans (Subgroup.centralizer_le_normalizer _)))
  have h := rank_combine hp hT₁ hT₁2 hF'a hBc hcomm hW le_rfl hN hF'card hb
  rw [pRank_eq_of_card hp.one_lt hBc hb]
  omega

end Situ

end CFSG.HardMathSupport.Solomon.Coordinator
