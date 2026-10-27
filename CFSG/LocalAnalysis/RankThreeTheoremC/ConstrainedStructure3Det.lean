module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Matrix CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.SectionRank.Ccomm
open scoped commutatorElement

section ClassTwo

variable {G : Type*} [Group G]

theorem classTwo_comm_mul_left (hc : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G) (x y w : G) :
    ⁅x * y, w⁆ = ⁅x, w⁆ * ⁅y, w⁆ := by
  have h1 : ∀ g : G, g * ⁅y, w⁆ = ⁅y, w⁆ * g := fun g => Subgroup.mem_center_iff.mp (hc y w) g
  have h2 : ∀ g : G, g * ⁅x, w⁆ = ⁅x, w⁆ * g := fun g => Subgroup.mem_center_iff.mp (hc x w) g
  simp only [commutatorElement_def] at h1 h2 ⊢
  calc x * y * w * (x * y)⁻¹ * w⁻¹ = x * (y * w * y⁻¹ * w⁻¹) * (w * x⁻¹ * w⁻¹) := by group
    _ = (y * w * y⁻¹ * w⁻¹) * x * (w * x⁻¹ * w⁻¹) := by rw [h1]
    _ = (y * w * y⁻¹ * w⁻¹) * (x * w * x⁻¹ * w⁻¹) := by group
    _ = (x * w * x⁻¹ * w⁻¹) * (y * w * y⁻¹ * w⁻¹) := by
      rw [← h2 (y * w * y⁻¹ * w⁻¹)]

theorem classTwo_comm_mul_right (hc : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G) (x y w : G) :
    ⁅x, y * w⁆ = ⁅x, y⁆ * ⁅x, w⁆ := by
  have h := Subgroup.mem_center_iff.mp (hc x y) ⁅x, w⁆
  rw [← commutatorElement_inv, classTwo_comm_mul_left hc, _root_.mul_inv_rev, commutatorElement_inv,
    commutatorElement_inv]
  exact h

theorem classTwo_comm_pow_left (hc : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G) (x w : G) (n : ℕ) :
    ⁅x ^ n, w⁆ = ⁅x, w⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, classTwo_comm_mul_left hc, ih, pow_succ]

theorem classTwo_comm_pow_right (hc : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G) (x w : G) (n : ℕ) :
    ⁅x, w ^ n⁆ = ⁅x, w⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, classTwo_comm_mul_right hc, ih, pow_succ]

theorem classTwo_comm_expand (hc : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G) (a b : G)
    (m n k l : ℕ) :
    ⁅a ^ m * b ^ n, a ^ k * b ^ l⁆ = ⁅a, b⁆ ^ (m * l) * (⁅a, b⁆⁻¹) ^ (n * k) := by
  rw [classTwo_comm_mul_left hc, classTwo_comm_mul_right hc, classTwo_comm_mul_right hc,
    classTwo_comm_pow_left hc, classTwo_comm_pow_left hc, classTwo_comm_pow_left hc,
    classTwo_comm_pow_left hc, classTwo_comm_pow_right hc, classTwo_comm_pow_right hc,
    classTwo_comm_pow_right hc, classTwo_comm_pow_right hc]
  rw [commutatorElement_self, commutatorElement_self, one_pow, one_pow, one_pow, one_pow, one_mul,
    mul_one, ← pow_mul, ← pow_mul, ← commutatorElement_inv a b, inv_pow, mul_comm l m,
    ← inv_pow, mul_comm k n]

theorem classTwo_comm_central_left (hc : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G) {z : G}
    (hz : z ∈ Subgroup.center G) (x y : G) : ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have := Subgroup.mem_center_iff.mp hz y
  rw [classTwo_comm_mul_left hc, commutatorElement_eq_one_iff_mul_comm.mpr this.symm, mul_one]

theorem classTwo_comm_central_right (hc : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G) {z : G}
    (hz : z ∈ Subgroup.center G) (x y : G) : ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have := Subgroup.mem_center_iff.mp hz x
  rw [classTwo_comm_mul_right hc, commutatorElement_eq_one_iff_mul_comm.mpr this, mul_one]

end ClassTwo

section Coordinates

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

theorem exists_mem_center_coord (e : G ⧸ Subgroup.center G ≃* Multiplicative (Fin 2 → ZMod p))
    (a b : G) (ha : e (a : G ⧸ Subgroup.center G) = Multiplicative.ofAdd (Pi.single 0 1))
    (hb : e (b : G ⧸ Subgroup.center G) = Multiplicative.ofAdd (Pi.single 1 1)) (u : G) :
    ∃ z' ∈ Subgroup.center G,
      u = a ^ (Multiplicative.toAdd (e (u : G ⧸ Subgroup.center G)) 0).val *
        b ^ (Multiplicative.toAdd (e (u : G ⧸ Subgroup.center G)) 1).val * z' := by
  set w := Multiplicative.toAdd (e (u : G ⧸ Subgroup.center G)) with hw
  have h1 : e ((a ^ (w 0).val * b ^ (w 1).val : G) : G ⧸ Subgroup.center G) =
      e (u : G ⧸ Subgroup.center G) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow, map_mul, map_pow,
      map_pow, ha, hb]
    apply Multiplicative.toAdd.injective
    ext r
    fin_cases r <;> simp [hw, -ZMod.natCast_val, ZMod.natCast_zmod_val]
  have h2 := e.injective h1
  rw [QuotientGroup.eq] at h2
  exact ⟨_, h2, by group⟩

theorem commutator_coord (hc : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G)
    (e : G ⧸ Subgroup.center G ≃* Multiplicative (Fin 2 → ZMod p))
    (a b : G) (ha : e (a : G ⧸ Subgroup.center G) = Multiplicative.ofAdd (Pi.single 0 1))
    (hb : e (b : G ⧸ Subgroup.center G) = Multiplicative.ofAdd (Pi.single 1 1)) (u v : G) :
    ⁅u, v⁆ = ⁅a, b⁆ ^ ((Multiplicative.toAdd (e (u : G ⧸ Subgroup.center G)) 0).val *
        (Multiplicative.toAdd (e (v : G ⧸ Subgroup.center G)) 1).val) *
      (⁅a, b⁆⁻¹) ^ ((Multiplicative.toAdd (e (u : G ⧸ Subgroup.center G)) 1).val *
        (Multiplicative.toAdd (e (v : G ⧸ Subgroup.center G)) 0).val) := by
  obtain ⟨z₁, hz₁, hu⟩ := exists_mem_center_coord e a b ha hb u
  obtain ⟨z₂, hz₂, hv⟩ := exists_mem_center_coord e a b ha hb v
  generalize (Multiplicative.toAdd (e (u : G ⧸ Subgroup.center G)) 0).val = i at hu ⊢
  generalize (Multiplicative.toAdd (e (u : G ⧸ Subgroup.center G)) 1).val = j at hu ⊢
  generalize (Multiplicative.toAdd (e (v : G ⧸ Subgroup.center G)) 0).val = s at hv ⊢
  generalize (Multiplicative.toAdd (e (v : G ⧸ Subgroup.center G)) 1).val = t at hv ⊢
  subst hu hv
  rw [classTwo_comm_central_left hc hz₁, classTwo_comm_central_right hc hz₂]
  exact classTwo_comm_expand hc a b i j s t

theorem det_eq_one_of_fixes_center (hc : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G)
    (hZ : Nat.card (Subgroup.center G) = p) (hnc : ∃ a b : G, a * b ≠ b * a)
    (e : G ⧸ Subgroup.center G ≃* Multiplicative (Fin 2 → ZMod p)) (σ : MulAut G)
    (hσ : ∀ c ∈ Subgroup.center G, σ c = c) :
    ((elemAutEquivGL e (autQuotient (Subgroup.center G) σ) : GL (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨a, ha⟩ : ∃ a : G, e (a : G ⧸ Subgroup.center G) =
      Multiplicative.ofAdd (Pi.single 0 1) := by
    obtain ⟨q, hq⟩ := e.surjective (Multiplicative.ofAdd (Pi.single 0 1))
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨a, hq⟩
  obtain ⟨b, hb⟩ : ∃ b : G, e (b : G ⧸ Subgroup.center G) =
      Multiplicative.ofAdd (Pi.single 1 1) := by
    obtain ⟨q, hq⟩ := e.surjective (Multiplicative.ofAdd (Pi.single 1 1))
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨b, hq⟩
  set A : Matrix (Fin 2) (Fin 2) (ZMod p) :=
    ((elemAutEquivGL e (autQuotient (Subgroup.center G) σ) : GL (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) with hA
  set c : G := ⁅a, b⁆ with hcdef
  have hcZ : c ∈ Subgroup.center G := hc a b
  have hc1 : c ≠ 1 := by
    intro hc1
    obtain ⟨u, v, huv⟩ := hnc
    apply huv
    have := commutator_coord hc e a b ha hb u v
    rw [← hcdef, hc1, one_pow, inv_one, one_pow, one_mul] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hco : orderOf c = p := by
    have hdvd : orderOf c ∣ p := by
      rw [← hZ, ← Subgroup.orderOf_mk c hcZ]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hc1
    · exact h1
  have hσa : Multiplicative.toAdd (e ((σ a : G) : G ⧸ Subgroup.center G)) =
      A.mulVec (Pi.single 0 1) := by
    rw [← autQuotient_mk, ← elemAutEquivGL_mulVec e _ (a : G ⧸ Subgroup.center G), ha]
    rfl
  have hσb : Multiplicative.toAdd (e ((σ b : G) : G ⧸ Subgroup.center G)) =
      A.mulVec (Pi.single 1 1) := by
    rw [← autQuotient_mk, ← elemAutEquivGL_mulVec e _ (b : G ⧸ Subgroup.center G), hb]
    rfl
  have key := commutator_coord hc e a b ha hb (σ a) (σ b)
  rw [hσa, hσb, ← hcdef, ← map_commutatorElement, hσ c hcZ] at key
  have h00 : A.mulVec (Pi.single 0 1) 0 = A 0 0 := by simp [Matrix.col_apply]
  have h10 : A.mulVec (Pi.single 0 1) 1 = A 1 0 := by simp [Matrix.col_apply]
  have h01 : A.mulVec (Pi.single 1 1) 0 = A 0 1 := by simp [Matrix.col_apply]
  have h11 : A.mulVec (Pi.single 1 1) 1 = A 1 1 := by simp [Matrix.col_apply]
  rw [h00, h10, h01, h11] at key
  set M : ℕ := (A 0 0).val * (A 1 1).val with hM
  set N : ℕ := (A 1 0).val * (A 0 1).val with hN
  have hzpow : c ^ ((M : ℤ) - N - 1) = 1 := by
    rw [_root_.zpow_sub, zpow_one, _root_.zpow_sub, zpow_natCast, zpow_natCast, ← inv_pow]
    rw [← key, mul_inv_cancel]
  have hdvd := orderOf_dvd_iff_zpow_eq_one.mpr hzpow
  rw [hco] at hdvd
  have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
  push_cast at hzero
  rw [hM, hN] at hzero
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val] at hzero
  rw [Matrix.det_fin_two]
  linear_combination hzero

end Coordinates

section Image

variable {X : Type*} [Group X] {p : ℕ} [Fact p.Prime]

theorem centerQuotientActionNormal_mem_statedSL {E : Subgroup X} [E.Normal] {z : X}
    (hZE : (Subgroup.center E).map E.subtype = Subgroup.zpowers z) (hzp : orderOf z = p)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (hzc : z ∈ Subgroup.center X) (x : X) :
    centerQuotientActionNormal E e x ∈ StatedSL 2 (ZMod p) := by
  have hcomm : ∀ u v : E, ⁅u, v⁆ ∈ Subgroup.center E := fun u v => by
    have h := commutator_mem_center_of_mulEquiv e u v
    have h2 := Subgroup.mem_center_iff.mp h (u * v)
    have : ⁅u, v⁆ = (v * u)⁻¹ * (u * v) := by
      calc ⁅u, v⁆ = (u * v) * ((v * u)⁻¹ * (u * v)) * (u * v)⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = (v * u)⁻¹ * (u * v) := by rw [h2]; group
    rw [this]
    exact h
  have hZ : Nat.card (Subgroup.center E) = p := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective, hZE, Nat.card_zpowers, hzp]
  have hfix : ∀ c ∈ Subgroup.center E, MulAut.conjNormal (H := E) x c = c := by
    intro c hc
    have hcz : (c : X) ∈ Subgroup.zpowers z := hZE ▸ ⟨c, hc, rfl⟩
    have hx : x * (c : X) = (c : X) * x :=
      Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hzc hcz) x
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    rw [hx]
    group
  have hnc : ∃ a b : E, a * b ≠ b * a := by
    have := not_forall_mul_comm_of_mulEquiv e
    push Not at this
    exact this
  have hdet := det_eq_one_of_fixes_center hcomm hZ hnc e (MulAut.conjNormal x) hfix
  exact (CFSG.RankThree.SubgroupLists.mem_statedSL_iff _).mpr hdet

theorem statedSL_le_range_centerQuotientActionNormal {E L : Subgroup X} [E.Normal]
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set X))).map (centerQuotientAction E e)) :
    StatedSL 2 (ZMod p) ≤ (centerQuotientActionNormal E e).range := by
  intro a ha
  obtain ⟨g, -, rfl⟩ := hSL ha
  exact ⟨g, centerQuotientActionNormal_eq E e g⟩

theorem range_centerQuotientActionNormal_eq_statedSL {E L : Subgroup X} [E.Normal] {z : X}
    (hZE : (Subgroup.center E).map E.subtype = Subgroup.zpowers z) (hzp : orderOf z = p)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set X))).map (centerQuotientAction E e))
    (hzc : z ∈ Subgroup.center X) :
    (centerQuotientActionNormal E e).range = StatedSL 2 (ZMod p) := by
  refine le_antisymm ?_ (statedSL_le_range_centerQuotientActionNormal e hSL)
  rintro _ ⟨x, rfl⟩
  exact centerQuotientActionNormal_mem_statedSL hZE hzp e hzc x

end Image

end CFSG.LocalAnalysis.RankThreeTheoremC
