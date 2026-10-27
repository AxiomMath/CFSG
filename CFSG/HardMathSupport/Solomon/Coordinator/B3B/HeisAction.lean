module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.HeisCoord
public import CFSG.HardMathSupport.MathTwE6.ExtraspecialComponents

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3B

open Matrix CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.HardMathSupport.MathTwE6

variable {G : Type*} [Group G] {n : ℕ} {x y : Fin n → G} {z : G}

section Coords

variable (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1)

theorem mul_inv_mem_zpowers_of_coord_eq {q q' : G} (hq : q ∈ heisSub x y) (hq' : q' ∈ heisSub x y)
    (e : heisCoordG h hy3 q = heisCoordG h hy3 q') : q * q'⁻¹ ∈ Subgroup.zpowers z := by
  rw [← heisCoordG_eq_zero_iff h hy3 (mul_mem hq (inv_mem hq'))]
  have h1 := heisCoordG_mul h hy3 (mul_mem hq (inv_mem hq')) hq'
  rw [inv_mul_cancel_right, e] at h1
  exact add_right_cancel (h1.symm.trans (zero_add _).symm)

theorem mul_eq_mul_mul_z_of_coords {a b : G} (ha : a ∈ heisSub x y) (hb : b ∈ heisSub x y)
    (j : Fin n) (hxa : heisCoordG h hy3 a = Pi.single (Fin.castAdd n j) 1)
    (hxb : heisCoordG h hy3 b = Pi.single (Fin.natAdd n j) 1) : a * b = b * a * z := by
  obtain ⟨va, ca, rfl⟩ := exists_heisNF_aux h hy3 a ha
  obtain ⟨vb, cb, rfl⟩ := exists_heisNF_aux h hy3 b hb
  rw [heisCoordG_of_mem h hy3 ha, heisCoordFun_heisNF h hy3] at hxa
  rw [heisCoordG_of_mem h hy3 hb, heisCoordFun_heisNF h hy3] at hxb
  subst hxa hxb
  have key : ∀ (w : Fin (n + n) → ZMod 3) (c : ZMod 3),
      heisNF x y z w (c + 1) = heisNF x y z w c * z := fun w c => by
    rw [heisNF_add_right h.zp, zmod3_val_one, pow_one]
  rw [heisNF_mul h hy3, heisNF_mul h hy3, heisCocycle_single_castAdd_left,
    heisCocycle_single_natAdd_left, Pi.single_eq_same, ← key,
    add_comm (Pi.single (Fin.natAdd n j) 1 : Fin (n + n) → ZMod 3) (Pi.single (Fin.castAdd n j) 1),
    zmod3_add_two_mul_add, add_comm cb ca, add_zero]

end Coords

section Mat

variable (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1)

@[expose] noncomputable def heisMat (g : G) : Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 3) :=
  Matrix.of fun i j => heisCoordG h hy3 (g * heisBasis x y j * g⁻¹) i

theorem heisMat_apply (g : G) (i j : Fin (n + n)) :
    heisMat h hy3 g i j = heisCoordG h hy3 (g * heisBasis x y j * g⁻¹) i := rfl

theorem heisMat_mulVec_single (g : G) (k : Fin (n + n)) :
    heisMat h hy3 g *ᵥ Pi.single k 1 = heisCoordG h hy3 (g * heisBasis x y k * g⁻¹) := by
  rw [Matrix.mulVec_single_one]
  rfl

theorem conj_mem_heisSub {g q : G} (hg : g ∈ Subgroup.normalizer (heisSub x y : Set G))
    (hq : q ∈ heisSub x y) : g * q * g⁻¹ ∈ heisSub x y :=
  (Subgroup.mem_normalizer_iff.1 hg q).1 hq

theorem heisCoordG_conj {g q : G} (hg : g ∈ Subgroup.normalizer (heisSub x y : Set G))
    (hq : q ∈ heisSub x y) :
    heisCoordG h hy3 (g * q * g⁻¹) = heisMat h hy3 g *ᵥ heisCoordG h hy3 q := by
  unfold heisSub at hq
  induction hq using Subgroup.closure_induction with
  | mem q hq =>
    rcases hq with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have := heisMat_mulVec_single h hy3 g (Fin.castAdd n i)
      rw [heisBasis_castAdd] at this
      rw [heisCoordG_x h hy3, this]
    · have := heisMat_mulVec_single h hy3 g (Fin.natAdd n i)
      rw [heisBasis_natAdd] at this
      rw [heisCoordG_y h hy3, this]
  | one => rw [mul_one, mul_inv_cancel, heisCoordG_one h hy3, Matrix.mulVec_zero]
  | mul a b ha hb iha ihb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e, heisCoordG_mul h hy3 (conj_mem_heisSub hg ha) (conj_mem_heisSub hg hb), iha, ihb,
      heisCoordG_mul h hy3 ha hb, Matrix.mulVec_add]
  | inv a ha iha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    have h1 := heisCoordG_inv_add h hy3 (conj_mem_heisSub hg ha)
    have h2 := heisCoordG_inv_add h hy3 ha
    rw [iha] at h1
    have h3 : heisMat h hy3 g *ᵥ heisCoordG h hy3 a⁻¹ +
        heisMat h hy3 g *ᵥ heisCoordG h hy3 a = 0 := by
      rw [← Matrix.mulVec_add, h2, Matrix.mulVec_zero]
    rw [e]
    exact add_right_cancel (h1.trans h3.symm)

theorem heisMat_mul {g g' : G} (hg : g ∈ Subgroup.normalizer (heisSub x y : Set G))
    (hg' : g' ∈ Subgroup.normalizer (heisSub x y : Set G)) :
    heisMat h hy3 (g * g') = heisMat h hy3 g * heisMat h hy3 g' := by
  ext i j
  have hb : g' * heisBasis x y j * g'⁻¹ ∈ heisSub x y := conj_mem_heisSub hg' (heisBasis_mem j)
  have e : g * g' * heisBasis x y j * (g * g')⁻¹ = g * (g' * heisBasis x y j * g'⁻¹) * g⁻¹ := by
    group
  rw [heisMat_apply, e, heisCoordG_conj h hy3 hg hb, Matrix.mul_apply]
  rfl

theorem heisMat_one : heisMat h hy3 (1 : G) = 1 := by
  ext i j
  rw [heisMat_apply, one_mul, inv_one, mul_one, heisCoordG_basis h hy3, Pi.single_apply,
    Matrix.one_apply]

theorem heisMat_pow {g : G} (hg : g ∈ Subgroup.normalizer (heisSub x y : Set G)) (k : ℕ) :
    heisMat h hy3 (g ^ k) = heisMat h hy3 g ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, heisMat_one h hy3]
  | succ k ih =>
    rw [pow_succ, pow_succ, heisMat_mul h hy3 ((Subgroup.normalizer _).pow_mem hg k) hg, ih]

theorem heisMat_of_mem {q : G} (hq : q ∈ heisSub x y) : heisMat h hy3 q = 1 := by
  ext i j
  rw [heisMat_apply, heisCoordG_conj_of_mem h hy3 hq (heisBasis_mem j), heisCoordG_basis h hy3,
    Pi.single_apply, Matrix.one_apply]

theorem heisMat_of_mem_centralizer {p : G}
    (hp : p ∈ Subgroup.centralizer (heisSub x y : Set G)) : heisMat h hy3 p = 1 := by
  ext i j
  have hb := Subgroup.mem_centralizer_iff.1 hp (heisBasis x y j) (heisBasis_mem j)
  have e : p * heisBasis x y j * p⁻¹ = heisBasis x y j := by rw [← hb]; group
  rw [heisMat_apply, e, heisCoordG_basis h hy3, Pi.single_apply, Matrix.one_apply]

theorem heisMat_col_x (hn : 0 < n) {g : G} {j : Fin n} {v : Fin (n + n) → ZMod 3} {c : ZMod 3}
    (hgx : g * x j * g⁻¹ = heisNF x y z v c) :
    (fun i => heisMat h hy3 g i (Fin.castAdd n j)) = v := by
  funext i
  rw [heisMat_apply, heisBasis_castAdd, hgx, heisCoordG_heisNF h hy3 hn]

theorem heisMat_col_y (hn : 0 < n) {g : G} {j : Fin n} {v : Fin (n + n) → ZMod 3} {c : ZMod 3}
    (hgy : g * y j * g⁻¹ = heisNF x y z v c) :
    (fun i => heisMat h hy3 g i (Fin.natAdd n j)) = v := by
  funext i
  rw [heisMat_apply, heisBasis_natAdd, hgy, heisCoordG_heisNF h hy3 hn]

theorem heisMat_eq_of_nf (hn : 0 < n) {g : G} (M : Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 3))
    (hx : ∀ j : Fin n, ∃ c, g * x j * g⁻¹ = heisNF x y z (fun i => M i (Fin.castAdd n j)) c)
    (hy : ∀ j : Fin n, ∃ c, g * y j * g⁻¹ = heisNF x y z (fun i => M i (Fin.natAdd n j)) c) :
    heisMat h hy3 g = M := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · obtain ⟨c, hc⟩ := hx j
    exact congrFun (heisMat_col_x h hy3 hn hc) i
  · obtain ⟨c, hc⟩ := hy j
    exact congrFun (heisMat_col_y h hy3 hn hc) i

end Mat

theorem mem_normalizer_of_conj_mem [Finite G] {g : G}
    (hgx : ∀ i, g * x i * g⁻¹ ∈ heisSub x y) (hgy : ∀ i, g * y i * g⁻¹ ∈ heisSub x y) :
    g ∈ Subgroup.normalizer (heisSub x y : Set G) := by
  have hle : (heisSub x y).map (MulAut.conj g).toMonoidHom ≤ heisSub x y := by
    rw [Subgroup.map_le_iff_le_comap]
    unfold heisSub
    rw [Subgroup.closure_le]
    rintro q (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact hgx i
    · exact hgy i
  have heq : (heisSub x y).map (MulAut.conj g).toMonoidHom = heisSub x y :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  exact (map_conj_eq_iff_mem_normalizer _ g).1 heq

section Rep

variable (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1)

@[expose] noncomputable def heisRepHom :
    ↥(Subgroup.normalizer (heisSub x y : Set G)) →*
      Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 3) where
  toFun g := heisMat h hy3 g.1
  map_one' := heisMat_one h hy3
  map_mul' g g' := heisMat_mul h hy3 g.2 g'.2

@[expose] noncomputable def heisRep (_hn : 0 < n) :
    ↥(Subgroup.normalizer (heisSub x y : Set G)) →*
      (Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 3))ˣ :=
  (heisRepHom h hy3).toHomUnits

@[expose] noncomputable def heisRepL (hn : 0 < n) (L : Subgroup G)
    (hLN : L ≤ Subgroup.normalizer (heisSub x y : Set G)) :
    ↥L →* (Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 3))ˣ :=
  (heisRep h hy3 hn).comp (Subgroup.inclusion hLN)

theorem mem_range_heisRepL (hn : 0 < n) (L : Subgroup G)
    (hLN : L ≤ Subgroup.normalizer (heisSub x y : Set G)) {g : G} (hg : g ∈ L)
    {u : (Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 3))ˣ}
    (hu : (u : Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 3)) = heisMat h hy3 g) :
    u ∈ (heisRepL h hy3 hn L hLN).range :=
  ⟨⟨g, hg⟩, Units.ext hu.symm⟩

end Rep

section Dich

variable (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1)

theorem dich_of_irred (hn : 0 < n) {ι : Type*} (hh : ι → G)
    (hhN : ∀ i, hh i ∈ Subgroup.normalizer (heisSub x y : Set G))
    (hirr : ∀ U : Submodule (ZMod 3) (Fin (n + n) → ZMod 3),
      (∀ i, ∀ v ∈ U, heisMat h hy3 (hh i) *ᵥ v ∈ U) → U = ⊥ ∨ U = ⊤)
    (N : Subgroup G) (hNQ : N ≤ heisSub x y)
    (hNn : ∀ i, hh i ∈ Subgroup.normalizer (N : Set G)) :
    N ≤ Subgroup.zpowers z ∨ N = heisSub x y := by
  let U : Submodule (ZMod 3) (Fin (n + n) → ZMod 3) :=
    { carrier := {v | ∃ q ∈ N, heisCoordG h hy3 q = v}
      add_mem' := by
        rintro _ _ ⟨q, hq, rfl⟩ ⟨q', hq', rfl⟩
        exact ⟨q * q', N.mul_mem hq hq', heisCoordG_mul h hy3 (hNQ hq) (hNQ hq')⟩
      zero_mem' := ⟨1, N.one_mem, heisCoordG_one h hy3⟩
      smul_mem' := by
        rintro c _ ⟨q, hq, rfl⟩
        refine ⟨q ^ c.val, N.pow_mem hq _, ?_⟩
        rw [heisCoordG_pow h hy3 (hNQ hq), ← Nat.cast_smul_eq_nsmul (ZMod 3),
          ZMod.natCast_zmod_val] }
  have hinv : ∀ i, ∀ v ∈ U, heisMat h hy3 (hh i) *ᵥ v ∈ U := by
    rintro i _ ⟨q, hq, rfl⟩
    exact ⟨hh i * q * (hh i)⁻¹, (Subgroup.mem_normalizer_iff.1 (hNn i) q).1 hq,
      heisCoordG_conj h hy3 (hhN i) (hNQ hq)⟩
  rcases hirr U hinv with hU | hU
  · refine Or.inl fun q hq => ?_
    have hmem : heisCoordG h hy3 q ∈ U := ⟨q, hq, rfl⟩
    rw [hU, Submodule.mem_bot] at hmem
    exact (heisCoordG_eq_zero_iff h hy3 (hNQ hq)).1 hmem
  · refine Or.inr (le_antisymm hNQ fun q hq => ?_)
    have hall : ∀ v, ∃ q ∈ N, heisCoordG h hy3 q = v := fun v => by
      have hv : v ∈ U := by rw [hU]; exact Submodule.mem_top
      exact hv
    obtain ⟨a, haN, ha⟩ := hall (Pi.single (Fin.castAdd n ⟨0, hn⟩) 1)
    obtain ⟨b, hbN, hb⟩ := hall (Pi.single (Fin.natAdd n ⟨0, hn⟩) 1)
    have hab := mul_eq_mul_mul_z_of_coords h hy3 (hNQ haN) (hNQ hbN) ⟨0, hn⟩ ha hb
    have hzN : z ∈ N := by
      have e : z = (b * a)⁻¹ * (a * b) := by rw [hab]; group
      rw [e]
      exact N.mul_mem (N.inv_mem (N.mul_mem hbN haN)) (N.mul_mem haN hbN)
    obtain ⟨q', hq'N, hq'⟩ := hall (heisCoordG h hy3 q)
    have hd := mul_inv_mem_zpowers_of_coord_eq h hy3 hq (hNQ hq'N) hq'.symm
    have hdN : q * q'⁻¹ ∈ N := Subgroup.zpowers_le.2 hzN hd
    have : q = (q * q'⁻¹) * q' := by group
    rw [this]
    exact N.mul_mem hdN hq'N

end Dich

section Step0

variable (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1)

theorem pow_dvd_card_of_image (hn : 0 < n) (L : Subgroup G) (hQL : heisSub x y ≤ L)
    (hLN : L ≤ Subgroup.normalizer (heisSub x y : Set G)) (k : ℕ)
    (H : Subgroup (Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 3))ˣ)
    (hH : H ≤ (heisRepL h hy3 hn L hLN).range) (hHk : Nat.card H = 3 ^ k) :
    3 ^ (2 * n + 1 + k) ∣ Nat.card L := by
  set ρ := heisRepL h hy3 hn L hLN with hρ
  have hker : (heisSub x y).subgroupOf L ≤ ρ.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    exact Units.ext (heisMat_of_mem h hy3 (Subgroup.mem_subgroupOf.1 hg))
  have h1 : 3 ^ (2 * n + 1) ∣ Nat.card ρ.ker := by
    rw [← card_heisSub h hy3 hn,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv]
    exact Subgroup.card_dvd_of_le hker
  have h2 : 3 ^ k ∣ Nat.card ρ.range := by
    rw [← hHk]
    exact Subgroup.card_dvd_of_le hH
  have h3 : Nat.card ρ.ker * Nat.card ρ.range = Nat.card L := by
    rw [← Subgroup.index_ker]
    exact Subgroup.card_mul_index ρ.ker
  rw [pow_add, ← h3]
  exact Nat.mul_dvd_mul h1 h2

theorem le_zpowers_of_le_centralizer_inf [Finite G] (hn : 0 < n) (L : Subgroup G)
    (hQL : heisSub x y ≤ L) (hLN : L ≤ Subgroup.normalizer (heisSub x y : Set G)) (k : ℕ)
    (H : Subgroup (Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 3))ˣ)
    (hH : H ≤ (heisRepL h hy3 hn L hLN).range) (hHk : Nat.card H = 3 ^ k)
    (hG : (Nat.card G).factorization 3 ≤ 2 * n + 1 + k) :
    ∀ P : Subgroup G, P ≤ Subgroup.centralizer (heisSub x y : Set G) ⊓ L → IsPGroup 3 P →
      P ≤ Subgroup.zpowers z := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro P hP hP3
  set ρ := heisRepL h hy3 hn L hLN with hρ
  set Q := heisSub x y with hQ
  set K : Subgroup G := ρ.ker.map L.subtype with hK
  have hQK : Q ≤ K := by
    intro q hq
    refine ⟨⟨q, hQL hq⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
    exact Units.ext (heisMat_of_mem h hy3 hq)
  have hPK : P ≤ K := by
    intro p hp
    obtain ⟨hpC, hpL⟩ := Subgroup.mem_inf.1 (hP hp)
    refine ⟨⟨p, hpL⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
    exact Units.ext (heisMat_of_mem_centralizer h hy3 hpC)
  have hmul : Nat.card K * Nat.card ρ.range = Nat.card L := by
    rw [hK, Subgroup.card_map_of_injective L.subtype_injective, ← Subgroup.index_ker]
    exact Subgroup.card_mul_index ρ.ker
  have hL0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hR0 : Nat.card ρ.range ≠ 0 := right_ne_zero_of_mul (hmul ▸ hL0)
  have hLG : (Nat.card L).factorization 3 ≤ (Nat.card G).factorization 3 :=
    (Nat.factorization_le_iff_dvd hL0 Nat.card_pos.ne').2 (Subgroup.card_subgroup_dvd_card L) 3
  have hRk : k ≤ (Nat.card ρ.range).factorization 3 := by
    refine (Nat.prime_three.pow_dvd_iff_le_factorization hR0).1 ?_
    rw [← hHk]
    exact Subgroup.card_dvd_of_le hH
  have hfac := congrArg (fun m => m.factorization 3) hmul
  simp only [Nat.factorization_mul hK0 hR0, Finsupp.add_apply] at hfac
  have hK3 : (Nat.card K).factorization 3 ≤ 2 * n + 1 := by omega
  have hPN : P ≤ Subgroup.normalizer (Q : Set G) := fun p hp =>
    hLN (Subgroup.mem_inf.1 (hP hp)).2
  have hprod := card_sup_mul_card_inf_of_le_normalizer (A := Q) hPN
  obtain ⟨a, ha⟩ := hP3.exists_card_eq
  have hQcard : Nat.card Q = 3 ^ (2 * n + 1) := card_heisSub h hy3 hn
  have hdvd : Nat.card ↥(Q ⊔ P) ∣ 3 ^ (2 * n + 1 + a) := by
    rw [pow_add, ← hQcard, ← ha]
    exact Dvd.intro _ hprod
  obtain ⟨c, -, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hdvdK : 3 ^ c ∣ Nat.card K := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le (sup_le hQK hPK)
  have hc' : c ≤ (Nat.card K).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hK0).1 hdvdK
  have hle : Nat.card ↥(Q ⊔ P) ≤ Nat.card Q := by
    rw [hcard, hQcard]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hQeq : Q = Q ⊔ P := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  have hPQ : P ≤ Q := calc P ≤ Q ⊔ P := le_sup_right
    _ = Q := hQeq.symm
  intro p hp
  have hpC := (Subgroup.mem_inf.1 (hP hp)).1
  refine mem_zpowers_of_forall_commute h hy3 (hPQ hp) fun i => ⟨?_, ?_⟩
  · exact (Subgroup.mem_centralizer_iff.1 hpC (x i) (x_mem_heisSub i)).symm
  · exact (Subgroup.mem_centralizer_iff.1 hpC (y i) (y_mem_heisSub i)).symm

theorem hCQ_of_image [Finite G] (hn : 0 < n) (L : Subgroup G) (hQL : heisSub x y ≤ L)
    (hLN : L ≤ Subgroup.normalizer (heisSub x y : Set G)) (k : ℕ)
    (H : Subgroup (Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 3))ˣ)
    (hH : H ≤ (heisRepL h hy3 hn L hLN).range) (hHk : Nat.card H = 3 ^ k)
    (hG : (Nat.card G).factorization 3 ≤ 2 * n + 1 + k) :
    ∀ P : Subgroup G, P ≤ Subgroup.centralizer (heisSub x y : Set G) → IsPGroup 3 P →
      Nat.card P ≤ 3 := by
  have hL3 : (Nat.card G).factorization 3 ≤ (Nat.card L).factorization 3 := by
    have h1 := pow_dvd_card_of_image h hy3 hn L hQL hLN k H hH hHk
    have h2 : 2 * n + 1 + k ≤ (Nat.card L).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h1
    omega
  exact card_le_three_of_le_centralizer z h.zp (heisSub x y) L hLN hL3
    (le_zpowers_of_le_centralizer_inf h hy3 hn L hQL hLN k H hH hHk hG)

end Step0

end CFSG.HardMathSupport.Solomon.Coordinator.B3B
