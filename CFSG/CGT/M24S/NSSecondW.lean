module

public import CFSG.CGT.M24S.NSSecondBasic

public section

namespace CFSG.CGT.M24S.NSSecond

open Matrix GL4

variable {G : Type} [Group G]

@[expose] def span3 (w : Fin 3 → G) : Subgroup G :=
  Subgroup.zpowers (w 0) ⊔ Subgroup.zpowers (w 1) ⊔ Subgroup.zpowers (w 2)

theorem mem_span3 (w : Fin 3 → G) (i : Fin 3) : w i ∈ span3 w := by
  fin_cases i
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem span3_le {w : Fin 3 → G} {X : Subgroup G} (h : ∀ i, w i ∈ X) : span3 w ≤ X :=
  sup_le (sup_le (Subgroup.zpowers_le.2 (h 0)) (Subgroup.zpowers_le.2 (h 1)))
    (Subgroup.zpowers_le.2 (h 2))

theorem map_conj_span3 (w : Fin 3 → G) (x : G) :
    (span3 w).map (MulAut.conj x).toMonoidHom = span3 (fun i => x * w i * x⁻¹) := by
  simp only [span3, Subgroup.map_sup, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]

theorem mem_normalizer_span3 [Finite G] {w : Fin 3 → G} {x : G}
    (h : ∀ i, x * w i * x⁻¹ ∈ span3 w) : x ∈ Subgroup.normalizer (span3 w : Set G) :=
  mem_normalizer_of_map_le (by rw [map_conj_span3]; exact span3_le h)

theorem card_span3_le {w : Fin 3 → G} {W : Subgroup G} (hw : ∀ i, w i ∈ W)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (h2 : ∀ i, w i * w i = 1) :
    Nat.card (span3 w) ≤ 8 := by
  have hc : ∀ {A B : Subgroup G}, A ≤ W → B ≤ W → B ≤ Subgroup.normalizer (A : Set G) :=
    fun hA hB => le_normalizer_of_commute fun a ha b hb => hWab a (hA ha) b (hB hb)
  have h01 : Subgroup.zpowers (w 0) ⊔ Subgroup.zpowers (w 1) ≤ W :=
    sup_le (Subgroup.zpowers_le.2 (hw 0)) (Subgroup.zpowers_le.2 (hw 1))
  calc Nat.card (span3 w)
      ≤ Nat.card (Subgroup.zpowers (w 0) ⊔ Subgroup.zpowers (w 1) : Subgroup G) *
          Nat.card (Subgroup.zpowers (w 2)) :=
        card_sup_le_of_le_normalizer (hc h01 (Subgroup.zpowers_le.2 (hw 2)))
    _ ≤ (Nat.card (Subgroup.zpowers (w 0)) * Nat.card (Subgroup.zpowers (w 1))) * 2 :=
        Nat.mul_le_mul (card_sup_le_of_le_normalizer
          (hc (Subgroup.zpowers_le.2 (hw 0)) (Subgroup.zpowers_le.2 (hw 1))))
          (card_zpowers_le_two (h2 2))
    _ ≤ (2 * 2) * 2 := Nat.mul_le_mul_right _
        (Nat.mul_le_mul (card_zpowers_le_two (h2 0)) (card_zpowers_le_two (h2 1)))

theorem eq_one_or_eq_of_mem_zpowers {g x : G} (hx : x ^ 2 = 1) (hg : g ∈ Subgroup.zpowers x) :
    g = 1 ∨ g = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact hx
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem sum_single_val : ∀ x : Fin 3 → ZMod 2,
    (x 0).val • (Pi.single 0 1 : Fin 3 → ZMod 2) + (x 1).val • Pi.single 1 1 +
      (x 2).val • Pi.single 2 1 = x := by
  decide

variable {T H : Subgroup G} {z : G}

structure SecondData (c : NatCoord T H z) (W : Subgroup G) (w : Fin 3 → G) : Prop where
  le_E : W ≤ c.E
  normal : ∀ k ∈ H ⊓ Subgroup.centralizer ({z} : Set G), ∀ y ∈ W, k * y * k⁻¹ ∈ W
  comm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a
  sq : ∀ y ∈ W, y ^ 2 = 1
  inf_T : W ⊓ T = Subgroup.zpowers z
  mem : ∀ i, w i ∈ W
  top_eq : ∀ i, top (c.mat (w i)) = Pi.single i 1

variable {c : NatCoord T H z} {W : Subgroup G} {w : Fin 3 → G}

theorem top_pow_of_mem_E (c : NatCoord T H z) {y : G} (hy : y ∈ c.E) (n : ℕ) :
    top (c.mat (y ^ n)) = n • top (c.mat y) := by
  induction n with
  | zero => rw [pow_zero, c.mat_one, top_one, zero_smul]
  | succ n ih => rw [pow_succ, top_mul_of_mem_E c (c.E.pow_mem hy n) hy, ih, succ_nsmul]

theorem exists_mem_span3_top_eq (hS : SecondData c W w) (x : Fin 3 → ZMod 2) :
    ∃ u ∈ span3 w, top (c.mat u) = x := by
  have hE : ∀ i, w i ∈ c.E := fun i => hS.le_E (hS.mem i)
  refine ⟨w 0 ^ (x 0).val * w 1 ^ (x 1).val * w 2 ^ (x 2).val,
    mul_mem (mul_mem (pow_mem (mem_span3 w 0) _) (pow_mem (mem_span3 w 1) _))
      (pow_mem (mem_span3 w 2) _), ?_⟩
  rw [top_mul_of_mem_E c (mul_mem (pow_mem (hE 0) _) (pow_mem (hE 1) _)) (pow_mem (hE 2) _),
    top_mul_of_mem_E c (pow_mem (hE 0) _) (pow_mem (hE 1) _), top_pow_of_mem_E c (hE 0),
    top_pow_of_mem_E c (hE 1), top_pow_of_mem_E c (hE 2), hS.top_eq 0, hS.top_eq 1,
    hS.top_eq 2]
  exact sum_single_val x

theorem mul_self_eq_one (hS : SecondData c W w) {y : G} (hy : y ∈ W) : y * y = 1 := by
  rw [← pow_two]
  exact hS.sq y hy

theorem card_span3_le' (hS : SecondData c W w) : Nat.card (span3 w) ≤ 8 :=
  card_span3_le hS.mem hS.comm fun i => mul_self_eq_one hS (hS.mem i)

theorem z_not_mem_span3 [Finite G] (hS : SecondData c W w) : z ∉ span3 w := by
  intro hz
  let g : span3 w → (Fin 3 → ZMod 2) := fun u => top (c.mat u)
  have hg : Function.Surjective g := fun x => by
    obtain ⟨u, hu, hux⟩ := exists_mem_span3_top_eq hS x
    exact ⟨⟨u, hu⟩, hux⟩
  have hcard : Nat.card (span3 w) ≤ Nat.card (Fin 3 → ZMod 2) := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    exact card_span3_le' hS
  have h1 : g ⟨z, hz⟩ = g ⟨1, one_mem _⟩ := by
    change top (c.mat z) = top (c.mat 1)
    rw [(c.mat_eq_one_iff (c.le c.mem)).2 c.mem, c.mat_one]
  exact c.z_ne_one (congrArg Subtype.val ((hg.bijective_of_nat_card_le hcard).1 h1))

theorem mem_span3_or_mul_mem (hS : SecondData c W w) {y : G} (hy : y ∈ W) :
    y ∈ span3 w ∨ y * z ∈ span3 w := by
  obtain ⟨u, hu, hut⟩ := exists_mem_span3_top_eq hS (top (c.mat y))
  have huW : u ∈ W := span3_le hS.mem hu
  have hyu : y * u⁻¹ ∈ W := W.mul_mem hy (W.inv_mem huW)
  have htop : top (c.mat (y * u⁻¹)) = 0 := by
    rw [top_mul_of_mem_E c (hS.le_E hy) (c.E.inv_mem (hS.le_E huW)),
      top_inv_of_mem_E c (hS.le_E huW), hut, vec_add_self]
  have hz : y * u⁻¹ ∈ Subgroup.zpowers z :=
    hS.inf_T ▸ ⟨hyu, mem_T_of_top_eq_zero c (hS.le_E hyu) htop⟩
  have hzW : z ∈ W := (hS.inf_T ▸ Subgroup.mem_zpowers z : z ∈ W ⊓ T).1
  rcases eq_one_or_eq_of_mem_zpowers c.z_sq hz with h | h
  · left
    rwa [mul_inv_eq_one.1 h]
  · right
    have hy' : y = z * u := by rw [← h]; group
    rw [hy', hS.comm z hzW u huW, mul_assoc, ← pow_two, c.z_sq, mul_one]
    exact hu

theorem eq_one_or_eq_z_of_mem_normalizer [Finite G] (hS : SecondData c W w) {s : G}
    (hs : s ∈ T) (hN : s ∈ Subgroup.normalizer (span3 w : Set G)) : s = 1 ∨ s = z := by
  have htail : tail (c.vec s) = 0 := by
    funext i
    rcases zmod_two_eq_zero_or_one (tail (c.vec s) i) with h | h
    · exact h
    · exfalso
      have hd : top (c.mat (w i)) ⬝ᵥ tail (c.vec s) = 1 := by
        rw [hS.top_eq i, single_one_dotProduct, h]
      have h2 : s * w i * s⁻¹ ∈ span3 w :=
        (Subgroup.mem_normalizer_iff.1 hN (w i)).1 (mem_span3 w i)
      rw [conj_eq_of_dotProduct_eq_one c (hS.le_E (hS.mem i)) hs hd] at h2
      apply z_not_mem_span3 hS
      have := (span3 w).mul_mem ((span3 w).inv_mem (mem_span3 w i)) h2
      rwa [inv_mul_cancel_left] at this
  rcases eq_zero_or_eq_e0_of_tail_eq_zero htail with h | h
  · exact Or.inl (c.eq_of_vec_eq hs T.one_mem (h.trans c.vec_one.symm))
  · exact Or.inr (c.eq_of_vec_eq hs c.mem (h.trans c.vec_z.symm))

theorem exists_mul_mem_normalizer [Finite G] (hS : SecondData c W w) {h : G}
    (hh : h ∈ H ⊓ Subgroup.centralizer ({z} : Set G)) :
    ∃ s ∈ T, s * h ∈ Subgroup.normalizer (span3 w : Set G) := by
  classical
  let ε : Fin 3 → ZMod 2 := fun i => if h * w i * h⁻¹ ∈ span3 w then 0 else 1
  obtain ⟨s, hs, hsv⟩ := c.exists_vec_eq (Fin.cons 0 (blk (c.mat h) *ᵥ ε))
  refine ⟨s, hs, mem_normalizer_span3 fun i => ?_⟩
  have hyW : h * w i * h⁻¹ ∈ W := hS.normal h hh (w i) (hS.mem i)
  have hyE := hS.le_E hyW
  have hd : top (c.mat (h * w i * h⁻¹)) ⬝ᵥ tail (c.vec s) = ε i := by
    rw [hsv, tail_cons_zero, dotProduct_mulVec, c.vecMul_top_conj hh (hS.le_E (hS.mem i)),
      hS.top_eq i, single_one_dotProduct]
  have heq : s * h * w i * (s * h)⁻¹ = s * (h * w i * h⁻¹) * s⁻¹ := by group
  rw [heq]
  by_cases hm : h * w i * h⁻¹ ∈ span3 w
  · rw [conj_eq_of_dotProduct_eq_zero c hyE hs (by rw [hd]; simp [ε, hm])]
    exact hm
  · rw [conj_eq_of_dotProduct_eq_one c hyE hs (by rw [hd]; simp [ε, hm])]
    exact (mem_span3_or_mul_mem hS hyW).resolve_left hm

theorem mul_self_eq_one_of_liftData [Finite G] (hS : SecondData c W w)
    {τ : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hτ : LiftData τ) {h : G}
    (hh : h ∈ H ⊓ Subgroup.centralizer ({z} : Set G))
    (hN : h ∈ Subgroup.normalizer (span3 w : Set G)) (hmat : c.mat h = τ) : h * h = 1 := by
  obtain ⟨hτe, hτd, M, hMM, hMτ⟩ := hτ
  obtain ⟨u, hu, hut⟩ := exists_mem_span3_top_eq hS ![0, 0, 1]
  have huW : u ∈ W := span3_le hS.mem hu
  have huH : u ∈ H := c.mem_H_of_mem_E (hS.le_E huW)
  have hum : c.mat u = mk4 ![0, 0, 1] 1 := by rw [c.mat_eq_mk4_of_mem_E (hS.le_E huW), hut]
  obtain ⟨g, hg, hgM⟩ := c.exists_mat_eq M (det_eq_one_of_mul_self' hMM)
  have hxH : g * u * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg huH) (H.inv_mem hg)
  have hxm : c.mat (g * u * g⁻¹) = τ := by
    rw [c.mat_mul (H.mul_mem hg huH) (H.inv_mem hg), c.mat_mul hg huH, hgM, hum, hMτ,
      Matrix.mul_assoc, ← hgM, c.mat_mul_inv hg, Matrix.mul_one]
  have hxx : g * u * g⁻¹ * (g * u * g⁻¹) = 1 := by
    calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [mul_self_eq_one hS huW, mul_one, mul_inv_cancel]
  have hxK : g * u * g⁻¹ ∈ H ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨hxH, (c.mem_centralizer_iff hxH).2 (by rw [hxm]; exact hτe)⟩
  obtain ⟨s, hs, hsN⟩ := exists_mul_mem_normalizer hS hxK
  have haH : s * (g * u * g⁻¹) ∈ H := H.mul_mem (c.le hs) hxH
  have ham : c.mat (s * (g * u * g⁻¹)) = τ := by
    rw [c.mat_mul (c.le hs) hxH, (c.mat_eq_one_iff (c.le hs)).2 hs, Matrix.one_mul, hxm]
  have haa : s * (g * u * g⁻¹) * (s * (g * u * g⁻¹)) =
      s * ((g * u * g⁻¹) * s * (g * u * g⁻¹)⁻¹) := by
    calc s * (g * u * g⁻¹) * (s * (g * u * g⁻¹)) =
        s * ((g * u * g⁻¹) * s * (g * u * g⁻¹)⁻¹) * (g * u * g⁻¹ * (g * u * g⁻¹)) := by group
      _ = _ := by rw [hxx, mul_one]
  have hcT := c.conj_mem hxH hs
  have haT : s * (g * u * g⁻¹) * (s * (g * u * g⁻¹)) ∈ T := by
    rw [haa]
    exact T.mul_mem hs hcT
  have hav : c.vec (s * (g * u * g⁻¹) * (s * (g * u * g⁻¹))) = c.vec s + τ *ᵥ c.vec s := by
    rw [haa, c.vec_mul hs hcT, c.vec_conj hxH hs, hxm]
  have ha1 : s * (g * u * g⁻¹) * (s * (g * u * g⁻¹)) = 1 := by
    have h2 : c.vec s + τ *ᵥ c.vec s = 0 := hτd _ (by
      rcases eq_one_or_eq_z_of_mem_normalizer hS haT (mul_mem hsN hsN) with h1 | h1
      · left
        rw [← hav, h1, c.vec_one]
      · right
        rw [← hav, h1, c.vec_z])
    exact c.eq_of_vec_eq haT T.one_mem (by rw [hav, h2, c.vec_one])
  set a := s * (g * u * g⁻¹) with ha
  have haK : a ∈ H ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨haH, (c.mem_centralizer_iff haH).2 (by rw [ham]; exact hτe)⟩
  have hv : a⁻¹ * h ∈ T := by
    rw [← c.mat_eq_one_iff (H.mul_mem (H.inv_mem haH) hh.1), c.mat_mul (H.inv_mem haH) hh.1,
      hmat, ← ham, c.mat_inv_mul haH]
  have hza : z * a = a * z := (Subgroup.mem_centralizer_singleton_iff.1 haK.2).symm
  rcases eq_one_or_eq_z_of_mem_normalizer hS hv (mul_mem (inv_mem hsN) hN) with h1 | h1
  · rw [← mul_inv_cancel_left a h, h1, mul_one]
    exact ha1
  · rw [← mul_inv_cancel_left a h, h1]
    calc a * z * (a * z) = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [hza]
      _ = a * a * (z * z) := by group
      _ = 1 := by rw [ha1, one_mul, ← pow_two, c.z_sq]

end CFSG.CGT.M24S.NSSecond
