module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23.Inspect
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowG23
public import Certificates.Certificate543001
import CFSG.Sporadic.Recognition.LyonsAS44Quat

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5 Certificates.S5Rows Certificates.S5RowsG23
  Certificates.S7G23Insp CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.Quasithin.G2U
  CFSG.Blueprint CFSG.Blueprint.Chevalley

local notation "M14" => Matrix (Fin 14) (Fin 14) (ZMod 3)
local notation "GL14" => GL (Fin 14) (ZMod 3)

theorem s7g23Checks_holds :
    c0 () = true ∧ c1 () = true ∧ c2 () = true ∧ c3 () = true ∧ c4 () = true :=
  Certificates.certificate543001

section Generic

variable {G : Type} [Group G]

theorem pow_succ_mem_of_mul_closed {S : Set G} (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) {x : G}
    (hx : x ∈ S) (n : ℕ) : x ^ (n + 1) ∈ S := by
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [pow_succ]; exact hmul _ ih _ hx

theorem one_mem_of_mul_closed [Finite G] {S : Set G} (hne : S.Nonempty)
    (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) : (1 : G) ∈ S := by
  obtain ⟨x, hx⟩ := hne
  have := pow_succ_mem_of_mul_closed hmul hx (orderOf x - 1)
  rwa [Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one] at this

theorem inv_mem_of_mul_closed [Finite G] {S : Set G} (hne : S.Nonempty)
    (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) {x : G} (hx : x ∈ S) : x⁻¹ ∈ S := by
  have h1 := one_mem_of_mul_closed hne hmul
  have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
  rw [hinv]
  rcases Nat.eq_zero_or_pos (orderOf x - 1) with h | h
  · rw [h, pow_zero]; exact h1
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    rw [hm]; exact pow_succ_mem_of_mul_closed hmul hx m

@[expose] def mulClosedSubgroup [Finite G] (S : Set G) (hne : S.Nonempty)
    (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) : Subgroup G where
  carrier := S
  mul_mem' := fun {x y} hx hy => hmul x hx y hy
  one_mem' := one_mem_of_mul_closed hne hmul
  inv_mem' := fun {x} hx => inv_mem_of_mul_closed hne hmul hx

theorem mem_normalizer_of_conj_mem [Finite G] {K : Subgroup G} {n : G}
    (h : ∀ k ∈ K, n * k * n⁻¹ ∈ K) : n ∈ Subgroup.normalizer (K : Set G) := by
  have hle : K.map (MulAut.conj n).toMonoidHom ≤ K := by
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  have heq : K.map (MulAut.conj n).toMonoidHom = K :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj n).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨k, hk, hkx⟩ := hx
  have : k = x := (MulAut.conj n).injective (by simpa using hkx)
  rw [← this]
  exact hk

theorem card_conjSub_eq (a : G) (K : Subgroup G) : Nat.card (conjSub a K) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj a).injective

theorem q8_sq_eq_one : ∀ w : QuaternionGroup 2, w * w = 1 → w = 1 ∨ w = QuaternionGroup.a 2 := by
  decide

theorem isUniqueInvolution_of_mulEquiv {K : Subgroup G} (e : ↥K ≃* QuaternionGroup 2) {z : G}
    (hz : z ∈ K) (hz1 : z ≠ 1) (hzz : z * z = 1) : IsUniqueInvolution K z := by
  have hz' : e ⟨z, hz⟩ = QuaternionGroup.a 2 := by
    have h1 : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := by
      rw [← map_mul, ← map_one e]
      congr 1
      exact Subtype.ext hzz
    rcases q8_sq_eq_one _ h1 with h | h
    · exfalso
      apply hz1
      have := e.injective (h.trans (map_one e).symm)
      exact congrArg Subtype.val this
    · exact h
  refine ⟨hz, hz1, hzz, fun y hy hyy => ?_⟩
  have h1 : e ⟨y, hy⟩ * e ⟨y, hy⟩ = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext hyy
  rcases q8_sq_eq_one _ h1 with h | h
  · left
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this
  · right
    have := e.injective (h.trans hz'.symm)
    exact congrArg Subtype.val this

theorem q8_of_pair [Finite G] {K : Subgroup G} (hK : Nat.card K = 8) {x y : G} (hx : x ∈ K)
    (hy : y ∈ K) (h : Q8Rel x y) : K ∈ q8Fam G ∧ IsUniqueInvolution K (x * x) := by
  obtain ⟨h4, h2, hxy, hyx⟩ := h
  have hyx' : y * x * y⁻¹ = x⁻¹ := by
    have h1 : y * x⁻¹ * y⁻¹ = x := by
      calc y * x⁻¹ * y⁻¹ = y * (y⁻¹ * x * y) * y⁻¹ := by rw [hyx]
        _ = x := by group
    calc y * x * y⁻¹ = (y * x⁻¹ * y⁻¹)⁻¹ := by group
      _ = x⁻¹ := by rw [h1]
  have hx4 : (⟨x, hx⟩ : K) ^ 4 = 1 := Subtype.ext (by simpa using h4)
  have hx2 : (⟨x, hx⟩ : K) ^ 2 ≠ 1 := fun h' => h2 (by simpa using congrArg Subtype.val h')
  have hyx2 : (⟨y, hy⟩ : K) * ⟨x, hx⟩ * (⟨y, hy⟩ : K)⁻¹ = (⟨x, hx⟩ : K)⁻¹ :=
    Subtype.ext (by simpa using hyx')
  have hy2 : (⟨y, hy⟩ : K) ^ 2 = (⟨x, hx⟩ : K) ^ 2 :=
    Subtype.ext (by simpa using hxy.symm)
  obtain ⟨e⟩ := CFSG.Sporadic.Recognition.LyonsSims.nonempty_mulEquiv_quaternionGroup_two hK
    ⟨x, hx⟩ ⟨y, hy⟩ hx4 hx2 hyx2 hy2
  refine ⟨⟨e⟩, isUniqueInvolution_of_mulEquiv e (K.mul_mem hx hx) ?_ ?_⟩
  · rw [← sq]; exact h2
  · calc x * x * (x * x) = x ^ 2 * x ^ 2 := by rw [sq]
      _ = x ^ 4 := by rw [← pow_add]
      _ = 1 := h4

theorem q8Rel_of_injective {M N : Type*} [Group M] [Group N] (f : M →* N)
    (hf : Function.Injective f) {i j : M} (h : Q8Rel (f i) (f j)) : Q8Rel i j := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨hf (by rw [map_pow, map_one]; exact h1), fun h => h2 (by rw [← map_pow, h, map_one]),
    hf (by rw [map_pow, map_pow]; exact h3),
    hf (by rw [map_mul, map_mul, map_inv, map_inv]; exact h4)⟩

theorem q8Rel_map_of_injective {M N : Type*} [Group M] [Group N] (f : M →* N)
    (hf : Function.Injective f) {i j : M} (h : Q8Rel i j) : Q8Rel (f i) (f j) :=
  h.map f fun h1 => h.2.1 (hf (by rw [h1, map_one]))

theorem q8Rel_coe {i j : H3} (h : Q8Rel i j) : Q8Rel (i : GL14) (j : GL14) :=
  q8Rel_map_of_injective R3.subtype R3.subtype_injective h

theorem q8Rel_conj {M : Type*} [Group M] {i j : M} (g : M) (h : Q8Rel i j) :
    Q8Rel (g⁻¹ * i * g) (g⁻¹ * j * g) := by
  have := q8Rel_map_of_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective h
  simpa [MulAut.conj_apply] using this

theorem q8Rel_of_q8RelC {ci cj : List ℕ} {i j : GL14} (hi : (i : M14) = dec14 ci)
    (hj : (j : M14) = dec14 cj) (h : q8RelC ci cj = true) : Q8Rel i j := by
  have hi2 : ((i ^ 2 : GL14) : M14) = dec14 (sq14 ci) := coe_sq hi
  have hj2 : ((j ^ 2 : GL14) : M14) = dec14 (sq14 cj) := coe_sq hj
  simp only [q8RelC, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Units.ext
    have : i ^ 4 = i ^ 2 * i ^ 2 := by rw [← pow_add]
    rw [this, Units.val_mul, hi2, ← dec14_mul14, h1, Units.val_one, dec14_one14]
  · intro he
    apply h2
    refine dec14_injective (canon14_mul14 _ _) canon14_one14 ?_
    rw [← hi2, he, Units.val_one, dec14_one14]
  · apply Units.ext
    rw [hi2, hj2, h3]
  · have hij : i * j * i = j := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hi, hj, ← dec14_mul14, ← dec14_mul14, h4]
    have h1 : i * j = j * i⁻¹ := by rw [eq_mul_inv_iff_mul_eq]; exact hij
    calc j⁻¹ * i * j = j⁻¹ * (i * j) := by rw [mul_assoc]
      _ = j⁻¹ * (j * i⁻¹) := by rw [h1]
      _ = i⁻¹ := inv_mul_cancel_left j i⁻¹

theorem c0_spec (h : c0 () = true) :
    closedL k1s = true ∧ closedL k2s = true ∧ q8RelC (es 1) (es 2) = true ∧
      q8RelC (es 3) (es 4) = true ∧ sq14 (es 1) = tc ∧ sq14 (es 3) = tc ∧
      (∀ k ∈ k1s, k < elemsS.size) ∧ ∀ k ∈ k2s, k < elemsS.size := by
  simp only [c0, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_append,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun k hk => h8 k (Or.inl hk), fun k hk => h8 k (Or.inr hk)⟩

theorem c1_spec (h : c1 () = true) {a b : ℕ} (ha : a < 64) (hb : b < 64)
    (hq : q8RelC (es a) (es b) = true) : (a ∈ k1s ∧ b ∈ k1s) ∨ (a ∈ k2s ∧ b ∈ k2s) := by
  simp only [c1, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', List.contains_iff_mem] at h
  rcases h a ha b hb with (h | h) | h
  · rw [hq] at h; exact absurd h (by decide)
  · exact Or.inl h
  · exact Or.inr h

theorem c2_spec (h : c2 () = true) {ks : List ℕ} (hks : ks = k1s ∨ ks = k2s) {y : List ℕ}
    (hy : y ∈ gensX) {k : ℕ} (hk : k ∈ ks) : ∃ k' ∈ ks, mul14 y (es k) = mul14 (es k') y := by
  simp only [c2, List.all_eq_true, List.any_eq_true, beq_iff_eq, List.mem_cons,
    List.not_mem_nil, or_false] at h
  have := h ks (by rcases hks with rfl | rfl <;> simp) y hy k hk
  exact this

theorem c3_spec (h : c3 () = true) :
    mul14 (gc ()) (gic ()) = one14 ∧ sq14 (es 4) ≠ one14 ∧ sq14 (sq14 (es 4)) = one14 ∧
      mul14 (mul14 (gc ()) (es 4)) (gic ()) ∈ elemsX ∧
      mul14 (mul14 (gc ()) (es 25)) (gic ()) ∉ elemsX := by
  simp only [c3, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true',
    Array.contains_iff_mem] at h
  obtain ⟨⟨h1, ⟨h2, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun hm => ?_⟩
  rw [Array.contains_iff_mem.mpr hm] at h5
  exact absurd h5 (by decide)

theorem c4_spec (h : c4 () = true) :
    x0c = mul14 (mul14 (sq14 (gc ())) (sq14 vc)) (sq14 (gic ())) ∧
      y0c = mul14 (mul14 (sq14 (gic ())) uc) (sq14 (gc ())) := by
  simp only [c4, Bool.and_eq_true, beq_iff_eq] at h
  exact h

end Generic

section Gens

theorem R3_le_of_gens (H : Subgroup GL14) (hX : ∀ n : Fin 2, gX n ∈ H)
    (hY : ∀ n : Fin 2, gY n ∈ H) : R3 ≤ H := by
  have hc3 : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  have hx : ∀ (n : Fin 2) (c : ZMod 3),
      glHom (RingEquiv.refl (ZMod 3)) (xUnit .G2 (ZMod 3) (ix n) c) ∈ H := by
    intro n c
    rcases hc3 c with rfl | rfl | rfl
    · have h0 : xUnit .G2 (ZMod 3) (ix n) 0 = 1 := Units.ext (xOp_zero _)
      rw [h0, map_one]
      exact H.one_mem
    · exact hX n
    · have h2 : xUnit .G2 (ZMod 3) (ix n) 2 =
          xUnit .G2 (ZMod 3) (ix n) 1 * xUnit .G2 (ZMod 3) (ix n) 1 := by
        apply Units.ext
        simp only [Units.val_mul, coe_xUnit]
        rw [xOp_mul_xOp (upTransport .G2)]
        rfl
      rw [h2, map_mul]
      exact H.mul_mem (hX n) (hX n)
  have hy : ∀ (n : Fin 2) (c : ZMod 3),
      glHom (RingEquiv.refl (ZMod 3)) (yUnit .G2 (ZMod 3) (ix n) c) ∈ H := by
    intro n c
    rcases hc3 c with rfl | rfl | rfl
    · have h0 : yUnit .G2 (ZMod 3) (ix n) 0 = 1 := Units.ext (yOp_zero _)
      rw [h0, map_one]
      exact H.one_mem
    · exact hY n
    · have h2 : yUnit .G2 (ZMod 3) (ix n) 2 =
          yUnit .G2 (ZMod 3) (ix n) 1 * yUnit .G2 (ZMod 3) (ix n) 1 := by
        apply Units.ext
        simp only [Units.val_mul, coe_yUnit]
        rw [yOp_mul_yOp (downTransport .G2)]
        rfl
      rw [h2, map_mul]
      exact H.mul_mem (hY n) (hY n)
  unfold R3
  rw [Subgroup.map_le_iff_le_comap, adjointGroup, Subgroup.closure_le]
  rintro g ⟨i, c, hg | hg⟩
  · obtain ⟨n, rfl⟩ : ∃ n : Fin 2, ix n = i := ⟨i, rfl⟩
    have hgu : g = xUnit .G2 (ZMod 3) (ix n) c := Units.ext hg
    show glHom (RingEquiv.refl (ZMod 3)) g ∈ H
    rw [hgu]
    exact hx n c
  · obtain ⟨n, rfl⟩ : ∃ n : Fin 2, ix n = i := ⟨i, rfl⟩
    have hgu : g = yUnit .G2 (ZMod 3) (ix n) c := Units.ext hg
    show glHom (RingEquiv.refl (ZMod 3)) g ∈ H
    rw [hgu]
    exact hy n c

theorem gens_mem_X0 : gX 1 ∈ X0 ∧ gY 1 ∈ X0 ∧ uU ∈ X0 ∧ vU ∈ X0 ∧ h0U ∈ X0 :=
  ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
    Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
    Subgroup.subset_closure (by simp)⟩

theorem S2_le_X0 : S2 ≤ X0 := by
  obtain ⟨h1, h2, hu, hv, hh⟩ := gens_mem_X0
  have hn1 : n1U ∈ X0 := mul_mem (mul_mem h1 (pow_mem h2 2)) h1
  have hnb : nbU ∈ X0 := mul_mem (mul_mem hu (pow_mem hv 2)) hu
  rw [S2, Subgroup.closure_le]
  rintro g (rfl | rfl | rfl | rfl | rfl)
  · exact hn1
  · exact mul_mem (mul_mem h1 hn1) (pow_mem h1 2)
  · exact hnb
  · exact mul_mem (mul_mem hu hnb) (pow_mem hu 2)
  · exact hh

@[expose] noncomputable def gU : GL14 :=
  gX 0 * gX 1 * gX 0 * gY 0 * (gY 1)⁻¹ * gY 0 * gY 1 * gX 1 * (gX 0)⁻¹ * gY 0

theorem gU_mem : gU ∈ R3 :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (gX_mem 0)
    (gX_mem 1)) (gX_mem 0)) (gY_mem 0)) (inv_mem (gY_mem 1))) (gY_mem 0)) (gY_mem 1))
    (gX_mem 1)) (inv_mem (gX_mem 0))) (gY_mem 0)

end Gens

section Elements

theorem coe_gU : ((gU : GL14) : M14) = dec14 (gc ()) := by
  obtain ⟨h0, -, -, h3⟩ := gens_pow_three
  have e1 : (gY 1)⁻¹ = gY 1 ^ 2 := inv_eq_sq h3
  have e0 : (gX 0)⁻¹ = gX 0 ^ 2 := inv_eq_sq h0
  have s1 : ((gX 0 : GL14) : M14) = dec14 (mul14 one14 x0c) := by
    rw [dec14_mul14, dec14_one14, one_mul, coe_gX0]
  have s2 := coe_mul s1 coe_gX1
  have s3 := coe_mul s2 coe_gX0
  have s4 := coe_mul s3 coe_gY0
  have s5 := coe_mul s4 (coe_sq coe_gY1)
  have s6 := coe_mul s5 coe_gY0
  have s7 := coe_mul s6 coe_gY1
  have s8 := coe_mul s7 coe_gX1
  have s9 := coe_mul s8 (coe_sq coe_gX0)
  have s10 := coe_mul s9 coe_gY0
  rw [gU, e1, e0]
  simp only [gc, wordG, List.foldl_cons, List.foldl_nil]
  exact s10

theorem coe_gU_inv (h : mul14 (gc ()) (gic ()) = one14) :
    (((gU⁻¹ : GL14)) : M14) = dec14 (gic ()) := by
  have h1 : (gU : M14) * dec14 (gic ()) = 1 := by
    rw [coe_gU, ← dec14_mul14, h, dec14_one14]
  calc ((gU⁻¹ : GL14) : M14) = ((gU⁻¹ : GL14) : M14) * ((gU : M14) * dec14 (gic ())) := by
        rw [h1, mul_one]
    _ = dec14 (gic ()) := by rw [← mul_assoc, Units.inv_mul, one_mul]

theorem exists_S2_of_lt {k : ℕ} (hk : k < elemsS.size) :
    ∃ g ∈ S2, (g : M14) = dec14 (es k) := by
  have h : dec14 (elemsS.getD k []) ∈ (Units.coeHom M14) '' (S2 : Set GL14) := by
    rw [image_S2]
    exact ⟨k, hk, rfl⟩
  obtain ⟨g, hg, e⟩ := h
  exact ⟨g, hg, e⟩

theorem exists_sE : ∃ f : ℕ → H3, ∀ k, f k ∈ S2H ∧
    (k < elemsS.size → (((f k : H3) : GL14) : M14) = dec14 (es k)) := by
  have h : ∀ k : ℕ, ∃ g : H3, g ∈ S2H ∧
      (k < elemsS.size → (((g : H3) : GL14) : M14) = dec14 (es k)) := by
    intro k
    by_cases hk : k < elemsS.size
    · obtain ⟨g, hg, e⟩ := exists_S2_of_lt hk
      exact ⟨⟨g, S2_le_R3 hg⟩, Subgroup.mem_subgroupOf.mpr hg, fun _ => e⟩
    · exact ⟨1, S2H.one_mem, fun h => absurd h hk⟩
  exact ⟨fun k => (h k).choose, fun k => (h k).choose_spec⟩

noncomputable def sE : ℕ → H3 := Classical.choose exists_sE

theorem coe_sE {k : ℕ} (hk : k < elemsS.size) : (((sE k : H3) : GL14) : M14) = dec14 (es k) :=
  (Classical.choose_spec exists_sE k).2 hk

theorem sE_inj {a b : ℕ} (ha : a < elemsS.size) (hb : b < elemsS.size) (h : sE a = sE b) :
    a = b := by
  have e : dec14 (es a) = dec14 (es b) := by rw [← coe_sE ha, ← coe_sE hb, h]
  exact distinctCheck_spec certS.2.2.1 ha hb
    (dec14_injective (allCheck_spec certS.2.2.2 ha) (allCheck_spec certS.2.2.2 hb) e)

theorem exists_sE_eq {x : H3} (hx : x ∈ S2H) : ∃ k < elemsS.size, x = sE k := by
  obtain ⟨k, hk, hcode⟩ := exists_code_S2 (Subgroup.mem_subgroupOf.mp hx)
  refine ⟨k, hk, Subtype.ext (Units.ext ?_)⟩
  rw [coe_sE hk]
  exact hcode.symm

end Elements

section Checks

theorem closedL_k1s : closedL k1s = true := (c0_spec s7g23Checks_holds.1).1

theorem closedL_k2s : closedL k2s = true := (c0_spec s7g23Checks_holds.1).2.1

theorem q8RelC_one_two : q8RelC (es 1) (es 2) = true := (c0_spec s7g23Checks_holds.1).2.2.1

theorem q8RelC_three_four : q8RelC (es 3) (es 4) = true :=
  (c0_spec s7g23Checks_holds.1).2.2.2.1

theorem sq14_es_one : sq14 (es 1) = tc := (c0_spec s7g23Checks_holds.1).2.2.2.2.1

theorem sq14_es_three : sq14 (es 3) = tc := (c0_spec s7g23Checks_holds.1).2.2.2.2.2.1

theorem k1s_lt : ∀ k ∈ k1s, k < elemsS.size := (c0_spec s7g23Checks_holds.1).2.2.2.2.2.2.1

theorem k2s_lt : ∀ k ∈ k2s, k < elemsS.size := (c0_spec s7g23Checks_holds.1).2.2.2.2.2.2.2

end Checks

structure KData (ks : List ℕ) : Prop where
  lt : ∀ k ∈ ks, k < elemsS.size
  closed : closedL ks = true
  nonempty : ∃ k, k ∈ ks

section Quaternions

def kSet (ks : List ℕ) : Set H3 := {x | ∃ k ∈ ks, x = sE k}

theorem exists_mul_sE {ks : List ℕ} (hk : KData ks) {a b : ℕ} (ha : a ∈ ks) (hb : b ∈ ks) :
    ∃ c ∈ ks, sE a * sE b = sE c := by
  have hcl := hk.closed
  simp only [closedL, List.all_eq_true, List.any_eq_true, beq_iff_eq] at hcl
  obtain ⟨c, hc, hmul⟩ := hcl a ha b hb
  refine ⟨c, hc, Subtype.ext (Units.ext ?_)⟩
  rw [Subgroup.coe_mul, Units.val_mul, coe_sE (hk.lt a ha), coe_sE (hk.lt b hb),
    coe_sE (hk.lt c hc), ← dec14_mul14, hmul]

theorem kSet_nonempty {ks : List ℕ} (hk : KData ks) : (kSet ks).Nonempty := by
  obtain ⟨k, hk'⟩ := hk.nonempty
  exact ⟨sE k, k, hk', rfl⟩

theorem kSet_mul {ks : List ℕ} (hk : KData ks) :
    ∀ x ∈ kSet ks, ∀ y ∈ kSet ks, x * y ∈ kSet ks := by
  rintro x ⟨a, ha, hxa⟩ y ⟨b, hb, hyb⟩
  obtain ⟨c, hc, e⟩ := exists_mul_sE hk ha hb
  exact ⟨c, hc, by rw [hxa, hyb, e]⟩

@[expose] noncomputable def kSubgroup (ks : List ℕ) (hk : KData ks) : Subgroup H3 :=
  mulClosedSubgroup (kSet ks) (kSet_nonempty hk) (kSet_mul hk)

theorem mem_kSubgroup {ks : List ℕ} {hk : KData ks} {x : H3} :
    x ∈ kSubgroup ks hk ↔ ∃ k ∈ ks, x = sE k :=
  Iff.rfl

theorem sE_mem_kSubgroup {ks : List ℕ} (hk : KData ks) {k : ℕ} (hk' : k ∈ ks) :
    sE k ∈ kSubgroup ks hk :=
  mem_kSubgroup.mpr ⟨k, hk', rfl⟩

theorem card_kSubgroup {ks : List ℕ} (hk : KData ks) (hnd : ks.Nodup) (hlen : ks.length = 8) :
    Nat.card (kSubgroup ks hk) = 8 := by
  have h1 : (kSubgroup ks hk : Set H3) = sE '' {k | k ∈ ks} := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk', hxk⟩ := mem_kSubgroup.mp hx
      exact ⟨k, hk', hxk.symm⟩
    · rintro ⟨k, hk', hkx⟩
      rw [← hkx]
      exact sE_mem_kSubgroup hk hk'
  have hinj : Set.InjOn sE {k | k ∈ ks} := fun a ha b hb hab =>
    sE_inj (hk.lt a ha) (hk.lt b hb) hab
  have h3 : Nat.card (kSubgroup ks hk) = Nat.card (sE '' {k | k ∈ ks}) := by
    rw [← h1]; rfl
  rw [h3, Nat.card_image_of_injOn hinj, Nat.card_coe_set_eq, ← List.coe_toFinset,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen]

theorem X0H_le_normalizer {ks : List ℕ} (hk : KData ks)
    (hc2 : ∀ y ∈ gensX, ∀ k ∈ ks, ∃ k' ∈ ks, mul14 y (es k) = mul14 (es k') y) :
    X0H ≤ Subgroup.normalizer (kSubgroup ks hk : Set H3) := by
  have hgen : ∀ g : H3, (g : GL14) ∈ ({gX 1, gY 1, uU, vU, h0U} : Set GL14) →
      g ∈ Subgroup.normalizer (kSubgroup ks hk : Set H3) := by
    intro g hg
    obtain ⟨c, hc, hcg⟩ : ∃ c ∈ gensX, dec14 c = ((g : GL14) : M14) := by
      have h : (Units.coeHom M14) (g : GL14) ∈
          (Units.coeHom M14) '' ({gX 1, gY 1, uU, vU, h0U} : Set GL14) := ⟨g, hg, rfl⟩
      rw [image_gens_X0] at h
      exact h
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨k, hkm, hxk⟩ := mem_kSubgroup.mp hx
    rw [hxk]
    obtain ⟨k', hk', hmul⟩ := hc2 c hc k hkm
    have h1 : g * sE k = sE k' * g := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_sE (hk.lt k hkm),
        coe_sE (hk.lt k' hk'), ← hcg, ← dec14_mul14, ← dec14_mul14, hmul]
    have h2 : g * sE k * g⁻¹ = sE k' := by rw [h1, mul_assoc, mul_inv_cancel, mul_one]
    rw [h2]
    exact sE_mem_kSubgroup hk hk'
  intro x hx
  have hx' : (x : GL14) ∈ X0 := Subgroup.mem_subgroupOf.mp hx
  have key : X0 ≤ (Subgroup.normalizer (kSubgroup ks hk : Set H3)).map R3.subtype := by
    rw [X0, Subgroup.closure_le]
    intro g hg
    have hgR : g ∈ R3 := X0_le_R3 (Subgroup.subset_closure hg)
    exact ⟨⟨g, hgR⟩, hgen ⟨g, hgR⟩ hg, rfl⟩
  obtain ⟨y, hy, hyx⟩ := key hx'
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hy

end Quaternions

section KDataK

theorem kData1 : KData k1s := ⟨k1s_lt, closedL_k1s, ⟨0, by decide⟩⟩

theorem kData2 : KData k2s := ⟨k2s_lt, closedL_k2s, ⟨0, by decide⟩⟩

theorem conj_k1s : ∀ y ∈ gensX, ∀ k ∈ k1s, ∃ k' ∈ k1s, mul14 y (es k) = mul14 (es k') y :=
  fun _ hy _ hk => c2_spec s7g23Checks_holds.2.2.1 (Or.inl rfl) hy hk

theorem conj_k2s : ∀ y ∈ gensX, ∀ k ∈ k2s, ∃ k' ∈ k2s, mul14 y (es k) = mul14 (es k') y :=
  fun _ hy _ hk => c2_spec s7g23Checks_holds.2.2.1 (Or.inr rfl) hy hk

end KDataK

section Model

@[expose] noncomputable def K1 : Subgroup H3 := kSubgroup k1s kData1

@[expose] noncomputable def K2 : Subgroup H3 := kSubgroup k2s kData2

theorem card_K1 : Nat.card K1 = 8 := card_kSubgroup kData1 (by decide) (by decide)

theorem card_K2 : Nat.card K2 = 8 := card_kSubgroup kData2 (by decide) (by decide)

theorem sE_mem_K1 {k : ℕ} (hk : k ∈ k1s) : sE k ∈ K1 := sE_mem_kSubgroup kData1 hk

theorem sE_mem_K2 {k : ℕ} (hk : k ∈ k2s) : sE k ∈ K2 := sE_mem_kSubgroup kData2 hk

theorem q8Rel_sE {a b : ℕ} (ha : a < elemsS.size) (hb : b < elemsS.size)
    (h : q8RelC (es a) (es b) = true) : Q8Rel (sE a) (sE b) :=
  q8Rel_of_injective R3.subtype R3.subtype_injective
    (q8Rel_of_q8RelC (coe_sE ha) (coe_sE hb) h)

theorem q8RelC_sE {a b : ℕ} (ha : a < elemsS.size) (hb : b < elemsS.size)
    (h : Q8Rel (sE a) (sE b)) : q8RelC (es a) (es b) = true := by
  have hcanon := allCheck_spec certS.2.2.2 hb
  exact q8RelC_of_q8Rel hcanon (coe_sE ha) (coe_sE hb) (q8Rel_coe h)

theorem sE_one_mul_self : sE 1 * sE 1 = tH := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_sE (kData1.lt 1 (by decide)), coe_tH, coe_tU,
    ← dec14_mul14]
  exact congrArg dec14 sq14_es_one

theorem sE_three_mul_self : sE 3 * sE 3 = tH := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_sE (kData2.lt 3 (by decide)), coe_tH, coe_tU,
    ← dec14_mul14]
  exact congrArg dec14 sq14_es_three

theorem K1_q8 : K1 ∈ q8Fam H3 ∧ IsUniqueInvolution K1 tH := by
  have := q8_of_pair card_K1 (sE_mem_K1 (by decide : 1 ∈ k1s)) (sE_mem_K1 (by decide : 2 ∈ k1s))
    (q8Rel_sE (kData1.lt 1 (by decide)) (kData1.lt 2 (by decide)) q8RelC_one_two)
  rwa [sE_one_mul_self] at this

theorem K2_q8 : K2 ∈ q8Fam H3 ∧ IsUniqueInvolution K2 tH := by
  have := q8_of_pair card_K2 (sE_mem_K2 (by decide : 3 ∈ k2s)) (sE_mem_K2 (by decide : 4 ∈ k2s))
    (q8Rel_sE (kData2.lt 3 (by decide)) (kData2.lt 4 (by decide)) q8RelC_three_four)
  rwa [sE_three_mul_self] at this

theorem K1_ne_K2 : K1 ≠ K2 := by
  intro h
  have h1 : sE 1 ∈ K2 := by rw [← h]; exact sE_mem_K1 (by decide)
  obtain ⟨b, hb, hbe⟩ := mem_kSubgroup.mp h1
  have hb1 : 1 = b := sE_inj (kData1.lt 1 (by decide)) (kData2.lt b hb) hbe
  rw [← hb1] at hb
  exact absurd hb (by decide)

theorem X0H_le_normalizer_K1 : X0H ≤ Subgroup.normalizer (K1 : Set H3) :=
  X0H_le_normalizer kData1 conj_k1s

theorem X0H_le_normalizer_K2 : X0H ≤ Subgroup.normalizer (K2 : Set H3) :=
  X0H_le_normalizer kData2 conj_k2s

theorem conjSub_eq_of_le_S2 {T : Subgroup H3} (hT : T ∈ q8Fam H3) {g : H3}
    (hg : ∀ x ∈ T, g⁻¹ * x * g ∈ S2H) : conjSub g K1 = T ∨ conjSub g K2 = T := by
  have hcard : Nat.card T = 8 := card_of_mem_q8Fam hT
  obtain ⟨e⟩ := hT
  obtain ⟨i, hi, j, hj, hij, hspan⟩ := exists_q8Pair e
  obtain ⟨a, ha, hia⟩ := exists_sE_eq (hg i hi)
  obtain ⟨b, hb, hjb⟩ := exists_sE_eq (hg j hj)
  have hq : Q8Rel (g⁻¹ * i * g) (g⁻¹ * j * g) := q8Rel_conj g hij
  have hq' : Q8Rel (sE a) (sE b) := by
    rw [← hia, ← hjb]
    exact hq
  have hqc : q8RelC (es a) (es b) = true := q8RelC_sE ha hb hq'
  have h64 := certS.1
  have key : ∀ K : Subgroup H3, Nat.card K = 8 → sE a ∈ K → sE b ∈ K → conjSub g K = T := by
    intro K hK haK hbK
    have hiK : i ∈ conjSub g K := mem_conjSub_iff.mpr (by rw [hia]; exact haK)
    have hjK : j ∈ conjSub g K := mem_conjSub_iff.mpr (by rw [hjb]; exact hbK)
    have hle : T ≤ conjSub g K := fun t ht => mem_of_mem_q8Span hiK hjK (hspan t ht)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub_eq, hK, hcard])).symm
  rcases c1_spec s7g23Checks_holds.2.1 (by omega) (by omega) hqc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (key K1 card_K1 (sE_mem_K1 h1) (sE_mem_K1 h2))
  · exact Or.inr (key K2 card_K2 (sE_mem_K2 h1) (sE_mem_K2 h2))

theorem eq_K1_or_K2_of_le_X0H {T : Subgroup H3} (hT : T ∈ q8Fam H3) (hTX : T ≤ X0H) :
    T = K1 ∨ T = K2 := by
  have hS : S2H ≤ X0H := Subgroup.subgroupOf_mono _ S2_le_X0
  have hcS : Nat.card (S2H.subgroupOf X0H) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv, card_S2H]
  have hP : IsPGroup 2 (S2H.subgroupOf X0H) := IsPGroup.of_card (n := 6) (by rw [hcS]; norm_num)
  have hidx : ¬ 2 ∣ (S2H.subgroupOf X0H).index := by
    have h := Subgroup.card_mul_index (S2H.subgroupOf X0H)
    rw [hcS, card_X0H] at h
    have h9 : (S2H.subgroupOf X0H).index = 9 := by omega
    rw [h9]
    decide
  have hH : IsPGroup 2 (T.subgroupOf X0H) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv, card_of_mem_q8Fam hT]
    norm_num
  obtain ⟨x, hx⟩ := exists_conj_mem_of_isPGroup hP hidx hH
  have hg : ∀ y ∈ T, (x : H3)⁻¹ * y * x ∈ S2H := fun y hy =>
    Subgroup.mem_subgroupOf.mp (hx ⟨y, hTX hy⟩ (Subgroup.mem_subgroupOf.mpr hy))
  rcases conjSub_eq_of_le_S2 hT hg with h | h
  · left
    rw [← h]
    exact conjSub_eq_of_mem_normalizer (X0H_le_normalizer_K1 x.2)
  · right
    rw [← h]
    exact conjSub_eq_of_mem_normalizer (X0H_le_normalizer_K2 x.2)

@[expose] noncomputable def gE : H3 := ⟨gU, gU_mem⟩

theorem coe_conj_sE {k : ℕ} (hk : k < elemsS.size) (h : mul14 (gc ()) (gic ()) = one14) :
    (((gE * sE k * gE⁻¹ : H3) : GL14) : M14) =
      dec14 (mul14 (mul14 (gc ()) (es k)) (gic ())) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact coe_mul (coe_mul coe_gU (coe_sE hk)) (coe_gU_inv h)

theorem coe_sE_sq {k : ℕ} (hk : k < elemsS.size) :
    (((sE k ^ 2 : H3) : GL14) : M14) = dec14 (sq14 (es k)) := by
  rw [Subgroup.coe_pow]
  exact coe_sq (coe_sE hk)

theorem coe_sE_pow_four {k : ℕ} (hk : k < elemsS.size) :
    (((sE k ^ 4 : H3) : GL14) : M14) = dec14 (sq14 (sq14 (es k))) := by
  have h : sE k ^ 4 = (sE k ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h, Subgroup.coe_pow]
  exact coe_sq (coe_sE_sq hk)

theorem orderOf_sE {k : ℕ} (hk : k < elemsS.size) (h2 : sq14 (es k) ≠ one14)
    (h4 : sq14 (sq14 (es k)) = one14) : orderOf (sE k) = 4 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : sE k ^ 2 ≠ 1 := by
    intro h
    apply h2
    have hcode := coe_sE_sq hk
    rw [h, Subgroup.coe_one, Units.val_one] at hcode
    exact dec14_injective (canon14_mul14 _ _) canon14_one14 (by rw [← hcode, dec14_one14])
  have hq4 : sE k ^ 4 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_sE_pow_four hk, h4, dec14_one14, Subgroup.coe_one, Units.val_one]
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := sE k) (by simpa using hsq)
    (by simpa using hq4)
  simpa using this

theorem edgeIn_R3 : ∃ c ∈ K2, orderOf c = 4 ∧ gE * c * gE⁻¹ ∈ X0H := by
  obtain ⟨h1, h2, h3, h4, -⟩ := c3_spec s7g23Checks_holds.2.2.2.1
  have hlt : 4 < elemsS.size := kData2.lt 4 (by decide)
  refine ⟨sE 4, sE_mem_K2 (by decide), orderOf_sE hlt h2 h3, ?_⟩
  obtain ⟨t, ht, hcode⟩ := exists_getD_of_mem h4
  have hmem : dec14 (elemsX.getD t []) ∈ (Units.coeHom M14) '' (X0 : Set GL14) := by
    rw [image_X0]
    exact ⟨t, ht, rfl⟩
  obtain ⟨y, hyX, hyc⟩ := hmem
  refine Subgroup.mem_subgroupOf.mpr ?_
  have e : ((gE * sE 4 * gE⁻¹ : H3) : GL14) = y := by
    apply Units.ext
    rw [coe_conj_sE hlt h1, ← hcode]
    exact hyc.symm
  rw [e]
  exact hyX

theorem edgeOut_R3 : ∃ k ∈ K2, gE * k * gE⁻¹ ∉ X0H := by
  obtain ⟨h1, -, -, -, h5⟩ := c3_spec s7g23Checks_holds.2.2.2.1
  have hlt : 25 < elemsS.size := kData2.lt 25 (by decide)
  refine ⟨sE 25, sE_mem_K2 (by decide), fun hmem => h5 ?_⟩
  obtain ⟨t, ht, hcode⟩ := exists_code_X0 (Subgroup.mem_subgroupOf.mp hmem)
  have e : dec14 (elemsX.getD t []) = dec14 (mul14 (mul14 (gc ()) (es 25)) (gic ())) := by
    rw [hcode, coe_conj_sE hlt h1]
  have hcanon := allCheck_spec certX.2.2.2.1 ht
  have := dec14_injective hcanon (canon14_mul14 _ _) e
  rw [← this]
  exact getD_mem_of_lt ht

theorem gen_R3 : ∀ N : Subgroup H3, X0H ≤ N → gE ∈ N → N = ⊤ := by
  intro N hXN hgN
  obtain ⟨hinv, -, -, -, -⟩ := c3_spec s7g23Checks_holds.2.2.2.1
  obtain ⟨hx0, hy0⟩ := c4_spec s7g23Checks_holds.2.2.2.2
  obtain ⟨h1, h2, hu, hv, hh⟩ := gens_mem_X0
  have hmemN : ∀ z : GL14, z ∈ X0 → z ∈ N.map R3.subtype := fun z hz =>
    ⟨⟨z, X0_le_R3 hz⟩, hXN (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  have hg' : gU ∈ N.map R3.subtype := ⟨gE, hgN, rfl⟩
  have hX : ∀ n : Fin 2, gX n ∈ N.map R3.subtype := by
    refine Fin.forall_fin_two.mpr ⟨?_, hmemN _ h1⟩
    have e : gX 0 = gU ^ 2 * vU ^ 2 * gU⁻¹ ^ 2 := by
      apply Units.ext
      rw [coe_mul (coe_mul (coe_sq coe_gU) (coe_sq coe_vU)) (coe_sq (coe_gU_inv hinv)), ← hx0,
        coe_gX0]
    rw [e]
    exact mul_mem (mul_mem (pow_mem hg' 2) (pow_mem (hmemN _ hv) 2))
      (pow_mem (inv_mem hg') 2)
  have hY : ∀ n : Fin 2, gY n ∈ N.map R3.subtype := by
    refine Fin.forall_fin_two.mpr ⟨?_, hmemN _ h2⟩
    have e : gY 0 = gU⁻¹ ^ 2 * uU * gU ^ 2 := by
      apply Units.ext
      rw [coe_mul (coe_mul (coe_sq (coe_gU_inv hinv)) coe_uU) (coe_sq coe_gU), ← hy0, coe_gY0]
    rw [e]
    exact mul_mem (mul_mem (pow_mem (inv_mem hg') 2) (hmemN _ hu)) (pow_mem hg' 2)
  have hR := R3_le_of_gens _ hX hY
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hR x.2
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hy

end Model

section Full

theorem centralizer_tH_eq_X0H : Subgroup.centralizer {tH} = X0H := by
  have h : Nat.card (Subgroup.centralizer {tH}) * 7371 ≤ Nat.card H3 :=
    card_centralizer_mul_le orbitElt orbitElt_injective orbitElt_conj
  have hR : Nat.card H3 = 4245696 := card_R3
  have hX : Nat.card X0H = 576 := card_X0H
  exact (Subgroup.eq_of_le_of_card_ge X0H_le_centralizer (by
    rw [hX]
    exact Nat.le_of_mul_le_mul_right (h.trans (hR.le.trans (by norm_num))) (by norm_num))).symm

theorem census_R3 : ∀ T ∈ q8Fam H3, ∃ a : H3, conjSub a K1 = T ∨ conjSub a K2 = T := by
  intro T hT
  obtain ⟨g, hg⟩ := g23_conj_mem_S2H T (isPGroup_of_mem_q8Fam hT)
  exact ⟨g, conjSub_eq_of_le_S2 hT hg⟩

@[expose] noncomputable def g23Data_R3 : G23Data H3 where
  t := tH
  X := X0H
  K₁ := K1
  K₂ := K2
  g := gE
  cent := centralizer_tH_eq_X0H
  census := census_R3
  censusX := fun _ hT hTX => eq_K1_or_K2_of_le_X0H hT hTX
  mem₁ := K1_q8.1
  mem₂ := K2_q8.1
  inv₁ := K1_q8.2
  inv₂ := K2_q8.2
  nor₁ := X0H_le_normalizer_K1
  ne := K1_ne_K2
  edgeIn := edgeIn_R3
  edgeOut := edgeOut_R3
  gen := gen_R3

end Full

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23
