module

public import CFSG.CGT.PushingUpLit.A78S4.Nat
public import CFSG.CGT.PushingUpLit.A78L3.Tori
public import CFSG.CGT.PushingUpLit.T2K.Nat

public section

namespace CFSG.CGT.PushingUpLit.A78S4

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78L3
open CFSG.ABGLocalTools
open Matrix
open scoped commutatorElement

structure S4Side (G : Type) [Group G] [Finite G] (L V W Z T : Subgroup G) (e : ℕ) : Prop where
  jst : JStructure G (V ⊔ W) V W e
  nat : Nonempty (NatCoordK G L V Z (GaloisField 2 e))
  Z_cent : Z ≤ Subgroup.centralizer (L : Set G)
  sylowJ : IsSylowOf 2 (V ⊔ W) L
  J_le_T : V ⊔ W ≤ T
  pT : IsPGroup 2 T
  T_le_L : T ≤ Subgroup.normalizer (L : Set G)
  T_le_V : T ≤ Subgroup.normalizer (V : Set G)
  T_le_W : T ≤ Subgroup.normalizer (W : Set G)
  cent : ∀ t ∈ T, (∀ v ∈ V, t * v * t⁻¹ * v⁻¹ ∈ Z) → t ∈ V

theorem eq_one_of_fix_two {F : Type} [Field F] {M : SpecialLinearGroup (Fin 2) F}
    {x y : Fin 2 → F} (hxy : det2 x y ≠ 0) (hx : (M : Matrix (Fin 2) (Fin 2) F) *ᵥ x = x)
    (hy : (M : Matrix (Fin 2) (Fin 2) F) *ᵥ y = y) : M = 1 := by
  have hy' : det2 x ((det2 x y)⁻¹ • y) = 1 := by rw [det2_smul_right, inv_mul_cancel₀ hxy]
  refine CFSG.CGT.PushingUpLit.T2K.eq_of_forall_mulVec fun u => ?_
  rw [eq_det2_smul hy' u, mulVec_add, mulVec_smul, mulVec_smul, hx, mulVec_smul, hy]
  simp

namespace S4Side

variable {G : Type} [Group G] [Finite G] {L V W Z T : Subgroup G} {e : ℕ}

section Basic

variable (h : S4Side G L V W Z T e)

include h

theorem two_le : 2 ≤ e := h.jst.two_le

theorem e_ne_zero : e ≠ 0 := by have := h.two_le; omega

theorem J_le_L : V ⊔ W ≤ L := h.sylowJ.le

theorem V_le_L : V ≤ L := le_sup_left.trans h.J_le_L

theorem W_le_L : W ≤ L := le_sup_right.trans h.J_le_L

theorem V_le_T : V ≤ T := le_sup_left.trans h.J_le_T

theorem W_le_T : W ≤ T := le_sup_right.trans h.J_le_T

theorem Z_le_V : Z ≤ V := by
  obtain ⟨D⟩ := h.nat
  exact D.K_le

theorem card_F : Nat.card (GaloisField 2 e) = 2 ^ e := GaloisField.card 2 e h.e_ne_zero

theorem mem_Z_of_cent {v : G} (hv : v ∈ V) (hc : v ∈ Subgroup.centralizer (L : Set G)) :
    v ∈ Z := by
  obtain ⟨D⟩ := h.nat
  by_contra hvZ
  have h0 := D.κ_ne_zero hv hvZ
  obtain ⟨y, hy0, hyv⟩ : ∃ y : Fin 2 → GaloisField 2 e, y ≠ 0 ∧ y ≠ D.κ v := by
    by_cases h1 : D.κ v = Pi.single 0 1
    · refine ⟨Pi.single 1 1, fun h2 => ?_, fun h2 => ?_⟩
      · have := congrFun h2 1
        simp at this
      · rw [h1] at h2
        have := congrFun h2 1
        simp at this
    · refine ⟨Pi.single 0 1, fun h2 => ?_, fun h2 => h1 h2.symm⟩
      have := congrFun h2 0
      simp at this
  obtain ⟨M, -, hM⟩ := exists_fixSL_mulVec_eq (σ := RingEquiv.refl _) h0 hy0 (fun _ => rfl)
    (fun _ => rfl)
  obtain ⟨l, hl, hlM⟩ := D.ρ_surj M
  have h1 : l * v * l⁻¹ = v := by
    rw [Subgroup.mem_centralizer_iff.1 hc l hl]
    group
  have h2 := D.conj l hl v hv
  rw [h1, hlM] at h2
  exact hyv (hM.symm.trans h2.symm)

theorem T_le_Z : T ≤ Subgroup.normalizer (Z : Set G) := by
  refine le_normalizer_of_conj fun t ht z hz => ?_
  refine h.mem_Z_of_cent (conj_mem_of_mem_normalizer (h.T_le_V ht) (h.Z_le_V hz))
    (Subgroup.mem_centralizer_iff.2 fun l hl => ?_)
  have htl : t⁻¹ * l * t ∈ L := by
    have := conj_mem_of_mem_normalizer (inv_mem (h.T_le_L ht)) hl
    simpa using this
  have hzl := Subgroup.mem_centralizer_iff.1 (h.Z_cent hz) _ htl
  calc l * (t * z * t⁻¹) = t * ((t⁻¹ * l * t) * z) * t⁻¹ := by group
    _ = t * (z * (t⁻¹ * l * t)) * t⁻¹ := by rw [hzl]
    _ = t * z * t⁻¹ * l := by group

theorem T_le_NVK : T ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G) :=
  le_inf h.T_le_V h.T_le_Z

theorem Z_le_N : Z ≤ V ⊓ W := by
  obtain ⟨w, hw, hwV⟩ : ∃ w ∈ W, w ∉ V := by
    by_contra hcon
    push Not at hcon
    exact h.jst.not_le_V hcon
  intro z hz
  have : z ∈ V ⊓ Subgroup.centralizer ({w} : Set G) :=
    ⟨h.Z_le_V hz, Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 (h.Z_cent hz) w (h.W_le_L hw)).symm⟩
  rwa [h.jst.inf_centralizer_eq hw hwV] at this

theorem card_V : Nat.card V = 2 ^ (2 * e) * Nat.card Z := by
  obtain ⟨D⟩ := h.nat
  rw [D.card_V, h.card_F, ← pow_mul, mul_comm e 2]

theorem card_N : Nat.card ↥(V ⊓ W) = 2 ^ e * Nat.card Z := by
  have h1 := h.jst.card_V_eq
  rw [h.card_V] at h1
  have hpos : 0 < 2 ^ e := by positivity
  have h2 : 2 ^ e * (2 ^ e * Nat.card Z) = 2 ^ e * Nat.card ↥(V ⊓ W) := by
    rw [← h1, ← mul_assoc, ← pow_add, show e + e = 2 * e by ring]
  exact (Nat.eq_of_mul_eq_mul_left hpos h2).symm

theorem exists_N_not_Z : ∃ n ∈ V ⊓ W, n ∉ Z := by
  by_contra hcon
  push Not at hcon
  have h1 := Subgroup.card_le_of_le (H := V ⊓ W) (K := Z) hcon
  rw [h.card_N] at h1
  have hpos : 0 < Nat.card Z := Nat.card_pos
  have h2 : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by have := h.two_le; omega)
  nlinarith

theorem ρ_fix_N (D : NatCoordK G L V Z (GaloisField 2 e)) {j n : G} (hj : j ∈ V ⊔ W)
    (hn : n ∈ V ⊓ W) :
    (D.ρ j : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ n = D.κ n := by
  rw [← D.conj j (h.J_le_L hj) n hn.1]
  congr 1
  rw [(h.jst.commute_of_mem_inf hn hj).eq.symm]
  group

theorem mem_J_iff (D : NatCoordK G L V Z (GaloisField 2 e)) {n₀ : G} (hn₀ : n₀ ∈ V ⊓ W)
    (hn₀Z : n₀ ∉ Z) {l : G} (hl : l ∈ L) :
    l ∈ V ⊔ W ↔ (D.ρ l : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ n₀ = D.κ n₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun hj => h.ρ_fix_N D hj hn₀, fun hfix => ?_⟩
  let H : Subgroup G :=
    { carrier := {g | g ∈ L ∧ (D.ρ g : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ n₀ =
        D.κ n₀}
      one_mem' := ⟨L.one_mem, by rw [D.ρ_one]; simp⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [D.ρ_mulVec_mul ha.1 hb.1, hb.2, ha.2]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have h1 : (D.ρ a⁻¹ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ
            ((D.ρ a : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ n₀) =
            (D.ρ a⁻¹ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ n₀ := by rw [ha.2]
        rw [← D.ρ_mulVec_mul (inv_mem ha.1) ha.1, inv_mul_cancel,
          D.ρ_mulVec_of_mem L.one_mem V.one_mem] at h1
        exact h1.symm⟩ }
  have hJH : V ⊔ W ≤ H := fun j hj => ⟨h.J_le_L hj, h.ρ_fix_N D hj hn₀⟩
  have hH2 : IsPGroup 2 H := by
    intro g
    refine ⟨2, Subtype.ext ?_⟩
    have hsq := D.sq_mem_of_fix hn₀.1 hn₀Z g.2.1 g.2.2
    have h1 := h.jst.sq_V _ hsq
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    calc (g : G) ^ 2 ^ 2 = (g : G) * g * ((g : G) * g) := by
          rw [show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add, pow_two]
      _ = 1 := h1
  have hHJ := h.sylowJ.eq_of_le hJH (fun g hg => hg.1) hH2
  rw [← hHJ]
  exact ⟨hl, hfix⟩

theorem det2_κ_N (D : NatCoordK G L V Z (GaloisField 2 e)) {n₀ n : G} (hn₀ : n₀ ∈ V ⊓ W)
    (hn : n ∈ V ⊓ W) : det2 (D.κ n₀) (D.κ n) = 0 := by
  by_contra hd
  obtain ⟨w, hw, hwV⟩ : ∃ w ∈ W, w ∉ V := by
    by_contra hcon
    push Not at hcon
    exact h.jst.not_le_V hcon
  have hwJ : w ∈ V ⊔ W := Subgroup.mem_sup_right hw
  have h1 := eq_one_of_fix_two hd (h.ρ_fix_N D hwJ hn₀) (h.ρ_fix_N D hwJ hn)
  exact hwV ((D.ρ_eq_one w (h.W_le_L hw)).1 h1)

end Basic

structure Frame (h : S4Side G L V W Z T e) (D : NatCoordK G L V Z (GaloisField 2 e)) where
  n₀ : G
  hn₀ : n₀ ∈ V ⊓ W
  hn₀Z : n₀ ∉ Z
  y₀ : Fin 2 → GaloisField 2 e
  hdet : det2 (D.κ n₀) y₀ = 1
  w₁ : G
  hw₁ : w₁ ∈ W
  hb : det2 ((D.ρ w₁ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ y₀) y₀ = 1

theorem exists_transvection {F : Type} [Field F] (x₀ : Fin 2 → F) (q : F) :
    ∃ M : SpecialLinearGroup (Fin 2) F,
      ∀ u, (M : Matrix (Fin 2) (Fin 2) F) *ᵥ u = u + (det2 x₀ u * q) • x₀ := by
  let M : Matrix (Fin 2) (Fin 2) F :=
    Matrix.of fun i k => (Pi.single k 1 : Fin 2 → F) i + (det2 x₀ (Pi.single k 1) * q) * x₀ i
  have hM : ∀ u, M *ᵥ u = u + (det2 x₀ u * q) • x₀ := by
    intro u
    ext i
    fin_cases i <;> simp [M, mulVec, dotProduct, Fin.sum_univ_two, det2] <;> ring
  have hdet : M.det = 1 := by
    rw [det_fin_two]
    simp [M, det2]
    ring
  exact ⟨⟨M, hdet⟩, hM⟩

section Frames

variable (h : S4Side G L V W Z T e)

include h

theorem exists_frame (D : NatCoordK G L V Z (GaloisField 2 e)) : Nonempty (Frame h D) := by
  obtain ⟨n₀, hn₀, hn₀Z⟩ := h.exists_N_not_Z
  obtain ⟨y₀, hy₀⟩ := exists_det2_eq_one (D.κ_ne_zero hn₀.1 hn₀Z)
  obtain ⟨M, hM⟩ := exists_transvection (D.κ n₀) (1 : GaloisField 2 e)
  obtain ⟨l, hl, hlM⟩ := D.ρ_surj M
  have hlM' : (D.ρ l : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) = M := by rw [hlM]
  have hlJ : l ∈ V ⊔ W := by
    rw [h.mem_J_iff D hn₀ hn₀Z hl, hlM', hM, det2_self, zero_mul, zero_smul, add_zero]
  obtain ⟨v, hv, w, hw, rfl⟩ := (h.jst.mem_sup_iff).1 hlJ
  refine ⟨⟨n₀, hn₀, hn₀Z, y₀, hy₀, w, hw, ?_⟩⟩
  have hρv : D.ρ v = 1 := (D.ρ_eq_one v (h.V_le_L hv)).2 hv
  have e1 : D.ρ w = D.ρ (v * w) := by
    rw [D.ρ_mul v (h.V_le_L hv) w (h.W_le_L hw), hρv, one_mul]
  rw [e1, hlM', hM, det2_add_left, det2_self, zero_add, det2_smul_left, hy₀, mul_one, mul_one]

theorem cent_L (D : NatCoordK G L V Z (GaloisField 2 e)) {n : G} (hn : n ∈ V ⊓ W) (hnZ : n ∉ Z) :
    L ⊓ Subgroup.centralizer ({n} : Set G) = V ⊔ W := by
  apply le_antisymm
  · rintro l ⟨hl, hlc⟩
    rw [h.mem_J_iff D hn hnZ hl, ← D.conj l hl n hn.1]
    congr 1
    rw [Subgroup.mem_centralizer_singleton_iff.1 hlc]
    group
  · intro j hj
    exact ⟨h.J_le_L hj, Subgroup.mem_centralizer_singleton_iff.2
      ((h.jst.commute_of_mem_inf hn hj).eq).symm⟩

end Frames

variable {h : S4Side G L V W Z T e} {D : NatCoordK G L V Z (GaloisField 2 e)}

namespace Frame

variable (fr : Frame h D)

@[expose] noncomputable def c (g : G) : GaloisField 2 e := det2 (D.κ g) fr.y₀

@[expose] noncomputable def b (g : G) : GaloisField 2 e :=
  det2 ((D.ρ g : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀) fr.y₀

@[expose] noncomputable def a (g : G) : GaloisField 2 e := fr.c ⁅g, fr.w₁⁆

theorem κ_eq_c {n : G} (hn : n ∈ V ⊓ W) : D.κ n = fr.c n • D.κ fr.n₀ := by
  have h1 := eq_det2_smul fr.hdet (D.κ n)
  rw [h.det2_κ_N D fr.hn₀ hn, zero_smul, add_zero] at h1
  exact h1

theorem c_mul {v v' : G} (hv : v ∈ V) (hv' : v' ∈ V) : fr.c (v * v') = fr.c v + fr.c v' := by
  rw [c, c, c, D.κ_mul v hv v' hv', det2_add_left]

theorem c_one : fr.c 1 = 0 := by rw [c, D.κ_one]; simp [det2]

theorem c_inv {v : G} (hv : v ∈ V) : fr.c v⁻¹ = fr.c v := by
  rw [c, c, D.κ_inv hv, det2_neg_left, CharTwo.neg_eq]

theorem c_of_mem_Z {z : G} (hz : z ∈ Z) : fr.c z = 0 := by
  rw [c, D.κ_of_mem_K hz]
  simp [det2]

theorem c_eq_zero_iff {n : G} (hn : n ∈ V ⊓ W) : fr.c n = 0 ↔ n ∈ Z := by
  refine ⟨fun h0 => ?_, fr.c_of_mem_Z⟩
  refine (D.κ_eq_zero n hn.1).1 ?_
  rw [fr.κ_eq_c hn, h0, zero_smul]

theorem c_surj (r : GaloisField 2 e) : ∃ n ∈ V ⊓ W, fr.c n = r := by
  let φ : ↥(V ⊓ W) →* Multiplicative (GaloisField 2 e) :=
    { toFun := fun n => Multiplicative.ofAdd (fr.c n)
      map_one' := by
        show Multiplicative.ofAdd (fr.c 1) = 1
        rw [fr.c_one]
        rfl
      map_mul' := fun n n' => by
        show Multiplicative.ofAdd (fr.c ((n : G) * n')) = _
        rw [fr.c_mul n.2.1 n'.2.1, ofAdd_add] }
  have hker : φ.ker = Z.subgroupOf (V ⊓ W) := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (fr.c n) = 1 ↔ (n : G) ∈ Z
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
    exact fr.c_eq_zero_iff n.2
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Z_le_N).toEquiv, h.card_N] at h1
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have h2 : Nat.card φ.range = 2 ^ e := by
    have : Nat.card ↥Z * Nat.card φ.range = Nat.card ↥Z * 2 ^ e := by rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hZpos this
  have h3 : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [h2, Nat.card_congr Multiplicative.toAdd, h.card_F]
  obtain ⟨n, hn⟩ := (MonoidHom.range_eq_top.1 h3) (Multiplicative.ofAdd r)
  exact ⟨n, n.2, Multiplicative.ofAdd.injective hn⟩

theorem mem_N_iff {v : G} (hv : v ∈ V) : v ∈ V ⊓ W ↔ det2 (D.κ fr.n₀) (D.κ v) = 0 := by
  refine ⟨fun hvN => h.det2_κ_N D fr.hn₀ hvN, fun h0 => ?_⟩
  obtain ⟨n, hn, hnc⟩ := fr.c_surj (fr.c v)
  have h1 : D.κ v = D.κ n := by
    have e1 := eq_det2_smul fr.hdet (D.κ v)
    rw [h0, zero_smul, add_zero] at e1
    rw [e1, fr.κ_eq_c hn, hnc]
    rfl
  have h2 := (D.κ_eq_iff hv hn.1).1 h1
  have e2 : v = (v * n⁻¹) * n := by group
  rw [e2]
  exact mul_mem (h.Z_le_N h2) hn

theorem c_inj_of_inf {n n' : G} (hn : n ∈ V ⊓ W) (hn' : n' ∈ V ⊓ W) (hnn : fr.c n = fr.c n') :
    n * n'⁻¹ ∈ Z := by
  refine (D.κ_eq_iff hn.1 hn'.1).1 ?_
  rw [fr.κ_eq_c hn, fr.κ_eq_c hn', hnn]

theorem ρ_x₀ {j : G} (hj : j ∈ V ⊔ W) :
    (D.ρ j : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ fr.n₀ = D.κ fr.n₀ :=
  h.ρ_fix_N D hj fr.hn₀

theorem ρ_mulVec {j : G} (hj : j ∈ V ⊔ W) (u : Fin 2 → GaloisField 2 e) :
    (D.ρ j : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ u =
      u + (det2 (D.κ fr.n₀) u * fr.b j) • D.κ fr.n₀ := by
  have hjL := h.J_le_L hj
  obtain ⟨d, hd⟩ : ∃ d : GaloisField 2 e,
      (D.ρ j : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ = fr.y₀ + d • D.κ fr.n₀ := by
    set v := D.sec fr.y₀ with hv
    have hvV : v ∈ V := D.sec_mem _
    have hc : ⁅j, v⁆ ∈ V ⊓ W :=
      h.jst.commutator_le (Subgroup.commutator_mem_commutator hj (Subgroup.mem_sup_left hvV))
    obtain ⟨d, hd⟩ : ∃ d : GaloisField 2 e, D.κ ⁅j, v⁆ = d • D.κ fr.n₀ := ⟨_, fr.κ_eq_c hc⟩
    refine ⟨d, ?_⟩
    have e1 : ⁅j, v⁆ = (j * v * j⁻¹) * v⁻¹ := by simp [commutatorElement_def]
    rw [e1, D.κ_mul _ (D.norm j hjL v hvV) _ (inv_mem hvV), D.κ_inv hvV,
      D.conj j hjL v hvV, D.κ_sec] at hd
    rw [← hd]
    abel
  have hb : fr.b j = d := by
    rw [b, hd, det2_add_left, det2_self, zero_add, det2_smul_left, fr.hdet, mul_one]
  have key : ∀ α β : GaloisField 2 e,
      (D.ρ j : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ (α • D.κ fr.n₀ + β • fr.y₀) =
        (α • D.κ fr.n₀ + β • fr.y₀) + (β * d) • D.κ fr.n₀ := by
    intro α β
    rw [mulVec_add, mulVec_smul, mulVec_smul, fr.ρ_x₀ hj, hd]
    module
  have h1 := key (det2 u fr.y₀) (det2 (D.κ fr.n₀) u)
  rw [← eq_det2_smul fr.hdet u] at h1
  rw [h1, hb]

theorem b_mul {j j' : G} (hj : j ∈ V ⊔ W) (hj' : j' ∈ V ⊔ W) :
    fr.b (j * j') = fr.b j + fr.b j' := by
  have h1 := fr.ρ_mulVec hj ((D.ρ j' : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀)
  rw [b, D.ρ_mulVec_mul (h.J_le_L hj) (h.J_le_L hj'), h1, fr.ρ_mulVec hj' fr.y₀]
  rw [b, b, fr.ρ_mulVec hj fr.y₀, fr.ρ_mulVec hj' fr.y₀]
  simp only [det2_add_left, det2_add_right, det2_smul_left, det2_smul_right, det2_self, fr.hdet]
  ring

theorem b_of_mem_V {v : G} (hv : v ∈ V) : fr.b v = 0 := by
  rw [b, D.ρ_mulVec_of_mem (h.V_le_L hv) hv, det2_self]

theorem mem_V_iff_b {j : G} (hj : j ∈ V ⊔ W) : j ∈ V ↔ fr.b j = 0 := by
  refine ⟨fr.b_of_mem_V, fun hb0 => ?_⟩
  refine (D.ρ_eq_one j (h.J_le_L hj)).1 ?_
  apply Subtype.ext
  ext i k
  have := congrFun (fr.ρ_mulVec hj (Pi.single k 1)) i
  rw [hb0, mul_zero, zero_smul, add_zero, mulVec_single_one] at this
  simpa [Pi.single_apply, eq_comm, Matrix.one_apply] using this

theorem c_comm {v w : G} (hv : v ∈ V) (hw : w ∈ W) :
    fr.c ⁅v, w⁆ = det2 (D.κ fr.n₀) (D.κ v) * fr.b w := by
  have e1 : ⁅v, w⁆ = v * (w * v⁻¹ * w⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [c, e1, D.κ_comm hv (h.W_le_L hw), fr.ρ_mulVec (Subgroup.mem_sup_right hw)]
  simp only [sub_add_cancel_left, det2_smul_left, fr.hdet, mul_one, CharTwo.neg_eq]

theorem a_vw {v w : G} (hv : v ∈ V) (hw : w ∈ W) : fr.a (v * w) = det2 (D.κ fr.n₀) (D.κ v) := by
  have hww : w * fr.w₁ = fr.w₁ * w := (h.jst.abelian_V₂ w hw fr.w₁ fr.hw₁).eq
  have e1 : ⁅v * w, fr.w₁⁆ = ⁅v, fr.w₁⁆ := by
    simp only [commutatorElement_def]
    calc v * w * fr.w₁ * (v * w)⁻¹ * fr.w₁⁻¹ = v * (w * fr.w₁) * w⁻¹ * v⁻¹ * fr.w₁⁻¹ := by group
      _ = v * (fr.w₁ * w) * w⁻¹ * v⁻¹ * fr.w₁⁻¹ := by rw [hww]
      _ = v * fr.w₁ * v⁻¹ * fr.w₁⁻¹ := by group
  have hb1 : fr.b fr.w₁ = 1 := fr.hb
  rw [a, e1, fr.c_comm hv fr.hw₁, hb1, mul_one]

theorem a_mul {x y : G} (hx : x ∈ V ⊔ W) (hy : y ∈ V ⊔ W) : fr.a (x * y) = fr.a x + fr.a y := by
  obtain ⟨v, hv, w, hw, rfl⟩ := (h.jst.mem_sup_iff).1 hx
  obtain ⟨v', hv', w', hw', rfl⟩ := (h.jst.mem_sup_iff).1 hy
  have hwv : w * v' * w⁻¹ ∈ V := h.jst.conj_V w (Subgroup.mem_sup_right hw) v' hv'
  have e1 : v * w * (v' * w') = (v * (w * v' * w⁻¹)) * (w * w') := by group
  rw [e1, fr.a_vw (mul_mem hv hwv) (mul_mem hw hw'), fr.a_vw hv hw, fr.a_vw hv' hw',
    D.κ_mul _ hv _ hwv, det2_add_right, D.conj w (h.W_le_L hw) v' hv',
    fr.ρ_mulVec (Subgroup.mem_sup_right hw), det2_add_right, det2_smul_right, det2_self,
    mul_zero, add_zero]

theorem mem_W_iff_a {x : G} (hx : x ∈ V ⊔ W) : x ∈ W ↔ fr.a x = 0 := by
  obtain ⟨v, hv, w, hw, rfl⟩ := (h.jst.mem_sup_iff).1 hx
  rw [fr.a_vw hv hw, ← fr.mem_N_iff hv]
  constructor
  · intro hvw
    have hvW : v ∈ W := by simpa using mul_mem hvw (inv_mem hw)
    exact ⟨hv, hvW⟩
  · intro hvN
    exact mul_mem hvN.2 hw

theorem b_vw {v w : G} (hv : v ∈ V) (hw : w ∈ W) : fr.b (v * w) = fr.b w := by
  rw [fr.b_mul (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hw), fr.b_of_mem_V hv, zero_add]

theorem surj_ab (p q : GaloisField 2 e) : ∃ x ∈ V ⊔ W, fr.a x = p ∧ fr.b x = q := by
  obtain ⟨w, hw, hwq⟩ : ∃ w ∈ W, fr.b w = q := by
    obtain ⟨M, hM⟩ := exists_transvection (D.κ fr.n₀) q
    obtain ⟨l, hl, hlM⟩ := D.ρ_surj M
    have hlM' : (D.ρ l : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) = M := by rw [hlM]
    have hlJ : l ∈ V ⊔ W := by
      rw [h.mem_J_iff D fr.hn₀ fr.hn₀Z hl, hlM', hM, det2_self, zero_mul, zero_smul, add_zero]
    obtain ⟨v, hv, w, hw, rfl⟩ := (h.jst.mem_sup_iff).1 hlJ
    refine ⟨w, hw, ?_⟩
    rw [← fr.b_vw hv hw, b, hlM', hM, det2_add_left, det2_self, zero_add, det2_smul_left,
      fr.hdet, mul_one, one_mul]
  obtain ⟨v, hv, hvp⟩ := D.κ_surj (p • fr.y₀)
  refine ⟨v * w, mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hw), ?_, ?_⟩
  · rw [fr.a_vw hv hw, hvp, det2_smul_right, fr.hdet, mul_one]
  · rw [fr.b_vw hv hw, hwq]

theorem det2_comb (α β γ δ : GaloisField 2 e) (x y : Fin 2 → GaloisField 2 e) :
    det2 (α • x + β • y) (γ • x + δ • y) = (α * δ - β * γ) * det2 x y := by
  simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem torus {t : GaloisField 2 e} (ht : t ≠ 0) :
    ∃ x ∈ L, (∀ j ∈ V ⊔ W, x * j * x⁻¹ ∈ V ⊔ W) ∧ (∀ w ∈ W, x * w * x⁻¹ ∈ W) ∧
      (∀ j ∈ V ⊔ W, fr.a (x * j * x⁻¹) = t⁻¹ * fr.a j ∧ fr.b (x * j * x⁻¹) = t ^ 2 * fr.b j) ∧
      ∀ n ∈ V ⊓ W, x * n * x⁻¹ ∈ V ⊓ W ∧ fr.c (x * n * x⁻¹) = t * fr.c n := by
  have hdet0 : det2 (D.κ fr.n₀) fr.y₀ = 1 := fr.hdet
  let M : Matrix (Fin 2) (Fin 2) (GaloisField 2 e) := Matrix.of fun i k =>
    (t * det2 (Pi.single k 1) fr.y₀) * D.κ fr.n₀ i +
      (t⁻¹ * det2 (D.κ fr.n₀) (Pi.single k 1)) * fr.y₀ i
  have hM : ∀ u, M *ᵥ u = (t * det2 u fr.y₀) • D.κ fr.n₀ +
      (t⁻¹ * det2 (D.κ fr.n₀) u) • fr.y₀ := by
    intro u
    ext i
    fin_cases i <;> simp [M, mulVec, dotProduct, Fin.sum_univ_two, det2] <;> ring
  have hdet : M.det = 1 := by
    rw [L3Side.Frame.det_eq_det2_cols, hM, hM, det2_comb, hdet0, mul_one]
    have key : det2 (Pi.single 0 1) fr.y₀ * det2 (D.κ fr.n₀) (Pi.single 1 1) -
        det2 (D.κ fr.n₀) (Pi.single 0 1) * det2 (Pi.single 1 1) fr.y₀ =
          det2 (D.κ fr.n₀) fr.y₀ := by
      simp [det2]; ring
    calc t * det2 (Pi.single 0 1) fr.y₀ * (t⁻¹ * det2 (D.κ fr.n₀) (Pi.single 1 1)) -
          t⁻¹ * det2 (D.κ fr.n₀) (Pi.single 0 1) * (t * det2 (Pi.single 1 1) fr.y₀)
        = (t * t⁻¹) * (det2 (Pi.single 0 1) fr.y₀ * det2 (D.κ fr.n₀) (Pi.single 1 1) -
          det2 (D.κ fr.n₀) (Pi.single 0 1) * det2 (Pi.single 1 1) fr.y₀) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ ht, one_mul, key, hdet0]
  obtain ⟨x, hx, hxM⟩ := D.ρ_surj ⟨M, hdet⟩
  have hxM' : (D.ρ x : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) = M := by rw [hxM]
  have hMx₀ : M *ᵥ D.κ fr.n₀ = t • D.κ fr.n₀ := by
    rw [hM, det2_self, mul_zero, zero_smul, add_zero, hdet0, mul_one]
  have hMy : M *ᵥ fr.y₀ = t⁻¹ • fr.y₀ := by
    rw [hM, det2_self, mul_zero, zero_smul, zero_add, hdet0, mul_one]
  have hMy₀ : M *ᵥ (t • fr.y₀) = fr.y₀ := by
    rw [mulVec_smul, hMy, smul_smul, mul_inv_cancel₀ ht, one_smul]
  have hMx₀' : M *ᵥ (t⁻¹ • D.κ fr.n₀) = D.κ fr.n₀ := by
    rw [mulVec_smul, hMx₀, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hxi₀ : (D.ρ x⁻¹ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ fr.n₀ =
      t⁻¹ • D.κ fr.n₀ := by
    have h1 : (D.ρ x⁻¹ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ
        (M *ᵥ (t⁻¹ • D.κ fr.n₀)) =
        (D.ρ x⁻¹ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ fr.n₀ := by rw [hMx₀']
    rw [← hxM', ← D.ρ_mulVec_mul (inv_mem hx) hx, inv_mul_cancel,
      D.ρ_mulVec_of_mem (Subgroup.one_mem _) (Subgroup.one_mem _)] at h1
    exact h1.symm
  have hxi : (D.ρ x⁻¹ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ = t • fr.y₀ := by
    have h1 : (D.ρ x⁻¹ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ (M *ᵥ (t • fr.y₀)) =
        (D.ρ x⁻¹ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ := by rw [hMy₀]
    rw [← hxM', ← D.ρ_mulVec_mul (inv_mem hx) hx, inv_mul_cancel,
      D.ρ_mulVec_of_mem (Subgroup.one_mem _) (Subgroup.one_mem _)] at h1
    exact h1.symm
  have hN : ∀ n ∈ V ⊓ W, x * n * x⁻¹ ∈ V ⊓ W ∧ fr.c (x * n * x⁻¹) = t * fr.c n := by
    intro n hn
    have hκ : D.κ (x * n * x⁻¹) = (t * fr.c n) • D.κ fr.n₀ := by
      rw [D.conj x hx n hn.1, hxM', fr.κ_eq_c hn, mulVec_smul, hMx₀, smul_smul, mul_comm]
    have hmem : x * n * x⁻¹ ∈ V ⊓ W := by
      rw [fr.mem_N_iff (D.norm x hx n hn.1), hκ, det2_smul_right, det2_self, mul_zero]
    refine ⟨hmem, ?_⟩
    rw [c, hκ, det2_smul_left, hdet0, mul_one]
  have hJ : ∀ j ∈ V ⊔ W, x * j * x⁻¹ ∈ V ⊔ W := by
    intro j hj
    have hxj : x * j * x⁻¹ ∈ L := mul_mem (mul_mem hx (h.J_le_L hj)) (inv_mem hx)
    rw [h.mem_J_iff D fr.hn₀ fr.hn₀Z hxj, D.ρ_mulVec_mul (mul_mem hx (h.J_le_L hj)) (inv_mem hx),
      hxi₀, D.ρ_mulVec_mul hx (h.J_le_L hj), mulVec_smul, fr.ρ_x₀ hj, mulVec_smul, hxM', hMx₀,
      smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hW : ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
    have hle : cj x W ≤ V ⊔ W := by
      intro y hy
      rw [mem_cj_iff] at hy
      have := hJ _ (Subgroup.mem_sup_right hy)
      simpa [mul_assoc] using this
    have hsq : ∀ y ∈ cj x W, y * y = 1 := fun y hy => by
      rw [mem_cj_iff] at hy
      have h1 := h.jst.sq_V₂ _ hy
      calc y * y = x * (x⁻¹ * y * x * (x⁻¹ * y * x)) * x⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hcard : Nat.card (cj x W) = Nat.card V := by
      rw [card_cj, h.jst.card_V₂_eq]
    rcases h.jst.mem_of_card hle hsq hcard with hV | hW'
    · exfalso
      have hxV : cj x V = V := cj_eq_of_mem_normalizer_set (D.le_normalizer hx)
      have := cj_injective (hV.trans hxV.symm)
      exact h.jst.not_le_V (this ▸ le_rfl)
    · intro w hw
      rw [← hW']
      exact mul_mem_cj x hw
  refine ⟨x, hx, hJ, hW, fun j hj => ?_, hN⟩
  obtain ⟨v, hv, w, hw, rfl⟩ := (h.jst.mem_sup_iff).1 hj
  have hxv : x * v * x⁻¹ ∈ V := D.norm x hx v hv
  have hxw : x * w * x⁻¹ ∈ W := hW w hw
  have e1 : x * (v * w) * x⁻¹ = (x * v * x⁻¹) * (x * w * x⁻¹) := by group
  refine ⟨?_, ?_⟩
  · rw [e1, fr.a_vw hxv hxw, fr.a_vw hv hw, D.conj x hx v hv, hxM', hM, det2_add_right,
      det2_smul_right, det2_self, mul_zero, zero_add, det2_smul_right, hdet0, mul_one]
  · have hj' : v * w ∈ V ⊔ W := hj
    have hb1 : (D.ρ (v * w) : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ =
        fr.y₀ + fr.b (v * w) • D.κ fr.n₀ := by
      rw [fr.ρ_mulVec hj', hdet0, one_mul]
    have hcomp : (D.ρ (x * (v * w) * x⁻¹) : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ =
        fr.y₀ + (t ^ 2 * fr.b (v * w)) • D.κ fr.n₀ := by
      rw [D.ρ_mulVec_mul (mul_mem hx (h.J_le_L hj')) (inv_mem hx),
        D.ρ_mulVec_mul hx (h.J_le_L hj'), hxi, mulVec_smul, hb1, hxM', mulVec_smul, mulVec_add,
        mulVec_smul, hMy, hMx₀, smul_add, smul_smul, mul_inv_cancel₀ ht, one_smul, smul_smul,
        smul_smul]
      congr 2
      ring
    rw [b, hcomp, det2_add_left, det2_self, zero_add, det2_smul_left, hdet0, mul_one]

end Frame

end S4Side

end CFSG.CGT.PushingUpLit.A78S4
