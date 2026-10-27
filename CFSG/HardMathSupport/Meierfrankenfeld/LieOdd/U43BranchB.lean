module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Interfaces
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.FixedFreeThree
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.CenterThree
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.RouteAAut
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.CenterFPF
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.PUMul
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem four_pow_eq_four {k : ℕ} (h1 : 4 ^ k ≠ 1) (h4 : 4 ^ k ≤ 4) : 4 ^ k = 4 := by
  have hk1 : k ≠ 0 := by rintro rfl; simp at h1
  have hk2 : k < 2 := by
    by_contra hk
    have : 4 ^ 2 ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at this
    omega
  obtain rfl : k = 1 := by omega
  norm_num

theorem four_pow_eq_sixteen {k : ℕ} (h16 : 16 ≤ 4 ^ k) (h32 : 4 ^ k ≤ 32) : 4 ^ k = 16 := by
  have hk2 : 2 ≤ k := by
    by_contra hk
    have : 4 ^ k ≤ 4 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at this
    omega
  have hk3 : k < 3 := by
    by_contra hk
    have : 4 ^ 3 ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at this
    omega
  obtain rfl : k = 2 := by omega
  norm_num

theorem exists_mem_ne_one_ne {G : Type} [Group G] (H : Subgroup G) (h : 2 < Nat.card H)
    (x : G) : ∃ y ∈ H, y ≠ 1 ∧ y ≠ x := by
  by_contra hcon
  push Not at hcon
  have hsub : (H : Set G) ⊆ {1, x} := by
    intro y hy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · exact Or.inr (hcon y hy hy1)
  have h1 : Nat.card H ≤ Nat.card ({1, x} : Set G) := Nat.card_mono (Set.toFinite _) hsub
  have h2 : ({1, x} : Set G).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : G) {x}
    rw [Set.ncard_singleton] at this
    exact this
  rw [Nat.card_coe_set_eq] at h1
  omega

theorem eq_of_le_of_index_eq {G : Type} [Group G] [Finite G] {H K : Subgroup G} (hHK : H ≤ K)
    (hidx : H.index = K.index) : H = K := by
  apply Subgroup.eq_of_le_of_card_ge hHK
  have h1 := Subgroup.card_mul_index H
  have h2 := Subgroup.card_mul_index K
  rw [hidx] at h1
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact (Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)).le

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {S : Type} [Group S]

omit [Finite W] in
theorem index_fixV_zpowers_ne_one {b : MulAut W} (hb1 : b ≠ 1) :
    (fixV (Subgroup.zpowers b)).index ≠ 1 := by
  intro h1
  apply hb1
  have htop := Subgroup.index_eq_one.1 h1
  ext w
  have : w ∈ fixV (Subgroup.zpowers b) := by rw [htop]; trivial
  exact (mem_fixV.1 this) b (Subgroup.mem_zpowers b)

theorem orderOf_mk_eq_two (hodd : Odd (Nat.card (Subgroup.center ↥L))) (e : CQ L ≃* S)
    {y : ↥L} (hy2 : y * y = 1) (hy1 : y ≠ 1) : orderOf (e (QuotientGroup.mk y)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [sq, ← map_mul, ← QuotientGroup.mk_mul, hy2, QuotientGroup.mk_one, map_one]
  · intro h
    apply hy1
    have h1 : (QuotientGroup.mk y : CQ L) = 1 := e.injective (by rw [h, map_one])
    rw [QuotientGroup.eq_one_iff] at h1
    exact Proving.eq_one_of_mem_center_of_mul_self hodd h1 hy2

theorem mul_comm_of_mk_commute (hodd : Odd (Nat.card (Subgroup.center ↥L))) {a c : ↥L}
    (ha : a * a = 1)
    (h : (QuotientGroup.mk c : CQ L) * QuotientGroup.mk a =
      QuotientGroup.mk a * QuotientGroup.mk c) :
    c * a = a * c := by
  have h1 : (QuotientGroup.mk (c * a * c⁻¹) : CQ L) = QuotientGroup.mk a := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, mul_inv_cancel_right]
  rw [QuotientGroup.eq] at h1
  obtain ⟨ζ, hζZ, hζ⟩ : ∃ ζ ∈ Subgroup.center ↥L, a = c * a * c⁻¹ * ζ :=
    ⟨_, h1, by group⟩
  have hcomm : c * a * c⁻¹ * ζ = ζ * (c * a * c⁻¹) :=
    Subgroup.mem_center_iff.1 hζZ (c * a * c⁻¹)
  have hζ2 : ζ * ζ = 1 := by
    have h2 : a * a = (c * a * c⁻¹) * (c * a * c⁻¹) * (ζ * ζ) := by
      calc a * a = (c * a * c⁻¹ * ζ) * (c * a * c⁻¹ * ζ) := by rw [← hζ]
        _ = (c * a * c⁻¹) * (ζ * (c * a * c⁻¹)) * ζ := by group
        _ = (c * a * c⁻¹) * ((c * a * c⁻¹) * ζ) * ζ := by rw [← hcomm]
        _ = (c * a * c⁻¹) * (c * a * c⁻¹) * (ζ * ζ) := by group
    have h3 : (c * a * c⁻¹) * (c * a * c⁻¹) = 1 := by
      calc (c * a * c⁻¹) * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
        _ = 1 := by rw [ha]; group
    rw [ha, h3, one_mul] at h2
    exact h2.symm
  have hζ1 : ζ = 1 := Proving.eq_one_of_mem_center_of_mul_self hodd hζZ hζ2
  rw [hζ1, mul_one] at hζ
  calc c * a = (c * a * c⁻¹) * c := by group
    _ = a * c := by rw [← hζ]

theorem mul_comm_of_psiAut_fixed (hirr : IsIrrOn L)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (e : CQ L ≃* S) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1)
    (hb4 : (fixV (Subgroup.zpowers b)).index = 4) (hW12 : 2 ^ 12 ≤ Nat.card W) (c : ↥L)
    (hc : psiAut L e hb (e (QuotientGroup.mk c)) = e (QuotientGroup.mk c)) :
    b * (c : MulAut W) = (c : MulAut W) * b := by
  rw [psiAut_mk] at hc
  have h1 : (QuotientGroup.mk c : CQ L) = QuotientGroup.mk (conjAut L hb c) := e.injective hc.symm
  rw [QuotientGroup.eq] at h1
  obtain ⟨ζ, hζZ, hζ⟩ : ∃ ζ ∈ Subgroup.center ↥L, conjAut L hb c = c * ζ := ⟨_, h1, by group⟩
  have hbc : b * (c : MulAut W) * b⁻¹ = (c : MulAut W) * (ζ : MulAut W) := by
    have := congrArg Subtype.val hζ
    rwa [coe_conjAut, Subgroup.coe_mul] at this
  have hinv : b * (ζ : MulAut W) * b⁻¹ = (ζ : MulAut W)⁻¹ := by
    have h2 : (c : MulAut W) = (c : MulAut W) * (ζ : MulAut W) * (b * (ζ : MulAut W) * b⁻¹) := by
      calc (c : MulAut W) = (b * b) * (c : MulAut W) * (b * b)⁻¹ := by rw [hb2]; group
        _ = b * (b * (c : MulAut W) * b⁻¹) * b⁻¹ := by group
        _ = b * ((c : MulAut W) * (ζ : MulAut W)) * b⁻¹ := by rw [hbc]
        _ = (b * (c : MulAut W) * b⁻¹) * (b * (ζ : MulAut W) * b⁻¹) := by group
        _ = (c : MulAut W) * (ζ : MulAut W) * (b * (ζ : MulAut W) * b⁻¹) := by rw [hbc]
    have h3 : (ζ : MulAut W) * (b * (ζ : MulAut W) * b⁻¹) = 1 := by
      calc (ζ : MulAut W) * (b * (ζ : MulAut W) * b⁻¹) =
            (c : MulAut W)⁻¹ * ((c : MulAut W) * (ζ : MulAut W) * (b * (ζ : MulAut W) * b⁻¹)) := by
              group
        _ = (c : MulAut W)⁻¹ * (c : MulAut W) := by rw [← h2]
        _ = 1 := inv_mul_cancel _
    exact eq_inv_of_mul_eq_one_right h3
  by_contra hne
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    apply hne
    rw [Subgroup.coe_one, mul_one] at hbc
    calc b * (c : MulAut W) = (b * (c : MulAut W) * b⁻¹) * b := by group
      _ = (c : MulAut W) * b := by rw [hbc]
  have hζ2 : ζ * ζ ≠ 1 := fun h => hζ1 (Proving.eq_one_of_mem_center_of_mul_self hodd hζZ h)
  have hcomm : ∀ l ∈ L, ((ζ * ζ : ↥L) : MulAut W) * l = l * ((ζ * ζ : ↥L) : MulAut W) := by
    intro l hl
    have := Subgroup.mem_center_iff.1 ((Subgroup.center ↥L).mul_mem hζZ hζZ) ⟨l, hl⟩
    exact (congrArg Subtype.val this).symm
  have hne1 : ((ζ * ζ : ↥L) : MulAut W) ≠ 1 := fun h => hζ2 (Subtype.ext h)
  have hfpf := Proving.fpf_of_mem_center_of_isIrrOn hirr hcomm hne1
  have hsq := Proving.card_fixV_sq_le_of_inverts_sq_fpf (ζ := (ζ : MulAut W)) (t := b)
    (fun w hw => hfpf w (by rw [Subgroup.coe_mul, MulAut.mul_apply]; exact hw)) hinv
  have hmul := Subgroup.card_mul_index (fixV (Subgroup.zpowers b))
  rw [hb4] at hmul
  have hpos : 0 < Nat.card (fixV (Subgroup.zpowers b)) := Nat.card_pos
  have hC : Nat.card (fixV (Subgroup.zpowers b)) ≤ 4 :=
    Nat.le_of_mul_le_mul_left (by rw [hmul]; exact hsq) hpos
  have h12 : (4096 : ℕ) ≤ Nat.card W := (by norm_num : (4096 : ℕ) = 2 ^ 12).trans_le hW12
  omega

theorem sixteen_le_index_of_mem (hW : ∀ w : W, w * w = 1)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (e : CQ L ≃* S) (hF1 : U43F1 S)
    {z : MulAut W} (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1)
    (hzL : ∀ l ∈ L, l * z = z * l) {a : MulAut W} (haL : a ∈ L) (ha1 : a ≠ 1)
    (ha2 : a * a = 1) : 16 ≤ (fixV (Subgroup.zpowers a)).index := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have ha'2 : (⟨a, haL⟩ : ↥L) * ⟨a, haL⟩ = 1 := Subtype.ext ha2
  have ha'1 : (⟨a, haL⟩ : ↥L) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := hF1 _ (orderOf_mk_eq_two hodd e ha'2 ha'1)
  obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective (e.symm g)
  have hgg : e (QuotientGroup.mk g') = g := by rw [hg']; exact e.apply_symm_apply g
  subst hgg
  refine sixteen_le_index_of_conj_order hW hz3 hfpf hzL haL ha1 ha2 ⟨g', g'.2, ?_⟩
  set Y : ↥L := ⟨a, haL⟩ * (g' * ⟨a, haL⟩ * g'⁻¹) with hY
  have hYS : e (QuotientGroup.mk ⟨a, haL⟩) * (e (QuotientGroup.mk g') *
      e (QuotientGroup.mk ⟨a, haL⟩) * (e (QuotientGroup.mk g'))⁻¹) =
      e (QuotientGroup.mk Y) := by
    simp only [hY, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
  rw [hYS] at hg
  have hdvd : orderOf (e (QuotientGroup.mk Y)) ∣ orderOf Y :=
    orderOf_map_dvd (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))) Y
  have hcoe : orderOf Y = orderOf (a * ((g' : MulAut W) * a * (g' : MulAut W)⁻¹)) := by
    rw [← Subgroup.orderOf_coe]
    rfl
  rw [hcoe] at hdvd
  exact lt_of_lt_of_le hg (Nat.le_of_dvd (orderOf_pos _) hdvd)

theorem isSmallAut_psiAut (hW : ∀ w : W, w * w = 1) (e : CQ L ≃* S) {z : MulAut W}
    (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) (hzL : ∀ l ∈ L, l * z = z * l)
    {b : MulAut W} (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hbz : b * z = z * b)
    (hb2 : b * b = 1) (hb4 : (fixV (Subgroup.zpowers b)).index = 4) :
    IsSmallAut (psiAut L e hb) := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  intro g
  obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective (e.symm g)
  have hgg : e (QuotientGroup.mk g') = g := by rw [hg']; exact e.apply_symm_apply g
  subst hgg
  set N := Subgroup.normalizer (L : Set (MulAut W)) with hN
  let Φ : ↥N →* MulAut S := psiHom L e (le_refl N)
  have hg'N : (g' : MulAut W) ∈ N := Subgroup.le_normalizer g'.2
  have hconj : MulAut.conj (e (QuotientGroup.mk g')) = Φ ⟨g', hg'N⟩ := by
    ext x
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm x)
    have hx : x = e (QuotientGroup.mk y) := by rw [hy]; simp
    rw [hx, FFToolkit.psiHom_apply, psiAut_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
  have hψ : psiAut L e hb = Φ ⟨b, hb⟩ := rfl
  rw [hψ, hconj]
  have hmap : Φ ⟨b, hb⟩ * (Φ ⟨g', hg'N⟩ * Φ ⟨b, hb⟩ * (Φ ⟨g', hg'N⟩)⁻¹) =
      Φ (⟨b, hb⟩ * (⟨g', hg'N⟩ * ⟨b, hb⟩ * ⟨g', hg'N⟩⁻¹)) := by
    rw [map_mul, map_mul, map_mul, map_inv]
  rw [hmap]
  refine (Nat.le_of_dvd (orderOf_pos _) (orderOf_map_dvd Φ _)).trans ?_
  rw [← Subgroup.orderOf_coe]
  have hgz : Commute (g' : MulAut W) z := hzL g' g'.2
  have hcz : ((g' : MulAut W) * b * (g' : MulAut W)⁻¹) * z =
      z * ((g' : MulAut W) * b * (g' : MulAut W)⁻¹) :=
    ((hgz.mul_left (show Commute b z from hbz)).mul_left hgz.inv_left)
  have hc2 : ((g' : MulAut W) * b * (g' : MulAut W)⁻¹) *
      ((g' : MulAut W) * b * (g' : MulAut W)⁻¹) = 1 := by
    calc ((g' : MulAut W) * b * (g' : MulAut W)⁻¹) * ((g' : MulAut W) * b * (g' : MulAut W)⁻¹) =
          (g' : MulAut W) * (b * b) * (g' : MulAut W)⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  have hc4 : (fixV (Subgroup.zpowers ((g' : MulAut W) * b * (g' : MulAut W)⁻¹))).index = 4 := by
    rw [FFToolkit.index_fixV_conj]
    exact hb4
  exact orderOf_mul_le_five_of_index_four hW hz3 hfpf hbz hcz hb2 hc2 hb4 hc4

theorem weight_lt_of_conj_ne (hW : ∀ w : W, w * w = 1) (hirr : IsIrrOn L)
    (h37 : 3 ^ 7 ∣ Nat.card L) {E : Subgroup (MulAut W)}
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hel : IsElemAbelian2 E)
    (hE5 : Nat.card E ≤ 2 ^ 5) {z : MulAut W} (hzLmem : z ∈ L) (hz3 : z ^ 3 = 1)
    (hzL : ∀ l ∈ L, l * z = z * l) {t : MulAut W} (htE : t ∈ E) (htz : t * z * t⁻¹ ≠ z) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have htN := hEN htE
  have ht2 : t * t = 1 := by have := hel.2 t htE; rwa [sq] at this
  obtain ⟨z', hz'⟩ : ∃ z', t * z * t⁻¹ = z' := ⟨_, rfl⟩
  rw [hz'] at htz
  have hz'L : ∀ l ∈ L, l * z' = z' * l := by
    intro l hl
    have hl' : t⁻¹ * l * t ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem htN) l).1 hl
      simpa using this
    have h1 := hzL _ hl'
    calc l * z' = t * ((t⁻¹ * l * t) * z) * t⁻¹ := by rw [← hz']; group
      _ = t * (z * (t⁻¹ * l * t)) * t⁻¹ := by rw [h1]
      _ = z' * l := by rw [← hz']; group
  have hz'mem : z' ∈ L := hz' ▸ (Subgroup.mem_normalizer_iff.1 htN z).1 hzLmem
  have hzz' : Commute z z' := (hzL z' hz'mem).symm
  have hz'3 : z' ^ 3 = 1 := by rw [← hz', conj_pow, hz3, mul_one, mul_inv_cancel]
  have hz'z : t * z' * t⁻¹ = z := by
    rw [← hz']
    calc t * (t * z * t⁻¹) * t⁻¹ = (t * t) * z * (t * t)⁻¹ := by group
      _ = z := by rw [ht2]; group
  obtain ⟨ζ, hζ⟩ : ∃ ζ, z * z'⁻¹ = ζ := ⟨_, rfl⟩
  have hζ3 : ζ ^ 3 = 1 := by
    rw [← hζ, (hzz'.inv_right).mul_pow, inv_pow, hz'3, inv_one, hz3, one_mul]
  have hζ1 : ζ ≠ 1 := by
    intro h
    apply htz
    rw [← hζ, mul_inv_eq_one] at h
    exact h.symm
  have hζL : ∀ l ∈ L, ζ * l = l * ζ := by
    intro l hl
    have h1 := hzL l hl
    have h2 := hz'L l hl
    have h2' : z'⁻¹ * l = l * z'⁻¹ := by
      calc z'⁻¹ * l = z'⁻¹ * (l * z') * z'⁻¹ := by group
        _ = z'⁻¹ * (z' * l) * z'⁻¹ := by rw [h2]
        _ = l * z'⁻¹ := by group
    calc ζ * l = z * (z'⁻¹ * l) := by rw [← hζ, mul_assoc]
      _ = z * (l * z'⁻¹) := by rw [h2']
      _ = (z * l) * z'⁻¹ := by rw [mul_assoc]
      _ = (l * z) * z'⁻¹ := by rw [h1]
      _ = l * ζ := by rw [← hζ, mul_assoc]
  have hζfpf := Proving.fpf_of_mem_center_of_isIrrOn hirr hζL hζ1
  have hinv : t * ζ * t⁻¹ = ζ⁻¹ := by
    calc t * ζ * t⁻¹ = (t * z * t⁻¹) * (t * z' * t⁻¹)⁻¹ := by rw [← hζ]; group
      _ = z' * z⁻¹ := by rw [hz', hz'z]
      _ = ζ⁻¹ := by rw [← hζ, mul_inv_rev, inv_inv]
  exact weight_lt_of_inverts_fpf_of_three_pow_seven_dvd hW h37 hE5 hζ3 hζfpf hinv htE

theorem false_of_inf_eq_bot (hW : ∀ w : W, w * w = 1) (hq : CFSG.IsQuasisimple ↥L)
    (hirr : IsIrrOn L) (e : CQ L ≃* S) (hcent : Subgroup.center S = ⊥)
    (hOut : OutElemIndexLE S 4) (hF1 : U43F1 S) (hF3 : U43F3 S) {z : MulAut W}
    (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) (hzL : ∀ l ∈ L, l * z = z * l)
    (hW12 : 2 ^ 12 ≤ Nat.card W) {E : Subgroup (MulAut W)}
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hE : E ≠ ⊥)
    (hel : IsElemAbelian2 E) (hquad : IsQuadratic E) (hEz : ∀ t ∈ E, t * z = z * t)
    (hle : (fixV E).index ≤ Nat.card E) (hEL : E ⊓ L = ⊥) : False := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hperf : Group.IsPerfect ↥L := hq.1
  have hodd := odd_card_center_of_isIrrOn hW hirr
  have hinner : ∀ g ∈ L, g ≠ 1 → g * g = 1 → 16 ≤ (fixV (Subgroup.zpowers g)).index :=
    fun g hg hg1 hg2 => sixteen_le_index_of_mem hW hodd e hF1 hz3 hfpf hzL hg hg1 hg2
  have hle_of : ∀ b ∈ E, fixV E ≤ fixV (Subgroup.zpowers b) := fun b hb =>
    QuasithinUnique.Setup.X1.fixV_anti ((Subgroup.zpowers_le).2 hb)
  have hmono : ∀ b ∈ E, (fixV (Subgroup.zpowers b)).index ≤ (fixV E).index := fun b hb =>
    Subgroup.index_antitone (hle_of b hb)
  have hOutE := card_le_mul_card_inf_of_outer hW hperf hirr hEN hel e hOut
  have hzpow : ∀ b : MulAut W, b * z = z * b → ∀ x ∈ Subgroup.zpowers b, x * z = z * x := by
    intro b hb x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact (Commute.zpow_left hb n)
  let Φ : ↥E →* MulAut S := psiHom L e hEN
  rw [hEL, Subgroup.card_bot, mul_one] at hOutE
  obtain ⟨k, hk⟩ := index_fixV_eq_four_pow hW hz3 hfpf E hEz
  have hk1 : (fixV E).index ≠ 1 := by
    intro h1
    apply hE
    have htop := Subgroup.index_eq_one.1 h1
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    ext w
    have : w ∈ fixV E := by rw [htop]; trivial
    exact (mem_fixV.1 this) b hb
  have hidx4 : (fixV E).index = 4 := by
    rw [hk] at hk1 hle ⊢
    exact four_pow_eq_four hk1 (hle.trans hOutE)
  have hE4 : Nat.card E = 4 := le_antisymm hOutE (by rw [← hidx4]; exact hle)
  have hb4 : ∀ b ∈ E, b ≠ 1 → (fixV (Subgroup.zpowers b)).index = 4 := by
    intro b hb hb1
    obtain ⟨j, hj⟩ := index_fixV_eq_four_pow hW hz3 hfpf _ (hzpow b (hEz b hb))
    have h1 := index_fixV_zpowers_ne_one hb1
    have h2 := hmono b hb
    rw [hj] at h1 h2 ⊢
    rw [hidx4] at h2
    exact four_pow_eq_four h1 h2
  have hbU : ∀ b ∈ E, b ≠ 1 → fixV (Subgroup.zpowers b) = fixV E := by
    intro b hb hb1
    exact (eq_of_le_of_index_eq (hle_of b hb) (by rw [hidx4, hb4 b hb hb1])).symm
  have hEPU : E ≤ Proving.pUMul (fixV E) := Proving.le_pUMul_fixV hquad
  set E' := Proving.pUMul (fixV E) ⊓ Subgroup.normalizer (L : Set (MulAut W)) with hE'
  have hEE' : E ≤ E' := le_inf hEPU hEN
  have hE'N : E' ≤ Subgroup.normalizer (L : Set (MulAut W)) := inf_le_right
  have hE'el : IsElemAbelian2 E' :=
    ⟨fun a ha b hb => Proving.pUMul_mul_comm (Subgroup.mem_inf.1 ha).1
        (Subgroup.mem_inf.1 hb).1,
      fun a ha => by rw [sq]; exact Proving.pUMul_mul_self hW (Subgroup.mem_inf.1 ha).1⟩
  have hE'L : E' ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgE', hgL⟩ := Subgroup.mem_inf.1 hg
    rw [Subgroup.mem_bot]
    by_contra hg1
    have hgPU := (Subgroup.mem_inf.1 hgE').1
    have h16 := hinner g hgL hg1 (Proving.pUMul_mul_self hW hgPU)
    have hle4 : (fixV (Subgroup.zpowers g)).index ≤ 4 := by
      rw [← hidx4]
      exact Subgroup.index_antitone (Proving.le_fixV_zpowers_of_mem_pUMul hgPU)
    omega
  have hE'card : Nat.card E' ≤ 4 := by
    have := card_le_mul_card_inf_of_outer hW hperf hirr hE'N hE'el e hOut
    rwa [hE'L, Subgroup.card_bot, mul_one] at this
  have hEeq : E = E' := Subgroup.eq_of_le_of_card_ge hEE' (by omega)
  have hΦ2 : ∀ x : ↥E, x ≠ 1 → orderOf (Φ x) = 2 := by
    intro x hx1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime
    · rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hel.2 x x.2)
      rw [this, map_one]
    · exact psiAut_ne_one hW hperf hirr hEN hel e hcent x.2
        (fun h' => hx1 (Subtype.ext h'))
  have hΦout : ∀ x : ↥E, x ≠ 1 → Φ x ∉ (MulAut.conj : S →* MulAut S).range := by
    rintro x hx1 ⟨s, hs⟩
    have hxL : (x : MulAut W) ∈ L := mem_of_psiAut_inner hW hperf hirr hEN hel e x.2 s
      (fun y => by rw [show psiAut L e (hEN x.2) = Φ x from rfl, ← hs, MulAut.conj_apply])
    apply hx1
    have hxEL : (x : MulAut W) ∈ E ⊓ L := Subgroup.mem_inf.2 ⟨x.2, hxL⟩
    rw [hEL] at hxEL
    exact Subtype.ext (Subgroup.mem_bot.1 hxEL)
  have hx2 : ∀ x : ↥E, (x : MulAut W) * x = 1 := fun x => by
    have := hel.2 x x.2
    rwa [sq] at this
  have hsmall : ∀ x : ↥E, x ≠ 1 → IsSmallAut (Φ x) := fun x hx1 =>
    isSmallAut_psiAut hW e hz3 hfpf hzL (hEN x.2) (hEz x x.2) (hx2 x)
      (hb4 x x.2 (fun h => hx1 (Subtype.ext h)))
  have hfix : ∀ x y : ↥E, x ≠ 1 → ∀ c : S, Φ x c = c → Φ y c = c := by
    intro x y hx1 c hc
    have hx1' : (x : MulAut W) ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨c', hc'⟩ := QuotientGroup.mk_surjective (e.symm c)
    have hcc : e (QuotientGroup.mk c') = c := by rw [hc']; exact e.apply_symm_apply c
    subst hcc
    have hxc := mul_comm_of_psiAut_fixed hirr hodd e (hEN x.2) (hx2 x) (hb4 x x.2 hx1') hW12
      c' hc
    have hU' := hbU x x.2 hx1'
    have hcx : Commute (c' : MulAut W) x := hxc.symm
    have hcU : ∀ u ∈ fixV E, (c' : MulAut W) u ∈ fixV E := by
      intro u hu
      rw [← hU'] at hu ⊢
      exact Proving.apply_mem_fixV_zpowers_of_commute hcx hu
    have hcU' : ∀ u ∈ fixV E, (c' : MulAut W)⁻¹ u ∈ fixV E := by
      intro u hu
      rw [← hU'] at hu ⊢
      exact Proving.apply_mem_fixV_zpowers_of_commute hcx.inv_left hu
    have hc'N : (c' : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      Subgroup.le_normalizer c'.2
    have hyE : (c' : MulAut W) * y * (c' : MulAut W)⁻¹ ∈ E := by
      refine hEeq.symm.le (Subgroup.mem_inf.2 ⟨Proving.conj_mem_pUMul hcU hcU' (hEPU y.2), ?_⟩)
      exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hc'N (hEN y.2))
        ((Subgroup.normalizer _).inv_mem hc'N)
    have hcomm : (c' : MulAut W) * y * (c' : MulAut W)⁻¹ * (y : MulAut W)⁻¹ ∈ E ⊓ L := by
      refine Subgroup.mem_inf.2 ⟨E.mul_mem hyE (E.inv_mem y.2), ?_⟩
      have h1 : (y : MulAut W) * (c' : MulAut W)⁻¹ * (y : MulAut W)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (hEN y.2) _).1 (L.inv_mem c'.2)
      have : (c' : MulAut W) * y * (c' : MulAut W)⁻¹ * (y : MulAut W)⁻¹ =
          c' * ((y : MulAut W) * (c' : MulAut W)⁻¹ * (y : MulAut W)⁻¹) := by group
      rw [this]
      exact L.mul_mem c'.2 h1
    rw [hEL, Subgroup.mem_bot] at hcomm
    have hyc : (c' : MulAut W) * y = y * c' := by
      calc (c' : MulAut W) * y =
            ((c' : MulAut W) * y * (c' : MulAut W)⁻¹ * (y : MulAut W)⁻¹) * y * c' := by group
        _ = y * c' := by rw [hcomm, one_mul]
    show psiAut L e (hEN y.2) (e (QuotientGroup.mk c')) = e (QuotientGroup.mk c')
    rw [psiAut_mk]
    congr 2
    exact Subtype.ext (by rw [coe_conjAut, ← hyc, mul_inv_cancel_right])
  obtain ⟨b₁, hb₁E, hb₁1⟩ : ∃ b ∈ E, b ≠ 1 := by
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE
    exact ⟨b, hb, fun h => hb1 (Subtype.ext h)⟩
  obtain ⟨b₂, hb₂E, hb₂1, hb₂b₁⟩ := exists_mem_ne_one_ne E (by omega) b₁
  set x₁ : ↥E := ⟨b₁, hb₁E⟩
  set x₂ : ↥E := ⟨b₂, hb₂E⟩
  have hx₁ : x₁ ≠ 1 := fun h => hb₁1 (congrArg Subtype.val h)
  have hx₂ : x₂ ≠ 1 := fun h => hb₂1 (congrArg Subtype.val h)
  have hx₁₂ : x₁ * x₂ ≠ 1 := by
    intro h
    apply hb₂b₁
    have h' : b₁ * b₂ = 1 := congrArg Subtype.val h
    calc b₂ = b₁⁻¹ := eq_inv_of_mul_eq_one_right h'
      _ = b₁ := inv_eq_of_mul_eq_one_right (hx2 x₁)
  have hcomm12 : Commute (Φ x₁) (Φ x₂) := by
    show Φ x₁ * Φ x₂ = Φ x₂ * Φ x₁
    rw [← map_mul, ← map_mul]
    exact congrArg Φ (Subtype.ext (hel.1 b₁ hb₁E b₂ hb₂E))
  have h3out := hΦout (x₁ * x₂) hx₁₂
  have h3small := hsmall (x₁ * x₂) hx₁₂
  rw [map_mul] at h3out h3small
  refine hF3 (Φ x₁) (Φ x₂) (hΦ2 x₁ hx₁) (hΦ2 x₂ hx₂) hcomm12 (hΦout x₁ hx₁) (hΦout x₂ hx₂)
    h3out (hsmall x₁ hx₁) (hsmall x₂ hx₂) h3small
    (fun c => ⟨hfix x₁ x₂ hx₁ c, hfix x₂ x₁ hx₂ c⟩) (fun c => ⟨fun h => ?_, fun h => ?_⟩)
  · rw [← map_mul]
    exact hfix x₁ (x₁ * x₂) hx₁ c h
  · rw [← map_mul] at h
    exact hfix (x₁ * x₂) x₁ hx₁₂ c h

theorem false_of_inf_ne_bot (hW : ∀ w : W, w * w = 1) (hq : CFSG.IsQuasisimple ↥L)
    (hirr : IsIrrOn L) (e : CQ L ≃* S) (hOut : OutElemIndexLE S 4) (hF1 : U43F1 S)
    (hF2 : U43F2 S) {z : MulAut W} (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1)
    (hzL : ∀ l ∈ L, l * z = z * l) {E : Subgroup (MulAut W)}
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hel : IsElemAbelian2 E)
    (hquad : IsQuadratic E) (hEz : ∀ t ∈ E, t * z = z * t) (hE5 : Nat.card E ≤ 2 ^ 5)
    (hle : (fixV E).index ≤ Nat.card E) (hEL : E ⊓ L ≠ ⊥) : False := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hperf : Group.IsPerfect ↥L := hq.1
  have hodd := odd_card_center_of_isIrrOn hW hirr
  have hinner : ∀ g ∈ L, g ≠ 1 → g * g = 1 → 16 ≤ (fixV (Subgroup.zpowers g)).index :=
    fun g hg hg1 hg2 => sixteen_le_index_of_mem hW hodd e hF1 hz3 hfpf hzL hg hg1 hg2
  have hle_of : ∀ b ∈ E, fixV E ≤ fixV (Subgroup.zpowers b) := fun b hb =>
    QuasithinUnique.Setup.X1.fixV_anti ((Subgroup.zpowers_le).2 hb)
  have hmono : ∀ b ∈ E, (fixV (Subgroup.zpowers b)).index ≤ (fixV E).index := fun b hb =>
    Subgroup.index_antitone (hle_of b hb)
  have hOutE := card_le_mul_card_inf_of_outer hW hperf hirr hEN hel e hOut
  obtain ⟨⟨a, haEL⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEL
  have haE : a ∈ E := (Subgroup.mem_inf.1 haEL).1
  have haL : a ∈ L := (Subgroup.mem_inf.1 haEL).2
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have ha2 : a * a = 1 := by have := hel.2 a haE; rwa [sq] at this
  have h16a := hinner a haL ha1' ha2
  have hmonoa := hmono a haE
  obtain ⟨k, hk⟩ := index_fixV_eq_four_pow hW hz3 hfpf E hEz
  have hidx16 : (fixV E).index = 16 := by
    rw [hk] at hle hmonoa ⊢
    exact four_pow_eq_sixteen (h16a.trans hmonoa) ((hle.trans hE5).trans_eq (by norm_num))
  have hidxa : (fixV (Subgroup.zpowers a)).index = 16 :=
    le_antisymm (hmonoa.trans hidx16.le) h16a
  have haU : fixV (Subgroup.zpowers a) = fixV E :=
    (eq_of_le_of_index_eq (hle_of a haE) (by rw [hidx16, hidxa])).symm
  have hE16 : 16 ≤ Nat.card E := by rw [← hidx16]; exact hle
  have hEL4 : 4 ≤ Nat.card ↥(E ⊓ L) := by omega
  obtain ⟨b, hbEL, hb1, hba⟩ := exists_mem_ne_one_ne (E ⊓ L) (by omega) a
  have hbE : b ∈ E := (Subgroup.mem_inf.1 hbEL).1
  have hbL : b ∈ L := (Subgroup.mem_inf.1 hbEL).2
  have hb2 : b * b = 1 := by have := hel.2 b hbE; rwa [sq] at this
  set a' : ↥L := ⟨a, haL⟩ with ha'
  set b' : ↥L := ⟨b, hbL⟩ with hb'
  have ha'2 : a' * a' = 1 := Subtype.ext ha2
  have hb'2 : b' * b' = 1 := Subtype.ext hb2
  have hab' : a' * b' = b' * a' := Subtype.ext (hel.1 a haE b hbE)
  have hu := orderOf_mk_eq_two hodd e ha'2 (fun h => ha1' (congrArg Subtype.val h))
  have hv := orderOf_mk_eq_two hodd e hb'2 (fun h => hb1 (congrArg Subtype.val h))
  have hvu : e (QuotientGroup.mk b') ≠ e (QuotientGroup.mk a') := by
    intro h
    have h1 : (QuotientGroup.mk b' : CQ L) = QuotientGroup.mk a' := e.injective h
    rw [QuotientGroup.eq] at h1
    have hbinv : b'⁻¹ = b' := inv_eq_of_mul_eq_one_right hb'2
    have h2 : b'⁻¹ * a' * (b'⁻¹ * a') = 1 := by
      rw [hbinv]
      calc b' * a' * (b' * a') = b' * (a' * b') * a' := by group
        _ = b' * (b' * a') * a' := by rw [hab']
        _ = (b' * b') * (a' * a') := by group
        _ = 1 := by rw [hb'2, ha'2, one_mul]
    have h3 := Proving.eq_one_of_mem_center_of_mul_self hodd h1 h2
    exact hba (congrArg Subtype.val (inv_mul_eq_one.1 h3))
  have hcuv : Commute (e (QuotientGroup.mk a')) (e (QuotientGroup.mk b')) := by
    show e (QuotientGroup.mk a') * e (QuotientGroup.mk b') =
      e (QuotientGroup.mk b') * e (QuotientGroup.mk a')
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab']
  obtain ⟨c, hca, hnc⟩ := hF2 _ _ hu hv hvu hcuv
  obtain ⟨c', hc'⟩ := QuotientGroup.mk_surjective (e.symm c)
  have hcc : e (QuotientGroup.mk c') = c := by rw [hc']; exact e.apply_symm_apply c
  subst hcc
  have hc'a : c' * a' = a' * c' :=
    mul_comm_of_mk_commute hodd ha'2 (e.injective (by rw [map_mul, map_mul]; exact hca))
  have hca' : Commute (c' : MulAut W) a := congrArg Subtype.val hc'a
  have hcU : ∀ u ∈ fixV E, (c' : MulAut W) u ∈ fixV E := by
    intro u hu
    rw [← haU] at hu ⊢
    exact Proving.apply_mem_fixV_zpowers_of_commute hca' hu
  have hcU' : ∀ u ∈ fixV E, (c' : MulAut W)⁻¹ u ∈ fixV E := by
    intro u hu
    rw [← haU] at hu ⊢
    exact Proving.apply_mem_fixV_zpowers_of_commute hca'.inv_left hu
  have hbPU : b ∈ Proving.pUMul (fixV E) := Proving.le_pUMul_fixV hquad hbE
  have hcbPU := Proving.conj_mem_pUMul hcU hcU' hbPU
  have hbcb := Proving.pUMul_mul_comm hbPU hcbPU
  apply hnc
  have hL : b' * (c' * b' * c'⁻¹) = (c' * b' * c'⁻¹) * b' := Subtype.ext hbcb
  have := congrArg (fun y : ↥L => e (QuotientGroup.mk y)) hL
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv] at this
  exact this

theorem weight_lt_of_three_dvd_center (hW : ∀ w : W, w * w = 1) {E : Subgroup (MulAut W)}
    (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L) (e : CQ L ≃* S)
    (hcent : Subgroup.center S = ⊥) (hS : 3 ^ 6 ∣ Nat.card S)
    (hZ : 3 ∣ Nat.card (Subgroup.center ↥L)) (hm2 : AutTwoRankLE S 5)
    (hOut : OutElemIndexLE S 4) (hF1 : U43F1 S) (hF2 : U43F2 S) (hF3 : U43F3 S)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hE : E ≠ ⊥)
    (hel : IsElemAbelian2 E) (hquad : IsQuadratic E) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hperf : Group.IsPerfect ↥L := hq.1
  have hodd := odd_card_center_of_isIrrOn hW hirr
  have h37 : 3 ^ 7 ∣ Nat.card L := by
    have h := Subgroup.card_mul_index (Subgroup.center ↥L)
    have hidx : (Subgroup.center ↥L).index = Nat.card S := by
      rw [Subgroup.index]
      exact Nat.card_congr e.toEquiv
    rw [hidx] at h
    rw [← h, show 3 ^ 7 = 3 * 3 ^ 6 by norm_num]
    exact mul_dvd_mul hZ hS
  have hW12 := two_pow_twelve_le_card_of_three_pow_seven_dvd hW h37
  let Φ : ↥E →* MulAut S := psiHom L e hEN
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    by_contra hb1
    exact psiAut_ne_one hW hperf hirr hEN hel e hcent b.2 (fun h => hb1 (Subtype.ext h)) hb
  have hE5 : Nat.card E ≤ 2 ^ 5 := by
    have h1 : Nat.card E = Nat.card Φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [h1]
    refine hm2 _ ?_ ?_
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg Φ (Subtype.ext (hel.1 a a.2 b b.2))
    · rintro _ ⟨a, rfl⟩
      rw [← map_mul]
      have : a * a = 1 := Subtype.ext (by have := hel.2 a a.2; simpa [pow_two] using this)
      rw [this, map_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' 3 hZ
  set z : MulAut W := ((z₀ : ↥L) : MulAut W) with hzdef
  have hzLmem : z ∈ L := (z₀ : ↥L).2
  have hzo : orderOf z = 3 := by rw [hzdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz₀]
  have hz3 : z ^ 3 = 1 := hzo ▸ pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzo
    omega
  have hzL : ∀ l ∈ L, l * z = z * l := by
    intro l hl
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 z₀.2 ⟨l, hl⟩)
  have hfpf := Proving.fpf_of_mem_center_of_isIrrOn hirr (fun l hl => (hzL l hl).symm) hz1
  by_cases hA : ∃ t ∈ E, t * z * t⁻¹ ≠ z
  · obtain ⟨t, htE, htz⟩ := hA
    exact weight_lt_of_conj_ne hW hirr h37 hEN hel hE5 hzLmem hz3 hzL htE htz
  push Not at hA
  have hEz : ∀ t ∈ E, t * z = z * t := by
    intro t ht
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [hA t ht]
  apply weight_lt_of_lt_index
  by_contra hle
  push Not at hle
  by_cases hEL : E ⊓ L = ⊥
  · exact false_of_inf_eq_bot hW hq hirr e hcent hOut hF1 hF3 hz3 hfpf hzL hW12 hEN hE hel hquad
      hEz hle hEL
  · exact false_of_inf_ne_bot hW hq hirr e hOut hF1 hF2 hz3 hfpf hzL hEN hel hquad hEz hE5 hle
      hEL

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
