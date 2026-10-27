module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.CentralizerDQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndCnt
public import CFSG.LinearAlgebra.GLInvariantEndSubgroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.CentralizerANormalizerD

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

theorem ThCyc.phi_b_eq_sq {G : Type} [Group G] {D : Subgroup G} {b : G} (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {d : G} (hd : d ∈ D) : d⁻¹ * (b * d * b⁻¹) = d ^ 2 := by
  have hd4 : d ^ 4 = 1 := h4 d hd
  have hd2sq : d ^ 2 * d ^ 2 = 1 := by
    rw [← pow_add]
    norm_num
    exact hd4
  calc d⁻¹ * (b * d * b⁻¹) = d⁻¹ * d⁻¹ := by rw [hb d hd]
    _ = (d * d)⁻¹ := by rw [← mul_inv_rev]
    _ = (d ^ 2)⁻¹ := by rw [pow_two]
    _ = d ^ 2 := inv_eq_of_mul_eq_one_right hd2sq

theorem ThCyc.phi_centralizer_eq_one {G : Type} [Group G] {D : Subgroup G} {c : G}
    (hc : c ∈ centralizer (D : Set G)) {d : G} (hd : d ∈ D) : d⁻¹ * (c * d * c⁻¹) = 1 := by
  have hcd : c * d = d * c := (mem_centralizer_iff.1 hc d hd).symm
  calc d⁻¹ * (c * d * c⁻¹) = d⁻¹ * ((d * c) * c⁻¹) := by rw [hcd]
    _ = 1 := by group

theorem ThCyc.b_not_mem_centralizer_D {G : Type} [Group G] {L S A B Aa D : Subgroup G} {z b : G}
    {t : G} (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) : b ∉ centralizer (D : Set G) := by
  intro hbC
  obtain ⟨x, hxAa, hx2⟩ := W2.exists_sq_ne_one W
  have hxD : x ∈ D := hD.Aa_le hxAa
  have h1 : b * x = x * b := (mem_centralizer_iff.1 hbC x hxD).symm
  have h2 : b * x * b⁻¹ = x := by
    calc b * x * b⁻¹ = (x * b) * b⁻¹ := by rw [h1]
      _ = x := by group
  have h3 : b * x * b⁻¹ = x⁻¹ := hb x hxD
  have h4 : x⁻¹ = x := h3.symm.trans h2
  apply hx2
  calc x ^ 2 = x * x := sq x
    _ = x * x⁻¹ := by rw [h4]
    _ = 1 := mul_inv_cancel x

theorem ThCyc.exists_sq_of_mem_A {G : Type} [Group G] {B A Aa D : Subgroup G} {b : G} {t : G}
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (a : ↥A) : ∃ d : ↥D, (d : G) ^ 2 = (a : G) := by
  obtain ⟨x, hx, hx2⟩ := (W2.A_eq_sq (a : G)).1 a.2
  exact ⟨⟨x, hD.Aa_le hx⟩, hx2⟩

private noncomputable def conjAut {G : Type} [Group G] {A : Subgroup G} (n : G)
    (hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A) (hnAinv : ∀ a ∈ A, n⁻¹ * a * n ∈ A) : ↥A ≃* ↥A where
  toFun a := ⟨n * a * n⁻¹, hnA a a.2⟩
  invFun a := ⟨n⁻¹ * a * n, hnAinv a a.2⟩
  left_inv a := Subtype.ext (by group)
  right_inv a := Subtype.ext (by group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem ThCyc.conjAut_apply {G : Type} [Group G] {A : Subgroup G} (n : G)
    (hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A) (hnAinv : ∀ a ∈ A, n⁻¹ * a * n ∈ A) (a : ↥A) :
    conjAut n hnA hnAinv a = ⟨n * a * n⁻¹, hnA a a.2⟩ := rfl

private theorem ThCyc.conjAut_symm_apply {G : Type} [Group G] {A : Subgroup G} (n : G)
    (hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A) (hnAinv : ∀ a ∈ A, n⁻¹ * a * n ∈ A) (a : ↥A) :
    (conjAut n hnA hnAinv).symm a = ⟨n⁻¹ * a * n, hnAinv a a.2⟩ := by
  apply (conjAut n hnA hnAinv).injective
  rw [MulEquiv.apply_symm_apply]
  rw [ThCyc.conjAut_apply]
  apply Subtype.ext
  show (a : G) = n * (n⁻¹ * (a : G) * n) * n⁻¹
  group

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

@[expose] def ThCyc.K1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) : Subgroup G where
  carrier := {κ | κ ∈ normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) ∧
    ∀ d ∈ D, d⁻¹ * (κ * d * κ⁻¹) ∈ A}
  one_mem' := ⟨Subgroup.one_mem _, fun d _ => by simp⟩
  mul_mem' := by
    rintro κ κ' ⟨hκK, hκA⟩ ⟨hκ'K, hκ'A⟩
    refine ⟨(normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)).mul_mem hκK hκ'K,
      fun d hd => ?_⟩
    rw [H.conj_D_mul_mul_conj W W2 hD h4 hκK hκ'K hd]
    exact A.mul_mem (hκA d hd) (hκ'A d hd)
  inv_mem' := by
    rintro κ ⟨hκK, hκA⟩
    refine ⟨(normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)).inv_mem hκK,
      fun d hd => ?_⟩
    simp only [inv_inv]
    rw [H.conj_D_mul_inv W W2 hD h4 hκK hd]
    exact A.inv_mem (hκA d hd)

theorem ThCyc.mem_K1_iff (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G} : κ ∈ K1 H W W2 hD h4 ↔
      κ ∈ normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) ∧
        ∀ d ∈ D, d⁻¹ * (κ * d * κ⁻¹) ∈ A := Iff.rfl

theorem ThCyc.K1_le_K (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) : K1 H W W2 hD h4 ≤
      normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
  fun _ hκ => hκ.1

theorem ThCyc.centralizer_le_K1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    centralizer (D : Set G) ≤ K1 H W W2 hD h4 := by
  intro c hc
  refine (H.mem_K1_iff W W2 hD h4).2
    ⟨(centralizer_le_inf_normalizer_centralizer_omega1 hD.comm) hc, fun d hd => ?_⟩
  have hcd : c * d = d * c := (mem_centralizer_iff.1 hc d hd).symm
  rw [show d⁻¹ * (c * d * c⁻¹) = 1 by
    calc d⁻¹ * (c * d * c⁻¹) = d⁻¹ * ((d * c) * c⁻¹) := by rw [hcd]
      _ = 1 := by group]
  exact A.one_mem

theorem ThCyc.b_mem_K1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    b ∈ K1 H W W2 hD h4 := by
  have hbL : b ∈ L := W.B_le W2.b_mem
  have hbA : ∀ a ∈ A, b * a * b⁻¹ ∈ A := fun a ha => by
    have haa : a * a = 1 := by rw [← pow_two]; exact W.A_sq a ha
    rw [W2.b_inv a (W2.A_le ha), inv_eq_of_mul_eq_one_right haa]
    exact ha
  have hbW5 : b ∈ normalizer ((W5 A t : Subgroup G) : Set G) :=
    H.mem_normalizer_W5_of_L W hbL hbA
  have hbD : b ∈ normalizer (D : Set G) := le_normalizer_of_conj_mem hD.norm hbW5
  have hbV : b ∈ centralizer (omega1 D hD.comm : Set G) :=
    mem_centralizer_iff.2 fun v hv => by
      have h := H.comm_omega1_of_mem_B W W2 hD hb W2.b_mem hv
      calc v * b = (b * v * b⁻¹) * b := by rw [h]
        _ = b * v := by group
  refine (H.mem_K1_iff W W2 hD h4).2 ⟨⟨hbD, hbV⟩, fun d hd => ?_⟩
  rw [ThCyc.phi_b_eq_sq h4 hb hd]
  exact H.D_sq_mem_A_of_fourth W W2 hD h4 hd

theorem ThCyc.centralizer_t_inf_K_le_B (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) ⊓
      centralizer ({t} : Set G) ≤ B := by
  intro x hx
  obtain ⟨hxK, hxt⟩ := hx
  have hxN : x ∈ normalizer (D : Set G) := hxK.1
  have hxV : x ∈ centralizer (omega1 D hD.comm : Set G) := hxK.2
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  have hA_le_L : A ≤ L := fun a ha => W.S_le ((W.mem_A_iff a).1 ha).1
  have hxNC : x ∈ normalizer (D : Set G) ⊓ centralizer ({t} : Set G) := ⟨hxN, hxt⟩
  rw [H.normalizer_D_inf_centralizer_t W W2 hD] at hxNC
  have hcomm : zpowers t ≤
      centralizer ((L ⊓ normalizer (A : Set G) : Subgroup G) : Set G) := by
    intro r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    exact mem_centralizer_iff.2 fun l hl =>
      (((show Commute l t from (H.comm_of_mem_L hl.1).symm).zpow_right k).eq)
  obtain ⟨l, hl, r, hr, hxlr⟩ := exists_mul_of_mem_sup hcomm hxNC
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
  have hx_eq : x = l * t ^ k := hxlr
  rcases zpow_eq_one_or_self H.sq_t k with hk | hk
  · rw [hk, mul_one] at hx_eq
    have hx' : x = l := hx_eq
    rw [hx']
    refine (W.mem_B_iff l hl.1).2 fun a ha => ?_
    have hcomm' : a * x = x * a :=
      mem_centralizer_iff.1 hxV a (H.A_le_omega1 W W2 hD ha)
    calc l * a = x * a := by rw [hx']
      _ = a * x := hcomm'.symm
      _ = a * l := by rw [hx']
  · rw [hk] at hx_eq
    have hx' : x = l * t := hx_eq
    have hxA : ∀ a ∈ A, x * a * x⁻¹ = a := fun a ha => by
      have h := mem_centralizer_iff.1 hxV a (H.A_le_omega1 W W2 hD ha)
      calc x * a * x⁻¹ = (a * x) * x⁻¹ := by rw [← h]
        _ = a := by group
    have htA : ∀ a ∈ A, t * a * t⁻¹ = a := fun a ha => by
      have h := H.comm_of_mem_L (hA_le_L ha)
      calc t * a * t⁻¹ = (a * t) * t⁻¹ := by rw [h]
        _ = a := by group
    have hlA : ∀ a ∈ A, l * a * l⁻¹ = a := fun a ha => by
      have hx_a : l * t * a * (l * t)⁻¹ = a := by
        rw [← hx']
        exact hxA a ha
      calc l * a * l⁻¹ = l * (t * a * t⁻¹) * l⁻¹ := by rw [htA a ha]
        _ = (l * t) * a * (l * t)⁻¹ := by group
        _ = a := hx_a
    have hlB : l ∈ B := (W.mem_B_iff l hl.1).2 fun a ha => by
      calc l * a = (l * a * l⁻¹) * l := by group
        _ = a * l := by rw [hlA a ha]
    have hlV : ∀ v ∈ omega1 D hD.comm, l * v * l⁻¹ = v :=
      fun v hv => H.comm_omega1_of_mem_B W W2 hD hb hlB hv
    have htV : ∀ v ∈ omega1 D hD.comm, t * v * t⁻¹ = v := by
      intro v hv
      have ht_eq : t = l⁻¹ * x := by rw [hx']; group
      have hxv : x * v * x⁻¹ = v := by
        have h := mem_centralizer_iff.1 hxV v hv
        calc x * v * x⁻¹ = (v * x) * x⁻¹ := by rw [← h]
          _ = v := by group
      calc t * v * t⁻¹ = l⁻¹ * (x * v * x⁻¹) * l := by rw [ht_eq]; group
        _ = l⁻¹ * v * l := by rw [hxv]
        _ = l⁻¹ * (l * v * l⁻¹) * l := by rw [hlV v hv]
        _ = v := by group
    have hVA : omega1 D hD.comm ≤ A := by
      intro v hv
      rw [← H.omega1_inf_centralizer_t W W2 hD]
      exact ⟨hv, mem_centralizer_singleton_iff.2 (by
        calc v * t = (t * v * t⁻¹) * t := by rw [htV v hv]
          _ = t * v := by group)⟩
    have hcard := Subgroup.card_le_of_le hVA
    rw [H.card_omega1 W W2 hD hsq, W.A_card] at hcard
    norm_num at hcard

theorem ThCyc.card_centralizer_t_inf_K_le (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    Nat.card ↥(normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) ⊓
      centralizer ({t} : Set G)) ≤ 2 ^ 9 :=
  (Subgroup.card_le_of_le (H.centralizer_t_inf_K_le_B W W2 hD h4 hb)).trans
    (le_of_eq W.B_card)

private theorem ThCyc.t_inv_eq (H : ThCyc G L R t) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (by simpa [sq] using H.sq_t)

private theorem ThCyc.t_comm_A (H : ThCyc G L R t) (W : ThLocalIn L S A B z) {a : G} (ha : a ∈ A) :
    t * a * t⁻¹ = a := by
  have h := H.comm_of_mem_L (W.S_le ((W.mem_A_iff a).1 ha).1)
  calc t * a * t⁻¹ = (a * t) * t⁻¹ := by rw [h]
    _ = a := by group

private theorem ThCyc.t_mem_normalizer_D (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) : t ∈ normalizer (D : Set G) :=
  le_normalizer_of_conj_mem hD.norm (H.t_mem_normalizer W W2 hD)

private theorem ThCyc.t_mem_normalizer_omega1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) : t ∈ normalizer ((omega1 D hD.comm) : Set G) :=
  H.normalizer_le_normalizer_omega1 W W2 hD (H.t_mem_normalizer W W2 hD)

private theorem ThCyc.t_inv_conj_mem_D (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {d : G} (hd : d ∈ D) : t⁻¹ * d * t ∈ D := by
  have h := (mem_normalizer_iff.1 ((normalizer (D : Set G)).inv_mem
    (H.t_mem_normalizer_D W W2 hD)) d).1 hd
  simpa using h

private theorem ThCyc.inv_conj_t_mem_omega1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {d : G} (hd : d ∈ D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    d⁻¹ * (t⁻¹ * d * t) ∈ (omega1 D hD.comm) := by
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  have huD : t⁻¹ * d * t ∈ D := H.t_inv_conj_mem_D W W2 hD hd
  have hvD : d⁻¹ * (t⁻¹ * d * t) ∈ D := D.mul_mem (D.inv_mem hd) huD
  refine mem_omega1_iff.2 ⟨hvD, ?_⟩
  have hu2 : (t⁻¹ * d * t) ^ 2 = d ^ 2 := by
    calc (t⁻¹ * d * t) ^ 2 = t⁻¹ * d ^ 2 * t := by rw [sq, sq]; group
      _ = t * d ^ 2 * t⁻¹ := by rw [H.t_inv_eq]
      _ = d ^ 2 := by
          have hA : d ^ 2 ∈ A := hsq d hd
          have hL : d ^ 2 ∈ L := W.S_le ((W.mem_A_iff (d ^ 2)).1 hA).1
          have h := H.comm_of_mem_L hL
          calc t * (d ^ 2) * t⁻¹ = ((d ^ 2) * t) * t⁻¹ := by rw [h]
            _ = d ^ 2 := by group
  have hc : Commute d⁻¹ (t⁻¹ * d * t) := hD.comm _ (D.inv_mem hd) _ huD
  rw [hc.mul_pow, inv_pow, hu2]
  exact inv_mul_cancel _

theorem ThCyc.phi_apply_inv (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ d : G}
    (hκ : κ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))) (hd : d ∈ D) :
    κ⁻¹ * d * κ = d * (d⁻¹ * (κ * d * κ⁻¹)) := by
  set φ := d⁻¹ * (κ * d * κ⁻¹) with hφdef
  have hφV : φ ∈ (omega1 D hD.comm) := H.conj_D_mul_mem_omega1_of_mem_inf W W2 hD h4 hκ d hd
  have hκφ : κ * φ * κ⁻¹ = φ := by
    have hcomm := mem_centralizer_iff.1 hκ.2 φ hφV
    calc κ * φ * κ⁻¹ = (φ * κ) * κ⁻¹ := by rw [← hcomm]
      _ = φ := by group
  have hκd : κ * d * κ⁻¹ = d * φ := by rw [hφdef]; group
  have hκφcomm : κ * φ = φ * κ := (mem_centralizer_iff.1 hκ.2 φ hφV).symm
  have h4eq : (κ⁻¹ * d * κ) * φ = d := by
    calc (κ⁻¹ * d * κ) * φ = κ⁻¹ * d * (κ * φ) := by group
      _ = κ⁻¹ * d * (φ * κ) := by rw [hκφcomm]
      _ = κ⁻¹ * (d * φ) * κ := by group
      _ = κ⁻¹ * (κ * d * κ⁻¹) * κ := by rw [← hκd]
      _ = d := by group
  have hφ2 : φ * φ = 1 := H.omega1_mul_self W W2 hD hφV
  calc κ⁻¹ * d * κ = (κ⁻¹ * d * κ) * 1 := by rw [mul_one]
    _ = (κ⁻¹ * d * κ) * (φ * φ) := by rw [hφ2]
    _ = ((κ⁻¹ * d * κ) * φ) * φ := by group
    _ = d * φ := by rw [h4eq]

theorem ThCyc.phi_t_conj (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκ : κ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))) {d : G}
    (hd : d ∈ D) : (t⁻¹ * d * t)⁻¹ * (κ * (t⁻¹ * d * t) * κ⁻¹) = d⁻¹ * (κ * d * κ⁻¹) := by
  set u : G := t⁻¹ * d * t with hudef
  set v : G := d⁻¹ * u with hvdef
  have huD : u ∈ D := by
    rw [hudef]
    exact H.t_inv_conj_mem_D W W2 hD hd
  have hvV : v ∈ (omega1 D hD.comm) := by
    rw [hvdef, hudef]
    exact H.inv_conj_t_mem_omega1 W W2 hD hd h4
  have hvD : v ∈ D := D.mul_mem (D.inv_mem hd) huD
  have hu_eq : u = d * v := by rw [hvdef]; group
  have hmul := H.conj_D_mul_mul W W2 hD h4 hκ hd hvD
  have hvphi : v⁻¹ * (κ * v * κ⁻¹) = 1 :=
    inv_mul_conj_eq_one_of_mem_centralizer hD.comm hκ.2 hvV
  calc u⁻¹ * (κ * u * κ⁻¹)
      = (d * v)⁻¹ * (κ * (d * v) * κ⁻¹) := by rw [hu_eq]
    _ = (d⁻¹ * (κ * d * κ⁻¹)) * (v⁻¹ * (κ * v * κ⁻¹)) := hmul
    _ = d⁻¹ * (κ * d * κ⁻¹) := by rw [hvphi, mul_one]

theorem ThCyc.commutator_t_apply (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκ : κ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))) {d : G}
    (hd : d ∈ D) : (κ * t * κ⁻¹ * t⁻¹) * d * (κ * t * κ⁻¹ * t⁻¹)⁻¹ =
      d * ((d⁻¹ * (κ * d * κ⁻¹)) * (t * (d⁻¹ * (κ * d * κ⁻¹)) * t⁻¹)) := by
  set φ := d⁻¹ * (κ * d * κ⁻¹) with hφdef
  set u := t⁻¹ * d * t with hudef
  have huD : u ∈ D := H.t_inv_conj_mem_D W W2 hD hd
  have hφV : φ ∈ (omega1 D hD.comm) := H.conj_D_mul_mem_omega1_of_mem_inf W W2 hD h4 hκ d hd
  have hφu : u⁻¹ * (κ * u * κ⁻¹) = φ := by
    rw [hudef, hφdef]
    exact H.phi_t_conj W W2 hD h4 hκ hd
  have hκinv : κ⁻¹ * u * κ = u * φ := by
    rw [← hφu]
    exact H.phi_apply_inv W W2 hD h4 hκ huD
  have htu : t * u * t⁻¹ = d := by
    rw [hudef]
    group
  have hwV : t * φ * t⁻¹ ∈ (omega1 D hD.comm) :=
    (mem_normalizer_iff.1 (H.t_mem_normalizer_omega1 W W2 hD) φ).1 hφV
  have hκw : κ * (t * φ * t⁻¹) * κ⁻¹ = t * φ * t⁻¹ := by
    have hcomm := mem_centralizer_iff.1 hκ.2 _ hwV
    calc κ * (t * φ * t⁻¹) * κ⁻¹ = ((t * φ * t⁻¹) * κ) * κ⁻¹ := by rw [← hcomm]
      _ = t * φ * t⁻¹ := by group
  have huφ : t * (u * φ) * t⁻¹ = d * (t * φ * t⁻¹) := by
    calc t * (u * φ) * t⁻¹ = (t * u * t⁻¹) * (t * φ * t⁻¹) := by group
      _ = d * (t * φ * t⁻¹) := by rw [htu]
  have hκd : κ * d * κ⁻¹ = d * φ := by rw [hφdef]; group
  calc (κ * t * κ⁻¹ * t⁻¹) * d * (κ * t * κ⁻¹ * t⁻¹)⁻¹
      = κ * t * (κ⁻¹ * (t⁻¹ * d * t) * κ) * t⁻¹ * κ⁻¹ := by group
    _ = κ * t * (u * φ) * t⁻¹ * κ⁻¹ := by rw [hκinv]
    _ = κ * (t * (u * φ) * t⁻¹) * κ⁻¹ := by group
    _ = κ * (d * (t * φ * t⁻¹)) * κ⁻¹ := by rw [huφ]
    _ = (κ * d * κ⁻¹) * (κ * (t * φ * t⁻¹) * κ⁻¹) := by group
    _ = (d * φ) * (t * φ * t⁻¹) := by rw [hκd, hκw]
    _ = d * (φ * (t * φ * t⁻¹)) := by group

theorem ThCyc.commutator_t_mem_K (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {κ : G}
    (hκ : κ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))) :
    κ * t * κ⁻¹ * t⁻¹ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) := by
  have h1 : t * κ * t⁻¹ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :=
    normalizer_conj_mem_normalizer_inf_centralizer_omega1 hD.comm
      (H.t_mem_normalizer_D W W2 hD) hκ
  have h2 : t * κ⁻¹ * t⁻¹ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) := by
    have hthis : t * (κ⁻¹ * t⁻¹) ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
      := by
      simpa [mul_inv_rev] using ((normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set
        G))).inv_mem h1
    rwa [show t * κ⁻¹ * t⁻¹ = t * (κ⁻¹ * t⁻¹) by group]
  have h3 : κ * (t * κ⁻¹ * t⁻¹) ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    := ((normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))).mul_mem hκ h2
  rwa [show κ * t * κ⁻¹ * t⁻¹ = κ * (t * κ⁻¹ * t⁻¹) by group]

theorem ThCyc.phi_commutator (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκ : κ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))) {d : G}
    (hd : d ∈ D) : d⁻¹ * ((κ * t * κ⁻¹ * t⁻¹) * d * (κ * t * κ⁻¹ * t⁻¹)⁻¹) =
      thV t (d⁻¹ * (κ * d * κ⁻¹)) := by
  rw [H.commutator_t_apply W W2 hD h4 hκ hd]
  rw [thV]
  group

theorem ThCyc.commutator_t_mem_K1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκ : κ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))) :
    κ * t * κ⁻¹ * t⁻¹ ∈ K1 H W W2 hD h4 := by
  refine (H.mem_K1_iff W W2 hD h4).2 ⟨H.commutator_t_mem_K W W2 hD hκ, fun d hd => ?_⟩
  rw [H.phi_commutator W W2 hD h4 hκ hd]
  exact H.thV_mem_A W W2 hD
    (H.conj_D_mul_mem_omega1_of_mem_inf W W2 hD h4 hκ d hd)

theorem ThCyc.thV_eq_one_of_mem_A (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {v : G} (hv : v ∈ A) : thV t v = 1 := by
  have hV : v ∈ (omega1 D hD.comm) := H.A_le_omega1 W W2 hD hv
  have ht : t * v * t⁻¹ = v := H.t_comm_A W hv
  rw [thV, ht, ← sq]
  exact W.A_sq v hv

theorem ThCyc.thV_inv (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) {v : G} (hv : v ∈ (omega1 D hD.comm)) : thV t v⁻¹ = (thV t v)⁻¹ := by
  have hv' : v⁻¹ ∈ (omega1 D hD.comm) := ((omega1 D hD.comm)).inv_mem hv
  have h := H.thV_mul W W2 hD hv' hv
  rw [inv_mul_cancel, show thV t 1 = 1 by simp [thV]] at h
  have h' : thV t v⁻¹ * thV t v = 1 := h.symm
  calc thV t v⁻¹ = (thV t v⁻¹ * thV t v) * (thV t v)⁻¹ := by group
    _ = 1 * (thV t v)⁻¹ := by rw [h']
    _ = (thV t v)⁻¹ := one_mul _

theorem ThCyc.mem_K1_iff_commutator_mem_centralizer (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκ : κ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))) :
    κ ∈ K1 H W W2 hD h4 ↔ κ * t * κ⁻¹ * t⁻¹ ∈ (centralizer (D : Set G)) := by
  constructor
  · intro hκ1
    refine mem_centralizer_iff_forall_inv_mul_conj_eq_one.2 fun d hd => ?_
    rw [H.phi_commutator W W2 hD h4 hκ hd]
    exact H.thV_eq_one_of_mem_A W W2 hD (hκ1.2 d hd)
  · intro he
    refine (H.mem_K1_iff W W2 hD h4).2 ⟨hκ, fun d hd => ?_⟩
    have hφV := H.conj_D_mul_mem_omega1_of_mem_inf W W2 hD h4 hκ d hd
    have h1 : d⁻¹ * ((κ * t * κ⁻¹ * t⁻¹) * d * (κ * t * κ⁻¹ * t⁻¹)⁻¹) = 1 :=
      mem_centralizer_iff_forall_inv_mul_conj_eq_one.1 he d hd
    rw [H.phi_commutator W W2 hD h4 hκ hd] at h1
    exact (H.thV_eq_one_iff W W2 hD hφV).1 h1

theorem ThCyc.commutator_t_mem_centralizer_of_mem_K1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκ : κ ∈ K1 H W W2 hD h4) : κ * t * κ⁻¹ * t⁻¹ ∈ (centralizer (D : Set G)) :=
  (H.mem_K1_iff_commutator_mem_centralizer W W2 hD h4 (H.K1_le_K W W2 hD h4 hκ)).1 hκ

theorem ThCyc.card_K1_le (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    Nat.card (K1 H W W2 hD h4) ≤ Nat.card ((centralizer (D : Set G))) * 2 ^ 9 := by
  have hfib := SylowEnd.ncard_le_of_fibers
    (X := (K1 H W W2 hD h4 : Set G)) (F := ((centralizer (D : Set G)) : Set G))
    (K := ((K1 H W W2 hD h4) ⊓ centralizer ({t} : Set G) : Set G))
    (φ := fun κ => κ * t * κ⁻¹ * t⁻¹)
    (fun κ hκ => H.commutator_t_mem_centralizer_of_mem_K1 W W2 hD h4 hκ)
    (fun κ hκ κ' hκ' hφ => by
      have hmem : κ⁻¹ * κ' ∈ K1 H W W2 hD h4 :=
        (K1 H W W2 hD h4).mul_mem ((K1 H W W2 hD h4).inv_mem hκ) hκ'
      have h1 : κ * t * κ⁻¹ = κ' * t * κ'⁻¹ := by
        calc κ * t * κ⁻¹ = (κ * t * κ⁻¹ * t⁻¹) * t := by group
          _ = (κ' * t * κ'⁻¹ * t⁻¹) * t := by rw [hφ]
          _ = κ' * t * κ'⁻¹ := by group
      have h2 : (κ'⁻¹ * κ) * t * (κ'⁻¹ * κ)⁻¹ = t := by
        calc (κ'⁻¹ * κ) * t * (κ'⁻¹ * κ)⁻¹ = κ'⁻¹ * (κ * t * κ⁻¹) * κ' := by group
          _ = κ'⁻¹ * (κ' * t * κ'⁻¹) * κ' := by rw [h1]
          _ = t := by group
      have h3 : (κ⁻¹ * κ') * t * (κ⁻¹ * κ')⁻¹ = t := by
        have h := congrArg (fun x => (κ'⁻¹ * κ)⁻¹ * x * (κ'⁻¹ * κ)) h2
        simpa [mul_assoc] using h.symm
      refine ⟨hmem, mem_centralizer_singleton_iff.2 ?_⟩
      calc (κ⁻¹ * κ') * t = ((κ⁻¹ * κ') * t * (κ⁻¹ * κ')⁻¹) * (κ⁻¹ * κ') := by group
        _ = t * (κ⁻¹ * κ') := by rw [h3])
  have hK1card : Nat.card (K1 H W W2 hD h4) = (K1 H W W2 hD h4 : Set G).ncard :=
    Nat.card_coe_set_eq ((K1 H W W2 hD h4) : Set G)
  have hCcard : Nat.card ((centralizer (D : Set G))) = ((centralizer (D : Set G)) : Set G).ncard :=
    Nat.card_coe_set_eq ((centralizer (D : Set G)) : Set G)
  rw [hK1card, hCcard]
  refine hfib.trans (Nat.mul_le_mul_left _ ?_)
  rw [← Nat.card_coe_set_eq ((K1 H W W2 hD h4) ⊓ centralizer ({t} : Set G) : Set G)]
  refine (Subgroup.card_le_of_le (le_inf (inf_le_left.trans (H.K1_le_K W W2 hD h4))
    inf_le_right)).trans ?_
  exact H.card_centralizer_t_inf_K_le W W2 hD h4 hb

section

private noncomputable def phiD (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (κ : G)
    (hκ : κ ∈ ThCyc.K1 H W W2 hD h4) : ↥D →* ↥A where
  toFun d := ⟨(d : G)⁻¹ * (κ * (d : G) * κ⁻¹), hκ.2 (d : G) d.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' d d' := Subtype.ext (H.conj_D_mul_mul W W2 hD h4 hκ.1 d.2 d'.2)

private theorem ThCyc.phiD_apply_eq_of_sq_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκ : κ ∈ ThCyc.K1 H W W2 hD h4) {d d' : ↥D} (h : (d : G) ^ 2 = (d' : G) ^ 2) :
    phiD H W W2 hD h4 κ hκ d = phiD H W W2 hD h4 κ hκ d' := by
  apply Subtype.ext
  show (d : G)⁻¹ * (κ * (d : G) * κ⁻¹) = (d' : G)⁻¹ * (κ * (d' : G) * κ⁻¹)
  set w : G := (d : G)⁻¹ * (d' : G) with hw
  have hwD : w ∈ D := D.mul_mem (D.inv_mem d.2) d'.2
  have hw2 : w ^ 2 = 1 := by
    have hc : Commute ((d : G)⁻¹) (d' : G) := hD.comm _ (D.inv_mem d.2) _ d'.2
    rw [hw, hc.mul_pow, inv_pow]
    rw [h, inv_mul_cancel]
  have hwV : w ∈ (omega1 D hD.comm) := mem_omega1_iff.2 ⟨hwD, hw2⟩
  have hwphi : w⁻¹ * (κ * w * κ⁻¹) = 1 :=
    inv_mul_conj_eq_one_of_mem_centralizer hD.comm hκ.1.2 hwV
  have hd' : (d' : G) = (d : G) * w := by rw [hw]; group
  have hmul := H.conj_D_mul_mul W W2 hD h4 hκ.1 d.2 hwD
  calc (d : G)⁻¹ * (κ * (d : G) * κ⁻¹)
      = ((d : G)⁻¹ * (κ * (d : G) * κ⁻¹)) * 1 := by rw [mul_one]
    _ = ((d : G)⁻¹ * (κ * (d : G) * κ⁻¹)) * (w⁻¹ * (κ * w * κ⁻¹)) := by rw [hwphi]
    _ = ((d : G) * w)⁻¹ * (κ * ((d : G) * w) * κ⁻¹) := hmul.symm
    _ = (d' : G)⁻¹ * (κ * (d' : G) * κ⁻¹) := by rw [← hd']

private noncomputable def muA (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (κ : G)
    (hκ : κ ∈ ThCyc.K1 H W W2 hD h4) (a : ↥A) : ↥A :=
  phiD H W W2 hD h4 κ hκ
    (Classical.choose (ThCyc.exists_sq_of_mem_A W2 hD a))

private theorem ThCyc.muA_eq_phiD_of_sq_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκ : κ ∈ ThCyc.K1 H W W2 hD h4) (a : ↥A) (d : ↥D) (hd : (d : G) ^ 2 = (a : G)) :
    muA H W W2 hD h4 κ hκ a = phiD H W W2 hD h4 κ hκ d := by
  have h2 : ((Classical.choose (ThCyc.exists_sq_of_mem_A W2 hD a) : ↥D) : G) ^ 2 =
      (d : G) ^ 2 := by
    rw [Classical.choose_spec (ThCyc.exists_sq_of_mem_A W2 hD a), ← hd]
  exact H.phiD_apply_eq_of_sq_eq W W2 hD h4 hκ h2

private theorem ThCyc.muA_apply_sq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκ : κ ∈ ThCyc.K1 H W W2 hD h4) (d : ↥D) : muA H W W2 hD h4 κ hκ
        ⟨(d : G) ^ 2, H.D_sq_mem_A_of_fourth W W2 hD h4 d.2⟩ =
      phiD H W W2 hD h4 κ hκ d :=
  H.muA_eq_phiD_of_sq_eq W W2 hD h4 hκ _ d rfl

private theorem ThCyc.muA_one (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκ : κ ∈ ThCyc.K1 H W W2 hD h4) : muA H W W2 hD h4 κ hκ 1 = 1 := by
  rw [H.muA_eq_phiD_of_sq_eq W W2 hD h4 hκ 1 1 (by simp)]
  exact map_one _

private theorem ThCyc.muA_mul (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκ : κ ∈ ThCyc.K1 H W W2 hD h4) (a b : ↥A) : muA H W W2 hD h4 κ hκ (a * b) =
      muA H W W2 hD h4 κ hκ a * muA H W W2 hD h4 κ hκ b := by
  obtain ⟨da, hda⟩ := ThCyc.exists_sq_of_mem_A W2 hD a
  obtain ⟨db, hdb⟩ := ThCyc.exists_sq_of_mem_A W2 hD b
  have hdab : ((da * db : ↥D) : G) ^ 2 = ((a * b : ↥A) : G) := by
    show ((da : G) * (db : G)) ^ 2 = (a : G) * (b : G)
    rw [(show Commute (da : G) (db : G) from hD.comm _ da.2 _ db.2).mul_pow, hda, hdb]
  rw [H.muA_eq_phiD_of_sq_eq W W2 hD h4 hκ (a * b) (da * db) hdab,
      H.muA_eq_phiD_of_sq_eq W W2 hD h4 hκ a da hda,
      H.muA_eq_phiD_of_sq_eq W W2 hD h4 hκ b db hdb,
      map_mul]

private theorem ThCyc.muA_one_apply (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (a : ↥A) :
    muA H W W2 hD h4 (1 : G) (ThCyc.K1 H W W2 hD h4).one_mem a = 1 := by
  obtain ⟨d, hd⟩ := ThCyc.exists_sq_of_mem_A W2 hD a
  rw [H.muA_eq_phiD_of_sq_eq W W2 hD h4 (ThCyc.K1 H W W2 hD h4).one_mem a d hd]
  apply Subtype.ext
  show (d : G)⁻¹ * ((1 : G) * (d : G) * (1 : G)⁻¹) = 1
  group

private theorem ThCyc.muA_mul_apply (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ κ' : G}
    (hκ : κ ∈ ThCyc.K1 H W W2 hD h4) (hκ' : κ' ∈ ThCyc.K1 H W W2 hD h4) (a : ↥A) :
    muA H W W2 hD h4 (κ * κ')
        ((ThCyc.K1 H W W2 hD h4).mul_mem hκ hκ') a =
      muA H W W2 hD h4 κ hκ a * muA H W W2 hD h4 κ' hκ' a := by
  obtain ⟨d, hd⟩ := ThCyc.exists_sq_of_mem_A W2 hD a
  rw [H.muA_eq_phiD_of_sq_eq W W2 hD h4
        ((ThCyc.K1 H W W2 hD h4).mul_mem hκ hκ') a d hd,
      H.muA_eq_phiD_of_sq_eq W W2 hD h4 hκ a d hd,
      H.muA_eq_phiD_of_sq_eq W W2 hD h4 hκ' a d hd]
  apply Subtype.ext
  exact H.conj_D_mul_mul_conj W W2 hD h4 hκ.1 hκ'.1 d.2

variable [hAcomm : Fact (∀ a b : ↥A, a * b = b * a)]

local instance : IsMulCommutative ↥A := IsMulCommutative.of_comm (Fact.out)
local instance : CommGroup ↥A := IsMulCommutative.instCommGroup

private noncomputable def muHom (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    ↥(ThCyc.K1 H W W2 hD h4) →* (↥A →* ↥A) where
  toFun κ :=
    { toFun := muA H W W2 hD h4 κ.1 κ.2
      map_one' := H.muA_one W W2 hD h4 κ.2
      map_mul' := H.muA_mul W W2 hD h4 κ.2 }
  map_one' := by
    apply MonoidHom.ext
    intro a
    change muA H W W2 hD h4 (1 : G) (ThCyc.K1 H W W2 hD h4).one_mem a = 1
    exact H.muA_one_apply W W2 hD h4 a
  map_mul' κ κ' := by
    apply MonoidHom.ext
    intro a
    change muA H W W2 hD h4 (κ.1 * κ'.1)
        ((ThCyc.K1 H W W2 hD h4).mul_mem κ.2 κ'.2) a =
      muA H W W2 hD h4 κ.1 κ.2 a * muA H W W2 hD h4 κ'.1 κ'.2 a
    exact H.muA_mul_apply W W2 hD h4 κ.2 κ'.2 a

private theorem ThCyc.muHom_b (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    muHom H W W2 hD h4 ⟨b, H.b_mem_K1 W W2 hD h4 hb⟩ = MonoidHom.id ↥A := by
  apply MonoidHom.ext
  intro a
  obtain ⟨d, hd⟩ := ThCyc.exists_sq_of_mem_A W2 hD a
  change muA H W W2 hD h4 b (H.b_mem_K1 W W2 hD h4 hb) a = (MonoidHom.id ↥A) a
  rw [H.muA_eq_phiD_of_sq_eq W W2 hD h4 (H.b_mem_K1 W W2 hD h4 hb) a d hd]
  apply Subtype.ext
  show (d : G)⁻¹ * (b * (d : G) * b⁻¹) = (a : G)
  rw [← hd]
  exact ThCyc.phi_b_eq_sq h4 hb d.2

end

section

variable [hAcomm : Fact (∀ a b : ↥A, a * b = b * a)]

local instance : IsMulCommutative ↥A := IsMulCommutative.of_comm (Fact.out)
local instance : CommGroup ↥A := IsMulCommutative.instCommGroup

private theorem ThCyc.muHom_ker
    (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1)
    :
    (muHom H W W2 hD h4).ker = ((centralizer (D : Set G))).subgroupOf (ThCyc.K1 H W W2 hD h4) := by
  ext κ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    rw [mem_centralizer_iff_forall_inv_mul_conj_eq_one]
    intro d hd
    have h1 : (muHom H W W2 hD h4 κ)
        ⟨(d : G) ^ 2, H.D_sq_mem_A_of_fourth W W2 hD h4 hd⟩ = 1 := by
      rw [h]; rfl
    change muA H W W2 hD h4 κ.1 κ.2
        ⟨(d : G) ^ 2, H.D_sq_mem_A_of_fourth W W2 hD h4 hd⟩ = 1 at h1
    rw [H.muA_apply_sq W W2 hD h4 κ.2 ⟨d, hd⟩] at h1
    exact congrArg Subtype.val h1
  · intro hc
    apply MonoidHom.ext
    intro a
    obtain ⟨d, hd⟩ := ThCyc.exists_sq_of_mem_A W2 hD a
    change muA H W W2 hD h4 κ.1 κ.2 a = 1
    rw [H.muA_eq_phiD_of_sq_eq W W2 hD h4 κ.2 a d hd]
    apply Subtype.ext
    show (d : G)⁻¹ * (κ.1 * (d : G) * κ.1⁻¹) = 1
    exact ThCyc.phi_centralizer_eq_one hc d.2

private theorem ThCyc.card_range_mu_le (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) : Nat.card ↥(muHom H W W2 hD h4).range ≤ 2 ^ 9 := by
  rw [← Subgroup.index_ker (muHom H W W2 hD h4)]
  rw [H.muHom_ker W W2 hD h4]
  have h1 := Subgroup.index_mul_card (((centralizer (D : Set G))).subgroupOf (ThCyc.K1 H W W2 hD
    h4))
  have hcardC : Nat.card ↥(((centralizer (D : Set G))).subgroupOf (ThCyc.K1 H W W2 hD h4)) =
    Nat.card ((centralizer (D : Set G))) :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H.centralizer_le_K1 W W2 hD h4)).toEquiv
  rw [hcardC] at h1
  have h2 := H.card_K1_le W W2 hD h4 hb
  have h3 : (((centralizer (D : Set G))).subgroupOf (ThCyc.K1 H W W2 hD h4)).index * Nat.card
    ((centralizer (D : Set G))) ≤
      2 ^ 9 * Nat.card ((centralizer (D : Set G))) := by
    calc
      (((centralizer (D : Set G))).subgroupOf (ThCyc.K1 H W W2 hD h4)).index *
          Nat.card ((centralizer (D : Set G)))
        = Nat.card (ThCyc.K1 H W W2 hD h4) := h1
      _ ≤ Nat.card ((centralizer (D : Set G))) * 2 ^ 9 := h2
      _ = 2 ^ 9 * Nat.card ((centralizer (D : Set G))) := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right h3 Nat.card_pos

end

private theorem ThCyc.mem_K1_conj (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {n κ : G}
    (hκ : κ ∈ ThCyc.K1 H W W2 hD h4) (hnL : n ∈ L) (hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A) :
    n * κ * n⁻¹ ∈ ThCyc.K1 H W W2 hD h4 := by
  have hnNormA : n ∈ normalizer (A : Set G) := by
    have hinv : n⁻¹ ∈ normalizer (A : Set G) :=
      mem_normalizer_iff.2 (mem_iff_conj_of_conj_le A (g := n⁻¹) (by simpa using hnA))
    simpa using (normalizer (A : Set G)).inv_mem hinv
  have hnD : n ∈ normalizer (D : Set G) := by
    have : n ∈ L ⊓ normalizer (D : Set G) := by
      rw [H.inf_normalizer_D_eq W W2 hD]
      exact ⟨hnL, hnNormA⟩
    exact this.2
  have hnK : n * κ * n⁻¹ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :=
    normalizer_conj_mem_normalizer_inf_centralizer_omega1 hD.comm hnD hκ.1
  refine (H.mem_K1_iff W W2 hD h4).2 ⟨hnK, fun d hd => ?_⟩
  have hndD : n⁻¹ * d * n ∈ D := by
    have h := (mem_normalizer_iff.1 ((normalizer (D : Set G)).inv_mem hnD) d).1 hd
    simpa using h
  have hφA : (n⁻¹ * d * n)⁻¹ * (κ * (n⁻¹ * d * n) * κ⁻¹) ∈ A := hκ.2 _ hndD
  have hidentity : d⁻¹ * ((n * κ * n⁻¹) * d * (n * κ * n⁻¹)⁻¹) =
      n * ((n⁻¹ * d * n)⁻¹ * (κ * (n⁻¹ * d * n) * κ⁻¹)) * n⁻¹ := by group
  rw [hidentity]
  exact hnA _ hφA

private theorem ThCyc.muA_conj_apply (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ n : G}
    (hκ : κ ∈ ThCyc.K1 H W W2 hD h4) (hnL : n ∈ L) (hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A)
    (hnAinv : ∀ a ∈ A, n⁻¹ * a * n ∈ A) (a : ↥A) :
    muA H W W2 hD h4 (n * κ * n⁻¹) (H.mem_K1_conj W W2 hD h4 hκ hnL hnA) a =
      conjAut n hnA hnAinv
        (muA H W W2 hD h4 κ hκ ((conjAut n hnA hnAinv).symm a)) := by
  obtain ⟨d, hd⟩ := ThCyc.exists_sq_of_mem_A W2 hD a
  have hnNormA : n ∈ normalizer (A : Set G) := by
    have hinv : n⁻¹ ∈ normalizer (A : Set G) :=
      mem_normalizer_iff.2 (mem_iff_conj_of_conj_le A (g := n⁻¹) (by simpa using hnA))
    simpa using (normalizer (A : Set G)).inv_mem hinv
  have hnD : n ∈ normalizer (D : Set G) := by
    have : n ∈ L ⊓ normalizer (D : Set G) := by
      rw [H.inf_normalizer_D_eq W W2 hD]
      exact ⟨hnL, hnNormA⟩
    exact this.2
  have heD : n⁻¹ * (d : G) * n ∈ D := by
    have h := (mem_normalizer_iff.1 ((normalizer (D : Set G)).inv_mem hnD) (d : G)).1 d.2
    simpa using h
  have hsymm_val : ((conjAut n hnA hnAinv).symm a : G) = n⁻¹ * (a : G) * n := by
    rw [ThCyc.conjAut_symm_apply]
  have he2 : ((⟨n⁻¹ * (d : G) * n, heD⟩ : ↥D) : G) ^ 2 =
      ((conjAut n hnA hnAinv).symm a : G) := by
    rw [hsymm_val]
    show (n⁻¹ * (d : G) * n) ^ 2 = n⁻¹ * (a : G) * n
    rw [show (n⁻¹ * (d : G) * n) ^ 2 = n⁻¹ * (d : G) ^ 2 * n by rw [sq, sq]; group, hd]
  have hleft := H.muA_eq_phiD_of_sq_eq W W2 hD h4
    (H.mem_K1_conj W W2 hD h4 hκ hnL hnA) a d hd
  have hright := H.muA_eq_phiD_of_sq_eq W W2 hD h4 hκ
    ((conjAut n hnA hnAinv).symm a) ⟨n⁻¹ * (d : G) * n, heD⟩ he2
  rw [hleft, hright]
  apply Subtype.ext
  rw [ThCyc.conjAut_apply]
  have hφconj : ((phiD H W W2 hD h4 (n * κ * n⁻¹)
        (H.mem_K1_conj W W2 hD h4 hκ hnL hnA) d : ↥A) : G) =
      n * ((phiD H W W2 hD h4 κ hκ ⟨n⁻¹ * (d : G) * n, heD⟩ : ↥A) : G) * n⁻¹ := by
    show (d : G)⁻¹ * ((n * κ * n⁻¹) * (d : G) * (n * κ * n⁻¹)⁻¹) =
      n * ((n⁻¹ * (d : G) * n)⁻¹ * (κ * (n⁻¹ * (d : G) * n) * κ⁻¹)) * n⁻¹
    group
  exact hφconj

section

variable [hAcomm : Fact (∀ a b : ↥A, a * b = b * a)]

local instance : IsMulCommutative ↥A := IsMulCommutative.of_comm (Fact.out)
local instance : CommGroup ↥A := IsMulCommutative.instCommGroup

private theorem ThCyc.mem_range_mu_conj (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {σ : ↥A ≃* ↥A}
    {f : ↥A →* ↥A} (hf : f ∈ (muHom H W W2 hD h4).range) :
    (σ : ↥A →* ↥A).comp (f.comp (σ.symm : ↥A →* ↥A)) ∈
      (muHom H W W2 hD h4).range := by
  obtain ⟨κ, rfl⟩ := hf
  classical
  obtain ⟨n, hnL, hnσ⟩ := W.surj
    (fun a => if h : a ∈ A then ((σ ⟨a, h⟩ : ↥A) : G) else 1)
    (fun a ha => by simp [ha])
    (fun a ha b hb => by
      simp only [ha, hb, mul_mem ha hb, dite_true]
      exact congrArg Subtype.val (σ.map_mul ⟨a, ha⟩ ⟨b, hb⟩))
    (fun a ha b hb hab => by
      simp only [ha, hb, dite_true] at hab
      exact congrArg Subtype.val (σ.injective (Subtype.ext hab)))
  have hnσ' : ∀ a (ha : a ∈ A), n * a * n⁻¹ = ((σ ⟨a, ha⟩ : ↥A) : G) := by
    intro a ha
    have h := hnσ a ha
    simpa only [dif_pos ha] using h
  have hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A := fun a ha => by
    rw [hnσ' a ha]
    exact (σ ⟨a, ha⟩).2
  have hnAinv : ∀ a ∈ A, n⁻¹ * a * n ∈ A := by
    intro a ha
    obtain ⟨b, hb⟩ := σ.surjective ⟨a, ha⟩
    have h := hnσ' b b.2
    rw [show ((σ b : ↥A) : G) = a from congrArg Subtype.val hb] at h
    have hb_eq : n⁻¹ * a * n = (b : G) := by
      calc n⁻¹ * a * n = n⁻¹ * (n * (b : G) * n⁻¹) * n := by rw [← h]
        _ = (b : G) := by group
    rw [hb_eq]
    exact b.2
  have hσ : σ = conjAut n hnA hnAinv := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [ThCyc.conjAut_apply]
    exact (hnσ' a.1 a.2).symm
  have hκ' : n * κ.1 * n⁻¹ ∈ ThCyc.K1 H W W2 hD h4 :=
    H.mem_K1_conj W W2 hD h4 κ.2 hnL hnA
  refine ⟨⟨n * κ.1 * n⁻¹, hκ'⟩, ?_⟩
  apply MonoidHom.ext
  intro a
  rw [hσ]
  change (muHom H W W2 hD h4 ⟨n * κ.1 * n⁻¹, hκ'⟩) a =
    conjAut n hnA hnAinv
      ((muHom H W W2 hD h4 κ) ((conjAut n hnA hnAinv).symm a))
  change muA H W W2 hD h4 (n * κ.1 * n⁻¹) hκ' a =
    conjAut n hnA hnAinv
      (muA H W W2 hD h4 κ.1 κ.2 ((conjAut n hnA hnAinv).symm a))
  exact H.muA_conj_apply W W2 hD h4 κ.2 hnL hnA hnAinv a

end

private theorem ThCyc.thV_phi_eq_sq_of_commutator_mul_b (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {κ : G}
    (hκ : κ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)))
    (h : κ * t * κ⁻¹ * t⁻¹ * b ∈ (centralizer (D : Set G))) {d : G} (hd : d ∈ D) :
    thV t (d⁻¹ * (κ * d * κ⁻¹)) = d ^ 2 := by
  have hbb : b * b = 1 := by rw [← sq]; exact W2.b_sq
  have heK : κ * t * κ⁻¹ * t⁻¹ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    := H.commutator_t_mem_K W W2 hD hκ
  have hbK : b ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) := H.K1_le_K W W2
    hD h4 (H.b_mem_K1 W W2 hD h4 hb)
  have hcK : (κ * t * κ⁻¹ * t⁻¹) * b ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set
    G)) :=
    (centralizer_le_inf_normalizer_centralizer_omega1 hD.comm) h
  set c : G := (κ * t * κ⁻¹ * t⁻¹) * b with hcdef
  have he_eq : κ * t * κ⁻¹ * t⁻¹ = c * b := by
    rw [hcdef]
    calc κ * t * κ⁻¹ * t⁻¹ = (κ * t * κ⁻¹ * t⁻¹) * 1 := by rw [mul_one]
      _ = (κ * t * κ⁻¹ * t⁻¹) * (b * b) := by rw [hbb]
      _ = ((κ * t * κ⁻¹ * t⁻¹) * b) * b := by group
  have hmul := H.conj_D_mul_mul_conj W W2 hD h4 hcK hbK hd
  calc thV t (d⁻¹ * (κ * d * κ⁻¹))
      = d⁻¹ * ((κ * t * κ⁻¹ * t⁻¹) * d * (κ * t * κ⁻¹ * t⁻¹)⁻¹) :=
        (H.phi_commutator W W2 hD h4 hκ hd).symm
    _ = d⁻¹ * ((c * b) * d * (c * b)⁻¹) := by rw [he_eq]
    _ = (d⁻¹ * (c * d * c⁻¹)) * (d⁻¹ * (b * d * b⁻¹)) := hmul
    _ = (d⁻¹ * (c * d * c⁻¹)) * d ^ 2 := by
        rw [ThCyc.phi_b_eq_sq h4 hb hd]
    _ = 1 * d ^ 2 := by rw [ThCyc.phi_centralizer_eq_one h hd]
    _ = d ^ 2 := by rw [one_mul]

theorem ThCyc.mul_inv_mem_K1_of_commutator_mul_b_mem_centralizer (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {κ κ' : G}
    (hκ : κ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)))
    (hκ' : κ' ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)))
    (h1 : κ * t * κ⁻¹ * t⁻¹ * b ∈ (centralizer (D : Set G)))
    (h2 : κ' * t * κ'⁻¹ * t⁻¹ * b ∈ (centralizer (D : Set G))) :
    κ * κ'⁻¹ ∈ ThCyc.K1 H W W2 hD h4 := by
  have hκinv : κ'⁻¹ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :=
    ((normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))).inv_mem hκ'
  have hκκ' : κ * κ'⁻¹ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :=
    ((normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))).mul_mem hκ hκinv
  refine (H.mem_K1_iff W W2 hD h4).2 ⟨hκκ', fun d hd => ?_⟩
  have hφV : d⁻¹ * (κ * d * κ⁻¹) ∈ (omega1 D hD.comm) :=
    H.conj_D_mul_mem_omega1_of_mem_inf W W2 hD h4 hκ d hd
  have hφ'V : d⁻¹ * (κ' * d * κ'⁻¹) ∈ (omega1 D hD.comm) :=
    H.conj_D_mul_mem_omega1_of_mem_inf W W2 hD h4 hκ' d hd
  have hquotV : (d⁻¹ * (κ * d * κ⁻¹)) * (d⁻¹ * (κ' * d * κ'⁻¹))⁻¹ ∈ (omega1 D hD.comm) :=
    ((omega1 D hD.comm)).mul_mem hφV (((omega1 D hD.comm)).inv_mem hφ'V)
  have hκthV := H.thV_phi_eq_sq_of_commutator_mul_b W W2 hD h4 hb hκ h1 hd
  have hκ'thV := H.thV_phi_eq_sq_of_commutator_mul_b W W2 hD h4 hb hκ' h2 hd
  have hthV : thV t ((d⁻¹ * (κ * d * κ⁻¹)) * (d⁻¹ * (κ' * d * κ'⁻¹))⁻¹) = 1 := by
    rw [H.thV_mul W W2 hD hφV (((omega1 D hD.comm)).inv_mem hφ'V), H.thV_inv W W2 hD hφ'V, hκthV,
      hκ'thV,
      mul_inv_cancel]
  have hA : (d⁻¹ * (κ * d * κ⁻¹)) * (d⁻¹ * (κ' * d * κ'⁻¹))⁻¹ ∈ A :=
    (H.thV_eq_one_iff W W2 hD hquotV).1 hthV
  have hφ' : d⁻¹ * (κ'⁻¹ * d * (κ'⁻¹)⁻¹) = (d⁻¹ * (κ' * d * κ'⁻¹))⁻¹ := by
    simpa only [inv_inv] using H.conj_D_mul_inv W W2 hD h4 hκ' hd
  rw [H.conj_D_mul_mul_conj W W2 hD h4 hκ hκinv hd, hφ']
  exact hA

theorem ThCyc.mem_K1_eq_centralizer_or_mul_b (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {κ : G} (hκ : κ ∈ ThCyc.K1 H W W2 hD h4) :
    κ ∈ (centralizer (D : Set G)) ∨ κ * b ∈ (centralizer (D : Set G)) := by
  classical
  haveI hAcomm : Fact (∀ a b : ↥A, a * b = b * a) :=
    ⟨fun a b => Subtype.ext (W.A_comm a.1 a.2 b.1 b.2)⟩
  letI : IsMulCommutative ↥A := IsMulCommutative.of_comm (Fact.out)
  letI : CommGroup ↥A := IsMulCommutative.instCommGroup
  have hsqA : ∀ x : ↥A, x ^ 2 = 1 := fun x => Subtype.ext (W.A_sq x x.2)
  have hcardA : Nat.card ↥A = 16 := W.A_card
  have hconj : ∀ (σ : ↥A ≃* ↥A) {f : ↥A →* ↥A},
      f ∈ (muHom H W W2 hD h4).range →
      (σ : ↥A →* ↥A).comp (f.comp (σ.symm : ↥A →* ↥A)) ∈
        (muHom H W W2 hD h4).range :=
    fun σ f hf => H.mem_range_mu_conj W W2 hD h4 hf
  have hid : MonoidHom.id ↥A ∈ (muHom H W W2 hD h4).range :=
    ⟨⟨b, H.b_mem_K1 W W2 hD h4 hb⟩, H.muHom_b W W2 hD h4 hb⟩
  have hcardW : Nat.card ↥(muHom H W W2 hD h4).range ≤ 2 ^ 10 :=
    (H.card_range_mu_le W W2 hD h4 hb).trans (by norm_num)
  have hcases := CFSG.LinearAlgebra.monoidHom_eq_one_or_id_of_conj_invariant_of_card_le
    hsqA hcardA hconj hid hcardW
  have hrange : (muHom H W W2 hD h4) ⟨κ, hκ⟩ ∈ (muHom H W W2 hD h4).range :=
    ⟨⟨κ, hκ⟩, rfl⟩
  rcases hcases ((muHom H W W2 hD h4) ⟨κ, hκ⟩) hrange with h1 | hid'
  · left
    have hker : (⟨κ, hκ⟩ : ↥(ThCyc.K1 H W W2 hD h4)) ∈
        (muHom H W W2 hD h4).ker := MonoidHom.mem_ker.2 h1
    rw [H.muHom_ker W W2 hD h4] at hker
    exact Subgroup.mem_subgroupOf.1 hker
  · right
    have hbK : b ∈ ThCyc.K1 H W W2 hD h4 := H.b_mem_K1 W W2 hD h4 hb
    have hmem : (⟨κ * b, (ThCyc.K1 H W W2 hD h4).mul_mem hκ hbK⟩ :
        ↥(ThCyc.K1 H W W2 hD h4)) = ⟨κ, hκ⟩ * ⟨b, hbK⟩ := Subtype.ext rfl
    have hμb : (muHom H W W2 hD h4)
        ⟨κ * b, (ThCyc.K1 H W W2 hD h4).mul_mem hκ hbK⟩ = 1 := by
      rw [hmem, map_mul, hid', H.muHom_b W W2 hD h4 hb]
      apply MonoidHom.ext
      intro a
      rw [MonoidHom.mul_apply, MonoidHom.id_apply, MonoidHom.one_apply]
      apply Subtype.ext
      show ((a : ↥A) : G) * ((a : ↥A) : G) = 1
      rw [← sq]
      exact W.A_sq a a.2
    have hker : (⟨κ * b, (ThCyc.K1 H W W2 hD h4).mul_mem hκ hbK⟩ :
        ↥(ThCyc.K1 H W W2 hD h4)) ∈ (muHom H W W2 hD h4).ker :=
      MonoidHom.mem_ker.2 hμb
    rw [H.muHom_ker W W2 hD h4] at hker
    exact Subgroup.mem_subgroupOf.1 hker

theorem ThCyc.mem_K1_iff_mem_centralizer_or_mul_b
    (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {κ : G}
    :
    κ ∈ ThCyc.K1 H W W2 hD h4 ↔ κ ∈ (centralizer (D : Set G)) ∨ κ * b ∈ (centralizer (D : Set G)) :=
      by
  constructor
  · intro hκ
    exact H.mem_K1_eq_centralizer_or_mul_b W W2 hD h4 hb hκ
  · rintro (hC | hCb)
    · exact H.centralizer_le_K1 W W2 hD h4 hC
    · have hbb : b * b = 1 := by rw [← sq]; exact W2.b_sq
      have hκ : κ = (κ * b) * b := by rw [mul_assoc, hbb, mul_one]
      rw [hκ]
      exact (ThCyc.K1 H W W2 hD h4).mul_mem
        (H.centralizer_le_K1 W W2 hD h4 hCb) (H.b_mem_K1 W W2 hD h4 hb)

theorem ThCyc.card_K1_eq_two_mul_card_centralizer (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    Nat.card (ThCyc.K1 H W W2 hD h4) = 2 * Nat.card ((centralizer (D : Set G))) := by
  have hunion : (ThCyc.K1 H W W2 hD h4 : Set G) =
      ((centralizer (D : Set G)) : Set G) ∪ (fun c => c * b) '' ((centralizer (D : Set G)) : Set G)
        := by
    ext κ
    rw [Set.mem_union, Set.mem_image]
    constructor
    · intro hκ
      rcases (H.mem_K1_iff_mem_centralizer_or_mul_b W W2 hD h4 hb).1 hκ with hC | hCb
      · exact Or.inl hC
      · right
        refine ⟨κ * b, hCb, ?_⟩
        have hbb : b * b = 1 := by rw [← sq]; exact W2.b_sq
        rw [mul_assoc, hbb, mul_one]
    · rintro (hC | ⟨c, hc, rfl⟩)
      · exact (H.centralizer_le_K1 W W2 hD h4) hC
      · exact (ThCyc.K1 H W W2 hD h4).mul_mem
          ((H.centralizer_le_K1 W W2 hD h4) hc) (H.b_mem_K1 W W2 hD h4 hb)
  have hdisj : Disjoint ((centralizer (D : Set G)) : Set G) ((fun c => c * b) '' ((centralizer (D :
    Set G)) : Set G)) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨c, hc, rfl⟩
    exact ThCyc.b_not_mem_centralizer_D W W2 hD hb (by
      have hmem : c⁻¹ * (c * b) ∈ (centralizer (D : Set G)) := ((centralizer (D : Set G))).mul_mem
        (((centralizer (D : Set G))).inv_mem hc) hx
      simpa using hmem)
  have h := Set.ncard_union_eq hdisj
  rw [← hunion] at h
  have himg : ((fun c => c * b) '' ((centralizer (D : Set G)) : Set G)).ncard = ((centralizer (D :
    Set G)) : Set G).ncard :=
    Set.ncard_image_of_injective _ (mul_left_injective b)
  rw [himg] at h
  have hK1card : Nat.card (ThCyc.K1 H W W2 hD h4) =
      (ThCyc.K1 H W W2 hD h4 : Set G).ncard := Nat.card_coe_set_eq _
  have hCcard : Nat.card ((centralizer (D : Set G))) = ((centralizer (D : Set G)) : Set G).ncard :=
    Nat.card_coe_set_eq _
  rw [← hK1card, ← hCcard] at h
  omega

theorem ThCyc.commutator_t_mul_b_mem_centralizer_of_not_mem_K1 (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {e : G}
    (he : e ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)))
    (he1 : e ∉ ThCyc.K1 H W W2 hD h4) : e * t * e⁻¹ * t⁻¹ * b ∈ (centralizer (D : Set G)) := by
  have hK1 := H.commutator_t_mem_K1 W W2 hD h4 he
  rcases (H.mem_K1_iff_mem_centralizer_or_mul_b W W2 hD h4 hb).1 hK1 with hC | hCb
  · exact absurd ((H.mem_K1_iff_commutator_mem_centralizer W W2 hD h4 he).2 hC) he1
  · exact hCb

theorem ThCyc.K_eq_K1_union_mul_of_mem (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {e : G}
    (he : e ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)))
    (he1 : e ∉ ThCyc.K1 H W W2 hD h4) :
    ((normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) : Set G) = (ThCyc.K1 H W W2
      hD h4 : Set G) ∪
      (fun k => k * e) '' (ThCyc.K1 H W W2 hD h4 : Set G) := by
  have hcomm_e := H.commutator_t_mul_b_mem_centralizer_of_not_mem_K1 W W2 hD h4 hb he he1
  ext κ
  rw [Set.mem_union, Set.mem_image]
  constructor
  · intro hκ
    by_cases hκ1 : κ ∈ ThCyc.K1 H W W2 hD h4
    · exact Or.inl hκ1
    · right
      have hκK1 := H.commutator_t_mem_K1 W W2 hD h4 hκ
      rcases (H.mem_K1_iff_mem_centralizer_or_mul_b W W2 hD h4 hb).1 hκK1 with hC | hCb
      · exact absurd ((H.mem_K1_iff_commutator_mem_centralizer W W2 hD h4 hκ).2 hC) hκ1
      · have hrel := H.mul_inv_mem_K1_of_commutator_mul_b_mem_centralizer W W2 hD h4 hb
            hκ he hCb hcomm_e
        refine ⟨κ * e⁻¹, hrel, ?_⟩
        rw [mul_assoc, inv_mul_cancel, mul_one]
  · rintro (hκ1 | ⟨k, hk, rfl⟩)
    · exact H.K1_le_K W W2 hD h4 hκ1
    · exact ((normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))).mul_mem (H.K1_le_K W
      W2 hD h4 hk) he

theorem ThCyc.card_K_le_two_mul_card_K1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    Nat.card ↥((normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))) ≤ 2 * Nat.card
      (ThCyc.K1 H W W2 hD h4) := by
  by_cases hle :
      (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) ≤
        ThCyc.K1 H W W2 hD h4
  · have heq :
        (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) =
          ThCyc.K1 H W W2 hD h4 :=
      le_antisymm hle (H.K1_le_K W W2 hD h4)
    rw [heq]
    omega
  · obtain ⟨e, heK, heK1⟩ := Set.not_subset.1 hle
    have hunion := H.K_eq_K1_union_mul_of_mem W W2 hD h4 hb heK heK1
    have hdisj : Disjoint (ThCyc.K1 H W W2 hD h4 : Set G)
        ((fun k => k * e) '' (ThCyc.K1 H W W2 hD h4 : Set G)) := by
      rw [Set.disjoint_left]
      rintro x hx ⟨k, hk, rfl⟩
      exact heK1 (by
        have hmem : k⁻¹ * (k * e) ∈ ThCyc.K1 H W W2 hD h4 :=
          (ThCyc.K1 H W W2 hD h4).mul_mem ((ThCyc.K1 H W W2 hD h4).inv_mem hk) hx
        simpa using hmem)
    have himg : ((fun k => k * e) '' (ThCyc.K1 H W W2 hD h4 : Set G)).ncard =
        (ThCyc.K1 H W W2 hD h4 : Set G).ncard :=
      Set.ncard_image_of_injective _ (mul_left_injective e)
    have h := Set.ncard_union_eq hdisj
    rw [← hunion] at h
    rw [himg] at h
    have hKcard : Nat.card ↥((normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))) =
      ((normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) : Set G).ncard :=
      Nat.card_coe_set_eq _
    have hK1card : Nat.card (ThCyc.K1 H W W2 hD h4) =
        (ThCyc.K1 H W W2 hD h4 : Set G).ncard := Nat.card_coe_set_eq _
    rw [← hKcard, ← hK1card] at h
    omega

theorem ThCyc.card_K_le_four_mul_card_centralizer (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    Nat.card ↥((normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))) ≤ 4 * Nat.card
      ((centralizer (D : Set G))) := by
  have h1 := H.card_K_le_two_mul_card_K1 W W2 hD h4 hb
  have h2 := H.card_K1_eq_two_mul_card_centralizer W W2 hD h4 hb
  rw [h2] at h1
  omega

theorem ThCyc.mem_centralizer_or_mul_b_or_commutator_mul_b_mem_centralizer (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    ∀ κ ∈ (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)), κ ∈ (centralizer (D :
      Set G)) ∨ κ * b ∈ (centralizer (D : Set G)) ∨ (κ * t * κ⁻¹ * t⁻¹) * b ∈ (centralizer (D : Set
      G)) := by
  intro κ hκ
  have hκ1 := H.commutator_t_mem_K1 W W2 hD h4 hκ
  rcases (H.mem_K1_iff_mem_centralizer_or_mul_b W W2 hD h4 hb).1 hκ1 with hC | hCb
  · have hκK1 : κ ∈ ThCyc.K1 H W W2 hD h4 :=
      (H.mem_K1_iff_commutator_mem_centralizer W W2 hD h4 hκ).2 hC
    rcases (H.mem_K1_iff_mem_centralizer_or_mul_b W W2 hD h4 hb).1 hκK1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hCb)

end CFSG.EvenSporadicStandard.ThStd
