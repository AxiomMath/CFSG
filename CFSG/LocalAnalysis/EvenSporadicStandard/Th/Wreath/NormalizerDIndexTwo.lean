module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.CentralizerANormalizerD

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

private theorem conj_mem_omega1_of_mem_normalizer_D' {G : Type} [Group G] {D : Subgroup G}
    (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {m : G} (hmD : m ∈ normalizer (D : Set G)) {v : G}
    (hv : v ∈ omega1 D hDc) : m * v * m⁻¹ ∈ omega1 D hDc := by
  refine mem_omega1_iff.2 ⟨(mem_normalizer_iff.1 hmD v).1 hv.1, ?_⟩
  calc (m * v * m⁻¹) ^ 2 = m * v ^ 2 * m⁻¹ := by rw [sq, sq]; group
    _ = 1 := by rw [hv.2]; group

theorem ThCyc.inf_centralizer_omega1_eq_of_mem_M0 {G : Type} [Group G] {A Aa D : Subgroup G} {t : G}
    (hD : DHyp A Aa t D) {m n : G} (hact : ∀ v ∈ omega1 D hD.comm, m * v * m⁻¹ = n * v * n⁻¹) :
    omega1 D hD.comm ⊓ centralizer ({m} : Set G) =
      omega1 D hD.comm ⊓ centralizer ({n} : Set G) := by
  have hiff : ∀ v ∈ omega1 D hD.comm,
      v ∈ centralizer ({m} : Set G) ↔ v ∈ centralizer ({n} : Set G) := by
    intro v hv
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : m * v * m⁻¹ = v := mul_inv_eq_iff_eq_mul.mpr h.symm
      have h'' : n * v * n⁻¹ = v := by rw [← hact v hv, h']
      exact (mul_inv_eq_iff_eq_mul.mp h'').symm
    · intro h
      have h' : n * v * n⁻¹ = v := mul_inv_eq_iff_eq_mul.mpr h.symm
      have h'' : m * v * m⁻¹ = v := by rw [hact v hv, h']
      exact (mul_inv_eq_iff_eq_mul.mp h'').symm
  ext v
  constructor
  · rintro ⟨hv, hc⟩
    exact ⟨hv, (hiff v hv).1 hc⟩
  · rintro ⟨hv, hc⟩
    exact ⟨hv, (hiff v hv).2 hc⟩

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

private theorem mem_normalizer_omega1_of_witness' {D : Subgroup G}
    (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {m n : G} (hmD : m ∈ normalizer (D : Set G))
    (hact : ∀ v ∈ omega1 D hDc, m * v * m⁻¹ = n * v * n⁻¹) :
    n ∈ normalizer (omega1 D hDc : Set G) := by
  have hinv : ∀ w ∈ omega1 D hDc, n⁻¹ * w * n ∈ omega1 D hDc := by
    intro w hw
    have hw' : m⁻¹ * w * m ∈ omega1 D hDc := by
      simpa using
        conj_mem_omega1_of_mem_normalizer_D' hDc ((normalizer (D : Set G)).inv_mem hmD) hw
    have h : n * (m⁻¹ * w * m) * n⁻¹ = w := by rw [← hact _ hw']; group
    have heq : n⁻¹ * w * n = m⁻¹ * w * m := by
      calc n⁻¹ * w * n = n⁻¹ * (n * (m⁻¹ * w * m) * n⁻¹) * n := by rw [h]
        _ = m⁻¹ * w * m := by group
    rw [heq]
    exact hw'
  exact mem_normalizer_iff.2 (mem_iff_conj_of_conj_le (omega1 D hDc) (g := n) hinv)

@[expose] def M0 (L A D : Subgroup G) (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) : Subgroup G where
  carrier := {m | m ∈ normalizer (D : Set G) ∧ ∃ n ∈ L ⊓ normalizer (A : Set G),
    ∀ v ∈ omega1 D hDc, m * v * m⁻¹ = n * v * n⁻¹}
  one_mem' := ⟨one_mem _, 1, ⟨one_mem _, one_mem _⟩, by intro v _; simp⟩
  mul_mem' := by
    rintro m₁ m₂ ⟨hm₁D, n₁, hn₁, hact₁⟩ ⟨hm₂D, n₂, hn₂, hact₂⟩
    have hn₂V : n₂ ∈ normalizer (omega1 D hDc : Set G) :=
      mem_normalizer_omega1_of_witness' hDc hm₂D hact₂
    refine ⟨(normalizer (D : Set G)).mul_mem hm₁D hm₂D, n₁ * n₂,
      ⟨L.mul_mem hn₁.1 hn₂.1, (normalizer (A : Set G)).mul_mem hn₁.2 hn₂.2⟩, ?_⟩
    intro v hv
    have hv₂ : n₂ * v * n₂⁻¹ ∈ omega1 D hDc := (mem_normalizer_iff.1 hn₂V v).1 hv
    calc (m₁ * m₂) * v * (m₁ * m₂)⁻¹ = m₁ * (m₂ * v * m₂⁻¹) * m₁⁻¹ := by group
      _ = m₁ * (n₂ * v * n₂⁻¹) * m₁⁻¹ := by rw [hact₂ v hv]
      _ = n₁ * (n₂ * v * n₂⁻¹) * n₁⁻¹ := hact₁ _ hv₂
      _ = (n₁ * n₂) * v * (n₁ * n₂)⁻¹ := by group
  inv_mem' := by
    rintro m ⟨hmD, n, hn, hact⟩
    refine ⟨(normalizer (D : Set G)).inv_mem hmD, n⁻¹,
      ⟨L.inv_mem hn.1, (normalizer (A : Set G)).inv_mem hn.2⟩, ?_⟩
    intro v hv
    have hv' : m⁻¹ * v * m ∈ omega1 D hDc := by
      simpa using
        conj_mem_omega1_of_mem_normalizer_D' hDc ((normalizer (D : Set G)).inv_mem hmD) hv
    have h := hact _ hv'
    have h2 : m * (m⁻¹ * v * m) * m⁻¹ = v := by group
    rw [h2] at h
    simp only [inv_inv]
    calc m⁻¹ * v * m = n⁻¹ * (n * (m⁻¹ * v * m) * n⁻¹) * n := by group
      _ = n⁻¹ * v * n := by rw [← h]

private theorem ThCyc.t_mem_normalizer_D (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) : t ∈ normalizer (D : Set G) :=
  le_normalizer_of_conj_mem hD.norm (H.t_mem_normalizer W W2 hD)

private theorem ThCyc.mem_inf_normalizer_D_of_mem_inf_normalizer_A (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {n : G}
    (hn : n ∈ L ⊓ normalizer (A : Set G)) : n ∈ L ⊓ normalizer (D : Set G) := by
  rw [H.inf_normalizer_D_eq W W2 hD]
  exact hn

theorem ThCyc.t_not_mem_M0 (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    t ∉ M0 L A D hD.comm := by
  intro ht
  obtain ⟨-, n, ⟨hnL, -⟩, hact⟩ := ht
  have hA_le_L : A ≤ L := fun a ha => W.S_le ((W.mem_A_iff a).1 ha).1
  have hnB : n ∈ B := (W.mem_B_iff n hnL).2 fun a ha => by
    have hta : t * a * t⁻¹ = a := by
      calc t * a * t⁻¹ = (a * t) * t⁻¹ := by rw [H.comm_of_mem_L (hA_le_L ha)]
        _ = a := by group
    have hna : n * a * n⁻¹ = a := by
      rw [← hact a (H.A_le_omega1 W W2 hD ha), hta]
    exact mul_inv_eq_iff_eq_mul.mp hna
  have htV : ∀ v ∈ omega1 D hD.comm, t * v * t⁻¹ = v := by
    intro v hv
    rw [hact v hv, H.comm_omega1_of_mem_B W W2 hD hb hnB hv]
  have hVle : omega1 D hD.comm ≤ centralizer ({t} : Set G) := by
    intro v hv
    exact mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.mp (htV v hv)).symm
  have hVeq : omega1 D hD.comm = A := by
    refine le_antisymm ?_ (H.A_le_omega1 W W2 hD)
    intro v hv
    have h : v ∈ omega1 D hD.comm ⊓ centralizer ({t} : Set G) := ⟨hv, hVle hv⟩
    rwa [H.omega1_inf_centralizer_t W W2 hD] at h
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  have hcard : Nat.card (omega1 D hD.comm) = Nat.card A := by rw [hVeq]
  rw [H.card_omega1 W W2 hD hsq, W.A_card] at hcard
  norm_num at hcard

theorem ThCyc.mem_M0_or_inv_t_mul_mem_M0 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {m : G} (hm : m ∈ normalizer (D : Set G)) :
    m ∈ M0 L A D hD.comm ∨ t⁻¹ * m ∈ M0 L A D hD.comm := by
  have hmA : m ∈ normalizer (A : Set G) := H.normalizer_D_le_normalizer_A W W2 hD h4 hm
  have hmA' : ∀ a ∈ A, m * a * m⁻¹ ∈ A := fun a ha => (mem_normalizer_iff.1 hmA a).1 ha
  obtain ⟨n, hnL, hn⟩ := W.surj (fun a => m * a * m⁻¹) hmA'
    (fun a _ b _ => by group)
    (fun a ha b hb hab => mul_left_cancel (mul_right_cancel hab))
  have hnAinv : ∀ a ∈ A, n⁻¹ * a * n ∈ A := by
    intro a ha
    have ha' : m⁻¹ * a * m ∈ A := by
      simpa using (mem_normalizer_iff.1 ((normalizer (A : Set G)).inv_mem hmA) a).1 ha
    have h : n * (m⁻¹ * a * m) * n⁻¹ = a := by rw [hn _ ha']; group
    have heq : n⁻¹ * a * n = m⁻¹ * a * m := by
      calc n⁻¹ * a * n = n⁻¹ * (n * (m⁻¹ * a * m) * n⁻¹) * n := by rw [h]
        _ = m⁻¹ * a * m := by group
    rw [heq]
    exact ha'
  have hnN : n ∈ normalizer (A : Set G) :=
    mem_normalizer_iff.2 (mem_iff_conj_of_conj_le A (g := n) hnAinv)
  have hnD : n ∈ normalizer (D : Set G) :=
    (H.mem_inf_normalizer_D_of_mem_inf_normalizer_A W W2 hD ⟨hnL, hnN⟩).2
  have hqD : n⁻¹ * m ∈ normalizer (D : Set G) :=
    (normalizer (D : Set G)).mul_mem ((normalizer (D : Set G)).inv_mem hnD) hm
  have hqA : ∀ a ∈ A, (n⁻¹ * m) * a * (n⁻¹ * m)⁻¹ = a := by
    intro a ha
    calc (n⁻¹ * m) * a * (n⁻¹ * m)⁻¹ = n⁻¹ * (m * a * m⁻¹) * n := by group
      _ = n⁻¹ * (n * a * n⁻¹) * n := by rw [← hn a ha]
      _ = a := by group
  rcases H.conj_omega1_eq_or_of_mem_normalizer_D W W2 hD h4 hb hqD hqA with htriv | ht
  · left
    refine ⟨hm, n, ⟨hnL, hnN⟩, ?_⟩
    intro v hv
    calc m * v * m⁻¹ = n * (n⁻¹ * m * v * (n⁻¹ * m)⁻¹) * n⁻¹ := by group
      _ = n * v * n⁻¹ := by rw [htriv v hv]
  · right
    refine ⟨?_, n, ⟨hnL, hnN⟩, ?_⟩
    · exact (normalizer (D : Set G)).mul_mem
        ((normalizer (D : Set G)).inv_mem (H.t_mem_normalizer_D W W2 hD)) hm
    intro v hv
    have hqv : n⁻¹ * m * v * (n⁻¹ * m)⁻¹ = t * v * t⁻¹ := ht v hv
    have hnt : n * t = t * n := (H.comm_of_mem_L hnL).symm
    calc (t⁻¹ * m) * v * (t⁻¹ * m)⁻¹
        = t⁻¹ * n * ((n⁻¹ * m) * v * (n⁻¹ * m)⁻¹) * n⁻¹ * t := by group
      _ = t⁻¹ * n * (t * v * t⁻¹) * n⁻¹ * t := by rw [hqv]
      _ = (t⁻¹ * n) * (t * v * t⁻¹) * (n⁻¹ * t) := by group
      _ = (n * t⁻¹) * (t * v * t⁻¹) * (t * n⁻¹) := by
          have h1 : t⁻¹ * n = n * t⁻¹ := by
            calc t⁻¹ * n = t⁻¹ * (n * t) * t⁻¹ := by group
              _ = t⁻¹ * (t * n) * t⁻¹ := by rw [hnt]
              _ = n * t⁻¹ := by group
          have h2 : n⁻¹ * t = t * n⁻¹ := by
            calc n⁻¹ * t = n⁻¹ * (t * n) * n⁻¹ := by group
              _ = n⁻¹ * (n * t) * n⁻¹ := by rw [← hnt]
              _ = t * n⁻¹ := by group
          rw [h1, h2]
      _ = n * v * n⁻¹ := by group

private theorem ThCyc.conj_action_eq_of_mem_C (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {p n : G} (hpD : p ∈ normalizer (D : Set G))
    (hpA : ∀ a ∈ A, p * a * p⁻¹ = a) (hnL : n ∈ L)
    (hnV : n ∈ normalizer (omega1 D hD.comm : Set G)) :
    ∀ w ∈ omega1 D hD.comm,
      (p * n * p⁻¹) * w * (p * n * p⁻¹)⁻¹ = n * w * n⁻¹ := by
  have hpV' : p⁻¹ ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).inv_mem
      (ThCyc.normalizer_D_le_normalizer_omega1 hD hpD)
  have hnt : n * t = t * n := (H.comm_of_mem_L hnL).symm
  have ht2 : t * t = 1 := by rw [← sq]; exact H.sq_t
  rcases H.conj_omega1_eq_or_of_mem_normalizer_D W W2 hD h4 hb hpD hpA with htriv | ht
  · intro w hw
    have hpw : p⁻¹ * w * p = w := by
      have h := htriv w hw
      calc p⁻¹ * w * p = p⁻¹ * (p * w * p⁻¹) * p := by rw [h]
        _ = w := by group
    calc (p * n * p⁻¹) * w * (p * n * p⁻¹)⁻¹
        = p * (n * (p⁻¹ * w * p) * n⁻¹) * p⁻¹ := by group
      _ = p * (n * w * n⁻¹) * p⁻¹ := by rw [hpw]
      _ = n * w * n⁻¹ := htriv (n * w * n⁻¹) ((mem_normalizer_iff.1 hnV w).1 hw)
  · intro w hw
    have hpwV : p⁻¹ * w * p ∈ omega1 D hD.comm := by
      simpa using (mem_normalizer_iff.1 hpV' w).1 hw
    have h1 : p⁻¹ * w * p = t * w * t⁻¹ := by
      have h := ht (p⁻¹ * w * p) hpwV
      have h2 : p * (p⁻¹ * w * p) * p⁻¹ = w := by group
      rw [h2] at h
      have h3 : t * w * t⁻¹ = p⁻¹ * w * p := by
        conv_lhs => rw [h]
        rw [show t * (t * (p⁻¹ * w * p) * t⁻¹) * t⁻¹
              = (t * t) * (p⁻¹ * w * p) * (t⁻¹ * t⁻¹) from by group,
          ht2, show t⁻¹ * t⁻¹ = 1 by rw [← mul_inv_rev, ht2, inv_one],
          one_mul, mul_one]
      exact h3.symm
    have hntw : n * (t * w * t⁻¹) * n⁻¹ = t * (n * w * n⁻¹) * t⁻¹ := by
      calc n * (t * w * t⁻¹) * n⁻¹ = (n * t) * w * (n * t)⁻¹ := by group
        _ = (t * n) * w * (t * n)⁻¹ := by rw [hnt]
        _ = t * (n * w * n⁻¹) * t⁻¹ := by group
    calc (p * n * p⁻¹) * w * (p * n * p⁻¹)⁻¹
        = p * (n * (p⁻¹ * w * p) * n⁻¹) * p⁻¹ := by group
      _ = p * (n * (t * w * t⁻¹) * n⁻¹) * p⁻¹ := by rw [h1]
      _ = p * (t * (n * w * n⁻¹) * t⁻¹) * p⁻¹ := by rw [hntw]
      _ = t * (t * (n * w * n⁻¹) * t⁻¹) * t⁻¹ := by
          rw [ht (t * (n * w * n⁻¹) * t⁻¹)
            (H.t_conj_mem_omega1 W W2 hD ((mem_normalizer_iff.1 hnV w).1 hw))]
      _ = n * w * n⁻¹ := by
          rw [show t * (t * (n * w * n⁻¹) * t⁻¹) * t⁻¹
                = (t * t) * (n * w * n⁻¹) * (t⁻¹ * t⁻¹) from by group,
            ht2, show t⁻¹ * t⁻¹ = 1 by rw [← mul_inv_rev, ht2, inv_one],
            one_mul, mul_one]

theorem ThCyc.conj_mem_M0 (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {x : G}
    (hx : x ∈ normalizer (D : Set G)) {q : G} (hq : q ∈ M0 L A D hD.comm) :
    x * q * x⁻¹ ∈ M0 L A D hD.comm := by
  obtain ⟨hqD, n, ⟨hnL, hnA⟩, hact⟩ := hq
  have hxA : x ∈ normalizer (A : Set G) := H.normalizer_D_le_normalizer_A W W2 hD h4 hx
  have hxA' : ∀ a ∈ A, x * a * x⁻¹ ∈ A := fun a ha => (mem_normalizer_iff.1 hxA a).1 ha
  obtain ⟨l, hlL, hl⟩ := W.surj (fun a => x * a * x⁻¹) hxA'
    (fun a _ b _ => by group)
    (fun a ha b hb hab => mul_left_cancel (mul_right_cancel hab))
  have hlA : ∀ a ∈ A, l * a * l⁻¹ ∈ A := fun a ha => by rw [hl a ha]; exact hxA' a ha
  have hlAinv : ∀ a ∈ A, l⁻¹ * a * l ∈ A := by
    intro a ha
    have ha' : x⁻¹ * a * x ∈ A := by
      simpa using (mem_normalizer_iff.1 ((normalizer (A : Set G)).inv_mem hxA) a).1 ha
    have h : l * (x⁻¹ * a * x) * l⁻¹ = a := by rw [hl _ ha']; group
    have heq : l⁻¹ * a * l = x⁻¹ * a * x := by
      calc l⁻¹ * a * l = l⁻¹ * (l * (x⁻¹ * a * x) * l⁻¹) * l := by rw [h]
        _ = x⁻¹ * a * x := by group
    rw [heq]
    exact ha'
  have hlN : l ∈ normalizer (A : Set G) :=
    mem_normalizer_iff.2 (mem_iff_conj_of_conj_le A (g := l) hlAinv)
  have hlD : l ∈ normalizer (D : Set G) :=
    (H.mem_inf_normalizer_D_of_mem_inf_normalizer_A W W2 hD ⟨hlL, hlN⟩).2
  have hpD : l⁻¹ * x ∈ normalizer (D : Set G) :=
    (normalizer (D : Set G)).mul_mem ((normalizer (D : Set G)).inv_mem hlD) hx
  have hpA : ∀ a ∈ A, (l⁻¹ * x) * a * (l⁻¹ * x)⁻¹ = a := by
    intro a ha
    calc (l⁻¹ * x) * a * (l⁻¹ * x)⁻¹ = l⁻¹ * (x * a * x⁻¹) * l := by group
      _ = l⁻¹ * (l * a * l⁻¹) * l := by rw [← hl a ha]
      _ = a := by group
  have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) :=
    mem_normalizer_omega1_of_witness' hD.comm hqD hact
  refine ⟨(normalizer (D : Set G)).mul_mem
      ((normalizer (D : Set G)).mul_mem hx hqD) ((normalizer (D : Set G)).inv_mem hx),
    l * n * l⁻¹, ⟨L.mul_mem (L.mul_mem hlL hnL) (L.inv_mem hlL),
      (normalizer (A : Set G)).mul_mem ((normalizer (A : Set G)).mul_mem hlN hnA)
        ((normalizer (A : Set G)).inv_mem hlN)⟩, ?_⟩
  intro v hv
  have hw : l⁻¹ * v * l ∈ omega1 D hD.comm := by
    simpa using
      conj_mem_omega1_of_mem_normalizer_D' hD.comm ((normalizer (D : Set G)).inv_mem hlD) hv
  have hv'' : (l⁻¹ * x)⁻¹ * (l⁻¹ * v * l) * (l⁻¹ * x) ∈ omega1 D hD.comm := by
    simpa using
      conj_mem_omega1_of_mem_normalizer_D' hD.comm ((normalizer (D : Set G)).inv_mem hpD) hw
  have hqact : ((l⁻¹ * x) * q * (l⁻¹ * x)⁻¹) * (l⁻¹ * v * l) *
        ((l⁻¹ * x) * q * (l⁻¹ * x)⁻¹)⁻¹
      = ((l⁻¹ * x) * n * (l⁻¹ * x)⁻¹) * (l⁻¹ * v * l) *
        ((l⁻¹ * x) * n * (l⁻¹ * x)⁻¹)⁻¹ := by
    calc ((l⁻¹ * x) * q * (l⁻¹ * x)⁻¹) * (l⁻¹ * v * l) *
          ((l⁻¹ * x) * q * (l⁻¹ * x)⁻¹)⁻¹
        = (l⁻¹ * x) * (q * ((l⁻¹ * x)⁻¹ * (l⁻¹ * v * l) * (l⁻¹ * x)) * q⁻¹) *
            (l⁻¹ * x)⁻¹ := by group
      _ = (l⁻¹ * x) * (n * ((l⁻¹ * x)⁻¹ * (l⁻¹ * v * l) * (l⁻¹ * x)) * n⁻¹) *
            (l⁻¹ * x)⁻¹ := by rw [hact _ hv'']
      _ = ((l⁻¹ * x) * n * (l⁻¹ * x)⁻¹) * (l⁻¹ * v * l) *
            ((l⁻¹ * x) * n * (l⁻¹ * x)⁻¹)⁻¹ := by group
  calc (x * q * x⁻¹) * v * (x * q * x⁻¹)⁻¹
      = l * (((l⁻¹ * x) * q * (l⁻¹ * x)⁻¹) * (l⁻¹ * v * l) *
          ((l⁻¹ * x) * q * (l⁻¹ * x)⁻¹)⁻¹) * l⁻¹ := by group
    _ = l * (((l⁻¹ * x) * n * (l⁻¹ * x)⁻¹) * (l⁻¹ * v * l) *
          ((l⁻¹ * x) * n * (l⁻¹ * x)⁻¹)⁻¹) * l⁻¹ := by rw [hqact]
    _ = l * (n * (l⁻¹ * v * l) * n⁻¹) * l⁻¹ := by
        rw [H.conj_action_eq_of_mem_C W W2 hD h4 hb hpD hpA hnL hnV (l⁻¹ * v * l) hw]
    _ = (l * n * l⁻¹) * v * (l * n * l⁻¹)⁻¹ := by group

theorem ThCyc.centralizes_omega1_of_mem_M0 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {m : G}
    (hm : m ∈ M0 L A D hD.comm) (hmA : ∀ a ∈ A, m * a * m⁻¹ = a) :
    ∀ v ∈ omega1 D hD.comm, m * v * m⁻¹ = v := by
  obtain ⟨-, n, ⟨hnL, -⟩, hact⟩ := hm
  have hnB : n ∈ B := (W.mem_B_iff n hnL).2 fun a ha => by
    have hna : n * a * n⁻¹ = a := by rw [← hact a (H.A_le_omega1 W W2 hD ha), hmA a ha]
    exact mul_inv_eq_iff_eq_mul.mp hna
  intro v hv
  rw [hact v hv, H.comm_omega1_of_mem_B W W2 hD hb hnB hv]

theorem ThCyc.M0_eq_sup_centralizer_omega1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) : M0 L A D hD.comm =
      (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) ⊔
        (L ⊓ normalizer (A : Set G)) := by
  refine le_antisymm ?_ ?_
  · intro m hm
    obtain ⟨hmD, n, hn, hact⟩ := hm
    have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) :=
      mem_normalizer_omega1_of_witness' hD.comm hmD hact
    have hnD : n ∈ normalizer (D : Set G) :=
      (H.mem_inf_normalizer_D_of_mem_inf_normalizer_A W W2 hD hn).2
    have hmn : m * n⁻¹ ∈
        normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) := by
      refine ⟨(normalizer (D : Set G)).mul_mem hmD ((normalizer (D : Set G)).inv_mem hnD), ?_⟩
      refine mem_centralizer_iff.2 fun v hv => ?_
      have hv' : n⁻¹ * v * n ∈ omega1 D hD.comm := by
        simpa using (mem_normalizer_iff.1 ((normalizer _).inv_mem hnV) v).1 hv
      have h1 : m * (n⁻¹ * v * n) * m⁻¹ = n * (n⁻¹ * v * n) * n⁻¹ := hact _ hv'
      have h2 : n * (n⁻¹ * v * n) * n⁻¹ = v := by group
      have h3 : (m * n⁻¹) * v * (m * n⁻¹)⁻¹ = v := by
        calc (m * n⁻¹) * v * (m * n⁻¹)⁻¹ = m * (n⁻¹ * v * n) * m⁻¹ := by group
          _ = v := by rw [h1, h2]
      exact (mul_inv_eq_iff_eq_mul.mp h3).symm
    have he : m = (m * n⁻¹) * n := by group
    rw [he]
    exact mul_mem_sup hmn hn
  · refine sup_le ?_ ?_
    · rintro m ⟨hmD, hmV⟩
      refine ⟨hmD, 1, ⟨one_mem _, one_mem _⟩, fun v hv => ?_⟩
      show m * v * m⁻¹ = 1 * v * 1⁻¹
      rw [one_mul, inv_one, mul_one]
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.1 hmV v hv).symm
    · intro n hn
      exact ⟨(H.mem_inf_normalizer_D_of_mem_inf_normalizer_A W W2 hD hn).2, n, hn,
        fun v _ => rfl⟩

theorem ThCyc.conj_mem_inf_M0 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {T : Subgroup G} (hT : T ≤ normalizer (D : Set G)) :
    ∀ x ∈ T, ∀ q ∈ T ⊓ M0 L A D hD.comm, x * q * x⁻¹ ∈ T ⊓ M0 L A D hD.comm := by
  intro x hx q hq
  exact ⟨T.mul_mem (T.mul_mem hx hq.1) (T.inv_mem hx),
    H.conj_mem_M0 W W2 hD h4 hb (hT hx) hq.2⟩

theorem ThCyc.exists_zpow_inv_mul_mem_inf_M0 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {T : Subgroup G} (hT : T ≤ normalizer (D : Set G))
    (htT : t ∈ T) : ∃ b ∈ T, ∀ x ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * x ∈ T ⊓ M0 L A D hD.comm := by
  refine ⟨t, htT, fun x hx => ?_⟩
  rcases H.mem_M0_or_inv_t_mul_mem_M0 W W2 hD h4 hb (hT hx) with hxM | hxM
  · exact ⟨0, by simpa using ⟨hx, hxM⟩⟩
  · refine ⟨1, ?_⟩
    have hxT : t⁻¹ * x ∈ T := T.mul_mem (T.inv_mem htT) hx
    simpa using ⟨hxT, hxM⟩

theorem ThCyc.t_not_mem_inf_M0 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {T : Subgroup G} : t ∉ T ⊓ M0 L A D hD.comm :=
  fun h => H.t_not_mem_M0 W W2 hD h4 hb h.2

theorem ThCyc.relIndex_M0_eq_two (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    (M0 L A D hD.comm).relIndex (normalizer (D : Set G)) = 2 := by
  refine Subgroup.relIndex_eq_two_iff_exists_notMem_and'.2
    ⟨t⁻¹, (normalizer (D : Set G)).inv_mem (H.t_mem_normalizer_D W W2 hD), ?_, ?_⟩
  · intro h
    exact H.t_not_mem_M0 W W2 hD h4 hb (by
      have := (M0 L A D hD.comm).inv_mem h
      simpa using this)
  · intro x hx
    rcases H.mem_M0_or_inv_t_mul_mem_M0 W W2 hD h4 hb hx with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem ThCyc.exists_mem_inf_normalizer_conj_eq_of_mem_M0 (hD : DHyp A Aa t D) {m : G}
    (hm : m ∈ M0 L A D hD.comm) : ∃ n ∈ L ⊓ normalizer (A : Set G),
      ∀ v ∈ omega1 D hD.comm, m * v * m⁻¹ = n * v * n⁻¹ :=
  hm.2

theorem ThCyc.inf_centralizer_A_eq_of_mem_M0 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {m n : G}
    (hact : ∀ v ∈ omega1 D hD.comm, m * v * m⁻¹ = n * v * n⁻¹) :
    A ⊓ centralizer ({m} : Set G) = A ⊓ centralizer ({n} : Set G) := by
  have h := inf_centralizer_omega1_eq_of_mem_M0 hD hact
  ext a
  constructor
  · rintro ⟨haA, hc⟩
    refine ⟨haA, ?_⟩
    have hc' : a ∈ omega1 D hD.comm ⊓ centralizer ({m} : Set G) :=
      ⟨H.A_le_omega1 W W2 hD haA, hc⟩
    rw [h] at hc'
    exact hc'.2
  · rintro ⟨haA, hc⟩
    refine ⟨haA, ?_⟩
    have hc' : a ∈ omega1 D hD.comm ⊓ centralizer ({n} : Set G) :=
      ⟨H.A_le_omega1 W W2 hD haA, hc⟩
    rw [← h] at hc'
    exact hc'.2

theorem ThCyc.exists_mem_inf_normalizer_centralizer_eq_of_mem_M0 (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {m : G}
    (hm : m ∈ M0 L A D hD.comm) : ∃ n ∈ L ⊓ normalizer (A : Set G),
      (∀ v ∈ omega1 D hD.comm, m * v * m⁻¹ = n * v * n⁻¹) ∧
      omega1 D hD.comm ⊓ centralizer ({m} : Set G)
        = omega1 D hD.comm ⊓ centralizer ({n} : Set G) ∧
      A ⊓ centralizer ({m} : Set G) = A ⊓ centralizer ({n} : Set G) := by
  obtain ⟨n, hn, hact⟩ := ThCyc.exists_mem_inf_normalizer_conj_eq_of_mem_M0 hD hm
  exact ⟨n, hn, hact, inf_centralizer_omega1_eq_of_mem_M0 hD hact,
    H.inf_centralizer_A_eq_of_mem_M0 W W2 hD hact⟩

end CFSG.EvenSporadicStandard.ThStd
