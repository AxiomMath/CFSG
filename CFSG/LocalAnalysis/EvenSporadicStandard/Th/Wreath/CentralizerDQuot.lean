module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SecondLayerVMod

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

theorem centralizer_le_inf_normalizer_centralizer_omega1 {G : Type} [Group G] {D : Subgroup G}
    (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) : centralizer (D : Set G) ≤
      normalizer (D : Set G) ⊓ centralizer (omega1 D hDc : Set G) :=
  le_inf (Subgroup.centralizer_le_normalizer (D : Set G))
    (Subgroup.centralizer_le (s := (omega1 D hDc : Set G)) (t := (D : Set G))
      fun _ hx => (mem_omega1_iff.1 hx).1)

theorem normalizer_conj_mem_centralizer {G : Type} [Group G] {D : Subgroup G} {m c : G}
    (hm : m ∈ normalizer (D : Set G)) (hc : c ∈ centralizer (D : Set G)) :
    m * c * m⁻¹ ∈ centralizer (D : Set G) := by
  refine mem_centralizer_iff.2 fun d hd => ?_
  have h1 : m⁻¹ * d * m ∈ D := (mem_normalizer_iff''.1 hm d).1 hd
  have h2 : (m⁻¹ * d * m) * c = c * (m⁻¹ * d * m) :=
    mem_centralizer_iff.1 hc _ h1
  calc d * (m * c * m⁻¹) = m * ((m⁻¹ * d * m) * c) * m⁻¹ := by group
    _ = m * (c * (m⁻¹ * d * m)) * m⁻¹ := by rw [h2]
    _ = m * c * m⁻¹ * d := by group

private theorem normalizer_conj_mem_normalizer {G : Type} [Group G] {D : Subgroup G} {m n : G}
    (hm : m ∈ normalizer (D : Set G)) (hn : n ∈ normalizer (D : Set G)) :
    m * n * m⁻¹ ∈ normalizer (D : Set G) := by
  rw [mem_normalizer_iff] at hn ⊢
  intro x
  constructor
  · intro hx
    have h1 : m⁻¹ * x * m ∈ D := (mem_normalizer_iff''.1 hm x).1 hx
    have h2 : n * (m⁻¹ * x * m) * n⁻¹ ∈ D := (hn (m⁻¹ * x * m)).1 h1
    have h3 : m * (n * (m⁻¹ * x * m) * n⁻¹) * m⁻¹ ∈ D :=
      (mem_normalizer_iff.1 hm _).1 h2
    rw [show (m * n * m⁻¹) * x * (m * n * m⁻¹)⁻¹ =
        m * (n * (m⁻¹ * x * m) * n⁻¹) * m⁻¹ by group]
    exact h3
  · intro hx
    have h0 : m * (n * (m⁻¹ * x * m) * n⁻¹) * m⁻¹ ∈ D := by
      rw [← show (m * n * m⁻¹) * x * (m * n * m⁻¹)⁻¹ =
        m * (n * (m⁻¹ * x * m) * n⁻¹) * m⁻¹ by group]
      exact hx
    have h1 : n * (m⁻¹ * x * m) * n⁻¹ ∈ D := (mem_normalizer_iff.1 hm _).2 h0
    have h2 : m⁻¹ * x * m ∈ D := (hn _).2 h1
    exact (mem_normalizer_iff''.1 hm x).2 h2

theorem normalizer_le_normalizer_omega1_of_comm {G : Type} [Group G] {D : Subgroup G}
    (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) :
    normalizer (D : Set G) ≤ normalizer (omega1 D hDc : Set G) := by
  intro m hm
  refine mem_normalizer_iff.2 fun v => ⟨?_, ?_⟩
  · rintro ⟨hvD, hv2⟩
    refine mem_omega1_iff.2 ⟨(mem_normalizer_iff.1 hm v).1 hvD, ?_⟩
    calc (m * v * m⁻¹) ^ 2 = m * v ^ 2 * m⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [hv2]; group
  · intro hv
    have hm' : m⁻¹ ∈ normalizer (D : Set G) := (normalizer (D : Set G)).inv_mem hm
    have h1 : m⁻¹ * (m * v * m⁻¹) * m ∈ D := by
      have h := (mem_normalizer_iff.1 hm' (m * v * m⁻¹)).1 (mem_omega1_iff.1 hv).1
      simpa using h
    have h2 : (m⁻¹ * (m * v * m⁻¹) * m) ^ 2 = 1 := by
      calc (m⁻¹ * (m * v * m⁻¹) * m) ^ 2 = m⁻¹ * (m * v * m⁻¹) ^ 2 * m := by
            rw [sq, sq]; group
        _ = 1 := by rw [(mem_omega1_iff.1 hv).2]; group
    have he : m⁻¹ * (m * v * m⁻¹) * m = v := by group
    rw [he] at h1 h2
    exact mem_omega1_iff.2 ⟨h1, h2⟩

theorem normalizer_conj_mem_normalizer_inf_centralizer_omega1 {G : Type} [Group G] {D : Subgroup G}
    (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {m κ : G} (hm : m ∈ normalizer (D : Set G))
    (hκ : κ ∈ normalizer (D : Set G) ⊓ centralizer (omega1 D hDc : Set G)) : m * κ * m⁻¹ ∈
      normalizer (D : Set G) ⊓ centralizer (omega1 D hDc : Set G) := by
  obtain ⟨hκN, hκV⟩ := hκ
  refine ⟨normalizer_conj_mem_normalizer hm hκN, ?_⟩
  refine mem_centralizer_iff.2 fun v hv => ?_
  have hmV : m ∈ normalizer (omega1 D hDc : Set G) :=
    normalizer_le_normalizer_omega1_of_comm hDc hm
  have hmvV : m⁻¹ * v * m ∈ omega1 D hDc := (mem_normalizer_iff''.1 hmV v).1 hv
  have hκv : κ * (m⁻¹ * v * m) * κ⁻¹ = m⁻¹ * v * m := by
    have hcomm := mem_centralizer_iff.1 hκV _ hmvV
    calc κ * (m⁻¹ * v * m) * κ⁻¹ = ((m⁻¹ * v * m) * κ) * κ⁻¹ := by rw [hcomm]
      _ = m⁻¹ * v * m := by group
  have hconj : (m * κ * m⁻¹) * v * (m * κ * m⁻¹)⁻¹ = v := by
    calc (m * κ * m⁻¹) * v * (m * κ * m⁻¹)⁻¹
        = m * (κ * (m⁻¹ * v * m) * κ⁻¹) * m⁻¹ := by group
      _ = m * (m⁻¹ * v * m) * m⁻¹ := by rw [hκv]
      _ = v := by group
  calc v * (m * κ * m⁻¹) = ((m * κ * m⁻¹) * v * (m * κ * m⁻¹)⁻¹) * (m * κ * m⁻¹) := by
        rw [hconj]
    _ = (m * κ * m⁻¹) * v := by group

theorem mem_centralizer_iff_forall_inv_mul_conj_eq_one {G : Type} [Group G] {D : Subgroup G}
    {κ : G} : κ ∈ centralizer (D : Set G) ↔ ∀ d ∈ D, d⁻¹ * (κ * d * κ⁻¹) = 1 := by
  constructor
  · intro hκ d hd
    have h : d * κ = κ * d := mem_centralizer_iff.1 hκ d hd
    have hfix : κ * d * κ⁻¹ = d := by
      calc κ * d * κ⁻¹ = (d * κ) * κ⁻¹ := by rw [← h]
        _ = d := by group
    rw [hfix, inv_mul_cancel]
  · intro h
    refine mem_centralizer_iff.2 fun d hd => ?_
    have h1 : κ * d * κ⁻¹ = d := by
      calc κ * d * κ⁻¹ = d * (d⁻¹ * (κ * d * κ⁻¹)) := by group
        _ = d * 1 := by rw [h d hd]
        _ = d := mul_one d
    calc d * κ = (κ * d * κ⁻¹) * κ := by rw [h1]
      _ = κ * d := by group

theorem inv_mul_conj_eq_one_of_mem_centralizer {G : Type} [Group G] {D : Subgroup G}
    (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {κ v : G} (hκ : κ ∈ centralizer (omega1 D hDc : Set G))
    (hv : v ∈ omega1 D hDc) : v⁻¹ * (κ * v * κ⁻¹) = 1 := by
  have hcomm : v * κ = κ * v := mem_centralizer_iff.1 hκ v hv
  have hfix : κ * v * κ⁻¹ = v := by
    calc κ * v * κ⁻¹ = (v * κ) * κ⁻¹ := by rw [← hcomm]
      _ = v := by group
  rw [hfix, inv_mul_cancel]

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem ThCyc.conj_D_mul_mem_omega1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκM : κ ∈ normalizer (D : Set G)) (hκA : ∀ a ∈ A, κ * a = a * κ) :
    ∀ d ∈ D, d⁻¹ * (κ * d * κ⁻¹) ∈ omega1 D hD.comm := by
  intro d hd
  have hκdD : κ * d * κ⁻¹ ∈ D := (mem_normalizer_iff.1 hκM d).1 hd
  have hd2A : d ^ 2 ∈ A := H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  have hw2 : (κ * d * κ⁻¹) ^ 2 = d ^ 2 := by
    calc (κ * d * κ⁻¹) ^ 2 = κ * d ^ 2 * κ⁻¹ := by rw [sq, sq]; group
      _ = d ^ 2 := by
          rw [hκA (d ^ 2) hd2A]
          group
  refine mem_omega1_iff.2 ⟨D.mul_mem (D.inv_mem hd) hκdD, ?_⟩
  calc (d⁻¹ * (κ * d * κ⁻¹)) ^ 2 =
      (d⁻¹) ^ 2 * (κ * d * κ⁻¹) ^ 2 :=
        (show Commute d⁻¹ (κ * d * κ⁻¹) from
          hD.comm _ (D.inv_mem hd) _ hκdD).mul_pow 2
    _ = (d⁻¹) ^ 2 * d ^ 2 := by rw [hw2]
    _ = 1 := by group

theorem ThCyc.conj_D_mul_mem_omega1_of_mem_inf (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκ : κ ∈ normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    ∀ d ∈ D, d⁻¹ * (κ * d * κ⁻¹) ∈ omega1 D hD.comm := by
  refine H.conj_D_mul_mem_omega1 W W2 hD h4 hκ.1 fun a ha => ?_
  exact (mem_centralizer_iff.1 hκ.2 a (H.A_le_omega1 W W2 hD ha)).symm

theorem ThCyc.conj_D_mul_mul (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκ : κ ∈ normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) {d d' : G}
    (hd : d ∈ D) (hd' : d' ∈ D) : (d * d')⁻¹ * (κ * (d * d') * κ⁻¹) =
      (d⁻¹ * (κ * d * κ⁻¹)) * (d'⁻¹ * (κ * d' * κ⁻¹)) := by
  have hφ : d⁻¹ * (κ * d * κ⁻¹) ∈ omega1 D hD.comm :=
    H.conj_D_mul_mem_omega1_of_mem_inf W W2 hD h4 hκ d hd
  have hκd'D : κ * d' * κ⁻¹ ∈ D := (mem_normalizer_iff.1 hκ.1 d').1 hd'
  have hcomm : d'⁻¹ * (d⁻¹ * (κ * d * κ⁻¹)) =
      (d⁻¹ * (κ * d * κ⁻¹)) * d'⁻¹ :=
    (hD.comm (d⁻¹ * (κ * d * κ⁻¹)) hφ.1 d'⁻¹ (D.inv_mem hd')).symm
  calc (d * d')⁻¹ * (κ * (d * d') * κ⁻¹)
      = d'⁻¹ * (d⁻¹ * (κ * d * κ⁻¹)) * (κ * d' * κ⁻¹) := by group
    _ = (d⁻¹ * (κ * d * κ⁻¹)) * d'⁻¹ * (κ * d' * κ⁻¹) := by rw [hcomm]
    _ = (d⁻¹ * (κ * d * κ⁻¹)) * (d'⁻¹ * (κ * d' * κ⁻¹)) := by group

theorem ThCyc.conj_D_mul_mul_conj (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ κ' : G}
    (hκ : κ ∈ normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G))
    (hκ' : κ' ∈ normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) {d : G}
    (hd : d ∈ D) : d⁻¹ * ((κ * κ') * d * (κ * κ')⁻¹) =
      (d⁻¹ * (κ * d * κ⁻¹)) * (d⁻¹ * (κ' * d * κ'⁻¹)) := by
  have hφ' : d⁻¹ * (κ' * d * κ'⁻¹) ∈ omega1 D hD.comm :=
    H.conj_D_mul_mem_omega1_of_mem_inf W W2 hD h4 hκ' d hd
  have hκφ' : κ * (d⁻¹ * (κ' * d * κ'⁻¹)) * κ⁻¹ = d⁻¹ * (κ' * d * κ'⁻¹) := by
    have hcomm := mem_centralizer_iff.1 hκ.2 _ hφ'
    calc κ * (d⁻¹ * (κ' * d * κ'⁻¹)) * κ⁻¹
        = ((d⁻¹ * (κ' * d * κ'⁻¹)) * κ) * κ⁻¹ := by rw [hcomm]
      _ = d⁻¹ * (κ' * d * κ'⁻¹) := by group
  calc d⁻¹ * ((κ * κ') * d * (κ * κ')⁻¹)
      = d⁻¹ * (κ * (κ' * d * κ'⁻¹) * κ⁻¹) := by group
    _ = d⁻¹ * (κ * (d * (d⁻¹ * (κ' * d * κ'⁻¹))) * κ⁻¹) := by group
    _ = d⁻¹ * ((κ * d * κ⁻¹) * (κ * (d⁻¹ * (κ' * d * κ'⁻¹)) * κ⁻¹)) := by group
    _ = d⁻¹ * ((κ * d * κ⁻¹) * (d⁻¹ * (κ' * d * κ'⁻¹))) := by rw [hκφ']
    _ = (d⁻¹ * (κ * d * κ⁻¹)) * (d⁻¹ * (κ' * d * κ'⁻¹)) := by group

theorem ThCyc.conj_D_mul_inv (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {κ : G}
    (hκ : κ ∈ normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) {d : G}
    (hd : d ∈ D) : d⁻¹ * (κ⁻¹ * d * κ) = (d⁻¹ * (κ * d * κ⁻¹))⁻¹ := by
  have hκinv : κ⁻¹ ∈ normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) :=
    (normalizer (D : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)).inv_mem hκ
  have hmul := H.conj_D_mul_mul_conj W W2 hD h4 hκ hκinv hd
  have hone : d⁻¹ * ((κ * κ⁻¹) * d * (κ * κ⁻¹)⁻¹) = 1 := by group
  rw [hone] at hmul
  rw [inv_inv] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

end CFSG.EvenSporadicStandard.ThStd
