module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Aa
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5AaFacts

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] {L S A B Aa : Subgroup G} {z b : G}

open Classical in
@[expose] noncomputable def sqPsi (W2 : ThLocalIn2 B A Aa b) (r a : G) : G :=
  if h : a ∈ A then psi r (Classical.choose ((W2.A_eq_sq a).1 h)) else 1

section

variable (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) {r : G}
  (hr : ∀ a ∈ A, r * a = a * r) (hrAa : ∀ x ∈ Aa, r * x * r⁻¹ ∈ Aa)

include W W2 hr hrAa

theorem sqPsi_eq {a x : G} (ha : a ∈ A) (hx : x ∈ Aa) (hxa : x ^ 2 = a) :
    sqPsi W2 r a = psi r x := by
  have hsp := Classical.choose_spec ((W2.A_eq_sq a).1 ha)
  rw [sqPsi, dite_eq_left ha]
  exact W2.psi_eq_of_sq_eq W hr hrAa hsp.1 hx (hsp.2.trans hxa.symm)

theorem sqPsi_mem {a : G} (ha : a ∈ A) : sqPsi W2 r a ∈ A := by
  obtain ⟨x, hx, hxa⟩ := (W2.A_eq_sq a).1 ha
  rw [sqPsi_eq W W2 hr hrAa ha hx hxa]
  exact W2.psi_mem_A W hr hrAa hx

theorem sqPsi_mul {a c : G} (ha : a ∈ A) (hc : c ∈ A) :
    sqPsi W2 r (a * c) = sqPsi W2 r a * sqPsi W2 r c := by
  obtain ⟨x, hx, hxa⟩ := (W2.A_eq_sq a).1 ha
  obtain ⟨y, hy, hyc⟩ := (W2.A_eq_sq c).1 hc
  have hxy : (x * y) ^ 2 = a * c := by
    rw [← hxa, ← hyc]
    exact Commute.mul_pow (show Commute x y from W2.Aa_comm x hx y hy) 2
  rw [sqPsi_eq W W2 hr hrAa (A.mul_mem ha hc) (Aa.mul_mem hx hy) hxy,
    sqPsi_eq W W2 hr hrAa ha hx hxa, sqPsi_eq W W2 hr hrAa hc hy hyc]
  exact W2.psi_mul hrAa hx hy

end

section

variable (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) {r r' : G}
  (hr : ∀ a ∈ A, r * a = a * r) (hrAa : ∀ x ∈ Aa, r * x * r⁻¹ ∈ Aa)
  (hr' : ∀ a ∈ A, r' * a = a * r') (hr'Aa : ∀ x ∈ Aa, r' * x * r'⁻¹ ∈ Aa)

include W W2 hr hrAa hr' hr'Aa

theorem sqPsi_mul_left {a : G} (ha : a ∈ A) :
    sqPsi W2 (r * r') a = sqPsi W2 r' a * sqPsi W2 r a := by
  obtain ⟨x, hx, hxa⟩ := (W2.A_eq_sq a).1 ha
  have hrr' : ∀ a ∈ A, r * r' * a = a * (r * r') := fun a ha => by
    rw [mul_assoc, hr' a ha, ← mul_assoc, hr a ha, mul_assoc]
  have hrr'Aa : ∀ x ∈ Aa, r * r' * x * (r * r')⁻¹ ∈ Aa := fun x hx => by
    have : r * r' * x * (r * r')⁻¹ = r * (r' * x * r'⁻¹) * r⁻¹ := by group
    rw [this]
    exact hrAa _ (hr'Aa x hx)
  rw [sqPsi_eq W W2 hrr' hrr'Aa ha hx hxa, sqPsi_eq W W2 hr hrAa ha hx hxa,
    sqPsi_eq W W2 hr' hr'Aa ha hx hxa, psi_mul_left]
  have hmem := W2.psi_mem_A W hr' hr'Aa hx
  have : r * psi r' x * r⁻¹ = psi r' x := by
    rw [hr _ hmem]
    group
  rw [this]

end

section

variable (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) {n r : G}
  (hr : ∀ a ∈ A, r * a = a * r) (hrAa : ∀ x ∈ Aa, r * x * r⁻¹ ∈ Aa)
  (hr' : ∀ a ∈ A, n * r * n⁻¹ * a = a * (n * r * n⁻¹))
  (hr'Aa : ∀ x ∈ Aa, n * r * n⁻¹ * x * (n * r * n⁻¹)⁻¹ ∈ Aa)
  (hn : ∀ x ∈ Aa, n * x * n⁻¹ ∈ Aa) (hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A)

include W W2 hr hrAa hr' hr'Aa hn hnA

theorem sqPsi_conj {a : G} (ha : a ∈ A) :
    sqPsi W2 (n * r * n⁻¹) (n * a * n⁻¹) = n * sqPsi W2 r a * n⁻¹ := by
  obtain ⟨x, hx, hxa⟩ := (W2.A_eq_sq a).1 ha
  have hsq : (n * x * n⁻¹) ^ 2 = n * a * n⁻¹ := by
    rw [conj_pow, hxa]
  rw [sqPsi_eq W W2 hr' hr'Aa (hnA a ha) (hn x hx) hsq, sqPsi_eq W W2 hr hrAa ha hx hxa, psi_conj]

end

section Cyc

variable [Finite G] {R : Subgroup G} {t : G}
  (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)

include H W W2

theorem sqPsi_centralizer_W5 {y : G} (hy : y ∈ centralizer ((W5 A t : Subgroup G) : Set G)) :
    ∃ e : ℕ, ∀ a ∈ A, sqPsi W2 y a = a ^ e := by
  have hyBp : y ∈ Bp A t := centralizer_W5_le_Bp A t hy
  have hr : ∀ a ∈ A, y * a = a * y := fun a ha => (mem_centralizer_iff.1 hyBp.1 a ha).symm
  have hrAa : ∀ x ∈ Aa, y * x * y⁻¹ ∈ Aa := H.Aa_normal W W2 hyBp.2
  obtain ⟨b'', hb'', k, rfl⟩ := (H.mem_centralizer_W5_iff W).1 hy
  have hpsi : ∀ x ∈ Aa, psi (b'' * t ^ k) x = psi b'' x := fun x hx => by
    have hxt : t ^ k * x = x * t ^ k :=
      (((show Commute x t from (H.comm_of_mem_L (W.B_le (W2.Aa_le hx))).symm).zpow_right k).eq).symm
    simp only [psi]
    calc b'' * t ^ k * x * (b'' * t ^ k)⁻¹ * x⁻¹
        = b'' * (t ^ k * x) * (t ^ k)⁻¹ * b''⁻¹ * x⁻¹ := by group
      _ = b'' * (x * t ^ k) * (t ^ k)⁻¹ * b''⁻¹ * x⁻¹ := by rw [hxt]
      _ = b'' * x * b''⁻¹ * x⁻¹ := by group
  rcases W2.psi_of_mem_B hb'' (W2.mem_Aa_or_mul_b W hb'') with h | h
  · refine ⟨0, fun a ha => ?_⟩
    obtain ⟨x, hx, hxa⟩ := (W2.A_eq_sq a).1 ha
    rw [sqPsi_eq W W2 hr hrAa ha hx hxa, hpsi x hx, h x hx, pow_zero]
  · refine ⟨1, fun a ha => ?_⟩
    obtain ⟨x, hx, hxa⟩ := (W2.A_eq_sq a).1 ha
    rw [sqPsi_eq W W2 hr hrAa ha hx hxa, hpsi x hx, h x hx, hxa, pow_one]

end Cyc

end CFSG.EvenSporadicStandard.ThStd
