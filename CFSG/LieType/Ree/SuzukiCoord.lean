module

public import CFSG.LieType.Ree.SuzukiBorelStructure

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint

variable {a : ℕ} {K : Type} [Field K]

noncomputable def szCoord (y : suzukiGroup a K) : K × K := by
  classical
  exact if h : ∃ p : K × K, suzukiSElt a K p.1 p.2 = y then h.choose else 0

private theorem szCoord_eq_of_eq {y : suzukiGroup a K} {p : K × K}
    (h : suzukiSElt a K p.1 p.2 = y) : szCoord y = p := by
  classical
  unfold szCoord
  split_ifs with hh
  · obtain ⟨h1, h2⟩ := suzukiSElt_inj.1 (hh.choose_spec.trans h.symm)
    exact Prod.ext h1 h2
  · exact absurd ⟨p, h⟩ hh

theorem szCoord_suzukiSElt (u v : K) : szCoord (suzukiSElt a K u v) = (u, v) :=
  szCoord_eq_of_eq rfl

theorem szCoord_mul_fst [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x y : suzukiGroup a K} (hx : x ∈ suzukiU a K) (hy : y ∈ suzukiU a K) :
    (szCoord (x * y)).1 = (szCoord x).1 + (szCoord y).1 := by
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
  obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hy
  simp only [suzukiSElt_mul hK, szCoord_suzukiSElt]

theorem szCoord_mul_snd [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x y : suzukiGroup a K} (hx : x ∈ suzukiZ0 a K) (hy : y ∈ suzukiZ0 a K) :
    (szCoord (x * y)).2 = (szCoord x).2 + (szCoord y).2 := by
  obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hx
  obtain ⟨d, rfl⟩ := (mem_suzukiZ0_iff hK).1 hy
  simp only [suzukiSElt_mul hK, szCoord_suzukiSElt]
  simp

theorem szCoord_fst_eq_zero_iff [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x : suzukiGroup a K} (hx : x ∈ suzukiU a K) :
    (szCoord x).1 = 0 ↔ x ∈ suzukiZ0 a K := by
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
  rw [szCoord_suzukiSElt, mem_suzukiZ0_iff hK]
  change u = 0 ↔ ∃ w : K, suzukiSElt a K 0 w = suzukiSElt a K u v
  constructor
  · intro h
    exact ⟨v, by rw [h]⟩
  · rintro ⟨w, hw⟩
    exact (suzukiSElt_inj.1 hw).1.symm

theorem szCoord_snd_eq_zero_iff [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x : suzukiGroup a K} (hx : x ∈ suzukiZ0 a K) :
    (szCoord x).2 = 0 ↔ x = 1 := by
  obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hx
  rw [szCoord_suzukiSElt]
  change v = 0 ↔ suzukiSElt a K 0 v = 1
  rw [← suzukiSElt_zero_zero hK, suzukiSElt_inj]
  simp

theorem szCoord_conj_suzukiDElt [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ)
    {x : suzukiGroup a K} (hx : x ∈ suzukiU a K) :
    szCoord (suzukiDElt a K l * x * (suzukiDElt a K l)⁻¹) =
      (((l⁻¹ : Kˣ) : K) * (szCoord x).1,
        ((l⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) * (szCoord x).2) := by
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
  simp only [suzukiDElt_conj' hK, szCoord_suzukiSElt]

private theorem suzukiSElt_sq [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K) :
    suzukiSElt a K u v ^ 2 = suzukiSElt a K 0 (u ^ (2 ^ (a + 1) + 1)) := by
  obtain ⟨h2, -, -⟩ := suzuki_frob_data a hK
  have h2u : ∀ x : K, x + x = 0 := fun x => by linear_combination x * h2
  rw [sq, suzukiSElt_mul hK, suzukiSElt_inj]
  exact ⟨by rw [h2u u], by rw [h2u v, zero_add]; simp only [pow_succ]⟩

theorem sq_mem_suzukiZ0 [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x : suzukiGroup a K} (hx : x ∈ suzukiU a K) : x ^ 2 ∈ suzukiZ0 a K := by
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
  rw [suzukiSElt_sq hK, mem_suzukiZ0_iff hK]
  exact ⟨_, rfl⟩

end CFSG.LieType.Ree

end
