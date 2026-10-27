module

public import CFSG.Fischer.Uniq.Graph
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X : Type} [Group X] {E : Set X}

section C3

theorem Pair.eq_of_mul_commute (hP : Pair X E) {x f z : X} (hx : x ∈ E) (hf : f ∈ E)
    (hz : z ∈ E) (hxz : z * x ≠ x * z) (hwx : x * (x * f) = x * f * x)
    (hwz : z * (x * f) = x * f * z) : x = f := by
  have hxf : x * f = f * x := by
    have h := hwx
    rw [← mul_assoc, Pair.mul_self hP hx, one_mul] at h
    exact (Pair.mul_mul_eq_self_iff hP hx f).1 h.symm
  have hfw : z * f = z * x * (x * f) := by
    simp only [← mul_assoc, mul_assoc z x x, Pair.mul_self hP hx, mul_one]
  have hzf : z * f ≠ f * z := by
    intro h
    apply hxz
    have h' : z * x * (x * f) = x * z * (x * f) := by
      calc z * x * (x * f) = z * f := hfw.symm
        _ = f * z := h
        _ = x * (x * f * z) := by simp only [← mul_assoc, Pair.mul_self hP hx, one_mul]
        _ = x * z * (x * f) := by rw [← hwz, mul_assoc]
    exact mul_right_cancel h'
  have hc : Commute (z * x) (x * f) :=
    (show Commute z (x * f) from hwz).mul_left (show Commute x (x * f) from hwx)
  have hw3 : (x * f) ^ 3 = 1 := by
    have h3 : (z * f) ^ 3 = 1 := by
      rw [← Pair.orderOf_mul_eq_three hP hz hf hzf, pow_orderOf_eq_one]
    have h3' : (z * x) ^ 3 = 1 := by
      rw [← Pair.orderOf_mul_eq_three hP hz hx hxz, pow_orderOf_eq_one]
    rwa [hfw, hc.mul_pow, h3', one_mul] at h3
  have hw2 : (x * f) ^ 2 = 1 := by
    rw [sq]
    calc x * f * (x * f) = x * (f * x) * f := by simp only [mul_assoc]
      _ = x * x * (f * f) := by rw [← hxf]; simp only [mul_assoc]
      _ = 1 := by rw [Pair.mul_self hP hx, Pair.mul_self hP hf, one_mul]
  have hw1 : x * f = 1 := by
    calc x * f = (x * f) ^ 3 * ((x * f) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hw3, hw2, inv_one, one_mul]
  rw [← mul_left_cancel_iff (a := x), hw1, Pair.mul_self hP hx]

end C3

section Star

theorem commute_of_mem_localGroup_self {d g : X} (hg : g ∈ LocalGroup E d) : g * d = d * g :=
  commute_of_mem_localGroup (fun _ hf => hf.2.2) hg

end Star

section S4

variable {d : X} {N : Subgroup X}

theorem Pair.commute_conj_of_commute (hP : Pair X E)
    (hN : ∀ f ∈ LocalClass E d, ∀ g ∈ N, f * g * f⁻¹ ∈ N)
    (hN2 : ∀ u ∈ N, u * u = 1 → ∀ f ∈ LocalClass E d, u * f = f * u)
    {x f g : X} (hx : x ∈ LocalClass E d) (hf : f ∈ LocalClass E d) (hfx : f ≠ x)
    (hcomm : f * x = x * f) (hg : g ∈ N) (hy : g * x * g⁻¹ ∈ LocalClass E d) :
    f * (g * x * g⁻¹) = g * x * g⁻¹ * f := by
  set y := g * x * g⁻¹ with hydef
  have hxE : x ∈ E := hx.1
  have hfE : f ∈ E := hf.1
  have hyE : y ∈ E := hy.1
  have hxyN : x * y ∈ N := by
    have h := N.mul_mem (hN x hx g hg) (N.inv_mem hg)
    rwa [Pair.inv_eq hP hxE, show x * g * x * g⁻¹ = x * (g * x * g⁻¹) by group] at h
  by_cases hxy : x * y = y * x
  · have h2 : x * y * (x * y) = 1 := by
      calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
        _ = x * x * (y * y) := by rw [← hxy]; simp only [mul_assoc]
        _ = 1 := by rw [Pair.mul_self hP hxE, Pair.mul_self hP hyE, one_mul]
    have hc := hN2 _ hxyN h2 f hf
    calc f * y = f * x * (x * y) := by
          rw [mul_assoc f x, ← mul_assoc x x, Pair.mul_self hP hxE, one_mul]
      _ = x * (f * (x * y)) := by rw [hcomm, mul_assoc]
      _ = x * (x * y) * f := by rw [← hc]; simp only [mul_assoc]
      _ = y * f := by rw [← mul_assoc, Pair.mul_self hP hxE, one_mul]
  · by_contra hfy
    have hbxy : x * y * x = y * x * y := Pair.mul_mul_eq hP hxE hyE hxy
    have hbfy : f * y * f = y * f * y := Pair.mul_mul_eq hP hfE hyE hfy
    have hu : x * y * (f * (x * y) * f⁻¹) = y * (x * f) * y := by
      rw [Pair.inv_eq hP hfE]
      calc x * y * (f * (x * y) * f) = x * y * (f * x) * y * f := by simp only [mul_assoc]
        _ = x * y * x * (f * y * f) := by rw [hcomm]; simp only [mul_assoc]
        _ = y * x * (y * y) * f * y := by rw [hbxy, hbfy]; simp only [mul_assoc]
        _ = y * (x * f) * y := by rw [Pair.mul_self hP hyE, mul_one]; simp only [mul_assoc]
    have huN : y * (x * f) * y ∈ N := hu ▸ N.mul_mem hxyN (hN f hf _ hxyN)
    have hu2 : y * (x * f) * y * (y * (x * f) * y) = 1 := by
      calc y * (x * f) * y * (y * (x * f) * y) = y * (x * f) * (y * y) * (x * f) * y := by
            simp only [mul_assoc]
        _ = y * (x * (f * x) * f) * y := by
          rw [Pair.mul_self hP hyE, mul_one]; simp only [mul_assoc]
        _ = y * (x * x * (f * f)) * y := by rw [hcomm]; simp only [mul_assoc]
        _ = 1 := by rw [Pair.mul_self hP hxE, Pair.mul_self hP hfE, one_mul, mul_one,
          Pair.mul_self hP hyE]
    have hcu := hN2 _ huN hu2
    have hw : x * f = y * (x * f) * y := by
      have e1 : y * (y * (x * f) * y) * y = x * f := by
        simp only [← mul_assoc, Pair.mul_self hP hyE, one_mul]
        rw [mul_assoc (x * f) y y, Pair.mul_self hP hyE, mul_one]
      calc x * f = y * (y * (x * f) * y) * y := e1.symm
        _ = y * (x * f) * y * y * y := by rw [← hcu y hy]
        _ = y * (x * f) * y := by rw [mul_assoc (y * (x * f) * y) y y, Pair.mul_self hP hyE,
          mul_one]
    have hwx : x * (x * f) = x * f * x := by rw [hw]; exact (hcu x hx).symm
    have hwy : y * (x * f) = x * f * y := by rw [hw]; exact (hcu y hy).symm
    exact hfx (Pair.eq_of_mul_commute hP hxE hfE hyE (fun h => hxy h.symm) hwx hwy).symm

end S4

section Extract

theorem eq_one_of_isPGroup_three {H : Type*} [Group H] {Q : Subgroup H} (hQ : IsPGroup 3 Q)
    {q : H} (hq : q ∈ Q) (h2 : q * q = 1) : q = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
  have h1 : orderOf (⟨q, hq⟩ : Q) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2' : orderOf (⟨q, hq⟩ : Q) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [sq] using h2))
  have hcop : Nat.Coprime (3 ^ k) 2 := Nat.Coprime.pow_left k (by norm_num)
  have h1' : orderOf (⟨q, hq⟩ : Q) = 1 :=
    Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h1 h2')
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h1')

end Extract

end CFSG.Fischer.Classification
