module

public import CFSG.ClassicalInvolution.Balance.WeakFrame.Frame

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups

section SquareRoot

variable {H : Type*} [Group H]

theorem conj_eq_of_sq {s u m : H} (hs : s * s = 1) (hu : u * u = m) (hsu : s * u * s = u⁻¹) :
    u * (s * m) * u⁻¹ = s := by
  have h3 : u * s = s * u⁻¹ := by
    calc u * s = (s * s) * u * s := by rw [hs, one_mul]
      _ = s * (s * u * s) := by group
      _ = s * u⁻¹ := by rw [hsu]
  subst hu
  calc u * (s * (u * u)) * u⁻¹ = (u * s) * (u * u) * u⁻¹ := by group
    _ = (s * u⁻¹) * (u * u) * u⁻¹ := by rw [h3]
    _ = s := by group

theorem exists_zpowers_conj_eq {s m : H} (hs : s * s = 1) (hsm : s * m * (s * m) = 1)
    (hodd : Odd (orderOf m)) : ∃ u ∈ Subgroup.zpowers m, u * (s * m) * u⁻¹ = s := by
  obtain ⟨j, hj⟩ := hodd
  have hu2 : m ^ (j + 1) * m ^ (j + 1) = m := by
    rw [← pow_add]
    have : j + 1 + (j + 1) = orderOf m + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have h1 : s * m * s = m⁻¹ := by
    have : s * m * s * m = 1 := by
      calc s * m * s * m = s * m * (s * m) := by group
        _ = 1 := hsm
    exact eq_inv_of_mul_eq_one_left this
  have h2 : s * m ^ (j + 1) * s = (m ^ (j + 1))⁻¹ := by
    calc s * m ^ (j + 1) * s = s * m ^ (j + 1) * s⁻¹ := by rw [hs']
      _ = (s * m * s⁻¹) ^ (j + 1) := conj_pow.symm
      _ = (m⁻¹) ^ (j + 1) := by rw [hs', h1]
      _ = (m ^ (j + 1))⁻¹ := inv_pow m (j + 1)
  exact ⟨m ^ (j + 1), Subgroup.pow_mem _ (Subgroup.mem_zpowers m) _,
    conj_eq_of_sq hs hu2 h2⟩

end SquareRoot

variable {F : Type*} [Field F] {G : Type*} [Group G] {E K : Subgroup G}

namespace WeakInSigma

theorem mul_mem_axis (hK : WeakInSigma F E K) (hE : ∀ x ∈ E, x * x = 1) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) (hx' : x ∉ axisSub E K) (hy' : y ∉ axisSub E K) : x * y ∈ axisSub E K := by
  obtain ⟨a, haE, haN, hsplit⟩ := hK.exists_split
  have hxa : x * a ∈ axisSub E K := (hsplit x hx).resolve_left hx'
  have hya : y * a ∈ axisSub E K := (hsplit y hy).resolve_left hy'
  have h4 := (axisSub E K).mul_mem hxa hya
  have e1 : x * a * (y * a) = x * y := by
    calc x * a * (y * a) = x * (a * y) * a := by group
      _ = x * (y * a) * a := by rw [comm_of_sq_eq_one hE haE hy]
      _ = x * y * (a * a) := by group
      _ = x * y := by rw [hE a haE, mul_one]
  rwa [e1] at h4

variable [Finite G]

theorem conj_eq_mul_of_not_mem_axis (hK : WeakInSigma F E K) (hE : ∀ x ∈ E, x * x = 1)
    (hodd : Odd (Nat.card F)) {z : G} (hz : IsCentralInvolution K z) {w : G}
    (hw : w ∈ normPart K E) (hw' : w ∉ centPart K E) {x : G} (hx : x ∈ E)
    (hx' : x ∉ axisSub E K) : w * x * w⁻¹ = x * z := by
  obtain ⟨φ, hφ, -, -⟩ := hK.chart
  have hwK : w ∈ K := (mem_normPart_iff.mp hw).1
  have hwN : w ∈ Subgroup.normalizer (E : Set G) := (mem_normPart_iff.mp hw).2
  have hyE : w * x * w⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hwN x).mp hx
  have hcE : w * x * w⁻¹ * x⁻¹ ∈ E := E.mul_mem hyE (E.inv_mem hx)
  have hcK : w * x * w⁻¹ * x⁻¹ ∈ K := by
    have := K.mul_mem hwK (hK.normalizes x hx w⁻¹ (K.inv_mem hwK))
    have e : w * (x * w⁻¹ * x⁻¹) = w * x * w⁻¹ * x⁻¹ := by group
    rwa [e] at this
  have hcsq : w * x * w⁻¹ * x⁻¹ * (w * x * w⁻¹ * x⁻¹) = 1 := hE _ hcE
  rcases hφ.eq_one_or_eq_of_sq hodd hz hcK hcsq with h | h
  · exfalso
    have hxc : w * x = x * w := by
      have : w * x * w⁻¹ = x := by
        calc w * x * w⁻¹ = (w * x * w⁻¹ * x⁻¹) * x := by group
          _ = x := by rw [h, one_mul]
      calc w * x = (w * x * w⁻¹) * w := by group
        _ = x * w := by rw [this]
    apply hw'
    rw [mem_centPart_iff]
    refine ⟨hwK, fun e he => ?_⟩
    by_cases hea : e ∈ axisSub E K
    · exact ((mem_axisSub_iff.mp hea).2 w hwK).symm
    · have hexa : e * x ∈ axisSub E K := hK.mul_mem_axis hE he hx hea hx'
      have h1 : w * (e * x) = (e * x) * w := ((mem_axisSub_iff.mp hexa).2 w hwK)
      have hxx : x * x = 1 := hE x hx
      have : w * e = e * w := by
        calc w * e = w * (e * x) * x := by
              calc w * e = w * e * (x * x) := by rw [hxx, mul_one]
                _ = w * (e * x) * x := by group
          _ = (e * x) * w * x := by rw [h1]
          _ = (e * x) * (w * x) := by group
          _ = (e * x) * (x * w) := by rw [hxc]
          _ = e * (x * x) * w := by group
          _ = e * w := by rw [hxx, mul_one]
      exact this.symm
  · have hzE : z ∈ E := by rw [← h]; exact hcE
    calc w * x * w⁻¹ = (w * x * w⁻¹ * x⁻¹) * x := by group
      _ = z * x := by rw [h]
      _ = x * z := comm_of_sq_eq_one hE hzE hx

theorem conj_inv_eq (hK : WeakInSigma F E K) (hE : ∀ x ∈ E, x * x = 1)
    (hodd : Odd (Nat.card F)) {z : G} (hz : IsCentralInvolution K z) {w : G}
    (hw : w ∈ normPart K E) (hw' : w ∉ centPart K E) {x : G} (hx : x ∈ E) :
    w⁻¹ * x * w = w * x * w⁻¹ := by
  have hwK : w ∈ K := (mem_normPart_iff.mp hw).1
  have hwz : w * z * w⁻¹ = z := by
    have := hz.central w hwK
    calc w * z * w⁻¹ = z * w * w⁻¹ := by rw [this]
      _ = z := by group
  have key : w * (w * x * w⁻¹) * w⁻¹ = x := by
    by_cases hxa : x ∈ axisSub E K
    · have : w * x * w⁻¹ = x := InSigma.conj_eq_of_mem_axis hwK hxa
      rw [this, this]
    · have h1 := hK.conj_eq_mul_of_not_mem_axis hE hodd hz hw hw' hx hxa
      rw [h1]
      calc w * (x * z) * w⁻¹ = (w * x * w⁻¹) * (w * z * w⁻¹) := by group
        _ = x * z * z := by rw [h1, hwz]
        _ = x := by
          have hzz : z * z = 1 := hz.sq
          rw [mul_assoc, hzz, mul_one]
  calc w⁻¹ * x * w = w⁻¹ * (w * (w * x * w⁻¹) * w⁻¹) * w := by rw [key]
    _ = w * x * w⁻¹ := by group

theorem exists_mem_normPart_not_mem_centPart (hK : WeakInSigma F E K) (hE : ∀ x ∈ E, x * x = 1)
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) :
    ∃ w ∈ normPart K E, w ∉ centPart K E := by
  have hfin := finite_of_odd_card hodd
  obtain ⟨z, hzm, hzE⟩ := hK.member
  have hz := hzm.isCentralInvolution
  obtain ⟨φ, hφ, hdiag, hker⟩ := hK.chart
  obtain ⟨e₀, he₀E, he₀N⟩ := hK.exists_mem_not_mem_axis
  obtain ⟨g, hg⟩ := hdiag e₀ he₀E
  have he₀sq : e₀ * e₀ = 1 := hE e₀ he₀E
  have he₀inv : e₀⁻¹ = e₀ := inv_eq_of_mul_eq_one_right he₀sq
  have hnorm : ∀ k : ↥K, e₀ * (k : G) * e₀⁻¹ ∈ K := fun k => hK.normalizes e₀ he₀E k k.2
  have hinv : IsInvolDiag g := by
    constructor
    · intro s
      obtain ⟨k, rfl⟩ := hφ.surjective s
      let k' : ↥K := ⟨e₀ * k * e₀⁻¹, hnorm k⟩
      let k'' : ↥K := ⟨e₀ * k' * e₀⁻¹, hnorm k'⟩
      have h1 : φ k' = slConjugation 2 F g (φ k) := hg k k' rfl
      have h2 : φ k'' = slConjugation 2 F g (φ k') := hg k' k'' rfl
      have h3 : k'' = k := by
        apply Subtype.ext
        show e₀ * (e₀ * (k : G) * e₀⁻¹) * e₀⁻¹ = k
        calc e₀ * (e₀ * (k : G) * e₀⁻¹) * e₀⁻¹ = (e₀ * e₀) * k * (e₀⁻¹ * e₀⁻¹) := by group
          _ = k := by rw [he₀sq, he₀inv, he₀sq]; group
      rw [← h1, ← h2, h3]
    · by_contra hne
      push Not at hne
      apply he₀N
      refine hker e₀ he₀E fun k k' hk' => ?_
      rw [hg k k' hk', hne]
  obtain ⟨wm, hwm⟩ := hinv.exists_anticomm hodd h5
  obtain ⟨w₁, hw₁⟩ := hφ.surjective wm
  have hφz : φ ⟨z, hz.mem⟩ = -1 := hφ.map_central hodd hz
  let zK : ↥K := ⟨z, hz.mem⟩
  let k' : ↥K := ⟨e₀ * w₁ * e₀⁻¹, hnorm w₁⟩
  have hk' : φ k' = φ (w₁ * zK) := by
    rw [hg w₁ k' rfl, map_mul, hw₁, hφz, hwm]
  let n : ↥K := (w₁ * zK)⁻¹ * k'
  have hn : n ∈ componentClassificationOddCore ↥K := by
    rw [← hφ.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, hk', inv_mul_cancel]
  let m : ↥K := w₁ * n * w₁⁻¹
  have hm : m ∈ componentClassificationOddCore ↥K :=
    (componentClassificationOddCore_normal ↥K).conj_mem n hn w₁
  have hmodd : Odd (orderOf (m : G)) := by
    rw [Subgroup.orderOf_coe]
    exact (OddCore.odd_card ↥K).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hm)
  have hzw : z * (w₁ : G) = (w₁ : G) * z := hz.central w₁ w₁.2
  have hk'eq : e₀ * (w₁ : G) * e₀⁻¹ = (w₁ : G) * z * (n : G) := by
    have : k' = w₁ * zK * n := (mul_inv_cancel_left (w₁ * zK) k').symm
    exact congrArg Subtype.val this
  have hss : (e₀ * z) * (e₀ * z) = 1 := by
    calc e₀ * z * (e₀ * z) = e₀ * (z * e₀) * z := by group
      _ = e₀ * (e₀ * z) * z := by rw [comm_of_sq_eq_one hE hzE he₀E]
      _ = (e₀ * e₀) * (z * z) := by group
      _ = 1 := by rw [he₀sq, hz.sq, one_mul]
  have ht : (e₀ * z) * (m : G) = (w₁ : G) * e₀ * (w₁ : G)⁻¹ := by
    calc (e₀ * z) * (m : G) = e₀ * (z * w₁) * n * (w₁ : G)⁻¹ := by
          show e₀ * z * ((w₁ : G) * n * (w₁ : G)⁻¹) = _
          group
      _ = e₀ * (w₁ * z) * n * (w₁ : G)⁻¹ := by rw [hzw]
      _ = e₀ * ((w₁ : G) * z * n) * (w₁ : G)⁻¹ := by group
      _ = e₀ * (e₀ * w₁ * e₀⁻¹) * (w₁ : G)⁻¹ := by rw [hk'eq]
      _ = (e₀ * e₀) * w₁ * e₀⁻¹ * (w₁ : G)⁻¹ := by group
      _ = (w₁ : G) * e₀ * (w₁ : G)⁻¹ := by rw [he₀sq, he₀inv]; group
  have hsm : (e₀ * z) * (m : G) * ((e₀ * z) * (m : G)) = 1 := by
    rw [ht]
    calc (w₁ : G) * e₀ * (w₁ : G)⁻¹ * ((w₁ : G) * e₀ * (w₁ : G)⁻¹)
        = (w₁ : G) * (e₀ * e₀) * (w₁ : G)⁻¹ := by group
      _ = 1 := by rw [he₀sq]; group
  obtain ⟨u, hu, hut⟩ := exists_zpowers_conj_eq hss hsm hmodd
  have huK : u ∈ K := (Subgroup.zpowers_le.mpr m.2) hu
  have hwK : u * (w₁ : G) ∈ K := K.mul_mem huK w₁.2
  have hwe₀ : u * (w₁ : G) * e₀ * (u * (w₁ : G))⁻¹ = e₀ * z := by
    calc u * (w₁ : G) * e₀ * (u * (w₁ : G))⁻¹
        = u * ((w₁ : G) * e₀ * (w₁ : G)⁻¹) * u⁻¹ := by group
      _ = u * ((e₀ * z) * (m : G)) * u⁻¹ := by rw [ht]
      _ = e₀ * z := hut
  generalize hwdef : u * (w₁ : G) = w at hwK hwe₀
  have hwz : w * z * w⁻¹ = z := by
    have := hz.central w hwK
    calc w * z * w⁻¹ = z * w * w⁻¹ := by rw [this]
      _ = z := by group
  have hw1 : ∀ e ∈ E, w * e * w⁻¹ = e ∨ w * e * w⁻¹ = e * z := by
    intro e he
    by_cases hea : e ∈ axisSub E K
    · exact Or.inl (InSigma.conj_eq_of_mem_axis hwK hea)
    · right
      have hee : e * e₀ ∈ axisSub E K := hK.mul_mem_axis hE he he₀E hea he₀N
      have h1 : w * (e * e₀) * w⁻¹ = e * e₀ := InSigma.conj_eq_of_mem_axis hwK hee
      calc w * e * w⁻¹ = w * (e * (e₀ * e₀)) * w⁻¹ := by rw [he₀sq, mul_one]
        _ = (w * (e * e₀) * w⁻¹) * (w * e₀ * w⁻¹) := by group
        _ = (e * e₀) * (e₀ * z) := by rw [h1, hwe₀]
        _ = e * (e₀ * e₀) * z := by group
        _ = e * z := by rw [he₀sq, mul_one]
  have hwE : ∀ e ∈ E, w * e * w⁻¹ ∈ E := by
    intro e he
    rcases hw1 e he with h | h
    · rw [h]
      exact he
    · rw [h]
      exact E.mul_mem he hzE
  have hconj2 : ∀ e ∈ E, w * (w * e * w⁻¹) * w⁻¹ = e := by
    intro e he
    rcases hw1 e he with h | h
    · rw [h, h]
    · rw [h]
      calc w * (e * z) * w⁻¹ = (w * e * w⁻¹) * (w * z * w⁻¹) := by group
        _ = e * z * z := by rw [h, hwz]
        _ = e := by rw [mul_assoc, hz.sq, mul_one]
  have hwN : w ∈ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hwE h hh, fun hh => ?_⟩
    have e1 : w⁻¹ * (w * h * w⁻¹) * w = w * (w * h * w⁻¹) * w⁻¹ := by
      calc w⁻¹ * (w * h * w⁻¹) * w = w⁻¹ * (w * (w * (w * h * w⁻¹) * w⁻¹) * w⁻¹) * w := by
            rw [hconj2 _ hh]
        _ = w * (w * h * w⁻¹) * w⁻¹ := by group
    have e2 : h = w * (w * h * w⁻¹) * w⁻¹ := by
      calc h = w⁻¹ * (w * h * w⁻¹) * w := by group
        _ = w * (w * h * w⁻¹) * w⁻¹ := e1
    rw [e2]
    exact hwE _ hh
  refine ⟨w, mem_normPart_iff.mpr ⟨hwK, hwN⟩, fun hc => ?_⟩
  have hc' := ((mem_centPart_iff.mp hc).2 e₀ he₀E)
  have h1 : w * e₀ * w⁻¹ = e₀ := by
    calc w * e₀ * w⁻¹ = (w * e₀) * w⁻¹ := rfl
      _ = (e₀ * w) * w⁻¹ := by rw [← hc']
      _ = e₀ := by group
  rw [hwe₀] at h1
  apply hz.ne_one
  have : e₀ * z = e₀ * 1 := by rw [h1, mul_one]
  exact mul_left_cancel this

end WeakInSigma

end CFSG.ClassicalInvolution.Balance
