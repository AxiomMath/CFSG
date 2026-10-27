module

public import CFSG.CGT.Stroth76.SylowCw
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Thompson

public section

namespace CFSG.CGT.Stroth77.Stroth42

variable {G : Type*} [Group G] [Finite G]

theorem conj_pow' (g x : G) (k : ℕ) : (g⁻¹ * x * g) ^ k = g⁻¹ * x ^ k * g := by
  simpa using conj_pow (a := g⁻¹) (b := x) (i := k)

theorem isConj_of_conj_eq {g x y : G} (h : g⁻¹ * x * g = y) : IsConj y x :=
  isConj_iff.2 ⟨g, by rw [← h]; group⟩

theorem mul_self_eq_one_of_isConj {y z : G} (h : IsConj y z) (hz2 : z * z = 1) : y * y = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  calc y * y = c⁻¹ * (c * y * c⁻¹ * (c * y * c⁻¹)) * c := by group
    _ = 1 := by rw [hc, hz2]; group

theorem ne_one_of_isConj {y z : G} (h : IsConj y z) (hz1 : z ≠ 1) : y ≠ 1 := by
  rintro rfl
  exact hz1 (isConj_one_right.1 h)

theorem exists_pow_eq_of_even {x z : G} {j k : ℕ} (hxz : x ^ 2 ^ j = z) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hk : x ^ (2 * k) ≠ 1) :
    ∃ l : ℕ, l + 1 ≤ j ∧ (x ^ (2 * k)) ^ 2 ^ l = z ∧ (x ^ (2 * k)) ^ 2 ^ j = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx1 : x ^ 2 ^ (j + 1) = 1 := by rw [pow_succ, pow_mul, hxz, sq, hz2]
  have hox : orderOf x = 2 ^ (j + 1) := orderOf_eq_prime_pow (by rw [hxz]; exact hz1) hx1
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  obtain ⟨v, q, hq, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk0
  have hv : v + 1 ≤ j := by
    by_contra hv
    apply hk
    rw [← orderOf_dvd_iff_pow_eq_one, hox, show 2 * (2 ^ v * q) = 2 ^ (v + 1) * q by ring]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) q
  obtain ⟨d, rfl⟩ : ∃ d, j = v + 1 + d := ⟨j - (v + 1), by omega⟩
  refine ⟨d, by omega, ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := hq
    rw [← pow_mul, show 2 * (2 ^ v * (2 * r + 1)) * 2 ^ d = 2 ^ (v + 1 + d) * (2 * r + 1) by ring,
      pow_mul, hxz, pow_succ, pow_mul, sq, hz2, one_pow, one_mul]
  · rw [← pow_mul, show 2 * (2 ^ v * q) * 2 ^ (v + 1 + d) = 2 ^ (v + 1 + d + 1) * (2 ^ v * q) by
      ring, pow_mul, hx1, one_pow]

theorem mul_self_mem_of_relIndex {S U : Subgroup G} (hU : U.relIndex S = 2) {y : G}
    (hyS : y ∈ S) : y * y ∈ U := by
  have h := Subgroup.sq_mem_of_index_two (H := U.subgroupOf S) hU ⟨y, hyS⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa [sq] using h

theorem mul_self_mem_of_mul_mem {D : Subgroup G} {uv y : G}
    (huvD : uv ∈ Subgroup.normalizer (D : Set G)) (huv : uv * uv = 1) (hy : y * uv ∈ D) :
    y * y ∈ D := by
  have huv' : uv⁻¹ = uv := inv_eq_of_mul_eq_one_right huv
  have h1 : uv * (y * uv) * uv⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp huvD _).mp hy
  have h2 := D.mul_mem hy h1
  have e : y * uv * (uv * (y * uv) * uv⁻¹) = y * y := by
    rw [huv']
    calc y * uv * (uv * (y * uv) * uv) = y * (uv * uv) * y * (uv * uv) := by group
      _ = y * y := by rw [huv]; group
  rwa [e] at h2

theorem pow_mem_of_mul_self {D U : Subgroup G} {uv y z : G} {l : ℕ} (hl : 1 ≤ l)
    (huvD : uv ∈ Subgroup.normalizer (D : Set G)) (huv : uv * uv = 1) (hz2 : z * z = 1)
    (hyU : y * y ∈ U) (h5 : y * y ∈ D ∨ y * y * uv ∈ D)
    (h6 : ∀ y ∈ U, y * uv ∈ D → y * y = 1 → ¬ IsConj y z) (hconj : IsConj (y ^ 2 ^ l) z) :
    y ^ 2 ^ l ∈ D := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' hl
  have hsq : y ^ 2 ^ (l + 1) = (y * y) ^ 2 ^ l := by rw [pow_succ', pow_mul, sq]
  rw [hsq] at hconj ⊢
  rcases h5 with h5 | h5
  · exact D.pow_mem h5 _
  · rcases Nat.eq_zero_or_pos l with rfl | hl'
    · rw [pow_zero, pow_one] at hconj
      exact absurd hconj (h6 _ hyU h5 (mul_self_eq_one_of_isConj hconj hz2))
    · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' hl'
      rw [pow_succ', pow_mul, sq]
      exact D.pow_mem (mul_self_mem_of_mul_mem huvD huv h5) _

theorem exists_conj_pow_eq {D U P : Subgroup G} {y z : G} {l : ℕ} (hPU : P ≤ U)
    (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z)
    (hD : y ^ 2 ^ l ∈ D) (hconj : IsConj (y ^ 2 ^ l) z) :
    ∃ p ∈ U, (p⁻¹ * y * p) ^ 2 ^ l = z := by
  obtain ⟨p, hpP, hp⟩ := h3 _ hD (mul_self_eq_one_of_isConj hconj hz2) (ne_one_of_isConj hconj hz1)
    hconj
  exact ⟨p, hPU hpP, by rw [conj_pow', hp]⟩

theorem conj_not_mem {D U P : Subgroup G} {x z uv : G} {j : ℕ} (hPU : P ≤ U) (hj : 1 ≤ j)
    (hxz : x ^ 2 ^ j = z) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (huvD : uv ∈ Subgroup.normalizer (D : Set G)) (huv : uv * uv = 1)
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z)
    (h4 : ∀ y ∈ U, y * z = z * y → y ^ 2 ^ j ≠ z)
    (h5 : ∀ y ∈ U, y * y ∈ D ∨ y * y * uv ∈ D)
    (h6 : ∀ y ∈ U, y * uv ∈ D → y * y = 1 → ¬ IsConj y z) (g : G) : g⁻¹ * x * g ∉ U := by
  intro hyU
  have hrz : IsConj ((g⁻¹ * x * g) ^ 2 ^ j) z := by
    rw [conj_pow', hxz]; exact isConj_of_conj_eq rfl
  have hrD := pow_mem_of_mul_self hj huvD huv hz2 (U.mul_mem hyU hyU) (h5 _ hyU) h6 hrz
  obtain ⟨p, hpU, hp⟩ := exists_conj_pow_eq hPU hz2 hz1 h3 hrD hrz
  have hy'U : p⁻¹ * (g⁻¹ * x * g) * p ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hpU) hyU) hpU
  refine h4 _ hy'U ?_ hp
  rw [← hp]
  exact ((Commute.refl _).pow_right _).eq

theorem false_of_harada [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    {D U P : Subgroup G} {x z uv : G} {j : ℕ} (hUS : U ≤ S) (hU : U.relIndex S = 2)
    (hPU : P ≤ U) (hxS : x ∈ S) (hxU : x ∉ U) (hxz : x ^ 2 ^ j = z) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (huvD : uv ∈ Subgroup.normalizer (D : Set G)) (huv : uv * uv = 1)
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z)
    (h5 : ∀ y ∈ (S : Subgroup G), y * y ∈ D ∨ y * y * uv ∈ D)
    (h6 : ∀ y ∈ U, y * uv ∈ D → y * y = 1 → ¬ IsConj y z)
    (h6' : ∀ y ∈ (S : Subgroup G), y ∉ U → y * y = 1 → ¬ IsConj y z)
    (h8 : ∀ y ∈ (S : Subgroup G), y ∉ U → ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = z → y ^ 2 ^ j ≠ 1)
    (hconj : ∀ g : G, g⁻¹ * x * g ∉ U) : False := by
  refine EvenSporadicStandard.TwoHS.false_of_thompson_pow hnonab S.isPGroup' S.not_dvd_index hUS
    hU hxS hxU (fun g k hgS => ?_) hconj
  by_contra hgU
  set y := g⁻¹ * x ^ (2 * k) * g with hy
  have hk : x ^ (2 * k) ≠ 1 := by
    rintro h1; apply hgU; rw [hy, h1]; simp
  obtain ⟨l, hlj, hl, hlj'⟩ := exists_pow_eq_of_even hxz hz2 hz1 hk
  have hrz : IsConj (y ^ 2 ^ l) z := by rw [hy, conj_pow', hl]; exact isConj_of_conj_eq rfl
  rcases Nat.eq_zero_or_pos l with rfl | hl1
  · rw [pow_zero, pow_one] at hrz
    exact h6' y hgS hgU (mul_self_eq_one_of_isConj hrz hz2) hrz
  · have hrD := pow_mem_of_mul_self hl1 huvD huv hz2 (mul_self_mem_of_relIndex hU hgS) (h5 y hgS)
      h6 hrz
    obtain ⟨p, hpU, hp⟩ := exists_conj_pow_eq hPU hz2 hz1 h3 hrD hrz
    have hy'S : p⁻¹ * y * p ∈ (S : Subgroup G) :=
      (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem (hUS hpU)) hgS)
        (hUS hpU)
    have hy'U : p⁻¹ * y * p ∉ U := fun h' => hgU (by
      have := U.mul_mem (U.mul_mem hpU h') (U.inv_mem hpU)
      rwa [show p * (p⁻¹ * y * p) * p⁻¹ = y by group] at this)
    exact h8 _ hy'S hy'U l hl1 hp (by rw [conj_pow', hy, conj_pow', hlj']; group)

theorem exists_conj_le_centralizer (S : Sylow 2 G) {D P : Subgroup G} {z : G}
    (hD : IsMulCommutative D) (hDS : D ≤ S)
    (hSD : (S : Subgroup G) ≤ Subgroup.normalizer (D : Set G)) (hPS : P ≤ S) (hzD : z ∈ D)
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z)
    (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (h9 : ∀ X : Subgroup G, X ≤ (S : Subgroup G) ⊓ Subgroup.centralizer {z} →
      IsMulCommutative X → Nat.card X = Nat.card D → X = D)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQz : Q ≤ Subgroup.centralizer {z}) :
    ∃ k ∈ Subgroup.centralizer {z}, ∀ q ∈ Q, k⁻¹ * q * k ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q₁ := (S : Subgroup G) ⊓ Subgroup.centralizer {z} with hQ₁
  have hDQ₁ : D ≤ Q₁ := fun d hd => Subgroup.mem_inf.2 ⟨hDS hd,
    Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (hD.is_comm.comm ⟨d, hd⟩ ⟨z, hzD⟩))⟩
  have hmax : ∀ {Q' : Subgroup G}, IsPGroup 2 Q' → Q' ≤ Subgroup.centralizer {z} → Q₁ ≤ Q' →
      Q' = Q₁ := by
    intro Q' hQ' hQ'z hQ₁Q'
    by_contra hne
    have hlt : Q₁ < Q' := lt_of_le_of_ne hQ₁Q' (Ne.symm hne)
    set R := Q' ⊓ Subgroup.normalizer (Q₁ : Set G) with hRdef
    have hRgt : Q₁ < R := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hQ' hlt
    have hRp : IsPGroup 2 R := hQ'.to_le inf_le_left
    have hRN : R ≤ Subgroup.normalizer (D : Set G) := by
      intro g hg
      have hgN : g ∈ Subgroup.normalizer (Q₁ : Set G) := hg.2
      have hX : D.map (MulAut.conj g).toMonoidHom = D := by
        refine h9 _ ?_ ?_ ?_
        · rintro _ ⟨d, hd, rfl⟩
          exact (Subgroup.mem_normalizer_iff.mp hgN d).mp (hDQ₁ hd)
        · refine ⟨⟨fun a b => ?_⟩⟩
          obtain ⟨_, a', ha', rfl⟩ := a
          obtain ⟨_, b', hb', rfl⟩ := b
          apply Subtype.ext
          change (MulAut.conj g).toMonoidHom a' * (MulAut.conj g).toMonoidHom b' =
            (MulAut.conj g).toMonoidHom b' * (MulAut.conj g).toMonoidHom a'
          rw [← map_mul, ← map_mul, show a' * b' = b' * a' from
            congrArg Subtype.val (hD.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)]
        · exact Stroth76.card_map_conj g D
      rw [Subgroup.mem_normalizer_iff]
      intro d
      refine ⟨fun hd => ?_, fun hd => ?_⟩
      · rw [← hX]; exact ⟨d, hd, rfl⟩
      · rw [← hX] at hd
        obtain ⟨d', hd', he⟩ := hd
        have he' : g * d' * g⁻¹ = g * d * g⁻¹ := he
        rwa [← mul_left_cancel (mul_right_cancel he')]
    obtain ⟨c, hcN, hc⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow
      (Subgroup.normalizer (D : Set G)) S hSD R hRN hRp
    have hz'D : c * z * c⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hcN z).mp hzD
    have hz'z : IsConj (c * z * c⁻¹) z := isConj_of_conj_eq (g := c⁻¹) (by group)
    obtain ⟨p, hpP, hp⟩ := h3 _ hz'D (mul_self_eq_one_of_isConj hz'z hz2)
      (ne_one_of_isConj hz'z hz1) hz'z
    have hle : R.map (MulAut.conj (p⁻¹ * c)).toMonoidHom ≤ Q₁ := by
      rintro _ ⟨r, hr, rfl⟩
      have hcr : c * r * c⁻¹ ∈ (S : Subgroup G) := hc ⟨r, hr, rfl⟩
      have hpS : p ∈ (S : Subgroup G) := hPS hpP
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have := (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem
          ((S : Subgroup G).inv_mem hpS) hcr) hpS
        rwa [show p⁻¹ * (c * r * c⁻¹) * p = p⁻¹ * c * r * (p⁻¹ * c)⁻¹ by group] at this
      · have hrz : r * z = z * r := Subgroup.mem_centralizer_singleton_iff.1 (hQ'z hr.1)
        have hw : p⁻¹ * c * z * (p⁻¹ * c)⁻¹ = z := by
          calc p⁻¹ * c * z * (p⁻¹ * c)⁻¹ = p⁻¹ * (c * z * c⁻¹) * p := by group
            _ = z := hp
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc p⁻¹ * c * r * (p⁻¹ * c)⁻¹ * z
            = p⁻¹ * c * r * (p⁻¹ * c)⁻¹ * (p⁻¹ * c * z * (p⁻¹ * c)⁻¹) := by rw [hw]
          _ = p⁻¹ * c * (r * z) * (p⁻¹ * c)⁻¹ := by group
          _ = p⁻¹ * c * (z * r) * (p⁻¹ * c)⁻¹ := by rw [hrz]
          _ = p⁻¹ * c * z * (p⁻¹ * c)⁻¹ * (p⁻¹ * c * r * (p⁻¹ * c)⁻¹) := by group
          _ = z * (p⁻¹ * c * r * (p⁻¹ * c)⁻¹) := by rw [hw]
    have h1 : Nat.card R ≤ Nat.card Q₁ := by
      rw [← Stroth76.card_map_conj (p⁻¹ * c) R]
      exact Subgroup.card_le_of_le hle
    have h2 : Nat.card Q₁ < Nat.card R := Subgroup.card_lt_of_lt hRgt
    omega
  exact Stroth76.exists_conj_le_of_maximal inf_le_right (S.isPGroup'.to_le inf_le_left) hmax hQ
    hQz |>.imp fun k ⟨hk, hkQ⟩ => ⟨hk, fun q hq => (hkQ q hq).1⟩

theorem not_isConj_of_e16 (S : Sylow 2 G) {D P : Subgroup G} {z y : G}
    (hD : IsMulCommutative D) (hDS : D ≤ S)
    (hSD : (S : Subgroup G) ≤ Subgroup.normalizer (D : Set G)) (hPS : P ≤ S) (hzD : z ∈ D)
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z)
    (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (h7 : ∀ E : Subgroup G, E ≤ (S : Subgroup G) ⊓ Subgroup.centralizer {z} →
      (∀ e ∈ E, e * e = 1) → Nat.card E ≠ 16)
    (h9 : ∀ X : Subgroup G, X ≤ (S : Subgroup G) ⊓ Subgroup.centralizer {z} →
      IsMulCommutative X → Nat.card X = Nat.card D → X = D)
    (hy : ∃ E : Subgroup G, E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧
      Nat.card E = 16) :
    ¬ IsConj y z := by
  intro hyz
  obtain ⟨E, hEy, hE2, hE16⟩ := hy
  obtain ⟨c, hc⟩ := isConj_iff.1 hyz
  set E' := E.map (MulAut.conj c).toMonoidHom with hE'
  have hE'2 : ∀ e ∈ E', e * e = 1 := by
    rintro _ ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * e * c⁻¹ * (c * e * c⁻¹) = c * (e * e) * c⁻¹ := by group
      _ = 1 := by rw [hE2 e he]; group
  have hE'z : E' ≤ Subgroup.centralizer {z} := by
    rintro _ ⟨e, he, rfl⟩
    have hey : e * y = y * e := Subgroup.mem_centralizer_singleton_iff.1 (hEy he)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    calc c * e * c⁻¹ * (c * y * c⁻¹) = c * (e * y) * c⁻¹ := by group
      _ = c * (y * e) * c⁻¹ := by rw [hey]
      _ = c * y * c⁻¹ * (c * e * c⁻¹) := by group
  have hE'p : IsPGroup 2 E' := fun e => ⟨1, Subtype.ext (by simpa [sq] using hE'2 e e.2)⟩
  obtain ⟨k, hk, hkE⟩ := exists_conj_le_centralizer S hD hDS hSD hPS hzD h3 hz2 hz1 h9 hE'p hE'z
  refine h7 (E'.map (MulAut.conj k⁻¹).toMonoidHom) ?_ ?_ ?_
  · rintro _ ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.mem_inf.2 ⟨hkE e he, ?_⟩
    exact (Subgroup.centralizer {z}).mul_mem ((Subgroup.centralizer {z}).mul_mem
      ((Subgroup.centralizer {z}).inv_mem hk) (hE'z he)) hk
  · rintro _ ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k⁻¹ * e * k⁻¹⁻¹ * (k⁻¹ * e * k⁻¹⁻¹) = k⁻¹ * (e * e) * k := by group
      _ = 1 := by rw [hE'2 e he]; group
  · rw [Stroth76.card_map_conj, hE', Stroth76.card_map_conj, hE16]

end CFSG.CGT.Stroth77.Stroth42
