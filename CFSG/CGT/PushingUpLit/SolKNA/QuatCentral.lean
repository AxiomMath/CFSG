module

import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open scoped commutatorElement

section Aux

variable {G : Type} [Group G]

private structure Inverted (R N : Subgroup G) : Prop where
  le : N ≤ R
  mul_mem_iff : ∀ a ∈ R, ∀ b ∈ R, a * b ∈ N ↔ (a ∈ N ↔ b ∈ N)
  exists_not_mem : ∃ x ∈ R, x ∉ N
  comm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a
  inv : ∀ x ∈ R, x ∉ N → ∀ n ∈ N, x * n * x⁻¹ = n⁻¹
  exists_sq_ne : ∃ n ∈ N, n * n ≠ 1

namespace Inverted

variable {R N : Subgroup G}

private theorem of_relIndex (hNR : N ≤ R) (hidx : N.relIndex R = 2)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hnel : ∃ n ∈ N, n * n ≠ 1)
    (hinv : ∀ x ∈ R, x ∉ N → ∀ n ∈ N, x * n * x⁻¹ = n⁻¹) : Inverted R N where
  le := hNR
  mul_mem_iff a ha b hb :=
    Subgroup.mul_mem_iff_of_index_two (H := N.subgroupOf R) hidx (a := (⟨a, ha⟩ : R))
      (b := (⟨b, hb⟩ : R))
  exists_not_mem := by
    by_contra hcon
    have hle : R ≤ N := fun x hx => by_contra fun hxN => hcon ⟨x, hx, hxN⟩
    have := Subgroup.relIndex_eq_one.mpr hle
    omega
  comm := hcomm
  inv := hinv
  exists_sq_ne := hnel

private theorem mem_of_central (h : Inverted R N) {y : G} (hyR : y ∈ R)
    (hy : ∀ r ∈ R, r * y = y * r) : y ∈ N := by
  by_contra hyN
  obtain ⟨n, hnN, hn⟩ := h.exists_sq_ne
  have h1 := h.inv y hyR hyN n hnN
  have h3 : y * n * y⁻¹ = n := by
    rw [← hy n (h.le hnN)]
    group
  exact hn (mul_eq_one_iff_eq_inv.mpr (h3.symm.trans h1))

private theorem map (h : Inverted R N) (α : MulAut G) (hα : R.map α.toMonoidHom = R) :
    Inverted R (N.map α.toMonoidHom) := by
  have hR : ∀ x : G, x ∈ R ↔ α.symm x ∈ R := fun x => by
    rw [← Subgroup.mem_map_equiv (f := α), hα]
  have hN : ∀ x : G, x ∈ N.map α.toMonoidHom ↔ α.symm x ∈ N := fun x =>
    Subgroup.mem_map_equiv
  refine ⟨fun x hx => ?_, fun a ha b hb => ?_, ?_, fun a ha b hb => ?_,
    fun x hx hxN n hn => ?_, ?_⟩
  · exact (hR x).mpr (h.le ((hN x).mp hx))
  · rw [hN, hN, hN, map_mul]
    exact h.mul_mem_iff _ ((hR a).mp ha) _ ((hR b).mp hb)
  · obtain ⟨x, hx, hxN⟩ := h.exists_not_mem
    refine ⟨α x, (hR _).mpr (by simpa using hx), fun hmem => hxN ?_⟩
    simpa [hN] using hmem
  · rw [hN] at ha hb
    apply α.symm.injective
    rw [map_mul, map_mul]
    exact h.comm _ ha _ hb
  · rw [hN] at hn hxN
    apply α.symm.injective
    rw [map_mul, map_mul, map_inv, map_inv]
    exact h.inv _ ((hR x).mp hx) hxN _ hn
  · obtain ⟨n, hn, hsq⟩ := h.exists_sq_ne
    refine ⟨α n, (hN _).mpr (by simpa using hn), fun h1 => hsq ?_⟩
    apply α.injective
    rw [map_mul, map_one]
    exact h1

end Inverted

private theorem mul_mul_self_eq {a b : G} (h : b * a * b⁻¹ = a⁻¹) :
    a * b * (a * b) = b * b := by
  calc a * b * (a * b) = a * (b * a * b⁻¹) * (b * b) := by group
    _ = b * b := by rw [h]; group

private theorem mul_self_eq_of_inv {a b : G} (h1 : b * a * b⁻¹ = a⁻¹) (h2 : a * b * a⁻¹ = b⁻¹) :
    a * a = b * b := by
  calc a * a = b * a * (b * a) := (mul_mul_self_eq h2).symm
    _ = b * (a * b * (a * b)) * b⁻¹ := by group
    _ = b * (b * b) * b⁻¹ := by rw [mul_mul_self_eq h1]
    _ = b * b := by group

section Pair

variable {R A B : Subgroup G}

private theorem not_le_of_ne (hA : Inverted R A) (hB : Inverted R B) (hAB : A ≠ B) :
    ¬ B ≤ A := by
  intro hBA
  refine hAB (le_antisymm (fun n hnA => ?_) hBA)
  by_contra hnB
  obtain ⟨x, hxR, hxA⟩ := hA.exists_not_mem
  apply hxA
  by_cases hxB : x ∈ B
  · exact hBA hxB
  · have hxn : x * n ∈ B :=
      (hB.mul_mem_iff x hxR n (hA.le hnA)).mpr (by simp [hxB, hnB])
    exact (Subgroup.mul_mem_cancel_right A hnA).mp (hBA hxn)

private theorem exists_mul_of_not_le (hA : Inverted R A) (hB : Inverted R B) (hBA : ¬ B ≤ A) :
    ∀ r ∈ R, ∃ a ∈ A, ∃ b ∈ B, r = a * b := by
  obtain ⟨x, hxB, hxA⟩ := IsConcreteLE.not_le_iff_exists.mp hBA
  intro r hr
  by_cases hrA : r ∈ A
  · exact ⟨r, hrA, 1, B.one_mem, (mul_one r).symm⟩
  · refine ⟨r * x⁻¹, ?_, x, hxB, by group⟩
    exact (hA.mul_mem_iff r hr x⁻¹ (R.inv_mem (hB.le hxB))).mpr (by simp [hrA, hxA])

private theorem mul_self_eq_one_of_mem_inf (hA : Inverted R A) (hB : Inverted R B)
    (hBA : ¬ B ≤ A) {z : G} (hzA : z ∈ A) (hzB : z ∈ B) : z * z = 1 := by
  obtain ⟨x, hxB, hxA⟩ := IsConcreteLE.not_le_iff_exists.mp hBA
  have h1 := hA.inv x (hB.le hxB) hxA z hzA
  rw [hB.comm x hxB z hzB, mul_inv_cancel_right] at h1
  exact mul_eq_one_iff_eq_inv.mpr h1

private theorem comm_of_mem_inf (hA : Inverted R A) (hB : Inverted R B) (hBA : ¬ B ≤ A)
    {z : G} (hzA : z ∈ A) (hzB : z ∈ B) : ∀ r ∈ R, r * z = z * r := by
  intro r hr
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_not_le hA hB hBA r hr
  calc a * b * z = a * (b * z) := mul_assoc _ _ _
    _ = a * (z * b) := by rw [hB.comm b hb z hzB]
    _ = a * z * b := (mul_assoc _ _ _).symm
    _ = z * a * b := by rw [hA.comm a ha z hzA]
    _ = z * (a * b) := mul_assoc _ _ _

private theorem mul_self_eq_of_mem (hA : Inverted R A) (hB : Inverted R B) {a b : G}
    (ha : a ∈ A) (haB : a ∉ B) (hb : b ∈ B) (hbA : b ∉ A) : a * a = b * b :=
  mul_self_eq_of_inv (hA.inv b (hB.le hb) hbA a ha) (hB.inv a (hA.le ha) haB b hb)

private theorem relIndex_eq_two (hAR : A ≤ R) (hB : Inverted R B) {a : G} (ha : a ∈ A)
    (haB : a ∉ B) : B.relIndex A = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨a, ha⟩, fun b => ?_⟩
  have h := hB.mul_mem_iff b (hAR b.2) a (hAR ha)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hb : (b : G) ∈ B <;> simp [h, hb, haB]

private theorem two_inverted [Finite G] (hA : Inverted R A) (hB : Inverted R B)
    (hidx : A.relIndex R = 2) (hAB : A ≠ B) (hrank : 2 ≤ CFSG.Open.pRank 2 R) :
    ∃ c : G, c ∈ R ∧ c ≠ 1 ∧ c * c = 1 ∧ (∀ r ∈ R, r * c = c * r) ∧
      ⁅R, R⁆ = Subgroup.zpowers c ∧
      (∀ y ∈ R, y ∈ R ⊓ Subgroup.centralizer (R : Set G) → y * y = 1) ∧
      (∀ y ∈ R, y ∉ R ⊓ Subgroup.centralizer (R : Set G) → y * y = c) ∧
      (R ⊓ Subgroup.centralizer (R : Set G)).relIndex R = 4 ∧
      4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer (R : Set G)) ∧
      R ⊓ Subgroup.centralizer (R : Set G) ≤ A := by
  have hBA : ¬ B ≤ A := not_le_of_ne hA hB hAB
  obtain ⟨n₀, hn₀A, hn₀sq⟩ := hA.exists_sq_ne
  have hn₀B : n₀ ∉ B := fun h => hn₀sq (mul_self_eq_one_of_mem_inf hA hB hBA hn₀A h)
  obtain ⟨b₀, hb₀B, hb₀A⟩ := IsConcreteLE.not_le_iff_exists.mp hBA
  have hn₀R : n₀ ∈ R := hA.le hn₀A
  have hb₀R : b₀ ∈ R := hB.le hb₀B
  have hcA : n₀ * n₀ ∈ A := A.mul_mem hn₀A hn₀A
  have hcB : n₀ * n₀ ∈ B := (hB.mul_mem_iff n₀ hn₀R n₀ hn₀R).mpr Iff.rfl
  have hcc : n₀ * n₀ * (n₀ * n₀) = 1 := mul_self_eq_one_of_mem_inf hA hB hBA hcA hcB
  have hSB : ∀ b ∈ B, b ∉ A → b * b = n₀ * n₀ := fun b hb hbA =>
    (mul_self_eq_of_mem hA hB hn₀A hn₀B hb hbA).symm
  have hSA : ∀ a ∈ A, a ∉ B → a * a = n₀ * n₀ := fun a ha haB =>
    (mul_self_eq_of_mem hA hB ha haB hb₀B hb₀A).trans (hSB b₀ hb₀B hb₀A)
  have hsq : ∀ y ∈ R, y ∉ A ⊓ B → y * y = n₀ * n₀ := by
    intro y hy hyAB
    by_cases hyA : y ∈ A
    · exact hSA y hyA fun hyB => hyAB ⟨hyA, hyB⟩
    · by_cases hyB : y ∈ B
      · exact hSB y hyB hyA
      · obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_not_le hA hB hBA y hy
        have hbA : b ∉ A := fun h => hyA (A.mul_mem ha h)
        rw [mul_mul_self_eq (hA.inv b (hB.le hb) hbA a ha)]
        exact hSB b hb hbA
  have hZ : R ⊓ Subgroup.centralizer (R : Set G) = A ⊓ B := by
    refine le_antisymm (fun y hy => ?_) (fun z hz => ?_)
    · have hcen : ∀ r ∈ R, r * y = y * r := Subgroup.mem_centralizer_iff.mp hy.2
      exact ⟨hA.mem_of_central hy.1 hcen, hB.mem_of_central hy.1 hcen⟩
    · exact ⟨hA.le hz.1, Subgroup.mem_centralizer_iff.mpr
        (comm_of_mem_inf hA hB hBA hz.1 hz.2)⟩
  have hcen : ∀ u ∈ Subgroup.zpowers (n₀ * n₀), ∀ s ∈ R, s * u = u * s := by
    intro u hu s hs
    have hle : Subgroup.zpowers (n₀ * n₀) ≤ Subgroup.centralizer (R : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr
        (comm_of_mem_inf hA hB hBA hcA hcB))
    exact Subgroup.mem_centralizer_iff.mp (hle hu) s hs
  have hsqmem : ∀ y ∈ R, y * y ∈ Subgroup.zpowers (n₀ * n₀) := by
    intro y hy
    by_cases hyZ : y ∈ A ⊓ B
    · rw [mul_self_eq_one_of_mem_inf hA hB hBA hyZ.1 hyZ.2]
      exact one_mem _
    · rw [hsq y hy hyZ]
      exact Subgroup.mem_zpowers _
  refine ⟨n₀ * n₀, hA.le hcA, hn₀sq, hcc, comm_of_mem_inf hA hB hBA hcA hcB, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · refine le_antisymm (Subgroup.commutator_le.mpr fun r hr s hs => ?_) ?_
    · have hu := hcen (r * r)⁻¹ (inv_mem (hsqmem r hr)) s hs
      have e : r * s * r⁻¹ * s⁻¹ = r * s * (r * s) * ((r * r)⁻¹ * (s * s)⁻¹) :=
        calc r * s * r⁻¹ * s⁻¹ = r * s * r * ((r * r)⁻¹ * s) * (s * s)⁻¹ := by group
          _ = r * s * r * (s * (r * r)⁻¹) * (s * s)⁻¹ := by rw [hu]
          _ = r * s * (r * s) * ((r * r)⁻¹ * (s * s)⁻¹) := by group
      rw [commutatorElement_def, e]
      exact mul_mem (hsqmem (r * s) (R.mul_mem hr hs))
        (mul_mem (inv_mem (hsqmem r hr)) (inv_mem (hsqmem s hs)))
    · rw [Subgroup.zpowers_le]
      have h := Subgroup.commutator_mem_commutator hb₀R hn₀R
      have h2 : b₀ * n₀ * b₀⁻¹ * n₀⁻¹ = n₀ * n₀ := by
        rw [hA.inv b₀ hb₀R hb₀A n₀ hn₀A, ← mul_inv_rev]
        exact inv_eq_of_mul_eq_one_right hcc
      rwa [commutatorElement_def, h2] at h
  · intro y _ hy
    rw [hZ] at hy
    exact mul_self_eq_one_of_mem_inf hA hB hBA hy.1 hy.2
  · intro y hy hyZ
    rw [hZ] at hyZ
    exact hsq y hy hyZ
  · rw [hZ]
    have h := Subgroup.relIndex_mul_relIndex (A ⊓ B) A R inf_le_left hA.le
    rw [Subgroup.inf_relIndex_left, relIndex_eq_two hA.le hB hn₀A hn₀B, hidx] at h
    omega
  · obtain ⟨E, hER, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) R
    have hEZ : E ≤ R ⊓ Subgroup.centralizer (R : Set G) := by
      intro e he
      by_contra hnot
      have h1 : e * e = n₀ * n₀ := by
        refine hsq e (hER he) fun h => hnot ?_
        rw [hZ]
        exact h
      have h2 : e * e = 1 := by simpa [pow_two] using hE.2 e he
      exact hn₀sq (h1.symm.trans h2)
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 R := Nat.pow_le_pow_right (by norm_num) hrank
      _ = Nat.card E := hEcard.symm
      _ ≤ _ := Subgroup.card_le_of_le hEZ
  · rw [hZ]
    exact inf_le_left

end Pair

end Aux

theorem caseI_dichotomy {G : Type} [Group G] [Finite G] {R N : Subgroup G}
    (hR2 : IsPGroup 2 R) (hNR : N ≤ R) (hidx : N.relIndex R = 2)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hnel : ∃ n ∈ N, n * n ≠ 1)
    (hinv : ∀ x ∈ R, x ∉ N → ∀ n ∈ N, x * n * x⁻¹ = n⁻¹)
    (hrank : 2 ≤ CFSG.Open.pRank 2 R)
    (α : MulAut G) (hα : R.map α.toMonoidHom = R) (hne : N.map α.toMonoidHom ≠ N) :
    ∃ c : G, c ∈ R ∧ c ≠ 1 ∧ c * c = 1 ∧ (∀ r ∈ R, r * c = c * r) ∧
      ⁅R, R⁆ = Subgroup.zpowers c ∧
      (∀ y ∈ R, y ∈ R ⊓ Subgroup.centralizer (R : Set G) → y * y = 1) ∧
      (∀ y ∈ R, y ∉ R ⊓ Subgroup.centralizer (R : Set G) → y * y = c) ∧
      (R ⊓ Subgroup.centralizer (R : Set G)).relIndex R = 4 ∧
      4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer (R : Set G)) ∧
      R ⊓ Subgroup.centralizer (R : Set G) ≤ N := by
  have _ := hR2
  have hN := Inverted.of_relIndex hNR hidx hcomm hnel hinv
  exact two_inverted hN (hN.map α hα) hidx hne.symm hrank

end CFSG.CGT.PushingUpLit.SolKNA
