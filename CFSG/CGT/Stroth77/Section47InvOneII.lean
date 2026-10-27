module

public import CFSG.CGT.Stroth76.SylowCwConj
public import CFSG.CGT.Stroth77.Section47Fus
public import CFSG.CGT.Stroth77.Section42

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace Stroth47Inv1

theorem not_isConj_of_card {S : Subgroup G} {z y : G} {n : ℕ}
    (hsyl : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {z} →
      ∃ k ∈ Subgroup.centralizer {z}, ∀ q ∈ Q, k⁻¹ * q * k ∈ S)
    (hS : ∀ A : Subgroup G, A ≤ S ⊓ Subgroup.centralizer {z} → (∀ x ∈ A, x * x = 1) →
      Nat.card A ≠ n)
    {A : Subgroup G} (hA : A ≤ Subgroup.centralizer {y}) (hA2 : ∀ x ∈ A, x * x = 1)
    (hAn : Nat.card A = n) : ¬ IsConj y z := by
  have hfin : Finite G := inferInstance
  intro hconj
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  set B : Subgroup G := A.map (MulAut.conj c).toMonoidHom with hB
  have hBz : B ≤ Subgroup.centralizer {z} := by
    rintro b ⟨a, ha, rfl⟩
    have hay : a * y = y * a := Subgroup.mem_centralizer_singleton_iff.1 (hA ha)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hc]
    calc c * a * c⁻¹ * (c * y * c⁻¹) = c * (a * y) * c⁻¹ := by group
      _ = c * (y * a) * c⁻¹ := by rw [hay]
      _ = c * y * c⁻¹ * (c * a * c⁻¹) := by group
  have hB2 : ∀ b ∈ B, b * b = 1 := by
    rintro b ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
      _ = 1 := by rw [hA2 a ha]; group
  have hBp : IsPGroup 2 B := fun b => ⟨1, Subtype.ext (by simpa [sq] using hB2 b b.2)⟩
  obtain ⟨k, hk, hkB⟩ := hsyl B hBp hBz
  have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.1 hk
  have hkiz : k⁻¹ * z = z * k⁻¹ := by
    calc k⁻¹ * z = k⁻¹ * (z * k) * k⁻¹ := by group
      _ = k⁻¹ * (k * z) * k⁻¹ := by rw [← hkz]
      _ = z * k⁻¹ := by group
  refine hS (B.map (MulAut.conj (k⁻¹)).toMonoidHom) ?_ ?_ ?_
  · rintro d ⟨b, hb, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hkB b hb
    have hbz : b * z = z * b := Subgroup.mem_centralizer_singleton_iff.1 (hBz hb)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc k⁻¹ * b * k * z = k⁻¹ * b * (k * z) := by group
      _ = k⁻¹ * b * (z * k) := by rw [hkz]
      _ = k⁻¹ * (b * z) * k := by group
      _ = k⁻¹ * (z * b) * k := by rw [hbz]
      _ = (k⁻¹ * z) * b * k := by group
      _ = (z * k⁻¹) * b * k := by rw [hkiz]
      _ = z * (k⁻¹ * b * k) := by group
  · rintro d ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc k⁻¹ * b * k * (k⁻¹ * b * k) = k⁻¹ * (b * b) * k := by group
      _ = 1 := by rw [hB2 b hb]; group
  · rw [Subgroup.card_map_of_injective (MulAut.conj (k⁻¹)).injective,
      Subgroup.card_map_of_injective (MulAut.conj c).injective, hAn]

theorem cabuv_isConj_of_two_le {S T Du : Subgroup G} {c₁ c₂ a₁ u x : G}
    (hT : T = S ⊓ Subgroup.centralizer {c₁})
    (hsyl : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {c₁} →
      ∃ k ∈ Subgroup.centralizer {c₁}, ∀ q ∈ Q, k⁻¹ * q * k ∈ S)
    (hS32 : ∀ A : Subgroup G, A ≤ T → (∀ y ∈ A, y * y = 1) → Nat.card A ≠ 32)
    (hDu : ∀ y ∈ Du, y * y = 1 → y ≠ 1 → IsConj y c₁ ∨ IsConj y a₁)
    (hc₂ : ∀ k ∈ T, k ∉ Du → c₂⁻¹ * k * c₂ = c₁ * k)
    (hu : IsConj u c₁) (hux : u * x = x * u) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hxuu : IsConj (u * x) u)
    (hx32 : ∃ A : Subgroup G, A ≤ Subgroup.centralizer {x} ∧ (∀ y ∈ A, y * y = 1) ∧
      Nat.card A = 32) :
    IsConj x a₁ := by
  classical
  have hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcu⟩ := isConj_iff.1 hu
  set t : G := c * x * c⁻¹ with ht
  have ht2 : t * t = 1 := by
    rw [ht]
    calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have ht1 : t ≠ 1 := by
    rw [ht]
    intro h'
    apply hx1
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [h']; group
  have htC : t * c₁ = c₁ * t := by
    rw [ht, ← hcu]
    calc c * x * c⁻¹ * (c * u * c⁻¹) = c * (x * u) * c⁻¹ := by group
      _ = c * (u * x) * c⁻¹ := by rw [hux]
      _ = c * u * c⁻¹ * (c * x * c⁻¹) := by group
  have hQp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers,
        @orderOf_eq_prime G _ t 2 hFact (by rw [pow_two]; exact ht2) ht1, pow_one])
  have hQc : Subgroup.zpowers t ≤ Subgroup.centralizer {c₁} := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.2 htC
  obtain ⟨k, hkC, hkQ⟩ := hsyl (Subgroup.zpowers t) hQp hQc
  set y : G := k⁻¹ * t * k with hy
  have hyS : y ∈ S := hkQ t (Subgroup.mem_zpowers t)
  have hkc₁ : k * c₁ = c₁ * k := Subgroup.mem_centralizer_singleton_iff.1 hkC
  have hkc₁' : k⁻¹ * c₁ * k = c₁ := by
    calc k⁻¹ * c₁ * k = k⁻¹ * (c₁ * k) := by group
      _ = k⁻¹ * (k * c₁) := by rw [← hkc₁]
      _ = c₁ := by group
  have hyC : y * c₁ = c₁ * y := by
    have hmem : y ∈ Subgroup.centralizer {c₁} := by
      rw [hy]
      exact (Subgroup.centralizer {c₁}).mul_mem
        ((Subgroup.centralizer {c₁}).mul_mem
          ((Subgroup.centralizer {c₁}).inv_mem hkC)
          (Subgroup.mem_centralizer_singleton_iff.2 htC)) hkC
    exact Subgroup.mem_centralizer_singleton_iff.1 hmem
  have hy2 : y * y = 1 := by
    rw [hy]
    calc k⁻¹ * t * k * (k⁻¹ * t * k) = k⁻¹ * (t * t) * k := by group
      _ = 1 := by rw [ht2]; group
  have hy1 : y ≠ 1 := by
    rw [hy]
    intro h'
    apply ht1
    calc t = k * (k⁻¹ * t * k) * k⁻¹ := by group
      _ = 1 := by rw [h']; group
  have hyT : y ∈ T := by
    rw [hT]
    exact Subgroup.mem_inf.2 ⟨hyS, Subgroup.mem_centralizer_singleton_iff.2 hyC⟩
  obtain ⟨A, hAx, hA2, hA32⟩ := hx32
  have hS' : ∀ B : Subgroup G, B ≤ S ⊓ Subgroup.centralizer {c₁} →
      (∀ y ∈ B, y * y = 1) → Nat.card B ≠ 32 := by
    intro B hB hB2 hBc
    exact hS32 B (by rw [hT]; exact hB) hB2 hBc
  have hnot : ¬ IsConj x c₁ :=
    not_isConj_of_card (S := S) (z := c₁) (y := x) (n := 32) hsyl hS' hAx hA2 hA32
  set g : G := c⁻¹ * k with hg
  have hyg : y = g⁻¹ * x * g := by
    rw [hy, ht, hg]
    group
  have hc₁g : c₁ = g⁻¹ * u * g := by
    calc c₁ = k⁻¹ * c₁ * k := hkc₁'.symm
      _ = k⁻¹ * (c * u * c⁻¹) * k := by rw [hcu]
      _ = g⁻¹ * u * g := by rw [hg]; group
  have hxy : IsConj x y := isConj_iff.2 ⟨g⁻¹, by rw [hyg]; group⟩
  have huxc₁y : IsConj (u * x) (c₁ * y) := by
    refine isConj_iff.2 ⟨g⁻¹, ?_⟩
    rw [hc₁g, hyg]
    group
  by_cases hyDu : y ∈ Du
  · rcases hDu y hyDu hy2 hy1 with h' | h'
    · exact absurd (hxy.trans h') hnot
    · exact hxy.trans h'
  · have hyc₁y : IsConj y (c₁ * y) := by
      refine isConj_iff.2 ⟨c₂⁻¹, ?_⟩
      rw [inv_inv]
      exact hc₂ y hyT hyDu
    exact absurd (hxy.trans (hyc₁y.trans (huxc₁y.symm.trans (hxuu.trans hu)))) hnot

end Stroth47Inv1

theorem StrothFrame.IsD.false_of_t200_inv1_ii_v {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t200 m)} (h : F.IsD D dD) (hm : 1 ≤ m) {e : G}
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (he2 : e * e = 1)
    (hc₁e : (dD.c : G) ^ 2 ^ (m - 1) * e = e * (dD.c : G) ^ 2 ^ (m - 1))
    (h1 : (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex (F.S : Subgroup G) = 2)
    (h2 : e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u})
    (hw : ∀ y ∈ (F.S : Subgroup G),
      y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) =
        (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) * y)
    (hwa : IsConj ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1))
      ((dD.a : G) ^ 2 ^ (m + 1)))
    (hI1 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}, y * y = 1 → y ≠ 1 →
      IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) ∨ IsConj y ((dD.a : G) ^ 2 ^ (m + 1)))
    (hR : ∀ y : G, IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) → ∀ A : Subgroup G,
      A ≤ Subgroup.centralizer {y} → (∀ x ∈ A, x * x = 1) → Nat.card A ≠ 32)
    (hU1 : (∃ A : Subgroup G, A ≤ Subgroup.centralizer {e} ∧ (∀ x ∈ A, x * x = 1) ∧
        Nat.card A = 32) ∧
      ∃ A : Subgroup G, A ≤ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1) * e} ∧
        (∀ x ∈ A, x * x = 1) ∧ Nat.card A = 32)
    (hU4 : ∀ y ∈ (F.S : Subgroup G), y * y = 1 → y ≠ 1 →
      y ≠ (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) →
      (∃ q ∈ (F.S : Subgroup G),
        q⁻¹ * y * q = y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1))) ∨
      ∃ A : Subgroup G, A ≤ Subgroup.centralizer {y} ∧ (∀ x ∈ A, x * x = 1) ∧
        Nat.card A = 32) :
    False := by
  classical
  have hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnonab := Stroth42.frame_exists_mul_ne F
  set S₁ : Subgroup G := D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} with hS₁
  set c₁ : G := (dD.c : G) ^ 2 ^ (m - 1) with hc₁
  set a₁ : G := (dD.a : G) ^ 2 ^ (m + 1) with ha₁
  set b₁ : G := (dD.b : G) ^ 2 ^ (m + 1) with hb₁
  set w₀ : G := a₁ * b₁ with hw₀
  have h1' : S₁.relIndex (F.S : Subgroup G) = 2 := by rw [hS₁]; exact h1
  have h2' : e ∉ S₁ := by rw [hS₁]; exact h2
  have hUS : S₁ ≤ (F.S : Subgroup G) := by rw [hS]; exact le_sup_left
  have heS : e ∈ (F.S : Subgroup G) := by
    rw [hS]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have he1 : e ≠ 1 := fun h' => h2' (by rw [h']; exact S₁.one_mem)
  have heord : orderOf e = 2 :=
    @orderOf_eq_prime G _ e 2 hFact (by rw [pow_two]; exact he2) he1
  obtain ⟨g, hg⟩ := @EvenSporadicStandard.exists_conj_mem_complement G _ _ F.simple hnonab
    (S := (F.S : Subgroup G)) (U := S₁) F.S.isPGroup' F.S.not_dvd_index hUS h1' (t := e)
    heS h2' heord
  set y : G := g⁻¹ * e * g with hy
  have hyS₁ : y ∈ S₁ := hg
  have hy2 : y * y = 1 := by
    rw [hy]
    calc g⁻¹ * e * g * (g⁻¹ * e * g) = g⁻¹ * (e * e) * g := by group
      _ = 1 := by rw [he2]; group
  have hy1 : y ≠ 1 := by
    rw [hy]
    intro h'
    apply he1
    calc e = g * (g⁻¹ * e * g) * g⁻¹ := by group
      _ = 1 := by rw [h']; group
  have hI1' : ∀ z ∈ S₁, z * z = 1 → z ≠ 1 → IsConj z c₁ ∨ IsConj z a₁ := by
    intro z hz hz2 hz1
    rw [hS₁] at hz
    exact hI1 z hz hz2 hz1
  have hey : IsConj e y := by
    refine isConj_iff.2 ⟨g⁻¹, ?_⟩
    rw [hy]
    group
  obtain ⟨Ae, hAe, hAe2, hAe32⟩ := hU1.1
  have hc₁2 : c₁ * c₁ = 1 := by
    rw [hc₁]
    exact Stroth47Fus.t200_c₁_mul_self dD hm
  have hc₁1 : c₁ ≠ 1 := by
    rw [hc₁]
    exact Stroth47Fus.t200_c₁_ne_one dD hm
  have hc₁D : c₁ ∈ D := by rw [hc₁]; exact D.pow_mem dD.c.2 _
  have hc₁S : c₁ ∈ (F.S : Subgroup G) := h.le_S hc₁D
  have hc₁S₁ : c₁ ∈ S₁ := by rw [hS₁]; exact Subgroup.mem_sup_left hc₁D
  have hea₁ : IsConj e a₁ := by
    rcases hI1' y hyS₁ hy2 hy1 with hyc | hya
    · exact absurd hAe32 (hR e (hey.trans hyc) Ae hAe hAe2)
    · exact hey.trans hya
  have hew₀ : IsConj e w₀ := hea₁.trans hwa.symm
  have hzS : (F.S : Subgroup G) ≤ Subgroup.centralizer {w₀} :=
    fun z hz => Subgroup.mem_centralizer_singleton_iff.2 (hw z hz)
  have hfact : ∀ x ∈ (F.S : Subgroup G), IsConj c₁ x → x ≠ w₀ →
      ∃ q ∈ (F.S : Subgroup G), q⁻¹ * x * q = x * w₀ := by
    intro x hxS hcx hxw
    have hx2 : x * x = 1 := Stroth42.mul_self_eq_one_of_isConj hcx.symm hc₁2
    have hx1 : x ≠ 1 := Stroth42.ne_one_of_isConj hcx.symm hc₁1
    rcases hU4 x hxS hx2 hx1 hxw with ⟨q, hqS, hq⟩ | ⟨A, hAx, hA2, hA32⟩
    · exact ⟨q, hqS, hq⟩
    · exact absurd hA32 (hR x hcx.symm A hAx hA2)
  have hne : c₁ ≠ e := fun h' => h2' (h' ▸ hc₁S₁)
  have hc₁e' : c₁ * e = e * c₁ := hc₁e
  have hc₁ce : IsConj c₁ (c₁ * e) :=
    Stroth76.isConj_mul_of_isConj_central_of_conj F.S hzS hfact hew₀ hc₁S hc₁e' hne
  obtain ⟨A, hA, hA2, hA32⟩ := hU1.2
  exact hR (c₁ * e) hc₁ce.symm A hA hA2 hA32

end CFSG.CGT.Stroth77
