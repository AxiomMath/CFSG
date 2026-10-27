module

public import CFSG.CGT.Stroth77.Section43
public import CFSG.CGT.Stroth77.StrothFrameNE

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace Stroth43C

theorem zab_ne_one {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t100 m)) :
    (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m ≠ 1 := by
  intro h1
  rw [StrothWeakTypeData.a_eq, StrothWeakTypeData.b_eq, ← dD.ofTorus_nsmul, ← dD.ofTorus_nsmul,
    ← dD.ofTorus_add, ← dD.ofTorus_zero] at h1
  have h2 := congrFun (dD.ofTorus_injective h1) 1
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply] at h2
  simp only [Torus.a, Torus.b, gen, Pi.single_eq_same,
    Pi.single_eq_of_ne (show (1 : Fin 3) ≠ 2 by decide), smul_zero, add_zero, Pi.zero_apply,
    nsmul_one] at h2
  have h3 : ((2 ^ m : ℕ) : ZMod (2 ^ (StrothTypeIndex.t100 m).k 1)) = 0 := by exact_mod_cast h2
  rw [ZMod.natCast_eq_zero_iff, show (StrothTypeIndex.t100 m).k 1 = m + 1 from rfl] at h3
  exact absurd (Nat.le_of_dvd (by positivity) h3)
    (by rw [pow_succ]; exact not_le.2 (by have := Nat.one_le_two_pow (n := m); omega))

theorem u_mul_c {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t100 m)) :
    dD.u * (dD.c : G) = (dD.c : G) * dD.u := by
  have h := dD.conj_ofTorus dD.u_mem dD.u_conj Torus.c
  rw [show (StrothTypeIndex.t100 m).action.φu Torus.c = Torus.c from
    (Type100.u_c m).trans (one_zsmul _), ← StrothWeakTypeData.c_eq] at h
  calc dD.u * (dD.c : G) = dD.u * (dD.u⁻¹ * (dD.c : G) * dD.u) := by rw [h]
    _ = (dD.c : G) * dD.u := by group


theorem exists_conj_mem_of_isConj {S Du X : Subgroup G} {v z za : G}
    (hsyl : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {z} →
      ∃ k ∈ Subgroup.centralizer {z}, ∀ q ∈ Q, k⁻¹ * q * k ∈ S)
    (hinDu : ∀ y ∈ S, y * z = z * y → y * y = 1 → IsConj y za → y ∈ Du)
    (hX : IsPGroup 2 X) (hXv : X ≤ Subgroup.centralizer {v}) (hvz : IsConj v z) :
    ∃ g : G, (∀ x ∈ X, g⁻¹ * x * g ∈ S ∧ g⁻¹ * x * g * z = z * (g⁻¹ * x * g)) ∧
      ∀ x ∈ X, x * x = 1 → IsConj x za → g⁻¹ * x * g ∈ Du := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hvz
  set X' := X.map (MulAut.conj c).toMonoidHom with hX'
  have hX'z : X' ≤ Subgroup.centralizer {z} := by
    rintro _ ⟨x, hx, rfl⟩
    have hxv : x * v = v * x := Subgroup.mem_centralizer_singleton_iff.1 (hXv hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    calc c * x * c⁻¹ * (c * v * c⁻¹) = c * (x * v) * c⁻¹ := by group
      _ = c * (v * x) * c⁻¹ := by rw [hxv]
      _ = c * v * c⁻¹ * (c * x * c⁻¹) := by group
  obtain ⟨k, hk, hkX⟩ := hsyl X' (hX.map _) hX'z
  have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.1 hk
  have key : ∀ x ∈ X, (c⁻¹ * k)⁻¹ * x * (c⁻¹ * k) ∈ S ∧
      (c⁻¹ * k)⁻¹ * x * (c⁻¹ * k) * z = z * ((c⁻¹ * k)⁻¹ * x * (c⁻¹ * k)) := by
    intro x hx
    have e : (c⁻¹ * k)⁻¹ * x * (c⁻¹ * k) = k⁻¹ * (c * x * c⁻¹) * k := by group
    have hxz : c * x * c⁻¹ * z = z * (c * x * c⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hX'z ⟨x, hx, rfl⟩)
    rw [e]
    refine ⟨hkX _ ⟨x, hx, rfl⟩, ?_⟩
    have hk' : k⁻¹ * z = z * k⁻¹ := (Commute.inv_left hkz).eq
    calc k⁻¹ * (c * x * c⁻¹) * k * z = k⁻¹ * (c * x * c⁻¹) * (k * z) := by group
      _ = k⁻¹ * (c * x * c⁻¹) * (z * k) := by rw [hkz]
      _ = k⁻¹ * (c * x * c⁻¹ * z) * k := by group
      _ = k⁻¹ * (z * (c * x * c⁻¹)) * k := by rw [hxz]
      _ = (k⁻¹ * z) * (c * x * c⁻¹) * k := by group
      _ = (z * k⁻¹) * (c * x * c⁻¹) * k := by rw [hk']
      _ = z * (k⁻¹ * (c * x * c⁻¹) * k) := by group
  refine ⟨c⁻¹ * k, key, fun x hx hx2 hxza => hinDu _ (key x hx).1 (key x hx).2 ?_ ?_⟩
  · calc (c⁻¹ * k)⁻¹ * x * (c⁻¹ * k) * ((c⁻¹ * k)⁻¹ * x * (c⁻¹ * k))
        = (c⁻¹ * k)⁻¹ * (x * x) * (c⁻¹ * k) := by group
      _ = 1 := by rw [hx2]; group
  · exact (Stroth42.isConj_of_conj_eq (g := c⁻¹ * k) rfl).trans hxza

theorem not_isConj_of_e8 {S Du F₁ : Subgroup G} {r z za : G}
    (hsyl : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {z} →
      ∃ k ∈ Subgroup.centralizer {z}, ∀ q ∈ Q, k⁻¹ * q * k ∈ S)
    (hinDu : ∀ y ∈ S, y * z = z * y → y * y = 1 → IsConj y za → y ∈ Du)
    (hza : ¬ IsConj z za) (hz1 : z ≠ 1)
    (hF1 : F₁ ≤ Subgroup.centralizer {r}) (hF2 : ∀ y ∈ F₁, y * y = 1)
    (hF8 : Nat.card F₁ = 8) (hFza : ∀ y ∈ F₁, y ≠ 1 → IsConj y za)
    (h13 : ∀ E : Subgroup G, E ≤ Du → (∀ y ∈ E, y * y = 1) → Nat.card E = 8 → z ∈ E) :
    ¬ IsConj r z := by
  intro hrz
  have hFp : IsPGroup 2 F₁ := fun f => ⟨1, Subtype.ext (by simpa [sq] using hF2 f f.2)⟩
  obtain ⟨g, -, hg⟩ := exists_conj_mem_of_isConj hsyl hinDu hFp hF1 hrz
  set F' := F₁.map (MulAut.conj g⁻¹).toMonoidHom with hF'
  have hF'Du : F' ≤ Du := by
    rintro _ ⟨f, hf, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    by_cases hf1 : f = 1
    · rw [hf1, mul_one, inv_mul_cancel]; exact Du.one_mem
    · exact hg f hf (hF2 f hf) (hFza f hf hf1)
  obtain ⟨f, hf, hfz⟩ := h13 F' hF'Du (by
    rintro _ ⟨f, hf, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * f * g * (g⁻¹ * f * g) = g⁻¹ * (f * f) * g := by group
      _ = 1 := by rw [hF2 f hf]; group) (by rw [Stroth76.card_map_conj, hF8])
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hfz
  have hf1 : f ≠ 1 := by rintro rfl; apply hz1; rw [← hfz]; group
  exact hza ((Stroth42.isConj_of_conj_eq hfz).trans (hFza f hf hf1))

theorem false_of_dihedral {S Du : Subgroup G} {r s v z za : G} {m : ℕ}
    (hsyl : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {z} →
      ∃ k ∈ Subgroup.centralizer {z}, ∀ q ∈ Q, k⁻¹ * q * k ∈ S)
    (hinDu : ∀ y ∈ S, y * z = z * y → y * y = 1 → IsConj y za → y ∈ Du)
    (hrs : IsPGroup 2 (Subgroup.closure {r, s})) (hrv : r * v = v * r) (hsv : s * v = v * s)
    (hvz : IsConj v z) (hr2 : r * r = 1) (hs2 : s * s = 1) (hrza : IsConj r za)
    (hsza : IsConj s za) (hm : (r * s) ^ 2 ^ (m + 1) ≠ 1)
    (h14 : ∀ y₁ ∈ Du, ∀ y₂ ∈ Du, y₁ * y₁ = 1 → y₂ * y₂ = 1 → (y₁ * y₂) ^ 2 ^ (m + 1) = 1) :
    False := by
  have hXv : Subgroup.closure {r, s} ≤ Subgroup.centralizer {v} := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hrv
    · exact Subgroup.mem_centralizer_singleton_iff.2 hsv
  obtain ⟨g, -, hg⟩ := exists_conj_mem_of_isConj hsyl hinDu hrs hXv hvz
  have h := h14 _ (hg r (Subgroup.subset_closure (by simp)) hr2 hrza) _
    (hg s (Subgroup.subset_closure (by simp)) hs2 hsza)
    (by calc g⁻¹ * r * g * (g⁻¹ * r * g) = g⁻¹ * (r * r) * g := by group
          _ = 1 := by rw [hr2]; group)
    (by calc g⁻¹ * s * g * (g⁻¹ * s * g) = g⁻¹ * (s * s) * g := by group
          _ = 1 := by rw [hs2]; group)
  rw [show g⁻¹ * r * g * (g⁻¹ * s * g) = g⁻¹ * (r * s) * g by group, Stroth42.conj_pow'] at h
  exact hm (by calc (r * s) ^ 2 ^ (m + 1) = g * (g⁻¹ * (r * s) ^ 2 ^ (m + 1) * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group)

theorem not_isConj_of_chain [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    {U U₂ : Subgroup G} {z za r e uv u zu ue ce cue : G}
    (hUS : U ≤ S) (hU : U.relIndex S = 2) (hU₂S : U₂ ≤ S) (hU₂ : U₂.relIndex S = 2)
    (hrS : r ∈ (S : Subgroup G)) (hrU : r ∉ U) (hrU₂ : r ∉ U₂) (hro : orderOf r = 2)
    (hza : ¬ IsConj z za) (huvza : IsConj uv za) (hu : IsConj u z) (hzu : IsConj zu za)
    (heue : IsConj e ue) (hcecue : IsConj ce cue)
    (hC6 : ∀ y ∈ (S : Subgroup G), y ∉ U → y * y = 1 →
      IsConj y r ∨ IsConj y ce ∨ IsConj y cue)
    (hC7 : ∀ y ∈ U, y * y = 1 → y ≠ 1 → IsConj y z ∨ IsConj y za ∨ IsConj y uv ∨
      IsConj y u ∨ IsConj y zu ∨ IsConj y e ∨ IsConj y ue)
    (hC10 : ∀ y ∈ U₂, y * y = 1 → y ≠ 1 → IsConj y z ∨ IsConj y za ∨ IsConj y uv ∨
      IsConj y u ∨ IsConj y zu ∨ IsConj y ce ∨ IsConj y cue)
    (hrz : ¬ IsConj r z) (hue : IsConj r za → IsConj ue cue)
    (hM : IsConj r za → IsConj z e → False) :
    ∀ y ∈ (S : Subgroup G), y ∉ U → y * y = 1 → ¬ IsConj y z := by
  intro y₀ hy₀S hy₀U hy₀2 hy₀z
  have hstar : IsConj z r ∨ IsConj z ce := by
    rcases hC6 y₀ hy₀S hy₀U hy₀2 with h' | h' | h'
    · exact Or.inl (hy₀z.symm.trans h')
    · exact Or.inr (hy₀z.symm.trans h')
    · exact Or.inr (hy₀z.symm.trans (h'.trans hcecue.symm))
  have hr1 : r ≠ 1 := fun h' => by rw [h', orderOf_one] at hro; omega
  have hr2 : r * r = 1 := by rw [← sq, ← hro]; exact pow_orderOf_eq_one r
  have hinv : ∀ g : G, (g⁻¹ * r * g) * (g⁻¹ * r * g) = 1 ∧ g⁻¹ * r * g ≠ 1 ∧
      IsConj r (g⁻¹ * r * g) := fun g => ⟨by
        calc g⁻¹ * r * g * (g⁻¹ * r * g) = g⁻¹ * (r * r) * g := by group
          _ = 1 := by rw [hr2]; group,
      fun h' => hr1 (by
        calc r = g * (g⁻¹ * r * g) * g⁻¹ := by group
          _ = 1 := by rw [h']; group),
      (Stroth42.isConj_of_conj_eq rfl).symm⟩
  obtain ⟨g₁, hg₁⟩ := EvenSporadicStandard.exists_conj_mem_complement hnonab S.isPGroup'
    S.not_dvd_index hUS hU hrS hrU hro
  obtain ⟨hr'2, hr'1, hrr'⟩ := hinv g₁
  have hr3 : IsConj r za ∨ IsConj r e := by
    rcases hC7 _ hg₁ hr'2 hr'1 with h' | h' | h' | h' | h' | h' | h'
    · exact absurd (hrr'.trans h') hrz
    · exact Or.inl (hrr'.trans h')
    · exact Or.inl ((hrr'.trans h').trans huvza)
    · exact absurd ((hrr'.trans h').trans hu) hrz
    · exact Or.inl ((hrr'.trans h').trans hzu)
    · exact Or.inr (hrr'.trans h')
    · exact Or.inr ((hrr'.trans h').trans heue.symm)
  have hrza : IsConj r za := by
    rcases hr3 with h' | hre
    · exact h'
    · by_contra hrza
      obtain ⟨g₂, hg₂⟩ := EvenSporadicStandard.exists_conj_mem_complement hnonab S.isPGroup'
        S.not_dvd_index hU₂S hU₂ hrS hrU₂ hro
      obtain ⟨hr''2, hr''1, hrr''⟩ := hinv g₂
      have hrce : IsConj r ce := by
        rcases hC10 _ hg₂ hr''2 hr''1 with h' | h' | h' | h' | h' | h' | h'
        · exact absurd (hrr''.trans h') hrz
        · exact absurd (hrr''.trans h') hrza
        · exact absurd ((hrr''.trans h').trans huvza) hrza
        · exact absurd ((hrr''.trans h').trans hu) hrz
        · exact absurd ((hrr''.trans h').trans hzu) hrza
        · exact hrr''.trans h'
        · exact (hrr''.trans h').trans hcecue.symm
      rcases hstar with h' | h'
      · exact hrz h'.symm
      · exact hrz (hrce.trans h'.symm)
  have hece : IsConj e ce := heue.trans ((hue hrza).trans hcecue.symm)
  rcases hstar with h' | h'
  · exact hza (h'.trans hrza)
  · exact hM hrza (h'.trans hece.symm)

end Stroth43C

theorem StrothFrame.IsD.false_of_t100_iii {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t100 m)} (h : F.IsD D dD) (hm : 2 ≤ m)
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    {e : G} (heN : e ∈ Subgroup.normalizer (D : Set G)) (he : e * e = 1)
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hue : e⁻¹ * dD.u * e = dD.u)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (hE : ∀ y ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ m, (dD.b : G) ^ 2 ^ m, dD.uv, dD.t},
      y ≠ 1 → IsConj y ((dD.a : G) ^ 2 ^ m))
    (hu : IsConj dD.u ((dD.c : G) ^ 2 ^ (m - 1)))
    (hzu : IsConj ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ((dD.a : G) ^ 2 ^ m))
    (h1 : (Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
      e}).relIndex (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2)
    (h2 : (dD.c : G) ∉
      Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e})
    (h1' : (Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
      (dD.c : G) * e}).relIndex
        (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2)
    (h2' : (dD.c : G) * dD.a * dD.uv ∉ Subgroup.closure
      {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, (dD.c : G) * e})
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 →
      (∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = (dD.c : G) ^ 2 ^ (m - 1)) ∨
        ∃ g ∈ dD.L, g⁻¹ * y * g = (dD.a : G) ^ 2 ^ m)
    (h4 : ∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e},
      y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
        y ^ 2 ^ (m - 1) ≠ (dD.c : G) ^ 2 ^ (m - 1))
    (h5 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * y ∈ D ∨ y * y * dD.uv ∈ D)
    (h8 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} →
      ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = (dD.c : G) ^ 2 ^ (m - 1) → y ^ 2 ^ (m - 1) ≠ 1)
    (h9 : ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        IsMulCommutative X → Nat.card X = Nat.card D → X = D)
    (hC2 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * y = 1 → y ≠ 1 → y ≠ (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m →
        ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
          q⁻¹ * y * q = y * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m))
    (hC2c : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) = (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m * y)
    (hC4 : ∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
      e}, y * dD.uv ∈ D → y * y = 1 →
        ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
          q⁻¹ * y * q = dD.uv)
    (hC6 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} →
      y * y = 1 → IsConj y ((dD.c : G) * dD.a * dD.uv) ∨ IsConj y ((dD.c : G) * e) ∨
        IsConj y ((dD.c : G) * dD.u * e))
    (hC7 : ∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
      e}, y * y = 1 → y ≠ 1 → IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) ∨
        IsConj y ((dD.a : G) ^ 2 ^ m) ∨ IsConj y dD.uv ∨ IsConj y dD.u ∨
        IsConj y ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ∨ IsConj y e ∨ IsConj y (dD.u * e))
    (hC10 : ∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u,
      (dD.c : G) * e}, y * y = 1 → y ≠ 1 → IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) ∨
        IsConj y ((dD.a : G) ^ 2 ^ m) ∨ IsConj y dD.uv ∨ IsConj y dD.u ∨
        IsConj y ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ∨ IsConj y ((dD.c : G) * e) ∨
        IsConj y ((dD.c : G) * dD.u * e))
    (hC11 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * e ∈ D ⊔ Subgroup.zpowers dD.u → y * y = 1 →
        ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
          q⁻¹ * y * q = (dD.c : G) ^ 2 ^ (m - 1) * y)
    (hC13 : ∀ E : Subgroup G, E ≤ D ⊔ Subgroup.zpowers dD.u → (∀ y ∈ E, y * y = 1) →
      Nat.card E = 8 → (dD.c : G) ^ 2 ^ (m - 1) ∈ E)
    (hC14 : ∀ y₁ ∈ D ⊔ Subgroup.zpowers dD.u, ∀ y₂ ∈ D ⊔ Subgroup.zpowers dD.u,
      y₁ * y₁ = 1 → y₂ * y₂ = 1 → (y₁ * y₂) ^ 2 ^ (m + 1) = 1)
    (hC15 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
        y ∈ D ⊔ Subgroup.zpowers dD.u ∨ y * e ∈ D ⊔ Subgroup.zpowers dD.u)
    (hr2 : (dD.c : G) * dD.a * dD.uv * ((dD.c : G) * dD.a * dD.uv) = 1)
    (hrue : (dD.c : G) * dD.a * dD.uv * (dD.u * e) = dD.u * e * ((dD.c : G) * dD.a * dD.uv))
    (hrta : (dD.t * dD.a)⁻¹ * ((dD.c : G) * dD.a * dD.uv * (dD.u * e)) * (dD.t * dD.a) =
      (dD.c : G) * dD.u * e)
    (hF : Subgroup.closure {(dD.a : G) ^ 2 ^ m, (dD.b : G) ^ 2 ^ m, dD.t} ≤
        Subgroup.centralizer {(dD.c : G) * dD.a * dD.uv} ∧
      (∀ y ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ m, (dD.b : G) ^ 2 ^ m, dD.t}, y * y = 1) ∧
      Nat.card (Subgroup.closure {(dD.a : G) ^ 2 ^ m, (dD.b : G) ^ 2 ^ m, dD.t}) = 8)
    (hM : (dD.c : G) ^ 2 ^ (m - 1) * dD.u * (dD.u * e) =
        dD.u * e * ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ∧
      ((dD.c : G) * dD.a * dD.uv * ((dD.c : G) ^ 2 ^ (m - 1) * dD.u)) ^ 2 ^ (m + 1) ≠ 1) :
    False := by
  classical
  haveI := F.simple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnonab := Stroth42.frame_exists_mul_ne F
  set P := Subgroup.closure {dD.uv, dD.t, dD.u} with hP
  set U := Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e}
    with hU
  set U₂ := Subgroup.closure
    {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, (dD.c : G) * e} with hU₂
  set c := (dD.c : G) with hc
  set z := c ^ 2 ^ (m - 1) with hz
  set za := (dD.a : G) ^ 2 ^ m with hzadef
  set w := za * (dD.b : G) ^ 2 ^ m with hw
  set r := c * dD.a * dD.uv with hr
  rw [← hS] at h1 h1' h5 h8 h9 hC2 hC2c hC6 hC11 hC15
  have hoc : orderOf c = 2 ^ m := by rw [hc, Stroth42.orderOf_c_coe]; rfl
  obtain ⟨hz2, hz1⟩ := Stroth42.pow_mul_self_eq_one (by omega) hoc
  rw [← hz] at hz2 hz1
  have hc2 : c ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by
    rw [hoc]; calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm)
  have hcD : c ∈ D := dD.c.2
  have hzD : z ∈ D := D.pow_mem hcD _
  have hDS : D ≤ (F.S : Subgroup G) := h.le_S
  have hPN : P ≤ Subgroup.normalizer (D : Set G) := by
    rw [hP, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    exacts [dD.uv_mem, dD.t_mem, dD.u_mem]
  have hSD : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
    rw [hS]
    exact sup_le (sup_le Subgroup.le_normalizer hPN) ((Subgroup.zpowers_le).2 heN)
  have hPS : P ≤ (F.S : Subgroup G) := by rw [hS]; exact le_sup_right.trans le_sup_left
  have heS : e ∈ (F.S : Subgroup G) := by
    rw [hS]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have hgenS : ∀ y ∈ ({c ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} : Set G),
      y ∈ (F.S : Subgroup G) := by
    rintro _ (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hDS (D.pow_mem hcD 2)
    · exact hDS dD.a.2
    · exact hDS dD.b.2
    all_goals exact hPS (Subgroup.subset_closure (by simp))
  have hUS : U ≤ (F.S : Subgroup G) := by
    rw [hU, Subgroup.closure_le]
    rintro y (hy | hy | hy | hy | hy | hy | hy)
    · exact hgenS y (by simp [hy])
    · exact hgenS y (by simp [hy])
    · exact hgenS y (by simp [hy])
    · exact hgenS y (by simp [hy])
    · exact hgenS y (by simp [hy])
    · exact hgenS y (by simp [hy])
    · rw [Set.mem_singleton_iff.1 hy]; exact heS
  have hU₂S : U₂ ≤ (F.S : Subgroup G) := by
    rw [hU₂, Subgroup.closure_le]
    rintro y (hy | hy | hy | hy | hy | hy | hy)
    · exact hgenS y (by simp [hy])
    · exact hgenS y (by simp [hy])
    · exact hgenS y (by simp [hy])
    · exact hgenS y (by simp [hy])
    · exact hgenS y (by simp [hy])
    · exact hgenS y (by simp [hy])
    · rw [Set.mem_singleton_iff.1 hy]; exact (F.S : Subgroup G).mul_mem (hDS hcD) heS
  have hPU : P ≤ U := by
    rw [hP, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
  have hmemU : ∀ y ∈ ({c ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u, e} : Set G), y ∈ U :=
    fun y hy => Subgroup.subset_closure hy
  have hc2U : c ^ 2 ∈ U := hmemU _ (by simp)
  have haU : (dD.a : G) ∈ U := hmemU _ (by simp)
  have huvU : dD.uv ∈ U := hmemU _ (by simp)
  have huU : dD.u ∈ U := hmemU _ (by simp)
  have heU : e ∈ U := hmemU _ (by simp)
  have hzU : z ∈ U := by
    rw [hz, show 2 ^ (m - 1) = 2 * 2 ^ (m - 2) by rw [← pow_succ']; congr 1; omega, pow_mul]
    exact U.pow_mem hc2U _
  have huS : dD.u ∈ (F.S : Subgroup G) := hUS huU
  have hcS : c ∈ (F.S : Subgroup G) := hDS hcD
  have hzS : z ∈ (F.S : Subgroup G) := hDS hzD
  have hza := h.not_isConj_of_omega hnc h3
  have h3' : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z := by
    intro y hyD hy2 hy1 hyz
    rcases h3 y hyD hy2 hy1 with hp | ⟨g, -, hg⟩
    · exact hp
    · exact absurd (hyz.symm.trans (Stroth42.isConj_of_conj_eq hg).symm) hza
  have hsyl : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {z} →
      ∃ k ∈ Subgroup.centralizer {z}, ∀ q ∈ Q, k⁻¹ * q * k ∈ (F.S : Subgroup G) :=
    fun Q hQ hQz => Stroth42.exists_conj_le_centralizer F.S dD.isMulCommutative hDS hSD hPS hzD
      h3' hz2 hz1 h9 hQ hQz
  have huv1 : dD.uv ≠ 1 := fun h1 => F.uv_not_mem_centralizer_A (by
    rw [← h.uv_eq, h1]; exact Subgroup.one_mem _)
  have huvza : IsConj dD.uv za := hE _ (Subgroup.subset_closure (by simp)) huv1
  have hwza : IsConj w za := hE _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))) (Stroth43C.zab_ne_one dD)
  have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have huc : dD.u * c = c * dD.u := Stroth43C.u_mul_c dD
  have hue' : dD.u * e = e * dD.u := by
    calc dD.u * e = e * (e⁻¹ * dD.u * e) := by group
      _ = e * dD.u := by rw [hue]
  have hcpow : ∀ k : ℕ, e⁻¹ * c ^ k * e = (c ^ k)⁻¹ := fun k => by
    rw [← Stroth42.conj_pow', hce, inv_pow]
  have hze : z * e = e * z := by
    have h0 : e⁻¹ * z * e = z := by
      rw [hz, hcpow, inv_eq_of_mul_eq_one_right hz2]
    calc z * e = e * (e⁻¹ * z * e) := by group
      _ = e * z := by rw [h0]
  have hcz : c * z = z * c := (Commute.pow_right (Commute.refl c) _).eq
  have huz : dD.u * z = z * dD.u := (Commute.pow_right huc _).eq
  set Du := D ⊔ Subgroup.zpowers dD.u with hDu
  have hDc : D ≤ Subgroup.centralizer {c} := fun d hd => Subgroup.mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨d, hd⟩ ⟨c, hcD⟩))
  have hDz : D ≤ Subgroup.centralizer {z} := fun d hd => Subgroup.mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨d, hd⟩ ⟨z, hzD⟩))
  have hDuc : Du ≤ Subgroup.centralizer {c} :=
    sup_le hDc ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 huc))
  have hDuz : Du ≤ Subgroup.centralizer {z} :=
    sup_le hDz ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 huz))
  have hec : ¬ e * c = c * e := fun h' => hc2 (by
    have h0 : e⁻¹ * c * e = c := by rw [mul_assoc, ← h']; group
    rw [hce] at h0
    calc c ^ 2 = c * c := sq c
      _ = c * c⁻¹ := by rw [h0]
      _ = 1 := mul_inv_cancel c)
  have heDu : e ∉ Du := fun h' => hec (Subgroup.mem_centralizer_singleton_iff.1 (hDuc h'))
  have hzuDu : z * dD.u ∈ Du := Du.mul_mem (Subgroup.mem_sup_left hzD)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hu2 : dD.u * dD.u = 1 := dD.u_sq
  have hue2 : dD.u * e * (dD.u * e) = 1 := by
    calc dD.u * e * (dD.u * e) = dD.u * (e * dD.u) * e := by group
      _ = dD.u * (dD.u * e) * e := by rw [hue']
      _ = (dD.u * dD.u) * (e * e) := by group
      _ = 1 := by rw [hu2, he, one_mul]
  have hece : e * c * e = c⁻¹ := by rw [← hce, he']
  have hce2 : c * e * (c * e) = 1 := by
    calc c * e * (c * e) = c * (e * c * e) := by group
      _ = 1 := by rw [hece, mul_inv_cancel]
  have hzu2 : z * dD.u * (z * dD.u) = 1 := by
    calc z * dD.u * (z * dD.u) = z * (dD.u * z) * dD.u := by group
      _ = z * (z * dD.u) * dD.u := by rw [huz]
      _ = (z * z) * (dD.u * dD.u) := by group
      _ = 1 := by rw [hz2, hu2, one_mul]
  have hzue : z * dD.u * e = e * (z * dD.u) := by
    calc z * dD.u * e = z * (dD.u * e) := by group
      _ = z * (e * dD.u) := by rw [hue']
      _ = (z * e) * dD.u := by group
      _ = (e * z) * dD.u := by rw [hze]
      _ = e * (z * dD.u) := by group
  have hzuce : c * e * (z * dD.u) = z * dD.u * (c * e) := by
    calc c * e * (z * dD.u) = c * (e * z) * dD.u := by group
      _ = c * (z * e) * dD.u := by rw [hze]
      _ = (c * z) * (e * dD.u) := by group
      _ = (z * c) * (dD.u * e) := by rw [hcz, hue']
      _ = z * (c * dD.u) * e := by group
      _ = z * (dD.u * c) * e := by rw [huc]
      _ = z * dD.u * (c * e) := by group
  have hueU : dD.u * e ∈ U := U.mul_mem huU heU
  have hueS : dD.u * e ∈ (F.S : Subgroup G) := hUS hueU
  have hzuU : z * dD.u ∈ U := U.mul_mem hzU huU
  have hzuS : z * dD.u ∈ (F.S : Subgroup G) := hUS hzuU
  have hceU : c * e ∉ U := fun h' => h2 (by
    have := U.mul_mem h' (U.inv_mem heU)
    rwa [mul_inv_cancel_right] at this)
  have hceS : c * e ∈ (F.S : Subgroup G) := (F.S : Subgroup G).mul_mem hcS heS
  have hrU : r ∉ U := fun h' => h2 (by
    have := U.mul_mem (U.mul_mem h' (U.inv_mem huvU)) (U.inv_mem haU)
    rwa [hr, mul_inv_cancel_right, mul_inv_cancel_right] at this)
  have hrS : r ∈ (F.S : Subgroup G) := (F.S : Subgroup G).mul_mem
    ((F.S : Subgroup G).mul_mem hcS (hDS dD.a.2)) (hPS (Subgroup.subset_closure (by simp)))
  have he1 : e ≠ 1 := fun h' => heDu (h' ▸ Du.one_mem)
  have hezu : e ≠ z * dD.u := fun h' => heDu (h' ▸ hzuDu)
  have hce1 : c * e ≠ 1 := fun h' => hceU (h' ▸ U.one_mem)
  have hcezu : c * e ≠ z * dD.u := fun h' => hceU (h' ▸ hzuU)
  have hue1 : dD.u * e ≠ 1 := fun h' => heDu (by
    have : e = dD.u⁻¹ := by rw [← mul_eq_one_iff_eq_inv', ← h']
    rw [this]; exact Du.inv_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  have huer : dD.u * e ≠ r := fun h' => hrU (h' ▸ hueU)
  have hr1 : r ≠ 1 := fun h' => hrU (h' ▸ U.one_mem)
  have hro : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hr2) hr1
  set q := c ^ 2 ^ (m - 2) with hq
  have hqq : q * q = z := by
    rw [hq, hz, ← pow_add, ← two_mul, ← pow_succ', show m - 2 + 1 = m - 1 by omega]
  have hqe : e⁻¹ * q * e = q⁻¹ := hcpow _
  have heq : e * q = q⁻¹ * e := by
    calc e * q = (e⁻¹ * q * e) * e := by rw [mul_assoc (e⁻¹ * q) e e, he, mul_one, he']
      _ = q⁻¹ * e := by rw [hqe]
  have huq : dD.u * q = q * dD.u := (Commute.pow_right huc _).eq
  have hcq : c * q = q * c := (Commute.pow_right (Commute.refl c) _).eq
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have huq' : dD.u * q⁻¹ = q⁻¹ * dD.u := ((Commute.pow_right huc _).inv_right).eq
  have hqc : q⁻¹ * c = c * q⁻¹ := ((Commute.pow_left (Commute.refl c) _).inv_left).eq
  have hk1 : q⁻¹ * (dD.u * e) * q = z * dD.u * e := by
    calc q⁻¹ * (dD.u * e) * q = q⁻¹ * dD.u * (e * q) := by group
      _ = q⁻¹ * dD.u * (q⁻¹ * e) := by rw [heq]
      _ = q⁻¹ * (dD.u * q⁻¹) * e := by group
      _ = q⁻¹ * (q⁻¹ * dD.u) * e := by rw [huq']
      _ = (q * q)⁻¹ * dD.u * e := by group
      _ = z * dD.u * e := by rw [hqq, hzinv]
  have hk2 : q⁻¹ * (c * dD.u * e) * q = z * dD.u * (c * e) := by
    calc q⁻¹ * (c * dD.u * e) * q = (q⁻¹ * c) * (q * (q⁻¹ * (dD.u * e) * q)) := by group
      _ = (c * q⁻¹) * (q * (z * dD.u * e)) := by
        rw [hk1, hqc]
      _ = c * z * dD.u * e := by group
      _ = z * dD.u * (c * e) := by
        rw [hcz]
        calc z * c * dD.u * e = z * (c * dD.u) * e := by group
          _ = z * (dD.u * c) * e := by rw [huc]
          _ = z * dD.u * (c * e) := by group
  have hwS : (F.S : Subgroup G) ≤ Subgroup.centralizer {w} := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.2 (hC2c y hy)
  have hL6 : ∀ {v y : G}, IsConj v za → y ∈ (F.S : Subgroup G) → v ∈ (F.S : Subgroup G) →
      y * v = v * y → y * y = 1 → y ≠ 1 → y ≠ v → IsConj y (y * v) :=
    fun hv hy hvS hyv hy2 hy1 hne =>
      Stroth76.isConj_mul_of_isConj_central F.S hwS hC2 (hv.trans hwza.symm) hy hvS hyv hy2 hy1
        hne
  have heue : IsConj e (dD.u * e) := by
    have h0 := hL6 hzu heS hzuS hzue.symm he he1 hezu
    rw [← hzue] at h0
    exact h0.trans (Stroth42.isConj_of_conj_eq hk1)
  have hcecue : IsConj (c * e) (c * dD.u * e) := by
    have h0 := hL6 hzu hceS hzuS hzuce hce2 hce1 hcezu
    rw [hzuce] at h0
    exact h0.trans (Stroth42.isConj_of_conj_eq hk2)
  have hDue : ∀ l ∈ (F.S : Subgroup G), l * e ∈ Du → l * l = 1 → ¬ IsConj l za := by
    intro l hlS hle hl2 hlza
    have hlDu : l ∉ Du := fun h' => heDu (by
      have := Du.mul_mem (Du.inv_mem h') hle
      rwa [inv_mul_cancel_left] at this)
    have hlz : z * l = l * z := by
      have h1' : l * e * z = z * (l * e) := Subgroup.mem_centralizer_singleton_iff.1 (hDuz hle)
      calc z * l = z * (l * e) * e := by rw [mul_assoc, mul_assoc, he, mul_one]
        _ = l * e * z * e := by rw [h1']
        _ = l * (e * z) * e := by group
        _ = l * (z * e) * e := by rw [hze]
        _ = l * z := by rw [mul_assoc, mul_assoc, he, mul_one]
    have hzl : z ≠ l := fun h' => hlDu (h' ▸ Subgroup.mem_sup_left hzD)
    have h0 := hL6 hlza hzS hlS hlz hz2 hz1 hzl
    obtain ⟨q', -, hq'⟩ := hC11 l hlS hle hl2
    exact hza (h0.trans ((Stroth42.isConj_of_conj_eq hq').trans hlza))
  have hinDu : ∀ y ∈ (F.S : Subgroup G), y * z = z * y → y * y = 1 → IsConj y za → y ∈ Du := by
    intro y hyS hyz hy2 hyza
    rcases hC15 y hyS hyz with h' | h'
    · exact h'
    · exact absurd hyza (hDue y hyS h' hy2)
  have hF₁E : Subgroup.closure {za, (dD.b : G) ^ 2 ^ m, dD.t} ≤
      Subgroup.closure {za, (dD.b : G) ^ 2 ^ m, dD.uv, dD.t} :=
    Subgroup.closure_mono (by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      tauto)
  have hrz : ¬ IsConj r z := Stroth43C.not_isConj_of_e8 hsyl hinDu hza hz1 hF.1 hF.2.1 hF.2.2
    (fun y hy hy1 => hE y (hF₁E hy) hy1) hC13
  have hue : IsConj r za → IsConj (dD.u * e) (c * dD.u * e) := fun hrza => by
    have h0 := hL6 hrza hueS hrS hrue.symm hue2 hue1 huer
    rw [← hrue] at h0
    exact h0.trans (Stroth42.isConj_of_conj_eq hrta).symm
  have hM' : IsConj r za → IsConj z e → False := fun hrza hze' =>
    Stroth43C.false_of_dihedral (m := m) hsyl hinDu
      (F.S.isPGroup'.to_le (by
        rw [Subgroup.closure_le]
        rintro _ (rfl | rfl)
        exacts [hrS, hzuS]))
      hrue hM.1 (heue.symm.trans hze'.symm) hr2 hzu2 hrza hzu hM.2 hC14
  have hK6 := Stroth43C.not_isConj_of_chain hnonab F.S hUS h1 hU₂S h1' hrS hrU h2' hro hza
    huvza hu hzu heue hcecue hC6 hC7 hC10 hrz hue hM'
  have h6U : ∀ y ∈ U, y * dD.uv ∈ D → y * y = 1 → ¬ IsConj y z := by
    intro y hyU hyuv hy2 hyz
    obtain ⟨q', -, hq'⟩ := hC4 y hyU hyuv hy2
    exact hza (hyz.symm.trans ((Stroth42.isConj_of_conj_eq hq').symm.trans huvza))
  exact Stroth42.false_of_harada hnonab F.S hUS h1 hPU hcS h2 rfl hz2 hz1 dD.uv_mem dD.uv_sq h3'
    h5 h6U hK6 h8 (Stroth42.conj_not_mem hPU (by omega) rfl hz2 hz1 dD.uv_mem dD.uv_sq h3' h4
      (fun y hy => h5 y (hUS hy)) h6U)

end CFSG.CGT.Stroth77
