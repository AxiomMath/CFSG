module

public import CFSG.CGT.Stroth77.Section310CharBA

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem StrothWeakTypeData.bound_comm (dD : StrothWeakTypeData D τ) {s j : ℕ}
    (hDs : Nat.card D = 2 ^ s) (hc1 : ¬ (dD.c : G) ^ 2 ^ (j - 1) * dD.uv =
      dD.uv * (dD.c : G) ^ 2 ^ (j - 1)) {e : G} (heN : e ∈ Subgroup.normalizer (D : Set G))
    (hc : e⁻¹ * (dD.c : G) * e = dD.c) {A B : G} (hAD : A ∈ D) (hBD : B ∈ D)
    (ha : e⁻¹ * (dD.a : G) * e = dD.a * A) (hb : e⁻¹ * (dD.b : G) * e = dD.b * B) (hA1 : A ≠ 1)
    (hB1 : B ≠ 1) (hAB : A ≠ B) {x : G} (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxc : (dD.c : G) ^ 2 ^ (j - 1) * x = x * (dD.c : G) ^ 2 ^ (j - 1)) :
    4 * 2 ^ j * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) ≤ Nat.card D := by
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hae : e⁻¹ * (dD.a : G) * e * (dD.a : G)⁻¹ = A := by
    rw [ha, mul_assoc, hcommD _ hAD _ (inv_mem dD.a.2), mul_inv_cancel_left]
  have hbe : e⁻¹ * (dD.b : G) * e * (dD.b : G)⁻¹ = B := by
    rw [hb, mul_assoc, hcommD _ hBD _ (inv_mem dD.b.2), mul_inv_cancel_left]
  have h4 := four_mul_card_inf_centralizer_le hcommD hDs heN dD.a.2 dD.b.2
    (by rw [hae]; exact hA1) (by rw [hbe]; exact hB1) (by rw [hae, hbe]; exact hAB)
  have hbN : dD.uv * x ∈ Subgroup.normalizer (D : Set G) := mul_mem dD.uv_mem hxN
  have hcH : (dD.c : G) ∈ D ⊓ Subgroup.centralizer ({e} : Set G) := by
    refine ⟨dD.c.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (dD.c : G) * e = e * (e⁻¹ * (dD.c : G) * e) := by group
      _ = e * dD.c := by rw [hc]
  have h2j := two_pow_mul_card_inf_centralizer_le hcommD hDs inf_le_left hbN hcH
    (not_commute_mul_of_commute hc1 hxc)
  rw [inf_right_comm D]
  calc 4 * 2 ^ j * Nat.card ↥(D ⊓ Subgroup.centralizer ({e} : Set G) ⊓
        Subgroup.centralizer ({dD.uv * x} : Set G))
      = 4 * (2 ^ j * Nat.card ↥(D ⊓ Subgroup.centralizer ({e} : Set G) ⊓
        Subgroup.centralizer ({dD.uv * x} : Set G))) := by ring
    _ ≤ 4 * Nat.card ↥(D ⊓ Subgroup.centralizer ({e} : Set G)) := Nat.mul_le_mul_left 4 h2j
    _ ≤ Nat.card D := h4

theorem sixteen_mul_card_inf_centralizer_le {D : Subgroup G}
    (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {f : G} (hf : f ∈ Subgroup.normalizer (D : Set G))
    {a b A B : G} (ha : a ∈ D) (hb : b ∈ D) (hA : f⁻¹ * a * f * a⁻¹ = A)
    (hB : f⁻¹ * b * f * b⁻¹ = B)
    (hinj : ∀ i l i' l' : Fin 4, A ^ (i : ℕ) * B ^ (l : ℕ) = A ^ (i' : ℕ) * B ^ (l' : ℕ) →
      i = i' ∧ l = l') :
    16 * Nat.card ↥(D ⊓ Subgroup.centralizer ({f} : Set G)) ≤ Nat.card D := by
  classical
  have hsplit := card_inf_centralizer_mul_card_range hD hf
  set φ := commHom hD hf with hφ
  have hφa : ((φ ⟨a, ha⟩ : D) : G) = A := by rw [hφ, coe_commHom]; exact hA
  have hφb : ((φ ⟨b, hb⟩ : D) : G) = B := by rw [hφ, coe_commHom]; exact hB
  let g : Fin 4 × Fin 4 → φ.range := fun p =>
    ⟨φ (⟨a, ha⟩ ^ (p.1 : ℕ) * ⟨b, hb⟩ ^ (p.2 : ℕ)), ⟨_, rfl⟩⟩
  have hg : Function.Injective g := by
    rintro ⟨i, l⟩ ⟨i', l'⟩ hil
    have h1 := congrArg (fun z : φ.range => ((z : D) : G)) hil
    simp only [g, map_mul, map_pow, Subgroup.coe_mul, SubgroupClass.coe_pow, hφa, hφb] at h1
    obtain ⟨rfl, rfl⟩ := hinj i l i' l' h1
    rfl
  have h16 : 16 ≤ Nat.card φ.range := by
    have := Nat.card_le_card_of_injective g hg
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at this
  calc 16 * Nat.card ↥(D ⊓ Subgroup.centralizer ({f} : Set G))
      ≤ Nat.card φ.range * Nat.card ↥(D ⊓ Subgroup.centralizer ({f} : Set G)) :=
        Nat.mul_le_mul_right _ h16
    _ = Nat.card D := by rw [mul_comm]; exact hsplit

theorem mem_normalizer_sup_zpowers {D : Subgroup G} {r s : G}
    (hsN : s ∈ Subgroup.normalizer (D : Set G))
    (hrs : s⁻¹ * r * s ∈ D ⊔ Subgroup.zpowers r) :
    s ∈ Subgroup.normalizer ((D ⊔ Subgroup.zpowers r : Subgroup G) : Set G) := by
  classical
  set H : Subgroup G := D ⊔ Subgroup.zpowers r with hH
  have hsub : H.map (MulAut.conj s⁻¹).toMonoidHom ≤ H := by
    rw [hH, Subgroup.map_sup, sup_le_iff]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      refine Subgroup.mem_sup_left ?_
      simpa using (Subgroup.mem_normalizer_iff''.mp hsN d).mp hd
    · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      simpa using hrs
  have hcard : Nat.card ↥(H.map (MulAut.conj s⁻¹).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj s⁻¹).injective
  have heq : H.map (MulAut.conj s⁻¹).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hsub hcard.ge
  rw [Subgroup.mem_normalizer_iff'']
  intro h
  constructor
  · intro hh
    have : s⁻¹ * h * s ∈ H.map (MulAut.conj s⁻¹).toMonoidHom := ⟨h, hh, by simp⟩
    rwa [heq] at this
  · intro hh
    rw [← heq] at hh
    obtain ⟨h', hh', hh'e⟩ := hh
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hh'e
    have : h = h' := by
      have := congrArg (fun z => s * z * s⁻¹) hh'e
      simpa [mul_assoc] using this.symm
    exact this ▸ hh'

theorem StrothFrame.IsD.hB_of_tower (h : F.IsD D dD) {r s : G}
    (hRrs : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) =
        (D ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers s)
    (hrN : r ∈ Subgroup.normalizer (D : Set G)) (hr2 : r * r ∈ D)
    (hsN : s ∈ Subgroup.normalizer ((D ⊔ Subgroup.zpowers r : Subgroup G) : Set G))
    (hs2 : s * s ∈ D ⊔ Subgroup.zpowers r)
    (hgood : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      8 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer ({r} : Set G)) < Nat.card D)
    (hbad : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), y ∉ D ⊔ Subgroup.zpowers r →
      16 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)) < Nat.card D) :
    ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      ∀ Q : Subgroup G, Q ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) → ¬ Q ≤ D →
      (∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) →
      4 * D.relIndex Q * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer (Q : Set G)) < Nat.card D := by
  intro x hx Q hQR hQD _
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set D' : Subgroup G := D ⊔ Subgroup.zpowers r with hD'
  have hDD' : D ≤ D' := le_sup_left
  have hQR' := hQR
  rw [hRrs] at hQR'
  have hCle : ∀ y ∈ Q, D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
      Subgroup.centralizer (Q : Set G) ≤ D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G) := fun y hy z hz =>
    ⟨hz.1, Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hz.2 y hy).symm)⟩
  by_cases hQD' : Q ≤ D'
  ·
    have hidx := relIndex_le_two_of_le_sup_zpowers hrN hr2 hQD'
    obtain ⟨q₀, hq₀Q, hq₀D⟩ := SetLike.not_le_iff_exists.mp hQD
    have hq₀ : r⁻¹ * q₀ ∈ D :=
      (mem_or_inv_mul_mem_of_mem_sup_zpowers hrN hr2 (hQD' hq₀Q)).resolve_left hq₀D
    have hCr : D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer ({q₀} : Set G) = D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
          Subgroup.centralizer ({r} : Set G) := by
      have e1 : q₀ = r * (r⁻¹ * q₀) := by rw [mul_inv_cancel_left]
      ext z
      constructor
      · intro hz
        refine ⟨hz.1, ?_⟩
        have hz' : z ∈ D ⊓ Subgroup.centralizer ({r * (r⁻¹ * q₀)} : Set G) :=
          ⟨hz.1.1, by rw [← e1]; exact hz.2⟩
        rw [inf_centralizer_mul_of_mem hcommD hq₀] at hz'
        exact hz'.2
      · intro hz
        refine ⟨hz.1, ?_⟩
        have hz' : z ∈ D ⊓ Subgroup.centralizer ({r} : Set G) := ⟨hz.1.1, hz.2⟩
        rw [← inf_centralizer_mul_of_mem hcommD hq₀, ← e1] at hz'
        exact hz'.2
    have hcard := Subgroup.card_le_of_le (hCle q₀ hq₀Q)
    rw [hCr] at hcard
    have hg := hgood x hx
    calc 4 * D.relIndex Q * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
          Subgroup.centralizer (Q : Set G))
        ≤ 4 * 2 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
          Subgroup.centralizer ({r} : Set G)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 4 hidx) hcard
      _ < Nat.card D := by omega
  ·
    obtain ⟨y, hyQ, hyD'⟩ := SetLike.not_le_iff_exists.mp hQD'
    have hidx1 := relIndex_le_two_of_le_sup_zpowers hsN hs2 hQR'
    have hidx2 := relIndex_le_two_of_le_sup_zpowers hrN hr2 (inf_le_left : D' ⊓ Q ≤ D')
    have htower : D.relIndex Q = D.relIndex (D' ⊓ Q) * D'.relIndex Q := by
      rw [Subgroup.relIndex_inf_mul_relIndex D D' Q, inf_eq_left.mpr hDD']
    have hidx : D.relIndex Q ≤ 4 := by
      rw [htower]
      calc D.relIndex (D' ⊓ Q) * D'.relIndex Q ≤ 2 * 2 := Nat.mul_le_mul hidx2 hidx1
        _ = 4 := by norm_num
    have hcard := Subgroup.card_le_of_le (hCle y hyQ)
    have hb := hbad x hx y (hQR hyQ) hyD'
    calc 4 * D.relIndex Q * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
          Subgroup.centralizer (Q : Set G))
        ≤ 4 * 4 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
          Subgroup.centralizer ({y} : Set G)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 4 hidx) hcard
      _ < Nat.card D := by omega

end CFSG.CGT.Stroth77
