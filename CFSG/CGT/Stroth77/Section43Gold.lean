module

public import CFSG.CGT.Stroth77.Section43
public import CFSG.CGT.Timmesfeld75.Sec4CaseIGDich

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace Stroth43Gold

section Cyclic

variable {Y : Type*} [Group Y]

theorem mem_zpowers_sq_of_sq_eq_one {b x : Y} (hb4 : b ^ 4 = 1) (hb2 : b ^ 2 ≠ 1)
    (hx : x ∈ Subgroup.zpowers b) (hx2 : x ^ 2 = 1) : x ∈ Subgroup.zpowers (b ^ 2) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h4 : b ^ (4 : ℤ) = 1 := by exact_mod_cast hb4
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · exact Subgroup.mem_zpowers_iff.2 ⟨n, by rw [← zpow_natCast, ← zpow_mul]; norm_num⟩
  · refine absurd ?_ hb2
    have h : (b ^ (2 * n + 1)) ^ 2 = b ^ 2 := by
      rw [← zpow_natCast (b ^ (2 * n + 1)), ← zpow_mul, ← zpow_natCast b 2,
        show (2 * n + 1) * ((2 : ℕ) : ℤ) = 4 * n + ((2 : ℕ) : ℤ) by push_cast; ring, zpow_add,
        zpow_mul, h4, one_zpow, one_mul]
    rw [← h, hx2]

theorem mem_zpowers_of_not_mem_zpowers_sq {b x : Y} (hb4 : b ^ 4 = 1)
    (hx : x ∈ Subgroup.zpowers b) (hx2 : x ∉ Subgroup.zpowers (b ^ 2)) :
    b ∈ Subgroup.zpowers x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h4 : b ^ (4 : ℤ) = 1 := by exact_mod_cast hb4
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · exact absurd (Subgroup.mem_zpowers_iff.2 ⟨n, by rw [← zpow_natCast, ← zpow_mul]; norm_num⟩)
      hx2
  · refine Subgroup.mem_zpowers_iff.2 ⟨2 * n + 1, ?_⟩
    rw [← zpow_mul, show (2 * n + 1) * (2 * n + 1) = 4 * (n * n + n) + 1 by ring, zpow_add,
      zpow_mul, h4, one_zpow, one_mul, zpow_one]

theorem not_mem_zpowers_sq_of_pow_four {b : Y} (hb4 : b ^ 4 = 1) (hb2 : b ^ 2 ≠ 1) :
    b ∉ Subgroup.zpowers (b ^ 2) := by
  intro hb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h4 : b ^ (4 : ℤ) = 1 := by exact_mod_cast hb4
  apply hb2
  calc b ^ 2 = ((b ^ 2) ^ k) ^ 2 := by rw [hk]
    _ = (b ^ (4 : ℤ)) ^ k := by
      rw [← zpow_natCast ((b ^ 2) ^ k) 2, ← zpow_mul, ← zpow_natCast b 2, ← zpow_mul,
        ← zpow_mul]
      congr 1
      push_cast
      ring
    _ = 1 := by rw [h4, one_zpow]

theorem mem_of_zpowers_eq_sup {b : Y} (hb4 : b ^ 4 = 1) (hb2 : b ^ 2 ≠ 1) {H : Subgroup Y}
    {s : Set Y} (hs : ∀ t ∈ s, t ^ 2 = 1) (h : Subgroup.zpowers b = H ⊔ Subgroup.closure s) :
    b ∈ H := by
  have hHb : H ≤ Subgroup.zpowers b := by rw [h]; exact le_sup_left
  have hsb : Subgroup.closure s ≤ Subgroup.zpowers (b ^ 2) := by
    rw [Subgroup.closure_le]
    intro t ht
    have htb : t ∈ Subgroup.zpowers b := by
      rw [h]; exact Subgroup.mem_sup_right (Subgroup.subset_closure ht)
    exact mem_zpowers_sq_of_sq_eq_one hb4 hb2 htb (hs t ht)
  by_contra hbH
  have hH2 : H ≤ Subgroup.zpowers (b ^ 2) := fun x hx => by
    by_contra hx2
    exact hbH (Subgroup.zpowers_le.2 hx (mem_zpowers_of_not_mem_zpowers_sq hb4 (hHb hx) hx2))
  have hb : b ∈ H ⊔ Subgroup.closure s := by rw [← h]; exact Subgroup.mem_zpowers b
  exact not_mem_zpowers_sq_of_pow_four hb4 hb2 (sup_le hH2 hsb hb)

theorem not_mem_of_odd_card_of_sq {H : Subgroup Y} (hH : Odd (Nat.card H)) {x : Y}
    (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) : x ∉ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hx
  have h2 := Subgroup.orderOf_dvd_natCard H hx
  rw [orderOf_eq_prime hx2 hx1] at h2
  exact Nat.not_even_iff_odd.2 hH (even_iff_two_dvd.2 h2)

theorem zpowers_subgroupOf_eq {M : Subgroup Y} {a : Y} (ha : a ∈ M) :
    (Subgroup.zpowers a).subgroupOf M = Subgroup.zpowers ⟨a, ha⟩ := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩

end Cyclic

theorem false_of_cyclic_four (hGold : CFSG.CGT.Timmesfeld75.Goldschmidt1974)
    {X : Type} [Group X] [Finite X] (T : Sylow 2 X) {a : X} (haT : a ∈ (T : Subgroup X))
    (ha4 : a ^ 4 = 1) (ha2 : a ^ 2 ≠ 1)
    (hsc : ∀ y ∈ Subgroup.zpowers a, ∀ g : X, g⁻¹ * y * g ∈ (T : Subgroup X) →
      g⁻¹ * y * g ∈ Subgroup.zpowers a)
    {e g : X} (he : e⁻¹ * a * e = a⁻¹) (hg : g⁻¹ * e * g * a = a * (g⁻¹ * e * g)) : False := by
  obtain ⟨-, hb, -⟩ := hGold X T (Subgroup.zpowers a) (Subgroup.zpowers_le.2 haT)
    (Subgroup.zpowers_isMulCommutative a) hsc
  set M : Subgroup X := Subgroup.normalClosure ((Subgroup.zpowers a : Subgroup X) : Set X)
  haveI hMn : M.Normal := Subgroup.normalClosure_normal
  have haM : a ∈ M := Subgroup.le_normalClosure (Subgroup.mem_zpowers a)
  set O : Subgroup ↥M := CFSG.Open.goldschmidtOddCore ↥M with hO
  rw [zpowers_subgroupOf_eq haM, MonoidHom.map_zpowers] at hb
  set ā : ↥M ⧸ O := QuotientGroup.mk' O ⟨a, haM⟩ with hā
  have hOodd : Odd (Nat.card O) := CFSG.CGT.Timmesfeld75.odd_card_goldschmidtOddCore ↥M
  have hā4 : ā ^ 4 = 1 := by
    rw [hā, ← map_pow, show (⟨a, haM⟩ : ↥M) ^ 4 = 1 from Subtype.ext (by simpa using ha4),
      map_one]
  have hā2 : ā ^ 2 ≠ 1 := by
    intro h
    rw [hā, ← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h
    refine not_mem_of_odd_card_of_sq hOodd ?_ ?_ h
    · intro h1
      exact ha2 (by simpa using congrArg Subtype.val h1)
    · exact Subtype.ext (by simp [← pow_mul, ha4])
  have hāP : ā ∈ CFSG.pCore 2 (↥M ⧸ O) := mem_of_zpowers_eq_sup hā4 hā2 (fun t ht => ht.2) hb
  have hPā : CFSG.pCore 2 (↥M ⧸ O) ≤ Subgroup.zpowers ā := by rw [hb]; exact le_sup_left
  have hOchar : O.Characteristic := by
    rw [hO, CFSG.Goldschmidt.goldschmidtOddCore_eq_pPrimeCore]; infer_instance
  have hψ : ∀ k : X, ∃ ψ : MulAut (↥M ⧸ O), ∀ m : ↥M,
      ψ (QuotientGroup.mk' O m) = QuotientGroup.mk' O ⟨k * m * k⁻¹, hMn.conj_mem _ m.2 k⟩ := by
    intro k
    refine ⟨QuotientGroup.congr O O (MulAut.conjNormal k)
      (Subgroup.characteristic_iff_map_eq.1 hOchar _), fun m => ?_⟩
    exact congrArg (QuotientGroup.mk' O) (Subtype.ext (MulAut.conjNormal_apply k m))
  set w := g * a * g⁻¹ with hw
  have hwM : w ∈ M := hMn.conj_mem a haM g
  have hew : e⁻¹ * w * e = w := by
    have h1 : e * w = w * e := by
      calc e * w = g * (g⁻¹ * e * g * a) * g⁻¹ := by rw [hw]; group
        _ = g * (a * (g⁻¹ * e * g)) * g⁻¹ := by rw [hg]
        _ = w * e := by rw [hw]; group
    calc e⁻¹ * w * e = e⁻¹ * (e * w) := by rw [h1]; group
      _ = w := by group
  obtain ⟨ψ, hψg⟩ := hψ g
  have hwP : QuotientGroup.mk' O ⟨w, hwM⟩ ∈ Subgroup.zpowers ā := by
    apply hPā
    have h2 : ψ ā ∈ CFSG.pCore 2 (↥M ⧸ O) := by
      have hfix := (inferInstance : (CFSG.pCore 2 (↥M ⧸ O)).Characteristic).fixed ψ
      rw [← hfix] at hāP
      exact hāP
    rw [hā, hψg ⟨a, haM⟩] at h2
    exact h2
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hwP
  obtain ⟨φ, hφ⟩ := hψ e⁻¹
  have hφa : φ ā = ā⁻¹ := by
    rw [hā, hφ, ← map_inv]
    congr 1
    exact Subtype.ext (by simp [he])
  have hφw : φ (QuotientGroup.mk' O ⟨w, hwM⟩) = QuotientGroup.mk' O ⟨w, hwM⟩ := by
    rw [hφ]
    congr 1
    exact Subtype.ext (by simp [hew])
  have hinv : QuotientGroup.mk' O ⟨w, hwM⟩ = (QuotientGroup.mk' O ⟨w, hwM⟩)⁻¹ := by
    conv_lhs => rw [← hφw]
    rw [← hi, map_zpow, hφa, inv_zpow]
  have hw2 : (QuotientGroup.mk' O ⟨w, hwM⟩) ^ 2 = 1 := by
    rw [sq]
    exact mul_eq_one_iff_eq_inv.2 hinv
  rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hw2
  refine not_mem_of_odd_card_of_sq hOodd ?_ ?_ hw2
  · intro h1
    apply ha2
    have h1' : (g * a * g⁻¹) ^ 2 = 1 := congrArg Subtype.val h1
    rw [conj_pow] at h1'
    calc a ^ 2 = g⁻¹ * (g * a ^ 2 * g⁻¹) * g := by group
      _ = 1 := by rw [h1']; group
  · apply Subtype.ext
    change ((g * a * g⁻¹) ^ 2) ^ 2 = 1
    rw [← pow_mul, conj_pow, show 2 * 2 = 4 from rfl, ha4, mul_one, mul_inv_cancel]

theorem exists_sylow_centralizer_eq {H : Type*} [Group H] [Finite H] (S : Sylow 2 H) {w : H}
    (hconj : ∀ {Q : Subgroup H}, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {w} →
      ∃ k ∈ Subgroup.centralizer {w}, ∀ q ∈ Q, k⁻¹ * q * k ∈ (S : Subgroup H)) :
    ∃ T : Sylow 2 ↥(Subgroup.centralizer {w}), ∀ t : ↥(Subgroup.centralizer {w}),
      t ∈ (T : Subgroup ↥(Subgroup.centralizer {w})) ↔ (t : H) ∈ (S : Subgroup H) := by
  set C := Subgroup.centralizer ({w} : Set H)
  set Q₁ := (S : Subgroup H) ⊓ C
  have hQ₁p : IsPGroup 2 Q₁ := S.isPGroup'.to_le inf_le_left
  have hQ' : IsPGroup 2 (Q₁.subgroupOf C) :=
    hQ₁p.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨T, hT⟩ := hQ'.exists_le_sylow
  refine ⟨T, fun t => ⟨fun ht => ?_, fun ht => hT (Subgroup.mem_subgroupOf.2
    (Subgroup.mem_inf.2 ⟨ht, t.2⟩))⟩⟩
  set Q := (T : Subgroup C).map C.subtype
  have hQc : Q ≤ C := Subgroup.map_subtype_le _
  obtain ⟨k, hk, hkQ⟩ := hconj (T.isPGroup'.map C.subtype) hQc
  have hle : Q.map (MulAut.conj k⁻¹).toMonoidHom ≤ Q₁ := by
    rintro _ ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact Subgroup.mem_inf.2 ⟨hkQ q hq, C.mul_mem (C.mul_mem (C.inv_mem hk) (hQc hq)) hk⟩
  have hQ₁Q : Q₁ ≤ Q := fun q hq =>
    ⟨⟨q, (Subgroup.mem_inf.1 hq).2⟩, hT (Subgroup.mem_subgroupOf.2 hq), rfl⟩
  have hcard : Nat.card Q ≤ Nat.card Q₁ := by
    rw [← Stroth76.card_map_conj k⁻¹ Q]
    exact Subgroup.card_le_of_le hle
  have hmem : (t : H) ∈ Q := ⟨t, ht, rfl⟩
  rw [← Subgroup.eq_of_le_of_card_ge hQ₁Q hcard] at hmem
  exact (Subgroup.mem_inf.1 hmem).1

end Stroth43Gold

theorem StrothFrame.IsD.false_of_t100_iv (hGold : CFSG.CGT.Timmesfeld75.Goldschmidt1974)
    {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t100 m)} (h : F.IsD D dD) (hm : 2 ≤ m)
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    {e : G} (heN : e ∈ Subgroup.normalizer (D : Set G))
    (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (he : e * e = (dD.c : G) ^ 2 ^ (m - 1))
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (h1 : (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2)
    (h2 : e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u})
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 →
      (∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = (dD.c : G) ^ 2 ^ (m - 1)) ∨
        ∃ g ∈ dD.L, g⁻¹ * y * g = (dD.a : G) ^ 2 ^ m)
    (h5 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * y ∈ D ∨ y * y * dD.uv ∈ D)
    (h6 : ∀ y : G, y * dD.uv ∈ D → y * y = 1 → ∃ E : Subgroup G,
      E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16)
    (h6' : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} → y * y ≠ 1)
    (h7 : ∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        (∀ e ∈ E, e * e = 1) → Nat.card E ≠ 16)
    (h9 : ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        IsMulCommutative X → Nat.card X = Nat.card D → X = D)
    (hc₂ : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
        y * (dD.c : G) ^ 2 ^ (m - 2) = (dD.c : G) ^ 2 ^ (m - 2) * y)
    (hsc : ∀ g ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
      ∀ y ∈ Subgroup.zpowers ((dD.c : G) ^ 2 ^ (m - 2)), g⁻¹ * y * g ∈ (F.S : Subgroup G) →
        g⁻¹ * y * g ∈ Subgroup.zpowers ((dD.c : G) ^ 2 ^ (m - 2))) :
    False := by
  haveI := F.simple
  set P := Subgroup.closure {dD.uv, dD.t, dD.u} with hP
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  set c₂ := (dD.c : G) ^ 2 ^ (m - 2) with hc₂def
  have hPN : P ≤ Subgroup.normalizer (D : Set G) := by
    rw [hP, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    exacts [dD.uv_mem, dD.t_mem, dD.u_mem]
  have hSD : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
    rw [hS]
    exact sup_le (sup_le Subgroup.le_normalizer hPN) ((Subgroup.zpowers_le).2 heN)
  have hUS : D ⊔ P ≤ (F.S : Subgroup G) := by rw [hS]; exact le_sup_left
  have hPS : P ≤ (F.S : Subgroup G) := le_sup_right.trans hUS
  have hoc : orderOf (dD.c : G) = 2 ^ m := by rw [Stroth42.orderOf_c_coe]; rfl
  obtain ⟨hz2, hz1⟩ := Stroth42.pow_mul_self_eq_one (by omega) hoc
  rw [← hz] at hz2 hz1
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hza := h.not_isConj_of_omega hnc h3
  have h3' : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z := by
    intro y hyD hy2 hy1 hyz
    rcases h3 y hyD hy2 hy1 with hp | ⟨g, -, hg⟩
    · exact hp
    · exact absurd (hyz.symm.trans (Stroth42.isConj_of_conj_eq hg).symm) hza
  rw [← hS] at h5 h6' h7 h9
  have h6U : ∀ y ∈ D ⊔ P, y * dD.uv ∈ D → y * y = 1 → ¬ IsConj y z := fun y _ hy hy2 =>
    Stroth42.not_isConj_of_e16 F.S dD.isMulCommutative h.le_S hSD hPS hzD h3' hz2 hz1 h7 h9
      (h6 y hy hy2)
  have heS : e ∈ (F.S : Subgroup G) := by
    rw [hS]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have hxz : e ^ 2 ^ 1 = z := by rw [pow_one, sq, he]
  obtain ⟨T, hT⟩ := Stroth43Gold.exists_sylow_centralizer_eq F.S (w := z) fun hQ hQz =>
    Stroth42.exists_conj_le_centralizer F.S dD.isMulCommutative h.le_S hSD hPS hzD h3' hz2 hz1
      h9 hQ hQz
  have hc₂z : c₂ ∈ Subgroup.centralizer {z} :=
    Subgroup.mem_centralizer_singleton_iff.2 (Commute.pow_pow_self (dD.c : G) _ _).eq
  have hez : e ∈ Subgroup.centralizer {z} :=
    Subgroup.mem_centralizer_singleton_iff.2 (by rw [← he, mul_assoc])
  have hc₂sq : c₂ ^ 2 = z := by
    rw [hc₂def, hz, ← pow_mul, ← pow_succ, show m - 2 + 1 = m - 1 by omega]
  have hc₂4 : c₂ ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hc₂sq, sq, hz2]
  have hec₂ : e⁻¹ * c₂ * e = c₂⁻¹ := by
    rw [hc₂def, ← Stroth42.conj_pow', hce, inv_pow]
  have hconj : ∀ g : G, g⁻¹ * e * g ∉ D ⊔ P := by
    intro g hyU
    have hyy : g⁻¹ * z * g = g⁻¹ * e * g * (g⁻¹ * e * g) := by rw [← he]; group
    have hyz : IsConj (g⁻¹ * e * g * (g⁻¹ * e * g)) z := Stroth42.isConj_of_conj_eq hyy
    have hyy2 := Stroth42.mul_self_eq_one_of_isConj hyz hz2
    have hyyD : g⁻¹ * e * g * (g⁻¹ * e * g) ∈ D := by
      rcases h5 _ (hUS hyU) with h' | h'
      · exact h'
      · exact absurd hyz (h6U _ ((D ⊔ P).mul_mem hyU hyU) h' hyy2)
    obtain ⟨p, hpP, hp⟩ := h3' _ hyyD hyy2 (Stroth42.ne_one_of_isConj hyz hz1) hyz
    have hpU : p ∈ D ⊔ P := Subgroup.mem_sup_right hpP
    have hy' : (g * p)⁻¹ * e * (g * p) = p⁻¹ * (g⁻¹ * e * g) * p := by group
    have hy'U : (g * p)⁻¹ * e * (g * p) ∈ D ⊔ P := by
      rw [hy']
      exact (D ⊔ P).mul_mem ((D ⊔ P).mul_mem ((D ⊔ P).inv_mem hpU) hyU) hpU
    have hy'sq : (g * p)⁻¹ * e * (g * p) * ((g * p)⁻¹ * e * (g * p)) = z := by
      rw [← hp]; group
    have hkz : (g * p)⁻¹ * z * (g * p) = z := by
      calc (g * p)⁻¹ * z * (g * p)
          = (g * p)⁻¹ * e * (g * p) * ((g * p)⁻¹ * e * (g * p)) := by rw [← he]; group
        _ = z := hy'sq
    have hgz : g * p ∈ Subgroup.centralizer {z} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * p * z = g * p * ((g * p)⁻¹ * z * (g * p)) := by rw [hkz]
        _ = z * (g * p) := by group
    have hy'z : (g * p)⁻¹ * e * (g * p) * z = z * ((g * p)⁻¹ * e * (g * p)) := by
      rw [← hy'sq]; group
    have hy'c₂ := hc₂ _ hy'U hy'z
    refine Stroth43Gold.false_of_cyclic_four (a := ⟨c₂, hc₂z⟩) (e := ⟨e, hez⟩)
      (g := ⟨g * p, hgz⟩) hGold T ((hT _).2 (h.le_S (D.pow_mem dD.c.2 _))) (Subtype.ext hc₂4)
      (fun h1 => hz1 (by rw [← hc₂sq]; exact congrArg Subtype.val h1)) ?_ (Subtype.ext hec₂)
      (Subtype.ext hy'c₂)
    intro y hy k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1
      (hsc k k.2 (c₂ ^ j) (Subgroup.zpow_mem_zpowers c₂ j) ((hT _).1 hk))
    exact Subgroup.mem_zpowers_iff.2 ⟨i, Subtype.ext (by simpa using hi)⟩
  have h8 : ∀ y ∈ (F.S : Subgroup G), y ∉ D ⊔ P → ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = z →
      y ^ 2 ^ 1 ≠ 1 := by
    intro y _ _ l hl hyl hy1
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' hl
    rw [pow_one] at hy1
    exact hz1 (by rw [← hyl, pow_succ', pow_mul, hy1, one_pow])
  exact Stroth42.false_of_harada (Stroth42.frame_exists_mul_ne F) F.S hUS (by rw [hS]; exact h1)
    le_sup_right heS h2 hxz hz2 hz1 dD.uv_mem dD.uv_sq h3' h5 h6U
    (fun y hyS hyU hy2 => absurd hy2 (h6' y hyS hyU)) h8 hconj

end CFSG.CGT.Stroth77
