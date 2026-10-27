module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue79
public import CFSG.CharacterTheory.Semidihedral.CenterAndOrders

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec7
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf

section OutArg

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem innOf_normal' (Q : Type) [Group Q] : (innOf Q).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨g, rfl⟩ α
  refine ⟨α g, ?_⟩
  ext x
  simp [MulAut.conj_apply]

noncomputable def phiHom' (K : Subgroup G) : ↥(normalizer (K : Set G)) →* MulAut (Hat K) where
  toFun c := phi K c c.2
  map_one' := by
    ext x
    obtain ⟨k, rfl⟩ := hatMk_surjective K x
    rw [phi_mk]
    simp
  map_mul' x y := phi_mul K x.2 y.2

omit [Finite G] in
theorem inducesInner_of_mul_odd {K : Subgroup G} {y j o : G} (hy : y ∈ normalizer (K : Set G))
    (hj : j ∈ normalizer (K : Set G)) (ho : o ∈ normalizer (K : Set G)) (hyjo : y = j * o)
    (hy2 : ∃ m : ℕ, orderOf y = 2 ^ m) (hodd : Odd (orderOf o)) (hjin : InducesInner j K) :
    InducesInner y K := by
  have : (innOf (Hat K)).Normal := innOf_normal' _
  let π : MulAut (Hat K) →* MulAut (Hat K) ⧸ innOf (Hat K) := QuotientGroup.mk' (innOf (Hat K))
  let ρ : ↥(normalizer (K : Set G)) →* MulAut (Hat K) ⧸ innOf (Hat K) := π.comp (phiHom' K)
  let Y : ↥(normalizer (K : Set G)) := ⟨y, hy⟩
  let J : ↥(normalizer (K : Set G)) := ⟨j, hj⟩
  let O : ↥(normalizer (K : Set G)) := ⟨o, ho⟩
  have hYJO : Y = J * O := Subtype.ext hyjo
  have hJ1 : ρ J = 1 := by
    show π (phi K j hj) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (phi_mem_inn_iff K hj).2 hjin
  have h1 : ρ Y = ρ O := by rw [hYJO, map_mul, hJ1, one_mul]
  have hYo : orderOf Y = orderOf y := Subgroup.orderOf_coe Y |>.symm
  have hOo : orderOf O = orderOf o := Subgroup.orderOf_coe O |>.symm
  have hd1 : orderOf (ρ Y) ∣ 2 ^ (hy2.choose) := by
    have := orderOf_map_dvd ρ Y
    rw [hYo, hy2.choose_spec] at this
    exact this
  have hd2 : orderOf (ρ Y) ∣ orderOf o := by
    have := orderOf_map_dvd ρ O
    rw [hOo, ← h1] at this
    exact this
  have hcop : Nat.Coprime (2 ^ (hy2.choose)) (orderOf o) :=
    Nat.Coprime.pow_left _ ((Nat.coprime_two_left).2 hodd)
  have hone : orderOf (ρ Y) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
  have hY1 : ρ Y = 1 := orderOf_eq_one_iff.1 hone
  have : phi K y hy ∈ innOf (Hat K) := by
    have h2 : π (phi K y hy) = 1 := hY1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact (phi_mem_inn_iff K hy).1 this

end OutArg


section Cfg

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

omit [Finite G] in
theorem mem_of_sq_mem_of_odd {H : Subgroup G} {o : G} (hsq : o * o ∈ H) (hodd : Odd (orderOf o)) :
    o ∈ H := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : o ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one o
  have h2 : (o * o) ^ (k + 1) = o := by
    calc (o * o) ^ (k + 1) = o ^ (2 * k + 2) := by rw [← pow_two, ← pow_mul]; ring_nf
      _ = o ^ (2 * k + 1) * o := by rw [pow_succ]
      _ = o := by rw [h1, one_mul]
  rw [← h2]; exact H.pow_mem hsq _

theorem norm_of_odd (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {o : G}
    (hoC : o ∈ centralizer ({z} : Set G)) (hodd : Odd (orderOf o)) :
    o ∈ normalizer (K₁ : Set G) := by
  rcases (h.m4 hII).perm o hoC with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact M.cj_eq_iff_normalizer.1 h1
  · refine mem_of_sq_mem_of_odd ?_ hodd
    apply M.cj_eq_iff_normalizer.1
    rw [← M.cj_cj, h1, h2]

theorem mem_Pz_of_inducesInner (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q)
    (hc73 : Concl73 z S K₁ K₂) {x : G} (hxS : x ∈ S) (hin : InducesInner x K₁) : x ∈ Pz S z := by
  obtain ⟨k, hk, hc⟩ := hin
  have hxC : x ∈ centralizer ({z} : Set G) := h.S_le_C hII hxS
  have hkC : k ∈ centralizer ({z} : Set G) := h.K_le_C hII (Or.inl rfl) hk
  have hcC : x * k⁻¹ ∈ centralizer ({z} : Set G) := mul_mem hxC (inv_mem hkC)
  have hX : x ∈ XK z K₁ := by
    have e : x = (x * k⁻¹) * k := by group
    rw [e]
    exact mul_mem (mem_sup_right ⟨hc, hcC⟩) (mem_sup_left hk)
  have := h.inf_XK_le hII (Or.inl rfl) x hxS hX
  rwa [h.PQ_eq hII hc73 (Or.inl rfl)] at this

omit [Finite G] in
theorem mem_conjugate_iff' {H : Subgroup G} {g x : G} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  show x ∈ H.map (MulAut.conj g⁻¹).toMonoidHom ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

end Cfg


@[expose] def IG_diag_balance : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ → ∀ q : ℕ,
    Odd q → 5 ≤ q → HatSL2 K₁ q → HatSL2 K₂ q →
      ∀ t₁ ∈ centralizer ({z} : Set G), orderOf t₁ = 2 → IsConj z t₁ → Interchanges t₁ K₁ K₂ →
        ∀ g : G, g⁻¹ * z * g = t₁ → IDiag z (conjugate K₁ g) ≤ K₁ ⊔ K₂

@[expose] def IVK_3_1b_diag : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ → ∀ q : ℕ,
    Odd q → 5 ≤ q → HatSL2 K₁ q → HatSL2 K₂ q →
      ∀ t₁ ∈ centralizer ({z} : Set G), orderOf t₁ = 2 → IsConj z t₁ → Interchanges t₁ K₁ K₂ →
        ∀ g : G, g⁻¹ * z * g = t₁ →
          ∀ k ∈ conjugate (K₁ ⊔ K₂) g ⊓ centralizer ({z} : Set G),
            ∃ ε ∈ zpowers t₁, ∃ j ∈ IDiag z (conjugate K₁ g),
              ∃ o ∈ pPrimeCoreOf 2 (conjugate (K₁ ⊔ K₂) g), k = ε * j * o


section Main

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

theorem l77_no_conj (hII : II4_4_4_center) (h73 : Lemma7_3) (hA : IG_diag_balance)
    (hB : IVK_3_1b_diag) : L77_no_conj := by
  intro G _ _ z S K₁ K₂ t u q h hidx D hD hsd h16 d₀ y hd₀ hyD hyP hyy t₁ ht₁ y₁ hy₁ hh hht hP
  have hc73 := h73 G z S K₁ K₂ t u q h
  have hzz := h.z_sq
  have hz1 := h.z_ne
  have ht2 := h.t_sq
  have hDE : D ≤ S ⊓ centralizer ({t} : Set G) := le_sup_right.trans hD.prod.1.le
  have hzS : z ∈ S := h.z_mem_S hII
  have htS : t ∈ S := h.ch.t_mem
  have hzc : ∀ s ∈ S, s * z = z * s := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.1 (h.S_le_C hII hs)
  have htz : t * z = z * t := h.t_mul_z hII
  have hd₀mem : d₀ ∈ (center ↥D).map D.subtype := by rw [hd₀]; exact mem_zpowers d₀
  obtain ⟨dd, hddc, hdd⟩ := hd₀mem
  have hd₀D : d₀ ∈ D := by rw [← hdd]; exact dd.2
  have hd₀y : y * d₀ = d₀ * y := by
    have := Subgroup.mem_center_iff.1 hddc ⟨y, hyD⟩
    have h2 := congrArg Subtype.val this
    simpa [← hdd] using h2
  have hd₀t : d₀ * t = t * d₀ := Subgroup.mem_centralizer_singleton_iff.1 (hDE hd₀D).2
  have hd₀S : d₀ ∈ S := (hDE hd₀D).1
  have hd₀2 : d₀ * d₀ = 1 := by
    obtain ⟨n, hn, ⟨e⟩⟩ := hsd
    have h1 : Nat.card ↥(center (CFSG.Open.SemidihedralGroup n)) = 2 :=
      CFSG.Semidihedral.center_card n (by omega)
    have h2 : Nat.card ↥((center ↥D).map (e : ↥D →* CFSG.Open.SemidihedralGroup n)) =
        Nat.card ↥(center ↥D) := Subgroup.card_map_of_injective e.injective
    rw [Subgroup.map_center_eq e] at h2
    have h3 : Nat.card ↥((center ↥D).map D.subtype) = Nat.card ↥(center ↥D) :=
      Subgroup.card_map_of_injective D.subtype_injective
    have h4 : Nat.card ↥(zpowers d₀) = 2 := by rw [← hd₀, h3, ← h2, h1]
    rw [Nat.card_zpowers] at h4
    exact mul_self_eq_one_of_orderOf_eq_two h4
  have hzP₁ : z ∈ Pof S K₁ := h.z_mem_P hII (Or.inl rfl)
  have hzP : z ∈ Pz S z := h.z_mem_Pz hII
  have hzS1 : z ∈ S1 S K₁ := h.P₁_le_S1 hzP₁
  have hyS1 : y ∈ S1 S K₁ := hD.le hyD
  have hyS : y ∈ S := hyS1.1
  have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.1 (hDE hyD).2
  have hd₀S1 : d₀ ∈ S1 S K₁ := hD.le hd₀D
  have hzd₀S1 : z * d₀ ∈ S1 S K₁ := (S1 S K₁).mul_mem hzS1 hd₀S1
  have hzd₀t : (z * d₀) * t = t * (z * d₀) := by
    calc (z * d₀) * t = z * (d₀ * t) := by group
      _ = z * (t * d₀) := by rw [hd₀t]
      _ = (z * t) * d₀ := by group
      _ = (t * z) * d₀ := by rw [htz]
      _ = t * (z * d₀) := by group
  have hyz : y * z = z * y := hzc y hyS
  have ht₁cases : t₁ = t ∨ t₁ = z * d₀ * t := by simpa using ht₁
  have hy₁cases : y₁ = y ∨ y₁ = y * z := by simpa using hy₁
  have ht₁S : t₁ ∈ S := by
    rcases ht₁cases with rfl | rfl
    · exact htS
    · exact S.mul_mem (S.mul_mem hzS hd₀S) htS
  have hzd₀sq : (z * d₀) * (z * d₀) = 1 := by
    have hd₀z : d₀ * z = z * d₀ := hzc d₀ hd₀S
    calc (z * d₀) * (z * d₀) = z * (d₀ * z) * d₀ := by group
      _ = z * (z * d₀) * d₀ := by rw [hd₀z]
      _ = (z * z) * (d₀ * d₀) := by group
      _ = 1 := by rw [hzz, hd₀2, mul_one]
  have ht₁sq : t₁ * t₁ = 1 := by
    rcases ht₁cases with rfl | rfl
    · exact ht2
    · calc z * d₀ * t * (z * d₀ * t) = (z * d₀) * (t * (z * d₀)) * t := by group
        _ = (z * d₀) * ((z * d₀) * t) * t := by rw [hzd₀t]
        _ = ((z * d₀) * (z * d₀)) * (t * t) := by group
        _ = 1 := by rw [hzd₀sq, ht2, mul_one]
  have hyt₁ : y * t₁ = t₁ * y := by
    rcases ht₁cases with rfl | rfl
    · exact hyt
    · calc y * (z * d₀ * t) = (y * z) * d₀ * t := by group
        _ = (z * y) * d₀ * t := by rw [hyz]
        _ = z * (y * d₀) * t := by group
        _ = z * (d₀ * y) * t := by rw [hd₀y]
        _ = z * d₀ * (y * t) := by group
        _ = z * d₀ * (t * y) := by rw [hyt]
        _ = z * d₀ * t * y := by group
  have hzt₁ : z * t₁ = t₁ * z := (hzc t₁ ht₁S).symm
  have hy₁S1 : y₁ ∈ S1 S K₁ := by
    rcases hy₁cases with rfl | rfl
    · exact hyS1
    · exact (S1 S K₁).mul_mem hyS1 hzS1
  have hy₁S : y₁ ∈ S := hy₁S1.1
  have hy₁P : y₁ ∉ Pz S z := by
    rcases hy₁cases with rfl | rfl
    · exact hyP
    · intro hmem
      apply hyP
      have := (Pz S z).mul_mem hmem ((Pz S z).inv_mem hzP)
      simpa using this
  have hconj : IsConj z t₁ := isConj_iff.2 ⟨hh, by rw [← hht]; group⟩
  have ht₁o : orderOf t₁ = 2 := orderOf_eq_two_of_isConj h.std.std.orderOf_z hconj
  have ht₁C : t₁ ∈ centralizer ({z} : Set G) := h.S_le_C hII ht₁S
  have ht₁swap : Interchanges t₁ K₁ K₂ := by
    rcases ht₁cases with rfl | rfl
    · exact h.ch.t_swap
    · rw [hzd₀t]; exact h.t_mul_swap hII hzd₀S1
  have hg : (hh⁻¹)⁻¹ * z * hh⁻¹ = t₁ := by rw [inv_inv]; rw [← hht]; group
  have hy₁K : y₁ ∈ conjugate (K₁ ⊔ K₂) hh⁻¹ := by
    rw [mem_conjugate_iff', inv_inv]
    have h1 : hh⁻¹ * y₁ * hh ∈ rigidProduct z := hP.2
    rwa [h.std.std.rigidProduct_eq] at h1
  have hy₁C : y₁ ∈ centralizer ({z} : Set G) := h.S_le_C hII hy₁S
  obtain ⟨ε, hε, j, hj, o, ho, hyeq⟩ := hB G z S K₁ K₂ h.std.std q h.ch.q_odd h.ch.q_ge h.ch.hq₁
    h.ch.hq₂ t₁ ht₁C ht₁o hconj ht₁swap hh⁻¹ hg y₁ ⟨hy₁K, hy₁C⟩
  have hjK : j ∈ K₁ ⊔ K₂ := hA G z S K₁ K₂ h.std.std q h.ch.q_odd h.ch.q_ge h.ch.hq₁ h.ch.hq₂ t₁
    ht₁C ht₁o hconj ht₁swap hh⁻¹ hg hj
  have hK₁C : K₁ ≤ centralizer ({z} : Set G) := h.K_le_C hII (Or.inl rfl)
  have hK₂C : K₂ ≤ centralizer ({z} : Set G) := h.K_le_C hII (Or.inr rfl)
  have hjC : j ∈ centralizer ({z} : Set G) := (sup_le hK₁C hK₂C) hjK
  have hKN : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set G) :=
    sup_le (fun x hx => Subgroup.le_normalizer hx) (fun x hx => (h.m4 hII).n₂₁ hx)
  have hjN : j ∈ normalizer (K₁ : Set G) := hKN hjK
  have hoodd : Odd (orderOf o) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd (conjugate (K₁ ⊔ K₂) hh⁻¹))
      (Subgroup.orderOf_dvd_natCard _ ho)
  have hεC : ε ∈ centralizer ({z} : Set G) := by
    have : zpowers t₁ ≤ centralizer ({z} : Set G) := zpowers_le.2 ht₁C
    exact this hε
  have hoC : o ∈ centralizer ({z} : Set G) := by
    have e : o = (ε * j)⁻¹ * y₁ := by rw [hyeq]; group
    rw [e]
    exact mul_mem (inv_mem (mul_mem hεC hjC)) hy₁C
  have hoN : o ∈ normalizer (K₁ : Set G) := norm_of_odd hII h hoC hoodd
  have hy₁N : y₁ ∈ normalizer (K₁ : Set G) := hy₁S1.2
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hε
  rcases B.zpow_of_sq_eq_one ht₁sq k with hε1 | hε1
  ·
    have hε' : ε = 1 := by rw [← hk, hε1]
    rw [hε', one_mul] at hyeq
    obtain ⟨b, hb, a, ha, hjba⟩ := A.mem_sup_of_le_normalizer
      (A := K₂) (B := K₁) (fun x hx => (h.m4 hII).n₂₁ hx) (by rw [sup_comm]; exact hjK)
    have hjin : InducesInner j K₁ := by
      refine ⟨a, ha, ?_⟩
      have e : j * a⁻¹ = b := by rw [hjba]; group
      rw [e]
      exact (h.m4 hII).cs₁ hb
    have hy2 : ∃ m : ℕ, orderOf y₁ = 2 ^ m := by
      obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 (h.S_pgroup hII)) ⟨y₁, hy₁S⟩
      exact ⟨m, by rw [← hm]; exact Subgroup.orderOf_coe (⟨y₁, hy₁S⟩ : ↥S)⟩
    have hin : InducesInner y₁ K₁ := inducesInner_of_mul_odd hy₁N hjN hoN hyeq hy2 hoodd hjin
    exact hy₁P (mem_Pz_of_inducesInner hII h hc73 hy₁S hin)
  ·
    have hε' : ε = t₁ := by rw [← hk, hε1]
    rw [hε'] at hyeq
    have ht₁N : t₁ ∈ normalizer (K₁ : Set G) := by
      have e : t₁ = y₁ * o⁻¹ * j⁻¹ := by rw [hyeq]; group
      rw [e]
      exact mul_mem (mul_mem hy₁N (inv_mem hoN)) (inv_mem hjN)
    have h1 : conjugate K₁ t₁ = K₁ := by
      rw [← cj_eq_conjugate]; exact M.cj_eq_iff_normalizer.2 ht₁N
    exact h.std.std.ne (h1.symm.trans ht₁swap.1)

end Main

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf
