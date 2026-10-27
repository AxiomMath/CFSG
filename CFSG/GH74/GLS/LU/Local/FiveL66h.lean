module

public import CFSG.GH74.GLS.LU.Local.FiveL66g

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

section TSyl

variable {G : Type} [Group G] [Finite G]

theorem mem_mul_of_C0 {C₀ T Xs : Subgroup G} {s : G}
    (heq : centralizer ({s} : Set G) ⊓ C₀ = Xs ⊔ T)
    (hnorm : ∀ g ∈ centralizer ({s} : Set G) ⊓ C₀, ∀ x ∈ Xs, g * x * g⁻¹ ∈ Xs)
    {q : G} (hq : q ∈ centralizer ({s} : Set G) ⊓ C₀) : ∃ a ∈ Xs, ∃ τ ∈ T, q = a * τ := by
  have hTle : T ≤ normalizer (Xs : Set G) := by
    intro g hg
    have hg' : g ∈ centralizer ({s} : Set G) ⊓ C₀ := by
      rw [heq]; exact Subgroup.mem_sup_right hg
    exact CFSG.Walter.J1.mem_normalizer_of_conj_mem (hnorm g hg')
  have hq' : q ∈ Xs ⊔ T := by rw [← heq]; exact hq
  have h1 : q ∈ (Xs : Set G) * (T : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Xs T hTle]; exact hq'
  obtain ⟨a, ha, τ, hτ, rfl⟩ := h1
  exact ⟨a, ha, τ, hτ, rfl⟩

omit [Finite G] in
theorem eq_one_of_two_group_of_pow_five {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q) {a : G} (ha : a ∈ Q)
    (h5 : a ^ 5 = 1) : a = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨a, ha⟩
  have hk' : a ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h1 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf a ∣ 5 := orderOf_dvd_of_pow_eq_one h5
  have h3 : orderOf a ∣ Nat.gcd (2 ^ k) 5 := Nat.dvd_gcd h1 h2
  have hcop : Nat.gcd (2 ^ k) 5 = 1 := Nat.Coprime.pow_left k (by norm_num)
  rw [hcop] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem max_two_of_C0 {C₀ T : Subgroup G} (hTcard : Nat.card ↥T = 4)
    (hT2 : ∀ a ∈ T, a * a = 1)
    (hC0 : ∀ s ∈ T, s ≠ 1 → ∃ Xs : Subgroup G, IsElemAb 5 Xs ∧
      centralizer ({s} : Set G) ⊓ C₀ = Xs ⊔ T ∧
      ∀ g ∈ centralizer ({s} : Set G) ⊓ C₀, ∀ x ∈ Xs, g * x * g⁻¹ ∈ Xs)
    {Q : Subgroup G} (hQC : Q ≤ C₀) (hQ : IsPGroup 2 ↥Q) (hTQ : T ≤ Q) : Q = T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ hTQ
  obtain ⟨s₀, hs₀T, hs₀1⟩ : ∃ s ∈ T, s ≠ 1 := by
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := T)).mp
      ((Subgroup.one_lt_card_iff_ne_bot T).mp (by rw [hTcard]; norm_num))
    exact ⟨a, a.2, fun h1 => ha (Subtype.ext h1)⟩
  have hQnt : Nontrivial ↥Q :=
    ⟨⟨⟨s₀, hTQ hs₀T⟩, 1, fun h => hs₀1 (congrArg Subtype.val h)⟩⟩
  have : Nontrivial (Subgroup.center ↥Q) := hQ.center_nontrivial
  have hZp : IsPGroup 2 ↥(Subgroup.center ↥Q) := hQ.to_subgroup _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hZp
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : Nat.card ↥(Subgroup.center ↥Q) = 1 := by rw [hn]; simp
    exact (not_nontrivial_iff_subsingleton.mpr (Nat.card_eq_one_iff_unique.mp h1).1) inferInstance
  have h2 : 2 ∣ Nat.card ↥(Subgroup.center ↥Q) := by rw [hn]; exact dvd_pow_self 2 hn0
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set y : G := (((y₀ : ↥Q)) : G) with hy
  have hyord : orderOf y = 2 := by
    rw [hy, Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hy₀
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hyord, pow_two] at this
  have hy1 : y ≠ 1 := by
    intro h; rw [h, orderOf_one] at hyord; omega
  have hyQ : y ∈ Q := ((y₀ : ↥Q)).2
  have hycomm : ∀ q ∈ Q, q * y = y * q := by
    intro q hq
    have h1 := Subgroup.mem_center_iff.mp y₀.2 ⟨q, hq⟩
    exact congrArg Subtype.val h1
  have hyT : y ∈ T := by
    obtain ⟨X, hXab, heq, hnorm⟩ := hC0 s₀ hs₀T hs₀1
    have hyc : y ∈ centralizer ({s₀} : Set G) ⊓ C₀ :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hycomm s₀ (hTQ hs₀T)).symm, hQC hyQ⟩
    obtain ⟨a, haX, τ, hτ, hyaτ⟩ := mem_mul_of_C0 heq hnorm hyc
    have hτ2 : τ * τ = 1 := hT2 τ hτ
    have hτy : τ * y = y * τ := hycomm τ (hTQ hτ)
    have ha : a = y * τ⁻¹ := eq_mul_inv_of_mul_eq hyaτ.symm
    have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
    have haa : a * a = 1 := by
      rw [ha, hτi]
      calc y * τ * (y * τ) = y * (τ * y) * τ := by group
        _ = y * (y * τ) * τ := by rw [hτy]
        _ = (y * y) * (τ * τ) := by group
        _ = 1 := by rw [hy2, hτ2, one_mul]
    have ha5 : a ^ 5 = 1 := hXab.2 a haX
    have ha1 : a = 1 := by
      calc a = a ^ 5 * ((a * a)⁻¹) ^ 2 := by group
        _ = 1 := by rw [ha5, haa]; simp
    rw [hyaτ, ha1, one_mul]
    exact hτ
  obtain ⟨X, hXab, heq, hnorm⟩ := hC0 y hyT hy1
  intro q hq
  have hqc : q ∈ centralizer ({y} : Set G) ⊓ C₀ :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hycomm q hq), hQC hq⟩
  obtain ⟨a, haX, τ, hτ, hqaτ⟩ := mem_mul_of_C0 heq hnorm hqc
  have haQ : a ∈ Q := by
    have : a = q * τ⁻¹ := eq_mul_inv_of_mul_eq hqaτ.symm
    rw [this]
    exact Q.mul_mem hq (Q.inv_mem (hTQ hτ))
  have ha1 : a = 1 := eq_one_of_two_group_of_pow_five hQ haQ (hXab.2 a haX)
  rw [hqaτ, ha1, one_mul]
  exact hτ

theorem isSylowIn_two_of_C0 {C₀ T : Subgroup G} (hTC : T ≤ C₀) (hTcard : Nat.card ↥T = 4)
    (hT2 : ∀ a ∈ T, a * a = 1)
    (hC0 : ∀ s ∈ T, s ≠ 1 → ∃ Xs : Subgroup G, IsElemAb 5 Xs ∧
      centralizer ({s} : Set G) ⊓ C₀ = Xs ⊔ T ∧
      ∀ g ∈ centralizer ({s} : Set G) ⊓ C₀, ∀ x ∈ Xs, g * x * g⁻¹ ∈ Xs) :
    IsSylowIn 2 T C₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 ↥T := IsPGroup.of_card (n := 2) (by rw [hTcard]; norm_num)
  refine ⟨hTC, hTp, ?_⟩
  have hTp' : IsPGroup 2 ↥(T.subgroupOf C₀) := hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
  obtain ⟨R, hR⟩ := hTp'.exists_le_sylow
  have hRp : IsPGroup 2 ↥((R : Subgroup ↥C₀).map C₀.subtype) :=
    R.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ C₀.subtype C₀.subtype_injective)
  have hTQ : T ≤ (R : Subgroup ↥C₀).map C₀.subtype := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hTC hx⟩, hR (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hmax := max_two_of_C0 hTcard hT2 hC0 (Subgroup.map_subtype_le _) hRp hTQ
  have hRT : (R : Subgroup ↥C₀) = T.subgroupOf C₀ := by
    apply le_antisymm
    · intro x hx
      have : (x : G) ∈ (R : Subgroup ↥C₀).map C₀.subtype := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hmax] at this
      exact Subgroup.mem_subgroupOf.mpr this
    · exact hR
  rw [← hRT]
  exact R.not_dvd_index

end TSyl

section C0Struct

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
  {t u : G} {Gs : Type} [Group Gs] {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ht : t ∈ Cz z} {hu : u ∈ Cz z} {ψ : ↥(Cz z) ≃* ↥(Cz z')}

omit [Finite G] in
theorem ModelPic.exists_q (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ) :
    ∃ q : G, q * z = z * q ∧ q * u = u * q ∧ q * t * q⁻¹ = z * t := by
  obtain ⟨p', hp'z, hp'u, hp't⟩ := pic.facts.t_conj
  have hp'C : p' ∈ Cz z' := Subgroup.mem_centralizer_singleton_iff.mpr hp'z
  obtain ⟨q, hqC, hψq⟩ := exists_psi_eq ψ hp'C
  have hzC : z ∈ Cz z := mem_Cz_self z
  have h1 : pe ψ q hqC = p' := hψq
  have h2 : pe ψ t ht = t' := pic.psi_t
  have h3 : pe ψ z hzC = z' := pic.psi_z
  have h4 : pe ψ u hu = u' := pic.psi_u
  refine ⟨q, Subgroup.mem_centralizer_singleton_iff.mp hqC, ?_, ?_⟩
  · refine (pe_comm_iff ψ hqC hu).mpr ?_
    rw [h1, h4]; exact hp'u
  · have hzt : z * t ∈ Cz z := (Cz z).mul_mem hzC ht
    have hqtq : q * t * q⁻¹ ∈ Cz z :=
      (Cz z).mul_mem ((Cz z).mul_mem hqC ht) ((Cz z).inv_mem hqC)
    refine (pe_eq_iff ψ hqtq hzt).mp ?_
    rw [pe_conj ψ hqC ht, pe_mul ψ hzC ht, h1, h2, h3]
    exact hp't

theorem FiveCtx.XB_le_K₂ (c : FiveCtx G p f z S K₁ K₂ t u) {X₁ : Subgroup G} (h : X₁ ≤ K₁) :
    XB t X₁ ≤ K₂ := by
  have := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) h
  rwa [c.hs.t_swap] at this

theorem FiveCtx.XX_cent_z (c : FiveCtx G p f z S K₁ K₂ t u) {X₁ : Subgroup G} (h : X₁ ≤ K₁) :
    ∀ a ∈ XX t X₁, a * z = z * a := by
  have h1 : XX t X₁ ≤ centralizer ({z} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact c.hc.cz₁ (h ha)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact c.hc.cz₂ (c.XB_le_K₂ h ha)
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (h1 ha)

theorem FiveCtx.u_inv_XX (c : FiveCtx G p f z S K₁ K₂ t u) {X₁ : Subgroup G} (h : X₁ ≤ K₁)
    (hX₁u : ∀ x ∈ X₁, u * x * u⁻¹ = x⁻¹) : ∀ x ∈ XX t X₁, u * x * u⁻¹ = x⁻¹ := by
  have hcomm : ∀ a ∈ X₁, ∀ b ∈ XB t X₁, a * b = b * a := fun a ha b hb =>
    c.hc.comm a (h ha) b (c.XB_le_K₂ h hb)
  have hut : u * t = t * u := c.hs.ut
  have e1 : t * u * t⁻¹ = u := by
    calc t * u * t⁻¹ = (u * t) * t⁻¹ := by rw [hut]
      _ = u := by group
  have hXB : ∀ b ∈ XB t X₁, u * b * u⁻¹ = b⁻¹ := by
    intro b hb
    have ha : t⁻¹ * b * t ∈ X₁ := mem_cjL.mp hb
    have h1 := hX₁u _ ha
    calc u * b * u⁻¹ = (t * u * t⁻¹) * b * (t * u * t⁻¹)⁻¹ := by rw [e1]
      _ = t * (u * (t⁻¹ * b * t) * u⁻¹) * t⁻¹ := by group
      _ = t * (t⁻¹ * b * t)⁻¹ * t⁻¹ := by rw [h1]
      _ = b⁻¹ := by group
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute hcomm).mp hx
  have e : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
  rw [e, hX₁u a ha, hXB b hb]
  calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := (mul_inv_rev b a).symm
    _ = (a * b)⁻¹ := by rw [hcomm a ha b hb]

theorem ModelPic.five82_C0 (c : FiveCtx G p f z S K₁ K₂ t u)
    (pic : ModelPic z t u K₁ K₂ c.t_mem_Cz c.u_mem_Cz z' S' K₁' K₂' t' u' ψ)
    {X₁ : Subgroup G} (hX₁le : X₁ ≤ K₁) (hX₁u : ∀ x ∈ X₁, u * x * u⁻¹ = x⁻¹)
    (hX0c : Nat.card ↥(XZ t X₁) = 5) :
    ∀ s ∈ TT z t, s ≠ 1 → ∃ Xs : Subgroup G, Xs ≤ CZ t X₁ ∧ IsElemAb 5 Xs ∧
      Nat.card ↥Xs = 25 ∧ (∀ x ∈ Xs, u * x * u⁻¹ = x⁻¹) ∧
      centralizer ({s} : Set G) ⊓ CZ t X₁ = Xs ⊔ TT z t ∧ Xs ⊓ TT z t = ⊥ ∧
      ∀ g ∈ centralizer ({s} : Set G) ⊓ CZ t X₁, ∀ x ∈ Xs, g * x * g⁻¹ ∈ Xs := by
  classical
  have hz2 : z * z = 1 := c.hs.z_sq
  have ht2 : t * t = 1 := c.hs.t_sq
  have hzt : z * t = t * z := c.hs.zt_comm
  have hzu : z * u = u * z := c.hs.zu_comm
  have hut : u * t = t * u := c.hs.ut
  have hX₀z : ∀ x ∈ XZ t X₁, z * x = x * z := fun x hx => (c.XX_cent_z hX₁le x hx.1).symm
  have hX₀t : ∀ x ∈ XZ t X₁, t * x = x * t := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
  have hX₀u : ∀ x ∈ XZ t X₁, u * x * u⁻¹ = x⁻¹ := fun x hx => c.u_inv_XX hX₁le hX₁u x hx.1
  intro s hsT hs1
  have hmem := (mem_UU_iff (u := t) hz2 ht2 hzt).mp hsT
  rcases hmem with h | h | h | h
  · exact absurd h hs1
  ·
    rw [h]
    have hgu : (1 : G) * u * (1 : G)⁻¹ ∈ normalizer (K₁ : Set G) := by
      simpa using c.hs.u_norm
    obtain ⟨Xs, h1, h2, h3, h4, h5, h6, h7⟩ := pic.c0_key hX0c hX₀u (s := z) (r := t) (g := 1)
      (by simp) hzt.symm ht2 c.t_ne_one c.t_ne_z hX₀z hX₀t hzu.symm hgu
    rw [TT_eq_sup_of (z := z) (t := t) (s := z) (r := t) (Or.inl ⟨rfl, rfl⟩)] at h5 h6
    exact ⟨Xs, h1, h2, h3, h4, h5, h6, h7⟩
  ·
    rw [h]
    obtain ⟨g, hgt, hJ₁, -⟩ := c.toLUCtx.h61.u_norm_J
    have hg : g * t * g⁻¹ = z := by rw [← hgt]; group
    obtain ⟨Xs, h1, h2, h3, h4, h5, h6, h7⟩ := pic.c0_key hX0c hX₀u (s := t) (r := z) (g := g)
      hg hzt hz2 c.z_ne_one c.t_ne_z.symm hX₀t hX₀z hut (conj_mem_normalizer_of_cj hJ₁)
    rw [TT_eq_sup_of (z := z) (t := t) (s := t) (r := z) (Or.inr (Or.inl ⟨rfl, rfl⟩))] at h5 h6
    exact ⟨Xs, h1, h2, h3, h4, h5, h6, h7⟩
  ·
    rw [h]
    obtain ⟨g, hgt, hJ₁, -⟩ := c.toLUCtx.h61.u_norm_J
    have hg : g * t * g⁻¹ = z := by rw [← hgt]; group
    have hgu : g * u * g⁻¹ ∈ normalizer (K₁ : Set G) := conj_mem_normalizer_of_cj hJ₁
    obtain ⟨q, hqz, hqu, hqt⟩ := pic.exists_q
    have hq3 : q⁻¹ * (z * t) * q = t := by rw [← hqt]; group
    have hq4 : q⁻¹ * u * q = u := by
      calc q⁻¹ * u * q = q⁻¹ * (u * q) := by group
        _ = q⁻¹ * (q * u) := by rw [hqu]
        _ = u := by group
    have hg' : (g * q⁻¹) * (z * t) * (g * q⁻¹)⁻¹ = z := by
      calc (g * q⁻¹) * (z * t) * (g * q⁻¹)⁻¹ = g * (q⁻¹ * (z * t) * q) * g⁻¹ := by group
        _ = z := by rw [hq3]; exact hg
    have hgu' : (g * q⁻¹) * u * (g * q⁻¹)⁻¹ ∈ normalizer (K₁ : Set G) := by
      have e : (g * q⁻¹) * u * (g * q⁻¹)⁻¹ = g * (q⁻¹ * u * q) * g⁻¹ := by group
      rw [e, hq4]; exact hgu
    have hrs : z * (z * t) = (z * t) * z := by
      calc z * (z * t) = z * (t * z) := by rw [hzt]
        _ = (z * t) * z := (mul_assoc z t z).symm
    have hne : z ≠ z * t := by
      intro h'
      apply c.t_ne_one
      calc t = z⁻¹ * (z * t) := by group
        _ = z⁻¹ * z := by rw [← h']
        _ = 1 := by group
    have hX₀zt : ∀ x ∈ XZ t X₁, (z * t) * x = x * (z * t) := by
      intro x hx
      calc z * t * x = z * (t * x) := by rw [mul_assoc]
        _ = z * (x * t) := by rw [hX₀t x hx]
        _ = (z * x) * t := by rw [mul_assoc]
        _ = (x * z) * t := by rw [hX₀z x hx]
        _ = x * (z * t) := by rw [mul_assoc]
    have huzt : u * (z * t) = (z * t) * u := by
      calc u * (z * t) = (u * z) * t := by rw [mul_assoc]
        _ = (z * u) * t := by rw [← hzu]
        _ = z * (u * t) := by rw [mul_assoc]
        _ = z * (t * u) := by rw [hut]
        _ = (z * t) * u := by rw [mul_assoc]
    obtain ⟨Xs, h1, h2, h3, h4, h5, h6, h7⟩ := pic.c0_key hX0c hX₀u (s := z * t) (r := z)
      (g := g * q⁻¹) hg' hrs hz2 c.z_ne_one hne hX₀zt hX₀z huzt hgu'
    rw [TT_eq_sup_of (z := z) (t := t) (s := z * t) (r := z) (Or.inr (Or.inr ⟨rfl, rfl⟩))] at h5 h6
    exact ⟨Xs, h1, h2, h3, h4, h5, h6, h7⟩

end C0Struct

section Five82WAssembly

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
  {t u : G} {Gs : Type} [Group Gs] {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ψ : ↥(Cz z) ≃* ↥(Cz z')}

theorem FiveCtx.TT_sq (c : FiveCtx G p f z S K₁ K₂ t u) : ∀ a ∈ TT z t, a * a = 1 := by
  have hzt : ∀ a ∈ zpowers z, ∀ b ∈ zpowers t, a * b = b * a :=
    commute_zpowers_zu c.hs.zt_comm
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_of_commute hzt).mp ha
  have hx2 : x * x = 1 := by
    rcases mem_zpowers_of_sq_eq_one c.hs.z_sq hx with h | h
    · rw [h, one_mul]
    · rw [h]; exact c.hs.z_sq
  have hy2 : y * y = 1 := by
    rcases mem_zpowers_of_sq_eq_one c.hs.t_sq hy with h | h
    · rw [h, one_mul]
    · rw [h]; exact c.hs.t_sq
  have hxy := hzt x hx y hy
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [← hxy]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx2, hy2, one_mul]

theorem ModelPic.exists_five82W (c : FiveCtx G p f z S K₁ K₂ t u)
    (pic : ModelPic z t u K₁ K₂ c.t_mem_Cz c.u_mem_Cz z' S' K₁' K₂' t' u' ψ)
    {H : Subgroup G} {w₁ : G} (b66 : Five66W z t u K₁ K₂ H w₁) :
    ∃ X₁ : Subgroup G, Five82W z t u K₁ K₂ H w₁ X₁ := by
  obtain ⟨X₁, hle, hsyl, hcard, hH, hgen, hXu, hNC2, hCC2, hNCX, hsylinv, hXinv, hX0c⟩ :=
    pic.five82_core c.card_K₁ c.card_Cz b66
  have hC0 := pic.five82_C0 c hle hXu hX0c
  have hTC : TT z t ≤ CZ t X₁ := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact c.XX_cent_z hle h hh.1
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp hh.2
  refine ⟨X₁, hsyl, hcard, hH, hgen, c.card_Cz, ?_, hC0, hNC2, hCC2, hNCX, hsylinv, hXinv⟩
  refine isSylowIn_two_of_C0 hTC c.card_TT c.TT_sq (fun s hs hs1 => ?_)
  obtain ⟨Xs, -, h2, -, -, h5, -, h7⟩ := hC0 s hs hs1
  exact ⟨Xs, h2, h5, h7⟩

end Five82WAssembly

end CFSG.GH74.GLS.LU.Local.Five
