module

public import CFSG.GH74.E2.Q8Basic

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped commutatorElement

namespace Q8

variable {X : Type*} [Group X] [Finite X] {c : MulAut X}

theorem frattini_le_of_gen {x y : X}
    (hxy : Subgroup.closure ({x, y} : Set X) = ⊤) {T : Subgroup X} [T.Normal]
    (hx : x * x ∈ T) (hy : y * y ∈ T) (hxy' : ⁅x, y⁆ ∈ T) : frattini X ≤ T := by
  let π : X →* X ⧸ T := QuotientGroup.mk' T
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective T
  have ha : π x * π x = 1 := by
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  have hb : π y * π y = 1 := by
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hy
  have hcomm : π x * π y = π y * π x := by
    have h1 : π ⁅x, y⁆ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hxy'
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_commute.1 h1).eq
  have hcl : Subgroup.closure ({π x, π y} : Set (X ⧸ T)) = ⊤ := by
    have h1 : Subgroup.closure (π '' ({x, y} : Set X)) = (Subgroup.closure ({x, y} : Set X)).map π :=
      (MonoidHom.map_closure π _).symm
    rw [hxy, Subgroup.map_top, MonoidHom.range_eq_top.2 hπ] at h1
    rw [Set.image_pair] at h1
    exact h1
  have hpair : ({π x, π y} : Set (X ⧸ T)).Pairwise Commute := by
    intro u hu v hv _
    rcases hu with rfl | hu'
    · rcases hv with rfl | hv'
      · exact Commute.refl _
      · rw [Set.mem_singleton_iff.1 hv']
        exact hcomm
    · rw [Set.mem_singleton_iff.1 hu']
      rcases hv with rfl | hv'
      · exact hcomm.symm
      · rw [Set.mem_singleton_iff.1 hv']
  have := Subgroup.isMulCommutative_closure hpair
  have hc : ∀ g h : X ⧸ T, g * h = h * g := by
    intro g h
    have hg : g ∈ Subgroup.closure ({π x, π y} : Set (X ⧸ T)) := by
      rw [hcl]
      trivial
    have hh : h ∈ Subgroup.closure ({π x, π y} : Set (X ⧸ T)) := by
      rw [hcl]
      trivial
    exact congrArg Subtype.val (mul_comm' (⟨g, hg⟩ : Subgroup.closure ({π x, π y} : Set (X ⧸ T)))
      ⟨h, hh⟩)
  have h2 : ∀ g : X ⧸ T, g * g = 1 := by
    intro g
    have hg : g ∈ Subgroup.closure ({π x, π y} : Set (X ⧸ T)) := by
      rw [hcl]
      trivial
    induction hg using Subgroup.closure_induction with
    | mem u hu =>
      rcases hu with rfl | hu'
      · exact ha
      · rw [Set.mem_singleton_iff.1 hu']
        exact hb
    | one => exact mul_one 1
    | mul u v _ _ hu hv =>
      calc u * v * (u * v) = u * u * (v * v) := by
            calc u * v * (u * v) = u * (v * u) * v := by group
              _ = u * (u * v) * v := by rw [hc v u]
              _ = u * u * (v * v) := by group
        _ = 1 := by rw [hu, hv, mul_one]
    | inv u _ hu =>
      calc u⁻¹ * u⁻¹ = (u * u)⁻¹ := by group
        _ = 1 := by rw [hu, inv_one]
  have hfr : frattini (X ⧸ T) = ⊥ := frattini_eq_bot_of_exponent_two hc h2
  have hle := frattini_le_comap_frattini_of_surjective (φ := π) hπ
  rw [hfr, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hle
  exact hle

theorem frattini_le_center (hg : Good X c) (htriv : ∀ p ∈ frattini X, c p = p) :
    frattini X ≤ Subgroup.center X := by
  have hnorm : (frattini X).Normal := inferInstance
  have hCg : ∀ g : X, g⁻¹ * c g ∈ Subgroup.centralizer (frattini X : Set X) := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have h1 : c (g * p * g⁻¹) = g * p * g⁻¹ := htriv _ (hnorm.conj_mem p hp g)
    rw [map_mul, map_mul, map_inv, htriv p hp] at h1
    calc p * (g⁻¹ * c g) = g⁻¹ * (g * p * g⁻¹) * c g := by group
      _ = g⁻¹ * (c g * p * (c g)⁻¹) * c g := by rw [h1]
      _ = (g⁻¹ * c g) * p := by group
  have hsup : Subgroup.centralizer (frattini X : Set X) ⊔ frattini X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨g, hgx⟩ := exists_inv_mul hg x
    have hxe : x = (g⁻¹ * c g) * (x⁻¹ * (g⁻¹ * c g))⁻¹ := by group
    rw [hxe]
    exact Subgroup.mul_mem_sup (hCg g) (Subgroup.inv_mem _ hgx)
  have htop : Subgroup.centralizer (frattini X : Set X) = ⊤ := frattini_nongenerating hsup
  intro p hp
  rw [Subgroup.mem_center_iff]
  intro g
  have hgC : g ∈ Subgroup.centralizer (frattini X : Set X) := by
    rw [htop]
    trivial
  exact ((Subgroup.mem_centralizer_iff.1 hgC) p hp).symm

omit [Finite X] in
theorem zpow_aux {s p e : X} {j : ℤ} (hj : s ^ j = p) (hmain : s * s * s = e * (p * p)) :
    e = s ^ (3 - 2 * j) := by
  have h1 : e = (s * s * s) * (p * p)⁻¹ := eq_mul_inv_of_mul_eq hmain.symm
  rw [h1, ← hj]
  group

theorem caseI (hg : Good X c) (hfix : ∃ t : X, t ≠ 1 ∧ c t = t)
    (htriv : ∀ p ∈ frattini X, c p = p) :
    Nat.card X = 8 ∧ ∃ x y : X, Subgroup.closure ({x, y} : Set X) = ⊤ ∧ x * x ≠ 1 ∧
      x * x * (x * x) = 1 ∧ y * y = x * x ∧ ⁅x, y⁆ = x * x := by
  have hP2 : IsPGroup 2 X := hg.pgroup
  have hcenP := frattini_le_center hg htriv
  have hcen : ∀ q ∈ frattini X, ∀ g : X, g * q = q * g := fun q hq g =>
    Subgroup.mem_center_iff.1 (hcenP hq) g
  obtain ⟨x, hx⟩ := exists_not_mem_frattini hg
  obtain ⟨y, hy⟩ : ∃ y, c x = y := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, c y = z := ⟨_, rfl⟩
  have hs : x * x ∈ frattini X := mul_self_mem_frattini hP2 x
  have he : ⁅x, y⁆ ∈ frattini X := dsub_le_frattini hP2
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  obtain ⟨p, hpdef⟩ : ∃ p, p = x * y * z := ⟨_, rfl⟩
  have hp : p ∈ frattini X := by
    have := X_norm hg x
    rw [hy, hz] at this
    rwa [hpdef]
  have hyy : y * y = x * x := by
    have := htriv (x * x) hs
    rw [map_mul, hy] at this
    exact this
  have hzz : z * z = x * x := by
    calc z * z = c (y * y) := by rw [map_mul, hz]
      _ = c (x * x) := by rw [hyy]
      _ = x * x := htriv _ hs
  have hei : ⁅x, y⁆⁻¹ ∈ frattini X := Subgroup.inv_mem _ he
  have hec : ∀ g : X, g * ⁅x, y⁆⁻¹ = ⁅x, y⁆⁻¹ * g := fun g => hcen _ hei g
  have hyx : y * x = ⁅x, y⁆⁻¹ * (x * y) := by
    rw [commutatorElement_def]
    group
  have hw2 : x * y * (x * y) = ⁅x, y⁆⁻¹ * (x * x * (x * x)) := by
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (⁅x, y⁆⁻¹ * (x * y)) * y := by rw [hyx]
      _ = (x * ⁅x, y⁆⁻¹) * (x * y) * y := by group
      _ = (⁅x, y⁆⁻¹ * x) * (x * y) * y := by rw [hec x]
      _ = ⁅x, y⁆⁻¹ * (x * x * (y * y)) := by group
      _ = ⁅x, y⁆⁻¹ * (x * x * (x * x)) := by rw [hyy]
  have he2 : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
    have h1 : y * x * y⁻¹ = ⁅x, y⁆⁻¹ * x := by
      rw [hyx]
      group
    have h3 : y * (x * x) * y⁻¹ = x * x := by
      calc y * (x * x) * y⁻¹ = (x * x) * y * y⁻¹ := by rw [hcen _ hs y]
        _ = x * x := by group
    have h4 : (⁅x, y⁆⁻¹ * x) * (⁅x, y⁆⁻¹ * x) = x * x := by
      calc (⁅x, y⁆⁻¹ * x) * (⁅x, y⁆⁻¹ * x) = (y * x * y⁻¹) * (y * x * y⁻¹) := by rw [h1]
        _ = y * (x * x) * y⁻¹ := by group
        _ = x * x := h3
    have h5 : ⁅x, y⁆⁻¹ * ⁅x, y⁆⁻¹ * (x * x) = 1 * (x * x) := by
      calc ⁅x, y⁆⁻¹ * ⁅x, y⁆⁻¹ * (x * x) = ⁅x, y⁆⁻¹ * (⁅x, y⁆⁻¹ * x) * x := by group
        _ = ⁅x, y⁆⁻¹ * (x * ⁅x, y⁆⁻¹) * x := by rw [hec x]
        _ = (⁅x, y⁆⁻¹ * x) * (⁅x, y⁆⁻¹ * x) := by group
        _ = x * x := h4
        _ = 1 * (x * x) := (one_mul _).symm
    have h6 : ⁅x, y⁆⁻¹ * ⁅x, y⁆⁻¹ = 1 := mul_right_cancel h5
    calc ⁅x, y⁆ * ⁅x, y⁆ = (⁅x, y⁆⁻¹ * ⁅x, y⁆⁻¹)⁻¹ := by group
      _ = 1 := by rw [h6, inv_one]
  have hmain : x * x * (x * x) * (x * x) = ⁅x, y⁆ * (p * p) := by
    have hzp : z = (x * y)⁻¹ * p := by
      rw [hpdef]
      group
    have h7 : z * z = (x * y * (x * y))⁻¹ * (p * p) := by
      calc z * z = ((x * y)⁻¹ * p) * ((x * y)⁻¹ * p) := by rw [← hzp]
        _ = (x * y)⁻¹ * (p * (x * y)⁻¹) * p := by group
        _ = (x * y)⁻¹ * ((x * y)⁻¹ * p) * p := by rw [← hcen p hp (x * y)⁻¹]
        _ = (x * y * (x * y))⁻¹ * (p * p) := by group
    have h8 : x * x = (x * x * (x * x))⁻¹ * (⁅x, y⁆ * (p * p)) := by
      calc x * x = z * z := hzz.symm
        _ = (x * y * (x * y))⁻¹ * (p * p) := h7
        _ = (⁅x, y⁆⁻¹ * (x * x * (x * x)))⁻¹ * (p * p) := by rw [hw2]
        _ = (x * x * (x * x))⁻¹ * (⁅x, y⁆ * (p * p)) := by group
    calc x * x * (x * x) * (x * x)
        = (x * x * (x * x)) * ((x * x * (x * x))⁻¹ * (⁅x, y⁆ * (p * p))) := by rw [← h8]
      _ = ⁅x, y⁆ * (p * p) := by group
  have hsq_center : sqsub (frattini X) ≤ Subgroup.center X := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.mul_mem _ (hcenP hu) (hcenP hu)
  have hzs_center : Subgroup.zpowers (x * x) ≤ Subgroup.center X := by
    rw [Subgroup.zpowers_le]
    exact hcenP hs
  have hTc : Subgroup.zpowers (x * x) ⊔ sqsub (frattini X) ≤ Subgroup.center X :=
    sup_le hzs_center hsq_center
  have : (Subgroup.zpowers (x * x) ⊔ sqsub (frattini X)).Normal :=
    Subgroup.normal_of_le_center hTc
  have hxT : x * x ∈ Subgroup.zpowers (x * x) ⊔ sqsub (frattini X) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hyT : y * y ∈ Subgroup.zpowers (x * x) ⊔ sqsub (frattini X) := by
    rw [hyy]
    exact hxT
  have heT : ⁅x, y⁆ ∈ Subgroup.zpowers (x * x) ⊔ sqsub (frattini X) := by
    have h1 : ⁅x, y⁆ = (x * x * (x * x) * (x * x)) * (p * p)⁻¹ := eq_mul_inv_of_mul_eq hmain.symm
    rw [h1]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.inv_mem _
      (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨p, hp, rfl⟩)))
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_zpowers _)
      (Subgroup.mem_zpowers _)) (Subgroup.mem_zpowers _)
  have hxy := closure_pair hg hx
  rw [hy] at hxy
  have hPT : frattini X ≤ Subgroup.zpowers (x * x) ⊔ sqsub (frattini X) :=
    frattini_le_of_gen hxy hxT hyT heT
  have hPcomm : ∀ a ∈ frattini X, ∀ b ∈ frattini X, a * b = b * a := fun a _ b hb => hcen b hb a
  have hzP : Subgroup.zpowers (x * x) ≤ frattini X := (Subgroup.zpowers_le).2 hs
  have hPz : ∀ π ∈ frattini X, π ∈ Subgroup.zpowers (x * x) := by
    have hP2' : IsPGroup 2 (frattini X) := hP2.to_subgroup _
    have hKtop : (Subgroup.zpowers (x * x)).subgroupOf (frattini X) ⊔ frattini (frattini X) =
        ⊤ := by
      rw [eq_top_iff]
      rintro ⟨π, hπ⟩ _
      obtain ⟨u, hu, v, hv, huv⟩ := (mem_sup_iff_of_commute
        (fun u hu v _ => (Subgroup.mem_center_iff.1 (hzs_center hu) v).symm)).1 (hPT hπ)
      obtain ⟨w, hw, hvw⟩ := (mem_sqsub_iff hPcomm).1 hv
      have huP : u ∈ frattini X := hzP hu
      have h1 : (⟨π, hπ⟩ : frattini X) = ⟨u, huP⟩ * (⟨w, hw⟩ * ⟨w, hw⟩) := by
        apply Subtype.ext
        change π = u * (w * w)
        rw [← hvw, huv]
      rw [h1]
      exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.2 hu)
        (mul_self_mem_frattini hP2' ⟨w, hw⟩)
    have hK := frattini_nongenerating hKtop
    intro π hπ
    have h2 : (⟨π, hπ⟩ : frattini X) ∈ (Subgroup.zpowers (x * x)).subgroupOf (frattini X) := by
      rw [hK]
      trivial
    exact Subgroup.mem_subgroupOf.1 h2
  have hPz' : frattini X ≤ Subgroup.zpowers (x * x) := fun π hπ => hPz π hπ
  obtain ⟨t, ht1, htfix⟩ := hfix
  have htP : t ∈ frattini X := fixed_mem_frattini hg htfix
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hPz p hp)
  have hezp : ⁅x, y⁆ = (x * x) ^ (3 - 2 * j) := zpow_aux hj hmain
  have hord : (x * x) ^ (2 * (3 - 2 * j)) = 1 := by
    rw [two_mul, zpow_add, ← hezp, he2]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hP2 (x * x)
  have hdvd : ((orderOf (x * x) : ℕ) : ℤ) ∣ 2 * (3 - 2 * j) := orderOf_dvd_iff_zpow_eq_one.2 hord
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have hk2' : 2 ≤ k := by omega
    have h4 : (4 : ℤ) ∣ ((orderOf (x * x) : ℕ) : ℤ) := by
      rw [hk]
      have h5 : (2 : ℕ) ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk2'
      exact_mod_cast h5
    have h6 := dvd_trans h4 hdvd
    omega
  have hord2 : orderOf (x * x) ≤ 2 := by
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 2 := by norm_num
  have hPe : frattini X = Subgroup.zpowers (x * x) := le_antisymm hPz' hzP
  have hPcard : Nat.card (frattini X) = 2 := by
    have h1 : Nat.card (frattini X) = orderOf (x * x) := by
      rw [hPe, Nat.card_zpowers]
    have h2 : Nat.card (frattini X) ≠ 1 := by
      intro h
      have h3 := Subgroup.card_eq_one.1 h
      apply ht1
      have h4 : t ∈ (⊥ : Subgroup X) := h3 ▸ htP
      exact Subgroup.mem_bot.1 h4
    have h3 : 0 < Nat.card (frattini X) := Nat.card_pos
    omega
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini X)
  rw [hPcard, hg.card_V] at hcard
  have hord_eq : orderOf (x * x) = 2 := by
    have h1 : Nat.card (frattini X) = orderOf (x * x) := by
      rw [hPe, Nat.card_zpowers]
    omega
  have hs1 : x * x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord_eq
    omega
  have hs2 : x * x * (x * x) = 1 := by
    have := pow_orderOf_eq_one (x * x)
    rw [hord_eq, pow_two] at this
    exact this
  have hxye : ⁅x, y⁆ = x * x := by
    rw [hezp, ← zpow_mod_orderOf, hord_eq]
    have : (3 - 2 * j) % ((2 : ℕ) : ℤ) = 1 := by omega
    rw [this, zpow_one]
  exact ⟨by omega, x, y, hxy, hs1, hs2, hyy, hxye⟩

end Q8

end CFSG.GH74.E2
