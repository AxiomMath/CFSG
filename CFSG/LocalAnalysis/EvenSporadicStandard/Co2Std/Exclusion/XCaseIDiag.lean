module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XFix
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XModule

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup
open scoped IsMulCommutative

variable {V : Type*} [Group V] {X : Type*} [Group X] {ρ : X →* MulAut V} {Q : Subgroup X}
  {V₁ V₂ : Subgroup V} {z : X} {Q₁ : Subgroup (MulAut ↥V₁)} {t₁ : ↥V₁}

theorem commute_of_map_conj_ne [Finite X] {K : Subgroup X} (hK : IsComponent K)
    (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) {k k' : X} (hk : k ∈ K)
    (hk' : k' ∈ K.map (MulAut.conj z).toMonoidHom) : k * k' = k' * k := by
  have hK' : IsComponent (K.map (MulAut.conj z).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj z) hK
  rcases CFSG.LocalCores.distinct_components_commute hK hK' with h | h
  · exact absurd h.symm hKz
  · have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact (Subgroup.mem_centralizer_iff.mp (hle hk) k' hk').symm

private noncomputable def psi [Finite X] {K : Subgroup X} (hK : IsComponent K)
    (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) : ↥K →* X where
  toFun k := (k : X) * MulAut.conj z (k : X)
  map_one' := by simp
  map_mul' a b := by
    have hcomm : (b : X) * MulAut.conj z (a : X) = MulAut.conj z (a : X) * (b : X) :=
      commute_of_map_conj_ne hK hKz b.2 (Subgroup.mem_map_of_mem _ a.2)
    change ((a : X) * (b : X)) * MulAut.conj z ((a : X) * (b : X)) =
      ((a : X) * MulAut.conj z (a : X)) * ((b : X) * MulAut.conj z (b : X))
    rw [map_mul]
    calc ((a : X) * (b : X)) * (MulAut.conj z (a : X) * MulAut.conj z (b : X))
        = (a : X) * ((b : X) * MulAut.conj z (a : X)) * MulAut.conj z (b : X) := by group
      _ = (a : X) * (MulAut.conj z (a : X) * (b : X)) * MulAut.conj z (b : X) := by rw [hcomm]
      _ = ((a : X) * MulAut.conj z (a : X)) * ((b : X) * MulAut.conj z (b : X)) := by group

private theorem psi_apply [Finite X] {K : Subgroup X} (hK : IsComponent K)
    (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) (k : ↥K) :
    psi (z := z) hK hKz k = (k : X) * (z * (k : X) * z⁻¹) := rfl

private theorem psi_range_le_centralizer [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    {K : Subgroup X} (hK : IsComponent K) (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) :
    (psi (z := z) hK hKz).range ≤ centralizer ({z} : Set X) := by
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.mul_self
  rintro d ⟨k, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  have hz : z * (psi (z := z) hK hKz k) * z⁻¹ = psi (z := z) hK hKz k := by
    rw [psi_apply]
    calc z * ((k : X) * (z * (k : X) * z⁻¹)) * z⁻¹
        = (z * (k : X) * z⁻¹) * (z * (z * (k : X) * z⁻¹) * z⁻¹) := by group
      _ = (z * (k : X) * z⁻¹) * (k : X) := by
            congr 1
            rw [hz_inv]
            calc z * (z * (k : X) * z) * z = (z * z) * (k : X) * (z * z) := by group
              _ = (k : X) := by rw [h.mul_self]; group
      _ = (k : X) * (z * (k : X) * z⁻¹) :=
            (commute_of_map_conj_ne hK hKz k.2 (Subgroup.mem_map_of_mem _ k.2)).symm
  calc z * (psi (z := z) hK hKz k) = z * (psi (z := z) hK hKz k) * (z * z) := by
        rw [h.mul_self, mul_one]
    _ = (z * (psi (z := z) hK hKz k) * z) * z := by group
    _ = (psi (z := z) hK hKz k) * z := by
          rw [show z * (psi (z := z) hK hKz k) * z = psi (z := z) hK hKz k by
            rwa [hz_inv] at hz]

private theorem psi_ne_one [Finite X] {K : Subgroup X} (hK : IsComponent K)
    (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) :
    psi (z := z) hK hKz ≠ 1 := by
  intro hpsi
  have hinv : ∀ a : ↥K, z * (a : X) * z⁻¹ = (a : X)⁻¹ := by
    intro a
    have h := congrArg (fun f : ↥K →* X => f a) hpsi
    simp only [MonoidHom.one_apply] at h
    rw [psi_apply] at h
    exact eq_inv_of_mul_eq_one_right h
  have habel : ∀ a b : ↥K, a * b = b * a := by
    intro a b
    have ha := hinv a
    have hb := hinv b
    have hab := hinv (a * b)
    rw [Subgroup.coe_mul] at hab
    have h1 : (a : X)⁻¹ * (b : X)⁻¹ = (b : X)⁻¹ * (a : X)⁻¹ := by
      calc (a : X)⁻¹ * (b : X)⁻¹
          = (z * (a : X) * z⁻¹) * (z * (b : X) * z⁻¹) := by rw [ha, hb]
        _ = z * ((a : X) * (b : X)) * z⁻¹ := by group
        _ = ((a : X) * (b : X))⁻¹ := hab
        _ = (b : X)⁻¹ * (a : X)⁻¹ := mul_inv_rev _ _
    have h2 : (b : X) * (a : X) = (a : X) * (b : X) := by
      have := congrArg Inv.inv h1
      simpa using this
    exact Subtype.ext h2.symm
  obtain ⟨a, b, hab⟩ := hK.1.2.2
  obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b₀, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, habel a₀ b₀])

private theorem layer_inf_centralizer_normalizes_psi_range [Finite X]
    (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {K : Subgroup X} (hK : IsComponent K)
    (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) :
    ∀ j ∈ layer X ⊓ centralizer ({z} : Set X), ∀ d ∈ (psi (z := z) hK hKz).range,
      j * d * j⁻¹ ∈ (psi (z := z) hK hKz).range := by
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.mul_self
  intro j hj d hd
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hd
  have hjk : j * (k : X) * j⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LocalCores.layer_le_normalizer hK hj.1) (k : X)).mp k.2
  refine MonoidHom.mem_range.mpr ⟨⟨j * (k : X) * j⁻¹, hjk⟩, ?_⟩
  have hjz : j * z = z * j := (Subgroup.mem_centralizer_iff.mp hj.2 z rfl).symm
  have h1 : z⁻¹ * j⁻¹ = j⁻¹ * z⁻¹ := by
    simpa using congrArg Inv.inv hjz
  have hjz_inv : j⁻¹ * z = z * j⁻¹ := by
    rw [← hz_inv]
    exact h1.symm
  have hjz_inv' : j⁻¹ * z⁻¹ = z⁻¹ * j⁻¹ := h1.symm
  rw [psi_apply, psi_apply]
  calc (j * (k : X) * j⁻¹) * (z * (j * (k : X) * j⁻¹) * z⁻¹)
      = j * (k : X) * (j⁻¹ * z * j) * (k : X) * (j⁻¹ * z⁻¹) := by group
    _ = j * (k : X) * (z * (j⁻¹ * j)) * (k : X) * (j⁻¹ * z⁻¹) := by rw [hjz_inv]; group
    _ = j * (k : X) * z * (k : X) * (j⁻¹ * z⁻¹) := by group
    _ = j * (k : X) * z * (k : X) * (z⁻¹ * j⁻¹) := by rw [hjz_inv']
    _ = j * ((k : X) * (z * (k : X) * z⁻¹)) * j⁻¹ := by group

private theorem psi_range_eq_commutator [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    {K : Subgroup X} (hK : IsComponent K) (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) :
    (psi (z := z) hK hKz).range = ⁅Q, Q⁆ := by
  haveI : Group.IsPerfect ↥K := hK.1.1
  have hDperf : ⁅(psi (z := z) hK hKz).range, (psi (z := z) hK hKz).range⁆ =
      (psi (z := z) hK hKz).range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (psi (z := z) hK hKz))
  have hDne : (psi (z := z) hK hKz).range ≠ ⊥ := by
    intro hbot
    exact psi_ne_one hK hKz (MonoidHom.range_eq_bot_iff.mp hbot)
  have hDle : (psi (z := z) hK hKz).range ≤ centralizer ({z} : Set X) :=
    psi_range_le_centralizer h hK hKz
  set J : Subgroup X := layer X ⊓ centralizer ({z} : Set X)
  have hJle : J ≤ centralizer ({z} : Set X) := inf_le_right
  have hJnorm : ∀ c ∈ centralizer ({z} : Set X), ∀ y ∈ J, c * y * c⁻¹ ∈ J := by
    intro c hc y hy
    haveI : (layer X).Characteristic := CFSG.LocalCores.layer_characteristic (G := X)
    refine ⟨?_, ?_⟩
    · exact (inferInstance : (layer X).Normal).conj_mem y hy.1 c
    · have hzc : Commute z c := Subgroup.mem_centralizer_iff.mp hc z rfl
      have hzy : Commute z y := Subgroup.mem_centralizer_iff.mp hy.2 z rfl
      change c * y * c⁻¹ ∈ centralizer ({z} : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ((hzc.mul_right hzy).mul_right hzc.inv_right).eq
  have hDleJ : (psi (z := z) hK hKz).range ≤ J := by
    intro d hd
    refine ⟨?_, hDle hd⟩
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hd
    rw [psi_apply]
    have hK' : IsComponent (K.map (MulAut.conj z).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj z) hK
    exact mul_mem (CFSG.LocalCores.component_le_layer hK k.2)
      (CFSG.LocalCores.component_le_layer hK' (by
        simpa using Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom k.2))
  rcases h.le_zpowers_or_le hJle hJnorm with hJz | hQ'J
  · exfalso
    have hDz : (psi (z := z) hK hKz).range ≤ zpowers z := hDleJ.trans hJz
    have hcomm : ⁅(psi (z := z) hK hKz).range, (psi (z := z) hK hKz).range⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hDz hd)
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hDz he)
      rw [← hm, ← hn]
      exact (zpow_mul_comm z m n).symm
    exact hDne (by rw [← hDperf]; exact hcomm)
  · have hDleQ' : (psi (z := z) hK hKz).range ≤ ⁅Q, Q⁆ :=
      h.le_commutator_of_perfect hDle hDperf
    have hDnormal : ((psi (z := z) hK hKz).range.subgroupOf ⁅Q, Q⁆).Normal := by
      refine ⟨fun d hd q => ?_⟩
      exact layer_inf_centralizer_normalizes_psi_range h hK hKz (q : X) (hQ'J q.2) (d : X) hd
    haveI : IsSimpleGroup ↥⁅Q, Q⁆ := h.isSimpleGroup_commutator
    haveI : ((psi (z := z) hK hKz).range.subgroupOf ⁅Q, Q⁆).Normal := hDnormal
    rcases Subgroup.Normal.eq_bot_or_eq_top ((psi (z := z) hK hKz).range.subgroupOf ⁅Q, Q⁆)
      with hbot | htop
    · exfalso
      have hdisj : Disjoint (psi (z := z) hK hKz).range ⁅Q, Q⁆ :=
        Subgroup.subgroupOf_eq_bot.mp hbot
      have hle : (psi (z := z) hK hKz).range ≤ ⊥ := by
        intro d hd
        have hmem : d ∈ (psi (z := z) hK hKz).range ⊓ ⁅Q, Q⁆ := ⟨hd, hDleQ' hd⟩
        rwa [disjoint_iff.mp hdisj] at hmem
      exact hDne (le_bot_iff.mp hle)
    · rw [Subgroup.subgroupOf_eq_top] at htop
      exact le_antisymm hDleQ' htop

theorem XHyp.mul_conj_mem_commutator [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {K : Subgroup X}
    (hK : IsComponent K) (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) {k : X} (hk : k ∈ K) :
    k * (z * k * z⁻¹) ∈ ⁅Q, Q⁆ := by
  have hle : (psi (z := z) hK hKz).range ≤ ⁅Q, Q⁆ := by
    rw [psi_range_eq_commutator h hK hKz]
  have hmem : psi (z := z) hK hKz ⟨k, hk⟩ ∈ (psi (z := z) hK hKz).range :=
    MonoidHom.mem_range.mpr ⟨⟨k, hk⟩, rfl⟩
  have := hle hmem
  rwa [psi_apply] at this

theorem XHyp.exists_mul_conj_eq [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {K : Subgroup X}
    (hK : IsComponent K) (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) {g : X}
    (hg : g ∈ ⁅Q, Q⁆) : ∃ k ∈ K, k * (z * k * z⁻¹) = g := by
  have hg' : g ∈ (psi (z := z) hK hKz).range := by
    rwa [psi_range_eq_commutator h hK hKz]
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hg'
  exact ⟨k, k.2, by rw [← hk, psi_apply]⟩

private def fixedBy (ρ : X →* MulAut V) (K : Subgroup X) : Subgroup V where
  carrier := {v | ∀ k ∈ K, ρ k v = v}
  one_mem' := by intro k _; simp
  mul_mem' := by
    intro a b ha hb k hk
    rw [map_mul, ha k hk, hb k hk]
  inv_mem' := by
    intro a ha k hk
    rw [map_inv, ha k hk]

private theorem mem_fixedBy {K : Subgroup X} {v : V} :
    v ∈ fixedBy ρ K ↔ ∀ k ∈ K, ρ k v = v := Iff.rfl

private theorem rho_z_apply_apply [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) (v : V) :
    ρ z (ρ z v) = v := by
  have hzz : ρ z * ρ z = 1 := by rw [← map_mul, h.mul_self, map_one]
  calc ρ z (ρ z v) = (ρ z * ρ z) v := by rw [MulAut.mul_apply]
    _ = v := by rw [hzz]; rfl

private theorem center_commutator_eq_bot [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    center ↥⁅Q, Q⁆ = ⊥ := by
  haveI : IsSimpleGroup ↥⁅Q, Q⁆ := h.isSimpleGroup_commutator
  rcases Subgroup.Normal.eq_bot_or_eq_top (center ↥⁅Q, Q⁆) with hc | hc
  · exact hc
  · exfalso
    haveI : IsMulCommutative ↥⁅Q, Q⁆ := Subgroup.center_eq_top_iff.mp hc
    have hp : (Nat.card ↥⁅Q, Q⁆).Prime :=
      (Group.is_simple_iff_prime_card).mp h.isSimpleGroup_commutator
    rw [h.card_commutator] at hp
    have h2 : 2 ∣ 443520 := by norm_num
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> norm_num at h

private theorem exists_orderOf_eq_eleven [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    {K : Subgroup X} (hK : IsComponent K) (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) :
    ∃ a : X, orderOf a = 11 ∧ ∀ k ∈ K, a * k = k * a := by
  have hψ : (psi (z := z) hK hKz).range = ⁅Q, Q⁆ := psi_range_eq_commutator h hK hKz
  have hdvd : Nat.card ↥⁅Q, Q⁆ ∣ Nat.card ↥K := by
    rw [← hψ]
    exact Subgroup.card_range_dvd (psi (z := z) hK hKz)
  have h11 : 11 ∣ Nat.card ↥K := by
    have h11' : 11 ∣ Nat.card ↥⁅Q, Q⁆ := by rw [h.card_commutator]; norm_num
    exact h11'.trans hdvd
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 11 h11
  refine ⟨MulAut.conj z (c : X), ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
    exact hc
  · intro k hk
    exact (commute_of_map_conj_ne hK hKz hk
      (Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom c.2)).symm

private theorem exists_noncentral_seven [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    {K : Subgroup X} (hK : IsComponent K) (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) :
    ∃ b ∈ K, (∃ n : ℕ, b ^ 7 ^ n = 1) ∧ ∃ k ∈ K, b * k ≠ k * b := by
  have hψ : (psi (z := z) hK hKz).range = ⁅Q, Q⁆ := psi_range_eq_commutator h hK hKz
  have h7 : 7 ∣ Nat.card ↥⁅Q, Q⁆ := by rw [h.card_commutator]; norm_num
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 7 h7
  have hdmem : (d : X) ∈ (psi (z := z) hK hKz).range := by
    rw [hψ]; exact d.2
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hdmem
  have hk7 : 7 ∣ orderOf k := by
    have h := orderOf_map_dvd (psi (z := z) hK hKz) k
    rw [hk, Subgroup.orderOf_coe, hd] at h
    exact h
  have hk0 : orderOf k ≠ 0 := (orderOf_pos k).ne' 
  obtain ⟨r, m, hm, hr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 7 (by norm_num)
  have hr1 : 1 ≤ r := by
    by_contra h
    have hr0 : r = 0 := by omega
    rw [hr0, pow_zero, one_mul] at hr
    rw [hr] at hk7
    exact hm hk7
  have hdm : d ^ m ≠ 1 := by
    intro hdm
    have hdvd : orderOf d ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hdm
    rw [hd] at hdvd
    exact hm hdvd
  have hdXm : (d : X) ^ m ≠ 1 := by
    intro h1
    exact hdm (Subtype.ext (by simpa using h1))
  refine ⟨((k ^ m : ↥K) : X), (k ^ m).2, ?_, ?_⟩
  · refine ⟨r, ?_⟩
    rw [Subgroup.coe_pow, ← pow_mul]
    have hord : m * 7 ^ r = orderOf (k : ↥K) := by
      rw [hr]; ring
    rw [hord, ← Subgroup.coe_pow, pow_orderOf_eq_one]
    rfl
  · by_contra hcon
    push Not at hcon
    have hmemQ' : psi (z := z) hK hKz (k ^ m) ∈ ⁅Q, Q⁆ := by
      have hmem : psi (z := z) hK hKz (k ^ m) ∈ (psi (z := z) hK hKz).range :=
        MonoidHom.mem_range.mpr ⟨k ^ m, rfl⟩
      rwa [hψ] at hmem
    have hcenter : (⟨psi (z := z) hK hKz (k ^ m), hmemQ'⟩ : ↥⁅Q, Q⁆) ∈ center ↥⁅Q, Q⁆ := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨k', hk'⟩ := MonoidHom.mem_range.mp (by rw [hψ]; exact x.2)
      apply Subtype.ext
      show (x : X) * (psi (z := z) hK hKz (k ^ m) : X) =
        (psi (z := z) hK hKz (k ^ m) : X) * (x : X)
      rw [← hk', ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (k' : X) * ((k ^ m : ↥K) : X) = ((k ^ m : ↥K) : X) * (k' : X)
      exact (hcon (k' : X) k'.2).symm
    have hbot : psi (z := z) hK hKz (k ^ m) = 1 := by
      have hmem : (⟨psi (z := z) hK hKz (k ^ m), hmemQ'⟩ : ↥⁅Q, Q⁆) ∈
          (⊥ : Subgroup ↥⁅Q, Q⁆) := by
        rw [← center_commutator_eq_bot h]
        exact hcenter
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
    have hpsib : (psi (z := z) hK hKz (k ^ m) : X) = (d : X) ^ m := by
      rw [map_pow, hk]
    exact hdXm (by rw [← hpsib, hbot])

private theorem fixedBy_ne_top [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {K : Subgroup X}
    (hK : IsComponent K) (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) :
    fixedBy ρ K ≠ ⊤ := by
  intro htop
  have hKbot : K = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    have hfix : ρ k = 1 := by
      ext v
      exact (show v ∈ fixedBy ρ K from htop ▸ Subgroup.mem_top v) k hk
    exact h.injective (by rw [hfix, map_one])
  haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  haveI : Subsingleton ↥K := ⟨fun a b => by
    apply Subtype.ext
    have ha : (a : X) = 1 := Subgroup.mem_bot.mp (hKbot ▸ a.2)
    have hb : (b : X) = 1 := Subgroup.mem_bot.mp (hKbot ▸ b.2)
    rw [ha, hb]⟩
  exact not_subsingleton ↥K inferInstance

private theorem fixedBy_ne_centralizer [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    {K : Subgroup X} (hK : IsComponent K) (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) :
    ¬ (∀ v : V, v ∈ fixedBy ρ K ↔ ρ z v = v) := by
  intro hU
  haveI : IsMulCommutative V := h.elemAb.toIsMulCommutative
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.mul_self
  have hzz_aut : ρ z * ρ z = 1 := by
    rw [← map_mul, h.mul_self, map_one]
  have hzz_apply : ∀ v : V, ρ z (ρ z v) = v := by
    intro v
    calc ρ z (ρ z v) = (ρ z * ρ z) v := by rw [MulAut.mul_apply]
      _ = v := by rw [hzz_aut]; rfl
  have hsq : ∀ x : V, x * x = 1 := by
    intro x
    have := (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.elemAb.exponent_dvd_p) x
    simpa [pow_two] using this
  have hψ : (psi (z := z) hK hKz).range = ⁅Q, Q⁆ := psi_range_eq_commutator h hK hKz
  have hDle : (psi (z := z) hK hKz).range ≤ centralizer ({z} : Set X) :=
    psi_range_le_centralizer h hK hKz
  have hcommV : ∀ x y : V, x * y = y * x :=
    fun x y => h.elemAb.toIsMulCommutative.is_comm.comm x y
  have hfix : ∀ g ∈ ⁅Q, Q⁆, ∀ u : V, ρ z u = u → ρ g u = u := by
    intro g hg u hu
    have hg' : g ∈ (psi (z := z) hK hKz).range := by rwa [hψ]
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hg'
    rw [psi_apply, map_mul, MulAut.mul_apply]
    have hku : ρ (k : X) u = u := (hU u).mpr hu k k.2
    have hconj : ρ (z * (k : X) * z⁻¹) u = u := by
      rw [map_mul, MulAut.mul_apply, map_mul, MulAut.mul_apply]
      rw [show ρ z⁻¹ u = u by rw [hz_inv]; exact hu, hku]
      exact hu
    rw [hconj, hku]
  have hgz : ∀ g ∈ ⁅Q, Q⁆, ∀ v : V, ρ g (ρ z v) = ρ z (ρ g v) := by
    intro g hg v
    have hc : g * z = z * g :=
      (Subgroup.mem_centralizer_iff.mp (hDle (by rwa [hψ])) z rfl).symm
    calc ρ g (ρ z v) = ρ (g * z) v := by rw [map_mul, MulAut.mul_apply]
      _ = ρ (z * g) v := by rw [hc]
      _ = ρ z (ρ g v) := by rw [map_mul, MulAut.mul_apply]
  have hpow2 : ∀ g ∈ ⁅Q, Q⁆, ρ g * ρ g = 1 := by
    intro g hg
    ext v
    have hfixg := hfix g hg
    have hgzg := hgz g hg
    have hv : ρ z (v * ρ z v) = v * ρ z v := by
      rw [map_mul, hzz_apply, hcommV (ρ z v) v]
    set a : V := ρ g v with ha
    have h1 : a * ρ z a = v * ρ z v := by
      calc a * ρ z a = ρ g v * ρ g (ρ z v) := by rw [ha, hgzg v]
        _ = ρ g (v * ρ z v) := by rw [map_mul]
        _ = v * ρ z v := hfixg _ hv
    have h2 : a * v = ρ z a * ρ z v := by
      have h3 : (a * v) * (a * v) = 1 := hsq _
      have h4 : (a * v) * (ρ z a * ρ z v) = 1 := by
        calc (a * v) * (ρ z a * ρ z v) = a * (v * ρ z a) * ρ z v := by group
          _ = a * (ρ z a * v) * ρ z v := by rw [hcommV v (ρ z a)]
          _ = (a * ρ z a) * (v * ρ z v) := by group
          _ = (v * ρ z v) * (v * ρ z v) := by rw [h1]
          _ = 1 := hsq _
      exact mul_left_cancel (by rw [h3, h4])
    have h5 : ρ g (a * v) = a * v := hfixg _ (by rw [map_mul, h2])
    have h6 : ρ g a * a = a * v := by
      have h6' : ρ g a * a = ρ g (a * v) := by rw [map_mul, ← ha]
      rw [h6', h5]
    have h7 : ρ g a = v := by
      calc ρ g a = ρ g a * (a * a) := by rw [hsq a, mul_one]
        _ = (ρ g a * a) * a := by group
        _ = (a * v) * a := by rw [h6]
        _ = v := by rw [mul_assoc, hcommV v a, ← mul_assoc, hsq a, one_mul]
    show ρ g (ρ g v) = v
    rw [← ha]
    exact h7
  have habel : ∀ x y : ↥⁅Q, Q⁆, x * y = y * x := by
    intro x y
    apply Subtype.ext
    apply h.injective
    show ρ ((x : X) * (y : X)) = ρ ((y : X) * (x : X))
    rw [map_mul, map_mul]
    have hx := hpow2 x x.2
    have hy := hpow2 y y.2
    have hxy : (ρ (x : X) * ρ (y : X)) * (ρ (x : X) * ρ (y : X)) = 1 := by
      simpa [map_mul] using hpow2 (x * y) (x * y).2
    have h1 : ρ (x : X) * ρ (y : X) = (ρ (x : X) * ρ (y : X))⁻¹ :=
      eq_inv_of_mul_eq_one_right hxy
    have hx' : (ρ (x : X))⁻¹ = ρ (x : X) := inv_eq_of_mul_eq_one_right hx
    have hy' : (ρ (y : X))⁻¹ = ρ (y : X) := inv_eq_of_mul_eq_one_right hy
    calc ρ (x : X) * ρ (y : X) = (ρ (x : X) * ρ (y : X))⁻¹ := h1
      _ = (ρ (y : X))⁻¹ * (ρ (x : X))⁻¹ := mul_inv_rev _ _
      _ = ρ (y : X) * ρ (x : X) := by rw [hx', hy']
  haveI : IsMulCommutative ↥⁅Q, Q⁆ := ⟨⟨habel⟩⟩
  have hp : (Nat.card ↥⁅Q, Q⁆).Prime :=
    (Group.is_simple_iff_prime_card).mp h.isSimpleGroup_commutator
  rw [h.card_commutator] at hp
  have h2 : 2 ∣ 443520 := by norm_num
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> norm_num at h

private theorem fixedBy_ne_bot [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {K : Subgroup X}
    (hK : IsComponent K) (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) :
    fixedBy ρ K ≠ ⊥ := by
  intro hbot
  obtain ⟨a, ha11, ha⟩ := exists_orderOf_eq_eleven h hK hKz
  obtain ⟨b, hbK, hb7, hbK'⟩ := exists_noncentral_seven h hK hKz
  obtain ⟨v, hv1, hvf⟩ := exists_ne_one_forall_fixed h.elemAb (XHyp.card_V h) h.injective
    hK.1 ha ha11 hbK hb7 hbK'
  have hv : v ∈ fixedBy ρ K := hvf
  rw [hbot] at hv
  exact hv1 (Subgroup.mem_bot.mp hv)

theorem XHyp.fixed_eq [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {K : Subgroup X}
    (hK : IsComponent K) (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) :
    (∀ v : V, (∀ k ∈ K, ρ k v = v) ↔ v ∈ V₁) ∨ ∀ v : V, (∀ k ∈ K, ρ k v = v) ↔ v ∈ V₂ := by
  have hUne : fixedBy ρ K ≠ ⊤ := fixedBy_ne_top h hK hKz
  have hUc : ¬ (∀ v : V, v ∈ fixedBy ρ K ↔ ρ z v = v) := fixedBy_ne_centralizer h hK hKz
  have hUb : fixedBy ρ K ≠ ⊥ := fixedBy_ne_bot h hK hKz
  have hQ'layer : ⁅Q, Q⁆ ≤ layer X := by
    rw [← psi_range_eq_commutator h hK hKz]
    intro d hd
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hd
    rw [psi_apply]
    have hK' : IsComponent (K.map (MulAut.conj z).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj z) hK
    exact mul_mem (CFSG.LocalCores.component_le_layer hK k.2)
      (CFSG.LocalCores.component_le_layer hK' (by
        simpa using Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom k.2))
  have hUinv : ∀ g ∈ ⁅Q, Q⁆, ∀ u ∈ fixedBy ρ K, ρ g u ∈ fixedBy ρ K := by
    intro g hg u hu
    have hg' : g ∈ (psi (z := z) hK hKz).range := by
      rwa [psi_range_eq_commutator h hK hKz]
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hg'
    have hnorm := CFSG.LocalCores.layer_le_normalizer hK (hQ'layer hg)
    rw [mem_fixedBy] at hu ⊢
    intro k' hk'
    have hconj : (psi (z := z) hK hKz k)⁻¹ * k' * psi (z := z) hK hKz k ∈ K :=
      (Subgroup.mem_normalizer_iff''.mp hnorm (k' : X)).mp hk'
    calc ρ k' (ρ (psi (z := z) hK hKz k) u)
        = ρ (k' * psi (z := z) hK hKz k) u := by rw [map_mul, MulAut.mul_apply]
      _ = ρ (psi (z := z) hK hKz k *
            ((psi (z := z) hK hKz k)⁻¹ * k' * psi (z := z) hK hKz k)) u := by
            rw [show k' * psi (z := z) hK hKz k = psi (z := z) hK hKz k *
              ((psi (z := z) hK hKz k)⁻¹ * k' * psi (z := z) hK hKz k) by group]
      _ = ρ (psi (z := z) hK hKz k)
            (ρ ((psi (z := z) hK hKz k)⁻¹ * k' * psi (z := z) hK hKz k) u) := by
            rw [map_mul, MulAut.mul_apply]
      _ = ρ (psi (z := z) hK hKz k) u := by rw [hu _ hconj]
  rcases h.invariant_cases hUinv with hbot | hV1 | hV2 | hC | htop
  · exact absurd hbot hUb
  · left
    intro v
    rw [← mem_fixedBy]
    exact SetLike.ext_iff.mp hV1 v
  · right
    intro v
    rw [← mem_fixedBy]
    exact SetLike.ext_iff.mp hV2 v
  · exact absurd hC hUc
  · exact absurd htop hUne

theorem XHyp.eq_or_eq_of_isComponent [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {K : Subgroup X}
    (hK : IsComponent K) (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) {L : Subgroup X}
    (hL : IsComponent L) : L = K ∨ L = K.map (MulAut.conj z).toMonoidHom := by
  haveI : IsMulCommutative V := h.elemAb.toIsMulCommutative
  by_cases hLK : L = K
  · exact Or.inl hLK
  by_cases hLK' : L = K.map (MulAut.conj z).toMonoidHom
  · exact Or.inr hLK'
  exfalso
  have hK' : IsComponent (K.map (MulAut.conj z).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj z) hK
  have hLKcomm : ⁅L, K⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hL hK with h1 | h1
    · exact absurd h1 hLK
    · exact h1
  have hLK'comm : ⁅L, K.map (MulAut.conj z).toMonoidHom⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hL hK' with h1 | h1
    · exact absurd h1 hLK'
    · exact h1
  have hLQ' : ∀ l ∈ L, ∀ g ∈ ⁅Q, Q⁆, l * g = g * l := by
    intro l hl g hg
    have hg' : g ∈ (psi (z := z) hK hKz).range := by
      rwa [psi_range_eq_commutator h hK hKz]
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hg'
    rw [psi_apply]
    have h1 : l * (k : X) = (k : X) * l :=
      (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLKcomm hl) (k : X) k.2).symm
    have h2 : l * (z * (k : X) * z⁻¹) = (z * (k : X) * z⁻¹) * l := by
      have hmem : z * (k : X) * z⁻¹ ∈ K.map (MulAut.conj z).toMonoidHom := by
        simpa using Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom k.2
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLK'comm hl) _ hmem).symm
    calc l * ((k : X) * (z * (k : X) * z⁻¹))
        = (l * (k : X)) * (z * (k : X) * z⁻¹) := by group
      _ = ((k : X) * l) * (z * (k : X) * z⁻¹) := by rw [h1]
      _ = (k : X) * (l * (z * (k : X) * z⁻¹)) := by group
      _ = (k : X) * ((z * (k : X) * z⁻¹) * l) := by rw [h2]
      _ = ((k : X) * (z * (k : X) * z⁻¹)) * l := by group
  set UK : Subgroup V := fixedBy ρ K
  set UK' : Subgroup V := fixedBy ρ (K.map (MulAut.conj z).toMonoidHom)
  have hUK' : ∀ v : V, v ∈ UK' ↔ ρ z v ∈ UK := by
    intro v
    have hzz : ρ z * ρ z = 1 := by rw [← map_mul, h.mul_self, map_one]
    constructor
    · intro hv k hk
      have hmem : MulAut.conj z (k : X) ∈ K.map (MulAut.conj z).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hk
      have hfix := hv _ hmem
      have hconj : ρ (MulAut.conj z (k : X)) = ρ z * ρ (k : X) * ρ z := by
        rw [MulAut.conj_apply, map_mul, map_mul]
        rw [show z⁻¹ = z from inv_eq_of_mul_eq_one_right h.mul_self]
      have h2 := congrArg (fun w => ρ z w) hfix
      rw [hconj] at h2
      have h3 : ρ z ((ρ z * ρ (k : X) * ρ z) v) = ρ (k : X) (ρ z v) := by
        rw [MulAut.mul_apply, MulAut.mul_apply, ← MulAut.mul_apply, hzz, MulAut.one_apply]
      rwa [h3] at h2
    · intro hv k' hk'
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hk'
      have hkfix : ρ k (ρ z v) = ρ z v := hv k hk
      show ρ (z * (k : X) * z⁻¹) v = v
      rw [show z⁻¹ = z from inv_eq_of_mul_eq_one_right h.mul_self]
      rw [map_mul, MulAut.mul_apply, map_mul, MulAut.mul_apply, hkfix]
      rw [← MulAut.mul_apply, hzz, MulAut.one_apply]
  have hmapUK : UK' = UK.map (ρ z).toMonoidHom := by
    ext v
    rw [Subgroup.mem_map]
    constructor
    · intro hv
      exact ⟨ρ z v, (hUK' v).mp hv, rho_z_apply_apply h v⟩
    · rintro ⟨w, hw, rfl⟩
      exact (hUK' (ρ z w)).mpr (by rwa [rho_z_apply_apply h w])
  have hmapV1 : V₁.map (ρ z).toMonoidHom = V₂ := by
    apply le_antisymm
    · rintro v ⟨w, hw, rfl⟩
      exact (h.swap w).mp hw
    · intro v hv
      exact ⟨ρ z v, (h.swap (ρ z v)).mpr (by rwa [rho_z_apply_apply h v]),
        rho_z_apply_apply h v⟩
  have hmapV2 : V₂.map (ρ z).toMonoidHom = V₁ := by
    apply le_antisymm
    · rintro v ⟨w, hw, rfl⟩
      exact (h.swap (ρ z w)).mpr (by rwa [rho_z_apply_apply h w])
    · intro v hv
      exact ⟨ρ z v, (h.swap v).mp hv, rho_z_apply_apply h v⟩
  have hUKV : UK = V₁ ∨ UK = V₂ := by
    rcases h.fixed_eq hK hKz with h1 | h1
    · left; ext v; simpa [UK, mem_fixedBy] using h1 v
    · right; ext v; simpa [UK, mem_fixedBy] using h1 v
  have htriv : ∀ c ∈ L, c = 1 := by
    intro c hcL
    have hpresUK : ∀ u ∈ UK, ρ c u ∈ UK := by
      intro u hu
      have hu' : ∀ k ∈ K, ρ k u = u := hu
      intro k hk
      have hck : c * k = k * c :=
        (Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLKcomm hcL) k hk).symm
      calc ρ k (ρ c u) = ρ (k * c) u := by rw [map_mul, MulAut.mul_apply]
        _ = ρ (c * k) u := by rw [hck]
        _ = ρ c (ρ k u) := by rw [map_mul, MulAut.mul_apply]
        _ = ρ c u := by rw [hu' k hk]
    have hpresUK' : ∀ u ∈ UK', ρ c u ∈ UK' := by
      intro u hu
      have hu' : ∀ k ∈ K.map (MulAut.conj z).toMonoidHom, ρ k u = u := hu
      intro k' hk'
      have hck' : c * k' = k' * c :=
        (Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLK'comm hcL) k' hk').symm
      calc ρ k' (ρ c u) = ρ (k' * c) u := by rw [map_mul, MulAut.mul_apply]
        _ = ρ (c * k') u := by rw [hck']
        _ = ρ c (ρ k' u) := by rw [map_mul, MulAut.mul_apply]
        _ = ρ c u := by rw [hu' k' hk']
    have hpresV1 : ∀ v ∈ V₁, ρ c v ∈ V₁ := by
      intro v hv
      rcases hUKV with h1 | h1
      · have hv' : v ∈ UK := by rw [h1]; exact hv
        have := hpresUK v hv'
        rwa [h1] at this
      · have h2 : UK' = V₁ := by rw [hmapUK, h1, hmapV2]
        have hv' : v ∈ UK' := by rw [h2]; exact hv
        have := hpresUK' v hv'
        rwa [h2] at this
    have hpresV2 : ∀ v ∈ V₂, ρ c v ∈ V₂ := by
      intro v hv
      rcases hUKV with h1 | h1
      · have h2 : UK' = V₂ := by rw [hmapUK, h1, hmapV1]
        have hv' : v ∈ UK' := by rw [h2]; exact hv
        have := hpresUK' v hv'
        rwa [h2] at this
      · have hv' : v ∈ UK := by rw [h1]; exact hv
        have := hpresUK v hv'
        rwa [h1] at this
    have hcQ'1 : ∀ g ∈ ⁅Q, Q⁆, ∀ v ∈ V₁, ρ c (ρ g v) = ρ g (ρ c v) := by
      intro g hg v _
      have hcg : c * g = g * c := hLQ' c hcL g hg
      calc ρ c (ρ g v) = ρ (c * g) v := by rw [map_mul, MulAut.mul_apply]
        _ = ρ (g * c) v := by rw [hcg]
        _ = ρ g (ρ c v) := by rw [map_mul, MulAut.mul_apply]
    have hcQ'2 : ∀ g ∈ ⁅Q, Q⁆, ∀ v ∈ V₂, ρ c (ρ g v) = ρ g (ρ c v) := by
      intro g hg v _
      have hcg : c * g = g * c := hLQ' c hcL g hg
      calc ρ c (ρ g v) = ρ (c * g) v := by rw [map_mul, MulAut.mul_apply]
        _ = ρ (g * c) v := by rw [hcg]
        _ = ρ g (ρ c v) := by rw [map_mul, MulAut.mul_apply]
    have heq1 := h.apply_eq_self₁ hpresV1 hcQ'1
    have heq2 := h.apply_eq_self₂ hpresV2 hcQ'2
    have hc1 : ρ c = 1 := by
      ext v
      have hv : v ∈ V₁ ⊔ V₂ := by rw [h.sup_eq_top]; exact Subgroup.mem_top v
      obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hv
      rw [map_mul, heq1 v1 hv1, heq2 v2 hv2]
      rfl
    exact h.injective (by rw [hc1, map_one])
  have hLbot : L = ⊥ := by
    rw [eq_bot_iff]
    exact htriv
  haveI : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  haveI : Subsingleton ↥L := ⟨fun a b => by
    apply Subtype.ext
    rw [htriv a a.2, htriv b b.2]⟩
  exact not_subsingleton ↥L inferInstance

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
