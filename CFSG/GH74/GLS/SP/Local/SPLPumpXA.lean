module

public import CFSG.GH74.GLS.SP.Local.SPLPumpX
public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk102L
public import CFSG.GH74.KGroups.TwoA7Fixed

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS
open scoped commutatorElement

theorem mem_normalizer_of_conj {G : Type} [Group G] {I : Subgroup G} {c : G}
    (h1 : ∀ i ∈ I, c * i * c⁻¹ ∈ I) (h2 : ∀ i ∈ I, c⁻¹ * i * c ∈ I) :
    c ∈ normalizer (I : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨h1 h, fun hh => ?_⟩
  have := h2 _ hh
  simpa [mul_assoc] using this

theorem mem_normalizer_of_comm {G : Type} [Group G] {I : Subgroup G} {c : G}
    (hc : ∀ i ∈ I, c * i = i * c) : c ∈ normalizer (I : Set G) := by
  refine mem_normalizer_of_conj (fun i hi => ?_) (fun i hi => ?_)
  · have : c * i * c⁻¹ = i := by rw [hc i hi]; group
    rw [this]; exact hi
  · have : c⁻¹ * i * c = i := by
      have h := hc i hi
      calc c⁻¹ * i * c = c⁻¹ * (i * c) := by group
        _ = c⁻¹ * (c * i) := by rw [h]
        _ = i := by group
    rw [this]; exact hi

theorem two_mem_sup_of_odd {G : Type} [Group G] [Finite G] {N F : Subgroup G}
    (hF : Odd (Nat.card ↥F)) (hnorm : F ≤ normalizer (N : Set G)) :
    ∀ y ∈ N ⊔ F, (∃ k : ℕ, y ^ (2 ^ k) = 1) → y ∈ N := by
  intro y hy ⟨k, hk⟩
  set W := N ⊔ F with hW
  have hNW : N ≤ W := le_sup_left
  have hF₀W : F ≤ W := le_sup_right
  have hWn : W ≤ normalizer (N : Set G) := sup_le le_normalizer hnorm
  have hnormal : (N.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff hNW).mpr fun h k hh hk =>
      (Subgroup.mem_normalizer_iff.mp (hWn hk) h).mp hh
  have hsup : (N ⊔ F).subgroupOf W = N.subgroupOf W ⊔ F.subgroupOf W :=
    Subgroup.subgroupOf_sup hNW hF₀W
  have hy' : (⟨y, hy⟩ : ↥W) ∈ N.subgroupOf W ⊔ F.subgroupOf W := by
    rw [← hsup, Subgroup.mem_subgroupOf]
    exact hy
  obtain ⟨n', hn', f', hf', hnf⟩ := Subgroup.mem_sup_of_normal_left.mp hy'
  let φ : ↥W →* ↥W ⧸ N.subgroupOf W := QuotientGroup.mk' (N.subgroupOf W)
  have hφn : φ n' = 1 := (QuotientGroup.eq_one_iff n').mpr hn'
  have hφy : φ ⟨y, hy⟩ = φ f' := by
    rw [← hnf, map_mul, hφn, one_mul]
  have hord2 : orderOf (φ f') ∣ 2 ^ k := by
    rw [← hφy]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow]
    have : (⟨y, hy⟩ : ↥W) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hf'F : (f' : G) ∈ F := Subgroup.mem_subgroupOf.mp hf'
  have hordF : orderOf (φ f') ∣ Nat.card ↥F := by
    refine (orderOf_map_dvd φ f').trans ?_
    have h1 : orderOf f' = orderOf (f' : G) := (Subgroup.orderOf_coe f').symm
    rw [h1]
    exact Subgroup.orderOf_dvd_natCard F hf'F
  have hcop : Nat.Coprime (Nat.card ↥F) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hF)
  have h1 : orderOf (φ f') = 1 := Nat.eq_one_of_dvd_coprimes hcop hordF hord2
  rw [orderOf_eq_one_iff] at h1
  have hyN : (⟨y, hy⟩ : ↥W) ∈ N.subgroupOf W := (QuotientGroup.eq_one_iff _).mp (hφy.trans h1)
  exact Subgroup.mem_subgroupOf.mp hyN

theorem mem_sup_of_comm {G : Type} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, one_mem _, by simp⟩
    · exact ⟨1, one_mem _, y, hy, by simp⟩
  · exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
    refine ⟨y₁ * y₂, mul_mem hy₁ hy₂, z₁ * z₂, mul_mem hz₁ hz₂, ?_⟩
    have := h y₂ hy₂ z₁ hz₁
    calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by group
      _ = y₁ * (z₁ * y₂) * z₂ := by rw [this]
      _ = y₁ * z₁ * (y₂ * z₂) := by group
  · rintro _ _ ⟨y, hy, z, hz, rfl⟩
    refine ⟨y⁻¹, inv_mem hy, z⁻¹, inv_mem hz, ?_⟩
    have := h y hy z hz
    calc y⁻¹ * z⁻¹ = (z * y)⁻¹ := by group
      _ = (y * z)⁻¹ := by rw [this]
      _ = _ := by group

theorem zt_comm_W {G : Type} [Group G] {z t : G} : ∀ ζ ∈ zpowers z ⊔ zpowers t,
    ∀ w ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G), ζ * w = w * ζ := by
  have hle : zpowers z ⊔ zpowers t ≤
      centralizer ((centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le, mem_centralizer_iff]
      intro g hg
      exact mem_centralizer_singleton_iff.mp hg.1
    · rw [zpowers_le, mem_centralizer_iff]
      intro g hg
      exact mem_centralizer_singleton_iff.mp hg.2
  intro ζ hζ w hw
  exact (mem_centralizer_iff.mp (hle hζ) w hw).symm

namespace PumpXSetting

variable {G : Type} [Group G] [Finite G] {q : ℕ} {z t : G} {I F₀ : Subgroup G}
  (S : PumpXSetting G q z t I F₀)

include S

theorem I_le_W : I ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) := by
  rw [S.cen]
  exact le_sup_of_le_right le_sup_left

theorem F₀_le_W : F₀ ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) := by
  rw [S.cen]
  exact le_sup_of_le_right le_sup_right

theorem z_mem_W : z ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) :=
  ⟨mem_centralizer_singleton_iff.mpr rfl, mem_centralizer_singleton_iff.mpr S.zt_comm⟩

theorem t_mem_W : t ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) :=
  ⟨mem_centralizer_singleton_iff.mpr S.zt_comm.symm, mem_centralizer_singleton_iff.mpr rfl⟩

theorem zt_le_W :
    zpowers z ⊔ zpowers t ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) :=
  sup_le (zpowers_le.mpr S.z_mem_W) (zpowers_le.mpr S.t_mem_W)

theorem W_le_normalizer_I :
    centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) ≤ normalizer (I : Set G) := by
  rw [S.cen]
  have hz : ∀ i ∈ I, z * i = i * z := fun i hi =>
    (mem_centralizer_singleton_iff.mp (S.I_le_W hi).1).symm
  have ht : ∀ i ∈ I, t * i = i * t := fun i hi =>
    (mem_centralizer_singleton_iff.mp (S.I_le_W hi).2).symm
  refine sup_le (sup_le ?_ ?_) (sup_le le_normalizer ?_)
  · rw [zpowers_le]; exact mem_normalizer_of_comm hz
  · rw [zpowers_le]; exact mem_normalizer_of_comm ht
  · intro f hf
    exact mem_normalizer_of_conj (S.F₀_norm f hf)
      (fun i hi => by simpa using S.F₀_norm f⁻¹ (inv_mem hf) i hi)

theorem W_normalizes_I : ∀ g ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G),
    ∀ i ∈ I, g * i * g⁻¹ ∈ I := fun _ hg i hi =>
  (Subgroup.mem_normalizer_iff.mp (S.W_le_normalizer_I hg) i).mp hi

theorem F₀_conj_N {f : G} (hf : f ∈ F₀) :
    ∀ n ∈ zpowers z ⊔ zpowers t ⊔ I, f * n * f⁻¹ ∈ zpowers z ⊔ zpowers t ⊔ I := by
  intro n hn
  have hz : f * z * f⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.mp (S.F₀_le_W hf).1]; group
  have ht : f * t * f⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp (S.F₀_le_W hf).2]; group
  have hmap : (zpowers z ⊔ zpowers t ⊔ I).map (MulAut.conj f).toMonoidHom ≤
      zpowers z ⊔ zpowers t ⊔ I := by
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (sup_le ?_ ?_) ?_
    · have : (MulAut.conj f).toMonoidHom z = z := by simpa [MulAut.conj_apply] using hz
      rw [this]; exact le_sup_of_le_left le_sup_left
    · have : (MulAut.conj f).toMonoidHom t = t := by simpa [MulAut.conj_apply] using ht
      rw [this]; exact le_sup_of_le_left le_sup_right
    · rintro _ ⟨i, hi, rfl⟩
      exact (le_sup_right : I ≤ zpowers z ⊔ zpowers t ⊔ I) (by
        simpa [MulAut.conj_apply] using S.F₀_norm f hf i hi)
  exact hmap ⟨n, hn, by simp [MulAut.conj_apply]⟩

theorem W_eq_sup : centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) =
    (zpowers z ⊔ zpowers t ⊔ I) ⊔ F₀ := by
  rw [S.cen]
  exact (sup_assoc _ _ _).symm

theorem N_le_W : zpowers z ⊔ zpowers t ⊔ I ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) :=
  sup_le S.zt_le_W S.I_le_W

theorem I_model :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), IVK.L2Field F ∧ Nonempty (↥I ≃* IVK.L2 F) := by
  obtain ⟨F, _, _, hq, ⟨e⟩⟩ := S.I_L2
  have hodd : Odd (Nat.card F) := by rw [hq]; exact S.odd_q
  have h5 : 3 < Nat.card F := by rw [hq]; have := S.q_ge; omega
  exact ⟨F, inferInstance, inferInstance, ⟨hodd, h5⟩, ⟨e⟩⟩

theorem I_simple : IsSimpleGroup ↥I := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := S.I_model
  exact IVK.Proofs2.isSimpleGroup_of_l2 hF e

theorem I_even : Even (Nat.card ↥I) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := S.I_model
  exact IVK.Proofs2.even_card_of_l2 hF e

theorem I_noncomm : ∃ a b : ↥I, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hle : I ≤ centralizer (I : Set G) := fun a ha =>
    mem_centralizer_iff.mpr fun b hb => congrArg Subtype.val (hcon ⟨b, hb⟩ ⟨a, ha⟩)
  have hbot : ⁅I, I⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
  rw [S.I_perf] at hbot
  have hcard : Nat.card ↥I = 1 := by rw [hbot]; exact Subgroup.card_bot
  have := S.I_even
  rw [hcard] at this
  exact absurd this (by decide)

theorem I_quasisimple : IsQuasisimple ↥I ∧ center ↥I = ⊥ := by
  have := S.I_simple
  exact CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := ↥I) S.I_noncomm

theorem F₀_le_normalizer_I : F₀ ≤ normalizer (I : Set G) := fun f hf =>
  mem_normalizer_of_conj (S.F₀_norm f hf)
    (fun i hi => by simpa using S.F₀_norm f⁻¹ (inv_mem hf) i hi)

theorem W_cen_mem : ∀ w ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G),
    (∀ i ∈ I, w * i = i * w) → w ∈ zpowers z ⊔ zpowers t := by
  intro w hw hwc
  have hMW : I ⊔ F₀ ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) :=
    sup_le S.I_le_W S.F₀_le_W
  have hw' : w ∈ (zpowers z ⊔ zpowers t) ⊔ (I ⊔ F₀) := by rw [← S.cen]; exact hw
  obtain ⟨ζ, hζ, m, hm, hwm⟩ :=
    mem_sup_of_comm (fun a ha b hb => zt_comm_W a ha b (hMW hb)) hw'
  have hmI : ∀ i ∈ I, m * i = i * m := by
    intro i hi
    have h1 := hwc i hi
    have h2 := zt_comm_W ζ hζ i (S.I_le_W hi)
    rw [← hwm] at h1
    have h3 : ζ * (m * i) = ζ * (i * m) := by
      calc ζ * (m * i) = ζ * m * i := by group
        _ = i * (ζ * m) := h1
        _ = i * ζ * m := by group
        _ = ζ * i * m := by rw [← h2]
        _ = ζ * (i * m) := by group
    exact mul_left_cancel h3
  set M₀ : Subgroup G := (I ⊔ F₀) ⊓ centralizer (I : Set G) with hM₀
  have hM₀W : M₀ ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) :=
    inf_le_left.trans hMW
  have hnorm : ∀ g ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G),
      ∀ n ∈ M₀, g * n * g⁻¹ ∈ M₀ := by
    intro g hg n hn
    have hg' : g ∈ (zpowers z ⊔ zpowers t) ⊔ (I ⊔ F₀) := by rw [← S.cen]; exact hg
    obtain ⟨ζ', hζ', m', hm', hgm⟩ :=
      mem_sup_of_comm (fun a ha b hb => zt_comm_W a ha b (hMW hb)) hg'
    have hn1 : n ∈ I ⊔ F₀ := hn.1
    have hn2 : ∀ i ∈ I, n * i = i * n := fun i hi =>
      (mem_centralizer_iff.mp hn.2 i hi).symm
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hcen : g * n * g⁻¹ = m' * n * m'⁻¹ := by
        have hζn : ζ' * (m' * n * m'⁻¹) = (m' * n * m'⁻¹) * ζ' :=
          zt_comm_W ζ' hζ' _ (mul_mem (mul_mem (hMW hm') (hM₀W hn)) (inv_mem (hMW hm')))
        rw [← hgm]
        have hζm : ζ' * m' = m' * ζ' := zt_comm_W ζ' hζ' m' (hMW hm')
        calc ζ' * m' * n * (ζ' * m')⁻¹ = ζ' * (m' * n * m'⁻¹) * ζ'⁻¹ := by group
          _ = (m' * n * m'⁻¹) * ζ' * ζ'⁻¹ := by rw [hζn]
          _ = m' * n * m'⁻¹ := by group
      rw [hcen]
      exact mul_mem (mul_mem hm' hn1) (inv_mem hm')
    · rw [mem_centralizer_iff]
      intro i hi
      have hgi : g⁻¹ * i * g ∈ I := by
        have := S.W_normalizes_I g⁻¹ (inv_mem hg) i hi
        simpa using this
      have h1 := hn2 _ hgi
      calc i * (g * n * g⁻¹) = g * ((g⁻¹ * i * g) * n) * g⁻¹ := by group
        _ = g * (n * (g⁻¹ * i * g)) * g⁻¹ := by rw [← h1]
        _ = (g * n * g⁻¹) * i := by group
  have hodd : Odd (Nat.card ↥M₀) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h2 : 2 ∣ Nat.card ↥M₀ := even_iff_two_dvd.mp hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥M₀) 2 h2
    have hxM : (x : G) ∈ I ⊔ F₀ := x.2.1
    have hxc : ∀ i ∈ I, (x : G) * i = i * (x : G) := fun i hi =>
      (mem_centralizer_iff.mp x.2.2 i hi).symm
    have hx2 : ((x : G)) ^ (2 ^ 1) = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      have h' : ((x ^ 2 : ↥M₀) : G) = 1 := by rw [this]; rfl
      simpa using h'
    have hxI : (x : G) ∈ I :=
      two_mem_sup_of_odd S.F₀_odd S.F₀_le_normalizer_I (x : G) hxM ⟨1, hx2⟩
    have hxz : (⟨(x : G), hxI⟩ : ↥I) ∈ center ↥I := by
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (hxc b b.2).symm
    rw [S.I_quasisimple.2, Subgroup.mem_bot] at hxz
    have hx1 : (x : G) = 1 := congrArg Subtype.val hxz
    have : x = 1 := Subtype.ext hx1
    rw [this, orderOf_one] at hx
    omega
  have hbot : M₀ = ⊥ := S.O2 M₀ hM₀W hnorm hodd
  have hm1 : m = 1 := by
    have hmM : m ∈ M₀ := ⟨hm, mem_centralizer_iff.mpr fun i hi => (hmI i hi).symm⟩
    rw [hbot, Subgroup.mem_bot] at hmM
    exact hmM
  rw [hm1, mul_one] at hwm
  rw [← hwm]
  exact hζ

theorem pPrimeCore_W :
    pPrimeCore 2 ↥(centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) = ⊥ := by
  set W := centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) with hW
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥W)) := TwoThin.odd_card_pPrimeCore ↥W
  have hNW : (pPrimeCore 2 ↥W).map W.subtype ≤ W := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hNnorm : ∀ g ∈ W, ∀ n ∈ (pPrimeCore 2 ↥W).map W.subtype,
      g * n * g⁻¹ ∈ (pPrimeCore 2 ↥W).map W.subtype := by
    rintro g hg _ ⟨a, ha, rfl⟩
    refine ⟨⟨g, hg⟩ * a * ⟨g, hg⟩⁻¹, (pPrimeCore_normal (p := 2) (G := ↥W)).conj_mem a ha ⟨g, hg⟩, ?_⟩
    simp
  have hNodd : Odd (Nat.card ↥((pPrimeCore 2 ↥W).map W.subtype)) := by
    have e := Subgroup.equivMapOfInjective (pPrimeCore 2 ↥W) W.subtype W.subtype_injective
    rw [← Nat.card_congr e.toEquiv]
    exact hodd
  have hbot : (pPrimeCore 2 ↥W).map W.subtype = ⊥ := S.O2 _ hNW hNnorm hNodd
  have hle := (Subgroup.map_eq_bot_iff _).mp hbot
  have hker : W.subtype.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr W.subtype_injective
  rw [hker] at hle
  exact le_bot_iff.mp hle

theorem I_normal_in_W :
    (I.subgroupOf (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff S.I_le_W).mpr fun h k hh hk => S.W_normalizes_I k hk h hh

theorem I_comp : IsPCompIn 2 (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) I := by
  refine ⟨S.I_le_W, ?_⟩
  have := S.I_normal_in_W
  refine KGroups.TwoA7.isPComponent_of_normal S.pPrimeCore_W ?_
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe S.I_le_W).symm S.I_quasisimple.1

end PumpXSetting

end CFSG.GH74.GLS.SP.Local
