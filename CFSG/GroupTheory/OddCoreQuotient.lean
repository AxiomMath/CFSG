module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.OddTranspositions.WidthSylow

import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.Timmesfeld.Bridge.Asc73Quotient

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {K : Type*} [Group K]

theorem map_conj_inf_centralizer {O : Subgroup K} [O.Normal] (c b : K) :
    (O ⊓ Subgroup.centralizer ({b} : Set K)).map (MulAut.conj c).toMonoidHom =
      O ⊓ Subgroup.centralizer ({c * b * c⁻¹} : Set K) := by
  rw [Subgroup.map_inf O (Subgroup.centralizer ({b} : Set K))
    (MulAut.conj c).toMonoidHom (MulAut.conj c).injective]
  have hOmap : O.map (MulAut.conj c).toMonoidHom = O := by
    simpa using Subgroup.Normal.map_conj_eq O c
  rw [hOmap]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : Commute y b := Subgroup.mem_centralizer_singleton_iff.mp hy
    have h1 : Commute ((MulAut.conj c) y) (c * b * c⁻¹) := by
      simpa only [MulAut.conj_apply] using (Commute.conj_iff c).mpr hy'
    exact Subgroup.mem_centralizer_singleton_iff.mpr h1
  · intro hx
    have hx' : Commute x (c * b * c⁻¹) := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hconj : c⁻¹ * (c * b * c⁻¹) * c = b := by group
    refine ⟨c⁻¹ * x * c, ?_, ?_⟩
    · have h1 : Commute (c⁻¹ * x * c) (c⁻¹ * (c * b * c⁻¹) * c) := by
        simpa using (Commute.conj_iff c⁻¹).mpr hx'
      rw [hconj] at h1
      exact Subgroup.mem_centralizer_singleton_iff.mpr h1
    · show (MulAut.conj c) (c⁻¹ * x * c) = x
      rw [MulAut.conj_apply]
      group

theorem le_center_of_centralizes_set {H : Type*} [Group H] {E : Set H} {O : Subgroup H}
    (hgen : Subgroup.closure E = ⊤) (h : ∀ d ∈ E, ∀ n ∈ O, Commute n d) :
    O ≤ Subgroup.center H := by
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.closure E := by rw [hgen]; exact Subgroup.mem_top g
  have hcomm : Commute n g := by
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact h x hx n hn
    | one => exact Commute.one_right n
    | mul x y _ _ hx hy => exact hx.mul_right hy
    | inv x _ hx => exact hx.inv_right
  exact hcomm.eq.symm

theorem card_inf_centralizer_eq_of_isConj {O : Subgroup K} [O.Normal] {b u : K}
    (h : IsConj b u) :
    Nat.card ↥(O ⊓ Subgroup.centralizer ({b} : Set K)) =
      Nat.card ↥(O ⊓ Subgroup.centralizer ({u} : Set K)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  calc Nat.card ↥(O ⊓ Subgroup.centralizer ({b} : Set K))
      = Nat.card ↥((O ⊓ Subgroup.centralizer ({b} : Set K)).map
          (MulAut.conj c).toMonoidHom) :=
        (Subgroup.card_map_of_injective
          (K := O ⊓ Subgroup.centralizer ({b} : Set K))
          (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective).symm
    _ = Nat.card ↥(O ⊓ Subgroup.centralizer ({c * b * c⁻¹} : Set K)) := by
        rw [map_conj_inf_centralizer]

theorem mul_mem_commutator_of_conj {H : Type*} [Group H] {d e k : H}
    (hk : k * e * k⁻¹ = d) (he : e * e = 1) : d * e ∈ commutator H := by
  have hdeq : d * e = ⁅k, e⁆ := by
    calc d * e = k * e * k⁻¹ * e := by rw [← hk]
      _ = k * e * k⁻¹ * e⁻¹ := by rw [← eq_inv_of_mul_eq_one_right he]
      _ = ⁅k, e⁆ := rfl
  rw [hdeq]
  simpa [commutator_def] using Subgroup.commutator_mem_commutator
    (H₁ := (⊤ : Subgroup H)) (H₂ := (⊤ : Subgroup H))
    (show k ∈ (⊤ : Subgroup H) from trivial) (show e ∈ (⊤ : Subgroup H) from trivial)

theorem isPGroup_two_map_mk_oddCore_of_le_center {H : Type*} [Group H] [Finite H]
    {R : Subgroup H} (hR : R ≤ Subgroup.center H) :
    IsPGroup 2 (R.map (QuotientGroup.mk' (CFSG.oddCore H))) := by
  rintro ⟨y, hy⟩
  obtain ⟨s, hs, rfl⟩ := hy
  obtain ⟨a, m, hm2, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos s).ne' 2 (by norm_num)
  have hmodd : Odd m := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm2)
  have hsZ : s ∈ Subgroup.center H := hR hs
  have hyZ : s ^ 2 ^ a ∈ Subgroup.center H := Subgroup.pow_mem _ hsZ _
  have hyOrd : orderOf (s ^ 2 ^ a) ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← hord, pow_orderOf_eq_one]
  have hyO : s ^ 2 ^ a ∈ CFSG.oddCore H := by
    have hodd : Odd (Nat.card (Subgroup.zpowers (s ^ 2 ^ a))) := by
      rw [Nat.card_zpowers]
      exact Odd.of_dvd_nat hmodd hyOrd
    exact CFSG.ABGLocalTools.le_oddCore_of_normal
      (Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hyZ)) hodd
      (Subgroup.mem_zpowers _)
  refine ⟨a, Subtype.ext ?_⟩
  show (QuotientGroup.mk' (CFSG.oddCore H) s) ^ 2 ^ a = 1
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hyO

theorem mul_mem_oddCore_of_mem_center {H : Type} [Group H] [Finite H] {c z : H}
    (hz : z ∈ Subgroup.center H) (hzz : z * z = 1) (hcz : c ∈ Subgroup.center H)
    (hπc : QuotientGroup.mk' (CFSG.oddCore H) c ∉ commutator (H ⧸ CFSG.oddCore H))
    (hπz : QuotientGroup.mk' (CFSG.oddCore H) z ∉ commutator (H ⧸ CFSG.oddCore H))
    (hinf : (CFSG.solvableRadical H).map (QuotientGroup.mk' (CFSG.oddCore H)) ⊓
      commutator (H ⧸ CFSG.oddCore H) = ⊥)
    (hidx : (commutator (H ⧸ CFSG.oddCore H)).index = 2) :
    c * z ∈ CFSG.oddCore H := by
  classical
  set O := CFSG.oddCore H with hO
  set π : H →* H ⧸ O := QuotientGroup.mk' O with hπ
  have hπc' : π c ∉ commutator (H ⧸ O) := by simpa only [hπ, hO] using hπc
  have hπz' : π z ∉ commutator (H ⧸ O) := by simpa only [hπ, hO] using hπz
  have hinf' : (CFSG.solvableRadical H).map π ⊓ commutator (H ⧸ O) = ⊥ := by
    simpa only [hπ, hO] using hinf
  have hπcE : π c ∈ (CFSG.solvableRadical H).map π :=
    Subgroup.mem_map_of_mem π (CFSG.OddTranspositions.center_le_solvableRadical H hcz)
  have hπzE : π z ∈ (CFSG.solvableRadical H).map π :=
    Subgroup.mem_map_of_mem π (CFSG.OddTranspositions.center_le_solvableRadical H hz)
  have hprodE : π c * (π z)⁻¹ ∈ (CFSG.solvableRadical H).map π :=
    Subgroup.mul_mem _ hπcE (Subgroup.inv_mem _ hπzE)
  have hprodK : π c * (π z)⁻¹ ∈ commutator (H ⧸ O) := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact iff_of_false hπc' (fun h => hπz' ((Subgroup.inv_mem_iff _).mp h))
  have hprod1 : π c * (π z)⁻¹ = 1 := by
    have hmem := Subgroup.mem_inf.mpr ⟨hprodE, hprodK⟩
    rw [hinf', Subgroup.mem_bot] at hmem
    exact hmem
  have h1 : π (c * z⁻¹) = 1 := by
    rw [map_mul, map_inv, hprod1]
  have h2 := (QuotientGroup.eq_one_iff (c * z⁻¹)).mp h1
  rwa [inv_eq_of_mul_eq_one_right hzz] at h2

theorem exists_conj_mul_mem_solvableRadical {H : Type*} [Group H] [Finite H]
    {R : Subgroup H} [R.Normal] (hR : R ≤ Subgroup.center H)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (H ⧸ R)) {u t : H}
    (hu2 : u * u = 1) (huR : u ∉ R) (ht2 : t * t = 1) (htR : t ∉ R) :
    ∃ d r : H, (∃ g : H, d = g * u * g⁻¹) ∧ r ∈ R ∧ t = d * r ∧ r * r = 1 := by
  have h2prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : H →* H ⧸ R := QuotientGroup.mk' R
  have hπu : π u ≠ 1 := fun h1 => huR ((QuotientGroup.eq_one_iff u).mp h1)
  have hπt : π t ≠ 1 := fun h1 => htR ((QuotientGroup.eq_one_iff t).mp h1)
  have hUord : orderOf (π u) = 2 :=
    orderOf_eq_prime (p := 2) (hp := h2prime) (by rw [pow_two, ← map_mul, hu2, map_one]) hπu
  have hTord : orderOf (π t) = 2 :=
    orderOf_eq_prime (p := 2) (hp := h2prime) (by rw [pow_two, ← map_mul, ht2, map_one]) hπt
  obtain ⟨k, hk⟩ := isConj_iff.mp
    (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hB hUord hTord)
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective R k
  rw [← hg] at hk
  let d : H := g * u * g⁻¹
  let r : H := d⁻¹ * t
  have hπd : π d = π t := by simpa only [d, map_mul, map_inv] using hk
  have hπr : π r = 1 := by simp only [r, map_mul, map_inv, hπd, inv_mul_cancel]
  have hrR : r ∈ R := (QuotientGroup.eq_one_iff r).mp hπr
  have hd2 : d * d = 1 := by
    simp only [d]
    calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have ht_eq : t = d * r := by simp only [r]; group
  have hrZ : r ∈ Subgroup.center H := hR hrR
  have hT_exp : t * t = r * r := by
    calc t * t = (d * r) * (d * r) := by rw [ht_eq]
      _ = (d * d) * (r * r) := by
        rw [show (d * r) * (d * r) = d * (r * d) * r by group,
          ← Subgroup.mem_center_iff.mp hrZ d]
        group
      _ = r * r := by rw [hd2, one_mul]
  have hrr : r * r = 1 := by rw [← hT_exp]; exact ht2
  exact ⟨d, r, ⟨g, rfl⟩, hrR, ht_eq, hrr⟩

theorem eq_of_mul_mem_oddCore_of_mem_center {H : Type*} [Group H] [Finite H] {c z : H}
    (hcz : z * c = c * z) (hc2 : c * c = 1) (hz2 : z * z = 1)
    (hO : c * z ∈ CFSG.oddCore H) : c = z := by
  have hsq : (c * z) * (c * z) = 1 := by
    calc (c * z) * (c * z) = c * (z * c) * z := by group
      _ = c * (c * z) * z := by rw [hcz]
      _ = (c * c) * (z * z) := by group
      _ = 1 := by rw [hc2, hz2, mul_one]
  have hcz1 : c * z = 1 := by
    by_contra hne
    have hord : orderOf (c * z) = 2 :=
      @orderOf_eq_prime H _ (c * z) 2 ⟨Nat.prime_two⟩ (by rwa [pow_two]) hne
    exact CFSG.Timmesfeld.Connectivity.not_mem_of_odd_card
      (CFSG.ABGLocalTools.odd_card_oddCore (H := H)) hord hO
  calc c = c * (z * z) := by rw [hz2, mul_one]
    _ = (c * z) * z := by group
    _ = z := by rw [hcz1, one_mul]

theorem exists_conj_mem_sylow_of_commute {G : Type} [Group G] [Finite G] {z b : G}
    (S : Sylow 2 G)
    (hzc : ∀ s ∈ S, Commute s z) (hzb : IsConj z b) (hb : Commute b z) (hne : b ≠ z)
    (hb2 : b * b = 1) :
    ∃ a ∈ S, a ≠ z ∧ IsConj z a ∧ a * a = 1 ∧ Commute a z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  have hSC : (S : Subgroup G) ≤ C := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc s hs).eq
  have hbC : b ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hb.eq
  let x : C := ⟨b, hbC⟩
  have hx2 : x * x = 1 := Subtype.ext hb2
  let P : Sylow 2 C := S.subtype hSC
  have hxP : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨y, hy⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hyy : y * y = 1 := by
      rcases (CFSG.Timmesfeld.Bridge.mem_zpowers_of_mul_self hx2).mp hy with rfl | rfl
      · exact one_mul 1
      · exact Subtype.ext hb2
    simp [pow_two, hyy]
  obtain ⟨R, hR⟩ := hxP.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C R P
  have h1 : x ∈ (R : Subgroup C) := hR (Subgroup.mem_zpowers x)
  have h2 : c * x * c⁻¹ ∈ ((c • R : Sylow 2 C) : Subgroup C) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
    simpa only [show c⁻¹ * (c * x * c⁻¹) * c = x by group] using h1
  rw [hc] at h2
  have hcb : (c : G) * b * (c : G)⁻¹ ∈ S := h2
  have hcz : Commute (c : G) z := Subgroup.mem_centralizer_singleton_iff.mp c.2
  refine ⟨(c : G) * b * (c : G)⁻¹, hcb, ?_, ?_, ?_, hzc _ hcb⟩
  · intro h
    apply hne
    calc b = (c : G)⁻¹ * ((c : G) * b * (c : G)⁻¹) * c := by group
      _ = (c : G)⁻¹ * z * c := by rw [h]
      _ = z := by rw [hcz.inv_left.eq]; group
  · obtain ⟨k, hk⟩ := isConj_iff.mp hzb
    exact isConj_iff.mpr ⟨(c : G) * k, by
      rw [show (c : G) * k * z * ((c : G) * k)⁻¹ =
        (c : G) * (k * z * k⁻¹) * (c : G)⁻¹ by group, hk]⟩
  · rw [show (c : G) * b * (c : G)⁻¹ * ((c : G) * b * (c : G)⁻¹) =
      (c : G) * (b * b) * (c : G)⁻¹ by group, hb2, mul_one, mul_inv_cancel]


end CFSG.GroupTheory
