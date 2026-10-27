module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4Fusion
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4FusionTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer
open scoped commutatorElement

@[expose] def Data.Delta {G : Type} [Group G] (d : Data G) : Set G :=
  {y | ∃ x ∈ normalizer ((d.withT d.A₂ : Subgroup G) : Set G), x⁻¹ * d.t * x = y}

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem mem_Delta_iff
    (h : d.Hyp) {y : G} :
    y ∈ d.Delta ↔ (∃ g : G, g⁻¹ * d.t * g = y) ∧ y ∈ d.withT d.F := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    have := (mem_normalizer_iff.1 (inv_mem (h.normalizer_A₂t_le hx)) d.t).1
      (mem_sup_right (mem_zpowers _))
    simpa using this
  · rintro ⟨⟨g, rfl⟩, hg⟩
    exact h.exists_normalizer_conj_eq hg

theorem t_mem_Delta (_h : d.Hyp) : d.t ∈ d.Delta :=
  ⟨1, one_mem _, by group⟩

theorem conj_mem_Delta
    (h : d.Hyp) {m : G} (hmL : m ∈ d.L)
    (hmF : ∀ f ∈ d.F, m * f * m⁻¹ ∈ d.F) {y : G} (hy : y ∈ d.Delta) : m * y * m⁻¹ ∈ d.Delta := by
  obtain ⟨⟨g, rfl⟩, hyF⟩ := (h.mem_Delta_iff).1 hy
  refine (h.mem_Delta_iff).2 ⟨⟨g * m⁻¹, by group⟩, ?_⟩
  obtain ⟨a, ha, k, hak⟩ := h.exists_eq_mul_of_mem_withT_F hyF
  have hmt : m * d.t ^ k * m⁻¹ = d.t ^ k := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Commute.zpow_right (comm_of_mem_centralizer h.t_mem hmL) k).eq
  rw [hak, show m * (a * d.t ^ k) * m⁻¹ = m * a * m⁻¹ * (m * d.t ^ k * m⁻¹) by group, hmt]
  exact mul_mem (mem_sup_left (hmF a ha)) (mem_sup_right (zpow_mem (mem_zpowers _) k))

omit [Finite G] in
theorem ι_N0_conj_mem_F {n : SU52} (hn : n ∈ N0sub) :
    ∀ f ∈ d.F, d.ι n * f * (d.ι n)⁻¹ ∈ d.F := by
  rintro _ ⟨φ, hφ, rfl⟩
  rw [ι_conj]
  exact d.ι_mem_pull_iff.2 ((mem_normalizer_iff.1 (N0sub_le_normalizer hn) φ).1 hφ)

theorem orb5_mem_Delta
    (h : d.Hyp) {k : Fin 5}
    (hk : d.ι (orb5SU k) * d.t ∈ d.Delta) (k' : Fin 5) : d.ι (orb5SU k') * d.t ∈ d.Delta := by
  obtain ⟨n, hn, hnk⟩ := exists_N0_conj_orb5 k
  obtain ⟨n', hn', hnk'⟩ := exists_N0_conj_orb5 k'
  have hm : n' * n⁻¹ ∈ N0sub := mul_mem hn' (inv_mem hn)
  have e : n' * n⁻¹ * orb5SU k * (n' * n⁻¹)⁻¹ = orb5SU k' := by
    rw [← hnk, ← hnk']
    group
  have := h.conj_mem_Delta (d.ι_mem (n' * n⁻¹)) (ι_N0_conj_mem_F hm) hk
  rwa [show d.ι (n' * n⁻¹) * (d.ι (orb5SU k) * d.t) * (d.ι (n' * n⁻¹))⁻¹ =
    d.ι (n' * n⁻¹) * d.ι (orb5SU k) * (d.ι (n' * n⁻¹))⁻¹ *
      (d.ι (n' * n⁻¹) * d.t * (d.ι (n' * n⁻¹))⁻¹) by group, ι_conj, e,
    mul_inv_eq_iff_eq_mul.2 (comm_of_mem_centralizer h.t_mem (d.ι_mem _))] at this

theorem orb10_mem_Delta
    (h : d.Hyp) {k : Fin 10}
    (hk : d.ι (orb10SU k) * d.t ∈ d.Delta) (k' : Fin 10) : d.ι (orb10SU k') * d.t ∈ d.Delta := by
  obtain ⟨n, hn, hnk⟩ := exists_N0_conj_orb10 k
  obtain ⟨n', hn', hnk'⟩ := exists_N0_conj_orb10 k'
  have hm : n' * n⁻¹ ∈ N0sub := mul_mem hn' (inv_mem hn)
  have e : n' * n⁻¹ * orb10SU k * (n' * n⁻¹)⁻¹ = orb10SU k' := by
    rw [← hnk, ← hnk']
    group
  have := h.conj_mem_Delta (d.ι_mem (n' * n⁻¹)) (ι_N0_conj_mem_F hm) hk
  rwa [show d.ι (n' * n⁻¹) * (d.ι (orb10SU k) * d.t) * (d.ι (n' * n⁻¹))⁻¹ =
    d.ι (n' * n⁻¹) * d.ι (orb10SU k) * (d.ι (n' * n⁻¹))⁻¹ *
      (d.ι (n' * n⁻¹) * d.t * (d.ι (n' * n⁻¹))⁻¹) by group, ι_conj, e,
    mul_inv_eq_iff_eq_mul.2 (comm_of_mem_centralizer h.t_mem (d.ι_mem _))] at this

theorem mem_Delta_cases
    (h : d.Hyp) {y : G} (hy : y ∈ d.Delta) :
    y = d.t ∨ (∃ k, y = d.ι (orb5SU k) * d.t) ∨ ∃ k, y = d.ι (orb10SU k) * d.t := by
  obtain ⟨⟨g, rfl⟩, hyF⟩ := (h.mem_Delta_iff).1 hy
  obtain ⟨a, ⟨φ, hφ, rfl⟩, e⟩ := h.conj_mem_F_mul_t hyF
  rw [e]
  by_cases hφ1 : φ = 1
  · left
    rw [hφ1, map_one, one_mul]
  · right
    rcases mem_orb5_or_mem_orb10 hφ hφ1 with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, rfl⟩

theorem mem_F_of_mem_withT_F_of_mem_L (h : d.Hyp) {z : G} (hz : z ∈ d.withT d.F)
    (hzL : z ∈ d.L) : z ∈ d.F := by
  obtain ⟨a, ha, k, rfl⟩ := h.exists_eq_mul_of_mem_withT_F hz
  have hk' : d.t ^ k = d.t ^ (k % 2) := by
    rw [← zpow_mod_orderOf, h.t_two]
    norm_cast
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [hk', h0, zpow_zero, mul_one]
    exact ha
  · exfalso
    rw [hk', h1, zpow_one] at hzL
    exact h.t_not_mem_L (by simpa using mul_mem (inv_mem (h.F_le_L ha)) hzL)

theorem card_withT_A₂
    (h : d.Hyp) :
    Nat.card (d.withT d.A₂) = 16 * Nat.card (d.withT d.F) := by
  rw [← h.A₂T_eq, h.card_A₂T, h.centralizer_inf_H_eq, h.card_zpowers_t, h.card_withT_F]
  norm_num

theorem exists_eq_mul_of_mem_withT_A₂
    (h : d.Hyp) {p : G}
    (hp : p ∈ d.withT d.A₂) : ∃ a ∈ d.A₂, ∃ c ∈ zpowers d.t, p = a * c := by
  rw [← h.A₂T_eq] at hp
  obtain ⟨a, ha, c, hc, rfl⟩ := (mem_sup_kernel_iff (d.pull_le_L _)).1 hp
  rw [h.centralizer_inf_H_eq] at hc
  exact ⟨a, ha, c, hc, rfl⟩

theorem comm_zpowers_t (h : d.Hyp) {c : G} (hc : c ∈ zpowers d.t) :
    (∀ l ∈ d.L, l * c = c * l) ∧ ∀ c' ∈ zpowers d.t, c * c' = c' * c := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  refine ⟨fun l hl => (Commute.zpow_right (comm_of_mem_centralizer h.t_mem hl) k).eq,
    fun c' hc' => ?_⟩
  obtain ⟨k', rfl⟩ := mem_zpowers_iff.1 hc'
  rw [← zpow_add, ← zpow_add, add_comm]

theorem section_hyps
    (h : d.Hyp) :
    (∀ p ∈ d.withT d.A₂, ∀ q ∈ d.withT d.A₂, p * q * p⁻¹ * q⁻¹ ∈ d.withT d.F) ∧
      ∀ p ∈ d.withT d.A₂, p * p ∈ d.withT d.F := by
  constructor
  · intro p hp q hq
    obtain ⟨a, ⟨α, hα, rfl⟩, c, hc, rfl⟩ := h.exists_eq_mul_of_mem_withT_A₂ hp
    obtain ⟨b, ⟨β, hβ, rfl⟩, c', hc', rfl⟩ := h.exists_eq_mul_of_mem_withT_A₂ hq
    have hcL := (h.comm_zpowers_t hc).1
    have hc'L := (h.comm_zpowers_t hc').1
    have e : d.ι α * c * (d.ι β * c') * (d.ι α * c)⁻¹ * (d.ι β * c')⁻¹ = ⁅d.ι α, d.ι β⁆ := by
      rw [← commutatorElement_def, commutatorElement_mul_mul_eq (hcL _ (d.ι_mem β)).symm
        ((h.comm_zpowers_t hc).2 c' hc') (hc'L _ (d.ι_mem α)).symm]
    rw [e, ← map_commutatorElement]
    exact mem_sup_left (d.ι_mem_pull_iff.2 (commutator_mem_Fsub hα hβ))
  · intro p hp
    obtain ⟨a, ⟨α, hα, rfl⟩, c, hc, rfl⟩ := h.exists_eq_mul_of_mem_withT_A₂ hp
    have hcα := (h.comm_zpowers_t hc).1 _ (d.ι_mem α)
    rw [show d.ι α * c * (d.ι α * c) = d.ι α * d.ι α * (c * c) by
      rw [show d.ι α * c * (d.ι α * c) = d.ι α * (c * d.ι α) * c by group, ← hcα]; group,
      ← map_mul]
    exact mul_mem (mem_sup_left (d.ι_mem_pull_iff.2 (mul_self_mem_Fsub hα)))
      (mem_sup_right (mul_mem hc hc))

@[expose] def X₀ (d : Data G) : Subgroup G :=
  (secHom (d.withT d.A₂)).ker.map (normalizer ((d.withT d.A₂ : Subgroup G) : Set G)).subtype

omit [Finite G] in
theorem X₀_le : X₀ d ≤ normalizer ((d.withT d.A₂ : Subgroup G) : Set G) := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem conj_mul_inv_mem_of_mem_X₀
    (h : d.Hyp) {x : G}
    (hx : x ∈ X₀ d) {p : G} (hp : p ∈ d.withT d.A₂) : x * p * x⁻¹ * p⁻¹ ∈ d.withT d.F := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hc := (secHom_eq_one_iff _ y).1 hy p hp
  have hxp : (y : G) * p * (y : G)⁻¹ ∈ d.withT d.A₂ := (mem_normalizer_iff.1 y.2 p).1 hp
  exact (h.mem_center_A₂t_iff).1 ⟨mul_mem hxp (inv_mem hp), fun q hq => hc q hq⟩

omit [Finite G] in
theorem conj_mem_X₀ {x k : G} (hx : x ∈ normalizer ((d.withT d.A₂ : Subgroup G) : Set G))
    (hk : k ∈ X₀ d) : x * k * x⁻¹ ∈ X₀ d := by
  obtain ⟨y, hy, rfl⟩ := hk
  have hy' : secHom (d.withT d.A₂) y = 1 := hy
  refine ⟨⟨x, hx⟩ * y * (⟨x, hx⟩)⁻¹, ?_, rfl⟩
  change secHom (d.withT d.A₂) (⟨x, hx⟩ * y * (⟨x, hx⟩)⁻¹) = 1
  rw [map_mul, map_mul, hy', mul_one, map_inv, mul_inv_cancel]

theorem comm_F_of_mem_X₀
    (h : d.Hyp) {x : G} (hx : x ∈ X₀ d) {f : G} (hf : f ∈ d.F) :
    x * f = f * x := by
  have hP : ∀ α ∈ A₂sub, d.ι α ∈ d.withT d.A₂ := fun α hα => mem_sup_left (d.ι_mem_pull_iff.2 hα)
  have hz : ∀ α ∈ A₂sub, ∃ z ∈ d.withT d.F, x * d.ι α * x⁻¹ = z * d.ι α := fun α hα =>
    ⟨_, h.conj_mul_inv_mem_of_mem_X₀ hx (hP α hα), by group⟩
  have hcen : ∀ z ∈ d.withT d.F, ∀ q ∈ d.withT d.A₂, z * q = q * z := fun z hz =>
    ((h.mem_center_A₂t_iff).2 hz).2
  have hgen : ∀ j, x * d.ι (genFSU j) * x⁻¹ = d.ι (genFSU j) := by
    intro j
    obtain ⟨α, hα, β, hβ, e⟩ := exists_genFSU_eq_commutator j
    obtain ⟨z₁, hz₁, e₁⟩ := hz α hα
    obtain ⟨z₂, hz₂, e₂⟩ := hz β hβ
    rw [e, map_commutatorElement, commutatorElement_def,
      show x * (d.ι α * d.ι β * (d.ι α)⁻¹ * (d.ι β)⁻¹) * x⁻¹ =
        (x * d.ι α * x⁻¹) * (x * d.ι β * x⁻¹) * (x * d.ι α * x⁻¹)⁻¹ * (x * d.ι β * x⁻¹)⁻¹ by
        group, e₁, e₂, hcen z₁ hz₁ _ (hP α hα), hcen z₂ hz₂ _ (hP β hβ),
      ← commutatorElement_def, ← commutatorElement_def,
      commutatorElement_mul_mul_eq (hcen z₁ hz₁ _ (hP β hβ))
        (hcen z₁ hz₁ _ (h.withT_F_le_A₂T hz₂ |> (h.A₂T_eq ▸ ·)))
        (hcen z₂ hz₂ _ (hP α hα))]
  have hle : closure (Set.range genFSU) ≤ (centralizer ({x} : Set G)).comap d.ι := by
    refine (closure_le _).2 ?_
    rintro _ ⟨j, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    have := hgen j
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [closure_genFSU] at hle
  obtain ⟨φ, hφ, rfl⟩ := hf
  exact (mem_centralizer_singleton_iff.1 (hle hφ)).symm

theorem conj_t_mul_inv_mem_F
    (h : d.Hyp) {x : G} (hx : x ∈ X₀ d) :
    x⁻¹ * d.t * x * d.t⁻¹ ∈ d.F := by
  have hxN := h.normalizer_A₂t_le (X₀_le hx)
  have hmem : x⁻¹ * d.t * x ∈ d.withT d.F := by
    have := (mem_normalizer_iff.1 (inv_mem hxN) d.t).1 (mem_sup_right (mem_zpowers _))
    simpa using this
  obtain ⟨a, ha, e⟩ := h.conj_mem_F_mul_t hmem
  rw [e, mul_inv_cancel_right]
  exact ha

theorem torus_le
    (h : d.Hyp) :
    d.pull Esub ≤ normalizer ((d.withT d.A₂ : Subgroup G) : Set G) ⊓ d.H := by
  rintro _ ⟨e, he, rfl⟩
  refine ⟨mem_normalizer_fintype fun p hp => ?_, h.L_le_H (d.ι_mem e)⟩
  obtain ⟨a, ⟨α, hα, rfl⟩, c, hc, rfl⟩ := h.exists_eq_mul_of_mem_withT_A₂ hp
  have hct : d.ι e * c * (d.ι e)⁻¹ = c := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (h.comm_zpowers_t hc).1 _ (d.ι_mem e)
  rw [show d.ι e * (d.ι α * c) * (d.ι e)⁻¹ = d.ι e * d.ι α * (d.ι e)⁻¹ * (d.ι e * c * (d.ι e)⁻¹) by
    group, hct, ι_conj]
  exact mul_mem (mem_sup_left (d.ι_mem_pull_iff.2 (DiagSub_conj_mem_A₂sub (Esub_le_DiagSub he) hα)))
    (mem_sup_right hc)

theorem torus_inf_X₀
    (h : d.Hyp) : d.pull Esub ⊓ X₀ d = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨e, he, rfl⟩, hx⟩
  rw [mem_bot]
  have he1 : e = 1 := eq_one_of_conj_mul_inv_mem_Fsub (Esub_le_DiagSub he) fun α hα => by
    have hP : d.ι α ∈ d.withT d.A₂ := mem_sup_left (d.ι_mem_pull_iff.2 hα)
    have h1 := h.conj_mul_inv_mem_of_mem_X₀ hx hP
    rw [ι_conj, ← map_inv, ← map_mul] at h1
    exact d.ι_mem_pull_iff.1 (h.mem_F_of_mem_withT_F_of_mem_L h1 (d.ι_mem _))
  rw [he1, map_one]

theorem nine_dvd_relIndex
    (h : d.Hyp) :
    9 ∣ (X₀ d ⊓ d.H).relIndex (normalizer ((d.withT d.A₂ : Subgroup G) : Set G) ⊓ d.H) := by
  set M := normalizer ((d.withT d.A₂ : Subgroup G) : Set G) ⊓ d.H with hM
  set K := X₀ d ⊓ d.H with hK
  have hKM : K ≤ M := inf_le_inf_right _ X₀_le
  have hnorm : (K.subgroupOf M).Normal := by
    constructor
    intro k hk m
    rw [mem_subgroupOf] at hk ⊢
    have hmX := (Subgroup.mem_inf.1 m.2).1
    have hmH := (Subgroup.mem_inf.1 m.2).2
    have hkX := (Subgroup.mem_inf.1 hk).1
    have hkH := (Subgroup.mem_inf.1 hk).2
    rw [coe_mul, coe_mul, coe_inv]
    exact Subgroup.mem_inf.2 ⟨conj_mem_X₀ hmX hkX, mul_mem (mul_mem hmH hkH) (inv_mem hmH)⟩
  set f : d.pull Esub →* M ⧸ K.subgroupOf M :=
    (QuotientGroup.mk' (K.subgroupOf M)).comp (inclusion h.torus_le) with hf
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf] at hy
    have : (y : G) ∈ d.pull Esub ⊓ X₀ d := ⟨y.2, (Subgroup.mem_inf.1 hy).1⟩
    rw [h.torus_inf_X₀, mem_bot] at this
    exact mem_bot.2 (Subtype.ext this)
  have hdvd := Subgroup.card_dvd_of_injective f hinj
  rw [d.card_pull, card_Esub] at hdvd
  exact hdvd

theorem ncard_Delta_ne
    (h : d.Hyp) : d.Delta.ncard ≠ 6 ∧ d.Delta.ncard ≠ 11 := by
  set P := d.withT d.A₂ with hP
  set X := normalizer ((P : Subgroup G) : Set G) with hX
  set M := X ⊓ d.H with hM
  set K := X₀ d ⊓ d.H with hK
  have hΔ : (centralizer ({d.t} : Set G)).relIndex X = d.Delta.ncard :=
    relIndex_centralizer_eq_ncard X d.t
  have hidx₁ : (X₀ d).relIndex X ∣ 20160 := by
    have e : (X₀ d).relIndex X = (secHom P).ker.index := by
      rw [relIndex, X₀, subgroupOf, comap_map_eq_self_of_injective (subtype_injective _)]
    rw [e]
    obtain ⟨hcomm, hsq⟩ := h.section_hyps
    exact index_ker_secHom_dvd P (fun z => (h.mem_center_A₂t_iff).symm) h.card_withT_A₂ hcomm
      hsq
  have hidx₂ : (centralizer ({d.t} : Set G)).relIndex (X₀ d) ∣ 16 := by
    have := relIndex_centralizer_dvd_card (K := X₀ d) (V := d.F) (t := d.t)
      (fun x hx f hf => h.comm_F_of_mem_X₀ hx hf) (fun x hx => h.conj_t_mul_inv_mem_F hx)
    rwa [d.card_F] at this
  have hidx₃ := h.nine_dvd_relIndex
  have e1 := Subgroup.relIndex_mul_card (X₀ d) X
  rw [inf_eq_left.2 X₀_le] at e1
  have e2 := Subgroup.relIndex_mul_card (centralizer ({d.t} : Set G)) (X₀ d)
  have e3 := Subgroup.relIndex_mul_card (centralizer ({d.t} : Set G)) X
  have e4 := Subgroup.relIndex_mul_card K M
  have hKM : K ≤ M := inf_le_inf_right _ X₀_le
  rw [inf_eq_left.2 hKM] at e4
  have hc2 : (centralizer ({d.t} : Set G) ⊓ X₀ d : Subgroup G) = K := by
    rw [hK, inf_comm]
    rfl
  have hc3 : (centralizer ({d.t} : Set G) ⊓ X : Subgroup G) = M := by
    rw [hM, inf_comm]
    rfl
  rw [hc2] at e2
  rw [hc3, hΔ] at e3
  have hK0 : 0 < Nat.card K := Nat.card_pos
  have key : (X₀ d).relIndex X * (centralizer ({d.t} : Set G)).relIndex (X₀ d) =
      d.Delta.ncard * K.relIndex M := by
    apply Nat.eq_of_mul_eq_mul_right hK0
    rw [mul_assoc, e2, e1, ← e3, ← e4, mul_assoc]
  have hdvd : (X₀ d).relIndex X * (centralizer ({d.t} : Set G)).relIndex (X₀ d) ∣ 20160 * 16 :=
    Nat.mul_dvd_mul hidx₁ hidx₂
  rw [key] at hdvd
  obtain ⟨m, hm⟩ := hidx₃
  rw [hm] at hdvd
  constructor
  · intro e
    rw [e] at hdvd
    have : 54 ∣ 20160 * 16 := Dvd.dvd.trans ⟨m, by ring⟩ hdvd
    norm_num at this
  · intro e
    rw [e] at hdvd
    have : 11 ∣ 20160 * 16 := Dvd.dvd.trans ⟨9 * m, by ring⟩ hdvd
    norm_num at this

theorem mul_t_mem_Delta
    (h : d.Hyp) {a : G} (ha : a ∈ d.F) : a * d.t ∈ d.Delta := by
  set o5 : Fin 5 → G := fun k => d.ι (orb5SU k) * d.t with ho5
  set o10 : Fin 10 → G := fun k => d.ι (orb10SU k) * d.t with ho10
  have hi5 : Function.Injective o5 := fun k l e =>
    orb5SU_injective (d.ι_injective (mul_right_cancel e))
  have hi10 : Function.Injective o10 := fun k l e =>
    orb10SU_injective (d.ι_injective (mul_right_cancel e))
  have ht5 : d.t ∉ Set.range o5 := by
    rintro ⟨k, e⟩
    have : d.ι (orb5SU k) = 1 := by simpa [ho5] using e
    exact orb5SU_ne_one k (d.ι_injective (this.trans (map_one d.ι).symm))
  have ht10 : d.t ∉ Set.range o10 := by
    rintro ⟨k, e⟩
    have : d.ι (orb10SU k) = 1 := by simpa [ho10] using e
    exact orb10SU_ne_one k (d.ι_injective (this.trans (map_one d.ι).symm))
  have hP5 : d.ι (orb5SU 0) * d.t ∈ d.Delta := by
    by_contra hn5
    by_cases hP10 : d.ι (orb10SU 0) * d.t ∈ d.Delta
    ·
      have heq : d.Delta = insert d.t (Set.range o10) := by
        ext y
        constructor
        · intro hy
          rcases h.mem_Delta_cases hy with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩
          · exact Set.mem_insert _ _
          · exact absurd (h.orb5_mem_Delta (k := k) hy 0) hn5
          · exact Set.mem_insert_of_mem _ ⟨k, rfl⟩
        · rintro (rfl | ⟨k, rfl⟩)
          · exact h.t_mem_Delta
          · exact h.orb10_mem_Delta hP10 k
      have hc : d.Delta.ncard = 11 := by
        rw [heq, Set.ncard_insert_of_notMem ht10, Set.ncard_range_of_injective hi10,
          Nat.card_eq_fintype_card, Fintype.card_fin]
      exact (h.ncard_Delta_ne).2 hc
    ·
      obtain ⟨g, hgF, hgt⟩ := h.exists_conj_mem_withT_F_ne
      have hy := (h.mem_Delta_iff).2 ⟨⟨g, rfl⟩, hgF⟩
      rcases h.mem_Delta_cases hy with e | ⟨k, e⟩ | ⟨k, e⟩
      · exact hgt e
      · exact hn5 (h.orb5_mem_Delta (e ▸ hy) 0)
      · exact hP10 (h.orb10_mem_Delta (e ▸ hy) 0)
  have hP10 : d.ι (orb10SU 0) * d.t ∈ d.Delta := by
    by_contra hn10
    have heq : d.Delta = insert d.t (Set.range o5) := by
      ext y
      constructor
      · intro hy
        rcases h.mem_Delta_cases hy with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ ⟨k, rfl⟩
        · exact absurd (h.orb10_mem_Delta (k := k) hy 0) hn10
      · rintro (rfl | ⟨k, rfl⟩)
        · exact h.t_mem_Delta
        · exact h.orb5_mem_Delta hP5 k
    have hc : d.Delta.ncard = 6 := by
      rw [heq, Set.ncard_insert_of_notMem ht5, Set.ncard_range_of_injective hi5,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    exact (h.ncard_Delta_ne).1 hc
  obtain ⟨φ, hφ, rfl⟩ := ha
  by_cases hφ1 : φ = 1
  · rw [hφ1, map_one, one_mul]
    exact h.t_mem_Delta
  · rcases mem_orb5_or_mem_orb10 hφ hφ1 with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact h.orb5_mem_Delta hP5 k
    · exact h.orb10_mem_Delta hP10 k

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
