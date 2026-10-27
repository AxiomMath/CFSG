module

public import CFSG.GH74.Uniqueness.SU.SU8UConf
public import CFSG.GH74.Uniqueness.SU.SU8Setup
public import CFSG.GH74.Uniqueness.Bender.Unitary

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.SU.SU8.UConf CFSG.GH74.Uniqueness.SU.SU8.Setup
open scoped commutatorElement

namespace UFrat

theorem exists_mul_mem_normalizer_pgroup {X : Type*} [Group X] [Finite X] {N R : Subgroup X}
    [N.Normal] (hN : Odd (Nat.card N)) (hR : IsPGroup 2 R) {m : X}
    (hm : ∀ a ∈ R, m⁻¹ * a * m ∈ N ⊔ R) :
    ∃ r ∈ N, m * r ∈ normalizer (R : Set X) := by
  have hRN : R ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := hR ⟨x, hx.1⟩
    have h1 : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h2 : x ^ (Nat.card N) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hx.2)
    exact eq_one_of_pow_odd h1 h2 hN
  have hcard : Nat.card ↥(N ⊔ R) = Nat.card N * Nat.card R :=
    CFSG.GH74.Uniqueness.Bender.card_sup_eq_mul_of_le_normalizer (A := N) (B := R)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top) (by rw [inf_comm]; exact hRN)
  set NR : Subgroup X := N ⊔ R with hNRdef
  have hR_le : R ≤ NR := le_sup_right
  set B : Subgroup X := R.map (MulAut.conj m⁻¹).toMonoidHom with hB
  have hB_mem : ∀ x, x ∈ B ↔ ∃ a ∈ R, m⁻¹ * a * m = x := by
    intro x
    simp [hB, Subgroup.mem_map]
  have hB_le : B ≤ NR := fun x hx => by
    obtain ⟨a, ha, rfl⟩ := (hB_mem x).mp hx
    exact hm a ha
  have hBp : IsPGroup 2 B := hR.map _
  have hpg : ∀ C : Subgroup X, IsPGroup 2 C → C ≤ NR → IsPGroup 2 ↥(C.subgroupOf NR) :=
    fun C hC hCNR => hC.of_equiv (Subgroup.subgroupOfEquivOfLe hCNR).symm
  have hindex : ∀ C : Subgroup X, Nat.card C = Nat.card R → C ≤ NR →
      ¬ 2 ∣ (C.subgroupOf NR).index := by
    intro C hCR hCNR
    have h1 := Subgroup.card_mul_index (C.subgroupOf NR)
    have h2 : Nat.card ↥(C.subgroupOf NR) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCNR).toEquiv
    rw [h2, hCR, hcard] at h1
    have hRpos : 0 < Nat.card R := Nat.card_pos
    have h3 : (C.subgroupOf NR).index = Nat.card N := by
      have : Nat.card R * (C.subgroupOf NR).index = Nat.card R * Nat.card N := by
        rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_left hRpos this
    rw [h3]
    have := Nat.odd_iff.mp hN
    omega
  have hBcard : Nat.card B = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective
  let P₁ : Sylow 2 ↥NR := (hpg R hR hR_le).toSylow (hindex R rfl hR_le)
  let P₂ : Sylow 2 ↥NR := (hpg B hBp hB_le).toSylow (hindex B hBcard hB_le)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥NR) P₁ P₂
  have hP2 : ∀ x : ↥NR, (x : X) ∈ B ↔ g⁻¹ * x * g ∈ R.subgroupOf NR := by
    intro x
    have h1 : x ∈ ((P₂ : Sylow 2 ↥NR) : Subgroup ↥NR) ↔ (x : X) ∈ B := Subgroup.mem_subgroupOf
    rw [← h1, ← hg, Setup.mem_sylow_smul_iff]
    rfl
  obtain ⟨r, hr, a, ha, hra⟩ := Subgroup.mem_sup_of_normal_left.mp g.2
  refine ⟨r, hr, mem_normalizer_of_conj_le fun a₀ ha₀ => ?_⟩
  have hrNR : r ∈ NR := Subgroup.mem_sup_left hr
  have hmem : r * a₀ * r⁻¹ ∈ NR :=
    NR.mul_mem (NR.mul_mem hrNR (hR_le ha₀)) (NR.inv_mem hrNR)
  have hx := (hP2 ⟨r * a₀ * r⁻¹, hmem⟩).mpr (by
    rw [Subgroup.mem_subgroupOf]
    have : (g⁻¹ * (⟨r * a₀ * r⁻¹, hmem⟩ : ↥NR) * g : ↥NR) = ⟨a⁻¹ * a₀ * a, by
        exact NR.mul_mem (NR.mul_mem (NR.inv_mem (hR_le ha)) (hR_le ha₀)) (hR_le ha)⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hra]; group
    rw [this]
    exact R.mul_mem (R.mul_mem (R.inv_mem ha) ha₀) ha)
  obtain ⟨a₁, ha₁, h₁⟩ := (hB_mem _).mp hx
  have h₁' : r * a₀ * r⁻¹ = m⁻¹ * a₁ * m := h₁.symm
  have : m * r * a₀ * (m * r)⁻¹ = a₁ := by
    calc m * r * a₀ * (m * r)⁻¹ = m * (r * a₀ * r⁻¹) * m⁻¹ := by group
      _ = a₁ := by rw [h₁']; group
  rw [this]
  exact ha₁

theorem exists_conf {N K : Type*} [Group N] [Finite N] [Group K] [Finite K] (φ : N →* K)
    (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker))
    (A₀ : Subgroup N) (hA₀ : ∀ a ∈ A₀, a * a = 1) (hA₀card : Nat.card A₀ = 4)
    (hK : ∀ P : Sylow 2 K, ∃ (Zp : Subgroup K) (c : K), KConf (P : Subgroup K) Zp c) :
    ∃ (R : Subgroup N) (y : N), ConfData R A₀ y := by
  classical
  obtain ⟨Q, hAQ⟩ :=
    (CFSG.GH74.Uniqueness.Bender.isPGroup_two_of_mul_self_eq_one hA₀).exists_le_sylow
  set R : Subgroup N := (Q : Subgroup N) with hRdef
  let P : Sylow 2 K := Q.mapSurjective hφ
  have hP : (P : Subgroup K) = R.map φ := Sylow.coe_mapSurjective hφ Q
  obtain ⟨Zp, c, kc⟩ := hK P
  rw [hP] at kc
  have hinj : ∀ a ∈ R, ∀ b ∈ R, φ a = φ b → a = b := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab]; group
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨a⁻¹ * b, R.mul_mem (R.inv_mem ha) hb⟩
    have hk' : (a⁻¹ * b) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    exact inv_mul_eq_one.mp (eq_one_of_mem_odd hker hmem hk')
  have hcardmap : ∀ E : Subgroup N, E ≤ R → Nat.card (E.map φ) = Nat.card E := by
    intro E hE
    have hψ : Function.Injective (φ.comp E.subtype) := by
      intro a b hab
      exact Subtype.ext (hinj a (hE a.2) b (hE b.2) hab)
    have hrange : (φ.comp E.subtype).range = E.map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  have hφA : ∀ u ∈ A₀, φ u ∈ Zp := by
    intro u hu
    refine kc.invol _ ⟨u, hAQ hu, rfl⟩ ?_
    rw [← map_mul, hA₀ u hu, map_one]
  have hmapA : A₀.map φ = Zp := by
    have hle : A₀.map φ ≤ Zp := by
      rintro _ ⟨u, hu, rfl⟩
      exact hφA u hu
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [kc.card_Z, hcardmap A₀ hAQ, hA₀card]
  have hcN' : ∀ p ∈ R.map φ, c⁻¹ * p * c ∈ R.map φ :=
    UAbs.inv_conj_mem (A := R.map φ) kc.c_norm
  obtain ⟨y₁, hy₁⟩ := hφ c
  have hm : ∀ a ∈ R, y₁⁻¹ * a * y₁ ∈ φ.ker ⊔ R := by
    intro a ha
    have h1 : c⁻¹ * φ a * c ∈ R.map φ := hcN' _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hbe⟩ := h1
    have h2 : b⁻¹ * (y₁⁻¹ * a * y₁) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbe, map_mul, map_mul, map_inv, hy₁]; group
    have : y₁⁻¹ * a * y₁ = b * (b⁻¹ * (y₁⁻¹ * a * y₁)) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hb) (Subgroup.mem_sup_left h2)
  obtain ⟨r₀, hr₀, hyN⟩ :=
    exists_mul_mem_normalizer_pgroup (N := φ.ker) (R := R) hker Q.isPGroup' hm
  set y : N := y₁ * r₀ with hy
  have hφy : φ y = c := by rw [hy, map_mul, hy₁, (MonoidHom.mem_ker.mp hr₀), mul_one]
  have hynorm : ∀ r ∈ R, y * r * y⁻¹ ∈ R := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp hyN r).mp hr
  have hcZ : ∀ w ∈ Zp, c * w * c⁻¹ = w := by
    refine conj_fixes_of_pow_five c kc.c_five Zp (fun w hw => ?_) (by rw [kc.card_Z]; norm_num)
    apply kc.invol _ (kc.c_norm w (kc.Z_le hw))
    calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
      _ = 1 := by rw [kc.Z_sq w hw]; group
  refine ⟨R, y, ?_, ?_, hAQ, ?_, hA₀, ?_, hynorm, ?_, ?_, ?_⟩
  · have := hcardmap R le_rfl
    exact this.symm.trans kc.card_P
  · exact hA₀card
  · intro w hw r hr
    apply hinj _ (R.mul_mem (hAQ hw) hr) _ (R.mul_mem hr (hAQ hw))
    rw [map_mul, map_mul]
    exact kc.Z_central _ (hφA w hw) _ ⟨r, hr, rfl⟩
  · intro u hu
    have hcomm_le : ⁅R, R⁆ ≤ R := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      simp only [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)
    have h1 : φ u ∈ (⁅R, R⁆ : Subgroup N).map φ := by
      rw [Subgroup.map_commutator, kc.comm_eq]
      exact hφA u hu
    obtain ⟨v, hv, hvu⟩ := h1
    have := hinj v (hcomm_le hv) u (hAQ hu) hvu
    rw [← this]; exact hv
  · intro w hw
    apply hinj _ (hynorm w (hAQ hw)) _ (hAQ hw)
    rw [map_mul, map_mul, map_inv, hφy]
    exact hcZ _ (hφA w hw)
  · intro r hr hrA
    have h1 : φ (y * r * y⁻¹ * r⁻¹) ∈ Zp := by
      rw [← hmapA]; exact ⟨_, hrA, rfl⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hφy] at h1
    have h2 : φ r ∈ Zp := kc.fpf _ ⟨r, hr, rfl⟩ h1
    rw [← hmapA] at h2
    obtain ⟨a, ha, hae⟩ := h2
    have := hinj a (hAQ ha) r hr hae
    rw [← this]; exact ha
  · intro r hr
    have hy5 : y ^ 5 ∈ normalizer (R : Set N) := pow_mem hyN 5
    have hr5 : y ^ 5 * r * (y ^ 5)⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hy5 r).mp hr
    apply hinj _ hr5 _ hr
    rw [map_mul, map_mul, map_inv, map_pow, hφy, kc.c_five]
    simp

end UFrat

end CFSG.GH74.Uniqueness.SU.SU8
