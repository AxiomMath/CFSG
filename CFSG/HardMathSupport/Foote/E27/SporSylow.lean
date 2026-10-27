module

public import CFSG.HardMathSupport.Foote.E27.SplitIn

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

theorem conj_map_centralizer {G : Type*} [Group G] (g x : G) :
    (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * x * g⁻¹} : Set G) := by
  ext y
  rw [mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_centralizer_singleton_iff] at hw
    rw [mem_centralizer_singleton_iff]
    show g * w * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * w * g⁻¹)
    calc g * w * g⁻¹ * (g * x * g⁻¹) = g * (w * x) * g⁻¹ := by group
      _ = g * (x * w) * g⁻¹ := by rw [hw]
      _ = g * x * g⁻¹ * (g * w * g⁻¹) := by group
  · intro hy
    rw [mem_centralizer_singleton_iff] at hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
        _ = x * (g⁻¹ * y * g) := by group
    · show g * (g⁻¹ * y * g) * g⁻¹ = y
      group

theorem centralizer_map_val_eq {X : Type*} [Group X] (K : Subgroup X) (z : X) (hz : z ∈ K) :
    (centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K)).map K.subtype = centralizer ({z} : Set X) ⊓ K := by
  ext x
  rw [mem_map, mem_inf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff] at hy
    refine ⟨?_, y.2⟩
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hy
  · rintro ⟨hx1, hx2⟩
    refine ⟨⟨x, hx2⟩, ?_, rfl⟩
    rw [mem_centralizer_singleton_iff] at hx1
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext hx1

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.exists_conj_mem_sylow (h : E27Config X K R T z) (hz : z ∈ K)
    (S₀ : Sylow 3 ↥K) : ∃ z₀ ∈ (S₀ : Subgroup ↥K), orderOf z₀ = 3 ∧
      Nat.card ↥((S₀ : Subgroup ↥K) ⊓ Subgroup.centralizer ({z₀} : Set ↥K)) = 27 ∧
      (∀ D : Subgroup ↥K, D ≤ Subgroup.centralizer ({z₀} : Set ↥K) → ⁅D, D⁆ = D →
        ¬ 3 ∣ Nat.card D) ∧
      ¬ 81 ∣ Nat.card (Subgroup.centralizer ({z₀} : Set ↥K)) := by
  set zK : ↥K := ⟨z, hz⟩ with hzK
  have hzK' : (zK : X) = z := rfl
  have hRK : R ≤ K := h.le_of_mem hz
  set R₁ : Subgroup ↥K := R.subgroupOf K with hR₁
  have hR₁card : Nat.card ↥R₁ = 27 := by
    rw [← h.card_R]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv
  have hR₁p : IsPGroup 3 ↥R₁ := IsPGroup.of_card (n := 3) (by rw [hR₁card]; norm_num)
  obtain ⟨S₁, hS₁⟩ := hR₁p.exists_le_sylow
  have hzR₁ : zK ∈ R₁ := Subgroup.mem_subgroupOf.mpr h.z_mem
  have hzS₁ : zK ∈ (S₁ : Subgroup ↥K) := hS₁ hzR₁
  have hR₁C : R₁ ≤ centralizer ({zK} : Set ↥K) := by
    intro r hr
    have hr' : (r : X) ∈ R := Subgroup.mem_subgroupOf.mp hr
    have hcomm : (r : X) * z = z * (r : X) :=
      congrArg Subtype.val (h.elem.1.is_comm.comm (⟨r, hr'⟩ : R) ⟨z, h.z_mem⟩)
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext hcomm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K S₁ S₀
  set z₀ : ↥K := MulAut.conj g zK with hz₀
  have hconj : ∀ x ∈ (S₁ : Subgroup ↥K), MulAut.conj g x ∈ (S₀ : Subgroup ↥K) := by
    intro x hx
    rw [← hg]
    show MulAut.conj g x ∈ ((g • S₁ : Sylow 3 ↥K) : Set ↥K)
    rw [Sylow.coe_smul]
    exact Set.smul_mem_smul_set hx
  have hz₀S₀ : z₀ ∈ (S₀ : Subgroup ↥K) := hconj zK hzS₁
  have hC₀ : centralizer ({z₀} : Set ↥K) =
      (centralizer ({zK} : Set ↥K)).map (MulAut.conj g).toMonoidHom :=
    (conj_map_centralizer g zK).symm
  have hzne : z ≠ 1 := fun e => h.z_not_mem (by rw [e]; exact T.one_mem)
  have hord : orderOf z = 3 := orderOf_eq_prime (h.elem.2 z h.z_mem) hzne
  have hordK : orderOf zK = 3 := by
    rw [← orderOf_coe]
    exact hord
  have hinjφ : Function.Injective (MulAut.conj g).toMonoidHom :=
    MulEquiv.injective (MulAut.conj g)
  have hord₀ : orderOf z₀ = 3 := by
    rw [hz₀, ← hordK]
    exact orderOf_injective (MulAut.conj g).toMonoidHom hinjφ zK
  have hCcard : Nat.card ↥(centralizer ({zK} : Set ↥K)) =
      Nat.card ↥(centralizer ({z} : Set X) ⊓ K) := by
    rw [← centralizer_map_val_eq K z hz, Subgroup.card_map_of_injective K.subtype_injective]
  have hfac := h.factorization_card_centralizer_inf_of_mem hz
  have hincl : ∀ Q : Subgroup ↥K, Q ≤ centralizer ({zK} : Set ↥K) →
      Q.map K.subtype ≤ centralizer ({z} : Set X) := fun Q hQ =>
    (Subgroup.map_mono hQ).trans
      ((le_of_eq (centralizer_map_val_eq K z hz)).trans inf_le_left)
  have hsub : ∀ Q : Subgroup ↥K, Q ≤ centralizer ({z₀} : Set ↥K) →
      Q.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({zK} : Set ↥K) := by
    intro Q hQ
    have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hQ
    rw [conj_map_centralizer g⁻¹ z₀] at h1
    have e : g⁻¹ * z₀ * g⁻¹⁻¹ = zK := by
      show g⁻¹ * (g * zK * g⁻¹) * g⁻¹⁻¹ = zK
      group
    rw [e] at h1
    exact h1
  have hψinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom :=
    MulEquiv.injective (MulAut.conj g⁻¹)
  have hbound : ∀ Q : Subgroup ↥K, Q ≤ centralizer ({z₀} : Set ↥K) → IsPGroup 3 ↥Q →
      Nat.card ↥Q ≤ 27 := by
    intro Q hQ hQp
    have hpg : IsPGroup 3 ↥((Q.map (MulAut.conj g⁻¹).toMonoidHom).map K.subtype) :=
      ((hQp.map _).map _)
    have h27 := h.card_le_twentyseven_of_isPGroup (hincl _ (hsub Q hQ)) hpg
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective hψinj] at h27
    exact h27
  have hS₀p : IsPGroup 3 ↥((S₀ : Subgroup ↥K) ⊓ centralizer ({z₀} : Set ↥K)) :=
    IsPGroup.to_le (S₀.isPGroup') inf_le_left
  have hup : Nat.card ↥((S₀ : Subgroup ↥K) ⊓ centralizer ({z₀} : Set ↥K)) ≤ 27 :=
    hbound _ inf_le_right hS₀p
  have hW : R₁.map (MulAut.conj g).toMonoidHom ≤
      (S₀ : Subgroup ↥K) ⊓ centralizer ({z₀} : Set ↥K) := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := mem_map.mp hy
    refine mem_inf.mpr ⟨hconj r (hS₁ hr), ?_⟩
    rw [hC₀]
    exact mem_map_of_mem _ (hR₁C hr)
  have hlow : 27 ≤ Nat.card ↥((S₀ : Subgroup ↥K) ⊓ centralizer ({z₀} : Set ↥K)) := by
    have := Subgroup.card_le_of_le hW
    rwa [Subgroup.card_map_of_injective hinjφ, hR₁card] at this
  refine ⟨z₀, hz₀S₀, hord₀, le_antisymm hup hlow, ?_, ?_⟩
  ·
    intro D hD hcomm hdvd
    have hD1 := hsub D hD
    have hcommψ : ⁅D.map (MulAut.conj g⁻¹).toMonoidHom,
        D.map (MulAut.conj g⁻¹).toMonoidHom⁆ =
        D.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [← Subgroup.map_commutator, hcomm]
    have hcommX : ⁅(D.map (MulAut.conj g⁻¹).toMonoidHom).map K.subtype,
        (D.map (MulAut.conj g⁻¹).toMonoidHom).map K.subtype⁆ =
        (D.map (MulAut.conj g⁻¹).toMonoidHom).map K.subtype := by
      rw [← Subgroup.map_commutator, hcommψ]
    have hperf := h.perfect _ (hincl _ hD1) hcommX
    apply hperf
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective hψinj]
    exact hdvd
  ·
    rw [hC₀, Subgroup.card_map_of_injective hinjφ, hCcard]
    intro hdiv
    have hn : Nat.card ↥(centralizer ({z} : Set X) ⊓ K) ≠ 0 := by
      intro h0
      rw [h0] at hfac
      simp at hfac
    have h81 : 3 ^ 4 ∣ Nat.card ↥(centralizer ({z} : Set X) ⊓ K) := by
      norm_num
      exact hdiv
    have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn).mp h81
    omega

end CFSG.HardMathSupport.Foote.E27
