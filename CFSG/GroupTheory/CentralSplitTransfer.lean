module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.GroupTheory

theorem not_mem_commutator_of_mem_center {C : Type*} [Group C] [Finite C] {p : ℕ} [Fact p.Prime]
    (P : Sylow p C) (hP : IsMulCommutative ↥P) {s : C} (hs : s ∈ Subgroup.center C)
    (hsp : orderOf s = p) : s ∉ commutator C := by
  intro hscomm
  letI : CommGroup ↥P := IsMulCommutative.instCommGroup
  let tr : C →* ↥P := MonoidHom.transfer (MonoidHom.id ↥P)
  have key : ∀ k : ℕ, ∀ g₀ : C,
      g₀⁻¹ * s ^ k * g₀ ∈ (P : Subgroup C) → g₀⁻¹ * s ^ k * g₀ = s ^ k := by
    intro k g₀ _
    have hcomm : s ^ k * g₀ = g₀ * s ^ k :=
      (Subgroup.mem_center_iff.mp ((Subgroup.center C).pow_mem hs k) g₀).symm
    calc g₀⁻¹ * s ^ k * g₀ = g₀⁻¹ * (g₀ * s ^ k) := by rw [mul_assoc, hcomm]
      _ = s ^ k := by group
  have htr := MonoidHom.transfer_eq_pow (MonoidHom.id ↥P) s key
  have hpow : s ^ (P : Subgroup C).index = 1 := by
    have hker : tr s = 1 := Abelianization.commutator_subset_ker tr hscomm
    have h2 := htr.symm.trans hker
    have h3 := congrArg (fun y : ↥P => (y : C)) h2
    change s ^ (P : Subgroup C).index = 1 at h3
    exact h3
  have hdvd : p ∣ (P : Subgroup C).index := by
    simpa [hsp] using orderOf_dvd_of_pow_eq_one hpow
  exact Sylow.not_dvd_index P hdvd

theorem commutator_inf_zpowers_eq_bot {C : Type*} [Group C] [Finite C] {p : ℕ} [Fact p.Prime]
    (P : Sylow p C) (hP : IsMulCommutative ↥P) {s : C} (hs : s ∈ Subgroup.center C)
    (hsp : orderOf s = p) : commutator C ⊓ Subgroup.zpowers s = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hxne
  have hxord : orderOf x = p := by
    have hdvd : orderOf x ∣ p := by
      simpa [hsp] using orderOf_dvd_of_mem_zpowers hx.2
    have hne1 : orderOf x ≠ 1 := fun h => hxne (orderOf_eq_one_iff.mp h)
    exact (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd |>.resolve_left hne1
  have hxcenter : x ∈ Subgroup.center C := (Subgroup.zpowers_le.mpr hs) hx.2
  exact not_mem_commutator_of_mem_center P hP hxcenter hxord hx.1

theorem not_mem_commutator_of_relIndex {X : Type*} [Group X] {C H : Subgroup X} {p : ℕ}
    [Fact p.Prime] (hHC : H ≤ C) (hidx : ¬ p ∣ H.relIndex C) {s : X} (hsH : s ∈ H)
    (hs : ∀ x ∈ C, Commute s x) (hsp : orderOf s = p) (hsH' : s ∉ ⁅H, H⁆) :
    s ∉ ⁅C, C⁆ := by
  classical
  intro hsC
  have hC : s ∈ C := hHC hsH
  let H' : Subgroup ↥C := H.subgroupOf C
  have hH'index : H'.index = H.relIndex C := rfl
  have hH'ne : H'.index ≠ 0 := by
    rintro h0
    exact hidx (by rw [← hH'index, h0]; exact dvd_zero p)
  haveI : H'.FiniteIndex := Subgroup.FiniteIndex.mk hH'ne
  let s' : ↥C := ⟨s, hC⟩
  have hsc : s' ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (hs (x : X) x.2).eq.symm
  have key : ∀ (k : ℕ) (g₀ : ↥C), g₀⁻¹ * s' ^ k * g₀ ∈ H' → g₀⁻¹ * s' ^ k * g₀ = s' ^ k := by
    intro k g₀ _
    have hcomm : Commute (s ^ k) (g₀ : X) := Commute.pow_left (hs (g₀ : X) g₀.2) k
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    calc (g₀ : X)⁻¹ * s ^ k * (g₀ : X) = (g₀ : X)⁻¹ * (s ^ k * (g₀ : X)) := by group
      _ = (g₀ : X)⁻¹ * ((g₀ : X) * s ^ k) := by rw [hcomm.eq]
      _ = s ^ k := by group
  have htr := MonoidHom.transfer_eq_pow
    (Abelianization.of : ↥H' →* Abelianization ↥H') s' key
  have hs'comm : s' ∈ commutator ↥C := by
    have h : s ∈ Subgroup.map C.subtype (commutator ↥C) := by
      rw [Subgroup.map_subtype_commutator]
      exact hsC
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp h
    have hxs : x = s' := Subtype.ext hxeq
    simpa [hxs] using hx
  have htriv : Abelianization.of.transfer s' = 1 :=
    MonoidHom.mem_ker.mp
      (Abelianization.commutator_subset_ker
        (MonoidHom.transfer (Abelianization.of : ↥H' →* Abelianization ↥H')) hs'comm)
  have hpow : (⟨s' ^ H'.index, MonoidHom.transfer_eq_pow_aux s' key⟩ : ↥H') ∈
      commutator ↥H' := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    rw [← htr, htriv]
  have hsn : s ^ H'.index ∈ ⁅H, H⁆ := by
    have h1 : ((⟨s' ^ H'.index, MonoidHom.transfer_eq_pow_aux s' key⟩ : ↥H') : ↥C) ∈
        Subgroup.map H'.subtype (commutator ↥H') := Subgroup.mem_map_of_mem _ hpow
    rw [Subgroup.map_subtype_commutator] at h1
    have h2 : ((⟨s' ^ H'.index, MonoidHom.transfer_eq_pow_aux s' key⟩ : ↥H') : X) ∈
        Subgroup.map C.subtype ⁅H', H'⁆ := Subgroup.mem_map_of_mem _ h1
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hHC] at h2
    simpa using h2
  have hcop : Nat.Coprime H'.index (orderOf s) := by
    rw [hsp]
    exact Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr (by rwa [hH'index]))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := s) (n := H'.index) hcop
  exact hsH' (hm ▸ Subgroup.pow_mem _ hsn m)

end CFSG.GroupTheory

end
