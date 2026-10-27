module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.A6Facts

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M24Std

variable {G : Type} [Group G] [Finite G] {z : G} {Q : Type} [Group Q] [IsCyclic Q]

theorem mul_comm_of_isCyclic (a b : Q) : a * b = b * a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
  exact (Commute.zpow_zpow_self g m n).eq

theorem mul_self_eq_one_z2 (ε : Multiplicative (ZMod 2)) : ε * ε = 1 := by
  have h : ∀ x : ZMod 2, x + x = 0 := by decide
  exact Multiplicative.toAdd.injective (h _)

theorem sq_mem_alternatingGroup (σ : Equiv.Perm (Fin 6)) : σ * σ ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
  exact Int.units_mul_self _

theorem card_ker_eq_720 (π : G →* Q)
    (φ : ↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))
    (hz : π z ≠ 1) :
    Nat.card (π.comp (centralizer ({z} : Set G)).subtype).ker = 720 := by
  set D := centralizer ({z} : Set G) with hD
  set ψ := π.comp D.subtype with hψ
  let ι : alternatingGroup (Fin 6) →* D :=
    φ.symm.toMonoidHom.comp ((MonoidHom.inr (Multiplicative (ZMod 2)) (Equiv.Perm (Fin 6))).comp
      (alternatingGroup (Fin 6)).subtype)
  have hA : ∀ a : alternatingGroup (Fin 6), ψ (ι a) = 1 := by
    have : (ψ.comp ι).ker.Normal := MonoidHom.normal_ker _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ψ.comp ι).ker with h0 | h0
    · exfalso
      have hinj : Function.Injective (ψ.comp ι) := (MonoidHom.ker_eq_bot_iff _).1 h0
      have hc : ∀ a b : alternatingGroup (Fin 6), a * b = b * a := fun a b =>
        hinj (by rw [map_mul, map_mul]; exact mul_comm_of_isCyclic _ _)
      have hcen : Subgroup.center (alternatingGroup (Fin 6)) = ⊤ := by
        rw [eq_top_iff]
        intro a _
        rw [Subgroup.mem_center_iff]
        exact fun b => hc b a
      rw [center_alternatingGroup_six] at hcen
      obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin 6))
      have : a ∈ (⊥ : Subgroup (alternatingGroup (Fin 6))) := hcen ▸ Subgroup.mem_top a
      exact ha (Subgroup.mem_bot.1 this)
    · intro a
      have h : a ∈ (ψ.comp ι).ker := h0 ▸ Subgroup.mem_top a
      exact h
  have hsq : ∀ d : D, ψ d * ψ d = 1 := by
    intro d
    obtain ⟨ε, σ, hd⟩ : ∃ ε σ, φ d = (ε, σ) := ⟨(φ d).1, (φ d).2, rfl⟩
    have hdd : d * d = ι ⟨σ * σ, sq_mem_alternatingGroup σ⟩ := by
      apply φ.injective
      have h1 : φ (d * d) = (ε * ε, σ * σ) := by rw [map_mul, hd]; rfl
      rw [h1]
      show _ = φ (φ.symm (1, σ * σ))
      rw [MulEquiv.apply_symm_apply]
      exact Prod.ext (mul_self_eq_one_z2 ε) rfl
    rw [← map_mul, hdd]
    exact hA _
  have hrange : Nat.card ψ.range ≤ 2 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ψ.range)
    have hg2 : g * g = 1 := by
      obtain ⟨d, hd⟩ := g.2
      apply Subtype.ext
      show (g : Q) * (g : Q) = 1
      rw [← hd]
      exact hsq d
    have hord : orderOf g = Nat.card ψ.range := orderOf_eq_card_of_forall_mem_zpowers hg
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    rw [← hord]
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hDcard : Nat.card D = 1440 := by rw [Nat.card_congr φ.toEquiv, natCard_z2s6]
  have hidx : ψ.ker.index = Nat.card ψ.range := Subgroup.index_ker ψ
  have hmul := Subgroup.card_mul_index ψ.ker
  have hne : ψ.ker ≠ ⊤ := by
    intro h
    have : ψ ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ = 1 :=
      MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top _)
    exact hz this
  have hidx1 : ψ.ker.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
  have hidx2 : ψ.ker.index = 2 := by
    have : ψ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  rw [hidx2, hDcard] at hmul
  omega

theorem nonempty_ker_equiv_perm_six (π : G →* Q)
    (φ : ↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))
    (hz : π z ≠ 1) :
    Nonempty (↥(π.comp (centralizer ({z} : Set G)).subtype).ker ≃* Equiv.Perm (Fin 6)) := by
  set D := centralizer ({z} : Set G) with hD
  set ψ := π.comp D.subtype with hψ
  have h720 := card_ker_eq_720 π φ hz
  let z' : D := ⟨z, mem_centralizer_singleton_iff.2 rfl⟩
  have hz' : ψ z' ≠ 1 := hz
  have hz1 : z' ≠ 1 := fun h => hz' (by rw [h, map_one])
  have hcen : ∀ q : Multiplicative (ZMod 2) × Equiv.Perm (Fin 6), q * φ z' = φ z' * q := by
    intro q
    have : φ.symm q * z' = z' * φ.symm q := Subtype.ext
      (mem_centralizer_singleton_iff.1 (φ.symm q).2)
    simpa using congrArg φ this
  have hs : (φ z').2 = 1 := by
    apply centralizer_alt_six
    intro a _
    have h := congrArg Prod.snd (hcen (1, a))
    simpa using h.symm
  have hε : (φ z').1 ≠ 1 := by
    intro h
    exact hz1 (φ.injective (Prod.ext (by simpa using h) (by simpa using hs)))
  let θ : ψ.ker →* Equiv.Perm (Fin 6) :=
    (MonoidHom.snd (Multiplicative (ZMod 2)) (Equiv.Perm (Fin 6))).comp
      (φ.toMonoidHom.comp ψ.ker.subtype)
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have hm2 : (φ (m : D)).2 = 1 := hm
    by_cases h1 : (φ (m : D)).1 = 1
    · have : (m : D) = 1 := φ.injective (Prod.ext (by simpa using h1) (by simpa using hm2))
      exact Subtype.ext this
    · exfalso
      have heq : (φ (m : D)).1 = (φ z').1 := by
        have : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by decide
        exact this _ _ h1 hε
      have : (m : D) = z' := φ.injective (Prod.ext heq (by rw [hm2, hs]))
      have hmk : ψ (m : D) = 1 := MonoidHom.mem_ker.1 m.2
      rw [this] at hmk
      exact hz' hmk
  have hcard : Nat.card ψ.ker = Nat.card (Equiv.Perm (Fin 6)) := by rw [h720, CResH4.card_perm_six]
  exact ⟨MulEquiv.ofBijective θ ((Nat.bijective_iff_injective_and_card θ).2 ⟨hinj, hcard⟩)⟩


end CFSG.EvenSporadicStandard.M22Std
