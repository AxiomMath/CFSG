module

public import CFSG.GH74.Uniqueness.SU.KI1r4L34Model
public import CFSG.GH74.KGroups.Generic6
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import CFSG.GH74.KGroups.L34Tables

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.L34M

open Subgroup CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Sporadic.Schreier
open scoped commutatorElement

variable {H : Type} [Group H]

theorem actHom_eq_e {N : Subgroup H} [N.Normal] (M : AutModel ↥N (Equiv.Perm (Fin 42)))
    (hPA : M.P ≤ M.A) (k : H) (hk : k ∈ N) :
    M.actHom N k = (M.e ⟨k, hk⟩ : Equiv.Perm (Fin 42)) := by
  have hτA : (M.e ⟨k, hk⟩ : Equiv.Perm (Fin 42)) ∈ M.A := hPA (M.e ⟨k, hk⟩).2
  have hσA : M.actHom N k ∈ M.A := M.actHom_mem N k
  have hcomm : ∀ y ∈ M.P, ((M.e ⟨k, hk⟩ : Equiv.Perm (Fin 42))⁻¹ * M.actHom N k) * y =
      y * ((M.e ⟨k, hk⟩ : Equiv.Perm (Fin 42))⁻¹ * M.actHom N k) := by
    intro y hy
    obtain ⟨z, hz⟩ := M.e.surjective ⟨y, hy⟩
    have hzy : (M.e z : Equiv.Perm (Fin 42)) = y := congrArg Subtype.val hz
    have h1 := M.actHom_spec N k z
    have h2 : MulAut.conjNormal (H := N) k z = ⟨k, hk⟩ * z * ⟨k, hk⟩⁻¹ := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      rfl
    simp only [h2, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hzy] at h1
    generalize (M.e ⟨k, hk⟩ : Equiv.Perm (Fin 42)) = τ at h1 ⊢
    generalize M.actHom N k = σ at h1 ⊢
    calc (τ⁻¹ * σ) * y = τ⁻¹ * (σ * y * σ⁻¹) * σ := by group
      _ = τ⁻¹ * (τ * y * τ⁻¹) * σ := by rw [← h1]
      _ = y * (τ⁻¹ * σ) := by group
  have hone : (M.e ⟨k, hk⟩ : Equiv.Perm (Fin 42))⁻¹ * M.actHom N k = 1 :=
    M.centralizer_trivial (M.A.mul_mem (M.A.inv_mem hτA) hσA) hcomm
  calc M.actHom N k = (M.e ⟨k, hk⟩ : Equiv.Perm (Fin 42)) *
        ((M.e ⟨k, hk⟩ : Equiv.Perm (Fin 42))⁻¹ * M.actHom N k) := by group
    _ = (M.e ⟨k, hk⟩ : Equiv.Perm (Fin 42)) := by rw [hone, mul_one]

variable [Finite H]

theorem l34_facts
    (T : Sylow 2 H) (K : Subgroup H) [K.Normal]
    (hcen : centralizer (K : Set H) = ⊥) (e : ↥K ≃* QP.originalSubgroup)
    (x : H) (hx2 : x * x = 1) (hxK : x ∉ K) (hxT : x ∈ (T : Subgroup H))
    (h9 : 9 ∣ Nat.card ↥(centralizer ({x} : Set H) ⊓ K)) :
    Nat.card ↥((T : Subgroup H) ⊓ K) = 64 ∧
      centralizer (((T : Subgroup H) ⊓ K : Subgroup H) : Set H) ≤ (T : Subgroup H) ⊓ K ∧
      (∃ y ∈ normalizer (((T : Subgroup H) ⊓ K : Subgroup H) : Set H),
        ∀ z ∈ (T : Subgroup H) ⊓ K, y * z * y⁻¹ = z → z = 1) ∧
      ∀ h : H, ⁅h, x⁆ ∈ K := by
  classical
  obtain ⟨M, hMP, hMA⟩ := autModel e
  set P : Subgroup H := (T : Subgroup H) ⊓ K with hPdef
  have hPK : P ≤ K := inf_le_right
  set ψ₀ : H →* Equiv.Perm (Fin 42) := M.actHom K with hψ₀def
  have hψ₀inj : Function.Injective ψ₀ := M.actHom_injective K hcen
  have hψ₀A : ∀ h : H, ψ₀ h ∈ QA.originalSubgroup := fun h => by
    rw [← hMA]
    exact M.actHom_mem K h
  have hMP' : ∀ g : Equiv.Perm (Fin 42), g ∈ M.P → g ∈ QP.originalSubgroup := fun g hg => by
    rw [← hMP]
    exact hg
  have hMP'' : ∀ g : Equiv.Perm (Fin 42), g ∈ QP.originalSubgroup → g ∈ M.P := fun g hg => by
    rw [hMP]
    exact hg
  have hψ₀K : ∀ (k : H) (hk : k ∈ K), ψ₀ k = (M.e ⟨k, hk⟩ : Equiv.Perm (Fin 42)) :=
    fun k hk => actHom_eq_e M (fun g hg => by rw [hMA]; exact P_le_A (hMP' g hg)) k hk
  have hKcard : Nat.card ↥K = 20160 := by
    rw [Nat.card_congr e.toEquiv, card_group QP QP_ok, QP_valid.2]
  have hPcard : Nat.card ↥P = 64 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let PK : Sylow 2 ↥K := CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal T K
    have hPK' : (PK : Subgroup ↥K).map K.subtype = P := by
      rw [show (PK : Subgroup ↥K) = (T : Subgroup H).comap K.subtype from
        CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal_coe T K]
      rw [Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype]
    have h1 : Nat.card ↥P = Nat.card (PK : Subgroup ↥K) := by
      rw [← hPK', Subgroup.card_map_of_injective K.subtype_injective]
    rw [h1, Sylow.card_eq_multiplicity PK, hKcard]
    have : (20160 : ℕ).factorization 2 = 6 := by
      have h : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
      rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]
    rw [this]
    norm_num
  have hSle : P.map ψ₀ ≤ QP.originalSubgroup := by
    rintro _ ⟨p, hp, rfl⟩
    rw [hψ₀K p (hPK hp)]
    exact hMP' _ (M.e ⟨p, hPK hp⟩).2
  have hScard : Nat.card (P.map ψ₀) = 64 := by
    rw [Subgroup.card_map_of_injective hψ₀inj, hPcard]
  obtain ⟨q, hqP, hq⟩ := exists_conj_S0 (P.map ψ₀) hSle hScard
  have hqA : q ∈ QA.originalSubgroup := P_le_A hqP
  set ψ : H →* Equiv.Perm (Fin 42) := (MulAut.conj q).toMonoidHom.comp ψ₀ with hψdef
  have hψapp : ∀ h : H, ψ h = q * ψ₀ h * q⁻¹ := fun h => rfl
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply hψ₀inj
    have h1 : q * ψ₀ a * q⁻¹ = q * ψ₀ b * q⁻¹ := by
      rw [← hψapp, ← hψapp]
      exact hab
    simpa using h1
  have hψA : ∀ h : H, ψ h ∈ QA.originalSubgroup := fun h => by
    rw [hψapp]
    exact QA.originalSubgroup.mul_mem (QA.originalSubgroup.mul_mem hqA (hψ₀A h))
      (QA.originalSubgroup.inv_mem hqA)
  have hψK : ∀ k : H, k ∈ K → ψ k ∈ QP.originalSubgroup := by
    intro k hk
    rw [hψapp, hψ₀K k hk]
    have hτ : (M.e ⟨k, hk⟩ : Equiv.Perm (Fin 42)) ∈ QP.originalSubgroup :=
      hMP' _ (M.e ⟨k, hk⟩).2
    exact QP.originalSubgroup.mul_mem (QP.originalSubgroup.mul_mem hqP hτ)
      (QP.originalSubgroup.inv_mem hqP)
  have hψsurj : ∀ y ∈ QP.originalSubgroup, ∃ k : H, k ∈ K ∧ ψ k = y := by
    intro y hy
    have hy' : q⁻¹ * y * q ∈ M.P := hMP'' _ (QP.originalSubgroup.mul_mem
      (QP.originalSubgroup.mul_mem (QP.originalSubgroup.inv_mem hqP) hy) hqP)
    obtain ⟨z, hz⟩ := M.e.surjective ⟨q⁻¹ * y * q, hy'⟩
    refine ⟨(z : H), z.2, ?_⟩
    rw [hψapp, hψ₀K (z : H) z.2]
    have : (M.e ⟨(z : H), z.2⟩ : Equiv.Perm (Fin 42)) = q⁻¹ * y * q := by
      have := congrArg Subtype.val hz
      simpa using this
    rw [this]
    group
  have hψP : P.map ψ = S0 := by
    rw [← hq]
    exact (Subgroup.map_map _ _ _).symm
  refine ⟨hPcard, ?_, ?_, ?_⟩
  ·
    intro c hc
    have hc' := Subgroup.mem_centralizer_iff.mp hc
    have h1 : ψ c ∈ S0 := by
      refine cent_le_S0 (ψ c) (hψA c) ?_
      intro s hs
      rw [← hψP] at hs
      obtain ⟨p, hp, rfl⟩ := hs
      rw [← map_mul, ← map_mul, hc' p hp]
    rw [← hψP] at h1
    obtain ⟨p, hp, hpc⟩ := h1
    rw [← hψinj hpc]
    exact hp
  ·
    obtain ⟨k, hkK, hk⟩ := hψsurj y0 y0_mem
    have hconj : ∀ z ∈ P, k * z * k⁻¹ ∈ P ∧ ψ (k * z * k⁻¹) = y0 * ψ z * y0⁻¹ := by
      intro z hz
      have h1 : ψ (k * z * k⁻¹) = y0 * ψ z * y0⁻¹ := by rw [map_mul, map_mul, map_inv, hk]
      have h2 : y0 * ψ z * y0⁻¹ ∈ S0 := y0_norm _ (by rw [← hψP]; exact ⟨z, hz, rfl⟩)
      rw [← hψP] at h2
      obtain ⟨p, hp, hpz⟩ := h2
      have : k * z * k⁻¹ = p := hψinj (by rw [h1, hpz])
      exact ⟨by rw [this]; exact hp, h1⟩
    refine ⟨k, mem_normalizer_of_conj_mem P k (fun z hz => (hconj z hz).1), ?_⟩
    intro z hz hkz
    have h1 := (hconj z hz).2
    rw [hkz] at h1
    have h2 : y0 * ψ z = ψ z * y0 := by
      rw [← mul_inv_eq_iff_eq_mul]
      exact h1.symm
    have h3 : ψ z ∈ S0 := by rw [← hψP]; exact ⟨z, hz, rfl⟩
    exact hψinj (by rw [y0_free _ h3 h2, map_one])
  ·
    obtain ⟨g, hgdef⟩ : ∃ g : Equiv.Perm (Fin 42), g = ψ x := ⟨_, rfl⟩
    have hg : g ∈ QA.originalSubgroup := hgdef ▸ hψA x
    have hg2 : g ^ 2 = 1 := by rw [pow_two, hgdef, ← map_mul, hx2, map_one]
    have hgP : g ∉ QP.originalSubgroup := by
      intro hgQ
      obtain ⟨k, hkK, hk⟩ := hψsurj g hgQ
      exact hxK (hψinj (hk.trans hgdef) ▸ hkK)
    have hnorm : ∀ s ∈ S0, g * s * g⁻¹ ∈ S0 := by
      intro s hs
      rw [← hψP] at hs ⊢
      obtain ⟨p, hp, rfl⟩ := hs
      refine ⟨x * p * x⁻¹, ⟨(T : Subgroup H).mul_mem ((T : Subgroup H).mul_mem hxT hp.1)
        ((T : Subgroup H).inv_mem hxT), ?_⟩, ?_⟩
      · exact Subgroup.Normal.conj_mem inferInstance p hp.2 x
      · rw [hgdef, map_mul, map_mul, map_inv]
    have hcentcard : Nat.card ↥(centralizer ({x} : Set H) ⊓ K) =
        Nat.card ↥(QP.originalSubgroup ⊓ centralizer ({g} : Set (Equiv.Perm (Fin 42)))) := by
      have hmap : (centralizer ({x} : Set H) ⊓ K).map ψ =
          QP.originalSubgroup ⊓ centralizer ({g} : Set (Equiv.Perm (Fin 42))) := by
        ext y
        constructor
        · rintro ⟨c, hc, rfl⟩
          refine Subgroup.mem_inf.2 ⟨hψK c hc.2, ?_⟩
          rw [Subgroup.mem_centralizer_singleton_iff]
          have := Subgroup.mem_centralizer_singleton_iff.1 hc.1
          rw [hgdef, ← map_mul, ← map_mul, this]
        · intro hy
          obtain ⟨hyP, hyC⟩ := Subgroup.mem_inf.1 hy
          obtain ⟨k, hkK, hk⟩ := hψsurj y hyP
          refine ⟨k, Subgroup.mem_inf.2 ⟨?_, hkK⟩, hk⟩
          rw [Subgroup.mem_centralizer_singleton_iff]
          have := Subgroup.mem_centralizer_singleton_iff.1 hyC
          rw [← hk, hgdef, ← map_mul, ← map_mul] at this
          exact hψinj this
      rw [← hmap, Subgroup.card_map_of_injective hψinj]
    have h9' : 9 ∣ Nat.card ↥(QP.originalSubgroup ⊓
        centralizer ({g} : Set (Equiv.Perm (Fin 42)))) := by
      rw [← hcentcard]
      exact h9
    intro h
    have hc := central_all g hg hg2 hgP hnorm h9' (ψ h) (hψA h)
    have hcomm : ψ ⁅h, x⁆ = ψ h * g * (ψ h)⁻¹ * g⁻¹ := by
      simp only [commutatorElement_def, map_mul, map_inv, hgdef]
    rw [← hcomm] at hc
    obtain ⟨k, hkK, hk⟩ := hψsurj _ hc
    have : k = ⁅h, x⁆ := hψinj hk
    rw [← this]
    exact hkK

end CFSG.GH74.Uniqueness.SU.K.R4.L34M
