module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33A

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.le_coreActionKernel_of_fix (hρ : IsPermAction θ ρ) [Finite X] {a : X}
    (ha : a ∈ normalizer (M : Set X)) (ha2 : a * a = 1)
    (h5 : 5 ≤ r - (ρ ⟨a, ha⟩).support.card) {Y : Subgroup X} (hYN : Y ≤ normalizer (M : Set X))
    (hYO : Y ≤ (pPrimeCore 2 (centralizer ({a} : Set X))).map
      (centralizer ({a} : Set X)).subtype) :
    Y ≤ UnbalancedLayer.coreActionKernel M := by
  classical
  set σ := ρ ⟨a, ha⟩ with hσdef
  set Ca : Subgroup X := centralizer ({a} : Set X) with hCadef
  set Oa := (pPrimeCore 2 ↥Ca).map Ca.subtype with hOadef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul]
    have : (⟨a, ha⟩ : ↥(normalizer (M : Set X))) * ⟨a, ha⟩ = 1 := Subtype.ext ha2
    rw [this, map_one]
  have hOaodd : Odd (Nat.card Oa) := by
    rw [hOadef, card_map_of_injective Ca.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOaCa : Oa ≤ Ca := map_subtype_le _
  have hOanorm : ∀ g ∈ Ca, ∀ z ∈ Oa, g * z * g⁻¹ ∈ Oa := fun g hg z hz =>
    (mem_normalizer_iff.mp (Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥Ca) hg) z).mp hz
  set π : ↥M →* alternatingGroup (Fin r) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥M)) with hπdef
  have hπ : ∀ x : ↥M, π x = θ (x : ↥M ⧸ pPrimeCore 2 ↥M) := fun _ => rfl
  have hconj : ∀ x : ↥M, (x : X) ∈ Ca → (π x : Perm (Fin r)) * σ = σ * π x := by
    intro x hx
    have hxa : M.normalizerMonoidHom ⟨a, ha⟩ x = x := by
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_apply_coe]
      change a * (x : X) * a⁻¹ = x
      have h1 : (x : X) * a = a * x := mem_centralizer_singleton_iff.mp hx
      rw [← h1]
      group
    have h1 := hρ ⟨a, ha⟩ x
    rw [hxa] at h1
    rw [hπ]
    calc (θ (x : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r)) * σ =
        (σ * (θ (x : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r)) * σ⁻¹) * σ := by rw [← h1]
      _ = σ * (θ (x : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r)) := by group
  set K : Subgroup ↥M := (Ca ⊓ Oa).subgroupOf M with hKdef
  set N : Subgroup (alternatingGroup (Fin r)) := K.map π with hNdef
  have hNodd : Odd (Nat.card N) := by
    have h1 : Nat.card N ∣ Nat.card K := K.card_map_dvd π
    let f : K →* Oa :=
      { toFun := fun x => ⟨((x : ↥M) : X), (mem_subgroupOf.mp x.2).2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun x y h => by
      have h' : ((x : ↥M) : X) = ((y : ↥M) : X) := congrArg (fun z : Oa => (z : X)) h
      exact Subtype.ext (Subtype.ext h')
    exact (hOaodd.of_dvd_nat (Subgroup.card_dvd_of_injective f hf)).of_dvd_nat h1
  have hNc : ∀ g ∈ N, (g : Perm (Fin r)) * σ = σ * g := by
    rintro _ ⟨k, hk, rfl⟩
    exact hconj k (mem_subgroupOf.mp hk).1
  have hNn : ∀ b : alternatingGroup (Fin r), (b : Perm (Fin r)) * σ = σ * b →
      ∀ g ∈ N, b * g * b⁻¹ ∈ N := by
    rintro b hb _ ⟨k, hk, rfl⟩
    obtain ⟨xb, hxbCa, hxbθ⟩ := hρ.exists_lift ha ha2 hb
    have hk' := mem_subgroupOf.mp hk
    refine ⟨xb * k * xb⁻¹, ?_, ?_⟩
    · refine mem_subgroupOf.mpr ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_inf.mpr
        ⟨mul_mem (mul_mem hxbCa hk'.1) (inv_mem hxbCa), hOanorm _ hxbCa _ hk'.2⟩
    · rw [map_mul, map_mul, map_inv, hπ xb, hxbθ]
  have hN : N = ⊥ := eq_bot_of_odd_normal_centralizer hσ2 h5 hNodd hNc hNn
  intro y hy
  have hyN := hYN hy
  have hyOa := hYO hy
  have hyCa : y ∈ Ca := hOaCa hyOa
  set ρy := ρ ⟨y, hyN⟩ with hρydef
  have hyodd : Odd (orderOf ρy) := by
    have h1 : orderOf ρy ∣ orderOf (⟨y, hyN⟩ : ↥(normalizer (M : Set X))) := orderOf_map_dvd ρ _
    rw [Subgroup.orderOf_mk] at h1
    have h2 : orderOf y ∣ Nat.card Oa := by
      have := orderOf_dvd_natCard (⟨y, hyOa⟩ : Oa)
      rwa [Subgroup.orderOf_mk] at this
    exact (hOaodd.of_dvd_nat h2).of_dvd_nat h1
  have hyc : ρy * σ = σ * ρy := by
    rw [hρydef, hσdef, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp hyCa
  have hcomm' : ∀ b : alternatingGroup (Fin r), (b : Perm (Fin r)) * σ = σ * b →
      ρy * (b : Perm (Fin r)) = (b : Perm (Fin r)) * ρy := by
    intro b hb
    obtain ⟨xb, hxbCa, hxbθ⟩ := hρ.exists_lift ha ha2 hb
    set z : ↥M := M.normalizerMonoidHom ⟨y, hyN⟩ xb * xb⁻¹ with hzdef
    have hzK : z ∈ K := by
      rw [mem_subgroupOf]
      have hz : (z : X) = y * xb * y⁻¹ * (xb : X)⁻¹ := by
        rw [hzdef, Subgroup.coe_mul, normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inv]
      rw [hz]
      refine Subgroup.mem_inf.mpr
        ⟨mul_mem (mul_mem (mul_mem hyCa hxbCa) (inv_mem hyCa)) (inv_mem hxbCa), ?_⟩
      have h1 : (xb : X) * y⁻¹ * (xb : X)⁻¹ ∈ Oa := hOanorm _ hxbCa _ (inv_mem hyOa)
      have h2 := mul_mem hyOa h1
      simpa [mul_assoc] using h2
    have hπz : π z = 1 := by
      have h1 : π z ∈ N := ⟨z, hzK, rfl⟩
      rw [hN] at h1
      exact h1
    rw [hzdef, map_mul, map_inv, hπ, hπ] at hπz
    have h2 : θ ((M.normalizerMonoidHom ⟨y, hyN⟩ xb : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) =
        θ (xb : ↥M ⧸ pPrimeCore 2 ↥M) := mul_inv_eq_one.mp hπz
    have h1 := hρ ⟨y, hyN⟩ xb
    rw [h2, hxbθ] at h1
    calc ρy * (b : Perm (Fin r)) = (ρy * (b : Perm (Fin r)) * ρy⁻¹) * ρy := by group
      _ = (b : Perm (Fin r)) * ρy := by rw [← h1]
  have hcomm : ∀ b ∈ fixAlt σ, ρy * (b : Perm (Fin r)) = (b : Perm (Fin r)) * ρy :=
    fun b hb => hcomm' b (commute_of_mem_fixAlt hb)
  have hpairs : ∀ x z : Fin r, σ x ≠ x → σ z ≠ z → z ≠ x → z ≠ σ x →
      ρy * (swap x (σ x) * swap z (σ z)) = (swap x (σ x) * swap z (σ z)) * ρy := by
    intro x z hx hz hzx hzσx
    have hbA : swap x (σ x) * swap z (σ z) ∈ alternatingGroup (Fin r) := by
      rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (Ne.symm hx),
        Perm.sign_swap (Ne.symm hz)]
      rfl
    have hbσ : (swap x (σ x) * swap z (σ z)) * σ = σ * (swap x (σ x) * swap z (σ z)) := by
      rw [mul_assoc, swap_mul_comm_of_involution hσ2 z, ← mul_assoc,
        swap_mul_comm_of_involution hσ2 x, mul_assoc]
    exact hcomm' ⟨_, hbA⟩ hbσ
  have hfix : ∀ x ∈ σ.support, ρy x = x := fun x hx =>
    apply_eq_of_odd_commute_pairs hσ2 hyc hyodd hpairs hx
  have hρy : ρy = 1 := eq_one_of_commute_fixAlt hfix (by omega) hcomm
  exact hρ.mem_coreActionKernel hyN hρy

end CFSG.ComponentClassification.SolMax
