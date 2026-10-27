module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallE
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33C

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.apply_eq_of_mem_oddCore (hρ : IsPermAction θ ρ) [Finite X] {a : X}
    (ha : a ∈ normalizer (M : Set X)) (ha2 : a * a = 1) {Y : Subgroup X}
    (hYN : Y ≤ normalizer (M : Set X))
    (hYO : Y ≤ (pPrimeCore 2 (centralizer ({a} : Set X))).map
      (centralizer ({a} : Set X)).subtype) {y : X} (hy : y ∈ Y) :
    ∀ v ∈ (ρ ⟨a, ha⟩).support, ρ ⟨y, hYN hy⟩ v = v := by
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
  have hNle : N ≤ fixAlt σ := le_fixAlt_of_odd_normal_centralizer hσ2 hNodd hNc hNn
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
  have hcommN : ∀ b : alternatingGroup (Fin r), (b : Perm (Fin r)) * σ = σ * b →
      ∀ w ∈ σ.support, (ρy * (b : Perm (Fin r)) * ρy⁻¹ * (b : Perm (Fin r))⁻¹) w = w := by
    intro b hb w hw
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
    have hπzN : π z ∈ fixAlt σ := hNle ⟨z, hzK, rfl⟩
    have hπz : ((π z : alternatingGroup (Fin r)) : Perm (Fin r)) =
        ρy * (b : Perm (Fin r)) * ρy⁻¹ * (b : Perm (Fin r))⁻¹ := by
      have h1 := hρ ⟨y, hyN⟩ xb
      rw [hzdef, map_mul, map_inv, hπ, hπ, Subgroup.coe_mul, Subgroup.coe_inv, h1, hxbθ]
    rw [mem_fixAlt] at hπzN
    rw [← hπz]
    exact Perm.notMem_support.mp fun h => Finset.mem_compl.mp (hπzN h) hw
  have hσσ : ∀ v, σ (σ v) = v := fun v => by rw [← Perm.mul_apply, hσ2, Perm.one_apply]
  have hρyinv : ∀ v, σ v = v → σ (ρy⁻¹ v) = ρy⁻¹ v := by
    intro v hv
    have h1 : ρy⁻¹ * σ = σ * ρy⁻¹ := by
      calc ρy⁻¹ * σ = ρy⁻¹ * (σ * ρy) * ρy⁻¹ := by group
        _ = ρy⁻¹ * (ρy * σ) * ρy⁻¹ := by rw [hyc]
        _ = σ * ρy⁻¹ := by group
    rw [← Perm.mul_apply, ← h1, Perm.mul_apply, hv]
  have hpairs : ∀ x z : Fin r, σ x ≠ x → σ z ≠ z → z ≠ x → z ≠ σ x →
      ρy * (swap x (σ x) * swap z (σ z)) = (swap x (σ x) * swap z (σ z)) * ρy := by
    intro x z hx hz hzx hzσx
    set b₀ := swap x (σ x) * swap z (σ z) with hb₀
    have hbA : b₀ ∈ alternatingGroup (Fin r) := by
      rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (Ne.symm hx),
        Perm.sign_swap (Ne.symm hz)]
      rfl
    have hbσ : b₀ * σ = σ * b₀ := by
      rw [mul_assoc, swap_mul_comm_of_involution hσ2 z, ← mul_assoc,
        swap_mul_comm_of_involution hσ2 x, mul_assoc]
    have hb₀w : ∀ u, σ u = u → b₀ u = u := by
      intro u hu
      have hux : u ≠ x := fun h => hx (h ▸ hu)
      have huσx : u ≠ σ x := by
        intro h
        have h1 := hu
        rw [h, hσσ] at h1
        exact hx h1.symm
      have huz : u ≠ z := fun h => hz (h ▸ hu)
      have huσz : u ≠ σ z := by
        intro h
        have h1 := hu
        rw [h, hσσ] at h1
        exact hz h1.symm
      rw [hb₀, Perm.mul_apply, swap_apply_of_ne_of_ne huz huσz, swap_apply_of_ne_of_ne hux huσx]
    have hn1 : ∀ w, (ρy * b₀ * ρy⁻¹ * b₀⁻¹) w = w := by
      intro w
      by_cases hw : w ∈ σ.support
      · exact hcommN ⟨b₀, hbA⟩ hbσ w hw
      · have hσw : σ w = w := Perm.notMem_support.mp hw
        have hb₀iw : b₀⁻¹ w = w := by
          rw [Perm.inv_eq_iff_eq]
          exact (hb₀w w hσw).symm
        rw [Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, hb₀iw, hb₀w _ (hρyinv w hσw),
          ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
    have hn : ρy * b₀ * ρy⁻¹ * b₀⁻¹ = 1 := Equiv.ext hn1
    calc ρy * b₀ = (ρy * b₀ * ρy⁻¹ * b₀⁻¹) * b₀ * ρy := by group
      _ = b₀ * ρy := by rw [hn, one_mul]
  exact fun v hv => apply_eq_of_odd_commute_pairs hσ2 hyc hyodd hpairs hv

theorem apply_eq_of_mem_cak_of_image [Finite X] {Je : Subgroup X}
    (hJeN : Je ≤ normalizer (M : Set X)) {τ : Perm (Fin r)} (hτ4 : 4 ≤ r - τ.support.card)
    (ψ : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* fixAlt τ)
    (hψ : ∀ x : ↥Je, (((ψ (x : ↥Je ⧸ pPrimeCore 2 ↥Je) : fixAlt τ) :
      alternatingGroup (Fin r)) : Perm (Fin r)) = ρ ⟨x, hJeN x.2⟩)
    {c : X} (hcN : c ∈ normalizer (M : Set X))
    (hcK : c ∈ UnbalancedLayer.coreActionKernel Je) :
    ∀ v ∉ τ.support, ρ ⟨c, hcN⟩ v = v := by
  classical
  set g := ρ ⟨c, hcN⟩ with hgdef
  have hρO : ∀ o : ↥Je, o ∈ pPrimeCore 2 ↥Je → ρ ⟨o, hJeN o.2⟩ = 1 := by
    intro o ho
    rw [← hψ o, (QuotientGroup.eq_one_iff o).mpr ho, map_one]
    rfl
  have hgx : ∀ x : ↥Je, g * ρ ⟨x, hJeN x.2⟩ = ρ ⟨x, hJeN x.2⟩ * g := by
    intro x
    have hcinv := inv_mem hcK
    obtain ⟨-, hcK'⟩ := UnbalancedLayer.mem_coreActionKernel.mp hcinv
    obtain ⟨o, ho, hoeq⟩ := hcK' x x.2
    rw [inv_inv] at hoeq
    have hoeq' : (o : X) = (x : X)⁻¹ * c * x * c⁻¹ := hoeq
    have hcx : c * x * c⁻¹ = (x : X) * o := by
      rw [hoeq']
      group
    have h1 : (⟨c, hcN⟩ : ↥(normalizer (M : Set X))) * ⟨x, hJeN x.2⟩ * ⟨c, hcN⟩⁻¹ =
        ⟨x, hJeN x.2⟩ * ⟨o, hJeN o.2⟩ := Subtype.ext hcx
    have h2 := congrArg ρ h1
    rw [map_mul, map_mul, map_inv, map_mul, hρO o ho, mul_one] at h2
    calc g * ρ ⟨x, hJeN x.2⟩ = (g * ρ ⟨x, hJeN x.2⟩ * g⁻¹) * g := by group
      _ = ρ ⟨x, hJeN x.2⟩ * g := by rw [hgdef, h2]
  have hgF : ∀ b ∈ fixAlt τ, g * (b : Perm (Fin r)) = (b : Perm (Fin r)) * g := by
    intro b hb
    obtain ⟨q, hq⟩ := ψ.surjective ⟨b, hb⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (b : Perm (Fin r)) = ρ ⟨x, hJeN x.2⟩ := by
      rw [← hψ x, hq]
    rw [h1]
    exact hgx x
  exact fun v hv => apply_eq_of_commute_fixAlt hτ4 hgF hv

end CFSG.ComponentClassification.SolMax
