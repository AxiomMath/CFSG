module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR29
import CFSG.GH74.GLS.C3.Layer1.Th2HYGrp
import CFSG.GH74.GLS.IVK.Proofs2.GHInvSym

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK.A7
open scoped commutatorElement

theorem dihedral_center_unique {G : Type} [Group G] {P : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (φ : ↥P ≃* DihedralGroup (2 ^ (n - 1))) :
    ∃ z ∈ P, orderOf z = 2 ∧ (∀ p ∈ P, z * p = p * z) ∧
      ∀ u ∈ P, (∀ p ∈ P, u * p = p * u) → u = 1 ∨ u = z := by
  have hk4 : 4 ≤ 2 ^ (n - 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkev : Even (2 ^ (n - 1)) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
  set k : ℕ := 2 ^ (n - 1) with hk
  set d₀ : DihedralGroup k := DihedralGroup.r ((k / 2 : ℕ) : ZMod k) with hd₀
  have hd₀c : ∀ x : DihedralGroup k, d₀ * x = x * d₀ := by
    intro x
    have hmem : d₀ ∈ Subgroup.center (DihedralGroup k) := by
      rw [DihedralGroup.center_eq_closure_of_even_ne_two hkev (by omega)]
      exact Subgroup.mem_zpowers _
    exact (Subgroup.mem_center_iff.1 hmem x).symm
  have hd₀o : orderOf d₀ = 2 := by
    rw [hd₀, DihedralGroup.orderOf_r]
    obtain ⟨m, hm⟩ := hkev
    have hm0 : 0 < m := by omega
    have hdiv : k / 2 = m := by omega
    rw [hdiv, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), hm]
    have : Nat.gcd (m + m) m = m := Nat.gcd_eq_right ⟨2, by ring⟩
    rw [this]
    exact Nat.div_eq_of_eq_mul_left hm0 (by ring)
  have hzP : (φ.symm d₀).1 ∈ P := (φ.symm d₀).2
  have hz2 : orderOf (φ.symm d₀).1 = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hd₀o
  have hzc : ∀ p ∈ P, (φ.symm d₀).1 * p = p * (φ.symm d₀).1 := by
    intro p hp
    have := hd₀c (φ ⟨p, hp⟩)
    have h2 := congrArg φ.symm this
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h2
    exact congrArg Subtype.val h2
  exact ⟨_, hzP, hz2, hzc, (central_of_dihedral hn φ hzP hz2 hzc).1⟩


theorem Z7_core (Eb Pb : Subgroup (Perm (Fin 7))) (hE4 : Nat.card ↥Eb = 4)
    {n : ℕ} (hn : 3 ≤ n) (φ : ↥Pb ≃* DihedralGroup (2 ^ (n - 1)))
    (hcomm : ∀ p ∈ Pb, ∀ e ∈ Eb, p * e = e * p) :
    ∃ f ∈ Eb, f.IsSwap := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z₀, hz₀P, hz₀2, hz₀c, hz₀u⟩ := dihedral_center_unique hn φ
  have hPcard : Nat.card ↥Pb = 2 ^ n := by
    have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card, ← pow_succ']
    congr 1
    omega
  have hEn : Eb ≤ normalizer (Pb : Set (Perm (Fin 7))) := fun e he =>
    Subgroup.centralizer_le_normalizer (Pb : Set (Perm (Fin 7)))
      (Subgroup.mem_centralizer_iff.2 (fun p hp => hcomm p hp e he))
  have hprod := Th2.HY.card_sup_mul_card_inf_of_le_normalizer hEn
  rw [hE4, hPcard] at hprod
  have hinf_le : Eb ⊓ Pb ≤ zpowers z₀ := by
    intro x hx
    rcases hz₀u x hx.2 (fun p hp => (hcomm p hp x hx.1).symm) with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers z₀
  have hinf_card : Nat.card ↥(Eb ⊓ Pb) ≤ 2 := by
    have := Subgroup.card_le_of_le hinf_le
    rwa [Nat.card_zpowers, hz₀2] at this
  have hinf_pos : 0 < Nat.card ↥(Eb ⊓ Pb) := Nat.card_pos
  have hRdvd : Nat.card ↥(Eb ⊔ Pb) ∣ 2 ^ (2 + n) := by
    refine ⟨Nat.card ↥(Eb ⊓ Pb), ?_⟩
    rw [pow_add]
    nlinarith [hprod]
  obtain ⟨j, hj, hRj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hRdvd
  have hj4 : j ≤ 4 := by
    by_contra hj5
    push Not at hj5
    have h1 : 2 ^ 5 ∣ 2 ^ j := Nat.pow_dvd_pow 2 hj5
    have h2 : Nat.card ↥(Eb ⊔ Pb) ∣ Nat.card (Perm (Fin 7)) := Subgroup.card_subgroup_dvd_card _
    rw [hRj] at h2
    have h3 : (2 : ℕ) ^ 5 ∣ Nat.card (Perm (Fin 7)) := h1.trans h2
    rw [card_S7] at h3
    norm_num at h3
  have hn3 : n = 3 := by
    by_contra hne
    have hn4 : 4 ≤ n := by omega
    have h1 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
    rw [hRj] at hprod
    have h2 : 2 ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hj4
    nlinarith [hprod, hinf_card, hinf_pos]
  subst hn3
  have hinf2 : Nat.card ↥(Eb ⊓ Pb) = 2 := by
    rw [hRj] at hprod
    have h2 : 2 ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hj4
    interval_cases hc : Nat.card ↥(Eb ⊓ Pb)
    · omega
    · omega
  have hRcard : Nat.card ↥(Eb ⊔ Pb) = 16 := by
    rw [hinf2] at hprod
    omega
  have hRsyl : Nat.card ↥(Eb ⊔ Pb) = 2 ^ (Nat.card S7).factorization 2 := by
    rw [hRcard, factorization_S7]
    norm_num
  let T : Sylow 2 S7 := Sylow.ofCard (Eb ⊔ Pb) hRsyl
  obtain ⟨f, hf2, hfct, hfT, -, hfc, hsup⟩ := exists_split T
  have hfR : f ∈ Eb ⊔ Pb := hfT
  have hsup' : (Eb ⊔ Pb) ⊓ alternatingGroup (Fin 7) ⊔ zpowers f = Eb ⊔ Pb := hsup
  have hfcen : ∀ x ∈ Eb ⊔ Pb, f * x = x * f := by
    intro x hx
    rw [← hsup'] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_right (show Commute a f from hfc a ha) k).eq) hx
    have hfa : f * a = a * f := (hfc a ha).symm
    have hfb : f * b = b * f := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (Commute.refl f) k).eq
    calc f * (a * b) = (f * a) * b := by group
      _ = (a * f) * b := by rw [hfa]
      _ = a * (f * b) := by group
      _ = a * (b * f) := by rw [hfb]
      _ = a * b * f := by group
  obtain ⟨e, he, p, hp, hfep⟩ := exists_mul_of_mem_sup_of_commute
    (fun e he p hp => (hcomm p hp e he).symm) hfR
  have hpe : p = e⁻¹ * f := by rw [hfep]; group
  have hecomm : ∀ q ∈ Pb, e⁻¹ * q = q * e⁻¹ := by
    intro q hq
    calc e⁻¹ * q = e⁻¹ * (q * e) * e⁻¹ := by group
      _ = e⁻¹ * (e * q) * e⁻¹ := by rw [hcomm q hq e he]
      _ = q * e⁻¹ := by group
  have hpc : ∀ q ∈ Pb, p * q = q * p := by
    intro q hq
    calc p * q = e⁻¹ * (f * q) := by rw [hpe]; group
      _ = e⁻¹ * (q * f) := by rw [hfcen q (Subgroup.mem_sup_right hq)]
      _ = (e⁻¹ * q) * f := by group
      _ = (q * e⁻¹) * f := by rw [hecomm q hq]
      _ = q * (e⁻¹ * f) := by group
      _ = q * p := by rw [hpe]
  have hinf_eq : Eb ⊓ Pb = zpowers z₀ :=
    Subgroup.eq_of_le_of_card_ge hinf_le (by rw [Nat.card_zpowers, hz₀2, hinf2])
  have hz₀E : z₀ ∈ Eb := by
    have : z₀ ∈ Eb ⊓ Pb := by rw [hinf_eq]; exact Subgroup.mem_zpowers z₀
    exact this.1
  have hpE : p ∈ Eb := by
    rcases hz₀u p hp hpc with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hz₀E
  exact ⟨f, hfep ▸ Eb.mul_mem he hpE, Equiv.Perm.isSwap_iff_cycleType.mpr hfct⟩


section A7Model

variable {X : Type} [Group X]

@[expose] noncomputable def autA7Phi : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective
    (MulAut.conjNormal (H := alternatingGroup (Fin 7)) :
      Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num))

theorem autA7Phi_apply (σ : Perm (Fin 7)) : autA7Phi σ = MulAut.conjNormal σ := rfl

@[expose] noncomputable def autA7Equiv (e : X ≃* alternatingGroup (Fin 7)) :
    MulAut X ≃* Perm (Fin 7) :=
  (MulAut.congr e).trans autA7Phi.symm

theorem autA7Equiv_spec (e : X ≃* alternatingGroup (Fin 7)) (y : MulAut X) (k : X) :
    ((e (y k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      autA7Equiv e y * (e k : Perm (Fin 7)) * (autA7Equiv e y)⁻¹ := by
  have h1 : autA7Phi (autA7Equiv e y) = MulAut.congr e y := autA7Phi.apply_symm_apply _
  rw [autA7Phi_apply] at h1
  have h2 : e (y k) = MulAut.congr e y (e k) := by simp [MulAut.congr_apply]
  rw [h2, ← h1, MulAut.conjNormal_apply]

@[expose] noncomputable def psiA7 (e : X ≃* alternatingGroup (Fin 7)) : X →* Perm (Fin 7) :=
  (alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom

theorem psiA7_injective (e : X ≃* alternatingGroup (Fin 7)) : Function.Injective (psiA7 e) :=
  (Subgroup.subtype_injective _).comp e.injective

theorem fixedSubgroup_map_A7 (e : X ≃* alternatingGroup (Fin 7)) (y : MulAut X) :
    (fixedSubgroup X y).map (psiA7 e) =
      centralizer ({autA7Equiv e y} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := by
  have hψy : ∀ k : X, psiA7 e (y k) = autA7Equiv e y * psiA7 e k * (autA7Equiv e y)⁻¹ :=
    fun k => autA7Equiv_spec e y k
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : y k = k := hk
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, (e k).2⟩
    have := hψy k
    rw [hk'] at this
    calc psiA7 e k * autA7Equiv e y = autA7Equiv e y * psiA7 e k * (autA7Equiv e y)⁻¹ * autA7Equiv e y := by
          rw [← this]
      _ = autA7Equiv e y * psiA7 e k := by group
  · rintro ⟨hxc, hxA⟩
    refine ⟨e.symm ⟨x, hxA⟩, ?_, by simp [psiA7]⟩
    show y (e.symm ⟨x, hxA⟩) = e.symm ⟨x, hxA⟩
    apply psiA7_injective e
    rw [hψy]
    have hx : autA7Equiv e y * x = x * autA7Equiv e y :=
      (Subgroup.mem_centralizer_singleton_iff.1 hxc).symm
    have : psiA7 e (e.symm ⟨x, hxA⟩) = x := by simp [psiA7]
    rw [this]
    calc autA7Equiv e y * x * (autA7Equiv e y)⁻¹ = x * autA7Equiv e y * (autA7Equiv e y)⁻¹ := by rw [hx]
      _ = x := by group

@[expose] noncomputable def fixedSubgroupEquivA7 (e : X ≃* alternatingGroup (Fin 7)) (y : MulAut X) :
    ↥(fixedSubgroup X y) ≃*
      ↥(centralizer ({autA7Equiv e y} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) :=
  (Subgroup.equivMapOfInjective _ (psiA7 e) (psiA7_injective e)).trans
    (MulEquiv.subgroupCongr (fixedSubgroup_map_A7 e y))

end A7Model


theorem autZ_A7 {X : Type} [Group X] [Finite X] (e : X ≃* alternatingGroup (Fin 7))
    (Eb Pb : Subgroup (MulAut X)) (hEel : CFSG.IsElementaryAbelian 2 ↥Eb) (hE4 : Nat.card ↥Eb = 4)
    (hsolv : ∀ ε ∈ Eb, ε ≠ 1 → Group.IsSolvable ↥(fixedSubgroup X ε))
    (hdih : ∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥Pb ≃* DihedralGroup (2 ^ (n - 1))))
    (hcomm : ∀ p ∈ Pb, ∀ e ∈ Eb, p * e = e * p) : False := by
  obtain ⟨n, hn3, ⟨φ⟩⟩ := hdih
  obtain ⟨hEc, hEsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hEel
  let θ : MulAut X ≃* Perm (Fin 7) := autA7Equiv e
  have hE4' : Nat.card ↥(Eb.map θ.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective θ.injective]
    exact hE4
  let φ' : ↥(Pb.map θ.toMonoidHom) ≃* DihedralGroup (2 ^ (n - 1)) :=
    (Subgroup.equivMapOfInjective Pb θ.toMonoidHom θ.injective).symm.trans φ
  have hcomm' : ∀ p ∈ Pb.map θ.toMonoidHom, ∀ e' ∈ Eb.map θ.toMonoidHom, p * e' = e' * p := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨e', he', rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hcomm p hp e' he']
  obtain ⟨f, hfE, hfs⟩ := Z7_core (Eb.map θ.toMonoidHom) (Pb.map θ.toMonoidHom) hE4' hn3 φ' hcomm'
  obtain ⟨ε₀, hε₀, rfl⟩ := hfE
  have hfs' : (autA7Equiv e ε₀).IsSwap := hfs
  have hε1 : ε₀ ≠ 1 := by
    intro h1
    have h2 := hfs'.orderOf
    rw [h1, map_one, orderOf_one] at h2
    omega
  have hsolvC := hsolv ε₀ hε₀ hε1
  have hsolvA : Group.IsSolvable ↥(centralizer ({autA7Equiv e ε₀} : Set (Perm (Fin 7))) ⊓
      alternatingGroup (Fin 7)) := by
    have := hsolvC
    exact Group.isSolvable_of_surjective (f := (fixedSubgroupEquivA7 e ε₀).toMonoidHom)
      (fixedSubgroupEquivA7 e ε₀).surjective
  obtain ⟨e5⟩ := IVK.A7.centralizer_A7_swap_equiv hfs'
  have : Group.IsSolvable (Perm (Fin 5)) := by
    have := hsolvA
    exact Group.isSolvable_of_isSolvable_injective (f := e5.symm.toMonoidHom) e5.symm.injective
  exact Equiv.Perm.not_isSolvable_fin_5 this


section U7

@[expose] def W7 (ε σ c : Perm (Fin 7)) : Prop :=
  sign c = 1 ∧ c * ε = ε * c ∧
    (σ * c * σ⁻¹ * c⁻¹) * (σ * c * σ⁻¹ * c⁻¹) = 1 ∧ σ * c * σ⁻¹ * c⁻¹ ≠ 1 ∧
    (σ * c * σ⁻¹ * c⁻¹) * ε = ε * (σ * c * σ⁻¹ * c⁻¹) ∧
    (σ * c * σ⁻¹ * c⁻¹) * σ = σ * (σ * c * σ⁻¹ * c⁻¹) ∧
    σ * c * σ⁻¹ * c⁻¹ ≠ σ ∧ σ * c * σ⁻¹ * c⁻¹ ≠ ε ∧ σ * c * σ⁻¹ * c⁻¹ ≠ ε * σ

theorem conj_eq_iff (g x y : Perm (Fin 7)) : g * x * g⁻¹ = g * y * g⁻¹ ↔ x = y := by
  constructor
  · intro h
    have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using this
  · rintro rfl
    rfl

theorem W7_conj (g ε σ c : Perm (Fin 7)) (h : W7 ε σ c) :
    W7 (g * ε * g⁻¹) (g * σ * g⁻¹) (g * c * g⁻¹) := by
  obtain ⟨hs, hcε, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hu : (g * σ * g⁻¹) * (g * c * g⁻¹) * (g * σ * g⁻¹)⁻¹ * (g * c * g⁻¹)⁻¹ =
      g * (σ * c * σ⁻¹ * c⁻¹) * g⁻¹ := by group
  have hεσ : g * ε * g⁻¹ * (g * σ * g⁻¹) = g * (ε * σ) * g⁻¹ := by group
  unfold W7
  rw [hu, hεσ]
  set u : Perm (Fin 7) := σ * c * σ⁻¹ * c⁻¹ with hu_def
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hs]
    simp [mul_comm]
  · calc g * c * g⁻¹ * (g * ε * g⁻¹) = g * (c * ε) * g⁻¹ := by group
      _ = g * (ε * c) * g⁻¹ := by rw [hcε]
      _ = g * ε * g⁻¹ * (g * c * g⁻¹) := by group
  · calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · intro h
    apply h2
    exact (conj_eq_iff g _ _).1 (by simpa using h)
  · calc g * u * g⁻¹ * (g * ε * g⁻¹) = g * (u * ε) * g⁻¹ := by group
      _ = g * (ε * u) * g⁻¹ := by rw [h3]
      _ = g * ε * g⁻¹ * (g * u * g⁻¹) := by group
  · calc g * u * g⁻¹ * (g * σ * g⁻¹) = g * (u * σ) * g⁻¹ := by group
      _ = g * (σ * u) * g⁻¹ := by rw [h4]
      _ = g * σ * g⁻¹ * (g * u * g⁻¹) := by group
  · intro h
    exact h5 ((conj_eq_iff g _ _).1 h)
  · intro h
    exact h6 ((conj_eq_iff g _ _).1 h)
  · intro h
    exact h7 ((conj_eq_iff g _ _).1 h)


theorem W7_rep1 : W7 1 (swap 0 1) (swap 0 2 * swap 1 3) := by
  unfold W7
  decide +kernel

theorem W7_rep2 : W7 1 (swap 0 1 * swap 2 3) (swap 2 4 * swap 3 5) := by
  unfold W7
  decide +kernel

theorem W7_rep3 : W7 1 (swap 0 1 * swap 2 3 * swap 4 5) (swap 0 1 * swap 3 4) := by
  unfold W7
  decide +kernel

theorem cyc1 : (swap 0 1 : Perm (Fin 7)).cycleType = {2} :=
  Equiv.Perm.isSwap_iff_cycleType.mp ⟨0, 1, by decide, rfl⟩

theorem cyc2 : (swap 0 1 * swap 2 3 : Perm (Fin 7)).cycleType = {2, 2} :=
  Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)

theorem cyc3 : (swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 7)).cycleType = {2, 2, 2} := by
  have hd : Equiv.Perm.Disjoint (swap 0 1 * swap 2 3 : Perm (Fin 7)) (swap 4 5) := by
    intro x
    fin_cases x <;> decide
  rw [hd.cycleType_mul, cyc2, Equiv.Perm.isSwap_iff_cycleType.mp (⟨4, 5, by decide, rfl⟩ : (swap 4 5 : Perm (Fin 7)).IsSwap)]
  rfl

theorem U7_one (σ : Perm (Fin 7)) (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) : ∃ c, W7 1 σ c := by
  have hsq : σ ^ 2 = 1 := by rw [sq]; exact hσ2
  have hct := involution_cycleType σ hsq hσ1
  have key : ∀ (σ₀ c₀ : Perm (Fin 7)), σ₀.cycleType = σ.cycleType → W7 1 σ₀ c₀ → ∃ c, W7 1 σ c := by
    intro σ₀ c₀ hct₀ hW
    obtain ⟨g, hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr hct₀)
    refine ⟨g * c₀ * g⁻¹, ?_⟩
    have := W7_conj g 1 σ₀ c₀ hW
    rw [hg] at this
    simpa using this
  rcases hct with h | h | h
  · exact key _ _ (by rw [h]; exact cyc1) W7_rep1
  · exact key _ _ (by rw [h]; exact cyc2) W7_rep2
  · exact key _ _ (by rw [h]; exact cyc3) W7_rep3


@[expose] def s5Ok (π c : Perm (Fin 5)) : Bool :=
  decide ((π * c * π⁻¹ * c⁻¹) * (π * c * π⁻¹ * c⁻¹) = 1) && decide (π * c * π⁻¹ * c⁻¹ ≠ 1) &&
    decide ((π * c * π⁻¹ * c⁻¹) * π = π * (π * c * π⁻¹ * c⁻¹)) && decide (π * c * π⁻¹ * c⁻¹ ≠ π)

theorem s5_ok_all : ∀ π : Perm (Fin 5), π * π = 1 → π ≠ 1 → ∃ c : Perm (Fin 5), s5Ok π c = true := by
  decide +kernel

theorem s5_comm_witness (π : Perm (Fin 5)) (h1 : π * π = 1) (h2 : π ≠ 1) :
    ∃ c : Perm (Fin 5), (π * c * π⁻¹ * c⁻¹) * (π * c * π⁻¹ * c⁻¹) = 1 ∧ π * c * π⁻¹ * c⁻¹ ≠ 1 ∧
      (π * c * π⁻¹ * c⁻¹) * π = π * (π * c * π⁻¹ * c⁻¹) ∧ π * c * π⁻¹ * c⁻¹ ≠ π := by
  obtain ⟨c, hc⟩ := s5_ok_all π h1 h2
  refine ⟨c, ?_⟩
  simpa [s5Ok, and_assoc] using hc

theorem Phi5_range_eq :
    Phi5.range = centralizer ({swap 5 6} : Set S7) ⊓ alternatingGroup (Fin 7) := by
  have hle : Phi5.range ≤ centralizer ({swap 5 6} : Set S7) ⊓ alternatingGroup (Fin 7) := by
    rintro _ ⟨σ, rfl⟩
    exact Phi5_mem σ
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_centralizer_A7_two swap56_cycleType (by decide +kernel) (by decide +kernel)]
  have : Nat.card Phi5.range = Nat.card (Perm (Fin 5)) :=
    (Nat.card_congr (MonoidHom.ofInjective Phi5_injective).toEquiv).symm
  rw [this]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

theorem Phi5_ne_swap (x : Perm (Fin 5)) : Phi5 x ≠ swap 5 6 := by
  intro h
  have h1 := (Equiv.Perm.mem_alternatingGroup.1 (Phi5_mem x).2)
  rw [h, Perm.sign_swap (by decide)] at h1
  exact absurd h1 (by decide)

theorem Phi5_commutes (x : Perm (Fin 5)) : Phi5 x * swap 5 6 = swap 5 6 * Phi5 x :=
  Subgroup.mem_centralizer_singleton_iff.1 (Phi5_mem x).1

theorem exists_Phi5_decomp (σ : Perm (Fin 7)) (hcomm : σ * swap 5 6 = swap 5 6 * σ) :
    ∃ (π : Perm (Fin 5)) (t : Perm (Fin 7)), (t = 1 ∨ t = swap 5 6) ∧ σ = Phi5 π * t := by
  by_cases hs : sign σ = 1
  · have hmem : σ ∈ Phi5.range := by
      rw [Phi5_range_eq]
      exact ⟨Subgroup.mem_centralizer_singleton_iff.2 hcomm, Equiv.Perm.mem_alternatingGroup.2 hs⟩
    obtain ⟨π, hπ⟩ := hmem
    exact ⟨π, 1, Or.inl rfl, by rw [mul_one]; exact hπ.symm⟩
  · have hs' : sign σ = -1 := by
      rcases Int.units_eq_one_or (sign σ) with h | h
      · exact absurd h hs
      · exact h
    have hmem : σ * swap 5 6 ∈ Phi5.range := by
      rw [Phi5_range_eq]
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, Equiv.Perm.mem_alternatingGroup.2 ?_⟩
      · have h1 : σ * swap 5 6 * swap 5 6 = σ := by rw [mul_assoc, Equiv.swap_mul_self, mul_one]
        have h2 : swap 5 6 * (σ * swap 5 6) = σ := by
          rw [← mul_assoc, ← hcomm, mul_assoc, Equiv.swap_mul_self, mul_one]
        rw [h1, h2]
      · rw [Perm.sign_mul, hs', Perm.sign_swap (by decide)]
        decide
    obtain ⟨π, hπ⟩ := hmem
    refine ⟨π, swap 5 6, Or.inr rfl, ?_⟩
    rw [hπ, mul_assoc, Equiv.swap_mul_self, mul_one]


theorem U7_swap (σ : Perm (Fin 7)) (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) (hσs : σ ≠ swap 5 6)
    (hcomm : σ * swap 5 6 = swap 5 6 * σ) : ∃ c, W7 (swap 5 6) σ c := by
  obtain ⟨π, t, ht, hσ⟩ := exists_Phi5_decomp σ hcomm
  have htc : ∀ x : Perm (Fin 5), t * Phi5 x = Phi5 x * t := by
    intro x
    rcases ht with rfl | rfl
    · simp
    · exact (Phi5_commutes x).symm
  have htt : t * t = 1 := by
    rcases ht with rfl | rfl
    · simp
    · exact Equiv.swap_mul_self _ _
  have hπ2 : π * π = 1 := by
    apply Phi5_injective
    rw [map_mul, map_one]
    have : σ * σ = Phi5 π * Phi5 π := by
      rw [hσ]
      calc Phi5 π * t * (Phi5 π * t) = Phi5 π * (t * Phi5 π) * t := by group
        _ = Phi5 π * (Phi5 π * t) * t := by rw [htc]
        _ = Phi5 π * Phi5 π * (t * t) := by group
        _ = Phi5 π * Phi5 π := by rw [htt, mul_one]
    rw [← this, hσ2]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    rw [map_one, one_mul] at hσ
    rcases ht with rfl | rfl
    · exact hσ1 hσ
    · exact hσs hσ
  obtain ⟨c₅, h1, h2, h3, h4⟩ := s5_comm_witness π hπ2 hπ1
  generalize hu₅ : π * c₅ * π⁻¹ * c₅⁻¹ = u₅ at h1 h2 h3 h4
  have hu_eq : σ * Phi5 c₅ * σ⁻¹ * (Phi5 c₅)⁻¹ = Phi5 u₅ := by
    have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    rw [hσ, ← hu₅, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc Phi5 π * t * Phi5 c₅ * (Phi5 π * t)⁻¹ * (Phi5 c₅)⁻¹
        = Phi5 π * t * Phi5 c₅ * (t⁻¹ * (Phi5 π)⁻¹) * (Phi5 c₅)⁻¹ := by rw [mul_inv_rev]
      _ = Phi5 π * t * Phi5 c₅ * (t * (Phi5 π)⁻¹) * (Phi5 c₅)⁻¹ := by rw [ht1]
      _ = Phi5 π * (t * Phi5 c₅ * t) * (Phi5 π)⁻¹ * (Phi5 c₅)⁻¹ := by group
      _ = Phi5 π * (Phi5 c₅ * t * t) * (Phi5 π)⁻¹ * (Phi5 c₅)⁻¹ := by rw [htc]
      _ = Phi5 π * Phi5 c₅ * (Phi5 π)⁻¹ * (Phi5 c₅)⁻¹ := by
        rw [mul_assoc (Phi5 c₅) t t, htt, mul_one]
  have hnot : ∀ t' : Perm (Fin 7), (t' = 1 ∨ t' = swap 5 6) → Phi5 u₅ = Phi5 π * t' →
      False := by
    intro t' ht' h
    have h' : Phi5 (π⁻¹ * u₅) = t' := by
      rw [map_mul, map_inv]
      exact inv_mul_eq_iff_eq_mul.2 h
    rcases ht' with rfl | rfl
    · apply h4
      have : π⁻¹ * u₅ = 1 := Phi5_injective (by rw [h', map_one])
      calc u₅ = π * (π⁻¹ * u₅) := by group
        _ = π := by rw [this, mul_one]
    · exact Phi5_ne_swap _ h'
  refine ⟨Phi5 c₅, ?_⟩
  unfold W7
  rw [hu_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Equiv.Perm.mem_alternatingGroup.1 (Phi5_mem c₅).2
  · exact Phi5_commutes c₅
  · rw [← map_mul, h1, map_one]
  · intro h
    exact h2 (Phi5_injective (by rw [h, map_one]))
  · exact Phi5_commutes u₅
  · rw [hσ]
    calc Phi5 u₅ * (Phi5 π * t) = (Phi5 u₅ * Phi5 π) * t := by group
      _ = Phi5 (u₅ * π) * t := by rw [← map_mul]
      _ = Phi5 (π * u₅) * t := by rw [h3]
      _ = (Phi5 π * Phi5 u₅) * t := by rw [← map_mul]
      _ = Phi5 π * (Phi5 u₅ * t) := by group
      _ = Phi5 π * (t * Phi5 u₅) := by rw [(htc u₅).symm]
      _ = Phi5 π * t * Phi5 u₅ := by group
  · intro h
    rw [hσ] at h
    exact hnot t ht h
  · exact Phi5_ne_swap _
  · intro h
    rw [hσ] at h
    have hsc : swap 5 6 * Phi5 π = Phi5 π * swap 5 6 := (Phi5_commutes π).symm
    have h' : Phi5 u₅ = Phi5 π * (swap 5 6 * t) := by
      rw [h]
      calc swap 5 6 * (Phi5 π * t) = (swap 5 6 * Phi5 π) * t := by group
        _ = (Phi5 π * swap 5 6) * t := by rw [hsc]
        _ = Phi5 π * (swap 5 6 * t) := by group
    refine hnot (swap 5 6 * t) ?_ h'
    rcases ht with rfl | rfl
    · right
      simp
    · left
      exact Equiv.swap_mul_self _ _

end U7



section U7Perm

theorem U7_perm (ε σ : Perm (Fin 7)) (hε2 : ε * ε = 1) (hσ2 : σ * σ = 1) (hcomm : ε * σ = σ * ε)
    (hσ1 : σ ≠ 1) (hσε : σ ≠ ε) (hε : ε = 1 ∨ ε.IsSwap) : ∃ c, W7 ε σ c := by
  rcases hε with rfl | hsw
  · exact U7_one σ hσ2 hσ1
  · obtain ⟨g, hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr
      (show (swap 5 6 : Perm (Fin 7)).cycleType = ε.cycleType by
        rw [swap56_cycleType, Equiv.Perm.isSwap_iff_cycleType.mp hsw]))
    have hεg : ε = g * swap 5 6 * g⁻¹ := hg.symm
    have hσ'' : g * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
    have hσ''2 : (g⁻¹ * σ * g) * (g⁻¹ * σ * g) = 1 := by
      calc (g⁻¹ * σ * g) * (g⁻¹ * σ * g) = g⁻¹ * (σ * σ) * g := by group
        _ = 1 := by rw [hσ2]; group
    have hσ''1 : g⁻¹ * σ * g ≠ 1 := by
      intro h
      apply hσ1
      calc σ = g * (g⁻¹ * σ * g) * g⁻¹ := hσ''.symm
        _ = 1 := by rw [h]; group
    have hσ''s : g⁻¹ * σ * g ≠ swap 5 6 := by
      intro h
      apply hσε
      rw [hεg, ← h]
      exact hσ''.symm
    have hcomm'' : (g⁻¹ * σ * g) * swap 5 6 = swap 5 6 * (g⁻¹ * σ * g) := by
      have hs : swap 5 6 = g⁻¹ * ε * g := by rw [hεg]; group
      rw [hs]
      calc g⁻¹ * σ * g * (g⁻¹ * ε * g) = g⁻¹ * (σ * ε) * g := by group
        _ = g⁻¹ * (ε * σ) * g := by rw [hcomm]
        _ = g⁻¹ * ε * g * (g⁻¹ * σ * g) := by group
    obtain ⟨c, hc⟩ := U7_swap _ hσ''2 hσ''1 hσ''s hcomm''
    refine ⟨g * c * g⁻¹, ?_⟩
    have := W7_conj g _ _ _ hc
    rw [← hεg, hσ''] at this
    exact this

end U7Perm


section A7Transport

variable {X : Type} [Group X]

theorem autA7Equiv_unique (e : X ≃* alternatingGroup (Fin 7)) (y : MulAut X) (τ : Perm (Fin 7))
    (h : ∀ k : X, psiA7 e (y k) = τ * psiA7 e k * τ⁻¹) : τ = autA7Equiv e y := by
  apply autA7Phi.injective
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  obtain ⟨k, rfl⟩ := e.surjective a
  have hl : ((autA7Phi τ (e k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      τ * (e k : Perm (Fin 7)) * τ⁻¹ := by
    rw [autA7Phi_apply, MulAut.conjNormal_apply]
  have hr : ((autA7Phi (autA7Equiv e y) (e k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      autA7Equiv e y * (e k : Perm (Fin 7)) * (autA7Equiv e y)⁻¹ := by
    rw [autA7Phi_apply, MulAut.conjNormal_apply]
  rw [hl, hr, ← autA7Equiv_spec e y k]
  exact (h k).symm

theorem autA7Equiv_conj (e : X ≃* alternatingGroup (Fin 7)) (k : X) :
    autA7Equiv e (MulAut.conj k) = psiA7 e k := by
  symm
  apply autA7Equiv_unique
  intro x
  simp [psiA7, MulAut.conj_apply]

end A7Transport


theorem autU_A7 {X : Type} [Group X] [Finite X] (e : X ≃* alternatingGroup (Fin 7))
    (ε σ : MulAut X) (hε2 : ε ^ 2 = 1) (hσ2 : σ ^ 2 = 1) (hεσ : ε * σ = σ * ε) (hσ1 : σ ≠ 1)
    (hσε : σ ≠ ε) (hns : ¬ Group.IsSolvable ↥(fixedSubgroup X ε)) :
    ∃ u : X, u ^ 2 = 1 ∧ u ≠ 1 ∧ ε u = u ∧ σ u = u ∧
      u ∈ Subgroup.closure {x : X | ∃ c ∈ fixedSubgroup X ε, x = σ c * c⁻¹} ∧
      MulAut.conj u ∉ ({1, ε, σ, ε * σ} : Set (MulAut X)) := by
  classical
  let θ : MulAut X ≃* Perm (Fin 7) := autA7Equiv e
  have hε'2 : θ ε * θ ε = 1 := by rw [← map_mul, ← sq, hε2, map_one]
  have hσ'2 : θ σ * θ σ = 1 := by rw [← map_mul, ← sq, hσ2, map_one]
  have hcomm' : θ ε * θ σ = θ σ * θ ε := by rw [← map_mul, ← map_mul, hεσ]
  have hσ'1 : θ σ ≠ 1 := fun h => hσ1 (θ.injective (by rw [h, map_one]))
  have hσ'ε : θ σ ≠ θ ε := fun h => hσε (θ.injective h)
  have hclass : θ ε = 1 ∨ (θ ε).IsSwap := by
    by_contra hno
    push Not at hno
    obtain ⟨hne, hnsw⟩ := hno
    have hsq : θ ε ^ 2 = 1 := by rw [sq]; exact hε'2
    apply hns
    have hcard : Nat.card ↥(centralizer ({θ ε} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) =
        24 := by
      rcases involution_cycleType (θ ε) hsq hne with h | h | h
      · exact absurd (Equiv.Perm.isSwap_iff_cycleType.mpr h) hnsw
      · exact card_centralizer_A7_two_two h hsq hne
      · exact card_centralizer_A7_two_two_two h hsq hne
    have hsolvA : Group.IsSolvable ↥(centralizer ({θ ε} : Set (Perm (Fin 7))) ⊓
        alternatingGroup (Fin 7)) :=
      CFSG.GH74.GLS.IVK.GHInv.isSolvable_of_card_dvd_two_pow_mul_three_pow (a := 3) (b := 1)
        (by rw [hcard]; norm_num)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (fixedSubgroupEquivA7 e ε).toMonoidHom) (fixedSubgroupEquivA7 e ε).injective
  obtain ⟨c, hs, hcε, h1, h2, h3, h4, h5, h6, h7⟩ :=
    U7_perm (θ ε) (θ σ) hε'2 hσ'2 hcomm' hσ'1 hσ'ε hclass
  set cX : X := e.symm ⟨c, Equiv.Perm.mem_alternatingGroup.2 hs⟩ with hcX
  have hψc : psiA7 e cX = c := by simp [psiA7, hcX]
  have hspec : ∀ (y : MulAut X) (k : X), psiA7 e (y k) = autA7Equiv e y * psiA7 e k *
      (autA7Equiv e y)⁻¹ := fun y k => autA7Equiv_spec e y k
  have hcXε : cX ∈ fixedSubgroup X ε := by
    show ε cX = cX
    apply psiA7_injective e
    rw [hspec ε cX, hψc]
    calc θ ε * c * (θ ε)⁻¹ = c * θ ε * (θ ε)⁻¹ := by rw [← hcε]
      _ = c := by group
  set uX : X := σ cX * cX⁻¹ with huX
  have hψu : psiA7 e uX = θ σ * c * (θ σ)⁻¹ * c⁻¹ := by
    rw [huX, map_mul, map_inv, hspec σ cX, hψc]
  refine ⟨uX, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply psiA7_injective e
    rw [map_pow, hψu, map_one, sq]
    exact h1
  · intro h
    apply h2
    rw [← hψu, h, map_one]
  · apply psiA7_injective e
    rw [hspec ε uX, hψu]
    calc θ ε * (θ σ * c * (θ σ)⁻¹ * c⁻¹) * (θ ε)⁻¹ =
        (θ σ * c * (θ σ)⁻¹ * c⁻¹) * θ ε * (θ ε)⁻¹ := by rw [← h3]
      _ = θ σ * c * (θ σ)⁻¹ * c⁻¹ := by group
  · apply psiA7_injective e
    rw [hspec σ uX, hψu]
    calc θ σ * (θ σ * c * (θ σ)⁻¹ * c⁻¹) * (θ σ)⁻¹ =
        (θ σ * c * (θ σ)⁻¹ * c⁻¹) * θ σ * (θ σ)⁻¹ := by rw [← h4]
      _ = θ σ * c * (θ σ)⁻¹ * c⁻¹ := by group
  · exact Subgroup.subset_closure ⟨cX, hcXε, rfl⟩
  · have hθu : θ (MulAut.conj uX) = θ σ * c * (θ σ)⁻¹ * c⁻¹ := by
      show autA7Equiv e (MulAut.conj uX) = _
      rw [autA7Equiv_conj, hψu]
    intro hmem
    rcases hmem with h | h | h | h
    · apply h2
      rw [← hθu, h, map_one]
    · exact h6 (by rw [← hθu, h])
    · exact h5 (by rw [← hθu, h])
    · apply h7
      rw [← hθu, h.out]
      exact map_mul θ ε σ


end CFSG.GH74.GLS.Th2.Obs
