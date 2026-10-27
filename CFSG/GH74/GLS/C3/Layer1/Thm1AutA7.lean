module

public import CFSG.GH74.GLS.C3.Layer1.Thm1AutModel
public import CFSG.GH74.GLS.IVK.A7.Glue

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK Equiv

theorem card_le_four_of_dih {Y : Type*} [Group Y] {k : ℕ} [NeZero k] (φ : Y ≃* DihedralGroup k)
    (X : Subgroup Y) (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hsq : ∀ x ∈ X, x * x = 1) :
    Nat.card ↥X ≤ 4 := by
  have hcard : Nat.card ↥(X.map φ.toMonoidHom) = Nat.card ↥X :=
    Subgroup.card_map_of_injective φ.injective
  have hb : Nat.card ↥(X.map φ.toMonoidHom) ≤ 4 := by
    apply DihedralAux.card_le_four_of_elemAbelian
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact hcomm a ha b hb
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul]
      have : a * a = 1 := hsq a ha
      rw [this, map_one]
  omega

theorem perm7_level (B : Subgroup (Perm (Fin 7))) (hB : IsPGroup 2 ↥B)
    (hSyl : IsSylowOf 2 (B ⊓ alternatingGroup (Fin 7)) (alternatingGroup (Fin 7)))
    (E : Subgroup (Perm (Fin 7))) (hEB : E ≤ B) (hE : IsElementaryAbelian 2 ↥E)
    (hE8 : 8 ≤ Nat.card ↥E) :
    ∃ f₀ y p : Perm (Fin 7), y ∈ E ∧ p ∈ B ⊓ alternatingGroup (Fin 7) ∧ f₀ = p⁻¹ * y ∧ f₀ ∈ B ∧
      orderOf f₀ = 2 ∧ f₀ ∉ alternatingGroup (Fin 7) ∧
      (∀ q ∈ B ⊓ alternatingGroup (Fin 7), f₀ * q = q * f₀) ∧
      IsDihedralOrder ↥(B ⊓ alternatingGroup (Fin 7)) 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', hBT'⟩ := hB.exists_le_sylow
  obtain ⟨f₀, hf₀2, -, hf₀T, hinter, hcentral, hsplit⟩ := ivk_1_1T T'
  have hPeq : (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) =
      B ⊓ alternatingGroup (Fin 7) :=
    hSyl.eq_of_le (inf_le_inf_right _ hBT') inf_le_right T'.isPGroup'.to_inf_left
  have hdih : IsDihedralOrder ↥(B ⊓ alternatingGroup (Fin 7)) 8 := by
    rw [← hPeq]
    exact ivk_1_1a T'
  have hsq := sq_eq_one_of_isElementaryAbelian' hE
  have hcomm := comm_of_isElementaryAbelian' hE
  obtain ⟨y, hyE, hyA⟩ : ∃ y ∈ E, y ∉ alternatingGroup (Fin 7) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk, hk2, ⟨φ⟩⟩ := hdih
    have hk4 : k = 4 := by omega
    subst hk4
    have hEP : E ≤ B ⊓ alternatingGroup (Fin 7) := le_inf hEB hcon
    have hc := card_le_four_of_dih φ (E.subgroupOf (B ⊓ alternatingGroup (Fin 7)))
      (fun a ha b hb => Subtype.ext (hcomm a ha b hb))
      (fun a ha => Subtype.ext (hsq a ha))
    have hcard : Nat.card ↥(E.subgroupOf (B ⊓ alternatingGroup (Fin 7))) = Nat.card ↥E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv
    omega
  have hyT : y ∈ (T' : Subgroup (Perm (Fin 7))) := hBT' (hEB hyE)
  have hcomm' : ∀ p ∈ (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7),
      ∀ q ∈ zpowers f₀, p * q = q * p := by
    intro p hp q hq
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
    exact (Commute.zpow_right (hcentral p hp) j).eq
  obtain ⟨p, hpP, q, hq, hyq⟩ :=
    Back.exists_mul_of_mem_sup_of_commute hcomm' (hsplit ▸ hyT)
  have hf₀sq : f₀ * f₀ = 1 := by
    have := pow_orderOf_eq_one f₀
    rwa [hf₀2, sq] at this
  have hq' : q = 1 ∨ q = f₀ := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
    rcases Int.even_or_odd' j with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul]
      simp [sq, hf₀sq]
    · right
      rw [zpow_add_one, zpow_mul]
      simp [sq, hf₀sq]
  have hpA : p ∈ alternatingGroup (Fin 7) := hpP.2
  have hqf : q = f₀ := by
    rcases hq' with h | h
    · exfalso
      apply hyA
      rw [hyq, h, mul_one]
      exact hpA
    · exact h
  have hpB : p ∈ B ⊓ alternatingGroup (Fin 7) := hPeq ▸ hpP
  have hf₀eq : f₀ = p⁻¹ * y := by
    rw [hyq, hqf]
    group
  refine ⟨f₀, y, p, hyE, hpB, hf₀eq, ?_, hf₀2, ?_, ?_, hdih⟩
  · rw [hf₀eq]
    exact B.mul_mem (B.inv_mem hpB.1) (hEB hyE)
  · intro hfA
    apply hyA
    rw [hyq, hqf]
    exact (alternatingGroup (Fin 7)).mul_mem hpA hfA
  · intro q' hq'
    exact (hcentral q' (hPeq ▸ hq')).symm

noncomputable def cEquiv : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num))

noncomputable def psiEquiv {Kb : Type} [Group Kb] (e7 : Kb ≃* alternatingGroup (Fin 7)) :
    MulAut Kb ≃* Perm (Fin 7) :=
  (MulAut.congr e7).trans cEquiv.symm

theorem psi_conj {Kb : Type} [Group Kb] (e7 : Kb ≃* alternatingGroup (Fin 7)) (k : Kb) :
    psiEquiv e7 (MulAut.conj k) = ((e7 k : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
  have h1 : MulAut.congr e7 (MulAut.conj k) = MulAut.conj (e7 k) := by
    ext a
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have h2 : cEquiv (((e7 k : alternatingGroup (Fin 7)) : Perm (Fin 7))) = MulAut.conj (e7 k) := by
    show MulAut.conjNormal (H := alternatingGroup (Fin 7)) ((e7 k : alternatingGroup (Fin 7)) :
      Perm (Fin 7)) = _
    exact MulAut.conjNormal_val
  show cEquiv.symm (MulAut.congr e7 (MulAut.conj k)) = _
  rw [h1, ← h2]
  exact cEquiv.symm_apply_apply _

theorem psi_map_innAut {Kb : Type} [Group Kb] (e7 : Kb ≃* alternatingGroup (Fin 7)) :
    (innAut Kb).map (psiEquiv e7).toMonoidHom = alternatingGroup (Fin 7) := by
  ext a
  constructor
  · rintro ⟨b, ⟨k, rfl⟩, rfl⟩
    show psiEquiv e7 (MulAut.conj k) ∈ alternatingGroup (Fin 7)
    rw [psi_conj]
    exact (e7 k).2
  · intro ha
    refine ⟨MulAut.conj (e7.symm ⟨a, ha⟩), ⟨e7.symm ⟨a, ha⟩, rfl⟩, ?_⟩
    show psiEquiv e7 (MulAut.conj (e7.symm ⟨a, ha⟩)) = a
    rw [psi_conj]
    simp

theorem conj_injective_of_A7 {Kb : Type} [Group Kb] (e7 : Kb ≃* alternatingGroup (Fin 7)) :
    Function.Injective (MulAut.conj : Kb →* MulAut Kb) := by
  intro a b h
  have h1 := congrArg (psiEquiv e7) h
  rw [psi_conj, psi_conj] at h1
  exact e7.injective (Subtype.ext h1)

theorem isSylowOf_map_equiv {X Y : Type*} [Group X] [Group Y] [Finite X] (ψ : X ≃* Y)
    {P K : Subgroup X}
    (h : IsSylowOf 2 P K) : IsSylowOf 2 (P.map ψ.toMonoidHom) (K.map ψ.toMonoidHom) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (ψ.toMonoidHom.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem exists_dihedral_center {X : Type} [Group X] {H : Subgroup X} {n : ℕ} (hn3 : 3 ≤ n)
    (h : IsDihedralTwoGroup ↥H n) :
    ∃ z ∈ H, orderOf z = 2 ∧ (∀ q ∈ H, z * q = q * z) ∧
      ∀ w ∈ H, (∀ q ∈ H, w * q = q * w) → w = 1 ∨ w = z := by
  obtain ⟨-, k, hk, hk2, ⟨φ⟩⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hk' : k = 4 * 2 ^ m := by
    have : 2 ^ (m + 3) = 2 * (4 * 2 ^ m) := by ring
    omega
  have hpos : 0 < 2 ^ m := by positivity
  have hkE : Even k := ⟨2 * 2 ^ m, by omega⟩
  have hkne : k ≠ 2 := by omega
  obtain ⟨c, hcc, hc1, hc2⟩ := DihedralAux.exists_central_involution hkE hkne (by omega)
  set z : ↥H := φ.symm c with hz
  have hφz : φ z = c := φ.apply_symm_apply c
  have hz1 : z ≠ 1 := fun h' => hc1 (by rw [← hφz, h', map_one])
  have hzz : z * z = 1 := by rw [hz, ← map_mul, hc2, map_one]
  have hzc : ∀ q : ↥H, z * q = q * z := by
    intro q
    have := Subgroup.mem_center_iff.mp hcc (φ q)
    have h2 := congrArg (fun y => (φ.symm y : ↥H)) this
    simpa [hz, map_mul] using h2.symm
  refine ⟨(z : X), z.2, ?_, fun q hq => congrArg Subtype.val (hzc ⟨q, hq⟩), ?_⟩
  · refine orderOf_eq_prime (by rw [sq]; exact congrArg Subtype.val hzz) ?_
    exact fun h' => hz1 (Subtype.ext h')
  · intro w hw hwc
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · refine Or.inr ?_
      have := DihedralAux.central_involution_unique φ hkE hkne (a := ⟨w, hw⟩) (b := z)
        (fun x => Subtype.ext (hwc x x.2)) hzc (fun h' => hw1 (congrArg Subtype.val h'))
        hz1
      exact congrArg Subtype.val this

theorem odd_involution_cycleType {u : Perm (Fin 7)} (hu2 : orderOf u = 2)
    (hodd : u ∉ alternatingGroup (Fin 7)) : u.cycleType = {2} ∨ u.cycleType = {2, 2, 2} := by
  have hall : ∀ n ∈ u.cycleType, n = 2 := by
    intro n hn
    have h1 : n ∣ 2 := hu2 ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  obtain ⟨k, hrep⟩ : ∃ k, u.cycleType = Multiset.replicate k 2 :=
    ⟨_, Multiset.eq_replicate_of_mem hall⟩
  have hsum : u.cycleType.sum = 2 * k := by
    rw [hrep, Multiset.sum_replicate]
    simp [mul_comm]
  have hsign : Equiv.Perm.sign u = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign u) with h | h
    · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h) hodd
    · exact h
  have hcard : Multiset.card u.cycleType = k := by rw [hrep, Multiset.card_replicate]
  have hkodd : Odd k := by
    by_contra hke
    rw [Nat.not_odd_iff_even] at hke
    rw [Equiv.Perm.sign_of_cycleType, hsum, hcard] at hsign
    have : Even (2 * k + k) := by
      obtain ⟨m, hm⟩ := hke
      exact ⟨3 * m, by omega⟩
    rw [Even.neg_one_pow this] at hsign
    exact absurd hsign (by decide)
  have hkle : 2 * k ≤ 7 := by
    rw [← hsum, Equiv.Perm.sum_cycleType]
    calc u.support.card ≤ Fintype.card (Fin 7) := Finset.card_le_univ _
      _ = 7 := Fintype.card_fin 7
  obtain ⟨m, hm⟩ := hkodd
  have hm' : m = 0 ∨ m = 1 := by omega
  rw [hrep]
  rcases hm' with rfl | rfl
  · left
    have : k = 1 := by omega
    rw [this]
    rfl
  · right
    have : k = 3 := by omega
    rw [this]
    rfl

theorem exists_alt_conj_of_odd {u v : Perm (Fin 7)} (hu : u ∉ alternatingGroup (Fin 7))
    (hu2 : u * u = 1) (hconj : IsConj u v) :
    ∃ g ∈ alternatingGroup (Fin 7), g * u * g⁻¹ = v := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  by_cases hcA : c ∈ alternatingGroup (Fin 7)
  · exact ⟨c, hcA, hc⟩
  · refine ⟨c * u, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, map_mul]
      have h1 : Equiv.Perm.sign c = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign c) with h | h
        · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h) hcA
        · exact h
      have h2 : Equiv.Perm.sign u = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign u) with h | h
        · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h) hu
        · exact h
      rw [h1, h2]
      decide
    · have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
      calc c * u * u * (c * u)⁻¹ = c * (u * u) * u⁻¹ * c⁻¹ := by group
        _ = c * u * c⁻¹ := by rw [hu2, huinv]; group
        _ = v := hc

theorem perm7_fus (B : Subgroup (Perm (Fin 7))) (hB : IsPGroup 2 ↥B)
    (hSyl : IsSylowOf 2 (B ⊓ alternatingGroup (Fin 7)) (alternatingGroup (Fin 7)))
    {z : Perm (Fin 7)} (hzP : z ∈ B ⊓ alternatingGroup (Fin 7)) (hz2 : orderOf z = 2)
    (hzc : ∀ q ∈ B ⊓ alternatingGroup (Fin 7), z * q = q * z) :
    ∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ alternatingGroup (Fin 7) →
      (∀ q ∈ B ⊓ alternatingGroup (Fin 7), σ' * q = q * σ') →
      (∃ (T : Sylow 2 (Perm (Fin 7))) (f₀ : Perm (Fin 7)), IsA7SylowSplit T f₀ ∧
        (σ' = f₀ ∨ σ' = f₀ * z)) ∧
      ∀ u ∈ (B ⊓ alternatingGroup (Fin 7)) ⊔ zpowers σ', orderOf u = 2 →
        ∃ g ∈ alternatingGroup (Fin 7),
          g * u * g⁻¹ = z ∨ g * u * g⁻¹ = σ' ∨ g * u * g⁻¹ = σ' * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', hBT'⟩ := hB.exists_le_sylow
  obtain ⟨f₀, hS⟩ := ivk_1_1T T'
  obtain ⟨hf₀2, hf₀ct, hf₀T, hinter, hcentral, hsplit⟩ := hS
  have hPeq : (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) =
      B ⊓ alternatingGroup (Fin 7) :=
    hSyl.eq_of_le (inf_le_inf_right _ hBT') inf_le_right T'.isPGroup'.to_inf_left
  have hdih : IsDihedralOrder ↥(B ⊓ alternatingGroup (Fin 7)) 8 := by
    rw [← hPeq]
    exact ivk_1_1a T'
  obtain ⟨z₀, hz₀H, hz₀2, hz₀c, hz₀u⟩ := exists_dihedral_center (H := B ⊓ alternatingGroup (Fin 7))
    (n := 3) le_rfl ⟨by norm_num, by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact hdih⟩
  have hzz₀ : z = z₀ := by
    rcases hz₀u z hzP hzc with h | h
    · rw [h, orderOf_one] at hz2
      omega
    · exact h
  have hf₀sq : f₀ * f₀ = 1 := by
    have := pow_orderOf_eq_one f₀
    rwa [hf₀2, sq] at this
  have hzsq : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have hf₀odd : f₀ ∉ alternatingGroup (Fin 7) := by
    intro h
    have : f₀ ∈ (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) ⊓ zpowers f₀ :=
      ⟨⟨hf₀T, h⟩, mem_zpowers f₀⟩
    rw [hinter, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hf₀2
    omega
  have hzT : z ∈ (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := by
    rw [hPeq]
    exact hzP
  have hf₀z : (f₀ * z).cycleType = {2, 2, 2} := ivk_1_1b T' f₀
    ⟨hf₀2, hf₀ct, hf₀T, hinter, hcentral, hsplit⟩ z hzT hz2
    (fun x hx => (hzc x (hPeq ▸ hx)).symm)
  have hf₀zc : f₀ * z = z * f₀ := (hcentral z hzT).symm
  intro σ' hσ'B hσ'2 hσ'odd hσ'c
  have hσ'T : σ' ∈ (T' : Subgroup (Perm (Fin 7))) := hBT' hσ'B
  have hcls : σ' = f₀ ∨ σ' = f₀ * z := by
    have hcomm : ∀ p ∈ (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7),
        ∀ q ∈ zpowers f₀, p * q = q * p := by
      intro p hp q hq
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
      exact (Commute.zpow_right (show Commute p f₀ from hcentral p hp) j).eq
    obtain ⟨p, hpP, w, hw, hσ'eq⟩ := Back.exists_mul_of_mem_sup_of_commute hcomm (hsplit ▸ hσ'T)
    rcases mem_zpowers_of_mul_self hf₀sq hw with hw1 | hwf
    · exfalso
      apply hσ'odd
      rw [hσ'eq, hw1, mul_one]
      exact hpP.2
    · have hpP' : p ∈ B ⊓ alternatingGroup (Fin 7) := hPeq ▸ hpP
      have hpc : ∀ q ∈ B ⊓ alternatingGroup (Fin 7), p * q = q * p := by
        intro q hq
        have hqT : q ∈ (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := hPeq ▸ hq
        have h1 := hσ'c q hq
        rw [hσ'eq, hwf] at h1
        have h2 : p * q * f₀ = q * p * f₀ := by
          calc p * q * f₀ = p * (q * f₀) := by group
            _ = p * (f₀ * q) := by rw [hcentral q hqT]
            _ = p * f₀ * q := by group
            _ = q * (p * f₀) := h1
            _ = q * p * f₀ := by group
        exact mul_right_cancel h2
      rcases hz₀u p hpP' hpc with hp1 | hpz
      · left
        rw [hσ'eq, hwf, hp1, one_mul]
      · right
        rw [hσ'eq, hwf, hpz, ← hzz₀, hf₀zc]
  refine ⟨⟨T', f₀, ⟨hf₀2, hf₀ct, hf₀T, hinter, hcentral, hsplit⟩, hcls⟩, ?_⟩
  intro u hu hu2
  have hcases : (∃ g ∈ alternatingGroup (Fin 7), g * u * g⁻¹ = z) ∨
      (∃ g ∈ alternatingGroup (Fin 7), g * u * g⁻¹ = f₀) ∨
      (∃ g ∈ alternatingGroup (Fin 7), g * u * g⁻¹ = f₀ * z) := by
    have huT : u ∈ (T' : Subgroup (Perm (Fin 7))) := by
      have hle : (B ⊓ alternatingGroup (Fin 7)) ⊔ zpowers σ' ≤ (T' : Subgroup (Perm (Fin 7))) :=
        sup_le (inf_le_left.trans hBT') ((zpowers_le).2 hσ'T)
      exact hle hu
    have hcomm : ∀ p ∈ (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7),
        ∀ q ∈ zpowers f₀, p * q = q * p := by
      intro p hp q hq
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
      exact (Commute.zpow_right (show Commute p f₀ from hcentral p hp) j).eq
    obtain ⟨p, hpP, w, hw, hueq⟩ := Back.exists_mul_of_mem_sup_of_commute hcomm (hsplit ▸ huT)
    rcases mem_zpowers_of_mul_self hf₀sq hw with hw1 | hwf
    · left
      have huA : u ∈ alternatingGroup (Fin 7) := by
        rw [hueq, hw1, mul_one]
        exact hpP.2
      obtain ⟨g, hg, hgu⟩ := (ivk_1_1d).1 u z huA hzP.2 hu2 hz2
      exact ⟨g, hg, hgu⟩
    · have huodd : u ∉ alternatingGroup (Fin 7) := by
        intro huA
        apply hf₀odd
        have : f₀ = p⁻¹ * u := by rw [hueq, hwf]; group
        rw [this]
        exact (alternatingGroup (Fin 7)).mul_mem ((alternatingGroup (Fin 7)).inv_mem hpP.2) huA
      have huu : u * u = 1 := by
        have := pow_orderOf_eq_one u
        rwa [hu2, sq] at this
      rcases odd_involution_cycleType hu2 huodd with hct | hct
      · right
        left
        exact exists_alt_conj_of_odd huodd huu (Equiv.Perm.isConj_iff_cycleType_eq.2 (by rw [hct, hf₀ct]))
      · right
        right
        exact exists_alt_conj_of_odd huodd huu (Equiv.Perm.isConj_iff_cycleType_eq.2 (by rw [hct, hf₀z]))
  rcases hcls with h | h
  · rw [h]
    rcases hcases with ⟨g, hg, hgu⟩ | ⟨g, hg, hgu⟩ | ⟨g, hg, hgu⟩
    · exact ⟨g, hg, Or.inl hgu⟩
    · exact ⟨g, hg, Or.inr (Or.inl hgu)⟩
    · exact ⟨g, hg, Or.inr (Or.inr hgu)⟩
  · rw [h]
    rcases hcases with ⟨g, hg, hgu⟩ | ⟨g, hg, hgu⟩ | ⟨g, hg, hgu⟩
    · exact ⟨g, hg, Or.inl hgu⟩
    · refine ⟨g, hg, Or.inr (Or.inr ?_)⟩
      have : f₀ * z * z = f₀ := by rw [mul_assoc, hzsq, mul_one]
      rw [this]
      exact hgu
    · exact ⟨g, hg, Or.inr (Or.inl hgu)⟩

theorem perm7_solv (B : Subgroup (Perm (Fin 7))) (hB : IsPGroup 2 ↥B)
    (hSyl : IsSylowOf 2 (B ⊓ alternatingGroup (Fin 7)) (alternatingGroup (Fin 7)))
    {z : Perm (Fin 7)} (hzP : z ∈ B ⊓ alternatingGroup (Fin 7)) (hz2 : orderOf z = 2)
    (hzc : ∀ q ∈ B ⊓ alternatingGroup (Fin 7), z * q = q * z) :
    Group.IsSolvable ↥(centralizer ({z} : Set (Perm (Fin 7)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', hBT'⟩ := hB.exists_le_sylow
  have hPeq : (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) =
      B ⊓ alternatingGroup (Fin 7) :=
    hSyl.eq_of_le (inf_le_inf_right _ hBT') inf_le_right T'.isPGroup'.to_inf_left
  have hzT : z ∈ (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := by
    rw [hPeq]
    exact hzP
  obtain ⟨⟨e⟩, -⟩ := (ivk_1_1d).2 T' z hzT hz2 (fun x hx => (hzc x (hPeq ▸ hx)).symm)
  have h1 := isSolvable_dihedral 4
  have h2 : Group.IsSolvable (Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  have h3 : Group.IsSolvable (DihedralGroup 4 × Perm (Fin 3)) := inferInstance
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem psi_apply {Kb : Type} [Group Kb] (e7 : Kb ≃* alternatingGroup (Fin 7)) (σ : MulAut Kb)
    (k : Kb) :
    ((e7 (σ k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      psiEquiv e7 σ * ((e7 k : alternatingGroup (Fin 7)) : Perm (Fin 7)) * (psiEquiv e7 σ)⁻¹ := by
  have h : cEquiv (psiEquiv e7 σ) = MulAut.congr e7 σ := by
    show cEquiv (cEquiv.symm (MulAut.congr e7 σ)) = _
    exact cEquiv.apply_symm_apply _
  have h2 := MulAut.conjNormal_apply (H := alternatingGroup (Fin 7)) (psiEquiv e7 σ) (e7 k)
  have h3 : (MulAut.conjNormal (H := alternatingGroup (Fin 7)) (psiEquiv e7 σ)) (e7 k) =
      e7 (σ k) := by
    have h4 : cEquiv (psiEquiv e7 σ) (e7 k) = (MulAut.congr e7 σ) (e7 k) := by rw [h]
    have h5 : (MulAut.congr e7 σ) (e7 k) = e7 (σ k) := by simp [MulAut.congr_apply]
    exact h4.trans h5
  rw [h3] at h2
  exact h2

theorem fixedSubgroup_equiv_A7 {Kb : Type} [Group Kb] (e7 : Kb ≃* alternatingGroup (Fin 7))
    (σ : MulAut Kb) :
    Nonempty (↥(fixedSubgroup Kb σ) ≃*
      ↥(centralizer ({psiEquiv e7 σ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7))) := by
  have hfix : ∀ k : Kb, σ k = k ↔ psiEquiv e7 σ * ((e7 k : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      ((e7 k : alternatingGroup (Fin 7)) : Perm (Fin 7)) * psiEquiv e7 σ := by
    intro k
    constructor
    · intro h
      have h1 := psi_apply e7 σ k
      rw [h] at h1
      calc psiEquiv e7 σ * ((e7 k : alternatingGroup (Fin 7)) : Perm (Fin 7))
          = (psiEquiv e7 σ * ((e7 k : alternatingGroup (Fin 7)) : Perm (Fin 7)) *
              (psiEquiv e7 σ)⁻¹) * psiEquiv e7 σ := by group
        _ = ((e7 k : alternatingGroup (Fin 7)) : Perm (Fin 7)) * psiEquiv e7 σ := by rw [← h1]
    · intro h
      apply e7.injective
      apply Subtype.ext
      rw [psi_apply, h, mul_inv_cancel_right]
  let f : ↥(fixedSubgroup Kb σ) →*
      ↥(centralizer ({psiEquiv e7 σ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) :=
    ((alternatingGroup (Fin 7)).subtype.comp (e7.toMonoidHom.comp
      (fixedSubgroup Kb σ).subtype)).codRestrict
      (centralizer ({psiEquiv e7 σ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7))
      (fun k => ⟨mem_centralizer_singleton_iff.2 ((hfix k).1 k.2).symm, (e7 k).2⟩)
  refine ⟨MulEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro a b hab
    have h1 := congrArg (fun w : ↥(centralizer ({psiEquiv e7 σ} : Set (Perm (Fin 7))) ⊓
      alternatingGroup (Fin 7)) => (w : Perm (Fin 7))) hab
    exact Subtype.ext (e7.injective (Subtype.ext h1))
  · rintro ⟨w, hwc, hwA⟩
    have hk : σ (e7.symm ⟨w, hwA⟩) = e7.symm ⟨w, hwA⟩ := by
      rw [hfix]
      simpa using (mem_centralizer_singleton_iff.1 hwc).symm
    exact ⟨⟨e7.symm ⟨w, hwA⟩, hk⟩, Subtype.ext (by simp [f])⟩

theorem goodC_A7 {Kb : Type} [Group Kb] (e7 : Kb ≃* alternatingGroup (Fin 7)) (σ : MulAut Kb)
    (hct : (psiEquiv e7 σ).cycleType = {2}) : GoodC Kb σ := by
  obtain ⟨e1⟩ := fixedSubgroup_equiv_A7 e7 σ
  obtain ⟨e2⟩ := A7.centralizer_A7_swap_equiv (Equiv.Perm.isSwap_iff_cycleType.mpr hct)
  exact ⟨Perm (Fin 5), inferInstance, inferInstance, perm5_pPrimeCore_eq_bot,
    ⟨_, alt5_isComponent⟩, ⟨e1.trans e2⟩⟩

theorem autLevelF_of_A7 {Kb : Type} [Group Kb] (e7 : Kb ≃* alternatingGroup (Fin 7)) :
    AutLevelF Kb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro B hB hSyl E hEB hE hE8
  set ψ := psiEquiv e7 with hψ
  have : Finite (MulAut Kb) := Finite.of_equiv _ ψ.symm.toEquiv
  have hinn := psi_map_innAut e7
  have hinj : Function.Injective ψ.toMonoidHom := ψ.injective
  have hBin : (B ⊓ innAut Kb).map ψ.toMonoidHom =
      B.map ψ.toMonoidHom ⊓ alternatingGroup (Fin 7) := by
    rw [Subgroup.map_inf _ _ _ hinj, hinn]
  have hB' : IsPGroup 2 ↥(B.map ψ.toMonoidHom) :=
    hB.of_equiv (Subgroup.equivMapOfInjective B ψ.toMonoidHom hinj)
  have hSyl' : IsSylowOf 2 (B.map ψ.toMonoidHom ⊓ alternatingGroup (Fin 7))
      (alternatingGroup (Fin 7)) := by
    have := isSylowOf_map_equiv ψ hSyl
    rwa [hBin, hinn] at this
  have hE' : IsElementaryAbelian 2 ↥(E.map ψ.toMonoidHom) := by
    have := hE
    exact IsElementaryAbelian.map ψ.toMonoidHom
  have hE8' : 8 ≤ Nat.card ↥(E.map ψ.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective hinj]
  obtain ⟨f₀, y, p, hyE, hpB, hf₀, hf₀B, hf₀2, hf₀A, hf₀c, hdih⟩ :=
    perm7_level (B.map ψ.toMonoidHom) hB' hSyl' (E.map ψ.toMonoidHom) (Subgroup.map_mono hEB)
      hE' hE8'
  have hy : ψ.symm y ∈ E := Subgroup.mem_map_equiv.1 hyE
  have hp : ψ.symm p ∈ B ⊓ innAut Kb := by
    apply Subgroup.mem_map_equiv.1
    rw [hBin]
    exact hpB
  have hσB : ψ.symm f₀ ∈ B := Subgroup.mem_map_equiv.1 hf₀B
  have hσ : ψ.symm f₀ = (ψ.symm p)⁻¹ * ψ.symm y := by
    rw [hf₀, map_mul, map_inv]
  have hσ2 : orderOf (ψ.symm f₀) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hf₀2
  have hσ1 : ψ.symm f₀ ≠ 1 := fun h => by rw [h, orderOf_one] at hσ2; omega
  have hσinn : ψ.symm f₀ ∉ innAut Kb := by
    intro h
    apply hf₀A
    have : f₀ ∈ (innAut Kb).map ψ.toMonoidHom := Subgroup.mem_map_equiv.2 h
    rwa [hinn] at this
  have hcent : ∀ q ∈ B ⊓ innAut Kb, ψ.symm f₀ * q = q * ψ.symm f₀ := by
    intro q hq
    have hq' : ψ q ∈ B.map ψ.toMonoidHom ⊓ alternatingGroup (Fin 7) := by
      rw [← hBin]
      exact ⟨q, hq, rfl⟩
    have := congrArg ψ.symm (hf₀c (ψ q) hq')
    simpa using this
  have hdihB : IsDihedralTwoGroup ↥(B ⊓ innAut Kb) 3 := by
    obtain ⟨k, hk, hk2, ⟨φ⟩⟩ := hdih
    refine ⟨by norm_num, k, by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact hk, hk2, ⟨?_⟩⟩
    exact ((Subgroup.equivMapOfInjective _ ψ.toMonoidHom hinj).trans
      (MulEquiv.subgroupCongr hBin)).trans φ
  obtain ⟨z, hzH, hz2, hzc, hzu⟩ := exists_dihedral_center (H := B ⊓ innAut Kb) (n := 3) le_rfl hdihB
  have hzB' : ψ z ∈ B.map ψ.toMonoidHom ⊓ alternatingGroup (Fin 7) := by
    rw [← hBin]
    exact ⟨z, hzH, rfl⟩
  have hz2' : orderOf (ψ z) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hz2
  have hzc' : ∀ q ∈ B.map ψ.toMonoidHom ⊓ alternatingGroup (Fin 7), ψ z * q = q * ψ z := by
    intro q hq
    rw [← hBin] at hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    show ψ z * ψ q₀ = ψ q₀ * ψ z
    rw [← map_mul, ← map_mul, hzc q₀ hq₀]
  have hfus := perm7_fus (B.map ψ.toMonoidHom) hB' hSyl' hzB' hz2' hzc'
  have hfus0 : ∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ innAut Kb →
      (∀ q ∈ B ⊓ innAut Kb, σ' * q = q * σ') →
      (∃ (T : Sylow 2 (Perm (Fin 7))) (f₀ : Perm (Fin 7)), IsA7SylowSplit T f₀ ∧
        (ψ σ' = f₀ ∨ ψ σ' = f₀ * ψ z)) ∧
      ∀ u ∈ (B.map ψ.toMonoidHom ⊓ alternatingGroup (Fin 7)) ⊔ zpowers (ψ σ'), orderOf u = 2 →
        ∃ g ∈ alternatingGroup (Fin 7),
          g * u * g⁻¹ = ψ z ∨ g * u * g⁻¹ = ψ σ' ∨ g * u * g⁻¹ = ψ σ' * ψ z := by
    intro σ' hσ'B hσ'2 hσ'inn hσ'c
    have hσ'odd : ψ σ' ∉ alternatingGroup (Fin 7) := by
      intro h
      apply hσ'inn
      rw [← hinn] at h
      simpa [hψ] using Subgroup.mem_map_equiv.1 h
    have hc : ∀ q ∈ B.map ψ.toMonoidHom ⊓ alternatingGroup (Fin 7), ψ σ' * q = q * ψ σ' := by
      intro q hq
      rw [← hBin] at hq
      obtain ⟨q₀, hq₀, rfl⟩ := hq
      show ψ σ' * ψ q₀ = ψ q₀ * ψ σ'
      rw [← map_mul, ← map_mul, hσ'c q₀ hq₀]
    exact hfus (ψ σ') (Subgroup.mem_map_of_mem _ hσ'B)
      (by rw [MulEquiv.orderOf_eq]; exact hσ'2) hσ'odd hc
  have hfus' : ∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ innAut Kb →
      (∀ q ∈ B ⊓ innAut Kb, σ' * q = q * σ') →
      ∀ u ∈ (B ⊓ innAut Kb) ⊔ zpowers σ', orderOf u = 2 →
        ∃ g ∈ innAut Kb, g * u * g⁻¹ = z ∨ g * u * g⁻¹ = σ' ∨ g * u * g⁻¹ = σ' * z := by
    intro σ' hσ'B hσ'2 hσ'inn hσ'c u hu hu2
    have hmem : ψ u ∈ (B.map ψ.toMonoidHom ⊓ alternatingGroup (Fin 7)) ⊔ zpowers (ψ σ') := by
      have h1 := Subgroup.mem_map_of_mem ψ.toMonoidHom hu
      rw [Subgroup.map_sup, hBin, MonoidHom.map_zpowers] at h1
      exact h1
    obtain ⟨g', hg', hg⟩ := (hfus0 σ' hσ'B hσ'2 hσ'inn hσ'c).2 (ψ u) hmem
      (by rw [MulEquiv.orderOf_eq]; exact hu2)
    refine ⟨ψ.symm g', ?_, ?_⟩
    · rw [← hinn] at hg'
      exact Subgroup.mem_map_equiv.1 hg'
    · have key : ∀ w : MulAut Kb, g' * ψ u * g'⁻¹ = ψ w → ψ.symm g' * u * (ψ.symm g')⁻¹ = w := by
        intro w hw
        apply ψ.injective
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hw]
      rcases hg with h | h | h
      · exact Or.inl (key z h)
      · exact Or.inr (Or.inl (key σ' h))
      · exact Or.inr (Or.inr (key (σ' * z) (by rw [map_mul]; exact h)))
  have hzz' : ψ z * ψ z = 1 := by
    have := pow_orderOf_eq_one (ψ z)
    rwa [hz2', sq] at this
  have hlay : ∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ innAut Kb →
      (∀ q ∈ B ⊓ innAut Kb, σ' * q = q * σ') →
      GoodC Kb σ' ∨ (Nonempty (Kb ≃* alternatingGroup (Fin 7)) ∧ GoodC Kb (σ' * z)) := by
    intro σ' hσ'B hσ'2 hσ'inn hσ'c
    obtain ⟨⟨T, f₀', ⟨-, hcyc, -⟩, hcls⟩, -⟩ := hfus0 σ' hσ'B hσ'2 hσ'inn hσ'c
    rcases hcls with h | h
    · exact Or.inl (goodC_A7 e7 σ' (by rw [← hψ, h]; exact hcyc))
    · refine Or.inr ⟨⟨e7⟩, goodC_A7 e7 (σ' * z) ?_⟩
      rw [← hψ, map_mul, h, mul_assoc, hzz', mul_one]
      exact hcyc
  have hsolv : ∀ k₀ : Kb, (MulAut.conj k₀ : MulAut Kb) = z →
      Group.IsSolvable ↥(centralizer ({k₀} : Set Kb)) := by
    intro k₀ hk₀
    have hψz : ψ z = ((e7 k₀ : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
      rw [← hk₀]
      exact psi_conj e7 k₀
    have hsolv' := perm7_solv (B.map ψ.toMonoidHom) hB' hSyl' hzB' hz2' hzc'
    let f : ↥(centralizer ({k₀} : Set Kb)) →* ↥(centralizer ({ψ z} : Set (Perm (Fin 7)))) :=
      ((alternatingGroup (Fin 7)).subtype.comp (e7.toMonoidHom.comp
        (centralizer ({k₀} : Set Kb)).subtype)).codRestrict
        (centralizer ({ψ z} : Set (Perm (Fin 7)))) (fun k => by
          rw [mem_centralizer_singleton_iff, hψz]
          have h1 := mem_centralizer_singleton_iff.1 k.2
          have h2 : e7 (k : Kb) * e7 k₀ = e7 k₀ * e7 (k : Kb) := by rw [← map_mul, ← map_mul, h1]
          exact congrArg Subtype.val h2)
    refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
    intro a b hab
    have h1 := congrArg (fun w : ↥(centralizer ({ψ z} : Set (Perm (Fin 7)))) =>
      (w : Perm (Fin 7))) hab
    exact Subtype.ext (e7.injective (Subtype.ext h1))
  exact ⟨ψ.symm f₀, ψ.symm y, ψ.symm p, z, hy, hp, hσ, hσB, hσ2, hcent, ⟨hσ1, Or.inr ⟨⟨e7⟩, hσinn⟩⟩,
    hσinn, ⟨3, le_rfl, hdihB⟩, hzH, hz2, hzc, hzu, hfus',
    fun σ' _ hσ'2 hσ'inn _ => ⟨fun h => by rw [h, orderOf_one] at hσ'2; omega,
      Or.inr ⟨⟨e7⟩, hσ'inn⟩⟩, hsolv, hlay⟩

end CFSG.GH74.GLS.C3.Layer1.Thm1
