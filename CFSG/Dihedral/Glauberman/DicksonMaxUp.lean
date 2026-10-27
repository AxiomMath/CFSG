module

public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.Dihedral.Glauberman.DicksonMaxStructure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Orders
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Maximal
public import Certificates.Certificate43
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient

public section

namespace CFSG.Glauberman.Dickson.MaxUp

open BenderSuzuki.MatrixGroups CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open CFSG.GorensteinWalter

theorem overgroup_comm_mem {M : Type*} [Group M] (E C : Subgroup M) [E.Normal]
    (hC : IsCyclic C) (hsup : E ⊔ C = ⊤) (a b : M) : a * b * a⁻¹ * b⁻¹ ∈ E := by
  have ha : a ∈ E ⊔ C := hsup ▸ Subgroup.mem_top a
  have hb : b ∈ E ⊔ C := hsup ▸ Subgroup.mem_top b
  obtain ⟨n₁, hn₁, c₁, hc₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
  obtain ⟨n₂, hn₂, c₂, hc₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hb
  have hc : c₁ * c₂ = c₂ * c₁ :=
    congrArg Subtype.val (hC.commGroup.mul_comm ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩)
  rw [← QuotientGroup.eq_one_iff (N := E)]
  have e1 : ((n₁ : M) : M ⧸ E) = 1 := (QuotientGroup.eq_one_iff _).mpr hn₁
  have e2 : ((n₂ : M) : M ⧸ E) = 1 := (QuotientGroup.eq_one_iff _).mpr hn₂
  have e3 : ((c₁ : M) : M ⧸ E) * c₂ = c₂ * c₁ := by
    rw [← QuotientGroup.mk_mul, hc, QuotientGroup.mk_mul]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, e1, e2, one_mul]
  rw [e3]
  group

theorem alternatingFour_pair : ∃ x y : alternatingGroup (Fin 4), x ^ 3 = 1 ∧ x ≠ 1 ∧
    y ^ 3 = 1 ∧ y ≠ 1 ∧ x * y ≠ y * x ∧ x * y * x⁻¹ * y⁻¹ ≠ 1 ∧
      (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    by decide⟩

theorem permFour_pair : ∃ x y : Equiv.Perm (Fin 4), x ^ 3 = 1 ∧ x ≠ 1 ∧
    y ^ 3 = 1 ∧ y ≠ 1 ∧ x * y ≠ y * x ∧ x * y * x⁻¹ * y⁻¹ ≠ 1 ∧
      (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 0 1 * Equiv.swap 1 3, by decide⟩

theorem alternatingFive_pair : ∃ x y : alternatingGroup (Fin 5), x ^ 3 = 1 ∧ x ≠ 1 ∧
    y ^ 3 = 1 ∧ y ≠ 1 ∧ x * y ≠ y * x ∧ x * y * x⁻¹ * y⁻¹ ≠ 1 ∧
      (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    by decide⟩

theorem pair_of_mulEquiv {M X : Type*} [Group M] [Group X] (e : M ≃* X)
    (h : ∃ x y : X, x ^ 3 = 1 ∧ x ≠ 1 ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ x * y ≠ y * x ∧
      x * y * x⁻¹ * y⁻¹ ≠ 1 ∧ (x * y * x⁻¹ * y⁻¹) ^ 2 = 1) :
    ∃ x y : M, x ^ 3 = 1 ∧ x ≠ 1 ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ x * y ≠ y * x ∧
      x * y * x⁻¹ * y⁻¹ ≠ 1 ∧ (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 := by
  obtain ⟨x, y, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨e.symm x, e.symm y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · exact fun h => h2 (e.symm.injective (h.trans (map_one _).symm))
  · rw [← map_pow, h3, map_one]
  · exact fun h => h4 (e.symm.injective (h.trans (map_one _).symm))
  · intro h
    apply h5
    apply e.symm.injective
    simpa only [map_mul] using h
  · intro h
    apply h6
    apply e.symm.injective
    simpa only [map_mul, map_inv, map_one] using h
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, h7, map_one]

end CFSG.Glauberman.Dickson.MaxUp

namespace CFSG.Glauberman.Dickson.MaxUp

open BenderSuzuki.MatrixGroups CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open CFSG.GorensteinWalter

theorem card_alternatingFour' : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem card_permFour : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem card_alternatingFive' : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem card_psl2_galoisField {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : m ≠ 0) :
    Nat.card (PSL2MatrixGroup (GaloisField p m)) = p ^ m * (p ^ (2 * m) - 1) / 2 := by
  have hK : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
  have hodd : IsOddPrimePower (Nat.card (GaloisField p m)) :=
    ⟨p, m, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hm, hK⟩
  have := psl2_card_formula (GaloisField p m) hodd
  rw [hK, ← pow_mul, mul_comm m 2] at this
  exact this

theorem card_pgl2_galoisField {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0) :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) = p ^ m * (p ^ (2 * m) - 1) := by
  have hK : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
  have := pgl2_card_formula (GaloisField p m)
  rw [hK, ← pow_mul, mul_comm m 2] at this
  exact this

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem overgroup_shapes (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (K : Subgroup (PSL2MatrixGroup F)) :
    ((∃ m, Nat.card K = p ^ m) ∧ ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) ∨
    ((∃ z, Nat.card K = z ∧ (z ∣ (p ^ f + 1) / 2 ∨ z ∣ (p ^ f - 1) / 2)) ∧
      ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) ∨
    ((∃ z, Nat.card K = 2 * z ∧ (z ∣ (p ^ f + 1) / 2 ∨ z ∣ (p ^ f - 1) / 2)) ∧
      ∀ x ∈ K, ∀ y ∈ K, 2 < orderOf x → 2 < orderOf y → x * y = y * x) ∨
    (Nat.card K = 12 ∧ (∀ x ∈ K, orderOf x ∣ 2 ∨ orderOf x ∣ 3) ∧
      ∀ y ∈ K, ∀ t ∈ K, y ^ 3 = 1 → y ≠ 1 → t * y * t⁻¹ ≠ y⁻¹) ∨
    ((p ^ f) ^ 2 ≡ 1 [MOD 16] ∧ Nat.card K = 24 ∧ ∀ x ∈ K, orderOf x ∣ 3 ∨ orderOf x ∣ 4) ∨
    ((p = 5 ∨ (p ^ f) ^ 2 ≡ 1 [MOD 5]) ∧ Nat.card K = 60 ∧
      ∀ x ∈ K, orderOf x ∣ 2 ∨ orderOf x ∣ 3 ∨ orderOf x ∣ 5) ∨
    ((∃ m t, Nat.card K = p ^ m * t ∧ t ∣ (p ^ f - 1) / 2) ∧
      ∀ x ∈ K, ∀ y ∈ K, (x * y * x⁻¹ * y⁻¹) ^ p = 1) ∨
    (∃ m, m ≠ 0 ∧ m ∣ f ∧ Nat.card K = p ^ m * (p ^ (2 * m) - 1) / 2 ∧
      ∀ x ∈ K, orderOf x ≤ p ^ m + 1) ∨
    (∃ m, m ≠ 0 ∧ 2 * m ∣ f ∧ Nat.card K = p ^ m * (p ^ (2 * m) - 1) ∧
      ∀ x ∈ K, orderOf x ≤ p ^ m + 1) := by
  classical
  have hp' := hp.out
  have hodd : Odd (p ^ f) := (hp'.odd_of_ne_two hp2).pow
  have hgcd : Nat.gcd 2 (p ^ f - 1) = 2 := by
    obtain ⟨j, hj⟩ := hodd
    rw [hj, show 2 * j + 1 - 1 = 2 * j by omega]
    exact Nat.gcd_eq_left (dvd_mul_right 2 j)
  have hcommK : ∀ (hc : ∀ a b : K, a * b = b * a), ∀ x ∈ K, ∀ y ∈ K, x * y = y * x :=
    fun hc x hx y hy => congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩)
  rcases dickson_psl2_subgroup_list hF K with
    ⟨m, -, hmc, hel⟩ | ⟨z, hz, hcard, hcyc⟩ | ⟨z, -, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, ⟨e⟩⟩ |
      ⟨h5, ⟨e⟩⟩ | ⟨m, t, -, -, -, htq, E, C, hE, hEel, hEcard, hCcyc, hCcard, hdisj, hsup, -⟩ |
      ⟨m, hmf, ⟨e⟩⟩ | ⟨m, hmf, ⟨e⟩⟩
  · exact Or.inl ⟨⟨m, hmc⟩, hcommK (fun a b => hel.toIsMulCommutative.is_comm.comm a b)⟩
  · rw [hgcd] at hz
    exact Or.inr (Or.inl ⟨⟨z, hcard, hz⟩, hcommK (fun a b => hcyc.commGroup.mul_comm a b)⟩)
  · rw [hgcd] at hz
    refine Or.inr (Or.inr (Or.inl ⟨⟨z, ?_, hz⟩, ?_⟩))
    · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    · intro x hx y hy hxo hyo
      have h := commute_of_equiv_dihedral e (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)
        (by rwa [Subgroup.orderOf_mk]) (by rwa [Subgroup.orderOf_mk])
      exact congrArg Subtype.val h
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))
    · rw [Nat.card_congr e.toEquiv, card_alternatingFour']
    · intro x hx
      have := orderOf_dvd_of_equiv_alternating_four e ⟨x, hx⟩
      rwa [Subgroup.orderOf_mk] at this
    · intro y hy t ht hy3 hy1 hinv
      apply not_inverted_of_equiv_alternating_four e (y := ⟨y, hy⟩) (t := ⟨t, ht⟩)
      · exact Subtype.ext (by simpa using hy3)
      · exact fun h => hy1 (congrArg Subtype.val h)
      · exact Subtype.ext (by simpa using hinv)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h16, ?_, ?_⟩))))
    · rw [Nat.card_congr e.toEquiv, card_permFour]
    · intro x hx
      have := orderOf_dvd_of_equiv_perm_four e ⟨x, hx⟩
      rwa [Subgroup.orderOf_mk] at this
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, ?_, ?_⟩)))))
    · rw [Nat.card_congr e.toEquiv, card_alternatingFive']
    · intro x hx
      have := orderOf_dvd_of_equiv_alternating_five e ⟨x, hx⟩
      rwa [Subgroup.orderOf_mk] at this
  · rw [hgcd] at htq
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨m, t, ?_, htq⟩, ?_⟩))))))
    · have hcomp : E.IsComplement' C := by
        apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
        rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]
      rw [← hEcard, ← hCcard, hcomp.card_mul_card]
    · intro x hx y hy
      have hc := overgroup_comm_mem E C hCcyc hsup ⟨x, hx⟩ ⟨y, hy⟩
      have := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) _ hc
      exact congrArg Subtype.val this
  · have hm0 : m ≠ 0 := by
      rintro rfl
      exact BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
        (zero_dvd_iff.mp hmf)
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, hm0, hmf, ?_, ?_⟩)))))))
    · rw [Nat.card_congr e.toEquiv, card_psl2_galoisField hp2 hm0]
    · intro x hx
      have h := psl2_orderOf_le (GaloisField p m) (e ⟨x, hx⟩)
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, GaloisField.card p m hm0] at h
      exact h
  · have hm0 : m ≠ 0 := by
      rintro rfl
      exact BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
        (zero_dvd_iff.mp (by simpa using hmf))
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨m, hm0, hmf, ?_, ?_⟩)))))))
    · rw [Nat.card_congr e.toEquiv, card_pgl2_galoisField hm0]
    · intro x hx
      have h := pgl2_orderOf_le (GaloisField p m) (e ⟨x, hx⟩)
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, GaloisField.card p m hm0] at h
      exact h

end CFSG.Glauberman.Dickson.MaxUp

namespace CFSG.Glauberman.Dickson.MaxUp

open BenderSuzuki.MatrixGroups CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open CFSG.GorensteinWalter CFSG.PSL2Table

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem two_mul_le_of_dvd_of_ne {m f : ℕ} (hm : m ∣ f) (hmf : m ≠ f) (hf0 : f ≠ 0) :
    2 * m ≤ f := by
  obtain ⟨c, rfl⟩ := hm
  rcases c with _ | _ | c
  · simp at hf0
  · simp at hmf
  · nlinarith

theorem coprime_half_sub (hp2 : p ≠ 2) (hf0 : f ≠ 0) : Nat.Coprime p ((p ^ f - 1) / 2) := by
  have h := hq_coprime_split_order (p ^ f) (Nat.one_le_pow _ _ hp.out.pos)
  have hodd : Odd (p ^ f) := (hp.out.odd_of_ne_two hp2).pow
  have hgcd : Nat.gcd (p ^ f - 1) 2 = 2 := by
    obtain ⟨j, hj⟩ := hodd
    rw [hj, show 2 * j + 1 - 1 = 2 * j by omega]
    exact Nat.gcd_eq_right (dvd_mul_right 2 j)
  rw [hgcd] at h
  exact Nat.Coprime.coprime_dvd_left (dvd_pow_self p hf0) h

theorem coprime_half_add (hp2 : p ≠ 2) (hf0 : f ≠ 0) : Nat.Coprime p ((p ^ f + 1) / 2) := by
  have h := hq_coprime_nonsplit_order (p ^ f)
    (Nat.one_le_pow _ _ hp.out.pos)
  have hodd : Odd (p ^ f) := (hp.out.odd_of_ne_two hp2).pow
  have hgcd : Nat.gcd (p ^ f - 1) 2 = 2 := by
    obtain ⟨j, hj⟩ := hodd
    rw [hj, show 2 * j + 1 - 1 = 2 * j by omega]
    exact Nat.gcd_eq_right (dvd_mul_right 2 j)
  rw [hgcd] at h
  exact Nat.Coprime.coprime_dvd_left (dvd_pow_self p hf0) h

theorem card_psl2_odd (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) :
    Nat.card (PSL2MatrixGroup F) = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp.out, hp.out.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hf0, hF⟩
  rw [← hF]
  exact psl2_card_formula F hodd

theorem card_lt_of_ne_top {G : Type*} [Group G] [Finite G] {K : Subgroup G} (hK : K ≠ ⊤) :
    Nat.card K < Nat.card G := by
  rw [← Subgroup.card_top (G := G)]
  exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hK)

theorem two_mul_le_of_psl2_shape (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    {K : Subgroup (PSL2MatrixGroup F)} (hK : K ≠ ⊤) {m : ℕ} (hmf : m ∣ f)
    (hcard : Nat.card K = p ^ m * (p ^ (2 * m) - 1) / 2) : 2 * m ≤ f := by
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  apply two_mul_le_of_dvd_of_ne hmf _ hf0
  rintro rfl
  have h := card_lt_of_ne_top hK
  rw [hcard, card_psl2_odd hF hp2, ← pow_mul, mul_comm 2 m] at h
  exact lt_irrefl _ h

theorem no_overgroup_of_inverted
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (H K : Subgroup (PSL2MatrixGroup F)) (hHK : H < K) (hK : K ≠ ⊤)
    {u w : PSL2MatrixGroup F} (huH : u ∈ H) (hwH : w ∈ H) (hinv : w * u * w⁻¹ = u⁻¹)
    {n : ℕ} (hun : orderOf u = n) (hHcard : Nat.card H = 2 * n) (hn6 : 6 ≤ n)
    (hnp : Nat.Coprime p n)
    (hcase : (n = (p ^ f - 1) / 2 ∧ 13 ≤ p ^ f) ∨ n = (p ^ f + 1) / 2) : False := by
  have hp' := hp.out
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hp3 : 3 ≤ p := by have := hp'.two_le; omega
  have hodd : Odd (p ^ f) := (hp'.odd_of_ne_two hp2).pow
  obtain ⟨j, hj⟩ := hodd
  have hn1 : (p ^ f + 1) / 2 = (p ^ f - 1) / 2 + 1 := by omega
  have huK : u ∈ K := hHK.le huH
  have hwK : w ∈ K := hHK.le hwH
  have hHKcard : Nat.card H < Nat.card K := Subgroup.card_lt_of_lt hHK
  have hHKdvd : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hHK.le
  have hu2 : ¬ u ^ 2 = 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hun] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hcomm_false : ¬ w * u = u * w := by
    intro h
    apply hu2
    have : u⁻¹ = u := by rw [← hinv, h, mul_inv_cancel_right]
    rw [pow_two]
    calc u * u = u * u⁻¹ := by rw [this]
      _ = 1 := mul_inv_cancel u
  rcases overgroup_shapes hF hp2 K with
    ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨⟨z, hzc, hz⟩, -⟩ | ⟨-, hord, -⟩ | ⟨-, -, hord⟩ | ⟨-, -, hord⟩ |
      ⟨-, hcomm⟩ | ⟨m, hm0, hmf, hcard, hord⟩ | ⟨m, hm0, hmf, hcard, hord⟩
  · exact hcomm_false (hc w hwK u huK)
  · exact hcomm_false (hc w hwK u huK)
  · rw [hHcard, hzc] at hHKdvd hHKcard
    have hnz : n ∣ z := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp hHKdvd
    have hz0 : 0 < z := by omega
    have hnzle := Nat.le_of_dvd hz0 hnz
    have hzle : z ≤ n + 1 := by
      rcases hz with hz | hz
      · have := Nat.le_of_dvd (by omega) hz
        rcases hcase with ⟨rfl, -⟩ | rfl <;> omega
      · have := Nat.le_of_dvd (by omega) hz
        rcases hcase with ⟨rfl, -⟩ | rfl <;> omega
    obtain ⟨c, hc⟩ := hnz
    rcases c with _ | _ | c
    · omega
    · omega
    · nlinarith
  · rcases hord u huK with h | h <;> rw [hun] at h <;> have := Nat.le_of_dvd (by norm_num) h <;>
      omega
  · rcases hord u huK with h | h <;> rw [hun] at h <;> have := Nat.le_of_dvd (by norm_num) h <;>
      omega
  · rcases hord u huK with h | h | h <;> rw [hun] at h <;>
      have := Nat.le_of_dvd (by norm_num) h <;> omega
  · have h := hcomm w hwK u huK
    have e : w * u * w⁻¹ * u⁻¹ = (u ^ 2)⁻¹ := by rw [hinv, pow_two, mul_inv_rev]
    rw [e, inv_pow, inv_eq_one, ← pow_mul] at h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hun] at this
    have h2 : n ∣ 2 := (Nat.Coprime.dvd_of_dvd_mul_right hnp.symm this)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · have h2m := two_mul_le_of_psl2_shape hF hp2 hK hmf hcard
    have hpow : (p ^ m) ^ 2 ≤ p ^ f := by
      rw [← pow_mul, mul_comm]
      exact Nat.pow_le_pow_right hp'.pos h2m
    have hle := hord u huK
    rw [hun] at hle
    have hpm : 3 ≤ p ^ m := le_trans hp3 (Nat.le_self_pow hm0 p)
    have hjm : (p ^ f - 1) / 2 = j := by omega
    have hjp : (p ^ f + 1) / 2 = j + 1 := by omega
    rw [hj] at hpow
    rcases hcase with ⟨rfl, h13⟩ | rfl
    · rw [hjm] at hle
      nlinarith
    · rw [hjp] at hle
      nlinarith
  · have h2m : 2 * m ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hmf
    have hpow : (p ^ m) ^ 2 ≤ p ^ f := by
      rw [← pow_mul, mul_comm]
      exact Nat.pow_le_pow_right hp'.pos h2m
    have hle := hord u huK
    rw [hun] at hle
    have hpm : 3 ≤ p ^ m := le_trans hp3 (Nat.le_self_pow hm0 p)
    have hjm : (p ^ f - 1) / 2 = j := by omega
    have hjp : (p ^ f + 1) / 2 = j + 1 := by omega
    rw [hj] at hpow
    rcases hcase with ⟨rfl, h13⟩ | rfl
    · rw [hjm] at hle
      nlinarith
    · rw [hjp] at hle
      nlinarith

end CFSG.Glauberman.Dickson.MaxUp

namespace CFSG.Glauberman.Dickson.MaxUp

open BenderSuzuki.MatrixGroups CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open CFSG.GorensteinWalter CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem ringChar_ne_two (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) : ringChar F ≠ 2 := by
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by simpa using hF)
  rw [ringChar.eq F p]
  exact hp2

theorem ne_top_of_card_lt {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (h : Nat.card H < Nat.card G) : H ≠ ⊤ := by
  rintro rfl
  rw [Subgroup.card_top] at h
  exact lt_irrefl _ h

theorem half_lt_card_psl2 {q n : ℕ} (hq : 5 ≤ q) (hn : n ≤ q + 1) : n < q * (q ^ 2 - 1) / 2 := by
  rw [Nat.lt_div_iff_mul_lt (by norm_num)]
  have h1 : 24 ≤ q ^ 2 - 1 := by
    have : 25 ≤ q ^ 2 := by nlinarith
    omega
  have h2 : q * 24 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul_left q h1
  omega

theorem coatom_of_forall {G : Type*} [Group G] {H : Subgroup G} (hH : H ≠ ⊤)
    (h : ∀ K : Subgroup G, H < K → K ≠ ⊤ → False) : IsCoatom H :=
  ⟨hH, fun K hK => by_contra (h K hK)⟩

theorem isCoatom_normalizer_splitTorus
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h13 : 13 ≤ p ^ f) :
    IsCoatom (Subgroup.normalizer (splitTorus F : Set (PSL2MatrixGroup F))) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hF2 := ringChar_ne_two hF hp2
  have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hq5 : 5 ≤ Fintype.card F := by omega
  have : IsCyclic (splitTorus F) := splitTorus_isCyclic
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := splitTorus F)
  have hTcard := card_splitTorus_eq hF2 (F := F)
  rw [hq] at hTcard
  have hNcard : Nat.card (Subgroup.normalizer (splitTorus F : Set (PSL2MatrixGroup F))) =
      2 * ((p ^ f - 1) / 2) := by
    rw [card_normalizer_splitTorus hF2 hq5, hTcard]
  have hodd : Odd (p ^ f) := (hp.out.odd_of_ne_two hp2).pow
  obtain ⟨j, hj⟩ := hodd
  apply coatom_of_forall
  · apply ne_top_of_card_lt
    rw [hNcard, card_psl2_odd hF hp2]
    exact half_lt_card_psl2 (by omega) (by omega)
  · intro K hHK hK
    apply no_overgroup_of_inverted hF hp2 _ K hHK hK
      (u := (u : PSL2MatrixGroup F)) (w := splitWeyl F)
      (Subgroup.le_normalizer u.2) (by
        rw [normalizer_splitTorus_eq hF2 hq5]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      (splitWeyl_conj u.2) (n := (p ^ f - 1) / 2) (by rw [Subgroup.orderOf_coe, hu, hTcard])
      hNcard (by omega) (coprime_half_sub hp2 hf0) (Or.inl ⟨rfl, h13⟩)

end CFSG.Glauberman.Dickson.MaxUp

namespace CFSG.Glauberman.Dickson.MaxUp

open BenderSuzuki.MatrixGroups CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open CFSG.GorensteinWalter CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem eq_five_of_pow_eq_five {p f : ℕ} (hp : p.Prime) (h : p ^ f = 5) : p = 5 ∧ f = 1 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h
  have hp5 : p = 5 := by
    have hdvd : p ∣ 5 := h ▸ dvd_pow_self p hf0
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hdvd
  subst hp5
  have h' : 5 ^ f = 5 ^ 1 := by rw [h]; norm_num
  exact ⟨rfl, Nat.pow_right_injective (by norm_num) h'⟩

theorem isCoatom_normalizer_nonsplitTorus
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (hq5 : 5 ≤ p ^ f) (h7 : p ^ f ≠ 7) (h9 : p ^ f ≠ 9) {ν : F} (hν : ¬ IsSquare ν) :
    IsCoatom (Subgroup.normalizer (nonsplitTorus ν : Set (PSL2MatrixGroup F))) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hF2 := ringChar_ne_two hF hp2
  have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hq5' : 5 ≤ Fintype.card F := by omega
  have : IsCyclic (nonsplitTorus ν) := nonsplitTorus_isCyclic hν
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := nonsplitTorus ν)
  have hScard := card_nonsplitTorus_eq hF2 hν
  rw [hq] at hScard
  obtain ⟨w, hwS, hww, hinv, hNeq⟩ := normalizer_nonsplitTorus_eq hF2 hq5' hν
  have hNcard : Nat.card (Subgroup.normalizer (nonsplitTorus ν : Set (PSL2MatrixGroup F))) =
      2 * ((p ^ f + 1) / 2) := by
    rw [card_normalizer_nonsplitTorus hF2 hq5' hν, hScard]
  have hodd : Odd (p ^ f) := (hp.out.odd_of_ne_two hp2).pow
  obtain ⟨j, hj⟩ := hodd
  have huN : (u : PSL2MatrixGroup F) ∈
      Subgroup.normalizer (nonsplitTorus ν : Set (PSL2MatrixGroup F)) := Subgroup.le_normalizer u.2
  have hwN : w ∈ Subgroup.normalizer (nonsplitTorus ν : Set (PSL2MatrixGroup F)) := by
    rw [hNeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have huord : orderOf (u : PSL2MatrixGroup F) = (p ^ f + 1) / 2 := by
    rw [Subgroup.orderOf_coe, hu, hScard]
  apply coatom_of_forall
  · apply ne_top_of_card_lt
    rw [hNcard, card_psl2_odd hF hp2]
    exact half_lt_card_psl2 hq5 (by omega)
  · intro K hHK hK
    by_cases h11 : 11 ≤ p ^ f
    · exact no_overgroup_of_inverted hF hp2 _ K hHK hK huN hwN (hinv _ u.2) huord hNcard
        (by omega) (coprime_half_add hp2 hf0) (Or.inr rfl)
    have hq5eq : p ^ f = 5 := by
      have hodd' : Odd (p ^ f) := (hp.out.odd_of_ne_two hp2).pow
      obtain ⟨k, hk⟩ := hodd'
      omega
    obtain ⟨rfl, rfl⟩ := eq_five_of_pow_eq_five hp.out hq5eq
    have huK : (u : PSL2MatrixGroup F) ∈ K := hHK.le huN
    have hwK : w ∈ K := hHK.le hwN
    have hu3 : (u : PSL2MatrixGroup F) ^ 3 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, huord]
      norm_num
    have hu1 : (u : PSL2MatrixGroup F) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at huord
      norm_num at huord
    have hcomm_false : ¬ w * (u : PSL2MatrixGroup F) = u * w := by
      intro h
      have h' := hinv _ u.2
      rw [h, mul_inv_cancel_right] at h'
      have : (u : PSL2MatrixGroup F) ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 2 [h']
        exact mul_inv_cancel _
      have := orderOf_dvd_of_pow_eq_one this
      rw [huord] at this
      norm_num at this
    have hHKcard : Nat.card _ < Nat.card K := Subgroup.card_lt_of_lt hHK
    have hKG := card_lt_of_ne_top hK
    have h60' : 5 ^ 1 * ((5 ^ 1) ^ 2 - 1) / 2 = 60 := by norm_num
    rw [card_psl2_odd hF hp2, h60'] at hKG
    have h6' : 2 * ((5 ^ 1 + 1) / 2) = 6 := by norm_num
    rw [hNcard, h6'] at hHKcard
    rcases overgroup_shapes hF hp2 K with
      ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨⟨z, hzc, hz⟩, -⟩ | ⟨-, -, hninv⟩ | ⟨h16, -, -⟩ | ⟨-, h60, -⟩ |
        ⟨-, hcomm⟩ | ⟨m, hm0, hmf, hcard, -⟩ | ⟨m, hm0, hmf, -, -⟩
    · exact hcomm_false (hc w hwK _ huK)
    · exact hcomm_false (hc w hwK _ huK)
    · norm_num at hz
      rcases hz with hz | hz
      · have := Nat.le_of_dvd (by norm_num) hz
        omega
      · have := Nat.le_of_dvd (by norm_num) hz
        omega
    · exact hninv _ huK w hwK hu3 hu1 (hinv _ u.2)
    · norm_num [Nat.ModEq] at h16
    · omega
    · have h := hcomm w hwK _ huK
      have e : w * (u : PSL2MatrixGroup F) * w⁻¹ * (u : PSL2MatrixGroup F)⁻¹ =
          ((u : PSL2MatrixGroup F) ^ 2)⁻¹ := by
        rw [hinv _ u.2, pow_two, mul_inv_rev]
      rw [e, inv_pow, inv_eq_one, ← pow_mul] at h
      have := orderOf_dvd_of_pow_eq_one h
      rw [huord] at this
      norm_num at this
    · have := two_mul_le_of_psl2_shape hF hp2 hK hmf hcard
      omega
    · have := Nat.le_of_dvd (by norm_num) hmf
      omega

end CFSG.Glauberman.Dickson.MaxUp

namespace CFSG.Glauberman.Dickson.MaxUp

open BenderSuzuki.MatrixGroups CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open CFSG.GorensteinWalter CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem exotic_overgroup_shapes (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (K : Subgroup (PSL2MatrixGroup F)) {x y : PSL2MatrixGroup F} (hxK : x ∈ K) (hyK : y ∈ K)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hxy : x * y ≠ y * x)
    (hc1 : x * y * x⁻¹ * y⁻¹ ≠ 1) (hc2 : (x * y * x⁻¹ * y⁻¹) ^ 2 = 1) :
    (Nat.card K = 12) ∨ ((p ^ f) ^ 2 ≡ 1 [MOD 16] ∧ Nat.card K = 24) ∨
    ((p = 5 ∨ (p ^ f) ^ 2 ≡ 1 [MOD 5]) ∧ Nat.card K = 60) ∨
    (∃ m, m ≠ 0 ∧ m ∣ f ∧ Nat.card K = p ^ m * (p ^ (2 * m) - 1) / 2) ∨
    (∃ m, m ≠ 0 ∧ 2 * m ∣ f ∧ Nat.card K = p ^ m * (p ^ (2 * m) - 1)) := by
  have hp' := hp.out
  have hxo : orderOf x = 3 := orderOf_eq_prime (p := 3) hx3 hx1
  have hyo : orderOf y = 3 := orderOf_eq_prime (p := 3) hy3 hy1
  rcases overgroup_shapes hF hp2 K with
    ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨h12, -, -⟩ | ⟨h16, h24, -⟩ | ⟨h5, h60, -⟩ |
      ⟨-, hcomm⟩ | ⟨m, hm0, hmf, hcard, -⟩ | ⟨m, hm0, hmf, hcard, -⟩
  · exact absurd (hc x hxK y hyK) hxy
  · exact absurd (hc x hxK y hyK) hxy
  · exact absurd (hc x hxK y hyK (by omega) (by omega)) hxy
  · exact Or.inl h12
  · exact Or.inr (Or.inl ⟨h16, h24⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h5, h60⟩))
  · exfalso
    have hcp := hcomm x hxK y hyK
    have h1 := orderOf_dvd_of_pow_eq_one hcp
    have h2 := orderOf_dvd_of_pow_eq_one hc2
    have h3 : orderOf (x * y * x⁻¹ * y⁻¹) ∣ Nat.gcd p 2 := Nat.dvd_gcd h1 h2
    rw [(Nat.coprime_primes hp' Nat.prime_two).mpr hp2] at h3
    exact hc1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm0, hmf, hcard⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m, hm0, hmf, hcard⟩)))

omit [Finite F] in
theorem exists_pair_of_mulEquiv {H : Subgroup (PSL2MatrixGroup F)} {X : Type*} [Group X]
    (e : H ≃* X) (hX : ∃ x y : X, x ^ 3 = 1 ∧ x ≠ 1 ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ x * y ≠ y * x ∧
      x * y * x⁻¹ * y⁻¹ ≠ 1 ∧ (x * y * x⁻¹ * y⁻¹) ^ 2 = 1) :
    ∃ x ∈ H, ∃ y ∈ H, x ^ 3 = 1 ∧ x ≠ 1 ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ x * y ≠ y * x ∧
      x * y * x⁻¹ * y⁻¹ ≠ 1 ∧ (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 := by
  obtain ⟨x, y, h1, h2, h3, h4, h5, h6, h7⟩ := pair_of_mulEquiv e hX
  refine ⟨x, x.2, y, y.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  · exact fun h => h2 (Subtype.ext h)
  · rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
  · exact fun h => h4 (Subtype.ext h)
  · exact fun h => h5 (Subtype.ext h)
  · exact fun h => h6 (Subtype.ext h)
  · have := congrArg Subtype.val h7
    simpa using this

theorem lt_card_psl2_of {q n : ℕ} (h : 2 * n + 2 ≤ q * (q ^ 2 - 1)) :
    n < q * (q ^ 2 - 1) / 2 :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega))

theorem le_mul_sq_sub_one {q : ℕ} (hq : 9 ≤ q) : 720 ≤ q * (q ^ 2 - 1) := by
  have h1 : 80 ≤ q ^ 2 - 1 := by
    have : 81 ≤ q ^ 2 := by nlinarith
    omega
  calc 720 = 9 * 80 := by norm_num
    _ ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq h1

theorem not_five_dvd_of_mod_ten {p : ℕ} (hp : p % 10 = 3 ∨ p % 10 = 7) :
    ¬ 5 ∣ p * (p ^ 2 - 1) := by
  intro h
  have h0 := Nat.mod_eq_zero_of_dvd h
  rw [Nat.mul_mod] at h0
  have hs := Nat.pow_mod p 2 5
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  rcases hp with hp | hp
  · have h5 : p % 5 = 3 := by omega
    rw [h5] at hs
    norm_num at hs
    have : (p ^ 2 - 1) % 5 = 3 := by omega
    rw [h5, this] at h0
    norm_num at h0
  · have h5 : p % 5 = 2 := by omega
    rw [h5] at hs
    norm_num at hs
    have : (p ^ 2 - 1) % 5 = 3 := by omega
    rw [h5, this] at h0
    norm_num at h0

theorem isCoatom_of_mulEquiv_alternatingFive
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (hcond : (f = 1 ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∨
      (f = 2 ∧ (p ≡ 3 [MOD 10] ∨ p ≡ 7 [MOD 10])))
    {H : Subgroup (PSL2MatrixGroup F)} (e : H ≃* alternatingGroup (Fin 5)) : IsCoatom H := by
  have hp' := hp.out
  have hH : Nat.card H = 60 := by rw [Nat.card_congr e.toEquiv, card_alternatingFive']
  obtain ⟨x, hx, y, hy, hx3, hx1, hy3, hy1, hxy, hc1, hc2⟩ :=
    exists_pair_of_mulEquiv e alternatingFive_pair
  have hq9 : 9 ≤ p ^ f := by
    rcases hcond with ⟨rfl, h | h⟩ | ⟨rfl, -⟩
    · have h' : p % 10 = 1 := h
      have : p ≠ 1 := hp'.one_lt.ne'
      simp only [pow_one]
      omega
    · have h' : p % 10 = 9 := h
      simp only [pow_one]
      omega
    · have : 3 ≤ p := by have := hp'.two_le; omega
      nlinarith
  have hG : 60 < Nat.card (PSL2MatrixGroup F) := by
    rw [card_psl2_odd hF hp2]
    apply lt_card_psl2_of
    have := le_mul_sq_sub_one hq9
    omega
  apply coatom_of_forall (ne_top_of_card_lt (by omega))
  intro K hHK hK
  have hHKc : 60 < Nat.card K := hH ▸ Subgroup.card_lt_of_lt hHK
  have hHKd : 60 ∣ Nat.card K := hH ▸ Subgroup.card_dvd_of_le hHK.le
  rcases exotic_overgroup_shapes hF hp2 K (hHK.le hx) (hHK.le hy) hx3 hx1 hy3 hy1 hxy hc1 hc2
    with h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨m, hm0, hmf, hcard⟩ | ⟨m, hm0, hmf, hcard⟩
  · omega
  · omega
  · omega
  · have h2m := two_mul_le_of_psl2_shape hF hp2 hK hmf hcard
    rcases hcond with ⟨rfl, -⟩ | ⟨rfl, hp10⟩
    · omega
    · have hm1 : m = 1 := by omega
      subst hm1
      rw [hcard] at hHKd
      have hp10' : p % 10 = 3 ∨ p % 10 = 7 := hp10
      apply not_five_dvd_of_mod_ten hp10'
      have h5 : 5 ∣ p ^ 1 * (p ^ (2 * 1) - 1) / 2 := dvd_trans (by norm_num) hHKd
      simp only [pow_one, mul_one] at h5
      have h2 : 2 ∣ p * (p ^ 2 - 1) :=
        Dvd.dvd.mul_left (Nat.Odd.sub_odd (hp'.odd_of_ne_two hp2).pow odd_one).two_dvd p
      exact dvd_trans h5 (Nat.div_dvd_of_dvd h2)
  · rcases hcond with ⟨rfl, -⟩ | ⟨rfl, hp10⟩
    · have := Nat.le_of_dvd (by norm_num) hmf
      omega
    · have hm1 : m = 1 := by
        have := Nat.le_of_dvd (by norm_num) hmf
        omega
      subst hm1
      rw [hcard] at hHKd
      have hp10' : p % 10 = 3 ∨ p % 10 = 7 := hp10
      apply not_five_dvd_of_mod_ten hp10'
      have h5 : 5 ∣ p ^ 1 * (p ^ (2 * 1) - 1) := dvd_trans (by norm_num) hHKd
      simpa using h5

end CFSG.Glauberman.Dickson.MaxUp

namespace CFSG.Glauberman.Dickson.MaxUp

open BenderSuzuki.MatrixGroups CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open CFSG.GorensteinWalter CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem sq_mod_sixteen_of_mod_eight {p : ℕ} (hp : p % 8 = 3 ∨ p % 8 = 5) : p ^ 2 % 16 = 9 := by
  have h := Nat.pow_mod p 2 16
  have hlt : p % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have h8 : p % 8 = (p % 16) % 8 := (Nat.mod_mod_of_dvd _ (by norm_num)).symm
  rw [h]
  interval_cases hr : p % 16 <;> omega

theorem sq_mod_five_of_mod_ten {p : ℕ} (hp2 : p % 2 = 1) (h : p ^ 2 % 5 = 1) :
    p % 10 = 1 ∨ p % 10 = 9 := by
  have h' := Nat.pow_mod p 2 5
  have hlt : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rw [h'] at h
  interval_cases hr : p % 5 <;> omega

theorem isCoatom_of_mulEquiv_alternatingFour
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (hq5 : 5 ≤ p ^ f) (hf : f = 1) (h8 : p ≡ 3 [MOD 8] ∨ p ≡ 5 [MOD 8])
    (h10 : ¬ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]))
    {H : Subgroup (PSL2MatrixGroup F)} (e : H ≃* alternatingGroup (Fin 4)) : IsCoatom H := by
  subst hf
  have hp' := hp.out
  have hH : Nat.card H = 12 := by rw [Nat.card_congr e.toEquiv, card_alternatingFour']
  obtain ⟨x, hx, y, hy, hx3, hx1, hy3, hy1, hxy, hc1, hc2⟩ :=
    exists_pair_of_mulEquiv e alternatingFour_pair
  have hG : 12 < Nat.card (PSL2MatrixGroup F) := by
    rw [card_psl2_odd hF hp2]
    apply lt_card_psl2_of
    have h1 : 24 ≤ (p ^ 1) ^ 2 - 1 := by
      have : 25 ≤ (p ^ 1) ^ 2 := by nlinarith
      omega
    have := Nat.mul_le_mul hq5 h1
    omega
  apply coatom_of_forall (ne_top_of_card_lt (by omega))
  intro K hHK hK
  have hHKc : 12 < Nat.card K := hH ▸ Subgroup.card_lt_of_lt hHK
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp'.odd_of_ne_two hp2)
  rcases exotic_overgroup_shapes hF hp2 K (hHK.le hx) (hHK.le hy) hx3 hx1 hy3 hy1 hxy hc1 hc2
    with h | ⟨h16, -⟩ | ⟨h5, h60⟩ | ⟨m, hm0, hmf, hcard⟩ | ⟨m, hm0, hmf, hcard⟩
  · omega
  · have h16' : (p ^ 1) ^ 2 % 16 = 1 := h16
    rw [pow_one, sq_mod_sixteen_of_mod_eight (by rcases h8 with h | h <;> [left; right] <;>
      exact h)] at h16'
    omega
  · rcases h5 with rfl | h5
    · have hKG := card_lt_of_ne_top hK
      rw [card_psl2_odd hF hp2, h60] at hKG
      norm_num at hKG
    · have h5' : (p ^ 1) ^ 2 % 5 = 1 := h5
      rw [pow_one] at h5'
      exact h10 (sq_mod_five_of_mod_ten hpodd h5')
  · have := two_mul_le_of_psl2_shape hF hp2 hK hmf hcard
    omega
  · have := Nat.le_of_dvd (by norm_num) hmf
    omega

theorem isCoatom_of_mulEquiv_permFour
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (hq5 : 5 ≤ p ^ f) (hf : f = 1)
    {H : Subgroup (PSL2MatrixGroup F)} (e : H ≃* Equiv.Perm (Fin 4)) : IsCoatom H := by
  subst hf
  have hH : Nat.card H = 24 := by rw [Nat.card_congr e.toEquiv, card_permFour]
  obtain ⟨x, hx, y, hy, hx3, hx1, hy3, hy1, hxy, hc1, hc2⟩ :=
    exists_pair_of_mulEquiv e permFour_pair
  have hG : 24 < Nat.card (PSL2MatrixGroup F) := by
    rw [card_psl2_odd hF hp2]
    apply lt_card_psl2_of
    have h1 : 24 ≤ (p ^ 1) ^ 2 - 1 := by
      have : 25 ≤ (p ^ 1) ^ 2 := by nlinarith
      omega
    have := Nat.mul_le_mul hq5 h1
    omega
  apply coatom_of_forall (ne_top_of_card_lt (by omega))
  intro K hHK hK
  have hHKc : 24 < Nat.card K := hH ▸ Subgroup.card_lt_of_lt hHK
  have hHKd : 24 ∣ Nat.card K := hH ▸ Subgroup.card_dvd_of_le hHK.le
  rcases exotic_overgroup_shapes hF hp2 K (hHK.le hx) (hHK.le hy) hx3 hx1 hy3 hy1 hxy hc1 hc2
    with h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨m, hm0, hmf, hcard⟩ | ⟨m, hm0, hmf, hcard⟩
  · omega
  · omega
  · rw [h] at hHKd
    norm_num at hHKd
  · have := two_mul_le_of_psl2_shape hF hp2 hK hmf hcard
    omega
  · have := Nat.le_of_dvd (by norm_num) hmf
    omega

end CFSG.Glauberman.Dickson.MaxUp

namespace CFSG.Glauberman.Dickson.MaxUp

open BenderSuzuki.MatrixGroups CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open CFSG.GorensteinWalter CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

omit hp in
theorem two_dvd_pow_sub_one (hpodd : Odd p) (k : ℕ) : 2 ∣ p ^ k - 1 :=
  (Nat.Odd.sub_odd hpodd.pow odd_one).two_dvd

theorem coprime_pow_sub_one {k : ℕ} (hk : k ≠ 0) : Nat.Coprime p (p ^ k - 1) := by
  have h1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.out.pos
  have : Nat.Coprime (p ^ k) (p ^ k - 1) :=
    (Nat.coprime_self_sub_right h1).mpr (Nat.coprime_one_right _)
  exact Nat.Coprime.coprime_dvd_left (dvd_pow_self p hk) this

theorem coprime_pow_sub_one_half (hpodd : Odd p) {k : ℕ} (hk : k ≠ 0) :
    Nat.Coprime p ((p ^ k - 1) / 2) :=
  Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd (two_dvd_pow_sub_one hpodd k))
    (coprime_pow_sub_one hk)

theorem dvd_of_half_dvd (hpodd : Odd p) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (p ^ (2 * a) - 1) / 2 ∣ p ^ (2 * b) - 1) : a ∣ b := by
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    rcases hpodd with ⟨k, hk⟩
    omega
  set g := Nat.gcd (2 * a) (2 * b) with hg
  have hA : (p ^ (2 * a) - 1) / 2 ∣ p ^ (2 * a) - 1 :=
    Nat.div_dvd_of_dvd (two_dvd_pow_sub_one hpodd _)
  have hgcd : Nat.gcd (p ^ (2 * a) - 1) (p ^ (2 * b) - 1) = p ^ g - 1 :=
    Nat.pow_sub_one_gcd_pow_sub_one p (2 * a) (2 * b)
  have hAg : (p ^ (2 * a) - 1) / 2 ∣ p ^ g - 1 := hgcd ▸ Nat.dvd_gcd hA h
  have hg2a : g ∣ 2 * a := Nat.gcd_dvd_left _ _
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_left (by omega)
  by_cases hgeq : g = 2 * a
  · have : 2 * a ∣ 2 * b := hgeq ▸ Nat.gcd_dvd_right _ _
    exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp this
  · exfalso
    have hgle : g ≤ a := by
      obtain ⟨c, hc⟩ := hg2a
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith
    have hpg : p ^ g ≤ p ^ a := Nat.pow_le_pow_right hp.out.pos hgle
    have hpa : 3 ≤ p ^ a := le_trans hp3 (Nat.le_self_pow ha p)
    have hpg3 : 3 ≤ p ^ g := le_trans hp3 (Nat.le_self_pow hg0 p)
    have hle := Nat.le_of_dvd (by omega) hAg
    have h2a : p ^ (2 * a) = p ^ a * p ^ a := by rw [two_mul, pow_add]
    rw [h2a] at hle
    have : p ^ a * p ^ a - 1 ≥ 2 * (p ^ a - 1) + 2 * (p ^ a - 1) + 2 := by
      have : p ^ a * p ^ a ≥ 3 * p ^ a := Nat.mul_le_mul_right _ hpa
      omega
    omega

theorem nine_pow_odd {r : ℕ} (hr : Odd r) : 9 ^ r % 16 = 9 ∧ 9 ^ r % 5 = 4 := by
  obtain ⟨k, rfl⟩ := hr
  rw [pow_succ, pow_mul]
  constructor
  · rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  · rw [Nat.mul_mod, Nat.pow_mod]
    norm_num

end CFSG.Glauberman.Dickson.MaxUp

namespace CFSG.Glauberman.Dickson.MaxUp

open BenderSuzuki.MatrixGroups CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open CFSG.GorensteinWalter CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem not_dvd_of_dvd_half (hp2 : p ≠ 2) (hf0 : f ≠ 0) {z : ℕ}
    (hz : z ∣ (p ^ f + 1) / 2 ∨ z ∣ (p ^ f - 1) / 2) : ¬ p ∣ 2 * z := by
  intro h
  have hpz : p ∣ z := (Nat.Coprime.dvd_of_dvd_mul_left
    ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2) h)
  rcases hz with hz | hz
  · have := Nat.Coprime.eq_one_of_dvd (coprime_half_add hp2 hf0) (dvd_trans hpz hz)
    exact hp.out.one_lt.ne' this
  · have := Nat.Coprime.eq_one_of_dvd (coprime_half_sub hp2 hf0) (dvd_trans hpz hz)
    exact hp.out.one_lt.ne' this

theorem isCoatom_of_mulEquiv_pgl2
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) {m : ℕ}
    (hf : f = 2 * m) {H : Subgroup (PSL2MatrixGroup F)}
    (e : H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) : IsCoatom H := by
  have hp' := hp.out
  have hpodd : Odd p := hp'.odd_of_ne_two hp2
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hm0 : m ≠ 0 := by omega
  have hp3 : 3 ≤ p := by have := hp'.two_le; rcases hpodd with ⟨k, hk⟩; omega
  have hr3 : 3 ≤ p ^ m := le_trans hp3 (Nat.le_self_pow hm0 p)
  have hq : p ^ f = (p ^ m) ^ 2 := by rw [hf, ← pow_mul, mul_comm]
  have hH : Nat.card H = p ^ m * ((p ^ m) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, card_pgl2_galoisField hm0, ← pow_mul, mul_comm m 2]
  have hG := card_psl2_odd hF hp2
  rw [hq] at hG
  set r := p ^ m with hr
  have hr2 : 8 ≤ r ^ 2 - 1 := by
    have : 9 ≤ r ^ 2 := by nlinarith
    omega
  have hpN : p ∣ Nat.card H := hH ▸ dvd_mul_of_dvd_left (dvd_pow_self p hm0) _
  have hcop : Nat.Coprime p (r ^ 2 - 1) := by
    rw [hr, ← pow_mul]
    exact coprime_pow_sub_one (by omega)
  apply coatom_of_forall
  · apply ne_top_of_card_lt
    rw [hH, hG]
    apply lt_card_psl2_of
    obtain ⟨s, hs⟩ : ∃ s, r ^ 2 = s + 1 := ⟨r ^ 2 - 1, by omega⟩
    have hs8 : 8 ≤ s := by omega
    have e1 : (r ^ 2) ^ 2 - 1 = s * (s + 2) := by
      rw [hs]
      have : (s + 1) ^ 2 = s * (s + 2) + 1 := by ring
      omega
    have e2 : r ^ 2 - 1 = s := by omega
    rw [e1, e2, hs]
    have hrs : r ≤ s + 1 := by nlinarith
    nlinarith
  intro K hHK hK
  have hHKc : Nat.card H < Nat.card K := Subgroup.card_lt_of_lt hHK
  have hHKd : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hHK.le
  rcases overgroup_shapes hF hp2 K with
    ⟨⟨m', hm'⟩, -⟩ | ⟨⟨z, hzc, hz⟩, -⟩ | ⟨⟨z, hzc, hz⟩, -⟩ | ⟨h12, -⟩ | ⟨-, h24, -⟩ | ⟨-, h60, -⟩ |
      ⟨⟨m', t, hKc, ht⟩, -⟩ | ⟨m', hm'0, hm'f, hcard, -⟩ | ⟨m', hm'0, hm'f, hcard, -⟩
  · rw [hm', hH] at hHKd
    have h1 : r ^ 2 - 1 ∣ p ^ m' := dvd_trans (dvd_mul_left _ _) hHKd
    have h2 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right m' hcop.symm) h1
    omega
  · rw [hzc] at hHKd
    exact not_dvd_of_dvd_half hp2 hf0 hz (dvd_trans (dvd_trans hpN hHKd) (dvd_mul_left z 2))
  · rw [hzc] at hHKd
    exact not_dvd_of_dvd_half hp2 hf0 hz (dvd_trans hpN hHKd)
  · rw [hH, h12] at hHKc
    nlinarith
  · rw [hH, h24] at hHKc
    nlinarith
  · rw [hH, h60] at hHKc hHKd
    by_cases hr5 : 5 ≤ r
    · have : 24 ≤ r ^ 2 - 1 := by
        have : 25 ≤ r ^ 2 := by nlinarith
        omega
      nlinarith
    · have hr3' : r = 3 := by
        have : Odd r := hpodd.pow
        rcases this with ⟨k, hk⟩
        omega
      rw [hr3'] at hHKd
      norm_num at hHKd
  · rw [hKc, hH] at hHKd
    have h1 : r ^ 2 - 1 ∣ p ^ m' * t := dvd_trans (dvd_mul_left _ _) hHKd
    have h2 : r ^ 2 - 1 ∣ t := (Nat.Coprime.pow_right m' hcop.symm).dvd_of_dvd_mul_left h1
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hKc
      exact Nat.card_pos.ne' hKc
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) h2
    have h4 := Nat.le_of_dvd (by
      rw [hq]
      have : 9 ≤ r ^ 2 := by nlinarith
      omega) ht
    rw [hq] at h4
    omega
  · have h2m := two_mul_le_of_psl2_shape hF hp2 hK hm'f hcard
    have hm'm : m' ≤ m := by omega
    have h1 : p ^ m' ≤ r := Nat.pow_le_pow_right hp'.pos hm'm
    have h2 : p ^ (2 * m') ≤ r ^ 2 := by
      rw [hr, ← pow_mul, mul_comm m 2]
      exact Nat.pow_le_pow_right hp'.pos (by omega)
    rw [hcard, hH] at hHKc
    have h3 : p ^ m' * (p ^ (2 * m') - 1) ≤ r * (r ^ 2 - 1) :=
      Nat.mul_le_mul h1 (by omega)
    have h4 : p ^ m' * (p ^ (2 * m') - 1) / 2 ≤ p ^ m' * (p ^ (2 * m') - 1) := Nat.div_le_self _ _
    omega
  · have hm'm : m' ≤ m := by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hm'f
      omega
    have h1 : p ^ m' ≤ r := Nat.pow_le_pow_right hp'.pos hm'm
    have h2 : p ^ (2 * m') ≤ r ^ 2 := by
      rw [hr, ← pow_mul, mul_comm m 2]
      exact Nat.pow_le_pow_right hp'.pos (by omega)
    rw [hcard, hH] at hHKc
    have h3 : p ^ m' * (p ^ (2 * m') - 1) ≤ r * (r ^ 2 - 1) :=
      Nat.mul_le_mul h1 (by omega)
    omega

end CFSG.Glauberman.Dickson.MaxUp

namespace CFSG.Glauberman.Dickson.MaxUp

open BenderSuzuki.MatrixGroups CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open CFSG.GorensteinWalter CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem eq_three_of_pow_eq_three {p m : ℕ} (hp : p.Prime) (h : p ^ m = 3) : p = 3 ∧ m = 1 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at h
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 := h ▸ dvd_pow_self p hm0
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
  subst hp3
  have h' : 3 ^ m = 3 ^ 1 := by rw [h]; norm_num
  exact ⟨rfl, Nat.pow_right_injective (by norm_num) h'⟩

theorem isCoatom_of_mulEquiv_psl2
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) {m r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hf : f = m * r) {H : Subgroup (PSL2MatrixGroup F)}
    (e : H ≃* PSL2MatrixGroup (GaloisField p m)) : IsCoatom H := by
  have hp' := hp.out
  have hpodd : Odd p := hp'.odd_of_ne_two hp2
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hf
    exact hf0 hf
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hp3 : 3 ≤ p := by have := hp'.two_le; rcases hpodd with ⟨k, hk⟩; omega
  have hs3 : 3 ≤ p ^ m := le_trans hp3 (Nat.le_self_pow hm0 p)
  have hsodd : Odd (p ^ m) := hpodd.pow
  have hq : p ^ f = (p ^ m) ^ r := by rw [hf, pow_mul]
  set s := p ^ m with hs
  have h2s : 2 ∣ s ^ 2 - 1 := by
    rw [hs, ← pow_mul]
    exact two_dvd_pow_sub_one hpodd _
  have hH : Nat.card H = s * ((s ^ 2 - 1) / 2) := by
    rw [Nat.card_congr e.toEquiv, card_psl2_galoisField hp2 hm0, show 2 * m = m * 2 by ring,
      pow_mul, ← hs, Nat.mul_div_assoc _ h2s]
  set A := (s ^ 2 - 1) / 2 with hA
  have hA2 : 2 * A = s ^ 2 - 1 := Nat.mul_div_cancel' h2s
  have hA4 : 4 ≤ A := by
    have : 9 ≤ s ^ 2 := by nlinarith
    omega
  have hcopA : Nat.Coprime p A := by
    have := coprime_pow_sub_one_half hpodd (k := 2 * m) (by omega)
    rwa [pow_mul', ← hs] at this
  have hpN : p ∣ Nat.card H := hH ▸ dvd_mul_of_dvd_left (dvd_pow_self p hm0) _
  have hsq : s < p ^ f := by
    rw [hq]
    calc s = s ^ 1 := (pow_one s).symm
      _ < s ^ r := Nat.pow_lt_pow_right (by omega) (by omega)
  apply coatom_of_forall
  · apply ne_top_of_card_lt
    rw [hH, card_psl2_odd hF hp2]
    apply lt_card_psl2_of
    have h1 : s ^ 2 - 1 < (p ^ f) ^ 2 - 1 := by
      have : s ^ 2 < (p ^ f) ^ 2 := Nat.pow_lt_pow_left hsq (by norm_num)
      have : 1 ≤ s ^ 2 := by nlinarith
      omega
    have h2 : 2 ∣ p ^ f * ((p ^ f) ^ 2 - 1) :=
      dvd_mul_of_dvd_right (by rw [← pow_mul]; exact two_dvd_pow_sub_one hpodd _) _
    have h3 : s * (2 * A) < p ^ f * ((p ^ f) ^ 2 - 1) := by
      rw [hA2]
      exact Nat.mul_lt_mul'' hsq h1
    obtain ⟨c, hc⟩ := h2
    have : 2 * (s * A) = s * (2 * A) := by ring
    omega
  intro K hHK hK
  have hHKc : Nat.card H < Nat.card K := Subgroup.card_lt_of_lt hHK
  have hHKd : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hHK.le
  have hAN : A ∣ Nat.card H := hH ▸ dvd_mul_left A s
  have hN12 : Nat.card H < 60 → s = 3 := by
    intro h
    rw [hH] at h
    by_contra hs3'
    have hs5 : 5 ≤ s := by rcases hsodd with ⟨k, hk⟩; omega
    have : 12 ≤ A := by
      have : 25 ≤ s ^ 2 := by nlinarith
      omega
    nlinarith
  have hp3' : s = 3 → p = 3 ∧ m = 1 := fun h => eq_three_of_pow_eq_three hp' (hs ▸ h)
  rcases overgroup_shapes hF hp2 K with
    ⟨⟨m', hm'⟩, -⟩ | ⟨⟨z, hzc, hz⟩, -⟩ | ⟨⟨z, hzc, hz⟩, -⟩ | ⟨h12, -⟩ | ⟨h16, h24, -⟩ |
      ⟨h5, h60, -⟩ | ⟨⟨m', t, hKc, ht⟩, -⟩ | ⟨m', hm'0, hm'f, hcard, -⟩ |
      ⟨m', hm'0, hm'f, hcard, -⟩
  · rw [hm'] at hHKd
    have h2 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right m' hcopA.symm)
      (dvd_trans hAN hHKd)
    omega
  · rw [hzc] at hHKd
    exact not_dvd_of_dvd_half hp2 hf0 hz (dvd_trans (dvd_trans hpN hHKd) (dvd_mul_left z 2))
  · rw [hzc] at hHKd
    exact not_dvd_of_dvd_half hp2 hf0 hz (dvd_trans hpN hHKd)
  · rw [hH, h12] at hHKc
    nlinarith
  · have hs' := hN12 (by omega)
    obtain ⟨rfl, rfl⟩ := hp3' hs'
    have h' : (3 ^ f) ^ 2 % 16 = 1 := h16
    rw [hf, one_mul, ← pow_mul, mul_comm, pow_mul] at h'
    norm_num at h'
    rw [(nine_pow_odd (hr.odd_of_ne_two hr2)).1] at h'
    norm_num at h'
  · have hs' := hN12 (by omega)
    obtain ⟨rfl, rfl⟩ := hp3' hs'
    rcases h5 with h5 | h5
    · norm_num at h5
    · have h' : (3 ^ f) ^ 2 % 5 = 1 := h5
      rw [hf, one_mul, ← pow_mul, mul_comm, pow_mul] at h'
      norm_num at h'
      rw [(nine_pow_odd (hr.odd_of_ne_two hr2)).2] at h'
      norm_num at h'
  · rw [hKc] at hHKd
    have h1 : A ∣ t := (Nat.Coprime.pow_right m' hcopA.symm).dvd_of_dvd_mul_left
      (dvd_trans hAN hHKd)
    have h2 : 2 * A ∣ p ^ f - 1 := by
      have := Nat.mul_dvd_mul_left 2 (dvd_trans h1 ht)
      rwa [Nat.mul_div_cancel' (two_dvd_pow_sub_one hpodd f)] at this
    rw [hA2, hs, ← pow_mul, hf] at h2
    have h3 := h826_exponent_dvd_of_pow_sub_one_dvd hp'.two_le h2
    have h4 : 2 ∣ r := (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hm0)).mp h3
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h4).symm
  · have h2m := two_mul_le_of_psl2_shape hF hp2 hK hm'f hcard
    have h2s' : 2 ∣ p ^ (2 * m') - 1 := two_dvd_pow_sub_one hpodd _
    rw [hcard, Nat.mul_div_assoc _ h2s'] at hHKd hHKc
    have hcopB : Nat.Coprime p ((p ^ (2 * m') - 1) / 2) := coprime_pow_sub_one_half hpodd (by omega)
    have hmm' : m ≤ m' := by
      have h1 : s ∣ p ^ m' * ((p ^ (2 * m') - 1) / 2) := dvd_trans
        (hH ▸ dvd_mul_right s A) hHKd
      have h2 : s ∣ p ^ m' := (Nat.Coprime.pow_left m hcopB).dvd_of_dvd_mul_right h1
      exact (Nat.pow_dvd_pow_iff_le_right hp'.one_lt).mp h2
    have hAB : A ∣ (p ^ (2 * m') - 1) / 2 :=
      (Nat.Coprime.pow_right m' hcopA.symm).dvd_of_dvd_mul_left (dvd_trans hAN hHKd)
    have h2AB : p ^ (2 * m) - 1 ∣ p ^ (2 * m') - 1 := by
      have := Nat.mul_dvd_mul_left 2 hAB
      rwa [hA2, Nat.mul_div_cancel' h2s', hs, ← pow_mul, mul_comm m 2] at this
    have h3 := h826_exponent_dvd_of_pow_sub_one_dvd hp'.two_le h2AB
    have hmd : m ∣ m' := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h3
    obtain ⟨j, rfl⟩ := hmd
    have hjr : j ∣ r := by
      rw [hf] at hm'f
      exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hm0)).mp hm'f
    rcases (Nat.dvd_prime hr).mp hjr with rfl | rfl
    · have heq : p ^ (m * 1) * ((p ^ (2 * (m * 1)) - 1) / 2) = Nat.card H := by
        rw [hH, mul_one, show 2 * m = m * 2 by ring, pow_mul, ← hs]
      omega
    · omega
  · have hAdvd : A ∣ p ^ (2 * m') - 1 :=
      (Nat.Coprime.pow_right m' hcopA.symm).dvd_of_dvd_mul_left (hcard ▸ dvd_trans hAN hHKd)
    have hmd : m ∣ m' := by
      apply dvd_of_half_dvd hpodd hm0 hm'0
      rwa [hA, hs, ← pow_mul, mul_comm m 2] at hAdvd
    obtain ⟨j, rfl⟩ := hmd
    have h2j : 2 * j ∣ r := by
      rw [hf, show 2 * (m * j) = m * (2 * j) by ring] at hm'f
      exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hm0)).mp hm'f
    have h4 : 2 ∣ r := dvd_trans (dvd_mul_right 2 j) h2j
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h4).symm

end CFSG.Glauberman.Dickson.MaxUp
