module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeSporGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HTD42Gen
public import Certificates.Certificate1322003
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis

open CFSG.Open CFSG.M23
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive (centGen_eq_top_of_equiv isElemAbelian_map
  card_map mem_normalizer_of_conj_mem conj_eq_of_mul_eq)
open CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree (coverGen SporadicCoverGen)


theorem centGen_eq_top_of_m24Facts {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : ¬ 3 ^ 4 ∣ Nat.card G)
    {x y z g11 g12 g13 t2 g21 g22 g23 w2 w4 : G}
    (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1)
    (hz : z ^ 3 = 1)
    (hz1 : z ≠ 1)
    (hxy : x * y = y * z * x)
    (hzx : z * x = x * z)
    (hzy : z * y = y * z)
    (e11z : g11 * z = z ^ 2 * x ^ 0 * g11)
    (e11t : g11 * x = z ^ 2 * x ^ 1 * g11)
    (e12z : g12 * z = z ^ 0 * x ^ 1 * g12)
    (e12t : g12 * x = z ^ 2 * x ^ 2 * g12)
    (c1 : g13 * x = x * g13)
    (hgen1 : Subgroup.closure ({g11, g12, g13} : Set G) = ⊤)
    (ht2 : t2 = x * y ^ 1)
    (e21z : g21 * z = z ^ 1 * t2 ^ 0 * g21)
    (e21t : g21 * t2 = z ^ 1 * t2 ^ 2 * g21)
    (e22z : g22 * z = z ^ 2 * t2 ^ 0 * g22)
    (e22t : g22 * t2 = z ^ 2 * t2 ^ 2 * g22)
    (c2 : g23 * t2 = t2 * g23)
    (hgen2 : Subgroup.closure ({g21, g22, g23} : Set G) = ⊤)
    (l2 : w2 * x = x ^ 0 * y ^ 1 * z ^ 0 * w2)
    (l2z : w2 * z = z ^ 1 * w2)
    (l4 : w4 * t2 = x ^ 2 * y ^ 1 * z ^ 1 * w4)
    (l4z : w4 * z = z ^ 2 * w4)
    (A : Subgroup G) (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 9) : centGen A = ⊤ := by
  have hnf1 : nf x y z ⟨1, 0, 0⟩ = x := by
    show x ^ 1 * y ^ 0 * z ^ 0 = _
    simp
  have hbase1 : centGen (Subgroup.closure ({z, nf x y z ⟨1, 0, 0⟩} : Set G)) = ⊤ := by
    rw [hnf1]
    have hzS : z ∈ Subgroup.closure ({z, x} : Set G) := Subgroup.subset_closure (by simp)
    have htS : x ∈ Subgroup.closure ({z, x} : Set G) :=
      Subgroup.subset_closure (by simp)
    have ht1 : x ≠ 1 := fun h => Heis.ne_one_of_ne_zero _ (by decide)
      (nfHom_injective hx hy hz hzx hzy hxy hz1
        (((nfHom_apply hx hy hz hzx hzy hxy _).trans hnf1).trans
          (h.trans (map_one _).symm)))
    refine centGen_eq_top_of_forall_mem hzS hz1 ?_ hgen1
    rintro g (rfl | rfl | rfl)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e11z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e11t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e12z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e12t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · exact Or.inr ⟨x, htS, ht1, c1⟩
  have hnf2 : nf x y z ⟨1, 1, 0⟩ = t2 := by
    rw [ht2]
    show x ^ 1 * y ^ 1 * z ^ 0 = _
    simp
  have hbase2 : centGen (Subgroup.closure ({z, nf x y z ⟨1, 1, 0⟩} : Set G)) = ⊤ := by
    rw [hnf2]
    have hzS : z ∈ Subgroup.closure ({z, t2} : Set G) := Subgroup.subset_closure (by simp)
    have htS : t2 ∈ Subgroup.closure ({z, t2} : Set G) :=
      Subgroup.subset_closure (by simp)
    have ht1 : t2 ≠ 1 := fun h => Heis.ne_one_of_ne_zero _ (by decide)
      (nfHom_injective hx hy hz hzx hzy hxy hz1
        (((nfHom_apply hx hy hz hzx hzy hxy _).trans hnf2).trans
          (h.trans (map_one _).symm)))
    refine centGen_eq_top_of_forall_mem hzS hz1 ?_ hgen2
    rintro g (rfl | rfl | rfl)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e21z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e21t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e22z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e22t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · exact Or.inr ⟨t2, htS, ht1, c2⟩
  refine centGen_eq_top_of_heis hx hy hz hzx hzy hxy hz1 hcard ?_ A hA hAc
  intro u hu
  have key : ∀ a b : ZMod 3, (a ≠ 0 ∨ b ≠ 0) →
      (1 * b = a * 0 ∨ 0 * b = a * 1 ∨ 1 * b = a * 1 ∨ 2 * b = a * 1) := by
    decide
  rcases key u.a u.b hu with h | h | h | h
  · exact ⟨⟨1, 0, 0⟩, 1, ⟨1, 0, 0⟩, by decide, hbase1, by simp, by decide, h,
      by simp⟩
  · refine ⟨⟨1, 0, 0⟩, w2, ⟨0, 1, 0⟩, by decide, hbase1, ?_, by decide, h, ?_⟩
    · rw [hnf1, conj_eq_of_mul_eq l2]
      rfl
    · rw [conj_eq_of_mul_eq l2z]
      exact pow_mem (Subgroup.mem_zpowers z) _
  · exact ⟨⟨1, 1, 0⟩, 1, ⟨1, 1, 0⟩, by decide, hbase2, by simp, by decide, h,
      by simp⟩
  · refine ⟨⟨1, 1, 0⟩, w4, ⟨2, 1, 1⟩, by decide, hbase2, ?_, by decide, h, ?_⟩
    · rw [hnf2, conj_eq_of_mul_eq l4]
      rfl
    · rw [conj_eq_of_mul_eq l4z]
      exact pow_mem (Subgroup.mem_zpowers z) _

section CoverGen

theorem mem_coverGen_of_mem {G : Type*} [Group G] {A : Subgroup G} {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {g : G} (hg : g = a ∨ (g * a = a * g ∧ Nat.Coprime (orderOf g) 3)) :
    g ∈ coverGen A := by
  refine (le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 le_rfl)) :
    Subgroup.closure ({a} ∪ {x | x * a = a * x ∧ Nat.Coprime (orderOf x) 3}) ≤ coverGen A) ?_
  apply Subgroup.subset_closure
  rcases hg with rfl | h
  · exact Or.inl rfl
  · exact Or.inr h

theorem map_coverGen_le {K K' : Type*} [Group K] [Group K'] (φ : K ≃* K') (A : Subgroup K) :
    (coverGen A).map φ.toMonoidHom ≤ coverGen (A.map φ.toMonoidHom) := by
  rw [coverGen, Subgroup.map_iSup]
  refine iSup_le fun a => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun ha => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun ha1 => ?_
  have hwa : φ.toMonoidHom a ∈ A.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ ha
  have hwa1 : φ.toMonoidHom a ≠ 1 := by simpa using ha1
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  refine mem_coverGen_of_mem hwa hwa1 ?_
  rcases hg with hg | ⟨hga, hgo⟩
  · left
    rw [Set.mem_singleton_iff.mp hg]
  · right
    refine ⟨?_, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hga]
    · simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] using hgo

theorem coverGen_eq_top_of_map {K K' : Type*} [Group K] [Group K'] {A : Subgroup K}
    (φ : K ≃* K') (h : coverGen A = ⊤) : coverGen (A.map φ.toMonoidHom) = ⊤ := by
  refine top_le_iff.mp (le_trans ?_ (map_coverGen_le φ A))
  rw [h, Subgroup.map_top_of_surjective _ φ.surjective]

theorem coverGen_eq_top_of_equiv {K K' : Type*} [Group K] [Group K'] {A : Subgroup K}
    (φ : K ≃* K') (h : coverGen (A.map φ.toMonoidHom) = ⊤) : coverGen A = ⊤ := by
  have h2 := coverGen_eq_top_of_map φ.symm h
  have hA : (A.map φ.toMonoidHom).map φ.symm.toMonoidHom = A := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A
    ext a
    simp
  rwa [hA] at h2

theorem coverGen_eq_top_of_m22Facts {G : Type*} [Group G] [Finite G]
    (hcard : ¬ 3 ^ 3 ∣ Nat.card G) {u v c1 c2 c3 : G}
    (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (huv : u * v = v * u)
    (hv1 : v ≠ 1) (hvu1 : v ≠ u) (hvu2 : v ≠ u ^ 2)
    (hc1 : c1 * u = u * c1) (hc1o : c1 ^ 2 = 1)
    (hc2 : c2 * v = v * c2) (hc2o : c2 ^ 2 = 1)
    (hc3 : c3 * (u * v) = (u * v) * c3) (hc3o : c3 ^ 2 = 1)
    (hgen : Subgroup.closure ({u, v, c1, c2, c3} : Set G) = ⊤)
    (A : Subgroup G) (hAc : Nat.card A = 9) : coverGen A = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hvz : v ∉ Subgroup.zpowers u := by
    intro hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
    have h3 : u ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hu3
    have hm : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have hl : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    have e : u ^ (k % 3).toNat = v := by
      rw [← hk, zpow_eq_zpow_emod k h3, ← zpow_natCast, Int.toNat_of_nonneg hm]
    have hcases : (k % 3).toNat = 0 ∨ (k % 3).toNat = 1 ∨ (k % 3).toNat = 2 := by omega
    rcases hcases with h | h | h <;> rw [h] at e
    · exact hv1 (by rw [← e, pow_zero])
    · exact hvu1 (by rw [← e, pow_one])
    · exact hvu2 e.symm
  obtain ⟨hA₀c, -⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.HTD42.sup_zpowers_card_nine hu3 hu1 hv3 huv hvz
  set A₀ := Subgroup.zpowers u ⊔ Subgroup.zpowers v
  have huA : u ∈ A₀ := Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
  have hvA : v ∈ A₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  have huv1 : u * v ≠ 1 := by
    intro h
    apply hvu2
    have hv' : v = u⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hv', inv_eq_iff_mul_eq_one, ← pow_succ', hu3]
  have hcop : ∀ g : G, g ^ 2 = 1 → Nat.Coprime (orderOf g) 3 := fun g hg =>
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hg) (by norm_num)
  have htop : coverGen A₀ = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl | rfl | rfl)
    · exact mem_coverGen_of_mem huA hu1 (Or.inl rfl)
    · exact mem_coverGen_of_mem hvA hv1 (Or.inl rfl)
    · exact mem_coverGen_of_mem huA hu1 (Or.inr ⟨hc1, hcop _ hc1o⟩)
    · exact mem_coverGen_of_mem hvA hv1 (Or.inr ⟨hc2, hcop _ hc2o⟩)
    · exact mem_coverGen_of_mem (mul_mem huA hvA) huv1 (Or.inr ⟨hc3, hcop _ hc3o⟩)
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h2 : 3 ^ 2 ∣ Nat.card G := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hA₀c]; exact Subgroup.card_subgroup_dvd_card A₀
  have hfac : (Nat.card G).factorization 3 = 2 := by
    have hle : 2 ≤ (Nat.card G).factorization 3 :=
      ((Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hG0).mp h2)
    have hlt : ¬ 3 ≤ (Nat.card G).factorization 3 := fun h3 =>
      hcard ((Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hG0).mpr h3)
    omega
  let PS : Sylow 3 G := Sylow.ofCard A₀ (by rw [hA₀c, hfac]; norm_num)
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 2) (by rw [hAc]; norm_num)
  obtain ⟨T, hAT⟩ := hAp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PS T
  set A' := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hA'P : A' ≤ A₀ := by
    rintro _ ⟨a, ha, rfl⟩
    have haT : a ∈ ((g • PS : Sylow 3 G) : Subgroup G) := hg ▸ hAT ha
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at haT
    have hPS : ((PS : Sylow 3 G) : Subgroup G) = A₀ := Sylow.coe_ofCard _ _
    rw [hPS] at haT
    simpa [MulAut.smul_def, MulAut.conj_apply] using haT
  have hA'eq : A' = A₀ := Subgroup.eq_of_le_of_card_ge hA'P (by
    rw [hA₀c, show A' = A.map (MulAut.conj g⁻¹).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hAc])
  have hAA : A₀.map (MulAut.conj g).toMonoidHom = A := by
    rw [← hA'eq, Subgroup.map_map]
    convert Subgroup.map_id A
    ext a
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  rw [← hAA]
  exact coverGen_eq_top_of_map (MulAut.conj g) htop

end CoverGen

section Perm

theorem range_pair {α : Type*} (a b : α) : Set.range ![a, b] = {a, b} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩]

theorem closure_eq_top_of_seedWords {n k : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    {a b : Equiv.Perm (Fin n)} (hH : H = Subgroup.closure {a, b}) (GS : Fin k → Equiv.Perm (Fin n))
    (s : Set H) (hs : ∀ i, ∃ h ∈ s, (h : Equiv.Perm (Fin n)) = GS i)
    {wA wB : List (Fin k × Bool)} (hA : evalGroupWord GS wA = a⁻¹)
    (hB : evalGroupWord GS wB = b⁻¹) : Subgroup.closure s = ⊤ := by
  set S := Subgroup.closure (((↑) : H → Equiv.Perm (Fin n)) '' s)
  have hGS : Subgroup.closure (Set.range GS) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨h, hh, hhi⟩ := hs i
    exact Subgroup.subset_closure ⟨h, hh, hhi⟩
  have hle : H ≤ S := by
    rw [hH, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · have h := evalGroupWord_mem_closure GS wA
      rw [hA] at h
      simpa using hGS (inv_mem h)
    · have h := evalGroupWord_mem_closure GS wB
      rw [hB] at h
      simpa using hGS (inv_mem h)
  have hmap : (Subgroup.closure s).map H.subtype = S := by
    rw [MonoidHom.map_closure]
    rfl
  rw [eq_top_iff]
  rintro x -
  have hx : (x : Equiv.Perm (Fin n)) ∈ S := hle x.2
  rw [← hmap] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := Subtype.ext hyx
  rwa [← this]

theorem mem_of_word {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {a b : Equiv.Perm (Fin n)}
    (hH : H = Subgroup.closure {a, b}) (w : List (Fin 2 × Bool)) :
    evalGroupWord ![a, b] w ∈ H := by
  rw [hH, ← range_pair]
  exact evalGroupWord_mem_closure _ w

end Perm

section Concrete

open CFSG.Blueprint Mathieu

theorem m24_eq_closure : NativeSporadic.M24 = Subgroup.closure {m24A, m24B} := rfl

theorem m22_eq_closure : NativeSporadic.M22 = Subgroup.closure {m22A, m22B} := rfl



theorem centGen_M24_three_of_cert [IsSimpleGroup ↥NativeSporadic.M24]
    (hcard : ¬ 3 ^ 4 ∣ Nat.card ↥NativeSporadic.M24) (A : Subgroup ↥NativeSporadic.M24)
    (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 9) : centGen A = ⊤ := by
  obtain ⟨hwx, hwy, hwz, hwg11, hwg12, hwg13, hwg21, hwg22, hwg23, hww2, hww4, f_hx, f_hy, f_hz,
    f_hz1, f_hxy, f_hzx, f_hzy, f_e11z, f_e11t, f_e12z, f_e12t, f_c1, f_e21z, f_e21t, f_e22z,
    f_e22t, f_c2, f_l2, f_l2z, f_l4, f_l4z, hsA1, hsB1, hsA2, hsB2⟩ :=
    (Certificates.certificate1322003).1
  let x : ↥NativeSporadic.M24 := ⟨m24X, hwx ▸ mem_of_word m24_eq_closure _⟩
  let y : ↥NativeSporadic.M24 := ⟨m24Y, hwy ▸ mem_of_word m24_eq_closure _⟩
  let z : ↥NativeSporadic.M24 := ⟨m24Z, hwz ▸ mem_of_word m24_eq_closure _⟩
  let g11 : ↥NativeSporadic.M24 := ⟨m24G11, hwg11 ▸ mem_of_word m24_eq_closure _⟩
  let g12 : ↥NativeSporadic.M24 := ⟨m24G12, hwg12 ▸ mem_of_word m24_eq_closure _⟩
  let g13 : ↥NativeSporadic.M24 := ⟨m24G13, hwg13 ▸ mem_of_word m24_eq_closure _⟩
  let g21 : ↥NativeSporadic.M24 := ⟨m24G21, hwg21 ▸ mem_of_word m24_eq_closure _⟩
  let g22 : ↥NativeSporadic.M24 := ⟨m24G22, hwg22 ▸ mem_of_word m24_eq_closure _⟩
  let g23 : ↥NativeSporadic.M24 := ⟨m24G23, hwg23 ▸ mem_of_word m24_eq_closure _⟩
  let w2 : ↥NativeSporadic.M24 := ⟨m24W2, hww2 ▸ mem_of_word m24_eq_closure _⟩
  let w4 : ↥NativeSporadic.M24 := ⟨m24W4, hww4 ▸ mem_of_word m24_eq_closure _⟩
  let t2 : ↥NativeSporadic.M24 := x * y ^ 1
  have hgen1 : Subgroup.closure ({g11, g12, g13} : Set ↥NativeSporadic.M24) =
      ⊤ := by
    refine closure_eq_top_of_seedWords m24_eq_closure m24GS1 _ ?_ hsA1 hsB1
    intro i
    fin_cases i
    · exact ⟨g11, by simp, rfl⟩
    · exact ⟨g12, by simp, rfl⟩
    · exact ⟨g13, by simp, rfl⟩
  have hgen2 : Subgroup.closure ({g21, g22, g23} : Set ↥NativeSporadic.M24) =
      ⊤ := by
    refine closure_eq_top_of_seedWords m24_eq_closure m24GS2 _ ?_ hsA2 hsB2
    intro i
    fin_cases i
    · exact ⟨g21, by simp, rfl⟩
    · exact ⟨g22, by simp, rfl⟩
    · exact ⟨g23, by simp, rfl⟩
  have hx : x ^ 3 = 1 := Subtype.ext f_hx
  have hy : y ^ 3 = 1 := Subtype.ext f_hy
  have hz : z ^ 3 = 1 := Subtype.ext f_hz
  have hz1 : z ≠ 1 := fun h => f_hz1 (congrArg Subtype.val h :)
  have hxy : x * y = y * z * x := Subtype.ext f_hxy
  have hzx : z * x = x * z := Subtype.ext f_hzx
  have hzy : z * y = y * z := Subtype.ext f_hzy
  have e11z : g11 * z = z ^ 2 * x ^ 0 * g11 := Subtype.ext f_e11z
  have e11t : g11 * x = z ^ 2 * x ^ 1 * g11 := Subtype.ext f_e11t
  have e12z : g12 * z = z ^ 0 * x ^ 1 * g12 := Subtype.ext f_e12z
  have e12t : g12 * x = z ^ 2 * x ^ 2 * g12 := Subtype.ext f_e12t
  have c1 : g13 * x = x * g13 := Subtype.ext f_c1
  have e21z : g21 * z = z ^ 1 * t2 ^ 0 * g21 := Subtype.ext f_e21z
  have e21t : g21 * t2 = z ^ 1 * t2 ^ 2 * g21 := Subtype.ext f_e21t
  have e22z : g22 * z = z ^ 2 * t2 ^ 0 * g22 := Subtype.ext f_e22z
  have e22t : g22 * t2 = z ^ 2 * t2 ^ 2 * g22 := Subtype.ext f_e22t
  have c2 : g23 * t2 = t2 * g23 := Subtype.ext f_c2
  have l2 : w2 * x = x ^ 0 * y ^ 1 * z ^ 0 * w2 := Subtype.ext f_l2
  have l2z : w2 * z = z ^ 1 * w2 := Subtype.ext f_l2z
  have l4 : w4 * t2 = x ^ 2 * y ^ 1 * z ^ 1 * w4 := Subtype.ext f_l4
  have l4z : w4 * z = z ^ 2 * w4 := Subtype.ext f_l4z
  exact centGen_eq_top_of_m24Facts (x := x) (y := y) (z := z) (g11 := g11) (g12 := g12) (g13 :=
    g13) (g21 := g21) (g22 := g22) (g23 := g23) (t2 := t2) (w2 := w2) (w4 := w4) hcard hx hy hz hz1
    hxy hzx hzy e11z e11t e12z e12t c1 hgen1 rfl e21z e21t e22z e22t c2 hgen2 l2 l2z l4 l4z A hA hAc

theorem coverGen_M22_of_cert (hcard : ¬ 3 ^ 3 ∣ Nat.card ↥NativeSporadic.M22)
    (A : Subgroup ↥NativeSporadic.M22) (hAc : Nat.card A = 9) : coverGen A = ⊤ := by
  obtain ⟨hwu, hwv, hwc1, hwc2, hwc3, hU1, hU3, hV3, hUV, hV1, hVU1, hVU2, hC1, hC1o, hC2, hC2o,
    hC3, hC3o, hsA, hsB⟩ := (Certificates.certificate1322003).2
  let u : ↥NativeSporadic.M22 := ⟨m22U, hwu ▸ mem_of_word m22_eq_closure _⟩
  let v : ↥NativeSporadic.M22 := ⟨m22V, hwv ▸ mem_of_word m22_eq_closure _⟩
  let c1 : ↥NativeSporadic.M22 := ⟨m22C1, hwc1 ▸ mem_of_word m22_eq_closure _⟩
  let c2 : ↥NativeSporadic.M22 := ⟨m22C2, hwc2 ▸ mem_of_word m22_eq_closure _⟩
  let c3 : ↥NativeSporadic.M22 := ⟨m22C3, hwc3 ▸ mem_of_word m22_eq_closure _⟩
  have hgen : Subgroup.closure ({u, v, c1, c2, c3} : Set ↥NativeSporadic.M22) = ⊤ := by
    refine closure_eq_top_of_seedWords m22_eq_closure m22GS _ ?_ hsA hsB
    intro i
    fin_cases i
    · exact ⟨u, by simp, rfl⟩
    · exact ⟨v, by simp, rfl⟩
    · exact ⟨c1, by simp, rfl⟩
    · exact ⟨c2, by simp, rfl⟩
    · exact ⟨c3, by simp, rfl⟩
  exact coverGen_eq_top_of_m22Facts hcard (u := u) (v := v) (c1 := c1) (c2 := c2) (c3 := c3)
    (fun h => hU1 (congrArg Subtype.val h :)) (Subtype.ext hU3) (Subtype.ext hV3)
    (Subtype.ext hUV) (fun h => hV1 (congrArg Subtype.val h :))
    (fun h => hVU1 (congrArg Subtype.val h :)) (fun h => hVU2 (congrArg Subtype.val h :))
    (Subtype.ext hC1) (Subtype.ext hC1o)
    (Subtype.ext hC2) (Subtype.ext hC2o) (Subtype.ext hC3) (Subtype.ext hC3o) hgen A hAc

end Concrete

section Wrapper

open CFSG.Blueprint TauCeti

set_option linter.unusedSectionVars false


theorem sporadicCentGen_M24_three : SporadicCentGen 3 .M24 := by
  intro L _ _ ⟨e⟩ A hA hAc
  have hf := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.carrierFacts_of_ne_M .M24
    (by decide)
  have : Finite (NativeSporadic.Carrier .M24) := hf.1
  have : IsSimpleGroup (NativeSporadic.Carrier .M24) := hf.2.1
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M24
  let ψ₁ : NativeSporadic.Carrier .M24 ≃* ↥NativeSporadic.M24 := MulEquiv.refl _
  have : IsSimpleGroup ↥NativeSporadic.M24 := ψ₁.symm.isSimpleGroup
  let ψ : L ≃* ↥NativeSporadic.M24 := (e.trans f.symm).trans ψ₁
  have hcard : ¬ 3 ^ 4 ∣ Nat.card ↥NativeSporadic.M24 := by
    rw [show Nat.card ↥NativeSporadic.M24 = Nat.card (NativeSporadic.Carrier .M24) from rfl,
      CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder .M24 (by decide)]
    norm_num [CFSG.AGLEmbeddingD2.d2SporadicOrder]
  refine centGen_eq_top_of_equiv ψ ?_
  exact centGen_M24_three_of_cert hcard _ (isElemAbelian_map hA ψ)
    (by rw [card_map, hAc]; norm_num)

theorem sporadicCoverGen_M22 : SporadicCoverGen .M22 := by
  intro L _ _ ⟨e⟩ A _ hAc
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M22
  let ψ₁ : NativeSporadic.Carrier .M22 ≃* ↥NativeSporadic.M22 := MulEquiv.refl _
  let ψ : L ≃* ↥NativeSporadic.M22 := (e.trans f.symm).trans ψ₁
  have hcard : ¬ 3 ^ 3 ∣ Nat.card ↥NativeSporadic.M22 := by
    rw [show Nat.card ↥NativeSporadic.M22 = Nat.card (NativeSporadic.Carrier .M22) from rfl,
      CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder .M22 (by decide)]
    norm_num [CFSG.AGLEmbeddingD2.d2SporadicOrder]
  refine coverGen_eq_top_of_equiv ψ ?_
  exact coverGen_M22_of_cert hcard _ (by rw [card_map, hAc]; norm_num)

end Wrapper

end CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis
