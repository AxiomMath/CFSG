module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeLocalQDBasic
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction

public section

namespace CFSG.Wreathed.OriginalAllPrime.LocalQD

open CFSG.Semidihedral.ProjectiveSL2Cover CFSG.GorensteinWalter

theorem torus_two_mul_dvd {n X : ℕ} (hn : n ≠ 0) (h1 : n ∣ X)
    (h2 : 2 * 2 ^ padicValNat 2 n ∣ X) : 2 * n ∣ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨o, ho⟩ := (pow_padicValNat_dvd : 2 ^ padicValNat 2 n ∣ n)
  have hodd : ¬ 2 ∣ o := by
    rintro ⟨c, hc⟩
    apply pow_succ_padicValNat_not_dvd (p := 2) hn
    refine ⟨c, ?_⟩
    calc n = 2 ^ padicValNat 2 n * o := ho
      _ = 2 ^ (padicValNat 2 n + 1) * c := by rw [hc, pow_succ]; ring
  have hcop : Nat.Coprime (2 * 2 ^ padicValNat 2 n) o := by
    rw [← pow_succ']
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have h3 : o ∣ X := (Dvd.intro_left _ ho.symm).trans h1
  calc 2 * n = 2 * 2 ^ padicValNat 2 n * o := by rw [mul_assoc, ← ho]
    _ ∣ X := hcop.mul_dvd_of_dvd_of_dvd h2 h3

theorem torus_alternatingGroup_four_cases :
    ∀ g : alternatingGroup (Fin 4), g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  decide +kernel

theorem torus_alternatingGroup_five_cases :
    ∀ g : alternatingGroup (Fin 5), g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  decide +kernel

theorem torus_commutator_index_eq {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (commutator G).index = (commutator H).index := by
  have hmap : (commutator G).map e.toMonoidHom = commutator H := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  rw [← hmap, Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]

theorem torus_commutator_index_pgl2 (K : Type*) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    (commutator (Matrix.ProjGenLinGroup (Fin 2) K)).index = 2 := by
  have h3 : 3 ≤ Nat.card K := by
    obtain ⟨p, n, hp, hpodd, hn, hcard⟩ := hK
    rw [hcard]
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      obtain ⟨k, hk⟩ := hpodd
      omega
    exact hp3.trans (Nat.le_self_pow (by omega) p)
  rcases h3.eq_or_lt with h3 | h3
  · rcases CFSG.BenderSuzuki.External.huppert_blackburn_XI_example_1_3_a K with
      ⟨-, _, _, -, -, -, -, -, -, -, -, -, hsmall⟩
    obtain ⟨⟨e⟩, -⟩ := hsmall h3.symm
    rw [torus_commutator_index_eq e, commutator_perm_fin_four_eq_alternatingGroup,
      alternatingGroup.index_eq_two]
  · rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK h3]
    exact pgl2_psl2Range_index_eq_two K hK

theorem torus_dihedral_r_mem_zpowers {z : ℕ} (hz : z ≠ 0) {i : ZMod z}
    (hi : orderOf (DihedralGroup.r i) = z) (j : ZMod z) :
    DihedralGroup.r j ∈ Subgroup.zpowers (DihedralGroup.r i) := by
  have : NeZero z := ⟨hz⟩
  have hmem : ∀ k : ZMod z,
      DihedralGroup.r k ∈ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z) := by
    intro k
    refine Subgroup.mem_zpowers_iff.mpr ⟨(k.val : ℤ), ?_⟩
    rw [DihedralGroup.r_one_zpow]
    simp
  have heq : Subgroup.zpowers (DihedralGroup.r i) =
      Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z) := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (hmem i))
    rw [Nat.card_zpowers, Nat.card_zpowers, hi, DihedralGroup.orderOf_r_one]
  rw [heq]
  exact hmem j

theorem torus_zpowers_subgroupOf_characteristic {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (hgA : g ∈ A) (h4 : ∀ a ∈ A, a ∈ Subgroup.zpowers g ∨ a ^ 4 = 1)
    (hg4 : ¬ orderOf g ∣ 4) : ((Subgroup.zpowers g).subgroupOf A).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  rintro σ _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hy' : y = (⟨g, hgA⟩ : A) ^ k := Subtype.ext (by simp [hk])
  rw [Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, hy', map_zpow, Subgroup.coe_zpow]
  apply zpow_mem
  rcases h4 _ (σ ⟨g, hgA⟩).2 with h | h
  · exact h
  · exfalso
    apply hg4
    have h' : σ ((⟨g, hgA⟩ : A) ^ 4) = σ 1 := by
      rw [map_pow, map_one]
      exact Subtype.ext (by simpa using h)
    have h'' := congrArg Subtype.val (σ.injective h')
    exact orderOf_dvd_of_pow_eq_one (by simpa using h'')

section SL2

variable {F : Type} [Field F]

theorem torus_nativeQuotient_eq_one_iff (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    nativeQuotient F g = 1 ↔ g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [← MonoidHom.mem_ker, nativeQuotient_ker, center_eq_zpowers_minusIdentity]

theorem torus_mem_ker_subgroupMap_iff (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (a : A) : a ∈ ((nativeQuotient F).subgroupMap A).ker ↔
      (a : Matrix.SpecialLinearGroup (Fin 2) F) ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [MonoidHom.mem_ker, ← torus_nativeQuotient_eq_one_iff, Subtype.ext_iff,
    MonoidHom.subgroupMap_apply_coe, OneMemClass.coe_one]

theorem torus_ker_subgroupMap_characteristic (hF : ringChar F ≠ 2)
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
    ((nativeQuotient F).subgroupMap A).ker.Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  rintro σ _ ⟨a, ha, rfl⟩
  rw [SetLike.mem_coe, torus_mem_ker_subgroupMap_iff] at ha
  rw [MulEquiv.coe_toMonoidHom, torus_mem_ker_subgroupMap_iff]
  have ha2 : a ^ 2 = 1 := Subtype.ext (by simpa using (sq_eq_one_iff_mem_center hF _).mpr ha)
  have hσ : σ a ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
  exact (sq_eq_one_iff_mem_center hF _).mp (by simpa using congrArg Subtype.val hσ)

theorem torus_exists_characteristic_index_two (hF : ringChar F ≠ 2)
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (h : (commutator (A.map (nativeQuotient F))).index = 2) :
    ∃ C : Subgroup A, C.Characteristic ∧ C.index = 2 := by
  set φ := (nativeQuotient F).subgroupMap A
  have hφ : Function.Surjective φ := (nativeQuotient F).subgroupMap_surjective A
  have hK : φ.ker.Characteristic := torus_ker_subgroupMap_characteristic hF A
  refine ⟨commutator A ⊔ φ.ker, ?_, ?_⟩
  · rw [Subgroup.characteristic_iff_map_le]
    intro σ
    rw [Subgroup.map_sup]
    exact sup_le_sup (Subgroup.characteristic_iff_map_le.mp inferInstance σ)
      (Subgroup.characteristic_iff_map_le.mp hK σ)
  · have hmap : (commutator A).map φ = commutator (A.map (nativeQuotient F)) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hφ]
      rfl
    rw [← Subgroup.comap_map_eq, hmap, Subgroup.index_comap_of_surjective _ hφ, h]

theorem torus_mem_zpowers_or_pow_four_eq_one (hF : ringChar F ≠ 2)
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (hgA : g ∈ A)
    (hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ≤ Subgroup.zpowers g) {z : ℕ}
    (hz : 3 ≤ z) (e : A.map (nativeQuotient F) ≃* DihedralGroup z)
    (hgz : orderOf (nativeQuotient F g) = z) {a : Matrix.SpecialLinearGroup (Fin 2) F}
    (ha : a ∈ A) : a ∈ Subgroup.zpowers g ∨ a ^ 4 = 1 := by
  set κ := nativeQuotient F
  set g' : A.map κ := ⟨κ g, Subgroup.mem_map_of_mem κ hgA⟩ with hg'
  set a' : A.map κ := ⟨κ a, Subgroup.mem_map_of_mem κ ha⟩
  have hg'ord : orderOf (e g') = z := by rw [MulEquiv.orderOf_eq, hg', Subgroup.orderOf_mk, hgz]
  obtain ⟨i, hi⟩ : ∃ i, e g' = DihedralGroup.r i := by
    rcases h : e g' with i | i
    · exact ⟨i, rfl⟩
    · rw [h, DihedralGroup.orderOf_sr] at hg'ord
      omega
  rcases h : e a' with j | j
  · left
    have hrot := torus_dihedral_r_mem_zpowers (by omega) (hi ▸ hg'ord) j
    rw [← hi] at hrot
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hrot
    have hk' : g' ^ k = a' := e.injective (by rw [map_zpow, hk, h])
    have hκk : κ (g ^ k) = κ a := by
      rw [map_zpow]
      simpa [g', a'] using congrArg Subtype.val hk'
    have hker : (g ^ k)⁻¹ * a ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [← torus_nativeQuotient_eq_one_iff, map_mul, map_inv, hκk, inv_mul_cancel]
    have hdecomp : a = g ^ k * ((g ^ k)⁻¹ * a) := by group
    rw [hdecomp]
    exact mul_mem (zpow_mem (Subgroup.mem_zpowers g) k) (hZ hker)
  · right
    have h2 : a' ^ 2 = 1 :=
      e.injective (by rw [map_pow, h, map_one, sq, DihedralGroup.sr_mul_self])
    have hκ2 : κ (a ^ 2) = 1 := by
      rw [map_pow]
      simpa [a'] using congrArg Subtype.val h2
    rw [show 4 = 2 * 2 from rfl, pow_mul]
    exact (sq_eq_one_iff_mem_center hF _).mpr ((torus_nativeQuotient_eq_one_iff _).mp hκ2)

end SL2

theorem eq_top_of_torus_le
    {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) (hq : 5 < p ^ f)
    (ε : ℤ) (hε : ε = if p ^ f % 4 = 1 then 1 else -1)
    (m : ℕ) (hm : m = 2 ^ padicValInt 2 ((p ^ f : ℕ) - ε))
    {A T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hTA : T ≤ A) (hT : IsCyclic T)
    (hTcard : (Nat.card T : ℤ) = (p ^ f : ℕ) - ε)
    (h2 : 2 * m ∣ Nat.card A)
    (hchar : ∀ C : Subgroup A, C.Characteristic → C.index ≠ 2) :
    A = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hF : ringChar F ≠ 2 := ringChar_ne_two_of_card hpodd hcard
  rw [← hTcard, padicValInt.of_nat] at hm
  obtain ⟨g, rfl⟩ : ∃ g, Subgroup.zpowers g = T :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top T).mp hT
  have hgA : g ∈ A := hTA (Subgroup.mem_zpowers g)
  have hTeq : Nat.card (Subgroup.zpowers g) = orderOf g := Nat.card_zpowers g
  rw [hTeq] at hm hTcard
  obtain ⟨n, hn⟩ : ∃ n, orderOf g = n := ⟨_, rfl⟩
  rw [hn] at hm hTcard hTeq
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hnq : (n + 1 = p ^ f ∧ p ^ f % 4 = 1) ∨ (n = p ^ f + 1 ∧ p ^ f % 4 = 3) := by
    obtain ⟨k, hk⟩ := hqodd
    split_ifs at hε with h4
    · subst hε
      left
      omega
    · subst hε
      right
      omega
  have h4n : 4 ∣ n := by omega
  have hn8 : 8 ≤ n := by omega
  have hcop : Nat.Coprime n p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hpn
    have hpq : p ∣ p ^ f := dvd_pow_self p (by omega)
    rcases hnq with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [← h1] at hpq
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpn).mp hpq))
    · rw [h1] at hpn
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpq).mp hpn))
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    apply Nat.gcd_eq_right
    rw [hcard]
    obtain ⟨k, hk⟩ := hqodd
    exact ⟨k, by omega⟩
  have hnA : n ∣ Nat.card A := hTeq ▸ Subgroup.card_dvd_of_le hTA
  have h2nA : 2 * n ∣ Nat.card A := torus_two_mul_dvd (by omega) hnA (hm ▸ h2)
  have hTeven : Even (Nat.card (Subgroup.zpowers g)) := by
    rw [hTeq]
    exact even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4n)
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ≤ Subgroup.zpowers g :=
    center_le_of_even_card hF hTeven
  have hAcard : Nat.card A = 2 * Nat.card (A.map (nativeQuotient F)) :=
    card_eq_two_mul_card_map hF (even_iff_two_dvd.mpr (dvd_trans (dvd_mul_right 2 n) h2nA))
  obtain ⟨t, ht⟩ : ∃ t, orderOf (nativeQuotient F g) = t := ⟨_, rfl⟩
  have hnt : n = 2 * t := by
    have h := card_eq_two_mul_card_map hF hTeven
    rwa [hTeq, MonoidHom.map_zpowers, Nat.card_zpowers, ht] at h
  have hnÂ : n ∣ Nat.card (A.map (nativeQuotient F)) := by
    rw [hAcard] at h2nA
    exact Nat.dvd_of_mul_dvd_mul_left two_pos h2nA
  have hÂpos : 0 < Nat.card (A.map (nativeQuotient F)) := Nat.card_pos
  have hgÂ : nativeQuotient F g ∈ A.map (nativeQuotient F) := Subgroup.mem_map_of_mem _ hgA
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hcard
      (A.map (nativeQuotient F)) with
    hEl | ⟨z, hz, hHz, -⟩ | ⟨z, hz, hHz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨k, s, -, hs, N, D, hN, -, hNcard, -, hDcard, hdisj, hsup⟩ | ⟨k, hk, hkf, ⟨e⟩⟩ |
      ⟨k, hk, -, ⟨e⟩⟩
  ·
    exfalso
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p (A.map (nativeQuotient F))).exists_card_eq
    rw [hk] at hnÂ
    have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (dvd_trans (by omega) hnÂ)
    exact (Nat.not_even_iff_odd.mpr hpodd) (even_iff_two_dvd.mpr h2p)
  ·
    exfalso
    rw [hgcd, hcard] at hz
    rw [hHz] at hnÂ hÂpos
    have hnz := Nat.le_of_dvd hÂpos hnÂ
    have hzle : z ≤ (p ^ f + 1) / 2 := by
      rcases hz with hz | hz
      · exact (Nat.le_of_dvd (by omega) hz).trans (by omega)
      · exact Nat.le_of_dvd (by omega) hz
    omega
  ·
    exfalso
    rw [hgcd, hcard] at hz
    have hzle : z ≤ (p ^ f + 1) / 2 := by
      rcases hz with hz | hz
      · exact (Nat.le_of_dvd (by omega) hz).trans (by omega)
      · exact Nat.le_of_dvd (by omega) hz
    rw [hHz] at hnÂ hÂpos hAcard
    have h2z : 2 * z = n := Nat.eq_of_dvd_of_lt_two_mul (by omega) hnÂ (by omega)
    have h4 : ∀ a ∈ A, a ∈ Subgroup.zpowers g ∨ a ^ 4 = 1 := fun a ha =>
      torus_mem_zpowers_or_pow_four_eq_one hF hgA hZ (by omega) e (by rw [ht]; omega) ha
    apply hchar _ (torus_zpowers_subgroupOf_characteristic hgA h4 (by
      rw [hn]
      intro hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega))
    have hi := Subgroup.card_mul_index ((Subgroup.zpowers g).subgroupOf A)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv, hTeq, hAcard, h2z] at hi
    exact Nat.eq_of_mul_eq_mul_left (by omega) (hi.trans (mul_comm 2 n))
  ·
    exfalso
    have hx : orderOf (e ⟨_, hgÂ⟩) = t := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ht]
    rcases torus_alternatingGroup_four_cases (e ⟨_, hgÂ⟩) with h | h <;>
    · have := Nat.le_of_dvd (by norm_num) (hx ▸ orderOf_dvd_of_pow_eq_one h)
      omega
  ·
    exfalso
    obtain ⟨C, hC, hCi⟩ := torus_exists_characteristic_index_two hF A (by
      rw [torus_commutator_index_eq e, commutator_perm_fin_four_eq_alternatingGroup,
        alternatingGroup.index_eq_two])
    exact hchar C hC hCi
  ·
    exfalso
    have hx : orderOf (e ⟨_, hgÂ⟩) = t := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ht]
    rcases torus_alternatingGroup_five_cases (e ⟨_, hgÂ⟩) with h | h | h
    · have := Nat.le_of_dvd (by norm_num) (hx ▸ orderOf_dvd_of_pow_eq_one h)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hx ▸ orderOf_dvd_of_pow_eq_one h)
      omega
    · rcases (Nat.dvd_prime Nat.prime_five).mp (hx ▸ orderOf_dvd_of_pow_eq_one h) with h5 | h5 <;>
        omega
  ·
    exfalso
    have : N.Normal := hN
    have hcompl : N.IsComplement' D := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
    have hHcard : Nat.card (A.map (nativeQuotient F)) = p ^ k * s := by
      rw [← hcompl.card_mul_card, hNcard, hDcard]
    rw [hHcard] at hnÂ
    have hns : n ∣ s := (Nat.Coprime.pow_right k hcop).dvd_of_dvd_mul_left hnÂ
    have hgcd' : Nat.gcd (p ^ f - 1) 2 = 2 := by rw [← hcard, hgcd]
    rw [hgcd'] at hs
    have hspos : 0 < s := hDcard ▸ Nat.card_pos
    have h1 := Nat.le_of_dvd hspos hns
    have h2 := Nat.le_of_dvd (by omega) hs
    omega
  ·
    have hK : IsOddPrimePower (Nat.card (GaloisField p k)) :=
      ⟨p, k, hp, hpodd, Nat.pos_of_ne_zero hk, GaloisField.card p k hk⟩
    have hcardH : Nat.card (A.map (nativeQuotient F)) = p ^ k * (p ^ k * p ^ k - 1) / 2 := by
      rw [Nat.card_congr e.toEquiv, psl2_card_formula _ hK, GaloisField.card p k hk, pow_two]
    by_cases hkf' : k = f
    · subst hkf'
      have htop : A.map (nativeQuotient F) = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [hcardH, psl2_card_formula F (isOddPrimePower_card hp hpodd hf hcard), hcard, pow_two]
      have hker : (nativeQuotient F).ker ≤ A := by
        rw [nativeQuotient_ker, ← center_eq_zpowers_minusIdentity]
        exact hZ.trans hTA
      rw [← Subgroup.comap_map_eq_self hker, htop, Subgroup.comap_top]
    · exfalso
      obtain ⟨c, hc⟩ := hkf
      have hc2 : 2 ≤ c := by
        rcases c with _ | _ | c
        · omega
        · exfalso
          apply hkf'
          omega
        · omega
      have hq0odd : Odd (p ^ k) := hpodd.pow
      have hq0sq : p ^ k * p ^ k ≤ p ^ f := by
        rw [← pow_add, hc]
        exact Nat.pow_le_pow_right hp.pos (by nlinarith)
      have h2 : 2 ∣ p ^ k * p ^ k - 1 := by
        obtain ⟨a, ha⟩ := hq0odd
        exact ⟨2 * a * a + 2 * a, by rw [ha]; ring_nf; omega⟩
      rw [hcardH, Nat.mul_div_assoc _ h2] at hnÂ
      have hcop0 : Nat.Coprime n (p ^ k) := Nat.Coprime.pow_right k hcop
      have hq03 : 3 ≤ p ^ k := by
        have : 1 < p ^ k := Nat.one_lt_pow hk hp.one_lt
        obtain ⟨a, ha⟩ := hq0odd
        omega
      have hq09 : 9 ≤ p ^ k * p ^ k := Nat.mul_le_mul hq03 hq03
      have := Nat.le_of_dvd (by omega) (hcop0.dvd_of_dvd_mul_left hnÂ)
      omega
  ·
    exfalso
    have hK : IsOddPrimePower (Nat.card (GaloisField p k)) :=
      ⟨p, k, hp, hpodd, Nat.pos_of_ne_zero hk, GaloisField.card p k hk⟩
    obtain ⟨C, hC, hCi⟩ := torus_exists_characteristic_index_two hF A (by
      rw [torus_commutator_index_eq e]
      exact torus_commutator_index_pgl2 _ hK)
    exact hchar C hC hCi

end CFSG.Wreathed.OriginalAllPrime.LocalQD
