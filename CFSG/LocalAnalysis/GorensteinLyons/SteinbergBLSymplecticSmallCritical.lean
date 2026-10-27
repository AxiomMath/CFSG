module

public import CFSG.RankThree.GroupTheory.SteinbergBYSymplecticCritical
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSmallKernelFiltrations

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

namespace SymplecticSmallCritical

open Subgroup
open scoped commutatorElement

variable {P : Type*} [Group P]

@[expose] def IsCriticalCentralProduct (D : Subgroup P) (z : P) (w : ℕ) : Prop :=
  D = ⊤ ∧ (center D).map D.subtype = center P ∧ Nat.card (center P) = 4 ∧ 1 ≤ w ∧
    ∃ E : Subgroup P, IsExtraspecialPGroup 2 E ∧ Nat.card E = 2 ^ (1 + 2 * w) ∧
      E ⊔ (center D).map D.subtype = ⊤ ∧ ⁅E, (center D).map D.subtype⁆ = ⊥ ∧
      E ⊓ (center D).map D.subtype = zpowers z ∧ (center E).map E.subtype = zpowers z

theorem sq_eq_one_of_mem_zpowers {z x : P} (hz : orderOf z = 2) (hx : x ∈ zpowers z) :
    x ^ 2 = 1 := by
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz hx with rfl | rfl
  · exact one_pow 2
  · rw [← hz]
    exact pow_orderOf_eq_one _

theorem commutator_mem_of_sq_mem {N : Subgroup P} (hN : N ≤ center P)
    (hsq : ∀ x : P, x ^ 2 ∈ N) (x y : P) : ⁅x, y⁆ ∈ N := by
  have hcy : y * (x ^ 2)⁻¹ = (x ^ 2)⁻¹ * y := mem_center_iff.mp (hN (inv_mem (hsq x))) y
  have key : ⁅x, y⁆ = (x * y) ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ := by
    calc ⁅x, y⁆ = x * y * x * ((x ^ 2)⁻¹ * y) * (y ^ 2)⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = x * y * x * (y * (x ^ 2)⁻¹) * (y ^ 2)⁻¹ := by rw [hcy]
      _ = (x * y) ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ := by
          rw [pow_two (x * y)]
          group
  rw [key]
  exact mul_mem (mul_mem (hsq _) (inv_mem (hsq x))) (inv_mem (hsq y))

theorem isExtraspecialPGroup_of_sq_mem [Finite P] (hP : IsPGroup 2 P) {z : P}
    (hz : orderOf z = 2) (hzc : z ∈ center P) (hsq : ∀ x : P, x ^ 2 ∈ zpowers z)
    (hcen : ∀ x ∈ center P, x ∈ zpowers z) (hnab : ∃ x y : P, x * y ≠ y * x) :
    IsExtraspecialPGroup 2 P := by
  have hzp : zpowers z ≤ center P := zpowers_le.mpr hzc
  obtain ⟨x, y, hxy⟩ := hnab
  have h := (isExtraspecialPGroup_two_of_forall (E := ⊤) (hP.to_subgroup ⊤) (mem_top z) hz
    (fun x _ => ⟨fun hx => hcen x (mem_center_iff.mpr fun g => (hx g (mem_top g)).symm),
      fun hx g _ => (mem_center_iff.mp (hzp hx) g).symm⟩)
    (fun x _ y _ => commutator_mem_of_sq_mem hzp hsq x y) (fun x _ => hsq x)
    ⟨x, mem_top x, y, mem_top y, hxy⟩).1
  exact isExtraspecialPGroup_congr_mulEquiv topEquiv h

theorem criticalCentralProduct_consequences [Finite P] (hP : IsPGroup 2 P) {D : Subgroup P}
    {z : P} (hz : orderOf z = 2)
    (huniq : ∀ x ∈ (center D).map D.subtype, orderOf x = 2 → x = z) {w : ℕ}
    (h : IsCriticalCentralProduct D z w) :
    commutator P = zpowers z ∧ frattini P = zpowers z ∧
      CFSG.IsElementaryAbelian 2 (P ⧸ center P) ∧ Nat.card (P ⧸ center P) = 2 ^ (2 * w) ∧
      Nat.card P = 2 ^ (2 * w + 2) ∧ ∀ g : P, g ^ 4 = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 P) := ⟨hP⟩
  obtain ⟨-, hZP, hZ4, -, E, hEx, hEcard, hEZ, -, hEZi, hEcen⟩ := h
  rw [hZP] at huniq hEZ hEZi
  have hzEZ : z ∈ E ⊓ center P := by
    rw [hEZi]
    exact mem_zpowers z
  have hzp : zpowers z ≤ center P := zpowers_le.mpr hzEZ.2
  have hZsq : ∀ s ∈ center P, s ^ 2 ∈ zpowers z := by
    intro s hs
    have h4 : (s ^ 2) ^ 2 = 1 := by
      have h1 := pow_card_eq_one' (G := center P) (x := ⟨s, hs⟩)
      rw [hZ4] at h1
      rw [← pow_mul]
      exact congrArg Subtype.val h1
    by_cases h1 : s ^ 2 = 1
    · rw [h1]
      exact one_mem _
    · rw [huniq _ (pow_mem hs 2) (orderOf_eq_prime h4 h1)]
      exact mem_zpowers z
  have hEsq : ∀ e ∈ E, e ^ 2 ∈ zpowers z := by
    intro e he
    rw [← hEcen]
    exact ⟨⟨e, he⟩ ^ 2, extraspecial_two_sq_mem_center hEx _, rfl⟩
  have hsq : ∀ x : P, x ^ 2 ∈ zpowers z := by
    intro x
    obtain ⟨e, he, s, hs, rfl⟩ := mem_sup_of_normal_right.mp
      (show x ∈ E ⊔ center P by rw [hEZ]; exact mem_top x)
    rw [(show Commute e s from mem_center_iff.mp hs e).mul_pow]
    exact mul_mem (hEsq e he) (hZsq s hs)
  have hcomm : ∀ x y : P, ⁅x, y⁆ ∈ zpowers z := commutator_mem_of_sq_mem hzp hsq
  have h4 : ∀ g : P, g ^ 4 = 1 := fun g => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    exact sq_eq_one_of_mem_zpowers hz (hsq g)
  have hcom : commutator P = zpowers z := by
    apply le_antisymm
    · rw [_root_.commutator_def, commutator_le]
      exact fun x _ y _ => hcomm x y
    · rw [zpowers_le]
      have h1 : (commutator E).map E.subtype ≤ commutator P := by
        rw [_root_.commutator_def, _root_.commutator_def, map_commutator]
        exact commutator_mono le_top le_top
      apply h1
      rw [hEx.2.1, hEcen]
      exact mem_zpowers z
  have hfr : frattini P = zpowers z := by
    apply le_antisymm
    · rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), closure_le]
      rintro _ (hx | ⟨y, rfl⟩)
      · rw [SetLike.mem_coe, hcom] at hx
        exact hx
      · exact hsq y
    · rw [← hcom]
      exact CFSG.commutator_le_frattini_of_isPGroup (p := 2)
  have hcommQ : ∀ a b : P ⧸ center P, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [h1]
    exact hzp (hcomm _ _)
  have hpowQ : ∀ a : P ⧸ center P, a ^ 2 = 1 := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hzp (hsq x)
  let f : E →* P ⧸ center P := (QuotientGroup.mk' (center P)).comp E.subtype
  have hfsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he, s, hs, rfl⟩ := mem_sup_of_normal_right.mp
      (show x ∈ E ⊔ center P by rw [hEZ]; exact mem_top x)
    refine ⟨⟨e, he⟩, ?_⟩
    change (QuotientGroup.mk e : P ⧸ center P) = QuotientGroup.mk (e * s)
    rw [QuotientGroup.eq, inv_mul_cancel_left]
    exact hs
  have hker : Nat.card f.ker = 2 := by
    have h1 : f.ker = (center P).subgroupOf E := by
      ext e
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      exact QuotientGroup.eq_one_iff (e : P)
    rw [h1, ← card_map_of_injective E.subtype_injective, subgroupOf_map_subtype, inf_comm, hEZi,
      Nat.card_zpowers, hz]
  have hrange : Nat.card f.range = Nat.card (P ⧸ center P) := by
    rw [MonoidHom.range_eq_top.mpr hfsurj, card_top]
  have hcardE := card_mul_index f.ker
  rw [index_ker, hrange, hker, hEcard] at hcardE
  have hQcard : Nat.card (P ⧸ center P) = 2 ^ (2 * w) := by
    have h1 : 2 ^ (1 + 2 * w) = 2 * 2 ^ (2 * w) := by rw [pow_add, pow_one]
    omega
  have hPcard : Nat.card P = 2 ^ (2 * w + 2) := by
    rw [card_eq_card_quotient_mul_card_subgroup (center P), hQcard, hZ4, pow_add]
    norm_num
  have hel : CFSG.IsElementaryAbelian 2 (P ⧸ center P) :=
    { toIsMulCommutative := ⟨⟨hcommQ⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpowQ }
  exact ⟨hcom, hfr, hel, hQcard, hPcard, h4⟩

end SymplecticSmallCritical

open SymplecticSmallCritical Subgroup CFSG.SectionRank.Ccomm CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement

variable {P : Type*} [Group P]

theorem symplectic_small_critical_center_structure [Finite P] [Nontrivial P]
    (hP : IsPGroup 2 P)
    (hsymp : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A)
    {D : Subgroup P} (hD : ThompsonCritical D) :
    (Nat.card ((center D).map D.subtype) ≤ 4 →
      ∃ z ∈ (center D).map D.subtype, orderOf z = 2 ∧
        (∀ x ∈ (center D).map D.subtype, orderOf x = 2 → x = z) ∧
        ((IsCyclic P ∧ (Nat.card P = 2 ∨ Nat.card P = 4)) ∨ IsExtraspecialPGroup 2 P ∨
          ∃ w, IsCriticalCentralProduct D z w) ∧
        ¬ ((IsCyclic P ∧ (Nat.card P = 2 ∨ Nat.card P = 4)) ∧ IsExtraspecialPGroup 2 P) ∧
        ¬ ((IsCyclic P ∧ (Nat.card P = 2 ∨ Nat.card P = 4)) ∧
          ∃ w, IsCriticalCentralProduct D z w) ∧
        ¬ (IsExtraspecialPGroup 2 P ∧ ∃ w, IsCriticalCentralProduct D z w) ∧
        (∀ w, IsCriticalCentralProduct D z w →
          commutator P = zpowers z ∧ frattini P = zpowers z ∧
            CFSG.IsElementaryAbelian 2 (P ⧸ center P) ∧
            Nat.card (P ⧸ center P) = 2 ^ (2 * w) ∧ Nat.card P = 2 ^ (2 * w + 2) ∧
            ∀ g : P, g ^ 4 = 1) ∧
        ∀ g : P, g ^ 4 = 1) ∧
    ((∃ g : P, 8 ≤ orderOf g) ↔ 8 ≤ Nat.card ((center D).map D.subtype)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hcp⟩ := symplectic_critical_subgroup_central_product hP hsymp
  obtain ⟨hZ0, hcyc, hZchar, z, hzZ, hz, huniq, hzc, -, -, E, R, hEZ, -, hER, hERc, hRZ, -,
    hRn, hcases, -, -⟩ := hcp D hD
  set Z := (center D).map D.subtype with hZdef
  have hZn : Z.Normal := normal_of_characteristic Z
  have hzp : zpowers z ≤ center P := zpowers_le.mpr hzc
  have hcD : centralizer (D : Set P) = Z := centralizer_eq_of_thompsonCritical hD
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hP.to_subgroup Z)
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero, Subgroup.card_eq_one] at hk
      exact absurd hk hZ0
    · exact h
  have hsmall : Nat.card Z ≤ 4 →
      ∃ z ∈ Z, orderOf z = 2 ∧ (∀ x ∈ Z, orderOf x = 2 → x = z) ∧
        ((IsCyclic P ∧ (Nat.card P = 2 ∨ Nat.card P = 4)) ∨ IsExtraspecialPGroup 2 P ∨
          ∃ w, IsCriticalCentralProduct D z w) ∧
        ¬ ((IsCyclic P ∧ (Nat.card P = 2 ∨ Nat.card P = 4)) ∧ IsExtraspecialPGroup 2 P) ∧
        ¬ ((IsCyclic P ∧ (Nat.card P = 2 ∨ Nat.card P = 4)) ∧
          ∃ w, IsCriticalCentralProduct D z w) ∧
        ¬ (IsExtraspecialPGroup 2 P ∧ ∃ w, IsCriticalCentralProduct D z w) ∧
        (∀ w, IsCriticalCentralProduct D z w →
          commutator P = zpowers z ∧ frattini P = zpowers z ∧
            CFSG.IsElementaryAbelian 2 (P ⧸ center P) ∧
            Nat.card (P ⧸ center P) = 2 ^ (2 * w) ∧ Nat.card P = 2 ^ (2 * w + 2) ∧
            ∀ g : P, g ^ 4 = 1) ∧
        ∀ g : P, g ^ 4 = 1 := by
    intro h4
    have hk2 : k ≤ 2 := by
      by_contra h
      push Not at h
      have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      rw [← hk] at h8
      norm_num at h8
      omega
    have hZ4 : ∀ x ∈ Z, (x ^ 2) ^ 2 = 1 := by
      intro x hx
      have h1 := pow_card_eq_one' (G := Z) (x := ⟨x, hx⟩)
      obtain ⟨c, hc⟩ : Nat.card Z ∣ 2 * 2 := by
        rw [hk]
        exact (pow_dvd_pow 2 hk2).trans (by norm_num)
      have h2 : (⟨x, hx⟩ : Z) ^ (2 * 2) = 1 := by rw [hc, pow_mul, h1, one_pow]
      rw [← pow_mul]
      exact congrArg Subtype.val h2
    have hinv : ∀ x ∈ Z, x ^ 2 = 1 → x ∈ zpowers z := by
      intro x hx hx2
      by_cases h1 : x = 1
      · rw [h1]
        exact one_mem _
      · rw [huniq x hx (orderOf_eq_prime hx2 h1)]
        exact mem_zpowers z
    have hZsq : ∀ x ∈ Z, x ^ 2 ∈ zpowers z := fun x hx => hinv _ (pow_mem hx 2) (hZ4 x hx)
    have hact : ∀ g : P, g ∈ centralizer (Z : Set P) ∨ ∀ x ∈ Z, g * x * g⁻¹ = x⁻¹ := by
      intro g
      rcases (show k = 1 ∨ k = 2 by omega) with hk' | hk'
      ·
        left
        rw [mem_centralizer_iff]
        intro x hx
        have hx2 : x ^ 2 = 1 := by
          have h1 := pow_card_eq_one' (G := Z) (x := ⟨x, hx⟩)
          rw [hk, hk', pow_one] at h1
          exact congrArg Subtype.val h1
        exact (mem_center_iff.mp (hzp (hinv x hx hx2)) g).symm
      ·
        obtain ⟨⟨a, haZ⟩, ha⟩ := @IsCyclic.exists_generator _ _ hcyc
        have hoa : orderOf a = 4 := (by
          rw [← Subgroup.orderOf_mk a haZ, orderOf_eq_card_of_forall_mem_zpowers ha, hk, hk'] :
            orderOf a = 2 ^ 2).trans (by norm_num)
        have hZa : ∀ x ∈ Z, ∃ n : ℤ, a ^ n = x := by
          intro x hx
          obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (ha ⟨x, hx⟩)
          exact ⟨n, by simpa using congrArg Subtype.val hn⟩
        have hZab : ∀ x ∈ Z, ∀ y ∈ Z, Commute x y := by
          intro x hx y hy
          obtain ⟨m, rfl⟩ := hZa x hx
          obtain ⟨n, rfl⟩ := hZa y hy
          exact (Commute.refl a).zpow_zpow m n
        have ha2 : a ^ 2 = z := by
          apply huniq _ (pow_mem haZ 2)
          rw [orderOf_pow' a (by norm_num), hoa]
          norm_num
        have hy : g * a * g⁻¹ ∈ Z := hZn.conj_mem a haZ g
        have hy2 : (g * a * g⁻¹) ^ 2 = z := by
          rw [conj_pow, ha2, mem_center_iff.mp hzc g, mul_inv_cancel_right]
        have hsq1 : (g * a * g⁻¹ * a⁻¹) ^ 2 = 1 := by
          rw [((hZab _ hy _ haZ).inv_right).mul_pow, hy2, inv_pow, ha2, mul_inv_cancel]
        rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz
          (hinv _ (mul_mem hy (inv_mem haZ)) hsq1) with h1 | h1
        · left
          have hga : g * a * g⁻¹ = a := mul_inv_eq_one.mp h1
          have hc : a * g = g * a := by
            calc a * g = g * a * g⁻¹ * g := by rw [hga]
              _ = g * a := by group
          rw [mem_centralizer_iff]
          intro x hx
          obtain ⟨n, rfl⟩ := hZa x hx
          exact (Commute.zpow_left hc n).eq
        · right
          have h3 : g * a * g⁻¹ = a ^ 2 * a := by rw [ha2, ← h1, inv_mul_cancel_right]
          have h4' : a ^ 2 * a * a = 1 := by
            calc a ^ 2 * a * a = a ^ 4 := by group
              _ = 1 := by rw [← hoa, pow_orderOf_eq_one]
          have hga : g * a * g⁻¹ = a⁻¹ := by
            rw [h3]
            exact eq_inv_of_mul_eq_one_left h4'
          intro x hx
          obtain ⟨n, rfl⟩ := hZa x hx
          rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hga, inv_zpow]
    have hRsq : ∀ r ∈ R, r ^ 2 ∈ zpowers z := by
      intro r hr
      rcases hact r with hrc | hrinv
      · exact hZsq r (hRZ ▸ mem_inf.mpr ⟨hr, hrc⟩)
      · have hr2c : r ^ 2 ∈ centralizer (Z : Set P) := by
          rw [mem_centralizer_iff]
          intro x hx
          have h1 := hrinv x hx
          have h2 := hrinv x⁻¹ (inv_mem hx)
          rw [inv_inv] at h2
          calc x * r ^ 2 = r * x⁻¹ * r⁻¹ * r ^ 2 := by rw [h2]
            _ = r * (r * x * r⁻¹) * r := by rw [h1]; group
            _ = r ^ 2 * x := by rw [pow_two]; group
        have hr2Z : r ^ 2 ∈ Z := hRZ ▸ mem_inf.mpr ⟨pow_mem hr 2, hr2c⟩
        apply hinv _ hr2Z
        have h1 := hrinv _ hr2Z
        have h2 : r * r ^ 2 * r⁻¹ = r ^ 2 := by group
        rw [h2] at h1
        rw [pow_two]
        exact mul_eq_one_iff_eq_inv.mpr h1
    have hEsq : ∀ e ∈ E, e ^ 2 ∈ zpowers z := by
      intro e he
      rcases hcases with ⟨-, hE0, -⟩ | ⟨_, -, -, -, -, hEx, -, -, -, -, hEcen, -⟩
      · rw [hE0, mem_bot] at he
        rw [he, one_pow]
        exact one_mem _
      · rw [← hEcen]
        exact ⟨⟨e, he⟩ ^ 2, extraspecial_two_sq_mem_center hEx _, rfl⟩
    have hERcomm : ∀ e ∈ E, ∀ r ∈ R, e * r = r * e := fun _ he r hr =>
      ((mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hERc he)) r hr).symm
    have hsq : ∀ x : P, x ^ 2 ∈ zpowers z := by
      intro x
      have := hRn
      obtain ⟨e, he, r, hr, rfl⟩ := mem_sup_of_normal_right.mp
        (show x ∈ E ⊔ R by rw [hER]; exact mem_top x)
      rw [(show Commute e r from hERcomm e he r hr).mul_pow]
      exact mul_mem (hEsq e he) (hRsq r hr)
    have h4P : ∀ g : P, g ^ 4 = 1 := fun g => by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
      exact sq_eq_one_of_mem_zpowers hz (hsq g)
    have htri : (IsCyclic P ∧ (Nat.card P = 2 ∨ Nat.card P = 4)) ∨ IsExtraspecialPGroup 2 P ∨
        ∃ w, IsCriticalCentralProduct D z w := by
      by_cases hRC : R ≤ centralizer (Z : Set P)
      ·
        have hRZ' : R = Z := by rw [← hRZ, inf_eq_left.mpr hRC]
        have hDtop : D = ⊤ := by rw [← hEZ, ← hRZ', hER]
        have hcenP : center P = Z := by rw [← hcD, hDtop, coe_top, centralizer_univ]
        rcases hcases with ⟨-, -, hRtop⟩ | ⟨w, hw, -, -, -, hEx, hEcard, -, -, hEZi, hEcen, -⟩
        ·
          left
          have hZtop : Z = ⊤ := hRZ'.symm.trans hRtop
          have hPZ : Nat.card P = Nat.card Z := by rw [hZtop, card_top]
          refine ⟨isCyclic_of_surjective (hH := hcyc) Z.subtype fun x =>
            ⟨⟨x, hZtop ▸ mem_top x⟩, rfl⟩, ?_⟩
          rw [hPZ, hk]
          rcases (show k = 1 ∨ k = 2 by omega) with hk' | hk'
          · left
            rw [hk', pow_one]
          · right
            rw [hk']
            norm_num
        · rcases (show k = 1 ∨ k = 2 by omega) with hk' | hk'
          ·
            right
            left
            have hZz : Z = zpowers z := by
              symm
              apply eq_of_le_of_card_ge (zpowers_le.mpr hzZ)
              exact (by rw [hk, hk', pow_one, Nat.card_zpowers, hz] :
                Nat.card Z = Nat.card (zpowers z)).le
            have hZE : Z ≤ E := by
              rw [hZz, ← hEZi]
              exact inf_le_left
            have hEtop : E = ⊤ := by rw [← hER, hRZ', sup_eq_left.mpr hZE]
            exact isExtraspecialPGroup_congr_mulEquiv
              ((MulEquiv.subgroupCongr hEtop).trans topEquiv) hEx
          ·
            right
            right
            refine ⟨w, hDtop, hcenP.symm, ?_, hw, E, hEx, hEcard, hEZ.trans hDtop, ?_, hEZi,
              hEcen⟩
            · rw [hcenP, hk, hk']
              norm_num
            · exact eq_bot_iff.mpr ((commutator_mono le_rfl hRZ'.ge).trans hERc.le)
      ·
        right
        left
        obtain ⟨r, -, hrc⟩ := IsConcreteLE.not_le_iff_exists.mp hRC
        have hrinv : ∀ x ∈ Z, r * x * r⁻¹ = x⁻¹ := (hact r).resolve_left hrc
        apply isExtraspecialPGroup_of_sq_mem hP hz hzc hsq
        · intro x hx
          have hxZ : x ∈ Z := by
            rw [← hcD, mem_centralizer_iff]
            exact fun y _ => mem_center_iff.mp hx y
          apply hinv x hxZ
          have h1 := hrinv x hxZ
          rw [mem_center_iff.mp hx r, mul_inv_cancel_right] at h1
          rw [pow_two]
          exact mul_eq_one_iff_eq_inv.mpr h1
        · rw [mem_centralizer_iff] at hrc
          push Not at hrc
          obtain ⟨x, -, hxr⟩ := hrc
          exact ⟨x, r, hxr⟩
    have hex12 : ¬ ((IsCyclic P ∧ (Nat.card P = 2 ∨ Nat.card P = 4)) ∧
        IsExtraspecialPGroup 2 P) := by
      rintro ⟨⟨hPc, -⟩, hPx⟩
      have hbot : commutator P = ⊥ := by
        rw [_root_.commutator_def, eq_bot_iff, commutator_le]
        intro a _ b _
        rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact (@IsCyclic.isMulCommutative P _ hPc).is_comm.comm a b
      have h1 := hPx.2.2.2
      rw [← hPx.2.1, hbot, card_bot] at h1
      exact absurd h1 (by norm_num)
    have hex13 : ¬ ((IsCyclic P ∧ (Nat.card P = 2 ∨ Nat.card P = 4)) ∧
        ∃ w, IsCriticalCentralProduct D z w) := by
      rintro ⟨⟨-, hP24⟩, w, -, -, -, hw, E', -, hE'card, -⟩
      have h1 : Nat.card E' ≤ Nat.card P := card_le_card_group E'
      rw [hE'card] at h1
      have h2 : 8 ≤ 2 ^ (1 + 2 * w) :=
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (1 + 2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rcases hP24 with h | h <;> rw [h] at h1 <;> omega
    have hex23 : ¬ (IsExtraspecialPGroup 2 P ∧ ∃ w, IsCriticalCentralProduct D z w) := by
      rintro ⟨hPx, _, -, -, h4c, -⟩
      rw [hPx.2.2.2] at h4c
      exact absurd h4c (by norm_num)
    exact ⟨z, hzZ, hz, huniq, htri, hex12, hex13, hex23,
      fun w hw => criticalCentralProduct_consequences hP hz huniq hw, h4P⟩
  refine ⟨hsmall, ?_, ?_⟩
  · rintro ⟨g, hg⟩
    by_contra hlt
    push Not at hlt
    have hk2 : k ≤ 2 := by
      by_contra h
      push Not at h
      have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      rw [← hk] at h8
      norm_num at h8
      omega
    have h4 : Nat.card Z ≤ 4 := by
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 4 := by norm_num
    obtain ⟨-, -, -, -, -, -, -, -, -, h4P⟩ := hsmall h4
    have := orderOf_le_of_pow_eq_one (by norm_num) (h4P g)
    omega
  · intro h8
    obtain ⟨⟨a, haZ⟩, ha⟩ := @IsCyclic.exists_generator _ _ hcyc
    refine ⟨a, ?_⟩
    rw [← Subgroup.orderOf_mk a haZ, orderOf_eq_card_of_forall_mem_zpowers ha]
    exact h8

end CFSG.LocalAnalysis.GorensteinLyons
