module

public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

namespace OddNormalCore

theorem oddCore_eq_pPrimeCore_two (F : Type*) [Group F] :
    CFSG.oddCore F = CFSG.pPrimeCore 2 F := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem odd_card_oddCore (F : Type*) [Group F] [Finite F] : Odd (Nat.card (CFSG.oddCore F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCore_eq_pPrimeCore_two]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem oddCore_characteristic (F : Type*) [Group F] : (CFSG.oddCore F).Characteristic := by
  rw [oddCore_eq_pPrimeCore_two]
  infer_instance

variable {F : Type*} [Group F]

theorem commute_of_four_group_centralizers [Finite F] {X : Subgroup F} (hX : Odd (Nat.card X))
    {a b : F} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hne : a ≠ b) (haX : a ∈ normalizer (X : Set F))
    (hbX : b ∈ normalizer (X : Set F)) {z : F}
    (hza : ∀ x ∈ X, x * a = a * x → z * x = x * z)
    (hzb : ∀ x ∈ X, x * b = b * x → z * x = x * z)
    (hzab : ∀ x ∈ X, x * (a * b) = a * b * x → z * x = x * z) :
    ∀ x ∈ X, z * x = x * z := by
  have hba : b * a = a * b := hab.symm
  have ha' : ∀ x, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have hb' : ∀ x, b * (b * x) = x := fun x => by rw [← mul_assoc, hb, one_mul]
  have hba' : ∀ x, b * (a * x) = a * (b * x) := fun x => by rw [← mul_assoc, hba, mul_assoc]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  let Q : Subgroup F :=
    { carrier := {1, a, b, a * b}
      mul_mem' := by
        rintro x y hx hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
          simp [mul_assoc, ha, hb, hba, ha', hba']
      one_mem' := by simp
      inv_mem' := by
        rintro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> simp [mul_inv_rev, hainv, hbinv, hba] }
  have hmemQ : ∀ {x : F}, x ∈ Q ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := fun {x} => by
    change x ∈ ({1, a, b, a * b} : Set F) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hQ : CFSG.Open.IsElemAbelian 2 Q := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · rcases hmemQ.mp x.2 with h | h | h | h <;> rcases hmemQ.mp y.2 with h' | h' | h' | h' <;>
        simp [h, h', mul_assoc, ha, hb, hba, ha', hba']
    · rcases hmemQ.mp hx with rfl | rfl | rfl | rfl <;>
        simp [pow_two, mul_assoc, ha, hb, hba']
  have hab1 : a * b ≠ 1 := fun h => hne (by rw [eq_inv_of_mul_eq_one_left h, hbinv])
  have haab : a ≠ a * b := fun h => hb1 (by
    calc b = a * (a * b) := (ha' b).symm
      _ = a * a := by rw [← h]
      _ = 1 := ha)
  have hbab : b ≠ a * b := fun h => ha1 (by
    calc a = a * b * b := by rw [mul_assoc, hb, mul_one]
      _ = b * b := by rw [← h]
      _ = 1 := hb)
  have hcard : 2 ^ (1 + 1) ≤ Nat.card Q := by
    have h : Nat.card Q = Set.ncard ({1, a, b, a * b} : Set F) := Nat.card_coe_set_eq _
    have h1 : (1 : F) ∉ ({a, b, a * b} : Set F) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
    have h2 : a ∉ ({b, a * b} : Set F) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, haab⟩
    have h3 : b ∉ ({a * b} : Set F) := by
      simp only [Set.mem_singleton_iff]
      exact hbab
    rw [h, Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
    norm_num
  have hQN : Q ≤ normalizer (X : Set F) := by
    intro x hx
    rcases hmemQ.mp hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact haX
    · exact hbX
    · exact mul_mem haX hbX
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two Q X hQ hcard hQN (Nat.coprime_two_left.mpr hX)
  have hle : (⨆ S ∈ CFSG.Open.signalizerFunctorEk 2 1 Q, X ⊓ centralizer (S : Set F)) ≤
      centralizer {z} := by
    refine iSup₂_le fun S hS => ?_
    obtain ⟨hSQ, hScard⟩ := hS
    have : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by rw [hScard]; norm_num)
    obtain ⟨⟨s, hsS⟩, hs1⟩ := exists_ne (1 : S)
    have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
    intro y hy
    obtain ⟨hyX, hyC⟩ := mem_inf.mp hy
    have hsy : s * y = y * s := mem_centralizer_iff.mp hyC s hsS
    rw [mem_centralizer_singleton_iff]
    rcases hmemQ.mp (hSQ hsS) with h | h | h | h
    · exact absurd h hs1'
    · rw [h] at hsy
      exact (hza y hyX hsy.symm).symm
    · rw [h] at hsy
      exact (hzb y hyX hsy.symm).symm
    · rw [h] at hsy
      exact (hzab y hyX hsy.symm).symm
  intro x hx
  rw [← hgen] at hx
  exact (mem_centralizer_singleton_iff.mp (hle hx)).symm

end OddNormalCore

open OddNormalCore in
theorem elementary_involution_commutator_centralizes_odd_normal_core {F : Type*} [Group F]
    [Finite F] {a : F} (ha : orderOf a = 2) {J : Subgroup F} [IsSimpleGroup J]
    (hJnab : ∃ x y : J, x * y ≠ y * x) (hJa : J ≤ centralizer {a})
    (hJn : (J.subgroupOf (centralizer {a})).Normal) {U : Subgroup F} [IsElementaryAbelian 2 U]
    (haU : a ∈ normalizer (U : Set F))
    (hB : closure {x | ∃ u ∈ U, x = u⁻¹ * (a⁻¹ * u * a)} ≠ ⊥)
    (hBJ : closure {x | ∃ u ∈ U, x = u⁻¹ * (a⁻¹ * u * a)} ≤ J)
    {L : Subgroup F} (hL : L = normalClosure (J : Set F)) :
    Group.IsPerfect L ∧
      (∀ A : Subgroup F, A.Normal → Odd (Nat.card A) → ⁅A, L⁆ = ⊥) ∧
      (centralizer (L.map (QuotientGroup.mk' (CFSG.oddCore F)) : Set (F ⧸ CFSG.oddCore F)) = ⊥ →
        centralizer (L : Set F) = CFSG.oddCore F ∧
          (center L).map L.subtype = (CFSG.oddCore L).map L.subtype ∧
          (CFSG.oddCore L).map L.subtype = L ⊓ CFSG.oddCore F ∧
          ∃ e : L ⧸ center L ≃* L.map (QuotientGroup.mk' (CFSG.oddCore F)),
            ∀ x : L, (e (QuotientGroup.mk x) : F ⧸ CFSG.oddCore F) =
              QuotientGroup.mk' (CFSG.oddCore F) x) := by
  classical
  set B := closure {x | ∃ u ∈ U, x = u⁻¹ * (a⁻¹ * u * a)} with hBdef
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    exact absurd ha (by norm_num)
  have hUcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : U) ⟨v, hv⟩)
  have hUsq : ∀ u ∈ U, u * u = 1 := fun u hu => by
    have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) u hu
    rwa [pow_two] at h
  have hUa : ∀ u ∈ U, a⁻¹ * u * a ∈ U := fun u hu => (mem_normalizer_iff''.mp haU u).mp hu
  have hBU : B ≤ U := by
    rw [closure_le]
    rintro x ⟨u, hu, rfl⟩
    exact U.mul_mem (U.inv_mem hu) (hUa u hu)
  have haU' : a ∉ U := by
    intro haU'
    apply hB
    rw [eq_bot_iff, closure_le]
    rintro x ⟨u, hu, rfl⟩
    have h : a⁻¹ * u * a = u := by
      rw [mul_assoc, hUcomm u hu a haU', ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h, inv_mul_cancel]
    exact one_mem _
  have hJconj : ∀ c ∈ centralizer ({a} : Set F), ∀ j ∈ J, c * j * c⁻¹ ∈ J := by
    intro c hc j hj
    exact mem_subgroupOf.mp (hJn.conj_mem ⟨j, hJa hj⟩ (mem_subgroupOf.mpr hj) ⟨c, hc⟩)
  have hkey : ∀ A : Subgroup F, A.Normal → Odd (Nat.card A) → B ≤ centralizer (A : Set F) := by
    intro A hAn hAodd
    have hAJ : ∀ x ∈ A, x ∈ J → x = 1 := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf J) with h | h
      · exact fun x hxA hxJ => disjoint_def.mp (subgroupOf_eq_bot.mp h) hxA hxJ
      · exfalso
        have hJA : J ≤ A := subgroupOf_eq_top.mp h
        obtain ⟨⟨x, hxB⟩, hx1⟩ := ne_bot_iff_exists_ne_one.mp hB
        have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
        have hxo : orderOf x = 2 := by
          have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          exact orderOf_eq_prime (by rw [pow_two]; exact hUsq x (hBU hxB)) hx1'
        have hdvd : 2 ∣ Nat.card A := hxo ▸ orderOf_dvd_natCard A (hJA (hBJ hxB))
        exact (Nat.not_even_iff_odd.mpr hAodd) (even_iff_two_dvd.mpr hdvd)
    have hJCA : ∀ j ∈ J, ∀ x ∈ A, x * a = a * x → j * x = x * j := by
      intro j hj x hxA hxa
      have hxC : x ∈ centralizer ({a} : Set F) := mem_centralizer_singleton_iff.mpr hxa
      have hcomm : x⁻¹ * j⁻¹ * x * j = 1 := by
        apply hAJ
        · have h1 : j⁻¹ * x * j ∈ A := by simpa using hAn.conj_mem x hxA j⁻¹
          have h2 : x⁻¹ * j⁻¹ * x * j = x⁻¹ * (j⁻¹ * x * j) := by group
          rw [h2]
          exact A.mul_mem (A.inv_mem hxA) h1
        · have h1 : x⁻¹ * j⁻¹ * x ∈ J := by
            simpa using hJconj x⁻¹ (inv_mem hxC) j⁻¹ (J.inv_mem hj)
          exact J.mul_mem h1 hj
      calc j * x = j * x * (x⁻¹ * j⁻¹ * x * j) := by rw [hcomm, mul_one]
        _ = x * j := by group
    have hAnorm : ∀ g : F, g ∈ normalizer (A : Set F) := fun g => by
      rw [normalizer_eq_top_iff.mpr hAn]
      exact mem_top g
    rw [closure_le]
    rintro b ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro x hxA
    by_cases hb1 : u⁻¹ * (a⁻¹ * u * a) = 1
    · rw [hb1, mul_one, one_mul]
    have hbB : u⁻¹ * (a⁻¹ * u * a) ∈ B := subset_closure ⟨u, hu, rfl⟩
    set b := u⁻¹ * (a⁻¹ * u * a) with hb
    have hbJ : b ∈ J := hBJ hbB
    have hbU : b ∈ U := hBU hbB
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hUsq u hu)
    have h1 : b = u * (a * u * a) := by rw [hb, hainv, huinv]
    have hc : a * u * a * u = u * (a * u * a) := by
      have h := hUcomm u hu _ (hUa u hu)
      rw [hainv] at h
      exact h.symm
    have hab : a * b = b * a := by
      rw [h1]
      calc a * (u * (a * u * a)) = a * u * a * u * a := by group
        _ = u * (a * u * a) * a := by rw [hc]
    have hau : u⁻¹ * a * u = a * b := by
      rw [h1, huinv]
      calc u * a * u = u * (a * u * a) * a := by
            rw [show u * (a * u * a) * a = u * a * u * (a * a) by group, ha2, mul_one]
        _ = a * u * a * u * a := by rw [hc]
        _ = a * (u * (a * u * a)) := by group
    have hne : a ≠ b := fun h => haU' (h ▸ hbU)
    have hzab : ∀ x ∈ A, x * (a * b) = a * b * x → b * x = x * b := by
      intro x hxA hx
      rw [← hau] at hx
      have hyA : u * x * u⁻¹ ∈ A := hAn.conj_mem x hxA u
      have hya : u * x * u⁻¹ * a = a * (u * x * u⁻¹) := by
        calc u * x * u⁻¹ * a = u * (x * (u⁻¹ * a * u)) * u⁻¹ := by group
          _ = u * ((u⁻¹ * a * u) * x) * u⁻¹ := by rw [hx]
          _ = a * (u * x * u⁻¹) := by group
      have hby := hJCA b hbJ _ hyA hya
      have hbu : b * u = u * b := hUcomm b hbU u hu
      calc b * x = b * u⁻¹ * (u * x * u⁻¹) * u := by group
        _ = b * u * (u * x * u⁻¹) * u := by rw [huinv]
        _ = u * (b * (u * x * u⁻¹)) * u := by rw [hbu]; group
        _ = u * ((u * x * u⁻¹) * b) * u := by rw [hby]
        _ = u * (u * x * u⁻¹) * (b * u) := by group
        _ = u * (u * x * u⁻¹) * (u * b) := by rw [hbu]
        _ = u * u * x * (u⁻¹ * u) * b := by group
        _ = x * b := by rw [hUsq u hu, inv_mul_cancel]; group
    exact (commute_of_four_group_centralizers hAodd ha2 (hUsq b hbU) hab ha1 hb1 hne
      (hAnorm a) (hAnorm b) (fun y hy hya => hJCA b hbJ y hy hya)
      (fun y _ hyb => hyb.symm) hzab x hxA).symm
  have hJcent : ∀ A : Subgroup F, A.Normal → Odd (Nat.card A) →
      J ≤ centralizer (A : Set F) := by
    intro A hAn hAodd
    have hBC := hkey A hAn hAodd
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((centralizer (A : Set F)).subgroupOf J)
      with h | h
    · exfalso
      apply hB
      rw [eq_bot_iff]
      intro x hx
      exact mem_bot.mpr (disjoint_def.mp (subgroupOf_eq_bot.mp h) (hBC hx) (hBJ hx))
    · exact subgroupOf_eq_top.mp h
  subst hL
  have hcomm : ∀ A : Subgroup F, A.Normal → Odd (Nat.card A) →
      ⁅A, normalClosure (J : Set F)⁆ = ⊥ := by
    intro A hAn hAodd
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
    exact normalClosure_le_normal (hJcent A hAn hAodd)
  have hJperf : ⁅J, J⁆ = J := by
    rw [← isPerfect_iff]
    constructor
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator J) with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hJnab
      have : IsMulCommutative J := (commutator_eq_bot_iff J).mp h
      exact hxy (mul_comm' x y)
    · exact h
  have hperf : Group.IsPerfect (normalClosure (J : Set F)) := by
    rw [isPerfect_iff]
    apply le_antisymm (commutator_le_left _ _)
    apply normalClosure_le_normal
    intro x hx
    have hJL : J ≤ normalClosure (J : Set F) := le_normalClosure
    rw [← hJperf] at hx
    exact commutator_mono hJL hJL hx
  refine ⟨hperf, hcomm, fun hCD => ?_⟩
  set L := normalClosure (J : Set F) with hLdef
  set R := CFSG.oddCore F with hR
  set θ := QuotientGroup.mk' R with hθ
  have hRodd : Odd (Nat.card R) := odd_card_oddCore F
  have hRL : R ≤ centralizer (L : Set F) :=
    commutator_eq_bot_iff_le_centralizer.mp (hcomm R inferInstance hRodd)
  have hCL : centralizer (L : Set F) = R := by
    apply le_antisymm _ hRL
    intro c hc
    have hθc : θ c ∈ centralizer (L.map θ : Set (F ⧸ R)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨l, hl, rfl⟩
      rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hc l hl]
    rw [hCD, mem_bot] at hθc
    exact (QuotientGroup.eq_one_iff c).mp hθc
  have hZ : (center L).map L.subtype = L ⊓ R := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine mem_inf.mpr ⟨y.2, ?_⟩
      rw [← hCL, mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (mem_center_iff.mp hy ⟨l, hl⟩)
    · intro hx
      obtain ⟨hxL, hxR⟩ := mem_inf.mp hx
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.mp (hRL hxR) g g.2)
  have hO : (CFSG.oddCore L).map L.subtype = L ⊓ R := by
    apply le_antisymm
    · refine le_inf (map_subtype_le _) ?_
      have : (CFSG.oddCore L).Characteristic := oddCore_characteristic L
      refine le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, ?_⟩
      rw [card_subtype]
      exact odd_card_oddCore L
    · rw [inf_comm, ← subgroupOf_map_subtype]
      apply map_mono
      refine le_sSup ⟨normal_subgroupOf, ?_⟩
      have hcard : Nat.card (R.subgroupOf L) = Nat.card (R ⊓ L : Subgroup F) := by
        rw [← subgroupOf_map_subtype, card_subtype]
      rw [hcard]
      exact hRodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  let ψ : L →* F ⧸ R := θ.comp L.subtype
  have hker : center L = ψ.ker := by
    apply map_injective L.subtype_injective
    have h : ψ.ker = R.subgroupOf L := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      exact QuotientGroup.eq_one_iff (x : F)
    rw [hZ, h, subgroupOf_map_subtype, inf_comm]
  have hrange : ψ.range = L.map θ := by
    rw [MonoidHom.range_comp, range_subtype]
  refine ⟨hCL, hZ.trans hO.symm, hO, (QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange)), ?_⟩
  intro x
  rfl

end CFSG.LocalAnalysis.ComponentInitial
