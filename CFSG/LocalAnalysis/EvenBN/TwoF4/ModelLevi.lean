module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelLeviWeyl
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.GroupTheory.ABGLocalTools.Basic

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair pairedTorusHom f4i)

section Centralizer

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem weylRepHom_mem_normalizer_torusH (hK : Nat.card K = 2 ^ (2 * a + 1))
    {w : WeylGroup F4.tag} (hw : w ∈ F4.relWeylRee) :
    weylRepHom K w ∈ Subgroup.normalizer (torusH K a : Set (ModGL F4.tag K)) := by
  have h : weylRepHom K w ∈ F4.relWeylRee.map (weylRepHom K) := ⟨w, hw, rfl⟩
  rw [map_weylRepHom_relWeylRee] at h
  refine (Subgroup.closure_le _).2 ?_ h
  rintro _ (rfl | rfl)
  · exact weylR_mem_normalizer_torusH hK
  · exact weylS_mem_normalizer_torusH hK

theorem reeGamma_inf_centralizer_torusHi_le (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx} (hi : i = .i1 ∨ i = .i3) :
    F4.reeGamma K a ⊓ Subgroup.centralizer (torusHi K a i : Set (ModGL F4.tag K)) ≤
      torusH K a ⊔ leviN K a i := by
  intro g hg
  obtain ⟨hgΓ, hgc⟩ := Subgroup.mem_inf.1 hg
  have hi' : i.isCenter = false := by rcases hi with rfl | rfl <;> rfl
  have hg' : g ∈ (F4.reeGamma K a : Set (ModGL F4.tag K)) := hgΓ
  rw [reeGamma_eq_iUnion_reeFixedBruhatCell] at hg'
  obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨k, rfl⟩ := exists_fixedRelElt_eq hw
  obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, hbu⟩ := (bijOn_reeFixedBruhatCell hw).2.2 hgw
  simp only at hbu
  set n := canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k) with hn
  have hnH : n ∈ Subgroup.normalizer (torusH K a : Set (ModGL F4.tag K)) :=
    weylRepHom_mem_normalizer_torusH hK hw
  have hHB : torusH K a ≤ F4.reeFixedBorel K a := by
    rw [torusH_eq_reeFixedTorus hK]
    exact reeFixedTorus_le_reeFixedBorel
  have hHT : torusH K a ≤ torusGroup F4.tag K := by
    rw [torusH_eq_reeFixedTorus hK]
    exact inf_le_left
  have key : ∀ h ∈ torusHi K a i,
      h * b * h⁻¹ * (h * n * h⁻¹ * n⁻¹) = b ∧ h * u * h⁻¹ = u := by
    intro h hh
    have hhH : h ∈ torusH K a := torusHi_le_torusH i hh
    have hc : h * n * h⁻¹ * n⁻¹ ∈ torusH K a := by
      have : n * h⁻¹ * n⁻¹ ∈ torusH K a :=
        (Subgroup.mem_normalizer_iff.1 hnH _).1 (inv_mem hhH)
      rw [show h * n * h⁻¹ * n⁻¹ = h * (n * h⁻¹ * n⁻¹) by group]
      exact mul_mem hhH this
    have hb' : h * b * h⁻¹ * (h * n * h⁻¹ * n⁻¹) ∈ F4.reeFixedBorel K a :=
      mul_mem (mul_mem (mul_mem (hHB hhH) hb) (inv_mem (hHB hhH))) (hHB hc)
    have hu' : h * u * h⁻¹ ∈ F4.reeFixedCellUnipotent K a (F4.fixedRelElt k) :=
      (Subgroup.mem_normalizer_iff.1 (torusH_le_normalizer_rootSpan_inf hK
        (fun α hα => (inversionSet_pos hα).1) hhH) u).1 hu
    have hcomm : h * g = g * h := Subgroup.mem_centralizer_iff.1 hgc h hh
    have heq : (h * b * h⁻¹ * (h * n * h⁻¹ * n⁻¹)) * n * (h * u * h⁻¹) = b * n * u := by
      calc (h * b * h⁻¹ * (h * n * h⁻¹ * n⁻¹)) * n * (h * u * h⁻¹) = h * (b * n * u) * h⁻¹ := by
            group
        _ = b * n * u := by rw [hbu, hcomm, mul_inv_cancel_right]
    have := (bijOn_reeFixedBruhatCell hw).2.1 (Set.mk_mem_prod hb' hu') (Set.mk_mem_prod hb hu) heq
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have huV : u ∈ rootV K a i := by
    rw [← sylowP_inf_centralizer_torusHi ha hK hi']
    refine Subgroup.mem_inf.2 ⟨reeFixedCellUnipotent_le_reeFixedPosUnipotent _ hu,
      Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have h1 := (key h hh).2
    calc h * u = h * u * h⁻¹ * h := by group
      _ = u * h := by rw [h1]
  have hb2 : b ∈ (F4.reeFixedBorel K a : Set (ModGL F4.tag K)) := hb
  rw [reeFixedBorel_eq_mul] at hb2
  obtain ⟨h₀, hh₀, v, hv, rfl⟩ := Set.mem_mul.1 hb2
  have hh₀' : h₀ ∈ torusH K a := by rw [torusH_eq_reeFixedTorus hK]; exact hh₀
  have key2 : ∀ h ∈ torusHi K a i, h * n * h⁻¹ * n⁻¹ = 1 ∧ h * v * h⁻¹ = v := by
    intro h hh
    have hhH : h ∈ torusH K a := torusHi_le_torusH i hh
    have hcomm : h * h₀ = h₀ * h := torusH_mul_comm hhH hh₀'
    have k2 : (h * v * h⁻¹) * (h * n * h⁻¹ * n⁻¹) = v := by
      apply mul_left_cancel (a := h₀)
      calc h₀ * ((h * v * h⁻¹) * (h * n * h⁻¹ * n⁻¹)) =
          h * (h₀ * v) * h⁻¹ * (h * n * h⁻¹ * n⁻¹) := by
            rw [show h * (h₀ * v) * h⁻¹ = (h * h₀) * v * h⁻¹ by group, hcomm]
            group
        _ = h₀ * v := (key h hh).1
    have hvU : h * v * h⁻¹ ∈ F4.reeFixedPosUnipotent K a :=
      (Subgroup.mem_normalizer_iff.1 (torusH_le_normalizer_sylowP hK hhH) v).1 hv
    have hc : h * n * h⁻¹ * n⁻¹ ∈ torusH K a := by
      have : n * h⁻¹ * n⁻¹ ∈ torusH K a :=
        (Subgroup.mem_normalizer_iff.1 hnH _).1 (inv_mem hhH)
      rw [show h * n * h⁻¹ * n⁻¹ = h * (n * h⁻¹ * n⁻¹) by group]
      exact mul_mem hhH this
    have hc_eq : h * n * h⁻¹ * n⁻¹ = (h * v * h⁻¹)⁻¹ * v := eq_inv_mul_of_mul_eq k2
    have hcU : h * n * h⁻¹ * n⁻¹ ∈ posUnipotent F4.tag K := by
      rw [hc_eq]
      exact mul_mem (inv_mem (Subgroup.mem_inf.1 hvU).1) (Subgroup.mem_inf.1 hv).1
    have h1 : h * n * h⁻¹ * n⁻¹ = 1 := by
      have := Subgroup.mem_inf.2 ⟨hHT hc, hcU⟩
      rwa [torusGroup_inf_posUnipotent, Subgroup.mem_bot] at this
    refine ⟨h1, ?_⟩
    rw [h1, mul_one] at k2
    exact k2
  have hvV : v ∈ rootV K a i := by
    rw [← sylowP_inf_centralizer_torusHi ha hK hi']
    refine Subgroup.mem_inf.2 ⟨hv, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have h1 := (key2 h hh).2
    calc h * v = h * v * h⁻¹ * h := by group
      _ = v * h := by rw [h1]
  have hnc : ∀ h ∈ torusHi K a i,
      weylRepHom K (F4.fixedRelElt k) * h = h * weylRepHom K (F4.fixedRelElt k) := by
    intro h hh
    have h1 := (key2 h hh).1
    change n * h = h * n
    calc n * h = (h * n * h⁻¹ * n⁻¹)⁻¹ * h * n := by group
      _ = h * n := by rw [h1, inv_one, one_mul]
  have hnN : n ∈ leviN K a i := by
    rcases hi with rfl | rfl
    · rcases weylRepHom_eq_of_commute_torusHi_one ha hK k hnc with h | h
      · change weylRepHom K (F4.fixedRelElt k) ∈ _
        rw [h]
        exact one_mem _
      · change weylRepHom K (F4.fixedRelElt k) ∈ _
        rw [h]
        exact weylR_mem_leviN
    · rcases weylRepHom_eq_of_commute_torusHi_three ha hK k hnc with h | h
      · change weylRepHom K (F4.fixedRelElt k) ∈ _
        rw [h]
        exact one_mem _
      · change weylRepHom K (F4.fixedRelElt k) ∈ _
        rw [h]
        exact weylS_mem_leviN
  rw [← hbu]
  exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left hh₀')
    (Subgroup.mem_sup_right (rootV_le_leviN hK i hvV))) (Subgroup.mem_sup_right hnN))
    (Subgroup.mem_sup_right (rootV_le_leviN hK i huV))

end Centralizer

section Simple

variable {G : Type*} [Group G]

theorem commutator_eq_self_of_isSimpleGroup {N : Subgroup G} (hs : IsSimpleGroup N)
    (hne : ∃ x y : N, x * y ≠ y * x) : ⁅N, N⁆ = N := by
  have hnorm : (⁅(⊤ : Subgroup N), ⊤⁆ : Subgroup N).Normal := inferInstance
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hnorm with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact hxy (Subgroup.mem_centralizer_iff.1 (h (Subgroup.mem_top y)) x (Subgroup.mem_top x))
  · have := congrArg (Subgroup.map N.subtype) h
    rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this

theorem eq_one_of_forall_commute_of_isSimpleGroup {N : Subgroup G} (hs : IsSimpleGroup N)
    (hne : ∃ x y : N, x * y ≠ y * x) {x : G} (hx : x ∈ N) (hc : ∀ y ∈ N, x * y = y * x) :
    x = 1 := by
  have hnorm : (Subgroup.center N).Normal := inferInstance
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hnorm with h | h
  · have hmem : (⟨x, hx⟩ : N) ∈ Subgroup.center N :=
      Subgroup.mem_center_iff.2 fun y => Subtype.ext (hc y y.2).symm
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    obtain ⟨y, z, hyz⟩ := hne
    have hy : y ∈ Subgroup.center N := h ▸ Subgroup.mem_top y
    exact hyz (Subgroup.mem_center_iff.1 hy z).symm

theorem isSimpleGroup_map_conj {R : Subgroup G} (hs : IsSimpleGroup R)
    (hne : ∃ x y : R, x * y ≠ y * x) (g : G) :
    IsSimpleGroup (R.map (MulAut.conj g).toMonoidHom) ∧
      ∃ x y : R.map (MulAut.conj g).toMonoidHom, x * y ≠ y * x := by
  have := hs
  let e := Subgroup.equivMapOfInjective R (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  obtain ⟨x, y, hxy⟩ := hne
  refine ⟨e x, e y, fun h => hxy ?_⟩
  rw [← map_mul, ← map_mul] at h
  exact e.injective h

theorem isSylowOf_two_of_card {V N : Subgroup G} (hVN : V ≤ N) {k m : ℕ}
    (hV : Nat.card V = 2 ^ k) (hN : Nat.card N = 2 ^ k * m) (hm : Odd m) :
    CFSG.ABGLocalTools.IsSylowOf 2 V N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (V.subgroupOf N) = 2 ^ k := by
    rw [← hV]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv
  have hidx : ¬ 2 ∣ (V.subgroupOf N).index := by
    intro h2
    have h := Subgroup.card_mul_index (V.subgroupOf N)
    rw [hcard, hN] at h
    rw [Nat.eq_of_mul_eq_mul_left (by positivity) h] at h2
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h2)
  exact ⟨(IsPGroup.of_card hcard).toSylow hidx, by
    rw [IsPGroup.toSylow_coe, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hVN]⟩

open scoped Pointwise commutatorElement in
theorem commutator_sup_le_of_central {Z N : Subgroup G}
    (hZ : ∀ z ∈ Z, ∀ y ∈ Z ⊔ N, z * y = y * z) : ⁅Z ⊔ N, Z ⊔ N⁆ ≤ ⁅N, N⁆ := by
  have hle : Z ≤ Subgroup.normalizer (N : Set G) := fun z hz =>
    mem_normalizer_of_conj_mem (fun n hn => by
        rw [hZ z hz n (Subgroup.mem_sup_right hn), mul_inv_cancel_right]
        exact hn)
      fun n hn => by
        rw [mul_assoc, ← hZ z hz n (Subgroup.mem_sup_right hn), inv_mul_cancel_left]
        exact hn
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right Z N hle
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have h1 : g₁ ∈ (Z : Set G) * (N : Set G) := by rw [← hcoe]; exact hg₁
  have h2 : g₂ ∈ (Z : Set G) * (N : Set G) := by rw [← hcoe]; exact hg₂
  obtain ⟨z₁, hz₁, n₁, hn₁, rfl⟩ := Set.mem_mul.1 h1
  obtain ⟨z₂, hz₂, n₂, hn₂, rfl⟩ := Set.mem_mul.1 h2
  have hn₁' : n₁ ∈ Z ⊔ N := Subgroup.mem_sup_right hn₁
  have hn₂' : n₂ ∈ Z ⊔ N := Subgroup.mem_sup_right hn₂
  have hz₂' : z₂ ∈ Z ⊔ N := Subgroup.mem_sup_left hz₂
  have hX : n₁ * z₂ * n₂ * n₁⁻¹ ∈ Z ⊔ N :=
    mul_mem (mul_mem (mul_mem hn₁' hz₂') hn₂') (inv_mem hn₁')
  have hY : n₁ * n₂ * n₁⁻¹ * n₂⁻¹ ∈ Z ⊔ N :=
    mul_mem (mul_mem (mul_mem hn₁' hn₂') (inv_mem hn₁')) (inv_mem hn₂')
  have e : ⁅z₁ * n₁, z₂ * n₂⁆ = ⁅n₁, n₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc z₁ * n₁ * (z₂ * n₂) * (z₁ * n₁)⁻¹ * (z₂ * n₂)⁻¹ =
        z₁ * (n₁ * z₂ * n₂ * n₁⁻¹) * z₁⁻¹ * n₂⁻¹ * z₂⁻¹ := by group
      _ = n₁ * z₂ * n₂ * n₁⁻¹ * n₂⁻¹ * z₂⁻¹ := by
        rw [hZ z₁ hz₁ _ hX, mul_inv_cancel_right]
      _ = z₂ * (n₁ * n₂ * n₁⁻¹ * n₂⁻¹) * z₂⁻¹ := by
        rw [show n₁ * z₂ = z₂ * n₁ from (hZ z₂ hz₂ n₁ hn₁').symm]
        group
      _ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by rw [hZ z₂ hz₂ _ hY, mul_inv_cancel_right]
  rw [e]
  exact Subgroup.commutator_mem_commutator hn₁ hn₂

end Simple

section Levi22

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem isSimpleGroup_leviN (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    IsSimpleGroup (leviN K a i) ∧ ∃ x y : leviN K a i, x * y ≠ y * x := by
  obtain ⟨h1, h1'⟩ := isSimpleGroup_rankOneGroupOne (K := K) ha hK
  obtain ⟨h2, h2'⟩ := isSimpleGroup_rankOneGroupTwo (K := K) ha hK
  cases i
  case i1 | i2 => exact ⟨h2, h2'⟩
  case i3 => exact ⟨h1, h1'⟩
  case i4 | i8 | i6 | i11 | i5 | i12 => exact isSimpleGroup_map_conj h2 h2' _
  case i7 | i9 | i10 => exact isSimpleGroup_map_conj h1 h1' _

theorem commutator_leviN (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    ⁅leviN K a i, leviN K a i⁆ = leviN K a i :=
  commutator_eq_self_of_isSimpleGroup (isSimpleGroup_leviN ha hK i).1
    (isSimpleGroup_leviN ha hK i).2

theorem isSylowOf_rootV_leviN (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isCenter = false) :
    CFSG.ABGLocalTools.IsSylowOf 2 (rootV K a i) (leviN K a i) := by
  have hq : Odd (2 ^ (2 * a + 1) - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  cases hlin : i.isLin
  · have hsz : i.isSz = true := by
      cases i <;> simp_all [Idx.isSz, Idx.isLin, Idx.isCenter]
    refine isSylowOf_two_of_card (rootV_le_leviN hK i) (k := 2 * (2 * a + 1))
      (m := (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)) ?_ ?_ ?_
    · rw [card_rootV hK]
      simp only [hsz, ↓reduceIte]
      rw [← pow_mul, mul_comm]
    · rw [card_leviN_of_not_isLin ha hK hlin, mul_assoc, ← pow_mul, mul_comm (2 * a + 1)]
    · exact hq.mul (Even.add_one (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩,
        by omega⟩))
  · have hsz : i.isSz = false := by
      cases i <;> simp_all [Idx.isSz, Idx.isLin, Idx.isCenter]
    refine isSylowOf_two_of_card (rootV_le_leviN hK i) (k := 2 * a + 1)
      (m := (2 ^ (2 * a + 1)) ^ 2 - 1) ?_ ?_ ?_
    · rw [card_rootV hK]
      simp only [hsz, Bool.false_eq_true, ↓reduceIte, pow_one]
    · rw [card_leviN_of_isLin hK hlin]
    · exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (Nat.two_pow_pos _))
        (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by omega⟩) odd_one

theorem leviN_one_le_centralizer (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    leviN K a .i1 ≤ Subgroup.centralizer (torusHi K a .i1 : Set (ModGL F4.tag K)) := by
  change rankOneGroupTwo K a ≤ _
  rw [rankOneGroupTwo, Subgroup.closure_le, reeFixedOrbitUnipotent_one_eq hK]
  rintro x ((hx | ⟨v, rfl⟩) | hx)
  · exact rootV_le_centralizer_torusHi _ hx
  · exact torusH_le_centralizer_torusHi _ (pairedTorusHom_mem_torusH v).2
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.mem_centralizer_iff.2 fun h hh =>
      ((weylR_commute_torusHi_weylS_commute_torusHi hK).1 h hh).symm

theorem leviN_three_le_centralizer (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    leviN K a .i3 ≤ Subgroup.centralizer (torusHi K a .i3 : Set (ModGL F4.tag K)) := by
  change rankOneGroupOne K a ≤ _
  rw [rankOneGroupOne, Subgroup.closure_le, reeFixedOrbitUnipotent_zero_eq hK]
  rintro x ((hx | ⟨u, rfl⟩) | hx)
  · exact rootV_le_centralizer_torusHi _ hx
  · exact torusH_le_centralizer_torusHi _ (pairedTorusHom_mem_torusH u).1
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.mem_centralizer_iff.2 fun h hh =>
      ((weylR_commute_torusHi_weylS_commute_torusHi hK).2 h hh).symm

theorem torusH_eq_sup_one (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    torusH K a = torusHi K a .i1 ⊔ (leviN K a .i1 ⊓ torusH K a) := by
  refine le_antisymm ?_ (sup_le (torusHi_le_torusH _) inf_le_right)
  rintro _ ⟨⟨u, v⟩, rfl⟩
  obtain ⟨⟨e10, e11⟩, -⟩ := torusExp_leadRoot ((2 : ℤ) ^ a)
  set w : Kˣ := u ^ (2 * (2 : ℤ) ^ a + 1) with hw
  have hwu : w ^ (2 * (2 : ℤ) ^ a - 1) = u := by
    rw [hw, ← zpow_mul]
    conv_rhs => rw [← zpow_one u]
    refine units_zpow_congr hK u 2 ?_
    rw [show (2 : ℤ) ^ (2 * a + 1) = 2 * (2 ^ a) ^ 2 by rw [pow_succ, pow_mul']; ring]
    ring
  have e : torusPair a (u, v) =
      torusPair a (torusHiParam K a .i1 w) * torusPair a (1, (w ^ (2 : ℤ) ^ a)⁻¹ * v) := by
    rw [← map_mul]
    congr 1
    simp only [torusHiParam, MonoidHom.prod_apply, zpowGroupHom_apply, e10, e11, neg_neg,
      Prod.mk_mul_mk, mul_one, hwu, mul_inv_cancel_left]
  rw [e]
  refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right
    (Subgroup.mem_inf.2 ⟨?_, ⟨_, rfl⟩⟩))
  · rw [← range_torusHiHom hK]
    exact ⟨w, rfl⟩
  · rw [rankOneTorusPair_right]
    exact Subgroup.subset_closure (Or.inl (Or.inr ⟨_, rfl⟩))

theorem torusH_eq_sup_three (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    torusH K a = torusHi K a .i3 ⊔ (leviN K a .i3 ⊓ torusH K a) := by
  refine le_antisymm ?_ (sup_le (torusHi_le_torusH _) inf_le_right)
  rintro _ ⟨⟨u, v⟩, rfl⟩
  obtain ⟨-, -, ⟨e30, e31⟩, -⟩ := torusExp_leadRoot ((2 : ℤ) ^ a)
  set w : Kˣ := v ^ (-(2 : ℤ) ^ a) with hw
  have hwv : w ^ (-(2 * (2 : ℤ) ^ a)) = v := by
    rw [hw, ← zpow_mul]
    conv_rhs => rw [← zpow_one v]
    refine units_zpow_congr hK v 1 ?_
    rw [show (2 : ℤ) ^ (2 * a + 1) = 2 * (2 ^ a) ^ 2 by rw [pow_succ, pow_mul']; ring]
    ring
  have e : torusPair a (u, v) =
      torusPair a (torusHiParam K a .i3 w) * torusPair a ((w ^ (-(2 : ℤ) ^ a))⁻¹ * u, 1) := by
    rw [← map_mul]
    congr 1
    simp only [torusHiParam, MonoidHom.prod_apply, zpowGroupHom_apply, e30, e31,
      Prod.mk_mul_mk, mul_one, hwv, mul_inv_cancel_left]
  rw [e]
  refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right
    (Subgroup.mem_inf.2 ⟨?_, ⟨_, rfl⟩⟩))
  · rw [← range_torusHiHom hK]
    exact ⟨w, rfl⟩
  · rw [rankOneTorusPair_left]
    exact Subgroup.subset_closure (Or.inl (Or.inr ⟨_, rfl⟩))

theorem levi_core_one_three (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i = .i1 ∨ i = .i3) :
    F4.reeGamma K a ⊓ Subgroup.centralizer (torusHi K a i : Set (ModGL F4.tag K)) =
        torusHi K a i ⊔ leviN K a i ∧
      leviN K a i ≤ Subgroup.centralizer (torusHi K a i : Set (ModGL F4.tag K)) ∧
      torusH K a = torusHi K a i ⊔ (leviN K a i ⊓ torusH K a) := by
  have h2 : leviN K a i ≤ Subgroup.centralizer (torusHi K a i : Set (ModGL F4.tag K)) := by
    rcases hi with rfl | rfl
    · exact leviN_one_le_centralizer hK
    · exact leviN_three_le_centralizer hK
  have h3 : torusH K a = torusHi K a i ⊔ (leviN K a i ⊓ torusH K a) := by
    rcases hi with rfl | rfl
    · exact torusH_eq_sup_one hK
    · exact torusH_eq_sup_three hK
  refine ⟨le_antisymm ((reeGamma_inf_centralizer_torusHi_le ha hK hi).trans
    (sup_le (h3.le.trans (sup_le le_sup_left (inf_le_left.trans le_sup_right))) le_sup_right))
    (sup_le (le_inf ((torusHi_le_torusH i).trans (torusH_le_reeGamma hK))
      ((torusHi_le_torusH i).trans (torusH_le_centralizer_torusHi i)))
      (le_inf (leviN_le_reeGamma hK i) h2)), h2, h3⟩

theorem levi_core_map {i j : Idx} {g : ModGL F4.tag K} (hgΓ : g ∈ F4.reeGamma K a)
    (hgH : g ∈ Subgroup.normalizer (torusH K a : Set (ModGL F4.tag K)))
    (hH : (torusHi K a i).map (MulAut.conj g).toMonoidHom = torusHi K a j)
    (hN : (leviN K a i).map (MulAut.conj g).toMonoidHom = leviN K a j)
    (h : F4.reeGamma K a ⊓ Subgroup.centralizer (torusHi K a i : Set (ModGL F4.tag K)) =
        torusHi K a i ⊔ leviN K a i ∧
      leviN K a i ≤ Subgroup.centralizer (torusHi K a i : Set (ModGL F4.tag K)) ∧
      torusH K a = torusHi K a i ⊔ (leviN K a i ⊓ torusH K a)) :
    F4.reeGamma K a ⊓ Subgroup.centralizer (torusHi K a j : Set (ModGL F4.tag K)) =
        torusHi K a j ⊔ leviN K a j ∧
      leviN K a j ≤ Subgroup.centralizer (torusHi K a j : Set (ModGL F4.tag K)) ∧
      torusH K a = torusHi K a j ⊔ (leviN K a j ⊓ torusH K a) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hΓ := map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hgΓ)
  have hHH := map_conj_eq_of_mem_normalizer hgH
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h1
    rwa [Subgroup.map_inf_eq _ _ _ hinj, hΓ, map_conj_centralizer, hH, Subgroup.map_sup, hH,
      hN] at this
  · rw [← hN, ← hH, ← map_conj_centralizer]
    exact Subgroup.map_mono h2
  · have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h3
    rwa [hHH, Subgroup.map_sup, Subgroup.map_inf_eq _ _ _ hinj, hH, hN, hHH] at this

theorem levi_core (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isCenter = false) :
    F4.reeGamma K a ⊓ Subgroup.centralizer (torusHi K a i : Set (ModGL F4.tag K)) =
        torusHi K a i ⊔ leviN K a i ∧
      leviN K a i ≤ Subgroup.centralizer (torusHi K a i : Set (ModGL F4.tag K)) ∧
      torusH K a = torusHi K a i ⊔ (leviN K a i ⊓ torusH K a) := by
  have hs := weylS_mem_reeGamma (K := K) (a := a)
  have hr := weylR_mem_reeGamma (K := K) (a := a)
  have hsN := weylS_mem_normalizer_torusH (K := K) hK
  have hrN := weylR_mem_normalizer_torusH (K := K) hK
  have c1 := levi_core_one_three ha hK (i := .i1) (Or.inl rfl)
  have c3 := levi_core_one_three ha hK (i := .i3) (Or.inr rfl)
  have c4 := levi_core_map (j := .i4) hs hsN (map_conj_weylS_torusHi hK (i := .i1) (by decide))
    rfl c1
  have c6 := levi_core_map (j := .i6) hr hrN
    (map_conj_weylR_torusHi hK (i := .i4) (by decide) (by decide))
    (map_conj_mul (rankOneGroupTwo K a) _ _).symm c4
  have c5 := levi_core_map (j := .i5) hs hsN (map_conj_weylS_torusHi hK (i := .i6) (by decide))
    (by
      change ((rankOneGroupTwo K a).map (MulAut.conj (weylR K * weylS K)).toMonoidHom).map
        (MulAut.conj (weylS K)).toMonoidHom =
          (rankOneGroupTwo K a).map (MulAut.conj (weylS K * weylR K * weylS K)).toMonoidHom
      rw [← map_conj_mul, mul_assoc]) c6
  have c7 := levi_core_map (j := .i7) hr hrN
    (map_conj_weylR_torusHi hK (i := .i3) (by decide) (by decide)) rfl c3
  have c9 := levi_core_map (j := .i9) hs hsN (map_conj_weylS_torusHi hK (i := .i7) (by decide))
    (map_conj_mul (rankOneGroupOne K a) _ _).symm c7
  have c10 := levi_core_map (j := .i10) hr hrN
    (map_conj_weylR_torusHi hK (i := .i9) (by decide) (by decide))
    (by
      change ((rankOneGroupOne K a).map (MulAut.conj (weylS K * weylR K)).toMonoidHom).map
        (MulAut.conj (weylR K)).toMonoidHom =
          (rankOneGroupOne K a).map (MulAut.conj (weylR K * weylS K * weylR K)).toMonoidHom
      rw [← map_conj_mul, mul_assoc]) c9
  cases i
  case i1 => exact c1
  case i3 => exact c3
  case i4 => exact c4
  case i5 => exact c5
  case i6 => exact c6
  case i7 => exact c7
  case i9 => exact c9
  case i10 => exact c10
  all_goals exact absurd hi (by decide)

theorem miyamoto_2_2 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isCenter = false) :
    F4.reeGamma K a ⊓ Subgroup.centralizer (torusHi K a i : Set (ModGL F4.tag K)) =
        torusHi K a i ⊔ leviN K a i ∧
      leviN K a i ≤ Subgroup.centralizer (torusHi K a i : Set (ModGL F4.tag K)) ∧
      torusHi K a i ⊓ leviN K a i = ⊥ ∧
      CFSG.Quasithin.perfectCore
          (F4.reeGamma K a ⊓ Subgroup.centralizer (torusHi K a i : Set (ModGL F4.tag K))) =
        leviN K a i ∧
      (i.isLin = false → Nonempty (leviN K a i ≃* CFSG.Blueprint.suzukiGroup a K)) ∧
      (i.isLin = true → Nonempty (leviN K a i ≃* SL2 K)) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (rootV K a i) (leviN K a i) ∧
      torusH K a = torusHi K a i ⊔ (leviN K a i ⊓ torusH K a) := by
  obtain ⟨h1, h2, h3⟩ := levi_core ha hK hi
  obtain ⟨hs, hne⟩ := isSimpleGroup_leviN ha hK i
  have hperf := commutator_leviN ha hK i
  refine ⟨h1, h2, ?_, ?_, fun h => nonempty_leviN_equiv_suzuki ha hK h,
    fun h => nonempty_leviN_equiv_SL2 hK h, isSylowOf_rootV_leviN ha hK hi, h3⟩
  · refine eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 ?_
    obtain ⟨hxH, hxN⟩ := Subgroup.mem_inf.1 hx
    exact eq_one_of_forall_commute_of_isSimpleGroup hs hne hxN fun y hy =>
      Subgroup.mem_centralizer_iff.1 (h2 hy) x hxH
  · refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect (h1 ▸ le_sup_right) hperf)
    refine (CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1).trans ?_
    rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero, h1]
    refine (commutator_sup_le_of_central fun z hz y hy => ?_).trans hperf.le
    have hle : torusHi K a i ⊔ leviN K a i ≤ Subgroup.centralizer {z} :=
      sup_le (fun w hw => Subgroup.mem_centralizer_singleton_iff.2
          (torusH_mul_comm (torusHi_le_torusH i hw) (torusHi_le_torusH i hz)))
        fun w hw => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 (h2 hw) z hz).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem reeFixedBorel_le_normalizer (hK : Nat.card K = 2 ^ (2 * a + 1))
    {U : Subgroup (ModGL F4.tag K)}
    (hP : F4.reeFixedPosUnipotent K a ≤ Subgroup.normalizer (U : Set (ModGL F4.tag K)))
    (hH : torusH K a ≤ Subgroup.normalizer (U : Set (ModGL F4.tag K))) :
    F4.reeFixedBorel K a ≤ Subgroup.normalizer (U : Set (ModGL F4.tag K)) := by
  intro b hb
  have hb' : b ∈ (F4.reeFixedBorel K a : Set (ModGL F4.tag K)) := hb
  rw [reeFixedBorel_eq_mul] at hb'
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hb'
  exact mul_mem (hH (by rw [torusH_eq_reeFixedTorus hK]; exact hh)) (hP hu)

theorem weylS_not_mem_normalizer_radR (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    weylS K ∉ Subgroup.normalizer (radR K a : Set (ModGL F4.tag K)) := by
  intro h
  have hA : rootElt K a .i3 1 ∈ F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ := by
    rw [reeFixedOrbitUnipotent_zero_eq hK]
    exact rootElt_mem_rootV _ _
  have hR : weylS K * rootElt K a .i3 1 * (weylS K)⁻¹ ∈ radR K a :=
    (Subgroup.mem_normalizer_iff.1 h _).1 (rootV_le_rootJoin (by decide) (rootElt_mem_rootV _ _))
  have h1 := eq_one_of_mem_reeFixedOrbitNegUnipotent_of_mem
    (conj_mem_reeFixedOrbitNegUnipotent (t := F4) hA)
    (reeFixedPosUnipotent_le_reeFixedBorel (rootJoin_le_sylowP hK _ hR))
  rw [mul_inv_eq_one, mul_eq_left] at h1
  exact one_ne_zero (rootElt_injective hK .i3 (h1.trans (rootElt_zero .i3).symm))

theorem weylR_not_mem_normalizer_radS (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    weylR K ∉ Subgroup.normalizer (radS K a : Set (ModGL F4.tag K)) := by
  intro h
  have hA : rootElt K a .i1 1 ∈ F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ := by
    rw [reeFixedOrbitUnipotent_one_eq hK]
    exact rootElt_mem_rootV _ _
  have hR : weylR K * rootElt K a .i1 1 * (weylR K)⁻¹ ∈ radS K a :=
    (Subgroup.mem_normalizer_iff.1 h _).1 (rootV_le_rootJoin (by decide) (rootElt_mem_rootV _ _))
  have h1 := eq_one_of_mem_reeFixedOrbitNegUnipotent_of_mem
    (conj_mem_reeFixedOrbitNegUnipotent (t := F4) hA)
    (reeFixedPosUnipotent_le_reeFixedBorel (rootJoin_le_sylowP hK _ hR))
  rw [mul_inv_eq_one, mul_eq_left] at h1
  exact one_ne_zero (rootElt_injective hK .i1 (h1.trans (rootElt_zero .i1).symm))

theorem reeGamma_inf_normalizer_radR (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ Subgroup.normalizer (radR K a : Set (ModGL F4.tag K)) =
      F4.reeLocalParabolic K a ⟨1, by decide⟩ := by
  have hspec := radR_spec (K := K) hK
  have hB : F4.reeFixedBorel K a ≤ F4.reeGamma K a ⊓
      Subgroup.normalizer (radR K a : Set (ModGL F4.tag K)) :=
    le_inf reeFixedBorel_le_reeGamma (reeFixedBorel_le_normalizer hK hspec.2.2.2 (by
      rw [hspec.1]
      exact torusH_le_normalizer_rootSpan_inf hK fun α hα => hα.1))
  have hr : weylR K ∈ Subgroup.normalizer (radR K a : Set (ModGL F4.tag K)) := by
    rw [radR_eq_complement hK]
    exact rankOneGroupTwo_le_normalizer_complement hK weylR_mem_leviN
  rw [(ree_Borel_overgroup_classification F4 a K _ hB inf_le_left).1]
  convert reeParabolic_singleton (t := F4) (K := K) (a := a) ⟨1, by decide⟩ using 2
  ext j
  change canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈
      F4.reeGamma K a ⊓ Subgroup.normalizer (radR K a : Set (ModGL F4.tag K)) ↔
    j ∈ ({⟨1, by decide⟩} : Set (Fin F4.fixedOrbitCount))
  rw [Set.mem_singleton_iff]
  fin_cases j
  · exact ⟨fun h => absurd (Subgroup.mem_inf.1 h).2 (weylS_not_mem_normalizer_radR hK),
      fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => rfl, fun _ => Subgroup.mem_inf.2 ⟨weylR_mem_reeGamma, hr⟩⟩

theorem reeGamma_inf_normalizer_radS (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ Subgroup.normalizer (radS K a : Set (ModGL F4.tag K)) =
      F4.reeLocalParabolic K a ⟨0, by decide⟩ := by
  have hspec := radS_spec (K := K) hK
  have hB : F4.reeFixedBorel K a ≤ F4.reeGamma K a ⊓
      Subgroup.normalizer (radS K a : Set (ModGL F4.tag K)) :=
    le_inf reeFixedBorel_le_reeGamma (reeFixedBorel_le_normalizer hK hspec.2.2.2 (by
      rw [hspec.1]
      exact torusH_le_normalizer_rootSpan_inf hK fun α hα => hα.1))
  have hs : weylS K ∈ Subgroup.normalizer (radS K a : Set (ModGL F4.tag K)) := by
    rw [radS_eq_complement hK]
    exact rankOneGroupOne_le_normalizer_complement hK weylS_mem_leviN
  rw [(ree_Borel_overgroup_classification F4 a K _ hB inf_le_left).1]
  convert reeParabolic_singleton (t := F4) (K := K) (a := a) ⟨0, by decide⟩ using 2
  ext j
  change canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈
      F4.reeGamma K a ⊓ Subgroup.normalizer (radS K a : Set (ModGL F4.tag K)) ↔
    j ∈ ({⟨0, by decide⟩} : Set (Fin F4.fixedOrbitCount))
  rw [Set.mem_singleton_iff]
  fin_cases j
  · exact ⟨fun _ => rfl, fun _ => Subgroup.mem_inf.2 ⟨weylS_mem_reeGamma, hs⟩⟩
  · exact ⟨fun h => absurd (Subgroup.mem_inf.1 h).2 (weylR_not_mem_normalizer_radS hK),
      fun h => absurd h (by decide)⟩

theorem miyamoto_2_3 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ Subgroup.normalizer (radR K a : Set (ModGL F4.tag K)) =
        radR K a ⊔ leviN K a .i1 ⊔ torusHi K a .i1 ∧
      F4.reeGamma K a ⊓ Subgroup.normalizer (radS K a : Set (ModGL F4.tag K)) =
        radS K a ⊔ leviN K a .i3 ⊔ torusHi K a .i3 ∧
      F4.reeGamma K a ⊓ Subgroup.normalizer (radR K a : Set (ModGL F4.tag K)) =
        F4.reeLocalParabolic K a ⟨1, by decide⟩ ∧
      F4.reeGamma K a ⊓ Subgroup.normalizer (radS K a : Set (ModGL F4.tag K)) =
        F4.reeLocalParabolic K a ⟨0, by decide⟩ := by
  have hR := reeGamma_inf_normalizer_radR (K := K) hK
  have hS := reeGamma_inf_normalizer_radS (K := K) hK
  have h1 := (levi_core_one_three ha hK (i := .i1) (Or.inl rfl)).2.2
  have h3 := (levi_core_one_three ha hK (i := .i3) (Or.inr rfl)).2.2
  have hH : torusH K a ≤ F4.reeGamma K a ⊓ Subgroup.normalizer (radR K a : Set _) ⊓
      Subgroup.normalizer (radS K a : Set (ModGL F4.tag K)) :=
    le_inf (le_inf (torusH_le_reeGamma hK) (by
      rw [(radR_spec hK).1]
      exact torusH_le_normalizer_rootSpan_inf hK fun α hα => hα.1)) (by
      rw [(radS_spec hK).1]
      exact torusH_le_normalizer_rootSpan_inf hK fun α hα => hα.1)
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_, hR, hS⟩
  · rw [hR]
    intro g hg
    obtain ⟨t, ht, x, hx, rfl⟩ := exists_mul_of_mem_reeLocalParabolic hK hg
    have htH : t ∈ torusH K a := by
      obtain ⟨u, rfl⟩ := ht
      exact (pairedTorusHom_mem_torusH u).1
    rw [h1] at htH
    have hle1 : torusHi K a .i1 ⊔ (leviN K a .i1 ⊓ torusH K a) ≤
        radR K a ⊔ leviN K a .i1 ⊔ torusHi K a .i1 :=
      sup_le le_sup_right (inf_le_left.trans (le_sup_right.trans le_sup_left))
    have hle2 : centralizerZ K a ≤ radR K a ⊔ leviN K a .i1 ⊔ torusHi K a .i1 := by
      rw [centralizerZ, ← radR_eq_complement hK]
      exact sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left)
    exact mul_mem (hle1 htH) (hle2 hx)
  · refine sup_le (sup_le (le_inf (rootJoin_le_sylowP hK _ |>.trans inf_le_right)
      Subgroup.le_normalizer) (le_inf (leviN_le_reeGamma hK _) ?_))
      ((torusHi_le_torusH _).trans (hH.trans inf_le_left))
    rw [radR_eq_complement hK]
    exact rankOneGroupTwo_le_normalizer_complement hK
  · rw [hS]
    intro g hg
    obtain ⟨t, ht, x, hx, rfl⟩ := exists_mul_of_mem_reeLocalParabolic_zero hK hg
    have htH : t ∈ torusH K a := by
      obtain ⟨v, rfl⟩ := ht
      exact (pairedTorusHom_mem_torusH v).2
    rw [h3] at htH
    have hle1 : torusHi K a .i3 ⊔ (leviN K a .i3 ⊓ torusH K a) ≤
        radS K a ⊔ leviN K a .i3 ⊔ torusHi K a .i3 :=
      sup_le le_sup_right (inf_le_left.trans (le_sup_right.trans le_sup_left))
    have hle2 : F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ⊔ rankOneGroupOne K a ≤
        radS K a ⊔ leviN K a .i3 ⊔ torusHi K a .i3 := by
      rw [← radS_eq_complement hK]
      exact sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left)
    exact mul_mem (hle1 htH) (hle2 hx)
  · refine sup_le (sup_le (le_inf (rootJoin_le_sylowP hK _ |>.trans inf_le_right)
      Subgroup.le_normalizer) (le_inf (leviN_le_reeGamma hK _) ?_))
      ((torusHi_le_torusH _).trans (hH.trans (le_inf (inf_le_left.trans inf_le_left)
        inf_le_right)))
    rw [radS_eq_complement hK]
    exact rankOneGroupOne_le_normalizer_complement hK

end Levi22

end CFSG.LocalAnalysis.EvenBN.TwoF4
