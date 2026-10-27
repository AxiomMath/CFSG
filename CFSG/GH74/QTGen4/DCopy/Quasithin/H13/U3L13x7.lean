module

public import CFSG.Quasithin.H13.U3L13x7
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S135Gen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem stmt13_3_7_of_F4 (h1332 : Stmt13_3_2_F4) (h1228 : Stmt12_2_8_F4) : A6.Stmt13_3_7_F4 := by
  intro G _ _ T L V hH hV hA6
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyp := hyp1223_of_F4 h1332 hH hV
  obtain ⟨h5, ⟨hTL, -, -, huniq⟩, ⟨-, hall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨hVT, hTV, -, -⟩ := hall V hV
  have hLV : L ≤ normalizer (V : Set G) := hV.2.2.1
  have hVf := fun v (hv : v ∈ V) => mem_reducedAggregate' (hV.1 hv)
  have hO : pCoreOf 2 L ≤ centralizer (V : Set G) := by
    refine (pCoreOf_le_pCoreOf_sup hTL).trans ?_
    intro k hk
    exact mem_centralizer_iff.2 fun v hv => ((hVf v hv).2.1 k hk).symm

  have hCM : centralizer (V : Set G) ≤ normalizer (L : Set G) := by
    have hV2 : IsPGroup 2 V := hH.sylow.1.to_le hVT
    obtain ⟨M', hM', hle⟩ :=
      exists_maxTwoLocal_ge (⟨V, hV.2.1, hV2, rfl⟩ : IsTwoLocal (normalizer (V : Set G)))
    have hM'eq := huniq M' hM' ((sup_le hLV hTV).trans hle)
    exact (centralizer_le_normalizer _).trans (hM'eq ▸ hle)

  have hcase := a6_or_hatA6_of_isA6On hLV hO h5 hA6
  have hQcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 ∨
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 := by
    rcases hcase with he | ⟨-, hz, ⟨e⟩⟩
    · left
      obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, card_alt6]
    · right
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (center (↥L ⧸ CFSG.pCore 2 ↥L))
      rw [Nat.card_congr e.toEquiv, card_alt6, hz] at h1
      rw [h1]

  have h3L : ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L := by
    intro x hx hx3
    rcases h1228 G T L V hyp with h | h | ⟨-, h⟩
    · rw [← h]
      exact subset_closure ⟨hx, 1, by rw [pow_one, ← hx3, pow_orderOf_eq_one]⟩
    · exfalso
      rcases h with he5 | h32
      · obtain ⟨e5⟩ := he5
        have := Nat.card_congr e5.toEquiv
        rw [card_alt5] at this
        omega
      · obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel h32
        have := Nat.card_congr e3.toEquiv
        rw [HSType.card_SL_three_two] at this
        omega
    · rw [h]
      exact subset_closure ⟨hx, hx3⟩
  have hCZ := centralizer_le_o2Z_of_isA6On hLV hO hyp.quasisimple hA6

  have hnot2 : ∀ y : ↥L, orderOf (y : G) = 3 → y ∉ CFSG.pCore 2 ↥L := by
    intro y hy3 hy
    obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨(y : G), coe_mem_pCoreOf_iff.2 hy⟩
    have h1 : (y : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hy3] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h2)
    omega

  have h3Z : ∀ x ∈ centralizer (V : Set G), orderOf x = 3 → x ∈ o2Z L :=
    fun x hx hx3 => hCZ ⟨h3L x (hCM hx) hx3, hx⟩
  rcases hcase with he6 | hHat
  ·
    obtain ⟨e6⟩ := he6
    left
    intro h3
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centralizer (V : Set G))) 3 h3
    have hx3 : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    obtain ⟨y, hy, hyx⟩ := h3Z x x.2 hx3
    have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hsQ : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := (MulEquiv.isSimpleGroup_congr e6).2 hs
    have hna : ∃ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := alt6_nonabelian
      exact ⟨e6.symm a, e6.symm b, fun h => hab (by simpa using congrArg e6 h)⟩
    have hcen := center_eq_bot_of_isSimpleGroup hna
    have hy1 : y ∈ CFSG.pCore 2 ↥L := by
      have : QuotientGroup.mk' (CFSG.pCore 2 ↥L) y ∈ center (↥L ⧸ CFSG.pCore 2 ↥L) := hy
      rw [hcen, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    exact hnot2 y (by rw [show (y : G) = x from hyx]; exact hx3) hy1
  · by_cases h3 : 3 ∣ Nat.card (centralizer (V : Set G))
    swap
    · exact Or.inl h3
    right
    refine ⟨hHat, ?_⟩
    obtain ⟨-, hz3, -⟩ := hHat
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centralizer (V : Set G))) 3 h3
    have hx3 : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    obtain ⟨x', hx'Z, hx'x⟩ := h3Z x x.2 hx3
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
    have hx'1 : π x' ≠ 1 := by
      intro h
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      exact hnot2 x' (by rw [show (x' : G) = x from hx'x]; exact hx3) h

    have hgen : ∀ z ∈ center (↥L ⧸ CFSG.pCore 2 ↥L), ∃ k : ℤ, z = π x' ^ k := by
      intro z hz
      have htop := zpowers_eq_top_of_prime_card hz3
        (g := (⟨π x', hx'Z⟩ : ↥(center (↥L ⧸ CFSG.pCore 2 ↥L))))
        (fun h => hx'1 (congrArg Subtype.val h))
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (htop ▸ mem_top (⟨z, hz⟩ :
        ↥(center (↥L ⧸ CFSG.pCore 2 ↥L))))
      exact ⟨k, by simpa using (congrArg Subtype.val hk).symm⟩

    have hZC : o2Z L ≤ centralizer (V : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := hgen _ hy
      have h1 : (x' ^ k)⁻¹ * y ∈ CFSG.pCore 2 ↥L := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_zpow]
        have : (QuotientGroup.mk y : ↥L ⧸ CFSG.pCore 2 ↥L) = π x' ^ k := hk
        rw [this]
        simp [hπ]
      have h2 : (((x' ^ k)⁻¹ * y : ↥L) : G) ∈ centralizer (V : Set G) :=
        hO (coe_mem_pCoreOf_iff.2 h1)
      have h3 : ((x' ^ k : ↥L) : G) ∈ centralizer (V : Set G) := by
        rw [SubgroupClass.coe_zpow, show (x' : G) = x from hx'x]
        exact zpow_mem x.2 k
      have e : ((y : ↥L) : G) = (x' ^ k : ↥L) * (((x' ^ k)⁻¹ * y : ↥L) : G) := by simp
      show ((y : ↥L) : G) ∈ _
      rw [e]
      exact mul_mem h3 h2

    have hodd3 : ∀ y ∈ o2Z L, ∀ m : ℕ, Odd m → y ^ m = 1 → y ^ 3 = 1 := by
      rintro _ ⟨y, hy, rfl⟩ m hm hym
      have h1 : π y ^ 3 = 1 := by
        have := pow_card_eq_one' (G := ↥(center (↥L ⧸ CFSG.pCore 2 ↥L))) (x := ⟨π y, hy⟩)
        rw [hz3] at this
        simpa using congrArg Subtype.val this
      have h2 : y ^ 3 ∈ CFSG.pCore 2 ↥L := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
        exact h1
      obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 L
        ⟨((y ^ 3 : ↥L) : G), coe_mem_pCoreOf_iff.2 h2⟩
      have h3 : ((y : G) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h4 : ((y : G) ^ 3) ^ m = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]
        have : (y : G) ^ m = 1 := by simpa using hym
        rw [this, one_pow]
      exact eq_one_of_pow_two_pow_of_odd hm h3 h4
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.Quasithin.pRank_top_subtype]
    refine ⟨le_antisymm ?_ ?_, ?_⟩
    ·
      obtain ⟨E, hEC, hEab, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
        (centralizer (V : Set G))
      have hEZ : ∀ e ∈ E, e ∈ o2Z L ∧ e ^ 3 = 1 := by
        intro e he
        have he3 : e ^ 3 = 1 := hEab.2 e he
        by_cases he1 : e = 1
        · rw [he1]
          exact ⟨one_mem _, one_pow 3⟩
        · exact ⟨h3Z e (hEC he) (orderOf_eq_prime he3 he1), he3⟩
      have hEL : E ≤ L := fun e he => map_subtype_le _ (hEZ e he).1
      let f : ↥E →* ↥L ⧸ CFSG.pCore 2 ↥L := π.comp (inclusion hEL)
      have hfZ : ∀ e : ↥E, f e ∈ center (↥L ⧸ CFSG.pCore 2 ↥L) := by
        intro e
        obtain ⟨y, hy, hye⟩ := (hEZ e e.2).1
        have : y = inclusion hEL e := Subtype.ext hye
        show π (inclusion hEL e) ∈ _
        rw [← this]
        exact hy
      let f' : ↥E →* ↥(center (↥L ⧸ CFSG.pCore 2 ↥L)) := f.codRestrict _ hfZ
      have hf' : Function.Injective f' := by
        rw [injective_iff_map_eq_one]
        intro e he
        have h1 : f e = 1 := congrArg Subtype.val he
        have h2 : inclusion hEL e ∈ CFSG.pCore 2 ↥L := by
          rw [← QuotientGroup.eq_one_iff]
          exact h1
        by_contra hne
        have hne' : (e : G) ≠ 1 := fun h => hne (Subtype.ext h)
        exact hnot2 (inclusion hEL e) (orderOf_eq_prime (hEZ e e.2).2 hne') h2
      have hle := Nat.card_le_card_of_injective f' hf'
      rw [hEc, hz3] at hle
      by_contra hgt
      push Not at hgt
      have h9 : 3 ^ 2 ≤ 3 := (Nat.pow_le_pow_right (by norm_num) hgt).trans hle
      norm_num at h9
    ·
      have hab : IsElemAbelian 3 (zpowers (x : G)) := by
        refine ⟨inferInstance, fun y hy => ?_⟩
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx3,
          pow_orderOf_eq_one, one_zpow]
      exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 3)
        ((zpowers_le (G := G)).2 x.2) hab (by rw [Nat.card_zpowers, hx3, pow_one])
    ·
      apply le_antisymm
      · refine (closure_le _).2 ?_
        rintro y ⟨hyZ, m, hm, hym⟩
        have hy3 := hodd3 y hyZ m hm hym
        by_cases hy1 : y = 1
        · rw [hy1]
          exact one_mem _
        · exact subset_closure ⟨hZC hyZ, orderOf_eq_prime hy3 hy1⟩
      · refine (closure_le _).2 ?_
        rintro y ⟨hyC, hy3⟩
        exact subset_closure ⟨h3Z y hyC hy3, 3, by decide, by rw [← hy3, pow_orderOf_eq_one]⟩

end CFSG.Quasithin.H13.U3
