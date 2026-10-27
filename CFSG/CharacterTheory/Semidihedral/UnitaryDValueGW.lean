module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueGWQuotient
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueGWLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import CFSG.Assembly.Defs
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueStep

public section

open scoped Classical

namespace CFSG.Semidihedral.UnitaryDValue

namespace GW

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem oddCore_eq_pPrimeCore_two (K : Type*) [Group K] :
    CFSG.oddCore K = CFSG.pPrimeCore 2 K :=
  (CFSG.oddCore_eq_piCore K).trans (CFSG.pPrimeCore_eq_piCore K 2).symm

theorem oddCore_sup_sylow_eq_top {K : Type*} [Group K] [Finite K] (P : Sylow 2 K)
    (h : IsPGroup 2 (K ⧸ CFSG.pPrimeCore 2 K)) :
    CFSG.oddCore K ⊔ (P : Subgroup K) = ⊤ := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 2 K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have htop : (P : Subgroup K).map π = ⊤ :=
    ((P.mapSurjective hπs).is_maximal' (h.to_subgroup ⊤) le_top).symm
  have h1 := Subgroup.comap_map_eq π (P : Subgroup K)
  rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
  rw [oddCore_eq_pPrimeCore_two, sup_comm, ← h1]

theorem factorization_two_card_quotient {K : Type*} [Group K] [Finite K] :
    (Nat.card (K ⧸ CFSG.pPrimeCore 2 K)).factorization 2 = (Nat.card K).factorization 2 := by
  have hodd : Odd (Nat.card (CFSG.pPrimeCore 2 K)) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pPrimeCore 2 K),
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr h)), add_zero]

theorem three_le_factorization_of_eight_dvd {X : Type*} [Group X] [Finite X]
    (h : 8 ∣ Nat.card X) : 3 ≤ (Nat.card X).factorization 2 :=
  (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp (by norm_num; exact h)

theorem eight_dvd_card_alternatingGroup_seven : 8 ∣ Nat.card (alternatingGroup (Fin 7)) := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

end GW

namespace DValueData

open GW

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem gwStep_of_m_eq_two
    (hm : D.m = 2) : D.GWStep := by
  intro w hw hw1 _ htw
  have hwC : w ∈ D.C := D.W_le hw
  have hyp := sylowU_hyp D hw hw1 htw
  have hK2 := factorization_two_card_centralizer D hm hw hw1 htw
  have hOeq := oddCore_eq_pPrimeCore_two (Subgroup.centralizer ({w} : Set G))
  have hOC := oddCore_le_C D hw hw1 htw
  have hfirst : (CFSG.oddCore (Subgroup.centralizer ({w} : Set G)) ⊔
      (D.sylowU hwC hyp : Subgroup (Subgroup.centralizer ({w} : Set G)))).Normal →
      Subgroup.centralizer {w} ≤ Subgroup.normalizer (D.T : Set G) :=
    centralizer_le_normalizer_T_of_normal D hw hw1 htw
  have hDG := CFSG.GorensteinWalter.gorensteinWalter (Subgroup.centralizer ({w} : Set G))
    (hasDihedralSylowTwo D hm hw hw1 htw)
  let K := Subgroup.centralizer ({w} : Set G)
  let O' := CFSG.pPrimeCore 2 K
  let π := QuotientGroup.mk' O'
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hKbar2 : (Nat.card (K ⧸ O')).factorization 2 = 2 :=
    factorization_two_card_quotient.trans hK2
  have hO'odd : Odd (Nat.card O') := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hO'C : ∀ o ∈ O', (o : G) ∈ D.C := fun o ho => hOC o (hOeq ▸ ho)
  have hO'comm : ∀ u ∈ O', ∀ o ∈ O', u * o = o * u := fun u hu o ho =>
    Subtype.ext (D.C_comm _ (hO'C u hu) _ (hO'C o ho))
  let x' : K := ⟨D.x, x_mem_centralizer D hwC⟩
  let z' : K := ⟨D.z, z_mem_centralizer D hwC⟩
  let t' : K := ⟨D.t, Subgroup.mem_centralizer_singleton_iff.mpr htw⟩
  have hnotO : ∀ u : K, orderOf u = 2 → π u ≠ 1 := by
    intro u hu h
    have huO : u ∈ O' := (QuotientGroup.eq_one_iff u).mp h
    have h2 : orderOf (⟨u, huO⟩ : O') ∣ Nat.card O' := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hu] at h2
    exact (Nat.not_even_iff_odd.mpr hO'odd) (even_iff_two_dvd.mpr h2)
  have hxo : orderOf x' = 2 := by rw [Subgroup.orderOf_mk]; exact D.x_order
  have hzo : orderOf z' = 2 := by rw [Subgroup.orderOf_mk]; exact D.z_order
  have hxzo : orderOf (x' * z') = 2 := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact D.orderOf_xz
  have hxz' : x' * z' = z' * x' := Subtype.ext D.z_comm
  let a : K ⧸ O' := π x'
  let b : K ⧸ O' := π z'
  have ha : a * a = 1 := by
    show π x' * π x' = 1
    rw [← map_mul, show x' * x' = 1 from Subtype.ext D.x_mul_self, map_one]
  have hb : b * b = 1 := by
    show π z' * π z' = 1
    rw [← map_mul, show z' * z' = 1 from Subtype.ext D.z_mul_self, map_one]
  have hab : a * b = b * a := by
    show π x' * π z' = π z' * π x'
    rw [← map_mul, ← map_mul, hxz']
  have ha1 : a ≠ 1 := hnotO x' hxo
  have hb1 : b ≠ 1 := hnotO z' hzo
  have hne : a ≠ b := fun h => hnotO (x' * z') hxzo (by
    rw [map_mul]
    change a * b = 1
    rw [← h, ha])
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb) hb1
  have hVK : IsKleinFour (Subgroup.closure ({a, b} : Set (K ⧸ O'))) := by
    refine CFSG.Wreathed.isKleinFour_closure_pair hao hbo hab ?_
    rw [Subgroup.disjoint_def]
    intro g hg1 hg2
    rcases eq_one_or_eq_of_mem_zpowers hao hg1 with h | h
    · exact h
    · rcases eq_one_or_eq_of_mem_zpowers hbo hg2 with h' | h'
      · exact h'
      · exact absurd (h'.symm.trans h) (Ne.symm hne)
  have hVmem : ∀ v ∈ Subgroup.closure ({a, b} : Set (K ⧸ O')),
      v = 1 ∨ v = a ∨ v = b ∨ v = a * b := fun v hv => mem_closure_pair ha hb hab hv
  have hTimg : ∀ (v : G) (hv : v ∈ D.T), π ⟨v, T_le_centralizer D hwC hv⟩ = 1 ∨
      π ⟨v, T_le_centralizer D hwC hv⟩ = a ∨ π ⟨v, T_le_centralizer D hwC hv⟩ = b ∨
      π ⟨v, T_le_centralizer D hwC hv⟩ = a * b := by
    intro v hv
    rcases D.mem_T_iff.mp hv with rfl | rfl | rfl | rfl
    · left
      rw [show (⟨1, T_le_centralizer D hwC hv⟩ : K) = 1 from rfl, map_one]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [show (⟨D.x * D.z, T_le_centralizer D hwC hv⟩ : K) = x' * z' from rfl, map_mul]
  have hPmem : ∀ u : K, u ∈ (D.sylowU hwC hyp : Subgroup K) ↔ (u : G) ∈ D.T := by
    intro u
    change u ∈ D.U.subgroupOf K ↔ _
    rw [Subgroup.mem_subgroupOf, U_eq_T D hm]
  have hmapP : (D.sylowU hwC hyp : Subgroup K).map π =
      Subgroup.closure ({a, b} : Set (K ⧸ O')) := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      have huT := (hPmem u).mp hu
      have h := hTimg u huT
      rw [show (⟨(u : G), T_le_centralizer D hwC huT⟩ : K) = u from rfl] at h
      rcases h with h | h | h | h <;> rw [h]
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨x', (hPmem x').mpr D.x_mem_T, rfl⟩
      · exact ⟨z', (hPmem z').mpr D.z_mem_T, rfl⟩
  have hsup : CFSG.oddCore K ⊔ (D.sylowU hwC hyp : Subgroup K) =
      (Subgroup.closure ({a, b} : Set (K ⧸ O'))).comap π := by
    rw [← hmapP, Subgroup.comap_map_eq, QuotientGroup.ker_mk', hOeq, sup_comm]
  rcases hDG with ⟨_, h2⟩ | ⟨_, ⟨eA⟩⟩ | ⟨_, F, hF, L, hLn, hLi, hLm⟩
  ·
    left
    apply hfirst
    rw [oddCore_sup_sylow_eq_top (D.sylowU hwC hyp) h2]
    infer_instance
  ·
    exfalso
    have h3 := three_le_factorization_of_eight_dvd (X := K ⧸ O')
      (by rw [Nat.card_congr eA.toEquiv]; exact eight_dvd_card_alternatingGroup_seven)
    omega
  · have hqodd : Odd (Nat.card F) := by
      obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hF
      rw [hq]
      exact hpodd.pow
    have hVL : Subgroup.closure ({a, b} : Set (K ⧸ O')) ≤ L := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact mem_of_odd_index hLi (k := 1) (by rw [pow_one]; exact hao)
      · exact mem_of_odd_index hLi (k := 1) (by rw [pow_one]; exact hbo)
    rcases hLm with hLm | hLm
    · obtain ⟨eL⟩ := hLm
      by_cases hF3 : Nat.card F = 3
      ·
        left
        apply hfirst
        rw [hsup]
        exact (normal_of_psl2_three hF3 eL hVL hVK.card_four).comap π
      ·
        right
        intro c hcC hc3
        have hF5 := five_le_of_isOddPrimePower hF hF3
        have : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F) :=
          Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
        have hLs : IsSimpleGroup L := (MulEquiv.isSimpleGroup_congr eL).mpr inferInstance
        obtain ⟨ℓ, hℓL, hℓa, hℓb⟩ :=
          exists_mem_cycle_of_psl2 hF hF3 hLi eL hKbar2 ha hb hab ha1 hb1 hne hVK hVL
        obtain ⟨m, hmℓ⟩ := hπs ℓ
        have hta : π t' * a * (π t')⁻¹ = b := by
          show π t' * π x' * (π t')⁻¹ = π z'
          rw [← map_inv, ← map_mul, ← map_mul, show t' * x' * t'⁻¹ = z' from Subtype.ext D.t_x]
        have htb : π t' * b * (π t')⁻¹ = a * b := by
          show π t' * π z' * (π t')⁻¹ = π x' * π z'
          rw [← map_inv, ← map_mul, ← map_mul, ← map_mul,
            show t' * z' * t'⁻¹ = x' * z' from Subtype.ext D.t_z]
        let k := m⁻¹ * t'
        have hπk : π k = ℓ⁻¹ * π t' := by
          show π (m⁻¹ * t') = _
          rw [map_mul, map_inv, hmℓ]
        have hka : π k * a = a * π k := by
          rw [hπk]
          calc ℓ⁻¹ * π t' * a = ℓ⁻¹ * (π t' * a * (π t')⁻¹) * π t' := by group
            _ = ℓ⁻¹ * (ℓ * a * ℓ⁻¹) * π t' := by rw [hta, hℓa]
            _ = a * (ℓ⁻¹ * π t') := by group
        have hkb : π k * b = b * π k := by
          rw [hπk]
          calc ℓ⁻¹ * π t' * b = ℓ⁻¹ * (π t' * b * (π t')⁻¹) * π t' := by group
            _ = ℓ⁻¹ * (ℓ * b * ℓ⁻¹) * π t' := by rw [htb, hℓb]
            _ = b * (ℓ⁻¹ * π t') := by group
        have hk : ∀ (v : G) (hv : v ∈ D.T), π ⟨v, T_le_centralizer D hwC hv⟩ * π k =
            π k * π ⟨v, T_le_centralizer D hwC hv⟩ := by
          intro v hv
          rcases hTimg v hv with h | h | h | h <;> rw [h]
          · rw [one_mul, mul_one]
          · exact hka.symm
          · exact hkb.symm
          · rw [mul_assoc, ← hkb, ← mul_assoc, ← hka, mul_assoc]
        obtain ⟨c₀, hc₀C, hc₀k⟩ :=
          exists_mem_C_of_quotient_commute D hw hw1 htw O' hOeq k hk
        let M := Subgroup.centralizer (O' : Set K)
        have hMn : M.Normal := inferInstance
        have hxM : x' ∈ M := Subgroup.mem_centralizer_iff.mpr fun o ho =>
          Subtype.ext (D.C_comm _ (hO'C o ho) _ D.x_mem_C)
        have haM : a ∈ M.map π := ⟨x', hxM, rfl⟩
        have hLM : L ≤ M.map π := by
          have := hLs
          have hn : ((M.map π).subgroupOf L).Normal :=
            @Subgroup.normal_subgroupOf _ _ L (M.map π) (hMn.map π hπs)
          rcases hn.eq_bot_or_eq_top with h | h
          · exfalso
            have haL : a ∈ L := hVL (Subgroup.subset_closure (Set.mem_insert _ _))
            have : (⟨a, haL⟩ : L) ∈ (M.map π).subgroupOf L := haM
            rw [h, Subgroup.mem_bot] at this
            exact ha1 (congrArg Subtype.val this)
          · exact Subgroup.subgroupOf_eq_top.mp h
        obtain ⟨m₁, hm₁M, hm₁ℓ⟩ := hLM hℓL
        have ho₁ : m₁⁻¹ * m ∈ O' := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
          change (π m₁)⁻¹ * π m = 1
          rw [hm₁ℓ, hmℓ, inv_mul_cancel]
        have hdecomp : t' = m₁ * (m₁⁻¹ * m) * c₀ * (c₀⁻¹ * k) := by
          show t' = m₁ * (m₁⁻¹ * m) * c₀ * (c₀⁻¹ * (m⁻¹ * t'))
          group
        have htO : ∀ o ∈ O', t' * o = o * t' := by
          intro o ho
          have c1 : Commute m₁ o := (Subgroup.mem_centralizer_iff.mp hm₁M o ho).symm
          have c2 : Commute (m₁⁻¹ * m) o := hO'comm _ ho₁ _ ho
          have c3 : Commute c₀ o := Subtype.ext (D.C_comm _ hc₀C _ (hO'C o ho))
          have c4 : Commute (c₀⁻¹ * k) o := hO'comm _ hc₀k _ ho
          rw [hdecomp]
          exact (((c1.mul_left c2).mul_left c3).mul_left c4).eq
        have hcK : c ∈ K := Subgroup.mem_centralizer_singleton_iff.mpr (D.C_comm c hcC w hwC)
        have heC : D.t * c * D.t⁻¹ * c⁻¹ ∈ D.C :=
          D.C.mul_mem (D.conj_mem_C D.t_mem_normalizer_T hcC) (D.C.inv_mem hcC)
        have heK : D.t * c * D.t⁻¹ * c⁻¹ ∈ K :=
          Subgroup.mem_centralizer_singleton_iff.mpr (D.C_comm _ heC w hwC)
        let c' : K := ⟨c, hcK⟩
        let e' : K := ⟨D.t * c * D.t⁻¹ * c⁻¹, heK⟩
        have he' : e' = t' * c' * t'⁻¹ * c'⁻¹ := rfl
        have hπc₀ : π c₀ = π k := QuotientGroup.eq.mpr hc₀k
        have hπt : π t' = ℓ * π c₀ := by
          rw [hπc₀, hπk, mul_inv_cancel_left]
        have hcc : π c₀ * π c' = π c' * π c₀ := by
          rw [← map_mul, ← map_mul, show c₀ * c' = c' * c₀ from Subtype.ext (D.C_comm _ hc₀C _ hcC)]
        have hπe : π e' = ℓ * (π c' * ℓ⁻¹ * (π c')⁻¹) := by
          rw [he', map_mul, map_mul, map_mul, map_inv, map_inv, hπt]
          calc ℓ * π c₀ * π c' * (ℓ * π c₀)⁻¹ * (π c')⁻¹ =
              ℓ * (π c₀ * π c') * (π c₀)⁻¹ * ℓ⁻¹ * (π c')⁻¹ := by group
            _ = ℓ * (π c' * π c₀) * (π c₀)⁻¹ * ℓ⁻¹ * (π c')⁻¹ := by rw [hcc]
            _ = ℓ * (π c' * ℓ⁻¹ * (π c')⁻¹) := by group
        have heL : π e' ∈ L := by
          rw [hπe]
          exact L.mul_mem hℓL (hLn.conj_mem _ (L.inv_mem hℓL) _)
        have hex : e' * x' = x' * e' := Subtype.ext ((D.mem_C_iff.mp heC).1)
        have hez : e' * z' = z' * e' := Subtype.ext ((D.mem_C_iff.mp heC).2)
        have hea : π e' * a = a * π e' := by
          show π e' * π x' = π x' * π e'
          rw [← map_mul, ← map_mul, hex]
        have heb : π e' * b = b * π e' := by
          show π e' * π z' = π z' * π e'
          rw [← map_mul, ← map_mul, hez]
        have heV : ∀ v ∈ Subgroup.closure ({a, b} : Set (K ⧸ O')), π e' * v = v * π e' := by
          intro v hv
          rcases hVmem v hv with h | h | h | h <;> rw [h]
          · rw [one_mul, mul_one]
          · exact hea
          · exact heb
          · rw [← mul_assoc, hea, mul_assoc, heb, mul_assoc]
        have heodd : Odd (orderOf (π e')) := by
          obtain ⟨j, hj⟩ := hc3
          have h1 : orderOf (D.t * c * D.t⁻¹) = 3 ^ j := by rw [orderOf_conj_eq, hj]
          have h2 : orderOf c⁻¹ = 3 ^ j := by rw [orderOf_inv, hj]
          have hcomm : Commute (D.t * c * D.t⁻¹) c⁻¹ :=
            D.C_comm _ (D.conj_mem_C D.t_mem_normalizer_T hcC) _ (D.C.inv_mem hcC)
          have h3 : orderOf (D.t * c * D.t⁻¹ * c⁻¹) ∣ 3 ^ j := by
            have := hcomm.orderOf_mul_dvd_lcm
            rw [h1, h2, Nat.lcm_self] at this
            exact this
          have h4 : orderOf (π e') ∣ 3 ^ j := by
            refine (orderOf_map_dvd π e').trans ?_
            rw [Subgroup.orderOf_mk]
            exact h3
          exact (Odd.pow (by decide : Odd 3)).of_dvd_nat h4
        have he1 : π e' = 1 := eq_one_of_commute_of_psl2 hF eL hVK hVL heL heV heodd
        have heO : e' ∈ O' := (QuotientGroup.eq_one_iff e').mp he1
        exact congrArg Subtype.val (htO e' heO)
    ·
      obtain ⟨eL⟩ := hLm
      exfalso
      have h8 : 8 ∣ Nat.card (CFSG.GorensteinWalter.PGL2 F) := by
        rw [CFSG.GorensteinWalter.pgl2_card_formula F]
        exact dvd_mul_of_dvd_right (Nat.eight_dvd_sq_sub_one_of_odd hqodd) _
      have h8' : 8 ∣ Nat.card (K ⧸ O') := by
        rw [← Nat.card_congr eL.toEquiv] at h8
        exact h8.trans (Subgroup.card_subgroup_dvd_card L)
      have h3 := three_le_factorization_of_eight_dvd h8'
      omega

end DValueData

end CFSG.Semidihedral.UnitaryDValue
