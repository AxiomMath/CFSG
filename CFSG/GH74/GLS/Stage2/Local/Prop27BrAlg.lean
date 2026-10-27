module

public import CFSG.GH74.GLS.Stage2.Local.P34S5Jbar
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.GH74.GLS.Stage2.Local.P34Embed
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27Br

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Local.P34
open scoped commutatorElement

section Prod

variable {G : Type} [Group G] {A B : Subgroup G}

@[expose] noncomputable def mulMap (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : ↥A × ↥B →* G :=
  MonoidHom.noncommCoprod A.subtype B.subtype (fun a b => hAB a.1 a.2 b.1 b.2)

theorem mulMap_apply (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (a : ↥A) (b : ↥B) :
    mulMap hAB (a, b) = (a : G) * (b : G) := rfl

theorem sup_le_range_mulMap (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ⊔ B ≤ (mulMap hAB).range := by
  refine sup_le (fun a ha => ⟨(⟨a, ha⟩, 1), ?_⟩) (fun b hb => ⟨(1, ⟨b, hb⟩), ?_⟩)
  · simp [mulMap_apply]
  · simp [mulMap_apply]

theorem exists_mul_of_comm (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  obtain ⟨⟨a, b⟩, h⟩ := sup_le_range_mulMap hAB hg
  exact ⟨a, a.2, b, b.2, by rw [← h, mulMap_apply]⟩

theorem commutator_sup_le (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) : ⁅A ⊔ B, A ⊔ B⁆ ≤ B := by
  rw [Subgroup.commutator_le]
  intro g hg g' hg'
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_comm hAB hg
  obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_comm hAB hg'
  have h1 : ⁅((⟨a, ha⟩ : ↥A), (⟨b, hb⟩ : ↥B)), ((⟨a', ha'⟩ : ↥A), (⟨b', hb'⟩ : ↥B))⁆ =
      (1, ⁅(⟨b, hb⟩ : ↥B), (⟨b', hb'⟩ : ↥B)⁆) := by
    refine Prod.ext ?_ rfl
    refine Subtype.ext ?_
    show a * a' * a⁻¹ * a'⁻¹ = 1
    rw [hA a ha a' ha']
    group
  have h2 := map_commutatorElement (mulMap hAB) ((⟨a, ha⟩ : ↥A), (⟨b, hb⟩ : ↥B))
    ((⟨a', ha'⟩ : ↥A), (⟨b', hb'⟩ : ↥B))
  rw [h1] at h2
  have h3 : mulMap hAB (1, ⁅(⟨b, hb⟩ : ↥B), (⟨b', hb'⟩ : ↥B)⁆) = ⁅b, b'⁆ := by
    simp [mulMap_apply, commutatorElement_def]
  rw [h3] at h2
  simp only [mulMap_apply] at h2
  rw [← h2, commutatorElement_def]
  exact B.mul_mem (B.mul_mem (B.mul_mem hb hb') (B.inv_mem hb)) (B.inv_mem hb')

theorem exists_injective_hom_of_le_sup (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hint : A ⊓ B = ⊥)
    {W : Subgroup G} (hW : W ≤ A ⊔ B) (hWA : W ⊓ A = ⊥) :
    ∃ φ : ↥W →* ↥B, Function.Injective φ := by
  have hμ : Function.Injective (mulMap hAB) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    rw [mulMap_apply] at h
    have hb : (b : G) = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right h
    have hmem : (b : G) ∈ A ⊓ B := ⟨by rw [hb]; exact A.inv_mem a.2, b.2⟩
    rw [hint, Subgroup.mem_bot] at hmem
    have ha : (a : G) = 1 := by
      have : (a : G)⁻¹ = 1 := by rw [← hb]; exact hmem
      simpa using this
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hmem)
  let e : (↥A × ↥B) ≃* (mulMap hAB).range := MonoidHom.ofInjective hμ
  have hWr : W ≤ (mulMap hAB).range := hW.trans (sup_le_range_mulMap hAB)
  let φ : ↥W →* ↥B := (MonoidHom.snd ↥A ↥B).comp (e.symm.toMonoidHom.comp (Subgroup.inclusion hWr))
  refine ⟨φ, ?_⟩
  rw [injective_iff_map_eq_one]
  intro w hw
  obtain ⟨⟨a, b⟩, hyab⟩ : ∃ y : ↥A × ↥B, y = e.symm (Subgroup.inclusion hWr w) := ⟨_, rfl⟩
  have hb : b = 1 := by
    have : φ w = b := by
      show (e.symm (Subgroup.inclusion hWr w)).2 = b
      rw [← hyab]
    rw [← this]
    exact hw
  have h2 : e (a, b) = Subgroup.inclusion hWr w := by
    rw [hyab]
    exact e.apply_symm_apply _
  have h3 : (w : G) = (a : G) * (b : G) := by
    have h5 : ((Subgroup.inclusion hWr w : (mulMap hAB).range) : G) = (w : G) := rfl
    rw [← h5, ← h2]
    rfl
  rw [hb] at h3
  have hmem : (w : G) ∈ W ⊓ A := ⟨w.2, by rw [h3]; simp⟩
  rw [hWA, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

end Prod

section Cyclic

variable {G : Type} [Group G]

theorem mem_zpowers_of_cyclic_involution {T₁ : Subgroup G} [Finite ↥T₁] (hcyc : IsCyclic ↥T₁)
    (h2 : IsPGroup 2 ↥T₁) {x g : G} (hx : x ∈ T₁) (hx2 : orderOf x = 2) (hg : g ∈ T₁)
    (hg1 : g ≠ 1) : x ∈ Subgroup.zpowers g := by
  classical
  let g' : ↥T₁ := ⟨g, hg⟩
  have hg'1 : g' ≠ 1 := fun h => hg1 (congrArg Subtype.val h)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h2) g'
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      rw [h0, pow_zero, orderOf_eq_one_iff] at hk
      exact hg'1 hk
    · exact h0
  have hdvd : 2 ∣ orderOf g' := by
    rw [hk]
    exact dvd_pow_self 2 (by omega)
  have hhord : orderOf (g' ^ (orderOf g' / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos g').ne' hdvd
  set h : ↥T₁ := g' ^ (orderOf g' / 2) with hh
  have hxo : orderOf (⟨x, hx⟩ : ↥T₁) = 2 := by
    rw [← hx2]
    exact (Subgroup.orderOf_coe _).symm
  have hsq : ∀ a : ↥T₁, orderOf a = 2 → a ^ 2 = 1 := fun a ha => by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have heq : (⟨x, hx⟩ : ↥T₁) = h := by
    by_contra hne
    have : Fintype ↥T₁ := Fintype.ofFinite _
    have hcard := IsCyclic.card_pow_eq_one_le (α := ↥T₁) (n := 2) (by norm_num)
    have h1x : (1 : ↥T₁) ≠ ⟨x, hx⟩ := by
      intro h
      have := hxo
      rw [← h, orderOf_one] at this
      omega
    have h1h : (1 : ↥T₁) ≠ h := by
      intro h'
      have := hhord
      rw [← h', orderOf_one] at this
      omega
    have hsub : ({1, ⟨x, hx⟩, h} : Finset ↥T₁) ⊆ Finset.univ.filter (fun a : ↥T₁ => a ^ 2 = 1) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases ha with rfl | rfl | rfl
      · simp
      · exact hsq _ hxo
      · exact hsq _ hhord
    have h3 : ({1, ⟨x, hx⟩, h} : Finset ↥T₁).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1x, h1h⟩
    have := Finset.card_le_card hsub
    omega
  have hxh : x = ((g' ^ (orderOf g' / 2) : ↥T₁) : G) := congrArg Subtype.val heq
  have hxg : x = g ^ (orderOf g' / 2) := by
    rw [hxh]
    rfl
  rw [hxg]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _

end Cyclic

section Sylow

theorem not_isCyclic_sylow_of_perfect {Y : Type*} [Group Y] [Finite Y] (hY : Group.IsPerfect Y)
    (P : Sylow 2 Y) (hcyc : IsCyclic ↥P) {t : Y} (ht : t ∈ (P : Subgroup Y)) (ht1 : t ≠ 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 P.isPGroup') ⟨t, ht⟩
  have hk' : orderOf t = 2 ^ k := (Subgroup.orderOf_coe (⟨t, ht⟩ : ↥(P : Subgroup Y))).trans hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      rw [h0, pow_zero, orderOf_eq_one_iff] at hk'
      exact ht1 hk'
    · exact h0
  have h2 : 2 ∣ Nat.card Y := by
    have : orderOf t ∣ Nat.card Y := orderOf_dvd_natCard t
    rw [hk'] at this
    exact (dvd_pow_self 2 (by omega)).trans this
  have hmin : (Nat.card Y).minFac = 2 := (Nat.minFac_eq_two_iff _).2 h2
  have hNC : normalizer (P : Set Y) ≤ centralizer (P : Set Y) := hcyc.normalizer_le_centralizer hmin
  have h1 := MonoidHom.transferSylow_eq_pow P hNC t ht
  have hcomm : ∀ a b : ↥P, a * b = b * a := fun a b => by
    have : IsMulCommutative ↥P := inferInstance
    exact (IsMulCommutative.is_comm : Std.Commutative (· * · : ↥P → ↥P → ↥P)).comm a b
  have h3 : MonoidHom.transferSylow P hNC t = 1 := by
    have hker : (⊤ : Subgroup Y) ≤ (MonoidHom.transferSylow P hNC).ker := by
      rw [← hY.commutator_eq_top, _root_.commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    exact (MonoidHom.mem_ker).1 (hker (Subgroup.mem_top t))
  rw [h1] at h3
  have h4 : t ^ (P : Subgroup Y).index = 1 := congrArg Subtype.val h3
  have hnodd : ¬ 2 ∣ (P : Subgroup Y).index := P.not_dvd_index
  have h5 : orderOf t ∣ (P : Subgroup Y).index := orderOf_dvd_of_pow_eq_one h4
  rw [hk'] at h5
  exact hnodd ((dvd_pow_self 2 (by omega)).trans h5)

theorem odd_orderOf_of_mem_pPrimeCore'' {H : Type} [Group H] [Finite H] {o : H}
    (ho : o ∈ pPrimeCore 2 H) : Odd (orderOf o) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf o ∣ Nat.card (pPrimeCore 2 H) := by
    rw [← Subgroup.orderOf_mk o ho]
    exact orderOf_dvd_natCard _
  exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h1

theorem nontrivial_quot_of_involution {Y : Type} [Group Y] [Finite Y] {t : Y} (ht : orderOf t = 2) :
    Nontrivial (Y ⧸ pPrimeCore 2 Y) := by
  refine ⟨⟨(t : Y ⧸ pPrimeCore 2 Y), 1, fun h => ?_⟩⟩
  have hmem : t ∈ pPrimeCore 2 Y := (QuotientGroup.eq_one_iff t).1 h
  have := odd_orderOf_of_mem_pPrimeCore'' hmem
  rw [ht] at this
  exact (by decide : ¬ Odd 2) this

theorem not_isPerfect_pgl2 (K : Type) [Field K] [Finite K]
    (hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K)) :
    ¬ Group.IsPerfect (CFSG.GorensteinWalter.PGL2 K) := by
  intro hperf
  have hle := CFSG.GorensteinWalter.pgl2_commutator_le_psl2_range K
  have hidx := CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two K hK
  have hc : commutator (CFSG.GorensteinWalter.PGL2 K) = ⊤ := hperf.commutator_eq_top
  rw [hc, top_le_iff] at hle
  rw [hle, Subgroup.index_top] at hidx
  omega

theorem hasDihedralSylowTwo_of_embedding {Y : Type} [Group Y] [Finite Y] (P : Sylow 2 Y) {m : ℕ}
    (hm : 1 ≤ m) (ψ : ↥(P : Subgroup Y) →* DihedralGroup (2 ^ m)) (hψ : Function.Injective ψ)
    (hnc : ¬ IsCyclic ↥(P : Subgroup Y)) : CFSG.GorensteinWalter.HasDihedralSylowTwo Y := by
  let e : ↥(P : Subgroup Y) ≃* ψ.range := MonoidHom.ofInjective hψ
  have hP : ∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥(P : Subgroup Y) ≃* DihedralGroup (2 ^ k)) := by
    rcases CFSG.GorensteinWalter.subgroups_dihedral_twoGroup_cyclic_or_dihedral hm ψ.range with
      hc | ⟨k, hk, ⟨e'⟩⟩
    · exact absurd ((MulEquiv.isCyclic e).2 hc) hnc
    · exact ⟨k, hk, ⟨e.trans e'⟩⟩
  intro S
  obtain ⟨k, hk, ⟨eP⟩⟩ := hP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P S
  refine ⟨k, hk, ⟨?_⟩⟩
  have hS : (S : Subgroup Y) = (P : Subgroup Y).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  exact ((MulEquiv.subgroupCongr hS).trans
    (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm).trans eP

end Sylow

section GW

open CFSG.GorensteinWalter (HasDihedralSylowTwo IsDGroup PSL2 PGL2 IsOddPrimePower)

theorem dihJ_of_perfect_dihedral
    {Y : Type} [Group Y] [Finite Y] (hY : Group.IsPerfect Y) {t : Y} (ht : orderOf t = 2)
    (hdih : HasDihedralSylowTwo Y) :
    (∃ r : ℕ, Odd r ∧ 3 < r ∧ IVK.IsL2 (Y ⧸ pPrimeCore 2 Y) (fun s => s = r)) ∨
      Nonempty ((Y ⧸ pPrimeCore 2 Y) ≃* alternatingGroup (Fin 7)) := by
  have hD : IsDGroup Y := CFSG.GorensteinWalter.gorensteinWalter Y hdih
  have hperf : Group.IsPerfect (Y ⧸ pPrimeCore 2 Y) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pPrimeCore 2 Y)) (QuotientGroup.mk'_surjective _)
  have hnt : Nontrivial (Y ⧸ pPrimeCore 2 Y) := nontrivial_quot_of_involution ht
  rcases hD with ⟨-, hTwo⟩ | ⟨-, ⟨h7⟩⟩ | ⟨-, K, hK, L, hLn, hLodd, hLmodel⟩
  · exfalso
    have hsolv : Group.IsSolvable (Y ⧸ pPrimeCore 2 Y) := by
      have := hTwo.isNilpotent
      infer_instance
    exact Group.IsPerfect.not_isSolvable _ hsolv
  · exact Or.inr ⟨h7⟩
  · left
    have hQfin : Finite (Y ⧸ pPrimeCore 2 Y) := inferInstance
    have hLtop : L = ⊤ := by
      by_contra hne
      have hodd : Odd (Nat.card ((Y ⧸ pPrimeCore 2 Y) ⧸ L)) := by
        rw [← Subgroup.index_eq_card]
        exact hLodd
      have hqsolv : Group.IsSolvable ((Y ⧸ pPrimeCore 2 Y) ⧸ L) :=
        CFSG.Milestones.odd_order_solvable hodd
      have hqperf : Group.IsPerfect ((Y ⧸ pPrimeCore 2 Y) ⧸ L) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' L) (QuotientGroup.mk'_surjective _)
      have hidx : L.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
      have hnt' : Nontrivial ((Y ⧸ pPrimeCore 2 Y) ⧸ L) := by
        rw [← Finite.one_lt_card_iff_nontrivial, ← Subgroup.index_eq_card]
        have : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
        omega
      exact Group.IsPerfect.not_isSolvable _ hqsolv
    let eQ : ↥L ≃* (Y ⧸ pPrimeCore 2 Y) := (MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv
    rcases hLmodel with hPSL | hPGL
    · obtain ⟨ePSL⟩ := hPSL
      let e : (Y ⧸ pPrimeCore 2 Y) ≃* PSL2 K := eQ.symm.trans ePSL
      have hodd : Odd (Nat.card K) := by
        obtain ⟨p, n, -, hp, -, hc⟩ := hK
        rw [hc]
        exact hp.pow
      refine ⟨Nat.card K, hodd, ?_, K, inferInstance, inferInstance, rfl,
        ⟨e.trans (IVK.L2.equivPSL K).symm⟩⟩
      by_contra hle
      have hsolvP : Group.IsSolvable (PSL2 K) := psl2_solvable_of_card_le_three (by omega)
      have hsolvQ : Group.IsSolvable (Y ⧸ pPrimeCore 2 Y) :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      exact Group.IsPerfect.not_isSolvable _ hsolvQ
    · exfalso
      obtain ⟨ePGL⟩ := hPGL
      have hperfP : Group.IsPerfect (PGL2 K) :=
        Group.IsPerfect.ofSurjective (f := (eQ.symm.trans ePGL).toMonoidHom) (eQ.symm.trans ePGL).surjective
      exact not_isPerfect_pgl2 K hK hperfP

end GW

end CFSG.GH74.GLS.Stage2.Local.P27Br
