module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneB
public import CFSG.Sporadic.Co1.Module.TwoB
public import Certificates.Certificate24513

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1.HypOne

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1Block CFSG.Monster.GMS
open CFSG.Sporadic.Co1.Module.TwoB (sBc)

theorem exists_conj_mem_of_card_pow_two {M : Type*} [Group M] [Finite M] {R S : Subgroup M}
    (hSR : S ≤ R) (hS : Nat.card S = 2 ^ (Nat.card R).factorization 2) {t : M} (ht : t ∈ R)
    {n : ℕ} (htn : t ^ (2 ^ n) = 1) : ∃ x ∈ R, x⁻¹ * t * x ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 R := Sylow.ofCard (S.subgroupOf R) (by
    rw [← hS]
    exact Nat.card_congr (subgroupOfEquivOfLe hSR).toEquiv)
  have htR2 : IsPGroup 2 (zpowers (⟨t, ht⟩ : R)) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show orderOf t ∣ 2 ^ n from orderOf_dvd_of_pow_eq_one htn)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hm])
  obtain ⟨T, hT⟩ := htR2.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq R S' T
  refine ⟨x, x.2, ?_⟩
  have htT : (⟨t, ht⟩ : R) ∈ (T : Subgroup R) := hT (mem_zpowers _)
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htT
  obtain ⟨s, hs, hst⟩ := htT
  have hsS : (s : M) ∈ S := by
    have : s ∈ S.subgroupOf R := by
      rwa [show ((S' : Subgroup R)) = S.subgroupOf R from Sylow.coe_ofCard _ _] at hs
    exact mem_subgroupOf.mp this
  have e : x⁻¹ * ⟨t, ht⟩ * x = s := by
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
  rw [e']
  exact hsS

theorem no_fourth_root_of_trees {K : Subgroup GL24} {sg : Array Native.Rows} {T : GTree}
    {sgG : ℕ → GL24} {tR : Native.Rows} {t : GL24} (ht : MRep tR t) (htv : validRows tR = true)
    (hcomm : ∀ k ∈ K, k * t = t * k)
    (hsgrep : ∀ l < sg.size, valHom (sgG l) = rowsMatrix 24 sg[l]!) (hsgK : ∀ l, sgG l ∈ K)
    (hT : gtOK sg T = true) (hord : T.pts.size = 2 ^ (Nat.card K).factorization 2)
    (hall : ∀ i < T.pts.size, (Native.mul (Native.mul T.pts[i]! T.pts[i]!)
      (Native.mul T.pts[i]! T.pts[i]!) != tR) = true) :
    ∀ z ∈ K, z ^ 8 = 1 → z ^ 4 ≠ t := by
  obtain ⟨f, hf, -, hcl⟩ := prodTree_closure_eq valHom valHom_injective hT sgG hsgrep
  have hScard := prodTree_card valHom valHom_injective hT sgG hsgrep
  have hSK : Subgroup.closure (sgG '' {l | l < sg.size}) ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, -, rfl⟩
    exact hsgK l
  have hSord : Nat.card (Subgroup.closure (sgG '' {l | l < sg.size})) =
      2 ^ (Nat.card K).factorization 2 := by rw [hScard, hord]
  have hvalid := validRows_of_gtOK hT
  intro z hz hz8 hz4
  obtain ⟨k, hkK, hkS⟩ := exists_conj_mem_of_card_pow_two (n := 3) hSK hSord hz (by
    simpa using hz8)
  have hkt : k⁻¹ * t * k = t := by
    have := hcomm k hkK
    calc k⁻¹ * t * k = k⁻¹ * (t * k) := by rw [mul_assoc]
      _ = k⁻¹ * (k * t) := by rw [this]
      _ = t := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hcS' : k⁻¹ * z * k ∈ (Subgroup.closure (sgG '' {l | l < sg.size}) : Set GL24) := hkS
  rw [hcl] at hcS'
  obtain ⟨i, hi, hsi⟩ := hcS'
  have hi' : i < T.pts.size := hi
  have hp : MRep T.pts[i]! (k⁻¹ * z * k) := by
    unfold MRep
    rw [← hsi]
    exact (hf i hi').symm
  have hss : MRep (Native.mul T.pts[i]! T.pts[i]!) ((k⁻¹ * z * k) * (k⁻¹ * z * k)) := hp.mul hp
  have hz4' : z * z * (z * z) = t := by
    have : z ^ 4 = z * z * (z * z) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    rw [← this]
    exact hz4
  have hss4 : MRep (Native.mul (Native.mul T.pts[i]! T.pts[i]!)
      (Native.mul T.pts[i]! T.pts[i]!)) t := by
    have e4 : (k⁻¹ * z * k) * (k⁻¹ * z * k) * ((k⁻¹ * z * k) * (k⁻¹ * z * k)) = t := by
      calc _ = k⁻¹ * (z * z * (z * z)) * k := by group
        _ = k⁻¹ * t * k := by rw [hz4']
        _ = t := hkt
    exact e4 ▸ hss.mul hss
  have hv2 := CFSG.Sporadic.Co1.Module.TwoB.validRows_mulRows (hvalid i hi') (hvalid i hi')
  have hv4 := CFSG.Sporadic.Co1.Module.TwoB.validRows_mulRows hv2 hv2
  have hrows : Native.mul (Native.mul T.pts[i]! T.pts[i]!) (Native.mul T.pts[i]! T.pts[i]!) =
      tR :=
    CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid hv4 htv (hss4.trans ht.symm)
  have := hall i hi'
  rw [hrows] at this
  simp at this

theorem no_fourth_root_of_check
    {tR : Native.Rows} {t : GL24} (ht : MRep tR t) (htG : t ∈ GA)
    {d₁ : List (List ℤ)} {bidx : List ℕ} {d₂ : List (List ℤ)} {sIdx : List ℕ} {ord : ℕ}
    {K : Subgroup GL24} (hK : K = GA ⊓ Subgroup.centralizer {t})
    (hord : ord = 2 ^ (Nat.card K).factorization 2)
    (h : fourthRootCheckOf tR d₁ bidx d₂ sIdx ord = true) : ∀ z ∈ K, z ^ 8 = 1 → z ^ 4 ≠ t := by
  simp only [fourthRootCheckOf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hD1, hD2⟩, hBall⟩, hT⟩, hsize⟩, htv⟩, hall⟩ := h
  have hrepB := rep_brayElts (bidx := bidx) ht hD1
  have hBGK : ∀ g ∈ brayEltsG t d₁ bidx, g ∈ K := by
    intro g hg
    rw [hK]
    refine Subgroup.mem_inf.2 ⟨brayElts_mem_GA htG g hg, ?_⟩
    obtain ⟨r, hr, hrg⟩ := forall₂_mem_left hrepB hg
    have e := (hBall r hr).1
    have h1 : MRep (Native.mul r tR) (g * t) := hrg.mul ht
    have h2 : MRep (Native.mul tR r) (t * g) := ht.mul hrg
    rw [e] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h2.eq h1).symm
  have hrepD2 := dag_rep hrepB d₂ hD2
  have hD2K : ∀ g ∈ dagG (brayEltsG t d₁ bidx) d₂, g ∈ K := dagG_mem hBGK d₂
  refine no_fourth_root_of_trees ht htv ?_
    (sgG := fun l => (dagG (brayEltsG t d₁ bidx) d₂).getD (sIdx.getD l 0) 1) ?_
    (fun l => getD_mem_of_forall hD2K _) hT (hsize.trans hord) ?_
  · intro k hk
    rw [hK] at hk
    have h2 : k ∈ Subgroup.centralizer ({t} : Set GL24) := (Subgroup.mem_inf.1 hk).2
    have h3 := Subgroup.mem_centralizer_singleton_iff.1 h2
    exact h3
  · intro l hl
    have hl' : l < sIdx.length := by simpa using hl
    rw [getElem!_toArray_map _ _ hl', List.getD_eq_getElem _ _ hl']
    exact (getD_rep hrepD2 MRep.one sIdx[l]).symm
  · intro i hi
    rw [getElem!_pos _ i hi]
    exact hall i hi

theorem no_fourth_root_a₁
    {z : GL24} (hz : z ∈ GA) (hz8 : z ^ 8 = 1)
    (hz4 : z ^ 4 = A₁) : False := by
  have hcomm : z * A₁ = A₁ * z := by
    rw [← hz4]
    group
  have hzK : z ∈ GA ⊓ Subgroup.centralizer ({A₁} : Set GL24) := by
    refine Subgroup.mem_inf.2 ⟨hz, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  exact no_fourth_root_of_check rep_A₁ A₁_mem rfl two_part_cent_B
    Certificates.certificate24513 _ hzK hz8 hz4

theorem exists_fourth_root_of_conj {G H : Type*} [Group G] [Group H] (φ : G → H)
    (hmul : ∀ a b, φ (a * b) = φ a * φ b) (U : Subgroup H) (hφ : ∀ x, φ x ∈ U)
    (y g s : G) (a c : H) (hc : c ∈ U) (hg : g * y ^ 4 * g⁻¹ = s) (hca : c * a * c⁻¹ = φ s)
    (h8 : y ^ 8 = 1) : ∃ z ∈ U, z ^ 8 = 1 ∧ z ^ 4 = a := by
  let ψ : G →* H := MonoidHom.mk' φ hmul
  refine ⟨(c⁻¹ * ψ g) * ψ y * (c⁻¹ * ψ g)⁻¹, ?_, ?_, ?_⟩
  · exact U.mul_mem (U.mul_mem (U.mul_mem (U.inv_mem hc) (hφ g)) (hφ y))
      (U.inv_mem (U.mul_mem (U.inv_mem hc) (hφ g)))
  · rw [conj_pow, ← map_pow, h8, map_one, mul_one, mul_inv_cancel]
  · rw [conj_pow, ← map_pow]
    have h4 : ψ g * ψ (y ^ 4) * (ψ g)⁻¹ = c * a * c⁻¹ := by
      have : ψ (g * y ^ 4 * g⁻¹) = ψ g * ψ (y ^ 4) * (ψ g)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [← this, hg, hca]
      rfl
    calc c⁻¹ * ψ g * ψ (y ^ 4) * (c⁻¹ * ψ g)⁻¹
        = c⁻¹ * (ψ g * ψ (y ^ 4) * (ψ g)⁻¹) * c := by group
      _ = c⁻¹ * (c * a * c⁻¹) * c := by rw [h4]
      _ = a := by group

theorem no_twoB_fourth_power
    (y : NativeSporadic.Co1) : ¬ IsCo1TwoB (y ^ 4) := by
  intro hy
  obtain ⟨g, hg⟩ := isConj_iff.1 (isCo1TwoB_isConj hy isCo1TwoB_sBc)
  have h8 : y ^ 8 = 1 := by
    have h := pow_orderOf_eq_one (y ^ 4)
    rw [hy.1, ← pow_mul] at h
    exact h
  have hca : conjB * A₁ * conjB⁻¹ = ((sBG : GA) : GL24) := by
    rw [conjB_conj, mul_inv_cancel_right]
  obtain ⟨z, hzGA, hz8, hz4⟩ := @exists_fourth_root_of_conj NativeSporadic.Co1 GL24 Units.instGroup
    _ (fun x => ((co1MatEquiv x : GA) : GL24)) (fun a b => by rw [map_mul]; rfl) GA
    (fun x => (co1MatEquiv x).2) y g sBc A₁ conjB conjB_mem hg hca h8
  exact no_fourth_root_a₁ hzGA hz8 hz4

end CFSG.EvenSporadicStandard.TwoCo1.HypOne
