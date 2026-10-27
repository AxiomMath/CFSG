module

public import CFSG.LocalAnalysis.AGLEmbedding.CharCore
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G] [Finite G]

@[expose] def nclIn (H X : Subgroup G) : Subgroup G :=
  (Subgroup.normalClosure ((X.subgroupOf H : Subgroup H) : Set H)).map H.subtype

omit [Finite G] in
theorem le_nclIn {H X : Subgroup G} (hXH : X ≤ H) : X ≤ nclIn H X := by
  have h := Subgroup.map_mono (f := H.subtype) (Subgroup.le_normalClosure (H := X.subgroupOf H))
  rwa [Subgroup.map_subgroupOf_eq_of_le hXH] at h

omit [Finite G] in
theorem nclIn_le_self (H X : Subgroup G) : nclIn H X ≤ H :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem nclIn_normal (H X : Subgroup G) : ((nclIn H X).subgroupOf H).Normal := by
  rw [Subgroup.subgroupOf, nclIn, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  infer_instance

omit [Finite G] in
theorem le_normalizer_nclIn (H X : Subgroup G) :
    H ≤ Subgroup.normalizer (nclIn H X : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (nclIn_le_self H X)).mp (nclIn_normal H X)

omit [Finite G] in
theorem nclIn_le {H X K : Subgroup G} (hXK : X ≤ K) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) : nclIn H X ≤ K := by
  have : (K.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
  rw [nclIn, ← Subgroup.map_subgroupOf_eq_of_le hKH]
  exact Subgroup.map_mono (Subgroup.normalClosure_le_normal fun x hx => hXK hx)

omit [Finite G] in
theorem commutator_nclIn_le {H X N S : Subgroup G} (hXH : X ≤ H)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hHS : H ≤ Subgroup.normalizer (S : Set G))
    (hNX : ⁅N, X⁆ ≤ S) : ⁅N, nclIn H X⁆ ≤ S := by
  let C : Subgroup G :=
    { carrier := {y | y ∈ H ∧ ∀ n ∈ N, n * y * n⁻¹ * y⁻¹ ∈ S}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨H.mul_mem ha hb, fun n hn => ?_⟩
        have e : n * (a * b) * n⁻¹ * (a * b)⁻¹ =
            n * a * n⁻¹ * a⁻¹ * (a * (n * b * n⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact S.mul_mem (ha' n hn) ((Subgroup.mem_normalizer_iff.mp (hHS ha) _).mp (hb' n hn))
      one_mem' := ⟨H.one_mem, fun n _ => by simp [S.one_mem]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨H.inv_mem ha, fun n hn => ?_⟩
        have hm : a⁻¹ * n * a ∈ N := by
          simpa using (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem ha)) n).mp hn
        have e : n * a⁻¹ * n⁻¹ * a⁻¹⁻¹ = (a⁻¹ * n * a * a * (a⁻¹ * n * a)⁻¹ * a⁻¹)⁻¹ := by
          group
        rw [e]
        exact S.inv_mem (ha' _ hm) }
  have hCH : C ≤ H := fun y hy => hy.1
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ H, ∀ y ∈ C, g * y * g⁻¹ ∈ C := by
      rintro g hg y ⟨hy, hy'⟩
      refine ⟨H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg), fun n hn => ?_⟩
      have hm : g⁻¹ * n * g ∈ N := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem hg)) n).mp hn
      have e : n * (g * y * g⁻¹) * n⁻¹ * (g * y * g⁻¹)⁻¹ =
          g * (g⁻¹ * n * g * y * (g⁻¹ * n * g)⁻¹ * y⁻¹) * g⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hHS hg) _).mp (hy' _ hm)
    intro y
    refine ⟨key h hh y, fun hy => ?_⟩
    simpa [mul_assoc] using key h⁻¹ (H.inv_mem hh) _ hy
  have hXC : X ≤ C := fun x hx => ⟨hXH hx, fun n hn => by
    simpa only [commutatorElement_def] using hNX (Subgroup.commutator_mem_commutator hn hx)⟩
  have hle := nclIn_le hXC hCH hHC
  rw [Subgroup.commutator_le]
  intro n hn y hy
  rw [commutatorElement_def]
  exact (hle hy).2 n hn

theorem normalizer_le_normalizer_pCoreOf_glbPrimeCore (p : ℕ) (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p J) : Set G) := by
  have : (primeComplementCore (G := J) p).Characteristic := primeComplementCore_characteristic p
  refine le_trans ?_ (normalizer_localGroup_le_normalizer_pCoreOf 2 _)
  rw [glbPrimeCore_eq_primeComplementCoreOf]
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _

theorem normal_pCoreOf_two_glbPrimeCore (p : ℕ) {J H' : Subgroup G} (hJH' : J ≤ H')
    (hJ : (J.subgroupOf H').Normal) :
    ((pCoreOf 2 (GLBPrimeCore p J)).subgroupOf H').Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
      (((pCoreOf_le 2 _).trans (glbPrimeCore_le p J)).trans hJH')).mpr
    (((Subgroup.normal_subgroupOf_iff_le_normalizer hJH').mp hJ).trans
      (normalizer_le_normalizer_pCoreOf_glbPrimeCore p J))

theorem pCoreOf_two_primeCore_ne_bot_of_normal {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H J X : Subgroup G} (hH : CharTwo H) (hJH : J ≤ H)
    (hHJ : H ≤ Subgroup.normalizer (J : Set G)) (hXJ : X ≤ J) (hX : IsPGroup p X)
    (hX1 : X ≠ ⊥) : pCoreOf 2 (GLBPrimeCore p J) ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 (pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  have hHS : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := localGroup_le_normalizer_pCoreOf 2 H
  have hJSJ : J ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓ J : Subgroup G) : Set G) :=
    (le_inf (hJH.trans hHS) Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hSJ2 : IsPGroup 2 (pCoreOf 2 H ⊓ J : Subgroup G) := hS2.to_le inf_le_left
  have hcop : p.Coprime (Nat.card (pCoreOf 2 H ⊓ J : Subgroup G)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSJ2
    exact hk ▸ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right k
  have hO : pCoreOf 2 H ⊓ J ≤ GLBPrimeCore p J := le_glbPrimeCore inf_le_right hJSJ hcop
  have hO2 : pCoreOf 2 H ⊓ J ≤ pCoreOf 2 (GLBPrimeCore p J) :=
    normal_pGroup_le_pCoreOf 2 _ _ hO
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hO).mpr ((glbPrimeCore_le p J).trans hJSJ))
      hSJ2
  intro hbot
  have hSJ : pCoreOf 2 H ⊓ J = ⊥ := le_bot_iff.mp (hbot ▸ hO2)
  have hJS : J ≤ pCoreOf 2 H := by
    intro j hj
    refine hH ⟨hJH hj, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hc : s * j * s⁻¹ * j⁻¹ ∈ pCoreOf 2 H ⊓ J := by
      refine ⟨?_, J.mul_mem ((Subgroup.mem_normalizer_iff.mp
        (hHJ (pCoreOf_le 2 H hs)) j).mp hj) (J.inv_mem hj)⟩
      rw [mul_assoc, mul_assoc]
      refine (pCoreOf 2 H).mul_mem hs ?_
      rw [← mul_assoc]
      exact (Subgroup.mem_normalizer_iff.mp (hHS (hJH hj)) s⁻¹).mp ((pCoreOf 2 H).inv_mem hs)
    rw [hSJ, Subgroup.mem_bot] at hc
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc)
  exact hX1 ((IsPGroup.disjoint_of_ne p 2 hp2 X (pCoreOf 2 H) hX hS2).eq_bot_of_le
    (hXJ.trans hJS))

theorem pCoreOf_two_primeCore_ne_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H X : Subgroup G}
    (hH : CharTwo H) (hXH : X ≤ H) (hX : IsPGroup p X) (hX1 : X ≠ ⊥) :
    pCoreOf 2 (GLBPrimeCore p (nclIn H X)) ≠ ⊥ :=
  pCoreOf_two_primeCore_ne_bot_of_normal hp hp2 hH (nclIn_le_self H X) (le_normalizer_nclIn H X)
    (le_nclIn hXH) hX hX1

omit [Finite G] in
theorem maxTwoLocal_normalizer_eq_of_normal {H A : Subgroup G} (hH : GLBIsMaxTwoLocal H)
    (hA : A ≠ ⊥) (hA2 : IsPGroup 2 A) (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal) :
    Subgroup.normalizer (A : Set G) = H :=
  maxTwoLocal_normalizer_eq_of_le_normalizer hH hA hA2
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mp hAn)

end CFSG.AGLEmbedding
