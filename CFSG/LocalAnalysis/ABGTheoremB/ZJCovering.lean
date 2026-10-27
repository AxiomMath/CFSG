module

import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStabilityReduction
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ABGTheoremB.Setting

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

universe u

section General

variable {G : Type u} [Group G] [Finite G]

private theorem zjc_mem_normalizer_of_conj_mem {J : Subgroup G} {g : G}
    (h : ∀ y ∈ J, g * y * g⁻¹ ∈ J) : g ∈ Subgroup.normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem zjc_normalizer_le_normalizer_map {Y : Subgroup G} (A : Subgroup Y)
    [hA : A.Characteristic] :
    Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer ((A.map Y.subtype : Subgroup G) : Set G) := by
  intro g hg
  apply zjc_mem_normalizer_of_conj_mem
  rintro _ ⟨a, ha, rfl⟩
  have hfix := hA.fixed (Subgroup.normalizerMonoidHom Y ⟨g, hg⟩)
  have hmem : a ∈ Subgroup.comap (Subgroup.normalizerMonoidHom Y ⟨g, hg⟩).toMonoidHom A := by
    rw [hfix]
    exact ha
  refine ⟨_, hmem, ?_⟩
  change (((Subgroup.normalizerMonoidHom Y ⟨g, hg⟩) a : Y) : G) = g * a * g⁻¹
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]

private theorem zjc_thompsonCenter_subgroupOf_map {Y P : Subgroup G} (hPY : P ≤ Y) :
    (thompsonCenter (G := Y) (P.subgroupOf Y)).map Y.subtype = thompsonCenter (G := G) P := by
  have h1 := thompsonCenter_top_map_subtype (G := Y) (P.subgroupOf Y)
  have h2 := thompsonCenter_top_map_subtype (G := G) P
  have h3 := thompsonCenter_top_map_mulEquiv (G := P.subgroupOf Y)
    (Subgroup.subgroupOfEquivOfLe hPY)
  rw [← h1, ← h2, ← h3, Subgroup.map_map, Subgroup.map_map]
  rfl

omit [Finite G] in
private theorem zjc_map_normalizer {Y : Subgroup G} (Q : Subgroup Y) :
    (Subgroup.normalizer (Q : Set Y)).map Y.subtype =
      Y ⊓ Subgroup.normalizer ((Q.map Y.subtype : Subgroup G) : Set G) := by
  have hle : Q.map Y.subtype ≤ Y := Subgroup.map_subtype_le Q
  have hQ : (Q.map Y.subtype).subgroupOf Y = Q :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective Q
  have h := Subgroup.subgroupOf_normalizer_eq hle
  rw [hQ] at h
  rw [← h, Subgroup.subgroupOf_map_subtype, inf_comm]

private theorem zjc_hasAbelianSylowTwo_of_odd {H : Type*} [Group H] [Finite H]
    (hH : Odd (Nat.card H)) : CFSG.BenderSuzuki.HasAbelianSylow 2 H := by
  have hodd : Odd (Nat.card (⊤ : Subgroup H)) := by rwa [Subgroup.card_top]
  have : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  exact CFSG.BenderSuzuki.hasAbelianSylowTwo_of_odd_normal_quotient_isMulCommutative ⊤ hodd
    ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩

omit [Finite G] in
private theorem zjc_le_of_le_sup_of_coprime {O A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (O : Set G)) (hB : B ≤ Subgroup.normalizer (O : Set G))
    (hAB : A ≤ B ⊔ O) (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) : A ≤ O := by
  have h1 : O.relIndex A ∣ O.relIndex B := by
    rw [← relIndex_sup_right_of_le_normalizer hA, ← relIndex_sup_right_of_le_normalizer hB]
    exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex O (A ⊔ O) (B ⊔ O) le_sup_right
      (sup_le hAB le_sup_right))
  refine Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop ?_ ?_)
  · exact Dvd.intro _ (Subgroup.relIndex_mul_card O A)
  · exact h1.trans (Dvd.intro _ (Subgroup.relIndex_mul_card O B))

variable {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
private theorem zjc_le_pPrimeCoreIn {X K : Subgroup G} (hXK : X ≤ K)
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) (hX : Nat.Coprime p (Nat.card X)) :
    X ≤ pPrimeCoreIn p K := by
  have hn : (X.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hKX
  have hc : Nat.Coprime p (Nat.card (X.subgroupOf K)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv]
  have hle : X.subgroupOf K ≤ CFSG.pPrimeCore p K := le_sSup ⟨hn, hc⟩
  intro x hx
  exact ⟨⟨x, hXK hx⟩, hle hx, rfl⟩

private theorem zjc_coprime_card_pPrimeCoreIn (K : Subgroup G) :
    Nat.Coprime p (Nat.card (pPrimeCoreIn p K)) := by
  rw [pPrimeCoreIn, Subgroup.card_map_of_injective K.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

omit [Fact p.Prime] in
private theorem zjc_normalizer_le_normalizer_pPrimeCoreIn (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((pPrimeCoreIn p K : Subgroup G) : Set G) :=
  zjc_normalizer_le_normalizer_map (CFSG.pPrimeCore p K)

private theorem zjc_zj_odd (hp : p ≠ 2) {X P : Subgroup G} (hX : Odd (Nat.card X))
    (hP : IsSylowOf p P X) (hcore : CFSG.pCore p X ≠ ⊥) :
    pPrimeCoreIn p X ⊔ (X ⊓ Subgroup.normalizer (thompsonCenter (G := G) P : Set G)) = X := by
  obtain ⟨S, hS⟩ := hP.exists_sylow_eq_subgroupOf
  have hsolv : Group.IsSolvable X := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hX
  have hZJ := CFSG.G_theorem_8_2_11 (G := X) p hp hcore
    (isPConstrained_iff_pConstrainedGroup.mp (isPConstrained_of_isSolvable hsolv))
    (CFSG.BenderSuzuki.pStableGroup'_of_solvable_abelianSylowTwo hsolv
      (zjc_hasAbelianSylowTwo_of_odd hX) ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp)) S
  set Z : Subgroup X := thompsonCenter (G := X) (S : Subgroup X) with hZ
  have hZp : IsPGroup p Z := S.isPGroup'.to_le (thompsonCenter_le_self _)
  have hM : (CFSG.pPrimeCore p X ⊔ Z).Normal := by rwa [sup_comm]
  have hsyl : IsSylowOf p Z (CFSG.pPrimeCore p X ⊔ Z) :=
    isSylowOf_sup_of_coprime CFSG.pPrimeCore_coprime_card hZp
  obtain ⟨T, hT⟩ := hsyl
  have hfr := Sylow.normalizer_sup_eq_top (N := CFSG.pPrimeCore p X ⊔ Z) T
  rw [hT] at hfr
  have htop : CFSG.pPrimeCore p X ⊔ Subgroup.normalizer (Z : Set X) = ⊤ := by
    apply top_le_iff.mp
    rw [← hfr]
    exact sup_le le_sup_right (sup_le le_sup_left (le_sup_of_le_right Subgroup.le_normalizer))
  have h := congrArg (Subgroup.map X.subtype) htop
  rw [Subgroup.map_sup, zjc_map_normalizer, hZ, hS, zjc_thompsonCenter_subgroupOf_map hP.le,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

private theorem zjc_isSylowOf_map_conj {Z X : Subgroup G} (hZ : IsSylowOf p Z X) {k : G}
    (hk : k ∈ Subgroup.normalizer (X : Set G)) :
    IsSylowOf p (Z.map (MulAut.conj k).toMonoidHom) X := by
  apply isSylowOf_of_card
  · rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hk z).mp (hZ.le hz)
  · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hZ.card_eq]

theorem zjCovering_sup (hp : p ≠ 2) {K O U B : Subgroup G} (hOK : O ≤ K)
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (hO : Odd (Nat.card O)) (hUK : U ≤ K)
    (hU : IsPGroup p U) (hUO : IsSylowOf p (U ⊓ O) O) (hB : B ≠ ⊥) (hBp : IsPGroup p B)
    (hBO : B ≤ O) (hKB : K ≤ Subgroup.normalizer (B : Set G)) :
    Odd (Nat.card (O ⊔ U : Subgroup G)) ∧ IsSylowOf p U (O ⊔ U) ∧
      pPrimeCoreIn p O ⊔ ((O ⊔ U) ⊓ Subgroup.normalizer (thompsonCenter (G := G) U : Set G)) =
        O ⊔ U := by
  set X := O ⊔ U with hX
  have hXK : X ≤ K := sup_le hOK hUK
  have hUN : U ≤ Subgroup.normalizer (O : Set G) := hUK.trans hKO
  have hUodd : Odd (Nat.card U) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
    rw [hk]
    exact ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp).pow
  have hXodd : Odd (Nat.card X) := odd_card_sup_of_le_normalizer_of_odd hUN hO hUodd
  have hUX : IsSylowOf p U X := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_right, hU, ?_⟩
    rw [relIndex_sup_eq_relIndex_of_le_normalizer hUN, ← Subgroup.inf_relIndex_right]
    exact (isSylowOf_iff.mp hUO).2.2
  have hcore : CFSG.pCore p X ≠ ⊥ := by
    have hBX : B ≤ X := hBO.trans le_sup_left
    have hn : (B.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBX).mpr (hXK.trans hKB)
    have hle : B.subgroupOf X ≤ CFSG.pCore p X := le_sSup ⟨hn, hBp.comap_subtype⟩
    intro hbot
    rw [hbot, le_bot_iff] at hle
    apply hB
    rw [← Subgroup.map_subgroupOf_eq_of_le hBX, hle, Subgroup.map_bot]
  have hzj := zjc_zj_odd hp hXodd hUX hcore
  have hMO : pPrimeCoreIn p X ≤ O := by
    refine zjc_le_of_le_sup_of_coprime ((pPrimeCoreIn_le p X).trans (hXK.trans hKO)) hUN
      ((pPrimeCoreIn_le p X).trans (sup_comm O U).le) ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
    rw [hk]
    exact (Nat.Coprime.pow_left k (zjc_coprime_card_pPrimeCoreIn X)).symm
  have hMOO : pPrimeCoreIn p X ≤ pPrimeCoreIn p O :=
    zjc_le_pPrimeCoreIn hMO ((le_sup_left : O ≤ X).trans
      (Subgroup.le_normalizer.trans (zjc_normalizer_le_normalizer_pPrimeCoreIn X)))
      (zjc_coprime_card_pPrimeCoreIn X)
  refine ⟨hXodd, hUX, le_antisymm (sup_le ((pPrimeCoreIn_le p O).trans le_sup_left)
    inf_le_left) ?_⟩
  calc X = pPrimeCoreIn p X ⊔ (X ⊓ Subgroup.normalizer
        (thompsonCenter (G := G) U : Set G)) := hzj.symm
    _ ≤ _ := sup_le_sup_right hMOO _

theorem zjCovering_normalizer_le (hp : p ≠ 2) {K O U B : Subgroup G} (hOK : O ≤ K)
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (hO : Odd (Nat.card O)) (hUK : U ≤ K)
    (hU : IsPGroup p U) (hUO : IsSylowOf p (U ⊓ O) O) (hB : B ≠ ⊥) (hBp : IsPGroup p B)
    (hBO : B ≤ O) (hKB : K ≤ Subgroup.normalizer (B : Set G)) :
    K ⊓ Subgroup.normalizer ((O ⊔ U : Subgroup G) : Set G) ≤
      (K ⊓ Subgroup.normalizer (thompsonCenter (G := G) U : Set G)) ⊔ O := by
  obtain ⟨-, hUX, hfac⟩ := zjCovering_sup hp hOK hKO hO hUK hU hUO hB hBp hBO hKB
  set Z := thompsonCenter (G := G) U with hZ
  have hXK : O ⊔ U ≤ K := sup_le hOK hUK
  intro g hg
  obtain ⟨hgK, hgX⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨y, hy, hconj⟩ := hUX.exists_mem_conj (zjc_isSylowOf_map_conj hUX hgX)
  have hc : y⁻¹ * g ∈ Subgroup.normalizer (U : Set G) := by
    apply zjc_mem_normalizer_of_conj_mem
    intro u hu
    have h := (hconj (g * u * g⁻¹)).mp ⟨u, hu, rfl⟩
    rwa [show y⁻¹ * g * u * (y⁻¹ * g)⁻¹ = y⁻¹ * (g * u * g⁻¹) * y by group]
  have hcZ : y⁻¹ * g ∈ Subgroup.normalizer (Z : Set G) :=
    normalizer_le_normalizer_thompsonCenter U hc
  have hcK : y⁻¹ * g ∈ K := K.mul_mem (K.inv_mem (hXK hy)) hgK
  have hyX : y ∈ (((O ⊔ U) ⊓ Subgroup.normalizer (Z : Set G) ⊔ O : Subgroup G) : Set G) := by
    have h : O ⊔ U ≤ (O ⊔ U) ⊓ Subgroup.normalizer (Z : Set G) ⊔ O :=
      hfac.ge.trans (sup_le ((pPrimeCoreIn_le p O).trans le_sup_right) le_sup_left)
    exact h hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (inf_le_left.trans (hXK.trans hKO))]
    at hyX
  obtain ⟨n, hn, o, ho, hno⟩ := hyX
  have hno : n * o = y := hno
  obtain ⟨hnX, hnZ⟩ := Subgroup.mem_inf.mp hn
  have ho' : (y⁻¹ * g)⁻¹ * o * (y⁻¹ * g) ∈ O := by
    have h := (Subgroup.mem_normalizer_iff.mp (hKO (K.inv_mem hcK)) o).mp ho
    rwa [inv_inv] at h
  have hg' : g = n * (y⁻¹ * g) * ((y⁻¹ * g)⁻¹ * o * (y⁻¹ * g)) := by
    rw [← hno]
    group
  rw [hg']
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨K.mul_mem (hXK hnX) hcK,
    Subgroup.mul_mem _ hnZ hcZ⟩) ho'

theorem zjCovering_eq_of_le (hp : p ≠ 2) {K O U B : Subgroup G} (hOK : O ≤ K)
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (hO : Odd (Nat.card O)) (hUK : U ≤ K)
    (hU : IsPGroup p U) (hUO : IsSylowOf p (U ⊓ O) O) (hB : B ≠ ⊥) (hBp : IsPGroup p B)
    (hBO : B ≤ O) (hKB : K ≤ Subgroup.normalizer (B : Set G)) (hUO' : U ≤ O) :
    (K ⊓ Subgroup.normalizer (thompsonCenter (G := G) U : Set G)) ⊔ O = K := by
  refine le_antisymm (sup_le inf_le_left hOK) fun g hg => ?_
  apply zjCovering_normalizer_le hp hOK hKO hO hUK hU hUO hB hBp hBO hKB
  refine Subgroup.mem_inf.mpr ⟨hg, ?_⟩
  rw [sup_eq_left.mpr hUO']
  exact hKO hg

theorem zjCovering_upgrade (hp : p ≠ 2) {K O U B : Subgroup G} (hOK : O ≤ K)
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (hO : Odd (Nat.card O)) (hUK : U ≤ K)
    (hU : IsPGroup p U) (hUO : IsSylowOf p (U ⊓ O) O) (hB : B ≠ ⊥) (hBp : IsPGroup p B)
    (hBO : B ≤ O) (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hK : O ⊔ (K ⊓ Subgroup.normalizer (thompsonCenter (G := G) U : Set G)) = K) :
    pPrimeCoreIn p K ⊔ (K ⊓ Subgroup.normalizer (thompsonCenter (G := G) U : Set G)) = K := by
  obtain ⟨-, -, hfac⟩ := zjCovering_sup hp hOK hKO hO hUK hU hUO hB hBp hBO hKB
  have hO' : pPrimeCoreIn p O ≤ pPrimeCoreIn p K :=
    zjc_le_pPrimeCoreIn ((pPrimeCoreIn_le p O).trans hOK)
      (hKO.trans (zjc_normalizer_le_normalizer_pPrimeCoreIn O)) (zjc_coprime_card_pPrimeCoreIn O)
  have hOle : O ≤ pPrimeCoreIn p K ⊔
      (K ⊓ Subgroup.normalizer (thompsonCenter (G := G) U : Set G)) := by
    refine (le_sup_left : O ≤ O ⊔ U).trans (hfac.ge.trans (sup_le (hO'.trans le_sup_left) ?_))
    exact (inf_le_inf_right _ (sup_le hOK hUK)).trans le_sup_right
  refine le_antisymm (sup_le (pPrimeCoreIn_le p K) inf_le_left) ?_
  calc K = O ⊔ (K ⊓ Subgroup.normalizer (thompsonCenter (G := G) U : Set G)) := hK.symm
    _ ≤ _ := sup_le hOle le_sup_right

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

theorem propR1 (hσ : σ.IsValid) {K U W L₁ E₁ X₁ : Subgroup G}
    (hK : K ∈ σ.familyL σ.p) (hU : U ∈ maximals (signalizers K σ.D σ.p))
    (hUO : IsSylowOf σ.p (U ⊓ oddCoreIn K) (oddCoreIn K)) (hWK : W ≤ K)
    (hWZ : W ≤ Subgroup.normalizer (thompsonCenter (G := G) U : Set G))
    (h_V_3_1 : ¬ σ.p ∣ Nat.card W)
    (h_II_4_9_i : U ≤ Subgroup.normalizer ((W ⊔ oddCoreIn K : Subgroup G) : Set G))
    (h_II_4_2_iii : ∀ y ∈ U, (∀ w ∈ W, y * w * y⁻¹ * w⁻¹ ∈ oddCoreIn K) → y ∈ oddCoreIn K)
    (h_II_3_3 : K ≤ L₁ ⊔ E₁)
    (h_II_3_3_E : E₁ ≤ K ⊓ Subgroup.normalizer ((oddCoreIn K ⊔ U : Subgroup G) : Set G))
    (h_II_4_2_vi : X₁ ≤ K ⊓ Subgroup.normalizer ((oddCoreIn K ⊔ U : Subgroup G) : Set G))
    (h_II_4_6 : L₁ ≤ W ⊔ σ.D ⊔ X₁ ⊔ oddCoreIn K) :
    thompsonCenter (G := G) U ≤ oddCoreIn K ∧
      pPrimeCoreIn σ.p K ⊔ (K ⊓ Subgroup.normalizer (thompsonCenter (G := G) U : Set G)) =
        K := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  have hp2 : σ.p ≠ 2 := hσ.p_ne_two
  set O := oddCoreIn K with hOdef
  set Z := thompsonCenter (G := G) U with hZdef
  obtain ⟨hUK, hUp, hDU, -⟩ := hU.1
  obtain ⟨⟨X₀, hX₀, hX₀p, hKX₀⟩, -, hDK, -⟩ := hK
  have hOK : O ≤ K := oddCoreIn_le K
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_oddCoreIn K
  have hO : Odd (Nat.card O) := odd_card_oddCoreIn K
  have hX₀odd : Odd (Nat.card X₀) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX₀p
    rw [hk]
    exact (hσ.p_prime.eq_two_or_odd'.resolve_left hp2).pow
  have hX₀N : K ≤ Subgroup.normalizer (X₀ : Set G) := hKX₀.le
  have hX₀O : X₀ ≤ O := by
    rw [hOdef, hKX₀]
    exact le_oddCoreIn Subgroup.le_normalizer le_rfl hX₀odd
  have hZU : Z ≤ U := thompsonCenter_le_self U
  have hZO : Z ≤ O := by
    intro z hz
    refine h_II_4_2_iii z (hZU hz) fun w hw => ?_
    have hc1 : z * w * z⁻¹ * w⁻¹ ∈ Z := by
      have h := (Subgroup.mem_normalizer_iff.mp (hWZ hw) z⁻¹).mp (Z.inv_mem hz)
      rw [show z * w * z⁻¹ * w⁻¹ = z * (w * z⁻¹ * w⁻¹) by group]
      exact Z.mul_mem hz h
    have hc2 : z * w * z⁻¹ * w⁻¹ ∈ W ⊔ O := by
      have h := (Subgroup.mem_normalizer_iff.mp (h_II_4_9_i (hZU hz)) w).mp
        (Subgroup.mem_sup_left hw)
      exact (W ⊔ O).mul_mem h (Subgroup.mem_sup_left (W.inv_mem hw))
    have hcK : z * w * z⁻¹ * w⁻¹ ∈ K := hUK (hZU hc1)
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers (z * w * z⁻¹ * w⁻¹))) (Nat.card W) := by
      rw [Nat.card_zpowers]
      obtain ⟨k, hk⟩ := hUp ⟨_, hZU hc1⟩
      have hdvd : orderOf (z * w * z⁻¹ * w⁻¹) ∣ σ.p ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      exact Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.pow_left k
        ((Nat.Prime.coprime_iff_not_dvd hσ.p_prime).mpr h_V_3_1))
    exact zjc_le_of_le_sup_of_coprime ((Subgroup.zpowers_le.mpr hcK).trans hKO)
      (hWK.trans hKO) (Subgroup.zpowers_le.mpr hc2) hcop (Subgroup.mem_zpowers _)
  have hRb := zjCovering_normalizer_le hp2 hOK hKO hO hUK hUp hUO hX₀ hX₀p hX₀O hX₀N
  have hDZ : σ.D ≤ K ⊓ Subgroup.normalizer (Z : Set G) :=
    le_inf hDK (hDU.trans (normalizer_le_normalizer_thompsonCenter U))
  have hWZ' : W ≤ K ⊓ Subgroup.normalizer (Z : Set G) := le_inf hWK hWZ
  have hKle : K ≤ K ⊓ Subgroup.normalizer (Z : Set G) ⊔ O := by
    refine h_II_3_3.trans (sup_le (h_II_4_6.trans ?_) (h_II_3_3_E.trans hRb))
    exact sup_le (sup_le (sup_le (hWZ'.trans le_sup_left) (hDZ.trans le_sup_left))
      (h_II_4_2_vi.trans hRb)) le_sup_right
  have hKeq : O ⊔ (K ⊓ Subgroup.normalizer (Z : Set G)) = K :=
    le_antisymm (sup_le hOK inf_le_left) (hKle.trans (sup_comm _ _).le)
  exact ⟨hZO, zjCovering_upgrade hp2 hOK hKO hO hUK hUp hUO hX₀ hX₀p hX₀O hX₀N hKeq⟩

end Setting

end CFSG.ABGTheoremB
