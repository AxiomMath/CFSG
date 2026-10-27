module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266G2Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K266G2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T266

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.K266
open CFSG.LocalAnalysis.GLTheoremA.S267
open scoped commutatorElement

section Transport

variable {G' : Type} [Group G']

theorem map_centralizer_subtype_set (K : Subgroup G') (S : Set K) :
    (Subgroup.centralizer S).map K.subtype = K ⊓ Subgroup.centralizer (K.subtype '' S) := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine Subgroup.mem_inf.2 ⟨c.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc s hs)
    simpa using h1
  · intro hx
    obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.1 hx
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    show _ ∈ Subgroup.centralizer S
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply Subtype.ext
    have h1 := Subgroup.mem_centralizer_iff.1 hxC (s : G') ⟨s, hs, rfl⟩
    simpa using h1

theorem le_normalizer_map (K : Subgroup G') {D : Subgroup G'} (hDK : D ≤ K) {T' : Subgroup K}
    (hN : D.subgroupOf K ≤ Subgroup.normalizer (T' : Set K)) :
    D ≤ Subgroup.normalizer ((T'.map K.subtype : Subgroup G') : Set G') := by
  intro d hd
  have hdK : d ∈ K := hDK hd
  have hd' : (⟨d, hdK⟩ : K) ∈ D.subgroupOf K := Subgroup.mem_subgroupOf.2 hd
  have hN' := Subgroup.mem_normalizer_iff.1 (hN hd')
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · rintro ⟨t', ht', rfl⟩
    have h1 : (⟨d, hdK⟩ : K) * t' * (⟨d, hdK⟩ : K)⁻¹ ∈ T' := (hN' t').1 ht'
    have h2 := Subgroup.mem_map_of_mem K.subtype h1
    simpa [mul_assoc] using h2
  · intro ht
    obtain ⟨s, hs, hsd⟩ := Subgroup.mem_map.1 ht
    have htK : t ∈ K := by
      have h1 : t = d⁻¹ * (d * t * d⁻¹) * d := by group
      rw [h1]
      exact K.mul_mem (K.mul_mem (K.inv_mem hdK) (by rw [← hsd]; exact s.2)) hdK
    set t' : K := ⟨t, htK⟩ with ht'def
    refine ⟨t', ?_, rfl⟩
    refine (hN' t').2 ?_
    have h2 : (⟨d, hdK⟩ : K) * t' * (⟨d, hdK⟩ : K)⁻¹ = s := by
      apply Subtype.ext
      simp only [ht'def, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hsd]
      simp [mul_assoc]
    rw [h2]
    exact hs

theorem subgroupOf_le_normalizer {K D T : Subgroup G'} (hDK : D ≤ K) (hTK : T ≤ K)
    (hDN : D ≤ Subgroup.normalizer (T : Set G')) :
    D.subgroupOf K ≤ Subgroup.normalizer ((T.subgroupOf K : Subgroup K) : Set K) := by
  intro d hd
  have hdN := Subgroup.mem_normalizer_iff.1 (hDN (Subgroup.mem_subgroupOf.1 hd))
  rw [Subgroup.mem_normalizer_iff]
  intro t
  have h1 := hdN (t : G')
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact h1

theorem map_subgroupOf_self {K D : Subgroup G'} (hDK : D ≤ K) :
    (D.subgroupOf K).map K.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDK

noncomputable def pquotMapInj {X Y : Type} [Group X] [Group Y] (p : ℕ) (J : Subgroup X) (ψ : X →* Y)
    (hψ : Function.Injective ψ) : PQuot p J ≃* PQuot p (J.map ψ) :=
  QuotientGroup.congr _ _ (Subgroup.equivMapOfInjective J ψ hψ)
    (glaPPrimeCore_map_iso p (Subgroup.equivMapOfInjective J ψ hψ))

theorem catalogIs_psimple_map_inj {X Y : Type} [Group X] [Group Y] (J : Subgroup X) (ψ : X →* Y)
    (hψ : Function.Injective ψ) (Q : TauCeti.CFSGIndex → Prop) :
    catalogIs (PSimple 3 J) Q ↔ catalogIs (PSimple 3 (J.map ψ)) Q :=
  catalogIs_congr (QuotientGroup.congr _ _ (pquotMapInj 3 J ψ hψ) (Subgroup.map_center_eq (pquotMapInj 3 J ψ hψ)))

end Transport

section Derive

variable {n : ℕ}

theorem deriveInn (h : T266G2Inn n) : K266InnG2 n := by
  intro G' _ _ X K A _hK hG2 hZ hO hInn
  exact h G' K A hG2 hZ hO hInn

theorem deriveOdd (h : T266G2Odd n) : K266OddG2 n := by
  intro G' _ _ K D T hK hodd hD hD9 hDK hTK hT2 hT0 hDN
  have hD' : IsElemAbelian 3 (D.subgroupOf K) := isElemAbelian_subgroupOf hD K
  have hcard : Nat.card (D.subgroupOf K) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv
  have hT' : IsPGroup 2 (T.subgroupOf K) :=
    (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm)
  have hT'ne : T.subgroupOf K ≠ ⊥ := by
    intro h0
    apply hT0
    rw [← Subgroup.map_subgroupOf_eq_of_le hTK, h0, Subgroup.map_bot]
  exact h K (D.subgroupOf K) (T.subgroupOf K) hK hodd hD' (hcard ▸ hD9) hT' hT'ne
    (subgroupOf_le_normalizer hDK hTK hDN)

theorem deriveLayer (h : T266G2Layer n) : K266LayerG2 n := by
  intro G' _ _ K D hK hEven hD hD9 hDK
  have hD' : IsElemAbelian 3 (D.subgroupOf K) := isElemAbelian_subgroupOf hD K
  have hcard : 9 ≤ Nat.card (D.subgroupOf K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv]
    exact hD9
  have h1 := h K (D.subgroupOf K) hK hEven hD' hcard
  have hN : ¬ 3 ∣ Nat.card (K.subtype : ↥K →* G').ker := by
    rw [Subgroup.ker_subtype, Subgroup.card_bot]
    exact Nat.prime_three.not_dvd_one
  have hm := map_glaPLayer Nat.prime_three K.subtype hN
    (Subgroup.centralizer ((D.subgroupOf K : Subgroup K) : Set K))
  rw [h1, Subgroup.map_bot, map_centralizer_subtype_set] at hm
  have himg : K.subtype '' ((D.subgroupOf K : Subgroup K) : Set K) = (D : Set G') := by
    rw [← Subgroup.coe_map, map_subgroupOf_self hDK]
  rw [himg] at hm
  exact hm.symm

theorem deriveKey (h : T266G2Key n) : K266KeyG2 n := by
  intro G' _ _ K D hK hEven hD hD9 hDK
  have hD' : IsElemAbelian 3 (D.subgroupOf K) := isElemAbelian_subgroupOf hD K
  have hcard : 9 ≤ Nat.card (D.subgroupOf K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv]
    exact hD9
  obtain ⟨y', hy'D, hy'1, ⟨J', hJ'ne, hJ'c, hJ'cat⟩, ⟨T', hT'C, hT'2, hT'N, hT'comm, hT'Q⟩⟩ :=
    h K (D.subgroupOf K) hK hEven hD' hcard
  have hψ : Function.Injective K.subtype := K.subtype_injective
  have hker : Nat.Coprime 3 (Nat.card ↥(Subgroup.centralizer ({y'} : Set K) ⊓ K.subtype.ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have hcomp := glaPComponent_map Nat.prime_three K.subtype hker hJ'c
  rw [map_centralizer_subtype_set, Set.image_singleton] at hcomp
  have hJne : J'.map K.subtype ≠ ⊥ := by
    intro h0
    exact hJ'ne ((Subgroup.map_eq_bot_iff_of_injective J' hψ).1 h0)
  have hcat := (catalogIs_psimple_map_inj J' K.subtype hψ (isL2n n)).1 hJ'cat
  have hTC : T'.map K.subtype ≤ K ⊓ Subgroup.centralizer ({(y' : G')} : Set G') := by
    have := Subgroup.map_mono (f := K.subtype) hT'C
    rwa [map_centralizer_subtype_set, Set.image_singleton] at this
  have hT2 : IsPGroup 2 (T'.map K.subtype) := hT'2.map K.subtype
  have hTN : D ≤ Subgroup.normalizer ((T'.map K.subtype : Subgroup G') : Set G') :=
    le_normalizer_map K hDK hT'N
  have hcomm : (⁅T'.map K.subtype, D⁆ : Subgroup G') ≠ ⊥ := by
    rw [← map_subgroupOf_self hDK, ← Subgroup.map_commutator]
    intro h0
    exact hT'comm ((Subgroup.map_eq_bot_iff_of_injective _ hψ).1 h0)
  have hQ : IsEmpty (T'.map K.subtype ≃* QuaternionGroup 2) :=
    ⟨fun e => hT'Q.false ((Subgroup.equivMapOfInjective T' K.subtype hψ).trans e)⟩
  exact ⟨(y' : G'), Subgroup.mem_subgroupOf.1 hy'D, fun h0 => hy'1 (Subtype.ext h0),
    ⟨J'.map K.subtype, hJne, hcomp, hcat⟩, ⟨T'.map K.subtype, hTC, hT2, hTN, hcomm, hQ⟩⟩

end Derive

section Main

theorem i266G2_of_restated (G : Type) [Group G] [Finite G] (n : ℕ)
    (hInn : T266G2Inn n) (hOdd : T266G2Odd n) (hLayer : T266G2Layer n) (hKey : T266G2Key n)
    (hDisj : T266G2NotU6) (X K B : Subgroup G) (hK : GLAPComponent 3 X K)
    (hG2 : catalogIs (PSimple 3 K) (S10.isG2n n))
    (hZ : Subgroup.center (PQuot 3 K) = ⊥) (hO : GLAPPrimeCoreOf 3 K = ⊥)
    (hB : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (hBc : 3 ^ 2 * Nat.card ↥(B ⊓ centModSubgroup 3 K) ≤ Nat.card B)
    (hInnB : InnDiagOn 3 B K)
    (hT : ∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 K) :
    ∃ (E : Subgroup G) (y : G) (J : Subgroup G), S10.IsE0 B K E ∧ y ∈ E ∧ ¬ CentMod 3 K y ∧
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J ∧
      ((catalogIs (PSimple 3 K) (S10.isG2n n) → Even n ∧ catalogIs (PSimple 3 J) (S10.isL2n n)) ∧
        (catalogIs (PSimple 3 K) (S10.isU6n n) → catalogIs (PSimple 3 J) (S10.isUrn n))) ∧
      ∃ T : Subgroup G, T ≤ K ⊓ Subgroup.centralizer ({y} : Set G) ∧ IsPGroup 2 T ∧
        B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥ ∧
        IsEmpty (T ≃* QuaternionGroup 2) :=
  i266G2_of_facts G n (deriveInn hInn) (deriveOdd hOdd) (deriveLayer hLayer) (deriveKey hKey) hDisj
    X K B hK hG2 hZ hO hB hBN hBc hInnB hT

end Main

end CFSG.LocalAnalysis.GLTheoremA.T266

end
