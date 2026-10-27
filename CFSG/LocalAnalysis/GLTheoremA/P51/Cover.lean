module

public import CFSG.LocalAnalysis.GLTheoremA.PComp
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Family
import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710XA1
import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P51

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def cent0 (p : ℕ) (X J : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ X ∧ ∀ j ∈ J, ⁅j, g⁆ ∈ GLAPPrimeCoreOf p X}
  mul_mem' := by
    rintro a b ⟨haX, ha⟩ ⟨hbX, hb⟩
    refine ⟨X.mul_mem haX hbX, fun j hj => ?_⟩
    rw [commutatorElement_mul_right]
    exact Subgroup.mul_mem _ (ha j hj)
      ((Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p X haX) _).1 (hb j hj))
  one_mem' := ⟨X.one_mem, fun j _ => by
    rw [commutatorElement_one_right]
    exact Subgroup.one_mem _⟩
  inv_mem' := by
    rintro a ⟨haX, ha⟩
    refine ⟨X.inv_mem haX, fun j hj => ?_⟩
    rw [commutatorElement_inv_right]
    have := (Subgroup.mem_normalizer_iff.1
      (le_normalizer_glaPPrimeCoreOf p X (X.inv_mem haX)) ⁅j, a⁆⁻¹).1
      (Subgroup.inv_mem _ (ha j hj))
    simpa [inv_inv] using this

private theorem glaPPrimeCoreOf_le_cent0 {p : ℕ} {X J : Subgroup G} (hJX : J ≤ X) :
    GLAPPrimeCoreOf p X ≤ cent0 p X J := by
  intro o ho
  refine ⟨Subgroup.map_subtype_le _ ho, fun j hj => ?_⟩
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _
    ((Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p X (hJX hj)) o).1 ho)
    (Subgroup.inv_mem _ ho)

private theorem le_glaPPrimeCoreOf_of_coprime {p : ℕ} {N K : Subgroup G} (hNK : N ≤ K)
    (hK : K ≤ Subgroup.normalizer (N : Set G)) (hN : Nat.Coprime p (Nat.card N)) :
    N ≤ GLAPPrimeCoreOf p K := by
  have hnorm : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hK
  have hcop : Nat.Coprime p (Nat.card (N.subgroupOf K)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv]
  have h : N.subgroupOf K ≤ GLAPPrimeCore p ↥K := le_sSup ⟨hnorm, hcop⟩
  calc N = (N.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hNK).symm
    _ ≤ GLAPPrimeCoreOf p K := Subgroup.map_mono h

theorem le_sup_of_isMaxInvariant {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X J B D S : Subgroup G} (hJ : GLAPComponent p X J) (hB : IsPGroup p B) (hBX : B ≤ X)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hDB : D ≤ B) (hDJ : D ≤ centModSubgroup p J)
    (hS2 : IsPGroup 2 S) (hSC : S ≤ cent0 p X J) (hBS : B ≤ Subgroup.normalizer (S : Set G))
    (hSmax : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ cent0 p X J →
      B ≤ Subgroup.normalizer (T : Set G) → S ≤ T → T = S) :
    J ≤ (Subgroup.normalizer (S : Set G) ⊓ (J ⊔ GLAPPrimeCoreOf p X) ⊓
      Subgroup.centralizer (D : Set G)) ⊔ GLAPPrimeCoreOf p X := by
  set O := GLAPPrimeCoreOf p X
  have hJX : J ≤ X := hJ.1
  have hOX : O ≤ X := Subgroup.map_subtype_le _
  have hXO : X ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p X
  have hOp : ¬ p ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hp X
  have hSX : S ≤ X := fun s hs => (hSC hs).1
  have hDX : D ≤ X := hDB.trans hBX
  have hOJ : GLAPPrimeCoreOf p J ≤ O := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hJ.2.1]
    exact inf_le_right
  set K := S ⊔ O
  have hKC : K ≤ cent0 p X J := sup_le hSC (glaPPrimeCoreOf_le_cent0 hJX)
  have hpS : ¬ p ∣ Nat.card S := by
    obtain ⟨n, hn⟩ := hS2.exists_card_eq
    rw [hn]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hKp : ¬ p ∣ Nat.card K := by
    have := not_dvd_card_sup_of_le_normalizer hp (A := O) (B := S) (hSX.trans hXO) hOp hpS
    rwa [sup_comm] at this
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_sup S O ⟨hBS hb, hXO (hBX hb)⟩
  have hrel : ¬ 2 ∣ S.relIndex K := by
    open CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710 in
    obtain ⟨Q, hSQ, hQK, hQ2, hQi, hBQ⟩ := exists_invariant_sylow_containing_of_pGroup hp
      Nat.prime_two hB hBK hKp le_sup_left hS2 hBS
    have hQS : Q = S := hSmax Q hQ2 (hQK.trans hKC) hBQ hSQ
    rwa [hQS] at hQi
  have hconj : ∀ j ∈ J, ∀ h ∈ K, j * h * j⁻¹ ∈ K := by
    intro j hj h hh
    have hh' : h ∈ ((S ⊔ O : Subgroup G) : Set G) := hh
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S O (hSX.trans hXO)] at hh'
    obtain ⟨s, hs, o, ho, rfl⟩ := Set.mem_mul.mp hh'
    have h1 : j * (s * o) * j⁻¹ = (⁅j, s⁆ * s) * (j * o * j⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h1]
    refine K.mul_mem (K.mul_mem ?_ (Subgroup.mem_sup_left hs)) ?_
    · exact Subgroup.mem_sup_right ((hSC hs).2 j hj)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hXO (hJX hj)) o).1 ho)
  have hJK : J ≤ Subgroup.normalizer (K : Set G) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hconj j hj h, fun hh => ?_⟩
    have h1 := hconj j⁻¹ (J.inv_mem hj) _ hh
    have e : j⁻¹ * (j * h * j⁻¹) * j⁻¹⁻¹ = h := by group
    rwa [e] at h1
  have hfr : ∀ j ∈ J, ∃ t ∈ K, t * j ∈ Subgroup.normalizer (S : Set G) := by
    intro j hj
    let P : Sylow 2 ↥K := (hS2.comap_subtype (K := K)).toSylow hrel
    obtain ⟨x, hx, hxj⟩ := CFSG.RankThree.PartTwo.Sec6.exists_inv_mul_mem_normalizer_sylow P
      (hJK hj)
    have hPS : ((P : Subgroup K).map K.subtype : Subgroup G) = S :=
      Subgroup.map_subgroupOf_eq_of_le le_sup_left
    rw [hPS] at hxj
    exact ⟨x⁻¹, K.inv_mem hx, hxj⟩
  set NS := Subgroup.normalizer (S : Set G)
  set N := NS ⊓ O with hN
  have hDNS : D ≤ NS := fun d hd => hBS (hDB hd)
  have hDN : D ≤ Subgroup.normalizer (N : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer (hDNS hd)) h)
    have h2 := (Subgroup.mem_normalizer_iff.1 (hXO (hDX hd)) h)
    simp only [hN, Subgroup.mem_inf]
    rw [h1, h2]
  have hNp : ¬ p ∣ Nat.card N := fun h => hOp (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  intro j hj
  obtain ⟨t, htK, htj⟩ := hfr j hj
  have htK' : t ∈ ((S ⊔ O : Subgroup G) : Set G) := htK
  rw [Subgroup.coe_mul_of_left_le_normalizer_right S O (hSX.trans hXO)] at htK'
  obtain ⟨s, hs, o, ho, rfl⟩ := Set.mem_mul.mp htK'
  have hn : o * j ∈ NS := by
    have h1 : s⁻¹ * (s * o * j) ∈ NS :=
      NS.mul_mem (NS.inv_mem (Subgroup.le_normalizer hs)) htj
    have e : s⁻¹ * (s * o * j) = o * j := by group
    rwa [e] at h1
  have hnJO : o * j ∈ J ⊔ O := Subgroup.mul_mem _ (Subgroup.mem_sup_right ho)
    (Subgroup.mem_sup_left hj)
  have hy : ∀ d ∈ D, (o * j)⁻¹ * (d * (o * j) * d⁻¹) ∈ N := by
    intro d hd
    refine ⟨NS.mul_mem (NS.inv_mem hn) (NS.mul_mem (NS.mul_mem (hDNS hd) hn)
      (NS.inv_mem (hDNS hd))), ?_⟩
    have hdO : d * o * d⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hXO (hDX hd)) o).1 ho
    have hz : o⁻¹ * (d * o * d⁻¹) ∈ O := O.mul_mem (O.inv_mem ho) hdO
    have hz' : j⁻¹ * (o⁻¹ * (d * o * d⁻¹)) * j ∈ O := by
      have := (Subgroup.mem_normalizer_iff.1 (hXO (X.inv_mem (hJX hj))) _).1 hz
      rwa [inv_inv] at this
    have hc : ⁅j⁻¹, d⁆ ∈ O := hOJ ((hDJ hd).2 j⁻¹ (J.inv_mem hj))
    have e : (o * j)⁻¹ * (d * (o * j) * d⁻¹) =
        (j⁻¹ * (o⁻¹ * (d * o * d⁻¹)) * j) * ⁅j⁻¹, d⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact O.mul_mem hz' hc
  obtain ⟨m, hmN, hnm⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.exists_fixed_mem_coset hp
      (hB.to_le hDB) hDN hNp hy
  have hmO : m ∈ O := hmN.2
  have hn'X : o * j * m ∈ X := X.mul_mem (X.mul_mem (hOX ho) (hJX hj)) (hOX hmO)
  have hn'H : o * j * m ∈ NS ⊓ (J ⊔ O) ⊓ Subgroup.centralizer (D : Set G) :=
    ⟨⟨NS.mul_mem hn hmN.1, Subgroup.mul_mem _ hnJO (Subgroup.mem_sup_right hmO)⟩, hnm⟩
  have hz : o⁻¹ * (o * j * m * m⁻¹ * (o * j * m)⁻¹) ∈ O :=
    O.mul_mem (O.inv_mem ho)
      ((Subgroup.mem_normalizer_iff.1 (hXO hn'X) m⁻¹).1 (O.inv_mem hmO))
  have e : j = (o⁻¹ * (o * j * m * m⁻¹ * (o * j * m)⁻¹)) * (o * j * m) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left hn'H)

theorem glaPLayer_cover {p : ℕ} (hp : p.Prime) {X J Y : Subgroup G}
    (hJ : GLAPComponent p X J) (hYJ : Y ≤ J ⊔ GLAPPrimeCoreOf p X)
    (hJY : J ≤ Y ⊔ GLAPPrimeCoreOf p X) :
    GLAPComponent p Y (GLAPLayer p Y) ∧ GLAPLayer p Y ≤ J ∧
      GLAPLayer p Y ⊔ GLAPPrimeCoreOf p J = J := by
  set O := GLAPPrimeCoreOf p X
  have hJX : J ≤ X := hJ.1
  have hOX : O ≤ X := Subgroup.map_subtype_le _
  have hXO : X ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p X
  have hOJ : O ≤ Subgroup.normalizer (J : Set G) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPPrimeCoreOf_le_normalizer hJ
  have hOcop : p.Coprime (Nat.card O) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp X
  set K := J ⊔ O
  have hKX : K ≤ X := sup_le hJX hOX
  have hJK : J ≤ K := le_sup_left
  have hOK : O ≤ GLAPPrimeCoreOf p K :=
    le_glaPPrimeCoreOf_of_coprime le_sup_right (hKX.trans hXO) hOcop
  have hOKK : GLAPPrimeCoreOf p K ≤ K := Subgroup.map_subtype_le _
  have hYK : Y ≤ K := hYJ
  have hsupJ : J ⊔ GLAPPrimeCoreOf p K = K :=
    le_antisymm (sup_le hJK hOKK) (sup_le le_sup_left (hOK.trans le_sup_right))
  have hsupY : Y ⊔ GLAPPrimeCoreOf p K = K :=
    le_antisymm (sup_le hYK hOKK)
      (sup_le (hJY.trans (sup_le le_sup_left (hOK.trans le_sup_right))) (hOK.trans le_sup_right))
  obtain ⟨-, ⟨e₁⟩⟩ := cover_facts hp hJK hsupJ
  obtain ⟨hOY, ⟨e₂⟩⟩ := cover_facts hp hYK hsupY
  have hYq : CFSG.Open.IsQuasisimple (PQuot p Y) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv (e₁.trans e₂.symm)
      (isQuasisimple_pQuot_of_glaPComponent hp hJ)
  obtain ⟨hLc, -, hbar⟩ := glaPLayer_of_isQuasisimple hYq
  have hLY : GLAPLayer p Y ≤ Y := hLc.1
  have hsupLY : GLAPLayer p Y ⊔ GLAPPrimeCoreOf p Y = Y :=
    sup_glaPPrimeCoreOf_eq_of_barX_eq_top hLY hbar
  have hLJ : GLAPLayer p Y ≤ J :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_le_of_le_sup hp hLc hOcop hOJ (hLY.trans hYJ)
  refine ⟨hLc, hLJ, le_antisymm (sup_le hLJ (Subgroup.map_subtype_le _)) ?_⟩
  have hJL : J ≤ GLAPLayer p Y ⊔ GLAPPrimeCoreOf p K := by
    calc J ≤ Y ⊔ O := hJY
      _ ≤ (GLAPLayer p Y ⊔ GLAPPrimeCoreOf p Y) ⊔ O := by rw [hsupLY]
      _ ≤ GLAPLayer p Y ⊔ GLAPPrimeCoreOf p K := by
        refine sup_le (sup_le le_sup_left ?_) (hOK.trans le_sup_right)
        rw [hOY]
        exact inf_le_right.trans le_sup_right
  have hLN : GLAPLayer p Y ≤ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) :=
    hLJ.trans (hJK.trans (le_normalizer_glaPPrimeCoreOf p K))
  have hJN : J ≤ Subgroup.normalizer ((J ⊓ GLAPPrimeCoreOf p K : Subgroup G) : Set G) :=
    fun j hj => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hj, le_normalizer_glaPPrimeCoreOf p K (hJK hj)⟩
  have hJOK : J ⊓ GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p J :=
    le_glaPPrimeCoreOf_of_coprime inf_le_left hJN
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        (CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp K))
  intro j hj
  have hj' : j ∈ ((GLAPLayer p Y ⊔ GLAPPrimeCoreOf p K : Subgroup G) : Set G) := hJL hj
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLN] at hj'
  obtain ⟨l, hl, o, ho, rfl⟩ := Set.mem_mul.mp hj'
  have hoJ : o ∈ J := by
    have := J.mul_mem (J.inv_mem (hLJ hl)) hj
    rwa [inv_mul_cancel_left] at this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right (hJOK ⟨hoJ, ho⟩))

end CFSG.LocalAnalysis.GLTheoremA.P51
