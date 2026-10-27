module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieAction
public import CFSG.LocalAnalysis.GLTheoremA.S6.Prop61
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieRank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Parts
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

variable {Y : Type} [Group Y] [Finite Y]

theorem onLie_k3Lie_le_k3NoA10 {i : TauCeti.CFSGIndex} (h : onLie k3Lie i) : k3NoA10 i := by
  cases i with
  | cyclic p hp => exact h.elim
  | alternating n hn => exact h.elim
  | lie d => simpa [onLie, k3NoA10] using h
  | sporadic s => exact h.elim

theorem catalogIs_pSimple_k3NoA10 {K : Subgroup Y} (hcore : GLAPPrimeCore 3 ↥K = ⊥)
    (hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie k3Lie)) :
    catalogIs (PSimple 3 K) k3NoA10 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  exact ⟨i, onLie_k3Lie_le_k3NoA10 hi,
    ⟨(CFSG.LocalAnalysis.GLTheoremA.pSimpleEquiv hcore).trans e⟩⟩

theorem inf_centralizer_eq_self_of_le_centralizer {K A : Subgroup Y}
    (hA : A ≤ Subgroup.centralizer (K : Set Y)) :
    K ⊓ Subgroup.centralizer (A : Set Y) = K := by
  rw [inf_eq_left]
  exact (Subgroup.le_centralizer_iff).mpr hA

private theorem sup_zpowers_facts {B A : Subgroup Y} {b : Y} (hB : IsElemAbelian 3 B)
    (hAB : A ≤ B) (hb : b ∈ B) (hbA : b ∉ A) (hAcard : Nat.card ↥A = 9) :
    A ⊔ Subgroup.zpowers b ≤ B ∧ IsElemAbelian 3 (A ⊔ Subgroup.zpowers b) ∧
      Nat.card ↥(A ⊔ Subgroup.zpowers b) = 3 ^ 3 := by
  have hcomm : ∀ x ∈ A, x * b = b * x := fun x hx =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hAB hx⟩ ⟨b, hb⟩)
  refine ⟨sup_le hAB (Subgroup.zpowers_le.2 hb),
    KD1426Common.isElemAbelian_of_le (sup_le hAB (Subgroup.zpowers_le.2 hb)) hB, ?_⟩
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.card_sup_zpowers_of_pow_three_eq_one
    (hB.2 b hb) hbA hcomm, hAcard]
  norm_num

private theorem card_of_relIndex_eq {A B : Subgroup Y} (hAB : A ≤ B)
    (hA : Nat.card ↥A = 9) (hrel : A.relIndex B = 9) : Nat.card ↥B = 81 := by
  have hmul := Subgroup.relIndex_mul_card A B
  rw [inf_eq_left.mpr hAB, hA, hrel] at hmul
  omega

theorem kd1426Lie_of_facts (hF : L3AutFourFacts) (hL : L3AutFieldFacts) : KD1426Lie := by
  intro Y _ _ K B hKn hq hcat hcore hlev hB hKB hcard hmax hC hH hM
  classical
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hCdef
  have hBN : B ≤ Subgroup.normalizer (K : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hKn]
    exact le_top
  have hCel : IsElemAbelian 3 C := KD1426Common.isElemAbelian_of_le inf_le_left hB
  have hCcard9 : Nat.card ↥C ≤ 9 := card_inf_centralizer_le_nine hq hcore hB hH
  have hCne : C ≠ ⊥ := hC
  have hC3 : IsPGroup 3 C := hCel.isPGroup
  obtain ⟨k, hk⟩ := hC3.exists_card_eq
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · exfalso
      apply hCne
      rw [h0] at hk
      simp at hk
      exact Subgroup.eq_bot_of_card_eq C (by simpa using hk)
    · exact h
  have hkle : k ≤ 2 := by
    have hle : 3 ^ k ≤ 9 := by rw [← hk]; exact hCcard9
    by_contra hk2
    have h3 : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h3
    omega
  rcases (by omega : k = 1 ∨ k = 2) with hk1 | hk2
  ·
    have hCcard3 : Nat.card ↥C = 3 := by rw [hk, hk1]; norm_num
    have hrel27 : 27 ≤ C.relIndex B := by
      have hmul := Subgroup.relIndex_mul_card C B
      have hinf : C ⊓ B = C := inf_eq_left.mpr inf_le_left
      rw [hinf, hCcard3] at hmul
      omega
    obtain ⟨b, hbB, hbnot, hcompJ, hJq, hcoreJ, hcatJ⟩ :=
      field_of_facts hL hq hcore hcat hB hBN hrel27
    set A : Subgroup Y := C ⊔ Subgroup.zpowers b with hAdef
    set J : Subgroup Y := GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) with hJdef
    have hAB : A ≤ B := sup_le inf_le_left (Subgroup.zpowers_le.2 hbB)
    have hAel : IsElemAbelian 3 A := KD1426Common.isElemAbelian_of_le hAB hB
    have hAcard : Nat.card ↥A = 9 := by
      have hbC : b ∉ C := fun hx => hbnot ((inf_le_right : C ≤ Subgroup.centralizer (K : Set Y)) hx)
      have hcomm : ∀ x ∈ C, x * b = b * x := fun x hx =>
        congrArg Subtype.val (hB.1.is_comm.comm ⟨x, (inf_le_left : C ≤ B) hx⟩ ⟨b, hbB⟩)
      rw [hAdef, CFSG.HardMathSupport.Solomon.LocalBalance.card_sup_zpowers_of_pow_three_eq_one
        (hB.2 b hbB) hbC hcomm, hCcard3]
    have hcentA : Subgroup.centralizer (A : Set Y) =
        Subgroup.centralizer (C : Set Y) ⊓ Subgroup.centralizer ({(b : Y)} : Set Y) := by
      rw [hAdef, centralizer_sup_zpowers_eq]
    have hfixA : K ⊓ Subgroup.centralizer (A : Set Y) =
        K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y) := by
      rw [hcentA, ← inf_assoc,
        inf_centralizer_eq_self_of_le_centralizer (A := C) inf_le_right]
    have hJcompA : GLAPComponent 3 (K ⊓ Subgroup.centralizer (A : Set Y))
        (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) := by
      rw [hfixA]
      exact hcompJ
    have huniqJ : ∀ K' : Subgroup Y,
        GLAPComponent 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) K' → K' = J :=
      fun K' hK' => glaPComponent_eq_of_glaPLayer hcompJ rfl hK'
    have hJnormA : (J.subgroupOf (K ⊓ Subgroup.centralizer (A : Set Y))).Normal := by
      rw [hfixA]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hcompJ.1).2
        (le_normalizer_of_unique_glaPComponent hcompJ huniqJ)
    have hJK : J ≤ K := by
      rw [hJdef]
      unfold GLAPLayer
      exact sSup_le fun L hL => hL.1.trans inf_le_left
    have hJcentA : J ≤ Subgroup.centralizer (A : Set Y) := by
      have hCcentJ : C ≤ Subgroup.centralizer (J : Set Y) := by
        intro c hc
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hxK : x ∈ K := hJK hx
        have hcK : c ∈ Subgroup.centralizer (K : Set Y) :=
          (inf_le_right : C ≤ Subgroup.centralizer (K : Set Y)) hc
        exact Subgroup.mem_centralizer_iff.1 hcK x hxK
      have hbcentJ : b ∈ Subgroup.centralizer (J : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hJle : J ≤ K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y) := by
          rw [hJdef]
          exact hcompJ.1
        have hxinf : x ∈ K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y) := hJle hx
        exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hxinf).2 b rfl).symm
      rw [hcentA]
      have hcentZ : Subgroup.centralizer (Subgroup.zpowers b : Set Y) =
          Subgroup.centralizer ({(b : Y)} : Set Y) :=
        CFSG.centralizer_zpowers_eq_centralizer_singleton b
      refine le_inf ((Subgroup.le_centralizer_iff).mp hCcentJ) ?_
      rw [← hcentZ]
      exact (Subgroup.le_centralizer_iff).mp (Subgroup.zpowers_le.2 hbcentJ)
    have hBJ : B ≤ Subgroup.normalizer (J : Set Y) := by
      have hstep : ∀ b'' ∈ B, ∀ x ∈ K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y),
          b'' * x * b''⁻¹ ∈ K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y) := by
        intro b'' hb'' x hx
        obtain ⟨hxK, hxCb⟩ := Subgroup.mem_inf.1 hx
        refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hBN hb'') x).1 hxK, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        have hbb' : b * b'' = b'' * b :=
          congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hbB⟩ ⟨b'', hb''⟩)
        have hbx : b * x = x * b := Subgroup.mem_centralizer_iff.1 hxCb b rfl
        have hcomm : Commute b b'' := hbb'
        calc b * (b'' * x * b''⁻¹) = (b * b'') * x * b''⁻¹ := by group
          _ = (b'' * b) * x * b''⁻¹ := by rw [hbb']
          _ = b'' * (b * x) * b''⁻¹ := by group
          _ = b'' * (x * b) * b''⁻¹ := by rw [hbx]
          _ = (b'' * x) * (b * b''⁻¹) := by group
          _ = (b'' * x) * (b''⁻¹ * b) := by rw [hcomm.inv_right.eq]
          _ = (b'' * x * b''⁻¹) * b := by group
      have hBinf : B ≤ Subgroup.normalizer
          (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y) : Set Y) := by
        intro b'' hb''
        change b'' ∈ Subgroup.normalizer
          ((K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y) : Subgroup Y) : Set Y)
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · exact hstep b'' hb'' x
        · intro hx
          have h := hstep b''⁻¹ (B.inv_mem hb'') (b'' * x * b''⁻¹) hx
          simpa [mul_assoc] using h
      intro b' hb'
      exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.mem_normalizer_glaPLayer
        (hBinf hb')
    have hcentBJ : ∀ b' ∈ B, b' ∈ Subgroup.centralizer (J : Set Y) ↔ b' ∈ A := by
      intro b' hb'
      constructor
      · intro hb'J
        by_contra hb'A
        have hb'1 : b' ≠ 1 := by
          intro h1
          exact hb'A (h1 ▸ A.one_mem)
        set E : Subgroup Y := A ⊔ Subgroup.zpowers b' with hEdef
        obtain ⟨hEB, hEel, hEcard⟩ := sup_zpowers_facts hB hAB hb' hb'A hAcard
        have hJcentE : J ≤ Subgroup.centralizer (E : Set Y) := by
          have hcentE : Subgroup.centralizer (E : Set Y) =
              Subgroup.centralizer (A : Set Y) ⊓
                Subgroup.centralizer ({(b' : Y)} : Set Y) := by
            rw [hEdef, centralizer_sup_zpowers_eq]
          rw [hcentE]
          have hcentZ : Subgroup.centralizer (Subgroup.zpowers b' : Set Y) =
              Subgroup.centralizer ({(b' : Y)} : Set Y) :=
            CFSG.centralizer_zpowers_eq_centralizer_singleton b'
          refine le_inf hJcentA ?_
          rw [← hcentZ]
          exact (Subgroup.le_centralizer_iff).mp (Subgroup.zpowers_le.2 hb'J)
        have hJleE : J ≤ K ⊓ Subgroup.centralizer (E : Set Y) :=
          le_inf hJK hJcentE
        have hHA : K ⊓ Subgroup.centralizer (E : Set Y) ≤
            K ⊓ Subgroup.centralizer (A : Set Y) := by
          exact inf_le_inf (le_refl K)
            (Subgroup.centralizer_le (show (A : Set Y) ⊆ E from fun x hx =>
              Subgroup.mem_sup_left hx))
        have hJcompA' : GLAPComponent 3 (K ⊓ Subgroup.centralizer (A : Set Y)) J := by
          have h := hJcompA
          rw [show GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) =
              GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) from
            congrArg (GLAPLayer 3) hfixA] at h
          exact h
        have hcompE : GLAPComponent 3 (K ⊓ Subgroup.centralizer (E : Set Y)) J :=
          CFSG.LocalAnalysis.GLTheoremB.glaPComponent_of_le
            (A := K ⊓ Subgroup.centralizer (A : Set Y))
            (H := K ⊓ Subgroup.centralizer (E : Set Y)) (K := J)
            Nat.prime_three hJcompA' hJleE hHA
        have hbot := hH E hEB hEel hEcard
        have hle : J ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set Y)) := by
          unfold GLAPLayer
          exact le_sSup (s := {L | GLAPComponent 3 (K ⊓ Subgroup.centralizer (E : Set Y)) L}) hcompE
        rw [hbot] at hle
        exact glaPComponent_ne_bot' hcompJ (le_bot_iff.1 hle)
      · intro hb'A
        exact (Subgroup.le_centralizer_iff).mp hJcentA hb'A
    have hcentBJ_eq : B ⊓ Subgroup.centralizer (J : Set Y) = A := by
      apply le_antisymm
      · intro x hx
        exact (hcentBJ x (Subgroup.mem_inf.1 hx).1).1 (Subgroup.mem_inf.1 hx).2
      · intro x hx
        exact Subgroup.mem_inf.2 ⟨hAB hx, (hcentBJ x (hAB hx)).2 hx⟩
    have hJel : IsElemAbelian 3 (B ⊓ Subgroup.centralizer (J : Set Y)) :=
      KD1426Common.isElemAbelian_of_le inf_le_left hB
    have hlayJ : ∀ b' ∈ B, b' ∉ Subgroup.centralizer (J : Set Y) →
        GLAPLayer 3 (J ⊓ Subgroup.centralizer ({(b' : Y)} : Set Y)) = ⊥ := by
      intro b' hb' hb'not
      by_contra hne
      obtain ⟨J₁, hJ₁⟩ := exists_glaPComponent_of_layer_ne_bot hne
      have hb'A : b' ∉ A := fun hx => hb'not ((hcentBJ b' hb').2 hx)
      set E : Subgroup Y := A ⊔ Subgroup.zpowers b' with hEdef
      obtain ⟨hEB, hEel, hEcard⟩ := sup_zpowers_facts hB hAB hb' hb'A hAcard
      have hcentE : Subgroup.centralizer (E : Set Y) =
          Subgroup.centralizer (A : Set Y) ⊓
            Subgroup.centralizer ({(b' : Y)} : Set Y) := by
        rw [hEdef, centralizer_sup_zpowers_eq]
      have hJE : J ⊓ Subgroup.centralizer ({(b' : Y)} : Set Y) =
          J ⊓ Subgroup.centralizer (E : Set Y) := by
        rw [hcentE, ← inf_assoc, inf_eq_left.mpr hJcentA]
      have hJ₁' : GLAPComponent 3 (J ⊓ Subgroup.centralizer (E : Set Y)) J₁ := by
        rwa [← hJE]
      have hJnormE : ((J ⊓ Subgroup.centralizer (E : Set Y)).subgroupOf
          (K ⊓ Subgroup.centralizer (E : Set Y))).Normal := by
        refine (Subgroup.normal_subgroupOf_iff_le_normalizer
          (show J ⊓ Subgroup.centralizer (E : Set Y) ≤
            K ⊓ Subgroup.centralizer (E : Set Y) from
              inf_le_inf hJK le_rfl)).2 ?_
        have hXA : K ⊓ Subgroup.centralizer (E : Set Y) ≤
            K ⊓ Subgroup.centralizer (A : Set Y) := by
          exact inf_le_inf (le_refl K)
            (Subgroup.centralizer_le (show (A : Set Y) ⊆ E from fun x hx =>
              Subgroup.mem_sup_left hx))
        have hJnormA' : (J.subgroupOf (K ⊓ Subgroup.centralizer
            ({(b : Y)} : Set Y))).Normal := by
          rw [← hfixA]
          exact hJnormA
        have hJleA : J ≤ K ⊓ Subgroup.centralizer (A : Set Y) := by
          rw [hJdef, hfixA]
          exact hcompJ.1
        have hNJ : K ⊓ Subgroup.centralizer (A : Set Y) ≤
            Subgroup.normalizer (J : Set Y) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hJleA).1 hJnormA
        intro x hx
        have hxE : x ∈ Subgroup.centralizer (E : Set Y) := (Subgroup.mem_inf.1 hx).2
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          obtain ⟨hyJ, hyE⟩ := Subgroup.mem_inf.1 hy
          refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hNJ (hXA hx)) y).1 hyJ, ?_⟩
          exact (Subgroup.centralizer (E : Set Y)).mul_mem
            ((Subgroup.centralizer (E : Set Y)).mul_mem hxE hyE)
            ((Subgroup.centralizer (E : Set Y)).inv_mem hxE)
        · intro hy
          obtain ⟨hyJ, hyE⟩ := Subgroup.mem_inf.1 hy
          have hmem : x⁻¹ * (x * y * x⁻¹) * x ∈ Subgroup.centralizer (E : Set Y) := by
            have h1 : x⁻¹ ∈ Subgroup.centralizer (E : Set Y) :=
              (Subgroup.centralizer (E : Set Y)).inv_mem hxE
            have h2 : x⁻¹ * (x * y * x⁻¹) ∈ Subgroup.centralizer (E : Set Y) :=
              (Subgroup.centralizer (E : Set Y)).mul_mem h1 hyE
            have h3 : (x⁻¹ * (x * y * x⁻¹)) * x ∈ Subgroup.centralizer (E : Set Y) :=
              (Subgroup.centralizer (E : Set Y)).mul_mem h2 hxE
            simpa [mul_assoc] using h3
          refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hNJ (hXA hx)) y).2 hyJ, ?_⟩
          rwa [show x⁻¹ * (x * y * x⁻¹) * x = y from by group] at hmem
      have hcompBig : GLAPComponent 3 (K ⊓ Subgroup.centralizer (E : Set Y)) J₁ :=
        CFSG.HardMathSupport.Solomon.Proving.glaPComponent_of_normal_overgroup
          (X := J ⊓ Subgroup.centralizer (E : Set Y))
          (N := K ⊓ Subgroup.centralizer (E : Set Y)) (L := J₁)
          Nat.prime_three (show J ⊓ Subgroup.centralizer (E : Set Y) ≤
            K ⊓ Subgroup.centralizer (E : Set Y) from inf_le_inf hJK le_rfl)
          hJnormE hJ₁'
      have hle : J₁ ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set Y)) := by
        unfold GLAPLayer
        exact le_sSup hcompBig
      rw [hH E hEB hEel hEcard] at hle
      exact glaPComponent_ne_bot' hJ₁ (le_bot_iff.1 hle)
    have hguard := four_of_facts hF hJq hcoreJ hcatJ hB hBJ hlayJ
    have hrelJ : (B ⊓ Subgroup.centralizer (J : Set Y)).relIndex B ≤ 9 := hguard.1
    have hrelA : A.relIndex B ≤ 9 := by rwa [hcentBJ_eq] at hrelJ
    have hrelA9 : A.relIndex B = 9 := by
      have hmul := Subgroup.relIndex_mul_card A B
      rw [inf_eq_left.mpr hAB, hAcard] at hmul
      refine le_antisymm hrelA ?_
      have h81 : 81 ≤ A.relIndex B * 9 := by rw [hmul]; exact hcard
      omega
    have hBcard81 : Nat.card ↥B = 81 := card_of_relIndex_eq hAB hAcard hrelA9
    obtain ⟨-, hT⟩ := hguard
    have hrel9 : (B ⊓ Subgroup.centralizer (J : Set Y)).relIndex B = 9 := by
      rw [hcentBJ_eq]
      have hmul := Subgroup.relIndex_mul_card A B
      have hinf : A ⊓ B = A := inf_eq_left.mpr hAB
      rw [hinf, hAcard] at hmul
      omega
    obtain ⟨T, hTJ, hTel, hTcard, hBT, hcommT⟩ := hT hrel9
    have hLyr : GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) =
        GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) :=
      congrArg (GLAPLayer 3) hfixA
    refine ⟨hBcard81, A, T, hAB, hAel, hAcard, ?_, ?_, ?_, ?_, hTel, hTcard, hBT, hcommT,
      ?_⟩
    · exact hJcompA
    · have hcatA : catalogIs (PSimple 3 (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))))
          k3NoA10 :=
        Eq.mpr (congrArg (fun X => catalogIs (PSimple 3 X) k3NoA10) hLyr)
          (catalogIs_pSimple_k3NoA10 hcoreJ hcatJ)
      exact hcatA
    · intro b' hb'
      rw [hLyr]
      exact hcentBJ b' hb'
    · rw [hLyr]
      exact hTJ
    · rw [hLyr]
      exact hcoreJ
  ·
    have hCcard9' : Nat.card ↥C = 9 := by rw [hk, hk2]; norm_num
    have hCK : C ≤ Subgroup.centralizer (K : Set Y) := inf_le_right
    have hlay : ∀ b ∈ B, b ∉ Subgroup.centralizer (K : Set Y) →
        GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) = ⊥ := by
      intro b hb hbnot
      have hbC : b ∉ C := fun hx => hbnot (hCK hx)
      set E : Subgroup Y := C ⊔ Subgroup.zpowers b with hEdef
      obtain ⟨hEB, hEel, hEcard⟩ := sup_zpowers_facts hB inf_le_left hb hbC hCcard9'
      have hcentE : Subgroup.centralizer (E : Set Y) =
          Subgroup.centralizer (C : Set Y) ⊓
            Subgroup.centralizer ({(b : Y)} : Set Y) := by
        rw [hEdef, centralizer_sup_zpowers_eq]
      have hKC : K ⊓ Subgroup.centralizer (C : Set Y) = K :=
        inf_centralizer_eq_self_of_le_centralizer hCK
      have hfix : K ⊓ Subgroup.centralizer (E : Set Y) =
          K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y) := by
        rw [hcentE, ← inf_assoc, hKC]
      have h := hH E hEB hEel hEcard
      rwa [hfix] at h
    obtain ⟨hrel9, hfour⟩ := four_of_facts hF hq hcore hcat hB hBN hlay
    have hrel9' : C.relIndex B = 9 := by
      have hmul := Subgroup.relIndex_mul_card C B
      rw [inf_eq_left.mpr inf_le_left, hCcard9'] at hmul
      refine le_antisymm hrel9 ?_
      have h81 : 81 ≤ C.relIndex B * 9 := by rw [hmul]; exact hcard
      omega
    have hBcard81 : Nat.card ↥B = 81 := card_of_relIndex_eq inf_le_left hCcard9' hrel9'
    obtain ⟨T, hTK, hTel, hTcard, hBT, hcommT⟩ := hfour hrel9'
    have hlayerC : GLAPLayer 3 (K ⊓ Subgroup.centralizer (C : Set Y)) = K := by
      rw [inf_centralizer_eq_self_of_le_centralizer hCK,
        CFSG.LocalAnalysis.GLTheoremA.KD1426Common.glaPLayer_eq_self hq hcore]
    refine ⟨hBcard81, C, T, inf_le_left, hCel, hCcard9', ?_, ?_, ?_, ?_, hTel, hTcard,
      hBT, hcommT, ?_⟩
    · have hX : K ⊓ Subgroup.centralizer (C : Set Y) = K :=
        inf_centralizer_eq_self_of_le_centralizer hCK
      rw [hX]
      rw [CFSG.LocalAnalysis.GLTheoremA.KD1426Common.glaPLayer_eq_self hq hcore]
      exact CFSG.LocalAnalysis.GLTheoremA.KD1426Common.glaPComponent_self hq hcore
    · exact Eq.mpr (congrArg (fun X => catalogIs (PSimple 3 X) k3NoA10) hlayerC)
        (catalogIs_pSimple_k3NoA10 hcore hcat)
    · intro b hb
      rw [hlayerC]
      exact ⟨fun hbK => Subgroup.mem_inf.2 ⟨hb, hbK⟩, fun hbC => hbC.2⟩
    · rw [hlayerC]
      exact hTK
    · rw [hlayerC]
      exact hcore
end CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

end
