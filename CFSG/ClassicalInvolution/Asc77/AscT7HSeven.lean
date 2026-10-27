module

public import CFSG.ClassicalInvolution.Asc77.AscT7DRS
import CFSG.ClassicalInvolution.Asc77.AscIHSectMA
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped MatrixGroups commutatorElement

namespace T7H

section Algebra

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ B ⊔ A) :
    ∃ b ∈ B, ∃ a ∈ A, x = b * a := by
  have hconj : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A := fun b hb a ha =>
    (Subgroup.mem_normalizer_iff.mp (hB hb) a).mp ha
  have hconj' : ∀ b ∈ B, ∀ a ∈ A, b⁻¹ * a * b ∈ A := fun b hb a ha => by
    have := hconj b⁻¹ (B.inv_mem hb) a ha
    simpa using this
  let S : Subgroup G :=
    { carrier := {x | ∃ b ∈ B, ∃ a ∈ A, x = b * a}
      one_mem' := ⟨1, B.one_mem, 1, A.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, a, ha, rfl⟩ ⟨b', hb', a', ha', rfl⟩
        refine ⟨b * b', B.mul_mem hb hb', (b'⁻¹ * a * b') * a', A.mul_mem (hconj' b' hb' a ha) ha',
          ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨b, hb, a, ha, rfl⟩
        refine ⟨b⁻¹, B.inv_mem hb, b * a⁻¹ * b⁻¹, ?_, by group⟩
        exact hconj b hb a⁻¹ (A.inv_mem ha) }
  have hBS : B ≤ S := fun b hb => ⟨b, hb, 1, A.one_mem, by simp⟩
  have hAS : A ≤ S := fun a ha => ⟨1, B.one_mem, a, ha, by simp⟩
  exact (sup_le hBS hAS) hx

theorem exists_pow_mem_of_mem_sup {A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G))
    (hB2 : IsPGroup 2 B) {x : G} (hx : x ∈ B ⊔ A) : ∃ n : ℕ, x ^ (2 ^ n) ∈ A := by
  obtain ⟨b, hb, a, ha, rfl⟩ := exists_mul_of_mem_sup_normalizer hB hx
  obtain ⟨k, hk⟩ := hB2 ⟨b, hb⟩
  have hbk : b ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hconj' : ∀ a ∈ A, b⁻¹ * a * b ∈ A := fun a ha => by
    have := (Subgroup.mem_normalizer_iff.mp (hB hb) a).mp ha
    have h2 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (A : Set G)).inv_mem (hB hb))
      a).mp ha
    simpa using h2
  have key : ∀ m : ℕ, ∃ a' ∈ A, (b * a) ^ m = b ^ m * a' := by
    intro m
    induction m with
    | zero => exact ⟨1, A.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨a', ha', h⟩ := ih
      refine ⟨(b⁻¹ * a' * b) * a, A.mul_mem (hconj' a' ha') ha, ?_⟩
      rw [pow_succ, h]
      group
  obtain ⟨a', ha', h⟩ := key (2 ^ k)
  exact ⟨k, by rw [h, hbk, one_mul]; exact ha'⟩

end Algebra

section Main

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_sup' {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hA hB ⊢
  unfold conjSub at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

omit [Finite G] in
theorem mem_normalizer_inf' {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hA hB ⊢
  unfold conjSub at hA hB ⊢
  rw [Subgroup.map_inf_eq _ _ (MulAut.conj x).toMonoidHom (MulAut.conj x).injective, hA, hB]

theorem not_rLayer_le_oddCore_sup_normalizer
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) (hW : W ∈ WSet Ω)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {R : Subgroup G} (hRK : IsSylow2In R K) (hRD : R ∈ DSet Ω W)
    {e : G} (he2 : e * e = 1)
    (hec : ∀ x ∈ Subgroup.normalizer (W : Set G), e * x = x * e) :
    ¬ rLayer Ω e ≤ oddCoreOf (rLayer Ω e) ⊔ (rLayer Ω e ⊓ Subgroup.normalizer (W : Set G)) := by
  intro hle
  set E := rLayer Ω e with hE
  set A := oddCoreOf E with hA
  have hcA : IsPGroup 2 (Subgroup.zpowers e) := isPGroup_zpowers_of_sq_eq_one he2
  have hW2 : IsPGroup 2 W := Thompson.isPGroup_of_mem_WSet hW
  have hRc : R ≤ Subgroup.centralizer ({e} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hec r (hRD.2 hr)).symm
  have hKt : K ∈ tqMembers Ω e :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcA).mpr ⟨hK, R, hRK, hRc⟩
  obtain ⟨w, hwRW, hw4⟩ := Thompson.exists_orderOf_four hp hq hΩ hW hRD
  have hKs : K ∈ AscE184Sect.sectionMembers Ω (Subgroup.zpowers e) := by
    rw [sectionMembers_zpowers]; exact hKt
  have hEsec : E = AscE184Sect.sectionHull Ω (Subgroup.zpowers e) :=
    rLayer_eq_sectionHull hp hq hΩ he2
  have hKeE : exactCore e K ≤ E := by
    rw [hEsec, ← secMember_zpowers_eq_exactCore hΩ hcA hK hKt.2]
    exact AscE184Sect.le_sectionHull hKs
  have hRKe : R ≤ exactCore e K :=
    ((isSylow2In_exactCore_iff hΩ hcA hK hKt.2).mpr ⟨hRK, hRc⟩).1
  obtain ⟨z', hz'⟩ := hΩ.classical K hK
  set W₁ : Subgroup G := W ⊓ E with hW₁
  have hW₁2 : IsPGroup 2 W₁ := hW2.to_inf_left
  have hAN : ∀ x ∈ E, x ∈ Subgroup.normalizer (A : Set G) := fun x hx =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hx)
  have hW₁A : W₁ ≤ Subgroup.normalizer (A : Set G) := fun x hx => hAN x hx.2
  set V : Subgroup G := W₁ ⊔ A with hV
  have hEV : E ≤ Subgroup.normalizer (V : Set G) := by
    refine hle.trans (sup_le ?_ ?_)
    · exact (le_sup_right : A ≤ V).trans Subgroup.le_normalizer
    · intro x hx
      refine mem_normalizer_sup' ?_ (hAN x hx.1)
      exact mem_normalizer_inf' hx.2 (Subgroup.le_normalizer hx.1)
  obtain ⟨φ, hφs, hφk⟩ := hΩ.exists_chart hK
  have hcover : ∀ s : SL(2, GaloisField p f), ∃ (i : G) (hi : i ∈ K), i ∈ exactCore e K ∧
      φ ⟨i, hi⟩ = s := by
    intro s
    obtain ⟨x, rfl⟩ := hφs s
    obtain ⟨i, hi, n, hn, hxin⟩ := exactCore_cover hz' hcA hKt.2 (x : G) x.2
    have hiK : i ∈ K := exactCore_le_left e K hi
    have hnK : n ∈ K := oddCoreOf_le_self K hn
    refine ⟨i, hiK, hi, ?_⟩
    have h1 : φ ⟨n, hnK⟩ = 1 := (hφk _).mpr (mem_oddCoreOf_iff.mp hn).2
    have h2 : x = ⟨i, hiK⟩ * ⟨n, hnK⟩ := Subtype.ext hxin
    rw [h2, map_mul, h1, mul_one]
  set Ke := exactCore e K with hKe
  have hKeK : Ke ≤ K := exactCore_le_left e K
  have hQ : Ke ⊓ A ≤ oddCoreOf K := by
    have hnorm : ((Ke ⊓ A).subgroupOf Ke).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      refine ⟨Ke.mul_mem (Ke.mul_mem g.2 hx.1) (Ke.inv_mem g.2), ?_⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (hAN (g : G) (hKeE g.2)) (x : G)).mp hx.2
      simpa using h1
    have hodd : Odd (Nat.card ((Ke ⊓ A).subgroupOf Ke)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Ke ⊓ A ≤ Ke)).toEquiv]
      exact (oddCoreOf_odd_natCard E).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    have hle' := CFSG.DisconnectedInvolutionGraph.Helpers.normal_odd_le_oddCore _ hnorm hodd
    intro x hx
    have hxO : x ∈ Balance.oddCoreIn Ke :=
      ⟨⟨x, hx.1⟩, hle' (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    rw [oddCoreIn_exactCore hz' hcA hKt.2] at hxO
    exact hxO.2
  set P : Subgroup G := Ke ⊓ V with hP
  have hPK : P ≤ K := inf_le_left.trans hKeK
  set N : Subgroup (SL(2, GaloisField p f)) := (P.subgroupOf K).map φ with hN
  have hNnorm : N.Normal := by
    refine ⟨fun n hn s => ?_⟩
    obtain ⟨i, hiK, hiKe, rfl⟩ := hcover s
    obtain ⟨x, hx, rfl⟩ := hn
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
    have hconj : i * (x : G) * i⁻¹ ∈ P := by
      refine ⟨Ke.mul_mem (Ke.mul_mem hiKe hxP.1) (Ke.inv_mem hiKe), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (hEV (hKeE hiKe)) (x : G)).mp hxP.2
    refine ⟨⟨i * (x : G) * i⁻¹, K.mul_mem (K.mul_mem hiK x.2) (K.inv_mem hiK)⟩,
      Subgroup.mem_subgroupOf.mpr hconj, ?_⟩
    have hmul : (⟨i * (x : G) * i⁻¹, K.mul_mem (K.mul_mem hiK x.2) (K.inv_mem hiK)⟩ : ↥K) =
        ⟨i, hiK⟩ * x * ⟨i, hiK⟩⁻¹ := rfl
    rw [hmul, map_mul, map_mul, map_inv]
  have hN2 : IsPGroup 2 N := by
    intro g
    obtain ⟨x, hx, hg⟩ := g.2
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hW₁A hW₁2 hxP.2
    refine ⟨k, Subtype.ext ?_⟩
    have h2 : x ^ (2 ^ k) ∈ classicalInvolutionOddCore ↥K :=
      (mem_oddCoreOf_iff.mp (hQ ⟨Ke.pow_mem hxP.1 _, hk⟩)).2
    have h3 : φ (x ^ (2 ^ k)) = 1 := (hφk _).mpr h2
    rw [map_pow, hg] at h3
    simpa using h3
  have hNc : N ≤ Subgroup.center (SL(2, GaloisField p f)) := by
    have := hNnorm
    have h4 : 4 ≤ Nat.card (GaloisField p f) := by
      have hf : f ≠ 0 := by
        rintro rfl
        simp at hq
      rw [GaloisField.card p f hf]
      omega
    have := comap_le_center_of_normal_pGroup (isQuasisimple_specialLinearGroup_two h4)
      (MonoidHom.id _) (by rw [MonoidHom.ker_id]; exact bot_le) hN2
    simpa using this
  have hwK : w ∈ K := hRK.1 hwRW.1
  have hwP : w ∈ P :=
    ⟨hRKe hwRW.1, (le_sup_left : W₁ ≤ V) ⟨hwRW.2, hKeE (hRKe hwRW.1)⟩⟩
  have hφw : φ ⟨w, hwK⟩ ∈ Subgroup.center (SL(2, GaloisField p f)) :=
    hNc ⟨⟨w, hwK⟩, Subgroup.mem_subgroupOf.mpr hwP, rfl⟩
  have hcomm : ∀ y ∈ K, ⁅w, y⁆ ∈ oddCoreOf K := by
    intro y hy
    have h1 : φ ⁅(⟨w, hwK⟩ : ↥K), ⟨y, hy⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_center_iff.mp hφw (φ ⟨y, hy⟩)).symm)
    exact mem_oddCoreOf_iff.mpr ⟨_, (hφk _).mp h1⟩
  have hw2 : IsPGroup 2 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hw4]; norm_num)
  rcases hΩ.center_two hp hq hK hz w hwK hw2 hcomm with h | h
  · rw [h, orderOf_one] at hw4
    omega
  · rw [h] at hw4
    have : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
    omega

end Main

end T7H

variable {p f : ℕ} [Fact p.Prime]

theorem c23_7_proved : C23_7 p f := by
  intro G _ _ _ Ω K K' W z u e g h
  have hs : Hyp23Setting p f Ω K K' z := h.std.setting
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  obtain ⟨S, R, R', hWS, hR, -, hRS, -⟩ := T7D.exists_sylow_frame hs h.hW h.hzW
  have hRD : R ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ h.hW hWS (mem_RSet_of_isSylow2In hK hR) hRS
  have heW : e ∈ W ⊓ centerIn (Subgroup.normalizer (W : Set G)) := by
    rw [← h.he]
    exact Subgroup.mem_closure_singleton_self e
  have hec : ∀ x ∈ Subgroup.normalizer (W : Set G), e * x = x * e := by
    intro x hx
    obtain ⟨y, hy, hye⟩ := heW.2
    have := Subgroup.mem_center_iff.mp hy ⟨x, hx⟩
    have h2 : (x : G) * (y : G) = (y : G) * (x : G) := congrArg Subtype.val this
    rw [← hye]
    exact h2.symm
  exact T7H.not_rLayer_le_oddCore_sup_normalizer hp hq hΩ h.hW hK hs.hz hR hRD h.he2 hec

end CFSG.ClassicalInvolution.Asc77
