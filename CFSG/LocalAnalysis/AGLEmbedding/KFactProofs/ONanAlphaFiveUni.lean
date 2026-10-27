module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaFiveLin
public import CFSG.ClassicalInvolution.Phan.Standard
public import CFSG.RankThree.PartOne.K159.CoverPSU

public section

namespace CFSG.AGLEmbedding.KFactProofs.AlphaFive

open CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Unitary

variable {ℓ f : ℕ} {F : Type} [Field F]

theorem torusHyp_unitarySU (hU : UnitaryFieldData ℓ f F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) {ζ : Fˣ} (hζ : orderOf ζ = p) {n : ℕ} (hn : 4 ≤ n) :
    TorusHyp (unitarySU ℓ f F n) p ζ where
  prime := hp
  ne_two := hp2
  orderOf_eq := hζ
  four_le := hn
  diag_mem d hd hdp := by
    rw [mem_unitarySU_iff hU]
    refine ⟨?_, diagHom_unitary hU fun i => ?_⟩
    · rw [det_diagHom, ← Units.coe_prod, hd, Units.val_one]
    · obtain ⟨k, hk⟩ := hpq
      rw [← Units.val_pow_eq_pow_val, hk, pow_mul, hdp i, one_pow, Units.val_one]
  sw_mem a c hac := by
    rw [mem_unitarySU_iff hU, sw, Units.val_mul]
    refine ⟨?_, unitary_mul hU (permGL_unitary hU _) (diagHom_unitary hU fun i => ?_)⟩
    · rw [← Units.val_mul]
      exact det_sw hac
    · by_cases hic : i = c
      · subst hic
        rw [Function.update_self, Units.val_neg, Units.val_one]
        exact CFSG.RankThree.PartOne.K159.neg_one_pow_norm hU
      · rw [Function.update_of_ne hic]
        simp

theorem commute_blockEmb2_diagHom [Finite F] [Fact ℓ.Prime] [CharP F ℓ] {m : ℕ} (i : Fin m)
    (C : Su F ℓ f 2) (e : Fin (m + 1) → Fˣ) (he : e i.castSucc = e i.succ) :
    Commute ((blockEmb2 F ℓ f m i C : Su F ℓ f (m + 1)) : GL (Fin (m + 1)) F)
      (diagHom (m + 1) e) := by
  refine Units.ext ?_
  have hmat : (((blockEmb2 F ℓ f m i C : Su F ℓ f (m + 1)) : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      blockMat (m + 1) i.val (((C : Su F ℓ f 2) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
    rfl
  change (((blockEmb2 F ℓ f m i C : Su F ℓ f (m + 1)) : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (diagHom (m + 1) e : Matrix _ _ F) =
    (diagHom (m + 1) e : Matrix _ _ F) * (((blockEmb2 F ℓ f m i C : Su F ℓ f (m + 1)) :
      GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
  rw [coe_diagHom, hmat]
  ext r s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, blockMat_apply]
  by_cases hij : (i.val ≤ r.val ∧ r.val < i.val + 2) ∧ (i.val ≤ s.val ∧ s.val < i.val + 2)
  · rw [dite_eq_left hij]
    have hd : ∀ k : Fin (m + 1), (i.val ≤ k.val ∧ k.val < i.val + 2) → e k = e i.castSucc := by
      intro k hk
      rcases (by omega : k.val = i.val ∨ k.val = i.val + 1) with hk1 | hk1
      · exact congrArg e (Fin.ext (by simpa using hk1))
      · rw [he]
        exact congrArg e (Fin.ext (by simpa using hk1))
    rw [hd r hij.1, hd s hij.2]
    exact mul_comm _ _
  · rw [dite_eq_right hij]
    by_cases hrs : r = s
    · subst hrs
      exact mul_comm _ _
    · simp [Matrix.one_apply_ne hrs]

theorem unitarySU_le_closure (hU : UnitaryFieldData ℓ f F) (hq : ℓ ^ f ≠ 2) {m : ℕ}
    (hm : 4 ≤ m) (ζ : Fˣ) :
    unitarySU ℓ f F (m + 1) ≤ Subgroup.closure {A : GL (Fin (m + 1)) F |
      A ∈ unitarySU ℓ f F (m + 1) ∧ ∃ a b c : Fin (m + 1), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        Commute A (diagHom (m + 1) (dlt ζ a c)) ∧ Commute A (diagHom (m + 1) (dlt ζ b c))} := by
  have : Fact ℓ.Prime := ⟨hU.prime⟩
  have : CharP F ℓ := hU.charP
  have : Finite F := hU.finite
  have hK : Nat.card F = (ℓ ^ f) ^ 2 := by rw [hU.card, ← pow_mul, mul_comm]
  have hS : unitarySU ℓ f F (m + 1) = SUid (unitaryInvolution F ℓ f) (m + 1) :=
    (SUid_eq_statedSU hK (m + 1)).symm
  intro A hA
  have hA' : (⟨A, by rw [← hS]; exact hA⟩ : Su F ℓ f (m + 1)) ∈
      ⨆ i : Fin m, (blockEmb2 F ℓ f m i).range := by
    rw [iSup_range_blockEmb2 hK hq m]
    trivial
  have hmap : A ∈ (⨆ i : Fin m, (blockEmb2 F ℓ f m i).range).map
      (SUid (unitaryInvolution F ℓ f) (m + 1)).subtype := ⟨_, hA', rfl⟩
  rw [Subgroup.map_iSup] at hmap
  refine (iSup_le (fun i => ?_) :
    (⨆ i : Fin m, ((blockEmb2 F ℓ f m i).range).map
      (SUid (unitaryInvolution F ℓ f) (m + 1)).subtype) ≤ _) hmap
  rintro _ ⟨_, ⟨C, rfl⟩, rfl⟩
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [hS]
    exact (blockEmb2 F ℓ f m i C).2
  · obtain ⟨a, b, c, hab, hac, hbc, hai, haj, hbi, hbj, hci, hcj⟩ :=
      exists_three_outside (n := m + 1) (by omega) i.castSucc i.succ
    refine ⟨a, b, c, hab, hac, hbc, ?_, ?_⟩
    · refine commute_blockEmb2_diagHom i C _ ?_
      rw [dlt_apply_other ζ (Ne.symm hai) (Ne.symm hci), dlt_apply_other ζ (Ne.symm haj)
        (Ne.symm hcj)]
    · refine commute_blockEmb2_diagHom i C _ ?_
      rw [dlt_apply_other ζ (Ne.symm hbi) (Ne.symm hci), dlt_apply_other ζ (Ne.symm hbj)
        (Ne.symm hcj)]

theorem glbCore_eq_top_of_statedSU {n : ℕ} (hU : UnitaryFieldData ℓ f F) {K : Type} [Group K]
    [Finite K] (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 5 ≤ n)
    (hpq : p ∣ ℓ ^ f + 1) (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU n (ℓ ^ f) F))
    (hpZ : p ∣ Nat.card (Subgroup.center K)) (T : Sylow p K) :
    Open.GLBCore p 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank p (⊤ : Subgroup K) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨ζ, hζ, -⟩ := exists_orderOf_eq_norm_one hU hp hpq
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) p hpZ
  have hz1 : (z : K) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hzp : (z : K) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have hq : ℓ ^ f ≠ 2 := by
    intro h2
    have := Nat.le_of_dvd (by omega) (h2 ▸ hpq)
    omega
  let φ : K →* StatedProj (StatedSU (m + 1) (ℓ ^ f) F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact glbCore_eq_top_of_torus (torusHyp_unitarySU hU hp (by omega) hpq hζ (by omega)) hφ hker.le
    hperf
    (by rw [hker]; exact z.2) hz1 hzp (unitarySU_le_closure hU hq (by omega) ζ) T

end Unitary

end CFSG.AGLEmbedding.KFactProofs.AlphaFive
