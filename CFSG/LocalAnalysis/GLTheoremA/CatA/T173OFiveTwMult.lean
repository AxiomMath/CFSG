module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMMult
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3317A
import CFSG.LieType.Multipliers.U42

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Assembly CFSG.RankThree.PerfectCover
open CFSG.LocalAnalysis.GLTheoremA.T173


variable {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
  {Γ : Type} [Group Γ] {G₀ Ghat : Subgroup Γ} {F : Type} [Field F] [Finite F]

private theorem scalars_inf_su_two_eq_bot (hF : Nat.card F = 2 ^ 2) {n : ℕ} (hn : 1 ≤ n)
    (hn3 : Nat.Coprime n 3) :
    (LargeEvenScalars (Fin n) F).subgroupOf (LargeEvenSUGroup (Fin n) F 2) = ⊥ := by
  have hF' : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have h := (CFSG.LinearGroups.unitary_scalar_kernel (K := F) (p := 2) (f := 1)
    Nat.prime_two hF' (n := n) hn).2.2
  have hcard : Nat.card ↥((LargeEvenScalars (Fin n) F).subgroupOf
      (LargeEvenSUGroup (Fin n) F (2 ^ 1))) = 1 := by
    rw [largeEvenSUGroup_eq_statedSU, largeEvenScalars_eq_statedScalars, h]
    simpa using hn3
  exact Subgroup.card_eq_one.mp hcard

theorem center_su_two_eq_bot (hF : Nat.card F = 2 ^ 2) {n : ℕ} (hn : 3 ≤ n)
    (hn3 : Nat.Coprime n 3) :
    Subgroup.center ↥(LargeEvenSUGroup (Fin n) F 2) = ⊥ := by
  have hF' : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hnq : (n, 2 ^ 1) ≠ (3, 2) := by
    intro h
    rw [Prod.mk.injEq] at h
    rw [h.1] at hn3
    norm_num at hn3
  have h : Subgroup.center ↥(LargeEvenSUGroup (Fin n) F 2) =
      (LargeEvenScalars (Fin n) F).subgroupOf (LargeEvenSUGroup (Fin n) F 2) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := F) (p := 2) (f := 1)
      hF' (n := n) hn hnq).2
  rw [h]
  exact scalars_inf_su_two_eq_bot hF (by omega) hn3

private noncomputable def suTwoProjEquiv (hF : Nat.card F = 2 ^ 2) {n : ℕ} (hn : 1 ≤ n)
    (hn3 : Nat.Coprime n 3) :
    LargeEvenProj (LargeEvenSUGroup (Fin n) F 2) ≃* LargeEvenSUGroup (Fin n) F 2 :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_inf_su_two_eq_bot hF hn hn3)).trans
    QuotientGroup.quotientBot

private theorem card_griessHopfMultiplier_su5_proj (hF : Nat.card F = 2 ^ 2) :
    Nat.card (griessHopfMultiplier (LargeEvenProj (LargeEvenSUGroup (Fin 5) F 2))) = 1 := by
  have hF' : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  obtain ⟨-, hdvd⟩ := CFSG.LocalAnalysis.GLTheoremA.T173A.uni_hopf_row (d := 5) (n := 1)
    (F := F) hF' (by norm_num) (by norm_num) (by intro h; omega) (by norm_num)
  rw [pow_one] at hdvd
  have hker : Nat.card ↥(LargeEvenProjMk (LargeEvenSUGroup (Fin 5) F 2)).ker = 1 := by
    rw [QuotientGroup.ker_mk']
    exact Subgroup.card_eq_one.mpr (scalars_inf_su_two_eq_bot hF (by norm_num) (by norm_num))
  have h2 : 2 ^ (if (5 : ℕ) = 6 ∧ (1 : ℕ) = 1 then 2 else 0) = 1 := by
    rw [if_neg (by norm_num : ¬ ((5 : ℕ) = 6 ∧ (1 : ℕ) = 1))]
    exact pow_zero 2
  rw [hker, h2, mul_one] at hdvd
  exact Nat.dvd_one.mp hdvd

private theorem card_hopfMultiplier_su5 (hF : Nat.card F = 2 ^ 2) :
    Nat.card ↥(hopfMultiplier (LargeEvenSUGroup (Fin 5) F 2)) = 1 := by
  rw [← CFSG.Quasithin.H13.L3317.card_hopfMultiplier_congr
    (suTwoProjEquiv hF (n := 5) (by norm_num) (by norm_num))]
  rw [← Nat.card_congr
    (hopfMultiplierEquivGriess (LargeEvenProj (LargeEvenSUGroup (Fin 5) F 2))).toEquiv]
  exact card_griessHopfMultiplier_su5_proj hF

private theorem card_griessHopfMultiplier_su4_proj (hF : Nat.card F = 2 ^ 2) :
    Nat.card (griessHopfMultiplier (LargeEvenProj (LargeEvenSUGroup (Fin 4) F 2))) = 2 := by
  have hF' : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hadm : StatedLieAdmissible .PSU 4 2 1 := ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩
  have hm : CFSG.Blueprint.LieModel (LargeEvenProj (LargeEvenSUGroup (Fin 4) F (2 ^ 1)))
      .PSU 4 2 1 :=
    Or.inl ⟨by decide, CFSG.StandardType.statedClassicalModel_unitary (K := F) 4 1 hF' hadm⟩
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two _ hm
  have h2 : Nat.card (griessHopfMultiplier
      (LargeEvenProj (LargeEvenSUGroup (Fin 4) F (2 ^ 1)))) = 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd : _ ≃ ZMod 2),
      Nat.card_zmod]
  exact h2

private theorem card_hopfMultiplier_su4 (hF : Nat.card F = 2 ^ 2) :
    Nat.card ↥(hopfMultiplier (LargeEvenSUGroup (Fin 4) F 2)) = 2 := by
  rw [← CFSG.Quasithin.H13.L3317.card_hopfMultiplier_congr
    (suTwoProjEquiv hF (n := 4) (by norm_num) (by norm_num))]
  rw [← Nat.card_congr
    (hopfMultiplierEquivGriess (LargeEvenProj (LargeEvenSUGroup (Fin 4) F 2))).toEquiv]
  exact card_griessHopfMultiplier_su4_proj hF

private def piRestrict (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S) :
    ↥K →* ↥(M.piImg K) :=
  MonoidHom.codRestrict ((G₀.subtype.comp M.π).comp (Subgroup.inclusion hKS)) (M.piImg K)
    (fun k => Subgroup.mem_map.mpr
      ⟨M.π (Subgroup.inclusion hKS k),
        Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKS k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩,
        rfl⟩)

private theorem piRestrict_surjective (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S) :
    Function.Surjective (piRestrict M hKS) := by
  rintro ⟨y, hy⟩
  obtain ⟨s, hs, hval⟩ := (M.mem_piImg).1 hy
  refine ⟨⟨(s : Ω), hs⟩, Subtype.ext ?_⟩
  show ((M.π (Subgroup.inclusion hKS ⟨(s : Ω), hs⟩) : ↥G₀) : Γ) = y
  rw [show Subgroup.inclusion hKS ⟨(s : Ω), hs⟩ = s from Subtype.ext rfl]
  exact hval

private theorem piRestrict_ker_le_center (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S) :
    (piRestrict M hKS).ker ≤ Subgroup.center ↥K := by
  intro k hk
  have hk1 : ((M.π (Subgroup.inclusion hKS k) : ↥G₀) : Γ) = 1 := congrArg Subtype.val hk
  have hz : Subgroup.inclusion hKS k ∈ Subgroup.center ↥S := by
    rw [← M.ker_π, MonoidHom.mem_ker]
    exact Subtype.ext hk1
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hc := Subgroup.mem_center_iff.1 hz (Subgroup.inclusion hKS y)
  simpa using congrArg Subtype.val hc

private theorem mem_ker_piRestrict (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S) {k : Ω}
    (hkK : k ∈ K) (hkC : k ∈ Subgroup.centralizer (S : Set Ω)) :
    (⟨k, hkK⟩ : ↥K) ∈ (piRestrict M hKS).ker := by
  have hkcen : Subgroup.inclusion hKS ⟨k, hkK⟩ ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 hkC (s : Ω) s.2
  rw [MonoidHom.mem_ker]
  refine Subtype.ext ?_
  show ((G₀.subtype.comp M.π) (Subgroup.inclusion hKS ⟨k, hkK⟩) : Γ) = 1
  have h1 : Subgroup.inclusion hKS ⟨k, hkK⟩ ∈ M.π.ker := by
    rw [M.ker_π]
    exact hkcen
  simpa using congrArg Subtype.val (MonoidHom.mem_ker.1 h1)

private theorem card_ker_piRestrict_dvd (hcfg : Cfg173 3 S B N D K x)
    (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S) (hF : Nat.card F = 2 ^ 2) {n : ℕ} (hn : 3 ≤ n)
    (hn3 : Nat.Coprime n 3)
    (ρ : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2) →* ↥(M.piImg K))
    (hρ : Function.Surjective ρ) (hρk : ρ.ker ≤ Subgroup.center _) :
    Nat.card ↥(piRestrict M hKS).ker ∣
      Nat.card ↥(hopfMultiplier (LargeEvenSUGroup (Fin n) F 2)) := by
  haveI hKperfect : Group.IsPerfect ↥K := ⟨hcfg.std.2.2.2.2.2.1.2.2.1⟩
  haveI hRfinite : Finite ↥(M.piImg K) := Finite.of_surjective ρ hρ
  have hρker : ρ.ker = ⊥ :=
    le_bot_iff.mp (hρk.trans (le_of_eq (center_su_two_eq_bot hF hn hn3)))
  let eρ : ↥(LargeEvenSUGroup (Fin n) F 2) ≃* ↥(M.piImg K) :=
    MulEquiv.ofBijective ρ ⟨(MonoidHom.ker_eq_bot_iff ρ).1 hρker, hρ⟩
  rw [CFSG.Quasithin.H13.L3317.card_hopfMultiplier_congr eρ]
  exact CFSG.Quasithin.H13.L3317.card_ker_dvd_hopfMultiplier (piRestrict M hKS)
    (piRestrict_surjective M hKS) (piRestrict_ker_le_center M hKS)

theorem eq_one_of_mem_inf_centralizer_of_su5 (hcfg : Cfg173 3 S B N D K x)
    (M : S172DModel S B G₀ Ghat) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 2)
    (ρ : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin 5) F 2) →* ↥(M.piImg K))
    (hρ : Function.Surjective ρ) (hρk : ρ.ker ≤ Subgroup.center _) :
    ∀ k ∈ K, k ∈ Subgroup.centralizer (S : Set Ω) → k = 1 := by
  have hKS : K ≤ S := (hcfg.std.2.2.2.2.2.1.1).trans inf_le_left
  have hd := card_ker_piRestrict_dvd hcfg M hKS hF (by norm_num) (by norm_num) ρ hρ hρk
  rw [card_hopfMultiplier_su5 hF] at hd
  have hkerbot : (piRestrict M hKS).ker = ⊥ := Subgroup.card_eq_one.mp (Nat.dvd_one.mp hd)
  intro k hkK hkC
  have hkker := mem_ker_piRestrict M hKS hkK hkC
  rw [hkerbot] at hkker
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hkker)

theorem eq_one_of_mem_inf_centralizer_of_su4 (hcfg : Cfg173 3 S B N D K x)
    (M : S172DModel S B G₀ Ghat) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 2)
    (ρ : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin 4) F 2) →* ↥(M.piImg K))
    (hρ : Function.Surjective ρ) (hρk : ρ.ker ≤ Subgroup.center _) :
    ∀ k ∈ K, k ∈ Subgroup.centralizer (S : Set Ω) → k ^ 3 = 1 → k = 1 := by
  have hKS : K ≤ S := (hcfg.std.2.2.2.2.2.1.1).trans inf_le_left
  have hd := card_ker_piRestrict_dvd hcfg M hKS hF (by norm_num) (by norm_num) ρ hρ hρk
  rw [card_hopfMultiplier_su4 hF] at hd
  intro k hkK hkC hk3
  set z : ↥(piRestrict M hKS).ker := ⟨⟨k, hkK⟩, mem_ker_piRestrict M hKS hkK hkC⟩ with hz
  have h2 : orderOf z ∣ 2 := (orderOf_dvd_natCard z).trans hd
  have h3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hk3)
  have hz1 : z = 1 := by
    have h := Nat.dvd_gcd h2 h3
    rw [show Nat.gcd 2 3 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h
    exact h
  have := congrArg (fun w : ↥(piRestrict M hKS).ker => ((w : ↥K) : Ω)) hz1
  simpa [hz] using this

theorem eq_one_of_mem_inf_centralizer_of_su_two (hcfg : Cfg173 3 S B N D K x)
    (M : S172DModel S B G₀ Ghat) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 2)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (ρ : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2) →* ↥(M.piImg K))
    (hρ : Function.Surjective ρ) (hρk : ρ.ker ≤ Subgroup.center _) :
    ∀ k ∈ K, k ∈ Subgroup.centralizer (S : Set Ω) → k ^ 3 = 1 → k = 1 := by
  rcases hn with rfl | rfl
  · exact eq_one_of_mem_inf_centralizer_of_su4 hcfg M hF ρ hρ hρk
  · exact fun k hk hkC _ => eq_one_of_mem_inf_centralizer_of_su5 hcfg M hF ρ hρ hρk k hk hkC

end CFSG.LocalAnalysis.GLTheoremA.T173O

end

