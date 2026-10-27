module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412
public import CFSG.GH74.KGroups.L33
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Models.Blueprint
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporExact
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
public import CFSG.LocalAnalysis.GLTheoremA.Pump

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup no_glaPComponent_of_exact)

private theorem lieRowL3_fixSubgroup_one {K : Type*} [Group K] :
    fixSubgroup (1 : MulAut K) = ⊤ := by
  ext x
  rw [mem_fixSubgroup]
  simp

private theorem lieRowL3_fixSubgroup_conj {K : Type*} [Group K] (u : K) :
    fixSubgroup (MulAut.conj u) = Subgroup.centralizer ({u} : Set K) := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

private theorem lieRowL3_center_eq_bot {T : Type} [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ Subgroup.center T := by
      rw [h]
      exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

private theorem lieRowL3_isSubnormal_top {T : Type} [Group T] [IsSimpleGroup T] {H K : Subgroup T}
    (h : IsSubnormal H K) : K = ⊤ → H = ⊥ ∨ H = ⊤ := by
  induction h with
  | refl H => intro hK; exact Or.inr hK
  | @step H M K hle hn _ ih =>
    intro hK
    rcases ih hK with hM | hM
    · exact Or.inl (le_bot_iff.1 (hM ▸ hle))
    · subst hM
      haveI : H.Normal :=
        ⟨fun n hn' g => (Subgroup.normal_subgroupOf_iff le_top).1 hn n g hn' (Subgroup.mem_top g)⟩
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H

private theorem lieRowL3_pSimple_top_equiv {p : ℕ} (hp : p.Prime) {T : Type} [Group T] [Finite T]
    [IsSimpleGroup T] (hnc : ∃ a b : T, a * b ≠ b * a) {I : Subgroup T}
    (hI : GLAPComponent p (⊤ : Subgroup T) I) : Nonempty (PSimple p I ≃* T) := by
  have hIeq : I = ⊤ := by
    rcases lieRowL3_isSubnormal_top hI.2.1 rfl with h | h
    · exact absurd h (glaPComponent_ne_bot' hI)
    · exact h
  subst hIeq
  have hq : CFSG.Open.IsQuasisimple (PQuot p (⊤ : Subgroup T)) :=
    isQuasisimple_pQuot_of_glaPComponent hp hI
  have hnt : Nontrivial (↥(⊤ : Subgroup T) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup T)) := by
    haveI : Nontrivial (PQuot p (⊤ : Subgroup T) ⧸ Subgroup.center (PQuot p (⊤ : Subgroup T))) :=
      hq.2.toNontrivial
    exact (QuotientGroup.mk'_surjective
      (Subgroup.center (PQuot p (⊤ : Subgroup T)))).nontrivial
  have hOb : GLAPPrimeCore p ↥(⊤ : Subgroup T) = ⊥ := by
    let ψ : ↥(⊤ : Subgroup T) ≃* T := Subgroup.topEquiv
    haveI : ((GLAPPrimeCore p ↥(⊤ : Subgroup T)).map ψ.toMonoidHom).Normal :=
      Subgroup.Normal.map (GLAPPrimeCore.normal p _) ψ.toMonoidHom ψ.surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((GLAPPrimeCore p ↥(⊤ : Subgroup T)).map ψ.toMonoidHom) with h | h
    · exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).1 h
    · exfalso
      have htop : GLAPPrimeCore p ↥(⊤ : Subgroup T) = ⊤ := by
        apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
        rw [h, Subgroup.map_top_of_surjective _ ψ.surjective]
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(⊤ : Subgroup T) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup T))
      apply hab
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq, htop]
      exact Subgroup.mem_top _
  have hZtop : Subgroup.center ↥(⊤ : Subgroup T) = ⊥ := by
    have h1 := Subgroup.map_center_eq (Subgroup.topEquiv : ↥(⊤ : Subgroup T) ≃* T)
    rw [lieRowL3_center_eq_bot hnc] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective).1 h1
  let e1 : PQuot p (⊤ : Subgroup T) ≃* ↥(⊤ : Subgroup T) :=
    (QuotientGroup.quotientMulEquivOfEq hOb).trans QuotientGroup.quotientBot
  let e2 : PSimple p (⊤ : Subgroup T) ≃*
      (↥(⊤ : Subgroup T) ⧸ Subgroup.center ↥(⊤ : Subgroup T)) :=
    QuotientGroup.congr _ _ e1 (Subgroup.map_center_eq e1)
  let e3 : (↥(⊤ : Subgroup T) ⧸ Subgroup.center ↥(⊤ : Subgroup T)) ≃* ↥(⊤ : Subgroup T) :=
    (QuotientGroup.quotientMulEquivOfEq hZtop).trans QuotientGroup.quotientBot
  exact ⟨e2.trans (e3.trans Subgroup.topEquiv)⟩

private theorem lieRowL3_kLevel_le_two {p : ℕ} {S : Type} [Group S] (h : catalogIs S (k2 p)) :
    kLevel p S ≤ 2 := by
  unfold kLevel
  split_ifs <;> first | omega | exact absurd h ‹_›

private theorem lieRowL3_downLe_of_iso {K : Type} [Group K]
    (eP : K ≃* CFSG.GH74.KGroups.L33.QP.originalSubgroup)
    (eS : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3))
    (hk2 : catalogIs K (k2 13)) : DownLe 13 2 K := by
  have hp : Nat.Prime 13 := by norm_num
  haveI : Fact (Nat.Prime 13) := ⟨hp⟩
  haveI : Finite K := CFSG.GH74.KGroups.L33.finite_K eP
  have hlin := CFSG.LinearGroups.linear_projective_simple (K := ZMod 3) (n := 3) (by norm_num)
    (Or.inl (by norm_num))
  have hsimp : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) := hlin.2.1
  haveI : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) := hlin.1
  haveI : IsSimpleGroup K := (MulEquiv.isSimpleGroup_congr eS).mpr hsimp
  have hncPSL : ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3), a * b ≠ b * a := by
    by_contra hcomm
    simp only [not_exists, ne_eq, not_not] at hcomm
    have hperf := CFSG.LinearGroups.linear_projective_perfect (K := ZMod 3) (n := 3)
      (by norm_num) (Or.inl (by norm_num))
    have htop : (⁅(⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3))),
        (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)))⁆ : Subgroup _) = ⊤ :=
      hperf.commutator_eq_top
    have hbot : (⁅(⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3))),
        (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)))⁆ : Subgroup _) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro h _
      exact hcomm h x
    have hTB : (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3))) = ⊥ :=
      htop.symm.trans hbot
    obtain ⟨x, hx⟩ := exists_ne (1 : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3))
    have hxt : x ∈ (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3))) :=
      Subgroup.mem_top x
    rw [hTB, Subgroup.mem_bot] at hxt
    exact hx hxt
  have hnc : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hncPSL
    exact ⟨eS.symm a, eS.symm b, fun h => hab (by
      have := congrArg eS h
      simpa using this)⟩
  have hZ : Subgroup.center K = ⊥ := lieRowL3_center_eq_bot hnc
  have hkle : kLevel 13 K ≤ 2 := lieRowL3_kLevel_le_two hk2
  have hcardK : Nat.card K = 5616 := by
    rw [Nat.card_congr eS.toEquiv, CFSG.GH74.KGroups.L33.card_psl]
  have hcardA : Nat.card (MulAut K) = 11232 := CFSG.GH74.KGroups.L33.card_mulAut eP
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx := DFunLike.congr_fun hg x
      rw [MulAut.conj_apply, MulAut.one_apply] at hx
      exact (mul_inv_eq_iff_eq_mul.1 hx).symm
    rw [hZ, Subgroup.mem_bot] at hgc
    exact hgc
  have hHcard : Nat.card (MulAut.conj : K →* MulAut K).range = 5616 := by
    rw [← hcardK]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hHidx : (MulAut.conj : K →* MulAut K).range.index = 2 := by
    have h := Subgroup.card_mul_index (MulAut.conj : K →* MulAut K).range
    rw [hHcard, hcardA] at h
    omega
  haveI : (MulAut.conj : K →* MulAut K).range.Normal := Subgroup.normal_of_index_eq_two hHidx
  have hmem : ∀ β : MulAut K, β ^ 13 = 1 → β ∈ (MulAut.conj : K →* MulAut K).range := by
    intro β hβ
    have h2 : ((β : MulAut K ⧸ (MulAut.conj : K →* MulAut K).range)) ^ 2 = 1 := by
      have h := @pow_card_eq_one' (MulAut K ⧸ (MulAut.conj : K →* MulAut K).range) _
        (β : MulAut K ⧸ (MulAut.conj : K →* MulAut K).range)
      rwa [show Nat.card (MulAut K ⧸ (MulAut.conj : K →* MulAut K).range) = 2 from hHidx] at h
    have h13 : ((β : MulAut K ⧸ (MulAut.conj : K →* MulAut K).range)) ^ 13 = 1 := by
      rw [← QuotientGroup.mk_pow, hβ]
      rfl
    have hd1 := orderOf_dvd_of_pow_eq_one h13
    have hd2 := orderOf_dvd_of_pow_eq_one h2
    have hd : orderOf ((β : MulAut K ⧸ (MulAut.conj : K →* MulAut K).range)) ∣ 1 := by
      have hg : Nat.gcd 13 2 = 1 := by norm_num
      have := Nat.dvd_gcd hd1 hd2
      rwa [hg] at this
    have hx : ((β : MulAut K ⧸ (MulAut.conj : K →* MulAut K).range)) = 1 :=
      orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
    exact (QuotientGroup.eq_one_iff β).1 hx
  intro β hβ J hJ
  by_cases hβ1 : β = 1
  · subst hβ1
    rw [lieRowL3_fixSubgroup_one] at hJ
    obtain ⟨f⟩ := lieRowL3_pSimple_top_equiv hp hnc hJ
    exact (kLevel_congr 13 f).trans_le hkle
  · exfalso
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 (hmem β hβ)
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hβ1 (map_one _)
    have hk13 : k ^ 13 = 1 := by
      have h : MulAut.conj (k ^ 13) = 1 := by
        rw [map_pow]
        exact hβ
      have hc : k ^ 13 ∈ Subgroup.center K := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg := DFunLike.congr_fun h g
        rw [MulAut.conj_apply, MulAut.one_apply] at hg
        exact (mul_inv_eq_iff_eq_mul.1 hg).symm
      rw [hZ, Subgroup.mem_bot] at hc
      exact hc
    have hord : orderOf k = 13 := orderOf_eq_prime hk13 hk1
    rw [lieRowL3_fixSubgroup_conj] at hJ
    exact no_glaPComponent_of_exact hp hord (by rw [hcardK]; norm_num) hJ

theorem lieRow_A2_three_thirteen (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) (hq : q.card = 3) :
    DownLe 13 2 (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group := by
  have hcard : q.p ^ q.exponent = 3 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq
  have hp3 : q.p = 3 := by
    have hdvd : q.p ∣ 3 := by
      rw [← hcard]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hdvd
  have he1 : q.exponent = 1 := by
    rw [hp3] at hcard
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3)
      (show 3 ^ q.exponent = 3 ^ 1 by simpa using hcard)
  have hK0 := CFSG.Models.lieModel_A 2 q hv (MulEquiv.refl _)
  rw [hp3, he1] at hK0
  have hB := CFSG.Models.LieModel.toBlueprint (by decide) hK0
  obtain ⟨eP⟩ := CFSG.GH74.KGroups.L33.equiv_of_lieModel hB
  obtain ⟨eS⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_lieModel (F := ZMod 3) 3 3 1 (by norm_num)
    CFSG.GH74.KGroups.L33.card_F hB
  have hk2 : catalogIs (TauCeti.ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩) (k2 13) :=
    ⟨.lie ⟨.A 2 q, hv⟩, by simp [k2, k2Lie, hq, hcard], ⟨MulEquiv.refl _⟩⟩
  exact lieRowL3_downLe_of_iso eP eS hk2

end CFSG.LocalAnalysis.GLTheoremA
