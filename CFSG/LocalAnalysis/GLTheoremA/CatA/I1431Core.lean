module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Rank
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.D44

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY rkY_of_ambient)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
section Facts

variable {G : Type} [Group G] [Finite G]

theorem i1431_isElemAbelian_zpowers {y : G} (hy : y ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers y) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [← hm, ← hn]
    exact (Commute.refl y).zpow_zpow m n |>.eq
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]

theorem i1431_le_sup_of_centMod {p : ℕ} {X K J : Subgroup G} {y : G}
    (hp : p.Prime) (hK : GLAPComponent p X K) (hy : IsPGroup p (Subgroup.zpowers y))
    (hCM : CentMod p K y) (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J) :
    K ≤ J ⊔ GLAPPrimeCoreOf p K := by
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({y} : Set G) with hCdef
  have hCK : C ⊔ GLAPPrimeCoreOf p K = K := inf_centralizer_sup_eq_of_centMod hp hy hCM
  obtain ⟨hcov, ⟨eC⟩⟩ := cover_facts hp (inf_le_left : C ≤ K) hCK
  have hqK : CFSG.Open.IsQuasisimple (PQuot p K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hqC : CFSG.Open.IsQuasisimple (PQuot p C) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eC.symm hqK
  obtain ⟨-, hlay, hbar⟩ := glaPLayer_of_isQuasisimple hqC
  have hJeq : J = GLAPLayer p C := hlay J hJ
  have hbarJ : barX p C J = ⊤ := hJeq ▸ hbar
  have hJcov : J ⊔ GLAPPrimeCoreOf p C = C := sup_glaPPrimeCoreOf_eq_of_barX_eq_top hJ.1 hbarJ
  have hOC : GLAPPrimeCoreOf p C ≤ GLAPPrimeCoreOf p K := by
    rw [hcov]
    exact inf_le_right
  calc K = C ⊔ GLAPPrimeCoreOf p K := hCK.symm
    _ ≤ J ⊔ GLAPPrimeCoreOf p K := by
      apply sup_le _ le_sup_right
      calc C = J ⊔ GLAPPrimeCoreOf p C := hJcov.symm
        _ ≤ J ⊔ GLAPPrimeCoreOf p K := sup_le_sup_left hOC J

theorem i1431_pSimple_equiv_barImage {p : ℕ} {K J : Subgroup G} {a : G} (hp : p.Prime)
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hap : IsPGroup p (Subgroup.zpowers a))
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) J) :
    Nonempty (PSimple p J ≃* PSimple p ((J.subgroupOf K).map (pQuotHom p K))) := by
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hJ0 : GLAPComponent p (fixSubgroup (K.normalizerMonoidHom ⟨a, ha⟩)) (J.subgroupOf K) := by
    rw [fixSubgroup_normalizerMonoidHom ha]
    exact glaPComponent_subgroupOf hp inf_le_left hJ
  have hJ1 := glaPComponent_map_pQuotHom hp ha hap hJ
  obtain ⟨g⟩ := nonempty_pQuot_equiv_subgroupOf p hJK
  obtain ⟨e₁⟩ := nonempty_pSimple_equiv_map hp (pQuotHom p K) hJ0 hJ1
  have e₀ : PSimple p J ≃* PSimple p (J.subgroupOf K) :=
    QuotientGroup.congr _ _ g.symm (Subgroup.map_center_eq g.symm)
  exact ⟨e₀.trans e₁⟩

theorem i1431_rkY {K : Subgroup G} {a : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (haK : a ∈ Subgroup.centralizer (K : Set G)) (hrk : GLATwoLocalRank 3 G ≤ 4) :
    RkY (PQuot 3 K) :=
  rkY_of_ambient ((CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le Nat.prime_three _).trans hrk)
    (i1431_isElemAbelian_zpowers ha3) (Subgroup.mem_zpowers a) ha1 haK

end Facts

theorem i1431_not_five_le_twoLocalRank {Y : Type} [Group Y] [Finite Y] (h : RkY Y) :
    ¬ 5 ≤ GLATwoLocalRank 3 Y := by
  intro h5
  obtain ⟨U, hU, hU2, hUr⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.exists_twoLocal_of_le Nat.one_lt_ofNat
      (by norm_num : 0 < 5) h5
  obtain ⟨E, hEN, hE, hEc⟩ := CFSG.SectionRank.exists_pRank Nat.one_lt_ofNat
    (Subgroup.normalizer (U : Set Y)) (p := 3)
  have hle := (h U hU hU2 E hEN hE).1
  rw [hEc] at hle
  have : 3 ^ 5 ≤ 3 ^ CFSG.Open.pRank 3 (Subgroup.normalizer (U : Set Y)) :=
    Nat.pow_le_pow_right (by norm_num) hUr
  omega

theorem i1431_chev3_of_u42 {S : Type} [Group S] (h : catalogIs S S9.isU4two) : IsChevSimple 3 S := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU4two h
  exact Or.inr ⟨.lie ⟨.twistedA 3 q, hv⟩, ⟨hq2, rfl⟩, ⟨e⟩⟩

theorem i1431_u42_not_alt {S : Type} [Group S] {m : ℕ} (hm : 5 ≤ m) (h : catalogIs S S9.isU4two)
    (e : S ≃* alternatingGroup (Fin m)) : False := by
  obtain ⟨f⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_u4two h
  have h1 : Nat.card S = 25920 := by
    rw [Nat.card_congr f.toEquiv]
    exact CFSG.LieType.Multipliers.U42.card_PSp43
  have h2 : Nat.card S = m.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv]
    haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin]
  have h3 : m.factorial / 2 = 25920 := h2.symm.trans h1
  rcases le_or_gt m 8 with h8 | h9
  · interval_cases m <;> simp [Nat.factorial] at h3
  · have h4 : Nat.factorial 9 ≤ m.factorial := Nat.factorial_le (by omega)
    have h5 : Nat.factorial 9 = 362880 := by decide
    omega

theorem i1431_char_two_or_three
    (h33 : ∀ (S : Type) [Group S] (q r : ℕ), IsChevSimple q S → IsChevSimple r S → q ≠ r → q = 2 ∨ r = 2)
    {S : Type} [Group S] {r : ℕ} (hr : IsChevSimple r S)
    (hU : catalogIs S S9.isU4two) : r = 2 ∨ r = 3 := by
  by_cases h3 : r = 3
  · exact Or.inr h3
  · rcases h33 S r 3 hr (i1431_chev3_of_u42 hU) h3 with h | h
    · exact Or.inl h
    · exact absurd h (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA

end
