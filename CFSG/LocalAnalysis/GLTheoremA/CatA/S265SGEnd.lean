module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2
import CFSG.GroupTheory.PLayer.CenterQuotientAction
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.Assembly
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup PerfectInLayer comm_mem_fixSubgroup
  map_fixSubgroup_le b3Lie_isQuasisimple_of_simple b3Lie_center_eq_bot)
open CFSG.Yardstones.Md42047359a2a (lieFamily)

private theorem exists_lieIdx_of_tyF {X : Type} [Group X] (h : catalogIs X (tyF 3)) :
    ∃ idx : TauCeti.ValidLieTypeIndex, lieFamily idx.1 = .linearUnitary ∧
      3 ≠ idx.1.characteristic ∧ Nonempty (X ≃* (TauCeti.CFSGIndex.lie idx).Group) := by
  obtain ⟨i, hi, he⟩ := h
  rcases i with _ | _ | ⟨⟨l, hv⟩⟩ | _ <;> try exact (hi : False).elim
  cases l
  case A r q =>
    exact ⟨⟨_, hv⟩, rfl, by simp [(hi : r + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card - 1).2.1], he⟩
  case twistedA r q =>
    exact ⟨⟨_, hv⟩, rfl, by simp [(hi : r + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card + 1).2.1], he⟩
  all_goals exact (hi : False).elim

private theorem commutator_comap_perfect_of_le_range {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hker : f.ker ≤ Subgroup.center G) {A : Subgroup H} (hAf : A ≤ f.range)
    (hA : ⁅A, A⁆ = A) :
    ⁅⁅A.comap f, A.comap f⁆, ⁅A.comap f, A.comap f⁆⁆ = ⁅A.comap f, A.comap f⁆ ∧
      ⁅A.comap f, A.comap f⁆.map f = A := by
  have hmap : ⁅A.comap f, A.comap f⁆.map f = A := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq, inf_of_le_right hAf, hA]
  refine ⟨le_antisymm (Subgroup.commutator_le_self _) ?_, hmap⟩
  have hdec : ∀ c ∈ A.comap f, ∃ y ∈ ⁅A.comap f, A.comap f⁆, ∃ z ∈ Subgroup.center G,
      c = y * z := fun c hc => by
    obtain ⟨y, hy, hyc⟩ : f c ∈ ⁅A.comap f, A.comap f⁆.map f := by rw [hmap]; exact hc
    refine ⟨y, hy, y⁻¹ * c, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyc, inv_mul_cancel]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  obtain ⟨y₁, hy₁, z₁, hz₁, rfl⟩ := hdec a ha
  obtain ⟨y₂, hy₂, z₂, hz₂, rfl⟩ := hdec b hb
  rw [CFSG.HardMathSupport.Solomon.Coordinator.commutatorElement_mul_mul'
    (Commute.symm (Subgroup.mem_center_iff.1 hz₁ y₂))
    (Commute.symm (Subgroup.mem_center_iff.1 hz₁ z₂))
    (Commute.symm (Subgroup.mem_center_iff.1 hz₂ y₁))]
  exact Subgroup.commutator_mem_commutator hy₁ hy₂

theorem SG.false_of_simple_fix {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hcat : catalogIs (PSimple 3 K) (tyF 3))
    {d e : Ω} (hdN : d ∈ Subgroup.normalizer (S : Set Ω))
    (heN : e ∈ Subgroup.normalizer (S : Set Ω)) (he : e ∈ B) (heD : e ∉ D)
    (hbr : GLALayer (fixSubgroup (chevAut 3 S ⟨d, hdN⟩)) = (K.subgroupOf S).map (chevQuotHom 3 S))
    (hpl : PerfectInLayer (chevAut 3 S ⟨d, hdN⟩)) {A : Subgroup (PSimple 3 S)}
    (hAd : A ≤ fixSubgroup (chevAut 3 S ⟨d, hdN⟩))
    (hAe : A ≤ fixSubgroup (chevAut 3 S ⟨e, heN⟩)) [IsSimpleGroup ↥A]
    (hnc : ∃ a b : ↥A, a * b ≠ b * a) (h3 : 3 ∣ Nat.card ↥A) : False := by
  obtain ⟨-, -, -, -, -, hKc, hDK⟩ := h.cfg.std
  have hKS : K ≤ S := hKc.1.trans inf_le_left
  have hAperf : ⁅A, A⁆ = A := by rw [← Subgroup.map_subtype_commutator,
    (b3Lie_isQuasisimple_of_simple hnc).1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set f : ↥K →* PSimple 3 S := (chevQuotHom 3 S).comp (Subgroup.inclusion hKS) with hf
  have hAf : A ≤ f.range := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range, ← hbr]; exact hpl A hAd hAperf
  have hfk : f.ker ≤ Subgroup.center ↥K := fun k hk => by
    have hk' : Subgroup.inclusion hKS k ∈ Subgroup.center ↥S := by
      rwa [← S171.ker_chevQuotHom_eq_center' h.cfg.prime h.cfg.comp h.cfg.quasi]
    refine Subgroup.mem_center_iff.2 fun k' => Subtype.ext ?_
    exact congrArg (fun s : ↥S => (s : Ω))
      (Subgroup.mem_center_iff.1 hk' (Subgroup.inclusion hKS k'))
  obtain ⟨hYperf, hYmap⟩ := commutator_comap_perfect_of_le_range f hfk hAf hAperf
  have hSN : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ =>
    (Subgroup.normalizer_eq_top_iff.2 h.cfg.normal) ▸ Subgroup.mem_top g
  have hBN := S171.B_norm_K h.cfg.elem hSN h.cfg.std
  set α := CFSG.normalizerConjAutOfMem K B hBN ⟨e, he⟩
  have hαf : ∀ k, f (α k) = chevAut 3 S ⟨e, heN⟩ (f k) := fun k =>
    (chevAut_chevQuotHom 3 S ⟨e, heN⟩ (Subgroup.inclusion hKS k)).symm
  have hYα : ⁅A.comap f, A.comap f⁆ ≤ fixSubgroup α := Subgroup.commutator_le.2
    fun a ha b hb => comm_mem_fixSubgroup f hfk _ _ hαf (hAe ha) (hAe hb)
  set ψ := CFSG.normalizerToCenterQuotientAut K B hBN ⟨e, he⟩ with hψ
  set P := ⁅A.comap f, A.comap f⁆.map (QuotientGroup.mk' (Subgroup.center ↥K)) with hP
  have hPψ : P ≤ fixSubgroup ψ := (Subgroup.map_mono hYα).trans (map_fixSubgroup_le _
    (QuotientGroup.ker_mk' _).le _ ψ (CFSG.normalizerConjAutOfMem_comp_mk K B hBN ⟨e, he⟩))
  have hPperf : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hYperf]
  have hZ : Subgroup.center ↥K ⊓ ⁅A.comap f, A.comap f⁆ ≤ f.ker := by
    rintro y ⟨hyz, hyY⟩
    have hyA : f y ∈ A := by rw [← hYmap]; exact Subgroup.mem_map_of_mem f hyY
    have hc : (⟨f y, hyA⟩ : ↥A) ∈ Subgroup.center ↥A := Subgroup.mem_center_iff.2 fun a => by
      obtain ⟨y', -, hy'⟩ : (a : PSimple 3 S) ∈ ⁅A.comap f, A.comap f⁆.map f := by
        rw [hYmap]; exact a.2
      refine Subtype.ext (?_ : (a : PSimple 3 S) * f y = f y * a)
      rw [← hy', ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hyz y']
    rw [b3Lie_center_eq_bot hnc, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hAY : Nat.card ↥A = f.ker.relIndex ⁅A.comap f, A.comap f⁆ := by
    rw [Subgroup.relIndex_ker, hYmap]
  have h3P : 3 ∣ Nat.card ↥P := by
    rw [hP, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk', ← Subgroup.inf_relIndex_right]
    exact (hAY ▸ h3).trans (Subgroup.relIndex_dvd_of_le_left _ hZ)
  have h3K : 3 ∣ Nat.card ↥K :=
    (h3.trans (Subgroup.card_dvd_of_le hAf)).trans (Subgroup.card_range_dvd f)
  haveI : Group.IsPerfect ↥K := ⟨hKc.2.2.1⟩
  have hne : GLAPPrimeCore 3 ↥K ≠ ⊤ := fun htop => by
    have hco : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥K)) :=
      CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K)
    rw [htop, Subgroup.card_top] at hco
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hco h3K
  have θ := S172A.pSimpleEquivCenterQuot 3
    (le_center_of_normal_of_isQuasisimple hKc.2.2 inferInstance hne)
  obtain ⟨idx, hF, hpc, ⟨eK⟩⟩ := exists_lieIdx_of_tyF hcat
  have hψ3 : ψ ^ 3 = 1 := by
    rw [hψ, ← map_pow, show (⟨e, he⟩ : ↥B) ^ 3 = 1 from
      Subtype.ext (by rw [Subgroup.coe_pow]; exact h.cfg.elem.2 e he), map_one]
  have hψ1 : ψ ≠ 1 := fun h1 => heD (hDK ▸
    (CFSG.normalizerToCenterQuotientAut_eq_one_iff ⟨hKc.2.2.1⟩ hBN ⟨e, he⟩).1 h1)
  have hpil : PerfectInLayer ψ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCentLinearUnitary
      (↥K ⧸ Subgroup.center ↥K) hKc.2.2.2 (GL83.CompFam.quasisimple_quotient_nonabelian hKc.2.2)
      idx hF ⟨θ.trans eK⟩ 3 Nat.prime_three (by decide) hpc ψ hψ3 hψ1
  exact SF.glaPLayer_ne_bot_of_le_glaLayer Nat.prime_three (hpil P hPψ hPperf) h3P
    ((CFSG.glaPLayer_inf_centralizer_eq_bot_iff Nat.prime_three hBN ⟨e, he⟩).1 (h.nl e he heD))

theorem SG.exists_chevAut_mem_of_relIndex_le {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω}
    {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hB : Nat.card B = 3 ^ 4)
    {Y : Subgroup (MulAut (PSimple 3 S))}
    (hY : Y.relIndex ((B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut 3 S)) ≤ 3) :
    ∃ e ∈ B, e ∉ D ∧ ∃ heN : e ∈ Subgroup.normalizer (S : Set Ω), chevAut 3 S ⟨e, heN⟩ ∈ Y := by
  have hSN : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ =>
    (Subgroup.normalizer_eq_top_iff.2 h.cfg.normal) ▸ Subgroup.mem_top g
  set φ : ↥B →* MulAut (PSimple 3 S) := (chevAut 3 S).comp (Subgroup.inclusion hSN) with hφ
  have hidx : (Y.comap φ).index ≤ 3 := by
    rwa [Subgroup.index_comap, hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
  by_contra hne
  have hle : Nat.card ↥(Y.comap φ) ≤ Nat.card ↥D := Nat.card_le_card_of_injective
    (fun b => ⟨b.1.1, not_not.1 fun hbD => hne ⟨b.1.1, b.1.2, hbD, hSN b.1.2, b.2⟩⟩)
    fun b b' hbb => Subtype.ext (Subtype.ext (congrArg (fun z : ↥D => (z : Ω)) hbb))
  obtain ⟨-, -, hD, -⟩ := h.cfg.std
  have h1 : Nat.card ↥B ≤ 3 ^ 2 * 3 := by
    rw [← Subgroup.card_mul_index (Y.comap φ)]; exact Nat.mul_le_mul (hle.trans hD.le) hidx
  norm_num [hB] at h1

theorem SG.false_of_simple_fix_relIndex {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω}
    {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hcat : catalogIs (PSimple 3 K) (tyF 3))
    (hB : Nat.card B = 3 ^ 4) {d : Ω} (hdN : d ∈ Subgroup.normalizer (S : Set Ω))
    (hbr : GLALayer (fixSubgroup (chevAut 3 S ⟨d, hdN⟩)) = (K.subgroupOf S).map (chevQuotHom 3 S))
    (hpl : PerfectInLayer (chevAut 3 S ⟨d, hdN⟩)) {A : Subgroup (PSimple 3 S)}
    (hAd : A ≤ fixSubgroup (chevAut 3 S ⟨d, hdN⟩)) [IsSimpleGroup ↥A]
    (hnc : ∃ a b : ↥A, a * b ≠ b * a) (h3 : 3 ∣ Nat.card ↥A) {Y : Subgroup (MulAut (PSimple 3 S))}
    (hY : Y.relIndex ((B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut 3 S)) ≤ 3)
    (hYA : ∀ ε ∈ Y, A ≤ fixSubgroup ε) : False := by
  obtain ⟨e, he, heD, heN, heY⟩ := SG.exists_chevAut_mem_of_relIndex_le h hB hY
  exact SG.false_of_simple_fix h hcat hdN heN he heD hbr hpl hAd (hYA _ heY) hnc h3

theorem SG.resLin_rank {lab : GLALabel} (h3 : 3 ≤ rk2Mult lab (rk2Ord 3 lab.n))
    (hc : (lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1 ∧ lab.rank ≤ 4) ∨
      (lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank ≤ 8) ∨
      (lab.tag = .D ∧ 3 ∣ 2 ^ lab.n - 1 ∧ lab.rank ≤ 3)) :
    (lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 3 ≤ lab.rank ∧ lab.rank ≤ 4) ∨
      (lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 5 ≤ lab.rank ∧ lab.rank ≤ 8) ∨
      (lab.tag = .D ∧ 3 ∣ 2 ^ lab.n - 1 ∧ lab.rank = 3) := by
  rcases hc with ⟨ht, hm, hr⟩ | ⟨ht, hp, hr⟩ | ⟨ht, hm, hr⟩
  · simp [rk2Mult, ht, rk2Ord_eq_one_iff.2 hm] at h3
    exact .inl ⟨ht, hm, by omega, hr⟩
  · simp [rk2Mult, ht, (rk2Ord_eq_two_iff Nat.prime_three (by decide)).2 hp] at h3
    exact .inr (.inl ⟨ht, hp, by omega, hr⟩)
  · simp [rk2Mult, ht, rk2Ord_eq_one_iff.2 hm] at h3
    exact .inr (.inr ⟨ht, hm, by omega⟩)

theorem SG.resUni_rank {lab : GLALabel} (h3 : 3 ≤ rk2Mult lab (rk2Ord 3 lab.n))
    (hc : (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank ≤ 4) ∨
      (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twD ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank = 3)) :
    (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 3 ≤ lab.rank ∧ lab.rank ≤ 4) ∨
      (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 5 ≤ lab.rank) ∨
      (lab.tag = .twD ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank = 3) := by
  rcases hc with ⟨ht, hp, hr⟩ | ⟨ht, hm⟩ | hd
  · simp [rk2Mult, ht, (rk2Ord_eq_two_iff Nat.prime_three (by decide)).2 hp] at h3
    exact .inl ⟨ht, hp, by omega, hr⟩
  · simp [rk2Mult, ht, rk2Ord_eq_one_iff.2 hm] at h3
    exact .inr (.inl ⟨ht, hm, by omega⟩)
  · exact .inr (.inr hd)

theorem SG.resSp_rank {lab : GLALabel} (h3 : 3 ≤ rk2Mult lab (rk2Ord 3 lab.n))
    (hc : (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank ≤ 4) : lab.rank = 3 ∨ lab.rank = 4 := by
  have hm := rk2Ord_pos Nat.prime_three (by decide) lab.n
  have hle : rk2Mult lab (rk2Ord 3 lab.n) ≤ lab.rank := by
    rcases hc.1 with ht | ht <;> simp only [rk2Mult, ht] <;> split_ifs with h2
    all_goals first
      | exact Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ (by omega))
      | exact Nat.div_le_self _ _
  omega

theorem SG.resOmP_rank {lab : GLALabel} (h3 : 3 ≤ rk2Mult lab (rk2Ord 3 lab.n))
    (hc : lab.tag = .D ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank ≤ 5) : lab.rank = 4 ∨ lab.rank = 5 := by
  obtain ⟨ht, hp, hr⟩ := hc
  simp [rk2Mult, ht, (rk2Ord_eq_two_iff Nat.prime_three (by decide)).2 hp] at h3
  split_ifs at h3 <;> omega

end CFSG.LocalAnalysis.GLTheoremA.S265

end
