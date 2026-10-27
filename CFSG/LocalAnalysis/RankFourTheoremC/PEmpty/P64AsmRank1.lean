module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmMeta
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Transport
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU Subgroup
  CFSG.ComponentClassification.OuterAutomorphisms

namespace P64Asm

theorem pRank_top_le_of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (P : Sylow p G) : Open.pRank p (⊤ : Subgroup G) ≤ Open.pRank p (P : Subgroup G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, -, hE, hEc⟩ := SU1.exists_pRank hp.one_lt (⊤ : Subgroup G)
  obtain ⟨P', hEP'⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
  have hle : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hmem : x ∈ ((g • P : Sylow p G) : Subgroup G) := by
      rw [hg]
      exact hEP' hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
    simpa [MulAut.smul_def, MulAut.conj_apply] using hmem
  exact SU1.le_pRank hp.one_lt hle (CFSG.Open.IsElemAbelian.map hE _)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hEc])

theorem isCyclic_of_pRank_le_one {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {P : Subgroup G} (hP : IsPGroup p P) (hrk : Open.pRank p P ≤ 1) :
    IsCyclic P := by
  by_contra hnc
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  haveI := hSel
  have hSm : CFSG.IsElementaryAbelian p (S.map P.subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  have hcard : Nat.card (S.map P.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hScard]
  have h2 := SU1.le_pRank hp.one_lt (Subgroup.map_subtype_le S)
    (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hSm) hcard
  omega

theorem mem_zpowers_of_cyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {p : ℕ}
    (hp : p.Prime) {x y : C} (hx1 : x ≠ 1) (hx : x ^ p = 1) (hy : y ^ p = 1) :
    y ∈ zpowers x := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  have hxo : orderOf x = p := orderOf_eq_prime hx hx1
  have hyo : orderOf y = p := orderOf_eq_prime hy hy1
  have heq : zpowers y = zpowers x := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hxo, hyo]
  rw [← heq]
  exact mem_zpowers y

end P64Asm

theorem kdI278Rank1_of_i713 (hI : GL83.I_7_13_1) : KDI278Rank1 := by
  rintro p hp hp5 Z _ _ K hKn hKs hKna hKcat hcen ⟨P, hPrk⟩ Q a ha b hb hap hbp
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hKrk : Open.pRank p (⊤ : Subgroup ↥K) ≤ 1 :=
    (P64Asm.pRank_top_le_of_sylow hp P).trans hPrk
  obtain ⟨hOut, -⟩ := hI p hp hp2 ↥K hKs hKna hKcat hKrk
  let θ : Z →* MulAut ↥K := MulAut.conjNormal
  let ψ : Z →* Outer ↥K := (QuotientGroup.mk' (inner ↥K)).comp θ
  have hker : ∀ x : Z, ψ x = 1 → x ∈ K := by
    intro x hx
    have hx' : θ x ∈ inner ↥K := (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨k, hk⟩ := hx'
    have hxk : x⁻¹ * (k : Z) ∈ centralizer (K : Set Z) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun α : MulAut ↥K => ((α ⟨y, hy⟩ : ↥K) : Z)) hk
      simp only [MulAut.conj_apply, θ, MulAut.conjNormal_apply] at h1
      have h1' : (k : Z) * y * (k : Z)⁻¹ = x * y * x⁻¹ := h1
      calc y * (x⁻¹ * k) = x⁻¹ * (x * y * x⁻¹) * k := by group
        _ = x⁻¹ * ((k : Z) * y * (k : Z)⁻¹) * k := by rw [h1']
        _ = x⁻¹ * k * y := by group
    rw [hcen, Subgroup.mem_bot] at hxk
    have hxk' : x = (k : Z) := inv_mul_eq_one.mp hxk
    rw [hxk']
    exact k.2
  have hNp : IsPGroup p ↥((Q : Subgroup Z) ⊓ K) := Q.isPGroup'.to_le inf_le_left
  have hKrk' : Open.pRank p (K : Subgroup Z) ≤ 1 := by
    have := hKrk
    rwa [← pRank_map_subtype hp.one_lt, Subgroup.map_top, Subgroup.range_subtype] at this
  have hNrk : Open.pRank p ((Q : Subgroup Z) ⊓ K) ≤ 1 :=
    (SU1.pRank_mono hp.one_lt (inf_le_right : (Q : Subgroup Z) ⊓ K ≤ K)).trans hKrk'
  haveI hNcyc : IsCyclic ↥((Q : Subgroup Z) ⊓ K) :=
    P64Asm.isCyclic_of_pRank_le_one hp hp2 hNp hNrk
  haveI : Finite (Outer ↥K) := inferInstance
  have hCp : IsPGroup p ((Q : Subgroup Z).map ψ) := Q.isPGroup'.map ψ
  have hCrk : Open.pRank p ((Q : Subgroup Z).map ψ) ≤ 1 :=
    (SU1.pRank_mono hp.one_lt le_top).trans hOut
  haveI hCcyc : IsCyclic ↥((Q : Subgroup Z).map ψ) :=
    P64Asm.isCyclic_of_pRank_le_one hp hp2 hCp hCrk
  have key : ∀ a ∈ (Q : Subgroup Z), ∀ b ∈ (Q : Subgroup Z), a ^ p = 1 → b ^ p = 1 →
      ψ a ≠ 1 → a * b = b * a := by
    intro a ha b hb hap hbp hψa
    have hψap : ψ a ^ p = 1 := by rw [← map_pow, hap, map_one]
    have hψbp : ψ b ^ p = 1 := by rw [← map_pow, hbp, map_one]
    have haC : ψ a ∈ (Q : Subgroup Z).map ψ := Subgroup.mem_map_of_mem _ ha
    have hbC : ψ b ∈ (Q : Subgroup Z).map ψ := Subgroup.mem_map_of_mem _ hb
    have hmem : (⟨ψ b, hbC⟩ : ↥((Q : Subgroup Z).map ψ)) ∈
        zpowers (⟨ψ a, haC⟩ : ↥((Q : Subgroup Z).map ψ)) :=
      P64Asm.mem_zpowers_of_cyclic hp (fun h => hψa (congrArg Subtype.val h))
        (Subtype.ext hψap) (Subtype.ext hψbp)
    obtain ⟨i, hi⟩ := (mem_powers_iff_mem_zpowers).mpr hmem
    have hψi : ψ a ^ i = ψ b := congrArg Subtype.val hi
    have hnQ : b * (a ^ i)⁻¹ ∈ (Q : Subgroup Z) :=
      (Q : Subgroup Z).mul_mem hb ((Q : Subgroup Z).inv_mem ((Q : Subgroup Z).pow_mem ha i))
    have hnK : b * (a ^ i)⁻¹ ∈ K := by
      apply hker
      rw [map_mul, map_inv, map_pow, hψi, mul_inv_cancel]
    have hnN : b * (a ^ i)⁻¹ ∈ (Q : Subgroup Z) ⊓ K := ⟨hnQ, hnK⟩
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥((Q : Subgroup Z) ⊓ K))
    obtain ⟨s, hs⟩ := (mem_powers_iff_mem_zpowers).mpr (hg ⟨_, hnN⟩)
    have hsn : (g : Z) ^ s = b * (a ^ i)⁻¹ := congrArg Subtype.val hs
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hNp) g
    have hdg : a * (g : Z) * a⁻¹ ∈ zpowers (g : Z) := by
      have hagN : a * (g : Z) * a⁻¹ ∈ (Q : Subgroup Z) ⊓ K :=
        ⟨(Q : Subgroup Z).mul_mem ((Q : Subgroup Z).mul_mem ha g.2.1)
            ((Q : Subgroup Z).inv_mem ha),
          by
            have := hKn.conj_mem (g : Z) g.2.2 a
            simpa using this⟩
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨_, hagN⟩)
      exact mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
    have hbeq : b = (g : Z) ^ s * a ^ i := by
      rw [hsn]
      group
    have hy : ((g : Z) ^ s * a ^ i) ^ p = 1 := by rw [← hbeq]; exact hbp
    have hcomm := P64Asm.comm_of_pow_eq_one hp hp2 hap (by rw [Subgroup.orderOf_coe, hm]) hdg hy
    rw [hbeq]
    calc a * ((g : Z) ^ s * a ^ i) = (a * (g : Z) ^ s) * a ^ i := by group
      _ = ((g : Z) ^ s * a) * a ^ i := by rw [hcomm]
      _ = ((g : Z) ^ s * a ^ i) * a := by group
  by_cases hψa : ψ a = 1
  · by_cases hψb : ψ b = 1
    · have haN : a ∈ (Q : Subgroup Z) ⊓ K := ⟨ha, hker a hψa⟩
      have hbN : b ∈ (Q : Subgroup Z) ⊓ K := ⟨hb, hker b hψb⟩
      exact congrArg Subtype.val (mul_comm' (⟨a, haN⟩ : ↥((Q : Subgroup Z) ⊓ K)) ⟨b, hbN⟩)
    · exact (key b hb a ha hbp hap hψb).symm
  · exact key a ha b hb hap hbp hψa

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
