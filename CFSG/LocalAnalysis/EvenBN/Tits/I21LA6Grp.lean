module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Defs
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LA6GrpO
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LA6GrpJ
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LA6GrpTr
public import CFSG.Sporadic.Recognition.JankoWongPSLNine

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup CFSG.LocalAnalysis.EvenBN.Tits CFSG.Open

theorem a6grp_equiv_A6 {K : Type*} [Group K] (hK : IsPSLTwo K 9) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := hK
  obtain ⟨φ⟩ :=
    CFSG.Sporadic.Recognition.JankoWong.nonempty_mulEquiv_alternatingGroup_six_of_card_nine hcard
  exact ⟨e.trans φ⟩

theorem a6grp_card_A6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem a6grp_quot_comm {Y : Type*} [Group Y] (O : Subgroup Y) [O.Normal]
    {L : Subgroup (Y ⧸ O)} (hL : Nat.card L = 360) {J₀ : Subgroup Y}
    (hJ₀L : J₀ ≤ L.comap (QuotientGroup.mk' O)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Subgroup Y} (hQ : Q ≤ J₀) (hQp : IsPGroup p Q) :
    ∀ a ∈ Q, ∀ b ∈ Q, b * a * b⁻¹ * a⁻¹ ∈ O := by
  intro a ha b hb
  have hQ'p : IsPGroup p (Q.map (QuotientGroup.mk' O)) := hQp.map _
  have hQ'L : Q.map (QuotientGroup.mk' O) ≤ L := by
    rintro _ ⟨q, hq, rfl⟩
    exact hJ₀L (hQ hq)
  have hdvd : Nat.card (Q.map (QuotientGroup.mk' O)) ∣ 360 :=
    hL ▸ Subgroup.card_dvd_of_le hQ'L
  have hcomm := a6grp_comm_of_pGroup hp hp2 hQ'p hdvd ⟨QuotientGroup.mk' O b, b, hb, rfl⟩
    ⟨QuotientGroup.mk' O a, a, ha, rfl⟩
  have h2 : (QuotientGroup.mk b : Y ⧸ O) * QuotientGroup.mk a =
      QuotientGroup.mk a * QuotientGroup.mk b := congrArg Subtype.val hcomm
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [h2]
  group

section Cases

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Y : Type*} [Group Y] [Finite Y]
  (ρ : Y →* (V ≃ₗ[ZMod 2] V)) (t : Y)

variable {ρ t} {u x h : Y}

theorem a6_branch_structure (H : HypYW ρ t u x h)
    (hxO : x ∉ standardComponentOddCore Y)
    (hL : ∃ L : Subgroup (Y ⧸ standardComponentOddCore Y), L.Normal ∧
      centralizer (L : Set (Y ⧸ standardComponentOddCore Y)) = ⊥ ∧ IsPSLTwo L 9 ∧
      (QuotientGroup.mk t : Y ⧸ standardComponentOddCore Y) ∉ L ∧
      (QuotientGroup.mk x : Y ⧸ standardComponentOddCore Y) ∈ L ∧
      (QuotientGroup.mk (u ^ 2) : Y ⧸ standardComponentOddCore Y) ∈ L ∧
      PGLTwoSquareOuter L (QuotientGroup.mk t : Y ⧸ standardComponentOddCore Y)) :
    normalClosure ({x} : Set Y) ⊓ standardComponentOddCore Y = ⊥ ∧
      Nonempty (normalClosure ({x} : Set Y) ≃* alternatingGroup (Fin 6)) ∧
      u ^ 2 ∈ normalClosure ({x} : Set Y) ∧
      (∀ o ∈ standardComponentOddCore Y, ∀ j ∈ normalClosure ({x} : Set Y), o * j = j * o) := by
  obtain ⟨L, hLn, -, hLP, -, hxL, hzL, -⟩ := hL
  set O := standardComponentOddCore Y with hOdef
  have hOodd : Odd (Nat.card O) := secTwo_odd_card_oddCore
  obtain ⟨hinv, habel, hzc⟩ :=
    a6grp_oddCore_abelian H.sec H.ord_x H.tx H.ux H.cent H.fuse hxO
  obtain ⟨e⟩ := a6grp_equiv_A6 hLP
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup L := e.isSimpleGroup
  haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  haveI : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hL360 : Nat.card L = 360 := by rw [Nat.card_congr e.toEquiv, a6grp_card_A6]
  have hzO : u ^ 2 ∉ O := fun hz =>
    H.sec.z_ne_one (secTwo_eq_one_of_sq hOodd hz H.sec.z_sq)
  have hzJ : u ^ 2 ∈ L.comap (QuotientGroup.mk' O) := hzL
  have hxJ : x ∈ L.comap (QuotientGroup.mk' O) := hxL
  have hcent := a6grp_oddCore_le_center O hzJ hzO habel hzc
  obtain ⟨hJ₀O, hperf⟩ := a6grp_J0_perfect O hOodd hxJ hxO H.tx hinv
  set J₀ := normalClosure ({x} : Set Y) with hJ₀
  haveI : Group.IsPerfect J₀ := hperf
  have hJ₀J : J₀ ≤ L.comap (QuotientGroup.mk' O) := hJ₀O ▸ le_sup_left
  have hxJ₀ : x ∈ J₀ := subset_normalClosure (Set.mem_singleton x)
  have hbot : J₀ ⊓ O = ⊥ :=
    a6grp_inf_eq_bot ρ H.inj H.dim H.fix hOodd hxJ₀ (fun g hg o ho => hcent g (hJ₀J hg) o ho)
      (fun p hp hp2 Q hQ hQp => a6grp_quot_comm O hL360 hJ₀J hp hp2 hQ hQp)
  refine ⟨hbot, ?_, ?_, fun o ho j hj => (hcent j (hJ₀J hj) o ho).symm⟩
  · obtain ⟨f⟩ := a6grp_equiv_of_inf_eq_bot O hJ₀O hbot
    exact ⟨f.trans e⟩
  · exact a6grp_mem_of_sq O hJ₀O hbot hOodd hcent hzJ (by rw [← sq]; exact H.sec.z_sq)

end Cases

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
