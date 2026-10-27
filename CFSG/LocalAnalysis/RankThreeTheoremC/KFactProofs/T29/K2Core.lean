module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.InnDiag
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.L227
public import CFSG.LieType.SeitzGeneration.HyperPlaneCube
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Tools
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Generic
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_16FieldMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator (Input23_16Three Field3Structure)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (IsLThreeEps)

theorem le_gammaQ_of_field_aut (h2316 : Input23_16Three) {X : Type} [Group X] [Finite X]
    {L : Subgroup X} [L.Normal] (hq : CFSG.Open.IsQuasisimple ↥L) (hT3 : IsThreeType ↥L)
    (hC : centralizer (L : Set X) = ⊥) {Q E : Subgroup X} (hEQ : E ≤ Q) (hEel : IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) {e : X} (heE : e ∈ E) (hne : e ≠ 1)
    (hfield : ∀ k : ℕ, IsFieldAutThree (MulAut.conjNormal (e ^ k) : MulAut ↥L)) :
    L ≤ K2.gammaQ Q := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have he3 : e ^ 3 = 1 := hEel.2 e heE
  have heord : orderOf e = 3 := orderOf_eq_prime he3 hne
  obtain ⟨d, hdE, hd⟩ : ∃ d ∈ E, d ∉ zpowers e := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ zpowers e := fun g hg => hcon g hg
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, heord, hE27] at h1
    omega
  have hcomm : ∀ a b : X, a ∈ E → b ∈ E → a * b = b * a := fun a b ha hb =>
    congrArg Subtype.val (hEel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set B₀ : Subgroup X := closure ({e, d} : Set X) with hB₀
  have hB₀E : B₀ ≤ E := by
    rw [hB₀, closure_le]
    intro a ha
    rcases ha with rfl | ha
    · exact heE
    · rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hdE
  have hB₀card : Nat.card B₀ = 3 ^ 2 :=
    CFSG.LieType.SeitzGeneration.card_closure_pair_of_not_mem Nat.prime_three hEel heE hdE hne hd
  have hB₀el : IsElemAbelian 3 B₀ := by
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · intro a ha b hb
      have haE : a ∈ E := by
        rcases ha with rfl | ha
        · exact heE
        · rw [Set.mem_singleton_iff] at ha
          rw [ha]
          exact hdE
      have hbE : b ∈ E := by
        rcases hb with rfl | hb
        · exact heE
        · rw [Set.mem_singleton_iff] at hb
          rw [hb]
          exact hdE
      exact hcomm a b haE hbE
    · intro a ha
      have haE : a ∈ E := by
        rcases ha with rfl | ha
        · exact heE
        · rw [Set.mem_singleton_iff] at ha
          rw [ha]
          exact hdE
      exact hEel.2 a haE
  have heB₀ : e ∈ B₀ := subset_closure (by simp)
  let ρ : ↥B₀ →* MulAut ↥L := (MulAut.conjNormal : X →* MulAut ↥L).comp B₀.subtype
  have hρ : ∀ b : ↥B₀, ρ b = MulAut.conjNormal (b : X) := fun b => rfl
  let H : Subgroup ↥B₀ := (zpowers e).subgroupOf B₀
  have hHcard : Nat.card H = 3 := by
    have h1 : Nat.card H = Nat.card (zpowers e) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_le.2 heB₀)).toEquiv
    rw [h1, Nat.card_zpowers, heord]
  have hH : Nat.card ↥B₀ = 3 * Nat.card H := by
    rw [hB₀card, hHcard]
    norm_num
  have hHf : ∀ h ∈ H, IsFieldAutThree (ρ h) := by
    intro h hh
    have hmem : (h : X) ∈ zpowers e := hh
    rw [mem_zpowers_iff_mem_range_orderOf] at hmem
    obtain ⟨k, hk, hkh⟩ := Finset.mem_image.mp hmem
    rw [hρ, ← hkh]
    exact hfield k
  have hBel : IsElemAbelian 3 (⊤ : Subgroup ↥B₀) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hB₀el.1.is_comm.comm a.1 b.1)⟩⟩, fun x _ => ?_⟩
    exact Subtype.ext (by simpa using hB₀el.2 (x : X) x.2)
  have hmain := h2316 ↥L hq hT3 ↥B₀ ρ hBel ⟨H, hH, hHf⟩
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥B₀) = 2 := by
    refine CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_eq_of_card
      (by norm_num) hBel (k := 2) ?_
    rw [Subgroup.card_top, hB₀card]
  have hfix : ∀ E' : Subgroup ↥B₀, CFSG.Open.pRank 3 (⊤ : Subgroup ↥B₀) - 1 ≤
      CFSG.Open.pRank 3 E' →
      Lemma54Ns.fixedSubgroup ρ E' ≤ (K2.gammaQ Q).comap L.subtype := by
    intro E' hE'
    rw [hrank] at hE'
    have hE'ne : E' ≠ ⊥ := by
      intro hbot
      rw [hbot] at hE'
      obtain ⟨E'', hE''le, -, hE''card⟩ :=
        CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊥ : Subgroup ↥B₀)
      have hle : E'' = ⊥ := le_bot_iff.mp hE''le
      rw [hle, Subgroup.card_bot] at hE''card
      have h3 : CFSG.Open.pRank 3 (⊥ : Subgroup ↥B₀) = 0 := by
        have h31 : (3 : ℕ) ^ CFSG.Open.pRank 3 (⊥ : Subgroup ↥B₀) = 1 := hE''card.symm
        exact (Nat.pow_eq_one.mp h31).resolve_left (by norm_num)
      omega
    set S : Subgroup X := E'.map B₀.subtype with hS
    have hSE : S ≤ E := by
      rintro _ ⟨b, -, rfl⟩
      exact hB₀E b.2
    have hSne : S ≠ ⊥ := by
      intro hbot
      apply hE'ne
      rw [eq_bot_iff]
      intro b hb
      have : (b : X) ∈ S := ⟨b, hb, rfl⟩
      rw [hbot, mem_bot] at this
      exact (mem_bot.mpr (Subtype.ext this))
    intro k hk
    have hkC : (k : X) ∈ centralizer (S : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have h1 := hk b hb
      have h2 := congrArg (fun t : ↥L => (t : X)) h1
      simp only [hρ, MulAut.conjNormal_apply] at h2
      change (b : X) * (k : X) * (b : X)⁻¹ = (k : X) at h2
      calc (b : X) * (k : X) = ((b : X) * (k : X) * (b : X)⁻¹) * (b : X) := by group
        _ = (k : X) * (b : X) := by rw [h2]
    have hkN : (k : X) ∈ normalizer (S : Set X) :=
      (Subgroup.centralizer_le_normalizer (S : Set X)) hkC
    have : normalizer (S : Set X) ≤ K2.gammaQ Q := by
      refine le_sup_of_le_right ?_
      exact le_iSup₂_of_le S ⟨E, hEQ, hEel, hE27, hSE, hSne⟩ le_rfl
    exact this hkN
  have htop : (⊤ : Subgroup ↥L) ≤ (K2.gammaQ Q).comap L.subtype :=
    hmain.trans (iSup₂_le fun E' hE' => hfix E' hE')
  intro l hl
  exact htop (Subgroup.mem_top (⟨l, hl⟩ : ↥L))

theorem k2_isQuasisimple_of_simple {S : Type} [Group S] [hS : IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : CFSG.Open.IsQuasisimple S := by
  have hcomm : commutator S = ⊤ := by
    rcases (Subgroup.commutator_normal (⊤ : Subgroup S) (⊤ : Subgroup S)).eq_bot_or_eq_top with
      h | h
    · obtain ⟨a, b, hab⟩ := hnab
      exact (hab (isMulCommutative_iff.mp ((commutator_eq_bot_iff S).mp h) a b)).elim
    · exact h
  have hcenter : Subgroup.center S = ⊥ := by
    rcases (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center S := by rw [h]; exact Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.mp hb a)
  refine ⟨hcomm, ?_⟩
  let e : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact MulEquiv.isSimpleGroup e

theorem le_gammaQ_of_typeL3 (hF2 : InnDiagRankTwo) (hFs : Field3Structure)
    (h2316 : Input23_16Three) {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]
    (hq : CFSG.Open.IsQuasisimple ↥L) (hT : IsLThreeEps (↥L ⧸ center ↥L))
    (hC : centralizer (L : Set X) = ⊥) {Q : Sylow 3 X}
    (hQ : 3 ≤ CFSG.Open.pRank 3 (Q : Subgroup X)) : L ≤ K2.gammaQ (Q : Subgroup X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEQ, hEel, hE27⟩ := CFSG.AGLEmbedding.KFactProofs.G28.exists_elemAbelian_27 hQ
  have hinj : Function.Injective (MulAut.conjNormal : X →* MulAut ↥L) :=
    conjNormal_injective_of_centralizer_eq_bot L hC
  have hÊel : IsElemAbelian 3 (E.map (MulAut.conjNormal : X →* MulAut ↥L)) :=
    hEel.map _
  have hÊ27 : Nat.card (E.map (MulAut.conjNormal : X →* MulAut ↥L)) = 27 := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hE27
  obtain ⟨α, hαE, hα1, hαfield⟩ := exists_field_aut_of_E27 hF2 hFs hq hT hÊel hÊ27
  obtain ⟨e, heE, rfl⟩ := Subgroup.mem_map.mp hαE
  have hne : e ≠ 1 := fun h => hα1 (by rw [h, map_one])
  have hfield : ∀ k : ℕ, IsFieldAutThree (MulAut.conjNormal (e ^ k) : MulAut ↥L) := fun k => by
    rw [map_pow]
    exact hαfield k
  exact le_gammaQ_of_field_aut h2316 hq (isThreeType_of_isLThreeEps hT) hC (hEQ.trans le_rfl)
    hEel hE27 heE hne hfield

theorem kfactRankThreeCore_of_T29 (hT : GL83I291Three) (hF2 : InnDiagRankTwo)
    (h2316 : Input23_16Three) : K2.KFactRankThreeCore := by
  intro X _ _ hcat hcore L hLn hLs hLnab hC Q hQ hx hnot
  haveI hLn' : L.Normal := hLn
  haveI hLs' : IsSimpleGroup ↥L := hLs
  obtain ⟨x, hxo, hxc⟩ := hx
  have hq : CFSG.Open.IsQuasisimple ↥L := k2_isQuasisimple_of_simple hLnab
  have hcomp : IsComponentOf L ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal hLn'), hq⟩
  have huniq : ∀ K : Subgroup X, IsComponentOf K ⊤ → K = L := by
    intro K hK
    by_contra hne
    have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne K L hK hcomp hne
    have hKC : K ≤ centralizer (L : Set X) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    rw [hC, le_bot_iff] at hKC
    exact ne_bot_of_isQuasisimple K hK.2.2 hKC
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    hQ.trans (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) le_top)
  obtain ⟨-, -, -, hconc⟩ := hT X hcat hcore L hcomp huniq hrank x hxo hxc
  rcases hconc with ⟨hLε, -, -, -, -⟩ | hb
  · exfalso
    exact hnot (le_gammaQ_of_typeL3 hF2
      CFSG.HardMathSupport.Solomon.Coordinator.field3Structure_holds h2316 hq hLε hC hQ)
  · obtain ⟨e, -, -⟩ := id hb
    exact ⟨⟨e⟩, index_eq_of_fieldAut_L227 hC hb⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
