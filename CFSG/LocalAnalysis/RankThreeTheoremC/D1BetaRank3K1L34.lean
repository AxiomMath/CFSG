module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34ModelS
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Three
import CFSG.LocalAnalysis.RankThreeTheoremC.D1BetaRank3K1Out
import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryComplements
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34OuterDefs
public import Certificates.Data.L34OuterData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

theorem exists_pair_complement {G : Type} [Group G] [Finite G] {P F : Subgroup G}
    (hP : IsElemAbelian 3 P) (hc : Nat.card P = 27) (hFP : F ≤ P) (hF : Nat.card F = 3) :
    ∃ x ∈ P, ∃ y ∈ P, Nat.card (Subgroup.closure {x, y}) = 9 ∧
      F ⊓ Subgroup.closure {x, y} = ⊥ := by
  have : IsMulCommutative P := hP.1
  let _ : CommGroup P := { (inferInstance : Group P) with mul_comm := mul_comm' }
  obtain ⟨C', hC'⟩ := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isCompl_exists 3
    Nat.prime_three P (fun x => Subtype.ext (by simpa using hP.2 x x.2)) (F.subgroupOf P)
  have hsup := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (F.subgroupOf P) C' (by rw [Subgroup.normalizer_eq_top]; exact le_top) hC'.disjoint
  rw [hC'.sup_eq_top, Subgroup.card_top, hc,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFP).toEquiv, hF] at hsup
  have hC9 : Nat.card C' = 9 := by omega
  set C : Subgroup G := C'.map P.subtype with hCdef
  have hCP : C ≤ P := Subgroup.map_subtype_le C'
  have hCcard : Nat.card C = 9 := by
    rw [hCdef, Subgroup.card_map_of_injective P.subtype_injective, hC9]
  have hC3 : ∀ x ∈ C, x ^ 3 = 1 := fun x hx => hP.2 x (hCP hx)
  obtain ⟨x, hx, y, hy, hxy⟩ := CFSG.AGLEmbeddingD2.exists_pair_closure hCcard hC3
  refine ⟨x, hCP hx, y, hCP hy, by rw [hxy, hCcard], ?_⟩
  rw [hxy, eq_bot_iff]
  rintro g ⟨hgF, hgC⟩
  obtain ⟨c, hc', rfl⟩ := hgC
  have hcF : c ∈ F.subgroupOf P := hgF
  have : c ∈ F.subgroupOf P ⊓ C' := ⟨hcF, hc'⟩
  rw [hC'.disjoint.eq_bot, Subgroup.mem_bot] at this
  simp [this]

theorem false_of_forall_pair {G : Type} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsElemAbelian 3 P) (hc : Nat.card P = 27) {z : G} (hz1 : z ≠ 1)
    (hz : ∀ x ∈ P, ∀ y ∈ P, Nat.card (Subgroup.closure {x, y}) = 9 →
      z ∈ Subgroup.closure {x, y}) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : ∀ x ∈ P, x ≠ 1 → Nat.card (Subgroup.zpowers x) = 3 := fun x hx hx1 => by
    rw [Nat.card_zpowers, orderOf_eq_prime (hP.2 x hx) hx1]
  have hzP : z ∈ P := by
    have hPbot : P ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hc
      omega
    obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hPbot
    have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
    obtain ⟨x, hx, y, hy, h9, -⟩ := exists_pair_complement hP hc (Subgroup.zpowers_le.2 hx₀)
      (hcard x₀ hx₀ hx₀1')
    have hle : Subgroup.closure {x, y} ≤ P := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      exacts [hx, hy]
    exact hle (hz x hx y hy h9)
  obtain ⟨x, hx, y, hy, h9, hdisj⟩ := exists_pair_complement hP hc (Subgroup.zpowers_le.2 hzP)
    (hcard z hzP hz1)
  have h : z ∈ Subgroup.zpowers z ⊓ Subgroup.closure {x, y} :=
    ⟨Subgroup.mem_zpowers z, hz x hx y hy h9⟩
  rw [hdisj, Subgroup.mem_bot] at h
  exact hz1 h

open CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.L34Outer in
theorem card_le_nine_of_isElemAbelian_R
    (E : Subgroup ↥R) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have facts := CFSG.AGLEmbeddingD2.l34_outer_check
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_of_openIsElemAbelian hE)
  have hdvd : 3 ^ k ∣ 241920 := card_R ▸ hk ▸ Subgroup.card_subgroup_dvd_card E
  have hk3 : k ≤ 3 := by
    by_contra hlt
    have h81 : 3 ^ 4 ∣ 241920 := (pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at h81
  by_contra hgt
  have hE27 : Nat.card E = 27 := by
    interval_cases k <;> simp_all
  set A : Subgroup (Equiv.Perm (Fin 42)) := E.map R.subtype with hA
  have hAe : IsElemAbelian 3 A := CFSG.SectionRank.isElemAbelian_map hE R.subtype
  have hAcard : Nat.card A = 27 := by
    rw [hA, Subgroup.card_map_of_injective R.subtype_injective, hE27]
  have hAT : A ≤ L34T := by
    rintro _ ⟨e, he, rfl⟩
    have h3 : (e : Equiv.Perm (Fin 42)) ^ 3 = 1 := by
      simpa using congrArg Subtype.val (hE.2 e he)
    exact facts.order3 e e.2 h3
  obtain ⟨c, hcT, hc⟩ := CFSG.AGLEmbeddingD2.exists_conj_le_P facts.P_le_T facts.cardP
    facts.cardT hAT hAe.2
  set A' : Subgroup (Equiv.Perm (Fin 42)) := A.map (MulAut.conj c⁻¹).toMonoidHom with hA'
  have hA'P : A' ≤ Psub Certificates.L34Outer.l34OuterData := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hc x hx
  have hA'card : Nat.card A' = 27 := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hAcard]
  have hPeq : A' = Psub Certificates.L34Outer.l34OuterData :=
    Subgroup.eq_of_le_of_card_ge hA'P (by rw [hA'card, facts.cardP])
  have hPe : IsElemAbelian 3 (Psub Certificates.L34Outer.l34OuterData) :=
    hPeq ▸ CFSG.SectionRank.isElemAbelian_map hAe (MulAut.conj c⁻¹).toMonoidHom
  refine false_of_forall_pair hPe facts.cardP facts.z_ne fun x hx y hy h9 => ?_
  obtain ⟨e, he, heq⟩ := facts.pairs x hx y hy h9
  rw [heq]
  exact facts.z_mem e he

theorem pRank_mulAut_le_two_of_isLinThreeFour
    {K : Type} [Group K] [Finite K]
    (h : CFSG.AGLEmbedding.IsLinThreeFour K) :
    Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  obtain ⟨θ⟩ := CFSG.AGLEmbedding.KFactProofs.L34ModelS.nonempty_mulEquiv_S_of_isLinThreeFour h
  obtain ⟨eR, -, -⟩ := CFSG.ComponentClassification.PSL3Four.full_automorphism_action
  have h1 : (1 : ℕ) < 3 := by norm_num
  rw [SectionRank.pRank_top_eq_of_mulEquiv h1 ((MulAut.congr θ).trans eR.symm)]
  exact SectionRank.pRank_le h1 fun E _ hE => by
    simpa using card_le_nine_of_isElemAbelian_R E hE

end CFSG.LocalAnalysis.RankThreeTheoremC
