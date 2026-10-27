module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosCover
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinTorus
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenFive
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.Open CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

namespace LeviBlock

variable {p f : ℕ} {K : Type} [Field K] {t s ε : ℕ}

theorem six_le_of_three_le_card_uniBlock {I : Finset ℕ} (hI : IsTopCut I t)
    (h3 : 3 ≤ Nat.card {b : ↥I // b.1 - predCut I b.1 = 2}) : 6 ≤ t := by
  let φ : {b : ↥I // b.1 - predCut I b.1 = 2} × Fin 2 → Fin t := fun x =>
    ⟨x.1.1.1 - 2 + x.2, by
      have := (hI.le _ x.1.1.2).2
      have := x.1.2
      have := x.2.isLt
      omega⟩
  have hφ : Function.Injective φ := by
    rintro ⟨⟨⟨b, hb⟩, hb2⟩, i⟩ ⟨⟨⟨b', hb'⟩, hb2'⟩, i'⟩ he
    change b - predCut I b = 2 at hb2
    change b' - predCut I b' = 2 at hb2'
    have he' : b - 2 + i = b' - 2 + i' := congrArg Fin.val he
    have hi := i.isLt
    have hi' := i'.isLt
    obtain rfl : b = b' := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := le_predCut hb hlt
        omega
      · have := le_predCut hb' hlt
        omega
    exact Prod.ext rfl (Fin.ext (show (i : ℕ) = i' by omega))
  have h := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, Nat.card_fin] at h
  omega

theorem three_le_card_uniBlock_two (h : UnitaryFieldData 2 1 K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t)
    (h3 : 3 ≤ Nat.card {j // CFSG.Open.IsQuasisimple (uniBlockSub (s := s) (ε := ε) h I j) ∧
      Nat.card (↥(uniBlockSub (s := s) (ε := ε) h I j) ⧸
        Subgroup.center ↥(uniBlockSub (s := s) (ε := ε) h I j)) = 60}) :
    3 ≤ Nat.card {b : ↥I // b.1 - predCut I b.1 = 2} := by
  have hsome : ∀ j, (CFSG.Open.IsQuasisimple (uniBlockSub (s := s) (ε := ε) h I j) ∧
      Nat.card (↥(uniBlockSub (s := s) (ε := ε) h I j) ⧸
        Subgroup.center ↥(uniBlockSub (s := s) (ε := ε) h I j)) = 60) →
      ∃ b : ↥I, j = some b ∧ b.1 - predCut I b.1 = 2 := by
    rintro (_ | b) ⟨hq, h60⟩
    · exfalso
      rw [(uniBlockSub_facts h hε hI none).2 hq] at h60
      change ordTwistedA (2 * s + ε - 1) (2 ^ 1) = 60 at h60
      exact absurd ((ordTwistedA_eq_sixty_iff (f := 1) rfl).mp h60).2 (by norm_num)
    · rw [(uniBlockSub_facts h hε hI (some b)).2 hq] at h60
      change ordA (b.1 - predCut I b.1 - 1) ((2 ^ 1) ^ 2) = 60 at h60
      have h1 := ((ordA_eq_sixty_iff (f := 2) (by norm_num)).mp h60).1
      have := predCut_lt (I := I) (hI.le b.1 b.2).1
      exact ⟨b, rfl, by omega⟩
  choose F hF hF2 using hsome
  refine h3.trans (Nat.card_le_card_of_injective (fun x => ⟨F x.1 x.2, hF2 x.1 x.2⟩) ?_)
  intro x y hxy
  have he : F x.1 x.2 = F y.1 y.2 := congrArg Subtype.val hxy
  exact Subtype.ext (by rw [hF x.1 x.2, hF y.1 y.2, he])

theorem torusRatio_torusFourVec (h : UnitaryFieldData p f K) {r : ℕ} (hr : 5 ≤ r)
    (x : Fin 4 → Kˣ) : torusRatio (ε := ε) h (torusFourVec (n := r) x) 1 = 1 := by
  rw [torusRatio, Finset.prod_div_distrib, ← map_prod, ← Units.coe_prod, prod_torusFourVec hr]
  simp

@[expose] noncomputable def uniTorusFour (h : UnitaryFieldData p f K) {r : ℕ} (hr : 5 ≤ r) :
    (Fin 4 → Kˣ) →* hypSU h r ε :=
  MonoidHom.mk' (fun x => mkHypSU h (diagonal (torusEntries h (torusFourVec x) 1))
      (diagonal_torusEntries_isometry h _ fun k => by simp [UnitaryFieldData.norm])
      (by rw [det_diagonal_torusEntries, torusRatio_torusFourVec h hr]))
    fun x y => Subtype.ext (Units.ext (by
      change diagonal _ = diagonal _ * diagonal _
      rw [diagonal_mul_diagonal, torusFourVec_mul]
      congr 1
      funext a
      rcases a with i | k | i <;> simp [torusEntries, mul_comm]))

theorem uniTorusFour_mem_hypTorus (h : UnitaryFieldData p f K) {r : ℕ} (hr : 5 ≤ r)
    (x : Fin 4 → Kˣ) : uniTorusFour (ε := ε) h hr x ∈ hypTorus h r ε :=
  ⟨torusFourVec x, 1, fun k => by simp [UnitaryFieldData.norm], torusRatio_torusFourVec h hr x,
    rfl⟩

theorem eq_one_of_uniTorusFour_mem_hypScalars (h : UnitaryFieldData p f K) {r : ℕ} (hr : 6 ≤ r)
    {x : Fin 4 → Kˣ} (hx : uniTorusFour (ε := ε) h (by omega) x ∈ hypScalars h r ε) : x = 1 := by
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.mp hx
  have hM : diagonal (torusEntries h (torusFourVec (n := r) x) (1 : Fin ε → Kˣ)) =
      Matrix.scalar _ (c : K) := congrArg Units.val hc
  have e5 := congrFun (congrFun hM (.inl ⟨5, by omega⟩)) (.inl ⟨5, by omega⟩)
  simp [torusEntries, torusFourVec] at e5
  funext j
  have ej := congrFun (congrFun hM (.inl ⟨j, by omega⟩)) (.inl ⟨j, by omega⟩)
  simp [torusEntries, torusFourVec, ← e5] at ej
  simpa using ej

theorem four_le_pRank_of_uniTorusFour {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (h : UnitaryFieldData 2 1 K) {I : Finset ℕ} (hI : IsTopCut I t) (ht : 6 ≤ t)
    (ρ : hypSU h (t + s) ε →* ↥L)
    (hZ : ∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h (t + s) ε) (g : hypSU h (t + s) ε)
    (hJ : ∀ y, y ∈ (P.subgroupOf L).comap ρ ↔
      ∀ i ∈ (↑I : Set ℕ), y • (g • hypFlag h (t + s) ε i) = g • hypFlag h (t + s) ε i) :
    4 ≤ CFSG.Open.pRank 3 P := by
  have : Finite K := h.finite
  have hr5 : 5 ≤ t + s := by omega
  obtain ⟨φ, hinj, hrange⟩ := exists_injective_of_hypFlag ρ hZ g hJ (uniTorusFour (ε := ε) h hr5)
    (fun x => hypBorel_le_flagStabilizer
      (fun i hi => ⟨(hI.le i hi).1, (hI.le i hi).2.trans (Nat.le_add_right t s)⟩)
      (hypTorus_le_hypBorel h (uniTorusFour_mem_hypTorus h hr5 x)))
    fun x hx => eq_one_of_uniTorusFour_mem_hypScalars h (by omega) hx
  have hunits : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, h.card]
    norm_num
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun a b => mul_comm a b)
    (fun a => ?_) ?_ φ hinj hrange
  · funext j
    rw [Pi.pow_apply, Pi.one_apply, ← hunits]
    exact pow_card_eq_one'
  · rw [Nat.card_fun, hunits, Nat.card_fin]

end LeviBlock

open LeviBlock


theorem kFactCompParabThreeFivesOn_unitary_two :
    KFactCompParabThreeFivesOn (IsLieOf (IdxTwistedAAt 2)) := by
  intro Y _ _ L P hCP hC O J _ hPO _ hsec hJ hJc
  obtain ⟨d, hd, ⟨e⟩⟩ := hC
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, g, hε, hI, hq, hρ, hZ, hJ'⟩ :=
    exists_uniFlag_dim_of_compParab hCP d (idxTwistedA_of_at hd) e
  have hf2 : 2 ^ f = 2 := two_pow_eq_of_at hd fun r₀ q h₀ => (hq r₀ q h₀).1
  obtain rfl : f = 1 := Nat.pow_right_injective le_rfl (hf2.trans (by norm_num))
  have : Finite K := h.finite
  set β := uniLeviHom (s := s) h hε hI
  set e' := stabMulEquiv g hJ'
  have hrange : (β.comp e'.toMonoidHom).range = β.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_map (e'.toMonoidHom),
      Subgroup.map_top_of_surjective _ e'.surjective, ← MonoidHom.range_eq_map]
  have h3 := three_le_card_fiveBlocks_of_cover hCP.parab.1 ρ hρ (β.comp e'.toMonoidHom)
    ((isPGroup_ker_uniLeviHom h hε hI).comap_of_injective e'.toMonoidHom e'.injective)
    (hrange ▸ pi_uniBlockSub_le_range h hε hI) (hrange ▸ commutator_range_le_pi h hε hI)
    (fun j => (uniBlockSub_facts h hε hI j).1)
    (fun j hq h60 => card_uniBlockSub_of_sixty h hε hI j hq h60) hPO hsec hJ hJc
  exact four_le_pRank_of_uniTorusFour h hI
    (six_le_of_three_le_card_uniBlock hI (three_le_card_uniBlock_two h hε hI h3)) ρ hZ g hJ'

theorem kFactCompParabThreeFivesOn_twistedA : KFactCompParabThreeFivesOn (IsLieOf IdxTwistedA) :=
  kFactCompParabThreeFivesOn_twistedA_of kFactCompParabThreeFivesOn_unitary_two

end CFSG.AGLEmbedding
