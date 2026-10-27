module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCenter
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd414
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Layer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB

theorem lieModel_S :
    Blueprint.LieModel ↥PSL3Four.S .PSL 3 2 2 := by
  obtain ⟨hadm, F, hF, hfin, hcard, ⟨e⟩⟩ := PSL3Four.statedClassicalModel_S
  exact Or.inl ⟨by decide, hadm, F, hF, hfin, hcard, ⟨e⟩⟩

namespace LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem isL34Type (hL : LLayer hs π) :
    GrSLit.IsL34Type (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
      Open.fusionZStar ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := by
  have e₁ := QuotientGroup.quotientKerEquivOfSurjective π hL.surj
  have e₀ := QuotientGroup.quotientMulEquivOfEq hL.ker.symm
  have e₂ := QuotientGroup.quotientMulEquivOfEq
    (Setting46e.fusionZStar_layer_eq_center (w ^ (orderOf w / 2) * t ^ i * z ^ j))
  exact GSThmB.OddQuot.lieModel_of_equiv ((e₂.trans e₀).trans e₁).symm lieModel_S

theorem zStarIn_eq :
    GrSLit.zStarIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) =
      (center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))).map
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype := by
  rw [GrSLit.zStarIn, Setting46e.fusionZStar_layer_eq_center]

theorem center_le_pCore (hL : LLayer hs π) :
    (center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))).map
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype ≤
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  rintro _ ⟨c, hc, rfl⟩
  rw [← hs.centralizer_layer_eq hL.h412, mem_centralizer_iff]
  intro e he
  have := congrArg Subtype.val (mem_center_iff.mp hc ⟨e, he⟩)
  simpa using this

theorem isPGroup_center (hL : LLayer hs π) :
    IsPGroup 2 ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := by
  have h := (pCore_isPGroup (p := 2)
    (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).to_le hL.center_le_pCore
  exact h.of_equiv ((center _).equivMapOfInjective _ (subtype_injective _)).symm

theorem center_pow_four
    (hL : LLayer hs π)
    (c : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    (hc : c ∈ center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) : c ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := (hL.isPGroup_center).exists_le_sylow
  have hP : GrSLit.IsSylowTwoIn ((P₀ : Subgroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i *
      z ^ j)))).map (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype)
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
    ⟨map_subtype_le _, P₀, by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (subtype_injective _)]⟩
  have hcP : (c : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      (P₀ : Subgroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))).map
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype ⊓
      GrSLit.zStarIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    rw [zStarIn_eq]
    exact ⟨⟨c, hP₀ hc, rfl⟩, ⟨c, hc, rfl⟩⟩
  have hperf : ⁅layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁆ =
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
    Subgroup.isPerfect_iff.mp hL.isPerfect
  have h := GrSLit.L34Facts.l34CenterExponentFact (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) _ hperf hL.isL34Type hP _ hcP
  exact Subtype.ext (by simpa using h)

theorem _root_.CFSG.ComponentClassification.HarrisLit.EndB.card_center_dihedral_two_pow
    {k : ℕ} (hk : 2 ≤ k) : Nat.card (center (DihedralGroup (2 ^ k))) = 2 := by
  have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hn : (2 : ℕ) ^ k ≠ 2 := by
    intro h
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  rw [DihedralGroup.center_eq_closure_of_even_ne_two (even_iff_two_dvd.2 h2) hn,
    Nat.card_zpowers, DihedralGroup.orderOf_r]
  have hlt : 2 ^ k / 2 < 2 ^ k := Nat.div_lt_self (by positivity) (by norm_num)
  rw [ZMod.val_natCast_of_lt hlt, Nat.gcd_eq_right (Nat.div_dvd_of_dvd h2),
    Nat.div_div_self h2 (by positivity)]

theorem center_cases
    (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥) :
    Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2 ∨
      (Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 4 ∧
        IsCyclic ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ∧
        IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ∨
      (Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 4 ∧
        (center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))).map
            (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype =
          pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
  set E := layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hE
  set Q := pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hQ
  have hZQ := hL.center_le_pCore
  have hcardZ : Nat.card ↥((center ↥E).map E.subtype) = Nat.card ↥(center ↥E) :=
    Subgroup.card_map_of_injective (subtype_injective _)
  have h1 : 1 < Nat.card ↥(center ↥E) := by
    rw [← Subgroup.one_lt_card_iff_ne_bot] at hZ
    exact hZ
  let eZ : ↥(center ↥E) ≃* ↥(((center ↥E).map E.subtype).subgroupOf Q) :=
    ((center ↥E).equivMapOfInjective _ (subtype_injective _)).trans
      (subgroupOfEquivOfLe hZQ).symm
  rcases hL.h412.pCore_shape with hcyc | ⟨k, hk, ⟨e⟩⟩
  ·
    have hZc : IsCyclic ↥(center ↥E) := isCyclic_of_surjective eZ.symm.toMonoidHom
      eZ.symm.surjective
    obtain ⟨g, hg⟩ := hZc.exists_generator
    have hog : orderOf g = Nat.card ↥(center ↥E) := orderOf_eq_card_of_forall_mem_zpowers hg
    have h4 : g ^ 4 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hL.center_pow_four _ g.2, Subgroup.coe_one])
    have hdvd : Nat.card ↥(center ↥E) ∣ 4 := hog ▸ orderOf_dvd_of_pow_eq_one h4
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card ↥(center ↥E)
    · exact Or.inl rfl
    · exact absurd hdvd (by norm_num)
    · exact Or.inr (Or.inl ⟨rfl, hZc, hcyc⟩)
  ·
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    ·
      have hk1 : k = 1 := by omega
      subst hk1
      have hQ4 : Nat.card ↥Q = 4 := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
        norm_num
      have hdvd := Subgroup.card_dvd_of_le hZQ
      rw [hcardZ, hQ4] at hdvd
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : Nat.card ↥(center ↥E)
      · exact Or.inl rfl
      · exact absurd hdvd (by norm_num)
      · refine Or.inr (Or.inr ⟨rfl, Subgroup.eq_of_le_of_card_ge hZQ ?_⟩)
        rw [hcardZ, hQ4]
    ·
      refine Or.inl (le_antisymm (le_of_le_of_eq ?_ (card_center_dihedral_two_pow hk2)) h1)
      refine Nat.card_le_card_of_injective (fun c => ⟨e (eZ c), ?_⟩) fun a b hab => ?_
      · rw [mem_center_iff]
        intro d
        obtain ⟨q, rfl⟩ := e.surjective d
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        have hq := mem_centralizer_iff.mp
          (show (q : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈ centralizer (E : Set _) by
            rw [hs.centralizer_layer_eq hL.h412]; exact q.2)
        exact (hq _ (map_subtype_le _ (eZ c).2)).symm
      · have h := congrArg Subtype.val hab
        simp only at h
        exact eZ.injective (Subtype.ext (e.injective h))

end LLayer

end EndB

end CFSG.ComponentClassification.HarrisLit
