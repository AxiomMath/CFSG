module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndSetting
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndJ3

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup HarrisEnd Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

theorem HarrisEnd.card_eq_2448_of_lieModel_dvd {Z : Type} [Group Z] {p m : ℕ} (hp2 : p ≠ 2)
    (h16 : 16 ∣ p ^ (2 * m) - 1) (h : Blueprint.LieModel Z .PSL 2 p m)
    (hdvd : Nat.card Z ∣ 2448) : Nat.card Z = 2448 := by
  obtain ⟨hp, -, h4, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel h
  rw [Nat.card_congr e.toEquiv, SectionRank.OddCover.card_psl_two hp hp2 hF] at hdvd ⊢
  set q := p ^ m with hq
  have hq2 : p ^ (2 * m) = q ^ 2 := by rw [hq, ← pow_mul, mul_comm]
  rw [hq2] at h16
  have hq17 : q ≤ 17 := by
    by_contra hlt
    have h1 : 324 ≤ q ^ 2 := by nlinarith
    have h2 : 161 ≤ (q ^ 2 - 1) / 2 := by omega
    have h3 : 18 * 161 ≤ q * ((q ^ 2 - 1) / 2) := Nat.mul_le_mul (by omega) h2
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases q
  all_goals (revert h16 hdvd; decide)

namespace Setting46e

theorem list_of_simple (hin : Harris36SimpleInput) (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (h47 : IsLemma47 p (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    [IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))] :
    conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
        innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
      (Nonempty (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≃*
          Blueprint.NativeSporadic.J2) ∨
        Nonempty (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≃*
          Blueprint.NativeSporadic.J3) ∨
        Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 3 2 2 ∨
        Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 3 p
          (f / 2) ∨
        Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSU 3 p
          (f / 2) ∨
        Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 2 p
          (2 * (f / 2))) := by
  have hK := hs.lieModel_KBar h412
  rw [← h412.layerIn_layer_centralizer] at hK
  exact HarrisEnd.list_of_simple hin hs.tBar_sq (hs.tBar_not_mem_centralizer_layer h412)
    (betaBar_mem_center _) hs.betaBar_sq hs.betaBar_ne_one hs.prime_p hs.p_ne_two
    hs.one_le_half hs.sixteen_dvd (hs.isOfType_layer_of_isSimpleGroup h412)
    (hs.not_lieModel_L4U4_of_isSimpleGroup h412 h47) hK
    (fun P hP hP2 => hs.exists_closure_card_le_four hP hP2)

theorem not_J3 (hin : Harris36SimpleInput) (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (h47 : IsLemma47 p (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    [IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))] :
    ¬ Nonempty (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≃*
      Blueprint.NativeSporadic.J3) := by
  intro hY
  have hK := hs.lieModel_KBar h412
  have hKnab := nonabelian_of_lieModel_psl2 hK
  have hKd := hasDihedralSylowTwo_of_lieModel_psl2 hs.p_ne_two hK
  obtain ⟨d, hd, e, he, hde, hK2⟩ := hs.exists_orderOf_eq_twoPart_KBar h412
  have hout := (hs.list_of_simple hin h412 h47).1
  have htb := hs.tBar_not_mem_centralizer_layer h412
  have hτ2 : orderOf (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
      (hs.setup.tBar i j)) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, hs.tBar_sq, map_one])
      fun h => htb (conjOn_eq_one_iff.mp h)
  obtain ⟨hall, h2448⟩ := j3_outer_facts hY hτ2 hout
  have hcard : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 2448 := by
    rw [← map_fixedPoints_conjOn, Subgroup.card_map_of_injective (subtype_injective _), h2448]
  have hKle : KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hs.setup.tBar i j} := by
    rw [← h412.layerIn_layer_centralizer]
    exact map_subtype_le _
  have hKcard := card_eq_2448_of_lieModel_dvd hs.p_ne_two hs.sixteen_dvd hK
    (by rw [← hcard]; exact Subgroup.card_dvd_of_le hKle)
  have hKeq : layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j} = GSThmB.layerIn
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hs.setup.tBar i j}) := by
    rw [h412.layerIn_layer_centralizer]
    exact (Subgroup.eq_of_le_of_card_ge hKle (by rw [hcard, hKcard])).symm
  rw [← h412.layerIn_layer_centralizer] at hKnab hKd hK2
  exact HarrisEnd.not_J3 hs.tBar_sq (betaBar_mem_center _) hs.betaBar_sq
    (hs.centralizer_layer_inf_centralizer_tBar h412) hKnab hall hKeq hKd hd (by omega) hde hK2

end Setting46e

@[expose] def Harris413CaseHyp (X : Type) [Group X] [Finite X] (t : X) (L : Subgroup X)
    (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ) : Prop :=
  ∃ hs : Setting46e t L p f S w z V i j,
    IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j) ∧
    (∀ i' j' : ℕ, IsLemma47 p (w ^ (orderOf w / 2) * t ^ i' * z ^ j')) ∧
    IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
    conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
      innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))

@[expose] def Harris413J2Case : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Harris413CaseHyp X t L p f S w z V i j →
      ¬ Nonempty (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≃*
        Blueprint.NativeSporadic.J2)

@[expose] def Harris413L34Case : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Harris413CaseHyp X t L p f S w z V i j →
      ¬ Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 3 2 2

@[expose] def Harris413L3U3Case : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Harris413CaseHyp X t L p f S w z V i j →
      ¬ Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 3 p
          (f / 2) ∧
        ¬ Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSU 3 p
          (f / 2)

@[expose] def Harris413L2Case : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Harris413CaseHyp X t L p f S w z V i j →
      ¬ Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 2 p
        (2 * (f / 2))

theorem harris413_of_cases (hin : Harris36SimpleInput)
    (h412 : Harris412Statement) (h47 : Harris47Input) (hJ2 : Harris413J2Case)
    (hL34 : Harris413L34Case) (hL3 : Harris413L3U3Case) (hL2 : Harris413L2Case) :
    Harris413Input46e := by
  intro X _ _ _ hnonab hK hcat t L p f S w z V i j hs hsimple
  have h412' := h412 X hnonab hK hcat t L p f S w z V i j hs
  have h47' := h47 X hnonab hK hcat t L p f S w z V i j hs
  obtain ⟨hout, hlist⟩ := hs.list_of_simple hin h412' (h47' i j)
  have hhyp : Harris413CaseHyp X t L p f S w z V i j := ⟨hs, h412', h47', hsimple, hout⟩
  rcases hlist with hY | hY | hY | hY | hY | hY
  · exact hJ2 X hnonab hK hcat t L p f S w z V i j hhyp hY
  · exact hs.not_J3 hin h412' (h47' i j) hY
  · exact hL34 X hnonab hK hcat t L p f S w z V i j hhyp hY
  · exact (hL3 X hnonab hK hcat t L p f S w z V i j hhyp).1 hY
  · exact (hL3 X hnonab hK hcat t L p f S w z V i j hhyp).2 hY
  · exact hL2 X hnonab hK hcat t L p f S w z V i j hhyp hY

end CFSG.ComponentClassification.HarrisLit
