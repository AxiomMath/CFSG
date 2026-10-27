module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Basic
public import CFSG.GroupTheory.SolvableHallNodes

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem coprime_of_isPGroup_of_odd {F R : Subgroup G} (hRF : R ≤ F) (hR2 : IsPGroup 2 R)
    (hodd : ¬ 2 ∣ R.relIndex F) :
    Nat.Coprime (Nat.card (R.subgroupOf F)) (R.subgroupOf F).index := by
  have hcard : Nat.card (R.subgroupOf F) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRF).toEquiv
  obtain ⟨e, he⟩ := hR2.exists_card_eq
  rw [hcard, he]
  exact Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)

theorem exists_complement_of_odd {F R : Subgroup G} (hRF : R ≤ F)
    (hN : F ≤ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 R) (hodd : ¬ 2 ∣ R.relIndex F) :
    ∃ B : Subgroup G, B ≤ F ∧ R ⊓ B = ⊥ ∧ ∀ f ∈ F, ∃ r ∈ R, ∃ b ∈ B, f = r * b := by
  have hnorm : (R.subgroupOf F).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRF).2 hN
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime
    (coprime_of_isPGroup_of_odd hRF hR2 hodd)
  refine ⟨H.map F.subtype, Subgroup.map_subtype_le H, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxR, y, hy, rfl⟩
    have hdis := hH.disjoint
    have hx : y ∈ R.subgroupOf F := hxR
    have : y ∈ (R.subgroupOf F) ⊓ H := ⟨hx, hy⟩
    rw [disjoint_iff.1 hdis, Subgroup.mem_bot] at this
    rw [this]
    exact Subgroup.one_mem _
  · intro f hf
    have h1 := Subgroup.IsComplement.equiv_fst_mul_equiv_snd hH ⟨f, hf⟩
    refine ⟨(((hH.equiv ⟨f, hf⟩).1 : F) : G), (hH.equiv ⟨f, hf⟩).1.2, (((hH.equiv ⟨f, hf⟩).2 : F) : G),
      ⟨_, (hH.equiv ⟨f, hf⟩).2.2, rfl⟩, ?_⟩
    have := congrArg Subtype.val h1
    simpa using this.symm

theorem exists_conj_of_complements {F R B B' : Subgroup G} (hRF : R ≤ F)
    (hN : F ≤ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 R) (hodd : ¬ 2 ∣ R.relIndex F)
    (hB : B ≤ F) (hB' : B' ≤ F) (hRB : R ⊓ B = ⊥) (hRB' : R ⊓ B' = ⊥)
    (hFB : ∀ f ∈ F, ∃ r ∈ R, ∃ b ∈ B, f = r * b)
    (hFB' : ∀ f ∈ F, ∃ r ∈ R, ∃ b ∈ B', f = r * b) : ∃ r ∈ R, B' = conjR B r := by
  have hnorm : (R.subgroupOf F).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRF).2 hN
  have hsolv : Group.IsSolvable (R.subgroupOf F) := by
    have hP : IsPGroup 2 (R.subgroupOf F) := hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRF).symm
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := IsPGroup.isNilpotent hP
    infer_instance
  have hmul : ∀ (X : Subgroup G), X ≤ F → (∀ f ∈ F, ∃ r ∈ R, ∃ b ∈ X, f = r * b) →
      ((R.subgroupOf F : Subgroup F) : Set F) * ((X.subgroupOf F : Subgroup F) : Set F) =
        Set.univ := by
    intro X hX hFX
    ext f
    simp only [Set.mem_mul, Set.mem_univ, iff_true]
    obtain ⟨r, hr, b, hb, hfb⟩ := hFX f f.2
    exact ⟨⟨r, hRF hr⟩, hr, ⟨b, hX hb⟩, hb, Subtype.ext hfb.symm⟩
  have hbot : ∀ (X : Subgroup G), R ⊓ X = ⊥ → (R.subgroupOf F) ⊓ (X.subgroupOf F) = ⊥ := by
    intro X hRX
    rw [eq_bot_iff]
    intro y hy
    have : (y : G) ∈ R ⊓ X := ⟨hy.1, hy.2⟩
    rw [hRX, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  obtain ⟨n, hn, hnB⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy (R.subgroupOf F) hsolv
    (coprime_of_isPGroup_of_odd hRF hR2 hodd) (hmul B hB hFB) (hmul B' hB' hFB')
    (hbot B hRB) (hbot B' hRB')
  refine ⟨(n : G), hn, ?_⟩
  ext g
  constructor
  · intro hg
    have hgF : g ∈ F := hB' hg
    have : (⟨g, hgF⟩ : F) ∈ B'.subgroupOf F := hg
    rw [hnB] at this
    obtain ⟨b, hb, hbg⟩ := this
    have hbg' : (n : G)⁻¹ * b * (n : G) = g := by
      have := congrArg Subtype.val hbg
      simpa [MulAut.conj_apply] using this
    rw [mem_conjR]
    have : (n : G) * g * (n : G)⁻¹ = b := by rw [← hbg']; group
    rw [this]
    exact hb
  · intro hg
    rw [mem_conjR] at hg
    have hnF : (n : G) ∈ F := n.2
    have hgF : g ∈ F := by
      have hb : (n : G) * g * (n : G)⁻¹ ∈ F := hB hg
      have := F.mul_mem (F.mul_mem (F.inv_mem n.2) hb) n.2
      simpa [mul_assoc] using this
    have : (⟨g, hgF⟩ : F) ∈ B'.subgroupOf F := by
      rw [hnB]
      refine ⟨⟨(n : G) * g * (n : G)⁻¹, hB hg⟩, hg, ?_⟩
      apply Subtype.ext
      simp
      group
    exact this

@[expose] def IsComplementIn (R F B : Subgroup G) : Prop :=
  B ≤ F ∧ R ⊓ B = ⊥ ∧ ∀ f ∈ F, ∃ r ∈ R, ∃ b ∈ B, f = r * b

omit [Finite G] in
theorem IsComplementIn.conj {R F B : Subgroup G} (hB : IsComplementIn R F B) {g : G}
    (hgF : g ∈ Subgroup.normalizer (F : Set G)) (hgR : g ∈ Subgroup.normalizer (R : Set G)) :
    IsComplementIn R F (conjR B g) := by
  obtain ⟨hBF, hRB, hdec⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · calc conjR B g ≤ conjR F g := conjR_mono hBF g
      _ = F := conjR_eq_of_mem_normalizer hgF
  · have : conjR (R ⊓ B) g = ⊥ := by rw [hRB]; exact conjR_eq_bot_iff.2 rfl
    rwa [conjR_inf, conjR_eq_of_mem_normalizer hgR] at this
  · intro f hf
    have hf' : g * f * g⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.1 hgF f).1 hf
    obtain ⟨r, hr, b, hb, hrb⟩ := hdec _ hf'
    have hr' : g⁻¹ * r * g ∈ R := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgR) r).1 hr
      simpa using this
    have hb' : g⁻¹ * b * g ∈ conjR B g := by
      rw [mem_conjR]
      have e : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
      rw [e]
      exact hb
    refine ⟨g⁻¹ * r * g, hr', g⁻¹ * b * g, hb', ?_⟩
    calc f = g⁻¹ * (g * f * g⁻¹) * g := by group
      _ = g⁻¹ * (r * b) * g := by rw [hrb]
      _ = (g⁻¹ * r * g) * (g⁻¹ * b * g) := by group

omit [Finite G] in
theorem IsComplementIn.sup_eq {R F B : Subgroup G} (hB : IsComplementIn R F B) (hRF : R ≤ F) :
    R ⊔ B = F := by
  apply le_antisymm (sup_le hRF hB.1)
  intro f hf
  obtain ⟨r, hr, b, hb, rfl⟩ := hB.2.2 f hf
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hb)

omit [Finite G] in
theorem IsComplementIn.card_mul {R F B : Subgroup G} (hB : IsComplementIn R F B) (hRF : R ≤ F)
    (hN : F ≤ Subgroup.normalizer (R : Set G)) :
    Nat.card F = Nat.card R * Nat.card B := by
  have hc := card_sup_mul_card_inf (A := B) (B := R) (hB.1.trans hN)
  rw [inf_comm, hB.2.1, Subgroup.card_bot, mul_one, sup_comm, hB.sup_eq hRF] at hc
  rw [hc, mul_comm]

end CFSG.QuasithinUnique.Lin2
