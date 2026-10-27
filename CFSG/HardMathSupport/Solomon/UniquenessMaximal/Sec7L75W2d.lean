module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem exists_pow_mul_eq {J : Subgroup G} {q : G}
    (hq : q ∈ Subgroup.normalizer (J : Set G)) {j : G} (hj : j ∈ J) (n : ℕ) :
    ∃ j' ∈ J, (j * q) ^ n = j' * q ^ n := by
  induction n with
  | zero => exact ⟨1, J.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨j', hj', he⟩ := ih
    refine ⟨j' * (q ^ n * j * (q ^ n)⁻¹), J.mul_mem hj' ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (pow_mem hq n) j).1 hj
    · rw [pow_succ, he]
      group

theorem mem_layer_of_isPGroup {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hcov : X ≤ GLAPLayer p X ⊔ GLAPPrimeCoreOf p X) {g : G} (hg : g ∈ X)
    (h : IsPGroup p (Subgroup.zpowers g)) : g ∈ GLAPLayer p X := by
  set J := GLAPLayer p X with hJ
  set O := GLAPPrimeCoreOf p X with hO
  have hJX : J ≤ X := glaPLayer_le p X
  have hOX : O ≤ X := Sec7.glaPPrimeCoreOf_le_self' p X
  have hJO : J ≤ Subgroup.normalizer (O : Set G) := hJX.trans (le_normalizer_glaPPrimeCoreOf p X)
  have hk : g ∈ ((J ⊔ O : Subgroup G) : Set G) := hcov hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right J O hJO] at hk
  obtain ⟨j, hj, q, hq, hgq⟩ := hk
  have hgq : j * q = g := hgq
  have hqN : q ∈ Subgroup.normalizer (J : Set G) := Sec7.le_normalizer_glaPLayer p X (hOX hq)
  obtain ⟨k, hk⟩ := h ⟨g, Subgroup.mem_zpowers g⟩
  have hgk : g ^ (p ^ k) = 1 := congrArg Subtype.val hk
  obtain ⟨j', hj', he⟩ := exists_pow_mul_eq hqN hj (p ^ k)
  rw [hgq, hgk] at he
  have hqk : q ^ (p ^ k) ∈ J := by
    have : q ^ (p ^ k) = j'⁻¹ := eq_inv_of_mul_eq_one_right he.symm
    rw [this]
    exact J.inv_mem hj'
  have hcop : Nat.Coprime (p ^ k) (orderOf q) := by
    refine Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_)
    exact not_dvd_card_glaPPrimeCoreOf hp X (hd.trans (Subgroup.orderOf_dvd_natCard O hq))
  rw [← hgq]
  exact J.mul_mem hj (Sec7.mem_of_pow_mem_of_coprime hcop hqk)

omit [Finite G] in
theorem le_glaPPrimeCoreOf_of_normal_of_cover {p : ℕ} (_hp : p.Prime) {X L V : Subgroup G}
    (hLX : L ≤ X) (hcov : X ≤ L ⊔ GLAPPrimeCoreOf p X)
    (hsimple : IsSimpleGroup (↥X ⧸ GLAPPrimeCore p ↥X))
    (hdiv : p ∣ Nat.card (↥X ⧸ GLAPPrimeCore p ↥X))
    (hVL : V ≤ L) (hVn : L ≤ Subgroup.normalizer (V : Set G)) (hV : ¬ p ∣ Nat.card V) :
    V ≤ GLAPPrimeCoreOf p X := by
  set O := GLAPPrimeCoreOf p X with hO
  have hVX : V ≤ X := hVL.trans hLX
  have hLO : L ≤ Subgroup.normalizer (O : Set G) := hLX.trans (le_normalizer_glaPPrimeCoreOf p X)
  have hLbar : barX p X X ≤ barX p X L := by
    refine barX_le_of_forall hLX fun k hk => ?_
    have hk' : k ∈ ((L ⊔ O : Subgroup G) : Set G) := hcov hk
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L O hLO] at hk'
    obtain ⟨l, hl, o, ho, rfl⟩ := hk'
    exact ⟨l, hl, by simpa using ho⟩
  have hLtop : barX p X L = ⊤ := by
    rw [eq_top_iff, ← barX_self p X]; exact hLbar
  have hnorm : (barX p X V).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hLtop]
    exact barX_le_normalizer hVn
  have hbot : barX p X V = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (barX p X V) with h | h
    · exact h
    · exfalso
      have h1 : Nat.card (↥X ⧸ GLAPPrimeCore p ↥X) ∣ Nat.card V := by
        have h2 : Nat.card (barX p X V) ∣ Nat.card (V.subgroupOf X) :=
          Subgroup.card_map_dvd _ _
        have h3 : Nat.card (V.subgroupOf X) = Nat.card V :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv
        have h4 : Nat.card (barX p X V) = Nat.card (↥X ⧸ GLAPPrimeCore p ↥X) := by
          rw [h, Subgroup.card_top]
        rw [← h4, ← h3]
        exact h2
      exact hV (hdiv.trans h1)
  exact Sec7.le_glaPPrimeCoreOf_of_barX_eq_bot hVX hbot

omit [Finite G] in
theorem comm_of_mem_centralizerQuot' {B K : Subgroup G}
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) {a : G} (ha : a ∈ centralizerQuot B K) :
    a ∈ B ∧ ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 K := by
  set O := GLAPPrimeCoreOf 3 K with hO
  have hBO : B ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf_of_le' hBK
  let T : Subgroup G :=
    { carrier := {b | b ∈ B ∧ ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ O}
      one_mem' := ⟨B.one_mem, fun k _ => by simp⟩
      mul_mem' := by
        rintro b b' ⟨hb, hbc⟩ ⟨hb', hbc'⟩
        refine ⟨B.mul_mem hb hb', fun k hk => ?_⟩
        have e : b * b' * k * (b * b')⁻¹ * k⁻¹ =
            (b * (b' * k * b'⁻¹ * k⁻¹) * b⁻¹) * (b * k * b⁻¹ * k⁻¹) := by group
        rw [e]
        exact O.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBO hb) _).1 (hbc' k hk)) (hbc k hk)
      inv_mem' := by
        rintro b ⟨hb, hbc⟩
        refine ⟨B.inv_mem hb, fun k hk => ?_⟩
        have hk' : b⁻¹ * k * b ∈ K := by
          have := (Subgroup.mem_normalizer_iff.1 (hBK (B.inv_mem hb)) k).1 hk
          simpa using this
        have e : b⁻¹ * k * (b⁻¹)⁻¹ * k⁻¹ =
            (b * (b⁻¹ * k * b) * b⁻¹ * (b⁻¹ * k * b)⁻¹)⁻¹ := by group
        rw [e]
        exact O.inv_mem (hbc _ hk') }
  have : centralizerQuot B K ≤ T := (Subgroup.closure_le T).2 fun b hb => hb
  exact this ha

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
