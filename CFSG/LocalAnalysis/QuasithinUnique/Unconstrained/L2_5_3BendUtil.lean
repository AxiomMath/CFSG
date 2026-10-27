module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinBender
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRad
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingComponents

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

section Fixed

variable {G : Type} [Group G] [Finite G]

theorem exists_ne_one_centralizer {L₀ Q : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hQL : Q ≤ Subgroup.normalizer (L₀ : Set G))
    (hS : ∀ S : Subgroup G, IsSylowTwoOf S L₀ → S ≠ ⊥) :
    ∃ x ∈ L₀, x ≠ 1 ∧ ∀ q ∈ Q, q * x = x * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJN : L₀ ⊔ Q ≤ Subgroup.normalizer (L₀ : Set G) :=
    sup_le Subgroup.le_normalizer hQL
  obtain ⟨P, hQP, hP⟩ := exists_isSylowTwoOf_of_le (le_sup_right : Q ≤ L₀ ⊔ Q) hQ
  have hnormal : (L₀.subgroupOf (L₀ ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hJN
  have hS₁ : IsSylowTwoOf (P ⊓ L₀) L₀ :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hP le_sup_left hnormal.isSubnormal
  have hS₁ne : P ⊓ L₀ ≠ ⊥ := hS _ hS₁
  have hPN : P ≤ Subgroup.normalizer ((P ⊓ L₀ : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf P P L₀
      Subgroup.le_normalizer (hP.1.trans hJN)
  have hQS₁ : Q ≤ Subgroup.normalizer ((P ⊓ L₀ : Subgroup G) : Set G) := hQP.trans hPN
  set S₁ : Subgroup G := P ⊓ L₀ with hS₁def
  have hS₁2 : IsPGroup 2 ↥S₁ := hP.2.1.to_le inf_le_left
  have hW2 : IsPGroup 2 ↥(Q ⊔ S₁) := hQ.to_sup_of_normal_right' hS₁2 hQS₁
  have hWN : Q ⊔ S₁ ≤ Subgroup.normalizer (S₁ : Set G) :=
    sup_le hQS₁ Subgroup.le_normalizer
  have hS₁W : S₁ ≤ Q ⊔ S₁ := le_sup_right
  have hnormW : (S₁.subgroupOf (Q ⊔ S₁)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS₁W).mpr hWN
  have hnilp : Group.IsNilpotent ↥(Q ⊔ S₁) := hW2.isNilpotent
  have hne : S₁.subgroupOf (Q ⊔ S₁) ≠ ⊥ := by
    intro h
    apply hS₁ne
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le hS₁W
  obtain ⟨⟨w, hwS⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨(w : G), (inf_le_right : S₁ ≤ L₀) hwS.1, fun h => hw1 (Subtype.ext (Subtype.ext h)),
    fun q hq => ?_⟩
  have hcen := Subgroup.mem_center_iff.mp hwS.2 ⟨q, (le_sup_left : Q ≤ Q ⊔ S₁) hq⟩
  exact congrArg Subtype.val hcen

end Fixed

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem eq_of_isSylowTwoOf_of_le {L P S S' : Subgroup G} (hBen : fusionIsBenderGroup ↥L)
    (hS : IsSylowTwoOf S L) (hS' : IsSylowTwoOf S' L) (hP : P ≠ ⊥) (hPS : P ≤ S)
    (hPS' : P ≤ S') : S = S' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, k, -, hBor⟩ := Unc25G2.BenderBorel.exists_borel_of_bender hBen
  have hSL : S ≤ L := hS.1
  have hS'L : S' ≤ L := hS'.1
  have hS2 : IsPGroup 2 (S.subgroupOf L) := Unc25G2.BenderBorel.isPGroup_subgroupOf' L hS.2.1
  have hS'2 : IsPGroup 2 (S'.subgroupOf L) := Unc25G2.BenderBorel.isPGroup_subgroupOf' L hS'.2.1
  let Q : Sylow 2 ↥L := hS2.toSylow hS.2.2
  let Q' : Sylow 2 ↥L := hS'2.toSylow hS'.2.2
  have hQ : (Q : Subgroup ↥L) = S.subgroupOf L := rfl
  have hQ' : (Q' : Subgroup ↥L) = S'.subgroupOf L := rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥L Q Q'
  by_cases hgN : g ∈ Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L)
  ·
    have hQQ' : Q = Q' := (Sylow.smul_eq_iff_mem_normalizer.mpr hgN).symm.trans hg
    have h1 : S.subgroupOf L = S'.subgroupOf L := by
      rw [← hQ, ← hQ', hQQ']
    rw [← Subgroup.map_subgroupOf_eq_of_le hSL, ← Subgroup.map_subgroupOf_eq_of_le hS'L, h1]
  · exfalso
    obtain ⟨hSE, -⟩ := hBor Q
    obtain ⟨-, -, hodd⟩ := hSE
    set B : Subgroup ↥L := Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) with hB
    have hgi : g⁻¹ ∉ B := fun h => hgN (by simpa using B.inv_mem h)
    have hZodd := hodd g⁻¹ hgi
    have hP'S : P.subgroupOf L ≤ (Q : Subgroup ↥L) := by
      intro x hx
      exact hPS (Subgroup.mem_subgroupOf.mp hx)
    have hP'S' : P.subgroupOf L ≤ ((g • Q : Sylow 2 ↥L) : Subgroup ↥L) := by
      rw [hg]
      intro x hx
      exact hPS' (Subgroup.mem_subgroupOf.mp hx)
    have hle : P.subgroupOf L ≤ B ⊓ B.map (MulAut.conj g⁻¹⁻¹).toMonoidHom := by
      intro x hx
      refine ⟨Subgroup.le_normalizer (hP'S hx), ?_⟩
      have hx' := hP'S' hx
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx'
      obtain ⟨s, hs, hsx⟩ := hx'
      refine ⟨s, Subgroup.le_normalizer hs, ?_⟩
      simpa [inv_inv] using hsx
    have hP2 : IsPGroup 2 (P.subgroupOf L) :=
      Unc25G2.BenderBorel.isPGroup_subgroupOf' L (hS.2.1.to_le hPS)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
    have hdvd : Nat.card ↥(P.subgroupOf L) ∣
        Nat.card ↥(B ⊓ B.map (MulAut.conj g⁻¹⁻¹).toMonoidHom) := Subgroup.card_dvd_of_le hle
    have hodd2 : Odd (Nat.card ↥(P.subgroupOf L)) := Odd.of_dvd_nat hZodd hdvd
    have hn0 : n = 0 := by
      by_contra hn0
      rw [hn] at hodd2
      exact (Nat.not_even_iff_odd.mpr hodd2) (Nat.even_pow.mpr ⟨even_two, hn0⟩)
    have hbot : P.subgroupOf L = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ (by rw [hn, hn0, pow_zero])
    apply hP
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    exact hbot.eq_bot_of_le (hPS.trans hSL)

end Sylow

section Conj

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_map_conj {L L' S : Subgroup G} {w : G}
    (hLL' : ∀ x, x ∈ L ↔ w * x * w⁻¹ ∈ L') (hS : IsSylowTwoOf S L) :
    IsSylowTwoOf (S.map (MulAut.conj w).toMonoidHom) L' := by
  have hmapL : L.map (MulAut.conj w).toMonoidHom = L' := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hLL' x).mp hx
    · intro hy
      refine ⟨w⁻¹ * y * w, (hLL' _).mpr ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have : w * (w⁻¹ * y * w) * w⁻¹ = y := by group
      rw [this]
      exact hy
  have hcardL : Nat.card ↥L' = Nat.card ↥L := by
    rw [← hmapL]
    exact Subgroup.card_map_of_injective (MulAut.conj w).injective
  refine isSylowTwoOf_iff.mpr ⟨hmapL ▸ Subgroup.map_mono hS.1, hS.2.1.map _, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj w).injective, hS.card_eq]
  unfold twoPart
  rw [hcardL]

@[expose] def projSub (A B P : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Subgroup G where
  carrier := {a | a ∈ A ∧ ∃ b ∈ B, a * b ∈ P}
  one_mem' := ⟨A.one_mem, 1, B.one_mem, by simp⟩
  mul_mem' := by
    rintro a a' ⟨ha, b, hb, hab⟩ ⟨ha', b', hb', hab'⟩
    refine ⟨A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    have h : a * a' * (b * b') = (a * b) * (a' * b') := by
      calc a * a' * (b * b') = a * (a' * b) * b' := by group
        _ = a * (b * a') * b' := by rw [hc a' ha' b hb]
        _ = (a * b) * (a' * b') := by group
    rw [h]
    exact P.mul_mem hab hab'
  inv_mem' := by
    rintro a ⟨ha, b, hb, hab⟩
    refine ⟨A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have h : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
      calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
        _ = (a * b)⁻¹ := by rw [hc a ha b hb]
    rw [h]
    exact P.inv_mem hab

omit [Finite G] in
theorem isPGroup_projSub {A B P : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hdisj : ∀ x, x ∈ A → x ∈ B → x = 1) (hP : IsPGroup 2 ↥P) :
    IsPGroup 2 ↥(projSub A B P hc) := by
  refine isPGroup_of_forall_pow fun a ha => ?_
  obtain ⟨haA, b, hb, hab⟩ := ha
  obtain ⟨k, hk⟩ := hP ⟨a * b, hab⟩
  have hk' : (a * b) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcomm : Commute a b := hc a haA b hb
  rw [hcomm.mul_pow] at hk'
  refine ⟨k, hdisj _ (A.pow_mem haA _) ?_⟩
  have h2 : a ^ 2 ^ k = (b ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hk'
  rw [h2]
  exact B.inv_mem (B.pow_mem hb _)

omit [Finite G] in
theorem le_of_projSub_eq_bot {A B P : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hPAB : P ≤ A ⊔ B) (h : projSub A B P hc = ⊥) : P ≤ B := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hc).mp (hPAB hx)
  have : a ∈ projSub A B P hc := ⟨ha, b, hb, hx⟩
  rw [h, Subgroup.mem_bot] at this
  rw [this, one_mul]
  exact hb

omit [Finite G] in
theorem conj_mem_projSub {A B P A' B' P' : Subgroup G}
    {hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a} {hc' : ∀ a ∈ A', ∀ b ∈ B', a * b = b * a} {w : G}
    (hA : ∀ x ∈ A, w * x * w⁻¹ ∈ A') (hB : ∀ x ∈ B, w * x * w⁻¹ ∈ B')
    (hP : ∀ x ∈ P, w * x * w⁻¹ ∈ P') {a : G} (ha : a ∈ projSub A B P hc) :
    w * a * w⁻¹ ∈ projSub A' B' P' hc' := by
  obtain ⟨haA, b, hb, hab⟩ := ha
  refine ⟨hA a haA, w * b * w⁻¹, hB b hb, ?_⟩
  have h : w * a * w⁻¹ * (w * b * w⁻¹) = w * (a * b) * w⁻¹ := by group
  rw [h]
  exact hP _ hab

theorem exists_sylow_normalized_single {L P W : Subgroup G} (hBen : fusionIsBenderGroup ↥L)
    (hPL : P ≤ L) (hP : P ≠ ⊥) (hP2 : IsPGroup 2 ↥P) (hWL : W ≤ Subgroup.normalizer (L : Set G))
    (hWP : W ≤ Subgroup.normalizer (P : Set G)) :
    ∃ S₀ : Subgroup G, IsSylowTwoOf S₀ L ∧ P ≤ S₀ ∧ W ≤ Subgroup.normalizer (S₀ : Set G) := by
  obtain ⟨S₀, hPS, hS₀⟩ := exists_isSylowTwoOf_of_le hPL hP2
  refine ⟨S₀, hS₀, hPS, fun h hh => ?_⟩
  have hhL : ∀ x, x ∈ L ↔ h * x * h⁻¹ ∈ L := fun x => Subgroup.mem_normalizer_iff.mp (hWL hh) x
  have hS' := isSylowTwoOf_map_conj hhL hS₀
  have hPS' : P ≤ S₀.map (MulAut.conj h).toMonoidHom := by
    intro x hx
    refine ⟨h⁻¹ * x * h, hPS ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (hWP (W.inv_mem hh)) x).mp hx
    simpa using this
  have heq := eq_of_isSylowTwoOf_of_le hBen hS₀ hS' hP hPS hPS'
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  rw [heq]
  exact ⟨x, hx, rfl⟩

omit [Finite G] in
theorem conj_inv_mem_of_iff {A A' : Subgroup G} {w : G} (h : ∀ x, x ∈ A ↔ w * x * w⁻¹ ∈ A')
    {y : G} (hy : y ∈ A') : w⁻¹ * y * w ∈ A := by
  refine (h _).mpr ?_
  have : w * (w⁻¹ * y * w) * w⁻¹ = y := by group
  rw [this]
  exact hy

omit [Finite G] in
theorem conj_inv_mem_projSub {A B P A' B' P' : Subgroup G}
    {hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a} {hc' : ∀ a ∈ A', ∀ b ∈ B', a * b = b * a} {w : G}
    (hA : ∀ x ∈ A, w⁻¹ * x * w ∈ A') (hB : ∀ x ∈ B, w⁻¹ * x * w ∈ B')
    (hP : ∀ x ∈ P, w⁻¹ * x * w ∈ P') {a : G} (ha : a ∈ projSub A B P hc) :
    w⁻¹ * a * w ∈ projSub A' B' P' hc' := by
  have := conj_mem_projSub (hc := hc) (hc' := hc') (w := w⁻¹) (by simpa using hA)
    (by simpa using hB) (by simpa using hP) ha
  simpa using this

theorem exists_sylow_normalized_pair {L₁ L₂ P W : Subgroup G} (hB₁ : fusionIsBenderGroup ↥L₁)
    (hB₂ : fusionIsBenderGroup ↥L₂) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hdisj : ∀ x, x ∈ L₁ → x ∈ L₂ → x = 1) (hPL : P ≤ L₁ ⊔ L₂) (hP : P ≠ ⊥)
    (hP2 : IsPGroup 2 ↥P) (hWP : W ≤ Subgroup.normalizer (P : Set G))
    (hW : ∀ w ∈ W, ((∀ x, x ∈ L₁ ↔ w * x * w⁻¹ ∈ L₁) ∧ (∀ x, x ∈ L₂ ↔ w * x * w⁻¹ ∈ L₂)) ∨
      ((∀ x, x ∈ L₁ ↔ w * x * w⁻¹ ∈ L₂) ∧ (∀ x, x ∈ L₂ ↔ w * x * w⁻¹ ∈ L₁)))
    (hswap : ∃ w ∈ W, (∀ x, x ∈ L₁ ↔ w * x * w⁻¹ ∈ L₂) ∧
      (∀ x, x ∈ L₂ ↔ w * x * w⁻¹ ∈ L₁)) :
    ∃ S₁ S₂ : Subgroup G, IsSylowTwoOf S₁ L₁ ∧ IsSylowTwoOf S₂ L₂ ∧
      W ≤ Subgroup.normalizer ((S₁ ⊔ S₂ : Subgroup G) : Set G) := by
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hdisj' : ∀ x, x ∈ L₂ → x ∈ L₁ → x = 1 := fun x h2 h1 => hdisj x h1 h2
  set P₁ := projSub L₁ L₂ P hc with hP₁def
  set P₂ := projSub L₂ L₁ P hc' with hP₂def
  have hP₁2 : IsPGroup 2 ↥P₁ := isPGroup_projSub hc hdisj hP2
  have hP₂2 : IsPGroup 2 ↥P₂ := isPGroup_projSub hc' hdisj' hP2
  have hP₁L : P₁ ≤ L₁ := fun a ha => ha.1
  have hP₂L : P₂ ≤ L₂ := fun a ha => ha.1
  obtain ⟨w₀, hw₀W, hw₀1, hw₀2⟩ := hswap
  have hPsw : ∀ x ∈ P, w₀ * x * w₀⁻¹ ∈ P := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hWP hw₀W) x).mp hx
  have hP₁ne : P₁ ≠ ⊥ := by
    intro h
    have hPL₂ : P ≤ L₂ := le_of_projSub_eq_bot hc hPL h
    apply hP
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h2 : w₀ * x * w₀⁻¹ ∈ L₁ := (hw₀2 x).mp (hPL₂ hx)
    have h3 : w₀ * x * w₀⁻¹ ∈ L₂ := hPL₂ (hPsw x hx)
    have h4 : w₀ * x * w₀⁻¹ = 1 := hdisj _ h2 h3
    have h5 : x = w₀⁻¹ * (w₀ * x * w₀⁻¹) * w₀ := by group
    rw [h5, h4]
    group
  have hP₂ne : P₂ ≠ ⊥ := by
    intro h
    have hPL₁ : P ≤ L₁ := le_of_projSub_eq_bot hc' (sup_comm L₁ L₂ ▸ hPL) h
    apply hP
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h2 : w₀ * x * w₀⁻¹ ∈ L₂ := (hw₀1 x).mp (hPL₁ hx)
    have h3 : w₀ * x * w₀⁻¹ ∈ L₁ := hPL₁ (hPsw x hx)
    have h4 : w₀ * x * w₀⁻¹ = 1 := hdisj _ h3 h2
    have h5 : x = w₀⁻¹ * (w₀ * x * w₀⁻¹) * w₀ := by group
    rw [h5, h4]
    group
  obtain ⟨S₁, hP₁S₁, hS₁⟩ := exists_isSylowTwoOf_of_le hP₁L hP₁2
  obtain ⟨S₂, hP₂S₂, hS₂⟩ := exists_isSylowTwoOf_of_le hP₂L hP₂2
  refine ⟨S₁, S₂, hS₁, hS₂, fun w hw => ?_⟩
  have hPw : ∀ x ∈ P, w⁻¹ * x * w ∈ P := fun x hx => by
    simpa using (Subgroup.mem_normalizer_iff.mp (hWP (W.inv_mem hw)) x).mp hx
  have hS₁L : S₁ ≤ L₁ := hS₁.1
  have hS₂L : S₂ ≤ L₂ := hS₂.1
  have key : ((∀ x ∈ S₁, w * x * w⁻¹ ∈ S₁) ∧ (∀ x ∈ S₂, w * x * w⁻¹ ∈ S₂)) ∨
      ((∀ x ∈ S₁, w * x * w⁻¹ ∈ S₂) ∧ (∀ x ∈ S₂, w * x * w⁻¹ ∈ S₁)) := by
    rcases hW w hw with ⟨hn1, hn2⟩ | ⟨hs1, hs2⟩
    · left
      have hS₁' := isSylowTwoOf_map_conj hn1 hS₁
      have hS₂' := isSylowTwoOf_map_conj hn2 hS₂
      have hP₁S₁' : P₁ ≤ S₁.map (MulAut.conj w).toMonoidHom := fun x hx =>
        ⟨w⁻¹ * x * w, hP₁S₁ (conj_inv_mem_projSub (hc := hc) (hc' := hc)
          (fun y hy => conj_inv_mem_of_iff hn1 hy) (fun y hy => conj_inv_mem_of_iff hn2 hy) hPw hx),
          by simp [MulAut.conj_apply, mul_assoc]⟩
      have hP₂S₂' : P₂ ≤ S₂.map (MulAut.conj w).toMonoidHom := fun x hx =>
        ⟨w⁻¹ * x * w, hP₂S₂ (conj_inv_mem_projSub (hc := hc') (hc' := hc')
          (fun y hy => conj_inv_mem_of_iff hn2 hy) (fun y hy => conj_inv_mem_of_iff hn1 hy) hPw hx),
          by simp [MulAut.conj_apply, mul_assoc]⟩
      have e₁ := eq_of_isSylowTwoOf_of_le hB₁ hS₁ hS₁' hP₁ne hP₁S₁ hP₁S₁'
      have e₂ := eq_of_isSylowTwoOf_of_le hB₂ hS₂ hS₂' hP₂ne hP₂S₂ hP₂S₂'
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · have : w * x * w⁻¹ ∈ S₁.map (MulAut.conj w).toMonoidHom := ⟨x, hx, rfl⟩
        rw [← e₁] at this
        exact this
      · have : w * x * w⁻¹ ∈ S₂.map (MulAut.conj w).toMonoidHom := ⟨x, hx, rfl⟩
        rw [← e₂] at this
        exact this
    · right
      have hS₁' := isSylowTwoOf_map_conj hs1 hS₁
      have hS₂' := isSylowTwoOf_map_conj hs2 hS₂
      have hP₂S₁' : P₂ ≤ S₁.map (MulAut.conj w).toMonoidHom := fun x hx =>
        ⟨w⁻¹ * x * w, hP₁S₁ (conj_inv_mem_projSub (hc := hc') (hc' := hc)
          (fun y hy => conj_inv_mem_of_iff hs1 hy) (fun y hy => conj_inv_mem_of_iff hs2 hy) hPw hx),
          by simp [MulAut.conj_apply, mul_assoc]⟩
      have hP₁S₂' : P₁ ≤ S₂.map (MulAut.conj w).toMonoidHom := fun x hx =>
        ⟨w⁻¹ * x * w, hP₂S₂ (conj_inv_mem_projSub (hc := hc) (hc' := hc')
          (fun y hy => conj_inv_mem_of_iff hs2 hy) (fun y hy => conj_inv_mem_of_iff hs1 hy) hPw hx),
          by simp [MulAut.conj_apply, mul_assoc]⟩
      have e₁ := eq_of_isSylowTwoOf_of_le hB₂ hS₂ hS₁' hP₂ne hP₂S₂ hP₂S₁'
      have e₂ := eq_of_isSylowTwoOf_of_le hB₁ hS₁ hS₂' hP₁ne hP₁S₁ hP₁S₂'
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · have : w * x * w⁻¹ ∈ S₁.map (MulAut.conj w).toMonoidHom := ⟨x, hx, rfl⟩
        rw [← e₁] at this
        exact this
      · have : w * x * w⁻¹ ∈ S₂.map (MulAut.conj w).toMonoidHom := ⟨x, hx, rfl⟩
        rw [← e₂] at this
        exact this
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute
    (fun a ha b hb => hc a (hS₁L ha) b (hS₂L hb))).mp hx
  have hconj : w * (a * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) := by group
  rw [hconj]
  rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (k1 a ha)) (Subgroup.mem_sup_right (k2 b hb))
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (k1 a ha)) (Subgroup.mem_sup_left (k2 b hb))

end Conj

section Subnormal

variable {G : Type} [Group G] [Finite G]

theorem charTwo_inf_of_isSubnormal {H X Y : Subgroup G} (hX : CharTwo X) (hXH : X ≤ H)
    (hY : (Y.subgroupOf H).IsSubnormal) : CharTwo (Y ⊓ X) := by
  refine EscapingComponents.charTwo_of_isSubnormal hX inf_le_right ?_
  have := hY.comap (Subgroup.inclusion hXH)
  convert this using 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion,
    Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩

end Subnormal

end CFSG.QuasithinUnique.Fin253
