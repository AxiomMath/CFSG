module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameVertex

public section

namespace CFSG.ClassicalInvolution.NDB.Vertex

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Balance.StrongBalance CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77.FrameVertex
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Toral

variable {G : Type} [Group G]

@[expose] def ToralOnComponentPow (m : ℕ) (c : G) (B : Subgroup G) {K : Type} [Group K]
    (ψ : K →* OddQuot c) : Prop :=
  ∃ P : Subgroup K, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
    ∀ b ∈ B, ∀ hb : b ∈ Subgroup.centralizer ({c} : Set G), ∃ x ∈ P, x ^ m = 1 ∧
      ∀ y ∈ ψ.range,
        oddQuotMk c ⟨b, hb⟩ * y * (oddQuotMk c ⟨b, hb⟩)⁻¹ = ψ x * y * (ψ x)⁻¹

theorem toralOnComponentPow_of_closure {m : ℕ} {c : G} {S : Set G} {K : Type} [Group K]
    {ψ : K →* OddQuot c} (hSC : Subgroup.closure S ≤ Subgroup.centralizer ({c} : Set G))
    {P : Subgroup K} (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hS : ∀ s ∈ S, ∀ hs : s ∈ Subgroup.centralizer ({c} : Set G), ∃ x ∈ P, x ^ m = 1 ∧
      ∀ y ∈ ψ.range,
        oddQuotMk c ⟨s, hs⟩ * y * (oddQuotMk c ⟨s, hs⟩)⁻¹ = ψ x * y * (ψ x)⁻¹) :
    ToralOnComponentPow m c (Subgroup.closure S) ψ := by
  refine ⟨P, hP, fun b hb => ?_⟩
  refine Subgroup.closure_induction (p := fun b _ => ∀ hb : b ∈ Subgroup.centralizer
    ({c} : Set G), ∃ x ∈ P, x ^ m = 1 ∧ ∀ y ∈ ψ.range,
      oddQuotMk c ⟨b, hb⟩ * y * (oddQuotMk c ⟨b, hb⟩)⁻¹ = ψ x * y * (ψ x)⁻¹) hS ?_ ?_ ?_ hb
  · intro hb
    refine ⟨1, P.one_mem, one_pow m, fun y _ => ?_⟩
    have e : (⟨1, hb⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 := rfl
    simp only [e, map_one, one_mul, inv_one, mul_one]
  · intro a b ha hb iha ihb hab
    have haC : a ∈ Subgroup.centralizer ({c} : Set G) := hSC ha
    have hbC : b ∈ Subgroup.centralizer ({c} : Set G) := hSC hb
    obtain ⟨x, hxP, hxm, hxa⟩ := iha haC
    obtain ⟨x', hx'P, hx'm, hx'a⟩ := ihb hbC
    refine ⟨x * x', P.mul_mem hxP hx'P, ?_, fun y hy => ?_⟩
    · rw [(show Commute x x' from hP x hxP x' hx'P).mul_pow, hxm, hx'm, one_mul]
    · have e : (⟨a * b, hab⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = ⟨a, haC⟩ * ⟨b, hbC⟩ :=
        rfl
      have hy' : ψ x' * y * (ψ x')⁻¹ ∈ ψ.range := by
        obtain ⟨w, rfl⟩ := hy
        exact ⟨x' * w * x'⁻¹, by simp only [map_mul, map_inv]⟩
      calc oddQuotMk c ⟨a * b, hab⟩ * y * (oddQuotMk c ⟨a * b, hab⟩)⁻¹
          = oddQuotMk c ⟨a, haC⟩ * (oddQuotMk c ⟨b, hbC⟩ * y * (oddQuotMk c ⟨b, hbC⟩)⁻¹) *
            (oddQuotMk c ⟨a, haC⟩)⁻¹ := by rw [e, map_mul]; group
        _ = oddQuotMk c ⟨a, haC⟩ * (ψ x' * y * (ψ x')⁻¹) * (oddQuotMk c ⟨a, haC⟩)⁻¹ := by
            rw [hx'a y hy]
        _ = ψ x * (ψ x' * y * (ψ x')⁻¹) * (ψ x)⁻¹ := hxa _ hy'
        _ = ψ (x * x') * y * (ψ (x * x'))⁻¹ := by rw [map_mul]; group
  · intro a ha iha haI
    have haC : a ∈ Subgroup.centralizer ({c} : Set G) := hSC ha
    obtain ⟨x, hxP, hxm, hxa⟩ := iha haC
    refine ⟨x⁻¹, P.inv_mem hxP, by rw [inv_pow, hxm, inv_one], fun y hy => ?_⟩
    have e : (⟨a⁻¹, haI⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = (⟨a, haC⟩)⁻¹ := rfl
    have hy' : (ψ x)⁻¹ * y * ψ x ∈ ψ.range := by
      obtain ⟨w, rfl⟩ := hy
      exact ⟨x⁻¹ * w * x, by simp only [map_mul, map_inv]⟩
    have h1 := hxa _ hy'
    rw [e, map_inv, inv_inv, map_inv, inv_inv]
    calc (oddQuotMk c ⟨a, haC⟩)⁻¹ * y * oddQuotMk c ⟨a, haC⟩
        = (oddQuotMk c ⟨a, haC⟩)⁻¹ * (ψ x * ((ψ x)⁻¹ * y * ψ x) * (ψ x)⁻¹) *
          oddQuotMk c ⟨a, haC⟩ := by group
      _ = (oddQuotMk c ⟨a, haC⟩)⁻¹ * (oddQuotMk c ⟨a, haC⟩ * ((ψ x)⁻¹ * y * ψ x) *
          (oddQuotMk c ⟨a, haC⟩)⁻¹) * oddQuotMk c ⟨a, haC⟩ := by rw [h1]
      _ = (ψ x)⁻¹ * y * ψ x := by group

end Toral

section Alpha

variable {Q : Type} [Group Q] [Finite Q]

theorem alphaOf_inducedImage_eq_bot_of_toralPow {m : ℕ} {t : StatedLieTag} {n p e : ℕ}
    (hp : p.Prime) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ e) {Qn : ℕ → ℕ → ℕ → Prop} (hQ : Qn n p e)
    (hSB : StrongLocalTwoBalanceToralPowOn m t Qn)
    [Group.IsPerfect (modelUniv t n p e hp).K] (ψ : (modelUniv t n p e hp).K →* Q)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K) {B : Subgroup Q}
    (hB2 : ∀ x ∈ B, x * x = 1) (hBcard : Nat.card B = 8)
    (hBN : B ≤ Subgroup.normalizer (ψ.range : Set Q)) {Z : Subgroup Q} (hZcard : Nat.card Z = 2)
    (hZB : Z ≤ B) (hZ : ∀ z ∈ Z, ∀ y ∈ ψ.range, z * y = y * z)
    (hZ' : ∀ b ∈ B, (∀ y ∈ ψ.range, b * y = y * b) → b ∈ Z)
    (htoral : ∃ P : Subgroup (modelUniv t n p e hp).K, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
      ∀ b ∈ B, ∃ x ∈ P, x ^ m = 1 ∧
        ∀ y ∈ ψ.range, b * y * b⁻¹ = ψ x * y * (ψ x)⁻¹) :
    alphaOf (inducedImage ψ.range B) = ⊥ := by
  classical
  obtain ⟨hcen, hnorm, hfaith⟩ := innerHom_spec ψ hker
  set L : Subgroup Q := ψ.range with hL
  set πB : ↥B →* ↥(inducedAutOn L) := (toInducedAutOn L).comp (Subgroup.inclusion hBN) with hπB
  have hπB_apply : ∀ b : ↥B, πB b = toInducedAutOn L ⟨b, hBN b.2⟩ := fun b => rfl
  have hF : inducedImage L B = πB.range := by
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨⟨b, hBN b.2⟩, b.2, rfl⟩
  have hker_iff : ∀ b : ↥B, πB b = 1 ↔ (b : Q) ∈ Z := by
    intro b
    rw [hπB_apply]
    constructor
    · intro h1
      exact hZ' b b.2 (Lemma52Proof.commute_of_toInducedAutOn_eq_one L (hBN b.2) h1)
    · intro h1
      exact Lemma52Proof.toInducedAutOn_eq_one_of_commute L (hBN b.2) (hZ _ h1)
  have hkerEq : πB.ker = Z.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker_iff]
  have hcardker : Nat.card πB.ker = 2 := by
    rw [hkerEq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv).trans hZcard
  have hcardF : Nat.card (inducedImage L B) = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup πB.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange πB).toEquiv, hcardker, hBcard] at h1
    rw [hF]
    omega
  have hFsq : ∀ f ∈ inducedImage L B, f * f = 1 := by
    intro f hf
    rw [hF] at hf
    obtain ⟨b, rfl⟩ := hf
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (hB2 b b.2)
    rw [this, map_one]
  have hFfaith : ∀ f ∈ inducedImage L B, f ≠ 1 → ¬ ∀ x ∈ (innerHom ψ).range, f * x = x * f :=
    fun f _ hf1 hall => hf1 (hfaith f hall)
  obtain ⟨P, hPc, hPact⟩ := htoral
  have htor : ToralActionPow m (innerHom ψ) (inducedImage L B) := by
    refine ⟨P, hPc, fun f hf => ?_⟩
    rw [hF] at hf
    obtain ⟨b, rfl⟩ := hf
    obtain ⟨x, hxP, hxm, hxact⟩ := hPact b b.2
    refine ⟨x, hxP, hxm, fun y => ?_⟩
    rw [innerHom_apply, innerHom_apply, hπB_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := hxact (ψ y) ⟨y, rfl⟩
    show (b : Q) * ψ y * (b : Q)⁻¹ = ψ (x * y * x⁻¹)
    rw [map_mul, map_mul, map_inv]
    exact this
  have hSC := hSB n p e hp hQ hfund hadm hp2 h5 ↥(inducedAutOn L) (innerHom ψ)
    (fun g hg => hcen g (MonoidHom.mem_ker.mp hg)) hnorm (inducedImage L B) hcardF hFsq hFfaith htor
  rw [alphaOf_eq_bot_iff]
  refine ⟨fun a ha ha1 => ?_, ?_⟩
  · rw [eq_bot_iff, Subgroup.commutator_le]
    intro d hd g hg
    have hc := hSC.2 a ha ha1 d hd g hg
    have hu : ((g * d)⁻¹ * (d * g)) = 1 := by
      apply hfaith
      intro y hy
      have h1 := hc y hy
      calc (g * d)⁻¹ * (d * g) * y = (g * d)⁻¹ * ((d * g) * y * (d * g)⁻¹) * (d * g) := by group
        _ = (g * d)⁻¹ * ((g * d) * y * (g * d)⁻¹) * (d * g) := by
          rw [show (d * g) * y * (d * g)⁻¹ = d * g * y * (d * g)⁻¹ from rfl, h1]
        _ = y * ((g * d)⁻¹ * (d * g)) := by group
    have hdg : d * g = g * d := by
      have := congrArg (fun w => (g * d) * w) hu
      simpa [mul_assoc] using this
    rw [Subgroup.mem_bot, commutatorElement_def]
    calc d * g * d⁻¹ * g⁻¹ = (g * d) * d⁻¹ * g⁻¹ := by rw [hdg]
      _ = 1 := by group
  · rw [eq_bot_iff]
    intro d hd
    have hd' : d ∈ deltaCore (inducedImage L B) := hd
    rw [Subgroup.mem_bot]
    exact hfaith d fun y hy => hSC.1 d hd' y hy

end Alpha

section Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem hyp51At_of_systemPow {m : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : ConjInvariant Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    {B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hcB : c ∈ B)
    (hc1 : c ≠ 1) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) (hbc : b ≠ c) {M : Subgroup G}
    (hM : M ∈ tqMembers Ω c) (hMb : IsClassicalMember p f M b)
    (hD : ∃ D : LocalLieSystemAt p f (exactFamily Ω c) c, ∀ j : Fin D.card,
      MovedByAll B c (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range →
        p ^ D.exp j ≠ 3 ∧ (∃ Qn : ℕ → ℕ → ℕ → Prop, Qn (D.rank j) p (D.exp j) ∧
          StrongLocalTwoBalanceToralPowOn m (D.tag j) Qn) ∧
          ToralOnComponentPow m c B (secComponentHom (normalizesLayer_exactFamily hΩ) D j)) :
    Hyp51At B c := by
  refine ⟨uniq_of_witness hp2 hq hΩ hcls hBelow hc2 hnc hB hcB hc1 hbB hb1 hbc hM hMb, ?_⟩
  intro L hL hmov
  have hne : (tqMembers Ω c).Nonempty := ⟨M, hM⟩
  obtain ⟨Dsys, hDsys⟩ := hD
  obtain ⟨D', hD'Q, -⟩ := lieDecomposition_exactFamily_comp hp2
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hq hΩ hcls hc2 hne Dsys
  obtain ⟨j₀, hj₀⟩ := movedComponent_eq hΩ hc2 hB hcB hc1 hbB hb1 hbc hM hMb D'
  obtain ⟨j, hj⟩ := hD'Q j₀
  have hLeq : L = (secComponentHom (normalizesLayer_exactFamily hΩ) Dsys j).range :=
    (hj₀ L hL hmov).trans hj.symm
  have hBN := modOdd_le_normalizer hp2 hq hΩ hcls hBelow hc2 hnc hB hcB hc1 hbB hb1 hbc hM hMb hL
    hmov
  subst hLeq
  set ψ := secComponentHom (normalizesLayer_exactFamily hΩ) Dsys j with hψ
  obtain ⟨hF3, ⟨Qn, hQn, hSB'⟩, P, hPc, hPact⟩ := hDsys j hmov
  have hker := secComponentHom_ker_le_center (normalizesLayer_exactFamily hΩ) Dsys j
  have hperf : Group.IsPerfect (compModel Dsys j).K :=
    Group.isPerfect_def.2 (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero _ _ _ _ _
      (Dsys.isFundTag j) (Dsys.admissible j)).1.1
  have h5 : 5 ≤ p ^ Dsys.exp j :=
    five_le_pow_of_ne_three Fact.out hp2 hq ((Dsys.exp_eq j).imp id And.right) hF3
  have hmemZ := fun x => Lemma52Proof.mem_modOdd_zpowers_iff hB hcB hc1 x
  have hself : Lemma52Proof.oddQuotSelf c ∈ modOdd c (Subgroup.zpowers c) :=
    (hmemZ _).mpr (Or.inr rfl)
  have hZcard : Nat.card (modOdd c (Subgroup.zpowers c)) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨Lemma52Proof.oddQuotSelf c, hself⟩, fun h =>
      Lemma52Proof.oddQuotSelf_ne_one hB hcB hc1 (congrArg Subtype.val h).symm, ?_⟩
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (hmemZ z).mp z.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hZB : modOdd c (Subgroup.zpowers c) ≤ modOdd c B := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hx
    exact ⟨k, Subgroup.zpowers_le.mpr hcB hk, rfl⟩
  have hZ : ∀ z ∈ modOdd c (Subgroup.zpowers c), ∀ y ∈ ψ.range, z * y = y * z := by
    intro z hz y _
    rcases (hmemZ z).mp hz with rfl | rfl
    · simp
    · exact (Lemma52Proof.oddQuotSelf_central c y).symm
  have hZ' : ∀ b' ∈ modOdd c B, (∀ y ∈ ψ.range, b' * y = y * b') →
      b' ∈ modOdd c (Subgroup.zpowers c) := by
    intro b' hb' hcomm
    by_contra hnot
    obtain ⟨y, hy, hne'⟩ := hmov b' hb' hnot
    exact hne' (hcomm y hy)
  refine alphaOf_inducedImage_eq_bot_of_toralPow Fact.out (Dsys.isFundTag j) (Dsys.admissible j)
    hp2 h5 hQn hSB' ψ hker (Lemma52Proof.modOdd_sq hB)
    (Lemma52Proof.card_modOdd_eq_eight hB hB8 hcB) hBN hZcard hZB hZ hZ' ⟨P, hPc, fun b' hb' => ?_⟩
  obtain ⟨k, hkB, rfl⟩ := mem_modOdd_iff.mp hb'
  exact hPact k hkB k.2

end Vertex

end CFSG.ClassicalInvolution.NDB.Vertex
