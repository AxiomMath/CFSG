module

public import CFSG.LocalAnalysis.GH72.Sec7Core

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools

namespace Sec7

variable {G : Type*} [Group G] [Finite G]

theorem not_le_O_of_isPGroup {T H : Subgroup G} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    ¬ T ≤ O H := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card T := by
    rcases hT.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hT1
    · exact h
  have hodd := Odd.of_dvd_nat (card_O_odd H) (card_dvd_of_le hle)
  rw [Nat.odd_iff] at hodd
  omega

omit [Finite G] in
theorem commute_of_odd_of_isPGroup {E T : Subgroup G} (hE : Odd (Nat.card E))
    (hT : IsPGroup 2 T) {e x : G} (he : e ∈ E) (hx : x ∈ T)
    (hxE : x ∈ normalizer (E : Set G)) (heT : e ∈ normalizer (T : Set G)) : e * x = x * e := by
  have h1 : e * x * e⁻¹ * x⁻¹ ∈ E := by
    have : x * e⁻¹ * x⁻¹ ∈ E := (mem_normalizer_iff.mp hxE e⁻¹).mp (inv_mem he)
    rw [show e * x * e⁻¹ * x⁻¹ = e * (x * e⁻¹ * x⁻¹) by group]
    exact mul_mem he this
  have h2 : e * x * e⁻¹ * x⁻¹ ∈ T :=
    mul_mem ((mem_normalizer_iff.mp heT x).mp hx) (inv_mem hx)
  have h3 : e * x * e⁻¹ * x⁻¹ = 1 := by
    set c := e * x * e⁻¹ * x⁻¹
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hT ⟨c, h2⟩
    have hoT : orderOf c ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_mk c h2]
      exact orderOf_dvd_of_pow_eq_one hk
    have hoE : orderOf c ∣ Nat.card E := by
      rw [← Subgroup.orderOf_mk c h1]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ k) (Nat.card E) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hE)
    have h1' : orderOf c = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hoT hoE)
    exact orderOf_eq_one_iff.mp h1'
  calc e * x = e * x * e⁻¹ * x⁻¹ * (x * e) := by group
    _ = x * e := by rw [h3, one_mul]

theorem nonempty_mulEquiv_of_ker_eq {M₀ : Type*} [Group M₀] {L L' : Type*} [Group L] [Group L']
    (f : M₀ →* L) (hf : Function.Surjective f) (f' : M₀ →* L') (hf' : Function.Surjective f')
    (h : f.ker = f'.ker) : Nonempty (L ≃* L') :=
  ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans
      (QuotientGroup.quotientKerEquivOfSurjective f' hf'))⟩

theorem le_of_isSylowOf_of_odd_relIndex {Q K₀ M : Subgroup G} (hQ : IsSylowOf 2 Q K₀)
    (hMK₀ : M ≤ K₀) (hM : K₀ ≤ normalizer (M : Set G)) (hodd : Odd (M.relIndex K₀)) : Q ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQM := hQ.inf_of_le_normalizer hMK₀ hM
  have hK₀ : M.relIndex K₀ * Nat.card M = Nat.card K₀ := by
    have h := relIndex_mul_card M K₀
    rwa [inf_of_le_left hMK₀] at h
  have hv : (Nat.card K₀).factorization 2 = (Nat.card M).factorization 2 := by
    rw [← hK₀, Nat.factorization_mul (by rintro h; rw [h] at hodd; simp at hodd) Nat.card_pos.ne',
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by
        rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hodd), zero_add]
  have hcard : Nat.card Q ≤ Nat.card (Q ⊓ M : Subgroup G) := by
    rw [hQ.card_eq, hQM.card_eq, hv]
  have heq : Q ⊓ M = Q := Subgroup.eq_of_le_of_card_ge inf_le_left hcard
  exact heq ▸ inf_le_right

omit [Finite G] in
theorem Covers.mono {K J M₀ OM : Subgroup G} (h : Covers K M₀ OM) (hKJ : K ≤ J) :
    Covers J M₀ OM :=
  h.trans (sup_le_sup_right (inf_le_inf_right _ hKJ) _)

omit [Finite G] in
theorem commute_of_mul_self {V : Subgroup G} (hV : ∀ x ∈ V, x * x = 1) {x y : G} (hx : x ∈ V)
    (hy : y ∈ V) : x * y = y * x := by
  have hxy := hV _ (mul_mem hx hy)
  have hx' := inv_eq_of_mul_eq_one_right (hV x hx)
  have hy' := inv_eq_of_mul_eq_one_right (hV y hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y * x := by rw [mul_inv_rev, hx', hy']

end Sec7

namespace Sec7

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_normalizer_of_four {P Q A Ast T' V M₁ M₀ M M₀st Mst J₀ : Subgroup G}
    {L : Type*} [Group L] [IsSimpleGroup L] (hLperf : commutator L = ⊤)
    (hQP : Q ≤ centralizer (P : Set G)) (hT'V : T' ≤ V) (hT' : T' ≠ ⊥)
    (hV : CFSG.CGT.Foote81L6.TStruct.IsFourIn P V) (hAst : IsE16 Ast)
    (hAsteq : Ast = V ⊔ (A ⊓ Q)) (hAstP : Ast ⊓ P = V) (hAstQ : Ast ⊓ Q = A ⊓ Q)
    (hXq : IsKleinFour ↥(A ⊓ Q)) (hXqQ : A ⊓ Q ≤ Q)
    (hJ : normalizer (T' : Set G) ≠ ⊤)
    (hcov : Covers (centralizer (P : Set G)) M₀st (O Mst))
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ → Covers H M₀st (O Mst) → ∀ p ∈ Ast ⊓ P, p ≠ 1 → p ∈ H →
      O H ⊓ C p ≤ O (C p))
    (h411 : ∀ q ∈ Ast ⊓ Q, q ≠ 1 → ∀ D : Subgroup G, D ≤ C q → Odd (Nat.card D) →
      Ast ≤ normalizer (D : Set G) → ⁅D, Ast ⊓ Q⁆ ≤ O (C q))
    (h66 : ∀ p q : G, p ∈ P → q ∈ Q → orderOf p = 2 → orderOf q = 2 → O (C p) ⊓ O (C q) = ⊥)
    (hJ₀def : J₀ = (normalizer (T' : Set G) ⊓ M₀) ⊔ O (normalizer (T' : Set G)))
    (hJ₀J : J₀ ≤ normalizer (T' : Set G)) (hJ₀n : (J₀.subgroupOf (normalizer (T' : Set G))).Normal)
    (hJ₀iso : QuotIso J₀ (O (normalizer (T' : Set G))) M₀ (O M))
    (hM₁K : M₁ ≤ centralizer (P : Set G)) (hM₁M₀ : M₁ ≤ M₀) (hperf : ⁅M₁, M₁⁆ = M₁)
    (hXqM₁ : A ⊓ Q ≤ M₁) (hcenM₁ : O M₁ ≤ centralizer (M₁ : Set G))
    (g : M₁ →* L) (hg : Function.Surjective g) (hgker : g.ker = (O M₁).subgroupOf M₁)
    (f₂ : M₀ →* L) (hf₂ : Function.Surjective f₂) (hf₂ker : f₂.ker = (O M).subgroupOf M₀) :
    normalizer (T' : Set G) ≤ normalizer (M₁ : Set G) := by
  set J := normalizer (T' : Set G) with hJdef
  have : Finite L := Finite.of_surjective g hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVP : V ≤ P := hV.1
  have hT'P : T' ≤ P := hT'V.trans hVP
  have hV2 : ∀ v ∈ V, v * v = 1 := hV.2.1
  have hT'2 : IsPGroup 2 T' :=
    (IsPGroup.of_card (n := 2) (by rw [hV.2.2]; norm_num)).to_le hT'V
  have hXq2 : IsPGroup 2 ↥(A ⊓ Q) :=
    IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  have hXq1 : A ⊓ Q ≠ ⊥ := by
    intro h
    have := IsKleinFour.card_four (G := ↥(A ⊓ Q))
    rw [h, card_bot] at this
    exact absurd this (by norm_num)
  have hKJ : centralizer (P : Set G) ≤ J := by
    refine (centralizer_le hT'P).trans fun c hc => Subgroup.mem_normalizer_fintype fun t ht => ?_
    rw [(mem_centralizer_iff.mp hc t ht).symm, mul_inv_cancel_right]
    exact ht
  have hcovJ : Covers J M₀st (O Mst) := Covers.mono hcov hKJ
  obtain ⟨⟨x, hxT'⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hT'
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxV : x ∈ V := hT'V hxT'
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hV2 x hxV) hx1'
  have hxJ : x ∈ J := le_normalizer hxT'
  set E := O J with hEdef
  have hEodd : Odd (Nat.card E) := card_O_odd J
  have hJE : J ≤ normalizer (E : Set G) := CFSG.GH72.le_normalizer_O J
  have hEC : E ≤ C x := by
    intro e he
    rw [mem_centralizer_singleton_iff]
    exact commute_of_odd_of_isPGroup hEodd hT'2 he hxT' (hJE hxJ) (O_le J he)
  have hEx : E ≤ O (C x) := by
    have h := h413 J hJ hcovJ x (by rw [hAstP]; exact hxV) hx1' hxJ
    exact (le_inf le_rfl hEC).trans h
  have hVJ : V ≤ J := fun v hv => Subgroup.mem_normalizer_fintype fun t ht => by
    rw [commute_of_mul_self hV2 hv (hT'V ht), mul_inv_cancel_right]
    exact ht
  have hAstJ : Ast ≤ J := hAsteq ▸ sup_le hVJ (hXqQ.trans (hQP.trans hKJ))
  have hXqJ : A ⊓ Q ≤ J := hXqQ.trans (hQP.trans hKJ)
  have hAstc : ∀ a ∈ Ast, ∀ b ∈ Ast, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hAst.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hloc : ∀ y ∈ A ⊓ Q, y ≠ 1 → A ⊓ Q ≤ centralizer ((E ⊓ C y : Subgroup G) : Set G) := by
    intro y hy hy1
    have hyAst : y ∈ Ast := by
      have : y ∈ Ast ⊓ Q := hAstQ ▸ hy
      exact this.1
    have hy2 : orderOf y = 2 := by
      refine orderOf_eq_prime ?_ hy1
      have := hAst.1.2 y hyAst
      exact this
    have hDodd : Odd (Nat.card (E ⊓ C y : Subgroup G)) :=
      Odd.of_dvd_nat hEodd (card_dvd_of_le inf_le_left)
    have hAstD : Ast ≤ normalizer ((E ⊓ C y : Subgroup G) : Set G) := by
      intro a ha
      refine inf_normalizer_le_normalizer_inf ⟨hJE (hAstJ ha), ?_⟩
      refine Subgroup.mem_normalizer_fintype fun c hc => ?_
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hc ⊢
      have hay := hAstc a ha y hyAst
      calc a * c * a⁻¹ * y = a * c * (a⁻¹ * y) := by group
        _ = a * c * (y * a⁻¹) := by rw [(show Commute a y from hay).inv_left.eq]
        _ = a * (c * y) * a⁻¹ := by group
        _ = a * (y * c) * a⁻¹ := by rw [hc]
        _ = a * y * c * a⁻¹ := by group
        _ = y * a * c * a⁻¹ := by rw [hay]
        _ = y * (a * c * a⁻¹) := by group
    have h1 := h411 y (by rw [hAstQ]; exact hy) hy1 (E ⊓ C y) inf_le_right hDodd hAstD
    rw [hAstQ] at h1
    have h2 : ⁅E ⊓ C y, A ⊓ Q⁆ ≤ E := by
      rw [commutator_le]
      intro d hd b hb
      rw [commutatorElement_def]
      have : b * d⁻¹ * b⁻¹ ∈ E := (mem_normalizer_iff.mp (hJE (hXqJ hb)) d⁻¹).mp (inv_mem hd.1)
      rw [show d * b * d⁻¹ * b⁻¹ = d * (b * d⁻¹ * b⁻¹) by group]
      exact mul_mem hd.1 this
    have h3 : ⁅E ⊓ C y, A ⊓ Q⁆ = ⊥ := by
      rw [eq_bot_iff, ← h66 x y (hVP hxV) (hXqQ hy) hx2 hy2]
      exact le_inf (h2.trans hEx) h1
    rw [commutator_eq_bot_iff_le_centralizer] at h3
    exact le_centralizer_iff.mp h3
  have hXqE : A ⊓ Q ≤ centralizer (E : Set G) :=
    @le_centralizer_of_forall_inf G _ _ E (A ⊓ Q) hXq hEodd (hXqJ.trans hJE) hloc
  have hM₁J : M₁ ≤ J := hM₁K.trans hKJ
  have hM₁E : M₁ ≤ centralizer (E : Set G) := by
    have hU : M₁ ≤ M₁ ⊓ centralizer (E : Set G) := by
      refine le_of_normal_of_not_le g hg hgker hcenM₁ hperf inf_le_left ?_ ?_
      · refine (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun m hm => ?_
        exact inf_normalizer_le_normalizer_inf
          ⟨le_normalizer hm, mem_normalizer_centralizer (hJE (hM₁J hm))⟩
      · intro hle
        exact not_le_O_of_isPGroup hXq2 hXq1 ((le_inf hXqM₁ hXqE).trans hle)
    exact hU.trans inf_le_right
  obtain ⟨LJ, _, fJ, f₂', hfJ, hf₂', hfJker, hf₂'ker⟩ := hJ₀iso
  obtain ⟨eL⟩ := nonempty_mulEquiv_of_ker_eq f₂ hf₂ f₂' hf₂' (hf₂ker.trans hf₂'ker.symm)
  have : IsSimpleGroup LJ := (MulEquiv.isSimpleGroup_congr eL.symm).mpr inferInstance
  have : Finite LJ := Finite.of_surjective fJ hfJ
  have : Group.IsPerfect L := ⟨hLperf⟩
  have hLJperf : commutator LJ = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := eL.toMonoidHom) eL.surjective).commutator_eq_top
  have hcardL : Nat.card LJ = Nat.card L := (Nat.card_congr eL.toEquiv).symm
  have hM₁J₀ : M₁ ≤ J₀ := hJ₀def ▸ (le_inf hM₁J hM₁M₀).trans le_sup_left
  set φ : M₁ →* LJ := fJ.comp (inclusion hM₁J₀) with hφdef
  have hφker : φ.ker ≤ g.ker := by
    intro m hm
    have hmO : (m : G) ∈ O J := by
      have : inclusion hM₁J₀ m ∈ fJ.ker := hm
      rw [hfJker] at this
      exact this
    have hle : M₁ ⊓ O J ≤ O M₁ := by
      refine le_O_of_normal inf_le_left ?_ (Odd.of_dvd_nat hEodd (card_dvd_of_le inf_le_right))
      exact (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk =>
        inf_normalizer_le_normalizer_inf ⟨le_normalizer hk, hJE (hM₁J hk)⟩
    rw [hgker]
    exact hle ⟨m.2, hmO⟩
  have hφ : Function.Surjective φ := surjective_of_ker_le φ g hg hφker hcardL.le
  obtain ⟨hD'J₀, hD'c, hD'n, hD'perf, -, -, -, -⟩ :=
    quasisimple_commutator_of_simple (T := M₁) (C := J₀ ⊓ centralizer (E : Set G))
      (M₁ := ⁅J₀ ⊓ centralizer (E : Set G), J₀ ⊓ centralizer (E : Set G)⁆) hLJperf hJ₀J hJ₀n fJ hfJ
      hfJker hM₁J₀ hM₁E (fun h => not_le_O_of_isPGroup hXq2 hXq1 (hXqM₁.trans h)) rfl rfl
  set D' := ⁅J₀ ⊓ centralizer (E : Set G), J₀ ⊓ centralizer (E : Set G)⁆ with hD'def
  have hM₁D' : M₁ ≤ D' := by
    calc M₁ = ⁅M₁, M₁⁆ := hperf.symm
      _ ≤ D' := commutator_mono (le_inf hM₁J₀ hM₁E) (le_inf hM₁J₀ hM₁E)
  have hD'M₁ : D' ≤ M₁ := by
    have hdec : ∀ d ∈ D', ∃ u ∈ M₁, ∃ z ∈ D', (∀ k ∈ D', Commute z k) ∧ d = u * z := by
      intro d hd
      obtain ⟨⟨m, hm⟩, hmd⟩ := hφ (fJ ⟨d, hD'J₀ hd⟩)
      have hz : m⁻¹ * d ∈ E := by
        have h1 : (⟨m, hM₁J₀ hm⟩ : J₀)⁻¹ * ⟨d, hD'J₀ hd⟩ ∈ fJ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv]
          exact inv_mul_eq_one.mpr hmd
        rw [hfJker] at h1
        exact h1
      refine ⟨m, hm, m⁻¹ * d, mul_mem (inv_mem (hM₁D' hm)) hd, fun k hk => ?_, by group⟩
      exact (mem_centralizer_iff.mp (hD'c hk) _ hz)
    calc D' = ⁅D', D'⁆ := hD'perf.symm
      _ ≤ ⁅M₁, M₁⁆ := commutator_le_of_forall_mul hM₁D' hdec
      _ = M₁ := hperf
  have hD'eq : D' = M₁ := le_antisymm hD'M₁ hM₁D'
  rw [hD'eq] at hD'n
  exact (normal_subgroupOf_iff_le_normalizer hM₁J).mp hD'n

end Sec7

end CFSG.GH72
