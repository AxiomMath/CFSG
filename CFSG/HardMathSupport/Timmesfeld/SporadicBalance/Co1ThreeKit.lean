module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Assembly.Defs
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

variable {p : ℕ} {S : Type*} [Group S]

theorem gLAPPrimeCoreOf_eq_bot_of_hyperplanes [Finite S] (hp : p.Prime) {C A : Subgroup S}
    (hA : IsElemAbelian p A) (hAC : A ≤ C) (hA1 : A ≠ ⊥)
    (hB : ∀ B : Subgroup S, B ≤ A → B.relIndex A = p →
      GLAPPrimeCoreOf p (C ⊓ Subgroup.centralizer (B : Set S)) = ⊥) :
    GLAPPrimeCoreOf p C = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set R := GLAPPrimeCoreOf p C with hRdef
  have hRC : R ≤ C := GLAPPrimeCoreOf_le C
  have hnorm : ∀ a ∈ A, ∀ x ∈ R, a * x * a⁻¹ ∈ R := fun a ha x hx =>
    GLAPPrimeCoreOf_conj_mem a (hAC ha) x hx
  have hcop : Nat.Coprime p (Nat.card R) := coprime_card_GLAPPrimeCoreOf hp C
  have hRp : ¬ p ∣ Nat.card R := (hp.coprime_iff_not_dvd).1 hcop
  let act : MulDistribMulAction ↥A ↥R :=
    { smul := fun a x => ⟨a * x * (a : S)⁻¹, hnorm a a.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change (1 : S) * (x : S) * (1 : S)⁻¹ = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        change ((a : S) * b) * (x : S) * ((a : S) * b)⁻¹ =
          a * ((b : S) * x * (b : S)⁻¹) * (a : S)⁻¹
        group)
      smul_one := fun a => Subtype.ext (by
        change (a : S) * 1 * (a : S)⁻¹ = 1
        simp)
      smul_mul := fun a x y => Subtype.ext (by
        change (a : S) * ((x : S) * y) * (a : S)⁻¹ = (a * x * (a : S)⁻¹) * (a * y * (a : S)⁻¹)
        group) }
  have : CFSG.IsElementaryAbelian p ↥A :=
    { toIsMulCommutative := hA.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hA.2 x x.2) }
  have : Nontrivial ↥A := by
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
    exact ⟨⟨a, 1, ha1⟩⟩
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := ↥A) (H := ↥R) hRp
  have hfix : ∀ B : Subgroup ↥A, B.index = p → CFSG.fixedPointSubgroup ↥B ↥R = ⊥ := by
    intro B hBi
    set Bs : Subgroup S := B.map A.subtype with hBs
    have hBsA : Bs ≤ A := Subgroup.map_subtype_le _
    have hrel : Bs.relIndex A = p := by
      have h : Bs.subgroupOf A = B :=
        Subgroup.comap_map_eq_self_of_injective A.subtype_injective B
      rw [Subgroup.relIndex, h]
      exact hBi
    rw [eq_bot_iff]
    intro x hx
    have hxR : (x : S) ∈ R := x.2
    have hxB : ∀ b ∈ Bs, b * (x : S) = (x : S) * b := by
      intro b hb
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
      have h1 : (⟨b', hb'⟩ : ↥B) • x = x := hx ⟨b', hb'⟩
      have h2 := congrArg Subtype.val h1
      change (b' : S) * x * (b' : S)⁻¹ = x at h2
      change (b' : S) * x = x * b'
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2
    have hle : R ⊓ Subgroup.centralizer (Bs : Set S) ≤
        GLAPPrimeCoreOf p (C ⊓ Subgroup.centralizer (Bs : Set S)) := by
      refine le_GLAPPrimeCoreOf_of_normal (inf_le_inf hRC le_rfl) ?_
        (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcop)
      intro g hg y hy
      obtain ⟨hgC, hgB⟩ := Subgroup.mem_inf.1 hg
      obtain ⟨hyR, hyB⟩ := Subgroup.mem_inf.1 hy
      refine Subgroup.mem_inf.2 ⟨GLAPPrimeCoreOf_conj_mem g hgC y hyR, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hgB hyB ⊢
      intro b hb
      have cbg : Commute b g := hgB b hb
      have cby : Commute b y := hyB b hb
      exact ((cbg.mul_right cby).mul_right cbg.inv_right).eq
    have hmem := hle (Subgroup.mem_inf.2 ⟨hxR, Subgroup.mem_centralizer_iff.2 hxB⟩)
    rw [hB Bs hBsA hrel] at hmem
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hmem))
  have hbot : ∀ B : Subgroup ↥A, ⨆ (_ : B.index = p), CFSG.fixedPointSubgroup ↥B ↥R = ⊥ := by
    intro B
    by_cases h : B.index = p
    · simp [h, hfix B h]
    · simp [h]
  have htop : (⊤ : Subgroup ↥R) = ⊥ := by
    rw [← hgen]
    simp [hbot]
  rw [eq_bot_iff]
  intro y hy
  have : (⟨y, hy⟩ : ↥R) ∈ (⊤ : Subgroup ↥R) := Subgroup.mem_top _
  rw [htop] at this
  exact congrArg Subtype.val (Subgroup.mem_bot.1 this)

theorem isPGroup_of_coprime_eq_one [Finite S] (hp : p.Prime) {H : Subgroup S}
    (h : ∀ g ∈ H, Nat.Coprime (orderOf g) p → g = 1) : IsPGroup p H := by
  intro g
  have hn0 : orderOf (g : S) ≠ 0 := (orderOf_pos_iff.2 (isOfFinOrder_of_finite _)).ne'
  obtain ⟨a, m, hm, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
  refine ⟨a, Subtype.ext ?_⟩
  have hpa : p ^ a ∣ orderOf (g : S) := heq ▸ Dvd.intro m rfl
  have hord : orderOf ((g : S) ^ p ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a hp.ne_zero) hpa, heq,
      Nat.mul_div_cancel_left m (pow_pos hp.pos a)]
  have hcop : Nat.Coprime (orderOf ((g : S) ^ p ^ a)) p := by
    rw [hord]
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hm))
  have := h _ (H.pow_mem g.2 _) hcop
  simpa using this

theorem list_sum_pow_two_pow {R : Type*} [Ring R] [CharP R 2] (k : ℕ) :
    ∀ l : List R, l.Pairwise Commute → l.sum ^ 2 ^ k = (l.map (· ^ 2 ^ k)).sum
  | [], _ => by
    simp only [List.sum_nil, List.map_nil]
    exact zero_pow (pow_ne_zero k two_ne_zero)
  | x :: l, hl => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [List.pairwise_cons] at hl
    have hc : Commute x l.sum := Commute.list_sum_right x l fun y hy => hl.1 y hy
    rw [List.sum_cons,
      add_pow_char_pow_of_commute (R := R) (p := 2) (n := k) (x := x) (y := l.sum) hc,
      list_sum_pow_two_pow k l hl.2, List.map_cons, List.sum_cons]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

end
