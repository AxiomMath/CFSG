module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEClasses
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.RankThree.GF2n.Stroth80.Sec117Config
import CFSG.RankThree.GF2n.Stroth80.Sec117ConfigBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem IsStrothInvolution.exists_conj_eq_of_orderOf_mul_conj_eq_six {X : Type*} [Group X]
    {t x₀ : X} {a : ℕ} {S : Set X} (h : IsStrothInvolution t a)
    (hS : t ^ 2 = 1 → t ≠ 1 → ∃ g : X, g * t * g⁻¹ ∈ S)
    (h6 : ∀ x ∈ S, x ≠ x₀ → ∃ c : X, orderOf (x * (c⁻¹ * x * c)) = 6) :
    ∃ g : X, g * t * g⁻¹ = x₀ := by
  have h2 : t ^ 2 = 1 := by
    rw [← h.orderOf_eq_two]
    exact pow_orderOf_eq_one t
  have h1 : t ≠ 1 := by
    intro h1
    have h3 := h.orderOf_eq_two
    rw [h1, orderOf_one] at h3
    omega
  obtain ⟨g, hg⟩ := hS h2 h1
  refine ⟨g, by_contra fun hne => ?_⟩
  obtain ⟨c, hc⟩ := h6 _ hg hne
  exact h.orderOf_mul_ne_six (isConj_iff.2 ⟨g, rfl⟩) (isConj_iff.2 ⟨c⁻¹ * g, by group⟩) hc

theorem IsKLConfig.le_of_sup_eq_centralizer {X : Type*} [Group X] [Finite X] {t : X} {a : ℕ}
    {N A Q L : Subgroup X} (h : IsKLConfig t a N A) (hQ : IsPGroup 2 Q)
    (hC : Q ⊔ L = Subgroup.centralizer {t}) (hLQ : L ≤ Subgroup.normalizer (Q : Set X))
    (hLN : L ≤ N) (hL : ∀ P : Subgroup L, P.Normal → IsPGroup 2 P → P = ⊥) : A ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAC : A ≤ Q ⊔ L := by
    rw [hC]
    exact fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (h.comm x hx t h.mem)
  have hAQ : IsPGroup 2 (A ⊔ Q : Subgroup X) :=
    h.isPGroup.to_sup_of_normal_right' hQ (hAC.trans (sup_le Subgroup.le_normalizer hLQ))
  have hconj : ∀ g ∈ L, ∀ x ∈ A ⊔ Q, g * x * g⁻¹ ∈ A ⊔ Q := by
    intro g hg x hx
    have hle : A ⊔ Q ≤ (A ⊔ Q).comap (MulAut.conj g).toMonoidHom :=
      sup_le (fun y hy => Subgroup.mem_sup_left (h.conj_mem g (hLN hg) y hy))
        (fun y hy => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hLQ hg) y).1 hy))
    exact hle hx
  have hP : (A ⊔ Q).subgroupOf L = ⊥ :=
    hL _ ⟨fun x hx g => Subgroup.mem_subgroupOf.2 (hconj g g.2 x (Subgroup.mem_subgroupOf.1 hx))⟩
      (hAQ.comap_of_injective L.subtype L.subtype_injective)
  intro x hx
  have hx' : x ∈ ((Q ⊔ L : Subgroup X) : Set X) := hAC hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q L hLQ] at hx'
  obtain ⟨q, hq, l, hl, rfl⟩ := Set.mem_mul.1 hx'
  have hl1 : (⟨l, hl⟩ : L) ∈ (A ⊔ Q).subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]
    have := mul_mem (Subgroup.mem_sup_right (inv_mem hq) : q⁻¹ ∈ A ⊔ Q)
      (Subgroup.mem_sup_left hx : q * l ∈ A ⊔ Q)
    simpa using this
  rw [hP, Subgroup.mem_bot] at hl1
  obtain rfl : l = 1 := by simpa using congrArg Subtype.val hl1
  simpa using hq

end CFSG.RankThree.GF2n.Stroth80

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

variable {τ : Tag} {K : Type} [Field K]

section OrderThree

private theorem coe_uSL_one_mul_vSL_one [CharP K 2] :
    ((uSL (1 : K) * vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 1] := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

private theorem uSL_one_mul_vSL_one_pow_three [CharP K 2] : (uSL (1 : K) * vSL 1) ^ 3 = 1 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_uSL_one_mul_vSL_one,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h2]

private theorem uSL_one_mul_vSL_one_ne_one [CharP K 2] : uSL (1 : K) * vSL 1 ≠ 1 := by
  intro h
  have h1 := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [coe_uSL_one_mul_vSL_one, Matrix.SpecialLinearGroup.coe_one] at h1
  simp at h1

theorem orderOf_pinnedX_mul_pinnedX_neg_one
    [CharP K 2] {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    orderOf (pinnedX τ K α 1 * pinnedX τ K (-α) 1) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hinj, -, -, huv, -⟩ := even_Chevalley_pinned_root_SL2_maps τ K hα
  rw [← (huv 1).1, ← (huv 1).2, ← map_mul, orderOf_injective _ hinj]
  exact orderOf_eq_prime uSL_one_mul_vSL_one_pow_three uSL_one_mul_vSL_one_ne_one

end OrderThree

@[expose] def oddDerivFrameSixB (τ : Tag) (d : Fin τ.rank → ℤ) : List (Fin τ.rank → ℤ) → Bool
  | b₀ :: b₁ :: bs =>
    (b₀ :: d :: (b₁ + d) :: b₁ :: bs).all (oddDerivIsRootB τ) && !oddDerivVecEq d b₁ &&
      !oddDerivVecEq d (-b₁) &&
      ((d :: b₁ :: bs).all fun v => oddDerivCommB τ v b₀ && oddDerivCommB τ v (-b₀)) &&
      (bs.all fun v => oddDerivCommB τ v d) &&
      ((b₁ + d) :: b₁ :: bs).all fun v => (b₁ :: bs).all (oddDerivCommB τ v)
  | _ => false

section Frame


section

private theorem orderOf_mul_conj_eq_three_of_sq_eq_one {s y : adjointGroup τ K}
    (hs : s * s = 1) (hy : y * y = 1) (h3 : orderOf (s * y) = 3) :
    orderOf (s * ((s * y * s)⁻¹ * s * (s * y * s))) = 3 := by
  have hsy3 : (s * y) ^ 3 = 1 := by simpa [h3] using pow_orderOf_eq_one (s * y)
  have h3' : s * y * s * y * s = y := by
    have h : s * y * s * y * s * y = 1 := by
      simpa [pow_succ, pow_two, mul_assoc] using hsy3
    calc s * y * s * y * s = s * y * s * y * s * (y * y) := by rw [hy, mul_one]
      _ = s * y * s * y * s * y * y := by group
      _ = y := by rw [h, one_mul]
  have hg0 : (s * y * s) * (s * y * s) = 1 := by
    calc (s * y * s) * (s * y * s) = s * (y * (s * s)) * y * s := by group
      _ = s * y * y * s := by rw [hs, mul_one]
      _ = s * (y * y) * s := by group
      _ = s * s := by rw [hy, mul_one]
      _ = 1 := hs
  have hconj : (s * y * s)⁻¹ * s * (s * y * s) = y := by
    rw [inv_eq_of_mul_eq_one_right hg0]
    show (s * y * s) * s * (s * y * s) = y
    calc (s * y * s) * s * (s * y * s) = s * y * (s * s) * (s * y * s) := by group
      _ = s * y * (s * y * s) := by rw [hs, mul_one]
      _ = s * y * s * y * s := by group
      _ = y := h3'
  rw [hconj]
  exact h3

private theorem frameSixB_centralizer {s y s' c : adjointGroup τ K}
    (hss' : Commute s' s) (hys' : Commute s' y) (hsc : Commute c s) (hyc : Commute c y) :
    (∀ j ∈ Subgroup.closure ({s, y} : Set (adjointGroup τ K)), s' * j = j * s') ∧
      (∀ j ∈ Subgroup.closure ({s, y} : Set (adjointGroup τ K)), c * j = j * c) := by
  have key : ∀ {k : adjointGroup τ K}, Commute k s → Commute k y →
      ∀ j ∈ Subgroup.closure ({s, y} : Set (adjointGroup τ K)), Commute j k := by
    intro k hks hky j hj
    have hle : Subgroup.closure ({s, y} : Set (adjointGroup τ K)) ≤
        Subgroup.centralizer ({k} : Set (adjointGroup τ K)) := by
      rw [Subgroup.closure_le]
      intro h hh
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rcases hh with rfl | rfl
      · exact hks.symm.eq
      · exact hky.symm.eq
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hj)
  exact ⟨fun j hj => (key hss' hys' j hj).eq.symm, fun j hj => (key hsc hyc j hj).eq.symm⟩

private theorem frameSixB_comm {s' c x : adjointGroup τ K}
    (hconjc : c⁻¹ * s' * c = x * s') (hx : Commute s' x) :
    s' * (c⁻¹ * s' * c) = c⁻¹ * s' * c * s' := by
  rw [hconjc]
  calc s' * (x * s') = (s' * x) * s' := by group
    _ = (x * s') * s' := by rw [hx.eq]

private theorem frameSixB_ne {s' c x : adjointGroup τ K}
    (hconjc : c⁻¹ * s' * c = x * s') (hx : x ≠ 1) :
    c⁻¹ * s' * c ≠ s' := by
  rw [hconjc]
  intro h
  apply hx
  calc x = x * s' * s'⁻¹ := by group
    _ = s' * s'⁻¹ := by rw [h]
    _ = 1 := by group

end

section

private theorem frameSixB_root_facts {b₀ b₁ : Fin τ.rank → ℤ} {bs : List (Fin τ.rank → ℤ)}
    {d : Fin τ.rank → ℤ} (hF : oddDerivFrameSixB τ d (b₀ :: b₁ :: bs) = true) :
    IsRoot τ b₀ ∧ IsRoot τ d ∧ IsRoot τ (b₁ + d) ∧ IsRoot τ b₁ ∧
      (∀ v ∈ bs, IsRoot τ v) ∧ d ≠ b₁ ∧ d ≠ -b₁ := by
  simp only [oddDerivFrameSixB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at hF
  obtain ⟨⟨⟨⟨⟨hroots, hne₁⟩, hne₂⟩, -⟩, -⟩, -⟩ := hF
  have hroot : ∀ v ∈ b₀ :: d :: (b₁ + d) :: b₁ :: bs, IsRoot τ v :=
    fun v hv => isRoot_of_oddDerivIsRootB (hroots v hv)
  have hb₀ : IsRoot τ b₀ := hroot b₀ (by simp)
  have hd : IsRoot τ d := hroot d (by simp)
  have hbd : IsRoot τ (b₁ + d) := hroot (b₁ + d) (by simp)
  have hb₁ : IsRoot τ b₁ := hroot b₁ (by simp)
  have hbs : ∀ v ∈ bs, IsRoot τ v := fun v hv => hroot v (by simp [hv])
  refine ⟨hb₀, hd, hbd, hb₁, hbs, ?_, ?_⟩
  · intro h
    rw [h, oddDerivVecEq_self] at hne₁
    exact Bool.false_ne_true hne₁.symm
  · intro h
    rw [h, oddDerivVecEq_self] at hne₂
    exact Bool.false_ne_true hne₂.symm

end

section

private theorem pinnedX_mul_self [CharP K 2] (v : Fin τ.rank → ℤ) :
    pinnedX τ K v 1 * pinnedX τ K v 1 = 1 := by
  rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

private theorem pinnedX_adjointGroup_ne_one (v : Fin τ.rank → ℤ) :
    (⟨pinnedX τ K v 1, pinnedX_mem_adjointGroup v 1⟩ : adjointGroup τ K) ≠ 1 := by
  intro h
  have h1 : pinnedX τ K v 1 = pinnedX τ K v 0 := by
    rw [pinnedX_zero]
    exact congrArg Subtype.val h
  exact one_ne_zero (pinnedX_injective τ K v h1)

private theorem prod_map_pinnedX_sq_eq_one (L : List (Fin τ.rank → ℤ))
    (hsq : ∀ v ∈ L, pinnedX τ K v 1 * pinnedX τ K v 1 = 1)
    (hc : ∀ v ∈ L, ∀ w ∈ L, Commute (pinnedX τ K v 1) (pinnedX τ K w 1)) :
    ((L.map fun v => pinnedX τ K v 1).prod) ^ 2 = 1 := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, pow_two]
    have hP : ((l.map fun v => pinnedX τ K v 1).prod) *
        ((l.map fun v => pinnedX τ K v 1).prod) = 1 := by
      rw [← pow_two]
      exact ih (fun v hv => hsq v (List.mem_cons_of_mem a hv))
        (fun v hv w hw => hc v (List.mem_cons_of_mem a hv) w (List.mem_cons_of_mem a hw))
    have ha : pinnedX τ K a 1 * pinnedX τ K a 1 = 1 := hsq a List.mem_cons_self
    have hcomm : Commute (pinnedX τ K a 1) ((l.map fun v => pinnedX τ K v 1).prod) :=
      Commute.list_prod_right _ _ (List.forall_mem_map.2 fun v hv =>
        hc a List.mem_cons_self v (List.mem_cons_of_mem a hv))
    calc pinnedX τ K a 1 * (l.map fun v => pinnedX τ K v 1).prod *
          (pinnedX τ K a 1 * (l.map fun v => pinnedX τ K v 1).prod)
        = pinnedX τ K a 1 * ((l.map fun v => pinnedX τ K v 1).prod * pinnedX τ K a 1) *
            (l.map fun v => pinnedX τ K v 1).prod := by group
      _ = pinnedX τ K a 1 * (pinnedX τ K a 1 * (l.map fun v => pinnedX τ K v 1).prod) *
            (l.map fun v => pinnedX τ K v 1).prod := by rw [hcomm.eq]
      _ = pinnedX τ K a 1 * pinnedX τ K a 1 *
            ((l.map fun v => pinnedX τ K v 1).prod *
              (l.map fun v => pinnedX τ K v 1).prod) := by group
      _ = 1 := by rw [ha, hP, mul_one]

private theorem pinnedX_mul_prod_mul_pinnedX {a d : Fin τ.rank → ℤ}
    {l : List (Fin τ.rank → ℤ)}
    (hbase : pinnedX τ K d 1 * pinnedX τ K a 1 * pinnedX τ K d 1 =
      pinnedX τ K (a + d) 1 * pinnedX τ K a 1)
    (hc : Commute (pinnedX τ K d 1) ((l.map fun v => pinnedX τ K v 1).prod)) :
    pinnedX τ K d 1 * ((a :: l).map fun v => pinnedX τ K v 1).prod * pinnedX τ K d 1 =
      pinnedX τ K (a + d) 1 * ((a :: l).map fun v => pinnedX τ K v 1).prod := by
  rw [List.map_cons, List.prod_cons]
  calc pinnedX τ K d 1 * (pinnedX τ K a 1 * (l.map fun v => pinnedX τ K v 1).prod) *
        pinnedX τ K d 1
      = pinnedX τ K d 1 * pinnedX τ K a 1 *
          ((l.map fun v => pinnedX τ K v 1).prod * pinnedX τ K d 1) := by group
    _ = pinnedX τ K d 1 * pinnedX τ K a 1 *
          (pinnedX τ K d 1 * (l.map fun v => pinnedX τ K v 1).prod) := by rw [hc.eq]
    _ = (pinnedX τ K d 1 * pinnedX τ K a 1 * pinnedX τ K d 1) *
          (l.map fun v => pinnedX τ K v 1).prod := by group
    _ = (pinnedX τ K (a + d) 1 * pinnedX τ K a 1) *
          (l.map fun v => pinnedX τ K v 1).prod := by rw [hbase]
    _ = pinnedX τ K (a + d) 1 *
          (pinnedX τ K a 1 * (l.map fun v => pinnedX τ K v 1).prod) := by group

private theorem frameSixB_order_two [CharP K 2] {b₁ : Fin τ.rank → ℤ}
    {bs : List (Fin τ.rank → ℤ)}
    {s' : adjointGroup τ K}
    (hs' : (s' : ModGL τ K) = ((b₁ :: bs).map fun v => pinnedX τ K v 1).prod)
    (hpair : ∀ v ∈ b₁ :: bs, ∀ w ∈ b₁ :: bs, Commute (pinnedX τ K v 1) (pinnedX τ K w 1))
    (hne : s' ≠ 1) : orderOf s' = 2 := by
  have hprod := prod_map_pinnedX_sq_eq_one (b₁ :: bs) (fun v _ => pinnedX_mul_self v) hpair
  rw [pow_two] at hprod
  refine orderOf_eq_prime (p := 2) ?_ hne
  rw [pow_two]
  exact Subtype.ext (by simpa [hs'] using hprod)

private theorem frameSixB_commute_adjointGroup {b₀ b₁ d : Fin τ.rank → ℤ}
    {bs : List (Fin τ.rank → ℤ)} {s y s' c x : adjointGroup τ K}
    (hs : (s : ModGL τ K) = pinnedX τ K b₀ 1)
    (hy : (y : ModGL τ K) = pinnedX τ K (-b₀) 1)
    (hs' : (s' : ModGL τ K) = ((b₁ :: bs).map fun v => pinnedX τ K v 1).prod)
    (hc : (c : ModGL τ K) = pinnedX τ K d 1)
    (hx : (x : ModGL τ K) = pinnedX τ K (b₁ + d) 1)
    (hcs : ∀ v ∈ b₁ :: bs, Commute (pinnedX τ K v 1) (pinnedX τ K b₀ 1))
    (hcy : ∀ v ∈ b₁ :: bs, Commute (pinnedX τ K v 1) (pinnedX τ K (-b₀) 1))
    (hcds : Commute (pinnedX τ K d 1) (pinnedX τ K b₀ 1))
    (hcdy : Commute (pinnedX τ K d 1) (pinnedX τ K (-b₀) 1))
    (hbdcomm : ∀ v ∈ b₁ :: bs, Commute (pinnedX τ K (b₁ + d) 1) (pinnedX τ K v 1)) :
    Commute s' s ∧ Commute s' y ∧ Commute c s ∧ Commute c y ∧ Commute s' x := by
  have h1 : Commute (pinnedX τ K b₀ 1)
      ((b₁ :: bs).map fun v => pinnedX τ K v 1).prod :=
    Commute.list_prod_right _ _ (List.forall_mem_map.2 fun v hv => (hcs v hv).symm)
  have h2 : Commute (pinnedX τ K (-b₀) 1)
      ((b₁ :: bs).map fun v => pinnedX τ K v 1).prod :=
    Commute.list_prod_right _ _ (List.forall_mem_map.2 fun v hv => (hcy v hv).symm)
  have h5 : Commute ((b₁ :: bs).map fun v => pinnedX τ K v 1).prod
      (pinnedX τ K (b₁ + d) 1) :=
    Commute.list_prod_left _ _ (List.forall_mem_map.2 fun v hv => (hbdcomm v hv).symm)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext (by simpa [hs, hs'] using h1.eq.symm)
  · exact Subtype.ext (by simpa [hy, hs'] using h2.eq.symm)
  · exact Subtype.ext (by simpa [hs, hc] using hcds.eq)
  · exact Subtype.ext (by simpa [hy, hc] using hcdy.eq)
  · exact Subtype.ext (by simpa [hs', hx] using h5.eq)

end

private theorem commute_pinnedX_of_oddDerivCommB {R : Type*} [CommRing R]
    {γ σ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hσ : IsRoot τ σ)
    (h : oddDerivCommB τ γ σ = true) (c e : R) :
    Commute (pinnedX τ R γ c) (pinnedX τ R σ e) := by
  rw [oddDerivCommB, Bool.or_eq_true] at h
  rcases h with he | h
  · rw [eq_of_oddDerivVecEq he]
    show pinnedX τ R σ c * pinnedX τ R σ e = pinnedX τ R σ e * pinnedX τ R σ c
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · rw [Bool.and_eq_true] at h
    obtain ⟨hne, hn⟩ := h
    refine commute_pinnedX_of_oddDeriv hγ hσ ?_ (not_isRoot_of_oddDerivNotRootB hn) c e
    intro he
    rw [he, oddDerivVecEq_self] at hne
    exact Bool.false_ne_true hne

private theorem pinnedX_mul_pinnedX_mul_pinnedX_eq [CharP K 2]
    (hτ : oddDerivLacedCheck τ = true) {a d : Fin τ.rank → ℤ} (ha : IsRoot τ a)
    (hd : IsRoot τ d) (hne : d ≠ a) (hne' : d ≠ -a) (had : IsRoot τ (a + d)) :
    pinnedX τ K d 1 * pinnedX τ K a 1 * pinnedX τ K d 1 =
      pinnedX τ K (a + d) 1 * pinnedX τ K a 1 := by
  have hinv' (v : Fin τ.rank → ℤ) : (pinnedX τ K v 1)⁻¹ = pinnedX τ K v 1 :=
    inv_eq_of_mul_eq_one_right (pinnedX_mul_self v)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hcomm := commutatorElement_pinnedX_of_oddDerivLaced (τ := τ) (R := K) h2 hτ hd ha
    hne hne' (by rwa [add_comm]) (1 : K) (1 : K)
  rw [commutatorElement_def, hinv' d, hinv' a, mul_one] at hcomm
  calc pinnedX τ K d 1 * pinnedX τ K a 1 * pinnedX τ K d 1
      = pinnedX τ K d 1 * pinnedX τ K a 1 * pinnedX τ K d 1 *
          (pinnedX τ K a 1 * pinnedX τ K a 1) := by rw [pinnedX_mul_self a, mul_one]
    _ = (pinnedX τ K d 1 * pinnedX τ K a 1 * pinnedX τ K d 1 * pinnedX τ K a 1) *
          pinnedX τ K a 1 := by group
    _ = pinnedX τ K (d + a) 1 * pinnedX τ K a 1 := by rw [hcomm]
    _ = pinnedX τ K (a + d) 1 * pinnedX τ K a 1 := by rw [add_comm d a]

private theorem frameSixB_commute_facts {b₀ b₁ : Fin τ.rank → ℤ}
    {bs : List (Fin τ.rank → ℤ)} {d : Fin τ.rank → ℤ}
    (hb₀ : IsRoot τ b₀) (hd : IsRoot τ d) (hbd : IsRoot τ (b₁ + d)) (hb₁ : IsRoot τ b₁)
    (hbs : ∀ v ∈ bs, IsRoot τ v)
    (hF : oddDerivFrameSixB τ d (b₀ :: b₁ :: bs) = true) :
    Commute (pinnedX τ K d 1) (pinnedX τ K b₀ 1) ∧
      Commute (pinnedX τ K d 1) (pinnedX τ K (-b₀) 1) ∧
      (∀ v ∈ b₁ :: bs, Commute (pinnedX τ K v 1) (pinnedX τ K b₀ 1)) ∧
      (∀ v ∈ b₁ :: bs, Commute (pinnedX τ K v 1) (pinnedX τ K (-b₀) 1)) ∧
      (∀ v ∈ bs, Commute (pinnedX τ K v 1) (pinnedX τ K d 1)) ∧
      (∀ v ∈ b₁ :: bs, Commute (pinnedX τ K (b₁ + d) 1) (pinnedX τ K v 1)) ∧
      (∀ v ∈ b₁ :: bs, ∀ w ∈ b₁ :: bs,
        Commute (pinnedX τ K v 1) (pinnedX τ K w 1)) := by
  simp only [oddDerivFrameSixB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at hF
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hcomm₁⟩, hcomm₂⟩, hcomm₃⟩ := hF
  have hmem : ∀ v ∈ b₁ :: bs, IsRoot τ v := by
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hb₁
    · exact hbs v hv
  exact ⟨commute_pinnedX_of_oddDerivCommB hd hb₀ (hcomm₁ d (by simp)).1 1 1,
    commute_pinnedX_of_oddDerivCommB hd (IsRoot.neg hb₀) (hcomm₁ d (by simp)).2 1 1,
    fun v hv => commute_pinnedX_of_oddDerivCommB (hmem v hv) hb₀
      (hcomm₁ v (List.mem_cons_of_mem d hv)).1 1 1,
    fun v hv => commute_pinnedX_of_oddDerivCommB (hmem v hv) (IsRoot.neg hb₀)
      (hcomm₁ v (List.mem_cons_of_mem d hv)).2 1 1,
    fun v hv => commute_pinnedX_of_oddDerivCommB (hbs v hv) hd (hcomm₂ v hv) 1 1,
    fun v hv => commute_pinnedX_of_oddDerivCommB hbd (hmem v hv)
      (hcomm₃ (b₁ + d) (by simp) v hv) 1 1,
    fun v hv w hw => commute_pinnedX_of_oddDerivCommB (hmem v hv) (hmem w hw)
      (hcomm₃ v (List.mem_cons_of_mem (b₁ + d) hv) w hw) 1 1⟩

private theorem frameSixB_conj_prod [CharP K 2] (hlaced : oddDerivLacedCheck τ = true)
    {b₁ d : Fin τ.rank → ℤ} {bs : List (Fin τ.rank → ℤ)}
    (hb₁ : IsRoot τ b₁) (hd : IsRoot τ d) (hbd : IsRoot τ (b₁ + d))
    (hdne : d ≠ b₁) (hdne' : d ≠ -b₁)
    (hdcomm : ∀ v ∈ bs, Commute (pinnedX τ K v 1) (pinnedX τ K d 1))
    {x p x' : adjointGroup τ K}
    (hx : (x : ModGL τ K) = pinnedX τ K d 1)
    (hp : (p : ModGL τ K) = ((b₁ :: bs).map fun v => pinnedX τ K v 1).prod)
    (hx' : (x' : ModGL τ K) = pinnedX τ K (b₁ + d) 1) :
    x⁻¹ * p * x = x' * p := by
  have hbase := pinnedX_mul_pinnedX_mul_pinnedX_eq (K := K) hlaced hb₁ hd hdne hdne' hbd
  have hprod : pinnedX τ K d 1 * ((b₁ :: bs).map fun v => pinnedX τ K v 1).prod *
      pinnedX τ K d 1 = pinnedX τ K (b₁ + d) 1 *
        ((b₁ :: bs).map fun v => pinnedX τ K v 1).prod :=
    pinnedX_mul_prod_mul_pinnedX hbase
      (Commute.list_prod_right _ _ (List.forall_mem_map.2 fun v hv => (hdcomm v hv).symm))
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx, hp, hx']
  rw [inv_eq_of_mul_eq_one_right (pinnedX_mul_self d)]
  exact hprod

section

private theorem frameSixB_order_three [CharP K 2] {b₀ : Fin τ.rank → ℤ} (hb₀ : IsRoot τ b₀)
    {s y : adjointGroup τ K} (hs : (s : ModGL τ K) = pinnedX τ K b₀ 1)
    (hy : (y : ModGL τ K) = pinnedX τ K (-b₀) 1) :
    orderOf (s * ((s * y * s)⁻¹ * s * (s * y * s))) = 3 := by
  have hs2 : s * s = 1 := Subtype.ext (by simpa [hs] using pinnedX_mul_self b₀)
  have hy2 : y * y = 1 := Subtype.ext (by simpa [hy] using pinnedX_mul_self (-b₀))
  have h3 : orderOf (s * y) = 3 := by
    rw [← Subgroup.orderOf_coe (s * y)]
    simpa [Subgroup.coe_mul, hs, hy] using
      orderOf_pinnedX_mul_pinnedX_neg_one (τ := τ) (K := K) hb₀
  exact orderOf_mul_conj_eq_three_of_sq_eq_one hs2 hy2 h3

end

theorem exists_orderOf_frame_mul_conj_eq_six [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {F : List (Fin τ.rank → ℤ)} {d : Fin τ.rank → ℤ} (hF : oddDerivFrameSixB τ d F = true) :
    ∃ g : adjointGroup τ K,
      orderOf ((⟨(F.map fun σ => pinnedX τ K σ 1).prod,
          list_prod_map_pinnedX_mem_adjointGroup _⟩ : adjointGroup τ K) *
        (g⁻¹ * ⟨(F.map fun σ => pinnedX τ K σ 1).prod,
          list_prod_map_pinnedX_mem_adjointGroup _⟩ * g)) = 6 := by
  rcases F with _ | ⟨b₀, F⟩
  · simp [oddDerivFrameSixB] at hF
  rcases F with _ | ⟨b₁, bs⟩
  · simp [oddDerivFrameSixB] at hF
  obtain ⟨hb₀, hd, hbd, hb₁, hbs, hdne, hdne'⟩ := frameSixB_root_facts hF
  obtain ⟨hcds, hcdy, hcs, hcy, hdcomm, hbdcomm, hpair⟩ :=
    frameSixB_commute_facts (K := K) hb₀ hd hbd hb₁ hbs hF
  let s : adjointGroup τ K := ⟨pinnedX τ K b₀ 1, pinnedX_mem_adjointGroup _ _⟩
  let y : adjointGroup τ K := ⟨pinnedX τ K (-b₀) 1, pinnedX_mem_adjointGroup _ _⟩
  let c : adjointGroup τ K := ⟨pinnedX τ K d 1, pinnedX_mem_adjointGroup _ _⟩
  let x : adjointGroup τ K := ⟨pinnedX τ K (b₁ + d) 1, pinnedX_mem_adjointGroup _ _⟩
  let s' : adjointGroup τ K :=
    ⟨((b₁ :: bs).map fun v => pinnedX τ K v 1).prod, list_prod_map_pinnedX_mem_adjointGroup _⟩
  let g₀ := s * y * s
  let J : Subgroup (adjointGroup τ K) := Subgroup.closure {s, y}
  have hs : s ∈ J := Subgroup.subset_closure (Or.inl rfl)
  have hy : y ∈ J := Subgroup.subset_closure (Or.inr rfl)
  have hg : g₀ ∈ J := J.mul_mem (J.mul_mem hs hy) hs
  have hconjc : c⁻¹ * s' * c = x * s' :=
    frameSixB_conj_prod (oddDerivLacedCheck_of_simplyLaced (Or.inr hτ)) hb₁ hd hbd hdne hdne'
      hdcomm rfl rfl rfl
  have hne : c⁻¹ * s' * c ≠ s' := frameSixB_ne hconjc (pinnedX_adjointGroup_ne_one (b₁ + d))
  have h3 : orderOf (s * (g₀⁻¹ * s * g₀)) = 3 := frameSixB_order_three hb₀ rfl rfl
  have hs'ne : s' ≠ 1 := fun h1 => hne (by rw [h1]; group)
  have hs'2 : orderOf s' = 2 := frameSixB_order_two (s' := s') rfl hpair hs'ne
  obtain ⟨hss', hys', hsc, hyc, hs'x⟩ :=
    frameSixB_commute_adjointGroup (s := s) (y := y) (s' := s') (c := c) (x := x)
      rfl rfl rfl rfl rfl hcs hcy hcds hcdy hbdcomm
  obtain ⟨hs', hc⟩ := frameSixB_centralizer hss' hys' hsc hyc
  have hcomm : s' * (c⁻¹ * s' * c) = c⁻¹ * s' * c * s' := frameSixB_comm hconjc hs'x
  have key := CFSG.RankThree.GF2n.Stroth80.orderOf_mul_conj_eq_six (J := J) (s := s)
    (s' := s') (g := g₀) (c := c) hs hg hs' hc hs'2 h3 hne hcomm
  exact ⟨g₀ * c, key⟩

end Frame

end CFSG.SeitzReduction.EPilot
