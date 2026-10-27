module

public import CFSG.ClassicalInvolution.Q3.Sec13RecogLabel
public import CFSG.ClassicalInvolution.Q3.Sec13RecogS

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

structure AERecog (Ω : Set (Subgroup G)) (n : ℕ) where
  V : Subgroup G
  H : Subgroup G
  σ : H →* Equiv.Perm (Fin n)
  β : Multiplicative (Fin n → ZMod 2) →* G
  split : AESplitHyp V H σ β
  alt : σ.range = alternatingGroup (Fin n)
  member : ∃ K ∈ Ω, ∃ (α : Finset (Fin n)) (hα : α.card = 4) (b : Bool) (φ : G →* AE.AEQ n),
    (∀ f : Multiplicative (Fin n → ZMod 2), ∑ i, f.toAdd i = 0 →
      φ (β f) = AE.mkQ n (AE.Wr.ofVec f.toAdd)) ∧
    (∀ x : H, φ x = AE.mkQ n (AE.Wr.ofPerm (σ x))) ∧ K.map φ = AE.memBar α hα b

theorem AERecog.nonempty_aeIdent {Ω : Set (Subgroup G)} {n : ℕ} (R : AERecog Ω n) (hn : 5 ≤ n)
    (hinv : ∀ g : G, ∀ L ∈ Ω, conjSub g L ∈ Ω)
    (htrans : ∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ g : G, conjSub g L = L') (hgen : pSpan Ω = ⊤) :
    Nonempty (AEIdent Ω n) := by
  obtain ⟨K, hK, α, hα, b, φ, hφβ, hφH, hKφ⟩ := R.member
  obtain ⟨φ', hinj, hrange, hβ', hH'⟩ := R.split.exists_hom_aeModel R.alt
  have heq : φ' = φ := by
    refine MonoidHom.ext fun g => ?_
    obtain ⟨f, hf, x, rfl⟩ := R.split.exists_eq_mul g
    rw [map_mul, map_mul, hβ' f hf, hφβ f hf, hH' x, hφH x]
  have hKφ' : K.map φ' = AE.memBar α hα b := by
    rw [heq]
    exact hKφ
  exact nonempty_aeIdent_of_hom hinv htrans hgen hn φ' hinj hrange hK hα hKφ'

private abbrev e15r_commGroup {D : Subgroup G} (hab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) :
    CommGroup D :=
  { (inferInstance : Group D) with
    mul_comm := fun a b => Subtype.ext (hab a a.2 b b.2) }

private theorem e15r_pow_add_val {X : Type*} [Group X] {x : X} (hx : x * x = 1) (a b : ZMod 2) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  have v0 : (0 : ZMod 2).val = 0 := rfl
  have v1 : (1 : ZMod 2).val = 1 := rfl
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl
  · simp [v0]
  · simp [v0, v1]
  · simp [v0, v1]
  · rw [h11, v0, v1, pow_zero, pow_one, hx]

theorem exists_aeSplitHyp_of_points {n : ℕ} (hn : Odd n) {D H : Subgroup G}
    (hcompl : D.IsComplement' H) (hab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hsq : ∀ a ∈ D, a * a = 1) (pt : Fin n → G) (hpt : Function.Injective pt)
    (hptD : ∀ i, pt i ∈ D) (hprod : (List.ofFn pt).prod = 1)
    (hspan : Subgroup.closure (Set.range pt) = D) (hcard : Nat.card D = 2 ^ (n - 1))
    (hinv : ∀ h ∈ H, ∀ i, ∃ j, h * pt i * h⁻¹ = pt j)
    (hfaith : ∀ h ∈ H, (∀ i, h * pt i * h⁻¹ = pt i) → h = 1) :
    ∃ (σ : H →* Equiv.Perm (Fin n)) (β : Multiplicative (Fin n → ZMod 2) →* G),
      AESplitHyp D H σ β ∧ (∀ i, β (Multiplicative.ofAdd (Pi.single i 1)) = pt i) ∧
        ∀ (h : H) (i : Fin n), (h : G) * pt i * (h : G)⁻¹ = pt (σ h i) := by
  letI : CommGroup D := e15r_commGroup hab
  obtain ⟨p, hp⟩ : ∃ p : Fin n → D, ∀ i, (p i : G) = pt i :=
    ⟨fun i => ⟨pt i, hptD i⟩, fun i => rfl⟩
  have hpp : ∀ i, p i * p i = 1 := fun i =>
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one, hp i]; exact hsq _ (hptD i))
  obtain ⟨B, hB⟩ : ∃ B : Multiplicative (Fin n → ZMod 2) →* D,
      ∀ f, B f = ∏ i, p i ^ (f.toAdd i).val :=
    ⟨{ toFun := fun f => ∏ i, p i ^ (f.toAdd i).val
       map_one' := by simp
       map_mul' := fun f g => by
         simp only [toAdd_mul, Pi.add_apply]
         rw [← Finset.prod_mul_distrib]
         exact Finset.prod_congr rfl fun i _ => e15r_pow_add_val (hpp i) _ _ }, fun f => rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Multiplicative (Fin n → ZMod 2) →* G, ∀ f, β f = (B f : G) :=
    ⟨D.subtype.comp B, fun f => rfl⟩
  have v0 : (0 : ZMod 2).val = 0 := rfl
  have v1 : (1 : ZMod 2).val = 1 := rfl
  have hBi : ∀ i, B (Multiplicative.ofAdd (Pi.single i 1)) = p i := by
    intro i
    rw [hB, toAdd_ofAdd, Finset.prod_eq_single i]
    · simp [v1]
    · intro j _ hji
      simp [Pi.single_apply, hji, v0]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hβpt : ∀ i, β (Multiplicative.ofAdd (Pi.single i 1)) = pt i := by
    intro i
    rw [hβ, hBi, hp]
  have hVeq : β.range = D := by
    apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      rw [hβ]
      exact (B f).2
    · rw [← hspan, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (Pi.single i 1), hβpt i⟩
  have hβ1 : β (Multiplicative.ofAdd fun _ : Fin n => (1 : ZMod 2)) = 1 := by
    have hmap : (List.ofFn p).map Subtype.val = List.ofFn pt := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact hp i
    have hsub : ∀ l : List D, ((l.prod : D) : G) = (l.map Subtype.val).prod := fun l =>
      map_list_prod D.subtype l
    rw [hβ, hB]
    simp only [toAdd_ofAdd, v1, pow_one]
    rw [← List.prod_ofFn, hsub, hmap, hprod]
  have hπne : Multiplicative.ofAdd (fun _ : Fin n => (1 : ZMod 2)) ≠ 1 := by
    intro h
    have h' : (1 : ZMod 2) = 0 :=
      congrArg (fun x : Multiplicative (Fin n → ZMod 2) => x.toAdd ⟨0, hn.pos⟩) h
    exact absurd h' (by decide)
  have hK2 : Nat.card β.ker = 2 := by
    have hdom : Nat.card (Multiplicative (Fin n → ZMod 2)) = 2 ^ n := by
      simp [Nat.card_eq_fintype_card, ZMod.card]
    have h1 := β.ker.card_mul_index
    rw [Subgroup.index_ker, hVeq, hcard, hdom] at h1
    have h2 : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      have := hn.pos
      omega
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  have hker : ∀ f : Multiplicative (Fin n → ZMod 2), β f = 1 ↔
      (f.toAdd = 0 ∨ f.toAdd = fun _ : Fin n => (1 : ZMod 2)) := by
    intro f
    constructor
    · intro hf
      have hfK : f ∈ β.ker := hf
      have hπK : Multiplicative.ofAdd (fun _ : Fin n => (1 : ZMod 2)) ∈ β.ker := hβ1
      obtain ⟨w, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : β.ker)).mp hK2
      by_cases h1 : f = 1
      · exact Or.inl (by rw [h1, toAdd_one])
      · right
        have e1 : (⟨f, hfK⟩ : β.ker) = w := huniq _ (fun h => h1 (congrArg Subtype.val h))
        have e2 : (⟨_, hπK⟩ : β.ker) = w := huniq _ (fun h => hπne (congrArg Subtype.val h))
        have hfπ : f = Multiplicative.ofAdd (fun _ : Fin n => (1 : ZMod 2)) :=
          congrArg Subtype.val (e1.trans e2.symm)
        rw [hfπ, toAdd_ofAdd]
    · rintro (h | h)
      · rw [show f = 1 from toAdd_eq_zero.mp h, map_one]
      · rw [show f = Multiplicative.ofAdd (fun _ : Fin n => (1 : ZMod 2)) by
          rw [← h, ofAdd_toAdd], hβ1]
  obtain ⟨jf, hjf⟩ : ∃ jf : H → Fin n → Fin n, ∀ (h : H) (i : Fin n),
      (h : G) * pt i * (h : G)⁻¹ = pt (jf h i) :=
    ⟨fun h i => Classical.choose (hinv h h.2 i),
      fun h i => Classical.choose_spec (hinv h h.2 i)⟩
  have hjf_inj : ∀ h : H, Function.Injective (jf h) := by
    intro h i i' hii'
    have e : (h : G) * pt i * (h : G)⁻¹ = (h : G) * pt i' * (h : G)⁻¹ := by
      rw [hjf, hjf, hii']
    exact hpt (mul_left_cancel (mul_right_cancel e))
  obtain ⟨σ, hσ⟩ : ∃ σ : H →* Equiv.Perm (Fin n), ∀ (h : H) (i : Fin n), σ h i = jf h i := by
    refine ⟨{ toFun := fun h => Equiv.ofBijective (jf h)
                (Finite.injective_iff_bijective.mp (hjf_inj h))
              map_one' := ?_
              map_mul' := ?_ }, fun h i => rfl⟩
    · apply Equiv.ext
      intro i
      show jf 1 i = i
      apply hpt
      rw [← hjf]
      simp
    · intro h k
      apply Equiv.ext
      intro i
      show jf (h * k) i = jf h (jf k i)
      apply hpt
      rw [← hjf (h * k) i, ← hjf h (jf k i), ← hjf k i, Subgroup.coe_mul]
      group
  have hσpt : ∀ (h : H) (i : Fin n), (h : G) * pt i * (h : G)⁻¹ = pt (σ h i) :=
    fun h i => by rw [hσ]; exact hjf h i
  have hσinj : Function.Injective σ := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have hfix : ∀ i, (h : G) * pt i * (h : G)⁻¹ = pt i := fun i => by
      rw [hσpt h i, hh, Equiv.Perm.one_apply]
    exact Subtype.ext (hfaith h h.2 hfix)
  have hnorm : ∀ h ∈ H, ∀ x ∈ D, h * x * h⁻¹ ∈ D := by
    intro h hh x hx
    have hle : Subgroup.closure (Set.range pt) ≤ D.comap (MulAut.conj h).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hinv h hh i
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      show h * pt i * h⁻¹ ∈ D
      rw [hj]
      exact hptD j
    rw [hspan] at hle
    have := hle hx
    rw [Subgroup.mem_comap] at this
    exact this
  obtain ⟨cD, hcD⟩ : ∃ cD : H → (D →* D), ∀ (h : H) (x : D),
      ((cD h x : D) : G) = (h : G) * (x : G) * (h : G)⁻¹ :=
    ⟨fun h => ((MulAut.conj (h : G)).toMonoidHom.comp D.subtype).codRestrict D
        (fun x => hnorm h h.2 x x.2), fun h x => rfl⟩
  have hcσ : ∀ (h : H) (i : Fin n), cD h (p i) = p (σ h i) := fun h i => by
    apply Subtype.ext
    rw [hcD, hp, hp]
    exact hσpt h i
  have hconj : ∀ (h : H) (f : Multiplicative (Fin n → ZMod 2)),
      (h : G) * β f * (h : G)⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd ((σ h).symm i)) := by
    intro h f
    have e : cD h (B f) = B (Multiplicative.ofAdd fun i => f.toAdd ((σ h).symm i)) := by
      rw [hB, hB, map_prod]
      simp only [map_pow, hcσ, toAdd_ofAdd]
      have key := Equiv.prod_comp (σ h) (fun j => p j ^ (f.toAdd ((σ h).symm j)).val)
      simp only [Equiv.symm_apply_apply] at key
      exact key
    rw [hβ, hβ, ← hcD, e]
  exact ⟨σ, β, AESplitHyp.of_odd hn hcompl hσinj hVeq hker hconj, hβpt, hσpt⟩

end CFSG.ClassicalInvolution.Q3.Sec13
