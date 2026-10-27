module

public import Certificates.Data.Kernel.Spor.CommBaseF
public import CFSG.Certificates.Kernel.Spor.CommBaseSound

public section

namespace CFSG.KC.CommBase

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.ComponentClassification.M12Cover

variable {n w nL : ℕ} {L : ℕ → ℕ} {ℓ : ℕ → Equiv.Perm (Fin n)}

theorem sq_fix_of_fix3OK (hL : ∀ z < nL, PRep n w (L z) (ℓ z)) {x : Equiv.Perm (Fin n)}
    (hx : ∀ z < nL, Commute x (ℓ z)) (hx4 : x ^ 4 = 1) {r : Fix3Rec}
    (h : fix3OK n w (mask w) L nL r = true) :
    ∃ hb : r.1 < n, x (x ⟨r.1, hb⟩) = ⟨r.1, hb⟩ := by
  obtain ⟨b, ss, p1, p2⟩ := r
  unfold fix3OK at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hb, -, -, hss, hsb, hall⟩ := h
  rw [Nat.blt_eq] at hb
  rw [allL_iff] at hss
  rw [fixAll, allL_iff] at hsb
  rw [allN_iff] at hall
  replace hss : ∀ s ∈ ss, ∀ z ∈ s, z < nL := fun s hs => lettersOK_iff.1 (hss s hs)
  refine ⟨hb, ?_⟩
  set B : Fin n := ⟨b, hb⟩
  have hSc : ∀ s ∈ ss, Commute x (word ℓ s) := fun s hs => commute_word hx (hss s hs)
  have hS : ∀ s ∈ ss, word ℓ s B = B := fun s hs =>
    Fin.ext (by rw [← wapp_eq hL (hss s hs)]; exact Nat.eq_of_beq_eq_true (hsb s hs))
  have hfix : ∀ y : Fin n, (∀ s ∈ ss, word ℓ s y = y) →
      (y : ℕ) = b ∨ (y : ℕ) = p1 ∨ (y : ℕ) = p2 := by
    intro y hy
    have hf : fixAll w (mask w) L ss y = true := by
      rw [fixAll, allL_iff]
      intro s hs
      rw [Nat.beq_eq, wapp_eq hL (hss s hs), hy s hs]
    have := hall y y.2
    rw [bIf_eqC, if_pos hf, bIf_eqC, bIf_eqC] at this
    split_ifs at this with h1 h2
    · exact Or.inl (Nat.eq_of_beq_eq_true h1)
    · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2))
    · exact Or.inr (Or.inr (Nat.eq_of_beq_eq_true this))
  have hxfix : ∀ y : Fin n, (∀ s ∈ ss, word ℓ s y = y) → ∀ s ∈ ss, word ℓ s (x y) = x y :=
    fun y hy s hs => by rw [← comm_apply (hSc s hs), hy s hs]
  have h1 := hxfix B hS
  have h2 := hxfix _ h1
  have h3 := hxfix _ h2
  have e4 : x (x (x (x B))) = B := by
    have h4 : x * (x * (x * x)) = 1 := by
      rw [← pow_three, ← pow_succ']
      exact hx4
    have := congrArg (fun g : Equiv.Perm (Fin n) => g B) h4
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using this
  by_contra hne
  have d01 : (B : ℕ) ≠ (x B : ℕ) := fun e => hne (by rw [← Fin.ext e, ← Fin.ext e])
  have d12 : (x B : ℕ) ≠ (x (x B) : ℕ) := fun e => d01 (congrArg Fin.val (x.injective (Fin.ext e)))
  have d23 : (x (x B) : ℕ) ≠ (x (x (x B)) : ℕ) := fun e =>
    d12 (congrArg Fin.val (x.injective (Fin.ext e)))
  have d13 : (x B : ℕ) ≠ (x (x (x B)) : ℕ) := fun e =>
    hne (x.injective (Fin.ext e)).symm
  have d03 : (B : ℕ) ≠ (x (x (x B)) : ℕ) := fun e => by
    have e' : x (x (x B)) = B := (Fin.ext e).symm
    have e5 : x (x (x (x B))) = x B := congrArg x e'
    exact d01 (congrArg Fin.val (e4.symm.trans e5))
  have v0 := hfix B hS
  have v1 := hfix _ h1
  have v2 := hfix _ h2
  have v3 := hfix _ h3
  have d02 : (B : ℕ) ≠ (x (x B) : ℕ) := fun e => hne (Fin.ext e).symm
  omega

theorem sq_eq_one_of_commBaseF (hL : ∀ z < nL, PRep n w (L z) (ℓ z)) {x : Equiv.Perm (Fin n)}
    (hx : ∀ z < nL, Commute x (ℓ z)) (hx4 : x ^ 4 = 1) {B : List BaseRec} {B3 : List Fix3Rec}
    {PF ZF DF : ℕ} (h : commBaseF n w (mask w) L nL B B3 PF ZF DF = true) : x ^ 2 = 1 := by
  rw [commBaseF, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, allL_iff, allL_iff] at h
  obtain ⟨hB, hB3, hF⟩ := h
  refine eq_one_of_forestOK hL (fun z hz => (hx z hz).pow_left 2) hF fun r hr hb => ?_
  rw [pow_two, Equiv.Perm.mul_apply]
  rcases List.mem_append.1 hr with hr | hr
  · obtain ⟨hb', e⟩ := sq_fix_of_baseOK hL hx (hB r hr)
    exact e
  · obtain ⟨r3, hr3, rfl⟩ := List.mem_map.1 hr
    obtain ⟨hb', e⟩ := sq_fix_of_fix3OK hL hx hx4 (hB3 r3 hr3)
    exact e

section Groups

variable {G : Type*} [Group G]

theorem isConj_pow_eq_one {x y : G} (h : IsConj x y) {k : ℕ} (hx : x ^ k = 1) : y ^ k = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  rw [conj_pow, hx, mul_one, mul_inv_cancel]

theorem card_isConj_eq_of_isConj {x y : G} (h : IsConj x y) :
    Nat.card {z // IsConj x z} = Nat.card {z // IsConj y z} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩)

theorem commute_pow_of_card_isConj_le [Finite G] {x : G} (g : G) {c e : ℕ}
    (hc : Nat.card {y // IsConj x y} ≤ c) (he : ∀ d, 0 < d → d ≤ c → d ∣ e) :
    Commute (g ^ e) x := by
  let f : Fin (c + 1) → {y // IsConj x y} := fun k =>
    ⟨g ^ (k : ℕ) * x * (g ^ (k : ℕ))⁻¹, isConj_iff.2 ⟨g ^ (k : ℕ), rfl⟩⟩
  have hnot : ¬ Function.Injective f := fun hf => by
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  have key : ∀ i j : Fin (c + 1), (i : ℕ) < j → f i = f j → Commute (g ^ e) x := by
    intro i j hij hfij
    have e1 : g ^ (i : ℕ) * x * (g ^ (i : ℕ))⁻¹ = g ^ (j : ℕ) * x * (g ^ (j : ℕ))⁻¹ :=
      congrArg Subtype.val hfij
    have hjc := j.2
    obtain ⟨d, hd⟩ : ∃ d, (j : ℕ) = i + d := ⟨j - i, by omega⟩
    rw [hd, pow_add] at e1
    have e2 := congrArg (fun y => (g ^ (i : ℕ))⁻¹ * y * g ^ (i : ℕ)) e1
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at e2
    have hcd : Commute (g ^ d) x :=
      calc g ^ d * x = g ^ d * (x * (g ^ d)⁻¹) * g ^ d := by group
        _ = x * g ^ d := by rw [← e2]
    obtain ⟨q, rfl⟩ := he d (by omega) (by omega)
    rw [pow_mul]
    exact hcd.pow_left q
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 hnot
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · exact key i j hlt hij
  · exact key j i hlt hij.symm

theorem exists_isConj_commute_of_isPGroup [Finite G] (x : G) {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA : IsPGroup p A) (hc : ¬ p ∣ Nat.card {y // IsConj x y}) :
    ∃ y, IsConj x y ∧ ∀ a ∈ A, Commute a y := by
  let X := {y // IsConj x y}
  let _ : MulAction A X :=
    { smul := fun a y => ⟨(a : G) * y * (a : G)⁻¹, y.2.trans (isConj_iff.2 ⟨a, rfl⟩)⟩
      one_smul := fun y => Subtype.ext (by
        change ((1 : A) : G) * y * ((1 : A) : G)⁻¹ = y
        simp)
      mul_smul := fun s t y => Subtype.ext (by
        change ((s * t : A) : G) * y * ((s * t : A) : G)⁻¹ =
          (s : G) * ((t : G) * y * (t : G)⁻¹) * (s : G)⁻¹
        simp [mul_assoc]) }
  obtain ⟨y, hy⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card X hc
  refine ⟨y, y.2, fun a ha => ?_⟩
  have e : (a : G) * y * a⁻¹ = y := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hy ⟨a, ha⟩)
  exact mul_inv_eq_iff_eq_mul.1 e

theorem isPGroup_closure_of_commute {S : Set G} {p k : ℕ} (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (hp : ∀ a ∈ S, a ^ p ^ k = 1) : IsPGroup p (Subgroup.closure S) := by
  have hC : Subgroup.closure S ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le _).2 fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (hS b hb a ha).eq
  have hcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, Commute x y := by
    intro x hx y hy
    have hxS := Subgroup.mem_centralizer_iff.1 (hC hx)
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {x} :=
      (Subgroup.closure_le _).2 fun s hs => Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact (hxS s hs).symm
    exact Subgroup.mem_centralizer_iff.1 (hle hy) x (Set.mem_singleton x)
  have hpow : ∀ x ∈ Subgroup.closure S, x ^ p ^ k = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem a ha => exact hp a ha
    | one => exact one_pow _
    | mul a b ha hb iha ihb => rw [(hcomm a ha b hb).mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  intro g
  exact ⟨k, Subtype.ext (by simpa using hpow g g.2)⟩

theorem fourClassesLarge_of_cases [Finite G] {SA SB : Set G}
    (hSA : ∀ a ∈ SA, ∀ b ∈ SA, Commute a b) (hSA3 : ∀ a ∈ SA, a ^ 3 = 1)
    (hSB : ∀ a ∈ SB, ∀ b ∈ SB, Commute a b) (hSB2 : ∀ a ∈ SB, a ^ 16 = 1)
    (hA : ∀ y : G, y ^ 4 = 1 → (∀ s ∈ SA, Commute s y) → (∀ g : G, Commute (g ^ 12) y) →
      y ^ 2 = 1)
    (hB : ∀ y : G, y ^ 4 = 1 → (∀ s ∈ SB, Commute s y) → (∀ g : G, Commute (g ^ 6) y) →
      y ^ 2 = 1) :
    FourClassesLarge G := by
  intro x hx4 hx2
  by_contra hlt
  have hle : Nat.card {y // IsConj x y} ≤ 4 := by omega
  have : Nonempty {y // IsConj x y} := ⟨⟨x, IsConj.refl x⟩⟩
  have hpos : 0 < Nat.card {y // IsConj x y} := Nat.card_pos
  by_cases h3 : 3 ∣ Nat.card {y // IsConj x y}
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hP := isPGroup_closure_of_commute (p := 2) (k := 4) hSB fun a ha => by
      simpa using hSB2 a ha
    obtain ⟨y, hxy, hy⟩ := exists_isConj_commute_of_isPGroup x hP (by omega)
    have hcy : Nat.card {z // IsConj y z} ≤ 3 := by
      rw [← card_isConj_eq_of_isConj hxy]
      omega
    refine hx2 (isConj_pow_eq_one hxy.symm (hB y (isConj_pow_eq_one hxy hx4)
      (fun s hs => hy s (Subgroup.subset_closure hs)) fun g => ?_))
    refine commute_pow_of_card_isConj_le g hcy fun d hd hd3 => ?_
    interval_cases d <;> norm_num
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hP := isPGroup_closure_of_commute (p := 3) (k := 1) hSA fun a ha => by
      simpa using hSA3 a ha
    obtain ⟨y, hxy, hy⟩ := exists_isConj_commute_of_isPGroup x hP h3
    have hcy : Nat.card {z // IsConj y z} ≤ 4 := by
      rw [← card_isConj_eq_of_isConj hxy]
      exact hle
    refine hx2 (isConj_pow_eq_one hxy.symm (hA y (isConj_pow_eq_one hxy hx4)
      (fun s hs => hy s (Subgroup.subset_closure hs)) fun g => ?_))
    refine commute_pow_of_card_isConj_le g hcy fun d hd hd4 => ?_
    interval_cases d <;> norm_num

end Groups

theorem commute_val {M : Type*} [Group M] {K : Subgroup M} {a b : K} (h : Commute a b) :
    Commute (a : M) (b : M) :=
  h.map K.subtype

@[expose] def LetterIn (K : Subgroup (Equiv.Perm (Fin n))) (S : Set K) (e : ℕ)
    (g : Equiv.Perm (Fin n)) : Prop :=
  (∃ s ∈ S, (s : Equiv.Perm (Fin n)) = g) ∨ (∃ k : K, ((k ^ e : K) : Equiv.Perm (Fin n)) = g) ∨
    ∀ k : K, Commute (k : Equiv.Perm (Fin n)) g

theorem sq_eq_one_of_letters (K : Subgroup (Equiv.Perm (Fin n))) {S : Set K} {e : ℕ}
    (hL : ∀ z < nL, PRep n w (L z) (ℓ z)) (hK : ∀ z < nL, LetterIn K S e (ℓ z))
    {B : List BaseRec} {B3 : List Fix3Rec} {PF ZF DF : ℕ}
    (h : commBaseF n w (mask w) L nL B B3 PF ZF DF = true) (y : K) (hy4 : y ^ 4 = 1)
    (hys : ∀ s ∈ S, Commute s y) (hyg : ∀ g : K, Commute (g ^ e) y) : y ^ 2 = 1 := by
  have hx : ∀ z < nL, Commute (y : Equiv.Perm (Fin n)) (ℓ z) := by
    intro z hz
    rcases hK z hz with ⟨s, hs, hse⟩ | ⟨g, hge⟩ | hc
    · rw [← hse]
      exact (commute_val (hys s hs)).symm
    · rw [← hge]
      exact (commute_val (hyg g)).symm
    · exact hc y
  have h4 : (y : Equiv.Perm (Fin n)) ^ 4 = 1 := by rw [← Subgroup.coe_pow, hy4, Subgroup.coe_one]
  have h2 := sq_eq_one_of_commBaseF hL hx h4 h
  exact Subtype.ext (by rw [Subgroup.coe_pow, h2, Subgroup.coe_one])

theorem fourClassesLarge_of_commBaseF {nLA nLB : ℕ} {LA LB : ℕ → ℕ} {ℓA ℓB : ℕ → Equiv.Perm (Fin n)}
    (K : Subgroup (Equiv.Perm (Fin n))) {SA SB : Set K}
    (hSA : ∀ a ∈ SA, ∀ b ∈ SA, Commute a b) (hSA3 : ∀ a ∈ SA, a ^ 3 = 1)
    (hSB : ∀ a ∈ SB, ∀ b ∈ SB, Commute a b) (hSB2 : ∀ a ∈ SB, a ^ 16 = 1)
    (hLA : ∀ z < nLA, PRep n w (LA z) (ℓA z)) (hKA : ∀ z < nLA, LetterIn K SA 12 (ℓA z))
    (hLB : ∀ z < nLB, PRep n w (LB z) (ℓB z)) (hKB : ∀ z < nLB, LetterIn K SB 6 (ℓB z))
    {BA BB : List BaseRec} {B3A B3B : List Fix3Rec} {PFA ZFA DFA PFB ZFB DFB : ℕ}
    (hA : commBaseF n w (mask w) LA nLA BA B3A PFA ZFA DFA = true)
    (hB : commBaseF n w (mask w) LB nLB BB B3B PFB ZFB DFB = true) : FourClassesLarge K :=
  fourClassesLarge_of_cases hSA hSA3 hSB hSB2 (sq_eq_one_of_letters K hLA hKA hA)
    (sq_eq_one_of_letters K hLB hKB hB)

end CFSG.KC.CommBase

end
