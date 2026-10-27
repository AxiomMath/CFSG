module

public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Comb
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.SpecExtract
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.UpperBound
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi24Facts
import all CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 Finset

section

variable {X : Type} [Group X] {p : ℕ} [Fact p.Prime]

theorem actsBy_unique (D : ModuleSpec X p) {x : X} {A A' : Matrix (Fin D.n) (Fin D.n) (ZMod p)}
    (h : ActsBy D x A) (h' : ActsBy D x A') : A = A' := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ext k i
  have := D.elt_injective ((h i).symm.trans (h' i))
  exact congrFun this k

omit [Fact p.Prime] in
theorem commute_span (D : ModuleSpec X p) {x : X} (h : ∀ i, x * D.a i = D.a i * x) :
    ∀ a ∈ D.span, x * a = a * x := by
  intro a ha
  have ha' : a ∈ Subgroup.closure (Set.range D.a) := ha
  clear ha
  induction ha' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact h i
  | one => simp
  | mul y z _ _ ihy ihz => rw [← mul_assoc, ihy, mul_assoc, ihz, mul_assoc]
  | inv y _ ihy => exact (Commute.inv_right (show Commute x y from ihy)).eq

end

theorem pRank_le_of_cover {X : Type} [Group X] [Finite X] {Lm : List (List ℕ)} {n r : ℕ}
    (hcov : SylowModuleCover X 3 n Lm)
    (hcomb : ∀ m : ℕ, m = n → ∀ (S : Finset (MatN m)) (B : Finset (VecN m)) (a j : ℕ),
      S ⊆ o3SetN m Lm → B.card = 3 ^ a → S.card + 1 = 3 ^ j → (∀ g ∈ S, B ⊆ fixSetN m g) →
      a + j ≤ r) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ r := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨D, P, hn, -, -, hPcard, hspan, hnorm, hcen, -, hmem, hcover⟩ := hcov
  refine pRank_le_of_sylow hp P hPcard (k := r) fun E hEP hE => ?_
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => by
    have := hE.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hEp : ∀ x ∈ E, x ^ 3 = 1 := hE.2
  have hex : ∀ x : P, ∃ A ∈ Lm, ActsBy D (x : X) (toMatL 3 D.n A) := fun x => hcover x x.2
  choose A hA hAct using hex
  let A' : E → List ℕ := fun e => A ⟨e, hEP e.2⟩
  have hAct' : ∀ e : E, ActsBy D (e : X) (toMatL 3 D.n (A' e)) := fun e => hAct ⟨e, hEP e.2⟩
  have hA' : ∀ e : E, A' e ∈ Lm := fun e => hA ⟨e, hEP e.2⟩
  have hmulE : ∀ e e' : E, toMatL 3 D.n (A' (e * e')) =
      toMatL 3 D.n (A' e) * toMatL 3 D.n (A' e') := fun e e' =>
    actsBy_unique D (hAct' (e * e')) (by simpa using actsBy_mul D (hAct' e) (hAct' e'))
  have hone : toMatL 3 D.n (A' 1) = 1 :=
    actsBy_unique D (hAct' 1) (by simpa using actsBy_one D)
  let φ : E →* Matrix (Fin D.n) (Fin D.n) (ZMod 3) :=
    { toFun := fun e => toMatL 3 D.n (A' e), map_one' := hone, map_mul' := hmulE }
  have hone_elt : ∀ i, D.elt (fun k => (1 : Matrix (Fin D.n) (Fin D.n) (ZMod 3)) k i) = D.a i :=
    fun i => by
      rw [← D.elt_single i]
      congr 1
      funext k
      simp [Matrix.one_apply, Pi.single_apply]
  have hker_iff : ∀ e : E, toMatL 3 D.n (A' e) = 1 ↔ (e : X) ∈ D.span := by
    intro e
    constructor
    · intro h1
      have hact : ActsBy D (e : X) 1 := h1 ▸ hAct' e
      refine hcen e (hEP e.2) (commute_span D fun i => ?_)
      have := hact i
      rw [hone_elt i] at this
      calc (e : X) * D.a i = ((e : X) * D.a i * (e : X)⁻¹) * e := by group
        _ = D.a i * e := by rw [this]
    · intro he
      refine actsBy_unique D (hAct' e) fun i => ?_
      rw [hone_elt i, D.mul_comm_of_mem he (D.a_mem_span i)]
      group
  let B : Subgroup X := E ⊓ D.span
  have hkerB : φ.toHomUnits.ker = B.subgroupOf E := by
    ext e
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, B]
    rw [Units.ext_iff]
    simp only [MonoidHom.coe_toHomUnits, Units.val_one]
    change toMatL 3 D.n (A' e) = 1 ↔ _
    rw [hker_iff e]
    exact ⟨fun h => ⟨e.2, h⟩, fun h => h.2⟩
  have hcardB : Nat.card φ.toHomUnits.ker = Nat.card B := by
    rw [hkerB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : B ≤ E)).toEquiv
  have hEpg : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hEp g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEpg
  have hBpg : IsPGroup 3 B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hEp g g.2.1)⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hBpg
  have hprod := Subgroup.card_ker_mul_card_range φ.toHomUnits
  rw [hcardB, ha, hk] at hprod
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1
    (Dvd.intro_left _ hprod : Nat.card φ.toHomUnits.range ∣ 3 ^ k)
  let _ : Fintype φ.toHomUnits.range := Fintype.ofFinite _
  let val : φ.toHomUnits.range → Matrix (Fin D.n) (Fin D.n) (ZMod 3) := fun u =>
    ((u : (Matrix (Fin D.n) (Fin D.n) (ZMod 3))ˣ) : Matrix (Fin D.n) (Fin D.n) (ZMod 3))
  let Sfull : Finset (Matrix (Fin D.n) (Fin D.n) (ZMod 3)) :=
    Finset.image val (Finset.univ : Finset φ.toHomUnits.range)
  have hSfullcard : Sfull.card = Nat.card φ.toHomUnits.range := by
    simp only [Sfull]
    rw [Finset.card_image_of_injective _ (fun u v (h : val u = val v) => Subtype.ext (Units.ext h)),
      Finset.card_univ, Nat.card_eq_fintype_card]
  have hmemS : ∀ M, M ∈ Sfull ↔ ∃ e : E, toMatL 3 D.n (A' e) = M := by
    intro M
    simp only [Sfull, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨e, he⟩ := u.2
      exact ⟨e, congrArg Units.val he⟩
    · rintro ⟨e, rfl⟩
      exact ⟨⟨φ.toHomUnits e, e, rfl⟩, rfl⟩
  have h1S : (1 : Matrix (Fin D.n) (Fin D.n) (ZMod 3)) ∈ Sfull := (hmemS _).2 ⟨1, hone⟩
  let S := Sfull.erase 1
  have hS : S.card + 1 = 3 ^ j := by
    rw [Finset.card_erase_add_one h1S, hSfullcard, hj]
  have hSO : S ⊆ o3SetN D.n Lm := by
    intro M hM
    obtain ⟨hne, hMs⟩ := Finset.mem_erase.1 hM
    obtain ⟨e, rfl⟩ := (hmemS M).1 hMs
    refine Finset.mem_filter.2 ⟨List.mem_toFinset.2 (List.mem_map.2 ⟨A' e, hA' e, rfl⟩), hne, ?_⟩
    have he3 : e ^ 3 = 1 := Subtype.ext (hEp e e.2)
    calc toMatL 3 D.n (A' e) ^ 3 = φ (e ^ 3) := (map_pow φ e 3).symm
      _ = 1 := by rw [he3, map_one]
  let Bv : Finset (Fin D.n → ZMod 3) := Finset.univ.filter fun v => D.elt v ∈ E
  have hBv : Bv.card = Nat.card B := by
    have hset : (B : Set X) = ↑(Bv.image D.elt) := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_inf, Finset.coe_image, Set.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and, B, Bv]
      constructor
      · rintro ⟨hxE, hxs⟩
        obtain ⟨c, rfl⟩ := D.exists_elt hxs
        exact ⟨c, hxE, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨hc, D.elt_mem c⟩
    rw [← Finset.card_image_of_injective Bv D.elt_injective]
    have : Nat.card B = Nat.card (B : Set X) := rfl
    rw [this, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hfixed : ∀ M ∈ S, Bv ⊆ fixSetN D.n M := by
    intro M hM v hv
    obtain ⟨hne, hMs⟩ := Finset.mem_erase.1 hM
    obtain ⟨e, rfl⟩ := (hmemS M).1 hMs
    have hvE : D.elt v ∈ E := (Finset.mem_filter.1 hv).2
    have hconj := conj_elt D (hAct' e) v
    have hcomm : (e : X) * D.elt v * (e : X)⁻¹ = D.elt v := by
      rw [hEc e e.2 _ hvE]
      group
    have := D.elt_injective (hconj.symm.trans hcomm)
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩
  have hcomb' := hcomb D.n hn S Bv a j hSO (by rw [hBv, ha]) hS hfixed
  calc Nat.card E = 3 ^ k := hk
    _ = 3 ^ a * 3 ^ j := by rw [← hprod, hj]
    _ = 3 ^ (a + j) := (pow_add 3 a j).symm
    _ ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) hcomb'

theorem pRank_le_nine_of_cover {X : Type} [Group X] [Finite X] {Lm : List (List ℕ)}
    (hcov : SylowModuleCover X 3 7 Lm) (hF : FactsN 7 Lm) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 9 := by
  refine pRank_le_of_cover hcov fun m hm S B a j hSO hB hS hfix => ?_
  subst hm
  obtain ⟨h1, h2, h3a, h3b, h4⟩ := hF
  have hV : Fintype.card (Fin 7 → ZMod 3) = 3 ^ 7 := by simp [ZMod.card]
  exact rank_le_nine hV (fixSetN 7) (o3SetN 7 Lm) h1 h2 h3a h3b h4 S hSO B hB hS hfix

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
