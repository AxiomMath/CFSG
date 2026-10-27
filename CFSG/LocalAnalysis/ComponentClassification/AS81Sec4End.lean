module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step17

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem index_ne_two_of_commutator_eq_top {G : Type} [Group G] (h : commutator G = ⊤)
    {N : Subgroup G} [N.Normal] : N.index ≠ 2 := by
  intro h2
  obtain ⟨a, haN, hb⟩ := (Subgroup.index_eq_two_iff_exists_notMem_and).mp h2
  have hsup : N ⊔ zpowers a = ⊤ := by
    rw [eq_top_iff]
    intro b _
    rcases hb b with h1 | h1
    · have e : b = (b * a) * a⁻¹ := by group
      rw [e]
      exact mul_mem (mem_sup_left h1) (mem_sup_right (inv_mem (mem_zpowers a)))
    · exact mem_sup_left h1
  have hle := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup
    (inferInstance : IsMulCommutative (zpowers a))
  rw [h] at hle
  have hNtop : N = ⊤ := eq_top_iff.mpr hle
  rw [hNtop, index_top] at h2
  exact absurd h2 (by norm_num)

theorem le_commutator_of_perfect {G : Type} [Group G] {A : Subgroup G}
    (hA : commutator ↥A = ⊤) : A ≤ commutator G := by
  have h1 : (commutator ↥A).map A.subtype = A := by
    rw [hA, ← MonoidHom.range_eq_map, range_subtype]
  rw [← h1, commutator_def, map_commutator, commutator_def]
  exact commutator_mono le_top le_top

theorem commutator_eq_top_of_normalClosure {G : Type} [Group G] {A : Subgroup G}
    (hA : commutator ↥A = ⊤) (htop : normalClosure (A : Set G) = ⊤) : commutator G = ⊤ := by
  rw [eq_top_iff, ← htop]
  exact normalClosure_le_normal (le_commutator_of_perfect hA)

theorem nonempty_mulEquiv_klein {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (hR : IsElemAbelian 2 R) (h4 : Nat.card R = 4) :
    Nonempty (R ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  have hcomm : ∀ a b : R, a * b = b * a := fun a b => hR.1.is_comm.comm a b
  have hsq : ∀ a : R, a * a = 1 := fun a => by
    have := hR.2 a a.2
    exact Subtype.ext (by simpa [pow_two] using this)
  have hne : ∃ a : R, a ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton R := ⟨fun x y => (h x).trans (h y).symm⟩
    have h1 : Nat.card R = 1 := Nat.card_of_subsingleton (1 : R)
    omega
  obtain ⟨a, ha⟩ := hne
  have hne' : ∃ b : R, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hsub : (Set.univ : Set R) ⊆ {1, a} := fun x _ => by
      by_cases hx : x = 1
      · exact Or.inl hx
      · exact Or.inr (h x hx)
    have : Nat.card R ≤ 2 := by
      rw [← Set.ncard_univ]
      calc (Set.univ : Set R).ncard ≤ ({1, a} : Set R).ncard := Set.ncard_le_ncard hsub
        _ ≤ ({a} : Set R).ncard + 1 := Set.ncard_insert_le 1 {a}
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  obtain ⟨b, hb1, hba⟩ := hne'
  let f : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* R :=
    { toFun := fun p => a ^ (Multiplicative.toAdd p.1).val * b ^ (Multiplicative.toAdd p.2).val
      map_one' := by simp
      map_mul' := by
        have hpow : ∀ (c : R) (i j : ZMod 2), c ^ (i + j).val = c ^ i.val * c ^ j.val := by
          intro c i j
          have hc2 : c ^ 2 = 1 := by rw [pow_two, hsq]
          rw [← pow_add, ← pow_mod_orderOf, ← pow_mod_orderOf (n := i.val + j.val)]
          congr 1
          have hdvd : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
          rw [ZMod.val_add]
          exact (Nat.mod_mod_of_dvd _ hdvd)
        intro p q
        simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul]
        rw [hpow a, hpow b]
        calc a ^ (Multiplicative.toAdd p.1).val * a ^ (Multiplicative.toAdd q.1).val *
              (b ^ (Multiplicative.toAdd p.2).val * b ^ (Multiplicative.toAdd q.2).val)
            = a ^ (Multiplicative.toAdd p.1).val * (a ^ (Multiplicative.toAdd q.1).val *
              b ^ (Multiplicative.toAdd p.2).val) * b ^ (Multiplicative.toAdd q.2).val := by group
          _ = a ^ (Multiplicative.toAdd p.1).val * (b ^ (Multiplicative.toAdd p.2).val *
              a ^ (Multiplicative.toAdd q.1).val) * b ^ (Multiplicative.toAdd q.2).val := by
              rw [hcomm (a ^ _) (b ^ _)]
          _ = _ := by group }
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    rw [MonoidHom.mem_ker] at hp
    rw [mem_bot]
    obtain ⟨p1, p2⟩ := p
    have hval : ∀ i : ZMod 2, (i.val = 0 ∧ i = 0) ∨ (i.val = 1 ∧ i = 1) := by decide
    have key : ∀ i j : ZMod 2, a ^ i.val * b ^ j.val = 1 → i = 0 ∧ j = 0 := by
      intro i j hij
      rcases hval i with ⟨hi, hi'⟩ | ⟨hi, hi'⟩ <;> rcases hval j with ⟨hj, hj'⟩ | ⟨hj, hj'⟩ <;>
        rw [hi, hj] at hij <;> simp only [pow_zero, pow_one, one_mul, mul_one] at hij
      · exact ⟨hi', hj'⟩
      · exact absurd hij hb1
      · exact absurd hij ha
      · exfalso
        apply hba
        calc b = a * (a * b) := by rw [← mul_assoc, hsq, one_mul]
          _ = a := by rw [hij, mul_one]
    obtain ⟨h1, h2⟩ := key _ _ hp
    ext
    · exact congrArg Multiplicative.ofAdd h1
    · exact congrArg Multiplicative.ofAdd h2
  have hcard : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = Nat.card R := by
    rw [h4, Nat.card_prod]
    simp [Nat.card_eq_fintype_card]
  have hbij : Function.Bijective f :=
    Function.Injective.bijective_of_nat_card_le hinj (le_of_eq hcard.symm)
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

theorem Sec4Setting.rankTwoX_eq_top {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G}
    {E F : Subgroup G} (h : Sec4Setting G A R g E F) (hRA : R ≤ A) : rankTwoX A = ⊤ := by
  have h1 : R ≤ rankTwoX A := hRA.trans le_normalClosure
  rw [← h.top]
  exact (sup_eq_left.mpr h1).symm

theorem center_mulEquiv_klein
    (h17 : Step17) (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34)
    {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) {G : Type} [Group G] [Finite G]
    {A R : Subgroup G} {g : G} {E F : Subgroup G} (hset : Sec4Setting G A R g E F) (hRA : R ≤ A)
    (hHe : IsSporadic (rankTwoX A) .He) :
    Nonempty (center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  have hF := hset.frame
  have hXtop := hset.rankTwoX_eq_top hRA
  have hcardG : Nat.card G = 4030387200 := by
    obtain ⟨e⟩ := hHe
    have h1 : Nat.card (Carrier .He) = 4030387200 := CFSG.Sporadic.He.card_He
    rw [← h1, ← Nat.card_congr e.toEquiv, hXtop, card_top]
  have hEA : E ≤ A := by
    have := hF.E_le
    rwa [sup_eq_left.mpr hRA] at this
  set Zc : Subgroup G := (center ↥A).map A.subtype with hZc
  have hZcA : ∀ x ∈ Zc, ∀ a ∈ A, a * x = x * a := by
    rintro _ ⟨y, hy, rfl⟩ a ha
    have := (mem_center_iff.mp hy) ⟨a, ha⟩
    exact congrArg Subtype.val this
  have hRZ : R ≤ Zc := by
    intro r hr
    refine ⟨⟨r, hRA hr⟩, mem_center_iff.mpr fun a => Subtype.ext ?_, rfl⟩
    exact (mem_centralizer_iff.mp (hF.sylowR.le hr)) a a.2
  have hZcC : Zc ≤ centralizer (A : Set G) := fun x hx =>
    mem_centralizer_iff.mpr fun a ha => hZcA x hx a ha
  have hodd : ∀ x ∈ Zc, ∀ q : ℕ, q.Prime → q ≠ 2 → orderOf x = q → False := by
    intro x hx q hq hq2 hxq
    have hOodd : Odd (Nat.card (zpowers x)) := by
      rw [Nat.card_zpowers, hxq]
      exact hq.odd_of_ne_two hq2
    have hEO : E ≤ normalizer ((zpowers x : Subgroup G) : Set G) := by
      refine le_trans ?_ (centralizer_le_normalizer _)
      rw [le_centralizer_iff, zpowers_le]
      exact mem_centralizer_iff.mpr fun e he => hZcA x hx e (hEA he)
    obtain ⟨X, hOX, hX⟩ := Finite.exists_le_maximal
      (p := fun Y : Subgroup G => Odd (Nat.card Y) ∧ E ≤ normalizer (Y : Set G)) ⟨hOodd, hEO⟩
    have hXne : X ≠ ⊥ := by
      intro h
      have hx1 : x = 1 := by
        have := hOX (mem_zpowers x)
        rwa [h, mem_bot] at this
      rw [hx1, orderOf_one] at hxq
      exact hq.one_lt.ne hxq
    obtain ⟨-, hNtop, -, -⟩ := step17a_of_frame h4 h34 hE16 hF hset.type X hX hXne
    obtain ⟨-, -, hcon⟩ := h17 G A R g E F hF hset.type hset.below X hX hXne
    have hlt : Nat.card (normalizer (X : Set G)) < Nat.card G := by
      rw [← card_top (G := G)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hNtop)
    rcases hcon with ⟨⟨e⟩, -⟩ | ⟨-, ⟨e⟩⟩
    · have h1 : Nat.card (Carrier .Suz) = 448345497600 := CFSG.Sporadic.Suz.card_Suz
      have h2 := Nat.card_congr e.toEquiv
      rw [h1] at h2
      have h3 := Nat.le_of_dvd Nat.card_pos
        (card_quotient_dvd_card (center ↥(rankTwoX (A.subgroupOf (normalizer (X : Set G))))))
      have h4 := Subgroup.card_le_card_group (rankTwoX (A.subgroupOf (normalizer (X : Set G))))
      omega
    · have h1 : Nat.card (Carrier .He) = 4030387200 := CFSG.Sporadic.He.card_He
      have h2 := Nat.card_congr e.toEquiv
      rw [h1] at h2
      have h4 := Subgroup.card_le_card_group (rankTwoX (A.subgroupOf (normalizer (X : Set G))))
      omega
  have hZc2 : IsPGroup 2 Zc := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hne : orderOf x ≠ 0 := (orderOf_pos x).ne'
    rw [← Subgroup.orderOf_coe] at hne ⊢
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hne fun {d} hd hdvd => ?_⟩
    by_contra hd2
    exact hodd _ (Zc.pow_mem x.2 (orderOf (x : G) / d)) d hd hd2
      (orderOf_pow_orderOf_div hne hdvd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZR : Zc = R := hF.sylowR.eq_of_le hRZ hZcC hZc2
  obtain ⟨e⟩ := nonempty_mulEquiv_klein hF.elemR hF.cardR
  have e1 : center ↥A ≃* Zc := Subgroup.equivMapOfInjective _ _ A.subtype_injective
  exact ⟨e1.trans ((MulEquiv.subgroupCongr hZR).trans e)⟩

theorem sec4HeXR_of_steps
    (h16 : Step16) (h17 : Step17) (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34)
    {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h45 : Step45) (h49 : Step49)
    (h410 : Step410) : Sec4HeXR := by
  intro G _ _ A R g E F hF hL he hb hXR
  have hset : Sec4Setting G A R g E F := ⟨hF, hL, he, hb, hXR⟩
  have hRA : R ≤ A := (h16 G A R g E F hF he).1
  have hXtop := hset.rankTwoX_eq_top hRA
  have hperf : commutator G = ⊤ := commutator_eq_top_of_normalClosure hF.quasisimple.1 hXtop
  obtain ⟨S₁, hS₁⟩ := exists_isSylowOf 2 (normalizer ((E ⊔ F : Subgroup G) : Set G))
  obtain ⟨-, Q, z, hQ⟩ := h45 G A R g E F hset S₁ hS₁
  have hHe : IsSporadic (rankTwoX A) .He := by
    rcases (h49 G A R g E F S₁ Q z hQ).2 with hP | hHe
    · obtain ⟨N, hN, h2⟩ := h410 G A R g E F S₁ Q z hQ hP
      exact absurd h2 (@index_ne_two_of_commutator_eq_top _ _ hperf N hN)
    · exact hHe
  exact ⟨center_mulEquiv_klein h17 h4 h34 hE16 hset hRA hHe, hHe⟩

end CFSG.ComponentClassification.AS81
