module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Shape
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open Subgroup

private lemma nonab_card_map_mul_card_inf_ker {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (K : Subgroup G) :
    Nat.card (K.map f) * Nat.card (f.ker ⊓ K : Subgroup G) = Nat.card K := by
  rw [← Subgroup.relIndex_ker]
  exact Subgroup.relIndex_mul_card _ _

private lemma nonab_card_eq_snd_mul_inl {A B : Type*} [Group A] [Group B]
    (S : Subgroup (A × B)) :
    Nat.card S = Nat.card (S.map (MonoidHom.snd A B)) *
      Nat.card (S.comap (MonoidHom.inl A B)) := by
  have h := nonab_card_map_mul_card_inf_ker (MonoidHom.snd A B) S
  have h2 : (MonoidHom.snd A B).ker ⊓ S =
      (S.comap (MonoidHom.inl A B)).map (MonoidHom.inl A B) := by
    ext ⟨a, b⟩
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_map, Subgroup.mem_comap,
      MonoidHom.coe_snd, MonoidHom.inl_apply, Function.comp_apply]
    constructor
    · rintro ⟨hb, hS⟩
      subst hb
      exact ⟨a, hS, rfl⟩
    · rintro ⟨a', ha', hEq⟩
      have h1 : a' = a := congrArg Prod.fst hEq
      have h2 : (1 : B) = b := congrArg Prod.snd hEq
      subst h1 h2
      exact ⟨rfl, ha'⟩
  have hinj : Function.Injective (MonoidHom.inl A B) := fun x y hxy => (Prod.ext_iff.1 hxy).1
  rw [h2, Subgroup.card_map_of_injective hinj] at h
  exact h.symm

private lemma nonab_card_eq_fst_mul_inr {A B : Type*} [Group A] [Group B]
    (S : Subgroup (A × B)) :
    Nat.card S = Nat.card (S.map (MonoidHom.fst A B)) *
      Nat.card (S.comap (MonoidHom.inr A B)) := by
  have h := nonab_card_map_mul_card_inf_ker (MonoidHom.fst A B) S
  have h2 : (MonoidHom.fst A B).ker ⊓ S =
      (S.comap (MonoidHom.inr A B)).map (MonoidHom.inr A B) := by
    ext ⟨a, b⟩
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_map, Subgroup.mem_comap,
      MonoidHom.coe_fst, MonoidHom.inr_apply, Function.comp_apply]
    constructor
    · rintro ⟨ha, hS⟩
      subst ha
      exact ⟨b, hS, rfl⟩
    · rintro ⟨b', hb', hEq⟩
      have h1 : (1 : A) = a := congrArg Prod.fst hEq
      have h2 : b' = b := congrArg Prod.snd hEq
      subst h1 h2
      exact ⟨rfl, hb'⟩
  have hinj : Function.Injective (MonoidHom.inr A B) := fun x y hxy => (Prod.ext_iff.1 hxy).2
  rw [h2, Subgroup.card_map_of_injective hinj] at h
  exact h.symm

private lemma nonab_card_le_mul_of_pow_mem {p : ℕ} (hp : 0 < p) {A : Type*} [Group A] [Finite A]
    [IsCyclic A] (R K : Subgroup A) (h : ∀ a ∈ R, a ^ p ∈ K) :
    Nat.card R ≤ p * Nat.card K := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := R)
  have hord : orderOf g = Nat.card R := orderOf_eq_card_of_forall_mem_zpowers hg
  have hx : (g : A) ^ p ∈ K := h _ g.2
  have h1 : Nat.card (Subgroup.zpowers ((g : A) ^ p)) ≤ Nat.card K :=
    Subgroup.card_le_of_le (Subgroup.zpowers_le.2 hx)
  rw [Nat.card_zpowers, orderOf_pow' _ hp.ne', Subgroup.orderOf_coe] at h1
  have hd : Nat.gcd (orderOf g) p ∣ orderOf g := Nat.gcd_dvd_left _ _
  have hle : Nat.gcd (orderOf g) p ≤ p := Nat.gcd_le_right _ hp
  calc Nat.card R = orderOf g := hord.symm
    _ = orderOf g / Nat.gcd (orderOf g) p * Nat.gcd (orderOf g) p :=
        (Nat.div_mul_cancel hd).symm
    _ ≤ Nat.card K * p := Nat.mul_le_mul h1 hle
    _ = p * Nat.card K := Nat.mul_comm _ _

private lemma nonab_isMulCommutative_of_card_dvd_lt {p : ℕ} (hp : p.Prime) {G : Type*} [Group G]
    (H : Subgroup G) (hdvd : Nat.card H ∣ p ^ 3) (hne : Nat.card H ≠ p ^ 3) :
    IsMulCommutative H := by
  haveI := Fact.mk hp
  obtain ⟨j, hj, hcard⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hj3 : j ≠ 3 := fun h => hne (h ▸ hcard)
  have hj' : j ≤ 2 := by omega
  interval_cases j
  · have : Nat.card H = 1 := by simpa using hcard
    haveI : Subsingleton H := (Nat.card_eq_one_iff_unique.1 this).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : Nat.card H = p := by simpa using hcard
    haveI : IsCyclic H := isCyclic_of_prime_card this
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (by simpa using hcard)

private lemma nonab_pow_eq_one_of_card_eq {G : Type*} [Group G] {H : Subgroup G} {n : ℕ}
    [Finite H] (hH : Nat.card H = n) : ∀ a ∈ H, a ^ n = 1 := by
  intro a ha
  have := pow_card_eq_one' (G := H) (x := ⟨a, ha⟩)
  rw [hH] at this
  exact congrArg Subtype.val this

private lemma nonab_card_subgroup_prod {A B : Type*} [Group A] [Group B] (H : Subgroup A)
    (K : Subgroup B) : Nat.card (H.prod K) = Nat.card H * Nat.card K := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (Subgroup.prodEquiv H K).toEquiv

private theorem nonab_card_eq_of_prod {p : ℕ} (hp : p.Prime) {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] [IsCyclic A] (hAp : IsPGroup p A) (hB : Nat.card B = p ^ 3)
    (hBe : ∀ b : B, b ^ p = 1) {S : Subgroup (A × B)} (hSn : ¬ IsMulCommutative S)
    (hS : ∀ E : Subgroup (A × B), E ≤ S → CFSG.Open.IsElemAbelian p E → Nat.card E ≠ p ^ 3) :
    Nat.card S = p ^ 3 := by
  haveI := Fact.mk hp
  have hT : Nat.card (S.map (MonoidHom.snd A B)) = p ^ 3 := by
    by_contra hne
    apply hSn
    have hcomm : IsMulCommutative (S.map (MonoidHom.snd A B)) :=
      nonab_isMulCommutative_of_card_dvd_lt hp _
        (by rw [← hB]; exact Subgroup.card_subgroup_dvd_card _) hne
    refine isMulCommutative_iff.2 ?_
    rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩
    have hb1 : b ∈ S.map (MonoidHom.snd A B) := Subgroup.mem_map.2 ⟨(a, b), hab, rfl⟩
    have hb2 : b' ∈ S.map (MonoidHom.snd A B) := Subgroup.mem_map.2 ⟨(a', b'), hab', rfl⟩
    refine Subtype.ext (Prod.ext (mul_comm' a a') ?_)
    show b * b' = b' * b
    exact setLike_mul_comm hb1 hb2
  have h1 := nonab_card_eq_snd_mul_inl S
  have h2 := nonab_card_eq_fst_mul_inr S
  rw [hT] at h1
  have hR : Nat.card (S.map (MonoidHom.fst A B)) ≤
      p * Nat.card (S.comap (MonoidHom.inl A B)) := by
    refine nonab_card_le_mul_of_pow_mem hp.pos _ _ ?_
    intro a ha
    obtain ⟨⟨a', b'⟩, hab', rfl⟩ := Subgroup.mem_map.1 ha
    have hmem : (a', b') ^ p ∈ S := S.pow_mem hab' p
    simp only [Subgroup.mem_comap, MonoidHom.inl_apply, MonoidHom.coe_fst, Function.comp_apply]
    simpa [Prod.pow_mk, hBe b'] using hmem
  by_contra hne
  have hKA : Nat.card (S.comap (MonoidHom.inl A B)) ≠ 1 := by
    intro h
    apply hne
    rw [h1, h, mul_one]
  set KA := S.comap (MonoidHom.inl A B) with hKAdef
  set KB := S.comap (MonoidHom.inr A B) with hKBdef
  have hpKA : p ∣ Nat.card KA := ((hAp.to_subgroup KA).card_eq_or_dvd).resolve_left hKA
  obtain ⟨A', hA'⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := KA) p (n := 1) (by simpa using hpKA)
  let A'' : Subgroup A := A'.map KA.subtype
  have hA''card : Nat.card A'' = p := by
    rw [Subgroup.card_map_of_injective KA.subtype_injective, hA']; simp
  have hA''mem : ∀ a ∈ A'', (a, (1 : B)) ∈ S := by
    intro a ha
    obtain ⟨c, _, rfl⟩ := Subgroup.mem_map.1 ha
    exact c.2
  have hKBge : p ^ 2 ≤ Nat.card KB := by
    have hpos : 0 < Nat.card KA := Nat.card_pos
    have h3 : p ^ 3 * Nat.card KA ≤ (p * Nat.card KB) * Nat.card KA := by
      calc p ^ 3 * Nat.card KA = Nat.card S := h1.symm
        _ = Nat.card (S.map (MonoidHom.fst A B)) * Nat.card KB := h2
        _ ≤ (p * Nat.card KA) * Nat.card KB := Nat.mul_le_mul_right _ hR
        _ = (p * Nat.card KB) * Nat.card KA := by ring
    have h4 : p ^ 3 ≤ p * Nat.card KB := Nat.le_of_mul_le_mul_right h3 hpos
    have h5 : p * p ^ 2 ≤ p * Nat.card KB := by rwa [← pow_succ']
    exact Nat.le_of_mul_le_mul_left h5 hp.pos
  have hKBdvd : p ^ 2 ∣ Nat.card KB := by
    have hdvd : Nat.card KB ∣ p ^ 3 := by
      rw [← hB]; exact Subgroup.card_subgroup_dvd_card KB
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hk2 : 2 ≤ k := by
      have : p ^ 2 ≤ p ^ k := hk' ▸ hKBge
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this
    rw [hk']
    exact pow_dvd_pow p hk2
  obtain ⟨B', hB'⟩ := Sylow.exists_subgroup_card_pow_prime (G := KB) p (n := 2) hKBdvd
  let B'' : Subgroup B := B'.map KB.subtype
  have hB''card : Nat.card B'' = p ^ 2 := by
    rw [Subgroup.card_map_of_injective KB.subtype_injective, hB']
  have hB''mem : ∀ b ∈ B'', ((1 : A), b) ∈ S := by
    intro b hb
    obtain ⟨c, _, rfl⟩ := Subgroup.mem_map.1 hb
    exact c.2
  let E : Subgroup (A × B) := A''.prod B''
  have hES : E ≤ S := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have := S.mul_mem (hA''mem a ha) (hB''mem b hb)
    simpa using this
  have hEcard : Nat.card E = p ^ 3 := by
    rw [nonab_card_subgroup_prod, hA''card, hB''card]; ring
  haveI : IsMulCommutative B'' := IsPGroup.isMulCommutative_of_card_eq_prime_sq hB''card
  have hEab : CFSG.Open.IsElemAbelian p E := by
    refine ⟨?_, ?_⟩
    · refine isMulCommutative_iff.2 ?_
      rintro ⟨⟨a, b⟩, ha, hb⟩ ⟨⟨a', b'⟩, ha', hb'⟩
      have hb1 : b ∈ B'' := hb
      have hb2 : b' ∈ B'' := hb'
      refine Subtype.ext (Prod.ext (mul_comm' a a') ?_)
      show b * b' = b' * b
      exact setLike_mul_comm hb1 hb2
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      exact Prod.ext (nonab_pow_eq_one_of_card_eq hA''card a ha) (hBe b)
  exact hS E hES hEab hEcard

private lemma nonab_le_pRank {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    {S E : Subgroup X} {k : ℕ} (hES : E ≤ S) (hE : CFSG.Open.IsElemAbelian p E)
    (hc : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p S := by
  unfold CFSG.Open.pRank
  apply le_csSup
  · refine ⟨Nat.card X, ?_⟩
    rintro j ⟨F, -, -, hF⟩
    have h1 : p ^ j ≤ Nat.card X := hF ▸ Subgroup.card_le_card_group F
    have h2 : j < p ^ j := Nat.lt_pow_self hp.one_lt
    omega
  · exact ⟨E, hES, hE, hc⟩

theorem card_eq_of_nonabelian_pRank_le_two {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    {Q Q₀ Q₁ : Subgroup X} (h : HeisShape p Q Q₀ Q₁) {S : Subgroup X} (hSQ : S ≤ Q)
    (hSn : ¬ IsMulCommutative S) (hS : CFSG.Open.pRank p S ≤ 2) : Nat.card S = p ^ 3 := by
  haveI := Fact.mk hp
  haveI := h.cyc
  let φ : ↥Q₀ × ↥Q₁ →* X :=
    MonoidHom.noncommCoprod Q₀.subtype Q₁.subtype (fun a b => h.comm a.1 a.2 b.1 b.2)
  have hφ : ∀ x : ↥Q₀ × ↥Q₁, φ x = (x.1 : X) * (x.2 : X) := fun x => rfl
  have hinj : Function.Injective φ := by
    intro x y hxy
    have := h.eq_of_mul_eq x.1.2 y.1.2 x.2.2 y.2.2 (by rw [← hφ, ← hφ]; exact hxy)
    exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2)
  have hsurj : S ≤ φ.range := by
    intro s hs
    obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul (hSQ hs)
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  let S' : Subgroup (↥Q₀ × ↥Q₁) := S.comap φ
  have hmap : S'.map φ = S := Subgroup.map_comap_eq_self hsurj
  have hcard : Nat.card S' = Nat.card S := by
    have := Subgroup.card_map_of_injective (K := S') hinj
    rw [hmap] at this
    exact this.symm
  rw [← hcard]
  refine nonab_card_eq_of_prod hp h.left_pgrp h.card
    (fun b => Subtype.ext (by simpa using h.exp b.1 b.2)) ?_ ?_
  · intro hc
    haveI : IsMulCommutative S' := hc
    have : IsMulCommutative (S'.map φ) := inferInstance
    rw [hmap] at this
    exact hSn this
  · intro E hES' hE hEcard
    have hEmap : E.map φ ≤ S := hmap ▸ Subgroup.map_mono hES'
    have hab : CFSG.Open.IsElemAbelian p (E.map φ) := by
      refine ⟨?_, ?_⟩
      · haveI := hE.1
        infer_instance
      · rintro _ ⟨y, hy, rfl⟩
        rw [← map_pow, hE.2 y hy, map_one]
    have hc : Nat.card (E.map φ) = p ^ 3 := by
      rw [Subgroup.card_map_of_injective hinj, hEcard]
    have := nonab_le_pRank hp hEmap hab hc
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
