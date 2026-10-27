module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzHyperGoodIn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.TauCetiBridge CFSG.LieType.SeitzGeneration

section Helpers


private theorem range_conj_eq_top_adjointGroup_G2 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) (K : Type) [Field K] (hK : Nat.card K = q) :
    (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
      MulAut (adjointGroup ReeTag.G2.tag K)).range = ⊤ := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq.ne_zero)
  haveI : Fact q.Prime := ⟨hq⟩
  have hsub : Subsingleton (K ≃+* K) :=
    CFSG.RankThree.PartOne.CTP.subsingleton_ringEquiv_of_card_eq_prime hK
  obtain ⟨hNF, Θ, hΘ, -, hker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hq hq2 (f := 1) le_rfl K
      (by rw [hK, pow_one]) ReeTag.G2.tag (Or.inr ⟨rfl, hq3⟩)
  rw [eq_top_iff]
  intro α _
  rw [← hker, MonoidHom.mem_ker]
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF α
  rw [hΘ α g σ hgσ]
  exact Subsingleton.elim σ 1

private theorem le_range_conj_adjointGroup_G2_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3)
    {A : Subgroup (MulAut (adjointGroup ReeTag.G2.tag K))} (hA : IsElemAbelian p A) :
    A ≤ (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
      MulAut (adjointGroup ReeTag.G2.tag K)).range := by
  obtain ⟨-, -, ⟨Θ, hΘ, -, hker⟩, -⟩ :=
    G2_three_exact_automorphism_normal_form (f := 1) le_rfl K (by rw [hK, pow_one])
  intro a ha
  have h2all : ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 := by decide
  have h2 : (Θ a) ^ 2 = 1 := h2all (Θ a)
  have hap : a ^ p = 1 := hA.2 a ha
  have hpp : (Θ a) ^ p = 1 := by
    calc (Θ a) ^ p = Θ (a ^ p) := (map_pow Θ a p).symm
      _ = Θ 1 := by rw [hap]
      _ = 1 := map_one Θ
  have hord : orderOf (Θ a) ∣ Nat.gcd 2 p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hpp)
  have hgcd : Nat.gcd 2 p = 1 := Nat.coprime_primes Nat.prime_two hp |>.mpr hp2.symm
  rw [hgcd] at hord
  have h1 : Θ a = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
  have hmem : a ∈ Θ.ker := MonoidHom.mem_ker.mpr h1
  rw [hker] at hmem
  exact hmem

end Helpers

section Main


private theorem card_lt_of_elemAbelian_mulAut_gTwo_cat {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : q ≠ p) (Q : TauCeti.PrimePower) (hQ : Q.p = q) (hQ1 : Q.exponent = 1)
    (hv : (TauCeti.LieTypeIndex.G2 Q).Valid)
    {A : Subgroup (MulAut (CFSG.AGLEmbedding.CatGroup ⟨TauCeti.LieTypeIndex.G2 Q, hv⟩))}
    (hA : IsElemAbelian p A) : Nat.card A < p ^ 3 := by
  have hq : q.Prime := hQ ▸ Q.prime_p
  obtain ⟨K, _, _, hK, hKchar, ⟨eK⟩⟩ :=
    exists_catEquiv_adjointGroup (τ := ReeTag.G2.tag) Even.chevalleyBridgesAll.g2 Q hv
  have hKq : Nat.card K = q := by
    calc Nat.card K = Q.card := hK
      _ = Q.p ^ Q.exponent := TauCeti.PrimePower.card_def Q
      _ = q := by rw [hQ, hQ1, pow_one]
  by_contra hlt
  push Not at hlt
  let A₀ : Subgroup (MulAut (adjointGroup ReeTag.G2.tag K)) :=
    A.map (MulAut.congr eK).toMonoidHom
  have hA₀ : IsElemAbelian p A₀ := hA.map _
  have hcardA₀ : Nat.card A₀ = Nat.card A := by
    rw [Subgroup.card_map_of_injective (MulAut.congr eK).injective]
  have hinner : A₀ ≤ (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
      MulAut (adjointGroup ReeTag.G2.tag K)).range := by
    rcases eq_or_ne q 3 with rfl | hq3
    · have h3 : Q.p = 3 := hQ
      have hchar3 : CharP K ReeTag.G2.prime := by
        simpa [ReeTag.prime] using (h3 ▸ hKchar)
      exact le_range_conj_adjointGroup_G2_three hp hp2 K (by rw [hKq]) hA₀
    · rw [range_conj_eq_top_adjointGroup_G2 hq hq2 hq3 K hKq]
      exact le_top
  have hrange : (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
      MulAut (adjointGroup ReeTag.G2.tag K)).range ≠ ⊥ := by
    intro hbot
    have hb : A₀ = ⊥ := le_bot_iff.mp (hbot ▸ hinner)
    rw [hb, Subgroup.card_bot] at hcardA₀
    have hp3 : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  haveI hsimple : IsSimpleGroup (adjointGroup ReeTag.G2.tag K) :=
    isSimpleGroup_adjointGroup_G2 Q hv K hK
  have hinj : Function.Injective (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
      MulAut (adjointGroup ReeTag.G2.tag K)) :=
    conj_injective_of_simple_of_range_ne_bot hrange
  set E : Subgroup (adjointGroup ReeTag.G2.tag K) :=
    A₀.comap (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
      MulAut (adjointGroup ReeTag.G2.tag K)) with hEdef
  have hE : IsElemAbelian p E := isElemAbelian_comap_conj hinj hA₀
  have hcardE : Nat.card E = Nat.card A := by
    rw [← hcardA₀, ← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hinner]
  obtain ⟨F, hFcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (G := ↥E) hp
    hE.isPGroup (by rw [hcardE]; exact hlt)
  have hF : IsElemAbelian p ((F.map E.subtype).map eK.symm.toMonoidHom) :=
    (hE.mono (Subgroup.map_subtype_le F)).map _
  have hFcard : Nat.card ((F.map E.subtype).map eK.symm.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective eK.symm.injective,
      Subgroup.card_map_of_injective E.subtype_injective, hFcard]
  refine CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzHyperGoodInAux.no_cube_G2
    (d := ⟨TauCeti.LieTypeIndex.G2 Q, hv⟩) ⟨Q, rfl⟩ hp hp2 ?_ hF hFcard
  simpa [hQ] using hpq.symm

end Main

theorem card_lt_of_elemAbelian_mulAut_gTwo
    {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : q ≠ p) {S : Type}
    [Group S] [Finite S] {d : TauCeti.ValidLieTypeIndex}
    (e : S ≃* CFSG.AGLEmbedding.CatGroup d) {Q : TauCeti.PrimePower} (hQ : Q.p = q)
    (hQ1 : Q.exponent = 1) (hd : d.1 = .G2 Q) {A : Subgroup (MulAut S)}
    (hA : CFSG.Open.IsElemAbelian p A) : Nat.card A < p ^ 3 := by
  obtain ⟨d1, hv⟩ := d
  obtain rfl : d1 = .G2 Q := hd
  let A' : Subgroup (MulAut (CFSG.AGLEmbedding.CatGroup ⟨.G2 Q, hv⟩)) :=
    A.map (MulAut.congr e).toMonoidHom
  have hA' : CFSG.Open.IsElemAbelian p A' := hA.map _
  have hcard' : Nat.card A' = Nat.card A := by
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective]
  have h := card_lt_of_elemAbelian_mulAut_gTwo_cat hp hp2 hq2 hpq Q hQ hQ1 hv hA'
  rwa [hcard'] at h

end CFSG.LocalAnalysis.GLTheoremA.H248
