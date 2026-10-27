module

public import CFSG.LieType.SeitzGeneration.OrthSingular
public import CFSG.LieType.SeitzGeneration.OrthPaired
public import CFSG.RankThree.CentralCover.SteinbergBNOrthogonalRepeatedSummands
public import CFSG.LieType.SeitzGeneration.Defs

public section

namespace CFSG.LieType.SeitzGeneration

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.RankThree.CentralCover
open CFSG.RankThree.Classical2 (orthDerived)

section Omega

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem mem_orthDerived_of_odd_pow (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ} (hodd : Odd p)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgp : g ^ p = 1) :
    g ∈ orthDerived Q := by
  obtain ⟨hE, hclos⟩ := orthDerived_eq_and_le_closure hQ hT
  obtain ⟨k, hk⟩ := hodd
  have hS : ∀ y ∈ Set.range (reflect Q) ∪ (elementaryGroup Q : Set (V ≃ₗ[K] V)),
      y ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ y ^ 2 ∈ orthDerived Q := by
    rintro y (⟨v, rfl⟩ | hy)
    · refine ⟨?_, ?_⟩
      · exact reflect_mem_orthogonalGroup Q v
      · rw [_root_.sq, reflect_mul_self Q v]
        exact one_mem _
    · refine ⟨elementaryGroup_le_orthogonalGroup Q hy, ?_⟩
      rw [hE]
      exact pow_mem hy 2
  have h2 := (sq_mem_orthDerived_of_mem_closure hS (hclos hg)).2
  have hpow : g = (g ^ (k + 1)) ^ 2 := by
    rw [← pow_mul, show (k + 1) * 2 = p + 1 by omega, pow_succ, hgp, one_mul]
  have hgk : g ^ (k + 1) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := pow_mem hg _
  have h3 := (sq_mem_orthDerived_of_mem_closure hS (hclos hgk)).2
  rw [hpow]
  exact h3

end Omega

section Rank3

theorem false_of_three_independent {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hr : RankLE2 p G) {e₁ e₂ e₃ : G} (h12 : Commute e₁ e₂) (h13 : Commute e₁ e₃)
    (h23 : Commute e₂ e₃) (h₁ : e₁ ^ p = 1) (h₂ : e₂ ^ p = 1) (h₃ : e₃ ^ p = 1)
    (hi : ∀ i j k : ℤ, e₁ ^ i * e₂ ^ j * e₃ ^ k = 1 →
      (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j ∧ (p : ℤ) ∣ k) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hne1 : e₁ ≠ 1 := fun h => by
    have := (hi 1 0 0 (by rw [h]; simp)).1
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast this))
  have hne2 : e₂ ≠ 1 := fun h => by
    have := (hi 0 1 0 (by rw [h]; simp)).2.1
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast this))
  have hne3 : e₃ ≠ 1 := fun h => by
    have := (hi 0 0 1 (by rw [h]; simp)).2.2
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast this))
  have ho₁ : orderOf e₁ = p := orderOf_eq_prime h₁ hne1
  have ho₂ : orderOf e₂ = p := orderOf_eq_prime h₂ hne2
  have ho₃ : orderOf e₃ = p := orderOf_eq_prime h₃ hne3
  have hc12 : ∀ (a : ↥(Subgroup.zpowers e₁)) (b : ↥(Subgroup.zpowers e₂)),
      Commute ((Subgroup.zpowers e₁).subtype a) ((Subgroup.zpowers e₂).subtype b) := by
    intro a b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    change Commute (a : G) (b : G)
    rw [← hk, ← hl]
    exact h12.zpow_zpow k l
  let f₂ : ↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂) →* G :=
    MonoidHom.noncommCoprod (Subgroup.zpowers e₁).subtype (Subgroup.zpowers e₂).subtype hc12
  have hc3 : ∀ (a : ↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂))
      (c : ↥(Subgroup.zpowers e₃)), Commute (f₂ a) ((Subgroup.zpowers e₃).subtype c) := by
    intro a c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.1.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp c.2
    change Commute ((a.1 : G) * (a.2 : G)) (c : G)
    rw [← hk, ← hl, ← hm]
    exact (h13.zpow_zpow k m).mul_left (h23.zpow_zpow l m)
  let f₃ : (↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂)) × ↥(Subgroup.zpowers e₃) →* G :=
    MonoidHom.noncommCoprod f₂ (Subgroup.zpowers e₃).subtype hc3
  have hf : Function.Injective f₃ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨⟨a, b⟩, c⟩ hab
    have hab' : (a : G) * b * c = 1 := hab
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp c.2
    rw [← hk, ← hl, ← hm] at hab'
    obtain ⟨hpk, hpl, hpm⟩ := hi k l m hab'
    have ha : a = 1 := by
      apply Subtype.ext
      rw [← hk]
      obtain ⟨n, rfl⟩ := hpk
      rw [zpow_mul, zpow_natCast, h₁, one_zpow]
      rfl
    have hb : b = 1 := by
      apply Subtype.ext
      rw [← hl]
      obtain ⟨n, rfl⟩ := hpl
      rw [zpow_mul, zpow_natCast, h₂, one_zpow]
      rfl
    have hc : c = 1 := by
      apply Subtype.ext
      rw [← hm]
      obtain ⟨n, rfl⟩ := hpm
      rw [zpow_mul, zpow_natCast, h₃, one_zpow]
      rfl
    rw [ha, hb, hc]
    rfl
  have hcard : Nat.card ((↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂)) ×
      ↥(Subgroup.zpowers e₃)) = p ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, Nat.card_zpowers, ho₁,
      ho₂, ho₃]
    ring
  have hF : IsElemAbelian p f₃.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : G) * b = b * a
      rw [← hx, ← hz, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (Prod.ext (mul_comm' x.1.1 z.1.1) (mul_comm' x.1.2 z.1.2))
        (mul_comm' x.2 z.2)
    · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
      rw [← map_pow]
      have hpow : ∀ (e : G) (he : e ^ p = 1) (a : ↥(Subgroup.zpowers e)), a ^ p = 1 := by
        intro e he a
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
        apply Subtype.ext
        change (a : G) ^ p = 1
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
      have : x ^ p = 1 := Prod.ext (Prod.ext (hpow e₁ h₁ x.1.1) (hpow e₂ h₂ x.1.2))
        (hpow e₃ h₃ x.2)
      rw [this, map_one]
  have hcardF : Nat.card f₃.range = p ^ 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hcard
  have hle := hr f₃.range hF
  rw [hcardF] at hle
  have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end Rank3

section Multiplicity

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem multiplicity_le_two_of_rankLE2 (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hrank : RankLE2 p (orthDerived Q)) {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) : primaryMultiplicity x.toLinearMap h ≤ 2 := by
  classical
  by_contra hlt
  push Not at hlt
  have hRS : RepeatedSummands Q x p h := by
    by_cases hself : h = reciprocalPolynomial h
    · exact hx.repeatedSummands_selfDual hp hp2 hh hne1 hself
    · exact hx.repeatedSummands_paired hp hh hne1 hself
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) fun e₁ e₂ h =>
      LinearEquiv.ext (congrFun h)
  set m := primaryMultiplicity x.toLinearMap h with hmdef
  obtain ⟨R, W, _, _, _, _, QR, QW, ψ, hψ, hQW, hnt, ⟨h₀, hh₀, ho, hx₀⟩, -, -⟩ := hRS
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : Fact p.Prime := ⟨hp⟩
  have hh₀p : h₀ ^ p = 1 := by rw [← ho, pow_orderOf_eq_one]
  let F : (Fin m → (W ≃ₗ[K] W)) →* (V ≃ₗ[K] V) := (coordAut ψ).comp (piAut K W m)
  have hFinj : Function.Injective F := fun a b hab =>
    piAut_injective (coordAut_injective ψ hab)
  have hgsO : ∀ j : Fin m, ∀ i, (Pi.mulSingle j h₀ : Fin m → (W ≃ₗ[K] W)) i ∈
      TauCeti.QuadraticMap.orthogonalGroup QW := by
    intro j i
    by_cases hij : i = j
    · subst hij
      simpa using hh₀
    · rw [Pi.mulSingle_eq_of_ne hij]
      exact one_mem _
  have hgO : ∀ j, F (Pi.mulSingle j h₀) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun j =>
    coordAut_piAut_mem hψ (hgsO j)
  have hgp : ∀ j, F (Pi.mulSingle j h₀) ^ p = 1 := by
    intro j
    rw [← map_pow, ← Pi.mulSingle_pow, hh₀p, Pi.mulSingle_one, map_one]
  have hgΩ : ∀ j, F (Pi.mulSingle j h₀) ∈ orthDerived Q := fun j =>
    mem_orthDerived_of_odd_pow hQ hT hodd (hgO j) (hgp j)
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  let i₂ : Fin m := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  let e : Fin m → orthDerived Q := fun j => ⟨F (Pi.mulSingle j h₀), hgΩ j⟩
  have hcomm : ∀ {a b : Fin m}, a ≠ b → Commute (e a) (e b) := fun {a b} hab =>
    Subtype.ext (Commute.map (Pi.mulSingle_commute (f := fun _ : Fin m => W ≃ₗ[K] W) hab h₀ h₀)
      F).eq
  have hep : ∀ j, e j ^ p = 1 := fun j => Subtype.ext (hgp j)
  refine false_of_three_independent (G := orthDerived Q) hp hrank (e₁ := e i₀) (e₂ := e i₁)
    (e₃ := e i₂) (hcomm h01) (hcomm h02) (hcomm h12) (hep i₀) (hep i₁) (hep i₂) ?_
  intro i j k hijk
  have h1 : F (Pi.mulSingle i₀ (h₀ ^ i) * Pi.mulSingle i₁ (h₀ ^ j) * Pi.mulSingle i₂ (h₀ ^ k)) =
      1 := by
    have := congrArg Subtype.val hijk
    simpa [e, map_mul, map_zpow, Pi.mulSingle_zpow] using this
  have h2 := hFinj (h1.trans (map_one F).symm)
  have hext : ∀ n : ℤ, h₀ ^ n = 1 → (p : ℤ) ∣ n := by
    intro n hn
    rw [← ho]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hn
  refine ⟨hext i ?_, hext j ?_, hext k ?_⟩
  · have := congrFun h2 i₀
    simpa [Pi.mulSingle_eq_of_ne h01, Pi.mulSingle_eq_of_ne h02] using this
  · have := congrFun h2 i₁
    simpa [Pi.mulSingle_eq_of_ne h01.symm, Pi.mulSingle_eq_of_ne h12] using this
  · have := congrFun h2 i₂
    simpa [Pi.mulSingle_eq_of_ne h02.symm, Pi.mulSingle_eq_of_ne h12.symm] using this

end Multiplicity

section Lines

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

omit [Finite K] [FiniteDimensional K V] in
theorem exists_not_mem_three_lines (hp : p.Prime) (hp2 : p ≠ 2) [Finite E]
    (hexp : ∀ x : E, x ^ p = 1) {M N B : Subgroup E}
    (hM : Nat.card M = p) (hN : Nat.card N = p) (hB : Nat.card B = p) (hMN : M ≠ N)
    (hNB : N ≠ B) : ∃ a : E, a ∉ M ∧ a ∉ N ∧ a ∉ B := by
  by_contra hcon
  push Not at hcon
  have hMN' := inf_eq_bot_of_card_prime' hp hM hN hMN
  have hNB' := inf_eq_bot_of_card_prime' hp hN hB hNB
  have hM0 : M ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hM
    exact hp.one_lt.ne' hM.symm
  have hN0 : N ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hN
    exact hp.one_lt.ne' hN.symm
  obtain ⟨m, hm1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hM0
  obtain ⟨n, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hN0
  have hm1' : (m : E) ≠ 1 := fun h => hm1 (Subtype.ext h)
  have hn1' : (n : E) ≠ 1 := fun h => hn1 (Subtype.ext h)
  have hnM : (n : E) ∉ M := fun h => by
    have : (n : E) ∈ M ⊓ N := ⟨h, n.2⟩
    rw [hMN'] at this
    exact hn1' (Subgroup.mem_bot.mp this)
  have hmN : (m : E) ∉ N := fun h => by
    have : (m : E) ∈ M ⊓ N := ⟨m.2, h⟩
    rw [hMN'] at this
    exact hm1' (Subgroup.mem_bot.mp this)
  have hn2 : (n : E) ^ 2 ∉ M := fun h => by
    have : (n : E) ^ 2 ∈ M ⊓ N := ⟨h, N.pow_mem n.2 2⟩
    rw [hMN'] at this
    have h2 : (n : E) ^ 2 = 1 := Subgroup.mem_bot.mp this
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    apply hn1'
    have h3 : (n : E) ^ (2 * k + 1) = 1 := hk ▸ hexp n
    rwa [pow_succ, pow_mul, h2, one_pow, one_mul] at h3
  have h1 : (m : E) * n ∈ B := by
    refine hcon _ (fun h => hnM ?_) (fun h => hmN ?_)
    · have := M.mul_mem (M.inv_mem m.2) h
      simpa using this
    · have := N.mul_mem h (N.inv_mem n.2)
      simpa using this
  have h2 : (m : E) * n ^ 2 ∈ B := by
    refine hcon _ (fun h => hn2 ?_) (fun h => hmN ?_)
    · have := M.mul_mem (M.inv_mem m.2) h
      simpa using this
    · have := N.mul_mem h (N.inv_mem (N.pow_mem n.2 2))
      simpa using this
  have h3 : (n : E) ∈ B := by
    have := B.mul_mem (B.inv_mem h1) h2
    have e : ((m : E) * n)⁻¹ * ((m : E) * n ^ 2) = n := by group
    rwa [e] at this
  have : (n : E) ∈ N ⊓ B := ⟨n.2, h3⟩
  rw [hNB'] at this
  exact hn1' (Subgroup.mem_bot.mp this)

end Lines

section Dim

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] in
open scoped _root_.Classical in
theorem sum_natDegree_nontrivial_le (hx : OddOrderIsometry Q p x) :
    ∑ k ∈ (primaryFactors x.toLinearMap).erase (X - 1), k.natDegree + 1 ≤ p := by
  set NT := (primaryFactors x.toLinearMap).erase (X - 1) with hNT
  have hnot : (X - 1 : K[X]) ∉ NT := Finset.notMem_erase _ _
  have hmon : ∀ k ∈ insert (X - 1 : K[X]) NT, k.Monic := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact monic_X_sub_one
    · exact monic_of_mem_primaryFactors (Finset.mem_of_mem_erase hk)
  have hirr : ∀ k ∈ insert (X - 1 : K[X]) NT, Irreducible k := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact irreducible_X_sub_one
    · exact irreducible_of_mem_primaryFactors (Finset.mem_of_mem_erase hk)
  have hdvd : ∀ k ∈ insert (X - 1 : K[X]) NT, k ∣ (X ^ p - 1 : K[X]) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simpa using sub_dvd_pow_sub_pow (X : K[X]) 1 p
    · exact hx.dvd_X_pow_sub_one (Finset.mem_of_mem_erase hk)
  have hcop : Set.Pairwise (↑(insert (X - 1 : K[X]) NT))
      (Function.onFun IsCoprime (id : K[X] → K[X])) := by
    intro k hk l hl hkl
    exact isCoprime_of_irreducible_monic_ne (hirr k hk) (hirr l hl) (hmon k hk) (hmon l hl) hkl
  have hprod : ∏ k ∈ insert (X - 1 : K[X]) NT, k ∣ (X ^ p - 1 : K[X]) :=
    Finset.prod_dvd_of_coprime hcop hdvd
  have hp0 : p ≠ 0 := fun h0 => hx.cast_ne_zero (by rw [h0]; simp)
  have hne : (X ^ p - 1 : K[X]) ≠ 0 := by
    simpa using X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hp0) (1 : K)
  have hle := natDegree_le_of_dvd hprod hne
  rw [natDegree_prod_of_monic _ _ hmon, Finset.sum_insert hnot] at hle
  have hdeg : (X ^ p - 1 : K[X]).natDegree = p := by
    simpa using natDegree_X_pow_sub_C (n := p) (r := (1 : K))
  have hX : (X - 1 : K[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : K)
  rw [hdeg, hX] at hle
  omega

open scoped _root_.Classical in
theorem finrank_le_fixed_add (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : RankLE2 p (orthDerived Q)) (hx : OddOrderIsometry Q p x) :
    finrank K V ≤ finrank K (primaryComponent x.toLinearMap (X - 1)) + 2 * (p - 1) := by
  have hsum := finrank_eq_sum_degree_mul_multiplicity (x := x.toLinearMap) hx.squarefree_minpoly
  rw [Finset.sum_coe_sort (primaryFactors x.toLinearMap)
    (fun k => k.natDegree * primaryMultiplicity x.toLinearMap k)] at hsum
  have hbound : ∑ k ∈ (primaryFactors x.toLinearMap).erase (X - 1),
      k.natDegree * primaryMultiplicity x.toLinearMap k ≤ 2 * (p - 1) := by
    have h1 := sum_natDegree_nontrivial_le hx
    calc ∑ k ∈ (primaryFactors x.toLinearMap).erase (X - 1),
          k.natDegree * primaryMultiplicity x.toLinearMap k
        ≤ ∑ k ∈ (primaryFactors x.toLinearMap).erase (X - 1), k.natDegree * 2 :=
          Finset.sum_le_sum fun k hk => Nat.mul_le_mul_left _
            (multiplicity_le_two_of_rankLE2 hQ hT hp hp2 hrank hx (Finset.mem_of_mem_erase hk)
              (Finset.ne_of_mem_erase hk))
      _ = 2 * ∑ k ∈ (primaryFactors x.toLinearMap).erase (X - 1), k.natDegree := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ 2 * (p - 1) := Nat.mul_le_mul_left _ (by omega)
  by_cases hmem : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap
  · rw [← Finset.add_sum_erase _ _ hmem] at hsum
    have : Fact (Irreducible (X - 1 : K[X])) := ⟨irreducible_X_sub_one⟩
    have hX : (X - 1 : K[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : K)
    have hfix := finrank_primaryComponent x.toLinearMap (X - 1 : K[X])
    rw [hX, one_mul] at hfix
    have hm : primaryMultiplicity x.toLinearMap (X - 1 : K[X]) =
        finrank K (primaryComponent x.toLinearMap (X - 1)) := by rw [hfix]
    rw [hX, one_mul, hm] at hsum
    omega
  · rw [Finset.erase_eq_of_notMem hmem] at hbound
    omega

end Dim

section ThreeLines

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

omit [Finite K] [FiniteDimensional K V] in
theorem finrank_sup_of_disjoint {s t : Submodule K V} [FiniteDimensional K V]
    (h : Disjoint s t) : finrank K ↥(s ⊔ t) = finrank K s + finrank K t := by
  have := Submodule.finrank_sup_add_finrank_inf_eq s t
  rw [h.eq_bot, finrank_bot] at this
  omega

omit [Finite K] [FiniteDimensional K V] in
theorem disjoint_lineSpace_sup_lineSpace (hK : KernelLineData Q p E) {L₁ L₂ L₃ : Subgroup E}
    (h₁ : Nat.card L₁ = p) (h₂ : Nat.card L₂ = p) (h₃ : Nat.card L₃ = p) (h13 : L₁ ≠ L₃)
    (h23 : L₂ ≠ L₃) : Disjoint (lineSpace L₃) (lineSpace L₁ ⊔ lineSpace L₂) := by
  classical
  have hind := hK.internal.submodule_iSupIndep
  have h := hind (some ⟨L₃, h₃⟩)
  refine h.mono_right (sup_le ?_ ?_)
  · have hne : (some ⟨L₁, h₁⟩ : Option {M : Subgroup E // Nat.card M = p}) ≠ some ⟨L₃, h₃⟩ :=
      fun h' => h13 (congrArg Subtype.val (Option.some.inj h'))
    exact le_iSup₂_of_le (some ⟨L₁, h₁⟩) hne le_rfl
  · have hne : (some ⟨L₂, h₂⟩ : Option {M : Subgroup E // Nat.card M = p}) ≠ some ⟨L₃, h₃⟩ :=
      fun h' => h23 (congrArg Subtype.val (Option.some.inj h'))
    exact le_iSup₂_of_le (some ⟨L₂, h₂⟩) hne le_rfl

omit [Finite K] in
theorem eq_zero_of_fixed_of_not_mem (hp : p.Prime) (hK : KernelLineData Q p E) {L : Subgroup E}
    (hL : Nat.card L = p) {a : E} (ha : a ≠ 1) (haL : a ∉ L) {v : V} (hv : v ∈ lineSpace L)
    (hfix : (((a : E) : orthDerived Q) : V ≃ₗ[K] V) v = v) : v = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf a = p := orderOf_eq_prime (hK.exp a) ha
  have hA : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hord]
  have hLA : L ≠ Subgroup.zpowers a := fun h => haL (h ▸ Subgroup.mem_zpowers a)
  exact eq_zero_of_fixed_lineSpace hK hp hL hA hLA (t := ⟨a, Subgroup.mem_zpowers a⟩)
    (fun h => ha (congrArg Subtype.val h)) hv hfix

omit [Finite K] in
theorem finrank_three_lines_le (hp : p.Prime) (hK : KernelLineData Q p E)
    {L₁ L₂ L₃ : Subgroup E} (h₁ : Nat.card L₁ = p) (h₂ : Nat.card L₂ = p)
    (h₃ : Nat.card L₃ = p) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) {a : E} (ha : a ≠ 1)
    (ha₁ : a ∉ L₁) (ha₂ : a ∉ L₂) (ha₃ : a ∉ L₃) :
    finrank K (primaryComponent (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap (X - 1)) +
      (finrank K (lineSpace L₁) + finrank K (lineSpace L₂) + finrank K (lineSpace L₃)) ≤
        finrank K V := by
  set x : V ≃ₗ[K] V := (((a : E) : orthDerived Q) : V ≃ₗ[K] V) with hx
  set C := primaryComponent x.toLinearMap (X - 1) with hC
  have hd12 : Disjoint (lineSpace L₁) (lineSpace L₂) :=
    (disjoint_lineSpace_sup hK h₁ h₂ h12).mono_right le_sup_right
  have hd3 := disjoint_lineSpace_sup_lineSpace hK h₁ h₂ h₃ h13 h23
  have hfree : ∀ (L : Subgroup E), Nat.card L = p → a ∉ L → ∀ v ∈ lineSpace L, x v = v → v = 0 :=
    fun L hL haL v hv hfix => eq_zero_of_fixed_of_not_mem hp hK hL ha haL hv hfix
  have hstab : ∀ (L : Subgroup E), ∀ v ∈ lineSpace L, x v ∈ lineSpace L :=
    fun L v hv => lineSpace_stable hK.comm L a hv
  have hdisj : Disjoint C (lineSpace L₁ ⊔ lineSpace L₂ ⊔ lineSpace L₃) := by
    rw [Submodule.disjoint_def]
    intro v hvC hvU
    have hfixv : x v = v := by
      have := mem_primaryComponent.mp hvC
      simpa [sub_eq_zero] using this
    obtain ⟨w, hw, u₃, hu₃, rfl⟩ := Submodule.mem_sup.mp hvU
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hw
    have hsum : (x u₁ - u₁) + (x u₂ - u₂) + (x u₃ - u₃) = 0 := by
      have : x (u₁ + u₂ + u₃) - (u₁ + u₂ + u₃) = 0 := sub_eq_zero.mpr hfixv
      rw [map_add, map_add] at this
      rw [← this]
      abel
    have hd1 : x u₁ - u₁ ∈ lineSpace L₁ := (lineSpace L₁).sub_mem (hstab L₁ u₁ hu₁) hu₁
    have hd2 : x u₂ - u₂ ∈ lineSpace L₂ := (lineSpace L₂).sub_mem (hstab L₂ u₂ hu₂) hu₂
    have hd3' : x u₃ - u₃ ∈ lineSpace L₃ := (lineSpace L₃).sub_mem (hstab L₃ u₃ hu₃) hu₃
    have e3 : x u₃ - u₃ = 0 := by
      refine Submodule.disjoint_def.mp hd3 _ hd3' ?_
      have : x u₃ - u₃ = -((x u₁ - u₁) + (x u₂ - u₂)) := by
        rw [eq_neg_iff_add_eq_zero, ← hsum]
        abel
      rw [this]
      exact (lineSpace L₁ ⊔ lineSpace L₂).neg_mem (Submodule.add_mem_sup hd1 hd2)
    have e1 : x u₁ - u₁ = 0 := by
      refine Submodule.disjoint_def.mp hd12 _ hd1 ?_
      have : x u₁ - u₁ = -(x u₂ - u₂) := by
        rw [eq_neg_iff_add_eq_zero]
        rw [e3, add_zero] at hsum
        exact hsum
      rw [this]
      exact (lineSpace L₂).neg_mem hd2
    have e2 : x u₂ - u₂ = 0 := by
      rw [e3, add_zero, e1, zero_add] at hsum
      exact hsum
    rw [hfree L₁ h₁ ha₁ u₁ hu₁ (sub_eq_zero.mp e1), hfree L₂ h₂ ha₂ u₂ hu₂ (sub_eq_zero.mp e2),
      hfree L₃ h₃ ha₃ u₃ hu₃ (sub_eq_zero.mp e3)]
    simp
  have h1 := finrank_sup_of_disjoint hdisj
  have h2 := finrank_sup_of_disjoint hd12
  have h3 := finrank_sup_of_disjoint (hd3.symm)
  have h4 := Submodule.finrank_le (C ⊔ (lineSpace L₁ ⊔ lineSpace L₂ ⊔ lineSpace L₃))
  omega

end ThreeLines

section TwoDim

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem two_le_finrank_of_fixedPointFree {S : Submodule K V} {T : V ≃ₗ[K] V}
    (hS : ∀ s ∈ S, T s ∈ S) (hreg : ∀ u ∈ S, (∀ t ∈ S, polar Q u t = 0) → u = 0)
    (hSne : S ≠ ⊥) (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {p : ℕ} (hodd : Odd p)
    (hTp : T ^ p = 1) (hfree : ∀ v ∈ S, T v = v → v = 0) : 2 ≤ finrank K S := by
  by_contra hlt
  push Not at hlt
  obtain ⟨w₀, hw₀S, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSne
  have hfr : finrank K S = 1 := by
    have : 0 < finrank K S := Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨w₀, hw₀S⟩, fun h0 => hw₀ (congrArg Subtype.val h0)⟩
    omega
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hfr
  have hvS : (v : V) ∈ S := v.2
  have hv0' : (v : V) ≠ 0 := fun h => hv0 (Subtype.ext h)
  obtain ⟨c, hc⟩ := hv ⟨T v, hS _ hvS⟩
  have hcv : T (v : V) = c • (v : V) := (congrArg Subtype.val hc).symm
  have hpolar : polar Q (v : V) (v : V) ≠ 0 := by
    intro h0
    refine hv0' (hreg v hvS fun t ht => ?_)
    obtain ⟨c', hc'⟩ := hv ⟨t, ht⟩
    have ht' : t = c' • (v : V) := (congrArg Subtype.val hc').symm
    rw [ht', polar_smul_right_eq, h0, mul_zero]
  have hc2 : c ^ 2 = 1 := by
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hT (v : V) (v : V)
    rw [hcv, polar_smul_left_eq, polar_smul_right_eq] at h1
    have : (c ^ 2 - 1) * polar Q (v : V) (v : V) = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hpolar)
  have hpow : ∀ n : ℕ, (T ^ n) (v : V) = c ^ n • (v : V) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, hcv, smul_smul, pow_succ]
  have hcp : c ^ p = 1 := by
    have h1 := hpow p
    rw [hTp] at h1
    have : (1 - c ^ p) • (v : V) = 0 := by
      rw [sub_smul, one_smul, ← h1]
      simp
    exact (sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hv0')).symm
  obtain ⟨k, hk⟩ := hodd
  have hc1 : c = 1 := by
    have : c ^ (2 * k + 1) = 1 := hk ▸ hcp
    rwa [pow_succ, pow_mul, hc2, one_pow, one_mul] at this
  rw [hc1, one_smul] at hcv
  exact hv0' (hfree _ hvS hcv)

end TwoDim

section Final

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem false_of_rankLE2_three (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    (hpl : 3 ≠ ringChar K) (hrank : RankLE2 3 (orthDerived Q)) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 3 ^ 2) (hV₀ : ∀ e ∈ planeFixSpace E, Q e = 0 → e = 0) : False := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hexpE : ∀ x : E, x ^ 3 = 1 := hK.exp
  obtain ⟨M, N, hM, hN, hMN, hVM, hVN⟩ := hK.two_active
  have hV0 : finrank K (planeFixSpace E) ≤ 2 := by
    by_contra h3
    push Not at h3
    have hreg : PolarNondegOn Q (planeFixSpace E) := fun u hu hperp =>
      congrArg Subtype.val ((hK.regular none).1 ⟨u, hu⟩ fun t => by
        simpa [polarBilin_apply_apply] using hperp t t.2)
    obtain ⟨e, he, he0, heQ⟩ := exists_singular_of_three_le_general hreg h3
    exact he0 (hV₀ e he heQ)
  have hM0 := ne_bot_of_card_prime hp hM
  have hN0 := ne_bot_of_card_prime hp hN
  obtain ⟨m, hm1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hM0
  obtain ⟨n, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hN0
  have hm1' : (m : E) ≠ 1 := fun h => hm1 (Subtype.ext h)
  have hn1' : (n : E) ≠ 1 := fun h => hn1 (Subtype.ext h)
  have hMN' := inf_eq_bot_of_card_prime' hp hM hN hMN
  have hmN : (m : E) ∉ N := fun h => by
    have : (m : E) ∈ M ⊓ N := ⟨m.2, h⟩
    rw [hMN'] at this
    exact hm1' (Subgroup.mem_bot.mp this)
  have hnM : (n : E) ∉ M := fun h => by
    have : (n : E) ∈ M ⊓ N := ⟨h, n.2⟩
    rw [hMN'] at this
    exact hn1' (Subgroup.mem_bot.mp this)
  have hpow3 : ∀ y : E, (((y : E) : orthDerived Q) : V ≃ₗ[K] V) ^ 3 = 1 := fun y => by
    have := congrArg (fun z : E => (((z : E) : orthDerived Q) : V ≃ₗ[K] V)) (hexpE y)
    simpa using this
  have hreg' : ∀ (L : Subgroup E), Nat.card L = 3 → ∀ u ∈ lineSpace L,
      (∀ t ∈ lineSpace L, polar Q u t = 0) → u = 0 := fun L hL => regular_lineSpace hK hL
  have hM2 : 2 ≤ finrank K (lineSpace M) :=
    two_le_finrank_of_fixedPointFree (T := (((n : E) : orthDerived Q) : V ≃ₗ[K] V))
      (fun s hs => lineSpace_stable hK.comm M n hs) (hreg' M hM) hVM
      (orthDerived_le_orthogonalGroup Q ((n : E) : orthDerived Q).2) (p := 3) (by decide)
      (hpow3 n) (fun v hv hfix =>
        eq_zero_of_fixed_of_not_mem hp hK hM hn1' hnM hv hfix)
  have hN2 : 2 ≤ finrank K (lineSpace N) :=
    two_le_finrank_of_fixedPointFree (T := (((m : E) : orthDerived Q) : V ≃ₗ[K] V))
      (fun s hs => lineSpace_stable hK.comm N m hs) (hreg' N hN) hVN
      (orthDerived_le_orthogonalGroup Q ((m : E) : orthDerived Q).2) (p := 3) (by decide)
      (hpow3 m) (fun v hv hfix =>
        eq_zero_of_fixed_of_not_mem hp hK hN hm1' hmN hv hfix)
  have key : ∀ B : Subgroup E, Nat.card B = 3 → B ≠ M → B ≠ N →
      finrank K (lineSpace M) + finrank K (lineSpace N) + finrank K (lineSpace B) ≤ 4 := by
    intro B hB hBM hBN
    obtain ⟨a, haM, haN, haB⟩ := exists_not_mem_three_lines hp hp2 hexpE hM hN hB hMN hBN.symm
    have ha1 : a ≠ 1 := fun h => haM (h ▸ M.one_mem)
    have hxa := oddOrderIsometry_of_mem hQ hp hpl hK ha1
    have h1 := finrank_le_fixed_add hQ hT hp hp2 hrank hxa
    have h2 := finrank_three_lines_le hp hK hM hN hB hMN hBM.symm hBN.symm ha1 haM haN haB
    omega
  have hmn : (m : E) * n ≠ 1 := fun h => hmN (by
    have : (m : E) = (n : E)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact N.inv_mem n.2)
  have hmnN : (m : E) * n ∉ N := fun h => hmN (by
    have := N.mul_mem h (N.inv_mem n.2)
    simpa using this)
  have hmnM : (m : E) * n ∉ M := fun h => hnM (by
    have := M.mul_mem (M.inv_mem m.2) h
    simpa using this)
  have hmn3 : ((m : E) * n) ^ 3 = 1 := hexpE _
  have hB0 : Nat.card (Subgroup.zpowers ((m : E) * n)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hmn3 hmn
  have hB0M : Subgroup.zpowers ((m : E) * n) ≠ M := fun h =>
    hmnM ((SetLike.ext_iff.mp h _).mp (Subgroup.mem_zpowers _))
  have hB0N : Subgroup.zpowers ((m : E) * n) ≠ N := fun h =>
    hmnN ((SetLike.ext_iff.mp h _).mp (Subgroup.mem_zpowers _))
  have hk0 := key _ hB0 hB0M hB0N
  have hM2' : finrank K (lineSpace M) ≤ 2 := by omega
  have hN2' : finrank K (lineSpace N) ≤ 2 := by omega
  have hzero : ∀ B : Subgroup E, Nat.card B = 3 → B ≠ M → B ≠ N → lineSpace B = ⊥ := by
    intro B hB hBM hBN
    have := key B hB hBM hBN
    exact Submodule.finrank_eq_zero.mp (by omega)
  have htop : (⊤ : Submodule K V) ≤ planeFixSpace E ⊔ lineSpace M ⊔ lineSpace N := by
    rw [← hK.internal.submodule_iSup_eq_top]
    refine iSup_le fun i => ?_
    rcases i with _ | ⟨B, hB⟩
    · exact le_sup_of_le_left (le_sup_left)
    · by_cases hBM : B = M
      · subst hBM
        exact le_sup_of_le_left le_sup_right
      · by_cases hBN : B = N
        · subst hBN
          exact le_sup_right
        · change lineSpace B ≤ _
          rw [hzero B hB hBM hBN]
          exact bot_le
  have h1 := Submodule.finrank_le (planeFixSpace E ⊔ lineSpace M ⊔ lineSpace N)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (planeFixSpace E ⊔ lineSpace M)
    (lineSpace N)
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (planeFixSpace E) (lineSpace M)
  have h4 : finrank K V ≤ finrank K ↥(planeFixSpace E ⊔ lineSpace M ⊔ lineSpace N) := by
    have := Submodule.finrank_mono htop
    rwa [finrank_top] at this
  omega

end Final

section Close

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem closure_eq_top_of_low_three (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    (hpl : 3 ≠ ringChar K) (hrank : RankLE2 3 (orthDerived Q)) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 3 ^ 2) :
    Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
  by_cases hs : ∃ e ∈ planeFixSpace E, e ≠ 0 ∧ Q e = 0
  · obtain ⟨e, he, he0, heQ⟩ := hs
    have : Nontrivial V := nontrivial_of_three_singular hT
    exact closure_eq_top_of_singular_fixed hQ hT Nat.prime_three (by norm_num) hpl E hcomm hexp
      hcard he he0 heQ
  · exact (false_of_rankLE2_three hQ hT hdim hpl hrank E hcomm hexp hcard
      (fun e he heQ => by_contra fun h0 => hs ⟨e, he, h0, heQ⟩)).elim

end Close

end CFSG.LieType.SeitzGeneration
