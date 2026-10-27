module

public import CFSG.LieType.Steinberg.BruhatTwistBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LieOut

section K

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem commute_neg_single_single (hext : SteinbergExtras D n H) {j k : Fin D.rank} (hjk : j ≠ k)
    {b c : K} (hb : b ∈ D.rootGroup (-Pi.single j 1)) (hc : c ∈ D.rootGroup (Pi.single k 1)) :
    b * c = c * b := by
  have hαj : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
  have hαk : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k
  have hαj' : (-Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hαj
  have hind : LinIndepPair (-Pi.single j 1 : Fin D.rank → ℤ) (Pi.single k 1) := by
    intro a b' hab
    have h1 := congrFun hab j
    have h2 := congrFun hab k
    simp [Pi.single_apply, hjk, hjk.symm] at h1 h2
    exact ⟨h1, h2⟩
  have hc' := hext.commutator_mem _ hαj' _ hαk hind b hb c hc
  have hempty : (⨆ ε ∈ openCone D.roots (-Pi.single j 1) (Pi.single k 1), D.rootGroup ε) = ⊥ := by
    refine iSup₂_eq_bot.2 fun ε hε => ?_
    exfalso
    obtain ⟨hεr, a, b', ha, hb', rfl⟩ := hε
    rcases (RootSystem.ofCartan D.isFiniteType D.divisible).sign _ hεr with h | h
    · have := h j
      simp [Pi.single_apply, hjk, hjk.symm] at this
      omega
    · have := h k
      simp [Pi.single_apply, hjk, hjk.symm] at this
      omega
  rw [hempty, Subgroup.mem_bot, commutatorElement_def] at hc'
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hc')

theorem list_prod_map_ite {ι : Type*} [DecidableEq ι] {L : List ι} (hL : L.Nodup) {a : ι}
    (ha : a ∈ L) (u : K) : (L.map fun δ => if δ = a then u else 1).prod = u := by
  induction L with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons x t ih =>
    rw [List.nodup_cons] at hL
    simp only [List.map_cons, List.prod_cons]
    by_cases hx : x = a
    · subst hx
      have : (t.map fun δ => if δ = x then u else 1).prod = 1 := by
        refine List.prod_eq_one fun y hy => ?_
        obtain ⟨δ, hδ, rfl⟩ := List.mem_map.1 hy
        have : δ ≠ x := fun e => hL.1 (e ▸ hδ)
        simp [this]
      simp [this]
    · have ha' : a ∈ t := by
        rcases List.mem_cons.1 ha with h | h
        · exact absurd h.symm hx
        · exact h
      simp [hx, ih hL.2 ha']

theorem rootGroup_inf_eq_bot (hext : SteinbergExtras D n H) {γ γ' : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hγ' : γ' ∈ D.roots)
    (hp : 0 < ht γ) (hp' : 0 < ht γ') (hd : ∀ δ ∈ D.roots, γ ≠ 2 • δ)
    (hd' : ∀ δ ∈ D.roots, γ' ≠ 2 • δ) (hne : γ ≠ γ') :
    D.rootGroup γ ⊓ D.rootGroup γ' = ⊥ := by
  classical
  have hfin : {γ : Fin D.rank → ℤ | γ ∈ D.roots ∧ 0 < ht γ ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ}.Finite :=
    ((RootSystem.ofCartan D.isFiniteType D.divisible).finite_roots).subset fun x hx => hx.1
  obtain ⟨L, hnd, hmem, hsort⟩ := exists_nodup_sorted hfin (fun γ => ht γ)
  have hL := hext.prodInjective_pos L hnd (fun γ => by
    rw [hmem]; rfl) hsort
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
  have hγL : γ ∈ L := (hmem γ).2 ⟨hγ, hp, hd⟩
  have hγL' : γ' ∈ L := (hmem γ').2 ⟨hγ', hp', hd'⟩
  have h := hL (fun δ => if δ = γ then u else 1) (fun δ => if δ = γ' then u else 1)
    (fun δ _ => by
      by_cases h : δ = γ
      · simp [h, hu1]
      · simp [h, one_mem])
    (fun δ _ => by
      by_cases h : δ = γ'
      · simp [h, hu2]
      · simp [h, one_mem])
    (by rw [list_prod_map_ite hnd hγL, list_prod_map_ite hnd hγL']) γ hγL
  simp only [if_true, hne, if_false] at h
  exact Subgroup.mem_bot.2 h

end K

section K2

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

include hct hext in
theorem exists_not_commute_of_cartan_ne_zero {j k : Fin D.rank} (hne : j ≠ k)
    (hjk : D.cartan j k ≠ 0) :
    ∃ a ∈ D.rootGroup (Pi.single j 1), ∃ c ∈ D.rootGroup (Pi.single k 1), a * c ≠ c * a := by
  classical
  by_contra hcon
  push Not at hcon
  have hαk : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k
  set C : Subgroup K := Subgroup.centralizer (D.rootGroup (Pi.single k 1) : Set K) with hC
  have hX1 : D.rootGroup (Pi.single j 1) ≤ C := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun c hc => (hcon a ha c hc).symm
  have hX2 : D.rootGroup (-Pi.single j 1) ≤ C := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun c hc => (commute_neg_single_single hext hne hb hc).symm
  have hn : n j ∈ C := (sup_le hX1 hX2 : rankOne D.rootGroup j ≤ C) (hct.n_mem j)
  set γ' : Fin D.rank → ℤ :=
    weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j)
      (Pi.single k 1) with hγ'
  have hγ'r : γ' ∈ D.roots := weylAction_mem_roots D.isFiniteType _ hαk
  have hγ'k : γ' k = 1 := by
    rw [hγ', weylAction_simple, reflection_apply_of_ne _ hne.symm]
    simp
  have hγ'j : γ' j = - D.cartan j k := by
    rw [hγ', weylAction_simple, reflection_apply]
    simp [Pi.single_apply, hne]
  have hpos : 0 < ht γ' := ht_pos_of_coord hγ'r (j := k) (by omega)
  have hdiv : ∀ (γ : Fin D.rank → ℤ), γ k = 1 → ∀ δ ∈ D.roots, γ ≠ 2 • δ := by
    intro γ hγ δ _ h
    have := congrFun h k
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at this
    omega
  have hinf := rootGroup_inf_eq_bot hext hαk hγ'r (ht_single_pos k) hpos
    (hdiv (Pi.single k 1) (by simp)) (hdiv _ hγ'k) (fun e => by
      have := congrFun e j
      simp [Pi.single_apply, hne, hγ'j] at this
      exact hjk this)
  apply hext.ne_bot _ hαk
  rw [eq_bot_iff, ← hinf]
  intro c hc
  refine Subgroup.mem_inf.2 ⟨hc, ?_⟩
  have h1 := (actsAs_n hct j).conj_mem hαk hc
  have h2 : n j * c * (n j)⁻¹ = c := by
    have := Subgroup.mem_centralizer_iff.1 hn c hc
    rw [← this]; group
  rwa [h2] at h1

include hct hext in
theorem rootGroup_le_iSup_rankOne {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    D.rootGroup γ ≤ ⨆ i, rankOne D.rootGroup i := by
  set Λ : Subgroup K := ⨆ i, rankOne D.rootGroup i with hΛ
  have hweyl : weylN n H ≤ Λ := by
    refine sup_le (iSup_le fun i => (hct.H_le i).trans (le_iSup _ i)) ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact le_iSup (fun i => rankOne D.rootGroup i) i (hct.n_mem i)
  have hroot : ∀ (w : (coxeterMatrix D.isFiniteType).Group) (i : Fin D.rank),
      D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1)) ≤ Λ := by
    intro w i
    have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
      (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
    rw [← (actsAs_nrep hct w) _ hα]
    rintro _ ⟨x, hx, rfl⟩
    have hxΛ : x ∈ Λ := le_iSup (fun i => rankOne D.rootGroup i) i
      (le_sup_left (a := D.rootGroup (Pi.single i 1)) hx)
    have hnΛ : nrep hct w ∈ Λ := hweyl (nrep_mem_weylN hct w)
    exact Λ.mul_mem (Λ.mul_mem hnΛ hxΛ) (Λ.inv_mem hnΛ)
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · exact hroot w i
  · have h1 : weylAction D.isFiniteType w (Pi.single i 1) ∈ D.roots := Or.inl ⟨w, i, rfl⟩
    have h2 : (2 : ℕ) • weylAction D.isFiniteType w (Pi.single i 1) ∈ D.roots :=
      Or.inr ⟨w, i, hi, rfl⟩
    exact (hext.two_smul_le _ h1 h2).trans (hroot w i)

include hct hext in
theorem iSup_rankOne_eq_top : (⨆ i, rankOne D.rootGroup i) = ⊤ := by
  rw [eq_top_iff, ← hct.iSup_eq_top]
  exact iSup₂_le fun γ hγ => rootGroup_le_iSup_rankOne hct hext hγ

end K2

section BQ

variable {K : Type*} {S : Type*} [Group K] [Finite K] [Group S] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* S} {M : ℕ}

theorem rootGroup_not_le_ker (h : BorelQuotient D n H π M) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) : ¬ D.rootGroup γ ≤ π.ker := by
  intro hle
  apply h.extras.ne_bot γ hγ
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := h.pGroup γ hγ ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hM := h.ker_pow _ (hle hx)
  have hcop : Nat.Coprime (2 ^ k) M := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 h.odd)
  have h1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hM)
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h1)

theorem exists_adj_of_proper (h : BorelQuotient D n H π M) (hS : IsSimpleGroup S)
    (hZ : Subgroup.center S = ⊥) {J : Set (Fin D.rank)} (hJ : J.Nonempty)
    (hJc : ∃ k, k ∉ J) : ∃ j ∈ J, ∃ k, k ∉ J ∧ D.cartan j k ≠ 0 := by
  by_contra hno
  push Not at hno
  obtain ⟨j₀, hj₀⟩ := hJ
  obtain ⟨k₀, hk₀⟩ := hJc
  set ΛJ : Subgroup K := ⨆ j ∈ J, rankOne D.rootGroup j with hΛJ
  set ΛC : Subgroup K := ⨆ k ∈ {k | k ∉ J}, rankOne D.rootGroup k with hΛC
  have hc1 : ∀ j ∈ J, ∀ k, k ∉ J → Commutes (rankOne D.rootGroup j) (rankOne D.rootGroup k) :=
    fun j hj k hk => commutes_rankOne_of_cartan_eq_zero h.extras (fun e => hk (e ▸ hj))
      (hno j hj k hk)
  have hc2 : ∀ j ∈ J, rankOne D.rootGroup j ≤ Subgroup.centralizer (ΛC : Set K) := by
    intro j hj
    rw [← commutes_iff_le_centralizer]
    refine Commutes.symm ?_
    rw [commutes_iff_le_centralizer]
    refine iSup₂_le fun k hk => ?_
    rw [← commutes_iff_le_centralizer]
    exact (hc1 j hj k hk).symm
  have hc3 : ΛJ ≤ Subgroup.centralizer (ΛC : Set K) := iSup₂_le hc2
  have htop : ΛJ ⊔ ΛC = ⊤ := by
    have h1 : (⨆ i, rankOne D.rootGroup i) ≤ ΛJ ⊔ ΛC := by
      refine iSup_le fun i => ?_
      by_cases hi : i ∈ J
      · exact le_sup_of_le_left (le_iSup₂ (f := fun j (_ : j ∈ J) => rankOne D.rootGroup j) i hi)
      · exact le_sup_of_le_right
          (le_iSup₂ (f := fun k (_ : k ∈ {k | k ∉ J}) => rankOne D.rootGroup k) i hi)
    rw [eq_top_iff, ← iSup_rankOne_eq_top h.ct h.extras]
    exact h1
  have hnormal : ΛJ.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer
      ((commutes_iff_le_centralizer.1 (commutes_iff_le_centralizer.2 hc3).symm).trans
        (Subgroup.centralizer_le_normalizer _))
  have hα : ∀ i : Fin D.rank, (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := fun i =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hXle : ∀ i : Fin D.rank, D.rootGroup (Pi.single i 1) ≤ rankOne D.rootGroup i :=
    fun i => le_sup_left
  haveI : (ΛJ.map π).Normal := hnormal.map π h.surj
  rcases hS.eq_bot_or_eq_top_of_normal (ΛJ.map π) with hbot | htop'
  · apply rootGroup_not_le_ker h (hα j₀)
    have : ΛJ ≤ π.ker := (Subgroup.map_eq_bot_iff ΛJ).1 hbot
    exact (hXle j₀).trans ((le_iSup₂ (f := fun j (_ : j ∈ J) => rankOne D.rootGroup j) j₀ hj₀).trans
      this)
  · apply rootGroup_not_le_ker h (hα k₀)
    have hΛC : ΛC ≤ π.ker := by
      intro g hg
      rw [MonoidHom.mem_ker]
      have : π g ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro s
        have hs : s ∈ ΛJ.map π := by rw [htop']; trivial
        obtain ⟨x, hx, rfl⟩ := hs
        have := (commutes_iff_le_centralizer.2 hc3).symm g hg x hx
        rw [← map_mul, ← map_mul, this]
      rw [hZ] at this
      exact Subgroup.mem_bot.1 this
    exact (hXle k₀).trans ((le_iSup₂ (f := fun k (_ : k ∈ {k | k ∉ J}) => rankOne D.rootGroup k)
      k₀ hk₀).trans hΛC)

end BQ

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
