module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineAltPerm
public import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Alt

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.AltPerm

open Equiv Equiv.Perm MulAction GL83 GL83.PiGen

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] [DecidableEq Ω] in
theorem reflTransGen_of_meets {ι : Type*} (S : ι → Set Ω) (T : Set Ω)
    (hmeet : ∀ i, (S i ∩ T).Nonempty) (hpair : ∀ x ∈ T, ∀ y ∈ T, ∃ k, x ∈ S k ∧ y ∈ S k) :
    ∀ i j, Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i j := by
  intro i j
  obtain ⟨x, hxi, hxT⟩ := hmeet i
  obtain ⟨y, hyj, hyT⟩ := hmeet j
  obtain ⟨k, hxk, hyk⟩ := hpair x hxT y hyT
  exact (Relation.ReflTransGen.single ⟨x, hxi, hxk⟩).tail ⟨y, hyk, hyj⟩

theorem card_support_cycleOf_of_pow_three {s : Perm Ω} (hs : s ^ 3 = 1) {x : Ω} (hx : s x ≠ x) :
    (s.cycleOf x).support.card = 3 := by
  have hc : (s.cycleOf x).IsCycle := isCycle_cycleOf s hx
  have h1 : orderOf (s.cycleOf x) ∣ 3 :=
    (orderOf_cycleOf_dvd_orderOf s x).trans (orderOf_dvd_of_pow_eq_one hs)
  rw [hc.orderOf] at h1
  rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h2 | h2
  · have := hc.two_le_card_support
    omega
  · exact h2

theorem altOn_support_le_zpowers {c : Perm Ω} (hc : c.support.card = 3) :
    altOn (c.support : Set Ω) ≤ Subgroup.zpowers c := by
  have h3 : c.IsThreeCycle := card_support_eq_three_iff.mp hc
  have hmem : c ∈ altOn (c.support : Set Ω) := by
    refine mem_altOn.2 ⟨h3.mem_alternatingGroup, fun x hx => ?_⟩
    by_contra hne
    exact hx (Finset.mem_coe.2 (Perm.mem_support.2 hne))
  have hle : Subgroup.zpowers c ≤ altOn (c.support : Set Ω) := Subgroup.zpowers_le.2 hmem
  have : Nontrivial ↥c.support := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe, hc]
    norm_num
  have hcard : Nat.card (altOn (c.support : Set Ω)) ≤ Nat.card (Subgroup.zpowers c) := by
    rw [Nat.card_congr (altOnEquiv c.support).toEquiv, Nat.card_zpowers, h3.orderOf,
      Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_coe, hc]
    decide
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).ge

theorem altOn_cycleOf_le {G : Subgroup (Perm Ω)} {s : Perm Ω} (hs : s ^ 3 = 1) {x : Ω}
    (hx : s x ≠ x) (hG : ∀ τ ∈ alternatingGroup Ω, τ * s = s * τ → τ ∈ G) :
    altOn ((s.cycleOf x).support : Set Ω) ≤ G := by
  intro τ hτ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp
    (altOn_support_le_zpowers (card_support_cycleOf_of_pow_three hs hx) hτ)
  have hcomm : Commute (s.cycleOf x) s :=
    self_mem_cycle_factors_commute (cycleOf_mem_cycleFactorsFinset_iff.2 (Perm.mem_support.2 hx))
  exact hG _ (mem_altOn.mp hτ).1 (hcomm.zpow_left k).eq

theorem alternatingGroup_le_of_orbit_of_isCycle {G R : Subgroup (Perm Ω)}
    (hRexp : ∀ r ∈ R, r ^ 3 = 1)
    (hRG : ∀ r ∈ R, r ≠ 1 → ∀ τ ∈ alternatingGroup Ω, τ * r = r * τ → τ ∈ G)
    (x₀ : Ω) (hT2 : 2 ≤ (orbit R x₀).ncard) (hTc : (orbit R x₀)ᶜ.ncard < 3)
    {σ : Perm Ω} (hσc : σ.IsCycle) (hσG : σ ∈ G) (hσfix : altOn {x | σ x = x} ≤ G)
    (hσs : (orbit R x₀)ᶜ.ncard < σ.support.card)
    (hfix : ∀ x, x ∉ orbit R x₀ → σ x = x → 3 ≤ {x | σ x = x}.ncard) :
    alternatingGroup Ω ≤ G := by
  set T := orbit R x₀ with hTdef
  have : Nonempty Ω := ⟨x₀⟩
  let ι := {q : Ω × Ω // q.1 ∈ T ∧ q.2 ∈ T ∧ q.1 ≠ q.2}
  have hmove : ∀ q : ι, ∃ s ∈ R, s q.1.1 = q.1.2 := by
    rintro ⟨⟨x, y⟩, hx, hy, -⟩
    have hy' : y ∈ orbit R x := by
      rw [MulAction.orbit_eq_iff.mpr hx]
      exact hy
    obtain ⟨⟨s, hs⟩, hsx⟩ := hy'
    exact ⟨s, hs, hsx⟩
  choose s hsR hsq using hmove
  have hsx : ∀ q : ι, s q q.1.1 ≠ q.1.1 := fun q => by
    rw [hsq q]
    exact q.2.2.2.symm
  have hs1 : ∀ q : ι, s q ≠ 1 := fun q h1 => hsx q (by rw [h1]; rfl)
  let L : ι → Set Ω := fun q => ((s q).cycleOf q.1.1).support
  have hL3 : ∀ q, (L q).ncard = 3 := fun q => by
    simp only [L, Set.ncard_coe_finset]
    exact card_support_cycleOf_of_pow_three (hRexp _ (hsR q)) (hsx q)
  have hLG : ∀ q, altOn (L q) ≤ G := fun q =>
    altOn_cycleOf_le (hRexp _ (hsR q)) (hsx q) (hRG _ (hsR q) (hs1 q))
  have hL1 : ∀ q : ι, q.1.1 ∈ L q := fun q => by
    simp only [L, Finset.mem_coe]
    exact (mem_support_cycleOf_iff' (hsx q)).2 (SameCycle.refl _ _)
  have hL2 : ∀ q : ι, q.1.2 ∈ L q := fun q => by
    simp only [L, Finset.mem_coe]
    rw [mem_support_cycleOf_iff' (hsx q), ← hsq q]
    exact sameCycle_apply_right.2 (SameCycle.refl _ _)
  have hline : ∀ x ∈ T, ∃ q : ι, x ∈ L q := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := exists_other hT2 x
    exact ⟨⟨(x, y), hx, hy, hyx.symm⟩, hL1 _⟩
  let F : ι × ℕ ⊕ PLift (3 ≤ {x | σ x = x}.ncard) → Set Ω :=
    Sum.elim (fun a => ⇑(σ ^ a.2) '' L a.1) (fun _ => {x | σ x = x})
  have hF3 : ∀ i, 3 ≤ (F i).ncard := by
    rintro (⟨q, m⟩ | h3)
    · show 3 ≤ (⇑(σ ^ m) '' L q).ncard
      rw [ncard_image_perm, hL3]
    · exact h3.down
  have hFG : ∀ i, altOn (F i) ≤ G := by
    rintro (⟨q, m⟩ | _)
    · exact altOn_image_le (G.pow_mem hσG m) (hLG q)
    · exact hσfix
  have hmeet : ∀ i, (F i ∩ T).Nonempty := by
    intro i
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsub : F i ⊆ Tᶜ := fun x hx hxT =>
      (Set.eq_empty_iff_forall_notMem.mp hcon) x ⟨hx, hxT⟩
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := hF3 i
    omega
  have hcover : ∀ x, ∃ i, x ∈ F i := by
    intro x
    by_cases hxT : x ∈ T
    · obtain ⟨q, hq⟩ := hline x hxT
      exact ⟨Sum.inl (q, 0), by simpa [F] using hq⟩
    by_cases hσx : σ x = x
    · exact ⟨Sum.inr ⟨hfix x hxT hσx⟩, hσx⟩
    obtain ⟨y, hyσ, hyT⟩ : ∃ y ∈ σ.support, y ∈ T := by
      by_contra hcon
      push Not at hcon
      have hsub : (σ.support : Set Ω) ⊆ Tᶜ := fun y hy => hcon y hy
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_coe_finset] at h1
      omega
    obtain ⟨i, -, hi⟩ := (hσc.sameCycle (Perm.mem_support.mp hyσ) hσx).exists_pow_eq'
    obtain ⟨q, hq⟩ := hline y hyT
    exact ⟨Sum.inl (q, i), show x ∈ ⇑(σ ^ i) '' L q from ⟨y, hq, hi⟩⟩
  have hpair : ∀ x ∈ T, ∀ y ∈ T, ∃ k, x ∈ F k ∧ y ∈ F k := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy
      obtain ⟨q, hq⟩ := hline x hx
      exact ⟨Sum.inl (q, 0), by simpa [F] using hq, by simpa [F] using hq⟩
    · exact ⟨Sum.inl (⟨(x, y), hx, hy, hxy⟩, 0), by simpa [F] using hL1 ⟨(x, y), hx, hy, hxy⟩,
        by simpa [F] using hL2 ⟨(x, y), hx, hy, hxy⟩⟩
  exact alternatingGroup_le_of_family F hF3 hFG hcover (reflTransGen_of_meets F T hmeet hpair)

theorem alternatingGroup_le_of_not_dvd_card {p : ℕ} [hpf : Fact p.Prime] (hp3 : 3 ≤ p)
    {G R : Subgroup (Perm Ω)} (hRp : IsPGroup p R) (hRc : Nat.card R = p ^ 2)
    (hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hnreg : ∀ ω : Ω, Nat.card (orbit R ω) ≠ p ^ 2) (hΩ : ¬ p ∣ Fintype.card Ω)
    (hRG : ∀ r ∈ R, r ≠ 1 → altOn {x | r x = x} ≤ G) :
    alternatingGroup Ω ≤ G := by
  have hp := hpf.out
  have horb : ∀ ω : Ω, Nat.card (orbit R ω) = 1 ∨ Nat.card (orbit R ω) = p := by
    intro ω
    have hdvd : Nat.card (orbit R ω) ∣ p ^ 2 :=
      (Dvd.intro _ (card_mul_card_stabIn R ω).symm).trans hRc.dvd
    obtain ⟨i, hi, hiq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    interval_cases i
    · exact Or.inl (by simpa using hiq)
    · exact Or.inr (by simpa using hiq)
    · exact absurd hiq (hnreg ω)
  have hfixed : ∀ x : Ω, Nat.card (orbit R x) = 1 → ∀ g ∈ R, g x = x := by
    intro x h1 g hg
    have hsub : Subsingleton (orbit R x) := (Nat.card_eq_one_iff_unique.mp h1).1
    have hmem : g x ∈ orbit R x := ⟨⟨g, hg⟩, rfl⟩
    exact congrArg Subtype.val (Subsingleton.elim (⟨g x, hmem⟩ : orbit R x)
      ⟨x, mem_orbit_self x⟩)
  obtain ⟨z, hz⟩ : (fixSet R).Nonempty := by
    have h := card_fixSet_modEq (Ω := Ω) hRp
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, Nat.card_coe_set_eq, Set.ncard_empty, Nat.card_eq_fintype_card] at h
    exact hΩ (Nat.modEq_zero_iff_dvd.mp h)
  have hfixer : ∀ ω : Ω, ∃ r ∈ R, r ≠ 1 ∧ r ω = ω := by
    intro ω
    have hst : 1 < Nat.card (stabIn R ω) := by
      have h := card_mul_card_stabIn R ω
      rw [hRc] at h
      rcases horb ω with h1 | h1 <;> rw [h1] at h <;> nlinarith [hp.two_le]
    obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.one_lt_card_iff_ne_bot _).mp hst |>
      Subgroup.ne_bot_iff_exists_ne_one.mp
    refine ⟨r, stabIn_le R ω hr, fun h => hr1 (Subtype.ext h), ?_⟩
    exact mem_fixSet_stabIn R ω r hr
  choose r hrR hr1 hrω using hfixer
  obtain ⟨ω₁, hω₁⟩ : ∃ ω : Ω, Nat.card (orbit R ω) = p := by
    by_contra hcon
    push Not at hcon
    have hR1 : R = ⊥ := (Subgroup.eq_bot_iff_forall R).mpr fun g hg => by
      ext x
      exact hfixed x ((horb x).resolve_right (hcon x)) g hg
    rw [hR1, Subgroup.card_bot] at hRc
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have : Nonempty Ω := ⟨z⟩
  let ι := {ω : Ω // Nat.card (orbit R ω) = p}
  let S : ι → Set Ω := fun ω => {x | r ω.1 x = x}
  have hS3 : ∀ ω : ι, 3 ≤ (S ω).ncard := by
    intro ω
    have hsub : orbit R ω.1 ⊆ S ω := fun x hx =>
      orbit_subset_fixed hRcomm (hrR ω.1) (hrω ω.1) x hx
    have h := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq (orbit R ω.1), ω.2] at h
    omega
  refine alternatingGroup_le_of_family S hS3 (fun ω => hRG _ (hrR ω.1) (hr1 ω.1)) ?_ ?_
  · intro x
    rcases horb x with h1 | h1
    · exact ⟨⟨ω₁, hω₁⟩, hfixed x h1 _ (hrR ω₁)⟩
    · exact ⟨⟨x, h1⟩, hrω x⟩
  · intro i j
    exact Relation.ReflTransGen.single ⟨z, hz _ (hrR i.1), hz _ (hrR j.1)⟩

theorem alternatingGroup_le_nine {d : ℕ} (hd : d.Prime) (hd3 : d ≠ 3) (hΩ : Fintype.card Ω = 9)
    {G R : Subgroup (Perm Ω)} (hRp : IsPGroup 3 R) (hRc : Nat.card R = 3 ^ 2)
    (hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRexp : ∀ r ∈ R, r ^ 3 = 1)
    (hRG : ∀ r ∈ R, r ≠ 1 → ∀ τ ∈ alternatingGroup Ω, τ * r = r * τ → τ ∈ G)
    {σ : Perm Ω} (hσc : σ.IsCycle) (hσd : σ.support.card = d) (hσG : σ ∈ G)
    (hσG' : ∀ τ ∈ alternatingGroup Ω, τ * σ = σ * τ → τ ∈ G) :
    alternatingGroup Ω ≤ G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hreg : ∃ ω : Ω, Nat.card (orbit R ω) = 3 ^ 2
  ·
    obtain ⟨x₀, hx₀⟩ := hreg
    have hTn : (orbit R x₀).ncard = 9 := by
      rw [← Nat.card_coe_set_eq, hx₀]
      norm_num
    have hT : orbit R x₀ = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hΩ, hTn]
    have hTc : (orbit R x₀)ᶜ.ncard = 0 := by
      rw [hT, Set.compl_univ, Set.ncard_empty]
    refine alternatingGroup_le_of_orbit_of_isCycle hRexp hRG x₀ (by omega) (by omega) hσc hσG
      (altOn_fixed_le_of_centralizer hσG') (by rw [hTc, hσd]; exact hd.pos) ?_
    intro x hx
    exact absurd (hT ▸ Set.mem_univ x) hx
  · push Not at hreg
    exact alternatingGroup_le_of_plane_of_isCycle_of_orbit (p := 3) le_rfl hd hd3
      (Or.inr hΩ) hRp hRc hRcomm hreg
      (fun r hr hr1 => altOn_fixed_le_of_centralizer (hRG r hr hr1)) hσc hσd hσG
      (altOn_fixed_le_of_centralizer hσG')

theorem alternatingGroup_le_ten_eleven {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hd3 : d ≠ 3)
    (hΩ : Fintype.card Ω = 10 ∨ Fintype.card Ω = 11)
    {G R : Subgroup (Perm Ω)} (hRp : IsPGroup 3 R) (hRc : Nat.card R = 3 ^ 2)
    (hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRexp : ∀ r ∈ R, r ^ 3 = 1)
    (hRG : ∀ r ∈ R, r ≠ 1 → ∀ τ ∈ alternatingGroup Ω, τ * r = r * τ → τ ∈ G)
    {σ : Perm Ω} (hσc : σ.IsCycle) (hσd : σ.support.card = d) (hσG : σ ∈ G)
    (hσG' : ∀ τ ∈ alternatingGroup Ω, τ * σ = σ * τ → τ ∈ G) :
    alternatingGroup Ω ≤ G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardΩ : Nat.card Ω = Fintype.card Ω := Nat.card_eq_fintype_card
  by_cases hreg : ∃ ω : Ω, Nat.card (orbit R ω) = 3 ^ 2
  ·
    obtain ⟨x₀, hx₀⟩ := hreg
    have hTn : (orbit R x₀).ncard = 9 := by
      rw [← Nat.card_coe_set_eq, hx₀]
      norm_num
    have hTc : (orbit R x₀)ᶜ.ncard = Fintype.card Ω - 9 := by
      rw [Set.ncard_compl, hTn, hcardΩ]
    have hd5 : 5 ≤ d := by
      have := hd.two_le
      by_contra hlt
      interval_cases d
      · exact hd2 rfl
      · exact hd3 rfl
      · exact absurd hd (by norm_num)
    have hfixσ : {x | σ x = x}.ncard = Fintype.card Ω - d := by
      have hc : {x | σ x = x} = ((σ.support : Set Ω))ᶜ := by
        ext x
        simp [Perm.mem_support]
      rw [hc, Set.ncard_compl, Set.ncard_coe_finset, hσd, hcardΩ]
    refine alternatingGroup_le_of_orbit_of_isCycle hRexp hRG x₀ (by omega)
      (by rcases hΩ with h | h <;> omega) hσc hσG (altOn_fixed_le_of_centralizer hσG')
      (by rw [hTc, hσd]; rcases hΩ with h | h <;> omega) ?_
    intro x _ hσx
    have hne : 0 < {x | σ x = x}.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨x, hσx⟩
    rw [hfixσ] at hne ⊢
    have hlt : d < Fintype.card Ω := by omega
    rcases hΩ with h | h
    · rw [h] at hlt ⊢
      interval_cases d <;> first | omega | exact absurd hd (by norm_num)
    · rw [h] at hlt ⊢
      interval_cases d <;> first | omega | exact absurd hd (by norm_num)
  ·
    push Not at hreg
    refine alternatingGroup_le_of_not_dvd_card (p := 3) le_rfl hRp hRc hRcomm hreg ?_
      (fun r hr hr1 => altOn_fixed_le_of_centralizer (hRG r hr hr1))
    rcases hΩ with h | h <;> rw [h] <;> norm_num

end CFSG.LocalAnalysis.AGL81I.Section3.AltPerm
