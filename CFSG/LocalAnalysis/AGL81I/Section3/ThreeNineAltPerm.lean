module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Perm

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.AltPerm

open Equiv Equiv.Perm MulAction GL83 GL83.PiGen

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] [DecidableEq Ω] in
theorem reflTransGen_of_saturated {ι : Type*} (S : ι → Set Ω) (hne : ∀ i, (S i).Nonempty)
    (hsat : ∀ U : Set Ω, (∀ i, S i ⊆ U ∨ S i ⊆ Uᶜ) → (∃ i, S i ⊆ U) → (∃ j, S j ⊆ Uᶜ) → False) :
    ∀ i j, Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i j := by
  intro i j
  set C : Set ι := {k | Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i k}
  set U : Set Ω := ⋃ k ∈ C, S k
  have hmem : ∀ k, (S k ∩ U).Nonempty → k ∈ C := by
    rintro k ⟨x, hxk, hxU⟩
    obtain ⟨k', hk', hxk'⟩ := Set.mem_iUnion₂.mp hxU
    exact Relation.ReflTransGen.tail hk' ⟨x, hxk', hxk⟩
  have hsatU : ∀ k, S k ⊆ U ∨ S k ⊆ Uᶜ := by
    intro k
    by_cases hk : k ∈ C
    · exact Or.inl (Set.subset_biUnion_of_mem (u := S) hk)
    · exact Or.inr fun x hxk hxU => hk (hmem k ⟨x, hxk, hxU⟩)
  have hiC : i ∈ C := Relation.ReflTransGen.refl
  by_contra hj
  have hjU : S j ⊆ Uᶜ := by
    rcases hsatU j with h | h
    · obtain ⟨x, hx⟩ := hne j
      exact absurd (hmem j ⟨x, hx, h hx⟩) hj
    · exact h
  exact hsat U hsatU ⟨i, Set.subset_biUnion_of_mem (u := S) hiC⟩ ⟨j, hjU⟩

theorem conj_mem_altOn {S : Set Ω} {τ : Perm Ω} (hτ : τ ∈ altOn S) (σ : Perm Ω) :
    σ * τ * σ⁻¹ ∈ altOn (σ '' S) := by
  rw [mem_altOn] at hτ ⊢
  refine ⟨(alternatingGroup.normal (α := Ω)).conj_mem τ hτ.1 σ, fun x hx => ?_⟩
  have hx' : σ⁻¹ x ∉ S := fun h => hx ⟨σ⁻¹ x, h, by simp⟩
  rw [Perm.mul_apply, Perm.mul_apply, hτ.2 _ hx']
  simp

theorem altOn_image_le {G : Subgroup (Perm Ω)} {S : Set Ω} {σ : Perm Ω} (hσ : σ ∈ G)
    (hS : altOn S ≤ G) : altOn (σ '' S) ≤ G := by
  intro τ hτ
  have h1 := conj_mem_altOn hτ σ⁻¹
  have hSS : (σ⁻¹ : Perm Ω) '' (σ '' S) = S := by
    ext x
    simp
  rw [hSS] at h1
  have h2 := G.mul_mem (G.mul_mem hσ (hS h1)) (G.inv_mem hσ)
  simpa [mul_assoc] using h2

theorem commute_of_mem_altOn_fixed {r τ : Perm Ω} (hτ : τ ∈ altOn {y | r y = y}) :
    τ * r = r * τ := by
  rw [mem_altOn] at hτ
  ext y
  simp only [Perm.mul_apply]
  by_cases hy : r y = y
  · have hτy : r (τ y) = τ y := by
      by_contra hne
      have h1 : τ (τ y) = τ y := hτ.2 (τ y) hne
      have h2 : τ y = y := τ.injective h1
      exact hne (by rw [h2]; exact hy)
    rw [hy, hτy]
  · have hry : r (r y) ≠ r y := fun h => hy (r.injective h)
    rw [hτ.2 y hy, hτ.2 (r y) hry]

theorem altOn_fixed_le_of_centralizer {G : Subgroup (Perm Ω)} {r : Perm Ω}
    (hr : ∀ τ ∈ alternatingGroup Ω, τ * r = r * τ → τ ∈ G) : altOn {y | r y = y} ≤ G :=
  fun τ hτ => hr τ (mem_altOn.mp hτ).1 (commute_of_mem_altOn_fixed hτ)

theorem fixed_of_image_eq {σ : Perm Ω} (hσ : σ.IsCycle) {W : Set Ω} (hW : σ '' W = W)
    (hcard : W.ncard < σ.support.card) {x : Ω} (hxW : x ∈ W) : σ x = x := by
  by_contra hx
  have hpow : ∀ n : ℕ, (σ ^ n) x ∈ W := by
    intro n
    induction n with
    | zero => simpa using hxW
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      exact hW ▸ Set.mem_image_of_mem σ ih
  have hsub : (σ.support : Set Ω) ⊆ W := by
    intro y hy
    obtain ⟨i, -, hi⟩ := (hσ.sameCycle hx (Perm.mem_support.mp hy)).exists_pow_eq'
    exact hi ▸ hpow i
  have h := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset] at h
  omega

omit [Fintype Ω] [DecidableEq Ω] in
theorem ncard_image_perm (σ : Perm Ω) (S : Set Ω) : (σ '' S).ncard = S.ncard :=
  Set.ncard_image_of_injective S σ.injective

omit [Fintype Ω] [DecidableEq Ω] in
theorem orbit_subset_fixed {R : Subgroup (Perm Ω)} (hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    {r : Perm Ω} (hrR : r ∈ R) {ω : Ω} (hrω : r ω = ω) :
    ∀ x ∈ MulAction.orbit R ω, r x = x := by
  rintro x ⟨g, rfl⟩
  have h := hRcomm r hrR g g.2
  change r ((g : Perm Ω) ω) = (g : Perm Ω) ω
  rw [← Perm.mul_apply, h, Perm.mul_apply, hrω]

omit [DecidableEq Ω] in
theorem ncard_fixed_modEq {p : ℕ} [Fact p.Prime] {R : Subgroup (Perm Ω)} (hRp : IsPGroup p R)
    {r : Perm Ω} (hrR : r ∈ R) :
    Nat.card Ω ≡ {x | r x = x}.ncard [MOD p] := by
  have hz : IsPGroup p (Subgroup.zpowers r) := hRp.to_le ((Subgroup.zpowers_le).mpr hrR)
  have h := card_fixSet_modEq hz
  have hfix : fixSet (Subgroup.zpowers r) = {x | r x = x} := by
    ext x
    simp only [fixSet, Set.mem_setOf_eq]
    constructor
    · intro hx
      exact hx r (Subgroup.mem_zpowers r)
    · rintro hx _ ⟨k, rfl⟩
      exact (Perm.zpow_apply_eq_self_of_apply_eq_self hx k)
  rw [hfix, Nat.card_coe_set_eq] at h
  exact h

theorem alternatingGroup_le_of_family {ι : Type*} [Nonempty Ω] {G : Subgroup (Perm Ω)}
    (T : ι → Set Ω) (hT3 : ∀ i, 3 ≤ (T i).ncard) (hTG : ∀ i, altOn (T i) ≤ G)
    (hcover : ∀ x, ∃ i, x ∈ T i)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => (T a ∩ T b).Nonempty) i j) :
    alternatingGroup Ω ≤ G := by
  have hcov : (⋃ i, T i) = Set.univ :=
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr (hcover x)
  rw [← iSup_altOn_eq_alternatingGroup hT3 hcov hconn]
  exact iSup_le hTG

theorem alternatingGroup_le_of_plane_of_isCycle_of_orbit {p d : ℕ} [hpf : Fact p.Prime]
    (hp3 : 3 ≤ p) (hd : d.Prime) (hdp : d ≠ p)
    (hn : Fintype.card Ω = 2 * p ∨ Fintype.card Ω = 3 * p)
    {G R : Subgroup (Perm Ω)} (hRp : IsPGroup p R) (hRc : Nat.card R = p ^ 2)
    (hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hnreg : ∀ ω : Ω, Nat.card (orbit R ω) ≠ p ^ 2)
    (hRG : ∀ r ∈ R, r ≠ 1 → altOn {x | r x = x} ≤ G)
    {σ : Perm Ω} (hσc : σ.IsCycle) (hσd : σ.support.card = d) (hσG : σ ∈ G)
    (hσfix : altOn {x | σ x = x} ≤ G) :
    alternatingGroup Ω ≤ G := by
  have hp := hpf.out
  have hcardΩ : Nat.card Ω = Fintype.card Ω := Nat.card_eq_fintype_card
  have hn5 : 5 ≤ Fintype.card Ω := by rcases hn with h | h <;> omega
  have : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
  have horb : ∀ ω : Ω, Nat.card (orbit R ω) = 1 ∨ Nat.card (orbit R ω) = p := by
    intro ω
    have hdvd : Nat.card (orbit R ω) ∣ p ^ 2 :=
      (Dvd.intro _ (card_mul_card_stabIn R ω).symm).trans hRc.dvd
    obtain ⟨i, hi, hiq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    interval_cases i
    · exact Or.inl (by simpa using hiq)
    · exact Or.inr (by simpa using hiq)
    · exact absurd hiq (hnreg ω)
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
  set S : Ω → Set Ω := fun ω => {x | r ω x = x}
  have hSω : ∀ ω, ω ∈ S ω := fun ω => hrω ω
  have hSorb : ∀ ω, ∀ x ∈ orbit R ω, x ∈ S ω := fun ω => orbit_subset_fixed hRcomm (hrR ω) (hrω ω)
  have hSG : ∀ ω, altOn (S ω) ≤ G := fun ω => hRG _ (hrR ω) (hr1 ω)
  have hS3 : ∀ ω, 3 ≤ (S ω).ncard := by
    intro ω
    have hmod : Nat.card Ω ≡ (S ω).ncard [MOD p] := ncard_fixed_modEq hRp (hrR ω)
    have hpos : 0 < (S ω).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨ω, hSω ω⟩
    have h0 : Nat.card Ω % p = 0 := by
      rw [hcardΩ]
      rcases hn with h | h <;> rw [h] <;> simp
    have h1 : (S ω).ncard % p = 0 := by
      have := hmod.symm
      unfold Nat.ModEq at this
      omega
    have : p ≤ (S ω).ncard := Nat.le_of_dvd hpos (Nat.dvd_of_mod_eq_zero h1)
    omega
  by_cases hfixR : ∃ ω₀ : Ω, Nat.card (orbit R ω₀) = 1
  ·
    obtain ⟨ω₀, hω₀⟩ := hfixR
    have hω₀fix : ∀ g ∈ R, g ω₀ = ω₀ := by
      intro g hg
      have hsub : Subsingleton (orbit R ω₀) := (Nat.card_eq_one_iff_unique.mp hω₀).1
      have hmem : g ω₀ ∈ orbit R ω₀ := ⟨⟨g, hg⟩, rfl⟩
      exact congrArg Subtype.val (Subsingleton.elim (⟨g ω₀, hmem⟩ : orbit R ω₀)
        ⟨ω₀, mem_orbit_self ω₀⟩)
    refine alternatingGroup_le_of_family S hS3 hSG (fun ω => ⟨ω, hSω ω⟩) fun i j => ?_
    exact Relation.ReflTransGen.single ⟨ω₀, hω₀fix _ (hrR i), hω₀fix _ (hrR j)⟩
  push Not at hfixR
  have horbp : ∀ ω, Nat.card (orbit R ω) = p := fun ω => (horb ω).resolve_left (hfixR ω)
  have horbn : ∀ ω, (orbit R ω).ncard = p := fun ω => by
    rw [← Nat.card_coe_set_eq]
    exact horbp ω
  have hsuppn : σ.support.card ≤ Fintype.card Ω := Finset.card_le_univ _
  have hfixσ : {x | σ x = x}.ncard = Fintype.card Ω - d := by
    have hc : {x | σ x = x} = ((σ.support : Set Ω))ᶜ := by
      ext x
      simp [Perm.mem_support]
    rw [hc, Set.ncard_compl, Set.ncard_coe_finset, hσd, hcardΩ]
  rcases Nat.lt_or_gt_of_ne hdp with hdlt | hdgt
  ·
    let T : Option Ω → Set Ω := fun i => i.elim {x | σ x = x} S
    have hmeet : ∀ ω, (S ω ∩ {x | σ x = x}).Nonempty := by
      intro ω
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      have hsub : orbit R ω ⊆ (σ.support : Set Ω) := by
        intro x hx
        rw [Finset.mem_coe, Perm.mem_support]
        intro hσx
        exact (Set.eq_empty_iff_forall_notMem.mp hcon) x ⟨hSorb ω x hx, hσx⟩
      have h := Set.ncard_le_ncard hsub
      rw [Set.ncard_coe_finset, horbn] at h
      omega
    refine alternatingGroup_le_of_family T ?_ ?_ (fun ω => ⟨some ω, hSω ω⟩) ?_
    · rintro (_ | ω)
      · show 3 ≤ {x | σ x = x}.ncard
        rw [hfixσ]
        rcases hn with h | h <;> rw [h] <;> omega
      · exact hS3 ω
    · rintro (_ | ω)
      · exact hσfix
      · exact hSG ω
    · have hadj : ∀ i, Relation.ReflTransGen (fun a b => (T a ∩ T b).Nonempty) i none := by
        rintro (_ | ω)
        · exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.single (hmeet ω)
      have hadj' : ∀ i, Relation.ReflTransGen (fun a b => (T a ∩ T b).Nonempty) none i := by
        rintro (_ | ω)
        · exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.single
            (show ({x | σ x = x} ∩ S ω).Nonempty by rw [Set.inter_comm]; exact hmeet ω)
      intro i j
      exact (hadj i).trans (hadj' j)
  ·
    let T : (Ω × ℕ) ⊕ PLift (3 ≤ {x | σ x = x}.ncard) → Set Ω :=
      Sum.elim (fun q => (⇑(σ ^ q.2)) '' (S q.1)) (fun _ => {x | σ x = x})
    have hT3 : ∀ i, 3 ≤ (T i).ncard := by
      rintro (⟨ω, m⟩ | h3)
      · show 3 ≤ (⇑(σ ^ m) '' S ω).ncard
        rw [ncard_image_perm]
        exact hS3 ω
      · exact h3.down
    have hTG : ∀ i, altOn (T i) ≤ G := by
      rintro (⟨ω, m⟩ | _)
      · exact altOn_image_le (G.pow_mem hσG m) (hSG ω)
      · exact hσfix
    have hord : σ ^ d = 1 := by
      rw [← hσd, ← hσc.orderOf]
      exact pow_orderOf_eq_one σ
    refine alternatingGroup_le_of_family T hT3 hTG (fun ω => ⟨Sum.inl (ω, 0), by simpa [T] using hSω ω⟩) ?_
    refine reflTransGen_of_saturated T (fun i => Set.nonempty_of_ncard_ne_zero
      (by have := hT3 i; omega)) ?_
    rintro U hsat ⟨i, hiU⟩ ⟨j, hjU⟩
    have hU : ∀ x, x ∈ U → orbit R x ⊆ U := by
      intro x hx
      rcases hsat (Sum.inl (x, 0)) with h | h
      · exact fun y hy => h (by simpa [T] using hSorb x y hy)
      · exact absurd hx (h (by simpa [T] using hSω x))
    have hUc : ∀ x, x ∈ Uᶜ → orbit R x ⊆ Uᶜ := by
      intro x hx
      rcases hsat (Sum.inl (x, 0)) with h | h
      · exact absurd (h (by simpa [T] using hSω x)) hx
      · exact fun y hy => h (by simpa [T] using hSorb x y hy)
    obtain ⟨W, hWsat, hWorb, hWlt, hWne⟩ : ∃ W : Set Ω, (∀ i, T i ⊆ W ∨ T i ⊆ Wᶜ) ∧
        (∀ x, x ∈ W → orbit R x ⊆ W) ∧ W.ncard < 2 * p ∧ W.Nonempty := by
      have hsum : U.ncard + Uᶜ.ncard = Fintype.card Ω := by
        rw [← Set.ncard_union_eq disjoint_compl_right, Set.union_compl_self, Set.ncard_univ,
          hcardΩ]
      have hUne : U.Nonempty := (Set.nonempty_of_ncard_ne_zero
        (by have := hT3 i; omega)).mono hiU
      have hUcne : Uᶜ.Nonempty := (Set.nonempty_of_ncard_ne_zero
        (by have := hT3 j; omega)).mono hjU
      by_cases hle : U.ncard ≤ Uᶜ.ncard
      · refine ⟨U, hsat, hU, ?_, hUne⟩
        rcases hn with h | h <;> omega
      · refine ⟨Uᶜ, fun k => ?_, hUc, ?_, hUcne⟩
        · rcases hsat k with h | h
          · exact Or.inr (by rwa [compl_compl])
          · exact Or.inl h
        · rcases hn with h | h <;> omega
    obtain ⟨ω₁, hω₁⟩ := hWne
    have hWeq : W = orbit R ω₁ := by
      refine le_antisymm (fun x hx => ?_) (hWorb ω₁ hω₁)
      by_contra hxo
      have hdisj : Disjoint (orbit R x) (orbit R ω₁) := by
        rw [Set.disjoint_left]
        intro y hyx hyω
        apply hxo
        have h1 : orbit R y = orbit R x := MulAction.orbit_eq_iff.mpr hyx
        have h2 : orbit R y = orbit R ω₁ := MulAction.orbit_eq_iff.mpr hyω
        rw [← h2, h1]
        exact mem_orbit_self x
      have hsub : orbit R x ∪ orbit R ω₁ ⊆ W :=
        Set.union_subset (hWorb x hx) (hWorb ω₁ hω₁)
      have h := Set.ncard_le_ncard hsub
      rw [Set.ncard_union_eq hdisj, horbn, horbn] at h
      omega
    have hWn : W.ncard = p := by rw [hWeq, horbn]
    have hSW : S ω₁ = W := by
      refine le_antisymm ?_ (fun x hx => hSorb ω₁ x (hWeq ▸ hx))
      rcases hWsat (Sum.inl (ω₁, 0)) with h | h
      · simpa [T] using h
      · exact absurd hω₁ (h (by simpa [T] using hSω ω₁))
    have hV : ∀ m : ℕ, ⇑(σ ^ m) '' W ⊆ W ∨ ⇑(σ ^ m) '' W ⊆ Wᶜ := fun m => by
      have h := hWsat (Sum.inl (ω₁, m))
      simp only [T, Sum.elim_inl] at h
      rwa [hSW] at h
    have hVn : ∀ m : ℕ, (⇑(σ ^ m) '' W).ncard = p := fun m => by rw [ncard_image_perm, hWn]
    have hσW : ⇑σ '' W = W := by
      by_contra hne
      have hk : ∀ k : ℕ, 0 < k → k < d → ⇑(σ ^ k) '' W ⊆ Wᶜ := by
        intro k hk0 hkd
        rcases hV k with h | h
        · exfalso
          have heq : ⇑(σ ^ k) '' W = W := Set.eq_of_subset_of_ncard_le h (by rw [hVn, hWn])
          have hcop : Nat.Coprime k d :=
            ((Nat.Prime.coprime_iff_not_dvd hd).mpr
              (fun hdk => by have := Nat.le_of_dvd hk0 hdk; omega)).symm
          obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hd.one_lt
          have hσk : (σ ^ k) ^ t = σ := by
            rw [← pow_mul, ← Nat.mod_add_div (k * t) d, ht, pow_add, pow_mul, hord, one_pow,
              mul_one, pow_one]
          have hiter : ∀ s : ℕ, ⇑((σ ^ k) ^ s) '' W = W := by
            intro s
            induction s with
            | zero => simp
            | succ s ih => rw [pow_succ', Perm.coe_mul, Set.image_comp, ih, heq]
          exact hne (by rw [← hσk]; exact hiter t)
        · exact h
      have hdisj : ∀ a b : ℕ, a < b → b < d →
          Disjoint (⇑(σ ^ a) '' W) (⇑(σ ^ b) '' W) := by
        intro a b hab hbd
        have hba := hk (b - a) (by omega) (by omega)
        rw [Set.disjoint_left]
        rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
        have hy' : (σ ^ (b - a)) y = x := by
          apply (σ ^ a).injective
          rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le, hxy]
        exact hba ⟨y, hy, hy'⟩ hx
      have h01 := hdisj 0 1 (by omega) (by omega)
      have h012 : Disjoint (⇑(σ ^ 0) '' W ∪ ⇑(σ ^ 1) '' W) (⇑(σ ^ 2) '' W) :=
        Set.disjoint_union_left.mpr ⟨hdisj 0 2 (by omega) (by omega),
          hdisj 1 2 (by omega) (by omega)⟩
      have h0123 : Disjoint (⇑(σ ^ 0) '' W ∪ ⇑(σ ^ 1) '' W ∪ ⇑(σ ^ 2) '' W)
          (⇑(σ ^ 3) '' W) :=
        Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr
          ⟨hdisj 0 3 (by omega) (by omega), hdisj 1 3 (by omega) (by omega)⟩,
          hdisj 2 3 (by omega) (by omega)⟩
      have hunion : (⇑(σ ^ 0) '' W ∪ ⇑(σ ^ 1) '' W ∪ ⇑(σ ^ 2) '' W ∪
          ⇑(σ ^ 3) '' W).ncard = 4 * p := by
        rw [Set.ncard_union_eq h0123, Set.ncard_union_eq h012, Set.ncard_union_eq h01, hVn, hVn,
          hVn, hVn]
        ring
      have hle : (⇑(σ ^ 0) '' W ∪ ⇑(σ ^ 1) '' W ∪ ⇑(σ ^ 2) '' W ∪
          ⇑(σ ^ 3) '' W).ncard ≤ Fintype.card Ω := by
        rw [← hcardΩ, ← Set.ncard_univ]
        exact Set.ncard_le_ncard (Set.subset_univ _)
      rcases hn with h | h <;> omega
    have hWfix : W ⊆ {x | σ x = x} := fun x hx =>
      fixed_of_image_eq hσc hσW (by rw [hWn, hσd]; omega) hx
    have h3 : 3 ≤ {x | σ x = x}.ncard := by
      have := Set.ncard_le_ncard hWfix
      omega
    have hfixW : {x | σ x = x} ⊆ W := by
      rcases hWsat (Sum.inr ⟨h3⟩) with h | h
      · exact h
      · exact absurd hω₁ (h (hWfix hω₁))
    have hfixeq : {x | σ x = x}.ncard = p := by
      rw [Set.Subset.antisymm hfixW hWfix, hWn]
    rw [hfixσ] at hfixeq
    rcases hn with h | h
    · omega
    · have h2p : d = 2 * p := by omega
      rcases hd.eq_one_or_self_of_dvd 2 (h2p ▸ dvd_mul_right 2 p) with h2 | h2 <;> omega

theorem alternatingGroup_le_of_plane_of_isCycle {p d : ℕ} [hpf : Fact p.Prime] (hp5 : 5 ≤ p)
    (hd : d.Prime) (hdp : d ≠ p)
    (hn : Fintype.card Ω = 2 * p ∨ Fintype.card Ω = 3 * p)
    {G R : Subgroup (Perm Ω)} (hRp : IsPGroup p R) (hRc : Nat.card R = p ^ 2)
    (hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hRG : ∀ r ∈ R, r ≠ 1 → altOn {x | r x = x} ≤ G)
    {σ : Perm Ω} (hσc : σ.IsCycle) (hσd : σ.support.card = d) (hσG : σ ∈ G)
    (hσfix : altOn {x | σ x = x} ≤ G) :
    alternatingGroup Ω ≤ G := by
  have hnlt : Fintype.card Ω < p ^ 2 := by
    rcases hn with h | h <;> rw [h] <;> nlinarith
  refine alternatingGroup_le_of_plane_of_isCycle_of_orbit (by omega) hd hdp hn hRp hRc hRcomm
    (fun ω h2 => ?_) hRG hσc hσd hσG hσfix
  have hle : Nat.card (orbit R ω) ≤ Fintype.card Ω := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective (Subtype.val : orbit R ω → Ω) Subtype.val_injective
  omega

end CFSG.LocalAnalysis.AGL81I.Section3.AltPerm
