module

public import CFSG.ClassicalInvolution.Q3.Q3NMProd

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open CFSG.Open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic
open scoped commutatorElement MatrixGroups

structure CompFacts (c : CompData) : Prop where
  finite : Finite c.G
  center_two : IsPGroup 2 (Subgroup.center c.G)
  second_center : ∀ g : c.G, (∀ h : c.G, ⁅g, h⁆ ∈ Subgroup.center c.G) →
    g ∈ Subgroup.center c.G
  normal_top : ∀ M : Subgroup c.G, M.Normal → 24 ∣ Nat.card M → M = ⊤

theorem not_dvd_24_of_isPGroup {H : Type} [Group H] [Finite H] (hp : IsPGroup 2 H) :
    ¬ 24 ∣ Nat.card H := by
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk]
  intro hd
  have h3 : 3 ∣ 2 ^ k := (by norm_num : 3 ∣ 24).trans hd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem sl23_center_sq : ∀ g : SL(2, ZMod 3), (∀ y : SL(2, ZMod 3), y * g = g * y) →
    g * g = 1 := by
  decide +kernel

theorem compFacts_sl23 : CompFacts CompData.sl23 := by
  refine ⟨inferInstanceAs (Finite SL(2, ZMod 3)), ?_, ?_, ?_⟩
  · intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have := sl23_center_sq g (fun y => (Subgroup.mem_center_iff.mp g.2 y))
    simpa [sq] using this
  · intro g hg
    have := sl23_second_center (QuotientGroup.mk' (Subgroup.center SL(2, ZMod 3)))
      (by rw [QuotientGroup.ker_mk']) g (fun h => by
        rw [QuotientGroup.ker_mk']
        exact hg h)
    exact this
  · intro M _ h24
    have h1 : Nat.card M ∣ 24 := natCard_sl2Three ▸ Subgroup.card_subgroup_dvd_card M
    refine Subgroup.eq_top_of_card_eq M ?_
    rw [natCard_sl2Three]
    exact Nat.dvd_antisymm h1 h24

theorem compFacts_m11 (hM : M11Facts) : CompFacts CompData.m11 := by
  have hfin : Finite ↥CFSG.Blueprint.NativeSporadic.M11 :=
    Nat.finite_of_card_ne_zero (by rw [hM.2]; norm_num)
  have hq := isQuasisimple_m11 hM
  have hperf : Group.IsPerfect ↥CFSG.Blueprint.NativeSporadic.M11 := ⟨hq.1⟩
  have hcenter := center_m11_eq_bot hM
  refine ⟨hfin, ?_, fun g hg => mem_center_of_commutator_mem le_rfl hg, ?_⟩
  · intro g
    refine ⟨0, ?_⟩
    apply Subtype.ext
    have h := g.2
    have : (g : ↥CFSG.Blueprint.NativeSporadic.M11) = 1 := by
      have h' : (g : ↥CFSG.Blueprint.NativeSporadic.M11) ∈ (⊥ : Subgroup _) := hcenter ▸ h
      exact h'
    simpa using this
  · intro M hMn h24
    have := hMn
    rcases hM.1.eq_bot_or_eq_top_of_normal M with hbot | htop
    · subst hbot
      rw [Subgroup.card_bot] at h24
      omega
    · exact htop

section Images

variable {ι X : Type} [Group X] {Φ : Set (Subgroup X)}

@[expose, reducible] def compR (D : LieSystemData3 ι X Φ) (i : ι) : Subgroup X := (D.hom i).range

variable (D : LieSystemData3 ι X Φ)

theorem compR_comm {i j : ι} (hij : i ≠ j) {a b : X} (ha : a ∈ compR D i) (hb : b ∈ compR D j) :
    a * b = b * a := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  exact D.commute i j hij u v

theorem compR_conj_mem (i : ι) (g : X) {x : X} (hx : x ∈ compR D i) : g * x * g⁻¹ ∈ compR D i := by
  have hg : g ∈ (⊤ : Subgroup X) := Subgroup.mem_top g
  rw [← D.generate] at hg
  have hle : (⨆ l, (D.hom l).range) ≤ Subgroup.normalizer (compR D i : Set X) := by
    refine iSup_le fun l => ?_
    by_cases hli : l = i
    · subst hli
      exact Subgroup.le_normalizer
    · intro g hg
      rw [Subgroup.mem_normalizer_iff]
      have fwd : ∀ g ∈ (D.hom l).range, ∀ y ∈ compR D i, g * y * g⁻¹ ∈ compR D i := by
        intro g hg y hy
        rw [compR_comm D hli hg hy]
        simpa using hy
      intro y
      exact ⟨fun hy => fwd g hg y hy, fun hy => by
        simpa [mul_assoc] using fwd g⁻¹ ((D.hom l).range.inv_mem hg) _ hy⟩
  exact (Subgroup.mem_normalizer_iff.mp (hle hg) x).mp hx

theorem compR_normal (i : ι) : (compR D i).Normal :=
  ⟨fun _ hx g => compR_conj_mem D i g hx⟩

theorem compR_inf_le_center {i j : ι} (hij : i ≠ j) :
    compR D i ⊓ compR D j ≤ Subgroup.center X := by
  rintro x ⟨hxi, hxj⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ (⊤ : Subgroup X) := Subgroup.mem_top g
  rw [← D.generate] at hg
  have hle : (⨆ l, (D.hom l).range) ≤ Subgroup.centralizer ({x} : Set X) := by
    refine iSup_le fun l => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hli : l = i
    · subst hli
      exact compR_comm D hij hy hxj
    · exact compR_comm D hli hy hxi
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

theorem ker_comp_eq_center {i : ι} (hF : CompFacts (D.kind i)) :
    ((QuotientGroup.mk' (Subgroup.center X)).comp (D.hom i)).ker =
      Subgroup.center (D.kind i).G := by
  ext g
  constructor
  · intro hg
    have hgZ : D.hom i g ∈ Subgroup.center X :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hg)
    refine hF.second_center g fun h => D.ker_le_center i ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hgZ (D.hom i h)).symm
  · intro hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro x
    have hx : x ∈ (⊤ : Subgroup X) := Subgroup.mem_top x
    rw [← D.generate] at hx
    have hle : (⨆ l, (D.hom l).range) ≤ Subgroup.centralizer ({D.hom i g} : Set X) := by
      refine iSup_le fun l => ?_
      rintro _ ⟨y, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hli : l = i
      · subst hli
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hg y]
      · exact D.commute l i hli y g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

end Images

section Perm

variable {ι X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
variable (D : LieSystemData3 ι X Φ)

theorem not_le_center_of_mem (hF : ∀ i, CompFacts (D.kind i)) {L : Subgroup X} (hL : L ∈ Φ) :
    ¬ L ≤ Subgroup.center X := by
  intro hLc
  obtain ⟨i, R, hR, rfl⟩ := D.fundamental L hL
  have hRk : R ≤ ((QuotientGroup.mk' (Subgroup.center X)).comp (D.hom i)).ker := by
    intro r hr
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hLc ⟨r, hr, rfl⟩
  rw [ker_comp_eq_center D (hF i)] at hRk
  have := (hF i).finite
  have hR2 : IsPGroup 2 R := (hF i).center_two.to_le hRk
  have hL2 : IsPGroup 2 ↥(R.map (D.hom i)) := by
    rintro ⟨_, r, hr, rfl⟩
    obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : r ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    show (D.hom i r) ^ (2 ^ k) = 1
    rw [← map_pow, h1, map_one]
  exact not_dvd_24_of_isPGroup hL2 (by rw [D.card_eq _ hL])

variable {D}

theorem LieSystemData3.exists_perm [Finite ι] (hF : ∀ i, CompFacts (D.kind i)) (σ : MulAut X)
    (hσ : σ * σ = 1) (hΦ : ∀ L ∈ Φ, L.map (σ : X →* X) ∈ Φ) :
    ∃ π : ι → ι, Function.Involutive π ∧
      ∀ i, (compR D i).map (σ : X →* X) = compR D (π i) := by
  have hmem : ∀ i, ∃ L ∈ Φ, L ≤ compR D i := fun i => by
    obtain ⟨R, hR, hmem⟩ := D.meets i
    exact ⟨_, hmem, Subgroup.map_le_range _ _⟩
  have hinj : ∀ i j, i ≠ j → ¬ compR D j ≤ compR D i := by
    intro i j hij hle
    obtain ⟨L, hL, hLj⟩ := hmem j
    exact not_le_center_of_mem D hF hL
      (hLj.trans (fun x hx => compR_inf_le_center D hij ⟨hle hx, hx⟩))
  have hσσ : ∀ H : Subgroup X, (H.map (σ : X →* X)).map (σ : X →* X) = H := by
    intro H
    rw [Subgroup.map_map]
    have : (σ : X →* X).comp (σ : X →* X) = MonoidHom.id X := by
      ext x
      exact apply_apply_of_mul_eq_one hσ x
    rw [this, Subgroup.map_id]
  have hcont : ∀ i, ∃ j, compR D j ≤ (compR D i).map (σ : X →* X) := by
    intro i
    obtain ⟨L, hL, hLi⟩ := hmem i
    obtain ⟨j, R', hR', hσL⟩ := D.fundamental _ (hΦ L hL)
    refine ⟨j, ?_⟩
    have : (compR D i).Normal := compR_normal D i
    have : (compR D j).Normal := compR_normal D j
    have : ((compR D i).map (σ : X →* X)).Normal :=
      Subgroup.Normal.map inferInstance _ σ.surjective
    set M : Subgroup X := (compR D i).map (σ : X →* X) ⊓ compR D j with hM
    have hσLM : L.map (σ : X →* X) ≤ M := by
      refine le_inf (Subgroup.map_mono hLi) ?_
      rw [hσL]
      exact Subgroup.map_le_range _ _
    have h24 : 24 ∣ Nat.card M := by
      have h := Subgroup.card_dvd_of_le hσLM
      rwa [D.card_eq _ (hΦ L hL)] at h
    have hMle : M ≤ (D.hom j).range := inf_le_right
    have hMmap : (M.comap (D.hom j)).map (D.hom j) = M := Subgroup.map_comap_eq_self hMle
    have h24' : 24 ∣ Nat.card (M.comap (D.hom j)) := by
      have h := Subgroup.card_map_dvd (M.comap (D.hom j)) (D.hom j)
      rw [hMmap] at h
      exact h24.trans h
    have htop : M.comap (D.hom j) = ⊤ :=
      (hF j).normal_top _ (Subgroup.Normal.comap inferInstance _) h24'
    have hMeq : M = compR D j := by
      rw [← hMmap, htop, Subgroup.map_top]
    exact hMeq ▸ inf_le_left
  have hex : ∀ i, ∃ j, (compR D i).map (σ : X →* X) = compR D j := by
    intro i
    obtain ⟨j, hj⟩ := hcont i
    obtain ⟨j', hj'⟩ := hcont j
    have h1 : (compR D j).map (σ : X →* X) ≤ compR D i := by
      have := Subgroup.map_mono (f := (σ : X →* X)) hj
      rwa [hσσ] at this
    have h2 : compR D j' ≤ compR D i := hj'.trans h1
    have hj'i : j' = i := by
      by_contra hne
      exact hinj i j' (fun h => hne h.symm) h2
    subst hj'i
    have h3 : (compR D j').map (σ : X →* X) ≤ compR D j := by
      have := Subgroup.map_mono (f := (σ : X →* X)) hj'
      rwa [hσσ] at this
    exact ⟨j, le_antisymm h3 hj⟩
  choose π hπ using hex
  refine ⟨π, fun i => ?_, hπ⟩
  have h1 : (compR D (π i)).map (σ : X →* X) = compR D i := by
    rw [← hπ i, hσσ]
  have h2 := hπ (π i)
  rw [h1] at h2
  by_contra hne
  exact hinj (π (π i)) i hne h2.le

end Perm

section Final

variable {ι X : Type} [Group X] {Φ : Set (Subgroup X)}

@[expose] def compBar (D : LieSystemData3 ι X Φ) (i : ι) : Subgroup (X ⧸ Subgroup.center X) :=
  (compR D i).map (QuotientGroup.mk' (Subgroup.center X))

@[expose] noncomputable def compBarEquiv (D : LieSystemData3 ι X Φ) {i : ι}
    (hF : CompFacts (D.kind i)) :
    ((D.kind i).G ⧸ Subgroup.center (D.kind i).G) ≃* ↥(compBar D i) :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_comp_eq_center D hF).symm).trans
    (QuotientGroup.quotientKerEquivRange
      ((QuotientGroup.mk' (Subgroup.center X)).comp (D.hom i)))).trans
    (MulEquiv.subgroupCongr
      (MonoidHom.range_comp (QuotientGroup.mk' (Subgroup.center X)) (D.hom i)))

variable [Finite ι] [Finite X] {D : LieSystemData3 ι X Φ}

theorem LieSystemData3.permProd (hF : ∀ i, CompFacts (D.kind i)) (σ : MulAut X)
    (hσ : σ * σ = 1) (hΦ : ∀ L ∈ Φ, L.map (σ : X →* X) ∈ Φ) :
    ∃ π : ι → ι, PermProd (compBar D) (autToCentralQuotient X σ) π := by
  obtain ⟨π, hπ, hπR⟩ := LieSystemData3.exists_perm hF σ hσ hΦ
  refine ⟨π, ?_, ?_, ?_, ?_, hπ, ?_⟩
  · rintro i j hij _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, compR_comm D hij ha hb]
  · intro j s hj
    have hmap : (⨆ i ∈ s, compBar D i) =
        (⨆ i ∈ s, compR D i).map (QuotientGroup.mk' (Subgroup.center X)) := by
      simp only [compBar, Subgroup.map_iSup]
    rw [hmap]
    exact map_center_inf_iSup_eq_bot (compR D) (fun i j hij a ha b hb => compR_comm D hij ha hb)
      D.generate j s hj
  · have hgen : (⨆ i, compR D i) = ⊤ := D.generate
    have : (⨆ i, compBar D i) =
        (⨆ i, compR D i).map (QuotientGroup.mk' (Subgroup.center X)) := by
      simp only [compBar, Subgroup.map_iSup]
    rw [this, hgen]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  · rw [← map_mul, hσ, map_one]
  · intro i
    rw [compBar, map_autToCentralQuotient, hπR i]
    rfl

end Final

end CFSG.ClassicalInvolution.Q3.Q3NM
