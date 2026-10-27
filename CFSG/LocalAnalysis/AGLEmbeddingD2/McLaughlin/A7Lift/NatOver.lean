module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Baum

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six.SixCtx

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
  CFSG.RankThree.PartTwo
open Equiv Equiv.Perm MulAction

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}
variable (c : SixCtx T L) {R : Subgroup X}
variable (pd : PermData)

private theorem offIdx_card_mul_card_centralizer (hJL : thompsonJ T ≤ nL T L)
    {A : Subgroup X} (hA : IsMaxElemAbelian T A) :
    Nat.card (c.img A) *
        Nat.card (A ⊓ Subgroup.centralizer (nV T L : Set X) : Subgroup X) = Nat.card A := by
  classical
  have hV : (gnV T).Normal := Subgroup.normalClosure_normal
  have hAL : A ≤ nL T L := (CFSG.Quasithin.B6.le_thompsonJ hA).trans hJL
  have hker : ∀ a (ha : a ∈ A), c.θ ⟨a, hAL ha⟩ = 1 ↔
      a ∈ A ⊓ Subgroup.centralizer (nV T L : Set X) := by
    intro a ha
    rw [c.theta_eq_one_iff hV]
    constructor
    · intro h
      refine ⟨ha, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
      have := h u hu
      calc u * a = a * u * a⁻¹ * a := by rw [this]
        _ = a * u := by group
    · rintro ⟨-, hc⟩ u hu
      have := Subgroup.mem_centralizer_iff.1 hc u hu
      rw [← this]; group
  let f : ↥(A.subgroupOf (nL T L)) →* Perm (Fin 7) := c.θ.comp (A.subgroupOf (nL T L)).subtype
  have hrange : f.range = c.img A := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hkerf : Nat.card f.ker =
      Nat.card (A ⊓ Subgroup.centralizer (nV T L : Set X) : Subgroup X) := by
    refine Nat.card_congr ⟨fun x => ⟨((x : ↥(A.subgroupOf (nL T L))) : X),
        (hker _ (x : ↥(A.subgroupOf (nL T L))).2).1 x.2⟩,
      fun y => ⟨⟨⟨y, hAL y.2.1⟩, y.2.1⟩, (hker _ y.2.1).2 y.2⟩, fun x => rfl, fun y => rfl⟩
  have h1 := f.ker.card_mul_index
  rw [Subgroup.index_ker, hrange, hkerf] at h1
  rw [mul_comm, h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv]

private theorem offIdx_card_inf_le (hX : GNSetting X T) {A : Subgroup X}
    (hA : IsMaxElemAbelian T A) :
    Nat.card (nV T L) *
        Nat.card (A ⊓ Subgroup.centralizer (nV T L : Set X) : Subgroup X) ≤
      Nat.card A * Nat.card (nV T L ⊓ A : Subgroup X) := by
  classical
  have hNT : nV T L ≤ T := nV_le (L := L) hX
  have hNe := isElemAbelian_nV (L := L) hX
  have hcomm : ∀ x ∈ nV T L, ∀ y ∈ A ⊓ Subgroup.centralizer (nV T L : Set X),
      x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 hy.2 x hx
  have hsup := CFSG.RankThree.PartOne.PlaneCommuting.card_sup_mul_card_inf hcomm
  have hinf : nV T L ⊓ (A ⊓ Subgroup.centralizer (nV T L : Set X)) = nV T L ⊓ A := by
    refine le_antisymm (inf_le_inf_left _ inf_le_left) fun x hx => ⟨hx.1, hx.2, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
    exact congrArg Subtype.val (hNe.1.1.comm ⟨u, hu⟩ ⟨x, hx.1⟩)
  have hA'e : IsElemAbelian 2 (A ⊓ Subgroup.centralizer (nV T L : Set X)) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => hA.2.1.2 x hx.1⟩
    have h2 := congrArg Subtype.val (hA.2.1.1.1.comm ⟨x, x.2.1⟩ ⟨y, y.2.1⟩)
    apply Subtype.ext
    simpa using h2
  have hBe : IsElemAbelian 2 (nV T L ⊔ (A ⊓ Subgroup.centralizer (nV T L : Set X))) :=
    isElemAbelian_sup_of_commute hNe hA'e hcomm
  have hBT : nV T L ⊔ (A ⊓ Subgroup.centralizer (nV T L : Set X)) ≤ T :=
    sup_le hNT (inf_le_left.trans hA.1)
  have hle := hA.2.2 _ hBT hBe
  rw [hinf] at hsup
  rw [← hsup]
  exact Nat.mul_le_mul_right _ hle

private theorem offIdx_card_altFix (hX : GNSetting X T) (hJL : thompsonJ T ≤ nL T L)
    {A : Subgroup X} (hA : IsMaxElemAbelian T A) :
    Nat.card (altFix 7 (c.img A)) = Nat.card (nV T L ⊓ A : Subgroup X) := by
  classical
  have hV : (gnV T).Normal := Subgroup.normalClosure_normal
  have hAL : A ≤ nL T L := (CFSG.Quasithin.B6.le_thompsonJ hA).trans hJL
  have hNT : nV T L ≤ T := nV_le (L := L) hX
  have hNe := isElemAbelian_nV (L := L) hX
  have hNA : ∀ u ∈ nV T L, u ∈ A ↔ ∀ a ∈ A, a * u * a⁻¹ = u := by
    intro u hu
    constructor
    · intro huA a ha
      have := congrArg Subtype.val (hA.2.1.1.1.comm ⟨a, ha⟩ ⟨u, huA⟩)
      simp only [Subgroup.coe_mul] at this
      rw [this]; group
    · intro h
      rw [eq_omegaOneOf_centralizer hA]
      refine Subgroup.subset_closure ⟨⟨hNT hu, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩,
        hNe.2 u hu⟩
      have := h a ha
      calc a * u = a * u * a⁻¹ * a := by group
        _ = u * a := by rw [this]
  have hmem : ∀ u : ↥(nV T L),
      Multiplicative.toAdd (c.φ u) ∈ altFix 7 (c.img A) ↔ (u : X) ∈ A := by
    intro u
    rw [mem_altFix_iff, hNA u u.2]
    constructor
    · intro h a ha
      have hv : (a : X) * u * a⁻¹ ∈ nV T L :=
        (Subgroup.mem_normalizer_iff.1 (nL_le_normalizer_nV hV (hAL ha)) u).1 u.2
      have h1 := c.hφe' ⟨a, hAL ha⟩ u ⟨_, hv⟩ rfl
      obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (c.φ u))
      have h2 := h (c.θ ⟨a, hAL ha⟩) ⟨⟨a, hAL ha⟩, ha, rfl⟩ x hx
      rw [← altAct_mk, hx] at h2
      rw [h2] at h1
      exact congrArg Subtype.val (c.hφ.1 (Multiplicative.toAdd.injective h1))
    · intro h σ hσ x hx
      obtain ⟨a, ha, rfl⟩ := (c.mem_img hAL).1 hσ
      rw [← altAct_mk, hx]
      have h1 := c.hφe' ⟨a, hAL ha⟩ u u (h a ha).symm
      exact h1.symm
  let f : ↥(nV T L ⊓ A : Subgroup X) → ↥(altFix 7 (c.img A)) := fun x =>
    ⟨Multiplicative.toAdd (c.φ ⟨x, x.2.1⟩), (hmem ⟨x, x.2.1⟩).2 x.2.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun v => ?_⟩
    · have h1 : c.φ ⟨x, x.2.1⟩ = c.φ ⟨y, y.2.1⟩ :=
        Multiplicative.toAdd.injective (congrArg Subtype.val hxy)
      have h2 := congrArg Subtype.val (c.hφ.1 h1)
      exact Subtype.ext h2
    · obtain ⟨u, hu⟩ := c.hφ.2 (Multiplicative.ofAdd (v : altHeart 7))
      have huA : (u : X) ∈ A := (hmem u).1 (by rw [hu]; exact v.2)
      refine ⟨⟨u, u.2, huA⟩, Subtype.ext ?_⟩
      show Multiplicative.toAdd (c.φ ⟨(u : X), u.2⟩) = (v : altHeart 7)
      rw [show (⟨(u : X), u.2⟩ : ↥(nV T L)) = u from rfl, hu]
      rfl
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem offIdx_le_R (hX : GNSetting X T) (hJL : thompsonJ T ≤ nL T L) {A : Subgroup X}
    (hA : IsMaxElemAbelian T A) : (altFix 7 (c.img A)).index ≤ Nat.card (c.img A) := by
  classical
  have hcardE := offIdx_card_mul_card_centralizer (L := L) c hJL hA
  have hineq := offIdx_card_inf_le (L := L) hX hA
  have hfix := offIdx_card_altFix (L := L) c hX hJL hA
  have hcardH : Nat.card (altHeart 7) = Nat.card (nV T L) :=
    (Nat.card_congr (Equiv.ofBijective c.φ c.hφ)).symm.trans rfl
  have hidx := (altFix 7 (c.img A)).index_mul_card
  rw [hfix, hcardH] at hidx
  have hpos1 : 0 < Nat.card (A ⊓ Subgroup.centralizer (nV T L : Set X) : Subgroup X) :=
    Nat.card_pos
  have hpos2 : 0 < Nat.card (nV T L ⊓ A : Subgroup X) := Nat.card_pos
  have h3 : (altFix 7 (c.img A)).index * Nat.card (nV T L ⊓ A : Subgroup X) *
      Nat.card (A ⊓ Subgroup.centralizer (nV T L : Set X) : Subgroup X) ≤
      Nat.card (c.img A) *
        Nat.card (A ⊓ Subgroup.centralizer (nV T L : Set X) : Subgroup X) *
        Nat.card (nV T L ⊓ A : Subgroup X) := by
    rw [hidx, hcardE]
    exact hineq
  have h4 : (altFix 7 (c.img A)).index *
      (Nat.card (nV T L ⊓ A : Subgroup X) *
        Nat.card (A ⊓ Subgroup.centralizer (nV T L : Set X) : Subgroup X)) ≤
      Nat.card (c.img A) *
        (Nat.card (nV T L ⊓ A : Subgroup X) *
          Nat.card (A ⊓ Subgroup.centralizer (nV T L : Set X) : Subgroup X)) := by
    calc _ = (altFix 7 (c.img A)).index * Nat.card (nV T L ⊓ A : Subgroup X) *
          Nat.card (A ⊓ Subgroup.centralizer (nV T L : Set X) : Subgroup X) := by ring
      _ ≤ _ := h3
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h4 (Nat.mul_pos hpos2 hpos1)

omit [Finite X] in
theorem img_sq_R (hJL : thompsonJ T ≤ nL T L) {A : Subgroup X}
    (hA : IsMaxElemAbelian T A) : ∀ σ ∈ c.img A, σ * σ = 1 := by
  intro σ hσ
  obtain ⟨a, ha, rfl⟩ := (c.mem_img ((CFSG.Quasithin.B6.le_thompsonJ hA).trans hJL)).1 hσ
  rw [← map_mul, ← map_one c.θ]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
  exact hA.2.1.2 a ha

theorem offenderShape_R (hX : GNSetting X T) (hJL : thompsonJ T ≤ nL T L) {A : Subgroup X}
    (hA : IsMaxElemAbelian T A) : Offender.OffenderShapeConcl (c.img A) :=
  offender_shape_altHeart (Or.inl rfl) _ (c.img_sq_R hJL hA) (c.offIdx_le_R hX hJL hA)

theorem swap_mem_theta_R (hX : GNSetting X T) (hJL : thompsonJ T ≤ nL T L)
    {A : Subgroup X} (hA : IsMaxElemAbelian T A) {σ : Perm (Fin 7)} (hσ : σ ∈ c.img A)
    {i : Fin 7} (hi : σ i ≠ i) : swap i (σ i) ∈ c.img A := by
  classical
  have hsq := c.img_sq_R hJL hA
  have hp : IsPGroup 2 (c.img A) := fun g => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, pow_two, Subgroup.coe_one]
    exact hsq g g.2)⟩
  obtain ⟨p, hp'⟩ := exists_fixed_of_isPGroup hp
  obtain ⟨-, hE⟩ := (c.offenderShape_R hX hJL hA).1 ⟨p, hp'⟩
  rw [hE]
  intro j
  by_cases hji : j = i
  · subst hji
    rw [swap_apply_left]
    exact ⟨⟨σ, hσ⟩, rfl⟩
  by_cases hjs : j = σ i
  · subst hjs
    rw [swap_apply_right]
    refine ⟨⟨σ, hσ⟩, ?_⟩
    show σ (σ i) = i
    rw [← Perm.mul_apply, hsq σ hσ, one_apply]
  · rw [swap_apply_of_ne_of_ne hji hjs]
    exact mem_orbit_self j

theorem exists_swap_mem_img_R (hX : GNSetting X T) (hRL : R ≤ nL T L)
    (hJR : thompsonJ T ≤ R) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) :
    ∃ i j : Fin 7, i ≠ j ∧ swap i j ∈ c.img R := by
  by_contra hcon
  push Not at hcon
  have hJL : thompsonJ T ≤ nL T L := hJR.trans hRL
  have hAbot : ∀ A : Subgroup X, IsMaxElemAbelian T A → c.img A = ⊥ := by
    intro A hA
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    by_contra hσ1
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra h
      push Not at h
      exact hσ1 (Equiv.ext h)
    have h1 := c.swap_mem_theta_R hX hJL hA hσ hi
    exact hcon i (σ i) hi.symm (c.img_mono ((CFSG.Quasithin.B6.le_thompsonJ hA).trans hJR) h1)
  have hJc : ∀ j ∈ thompsonJ T, ∀ l ∈ L, QuotientGroup.mk' (gnC T) j * l *
      (QuotientGroup.mk' (gnC T) j)⁻¹ = l := by
    intro j hj
    set K : Subgroup X := (c.θ.ker).map (nL T L).subtype with hK
    have hJK : thompsonJ T ≤ K := by
      refine iSup₂_le fun A hA a ha => ?_
      have haL : a ∈ nL T L := hJL (CFSG.Quasithin.B6.le_thompsonJ hA ha)
      have h1 : c.θ ⟨a, haL⟩ ∈ c.img A := ⟨⟨a, haL⟩, ha, rfl⟩
      rw [hAbot A hA, Subgroup.mem_bot] at h1
      exact ⟨⟨a, haL⟩, h1, rfl⟩
    obtain ⟨⟨g, hg⟩, hg1, hgj⟩ := hJK hj
    simp only [Subgroup.coe_subtype] at hgj
    subst hgj
    exact (c.hθ1 ⟨g, hg⟩).1 hg1
  have hbot : ⁅L, gnImg T (thompsonJ T)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    have := hJc j hj l hl
    calc QuotientGroup.mk' (gnC T) j * l =
        QuotientGroup.mk' (gnC T) j * l * (QuotientGroup.mk' (gnC T) j)⁻¹ *
          QuotientGroup.mk' (gnC T) j := by group
      _ = l * QuotientGroup.mk' (gnC T) j := by rw [this]
  rw [hJ] at hbot
  have h1 : Nat.card ↥L = 1 := by rw [hbot, Subgroup.card_bot]
  have h2 : Nat.card ↥L = 2520 := by
    rw [Nat.card_congr c.eL.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  omega

theorem eight_le_card_img_R_inf (hX : GNSetting X T) (hRL : R ≤ nL T L)
    (hLR : T ⊓ lT T L ≤ R) (hL : IsComponentOf L ⊤) :
    8 ≤ Nat.card (c.img R ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) := by
  classical
  have hSyl := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf
    hX.sylow hL.2.1
  have hcardL : Nat.card ↥L = 2520 := by
    rw [Nat.card_congr c.eL.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have h8 : 2 ^ 3 ∣ Nat.card (gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)) := by
    have hmul := Subgroup.relIndex_mul_card (gnImg T T ⊓ L) L
    rw [inf_eq_left.mpr hSyl.1, hcardL] at hmul
    have hodd : ¬ 2 ∣ (gnImg T T ⊓ L).relIndex L := hSyl.2.2
    have hcop : Nat.Coprime (2 ^ 3) ((gnImg T T ⊓ L).relIndex L) :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    have h1 : 2 ^ 3 ∣ Nat.card (gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)) *
        (gnImg T T ⊓ L).relIndex L := by
      rw [mul_comm, hmul]; norm_num
    exact hcop.dvd_of_dvd_mul_right h1
  have hmem : ∀ y : ↥(gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)),
      ((c.eL ⟨y, y.2.2⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈
        c.img R ⊓ alternatingGroup (Fin 7) := by
    rintro ⟨y, ⟨t, ht, rfl⟩, hy⟩
    have htL : t ∈ lT T L := Subgroup.mem_comap.mpr hy
    have htR : t ∈ R := hLR ⟨ht, htL⟩
    refine ⟨⟨⟨t, hRL htR⟩, htR, ?_⟩, (c.eL ⟨_, hy⟩).2⟩
    exact c.hθL ⟨t, hRL htR⟩ ⟨_, hy⟩ rfl
  let f : ↥(gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)) →
      ↥(c.img R ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) :=
    fun y => ⟨_, hmem y⟩
  have hf : Function.Injective f := by
    intro y y' h
    have h0 := congrArg Subtype.val h
    have h1 : c.eL ⟨y, y.2.2⟩ = c.eL ⟨y', y'.2.2⟩ := Subtype.ext h0
    have h2 := congrArg Subtype.val (c.eL.injective h1)
    exact Subtype.ext h2
  have hle := Nat.card_le_card_of_injective f hf
  exact (Nat.le_of_dvd Nat.card_pos h8).trans hle

theorem card_img_R (hX : GNSetting X T) (hRL : R ≤ nL T L) (hRT : R ≤ T)
    (hJR : thompsonJ T ≤ R) (hLR : T ⊓ lT T L ≤ R) (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) : Nat.card (c.img R) = 16 := by
  classical
  set H := c.img R with hH
  have hp : IsPGroup 2 H := by
    have hR2 : IsPGroup 2 ↥R := IsPGroup.to_le (p := 2) hX.sylow.2.1 hRT
    have hT2 : IsPGroup 2 ↥(R.subgroupOf (nL T L)) :=
      IsPGroup.of_equiv hR2 (Subgroup.subgroupOfEquivOfLe hRL).symm
    exact IsPGroup.map hT2 c.θ
  obtain ⟨i, j, hij, hsw⟩ := c.exists_swap_mem_img_R hX hRL hJR hJ
  have hrel : (alternatingGroup (Fin 7)).relIndex H = 2 := by
    have hdvd : (alternatingGroup (Fin 7)).relIndex H ∣ 2 := by
      rw [← alternatingGroup.index_eq_two (α := Fin 7)]
      exact Subgroup.relIndex_dvd_index_of_normal (H := alternatingGroup (Fin 7)) (K := H)
    have hne1 : (alternatingGroup (Fin 7)).relIndex H ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro hle
      have := Equiv.Perm.mem_alternatingGroup.mp (hle hsw)
      rw [Equiv.Perm.sign_swap hij] at this
      exact absurd this (by decide)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hmul : (alternatingGroup (Fin 7)).relIndex H *
      Nat.card (alternatingGroup (Fin 7) ⊓ H : Subgroup (Perm (Fin 7))) = Nat.card H :=
    Subgroup.relIndex_mul_card (alternatingGroup (Fin 7)) H
  rw [hrel] at hmul
  have h8 := c.eight_le_card_img_R_inf hX hRL hLR hL
  rw [← hH, inf_comm] at h8
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hdvd : Nat.card H ∣ 5040 := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [Nat.card_perm, Nat.card_fin] at this
  rw [hk] at hdvd hmul
  have hk4 : k ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 5 ∣ 5040 := (Nat.pow_dvd_pow 2 hlt).trans hdvd
    exact absurd this (by decide)
  have hk4' : 4 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hk, show k = 4 by omega]
  rfl

theorem exists_conj_img_R (hX : GNSetting X T) (hRL : R ≤ nL T L) (hRT : R ≤ T)
    (hJR : thompsonJ T ≤ R) (hLR : T ⊓ lT T L ≤ R) (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) {D : Subgroup (Perm (Fin 7))}
    (hD : Nat.card D = 16) : ∃ σ : Perm (Fin 7), (c.conj σ).img R = D := by
  have h2 : (Nat.card (Perm (Fin 7))).factorization 2 = 4 := by
    rw [Nat.card_perm, Nat.card_fin, Nat.factorization_def _ Nat.prime_two]
    have : Nat.factorial 7 = 2 ^ 4 * 315 := by decide
    rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
    simp [padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ 315 by decide)]
  have hP : Nat.card (c.img R) = 2 ^ (Nat.card (Perm (Fin 7))).factorization 2 := by
    rw [h2, c.card_img_R hX hRL hRT hJR hLR hL hJ]; norm_num
  have hQ : Nat.card D = 2 ^ (Nat.card (Perm (Fin 7))).factorization 2 := by
    rw [h2, hD]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Perm (Fin 7))
    (Sylow.ofCard (c.img R) hP) (Sylow.ofCard D hQ)
  refine ⟨σ, ?_⟩
  have h3 := congrArg (fun P : Sylow 2 (Perm (Fin 7)) => (P : Subgroup (Perm (Fin 7)))) hσ
  simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at h3
  rw [img_conj, ← h3]
  rfl

theorem img_maxElem_le_E_R (hX : GNSetting X T) (hRL : R ≤ nL T L)
    (hJR : thompsonJ T ≤ R) (hD : c.img R = pd.D) {A : Subgroup X}
    (hA : IsMaxElemAbelian T A) : c.img A ≤ pd.E := by
  have hJL : thompsonJ T ≤ nL T L := hJR.trans hRL
  intro σ hσ
  have hAR : A ≤ R := (CFSG.Quasithin.B6.le_thompsonJ hA).trans hJR
  have hσD : σ ∈ pd.D := hD ▸ c.img_mono hAR hσ
  refine pd.D_trans σ hσD (c.img_sq_R hJL hA σ hσ) fun i hi => ?_
  exact hD ▸ c.img_mono hAR (c.swap_mem_theta_R hX hJL hA hσ hi)

theorem theta_mem_E_of_mem_J_R (hX : GNSetting X T) (hRL : R ≤ nL T L)
    (hJR : thompsonJ T ≤ R) (hD : c.img R = pd.D) {j : X} (hj : j ∈ thompsonJ T)
    (hjL : j ∈ nL T L) : c.θ ⟨j, hjL⟩ ∈ pd.E := by
  have hJK : thompsonJ T ≤ (pd.E.comap c.θ).map (nL T L).subtype := by
    refine iSup₂_le fun A hA a ha => ?_
    have haL : a ∈ nL T L := hRL (hJR (CFSG.Quasithin.B6.le_thompsonJ hA ha))
    exact ⟨⟨a, haL⟩,
      c.img_maxElem_le_E_R pd hX hRL hJR hD hA ⟨⟨a, haL⟩, ha, rfl⟩, rfl⟩
  obtain ⟨⟨g, hg⟩, hgE, hgj⟩ := hJK hj
  simp only [Subgroup.coe_subtype] at hgj
  subst hgj
  exact hgE

theorem baum_fix_pair_R (hX : GNSetting X T) (hRL : R ≤ nL T L) (hJR : thompsonJ T ≤ R)
    (hbR : baum T ≤ R) (hD : c.img R = pd.D) {a b : Fin 7} (hab : a ≠ b)
    (hE : ∀ σ ∈ pd.E, (σ a = a ∨ σ a = b) ∧ (σ b = a ∨ σ b = b))
    {g : X} (hg : g ∈ baum T) :
    altAct (c.θ ⟨g, hRL (hbR hg)⟩) (QuotientAddGroup.mk (pairVec a b) : altHeart 7) =
      (QuotientAddGroup.mk (pairVec a b) : altHeart 7) := by
  have hV : (gnV T).Normal := Subgroup.normalClosure_normal
  have hVe := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV T hX
  have hVT := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.gnV_le T hX
  have hJL : thompsonJ T ≤ nL T L := hJR.trans hRL
  obtain ⟨u, hu⟩ := c.hφ.2 (Multiplicative.ofAdd (QuotientAddGroup.mk (pairVec a b)))
  have hc : ∀ j ∈ thompsonJ T, j * (u : X) = (u : X) * j := by
    intro j hj
    have hjL : j ∈ nL T L := hJL hj
    have hθj := c.theta_mem_E_of_mem_J_R pd hX hRL hJR hD hj hjL
    have hv : j * (u : X) * j⁻¹ ∈ nV T L :=
      (Subgroup.mem_normalizer_iff.1 (nL_le_normalizer_nV hV hjL) u).1 u.2
    have h1 := c.hφe' ⟨j, hjL⟩ u ⟨_, hv⟩ rfl
    rw [hu, toAdd_ofAdd, altAct_fix_of_pair hab (hE _ hθj).1 (hE _ hθj).2] at h1
    have h2 : c.φ ⟨_, hv⟩ = c.φ u := by
      rw [hu]
      exact Multiplicative.toAdd.injective h1
    have h3 := congrArg Subtype.val (c.hφ.1 h2)
    simp only at h3
    calc j * (u : X) = j * (u : X) * j⁻¹ * j := by group
      _ = (u : X) * j := by rw [h3]
  have huV : (u : X) ∈ gnV T := Subgroup.commutator_le_left _ _ u.2
  have huΩ := CFSG.AGLEmbeddingD2.Tits.E23.mem_omegaOneCenterOf_thompsonJ hVe hVT huV hc
  have hgu : g * (u : X) * g⁻¹ = (u : X) := by
    have := Subgroup.mem_centralizer_iff.1 hg.2 _ huΩ
    rw [← this]; group
  have hv : g * (u : X) * g⁻¹ ∈ nV T L := by rw [hgu]; exact u.2
  have h1 := c.hφe' ⟨g, hRL (hbR hg)⟩ u ⟨_, hv⟩ rfl
  have h4 : (⟨g * (u : X) * g⁻¹, hv⟩ : ↥(nV T L)) = u := Subtype.ext hgu
  rw [h4, hu, toAdd_ofAdd] at h1
  exact h1.symm

theorem theta_mem_E_of_mem_baum_R (hX : GNSetting X T) (hRL : R ≤ nL T L)
    (hJR : thompsonJ T ≤ R) (hbR : baum T ≤ R) (hD : c.img R = pd.D)
    {g : X} (hg : g ∈ baum T) : c.θ ⟨g, hRL (hbR hg)⟩ ∈ pd.E := by
  have hgD : c.θ ⟨g, hRL (hbR hg)⟩ ∈ pd.D :=
    hD ▸ ⟨⟨g, hRL (hbR hg)⟩, hbR hg, rfl⟩
  have hE02 : ∀ σ ∈ pd.E, (σ 0 = 0 ∨ σ 0 = 2) ∧ (σ 2 = 0 ∨ σ 2 = 2) := fun σ hσ =>
    pair_of_finset (pd.E_pairs σ hσ).1 (pd.E_pairs σ hσ).2.1
  have hE13 : ∀ σ ∈ pd.E, (σ 1 = 1 ∨ σ 1 = 3) ∧ (σ 3 = 1 ∨ σ 3 = 3) := fun σ hσ =>
    pair_of_finset (pd.E_pairs σ hσ).2.2.1 (pd.E_pairs σ hσ).2.2.2.1
  have hE45 : ∀ σ ∈ pd.E, (σ 4 = 4 ∨ σ 4 = 5) ∧ (σ 5 = 4 ∨ σ 5 = 5) := fun σ hσ =>
    pair_of_finset (pd.E_pairs σ hσ).2.2.2.2.1 (pd.E_pairs σ hσ).2.2.2.2.2
  obtain ⟨h0, h2⟩ := pair_of_altAct_fix (by decide)
    (c.baum_fix_pair_R pd hX hRL hJR hbR hD (by decide) hE02 hg)
  obtain ⟨h1, h3⟩ := pair_of_altAct_fix (by decide)
    (c.baum_fix_pair_R pd hX hRL hJR hbR hD (by decide) hE13 hg)
  obtain ⟨h4, h5⟩ := pair_of_altAct_fix (by decide)
    (c.baum_fix_pair_R pd hX hRL hJR hbR hD (by decide) hE45 hg)
  refine pd.D_stab _ hgD ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] <;> assumption

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six.SixCtx
