module

public import CFSG.GH74.E2.Q8Basic

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped commutatorElement

namespace Q8

section Restrict

variable {X : Type*} [Group X]

private def q8II_res (g : MulAut X) : MulAut ↥(frattini X) where
  toFun x := ⟨g x, frattini_inv g x.2⟩
  invFun x := ⟨g⁻¹ x, frattini_inv g⁻¹ x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (map_mul g x.1 y.1)

private theorem q8II_res_apply (g : MulAut X) (x : ↥(frattini X)) :
    ((q8II_res g x : ↥(frattini X)) : X) = g x := rfl

private theorem q8II_res_cube {g : MulAut X} (hg : g ^ 3 = 1) : q8II_res g ^ 3 = 1 := by
  have h3 : ∀ y, g (g (g y)) = y := fun y => by
    have := congrArg (fun f : MulAut X => f y) hg
    simpa [pow_succ, MulAut.mul_apply] using this
  refine MulEquiv.ext fun x => Subtype.ext ?_
  have e : ((q8II_res g ^ 3) x : X) = g (g (g x)) := by
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, q8II_res_apply]
  rw [e, h3]
  rfl

end Restrict

section Coprime

variable {P : Type*} [Group P] [Finite P]

private theorem q8II_eq_one_of_aV (hP : IsPGroup 2 P) {g : MulAut P} (hg : g ^ 3 = 1)
    (h : aV g hg = 1) : g = 1 := by
  have hN := frattini_inv_iff hg
  have hsup : fixSub g ⊔ frattini P = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x⁻¹ * g x ∈ frattini P := by
      have := congrArg (fun f : MulAut (P ⧸ frattini P) => f (x : P ⧸ frattini P)) h
      simp only [aV, quotAut_mk, MulAut.one_apply] at this
      exact QuotientGroup.eq.1 this.symm
    obtain ⟨n, hn, hfix⟩ := exists_fixed_mul_mem hP hg hN hx
    have hxn : x * n ∈ fixSub g := hfix
    have hxe : x = (x * n) * n⁻¹ := by group
    rw [hxe]
    exact Subgroup.mul_mem_sup hxn (Subgroup.inv_mem _ hn)
  have htop := frattini_nongenerating hsup
  refine MulEquiv.ext fun x => ?_
  have hx : x ∈ fixSub g := by rw [htop]; trivial
  exact hx

private theorem q8II_fpf (hP : IsPGroup 2 P) (hrk : Group.rank P ≤ 2) {g : MulAut P}
    (hg : g ^ 3 = 1) (hne : g ≠ 1) :
    Group.rank P = 2 ∧ ∀ x : P, g x * x⁻¹ ∈ frattini P → x ∈ frattini P := by
  have hWcard : Nat.card (P ⧸ frattini P) = 2 ^ Group.rank P :=
    card_frattini_quotient_eq_two_pow_rank hP
  have hgW3 : aV g hg ^ 3 = 1 := quotAut_pow_three g _ _ hg
  have hgW1 : aV g hg ≠ 1 := fun h1 => hne (q8II_eq_one_of_aV hP hg h1)
  have hmod : Nat.card (P ⧸ frattini P) ≡ Nat.card (fixSub (aV g hg)) [MOD 3] := by
    have h := card_modEq_three_fixed hgW3 (Set.univ : Set (P ⧸ frattini P))
      (fun y _ => Set.mem_univ _)
    have hset : {y : P ⧸ frattini P | y ∈ (Set.univ : Set (P ⧸ frattini P)) ∧
        aV g hg y = y} = (fixSub (aV g hg) : Set (P ⧸ frattini P)) := by
      ext y
      simp [mem_fixSub]
    rw [hset, Nat.card_univ] at h
    exact h
  have hdvd : Nat.card (fixSub (aV g hg)) ∣ 2 ^ Group.rank P := by
    rw [← hWcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hne' : Nat.card (fixSub (aV g hg)) ≠ Nat.card (P ⧸ frattini P) := by
    intro heq
    apply hgW1
    have htop : fixSub (aV g hg) = ⊤ := Subgroup.eq_top_of_card_eq _ heq
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ fixSub (aV g hg) := by rw [htop]; trivial
    exact hv
  obtain ⟨i, hi, hni⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hr2 : Group.rank P = 2 ∧ i = 0 := by
    rw [hWcard, hni] at hmod
    rw [hWcard, hni] at hne'
    generalize Group.rank P = r at *
    interval_cases r <;> interval_cases i <;> simp_all [Nat.ModEq]
  refine ⟨hr2.1, fun x hx => ?_⟩
  have h1 : (QuotientGroup.mk x : P ⧸ frattini P) ∈ fixSub (aV g hg) := by
    show aV g hg (QuotientGroup.mk x) = QuotientGroup.mk x
    unfold aV
    rw [quotAut_mk]
    exact QuotientGroup.eq_iff_div_mem.2 (by simpa [div_eq_mul_inv] using hx)
  have hbot : fixSub (aV g hg) = ⊥ := by
    rw [Subgroup.eq_bot_iff_card, hni, hr2.2]
    simp
  rw [hbot, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff x).1 h1

end Coprime

section Pair

variable {X : Type*} [Group X] [Finite X] {c : MulAut X}

private theorem q8II_good (hg : Good X c) (hnt : ∃ p ∈ frattini X, c p ≠ p) :
    Good ↥(frattini X) (q8II_res c) := by
  have hcube : q8II_res c ^ 3 = 1 := q8II_res_cube hg.cube
  have hne : q8II_res c ≠ 1 := by
    intro h1
    obtain ⟨p, hp, hcp⟩ := hnt
    apply hcp
    have := congrArg (fun f : MulAut ↥(frattini X) => ((f ⟨p, hp⟩ : ↥(frattini X)) : X)) h1
    simpa [q8II_res_apply] using this
  obtain ⟨hr, hfpf⟩ := q8II_fpf (hg.pgroup.to_subgroup _) (hg.sub_rank _) hcube hne
  refine ⟨hg.pgroup.to_subgroup _, hr, ?_, hcube, hfpf⟩
  intro Q'
  have h1 := hg.sub_rank (Q'.map (frattini X).subtype)
  rwa [← Group.rank_congr (Q'.equivMapOfInjective _ (Subgroup.subtype_injective _))] at h1

private abbrev q8II_R (X : Type*) [Group X] : Subgroup X :=
  (frattini ↥(frattini X)).map (frattini X).subtype

omit [Finite X] in
private theorem q8II_R_le : q8II_R X ≤ frattini X := by
  rintro _ ⟨π, -, rfl⟩
  exact π.2

omit [Finite X] in
private theorem q8II_R_c (g : MulAut X) {r : X} (hr : r ∈ q8II_R X) : g r ∈ q8II_R X := by
  obtain ⟨π, hπ, rfl⟩ := hr
  exact ⟨q8II_res g π, frattini_inv _ hπ, rfl⟩

omit [Finite X] in
private theorem q8II_R_conj (x : X) {r : X} (hr : r ∈ q8II_R X) : x * r * x⁻¹ ∈ q8II_R X := by
  obtain ⟨π, hπ, rfl⟩ := hr
  exact ⟨MulAut.conjNormal x π, frattini_inv _ hπ, MulAut.conjNormal_apply x π⟩

private theorem q8II_between (hgP : Good ↥(frattini X) (q8II_res c)) {D : Subgroup X}
    (hRD : q8II_R X ≤ D) (hDP : D ≤ frattini X) (hD : ∀ x ∈ D, c x ∈ D) :
    D = q8II_R X ∨ D = frattini X := by
  let Dg : Subgroup ↥(frattini X) := D.comap (frattini X).subtype
  have hΦ : frattini ↥(frattini X) ≤ Dg := fun π hπ => hRD ⟨π, hπ, rfl⟩
  have hinv : ∀ x ∈ Dg, q8II_res c x ∈ Dg := fun x hx => hD x.1 hx
  rcases inv_between hgP hΦ hinv with h1 | h1
  · left
    refine le_antisymm (fun d hd => ?_) hRD
    have hd' : (⟨d, hDP hd⟩ : ↥(frattini X)) ∈ Dg := hd
    rw [h1] at hd'
    exact ⟨_, hd', rfl⟩
  · right
    refine le_antisymm hDP (fun p hp => ?_)
    have : (⟨p, hp⟩ : ↥(frattini X)) ∈ Dg := by rw [h1]; trivial
    exact this

private theorem q8II_nongen {A : Subgroup X} (hA : A ≤ frattini X)
    (h : A ⊔ q8II_R X = frattini X) : A = frattini X := by
  have hsup := Subgroup.comap_sup_eq_of_le_range (f := (frattini X).subtype) (H := A)
    (K := q8II_R X) (by rwa [Subgroup.range_subtype]) (by
      rw [Subgroup.range_subtype]
      exact q8II_R_le)
  have hR : (q8II_R X).comap (frattini X).subtype = frattini ↥(frattini X) :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have hP : (frattini X).comap (frattini X).subtype = ⊤ := Subgroup.subgroupOf_self _
  rw [hR, h, hP] at hsup
  have h1 := frattini_nongenerating hsup
  refine le_antisymm hA (fun p hp => ?_)
  have : (⟨p, hp⟩ : ↥(frattini X)) ∈ A.comap (frattini X).subtype := by rw [h1]; trivial
  exact this

private theorem q8II_R_card (hgP : Good ↥(frattini X) (q8II_res c))
    (hP8 : Nat.card ↥(frattini X) = 8) : Nat.card (frattini ↥(frattini X)) = 2 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥(frattini X))
  rw [hP8, hgP.card_V] at h
  omega

omit [Finite X] in
private theorem q8II_R_elems (hR : Nat.card (frattini ↥(frattini X)) = 2) :
    ∃ u : X, u ≠ 1 ∧ u ∈ q8II_R X ∧ ∀ r ∈ q8II_R X, r = 1 ∨ r = u := by
  have hR' : Nat.card (q8II_R X) = 2 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hR
  obtain ⟨u, hu1, hu2⟩ := (Nat.card_eq_two_iff' (1 : q8II_R X)).1 hR'
  refine ⟨u.1, fun h => hu1 (Subtype.ext h), u.2, fun r hr => ?_⟩
  by_cases h : r = 1
  · exact Or.inl h
  · right
    have := hu2 ⟨r, hr⟩ (fun e => h (congrArg Subtype.val e))
    exact congrArg Subtype.val this

omit [Finite X] in
private theorem q8II_R_props {u : X} (hall : ∀ r ∈ q8II_R X, r = 1 ∨ r = u) :
    (∀ r ∈ q8II_R X, ∀ x : X, x * r = r * x) ∧ (∀ r ∈ q8II_R X, r * r = 1) := by
  have huniq : ∀ y ∈ q8II_R X, ∀ z ∈ q8II_R X, y ≠ 1 → z ≠ 1 → y = z := by
    intro y hy z hz hy1 hz1
    rcases hall y hy with h | h
    · exact absurd h hy1
    · rcases hall z hz with h' | h'
      · exact absurd h' hz1
      · rw [h, h']
  refine ⟨fun r hr x => ?_, fun r hr => ?_⟩
  · by_cases h : r = 1
    · rw [h, mul_one, one_mul]
    · have h1 : x * r * x⁻¹ = r := by
        refine huniq _ (q8II_R_conj x hr) r hr (fun e => h ?_) h
        have : r = x⁻¹ * (x * r * x⁻¹) * x := by group
        rw [this, e]
        group
      exact mul_inv_eq_iff_eq_mul.1 h1
  · by_cases h : r = 1
    · rw [h, mul_one]
    · by_contra hne
      have hrr : r * r ∈ q8II_R X := Subgroup.mul_mem _ hr hr
      have : r * r = r := huniq _ hrr r hr hne h
      exact h (mul_left_cancel (a := r) (show r * r = r * 1 by rw [mul_one]; exact this))

end Pair

section Final

variable {X : Type*} [Group X] [Finite X] {c : MulAut X}

private theorem q8II_comm_of_closure {G : Type*} [Group G] {S : Set G}
    (hS : Subgroup.closure S = ⊤) (hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) :
    ∀ g h : G, g * h = h * g := by
  have h1 : ∀ s ∈ S, ∀ g : G, g * s = s * g := by
    intro s hs g
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.closure_le]
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      exact hcomm s hs t ht
    have hg : g ∈ Subgroup.centralizer ({s} : Set G) := hle (hS ▸ Subgroup.mem_top g)
    exact ((Subgroup.mem_centralizer_iff.1 hg) s rfl).symm
  intro g h
  have hle : Subgroup.closure S ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [Subgroup.closure_le]
    intro t ht
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    rw [hu]
    exact h1 t ht g
  have hh : h ∈ Subgroup.centralizer ({g} : Set G) := hle (hS ▸ Subgroup.mem_top h)
  exact (Subgroup.mem_centralizer_iff.1 hh) g rfl

omit [Finite X] in
private theorem q8II_dsub_le_of_gen {x y : X} (hxy : Subgroup.closure ({x, y} : Set X) = ⊤)
    {T : Subgroup X} [T.Normal] (h : ⁅x, y⁆ ∈ T) : ⁅(⊤ : Subgroup X), ⊤⁆ ≤ T := by
  have hπ : Function.Surjective (QuotientGroup.mk' T) := QuotientGroup.mk'_surjective T
  have hcl : Subgroup.closure ((QuotientGroup.mk' T) '' ({x, y} : Set X)) = ⊤ := by
    rw [← MonoidHom.map_closure, hxy, Subgroup.map_top_of_surjective _ hπ]
  have hxy' : (QuotientGroup.mk' T) x * (QuotientGroup.mk' T) y =
      (QuotientGroup.mk' T) y * (QuotientGroup.mk' T) x := by
    have h1 : (QuotientGroup.mk' T) ⁅x, y⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hc : ∀ g h : X ⧸ T, g * h = h * g := by
    refine q8II_comm_of_closure hcl ?_
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · rfl
    · exact hxy'
    · exact hxy'.symm
    · rfl
  refine Subgroup.commutator_le.2 (fun g _ g' _ => ?_)
  have h1 : (QuotientGroup.mk' T) ⁅g, g'⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hc _ _)
  exact (QuotientGroup.eq_one_iff _).1 h1

private theorem q8II_frattini_le {T : Subgroup X} [T.Normal] (hc : ∀ g h : X, ⁅g, h⁆ ∈ T)
    (hs : ∀ g : X, g * g ∈ T) : frattini X ≤ T := by
  have hcomm : ∀ a b : X ⧸ T, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H g =>
      induction b using QuotientGroup.induction_on with
      | H g' =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have e : (g * g')⁻¹ * (g' * g) = ⁅g'⁻¹, g⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hc _ _
  have hexp : ∀ a : X ⧸ T, a * a = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H g =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact hs g
  have hfr : frattini (X ⧸ T) = ⊥ := frattini_eq_bot_of_exponent_two hcomm hexp
  have hle := frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective T)
  rw [hfr, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hle
  exact hle

private theorem q8II_comm_le (hg : Good X c) (hgP : Good ↥(frattini X) (q8II_res c))
    (hP8 : Nat.card ↥(frattini X) = 8) : ⁅(⊤ : Subgroup X), frattini X⁆ ≤ q8II_R X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent X := hg.pgroup.isNilpotent
  let D : Subgroup X := ⁅(⊤ : Subgroup X), frattini X⁆ ⊔ q8II_R X
  have hRD : q8II_R X ≤ D := le_sup_right
  have hDP : D ≤ frattini X := sup_le (Subgroup.commutator_le_right _ _) q8II_R_le
  have hDc : ∀ x ∈ D, c x ∈ D := by
    have h1 : D ≤ D.comap c.toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro g _ p hp
        show c ⁅g, p⁆ ∈ D
        rw [map_commutatorElement]
        exact Subgroup.mem_sup_left
          (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (frattini_inv c hp))
      · intro r hr
        exact Subgroup.mem_sup_right (q8II_R_c c hr)
    exact fun x hx => h1 hx
  rcases q8II_between hgP hRD hDP hDc with h1 | h1
  · exact le_sup_left.trans h1.le
  · exfalso
    have hA : ⁅(⊤ : Subgroup X), frattini X⁆ = frattini X :=
      q8II_nongen (Subgroup.commutator_le_right _ _) h1
    have hle : ∀ n : ℕ, frattini X ≤ (⊤ : Subgroup X).lowerCentralSeries n := by
      intro n
      induction n with
      | zero => rw [Subgroup.lowerCentralSeries_zero]; exact le_top
      | succ n ih =>
        rw [Subgroup.lowerCentralSeries_succ]
        calc frattini X = ⁅(⊤ : Subgroup X), frattini X⁆ := hA.symm
          _ = ⁅frattini X, ⊤⁆ := Subgroup.commutator_comm _ _
          _ ≤ ⁅(⊤ : Subgroup X).lowerCentralSeries n, ⊤⁆ := Subgroup.commutator_mono ih le_rfl
    have hbot : frattini X ≤ ⊥ := by
      have := hle (Group.nilpotencyClass X)
      rwa [Subgroup.lowerCentralSeries_nilpotencyClass] at this
    have h2 : Nat.card ↥(frattini X) = 1 := Subgroup.card_eq_one.2 (le_bot_iff.1 hbot)
    omega

private theorem q8II_dsub_le (hg : Good X c) (hgP : Good ↥(frattini X) (q8II_res c))
    (hRcen : ∀ r ∈ q8II_R X, ∀ x : X, x * r = r * x)
    (hcomm : ⁅(⊤ : Subgroup X), frattini X⁆ ≤ q8II_R X) :
    ⁅(⊤ : Subgroup X), ⊤⁆ ≤ q8II_R X := by
  let K : Subgroup X := ⁅(⊤ : Subgroup X), ⊤⁆ ⊔ q8II_R X
  have hdP : ⁅(⊤ : Subgroup X), ⊤⁆ ≤ frattini X := dsub_le_frattini hg.pgroup
  have hRK : q8II_R X ≤ K := le_sup_right
  have hKP : K ≤ frattini X := sup_le hdP q8II_R_le
  have hKc : ∀ x ∈ K, c x ∈ K := by
    have h1 : K ≤ K.comap c.toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro g _ h _
        show c ⁅g, h⁆ ∈ K
        rw [map_commutatorElement]
        exact Subgroup.mem_sup_left
          (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
      · intro r hr
        exact Subgroup.mem_sup_right (q8II_R_c c hr)
    exact fun x hx => h1 hx
  rcases q8II_between hgP hRK hKP hKc with h1 | h1
  · exact le_sup_left.trans h1.le
  · exfalso
    have hdeq : ⁅(⊤ : Subgroup X), ⊤⁆ = frattini X := q8II_nongen hdP h1
    obtain ⟨x, hx⟩ := exists_not_mem_frattini hg
    have hxy := closure_pair hg hx
    have heP : ⁅x, c x⁆ ∈ frattini X :=
      hdP (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top (c x)))
    let S : Subgroup X := Subgroup.zpowers ⁅x, c x⁆ ⊔ q8II_R X
    have hSn : S.Normal := by
      refine ⟨fun s hs g => ?_⟩
      have h2 : S ≤ S.comap (MulAut.conj g).toMonoidHom := by
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le]
          show g * ⁅x, c x⁆ * g⁻¹ ∈ S
          have e : g * ⁅x, c x⁆ * g⁻¹ = ⁅g, ⁅x, c x⁆⁆ * ⁅x, c x⁆ := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hcomm
            (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) heP)))
            (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        · intro r hr
          show g * r * g⁻¹ ∈ S
          have e : g * r * g⁻¹ = r := by rw [hRcen r hr g, mul_inv_cancel_right]
          rw [e]
          exact Subgroup.mem_sup_right hr
      exact h2 hs
    have hxyS : ⁅x, c x⁆ ∈ S := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have hdS : ⁅(⊤ : Subgroup X), ⊤⁆ ≤ S := q8II_dsub_le_of_gen hxy hxyS
    have hPS : Subgroup.zpowers ⁅x, c x⁆ ⊔ q8II_R X = frattini X :=
      le_antisymm (sup_le ((Subgroup.zpowers_le).2 heP) q8II_R_le) (by rw [← hdeq]; exact hdS)
    have hzP : Subgroup.zpowers ⁅x, c x⁆ = frattini X :=
      q8II_nongen ((Subgroup.zpowers_le).2 heP) hPS
    have hcl : Subgroup.closure ({(⟨⁅x, c x⁆, heP⟩ : ↥(frattini X))} : Set ↥(frattini X)) = ⊤ := by
      rw [eq_top_iff]
      intro π _
      have hπ : (π : X) ∈ Subgroup.zpowers ⁅x, c x⁆ := by rw [hzP]; exact π.2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hπ
      rw [← Subgroup.zpowers_eq_closure]
      exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩
    have hrank := Group.rank_le (S := {(⟨⁅x, c x⁆, heP⟩ : ↥(frattini X))}) (by simpa using hcl)
    rw [hgP.rank_eq] at hrank
    simp at hrank

private theorem q8II_P_central (hdsub : ⁅(⊤ : Subgroup X), ⊤⁆ ≤ q8II_R X)
    (hRcen : ∀ r ∈ q8II_R X, ∀ x : X, x * r = r * x) (hRsq : ∀ r ∈ q8II_R X, r * r = 1) :
    ∀ p ∈ frattini X, ∀ x : X, x * p = p * x := by
  have hRZ : q8II_R X ≤ Subgroup.center X := fun r hr =>
    Subgroup.mem_center_iff.2 (fun g => hRcen r hr g)
  have hle : frattini X ≤ Subgroup.center X := by
    refine q8II_frattini_le (T := Subgroup.center X)
      (fun g h => hRZ (hdsub (Subgroup.commutator_mem_commutator (Subgroup.mem_top g)
        (Subgroup.mem_top h)))) (fun g => ?_)
    rw [Subgroup.mem_center_iff]
    intro h
    have hc0 : ⁅g, h⁆ ∈ q8II_R X :=
      hdsub (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))
    have e : ⁅g * g, h⁆ = (g * ⁅g, h⁆ * g⁻¹) * ⁅g, h⁆ := by
      simp only [commutatorElement_def]; group
    have e2 : g * ⁅g, h⁆ * g⁻¹ = ⁅g, h⁆ := by rw [hRcen _ hc0 g, mul_inv_cancel_right]
    have h1 : ⁅g * g, h⁆ = 1 := by rw [e, e2]; exact hRsq _ hc0
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  intro p hp x
  exact Subgroup.mem_center_iff.1 (hle hp) x

private theorem q8II_final (hgP : Good ↥(frattini X) (q8II_res c))
    (hP8 : Nat.card ↥(frattini X) = 8) (hRcard : Nat.card (frattini ↥(frattini X)) = 2)
    (hRsq : ∀ r ∈ q8II_R X, r * r = 1)
    (hPc : ∀ p ∈ frattini X, ∀ x : X, x * p = p * x) : False := by
  have hP2 : IsPGroup 2 ↥(frattini X) := hgP.pgroup
  have hcomm : ∀ π ρ : ↥(frattini X), π * ρ = ρ * π := fun π ρ =>
    Subtype.ext (hPc π.1 π.2 ρ.1).symm
  let σ : ↥(frattini X) →* ↥(frattini X) :=
    MonoidHom.mk' (fun π => π * π) (fun a b => by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hcomm b a]
        _ = a * a * (b * b) := by group)
  have hΦK : frattini ↥(frattini X) ≤ σ.ker := fun π hπ => by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (hRsq π.1 ⟨π, hπ, rfl⟩)
  have hKinv : ∀ x ∈ σ.ker, q8II_res c x ∈ σ.ker := fun x hx => by
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : x * x = 1 := hx
    show q8II_res c x * q8II_res c x = 1
    rw [← map_mul, hx', map_one]
  rcases inv_between hgP hΦK hKinv with h1 | h1
  · have hk := Subgroup.card_mul_index σ.ker
    rw [Subgroup.index_ker, hP8, h1, hRcard] at hk
    have hr : Nat.card σ.range ≤ 2 := by
      rw [← hRcard]
      exact Subgroup.card_le_of_le (by
        rintro _ ⟨π, rfl⟩
        exact mul_self_mem_frattini hP2 π)
    omega
  · have h2 : ∀ π : ↥(frattini X), π * π = 1 := fun π => by
      have : π ∈ σ.ker := by rw [h1]; trivial
      exact this
    have hbot : frattini ↥(frattini X) = ⊥ := frattini_eq_bot_of_exponent_two hcomm h2
    rw [hbot, Subgroup.card_bot] at hRcard
    omega

end Final

theorem caseII {X : Type} [Group X] [Finite X] {c : MulAut X} (hg : Good X c)
    (hfix : ∃ t : X, t ≠ 1 ∧ c t = t) (hnt : ∃ p ∈ frattini X, c p ≠ p)
    (ih : ∀ (Y : Type) [Group Y] [Finite Y] (d : MulAut Y), Nat.card Y < Nat.card X →
      Good Y d → (∃ t : Y, t ≠ 1 ∧ d t = t) → Nat.card Y = 8) : False := by
  have hgP := q8II_good hg hnt
  have hcard : Nat.card X = 4 * Nat.card ↥(frattini X) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini X)
    rwa [hg.card_V] at this
  have hP8 : Nat.card ↥(frattini X) = 8 := by
    obtain ⟨t, ht1, htc⟩ := hfix
    have htP : t ∈ frattini X := fixed_mem_frattini hg htc
    refine ih ↥(frattini X) (q8II_res c) ?_ hgP
      ⟨⟨t, htP⟩, fun h => ht1 (congrArg Subtype.val h), Subtype.ext htc⟩
    have hpos : 0 < Nat.card ↥(frattini X) := Nat.card_pos
    omega
  have hRcard := q8II_R_card hgP hP8
  obtain ⟨_, -, -, hall⟩ := q8II_R_elems hRcard
  obtain ⟨hRcen, hRsq⟩ := q8II_R_props hall
  have hcomm := q8II_comm_le hg hgP hP8
  have hdsub := q8II_dsub_le hg hgP hRcen hcomm
  have hPc := q8II_P_central hdsub hRcen hRsq
  exact q8II_final hgP hP8 hRcard hRsq hPc

end Q8

end CFSG.GH74.E2
