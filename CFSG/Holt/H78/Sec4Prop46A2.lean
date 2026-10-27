module

public import CFSG.Holt.H78.Sec4Prop46A
public import CFSG.Holt.H78.KernelSplit
public import CFSG.Holt.H78.Lemma27Alt
import CFSG.Holt.H78.Lemma27SE
import CFSG.Holt.H78.DataSocle
import CFSG.Holt.H78.Sec4AltSylow
import CFSG.Holt.H78.Sec4Box
import CFSG.Holt.H78.Sec4CCLMatch

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise commutatorElement

theorem zpowers_isPGroup_two_of_pow_eq_one {X : Type*} [Group X] {g : X} {n : ℕ}
    (h : g ^ 2 ^ n = 1) : IsPGroup 2 (Subgroup.zpowers g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])

section T6

theorem exists_mem_forall_smul_eq_of_odd {X Y : Type*} [Group X] [MulAction X Y] {B : Set Y}
    [Finite B] (hB : Odd (Nat.card B)) {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPB : P ≤ stabilizer X B) : ∃ b ∈ B, ∀ g ∈ P, g • b = b := by
  have hP' : IsPGroup 2 (P.subgroupOf (stabilizer X B)) :=
    hP.comap_of_injective _ (stabilizer X B).subtype_injective
  obtain ⟨b, hb⟩ := fixSet_nonempty_of_odd (Ω := B) hB hP'
  exact ⟨b, b.2, fun g hg => congrArg Subtype.val (hb ⟨g, hPB hg⟩ hg)⟩

theorem eq_conj_of_sq_eq_one {X : Type*} [Group X] {s t : X} (hs : s * s = 1) (ht : t * t = 1)
    {j : ℕ} (hj : (s * t) ^ (2 * j + 1) = 1) :
    s = (s * t) ^ (j + 1) * t * ((s * t) ^ (j + 1))⁻¹ := by
  have hts : t * (s * t) * t = (s * t)⁻¹ := by
    rw [mul_inv_rev, show s⁻¹ = s from inv_eq_of_mul_eq_one_right hs,
      show t⁻¹ = t from inv_eq_of_mul_eq_one_right ht, mul_assoc, mul_assoc, ht, mul_one]
  have hconj : ∀ n : ℕ, t * (s * t) ^ n * t = ((s * t) ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => rw [pow_zero, mul_one, ht, inv_one]
    | succ n ih =>
      rw [pow_succ, show t * ((s * t) ^ n * (s * t)) * t =
        (t * (s * t) ^ n * t) * (t * (s * t) * t) by
          rw [mul_assoc t, mul_assoc t (s * t) t, ← mul_assoc (t * (s * t) ^ n * t),
            mul_assoc (t * (s * t) ^ n) t t, ht]; group, ih, hts, ← mul_inv_rev, ← pow_succ',
        pow_succ]
  have h1 : t * ((s * t) ^ (j + 1))⁻¹ = (s * t) ^ (j + 1) * t := by
    have := hconj (j + 1)
    rw [← this]
    calc t * (t * (s * t) ^ (j + 1) * t) = (t * t) * (s * t) ^ (j + 1) * t := by group
      _ = (s * t) ^ (j + 1) * t := by rw [ht, one_mul]
  symm
  calc (s * t) ^ (j + 1) * t * ((s * t) ^ (j + 1))⁻¹
      = (s * t) ^ (j + 1) * (t * ((s * t) ^ (j + 1))⁻¹) := by rw [mul_assoc]
    _ = (s * t) ^ (j + 1) * ((s * t) ^ (j + 1) * t) := by rw [h1]
    _ = (s * t) ^ (2 * j + 1) * (s * t) * t := by
        rw [← mul_assoc, ← pow_add, show j + 1 + (j + 1) = 2 * j + 1 + 1 by ring, pow_succ]
    _ = s := by rw [hj, one_mul, mul_assoc, ht, mul_one]

end T6

section KnownT6

variable {K X : Type} [Group K] [Finite K] [MulAction K X] [Finite X] [FaithfulSMul K X]

theorem HoltData.socInvFixesBlocks_of_below (hK : IsStarGroup K X)
    (hB : HoltTheorem1Below (Nat.card K) (Nat.card X + 1)) (D : HoltData K X) :
    SocInvFixesBlocks D := by
  intro v hv hv2 ω hvω ω' hω'
  by_cases h1 : v = 1
  · rw [h1, one_smul]
  have hord : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) h1
  exact (D.lemma_2_4_iv hK hB (D.socPre_le_jHull hv) hord hvω).1 hv ω' hω'

omit [Finite K] [Finite X] [FaithfulSMul K X] in
theorem HoltData.mem_stabilizer_orbit_of_rho (D : HoltData K X) {g : jHull K X} {ω : X}
    (hg : ∀ i, D.ρ i g (D.coord ω i) = D.coord ω i) :
    (g : K) ∈ stabilizer K (orbit (jOddCore K X) ω) := by
  have hgω : (g : K) • ω ∈ orbit (jOddCore K X) ω := (D.coord_eq_iff _ _).mp (funext fun i => by
    rw [D.coord_smul g ω i, hg i])
  rw [mem_stabilizer_iff, smul_orbit_eq_orbit_smul, orbit_eq_iff.mpr hgω]

theorem HoltData.existsUnique_smul_eq_of_two_element (hK : IsStarGroup K X)
    (hB : HoltTheorem1Below (Nat.card K) (Nat.card X + 1)) (D : HoltData K X) {c₀ : D.ι}
    (hc₀ : ∀ k, k = c₀) (hA : D.M c₀ = alternatingGroup (D.Ψc c₀))
    (hout : IsOuterFactor (D.M c₀)) (h6 : 6 ≤ Fintype.card (D.Ψc c₀)) {ρ : jHull K X} {a : ℕ}
    (hρ : ρ ^ 2 ^ a = 1) (hρS : (ρ : K) ∉ D.socPre) {ω : X}
    (hρω : D.ρ c₀ ρ (D.coord ω c₀) = D.coord ω c₀) :
    (∀ ω' ∈ orbit (jOddCore K X) ω, ((ρ : K) * (ρ : K)) • ω' = ω') ∧
      ∃! ω', ω' ∈ orbit (jOddCore K X) ω ∧ (ρ : K) • ω' = ω' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h24 := D.socInvFixesBlocks_of_below hK hB
  set S := D.socPre.subgroupOf (jHull K X)
  have hρS' : ρ ∉ S := hρS
  have hidx : S.index = 2 := by
    have h1 : S.index ≤ 2 := D.relIndex_socPre_jHull_le_two
    have h2 : S.index ≠ 1 := fun h => hρS' (by rw [Subgroup.index_eq_one.mp h]; trivial)
    have h0 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hsocL : D.socPre ≤ D.L c₀ := sup_le (D.oddCore_le c₀) (iSup_le fun i => by rw [hc₀ i])
  set B := orbit (jOddCore K X) ω
  have hcoordB : ∀ ω' ∈ B, D.coord ω' c₀ = D.coord ω c₀ := fun ω' hω' =>
    (congrFun ((D.coord_eq_iff ω ω').mpr hω') c₀).symm
  have hP : ∀ (y : jHull K X) (b : ℕ), (y : K) ∈ D.socPre → y ^ 2 ^ b = 1 →
      D.ρ c₀ y (D.coord ω c₀) = D.coord ω c₀ → ∀ ω' ∈ B, (y : K) • ω' = ω' :=
    fun y b hy hyb hyω ω' hω' => D.smul_eq_of_mem_L_of_pow_two_pow h24 hA h6 (hsocL hy) hyb
      (by rw [hcoordB ω' hω']; exact hyω)
  have hρ2S : ((ρ ^ 2 : jHull K X) : K) ∈ D.socPre := Subgroup.sq_mem_of_index_two hidx ρ
  have hpart1 : ∀ ω' ∈ B, ((ρ : K) * (ρ : K)) • ω' = ω' := fun ω' hω' => by
    have := hP (ρ ^ 2) a hρ2S (by rw [← pow_mul, mul_comm, pow_mul, hρ, one_pow])
      (by rw [map_pow, sq, Equiv.Perm.mul_apply, hρω, hρω]) ω' hω'
    rwa [pow_two, Subgroup.coe_mul] at this
  refine ⟨hpart1, ?_⟩
  have hρB := D.mem_stabilizer_orbit_of_rho (g := ρ) (ω := ω) fun i => by rw [hc₀ i]; exact hρω
  have hB2 : IsPGroup 2 (Subgroup.zpowers (ρ : K)) :=
    zpowers_isPGroup_two_of_pow_eq_one (n := a)
      (by rw [← Subgroup.coe_pow, hρ, Subgroup.coe_one])
  obtain ⟨b', hb'B, hb'⟩ := exists_mem_forall_smul_eq_of_odd (B := B)
    (odd_card_orbit_jOddCore ω) hB2 (Subgroup.zpowers_le.mpr hρB)
  have := hK.isPretransitive
  obtain ⟨u, hu⟩ := longInvAt_nonempty_of_mem_longInv D.t_mem b'
  set u' : jHull K X := ⟨u, mem_jHull_of_mem_longInv hu.1⟩
  have hb'c : D.coord b' = D.coord ω := ((D.coord_eq_iff ω b').mpr hb'B).symm
  have hu'coord : ∀ i, D.ρ i u' (D.coord ω i) = D.coord ω i := fun i => by
    rw [← hb'c, ← D.coord_smul u' b' i]
    exact congrFun (congrArg D.coord hu.2) i
  have huB := D.mem_stabilizer_orbit_of_rho hu'coord
  have hu'S : u' ∉ S := fun h =>
    (D.rho_mem_M_iff hu.1 c₀).mp (D.rho_mem_M_of_mem_socPre (h := u')
      (Subgroup.mem_subgroupOf.mp h) c₀) hout
  have hyS : ρ * u' ∈ S :=
    (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hρS' hu'S)
  obtain ⟨e, m, hm, hym⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (ρ * u')).ne'
  have hym1 : ∀ ω' ∈ B, (((ρ * u') ^ m : jHull K X) : K) • ω' = ω' := by
    refine hP ((ρ * u') ^ m) e (S.pow_mem hyS m) ?_ ?_
    · rw [← pow_mul, mul_comm, ← hym, pow_orderOf_eq_one]
    · rw [map_pow, map_mul]
      exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self
        (by rw [Equiv.Perm.mul_apply, hu'coord c₀, hρω]) m
  set π := MulAction.toPermHom (stabilizer K B) B
  set sρ := π ⟨ρ, hρB⟩
  set tu := π ⟨u, huB⟩
  have hs : sρ * sρ = 1 := Equiv.ext fun x => Subtype.ext (by
    show (ρ : K) • (ρ : K) • (x : X) = x
    rw [← mul_smul]
    exact hpart1 x x.2)
  have ht : tu * tu = 1 := Equiv.ext fun x => Subtype.ext (by
    show u • u • (x : X) = x
    rw [← mul_smul, mul_self_eq_one_of_mem_longInv hu.1, one_smul])
  obtain ⟨j, rfl⟩ := hm
  have hj : (sρ * tu) ^ (2 * j + 1) = 1 := Equiv.ext fun x => Subtype.ext (by
    rw [← map_mul, ← map_pow]
    exact hym1 x x.2)
  have hconj := eq_conj_of_sq_eq_one hs ht hj
  set c := (sρ * tu) ^ (j + 1)
  have htb : tu ⟨b', hb'B⟩ = ⟨b', hb'B⟩ := Subtype.ext hu.2
  have hcinv : ∀ y : B, c⁻¹ (c y) = y := fun y => Equiv.Perm.inv_eq_iff_eq.mpr rfl
  have hcinv' : ∀ y : B, c (c⁻¹ y) = y := fun y => (Equiv.eq_symm_apply c).mp rfl
  refine ⟨(c ⟨b', hb'B⟩ : X), ⟨(c ⟨b', hb'B⟩).2, ?_⟩, ?_⟩
  · have h1 : sρ (c ⟨b', hb'B⟩) = c ⟨b', hb'B⟩ := by
      rw [hconj, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hcinv, htb]
    exact congrArg Subtype.val h1
  · rintro ω' ⟨hω'B, hω'⟩
    have hfix : sρ ⟨ω', hω'B⟩ = ⟨ω', hω'B⟩ := Subtype.ext hω'
    rw [hconj, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at hfix
    have h1 : tu (c⁻¹ ⟨ω', hω'B⟩) = c⁻¹ ⟨ω', hω'B⟩ := by
      have := congrArg (⇑c⁻¹) hfix
      rwa [hcinv] at this
    have h2 : ((c⁻¹ ⟨ω', hω'B⟩ : B) : X) = b' :=
      hu.1.2.unique (congrArg Subtype.val h1) hu.2
    have h3 : c⁻¹ ⟨ω', hω'B⟩ = ⟨b', hb'B⟩ := Subtype.ext h2
    have h4 : (⟨ω', hω'B⟩ : B) = c ⟨b', hb'B⟩ := by rw [← h3, hcinv']
    exact congrArg Subtype.val h4

end KnownT6

section Section

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

omit [Finite G] in
theorem Sec4Setting.exists_longInv_mul_eq_of_mem_normalizer (hS : Sec4Setting G Ω)
    {U : Subgroup G} (hU : IsPGroup 2 U) (h3 : 3 ≤ Nat.card (fixSet Ω U)) {v w : G}
    (hvU : v ∈ Subgroup.centralizer (U : Set G)) (hw : w ∈ longInv G Ω)
    (hwv : w * v ∈ longInv G Ω) (hwU : w ∈ Subgroup.normalizer (U : Set G)) :
    ∃ c₁ ∈ longInv G Ω, ∃ c₂ ∈ longInv G Ω, c₁ ∈ Subgroup.centralizer (U : Set G) ∧
      c₂ ∈ Subgroup.centralizer (U : Set G) ∧ ∀ ω ∈ fixSet Ω U, v • ω = c₁ • c₂ • ω := by
  have hwvU : w * v ∈ Subgroup.normalizer (U : Set G) :=
    mul_mem hwU (Subgroup.centralizer_le_normalizer _ hvU)
  obtain ⟨c₁, hc₁, hc₁U, hc₁w⟩ := hS.frattini h3 hU (le_fixingSubgroup_fixSet U) hw
    (normalizer_le_stabilizer_fixSet U hwU)
  obtain ⟨c₂, hc₂, hc₂U, hc₂w⟩ := hS.frattini h3 hU (le_fixingSubgroup_fixSet U) hwv
    (normalizer_le_stabilizer_fixSet U hwvU)
  refine ⟨c₁, hc₁, c₂, hc₂, hc₁U, hc₂U, fun ω hω => ?_⟩
  have hwvω : (w * v) • ω ∈ fixSet Ω U := smul_mem_fixSet_of_mem_normalizer hwvU hω
  rw [hc₂w ω hω, hc₁w _ hwvω, ← mul_smul, ← mul_assoc, mul_self_eq_one_of_mem_longInv hw,
    one_mul]

theorem Sec4Setting.restrict_mem_socPre [FaithfulSMul G Ω] (hS : Sec4Setting G Ω)
    {U : Subgroup G} (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥) (h3 : 3 ≤ Nat.card (fixSet Ω U))
    {v w : G} (hvU : v ∈ Subgroup.centralizer (U : Set G)) (hw : w ∈ longInv G Ω)
    (hwv : w * v ∈ longInv G Ω) (hwU : w ∈ Subgroup.normalizer (U : Set G))
    (D : HoltData (centralizerImage Ω U) (fixSet Ω U)) :
    (restrictCentralizer Ω U ⟨v, hvU⟩ : centralizerImage Ω U) ∈ D.socPre := by
  obtain ⟨c₁, hc₁, c₂, hc₂, hc₁U, hc₂U, hv⟩ :=
    hS.exists_longInv_mul_eq_of_mem_normalizer hU h3 hvU hw hwv hwU
  have h1 : restrictCentralizer Ω U ⟨c₁, hc₁U⟩ ∈ longInv (centralizerImage Ω U) (fixSet Ω U) :=
    (hS.mem_longInv_centralizerImage_iff hU h3 _).mpr ⟨c₁, hc₁, hc₁U, fun _ => rfl⟩
  have h2 : restrictCentralizer Ω U ⟨c₂, hc₂U⟩ ∈ longInv (centralizerImage Ω U) (fixSet Ω U) :=
    (hS.mem_longInv_centralizerImage_iff hU h3 _).mpr ⟨c₂, hc₂, hc₂U, fun _ => rfl⟩
  have heq : restrictCentralizer Ω U ⟨v, hvU⟩ =
      restrictCentralizer Ω U ⟨c₁, hc₁U⟩ * restrictCentralizer Ω U ⟨c₂, hc₂U⟩ :=
    Subtype.ext (Equiv.ext fun ω => Subtype.ext (hv ω ω.2))
  rw [heq]
  exact D.mul_mem_socPre_of_mem_longInv (hS.star_centralizerImage hU h3)
    (hS.holtTheorem1Below_centralizerImage hU hU1 h3) h1 h2

theorem exists_fusionIsSylowIn_ge_le_normalizer {X : Type*} [Group X] [Finite X]
    {V F T : Subgroup X} (hV : IsPGroup 2 V) (hVF : V ≤ F) (hT : IsPGroup 2 T)
    (hTF : T ≤ Subgroup.normalizer (F : Set X)) (hTV : T ≤ Subgroup.normalizer (V : Set X)) :
    ∃ W : Subgroup X, V ≤ W ∧ fusionIsSylowIn 2 W F ∧ T ≤ Subgroup.normalizer (W : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : IsPGroup 2 (V ⊔ T : Subgroup X) := hV.to_sup_of_normal_left' hT hTV
  obtain ⟨Q, hBQ, hQ⟩ := exists_fusionIsSylowIn_ge hB (sup_le_sup_right hVF T)
  have hN : (F.subgroupOf (F ⊔ T)).Normal :=
    Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left |>.mpr
      (sup_le Subgroup.le_normalizer hTF)
  refine ⟨Q ⊓ F, le_inf (le_sup_left.trans hBQ) hVF,
    fusionIsSylowIn_inf_of_normal_subgroupOf hQ le_sup_left hN, fun s hs => ?_⟩
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer (hBQ (Subgroup.mem_sup_right hs)), hTF hs⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem mem_normalizer_fixingSubgroup_fixSet {U : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (U : Set G)) :
    h ∈ Subgroup.normalizer (fixingSubgroup G (fixSet Ω U) : Set G) := by
  have key : ∀ (h : G), h ∈ Subgroup.normalizer (U : Set G) → ∀ g : G,
      g ∈ fixingSubgroup G (fixSet Ω U) → h * g * h⁻¹ ∈ fixingSubgroup G (fixSet Ω U) :=
    fun h hh g hg => by
      rw [mem_fixingSubgroup_iff] at hg ⊢
      intro ω hω
      have hω' : h⁻¹ • ω ∈ fixSet Ω U := smul_mem_fixSet_of_mem_normalizer (inv_mem hh) hω
      rw [mul_smul, mul_smul, hg _ hω', smul_inv_smul]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key h hh g, fun hg => ?_⟩
  have := key h⁻¹ (inv_mem hh) _ hg
  rwa [inv_inv, show h⁻¹ * (h * g * h⁻¹) * h = g by group] at this

theorem Sec4Setting.exists_sylow_centralizer_mul (hS : Sec4Setting G Ω) {U : Subgroup G}
    (hU : IsPGroup 2 U) (h3 : 3 ≤ Nat.card (fixSet Ω U)) {v w : G} (hv2 : v * v = 1)
    (hvU : v ∈ Subgroup.centralizer (U : Set G)) (hw : w ∈ longInv G Ω)
    (hwv : w * v ∈ longInv G Ω) (hwU : w ∈ Subgroup.normalizer (U : Set G)) {T : Subgroup G}
    (hT : IsPGroup 2 T) (hvT : v ∈ T) (hTU : T ≤ Subgroup.normalizer (U : Set G)) :
    ∃ W : Subgroup G, U ≤ W ∧ fusionIsSylowIn 2 W (fixingSubgroup G (fixSet Ω U)) ∧
      T ≤ Subgroup.normalizer (W : Set G) ∧
      ∃ x ∈ Subgroup.centralizer (W : Set G), IsPGroup 2 (Subgroup.zpowers x) ∧
        (∀ ω ∈ fixSet Ω U, x • ω = v • ω) ∧
        ∀ c ∈ Subgroup.centralizer (W : Set G), Commute c x → Commute c v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv2' : IsPGroup 2 (Subgroup.zpowers v) :=
    zpowers_isPGroup_two_of_pow_eq_one (n := 1) (by rw [pow_one, sq]; exact hv2)
  obtain ⟨W, hUW, hW, hTW⟩ := exists_fusionIsSylowIn_ge_le_normalizer hU
    (le_fixingSubgroup_fixSet U) hT
    (fun h hh => mem_normalizer_fixingSubgroup_fixSet (Ω := Ω) (hTU hh))
    hTU
  have hvW : v ∈ Subgroup.normalizer (W : Set G) := hTW hvT
  obtain ⟨c₁, hc₁, c₂, hc₂, hc₁U, hc₂U, hv⟩ :=
    hS.exists_longInv_mul_eq_of_mem_normalizer hU h3 hvU hw hwv hwU
  obtain ⟨c₁', -, hc₁W, hc₁'⟩ := hS.frattini h3 hW.2.1 hW.1 hc₁
    (centralizer_le_stabilizer_fixSet U hc₁U)
  obtain ⟨c₂', -, hc₂W, hc₂'⟩ := hS.frattini h3 hW.2.1 hW.1 hc₂
    (centralizer_le_stabilizer_fixSet U hc₂U)
  set ℓ := c₁' * c₂'
  have hℓ : ℓ ∈ Subgroup.centralizer (W : Set G) := mul_mem hc₁W hc₂W
  have hℓv : ∀ ω ∈ fixSet Ω U, ℓ • ω = v • ω := fun ω hω => by
    have hc₂ω : c₂ • ω ∈ fixSet Ω U :=
      smul_mem_fixSet_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ hc₂U) hω
    rw [hv ω hω, mul_smul, hc₂' ω hω, hc₁' _ hc₂ω]
  have hkF : ℓ⁻¹ * v ∈ fixingSubgroup G (fixSet Ω U) := (mem_fixingSubgroup_iff G).mpr
    fun ω hω => by rw [mul_smul, ← hℓv ω hω, inv_smul_smul]
  have hkW : ℓ⁻¹ * v ∈ Subgroup.normalizer (W : Set G) :=
    mul_mem (inv_mem (Subgroup.centralizer_le_normalizer _ hℓ)) hvW
  obtain ⟨m, hm, hkm⟩ := exists_odd_pow_mem_of_fusionIsSylowIn hW hkF hkW
  obtain ⟨y, hy, x, hx, hyx⟩ := exists_mem_mul_mem_centralizer hv2 hℓ hkW hm hkm (by group)
  refine ⟨W, hUW, hW, hTW, x, hx, ?_, fun ω hω => ?_, fun c hc hcx => ?_⟩
  · have hsup : IsPGroup 2 (W ⊔ Subgroup.zpowers v : Subgroup G) :=
      hW.2.1.to_sup_of_normal_left' hv2' (Subgroup.zpowers_le.mpr hvW)
    refine hsup.to_le (Subgroup.zpowers_le.mpr ?_)
    rw [show x = y⁻¹ * v by rw [hyx]; group]
    exact mul_mem (Subgroup.mem_sup_left (inv_mem hy))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  · have hxω : x • ω ∈ fixSet Ω U := smul_mem_fixSet_of_mem_normalizer
      (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hUW hx)) hω
    rw [hyx, mul_smul, (mem_fixingSubgroup_iff G).mp (hW.1 hy) _ hxω]
  · rw [hyx]
    exact (Commute.symm (Subgroup.mem_centralizer_iff.mp hc y hy)).mul_right hcx

omit [Fintype Ω] [DecidableEq Ω] in
theorem exists_commute_eqOn_of_odd_twoPointKernel {α β γ : Ω} (hγ : γ ∈ holtDelta G Ω α β)
    (hodd : Odd (Nat.card (twoPointKernel G Ω α β))) {v g : G}
    (hv : v ∈ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v))
    (hg : g ∈ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ)
    (hcomm : ∀ δ ∈ holtDelta G Ω α β, g • v • δ = v • g • δ) :
    ∃ c ∈ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ, Commute c v ∧
      ∀ δ ∈ holtDelta G Ω α β, c • δ = g • δ := by
  set H := stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ
  have hHΔ : ∀ h ∈ H, ∀ δ ∈ holtDelta G Ω α β, h • δ ∈ holtDelta G Ω α β := fun h hh δ hδ => by
    have h1 := stabilizer_pair_le (G := G) α β
      (stabilizer_inf_le_stabilizer_pair α β (Subgroup.mem_inf.mp hh).1)
    rw [mem_stabilizer_iff] at h1
    rw [← h1]; exact Set.smul_mem_smul_set hδ
  have hN : ((twoPointKernel G Ω α β).subgroupOf H).Normal := normal_twoPointKernel_subgroupOf hγ
  have hNodd : Odd (Nat.card ((twoPointKernel G Ω α β).subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (twoPointKernel_le_of_mem hγ)).toEquiv]
  have hx2 : IsPGroup 2 (Subgroup.zpowers (⟨v, hv⟩ : H)) := by
    have h1 := hv2.comap_of_injective H.subtype H.subtype_injective
    exact h1.to_le (Subgroup.zpowers_le.mpr (Subgroup.mem_comap.mpr (Subgroup.mem_zpowers v)))
  have hcomm' : (⟨g, hg⟩ : H) * ⟨v, hv⟩ * (⟨g, hg⟩ : H)⁻¹ * (⟨v, hv⟩ : H)⁻¹ ∈
      (twoPointKernel G Ω α β).subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    refine ⟨Subgroup.mem_inf.mp (H.mul_mem (H.mul_mem (H.mul_mem hg hv) (H.inv_mem hg))
      (H.inv_mem hv)) |>.1, (mem_fixingSubgroup_iff G).mpr fun δ hδ => ?_⟩
    have hδ' : g⁻¹ • v⁻¹ • δ ∈ holtDelta G Ω α β :=
      hHΔ _ (H.inv_mem hg) _ (hHΔ _ (H.inv_mem hv) δ hδ)
    show (g * v * g⁻¹ * v⁻¹) • δ = δ
    have := hcomm _ hδ'
    rw [smul_inv_smul, smul_inv_smul] at this
    rw [mul_smul, mul_smul, mul_smul]
    exact this
  obtain ⟨c, hcx, hcg⟩ := exists_commute_inv_mul_mem _ hNodd hx2 hcomm'
  refine ⟨c, c.2, ?_, fun δ hδ => ?_⟩
  · have := congrArg Subtype.val hcx.eq
    exact this
  · have h1 := (mem_fixingSubgroup_iff G).mp (Subgroup.mem_subgroupOf.mp hcg).2 δ hδ
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_eq_iff] at h1
    exact h1.symm

omit [Fintype Ω] [DecidableEq Ω] in
theorem fixSet_inter_subset_of_fusionIsSylowIn {𝒞 V E : Subgroup G} (hV : fusionIsSylowIn 2 V 𝒞)
    (hE : IsPGroup 2 E) (hE𝒞 : E ≤ 𝒞) {Δ Λ : Set Ω} (h𝒞Δ : 𝒞 ≤ stabilizer G Δ)
    (h𝒞Λ : 𝒞 ≤ fixingSubgroup G Λ) (hEΛ : ∀ δ ∈ Δ, δ ∈ fixSet Ω E → δ ∈ Λ) :
    (E ≠ ⊥ → V ≠ ⊥) ∧ ∀ δ ∈ Δ, δ ∈ fixSet Ω V → δ ∈ Λ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hER, hR⟩ := exists_fusionIsSylowIn_ge hE hE𝒞
  obtain ⟨k, hk, hkR⟩ := exists_mem_conj_of_fusionIsSylowIn hV hR
  refine ⟨fun hE1 hV1 => hE1 (eq_bot_iff.mpr fun x hx => ?_), fun δ hδ hδV => ?_⟩
  · have := (hkR x).mp (hER hx)
    rw [hV1, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot, show x = k * (k⁻¹ * x * k) * k⁻¹ by group, this, mul_one,
      mul_inv_cancel]
  · have hkδ : k • δ ∈ Δ := by
      have h1 := h𝒞Δ hk
      rw [mem_stabilizer_iff] at h1
      rw [← h1]; exact Set.smul_mem_smul_set hδ
    have hkδE : k • δ ∈ fixSet Ω E := fun x hx => by
      have hxV := (hkR x).mp (hER hx)
      rw [show x • k • δ = k • ((k⁻¹ * x * k) • δ) by simp only [mul_smul, smul_inv_smul],
        hδV _ hxV]
    have h1 := hEΛ _ hkδ hkδE
    have h2 := (mem_fixingSubgroup_iff G).mp (h𝒞Λ hk) _ h1
    rw [smul_left_cancel_iff] at h2
    rw [← h2]; exact h1

omit [Fintype Ω] [DecidableEq Ω] in
theorem exists_ne_one_commute_of_mem_normalizer {T : Subgroup G} (hT : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) {s : G} (hs : IsPGroup 2 (Subgroup.zpowers s))
    (hsT : s ∈ Subgroup.normalizer (T : Set G)) : ∃ z ∈ T, z ≠ 1 ∧ Commute z s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := T ⊔ Subgroup.zpowers s
  have hB : IsPGroup 2 B := hT.to_sup_of_normal_left' hs (Subgroup.zpowers_le.mpr hsT)
  have : Group.IsNilpotent B := hB.isNilpotent
  have hN : (T.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hsT))
  have hne : T.subgroupOf B ≠ ⊥ := fun h => hT1 (by
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, (le_sup_left : T ≤ B) hx⟩ : B) ∈ T.subgroupOf B := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this))
  obtain ⟨⟨⟨z, hzB⟩, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨z, (Subgroup.mem_inf.mp hz).1, fun h => hz1 (Subtype.ext (Subtype.ext h)), ?_⟩
  have hc := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hz).2
    ⟨s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s)⟩
  exact (congrArg Subtype.val hc).symm

end Section

section Components

variable {K X : Type*} [Group K] [MulAction K X] (D : HoltData K X)

theorem HoltData.exists_mem_L_rho_eq {i : D.ι} {m : Equiv.Perm (D.Ψc i)} (hm : m ∈ D.M i) :
    ∃ ℓ : jHull K X, (ℓ : K) ∈ D.L i ∧ D.ρ i ℓ = m ∧ ∀ k, k ≠ i → D.ρ k ℓ = 1 := by
  obtain ⟨ℓ, hℓ, hρ⟩ := D.mem_M.mp hm
  exact ⟨ℓ, hℓ, hρ, fun k hk => D.rho_eq_one_of_mem_L (Ne.symm hk) hℓ⟩

theorem HoltData.liftsCommute_of_rho_eq_one {x : jHull K X} (hx : (x : K) ∈ D.socPre)
    {i : D.ι} {ℓ : jHull K X} (hℓ : ∀ k, k ≠ i → D.ρ k ℓ = 1) (e : ℕ)
    (he : (D.ρ i ℓ ^ e)⁻¹ * D.ρ i x = 1) :
    LiftsCommute (psiHom D).range (psiHom D ℓ) (psiHom D x) := by
  classical
  set P : Subgroup (∀ k, Equiv.Perm (D.Ψc k)) :=
    Subgroup.pi Set.univ fun k => if k = i then ⊥ else D.M k
  have hPR : P ≤ (psiHom D).range := by
    intro p hp
    have hm : ∀ k ∈ Finset.univ.erase i, p k ∈ D.M k := fun k hk => by
      simpa [Finset.ne_of_mem_erase hk] using hp k (Set.mem_univ k)
    obtain ⟨h, hh, hρ⟩ := D.exists_mem_finsetSup_rho_eq _ p hm
    refine ⟨h, funext fun k => ?_⟩
    by_cases hk : k = i
    · subst hk
      have h1 := (D.rho_eq_one_of_mem_sup_finsetSup (Finset.univ.erase k) (h := h)
        (Subgroup.mem_sup_right hh)).1 k (Finset.notMem_erase k _)
      have h2 : p k = 1 := by simpa using hp k (Set.mem_univ k)
      exact h1.trans h2.symm
    · exact hρ k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
  have hPq : ∀ p ∈ P, Commute (psiHom D ℓ) p := fun p hp => funext fun k => by
    show D.ρ k ℓ * p k = p k * D.ρ k ℓ
    by_cases hk : k = i
    · subst hk
      have h2 : p k = 1 := by simpa using hp k (Set.mem_univ k)
      rw [h2, mul_one, one_mul]
    · rw [hℓ k hk, one_mul, mul_one]
  have hPP : ⁅P, P⁆ = P := by
    rw [Subgroup.commutator_pi_pi_of_finite]
    congr 1
    funext k
    by_cases hk : k = i
    · simp [hk]
    · simp only [hk, ite_false]
      have := D.isPerfect_M k
      exact Subgroup.isPerfect_iff.mp this
  refine liftsCommute_of_mem_commutator hPR hPq e ?_
  rw [hPP]
  intro k _
  show ((D.ρ k ℓ ^ e)⁻¹ * D.ρ k x) ∈ (if k = i then ⊥ else D.M k)
  by_cases hk : k = i
  · subst hk; simpa using he
  · simp only [hk, ite_false, hℓ k hk, one_pow, inv_one, one_mul]
    exact D.rho_mem_M_of_mem_socPre (h := x) hx k

theorem LiftsCommute.mul {Q : Type} [Group Q] {R : Subgroup Q} {q₁ q₂ g : Q} (hq₁ : q₁ ∈ R)
    (h₁ : LiftsCommute R q₁ g) (h₂ : LiftsCommute R q₂ g) : LiftsCommute R (q₁ * q₂) g := by
  intro Y _ π hker hrange a b ha hb
  obtain ⟨a₁, ha₁⟩ : q₁ ∈ π.range := hrange ▸ hq₁
  have hk : π (a₁⁻¹ * a) = q₂ := by rw [map_mul, map_inv, ha₁, ha]; group
  rw [show a = a₁ * (a₁⁻¹ * a) by group]
  exact (h₁ Y π hker hrange a₁ b ha₁ hb).mul_left (h₂ Y π hker hrange _ b hk hb)

theorem LiftsCommute.closure {Q : Type} [Group Q] {R : Subgroup Q} {S : Set Q} (hSR : S ⊆ R)
    {g : Q} (hS : ∀ q ∈ S, LiftsCommute R q g) :
    ∀ q ∈ Subgroup.closure S, LiftsCommute R q g := by
  intro q hq
  have hqR : q ∈ R := (Subgroup.closure_le R).mpr hSR hq
  induction hq using Subgroup.closure_induction with
  | mem q hq => exact hS q hq
  | one =>
    intro Y _ π hker _ a b ha _
    exact (Subgroup.mem_center_iff.mp (hker (by rw [MonoidHom.mem_ker, ha])) b).symm
  | mul q₁ q₂ h₁ _ ih₁ ih₂ =>
    exact LiftsCommute.mul ((Subgroup.closure_le R).mpr hSR h₁) (ih₁ ((Subgroup.closure_le R).mpr
      hSR h₁)) (ih₂ ((Subgroup.closure_le R).mpr hSR ‹_›))
  | inv q h ih =>
    have := (ih ((Subgroup.closure_le R).mpr hSR h)).zpow ((Subgroup.closure_le R).mpr hSR h) (-1)
    rwa [zpow_neg, zpow_one] at this

theorem HoltData.smul_eq_of_rho_eq (h24 : SocInvFixesBlocks D) {y : jHull K X}
    (hy : (y : K) ∈ D.socPre) (hy2 : y * y = 1) {ω : X}
    (hω : ∀ i, D.ρ i y (D.coord ω i) = D.coord ω i) : (y : K) • ω = ω := by
  have h1 : (y : K) • ω ∈ orbit (jOddCore K X) ω := (D.coord_eq_iff _ _).mp (funext fun i => by
    rw [D.coord_smul y ω i, hω i])
  exact h24 y hy (by rw [← Subgroup.coe_mul, hy2, Subgroup.coe_one]) ω h1 ω (mem_orbit_self ω)

theorem mul_self_eq_one_of_mem_closure {M : Type*} [Group M] {S : Set M}
    (hS : ∀ s ∈ S, s * s = 1) (hcomm : ∀ s ∈ S, ∀ t ∈ S, Commute s t) :
    ∀ q ∈ Subgroup.closure S, q * q = 1 := by
  have hc : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set M) := by
    have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := (Subgroup.closure_le _).mpr
      fun σ hσ => Subgroup.mem_centralizer_iff.mpr fun τ hτ => (hcomm τ hτ σ hσ).eq
    have h2 : S ⊆ (Subgroup.centralizer (Subgroup.closure S : Set M) : Set M) :=
      fun σ hσ => Subgroup.mem_centralizer_iff.mpr
        fun τ hτ => (Subgroup.mem_centralizer_iff.mp (h1 hτ) σ hσ).symm
    exact (Subgroup.closure_le _).mpr h2
  intro q hq
  induction hq using Subgroup.closure_induction with
  | mem q hq => exact hS q hq
  | one => rw [mul_one]
  | mul σ τ hσ hτ ihσ ihτ =>
    have hστ : τ * σ = σ * τ := Subgroup.mem_centralizer_iff.mp (hc hσ) τ hτ
    calc σ * τ * (σ * τ) = σ * (τ * σ) * τ := by group
      _ = σ * σ * (τ * τ) := by rw [hστ]; group
      _ = 1 := by rw [ihσ, ihτ, mul_one]
  | inv σ hσ ih => rw [← mul_inv_rev, ih, inv_one]

theorem isPGroup_of_mul_self {M : Type*} [Group M] {H : Subgroup M}
    (hH : ∀ q ∈ H, q * q = 1) : IsPGroup 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.iff_orderOf.mpr fun σ => ?_
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one
    (show σ ^ 2 ^ 1 = 1 by rw [pow_one, sq]; exact Subtype.ext (hH σ σ.2)))
  exact ⟨b, hb⟩

end Components

section CCLSection

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.exists_ccl (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (A : CaseAData G Ω α β)
    {U : Subgroup G} (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥) (h3 : 3 ≤ Nat.card (fixSet Ω U))
    {a b : fixSet Ω U} (ha : (a : Ω) = α) (hb : (b : Ω) = β) (Λc : ∀ i, Set (A.D.Ψc i))
    (hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω U ↔ ∀ i, A.D.coord δ i ∈ Λc i)
    (h5 : ∀ i, (Λc i).Nontrivial → 5 ≤ (Λc i).ncard)
    (DK : HoltData (centralizerImage Ω U) (fixSet Ω U)) :
    ∃ c : {i // (Λc i).Nontrivial} → DK.ι, Function.Injective c ∧
      (∀ j, factorImage _ _ (DK.L (c j)) (DK.ρ (c j)) = alternatingGroup (DK.Ψc (c j)) ∧
        Fintype.card (DK.Ψc (c j)) = (Λc j).ncard + 2 ∧ DK.coord a (c j) ≠ DK.coord b (c j)) ∧
      (∀ j (δ δ' : fixSet Ω U) (hδ : (δ : Ω) ∈ holtDelta G Ω α β)
          (hδ' : (δ' : Ω) ∈ holtDelta G Ω α β),
        (DK.coord δ (c j) = DK.coord δ' (c j) ↔
          A.D.coord ⟨δ, hδ⟩ j = A.D.coord ⟨δ', hδ'⟩ j) ∧
        DK.coord δ (c j) ≠ DK.coord a (c j) ∧ DK.coord δ (c j) ≠ DK.coord b (c j)) ∧
      (∀ k, k ∉ Set.range c → ∀ δ : fixSet Ω U, (δ : Ω) ∈ holtDelta G Ω α β →
        DK.coord δ k = DK.coord a k ∧ DK.coord b k = DK.coord a k) := by
  classical
  have hab : a ≠ b := fun h => hαβ (by rw [← ha, ← hb, h])
  obtain ⟨e, he, hcoord, hreal⟩ := hS.exists_boxEquiv_ccl hαβ A.D A.oddCore_eq_bot A.alt hU ha hb
    Λc hbox
    (p := fun i => (Λc i).Nontrivial) (fun _ h => h) (fun _ h => Set.not_nontrivial_iff.mp h)
  have h5' : ∀ j : {i // (Λc i).Nontrivial}, 5 ≤ Fintype.card (Λc j) := fun j => by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; exact h5 j j.2
  obtain ⟨c, hinj, hc1, hpar, -⟩ := HoltData.ccl (hS.star_centralizerImage hU h3)
    (hS.holtTheorem1Below_centralizerImage hU hU1 h3) DK hab
    (ι' := {i // (Λc i).Nontrivial}) (Λc := fun j => (Λc j.1 : Type)) e h5' hcoord hreal
  have hmem : ∀ (δ : fixSet Ω U), (δ : Ω) ∈ holtDelta G Ω α β →
      δ ∈ holtDelta (centralizerImage Ω U) (fixSet Ω U) a b := fun δ hδ => by
    rw [hS.mem_holtDelta_centralizerImage_iff hU h3 hab, ha, hb]; exact hδ
  refine ⟨c, hinj, fun j => ⟨(hc1 j).1, ?_, (hc1 j).2.2.1⟩, fun j δ δ' hδ hδ' => ?_,
    fun k hk δ hδ => hpar k hk ⟨δ, hmem δ hδ⟩⟩
  · rw [(hc1 j).2.1, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  · obtain ⟨hiff, hne⟩ := (hc1 j).2.2.2 ⟨δ, hmem δ hδ⟩ ⟨δ', hmem δ' hδ'⟩
    refine ⟨?_, hne⟩
    rw [show DK.coord δ (c j) = DK.coord ((⟨δ, hmem δ hδ⟩ :
      holtDelta (centralizerImage Ω U) (fixSet Ω U) a b) : fixSet Ω U) (c j) from rfl, hiff,
      Subtype.ext_iff, he _ ⟨δ, hδ⟩ rfl j, he _ ⟨δ', hδ'⟩ rfl j]

end CCLSection

section Start

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_eq_of_mem_p46Orbit {β : Ω} (hβ : β ∈ p46Orbit G Ω v P α) : v • β = β := by
  obtain ⟨p, -, a, -, rfl⟩ := hβ
  exact (p • a).2 v (Subgroup.mem_zpowers v)

namespace CaseAData

variable {β : Ω} (A : CaseAData G Ω α β)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem coord_injective : Function.Injective A.D.coord :=
  A.D.coord_injective A.oddCore_eq_bot

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem coord_bijective_of_card_eq_one (h1 : Fintype.card A.D.ι = 1) (i : A.D.ι) :
    Function.Bijective fun δ : holtDelta G Ω α β => A.D.coord δ i := by
  have hi : ∀ j, j = i := fun j => Fintype.card_le_one_iff.mp h1.le _ _
  refine ⟨fun δ δ' h => A.coord_injective (funext fun j => by rw [hi j]; exact h), fun x => ?_⟩
  obtain ⟨δ, hδ⟩ := A.D.coord_surjective (fun j => (hi j).symm ▸ x)
  exact ⟨δ, by show A.D.coord δ i = x; rw [hδ]⟩

omit [Finite G] [Fintype Ω] [FaithfulSMul G Ω] in
theorem alternatingGroup_le_twoPointSection [Fintype (holtDelta G Ω α β)]
    (h1 : Fintype.card A.D.ι = 1) :
    alternatingGroup (holtDelta G Ω α β) ≤ twoPointSection G Ω α β := by
  classical
  obtain ⟨i⟩ : Nonempty A.D.ι := Fintype.card_pos_iff.mp (by omega)
  set e := Equiv.ofBijective _ (A.coord_bijective_of_card_eq_one h1 i)
  intro σ hσ
  have hσ' : e.permCongr σ ∈ factorImage _ _ (A.D.L i) (A.D.ρ i) := by
    rw [A.alt i, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_permCongr]
    exact hσ
  obtain ⟨h, -, hρ⟩ := mem_factorImage.mp hσ'
  have heq : ((h : twoPointSection G Ω α β) : Equiv.Perm (holtDelta G Ω α β)) = σ := by
    ext δ
    have h2 : e (h • δ) = e (σ δ) := by
      show A.D.coord ((h : twoPointSection G Ω α β) • δ) i = _
      rw [A.D.coord_smul h δ i, hρ]
      simp [e, Equiv.permCongr_apply]
    exact congrArg Subtype.val (e.injective h2)
  rw [← heq]
  exact (h : twoPointSection G Ω α β).2

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem card_le_card_holtDelta (δ₀ : holtDelta G Ω α β) (i : A.D.ι) :
    Fintype.card (A.D.Ψc i) ≤ Nat.card (holtDelta G Ω α β) := by
  classical
  have hs : Function.Surjective fun δ : holtDelta G Ω α β => A.D.coord δ i := fun x => by
    obtain ⟨δ, hδ⟩ := A.D.coord_surjective (Function.update (A.D.coord δ₀) i x)
    exact ⟨δ, by simp only [hδ, Function.update_self]⟩
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_surjective _ hs

end CaseAData

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_mem_stabilizer_eq_of_mem_commutator {β : Ω} {π : Equiv.Perm (holtDelta G Ω α β)}
    (hπ : π ∈ ⁅twoPointSection G Ω α β, twoPointSection G Ω α β⁆) :
    ∃ g ∈ stabilizer G α ⊓ stabilizer G β, ∀ δ : holtDelta G Ω α β, (π δ : Ω) = g • (δ : Ω) := by
  rw [twoPointSection_eq_range, MonoidHom.range_eq_map, ← Subgroup.map_commutator] at hπ
  obtain ⟨k, hk, rfl⟩ := hπ
  refine ⟨k, commutator_stabilizer_pair_le α β ?_, fun δ => rfl⟩
  have := Subgroup.mem_map_of_mem (stabilizer G ({α, β} : Set Ω)).subtype hk
  rwa [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at this

namespace CaseAStart

variable (X : CaseAStart G Ω α v P)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem α_ne : α ≠ X.β := X.ne.symm

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem γ_ne : (X.γ : Ω) ≠ α ∧ (X.γ : Ω) ≠ X.β :=
  ⟨fun h => left_notMem_holtDelta X.α_ne (h ▸ X.γ.2),
    fun h => right_notMem_holtDelta X.α_ne (h ▸ X.γ.2)⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem Λ_subset_and_γ_mem : X.Λ ⊆ holtDelta G Ω α X.β ∧ (X.γ : Ω) ∈ X.Λ := by
  rcases X.admissible with ⟨-, i₀, hΛ⟩ | ⟨-, -, hΛ⟩ | ⟨-, -, O, hO, -, -, -, -, hΛ⟩
  · rw [hΛ]
    exact ⟨Set.image_subset_iff.mpr fun δ _ => δ.2, ⟨X.γ, fun _ _ => rfl, rfl⟩⟩
  · rw [hΛ]; exact ⟨subset_rfl, X.γ.2⟩
  · rw [hΛ]; exact ⟨Set.insert_subset X.γ.2 hO, Set.mem_insert _ _⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem v_mem_stab (hP : Prop46Setup G Ω α v P) :
    v ∈ stabilizer G α ⊓ stabilizer G X.β ⊓ stabilizer G (X.γ : Ω) :=
  ⟨⟨hP.typeL.smul_eq, smul_eq_of_mem_p46Orbit X.mem⟩, X.v_fix⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem v_mem_pair (hP : Prop46Setup G Ω α v P) : v ∈ stabilizer G ({α, X.β} : Set Ω) :=
  stabilizer_inf_le_stabilizer_pair α X.β (X.v_mem_stab hP).1

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem eq_γ_of_smul_eq (hP : Prop46Setup G Ω α v P) {δ : Ω} (hδ : δ ∈ holtDelta G Ω α X.β)
    (hvδ : v • δ = δ) : δ = X.γ := by
  obtain ⟨γ', -, huniq⟩ := hP.one_point X.β X.mem X.ne
  exact (huniq δ ⟨hδ, hvδ⟩).trans (huniq _ ⟨X.γ.2, X.v_fix⟩).symm

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem w_mem_pair : X.w ∈ stabilizer G ({α, X.β} : Set Ω) :=
  mem_stabilizer_pair_of_orderOf_eq_two X.w_mem.1.1 X.w_mem.2

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_mem_holtDelta {g : G} (hg : g ∈ stabilizer G ({α, X.β} : Set Ω)) {δ : Ω}
    (hδ : δ ∈ holtDelta G Ω α X.β) : g • δ ∈ holtDelta G Ω α X.β := by
  have h1 := stabilizer_pair_le (G := G) α X.β hg
  rw [mem_stabilizer_iff] at h1
  rw [← h1]; exact Set.smul_mem_smul_set hδ

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem w_fix (hP : Prop46Setup G Ω α v P) : X.w • (X.γ : Ω) = X.γ := by
  refine X.eq_γ_of_smul_eq hP (X.smul_mem_holtDelta X.w_mem_pair X.γ.2) ?_
  rw [← mul_smul, ← X.w_comm.eq, mul_smul, X.v_fix]

omit [FaithfulSMul G Ω] in
theorem exists_testGroup_c (hP : Prop46Setup G Ω α v P) (h1 : Fintype.card X.A.D.ι = 1)
    (hodd : Odd (Nat.card (twoPointKernel G Ω α X.β))) {O : Set Ω}
    (hγO : (X.γ : Ω) ∉ O) (hO4 : O.ncard = 4) (hvO : v • O = O)
    (hΛ : X.Λ = insert (X.γ : Ω) O) :
    ∃ E : Subgroup G, IsPGroup 2 E ∧ E ≤ caseACentralizer G Ω α X.β v X.Λ ∧ E ≠ ⊥ ∧
      ∀ δ ∈ holtDelta G Ω α X.β, δ ∈ fixSet Ω E → δ ∈ X.Λ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Δ := holtDelta G Ω α X.β
  obtain ⟨i₁⟩ : Nonempty X.A.D.ι := Fintype.card_pos_iff.mp (by omega)
  have hcardΔ : Fintype.card Δ = Fintype.card (X.A.D.Ψc i₁) :=
    Fintype.card_of_bijective (X.A.coord_bijective_of_card_eq_one h1 i₁)
  have hmod : Fintype.card Δ % 4 = 1 := by rw [hcardΔ]; exact X.A.mod4 i₁
  have h9 : 9 ≤ Fintype.card Δ := by
    have h5 := X.A.D.five_le_card i₁
    have hne : Fintype.card (X.A.D.Ψc i₁) ≠ 5 := fun h => X.A.five h1 i₁ h hodd
    omega
  have hΛ5 : X.Λ.ncard = 5 := by rw [hΛ, Set.ncard_insert_of_notMem hγO, hO4]
  have hvΛ : ∀ δ : Ω, v • δ ∈ X.Λ ↔ δ ∈ X.Λ := fun δ => by
    have e1 : v • δ = (X.γ : Ω) ↔ δ = X.γ := ⟨fun h => by
      rw [← X.v_fix] at h; exact smul_left_cancel v h, fun h => by rw [h, X.v_fix]⟩
    have e2 : v • δ ∈ O ↔ δ ∈ O := by
      conv_lhs => rw [← hvO]
      exact Set.smul_mem_smul_set_iff
    rw [hΛ, Set.mem_insert_iff, Set.mem_insert_iff, e1, e2]
  have hΛΔ := X.Λ_subset_and_γ_mem.1
  have hγΛ := X.Λ_subset_and_γ_mem.2
  have hv2 : v * v = 1 := by rw [← sq, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one]
  set σ : Equiv.Perm Δ :=
    ((twoPointElt (X.v_mem_pair hP) : twoPointSection G Ω α X.β) : Equiv.Perm Δ)
  have hσ : ∀ δ : Δ, (σ δ : Ω) = v • (δ : Ω) := fun _ => rfl
  set p : Δ → Prop := fun δ => (δ : Ω) ∉ X.Λ
  have hσp : ∀ δ, p (σ δ) ↔ p δ := fun δ => by simp only [p, hσ, hvΛ]
  set σ₀ : Equiv.Perm {δ // p δ} := σ.subtypePerm hσp
  set v' : Equiv.Perm Δ := Equiv.Perm.ofSubtype σ₀
  have hv'p : ∀ δ : Δ, p δ → v' δ = σ δ := fun δ h =>
    Equiv.Perm.ofSubtype_apply_of_mem σ₀ h
  have hv'np : ∀ δ : Δ, ¬ p δ → v' δ = δ := fun δ h =>
    Equiv.Perm.ofSubtype_apply_of_not_mem σ₀ h
  have hσσ : ∀ δ : Δ, σ (σ δ) = δ := fun δ => Subtype.ext (by rw [hσ, hσ, ← mul_smul, hv2,
    one_smul])
  have hσfix : ∀ δ : Δ, p δ → σ δ ≠ δ := fun δ hp h => hp (by
    rw [X.eq_γ_of_smul_eq hP δ.2 (by rw [← hσ, h])]; exact hγΛ)
  have hcardp : 4 ∣ Fintype.card {δ // p δ} := by
    have h1 : Fintype.card {δ : Δ // (δ : Ω) ∈ X.Λ} = 5 := by
      rw [← hΛ5, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      exact Fintype.card_congr
        { toFun := fun x => ⟨x.1.1, x.2⟩, invFun := fun y => ⟨⟨y.1, hΛΔ y.2⟩, y.2⟩,
          left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    have h2 := Fintype.card_subtype_compl (fun δ : Δ => (δ : Ω) ∈ X.Λ)
    rw [h1] at h2
    have h3 : Fintype.card {δ // p δ} = Fintype.card Δ - 5 := h2
    rw [h3]
    exact Nat.dvd_of_mod_eq_zero (by omega)
  have hσ₀alt : σ₀ ∈ alternatingGroup {δ // p δ} :=
    mem_alternatingGroup_of_sq_eq_one_of_forall_apply_ne hcardp
      (Equiv.ext fun x => Subtype.ext (by rw [sq, Equiv.Perm.mul_apply]; exact hσσ x.1))
      (fun x h => hσfix x.1 x.2 (congrArg Subtype.val h))
  have hv'alt : v' ∈ alternatingGroup Δ := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]; exact hσ₀alt
  have hv'G : v' ∈ ⁅twoPointSection G Ω α X.β, twoPointSection G Ω α X.β⁆ := by
    have h5 : 5 ≤ Nat.card Δ := by rw [Nat.card_eq_fintype_card]; omega
    rw [← commutator_alternatingGroup_eq_self h5] at hv'alt
    exact Subgroup.commutator_mono (X.A.alternatingGroup_le_twoPointSection h1)
      (X.A.alternatingGroup_le_twoPointSection h1) hv'alt
  obtain ⟨g, hgαβ, hg⟩ := exists_mem_stabilizer_eq_of_mem_commutator hv'G
  have hgγ : g • (X.γ : Ω) = X.γ := by
    rw [← hg X.γ, hv'np X.γ (not_not.mpr hγΛ)]
  have hcomm : ∀ δ ∈ Δ, g • v • δ = v • g • δ := fun δ hδ => by
    have e1 : v • δ = (σ ⟨δ, hδ⟩ : Ω) := rfl
    rw [e1, ← hg, ← hg ⟨δ, hδ⟩, ← hσ]
    congr 1
    by_cases hp : p ⟨δ, hδ⟩
    · rw [hv'p _ ((hσp _).mpr hp), hv'p _ hp]
    · rw [hv'np _ (fun h => hp ((hσp _).mp h)), hv'np _ hp]
  have hv2' : IsPGroup 2 (Subgroup.zpowers v) :=
    zpowers_isPGroup_two_of_pow_eq_one (n := 1) (by rw [pow_one, sq, hv2])
  obtain ⟨c, hc, hcv, hcg⟩ := exists_commute_eqOn_of_odd_twoPointKernel X.γ.2 hodd
    (X.v_mem_stab hP) hv2' ⟨hgαβ, hgγ⟩ hcomm
  have hcv' : ∀ δ : Δ, c • (δ : Ω) = (v' δ : Ω) := fun δ => (hcg δ δ.2).trans (hg δ).symm
  have hv'2 : v' * v' = 1 := Equiv.ext fun δ => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    by_cases hp : p δ
    · rw [hv'p δ hp, hv'p _ ((hσp _).mpr hp), hσσ]
    · rw [hv'np δ hp, hv'np δ hp]
  have hpow : ∀ n : ℕ, ∀ δ : Δ, c ^ n • (δ : Ω) = ((v' ^ n) δ : Ω) := by
    intro n
    induction n with
    | zero => intro δ; rw [pow_zero, pow_zero, one_smul, Equiv.Perm.one_apply]
    | succ n ih =>
      intro δ
      rw [pow_succ', mul_smul, ih δ, hcv', pow_succ', Equiv.Perm.mul_apply]
  obtain ⟨e, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  obtain ⟨k, rfl⟩ := hm
  have hv'm : v' ^ (2 * k + 1) = v' := by rw [pow_succ, pow_mul, sq, hv'2, one_pow, one_mul]
  have hc₂ : ∀ δ : Δ, c ^ (2 * k + 1) • (δ : Ω) = (v' δ : Ω) := fun δ => by
    rw [hpow, hv'm]
  refine ⟨Subgroup.zpowers (c ^ (2 * k + 1)), zpowers_isPGroup_two_of_pow_eq_one (n := e) ?_,
    Subgroup.zpowers_le.mpr ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hcm, pow_orderOf_eq_one]
  · refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨n, rfl⟩
    exact ((hcv.pow_left _).zpow_right n).eq.symm
  · exact Subgroup.pow_mem _ (Subgroup.mem_inf.mp hc).1 _
  · refine (mem_fixingSubgroup_iff G).mpr fun δ hδ => ?_
    rw [hc₂ ⟨δ, hΛΔ hδ⟩, hv'np _ (not_not.mpr hδ)]
  · obtain ⟨δ, hδΔ, hδΛ⟩ : ∃ δ ∈ Δ, δ ∉ X.Λ := Set.not_subset.mp fun h => by
      have := Set.ncard_le_ncard h (Set.toFinite _)
      rw [hΛ5, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at this
      omega
    intro hbot
    have h1 : c ^ (2 * k + 1) = 1 := by
      rw [← Subgroup.mem_bot, ← hbot]; exact Subgroup.mem_zpowers _
    have h2 := hc₂ ⟨δ, hδΔ⟩
    rw [h1, one_smul, hv'p _ hδΛ, hσ] at h2
    exact hσfix ⟨δ, hδΔ⟩ hδΛ (Subtype.ext (by rw [hσ]; exact h2.symm))
  · intro δ hδ hδE
    by_contra hδΛ
    have h2 := hc₂ ⟨δ, hδ⟩
    rw [hδE _ (Subgroup.mem_zpowers _), hv'p _ hδΛ] at h2
    exact hσfix ⟨δ, hδ⟩ hδΛ (Subtype.ext h2.symm)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem v_mem_normalizer_twoPointKernel (hP : Prop46Setup G Ω α v P) :
    v ∈ Subgroup.normalizer (twoPointKernel G Ω α X.β : Set G) := by
  have hv := (X.v_mem_stab hP).1
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => conj_mem_twoPointKernel hv hk, fun hk => ?_⟩
  have := conj_mem_twoPointKernel (inv_mem hv) hk
  rwa [inv_inv, show v⁻¹ * (v * k * v⁻¹) * v = k by group] at this

omit [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_isPGroup_le_caseACentralizer_holtDelta (hP : Prop46Setup G Ω α v P)
    (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α X.β))) :
    ∃ E : Subgroup G, IsPGroup 2 E ∧
      E ≤ caseACentralizer G Ω α X.β v (holtDelta G Ω α X.β) ∧ E ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := zpowers_isPGroup_two_of_pow_eq_one (n := 1)
    (by rw [pow_one, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one])
  obtain ⟨T, -, hT', hvT⟩ := exists_fusionIsSylowIn_ge_mem_normalizer (V := ⊥) IsPGroup.of_bot
    bot_le hv2 (X.v_mem_normalizer_twoPointKernel hP)
    (by rw [Subgroup.normalizer_eq_top_iff.mpr (Subgroup.normal_bot)]; exact Subgroup.mem_top v)
  have hT1 : T ≠ ⊥ := fun h => hT (by
    have hc := card_eq_of_fusionIsSylowIn hT'
    rw [h, Subgroup.card_bot] at hc
    have h0 : (Nat.card (twoPointKernel G Ω α X.β)).factorization 2 = 0 := by
      have := (Nat.pow_right_injective le_rfl) (hc.symm.trans (pow_zero 2).symm)
      exact this
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 => by
      have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two
        Nat.card_pos.ne').mp h2
      omega))
  obtain ⟨z, hzT, hz1, hzv⟩ := exists_ne_one_commute_of_mem_normalizer hT'.2.1 hT1 hv2 hvT
  have hzK := hT'.1 hzT
  refine ⟨Subgroup.zpowers z, hT'.2.1.to_le (Subgroup.zpowers_le.mpr hzT),
    Subgroup.zpowers_le.mpr ⟨⟨?_, twoPointKernel_le_inf hzK⟩,
      twoPointKernel_le_fixingSubgroup hzK⟩,
    fun h => hz1 (by rw [← Subgroup.mem_bot, ← h]; exact Subgroup.mem_zpowers z)⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  rintro _ ⟨n, rfl⟩
  exact (hzv.zpow_right n).eq.symm

omit [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_testGroup_b (hP : Prop46Setup G Ω α v P)
    (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α X.β))) (hΛ : X.Λ = holtDelta G Ω α X.β) :
    ∃ E : Subgroup G, IsPGroup 2 E ∧ E ≤ caseACentralizer G Ω α X.β v X.Λ ∧ E ≠ ⊥ ∧
      ∀ δ ∈ holtDelta G Ω α X.β, δ ∈ fixSet Ω E → δ ∈ X.Λ := by
  obtain ⟨E, hE, hE𝒞, hE1⟩ := X.exists_isPGroup_le_caseACentralizer_holtDelta hP hT
  exact ⟨E, hE, hΛ ▸ hE𝒞, hE1, fun δ hδ _ => hΛ ▸ hδ⟩

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem five_le_card_holtDelta : 5 ≤ Nat.card (holtDelta G Ω α X.β) := by
  obtain ⟨i⟩ : Nonempty X.A.D.ι := by
    rcases X.admissible with ⟨h2, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Fintype.card_pos_iff.mp (by omega)
    · exact Fintype.card_pos_iff.mp (by omega)
    · exact Fintype.card_pos_iff.mp (by omega)
  exact (X.A.D.five_le_card i).trans (X.A.card_le_card_holtDelta X.γ i)

omit [FaithfulSMul G Ω] in
theorem vDelta_mem_socPre (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) :
    (twoPointElt (X.v_mem_pair hP) : twoPointSection G Ω α X.β) ∈ X.A.D.socPre := by
  have h3 : 3 ≤ Nat.card (holtDelta G Ω α X.β) := le_trans (by norm_num) X.five_le_card_holtDelta
  have hwv : X.w * v ∈ longInvSwap G Ω α X.β :=
    ⟨X.wv_mem, by rw [mul_smul, hP.typeL.smul_eq, X.w_mem.2]⟩
  have hwvpair : X.w * v ∈ stabilizer G ({α, X.β} : Set Ω) := mul_mem X.w_mem_pair (X.v_mem_pair hP)
  have h1 : twoPointElt X.w_mem_pair ∈ longInv (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β) :=
    (hS.mem_longInv_twoPointSection_iff X.α_ne h3 _).mpr ⟨X.w, X.w_mem, fun _ => rfl⟩
  have h2 : twoPointElt hwvpair ∈ longInv (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β) :=
    (hS.mem_longInv_twoPointSection_iff X.α_ne h3 _).mpr ⟨_, hwv, fun _ => rfl⟩
  have heq : twoPointElt (X.v_mem_pair hP) = twoPointElt X.w_mem_pair * twoPointElt hwvpair :=
    Subtype.ext (Equiv.ext fun δ => Subtype.ext (by
      show v • (δ : Ω) = X.w • (X.w * v) • (δ : Ω)
      rw [← mul_smul, ← mul_assoc, mul_self_eq_one_of_mem_longInv X.w_mem.1, one_mul]))
  rw [heq]
  exact X.A.D.mul_mem_socPre_of_mem_longInv (hS.star_twoPoint X.α_ne h3)
    (hS.holtTheorem1Below_twoPoint h3) h1 h2

omit [FaithfulSMul G Ω] in
theorem exists_coordElt (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) (j : X.A.D.ι) :
    ∃ ℓ : jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β),
      ((ℓ : twoPointSection G Ω α X.β) : Equiv.Perm (holtDelta G Ω α X.β)) ∈
        ⁅twoPointSection G Ω α X.β, twoPointSection G Ω α X.β⁆ ∧
      X.A.D.ρ j ℓ = X.A.D.ρ j ⟨_, X.A.D.socPre_le_jHull (X.vDelta_mem_socPre hS hP)⟩ ∧
      ∀ k, k ≠ j → X.A.D.ρ k ℓ = 1 := by
  set vΔ : jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β) :=
    ⟨_, X.A.D.socPre_le_jHull (X.vDelta_mem_socPre hS hP)⟩
  have hvj : X.A.D.ρ j vΔ ∈ X.A.D.M j :=
    X.A.D.rho_mem_M_of_mem_socPre (h := vΔ) (X.vDelta_mem_socPre hS hP) j
  have hperf := X.A.D.isPerfect_M j
  rw [Subgroup.isPerfect_iff] at hperf
  rw [← hperf] at hvj
  have hM : X.A.D.M j = ((X.A.D.L j).subgroupOf
      (jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β))).map (X.A.D.ρ j) := rfl
  rw [hM, ← Subgroup.map_commutator] at hvj
  obtain ⟨ℓ, hℓ, hℓv⟩ := hvj
  have hℓL : ℓ ∈ (X.A.D.L j).subgroupOf
      (jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β)) :=
    (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) hℓ
  refine ⟨ℓ, ?_, hℓv, fun k hk => X.A.D.rho_eq_one_of_mem_L (Ne.symm hk) hℓL⟩
  have h1 := Subgroup.mem_map_of_mem
    (jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β)).subtype
    (Subgroup.commutator_mono le_top le_top hℓ)
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h1
  have h2 := Subgroup.mem_map_of_mem (twoPointSection G Ω α X.β).subtype
    (Subgroup.commutator_mono le_top le_top h1)
  rwa [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h2

omit [FaithfulSMul G Ω] in
theorem coord_v (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) :
    (∀ (δ : holtDelta G Ω α X.β) (j : X.A.D.ι), X.A.D.coord ⟨v • (δ : Ω),
        X.smul_mem_holtDelta (X.v_mem_pair hP) δ.2⟩ j =
      X.A.D.ρ j ⟨_, X.A.D.socPre_le_jHull (X.vDelta_mem_socPre hS hP)⟩ (X.A.D.coord δ j)) ∧
    ∀ (j : X.A.D.ι) (x : X.A.D.Ψc j),
      X.A.D.ρ j ⟨_, X.A.D.socPre_le_jHull (X.vDelta_mem_socPre hS hP)⟩ x = x →
        x = X.A.D.coord X.γ j := by
  classical
  set vΔ : jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β) :=
    ⟨_, X.A.D.socPre_le_jHull (X.vDelta_mem_socPre hS hP)⟩
  have hact : ∀ (δ : holtDelta G Ω α X.β) (j : X.A.D.ι), X.A.D.coord ⟨v • (δ : Ω),
      X.smul_mem_holtDelta (X.v_mem_pair hP) δ.2⟩ j = X.A.D.ρ j vΔ (X.A.D.coord δ j) :=
    fun δ j => X.A.D.coord_smul vΔ δ j
  refine ⟨hact, fun j x hx => ?_⟩
  obtain ⟨δ, hδ⟩ := X.A.D.coord_surjective (Function.update (X.A.D.coord X.γ) j x)
  have e : (⟨v • (X.γ : Ω), X.smul_mem_holtDelta (X.v_mem_pair hP) X.γ.2⟩ :
      holtDelta G Ω α X.β) = X.γ := Subtype.ext X.v_fix
  have hvγ : ∀ k, X.A.D.ρ k vΔ (X.A.D.coord X.γ k) = X.A.D.coord X.γ k := fun k => by
    rw [← hact, e]
  have hfix : (⟨v • (δ : Ω), X.smul_mem_holtDelta (X.v_mem_pair hP) δ.2⟩ :
      holtDelta G Ω α X.β) = δ := X.A.coord_injective (funext fun k => by
    rw [hact, hδ]
    by_cases hk : k = j
    · subst hk; rw [Function.update_self, hx]
    · rw [Function.update_of_ne hk, hvγ])
  have hδγ : (δ : Ω) = X.γ :=
    X.eq_γ_of_smul_eq hP δ.2 (congrArg Subtype.val hfix)
  have := congrFun hδ j
  rw [Function.update_self, show δ = X.γ from Subtype.ext hδγ] at this
  exact this.symm

omit [FaithfulSMul G Ω] in
theorem fixSet_subset_of_coord (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (h2 : 2 ≤ Fintype.card X.A.D.ι) {i₀ : X.A.D.ι}
    (hΛ : X.Λ = (↑) '' {δ : holtDelta G Ω α X.β | ∀ j, j ≠ i₀ →
      X.A.D.coord δ j = X.A.D.coord X.γ j})
    {E : Subgroup G} (hE𝒞 : E ≤ caseACentralizer G Ω α X.β v X.Λ)
    (hEj : ∀ j, j ≠ i₀ → ∃ (g : G) (hg : g ∈ E), ∀ δ : holtDelta G Ω α X.β,
      X.A.D.coord ⟨g • (δ : Ω), X.smul_mem_holtDelta (stabilizer_inf_le_stabilizer_pair α X.β
        (Subgroup.mem_inf.mp (hE𝒞 hg)).1.2) δ.2⟩ j =
      X.A.D.ρ j ⟨_, X.A.D.socPre_le_jHull (X.vDelta_mem_socPre hS hP)⟩ (X.A.D.coord δ j)) :
    E ≠ ⊥ ∧ ∀ δ ∈ holtDelta G Ω α X.β, δ ∈ fixSet Ω E → δ ∈ X.Λ := by
  classical
  obtain ⟨-, hvfix⟩ := X.coord_v hS hP
  have hmove : ∀ j, j ≠ i₀ → ∀ δ : holtDelta G Ω α X.β,
      X.A.D.coord δ j ≠ X.A.D.coord X.γ j → ∃ g ∈ E, g • (δ : Ω) ≠ δ := by
    intro j hj δ hδ
    obtain ⟨g, hg, hgδ⟩ := hEj j hj
    refine ⟨g, hg, fun h => hδ (hvfix j _ ?_)⟩
    have := hgδ δ
    rw [show (⟨g • (δ : Ω), _⟩ : holtDelta G Ω α X.β) = δ from Subtype.ext h] at this
    exact this.symm
  refine ⟨?_, fun δ hδ hδE => ?_⟩
  · obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i₀
    have : Nontrivial (X.A.D.Ψc j) :=
      Fintype.one_lt_card_iff_nontrivial.mp (by have := X.A.D.five_le_card j; omega)
    obtain ⟨x, hx⟩ := exists_ne (X.A.D.coord X.γ j)
    obtain ⟨δ, hδ⟩ := X.A.D.coord_surjective (Function.update (X.A.D.coord X.γ) j x)
    obtain ⟨g, hg, hgδ⟩ := hmove j hj δ (by rw [hδ, Function.update_self]; exact hx)
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hg
    rw [hg, one_smul] at hgδ
    exact hgδ rfl
  · by_contra hδΛ
    rw [hΛ] at hδΛ
    have : ∃ j, j ≠ i₀ ∧ X.A.D.coord ⟨δ, hδ⟩ j ≠ X.A.D.coord X.γ j := by
      by_contra h
      exact hδΛ ⟨⟨δ, hδ⟩, fun j hj => not_not.mp fun hne => h ⟨j, hj, hne⟩, rfl⟩
    obtain ⟨j, hj, hne⟩ := this
    obtain ⟨g, hg, hgδ⟩ := hmove j hj ⟨δ, hδ⟩ hne
    exact hgδ (hδE g hg)

omit [FaithfulSMul G Ω] in
theorem exists_testGroup_a_odd (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (h2 : 2 ≤ Fintype.card X.A.D.ι) {i₀ : X.A.D.ι}
    (hΛ : X.Λ = (↑) '' {δ : holtDelta G Ω α X.β | ∀ j, j ≠ i₀ →
      X.A.D.coord δ j = X.A.D.coord X.γ j})
    (hodd : Odd (Nat.card (twoPointKernel G Ω α X.β))) :
    ∃ E : Subgroup G, IsPGroup 2 E ∧ E ≤ caseACentralizer G Ω α X.β v X.Λ ∧ E ≠ ⊥ ∧
      ∀ δ ∈ holtDelta G Ω α X.β, δ ∈ fixSet Ω E → δ ∈ X.Λ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Δ := holtDelta G Ω α X.β
  set vΔ : jHull (twoPointSection G Ω α X.β) Δ :=
    ⟨_, X.A.D.socPre_le_jHull (X.vDelta_mem_socPre hS hP)⟩
  obtain ⟨hvc, hvfix⟩ := X.coord_v hS hP
  choose ℓ hℓG hℓj hℓk using fun j => X.exists_coordElt hS hP j
  set e : X.A.D.ι → Equiv.Perm Δ := fun j => ((ℓ j : twoPointSection G Ω α X.β) : Equiv.Perm Δ)
  have hec : ∀ j (δ : Δ) k, X.A.D.coord (e j δ) k = X.A.D.ρ k (ℓ j) (X.A.D.coord δ k) :=
    fun j δ k => X.A.D.coord_smul (ℓ j) δ k
  have e₀ : (⟨v • (X.γ : Ω), X.smul_mem_holtDelta (X.v_mem_pair hP) X.γ.2⟩ : Δ) = X.γ :=
    Subtype.ext X.v_fix
  have hvγ : ∀ k, X.A.D.ρ k vΔ (X.A.D.coord X.γ k) = X.A.D.coord X.γ k := fun k => by rw [← hvc, e₀]
  set L : Set Δ := {δ | ∀ j, j ≠ i₀ → X.A.D.coord δ j = X.A.D.coord X.γ j}
  set S : Set (Equiv.Perm Δ) := e '' {j | j ≠ i₀}
  set Ē := Subgroup.closure S
  have hecoord : ∀ j k (δ : Δ), X.A.D.coord (e j δ) k =
      if k = j then X.A.D.ρ k vΔ (X.A.D.coord δ k) else X.A.D.coord δ k := fun j k δ => by
    rw [hec]
    split_ifs with hk
    · subst hk; rw [hℓj]
    · rw [hℓk j k hk, Equiv.Perm.one_apply]
  have hcommS : ∀ σ ∈ S, ∀ τ ∈ S, Commute σ τ := by
    rintro _ ⟨j, -, rfl⟩ _ ⟨k, -, rfl⟩
    refine Equiv.ext fun δ => X.A.coord_injective (funext fun i => ?_)
    show X.A.D.coord (e j (e k δ)) i = X.A.D.coord (e k (e j δ)) i
    rw [hecoord j i, hecoord k i, hecoord k i, hecoord j i]
    by_cases hij : i = j <;> by_cases hik : i = k
    · subst hij; subst hik; rfl
    · subst hij; simp [hik]
    · subst hik; simp [hij]
    · simp [hij, hik]
  have hĒc : Ē ≤ Subgroup.centralizer (Ē : Set (Equiv.Perm Δ)) := by
    have h1 : Ē ≤ Subgroup.centralizer S := (Subgroup.closure_le _).mpr fun σ hσ =>
      Subgroup.mem_centralizer_iff.mpr fun τ hτ => (hcommS τ hτ σ hσ).eq
    have h2 : S ⊆ (Subgroup.centralizer (Ē : Set (Equiv.Perm Δ)) : Set (Equiv.Perm Δ)) :=
      fun σ hσ => Subgroup.mem_centralizer_iff.mpr
        fun τ hτ => (Subgroup.mem_centralizer_iff.mp (h1 hτ) σ hσ).symm
    exact (Subgroup.closure_le _).mpr h2
  have hsq : ∀ σ ∈ Ē, σ * σ = 1 := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem σ hσ =>
      obtain ⟨j, -, rfl⟩ := hσ
      refine Equiv.ext fun δ => X.A.coord_injective (funext fun i => ?_)
      show X.A.D.coord (e j (e j δ)) i = X.A.D.coord δ i
      rw [hecoord j i, hecoord j i]
      by_cases hij : i = j
      · simp only [hij, ite_true]
        rw [← Equiv.Perm.mul_apply, ← map_mul, show vΔ * vΔ = 1 from Subtype.ext (Subtype.ext
          (Equiv.ext fun δ' => Subtype.ext (by
            show v • v • (δ' : Ω) = δ'
            rw [← mul_smul, ← sq, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one, one_smul]))),
          map_one, Equiv.Perm.one_apply]
      · simp [hij]
    | one => rw [mul_one]
    | mul σ τ hσ hτ ihσ ihτ =>
      have hστ : τ * σ = σ * τ := Subgroup.mem_centralizer_iff.mp (hĒc hσ) τ hτ
      calc σ * τ * (σ * τ) = σ * (τ * σ) * τ := by group
        _ = σ * σ * (τ * τ) := by rw [hστ]; group
        _ = 1 := by rw [ihσ, ihτ, mul_one]
    | inv σ hσ ih => rw [← mul_inv_rev, ih, inv_one]
  have hĒ2 : IsPGroup 2 Ē := IsPGroup.iff_orderOf.mpr fun σ => by
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one
      (show σ ^ 2 ^ 1 = 1 by rw [pow_one, sq]; exact Subtype.ext (hsq σ σ.2)))
    exact ⟨b, hb⟩
  have hĒL : ∀ σ ∈ Ē, ∀ δ ∈ L, σ δ = δ := by
    have hle : Ē ≤ fixingSubgroup (Equiv.Perm Δ) L := (Subgroup.closure_le _).mpr fun σ hσ => by
      obtain ⟨j, hj, rfl⟩ := hσ
      refine (mem_fixingSubgroup_iff _).mpr fun δ hδ => X.A.coord_injective (funext fun i => ?_)
      show X.A.D.coord (e j δ) i = X.A.D.coord δ i
      rw [hecoord j i]
      by_cases hij : i = j
      · subst hij; simp only [ite_true]; rw [hδ i hj, hvγ]
      · simp [hij]
    exact fun σ hσ δ hδ => (mem_fixingSubgroup_iff _).mp (hle hσ) δ hδ
  set vP : Equiv.Perm Δ := ((vΔ : twoPointSection G Ω α X.β) : Equiv.Perm Δ)
  have hvP : ∀ δ : Δ, X.A.D.coord (vP δ) = fun k => X.A.D.ρ k vΔ (X.A.D.coord δ k) :=
    fun δ => funext fun k => X.A.D.coord_smul vΔ δ k
  have hĒv : ∀ σ ∈ Ē, Commute σ vP := by
    have hle : Ē ≤ Subgroup.centralizer {vP} := (Subgroup.closure_le _).mpr fun σ hσ => by
      obtain ⟨j, -, rfl⟩ := hσ
      refine Subgroup.mem_centralizer_singleton_iff.mpr (Equiv.ext fun δ =>
        X.A.coord_injective (funext fun i => ?_))
      show X.A.D.coord (e j (vP δ)) i = X.A.D.coord (vP (e j δ)) i
      rw [hecoord j i, congrFun (hvP _) i, congrFun (hvP _) i, hecoord j i]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    exact fun σ hσ => Subgroup.mem_centralizer_singleton_iff.mp (hle hσ)
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := zpowers_isPGroup_two_of_pow_eq_one (n := 1)
    (by rw [pow_one, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one])
  set H₃ := stabilizer G α ⊓ stabilizer G X.β ⊓ stabilizer G (X.γ : Ω)
  have hH₃Δ : H₃ ≤ stabilizer G Δ := fun g hg => by
    have := stabilizer_pair_le (G := G) α X.β
      (stabilizer_inf_le_stabilizer_pair α X.β (Subgroup.mem_inf.mp hg).1)
    exact this
  set res := inducedHom H₃ Δ hH₃Δ
  set Y' : Subgroup H₃ := Ē.comap res ⊓
    (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)).subgroupOf H₃
  have hYmap : Y'.map res = Ē := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_left)
      ((Subgroup.closure_le _).mpr ?_)
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨g, hgαβ, hg⟩ := exists_mem_stabilizer_eq_of_mem_commutator (hℓG j)
    have hej : e j ∈ Ē := Subgroup.subset_closure ⟨j, hj, rfl⟩
    have hgγ : g • (X.γ : Ω) = X.γ := by
      rw [← hg X.γ, hĒL _ hej X.γ fun k _ => rfl]
    have hcomm : ∀ δ ∈ Δ, g • v • δ = v • g • δ := fun δ hδ => by
      have h1 := congrArg (fun σ : Equiv.Perm Δ => ((σ ⟨δ, hδ⟩ : Δ) : Ω)) (hĒv _ hej).eq
      simp only [Equiv.Perm.mul_apply] at h1
      calc g • v • δ = ((e j (vP ⟨δ, hδ⟩) : Δ) : Ω) := (hg (vP ⟨δ, hδ⟩)).symm
        _ = ((vP (e j ⟨δ, hδ⟩) : Δ) : Ω) := h1
        _ = v • g • δ := by
          rw [show ((vP (e j ⟨δ, hδ⟩) : Δ) : Ω) = v • ((e j ⟨δ, hδ⟩ : Δ) : Ω) from rfl, hg]
    obtain ⟨c, hc, hcv, hcg⟩ := exists_commute_eqOn_of_odd_twoPointKernel X.γ.2 hodd
      (X.v_mem_stab hP) hv2 ⟨hgαβ, hgγ⟩ hcomm
    have hres : res ⟨c, hc⟩ = e j :=
      Equiv.ext fun δ => Subtype.ext ((hcg δ δ.2).trans (hg δ).symm)
    refine ⟨⟨c, hc⟩, ⟨?_, ?_⟩, hres⟩
    · show res ⟨c, hc⟩ ∈ Ē
      rw [hres]; exact hej
    · refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_iff.mpr ?_)
      rintro _ ⟨n, rfl⟩
      exact (hcv.zpow_right n).eq.symm
  obtain ⟨E₀, hE₀, hE₀Ē⟩ := exists_fusionIsSylowIn_map_eq res (H := Y') (Q := Ē)
    (by rw [hYmap]; exact ⟨le_rfl, hĒ2, fun Q hQ _ hle => le_antisymm hQ hle⟩)
  set E := E₀.map H₃.subtype
  have hE𝒞 : E ≤ caseACentralizer G Ω α X.β v X.Λ := by
    rintro _ ⟨y, hy, rfl⟩
    have hyY := hE₀.1 hy
    refine ⟨⟨Subgroup.mem_subgroupOf.mp hyY.2, (Subgroup.mem_inf.mp y.2).1⟩, ?_⟩
    refine (mem_fixingSubgroup_iff G).mpr fun l hl => ?_
    rw [hΛ] at hl
    obtain ⟨δ, hδ, rfl⟩ := hl
    exact congrArg Subtype.val (hĒL _ hyY.1 δ hδ)
  refine ⟨E, hE₀.2.1.map _, hE𝒞, X.fixSet_subset_of_coord hS hP h2 hΛ hE𝒞 fun j hj => ?_⟩
  have hej : e j ∈ E₀.map res := hE₀Ē ▸ Subgroup.subset_closure ⟨j, hj, rfl⟩
  obtain ⟨y, hy, hyj⟩ := hej
  refine ⟨y, ⟨y, hy, rfl⟩, fun δ => ?_⟩
  show X.A.D.coord (res y δ) j = _
  rw [hyj, hecoord j j δ, ite_eq_left rfl]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem w_mem_normalizer_caseACentralizer {Λ' : Set Ω} (hwΛ : X.w • Λ' = Λ') :
    X.w ∈ Subgroup.normalizer (caseACentralizer G Ω α X.β v Λ' : Set G) := by
  have hw2 : X.w * X.w = 1 := mul_self_eq_one_of_mem_longInv X.w_mem.1
  have hwinv : X.w⁻¹ = X.w := inv_eq_of_mul_eq_one_right hw2
  have hwα : X.w • α = X.β := X.w_mem.2
  have hwβ : X.w • X.β = α := by rw [← hwα, ← mul_smul, hw2, one_smul]
  have key : ∀ g ∈ caseACentralizer G Ω α X.β v Λ',
      X.w * g * X.w⁻¹ ∈ caseACentralizer G Ω α X.β v Λ' := by
    rintro g ⟨⟨hgv, hgα, hgβ⟩, hgΛ⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ ⟨n, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hgv (v ^ n) ⟨n, rfl⟩
      have h2 : Commute X.w (v ^ n) := X.w_comm.zpow_right n
      simp only at h1 ⊢
      rw [hwinv]
      calc v ^ n * (X.w * g * X.w) = (v ^ n * X.w) * g * X.w := by group
        _ = X.w * (v ^ n * g) * X.w := by rw [← h2.eq]; group
        _ = X.w * (g * v ^ n) * X.w := by rw [h1]
        _ = X.w * g * (v ^ n * X.w) := by group
        _ = X.w * g * X.w * v ^ n := by rw [← h2.eq]; group
    · show (X.w * g * X.w⁻¹) • α = α
      rw [hwinv, mul_smul, mul_smul, hwα, show g • X.β = X.β from hgβ, hwβ]
    · show (X.w * g * X.w⁻¹) • X.β = X.β
      rw [hwinv, mul_smul, mul_smul, hwβ, show g • α = α from hgα, hwα]
    · refine (mem_fixingSubgroup_iff G).mpr fun l hl => ?_
      have hl' : X.w⁻¹ • l ∈ Λ' := by
        rw [← hwΛ] at hl
        rwa [Set.mem_smul_set_iff_inv_smul_mem] at hl
      rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp hgΛ _ hl', smul_inv_smul]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key g, fun hg => ?_⟩
  have := key _ hg
  rwa [hwinv, show X.w * (X.w * g * X.w) * X.w = g by
    rw [← mul_assoc, ← mul_assoc, hw2, one_mul, mul_assoc, hw2, mul_one]] at this

theorem exists_testGroup_a_even (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (h2 : 2 ≤ Fintype.card X.A.D.ι) {i₀ : X.A.D.ι}
    (hΛ : X.Λ = (↑) '' {δ : holtDelta G Ω α X.β | ∀ j, j ≠ i₀ →
      X.A.D.coord δ j = X.A.D.coord X.γ j})
    (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α X.β))) :
    ∃ E : Subgroup G, IsPGroup 2 E ∧ E ≤ caseACentralizer G Ω α X.β v X.Λ ∧ E ≠ ⊥ ∧
      ∀ δ ∈ holtDelta G Ω α X.β, δ ∈ fixSet Ω E → δ ∈ X.Λ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Δ := holtDelta G Ω α X.β
  have hv2 : v * v = 1 := by rw [← sq, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one]
  have hw2 : IsPGroup 2 (Subgroup.zpowers X.w) := zpowers_isPGroup_two_of_pow_eq_one (n := 1)
    (by rw [pow_one, sq]; exact mul_self_eq_one_of_mem_longInv X.w_mem.1)
  have hwΔ : X.w • Δ = Δ := by
    have := stabilizer_pair_le (G := G) α X.β X.w_mem_pair
    rwa [mem_stabilizer_iff] at this
  obtain ⟨T', -, hT', hwT'⟩ := exists_fusionIsSylowIn_ge_mem_normalizer (V := ⊥) IsPGroup.of_bot
    bot_le hw2 (X.w_mem_normalizer_caseACentralizer hwΔ)
    (by rw [Subgroup.normalizer_eq_top_iff.mpr (Subgroup.normal_bot)]; exact Subgroup.mem_top _)
  have hstabΔ : caseACentralizer G Ω α X.β v Δ ≤ stabilizer G Δ := fun g hg => by
    have := stabilizer_pair_le (G := G) α X.β (stabilizer_inf_le_stabilizer_pair α X.β
      (Subgroup.mem_inf.mp hg).1.2)
    exact this
  have hT'1 : T' ≠ ⊥ := by
    obtain ⟨E₀, hE₀, hE₀𝒞, hE₀1⟩ := X.exists_isPGroup_le_caseACentralizer_holtDelta hP hT
    exact (fixSet_inter_subset_of_fusionIsSylowIn hT' hE₀ hE₀𝒞 hstabΔ
      (fun g hg => (Subgroup.mem_inf.mp hg).2) (fun δ hδ _ => hδ)).1 hE₀1
  have hT'v : v ∈ Subgroup.centralizer (T' : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun g hg => (Subgroup.mem_centralizer_iff.mp (hT'.1 hg).1.1 v (Subgroup.mem_zpowers v)).symm
  have hαT : α ∈ fixSet Ω T' := fun g hg => (hT'.1 hg).1.2.1
  have hβT : X.β ∈ fixSet Ω T' := fun g hg => (hT'.1 hg).1.2.2
  have hΔT : ∀ δ ∈ Δ, δ ∈ fixSet Ω T' := fun δ hδ g hg =>
    (mem_fixingSubgroup_iff G).mp (hT'.1 hg).2 δ hδ
  have h3 : 3 ≤ Nat.card (fixSet Ω T') := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_eq_three.mpr ⟨α, X.β, X.γ, X.α_ne, X.γ_ne.1.symm, X.γ_ne.2.symm,
      rfl⟩).symm.le.trans
      (Set.ncard_le_ncard (Set.insert_subset hαT (Set.insert_subset hβT
        (Set.singleton_subset_iff.mpr (hΔT _ X.γ.2)))) (Set.toFinite _))
  obtain ⟨DK⟩ := hS.holtData_centralizerImage hT'.2.1 hT'1 h3
  set a : fixSet Ω T' := ⟨α, hαT⟩
  set b : fixSet Ω T' := ⟨X.β, hβT⟩
  set g₀ : fixSet Ω T' := ⟨X.γ, hΔT _ X.γ.2⟩
  have hnt : ∀ i, (Set.univ : Set (X.A.D.Ψc i)).Nontrivial := fun i =>
    Set.nontrivial_univ_iff.mpr (Fintype.one_lt_card_iff_nontrivial.mp
      (by have := X.A.D.five_le_card i; omega))
  obtain ⟨c, hcinj, hcalt, hcfib, hcpar⟩ := hS.exists_ccl X.α_ne X.A hT'.2.1 hT'1 h3
    (a := a) (b := b) rfl rfl (fun _ => Set.univ) (fun δ => iff_of_true (hΔT δ δ.2)
      fun _ => Set.mem_univ _) (fun i _ => by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card]; exact X.A.D.five_le_card i) DK
  set c' : X.A.D.ι → DK.ι := fun j => c ⟨j, hnt j⟩
  have hc'inj : Function.Injective c' := fun j j' h => congrArg Subtype.val (hcinj h)
  have hcard' : ∀ j, Fintype.card (DK.Ψc (c' j)) = Fintype.card (X.A.D.Ψc j) + 2 := fun j => by
    rw [(hcalt ⟨j, hnt j⟩).2.1, Set.ncard_univ, Nat.card_eq_fintype_card]
  have hout : IsOuterFactor (DK.M (c' i₀)) :=
    ⟨(hcalt ⟨i₀, hnt i₀⟩).1, by rw [hcard']; have := X.A.mod4 i₀; omega⟩
  have hker := DK.ker_outer ⟨c' i₀, hout⟩
  obtain ⟨W, hTW, hW, -, x, hxW, hx2, hxv, hxc⟩ :=
    hS.exists_sylow_centralizer_mul hT'.2.1 h3 hv2 hT'v X.w_mem.1 X.wv_mem hwT'
      (zpowers_isPGroup_two_of_pow_eq_one (n := 1) (by rw [pow_one, sq]; exact hv2))
      (Subgroup.mem_zpowers v) (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hT'v))
  have hxbar : restrictCentralizer Ω T' ⟨x, Subgroup.centralizer_le hTW hxW⟩ =
      restrictCentralizer Ω T' ⟨v, hT'v⟩ :=
    Subtype.ext (Equiv.ext fun ω => Subtype.ext (hxv ω ω.2))
  have hxS : (restrictCentralizer Ω T' ⟨x, Subgroup.centralizer_le hTW hxW⟩ :
      centralizerImage Ω T') ∈ DK.socPre := by
    rw [hxbar]
    exact hS.restrict_mem_socPre hT'.2.1 hT'1 h3 hT'v X.w_mem.1 X.wv_mem hwT' DK
  have hxJ := DK.socPre_le_jHull hxS
  set xJ : jHull (centralizerImage Ω T') (fixSet Ω T') := ⟨_, hxJ⟩
  have hxfix : ∀ ω : fixSet Ω T', v • (ω : Ω) = ω →
      ∀ k, DK.ρ k xJ (DK.coord ω k) = DK.coord ω k := fun ω hω k => by
    rw [← DK.coord_smul xJ ω k]
    congr 2
    exact Subtype.ext ((hxv ω ω.2).trans hω)
  have hxa := hxfix a hP.typeL.smul_eq
  have hxb := hxfix b (smul_eq_of_mem_p46Orbit X.mem)
  have hxg := hxfix g₀ X.v_fix
  have hxx : xJ * xJ = 1 := Subtype.ext (Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
    show x • x • (ω : Ω) = ω
    have h1 : x • (ω : Ω) ∈ fixSet Ω T' := smul_mem_fixSet_of_mem_normalizer
      (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hTW hxW)) ω.2
    rw [hxv _ h1, hxv _ ω.2, ← mul_smul, hv2, one_smul])))
  have h24 := DK.socInvFixesBlocks_of_below (hS.star_centralizerImage hT'.2.1 h3)
    (hS.holtTheorem1Below_centralizerImage hT'.2.1 hT'1 h3)
  have hxω : ∀ ω ∈ orbit (jOddCore (centralizerImage Ω T') (fixSet Ω T')) a,
      x • (ω : Ω) = ω := fun ω hω => by
    have h1 := h24 xJ hxS (by rw [← Subgroup.coe_mul, hxx, Subgroup.coe_one]) a
      (by rw [DK.smul_eq_of_rho_eq h24 hxS hxx hxa]; exact mem_orbit_self a) ω hω
    exact congrArg Subtype.val h1
  choose ℓ hℓL hℓρ hℓk using fun j => DK.exists_mem_L_rho_eq
    (DK.rho_mem_M_of_mem_socPre (h := xJ) hxS (c' j))
  set S : Set (∀ k, Equiv.Perm (DK.Ψc k)) := (fun j => psiHom DK (ℓ j)) '' {j | j ≠ i₀}
  have hρℓ : ∀ j k, DK.ρ k (ℓ j) = if k = c' j then DK.ρ k xJ else 1 := fun j k => by
    split_ifs with hk
    · subst hk; exact hℓρ j
    · exact hℓk j k hk
  have hSsq : ∀ s ∈ S, s * s = 1 := by
    rintro _ ⟨j, -, rfl⟩
    funext k
    show DK.ρ k (ℓ j) * DK.ρ k (ℓ j) = 1
    rw [hρℓ]
    split_ifs
    · rw [← map_mul, hxx, map_one]
    · rw [mul_one]
  have hScomm : ∀ s ∈ S, ∀ t ∈ S, Commute s t := by
    rintro _ ⟨j, -, rfl⟩ _ ⟨j', -, rfl⟩
    funext k
    show DK.ρ k (ℓ j) * DK.ρ k (ℓ j') = DK.ρ k (ℓ j') * DK.ρ k (ℓ j)
    rw [hρℓ, hρℓ]
    by_cases h1 : k = c' j <;> by_cases h2 : k = c' j' <;> simp [h1, h2]
  set Q := Subgroup.closure S
  have hQsq := mul_self_eq_one_of_mem_closure hSsq hScomm
  have hQ2 : IsPGroup 2 Q := isPGroup_of_mul_self hQsq
  have hSR : S ⊆ (psiHom DK).range := by rintro _ ⟨j, -, rfl⟩; exact ⟨ℓ j, rfl⟩
  have hQR : Q ≤ (psiHom DK).range := (Subgroup.closure_le _).mpr hSR
  have hlc : ∀ q ∈ Q, LiftsCommute (psiHom DK).range q (psiHom DK xJ) :=
    LiftsCommute.closure hSR (by
      rintro _ ⟨j, -, rfl⟩
      exact DK.liftsCommute_of_rho_eq_one hxS (i := c' j) (hℓk j) 1
        (by rw [pow_one, hℓρ j, inv_mul_cancel]))
  have hfixQ : ∀ y : ∀ k, DK.Ψc k, (∀ k, DK.ρ k xJ (y k) = y k) →
      ∀ q ∈ Q, ∀ k, q k (y k) = y k := by
    intro y hy
    have hle : Q ≤ Subgroup.pi Set.univ fun k =>
        MulAction.stabilizer (Equiv.Perm (DK.Ψc k)) (y k) :=
      (Subgroup.closure_le _).mpr (by
        rintro _ ⟨j, -, rfl⟩ k -
        show DK.ρ k (ℓ j) • y k = y k
        rw [hρℓ]
        split_ifs
        · exact hy k
        · rfl)
    exact fun q hq k => hle hq k (Set.mem_univ k)
  have hQi₀ : ∀ q ∈ Q, q (c' i₀) = 1 := by
    have hle : Q ≤ (Pi.evalMonoidHom (fun k => Equiv.Perm (DK.Ψc k)) (c' i₀)).ker :=
      (Subgroup.closure_le _).mpr (by
        rintro _ ⟨j, hj, rfl⟩
        show DK.ρ (c' i₀) (ℓ j) = 1
        rw [hρℓ, ite_eq_right (fun h => hj (hc'inj h).symm)])
    exact fun q hq => hle hq
  obtain ⟨E, hEW, hE2, hEx, hEα, hEψ, hEsurj⟩ := hS.exists_lift hT'.2.1 h3 hTW hW DK hker hxW
    hx2 hxJ hQ2 hQR hlc a hxω (hfixQ _ hxa)
  have hQsoc : Q ≤ (DK.socPre.subgroupOf (jHull (centralizerImage Ω T') (fixSet Ω T'))).map
      (psiHom DK) := (Subgroup.closure_le _).mpr (by
    rintro _ ⟨j, -, rfl⟩
    exact ⟨ℓ j, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem (c' j) (hℓL j))), rfl⟩)
  have hEinv : ∀ (e : G) (he : e ∈ E), ∃ hJ : restrictCentralizer Ω T'
      ⟨e, Subgroup.centralizer_le hTW (hEW he)⟩ ∈ jHull (centralizerImage Ω T') (fixSet Ω T'),
      ((restrictCentralizer Ω T' ⟨e, Subgroup.centralizer_le hTW (hEW he)⟩ :
        centralizerImage Ω T') ∈ DK.socPre) ∧
      (⟨_, hJ⟩ : jHull (centralizerImage Ω T') (fixSet Ω T')) * ⟨_, hJ⟩ = 1 ∧
      psiHom DK ⟨_, hJ⟩ ∈ Q := by
    intro e he
    obtain ⟨hJ, hψ⟩ := hEψ e he
    set ē : jHull (centralizerImage Ω T') (fixSet Ω T') := ⟨_, hJ⟩
    refine ⟨hJ, ?_, ?_, hψ⟩
    · obtain ⟨s, hs, hsē⟩ := hQsoc hψ
      have hk : ((s⁻¹ * ē : jHull (centralizerImage Ω T') (fixSet Ω T')) :
          centralizerImage Ω T') ∈ jOddCore (centralizerImage Ω T') (fixSet Ω T') := by
        rw [← hker, DK.mem_jOrbitKernel_iff_rho]
        intro k
        rw [map_mul, map_inv, inv_mul_eq_one]
        exact (congrFun hsē k)
      have := mul_mem (Subgroup.mem_subgroupOf.mp hs) (DK.jOddCore_le_socPre hk)
      rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this
    · obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hE2) ⟨e, he⟩
      have hen : e ^ 2 ^ n = 1 := by
        have := pow_orderOf_eq_one (⟨e, he⟩ : E)
        rw [hn] at this
        exact congrArg Subtype.val this
      have hēn : (ē * ē) ^ 2 ^ n = 1 := by
        rw [← sq, ← pow_mul, mul_comm, pow_mul]
        have : ē ^ 2 ^ n = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          show (restrictCentralizer Ω T' ⟨e, _⟩) ^ 2 ^ n = 1
          rw [← map_pow, show (⟨e, Subgroup.centralizer_le hTW (hEW he)⟩ :
            Subgroup.centralizer (T' : Set G)) ^ 2 ^ n = 1 from Subtype.ext (by
              rw [Subgroup.coe_pow]; exact hen), map_one])
        rw [this, one_pow]
      have hk : ((ē * ē : jHull (centralizerImage Ω T') (fixSet Ω T')) :
          centralizerImage Ω T') ∈ jOddCore (centralizerImage Ω T') (fixSet Ω T') := by
        rw [← hker, DK.mem_jOrbitKernel_iff_rho]
        intro k
        rw [map_mul]
        exact congrFun (hQsq _ hψ) k
      exact Subtype.ext (eq_one_of_pow_two_pow_eq_one_of_mem odd_card_jOddCore hk
        (by rw [← Subgroup.coe_pow, hēn, Subgroup.coe_one]))
  have hrange : ∀ k, k ∉ Set.range c' → k ∉ Set.range c := fun k hk ⟨j, hj⟩ =>
    hk ⟨j.1, by rw [← hj]⟩
  have hE𝒞 : E ≤ caseACentralizer G Ω α X.β v X.Λ := by
    intro e he
    obtain ⟨hJ, hēS, hēē, hψ⟩ := hEinv e he
    set ē : jHull (centralizerImage Ω T') (fixSet Ω T') := ⟨_, hJ⟩
    have hfixē : ∀ ω : fixSet Ω T', (∀ k, DK.ρ k ē (DK.coord ω k) = DK.coord ω k) →
        e • (ω : Ω) = ω := fun ω hω =>
      congrArg Subtype.val (DK.smul_eq_of_rho_eq h24 hēS hēē hω)
    refine ⟨⟨?_, hEα e he, ?_⟩, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ ⟨n, rfl⟩
      exact ((hxc e (hEW he) (hEx e he)).zpow_right n).eq.symm
    · exact hfixē b (hfixQ _ hxb _ hψ)
    · refine (mem_fixingSubgroup_iff G).mpr fun l hl => ?_
      rw [hΛ] at hl
      obtain ⟨δ, hδL, rfl⟩ := hl
      refine hfixē ⟨δ, hΔT δ δ.2⟩ fun k => ?_
      by_cases hk : k ∈ Set.range c'
      · obtain ⟨j, rfl⟩ := hk
        by_cases hj : j = i₀
        · subst hj
          show (psiHom DK ē) (c' j) _ = _
          rw [hQi₀ _ hψ, Equiv.Perm.one_apply]
        · have hco : DK.coord (⟨δ, hΔT δ δ.2⟩ : fixSet Ω T') (c' j) = DK.coord g₀ (c' j) :=
            ((hcfib ⟨j, hnt j⟩ _ g₀ δ.2 X.γ.2).1).mpr (hδL j hj)
          rw [hco]
          exact hfixQ _ hxg _ hψ (c' j)
      · rw [(hcpar k (hrange k hk) ⟨δ, hΔT δ δ.2⟩ δ.2).1]
        exact hfixQ _ hxa _ hψ k
  refine ⟨E, hE2, hE𝒞, X.fixSet_subset_of_coord hS hP h2 hΛ hE𝒞 fun j hj => ?_⟩
  obtain ⟨g, hg, hJ, hgψ⟩ := hEsurj _ (Subgroup.subset_closure ⟨j, hj, rfl⟩)
  refine ⟨g, hg, fun δ => ?_⟩
  have hgδ : g • (δ : Ω) ∈ Δ := X.smul_mem_holtDelta (stabilizer_inf_le_stabilizer_pair α X.β
    (Subgroup.mem_inf.mp (hE𝒞 hg)).1.2) δ.2
  have hvδ : v • (δ : Ω) ∈ Δ := X.smul_mem_holtDelta (X.v_mem_pair hP) δ.2
  set gJ : jHull (centralizerImage Ω T') (fixSet Ω T') := ⟨_, hJ⟩
  have h1 : DK.coord (⟨g • (δ : Ω), hΔT _ hgδ⟩ : fixSet Ω T') (c' j) =
      DK.coord (⟨v • (δ : Ω), hΔT _ hvδ⟩ : fixSet Ω T') (c' j) := by
    have e1 : (⟨g • (δ : Ω), hΔT _ hgδ⟩ : fixSet Ω T') =
        (gJ : centralizerImage Ω T') • (⟨δ, hΔT δ δ.2⟩ : fixSet Ω T') := rfl
    have e2 : (⟨v • (δ : Ω), hΔT _ hvδ⟩ : fixSet Ω T') =
        (xJ : centralizerImage Ω T') • (⟨δ, hΔT δ δ.2⟩ : fixSet Ω T') :=
      Subtype.ext (hxv _ (hΔT δ δ.2)).symm
    rw [e1, e2, DK.coord_smul gJ, DK.coord_smul xJ]
    have := congrFun hgψ (c' j)
    simp only at this
    rw [show DK.ρ (c' j) gJ = DK.ρ (c' j) (ℓ j) from this, hℓρ j]
  have h2 := ((hcfib ⟨j, hnt j⟩ _ _ hgδ hvδ).1).mp h1
  rw [show X.A.D.coord ⟨g • (δ : Ω), _⟩ j = X.A.D.coord ⟨g • (δ : Ω), hgδ⟩ j from rfl, h2]
  exact (X.coord_v hS hP).1 δ j

end CaseAStart

end Start

section Endgame

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem le_twoPointNormalizer_of_card_ι_eq_one {α β : Ω}
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) (h1 : Fintype.card D.ι = 1)
    (i : D.ι) : stabilizer G ({α, β} : Set Ω) ≤ twoPointNormalizer G Ω α β (D.L i) := by
  intro g hg
  rw [mem_twoPointNormalizer]
  refine ⟨hg, ?_⟩
  obtain ⟨σ, hσ⟩ := D.conj_L ⟨twoPointHom G Ω α β ⟨g, hg⟩, twoPointHom_mem_twoPointSection _⟩
  have hσi : σ i = i := Fintype.card_le_one_iff.mp h1.le _ _
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have := hσ i
  rw [hσi] at this
  exact this.symm

omit [FaithfulSMul G Ω] in
theorem Sec4Setting.typeB_of_caseA_output (hS : Sec4Setting G Ω) {α : Ω} {v : G}
    {P : Subgroup (typeLSection G Ω v)} (hP : Prop46Setup G Ω α v P)
    (h43 : ∀ a b : Ω, a ≠ b → IsEmpty (AltConfig G Ω a b)) (hD : CaseAStepA7 G Ω α v P)
    (X : CaseAStart G Ω α v P) {V : Subgroup G}
    (hVs : fusionIsSylowIn 2 V (caseACentralizer G Ω α X.β v X.Λ))
    (hVw : X.w ∈ Subgroup.normalizer (V : Set G)) (hκ : IsKappaMaximal X V) (hV1 : V ≠ ⊥)
    {r : G} {β₁ γ₁ : Ω} (hr2 : IsPGroup 2 (Subgroup.zpowers r))
    (hrV : r ∈ Subgroup.centralizer (V : Set G)) (hrv : Commute r v) (hrα : r • α = α)
    (hfix : fixSet Ω (V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r) = {α, β₁, γ₁})
    (hβ₁ : β₁ ∈ p46Orbit G Ω v P α) (hβ₁α : β₁ ≠ α) (hγ₁C : γ₁ ∈ p46Orbit G Ω v P α)
    (hγ₁ : γ₁ ∈ holtDelta G Ω α β₁) (hvγ₁ : v • γ₁ = γ₁)
    (h5 : 5 ≤ (holtDelta G Ω α β₁ ∩ fixSet Ω V).ncard)
    (horb : ∃ (hb : X.β ∈ fixSet Ω V) (hb₁ : β₁ ∈ fixSet Ω V) (hc : (X.γ : Ω) ∈ fixSet Ω V)
          (hc₁ : γ₁ ∈ fixSet Ω V),
        (⟨β₁, hb₁⟩ : fixSet Ω V) ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V))
          ⟨X.β, hb⟩ ∧
        (⟨γ₁, hc₁⟩ : fixSet Ω V) ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V))
          ⟨X.γ, hc⟩) :
    IsTypeBAt G Ω α β₁ ∧ Nat.card (holtDelta G Ω α β₁) ≠ 5 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαβ₁ : α ≠ β₁ := hβ₁α.symm
  have hγα : γ₁ ≠ α := fun h => left_notMem_holtDelta hαβ₁ (h ▸ hγ₁)
  have hγβ : γ₁ ≠ β₁ := fun h => right_notMem_holtDelta hαβ₁ (h ▸ hγ₁)
  set 𝔛 := V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r
  have hVv : v ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp ((hVs.1 hg).1.1) v (Subgroup.mem_zpowers v)).symm
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := zpowers_isPGroup_two_of_pow_eq_one (n := 1)
    (by rw [pow_one, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one])
  have h𝔛2 : IsPGroup 2 𝔛 := by
    have h1 : IsPGroup 2 (V ⊔ Subgroup.zpowers v : Subgroup G) :=
      hVs.2.1.to_sup_of_normal_left' hv2
        (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hVv))
    refine h1.to_sup_of_normal_left' hr2 (Subgroup.zpowers_le.mpr
      (Subgroup.centralizer_le_normalizer _ ?_))
    have h2 : V ⊔ Subgroup.zpowers v ≤ Subgroup.centralizer
        ((Subgroup.zpowers r : Subgroup G) : Set G) := by
      refine sup_le ?_ ?_
      · exact Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hrV)
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun g hg => by
          obtain ⟨n, rfl⟩ := hg
          exact (hrv.zpow_left n).eq)
    exact Subgroup.le_centralizer_iff.mp h2 (Subgroup.mem_zpowers r)
  have hmem : ∀ ω ∈ ({α, β₁, γ₁} : Set Ω), ω ∈ fixSet Ω 𝔛 := fun ω hω => by rw [hfix]; exact hω
  have hfα := hmem α (by simp)
  have hfβ := hmem β₁ (by simp)
  have hfγ := hmem γ₁ (by simp)
  have h𝔛st : 𝔛 ≤ stabilizer G α ⊓ stabilizer G β₁ ⊓ stabilizer G γ₁ := fun g hg =>
    ⟨⟨hfα g hg, hfβ g hg⟩, hfγ g hg⟩
  have h𝔛pair : 𝔛 ≤ stabilizer G ({α, β₁} : Set Ω) := fun g hg =>
    stabilizer_inf_le_stabilizer_pair α β₁ ⟨hfα g hg, hfβ g hg⟩
  have hfixV : fixSet Ω 𝔛 ⊆ fixSet Ω V := fixSet_anti (le_sup_left.trans le_sup_left)
  have hΔ5 : 5 ≤ Nat.card (holtDelta G Ω α β₁) := by
    rw [Nat.card_coe_set_eq]
    exact h5.trans (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _))
  have h3 : Nat.card ({α, β₁, γ₁} : Set Ω) = 3 := by
    rw [Nat.card_coe_set_eq]
    exact Set.ncard_eq_three.mpr ⟨α, β₁, γ₁, hαβ₁, hγα.symm, hγβ.symm, rfl⟩
  rcases hP.typeAB β₁ hβ₁ hβ₁α (by omega) with hA₁ | hBt
  ·
    exfalso
    obtain ⟨A₁⟩ : Nonempty (CaseAData G Ω α β₁) := hA₁
    have hne : Nonempty A₁.D.ι := by
      by_contra hι
      rw [not_nonempty_iff] at hι
      have hsub : (holtDelta G Ω α β₁).Subsingleton := fun δ hδ δ' hδ' => by
        have h1 := (A₁.D.coord_eq_iff ⟨δ, hδ⟩ ⟨δ', hδ'⟩).mp (Subsingleton.elim _ _)
        rw [orbit_jOddCore_eq_singleton A₁.oddCore_eq_bot] at h1
        exact (congrArg Subtype.val (Set.mem_singleton_iff.mp h1)).symm
      have : (holtDelta G Ω α β₁).ncard ≤ 1 := Set.ncard_le_one_iff_subsingleton.mpr hsub
      rw [Nat.card_coe_set_eq] at hΔ5
      omega
    obtain ⟨j, hj⟩ : ∃ j, 𝔛 ≤ twoPointNormalizer G Ω α β₁ (A₁.D.L j) := by
      by_cases h2 : 2 ≤ Fintype.card A₁.D.ι
      · exact hD X V hVs hVw hκ r β₁ γ₁ hr2 hrV hrv hrα hfix hβ₁ hγ₁C hγ₁ hvγ₁ h5 horb A₁ h2
      · obtain ⟨i⟩ := hne
        have h1 : Fintype.card A₁.D.ι = 1 := by
          have := Fintype.card_pos_iff.mpr ⟨i⟩
          omega
        exact ⟨i, h𝔛pair.trans (le_twoPointNormalizer_of_card_ι_eq_one A₁.D h1 i)⟩
    obtain ⟨S₁, h𝔛S₁, hS₁⟩ := exists_fusionIsSylowIn_ge h𝔛2 h𝔛st
    obtain ⟨-, w₁, hw₁, hw₁γ, hw₁S⟩ := hS.sylow_twoPoint hαβ₁ hγ₁ hS₁
    have hfix3 : fixSet Ω (S₁ ⊓ twoPointNormalizer G Ω α β₁ (A₁.D.L j)) = {α, β₁, γ₁} := by
      refine le_antisymm ?_ fun ω hω g hg => ?_
      · rw [← hfix]
        exact fixSet_anti (le_inf h𝔛S₁ hj)
      · have hgS := hS₁.1 (Subgroup.mem_inf.mp hg).1
        rcases hω with rfl | rfl | rfl
        · exact hgS.1.1
        · exact hgS.1.2
        · exact hgS.2
    exact (h43 α β₁ hαβ₁).false
      { D := A₁.D, oddCore_eq_bot := A₁.oddCore_eq_bot, i₁ := j, alt := A₁.alt
        mod4 := fun i _ => A₁.mod4 i, γ := ⟨γ₁, hγ₁⟩, S := S₁, sylow := hS₁, w := w₁
        w_mem := hw₁, w_fix := hw₁γ, w_comm := hw₁S
        fix_three := by rw [hfix3, h3]
        fix_five := fun h => absurd ((A₁.mod4 j).symm.trans h) (by norm_num)
        five := fun h1 h5' => A₁.five h1 j h5' }
  ·
    refine ⟨hBt, fun h5' => ?_⟩
    have hsub : holtDelta G Ω α β₁ ⊆ fixSet Ω V := by
      have heq : holtDelta G Ω α β₁ ∩ fixSet Ω V = holtDelta G Ω α β₁ :=
        Set.eq_of_subset_of_ncard_le Set.inter_subset_left
          (by rw [Nat.card_coe_set_eq] at h5'; omega) (Set.toFinite _)
      rw [← heq]; exact Set.inter_subset_right
    have hVK : V ≤ twoPointKernel G Ω α β₁ := fun g hg =>
      ⟨⟨hfixV hfα g hg, hfixV hfβ g hg⟩, (mem_fixingSubgroup_iff G).mpr fun δ hδ =>
        hsub hδ g hg⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hVs.2.1
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hV1 (Subgroup.card_eq_one.mp (by rw [hn, pow_zero]))
    have hdvd : 2 ∣ Nat.card (twoPointKernel G Ω α β₁) :=
      (dvd_pow_self 2 hn0).trans (hn ▸ Subgroup.card_dvd_of_le hVK)
    exact Nat.not_even_iff_odd.mpr hBt.2 (even_iff_two_dvd.mpr hdvd)

end Endgame

end CFSG.Holt.H78
