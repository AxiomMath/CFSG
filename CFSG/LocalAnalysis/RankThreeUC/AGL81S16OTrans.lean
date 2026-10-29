module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OAct

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite)

section Model

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem transvection_quad (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)
    (hiso : ∀ x, StatedQuadMinus 3 F b c (A *ᵥ x) = StatedQuadMinus 3 F b c x) (u : OW F)
    (hu : ∀ x : OW F, ∃ r : F, (A - 1) *ᵥ x = r • u) :
    ∀ x : OW F, (A - 1) *ᵥ x ≠ 0 → StatedQuadMinus 3 F b c ((A - 1) *ᵥ x) ≠ 0 := by
  intro x₁ hx₁
  have hQn := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  have hiso' : ∀ x, quadMinus 3 F b c (A *ᵥ x) = quadMinus 3 F b c x := fun x => by
    rw [quadMinus_eq_stated, quadMinus_eq_stated]
    exact hiso x
  have hu0 : u ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ := hu x₁
    apply hx₁
    rw [hr, h, smul_zero]
  have hmain : quadMinus 3 F b c u ≠ 0 := by
    intro hQu
    have key : ∀ x, (A - 1) *ᵥ x ≠ 0 → polar (quadMinus 3 F b c) x u = 0 := by
      intro x hx
      obtain ⟨r, hr⟩ := hu x
      have hr0 : r ≠ 0 := by
        intro h
        apply hx
        rw [hr, h, zero_smul]
      have hAx : A *ᵥ x = x + (A - 1) *ᵥ x := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
      have h1 := hiso' x
      rw [hAx, hr, QuadraticMap.map_add (quadMinus 3 F b c), map_smul_eq_sq, polar_smul_right_eq,
        hQu] at h1
      have h3 : r * polar (quadMinus 3 F b c) x u = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h3).resolve_left hr0
    obtain ⟨x₂, hx₂⟩ := exists_polar_ne_zero hQn hu0
    have hx₂' : polar (quadMinus 3 F b c) x₂ u ≠ 0 := by rwa [polar_comm]
    have hN2 : (A - 1) *ᵥ x₂ = 0 := by
      by_contra h
      exact hx₂' (key x₂ h)
    have hx3 : (A - 1) *ᵥ (x₁ + x₂) ≠ 0 := by
      rw [Matrix.mulVec_add, hN2, add_zero]
      exact hx₁
    have h4 := key (x₁ + x₂) hx3
    rw [polar_add_left, key x₁ hx₁, zero_add] at h4
    exact hx₂' h4
  obtain ⟨r, hr⟩ := hu x₁
  have hr0 : r ≠ 0 := by
    intro h
    apply hx₁
    rw [hr, h, zero_smul]
  rw [← quadMinus_eq_stated, hr, map_smul_eq_sq]
  exact mul_ne_zero (pow_ne_zero 2 hr0) hmain

end Model

section Model2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem exists_outer_quad (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)
    (hAA : A * A = 1)
    (hiso : ∀ x, StatedQuadMinus 3 F b c (A *ᵥ x) = StatedQuadMinus 3 F b c x)
    (hnot : (⟨A, A, hAA, hAA⟩ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) ∉
      StatedOmega (StatedQuadMinus 3 F b c)) :
    ∃ x : OW F, StatedQuadMinus 3 F b c ((A - 1) *ᵥ x) ≠ 0 := by
  have hQn := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  set g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F := ⟨A, A, hAA, hAA⟩ with hg
  set ℓ : OW F ≃ₗ[F] OW F := toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F g with hℓ
  have hℓx : ∀ x, ℓ x = A *ᵥ x := fun x => rfl
  have hO : ℓ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 F b c) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    rw [hℓx, quadMinus_eq_stated, quadMinus_eq_stated]
    exact hiso x
  have hℓℓ : ℓ * ℓ = 1 := by
    refine LinearEquiv.ext fun x => ?_
    show A *ᵥ (A *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  by_contra hcon
  push Not at hcon
  have hzero : ∀ y ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace ℓ,
      quadMinus 3 F b c y = 0 := by
    intro y hy
    obtain ⟨x, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hy
    rw [quadMinus_eq_stated]
    have := hcon x
    rw [hℓx, Matrix.sub_mulVec, Matrix.one_mulVec] at *
    simpa [hℓx] using this
  have heven := CFSG.RankThree.OrthogonalInvolutions.even_finrank_commSpace_of_forall_eq_zero hQn hO
    hℓℓ hzero
  apply hnot
  rw [mem_statedOmega_iff]
  have hmem : ℓ ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (quadMinus 3 F b c) hQn :=
    CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨hO, heven⟩
  rw [← omegaGroup_eq_commutator hQn (quadMinus_three_derived hirr).1]
  exact hmem

end Model2

section GLevel

variable {G : Type} [Group G] [Finite G] {n : ℕ} {M L V : Subgroup G} (d : O6NatData G n L V)

theorem O6NatData.eqv_inv (v : ↥V) : d.eqv v⁻¹ = - d.eqv v := by
  have h : d.eqv (v⁻¹ * v) = d.eqv v⁻¹ + d.eqv v := d.eqv_mul _ _
  rw [inv_mul_cancel] at h
  have h0 : d.eqv (1 : ↥V) = 0 := by
    rw [O6NatData.eqv_apply, map_one, toAdd_one]
  rw [h0] at h
  exact (neg_eq_of_add_eq_zero_left h.symm).symm

theorem O6NatData.eqv_one : d.eqv (1 : ↥V) = 0 := by
  rw [O6NatData.eqv_apply, map_one, toAdd_one]

theorem O6NatData.card_centralizer_eq (hMV : M ≤ normalizer (V : Set G)) {t : G} (ht : t ∈ M) :
    Nat.card ↥(V ⊓ centralizer ({t} : Set G)) =
      Nat.card {x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F // d.act t (hMV ht) x = x} := by
  have hfix : ∀ g : ↥(V ⊓ centralizer ({t} : Set G)),
      d.act t (hMV ht) (d.eqv ⟨(g : G), g.2.1⟩) = d.eqv ⟨(g : G), g.2.1⟩ := by
    intro g
    have hg := Subgroup.mem_centralizer_iff.mp g.2.2 t (Set.mem_singleton t)
    rw [d.act_eqv]
    refine congrArg d.eqv (Subtype.ext ?_)
    show t * (g : G) * t⁻¹ = (g : G)
    rw [mul_inv_eq_iff_eq_mul]
    exact hg
  refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨d.eqv ⟨(g : G), g.2.1⟩, hfix g⟩) ⟨?_, ?_⟩)
  · intro g g' h
    have h1 : d.eqv ⟨(g : G), g.2.1⟩ = d.eqv ⟨(g' : G), g'.2.1⟩ := congrArg Subtype.val h
    have h2 := d.eqv.injective h1
    exact Subtype.ext (by simpa using congrArg (fun z : ↥V => (z : G)) h2)
  · rintro ⟨x, hx⟩
    obtain ⟨v, rfl⟩ := d.eqv.surjective x
    rw [d.act_eqv] at hx
    have h2 : conjOn V t (hMV ht) v = v := d.eqv.injective hx
    have h3 : t * (v : G) * t⁻¹ = (v : G) := congrArg Subtype.val h2
    refine ⟨⟨(v : G), v.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩, rfl⟩
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc t * (v : G) = (t * (v : G) * t⁻¹) * t := by group
      _ = (v : G) * t := by rw [h3]


theorem O6NatData.exists_matrix (hMV : M ≤ normalizer (V : Set G)) {m : G} (hm : m ∈ M)
    (hlin : ∀ (c : d.F) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F),
      d.act m (hMV hm) (c • x) = c • d.act m (hMV hm) x) :
    ∃ A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F,
      ∀ x, A *ᵥ x = d.act m (hMV hm) x := by
  let lin : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) →ₗ[d.F]
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) :=
    { toFun := d.act m (hMV hm)
      map_add' := d.act_add m (hMV hm)
      map_smul' := hlin }
  refine ⟨LinearMap.toMatrix' lin, fun x => ?_⟩
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

theorem O6NatData.matrix_pow (hMV : M ≤ normalizer (V : Set G)) {m : G} (hm : m ∈ M)
    {A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F}
    (hA : ∀ x, A *ᵥ x = d.act m (hMV hm) x) (k : ℕ) (hmk : m ^ (2 ^ k) = 1) :
    A ^ (2 ^ k) = 1 := by
  have hpow : ∀ (j : ℕ) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F),
      (A ^ j) *ᵥ x = ((d.rho M hMV ⟨m, hm⟩) ^ j) x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hA, pow_succ', Equiv.Perm.mul_apply,
        O6NatData.rho_apply]
  have hP : (d.rho M hMV ⟨m, hm⟩) ^ (2 ^ k) = 1 := by
    rw [← map_pow]
    have : (⟨m, hm⟩ : ↥M) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hmk)
    rw [this, map_one]
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [hpow, hP, Equiv.Perm.one_apply, Matrix.one_mulVec]

theorem O6NatData.eqv_comm (hMV : M ≤ normalizer (V : Set G)) {t : G} (ht : t ∈ M) {v : G}
    (hv : v ∈ V) (hc : ⁅t, v⁆ ∈ V) :
    d.eqv ⟨⁅t, v⁆, hc⟩ = d.act t (hMV ht) (d.eqv ⟨v, hv⟩) - d.eqv ⟨v, hv⟩ := by
  have h1 : (⟨⁅t, v⁆, hc⟩ : ↥V) = conjOn V t (hMV ht) ⟨v, hv⟩ * (⟨v, hv⟩ : ↥V)⁻¹ := by
    apply Subtype.ext
    simp [commutatorElement_def, mul_assoc]
  rw [h1, d.eqv_mul, d.eqv_inv, ← d.act_eqv]
  abel


theorem O6NatData.transvection (hn : 1 ≤ n) (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ t ∈ M, IsPGroup 2 ↥(zpowers t) → t ∉ centralizer (V : Set G) →
      (V ⊓ centralizer ({t} : Set G)).relIndex V < 2 ^ (2 * n) →
      ∀ v ∈ V, ⁅t, v⁆ ≠ 1 → ¬ d.sing ⁅t, v⁆ := by
  intro t htM h2g htC hidx v hv hcomm hsing
  haveI := d.charP hn
  obtain ⟨θ, hθ⟩ := d.act_semilinear hn hLM hML hMV htM
  have hmul : (V ⊓ centralizer ({t} : Set G)).relIndex V *
      Nat.card ↥(V ⊓ centralizer ({t} : Set G)) = 2 ^ (6 * n) := by
    have h := Subgroup.relIndex_mul_card (H := V ⊓ centralizer ({t} : Set G)) (K := V)
    rw [inf_eq_left.mpr inf_le_left] at h
    rw [h, d.card_V]
  have hfix := d.card_centralizer_eq hMV htM
  by_cases hθid : θ = RingHom.id d.F
  ·
    have hlin : ∀ (c : d.F) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F),
        d.act t (hMV htM) (c • x) = c • d.act t (hMV htM) x := by
      intro c x
      rw [hθ c x, hθid]
      rfl
    obtain ⟨A, hA⟩ := d.exists_matrix hMV htM hlin
    obtain ⟨k₂, hk₂⟩ := h2g ⟨t, mem_zpowers t⟩
    have htk : t ^ (2 ^ k₂) = 1 := by simpa using congrArg Subtype.val hk₂
    have hAk := d.matrix_pow hMV htM hA k₂ htk
    have hN : ∀ g ∈ StatedOmega (StatedQuadMinus 3 d.F d.b d.c),
        ∃ g' ∈ StatedOmega (StatedQuadMinus 3 d.F d.b d.c),
          ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F,
          A *ᵥ ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            d.F) *ᵥ x) =
            (g' : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
              d.F) *ᵥ (A *ᵥ x) := by
      intro g hg
      obtain ⟨g', hg', hgx⟩ := d.act_normalizes hLM hML hMV htM hg
      exact ⟨g', hg', fun x => by rw [hA, hA, hgx]⟩
    have hiso := omega_isometry_of_normalizes_pow d.irred A k₂ hAk hN
    have hu' : ∃ u : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F, ∀ x, ∃ r : d.F,
        (A - 1) *ᵥ x = r • u := by
      let Nlin : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) →ₗ[d.F]
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) := Matrix.mulVecLin (A - 1)
      have hkerx : ∀ x, x ∈ LinearMap.ker Nlin ↔ d.act t (hMV htM) x = x := by
        intro x
        rw [LinearMap.mem_ker]
        show (A - 1) *ᵥ x = 0 ↔ _
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA, sub_eq_zero]
      have hcardker : Nat.card ↥(LinearMap.ker Nlin) =
          Nat.card ↥(V ⊓ centralizer ({t} : Set G)) := by
        rw [hfix]
        exact Nat.card_congr (Equiv.subtypeEquivRight hkerx)
      have hrn := LinearMap.finrank_range_add_finrank_ker Nlin
      have hfr : Module.finrank d.F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) = 6 := by
        simp [Module.finrank_fintype_fun_eq_card]
      rw [hfr] at hrn
      have hkpow : Nat.card ↥(V ⊓ centralizer ({t} : Set G)) =
          (2 ^ n) ^ Module.finrank d.F ↥(LinearMap.ker Nlin) := by
        rw [← hcardker, Module.natCard_eq_pow_finrank (K := d.F) (V := ↥(LinearMap.ker Nlin)),
          d.card_F]
      have hq2 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
      have hpos : 0 < (2 ^ n) ^ Module.finrank d.F ↥(LinearMap.ker Nlin) := by positivity
      have hrel : (V ⊓ centralizer ({t} : Set G)).relIndex V =
          (2 ^ n) ^ Module.finrank d.F ↥(LinearMap.range Nlin) := by
        have h1 : (V ⊓ centralizer ({t} : Set G)).relIndex V *
            (2 ^ n) ^ Module.finrank d.F ↥(LinearMap.ker Nlin) =
            (2 ^ n) ^ Module.finrank d.F ↥(LinearMap.range Nlin) *
              (2 ^ n) ^ Module.finrank d.F ↥(LinearMap.ker Nlin) := by
          calc (V ⊓ centralizer ({t} : Set G)).relIndex V *
                (2 ^ n) ^ Module.finrank d.F ↥(LinearMap.ker Nlin)
              = (V ⊓ centralizer ({t} : Set G)).relIndex V *
                Nat.card ↥(V ⊓ centralizer ({t} : Set G)) := by rw [← hkpow]
            _ = 2 ^ (6 * n) := hmul
            _ = (2 ^ n) ^ (Module.finrank d.F ↥(LinearMap.range Nlin) +
                Module.finrank d.F ↥(LinearMap.ker Nlin)) := by
              rw [hrn, ← pow_mul, mul_comm]
            _ = (2 ^ n) ^ Module.finrank d.F ↥(LinearMap.range Nlin) *
                (2 ^ n) ^ Module.finrank d.F ↥(LinearMap.ker Nlin) := pow_add _ _ _
        exact Nat.eq_of_mul_eq_mul_right hpos h1
      have hlt : (2 ^ n) ^ Module.finrank d.F ↥(LinearMap.range Nlin) < (2 ^ n) ^ 2 := by
        rw [← hrel, ← pow_mul, mul_comm]
        exact hidx
      have hr2 : Module.finrank d.F ↥(LinearMap.range Nlin) < 2 :=
        (Nat.pow_lt_pow_iff_right hq2).mp hlt
      obtain ⟨w, hw⟩ := (finrank_le_one_iff (K := d.F) (V := ↥(LinearMap.range Nlin))).mp
        (by omega)
      refine ⟨(w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F), fun x => ?_⟩
      obtain ⟨r, hr⟩ := hw ⟨Nlin x, LinearMap.mem_range_self Nlin x⟩
      exact ⟨r, (congrArg Subtype.val hr).symm⟩
    obtain ⟨u, hu⟩ := hu'
    obtain ⟨hx, hQ⟩ := hsing
    have hcomm' : d.eqv ⟨⁅t, v⁆, hx⟩ = (A - 1) *ᵥ d.eqv ⟨v, hv⟩ := by
      rw [d.eqv_comm hMV htM hv hx, Matrix.sub_mulVec, Matrix.one_mulVec, hA]
    have hne : (A - 1) *ᵥ d.eqv ⟨v, hv⟩ ≠ 0 := by
      rw [← hcomm']
      intro h
      apply hcomm
      have h1 : (⟨⁅t, v⁆, hx⟩ : ↥V) = 1 := d.eqv.injective (h.trans d.eqv_one.symm)
      exact congrArg Subtype.val h1
    have := transvection_quad d.irred A hiso u hu (d.eqv ⟨v, hv⟩) hne
    rw [← hcomm'] at this
    exact this hQ
  · exfalso
    have hsq := card_fix_sq_le hθid (d.actAddEquiv hMV htM) hθ
    have hW : Nat.card (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) = 2 ^ (6 * n) := by
      rw [← d.card_V]
      exact (Nat.card_congr d.eqv).symm
    rw [hW] at hsq
    change Nat.card {x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F // d.act t (hMV htM) x = x} ^ 2 ≤
      2 ^ (6 * n) at hsq
    rw [← hfix] at hsq
    set k := Nat.card ↥(V ⊓ centralizer ({t} : Set G)) with hk
    set r := (V ⊓ centralizer ({t} : Set G)).relIndex V with hr
    have hk3 : k ≤ 2 ^ (3 * n) := by
      by_contra h
      push Not at h
      have : (2 ^ (3 * n)) ^ 2 < k ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
      have e : (2 ^ (3 * n)) ^ 2 = 2 ^ (6 * n) := by ring
      omega
    have hkpos : 0 < k := Nat.card_pos
    have h1 : r * k < 2 ^ (2 * n) * 2 ^ (3 * n) :=
      calc r * k ≤ r * 2 ^ (3 * n) := Nat.mul_le_mul le_rfl hk3
        _ < 2 ^ (2 * n) * 2 ^ (3 * n) := Nat.mul_lt_mul_of_pos_right hidx (by positivity)
    have e2 : 2 ^ (2 * n) * 2 ^ (3 * n) = 2 ^ (5 * n) := by rw [← pow_add]; congr 1; ring
    have h5 : 2 ^ (5 * n) < 2 ^ (6 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega


theorem O6NatData.exists_of_quad (hn : 1 ≤ n) (hMV : M ≤ normalizer (V : Set G)) {a : G}
    (ha : a ∈ M) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F)
    (hx : StatedQuadMinus 3 d.F d.b d.c (d.act a (hMV ha) x - x) ≠ 0) :
    ∃ v ∈ V, ⁅a, v⁆ ≠ 1 ∧ ¬ d.sing ⁅a, v⁆ := by
  haveI := d.charP hn
  set w : ↥V := d.eqv.symm x with hw
  have hwx : d.eqv w = x := d.eqv.apply_symm_apply x
  have hc : ⁅a, (w : G)⁆ ∈ V := by
    have h1 : ⁅a, (w : G)⁆ = ((conjOn V a (hMV ha) w : ↥V) : G) * ((w⁻¹ : ↥V) : G) := by
      simp [commutatorElement_def, mul_assoc]
    rw [h1]
    exact V.mul_mem (conjOn V a (hMV ha) w).2 (w⁻¹).2
  have hcomm : d.eqv ⟨⁅a, (w : G)⁆, hc⟩ = d.act a (hMV ha) x - x := by
    have := d.eqv_comm hMV ha w.2 hc
    rw [hwx] at this
    simpa using this
  refine ⟨(w : G), w.2, ?_, ?_⟩
  · intro h1
    apply hx
    have h2 : (⟨⁅a, (w : G)⁆, hc⟩ : ↥V) = 1 := Subtype.ext h1
    rw [← hcomm, h2, d.eqv_one]
    exact stated_quad_zero
  · rintro ⟨hx', hQ⟩
    apply hx
    have : Multiplicative.toAdd (d.φ ⟨⁅a, (w : G)⁆, hx'⟩) = d.act a (hMV ha) x - x := hcomm
    rw [← this]
    exact hQ

theorem O6NatData.outer_nonsing (hn : 1 ≤ n) (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ a ∈ M, a ^ 2 = 1 → a ∉ L ⊔ (M ⊓ centralizer (V : Set G)) →
      ∃ v ∈ V, ⁅a, v⁆ ≠ 1 ∧ ¬ d.sing ⁅a, v⁆ := by
  intro a haM ha2 haLC
  haveI := d.charP hn
  obtain ⟨θ, hθ⟩ := d.act_semilinear hn hLM hML hMV haM
  by_cases hθid : θ = RingHom.id d.F
  ·
    have hlin : ∀ (c : d.F) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F),
        d.act a (hMV haM) (c • x) = c • d.act a (hMV haM) x := by
      intro c x
      rw [hθ c x, hθid]
      rfl
    obtain ⟨A, hA⟩ := d.exists_matrix hMV haM hlin
    have hAA : A * A = 1 := by
      have := d.matrix_pow hMV haM hA 1 (by simpa using ha2)
      simpa [pow_two] using this
    have hN : ∀ g ∈ StatedOmega (StatedQuadMinus 3 d.F d.b d.c),
        ∃ g' ∈ StatedOmega (StatedQuadMinus 3 d.F d.b d.c),
          ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F,
          A *ᵥ ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            d.F) *ᵥ x) =
            (g' : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
              d.F) *ᵥ (A *ᵥ x) := by
      intro g hg
      obtain ⟨g', hg', hgx⟩ := d.act_normalizes hLM hML hMV haM hg
      exact ⟨g', hg', fun x => by rw [hA, hA, hgx]⟩
    have hiso := omega_isometry_of_normalizes d.irred A hAA hN
    have hnot : (⟨A, A, hAA, hAA⟩ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) ∉
        StatedOmega (StatedQuadMinus 3 d.F d.b d.c) := by
      intro hgΩ
      obtain ⟨l, hl⟩ := d.ε_surj ⟨_, hgΩ⟩
      have hlL : (l : G) ∈ L := l.2
      have hlV : (l : G) ∈ normalizer (V : Set G) := hMV (hLM hlL)
      have hlM : (l : G) ∈ M := hLM hlL
      have hgl : ((d.ε ⟨(l : G), hlL⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
          GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) =
          (⟨A, A, hAA, hAA⟩ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) := congrArg Subtype.val hl
      have hact : ∀ x, d.act (l : G) hlV x = d.act a (hMV haM) x := by
        intro x
        obtain ⟨v, rfl⟩ := d.eqv.surjective x
        rw [d.act_eqv, ← d.eps_eqv hlL hlV v, hgl, ← hA]
      have hm : a⁻¹ * (l : G) ∈ M := M.mul_mem (M.inv_mem haM) hlM
      have htriv : ∀ x, d.act (a⁻¹ * (l : G)) (hMV hm) x = x := by
        intro x
        have h1 : d.rho M hMV ⟨a⁻¹ * (l : G), hm⟩ =
            d.rho M hMV ⟨a⁻¹, M.inv_mem haM⟩ * d.rho M hMV ⟨(l : G), hlM⟩ := by
          rw [← map_mul]
          rfl
        have h2 := congrArg (fun f => f x) h1
        simp only [Equiv.Perm.mul_apply] at h2
        rw [O6NatData.rho_apply, O6NatData.rho_apply, O6NatData.rho_apply] at h2
        rw [h2]
        show d.act a⁻¹ (hMV (M.inv_mem haM)) (d.act (l : G) (hMV hlM) x) = x
        rw [hact x]
        exact d.act_inv_act hMV haM x
      have hcent := d.mem_centralizer_of_act_eq hMV hm htriv
      apply haLC
      have : a = (l : G) * (a⁻¹ * (l : G))⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem_sup hlL (Subgroup.inv_mem _ ⟨hm, hcent⟩)
    obtain ⟨x, hx⟩ := exists_outer_quad d.irred A hAA hiso hnot
    refine d.exists_of_quad hn hMV haM x ?_
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA] at hx
    exact hx
  ·
    by_contra hcon
    have hQ0 : ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F,
        StatedQuadMinus 3 d.F d.b d.c (d.act a (hMV haM) x - x) = 0 := by
      intro x
      by_contra hne
      exact hcon (d.exists_of_quad hn hMV haM x hne)
    let ψ : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) →+
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) :=
      (d.actAddEquiv hMV haM).toAddMonoidHom - AddMonoidHom.id _
    have hψ : ∀ x, ψ x = d.act a (hMV haM) x - x := fun x => rfl
    have hkerψ : Nat.card ψ.ker =
        Nat.card {x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F // d.act a (hMV haM) x = x} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      rw [AddMonoidHom.mem_ker, hψ, sub_eq_zero]
    have hmulψ := AddSubgroup.card_ker_mul_card_range ψ
    have hW : Nat.card (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) = 2 ^ (6 * n) := by
      rw [← d.card_V]
      exact (Nat.card_congr d.eqv).symm
    have hY : ∀ y ∈ ψ.range, StatedQuadMinus 3 d.F d.b d.c y = 0 := by
      rintro _ ⟨x, rfl⟩
      rw [hψ]
      exact hQ0 x
    have hyy : Nat.card ψ.range ≤ (2 ^ n) ^ 2 := by
      have := ts_card_le d.irred ψ.range hY
      rwa [d.card_F] at this
    have hsq := card_fix_sq_le hθid (d.actAddEquiv hMV haM) hθ
    rw [hW] at hsq
    change Nat.card {x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F // d.act a (hMV haM) x = x} ^ 2 ≤
      2 ^ (6 * n) at hsq
    rw [← hkerψ] at hsq
    rw [hW] at hmulψ
    set kk := Nat.card ψ.ker with hkk
    set yy := Nat.card ψ.range with hyy'
    have hk3 : kk ≤ 2 ^ (3 * n) := by
      by_contra h
      push Not at h
      have : (2 ^ (3 * n)) ^ 2 < kk ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
      have e : (2 ^ (3 * n)) ^ 2 = 2 ^ (6 * n) := by ring
      omega
    have hy2 : yy ≤ 2 ^ (2 * n) := by
      calc yy ≤ (2 ^ n) ^ 2 := hyy
        _ = 2 ^ (2 * n) := by ring
    have h1 : kk * yy ≤ 2 ^ (3 * n) * 2 ^ (2 * n) := Nat.mul_le_mul hk3 hy2
    have e2 : 2 ^ (3 * n) * 2 ^ (2 * n) = 2 ^ (5 * n) := by rw [← pow_add]; congr 1; ring
    have h5 : 2 ^ (5 * n) < 2 ^ (6 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end GLevel

end CFSG.LocalAnalysis.RankThreeUC
