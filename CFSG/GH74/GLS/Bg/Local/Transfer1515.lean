module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.GH74.GLS.Bg.Thompson

open MulAction Subgroup

section Orbits

open scoped Classical

variable {α : Type*} {G : Type*} [Group G] [MulAction G α] {A : Type*} [CommGroup A]

theorem out_mk_of_fixed {x : α} (hx : x ∈ fixedPoints G α) :
    (Quotient.mk'' x : orbitRel.Quotient G α).out = x := by
  have h := Quotient.mk_out (s := orbitRel G α) x
  obtain ⟨g, hg⟩ := (orbitRel_apply.mp h)
  exact hg.symm.trans (mem_fixedPoints.mp hx g)

theorem prod_orbitReps_fixed [Fintype α] (h : α → A) :
    ∏ ω : orbitRel.Quotient G α, (if ω.out ∈ fixedPoints G α then h ω.out else 1) =
      ∏ x : fixedPoints G α, h x := by
  rw [← Finset.prod_filter]
  refine Finset.prod_bij (fun ω hω => (⟨ω.out, (Finset.mem_filter.mp hω).2⟩ : fixedPoints G α))
    ?_ ?_ ?_ ?_
  · intro ω _; exact Finset.mem_univ _
  · intro ω₁ _ ω₂ _ h12
    have := congrArg Subtype.val h12
    simpa using this
  · intro x _
    refine ⟨(Quotient.mk'' x.1 : orbitRel.Quotient G α), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [out_mk_of_fixed x.2]; exact x.2⟩
    · exact Subtype.ext (out_mk_of_fixed x.2)
  · intro ω hω
    rfl


theorem prod_eq_prod_fixedPoints [Fintype α] {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    (f : α → A) (hinv : ∀ (g : G) (x : α), f (g • x) = f x) (hp : ∀ x, f x ^ p = 1) :
    ∏ x : α, f x = ∏ x : fixedPoints G α, f x := by
  calc ∏ x : α, f x
      = ∏ s : (ω : orbitRel.Quotient G α) × ↥(orbit G ω.out), f s.2.1 := by
        rw [← Equiv.prod_comp (selfEquivSigmaOrbits G α) (fun s => f s.2.1)]
        rfl
    _ = ∏ ω : orbitRel.Quotient G α, ∏ y : ↥(orbit G ω.out), f y.1 := Fintype.prod_sigma _
    _ = ∏ ω : orbitRel.Quotient G α, (if ω.out ∈ fixedPoints G α then f ω.out else 1) := by
        refine Finset.prod_congr rfl fun ω _ => ?_
        have hconst : ∀ y : ↥(orbit G ω.out), f y.1 = f ω.out := by
          intro y
          obtain ⟨g, hg⟩ := y.2
          rw [← hg]
          exact hinv g _
        rw [Finset.prod_congr rfl (fun y _ => hconst y), Finset.prod_const, Finset.card_univ,
          Fintype.card_eq_nat_card]
        obtain ⟨n, hn⟩ := hG.card_orbit ω.out
        rw [hn]
        by_cases h0 : n = 0
        · subst h0
          have hfix : ω.out ∈ fixedPoints G α := by
            rw [mem_fixedPoints_iff_card_orbit_eq_one, Fintype.card_eq_nat_card]
            simpa using hn
          simp only [hfix, ↓reduceIte]
          simp
        · have hnfix : ω.out ∉ fixedPoints G α := by
            intro hfix
            have := (mem_fixedPoints_iff_card_orbit_eq_one.mp hfix)
            rw [Fintype.card_eq_nat_card, hn] at this
            rcases Nat.pow_eq_one.mp this with h1 | h1
            · exact absurd h1 (Fact.out : p.Prime).one_lt.ne'
            · exact h0 h1
          simp only [hnfix, ↓reduceIte]
          obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
          rw [pow_succ, mul_comm, pow_mul, hp, one_pow]
    _ = ∏ x : fixedPoints G α, f x := prod_orbitReps_fixed f

end Orbits

section Transfer

open scoped IsMulCommutative

variable {X : Type*} [Group X]

@[expose] def IsSylowIn (p : ℕ) (P H : Subgroup X) : Prop :=
  P ≤ H ∧ IsPGroup p ↥P ∧ ¬ p ∣ P.relIndex H

@[expose] def IsExtremalIn (p : ℕ) (P : Subgroup X) (y : X) : Prop :=
  IsSylowIn p (P ⊓ Subgroup.centralizer {y}) (Subgroup.centralizer {y})

variable (P Q : Subgroup X) [(Q.subgroupOf P).Normal]

abbrev Qbar : Type _ := ↥P ⧸ Q.subgroupOf P

def phiQ : ↥P →* Qbar P Q := QuotientGroup.mk' (Q.subgroupOf P)

variable [IsMulCommutative (Qbar P Q)]

open scoped Classical in
noncomputable def valF (u : X) (x : X ⧸ P) : Qbar P Q :=
  if h : x.out⁻¹ * u * x.out ∈ P then phiQ P Q ⟨x.out⁻¹ * u * x.out, h⟩ else 1

theorem phiQ_conj (y h : ↥P) : phiQ P Q (h⁻¹ * y * h) = phiQ P Q y := by
  rw [map_mul, map_mul, map_inv]
  have := mul_comm (phiQ P Q y) (phiQ P Q h)
  calc (phiQ P Q h)⁻¹ * phiQ P Q y * phiQ P Q h
      = (phiQ P Q h)⁻¹ * (phiQ P Q h * phiQ P Q y) := by rw [← this]; group
    _ = phiQ P Q y := by group

open scoped Classical in
theorem valF_eq (u : X) (x : X ⧸ P) (t : X) (ht : (t : X ⧸ P) = x) :
    valF P Q u x = if h : t⁻¹ * u * t ∈ P then phiQ P Q ⟨t⁻¹ * u * t, h⟩ else 1 := by
  have hout : x.out⁻¹ * t ∈ P := QuotientGroup.eq.mp ((QuotientGroup.out_eq' x).trans ht.symm)
  obtain ⟨h, hh⟩ : ∃ h : P, (h : X) = x.out⁻¹ * t := ⟨⟨_, hout⟩, rfl⟩
  have e : t⁻¹ * u * t = (h : X)⁻¹ * (x.out⁻¹ * u * x.out) * h := by rw [hh]; group
  unfold valF
  by_cases hy : x.out⁻¹ * u * x.out ∈ P
  · have hy' : t⁻¹ * u * t ∈ P := by
      rw [e]; exact mul_mem (mul_mem (inv_mem h.2) hy) h.2
    simp only [hy, hy', ↓reduceDIte]
    have : (⟨t⁻¹ * u * t, hy'⟩ : P) = h⁻¹ * ⟨_, hy⟩ * h := Subtype.ext (by simpa using e)
    rw [this, phiQ_conj]
  · have hy' : ¬ t⁻¹ * u * t ∈ P := by
      intro hh'
      apply hy
      have e2 : x.out⁻¹ * u * x.out = (h : X) * (t⁻¹ * u * t) * (h : X)⁻¹ := by rw [e]; group
      rw [e2]
      exact mul_mem (mul_mem h.2 hh') (inv_mem h.2)
    simp only [hy, hy', ↓reduceDIte]

end Transfer


section Transfer2

open scoped IsMulCommutative

variable {X : Type*} [Group X] (P Q : Subgroup X) [(Q.subgroupOf P).Normal]
  [IsMulCommutative (Qbar P Q)]

omit [IsMulCommutative (Qbar P Q)] in
theorem smul_mk_eq_iff (g t : X) : g • (t : X ⧸ P) = (t : X ⧸ P) ↔ t⁻¹ * g * t ∈ P := by
  have : g • (t : X ⧸ P) = ((g * t : X) : X ⧸ P) := rfl
  rw [this, QuotientGroup.eq]
  constructor
  · intro h
    have := inv_mem h
    simpa [mul_assoc] using this
  · intro h
    have := inv_mem h
    simpa [mul_assoc] using this

open scoped Classical in
theorem valF_smul (u d : X) (hd : d * u = u * d) (x : X ⧸ P) :
    valF P Q u (d • x) = valF P Q u x := by
  have h1 : ((d * x.out : X) : X ⧸ P) = d • x := by
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rfl
  rw [valF_eq P Q u (d • x) (d * x.out) h1]
  have e : (d * x.out)⁻¹ * u * (d * x.out) = x.out⁻¹ * u * x.out := by
    have : d⁻¹ * u * d = u := by
      calc d⁻¹ * u * d = d⁻¹ * (u * d) := by group
        _ = d⁻¹ * (d * u) := by rw [hd]
        _ = u := by group
    calc (d * x.out)⁻¹ * u * (d * x.out) = x.out⁻¹ * (d⁻¹ * u * d) * x.out := by group
      _ = x.out⁻¹ * u * x.out := by rw [this]
  unfold valF
  by_cases hy : x.out⁻¹ * u * x.out ∈ P
  · have hy' : (d * x.out)⁻¹ * u * (d * x.out) ∈ P := by rw [e]; exact hy
    simp only [hy, hy', ↓reduceDIte]
    congr 1
    exact Subtype.ext e
  · have hy' : ¬ (d * x.out)⁻¹ * u * (d * x.out) ∈ P := by rw [e]; exact hy
    simp only [hy, hy', ↓reduceDIte]

open scoped Classical in
theorem valF_eq_one_of_not_fixed (u : X) (x : X ⧸ P) (hx : u • x ≠ x) : valF P Q u x = 1 := by
  unfold valF
  have : ¬ x.out⁻¹ * u * x.out ∈ P := by
    intro h
    apply hx
    have := (smul_mk_eq_iff P u x.out).mpr h
    rwa [QuotientGroup.out_eq'] at this
  simp only [this, ↓reduceDIte]

theorem phiQ_eq_one_iff (z : ↥P) : phiQ P Q z = 1 ↔ (z : X) ∈ Q := by
  unfold phiQ
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

open scoped Classical in
theorem valF_pow {p : ℕ} (u : X)
    (hb : ∀ (g : X) (k : ℕ), g⁻¹ * u ^ (p * k) * g ∈ P → g⁻¹ * u ^ (p * k) * g ∈ Q)
    (x : X ⧸ P) : valF P Q u x ^ p = 1 := by
  unfold valF
  by_cases hy : x.out⁻¹ * u * x.out ∈ P
  · simp only [hy, ↓reduceDIte]
    rw [← map_pow, phiQ_eq_one_iff]
    have e : (x.out⁻¹ * u * x.out) ^ p = x.out⁻¹ * u ^ (p * 1) * x.out := by
      have := conj_pow (a := x.out⁻¹) (b := u) (i := p)
      rw [mul_one]
      simpa using this
    show (x.out⁻¹ * u * x.out) ^ p ∈ Q
    rw [e]
    refine hb x.out 1 ?_
    rw [← e]
    exact pow_mem hy p
  · simp only [hy, ↓reduceDIte, one_pow]

end Transfer2


section Transfer3

open scoped IsMulCommutative

variable {X : Type*} [Group X] [Finite X] (P Q : Subgroup X) [(Q.subgroupOf P).Normal]
  [IsMulCommutative (Qbar P Q)]

omit [Finite X] [IsMulCommutative (Qbar P Q)] in
theorem mem_fixedPoints_zpowers_iff (u : X) (x : X ⧸ P) :
    x ∈ fixedPoints (Subgroup.zpowers u) (X ⧸ P) ↔ u • x = x := by
  rw [mem_fixedPoints]
  constructor
  · intro h
    exact h ⟨u, Subgroup.mem_zpowers u⟩
  · intro h g
    have hu : u ∈ MulAction.stabilizer X x := h
    have hle : Subgroup.zpowers u ≤ MulAction.stabilizer X x := Subgroup.zpowers_le.mpr hu
    exact hle g.2

open scoped Classical in
theorem transfer_eq_prod_valF [Fintype (X ⧸ P)] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p ↥P) {u : X} (huP : u ∈ P)
    (hb : ∀ (g : X) (k : ℕ), g⁻¹ * u ^ (p * k) * g ∈ P → g⁻¹ * u ^ (p * k) * g ∈ Q) :
    MonoidHom.transfer (phiQ P Q) u = ∏ x : X ⧸ P, valF P Q u x := by
  have hGp : IsPGroup p ↥(Subgroup.zpowers u) := hP.to_le (Subgroup.zpowers_le.mpr huP)
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  obtain ⟨n, hn⟩ : ∃ n, orderOf u = p ^ n := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hP ⟨u, huP⟩
    exact ⟨n, by simpa using hn⟩
  have hterm : ∀ q : orbitRel.Quotient (Subgroup.zpowers u) (X ⧸ P),
      phiQ P Q ⟨q.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) q.out * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem P u q.out⟩ = valF P Q u q.out := by
    intro q
    by_cases hr : Function.minimalPeriod (u • ·) q.out = 1
    · have hmem : q.out.out⁻¹ * u * q.out.out ∈ P := by
        simpa [hr] using QuotientGroup.out_conj_pow_minimalPeriod_mem P u q.out
      unfold valF
      simp only [hmem, ↓reduceDIte]
      congr 1
      exact Subtype.ext (by simp [hr])
    ·
      have hfix : ¬ u • q.out = q.out := by
        intro hfix
        apply hr
        exact Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hfix
      rw [valF_eq_one_of_not_fixed P Q u q.out hfix]
      rw [phiQ_eq_one_iff]
      have hdvd : Function.minimalPeriod (u • ·) q.out ∣ p ^ n := by
        rw [← hn]
        apply Function.IsPeriodicPt.minimalPeriod_dvd
        show (u • ·)^[orderOf u] q.out = q.out
        simp [smul_iterate, pow_orderOf_eq_one]
      obtain ⟨j, hj, hjr⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
      have hj0 : j ≠ 0 := by
        rintro rfl
        exact hr (by simpa using hjr)
      obtain ⟨k, hk⟩ : ∃ k, Function.minimalPeriod (u • ·) q.out = p * k := by
        refine ⟨p ^ (j - 1), ?_⟩
        rw [hjr, ← pow_succ']
        congr 1
        omega
      show q.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) q.out * q.out.out ∈ Q
      have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem P u q.out
      have e : u ^ Function.minimalPeriod (u • ·) q.out = u ^ (p * k) := by rw [hk]
      rw [e] at hmem ⊢
      exact hb q.out.out k hmem
  rw [Finset.prod_congr rfl fun q _ => hterm q]
  have hval1 : ∀ q : orbitRel.Quotient (Subgroup.zpowers u) (X ⧸ P),
      valF P Q u q.out =
        if q.out ∈ fixedPoints (Subgroup.zpowers u) (X ⧸ P) then valF P Q u q.out else 1 := by
    intro q
    by_cases hq : q.out ∈ fixedPoints (Subgroup.zpowers u) (X ⧸ P)
    · simp only [hq, ↓reduceIte]
    · simp only [hq, ↓reduceIte]
      exact valF_eq_one_of_not_fixed P Q u _
        (fun h => hq ((mem_fixedPoints_zpowers_iff P u _).mpr h))
  rw [Finset.prod_congr rfl fun q _ => hval1 q,
    prod_orbitReps_fixed (G := Subgroup.zpowers u) (valF P Q u)]
  refine (prod_eq_prod_fixedPoints hGp (valF P Q u) (fun g x => ?_) (valF_pow P Q u hb)).symm
  have hcomm : (g : X) * u = u * g := by
    obtain ⟨k, hk⟩ := g.2
    rw [← hk]
    exact ((Commute.refl u).zpow_left k).eq
  exact valF_smul P Q u g hcomm x

end Transfer3


section Sylow4

variable {X : Type*} [Group X]

theorem mem_smul_sylow {p : ℕ} (P : Sylow p X) (g y : X) :
    y ∈ ((g • P : Sylow p X) : Subgroup X) ↔ g⁻¹ * y * g ∈ (P : Subgroup X) := by
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem centralizer_conj_eq (u t : X) :
    Subgroup.centralizer ({t⁻¹ * u * t} : Set X) =
      (Subgroup.centralizer ({u} : Set X)).map (MulAut.conj t⁻¹).toMonoidHom := by
  ext z
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, Subgroup.mem_map,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro h
    refine ⟨t * z * t⁻¹, ?_, by group⟩
    have : t⁻¹ * u * t * z = z * (t⁻¹ * u * t) := h
    calc u * (t * z * t⁻¹) = t * ((t⁻¹ * u * t) * z) * t⁻¹ := by group
      _ = t * (z * (t⁻¹ * u * t)) * t⁻¹ := by rw [this]
      _ = t * z * t⁻¹ * u := by group
  · rintro ⟨c, hc, rfl⟩
    have : u * c = c * u := hc
    calc t⁻¹ * u * t * (t⁻¹ * c * t⁻¹⁻¹) = t⁻¹ * (u * c) * t := by group
      _ = t⁻¹ * (c * u) * t := by rw [this]
      _ = t⁻¹ * c * t⁻¹⁻¹ * (t⁻¹ * u * t) := by group

variable {p : ℕ} [Fact p.Prime]

theorem exists_sylow_centralizer [Finite X] {u : X} (hu : ∃ n, orderOf u = p ^ n) :
    ∃ D : Subgroup X, D ≤ Subgroup.centralizer ({u} : Set X) ∧ IsPGroup p ↥D ∧
      ¬ p ∣ D.relIndex (Subgroup.centralizer ({u} : Set X)) ∧ u ∈ D := by
  set C : Subgroup X := Subgroup.centralizer ({u} : Set X) with hC
  have huC : u ∈ C := Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh]
  have hzC : Subgroup.zpowers u ≤ C := Subgroup.zpowers_le.mpr huC
  have hz : IsPGroup p ↥(Subgroup.zpowers u) := by
    obtain ⟨n, hn⟩ := hu
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hn])
  have hU0 : IsPGroup p ↥((Subgroup.zpowers u).subgroupOf C) :=
    IsPGroup.of_equiv hz (Subgroup.subgroupOfEquivOfLe hzC).symm
  obtain ⟨S, hS⟩ := hU0.exists_le_sylow
  refine ⟨(S : Subgroup ↥C).map C.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact S.isPGroup'.map C.subtype
  · have hS' : ((S : Subgroup ↥C).map C.subtype).subgroupOf C = (S : Subgroup ↥C) := by
      ext z
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨w, hw, hwz⟩
        have : w = z := Subtype.ext hwz
        rwa [this] at hw
      · intro hz
        exact ⟨z, hz, rfl⟩
    have : ((S : Subgroup ↥C).map C.subtype).relIndex C = (S : Subgroup ↥C).index := by
      unfold Subgroup.relIndex
      rw [hS']
    rw [this]
    exact Sylow.not_dvd_index S
  · have : (⟨u, huC⟩ : ↥C) ∈ (Subgroup.zpowers u).subgroupOf C := Subgroup.mem_zpowers u
    exact ⟨⟨u, huC⟩, hS this, rfl⟩

end Sylow4


section Extremal5

variable {X : Type*} [Group X] {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem extremal_of_fixed [Finite X] {P : Subgroup X} (hP : IsPGroup p ↥P) {u : X} {D : Subgroup X}
    (hDC : D ≤ Subgroup.centralizer ({u} : Set X))
    (hDsyl : ¬ p ∣ D.relIndex (Subgroup.centralizer ({u} : Set X))) (huD : u ∈ D)
    {x : X ⧸ P} (hx : x ∈ fixedPoints D (X ⧸ P)) :
    x.out⁻¹ * u * x.out ∈ P ∧ IsExtremalIn p P (x.out⁻¹ * u * x.out) := by
  set t : X := x.out with ht
  have hDt : ∀ d ∈ D, t⁻¹ * d * t ∈ P := by
    intro d hd
    have h1 : d • x = x := mem_fixedPoints.mp hx ⟨d, hd⟩
    have h2 : d • (t : X ⧸ P) = (t : X ⧸ P) := by
      rw [ht, QuotientGroup.out_eq']; exact h1
    exact (smul_mk_eq_iff P d t).mp h2
  have huP : t⁻¹ * u * t ∈ P := hDt u huD
  refine ⟨huP, ?_, hP.to_le inf_le_left, ?_⟩
  · exact inf_le_right
  ·
    set f : X →* X := (MulAut.conj t⁻¹).toMonoidHom with hf
    have hfinj : Function.Injective f := (MulAut.conj t⁻¹).injective
    set y := t⁻¹ * u * t with hy
    have hCy : Subgroup.centralizer ({y} : Set X) =
        (Subgroup.centralizer ({u} : Set X)).map f := centralizer_conj_eq u t
    have hD'le : D.map f ≤ P ⊓ Subgroup.centralizer ({y} : Set X) := by
      rintro z ⟨d, hd, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa [hf, MulAut.conj_apply] using hDt d hd
      · rw [hCy]
        exact ⟨d, hDC hd, rfl⟩
    have hD'le2 : D.map f ≤ Subgroup.centralizer ({y} : Set X) := hD'le.trans inf_le_right
    have h1 := Subgroup.relIndex_mul_relIndex (D.map f) (P ⊓ Subgroup.centralizer ({y} : Set X))
      (Subgroup.centralizer ({y} : Set X)) hD'le inf_le_right
    have h2 : (D.map f).relIndex (Subgroup.centralizer ({y} : Set X)) =
        D.relIndex (Subgroup.centralizer ({u} : Set X)) := by
      rw [hCy]
      exact Subgroup.relIndex_map_map_of_injective D _ hfinj
    intro hdvd
    apply hDsyl
    rw [← h2, ← h1]
    exact Dvd.dvd.mul_left hdvd _

end Extremal5


section Final6

open scoped IsMulCommutative

variable {X : Type*} [Group X] {p : ℕ} [Fact p.Prime]

theorem exists_conj_into_sylow [Finite X] {N K S₀ : Subgroup X} (hKN : K ≤ N)
    (hKp : IsPGroup p ↥K) (hS₀N : S₀ ≤ N) (hS₀p : IsPGroup p ↥S₀)
    (hS₀idx : ¬ p ∣ S₀.relIndex N) : ∃ c ∈ N, ∀ k ∈ K, c⁻¹ * k * c ∈ S₀ := by
  have hS₀p' : IsPGroup p ↥(S₀.subgroupOf N) :=
    IsPGroup.of_equiv hS₀p (Subgroup.subgroupOfEquivOfLe hS₀N).symm
  let SP : Sylow p ↥N := hS₀p'.toSylow hS₀idx
  have hSP : (SP : Subgroup ↥N) = S₀.subgroupOf N := rfl
  have hKp' : IsPGroup p ↥(K.subgroupOf N) :=
    IsPGroup.of_equiv hKp (Subgroup.subgroupOfEquivOfLe hKN).symm
  obtain ⟨S1, hS1⟩ := hKp'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥N) SP S1
  refine ⟨(c : X), c.2, fun k hk => ?_⟩
  have hk' : (⟨k, hKN hk⟩ : ↥N) ∈ (S1 : Subgroup ↥N) := hS1 (by simpa [Subgroup.mem_subgroupOf] using hk)
  rw [← hc, mem_smul_sylow, hSP, Subgroup.mem_subgroupOf] at hk'
  simpa using hk'

theorem exists_iii [Finite X] {P : Subgroup X} (hP : IsPGroup p ↥P) {u g : X}
    (hg : IsExtremalIn p P (g⁻¹ * u * g)) :
    ∃ c ∈ Subgroup.centralizer ({g⁻¹ * u * g} : Set X),
      ∀ w ∈ P ⊓ Subgroup.centralizer ({u} : Set X),
        (g * c)⁻¹ * w * (g * c) ∈ P ⊓ Subgroup.centralizer ({g⁻¹ * u * g} : Set X) := by
  set f : X →* X := (MulAut.conj g⁻¹).toMonoidHom with hf
  have hCy := centralizer_conj_eq u g
  have hKN : (P ⊓ Subgroup.centralizer ({u} : Set X)).map f ≤
      Subgroup.centralizer ({g⁻¹ * u * g} : Set X) := by
    rintro z ⟨w, hw, rfl⟩
    rw [hCy]
    exact ⟨w, hw.2, rfl⟩
  have hKp : IsPGroup p ↥((P ⊓ Subgroup.centralizer ({u} : Set X)).map f) :=
    (hP.to_le inf_le_left).map f
  obtain ⟨hS₀N, hS₀p, hS₀idx⟩ := hg
  obtain ⟨c, hcN, hc⟩ := exists_conj_into_sylow hKN hKp hS₀N hS₀p hS₀idx
  refine ⟨c, hcN, fun w hw => ?_⟩
  have := hc (g⁻¹ * w * g) ⟨w, hw, by simp [hf]⟩
  have e : (g * c)⁻¹ * w * (g * c) = c⁻¹ * (g⁻¹ * w * g) * c := by group
  rw [e]
  exact this

end Final6


section Main7

open scoped IsMulCommutative

variable {X : Type*} [Group X] {p : ℕ} [Fact p.Prime]

theorem thompson_transfer_1515 [Finite X] {P Q : Subgroup X} {u : X}
    (hP : IsPGroup p ↥P) (hPidx : ¬ p ∣ P.index)
    (hQn : ∀ t ∈ P, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q)
    (hcyc : ∃ b ∈ P, ∀ t ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Q)
    (huP : u ∈ P) (huQ : u ∉ Q)
    (hb : ∀ (g : X) (k : ℕ), g⁻¹ * u ^ (p * k) * g ∈ P → g⁻¹ * u ^ (p * k) * g ∈ Q)
    (hc : ∀ g : X, g⁻¹ * u * g ∈ P → IsExtremalIn p P (g⁻¹ * u * g) →
      g⁻¹ * u * g ∈ Q ∨ u⁻¹ * (g⁻¹ * u * g) ∈ Q) :
    (∃ (N : Subgroup X) (_ : N.Normal), IsCyclic (X ⧸ N) ∧ IsPGroup p (X ⧸ N) ∧ u ∉ N) ∨
    ∃ g : X, g⁻¹ * u * g ∈ Q ∧ IsExtremalIn p P (g⁻¹ * u * g) ∧
      ∀ c ∈ P ⊓ Subgroup.centralizer ({u} : Set X),
        g⁻¹ * c * g ∈ P ⊓ Subgroup.centralizer ({g⁻¹ * u * g} : Set X) := by
  classical
  by_cases hex : ∃ g : X, g⁻¹ * u * g ∈ Q ∧ IsExtremalIn p P (g⁻¹ * u * g)
  · right
    obtain ⟨g, hgQ, hgext⟩ := hex
    obtain ⟨c, hcy, hcall⟩ := exists_iii hP hgext
    have e : (g * c)⁻¹ * u * (g * c) = g⁻¹ * u * g := by
      have hcy' : c * (g⁻¹ * u * g) = (g⁻¹ * u * g) * c :=
        (Subgroup.mem_centralizer_iff.mp hcy (g⁻¹ * u * g) rfl).symm
      calc (g * c)⁻¹ * u * (g * c) = c⁻¹ * (g⁻¹ * u * g) * c := by group
        _ = g⁻¹ * u * g := by rw [mul_assoc, ← hcy']; group
    refine ⟨g * c, ?_, ?_, ?_⟩
    · rw [e]; exact hgQ
    · rw [e]; exact hgext
    · intro w hw
      rw [e]
      exact hcall w hw
  · left
    have hn : (Q.subgroupOf P).Normal :=
      ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact hQn g g.2 n hn⟩
    have hcycA : IsCyclic (Qbar P Q) := by
      obtain ⟨b, hbP, hbt⟩ := hcyc
      refine ⟨phiQ P Q ⟨b, hbP⟩, fun a => ?_⟩
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨k, hk⟩ := hbt t t.2
      refine ⟨k, ?_⟩
      have hmem : (⟨b, hbP⟩ ^ k)⁻¹ * t ∈ Q.subgroupOf P := by
        rw [Subgroup.mem_subgroupOf]
        simpa using hk
      show (phiQ P Q ⟨b, hbP⟩) ^ k = phiQ P Q t
      rw [← map_zpow]
      have := (QuotientGroup.eq (s := Q.subgroupOf P)).mpr hmem
      exact this
    have hAp : IsPGroup p (Qbar P Q) := hP.to_quotient _
    have : IsMulCommutative (Qbar P Q) := inferInstance
    have := Fintype.ofFinite (X ⧸ P)
    obtain ⟨n, hn⟩ : ∃ n, orderOf u = p ^ n := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hP ⟨u, huP⟩
      exact ⟨n, by simpa using hn⟩
    obtain ⟨D, hDC, hDp, hDsyl, huD⟩ := exists_sylow_centralizer (p := p) ⟨n, hn⟩
    let τ : X →* Qbar P Q := MonoidHom.transfer (phiQ P Q)
    have hτ : τ u = ∏ x : X ⧸ P, valF P Q u x := transfer_eq_prod_valF P Q hP huP hb
    have hcomm : ∀ d : ↥D, (d : X) * u = u * d := fun d =>
      (Subgroup.mem_centralizer_iff.mp (hDC d.2) u (Set.mem_singleton u)).symm
    have h1 : ∏ x : X ⧸ P, valF P Q u x = ∏ x : fixedPoints D (X ⧸ P), valF P Q u x :=
      prod_eq_prod_fixedPoints hDp (valF P Q u)
        (fun d x => valF_smul P Q u d (hcomm d) x) (valF_pow P Q u hb)
    have hfixed : ∀ x : fixedPoints D (X ⧸ P), valF P Q u x = phiQ P Q ⟨u, huP⟩ := by
      intro x
      obtain ⟨hyP, hyext⟩ := extremal_of_fixed hP hDC hDsyl huD x.2
      have hxout : valF P Q u x.1 = phiQ P Q ⟨x.1.out⁻¹ * u * x.1.out, hyP⟩ := by
        unfold valF
        simp only [hyP, ↓reduceDIte]
      rw [hxout]
      rcases hc x.1.out hyP hyext with hyQ | hyQ
      · exact absurd ⟨x.1.out, hyQ, hyext⟩ hex
      · have : (⟨u, huP⟩ : ↥P)⁻¹ * ⟨x.1.out⁻¹ * u * x.1.out, hyP⟩ ∈ Q.subgroupOf P := by
          rw [Subgroup.mem_subgroupOf]
          simpa using hyQ
        have h2 := (QuotientGroup.eq (s := Q.subgroupOf P)).mpr this
        exact h2.symm
    have hcard : ¬ p ∣ Nat.card (fixedPoints D (X ⧸ P)) := by
      have hmod := hDp.card_modEq_card_fixedPoints (X ⧸ P)
      rw [← Nat.ModEq.dvd_iff hmod dvd_rfl, ← Subgroup.index_eq_card]
      exact hPidx
    have hphi_u : phiQ P Q ⟨u, huP⟩ ≠ 1 := by
      intro h
      exact huQ ((phiQ_eq_one_iff P Q _).mp h)
    have hτu : τ u ≠ 1 := by
      rw [hτ, h1, Finset.prod_congr rfl fun x _ => hfixed x, Finset.prod_const, Finset.card_univ,
        Fintype.card_eq_nat_card]
      intro h
      obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hAp (phiQ P Q ⟨u, huP⟩)
      have hdvd : p ^ m ∣ Nat.card (fixedPoints D (X ⧸ P)) := by
        rw [← hm]; exact orderOf_dvd_of_pow_eq_one h
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp at hm
        exact hphi_u hm
      exact hcard ((dvd_pow_self p hm0).trans hdvd)
    refine ⟨τ.ker, τ.normal_ker, ?_, ?_, fun h => hτu (MonoidHom.mem_ker.mp h)⟩
    · have hcycR : IsCyclic ↥τ.range := inferInstance
      exact isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange τ).symm.toMonoidHom
        (QuotientGroup.quotientKerEquivRange τ).symm.surjective
    · exact IsPGroup.of_equiv (hAp.to_subgroup τ.range) (QuotientGroup.quotientKerEquivRange τ).symm

end Main7

end CFSG.GH74.GLS.Bg.Thompson
