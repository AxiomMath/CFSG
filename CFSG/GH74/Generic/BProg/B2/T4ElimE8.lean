module

public import CFSG.GH74.Generic.BProg.B2.T4ElimE8Core
public import CFSG.GH74.Generic.BProg.B2.T4OutCore
public import CFSG.GH74.Generic.BProg.B2.FixFourS45
public import CFSG.GH74.Generic.BProg.B2.PumpupTable
public import CFSG.ClassicalInvolution.Orders.Basic

public section

namespace CFSG.GH74.Generic.BProg.B2.T4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace T4ElimE8

section Lift

theorem exists_lift_sylow_aux {G H : Type*} [Group G] [Finite G] [Group H] (ρ : G →* H)
    (hker : ¬ 2 ∣ Nat.card ρ.ker) (E : Subgroup H) (hE : E ≤ ρ.range) {k : ℕ}
    (hEcard : Nat.card E = 2 ^ k) :
    ∃ (M : Subgroup G) (S : Sylow 2 ↥M), (∀ x, x ∈ M ↔ ρ x ∈ E) ∧
      ((S : Subgroup ↥M).map M.subtype).map ρ = E ∧
      ∀ x ∈ (S : Subgroup ↥M).map M.subtype, ρ x = 1 → x = 1 := by
  classical
  have hp : Nat.Prime 2 := Nat.prime_two
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero k hp.ne_zero)
  set P' : Subgroup G := E.comap ρ with hP'
  let f : P' →* E := (ρ.comp P'.subtype).codRestrict E fun x => x.2
  have hfsurj : Function.Surjective f := fun e => by
    obtain ⟨g, hg⟩ := hE e.2
    exact ⟨⟨g, show ρ g ∈ E by rw [hg]; exact e.2⟩, Subtype.ext hg⟩
  have hfx : ∀ x : P', (f x : H) = ρ x := fun x => rfl
  have hkerf : Nat.card f.ker = Nat.card ρ.ker := by
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, ?_⟩, fun x => ⟨⟨x.1, ?_⟩, ?_⟩, ?_, ?_⟩
    · have := x.2
      rw [MonoidHom.mem_ker] at this ⊢
      have h2 := congrArg Subtype.val this
      rwa [hfx] at h2
    · show ρ x.1 ∈ E
      rw [MonoidHom.mem_ker.mp x.2]; exact E.one_mem
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hfx]
      exact MonoidHom.mem_ker.mp x.2
    · intro x; rfl
    · intro x; rfl
  have hPc : Nat.card P' = Nat.card ρ.ker * 2 ^ k := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv, hEcard,
      hkerf] at h1
    rw [h1, mul_comm]
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 P'))
  have hScard : Nat.card S = 2 ^ k := by
    rw [Sylow.card_eq_multiplicity, hPc, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero k hp.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, Nat.Prime.factorization_pow hp]
    simp
  have key : ∀ x ∈ S.map P'.subtype, ρ x = 1 → x = 1 := by
    intro x hx hρx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    have h1 : orderOf (x' : G) ∣ 2 ^ k := by
      rw [← hScard]
      have := Subgroup.orderOf_dvd_natCard (S : Subgroup P') hx'
      simpa [Subgroup.orderOf_coe] using this
    have h2 : orderOf (x' : G) ∣ Nat.card ρ.ker := by
      have hmem : (x' : G) ∈ ρ.ker := hρx
      have := Subgroup.orderOf_dvd_natCard ρ.ker hmem
      simpa [Subgroup.orderOf_coe] using this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ρ.ker) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hker)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
  have hSinj : ∀ x ∈ S.map P'.subtype, ∀ y ∈ S.map P'.subtype, ρ x = ρ y → x = y := by
    intro x hx y hy hxy
    have : x * y⁻¹ = 1 := key _ (Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy))
      (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  set E₀ : Subgroup G := S.map P'.subtype with hE₀
  have hE₀card : Nat.card E₀ = 2 ^ k := by
    rw [hE₀, Subgroup.card_map_of_injective P'.subtype_injective, hScard]
  have hmapE : E₀.map ρ = E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
      exact g'.2
    · have : Nat.card (E₀.map ρ) = Nat.card E₀ := by
        refine Nat.card_congr (Equiv.ofBijective
          (fun x : E₀ => ⟨ρ x, Subgroup.mem_map_of_mem _ x.2⟩) ⟨?_, ?_⟩).symm
        · intro x y hxy
          exact Subtype.ext (hSinj _ x.2 _ y.2 (congrArg Subtype.val hxy))
        · rintro ⟨_, g, hg, rfl⟩
          exact ⟨⟨g, hg⟩, rfl⟩
      rw [this, hE₀card, hEcard]
  exact ⟨P', S, fun x => Iff.rfl, hmapE, key⟩


theorem exists_lift_normalizer {L : Type} [Group L] [Finite L] (Z : Subgroup L) [Z.Normal]
    (hZ : ¬ 2 ∣ Nat.card Z) (P : Subgroup (L ⧸ Z)) (hP8 : Nat.card P = 2 ^ 3)
    (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {n : L ⧸ Z}
    (hn : n ∈ normalizer (P : Set (L ⧸ Z))) :
    ∃ (E₀ : Subgroup L) (g : L), E₀.map (QuotientGroup.mk' Z) = P ∧
      (∀ x ∈ E₀, QuotientGroup.mk' Z x = 1 → x = 1) ∧ g ∈ normalizer (E₀ : Set L) ∧
      ∀ x ∈ E₀, QuotientGroup.mk' Z (g * x * g⁻¹) = n * QuotientGroup.mk' Z x * n⁻¹ := by
  classical
  set π : L →* L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : ¬ 2 ∣ Nat.card π.ker := by rw [hπ, QuotientGroup.ker_mk']; exact hZ
  have hrange : P ≤ π.range := by
    rw [MonoidHom.range_eq_top_of_surjective π (QuotientGroup.mk'_surjective Z)]; exact le_top
  obtain ⟨M, S, hMmem, hmap0, key0⟩ := exists_lift_sylow_aux π hker P hrange hP8
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : Subgroup L, E₀ = (S : Subgroup ↥M).map M.subtype := ⟨_, rfl⟩
  have hmap : E₀.map π = P := by rw [hE₀]; exact hmap0
  have key : ∀ x ∈ E₀, π x = 1 → x = 1 := by rw [hE₀]; exact key0
  obtain ⟨g₁, hg₁⟩ := QuotientGroup.mk'_surjective Z n
  have hnorm : ∀ m ∈ M, g₁ * m * g₁⁻¹ ∈ M := by
    intro m hm
    have : π (g₁ * m * g₁⁻¹) = n * π m * n⁻¹ := by rw [map_mul, map_mul, map_inv, hg₁]
    rw [hMmem]
    rw [this]
    exact (Subgroup.mem_normalizer_iff.1 hn (π m)).1 ((hMmem m).1 hm)
  have hnorm' : ∀ m ∈ M, g₁⁻¹ * m * g₁ ∈ M := by
    intro m hm
    have : π (g₁⁻¹ * m * g₁) = n⁻¹ * π m * n⁻¹⁻¹ := by
      rw [map_mul, map_mul, map_inv, hg₁, inv_inv]
    rw [hMmem]
    rw [this]
    exact (Subgroup.mem_normalizer_iff.1 (inv_mem hn) (π m)).1 ((hMmem m).1 hm)
  let f : M →* M :=
    { toFun := fun m => ⟨g₁ * m * g₁⁻¹, hnorm m m.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp [mul_assoc] }
  have hfs : Function.Surjective f := by
    intro m
    refine ⟨⟨g₁⁻¹ * m * g₁, hnorm' m m.2⟩, ?_⟩
    apply Subtype.ext
    simp [f, mul_assoc]
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 ↥M := Sylow.mapSurjective hfs S
  have hS' : (S' : Subgroup ↥M) = (S : Subgroup ↥M).map f := Sylow.coe_mapSurjective hfs S
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (↥M) S S'
  have hmS : (S' : Subgroup ↥M) = (S : Subgroup ↥M).map (MulAut.conj m).toMonoidHom := by
    rw [← hm, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  set g : L := (m : L)⁻¹ * g₁ with hg
  have hconj : ∀ x ∈ E₀, g * x * g⁻¹ ∈ E₀ := by
    intro x hx
    rw [hE₀] at hx ⊢
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx
    have hfs_mem : f s ∈ (S' : Subgroup ↥M) := by
      rw [hS']; exact Subgroup.mem_map_of_mem _ hs
    rw [hmS] at hfs_mem
    obtain ⟨s', hs', hs'e⟩ := Subgroup.mem_map.1 hfs_mem
    have h1 : (m : L) * (s' : L) * (m : L)⁻¹ = g₁ * (s : L) * g₁⁻¹ := by
      have := congrArg (fun x : ↥M => (x : L)) hs'e
      simpa [MulAut.conj_apply, f] using this
    refine ⟨s', hs', ?_⟩
    show (s' : L) = g * (s : L) * g⁻¹
    rw [hg]
    calc (s' : L) = (m : L)⁻¹ * ((m : L) * s' * (m : L)⁻¹) * m := by group
      _ = (m : L)⁻¹ * (g₁ * s * g₁⁻¹) * m := by rw [h1]
      _ = ((m : L)⁻¹ * g₁) * s * ((m : L)⁻¹ * g₁)⁻¹ := by group
  have hcardE : Nat.card E₀ = Nat.card (E₀.map (MulAut.conj g).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
  have hmapE : E₀.map (MulAut.conj g).toMonoidHom = E₀ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ hcardE.le
    rintro _ ⟨x, hx, rfl⟩
    exact hconj x hx
  have hgnorm : g ∈ normalizer (E₀ : Set L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact hconj h hh
    · intro hh
      rw [← hmapE] at hh
      obtain ⟨y, hy, hyh⟩ := Subgroup.mem_map.1 hh
      have : y = h := by
        have h1 : g * y * g⁻¹ = g * h * g⁻¹ := hyh
        exact mul_left_cancel (mul_right_cancel h1)
      rw [← this]; exact hy
  have hE₀P : ∀ x ∈ E₀, π x ∈ P := fun x hx => by
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ hx
  refine ⟨E₀, g, hmap, key, hgnorm, ?_⟩
  intro x hx
  have hmM : π (m : L) ∈ P := (hMmem _).1 m.2
  have hy : n * π x * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 hn (π x)).1 (hE₀P x hx)
  have hπg : π g = (π (m : L))⁻¹ * n := by rw [hg, map_mul, map_inv, hg₁]
  calc π (g * x * g⁻¹) = (π (m : L))⁻¹ * (n * π x * n⁻¹) * π (m : L) := by
        rw [map_mul, map_mul, map_inv, hπg]; group
    _ = n * π x * n⁻¹ := by
        have hc := hPab _ hy _ hmM
        calc (π (m : L))⁻¹ * (n * π x * n⁻¹) * π (m : L)
            = (π (m : L))⁻¹ * ((n * π x * n⁻¹) * π (m : L)) := by group
          _ = (π (m : L))⁻¹ * (π (m : L) * (n * π x * n⁻¹)) := by rw [hc]
          _ = n * π x * n⁻¹ := by group


theorem lift_E8_seven {L : Type} [Group L] [Finite L] {Z : Subgroup L} [Z.Normal]
    (hZ : ¬ 2 ∣ Nat.card Z) (P : Subgroup (L ⧸ Z)) (hP8 : Nat.card P = 8)
    (hPel : ∀ x ∈ P, x * x = 1) (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {n : L ⧸ Z}
    (hn : n ∈ normalizer (P : Set (L ⧸ Z)))
    (h7 : orderOf (P.normalizerMonoidHom ⟨n, hn⟩) = 7) :
    ∃ (E₀ : Subgroup L) (g : L) (hg : g ∈ normalizer (E₀ : Set L)),
      Nat.card E₀ = 8 ∧ (∀ r : E₀, r * r = 1) ∧ (∀ r s : E₀, r * s = s * r) ∧
      orderOf (E₀.normalizerMonoidHom ⟨g, hg⟩) = 7 := by
  classical
  obtain ⟨E₀, g, hmap, key, hgnorm, hπg⟩ :=
    exists_lift_normalizer Z hZ P (by rw [hP8]; norm_num) hPab hn
  set π : L →* L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hEP : ∀ x ∈ E₀, π x ∈ P := fun x hx => by
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ hx
  let φ : E₀ →* P := (π.comp E₀.subtype).codRestrict P fun x => hEP x x.2
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h1 : π (x : L) = π (y : L) := congrArg Subtype.val hxy
    have : (x : L) * (y : L)⁻¹ = 1 := key _ (E₀.mul_mem x.2 (E₀.inv_mem y.2))
      (by rw [map_mul, map_inv, h1, mul_inv_cancel])
    exact Subtype.ext (mul_inv_eq_one.mp this)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨p, hp⟩
    rw [← hmap] at hp
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : E₀ ≃* P := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hcard : Nat.card E₀ = 8 := by rw [Nat.card_congr e.toEquiv, hP8]
  refine ⟨E₀, g, hgnorm, hcard, ?_, ?_, ?_⟩
  · intro r
    apply Subtype.ext
    have h1 : π ((r : L) * r) = 1 := by rw [map_mul]; exact hPel _ (hEP r r.2)
    exact key _ (E₀.mul_mem r.2 r.2) h1
  · intro r s
    have h1 : π ((r : L) * s * ((s : L) * r)⁻¹) = 1 := by
      have hc := hPab _ (hEP r r.2) _ (hEP s s.2)
      rw [map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel]
    exact Subtype.ext (mul_inv_eq_one.1 (key _ (E₀.mul_mem (E₀.mul_mem r.2 s.2)
      (E₀.inv_mem (E₀.mul_mem s.2 r.2))) h1))
  ·
    let a : MulAut P := P.normalizerMonoidHom ⟨n, hn⟩
    let σ : MulAut E₀ := E₀.normalizerMonoidHom ⟨g, hgnorm⟩
    have hσφ : ∀ x : E₀, φ (σ x) = a (φ x) := by
      intro x
      apply Subtype.ext
      show π ((σ x : E₀) : L) = ((a (φ x) : P) : L ⧸ Z)
      have h1 : ((σ x : E₀) : L) = g * (x : L) * g⁻¹ := by simp [σ]
      have h2 : ((a (φ x) : P) : L ⧸ Z) = n * ((φ x : P) : L ⧸ Z) * n⁻¹ := by simp [a]
      have h3 : ((φ x : P) : L ⧸ Z) = π (x : L) := rfl
      rw [h1, h2, h3]
      exact hπg x x.2
    have hcongr : MulAut.congr e σ = a := by
      ext p
      obtain ⟨x, rfl⟩ := e.surjective p
      have : MulAut.congr e σ (e x) = e (σ x) := by
        simp [MulAut.congr_apply]
      rw [this]
      exact congrArg Subtype.val (hσφ x)
    have : orderOf σ = orderOf a := by
      rw [← hcongr, MulEquiv.orderOf_eq]
    rw [this]
    exact h7


end Lift

section Models

theorem no_E8_seven_of_scalarQuot {X : Type} [Group X] {n : ℕ} [NeZero n] {K : Type} [Field K]
    [Finite K] (h2 : (2 : K) ≠ 0) (hn : n ≤ 6) {S₀ : Type} [Group S₀] (ι : S₀ →* GL (Fin n) K)
    (p : S₀ →* X) (hp : Function.Surjective p) (hker : ∀ z, p z = 1 → ∃ c : Kˣ, ι z = sc c)
    (hsc : ∀ s, (∃ c : Kˣ, ι s = sc c) → p s = 1) {R : Type} [Group R] [Finite R]
    (hR8 : Nat.card R = 8) (hR2 : ∀ r : R, r * r = 1) (hRc : ∀ r s : R, r * s = s * r)
    (ρ : R →* X) (hρ : Function.Injective ρ) (σ : MulAut R) (hσ : orderOf σ = 7) (g : X)
    (hg : ∀ r : R, g * ρ r * g⁻¹ = ρ (σ r)) : False := by
  classical
  choose lift hlift using fun r => hp (ρ r)
  obtain ⟨Ĝ, hĜ⟩ := hp g
  let A : R → GL (Fin n) K := fun r => ι (lift r)
  let G : GL (Fin n) K := ι Ĝ
  have hdata : ProjData σ A G := by
    refine ⟨?_, ?_, ?_⟩
    · intro r s
      have h1 : p (lift (r * s) * (lift r * lift s)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, hlift, hlift, hlift, map_mul, mul_inv_cancel]
      obtain ⟨c, hc⟩ := hker _ h1
      refine ⟨c, ?_⟩
      have : A (r * s) * (A r * A s)⁻¹ = sc c := by
        simpa [A, map_mul, map_inv] using hc
      calc A (r * s) = (A (r * s) * (A r * A s)⁻¹) * (A r * A s) := by group
        _ = sc c * (A r * A s) := by rw [this]
    · rintro r ⟨c, hc⟩
      have : p (lift r) = 1 := hsc _ ⟨c, hc⟩
      rw [hlift] at this
      exact hρ (this.trans (map_one ρ).symm)
    · intro r
      have h1 : p (Ĝ * lift r * Ĝ⁻¹ * (lift (σ r))⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, map_mul, map_inv, hĜ, hlift, hlift, hg, mul_inv_cancel]
      obtain ⟨c, hc⟩ := hker _ h1
      refine ⟨c, ?_⟩
      have : G * A r * G⁻¹ * (A (σ r))⁻¹ = sc c := by simpa [A, G] using hc
      calc G * A r * G⁻¹ = (G * A r * G⁻¹ * (A (σ r))⁻¹) * A (σ r) := by group
        _ = sc c * A (σ r) := by rw [this]
  exact no_E8_seven_core ⟨hdata, h2, hR2, hRc⟩ hR8 hσ hn


open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag in
theorem no_E8_seven_psl {J : Type} [Group J] {n p f : ℕ} (hn3 : 3 ≤ n) (hn6 : n ≤ 6) (hp : p.Prime)
    (hp2 : p ≠ 2) (hL : LieModel J .PSL n p f) {R : Type} [Group R] [Finite R]
    (hR8 : Nat.card R = 8) (hR2 : ∀ r : R, r * r = 1) (hRc : ∀ r s : R, r * s = s * r)
    (ρ : R →* J) (hρ : Function.Injective ρ) (σ : MulAut R) (hσ : orderOf σ = 7) (g : J)
    (hg : ∀ r : R, g * ρ r * g⁻¹ = ρ (σ r)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := T4OutCore.linear_model hL
  have : NeZero n := ⟨by omega⟩
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
  refine no_E8_seven_of_scalarQuot h2 hn6 (S₀ := Matrix.SpecialLinearGroup (Fin n) F)
    Matrix.SpecialLinearGroup.toGL (LinearFlag.proj n F) (LinearFlag.proj_surjective n F) ?_ ?_ hR8 hR2
    hRc ((e : J →* LinearFlag.projectiveSL n F).comp ρ) (e.injective.comp hρ) σ hσ (e g) ?_
  · intro z hz
    have hz' : z ∈ LinearFlag.scalars n F := by
      rw [← LinearFlag.ker_proj]; exact hz
    obtain ⟨c, -, hc⟩ := hz'
    refine ⟨c, Units.ext ?_⟩
    simpa using hc
  · rintro s ⟨c, hc⟩
    rw [← MonoidHom.mem_ker, LinearFlag.ker_proj]
    refine ⟨c, ?_, ?_⟩
    · have h1 := congrArg (fun M : GL (Fin n) F => Matrix.GeneralLinearGroup.det M) hc
      simp at h1
      exact h1.symm
    · have := congrArg (fun M : GL (Fin n) F => (M : Matrix (Fin n) (Fin n) F)) hc
      simpa using this
  · intro r
    simp only [MonoidHom.comp_apply, MonoidHom.coe_ofClass]
    rw [← map_mul, ← map_inv, ← map_mul, hg]

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag in
theorem no_E8_seven_psu {J : Type} [Group J] {n p f : ℕ} (hn3 : 3 ≤ n) (hn6 : n ≤ 6) (hp2 : p ≠ 2)
    (hq : ¬ (n = 3 ∧ p ^ f = 2)) (hL : LieModel J .PSU n p f) {R : Type} [Group R] [Finite R]
    (hR8 : Nat.card R = 8) (hR2 : ∀ r : R, r * r = 1) (hRc : ∀ r s : R, r * s = s * r)
    (ρ : R →* J) (hρ : Function.Injective ρ) (σ : MulAut R) (hσ : orderOf σ = 7) (g : J)
    (hg : ∀ r : R, g * ρ r * g⁻¹ = ρ (σ r)) : False := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := T4OutCore.primeForm_model hn3 hq hL
  have : NeZero n := ⟨by omega⟩
  have := h.finite
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := T4OutCore.two_ne_zero_of_charP h.prime hp2
  refine no_E8_seven_of_scalarQuot h2 hn6
    (S₀ := ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).subtype
    (QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n))
    (QuotientGroup.mk'_surjective _) ?_ ?_ hR8 hR2 hRc
    ((e : J →* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).comp ρ)
    (e.injective.comp hρ) σ hσ (e g) ?_
  · intro z hz
    have hz' : z ∈ normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n :=
      (QuotientGroup.eq_one_iff z).1 hz
    obtain ⟨c, -, -, hc⟩ := hz'
    exact ⟨c, hc⟩
  · rintro s ⟨c, hc⟩
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    have hs := s.2
    rw [mem_gramSU] at hs
    have hcm : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) (c : K) := by
      have := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
      simpa using this
    refine ⟨c, ?_, ?_, hc⟩
    · have h1 := hs.1
      rw [hcm] at h1
      have h0 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
      simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply] at h0
      unfold UnitaryFieldData.norm
      rw [mul_comm]
      exact h0
    · have h1 := hs.2
      rw [hcm] at h1
      exact Units.ext (by simpa using h1)
  · intro r
    simp only [MonoidHom.comp_apply, MonoidHom.coe_ofClass]
    rw [← map_mul, ← map_inv, ← map_mul, hg]

section Certified


theorem exists_E8_seven_of_shape45 {L : Type} [Group L] [Finite L] {Z : Subgroup L} [Z.Normal]
    (hZ : Odd (Nat.card Z)) (h45 : QShape4 (L ⧸ Z) ∨ QShape5 (L ⧸ Z)) :
    ∃ (E₀ : Subgroup L) (g : L) (hg : g ∈ normalizer (E₀ : Set L)),
      Nat.card E₀ = 8 ∧ (∀ r : E₀, r * r = 1) ∧ (∀ r s : E₀, r * s = s * r) ∧
      orderOf (E₀.normalizerMonoidHom ⟨g, hg⟩) = 7 := by
  classical
  have hZ2 : ¬ 2 ∣ Nat.card Z := fun h => (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr h)
  have hdata : FixFourS45.HasE8Sylow (L ⧸ Z) ∧ FixFourS45.InvolConj (L ⧸ Z) := by
    rcases h45 with h | h
    · exact FixFourS45.shape4_data h
    · exact FixFourS45.shape5_data h
  obtain ⟨⟨P, hPel, hP8⟩, hconj⟩ := hdata
  obtain ⟨a, haP, ha7⟩ := FixFourS45.exists_order_seven P hPel hP8 hconj
  obtain ⟨⟨ñ, hñ⟩, hña⟩ := haP
  have hsq : ∀ x ∈ (P : Subgroup (L ⧸ Z)), x * x = 1 := by
    intro x hx
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 ↥(P : Subgroup (L ⧸ Z))) ⟨x, hx⟩
    simpa [pow_two] using congrArg Subtype.val this
  have hab : ∀ x ∈ (P : Subgroup (L ⧸ Z)), ∀ y ∈ (P : Subgroup (L ⧸ Z)), x * y = y * x := by
    intro x hx y hy
    have := (IsMulCommutative.is_comm (M := ↥(P : Subgroup (L ⧸ Z)))).comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  exact lift_E8_seven hZ2 (P : Subgroup (L ⧸ Z)) hP8 hsq hab hñ (by rw [hña]; exact ha7)

theorem false_of_shape45_psl {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) {n p f : ℕ} (hn3 : 3 ≤ n) (hn6 : n ≤ 6)
    (hp : p.Prime) (hp2 : p ≠ 2) (hL : LieModel ↥H .PSL n p f)
    (h45 : ∃ Z : Subgroup ↥L, Z ≤ center ↥L ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal,
      (QShape4 (↥L ⧸ Z) ∨ QShape5 (↥L ⧸ Z))) : False := by
  obtain ⟨Z, -, hZo, hZn, h45⟩ := h45
  have hLH : L ≤ H := hs.comp.1.trans inf_le_left
  obtain ⟨E₀, g, hg, hE8, hE2, hEc, hord⟩ := exists_E8_seven_of_shape45 hZo h45
  refine no_E8_seven_psl hn3 hn6 hp hp2 hL (R := ↥E₀) hE8 hE2 hEc
    ((Subgroup.inclusion hLH).comp E₀.subtype)
    ((Subgroup.inclusion_injective hLH).comp E₀.subtype_injective)
    (E₀.normalizerMonoidHom ⟨g, hg⟩) hord (Subgroup.inclusion hLH g) ?_
  intro r
  have h1 : E₀.subtype (E₀.normalizerMonoidHom ⟨g, hg⟩ r) = g * E₀.subtype r * g⁻¹ := by simp
  simp only [MonoidHom.comp_apply]
  rw [h1, map_mul, map_mul, map_inv]

theorem false_of_shape45_psu {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) {n p f : ℕ} (hn3 : 3 ≤ n) (hn6 : n ≤ 6)
    (hp2 : p ≠ 2) (hq : ¬ (n = 3 ∧ p ^ f = 2)) (hL : LieModel ↥H .PSU n p f)
    (h45 : ∃ Z : Subgroup ↥L, Z ≤ center ↥L ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal,
      (QShape4 (↥L ⧸ Z) ∨ QShape5 (↥L ⧸ Z))) : False := by
  obtain ⟨Z, -, hZo, hZn, h45⟩ := h45
  have hLH : L ≤ H := hs.comp.1.trans inf_le_left
  obtain ⟨E₀, g, hg, hE8, hE2, hEc, hord⟩ := exists_E8_seven_of_shape45 hZo h45
  refine no_E8_seven_psu hn3 hn6 hp2 hq hL (R := ↥E₀) hE8 hE2 hEc
    ((Subgroup.inclusion hLH).comp E₀.subtype)
    ((Subgroup.inclusion_injective hLH).comp E₀.subtype_injective)
    (E₀.normalizerMonoidHom ⟨g, hg⟩) hord (Subgroup.inclusion hLH g) ?_
  intro r
  have h1 : E₀.subtype (E₀.normalizerMonoidHom ⟨g, hg⟩ r) = g * E₀.subtype r * g⁻¹ := by simp
  simp only [MonoidHom.comp_apply]
  rw [h1, map_mul, map_mul, map_inv]

theorem false_of_shape45_puL5 {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) (hL : PuL5 ↥H)
    (h45 : ∃ Z : Subgroup ↥L, Z ≤ center ↥L ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal,
      (QShape4 (↥L ⧸ Z) ∨ QShape5 (↥L ⧸ Z))) : False := by
  obtain ⟨p, f, hp, hp2, hf, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hL
  · exact false_of_shape45_psl hs (n := 5) (by norm_num) (by norm_num) hp hp2 hm h45
  · exact false_of_shape45_psu hs (n := 5) (by norm_num) (by norm_num) hp2
      (fun hh => absurd hh.1 (by norm_num)) hm h45

theorem false_of_shape45_puL4 {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) (hL : PuL4 ↥H)
    (h45 : ∃ Z : Subgroup ↥L, Z ≤ center ↥L ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal,
      (QShape4 (↥L ⧸ Z) ∨ QShape5 (↥L ⧸ Z))) : False := by
  obtain ⟨p, f, hp, hp2, hf, h3, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hL
  · exact false_of_shape45_psl hs (n := 4) (by norm_num) (by norm_num) hp hp2 hm h45
  · exact false_of_shape45_psu hs (n := 4) (by norm_num) (by norm_num) hp2
      (fun hh => absurd hh.1 (by norm_num)) hm h45

end Certified

end Models


end T4ElimE8

end CFSG.GH74.Generic.BProg.B2.T4
