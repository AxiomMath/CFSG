module

public import CFSG.GroupTheory.InnerOfFixSylowTwo
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GroupTheory

open Subgroup
open CFSG.Open

open scoped IsMulCommutative commutatorElement

theorem exists_eq_of_endomorphisms_of_card_pow_le
    {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    (x y : A →ₗ[ZMod 2] A)
    (hx2 : ∀ z, x (x z) = 0) (hy2 : ∀ z, y (y z) = 0)
    (hxy : ∀ z, x (y z) = y (x z))
    (hfix : Nat.card ↥(LinearMap.ker x ⊓ LinearMap.ker y) ^ 4 ≤ Nat.card A)
    {a b : A} (ha : x a = 0) (hb : y b = 0) (hab : x b = y a) :
    ∃ n, x n = a ∧ y n = b := by
  classical
  have hcardC : Nat.card ↥(LinearMap.ker x ⊓ LinearMap.ker y) =
      2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := ↥(LinearMap.ker x ⊓ LinearMap.ker y)), Nat.card_zmod]
  have hcardA : Nat.card A = 2 ^ Module.finrank (ZMod 2) A := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A), Nat.card_zmod]
  have h4d : 4 * Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) ≤
      Module.finrank (ZMod 2) A := by
    rw [hcardC, hcardA, ← pow_mul] at hfix
    refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp ?_
    simpa [mul_comm] using hfix
  have hyK_range : LinearMap.range (y.domRestrict (LinearMap.ker x)) ≤
      LinearMap.ker x ⊓ LinearMap.ker y := by
    rintro _ ⟨z, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · change x (y (z : A)) = 0
      rw [hxy (z : A), LinearMap.mem_ker.mp z.2, map_zero]
    · exact LinearMap.mem_ker.mpr (hy2 (z : A))
  have hker_yK : Module.finrank (ZMod 2) ↥(LinearMap.ker (y.domRestrict (LinearMap.ker x))) =
      Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) := by
    rw [LinearMap.ker_domRestrict]
    exact (Submodule.finrank_map_subtype_eq (LinearMap.ker x)
      ((LinearMap.ker y).comap (LinearMap.ker x).subtype)).symm.trans
        (by rw [Submodule.map_comap_subtype])
  have hK_le : Module.finrank (ZMod 2) ↥(LinearMap.ker x) ≤
      2 * Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (y.domRestrict (LinearMap.ker x))
    have hle := Submodule.finrank_mono hyK_range
    rw [hker_yK] at hrn
    omega
  have hrange_x_le_ker : LinearMap.range x ≤ LinearMap.ker x :=
    LinearMap.range_le_ker_iff.mpr (LinearMap.ext hx2)
  have hrange_x_le : Module.finrank (ZMod 2) ↥(LinearMap.range x) ≤
      Module.finrank (ZMod 2) ↥(LinearMap.ker x) := Submodule.finrank_mono hrange_x_le_ker
  have hn_le : Module.finrank (ZMod 2) A ≤
      4 * Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker x
    omega
  have hn_eq : Module.finrank (ZMod 2) A =
      4 * Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) :=
    le_antisymm hn_le h4d
  have hK_eq : Module.finrank (ZMod 2) ↥(LinearMap.ker x) =
      2 * Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker x
    omega
  have hrange_x_eq : Module.finrank (ZMod 2) ↥(LinearMap.range x) =
      Module.finrank (ZMod 2) ↥(LinearMap.ker x) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker x
    omega
  have hrange_x : LinearMap.range x = LinearMap.ker x :=
    Submodule.eq_of_le_of_finrank_eq hrange_x_le_ker hrange_x_eq
  have hrange_yK_eq : Module.finrank (ZMod 2)
      ↥(LinearMap.range (y.domRestrict (LinearMap.ker x))) =
      Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (y.domRestrict (LinearMap.ker x))
    rw [hker_yK] at hrn
    omega
  have hrange_yK : LinearMap.range (y.domRestrict (LinearMap.ker x)) =
      LinearMap.ker x ⊓ LinearMap.ker y :=
    Submodule.eq_of_le_of_finrank_eq hyK_range hrange_yK_eq
  have ha_mem : a ∈ LinearMap.range x := by
    rw [hrange_x]
    exact LinearMap.mem_ker.mpr ha
  obtain ⟨r, hr⟩ := ha_mem
  have hb'_mem : b - y r ∈ LinearMap.ker x ⊓ LinearMap.ker y := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hxy, hr, hab, sub_self]
    · rw [LinearMap.mem_ker, map_sub, hy2, hb, sub_self]
  rw [← hrange_yK] at hb'_mem
  obtain ⟨u, hu⟩ := hb'_mem
  have hu' : y (u : A) = b - y r := hu
  refine ⟨r + (u : A), ?_, ?_⟩
  · rw [map_add, hr, LinearMap.mem_ker.mp u.2, add_zero]
  · rw [map_add, hu']
    abel

private lemma quotient_isKleinFour {G : Type*} [Group G] {Q T : Subgroup G} [Finite T]
    (hQn : (Q.subgroupOf T).Normal) (hidx : Q.relIndex T = 4)
    (hsq : ∀ t ∈ T, t ^ 2 ∈ Q) : IsKleinFour (T ⧸ Q.subgroupOf T) := by
  let Q' := Q.subgroupOf T
  haveI : Q'.Normal := hQn
  let V := T ⧸ Q'
  haveI : Finite V :=
    Finite.of_surjective (QuotientGroup.mk' Q') (QuotientGroup.mk'_surjective (N := Q'))
  letI : Fintype V := Fintype.ofFinite V
  have hcardV : Nat.card V = 4 := by
    rw [← hidx]
    rfl
  have hVexp_dvd : Monoid.exponent V ∣ 2 := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
    intro x
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (N := Q') x
    change (QuotientGroup.mk' Q' t) ^ 2 = 1
    rw [← map_pow (QuotientGroup.mk' Q') t 2]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (hsq t t.2))
  have hVexp : Monoid.exponent V = 2 := by
    have hne : Monoid.exponent V ≠ 1 := by
      intro h
      have hsub : Subsingleton V := Monoid.exp_eq_one_iff.mp h
      have hle : Nat.card V ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
      omega
    exact (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : Nat.Prime 2) _ hVexp_dvd).resolve_left hne
  exact ⟨hcardV, hVexp⟩

private lemma exists_reps {G : Type*} [Group G] {Q T : Subgroup G} [Finite T]
    (hQn : (Q.subgroupOf T).Normal) [hK : IsKleinFour (T ⧸ Q.subgroupOf T)] :
    ∃ a b : T,
      QuotientGroup.mk' (Q.subgroupOf T) a ≠ 1 ∧
      QuotientGroup.mk' (Q.subgroupOf T) b ≠ 1 ∧
      QuotientGroup.mk' (Q.subgroupOf T) a ≠ QuotientGroup.mk' (Q.subgroupOf T) b ∧
      a * b * a⁻¹ * b⁻¹ ∈ Q.subgroupOf T := by
  classical
  let Q' := Q.subgroupOf T
  let V := T ⧸ Q'
  haveI : Q'.Normal := hQn
  haveI : Finite V :=
    Finite.of_surjective (QuotientGroup.mk' Q') (QuotientGroup.mk'_surjective (N := Q'))
  letI : Fintype V := Fintype.ofFinite V
  haveI : IsMulCommutative V := IsKleinFour.isMulCommutative
  have hcardV : Nat.card V = 4 := hK.card_four
  have hVcard_gt1 : 1 < Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, hcardV]
    norm_num
  obtain ⟨aV, haV_ne⟩ := Fintype.exists_ne_of_one_lt_card hVcard_gt1 (1 : V)
  obtain ⟨a, ha_mk⟩ := QuotientGroup.mk'_surjective (N := Q') aV
  have ha_ne : QuotientGroup.mk' Q' a ≠ 1 := by rw [ha_mk]; exact haV_ne
  have hsubtype_card : Fintype.card {x : V // x ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl (fun x : V => x = 1)]
    simp [hcardV]
  have hsubtype_gt1 : 1 < Fintype.card {x : V // x ≠ 1} := by
    rw [hsubtype_card]; norm_num
  obtain ⟨bSub, hbSub_ne⟩ := Fintype.exists_ne_of_one_lt_card hsubtype_gt1
    (⟨aV, haV_ne⟩ : {x : V // x ≠ 1})
  let bV : V := bSub.1
  have hbV_ne : bV ≠ 1 := bSub.2
  have hbV_ne_a : bV ≠ aV := by
    intro h
    exact hbSub_ne (Subtype.ext h)
  obtain ⟨b, hb_mk⟩ := QuotientGroup.mk'_surjective (N := Q') bV
  have hb_ne : QuotientGroup.mk' Q' b ≠ 1 := by rw [hb_mk]; exact hbV_ne
  have ha_ne_b : QuotientGroup.mk' Q' a ≠ QuotientGroup.mk' Q' b := by
    rw [ha_mk, hb_mk]
    exact hbV_ne_a.symm
  refine ⟨a, b, ha_ne, hb_ne, ha_ne_b, ?_⟩
  rw [← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' Q' (a * b * a⁻¹ * b⁻¹) = 1
  simp only [map_mul, map_inv]
  rw [mul_comm (QuotientGroup.mk' Q' a) (QuotientGroup.mk' Q' b)]
  group

private lemma coset_decomp {G : Type*} [Group G] {Q T : Subgroup G} [Finite T]
    (hQn : (Q.subgroupOf T).Normal) [hK : IsKleinFour (T ⧸ Q.subgroupOf T)]
    {a b : T} (ha : QuotientGroup.mk' (Q.subgroupOf T) a ≠ 1)
    (hb : QuotientGroup.mk' (Q.subgroupOf T) b ≠ 1)
    (hab : QuotientGroup.mk' (Q.subgroupOf T) a ≠ QuotientGroup.mk' (Q.subgroupOf T) b) :
    ∀ t : T, ∃ q : Q.subgroupOf T, ∃ w : T,
      (w = 1 ∨ w = a ∨ w = b ∨ w = a * b) ∧ t = q * w := by
  classical
  let Q' := Q.subgroupOf T
  let V := T ⧸ Q'
  haveI : Q'.Normal := hQn
  haveI : Finite V :=
    Finite.of_surjective (QuotientGroup.mk' Q') (QuotientGroup.mk'_surjective (N := Q'))
  letI : Fintype V := Fintype.ofFinite V
  have hV_univ : ({QuotientGroup.mk' Q' a * QuotientGroup.mk' Q' b,
      QuotientGroup.mk' Q' a, QuotientGroup.mk' Q' b, (1 : V)} : Finset V) = Finset.univ :=
    IsKleinFour.eq_finset_univ ha hb hab
  intro t
  have ht : QuotientGroup.mk' Q' t ∈
      ({QuotientGroup.mk' Q' a * QuotientGroup.mk' Q' b,
        QuotientGroup.mk' Q' a, QuotientGroup.mk' Q' b, (1 : V)} : Finset V) := by
    rw [hV_univ]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with ht | ht | ht | ht
  · refine ⟨⟨t * (a * b)⁻¹, ?_⟩, a * b, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
    · rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' Q' (t * (a * b)⁻¹) = 1
      rw [map_mul, map_inv, map_mul, ht]
      group
    · group
  · refine ⟨⟨t * a⁻¹, ?_⟩, a, Or.inr (Or.inl rfl), ?_⟩
    · rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' Q' (t * a⁻¹) = 1
      rw [map_mul, map_inv, ht]
      group
    · group
  · refine ⟨⟨t * b⁻¹, ?_⟩, b, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
    · rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' Q' (t * b⁻¹) = 1
      rw [map_mul, map_inv, ht]
      group
    · group
  · refine ⟨⟨t, ?_⟩, 1, Or.inl rfl, ?_⟩
    · rw [← QuotientGroup.eq_one_iff]
      exact ht
    · simp

private lemma conjNormal_trivial_on_abelian {G : Type*} [Group G] {Q T : Subgroup G}
    [hQn : (Q.subgroupOf T).Normal] [hcomm : IsMulCommutative (Q.subgroupOf T)] :
    ∀ q : Q.subgroupOf T, (MulAut.conjNormal (G := T) (H := Q.subgroupOf T)) q = 1 := by
  intro q
  ext p
  rw [MulAut.conjNormal_apply]
  change (((q : T) : G) * ((p : T) : G) * (((q : T) : G))⁻¹ : G) = ((p : T) : G)
  have hcomm' : ((q : T) : G) * ((p : T) : G) = ((p : T) : G) * ((q : T) : G) :=
    congrArg (fun z : Q.subgroupOf T => ((z : T) : G)) (mul_comm q p)
  rw [hcomm', mul_assoc, mul_inv_cancel, mul_one]

private lemma conjNormal_sq_eq_one {G : Type*} [Group G] {Q T : Subgroup G}
    [hQn : (Q.subgroupOf T).Normal] [hcomm : IsMulCommutative (Q.subgroupOf T)]
    {a : T} (ha : a * a ∈ Q.subgroupOf T) :
    (MulAut.conjNormal (G := T) (H := Q.subgroupOf T)) (a * a) = 1 := by
  simpa using conjNormal_trivial_on_abelian (Q := Q) (T := T) ⟨a * a, ha⟩

private lemma conjOne_sq {Q T : Type*} [CommGroup Q] [Group T]
    (ρ : T →* MulAut Q) (a : T) (hsq : ∀ q : Q, q * q = 1)
    (hρa : ρ (a * a) = 1) :
    ∀ q : Q, (q * ρ a q) * ρ a (q * ρ a q) = 1 := by
  intro q
  have h1 : ρ a (ρ a q) = q := by
    rw [← MulAut.mul_apply, ← map_mul, hρa, MulAut.one_apply]
  calc (q * ρ a q) * ρ a (q * ρ a q)
      = q * ρ a q * (ρ a q * ρ a (ρ a q)) := by rw [map_mul]
    _ = q * (ρ a q * ρ a q) * ρ a (ρ a q) := by ac_rfl
    _ = q * 1 * q := by rw [hsq (ρ a q), h1]
    _ = 1 := by rw [mul_one, hsq q]

private lemma conjNormal_comm {G : Type*} [Group G] {Q T : Subgroup G}
    [hQn : (Q.subgroupOf T).Normal] [hcomm : IsMulCommutative (Q.subgroupOf T)]
    {a b : T} (hcomm_mem : a * b * a⁻¹ * b⁻¹ ∈ Q.subgroupOf T) :
    (MulAut.conjNormal (G := T) (H := Q.subgroupOf T)) (a * b) =
      (MulAut.conjNormal (G := T) (H := Q.subgroupOf T)) (b * a) := by
  have h1 : a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
  rw [h1, map_mul, conjNormal_trivial_on_abelian (Q := Q) (T := T) ⟨_, hcomm_mem⟩, one_mul]

private lemma conjOne_commute {Q T : Type*} [CommGroup Q] [Group T]
    (ρ : T →* MulAut Q) (a b : T)
    (hρab : ρ (a * b) = ρ (b * a)) :
    ∀ q : Q, (q * ρ b q) * ρ a (q * ρ b q) = (q * ρ a q) * ρ b (q * ρ a q) := by
  intro q
  calc (q * ρ b q) * ρ a (q * ρ b q)
      = q * ρ b q * (ρ a q * ρ a (ρ b q)) := by rw [map_mul]
    _ = q * ρ b q * (ρ a q * ρ (a * b) q) := by
        rw [← MulAut.mul_apply, ← map_mul]
    _ = q * ρ a q * (ρ b q * ρ (a * b) q) := by ac_rfl
    _ = q * ρ a q * (ρ b q * ρ (b * a) q) := by rw [hρab]
    _ = q * ρ a q * (ρ b q * (ρ b * ρ a) q) := by rw [← map_mul]
    _ = q * ρ a q * (ρ b q * ρ b (ρ a q)) := by rw [MulAut.mul_apply]
    _ = (q * ρ a q) * (ρ b q * ρ b (ρ a q)) := by ac_rfl
    _ = (q * ρ a q) * ρ b (q * ρ a q) := by rw [map_mul]

theorem mul_commute_of_coboundary {G : Type*} [Group G] {Q L : Subgroup G} {c : G}
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hcQ : ∀ q ∈ Q, c * q = q * c)
    {y : G} (hyQ : y ∈ Q)
    (hcL : ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ Q)
    (hδ : ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ = l * y * l⁻¹ * y⁻¹) :
    ∀ l ∈ L, c * y * l = l * (c * y) := by
  intro l hl
  have hδl := hδ l hl
  have hlyQ : l * y * l⁻¹ ∈ Q := by
    have h := hcL l hl
    rw [hδl] at h
    have := Q.mul_mem h hyQ
    simpa [mul_assoc] using this
  have hcomm : l * y * l⁻¹ * y⁻¹ = y⁻¹ * l * y * l⁻¹ := by
    have h1 : (⟨l * y * l⁻¹, hlyQ⟩ : Q) * ⟨y⁻¹, Q.inv_mem hyQ⟩ =
        ⟨y⁻¹, Q.inv_mem hyQ⟩ * ⟨l * y * l⁻¹, hlyQ⟩ := by
      apply Subtype.ext
      exact hQab (l * y * l⁻¹) hlyQ y⁻¹ (Q.inv_mem hyQ)
    simpa [mul_assoc] using congrArg (fun z : Q => (z : G)) h1
  have h1 : c * l * c⁻¹ = y⁻¹ * l * y := by
    have h := hδl
    rw [hcomm] at h
    calc c * l * c⁻¹ = (c * l * c⁻¹ * l⁻¹) * l := by group
      _ = (y⁻¹ * l * y * l⁻¹) * l := by rw [h]
      _ = y⁻¹ * l * y := by group
  have hyc : y * c = c * y := (hcQ y hyQ).symm
  calc c * y * l = y * c * l := by rw [hyc]
    _ = y * (c * l) := by group
    _ = y * (y⁻¹ * l * y * c) := by
        have h := congrArg (fun z => z * c) h1
        have h' : c * l = y⁻¹ * l * y * c := by simpa [mul_assoc] using h
        rw [h']
    _ = l * y * c := by group
    _ = l * (c * y) := by
        calc l * y * c = l * (y * c) := by rw [mul_assoc]
          _ = l * (c * y) := by rw [hyc]

private lemma fixed_comm {G : Type*} [Group G] {Q T : Subgroup G} {a : T}
    (hQn : (Q.subgroupOf T).Normal) [hcomm : IsMulCommutative (Q.subgroupOf T)]
    (hQ'sq : ∀ q : Q.subgroupOf T, q * q = 1)
    (ρ : T →* MulAut (Q.subgroupOf T)) (hρ : ρ = MulAut.conjNormal)
    (xm : Q.subgroupOf T →* Q.subgroupOf T)
    (hxm : ∀ q, xm q = q * ρ a q)
    {q : Q.subgroupOf T} (h : xm q = 1) :
    ((q : T) : G) * ((a : T) : G) = ((a : T) : G) * ((q : T) : G) := by
  have h1 : ρ a q = q⁻¹ := by
    rw [hxm q] at h
    exact eq_inv_of_mul_eq_one_right h
  rw [hρ] at h1
  have h2 : (a : T) * (q : T) * (a : T)⁻¹ = (q : T) := by
    have h3 := congrArg (fun z : Q.subgroupOf T => (z : T)) h1
    rw [MulAut.conjNormal_apply] at h3
    have hqinv : ((q⁻¹ : Q.subgroupOf T) : T) = (q : T) :=
      congrArg (fun z : Q.subgroupOf T => (z : T))
        (inv_eq_of_mul_eq_one_right (hQ'sq q))
    rw [h3, hqinv]
  have h3 : ((a : T) : G) * ((q : T) : G) = ((q : T) : G) * ((a : T) : G) := by
    have h4 : (a : T) * (q : T) = (q : T) * (a : T) := by
      calc (a : T) * (q : T) = (a * q * a⁻¹) * a := by group
        _ = (q : T) * (a : T) := by rw [h2]
    exact congrArg (fun z : T => (z : G)) h4
  exact h3.symm

private lemma fixed_centralizes_T {G : Type*} [Group G] {Q T : Subgroup G}
    (hQ : IsElemAbelian 2 Q)
    {a b : T}
    (hdecomp : ∀ t : T, ∃ q : Q.subgroupOf T, ∃ w : T,
      (w = 1 ∨ w = a ∨ w = b ∨ w = a * b) ∧ t = q * w)
    (xm ym : Q.subgroupOf T →* Q.subgroupOf T)
    (hx_fixed_comm : ∀ q : Q.subgroupOf T, xm q = 1 →
      ((q : T) : G) * ((a : T) : G) = ((a : T) : G) * ((q : T) : G))
    (hy_fixed_comm : ∀ q : Q.subgroupOf T, ym q = 1 →
      ((q : T) : G) * ((b : T) : G) = ((b : T) : G) * ((q : T) : G))
    {q : Q.subgroupOf T} (hxq : xm q = 1) (hyq : ym q = 1) :
    ∀ t ∈ T, t * ((q : T) : G) = ((q : T) : G) * t := by
  intro t ht
  have hqa : ((q : T) : G) * ((a : T) : G) = ((a : T) : G) * ((q : T) : G) :=
    hx_fixed_comm q hxq
  have hqb : ((q : T) : G) * ((b : T) : G) = ((b : T) : G) * ((q : T) : G) :=
    hy_fixed_comm q hyq
  have hqab : ((q : T) : G) * (((a * b : T) : G)) =
      (((a * b : T) : G)) * ((q : T) : G) := by
    change ((q : T) : G) * (((a : T) : G) * ((b : T) : G)) =
      (((a : T) : G) * ((b : T) : G)) * ((q : T) : G)
    calc ((q : T) : G) * (((a : T) : G) * ((b : T) : G))
        = (((q : T) : G) * ((a : T) : G)) * ((b : T) : G) := by rw [mul_assoc]
      _ = (((a : T) : G) * ((q : T) : G)) * ((b : T) : G) := by rw [hqa]
      _ = ((a : T) : G) * (((q : T) : G) * ((b : T) : G)) := by rw [mul_assoc]
      _ = ((a : T) : G) * (((b : T) : G) * ((q : T) : G)) := by rw [hqb]
      _ = (((a : T) : G) * ((b : T) : G)) * ((q : T) : G) := by rw [mul_assoc]
  let tT : T := ⟨t, ht⟩
  obtain ⟨qt, w, hw, ht_eq⟩ := hdecomp tT
  have hq_qt : ((q : T) : G) * ((qt : T) : G) = ((qt : T) : G) * ((q : T) : G) :=
    congrArg (fun z : Q => (z : G))
      (hQ.1.is_comm.comm ⟨(q : T), q.2⟩ ⟨(qt : T), qt.2⟩)
  have hq_w : ((q : T) : G) * (w : G) = (w : G) * ((q : T) : G) := by
    rcases hw with rfl | rfl | rfl | rfl
    · simp
    · exact hqa
    · exact hqb
    · exact hqab
  change (tT : G) * ((q : T) : G) = ((q : T) : G) * (tT : G)
  rw [ht_eq]
  calc (((qt : T) : G) * (w : G)) * ((q : T) : G)
      = ((qt : T) : G) * ((w : G) * ((q : T) : G)) := by rw [mul_assoc]
    _ = ((qt : T) : G) * (((q : T) : G) * (w : G)) := by rw [hq_w]
    _ = (((qt : T) : G) * ((q : T) : G)) * (w : G) := by rw [mul_assoc]
    _ = (((q : T) : G) * ((qt : T) : G)) * (w : G) := by rw [hq_qt]
    _ = ((q : T) : G) * (((qt : T) : G) * (w : G)) := by rw [mul_assoc]

private lemma fixed_points_card_le {G : Type*} [Group G] {Q T : Subgroup G}
    (hQ : IsElemAbelian 2 Q) [Finite Q] [hcomm : IsMulCommutative (Q.subgroupOf T)]
    [hmod : Module (ZMod 2) (Additive (Q.subgroupOf T))]
    {a b : T}
    (hdecomp : ∀ t : T, ∃ q : Q.subgroupOf T, ∃ w : T,
      (w = 1 ∨ w = a ∨ w = b ∨ w = a * b) ∧ t = q * w)
    (xm ym : Q.subgroupOf T →* Q.subgroupOf T)
    (x y : Additive (Q.subgroupOf T) →ₗ[ZMod 2] Additive (Q.subgroupOf T))
    (hx_apply : ∀ q : Q.subgroupOf T, x (Additive.ofMul q) = Additive.ofMul (xm q))
    (hy_apply : ∀ q : Q.subgroupOf T, y (Additive.ofMul q) = Additive.ofMul (ym q))
    (hx_fixed_comm : ∀ q : Q.subgroupOf T, xm q = 1 →
      ((q : T) : G) * ((a : T) : G) = ((a : T) : G) * ((q : T) : G))
    (hy_fixed_comm : ∀ q : Q.subgroupOf T, ym q = 1 →
      ((q : T) : G) * ((b : T) : G) = ((b : T) : G) * ((q : T) : G)) :
    Nat.card ↥(LinearMap.ker x ⊓ LinearMap.ker y) ≤
      Nat.card ↥(Q ⊓ Subgroup.centralizer (T : Set G)) := by
  let Q' := Q.subgroupOf T
  let f : ↥(LinearMap.ker x ⊓ LinearMap.ker y) →
      ↥(Q ⊓ Subgroup.centralizer (T : Set G)) :=
    fun z => ⟨(((Additive.toMul (z : Additive Q') : Q') : T) : G), by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Additive.toMul (z : Additive Q') : Q').2
      · rw [Subgroup.mem_centralizer_iff]
        intro t ht
        let q : Q' := Additive.toMul (z : Additive Q')
        have hx0 : x (z : Additive Q') = 0 :=
          LinearMap.mem_ker.mp (Submodule.mem_inf.mp z.2).1
        have hy0 : y (z : Additive Q') = 0 :=
          LinearMap.mem_ker.mp (Submodule.mem_inf.mp z.2).2
        have hq_x : xm q = 1 := by
          have h := hx0
          rw [show (z : Additive Q') = Additive.ofMul q from
            (ofMul_toMul (z : Additive Q')).symm, hx_apply] at h
          exact ofMul_eq_zero.mp h
        have hq_y : ym q = 1 := by
          have h := hy0
          rw [show (z : Additive Q') = Additive.ofMul q from
            (ofMul_toMul (z : Additive Q')).symm, hy_apply] at h
          exact ofMul_eq_zero.mp h
        exact fixed_centralizes_T hQ hdecomp xm ym hx_fixed_comm hy_fixed_comm
          hq_x hq_y t ht
    ⟩
  haveI : Finite ↥(Q ⊓ Subgroup.centralizer (T : Set G)) :=
    Finite.of_injective (fun x => (⟨x.1, x.2.1⟩ : Q)) (fun x y h => by
      apply Subtype.ext
      exact congrArg (fun z : Q => (z : G)) h)
  have hinj : Function.Injective f := by
    intro z1 z2 h
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : ↥(Q ⊓ Subgroup.centralizer (T : Set G)) => (w : G)) h
  exact Nat.card_le_card_of_injective f hinj

private lemma cocycle_values {G : Type*} [Group G] {Q T : Subgroup G}
    [hcomm : IsMulCommutative (Q.subgroupOf T)]
    {a b : T} (hsq : ∀ t ∈ T, t ^ 2 ∈ Q)
    (hcomm_mem : a * b * a⁻¹ * b⁻¹ ∈ Q.subgroupOf T)
    (ρ : T →* MulAut (Q.subgroupOf T))
    (δ : T → Q.subgroupOf T)
    (hδ_cocycle : ∀ s t, δ (s * t) = δ s * ρ s (δ t))
    (hδ_Q : ∀ q : Q.subgroupOf T, δ q = 1)
    (hδ_const_left : ∀ (q : Q.subgroupOf T) (t : T), δ (q * t) = δ t)
    (xm ym : Q.subgroupOf T →* Q.subgroupOf T)
    (hxm : ∀ q, xm q = q * ρ a q) (hym : ∀ q, ym q = q * ρ b q)
    (hQ'sq : ∀ q : Q.subgroupOf T, q * q = 1) :
    xm (δ a) = 1 ∧ ym (δ b) = 1 ∧ xm (δ b) = ym (δ a) := by
  have hx_ma : xm (δ a) = 1 := by
    have h1 := hδ_cocycle a a
    have haa : (a * a : T) ∈ Q.subgroupOf T :=
      Subgroup.mem_subgroupOf.mpr (by
        change ((a * a : T) : G) ∈ Q
        simpa [pow_two] using hsq a a.2)
    have h2 : δ (a * a) = 1 := hδ_Q ⟨a * a, haa⟩
    rw [h2] at h1
    simpa [hxm] using h1.symm
  have hy_mb : ym (δ b) = 1 := by
    have h1 := hδ_cocycle b b
    have hbb : (b * b : T) ∈ Q.subgroupOf T :=
      Subgroup.mem_subgroupOf.mpr (by
        change ((b * b : T) : G) ∈ Q
        simpa [pow_two] using hsq b b.2)
    have h2 : δ (b * b) = 1 := hδ_Q ⟨b * b, hbb⟩
    rw [h2] at h1
    simpa [hym] using h1.symm
  have hxm_mb : xm (δ b) = ym (δ a) := by
    have h1 : δ a * ρ a (δ b) = δ b * ρ b (δ a) := by
      have h2 : δ (a * b) = δ (b * a) := by
        have hcommab : a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        rw [hcommab]
        exact hδ_const_left ⟨_, hcomm_mem⟩ (b * a)
      rw [hδ_cocycle a b, hδ_cocycle b a] at h2
      simpa using h2
    have h2 : (δ a * δ b) * (δ b * ρ a (δ b)) =
        (δ a * δ b) * (δ a * ρ b (δ a)) := by
      calc (δ a * δ b) * (δ b * ρ a (δ b))
          = δ a * (δ b * δ b) * ρ a (δ b) := by ac_rfl
        _ = δ a * ρ a (δ b) := by rw [hQ'sq (δ b), mul_one]
        _ = δ b * ρ b (δ a) := h1
        _ = δ b * (δ a * δ a) * ρ b (δ a) := by rw [hQ'sq (δ a), mul_one]
        _ = (δ a * δ b) * (δ a * ρ b (δ a)) := by ac_rfl
    have h3 := mul_left_cancel h2
    simpa [hxm, hym] using h3
  exact ⟨hx_ma, hy_mb, hxm_mb⟩

private lemma coboundary_on_T {G : Type*} [Group G] {Q T : Subgroup G}
    [hcomm : IsMulCommutative (Q.subgroupOf T)]
    {a b : T}
    (hdecomp : ∀ t : T, ∃ q : Q.subgroupOf T, ∃ w : T,
      (w = 1 ∨ w = a ∨ w = b ∨ w = a * b) ∧ t = q * w)
    (ρ : T →* MulAut (Q.subgroupOf T)) (hρQ : ∀ q : Q.subgroupOf T, ρ q = 1)
    (δ : T → Q.subgroupOf T)
    (hδ_cocycle : ∀ s t, δ (s * t) = δ s * ρ s (δ t))
    (hδ_Q : ∀ q : Q.subgroupOf T, δ q = 1)
    (hδ_const_left : ∀ (q : Q.subgroupOf T) (t : T), δ (q * t) = δ t)
    (xm ym : Q.subgroupOf T →* Q.subgroupOf T)
    (hxm : ∀ q, xm q = q * ρ a q) (hym : ∀ q, ym q = q * ρ b q)
    {ma mb : Q.subgroupOf T} (hma : ma = δ a) (hmb : mb = δ b)
    (hQ'sq : ∀ q : Q.subgroupOf T, q * q = 1)
    (n' : Q.subgroupOf T) (hxm_n : xm n' = ma) (hym_n : ym n' = mb) :
    ∀ t : T, δ t = ρ t n' * n'⁻¹ := by
  have hρa_n : ρ a n' = n' * ma := by
    have h : n' * ρ a n' = ma := by rw [← hxm n', hxm_n]
    calc ρ a n' = 1 * ρ a n' := (one_mul _).symm
      _ = (n' * n') * ρ a n' := by rw [hQ'sq n']
      _ = n' * (n' * ρ a n') := by rw [mul_assoc]
      _ = n' * ma := by rw [h]
  have hρb_n : ρ b n' = n' * mb := by
    have h : n' * ρ b n' = mb := by rw [← hym n', hym_n]
    calc ρ b n' = 1 * ρ b n' := (one_mul _).symm
      _ = (n' * n') * ρ b n' := by rw [hQ'sq n']
      _ = n' * (n' * ρ b n') := by rw [mul_assoc]
      _ = n' * mb := by rw [h]
  have hδ_a_eq : ρ a n' * n'⁻¹ = ma := by
    rw [hρa_n]
    calc n' * ma * n'⁻¹ = ma * n' * n'⁻¹ := by rw [mul_comm n' ma]
      _ = ma * (n' * n'⁻¹) := by rw [mul_assoc]
      _ = ma := by rw [mul_inv_cancel, mul_one]
  have hδ_b_eq : ρ b n' * n'⁻¹ = mb := by
    rw [hρb_n]
    calc n' * mb * n'⁻¹ = mb * n' * n'⁻¹ := by rw [mul_comm n' mb]
      _ = mb * (n' * n'⁻¹) := by rw [mul_assoc]
      _ = mb := by rw [mul_inv_cancel, mul_one]
  have hδ_ab_eq : ρ (a * b) n' * n'⁻¹ = ma * ρ a mb := by
    have h1 : ρ (a * b) n' = ρ a (ρ b n') := by
      rw [← MulAut.mul_apply, ← map_mul]
    calc ρ (a * b) n' * n'⁻¹
        = ((n' * ma) * ρ a mb) * n'⁻¹ := by rw [h1, hρb_n, map_mul, hρa_n]
      _ = (ma * ρ a mb) * (n' * n'⁻¹) := by ac_rfl
      _ = ma * ρ a mb := by rw [mul_inv_cancel, mul_one]
  intro t
  obtain ⟨q, w, hw, ht_eq⟩ := hdecomp t
  rw [ht_eq, hδ_const_left]
  have hρt : ρ (q * w) n' = ρ w n' := by
    rw [map_mul, hρQ q, MulAut.mul_apply, MulAut.one_apply]
  rw [hρt]
  rcases hw with hw | hw | hw | hw
  · rw [hw]
    have hδ1 : δ (1 : T) = 1 := by simpa using hδ_Q (1 : Q.subgroupOf T)
    rw [hδ1, map_one, MulAut.one_apply, mul_inv_cancel]
  · rw [hw, ← hma, hδ_a_eq]
  · rw [hw, ← hmb, hδ_b_eq]
  · rw [hw, show δ (a * b) = ma * ρ a mb by
        rw [hδ_cocycle a b, ← hma, ← hmb], hδ_ab_eq]

theorem exists_mul_commute_of_kleinFour_of_card_pow_le {G : Type*} [Group G]
    {Q T : Subgroup G} [Finite ↥Q] (hQT : Q ≤ T) (hQn : (Q.subgroupOf T).Normal)
    (hQ : IsElemAbelian 2 Q) (hidx : Q.relIndex T = 4) (hsq : ∀ t ∈ T, t ^ 2 ∈ Q)
    (hfix : Nat.card ↥(Q ⊓ Subgroup.centralizer (T : Set G)) ^ 4 ≤ Nat.card ↥Q)
    {c : G} (hcQ : ∀ q ∈ Q, c * q = q * c) (hcT : ∀ t ∈ T, c * t * c⁻¹ * t⁻¹ ∈ Q) :
    ∃ n ∈ Q, ∀ t ∈ T, c * n * t = t * (c * n) := by
  classical
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hcardT : Nat.card T = 4 * Nat.card Q := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := T)
    rw [inf_eq_left.mpr hQT, hidx] at h
    omega
  have hTfin : Finite T := Nat.finite_of_card_ne_zero (by rw [hcardT]; positivity)
  haveI : Finite T := hTfin
  let Q' : Subgroup T := Q.subgroupOf T
  haveI : Q'.Normal := hQn
  have hQ'comm : IsMulCommutative Q' := by
    refine IsMulCommutative.of_comm ?_
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    change ((x : T) : G) * ((y : T) : G) = ((y : T) : G) * ((x : T) : G)
    exact congrArg (fun z : Q => (z : G))
      (hQ.1.is_comm.comm ⟨((x : T) : G), x.2⟩ ⟨((y : T) : G), y.2⟩)
  haveI : IsMulCommutative Q' := hQ'comm
  have hQ'sq : ∀ q : Q', q * q = 1 := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    change ((q : T) : G) * ((q : T) : G) = 1
    have h := hQ.2 ((q : T) : G) q.2
    simpa [pow_two] using h
  haveI : IsKleinFour (T ⧸ Q') := quotient_isKleinFour hQn hidx hsq
  obtain ⟨a, b, ha_ne, hb_ne, ha_ne_b, hcomm_mem⟩ := exists_reps hQn
  have hdecomp : ∀ t : T, ∃ q : Q', ∃ w : T,
      (w = 1 ∨ w = a ∨ w = b ∨ w = a * b) ∧ t = q * w :=
    coset_decomp hQn ha_ne hb_ne ha_ne_b
  let ρ : T →* MulAut Q' := MulAut.conjNormal
  have hρQ : ∀ q : Q', ρ q = 1 := conjNormal_trivial_on_abelian
  let δ : T → Q' := fun t =>
    ⟨⟨c * (t : G) * c⁻¹ * (t : G)⁻¹, hQT (hcT t t.2)⟩,
      Subgroup.mem_subgroupOf.mpr (hcT t t.2)⟩
  let xm : Q' →* Q' :=
    { toFun := fun q => q * ρ a q
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [map_mul]
        ac_rfl }
  let ym : Q' →* Q' :=
    { toFun := fun q => q * ρ b q
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [map_mul]
        ac_rfl }
  have hx2_mul : ∀ q : Q', xm (xm q) = 1 := by
    intro q
    have haa : a * a ∈ Q' :=
      Subgroup.mem_subgroupOf.mpr (by simpa [pow_two] using hsq a a.2)
    exact conjOne_sq ρ a hQ'sq (conjNormal_sq_eq_one haa) q
  have hy2_mul : ∀ q : Q', ym (ym q) = 1 := by
    intro q
    have hbb : b * b ∈ Q' :=
      Subgroup.mem_subgroupOf.mpr (by simpa [pow_two] using hsq b b.2)
    exact conjOne_sq ρ b hQ'sq (conjNormal_sq_eq_one hbb) q
  have hρ_comm : ρ (a * b) = ρ (b * a) := conjNormal_comm hcomm_mem
  have hxy_mul : ∀ q : Q', xm (ym q) = ym (xm q) := conjOne_commute ρ a b hρ_comm

  let A := Additive Q'
  haveI : Finite A := inferInstance
  haveI : Module (ZMod 2) A := AddCommGroup.zmodModule (n := 2) (by
    intro z
    rw [two_smul]
    rw [← ofMul_toMul z]
    change Additive.ofMul (Additive.toMul z) + Additive.ofMul (Additive.toMul z) = 0
    rw [← ofMul_mul, hQ'sq, ofMul_one])
  let x : A →ₗ[ZMod 2] A := (xm.toAdditive).toZModLinearMap 2
  let y : A →ₗ[ZMod 2] A := (ym.toAdditive).toZModLinearMap 2
  have hx_apply : ∀ q : Q', x (Additive.ofMul q) = Additive.ofMul (xm q) := fun q => rfl
  have hy_apply : ∀ q : Q', y (Additive.ofMul q) = Additive.ofMul (ym q) := fun q => rfl
  have hx2 : ∀ z : A, x (x z) = 0 := by
    intro z
    rw [← ofMul_toMul z]
    rw [hx_apply, hx_apply, hx2_mul, ofMul_one]
  have hy2 : ∀ z : A, y (y z) = 0 := by
    intro z
    rw [← ofMul_toMul z]
    rw [hy_apply, hy_apply, hy2_mul, ofMul_one]
  have hxy : ∀ z : A, x (y z) = y (x z) := by
    intro z
    rw [← ofMul_toMul z]
    rw [hy_apply, hx_apply, hx_apply, hy_apply, hxy_mul]
  have hcardA : Nat.card A = Nat.card Q := by
    change Nat.card Q' = Nat.card Q
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQT).toEquiv
  have hδ_cocycle : ∀ s t : T, δ (s * t) = δ s * ρ s (δ t) := by
    intro s t
    apply Subtype.ext
    apply Subtype.ext
    simp only [δ, ρ, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hδ_Q : ∀ q : Q', δ q = 1 := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    simp only [δ, Subgroup.coe_one]
    rw [hcQ ((q : T) : G) q.2]
    group
  have hδ_const_left : ∀ (q : Q') (t : T), δ (q * t) = δ t := by
    intro q t
    rw [hδ_cocycle, hδ_Q, hρQ q, MulAut.one_apply, one_mul]
  let ma : Q' := δ a
  let mb : Q' := δ b
  obtain ⟨hx_ma, hy_mb, hxm_mb⟩ :=
    cocycle_values hsq hcomm_mem ρ δ
      hδ_cocycle hδ_Q hδ_const_left xm ym (fun q => rfl) (fun q => rfl) hQ'sq
  have ha_add : x (Additive.ofMul ma) = 0 := by
    rw [hx_apply, hx_ma, ofMul_one]
  have hb_add : y (Additive.ofMul mb) = 0 := by
    rw [hy_apply, hy_mb, ofMul_one]
  have hab_add : x (Additive.ofMul mb) = y (Additive.ofMul ma) := by
    rw [hx_apply, hy_apply, hxm_mb]
  have hx_fixed_comm : ∀ q : Q', xm q = 1 →
      ((q : T) : G) * ((a : T) : G) = ((a : T) : G) * ((q : T) : G) :=
    fun q hq => fixed_comm hQn hQ'sq ρ rfl xm (fun q => rfl) hq
  have hy_fixed_comm : ∀ q : Q', ym q = 1 →
      ((q : T) : G) * ((b : T) : G) = ((b : T) : G) * ((q : T) : G) :=
    fun q hq => fixed_comm hQn hQ'sq ρ rfl ym (fun q => rfl) hq
  have hfixA : Nat.card ↥(LinearMap.ker x ⊓ LinearMap.ker y) ^ 4 ≤ Nat.card A := by
    rw [hcardA]
    exact (Nat.pow_le_pow_left
      (fixed_points_card_le hQ hdecomp xm ym x y hx_apply hy_apply
        hx_fixed_comm hy_fixed_comm) 4).trans hfix
  obtain ⟨nA, hnxa, hnyb⟩ := exists_eq_of_endomorphisms_of_card_pow_le x y hx2 hy2 hxy hfixA
    ha_add hb_add hab_add
  let n' : Q' := Additive.toMul nA
  let n : G := ((n' : T) : G)
  have hnQ : n ∈ Q := n'.2
  have hxm_n : xm n' = ma := by
    have h := hnxa
    rw [show nA = Additive.ofMul n' from (ofMul_toMul nA).symm, hx_apply] at h
    exact Additive.ofMul.injective h
  have hym_n : ym n' = mb := by
    have h := hnyb
    rw [show nA = Additive.ofMul n' from (ofMul_toMul nA).symm, hy_apply] at h
    exact Additive.ofMul.injective h
  have hδn : ∀ t : T, δ t = ρ t n' * n'⁻¹ :=
    coboundary_on_T hdecomp ρ hρQ δ hδ_cocycle hδ_Q hδ_const_left
      xm ym (fun q => rfl) (fun q => rfl) rfl rfl hQ'sq n' hxm_n hym_n
  have hδeq : ∀ t ∈ T, c * t * c⁻¹ * t⁻¹ = t * n * t⁻¹ * n⁻¹ := by
    intro t ht
    have h := hδn ⟨t, ht⟩
    simpa [δ, ρ, MulAut.conjNormal_apply, n] using
      congrArg (fun z : Q' => ((z : T) : G)) h
  exact ⟨n, hnQ, mul_commute_of_coboundary
    (fun x hx y hy => congrArg (fun z : Q => (z : G))
      (hQ.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hcQ hnQ hcT hδeq⟩

theorem exists_mul_commute_of_odd_index {G : Type*} [Group G] {L Q T : Subgroup G} [Finite L]
    (hQL : Q ≤ L) (hQn : (Q.subgroupOf L).Normal)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hQ2 : IsPGroup 2 Q) (hTL : T ≤ L) (hTodd : Odd (T.subgroupOf L).index)
    {c : G} (hcQ : ∀ q ∈ Q, c * q = q * c)
    (hcL : ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ Q)
    (hcT : ∀ t ∈ T, c * t = t * c) :
    ∃ y ∈ Q, ∀ l ∈ L, c * y * l = l * (c * y) := by
  classical
  let M : Subgroup L := Q.subgroupOf L
  haveI : M.Normal := hQn
  letI : CommGroup M :=
    { (inferInstance : Group M) with
      mul_comm := fun x y => by
        apply Subtype.ext
        apply Subtype.ext
        change ((x : L) : G) * ((y : L) : G) = ((y : L) : G) * ((x : L) : G)
        exact hQab ((x : L) : G) x.2 ((y : L) : G) y.2 }
  haveI : Finite M := Subtype.finite
  have hM2 : IsPGroup 2 M := hQ2.comap_subtype
  let ρ : L →* MulAut M := MulAut.conjNormal
  let δ : L → M := fun l =>
    ⟨⟨c * (l : G) * c⁻¹ * (l : G)⁻¹, hQL (hcL l l.2)⟩,
      Subgroup.mem_subgroupOf.mpr (hcL l l.2)⟩
  have hδcocycle : ∀ x y : L, δ (x * y) = δ x * ρ x (δ y) := by
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    simp only [δ, ρ, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hδT : ∀ t ∈ T.subgroupOf L, δ t = 1 := by
    intro t ht
    apply Subtype.ext
    apply Subtype.ext
    simp only [δ, Subgroup.coe_one]
    have htL : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    rw [hcT (t : G) htL]
    group
  obtain ⟨y, hy⟩ := exists_coboundary_of_odd_index_of_isPGroup (hM := hM2) (ρ := ρ)
    (δ := δ) (hδ := hδcocycle) (T := T.subgroupOf L) hTodd hδT
  have hyQ : ((y : L) : G) ∈ Q := y.2
  have hδeq : ∀ l ∈ L, c * (l : G) * c⁻¹ * (l : G)⁻¹ =
      (l : G) * ((y : L) : G) * (l : G)⁻¹ * ((y : L) : G)⁻¹ := by
    intro l hl
    have h := congrArg (fun z : M => ((z : L) : G)) (hy ⟨l, hl⟩)
    simpa [δ, ρ, MulAut.conjNormal_apply] using h
  exact ⟨((y : L) : G), hyQ, mul_commute_of_coboundary hQab hcQ hyQ hcL hδeq⟩

theorem exists_mul_commute_of_kleinFour_odd_index_of_card_pow_le {G : Type*} [Group G]
    {L Q T : Subgroup G} [Finite L]
    (hQL : Q ≤ L) (hQT : Q ≤ T) (hTL : T ≤ L)
    (hQnL : (Q.subgroupOf L).Normal)
    (hQ : IsElemAbelian 2 Q)
    (hTQ : Q.relIndex T = 4) (hTsq : ∀ t ∈ T, t ^ 2 ∈ Q)
    (hfix : Nat.card ↥(Q ⊓ Subgroup.centralizer (T : Set G)) ^ 4 ≤ Nat.card ↥Q)
    (hTodd : Odd (T.subgroupOf L).index)
    {c : G} (hcQ : ∀ q ∈ Q, c * q = q * c)
    (hcL : ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ Q) :
    ∃ y ∈ Q, ∀ l ∈ L, c * y * l = l * (c * y) := by
  classical
  have hQnT : (Q.subgroupOf T).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQT).mpr ?_
    exact hTL.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hQL).mp hQnL)
  have hcT : ∀ t ∈ T, c * t * c⁻¹ * t⁻¹ ∈ Q := fun t ht => hcL t (hTL ht)
  have hQfin : Finite Q :=
    Finite.of_injective (Subgroup.inclusion hQL) (Subgroup.inclusion_injective hQL)
  haveI : Finite Q := hQfin
  obtain ⟨n, hnQ, hnT⟩ :=
    exists_mul_commute_of_kleinFour_of_card_pow_le hQT hQnT hQ hTQ hTsq hfix hcQ hcT
  have hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    intro x hx y hy
    have h := hQ.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg (fun z : Q => (z : G)) h
  have hQ2 : IsPGroup 2 Q := fun x => ⟨1, by
    rw [pow_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hQ.2 (x : G) x.2⟩
  have hc'Q : ∀ q ∈ Q, (c * n) * q = q * (c * n) := by
    intro q hq
    have hnq : n * q = q * n := hQab n hnQ q hq
    calc (c * n) * q = c * (n * q) := by group
      _ = c * (q * n) := by rw [hnq]
      _ = (c * q) * n := by group
      _ = (q * c) * n := by rw [hcQ q hq]
      _ = q * (c * n) := by group
  have hc'L : ∀ l ∈ L, (c * n) * l * (c * n)⁻¹ * l⁻¹ ∈ Q := by
    intro l hl
    change ⁅c * n, l⁆ ∈ Q
    have h1 : ⁅c * n, l⁆ = c * ⁅n, l⁆ * c⁻¹ * ⁅c, l⁆ :=
      commutatorElement_mul_left_eq_conj_mul c n l
    have hcl : ⁅c, l⁆ ∈ Q := by
      show c * l * c⁻¹ * l⁻¹ ∈ Q
      exact hcL l hl
    have hln : ⁅l, n⁆ ∈ Q := by
      have hconj : l * n * l⁻¹ ∈ Q := by
        let nM : Q.subgroupOf L :=
          ⟨⟨n, hQL hnQ⟩, Subgroup.mem_subgroupOf.mpr hnQ⟩
        let lL : L := ⟨l, hl⟩
        have h := hQnL.conj_mem nM nM.2 lL
        simpa using Subgroup.mem_subgroupOf.mp h
      have h := Q.mul_mem hconj (Q.inv_mem hnQ)
      simpa [commutatorElement_def] using h
    have hnl : ⁅n, l⁆ ∈ Q := by
      have h := Q.inv_mem hln
      simpa using h
    have hc_conj : c * ⁅n, l⁆ * c⁻¹ = ⁅n, l⁆ := by
      have h := hcQ ⁅n, l⁆ hnl
      calc c * ⁅n, l⁆ * c⁻¹ = (⁅n, l⁆ * c) * c⁻¹ := by rw [h]
        _ = ⁅n, l⁆ := by group
    rw [h1, hc_conj]
    exact Q.mul_mem hnl hcl
  obtain ⟨y, hyQ, hyL⟩ := exists_mul_commute_of_odd_index hQL hQnL hQab hQ2 hTL hTodd
    hc'Q hc'L hnT
  refine ⟨n * y, Q.mul_mem hnQ hyQ, ?_⟩
  intro l hl
  simpa [mul_assoc] using hyL l hl

theorem exists_mul_commute_of_kleinFour_odd_index {G : Type*} [Group G]
    {L Q T : Subgroup G} [Finite L]
    (hQL : Q ≤ L) (hQT : Q ≤ T) (hTL : T ≤ L)
    (hQnL : (Q.subgroupOf L).Normal)
    (hQ : IsElemAbelian 2 Q) (hQcard : Nat.card Q = 16)
    (hTQ : Q.relIndex T = 4) (hTsq : ∀ t ∈ T, t ^ 2 ∈ Q)
    (hfix : Nat.card ↥(Q ⊓ Subgroup.centralizer (T : Set G)) ≤ 2)
    (hTodd : Odd (T.subgroupOf L).index)
    {c : G} (hcQ : ∀ q ∈ Q, c * q = q * c)
    (hcL : ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ Q) :
    ∃ y ∈ Q, ∀ l ∈ L, c * y * l = l * (c * y) := by
  refine exists_mul_commute_of_kleinFour_odd_index_of_card_pow_le
    hQL hQT hTL hQnL hQ hTQ hTsq ?_ hTodd hcQ hcL
  calc Nat.card ↥(Q ⊓ Subgroup.centralizer (T : Set G)) ^ 4
      ≤ 2 ^ 4 := Nat.pow_le_pow_left hfix 4
    _ = 16 := by norm_num
    _ = Nat.card Q := hQcard.symm

private lemma card_map_quotient {G : Type*} [Group G] {Z N A : Subgroup G}
    [hN : (Z.subgroupOf N).Normal] (hAN : A ≤ N) :
    Nat.card ↥((A.subgroupOf N).map (QuotientGroup.mk' (Z.subgroupOf N))) = Z.relIndex A := by
  have h := Subgroup.relIndex_ker (QuotientGroup.mk' (Z.subgroupOf N)) (K := A.subgroupOf N)
  rw [QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hAN] at h
  exact h.symm

private lemma relIndex_map_quotient {G : Type*} [Group G] {Z N A B : Subgroup G}
    [hN : (Z.subgroupOf N).Normal] (hBN : B ≤ N) (hZA : Z ≤ A) (hZB : Z ≤ B) :
    ((A.subgroupOf N).map (QuotientGroup.mk' (Z.subgroupOf N))).relIndex
        ((B.subgroupOf N).map (QuotientGroup.mk' (Z.subgroupOf N))) = A.relIndex B := by
  rw [Subgroup.relIndex_map_map, QuotientGroup.ker_mk',
    sup_eq_left.mpr (Subgroup.subgroupOf_mono N hZA),
    sup_eq_left.mpr (Subgroup.subgroupOf_mono N hZB),
    Subgroup.relIndex_subgroupOf hBN]

private lemma isElemAbelian_map_quotient {G : Type*} [Group G] {Z N Q : Subgroup G}
    [hN : (Z.subgroupOf N).Normal]
    (hQsq : ∀ q ∈ Q, q ^ 2 ∈ Z) (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z) :
    IsElemAbelian 2 ((Q.subgroupOf N).map (QuotientGroup.mk' (Z.subgroupOf N))) := by
  let π := QuotientGroup.mk' (Z.subgroupOf N)
  refine ⟨?_, ?_⟩
  · refine IsMulCommutative.of_comm ?_
    intro x y
    apply Subtype.ext
    have hcommG : ⁅(x : N ⧸ Z.subgroupOf N), (y : N ⧸ Z.subgroupOf N)⁆ = 1 := by
      obtain ⟨xN, hxN, hxval⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨yN, hyN, hyval⟩ := Subgroup.mem_map.mp y.2
      rw [← hxval, ← hyval, ← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf N) ⁅xN, yN⁆).mpr
        (Subgroup.mem_subgroupOf.mpr
          (hQcomm (xN : G) (Subgroup.mem_subgroupOf.mp hxN) (yN : G)
            (Subgroup.mem_subgroupOf.mp hyN)))
    simpa using (commutatorElement_eq_one_iff_mul_comm.mp hcommG)
  · intro x hx
    obtain ⟨xN, hxN, hxval⟩ := Subgroup.mem_map.mp hx
    rw [← hxval, ← map_pow]
    exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf N) (xN ^ 2)).mpr
      (Subgroup.mem_subgroupOf.mpr (hQsq (xN : G) (Subgroup.mem_subgroupOf.mp hxN)))

private lemma normal_subgroupOf_map_quotient {G : Type*} [Group G] {Z N Q L : Subgroup G}
    [hN : (Z.subgroupOf N).Normal] (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hQL : Q ≤ L) (hLN : L ≤ N) :
    (((Q.subgroupOf N).map (QuotientGroup.mk' (Z.subgroupOf N))).subgroupOf
      ((L.subgroupOf N).map (QuotientGroup.mk' (Z.subgroupOf N)))).Normal := by
  let π := QuotientGroup.mk' (Z.subgroupOf N)
  have hLNQ : L.subgroupOf N ≤ Subgroup.normalizer (Q.subgroupOf N) := by
    intro x hx
    exact Subgroup.le_normalizer_comap N.subtype (hLQ (Subgroup.mem_subgroupOf.mp hx))
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_mono (Subgroup.subgroupOf_mono N hQL))).mpr ?_
  calc (L.subgroupOf N).map π ≤ (Subgroup.normalizer (Q.subgroupOf N)).map π :=
        Subgroup.map_mono hLNQ
    _ ≤ Subgroup.normalizer ((Q.subgroupOf N).map π) := Subgroup.le_normalizer_map π

private lemma fixed_points_map_le {G : Type*} [Group G] {Z Q T L R N : Subgroup G}
    [hN : (Z.subgroupOf N).Normal]
    (hTL : T ≤ L) (hLN : L ≤ N)
    (hR : ∀ q ∈ Q, (∀ t ∈ T, ⁅q, t⁆ ∈ Z) → q ∈ R) :
    ((Q.subgroupOf N).map (QuotientGroup.mk' (Z.subgroupOf N))) ⊓
      Subgroup.centralizer (((T.subgroupOf N).map (QuotientGroup.mk' (Z.subgroupOf N))) :
        Set (N ⧸ (Z.subgroupOf N))) ≤
    (R.subgroupOf N).map (QuotientGroup.mk' (Z.subgroupOf N)) := by
  let π := QuotientGroup.mk' (Z.subgroupOf N)
  rintro x ⟨hxQ, hxT⟩
  obtain ⟨q, hqN, hqval⟩ := Subgroup.mem_map.mp hxQ
  have hqT : ∀ t ∈ T, ⁅(q : G), t⁆ ∈ Z := by
    intro t ht
    have htN : (⟨t, hTL.trans hLN ht⟩ : N) ∈ T.subgroupOf N :=
      Subgroup.mem_subgroupOf.mpr ht
    have htbar : π ⟨t, hTL.trans hLN ht⟩ ∈ (T.subgroupOf N).map π :=
      Subgroup.mem_map_of_mem π htN
    have hxcomm : ⁅(x : N ⧸ Z.subgroupOf N), π ⟨t, hTL.trans hLN ht⟩⁆ = 1 :=
      (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hxT) _ htbar
    have hmap : π ⁅q, (⟨t, hTL.trans hLN ht⟩ : N)⁆ =
        ⁅(x : N ⧸ Z.subgroupOf N), π ⟨t, hTL.trans hLN ht⟩⁆ := by
      rw [map_commutatorElement, hqval]
    have hxcomm' : π ⁅q, (⟨t, hTL.trans hLN ht⟩ : N)⁆ = 1 := by
      rw [hmap]
      exact hxcomm
    exact Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (N := Z.subgroupOf N) _).mp hxcomm')
  rw [← hqval]
  exact Subgroup.mem_map_of_mem π
    (Subgroup.mem_subgroupOf.mpr (hR (q : G) (Subgroup.mem_subgroupOf.mp hqN) hqT))

private lemma lift_commutator_mem {G : Type*} [Group G] {Z Q L N : Subgroup G}
    [hN : (Z.subgroupOf N).Normal] (hLN : L ≤ N)
    {c : G} (hcZ : c ∈ N) {ybar : N ⧸ (Z.subgroupOf N)}
    (hybarQ : ybar ∈ (Q.subgroupOf N).map (QuotientGroup.mk' (Z.subgroupOf N)))
    (hybarL : ∀ l ∈ (L.subgroupOf N).map (QuotientGroup.mk' (Z.subgroupOf N)),
      QuotientGroup.mk' (Z.subgroupOf N) ⟨c, hcZ⟩ * ybar * l =
        l * (QuotientGroup.mk' (Z.subgroupOf N) ⟨c, hcZ⟩ * ybar)) :
    ∃ y ∈ Q, ∀ l ∈ L, ⁅c * y, l⁆ ∈ Z := by
  let π := QuotientGroup.mk' (Z.subgroupOf N)
  let cN : N := ⟨c, hcZ⟩
  obtain ⟨yN, hyNQ, hyval⟩ := Subgroup.mem_map.mp hybarQ
  refine ⟨(yN : G), Subgroup.mem_subgroupOf.mp hyNQ, ?_⟩
  intro l hl
  have hcyN : c * (yN : G) ∈ N := N.mul_mem hcZ yN.2
  have hlN : (⟨l, hLN hl⟩ : N) ∈ L.subgroupOf N := Subgroup.mem_subgroupOf.mpr hl
  have hlbar : π ⟨l, hLN hl⟩ ∈ (L.subgroupOf N).map π := Subgroup.mem_map_of_mem π hlN
  have hcomm := hybarL _ hlbar
  have hcy : π ⟨c * (yN : G), hcyN⟩ = π cN * ybar := by
    rw [show (⟨c * (yN : G), hcyN⟩ : N) = cN * yN from Subtype.ext rfl, map_mul, hyval]
  have hcommN : ⁅c * (yN : G), l⁆ ∈ N := by
    simpa [commutatorElement_def] using
      N.mul_mem (N.mul_mem (N.mul_mem hcyN (hLN hl)) (N.inv_mem hcyN)) (N.inv_mem (hLN hl))
  have hmem : π ⟨⁅c * (yN : G), l⁆, hcommN⟩ = 1 := by
    have hmap : π ⟨⁅c * (yN : G), l⁆, hcommN⟩ =
        ⁅π ⟨c * (yN : G), hcyN⟩, π ⟨l, hLN hl⟩⁆ := by
      rw [← map_commutatorElement]
      rfl
    rw [hmap, commutatorElement_eq_one_iff_mul_comm, hcy]
    exact hcomm
  exact Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff (N := Z.subgroupOf N) ⟨⁅c * (yN : G), l⁆, hcommN⟩).mp hmem)

theorem exists_mul_commutator_mem_of_kleinFour_odd_index_mod {G : Type*} [Group G] [Finite G]
    {Z Q T L R : Subgroup G}
    (hZQ : Z ≤ Q) (hQT : Q ≤ T) (hTL : T ≤ L)
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G)) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hQsq : ∀ q ∈ Q, q ^ 2 ∈ Z) (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z)
    (hTsq : ∀ t ∈ T, t ^ 2 ∈ Q) (hTQ : Q.relIndex T = 4)
    (hZR : Z ≤ R) (hRQ : R ≤ Q) (hR : ∀ q ∈ Q, (∀ t ∈ T, ⁅q, t⁆ ∈ Z) → q ∈ R)
    (hfix : Z.relIndex R ^ 4 ≤ Z.relIndex Q)
    (hTodd : Odd (T.relIndex L))
    {c : G} (hcZ : c ∈ Subgroup.normalizer (Z : Set G))
    (hcQ : ∀ q ∈ Q, ⁅c, q⁆ ∈ Z) (hcL : ∀ l ∈ L, ⁅c, l⁆ ∈ Q) :
    ∃ y ∈ Q, ∀ l ∈ L, ⁅c * y, l⁆ ∈ Z := by
  classical
  let N : Subgroup G := Subgroup.normalizer (Z : Set G)
  have hQN : Q ≤ N := hQT.trans (hTL.trans hLZ)
  have hTN : T ≤ N := hTL.trans hLZ
  have hLN : L ≤ N := hLZ
  have hRN : R ≤ N := hRQ.trans hQN
  let ZN : Subgroup N := Z.subgroupOf N
  haveI : ZN.Normal := Subgroup.normal_in_normalizer
  let π : N →* N ⧸ ZN := QuotientGroup.mk' ZN
  let cN : N := ⟨c, hcZ⟩
  haveI : Finite (N ⧸ ZN) := Finite.of_surjective π (QuotientGroup.mk'_surjective ZN)
  let Qbar : Subgroup (N ⧸ ZN) := (Q.subgroupOf N).map π
  let Tbar : Subgroup (N ⧸ ZN) := (T.subgroupOf N).map π
  let Lbar : Subgroup (N ⧸ ZN) := (L.subgroupOf N).map π
  let Rbar : Subgroup (N ⧸ ZN) := (R.subgroupOf N).map π
  have hQbarLbar : Qbar ≤ Lbar :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono N (hQT.trans hTL))
  have hQbarTbar : Qbar ≤ Tbar := Subgroup.map_mono (Subgroup.subgroupOf_mono N hQT)
  have hTbarLbar : Tbar ≤ Lbar := Subgroup.map_mono (Subgroup.subgroupOf_mono N hTL)
  have hQnBar : (Qbar.subgroupOf Lbar).Normal :=
    normal_subgroupOf_map_quotient hLQ (hQT.trans hTL) hLN
  have hQbarElem : IsElemAbelian 2 Qbar := isElemAbelian_map_quotient hQsq hQcomm
  have hTQbar : Qbar.relIndex Tbar = 4 := by
    have h := relIndex_map_quotient hTN hZQ (hZQ.trans hQT)
    rw [h, hTQ]
  have hTLbar : Tbar.relIndex Lbar = T.relIndex L :=
    relIndex_map_quotient hLN (hZQ.trans hQT) (hZQ.trans (hQT.trans hTL))
  have hTsqBar : ∀ t ∈ Tbar, t ^ 2 ∈ Qbar := by
    intro t ht
    obtain ⟨tN, htN, htval⟩ := Subgroup.mem_map.mp ht
    rw [← htval, ← map_pow]
    refine Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ?_)
    simpa using hTsq (tN : G) (Subgroup.mem_subgroupOf.mp htN)
  have hcardQ : Nat.card ↥Qbar = Z.relIndex Q := card_map_quotient hQN
  have hcardR : Nat.card ↥Rbar = Z.relIndex R := card_map_quotient hRN
  have hfixBar : Nat.card ↥(Qbar ⊓ Subgroup.centralizer (Tbar : Set (N ⧸ ZN))) ^ 4 ≤
      Nat.card ↥Qbar := by
    have hle : Qbar ⊓ Subgroup.centralizer (Tbar : Set (N ⧸ ZN)) ≤ Rbar :=
      fixed_points_map_le hTL hLN hR
    have hcard_le : Nat.card ↥(Qbar ⊓ Subgroup.centralizer (Tbar : Set (N ⧸ ZN))) ≤
        Nat.card ↥Rbar :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    calc Nat.card ↥(Qbar ⊓ Subgroup.centralizer (Tbar : Set (N ⧸ ZN))) ^ 4
        ≤ Nat.card ↥Rbar ^ 4 := Nat.pow_le_pow_left hcard_le 4
      _ = Z.relIndex R ^ 4 := by rw [hcardR]
      _ ≤ Z.relIndex Q := hfix
      _ = Nat.card ↥Qbar := hcardQ.symm
  have hToddBar : Odd (Tbar.subgroupOf Lbar).index := by
    show Odd (Tbar.relIndex Lbar)
    rw [hTLbar]
    exact hTodd
  have hcQbar : ∀ q ∈ Qbar, π cN * q = q * π cN := by
    intro q hq
    obtain ⟨qN, hqN, hqval⟩ := Subgroup.mem_map.mp hq
    rw [← hqval, ← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := ZN) ⁅cN, qN⁆).mpr
      (Subgroup.mem_subgroupOf.mpr (hcQ (qN : G) (Subgroup.mem_subgroupOf.mp hqN)))
  have hcLbar : ∀ l ∈ Lbar, ⁅π cN, l⁆ ∈ Qbar := by
    intro l hl
    obtain ⟨lN, hlN, hlval⟩ := Subgroup.mem_map.mp hl
    rw [← hlval, ← map_commutatorElement]
    exact Subgroup.mem_map_of_mem π
      (Subgroup.mem_subgroupOf.mpr (hcL (lN : G) (Subgroup.mem_subgroupOf.mp hlN)))
  obtain ⟨ybar, hybarQ, hybarL⟩ :=
    exists_mul_commute_of_kleinFour_odd_index_of_card_pow_le
      hQbarLbar hQbarTbar hTbarLbar hQnBar hQbarElem hTQbar hTsqBar hfixBar hToddBar
      hcQbar hcLbar
  exact lift_commutator_mem hLN hcZ hybarQ hybarL

end CFSG.GroupTheory
