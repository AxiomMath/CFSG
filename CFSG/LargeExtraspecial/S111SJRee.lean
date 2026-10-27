module

public import CFSG.Walter.JRFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurGoldAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup
open scoped Pointwise

theorem exists_commute_of_odd {M Ω : Type*} [Group M] [MulAction M Ω] {K : Subgroup M}
    [Finite K] (hK : Odd (Nat.card K)) {l : M} (hl : l * l = 1)
    (hlK : ∀ k ∈ K, l * k * l⁻¹ ∈ K) {w y : Ω} (hlw : l • w = w) (hly : l • y = y)
    {k₁ : M} (hk₁ : k₁ ∈ K) (hk₁w : k₁ • w = y) :
    ∃ k ∈ K, k • w = y ∧ k * l = l * k := by
  classical
  have hli : l⁻¹ = l := inv_eq_of_mul_eq_one_right hl
  set S : Subgroup M := K ⊓ MulAction.stabilizer M w with hS
  have hSK : S ≤ K := inf_le_left
  have : Finite S := Finite.of_injective (Subgroup.inclusion hSK) (Subgroup.inclusion_injective hSK)
  have : Fintype S := Fintype.ofFinite S
  have hSodd : Odd (Nat.card S) := Odd.of_dvd_nat hK (Subgroup.card_dvd_of_le hSK)
  have hmemS : ∀ s : M, s ∈ S ↔ s ∈ K ∧ s • w = w := fun s => by
    rw [hS, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  set a : M := k₁⁻¹ * (l * k₁ * l⁻¹) with ha
  have haS : a ∈ S := by
    refine (hmemS a).mpr ⟨mul_mem (inv_mem hk₁) (hlK k₁ hk₁), ?_⟩
    rw [ha, mul_smul, mul_smul, mul_smul, hli, hlw, hk₁w, hly, ← hk₁w, inv_smul_smul]
  have hconjS : ∀ s ∈ S, l * s * l⁻¹ ∈ S := by
    intro s hs
    obtain ⟨hsK, hsw⟩ := (hmemS s).mp hs
    refine (hmemS _).mpr ⟨hlK s hsK, ?_⟩
    rw [mul_smul, mul_smul, hli, hlw, hsw, hlw]
  have hinv : ∀ s : M, a * (l * (a * (l * s * l⁻¹)) * l⁻¹) = s := by
    intro s
    calc a * (l * (a * (l * s * l⁻¹)) * l⁻¹)
        = k₁⁻¹ * (l * l) * k₁ * s * (l⁻¹ * l⁻¹) := by rw [ha]; group
      _ = s := by rw [hl, ← mul_inv_rev, hl]; group
  let σ : Equiv.Perm S :=
    { toFun := fun s => ⟨a * (l * s * l⁻¹), mul_mem haS (hconjS s s.2)⟩
      invFun := fun s => ⟨a * (l * s * l⁻¹), mul_mem haS (hconjS s s.2)⟩
      left_inv := fun s => Subtype.ext (hinv s)
      right_inv := fun s => Subtype.ext (hinv s) }
  have hσ2 : σ ^ 2 = 1 := by
    ext s
    simp only [sq, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact hinv s
  obtain ⟨s, hs⟩ : ∃ s : S, σ s = s := by
    by_contra hno
    push Not at hno
    have hsupp : σ.support = Finset.univ := by
      ext s
      simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
      exact hno s
    have h2 := Equiv.Perm.two_dvd_card_support hσ2
    rw [hsupp, Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
    exact (Nat.not_even_iff_odd.mpr hSodd) (even_iff_two_dvd.mpr h2)
  have hs' : a * (l * (s : M) * l⁻¹) = s := congrArg Subtype.val hs
  obtain ⟨hsK, hsw⟩ := (hmemS s).mp s.2
  refine ⟨k₁ * s, mul_mem hk₁ hsK, by rw [mul_smul, hsw, hk₁w], ?_⟩
  calc k₁ * (s : M) * l = k₁ * (a * (l * (s : M) * l⁻¹)) * l := by rw [hs']
    _ = l * (k₁ * s) := by rw [ha]; group

theorem exists_fix_pair_of_card_eight {P : Type*} [Group P] [Finite P]
    (hcomm : ∀ x y : P, x * y = y * x) (hsq : ∀ x : P, x * x = 1) (h8 : Nat.card P = 8)
    {l : MulAut P} (hl : l * l = 1) (hl1 : l ≠ 1) :
    ∃ w y : P, w ≠ 1 ∧ y ≠ 1 ∧ l w = w ∧ l y = y ∧
      ∀ k : MulAut P, k * l = l * k → k w ≠ y := by
  classical
  have hll : ∀ x : P, l (l x) = x := fun x => by
    rw [← MulAut.mul_apply, hl, MulAut.one_apply]
  have hinv : ∀ x : P, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  let δ : P →* P :=
    { toFun := fun x => x * l x
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul]
        calc x * y * (l x * l y) = x * (y * l x) * l y := by group
          _ = x * (l x * y) * l y := by rw [hcomm y (l x)]
          _ = x * l x * (y * l y) := by group }
  have hδ : ∀ x, δ x = x * l x := fun x => rfl
  let C : Subgroup P :=
    { carrier := {x | l x = x}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, map_mul] at *
        rw [hx, hy]
      one_mem' := map_one l
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq, map_inv] at *
        rw [hx] }
  have hmemC : ∀ x, x ∈ C ↔ l x = x := fun x => Iff.rfl
  have hBC : δ.range ≤ C := by
    rintro _ ⟨x, rfl⟩
    rw [hmemC, hδ, map_mul, hll, hcomm]
  have hker : δ.ker = C := by
    ext x
    rw [MonoidHom.mem_ker, hδ, hmemC]
    constructor
    · intro h
      rw [eq_inv_of_mul_eq_one_right h, hinv]
    · intro h
      rw [h, hsq]
  have hcard : Nat.card C * Nat.card δ.range = 8 := by
    rw [← hker, ← Subgroup.index_ker, Subgroup.card_mul_index, h8]
  have hB1 : δ.range ≠ ⊥ := by
    intro h
    apply hl1
    ext x
    have hx : δ x = 1 := by
      have : δ x ∈ δ.range := ⟨x, rfl⟩
      rw [h, mem_bot] at this
      exact this
    rw [hδ] at hx
    rw [MulAut.one_apply, eq_inv_of_mul_eq_one_right hx, hinv]
  have hBne : δ.range ≠ C := by
    intro h
    rw [h] at hcard
    have h1 : Nat.card C ≤ 2 := by nlinarith
    have h2 : 2 ≤ Nat.card C := by
      rw [← h] at hcard ⊢
      by_contra h3
      push Not at h3
      interval_cases (Nat.card δ.range)
      · omega
      · omega
    have h3 : Nat.card C = 2 := le_antisymm h1 h2
    rw [h3] at hcard
    omega
  obtain ⟨⟨w, hwB⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB1
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨y, hyC, hyB⟩ : ∃ y ∈ C, y ∉ δ.range := by
    by_contra hno
    push Not at hno
    exact hBne (le_antisymm hBC hno)
  refine ⟨w, y, hw1', fun h => hyB (h ▸ one_mem _), hBC hwB, hyC, fun k hk hky => hyB ?_⟩
  obtain ⟨x, rfl⟩ := hwB
  rw [← hky, hδ, map_mul]
  refine ⟨k x, ?_⟩
  rw [hδ, ← MulAut.mul_apply, ← MulAut.mul_apply, hk]

variable {X : Type} [Group X]

@[expose] def sylowNormConj (P : Subgroup X) : normalizer (P : Set X) →* MulAut P where
  toFun n :=
    { toFun := fun p => ⟨n * p * (n : X)⁻¹, (mem_normalizer_iff.mp n.2 p).mp p.2⟩
      invFun := fun p => ⟨(n : X)⁻¹ * p * n, by
        have := (mem_normalizer_iff.mp (inv_mem n.2) p).mp p.2
        simpa using this⟩
      left_inv := fun p => Subtype.ext (by simp [mul_assoc])
      right_inv := fun p => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun p q => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext p
    simp
  map_mul' n n' := by
    ext p
    simp [mul_assoc]

theorem sylowNormConj_apply (P : Subgroup X) (n : normalizer (P : Set X)) (p : P) :
    ((sylowNormConj P n p : P) : X) = n * p * (n : X)⁻¹ := rfl

@[expose] def mapsToRestrict (P : Subgroup X) (a : MulAut X) (ha : ∀ x ∈ P, a x ∈ P)
    (ha' : ∀ x ∈ P, a⁻¹ x ∈ P) : MulAut P where
  toFun x := ⟨a x, ha x x.2⟩
  invFun x := ⟨a⁻¹ x, ha' x x.2⟩
  left_inv x := Subtype.ext (MulAut.inv_apply_self X a x)
  right_inv x := Subtype.ext (MulAut.apply_inv_self X a x)
  map_mul' x y := Subtype.ext (map_mul a (x : X) y)

theorem map_eq_self_of_mapsTo (P : Subgroup X) {a : MulAut X} (ha : a * a = 1)
    (haP : ∀ x ∈ P, a x ∈ P) : P.map a.toMonoidHom = P := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact haP x hx
  · intro x hx
    refine ⟨a x, haP x hx, ?_⟩
    change a (a x) = x
    rw [← MulAut.mul_apply, ha, MulAut.one_apply]

theorem apply_eq_self_of_sylow_eight [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (P : Sylow 2 X)
    (hPc : IsMulCommutative (P : Subgroup X)) (hP8 : Nat.card (P : Subgroup X) = 8)
    (hPsq : ∀ t ∈ (P : Subgroup X), t * t = 1)
    {a : MulAut X} (ha : a * a = 1) (haP : ∀ x ∈ (P : Subgroup X), a x ∈ (P : Subgroup X)) :
    ∀ x ∈ (P : Subgroup X), a x = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have ha' : ∀ x ∈ (P : Subgroup X), a⁻¹ x ∈ (P : Subgroup X) := by rw [hai]; exact haP
  by_contra hne
  push Not at hne
  obtain ⟨x₀, hx₀, hx₀ne⟩ := hne
  set l := mapsToRestrict (P : Subgroup X) a haP ha' with hldef
  have hlapp : ∀ x : (P : Subgroup X), ((l x : (P : Subgroup X)) : X) = a x := fun x => rfl
  have hliapp : ∀ x : (P : Subgroup X), ((l⁻¹ x : (P : Subgroup X)) : X) = a⁻¹ x := fun x => rfl
  have hl : l * l = 1 := by
    ext x
    rw [MulAut.mul_apply, hlapp, hlapp, MulAut.one_apply, ← MulAut.mul_apply, ha,
      MulAut.one_apply]
  have hl1 : l ≠ 1 := by
    intro h
    apply hx₀ne
    have := congrArg (fun σ : MulAut (P : Subgroup X) => ((σ ⟨x₀, hx₀⟩ : (P : Subgroup X)) : X)) h
    simpa [hlapp] using this
  have hcomm : ∀ x y : (P : Subgroup X), x * y = y * x := fun x y => hPc.is_comm.comm x y
  have hsq : ∀ x : (P : Subgroup X), x * x = 1 := fun x => Subtype.ext (hPsq x x.2)
  obtain ⟨w, y, hw1, hy1, hlw, hly, hk⟩ := exists_fix_pair_of_card_eight hcomm hsq hP8 hl hl1
  obtain ⟨htrans, -⟩ := CFSG.Walter.sylow_two_card_eight_transitive hnonab P hPc hP8
  obtain ⟨n, hn, hny⟩ := htrans w w.2 (fun h => hw1 (Subtype.ext h)) y y.2
    (fun h => hy1 (Subtype.ext h))
  set K := (sylowNormConj (P : Subgroup X)).range with hK
  have hKodd : Odd (Nat.card K) := by
    have hPN : (P : Subgroup X) ≤ normalizer ((P : Subgroup X) : Set X) := le_normalizer
    have hle : (P : Subgroup X).subgroupOf (normalizer ((P : Subgroup X) : Set X)) ≤
        (sylowNormConj (P : Subgroup X)).ker := by
      intro p hp
      rw [MonoidHom.mem_ker]
      ext x
      rw [sylowNormConj_apply, MulAut.one_apply]
      have hpx : (p : X) * x = x * p :=
        congrArg Subtype.val (hcomm ⟨p, mem_subgroupOf.mp hp⟩ x)
      rw [hpx, mul_inv_cancel_right]
    have h1 : Nat.card K = (sylowNormConj (P : Subgroup X)).ker.index := (Subgroup.index_ker _).symm
    have h2 := Subgroup.index_dvd_of_le hle
    have h3 : (P : Subgroup X).relIndex (normalizer ((P : Subgroup X) : Set X)) ∣
        (P : Subgroup X).index := Subgroup.relIndex_dvd_index_of_le hPN
    have h4 : ¬ 2 ∣ (P : Subgroup X).index := P.not_dvd_index
    rw [h1]
    refine Nat.odd_iff.mpr ?_
    have h5 : ¬ 2 ∣ (sylowNormConj (P : Subgroup X)).ker.index := fun h =>
      h4 (h.trans (h2.trans h3))
    omega
  have hmapP := map_eq_self_of_mapsTo (P : Subgroup X) ha haP
  have hlK : ∀ k ∈ K, l * k * l⁻¹ ∈ K := by
    rintro _ ⟨n', rfl⟩
    have han : a n' ∈ normalizer ((P : Subgroup X) : Set X) := by
      have h := Subgroup.map_equiv_normalizer_eq (P : Subgroup X) a
      have : a n' ∈ (normalizer ((P : Subgroup X) : Set X)).map a.toMonoidHom :=
        ⟨n', n'.2, rfl⟩
      rw [h, hmapP] at this
      exact this
    refine ⟨⟨a n', han⟩, ?_⟩
    ext x
    rw [sylowNormConj_apply, MulAut.mul_apply, MulAut.mul_apply, hlapp, sylowNormConj_apply, hliapp,
      map_mul, map_mul, map_inv, MulAut.apply_inv_self]
  have hk₁w : sylowNormConj (P : Subgroup X) ⟨n, hn⟩ • w = y := by
    rw [MulAut.smul_def]
    exact Subtype.ext (by rw [sylowNormConj_apply]; exact hny)
  obtain ⟨k, -, hkw, hkl⟩ := exists_commute_of_odd (M := MulAut (P : Subgroup X))
    (Ω := (P : Subgroup X)) hKodd hl hlK (by rw [MulAut.smul_def]; exact hlw)
    (by rw [MulAut.smul_def]; exact hly) ⟨⟨n, hn⟩, rfl⟩ hk₁w
  exact hk k hkl (by rw [← MulAut.smul_def]; exact hkw)

theorem card_le_eight_of_sylow_eight [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hT : ∀ T : Sylow 2 X, Nat.card (T : Subgroup X) = 8 ∧ IsMulCommutative (T : Subgroup X) ∧
      ∀ t ∈ (T : Subgroup X), t * t = 1)
    (A : Subgroup (MulAut X)) (hA : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut X) := Finite.of_injective (fun f : MulAut X => (f : X → X))
    DFunLike.coe_injective
  have hcenter : center X = ⊥ := by
    rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab ((mem_center_iff.mp (h ▸ mem_top a : a ∈ center X)) b).symm
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have : g ∈ center X := mem_center_iff.mpr fun y => by
      have := congrArg (fun σ : MulAut X => σ y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g = (g * y * g⁻¹) * g := by rw [this]
        _ = g * y := by group
    rw [hcenter, mem_bot] at this
    exact this
  have hA2 : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by
    rw [pow_one, pow_two]; exact hA a a.2)⟩
  obtain ⟨P, hP⟩ := hA2.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 X)
    (not_dvd_card_sylow 2 X)
  have hPmap : ∀ a ∈ A, ∀ x ∈ (P : Subgroup X), a x ∈ (P : Subgroup X) := by
    intro a ha x hx
    have h1 : (⟨a, ha⟩ : A) • P = P := hP ⟨a, ha⟩
    have h2 : a • x ∈ ((a • P : Sylow 2 X) : Subgroup X) :=
      Subgroup.smul_mem_pointwise_smul x a (P : Subgroup X) hx
    have h3 : (a • P : Sylow 2 X) = P := h1
    rw [h3] at h2
    rwa [MulAut.smul_def] at h2
  obtain ⟨hP8, hPc, hPsq⟩ := hT P
  have hfix : ∀ a ∈ A, ∀ x ∈ (P : Subgroup X), a x = x := fun a ha =>
    apply_eq_self_of_sylow_eight hnonab P hPc hP8 hPsq (hA a ha) (hPmap a ha)
  set Xi : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range with hXi
  let φ : X ≃* Xi := MonoidHom.ofInjective hinj
  have hφ : ∀ x, ((φ x : Xi) : MulAut X) = MulAut.conj x := fun x => rfl
  have hXs : IsSimpleGroup Xi := φ.symm.isSimpleGroup
  have hXnonab : ∃ a b : Xi, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨φ a, φ b, fun h => hab (φ.injective (by rw [map_mul, map_mul, h]))⟩
  set Pi : Subgroup (MulAut X) := (P : Subgroup X).map (MulAut.conj : X →* MulAut X) with hPi
  have hcardPi : Nat.card Pi = 8 := by
    rw [hPi, Subgroup.card_map_of_injective hinj, hP8]
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 2 Pi Xi := by
    let Q₀ : Subgroup Xi := (P : Subgroup X).map φ.toMonoidHom
    have hQ₀ : Nat.card Q₀ = 2 ^ (Nat.card Xi).factorization 2 := by
      show Nat.card ((P : Subgroup X).map φ.toMonoidHom) = _
      rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective,
        Nat.card_congr φ.symm.toEquiv]
      exact P.card_eq_multiplicity
    refine ⟨Sylow.ofCard Q₀ hQ₀, ?_⟩
    change Q₀.map Xi.subtype = Pi
    rw [Subgroup.map_map]
    rfl
  have hPi2 : ∀ p ∈ Pi, p * p = 1 := by
    rintro _ ⟨p, hp, rfl⟩
    rw [← map_mul, hPsq p hp, map_one]
  have hPic : ∀ p ∈ Pi, ∀ q ∈ Pi, p * q = q * p := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hPc.is_comm.comm ⟨p, hp⟩ ⟨q, hq⟩)
  have hAinv : ∀ a ∈ A, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hA a ha)
  have hAe : CFSG.Open.IsElemAbelian 2 A := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => by rw [pow_two]; exact hA a ha⟩
    calc (a : MulAut X) * b = ((a : MulAut X) * b)⁻¹ := (hAinv _ (mul_mem a.2 b.2)).symm
      _ = b * a := by rw [mul_inv_rev, hAinv _ a.2, hAinv _ b.2]
  have hconjform : ∀ (σ : MulAut X) (g : X), σ * MulAut.conj g * σ⁻¹ = MulAut.conj (σ g) := by
    intro σ g
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have hEX : A ≤ normalizer (Xi : Set (MulAut X)) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro σ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨a g, (hconjform a g).symm⟩
    · rintro ⟨g, hg⟩
      refine ⟨a⁻¹ g, ?_⟩
      rw [← hconjform, hg]
      group
  have hEcent : ∀ e ∈ A, ∀ x ∈ CFSG.ComponentClassification.AschbacherTheorem3.omegaOne Pi,
      e * x = x * e := by
    intro e he x hx
    rw [CFSG.ComponentClassification.WalterSchur.omegaOne_eq_self hPi2] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have h1 := hconjform e p
    rw [hfix e he p hp] at h1
    calc e * MulAut.conj p = e * MulAut.conj p * e⁻¹ * e := by group
      _ = MulAut.conj p * e := by rw [h1]
  have hN1 := CFSG.ComponentClassification.WalterSchur.card_le_omegaOne_of_elementary hXs
    hXnonab hPsyl hPi2 hPic hAe hEX hEcent
  have hbot : A ⊓ centralizer (Xi : Set (MulAut X)) = ⊥ := by
    rw [eq_bot_iff]
    rintro σ ⟨-, hσ⟩
    rw [mem_bot]
    ext g
    have h1 := (mem_centralizer_iff.mp hσ) (MulAut.conj g) ⟨g, rfl⟩
    have h2 : σ * MulAut.conj g * σ⁻¹ = MulAut.conj g := by rw [← h1]; group
    rw [hconjform] at h2
    rw [MulAut.one_apply]
    exact hinj h2
  rw [CFSG.ComponentClassification.WalterSchur.omegaOne_eq_self hPi2, hcardPi, hbot,
    Subgroup.card_bot, mul_one] at hN1
  exact hN1

end CFSG.LargeExtraspecial.S11
