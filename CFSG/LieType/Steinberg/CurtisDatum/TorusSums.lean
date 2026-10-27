module

public import CFSG.LieType.Steinberg.CurtisDatum
public import CFSG.Quasithin.Background.SmithCurtisMain

public section

namespace CFSG.LieType.Steinberg

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.SpecialLinear CFSG.Quasithin.SmithCurtis
open scoped commutatorElement Pointwise

@[instance_reducible] private noncomputable def fintypeOfFinite (α : Type*) [Finite α] : Fintype α :=
  Fintype.ofFinite α

attribute [local instance] fintypeOfFinite

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρD" => weylAction D.isFiniteType

theorem mul_diagonal_mul_apply_self {R : Type*} [CommRing R] {n : ℕ}
    {L U : Matrix (Fin n) (Fin n) R} (d : Fin n → R)
    (hU : ∀ a b, b < a → U a b = 0)
    (hU1 : ∀ a, U a a = 1) {p : Fin n} (hLp : L p p = 1)
    (h0 : ∀ j, j < p → (L * diagonal d * U) p j = 0) :
    (L * diagonal d * U) p p = d p := by
  let A := L * diagonal d
  have hA : ∀ j : Fin n, j < p → A p j = 0 := by
    intro j hj
    have hjv : j.val < p.val := Fin.lt_def.mp hj
    have key : ∀ m, m < p.val → ∀ i : Fin n, i.val = m → A p i = 0 := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro hm i hi
        have hip : i < p := Fin.lt_def.mpr (by omega)
        have hprod : (A * U) p i = A p i := by
          rw [Matrix.mul_apply]
          refine (Finset.sum_eq_single i ?_ ?_).trans ?_
          · intro k _ hki
            rcases lt_or_gt_of_ne hki with hki' | hki'
            · have hk : A p k = 0 := ih k.val (by omega) (by omega) k rfl
              rw [hk, zero_mul]
            · rw [hU k i hki', mul_zero]
          · intro hi'; simp at hi'
          · rw [hU1 i, mul_one]
        rw [← hprod, h0 i hip]
    exact key j.val hjv j rfl
  have hApp : A p p = d p := by
    rw [show A = L * diagonal d from rfl, Matrix.mul_apply]
    refine (Finset.sum_eq_single p ?_ ?_).trans ?_
    · intro k _ hkp
      rw [Matrix.diagonal_apply_ne _ hkp, mul_zero]
    · intro hp'; simp at hp'
    · rw [Matrix.diagonal_apply_eq, hLp, one_mul]
  have hdiag : (A * U) p p = A p p * U p p := by
    rw [Matrix.mul_apply]
    refine (Finset.sum_eq_single p ?_ ?_).trans ?_
    · intro k _ hkp
      rcases lt_or_gt_of_ne hkp with hkp' | hkp'
      · rw [hA k hkp', zero_mul]
      · rw [hU k p hkp', mul_zero]
    · intro hp'; simp at hp'
    · rfl
  rw [show (L * diagonal d * U) p p = (A * U) p p from rfl, hdiag, hApp, hU1 p, mul_one]

theorem curtisDatumOf_phi_conj
    (hct : IsCTGroupDatum cs ρD D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (hBU : BruhatExtras D H) (p : ℕ)
    (hpG : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    {i : Fin D.rank} {x : K} (hx : x ∈ D.rootGroup (Pi.single i 1)) (hx1 : x ≠ 1)
    {t : K} (ht : t ∈ ⨆ j, H j) :
    (curtisDatumOf hct hext hBU p hpG).phi i (t * x * t⁻¹) =
      t * (curtisDatumOf hct hext hBU p hpG).phi i x * ((n i)⁻¹ * t⁻¹ * n i) := by
  classical
  set D' := curtisDatumOf hct hext hBU p hpG with hD'
  set z := (n i)⁻¹ * t⁻¹ * n i with hzdef
  have hz : z ∈ ⨆ j, H j := by
    rw [hzdef]
    exact D'.n_inv_normH (s := i) (h := t⁻¹) (inv_mem ht)
  have hx' : t * x * t⁻¹ ∈ D.rootGroup (Pi.single i 1) := D'.H_normX i t ht x hx
  have hx1' : t * x * t⁻¹ ≠ 1 := by
    intro h
    apply hx1
    calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
      _ = 1 := by rw [h]; group
  obtain ⟨l, hl, u, hu, he⟩ := rankOnePhi_spec hct hext hBU i hx hx1
  have hphi_mem : rankOnePhi hct hext hBU i x ∈ H i := rankOnePhi_mem hct hext hBU i hx hx1
  have hl' : t * l * t⁻¹ ∈ negUnipotent D := D'.H_normL t ht l hl
  have hh' : t * rankOnePhi hct hext hBU i x * z ∈ ⨆ j, H j :=
    mul_mem (mul_mem ht (le_iSup H i hphi_mem)) hz
  have hu' : z⁻¹ * u * z ∈ posUnipotent D := D'.H_normU' z hz u hu
  have heq : (t * x * t⁻¹) * n i =
      (t * l * t⁻¹) * (t * rankOnePhi hct hext hBU i x * z) * (z⁻¹ * u * z) := by
    rw [hzdef] at *
    calc (t * x * t⁻¹) * n i = t * (x * n i) * ((n i)⁻¹ * t⁻¹ * n i) := by group
      _ = t * (l * rankOnePhi hct hext hBU i x * u) * ((n i)⁻¹ * t⁻¹ * n i) := by rw [he]
      _ = t * l * t⁻¹ * (t * rankOnePhi hct hext hBU i x * ((n i)⁻¹ * t⁻¹ * n i)) *
            (((n i)⁻¹ * t⁻¹ * n i)⁻¹ * u * ((n i)⁻¹ * t⁻¹ * n i)) := by group
  have hres := curtisDatumOf_phi_unique hct hext hBU p hpG hx' hx1' hl' hh' hu' heq
  rw [← hres, hD', curtisDatumOf_phi_apply]

theorem curtisDatumOf_d'Scalar_eq_dScalar
    (hct : IsCTGroupDatum cs ρD D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (hBU : BruhatExtras D H) (p : ℕ)
    (hpG : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) {k : Type*} [Field k] (χ : K → k)
    (i : Fin D.rank) :
    (curtisDatumOf hct hext hBU p hpG).d'Scalar χ i =
      (curtisDatumOf hct hext hBU p hpG).dScalar χ i := by
  unfold CurtisDatum.dScalar CurtisDatum.d'Scalar
  rfl

theorem curtisDatumOf_dScalar_eq_zero_of_conj
    (hct : IsCTGroupDatum cs ρD D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (hBU : BruhatExtras D H) (p : ℕ)
    (hpG : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) {k : Type*} [Field k] (χ : K → k)
    (hχ : ∀ a ∈ ⨆ j, H j, ∀ b ∈ ⨆ j, H j, χ (a * b) = χ a * χ b)
    (i : Fin D.rank) {t : K} (ht : t ∈ ⨆ j, H j)
    (hχt : χ t * χ ((n i)⁻¹ * t⁻¹ * n i) ≠ 1) :
    (curtisDatumOf hct hext hBU p hpG).dScalar χ i = 0 := by
  classical
  set D' := curtisDatumOf hct hext hBU p hpG with hD'
  set z := (n i)⁻¹ * t⁻¹ * n i with hzdef
  have hz : z ∈ ⨆ j, H j := by
    rw [hzdef]
    exact D'.n_inv_normH (s := i) (h := t⁻¹) (inv_mem ht)
  have hz1 : χ t * χ z ≠ 1 := by rw [hzdef]; exact hχt
  have hd : D'.dScalar χ i =
      ∑ x ∈ (Finset.univ : Finset (D'.X i)).erase 1, χ (D'.phi i x) := by
    unfold CurtisDatum.dScalar
    dsimp only
    refine Finset.sum_congr ?_ (fun x _ => rfl)
    ext x
    simp
  have hinv : D'.dScalar χ i = (χ t * χ z) * D'.dScalar χ i := by
    rw [hd]
    set S : Finset (D'.X i) := Finset.univ.erase 1 with hS
    have hmemS : ∀ x : D'.X i, x ∈ S ↔ x ≠ 1 := by
      intro x
      rw [hS, Finset.mem_erase]
      simp
    have hbij : ∑ x ∈ S, χ (D'.phi i (t * x * t⁻¹)) = ∑ x ∈ S, χ (D'.phi i x) := by
      refine Finset.sum_bij
        (fun x _ => (⟨t * (x : K) * t⁻¹, D'.H_normX i t ht x x.2⟩ : D'.X i)) ?_ ?_ ?_ ?_
      ·
        intro x hx
        rw [hmemS]
        intro h
        apply (hmemS x).mp hx
        have := congrArg (fun y : D'.X i => (y : K)) h
        simp only at this
        apply Subtype.ext
        calc (x : K) = t⁻¹ * (t * (x : K) * t⁻¹) * t := by group
          _ = 1 := by rw [this]; simp
      ·
        intro x₁ _ x₂ _ h
        apply Subtype.ext
        have := congrArg (fun y : D'.X i => (y : K)) h
        simp only at this
        calc (x₁ : K) = t⁻¹ * (t * (x₁ : K) * t⁻¹) * t := by group
          _ = t⁻¹ * (t * (x₂ : K) * t⁻¹) * t := by rw [this]
          _ = x₂ := by group
      ·
        intro y hy
        have hmem : t⁻¹ * (y : K) * t ∈ D'.X i := by
          simpa only [inv_inv] using D'.H_normX i t⁻¹ (inv_mem ht) (y : K) y.2
        refine ⟨(⟨t⁻¹ * (y : K) * t, hmem⟩ : D'.X i), ?_, ?_⟩
        · rw [hmemS]
          intro h
          apply (hmemS y).mp hy
          have := congrArg (fun y : D'.X i => (y : K)) h
          simp only at this
          apply Subtype.ext
          calc (y : K) = t * (t⁻¹ * (y : K) * t) * t⁻¹ := by group
            _ = 1 := by rw [this]; simp
        · apply Subtype.ext
          simp only
          group
      ·
        intro x _
        rfl
    have hstep : ∑ x ∈ S, χ (D'.phi i (t * x * t⁻¹)) =
        ∑ x ∈ S, χ t * χ (D'.phi i x) * χ z := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx1 : x ≠ 1 := (hmemS x).mp hx
      have hx1' : (x : K) ≠ 1 := fun h => hx1 (Subtype.ext h)
      have hp : D'.phi i x ∈ ⨆ j, H j := D'.phi_mem i x x.2 hx1'
      rw [curtisDatumOf_phi_conj hct hext hBU p hpG x.2 hx1' ht]
      calc χ (t * D'.phi i x * z) = χ (t * (D'.phi i x * z)) := by rw [mul_assoc]
        _ = χ t * χ (D'.phi i x * z) := hχ t ht (D'.phi i x * z) (mul_mem hp hz)
        _ = χ t * (χ (D'.phi i x) * χ z) := by rw [hχ (D'.phi i x) hp z hz]
        _ = χ t * χ (D'.phi i x) * χ z := by ring
    have hfactor : ∑ x ∈ S, χ t * χ (D'.phi i x) * χ z =
        (χ t * χ z) * ∑ x ∈ S, χ (D'.phi i x) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    calc ∑ x ∈ S, χ (D'.phi i x)
        = ∑ x ∈ S, χ (D'.phi i (t * x * t⁻¹)) := hbij.symm
      _ = ∑ x ∈ S, χ t * χ (D'.phi i x) * χ z := hstep
      _ = (χ t * χ z) * ∑ x ∈ S, χ (D'.phi i x) := hfactor
  have hmul : (χ t * χ z - 1) * D'.dScalar χ i = 0 := by
    rw [sub_mul, one_mul, ← hinv, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hz1)

theorem curtisDatumOf_dScalar_eq_neg_one
    (hct : IsCTGroupDatum cs ρD D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (hBU : BruhatExtras D H) (p : ℕ)
    (hpG : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p] (χ : K → k) (i : Fin D.rank)
    (hχ : ∀ h ∈ H i, χ h = 1) :
    (curtisDatumOf hct hext hBU p hpG).dScalar χ i = -1 := by
  classical
  set D' := curtisDatumOf hct hext hBU p hpG with hD'
  have hterm : ∀ x : D'.X i, x ≠ 1 → χ (D'.phi i x) = 1 := by
    intro x hx1
    have hphi : D'.phi i (x : K) = rankOnePhi hct hext hBU i (x : K) := by
      show (curtisDatumOf hct hext hBU p hpG).phi i (x : K) =
        rankOnePhi hct hext hBU i (x : K)
      rfl
    rw [hphi]
    exact hχ _ (rankOnePhi_mem hct hext hBU i x.2 (fun h => hx1 (Subtype.ext h)))
  have hd : D'.dScalar χ i =
      ∑ x ∈ (Finset.univ : Finset (D'.X i)).erase 1, χ (D'.phi i x) := by
    unfold CurtisDatum.dScalar
    dsimp only
    refine Finset.sum_congr ?_ (fun x _ => rfl)
    ext x
    simp
  rw [hd]
  set S : Finset (D'.X i) := Finset.univ.erase 1 with hS
  have hmemS : ∀ x : D'.X i, x ∈ S ↔ x ≠ 1 := by
    intro x
    rw [hS, Finset.mem_erase]
    simp
  rw [Finset.sum_congr rfl (fun x hx => hterm x ((hmemS x).mp hx))]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : S.card = Nat.card (D'.X i) - 1 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
      Nat.card_eq_fintype_card]
  rw [hcard, Nat.cast_sub (by
    have := Nat.card_pos (α := D'.X i)
    omega), Nat.cast_one,
    (CharP.cast_eq_zero_iff k p (Nat.card (D'.X i))).mpr (D'.dvd_card_X i)]
  ring

theorem heckeT_eq_zero_of_fixed {G : Type*} [Group G] {B : Type*} {M : CoxeterMatrix B}
    {W : Type*} [Group W] {cs' : CoxeterSystem M W} {p : ℕ} {D : CurtisDatum G cs' p}
    [Finite G] {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [Fact p.Prime]
    [CharP k p] (ρ : Representation k G V) (s : B) {y : V}
    (hX : ∀ x ∈ D.X s, ρ x y = y) (hn : ρ (D.n s) y = y) : D.heckeT ρ s y = 0 := by
  classical
  rw [D.heckeT_apply ρ s y]
  have hterm : ∀ x : D.X s, ρ ((x : G) * D.n s) y = y := by
    intro x
    rw [map_mul, Module.End.mul_apply, hn, hX x x.2]
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul k,
    (CharP.cast_eq_zero_iff k p (Nat.card (D.X s))).mpr (D.dvd_card_X s), zero_smul]

end CFSG.LieType.Steinberg
