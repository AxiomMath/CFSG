module

public import CFSG.LieType.SpecialLinear.CurtisDatum.Unipotent
public import CFSG.LieType.Steinberg.BruhatWeyl
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherDescents
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
public import CFSG.Quasithin.Background.SmithCurtisHecke
import Mathlib.Tactic.Group

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.StandardType
  CFSG.StandardType.GGRootSL CFSG.Quasithin.SmithCurtis

variable (m : ℕ) (F : Type) [Field F]

@[expose] noncomputable def weylN (k : Fin m) : SpecialLinearGroup (Fin (m + 1)) F :=
  weylRep m F k

@[expose] noncomputable def weylNW (w : (coxeterMatrix (isFiniteType_A m)).Group) :
    SpecialLinearGroup (Fin (m + 1)) F :=
  nrep (D := rootDatum m F) (isCTGroupDatum m F) w

theorem weylN_coe (k : Fin m) :
    ((weylN m F k : SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      signedPerm (Equiv.swap k.castSucc k.succ) (weylSign k.castSucc) := by
  rw [weylN, weylRep]
  exact coe_transvection_mul_transvection_mul_transvection (Fin.castSucc_lt_succ (i := k)).ne

theorem prod_n_coe_signedPerm (ω : List (Fin m)) :
    ∃ ε : Fin (m + 1) → F, (∀ i, ε i * ε i = 1) ∧
      ((((ω.map (weylN m F)).prod : SpecialLinearGroup (Fin (m + 1)) F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        signedPerm (ω.map (fun k => Equiv.swap k.castSucc k.succ)).prod ε := by
  classical
  induction ω with
  | nil =>
    refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
    simp only [List.map_nil, List.prod_nil,
      Matrix.SpecialLinearGroup.coe_one]
    rw [show (signedPerm (1 : Equiv.Perm (Fin (m + 1))) (fun _ => 1) : Matrix _ _ F) = 1 by
      rw [signedPerm_one, diagonal_one]]
  | cons k ω ih =>
    obtain ⟨ε, hε, hmat⟩ := ih
    refine ⟨fun s => weylSign k.castSucc
        (((ω.map (fun k => Equiv.swap k.castSucc k.succ)).prod) s) * ε s,
      fun s => by
        rw [mul_mul_mul_comm, weylSign_mul_self, hε _, one_mul], ?_⟩
    simp only [List.map_cons, List.prod_cons]
    rw [Matrix.SpecialLinearGroup.coe_mul, weylN_coe, hmat,
      signedPerm_mul_signedPerm]

set_option backward.isDefEq.respectTransparency false in
theorem nW_matrix_signedPerm (w : (coxeterMatrix (isFiniteType_A m)).Group) :
    ∃ ε : Fin (m + 1) → F, (∀ i, ε i * ε i = 1) ∧
      (((weylNW m F w : SpecialLinearGroup (Fin (m + 1)) F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        signedPerm ((typeAWeylEquiv m).symm w) ε := by
  classical
  obtain ⟨ω, hω, rfl⟩ :=
    (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.exists_isReduced w
  have hword : weylNW m F ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.wordProd ω) =
      ((ω.map (weylN m F)).prod) :=
    nrep_wordProd (D := rootDatum m F) (n := weylRep m F) (H := torus m F)
      (isCTGroupDatum m F) hω
  rw [hword]
  obtain ⟨ε, hε, hmat⟩ := prod_n_coe_signedPerm m F ω
  refine ⟨ε, hε, ?_⟩
  have hπ : (ω.map (fun k => Equiv.swap k.castSucc k.succ)).prod =
      (typeAWeylEquiv m).symm
        ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.wordProd ω) := by
    apply (typeAWeylEquiv m).injective
    rw [MulEquiv.apply_symm_apply]
    calc
      (typeAWeylEquiv m) ((ω.map (fun k => Equiv.swap k.castSucc k.succ)).prod)
          = ((ω.map (fun k => Equiv.swap k.castSucc k.succ)).map
              fun σ => (typeAWeylEquiv m) σ).prod :=
            map_list_prod (typeAWeylEquiv m).toMonoidHom _
      _ = (ω.map fun k => (typeAWeylEquiv m)
              (Equiv.swap k.castSucc k.succ)).prod := by
            rw [List.map_map]
            rfl
      _ = (ω.map fun k =>
              (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple k).prod := by
            congr 1
            apply List.map_congr_left
            intro k _
            exact typeAWeylEquiv_swap m k
      _ = (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.wordProd ω := rfl
  rw [← hπ]
  exact hmat

private theorem adjWordProd_map_valSucc (ω : List (Fin m)) :
    adjWordProd (m + 1) (ω.map fun k => k.val + 1) =
      (ω.map fun k => Equiv.swap k.castSucc k.succ).prod := by
  rw [adjWordProd, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  change adjSwap (m + 1) (k.val + 1) = Equiv.swap k.castSucc k.succ
  rw [adjSwap_of_lt (by omega) (by omega)]
  have h1 : (k.castSucc : Fin (m + 1)) = ⟨k.val + 1 - 1, by omega⟩ := Fin.ext (by simp)
  have h2 : (k.succ : Fin (m + 1)) = ⟨k.val + 1, by omega⟩ := Fin.ext (by simp)
  rw [← h1, ← h2]

theorem length_eq_inversionCount (w : (coxeterMatrix (isFiniteType_A m)).Group) :
    (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.length w =
      inversionCount ((typeAWeylEquiv m).symm w) := by
  classical
  let cs := (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem
  let π := (typeAWeylEquiv m).symm w
  have h_le : inversionCount π ≤ cs.length w := by
    obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    have hlen : cs.length (cs.wordProd ω) = ω.length := hω.eq
    have hπ : (ω.map fun k => Equiv.swap k.castSucc k.succ).prod =
        (typeAWeylEquiv m).symm (cs.wordProd ω) := by
      apply (typeAWeylEquiv m).injective
      rw [MulEquiv.apply_symm_apply]
      calc
        (typeAWeylEquiv m) ((ω.map fun k => Equiv.swap k.castSucc k.succ).prod)
            = ((ω.map fun k => Equiv.swap k.castSucc k.succ).map
                fun σ => (typeAWeylEquiv m) σ).prod :=
              map_list_prod (typeAWeylEquiv m).toMonoidHom _
        _ = (ω.map fun k => (typeAWeylEquiv m)
                (Equiv.swap k.castSucc k.succ)).prod := by
              rw [List.map_map]
              rfl
        _ = (ω.map fun k => cs.simple k).prod := by
              congr 1
              apply List.map_congr_left
              intro k _
              exact typeAWeylEquiv_swap m k
        _ = cs.wordProd ω := rfl
    have hl : IsAdjWord (m + 1) (ω.map fun k => k.val + 1) := by
      intro i hi
      obtain ⟨k, _, hk⟩ := List.mem_map.mp hi
      subst hk
      exact ⟨by omega, by omega⟩
    have hprod : adjWordProd (m + 1) (ω.map fun k => k.val + 1) = π := by
      rw [adjWordProd_map_valSucc, hπ]
    have hle : adjLength π ≤ (ω.map fun k => k.val + 1).length :=
      Nat.sInf_le ⟨_, hl, rfl, hprod⟩
    rw [adjLength_eq_inversionCount] at hle
    simpa [List.length_map, hlen] using hle
  have h_ge : cs.length w ≤ inversionCount π := by
    obtain ⟨l, hl, hlen, hprod⟩ := exists_word_length_eq π
    let ω : List (Fin m) :=
      l.pmap (fun i hi => (⟨i - 1, by have := hi.1; have := hi.2; omega⟩ : Fin m))
        (fun i hi => hl i hi)
    have hlenω : ω.length = l.length := List.length_pmap
    have hword : cs.wordProd ω = (typeAWeylEquiv m) (adjWordProd (m + 1) l) := by
      have hmain : ∀ (l : List ℕ) (hl : IsAdjWord (m + 1) l),
          cs.wordProd (l.pmap
              (fun i hi => (⟨i - 1, by have := hi.1; have := hi.2; omega⟩ : Fin m))
              (fun i hi => hl i hi))
            = (typeAWeylEquiv m) (adjWordProd (m + 1) l) := by
        intro l hl
        induction l with
        | nil => simp [adjWordProd]
        | cons i l ih =>
          have hi := hl i (by simp)
          have hl' : IsAdjWord (m + 1) l := fun j hj => hl j (by simp [hj])
          rw [List.pmap_cons, CoxeterSystem.wordProd_cons, adjWordProd_cons, map_mul,
            ih hl']
          congr 1
          let k : Fin m := ⟨i - 1, by omega⟩
          have hk : adjSwap (m + 1) i = Equiv.swap k.castSucc k.succ := by
            rw [adjSwap_of_lt hi.1 hi.2]
            have h1 : (k.castSucc : Fin (m + 1)) =
                ⟨i - 1, by omega⟩ := Fin.ext (by simp [k])
            have h2 : (k.succ : Fin (m + 1)) = ⟨i, hi.2⟩ := Fin.ext (by simp [k]; omega)
            rw [← h1, ← h2]
          rw [hk, typeAWeylEquiv_swap m k]
          rfl
      exact hmain l hl
    have hw : cs.wordProd ω = w := by
      rw [hword, hprod, MulEquiv.apply_symm_apply]
    have hlen' : cs.length w ≤ ω.length := by
      have := cs.length_wordProd_le ω
      rwa [hw] at this
    rw [hlenω] at hlen'
    omega
  exact le_antisymm h_ge h_le

open CFSG.LieType.Universal.SpecialLinear in
theorem signedPerm_conj_apply {n : ℕ} {R : Type*} [Field R]
    (π : Equiv.Perm (Fin n)) (ε : Fin n → R) (M : Matrix (Fin n) (Fin n) R)
    (a b : Fin n) :
    (signedPerm π ε * M * signedPerm π⁻¹ (fun s => ε (π⁻¹ s))) a b =
      ε (π⁻¹ a) * M (π⁻¹ a) (π⁻¹ b) * ε (π⁻¹ b) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  have hMQ : ∀ s, (M * signedPerm π⁻¹ (fun s => ε (π⁻¹ s))) s b =
      M s (π⁻¹ b) * ε (π⁻¹ b) := by
    intro s
    rw [Matrix.mul_apply, Finset.sum_eq_single (π⁻¹ b)]
    · rw [signedPerm_apply, if_pos rfl]
    · intro t _ ht
      have hne : ¬ (t = π⁻¹ b) := ht
      rw [signedPerm_apply, if_neg hne]
      simp
    · simp
  simp only [hMQ]
  rw [Finset.sum_eq_single (π⁻¹ a)]
  · rw [signedPerm_apply]
    rw [show π (π⁻¹ a) = a from Equiv.apply_symm_apply π a, if_pos rfl, mul_assoc]
  · intro s _ hs
    have hne : ¬ (a = π s) := fun h => hs (by rw [h]; exact (Equiv.symm_apply_apply π s).symm)
    rw [signedPerm_apply, if_neg hne]
    simp
  · simp

open CFSG.LieType.Universal.SpecialLinear in
theorem signedPerm_mul_inv {n : ℕ} {R : Type*} [Field R]
    (π : Equiv.Perm (Fin n)) (ε : Fin n → R) (hε : ∀ i, ε i * ε i = 1) :
    signedPerm π ε * signedPerm π⁻¹ (fun s => ε (π⁻¹ s)) = 1 := by
  rw [signedPerm_mul_signedPerm]
  rw [show π * π⁻¹ = (1 : Equiv.Perm (Fin n)) by simp, signedPerm_one]
  rw [show (fun s => ε (π⁻¹ s) * ε (π⁻¹ s)) = fun _ => (1 : R) by
    funext s
    exact hε _]
  exact Matrix.diagonal_one

open CFSG.LieType.Universal.SpecialLinear in
theorem inv_coe_signedPerm {n : ℕ} {R : Type*} [Field R]
    {g : SpecialLinearGroup (Fin n) R} {π : Equiv.Perm (Fin n)} {ε : Fin n → R}
    (hg : (g : Matrix (Fin n) (Fin n) R) = signedPerm π ε)
    (hε : ∀ i, ε i * ε i = 1) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      signedPerm π⁻¹ (fun s => ε (π⁻¹ s)) := by
  have hprod := signedPerm_mul_inv π ε hε
  have hPdet : (signedPerm π ε).det = 1 := by rw [← hg]; exact g.2
  have hQdet : (signedPerm π⁻¹ (fun s => ε (π⁻¹ s))).det = 1 := by
    have h := congrArg Matrix.det hprod
    rw [Matrix.det_mul, hPdet, Matrix.det_one, one_mul] at h
    exact h
  let g' : SpecialLinearGroup (Fin n) R :=
    ⟨signedPerm π⁻¹ (fun s => ε (π⁻¹ s)), hQdet⟩
  have hmul : g * g' = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hg]
    exact hprod
  rw [← eq_inv_of_mul_eq_one_right hmul]

section FiniteField

variable [Finite F]

theorem posUnipotent_eq_unitriangular :
    posUnipotent (rootDatum m F) = unitriangular (m + 1) F := by
  ext x
  rw [mem_posUnipotent_iff, mem_unitriangular, UpperT]

@[expose] noncomputable def posUnipotentEquiv :
    ↥(posUnipotent (rootDatum m F)) ≃ (UpperPair m → F) where
  toFun u := fun p => (u.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) p.1.1 p.1.2
  invFun f :=
    ⟨(((unitriangularEquiv (m + 1) (K := F)).symm f :
        ↥(unitriangular (m + 1) F)) : SpecialLinearGroup (Fin (m + 1)) F),
      by
        rw [posUnipotent_eq_unitriangular]
        exact ((unitriangularEquiv (m + 1) (K := F)).symm f).2⟩
  left_inv u := by
    have hu : (u.1 : SpecialLinearGroup (Fin (m + 1)) F) ∈ unitriangular (m + 1) F := by
      rw [← posUnipotent_eq_unitriangular]
      exact u.2
    exact Subtype.ext
      (congrArg (fun x : ↥(unitriangular (m + 1) F) =>
        (x : SpecialLinearGroup (Fin (m + 1)) F))
        ((unitriangularEquiv (m + 1) (K := F)).left_inv ⟨u.1, hu⟩))
  right_inv f := (unitriangularEquiv (m + 1) (K := F)).right_inv f

omit [Finite F] in
theorem conj_signedPerm_coe {π : Equiv.Perm (Fin (m + 1))} {ε : Fin (m + 1) → F}
    {g : SpecialLinearGroup (Fin (m + 1)) F}
    (hg : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = signedPerm π ε)
    (hε : ∀ i, ε i * ε i = 1) (u : SpecialLinearGroup (Fin (m + 1)) F)
    (a b : Fin (m + 1)) :
    ((g * u * g⁻¹ : SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b =
      ε (π⁻¹ a) * (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (π⁻¹ a) (π⁻¹ b) *
        ε (π⁻¹ b) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg,
    inv_coe_signedPerm hg hε, signedPerm_conj_apply]

theorem conj_mem_posUnipotent_iff {π : Equiv.Perm (Fin (m + 1))} {ε : Fin (m + 1) → F}
    {g : SpecialLinearGroup (Fin (m + 1)) F}
    (hg : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = signedPerm π ε)
    (hε : ∀ i, ε i * ε i = 1) {u : SpecialLinearGroup (Fin (m + 1)) F}
    (hu : u ∈ posUnipotent (rootDatum m F)) :
    g * u * g⁻¹ ∈ posUnipotent (rootDatum m F) ↔
      ∀ p : UpperPair m, π p.1.1 > π p.1.2 →
        (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) p.1.1 p.1.2 = 0 := by
  rw [mem_posUnipotent_iff]
  constructor
  · rintro ⟨hUT, -⟩ p hp
    have hzero : ((g * u * g⁻¹ : SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) (π p.1.1) (π p.1.2) = 0 :=
      hUT (π p.1.1) (π p.1.2) hp
    rw [conj_signedPerm_coe m F hg hε] at hzero
    rw [show π⁻¹ (π p.1.1) = p.1.1 from Equiv.symm_apply_apply π p.1.1,
      show π⁻¹ (π p.1.2) = p.1.2 from Equiv.symm_apply_apply π p.1.2] at hzero
    have h1 : ε p.1.1 ≠ 0 := by
      intro h
      have := hε p.1.1
      rw [h, zero_mul] at this
      exact zero_ne_one this
    have h2 : ε p.1.2 ≠ 0 := by
      intro h
      have := hε p.1.2
      rw [h, zero_mul] at this
      exact zero_ne_one this
    have hEq : ε p.1.1 * ((u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) p.1.1 p.1.2 *
        ε p.1.2) = 0 := by
      rwa [mul_assoc] at hzero
    have h1' : ((u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) p.1.1 p.1.2 * ε p.1.2) = 0 :=
      (mul_eq_zero.mp hEq).resolve_left h1
    exact (mul_eq_zero.mp h1').resolve_right h2
  · rintro h
    have huU : UpperT (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
        ∀ i, (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i = 1 :=
      (mem_posUnipotent_iff (m := m) (F := F)).mp hu
    refine ⟨fun a b hba => ?_, fun a => ?_⟩
    · rw [conj_signedPerm_coe m F hg hε]
      rcases lt_trichotomy (π⁻¹ a) (π⁻¹ b) with hlt | heq | hgt
      · have hpi : π (π⁻¹ a) > π (π⁻¹ b) := by
          have ha : π (π⁻¹ a) = a := Equiv.apply_symm_apply π a
          have hb : π (π⁻¹ b) = b := Equiv.apply_symm_apply π b
          rw [ha, hb]
          exact hba
        have hz := h ⟨(π⁻¹ a, π⁻¹ b), hlt⟩ hpi
        rw [hz, mul_zero, zero_mul]
      · exfalso
        have hab : a = b := by
          simpa using congrArg π heq
        exact (ne_of_gt hba) hab
      · have hz := huU.1 (π⁻¹ a) (π⁻¹ b) hgt
        rw [hz, mul_zero, zero_mul]
    · rw [conj_signedPerm_coe m F hg hε, huU.2 (π⁻¹ a)]
      simpa using hε (π⁻¹ a)

omit [Finite F] in
theorem mem_map_conj_inv_iff {g u : SpecialLinearGroup (Fin (m + 1)) F} :
    u ∈ (posUnipotent (rootDatum m F)).map (MulAut.conj g⁻¹).toMonoidHom ↔
      g * u * g⁻¹ ∈ posUnipotent (rootDatum m F) := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, h⟩
    have h' : u = g⁻¹ * y * g := by
      simpa [MulAut.conj_apply] using h.symm
    rw [h']
    have : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [this]
  · intro hu
    refine ⟨g * u * g⁻¹, hu, ?_⟩
    change g⁻¹ * (g * u * g⁻¹) * (g⁻¹)⁻¹ = u
    group

theorem mem_inf_conj_inv_iff {π : Equiv.Perm (Fin (m + 1))} {ε : Fin (m + 1) → F}
    {g : SpecialLinearGroup (Fin (m + 1)) F}
    (hg : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = signedPerm π ε)
    (hε : ∀ i, ε i * ε i = 1) {u : SpecialLinearGroup (Fin (m + 1)) F} :
    u ∈ posUnipotent (rootDatum m F) ⊓
        (posUnipotent (rootDatum m F)).map (MulAut.conj g⁻¹).toMonoidHom ↔
      u ∈ posUnipotent (rootDatum m F) ∧
        ∀ p : UpperPair m, π p.1.1 > π p.1.2 →
          (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) p.1.1 p.1.2 = 0 := by
  rw [Subgroup.mem_inf, mem_map_conj_inv_iff]
  constructor
  · rintro ⟨hu, hconj⟩
    exact ⟨hu, (conj_mem_posUnipotent_iff m F hg hε hu).mp hconj⟩
  · rintro ⟨hu, hz⟩
    exact ⟨hu, (conj_mem_posUnipotent_iff m F hg hε hu).mpr hz⟩

theorem card_inversionSet_eq_inversionCount (π : Equiv.Perm (Fin (m + 1))) :
    Nat.card {p : UpperPair m // π p.1.1 > π p.1.2} = inversionCount π := by
  classical
  let e : {p : UpperPair m // π p.1.1 > π p.1.2} ≃
      {q : Fin (m + 1) × Fin (m + 1) // q.1 < q.2 ∧ π q.2 < π q.1} :=
    { toFun := fun x => by
        rcases x with ⟨p, hp⟩
        rcases p with ⟨⟨i, j⟩, hij⟩
        exact ⟨(i, j), ⟨hij, hp⟩⟩
      invFun := fun y => by
        rcases y with ⟨⟨i, j⟩, hy⟩
        exact ⟨⟨(i, j), hy.1⟩, hy.2⟩
      left_inv := fun x => by
        rcases x with ⟨p, hp⟩
        rcases p with ⟨⟨i, j⟩, hij⟩
        rfl
      right_inv := fun y => by
        rcases y with ⟨⟨i, j⟩, hy⟩
        rfl }
  rw [inversionCount, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [Finite F] in
theorem mem_map_conj_iff {g u : SpecialLinearGroup (Fin (m + 1)) F} :
    u ∈ (posUnipotent (rootDatum m F)).map (MulAut.conj g).toMonoidHom ↔
      g⁻¹ * u * g ∈ posUnipotent (rootDatum m F) := by
  have h := mem_map_conj_inv_iff (m := m) (F := F) (g := g⁻¹) (u := u)
  simpa using h

omit [Finite F] in
theorem card_conj_inf_eq (g : SpecialLinearGroup (Fin (m + 1)) F) :
    Nat.card ↥(posUnipotent (rootDatum m F) ⊓
        (posUnipotent (rootDatum m F)).map (MulAut.conj g).toMonoidHom) =
      Nat.card ↥(posUnipotent (rootDatum m F) ⊓
        (posUnipotent (rootDatum m F)).map (MulAut.conj g⁻¹).toMonoidHom) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨g⁻¹ * x.1 * g, ?_⟩
      invFun := fun y => ⟨g * y.1 * g⁻¹, ?_⟩
      left_inv := fun x => by
        apply Subtype.ext
        group
      right_inv := fun y => by
        apply Subtype.ext
        group }
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (mem_map_conj_iff (g := g) (u := x.1)).mp x.2.2
    · refine (mem_map_conj_inv_iff (m := m) (F := F) (g := g)
        (u := g⁻¹ * x.1 * g)).mpr ?_
      have h : g * (g⁻¹ * x.1 * g) * g⁻¹ = x.1 := by group
      rw [h]
      exact x.2.1
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (mem_map_conj_inv_iff (m := m) (F := F) (g := g) (u := y.1)).mp y.2.2
    · refine (mem_map_conj_iff (g := g) (u := g * y.1 * g⁻¹)).mpr ?_
      have h : g⁻¹ * (g * y.1 * g⁻¹) * g = y.1 := by group
      rw [h]
      exact y.2.1

omit [Finite F] in
theorem card_zeroOn_inversions (π : Equiv.Perm (Fin (m + 1))) :
    Nat.card {f : UpperPair m → F //
        ∀ p : UpperPair m, π p.1.1 > π p.1.2 → f p = 0} =
      Nat.card F ^ (Nat.card (UpperPair m) -
        Nat.card {p : UpperPair m // π p.1.1 > π p.1.2}) := by
  classical
  let e : {f : UpperPair m → F //
      ∀ p : UpperPair m, π p.1.1 > π p.1.2 → f p = 0} ≃
      ({p : UpperPair m // ¬ (π p.1.1 > π p.1.2)} → F) :=
    { toFun := fun f p => f.1 p.1
      invFun := fun g => ⟨fun p => if h : π p.1.1 > π p.1.2 then 0 else g ⟨p, h⟩,
        fun p hp => by
          change (if h : π p.1.1 > π p.1.2 then 0 else g ⟨p, h⟩) = 0
          rw [dif_pos hp]⟩
      left_inv := fun f => by
        apply Subtype.ext
        funext p
        by_cases hp : π p.1.1 > π p.1.2
        · change (if h : π p.1.1 > π p.1.2 then 0 else f.1 p) = f.1 p
          rw [dif_pos hp]
          exact (f.2 p hp).symm
        · change (if h : π p.1.1 > π p.1.2 then 0 else f.1 p) = f.1 p
          rw [dif_neg hp]
      right_inv := fun g => by
        funext p
        rcases p with ⟨p, hp⟩
        change (if h : π p.1.1 > π p.1.2 then 0 else g ⟨p, h⟩) = g ⟨p, hp⟩
        rw [dif_neg hp] }
  rw [Nat.card_congr e, Nat.card_fun]
  congr 1
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

theorem card_inf_conj_inv {π : Equiv.Perm (Fin (m + 1))} {ε : Fin (m + 1) → F}
    {g : SpecialLinearGroup (Fin (m + 1)) F}
    (hg : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = signedPerm π ε)
    (hε : ∀ i, ε i * ε i = 1) :
    Nat.card ↥(posUnipotent (rootDatum m F) ⊓
        (posUnipotent (rootDatum m F)).map (MulAut.conj g⁻¹).toMonoidHom) =
      Nat.card F ^ (Nat.card (UpperPair m) - inversionCount π) := by
  classical
  let e : ↥(posUnipotent (rootDatum m F) ⊓
      (posUnipotent (rootDatum m F)).map (MulAut.conj g⁻¹).toMonoidHom) ≃
      {f : UpperPair m → F //
        ∀ p : UpperPair m, π p.1.1 > π p.1.2 → f p = 0} :=
    { toFun := fun u =>
        ⟨posUnipotentEquiv m F ⟨u.1, u.2.1⟩, fun p hp =>
          ((mem_inf_conj_inv_iff m F hg hε).mp u.2).2 p hp⟩
      invFun := fun f =>
        ⟨(posUnipotentEquiv m F).symm f.1, by
          refine (mem_inf_conj_inv_iff m F hg hε).mpr ⟨?_, ?_⟩
          · exact ((posUnipotentEquiv m F).symm f.1).2
          · intro p hp
            change posUnipotentEquiv m F ((posUnipotentEquiv m F).symm f.1) p = 0
            have hf := congrFun ((posUnipotentEquiv m F).right_inv f.1) p
            exact hf.trans (f.2 p hp)⟩
      left_inv := fun u => by
        apply Subtype.ext
        exact congrArg (fun x : ↥(posUnipotent (rootDatum m F)) =>
          (x : SpecialLinearGroup (Fin (m + 1)) F))
          ((posUnipotentEquiv m F).left_inv ⟨u.1, u.2.1⟩)
      right_inv := fun f => by
        apply Subtype.ext
        exact (posUnipotentEquiv m F).right_inv f.1 }
  rw [Nat.card_congr e, card_zeroOn_inversions, card_inversionSet_eq_inversionCount]

theorem heckeDeg_nW (w : (coxeterMatrix (isFiniteType_A m)).Group) :
    heckeDeg (posUnipotent (rootDatum m F)) (weylNW m F w) =
      Nat.card F ^ (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.length w := by
  classical
  let U := posUnipotent (rootDatum m F)
  let g := weylNW m F w
  let π : Equiv.Perm (Fin (m + 1)) := (typeAWeylEquiv m).symm w
  let q := Nat.card F
  let N := Nat.card (UpperPair m)
  let inv := inversionCount π
  obtain ⟨ε, hε, hg⟩ := nW_matrix_signedPerm m F w
  have hg' : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = signedPerm π ε := by
    simpa [g, π] using hg
  have hcardU : Nat.card U = q ^ N := by
    simpa [U, q, N] using card_posUnipotent (m := m) F
  have hcardInter : Nat.card ↥((U.map (MulAut.conj g).toMonoidHom) ⊓ U) = q ^ (N - inv) := by
    rw [inf_comm]
    rw [card_conj_inf_eq (m := m) (F := F) (g := g)]
    simpa [q, N, inv, π] using card_inf_conj_inv (m := m) (F := F) hg' hε
  have hinv_le : inv ≤ N := by
    rw [show inv = inversionCount π from rfl, ← card_inversionSet_eq_inversionCount]
    exact Nat.card_le_card_of_injective Subtype.val (fun _ _ h => Subtype.ext h)
  have hrel := Subgroup.relIndex_mul_card
    (H := U.map (MulAut.conj g).toMonoidHom) (K := U)
  have hmain : heckeDeg U g * q ^ (N - inv) = q ^ N := by
    calc
      heckeDeg U g * q ^ (N - inv)
          = (U.map (MulAut.conj g).toMonoidHom).relIndex U * q ^ (N - inv) := rfl
      _ = (U.map (MulAut.conj g).toMonoidHom).relIndex U *
            Nat.card ↥((U.map (MulAut.conj g).toMonoidHom) ⊓ U) := by rw [hcardInter]
      _ = Nat.card U := hrel
      _ = q ^ N := hcardU
  have hN : q ^ N = q ^ inv * q ^ (N - inv) := by
    conv_lhs => rw [← Nat.add_sub_of_le hinv_le]
    rw [pow_add]
  have hc : 0 < q ^ (N - inv) := pow_pos (Nat.card_pos) _
  have heq : heckeDeg U g * q ^ (N - inv) = q ^ inv * q ^ (N - inv) := by
    rw [hmain, hN]
  have hdeg : heckeDeg U g = q ^ inv := Nat.eq_of_mul_eq_mul_right hc heq
  have hlen : (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.length w = inv := by
    simpa [inv, π] using length_eq_inversionCount (m := m) w
  show heckeDeg U g = Nat.card F ^
    (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.length w
  rw [hlen]
  simpa [q] using hdeg

omit [Finite F] in
theorem nW_simple (s : Fin m) :
    weylNW m F ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple s) = weylN m F s := by
  rw [weylNW, weylN]
  exact nrep_simple (D := rootDatum m F) (n := weylRep m F) (H := torus m F)
    (isCTGroupDatum m F) s

theorem heckeDeg_mul (w : (coxeterMatrix (isFiniteType_A m)).Group) (s : Fin m)
    (h : (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.length
        ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple s * w) =
      (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.length w + 1) :
    heckeDeg (posUnipotent (rootDatum m F)) (weylN m F s) *
        heckeDeg (posUnipotent (rootDatum m F)) (weylNW m F w) =
      heckeDeg (posUnipotent (rootDatum m F))
        (weylNW m F ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple s * w)) := by
  classical
  rw [← nW_simple (m := m) (F := F) s]
  rw [heckeDeg_nW, heckeDeg_nW, heckeDeg_nW, h,
    (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.length_simple]
  rw [pow_one, pow_succ]
  ring

end FiniteField

end CFSG.LieType.SpecialLinear



