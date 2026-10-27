module

public import CFSG.Quasithin.MS93.S32Desc
public import CFSG.Quasithin.MS93.S32Nat

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Quasithin CFSG.Quasithin.MS93.S32 CFSG.Assembly.LowTwoRank
open scoped Matrix

section Abstract

variable {V : Type} [CommGroup V] {F : Type} [Field F]

theorem map_mem_commV_of_mem_centralizer {K : Subgroup (MulAut V)} {p : MulAut V}
    (hp : p ∈ Subgroup.centralizer (K : Set (MulAut V))) {u : V} (hu : u ∈ commV K) :
    p u ∈ commV K := by
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨k, hk, v, rfl⟩ := hw
    have hc : k * p = p * k := Subgroup.mem_centralizer_iff.mp hp k hk
    have h1 : p (k v) = k (p v) := by
      change (p * k) v = (k * p) v
      rw [hc]
    rw [map_mul, map_inv, h1]
    exact Subgroup.subset_closure ⟨k, hk, p v, rfl⟩
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

structure Coord (K : Subgroup (MulAut V)) (π : ↥(StatedSL 3 F) →* ↥K) where
  T : (Fin 3 → F) × (Fin 3 → F) → V
  add : ∀ w w', T (w + w') = T w * T w'
  inj : Function.Injective T
  mem : ∀ w, T w ∈ commV K
  surj : ∀ u ∈ commV K, ∃ w, T w = u
  equiv : ∀ (γ : ↥(StatedSL 3 F)) w,
    T (dg (γ : GL (Fin 3) F) w) = ((π γ : ↥K) : MulAut V) (T w)

variable {K P : Subgroup (MulAut V)} {π : ↥(StatedSL 3 F) →* ↥K}

namespace Coord

variable (c : Coord K π)

@[expose] def Rep (p : MulAut V) (a b d e : F) : Prop :=
  ∀ w, c.T (blockSmul a b d e w) = p (c.T w)

theorem rep_unique {p : MulAut V} {a b d e a' b' d' e' : F} (h : c.Rep p a b d e)
    (h' : c.Rep p a' b' d' e') : a = a' ∧ b = b' ∧ d = d' ∧ e = e' := by
  have key : ∀ w, blockSmul a b d e w = blockSmul a' b' d' e' w := fun w =>
    c.inj ((h w).trans (h' w).symm)
  have h1 := key (fun _ => 1, 0)
  have h2 := key (0, fun _ => 1)
  simp only [blockSmul, smul_zero, add_zero, zero_add, Prod.mk.injEq] at h1 h2
  have p1 := congrFun h1.1 0
  have p2 := congrFun h1.2 0
  have p3 := congrFun h2.1 0
  have p4 := congrFun h2.2 0
  simp at p1 p2 p3 p4
  exact ⟨p1, p3, p2, p4⟩

theorem rep_one : c.Rep 1 1 0 0 1 := fun w => by
  have : blockSmul (1 : F) 0 0 1 w = w := by simp [blockSmul]
  rw [this]; rfl

theorem rep_mul {p q : MulAut V} {a b d e a' b' d' e' : F} (h : c.Rep p a b d e)
    (h' : c.Rep q a' b' d' e') :
    c.Rep (p * q) (a * a' + b * d') (a * b' + b * e') (d * a' + e * d') (d * b' + e * e') :=
  fun w => by
  have : blockSmul a b d e (blockSmul a' b' d' e' w) =
      blockSmul (a * a' + b * d') (a * b' + b * e') (d * a' + e * d') (d * b' + e * e') w := by
    simp only [blockSmul, Prod.mk.injEq, smul_add, smul_smul, add_smul]
    constructor <;> abel
  rw [← this, h, h']
  rfl

theorem exists_rep {p : MulAut V} (hp : p ∈ Subgroup.centralizer (K : Set (MulAut V))) :
    ∃ a b d e : F, c.Rep p a b d e := by
  classical
  have hmem : ∀ w, p (c.T w) ∈ commV K := fun w => map_mem_commV_of_mem_centralizer hp (c.mem w)
  choose D hD using fun w => c.surj _ (hmem w)
  let D' : ((Fin 3 → F) × (Fin 3 → F)) →+ ((Fin 3 → F) × (Fin 3 → F)) :=
    AddMonoidHom.mk' D fun w w' => c.inj (by
      rw [hD, c.add, c.add, hD, hD, map_mul])
  have hcomm : ∀ γ ∈ StatedSL 3 F, ∀ w, D' (dg γ w) = dg γ (D' w) := by
    intro γ hγ w
    apply c.inj
    have e1 := c.equiv ⟨γ, hγ⟩ w
    have e2 := c.equiv ⟨γ, hγ⟩ (D w)
    have hc : ((π ⟨γ, hγ⟩ : ↥K) : MulAut V) * p = p * ((π ⟨γ, hγ⟩ : ↥K) : MulAut V) :=
      Subgroup.mem_centralizer_iff.mp hp _ (π ⟨γ, hγ⟩).2
    have e3 : ((π ⟨γ, hγ⟩ : ↥K) : MulAut V) (p (c.T w)) = p (((π ⟨γ, hγ⟩ : ↥K) : MulAut V)
        (c.T w)) := by
      change (_ * p) _ = (p * _) _
      rw [hc]
    change c.T (D (dg γ w)) = c.T (dg γ (D w))
    rw [hD, e2, hD, e3, ← e1]
  obtain ⟨a, b, d, e, h⟩ := exists_blockSmul_of_commute D' hcomm
  exact ⟨a, b, d, e, fun w => by rw [← h, AddMonoidHom.mk'_apply, hD]⟩

theorem exists_rep_det_one (c : Coord K π)
    (hP : P ≤ Subgroup.centralizer (K : Set (MulAut V))) :
    ∀ x ∈ ⁅P, P⁆, ∃ a b d e : F, c.Rep x a b d e ∧ a * e - b * d = 1 := by
  choose! a b d e hrep using fun (p : MulAut V) (hp : p ∈ P) => c.exists_rep (hP hp)
  let ψ : ↥P →* F :=
    { toFun := fun p => a p * e p - b p * d p
      map_one' := by
        obtain ⟨h1, h2, h3, h4⟩ := c.rep_unique (c.rep_one) (hrep 1 P.one_mem)
        simp [← h1, ← h2, ← h3, ← h4]
      map_mul' := fun p q => by
        have h := c.rep_mul (hrep p p.2) (hrep q q.2)
        obtain ⟨h1, h2, h3, h4⟩ := c.rep_unique (hrep (p * q) (P.mul_mem p.2 q.2)) h
        show a (p * q : P) * e (p * q : P) - b (p * q : P) * d (p * q : P) = _
        simp only [Subgroup.coe_mul]
        rw [h1, h2, h3, h4]
        ring }
  have hker : ⁅P, P⁆ ≤ (MonoidHom.ker ψ.toHomUnits).map P.subtype := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    set g' : ↥P := ⟨g, hg⟩
    set h' : ↥P := ⟨h, hh⟩
    open scoped commutatorElement in
    refine ⟨⁅g', h'⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hker hx
  have hy' : ψ.toHomUnits y = 1 := hy
  have hy'' := congrArg Units.val hy'
  exact ⟨a y, b y, d y, e y, hrep y y.2, hy''⟩

end Coord

theorem commutator_trivial_of_coord (c : Coord K π) (hπ : Function.Surjective π)
    (hP : P ≤ Subgroup.centralizer (K : Set (MulAut V))) :
    ∀ x ∈ ⁅P, P⁆, x ∈ K → ∀ m : ℕ, Odd m → x ^ m = 1 → ∀ u ∈ commV K, x u = u := by
  intro x hx hxK m hm hxm u hu
  obtain ⟨a, b, d, e, hr, hdet⟩ := Coord.exists_rep_det_one c hP x hx
  obtain ⟨γ, hγ⟩ := hπ ⟨x, hxK⟩
  have hγx : ∀ w, c.T (dg (γ : GL (Fin 3) F) w) = x (c.T w) := fun w => by
    rw [c.equiv, hγ]
  have key : ∀ w, blockSmul a b d e w = dg (γ : GL (Fin 3) F) w := fun w =>
    c.inj ((hr w).trans (hγx w).symm)
  have h1 := key (fun _ => 1, 0)
  have h2 := key (0, fun _ => 1)
  simp only [blockSmul, dg, smul_zero, add_zero, zero_add, Matrix.mulVec_zero, Prod.mk.injEq]
    at h1 h2
  have hd : d = 0 := by simpa using congrFun h1.2 0
  have hb : b = 0 := by simpa using congrFun h2.1 0
  have hae : a = e := by
    have p1 := congrFun h1.1 0
    have p2 := congrFun h2.2 0
    simp only [Pi.smul_apply, smul_eq_mul, mul_one] at p1 p2
    exact p1.trans p2.symm
  subst hd hb hae
  have haa : a * a = 1 := by simpa using hdet
  have hpow : ∀ k : ℕ, c.Rep (x ^ k) (a ^ k) 0 0 (a ^ k) := by
    intro k
    induction k with
    | zero => simpa using c.rep_one
    | succ k ih => simpa [pow_succ] using c.rep_mul ih hr
  have hm' : a ^ m = 1 := by
    have h := hpow m
    rw [hxm] at h
    exact (c.rep_unique c.rep_one h).1.symm
  obtain ⟨k, rfl⟩ := hm
  have ha : a = 1 := by
    rw [pow_succ, pow_mul, sq, haa, one_pow, one_mul] at hm'
    exact hm'
  subst ha
  obtain ⟨w, rfl⟩ := c.surj u hu
  rw [← hr w]
  congr 1
  simp [blockSmul]

end Abstract

section Natural

variable {V : Type} [CommGroup V] {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_natEquiv {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {H : Subgroup (MulAut V)}
    {I : Subgroup V} {π : ↥Γ →* ↥H} (h : (FFModel.nat Γ).RealizesVia H I ⊥ π) :
    ∃ e : Multiplicative (ι → F) ≃* ↥I, ∀ (γ : ↥Γ) (x : Multiplicative (ι → F)),
      ((π γ : ↥H) : MulAut V) (e x : V) = (e (Multiplicative.ofAdd
        (((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec
          (Multiplicative.toAdd x))) : V) := by
  obtain ⟨β, hs, hk, he⟩ := natReal_coord h
  have hinj : Function.Injective β := (injective_iff_map_eq_one β).2 fun u hu =>
    Subtype.ext (Subgroup.mem_bot.mp ((hk u).mp hu))
  let eq := MulEquiv.ofBijective β ⟨hinj, hs⟩
  refine ⟨eq.symm, fun γ x => ?_⟩
  have hu : ((π γ : ↥H) : MulAut V) ((eq.symm x : ↥I) : V) ∈ I :=
    h.2.2.2.1 (π γ) _ (eq.symm x).2
  have h1 := he γ (eq.symm x) hu
  have hx : β (eq.symm x) = x := eq.apply_symm_apply x
  rw [hx] at h1
  have h2 := congrArg eq.symm h1
  have h3 : eq.symm (β ⟨((π γ : ↥H) : MulAut V) ((eq.symm x : ↥I) : V), hu⟩) =
      ⟨((π γ : ↥H) : MulAut V) ((eq.symm x : ↥I) : V), hu⟩ := eq.symm_apply_apply _
  rw [h3] at h2
  exact congrArg Subtype.val h2

end Natural

theorem exists_coord_of_two_natural {V : Type} [CommGroup V] {F : Type} [Field F]
    {K : Subgroup (MulAut V)} {π : ↥(StatedSL 3 F) →* ↥K} {I : Fin 2 → Subgroup V}
    (hind : iSupIndep I) (hsup : (⨆ i, I i) = commV K)
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 F)).RealizesVia K (I i) ⊥ π) :
    Nonempty (Coord K π) := by
  obtain ⟨e₀, he₀⟩ := exists_natEquiv (hreal 0)
  obtain ⟨e₁, he₁⟩ := exists_natEquiv (hreal 1)
  have hdisj : Disjoint (I 0) (I 1) := hind.pairwiseDisjoint (by decide)
  have hle : ∀ i, I i ≤ commV K := fun i => hsup ▸ le_iSup I i
  obtain ⟨T, hT⟩ : ∃ T : (Fin 3 → F) × (Fin 3 → F) → V, ∀ w, T w =
      ((e₀ (Multiplicative.ofAdd w.1) : ↥(I 0)) : V) *
        ((e₁ (Multiplicative.ofAdd w.2) : ↥(I 1)) : V) := ⟨_, fun _ => rfl⟩
  have hadd : ∀ w w', T (w + w') = T w * T w' := fun w w' => by
    simp only [hT, Prod.fst_add, Prod.snd_add, ofAdd_add, map_mul, Subgroup.coe_mul]
    exact mul_mul_mul_comm _ _ _ _
  refine ⟨⟨T, hadd, ?_, ?_, ?_, ?_⟩⟩
  · intro w w' h
    rw [hT, hT] at h
    have hm : ((e₀ (Multiplicative.ofAdd w.1) : ↥(I 0)) : V) *
        ((e₀ (Multiplicative.ofAdd w'.1) : ↥(I 0)) : V)⁻¹ = 1 := by
      refine Subgroup.disjoint_def.mp hdisj (Subgroup.mul_mem _ (Subtype.prop _)
        (Subgroup.inv_mem _ (Subtype.prop _))) ?_
      have h2 : ((e₁ (Multiplicative.ofAdd w'.2) : ↥(I 1)) : V) *
          ((e₁ (Multiplicative.ofAdd w.2) : ↥(I 1)) : V)⁻¹ ∈ I 1 :=
        Subgroup.mul_mem _ (Subtype.prop _) (Subgroup.inv_mem _ (Subtype.prop _))
      convert h2 using 1
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
      exact h.trans (mul_comm _ _)
    have h0 := mul_inv_eq_one.mp hm
    rw [h0] at h
    have h1 := mul_left_cancel h
    exact Prod.ext (Multiplicative.ofAdd.injective (e₀.injective (Subtype.ext h0)))
      (Multiplicative.ofAdd.injective (e₁.injective (Subtype.ext h1)))
  · intro w
    rw [hT]
    exact Subgroup.mul_mem _ (hle 0 (Subtype.prop _)) (hle 1 (Subtype.prop _))
  · intro u hu
    rw [← hsup] at hu
    refine Subgroup.iSup_induction I (C := fun u => ∃ w, T w = u) hu ?_ ?_ ?_
    · intro i x hx
      fin_cases i
      · refine ⟨(Multiplicative.toAdd (e₀.symm ⟨x, hx⟩), 0), ?_⟩
        simp [hT]
      · refine ⟨(0, Multiplicative.toAdd (e₁.symm ⟨x, hx⟩)), ?_⟩
        simp [hT]
    · exact ⟨0, by simp [hT]⟩
    · rintro x y ⟨w, rfl⟩ ⟨w', rfl⟩
      exact ⟨w + w', hadd w w'⟩
  · intro γ w
    simp only [hT, map_mul, he₀, he₁, toAdd_ofAdd, dg_fst, dg_snd]

variable {V : Type} [CommGroup V]

theorem commutator_trivial_of_case1ii {K P : Subgroup (MulAut V)}
    (hii : ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      ∃ (I : Fin 2 → Subgroup V) (π : ↥(StatedSL 3 F) →* ↥K), iSupIndep I ∧
        (⨆ i, I i) = commV K ∧ ∀ i, (FFModel.nat (StatedSL 3 F)).RealizesVia K (I i) ⊥ π)
    (hP : P ≤ Subgroup.centralizer (K : Set (MulAut V))) :
    ∀ x ∈ ⁅P, P⁆, x ∈ K → ∀ m : ℕ, Odd m → x ^ m = 1 → ∀ u ∈ commV K, x u = u := by
  obtain ⟨_, F, _, _, -, I, π, hind, hsup, hreal⟩ := hii
  obtain ⟨c⟩ := exists_coord_of_two_natural hind hsup hreal
  exact commutator_trivial_of_coord c (hreal 0).1 hP

end CFSG.HardMathSupport.Curtis.Coordinator
