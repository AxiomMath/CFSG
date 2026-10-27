module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutRoots
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusBasic
public import CFSG.LieType.Steinberg.PartB
public import CFSG.LieType.TitsSimplicity.Core
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

section TorusAct

variable {K : Type*} [Group K] {F : Type} [Field F] {r : ℕ} {x : (Fin r → ℤ) → F → K}

@[expose] def torusGen (x : (Fin r → ℤ) → F → K) (i : Fin r) (s : Fˣ) : K :=
  weylElement x i s * (weylElement x i 1)⁻¹

@[expose] def TAct (x : (Fin r → ℤ) → F → K) (t : K) (γ : Fin r → ℤ) (l : Fˣ) : Prop :=
  ∀ u : F, t * x γ u * t⁻¹ = x γ ((l : F) * u)

theorem TAct.one (γ : Fin r → ℤ) : TAct x 1 γ 1 := fun u => by simp

theorem TAct.mul {t t' : K} {γ : Fin r → ℤ} {l l' : Fˣ} (h : TAct x t γ l) (h' : TAct x t' γ l') :
    TAct x (t * t') γ (l * l') := fun u => by
  calc t * t' * x γ u * (t * t')⁻¹ = t * (t' * x γ u * t'⁻¹) * t⁻¹ := by group
    _ = x γ ((l : F) * ((l' : F) * u)) := by rw [h' u, h]
    _ = x γ (((l * l' : Fˣ) : F) * u) := by rw [Units.val_mul, mul_assoc]

theorem TAct.inv {t : K} {γ : Fin r → ℤ} {l : Fˣ} (h : TAct x t γ l) : TAct x t⁻¹ γ l⁻¹ :=
  fun u => by
  have h1 := h (((l⁻¹ : Fˣ) : F) * u)
  rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h1
  rw [← h1]
  group

theorem TAct.conj {t h : K} {γ : Fin r → ℤ} {l l' : Fˣ} (hh : TAct x h γ l') (ht : TAct x t γ l) :
    TAct x (h * t * h⁻¹) γ l := fun u => by
  have h1 : ((l' : Fˣ) : F) * ((l'⁻¹ : Fˣ) : F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc h * t * h⁻¹ * x γ u * (h * t * h⁻¹)⁻¹
      = h * (t * (h⁻¹ * x γ u * h⁻¹⁻¹) * t⁻¹) * h⁻¹ := by group
    _ = x γ ((l : F) * u) := by
      rw [hh.inv u, ht, hh]
      congr 1
      calc ((l' : Fˣ) : F) * ((l : F) * (((l'⁻¹ : Fˣ) : F) * u))
          = (l : F) * (((l' : Fˣ) : F) * ((l'⁻¹ : Fˣ) : F)) * u := by ring
        _ = (l : F) * u := by rw [h1, mul_one]

theorem TAct.conj_of_sign {y t : K} {δ δ' : Fin r → ℤ} {l : Fˣ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hy : ∀ c : F, y * x δ c * y⁻¹ = x δ' ((ε : F) * c)) (ht : TAct x t δ l) :
    TAct x (y * t * y⁻¹) δ' l := fun u => by
  have hε2 : (ε : F) * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have h1 : y⁻¹ * x δ' u * y = x δ ((ε : F) * u) := by
    have h2 := hy ((ε : F) * u)
    have h3 : (ε : F) * ((ε : F) * u) = u := by linear_combination u * hε2
    rw [h3] at h2
    rw [← h2]
    group
  calc y * t * y⁻¹ * x δ' u * (y * t * y⁻¹)⁻¹
      = y * (t * (y⁻¹ * x δ' u * y) * t⁻¹) * y⁻¹ := by group
    _ = y * (t * x δ ((ε : F) * u) * t⁻¹) * y⁻¹ := by rw [h1]
    _ = y * x δ ((l : F) * ((ε : F) * u)) * y⁻¹ := by rw [ht]
    _ = x δ' ((ε : F) * ((l : F) * ((ε : F) * u))) := hy _
    _ = x δ' ((l : F) * u) := by
      congr 1
      linear_combination ((l : F) * u) * hε2

theorem TAct.central_mul {z t : K} {γ : Fin r → ℤ} {l : Fˣ} (hz : z ∈ Subgroup.center K)
    (ht : TAct x t γ l) : TAct x (z * t) γ l := fun u => by
  have hz' := Subgroup.mem_center_iff.1 hz
  calc z * t * x γ u * (z * t)⁻¹ = z * (t * x γ u * t⁻¹) * z⁻¹ := by group
    _ = x γ ((l : F) * u) := by
      rw [ht u]
      exact mul_inv_eq_iff_eq_mul.2 (hz' _).symm

theorem TAct.unique {t : K} {γ : Fin r → ℤ} {l l' : Fˣ} (hinj : Function.Injective (x γ))
    (h : TAct x t γ l) (h' : TAct x t γ l') : l = l' := by
  have := (h 1).symm.trans (h' 1)
  have := hinj this
  exact Units.ext (by simpa using this)

end TorusAct

section Act

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem reflection_mem_roots {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (i : Fin D.rank) :
    reflection D.cartan i γ ∈ D.roots := by
  have := weylAction_mem_roots D.isFiniteType
    ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) hγ
  rwa [weylAction_simple] at this

theorem torusGen_act (hE : ChevalleyExtras D F x C O) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (i : Fin D.rank) (s : Fˣ) :
    TAct x (torusGen x i s) γ (s ^ (∑ l, D.cartan i l * γ l)) := by
  have hii : D.cartan i i = 2 := D.isFiniteType.apply_self i
  have hβ₁ : reflection D.cartan i γ ∈ D.roots := reflection_mem_roots hγ i
  have hrefl : reflection D.cartan i (reflection D.cartan i γ) = γ := by
    have := congrArg (fun f : Module.End ℤ (Fin D.rank → ℤ) => f γ) (reflection_mul_self hii)
    simpa using this
  have hpair : ∑ l, D.cartan i l * (reflection D.cartan i γ) l = -∑ l, D.cartan i l * γ l := by
    have := coroot_reflection hii γ
    simpa [coroot_apply] using this
  obtain ⟨ε, hε, hw⟩ := hE.weyl i _ hβ₁
  rw [hrefl, hpair, neg_neg] at hw
  have hε2 : (ε : F) * ε = 1 := by
    rcases hε with rfl | rfl <;> simp
  intro u
  have h1 : weylElement x i 1 * x (reflection D.cartan i γ) ((ε : F) * u) *
      (weylElement x i 1)⁻¹ = x γ u := by
    rw [hw 1 ((ε : F) * u)]
    congr 1
    simp [← mul_assoc, hε2]
  have h2 : (weylElement x i 1)⁻¹ * x γ u * weylElement x i 1 =
      x (reflection D.cartan i γ) ((ε : F) * u) := by
    rw [← h1]; group
  calc torusGen x i s * x γ u * (torusGen x i s)⁻¹ =
      weylElement x i s * ((weylElement x i 1)⁻¹ * x γ u * weylElement x i 1) *
        (weylElement x i s)⁻¹ := by
        simp only [torusGen]; group
    _ = x γ (((s ^ (∑ l, D.cartan i l * γ l) : Fˣ) : F) * u) := by
        rw [h2, hw s]
        congr 1
        linear_combination ((s ^ (∑ l, D.cartan i l * γ l) : Fˣ) : F) * u * hε2

end Act


section Char

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}

theorem pair_single (A : Matrix (Fin r) (Fin r) ℤ) (k j : Fin r) :
    pair A (Pi.single k 1) j = A j k := by
  simp [pair, Pi.single_apply]

theorem pair_neg (A : Matrix (Fin r) (Fin r) ℤ) (γ : Fin r → ℤ) (j : Fin r) :
    pair A (-γ) j = -pair A γ j := by
  simp [pair, Finset.sum_neg_distrib]

theorem pair_sub (A : Matrix (Fin r) (Fin r) ℤ) (γ δ : Fin r → ℤ) (j : Fin r) :
    pair A (γ - δ) j = pair A γ j - pair A δ j := by
  simp [pair, mul_sub, Finset.sum_sub_distrib]

variable {F : Type} [Field F]

@[expose] def charVal (A : Matrix (Fin r) (Fin r) ℤ) (lam : Fin r → Fˣ) (γ : Fin r → ℤ) : Fˣ :=
  ∏ l, lam l ^ pair A γ l

theorem charVal_one (γ : Fin r → ℤ) : charVal A (1 : Fin r → Fˣ) γ = 1 := by
  simp [charVal]

theorem charVal_mul (lam lam' : Fin r → Fˣ) (γ : Fin r → ℤ) :
    charVal A (lam * lam') γ = charVal A lam γ * charVal A lam' γ := by
  simp [charVal, mul_zpow, Finset.prod_mul_distrib]

theorem charVal_mulSingle (j : Fin r) (s : Fˣ) (γ : Fin r → ℤ) :
    charVal A (Pi.mulSingle j s) γ = s ^ pair A γ j := by
  rw [charVal, Finset.prod_eq_single j]
  · simp
  · intro l _ hl
    simp [Pi.mulSingle_eq_of_ne hl]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem charVal_neg (lam : Fin r → Fˣ) (γ : Fin r → ℤ) :
    charVal A lam (-γ) = (charVal A lam γ)⁻¹ := by
  simp [charVal, pair_neg, zpow_neg, Finset.prod_inv_distrib]

end Char

section Torus

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem exists_tact_of_mem_iSup (hE : ChevalleyExtras D F x C O) {H : Fin D.rank → Subgroup K}
    (hH : ∀ i y, y ∈ H i ↔ ∃ s : Fˣ, y = torusGen x i s) {t : K} (ht : t ∈ ⨆ i, H i) :
    ∃ lam : Fin D.rank → Fˣ, ∀ γ ∈ D.roots, TAct x t γ (charVal D.cartan lam γ) := by
  refine Subgroup.iSup_induction H (C := fun t => ∃ lam : Fin D.rank → Fˣ, ∀ γ ∈ D.roots,
    TAct x t γ (charVal D.cartan lam γ)) ht ?_ ?_ ?_
  · intro i y hy
    obtain ⟨s, rfl⟩ := (hH i y).1 hy
    exact ⟨Pi.mulSingle i s, fun γ hγ => by
      rw [charVal_mulSingle]
      exact torusGen_act hE hγ i s⟩
  · exact ⟨1, fun γ _ => by rw [charVal_one]; exact TAct.one γ⟩
  · rintro y z ⟨l, hl⟩ ⟨l', hl'⟩
    exact ⟨l * l', fun γ hγ => by rw [charVal_mul]; exact (hl γ hγ).mul (hl' γ hγ)⟩

@[expose] def SignConj (D : UniversalRootDatum K) (x : (Fin D.rank → ℤ) → F → K) (y : K)
    (w : (coxeterMatrix D.isFiniteType).Group) : Prop :=
  ∀ δ ∈ D.roots, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    ∀ c : F, y * x δ c * y⁻¹ = x (weylAction D.isFiniteType w δ) ((ε : F) * c)

theorem SignConj.one : SignConj D x 1 1 := fun δ _ => ⟨1, Or.inl rfl, fun c => by simp⟩

theorem SignConj.mul {y y' : K} {w w' : (coxeterMatrix D.isFiniteType).Group}
    (h : SignConj D x y w) (h' : SignConj D x y' w') : SignConj D x (y * y') (w * w') :=
  fun δ hδ => by
  obtain ⟨ε', hε', h'c⟩ := h' δ hδ
  obtain ⟨ε, hε, hc⟩ :=
    h (weylAction D.isFiniteType w' δ) (weylAction_mem_roots D.isFiniteType w' hδ)
  refine ⟨ε * ε', ?_, fun c => ?_⟩
  · rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> simp
  · rw [weylAction_mul_apply]
    calc y * y' * x δ c * (y * y')⁻¹ = y * (y' * x δ c * y'⁻¹) * y⁻¹ := by group
      _ = _ := by
        rw [h'c c, hc]
        congr 1
        push_cast
        ring

theorem signConj_n (hE : ChevalleyExtras D F x C O) {n : Fin D.rank → K}
    (hn : ∀ i, n i = weylElement x i 1) (i : Fin D.rank) :
    SignConj D x (n i) ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) := by
  intro δ hδ
  obtain ⟨ε, hε, hw⟩ := hE.weyl i δ hδ
  refine ⟨ε, hε, fun c => ?_⟩
  rw [hn i, weylAction_simple, hw 1 c]
  simp

theorem signConj_list_prod (hE : ChevalleyExtras D F x C O) {n : Fin D.rank → K}
    (hn : ∀ i, n i = weylElement x i 1) (ω : List (Fin D.rank)) :
    SignConj D x (ω.map n).prod
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem.wordProd ω) := by
  induction ω with
  | nil =>
    rw [List.map_nil, List.prod_nil, CoxeterSystem.wordProd_nil]
    exact SignConj.one
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, CoxeterSystem.wordProd_cons]
    exact (signConj_n hE hn i).mul ih

theorem signConj_nrep (hE : ChevalleyExtras D F x C O) {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hn : ∀ i, n i = weylElement x i 1) (w : (coxeterMatrix D.isFiniteType).Group) :
    SignConj D x (nrep hct w) w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_isReduced w
  rw [nrep_wordProd hct hω]
  exact signConj_list_prod hE hn ω

end Torus

section Setup

variable {K : Type*} [Group K] (D : UniversalRootDatum K) {F : Type} [Field F]

structure TorusSetup (x : (Fin D.rank → ℤ) → F → K) (n : Fin D.rank → K)
    (H : Fin D.rank → Subgroup K) : Prop where
  chev : ∃ (C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ)
    (O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)), ChevalleyExtras D F x C O
  ct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem (weylAction D.isFiniteType)
    D.roots D.rootGroup n H
  ext : SteinbergExtras D n H
  bru : BruhatExtras D H
  n_eq : ∀ i, n i = weylElement x i 1
  H_iff : ∀ i y, y ∈ H i ↔ ∃ s : Fˣ, y = torusGen x i s
  hom : ∀ i s s', torusGen x i (s * s') = torusGen x i s * torusGen x i s'
  div : D.divisible = ∅

variable {D} {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

theorem TorusSetup.torusGen_mem (hS : TorusSetup D x n H) (i : Fin D.rank) (s : Fˣ) :
    torusGen x i s ∈ ⨆ i, H i :=
  Subgroup.mem_iSup_of_mem i ((hS.H_iff i _).2 ⟨s, rfl⟩)

theorem TorusSetup.center_le (hS : TorusSetup D x n H) : Subgroup.center K ≤ ⨆ i, H i := by
  intro z hz
  rw [CFSG.LieType.TitsSimplicity.center_eq_normalCore_borel hS.ct hS.ext hS.bru] at hz
  exact CFSG.LieType.TitsSimplicity.normalCore_borel_le_iSup hS.ct hS.bru hz

theorem TorusSetup.hno (hS : TorusSetup D x n H) {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp2 : p ≠ 2) (hlong : ∀ k, IsLongest D.isFiniteType ∅ (Pi.single k 1))
    (hnb : ∀ k, ∃ j, D.cartan j k = -1) :
    ∀ γ ∈ D.roots, ∃ t ∈ ⨆ i, H i, ∀ y ∈ D.rootGroup γ, t * y * t⁻¹ = y → y = 1 := by
  obtain ⟨C, O, hE⟩ := hS.chev
  intro γ hγ
  have hγ' : γ ∈ roots D.isFiniteType ∅ := by rw [← hS.div]; exact hγ
  obtain ⟨j, hj⟩ := exists_odd_pair D.isFiniteType hlong hnb hγ'
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff F p 2).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  refine ⟨torusGen x j (-1), hS.torusGen_mem j (-1), fun y hy hfix => ?_⟩
  obtain ⟨u, rfl⟩ := ((hE.param γ hγ).1 y).1 hy
  have hact := torusGen_act hE hγ j (-1) u
  have hodd : ((-1 : Fˣ) ^ (∑ l, D.cartan j l * γ l)) = -1 :=
    (Int.not_even_iff_odd.1 hj).neg_one_zpow
  rw [hodd] at hact
  have h3 := (hE.param γ hγ).2.2 (hact.symm.trans hfix)
  have h4 : u = 0 := by
    have h5 : 2 * u = 0 := by
      rw [two_mul]
      simp only [Units.val_neg, Units.val_one] at h3
      linear_combination -h3
    exact (mul_eq_zero.1 h5).resolve_left h2
  rw [h4]
  have h6 := (hE.param γ hγ).2.1 0 0
  rw [add_zero] at h6
  exact (mul_left_cancel (a := x γ 0) (by rw [mul_one]; exact h6)).symm

end Setup

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
