module

public import CFSG.Certificates.Kernel.LeftOrbSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.OrbGroup

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.ConjOrb
  CFSG.KC.LeftOrb CFSG.KC.BfsPin Subgroup
open CFSG.KLie.CT (fget)

variable {n w : Nat}

theorem prep_eq {P : Nat} {g h : Equiv.Perm (Fin n)} (hg : PRep n w P g) (hh : PRep n w P h) :
    g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem prep_inv {G GI : Nat} {g : Equiv.Perm (Fin n)} (hG : PRep n w G g)
    (h : permOK n w (mask w) (n * w) G GI = true) : PRep n w GI g⁻¹ := by
  intro x
  have h3 := ((permOK_facts h).2.2 (g⁻¹ x) (g⁻¹ x).2).2
  rw [hG (g⁻¹ x)] at h3
  simpa using h3

theorem prep_pconj (hn : n < 2 ^ 32) {G GI T : Nat} {g t : Equiv.Perm (Fin n)}
    (hG : PRep n w G g) (hGI : PRep n w GI g⁻¹) (hT : PRep n w T t) :
    PRep n w (pconj n w (mask w) G GI T) (g * t * g⁻¹) := by
  rw [mul_assoc]
  exact prep_pcomp hn hG (prep_pcomp hn hT hGI)

theorem pkeyK_congr {ps : List Nat} (hps : ∀ p ∈ ps, p < n) {P Q : Nat}
    {σ : Equiv.Perm (Fin n)} (hP : PRep n w P σ) (hQ : PRep n w Q σ) :
    pkeyK n w ps P = pkeyK n w ps Q := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := hps p List.mem_cons_self
    have e : pg w (mask w) P p = pg w (mask w) Q p := (hP ⟨p, hp⟩).trans (hQ ⟨p, hp⟩).symm
    change Nat.add (pg w (mask w) P p) (Nat.mul n (pkeyK n w ps P)) =
      Nat.add (pg w (mask w) Q p) (Nat.mul n (pkeyK n w ps Q))
    rw [e, ih fun q hq => hps q (List.mem_cons_of_mem _ hq)]

theorem tree_reach {ng N r : Nat} {E D : Nat → Nat} (htr : ∀ i < N, treePt ng N r E D i = true)
    {Q : Nat → Prop} (hr : Q r) (hstep : ∀ i < N, Q i → ∀ k < ng, Q (fget (E i) k 20)) :
    ∀ i < N, Q i := by
  have key : ∀ d, ∀ i < N, tDep (D i) = d → Q i := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hi hd
      by_cases hir : i = r
      · rw [hir]
        exact hr
      · obtain ⟨hp, hl, he, hdep⟩ := treePt_spec (htr i hi) hir
        have h := hstep _ hp (ih _ (by omega) _ hp rfl) _ hl
        rwa [he] at h
  exact fun i hi => key _ i hi rfl

theorem conjOrb_reps (hn : n < 2 ^ 32) {ng N r : Nat} {G GI T E D S : Nat → Nat}
    {ps : List Nat} {g : Nat → Equiv.Perm (Fin n)} {t : Equiv.Perm (Fin n)}
    (hh : headK n w ng G GI = true) (hg : ∀ k < ng, PRep n w (G k) (g k))
    (hcl : ∀ i < N, closPt n w ng N G GI T E i = true)
    (htr : ∀ i < N, treePt ng N r E D i = true) (hr : r < N) (ht : PRep n w (T r) t)
    (hps : ∀ p ∈ ps, p < n) (hK : distinctK N (fun i => pkeyK n w ps (T i)) S = true) :
    ∃ c : Nat → Equiv.Perm (Fin n), (∀ i < N, PRep n w (T i) (c i)) ∧
      (∀ i < N, ∃ h ∈ closure (g '' {k | k < ng}), c i = h * t * h⁻¹) ∧
      (∀ i < N, ∀ k < ng, ∃ j < N, g k * c i * (g k)⁻¹ = c j) ∧
      (∀ i < N, ∀ j < N, c i = c j → i = j) := by
  classical
  have hGI : ∀ k < ng, PRep n w (GI k) (g k)⁻¹ :=
    fun k hk => prep_inv (hg k hk) ((headK_spec hh).2 k hk).2.2
  have hstep : ∀ i < N, ∀ σ, PRep n w (T i) σ → ∀ k < ng,
      PRep n w (T (fget (E i) k 20)) (g k * σ * (g k)⁻¹) := by
    intro i hi σ hσ k hk
    rw [← ((closPt_spec (hcl i hi)).2 k hk).2]
    exact prep_pconj hn (hg k hk) (hGI k hk) hσ
  have hreach : ∀ i < N, ∃ σ, PRep n w (T i) σ ∧
      ∃ h ∈ closure (g '' {k | k < ng}), σ = h * t * h⁻¹ := by
    refine tree_reach htr ⟨t, ht, 1, one_mem _, by group⟩ ?_
    rintro i hi ⟨σ, hσ, h, hm, rfl⟩ k hk
    exact ⟨_, hstep i hi _ hσ k hk, g k * h, mul_mem (subset_closure ⟨k, hk, rfl⟩) hm, by group⟩
  let c : Nat → Equiv.Perm (Fin n) := fun i =>
    if hx : ∃ σ, PRep n w (T i) σ then hx.choose else 1
  have hc : ∀ i < N, PRep n w (T i) (c i) := fun i hi => by
    obtain ⟨σ, hσ, -⟩ := hreach i hi
    have hx : ∃ σ, PRep n w (T i) σ := ⟨σ, hσ⟩
    simp only [c, dif_pos hx]
    exact hx.choose_spec
  refine ⟨c, hc, fun i hi => ?_, fun i hi k hk => ?_, fun i hi j hj e => ?_⟩
  · obtain ⟨σ, hσ, h, hm, e⟩ := hreach i hi
    exact ⟨h, hm, (prep_eq (hc i hi) hσ).trans e⟩
  · have hj := ((closPt_spec (hcl i hi)).2 k hk).1
    exact ⟨_, hj, prep_eq (hstep i hi _ (hc i hi) k hk) (hc _ hj)⟩
  · have hj' : PRep n w (T j) (c i) := by
      rw [e]
      exact hc j hj
    exact distinctK_inj hK i hi j hj (pkeyK_congr hps (hc i hi) hj')

theorem leftOrb_reps (hn : n < 2 ^ 32) {ng N : Nat} {G T E D S : Nat → Nat} {ps : List Nat}
    {g : Nat → Equiv.Perm (Fin n)} (hg : ∀ k < ng, PRep n w (G k) (g k))
    (hcl : ∀ i < N, closPtL n w ng N G T E i = true)
    (htr : ∀ i < N, treePt ng N 0 E D i = true) (hN : 0 < N) (h0 : PRep n w (T 0) 1)
    (hps : ∀ p ∈ ps, p < n) (hK : distinctK N (fun i => pkeyK n w ps (T i)) S = true) :
    ∃ c : Nat → Equiv.Perm (Fin n), c 0 = 1 ∧ (∀ i < N, PRep n w (T i) (c i)) ∧
      (∀ i < N, c i ∈ closure (g '' {k | k < ng})) ∧
      (∀ i < N, ∀ k < ng, ∃ j < N, g k * c i = c j) ∧
      (∀ i < N, ∀ j < N, c i = c j → i = j) := by
  classical
  have hstep : ∀ i < N, ∀ σ, PRep n w (T i) σ → ∀ k < ng,
      PRep n w (T (fget (E i) k 20)) (g k * σ) := by
    intro i hi σ hσ k hk
    rw [← ((closPtL_spec (hcl i hi)).2 k hk).2]
    exact prep_pcomp hn (hg k hk) hσ
  have hreach : ∀ i < N, ∃ σ, PRep n w (T i) σ ∧ σ ∈ closure (g '' {k | k < ng}) := by
    refine tree_reach htr ⟨1, h0, one_mem _⟩ ?_
    rintro i hi ⟨σ, hσ, hm⟩ k hk
    exact ⟨_, hstep i hi _ hσ k hk, mul_mem (subset_closure ⟨k, hk, rfl⟩) hm⟩
  let c : Nat → Equiv.Perm (Fin n) := fun i =>
    if hx : ∃ σ, PRep n w (T i) σ then hx.choose else 1
  have hc : ∀ i < N, PRep n w (T i) (c i) := fun i hi => by
    obtain ⟨σ, hσ, -⟩ := hreach i hi
    have hx : ∃ σ, PRep n w (T i) σ := ⟨σ, hσ⟩
    simp only [c, dif_pos hx]
    exact hx.choose_spec
  refine ⟨c, prep_eq (hc 0 hN) h0, hc, fun i hi => ?_, fun i hi k hk => ?_,
    fun i hi j hj e => ?_⟩
  · obtain ⟨σ, hσ, hm⟩ := hreach i hi
    rw [prep_eq (hc i hi) hσ]
    exact hm
  · have hj := ((closPtL_spec (hcl i hi)).2 k hk).1
    exact ⟨_, hj, prep_eq (hstep i hi _ (hc i hi) k hk) (hc _ hj)⟩
  · have hj' : PRep n w (T j) (c i) := by
      rw [e]
      exact hc j hj
    exact distinctK_inj hK i hi j hj (pkeyK_congr hps (hc i hi) hj')

section Group

variable {X : Type*} [Group X] [Finite X]

theorem surj_of_mapsTo {T : Set X} (f : X → X) (hf : Function.Injective f)
    (hm : ∀ y ∈ T, f y ∈ T) : ∀ y ∈ T, ∃ z ∈ T, f z = y := by
  intro y hy
  let F : T → T := fun z => ⟨f z, hm z z.2⟩
  have hF : Function.Injective F := fun a b e => Subtype.ext (hf (congrArg Subtype.val e))
  obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.1 hF) ⟨y, hy⟩
  exact ⟨z, z.2, congrArg Subtype.val hz⟩

theorem mem_map_closure (φ : X →* Equiv.Perm (Fin n)) {ng : Nat} (gx : Nat → X)
    {h : Equiv.Perm (Fin n)} (hm : h ∈ closure ((fun k => φ (gx k)) '' {k | k < ng})) :
    ∃ x ∈ closure (gx '' {k | k < ng}), φ x = h := by
  have e : closure ((fun k => φ (gx k)) '' {k | k < ng}) =
      (closure (gx '' {k | k < ng})).map φ := by
    rw [MonoidHom.map_closure, Set.image_image]
  rw [e] at hm
  exact hm

theorem ncard_of_reps (φ : X →* Equiv.Perm (Fin n)) (hφ : Function.Injective φ) {N : Nat}
    (c : Nat → Equiv.Perm (Fin n)) (hpre : ∀ i < N, ∃ y, φ y = c i)
    (hinj : ∀ i < N, ∀ j < N, c i = c j → i = j) :
    {y : X | ∃ i < N, c i = φ y}.ncard = N := by
  have himg : φ '' {y : X | ∃ i < N, c i = φ y} = c '' (Finset.range N : Set Nat) := by
    ext z
    constructor
    · rintro ⟨y, ⟨i, hi, e⟩, rfl⟩
      exact ⟨i, by simpa using hi, e⟩
    · rintro ⟨i, hi, rfl⟩
      have hi' : i < N := by simpa using hi
      obtain ⟨y, hy⟩ := hpre i hi'
      exact ⟨y, ⟨i, hi', hy.symm⟩, hy⟩
  have hio : Set.InjOn c (Finset.range N : Set Nat) :=
    fun i hi j hj e => hinj i (by simpa using hi) j (by simpa using hj) e
  rw [← Set.ncard_image_of_injective _ hφ, himg, hio.ncard_image, Set.ncard_coe_finset,
    Finset.card_range]

theorem class_of_reps (φ : X →* Equiv.Perm (Fin n)) (hφ : Function.Injective φ) {ng N : Nat}
    (gx : Nat → X) (hgen : closure (gx '' {k | k < ng}) = ⊤) (r : X)
    (c : Nat → Equiv.Perm (Fin n))
    (hreach : ∀ i < N, ∃ h ∈ closure ((fun k => φ (gx k)) '' {k | k < ng}), c i = h * φ r * h⁻¹)
    (hcl : ∀ i < N, ∀ k < ng, ∃ j < N, φ (gx k) * c i * (φ (gx k))⁻¹ = c j)
    (hroot : ∃ i < N, c i = φ r) (hinj : ∀ i < N, ∀ j < N, c i = c j → i = j) :
    N * Nat.card (centralizer ({r} : Set X)) = Nat.card X ∧
      ∀ y : X, (∃ i < N, c i = φ y) → IsConj r y := by
  classical
  let Tset : Set X := {y | ∃ i < N, c i = φ y}
  have hconj : ∀ y ∈ Tset, IsConj r y := by
    rintro y ⟨i, hi, e⟩
    obtain ⟨h, hm, e2⟩ := hreach i hi
    obtain ⟨x, -, rfl⟩ := mem_map_closure φ gx hm
    refine isConj_iff.2 ⟨x, hφ ?_⟩
    rw [map_mul, map_mul, map_inv, ← e2, e]
  have hmaps : ∀ k < ng, ∀ y ∈ Tset, gx k * y * (gx k)⁻¹ ∈ Tset := by
    rintro k hk y ⟨i, hi, e⟩
    obtain ⟨j, hj, e2⟩ := hcl i hi k hk
    exact ⟨j, hj, by rw [← e2, e, map_mul, map_mul, map_inv]⟩
  have hall : ∀ g : X, ∀ y ∈ Tset, g * y * g⁻¹ ∈ Tset := by
    intro g
    have hg : g ∈ closure (gx '' {k | k < ng}) := by
      rw [hgen]
      exact mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hmaps k hk
    | one =>
      intro y hy
      rw [one_mul, inv_one, mul_one]
      exact hy
    | mul a b _ _ ha hb =>
      intro y hy
      have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      rw [e]
      exact ha _ (hb y hy)
    | inv a _ ha =>
      intro y hy
      obtain ⟨z, hz, e⟩ := surj_of_mapsTo (fun z => a * z * a⁻¹)
        (fun u v e => by simpa using e) ha y hy
      have e2 : a⁻¹ * y * a⁻¹⁻¹ = z := by
        rw [← e]
        group
      rw [e2]
      exact hz
  have hr : r ∈ Tset := by
    obtain ⟨i, hi, e⟩ := hroot
    exact ⟨i, hi, e⟩
  have hset : conjugatesOf r = Tset := by
    ext y
    constructor
    · intro hy
      obtain ⟨g, rfl⟩ := isConj_iff.1 hy
      exact hall g r hr
    · exact hconj y
  have hpre : ∀ i < N, ∃ y, φ y = c i := by
    intro i hi
    obtain ⟨h, hm, e2⟩ := hreach i hi
    obtain ⟨x, -, rfl⟩ := mem_map_closure φ gx hm
    exact ⟨x * r * x⁻¹, by rw [map_mul, map_mul, map_inv, e2]⟩
  have hcard : Tset.ncard = N := ncard_of_reps φ hφ c hpre hinj
  refine ⟨?_, fun y hy => hconj y hy⟩
  rw [← hcard, ← hset, ← Subgroup.index_centralizer_eq_ncard, Subgroup.index_mul_card]

theorem group_of_reps (φ : X →* Equiv.Perm (Fin n)) (hφ : Function.Injective φ) {ng N : Nat}
    (gx : Nat → X) (c : Nat → Equiv.Perm (Fin n)) (h0 : ∃ i < N, c i = 1)
    (hmem : ∀ i < N, c i ∈ closure ((fun k => φ (gx k)) '' {k | k < ng}))
    (hcl : ∀ i < N, ∀ k < ng, ∃ j < N, φ (gx k) * c i = c j)
    (hinj : ∀ i < N, ∀ j < N, c i = c j → i = j) :
    Nat.card (closure (gx '' {k | k < ng})) = N ∧
      ∀ y ∈ closure (gx '' {k | k < ng}), ∃ i < N, c i = φ y := by
  classical
  let H := closure (gx '' {k | k < ng})
  let Hset : Set X := {y | ∃ i < N, c i = φ y}
  have hmaps : ∀ k < ng, ∀ y ∈ Hset, gx k * y ∈ Hset := by
    rintro k hk y ⟨i, hi, e⟩
    obtain ⟨j, hj, e2⟩ := hcl i hi k hk
    exact ⟨j, hj, by rw [← e2, e, map_mul]⟩
  have hall : ∀ g ∈ H, ∀ y ∈ Hset, g * y ∈ Hset := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hmaps k hk
    | one =>
      intro y hy
      rw [one_mul]
      exact hy
    | mul a b _ _ ha hb =>
      intro y hy
      rw [mul_assoc]
      exact ha _ (hb y hy)
    | inv a _ ha =>
      intro y hy
      obtain ⟨z, hz, e⟩ := surj_of_mapsTo (fun z => a * z) (fun u v e => by simpa using e) ha y hy
      have e2 : a⁻¹ * y = z := by
        rw [← e]
        group
      rw [e2]
      exact hz
  have h1 : (1 : X) ∈ Hset := by
    obtain ⟨i, hi, e⟩ := h0
    exact ⟨i, hi, by rw [e, map_one]⟩
  have hset : (H : Set X) = Hset := by
    ext y
    constructor
    · intro hy
      have := hall y hy 1 h1
      rwa [mul_one] at this
    · rintro ⟨i, hi, e⟩
      obtain ⟨x, hx, ex⟩ := mem_map_closure φ gx (hmem i hi)
      rw [← hφ (ex.trans e)]
      exact hx
  have hpre : ∀ i < N, ∃ y, φ y = c i := by
    intro i hi
    obtain ⟨x, -, ex⟩ := mem_map_closure φ gx (hmem i hi)
    exact ⟨x, ex⟩
  refine ⟨?_, fun y hy => ?_⟩
  · have e : Nat.card H = (H : Set X).ncard := Nat.card_coe_set_eq _
    rw [e, hset]
    exact ncard_of_reps φ hφ c hpre hinj
  · have : y ∈ Hset := by
      rw [← hset]
      exact hy
    exact this

theorem card_centralizer_of_isConj {a b : X} (h : IsConj a b) :
    Nat.card (centralizer ({a} : Set X)) = Nat.card (centralizer ({b} : Set X)) := by
  have ha := Subgroup.index_mul_card (centralizer ({a} : Set X))
  have hb := Subgroup.index_mul_card (centralizer ({b} : Set X))
  have e : (centralizer ({a} : Set X)).index = (centralizer ({b} : Set X)).index := by
    rw [Subgroup.index_centralizer_eq_ncard, Subgroup.index_centralizer_eq_ncard,
      h.conjugatesOf_eq]
  have hpos : 0 < (centralizer ({b} : Set X)).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [e] at ha
  exact Nat.eq_of_mul_eq_mul_left hpos (ha.trans hb.symm)

theorem exists_conj_mem_of_card {p : Nat} [Fact p.Prime] (S : Subgroup X)
    (hS : Nat.card S = p ^ (Nat.card X).factorization p) {x : X}
    (hx : IsPGroup p (zpowers x)) : ∃ g : X, g⁻¹ * x * g ∈ S := by
  obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (Sylow.ofCard S hS) Q
  have hxQ : x ∈ (Q : Subgroup X) := hQ (mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Sylow.coe_ofCard] at hxQ
  refine ⟨g, ?_⟩
  have e : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
  rw [← e]
  exact hxQ

end Group

end CFSG.KC.OrbGroup

end
