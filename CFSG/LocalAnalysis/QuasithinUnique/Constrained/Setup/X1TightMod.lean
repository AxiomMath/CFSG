module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Fix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TightCoord

public section

namespace CFSG.QuasithinUnique.Setup.X1.Tight

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1

section Dd

variable {W : Type} [CommGroup W]

@[expose] def dd (x : MulAut W) : W →* W where
  toFun w := x w * w⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem dd_apply (x : MulAut W) (w : W) : dd x w = x w * w⁻¹ := rfl

theorem dd_mem_fix {E : Subgroup (MulAut W)} (hq : IsQuadratic E) {x : MulAut W} (hx : x ∈ E)
    (w : W) : dd x w ∈ fixV E :=
  hq (Subgroup.subset_closure ⟨x, hx, w, rfl⟩)

theorem dd_fix {E : Subgroup (MulAut W)} {x : MulAut W} (hx : x ∈ E) {u : W} (hu : u ∈ fixV E) :
    dd x u = 1 := by
  rw [dd_apply, hu x hx, mul_inv_cancel]

theorem dd_mul {E : Subgroup (MulAut W)} (hq : IsQuadratic E) {x y : MulAut W} (hx : x ∈ E)
    (hy : y ∈ E) (w : W) : dd (x * y) w = dd x w * dd y w := by
  have h : x (y w * w⁻¹) = y w * w⁻¹ := dd_mem_fix hq hy w x hx
  have h2 : x (y w) = (y w * w⁻¹) * x w := by
    calc x (y w) = x ((y w * w⁻¹) * w) := by rw [inv_mul_cancel_right]
      _ = _ := by rw [map_mul, h]
  rw [dd_apply, dd_apply, dd_apply, MulAut.mul_apply, h2]
  simp only [mul_comm, mul_left_comm]

theorem dd_conj (g x : MulAut W) (w : W) : dd (g * x * g⁻¹) w = g (dd x (g⁻¹ w)) := by
  simp [dd_apply, MulAut.mul_apply, map_mul, map_inv]

theorem ker_dd (x : MulAut W) : (dd x).ker = fixV (Subgroup.zpowers x) := by
  ext w
  rw [MonoidHom.mem_ker, mem_fixV_zpowers, dd_apply, mul_inv_eq_one]

theorem card_range_dd [Finite W] (x : MulAut W) :
    Nat.card (dd x).range = (fixV (Subgroup.zpowers x)).index := by
  rw [← ker_dd, Subgroup.index_ker]

theorem fixV_zpowers_eq [Finite W] {E : Subgroup (MulAut W)} {x : MulAut W} (hx : x ∈ E) {n : ℕ}
    (hidx : (fixV E).index = n) (hge : n ≤ (fixV (Subgroup.zpowers x)).index) :
    fixV (Subgroup.zpowers x) = fixV E := by
  have hle : fixV E ≤ fixV (Subgroup.zpowers x) :=
    fixV_anti (by rw [Subgroup.zpowers_le]; exact hx)
  have h1 : (fixV (Subgroup.zpowers x)).index ≤ (fixV E).index := Subgroup.index_antitone hle
  have h2 : (fixV (Subgroup.zpowers x)).index = n := by omega
  have e1 := Subgroup.card_mul_index (fixV E)
  have e2 := Subgroup.card_mul_index (fixV (Subgroup.zpowers x))
  rw [hidx] at e1
  rw [h2] at e2
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at e1; exact absurd e1 (by have := Nat.card_pos (α := W); omega)
    · exact h
  have : Nat.card (fixV (Subgroup.zpowers x)) = Nat.card (fixV E) := by
    have := e1.trans e2.symm
    exact (Nat.eq_of_mul_eq_mul_right hn this).symm
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq this)).symm

end Dd

section Quot

variable {W : Type} [CommGroup W] {E : Subgroup (MulAut W)} (hq : IsQuadratic E)

@[expose] noncomputable def Dq {x : MulAut W} (hx : x ∈ E) : (W ⧸ fixV E) →* fixV E :=
  QuotientGroup.lift (fixV E) ((dd x).codRestrict (fixV E) (dd_mem_fix hq hx))
    (fun _ hu => Subtype.ext (dd_fix hx hu))

theorem Dq_mk {x : MulAut W} (hx : x ∈ E) (w : W) :
    ((Dq hq hx (QuotientGroup.mk w) : fixV E) : W) = dd x w := rfl

theorem Dq_injective {t : MulAut W} (ht : t ∈ E) (hker : fixV (Subgroup.zpowers t) = fixV E) :
    Function.Injective (Dq hq ht) := by
  rw [injective_iff_map_eq_one]
  intro q hq1
  induction q using QuotientGroup.induction_on with
  | H w =>
    have h1 : dd t w = 1 := congrArg Subtype.val hq1
    have h2 : w ∈ fixV (Subgroup.zpowers t) := by rw [← ker_dd]; exact h1
    rw [hker] at h2
    exact (QuotientGroup.eq_one_iff w).2 h2

theorem Dq_bijective {t : MulAut W} (ht : t ∈ E) (hker : fixV (Subgroup.zpowers t) = fixV E)
    (hsurj : ∀ u ∈ fixV E, ∃ w, dd t w = u) : Function.Bijective (Dq hq ht) := by
  refine ⟨Dq_injective hq ht hker, fun u => ?_⟩
  obtain ⟨w, hw⟩ := hsurj u u.2
  exact ⟨QuotientGroup.mk w, Subtype.ext hw⟩

@[expose] noncomputable def Tq {t : MulAut W} (ht : t ∈ E)
    (hker : fixV (Subgroup.zpowers t) = fixV E) (hsurj : ∀ u ∈ fixV E, ∃ w, dd t w = u) :
    (W ⧸ fixV E) ≃* fixV E :=
  MulEquiv.ofBijective (Dq hq ht) (Dq_bijective hq ht hker hsurj)

@[expose] noncomputable def Thq (T : (W ⧸ fixV E) ≃* fixV E) {x : MulAut W} (hx : x ∈ E) :
    (W ⧸ fixV E) →* (W ⧸ fixV E) :=
  T.symm.toMonoidHom.comp (Dq hq hx)

theorem T_Thq (T : (W ⧸ fixV E) ≃* fixV E) {x : MulAut W} (hx : x ∈ E) (q : W ⧸ fixV E) :
    T (Thq hq T hx q) = Dq hq hx q := by
  simp [Thq]

theorem Thq_mul (T : (W ⧸ fixV E) ≃* fixV E) {x y : MulAut W} (hx : x ∈ E) (hy : y ∈ E) :
    Thq hq T (E.mul_mem hx hy) = Thq hq T hx * Thq hq T hy := by
  apply MonoidHom.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H w =>
    simp only [MonoidHom.mul_apply]
    apply T.injective
    rw [map_mul, T_Thq, T_Thq, T_Thq]
    exact Subtype.ext (dd_mul hq hx hy w)

theorem card_range_Thq (T : (W ⧸ fixV E) ≃* fixV E) {x : MulAut W} (hx : x ∈ E) :
    Nat.card (Thq hq T hx).range = Nat.card (dd x).range := by
  have h1 : Set.range (Thq hq T hx) = T.symm '' Set.range (Dq hq hx) := by
    rw [← Set.range_comp]; rfl
  have h2 : Set.range (dd x) = Subtype.val '' Set.range (Dq hq hx) := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨Dq hq hx (QuotientGroup.mk w), ⟨_, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H w => exact ⟨w, rfl⟩
  calc Nat.card (Thq hq T hx).range = (Set.range (Thq hq T hx)).ncard := Nat.card_coe_set_eq _
    _ = (Set.range (Dq hq hx)).ncard := by
        rw [h1]; exact Set.ncard_image_of_injective _ T.symm.injective
    _ = (Set.range (dd x)).ncard := by
        rw [h2]; exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ = Nat.card (dd x).range := (Nat.card_coe_set_eq _).symm

@[expose] noncomputable def actQ (g : MulAut W) (hg : ∀ u ∈ fixV E, g u ∈ fixV E)
    (hg' : ∀ u ∈ fixV E, g⁻¹ u ∈ fixV E) : MulAut (W ⧸ fixV E) :=
  QuotientGroup.congr (fixV E) (fixV E) g (by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hg u hu
    · intro hy
      exact ⟨g⁻¹ y, hg' y hy, MulAut.apply_inv_self W g y⟩)

theorem actQ_mk (g : MulAut W) (hg : ∀ u ∈ fixV E, g u ∈ fixV E)
    (hg' : ∀ u ∈ fixV E, g⁻¹ u ∈ fixV E) (w : W) :
    actQ g hg hg' (QuotientGroup.mk w) = QuotientGroup.mk (g w) := rfl

end Quot

section Conj

variable {W : Type} [CommGroup W] {E : Subgroup (MulAut W)} (hq : IsQuadratic E)

theorem Dq_actQ (g : MulAut W) (hg : ∀ u ∈ fixV E, g u ∈ fixV E)
    (hg' : ∀ u ∈ fixV E, g⁻¹ u ∈ fixV E) {x y : MulAut W} (hx : x ∈ E) (hy : y ∈ E)
    (hgxy : g * x * g⁻¹ = y) (q : W ⧸ fixV E) :
    ((Dq hq hy (actQ g hg hg' q) : fixV E) : W) = g ((Dq hq hx q : fixV E) : W) := by
  induction q using QuotientGroup.induction_on with
  | H w =>
    rw [actQ_mk, Dq_mk, Dq_mk, ← hgxy, dd_conj, MulAut.inv_apply_self W g w]

theorem Thq_actQ (T : (W ⧸ fixV E) ≃* fixV E) (g : MulAut W) (hg : ∀ u ∈ fixV E, g u ∈ fixV E)
    (hg' : ∀ u ∈ fixV E, g⁻¹ u ∈ fixV E)
    (hTg : ∀ q, ((T (actQ g hg hg' q) : fixV E) : W) = g ((T q : fixV E) : W))
    {x y : MulAut W} (hx : x ∈ E) (hy : y ∈ E) (hgxy : g * x * g⁻¹ = y) (q : W ⧸ fixV E) :
    Thq hq T hy (actQ g hg hg' q) = actQ g hg hg' (Thq hq T hx q) := by
  apply T.injective
  apply Subtype.ext
  rw [T_Thq, Dq_actQ hq g hg hg' hx hy hgxy, hTg, T_Thq]

theorem fixV_stable {g : MulAut W} (hg : ∀ x ∈ E, g⁻¹ * x * g ∈ E) {u : W} (hu : u ∈ fixV E) :
    g u ∈ fixV E := by
  intro x hx
  have h2 : g⁻¹ (x (g u)) = u := hu (g⁻¹ * x * g) (hg x hx)
  calc x (g u) = g (g⁻¹ (x (g u))) := (MulAut.apply_inv_self W g _).symm
    _ = g u := by rw [h2]

theorem conj_mem_closure {S : Set (MulAut W)} (g : MulAut W)
    (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ Subgroup.closure S) :
    ∀ x ∈ Subgroup.closure S, g * x * g⁻¹ ∈ Subgroup.closure S := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem actQ_pow_mk (g : MulAut W) (hg : ∀ u ∈ fixV E, g u ∈ fixV E)
    (hg' : ∀ u ∈ fixV E, g⁻¹ u ∈ fixV E) (n : ℕ) (w : W) :
    (actQ g hg hg' ^ n) (QuotientGroup.mk w) = QuotientGroup.mk ((g ^ n) w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, actQ_mk, pow_succ', MulAut.mul_apply]

end Conj

section Main

variable {W : Type} [CommGroup W] [Finite W]

theorem tight_core
    (hW : ∀ w : W, w * w = 1) (E : Subgroup (MulAut W)) (hq : IsQuadratic E)
    (hWcard : Nat.card W = 2 ^ 10) (hidx : (fixV E).index = 2 ^ 5)
    (b : Fin 5 → MulAut W) (hE : E = Subgroup.closure (Set.range b))
    (c d : MulAut W) (hc : ∀ i : Fin 5, c * b i * c⁻¹ = b (i + 1))
    (hd : ∀ i : Fin 5, d * b i * d⁻¹ = b (2 * i))
    (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) (hd4 : d ^ 4 = 1) (hdc : d * c * d⁻¹ = c ^ 2)
    (hct : c * (b 0 * b 1 * b 2 * b 3 * b 4) * c⁻¹ = b 0 * b 1 * b 2 * b 3 * b 4)
    (hdt : d * (b 0 * b 1 * b 2 * b 3 * b 4) * d⁻¹ = b 0 * b 1 * b 2 * b 3 * b 4)
    (ht : 2 ^ 5 ≤ (fixV (Subgroup.zpowers (b 0 * b 1 * b 2 * b 3 * b 4))).index)
    (h0 : 2 ^ 5 ≤ (fixV (Subgroup.zpowers (b 0))).index)
    (h2 : 2 ^ 4 ≤ (fixV (Subgroup.zpowers (b 0 * b 1))).index)
    (h4 : 2 ^ 4 ≤ (fixV (Subgroup.zpowers (b 0 * b 1 * b 2 * b 3))).index) : False := by
  have hbE : ∀ i, b i ∈ E := fun i => by rw [hE]; exact Subgroup.subset_closure ⟨i, rfl⟩
  have h01 : b 0 * b 1 ∈ E := E.mul_mem (hbE 0) (hbE 1)
  have h012 : b 0 * b 1 * b 2 ∈ E := E.mul_mem h01 (hbE 2)
  have h0123 : b 0 * b 1 * b 2 * b 3 ∈ E := E.mul_mem h012 (hbE 3)
  have htE : b 0 * b 1 * b 2 * b 3 * b 4 ∈ E := E.mul_mem h0123 (hbE 4)
  have hU : Nat.card (fixV E) = 2 ^ 5 := by
    have h := Subgroup.card_mul_index (fixV E)
    rw [hidx, hWcard] at h
    have h32 : 0 < 2 ^ 5 := by norm_num
    exact Nat.eq_of_mul_eq_mul_right h32 (by rw [h]; norm_num)
  have hkt : fixV (Subgroup.zpowers (b 0 * b 1 * b 2 * b 3 * b 4)) = fixV E :=
    fixV_zpowers_eq htE hidx ht
  have hsurj : ∀ u ∈ fixV E, ∃ w, dd (b 0 * b 1 * b 2 * b 3 * b 4) w = u := by
    have hR : (dd (b 0 * b 1 * b 2 * b 3 * b 4)).range = fixV E := by
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨w, rfl⟩
        exact dd_mem_fix hq htE w
      · rw [hU, card_range_dd, hkt, hidx]
    intro u hu
    have : u ∈ (dd (b 0 * b 1 * b 2 * b 3 * b 4)).range := by rw [hR]; exact hu
    exact this
  let T := Tq hq htE hkt hsurj
  have hcb' : ∀ i : Fin 5, c⁻¹ * b i * c = b (i - 1) := by
    intro i
    have h := hc (i - 1)
    rw [sub_add_cancel] at h
    rw [← h]
    group
  have hdb' : ∀ i : Fin 5, d⁻¹ * b i * d = b (3 * i) := by
    intro i
    have h := hd (3 * i)
    have e : ∀ j : Fin 5, (2 * (3 * j) : Fin 5) = j := by decide
    rw [e] at h
    rw [← h]
    group
  have hcE : ∀ x ∈ E, c * x * c⁻¹ ∈ E := by
    rw [hE]
    exact conj_mem_closure c (fun s hs => by
      obtain ⟨i, rfl⟩ := hs
      rw [hc i]
      exact Subgroup.subset_closure ⟨i + 1, rfl⟩)
  have hcE' : ∀ x ∈ E, c⁻¹ * x * c ∈ E := by
    rw [hE]
    have := conj_mem_closure (S := Set.range b) c⁻¹ (fun s hs => by
      obtain ⟨i, rfl⟩ := hs
      rw [inv_inv, hcb' i]
      exact Subgroup.subset_closure ⟨i - 1, rfl⟩)
    simpa using this
  have hdE : ∀ x ∈ E, d * x * d⁻¹ ∈ E := by
    rw [hE]
    exact conj_mem_closure d (fun s hs => by
      obtain ⟨i, rfl⟩ := hs
      rw [hd i]
      exact Subgroup.subset_closure ⟨2 * i, rfl⟩)
  have hdE' : ∀ x ∈ E, d⁻¹ * x * d ∈ E := by
    rw [hE]
    have := conj_mem_closure (S := Set.range b) d⁻¹ (fun s hs => by
      obtain ⟨i, rfl⟩ := hs
      rw [inv_inv, hdb' i]
      exact Subgroup.subset_closure ⟨3 * i, rfl⟩)
    simpa using this
  have hcU : ∀ u ∈ fixV E, c u ∈ fixV E := fun u hu => fixV_stable hcE' hu
  have hcU' : ∀ u ∈ fixV E, c⁻¹ u ∈ fixV E := fun u hu =>
    fixV_stable (g := c⁻¹) (fun x hx => by simpa using hcE x hx) hu
  have hdU : ∀ u ∈ fixV E, d u ∈ fixV E := fun u hu => fixV_stable hdE' hu
  have hdU' : ∀ u ∈ fixV E, d⁻¹ u ∈ fixV E := fun u hu =>
    fixV_stable (g := d⁻¹) (fun x hx => by simpa using hdE x hx) hu
  let γ := actQ c hcU hcU'
  let δ := actQ d hdU hdU'
  have hTc : ∀ q, ((T (γ q) : fixV E) : W) = c ((T q : fixV E) : W) := fun q =>
    Dq_actQ hq c hcU hcU' htE htE hct q
  have hTd : ∀ q, ((T (δ q) : fixV E) : W) = d ((T q : fixV E) : W) := fun q =>
    Dq_actQ hq d hdU hdU' htE htE hdt q
  have hγ5 : γ ^ 5 = 1 := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H w => rw [actQ_pow_mk, hc5]; rfl
  have hδ4 : δ ^ 4 = 1 := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H w => rw [actQ_pow_mk, hd4]; rfl
  have hδγ : δ * γ * δ⁻¹ = γ ^ 2 := by
    have h1 : δ * γ = γ ^ 2 * δ := by
      apply MulEquiv.ext
      intro q
      induction q using QuotientGroup.induction_on with
      | H w =>
        have e : d * c = c ^ 2 * d := mul_inv_eq_iff_eq_mul.1 hdc
        show actQ d hdU hdU' (actQ c hcU hcU' (QuotientGroup.mk w)) =
          (actQ c hcU hcU' ^ 2) (actQ d hdU hdU' (QuotientGroup.mk w))
        rw [actQ_mk, actQ_mk, actQ_mk, actQ_pow_mk]
        have e' : d (c w) = (c ^ 2) (d w) := by
          have := congrArg (fun z : MulAut W => z w) e
          simpa [MulAut.mul_apply] using this
        rw [e']
    exact mul_inv_eq_iff_eq_mul.2 h1
  have hγ1 : γ ≠ 1 := by
    intro hγ
    have hfix : ∀ u ∈ fixV E, c u = u := by
      intro u hu
      obtain ⟨q, hq'⟩ := T.surjective ⟨u, hu⟩
      have h1 := hTc q
      rw [hγ] at h1
      have h2 : ((T q : fixV E) : W) = u := by rw [hq']
      have h3 : ((1 : MulAut (W ⧸ fixV E)) q) = q := rfl
      rw [h3, h2] at h1
      exact h1.symm
    have hdiff : ∀ w : W, c w * w⁻¹ ∈ fixV E := by
      intro w
      have h1 : γ (QuotientGroup.mk w) = QuotientGroup.mk w := by rw [hγ]; rfl
      rw [actQ_mk] at h1
      have h2 := (QuotientGroup.eq).1 h1
      have h3 := (fixV E).inv_mem h2
      rw [mul_comm]
      simpa using h3
    have hc2 : c ^ 2 = 1 := by
      apply MulEquiv.ext
      intro w
      set u := c w * w⁻¹ with hu
      have hcw : c w = u * w := by rw [hu, inv_mul_cancel_right]
      have hcu : c u = u := hfix u (hdiff w)
      have huu : u * u = 1 := hW u
      show c (c w) = w
      rw [hcw, map_mul, hcu, hcw, ← mul_assoc, huu, one_mul]
    apply hc1
    calc c = c ^ 5 * ((c ^ 2)⁻¹) ^ 2 := by group
      _ = 1 := by rw [hc5, hc2]; simp
  have hV : ∀ q : W ⧸ fixV E, q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w => rw [← QuotientGroup.mk_mul, hW w, QuotientGroup.mk_one]
  have hcardQ : Nat.card (W ⧸ fixV E) = 32 := by
    rw [← Subgroup.index_eq_card, hidx]; norm_num
  let Θ : Fin 5 → ((W ⧸ fixV E) →* (W ⧸ fixV E)) := fun i => Thq hq T (hbE i)
  have hΘc : ∀ (i : Fin 5) (x : W ⧸ fixV E), Θ (i + 1) x = γ (Θ i (γ⁻¹ x)) := by
    intro i x
    have h := Thq_actQ hq T c hcU hcU' hTc (hbE i) (hbE (i + 1)) (hc i) (γ⁻¹ x)
    have e : actQ c hcU hcU' (γ⁻¹ x) = x := MulAut.apply_inv_self _ γ x
    rw [e] at h
    exact h
  have hk0 : fixV (Subgroup.zpowers (b 0)) = fixV E := fixV_zpowers_eq (hbE 0) hidx h0
  have hinj : Function.Injective (Θ 0) :=
    T.symm.injective.comp (Dq_injective hq (hbE 0) hk0)
  have hΘδ : ∀ x, Θ 0 (δ x) = δ (Θ 0 x) := by
    intro x
    have h := Thq_actQ hq T d hdU hdU' hTd (hbE 0) (hbE 0) (by simpa using hd 0) x
    exact h
  have hΘsum : Θ 0 * Θ 1 * Θ 2 * Θ 3 * Θ 4 = MonoidHom.id (W ⧸ fixV E) := by
    have e : Θ 0 * Θ 1 * Θ 2 * Θ 3 * Θ 4 = Thq hq T htE := by
      show Thq hq T (hbE 0) * Thq hq T (hbE 1) * Thq hq T (hbE 2) * Thq hq T (hbE 3) *
        Thq hq T (hbE 4) = _
      rw [← Thq_mul hq T (hbE 0) (hbE 1), ← Thq_mul hq T h01 (hbE 2),
        ← Thq_mul hq T h012 (hbE 3), ← Thq_mul hq T h0123 (hbE 4)]
    rw [e]
    apply MonoidHom.ext
    intro q
    apply T.injective
    rw [T_Thq]
    rfl
  have hsum : ∀ x, Θ 0 x * Θ 1 x * Θ 2 x * Θ 3 x * Θ 4 x = x := by
    intro x
    have := congrArg (fun f : (W ⧸ fixV E) →* (W ⧸ fixV E) => f x) hΘsum
    simpa using this
  have hr1 : 16 ≤ Nat.card (Θ 0 * Θ 1).range := by
    have e : Θ 0 * Θ 1 = Thq hq T h01 := (Thq_mul hq T (hbE 0) (hbE 1)).symm
    rw [e, card_range_Thq, card_range_dd]
    exact h2
  have hr2 : 16 ≤ Nat.card (Θ 0 * Θ 1 * Θ 2 * Θ 3).range := by
    have e : Θ 0 * Θ 1 * Θ 2 * Θ 3 = Thq hq T h0123 := by
      show Thq hq T (hbE 0) * Thq hq T (hbE 1) * Thq hq T (hbE 2) * Thq hq T (hbE 3) = _
      rw [← Thq_mul hq T (hbE 0) (hbE 1), ← Thq_mul hq T h01 (hbE 2),
        ← Thq_mul hq T h012 (hbE 3)]
    rw [e, card_range_Thq, card_range_dd]
    exact h4
  exact afc2 hV hcardQ γ δ hγ5 hγ1 hδ4 hδγ Θ hΘc hinj hΘδ hsum hr1 hr2

end Main

end CFSG.QuasithinUnique.Setup.X1.Tight
