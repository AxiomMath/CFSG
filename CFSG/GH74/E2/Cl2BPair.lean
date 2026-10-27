module

public import CFSG.GH74.E2.Cl2Quot
public import CFSG.GH74.E2.Cl2Rank

public section

namespace CFSG.GH74.E2

open Subgroup

variable {Q : Type*} [Group Q]

@[expose] def commSub (a b : MulAut Q) : Subgroup Q :=
  Subgroup.closure {w | ∃ z ∈ fixSub a, w = z⁻¹ * b z}

private theorem vlevel {V : Type*} [Group V] [Finite V] (h2 : ∀ x : V, x * x = 1)
    (hV4 : Nat.card V ≤ 16) {a b : MulAut V} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (hsup : fixSub a ⊔ fixSub b = ⊤) (hinf : fixSub a ⊓ fixSub b = ⊥)
    (hna : fixSub a ≠ ⊤) (hnb : fixSub b ≠ ⊤) :
    Nat.card V = 16 ∧ Nat.card (fixSub a) = 4 ∧ Nat.card (fixSub b) = 4 := by
  classical
  have hi : ∀ z : V, z⁻¹ = z := fun z => inv_eq_of_mul_eq_one_right (h2 z)
  have hc : ∀ x y : V, x * y = y * x := by
    intro x y
    calc x * y = (x * y)⁻¹ := (hi (x * y)).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hi x, hi y]
  have hab' : ∀ x, a (b x) = b (a x) := fun x => by
    have := congrArg (fun f : MulAut V => f x) hab
    simpa [MulAut.mul_apply] using this
  have hcardV : Nat.card V = Nat.card (fixSub a) * Nat.card (fixSub b) := by
    have h := relIndex_sup_of_commute (U := fixSub a) (V := fixSub b) (RU := ⊥) (RV := ⊥)
      (fun u _ v _ => hc u v) bot_le bot_le
      (fun u _ r hr => by rw [Subgroup.mem_bot] at hr ⊢; simp [hr])
      (fun u _ r hr => by rw [Subgroup.mem_bot] at hr ⊢; simp [hr])
      (by rw [hinf]; simp)
    rw [bot_sup_eq, hsup, Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
      Subgroup.relIndex_bot_left, Subgroup.card_top] at h
    exact h
  have hmod : ∀ {c d : MulAut V} (hc3 : c ^ 3 = 1) (hcd : c * d = d * c)
      (hint : fixSub c ⊓ fixSub d = ⊥), Nat.card (fixSub d) ≡ 1 [MOD 3] := by
    intro c d hc3 hcd hint
    have hdc : ∀ x, c (d x) = d (c x) := fun x => by
      have := congrArg (fun f : MulAut V => f x) hcd
      simpa [MulAut.mul_apply] using this
    have h := card_modEq_three_fixed hc3 (fixSub d : Set V) (fun y hy => by
      show d (c y) = c y
      rw [← hdc, show d y = y from hy])
    have hset : {y : V | y ∈ (fixSub d : Set V) ∧ c y = y} = {1} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hy1, hy2⟩
        have : y ∈ fixSub c ⊓ fixSub d := ⟨hy2, hy1⟩
        rw [hint] at this
        simpa using this
      · rintro rfl
        exact ⟨(fixSub d).one_mem, map_one c⟩
    rw [hset] at h
    simpa using h
  have hP2 : IsPGroup 2 V := fun x => ⟨1, by simpa [sq] using h2 x⟩
  have hmodA : Nat.card (fixSub a) ≡ 1 [MOD 3] :=
    hmod hb (by rw [hab]) (by rw [inf_comm, hinf])
  have hmodB : Nat.card (fixSub b) ≡ 1 [MOD 3] := hmod ha hab hinf
  obtain ⟨i, hi'⟩ := (IsPGroup.iff_card).mp (hP2.to_subgroup (fixSub a))
  obtain ⟨j, hj'⟩ := (IsPGroup.iff_card).mp (hP2.to_subgroup (fixSub b))
  have hV : Nat.card V = 2 ^ (i + j) := by rw [hcardV, hi', hj', pow_add]
  have hle : i + j ≤ 4 := by
    have : 2 ^ (i + j) ≤ 2 ^ 4 := by rw [← hV]; simpa using hV4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hnb
    have : fixSub a = ⊥ := by
      rw [Subgroup.eq_bot_iff_card, hi']; simp
    rw [this, bot_sup_eq] at hsup
    exact hsup
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hna
    have : fixSub b = ⊥ := by
      rw [Subgroup.eq_bot_iff_card, hj']; simp
    rw [this, sup_bot_eq] at hsup
    exact hsup
  rw [hi'] at hmodA
  rw [hj'] at hmodB
  have hiEven : i = 2 := by
    have : i ≤ 3 := by omega
    interval_cases i
    · omega
    · exfalso; revert hmodA; decide
    · rfl
    · exfalso; revert hmodA; decide
  have hjEven : j = 2 := by
    have : j ≤ 3 := by omega
    interval_cases j
    · omega
    · exfalso; revert hmodB; decide
    · rfl
    · exfalso; revert hmodB; decide
  subst hiEven hjEven
  refine ⟨?_, ?_, ?_⟩
  · rw [hV]; norm_num
  · rw [hi']; norm_num
  · rw [hj']; norm_num

private theorem vfacts_V {V : Type*} [Group V] [Finite V] (h4 : FourGen V)
    (h2 : ∀ x : V, x * x = 1) (hfr : frattini V = ⊥) {a b : MulAut V} (h : BPair V a b) :
    Nat.card V = 16 ∧ fixSub a ⊓ fixSub b = ⊥ ∧ fixSub a ⊔ fixSub b = ⊤ ∧
      Nat.card (fixSub a) = 4 ∧ Nat.card (fixSub b) = 4 := by
  have hsup : fixSub a ⊔ fixSub b = ⊤ := by
    have := h.sup_top
    simpa [hfr] using this
  have hinf : fixSub a ⊓ fixSub b = ⊥ := by
    have := h.inf_le
    rw [hfr] at this
    simpa using this
  have hna : fixSub a ≠ ⊤ := by
    have := h.a_ne
    simpa [hfr] using this
  have hnb : fixSub b ≠ ⊤ := by
    have := h.b_ne
    simpa [hfr] using this
  have hV4 : Nat.card V ≤ 16 := by
    have := h4.relIndex_le (H := ⊤) (R := ⊥)
      (fun x _ r hr => by rw [Subgroup.mem_bot] at hr ⊢; simp [hr]) (fun x _ => by
        rw [Subgroup.mem_bot]; exact h2 x)
    rwa [Subgroup.relIndex_bot_left, Subgroup.card_top] at this
  obtain ⟨c1, c2, c3⟩ := vlevel h2 hV4 h.a_cube h.b_cube h.comm hsup hinf hna hnb
  exact ⟨c1, hinf, hsup, c2, c3⟩

theorem frattini_inv_iff {g : MulAut Q} (hg : g ^ 3 = 1) (x : Q) :
    g x ∈ frattini Q ↔ x ∈ frattini Q := by
  constructor
  · intro hx
    have h3 : g (g (g x)) = x := by
      have := congrArg (fun f : MulAut Q => f x) hg
      simpa [pow_succ, MulAut.mul_apply] using this
    rw [← h3]
    exact frattini_inv g (frattini_inv g hx)
  · intro hx
    exact frattini_inv g hx

@[expose] noncomputable def aV (a : MulAut Q) (ha : a ^ 3 = 1) : MulAut (Q ⧸ frattini Q) :=
  quotAut a (frattini Q) (frattini_inv_iff ha)

private theorem V_sq [Finite Q] (hQ : IsPGroup 2 Q) (x : Q ⧸ frattini Q) : x * x = 1 := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact mul_self_mem_frattini hQ g

private theorem V_frattini [Finite Q] : frattini (Q ⧸ frattini Q) = ⊥ := by
  rw [frattini_quotient (frattini Q) le_rfl]
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

private theorem vfacts [Finite Q] (hQ : IsPGroup 2 Q) (h4 : FourGen Q) {a b : MulAut Q}
    (h : BPair Q a b) :
    Nat.card (Q ⧸ frattini Q) = 16 ∧ fixSub (aV a h.a_cube) ⊓ fixSub (aV b h.b_cube) = ⊥ ∧
      fixSub (aV a h.a_cube) ⊔ fixSub (aV b h.b_cube) = ⊤ ∧
      Nat.card (fixSub (aV a h.a_cube)) = 4 ∧ Nat.card (fixSub (aV b h.b_cube)) = 4 :=
  vfacts_V (h4.quotient (frattini Q)) (V_sq hQ) V_frattini
    (h.quotient hQ (frattini Q) (frattini_inv_iff h.a_cube) (frattini_inv_iff h.b_cube) le_rfl)

private theorem eps_eq_one {V : Type*} [Group V] (h2 : ∀ x : V, x * x = 1) {a b : MulAut V}
    (ha : a ^ 3 = 1) (hab : a * b = b * a) (hinf : fixSub a ⊓ fixSub b = ⊥) {y : V}
    (hy : y ∈ fixSub b) : eps a y = 1 := by
  have hi : ∀ z : V, z⁻¹ = z := fun z => inv_eq_of_mul_eq_one_right (h2 z)
  have hc : ∀ x y : V, x * y = y * x := by
    intro x y
    calc x * y = (x * y)⁻¹ := (hi (x * y)).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hi x, hi y]
  have h3 : ∀ z, a (a (a z)) = z := fun z => by
    have := congrArg (fun f : MulAut V => f z) ha
    simpa [pow_succ, MulAut.mul_apply] using this
  have hab' : ∀ x, a (b x) = b (a x) := fun x => by
    have := congrArg (fun f : MulAut V => f x) hab
    simpa [MulAut.mul_apply] using this
  have hby : b y = y := hy
  have hfa : a (eps a y) = eps a y := by
    unfold eps
    rw [map_mul, map_mul, h3, hc (a y * a (a y)) y, mul_assoc]
  have e1 : b (a y) = a y := by rw [← hab', hby]
  have e2 : b (a (a y)) = a (a y) := by rw [← hab', ← hab', hby]
  have hfb : b (eps a y) = eps a y := by
    unfold eps
    rw [map_mul, map_mul, hby, e1, e2]
  have : eps a y ∈ fixSub a ⊓ fixSub b := ⟨hfa, hfb⟩
  rw [hinf, Subgroup.mem_bot] at this
  exact this

private theorem mem_fixSub_aV [Finite Q] (hQ : IsPGroup 2 Q) {a : MulAut Q} (ha : a ^ 3 = 1)
    {x : Q} (hx : x ∈ fixSub a) :
    (QuotientGroup.mk x : Q ⧸ frattini Q) ∈ fixSub (aV a ha) := by
  unfold aV
  rw [fixSub_quotAut hQ ha]
  exact ⟨x, hx, rfl⟩

private theorem fixSub_aV_comap [Finite Q] (hQ : IsPGroup 2 Q) {a : MulAut Q} (ha : a ^ 3 = 1) :
    (fixSub (aV a ha)).comap (QuotientGroup.mk' (frattini Q)) = fixSub a ⊔ frattini Q := by
  unfold aV
  rw [fixSub_quotAut hQ ha, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

variable [Finite Q] {a b : MulAut Q}

omit [Finite Q] in
private theorem aV_comm (h : BPair Q a b) :
    aV a h.a_cube * aV b h.b_cube = aV b h.b_cube * aV a h.a_cube := by
  have hab' : ∀ x, a (b x) = b (a x) := fun x => by
    have := congrArg (fun f : MulAut Q => f x) h.comm
    simpa [MulAut.mul_apply] using this
  ext z
  induction z using QuotientGroup.induction_on with
  | H y => simp [aV, quotAut_mk, MulAut.mul_apply, hab']

theorem BPair.index_frattini (hQ : IsPGroup 2 Q) (h4 : FourGen Q) (h : BPair Q a b) :
    (frattini Q).index = 16 := by
  rw [Subgroup.index_eq_card]
  exact (vfacts hQ h4 h).1

theorem BPair.index_fixSub_a (hQ : IsPGroup 2 Q) (h4 : FourGen Q) (h : BPair Q a b) :
    (fixSub a ⊔ frattini Q).index = 4 := by
  obtain ⟨hV, -, -, hA, -⟩ := vfacts hQ h4 h
  rw [← fixSub_aV_comap hQ h.a_cube,
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have := Subgroup.card_mul_index (fixSub (aV a h.a_cube))
  rw [hV, hA] at this
  omega

theorem BPair.index_fixSub_b (hQ : IsPGroup 2 Q) (h4 : FourGen Q) (h : BPair Q a b) :
    (fixSub b ⊔ frattini Q).index = 4 := by
  obtain ⟨hV, -, -, -, hB⟩ := vfacts hQ h4 h
  rw [← fixSub_aV_comap hQ h.b_cube,
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have := Subgroup.card_mul_index (fixSub (aV b h.b_cube))
  rw [hV, hB] at this
  omega

theorem BPair.fix_inf_le (hQ : IsPGroup 2 Q) (h4 : FourGen Q) (h : BPair Q a b) :
    fixSub a ⊓ fixSub b ≤ frattini Q := by
  rintro x ⟨hxa, hxb⟩
  obtain ⟨-, hinf, -, -, -⟩ := vfacts hQ h4 h
  have : (QuotientGroup.mk x : Q ⧸ frattini Q) ∈
      fixSub (aV a h.a_cube) ⊓ fixSub (aV b h.b_cube) :=
    ⟨mem_fixSub_aV hQ h.a_cube hxa, mem_fixSub_aV hQ h.b_cube hxb⟩
  rw [hinf, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff x).mp this

theorem BPair.sup_fix (_hQ : IsPGroup 2 Q) (_h4 : FourGen Q) (h : BPair Q a b) :
    fixSub a ⊔ fixSub b = ⊤ := by
  have hle : (fixSub a ⊔ frattini Q) ⊔ (fixSub b ⊔ frattini Q) ≤
      (fixSub a ⊔ fixSub b) ⊔ frattini Q :=
    sup_le (sup_le_sup_right le_sup_left _) (sup_le_sup_right le_sup_right _)
  have htop : (fixSub a ⊔ fixSub b) ⊔ frattini Q = ⊤ := eq_top_iff.2 (h.sup_top ▸ hle)
  have : IsCoatomic (Subgroup Q) := inferInstance
  exact frattini_nongenerating htop

theorem BPair.eps_a_mem (hQ : IsPGroup 2 Q) (h4 : FourGen Q) (h : BPair Q a b) {x : Q}
    (hx : x ∈ fixSub b) : eps a x ∈ frattini Q := by
  obtain ⟨-, hinf, -, -, -⟩ := vfacts hQ h4 h
  have h1 := eps_eq_one (V_sq hQ) (a := aV a h.a_cube) (b := aV b h.b_cube)
    (quotAut_pow_three a _ _ h.a_cube) (aV_comm h) hinf (y := (QuotientGroup.mk x : Q ⧸ frattini Q))
    (mem_fixSub_aV hQ h.b_cube hx)
  have h2 : eps (aV a h.a_cube) (QuotientGroup.mk x : Q ⧸ frattini Q) =
      ((eps a x : Q) : Q ⧸ frattini Q) := by
    unfold eps
    simp [aV, quotAut_mk]
  rw [h2] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem BPair.eps_b_mem (hQ : IsPGroup 2 Q) (h4 : FourGen Q) (h : BPair Q a b) {x : Q}
    (hx : x ∈ fixSub a) : eps b x ∈ frattini Q := by
  obtain ⟨-, hinf, -, -, -⟩ := vfacts hQ h4 h
  have h1 := eps_eq_one (V_sq hQ) (a := aV b h.b_cube) (b := aV a h.a_cube)
    (quotAut_pow_three b _ _ h.b_cube) (aV_comm h).symm (by rw [inf_comm]; exact hinf)
    (y := (QuotientGroup.mk x : Q ⧸ frattini Q)) (mem_fixSub_aV hQ h.a_cube hx)
  have h2 : eps (aV b h.b_cube) (QuotientGroup.mk x : Q ⧸ frattini Q) =
      ((eps b x : Q) : Q ⧸ frattini Q) := by
    unfold eps
    simp [aV, quotAut_mk]
  rw [h2] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem BPair.mem_frattini_of_fix (hQ : IsPGroup 2 Q) (h4 : FourGen Q) (h : BPair Q a b) {x : Q}
    (hx : x ∈ fixSub b) (hax : x⁻¹ * a x ∈ frattini Q) : x ∈ frattini Q := by
  obtain ⟨-, hinf, -, -, -⟩ := vfacts hQ h4 h
  have hxa : (QuotientGroup.mk x : Q ⧸ frattini Q) ∈ fixSub (aV a h.a_cube) := by
    show aV a h.a_cube (QuotientGroup.mk x) = QuotientGroup.mk x
    unfold aV
    rw [quotAut_mk]
    exact ((QuotientGroup.eq).mpr hax).symm
  have : (QuotientGroup.mk x : Q ⧸ frattini Q) ∈
      fixSub (aV a h.a_cube) ⊓ fixSub (aV b h.b_cube) :=
    ⟨hxa, mem_fixSub_aV hQ h.b_cube hx⟩
  rw [hinf, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff x).mp this

theorem BPair.relIndex_fixSub_b (hQ : IsPGroup 2 Q) (h4 : FourGen Q) (h : BPair Q a b) :
    (fixSub b ⊓ frattini Q).relIndex (fixSub b) = 4 := by
  obtain ⟨-, -, -, -, hB⟩ := vfacts hQ h4 h
  rw [Subgroup.inf_relIndex_left, Subgroup.relIndex]
  let f := (QuotientGroup.mk' (frattini Q)).comp (fixSub b).subtype
  have hker : f.ker = (frattini Q).subgroupOf (fixSub b) := by
    ext x
    simp [f, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : f.range = (fixSub b).map (QuotientGroup.mk' (frattini Q)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hker, Subgroup.index_ker, hrange, ← fixSub_quotAut hQ h.b_cube]
  exact hB

theorem BPair.relIndex_fixSub_a (hQ : IsPGroup 2 Q) (h4 : FourGen Q) (h : BPair Q a b) :
    (fixSub a ⊓ frattini Q).relIndex (fixSub a) = 4 := by
  obtain ⟨-, -, -, hA, -⟩ := vfacts hQ h4 h
  rw [Subgroup.inf_relIndex_left, Subgroup.relIndex]
  let f := (QuotientGroup.mk' (frattini Q)).comp (fixSub a).subtype
  have hker : f.ker = (frattini Q).subgroupOf (fixSub a) := by
    ext x
    simp [f, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : f.range = (fixSub a).map (QuotientGroup.mk' (frattini Q)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hker, Subgroup.index_ker, hrange, ← fixSub_quotAut hQ h.a_cube]
  exact hA

omit [Finite Q] in
theorem commSub_le_fixSub_a (h : BPair Q a b) : commSub a b ≤ fixSub a := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro w ⟨z, hz, rfl⟩
  have hz' : a z = z := hz
  have hab' : a (b z) = b (a z) := by
    have := congrArg (fun f : MulAut Q => f z) h.comm
    simpa [MulAut.mul_apply] using this
  show a (z⁻¹ * b z) = z⁻¹ * b z
  rw [map_mul, map_inv, hz', hab', hz']

omit [Finite Q] in
private theorem closure_pair_eq {V : Type*} [Group V] [Finite V] {a : MulAut V} {U : Subgroup V}
    (hU4 : Nat.card U = 4) (hUinv : ∀ u ∈ U, a u ∈ U) (hfix : ∀ u ∈ U, a u = u → u = 1)
    {v : V} (hv : v ∈ U) (hv1 : v ≠ 1) : Subgroup.closure ({v, a v} : Set V) = U := by
  have hK : Subgroup.closure ({v, a v} : Set V) ≤ U := by
    rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | hw
    · exact hv
    · rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact hUinv v hv
  have hne1 : a v ≠ 1 := fun h => hv1 (by simpa using h)
  have hne2 : a v ≠ v := fun h => hv1 (hfix v hv h)
  set K := Subgroup.closure ({v, a v} : Set V) with hKdef
  have hvK : v ∈ K := Subgroup.subset_closure (by simp)
  have havK : a v ∈ K := Subgroup.subset_closure (by simp)
  have h3 : 3 ≤ Nat.card K := by
    let g : Fin 3 → K := ![1, ⟨v, hvK⟩, ⟨a v, havK⟩]
    have hg : Function.Injective g := by
      intro i j hij
      have hij' := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | (exfalso
           simp [g] at hij'
           first
             | exact absurd hij' hv1
             | exact absurd hij' hv1.symm
             | exact absurd hij' hne1
             | exact absurd hij' hne1.symm
             | exact absurd hij' hne2
             | exact absurd hij' hne2.symm)
    calc 3 = Nat.card (Fin 3) := by simp
      _ ≤ Nat.card K := Nat.card_le_card_of_injective g hg
  have hdvd : Nat.card K ∣ 4 := hU4 ▸ Subgroup.card_dvd_of_le hK
  have hK4 : Nat.card K = 4 := by
    have hle : Nat.card K ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card K = c at *
    interval_cases c
    · exact absurd hdvd (by norm_num)
    · rfl
  exact Subgroup.eq_of_le_of_card_ge hK (by rw [hK4, hU4])

theorem BPair.exists_gens (hQ : IsPGroup 2 Q) (h4 : FourGen Q) (h : BPair Q a b) :
    ∃ x ∈ fixSub b, ∃ y ∈ commSub a b,
      Subgroup.closure ({x, a x, y, b y} : Set Q) = ⊤ := by
  obtain ⟨hV, hinf, hsup, hA, hB⟩ := vfacts hQ h4 h
  have hfa := fixSub_quotAut hQ h.a_cube (frattini Q) (frattini_inv_iff h.a_cube)
  have hfb := fixSub_quotAut hQ h.b_cube (frattini Q) (frattini_inv_iff h.b_cube)
  have hcomm : ∀ z : Q ⧸ frattini Q, aV a h.a_cube (aV b h.b_cube z) =
      aV b h.b_cube (aV a h.a_cube z) := fun z => by
    have := congrArg (fun f : MulAut (Q ⧸ frattini Q) => f z) (aV_comm h)
    simpa [MulAut.mul_apply] using this
  have hBne : fixSub (aV b h.b_cube) ≠ ⊥ := fun h0 => by
    rw [h0] at hB
    simp at hB
  obtain ⟨⟨v, hvB⟩, hv1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hv1 : v ≠ 1 := fun h' => hv1' (Subtype.ext h')
  have hvB' := hvB
  unfold aV at hvB'
  rw [hfb] at hvB'
  obtain ⟨x, hx, rfl⟩ := hvB'
  have hAne : fixSub (aV a h.a_cube) ≠ ⊥ := fun h0 => by
    rw [h0] at hA
    simp at hA
  obtain ⟨⟨w, hwA⟩, hw1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  have hw1 : w ≠ 1 := fun h' => hw1' (Subtype.ext h')
  have hwA' := hwA
  unfold aV at hwA'
  rw [hfa] at hwA'
  obtain ⟨z, hz, rfl⟩ := hwA'
  set y : Q := z⁻¹ * b z with hy
  have hycomm : y ∈ commSub a b := Subgroup.subset_closure ⟨z, hz, rfl⟩
  refine ⟨x, hx, y, hycomm, ?_⟩
  set v : Q ⧸ frattini Q := QuotientGroup.mk' (frattini Q) x with hvdef
  set w : Q ⧸ frattini Q := QuotientGroup.mk' (frattini Q) z with hwdef
  have hav : aV a h.a_cube v = QuotientGroup.mk' (frattini Q) (a x) :=
    quotAut_mk a (frattini Q) (frattini_inv_iff h.a_cube) x
  have hbw : aV b h.b_cube w = QuotientGroup.mk' (frattini Q) (b z) :=
    quotAut_mk b (frattini Q) (frattini_inv_iff h.b_cube) z
  have hyv : QuotientGroup.mk' (frattini Q) y = w⁻¹ * aV b h.b_cube w := by
    rw [hbw, hy, map_mul, map_inv]
  have hbyv : QuotientGroup.mk' (frattini Q) (b y) =
      aV b h.b_cube (w⁻¹ * aV b h.b_cube w) := by
    rw [← hyv]
    exact quotAut_mk b (frattini Q) (frattini_inv_iff h.b_cube) y
  have hUb : Subgroup.closure ({v, aV a h.a_cube v} : Set (Q ⧸ frattini Q)) =
      fixSub (aV b h.b_cube) := by
    refine closure_pair_eq hB (fun u hu => ?_) (fun u hu hau => ?_) hvB hv1
    · show aV b h.b_cube (aV a h.a_cube u) = aV a h.a_cube u
      rw [← hcomm, show aV b h.b_cube u = u from hu]
    · have : u ∈ fixSub (aV a h.a_cube) ⊓ fixSub (aV b h.b_cube) := ⟨hau, hu⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact this
  have hyA : w⁻¹ * aV b h.b_cube w ∈ fixSub (aV a h.a_cube) := by
    refine Subgroup.mul_mem _ (Subgroup.inv_mem _ hwA) ?_
    show aV a h.a_cube (aV b h.b_cube w) = aV b h.b_cube w
    rw [hcomm, show aV a h.a_cube w = w from hwA]
  have hy1 : w⁻¹ * aV b h.b_cube w ≠ 1 := by
    intro h1
    apply hw1
    have hbw' : aV b h.b_cube w = w := by
      have := mul_eq_one_iff_eq_inv.mp h1
      simpa using this.symm
    have : w ∈ fixSub (aV a h.a_cube) ⊓ fixSub (aV b h.b_cube) := ⟨hwA, hbw'⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this
  have hUa : Subgroup.closure ({w⁻¹ * aV b h.b_cube w,
      aV b h.b_cube (w⁻¹ * aV b h.b_cube w)} : Set (Q ⧸ frattini Q)) =
      fixSub (aV a h.a_cube) := by
    refine closure_pair_eq hA (fun u hu => ?_) (fun u hu hbu => ?_) hyA hy1
    · show aV a h.a_cube (aV b h.b_cube u) = aV b h.b_cube u
      rw [hcomm, show aV a h.a_cube u = u from hu]
    · have : u ∈ fixSub (aV a h.a_cube) ⊓ fixSub (aV b h.b_cube) := ⟨hu, hbu⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact this
  set C := Subgroup.closure ({x, a x, y, b y} : Set Q) with hC
  have hmem : ∀ t ∈ ({x, a x, y, b y} : Set Q),
      QuotientGroup.mk' (frattini Q) t ∈ C.map (QuotientGroup.mk' (frattini Q)) :=
    fun t ht => ⟨t, Subgroup.subset_closure ht, rfl⟩
  have hmapTop : C.map (QuotientGroup.mk' (frattini Q)) = ⊤ := by
    rw [eq_top_iff, ← hsup, sup_le_iff]
    constructor
    · rw [← hUa, Subgroup.closure_le]
      intro t ht
      rcases ht with rfl | ht
      · rw [← hyv]
        exact hmem y (by simp)
      · rw [Set.mem_singleton_iff] at ht
        rw [ht, ← hbyv]
        exact hmem (b y) (by simp)
    · rw [← hUb, Subgroup.closure_le]
      intro t ht
      rcases ht with rfl | ht
      · exact hmem x (by simp)
      · rw [Set.mem_singleton_iff] at ht
        rw [ht, hav]
        exact hmem (a x) (by simp)
  have hCtop : C ⊔ frattini Q = ⊤ := by
    have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' (frattini Q)) C
    rw [hmapTop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  have : IsCoatomic (Subgroup Q) := inferInstance
  exact frattini_nongenerating hCtop

end CFSG.GH74.E2
