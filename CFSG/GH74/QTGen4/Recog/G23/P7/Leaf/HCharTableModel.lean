module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HFactsNative
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HCharTableA
public import Certificates.Certificate320017

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.HChar

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.HFactsData
  CFSG.GH74.QTGen4.Recog.G23.HCharData CFSG.GH74.QTGen4.Recog.G23.P7.HFactsAux

theorem hc_checks :
    F5Eq ∧ RepLOK ∧ KFstOK ∧ RepOK ∧ InvOK ∧ OrdOK ∧ DOK ∧ ClassOK ∧ CtOK ∧ AOK :=
  Certificates.certificate320017

theorem hc_f5_eq : F5Eq := hc_checks.1

theorem Hc_induction {P : ↥Hc → Prop} (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (hinv : ∀ a, P a → P a⁻¹) (hgen : ∀ k : Fin 5, P (gA k)) (x : ↥Hc) : P x := by
  obtain ⟨σ, hσ⟩ := x
  refine Subgroup.closure_induction (p := fun σ hσ => P ⟨σ, hσ⟩) ?_ ?_ ?_ ?_ hσ
  · rintro x ⟨k, rfl⟩
    exact hgen k
  · exact h1
  · intro x y hx hy hPx hPy
    exact hmul ⟨x, hx⟩ ⟨y, hy⟩ hPx hPy
  · intro x hx hPx
    exact hinv ⟨x, hx⟩ hPx

section Model

theorem card_of_list (L : List (List ℕ)) (hnd : L.Nodup) (hsub : ∀ l ∈ L, l ∈ elts)
    (P : ↥Hc → Prop) (q : List ℕ → Prop) [DecidablePred q]
    (hP : ∀ x : ↥Hc, P x ↔ (Lx x ∈ L ∧ q (Lx x))) :
    Nat.card {x : ↥Hc // P x} = (L.filter fun l => decide (q l)).length := by
  have himg : Lx '' ({x : ↥Hc | P x} : Set ↥Hc) =
      (((L.filter fun l => decide (q l)).toFinset : Finset (List ℕ)) : Set (List ℕ)) := by
    ext l
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h1, h2⟩ := (hP x).1 hx
      exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨h1, by simpa using h2⟩)
    · intro hl
      obtain ⟨hl1, hl2⟩ := List.mem_filter.mp (List.mem_toFinset.mp hl)
      obtain ⟨x, rfl⟩ := exists_Lx (hsub l hl1)
      exact ⟨x, (hP x).2 ⟨hl1, by simpa using hl2⟩, rfl⟩
  show Nat.card ({x : ↥Hc | P x} : Set ↥Hc) = _
  rw [Nat.card_coe_set_eq, ← Set.ncard_image_of_injective _ Lx_inj, himg, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (hnd.filter _)]

theorem Lx_inv (x : ↥Hc) : Lx x⁻¹ = invL (Lx x) := by
  obtain ⟨h1, h2⟩ := (hc_checks.2.2.2.2.1) (Lx x) (Lx_mem_elts x)
  obtain ⟨w, hw⟩ := exists_Lx h1
  have : w * x = 1 := Lx_inj (by rw [Lx_mul, hw, h2, Lx_one])
  rw [← hw, eq_inv_of_mul_eq_one_left this]

theorem Lx_pow (x : ↥Hc) (n : ℕ) : Lx (x ^ n) = powL (Lx x) n := by
  induction n with
  | zero => simp [powL, Lx_one]
  | succ n ih => rw [pow_succ', Lx_mul, ih, powL]

theorem hcRepL_eq (j : Fin 20) : hcRepL j = Lx (hcRep j) := hc_checks.2.1 j

theorem hc_kfstOK : KFstOK := hc_checks.2.2.1
theorem hc_repOK : RepOK := hc_checks.2.2.2.1
theorem hc_ordOK : OrdOK := hc_checks.2.2.2.2.2.1
theorem hc_dOK : DOK := hc_checks.2.2.2.2.2.2.1
theorem hc_classOK : ClassOK := hc_checks.2.2.2.2.2.2.2.1
theorem hc_ctOK : CtOK := hc_checks.2.2.2.2.2.2.2.2.1
theorem hc_aOK : AOK := hc_checks.2.2.2.2.2.2.2.2.2

theorem mem_KFst_iff (j : Fin 20) (x : ↥Hc) : Lx x ∈ KFst j ↔ IsConj (hcRep j) x := by
  obtain ⟨c1, c2, c3, -, -, -⟩ := hc_classOK
  have hK : KFst j = (KC j).map Prod.fst := hc_kfstOK j
  constructor
  · intro hx
    rw [hK] at hx
    obtain ⟨p, hp, hpx⟩ := List.mem_map.1 hx
    obtain ⟨-, hp2, hp3⟩ := c2 j p hp
    obtain ⟨c, hc⟩ := exists_Lx hp2
    rw [isConj_iff]
    refine ⟨c, ?_⟩
    have : c * hcRep j = x * c := by
      apply Lx_inj
      rw [Lx_mul, Lx_mul, hc, ← hcRepL_eq, hp3, hpx]
    rw [this, mul_inv_cancel_right]
  · intro hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hx
    let Q : ↥Hc → Prop := fun c => ∀ y : ↥Hc, Lx y ∈ KFst j → Lx (c * y * c⁻¹) ∈ KFst j
    have hQ : ∀ c : ↥Hc, Q c ∧ Q c⁻¹ := by
      refine fun c => Hc_induction (P := fun c => Q c ∧ Q c⁻¹) ?_ ?_ ?_ ?_ c
      · refine ⟨fun y hy => ?_, fun y hy => ?_⟩ <;> simpa using hy
      · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨fun y hy => ?_, fun y hy => ?_⟩
        · have := ha _ (hb y hy)
          simpa [mul_assoc] using this
        · have := hb' _ (ha' y hy)
          simpa [mul_assoc] using this
      · rintro a ⟨ha, ha'⟩
        exact ⟨ha', by simpa using ha⟩
      · intro k
        have hgen : ∀ y : ↥Hc, Lx y ∈ KFst j →
            Lx (gA k * y * (gA k)⁻¹) ∈ KFst j ∧ Lx ((gA k)⁻¹ * y * (gA k)⁻¹⁻¹) ∈ KFst j := by
          intro y hy
          rw [hK] at hy
          obtain ⟨p, hp, hpy⟩ := List.mem_map.1 hy
          obtain ⟨e1, e2⟩ := c3 j p hp k
          rw [hpy] at e1 e2
          rw [inv_inv, Lx_mul, Lx_mul, Lx_mul, Lx_mul]
          exact ⟨e1, e2⟩
        exact ⟨fun y hy => (hgen y hy).1, fun y hy => (hgen y hy).2⟩
    have hrep : Lx (hcRep j) ∈ KFst j := by
      rw [← hcRepL_eq, hK]
      exact List.mem_map.2 ⟨_, c1 j, rfl⟩
    exact (hQ c).1 _ hrep

theorem hc_cover (x : ↥Hc) : ∃ j, IsConj (hcRep j) x := by
  obtain ⟨-, -, -, c4, -, -⟩ := hc_classOK
  obtain ⟨j, hj⟩ := c4 (Lx x) (Lx_mem_elts x)
  exact ⟨j, (mem_KFst_iff j x).1 hj⟩

theorem hc_distinct (i j : Fin 20) (h : IsConj (hcRep i) (hcRep j)) : i = j := by
  by_contra hne
  obtain ⟨c1, -, -, -, c5, -⟩ := hc_classOK
  have h1 : Lx (hcRep j) ∈ KFst i := (mem_KFst_iff i _).2 h
  have h2 : Lx (hcRep j) ∈ KFst j := by
    rw [← hcRepL_eq, hc_kfstOK j]
    exact List.mem_map.2 ⟨_, c1 j, rfl⟩
  exact c5 i j hne _ h1 h2

theorem hc_card (j : Fin 20) : Nat.card {x : ↥Hc // IsConj (hcRep j) x} = hcSize j := by
  obtain ⟨-, c2, -, -, -, c6⟩ := hc_classOK
  have hsub : ∀ l ∈ KFst j, l ∈ elts := by
    intro l hl
    rw [hc_kfstOK j] at hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
    exact (c2 j p hp).1
  have := card_of_list (KFst j) (c6 j).1 hsub (fun x => IsConj (hcRep j) x) (fun _ => True)
    (fun x => by simp [mem_KFst_iff j x])
  simpa [(c6 j).2] using this

theorem hc_order (j : Fin 20) : orderOf (hcRep j) = hcOrd j := by
  have hposAll : ∀ j : Fin 20, 0 < hcOrd j := by decide
  obtain ⟨h1, h2⟩ := hc_ordOK j
  rw [orderOf_eq_iff (hposAll j)]
  refine ⟨?_, fun m hm hm0 => ?_⟩
  · apply Lx_inj
    rw [Lx_pow, Lx_one, ← hcRepL_eq]
    exact h1
  · intro hm1
    apply h2 m hm hm0
    rw [hcRepL_eq, ← Lx_pow, hm1, Lx_one]

theorem hc_rep_zero : hcRep 0 = 1 := by
  apply Lx_inj
  rw [← hcRepL_eq, Lx_one]
  exact hc_repOK.1

theorem hc_rep_one : hcRep 1 = zA := by
  apply Lx_inj
  rw [← hcRepL_eq]
  exact hc_repOK.2

theorem hc_dflag (j : Fin 20) : InD zA (hcRep j) ↔ hcDfl j = true := by
  have hposAll : ∀ j : Fin 20, 0 < hcOrd j := by decide
  have hD := hc_dOK j
  have hord := hc_order j
  have hpos := hposAll j
  rw [hD]
  unfold InD
  constructor
  · rintro (⟨h3, h1⟩ | ⟨k, hk, ho, hz⟩)
    · left
      rw [← hord]
      exact orderOf_eq_prime h3 h1
    · right
      refine ⟨?_, ?_⟩
      · rw [← hord, ho]
        omega
      · have : hcOrd j / 2 = k := by
          rw [← hord, ho]
          omega
        rw [this, hcRepL_eq, ← Lx_pow, hz]
  · rintro (h3 | ⟨h2, hp⟩)
    · left
      refine ⟨?_, ?_⟩
      · have : orderOf (hcRep j) = 3 := by rw [hord, h3]
        rw [← this]
        exact pow_orderOf_eq_one _
      · intro h1
        rw [h1, orderOf_one] at hord
        omega
    · right
      refine ⟨hcOrd j / 2, by omega, by rw [hord]; omega, ?_⟩
      apply Lx_inj
      rw [Lx_pow, ← hcRepL_eq]
      exact hp

theorem orderOf_two_iff_lx (x : ↥Hc) :
    orderOf x = 2 ↔ (mulL (Lx x) (Lx x) = idL ∧ Lx x ≠ idL) := by
  rw [orderOf_eq_prime_iff, sq]
  have h1 : x * x = 1 ↔ mulL (Lx x) (Lx x) = idL := by
    rw [← Lx_mul, ← Lx_one, Lx_inj.eq_iff]
  have h2 : x ≠ 1 ↔ Lx x ≠ idL := by
    rw [← Lx_one, ne_eq, ne_eq, Lx_inj.eq_iff]
  rw [h1, h2]

theorem hc_ct_z : Nat.card {u : ↥Hc // orderOf u = 2 ∧ u ≠ zA} = hcCt 1 := by
  obtain ⟨ct1, -⟩ := hc_ctOK
  have key := card_of_list elts elts_nodup (fun l hl => hl)
    (fun u : ↥Hc => orderOf u = 2 ∧ u ≠ zA)
    (fun l => mulL l l = idL ∧ l ≠ idL ∧ l ≠ Lx zA) (fun x => by
      rw [orderOf_two_iff_lx]
      constructor
      · rintro ⟨⟨a, b⟩, c⟩
        exact ⟨Lx_mem_elts x, a, b, fun h => c (Lx_inj h)⟩
      · rintro ⟨-, a, b, c⟩
        exact ⟨⟨a, b⟩, fun h => c (by rw [h])⟩)
  rw [key]
  exact ct1

theorem hc_ct_other (j : Fin 20) (hj : j ≠ 1) :
    Nat.card {u : ↥Hc // orderOf u = 2 ∧ u * hcRep j * u⁻¹ = (hcRep j)⁻¹} = hcCt j := by
  obtain ⟨-, ct2⟩ := hc_ctOK
  have key := card_of_list elts elts_nodup (fun l hl => hl)
    (fun u : ↥Hc => orderOf u = 2 ∧ u * hcRep j * u⁻¹ = (hcRep j)⁻¹)
    (fun l => mulL l l = idL ∧ l ≠ idL ∧ mulL l (hcRepL j) = mulL (invL (hcRepL j)) l) (fun x => by
      rw [orderOf_two_iff_lx]
      have hc : x * hcRep j * x⁻¹ = (hcRep j)⁻¹ ↔
          mulL (Lx x) (hcRepL j) = mulL (invL (hcRepL j)) (Lx x) := by
        rw [mul_inv_eq_iff_eq_mul, ← Lx_inj.eq_iff, Lx_mul, Lx_mul, Lx_inv, ← hcRepL_eq]
      rw [hc]
      constructor
      · rintro ⟨⟨a, b⟩, c⟩
        exact ⟨Lx_mem_elts x, a, b, c⟩
      · rintro ⟨-, a, b, c⟩
        exact ⟨⟨a, b⟩, c⟩)
  rw [key]
  exact ct2 j hj

theorem hc_KFst_sub (j : Fin 20) : ∀ l ∈ KFst j, l ∈ elts := by
  obtain ⟨-, c2, -, -, -, -⟩ := hc_classOK
  intro l hl
  rw [hc_kfstOK j] at hl
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
  exact (c2 j p hp).1

theorem hc_acount (r : Fin 4) (j k : Fin 20) :
    Nat.card {x : ↥Hc // IsConj (hcRep (hcI r)) x ∧ IsConj (hcRep j) (x⁻¹ * hcRep k)} =
      hcA r j k := by
  obtain ⟨-, -, -, -, -, c6⟩ := hc_classOK
  have key := card_of_list (KFst (hcI r)) (c6 _).1 (hc_KFst_sub _)
    (fun x => IsConj (hcRep (hcI r)) x ∧ IsConj (hcRep j) (x⁻¹ * hcRep k))
    (fun l => mulL (invL l) (hcRepL k) ∈ KFst j) (fun x => by
      rw [← mem_KFst_iff, ← mem_KFst_iff, Lx_mul, Lx_inv, ← hcRepL_eq])
  rw [key, ← hc_aOK r k j, hc_kfstOK (hcI r)]
  simp only [List.filter_map, List.length_map, Function.comp_def]

theorem tabHyp_Hc : TabHyp ↥Hc zA hcRep :=
  { cover := hc_cover
    distinct := hc_distinct
    card_class := hc_card
    rep_zero := hc_rep_zero
    rep_one := hc_rep_one
    order_rep := hc_order
    dflag := hc_dflag
    ct_z := hc_ct_z
    ct_other := hc_ct_other
    acount := hc_acount }

end Model

end CFSG.GH74.QTGen4.Recog.G23.P7.HChar
