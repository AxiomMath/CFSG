module

public import CFSG.GH74.Generic.BProg.B1.Lift1
public import CFSG.GH74.Generic.BProg.Thm2

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg Subgroup

section Centralizers

variable {G : Type} [Group G]

theorem centralizer_sup_le_left_of_mem {x : G} {D E : Subgroup G} (hx : x ∈ D) :
    centralizer ((D ⊔ E : Subgroup G) : Set G) ≤ centralizer ({x} : Set G) :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Subgroup.mem_sup_left hx))

theorem mem_centralizer_closure_pair_sup {x y g : G} {E : Subgroup G} (hgx : g * x = x * g)
    (hgy : g * y = y * g) (hgE : ∀ e ∈ E, g * e = e * g) :
    g ∈ centralizer (((closure ({x, y} : Set G) : Subgroup G) ⊔ E : Subgroup G) : Set G) := by
  have : (closure ({x, y} : Set G) : Subgroup G) ⊔ E ≤ centralizer ({g} : Set G) := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) ?_
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.2 hgx.symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 hgy.symm
    · intro e he
      exact Subgroup.mem_centralizer_singleton_iff.2 (hgE e he).symm
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact Subgroup.mem_centralizer_singleton_iff.1 (this hr)

theorem commute_y_of_mem_centralizer_sup {x y g : G} {E : Subgroup G}
    (hg : g ∈ centralizer (((closure ({x, y} : Set G) : Subgroup G) ⊔ E : Subgroup G) : Set G)) :
    g * y = y * g :=
  (Subgroup.mem_centralizer_iff.1 hg y
    (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))).symm

theorem commute_of_mem_centralizer_sup {x y g : G} {E : Subgroup G}
    (hg : g ∈ centralizer (((closure ({x, y} : Set G) : Subgroup G) ⊔ E : Subgroup G) : Set G))
    {e : G} (he : e ∈ E) : g * e = e * g :=
  (Subgroup.mem_centralizer_iff.1 hg e (Subgroup.mem_sup_right he)).symm

end Centralizers

section Image

variable {G : Type} [Group G] [Finite G]

theorem imgBar_centralizer_sup {x y : G} {E : Subgroup G} (hxy : x * y = y * x) (hy : orderOf y = 2)
    (hEC : E ≤ centralizer ({x} : Set G)) (hE : IsPGroup 2 ↥E) (hyE : y ∈ normalizer (E : Set G)) :
    imgBar x (centralizer (((closure ({x, y} : Set G) : Subgroup G) ⊔ E : Subgroup G) : Set G)) =
      centralizer ({bar x y} : Set (CentralizerBar x)) ⊓
        centralizer ((imgBar x E : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyC : y ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hxy.symm
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set u : ↥C := ⟨y, hyC⟩ with hu
  have hbar : bar x y = proj x u := bar_of_mem hyC
  ext c
  constructor
  · intro hc
    obtain ⟨g, hg, rfl⟩ := mem_imgBar.1 hc
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff, hbar, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact commute_y_of_mem_centralizer_sup hg
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨e, he, rfl⟩ := mem_imgBar.1 hb
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (commute_of_mem_centralizer_sup hg he).symm
  · intro hc
    obtain ⟨hcy, hcE⟩ := Subgroup.mem_inf.1 hc
    have hzp : IsPGroup 2 ↥(zpowers y) := isPGroup_two_zpowers_of_orderOf hy
    have hA : IsPGroup 2 ↥(zpowers y ⊔ E) :=
      IsPGroup.to_sup_of_normal_right' hzp hE (Subgroup.zpowers_le.2 hyE)
    have hAC : zpowers y ⊔ E ≤ C := sup_le (Subgroup.zpowers_le.2 hyC) hEC
    have hA' : IsPGroup 2 ↥((zpowers y ⊔ E).subgroupOf C) :=
      hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAC).symm
    have hW : (zpowers y ⊔ E) ≤
        ((centralizer ({c} : Set (CentralizerBar x))).comap (proj x)).map C.subtype := by
      refine sup_le (Subgroup.zpowers_le.2 ⟨u, ?_, rfl⟩) fun e he => ⟨⟨e, hEC he⟩, ?_, rfl⟩
      · change proj x u ∈ centralizer ({c} : Set (CentralizerBar x))
        rw [Subgroup.mem_centralizer_singleton_iff, ← hbar]
        exact (Subgroup.mem_centralizer_singleton_iff.1 hcy).symm
      · change proj x ⟨e, hEC he⟩ ∈ centralizer ({c} : Set (CentralizerBar x))
        exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hcE _ (mem_imgBar.2 ⟨⟨e, hEC he⟩, he, rfl⟩))
    obtain ⟨g, hgc, hg⟩ := centralizer_quotient_of_pGroup (pPrimeCore 2 ↥C)
      (Nat.coprime_two_left.1 pPrimeCore_coprime_card) (A := (zpowers y ⊔ E).subgroupOf C) hA'
      (c := c) (by
        intro a ha
        obtain ⟨w, hw, hwa⟩ := hW ha
        have hwa' : w = a := Subtype.ext hwa
        subst hwa'
        exact Subgroup.mem_centralizer_singleton_iff.1 hw)
    refine mem_imgBar.2 ⟨g, ?_, hgc⟩
    refine mem_centralizer_closure_pair_sup (E := E) (x := x) (y := y)
      (Subgroup.mem_centralizer_singleton_iff.1 g.2) ?_ ?_
    · exact congrArg Subtype.val (hg u (show u ∈ (zpowers y ⊔ E).subgroupOf C from
        Subgroup.mem_sup_left (Subgroup.mem_zpowers y))).symm
    · intro e he
      exact congrArg Subtype.val (hg ⟨e, hEC he⟩ (show (⟨e, hEC he⟩ : ↥C) ∈
        (zpowers y ⊔ E).subgroupOf C from Subgroup.mem_sup_right he)).symm

end Image

section Lift2

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_comp_E_of_fields {x y : G} {K E : Subgroup G} (hxy : x * y = y * x)
    (hy : orderOf y = 2) (hEC : E ≤ centralizer ({x} : Set G)) (hE : IsPGroup 2 ↥E)
    (hyE : y ∈ normalizer (E : Set G)) (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    {Lb Ib : Subgroup (CentralizerBar x)}
    (hLb : IsPCompIn 2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) Lb)
    (hIb : IsPCompIn 2 (pLayerOf 2 (centralizer ((imgBar x E : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)) ⊓ Lb)) Ib) :
    ∃ L I : Subgroup G,
      (IsPCompIn 2 (centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G)) L ∧
        (L.subgroupOf (centralizer ({x} : Set G))).map (proj x) = Lb ∧
        liftAt x y Lb ≤ oPrimeResidualOf 2 L) ∧
      IsPCompIn 2 (centralizer (((closure ({x, y} : Set G) : Subgroup G) ⊔ E : Subgroup G) :
        Set G)) I ∧
      I ≤ L ∧ I ≠ ⊥ ∧ (I.subgroupOf (centralizer ({x} : Set G))).map (proj x) = Ib := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set D : Subgroup G := closure ({x, y} : Set G) with hD
  set Y : Subgroup G := centralizer ((D ⊔ E : Subgroup G) : Set G) with hY
  have hxD : x ∈ D := Subgroup.subset_closure (by simp)
  have hYC : Y ≤ C := centralizer_sup_le_left_of_mem hxD
  obtain ⟨hLcomp, hLmap⟩ := isPCompIn_liftAt hxy hy hK hLb
  set S : Subgroup (CentralizerBar x) :=
    centralizer ((imgBar x E : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) with hS
  have hrange : (projRes hYC).range = centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ S := by
    rw [range_projRes]
    exact imgBar_centralizer_sup hxy hy hEC hE hyE
  have hLbH : IsPCompIn 2 (centralizer ({bar x y} : Set (CentralizerBar x))) Lb :=
    isPCompIn_centralizer_of_isPCompIn_inf hK _ hLb
  have hIb2 : IsPCompIn 2 (S ⊓ Lb) Ib := isPCompIn_of_isPCompIn_pLayerOf 2 hIb
  have hIb3 : IsPCompIn 2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ S) Ib := by
    refine isPCompIn_of_isSubnormal 2 (le_inf (inf_le_right.trans hLbH.1) inf_le_left) ?_ hIb2
    rw [inf_comm S Lb]
    exact isSubnormal_subgroupOf_inf (isSubnormal_of_isPCompIn hLbH)
  have hIb' : IsPCompIn 2 (projRes hYC).range Ib := by
    rw [hrange]
    exact hIb3
  obtain ⟨hI, hImap⟩ := exists_isPCompIn_lift_of_odd_ker (projRes hYC)
    (not_two_dvd_card_ker_projRes hYC) hIb'
  set I : Subgroup G := oPrimeResidualOf 2 ((Ib.comap (projRes hYC)).map Y.subtype) with hIdef
  have hIbLb : Ib ≤ Lb := hIb2.1.trans inf_le_right
  refine ⟨liftAt x y Lb, I, ⟨hLcomp, hLmap, oPrimeResidualOf_le_oPrimeResidualOf_self _⟩, hI, ?_, ?_, ?_⟩
  ·
    refine Balance.oPrimeResidualOf_le_of_two_elements fun v hv h2 => ?_
    obtain ⟨z, hz, rfl⟩ := hv
    have hzLb : proj x ⟨(z : G), hYC z.2⟩ ∈ Lb := hIbLb hz
    have hzy : (z : G) * y = y * (z : G) := commute_y_of_mem_centralizer_sup z.2
    have hmem : (z : G) ∈ ((Lb.comap (proj x)).map C.subtype) ⊓ centralizer ({y} : Set G) :=
      ⟨⟨⟨(z : G), hYC z.2⟩, hzLb, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 hzy⟩
    exact Balance.mem_oPrimeResidualOf_of_two_element hmem h2
  ·
    intro hbot
    have hnt := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_nontrivial hIb.2
    have hIb0 : Ib ≠ ⊥ := fun h => (Subgroup.nontrivial_iff_ne_bot _).1 hnt
      (by rw [h, Subgroup.bot_subgroupOf])
    apply hIb0
    rw [← hImap, hbot, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  · rw [map_proj_subgroupOf_eq hYC hI.1]
    exact hImap

theorem exists_lift_comp_E {x y : G} {K E : Subgroup G} (hS : Setup1E x y E)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) {Lb Ib : Subgroup (CentralizerBar x)}
    (hLb : IsPCompIn 2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) Lb)
    (hIb : IsPCompIn 2 (pLayerOf 2 (centralizer ((imgBar x E : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)) ⊓ Lb)) Ib) :
    ∃ L I : Subgroup G,
      (IsPCompIn 2 (centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G)) L ∧
        (L.subgroupOf (centralizer ({x} : Set G))).map (proj x) = Lb ∧
        liftAt x y Lb ≤ oPrimeResidualOf 2 L) ∧
      IsPCompIn 2 (centralizer (((closure ({x, y} : Set G) : Subgroup G) ⊔ E : Subgroup G) :
        Set G)) I ∧
      I ≤ L ∧ I ≠ ⊥ ∧ (I.subgroupOf (centralizer ({x} : Set G))).map (proj x) = Ib := by
  have := hS.E_ea
  exact exists_lift_comp_E_of_fields
    (Subgroup.mem_centralizer_singleton_iff.1 hS.y_mem).symm hS.y_ord hS.E_le
    (IsElementaryAbelian.isPGroup 2 ↥E) (hS.E_norm y (Subgroup.subset_closure (by simp))) hK hLb hIb

theorem exists_lift_comp_E_of_nonsolvAdm {x y : G} {K E : Subgroup G}
    {Lb Ib : Subgroup (CentralizerBar x)} (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (h : NonsolvAdm x y K E Lb Ib) :
    ∃ L I : Subgroup G,
      (IsPCompIn 2 (centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G)) L ∧
        (L.subgroupOf (centralizer ({x} : Set G))).map (proj x) = Lb ∧
        liftAt x y Lb ≤ oPrimeResidualOf 2 L) ∧
      IsPCompIn 2 (centralizer (((closure ({x, y} : Set G) : Subgroup G) ⊔ E : Subgroup G) :
        Set G)) I ∧
      I ≤ L ∧ I ≠ ⊥ ∧ (I.subgroupOf (centralizer ({x} : Set G))).map (proj x) = Ib :=
  exists_lift_comp_E h.setup hK h.compL h.compI

end Lift2

section ElemAb

variable {G : Type*} [Group G]

theorem isElementaryAbelian_closure_pair {x y : G} (hxy : x * y = y * x) (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) : IsElementaryAbelian 2 ↥(closure ({x, y} : Set G)) := by
  have hcomm : ∀ a ∈ ({x, y} : Set G), ∀ b ∈ ({x, y} : Set G), a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hxy
    · exact hxy.symm
    · rfl
  have hcl : IsMulCommutative ↥(closure ({x, y} : Set G)) :=
    Subgroup.isMulCommutative_closure (fun a ha b hb _ => hcomm a ha b hb)
  refine { toIsMulCommutative := hcl, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun d => ?_
  apply Subtype.ext
  have hd : (d : G) ∈ closure ({x, y} : Set G) := d.2
  refine Subgroup.closure_induction (p := fun z _ => z ^ 2 = 1) ?_ ?_ ?_ ?_ hd
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  · simp
  · intro a b ha hb ha2 hb2
    have hab : Commute a b := by
      have := (IsMulCommutative.is_comm (M := closure ({x, y} : Set G))).comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this
    calc (a * b) ^ 2 = a ^ 2 * b ^ 2 := hab.mul_pow 2
      _ = 1 := by rw [ha2, hb2, one_mul]
  · intro a _ ha2
    rw [inv_pow, ha2, inv_one]

end ElemAb

section Dictionary

variable {G : Type} [Group G] [Finite G]

theorem nonsolvAdm_dichotomy (hB : B_B2_g4)
    (hKG : ∀ e : G, orderOf e = 2 →
      Gen4 ↥(centralizer ({e} : Set G)) ∧ IsKGroupNative ↥(centralizer ({e} : Set G)))
    {x y : G} {K E : Subgroup G} {Lb Ib : Subgroup (CentralizerBar x)}
    (hx : orderOf x = 2) (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (h : NonsolvAdm x y K E Lb Ib) :
    thetaHalf (pRank 2 ↥E - 1) E ≠ ⊥ ∨ NbhdSemisimple x y Lb := by
  obtain ⟨L, I, ⟨hL, -, hlift⟩, hI, hIL, hI1, -⟩ := exists_lift_comp_E_of_nonsolvAdm hK h
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := by rw [← h.setup.y_ord]; exact pow_orderOf_eq_one y
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 h.setup.y_mem).symm
  have hD := isElementaryAbelian_closure_pair hxy hx2 hy2
  rcases thm2_nonsolvable hB hKG hD h.setup.E_ea (fun d hd => h.setup.E_norm d hd)
    h.setup.E_rank hL hI hIL hI1 with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (nbhdSemisimple_of_dsemisimple hlift h2)

end Dictionary

end CFSG.GH74.Generic.BProg.B1
