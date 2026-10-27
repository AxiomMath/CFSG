module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinA6Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Klein
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace A6I

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.DoubleA3 Equiv

abbrev PS : Type := ↥A6Models.psl29

theorem closedOK_one {l : List (List Nat)} (h : closedOK l = true) : Core.cid ∈ l := by
  simp only [closedOK, Bool.and_eq_true, List.contains_iff_mem] at h
  exact h.1.1

theorem closedOK_mul {l : List (List Nat)} (h : closedOK l = true) {a b : List Nat} (ha : a ∈ l)
    (hb : b ∈ l) : Core.cmul a b ∈ l := by
  simp only [closedOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact h.1.2 a ha b hb

theorem closedOK_inv {l : List (List Nat)} (h : closedOK l = true) {a : List Nat} (ha : a ∈ l) :
    cinvT a ∈ l := by
  simp only [closedOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact h.2 a ha

theorem code_inv' (σ : P10) : code σ⁻¹ = cinvT (code σ) := DoubleA3.code_inv σ

structure LGC where
  elts : List (List Nat)
  closed : closedOK elts = true

@[expose] def LGC.sub (T : LGC) : Subgroup PS where
  carrier := {x | code (x : P10) ∈ T.elts}
  mul_mem' := fun {x y} hx hy => by
    show code ((x : P10) * (y : P10)) ∈ T.elts
    rw [code_mul]
    exact closedOK_mul T.closed hx hy
  one_mem' := by
    show code (1 : P10) ∈ T.elts
    rw [code_one]
    exact closedOK_one T.closed
  inv_mem' := fun {x} hx => by
    show code ((x : P10)⁻¹) ∈ T.elts
    rw [code_inv']
    exact closedOK_inv T.closed hx

theorem subsetOK_mem {X Y : List (List Nat)} (h : subsetOK X Y = true) {x : List Nat} (hx : x ∈ X) :
    x ∈ Y := by
  simp only [subsetOK, List.all_eq_true, List.contains_iff_mem] at h
  exact h x hx

theorem subsetOK_trans {X Y Z : List (List Nat)} (h1 : subsetOK X Y = true)
    (h2 : subsetOK Y Z = true) : subsetOK X Z = true := by
  simp only [subsetOK, List.all_eq_true, List.contains_iff_mem] at h1 h2 ⊢
  exact fun x hx => h2 x (h1 x hx)

theorem LGC.card_sub (T : LGC) (hsub : subsetOK T.elts Core.pslLit = true) (hnd : T.elts.Nodup) :
    Nat.card T.sub = T.elts.length := by
  have hbij : Function.Bijective
      (fun x : T.sub => (⟨code ((x : PS) : P10), x.2⟩ : {c // c ∈ T.elts})) := by
    constructor
    · intro x y h
      have h1 := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (code_injective h1))
    · rintro ⟨c, hc⟩
      obtain ⟨x, hx, hxc⟩ := exists_psl29_of_code (subsetOK_mem hsub hc)
      exact ⟨⟨⟨x, hx⟩, by show code x ∈ T.elts; rw [hxc]; exact hc⟩, Subtype.ext hxc⟩
  rw [Nat.card_eq_of_bijective _ hbij]
  calc Nat.card {c // c ∈ T.elts} = Nat.card ↥(T.elts.toFinset) :=
        Nat.card_congr (Equiv.subtypeEquivRight (by simp))
    _ = T.elts.length := by rw [Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hnd]

@[expose] def Dd : Subgroup PS := (LGC.mk Core.dLit facts6_D.1).sub

@[expose] def KaS : Subgroup PS := (LGC.mk Ka facts6_closed.1).sub

@[expose] def KbS : Subgroup PS := (LGC.mk Kb facts6_closed.2.1).sub

@[expose] def VaS : Subgroup PS := (LGC.mk Va facts6_closed.2.2.1).sub

@[expose] def VbS : Subgroup PS := (LGC.mk Vb facts6_closed.2.2.2).sub

theorem mem_Dd {x : PS} : x ∈ Dd ↔ code (x : P10) ∈ Core.dLit := Iff.rfl
theorem mem_KaS {x : PS} : x ∈ KaS ↔ code (x : P10) ∈ Ka := Iff.rfl
theorem mem_KbS {x : PS} : x ∈ KbS ↔ code (x : P10) ∈ Kb := Iff.rfl
theorem card_Dd : Nat.card Dd = 8 :=
  (LGC.card_sub (LGC.mk Core.dLit facts6_D.1) facts6_D.2.1 facts6_D.2.2.1).trans facts6_D.2.2.2

theorem card_KaS : Nat.card KaS = 24 :=
  (LGC.card_sub (LGC.mk Ka facts6_closed.1) facts6_sub.1 facts6_card.1).trans facts6_card.2.1

theorem card_KbS : Nat.card KbS = 24 :=
  (LGC.card_sub (LGC.mk Kb facts6_closed.2.1) facts6_sub.2.1 facts6_card.2.2.1).trans
    facts6_card.2.2.2.1

theorem card_VaS : Nat.card VaS = 4 :=
  (LGC.card_sub (LGC.mk Va facts6_closed.2.2.1)
    (subsetOK_trans facts6_sub.2.2.2.2.1 facts6_D.2.1) facts6_card.2.2.2.2.1).trans
    facts6_card.2.2.2.2.2.1

theorem card_VbS : Nat.card VbS = 4 :=
  (LGC.card_sub (LGC.mk Vb facts6_closed.2.2.2)
    (subsetOK_trans facts6_sub.2.2.2.2.2 facts6_D.2.1) facts6_card.2.2.2.2.2.2.1).trans
    facts6_card.2.2.2.2.2.2.2

theorem Dd_isPGroup : IsPGroup 2 Dd := IsPGroup.of_card (n := 3) (by rw [card_Dd]; norm_num)

theorem card_PS : Nat.card PS = 360 := card_psl29

theorem Dd_index_odd : ¬ 2 ∣ Dd.index := by
  have h := Dd.card_mul_index
  rw [card_Dd, card_PS] at h
  omega

theorem code_conj (k v : PS) : code ((k * v * k⁻¹ : PS) : P10) = conjT (code (k : P10)) (code (v : P10)) := by
  show code ((k : P10) * (v : P10) * (k : P10)⁻¹) = _
  rw [code_mul, code_mul, code_inv']
  rfl

theorem exists_of_code_mem {c : List Nat} (hc : c ∈ Core.pslLit) : ∃ x : PS, code (x : P10) = c := by
  obtain ⟨x, hx, hxc⟩ := exists_psl29_of_code hc
  exact ⟨⟨x, hx⟩, hxc⟩

theorem V_normal {V K : List (List Nat)} (h : normCent V K = true) {k v : PS}
    (hk : code (k : P10) ∈ K) (hv : code (v : P10) ∈ V) : code ((k * v * k⁻¹ : PS) : P10) ∈ V := by
  simp only [normCent, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  rw [code_conj]
  exact h.1 _ hk _ hv

theorem V_cent {V K : List (List Nat)} (h : normCent V K = true) (hVpsl : subsetOK V Core.pslLit = true)
    {k : PS} (hk : code (k : P10) ∈ K) (hc : ∀ v : PS, code (v : P10) ∈ V → k * v = v * k) :
    code (k : P10) ∈ V := by
  simp only [normCent, Bool.and_eq_true, List.all_eq_true] at h
  have h2 := h.2 _ hk
  have hX : (V.all fun v => Core.cmul (code (k : P10)) v == Core.cmul v (code (k : P10))) = true := by
    rw [List.all_eq_true]
    intro v hv
    obtain ⟨x, hx⟩ := exists_of_code_mem (subsetOK_mem hVpsl hv)
    have h3 := congrArg (fun y : PS => code (y : P10)) (hc x (by rw [hx]; exact hv))
    have h3' : code ((k : P10) * (x : P10)) = code ((x : P10) * (k : P10)) := h3
    rw [code_mul, code_mul] at h3'
    rw [← hx]
    exact beq_iff_eq.mpr h3'

  rw [hX] at h2
  simpa [List.contains_iff_mem] using h2

theorem not_normal_of {K : List (List Nat)} (h : notNormal K = true)
    (hK : subsetOK K Core.pslLit = true) (hD : subsetOK Core.dLit Core.pslLit = true) :
    ∃ k p : PS, code (k : P10) ∈ K ∧ code (p : P10) ∈ Core.dLit ∧
      code ((k * p * k⁻¹ : PS) : P10) ∉ Core.dLit := by
  simp only [notNormal, List.any_eq_true, Bool.not_eq_true'] at h
  obtain ⟨c, hc, d, hd, hn⟩ := h
  obtain ⟨k, hk⟩ := exists_of_code_mem (subsetOK_mem hK hc)
  obtain ⟨p, hp⟩ := exists_of_code_mem (subsetOK_mem hD hd)
  refine ⟨k, p, by rw [hk]; exact hc, by rw [hp]; exact hd, ?_⟩
  rw [code_conj, hk, hp]
  simpa using hn

theorem exists_rho6 {G : Type} [Group G] {L : Subgroup G}
    (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∨ IsThreeFoldCoverAlt L 6) :
    ∃ ρ₀ : ↥L →* PS, Function.Surjective ρ₀ ∧ (∀ x, ρ₀ x = 1 ↔ x ∈ Subgroup.center ↥L) ∧
      (Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) ∧
      (ρ₀.ker = ⊥ ∨ commutator ↥L = ⊤) := by
  obtain ⟨ψ, -⟩ := exists_psl_equiv
  rcases hL with ⟨⟨e⟩⟩ | ⟨hq, hc, ⟨φ⟩⟩
  · let ε : ↥L ≃* PS := e.trans ψ.symm
    have hker : ∀ x, ε x = 1 ↔ x ∈ Subgroup.center ↥L := by
      intro x
      constructor
      · intro h
        have : x = 1 := ε.injective (by rw [h, map_one])
        rw [this]
        exact Subgroup.one_mem _
      · intro hx
        have hc : ∀ y : PS, y * ε x = ε x * y := fun y => by
          obtain ⟨w, rfl⟩ := ε.surjective y
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx w]
        have h1 : ((ε x : PS) : P10) = 1 :=
          centralizer_psl29 (psl29_le_autA6 (ε x).2) (fun y hy => (congrArg Subtype.val (hc ⟨y, hy⟩)).symm)
        exact Subtype.ext h1
    have hbot : Subgroup.center ↥L = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ε.injective ?_
      rw [(hker x).mpr hx, map_one]
    refine ⟨ε.toMonoidHom, ε.surjective, hker, Or.inl (by rw [hbot]; exact Subgroup.card_bot), Or.inl ?_⟩
    exact (MonoidHom.ker_eq_bot_iff _).mpr ε.injective
  · let ε : (↥L ⧸ Subgroup.center ↥L) ≃* PS := φ.trans ψ.symm
    refine ⟨ε.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L)),
      ε.surjective.comp (QuotientGroup.mk'_surjective _), ?_, Or.inr hc, Or.inr hq.1⟩
    intro x
    show ε (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff ε ε.injective, QuotientGroup.eq_one_iff]

theorem exists_b {X : Type*} [Group X] (ρ : X →* PS) (hρ : Function.Surjective ρ)
    (hker : ∀ x, ρ x = 1 ↔ x ∈ Subgroup.center X) (α : MulAut X) :
    ∃ b : P10, b ∈ A6Models.autA6 ∧
      ∀ x, ((ρ (α x) : PS) : P10) = b * ((ρ x : PS) : P10) * b⁻¹ := by
  obtain ⟨α', hα'⟩ := exists_descent_of_center hρ hker α
  obtain ⟨⟨b, hb⟩, hbα⟩ := conjAut_surjective α'
  refine ⟨b, hb, fun x => ?_⟩
  rw [hα' x, ← hbα]
  rfl

theorem foldl_mem (w : List (List Nat)) (hw : ∀ c ∈ w, c ∈ Ka ∨ c ∈ Kb) :
    ∀ (acc : List Nat) (x : PS), code (x : P10) = acc → x ∈ KaS ⊔ KbS →
      ∃ y : PS, code (y : P10) = w.foldl Core.cmul acc ∧ y ∈ KaS ⊔ KbS := by
  induction w with
  | nil => intro acc x hx hxH; exact ⟨x, hx, hxH⟩
  | cons c w ih =>
    intro acc x hx hxH
    have hc : c ∈ Ka ∨ c ∈ Kb := hw c (List.mem_cons_self)
    have hcpsl : c ∈ Core.pslLit := by
      rcases hc with hc | hc
      · exact subsetOK_mem facts6_sub.1 hc
      · exact subsetOK_mem facts6_sub.2.1 hc
    obtain ⟨y, hy⟩ := exists_of_code_mem hcpsl
    have hyH : y ∈ KaS ⊔ KbS := by
      rcases hc with hc | hc
      · exact Subgroup.mem_sup_left (by rw [mem_KaS, hy]; exact hc)
      · exact Subgroup.mem_sup_right (by rw [mem_KbS, hy]; exact hc)
    refine ih (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) (Core.cmul acc c) (x * y) ?_
      ((KaS ⊔ KbS).mul_mem hxH hyH)
    show code ((x : P10) * (y : P10)) = _
    rw [code_mul, hx, hy]

theorem mem_sup_of_code {g : P10} (hg : g ∈ A6Models.psl29) (hc : code g ∈ Ka ∨ code g ∈ Kb) :
    (⟨g, hg⟩ : PS) ∈ KaS ⊔ KbS := by
  rcases hc with hc | hc
  · exact Subgroup.mem_sup_left (by rw [mem_KaS]; exact hc)
  · exact Subgroup.mem_sup_right (by rw [mem_KbS]; exact hc)

theorem Ka_sup_Kb : KaS ⊔ KbS = ⊤ := by
  obtain ⟨hw1, hprod, hw2⟩ := facts6_gen
  have hmemKK : ∀ c, c ∈ Ka ++ Kb → c ∈ Ka ∨ c ∈ Kb := fun c hc => List.mem_append.mp hc
  have hgen : ∀ g : P10, g ∈ pslGens → ∃ h : g ∈ A6Models.psl29, (⟨g, h⟩ : PS) ∈ KaS ⊔ KbS := by
    intro g hg
    have hgpsl : g ∈ A6Models.psl29 := by rw [psl29_eq]; exact Subgroup.subset_closure hg
    refine ⟨hgpsl, ?_⟩
    simp only [pslGens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · have hc0 : code A6Models.tAdd = Core.pslGenC[0]! := by
        have := congrArg (fun l => l[0]!) pslGens_code
        simpa [pslGens] using this
      obtain ⟨y, hy, hyH⟩ := foldl_mem wordA (fun c hc => hmemKK c (subsetOK_mem hw1 hc)) Core.cid 1
        code_one (one_mem _)
      have hyg : y = ⟨A6Models.tAdd, hgpsl⟩ :=
        Subtype.ext (code_injective (by rw [hy, hc0, ← hprod]; rfl))
      rw [← hyg]; exact hyH
    · have hc1 : code A6Models.tSq = Core.pslGenC[1]! := by
        have := congrArg (fun l => l[1]!) pslGens_code
        simpa [pslGens] using this
      refine mem_sup_of_code hgpsl (hmemKK _ (subsetOK_mem hw2 ?_)) 
      rw [hc1]; simp
    · have hc2 : code A6Models.tInv = Core.pslGenC[2]! := by
        have := congrArg (fun l => l[2]!) pslGens_code
        simpa [pslGens] using this
      refine mem_sup_of_code hgpsl (hmemKK _ (subsetOK_mem hw2 ?_))
      rw [hc2]; simp
  have hle : A6Models.psl29 ≤ (KaS ⊔ KbS).map A6Models.psl29.subtype := by
    refine psl29_eq.le.trans ((Subgroup.closure_le _).mpr ?_)
    intro g hg
    obtain ⟨h, hH⟩ := hgen g hg
    exact ⟨⟨g, h⟩, hH, rfl⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

theorem lift_K {X : Type*} [Group X] [Finite X] (ρ : X →* PS) (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ Subgroup.center X) (hZc : Nat.card ρ.ker = 1 ∨ Nat.card ρ.ker = 3)
    {P : Subgroup X} (hP : IsPGroup 2 P) (hPmap : P.map ρ = Dd)
    {K V : List (List Nat)} (hKc : closedOK K = true) (hVc : closedOK V = true)
    (hKpsl : subsetOK K Core.pslLit = true) (hK24 : Nat.card (LGC.mk K hKc).sub = 24)
    (hDK : subsetOK Core.dLit K = true) (hVD : subsetOK V Core.dLit = true)
    (hV4 : Nat.card (LGC.mk V hVc).sub = 4) (hnc : normCent V K = true) (hnn : notNormal K = true)
    (Φ : MulAut X → Prop) (hΦ : ∀ α, Φ α → P.map α.toMonoidHom = P)
    (hinv : ∀ α, Φ α → ∃ α' : MulAut PS, (∀ x, ρ (α x) = α' (ρ x)) ∧
      (LGC.mk K hKc).sub.map α'.toMonoidHom = (LGC.mk K hKc).sub) :
    ∃ K' V' : Subgroup X, V' ≤ K' ∧ K' ≤ Subgroup.normalizer (V' : Set X) ∧ IsPGroup 2 V' ∧
      (∀ x ∈ K', (∀ v ∈ V', x * v = v * x) → x ∈ V') ∧ K'.map ρ = (LGC.mk K hKc).sub ∧
      ∀ α, Φ α → K'.map α.toMonoidHom = K' := by
  have hVpsl : subsetOK V Core.pslLit = true := subsetOK_trans hVD facts6_D.2.1
  have hDpsl := facts6_D.2.1
  refine lift_charTwo' ρ hρ hZ hZc hP hPmap card_Dd hK24 (fun x hx => subsetOK_mem hDK hx)
    (fun x hx => subsetOK_mem hVD hx) (IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num))
    (fun k hk v hv => V_normal hnc hk hv) (fun k hk hc => V_cent hnc hVpsl hk (fun v hv => hc v hv))
    ?_ Φ hΦ hinv
  obtain ⟨k, p, hk, hp, hn⟩ := not_normal_of hnn hKpsl hDpsl
  exact ⟨k, hk, p, hp, hn⟩

end A6I

end CFSG.QuasithinUnique.Unc25G2

namespace CFSG.QuasithinUnique

open Equiv CFSG.Open CFSG.Quasithin Unc25G2 Unc25G2.A6I CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.DoubleA3

theorem a6InnerFact : A6InnerFact := by
  intro G _ _ L S₀ ML z hL hS₀2 hS₀N hsyl hz hzS hMLL hMLne hall
  obtain ⟨ρ₀, hρ₀, hker₀, hZc₀, hperf₀⟩ := exists_rho6 hL
  have hP'2 : IsPGroup 2 ((S₀ ⊓ L).subgroupOf L) := isPGroup_inf_subgroupOf L hS₀2
  obtain ⟨a, ha⟩ := exists_conj_comp_map_eq ρ₀ hρ₀ hP'2 hsyl.2.2 Dd_isPGroup Dd_index_odd
  let ρ : ↥L →* PS := (MulAut.conj a).toMonoidHom.comp ρ₀
  have hρ : Function.Surjective ρ := (MulAut.conj a).surjective.comp hρ₀
  have hker : ∀ x, ρ x = 1 ↔ x ∈ Subgroup.center ↥L := by
    intro x
    rw [← hker₀ x]
    show (MulAut.conj a) (ρ₀ x) = 1 ↔ _
    rw [map_eq_one_iff _ (MulAut.conj a).injective]
  have hkerρ : ρ.ker = Subgroup.center ↥L := by
    ext x; exact hker x
  have hker0 : ρ₀.ker = Subgroup.center ↥L := by
    ext x; exact hker₀ x
  have hZ : ρ.ker ≤ Subgroup.center ↥L := hkerρ.le
  have hZc : Nat.card ρ.ker = 1 ∨ Nat.card ρ.ker = 3 := by rw [hkerρ]; exact hZc₀
  have hperf : ρ.ker = ⊥ ∨ commutator ↥L = ⊤ := by
    rw [hkerρ, ← hker0]; exact hperf₀
  obtain ⟨bz, hbzA, hbz⟩ := exists_b ρ hρ hker (conjAut L z hz)
  by_cases hin : bz ∈ A6Models.psl29
  ·
    obtain ⟨l, hl⟩ := hρ ⟨bz, hin⟩
    have hdesc : ∀ x, ρ (conjAut L z hz x) = ρ (l * x * l⁻¹) := by
      intro x
      apply Subtype.ext
      rw [hbz x, map_mul, map_mul, map_inv, hl]
      rfl
    have heq := eq_conj_of_descend ρ hZ hperf (conjAut L z hz) l hdesc
    refine ⟨(l : G), l.2, fun x hx => ?_⟩
    have hmem : z⁻¹ * x * z ∈ L := by
      apply (Subgroup.mem_normalizer_iff.mp hz (z⁻¹ * x * z)).mpr
      have e : z * (z⁻¹ * x * z) * z⁻¹ = x := by group
      rw [e]; exact hx
    have h1 := congrArg Subtype.val (heq ⟨z⁻¹ * x * z, hmem⟩)
    simp only [coe_conjAut, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have e : z * (z⁻¹ * x * z) * z⁻¹ = x := by group
    rw [e] at h1
    calc z⁻¹ * x * z = (l : G)⁻¹ * ((l : G) * (z⁻¹ * x * z) * (l : G)⁻¹) * (l : G) := by group
      _ = (l : G)⁻¹ * x * (l : G) := by rw [← h1]
  · exfalso
    have hP'ρ : ∀ p ∈ (S₀ ⊓ L).subgroupOf L, ρ p ∈ Dd := fun p hp => by
      rw [← ha]; exact ⟨p, hp, rfl⟩
    have hDcodes : ∀ d ∈ Core.dLit, ∃ p ∈ (S₀ ⊓ L).subgroupOf L,
        code ((ρ p : PS) : P10) = d := by
      intro d hd
      obtain ⟨y, hy⟩ := exists_of_code_mem (subsetOK_mem facts6_D.2.1 hd)
      have hyD : y ∈ Dd := by rw [mem_Dd, hy]; exact hd
      rw [← ha] at hyD
      obtain ⟨p, hp, hpy⟩ := hyD
      exact ⟨p, hp, by rw [hpy, hy]⟩
    have hbzpsl : code bz ∉ Core.pslLit := fun h => hin ((mem_psl29_iff bz).mpr h)
    have hbzD : ∀ d ∈ Core.dLit, Core.cmul (code bz) d = Core.cmul d (code bz) := by
      intro d hd
      obtain ⟨p, hp, hpd⟩ := hDcodes d hd
      have hpS : ((p : ↥L) : G) ∈ S₀ := (Subgroup.mem_subgroupOf.mp hp).1
      have hzp : z * ((p : ↥L) : G) = ((p : ↥L) : G) * z :=
        Subgroup.mem_centralizer_iff.mp (hzS hpS) z (Set.mem_singleton z)
      have hfix : conjAut L z hz p = p := by
        apply Subtype.ext
        rw [coe_conjAut, hzp]
        group
      have h1 := hbz p
      rw [hfix] at h1
      have h2 : bz * ((ρ p : PS) : P10) = ((ρ p : PS) : P10) * bz := by
        calc bz * ((ρ p : PS) : P10) = (bz * ((ρ p : PS) : P10) * bz⁻¹) * bz := by group
          _ = ((ρ p : PS) : P10) * bz := by rw [← h1]
      have h3 := congrArg code h2
      rw [code_mul, code_mul, hpd] at h3
      exact h3
    have hS : ∀ s (hs : s ∈ S₀), ∃ bs : P10, ∃ _ : bs ∈ A6Models.autA6,
        (∀ x, ((ρ (conjAut L s (hS₀N hs) x) : PS) : P10) = bs * ((ρ x : PS) : P10) * bs⁻¹) ∧
        (∀ k ∈ Ka, conjT (code bs) k ∈ Ka) ∧ (∀ k ∈ Kb, conjT (code bs) k ∈ Kb) := by
      intro s hs
      obtain ⟨bs, hbsA, hbs⟩ := exists_b ρ hρ hker (conjAut L s (hS₀N hs))
      have hbsD : ∀ d ∈ Core.dLit, conjT (code bs) d ∈ Core.dLit := by
        intro d hd
        obtain ⟨p, hp, hpd⟩ := hDcodes d hd
        have hp' : conjAut L s (hS₀N hs) p ∈ (S₀ ⊓ L).subgroupOf L := by
          rw [← map_conjAut_subgroupOf_eq hS₀N hs]; exact ⟨p, hp, rfl⟩
        have h1 := hP'ρ _ hp'
        rw [mem_Dd, hbs p] at h1
        have e : code (bs * ((ρ p : PS) : P10) * bs⁻¹) = conjT (code bs) d := by
          rw [code_mul, code_mul, code_inv', hpd]; rfl
        rwa [e] at h1
      have hcomm : bs * bz = bz * bs := by
        have hg : (bs * bz)⁻¹ * (bz * bs) ∈ A6Models.autA6 :=
          A6Models.autA6.mul_mem (A6Models.autA6.inv_mem (A6Models.autA6.mul_mem hbsA hbzA))
            (A6Models.autA6.mul_mem hbzA hbsA)
        have h1 := centralizer_psl29 hg (fun x hx => by
          obtain ⟨y, hy⟩ := hρ ⟨x, hx⟩
          have hyx : ((ρ y : PS) : P10) = x := congrArg Subtype.val hy
          have e1 : conjAut L z hz (conjAut L s (hS₀N hs) y) = conjAut L s (hS₀N hs) (conjAut L z hz y) := by
            apply Subtype.ext
            rw [coe_conjAut, coe_conjAut, coe_conjAut, coe_conjAut]
            have hsz : z * s = s * z :=
              (Subgroup.mem_centralizer_iff.mp (hzS hs) z (Set.mem_singleton z))
            calc z * (s * (y : G) * s⁻¹) * z⁻¹ = (z * s) * (y : G) * (z * s)⁻¹ := by group
              _ = (s * z) * (y : G) * (s * z)⁻¹ := by rw [hsz]
              _ = s * (z * (y : G) * z⁻¹) * s⁻¹ := by group
          have e2 := congrArg (fun w : ↥L => ((ρ w : PS) : P10)) e1
          simp only [hbz, hbs, hyx] at e2
          calc (bs * bz)⁻¹ * (bz * bs) * x
              = (bs * bz)⁻¹ * (bz * (bs * x * bs⁻¹) * bz⁻¹) * (bz * bs) := by group
            _ = (bs * bz)⁻¹ * (bs * (bz * x * bz⁻¹) * bs⁻¹) * (bz * bs) := by rw [e2]
            _ = x * ((bs * bz)⁻¹ * (bz * bs)) := by group)
        rwa [inv_mul_eq_one] at h1
      have hcc : Core.cmul (code bs) (code bz) = Core.cmul (code bz) (code bs) := by
        have := congrArg code hcomm
        rwa [code_mul, code_mul] at this
      exact ⟨bs, hbsA, hbs,
        facts6_aut_a (code bz) (code_mem_autL hbzA) hbzpsl hbzD (code bs) (code_mem_autL hbsA) hbsD hcc,
        facts6_aut_b (code bz) (code_mem_autL hbzA) hbzpsl hbzD (code bs) (code_mem_autL hbsA) hbsD hcc⟩
    let Φ : MulAut ↥L → Prop := fun α => ∃ s, ∃ hs : s ∈ S₀, α = conjAut L s (hS₀N hs)
    have hΦ : ∀ α, Φ α → ((S₀ ⊓ L).subgroupOf L).map α.toMonoidHom = (S₀ ⊓ L).subgroupOf L := by
      rintro α ⟨s, hs, rfl⟩
      exact map_conjAut_subgroupOf_eq hS₀N hs
    have hinvgen : ∀ (K : List (List Nat)) (hKc : closedOK K = true),
        (∀ s (hs : s ∈ S₀), ∃ bs : P10, ∃ _ : bs ∈ A6Models.autA6,
          (∀ x, ((ρ (conjAut L s (hS₀N hs) x) : PS) : P10) = bs * ((ρ x : PS) : P10) * bs⁻¹) ∧
          ∀ k ∈ K, conjT (code bs) k ∈ K) →
        ∀ α, Φ α → ∃ α' : MulAut PS, (∀ x, ρ (α x) = α' (ρ x)) ∧
          (LGC.mk K hKc).sub.map α'.toMonoidHom = (LGC.mk K hKc).sub := by
      intro K hKc h α hα
      obtain ⟨s, hs, rfl⟩ := hα
      obtain ⟨bs, hbsA, hbs, hK⟩ := h s hs
      refine ⟨conjAut ⟨bs, hbsA⟩, fun x => Subtype.ext (by rw [hbs x]; rfl),
        map_eq_of_forall_mem _ (fun x hx => ?_)⟩
      show code (bs * (x : P10) * bs⁻¹) ∈ K
      rw [code_mul, code_mul, code_inv']
      exact hK _ hx
    obtain ⟨Ka', Va', hVKa, hnKa, hVa2, hCa, hKamap, hKainv⟩ :=
      lift_K ρ hρ hZ hZc hP'2 ha facts6_closed.1 facts6_closed.2.2.1 facts6_sub.1 card_KaS
        facts6_sub.2.2.1 facts6_sub.2.2.2.2.1 card_VaS facts6_normal.2.2.1 facts6_normal.1 Φ hΦ
        (hinvgen Ka facts6_closed.1 (fun s hs => by
          obtain ⟨bs, hbsA, hbs, hKa, -⟩ := hS s hs
          exact ⟨bs, hbsA, hbs, hKa⟩))
    obtain ⟨Kb', Vb', hVKb, hnKb, hVb2, hCb, hKbmap, hKbinv⟩ :=
      lift_K ρ hρ hZ hZc hP'2 ha facts6_closed.2.1 facts6_closed.2.2.2 facts6_sub.2.1 card_KbS
        facts6_sub.2.2.2.1 facts6_sub.2.2.2.2.2 card_VbS facts6_normal.2.2.2 facts6_normal.2.1 Φ hΦ
        (hinvgen Kb facts6_closed.2.1 (fun s hs => by
          obtain ⟨bs, hbsA, hbs, -, hKb⟩ := hS s hs
          exact ⟨bs, hbsA, hbs, hKb⟩))
    obtain ⟨hcharA, hnormA⟩ := exists_charTwo_map_of_canonical hS₀N hVKa hnKa hVa2 hCa
      (fun s hs => hKainv _ ⟨s, hs, rfl⟩)
    obtain ⟨hcharB, hnormB⟩ := exists_charTwo_map_of_canonical hS₀N hVKb hnKb hVb2 hCb
      (fun s hs => hKbinv _ ⟨s, hs, rfl⟩)
    have hKaML : Ka'.map L.subtype ≤ ML := hall _ (Subgroup.map_subtype_le Ka') hnormA hcharA
    have hKbML : Kb'.map L.subtype ≤ ML := hall _ (Subgroup.map_subtype_le Kb') hnormB hcharB
    have hsup : Ka' ⊔ Kb' ≤ ML.subgroupOf L := by
      refine sup_le (fun k hk => ?_) (fun k hk => ?_)
      · exact Subgroup.mem_subgroupOf.mpr (hKaML ⟨k, hk, rfl⟩)
      · exact Subgroup.mem_subgroupOf.mpr (hKbML ⟨k, hk, rfl⟩)
    have hmap : (Ka' ⊔ Kb').map ρ = ⊤ := by
      rw [Subgroup.map_sup, hKamap, hKbmap]
      exact Ka_sup_Kb
    have htop := eq_top_of_map_eq_top ρ hZ hperf hmap
    apply hMLne
    apply le_antisymm hMLL
    intro g hg
    have hg' : (⟨g, hg⟩ : ↥L) ∈ ML.subgroupOf L := hsup (by rw [htop]; trivial)
    exact Subgroup.mem_subgroupOf.mp hg'

end CFSG.QuasithinUnique
