module

public import CFSG.GH74.Generic.BProg.B2.GenLocBasicExc
public import CFSG.GH74.Generic.BProg.B2.GenLocPsl2Gen
public import CFSG.GH74.Generic.BProg.B2.ShapeGenS45
public import CFSG.LieType.Ree.SuzukiReeOuterTwoPart
public import CFSG.LieType.Simplicity.ReeSmall
public import CFSG.GH74.Generic.BProg.B2.GenLoc4Defs

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Subgroup CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B1.PilotS4 CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Walter CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Chevalley CFSG.Walter.Ree.Model
open scoped MatrixGroups

namespace GenLocRee

@[expose] def ReeDatum {T : Type} [Group T] (u : T) (f : ℕ) : Prop :=
  ∃ F : Subgroup T, F ≤ centralizer ({u} : Set T) ∧ u ∉ F ∧
    centralizer ({u} : Set T) = zpowers u ⊔ F ∧ Nonempty (↥F ≃* PSL(2, GaloisField 3 f))

theorem ReeDatum.map_equiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T') {u : T} {f : ℕ}
    (h : ReeDatum u f) : ReeDatum (e u) f := by
  obtain ⟨F, hF1, hF2, hF3, ⟨iso⟩⟩ := h
  refine ⟨F.map e.toMonoidHom, ?_, ?_, ?_,
    ⟨(F.equivMapOfInjective e.toMonoidHom e.injective).symm.trans iso⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.1 (hF1 hx)
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, this]
  · rintro ⟨x, hx, hxu⟩
    exact hF2 (e.injective hxu ▸ hx)
  · rw [← CFSG.GH74.GLS.IVK.GHInv.map_centralizer_singleton' e u, hF3, Subgroup.map_sup,
      MonoidHom.map_zpowers]
    rfl

section Datum

theorem reeGamma_datum {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    (u : ↥(ReeTag.G2.reeGamma K a)) (hu : orderOf u = 2) : ReeDatum u (2 * a + 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  set J : JT.JTHyp ↥(ReeTag.G2.reeGamma K a) := smallReeJTHyp ha hK with hJ
  have hu' : orderOf (u : ModGL ReeTag.G2.tag K) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  obtain ⟨g, hgΓ, hgu⟩ := exists_conj_eq_smallReeH_of_orderOf hK hw₀ u.2 hu'
  set g₀ : ↥(ReeTag.G2.reeGamma K a) := ⟨g, hgΓ⟩ with hg₀
  have hconj : g₀ * u * g₀⁻¹ = J.t := Subtype.ext hgu
  have ht' : (J.conj g₀⁻¹).t = u := by
    rw [JT.JTHyp.conj_t, ← hconj]
    group
  refine ⟨(J.conj g₀⁻¹).F, ?_, ?_, ?_, ⟨(J.conj g₀⁻¹).iso⟩⟩
  · rw [← ht']
    exact (J.conj g₀⁻¹).le_centralizer
  · rw [← ht']
    exact (J.conj g₀⁻¹).t_not_mem
  · rw [← ht']
    exact (J.conj g₀⁻¹).centralizer_eq

theorem ree_cent_datum {T : Type} [Group T] (h : QShape4 T) :
    ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ∀ u : T, orderOf u = 2 → ReeDatum u f := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ := ree_model_data' (reeTitsModel_of_lieModel hf)
  refine ⟨2 * a + 1, ⟨a, rfl⟩, by omega, fun u hu => ?_⟩
  have hu' : orderOf (e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  have := (reeGamma_datum ha hK (e u) hu').map_equiv e.symm
  simpa using this

end Datum

theorem three_pow_odd_mod_eight {f : ℕ} (hf : Odd f) : 3 ^ f % 8 = 3 := by
  obtain ⟨a, rfl⟩ := hf
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem sup_centralizer_eq_top_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {a b : X}
    (h : centralizer ({e a} : Set Y) ⊔ centralizer ({e b} : Set Y) = ⊤) :
    centralizer ({a} : Set X) ⊔ centralizer ({b} : Set X) = ⊤ := by
  have := congrArg (Subgroup.map e.symm.toMonoidHom) h
  rw [Subgroup.map_sup, CFSG.GH74.GLS.IVK.GHInv.map_centralizer_singleton' e.symm (e a),
    CFSG.GH74.GLS.IVK.GHInv.map_centralizer_singleton' e.symm (e b), MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply] at this
  rw [this]
  exact Subgroup.map_top_of_surjective _ e.symm.surjective

theorem exists_two_ne_one' {J : Type} [Group J] {B : Subgroup J} [Finite B]
    (h : 2 < Nat.card ↥B) : ∃ t ∈ B, ∃ u ∈ B, t ≠ 1 ∧ u ≠ 1 ∧ t ≠ u := by
  have := Fintype.ofFinite ↥B
  have h' : 2 < Fintype.card ↥B := by rwa [Fintype.card_eq_nat_card]
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h'
  by_cases ha : a = 1
  · exact ⟨b, b.2, c, c.2, fun h => hab (ha.trans (Subtype.ext h.symm)),
      fun h => hac (ha.trans (Subtype.ext h.symm)), fun h => hbc (Subtype.ext h)⟩
  · by_cases hb : b = 1
    · exact ⟨a, a.2, c, c.2, fun h => ha (Subtype.ext h),
        fun h => hbc (hb.trans (Subtype.ext h.symm)), fun h => hac (Subtype.ext h)⟩
    · exact ⟨a, a.2, b, b.2, fun h => ha (Subtype.ext h), fun h => hb (Subtype.ext h),
        fun h => hab (Subtype.ext h)⟩

theorem cent_four {T : Type} [Group T] {E F : Subgroup T} (hE : CFSG.IsElementaryAbelian 2 ↥E)
    {t x : T} (ht2 : orderOf t = 2) (hFt : F ≤ centralizer ({t} : Set T)) (htE : t ∈ E)
    (htF : t ∉ F) (hx : x ∈ E ⊓ F) (hx1 : x ≠ 1) :
    orderOf x = 2 ∧ closure ({t, x} : Set T) ≤ E ∧ t ∈ closure ({t, x} : Set T) ∧
      Nat.card ↥(closure ({t, x} : Set T)) = 4 ∧
      (∀ z ∈ F, z * x = x * z → z ∈ centralizer (closure ({t, x} : Set T) : Set T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hab, hsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hE
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hsq x hx.1) hx1
  have htx : t * x = x * t := hab t htE x hx.1
  have hne : t ≠ x := fun h => htF (h ▸ hx.2)
  obtain ⟨-, -, hc4⟩ := CFSG.GH74.Generic.BProg.B1.PilotS5.closure_pair_facts ht2 hx2 htx hne
  refine ⟨hx2, ?_, subset_closure (by simp), hc4, fun z hz hzx => ?_⟩
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact htE
    · exact hx.1
  · rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro g (rfl | hg)
    · exact (mem_centralizer_singleton_iff.1 (hFt hz)).symm
    · rw [Set.mem_singleton_iff.1 hg]
      exact hzx.symm

end GenLocRee

section ModelA

variable {T : Type} [Group T] [Finite T]

theorem ree_sq_aut_inner (h : QShape4 T) {φ : MulAut T} (hφ : φ * φ = 1) :
    φ ∈ (MulAut.conj : T →* MulAut T).range := by
  obtain ⟨f, hf⟩ := h
  have hout := (CFSG.LieType.Ree.SuzukiReeOuterTwoPart.small_Ree_case
    (reeTitsModel_of_lieModel hf)).1
  have : Finite (MulAut T) := MulEquiv.finite_left
  have hpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) :=
    Nat.card_pos
  have hodd : ¬ 2 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) := by
    intro h2
    have h3 := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos.ne' h2
    exact (Nat.ne_of_gt (Nat.one_lt_two_pow h3.ne')) hout
  have hx2 : (QuotientGroup.mk φ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer T) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, sq, hφ, QuotientGroup.mk_one]
  have hx1 : (QuotientGroup.mk φ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer T) = 1 := by
    by_contra hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord := orderOf_eq_prime hx2 hne
    have hdvd := orderOf_dvd_natCard (QuotientGroup.mk φ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer T)
    rw [hord] at hdvd
    exact hodd hdvd
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff φ).1 hx1
  exact ⟨g, hg⟩

omit [Finite T] in
theorem ree_conj_injective (h : QShape4 T) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  have hZ := center_of_qShape4 h
  intro g k hgk
  have hc : ∀ x : T, g * x * g⁻¹ = k * x * k⁻¹ := fun x => by
    simpa [MulAut.conj_apply] using congrArg (fun φ : MulAut T => φ x) hgk
  have := hZ (k⁻¹ * g) fun x => by
    have := hc x
    calc x * (k⁻¹ * g) = k⁻¹ * (k * x * k⁻¹) * g := by group
      _ = k⁻¹ * (g * x * g⁻¹) * g := by rw [this]
      _ = (k⁻¹ * g) * x := by group
  exact (inv_mul_eq_one.1 this).symm

omit [Finite T] in
theorem ree_involution_noncentral (h : QShape4 T) {x : T} (hx : x ≠ 1) :
    ∃ y : T, y * x ≠ x * y := by
  by_contra hcon
  push Not at hcon
  exact hx (center_of_qShape4 h x fun g => hcon g)

omit [Finite T] in
theorem ree_isSimple (h : QShape4 T) : IsSimpleGroup T := by
  obtain ⟨f, hf⟩ := h
  exact (CFSG.LieType.Simplicity.fam_2g2_simplicity T 3 f (reeTitsModel_of_lieModel hf)).2

end ModelA

section ModelC

open GenLocRee

variable {T : Type} [Group T] [Finite T]

theorem ree_centralizer_le_iSup_four (h : QShape4 T) {E : Subgroup T}
    (hE : CFSG.IsElementaryAbelian 2 ↥E) (hcard : Nat.card ↥E = 8) {t : T} (htE : t ∈ E)
    (ht : t ≠ 1) :
    centralizer ({t} : Set T) ≤
      ⨆ (V : Subgroup T) (_ : V ≤ E) (_ : t ∈ V) (_ : Nat.card ↥V = 4), centralizer (V : Set T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hab, hsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hE
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact hsq t htE) ht
  obtain ⟨f, hodd, hf3, hdat⟩ := ree_cent_datum h
  obtain ⟨F, hF1, hF2, hF3, ⟨iso⟩⟩ := hdat t ht2
  have hEF : 4 ≤ Nat.card ↥(E ⊓ F) := by
    have hsurj : Function.Surjective (Sum.elim (fun z : ↥(E ⊓ F) => (⟨z.1, z.2.1⟩ : ↥E))
        (fun z : ↥(E ⊓ F) => (⟨t * z.1, E.mul_mem htE z.2.1⟩ : ↥E))) := by
      rintro ⟨e, he⟩
      have hecent : e ∈ centralizer ({t} : Set T) :=
        mem_centralizer_singleton_iff.2 (hab e he t htE)
      rw [hF3] at hecent
      rcases CFSG.GH74.Generic.BProg.B1.PilotS5.mem_sup_zpowers_of_two ht2 hF1 hecent with
        ⟨l, hl, rfl⟩ | ⟨l, hl, hel⟩
      · exact ⟨Sum.inl ⟨e, he, hl⟩, rfl⟩
      · have hlE : l ∈ E := by
          have hl' : t * e = l := by rw [hel, ← mul_assoc, hsq t htE, one_mul]
          exact hl' ▸ E.mul_mem htE he
        exact ⟨Sum.inr ⟨l, hlE, hl⟩, Subtype.ext hel.symm⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_sum, hcard] at this
    omega
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ := exists_two_ne_one' (B := E ⊓ F) (by omega)
  obtain ⟨hx2, hVxE, htVx, hVx4, hVxC⟩ := cent_four hE ht2 hF1 htE hF2 hx hx1
  obtain ⟨hy2, hVyE, htVy, hVy4, hVyC⟩ := cent_four hE ht2 hF1 htE hF2 hy hy1
  have hL1 : centralizer ({(⟨x, hx.2⟩ : ↥F)} : Set ↥F) ⊔
      centralizer ({(⟨y, hy.2⟩ : ↥F)} : Set ↥F) = ⊤ := by
    refine sup_centralizer_eq_top_of_equiv iso ?_
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hf0 : f ≠ 0 := by omega
    have hq11 : 11 ≤ 3 ^ f := by
      have : 3 ^ 3 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
      omega
    refine psl2_sup_centralizer_eq_top_mod_eight (p := 3) (f := f) (GaloisField.card 3 f hf0)
      (by norm_num) hq11 (Or.inl (three_pow_odd_mod_eight hodd)) ?_ ?_ ?_
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hx2
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hy2
    · intro hxy'
      exact hxy (congrArg Subtype.val (iso.injective hxy'))
  have hFle : F ≤ centralizer (closure ({t, x} : Set T) : Set T) ⊔
      centralizer (closure ({t, y} : Set T) : Set T) := by
    have hmapF : (⊤ : Subgroup ↥F).map F.subtype = F := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [← hmapF, ← hL1, Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hVxC z.1 z.2 (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hz))
    · rintro _ ⟨z, hz, rfl⟩
      exact hVyC z.1 z.2 (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hz))
  have htC : ∀ V : Subgroup T, V ≤ E → zpowers t ≤ centralizer (V : Set T) := fun V hV =>
    zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun v hv => hab v (hV hv) t htE)
  have hsup : centralizer (closure ({t, x} : Set T) : Set T) ⊔
      centralizer (closure ({t, y} : Set T) : Set T) ≤
      ⨆ (V : Subgroup T) (_ : V ≤ E) (_ : t ∈ V) (_ : Nat.card ↥V = 4), centralizer (V : Set T) :=
    sup_le (le_iSup_of_le (closure ({t, x} : Set T))
      (le_iSup_of_le hVxE (le_iSup_of_le htVx (le_iSup_of_le hVx4 le_rfl))))
      (le_iSup_of_le (closure ({t, y} : Set T))
      (le_iSup_of_le hVyE (le_iSup_of_le htVy (le_iSup_of_le hVy4 le_rfl))))
  rw [hF3]
  exact sup_le ((htC _ hVxE).trans (le_sup_left.trans hsup)) (hFle.trans hsup)

end ModelC

section ModelB

open GenLocRee

variable {T : Type} [Group T] [Finite T]

theorem ree_sup_centralizer_eq_top (h : QShape4 T) {t u : T} (ht : orderOf t = 2)
    (hu : orderOf u = 2) (hne : t ≠ u) :
    centralizer ({t} : Set T) ⊔ centralizer ({u} : Set T) = ⊤ := by
  obtain ⟨n, hsplit⟩ := splitGrp_of_qShape4 h
  obtain ⟨f, hf⟩ := h
  have hT := reeTitsModel_of_lieModel hf
  have hco1 := (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.ree_involution_centralizer hT ht).1
  have hco2 := (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.ree_involution_centralizer hT hu).1
  have hu1 : u ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hu; omega
  exact hco1.sup_eq_top_of_ne hco2
    (ShapeGenS45.centralizer_ne_of_ne hsplit ht hu1 (Ne.symm hne))

theorem genSub_ree (h : QShape4 T) : GenSub T := by
  intro D hD hrk
  have hZ := center_of_qShape4 h
  obtain ⟨hDab, hDsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hD
  have hDinn : D ≤ (MulAut.conj : T →* MulAut T).range := fun φ hφ =>
    ree_sq_aut_inner h (hDsq φ hφ)
  obtain ⟨hmap, hrank⟩ := map_comap_conj_of_le_inn hZ hDinn
  have hinj := ree_conj_injective h
  set B := D.comap (MulAut.conj : T →* MulAut T) with hBdef
  have hB : CFSG.IsElementaryAbelian 2 ↥B := by
    refine WeakSigGen.isElementaryAbelian_of_forall (fun b hb c hc => ?_) (fun b hb => ?_)
    · apply hinj
      rw [map_mul, map_mul]
      exact hDab _ hb _ hc
    · apply hinj
      rw [map_mul, map_one]
      exact hDsq _ hb
  obtain ⟨hBab, hBsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hB
  have hord : ∀ b ∈ B, b ≠ 1 → orderOf b = 2 := fun b hb hb1 => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hBsq b hb) hb1
  have hgen : ∀ t ∈ B, ∀ u ∈ B, t ≠ 1 → u ≠ 1 → t ≠ u →
      centralizer ({t} : Set T) ⊔ centralizer ({u} : Set T) = ⊤ :=
    fun t ht u hu ht1 hu1 htu => ree_sup_centralizer_eq_top h (hord t ht ht1) (hord u hu hu1) htu
  rw [← hmap]
  rcases hrk with h2 | h3
  · exact gammaSub_inner_two hB (by rw [hrank]; exact h2) hgen
  · refine gammaSub_inner_three hB (by rw [hrank]; exact h3) (fun t ht ht1 => ?_) hgen
    refine ree_centralizer_le_iSup_four h hB ?_ ht ht1
    rw [WeakSigGen.card_eq_two_pow_pRank hB, hrank, h3]
    norm_num

theorem genLoc_ree (h : QShape4 T) : GenLoc T :=
  (genProp_of_genSub (genSub_ree h)).genLoc

theorem genLoc4_ree (h : QShape4 T) : GenLoc4 T :=
  (genLoc_ree h).genLoc4

end ModelB

end CFSG.GH74.Generic.BProg.B2
