module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Setup

public section

namespace CFSG.QuasithinUnique.L246.C123

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

section Transfer

theorem transfer {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Γ : Type}
    [Group Γ] [Finite Γ] (act : Γ →* MulAut V) {P : Subgroup Γ} (hodd : ¬ 2 ∣ P.index) {z : V}
    (hz : ∀ p ∈ P, act p z = z) :
    ∃ v : V, (∀ g : Γ, act g v = v) ∧
      z * v⁻¹ ∈ Subgroup.closure (Set.range fun g : Γ => act g z * z⁻¹) := by
  classical
  have hfinQ : Finite (Γ ⧸ P) := Subgroup.finite_quotient_of_finiteIndex
  let _ : Fintype (Γ ⧸ P) := Fintype.ofFinite _
  let f : Γ ⧸ P → V := fun q => act q.out z
  have hf : ∀ g : Γ, f (QuotientGroup.mk g) = act g z := by
    intro g
    obtain ⟨p, hp⟩ := QuotientGroup.mk_out_eq_mul P g
    show act (QuotientGroup.mk g : Γ ⧸ P).out z = act g z
    rw [hp, map_mul, MulAut.mul_apply, hz p p.2]
  have hact : ∀ (g : Γ) (q : Γ ⧸ P), act g (f q) = f (g • q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H h =>
      rw [hf h, MulAction.Quotient.smul_mk, hf, smul_eq_mul, map_mul, MulAut.mul_apply]
  refine ⟨∏ q, f q, fun g => ?_, ?_⟩
  · rw [map_prod]
    simp_rw [hact g]
    exact Equiv.prod_comp (MulAction.toPerm g) f
  · have hn : Odd (Fintype.card (Γ ⧸ P)) := by
      have : Fintype.card (Γ ⧸ P) = P.index := by
        rw [Subgroup.index, Nat.card_eq_fintype_card]
      rw [this]
      exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
    obtain ⟨k, hk⟩ := hn
    have h1 : z = ∏ _q : Γ ⧸ P, z := by
      rw [Finset.prod_const, Finset.card_univ, hk, pow_succ, pow_mul, hV z, one_pow, one_mul]
    have h2 : z * (∏ q, f q)⁻¹ = ∏ q : Γ ⧸ P, (z * (f q)⁻¹) := by
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← h1]
    rw [h2]
    refine Subgroup.prod_mem _ fun q _ => ?_
    have hq : z * (f q)⁻¹ = (act q.out z * z⁻¹)⁻¹ := by
      show z * (act q.out z)⁻¹ = _
      rw [mul_inv_rev, inv_inv, mul_comm]
    rw [hq]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨q.out, rfl⟩)

end Transfer

section ModCore

variable {G : Type} [Group G] [Finite G] {T Y L : Subgroup G} {M : Type} [CommGroup M]
  {φ : ↥(blockU L) ≃* M} {π : ↥Y →* A7} {ρ : A7 →* MulAut M}

@[expose] def img (π : ↥Y →* A7) (H : Subgroup G) : Subgroup A7 := (H.subgroupOf Y).map π

omit [Finite G] in
theorem mem_img {H : Subgroup G} {x : A7} :
    x ∈ img π H ↔ ∃ y : ↥Y, (y : G) ∈ H ∧ π y = x := by
  unfold img
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem img_mono {H K : Subgroup G} (h : H ≤ K) : img π H ≤ img π K :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono Y h)

omit [Finite G] in
theorem mem_img_of_mem {H : Subgroup G} {y : G} (hy : y ∈ Y) (hyH : y ∈ H) :
    π ⟨y, hy⟩ ∈ img π H := mem_img.2 ⟨⟨y, hy⟩, hyH, rfl⟩

omit [Finite G] in
theorem card_img_T (hH : Hyp T Y L) (hπ : Function.Surjective π) : Nat.card (img π T) = 8 := by
  have hP : IsPGroup 2 ↥(T.subgroupOf Y) :=
    hH.sylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hH.TY).symm
  have hP' : IsPGroup 2 ↥(img π T) := hP.map π
  obtain ⟨k, hk⟩ := hP'.exists_card_eq
  have hidx : ¬ 2 ∣ (img π T).index := fun hd =>
    hH.sylow.2.2 (hd.trans (Subgroup.index_map_dvd (T.subgroupOf Y) hπ))
  have h1 := (img π T).index_mul_card
  rw [hk, show Nat.card A7 = 2520 from card_A7] at h1
  have hk3 : k ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have h2520 : 2 ^ k ∣ 2520 := ⟨(img π T).index, by rw [← h1]; ring⟩
    have := h16.trans h2520
    norm_num at this
  interval_cases k
  · omega
  · omega
  · omega
  · rw [hk]; norm_num

omit [Finite G] in
theorem exists_offender (m : Main T Y L) :
    ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      ¬ A ≤ Subgroup.centralizer (VZ T Y : Set G) := by
  by_contra hcon
  push Not at hcon
  exact m.jt (iSup₂_le fun A hA => hcon A hA)

omit [Finite G] in
theorem img_eq
    (hH : Hyp T Y L) (D : ModData T Y L φ π ρ) {A A' : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hAc : ¬ A ≤ Subgroup.centralizer (VZ T Y : Set G))
    (hA' : IsMaxElemAbelian T A') (hAc' : ¬ A' ≤ Subgroup.centralizer (VZ T Y : Set G)) :
    img π A = img π A' :=
  IsKleinConj.eq_of_le (card_img_T hH D.surj) (D.klein A hA hAc).1 (D.klein A' hA' hAc').1
    (img_mono hA.1) (img_mono hA'.1)

theorem trivial_mod_U (m : Main T Y L) (D : ModData T Y L φ π ρ) :
    ∀ y ∈ Y, ∀ v ∈ VZ T Y, y * v * y⁻¹ * v⁻¹ ∈ blockU L := by
  obtain ⟨A₁, hA₁, hA₁c⟩ := exists_offender m
  have hVY : ∀ y ∈ Y, ∀ v ∈ VZ T Y, y * v * y⁻¹ ∈ VZ T Y := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.1 (m.hyp.YN hy) v).1 hv
  have hUY : ∀ y ∈ Y, ∀ u ∈ blockU L, y * u * y⁻¹ ∈ blockU L := fun y hy u hu =>
    (Subgroup.mem_normalizer_iff.1 (m.YU hy) u).1 hu
  let Wn : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ ∀ v ∈ VZ T Y, y * v * y⁻¹ * v⁻¹ ∈ blockU L}
      one_mem' := ⟨Y.one_mem, fun v _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨Y.mul_mem ha.1 hb.1, fun v hv => by
        have h1 := ha.2 (b * v * b⁻¹) (hVY b hb.1 v hv)
        have h2 := hb.2 v hv
        have e : a * b * v * (a * b)⁻¹ * v⁻¹ = (a * (b * v * b⁻¹) * a⁻¹ * (b * v * b⁻¹)⁻¹) *
            (b * v * b⁻¹ * v⁻¹) := by group
        rw [e]; exact (blockU L).mul_mem h1 h2⟩
      inv_mem' := fun {a} ha => ⟨Y.inv_mem ha.1, fun v hv => by
        have h1 := ha.2 (a⁻¹ * v * a) (by simpa using hVY a⁻¹ (Y.inv_mem ha.1) v hv)
        have e : a⁻¹ * v * a⁻¹⁻¹ * v⁻¹ =
            (a * (a⁻¹ * v * a) * a⁻¹ * (a⁻¹ * v * a)⁻¹)⁻¹ := by group
        rw [e]; exact (blockU L).inv_mem h1⟩ }
  have hWnN : Y ≤ Subgroup.normalizer (Wn : Set G) := by
    refine le_normalizer_of_forall_conj fun y hy w hw =>
      ⟨Y.mul_mem (Y.mul_mem hy hw.1) (Y.inv_mem hy), fun v hv => ?_⟩
    have h1 := hw.2 (y⁻¹ * v * y) (by simpa using hVY y⁻¹ (Y.inv_mem hy) v hv)
    have h2 := hUY y hy _ h1
    have e : y * w * y⁻¹ * v * (y * w * y⁻¹)⁻¹ * v⁻¹ =
        y * (w * (y⁻¹ * v * y) * w⁻¹ * (y⁻¹ * v * y)⁻¹) * y⁻¹ := by group
    rw [e]; exact h2
  have hDW : Y ⊓ Subgroup.centralizer (VZ T Y : Set G) ≤ Wn := fun d hd =>
    ⟨hd.1, fun v hv => by
      have h1 := Subgroup.mem_centralizer_iff.1 hd.2 v hv
      have e : d * v * d⁻¹ * v⁻¹ = 1 := by rw [← h1]; group
      rw [e]; exact (blockU L).one_mem⟩
  have hAW : A₁ ≤ Wn := fun a ha => ⟨m.hyp.TY (hA₁.1 ha), fun v hv => by
    obtain ⟨u, hu, c, hc, hcomm, rfl⟩ := D.split A₁ hA₁ hA₁c v hv
    have hca : a * c * a⁻¹ = c := mul_inv_eq_iff_eq_mul.2 (hcomm a ha)
    have e : a * (u * c) * a⁻¹ * (u * c)⁻¹ = (a * u * a⁻¹) * (a * c * a⁻¹) * c⁻¹ * u⁻¹ := by
      group
    rw [e, hca]
    have e2 : a * u * a⁻¹ * c * c⁻¹ * u⁻¹ = (a * u * a⁻¹) * u⁻¹ := by group
    rw [e2]
    exact (blockU L).mul_mem (hUY a (m.hyp.TY (hA₁.1 ha)) u hu) ((blockU L).inv_mem hu)⟩
  have hWnY : Wn ≤ Y := fun w hw => hw.1
  have hnorm : (Wn.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWnY).2 hWnN
  have hnormimg : (img π Wn).Normal := hnorm.map π D.surj
  have hK : img π A₁ ≤ img π Wn := img_mono hAW
  have hKcard : Nat.card (img π A₁) = 4 := (D.klein A₁ hA₁ hA₁c).1.card
  have htop : img π Wn = ⊤ := by
    have : IsSimpleGroup A7 := isSimple_A7
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (img π Wn) with h | h
    · exfalso
      have h0 : img π A₁ = ⊥ := le_bot_iff.1 (h ▸ hK)
      rw [h0, Subgroup.card_bot] at hKcard
      omega
    · exact h
  intro y hy v hv
  have hmem : π ⟨y, hy⟩ ∈ img π Wn := by rw [htop]; trivial
  obtain ⟨w, hwW, hw⟩ := mem_img.1 hmem
  have hker : π (⟨y, hy⟩ * w⁻¹) = 1 := by rw [map_mul, map_inv, hw, mul_inv_cancel]
  have hc := D.ker _ hker
  have hyw : y * (w : G)⁻¹ ∈ Wn := hDW ⟨Y.mul_mem hy (Y.inv_mem w.2), hc⟩
  have hyWn : y ∈ Wn := by
    have := Wn.mul_mem hyw hwW
    simpa using this
  exact hyWn.2 v hv

theorem exists_split_Z (m : Main T Y L) (D : ModData T Y L φ π ρ) :
    ∀ z ∈ quasithinOmegaOneCenter T, ∃ u ∈ blockU L, ∃ c ∈ VZ T Y,
      (∀ l ∈ L, l * c * l⁻¹ = c) ∧ z = u * c := by
  intro z hz
  have hV := m.hyp.elem
  have hLN : L ≤ Subgroup.normalizer (VZ T Y : Set G) := m.hyp.LY.trans m.hyp.YN
  let act : ↥L →* MulAut (IntMod (VZ T Y) hV) := (convI hV).comp (Subgroup.inclusion hLN)
  have hodd : ¬ 2 ∣ ((T ⊓ L).subgroupOf L).index :=
    (A4.isSylowTwoOf_inf_normal m.hyp.sylow m.hyp.LY m.hyp.normal).2.2
  have hzV : z ∈ VZ T Y := Hyp.Z_le_V hz
  let z₀ : IntMod (VZ T Y) hV := IntMod.mk hV ⟨z, hzV⟩
  have hzc : z ∈ Subgroup.centralizer (T : Set G) := (C1GN.omegaOneCenterOf_le_centerOf T hz).2
  have hz₀ : ∀ p ∈ (T ⊓ L).subgroupOf L, act p z₀ = z₀ := by
    intro p hp
    apply IntMod.val_injective
    show (convI hV (Subgroup.inclusion hLN p) z₀).val = z₀.val
    rw [convI_apply_val]
    have hpT : (p : G) ∈ T := (Subgroup.mem_subgroupOf.1 hp).1
    have h1 := Subgroup.mem_centralizer_iff.1 hzc p hpT
    show (p : G) * z * (p : G)⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.2 h1
  obtain ⟨v, hv, hmem⟩ := transfer (fun v => IntMod.sq_eq_one v) act hodd hz₀
  have hW : Subgroup.closure (Set.range fun g : ↥L => act g z₀ * z₀⁻¹) ≤
      intSub hV (blockU L) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    show (act g z₀ * z₀⁻¹).val ∈ blockU L
    rw [IntMod.val_mul, IntMod.val_inv]
    have h1 : (act g z₀).val = (g : G) * z * (g : G)⁻¹ :=
      convI_apply_val hV (Subgroup.inclusion hLN g) z₀
    rw [h1]
    exact trivial_mod_U m D g (m.hyp.LY g.2) z hzV
  have hu := hW hmem
  refine ⟨(z₀ * v⁻¹).val, hu, v.val, v.val_mem, fun l hl => ?_, ?_⟩
  · have h1 := congrArg IntMod.val (hv ⟨l, hl⟩)
    have h2 : (act ⟨l, hl⟩ v).val = l * v.val * l⁻¹ :=
      convI_apply_val hV (Subgroup.inclusion hLN ⟨l, hl⟩) v
    rw [h2] at h1
    exact h1
  · show z = (z₀ * v⁻¹).val * v.val
    rw [IntMod.val_mul, IntMod.val_inv, inv_mul_cancel_right]
    rfl

omit [Finite G] in
theorem decomp_unique (m : Main T Y L) {u u' c c' : G} (hu : u ∈ blockU L)
    (hu' : u' ∈ blockU L) (hc : ∀ l ∈ L, l * c * l⁻¹ = c) (hc' : ∀ l ∈ L, l * c' * l⁻¹ = c')
    (h : u * c = u' * c') : u = u' := by
  have hw : u'⁻¹ * u = c' * c⁻¹ := by
    calc u'⁻¹ * u = u'⁻¹ * (u * c) * c⁻¹ := by group
      _ = u'⁻¹ * (u' * c') * c⁻¹ := by rw [h]
      _ = c' * c⁻¹ := by group
  have hwU : u'⁻¹ * u ∈ blockU L := (blockU L).mul_mem ((blockU L).inv_mem hu') hu
  have hwZ : u'⁻¹ * u ∈ blockZ L := by
    refine ⟨hwU, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have h1 : l * (c' * c⁻¹) * l⁻¹ = c' * c⁻¹ := by
      have e : l * (c' * c⁻¹) * l⁻¹ = (l * c' * l⁻¹) * (l * c * l⁻¹)⁻¹ := by group
      rw [e, hc' l hl, hc l hl]
    rw [← hw] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  rw [m.zl, Subgroup.mem_bot, inv_mul_eq_one] at hwZ
  exact hwZ.symm

theorem exists_seven (m : Main T Y L) (D : ModData T Y L φ π ρ) :
    ∃ y : G, ∃ hy : y ∈ Y, y ∈ L ∧ (∀ z ∈ quasithinOmegaOneCenter T, z * y = y * z) ∧
      orderOf (π ⟨y, hy⟩) = 7 := by
  have hT8 := card_img_T m.hyp D.surj
  obtain ⟨m₀, hm₀fix, hm₀1⟩ := exists_fixed_ne_one ρ D.card_M hT8
  obtain ⟨x, hx7, hxfix⟩ := exists_order_seven_fixing ρ D.card_M D.inj hT8 hm₀1 hm₀fix
  have hLY := m.hyp.LY
  have hLn : (L.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).2 m.hyp.normal
  have hnorm : (img π L).Normal := hLn.map π D.surj
  have htop : img π L = ⊤ := by
    have : IsSimpleGroup A7 := isSimple_A7
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (img π L) with h | h
    · exfalso
      have hLc : L ≤ Subgroup.centralizer (VZ T Y : Set G) := by
        intro l hl
        apply D.ker ⟨l, hLY hl⟩
        have : π ⟨l, hLY hl⟩ ∈ img π L := mem_img_of_mem (hLY hl) hl
        rw [h, Subgroup.mem_bot] at this
        exact this
      have hUZ : blockU L ≤ blockZ L := fun u hu =>
        ⟨hu, Subgroup.mem_centralizer_iff.2 fun l hl =>
          (Subgroup.mem_centralizer_iff.1 (hLc hl) u (m.uV hu)).symm⟩
      rw [m.zl] at hUZ
      have h1 : Nat.card ↥(blockU L) = 1 := by
        have : blockU L = ⊥ := le_bot_iff.1 hUZ
        rw [this]; exact Subgroup.card_bot
      have := m.card_U
      omega
    · exact h
  have hxL : x ∈ img π L := by rw [htop]; trivial
  obtain ⟨y, hyL, hyx⟩ := mem_img.1 hxL
  refine ⟨y, y.2, hyL, fun z hz => ?_, by rw [hyx]; exact hx7⟩
  obtain ⟨u, hu, c, hc, hcL, rfl⟩ := exists_split_Z m D z hz
  have huT : ∀ t ∈ T, t * u * t⁻¹ = u := by
    intro t ht
    have hzc : u * c ∈ Subgroup.centralizer (T : Set G) :=
      (C1GN.omegaOneCenterOf_le_centerOf T hz).2
    have h1 := Subgroup.mem_centralizer_iff.1 hzc t ht
    have h2 : u * c = (t * u * t⁻¹) * (t * c * t⁻¹) := by
      have : t * (u * c) * t⁻¹ = u * c := mul_inv_eq_iff_eq_mul.2 h1
      rw [← this]; group
    have hu' : t * u * t⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.1 (m.YU (m.hyp.TY ht)) u).1 hu
    have hc' : ∀ l ∈ L, l * (t * c * t⁻¹) * l⁻¹ = t * c * t⁻¹ := by
      intro l hl
      have hl' : t⁻¹ * l * t ∈ L := by
        simpa using (Subgroup.mem_normalizer_iff.1
          (m.hyp.normal (Y.inv_mem (m.hyp.TY ht))) l).1 hl
      have h3 := hcL _ hl'
      calc l * (t * c * t⁻¹) * l⁻¹ = t * ((t⁻¹ * l * t) * c * (t⁻¹ * l * t)⁻¹) * t⁻¹ := by group
        _ = t * c * t⁻¹ := by rw [h3]
    exact (decomp_unique m hu hu' hcL hc' h2).symm
  have hfix : ρ x (φ ⟨u, hu⟩) = φ ⟨u, hu⟩ := by
    apply fix_of_fix_one ρ D.card_M D.inj hT8 hm₀1 hm₀fix hxfix
    rw [mem_fixU]
    intro a ha
    obtain ⟨t, htT, rfl⟩ := mem_img.1 ha
    exact D.equiv t ⟨u, hu⟩ ⟨u, hu⟩ (huT _ htT).symm
  have hyu : (y : G) * u * (y : G)⁻¹ = u := by
    have hmem : (y : G) * u * (y : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.1 (m.YU y.2) u).1 hu
    have h1 := D.equiv y ⟨u, hu⟩ ⟨_, hmem⟩ rfl
    rw [hyx, hfix] at h1
    exact (congrArg Subtype.val (φ.injective h1)).symm
  have hyc : (y : G) * c * (y : G)⁻¹ = c := hcL y hyL
  have h3 : (y : G) * (u * c) * (y : G)⁻¹ = u * c := by
    calc (y : G) * (u * c) * (y : G)⁻¹
        = ((y : G) * u * (y : G)⁻¹) * ((y : G) * c * (y : G)⁻¹) := by group
      _ = u * c := by rw [hyu, hyc]
  exact (mul_inv_eq_iff_eq_mul.1 h3).symm

theorem conj_mem_of_card {Γ : Type} [Group Γ] {T A : Subgroup Γ} (hT : Nat.card T = 8)
    (hA : Nat.card A = 4) (hAT : A ≤ T) : ∀ a ∈ A, ∀ s ∈ T, s * a * s⁻¹ ∈ A := by
  have hidx : (A.subgroupOf T).index = 2 := by
    have h1 := (A.subgroupOf T).index_mul_card
    have h2 : Nat.card (A.subgroupOf T) = 4 := by
      rw [← hA]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv
    rw [h2, hT] at h1
    omega
  have hnorm : (A.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hidx
  intro a ha s hs
  have := hnorm.conj_mem ⟨a, hAT ha⟩ (Subgroup.mem_subgroupOf.2 ha) ⟨s, hs⟩
  exact Subgroup.mem_subgroupOf.1 this

omit [Finite G] in
theorem thompsonJ_le_baum' (T : Subgroup G) : thompsonJ T ≤ baum T := by
  refine le_inf (thompsonJ_le_self T) ?_
  rw [Subgroup.le_centralizer_iff]
  intro x hx
  exact (C1GN.omegaOneCenterOf_le_centerOf (thompsonJ T) hx).2

theorem img_baum
    (m : Main T Y L) (D : ModData T Y L φ π ρ) {A₁ : Subgroup G}
    (hA₁ : IsMaxElemAbelian T A₁) (hA₁c : ¬ A₁ ≤ Subgroup.centralizer (VZ T Y : Set G)) :
    img π (baum T) = img π A₁ := by
  have hT8 := card_img_T m.hyp D.surj
  obtain ⟨hKk, hK4⟩ := D.klein A₁ hA₁ hA₁c
  have hKcard : Nat.card (img π A₁) = 4 := hKk.card
  have hUel : IsElemAbelian 2 (blockU L) :=
    ⟨⟨⟨fun a b => Subtype.ext (m.U_comm _ a.2 _ b.2)⟩⟩, fun x hx => m.U_exp x hx⟩
  have hJ : A₁ ≤ thompsonJ T := le_iSup₂_of_le A₁ hA₁ le_rfl
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hsS, rfl⟩ := mem_img.1 hx
    have hsT : (s : G) ∈ T := hsS.1
    refine mem_of_centralizes_fixU ρ D.card_M D.inj hT8 hKcard (img_mono hA₁.1) hK4
      (mem_img_of_mem s.2 hsT) ?_
    intro m' hm'
    obtain ⟨u, rfl⟩ := φ.surjective m'
    have hu : (u : G) ∈ blockU L := u.2
    have hcomm : ∀ A : Subgroup G, IsMaxElemAbelian T A → ∀ a ∈ A, (a : G) * u = u * a := by
      intro A hA a ha
      by_cases hAc : A ≤ Subgroup.centralizer (VZ T Y : Set G)
      · exact (Subgroup.mem_centralizer_iff.1 (hAc ha) u (m.uV hu)).symm
      · have haY : a ∈ Y := m.hyp.TY (hA.1 ha)
        have hmem : π ⟨a, haY⟩ ∈ img π A₁ := by
          rw [← img_eq m.hyp D hA hAc hA₁ hA₁c]
          exact mem_img_of_mem haY ha
        have h1 := (mem_fixU.1 hm') _ hmem
        have hmem' : a * u * a⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.1 (m.YU haY) u).1 hu
        have h2 := D.equiv ⟨a, haY⟩ u ⟨_, hmem'⟩ rfl
        rw [h2] at h1
        have h3 := congrArg Subtype.val (φ.injective h1)
        have h4 : a * (u : G) * a⁻¹ = u := h3
        exact mul_inv_eq_iff_eq_mul.1 h4
    have huA : (u : G) ∈ A₁ :=
      inf_centralizer_le_of_isMaxElemAbelian hUel m.U_le_T hA₁
        ⟨hu, Subgroup.mem_centralizer_iff.2 fun a ha => hcomm A₁ hA₁ a ha⟩
    have huF : (u : G) ∈ omegaOneCenterOf (thompsonJ T) := by
      apply Subgroup.subset_closure
      refine ⟨⟨hJ huA, Subgroup.mem_centralizer_iff.2 ?_⟩, m.U_exp u hu⟩
      intro j hj
      have hle : thompsonJ T ≤ Subgroup.centralizer ({(u : G)} : Set G) := by
        refine iSup₂_le fun A hA a ha => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (hcomm A hA a ha).symm
      have := Subgroup.mem_centralizer_iff.1 (hle hj) u rfl
      exact this.symm
    have hus : (u : G) * s = s * u := Subgroup.mem_centralizer_iff.1 hsS.2 u huF
    exact D.equiv s u u (mul_inv_eq_iff_eq_mul.2 hus.symm).symm
  · exact img_mono (hJ.trans (thompsonJ_le_baum' T))

theorem core
    (m : Main T Y L) (D : ModData T Y L φ π ρ) : Y ≤ cgsIn Y T := by
  have hH := m.hyp
  obtain ⟨A₁, hA₁, hA₁c⟩ := exists_offender m
  obtain ⟨hKk, hK4⟩ := D.klein A₁ hA₁ hA₁c
  have hT8 := card_img_T hH D.surj
  have hS : img π (baum T) = img π A₁ := img_baum m D hA₁ hA₁c
  have hKT : img π A₁ ≤ img π T := img_mono hA₁.1
  have hKc : Nat.card (img π A₁) = 4 := hKk.card
  have hconj := conj_mem_of_card hT8 hKc hKT
  have hDc : ∀ d : G, d ∈ Y → (∀ v ∈ VZ T Y, v * d = d * v) → d ∈ cgsIn Y T := fun d hd hc =>
    hH.inf_centralizer_le_cgsIn ⟨hd, Subgroup.mem_centralizer_iff.2 hc⟩
  let Kt : Subgroup G := ((img π A₁).comap π).map Y.subtype
  have hKt : ∀ y : G, y ∈ Kt ↔ ∃ hy : y ∈ Y, π ⟨y, hy⟩ ∈ img π A₁ := by
    intro y
    simp only [Kt, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hy, hx⟩
      exact ⟨⟨y, hy⟩, hx, rfl⟩
  have hKtY : Kt ≤ Y := fun k hk => ((hKt k).1 hk).1
  have hnormKt : ∀ (y : G) (hy : y ∈ Y), π ⟨y, hy⟩ ∈ Subgroup.normalizer (img π A₁ : Set A7) →
      y ∈ Subgroup.normalizer (Kt : Set G) := by
    intro y hy hn k
    show k ∈ Kt ↔ y * k * y⁻¹ ∈ Kt
    rw [hKt, hKt]
    have hmem := Subgroup.mem_normalizer_iff.1 hn
    constructor
    · rintro ⟨hk, hkK⟩
      have hykY : y * k * y⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hy hk) (Y.inv_mem hy)
      refine ⟨hykY, ?_⟩
      have e : π ⟨y * k * y⁻¹, hykY⟩ = π ⟨y, hy⟩ * π ⟨k, hk⟩ * (π ⟨y, hy⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]; rfl
      rw [e]
      exact (hmem _).1 hkK
    · rintro ⟨hykY, hykK⟩
      have hk : k ∈ Y := by
        have := Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hykY) hy
        simpa [mul_assoc] using this
      refine ⟨hk, ?_⟩
      have e : π ⟨y * k * y⁻¹, hykY⟩ = π ⟨y, hy⟩ * π ⟨k, hk⟩ * (π ⟨y, hy⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]; rfl
      rw [e] at hykK
      exact (hmem _).2 hykK
  have hTn : ∀ (t : G) (ht : t ∈ T), π ⟨t, hH.TY ht⟩ ∈ Subgroup.normalizer (img π A₁ : Set A7) := by
    intro t ht
    have hmem : π ⟨t, hH.TY ht⟩ ∈ img π T := mem_img_of_mem (hH.TY ht) ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconj x hx _ hmem, fun hx => ?_⟩
    have := hconj _ hx _ (Subgroup.inv_mem _ hmem)
    simpa [mul_assoc] using this
  let H₁ : Subgroup G := Y ⊓ Subgroup.normalizer (Kt : Set G)
  have hTH₁ : T ≤ H₁ := fun t ht => ⟨hH.TY ht, hnormKt t (hH.TY ht) (hTn t ht)⟩
  have hKtH₁ : Kt ≤ H₁ := fun k hk => ⟨hKtY hk, Subgroup.le_normalizer hk⟩
  have hH₁n : H₁ ≤ Subgroup.normalizer (Kt : Set G) := inf_le_right
  have hTsyl₁ : IsSylowTwoOf T H₁ := by
    refine ⟨hTH₁, hH.sylow.2.1, ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex T H₁ Y hTH₁ inf_le_left
    exact fun hd => hH.sylow.2.2 (hd.trans (Dvd.intro _ h1))
  have hRsyl : IsSylowTwoOf (T ⊓ Kt) Kt := A4.isSylowTwoOf_inf_normal hTsyl₁ hKtH₁ hH₁n
  have hS_le_R : baum T ≤ T ⊓ Kt := by
    refine le_inf (C1GN.baum_le T) fun s hs => ?_
    rw [hKt]
    have hsY : s ∈ Y := hH.TY (C1GN.baum_le T hs)
    refine ⟨hsY, ?_⟩
    rw [← hS]
    exact mem_img_of_mem hsY hs
  have hbaumR : baum T = baum (T ⊓ Kt) := baum_eq_of_le hS_le_R inf_le_left
  have hfrat := exists_mul_of_sylow hKtH₁ hH₁n (inf_le_right : T ⊓ Kt ≤ Kt)
    (hH.sylow.2.1.to_le inf_le_left) hRsyl.2.2
  have hbaumcgs : Y ⊓ Subgroup.normalizer (baum T : Set G) ≤ cgsIn Y T :=
    le_cgsIn_of_char (C1GN.baum_le T) (C1GN.baum_ne_bot hH.sylow.2.1 hH.T_ne_bot)
      (C1GN.characteristic_baum T)
  have hfratY : ∀ (y : G) (hy : y ∈ Y),
      π ⟨y, hy⟩ ∈ Subgroup.normalizer (img π A₁ : Set A7) → y ∈ cgsIn Y T := by
    intro y hy hyn
    obtain ⟨n, hn, c, hc, hnc⟩ := hfrat y ⟨hy, hnormKt y hy hyn⟩
    have hnS : n ∈ Subgroup.normalizer (baum T : Set G) := by
      rw [hbaumR]
      exact normalizer_le_normalizer_baum _ hn.2
    have hn' : n ∈ cgsIn Y T := hbaumcgs ⟨hn.1.1, hnS⟩
    obtain ⟨hcY, hcK⟩ := (hKt c).1 hc
    rw [← hS] at hcK
    obtain ⟨s, hsS, hsc⟩ := mem_img.1 hcK
    have hker : π (⟨c, hcY⟩ * s⁻¹) = 1 := by rw [map_mul, map_inv, hsc, mul_inv_cancel]
    have hd := D.ker _ hker
    have hdY : c * (s : G)⁻¹ ∈ Y := Y.mul_mem hcY (Y.inv_mem s.2)
    have hd' : c * (s : G)⁻¹ ∈ cgsIn Y T :=
      hDc _ hdY (fun v hv => Subgroup.mem_centralizer_iff.1 hd v hv)
    have hs' : (s : G) ∈ cgsIn Y T := hbaumcgs ⟨s.2, Subgroup.le_normalizer hsS⟩
    have e : c = (c * (s : G)⁻¹) * s := by group
    rw [hnc, e]
    exact (cgsIn Y T).mul_mem hn' ((cgsIn Y T).mul_mem hd' hs')
  let Γ : Subgroup A7 := img π (cgsIn Y T)
  have hNΓ : Subgroup.normalizer (img π A₁ : Set A7) ≤ Γ := by
    intro x hx
    obtain ⟨y, rfl⟩ := D.surj x
    exact mem_img.2 ⟨y, hfratY y y.2 hx, rfl⟩
  obtain ⟨y₀, hy₀Y, -, hy₀c, hy₀o⟩ := exists_seven m D
  have hy₀cgs : y₀ ∈ cgsIn Y T := by
    apply hH.inf_normalizer_Z_le_cgsIn
    refine ⟨hy₀Y, ?_⟩
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    exact fun z hz => hy₀c z hz
  have h7 : 7 ∣ Nat.card Γ := by
    have hx : π ⟨y₀, hy₀Y⟩ ∈ Γ := mem_img_of_mem hy₀Y hy₀cgs
    have := Subgroup.orderOf_dvd_natCard Γ hx
    rwa [hy₀o] at this
  have h72 : 72 ∣ Nat.card Γ := by
    have h1 := Subgroup.card_dvd_of_le hNΓ
    have h2 : Nat.card (Subgroup.normalizer (img π A₁ : Set A7)) = 72 := hKk.card_normalizer
    rwa [h2] at h1
  have hΓtop : Γ = ⊤ := eq_top_of_dvd h7 h72
  intro y hy
  have hmem : π ⟨y, hy⟩ ∈ Γ := by rw [hΓtop]; trivial
  obtain ⟨g, hgc, hg⟩ := mem_img.1 hmem
  have hker : π (⟨y, hy⟩ * g⁻¹) = 1 := by rw [map_mul, map_inv, hg, mul_inv_cancel]
  have hd := D.ker _ hker
  have hdY : y * (g : G)⁻¹ ∈ Y := Y.mul_mem hy (Y.inv_mem g.2)
  have hd' : y * (g : G)⁻¹ ∈ cgsIn Y T :=
    hDc _ hdY (fun v hv => Subgroup.mem_centralizer_iff.1 hd v hv)
  have e : y = (y * (g : G)⁻¹) * g := by group
  rw [e]
  exact (cgsIn Y T).mul_mem hd' hgc

end ModCore

end CFSG.QuasithinUnique.L246.C123
