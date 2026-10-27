module

public import CFSG.GH74.GLS.IVK.L2.Involutions
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Cent

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b CFSG.GorensteinWalter

variable {G : Type} [Group G]

theorem exists_four_of_comm_invol {A : Type*} [Group A] {s w : A} (hs : s * s = 1)
    (hw : w * w = 1) (hsw : s * w = w * s) (hs1 : s ≠ 1) (hw1 : w ≠ 1) (hne : s ≠ w) :
    ∃ V : Subgroup A, Dihedral.IsEA V ∧ Nat.card V = 4 ∧
      (∀ g ∈ V, g = 1 ∨ g = s ∨ g = w ∨ g = s * w) ∧ s ∈ V ∧ w ∈ V := by
  have hws : w * s = s * w := hsw.symm
  have h1 : s * (s * w) = w := by rw [← mul_assoc, hs, one_mul]
  have h2 : w * (s * w) = s := by rw [← mul_assoc, hws, mul_assoc, hw, mul_one]
  have h3 : s * w * s = w := by rw [mul_assoc, hws, ← mul_assoc, hs, one_mul]
  have h4 : s * w * w = s := by rw [mul_assoc, hw, mul_one]
  have h5 : s * w * (s * w) = 1 := by rw [mul_assoc, h2, hs]
  let V : Subgroup A :=
    { carrier := {g | g = 1 ∨ g = s ∨ g = w ∨ g = s * w}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp [hs, hw, hws, h1, h2, h3, h4, h5]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl
        · simp
        · rw [inv_eq_of_mul_eq_one_right hs]; simp
        · rw [inv_eq_of_mul_eq_one_right hw]; simp
        · rw [inv_eq_of_mul_eq_one_right h5]; simp }
  have hmem : ∀ g, g ∈ V ↔ g = 1 ∨ g = s ∨ g = w ∨ g = s * w := fun g => Iff.rfl
  refine ⟨V, ?_, ?_, fun g hg => (hmem g).1 hg, (hmem s).2 (Or.inr (Or.inl rfl)),
    (hmem w).2 (Or.inr (Or.inr (Or.inl rfl)))⟩
  · intro a ha
    refine ⟨?_, fun b hb => ?_⟩
    · rcases (hmem a).1 ha with rfl | rfl | rfl | rfl <;> simp [hs, hw, h5]
    · rcases (hmem a).1 ha with rfl | rfl | rfl | rfl <;>
        rcases (hmem b).1 hb with rfl | rfl | rfl | rfl <;>
        first | rfl | simp | exact hsw | exact hsw.symm | rw [h1, h3] | rw [h3, h1] | rw [h2, h4]
  · have hset : (V : Set A) = {1, s, w, s * w} := by
      ext g; simp [hmem]
    have hc : Nat.card V = (V : Set A).ncard := Nat.card_coe_set_eq _
    rw [hc, hset]
    have d1 : (1 : A) ≠ s := fun h => hs1 h.symm
    have d2 : (1 : A) ≠ w := fun h => hw1 h.symm
    have d3 : (1 : A) ≠ s * w := fun h => hne (by
      have h' := mul_eq_one_iff_eq_inv.1 h.symm
      rw [h', inv_eq_of_mul_eq_one_right hw])
    have d5 : s ≠ s * w := fun h => hw1 (mul_left_cancel (a := s) (by rw [mul_one]; exact h)).symm
    have d6 : w ≠ s * w := fun h => hs1 (mul_right_cancel (b := w) (by rw [one_mul]; exact h)).symm
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair d6]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, d5⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨d1, d2, d3⟩

theorem exists_four_PGL2 {F₀ : Type} [Field F₀] [Finite F₀] (hodd : Odd (Nat.card F₀)) :
    ∃ V : Subgroup (PGL2 F₀), Dihedral.IsEA V ∧ Nat.card V = 4 := by
  obtain ⟨U, s, w, -, -, hsU, hs2, hs1, hwU, hw2, hinv, -, -⟩ := IVK.torus_data hodd 1 (Or.inl rfl)
  have hsw : s * w = w * s := by
    have := hinv s hsU
    rw [inv_eq_of_mul_eq_one_right hs2] at this
    calc s * w = (w * s * w⁻¹) * w := by rw [this]
      _ = w * s := by group
  have hw1 : w ≠ 1 := fun h => hwU (h ▸ U.one_mem)
  have hne : s ≠ w := fun h => hwU (h ▸ hsU)
  obtain ⟨V, hV, hc, -⟩ := exists_four_of_comm_invol hs2 hw2 hsw hs1 hw1 hne
  exact ⟨V, hV, hc⟩

theorem isEA_map_hom {X Y : Type*} [Group X] [Group Y] {V : Subgroup X} (f : X →* Y)
    (hV : Dihedral.IsEA V) : Dihedral.IsEA (V.map f) := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [← map_mul, (hV a ha).1, map_one]
  · rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, (hV a ha).2 b hb]

theorem card_map_mk_of_inf_eq_bot {C : Type*} [Group C] (N : Subgroup C) [N.Normal]
    (A : Subgroup C) (h : A ⊓ N = ⊥) :
    Nat.card (A.map (QuotientGroup.mk' N)) = Nat.card A := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun a : A => (⟨QuotientGroup.mk' N a, a, a.2, rfl⟩ : A.map (QuotientGroup.mk' N))) ⟨?_, ?_⟩)
  · intro a b hab
    have h1 : (QuotientGroup.mk' N) (a : C) = (QuotientGroup.mk' N) (b : C) :=
      congrArg Subtype.val hab
    have h2 : (a : C)⁻¹ * b ∈ N := by
      rw [← QuotientGroup.eq]; exact h1
    have h3 : (a : C)⁻¹ * b ∈ A ⊓ N := ⟨A.mul_mem (A.inv_mem a.2) b.2, h2⟩
    rw [h, Subgroup.mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.1 h3)
  · rintro ⟨y, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem exists_lift_elemAb [Finite G] (x : G) {Eb : Subgroup (CentralizerBar x)}
    (hEb : Dihedral.IsEA Eb) :
    ∃ E : Subgroup G, E ≤ Cx x ∧ IsElemAb2 E ∧ Nat.card E = Nat.card Eb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥Eb := fun g => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using (hEb g g.2).1⟩
  obtain ⟨A, -, hAE, hAN⟩ := exists_lift_pSubgroup (Ox x) (Ox_odd x) Eb hp
  have hker : ∀ a ∈ A, QuotientGroup.mk' (Ox x) a = 1 → a = 1 := by
    intro a ha h1
    have : a ∈ A ⊓ Ox x := ⟨ha, (QuotientGroup.eq_one_iff a).1 h1⟩
    rw [hAN, Subgroup.mem_bot] at this
    exact this
  have hmemE : ∀ a ∈ A, QuotientGroup.mk' (Ox x) a ∈ Eb := fun a ha => hAE ▸ ⟨a, ha, rfl⟩
  refine ⟨A.map (Cx x).subtype, fun g ⟨a, _, hag⟩ => hag ▸ a.2, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, ?_⟩
    · have : a * a = 1 := hker _ (A.mul_mem ha ha) (by
        rw [map_mul]; exact (hEb _ (hmemE a ha)).1)
      simpa using congrArg Subtype.val this
    · rintro _ ⟨b, hb, rfl⟩
      have : a * b * (b * a)⁻¹ = 1 := hker _ (A.mul_mem (A.mul_mem ha hb) (A.inv_mem (A.mul_mem hb ha)))
        (by rw [map_mul, map_mul, map_inv, map_mul, (hEb _ (hmemE a ha)).2 _ (hmemE b hb)]; group)
      have h2 := mul_inv_eq_one.1 this
      simpa using congrArg Subtype.val h2
  · rw [Subgroup.card_map_of_injective (Cx x).subtype_injective, ← hAE]
    exact (card_map_mk_of_inf_eq_bot (Ox x) A hAN).symm

variable [Finite G] {x : G} {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]
  {F : Type} [Field F] [Finite F] {e : ↥Kb ≃* IVK.L2 F} {N : IVK.L2Notation e} {T : Subgroup G}

theorem ip_outer (h : SitFacts x Kb e N T) (h12hc : IVK.IVK_1_2h_c) (h14a : IVK.IVK_1_4a)
    (hx : x * x = 1) (hx1 : x ≠ 1) : IP_outer x T (Rdg x Kb e T) := by
  intro u huT hu2 huRd
  have huC := h.T_le_C huT
  have hconj := IVK.conj_injective_of_L2 e
  have hD : (IVK.innDiagSub e).Normal := IVK.innDiagSub_normal e
  have hFD := IVK.innDiagSub_inf_fieldAutSub e
  have hDF := IVK.innDiagSub_sup_fieldAutSub e
  have hxT : x ∈ T := x_mem_of_sylow x h.sylow hx hx1
  set ub : MulAut ↥Kb := phig x Kb u with hub
  have hub2 : ub * ub = 1 := by rw [hub, ← phig_mul x Kb huC huC, hu2, phig_one]
  have hubD : ub ∉ IVK.innDiagSub e := fun hd => huRd ⟨huT, huC, hd⟩
  have hub1 : ub ≠ 1 := fun h1 => hubD (h1 ▸ one_mem _)
  have hubord : orderOf ub = 2 := orderOf_eq_prime (by rw [pow_two]; exact hub2) hub1
  obtain ⟨d, hd, f, hf, hdf⟩ := Subgroup.mem_sup_of_normal_left.1
    (show ub ∈ IVK.innDiagSub e ⊔ IVK.fieldAutSub e by rw [hDF]; exact Subgroup.mem_top _)
  have hfD : f ∉ IVK.innDiagSub e := fun hfd => hubD (by rw [← hdf]; exact mul_mem hd hfd)
  have hff : f * f = 1 := by
    have h1 : f * f ∈ IVK.innDiagSub e := by
      have e1 : f * f = d⁻¹ * (ub * ub) * (f⁻¹ * d⁻¹ * f) := by rw [← hdf]; group
      rw [e1, hub2, mul_one]
      have := hD.conj_mem d⁻¹ (inv_mem hd) f⁻¹
      simp only [inv_inv] at this
      exact mul_mem (inv_mem hd) this
    have h2 : f * f ∈ IVK.innDiagSub e ⊓ IVK.fieldAutSub e := ⟨h1, mul_mem hf hf⟩
    rw [hFD] at h2
    exact h2
  have hf1 : f ≠ 1 := fun h1 => hfD (h1 ▸ one_mem _)
  have hford : orderOf f = 2 := orderOf_eq_prime (by rw [pow_two]; exact hff) hf1
  have hfT : f ∈ (N.T : Subgroup (MulAut ↥Kb)) := by
    have hp : IsPGroup 2 ↥(Subgroup.zpowers f) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hford]; norm_num)
    have hs := hp.inf_normalizer_sylow N.T
    have hmem : f ∈ Subgroup.zpowers f ⊓ Subgroup.normalizer (N.T : Set (MulAut ↥Kb)) :=
      ⟨Subgroup.mem_zpowers f, N.T_inv hf⟩
    rw [hs] at hmem
    exact hmem.2
  obtain ⟨c, hc, hcf⟩ := h12hc F h.hF ↥Kb e N f ⟨hfT, hf⟩ hford d hd
    (by rw [hdf]; exact hubord)
  have hubc : ub = c⁻¹ * f * c := by
    calc ub = c⁻¹ * (c * (d * f) * c⁻¹) * c := by rw [hdf]; group
      _ = c⁻¹ * f * c := by rw [hcf]
  obtain ⟨σ, hσ⟩ := (hf : f ∈ (IVK.fieldAutHom e).range)
  have hσ2 : orderOf σ = 2 := by
    rw [← hford, ← hσ]
    exact (orderOf_injective (IVK.fieldAutHom e) (IVK.fieldAutHom_injective e) σ).symm
  obtain ⟨F₀, _, _, hF₀, ⟨φ₀⟩⟩ := (h14a F h.hF ↥Kb e σ).2.2 (by rw [hσ2]; exact even_two)
  have hodd₀ : Odd (Nat.card F₀) := by
    have h1 : Odd (Nat.card F) := h.hF.1
    rw [← hF₀, hσ2, pow_two] at h1
    exact (Nat.odd_mul.1 h1).1
  obtain ⟨V₀, hV₀, hc₀⟩ := exists_four_PGL2 hodd₀
  let fixf := fixedSubgroup ↥Kb (IVK.fieldAutHom e σ)
  let V₁ : Subgroup ↥Kb := (V₀.map φ₀.symm.toMonoidHom).map fixf.subtype
  have hV₁ : Dihedral.IsEA V₁ := isEA_map_hom _ (isEA_map_hom _ hV₀)
  have hc₁ : Nat.card V₁ = 4 := by
    rw [Subgroup.card_map_of_injective fixf.subtype_injective,
      Subgroup.card_map_of_injective φ₀.symm.injective]
    exact hc₀
  have hfix₁ : ∀ v ∈ V₁, (IVK.fieldAutHom e σ) v = v := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hcc : ∀ k : ↥Kb, c (c⁻¹ k) = k := fun k => by simp
  let V₂ : Subgroup ↥Kb := V₁.map (c⁻¹ : MulAut ↥Kb).toMonoidHom
  have hV₂ : Dihedral.IsEA V₂ := isEA_map_hom _ hV₁
  have hc₂ : Nat.card V₂ = 4 := by
    rw [Subgroup.card_map_of_injective (c⁻¹ : MulAut ↥Kb).injective]; exact hc₁
  have hfix₂ : ∀ v ∈ V₂, ub v = v := by
    rintro _ ⟨v₁, hv₁, rfl⟩
    show ub (c⁻¹ v₁) = c⁻¹ v₁
    rw [hubc]
    show c⁻¹ (f (c (c⁻¹ v₁))) = c⁻¹ v₁
    rw [hcc, ← hσ, hfix₁ v₁ hv₁]
  let Vb : Subgroup (CentralizerBar x) := V₂.map Kb.subtype
  have hVb : Dihedral.IsEA Vb := isEA_map_hom _ hV₂
  have hcb : Nat.card Vb = 4 := by
    rw [Subgroup.card_map_of_injective Kb.subtype_injective]; exact hc₂
  have hVbK : ∀ g ∈ Vb, g ∈ Kb := by
    rintro _ ⟨v, -, rfl⟩
    exact v.2
  have hcommU : ∀ g ∈ Vb, pr x u * g = g * pr x u := by
    rintro _ ⟨v, hv, rfl⟩
    have h1 := phig_apply x Kb u v
    rw [hfix₂ v hv] at h1
    have h2 : pr x u * (v : CentralizerBar x) * (pr x u)⁻¹ = (v : CentralizerBar x) := h1.symm
    calc pr x u * (v : CentralizerBar x) = (pr x u * (v : CentralizerBar x) * (pr x u)⁻¹) * pr x u := by
          group
      _ = (v : CentralizerBar x) * pr x u := by rw [h2]
  have ha2 : pr x u * pr x u = 1 := by rw [← pr_mul x huC huC, hu2, pr_one]
  have hb2 : pr x x * pr x x = 1 := by rw [← pr_mul x (x_mem_Cx x) (x_mem_Cx x), hx, pr_one]
  have hab : pr x u * pr x x = pr x x * pr x u := (pr_x_central x (pr x u)).symm
  have hu1 : u ≠ 1 := fun h1 => huRd (h1 ▸ (Rdg x Kb e T).one_mem)
  have ha1 : pr x u ≠ 1 := fun h1 => hu1 (eq_one_of_pr_eq_one x h.sylow huT huC h1)
  have hb1 : pr x x ≠ 1 := fun h1 => hx1 (eq_one_of_pr_eq_one x h.sylow hxT (x_mem_Cx x) h1)
  have hne : pr x u ≠ pr x x := by
    intro h1
    apply huRd
    have h2 : u * x⁻¹ = 1 := by
      apply eq_one_of_pr_eq_one x h.sylow (T.mul_mem huT (T.inv_mem hxT))
        (mul_mem huC (inv_mem (x_mem_Cx x)))
      rw [pr_mul x huC (inv_mem (x_mem_Cx x)), pr_inv x (x_mem_Cx x), h1, mul_inv_cancel]
    have : u = x := mul_inv_eq_one.1 h2
    rw [this]
    exact SitFacts.Qg_le_Rd (h.x_mem_Q hx hx1)
  obtain ⟨D₁, hD₁, hc₁', hD₁el, haD, hbD⟩ := exists_four_of_comm_invol ha2 hb2 hab ha1 hb1 hne
  have hcomm : ∀ g ∈ D₁, ∀ v ∈ Vb, g * v = v * g := by
    intro g hg v hv
    rcases hD₁el g hg with rfl | rfl | rfl | rfl
    · simp
    · exact hcommU v hv
    · exact pr_x_central x v
    · calc pr x u * pr x x * v = pr x u * (pr x x * v) := by rw [mul_assoc]
        _ = pr x u * (v * pr x x) := by rw [pr_x_central x v]
        _ = (pr x u * v) * pr x x := by rw [← mul_assoc]
        _ = (v * pr x u) * pr x x := by rw [hcommU v hv]
        _ = v * (pr x u * pr x x) := by rw [mul_assoc]
  have hinter : D₁ ⊓ Vb = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgD, hgV⟩
    have hgK := hVbK g hgV
    rw [Subgroup.mem_bot]
    rcases hD₁el g hgD with rfl | rfl | rfl | rfl
    · rfl
    · exfalso
      apply hubD
      exact IVK.innAut_le_innDiagSub e (SitFacts.phig_mem_inn ((mem_Kg x Kb).2 ⟨huC, hgK⟩))
    · exfalso
      apply hx1
      have hxK : x ∈ Kg x Kb := (mem_Kg x Kb).2 ⟨x_mem_Cx x, hgK⟩
      have := Pg_inf_Qg x Kb hconj h.sylow
      have hmem : x ∈ Pg x Kb T ⊓ Qg x Kb T := ⟨⟨hxT, hxK⟩, h.x_mem_Q hx hx1⟩
      rw [this, Subgroup.mem_bot] at hmem
      exact hmem
    · exfalso
      apply hubD
      have hux : u * x ∈ Kg x Kb := (mem_Kg x Kb).2 ⟨mul_mem huC (x_mem_Cx x), by
        rw [pr_mul x huC (x_mem_Cx x)]; exact hgK⟩
      have h1 := IVK.innAut_le_innDiagSub e (SitFacts.phig_mem_inn hux)
      rwa [phig_mul x Kb huC (x_mem_Cx x), phig_x_eq_one x Kb, mul_one] at h1
  let ψ : ↥D₁ × ↥Vb →* CentralizerBar x :=
    MonoidHom.noncommCoprod D₁.subtype Vb.subtype (fun m n => hcomm m m.2 n n.2)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨m, n⟩ hmn
    have h1 : (m : CentralizerBar x) * n = 1 := hmn
    have h2 : (m : CentralizerBar x) = (n : CentralizerBar x)⁻¹ := mul_eq_one_iff_eq_inv.1 h1
    have h3 : (m : CentralizerBar x) ∈ D₁ ⊓ Vb := ⟨m.2, h2 ▸ Vb.inv_mem n.2⟩
    rw [hinter, Subgroup.mem_bot] at h3
    have hm1 : m = 1 := Subtype.ext h3
    have hn1 : (n : CentralizerBar x) = 1 := by
      rw [h3, one_mul] at h1; exact h1
    exact Prod.ext hm1 (Subtype.ext hn1)
  have hEb : Dihedral.IsEA ψ.range := by
    rintro _ ⟨⟨m, n⟩, rfl⟩
    have hmm : (m : CentralizerBar x) * m = 1 := (hD₁ m m.2).1
    have hnn : (n : CentralizerBar x) * n = 1 := (hVb n n.2).1
    have hmn : (m : CentralizerBar x) * n = n * m := hcomm m m.2 n n.2
    refine ⟨?_, ?_⟩
    · show (m : CentralizerBar x) * n * ((m : CentralizerBar x) * n) = 1
      calc (m : CentralizerBar x) * n * (m * n) = m * (n * m) * n := by simp only [mul_assoc]
        _ = m * (m * n) * n := by rw [← hmn]
        _ = (m * m) * (n * n) := by simp only [mul_assoc]
        _ = 1 := by rw [hmm, hnn, mul_one]
    · rintro _ ⟨⟨m', n'⟩, rfl⟩
      show (m : CentralizerBar x) * n * ((m' : CentralizerBar x) * n') =
        (m' : CentralizerBar x) * n' * ((m : CentralizerBar x) * n)
      have c1 : (m : CentralizerBar x) * m' = m' * m := (hD₁ m m.2).2 m' m'.2
      have c2 : (n : CentralizerBar x) * n' = n' * n := (hVb n n.2).2 n' n'.2
      have c3 : (m : CentralizerBar x) * n' = n' * m := hcomm m m.2 n' n'.2
      have c4 : (m' : CentralizerBar x) * n = n * m' := hcomm m' m'.2 n n.2
      calc (m : CentralizerBar x) * n * (m' * n') = m * (n * m') * n' := by simp only [mul_assoc]
        _ = m * (m' * n) * n' := by rw [← c4]
        _ = (m * m') * (n * n') := by simp only [mul_assoc]
        _ = (m' * m) * (n' * n) := by rw [c1, c2]
        _ = m' * (m * n') * n := by simp only [mul_assoc]
        _ = m' * (n' * m) * n := by rw [c3]
        _ = m' * n' * (m * n) := by simp only [mul_assoc]
  have hcardEb : Nat.card ψ.range = 16 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, Nat.card_prod, hc₁', hcb]
  obtain ⟨E, hEC, hE, hEcard⟩ := exists_lift_elemAb x hEb
  exact ⟨E, hEC, hE, by rw [hEcard, hcardEb]⟩

end CFSG.GH74.GLS.Stage1.Thm6.Glue
