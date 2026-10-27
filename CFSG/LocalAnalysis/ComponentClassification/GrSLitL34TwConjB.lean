module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwDefs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four

private theorem mem_wrR {x : WrE} : x ∈ wrR ↔ x.a ∈ R ∧ x.b ∈ R := Iff.rfl

private theorem mem_ssS {x : WrE} : x ∈ ssS ↔ x.e = false ∧ x.a ∈ S ∧ x.b ∈ S := Iff.rfl

private theorem conj_e (c x : WrE) : (c * x * c⁻¹).e = x.e := by
  rcases c with ⟨c₁, c₂, ce⟩
  rcases x with ⟨x₁, x₂, xe⟩
  cases ce <;> cases xe <;> rfl

private theorem conj_of_e_false_a {c x : WrE} (hx : x.e = false) (hc : c.e = false) :
    c * x * c⁻¹ = ⟨c.a * x.a * c.a⁻¹, c.b * x.b * c.b⁻¹, false⟩ := by
  rcases c with ⟨c₁, c₂, ce⟩
  rcases x with ⟨x₁, x₂, xe⟩
  have hx' : xe = false := hx
  have hc' : ce = false := hc
  subst hx' hc'
  rfl

private theorem conj_of_e_false_b {c x : WrE} (hx : x.e = false) (hc : c.e = true) :
    c * x * c⁻¹ = ⟨c.b * x.b * c.b⁻¹, c.a * x.a * c.a⁻¹, false⟩ := by
  rcases c with ⟨c₁, c₂, ce⟩
  rcases x with ⟨x₁, x₂, xe⟩
  have hx' : xe = false := hx
  have hc' : ce = true := hc
  subst hx' hc'
  rfl

private theorem sq_e {g : WrE} (hg : g.e = true) : (g * g).e = false := by
  rcases g with ⟨g₁, g₂, ge⟩
  have : ge = true := hg
  subst this
  rfl

private theorem sq_a_eq {g : WrE} (hg : g.e = true) : (g * g).a = g.b * (g * g).b * g.b⁻¹ := by
  rcases g with ⟨g₁, g₂, ge⟩
  have : ge = true := hg
  subst this
  show g₂ * g₁ = g₂ * (g₁ * g₂) * g₂⁻¹
  group

private theorem conj_mul' (c a b : WrE) : c * a * c⁻¹ * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by
  group

private theorem conj_pow' (c x : WrE) (n : ℕ) : (c * x * c⁻¹) ^ n = c * x ^ n * c⁻¹ :=
  _root_.conj_pow

private theorem conj_inj {c x y : WrE} (h : c * x * c⁻¹ = c * y * c⁻¹) : x = y := by
  simpa using h

private theorem conj_ne_one {c x : WrE} (h : c * x * c⁻¹ ≠ 1) : x ≠ 1 :=
  fun h1 => h (by rw [h1]; simp)

private theorem conj_sq_eq_one {c x : WrE} (h : c * x * c⁻¹ * (c * x * c⁻¹) = 1) : x * x = 1 := by
  rw [conj_mul'] at h
  exact _root_.conj_eq_one_iff.1 h

private theorem orderOf_conj' (c x : WrE) : orderOf (c * x * c⁻¹) = orderOf x := by
  have := (MulAut.conj c).orderOf_eq x
  simpa [MulAut.conj_apply] using this

private theorem conj_comm_iff {c a y : WrE} :
    c * a * c⁻¹ * (c * y * c⁻¹) = c * y * c⁻¹ * (c * a * c⁻¹) ↔ a * y = y * a := by
  rw [conj_mul', conj_mul']
  exact ⟨conj_inj, fun h => by rw [h]⟩

private theorem conj_conj_inv {c x : WrE} : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group

private theorem inS_conj {r y : Equiv.Perm (Fin 42)} (hr : r ∈ R) :
    r * y * r⁻¹ ∈ S ↔ y ∈ S := ⟨conj_mem_S' hr, conj_mem_S hr⟩

private theorem isUni_conj {r y : Equiv.Perm (Fin 42)} (hr : r ∈ R) (h : isUni y) :
    isUni (r * y * r⁻¹) := by
  obtain ⟨d, hd, rfl⟩ := h
  exact ⟨r * d, R.mul_mem hr hd, by group⟩

theorem isA_conj {x c : WrE} (hc : c ∈ wrR) (h : IsA x) :
    IsA (c * x * c⁻¹) := by
  obtain ⟨hxe, hx2, hcase⟩ := h
  have hc1 : c.a ∈ R := (mem_wrR.1 hc).1
  have hc2 : c.b ∈ R := (mem_wrR.1 hc).2
  refine ⟨by rw [conj_e]; exact hxe, by rw [conj_mul', hx2]; simp, ?_⟩
  cases hce : c.e
  · rw [conj_of_e_false_a hxe hce]
    rcases hcase with ⟨ha, hb, hbS⟩ | ⟨hb, ha, haS⟩
    · exact Or.inl ⟨by simp [ha], fun h => hb (_root_.conj_eq_one_iff.1 h), (inS_conj hc2).2 hbS⟩
    · exact Or.inr ⟨by simp [hb], fun h => ha (_root_.conj_eq_one_iff.1 h), (inS_conj hc1).2 haS⟩
  · rw [conj_of_e_false_b hxe hce]
    rcases hcase with ⟨ha, hb, hbS⟩ | ⟨hb, ha, haS⟩
    · exact Or.inr ⟨by simp [ha], fun h => hb (_root_.conj_eq_one_iff.1 h), (inS_conj hc2).2 hbS⟩
    · exact Or.inl ⟨by simp [hb], fun h => ha (_root_.conj_eq_one_iff.1 h), (inS_conj hc1).2 haS⟩

theorem isD_conj {x c : WrE} (hc : c ∈ wrR) (h : IsD x) :
    IsD (c * x * c⁻¹) := by
  obtain ⟨hxe, hx2, ha1, hb1, haS, hbS⟩ := h
  have hc1 : c.a ∈ R := (mem_wrR.1 hc).1
  have hc2 : c.b ∈ R := (mem_wrR.1 hc).2
  refine ⟨by rw [conj_e]; exact hxe, by rw [conj_mul', hx2]; simp, ?_⟩
  cases hce : c.e
  · rw [conj_of_e_false_a hxe hce]
    exact ⟨fun h => ha1 (_root_.conj_eq_one_iff.1 h), fun h => hb1 (_root_.conj_eq_one_iff.1 h),
      (inS_conj hc1).2 haS, (inS_conj hc2).2 hbS⟩
  · rw [conj_of_e_false_b hxe hce]
    exact ⟨fun h => hb1 (_root_.conj_eq_one_iff.1 h), fun h => ha1 (_root_.conj_eq_one_iff.1 h),
      (inS_conj hc2).2 hbS, (inS_conj hc1).2 haS⟩

theorem isUU_conj {x c : WrE} (hc : c ∈ wrR) (h : IsUU x) :
    IsUU (c * x * c⁻¹) := by
  obtain ⟨hxe, hx2, ha, hb⟩ := h
  have hc1 : c.a ∈ R := (mem_wrR.1 hc).1
  have hc2 : c.b ∈ R := (mem_wrR.1 hc).2
  refine ⟨by rw [conj_e]; exact hxe, by rw [conj_mul', hx2]; simp, ?_⟩
  cases hce : c.e
  · rw [conj_of_e_false_a hxe hce]
    exact ⟨isUni_conj hc1 ha, isUni_conj hc2 hb⟩
  · rw [conj_of_e_false_b hxe hce]
    exact ⟨isUni_conj hc2 hb, isUni_conj hc1 ha⟩

private theorem isA_conj_iff {x c : WrE} (hc : c ∈ wrR) :
    IsA (c * x * c⁻¹) ↔ IsA x := by
  refine ⟨fun h => ?_, isA_conj hc⟩
  have := isA_conj (wrR.inv_mem hc) h
  rwa [conj_conj_inv] at this

private theorem isUU_conj_iff {x c : WrE} (hc : c ∈ wrR) :
    IsUU (c * x * c⁻¹) ↔ IsUU x := by
  refine ⟨fun h => ?_, isUU_conj hc⟩
  have := isUU_conj (wrR.inv_mem hc) h
  rwa [conj_conj_inv] at this

private theorem ssS_conj_mem {c x : WrE} (hc : c ∈ wrR)
    (hx : x ∈ ssS) : c * x * c⁻¹ ∈ ssS := by
  obtain ⟨hxe, hxa, hxb⟩ := mem_ssS.1 hx
  have hc1 : c.a ∈ R := (mem_wrR.1 hc).1
  have hc2 : c.b ∈ R := (mem_wrR.1 hc).2
  cases hce : c.e
  · rw [conj_of_e_false_a hxe hce]
    exact mem_ssS.2 ⟨rfl, conj_mem_S hc1 hxa, conj_mem_S hc2 hxb⟩
  · rw [conj_of_e_false_b hxe hce]
    exact mem_ssS.2 ⟨rfl, conj_mem_S hc2 hxb, conj_mem_S hc1 hxa⟩

namespace ConjCS

@[expose] def cs (c : WrE) (X : Subgroup WrE) : Subgroup WrE :=
  X.map (MulAut.conj c).toMonoidHom

theorem mem_cs_iff {c y : WrE} {X : Subgroup WrE} : y ∈ cs c X ↔ ∃ x ∈ X, c * x * c⁻¹ = y := by
  simp [cs, Subgroup.mem_map, MulAut.conj_apply]

theorem mem_cs {c y : WrE} {X : Subgroup WrE} : y ∈ cs c X ↔ c⁻¹ * y * c ∈ X := by
  unfold cs
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem conj_mem_cs {c x : WrE} {X : Subgroup WrE} (hx : x ∈ X) : c * x * c⁻¹ ∈ cs c X :=
  mem_cs_iff.2 ⟨x, hx, rfl⟩

theorem cs_cs (c d : WrE) (X : Subgroup WrE) : cs c (cs d X) = cs (c * d) X := by
  ext y
  rw [mem_cs, mem_cs, mem_cs]
  have : (c * d)⁻¹ * y * (c * d) = d⁻¹ * (c⁻¹ * y * c) * d := by group
  rw [this]

theorem cs_one (X : Subgroup WrE) : cs 1 X = X := by
  ext y
  rw [mem_cs]
  simp

theorem cs_inv_cs (c : WrE) (X : Subgroup WrE) : cs c⁻¹ (cs c X) = X := by
  rw [cs_cs, inv_mul_cancel, cs_one]

theorem cs_cs_inv (c : WrE) (X : Subgroup WrE) : cs c (cs c⁻¹ X) = X := by
  rw [cs_cs, mul_inv_cancel, cs_one]

theorem card_cs (c : WrE) (X : Subgroup WrE) : Nat.card ↥(cs c X) = Nat.card ↥X :=
  Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective

theorem cs_mono {c : WrE} {X Y : Subgroup WrE} (h : X ≤ Y) : cs c X ≤ cs c Y :=
  Subgroup.map_mono h

theorem cs_inf (c : WrE) (X Y : Subgroup WrE) : cs c (X ⊓ Y) = cs c X ⊓ cs c Y :=
  Subgroup.map_inf X Y (MulAut.conj c).toMonoidHom (MulAut.conj c).injective

theorem cs_centralizer (c b : WrE) :
    cs c (centralizer ({b} : Set WrE)) = centralizer ({c * b * c⁻¹} : Set WrE) := by
  ext y
  rw [mem_cs, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * (c * b * c⁻¹) = c * ((c⁻¹ * y * c) * b) * c⁻¹ := by group
      _ = c * (b * (c⁻¹ * y * c)) * c⁻¹ := by rw [h]
      _ = c * b * c⁻¹ * y := by group
  · intro h
    calc c⁻¹ * y * c * b = c⁻¹ * (y * (c * b * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * b * c⁻¹ * y) * c := by rw [h]
      _ = b * (c⁻¹ * y * c) := by group

theorem cs_inf_centralizer (c : WrE) (X : Subgroup WrE) (z : WrE) :
    cs c X ⊓ centralizer ({c * z * c⁻¹} : Set WrE) = cs c (X ⊓ centralizer ({z} : Set WrE)) := by
  rw [cs_inf, cs_centralizer]

theorem cs_inf3 (c : WrE) (X : Subgroup WrE) (a y : WrE) :
    cs c X ⊓ centralizer ({c * a * c⁻¹} : Set WrE) ⊓ centralizer ({c * y * c⁻¹} : Set WrE) =
      cs c (X ⊓ centralizer ({a} : Set WrE) ⊓ centralizer ({y} : Set WrE)) := by
  rw [cs_inf, cs_inf, cs_centralizer, cs_centralizer]

theorem exists_of_le_cs {c : WrE} {Y E : Subgroup WrE} (h : E ≤ cs c Y) :
    ∃ F : Subgroup WrE, F ≤ Y ∧ cs c F = E := by
  refine ⟨cs c⁻¹ E, ?_, cs_cs_inv c E⟩
  have := cs_mono (c := c⁻¹) h
  rwa [cs_inv_cs] at this

theorem isElemTwo_cs {c : WrE} {F : Subgroup WrE} :
    GrSLit.IsElemTwo (cs c F) ↔ GrSLit.IsElemTwo F := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · have := h1 _ (conj_mem_cs hx) _ (conj_mem_cs hy)
      rw [conj_mul', conj_mul'] at this
      exact conj_inj this
    · have := h2 _ (conj_mem_cs hx)
      rw [conj_mul'] at this
      exact _root_.conj_eq_one_iff.1 this
  · rintro ⟨h1, h2⟩
    refine ⟨fun x' hx' y' hy' => ?_, fun x' hx' => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := mem_cs_iff.1 hx'
      obtain ⟨y, hy, rfl⟩ := mem_cs_iff.1 hy'
      rw [conj_mul', conj_mul', h1 x hx y hy]
    · obtain ⟨x, hx, rfl⟩ := mem_cs_iff.1 hx'
      rw [conj_mul', h2 x hx]
      simp

theorem isEightGroup_cs {c : WrE} {F : Subgroup WrE} :
    GrSLit.IsEightGroup (cs c F) ↔ GrSLit.IsEightGroup F := by
  unfold GrSLit.IsEightGroup
  rw [isElemTwo_cs, card_cs]

private theorem cs_ssS {c : WrE} (hc : c ∈ wrR) :
    cs c ssS = ssS := by
  ext y
  rw [mem_cs]
  constructor
  · intro h
    have := ssS_conj_mem hc h
    rwa [show c * (c⁻¹ * y * c) * c⁻¹ = y by group] at this
  · intro h
    have := ssS_conj_mem (wrR.inv_mem hc) h
    rwa [inv_inv] at this

theorem goodX_cs {X : Subgroup WrE} (hX : GoodX X) {c : WrE}
    (hc : c ∈ wrR) : GoodX (cs c X) where
  le_wrR := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_cs_iff.1 hy
    exact wrR.mul_mem (wrR.mul_mem hc (hX.le_wrR hx)) (wrR.inv_mem hc)
  two := hX.two.map (MulAut.conj c).toMonoidHom
  card_ss := by
    rw [← cs_ssS hc, ← cs_inf, card_cs]
    exact hX.card_ss
  swap := by
    obtain ⟨g, hg, hge⟩ := hX.swap
    exact ⟨c * g * c⁻¹, conj_mem_cs hg, by rw [conj_e]; exact hge⟩
  h13 := by
    intro g' hg' hge
    obtain ⟨g, hg, rfl⟩ := mem_cs_iff.1 hg'
    rw [conj_e] at hge
    intro h1
    apply hX.h13 g hg hge
    exact conj_sq_eq_one h1
  h14 := by
    obtain ⟨g, hg, hge, hg4⟩ := hX.h14
    refine ⟨c * g * c⁻¹, conj_mem_cs hg, by rw [conj_e]; exact hge, ?_⟩
    rw [conj_pow', hg4]
    simp
  h20 := by
    intro g' hg' hge
    obtain ⟨g, hg, rfl⟩ := mem_cs_iff.1 hg'
    rw [conj_e] at hge
    have hgw : g ∈ wrR := hX.le_wrR hg
    have h0 := hX.h20 g hg hge
    have hyE : (g * g).e = false := sq_e hge
    rw [conj_mul']
    cases hce : c.e
    · rw [conj_of_e_false_a hyE hce]
      intro hS
      exact h0 ((inS_conj (mem_wrR.1 hc).1).1 hS)
    · rw [conj_of_e_false_b hyE hce]
      intro hS
      have hb : (g * g).b ∈ S := (inS_conj (mem_wrR.1 hc).2).1 hS
      apply h0
      rw [sq_a_eq hge]
      exact conj_mem_S (mem_wrR.1 hgw).2 hb
  h22 := by
    intro g' hg' hge hmin
    obtain ⟨g, hg, rfl⟩ := mem_cs_iff.1 hg'
    rw [conj_e] at hge
    have hmin' : ∀ h ∈ X, h.e = true → orderOf g ≤ orderOf h := by
      intro h hh hhe
      have := hmin (c * h * c⁻¹) (conj_mem_cs hh) (by rw [conj_e]; exact hhe)
      rwa [orderOf_conj', orderOf_conj'] at this
    rintro ⟨F', hF', hF8, w', hw', hw2, hwF, hwnot⟩
    rw [conj_mul', cs_inf_centralizer] at hF' hw'
    obtain ⟨F, hFle, rfl⟩ := exists_of_le_cs hF'
    refine hX.h22 g hg hge hmin'
      ⟨F, hFle, isEightGroup_cs.1 hF8, c⁻¹ * w' * c, mem_cs.1 hw', ?_, ?_, ?_⟩
    · rw [show c⁻¹ * w' * c * (c⁻¹ * w' * c) = c⁻¹ * (w' * w') * c by group, hw2]
      group
    · intro e he
      have h1 := hwF (c * e * c⁻¹) (conj_mem_cs he)
      calc c⁻¹ * w' * c * e = c⁻¹ * (w' * (c * e * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * e * c⁻¹ * w') * c := by rw [h1]
        _ = e * (c⁻¹ * w' * c) := by group
    · intro hmem
      apply hwnot
      have h2 := conj_mem_cs (c := c) hmem
      rwa [show c * (c⁻¹ * w' * c) * c⁻¹ = w' by group] at h2

theorem concX_cs {X : Subgroup WrE} (hX : ConcX X) {c : WrE}
    (hc : c ∈ wrR) : ConcX (cs c X) where
  d_central := by
    obtain ⟨d, hd, hdc, hdD⟩ := hX.d_central
    refine ⟨c * d * c⁻¹, conj_mem_cs hd, fun x' hx' => ?_, isD_conj hc hdD⟩
    obtain ⟨x, hx, rfl⟩ := mem_cs_iff.1 hx'
    rw [conj_mul', conj_mul', hdc x hx]
  swap_min := by
    intro g' hg' hge hmin
    obtain ⟨g, hg, rfl⟩ := mem_cs_iff.1 hg'
    rw [conj_e] at hge
    have hmin' : ∀ h ∈ X, h.e = true → orderOf g ≤ orderOf h := by
      intro h hh hhe
      have := hmin (c * h * c⁻¹) (conj_mem_cs hh) (by rw [conj_e]; exact hhe)
      rwa [orderOf_conj', orderOf_conj'] at this
    obtain ⟨h4, hU⟩ := hX.swap_min g hg hge hmin'
    refine ⟨?_, ?_⟩
    · rw [conj_pow', h4]
      simp
    · rw [conj_mul']
      exact isUU_conj hc hU
  inv_types := by
    intro x' hx' hx2 hx1
    obtain ⟨x, hx, rfl⟩ := mem_cs_iff.1 hx'
    rcases hX.inv_types x hx (conj_sq_eq_one hx2) (conj_ne_one hx1) with h | h | h
    · exact Or.inl (isA_conj hc h)
    · exact Or.inr (Or.inl (isD_conj hc h))
    · exact Or.inr (Or.inr (isUU_conj hc h))
  a_noncentral := by
    intro b' hb' hA
    obtain ⟨b, hb, rfl⟩ := mem_cs_iff.1 hb'
    obtain ⟨x, hx, hne⟩ := hX.a_noncentral b hb ((isA_conj_iff hc).1 hA)
    refine ⟨c * x * c⁻¹, conj_mem_cs hx, fun h => hne ?_⟩
    rw [conj_mul', conj_mul'] at h
    exact conj_inj h
  a_big := by
    intro b' hb' hA
    obtain ⟨b, hb, rfl⟩ := mem_cs_iff.1 hb'
    rw [cs_inf_centralizer, card_cs]
    exact hX.a_big b hb ((isA_conj_iff hc).1 hA)
  pair_card := by
    intro a' ha' y' hy' hA hU hcomm
    obtain ⟨a, ha, rfl⟩ := mem_cs_iff.1 ha'
    obtain ⟨y, hy, rfl⟩ := mem_cs_iff.1 hy'
    rw [cs_inf3, card_cs]
    exact hX.pair_card a ha y hy ((isA_conj_iff hc).1 hA) ((isUU_conj_iff hc).1 hU)
      (conj_comm_iff.1 hcomm)
  pair_rank := by
    intro a' ha' y' hy' hA hU hcomm
    obtain ⟨a, ha, rfl⟩ := mem_cs_iff.1 ha'
    obtain ⟨y, hy, rfl⟩ := mem_cs_iff.1 hy'
    rintro ⟨E', hE', hE2, hE16⟩
    rw [cs_inf3] at hE'
    obtain ⟨E, hEle, rfl⟩ := exists_of_le_cs hE'
    exact hX.pair_rank a ha y hy ((isA_conj_iff hc).1 hA) ((isUU_conj_iff hc).1 hU)
      (conj_comm_iff.1 hcomm) ⟨E, hEle, isElemTwo_cs.1 hE2, by rwa [card_cs] at hE16⟩
  pair_sq := by
    intro a' ha' y' hy' hA hU hcomm x' hx' hx2
    obtain ⟨a, ha, rfl⟩ := mem_cs_iff.1 ha'
    obtain ⟨y, hy, rfl⟩ := mem_cs_iff.1 hy'
    rw [cs_inf3] at hx'
    obtain ⟨x, hx, rfl⟩ := mem_cs_iff.1 hx'
    rw [conj_mul'] at hx2
    have hx2' : x * x ≠ 1 := conj_ne_one hx2
    simp only [conj_mul']
    rcases hX.pair_sq a ha y hy ((isA_conj_iff hc).1 hA) ((isUU_conj_iff hc).1 hU)
      (conj_comm_iff.1 hcomm) x hx hx2' with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inl ⟨isA_conj hc h1, isD_conj hc h2⟩)
    · exact Or.inr (Or.inr ⟨isD_conj hc h1, isA_conj hc h2⟩)

end ConjCS

end CFSG.ComponentClassification.GrSLit.L34Tw
