module

public import CFSG.CGT.PushingUpLit.BHS.GlaubThmOne

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.RankThree.PartOne CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.CGT.PushingUpLit.BHS.Glauberman

variable {V : Type*} [CommGroup V]

namespace GlPair

variable [Finite V] {G M S A : Subgroup (MulAut V)} {k : MulAut V} (h : GlPair G M S A k)

include h

theorem commV_A_eq : commV A = fixV A := h.lemma_three.1

theorem quad_move {a : MulAut V} (ha : a ∈ A) (v : V) : a v * v⁻¹ ∈ fixV A := by
  rw [← h.commV_A_eq]
  exact G6.mem_commV_of_mem ha v

theorem sup_fixV_eq_top :
    fixV A ⊔ fixV (A.map (MulAut.conj k).toMonoidHom) = ⊤ := h.lemma_three.2.2.1

theorem card_fixV_A : Nat.card (fixV A) = Nat.card A := h.lemma_three.2.2.2.1

theorem exists_mul (v : V) :
    ∃ x₁ ∈ fixV A, ∃ x₂ ∈ fixV (A.map (MulAut.conj k).toMonoidHom), x₁ * x₂ = v :=
  Subgroup.mem_sup.1 (h.sup_fixV_eq_top ▸ Subgroup.mem_top v)

theorem fixV_ne_bot : fixV A ≠ ⊥ := by
  rw [← Subgroup.one_lt_card_iff_ne_bot, h.card_fixV_A, Subgroup.one_lt_card_iff_ne_bot]
  exact h.ne

omit [Finite V] h in
theorem exists_eq_apply_of_mem_fixV_B {u : V}
    (hu : u ∈ fixV (A.map (MulAut.conj k).toMonoidHom)) : ∃ u₁ ∈ fixV A, k u₁ = u := by
  rw [fixV_map_conj] at hu
  obtain ⟨u₁, hu₁, h'⟩ := hu
  exact ⟨u₁, hu₁, h'⟩

omit [Finite V] h in
theorem apply_mem_fixV_B {u : V} (hu : u ∈ fixV A) :
    k u ∈ fixV (A.map (MulAut.conj k).toMonoidHom) := by
  rw [fixV_map_conj]
  exact ⟨u, hu, rfl⟩

theorem exists_apply_eq {v u : V} (hv : v ∉ fixV A) (hu : u * v⁻¹ ∈ fixV A) :
    ∃ a ∈ A, a v = u := by
  let f : A → fixV A := fun a => ⟨(a : MulAut V) v * v⁻¹, h.quad_move a.2 v⟩
  have hf : Function.Injective f := by
    intro a a' haa'
    have h1 : (a : MulAut V) v * v⁻¹ = (a' : MulAut V) v * v⁻¹ := congrArg Subtype.val haa'
    have h2 : (a : MulAut V) v = (a' : MulAut V) v := mul_right_cancel h1
    by_contra hne
    have hcA : (a' : MulAut V)⁻¹ * (a : MulAut V) ∈ A := A.mul_mem (A.inv_mem a'.2) a.2
    have hc1 : (a' : MulAut V)⁻¹ * (a : MulAut V) ≠ 1 := fun h0 =>
      hne (Subtype.ext (inv_mul_eq_one.1 h0).symm)
    have hcy : ((a' : MulAut V)⁻¹ * (a : MulAut V)) v = v := by
      rw [MulAut.mul_apply, h2]
      simp
    have hmem : v ∈ fixV (Subgroup.zpowers ((a' : MulAut V)⁻¹ * (a : MulAut V))) :=
      Glauberman.mem_fixV_zpowers.2 hcy
    rw [h.fixV_zpowers_eq hcA hc1] at hmem
    exact hv hmem
  have hcard : Nat.card A = Nat.card (fixV A) := h.card_fixV_A.symm
  have hbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩
  obtain ⟨a, ha⟩ := hbij.2 ⟨u * v⁻¹, hu⟩
  refine ⟨a, a.2, ?_⟩
  have h3 := congrArg Subtype.val ha
  exact mul_right_cancel h3

omit [Finite V] in
theorem mem_M_of_fixes {g : MulAut V} (hg : g ∈ G) {v : V} (hv : v ∈ fixV A) (hv1 : v ≠ 1)
    (hgv : g v = v) : g ∈ M := by
  by_contra hgM
  have hgen := h.gen g hg hgM
  have hvG : v ∈ fixV G := by
    rw [← hgen, fixV_sup]
    exact ⟨hv, Glauberman.mem_fixV_zpowers.2 hgv⟩
  rw [h.fix] at hvG
  exact hv1 hvG

theorem apply_mem_fixV_of_mem_M {m : MulAut V} (hm : m ∈ M) {v : V} (hv : v ∈ fixV A) :
    m v ∈ fixV A := by
  by_contra hmv
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact hmv (by simp)
  obtain ⟨x₁, hx₁, x₂, hx₂, hx⟩ := h.exists_mul (m v)
  have hx2 : x₂ ≠ 1 := by
    rintro rfl
    apply hmv
    rw [← hx, mul_one]
    exact hx₁
  have hu : x₂ * (m v)⁻¹ ∈ fixV A := by
    rw [← hx]
    have : x₂ * (x₁ * x₂)⁻¹ = x₁⁻¹ := by group
    rw [this]
    exact (fixV A).inv_mem hx₁
  obtain ⟨a, haA, hax⟩ := h.exists_apply_eq hmv hu
  set g₀ := a * m with hg₀
  have hg₀M : g₀ ∈ M := M.mul_mem (h.A_le_M haA) hm
  have hg₀v : g₀ v = x₂ := by rw [hg₀, MulAut.mul_apply, hax]
  apply h.hAk
  rintro _ ⟨b, hb, rfl⟩
  have hβfix : ((MulAut.conj k).toMonoidHom b) x₂ = x₂ := hx₂ _ ⟨b, hb, rfl⟩
  have hβG : (MulAut.conj k).toMonoidHom b ∈ G := h.B_le_G ⟨b, hb, rfl⟩
  have hg₀G : g₀ ∈ G := h.lt.le hg₀M
  have h1 : g₀⁻¹ * (MulAut.conj k).toMonoidHom b * g₀ ∈ M := by
    refine h.mem_M_of_fixes (G.mul_mem (G.mul_mem (G.inv_mem hg₀G) hβG) hg₀G) hv hv1 ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, hg₀v, hβfix, ← hg₀v]
    simp
  have h2 : (MulAut.conj k).toMonoidHom b =
      g₀ * (g₀⁻¹ * (MulAut.conj k).toMonoidHom b * g₀) * g₀⁻¹ := by group
  rw [h2]
  exact M.mul_mem (M.mul_mem hg₀M h1) (M.inv_mem hg₀M)

theorem k_not_mem_stabSub : k ∉ stabSub (fixV A) := by
  intro hk
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h.fixV_ne_bot
  have hu1' : u ≠ 1 := fun h0 => hu1 (Subtype.ext h0)
  have h1 : k u ∈ fixV A := (hk u).2 hu
  have h2 : k u ∈ fixV (A.map (MulAut.conj k).toMonoidHom) := GlPair.apply_mem_fixV_B hu
  have h3 : k u ∈ fixV A ⊓ fixV (A.map (MulAut.conj k).toMonoidHom) := ⟨h1, h2⟩
  rw [h.fixV_inf_eq_bot] at h3
  apply hu1'
  have : k u = 1 := h3
  simpa using this

theorem mem_M_of_apply_mem {g : MulAut V} (hg : g ∈ G) (hgV : ∀ u ∈ fixV A, g u ∈ fixV A) :
    g ∈ M := by
  have hMY : M ≤ G ⊓ stabSub (fixV A) := by
    intro m hm
    refine ⟨h.lt.le hm, fun u => ⟨fun hu => ?_, fun hu => h.apply_mem_fixV_of_mem_M hm hu⟩⟩
    have := h.apply_mem_fixV_of_mem_M (M.inv_mem hm) hu
    simpa using this
  rcases h.max _ hMY inf_le_left with hY | hY
  · have hinj : Function.Injective
        (fun u : fixV A => (⟨g u, hgV u u.2⟩ : fixV A)) := fun u u' huu' =>
      Subtype.ext (g.injective (congrArg Subtype.val huu'))
    have hsurj := Finite.injective_iff_surjective.1 hinj
    have hgY : g ∈ G ⊓ stabSub (fixV A) := by
      refine ⟨hg, fun u => ⟨fun hu => ?_, hgV u⟩⟩
      obtain ⟨u', hu'⟩ := hsurj ⟨g u, hu⟩
      have : (u' : V) = u := g.injective (congrArg Subtype.val hu')
      rw [← this]
      exact u'.2
    rw [hY] at hgY
    exact hgY
  · exfalso
    have : k ∈ G ⊓ stabSub (fixV A) := by
      rw [hY]
      exact h.hk
    exact h.k_not_mem_stabSub this.2

theorem mem_M_of_apply_eq {g : MulAut V} (hg : g ∈ G) {v w : V} (hv : v ∈ fixV A)
    (hw : w ∈ fixV A) (hv1 : v ≠ 1) (hgvw : g v = w) : g ∈ M := by
  by_contra hgM
  have hAMg : A ≤ M.map (MulAut.conj g).toMonoidHom := by
    intro a ha
    have h1 : g⁻¹ * a * g ∈ M := by
      refine h.mem_M_of_fixes (G.mul_mem (G.mul_mem (G.inv_mem hg) (h.A_le_G ha)) hg) hv hv1 ?_
      rw [MulAut.mul_apply, MulAut.mul_apply, hgvw, show a w = w from (mem_fixV.1 hw) a ha,
        ← hgvw]
      simp
    refine ⟨g⁻¹ * a * g, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hMgM : M.map (MulAut.conj g).toMonoidHom ≤ M := by
    intro x hx
    by_contra hxM
    have hxG : x ∈ G := map_conj_le hg h.lt.le hx
    have hgen := h.gen x hxG hxM
    have hGle : G ≤ M.map (MulAut.conj g).toMonoidHom := by
      have hle : A ⊔ Subgroup.zpowers x ≤ M.map (MulAut.conj g).toMonoidHom :=
        sup_le hAMg ((Subgroup.zpowers_le).2 hx)
      rwa [hgen] at hle
    have hcard : Nat.card G ≤ Nat.card M := by
      have := Subgroup.card_le_of_le hGle
      rwa [card_map_conj] at this
    exact h.lt.ne (Subgroup.eq_of_le_of_card_ge h.lt.le hcard)
  have hMgeq : M.map (MulAut.conj g).toMonoidHom = M :=
    Subgroup.eq_of_le_of_card_ge hMgM (by rw [card_map_conj])
  have hgN : g ∈ Subgroup.normalizer (M : Set (MulAut V)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 hMgeq
  have hle : M ≤ G ⊓ Subgroup.normalizer (M : Set (MulAut V)) :=
    le_inf h.lt.le Subgroup.le_normalizer
  rcases h.max _ hle inf_le_left with hY | hY
  · have hgY : g ∈ G ⊓ Subgroup.normalizer (M : Set (MulAut V)) := ⟨hg, hgN⟩
    rw [hY] at hgY
    exact hgM hgY
  · have hGN : G ≤ Subgroup.normalizer (M : Set (MulAut V)) := inf_eq_left.1 hY
    apply h.hAk
    rintro _ ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hGN h.hk) b).1 (h.A_le_M hb)

theorem exists_mul_apply_mem {g : MulAut V} (hg : g ∈ G) (hgM : g ∉ M) :
    ∃ a ∈ A, ∀ u ∈ fixV A, (a * g) u ∈ fixV (A.map (MulAut.conj k).toMonoidHom) := by
  obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h.fixV_ne_bot
  have hv1' : v ≠ 1 := fun h0 => hv1 (Subtype.ext h0)
  have hgv : g v ∉ fixV A := fun hgv => hgM (h.mem_M_of_apply_eq hg hv hgv hv1' rfl)
  obtain ⟨x₁, hx₁, x₂, hx₂, hx⟩ := h.exists_mul (g v)
  have hx2 : x₂ ≠ 1 := by
    rintro rfl
    apply hgv
    rw [← hx, mul_one]
    exact hx₁
  have hu : x₂ * (g v)⁻¹ ∈ fixV A := by
    rw [← hx]
    have : x₂ * (x₁ * x₂)⁻¹ = x₁⁻¹ := by group
    rw [this]
    exact (fixV A).inv_mem hx₁
  obtain ⟨a, haA, hax⟩ := h.exists_apply_eq hgv hu
  refine ⟨a, haA, ?_⟩
  obtain ⟨w, hw, hkw⟩ := GlPair.exists_eq_apply_of_mem_fixV_B hx₂
  have hg'G : k⁻¹ * a * g ∈ G := G.mul_mem (G.mul_mem (G.inv_mem h.hk) (h.A_le_G haA)) hg
  have hg'v : (k⁻¹ * a * g) v = w := by
    rw [MulAut.mul_apply, MulAut.mul_apply, hax, ← hkw]
    simp
  have hg'M : k⁻¹ * a * g ∈ M := h.mem_M_of_apply_eq hg'G hv hw hv1' hg'v
  intro u hu'
  have h1 : (k⁻¹ * a * g) u ∈ fixV A := h.apply_mem_fixV_of_mem_M hg'M hu'
  have h2 : (a * g) u = k ((k⁻¹ * a * g) u) := by
    simp [MulAut.mul_apply]
  rw [h2]
  exact GlPair.apply_mem_fixV_B h1

theorem eq_one_of_trivial_stab {x : MulAut V} (hx1 : ∀ v ∈ fixV A, x v = v)
    (hx2 : ∀ v, x v * v⁻¹ ∈ fixV A)
    (hx3 : ∀ u ∈ fixV (A.map (MulAut.conj k).toMonoidHom),
      x u ∈ fixV (A.map (MulAut.conj k).toMonoidHom)) : x = 1 := by
  ext v
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := h.exists_mul v
  have hy2 : x y₂ = y₂ := by
    have h1 : x y₂ * y₂⁻¹ ∈ fixV A ⊓ fixV (A.map (MulAut.conj k).toMonoidHom) :=
      ⟨hx2 y₂, (fixV _).mul_mem (hx3 y₂ hy₂) ((fixV _).inv_mem hy₂)⟩
    rw [h.fixV_inf_eq_bot] at h1
    exact mul_inv_eq_one.1 h1
  simp [map_mul, hx1 y₁ hy₁, hy2]

theorem mem_A_of_mem_M {m : MulAut V} (hm : m ∈ M) (hm1 : ∀ v ∈ fixV A, m v = v)
    (hm2 : ∀ v, m v * v⁻¹ ∈ fixV A) : m ∈ A := by
  have hmk : m * k ∈ G := G.mul_mem (h.lt.le hm) h.hk
  have hmkM : m * k ∉ M := fun h' =>
    h.k_not_mem (by simpa using M.mul_mem (M.inv_mem hm) h')
  obtain ⟨a, haA, ha⟩ := h.exists_mul_apply_mem hmk hmkM
  have hx : a * m = 1 := by
    refine h.eq_one_of_trivial_stab (x := a * m) ?_ ?_ ?_
    · intro v hv
      rw [MulAut.mul_apply, hm1 v hv]
      exact (mem_fixV.1 hv) a haA
    · intro v
      have h1 : (a * m) v * v⁻¹ = (a (m v) * (m v)⁻¹) * (m v * v⁻¹) := by
        simp only [MulAut.mul_apply]
        group
      rw [h1]
      exact (fixV A).mul_mem (h.quad_move haA _) (hm2 v)
    · intro u hu
      obtain ⟨u₁, hu₁, rfl⟩ := GlPair.exists_eq_apply_of_mem_fixV_B hu
      have := ha u₁ hu₁
      simpa [MulAut.mul_apply] using this
  have : m = a⁻¹ := eq_inv_of_mul_eq_one_right hx
  rw [this]
  exact A.inv_mem haA

theorem map_conj_le_of_mem_M {m : MulAut V} (hm : m ∈ M) :
    A.map (MulAut.conj m).toMonoidHom ≤ A := by
  rintro _ ⟨a, ha, rfl⟩
  have hmi : m⁻¹ ∈ M := M.inv_mem hm
  refine h.mem_A_of_mem_M (M.mul_mem (M.mul_mem hm (h.A_le_M ha)) hmi) ?_ ?_
  · intro v hv
    have h1 : m⁻¹ v ∈ fixV A := h.apply_mem_fixV_of_mem_M hmi hv
    show (m * a * m⁻¹) v = v
    rw [MulAut.mul_apply, MulAut.mul_apply, (mem_fixV.1 h1) a ha]
    simp
  · intro v
    have h1 : (MulAut.conj m).toMonoidHom a v * v⁻¹ = m (a (m⁻¹ v) * (m⁻¹ v)⁻¹) := by
      simp [MulAut.conj_apply, MulAut.mul_apply]
    show (MulAut.conj m).toMonoidHom a v * v⁻¹ ∈ fixV A
    rw [h1]
    exact h.apply_mem_fixV_of_mem_M hm (h.quad_move ha _)

theorem map_conj_eq_of_mem_M {m : MulAut V} (hm : m ∈ M) :
    A.map (MulAut.conj m).toMonoidHom = A :=
  Subgroup.eq_of_le_of_card_ge (h.map_conj_le_of_mem_M hm) (by rw [card_map_conj])

theorem fixV_B_ne_bot : fixV (A.map (MulAut.conj k).toMonoidHom) ≠ ⊥ := by
  rw [← Subgroup.one_lt_card_iff_ne_bot, h.lemma_three.2.2.2.2.1,
    Subgroup.one_lt_card_iff_ne_bot]
  exact h.ne

theorem conj_mem_normalizer_B {m : MulAut V} (hm : m ∈ M) :
    k * m * k⁻¹ ∈
      Subgroup.normalizer ((A.map (MulAut.conj k).toMonoidHom : Subgroup (MulAut V)) :
        Set (MulAut V)) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.2
  have e1 : (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj (k * m * k⁻¹)).toMonoidHom =
      A.map (MulAut.conj (k * m)).toMonoidHom := by
    rw [Glauberman.map_conj_map_conj, show k * m * k⁻¹ * k = k * m by group]
  have e2 : (A.map (MulAut.conj m).toMonoidHom).map (MulAut.conj k).toMonoidHom =
      A.map (MulAut.conj (k * m)).toMonoidHom := Glauberman.map_conj_map_conj k m A
  show (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj (k * m * k⁻¹)).toMonoidHom =
    A.map (MulAut.conj k).toMonoidHom
  rw [e1, ← e2, h.map_conj_eq_of_mem_M hm]

theorem not_le_map_conj_M : ¬ A ≤ M.map (MulAut.conj k).toMonoidHom := by
  intro hAMk
  have hAN : A ≤ Subgroup.normalizer
      ((A.map (MulAut.conj k).toMonoidHom : Subgroup (MulAut V)) : Set (MulAut V)) := by
    intro a ha
    obtain ⟨m, hm, hma⟩ := hAMk ha
    have : a = k * m * k⁻¹ := hma.symm
    rw [this]
    exact h.conj_mem_normalizer_B hm
  have hGN : G ≤ Subgroup.normalizer
      ((A.map (MulAut.conj k).toMonoidHom : Subgroup (MulAut V)) : Set (MulAut V)) := by
    have hle : A ⊔ A.map (MulAut.conj k).toMonoidHom ≤ Subgroup.normalizer
        ((A.map (MulAut.conj k).toMonoidHom : Subgroup (MulAut V)) : Set (MulAut V)) :=
      sup_le hAN Subgroup.le_normalizer
    rwa [h.sup_eq] at hle
  have hB2 : IsPGroup 2 (A.map (MulAut.conj k).toMonoidHom) := (h.syl.2.1.to_le h.le).map _
  have hBle : A.map (MulAut.conj k).toMonoidHom ≤ pCoreOf 2 G :=
    le_pCoreOf_of_le_normalizer 2 h.B_le_G hGN hB2
  rw [h.o2] at hBle
  have hcard : Nat.card A = 1 := by
    rw [← card_map_conj k A, le_bot_iff.1 hBle, Subgroup.card_bot]
  exact h.ne (Subgroup.eq_bot_of_card_eq _ hcard)

theorem swap : GlPair G (M.map (MulAut.conj k).toMonoidHom) (S.map (MulAut.conj k).toMonoidHom)
    (A.map (MulAut.conj k).toMonoidHom) k⁻¹ where
  toGlHyp := h.toGlHyp.conj h.hk
  hk := G.inv_mem h.hk
  hAk := by
    rw [map_conj_inv_map_conj]
    exact h.not_le_map_conj_M

theorem exists_moufang {a : MulAut V} (ha : a ∈ A) (ha1 : a ≠ 1) :
    ∃ b ∈ A.map (MulAut.conj k).toMonoidHom, b ≠ 1 ∧
      A.map (MulAut.conj b).toMonoidHom =
        (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  have hakM : a ∉ M.map (MulAut.conj k).toMonoidHom := by
    intro hamk
    obtain ⟨m, hm, hma⟩ := hamk
    have haN : a ∈ Subgroup.normalizer
        ((A.map (MulAut.conj k).toMonoidHom : Subgroup (MulAut V)) : Set (MulAut V)) := by
      have : a = k * m * k⁻¹ := hma.symm
      rw [this]
      exact h.conj_mem_normalizer_B hm
    have h2 : (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        A.map (MulAut.conj k).toMonoidHom := Subgroup.mem_normalizer_iff_map_conj_eq.1 haN
    have hfix : ∀ u ∈ fixV (A.map (MulAut.conj k).toMonoidHom),
        a u ∈ fixV (A.map (MulAut.conj k).toMonoidHom) := by
      intro u hu
      have h1 := fixV_map_conj a (A.map (MulAut.conj k).toMonoidHom)
      rw [h2] at h1
      rw [h1]
      exact ⟨u, hu, rfl⟩
    exact ha1 (h.eq_one_of_trivial_stab (x := a) (fun v hv => (mem_fixV.1 hv) a ha)
      (fun v => h.quad_move ha v) hfix)
  obtain ⟨b', hb'B, hb'⟩ := h.swap.exists_mul_apply_mem (h.A_le_G ha) hakM
  rw [map_conj_inv_map_conj] at hb'
  refine ⟨b'⁻¹, (A.map (MulAut.conj k).toMonoidHom).inv_mem hb'B, ?_, ?_⟩
  · intro hb1
    have hb'1 : b' = 1 := inv_eq_one.1 hb1
    subst hb'1
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h.fixV_B_ne_bot
    have h1 : a u ∈ fixV A := by simpa using hb' u hu
    have h2 : a u * u⁻¹ ∈ fixV A := h.quad_move ha u
    have h3 : u⁻¹ ∈ fixV A := by
      have := (fixV A).mul_mem ((fixV A).inv_mem h1) h2
      simpa using this
    have h4 : u ∈ fixV A := by simpa using (fixV A).inv_mem h3
    have h5 : u ∈ fixV A ⊓ fixV (A.map (MulAut.conj k).toMonoidHom) := ⟨h4, hu⟩
    rw [h.fixV_inf_eq_bot] at h5
    exact hu1 (Subtype.ext h5)
  · have hy : b' * a * k ∈ M := by
      refine h.mem_M_of_apply_mem (G.mul_mem (G.mul_mem (h.B_le_G hb'B) (h.A_le_G ha)) h.hk) ?_
      intro u hu
      have := hb' (k u) (GlPair.apply_mem_fixV_B hu)
      simpa [MulAut.mul_apply] using this
    have e1 : A.map (MulAut.conj (b' * a * k)).toMonoidHom = A := h.map_conj_eq_of_mem_M hy
    have e2 : ((A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj b').toMonoidHom = A.map (MulAut.conj (b' * a * k)).toMonoidHom := by
      rw [Glauberman.map_conj_map_conj a k A, Glauberman.map_conj_map_conj b' (a * k) A,
        mul_assoc]
    calc A.map (MulAut.conj b'⁻¹).toMonoidHom
        = (((A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj a).toMonoidHom).map
            (MulAut.conj b').toMonoidHom).map (MulAut.conj b'⁻¹).toMonoidHom := by
          rw [e2, e1]
      _ = (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj a).toMonoidHom :=
          map_conj_inv_map_conj b' _

theorem exists_moufang' {b : MulAut V} (hb : b ∈ A.map (MulAut.conj k).toMonoidHom)
    (hb1 : b ≠ 1) :
    ∃ a ∈ A, a ≠ 1 ∧
      (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        A.map (MulAut.conj b).toMonoidHom := by
  obtain ⟨a, haA, ha1, hrel⟩ := h.swap.exists_moufang hb hb1
  rw [map_conj_inv_map_conj] at haA hrel
  exact ⟨a, haA, ha1, hrel⟩

end GlPair

end CFSG.CGT.PushingUpLit.BHS
