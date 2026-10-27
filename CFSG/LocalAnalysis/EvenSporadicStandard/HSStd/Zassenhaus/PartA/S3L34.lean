module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3L34Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Catalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Shape
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Generic

variable {G : Type} [Group G]

theorem s3l_mem_Vsub_iff {t u : G} (ht : t * t = 1) (hu : u * u = 1) (htu : t * u = u * t) {y : G} :
    y ∈ Vsub t u ↔ y = 1 ∨ y = t ∨ y = u ∨ y = t * u := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hut : u * t = t * u := htu.symm
  have e1 : t * (t * u) = u := by rw [← mul_assoc, ht, one_mul]
  have e2 : u * (t * u) = t := by rw [← mul_assoc, hut, mul_assoc, hu, mul_one]
  have e3 : t * u * t = u := by rw [mul_assoc, hut, ← mul_assoc, ht, one_mul]
  have e4 : t * u * u = t := by rw [mul_assoc, hu, mul_one]
  have e5 : t * u * (t * u) = 1 := by rw [← mul_assoc, e3, hu]
  constructor
  · intro hy
    let M : Subgroup G :=
      { carrier := {y | y = 1 ∨ y = t ∨ y = u ∨ y = t * u}
        one_mem' := Or.inl rfl
        mul_mem' := by
          rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
            simp [ht, hu, hut, e1, e2, e3, e4, e5]
        inv_mem' := by
          rintro x (rfl | rfl | rfl | rfl)
          · simp
          · simp [hti]
          · simp [hui]
          · simp [mul_inv_rev, hti, hui, hut] }
    have hle : Vsub t u ≤ M :=
      sup_le ((zpowers_le).2 (Or.inr (Or.inl rfl))) ((zpowers_le).2 (Or.inr (Or.inr (Or.inl rfl))))
    exact hle hy
  · rintro (h | h | h | h) <;> subst h
    · exact one_mem _
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem s3l_commute_Vsub {t u c : G} (h1 : c * t = t * c) (h2 : c * u = u * c) :
    ∀ y ∈ Vsub t u, c * y = y * c := by
  have hle : Vsub t u ≤ Cen c :=
    sup_le ((zpowers_le).2 (mem_Cen.2 h1.symm)) ((zpowers_le).2 (mem_Cen.2 h2.symm))
  intro y hy
  exact (mem_Cen.1 (hle hy)).symm

theorem s3l_mem_centralizer_Vsub {t u c : G} :
    c ∈ centralizer ((Vsub t u : Subgroup G) : Set G) ↔ c * t = t * c ∧ c * u = u * c := by
  constructor
  · intro hc
    exact ⟨(mem_centralizer_iff.1 hc t (mem_sup_left (mem_zpowers t))).symm,
      (mem_centralizer_iff.1 hc u (mem_sup_right (mem_zpowers u))).symm⟩
  · rintro ⟨h1, h2⟩
    exact mem_centralizer_iff.2 fun y hy => (s3l_commute_Vsub h1 h2 y hy).symm

theorem s3l_mem_normalizer_Vsub [Finite G] {t u g : G} (ht : t * t = 1) (hu : u * u = 1)
    (htu : t * u = u * t) (h1 : g * t * g⁻¹ ∈ Vsub t u) (h2 : g * u * g⁻¹ ∈ Vsub t u) :
    g ∈ normalizer ((Vsub t u : Subgroup G) : Set G) := by
  have hmap : ∀ y ∈ Vsub t u, g * y * g⁻¹ ∈ Vsub t u := by
    intro y hy
    rcases (s3l_mem_Vsub_iff ht hu htu).1 hy with h | h | h | h <;> rw [h]
    · simp
    · exact h1
    · exact h2
    · have : g * (t * u) * g⁻¹ = (g * t * g⁻¹) * (g * u * g⁻¹) := by group
      rw [this]
      exact mul_mem h1 h2
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hmap y hy, fun hy => ?_⟩
  let f : Vsub t u → Vsub t u := fun x => ⟨g * x * g⁻¹, hmap x x.2⟩
  have hf : Function.Injective f := by
    intro x x' h
    have h' := congrArg Subtype.val h
    simp only [f] at h'
    exact Subtype.ext (by simpa using h')
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.1 hf ⟨g * y * g⁻¹, hy⟩
  have h' := congrArg Subtype.val hx
  simp only [f] at h'
  have hxy : (x : G) = y := by simpa using h'
  rw [← hxy]
  exact x.2

end Generic

structure S3lSetup (G : Type) [Group G] (L A : Subgroup G) (t u : G) : Prop where
  t_sq : t * t = 1
  u_sq : u * u = 1
  u_ne : u ≠ 1
  tu : t * u = u * t
  t_comm : ∀ l ∈ L, l * t = t * l
  u_mem : u ∈ L
  A_le : A ≤ L
  A_u : ∀ a ∈ A, a * u = u * a
  cent_t : centralizer ({t} : Set G) = L ⊔ zpowers t
  Lu : L ⊓ centralizer ({u} : Set G) = zpowers u ⊔ A
  disj : Disjoint (zpowers u) A
  t_nmem : t ∉ L

section Setup

variable {G : Type} [Group G] {L A : Subgroup G} {t u : G}

theorem S3lSetup.t_ne (S : S3lSetup G L A t u) : t ≠ 1 := fun h =>
  S.t_nmem (h ▸ one_mem L)

theorem S3lSetup.t_mem_V (_ : S3lSetup G L A t u) : t ∈ Vsub t u :=
  mem_sup_left (mem_zpowers t)

theorem S3lSetup.u_mem_V (_ : S3lSetup G L A t u) : u ∈ Vsub t u :=
  mem_sup_right (mem_zpowers u)

theorem S3lSetup.V_inf_A (S : S3lSetup G L A t u) {y : G} (hy : y ∈ Vsub t u) (hA : y ∈ A) :
    y = 1 := by
  rcases (s3l_mem_Vsub_iff S.t_sq S.u_sq S.tu).1 hy with h | h | h | h
  · exact h
  · rw [h] at hA
    exact absurd (S.A_le hA) S.t_nmem
  · rw [h] at hA
    have := Subgroup.disjoint_def.1 S.disj (mem_zpowers u) hA
    rw [h, this]
  · exfalso
    rw [h] at hA
    apply S.t_nmem
    have : t = (t * u) * u := by rw [mul_assoc, S.u_sq, mul_one]
    rw [this]
    exact mul_mem (S.A_le hA) S.u_mem

theorem S3lSetup.L_u_decomp (S : S3lSetup G L A t u) {l : G} (hl : l ∈ L)
    (hlu : l * u = u * l) : l ∈ A ∨ u⁻¹ * l ∈ A := by
  have h1 : l ∈ L ⊓ centralizer ({u} : Set G) := ⟨hl, mem_centralizer_singleton_iff.2 hlu⟩
  rw [S.Lu, sup_comm] at h1
  exact mem_or_inv_mul_mem_of_mem_sup_zpowers S.u_sq S.A_u h1

theorem S3lSetup.cent_V_decomp (S : S3lSetup G L A t u) {c : G}
    (hc : c ∈ centralizer ((Vsub t u : Subgroup G) : Set G)) :
    ∃ v ∈ Vsub t u, ∃ a ∈ A, c = v * a := by
  obtain ⟨hct, hcu⟩ := s3l_mem_centralizer_Vsub.1 hc
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right S.t_sq
  have hc' : c ∈ L ⊔ zpowers t := by
    rw [← S.cent_t]
    exact mem_centralizer_singleton_iff.2 hct
  rcases mem_or_inv_mul_mem_of_mem_sup_zpowers S.t_sq S.t_comm hc' with hl | hl
  · rcases S.L_u_decomp hl hcu with h | h
    · exact ⟨1, one_mem _, c, h, (one_mul c).symm⟩
    · exact ⟨u, S.u_mem_V, u⁻¹ * c, h, (mul_inv_cancel_left u c).symm⟩
  · have htu' : t⁻¹ * u = u * t⁻¹ := by rw [hti]; exact S.tu
    have hlu : (t⁻¹ * c) * u = u * (t⁻¹ * c) := by
      calc (t⁻¹ * c) * u = t⁻¹ * (c * u) := mul_assoc _ _ _
        _ = t⁻¹ * (u * c) := by rw [hcu]
        _ = (t⁻¹ * u) * c := (mul_assoc _ _ _).symm
        _ = (u * t⁻¹) * c := by rw [htu']
        _ = u * (t⁻¹ * c) := mul_assoc _ _ _
    rcases S.L_u_decomp hl hlu with h | h
    · exact ⟨t, S.t_mem_V, t⁻¹ * c, h, by rw [mul_inv_cancel_left]⟩
    · refine ⟨t * u, mul_mem S.t_mem_V S.u_mem_V, u⁻¹ * (t⁻¹ * c), h, ?_⟩
      group

end Setup

theorem s3l_card_centralizer_subtype {G : Type*} [Group G] (H : Subgroup G) (h : G) (hh : h ∈ H) :
    Nat.card ↥(centralizer ({(⟨h, hh⟩ : ↥H)} : Set ↥H)) =
      Nat.card ↥(H ⊓ centralizer ({h} : Set G)) := by
  have heq : (centralizer ({(⟨h, hh⟩ : ↥H)} : Set ↥H)).map H.subtype =
      H ⊓ centralizer ({h} : Set G) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx))
    · rintro ⟨hg, hgc⟩
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      exact mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 hgc))
  rw [← heq]
  exact (Subgroup.card_map_of_injective Subtype.coe_injective).symm

theorem s3l_conj_of_comm {G : Type*} [Group G] {c x : G} (h : c * x = x * c) :
    c⁻¹ * x * c = x := by
  rw [mul_assoc, ← h, inv_mul_cancel_left]

section Main

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem s3l_t_not_mem (hb : PAB G L t E W z) : t ∉ L := by
  intro h
  have hZ := CFSG.EvenSporadicStandard.TwoHS.center_eq_bot_of_isSporadic_hs hb.setting.2.1
  have hc : (⟨t, h⟩ : ↥L) ∈ center ↥L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 hb.t_cent g g.2)
  rw [hZ, mem_bot] at hc
  have h1 : t = 1 := congrArg Subtype.val hc
  have := hb.t_ord
  rw [h1, orderOf_one] at this
  omega

theorem s3l_setup (hb : PAB G L t E W z) (a : PA0 L t E z) :
    S3lSetup G L a.Abar t a.u := by
  have hu1 : (a.eK₀ ⟨a.u, a.u_mem⟩) * (a.eK₀ ⟨a.u, a.u_mem⟩) = 1 := by
    have := pow_orderOf_eq_one (a.eK₀ ⟨a.u, a.u_mem⟩)
    rwa [a.u_swap.orderOf, pow_two] at this
  have hu_mem : a.u ∈ L := (a.K₀_le a.u_mem).1
  refine ⟨hb.t_mul_t, ?_, ?_, ?_, ?_, hu_mem, ?_, ?_, hb.inner, a.Abar_comp, a.Abar_disj, ?_⟩
  · have : a.eK₀ (⟨a.u, a.u_mem⟩ * ⟨a.u, a.u_mem⟩) = a.eK₀ 1 := by rw [map_mul, hu1, map_one]
    exact congrArg Subtype.val (a.eK₀.injective this)
  · intro h
    have h1 : a.eK₀ ⟨a.u, a.u_mem⟩ = 1 := by
      have : (⟨a.u, a.u_mem⟩ : ↥a.K₀) = 1 := Subtype.ext h
      rw [this, map_one]
    have := a.u_swap.orderOf
    rw [h1, orderOf_one] at this
    omega
  · exact (mem_centralizer_iff.1 hb.t_cent a.u hu_mem).symm
  · intro l hl
    exact mem_centralizer_iff.1 hb.t_cent l hl
  · exact fun x hx => ((a.Abar_le hx).1)
  · intro x hx
    exact mem_centralizer_singleton_iff.1 ((a.Abar_le hx).2)
  · exact s3l_t_not_mem hb

end Main

theorem l34_false (hc : HarrisContra) (hF : FusionA) {G : Type}
    [Group G] [Finite G]
    {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G} (hb : PAB G L t E W z)
    (a : PA2 L t E z) (w : G) (hw : w = a.u ∨ w = t * a.u) (hwy : w ∈ Cen a.y)
    (h7 : 7 ∣ Nat.card ↥(centralizer ({oMk (Cen a.y) ⟨w, hwy⟩} : Set (OQuot (Cen a.y)))))
    (hnc : ¬ ∃ g ∈ centralizer ({oMk (Cen a.y) ⟨w, hwy⟩} : Set (OQuot (Cen a.y))),
      g * oMk (Cen a.y) ⟨t, a.t_cy⟩ * g⁻¹ = oMk (Cen a.y) ⟨t, a.t_cy⟩ * oMk (Cen a.y) ⟨w, hwy⟩) :
    False := by
  have S := s3l_setup hb a.toPA0
  have hF' := hF G L t E W z hb a.toPA0
  have hyJ := a.y_J
  have hAle' := a.Abar_le
  set u := a.u with hu_def
  set Ab := a.Abar with hAb_def
  have ht2 : t * t = 1 := hb.t_mul_t
  have hu2 : u * u = 1 := S.u_sq
  have htu : t * u = u * t := S.tu
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htV : t ∈ Vsub t u := S.t_mem_V
  have huV : u ∈ Vsub t u := S.u_mem_V
  have hVw : u = w ∨ u = t * w := by
    rcases hw with h | h
    · exact Or.inl h.symm
    · right
      rw [h, ← mul_assoc, ht2, one_mul]
  have hwt : w * t = t * w := by
    rcases hw with h | h
    · rw [h]; exact htu.symm
    · rw [h]
      calc t * u * t = t * (u * t) := mul_assoc _ _ _
        _ = t * (t * u) := by rw [htu]
  have hw2 : w * w = 1 := by
    rcases hw with h | h
    · rw [h]; exact hu2
    · rw [h]
      calc t * u * (t * u) = t * (u * t) * u := by simp only [mul_assoc]
        _ = t * (t * u) * u := by rw [← htu]
        _ = (t * t) * (u * u) := by simp only [mul_assoc]
        _ = 1 := by rw [ht2, hu2, one_mul]
  have hne_tw : t ≠ w := by
    intro h
    rcases hw with h' | h'
    · exact S.t_nmem (by rw [h, h']; exact S.u_mem)
    · apply S.u_ne
      have : t * u = t * 1 := by rw [mul_one, ← h', h]
      exact mul_left_cancel this
  have hw1 : w ≠ 1 := by
    intro h
    rcases hw with h' | h'
    · exact S.u_ne (h' ▸ h)
    · have h1 : t * u = 1 := h' ▸ h
      have h3 : t = u⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
      exact S.t_nmem (by rw [h3, hui]; exact S.u_mem)
  have hwV : w ∈ Vsub t u := by
    rcases hw with h | h
    · rw [h]; exact huV
    · rw [h]; exact mul_mem htV huV
  have htwV : t * w ∈ Vsub t u := mul_mem htV hwV
  have hVmem : ∀ y, y ∈ Vsub t u → y = 1 ∨ y = t ∨ y = w ∨ y = t * w := by
    intro y hy
    rcases (s3l_mem_Vsub_iff ht2 hu2 htu).1 hy with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases hVw with h' | h'
      · exact Or.inr (Or.inr (Or.inl (h.trans h')))
      · exact Or.inr (Or.inr (Or.inr (h.trans h')))
    · rcases hw with h' | h'
      · rw [h, h']; exact Or.inr (Or.inr (Or.inr rfl))
      · rw [h, h']; exact Or.inr (Or.inr (Or.inl rfl))
  have hAt : ∀ x ∈ Ab, x * t = t * x := fun x hx => S.t_comm x (S.A_le hx)
  have hAw : ∀ x ∈ Ab, x * w = w * x := by
    intro x hx
    rcases hw with h | h
    · rw [h]; exact S.A_u x hx
    · rw [h]
      calc x * (t * u) = (x * t) * u := by rw [mul_assoc]
        _ = (t * x) * u := by rw [hAt x hx]
        _ = t * (x * u) := by rw [mul_assoc]
        _ = t * (u * x) := by rw [S.A_u x hx]
        _ = (t * u) * x := by rw [mul_assoc]
  have hAtw : ∀ x ∈ Ab, x * (t * w) = (t * w) * x := by
    intro x hx
    calc x * (t * w) = (x * t) * w := by rw [mul_assoc]
      _ = (t * x) * w := by rw [hAt x hx]
      _ = t * (x * w) := by rw [mul_assoc]
      _ = t * (w * x) := by rw [hAw x hx]
      _ = (t * w) * x := by rw [mul_assoc]
  have hAV : ∀ y ∈ Vsub t u, y ∈ Ab → y = 1 := fun y hy hA => S.V_inf_A hy hA
  have htA : t ∉ Ab := fun h => S.t_nmem (S.A_le h)
  have hwA : w ∉ Ab := fun h => hw1 (hAV w hwV h)
  have htwA : t * w ∉ Ab := by
    intro h
    have h1 : t * w = 1 := hAV _ htwV h
    have : w = t⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hti] at this
    exact hne_tw this.symm
  have hno : ∀ g : G, g * w = w * g → g * t * g⁻¹ ≠ t * w := by
    intro g hgw hg
    have hgw' : g * w * g⁻¹ = w := by rw [hgw]; group
    have h1 : g * t * g⁻¹ ∈ Vsub t u := by rw [hg]; exact htwV
    have h2 : g * u * g⁻¹ ∈ Vsub t u := by
      rcases hVw with hu' | hu'
      · have h3 : g * u * g⁻¹ = w := by rw [hu', hgw']
        rw [h3]; exact hwV
      · have : g * u * g⁻¹ = (g * t * g⁻¹) * (g * w * g⁻¹) := by rw [hu']; group
        rw [this, hg, hgw', mul_assoc, hw2, mul_one]
        exact htV
    have hgN := s3l_mem_normalizer_Vsub ht2 hu2 htu h1 h2
    obtain ⟨ab, hab, g', hg', hgeq⟩ := hF' g hgN
    have hg'eq : g' = ab⁻¹ * g := by rw [hgeq]; group
    have hg't : g' * t * g'⁻¹ = t * w := by
      have : g' * t * g'⁻¹ = ab⁻¹ * (g * t * g⁻¹) * ab := by rw [hg'eq]; group
      rw [this, hg]
      exact s3l_conj_of_comm (hAtw ab hab)
    have hg'w : g' * w * g'⁻¹ = w := by
      have : g' * w * g'⁻¹ = ab⁻¹ * (g * w * g⁻¹) * ab := by rw [hg'eq]; group
      rw [this, hgw']
      exact s3l_conj_of_comm (hAw ab hab)
    have hg'y : g' * a.y = a.y * g' := (mem_centralizer_iff.1 hg'.1 a.y hyJ).symm
    have hg'w' : g' * w = w * g' := by
      calc g' * w = (g' * w * g'⁻¹) * g' := by group
        _ = w * g' := by rw [hg'w]
    apply hnc
    refine ⟨oMk (Cen a.y) ⟨g', mem_Cen.2 hg'y⟩, ?_, ?_⟩
    · rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hg'w')
    · rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hg't)
  have htw : t ∈ Cen w := mem_Cen.2 hwt.symm
  have hww : w ∈ Cen w := mem_Cen.2 rfl
  have hyw : a.y ∈ Cen w := mem_Cen.2 (mem_Cen.1 hwy).symm
  have hAle : Ab ≤ Cen w := fun x hx => mem_Cen.2 (hAw x hx)
  obtain ⟨w', hw'v⟩ : ∃ w' : ↥(Cen w), (w' : G) = w := ⟨⟨w, hww⟩, rfl⟩
  obtain ⟨t', ht'v⟩ : ∃ t' : ↥(Cen w), (t' : G) = t := ⟨⟨t, htw⟩, rfl⟩
  obtain ⟨y', hy'v⟩ : ∃ y' : ↥(Cen w), (y' : G) = a.y := ⟨⟨a.y, hyw⟩, rfl⟩
  have hcw : ∀ g : ↥(Cen w), g * w' = w' * g := fun g =>
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hw'v]; exact mem_Cen.1 g.2)
  have hw2' : w' * w' = 1 := Subtype.ext (by rw [Subgroup.coe_mul, hw'v]; exact hw2)
  have hw1' : w' ≠ 1 := fun h => hw1 (by rw [← hw'v, h]; rfl)
  have ht2' : t' * t' = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ht'v]; exact ht2)
  have hnorm : (zpowers w').Normal := s3l_normal_zpowers hcw
  have hword : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
  have hbot : Open.fusionOddCore ↥(Cen w) = ⊥ :=
    (fusionOddCore_eq_standardComponentOddCore _).trans (hb.setting.1.oddCore w hword)
  have hodd : Open.fusionOddCore (↥(Cen w) ⧸ zpowers w') = ⊥ :=
    s3l_fusionOddCore_quot_zpowers hw2' hw1' hcw hbot
  have hcoe_tw : ((t' * w' : ↥(Cen w)) : G) = t * w := by
    rw [Subgroup.coe_mul, ht'v, hw'v]
  have hequiv := s3l_cent_equiv (w := w') (t := t') (A := Ab.subgroupOf (Cen w)) hw2' ht2'
    (fun x hx => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ht'v]; exact hAt _ hx))
    (fun h => htA (by rw [← ht'v]; exact h))
    (fun h => hwA (by rw [← hw'v]; exact h))
    (fun h => htwA (by rw [← hcoe_tw]; exact h))
    (by
      intro g hg
      have hgt : (g : G) * t = t * g := by
        have := congrArg Subtype.val hg
        rwa [Subgroup.coe_mul, Subgroup.coe_mul, ht'v] at this
      have hgw : (g : G) * w = w * g := mem_Cen.1 g.2
      have hgu : (g : G) * u = u * g := by
        rcases hVw with h | h
        · rw [h]; exact hgw
        · rw [h]
          calc (g : G) * (t * w) = (g * t) * w := by rw [mul_assoc]
            _ = (t * g) * w := by rw [hgt]
            _ = t * (g * w) := by rw [mul_assoc]
            _ = t * (w * g) := by rw [hgw]
            _ = (t * w) * g := by rw [mul_assoc]
      obtain ⟨v, hv, ab, hab, hgeq⟩ := S.cent_V_decomp (s3l_mem_centralizer_Vsub.2 ⟨hgt, hgu⟩)
      have hab' : ab ∈ Cen w := hAle hab
      have hxA : (⟨ab, hab'⟩ : ↥(Cen w)) ∈ Ab.subgroupOf (Cen w) := hab
      rcases hVmem v hv with h | h | h | h
      · exact ⟨1, Or.inl rfl, ⟨ab, hab'⟩, hxA, Subtype.ext (by rw [hgeq, h]; try rfl)⟩
      · exact ⟨t', Or.inr (Or.inl rfl), ⟨ab, hab'⟩, hxA, Subtype.ext (by
          rw [hgeq, h, Subgroup.coe_mul, ht'v]; try rfl)⟩
      · exact ⟨w', Or.inr (Or.inr (Or.inl rfl)), ⟨ab, hab'⟩, hxA, Subtype.ext (by
          rw [hgeq, h, Subgroup.coe_mul, hw'v]; try rfl)⟩
      · exact ⟨t' * w', Or.inr (Or.inr (Or.inr rfl)), ⟨ab, hab'⟩, hxA, Subtype.ext (by
          rw [hgeq, h, Subgroup.coe_mul, hcoe_tw]; try rfl)⟩)
    (by
      intro g hg
      refine hno g (mem_Cen.1 g.2) ?_
      have := congrArg Subtype.val hg
      rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ht'v, hcoe_tw] at this)
  obtain ⟨e⟩ := hequiv
  have hiso : Nonempty (↥(centralizer ({((t' : ↥(Cen w)) : ↥(Cen w) ⧸ zpowers w')} :
      Set (↥(Cen w) ⧸ zpowers w'))) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :=
    ⟨e.trans (MulEquiv.prodCongr (MulEquiv.refl _)
      ((Subgroup.subgroupOfEquivOfLe hAle).trans a.eAbar))⟩
  have hs2 : ((t' : ↥(Cen w)) : ↥(Cen w) ⧸ zpowers w') * ((t' : ↥(Cen w)) : ↥(Cen w) ⧸ zpowers w')
      = 1 := by
    rw [← QuotientGroup.mk_mul, ht2', QuotientGroup.mk_one]
  have hs1 : ((t' : ↥(Cen w)) : ↥(Cen w) ⧸ zpowers w') ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    rcases s3l_mem_zpowers_two hw2' h with h1 | h1
    · apply S.t_ne
      have h2 := congrArg Subtype.val h1
      rw [ht'v] at h2
      exact h2
    · apply hne_tw
      have h2 := congrArg Subtype.val h1
      rwa [ht'v, hw'v] at h2
  have hsord : orderOf ((t' : ↥(Cen w)) : ↥(Cen w) ⧸ zpowers w') = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hy3 : a.y ^ 3 = 1 := by
    have := pow_orderOf_eq_one a.y
    rwa [a.y_ord] at this
  have hy'3 : y' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hy'v]; exact hy3)
  have hyb3 : ((y' : ↥(Cen w)) : ↥(Cen w) ⧸ zpowers w') ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hy'3, QuotientGroup.mk_one]
  have hyb1 : ((y' : ↥(Cen w)) : ↥(Cen w) ⧸ zpowers w') ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    rcases s3l_mem_zpowers_two hw2' h with h1 | h1
    · have : a.y = 1 := by
        have h2 := congrArg Subtype.val h1
        rw [hy'v] at h2
        exact h2
      have h3 := a.y_ord
      rw [this, orderOf_one] at h3
      omega
    · have : a.y = w := by
        have h2 := congrArg Subtype.val h1
        rwa [hy'v, hw'v] at h2
      have h3 := a.y_ord
      rw [this, hword] at h3
      omega
  have hybord : orderOf ((y' : ↥(Cen w)) : ↥(Cen w) ⧸ zpowers w') = 3 :=
    orderOf_eq_prime hyb3 hyb1
  have h7' : 7 ∣ Nat.card ↥(centralizer ({y'} : Set ↥(Cen w))) := by
    have hOodd : Odd (Nat.card (Open.fusionOddCore ↥(Cen a.y))) :=
      s3l_natCard_fusionOddCore_odd _
    have hw''2 : (⟨w, hwy⟩ : ↥(Cen a.y)) * ⟨w, hwy⟩ = 1 := Subtype.ext hw2
    have hT2 := map_centralizer_eq_of_odd (G := ↥(Cen a.y)) (Open.fusionOddCore ↥(Cen a.y))
      hOodd hw''2
    have h7a : 7 ∣ Nat.card ↥((centralizer ({(⟨w, hwy⟩ : ↥(Cen a.y))} : Set ↥(Cen a.y))).map
        (QuotientGroup.mk' (Open.fusionOddCore ↥(Cen a.y)))) := by
      rw [hT2]; exact h7
    have h7b := h7a.trans (Subgroup.card_map_dvd _ _)
    have e1 := s3l_card_centralizer_subtype (Cen a.y) w hwy
    have e2 := s3l_card_centralizer_subtype (Cen w) a.y hyw
    have e3 : (⟨a.y, hyw⟩ : ↥(Cen w)) = y' := Subtype.ext hy'v.symm
    rw [e3] at e2
    rw [e2, inf_comm, ← e1]
    exact h7b
  let π : ↥(Cen w) →* ↥(Cen w) ⧸ zpowers w' := QuotientGroup.mk' (zpowers w')
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hkerπ : π.ker = zpowers w' := QuotientGroup.ker_mk' _
  have hcardw' : Nat.card (zpowers w') = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hw2') hw1'
  have hkerP : π.ker ≤ centralizer ({y'} : Set ↥(Cen w)) := by
    rw [hkerπ, zpowers_le]
    refine mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hw'v, hy'v]
    exact mem_Cen.1 hwy
  have hcomap : ((centralizer ({y'} : Set ↥(Cen w))).map π).comap π =
      centralizer ({y'} : Set ↥(Cen w)) := Subgroup.comap_map_eq_self hkerP
  have hcardP : Nat.card ↥(centralizer ({y'} : Set ↥(Cen w))) =
      2 * Nat.card ↥((centralizer ({y'} : Set ↥(Cen w))).map π) := by
    have := s3l_natCard_comap_of_surjective π hπ ((centralizer ({y'} : Set ↥(Cen w))).map π)
    rw [hcomap, hkerπ, hcardw'] at this
    exact this
  have h7Q : 7 ∣ Nat.card ↥((centralizer ({y'} : Set ↥(Cen w))).map π) := by
    rw [hcardP] at h7'
    exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h7'
  have hQle : (centralizer ({y'} : Set ↥(Cen w))).map π ≤
      centralizer ({((y' : ↥(Cen w)) : ↥(Cen w) ⧸ zpowers w')} :
        Set (↥(Cen w) ⧸ zpowers w')) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x * y' = y' * x := mem_centralizer_singleton_iff.1 hx
    refine mem_centralizer_singleton_iff.2 ?_
    change (x : ↥(Cen w) ⧸ zpowers w') * (y' : ↥(Cen w) ⧸ zpowers w') =
      (y' : ↥(Cen w) ⧸ zpowers w') * (x : ↥(Cen w) ⧸ zpowers w')
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hx']
  exact hc (↥(Cen w) ⧸ zpowers w')
    ((hb.setting.1.isKGroupCat_centralizer hw1).quotient (zpowers w')) hodd _ hsord hiso _ hybord
    (h7Q.trans (Subgroup.card_dvd_of_le hQle))

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
