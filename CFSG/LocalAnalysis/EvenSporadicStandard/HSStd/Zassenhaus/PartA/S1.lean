module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Stages
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

theorem mem_Vsub_iff {t u : G} (ht : t * t = 1) (hu : u * u = 1) (htu : t * u = u * t) {y : G} :
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

theorem commute_Vsub {t u c : G} (h1 : c * t = t * c) (h2 : c * u = u * c) :
    ∀ y ∈ Vsub t u, c * y = y * c := by
  have hle : Vsub t u ≤ Cen c :=
    sup_le ((zpowers_le).2 (mem_Cen.2 h1.symm)) ((zpowers_le).2 (mem_Cen.2 h2.symm))
  intro y hy
  exact (mem_Cen.1 (hle hy)).symm

theorem Vsub_comm {t u : G} (htu : t * u = u * t) {y y' : G} (hy : y ∈ Vsub t u)
    (hy' : y' ∈ Vsub t u) : y * y' = y' * y := by
  have ht : ∀ y ∈ Vsub t u, t * y = y * t := commute_Vsub rfl htu
  have hu : ∀ y ∈ Vsub t u, u * y = y * u := commute_Vsub htu.symm rfl
  exact commute_Vsub (ht y hy).symm (hu y hy).symm y' hy'

theorem mem_centralizer_Vsub {t u c : G} :
    c ∈ centralizer ((Vsub t u : Subgroup G) : Set G) ↔ c * t = t * c ∧ c * u = u * c := by
  constructor
  · intro hc
    exact ⟨(mem_centralizer_iff.1 hc t (mem_sup_left (mem_zpowers t))).symm,
      (mem_centralizer_iff.1 hc u (mem_sup_right (mem_zpowers u))).symm⟩
  · rintro ⟨h1, h2⟩
    exact mem_centralizer_iff.2 fun y hy => (commute_Vsub h1 h2 y hy).symm

theorem mem_normalizer_Vsub [Finite G] {t u g : G} (ht : t * t = 1) (hu : u * u = 1)
    (htu : t * u = u * t) (h1 : g * t * g⁻¹ ∈ Vsub t u) (h2 : g * u * g⁻¹ ∈ Vsub t u) :
    g ∈ normalizer ((Vsub t u : Subgroup G) : Set G) := by
  have hmap : ∀ y ∈ Vsub t u, g * y * g⁻¹ ∈ Vsub t u := by
    intro y hy
    rcases (mem_Vsub_iff ht hu htu).1 hy with h | h | h | h <;> rw [h]
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

theorem conj_comm_iff {g c s : G} :
    (g * c * g⁻¹) * (g * s * g⁻¹) = (g * s * g⁻¹) * (g * c * g⁻¹) ↔ c * s = s * c := by
  constructor
  · intro h
    have h' : g * (c * s) * g⁻¹ = g * (s * c) * g⁻¹ := by
      calc g * (c * s) * g⁻¹ = (g * c * g⁻¹) * (g * s * g⁻¹) := by group
        _ = (g * s * g⁻¹) * (g * c * g⁻¹) := h
        _ = g * (s * c) * g⁻¹ := by group
    have := mul_right_cancel h'
    exact mul_left_cancel this
  · intro h
    calc (g * c * g⁻¹) * (g * s * g⁻¹) = g * (c * s) * g⁻¹ := by group
      _ = g * (s * c) * g⁻¹ := by rw [h]
      _ = (g * s * g⁻¹) * (g * c * g⁻¹) := by group

theorem commutator_central_mul {v v' a b : G} (hva : v * a = a * v) (hvb : v * b = b * v)
    (hv'a : v' * a = a * v') (hv'b : v' * b = b * v') (hvv' : v * v' = v' * v) :
    ⁅v * a, v' * b⁆ = ⁅a, b⁆ := by
  have cva : Commute v a := hva
  have cvb : Commute v b := hvb
  have cv'a : Commute v' a := hv'a
  have cv'b : Commute v' b := hv'b
  have cvv : Commute v v' := hvv'
  have hxy : (v * a) * (v' * b) = (v * v') * (a * b) := by
    calc (v * a) * (v' * b) = v * (a * v') * b := by group
      _ = v * (v' * a) * b := by rw [← hv'a]
      _ = (v * v') * (a * b) := by group
  have hyx : (v' * b) * (v * a) = (v * v') * (b * a) := by
    calc (v' * b) * (v * a) = v' * (b * v) * a := by group
      _ = v' * (v * b) * a := by rw [← hvb]
      _ = (v' * v) * (b * a) := by group
      _ = (v * v') * (b * a) := by rw [hvv']
  have hcomm : Commute (v * v') (a * b * (b * a)⁻¹) :=
    ((cva.mul_left cv'a).mul_right (cvb.mul_left cv'b)).mul_right
      (((cvb.mul_left cv'b).mul_right (cva.mul_left cv'a)).inv_right)
  have key : ⁅v * a, v' * b⁆ = ((v * a) * (v' * b)) * ((v' * b) * (v * a))⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [key, hxy, hyx, mul_inv_rev, ← mul_assoc]
  have h2 : (v * v') * (a * b) * (b * a)⁻¹ * (v * v')⁻¹ = a * b * (b * a)⁻¹ := by
    have := hcomm.mul_inv_cancel
    simpa [mul_assoc] using this
  rw [h2]
  simp only [commutatorElement_def]
  group

end Generic

structure FusionSetup (G : Type) [Group G] (L A : Subgroup G) (t u : G) : Prop where
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

theorem FusionSetup.t_ne (S : FusionSetup G L A t u) : t ≠ 1 := fun h =>
  S.t_nmem (h ▸ one_mem L)

theorem FusionSetup.t_mem_V (_ : FusionSetup G L A t u) : t ∈ Vsub t u :=
  mem_sup_left (mem_zpowers t)

theorem FusionSetup.u_mem_V (_ : FusionSetup G L A t u) : u ∈ Vsub t u :=
  mem_sup_right (mem_zpowers u)

theorem FusionSetup.A_comm_V (S : FusionSetup G L A t u) {a : G} (ha : a ∈ A) :
    ∀ y ∈ Vsub t u, a * y = y * a :=
  commute_Vsub (S.t_comm a (S.A_le ha)) (S.A_u a ha)

theorem FusionSetup.A_mem_cent (S : FusionSetup G L A t u) {a : G} (ha : a ∈ A) :
    a ∈ centralizer ((Vsub t u : Subgroup G) : Set G) :=
  mem_centralizer_Vsub.2 ⟨S.t_comm a (S.A_le ha), S.A_u a ha⟩

theorem FusionSetup.V_inf_A (S : FusionSetup G L A t u) {y : G} (hy : y ∈ Vsub t u) (hA : y ∈ A) :
    y = 1 := by
  rcases (mem_Vsub_iff S.t_sq S.u_sq S.tu).1 hy with h | h | h | h
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

theorem FusionSetup.L_u_decomp (S : FusionSetup G L A t u) {l : G} (hl : l ∈ L)
    (hlu : l * u = u * l) : l ∈ A ∨ u⁻¹ * l ∈ A := by
  have h1 : l ∈ L ⊓ centralizer ({u} : Set G) := ⟨hl, mem_centralizer_singleton_iff.2 hlu⟩
  rw [S.Lu, sup_comm] at h1
  exact mem_or_inv_mul_mem_of_mem_sup_zpowers S.u_sq S.A_u h1

theorem FusionSetup.cent_V_decomp (S : FusionSetup G L A t u) {c : G}
    (hc : c ∈ centralizer ((Vsub t u : Subgroup G) : Set G)) :
    ∃ v ∈ Vsub t u, ∃ a ∈ A, c = v * a := by
  obtain ⟨hct, hcu⟩ := mem_centralizer_Vsub.1 hc
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

section FusionA

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {t u : G}

theorem fusion_a_core (S : FusionSetup G L A t u)
    (hcomp : ∀ α : MulAut ↥A, ∃ b : ↥A, ∀ x : ↥A, α x = b * x * b⁻¹) :
    ∀ g ∈ normalizer ((Vsub t u : Subgroup G) : Set G),
      ∃ ā ∈ A, ∃ g' ∈ centralizer ((derivedIn A : Subgroup G) : Set G) ⊓
          normalizer ((Vsub t u : Subgroup G) : Set G),
        g = ā * g' ∧ ∀ y ∈ Vsub t u, g' * y * g'⁻¹ = g * y * g⁻¹ := by
  intro g hg
  have hgV : ∀ y, y ∈ Vsub t u ↔ g * y * g⁻¹ ∈ Vsub t u := mem_normalizer_iff.1 hg
  have hgV' : ∀ y ∈ Vsub t u, g⁻¹ * y * g ∈ Vsub t u := by
    intro y hy
    refine (hgV _).2 ?_
    have : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [this]
    exact hy
  have hcen : ∀ a ∈ A, g * a * g⁻¹ ∈ centralizer ((Vsub t u : Subgroup G) : Set G) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro y hy
    have hcomm := S.A_comm_V ha (g⁻¹ * y * g) (hgV' y hy)
    calc y * (g * a * g⁻¹) = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * a * g⁻¹) * y := by group
  have hdec : ∀ a : ↥A, ∃ a' : ↥A, ∃ v ∈ Vsub t u, g * (a : G) * g⁻¹ = v * (a' : G) := by
    intro a
    obtain ⟨v, hv, a', ha', h⟩ := S.cent_V_decomp (hcen a a.2)
    exact ⟨⟨a', ha'⟩, v, hv, h⟩
  choose α0 v hv hα0 using hdec
  have huniq : ∀ (v v' a a' : G), v ∈ Vsub t u → v' ∈ Vsub t u → a ∈ A → a' ∈ A →
      v * a = v' * a' → a = a' := by
    intro v v' a a' hv hv' ha ha' h
    have h1 : v'⁻¹ * v = a' * a⁻¹ := by
      calc v'⁻¹ * v = v'⁻¹ * (v * a) * a⁻¹ := by group
        _ = v'⁻¹ * (v' * a') * a⁻¹ := by rw [h]
        _ = a' * a⁻¹ := by group
    have hyV : a' * a⁻¹ ∈ Vsub t u := by
      rw [← h1]
      exact mul_mem (inv_mem hv') hv
    have := S.V_inf_A hyV (mul_mem ha' (inv_mem ha))
    exact (mul_inv_eq_one.1 this).symm
  have hmul : ∀ a b : ↥A, α0 (a * b) = α0 a * α0 b := by
    intro a b
    have h1 : g * ((a * b : ↥A) : G) * g⁻¹ = (v a * v b) * ((α0 a : G) * (α0 b : G)) := by
      calc g * ((a * b : ↥A) : G) * g⁻¹ = (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹) := by
            push_cast; group
        _ = (v a * (α0 a : G)) * (v b * (α0 b : G)) := by rw [hα0 a, hα0 b]
        _ = v a * ((α0 a : G) * v b) * (α0 b : G) := by group
        _ = v a * (v b * (α0 a : G)) * (α0 b : G) := by rw [S.A_comm_V (α0 a).2 _ (hv b)]
        _ = (v a * v b) * ((α0 a : G) * (α0 b : G)) := by group
    have := huniq _ _ _ _ (hv _) (mul_mem (hv a) (hv b)) (α0 (a * b)).2
      (mul_mem (α0 a).2 (α0 b).2) ((hα0 _).symm.trans h1)
    exact Subtype.ext this
  let αh : ↥A →* ↥A := MonoidHom.mk' α0 hmul
  have hinj : Function.Injective αh := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : α0 a = 1 := ha
    have h2 : g * (a : G) * g⁻¹ ∈ Vsub t u := by
      rw [hα0 a, h1]
      simpa using hv a
    have h3 := S.V_inf_A ((hgV _).2 h2) a.2
    exact Subtype.ext h3
  let α : MulAut ↥A := MulEquiv.ofBijective αh ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  obtain ⟨b, hb⟩ := hcomp α
  have hαb : ∀ x : ↥A, ((α0 x : ↥A) : G) = (b : G) * (x : G) * (b : G)⁻¹ := by
    intro x
    exact congrArg Subtype.val (hb x)
  have hbV : (b : G) ∈ centralizer ((Vsub t u : Subgroup G) : Set G) := S.A_mem_cent b.2
  have hbN : (b : G) ∈ normalizer ((Vsub t u : Subgroup G) : Set G) := centralizer_le_normalizer _ hbV
  have hbc : ∀ y ∈ Vsub t u, (b : G)⁻¹ * y * (b : G) = y := by
    intro y hy
    have := S.A_comm_V b.2 y hy
    calc (b : G)⁻¹ * y * (b : G) = (b : G)⁻¹ * (y * (b : G)) := mul_assoc _ _ _
      _ = (b : G)⁻¹ * ((b : G) * y) := by rw [this]
      _ = y := inv_mul_cancel_left _ _
  have hact : ∀ a : ↥A, ((b : G)⁻¹ * g) * (a : G) * ((b : G)⁻¹ * g)⁻¹ = v a * (a : G) := by
    intro a
    calc ((b : G)⁻¹ * g) * (a : G) * ((b : G)⁻¹ * g)⁻¹
        = (b : G)⁻¹ * (g * (a : G) * g⁻¹) * (b : G) := by group
      _ = (b : G)⁻¹ * (v a * ((b : G) * (a : G) * (b : G)⁻¹)) * (b : G) := by
          rw [hα0 a, hαb a]
      _ = ((b : G)⁻¹ * v a * (b : G)) * (a : G) := by group
      _ = v a * (a : G) := by rw [hbc _ (hv a)]
  refine ⟨b, b.2, (b : G)⁻¹ * g, mem_inf.2 ⟨?_, ?_⟩, (mul_inv_cancel_left _ _).symm, ?_⟩
  ·
    rw [mem_centralizer_iff]
    intro j hj
    have hJ : derivedIn A ≤ centralizer ({(b : G)⁻¹ * g} : Set G) := by
      unfold derivedIn
      rw [Subgroup.map_le_iff_le_comap, commutator_eq_closure, Subgroup.closure_le]
      rintro _ ⟨a₁, a₂, rfl⟩
      show A.subtype ⁅a₁, a₂⁆ ∈ centralizer ({(b : G)⁻¹ * g} : Set G)
      rw [map_commutatorElement, mem_centralizer_singleton_iff]
      set g' := (b : G)⁻¹ * g with hg'
      have h1 := hact a₁
      have h2 := hact a₂
      have h3 : g' * ⁅(a₁ : G), (a₂ : G)⁆ * g'⁻¹ = ⁅(a₁ : G), (a₂ : G)⁆ := by
        calc g' * ⁅(a₁ : G), (a₂ : G)⁆ * g'⁻¹
            = ⁅g' * (a₁ : G) * g'⁻¹, g' * (a₂ : G) * g'⁻¹⁆ := by
              simp only [commutatorElement_def]; group
          _ = ⁅v a₁ * (a₁ : G), v a₂ * (a₂ : G)⁆ := by rw [h1, h2]
          _ = ⁅(a₁ : G), (a₂ : G)⁆ := by
              refine commutator_central_mul ?_ ?_ ?_ ?_ (Vsub_comm S.tu (hv a₁) (hv a₂))
              · exact (S.A_comm_V a₁.2 _ (hv a₁)).symm
              · exact (S.A_comm_V a₂.2 _ (hv a₁)).symm
              · exact (S.A_comm_V a₁.2 _ (hv a₂)).symm
              · exact (S.A_comm_V a₂.2 _ (hv a₂)).symm
      show ⁅(a₁ : G), (a₂ : G)⁆ * g' = g' * ⁅(a₁ : G), (a₂ : G)⁆
      calc ⁅(a₁ : G), (a₂ : G)⁆ * g' = g' * (g'⁻¹ * ⁅(a₁ : G), (a₂ : G)⁆ * g') := by group
        _ = g' * (g'⁻¹ * (g' * ⁅(a₁ : G), (a₂ : G)⁆ * g'⁻¹) * g') := by rw [h3]
        _ = g' * ⁅(a₁ : G), (a₂ : G)⁆ := by group
    exact mem_centralizer_singleton_iff.1 (hJ hj)
  · exact (normalizer ((Vsub t u : Subgroup G) : Set G)).mul_mem
      ((normalizer ((Vsub t u : Subgroup G) : Set G)).inv_mem hbN) hg
  · intro y hy
    have h1 := hbc _ (((hgV y).1 hy))
    calc ((b : G)⁻¹ * g) * y * ((b : G)⁻¹ * g)⁻¹ = (b : G)⁻¹ * (g * y * g⁻¹) * (b : G) := by group
      _ = g * y * g⁻¹ := h1

end FusionA

section FusionB

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {t u : G}

theorem FusionSetup.card_eq_two_mul_inf (S : FusionSetup G L A t u) {D : Subgroup G}
    (hD : ∀ c ∈ D, c * t = t * c) (htD : t ∈ D) : Nat.card D = 2 * Nat.card ↥(D ⊓ L) := by
  have hle := card_le_two_mul_card_inf (D := D) (L := L) (t := t) (fun x hx =>
    mem_or_inv_mul_mem_of_mem_sup_zpowers S.t_sq S.t_comm (by
      rw [← S.cent_t]
      exact mem_centralizer_singleton_iff.2 (hD x hx)))
  have hge := two_mul_card_le_of_exists (K := D ⊓ L) (C := D) inf_le_left
    ⟨t, htD, fun h => S.t_nmem h.2⟩
  omega

theorem FusionSetup.card_cent_V (S : FusionSetup G L A t u) :
    Nat.card (centralizer ((Vsub t u : Subgroup G) : Set G)) =
      2 * Nat.card ↥(L ⊓ centralizer ({u} : Set G)) := by
  have h := S.card_eq_two_mul_inf (D := centralizer ((Vsub t u : Subgroup G) : Set G))
    (fun c hc => (mem_centralizer_Vsub.1 hc).1) (mem_centralizer_Vsub.2 ⟨rfl, S.tu⟩)
  have hDL : centralizer ((Vsub t u : Subgroup G) : Set G) ⊓ L =
      L ⊓ centralizer ({u} : Set G) := by
    ext c
    constructor
    · rintro ⟨hc, hcL⟩
      exact ⟨hcL, mem_centralizer_singleton_iff.2 (mem_centralizer_Vsub.1 hc).2⟩
    · rintro ⟨hcL, hcu⟩
      exact ⟨mem_centralizer_Vsub.2 ⟨S.t_comm c hcL, mem_centralizer_singleton_iff.1 hcu⟩, hcL⟩
  rw [h, hDL]

theorem fusion_b_core (S : FusionSetup G L A t u) (hHS : IsSporadic ↥L .HS)
    (hu2 : orderOf u = 2) (hLu : Nat.card ↥(L ⊓ centralizer ({u} : Set G)) = 2880)
    (hfa : ∀ g ∈ normalizer ((Vsub t u : Subgroup G) : Set G),
      ∃ ā ∈ A, ∃ g' ∈ centralizer ((derivedIn A : Subgroup G) : Set G) ⊓
          normalizer ((Vsub t u : Subgroup G) : Set G),
        g = ā * g' ∧ ∀ y ∈ Vsub t u, g' * y * g'⁻¹ = g * y * g⁻¹)
    {x : G} (hx : x = u ∨ x = t * u) (hconj : IsConj t x) :
    ∃ h ∈ centralizer ((derivedIn A : Subgroup G) : Set G), h * t * h⁻¹ = x := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right S.t_sq
  have htV : t ∈ Vsub t u := S.t_mem_V
  have huV : u ∈ Vsub t u := S.u_mem_V
  have hxV : x ∈ Vsub t u := by
    rcases hx with rfl | rfl
    · exact huV
    · exact mul_mem htV huV
  have hxt : x * t = t * x := by
    rcases hx with rfl | rfl
    · exact S.tu.symm
    · calc t * u * t = t * (u * t) := mul_assoc _ _ _
        _ = t * (t * u) := by rw [S.tu]
  have hux : u = x ∨ u = t * x := by
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by rw [← mul_assoc, S.t_sq, one_mul])
  have hx_ne : x ≠ t := by
    rcases hx with rfl | rfl
    · intro h
      exact S.t_nmem (h ▸ S.u_mem)
    · intro h
      apply S.u_ne
      have : t * u = t * 1 := by rw [mul_one]; exact h
      exact mul_left_cancel this
  have hgx : g⁻¹ * x * g = t := by rw [← hg]; group
  obtain ⟨p, hp⟩ : ∃ p : G, p = g⁻¹ * t * g := ⟨_, rfl⟩
  have hpg : g * p * g⁻¹ = t := by rw [hp]; group
  have hp_sq : p * p = 1 := by
    calc p * p = g⁻¹ * (t * t) * g := by rw [hp]; group
      _ = 1 := by rw [S.t_sq]; group
  have htp : t * p = p * t := by
    have h1 : g⁻¹ * (x * t) * g = g⁻¹ * (t * x) * g := by rw [hxt]
    calc t * p = (g⁻¹ * x * g) * (g⁻¹ * t * g) := by rw [hgx, hp]
      _ = g⁻¹ * (x * t) * g := by group
      _ = g⁻¹ * (t * x) * g := h1
      _ = (g⁻¹ * t * g) * (g⁻¹ * x * g) := by group
      _ = p * t := by rw [hgx, hp]
  have hp_ne1 : p ≠ 1 := by
    intro h
    apply S.t_ne
    rw [← hpg, h]
    group
  have hp_net : p ≠ t := by
    intro h
    apply hx_ne
    rw [← hg]
    calc g * t * g⁻¹ = g * p * g⁻¹ := by rw [h]
      _ = t := hpg
  have hpc : p ∈ L ⊔ zpowers t := by
    rw [← S.cent_t]
    exact mem_centralizer_singleton_iff.2 htp.symm
  obtain ⟨w, hwL, hwp⟩ : ∃ w ∈ L, w = p ∨ w = t * p := by
    rcases mem_or_inv_mul_mem_of_mem_sup_zpowers S.t_sq S.t_comm hpc with h | h
    · exact ⟨p, h, Or.inl rfl⟩
    · exact ⟨t⁻¹ * p, h, Or.inr (by rw [hti])⟩
  have hw_sq : w * w = 1 := by
    rcases hwp with hwp | hwp <;> rw [hwp]
    · exact hp_sq
    · calc t * p * (t * p) = t * (p * t) * p := by group
        _ = t * (t * p) * p := by rw [← htp]
        _ = (t * t) * (p * p) := by group
        _ = 1 := by rw [S.t_sq, hp_sq, one_mul]
  have hw_ne : w ≠ 1 := by
    rcases hwp with hwp | hwp <;> rw [hwp]
    · exact hp_ne1
    · intro h
      apply hp_net
      have := eq_inv_of_mul_eq_one_right h
      rw [this, hti]
  have hw2 : orderOf w = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hw_sq) hw_ne
  have hgw : g * w * g⁻¹ ∈ Vsub t u := by
    rcases hwp with hwp | hwp <;> rw [hwp]
    · rw [hpg]; exact htV
    · have : g * (t * p) * g⁻¹ = (g * t * g⁻¹) * (g * p * g⁻¹) := by group
      rw [this, hg, hpg]
      exact mul_mem hxV htV
  let D : Subgroup G := centralizer ((Vsub t u : Subgroup G) : Set G)
  let D' : Subgroup G := D.comap (MulAut.conj g).toMonoidHom
  have hD'mem : ∀ c, c ∈ D' ↔ g * c * g⁻¹ ∈ D := fun c => Iff.rfl
  have hD'card : Nat.card D' = Nat.card D :=
    Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv (fun c => Iff.rfl))
  have hDcard : Nat.card D = 5760 := by
    have := S.card_cent_V
    rw [hLu] at this
    exact this
  have hxD : x ∈ D := mem_centralizer_iff.2 fun y hy => Vsub_comm S.tu hy hxV
  have htD' : t ∈ D' := (hD'mem t).2 (by rw [hg]; exact hxD)
  have hD't : ∀ c ∈ D', c * t = t * c := by
    intro c hc
    have h1 := mem_centralizer_iff.1 ((hD'mem c).1 hc) x hxV
    exact (conj_comm_iff (g := g) (c := c) (s := t)).1 (by rw [hg]; exact h1.symm)
  have hDL : D' ⊓ L = L ⊓ centralizer ({w} : Set G) := by
    ext c
    constructor
    · rintro ⟨hc, hcL⟩
      refine ⟨hcL, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := mem_centralizer_iff.1 ((hD'mem c).1 hc) t htV
      have h2 : c * p = p * c :=
        (conj_comm_iff (g := g) (c := c) (s := p)).1 (by rw [hpg]; exact h1.symm)
      have h3 := S.t_comm c hcL
      rcases hwp with hwp | hwp
      · rw [hwp]; exact h2
      · rw [hwp]
        calc c * (t * p) = (c * t) * p := (mul_assoc _ _ _).symm
          _ = (t * c) * p := by rw [h3]
          _ = t * (c * p) := mul_assoc _ _ _
          _ = t * (p * c) := by rw [h2]
          _ = (t * p) * c := (mul_assoc _ _ _).symm
    · rintro ⟨hcL, hcw⟩
      refine ⟨?_, hcL⟩
      have hcw' := mem_centralizer_singleton_iff.1 hcw
      have h3 := S.t_comm c hcL
      have h2 : c * p = p * c := by
        rcases hwp with hwp | hwp
        · rw [hwp] at hcw'; exact hcw'
        · rw [hwp] at hcw'
          have : t * (c * p) = t * (p * c) := by
            calc t * (c * p) = (t * c) * p := (mul_assoc _ _ _).symm
              _ = (c * t) * p := by rw [h3]
              _ = c * (t * p) := mul_assoc _ _ _
              _ = (t * p) * c := hcw'
              _ = t * (p * c) := mul_assoc _ _ _
          exact mul_left_cancel this
      have hdt : (g * c * g⁻¹) * t = t * (g * c * g⁻¹) := by
        have := (conj_comm_iff (g := g) (c := c) (s := p)).2 h2
        rw [hpg] at this
        exact this
      have hdx : (g * c * g⁻¹) * x = x * (g * c * g⁻¹) := by
        have := (conj_comm_iff (g := g) (c := c) (s := t)).2 h3
        rw [hg] at this
        exact this
      refine (hD'mem c).2 (mem_centralizer_Vsub.2 ⟨hdt, ?_⟩)
      rcases hux with h | h
      · rw [h]; exact hdx
      · rw [h]
        have c1 : Commute (g * c * g⁻¹) t := hdt
        have c2 : Commute (g * c * g⁻¹) x := hdx
        exact (c1.mul_right c2).eq
  have hcardw : Nat.card ↥(L ⊓ centralizer ({w} : Set G)) = 2880 := by
    have h := S.card_eq_two_mul_inf (D := D') hD't htD'
    rw [hDL, hD'card, hDcard] at h
    omega
  obtain ⟨l, hl, hlw⟩ := exists_conj_in_L hHS hwL S.u_mem hw2 hu2 (by rw [hcardw, hLu])
  have hht : (g * l⁻¹) * t * (g * l⁻¹)⁻¹ = x := by
    have := S.t_comm l⁻¹ (inv_mem hl)
    calc (g * l⁻¹) * t * (g * l⁻¹)⁻¹ = g * (l⁻¹ * t) * l * g⁻¹ := by group
      _ = g * (t * l⁻¹) * l * g⁻¹ := by rw [this]
      _ = g * t * g⁻¹ := by group
      _ = x := hg
  have hhu : (g * l⁻¹) * u * (g * l⁻¹)⁻¹ = g * w * g⁻¹ := by
    calc (g * l⁻¹) * u * (g * l⁻¹)⁻¹ = (g * l⁻¹) * (l * w * l⁻¹) * (g * l⁻¹)⁻¹ := by rw [hlw]
      _ = g * w * g⁻¹ := by group
  have hN : g * l⁻¹ ∈ normalizer ((Vsub t u : Subgroup G) : Set G) :=
    mem_normalizer_Vsub S.t_sq S.u_sq S.tu (by rw [hht]; exact hxV) (by rw [hhu]; exact hgw)
  obtain ⟨_, _, h', hh', _, hact⟩ := hfa _ hN
  exact ⟨h', hh'.1, by rw [hact t htV, hht]⟩

end FusionB

section Main

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem alternatingGroup_six_nonabelian' :
    ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    fun h => ?_⟩
  have := congrArg Subtype.val h
  revert this
  decide

theorem hcomp_of_equiv {A : Subgroup G} (e : ↥A ≃* MulAut (alternatingGroup (Fin 6))) :
    ∀ α : MulAut ↥A, ∃ b : ↥A, ∀ x : ↥A, α x = b * x * b⁻¹ := by
  intro α
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨β, hβ⟩ := mulAut_mulAut_eq_conj alternatingGroup_six_nonabelian'
    ((e.symm.trans α).trans e)
  refine ⟨e.symm β, fun x => e.injective ?_⟩
  have h1 : e (α x) = (MulAut.conj β) (e x) := by
    have := congrArg (fun f : MulAut (MulAut (alternatingGroup (Fin 6))) => f (e x)) hβ
    simpa using this
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]

theorem PA0.fusionSetup (hb : PAB G L t E W z) (a : PA0 L t E z) :
    FusionSetup G L a.Abar t a.u := by
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
  · exact t_not_mem_of_isSporadic_hs hb.setting.2.1 hb.t_cent hb.t_ord

theorem PA0.u_mul_u (hb : PAB G L t E W z) (a : PA0 L t E z) : a.u * a.u = 1 :=
  (PA0.fusionSetup hb a).u_sq

theorem PA0.t_mul_u (hb : PAB G L t E W z) (a : PA0 L t E z) : t * a.u = a.u * t :=
  (PA0.fusionSetup hb a).tu

theorem PA0.orderOf_u (hb : PAB G L t E W z) (a : PA0 L t E z) : orderOf a.u = 2 := by
  have S := PA0.fusionSetup hb a
  exact orderOf_eq_prime (by rw [pow_two]; exact S.u_sq) S.u_ne

theorem PA0.u_mem_L (a : PA0 L t E z) : a.u ∈ L := (a.K₀_le a.u_mem).1

theorem PA0.card_cent_V (hb : PAB G L t E W z) (a : PA0 L t E z) :
    Nat.card (centralizer ((Vsub t a.u : Subgroup G) : Set G)) = 5760 := by
  have := (PA0.fusionSetup hb a).card_cent_V
  rw [a.card_Lu] at this
  exact this

theorem fusion_a_strong (hb : PAB G L t E W z) (a : PA0 L t E z) :
    ∀ g ∈ normalizer ((Vsub t a.u : Subgroup G) : Set G),
      ∃ ā ∈ a.Abar, ∃ g' ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) ⊓
          normalizer ((Vsub t a.u : Subgroup G) : Set G),
        g = ā * g' ∧ ∀ y ∈ Vsub t a.u, g' * y * g'⁻¹ = g * y * g⁻¹ :=
  fusion_a_core (PA0.fusionSetup hb a) (hcomp_of_equiv a.eAbar)

theorem fusion_a (hb : PAB G L t E W z) (a : PA0 L t E z) :
    ∀ g ∈ normalizer ((Vsub t a.u : Subgroup G) : Set G),
      ∃ ā ∈ a.Abar, ∃ g' ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) ⊓
          normalizer ((Vsub t a.u : Subgroup G) : Set G), g = ā * g' := by
  intro g hg
  obtain ⟨ā, hā, g', hg', h, -⟩ := fusion_a_strong hb a g hg
  exact ⟨ā, hā, g', hg', h⟩

theorem fusion_b (hb : PAB G L t E W z) (a : PA0 L t E z) :
    ∀ x, (x = a.u ∨ x = t * a.u) →
      (IsConj t x ↔ ∃ h ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G),
        h * t * h⁻¹ = x) := by
  intro x hx
  constructor
  · intro hconj
    exact fusion_b_core (PA0.fusionSetup hb a) hb.setting.2.1 (PA0.orderOf_u hb a) a.card_Lu
      (fusion_a_strong hb a) hx hconj
  · rintro ⟨h, -, hh⟩
    exact isConj_iff.2 ⟨h, hh⟩

end Main

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
