module

public import CFSG.LocalAnalysis.ComponentClassification.Layer

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc

open CFSG CFSG.Open
open scoped commutatorElement

private theorem lad_conj_comm {G : Type*} [Group G] {u v : G} (h : u * v = v * u) (a : G) :
    u * (v * a * v⁻¹) * u⁻¹ = v * (u * a * u⁻¹) * v⁻¹ :=
  calc u * (v * a * v⁻¹) * u⁻¹ = (u * v) * a * (u * v)⁻¹ := by group
    _ = (v * u) * a * (v * u)⁻¹ := by rw [h]
    _ = v * (u * a * u⁻¹) * v⁻¹ := by group

private theorem lad_mem_center_of_conj_eq {Q : Type*} [Group Q] {a b : Q}
    (h : ∀ t : Q, a * t * a⁻¹ = b * t * b⁻¹) : a * b⁻¹ ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  intro m
  have h3 : a * (b⁻¹ * m * b) * a⁻¹ = m := by rw [h]; group
  calc m * (a * b⁻¹) = (a * (b⁻¹ * m * b) * a⁻¹) * (a * b⁻¹) := by rw [h3]
    _ = a * b⁻¹ * m := by group

private theorem lad_perfect_comm {Q : Type*} [Group Q] (S : Subgroup Q) [Group.IsPerfect S] (y : Q)
    (h : ∀ l ∈ S, ⁅l, y⁆ ∈ Subgroup.center Q) : ∀ l ∈ S, l * y = y * l := by
  let φ : S →* Subgroup.center Q := MonoidHom.mk' (fun l => ⟨⁅(l : Q), y⁆, h l l.2⟩) (by
    intro a b
    apply Subtype.ext
    have hb := Subgroup.mem_center_iff.mp (h b b.2)
    have ha := Subgroup.mem_center_iff.mp (h a a.2)
    show ⁅((a * b : S) : Q), y⁆ = ⁅(a : Q), y⁆ * ⁅(b : Q), y⁆
    have e : ⁅((a * b : S) : Q), y⁆ = (a : Q) * ⁅(b : Q), y⁆ * (a : Q)⁻¹ * ⁅(a : Q), y⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul]; group
    rw [e, hb (a : Q), mul_inv_cancel_right]
    exact ha _)
  have hφ : ∀ l, φ l = 1 := by
    have hle : commutator S ≤ φ.ker := by
      rw [commutator_def]
      refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext ((Subgroup.mem_center_iff.mp (φ b).2) (φ a))
    rw [Group.IsPerfect.commutator_eq_top] at hle
    intro l
    exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top l))
  intro l hl
  exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val (hφ ⟨l, hl⟩))

private theorem lad_exists_perfect_lift {Q : Type*} [Group Q] [Finite Q]
    (P : Subgroup (MulAut Q)) [Group.IsPerfect P] (hP : P ≤ (MulAut.conj : Q →* MulAut Q).range) :
    ∃ S : Subgroup Q, Group.IsPerfect S ∧ S.map (MulAut.conj : Q →* MulAut Q) = P := by
  obtain ⟨S, hS, hmin⟩ := (wellFounded_lt (α := Subgroup Q)).has_min
    {S : Subgroup Q | S.map (MulAut.conj : Q →* MulAut Q) = P}
    ⟨P.comap (MulAut.conj : Q →* MulAut Q), by
      rw [Set.mem_setOf_eq, Subgroup.map_comap_eq]; exact inf_eq_right.mpr hP⟩
  refine ⟨S, ?_, hS⟩
  have hmap : ⁅S, S⁆.map (MulAut.conj : Q →* MulAut Q) = P := by
    rw [Subgroup.map_commutator, show S.map (MulAut.conj : Q →* MulAut Q) = P from hS]
    exact Subgroup.commutator_eq_self
  rw [Subgroup.isPerfect_iff]
  exact (Subgroup.commutator_le_self S).eq_or_lt.resolve_right (hmin _ hmap)

theorem A_normalized {G : Type} [Group G] {F L A : Subgroup G} {y z : G}
    (hFL : ∀ f ∈ F, ∀ l ∈ L, f * l * f⁻¹ ∈ L) (hzF : ∀ x ∈ F, x * z = z * x)
    (hzy : ∀ l ∈ L, z * l * z⁻¹ = y * l * y⁻¹) (hyL : y ∈ L)
    (hAL : A ≤ L) (hAy : ∀ x ∈ A, x * y = y * x) (hAperf : Group.IsPerfect ↥A)
    (hAmax : ∀ P : Subgroup G, P ≤ L → (∀ x ∈ P, x * y = y * x) → Group.IsPerfect ↥P → P ≤ A) :
    ∀ f ∈ F, ∀ x ∈ A, f * x * f⁻¹ ∈ A := by
  intro f hf x hx
  haveI : Group.IsPerfect ↥A := hAperf
  have hzA : ∀ a ∈ A, z * a * z⁻¹ = a := fun a ha => by
    rw [hzy a (hAL ha), ← hAy a ha, mul_inv_cancel_right]
  have hPL : A.map (MulAut.conj f).toMonoidHom ≤ L := by
    rintro _ ⟨a, ha, rfl⟩
    exact hFL f hf a (hAL ha)
  have hPy : ∀ p ∈ A.map (MulAut.conj f).toMonoidHom, p * y = y * p := by
    rintro _ ⟨a, ha, rfl⟩
    have hpL : f * a * f⁻¹ ∈ L := hFL f hf a (hAL ha)
    have h1 : y * (f * a * f⁻¹) * y⁻¹ = f * a * f⁻¹ := by
      rw [← hzy _ hpL, lad_conj_comm (hzF f hf).symm a, hzA a ha]
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  exact hAmax _ hPL hPy (Group.IsPerfect.map _) ⟨x, hx, rfl⟩

theorem layer_le_mul {G : Type} [Group G] [Finite G] {F L A : Subgroup G} {y z : G}
    (hFL : ∀ f ∈ F, ∀ l ∈ L, f * l * f⁻¹ ∈ L) (hyL : y ∈ L)
    (hzF : ∀ x ∈ F, x * z = z * x) (hzy : ∀ l ∈ L, z * l * z⁻¹ = y * l * y⁻¹)
    (hAL : A ≤ L) (hAy : ∀ x ∈ A, x * y = y * x) (hAF : A ≤ F)
    (hAmax : ∀ P : Subgroup G, P ≤ L → (∀ x ∈ P, x * y = y * x) → Group.IsPerfect ↥P → P ≤ A)
    (hOut : ∀ P : Subgroup (MulAut ↥L), Group.IsPerfect ↥P →
      P ≤ (MulAut.conj : ↥L →* MulAut ↥L).range) :
    ∀ x ∈ ComponentClassification.Layer.subgroup ↥F,
      ∃ r ∈ A, ∃ d ∈ F, (∀ l ∈ L, d * l = l * d) ∧ (x : G) = r * d := by
  have hFN : F ≤ Subgroup.normalizer (L : Set G) := fun f hf =>
    Subgroup.mem_normalizer_fintype fun n hn => hFL f hf n hn
  let act : ↥F →* MulAut ↥L := (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hFN)
  have hact : ∀ (f : ↥F) (l : ↥L), ((act f l : ↥L) : G) = (f : G) * l * (f : G)⁻¹ :=
    fun f l => rfl
  haveI : Group.IsPerfect ↥(ComponentClassification.Layer.subgroup ↥F) :=
    ComponentClassification.Layer.perfect ↥F
  haveI hPperf : Group.IsPerfect ↥((ComponentClassification.Layer.subgroup ↥F).map act) :=
    Group.IsPerfect.map act
  obtain ⟨S, hSperf, hSmap⟩ := lad_exists_perfect_lift _ (hOut _ hPperf)
  haveI := hSperf
  let y' : ↥L := ⟨y, hyL⟩
  have hcomm : ∀ x : ↥F, ∀ m : ↥L, act x (y' * m * y'⁻¹) = y' * act x m * y'⁻¹ := by
    intro x m
    apply Subtype.ext
    have h1 : ((x : G) * m * (x : G)⁻¹) ∈ L := hFL x x.2 m m.2
    have h2 := lad_conj_comm (hzF x x.2) (m : G)
    rw [hzy m m.2, hzy _ h1] at h2
    simpa [hact, y', mul_assoc] using h2
  have hSz : ∀ l ∈ S, ⁅l, y'⁆ ∈ Subgroup.center ↥L := by
    intro l hl
    have hlP : (MulAut.conj : ↥L →* MulAut ↥L) l ∈
        (ComponentClassification.Layer.subgroup ↥F).map act := by
      rw [← hSmap]; exact Subgroup.mem_map_of_mem _ hl
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.mp hlP
    have hx' : ∀ m : ↥L, act x m = l * m * l⁻¹ := fun m => by rw [hx]; rfl
    have : ⁅l, y'⁆ = (l * y') * (y' * l)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [this]
    refine lad_mem_center_of_conj_eq fun t => ?_
    have h3 := hcomm x t
    rw [hx', hx'] at h3
    calc l * y' * t * (l * y')⁻¹ = l * (y' * t * y'⁻¹) * l⁻¹ := by group
      _ = y' * (l * t * l⁻¹) * y'⁻¹ := h3
      _ = y' * l * t * (y' * l)⁻¹ := by group
  have hScomm := lad_perfect_comm S y' hSz
  have hSA : S.map L.subtype ≤ A := by
    refine hAmax _ (Subgroup.map_subtype_le S) ?_ (Group.IsPerfect.map _)
    rintro _ ⟨l, hl, rfl⟩
    exact congrArg Subtype.val (hScomm l hl)
  intro x hx
  have hxP : act x ∈ S.map (MulAut.conj : ↥L →* MulAut ↥L) := by
    rw [hSmap]; exact Subgroup.mem_map_of_mem _ hx
  obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp hxP
  have hrA : (l : G) ∈ A := hSA ⟨l, hl, rfl⟩
  refine ⟨(l : G), hrA, (l : G)⁻¹ * (x : G), F.mul_mem (F.inv_mem (hAF hrA)) x.2, ?_, ?_⟩
  · intro l' hl'
    have h4 := congrArg (fun φ : MulAut ↥L => ((φ ⟨l', hl'⟩ : ↥L) : G)) hlx
    simp only [MulAut.conj_apply, hact] at h4
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
    calc (l : G)⁻¹ * (x : G) * l' = (l : G)⁻¹ * ((x : G) * l' * (x : G)⁻¹) * (x : G) := by group
      _ = (l : G)⁻¹ * ((l : G) * l' * (l : G)⁻¹) * (x : G) := by rw [h4]
      _ = l' * ((l : G)⁻¹ * (x : G)) := by group
  · group

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc
