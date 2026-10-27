module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25Comp

public section

namespace CFSG.ComponentClassification.GrSLit.Sol25

open CFSG Subgroup CFSG.LocalCores CFSG.LocalAnalysis.ComponentInitial
open scoped Function commutatorElement

theorem noncommProd_image {α γ β : Type*} [Monoid β] [DecidableEq γ] {s : Finset α}
    {σ : α → γ} (hσ : Set.InjOn σ s) (F : γ → β)
    (comm : ((s.image σ : Finset γ) : Set γ).Pairwise (Commute on F))
    (comm' : (s : Set α).Pairwise (Commute on (F ∘ σ))) :
    (s.image σ).noncommProd F comm = s.noncommProd (F ∘ σ) comm' := by
  unfold Finset.noncommProd
  have h : (s.image σ).1.map F = s.1.map (F ∘ σ) := by
    rw [Finset.image_val_of_injOn hσ, Multiset.map_map]
  congr 1

variable {H : Type*} [Group H] [Finite H]

@[expose] noncomputable def orbitRep (A K L : Subgroup H) : H :=
  open Classical in if h : ∃ a ∈ A, conjSub a K = L then h.choose else 1

omit [Finite H] in
theorem orbitRep_mem {A K L : Subgroup H} : orbitRep A K L ∈ A := by
  unfold orbitRep
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_mem A

omit [Finite H] in
theorem conjSub_orbitRep {A K L : Subgroup H} (h : ∃ a ∈ A, conjSub a K = L) :
    conjSub (orbitRep A K L) K = L := by
  unfold orbitRep
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.2

omit [Finite H] in
theorem conj_eq_of_conjSub_eq {A K : Subgroup H}
    (hN : ∀ a ∈ A, a ∈ normalizer (K : Set H) → a ∈ centralizer (K : Set H)) {a b : H}
    (ha : a ∈ A) (hb : b ∈ A) (hab : conjSub a K = conjSub b K) {k : H} (hk : k ∈ K) :
    a * k * a⁻¹ = b * k * b⁻¹ := by
  have h1 : conjSub (b⁻¹ * a) K = K := by
    rw [conjSub_mul, hab, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hc := mem_centralizer_iff.mp (hN _ (mul_mem (inv_mem hb) ha)
    (mem_normalizer_of_conjSub_eq h1)) k hk
  calc a * k * a⁻¹ = b * ((b⁻¹ * a) * k) * (b⁻¹ * a)⁻¹ * b⁻¹ := by group
    _ = b * (k * (b⁻¹ * a)) * (b⁻¹ * a)⁻¹ * b⁻¹ := by rw [hc]
    _ = b * k * b⁻¹ := by group

@[expose] noncomputable def orbitFinset (A K : Subgroup H) : Finset (Subgroup H) :=
  open Classical in (Set.toFinite (A : Set H)).toFinset.image fun a => conjSub a K

theorem mem_orbitFinset {A K L : Subgroup H} :
    L ∈ orbitFinset A K ↔ ∃ a ∈ A, conjSub a K = L := by
  classical
  unfold orbitFinset
  simp

@[expose] noncomputable def factor (A K : Subgroup H) (k : H) (L : Subgroup H) : H :=
  orbitRep A K L * k * (orbitRep A K L)⁻¹

theorem factor_mem {A K L : Subgroup H} (hL : L ∈ orbitFinset A K) {k : H} (hk : k ∈ K) :
    factor A K k L ∈ L := by
  have h1 := conjSub_orbitRep (mem_orbitFinset.mp hL)
  have h2 : factor A K k L ∈ conjSub (orbitRep A K L) K := ⟨k, hk, rfl⟩
  rwa [h1] at h2

theorem isComponent_of_mem_orbitFinset {A K L : Subgroup H} (hK : IsComponent K)
    (hL : L ∈ orbitFinset A K) : IsComponent L := by
  rw [← conjSub_orbitRep (mem_orbitFinset.mp hL)]
  exact isComponent_map_of_isComponent _ hK

theorem factor_commute {A K : Subgroup H} (hK : IsComponent K) {k k' : H} (hk : k ∈ K)
    (hk' : k' ∈ K) {L₁ L₂ : Subgroup H} (hL₁ : L₁ ∈ orbitFinset A K) (hL₂ : L₂ ∈ orbitFinset A K)
    (hne : L₁ ≠ L₂) : Commute (factor A K k L₁) (factor A K k' L₂) := by
  rcases distinct_components_commute (isComponent_of_mem_orbitFinset hK hL₁)
    (isComponent_of_mem_orbitFinset hK hL₂) with h | h
  · exact absurd h hne
  · exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h
      (factor_mem hL₁ hk)) _ (factor_mem hL₂ hk')).symm

@[expose] noncomputable def diagFun {A K : Subgroup H} (hK : IsComponent K) (k : K) : H :=
  (orbitFinset A K).noncommProd (factor A K k)
    (fun _ hL₁ _ hL₂ hne => factor_commute hK k.2 k.2 hL₁ hL₂ hne)

@[expose] noncomputable def diag {A K : Subgroup H} (hK : IsComponent K) : K →* H where
  toFun := diagFun (A := A) hK
  map_one' := by
    refine (Finset.noncommProd_eq_pow_card _ _ _ 1 (fun L _ => ?_)).trans (one_pow _)
    simp [factor]
  map_mul' k₁ k₂ := by
    have hc : ((orbitFinset A K : Finset (Subgroup H)) : Set (Subgroup H)).Pairwise
        (Commute on (factor A K k₁ * factor A K k₂)) := by
      intro L₁ hL₁ L₂ hL₂ hne
      simp only [Function.onFun, Pi.mul_apply]
      exact ((factor_commute hK k₁.2 k₁.2 hL₁ hL₂ hne).mul_right
        (factor_commute hK k₁.2 k₂.2 hL₁ hL₂ hne)).mul_left
        ((factor_commute hK k₂.2 k₁.2 hL₁ hL₂ hne).mul_right
        (factor_commute hK k₂.2 k₂.2 hL₁ hL₂ hne))
    have e1 : diagFun (A := A) hK (k₁ * k₂) =
        (orbitFinset A K).noncommProd (factor A K k₁ * factor A K k₂) hc :=
      Finset.noncommProd_congr rfl (fun L _ => by
        simp only [Pi.mul_apply, factor, Subgroup.coe_mul]; group) _
    rw [e1]
    exact Finset.noncommProd_mul_distrib (factor A K k₁) (factor A K k₂) _ _
      (fun _ hL₁ _ hL₂ hne => factor_commute hK k₂.2 k₁.2 hL₁ hL₂ hne)

theorem diag_apply {A K : Subgroup H} (hK : IsComponent K) (k : K) :
    diag (A := A) hK k = diagFun (A := A) hK k := rfl

theorem mem_orbitFinset_self {A K : Subgroup H} : K ∈ orbitFinset A K :=
  mem_orbitFinset.mpr ⟨1, one_mem A, conjSub_one K⟩

omit [Finite H] in
theorem conjSub_injective (g : H) : Function.Injective (conjSub g) := fun L₁ L₂ h => by
  rw [← conjSub_inv_conjSub g L₁, h, conjSub_inv_conjSub]

open Classical in
theorem image_conjSub_orbitFinset {A K : Subgroup H} {b : H} (hb : b ∈ A) :
    (orbitFinset A K).image (conjSub b) = orbitFinset A K := by
  classical
  ext L
  rw [Finset.mem_image, mem_orbitFinset]
  constructor
  · rintro ⟨L', hL', rfl⟩
    obtain ⟨a, ha, rfl⟩ := mem_orbitFinset.mp hL'
    exact ⟨b * a, mul_mem hb ha, conjSub_mul b a K⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨conjSub (b⁻¹ * a) K, mem_orbitFinset.mpr ⟨b⁻¹ * a, mul_mem (inv_mem hb) ha, rfl⟩, ?_⟩
    rw [← conjSub_mul, mul_inv_cancel_left]

theorem factor_pairwise {A K : Subgroup H} (hK : IsComponent K) (k : K) :
    ((orbitFinset A K : Finset (Subgroup H)) : Set (Subgroup H)).Pairwise
      (Commute on factor A K k) := fun _ hL₁ _ hL₂ hne => factor_commute hK k.2 k.2 hL₁ hL₂ hne

theorem conj_factor_pairwise {A K : Subgroup H} (hK : IsComponent K) (k : K) (g : H) :
    ((orbitFinset A K : Finset (Subgroup H)) : Set (Subgroup H)).Pairwise
      (Commute on fun L => (MulAut.conj g) (factor A K k L)) :=
  fun _ hL₁ _ hL₂ hne => (factor_commute hK k.2 k.2 hL₁ hL₂ hne).map (MulAut.conj g)

theorem diag_mem_centralizer {A K : Subgroup H} (hK : IsComponent K)
    (hN : ∀ a ∈ A, a ∈ normalizer (K : Set H) → a ∈ centralizer (K : Set H)) (k : K) :
    diag (A := A) hK k ∈ centralizer (A : Set H) := by
  classical
  rw [mem_centralizer_iff]
  intro b hb
  suffices h : (MulAut.conj b) (diag (A := A) hK k) = diag (A := A) hK k by
    rw [MulAut.conj_apply] at h
    calc b * diag (A := A) hK k = b * diag (A := A) hK k * b⁻¹ * b := by group
      _ = diag (A := A) hK k * b := by rw [h]
  have hO : ∀ L ∈ orbitFinset A K, conjSub b L ∈ orbitFinset A K := fun L hL => by
    rw [← image_conjSub_orbitFinset hb]; exact Finset.mem_image_of_mem _ hL
  have hconj : ∀ L ∈ orbitFinset A K, (MulAut.conj b) (factor A K k L) =
      factor A K k (conjSub b L) := by
    intro L hL
    have h1 := conjSub_orbitRep (mem_orbitFinset.mp hL)
    have h2 := conjSub_orbitRep (mem_orbitFinset.mp (hO L hL))
    have h3 := conj_eq_of_conjSub_eq hN (mul_mem hb (orbitRep_mem (L := L)))
      (orbitRep_mem (L := conjSub b L)) (by rw [conjSub_mul, h1, h2]) k.2
    simp only [factor, MulAut.conj_apply]
    rw [← h3]
    group
  have hc1 : ((orbitFinset A K : Finset (Subgroup H)) : Set (Subgroup H)).Pairwise
      (Commute on (factor A K k ∘ conjSub b)) := fun L₁ hL₁ L₂ hL₂ hne =>
    factor_commute hK k.2 k.2 (hO L₁ hL₁) (hO L₂ hL₂) fun h => hne (conjSub_injective b h)
  have hc2 : (((orbitFinset A K).image (conjSub b) : Finset (Subgroup H)) :
      Set (Subgroup H)).Pairwise (Commute on factor A K k) := by
    rw [image_conjSub_orbitFinset hb]
    exact factor_pairwise hK k
  have e1 : (MulAut.conj b) (diag (A := A) hK k) = (orbitFinset A K).noncommProd
      (fun L => (MulAut.conj b) (factor A K k L)) (conj_factor_pairwise hK k b) :=
    Finset.map_noncommProd _ _ (factor_pairwise hK k) (MulAut.conj b)
  have e2 : (orbitFinset A K).noncommProd (fun L => (MulAut.conj b) (factor A K k L))
      (conj_factor_pairwise hK k b) =
        (orbitFinset A K).noncommProd (factor A K k ∘ conjSub b) hc1 :=
    Finset.noncommProd_congr rfl (fun L hL => by rw [Function.comp_apply, hconj L hL]) _
  have e3 : ((orbitFinset A K).image (conjSub b)).noncommProd (factor A K k) hc2 =
      (orbitFinset A K).noncommProd (factor A K k ∘ conjSub b) hc1 :=
    noncommProd_image (fun L₁ _ L₂ _ h => conjSub_injective b h) _ hc2 hc1
  have e4 : ((orbitFinset A K).image (conjSub b)).noncommProd (factor A K k) hc2 =
      diag (A := A) hK k :=
    Finset.noncommProd_congr (image_conjSub_orbitFinset hb) (fun _ _ => rfl) _
  rw [e1, e2, ← e3, e4]

theorem exists_diag_eq_mul {A K : Subgroup H} (hK : IsComponent K)
    (hN : ∀ a ∈ A, a ∈ normalizer (K : Set H) → a ∈ centralizer (K : Set H)) (k : K) :
    ∃ c ∈ centralizer (K : Set H), diag (A := A) hK k = k * c := by
  classical
  have hKO : K ∈ orbitFinset A K := mem_orbitFinset_self
  have hfK : factor A K k K = k := by
    have h1 := conjSub_orbitRep (mem_orbitFinset.mp hKO)
    have hc := mem_centralizer_iff.mp (hN _ orbitRep_mem (mem_normalizer_of_conjSub_eq h1)) k k.2
    simp only [factor]
    rw [← hc, mul_inv_cancel_right]
  have hce : ((((orbitFinset A K).erase K : Finset (Subgroup H)) : Set (Subgroup H))).Pairwise
      (Commute on factor A K k) :=
    (factor_pairwise hK k).mono (Finset.coe_subset.mpr (Finset.erase_subset K _))
  refine ⟨((orbitFinset A K).erase K).noncommProd (factor A K k) hce, ?_, ?_⟩
  · refine Subgroup.noncommProd_mem _ _ fun L hL => ?_
    obtain ⟨hLK, hLO⟩ := Finset.mem_erase.mp hL
    rcases distinct_components_commute (isComponent_of_mem_orbitFinset hK hLO) hK with h | h
    · exact absurd h hLK
    · exact commutator_eq_bot_iff_le_centralizer.mp h (factor_mem hLO k.2)
  · rw [diag_apply, diagFun, ← Finset.mul_noncommProd_erase _ hKO _ (factor_pairwise hK k) hce,
      hfK]

theorem conj_diag {A K : Subgroup H} (hK : IsComponent K) {y : H}
    (hyA : ∀ a ∈ A, y * a = a * y) (k : K) (hk : y * (k : H) * y⁻¹ ∈ K) :
    y * diag (A := A) hK k * y⁻¹ = diag (A := A) hK ⟨_, hk⟩ := by
  have e1 : (MulAut.conj y) (diag (A := A) hK k) = (orbitFinset A K).noncommProd
      (fun L => (MulAut.conj y) (factor A K k L)) (conj_factor_pairwise hK k y) :=
    Finset.map_noncommProd _ _ (factor_pairwise hK k) (MulAut.conj y)
  rw [← MulAut.conj_apply, e1]
  refine Finset.noncommProd_congr rfl (fun L _ => ?_) _
  have hc := hyA _ (orbitRep_mem (A := A) (K := K) (L := L))
  simp only [MulAut.conj_apply, factor]
  calc y * (orbitRep A K L * ↑k * (orbitRep A K L)⁻¹) * y⁻¹
      = (y * orbitRep A K L) * ↑k * (y * orbitRep A K L)⁻¹ * y * y⁻¹ := by group
    _ = (orbitRep A K L * y) * ↑k * (orbitRep A K L * y)⁻¹ * y * y⁻¹ := by rw [hc]
    _ = orbitRep A K L * (y * ↑k * y⁻¹) * (orbitRep A K L)⁻¹ := by group

theorem le_centralizer_of_stabilizer_le {A Y K : Subgroup H} (hK : IsComponent K)
    (hY : Odd (Nat.card Y)) (hYA : ∀ y ∈ Y, ∀ a ∈ A, y * a = a * y)
    (hNY : centralizer (A : Set H) ≤ normalizer (Y : Set H))
    (hYK : Y ≤ normalizer (K : Set H))
    (hN : ∀ a ∈ A, a ∈ normalizer (K : Set H) → a ∈ centralizer (K : Set H)) :
    Y ≤ centralizer (K : Set H) := by
  classical
  set V : Subgroup K := Y.comap (diag (A := A) hK) with hV
  have hVn : V.Normal := by
    refine ⟨fun v hv k => ?_⟩
    rw [hV, mem_comap] at hv ⊢
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hNY (diag_mem_centralizer hK hN k)) _).mp hv
  have hkyK : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ ∈ K := fun y hy k hk =>
    (mem_normalizer_iff.mp (hYK hy) k).mp hk
  have hcomm : ∀ (y : H) (hy : y ∈ Y) (k : K),
      k * ⟨y * (k⁻¹ : K) * y⁻¹, hkyK y hy _ (k⁻¹).2⟩ ∈ V := by
    intro y hy k
    rw [hV, mem_comap, map_mul, ← conj_diag hK (fun a ha => hYA y hy a ha) k⁻¹, map_inv]
    have h := (mem_normalizer_iff.mp (hNY (diag_mem_centralizer hK hN k)) y).mp hy
    rw [show diag (A := A) hK k * (y * (diag (A := A) hK k)⁻¹ * y⁻¹) =
      diag (A := A) hK k * y * (diag (A := A) hK k)⁻¹ * y⁻¹ by group]
    exact mul_mem h (inv_mem hy)
  rcases LocalCores.quasisimple_normal_subgroups hK.1 hVn with hVtop | hVZ
  · exfalso
    obtain ⟨k₀, hk₀K, hk₀Z, hk₀2⟩ := exists_noncentral_mul_self_mem_center hK.1
    set κ : K := ⟨k₀, hk₀K⟩ with hκ
    have hδ : diag (A := A) hK κ ∈ Y := by
      have h : κ ∈ V := hVtop ▸ mem_top κ
      exact h
    obtain ⟨m, hm⟩ := odd_orderOf_of_mem hY hδ
    set n := orderOf (diag (A := A) hK κ) with hn
    obtain ⟨c, hc, hce⟩ := exists_diag_eq_mul hK hN (κ ^ n)
    have h1 : diag (A := A) hK (κ ^ n) = 1 := by rw [map_pow, hn, pow_orderOf_eq_one]
    rw [h1] at hce
    have hkn : k₀ ^ n ∈ (center K).map K.subtype := by
      have hkn' : ((κ ^ n : K) : H) = c⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← hce]
      refine LocalAnalysis.ComponentInitial.mem_map_center_iff.mpr ⟨pow_mem hk₀K n,
        fun e he => ?_⟩
      have h2 : ((κ ^ n : K) : H) = k₀ ^ n := by rw [Subgroup.coe_pow]
      rw [← h2, hkn']
      exact ((mem_centralizer_iff.mp (inv_mem hc)) e he)
    have hk2m : k₀ ^ (n + 1) ∈ (center K).map K.subtype := by
      rw [show n + 1 = 2 * (m + 1) by omega, pow_mul, pow_two]
      exact pow_mem hk₀2 _
    apply hk₀Z
    have e : k₀ = k₀ ^ (n + 1) * (k₀ ^ n)⁻¹ := by rw [pow_succ]; group
    rw [e]
    exact mul_mem hk2m (inv_mem hkn)
  · have h1 : ⁅K, Y⁆ ≤ (center K).map K.subtype := by
      rw [commutator_le]
      intro k hk y hy
      have h := hVZ (hcomm y hy ⟨k, hk⟩)
      have e : ⁅k, y⁆ = ((⟨k, hk⟩ * ⟨y * ((⟨k, hk⟩ : K)⁻¹ : K) * y⁻¹,
          hkyK y hy _ ((⟨k, hk⟩ : K)⁻¹).2⟩ : K) : H) := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact mem_map_of_mem _ h
    have h2 : ⁅⁅K, Y⁆, K⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [mem_centralizer_iff]
      intro k hk
      exact (LocalAnalysis.ComponentInitial.mem_map_center_iff.mp (h1 hx)).2 k hk
    have h3 := perfect_double_commutator hK.1.1 h2
    rw [le_centralizer_iff]
    exact commutator_eq_bot_iff_le_centralizer.mp h3

end CFSG.ComponentClassification.GrSLit.Sol25
