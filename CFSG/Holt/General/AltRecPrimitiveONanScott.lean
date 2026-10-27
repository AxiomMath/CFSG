module

public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Holt.General.AltRecPrim

open MulAction

variable {G : Type*} [Group G]

structure SimpleFactors (N : Subgroup G) where
  r : ℕ
  S : Fin r → Subgroup G
  one_le : 1 ≤ r
  le : ∀ i, S i ≤ N
  isSimpleGroup : ∀ i, IsSimpleGroup (S i)
  not_commute : ∀ i, ∃ a ∈ S i, ∃ b ∈ S i, a * b ≠ b * a
  normal : ∀ i, ((S i).subgroupOf N).Normal
  conj : ∀ i j, ∃ g : G, S j = (S i).map (MulAut.conj g).toMonoidHom
  e : ((i : Fin r) → S i) ≃* N
  e_single : ∀ (i : Fin r) (x : (j : Fin r) → S j), (∀ j, j ≠ i → x j = 1) → (e x : G) = x i

namespace SimpleFactors

variable {N : Subgroup G} (F : SimpleFactors N)

@[expose] noncomputable def proj (i : Fin F.r) : N →* F.S i :=
  (Pi.evalMonoidHom (fun j => F.S j) i).comp F.e.symm.toMonoidHom

theorem proj_apply (i : Fin F.r) (m : N) : F.proj i m = F.e.symm m i := rfl

theorem e_mulSingle (i : Fin F.r) (t : F.S i) : (F.e (Pi.mulSingle i t) : G) = t := by
  rw [F.e_single i _ fun _ hj => by rw [Pi.mulSingle_eq_of_ne hj], Pi.mulSingle_eq_same]

theorem e_symm_of_mem {i : Fin F.r} {t : G} (ht : t ∈ F.S i) :
    F.e.symm ⟨t, F.le i ht⟩ = Pi.mulSingle i ⟨t, ht⟩ := by
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (F.e_mulSingle i ⟨t, ht⟩).symm

theorem proj_of_mem {i : Fin F.r} {t : G} (ht : t ∈ F.S i) :
    (F.proj i ⟨t, F.le i ht⟩ : G) = t := by
  rw [proj_apply, F.e_symm_of_mem ht, Pi.mulSingle_eq_same]

theorem proj_of_mem_of_ne {i j : Fin F.r} (hij : j ≠ i) {t : G} (ht : t ∈ F.S i) :
    F.proj j ⟨t, F.le i ht⟩ = 1 := by
  rw [proj_apply, F.e_symm_of_mem ht, Pi.mulSingle_eq_of_ne hij]

theorem conj_eq (m : N) {i : Fin F.r} {t : G} (ht : t ∈ F.S i) :
    (m : G) * t * (m : G)⁻¹ = (F.proj i m : G) * t * (F.proj i m : G)⁻¹ := by
  obtain ⟨y, rfl⟩ := F.e.surjective m
  have key : y * Pi.mulSingle i ⟨t, ht⟩ * y⁻¹ = Pi.mulSingle i (y i * ⟨t, ht⟩ * (y i)⁻¹) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  have h1 : ((F.e y : N) : G) * t * ((F.e y : N) : G)⁻¹ =
      (F.e (Pi.mulSingle i (y i * ⟨t, ht⟩ * (y i)⁻¹)) : G) := by
    rw [← key, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      F.e_mulSingle]
  rw [h1, F.e_mulSingle, proj_apply, MulEquiv.symm_apply_apply]
  simp

theorem commute_of_ne {i j : Fin F.r} (hij : i ≠ j) {a b : G} (ha : a ∈ F.S i)
    (hb : b ∈ F.S j) : Commute a b := by
  have h := F.conj_eq ⟨b, F.le j hb⟩ ha
  rw [F.proj_of_mem_of_ne hij hb] at h
  simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h
  show a * b = b * a
  calc a * b = (b * a * b⁻¹) * b := by rw [h]
    _ = b * a := by group

theorem eq_one_of_forall_proj_eq_one {m : N} (h : ∀ i, F.proj i m = 1) : m = 1 := by
  have h1 : F.e.symm m = 1 := funext h
  rw [MulEquiv.symm_apply_eq, map_one] at h1
  exact h1

theorem conj_mem (m : N) {i : Fin F.r} {t : G} (ht : t ∈ F.S i) :
    (m : G) * t * (m : G)⁻¹ ∈ F.S i := by
  rw [F.conj_eq m ht]
  exact mul_mem (mul_mem (F.proj i m).2 ht) (inv_mem (F.proj i m).2)

theorem eq_one_of_forall_commute {i : Fin F.r} {u : G} (hu : u ∈ F.S i)
    (h : ∀ t ∈ F.S i, Commute u t) : u = 1 := by
  have := F.isSimpleGroup i
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (F.S i)) with hc | hc
  · have hmem : (⟨u, hu⟩ : F.S i) ∈ Subgroup.center (F.S i) :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (h g g.2).eq.symm
    rw [hc] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := F.not_commute i
    have hmem : (⟨b, hb⟩ : F.S i) ∈ Subgroup.center (F.S i) := hc ▸ Subgroup.mem_top _
    exact hab (congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨a, ha⟩))

theorem proj_eq_one_of_commute {i : Fin F.r} (m : N) (h : ∀ t ∈ F.S i, Commute (m : G) t) :
    F.proj i m = 1 := by
  apply Subtype.ext
  apply F.eq_one_of_forall_commute (F.proj i m).2
  intro t ht
  have h1 := F.conj_eq m ht
  have h2 : (m : G) * t * (m : G)⁻¹ = t := by rw [(h t ht).eq]; group
  rw [h2] at h1
  show _ = _
  calc (F.proj i m : G) * t
      = ((F.proj i m : G) * t * (F.proj i m : G)⁻¹) * (F.proj i m : G) := by group
    _ = t * (F.proj i m) := by rw [← h1]

theorem commute_of_proj_eq_one {i : Fin F.r} {m : N} (h : F.proj i m = 1) {t : G}
    (ht : t ∈ F.S i) : Commute (m : G) t := by
  have h1 := F.conj_eq m ht
  rw [h] at h1
  simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h1
  show _ = _
  calc (m : G) * t = ((m : G) * t * (m : G)⁻¹) * m := by group
    _ = t * m := by rw [h1]

theorem eq_one_of_forall_commute_factors {m : N} (h : ∀ i, ∀ t ∈ F.S i, Commute (m : G) t) :
    m = 1 :=
  F.eq_one_of_forall_proj_eq_one fun i => F.proj_eq_one_of_commute m (h i)

theorem le_of_inf_ne_bot {A : Subgroup G} (hA : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A)
    {i : Fin F.r} (h : A ⊓ F.S i ≠ ⊥) : F.S i ≤ A := by
  have := F.isSimpleGroup i
  have hn : ((A ⊓ F.S i).subgroupOf (F.S i)).Normal := ⟨fun x hx t => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_inf.mpr
      ⟨hA t (F.le i t.2) x hx.1, mul_mem (mul_mem t.2 hx.2) (inv_mem t.2)⟩⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top ((A ⊓ F.S i).subgroupOf (F.S i)) with hb | ht
  · have h' := disjoint_iff.mp ((Subgroup.subgroupOf_eq_bot).mp hb)
    rw [inf_assoc, inf_idem] at h'
    exact absurd h' h
  · intro t htS
    have : (⟨t, htS⟩ : F.S i) ∈ (A ⊓ F.S i).subgroupOf (F.S i) := ht ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1

theorem exists_map_conj_eq (hN : N.Normal) (g : G) (i : Fin F.r) :
    ∃ j, (F.S i).map (MulAut.conj g).toMonoidHom = F.S j := by
  set T := (F.S i).map (MulAut.conj g).toMonoidHom with hT
  have hTN : ∀ n ∈ N, ∀ a ∈ T, n * a * n⁻¹ ∈ T := by
    rintro n hn _ ⟨s, hs, rfl⟩
    have hn' : g⁻¹ * n * g ∈ N := by simpa using hN.conj_mem n hn g⁻¹
    refine ⟨(g⁻¹ * n * g) * s * (g⁻¹ * n * g)⁻¹, F.conj_mem ⟨_, hn'⟩ hs, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hTle : T ≤ N := by
    rintro _ ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply] using hN.conj_mem s (F.le i hs) g
  have hTs : IsSimpleGroup T := by
    have := F.isSimpleGroup i
    exact (Subgroup.equivMapOfInjective (F.S i) _ (MulAut.conj g).injective).symm.isSimpleGroup
  by_contra hne'
  have hne : ∀ j, T ≠ F.S j := fun j h => hne' ⟨j, h⟩
  have hdisj : ∀ j, T ⊓ F.S j = ⊥ := by
    intro j
    by_contra hj
    apply hne j
    have h1 : F.S j ≤ T := F.le_of_inf_ne_bot hTN hj
    have hn : ((F.S j).subgroupOf T).Normal := ⟨fun x hx t => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact F.conj_mem ⟨t, hTle t.2⟩ hx⟩
    rcases Subgroup.Normal.eq_bot_or_eq_top ((F.S j).subgroupOf T) with hb | ht
    · exfalso
      have hSj : F.S j = ⊥ := disjoint_self.mp (((Subgroup.subgroupOf_eq_bot).mp hb).mono_right h1)
      have := F.isSimpleGroup j
      exact (Subgroup.nontrivial_iff_ne_bot (F.S j)).mp inferInstance hSj
    · refine le_antisymm (fun t htT => ?_) h1
      have : (⟨t, htT⟩ : T) ∈ (F.S j).subgroupOf T := ht ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  have hTbot : T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 := F.eq_one_of_forall_commute_factors (m := ⟨x, hTle hx⟩) fun j t ht => by
      have hc : x * t * x⁻¹ * t⁻¹ ∈ T ⊓ F.S j := by
        refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (F.conj_mem ⟨x, hTle hx⟩ ht) (inv_mem ht)⟩
        have e : x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
        rw [e]
        exact mul_mem hx (hTN t (F.le j ht) _ (inv_mem hx))
      rw [hdisj j, Subgroup.mem_bot] at hc
      show x * t = t * x
      calc x * t = (x * t * x⁻¹ * t⁻¹) * (t * x) := by group
        _ = t * x := by rw [hc, one_mul]
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  exact (Subgroup.nontrivial_iff_ne_bot T).mp inferInstance hTbot

theorem proj_conj {g : G} {i j : Fin F.r}
    (hij : (F.S i).map (MulAut.conj g).toMonoidHom = F.S j) (m : N) (hm : g * m * g⁻¹ ∈ N) :
    (F.proj j ⟨g * m * g⁻¹, hm⟩ : G) = g * F.proj i m * g⁻¹ := by
  have hy : g * (F.proj i m : G) * g⁻¹ ∈ F.S j := hij ▸ ⟨_, (F.proj i m).2, rfl⟩
  have hpi : F.proj i ⟨F.proj i m, F.le i (F.proj i m).2⟩ = F.proj i m :=
    Subtype.ext (F.proj_of_mem (F.proj i m).2)
  have hc : F.proj i (m * ⟨F.proj i m, F.le i (F.proj i m).2⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, hpi, mul_inv_cancel]
  have hc' : F.proj j (⟨g * m * g⁻¹, hm⟩ * ⟨g * F.proj i m * g⁻¹, F.le j hy⟩⁻¹) = 1 := by
    apply F.proj_eq_one_of_commute
    intro t ht
    rw [← hij] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have h1 := (Commute.conj_iff g).mpr (F.commute_of_proj_eq_one hc hs)
    convert h1 using 1
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [map_mul, map_inv, mul_inv_eq_one] at hc'
  rw [hc']
  exact F.proj_of_mem hy

end SimpleFactors

theorem nonempty_simpleFactors [Finite G] {N : Subgroup G} (hN : N.Normal) (hN1 : N ≠ ⊥)
    (hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N)
    (hab : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a) : Nonempty (SimpleFactors N) := by
  obtain ⟨r, S, hr, hle, hsimple, hconj, hnorm, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hN hN1 hmin
  have hconj' : ∀ i j, ∃ g : G, S j = (S i).map (MulAut.conj g).toMonoidHom := by
    intro i j
    obtain ⟨g, hg⟩ := hconj i j
    exact ⟨g⁻¹, hg⟩
  have hnc : ∀ i, ∃ a ∈ S i, ∃ b ∈ S i, a * b ≠ b * a := by
    intro i
    by_contra hi
    simp only [not_exists, not_and, not_not] at hi
    have hall : ∀ j, ∀ a ∈ S j, ∀ b ∈ S j, a * b = b * a := by
      intro j a ha b hb
      obtain ⟨g, hg⟩ := hconj' i j
      rw [hg] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      rw [← map_mul, ← map_mul, hi a' ha' b' hb']
    obtain ⟨a, ha, b, hb, hab'⟩ := hab
    apply hab'
    obtain ⟨x, hx⟩ := e.surjective ⟨a, ha⟩
    obtain ⟨y, hy⟩ := e.surjective ⟨b, hb⟩
    have hxy : x * y = y * x := funext fun j => Subtype.ext (hall j _ (x j).2 _ (y j).2)
    have h1 := congrArg (fun w => ((e w : N) : G)) hxy
    simpa [map_mul, hx, hy] using h1
  exact ⟨⟨r, S, hr, hle, hsimple, hnc, hnorm, hconj', e, he⟩⟩

end CFSG.Holt.General.AltRecPrim
