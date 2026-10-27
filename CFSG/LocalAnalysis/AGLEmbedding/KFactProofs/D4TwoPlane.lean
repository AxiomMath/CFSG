module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoSylow
public import Certificates.Certificate29700
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Quasithin CFSG.Open

namespace CFSG.AGLEmbedding.D4Two

theorem plane_check : d4PlaneCheck = true :=
  Certificates.certificate29700

theorem plane_check_spec (h : d4PlaneCheck = true) :
    planeCoverCheck d4PlaneCerts sylowElems = true ∧
      ∀ c ∈ d4PlaneCerts, c.poolOK = true ∧ c.targetOK = true := by
  simpa only [d4PlaneCheck, Bool.and_eq_true, List.all_eq_true] using h

theorem sylowElemAt_mem (i : ℕ) : sylowElemAt i ∈ sylowElems := by
  unfold sylowElemAt
  by_cases hi : i < sylowElems.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · rw [List.getD_eq_default _ _ (by omega)]
    exact oneArr_mem_bfsElems _ _ _

theorem exists_elem_of_mem_sylowElems {x : Array GF8} (hx : x ∈ sylowElems) :
    ∃ g : trialityGroup8, ((g : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat x := by
  obtain ⟨g, hg, hgx⟩ := exists_mem_of_mem_sylowElems x hx
  exact ⟨⟨g, sylowGroup_le hg⟩, hgx⟩

theorem ne_one_of_ne_oneArr {y : Array GF8} (hy : y ∈ sylowElems) {g : GL (Fin 8) GF8}
    (hg : (g : Matrix (Fin 8) (Fin 8) GF8) = toMat y) (hne : y ≠ oneArr) : g ≠ 1 := by
  rintro rfl
  apply hne
  apply eq_of_toMat_eq (size_sylowElems y hy) size_oneArr
  rw [← hg, oneArr, toMat_ofMat]
  rfl

theorem mul_comm_of_commutes {a b : Array GF8} (h : commutes a b = true) {g k : GL (Fin 8) GF8}
    (hg : (g : Matrix (Fin 8) (Fin 8) GF8) = toMat a)
    (hk : (k : Matrix (Fin 8) (Fin 8) GF8) = toMat b) : g * k = k * g := by
  unfold commutes at h
  rw [beq_iff_eq] at h
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hg, hk, ← toMat_mulArr, ← toMat_mulArr, h]

private theorem ofNat'_toNat (a : GF8) : GF8.ofNat' a.toNat = a := by
  obtain ⟨⟨v, hv⟩⟩ := a
  simp [GF8.ofNat', GF8.toNat, Nat.mod_eq_of_lt hv]

private theorem exists_letter_of_mem_gens {M : Matrix (Fin 8) (Fin 8) GF8}
    (hM : M ∈ trialityGens8) : ∃ j < 18, M = letterMat j := by
  rcases hM with ⟨a, s, rfl⟩ | ⟨s, rfl⟩
  · have ha : a.toNat < 8 := a.val.isLt
    cases s
    · refine ⟨8 + a.toNat, by omega, ?_⟩
      have h1 : ¬ (8 + a.toNat < 8) := by omega
      have h2 : 8 + a.toNat < 16 := by omega
      rw [letterMat, if_neg h1, if_pos h2, Nat.add_sub_cancel_left, ofNat'_toNat]
    · refine ⟨a.toNat, by omega, ?_⟩
      rw [letterMat, if_pos ha, ofNat'_toNat]
  · cases s
    · exact ⟨17, by norm_num, by simp [letterMat]⟩
    · exact ⟨16, by norm_num, by simp [letterMat]⟩

private theorem cover_spec (h : planeCoverCheck d4PlaneCerts sylowElems = true) {x y : Array GF8}
    (hx : x ∈ sylowElems) (hy : y ∈ sylowElems) (hx3 : cube1 x = true) (hy3 : cube1 y = true)
    (hxy : commutes x y = true) (hx1 : x ≠ oneArr) (hyx : y ∉ [oneArr, x, mulArr x x]) :
    ∃ c ∈ d4PlaneCerts, ∀ p ∈ c.elems, p ∈ planeSpan x y := by
  unfold planeCoverCheck at h
  simp only [List.all_eq_true, List.mem_filter, Bool.or_eq_true, beq_iff_eq,
    List.contains_iff_mem, Bool.and_eq_true, List.any_eq_true, List.mem_map] at h
  rcases h x ⟨hx, hx3⟩ with h1 | h1
  · exact absurd h1 hx1
  · rcases h1 y ⟨⟨hy, hy3⟩, hxy⟩ with h2 | ⟨E, ⟨c, hc, rfl⟩, ⟨-, -⟩, hall⟩
    · exact absurd h2 hyx
    · exact ⟨c, hc, hall⟩

theorem exists_plane_le
    (E : Subgroup trialityGroup8) (hsyl : ∀ x ∈ E, (x : GL (Fin 8) GF8) ∈ sylowGroup)
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2) :
    ∃ c ∈ d4PlaneCerts, ∀ g : trialityGroup8, ∀ p ∈ c.elems,
      ((g : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat p → g ∈ E := by
  classical
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcube : ∀ x ∈ E, (x : GL (Fin 8) GF8) ^ 3 = 1 := fun x hx => by
    have := congrArg Subtype.val (hE.2 x hx)
    simpa using this
  obtain ⟨x1, hx1E, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    have hne : E ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at hcard
      omega
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩
  obtain ⟨x2, hx2E, hx2⟩ : ∃ x ∈ E, x ∉ Subgroup.zpowers x1 := by
    by_contra hall
    have hle : E ≤ Subgroup.zpowers x1 := fun x hx => by_contra fun hxn => hall ⟨x, hx, hxn⟩
    have h3 : orderOf x1 ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (hcube x1 hx1E))
    have h4 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h4
    have h5 := Nat.le_of_dvd (by norm_num) h3
    omega
  obtain ⟨a1, ha1, hga1⟩ := exists_sylowElems_eq _ (hsyl x1 hx1E)
  obtain ⟨a2, ha2, hga2⟩ := exists_sylowElems_eq _ (hsyl x2 hx2E)
  have hc1 : cube1 a1 = true := cube1_of _ hga1 (hcube x1 hx1E)
  have hc2 : cube1 a2 = true := cube1_of _ hga2 (hcube x2 hx2E)
  have hcm : commutes a1 a2 = true :=
    commutes_of _ _ hga1 hga2 (congrArg Subtype.val (hcomm x1 hx1E x2 hx2E))
  have ha1ne : a1 ≠ oneArr := by
    rintro rfl
    apply hx1
    apply Subtype.ext
    apply Units.ext
    rw [hga1, oneArr, toMat_ofMat]
    rfl
  have ha2ne : a2 ∉ [oneArr, a1, mulArr a1 a1] := by
    intro hmem
    obtain ⟨i, hi⟩ := toMat_mem_pows hga1 a2 hmem
    apply hx2
    have hGL : (x1 : GL (Fin 8) GF8) ^ (i : ℕ) = (x2 : GL (Fin 8) GF8) :=
      Units.ext (by rw [← hi, hga2])
    refine Subgroup.mem_zpowers_iff.mpr ⟨(i : ℕ), ?_⟩
    rw [zpow_natCast]
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hGL)
  obtain ⟨c, hc, hcover⟩ := cover_spec (plane_check_spec plane_check).1 ha1 ha2 hc1 hc2 hcm
    ha1ne ha2ne
  refine ⟨c, hc, fun g p hp hgp => ?_⟩
  have hps := hcover p hp
  simp only [planeSpan, List.mem_flatMap, List.mem_map] at hps
  obtain ⟨u, hu, v, hv, rfl⟩ := hps
  obtain ⟨i, hi⟩ := toMat_mem_pows hga1 u hu
  obtain ⟨j, hj⟩ := toMat_mem_pows hga2 v hv
  have : g = x1 ^ (i : ℕ) * x2 ^ (j : ℕ) := by
    apply Subtype.ext
    apply Units.ext
    rw [hgp, toMat_mulArr, hi, hj]
    simp
  rw [this]
  exact mul_mem (pow_mem hx1E _) (pow_mem hx2E _)

private theorem exists_mem_of_mem_closure {G : Type*} [Group G] {K : Subgroup G} (H : Subgroup K)
    {S : Set G} (hS : ∀ A ∈ S, ∃ hA : A ∈ K, (⟨A, hA⟩ : K) ∈ H) :
    ∀ g ∈ Subgroup.closure S, ∃ hg : g ∈ K, (⟨g, hg⟩ : K) ∈ H := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem A hA => exact hS A hA
  | one => exact ⟨one_mem _, one_mem _⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨hx', hxH⟩ := ihx
    obtain ⟨hy', hyH⟩ := ihy
    exact ⟨mul_mem hx' hy', mul_mem hxH hyH⟩
  | inv x hx ih =>
    obtain ⟨hx', hxH⟩ := ih
    exact ⟨inv_mem hx', inv_mem hxH⟩

theorem closure_centralizers_of_plane (c : D4PlaneCert) (hp : c.poolOK = true)
    (ht : c.targetOK = true) (E : Subgroup trialityGroup8)
    (hE : ∀ g : trialityGroup8, ∀ p ∈ c.elems,
      ((g : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat p → g ∈ E) :
    Subgroup.closure {k : trialityGroup8 | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  set H := Subgroup.closure {k : trialityGroup8 | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} with hH
  have hpool : ∀ e ∈ c.pool, (⟨wordGL e.1, wordGL_mem e.1⟩ : trialityGroup8) ∈ H := by
    intro e he
    unfold D4PlaneCert.poolOK at hp
    simp only [List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne,
      ne_eq] at hp
    obtain ⟨⟨hmem, hne⟩, hcomm⟩ := hp e he
    have hy : sylowElemAt e.2 ∈ sylowElems := sylowElemAt_mem _
    obtain ⟨gy, hgy⟩ := exists_elem_of_mem_sylowElems hy
    have hgyE : gy ∈ E :=
      hE gy (sylowElemAt e.2) (List.mem_map.mpr ⟨e.2, hmem, rfl⟩) hgy
    refine Subgroup.subset_closure ⟨gy, hgyE, ?_, ?_⟩
    · intro h
      exact ne_one_of_ne_oneArr hy hgy hne (congrArg Subtype.val h)
    · exact Subtype.ext (mul_comm_of_commutes hcomm (coe_wordGL e.1) hgy)
  have hpa : ∀ m : ℕ, ∃ s ∈ H,
      ((s : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat (c.poolArr.getD m oneArr) := by
    intro m
    by_cases hm : m < c.pool.length
    · have hm' : m < c.poolArr.length := by simpa [D4PlaneCert.poolArr] using hm
      refine ⟨⟨wordGL (c.pool[m]).1, wordGL_mem _⟩, hpool _ (List.getElem_mem hm), ?_⟩
      have : c.poolArr.getD m oneArr = wordArr (c.pool[m]).1 := by
        rw [List.getD_eq_getElem _ _ hm']
        simp [D4PlaneCert.poolArr]
      rw [this]
      exact coe_wordGL _
    · have hm' : c.poolArr.length ≤ m := by simpa [D4PlaneCert.poolArr] using hm
      refine ⟨1, one_mem _, ?_⟩
      rw [List.getD_eq_default _ _ hm', oneArr, toMat_ofMat]
      rfl
  have hprod : ∀ l : List ℕ, ∃ s ∈ H,
      ((s : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
        toMat (arrProd (l.map fun m => c.poolArr.getD m oneArr)) := by
    intro l
    induction l with
    | nil =>
      refine ⟨1, one_mem _, ?_⟩
      rw [List.map_nil, arrProd, List.foldr_nil, oneArr, toMat_ofMat]
      rfl
    | cons m l ih =>
      obtain ⟨s, hs, hsm⟩ := hpa m
      obtain ⟨s', hs', hsm'⟩ := ih
      refine ⟨s * s', mul_mem hs hs', ?_⟩
      have : arrProd ((m :: l).map fun m => c.poolArr.getD m oneArr) =
          mulArr (c.poolArr.getD m oneArr) (arrProd (l.map fun m => c.poolArr.getD m oneArr)) :=
        rfl
      rw [this, toMat_mulArr, ← hsm, ← hsm']
      rfl
  have hletter : ∀ j < 18, (⟨letterGL j, letterGL_mem j⟩ : trialityGroup8) ∈ H := by
    intro j hj
    unfold D4PlaneCert.targetOK at ht
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at ht
    have hj' := ht j hj
    obtain ⟨s, hs, hsm⟩ := hprod (c.targets.getD j [])
    have hsj : s = ⟨letterGL j, letterGL_mem j⟩ := by
      apply Subtype.ext
      apply Units.ext
      rw [hsm, hj', letterArr, toMat_ofMat]
      rfl
    rw [← hsj]
    exact hs
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  refine (exists_mem_of_mem_closure H (S := {A : GL (Fin 8) GF8 |
    (A : Matrix (Fin 8) (Fin 8) GF8) ∈ trialityGens8}) (fun A hA => ?_) g hg).2
  obtain ⟨j, hj, hjA⟩ := exists_letter_of_mem_gens hA
  have : A = letterGL j := Units.ext hjA
  subst this
  exact ⟨letterGL_mem j, hletter j hj⟩

private theorem isElemAbelian_map {p : ℕ} {H K : Type*} [Group H] [Group K] {E : Subgroup H}
    (hE : IsElemAbelian p E) (f : H →* K) : IsElemAbelian p (E.map f) := by
  exact CFSG.Open.IsElemAbelian.map hE f

private theorem closure_centralizers_of_map {G : Type*} [Group G] (e : G ≃* G) (E : Subgroup G)
    (h : Subgroup.closure {k : G | ∃ x ∈ E.map e.toMonoidHom, x ≠ 1 ∧ k * x = x * k} = ⊤) :
    Subgroup.closure {k : G | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hsub : {k' : G | ∃ x ∈ E.map e.toMonoidHom, x ≠ 1 ∧ k' * x = x * k'} ⊆
      e.toMonoidHom '' {k : G | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} := by
    rintro k' ⟨_, ⟨x, hx, rfl⟩, hx1, hk⟩
    refine ⟨e.symm k', ⟨x, hx, ?_, ?_⟩, by simp⟩
    · rintro rfl
      exact hx1 (map_one _)
    · apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hk
  have hle : (⊤ : Subgroup G) ≤
      (Subgroup.closure {k : G | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k}).map e.toMonoidHom := by
    rw [MonoidHom.map_closure, ← h]
    exact Subgroup.closure_mono hsub
  rw [eq_top_iff]
  intro k _
  obtain ⟨c, hc, hck⟩ := hle (Subgroup.mem_top (e k))
  have : c = k := e.injective hck
  exact this ▸ hc

theorem exists_conj_le_sylow
    (hG : Nat.card trialityGroup8 = 211341312) (E : Subgroup trialityGroup8)
    (hE : IsElemAbelian 3 E) :
    ∃ g : trialityGroup8, ∀ x ∈ E.map (MulAut.conj g).toMonoidHom,
      (x : GL (Fin 8) GF8) ∈ sylowGroup := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hle, hcard, -⟩ := sylowGroup_facts
  have hv : (Nat.card trialityGroup8).factorization 3 = 4 := by
    rw [hG]
    have h : (211341312 : ℕ) = 3 ^ 4 * 2609152 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hS : Nat.card (sylowGroup.subgroupOf trialityGroup8) =
      3 ^ (Nat.card trialityGroup8).factorization 3 := by
    rw [hv, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x.1 x.2)⟩
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq trialityGroup8 Q (Sylow.ofCard _ hS)
  have hQ : ((g • Q : Sylow 3 trialityGroup8) : Subgroup trialityGroup8) =
      (Q : Subgroup trialityGroup8).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hconj : E.map (MulAut.conj g).toMonoidHom ≤ sylowGroup.subgroupOf trialityGroup8 := by
    have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hEQ
    rw [← hQ, hg] at this
    exact this
  exact ⟨g, fun x hx => Subgroup.mem_subgroupOf.mp (hconj hx)⟩

theorem closure_centralizers_trialityGroup8
    (hG : Nat.card trialityGroup8 = 211341312)
    (E : Subgroup trialityGroup8) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2) :
    Subgroup.closure {k : trialityGroup8 | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hG E hE
  have hcard' : Nat.card (E.map (MulAut.conj g).toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  obtain ⟨c, hc, hplane⟩ := exists_plane_le _ hg (isElemAbelian_map hE _) hcard'
  obtain ⟨hp, ht⟩ := (plane_check_spec plane_check).2 c hc
  exact closure_centralizers_of_map (MulAut.conj g) E
    (closure_centralizers_of_plane c hp ht _ hplane)

end CFSG.AGLEmbedding.D4Two
