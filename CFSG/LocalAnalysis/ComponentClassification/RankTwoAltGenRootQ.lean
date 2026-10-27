module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenRootPair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEPerm

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

section Four

theorem dep_of_commute_perm_four : ∀ a b c : Perm (Fin 4), a * a = 1 → b * b = 1 → c * c = 1 →
    a * b = b * a → a * c = c * a → b * c = c * b →
    a = 1 ∨ b = 1 ∨ c = 1 ∨ a = b ∨ a = c ∨ b = c ∨ a * b = c := by
  decide

theorem card_filter_pow_four :
    (Finset.univ.filter fun σ : Perm (Fin 4) => sign σ = 1 ∧ σ ^ 4 = 1).card = 4 := by
  decide

variable {N : ℕ} {U : Finset (Fin N)}

@[expose] def FixOut (U : Finset (Fin N)) (w : Perm (Fin N)) : Prop :=
  ∀ y, y ∉ U → w y = y

theorem FixOut.apply_mem_iff {w : Perm (Fin N)} (hw : FixOut U w) (y : Fin N) :
    w y ∈ U ↔ y ∈ U := by
  constructor
  · intro h
    by_contra hy
    rw [hw y hy] at h
    exact hy h
  · intro h
    by_contra hwy
    have h1 := hw (w y) hwy
    rw [w.injective h1] at hwy
    exact hwy h

theorem FixOut.ne_mem {w : Perm (Fin N)} (hw : FixOut U w) (y : Fin N) (h : w y ≠ y) :
    y ∈ U := by
  by_contra hy
  exact h (hw y hy)

theorem FixOut.mul {w w' : Perm (Fin N)} (hw : FixOut U w) (hw' : FixOut U w') :
    FixOut U (w * w') := fun y hy => by rw [Perm.mul_apply, hw' y hy, hw y hy]

theorem FixOut.one : FixOut U (1 : Perm (Fin N)) := fun _ _ => rfl

theorem FixOut.pow {w : Perm (Fin N)} (hw : FixOut U w) (k : ℕ) : FixOut U (w ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact FixOut.one
  | succ k ih => rw [pow_succ]; exact ih.mul hw

@[expose] noncomputable def restr (hU : U.card = 4) (w : Perm (Fin N)) (hw : FixOut U w) :
    Perm (Fin 4) :=
  (Fintype.equivFinOfCardEq (by simp [hU]) : {y // y ∈ U} ≃ Fin 4).permCongrHom
    (w.subtypePerm hw.apply_mem_iff)

theorem restr_mul (hU : U.card = 4) {w w' : Perm (Fin N)} (hw : FixOut U w) (hw' : FixOut U w') :
    restr hU (w * w') (hw.mul hw') = restr hU w hw * restr hU w' hw' := by
  rw [restr, restr, restr, ← map_mul, subtypePerm_mul]

theorem restr_one (hU : U.card = 4) : restr hU 1 FixOut.one = 1 := by
  rw [restr, ← map_one ((Fintype.equivFinOfCardEq (by simp [hU]) :
    {y // y ∈ U} ≃ Fin 4).permCongrHom)]
  congr 1

theorem restr_injective (hU : U.card = 4) {w w' : Perm (Fin N)} (hw : FixOut U w)
    (hw' : FixOut U w') (h : restr hU w hw = restr hU w' hw') : w = w' := by
  rw [restr, restr] at h
  have h1 := (MulEquiv.injective _) h
  rw [← ofSubtype_subtypePerm hw.apply_mem_iff hw.ne_mem,
    ← ofSubtype_subtypePerm hw'.apply_mem_iff hw'.ne_mem, h1]

theorem restr_congr (hU : U.card = 4) {w w' : Perm (Fin N)} (h : w = w') (hw : FixOut U w)
    (hw' : FixOut U w') : restr hU w hw = restr hU w' hw' := by
  subst h
  rfl

theorem sign_restr (hU : U.card = 4) {w : Perm (Fin N)} (hw : FixOut U w) :
    sign (restr hU w hw) = sign w := by
  rw [restr, Equiv.permCongrHom]
  simp only [MulEquiv.coe_mk]
  rw [sign_permCongr]
  convert sign_subtypePerm w hw.apply_mem_iff hw.ne_mem

theorem dep_of_commute_of_fixOut (hU : U.card = 4) {a b c : Perm (Fin N)} (ha : FixOut U a)
    (hb : FixOut U b) (hc : FixOut U c) (ha2 : a * a = 1) (hb2 : b * b = 1) (hc2 : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    a = 1 ∨ b = 1 ∨ c = 1 ∨ a = b ∨ a = c ∨ b = c ∨ a * b = c := by
  have key : ∀ {w w' : Perm (Fin N)} (hw : FixOut U w) (hw' : FixOut U w'), w * w' = w' * w →
      restr hU w hw * restr hU w' hw' = restr hU w' hw' * restr hU w hw := by
    intro w w' hw hw' h
    rw [← restr_mul, ← restr_mul]
    congr 1
  have key2 : ∀ {w : Perm (Fin N)} (hw : FixOut U w), w * w = 1 →
      restr hU w hw * restr hU w hw = 1 := by
    intro w hw h
    rw [← restr_mul, ← restr_one hU]
    congr 1
  rcases dep_of_commute_perm_four _ _ _ (key2 ha ha2) (key2 hb hb2) (key2 hc hc2) (key ha hb hab)
      (key ha hc hac) (key hb hc hbc) with h | h | h | h | h | h | h
  · exact Or.inl (restr_injective hU ha FixOut.one (h.trans (restr_one hU).symm))
  · exact Or.inr (Or.inl (restr_injective hU hb FixOut.one (h.trans (restr_one hU).symm)))
  · exact Or.inr (Or.inr (Or.inl (restr_injective hU hc FixOut.one
      (h.trans (restr_one hU).symm))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (restr_injective hU ha hb h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (restr_injective hU ha hc h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (restr_injective hU hb hc h))))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
    exact restr_injective hU (ha.mul hb) hc (by rw [restr_mul]; exact h)

theorem card_le_four_of_fixOut (hU : U.card = 4) {S : Finset (Perm (Fin N))}
    (hS : ∀ w ∈ S, FixOut U w ∧ sign w = 1 ∧ w ^ 4 = 1) : S.card ≤ 4 := by
  classical
  let ρ : Perm (Fin N) → Perm (Fin 4) := fun w =>
    if h : FixOut U w then restr hU w h else 1
  have hρ : ∀ w (hw : FixOut U w), ρ w = restr hU w hw := fun w hw =>
    dite_eq_left_of_eq_true (eq_true hw)
  have hinj : Set.InjOn ρ S := by
    intro w hwS w' hw'S h
    rw [hρ w (hS w hwS).1, hρ w' (hS w' hw'S).1] at h
    exact restr_injective hU _ _ h
  have himg : S.image ρ ⊆ Finset.univ.filter fun σ : Perm (Fin 4) => sign σ = 1 ∧ σ ^ 4 = 1 := by
    intro σ hσ
    obtain ⟨w, hwS, rfl⟩ := Finset.mem_image.mp hσ
    obtain ⟨hw, hs, h4⟩ := hS w hwS
    rw [Finset.mem_filter, hρ w hw]
    refine ⟨Finset.mem_univ _, by rw [sign_restr]; exact hs, ?_⟩
    have hpow : ∀ k : ℕ, restr hU (w ^ k) (hw.pow k) = restr hU w hw ^ k := by
      intro k
      induction k with
      | zero => exact (restr_congr hU (pow_zero w) _ FixOut.one).trans (restr_one hU)
      | succ k ih =>
        calc restr hU (w ^ (k + 1)) (hw.pow (k + 1)) =
            restr hU (w ^ k * w) ((hw.pow k).mul hw) := restr_congr hU (pow_succ w k) _ _
          _ = restr hU (w ^ k) (hw.pow k) * restr hU w hw := restr_mul hU _ _
          _ = restr hU w hw ^ k * restr hU w hw := by rw [ih]
          _ = restr hU w hw ^ (k + 1) := (pow_succ _ k).symm
    rw [← hpow 4, restr_congr hU h4 _ FixOut.one, restr_one hU]
  calc S.card = (S.image ρ).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card himg
    _ = 4 := card_filter_pow_four

end Four

section QGroup

@[expose] noncomputable def qGen : Fin 4 → Perm (Fin 4 × Fin 2) :=
  ![tauPair 0 * tauPair 1, tauPair 0 * tauPair 2, diagHom (swap 0 1 * swap 2 3),
    diagHom (swap 0 2 * swap 1 3)]

@[expose] noncomputable def qProd (I : Finset (Fin 4)) : Perm (Fin 4 × Fin 2) :=
  (if 0 ∈ I then qGen 0 else 1) * (if 1 ∈ I then qGen 1 else 1) *
    (if 2 ∈ I then qGen 2 else 1) * (if 3 ∈ I then qGen 3 else 1)

theorem qGen_mul_self : ∀ i, qGen i * qGen i = 1 := by
  decide

theorem qGen_commute : ∀ i j, qGen i * qGen j = qGen j * qGen i ∨
    qGen i * qGen j = qGen j * qGen i * zPair 4 := by
  decide

theorem sign_qProd : ∀ I, sign (qProd I) = 1 := by
  decide

theorem qProd_zPair : ∀ I, qProd I * zPair 4 = zPair 4 * qProd I := by
  decide

theorem qProd_pow_four : ∀ I, qProd I ^ 4 = 1 ∧ (qProd I * zPair 4) ^ 4 = 1 := by
  decide

theorem qProd_nodup : ∀ I J : Finset (Fin 4), I ≠ ∅ → J ≠ ∅ → I ≠ J →
    [1, zPair 4, qProd I, qProd I * zPair 4, qProd J, qProd J * zPair 4].Nodup := by
  decide

theorem qProd_triple : ∀ a b c : Fin 4, a < b → b < c →
    qProd {a} = qGen a ∧ qProd {b} = qGen b ∧ qProd {c} = qGen c ∧
      qProd {a, b} = qGen a * qGen b ∧ qProd {a, c} = qGen a * qGen c ∧
      qProd {b, c} = qGen b * qGen c ∧ qProd {a, b, c} = qGen a * qGen b * qGen c := by
  decide

theorem qProd_singleton : ∀ i : Fin 4, qProd {i} = qGen i := by
  decide

theorem eq_empty_of_subset_four : ∀ I : Finset (Fin 4), I ⊆ {1, 2, 3} → I ⊆ {0, 2, 3} →
    I ⊆ {0, 1, 3} → I ⊆ {0, 1, 2} → I = ∅ := by
  decide

end QGroup

section Letters

variable {n : ℕ}

@[expose] def emb8 (n : ℕ) : Fin (n - 4) ↪ Fin (n + 4) where
  toFun k := ⟨k + 8, by have := k.2; omega⟩
  inj' a b h := Fin.ext (by have := congrArg Fin.val h; simp only at this; omega)

@[expose] noncomputable def altEmb8 (n : ℕ) :
    alternatingGroup (Fin (n - 4)) →* alternatingGroup (Fin (n + 4)) :=
  ((viaEmbeddingHom (emb8 n)).comp (alternatingGroup (Fin (n - 4))).subtype).codRestrict _
    fun x => by
      rw [MonoidHom.comp_apply, mem_alternatingGroup, sign_viaEmbeddingHom]
      exact x.2

theorem altEmb8_injective : Function.Injective (altEmb8 n) := by
  intro x y hxy
  have h1 := congrArg (fun z : alternatingGroup (Fin (n + 4)) => (z : Perm (Fin (n + 4)))) hxy
  exact Subtype.ext (viaEmbeddingHom_injective _ h1)

theorem pairAlt_commute_altEmb8 (h8 : 2 * 4 ≤ n + 4) (a : alternatingGroup (Fin 4 × Fin 2))
    (γ : alternatingGroup (Fin (n - 4))) :
    pairAlt h8 a * altEmb8 n γ = altEmb8 n γ * pairAlt h8 a := by
  apply Subtype.ext
  show viaEmbeddingHom (pairEmb h8) (a : Perm (Fin 4 × Fin 2)) *
      viaEmbeddingHom (emb8 n) (γ : Perm (Fin (n - 4))) =
    viaEmbeddingHom (emb8 n) (γ : Perm (Fin (n - 4))) *
      viaEmbeddingHom (pairEmb h8) (a : Perm (Fin 4 × Fin 2))
  refine viaEmbeddingHom_mul_comm _ (τ := 1) (fun kb => ?_) (by rw [mul_one, one_mul])
  rw [Perm.one_apply]
  refine viaEmbeddingHom_apply_of_notMem _ _ ?_
  rintro ⟨k, hk⟩
  have h1 := congrArg Fin.val hk
  have h2 : ((pairEmb h8 kb : Fin (n + 4)) : ℕ) = 2 * kb.1 + kb.2 := rfl
  have h3 : ((emb8 n k : Fin (n + 4)) : ℕ) = k + 8 := rfl
  have := kb.1.2
  have := kb.2.2
  omega

end Letters

section Moved

variable {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ} {f : alternatingGroup α →* Perm (Fin N)}

theorem card_le_card_movedSet (hf : Function.Injective f) (hm : 5 ≤ Fintype.card α) :
    Fintype.card α ≤ (movedSet f).card := by
  obtain ⟨ω₀, hω₀⟩ := exists_stabilizer_ne_top hm (rangeEquiv hf)
  have horb : MulAction.orbit f.range ω₀ ⊆ ((movedSet f : Finset (Fin N)) : Set (Fin N)) := by
    rintro y ⟨h, rfl⟩
    rw [Finset.mem_coe]
    by_contra hy
    apply hω₀
    refine eq_top_iff.mpr fun k _ => ?_
    rw [MulAction.mem_stabilizer_iff]
    have hfix : ∀ z : f.range, z • (h • ω₀) = h • ω₀ := fun z => by
      obtain ⟨x, hx⟩ := z.2
      rw [Subgroup.smul_def, Perm.smul_def, ← hx]
      exact apply_of_not_mem_movedSet f hy x
    have := hfix (h * k * h⁻¹)
    rw [mul_smul, mul_smul, inv_smul_smul] at this
    exact smul_left_cancel h this
  have h1 := le_ncard_orbit hm (rangeEquiv hf) hω₀
  have h2 : (MulAction.orbit f.range ω₀).ncard ≤ (movedSet f).card := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard horb (Finset.finite_toSet _)
  omega

end Moved

namespace AltGenSetting

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G} (s : AltGenSetting A R T g n Φ)
include s

open scoped Pointwise in
theorem mem_of_mem_sup_of_pow_four {w : G}
    (hw : w ∈ Φ.range ⊔ centralizer (Φ.range : Set G)) (h4 : w ^ 4 = 1) : w ∈ Φ.range := by
  have hle : centralizer (Φ.range : Set G) ≤ normalizer (Φ.range : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hw' : w ∈ ((Φ.range : Set G) * (centralizer (Φ.range : Set G) : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hle]
    exact hw
  obtain ⟨y, hy, c, hc, rfl⟩ := Set.mem_mul.mp hw'
  have hyc : Commute y c := mem_centralizer_iff.mp hc y hy
  have h1 : y ^ 4 * c ^ 4 = 1 := by rw [← hyc.mul_pow]; exact h4
  have hc4 : c ^ 4 = 1 := by
    have hcY : c ^ 4 ∈ Φ.range := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_mem (pow_mem hy 4)
    have hcC : c ^ 4 ∈ centralizer (Φ.range : Set G) := pow_mem hc 4
    obtain ⟨π, hπ⟩ := hcY
    have h2 : (π : Perm (Fin (n + 4))) = 1 := by
      refine
        LocalAnalysis.ComponentInitial.AlternatingFourGroup.eq_one_of_forall_commute_alternating
          (by simp only [Fintype.card_fin]; have := s.six_le; omega) fun β hβ => ?_
      have h3 : π * ⟨β, hβ⟩ = ⟨β, hβ⟩ * π := by
        apply s.injective
        rw [map_mul, map_mul, hπ]
        exact (mem_centralizer_iff.mp hcC _ ⟨⟨β, hβ⟩, rfl⟩).symm
      exact congrArg Subtype.val h3
    rw [← hπ, show π = 1 from Subtype.ext h2, map_one]
  have hc1 : c = 1 := by
    have hodd : Odd (orderOf c) :=
      s.odd_card_centralizer.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hc)
    have hdvd : orderOf c ∣ 4 := orderOf_dvd_of_pow_eq_one hc4
    have h1' : orderOf c = 1 := by
      have hle4 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : orderOf c
      · exact absurd hdvd (by norm_num)
      · rfl
      · exact absurd hodd (by decide)
      · exact absurd hdvd (by norm_num)
      · exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp h1'
  rw [hc1, mul_one]
  exact hy

theorem card_le_four_of_pow_four {S : Finset G}
    (hS : ∀ k ∈ S, k ∈ centralizer (A : Set G) ∧ k ^ 4 = 1) : S.card ≤ 4 := by
  classical
  have hY : ∀ k ∈ S, k ∈ Φ.range := fun k hk =>
    s.mem_of_mem_sup_of_pow_four (s.centralizer_le (hS k hk).1) (hS k hk).2
  let θ : G → Perm (Fin (n + 4)) := fun k =>
    if h : k ∈ Φ.range then
      ((MonoidHom.ofInjective s.injective).symm ⟨k, h⟩ : alternatingGroup (Fin (n + 4)))
    else 1
  have hθ : ∀ π : alternatingGroup (Fin (n + 4)), θ (Φ π) = π := by
    intro π
    have h1 : (⟨Φ π, ⟨π, rfl⟩⟩ : Φ.range) = MonoidHom.ofInjective s.injective π :=
      Subtype.ext (MonoidHom.ofInjective_apply _).symm
    show (if h : Φ π ∈ Φ.range then _ else _) = _
    rw [dite_eq_left_of_eq_true (eq_true ⟨π, rfl⟩), h1, MulEquiv.symm_apply_apply]
  have hinj : Set.InjOn θ S := by
    intro k hk k' hk' h
    obtain ⟨π, rfl⟩ := hY k hk
    obtain ⟨π', rfl⟩ := hY k' hk'
    rw [hθ, hθ] at h
    rw [Subtype.ext h]
  set U : Finset (Fin (n + 4)) := Finset.univ.map (Fin.natAddEmb n) with hUdef
  have hU : U.card = 4 := by rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.card_image_of_injOn hinj]
  apply card_le_four_of_fixOut hU
  intro w hw
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨π, rfl⟩ := hY k hk
  rw [hθ]
  refine ⟨fun y hy => ?_, π.2, ?_⟩
  · have hyn : (y : ℕ) < n := by
      by_contra hyn
      apply hy
      rw [hUdef, Finset.mem_map]
      refine ⟨⟨(y : ℕ) - n, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
      simp only [Fin.natAddEmb_apply, Fin.val_natAdd]
      omega
    have h1 := s.fix_of_mem_centralizer (hS _ hk).1 ⟨y, hyn⟩
    have h2 : (Fin.castLEEmb (by omega : n ≤ n + 4) ⟨y, hyn⟩ : Fin (n + 4)) = y :=
      Fin.ext (by simp)
    rw [h2] at h1
    exact h1
  · have h1 := (hS _ hk).2
    rw [← map_pow] at h1
    have h2 := s.injective (h1.trans (map_one Φ).symm)
    exact congrArg Subtype.val h2

theorem false_of_conj_mem_four (hn : 9 ≤ n) (h8 : 2 * 4 ≤ n + 4) {x : G}
    (hx : x * Φ (pairAlt h8 (zAlt (m := 4) ⟨2, rfl⟩)) * x⁻¹ ∈ centralizer (A : Set G)) :
    False := by
  classical
  have h7 : 7 ≤ n := by omega
  set z4 : alternatingGroup (Fin 4 × Fin 2) := zAlt (m := 4) ⟨2, rfl⟩ with hz4
  set Θ := Φ.comp (pairAlt h8) with hΘdef
  have hΘ : Function.Injective Θ := s.injective.comp (pairAlt_injective h8)
  set u := Θ z4 with hu
  have hzz : z4 * z4 = 1 := zAlt_mul_self _
  have hu2 : u * u = 1 := by rw [hu, ← map_mul, hzz, map_one]
  have hu1 : u ≠ 1 := fun h1 => zAlt_ne_one _ (by norm_num) (hΘ (h1.trans (map_one Θ).symm))
  have hux : x * u * x⁻¹ ∈ centralizer (A : Set G) := hx
  have hT1 : ∀ y ∈ centralizer ({u} : Set G), x * y * x⁻¹ ∈ normalizer (A : Set G) := by
    have h := Lemma39.centralizer_le_normalizer_rightConjugate s.sec3.hyp 1
      (t := x * u * x⁻¹) (by rw [AschbacherTightEmbedding.rightConjugate_one]; exact hux)
      (fun h => hu1 (by
        have h' : u = x⁻¹ * (x * u * x⁻¹) * x := by group
        rw [h', h]
        group))
      (by rw [sq]; calc x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
                      _ = 1 := by rw [hu2, mul_one, mul_inv_cancel])
    rw [AschbacherTightEmbedding.rightConjugate_one] at h
    intro y hy
    apply h
    rw [mem_centralizer_singleton_iff] at hy ⊢
    calc x * y * x⁻¹ * (x * u * x⁻¹) = x * (y * u) * x⁻¹ := by group
      _ = x * (u * y) * x⁻¹ := by rw [hy]
      _ = x * u * x⁻¹ * (x * y * x⁻¹) := by group
  set Ψ := Φ.comp (altEmb8 n) with hΨdef
  have hΨ : Function.Injective Ψ := s.injective.comp altEmb8_injective
  have hSu : Ψ.range ≤ centralizer ({u} : Set G) := by
    rintro _ ⟨γ, rfl⟩
    rw [mem_centralizer_singleton_iff, hu, hΨdef, hΘdef, MonoidHom.comp_apply,
      MonoidHom.comp_apply, ← map_mul, ← map_mul, pairAlt_commute_altEmb8]
  have hsimple : IsSimpleGroup (alternatingGroup (Fin (n - 4))) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have eS : alternatingGroup (Fin (n - 4)) ≃* Ψ.range := MonoidHom.ofInjective hΨ
  obtain ⟨hev, h5⟩ := even_five_dvd_card_alternatingGroup (m := n - 4) (by omega)
  have hcS : Nat.card Ψ.range = Nat.card (alternatingGroup (Fin (n - 4))) :=
    (Nat.card_congr eS.toEquiv).symm
  have hSA := s.conj_le_of_simple h7 hu1 hu2 hux hSu (MulEquiv.isSimpleGroup eS.symm)
    (hcS ▸ hev) (hcS ▸ h5)
  set act := actPerm s.psiA.symm (Or.inr h7) with hact
  have hact1 : ∀ y (hy : y ∈ normalizer (A : Set G)), act ⟨y, hy⟩ = 1 ↔
      y ∈ centralizer (A : Set G) := fun y hy => actPerm_eq_one_iff _ _ ⟨y, hy⟩
  have hfmem : ∀ γ, x * Ψ γ * x⁻¹ ∈ normalizer (A : Set G) := fun γ =>
    le_normalizer (hSA ⟨Ψ γ, ⟨γ, rfl⟩, rfl⟩)
  let f₀ : alternatingGroup (Fin (n - 4)) →* normalizer (A : Set G) :=
    ((MulAut.conj x).toMonoidHom.comp Ψ).codRestrict _ hfmem
  let f : alternatingGroup (Fin (n - 4)) →* Perm (Fin n) := act.comp f₀
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro γ hγ
    rw [MonoidHom.mem_ker] at hγ
    have hK : x * Ψ γ * x⁻¹ ∈ centralizer (A : Set G) := (hact1 _ (hfmem γ)).mp hγ
    have hA : x * Ψ γ * x⁻¹ ∈ A := hSA ⟨Ψ γ, ⟨γ, rfl⟩, rfl⟩
    have h1 : x * Ψ γ * x⁻¹ ∈ A ⊓ centralizer (A : Set G) := ⟨hA, hK⟩
    rw [s.inf_centralizer_eq_bot, mem_bot] at h1
    have h2 : Ψ γ = 1 := by
      calc Ψ γ = x⁻¹ * (x * Ψ γ * x⁻¹) * x := by group
        _ = 1 := by rw [h1, mul_one, inv_mul_cancel]
    exact mem_bot.mpr (hΨ (h2.trans (map_one Ψ).symm))
  set Cz : Subgroup (alternatingGroup (Fin 4 × Fin 2)) := centralizer ({z4} : Set _) with hCz
  have hηmem : ∀ a : Cz, x * Θ a * x⁻¹ ∈ normalizer (A : Set G) := by
    intro a
    apply hT1
    rw [mem_centralizer_singleton_iff, hu, ← map_mul, ← map_mul]
    congr 1
    exact mem_centralizer_singleton_iff.mp a.2
  let η₀ : Cz →* normalizer (A : Set G) :=
    ((MulAut.conj x).toMonoidHom.comp (Θ.comp Cz.subtype)).codRestrict _ hηmem
  let η : Cz →* Perm (Fin n) := act.comp η₀
  have hη1 : ∀ a : Cz, η a = 1 ↔ x * Θ a * x⁻¹ ∈ centralizer (A : Set G) := fun a =>
    hact1 _ (hηmem a)
  have hz4C : z4 ∈ Cz := mem_centralizer_singleton_iff.mpr rfl
  have hηz : η ⟨z4, hz4C⟩ = 1 := (hη1 _).mpr hux
  have hηf : ∀ (a : Cz) (γ : alternatingGroup (Fin (n - 4))), f γ * η a = η a * f γ := by
    intro a γ
    have h2 : Ψ γ * Θ a = Θ a * Ψ γ := by
      show Φ (altEmb8 n γ) * Φ (pairAlt h8 a) = Φ (pairAlt h8 a) * Φ (altEmb8 n γ)
      rw [← map_mul, ← map_mul, pairAlt_commute_altEmb8]
    have h1 : f₀ γ * η₀ a = η₀ a * f₀ γ := by
      apply Subtype.ext
      show x * Ψ γ * x⁻¹ * (x * Θ a * x⁻¹) = x * Θ a * x⁻¹ * (x * Ψ γ * x⁻¹)
      calc x * Ψ γ * x⁻¹ * (x * Θ a * x⁻¹) = x * (Ψ γ * Θ a) * x⁻¹ := by group
        _ = x * (Θ a * Ψ γ) * x⁻¹ := by rw [h2]
        _ = x * Θ a * x⁻¹ * (x * Ψ γ * x⁻¹) := by group
    show act (f₀ γ) * act (η₀ a) = act (η₀ a) * act (f₀ γ)
    rw [← map_mul, ← map_mul, h1]
  have hm5 : 5 ≤ Fintype.card (Fin (n - 4)) := by rw [Fintype.card_fin]; omega
  have hNm : n < 2 * Fintype.card (Fin (n - 4)) := by rw [Fintype.card_fin]; omega
  have hM := card_le_card_movedSet hf hm5
  rw [Fintype.card_fin] at hM
  obtain ⟨U, hUsub, -, hU⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ (movedSet f)ᶜ)
    (n := 4) (by rw [Finset.card_compl, Fintype.card_fin]; omega)
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  have hfix : ∀ a : Cz, FixOut U (η a) := by
    intro a y hy
    have hyM : y ∈ movedSet f := by
      by_contra h
      exact hy (hUsub (Finset.mem_compl.mpr h))
    exact fix_of_commute_movedSet hf hm5 hNm (fun γ => hηf a γ) hyM
  let qa : Finset (Fin 4) → Cz := fun I => ⟨⟨qProd I, by
      rw [mem_alternatingGroup]; exact sign_qProd I⟩, by
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (qProd_zPair I)⟩
  have hqa_mul : ∀ I J K, qProd I * qProd J = qProd K → qa I * qa J = qa K := fun I J K h =>
    Subtype.ext (Subtype.ext h)
  set w : Fin 4 → Perm (Fin n) := fun i => η (qa {i}) with hw
  have hw2 : ∀ i, w i * w i = 1 := by
    intro i
    rw [hw, ← map_mul]
    have h1 : qa {i} * qa {i} = 1 := Subtype.ext (Subtype.ext (by
      show qProd {i} * qProd {i} = 1
      rw [qProd_singleton]
      exact qGen_mul_self i))
    rw [h1, map_one]
  have hwc : ∀ i j, w i * w j = w j * w i := by
    intro i j
    rcases qGen_commute i j with h | h
    · rw [hw, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subtype.ext (by
        show qProd {i} * qProd {j} = qProd {j} * qProd {i}
        rw [qProd_singleton, qProd_singleton, h]))
    · rw [hw, ← map_mul, ← map_mul]
      have h1 : qa {i} * qa {j} = qa {j} * qa {i} * ⟨z4, hz4C⟩ := Subtype.ext (Subtype.ext (by
        show qProd {i} * qProd {j} = qProd {j} * qProd {i} * zPair 4
        rw [qProd_singleton, qProd_singleton, h]))
      rw [h1, map_mul, hηz, mul_one]
  set P : Finset (Fin 4) → Prop := fun I => η (qa I) = 1 with hP
  have hP2 : ∀ I J, I ≠ ∅ → J ≠ ∅ → P I → P J → I = J := by
    intro I J hI hJ hPI hPJ
    by_contra hIJ
    let L : List (alternatingGroup (Fin 4 × Fin 2)) :=
      [1, z4, (qa I : alternatingGroup _), (qa I : alternatingGroup _) * z4,
        (qa J : alternatingGroup _), (qa J : alternatingGroup _) * z4]
    have hLnd : L.Nodup := by
      apply List.Nodup.of_map Subtype.val
      exact qProd_nodup I J hI hJ hIJ
    have hconj : Function.Injective fun a : alternatingGroup (Fin 4 × Fin 2) => x * Θ a * x⁻¹ := by
      intro a b h
      apply hΘ
      simpa using h
    have hcard : (L.map fun a => x * Θ a * x⁻¹).toFinset.card = 6 := by
      rw [List.toFinset_card_of_nodup (hLnd.map hconj)]
      simp [L]
    have hle := s.card_le_four_of_pow_four (S := (L.map fun a => x * Θ a * x⁻¹).toFinset) (by
      intro k hk
      rw [List.mem_toFinset, List.mem_map] at hk
      obtain ⟨a, ha, rfl⟩ := hk
      have hKI : x * Θ (qa I) * x⁻¹ ∈ centralizer (A : Set G) := (hη1 _).mp hPI
      have hKJ : x * Θ (qa J) * x⁻¹ ∈ centralizer (A : Set G) := (hη1 _).mp hPJ
      have hmul : ∀ b c : alternatingGroup (Fin 4 × Fin 2), x * Θ (b * c) * x⁻¹ =
          (x * Θ b * x⁻¹) * (x * Θ c * x⁻¹) := fun b c => by rw [map_mul]; group
      have hpow : ∀ b : alternatingGroup (Fin 4 × Fin 2), (b : Perm (Fin 4 × Fin 2)) ^ 4 = 1 →
          (x * Θ b * x⁻¹) ^ 4 = 1 := by
        intro b hb
        have hb' : b ^ 4 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hb)
        rw [conj_pow, ← map_pow, hb', map_one, mul_one, mul_inv_cancel]
      simp only [L, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨by rw [map_one, mul_one, mul_inv_cancel]; exact one_mem _, by
          rw [map_one, mul_one, mul_inv_cancel, one_pow]⟩
      · exact ⟨hux, hpow _ (by show (zPair 4) ^ 4 = 1; decide)⟩
      · exact ⟨hKI, hpow _ (qProd_pow_four I).1⟩
      · exact ⟨by rw [hmul]; exact mul_mem hKI hux, hpow _ (qProd_pow_four I).2⟩
      · exact ⟨hKJ, hpow _ (qProd_pow_four J).1⟩
      · exact ⟨by rw [hmul]; exact mul_mem hKJ hux, hpow _ (qProd_pow_four J).2⟩)
    omega
  have htriple : ∀ a b c : Fin 4, a < b → b < c →
      ∃ I : Finset (Fin 4), I ≠ ∅ ∧ I ⊆ {a, b, c} ∧ P I := by
    intro a b c hab hbc
    obtain ⟨-, -, -, e12, e13, e23, e123⟩ := qProd_triple a b c hab hbc
    have hw_mul : ∀ I : Finset (Fin 4), ∀ i j, qProd I = qGen i * qGen j →
        η (qa I) = w i * w j := by
      intro I i j h
      rw [hw, ← map_mul]
      congr 1
      exact Subtype.ext (Subtype.ext (by
        show qProd I = qProd {i} * qProd {j}
        rw [qProd_singleton, qProd_singleton, h]))
    have hw_mul3 : ∀ I : Finset (Fin 4), ∀ i j k, qProd I = qGen i * qGen j * qGen k →
        η (qa I) = w i * w j * w k := by
      intro I i j k h
      rw [hw, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subtype.ext (by
        show qProd I = qProd {i} * qProd {j} * qProd {k}
        rw [qProd_singleton, qProd_singleton, qProd_singleton, h]))
    rcases dep_of_commute_of_fixOut (a := w a) (b := w b) (c := w c) hU (hfix _) (hfix _)
        (hfix _) (hw2 a) (hw2 b) (hw2 c) (hwc a b) (hwc a c) (hwc b c) with
      h | h | h | h | h | h | h
    · exact ⟨{a}, by simp, by simp, h⟩
    · exact ⟨{b}, by simp, by simp, h⟩
    · exact ⟨{c}, by simp, by simp, h⟩
    · refine ⟨{a, b}, by simp, by simp [Finset.insert_subset_iff], ?_⟩
      show η (qa {a, b}) = 1
      rw [hw_mul _ a b e12, h, hw2]
    · refine ⟨{a, c}, by simp, by simp [Finset.insert_subset_iff], ?_⟩
      show η (qa {a, c}) = 1
      rw [hw_mul _ a c e13, h, hw2]
    · refine ⟨{b, c}, by simp, by simp, ?_⟩
      show η (qa {b, c}) = 1
      rw [hw_mul _ b c e23, h, hw2]
    · refine ⟨{a, b, c}, by simp, le_refl _, ?_⟩
      show η (qa {a, b, c}) = 1
      rw [hw_mul3 _ a b c e123, h, hw2]
  obtain ⟨I₁, hI₁, hs₁, hP₁⟩ := htriple 1 2 3 (by decide) (by decide)
  obtain ⟨I₂, hI₂, hs₂, hP₂⟩ := htriple 0 2 3 (by decide) (by decide)
  obtain ⟨I₃, hI₃, hs₃, hP₃⟩ := htriple 0 1 3 (by decide) (by decide)
  obtain ⟨I₄, hI₄, hs₄, hP₄⟩ := htriple 0 1 2 (by decide) (by decide)
  have h12 := hP2 _ _ hI₁ hI₂ hP₁ hP₂
  have h13 := hP2 _ _ hI₁ hI₃ hP₁ hP₃
  have h14 := hP2 _ _ hI₁ hI₄ hP₁ hP₄
  exact hI₁ (eq_empty_of_subset_four I₁ hs₁ (h12 ▸ hs₂) (h13 ▸ hs₃) (h14 ▸ hs₄))

end AltGenSetting

end CFSG.ComponentClassification.RankTwoAlt
