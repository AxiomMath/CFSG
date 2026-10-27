module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaTorus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpARadicalComm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.SeitzReduction.SymplecticPilot CFSG.SignalizerFunctorTheorem.NonLocal
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open scoped MatrixGroups Matrix commutatorElement
open Matrix

section Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2] {ℓ : ℕ}

@[expose] noncomputable def symplecticQTorus (q : ℕ) : Subgroup (StatedSp ℓ F) :=
  ((⊤ : Subgroup (Fin ℓ → rootsOfUnity q F)).map
    ((diagSp F ℓ).comp ((rootsOfUnity q F).subtype.compLeft (Fin ℓ))))

theorem mem_symplecticQTorus {q : ℕ} {g : StatedSp ℓ F} :
    g ∈ symplecticQTorus (F := F) (ℓ := ℓ) q ↔
      ∃ t : Fin ℓ → Fˣ, (∀ i, t i ^ q = 1) ∧ g = diagSp F ℓ t := by
  constructor
  · rintro ⟨t, -, rfl⟩
    exact ⟨fun i => (t i : Fˣ), fun i => by
      have h := congrArg Subtype.val
        (CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.rootsOfUnity_pow_eq_one'
          (t i))
      simpa using h, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => (⟨t i, ht i⟩ : rootsOfUnity q F), trivial, ?_⟩
    rfl

theorem isElemAbelian_symplecticQTorus {q : ℕ} (hq : q.Prime) :
    IsElemAbelian q (symplecticQTorus (F := F) (ℓ := ℓ) q) := by
  have htop : IsElemAbelian q (⊤ : Subgroup (Fin ℓ → rootsOfUnity q F)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (funext fun i => mul_comm _ _)⟩⟩, fun x _ => ?_⟩
    funext i
    exact Subtype.ext (by
      have h := congrArg Subtype.val
        (CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.rootsOfUnity_pow_eq_one'
          (x i))
      simpa using h)
  have h := CFSG.SectionRank.isElemAbelian_map htop
    ((diagSp F ℓ).comp ((rootsOfUnity q F).subtype.compLeft (Fin ℓ)))
  simpa [symplecticQTorus, MonoidHom.range_eq_map] using h

theorem card_symplecticQTorus {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1) :
    Nat.card (symplecticQTorus (F := F) (ℓ := ℓ) q) = q ^ ℓ := by
  have hφ : Function.Injective
      ((diagSp F ℓ).comp ((rootsOfUnity q F).subtype.compLeft (Fin ℓ))) :=
    diagSp_injective.comp fun a b h => funext fun i => Subtype.ext (congrFun h i)
  rw [symplecticQTorus, ← MonoidHom.range_eq_map,
    ← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_fun,
    CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.card_rootsOfUnity_of_dvd'
      hq (by rwa [Nat.card_units]),
    Nat.card_fin]

end Torus

section Centralizer

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}

theorem commutator_mem_complSp_of_centralizer_rootTorusHom {k : Fin (m + 1)} {ζ : Fˣ}
    (hζ : ζ * ζ ≠ 1) {g g' : StatedSp (m + 1) F}
    (hg : g ∈ Subgroup.centralizer ({rootTorusHom F (m + 1) k ζ} : Set (StatedSp (m + 1) F)))
    (hg' : g' ∈ Subgroup.centralizer
      ({rootTorusHom F (m + 1) k ζ} : Set (StatedSp (m + 1) F))) :
    g * g' * g⁻¹ * g'⁻¹ ∈ complSp F k := by
  refine commutator_mem_of_eq_mul
    (A := rootTorusSp F k)
    (fun a ha a' ha' => Subgroup.mem_centralizer_iff.1
      (rootTorusSp_le_centralizer_self k ha') a ha)
    (fun a ha d hd => Subgroup.mem_centralizer_iff.1
      (complSp_le_centralizer_rootTorusSp k hd) a ha)
    ?_ ?_
  · have hcomm : g * rootTorusHom F (m + 1) k ζ = rootTorusHom F (m + 1) k ζ * g :=
      Subgroup.mem_centralizer_singleton_iff.1 hg
    obtain ⟨u, y, hy, rfl⟩ := exists_eq_mul_of_commute_rootTorusHom hζ hcomm
    exact ⟨_, rootTorusHom_mem_rootTorusSp k u, y, hy, rfl⟩
  · have hcomm : g' * rootTorusHom F (m + 1) k ζ = rootTorusHom F (m + 1) k ζ * g' :=
      Subgroup.mem_centralizer_singleton_iff.1 hg'
    obtain ⟨u, y, hy, rfl⟩ := exists_eq_mul_of_commute_rootTorusHom hζ hcomm
    exact ⟨_, rootTorusHom_mem_rootTorusSp k u, y, hy, rfl⟩

end Centralizer

section Siegel

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

private theorem eq_upperUnipotentSp_of_mem_spSiegel {e : StatedSp m F} {C : Matrix (Fin m) (Fin m) F}
    (hC : Cᵀ = C) (h : ((e : GL (Fin m ⊕ Fin m) F) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) =
      Matrix.fromBlocks 1 C 0 1) : e = upperUnipotentSp m F hC := by
  apply mat_injective
  rw [mat_upperUnipotentSp, mat_apply]
  exact h

private theorem upperUnipotentSp_eq_one_iff {C : Matrix (Fin m) (Fin m) F} (hC : Cᵀ = C) :
    upperUnipotentSp m F hC = 1 ↔ C = 0 := by
  constructor
  · intro h
    have h' := congrArg (mat m F) h
    rw [mat_upperUnipotentSp, MonoidHom.map_one, ← Matrix.fromBlocks_one] at h'
    exact (Matrix.fromBlocks_inj.1 h').2.1
  · rintro rfl
    exact upperUnipotentSp_zero

private theorem leviEmbedGL_conj_mem_spSiegel (A : GL (Fin m) F) {e : StatedSp m F}
    (he : e ∈ spSiegel m F) :
    leviEmbedGL F m A * e * (leviEmbedGL F m A)⁻¹ ∈ spSiegel m F := by
  obtain ⟨C, hC, hM⟩ := he
  rw [eq_upperUnipotentSp_of_mem_spSiegel hC.eq hM, leviEmbedGL_conj_upperUnipotentSp]
  exact (mem_spSiegel m F).2 ⟨_, (transpose_mul_mul_transpose _ hC.eq),
    mat_upperUnipotentSp _⟩

private theorem diagGL_mul_mul_transpose_apply (t : Fin m → Fˣ) (C : Matrix (Fin m) (Fin m) F)
    (i j : Fin m) :
    ((TauCeti.diagGL t : Matrix (Fin m) (Fin m) F) * C *
      (TauCeti.diagGL t : Matrix (Fin m) (Fin m) F)ᵀ) i j = (t i : F) * C i j * (t j : F) := by
  rw [TauCeti.diagGL_coe]
  exact diagonal_mul_mul_transpose_apply (fun i => (t i : F)) C i j

private theorem diagSp_mul_eq_one_of_mem_centralizer_spSiegel {t : Fin m → Fˣ}
    (hc : diagSp F m t ∈ Subgroup.centralizer (spSiegel m F : Set (StatedSp m F))) (i j : Fin m) :
    t i * t j = 1 := by
  set C : Matrix (Fin m) (Fin m) F :=
    if i = j then Matrix.single i i (1 : F) else Matrix.single i j 1 + Matrix.single j i 1 with hCdef
  have hCsymm : Cᵀ = C := by
    by_cases hij : i = j
    · subst hij
      simp [hCdef]
    · simp only [hCdef, if_neg hij, Matrix.transpose_add, Matrix.transpose_single, add_comm]
  have hcomm : upperUnipotentSp m F hCsymm * diagSp F m t =
      diagSp F m t * upperUnipotentSp m F hCsymm :=
    Subgroup.mem_centralizer_iff.1 hc (upperUnipotentSp m F hCsymm)
      ((mem_spSiegel m F).2 ⟨C, hCsymm, mat_upperUnipotentSp _⟩)
  have hconj : diagSp F m t * upperUnipotentSp m F hCsymm * (diagSp F m t)⁻¹ =
      upperUnipotentSp m F hCsymm := by
    rw [← hcomm]
    group
  have hcommutator : ⁅diagSp F m t, upperUnipotentSp m F hCsymm⁆ = 1 := by
    rw [commutatorElement_def, hconj, mul_inv_cancel]
  rw [diagSp_apply, commutatorElement_leviEmbedGL_upperUnipotentSp] at hcommutator
  have hzero := (upperUnipotentSp_eq_one_iff _).1 hcommutator
  have hentry : (t i : F) * C i j * (t j : F) - C i j = 0 := by
    have := congrArg (fun M : Matrix (Fin m) (Fin m) F => M i j) hzero
    rwa [Matrix.sub_apply, Matrix.zero_apply, diagGL_mul_mul_transpose_apply] at this
  have hCij : C i j = 1 := by
    by_cases hij : i = j
    · subst hij
      simp [hCdef]
    · simp [hCdef, hij]
  rw [hCij, mul_one] at hentry
  have hprod : (t i : F) * (t j : F) = 1 := by
    have := sub_eq_zero.1 hentry
    exact this
  exact Units.ext hprod

end Siegel

section Element

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}

private theorem rootsOfUnity_eq_zpowers {q : ℕ} (hq : q.Prime) {ζ : Fˣ}
    (hζ : orderOf ζ = q) : rootsOfUnity q F = Subgroup.zpowers ζ := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  exact ((hζ ▸ IsPrimitiveRoot.orderOf ζ).zpowers_eq).symm

private theorem diagSp_eq_one_of_mem_centralizer_spSiegel {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {t : Fin m → Fˣ} (hpow : ∀ i, t i ^ q = 1)
    (hc : diagSp F m t ∈ Subgroup.centralizer (spSiegel m F : Set (StatedSp m F))) :
    t = 1 := by
  funext i
  have h2 : t i ^ 2 = 1 := by
    rw [pow_two]
    exact diagSp_mul_eq_one_of_mem_centralizer_spSiegel hc i i
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega
  have hcop : Nat.Coprime 2 q := Nat.coprime_two_left.2 (hq.odd_iff.2 hq3)
  have hdvd : orderOf (t i) ∣ 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one (hpow i))
    rwa [hcop] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd)

theorem symplecticQTorus_le_normalizer_spSiegel (q : ℕ) :
    symplecticQTorus (F := F) (ℓ := m) q ≤
      Subgroup.normalizer (spSiegel m F : Set (StatedSp m F)) := by
  intro b hb
  obtain ⟨t, -, rfl⟩ := (mem_symplecticQTorus (F := F) (ℓ := m)).1 hb
  rw [diagSp_apply]
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨?_, ?_⟩
  · intro hx
    simpa using leviEmbedGL_conj_mem_spSiegel (TauCeti.diagGL t) hx
  · intro hx
    have hx' : leviEmbedGL F m (TauCeti.diagGL t) * x *
        (leviEmbedGL F m (TauCeti.diagGL t))⁻¹ ∈ spSiegel m F := by
      simpa [diagSp_apply] using hx
    have h := leviEmbedGL_conj_mem_spSiegel (A := (TauCeti.diagGL t)⁻¹) hx'
    simpa [map_inv, mul_assoc] using h

theorem symplecticQTorus_inf_centralizer_spSiegel {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    symplecticQTorus (F := F) (ℓ := m) q ⊓
        Subgroup.centralizer (spSiegel m F : Set (StatedSp m F)) = ⊥ := by
  refine le_bot_iff.1 ?_
  rintro b ⟨hb, hbc⟩
  obtain ⟨t, hpow, rfl⟩ := (mem_symplecticQTorus (F := F) (ℓ := m)).1 hb
  rw [diagSp_eq_one_of_mem_centralizer_spSiegel hq hq2 hpow hbc, map_one]
  exact Subgroup.mem_bot.2 rfl

private theorem diagSp_eq_rootTorusHom_mul_update {t : Fin (m + 1) → Fˣ} :
    diagSp F (m + 1) t =
      rootTorusHom F (m + 1) 0 (t 0) * diagSp F (m + 1) (Function.update t 0 1) := by
  rw [rootTorusHom_apply, ← map_mul]
  congr 1
  funext i
  rw [Pi.mul_apply, Function.update_apply]
  by_cases hi : i = 0
  · subst hi
    simp
  · rw [Pi.mulSingle_eq_of_ne hi]
    simp [hi]

private theorem mem_complSp_diagSp {t : Fin (m + 1) → Fˣ} (h0 : t 0 = 1) :
    diagSp F (m + 1) t ∈ complSp F (0 : Fin (m + 1)) := by
  rw [mem_complSp, IsSupp]
  intro r s hrs
  rw [mat_diagSp_apply]
  have hone : (1 : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) r s =
      if r = s then 1 else 0 := Matrix.one_apply
  rw [hone]
  by_cases h : r = s
  · subst h
    have hmem : r ∈ coords (0 : Fin (m + 1)) := by
      by_contra hc
      exact hrs ⟨by simpa using hc, by simpa using hc⟩
    rcases mem_coords.1 hmem with rfl | rfl <;> simp [h0]
  · simp [h]

theorem rootTorusHom_mem_complSp_of_ne {k j : Fin (m + 1)} (hkj : k ≠ j) (u : Fˣ) :
    rootTorusHom F (m + 1) k u ∈ complSp F j := by
  refine suppGroup_mono ?_ (isSupp_rootTorusHom k u)
  intro a ha
  rw [Set.mem_compl_iff]
  intro haj
  rcases mem_coords.1 ha with rfl | rfl <;> rcases mem_coords.1 haj with h | h
  · exact hkj (Sum.inl_injective h)
  · exact Sum.inl_ne_inr h
  · exact Sum.inr_ne_inl h
  · exact hkj (Sum.inr_injective h)

theorem symplecticQTorus_le_sup_complSp_zpowers {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card F - 1) {ζ : Fˣ} (hζ : orderOf ζ = q) :
    symplecticQTorus (F := F) (ℓ := m + 1) q ≤
      complSp F (0 : Fin (m + 1)) ⊔ Subgroup.zpowers (rootTorusHom F (m + 1) 0 ζ) := by
  intro b hb
  obtain ⟨t, hpow, rfl⟩ := (mem_symplecticQTorus).1 hb
  have ht0 : t 0 ∈ Subgroup.zpowers ζ := by
    rw [← rootsOfUnity_eq_zpowers hq hζ]
    exact (mem_rootsOfUnity q (t 0)).2 (hpow 0)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ht0
  have hx : rootTorusHom F (m + 1) 0 (t 0) =
      (rootTorusHom F (m + 1) 0 ζ) ^ k := by
    rw [← hk, map_zpow]
  have hd : diagSp F (m + 1) (Function.update t 0 1) ∈ complSp F (0 : Fin (m + 1)) := by
    refine mem_complSp_diagSp ?_
    rw [Function.update_apply, if_pos rfl]
  rw [diagSp_eq_rootTorusHom_mul_update, hx]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k))
    (Subgroup.mem_sup_left hd)

end Element

section Complement

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}

@[expose] noncomputable def complSpSiegel (m : ℕ) : Subgroup (StatedSp (m + 1) F) :=
  (spSiegel m F).map ((complSp F (0 : Fin (m + 1))).subtype.comp
    (complSpEquiv (K := F) (0 : Fin (m + 1))).toMonoidHom)

private theorem mem_complSpSiegel {x : StatedSp (m + 1) F} :
    x ∈ complSpSiegel (F := F) m ↔ ∃ s ∈ spSiegel m F,
      ((complSpEquiv (K := F) (0 : Fin (m + 1)) s : complSp F 0) : StatedSp (m + 1) F) = x := by
  simp [complSpSiegel, Subgroup.mem_map]

private theorem complSpEquiv_mem_complSpSiegel {s : StatedSp m F} (hs : s ∈ spSiegel m F) :
    ((complSpEquiv (K := F) (0 : Fin (m + 1)) s : complSp F 0) : StatedSp (m + 1) F) ∈
      complSpSiegel (F := F) m :=
  (mem_complSpSiegel (F := F) (m := m)).2 ⟨s, hs, rfl⟩

theorem complSpSiegel_le_complSp :
    complSpSiegel (F := F) m ≤ complSp F (0 : Fin (m + 1)) := by
  rintro _ ⟨s, -, rfl⟩
  exact (complSpEquiv (K := F) (0 : Fin (m + 1)) s).2

theorem isPGroup_complSpSiegel : IsPGroup 2 (complSpSiegel (F := F) m) := by
  have h := IsPGroup.map (p := 2) (isPGroup_spSiegel (F := F) m)
    ((complSp F (0 : Fin (m + 1))).subtype.comp
      (complSpEquiv (K := F) (0 : Fin (m + 1))).toMonoidHom)
  exact h

private theorem coe_complSpEquiv_diagSp {t : Fin m → Fˣ} :
    ((complSpEquiv (K := F) (0 : Fin (m + 1)) (diagSp F m t) : complSp F 0) :
        StatedSp (m + 1) F) =
      diagSp F (m + 1) (Fin.insertNth (0 : Fin (m + 1)) (1 : Fˣ) t) := by
  rw [kOmega_coe_complSpEquiv_diagSp, kOmegaInsert_apply]

private theorem diagSp_conj_mem_complSpSiegel {t : Fin (m + 1) → Fˣ} (h0 : t 0 = 1)
    {x : StatedSp (m + 1) F} (hx : x ∈ complSpSiegel (F := F) m) :
    diagSp F (m + 1) t * x * (diagSp F (m + 1) t)⁻¹ ∈ complSpSiegel (F := F) m := by
  have hins : Fin.insertNth (0 : Fin (m + 1)) (1 : Fˣ)
      (fun i : Fin m => t (Fin.succAbove (0 : Fin (m + 1)) i)) = t := by
    funext i
    rcases Fin.eq_self_or_eq_succAbove (0 : Fin (m + 1)) i with rfl | ⟨j, rfl⟩
    · simp [h0]
    · rw [Fin.insertNth_apply_succAbove]
  have hd : ((complSpEquiv (K := F) (0 : Fin (m + 1))
      (diagSp F m (fun i : Fin m => t (Fin.succAbove (0 : Fin (m + 1)) i))) : complSp F 0) :
        StatedSp (m + 1) F) = diagSp F (m + 1) t :=
    (coe_complSpEquiv_diagSp (t := fun i : Fin m => t (Fin.succAbove (0 : Fin (m + 1)) i))).trans
      (congrArg (diagSp F (m + 1)) hins)
  obtain ⟨s, hs, rfl⟩ := (mem_complSpSiegel (F := F) (m := m)).1 hx
  have hlev := leviEmbedGL_conj_mem_spSiegel (F := F) (m := m)
    (TauCeti.diagGL (fun i : Fin m => t (Fin.succAbove (0 : Fin (m + 1)) i))) hs
  have hlev' : diagSp F m (fun i : Fin m => t (Fin.succAbove (0 : Fin (m + 1)) i)) * s *
      (diagSp F m (fun i : Fin m => t (Fin.succAbove (0 : Fin (m + 1)) i)))⁻¹ ∈
        spSiegel m F := by
    simpa [diagSp_apply] using hlev
  refine (mem_complSpSiegel (F := F) (m := m)).2 ⟨_, hlev', ?_⟩
  have hcoe : ((complSpEquiv (K := F) (0 : Fin (m + 1))
      (diagSp F m (fun i : Fin m => t (Fin.succAbove (0 : Fin (m + 1)) i)) * s *
        (diagSp F m (fun i : Fin m => t (Fin.succAbove (0 : Fin (m + 1)) i)))⁻¹) :
          complSp F 0) : StatedSp (m + 1) F) = diagSp F (m + 1) t *
      ((complSpEquiv (K := F) (0 : Fin (m + 1)) s : complSp F 0) : StatedSp (m + 1) F) *
        (diagSp F (m + 1) t)⁻¹ := by
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hd]
  exact hcoe

private theorem diagSp_mem_normalizer_complSpSiegel {t : Fin (m + 1) → Fˣ} (h0 : t 0 = 1) :
    diagSp F (m + 1) t ∈ Subgroup.normalizer (complSpSiegel (F := F) m : Set _) := by
  have h0inv : (t⁻¹) 0 = 1 := by
    rw [Pi.inv_apply, h0, inv_one]
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨diagSp_conj_mem_complSpSiegel h0,
    fun hx => ?_⟩
  have h := diagSp_conj_mem_complSpSiegel (t := t⁻¹) h0inv hx
  simpa [map_inv, mul_assoc] using h

end Complement

section Normalizer

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}

theorem symplecticQTorus_le_normalizer_complSpSiegel (q : ℕ) :
    symplecticQTorus (F := F) (ℓ := m + 1) q ≤
      Subgroup.normalizer (complSpSiegel (F := F) m : Set _) := by
  intro b hb
  obtain ⟨t, hpow, rfl⟩ := (mem_symplecticQTorus (ℓ := m + 1)).1 hb
  rw [diagSp_eq_rootTorusHom_mul_update]
  refine Subgroup.mul_mem _ ?_ ?_
  · refine Subgroup.mem_normalizer_iff.2 fun z => ⟨?_, ?_⟩
    · intro hz
      have hcomm : Commute (rootTorusHom F (m + 1) 0 (t 0)) z :=
        commute_of_mem_longRootSp2_of_mem_complSp
          (rootTorusSp_le_longRootSp2 0 (rootTorusHom_mem_rootTorusSp 0 (t 0)))
          (complSpSiegel_le_complSp hz)
      have h : rootTorusHom F (m + 1) 0 (t 0) * z * (rootTorusHom F (m + 1) 0 (t 0))⁻¹ = z := by
        rw [hcomm.eq]
        group
      rwa [h]
    · intro hz
      have hzJ : rootTorusHom F (m + 1) 0 (t 0) * z *
          (rootTorusHom F (m + 1) 0 (t 0))⁻¹ ∈ complSp F (0 : Fin (m + 1)) :=
        complSpSiegel_le_complSp hz
      have hcomm : Commute (rootTorusHom F (m + 1) 0 (t 0))
          (rootTorusHom F (m + 1) 0 (t 0) * z * (rootTorusHom F (m + 1) 0 (t 0))⁻¹) :=
        commute_of_mem_longRootSp2_of_mem_complSp
          (rootTorusSp_le_longRootSp2 0 (rootTorusHom_mem_rootTorusSp 0 (t 0))) hzJ
      have h : z = rootTorusHom F (m + 1) 0 (t 0) * z *
          (rootTorusHom F (m + 1) 0 (t 0))⁻¹ := by
        calc z = (rootTorusHom F (m + 1) 0 (t 0))⁻¹ *
              (rootTorusHom F (m + 1) 0 (t 0) * z *
                (rootTorusHom F (m + 1) 0 (t 0))⁻¹) *
              rootTorusHom F (m + 1) 0 (t 0) := by group
          _ = rootTorusHom F (m + 1) 0 (t 0) * z *
              (rootTorusHom F (m + 1) 0 (t 0))⁻¹ := by
            rw [mul_assoc, hcomm.eq.symm, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h]
      exact hz
  · refine diagSp_mem_normalizer_complSpSiegel ?_
    rw [Function.update_apply, if_pos rfl]

private theorem exists_zpow_of_mem_symplecticQTorus {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1)
    {ζ : Fˣ} (hζ : orderOf ζ = q) {u : Fˣ} (hu : u ^ q = 1) :
    ∃ k : ℤ, ζ ^ k = u := by
  have hmem : u ∈ rootsOfUnity q F := (mem_rootsOfUnity q u).2 hu
  rw [rootsOfUnity_eq_zpowers hq hζ] at hmem
  exact Subgroup.mem_zpowers_iff.1 hmem

theorem symplecticQTorus_inf_centralizer_complSpSiegel {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ Nat.card F - 1) {ζ : Fˣ} (hζ : orderOf ζ = q) :
    symplecticQTorus (F := F) (ℓ := m + 1) q ⊓
        Subgroup.centralizer (complSpSiegel (F := F) m : Set _) =
      Subgroup.zpowers (rootTorusHom F (m + 1) 0 ζ) := by
  set e := complSpEquiv (K := F) (0 : Fin (m + 1)) with he
  refine le_antisymm ?_ ?_
  · rintro b ⟨hb, hbc⟩
    obtain ⟨t, hpow, rfl⟩ := (mem_symplecticQTorus (F := F) (ℓ := m + 1)).1 hb
    set t' : Fin m → Fˣ := fun i => t (Fin.succAbove (0 : Fin (m + 1)) i) with ht'
    have ht'pow : ∀ i, t' i ^ q = 1 := fun i => hpow _
    have haC : rootTorusHom F (m + 1) 0 (t 0) ∈
        Subgroup.centralizer (complSpSiegel (F := F) m : Set _) := by
      refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
      exact (commute_of_mem_longRootSp2_of_mem_complSp
        (rootTorusSp_le_longRootSp2 0 (rootTorusHom_mem_rootTorusSp 0 (t 0)))
        (complSpSiegel_le_complSp hz)).eq.symm
    have h0ins : Fin.insertNth (0 : Fin (m + 1)) (1 : Fˣ) t' =
        Function.update t 0 1 := by
      funext i
      rcases Fin.eq_self_or_eq_succAbove (0 : Fin (m + 1)) i with rfl | ⟨j, rfl⟩
      · rw [Fin.insertNth_apply_same, Function.update_apply, if_pos rfl]
      · rw [Fin.insertNth_apply_succAbove, Function.update_apply, if_neg (Fin.succAbove_ne 0 j)]
    have hdC : diagSp F (m + 1) (Function.update t 0 1) ∈
        Subgroup.centralizer (complSpSiegel (F := F) m : Set _) := by
      have h1 : (rootTorusHom F (m + 1) 0 (t 0))⁻¹ * diagSp F (m + 1) t ∈
          Subgroup.centralizer (complSpSiegel (F := F) m : Set _) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ haC) hbc
      have heq : (rootTorusHom F (m + 1) 0 (t 0))⁻¹ * diagSp F (m + 1) t =
          diagSp F (m + 1) (Function.update t 0 1) := by
        rw [diagSp_eq_rootTorusHom_mul_update]
        group
      rwa [heq] at h1
    have hx0eq : ((e (diagSp F m t') : complSp F 0) : StatedSp (m + 1) F) =
        diagSp F (m + 1) (Function.update t 0 1) := by
      rw [coe_complSpEquiv_diagSp, h0ins]
    have hdcent' : diagSp F m t' ∈
        Subgroup.centralizer (spSiegel m F : Set (StatedSp m F)) := by
      intro s hs
      have hS : ((e s : complSp F 0) : StatedSp (m + 1) F) ∈ complSpSiegel (F := F) m :=
        complSpEquiv_mem_complSpSiegel hs
      have h1 := Subgroup.mem_centralizer_iff.1 hdC
        ((e s : complSp F 0) : StatedSp (m + 1) F) hS
      apply e.injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hx0eq]
      exact h1
    have ht'one : t' = 1 := diagSp_eq_one_of_mem_centralizer_spSiegel hq hq2 ht'pow hdcent'
    have hupd : Function.update t 0 1 = 1 := by
      rw [← h0ins, ht']
      funext i
      rcases Fin.eq_self_or_eq_succAbove (0 : Fin (m + 1)) i with rfl | ⟨j, rfl⟩
      · simp
      · rw [Fin.insertNth_apply_succAbove]
        have htj : t' j = t (Fin.succAbove (0 : Fin (m + 1)) j) := congrFun ht' j
        rw [← htj]
        exact congrFun ht'one j
    have hb' : diagSp F (m + 1) t = rootTorusHom F (m + 1) 0 (t 0) := by
      rw [diagSp_eq_rootTorusHom_mul_update, hupd, map_one, mul_one]
    rw [hb']
    obtain ⟨k, hk⟩ := exists_zpow_of_mem_symplecticQTorus hq hdvd hζ (hpow 0)
    rw [← hk, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers (rootTorusHom F (m + 1) 0 ζ)) k
  · refine le_inf ?_ ?_
    · refine Subgroup.zpowers_le.2 ?_
      refine (mem_symplecticQTorus (F := F) (ℓ := m + 1)).2
        ⟨Pi.mulSingle 0 ζ, ?_, rootTorusHom_apply ..⟩
      intro i
      by_cases hi : i = 0
      · subst hi
        rw [Pi.mulSingle_eq_same]
        exact (by rw [← hζ]; exact pow_orderOf_eq_one ζ)
      · rw [Pi.mulSingle_eq_of_ne hi]
        simp
    · refine Subgroup.zpowers_le.2 ?_
      refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
      exact (commute_of_mem_longRootSp2_of_mem_complSp
        (rootTorusSp_le_longRootSp2 0 (rootTorusHom_mem_rootTorusSp 0 ζ))
        (complSpSiegel_le_complSp hz)).eq.symm

theorem evenRank_le_pRank_symplecticQTorus_inf {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ Nat.card F - 1) (hm : 2 ≤ m) :
    m + 1 ≤ CFSG.Open.pRank q
      (symplecticQTorus (F := F) (ℓ := m + 1) q ⊓ complSp F (0 : Fin (m + 1))) + 2 := by
  set e := complSpEquiv (K := F) (0 : Fin (m + 1)) with he
  have hφinj : Function.Injective
      ((complSp F (0 : Fin (m + 1))).subtype.comp e.toMonoidHom) :=
    (complSp F (0 : Fin (m + 1))).subtype_injective.comp e.injective
  have hEelem : IsElemAbelian q
      ((symplecticQTorus (F := F) (ℓ := m) q).map
        ((complSp F (0 : Fin (m + 1))).subtype.comp e.toMonoidHom)) :=
    CFSG.SectionRank.isElemAbelian_map (isElemAbelian_symplecticQTorus (F := F) (ℓ := m) hq) _
  have hEcard : Nat.card ((symplecticQTorus (F := F) (ℓ := m) q).map
      ((complSp F (0 : Fin (m + 1))).subtype.comp e.toMonoidHom)) = q ^ m := by
    rw [Subgroup.card_map_of_injective hφinj,
      card_symplecticQTorus (F := F) (ℓ := m) hq hdvd]
  have hEle : (symplecticQTorus (F := F) (ℓ := m) q).map
      ((complSp F (0 : Fin (m + 1))).subtype.comp e.toMonoidHom) ≤
      symplecticQTorus (F := F) (ℓ := m + 1) q ⊓ complSp F (0 : Fin (m + 1)) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, (e y).2⟩
    obtain ⟨t, hpow, rfl⟩ := (mem_symplecticQTorus (F := F) (ℓ := m)).1 hy
    rw [MonoidHom.comp_apply]
    change ((e (diagSp F m t) : complSp F 0) : StatedSp (m + 1) F) ∈
      symplecticQTorus (F := F) (ℓ := m + 1) q
    rw [coe_complSpEquiv_diagSp]
    refine (mem_symplecticQTorus (F := F) (ℓ := m + 1)).2
      ⟨Fin.insertNth (0 : Fin (m + 1)) (1 : Fˣ) t, ?_, rfl⟩
    intro i
    rcases Fin.eq_self_or_eq_succAbove (0 : Fin (m + 1)) i with rfl | ⟨j, rfl⟩
    · simp
    · rw [Fin.insertNth_apply_succAbove]; exact hpow j
  have := CFSG.SectionRank.le_pRank hq.one_lt hEle hEelem hEcard
  omega

end Normalizer

end CFSG.LocalAnalysis.GLTheoremA.Y10F
