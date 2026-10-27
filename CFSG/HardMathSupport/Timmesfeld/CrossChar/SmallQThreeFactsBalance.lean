module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThree

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Balance

section Transport

variable {G M : Type*} [Group G] [Group M]

theorem gLAPPrimeCoreOf_map_of_injective (p : ℕ) (f : G →* M) (hf : Function.Injective f)
    (S : Subgroup G) : GLAPPrimeCoreOf p (S.map f) = (GLAPPrimeCoreOf p S).map f := by
  have hp := CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCore_map_iso p (S.equivMapOfInjective f hf)
  have hcomp : (S.map f).subtype.comp (S.equivMapOfInjective f hf).toMonoidHom =
      f.comp S.subtype := by
    ext t
    rfl
  calc GLAPPrimeCoreOf p (S.map f)
      = ((GLAPPrimeCore p ↥S).map (S.equivMapOfInjective f hf).toMonoidHom).map
          (S.map f).subtype := by
        rw [hp]; rfl
    _ = (GLAPPrimeCore p ↥S).map ((S.map f).subtype.comp
        (S.equivMapOfInjective f hf).toMonoidHom) := Subgroup.map_map _ _ _
    _ = (GLAPPrimeCore p ↥S).map (f.comp S.subtype) := by rw [hcomp]
    _ = (GLAPPrimeCoreOf p S).map f := (Subgroup.map_map _ _ _).symm

theorem eq_bot_of_map_eq_bot {f : G →* M} (hf : Function.Injective f) {S : Subgroup G}
    (h : S.map f = ⊥) : S = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have : f x ∈ S.map f := Subgroup.mem_map_of_mem f hx
  rw [h, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact hf (this.trans f.map_one.symm)

end Transport

section Conj

variable {K : Type*} [Group K]

theorem map_conj_eq_of_mem {M : Type*} [Group M] {H : Subgroup M} {g : M} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
  · intro hy
    refine ⟨g⁻¹ * y * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hy) hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem map_conj_centralizer {M : Type*} [Group M] (g d : M) :
    (Subgroup.centralizer ({d} : Set M)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * d * g⁻¹} : Set M) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  simp only [MulAut.conj_symm_apply]
  constructor
  · intro h
    calc y * (g * d * g⁻¹) = g * ((g⁻¹ * y * g) * d) * g⁻¹ := by group
      _ = g * (d * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * d * g⁻¹ * y := by group
  · intro h
    calc g⁻¹ * y * g * d = g⁻¹ * (y * (g * d * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * d * g⁻¹ * y) * g := by rw [h]
      _ = d * (g⁻¹ * y * g) := by group

theorem gLAPPrimeCoreOf_inf_centralizer_conj_iff {H : Subgroup (MulAut K)}
    (hH : innerAut K ≤ H) (c s : K) :
    GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer {MulAut.conj (c * s * c⁻¹)}) = ⊥ ↔
      GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer {MulAut.conj s}) = ⊥ := by
  set γ := MulAut.conj c with hγ
  have hγH : γ ∈ H := hH ⟨c, rfl⟩
  have e1 : (H ⊓ Subgroup.centralizer {MulAut.conj s}).map (MulAut.conj γ).toMonoidHom =
      H ⊓ Subgroup.centralizer {MulAut.conj (c * s * c⁻¹)} := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj γ).injective, map_conj_eq_of_mem hγH,
      map_conj_centralizer]
    congr 3
    rw [map_mul, map_mul, map_inv]
  rw [← e1, gLAPPrimeCoreOf_map_of_injective 3 _ (MulAut.conj γ).injective]
  constructor
  · exact eq_bot_of_map_eq_bot (MulAut.conj γ).injective
  · intro h
    rw [h, Subgroup.map_bot]

end Conj

section Balance

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
theorem inner_inf_centralizer_conj (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (t : K) : innerAut K ⊓ Subgroup.centralizer {MulAut.conj t} =
      (Subgroup.centralizer {t}).map (MulAut.conj : K →* MulAut K) := by
  ext φ
  rw [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨y, rfl⟩, h⟩
    refine ⟨y, Subgroup.mem_centralizer_singleton_iff.2 (hinj ?_), rfl⟩
    rw [map_mul, map_mul]
    exact h
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hy]

theorem gLAPPrimeCoreOf_inf_centralizer_conj_eq_bot
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {t : K}
    (hin : GLAPPrimeCoreOf 3 (Subgroup.centralizer {t}) = ⊥)
    (hrig : ∀ α : MulAut K, (∀ y ∈ Subgroup.centralizer {t}, α y = y) → α ∈ innerAut K)
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H) :
    GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer {MulAut.conj t}) = ⊥ := by
  have : Finite (MulAut K) :=
    Finite.of_injective (fun φ : MulAut K => (φ : K → K)) DFunLike.coe_injective
  set C := H ⊓ Subgroup.centralizer {MulAut.conj t} with hC
  set O := GLAPPrimeCoreOf 3 C with hO
  set CI := innerAut K ⊓ Subgroup.centralizer {MulAut.conj t} with hCI
  have hCI0 : GLAPPrimeCoreOf 3 CI = ⊥ := by
    rw [hCI, inner_inf_centralizer_conj hinj, gLAPPrimeCoreOf_map_of_injective 3 _ hinj, hin,
      Subgroup.map_bot]
  have hCIC : CI ≤ C := inf_le_inf_right _ hH
  have hOI : ∀ φ ∈ O, φ ∈ innerAut K → φ = 1 := by
    intro φ hφ hφI
    have hle : O ⊓ innerAut K ≤ GLAPPrimeCoreOf 3 CI := by
      refine le_gLAPPrimeCoreOf_of_normal' ?_ ?_ ?_
      · intro x hx
        exact ⟨hx.2, (Subgroup.mem_inf.1 (gLAPPrimeCoreOf_le_self' C hx.1)).2⟩
      · intro g hg x hx
        refine ⟨gLAPPrimeCoreOf_conj_mem' g (hCIC hg) x hx.1, ?_⟩
        exact (innerAut K).mul_mem ((innerAut K).mul_mem (Subgroup.mem_inf.1 hg).1 hx.2)
          ((innerAut K).inv_mem (Subgroup.mem_inf.1 hg).1)
      · exact (coprime_card_gLAPPrimeCoreOf' Nat.prime_three C).coprime_dvd_right
          (Subgroup.card_dvd_of_le inf_le_left)
    have := hle ⟨hφ, hφI⟩
    rw [hCI0, Subgroup.mem_bot] at this
    exact this
  refine eq_bot_iff.2 fun α hα => ?_
  rw [Subgroup.mem_bot]
  have hfix : ∀ y ∈ Subgroup.centralizer {t}, α y = y := by
    intro y hy
    have hyCI : MulAut.conj y ∈ CI := by
      rw [hCI, inner_inf_centralizer_conj hinj]
      exact ⟨y, hy, rfl⟩
    have h1 : α * MulAut.conj y * α⁻¹ * (MulAut.conj y)⁻¹ ∈ O := by
      have h2 : MulAut.conj y * α⁻¹ * (MulAut.conj y)⁻¹ ∈ O :=
        gLAPPrimeCoreOf_conj_mem' _ (hCIC hyCI) _ (O.inv_mem hα)
      have := O.mul_mem hα h2
      simpa [mul_assoc] using this
    have h3 : α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
      ext z
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
    have h4 : α * MulAut.conj y * α⁻¹ * (MulAut.conj y)⁻¹ ∈ innerAut K := by
      rw [h3]
      exact (innerAut K).mul_mem ⟨α y, rfl⟩ ((innerAut K).inv_mem ⟨y, rfl⟩)
    have h5 := hOI _ h1 h4
    rw [mul_inv_eq_one, h3] at h5
    exact hinj h5
  exact hOI α hα (hrig α hfix)

theorem innerOneBalanceThree_of_toral
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) (T : Set K)
    (hfus : ∀ s : K, s ^ 3 = 1 → s ≠ 1 → ∃ c, c * s * c⁻¹ ∈ T)
    (hin : ∀ t ∈ T, GLAPPrimeCoreOf 3 (Subgroup.centralizer {t}) = ⊥)
    (hrig : ∀ t ∈ T, ∀ α : MulAut K, (∀ y ∈ Subgroup.centralizer {t}, α y = y) →
      α ∈ innerAut K) :
    InnerOneBalanceThree K := by
  intro d hd hd3 hd1 H hH
  obtain ⟨s, rfl⟩ := hd
  have hs3 : s ^ 3 = 1 := hinj (by rw [map_pow, hd3, map_one])
  have hs1 : s ≠ 1 := fun h => hd1 (by rw [h, map_one])
  obtain ⟨c, hc⟩ := hfus s hs3 hs1
  rw [← gLAPPrimeCoreOf_inf_centralizer_conj_iff hH c s]
  exact gLAPPrimeCoreOf_inf_centralizer_conj_eq_bot hinj (hin _ hc) (hrig _ hc) hH

end Balance

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
