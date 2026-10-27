module

public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs
public import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

variable {G : Type*} [Group G]

theorem gLBConj_eq_comap (g : G) (H : Subgroup G) :
    GLBConj g H = H.comap (MulAut.conj g).toMonoidHom := by
  ext y
  rw [mem_gLBConj, Subgroup.mem_comap]
  rfl

theorem gLBConj_gLBConj_inv (g : G) (H : Subgroup G) : GLBConj g (GLBConj g⁻¹ H) = H := by
  rw [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one]

theorem gLBConj_inv_gLBConj (g : G) (H : Subgroup G) : GLBConj g⁻¹ (GLBConj g H) = H := by
  rw [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one]

theorem gLBConj_eq_bot_iff (g : G) (H : Subgroup G) : GLBConj g H = ⊥ ↔ H = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective H (MulAut.conj g⁻¹).injective

theorem gLBConj_eq_of_forall_le {F : Subgroup G → Subgroup G}
    (h : ∀ (g : G) (H : Subgroup G), F (GLBConj g H) ≤ GLBConj g (F H)) (g : G)
    (H : Subgroup G) : F (GLBConj g H) = GLBConj g (F H) := by
  refine le_antisymm (h g H) ?_
  have h1 := h g⁻¹ (GLBConj g H)
  rw [gLBConj_inv_gLBConj] at h1
  have h2 := gLBConj_mono g h1
  rwa [gLBConj_gLBConj_inv] at h2

theorem mem_normalizer_iff_gLBConj_eq {g : G} {H : Subgroup G} :
    g ∈ Subgroup.normalizer (H : Set G) ↔ GLBConj g H = H := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    ext y
    rw [mem_gLBConj]
    exact (h y).symm
  · intro h y
    rw [← mem_gLBConj, h]

@[expose] def conjEquiv (g : G) (T : Subgroup G) : ↥T ≃* ↥(GLBConj g T) where
  toFun t := ⟨g⁻¹ * t * g, mem_gLBConj.2 (by simp [mul_assoc])⟩
  invFun x := ⟨g * x * g⁻¹, mem_gLBConj.1 x.2⟩
  left_inv t := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[simp] theorem coe_conjEquiv (g : G) (T : Subgroup G) (t : ↥T) :
    ((conjEquiv g T t : ↥(GLBConj g T)) : G) = g⁻¹ * t * g := rfl

@[simp] theorem coe_conjEquiv_symm (g : G) (T : Subgroup G) (x : ↥(GLBConj g T)) :
    (((conjEquiv g T).symm x : ↥T) : G) = g * x * g⁻¹ := rfl

theorem pCoreOf_gLBConj (r : ℕ) (g : G) (H : Subgroup G) :
    pCoreOf r (GLBConj g H) = GLBConj g (pCoreOf r H) := by
  have hp := CFSG.LieType.BorelTits.map_pCore_mulEquiv r (conjEquiv g H)
  have hf : (GLBConj g H).subtype.comp (conjEquiv g H).toMonoidHom =
      (MulAut.conj g⁻¹).toMonoidHom.comp H.subtype := by
    ext t
    simp
  calc pCoreOf r (GLBConj g H)
      = ((CFSG.Open.pCore r ↥H).map (conjEquiv g H).toMonoidHom).map (GLBConj g H).subtype := by
        rw [hp]; rfl
    _ = (CFSG.Open.pCore r ↥H).map ((GLBConj g H).subtype.comp (conjEquiv g H).toMonoidHom) :=
        Subgroup.map_map _ _ _
    _ = (CFSG.Open.pCore r ↥H).map ((MulAut.conj g⁻¹).toMonoidHom.comp H.subtype) := by rw [hf]
    _ = ((CFSG.Open.pCore r ↥H).map H.subtype).map (MulAut.conj g⁻¹).toMonoidHom :=
        (Subgroup.map_map _ _ _).symm
    _ = GLBConj g (pCoreOf r H) := rfl

theorem normalizer_gLBConj (g : G) (H : Subgroup G) :
    Subgroup.normalizer ((GLBConj g H : Subgroup G) : Set G) =
      GLBConj g (Subgroup.normalizer (H : Set G)) :=
  (Subgroup.map_equiv_normalizer_eq H (MulAut.conj g⁻¹)).symm

theorem centralizer_singleton_gLBConj (g d : G) :
    Subgroup.centralizer ({g⁻¹ * d * g} : Set G) =
      GLBConj g (Subgroup.centralizer ({d} : Set G)) := by
  ext x
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x * g⁻¹ * d = g * (x * (g⁻¹ * d * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * d * g) * x) * g⁻¹ := by rw [h]
      _ = d * (g * x * g⁻¹) := by group
  · intro h
    calc x * (g⁻¹ * d * g) = g⁻¹ * ((g * x * g⁻¹) * d) * g := by group
      _ = g⁻¹ * (d * (g * x * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * d * g * x := by group

theorem IsCharIn.gLBConj {T₀ T : Subgroup G} (h : IsCharIn T₀ T) (g : G) :
    IsCharIn (GLBConj g T₀) (GLBConj g T) := by
  refine ⟨gLBConj_mono g h.1, fun ψ x hx => ?_⟩
  have hx0 : (((conjEquiv g T).symm x : ↥T) : G) ∈ T₀ := mem_gLBConj.1 hx
  have h1 := h.2 ((conjEquiv g T).trans (ψ.trans (conjEquiv g T).symm))
    ((conjEquiv g T).symm x) hx0
  rw [mem_gLBConj]
  simpa using h1

theorem IsCharIn.normalizer_le {T₀ T : Subgroup G} (h : IsCharIn T₀ T) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (T₀ : Set G) := by
  have key : ∀ n ∈ Subgroup.normalizer (T : Set G), ∀ t ∈ T₀, n * t * n⁻¹ ∈ T₀ := by
    intro n hn t ht
    have := h.2 (T.normalizerMonoidHom ⟨n, hn⟩) ⟨t, h.1 ht⟩ ht
    simpa using this
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨key n hn t, fun htn => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ htn
  simpa [mul_assoc] using this

theorem mem_gammaOne {T : Subgroup G} {x : G} :
    x ∈ gammaOne T ↔ x ∈ T ∧ ∀ T₀ : Subgroup G, T₀ ≠ ⊥ → IsCharIn T₀ T →
      x ∈ pCoreOf 2 (Subgroup.normalizer (T₀ : Set G)) := by
  unfold gammaOne
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun T₀ h1 h2 => h T₀ ⟨h1, h2⟩⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun T₀ ⟨h1, h2⟩ => h T₀ h1 h2⟩

theorem gammaOne_le (T : Subgroup G) : gammaOne T ≤ T := inf_le_left

theorem gammaOne_le_pCoreOf_normalizer {T T₀ : Subgroup G} (h0 : T₀ ≠ ⊥) (h : IsCharIn T₀ T) :
    gammaOne T ≤ pCoreOf 2 (Subgroup.normalizer (T₀ : Set G)) :=
  fun _ hx => (mem_gammaOne.1 hx).2 T₀ h0 h

theorem gammaOne_gLBConj_le (g : G) (T : Subgroup G) :
    gammaOne (GLBConj g T) ≤ GLBConj g (gammaOne T) := by
  intro y hy
  rw [mem_gammaOne] at hy
  rw [mem_gLBConj, mem_gammaOne]
  refine ⟨mem_gLBConj.1 hy.1, fun T₁ h1 h2 => ?_⟩
  have h3 := hy.2 (GLBConj g T₁) (fun h => h1 ((gLBConj_eq_bot_iff g T₁).1 h)) (h2.gLBConj g)
  rw [normalizer_gLBConj, pCoreOf_gLBConj, mem_gLBConj] at h3
  exact h3

theorem gammaOne_gLBConj (g : G) (T : Subgroup G) :
    gammaOne (GLBConj g T) = GLBConj g (gammaOne T) :=
  gLBConj_eq_of_forall_le (F := gammaOne) gammaOne_gLBConj_le g T

theorem gammaIter_gLBConj (g : G) (T : Subgroup G) (n : ℕ) :
    gammaIter (GLBConj g T) n = GLBConj g (gammaIter T n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gammaIter, gammaIter, ih, gammaOne_gLBConj]

theorem gammaInf_gLBConj (g : G) (T : Subgroup G) :
    gammaInf (GLBConj g T) = GLBConj g (gammaInf T) := by
  unfold gammaInf
  simp only [gammaIter_gLBConj]
  rw [gLBConj_eq_comap, Subgroup.comap_iInf]
  exact iInf_congr fun n => gLBConj_eq_comap g _

theorem normalizer_le_normalizer_gammaOne (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (gammaOne T : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_gLBConj_eq] at hn ⊢
  rw [← gammaOne_gLBConj, hn]

theorem normalizer_le_normalizer_gammaInf (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (gammaInf T : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_gLBConj_eq] at hn ⊢
  rw [← gammaInf_gLBConj, hn]

theorem gammaIter_succ_le (T : Subgroup G) (n : ℕ) : gammaIter T (n + 1) ≤ gammaIter T n :=
  gammaOne_le _

theorem gammaIter_antitone (T : Subgroup G) : Antitone (gammaIter T) :=
  antitone_nat_of_succ_le (gammaIter_succ_le T)

theorem gammaInf_le_gammaOne (T : Subgroup G) : gammaInf T ≤ gammaOne T :=
  iInf_le (fun n => gammaIter T (n + 1)) 0

theorem gammaInf_le (T : Subgroup G) : gammaInf T ≤ T :=
  (gammaInf_le_gammaOne T).trans (gammaOne_le T)

theorem exists_gammaIter_stable [Finite G] (T : Subgroup G) :
    ∃ m : ℕ, ∀ k, m ≤ k → gammaIter T k = gammaIter T m := by
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite (gammaIter T)
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm heq.symm (lt_of_le_of_ne (not_lt.1 hlt) hab.symm)
  have hstep : gammaIter T (a + 1) = gammaIter T a := by
    refine le_antisymm (gammaIter_succ_le T a) ?_
    calc gammaIter T a = gammaIter T b := heq
      _ ≤ gammaIter T (a + 1) := gammaIter_antitone T hlt
  refine ⟨a, fun k hk => ?_⟩
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [gammaIter, ih, ← gammaIter, hstep]

theorem exists_gammaInf_eq_gammaIter [Finite G] (T : Subgroup G) :
    ∃ m : ℕ, gammaInf T = gammaIter T m ∧ gammaOne (gammaInf T) = gammaInf T := by
  obtain ⟨m, hm⟩ := exists_gammaIter_stable T
  have h : gammaInf T = gammaIter T m := by
    refine le_antisymm ?_ (le_iInf fun n => ?_)
    · have := iInf_le (fun n => gammaIter T (n + 1)) m
      rwa [hm (m + 1) (Nat.le_succ m)] at this
    · rcases le_total m (n + 1) with h | h
      · rw [hm (n + 1) h]
      · exact gammaIter_antitone T h
  refine ⟨m, h, ?_⟩
  rw [h, ← gammaIter, hm (m + 1) (Nat.le_succ m)]

theorem gammaOne_gammaInf [Finite G] (T : Subgroup G) : gammaOne (gammaInf T) = gammaInf T :=
  (exists_gammaInf_eq_gammaIter T).choose_spec.2

theorem sigmaStar_gLBConj (g : G) (D : Subgroup G) :
    sigmaStar (GLBConj g D) = GLBConj g (sigmaStar D) := by
  refine gLBConj_eq_of_forall_le (F := sigmaStar) (fun g D => ?_) g D
  refine iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => ?_
  have hd' : g * d * g⁻¹ ∈ D := mem_gLBConj.1 hd
  have hd'1 : g * d * g⁻¹ ≠ 1 := fun h => hd1 (by simpa [mul_assoc] using congrArg (g⁻¹ * · * g) h)
  have hle : pCoreOf 2 (Subgroup.centralizer ({g * d * g⁻¹} : Set G)) ≤ sigmaStar D :=
    le_iSup_of_le (g * d * g⁻¹) (le_iSup_of_le hd' (le_iSup_of_le hd'1 le_rfl))
  have hc := centralizer_singleton_gLBConj g (g * d * g⁻¹)
  rw [show g⁻¹ * (g * d * g⁻¹) * g = d by group] at hc
  rw [hc, pCoreOf_gLBConj]
  exact gLBConj_mono g hle

theorem sigmaOf_gLBConj (g : G) (D : Subgroup G) :
    sigmaOf (GLBConj g D) = GLBConj g (sigmaOf D) := by
  rw [sigmaOf, sigmaOf, sigmaStar_gLBConj, pCoreOf_gLBConj]

theorem gammaD_gLBConj (g : G) (D : Subgroup G) :
    gammaD (GLBConj g D) = GLBConj g (gammaD D) := by
  rw [gammaD, gammaD, sigmaOf_gLBConj, gammaInf_gLBConj]

theorem normalizer_le_normalizer_gammaD (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (gammaD D : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_gLBConj_eq] at hn ⊢
  rw [← gammaD_gLBConj, hn]

theorem gammaD_le_sigmaOf (D : Subgroup G) : gammaD D ≤ sigmaOf D :=
  gammaInf_le _

theorem sigmaOf_le_sigmaStar (D : Subgroup G) : sigmaOf D ≤ sigmaStar D :=
  CFSG.LieType.BorelTits.pCoreOf_le 2 _

theorem gammaD_le_sigmaStar (D : Subgroup G) : gammaD D ≤ sigmaStar D :=
  (gammaD_le_sigmaOf D).trans (sigmaOf_le_sigmaStar D)

theorem isPGroup_gammaD [Finite G] (D : Subgroup G) : IsPGroup 2 (gammaD D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (sigmaStar D)).to_le (gammaD_le_sigmaOf D)

theorem sigmaStar_le_normalizer_sigmaOf (D : Subgroup G) :
    sigmaStar D ≤ Subgroup.normalizer (sigmaOf D : Set G) := by
  have : (CFSG.Open.pCore 2 ↥(sigmaStar D)).Characteristic :=
    CFSG.LieType.BorelTits.pCore_characteristic 2
  exact Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.Open.pCore 2 ↥(sigmaStar D)))

theorem sigmaStar_le_normalizer_gammaD (D : Subgroup G) :
    sigmaStar D ≤ Subgroup.normalizer (gammaD D : Set G) :=
  (sigmaStar_le_normalizer_sigmaOf D).trans (normalizer_le_normalizer_gammaInf _)

theorem gammaD_le_pCoreOf_normalizer_of_isCharIn_gammaD [Finite G] {D T₀ : Subgroup G}
    (h0 : T₀ ≠ ⊥) (h : IsCharIn T₀ (gammaD D)) :
    gammaD D ≤ pCoreOf 2 (Subgroup.normalizer (T₀ : Set G)) := by
  have := gammaOne_le_pCoreOf_normalizer h0 h
  rwa [gammaD, gammaOne_gammaInf] at this

theorem gammaD_le_pCoreOf_normalizer_of_isCharIn_sigmaOf {D T₀ : Subgroup G}
    (h0 : T₀ ≠ ⊥) (h : IsCharIn T₀ (sigmaOf D)) :
    gammaD D ≤ pCoreOf 2 (Subgroup.normalizer (T₀ : Set G)) :=
  (gammaInf_le_gammaOne _).trans (gammaOne_le_pCoreOf_normalizer h0 h)

end CFSG.LocalAnalysis.GLTheoremB
