module

public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsRankFour

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Generic.DeltaClosure (OmegaConnected)
open scoped commutatorElement

section NAdj

variable {G : Type} [Group G]

@[expose] def NAdj (z : G) (J L : Subgroup G) : Prop :=
  ∀ x ∈ J, ∀ y ∈ L, ⁅x, y⁆ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G))

theorem NAdj.symm {z : G} {J L : Subgroup G} (h : NAdj z J L) : NAdj z L J := fun x hx y hy => by
  have := (oddCoreIn (Subgroup.centralizer ({z} : Set G))).inv_mem (h y hy x hx)
  rwa [commutatorElement_inv] at this

theorem NAdj.of_commutes {z : G} {J L : Subgroup G} (h : Commutes J L) : NAdj z J L :=
  fun x hx y hy => by
    rw [(commutatorElement_eq_one_iff_mul_comm).mpr (h x hx y hy)]
    exact one_mem _

theorem NAdj.mono {z : G} {J L J' L' : Subgroup G} (h : NAdj z J L) (hJ : J' ≤ J) (hL : L' ≤ L) :
    NAdj z J' L' := fun x hx y hy => h x (hJ hx) y (hL hy)

end NAdj

section Conj

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_centralizes_of_commutator_mem {z u : G} {A : Subgroup G} (hA : IsPGroup 2 A)
    (hAC : A ≤ Subgroup.centralizer ({z} : Set G)) (hu : u * u = 1)
    (huC : u ∈ Subgroup.centralizer ({z} : Set G))
    (hcomm : ∀ x ∈ A, ⁅x, u⁆ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G))) :
    ∃ n ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)),
      ∀ x ∈ A, x * (n * u * n⁻¹) = (n * u * n⁻¹) * x := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  obtain ⟨n, hn, hfix⟩ := exists_conj_fixed_of_isPGroup (A := A)
    (N := oddCoreIn (Subgroup.centralizer ({z} : Set G))) hA (odd_card_oddCoreIn _)
    (fun x hx m hm => conj_mem_oddCoreIn (hAC hx) hm) hu
    (fun m hm => conj_mem_oddCoreIn huC hm) (by
      intro x hx
      have h1 := (oddCoreIn (Subgroup.centralizer ({z} : Set G))).inv_mem (hcomm x hx)
      rw [commutatorElement_inv] at h1
      have e : u * (x * u * x⁻¹) = ⁅u, x⁆ := by
        simp only [commutatorElement_def, hu']
        group
      rw [e]
      exact h1)
  refine ⟨n, hn, fun x hx => ?_⟩
  have := hfix x hx
  exact mul_inv_eq_iff_eq_mul.mp this

theorem exists_conj_commute_of_nadj {z t u : G} {J L : Subgroup G} (hJL : NAdj z J L)
    (hJC : J ≤ Subgroup.centralizer ({z} : Set G)) (hLC : L ≤ Subgroup.centralizer ({z} : Set G))
    (htJ : t ∈ J) (huL : u ∈ L) (ht : t * t = 1) (hu : u * u = 1) :
    ∃ n ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)),
      t * (n * u * n⁻¹) = (n * u * n⁻¹) * t := by
  obtain ⟨n, hn, h⟩ := exists_conj_centralizes_of_commutator_mem
    (A := Subgroup.zpowers t) (isPGroup_zpowers_of_mul_self_eq_one ht)
    ((Subgroup.zpowers_le.mpr htJ).trans hJC) hu (hLC huL)
    (fun x hx => hJL x ((Subgroup.zpowers_le.mpr htJ) hx) u huL)
  exact ⟨n, hn, h t (Subgroup.mem_zpowers t)⟩

end Conj

section Equivariance

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_conjSub_eq (g : G) (X : Subgroup G) :
    oddCoreIn (conjSub g X) = conjSub g (oddCoreIn X) := by
  have key : ∀ (g : G) (X : Subgroup G), conjSub g (oddCoreIn X) ≤ oddCoreIn (conjSub g X) := by
    intro g X
    refine le_oddCoreIn_of_normalizes (conjSub_mono (oddCoreIn_le X)) ?_ ?_
    · intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro s
      have hy' : g⁻¹ * y * g ∈ X := mem_conjSub_iff.mp hy
      have e : g⁻¹ * (y * s * y⁻¹) * g = (g⁻¹ * y * g) * (g⁻¹ * s * g) * (g⁻¹ * y * g)⁻¹ := by
        group
      constructor
      · intro hs
        have hs' : g⁻¹ * s * g ∈ oddCoreIn X := mem_conjSub_iff.mp hs
        rw [mem_conjSub_iff, e]
        exact conj_mem_oddCoreIn hy' hs'
      · intro hs
        have hs' : g⁻¹ * (y * s * y⁻¹) * g ∈ oddCoreIn X := mem_conjSub_iff.mp hs
        rw [e] at hs'
        rw [mem_conjSub_iff]
        have e2 : g⁻¹ * s * g = (g⁻¹ * y * g)⁻¹ *
            ((g⁻¹ * y * g) * (g⁻¹ * s * g) * (g⁻¹ * y * g)⁻¹) * ((g⁻¹ * y * g)⁻¹)⁻¹ := by group
        rw [e2]
        exact conj_mem_oddCoreIn (X.inv_mem hy') hs'
    · rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact odd_card_oddCoreIn X
  refine le_antisymm ?_ (key g X)
  have h2 := conjSub_mono (n := g) (key g⁻¹ (conjSub g X))
  rw [conjSub_conjSub_inv, conjSub_inv_conjSub] at h2
  exact h2

omit [Finite G] in
theorem centralizer_singleton_conj_eq (g d : G) :
    Subgroup.centralizer ({g * d * g⁻¹} : Set G) =
      conjSub g (Subgroup.centralizer ({d} : Set G)) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, mem_conjSub_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have : x * (g * d * g⁻¹) * g = g * d * g⁻¹ * x * g := by rw [h]
    calc g⁻¹ * x * g * d = g⁻¹ * (x * (g * d * g⁻¹) * g) := by group
      _ = g⁻¹ * (g * d * g⁻¹ * x * g) := by rw [this]
      _ = d * (g⁻¹ * x * g) := by group
  · intro h
    have : g * (g⁻¹ * x * g * d) * g⁻¹ = g * (d * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
    calc x * (g * d * g⁻¹) = g * (g⁻¹ * x * g * d) * g⁻¹ := by group
      _ = g * (d * (g⁻¹ * x * g)) * g⁻¹ := this
      _ = g * d * g⁻¹ * x := by group

theorem involutionOddCore_conj (g d : G) :
    CFSG.Assembly.Dichotomy.involutionOddCore (g * d * g⁻¹) =
      conjSub g (CFSG.Assembly.Dichotomy.involutionOddCore d) := by
  rw [involutionOddCore_eq_oddCoreIn, involutionOddCore_eq_oddCoreIn, centralizer_singleton_conj_eq,
    oddCoreIn_conjSub_eq]

theorem deltaCore_conjSub (g : G) (D : Subgroup G) :
    deltaCore (conjSub g D) = conjSub g (deltaCore D) := by
  ext x
  rw [mem_deltaCore_iff, mem_conjSub_iff, mem_deltaCore_iff]
  constructor
  · intro h d hd hd1
    have := h (g * d * g⁻¹) (mem_conjSub_iff.mpr (by simpa [mul_assoc] using hd)) (by
      intro h1
      apply hd1
      have : g * d * g⁻¹ = 1 := h1
      calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group)
    rw [involutionOddCore_conj, mem_conjSub_iff] at this
    exact this
  · intro h d hd hd1
    have hd' : g⁻¹ * d * g ∈ D := mem_conjSub_iff.mp hd
    have := h (g⁻¹ * d * g) hd' (by
      intro h1
      apply hd1
      calc d = g * (g⁻¹ * d * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group)
    have e : d = g * (g⁻¹ * d * g) * g⁻¹ := by group
    rw [e, involutionOddCore_conj, mem_conjSub_iff]
    simpa [mul_assoc] using this

theorem uCore_conjSub (g : G) (F : Subgroup G) : uCore (conjSub g F) = conjSub g (uCore F) := by
  apply le_antisymm
  · refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
    have hf' : g⁻¹ * f * g ∈ F := mem_conjSub_iff.mp hf
    have e : f = g * (g⁻¹ * f * g) * g⁻¹ := by group
    rw [e, involutionOddCore_conj]
    refine conjSub_mono (involutionOddCore_le_uCore hf' ?_)
    intro h1
    apply hf1
    calc f = g * (g⁻¹ * f * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · show (uCore F).map (MulAut.conj g).toMonoidHom ≤ _
    rw [uCore, Subgroup.map_iSup]
    refine iSup_le fun f => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hf => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hf1 => ?_
    have hmem : g * f * g⁻¹ ∈ conjSub g F := mem_conjSub_iff.mpr (by simpa [mul_assoc] using hf)
    have hne : g * f * g⁻¹ ≠ 1 := by
      intro h1
      apply hf1
      calc f = g⁻¹ * (g * f * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have := involutionOddCore_le_uCore hmem hne
    rwa [involutionOddCore_conj] at this

omit [Finite G] in
theorem normalClosureIn_conjSub (g : G) (H L : Subgroup G) :
    normalClosureIn (conjSub g H) (conjSub g L) = conjSub g (normalClosureIn H L) := by
  apply le_antisymm
  · refine normalClosureIn_le fun h' hh' => ?_
    have hh : g⁻¹ * h' * g ∈ H := mem_conjSub_iff.mp hh'
    have e : h' = g * (g⁻¹ * h' * g) * g⁻¹ := by group
    show (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h').toMonoidHom ≤
      (normalClosureIn H L).map (MulAut.conj g).toMonoidHom
    rw [map_map_conj]
    have : h' * g = g * (g⁻¹ * h' * g) := by group
    rw [this, ← map_map_conj]
    exact Subgroup.map_mono (le_iSup₂_of_le (g⁻¹ * h' * g) hh le_rfl)
  · show (normalClosureIn H L).map (MulAut.conj g).toMonoidHom ≤ _
    unfold normalClosureIn
    rw [Subgroup.map_iSup]
    refine iSup_le fun h => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hh => ?_
    have hmem : g * h * g⁻¹ ∈ conjSub g H := mem_conjSub_iff.mpr (by simpa [mul_assoc] using hh)
    refine le_iSup₂_of_le (g * h * g⁻¹) hmem ?_
    show (L.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom ≤
      (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (g * h * g⁻¹)).toMonoidHom
    rw [map_map_conj, map_map_conj]
    have : g * h * g⁻¹ * g = g * h := by group
    rw [this]

theorem alphaCore_conjSub (g : G) (F : Subgroup G) :
    alphaCore (conjSub g F) = conjSub g (alphaCore F) := by
  unfold alphaCore
  rw [uCore_conjSub, deltaCore_conjSub]
  have hcomm : ⁅conjSub g (uCore F), conjSub g F⁆ = conjSub g ⁅uCore F, F⁆ := by
    show ⁅(uCore F).map (MulAut.conj g).toMonoidHom, F.map (MulAut.conj g).toMonoidHom⁆ =
      ⁅uCore F, F⁆.map (MulAut.conj g).toMonoidHom
    rw [Subgroup.map_commutator]
  rw [hcomm, ← normalClosureIn_conjSub]
  congr 1
  show _ = ((⁅uCore F, F⁆ ⊔ deltaCore F).map (MulAut.conj g).toMonoidHom)
  rw [Subgroup.map_sup]
  rfl

end Equivariance

section AlphaStep

variable {G : Type} [Group G] [Finite G] {A B : Subgroup G}

omit [Finite G] in
theorem closure_pair_conj (g u v : G) :
    Subgroup.closure ({g * u * g⁻¹, g * v * g⁻¹} : Set G) =
      conjSub g (Subgroup.closure ({u, v} : Set G)) := by
  show _ = (Subgroup.closure ({u, v} : Set G)).map (MulAut.conj g).toMonoidHom
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

theorem odd_card_alphaCore_of_rankThreeBalance (h : RankThreeBalance A) {F : Subgroup G}
    (hFA : F ≤ A) (hF4 : Nat.card F = 4) : Odd (Nat.card (alphaCore F)) := by
  obtain ⟨d, hdF, hd1⟩ := exists_ne_one_of_card_eq_two_pow (n := 2) (by norm_num)
    (show Nat.card F = 2 ^ 2 by rw [hF4]; norm_num)
  obtain ⟨hodd, -⟩ := deltaStar_isCompletion h.elem (by rw [h.card]) h.weak
  have hαW : alphaCore F ≤ deltaStarCompletion A :=
    (alphaCore_le_uCore (comm_of_mem_subgroup h hFA) hdF hd1).trans (uCore_le_completion hFA)
  exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le hαW)

theorem oddCoreIn_centralizer_le_normalizer_alphaCore (hA : RankThreeBalance A) {F : Subgroup G}
    (hFA : F ≤ A) (hF4 : Nat.card F = 4) {b : G} (hb : b ∈ A) :
    oddCoreIn (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (alphaCore F : Set G) := by
  set X := oddCoreIn (Subgroup.centralizer ({b} : Set G)) with hX
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hA.comm ha hb)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := fun a ha => normalizer_oddCoreIn _ (hAC ha)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two A X hA.elem (by rw [hA.card]; norm_num) hAX
    (Nat.coprime_two_left.mpr (odd_card_oddCoreIn _))
  conv_lhs => rw [← hgen]
  refine iSup₂_le fun F' hF' => ?_
  have hconst : alphaCore F' = alphaCore F :=
    alphaCore_eq_alphaCore hA hF'.1 (by rw [hF'.2]; norm_num) hFA hF4
  intro c hc
  have hcF : ∀ f ∈ F', c * f = f * c := fun f hf =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 f hf).symm
  have hcF' : ∀ f ∈ F', c⁻¹ * f = f * c⁻¹ := fun f hf => by
    have := hcF f hf
    calc c⁻¹ * f = c⁻¹ * (f * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * f) * c⁻¹ := by rw [this]
      _ = f * c⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [← hconst] at hy ⊢
    exact conj_mem_alphaCore hcF hy
  · rw [← hconst] at hy ⊢
    have := conj_mem_alphaCore hcF' hy
    simpa [mul_assoc] using this

theorem alphaCore_closure_pair_eq_of_conj (hB : RankThreeBalance B) {z t u x : G} (hz : z ∈ B)
    (ht : t ∈ B) (hu : x * u * x⁻¹ ∈ B) (hx : x ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)))
    (hzt : Nat.card (Subgroup.closure ({z, t} : Set G)) = 4)
    (hzu : Nat.card (Subgroup.closure ({z, u} : Set G)) = 4) :
    alphaCore (Subgroup.closure ({z, t} : Set G)) =
      alphaCore (Subgroup.closure ({z, u} : Set G)) := by
  have hxz : x * z * x⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (oddCoreIn_le _ hx)
    calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [this]
      _ = z := by group
  have hF₂ : Subgroup.closure ({z, x * u * x⁻¹} : Set G) =
      conjSub x (Subgroup.closure ({z, u} : Set G)) := by
    rw [← closure_pair_conj, hxz]
  have hF₂4 : Nat.card (Subgroup.closure ({z, x * u * x⁻¹} : Set G)) = 4 := by
    rw [hF₂, conjSub, Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact hzu
  have hF₁B : Subgroup.closure ({z, t} : Set G) ≤ B :=
    (Subgroup.closure_le _).mpr (by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl <;> assumption)
  have hF₂B : Subgroup.closure ({z, x * u * x⁻¹} : Set G) ≤ B :=
    (Subgroup.closure_le _).mpr (by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl <;> assumption)
  have hconst := alphaCore_eq_alphaCore hB hF₁B hzt hF₂B hF₂4
  have hxn : x⁻¹ ∈ Subgroup.normalizer (alphaCore (Subgroup.closure ({z, x * u * x⁻¹} : Set G)) :
      Set G) :=
    inv_mem (oddCoreIn_centralizer_le_normalizer_alphaCore hB hF₂B hF₂4 hz hx)
  have hback : Subgroup.closure ({z, u} : Set G) =
      conjSub x⁻¹ (Subgroup.closure ({z, x * u * x⁻¹} : Set G)) := by
    rw [hF₂, conjSub_inv_conjSub]
  rw [hconst, hback, alphaCore_conjSub, conjSub_eq_of_mem_normalizer hxn]

omit [Finite G] in
theorem mem_closure_pair_cases {x y g : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (hg : g ∈ Subgroup.closure ({x, y} : Set G)) : g = 1 ∨ g = x ∨ g = y ∨ g = x * y := by
  have c : y * x = x * y := hxy.symm
  have s1' : ∀ b, x * (x * b) = b := fun b => by rw [← mul_assoc, hx, one_mul]
  have c' : ∀ b, y * (x * b) = x * (y * b) := fun b => by rw [← mul_assoc, c, mul_assoc]
  have i1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have i2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  refine Subgroup.closure_induction
    (p := fun g _ => g = 1 ∨ g = x ∨ g = y ∨ g = x * y) ?_ ?_ ?_ ?_ hg
  · intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hu | hu <;> subst hu <;> simp
  · simp
  · rintro a b - - (ha | ha | ha | ha) (hb | hb | hb | hb) <;> subst ha <;> subst hb <;>
      simp [mul_assoc, hx, hy, s1', c, c']
  · rintro a - (ha | ha | ha | ha) <;> subst ha <;> simp [i1, i2, c]

theorem alphaCore_closure_pair_eq_of_conj_of_mem (hB : RankThreeBalance B) {z t u x : G}
    (hz : z ∈ B) (ht : t ∈ B) (hx : x ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)))
    (hz2 : z * z = 1) (ht2 : t * t = 1) (hzt : z * t = t * z) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hcard : Nat.card (Subgroup.closure ({z, t} : Set G)) = 4)
    (hu' : x * u * x⁻¹ ∈ Subgroup.closure ({z, t} : Set G)) :
    alphaCore (Subgroup.closure ({z, t} : Set G)) =
      alphaCore (Subgroup.closure ({z, u} : Set G)) := by
  have hxz : x * z * x⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (oddCoreIn_le _ hx)
    calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [this]
      _ = z := by group
  have hne1 : x * u * x⁻¹ ≠ 1 := by
    intro h
    apply hu1
    calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  have hnez : x * u * x⁻¹ ≠ z := by
    intro h
    apply huz
    calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
      _ = x⁻¹ * z * x := by rw [h]
      _ = z := by
        calc x⁻¹ * z * x = x⁻¹ * (x * z * x⁻¹) * x := by rw [hxz]
          _ = z := by group
  have hz' : z ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have ht' : t ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have hF₂ : Subgroup.closure ({z, x * u * x⁻¹} : Set G) = Subgroup.closure ({z, t} : Set G) := by
    rcases mem_closure_pair_cases hz2 ht2 hzt hu' with h | h | h | h
    · exact absurd h hne1
    · exact absurd h hnez
    · rw [h]
    · rw [h]
      have hz'' : z ∈ Subgroup.closure ({z, z * t} : Set G) := Subgroup.subset_closure (by simp)
      have hzt'' : z * t ∈ Subgroup.closure ({z, z * t} : Set G) :=
        Subgroup.subset_closure (by simp)
      apply le_antisymm
      · refine (Subgroup.closure_le _).mpr fun y hy => ?_
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with hy | hy
        · rw [hy]
          exact hz'
        · rw [hy]
          exact mul_mem hz' ht'
      · refine (Subgroup.closure_le _).mpr fun y hy => ?_
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with hy | hy
        · rw [hy]
          exact hz''
        · rw [hy]
          simpa using mul_mem (inv_mem hz'') hzt''
  have hF₁B : Subgroup.closure ({z, t} : Set G) ≤ B :=
    (Subgroup.closure_le _).mpr (by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl <;> assumption)
  have hxn : x⁻¹ ∈ Subgroup.normalizer (alphaCore (Subgroup.closure ({z, t} : Set G)) : Set G) :=
    inv_mem (oddCoreIn_centralizer_le_normalizer_alphaCore hB hF₁B hcard hz hx)
  have hF₂' : Subgroup.closure ({z, x * u * x⁻¹} : Set G) =
      conjSub x (Subgroup.closure ({z, u} : Set G)) := by
    rw [← closure_pair_conj, hxz]
  have hback : Subgroup.closure ({z, u} : Set G) =
      conjSub x⁻¹ (Subgroup.closure ({z, t} : Set G)) := by
    rw [← hF₂, hF₂', conjSub_inv_conjSub]
  rw [hback, alphaCore_conjSub, conjSub_eq_of_mem_normalizer hxn]

theorem alphaCore_eq_of_nadj {z t u : G} {J L : Subgroup G} (hJL : NAdj z J L)
    (hJC : J ≤ Subgroup.centralizer ({z} : Set G)) (hLC : L ≤ Subgroup.centralizer ({z} : Set G))
    (htJ : t ∈ J) (huL : u ∈ L) (hz2 : z * z = 1) (ht2 : t * t = 1) (hu2 : u * u = 1)
    (hz1 : z ≠ 1) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htz : t ≠ z) (huz : u ≠ z)
    (hB : ∀ x ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)),
      t * (x * u * x⁻¹) = (x * u * x⁻¹) * t →
        (x * u * x⁻¹ ∉ Subgroup.closure ({z, t} : Set G) →
          RankThreeBalance (Subgroup.closure ({z, t, x * u * x⁻¹} : Set G))) ∧
        (x * u * x⁻¹ ∈ Subgroup.closure ({z, t} : Set G) →
          ∃ B : Subgroup G, RankThreeBalance B ∧ z ∈ B ∧ t ∈ B)) :
    alphaCore (Subgroup.closure ({z, t} : Set G)) =
      alphaCore (Subgroup.closure ({z, u} : Set G)) := by
  obtain ⟨x, hx, hcomm⟩ := exists_conj_commute_of_nadj hJL hJC hLC htJ huL ht2 hu2
  have hzt : z * t = t * z := (Subgroup.mem_centralizer_singleton_iff.mp (hJC htJ)).symm
  have hzu : z * u = u * z := (Subgroup.mem_centralizer_singleton_iff.mp (hLC huL)).symm
  have hcardt : Nat.card (Subgroup.closure ({z, t} : Set G)) = 4 :=
    card_closure_pair_eq_four hz2 ht2 hz1 ht1 htz.symm hzt
  have hcardu : Nat.card (Subgroup.closure ({z, u} : Set G)) = 4 :=
    card_closure_pair_eq_four hz2 hu2 hz1 hu1 huz.symm hzu
  by_cases hdeg : x * u * x⁻¹ ∈ Subgroup.closure ({z, t} : Set G)
  · obtain ⟨B, hBb, hzB, htB⟩ := ((hB x hx hcomm).2 hdeg)
    exact alphaCore_closure_pair_eq_of_conj_of_mem hBb hzB htB hx hz2 ht2 hzt hu1 huz hcardt hdeg
  · have hbal := (hB x hx hcomm).1 hdeg
    exact alphaCore_closure_pair_eq_of_conj hbal
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)) hx hcardt hcardu

end AlphaStep

section Propagation

variable {G : Type} [Group G] [Finite G]

theorem alphaCore_eq_bot_of_local_constancy {V : Type} (inv : V → G) (act : G → V → V)
    (E : V → V → Prop) (hO : CFSG.Open.componentClassificationOddCore G = ⊥)
    (hinv : ∀ g v, inv (act g v) = g * inv v * g⁻¹)
    (hEsymm : ∀ v w, E v w → E w v) (hEact : ∀ g v w, E v w → E (act g v) (act g w))
    (hconn : ∀ v w, Relation.ReflTransGen E v w)
    (hloc : ∀ u v w, E u v → E u w →
      alphaCore (Subgroup.closure ({inv u, inv v} : Set G)) =
        alphaCore (Subgroup.closure ({inv u, inv w} : Set G)))
    (hodd : ∀ v w, E v w → Odd (Nat.card (alphaCore (Subgroup.closure ({inv v, inv w} : Set G))))) :
    ∀ v w, E v w → alphaCore (Subgroup.closure ({inv v, inv w} : Set G)) = ⊥ := by
  intro v₀ w₀ h₀
  set lab : V → V → Subgroup G := fun v w => alphaCore (Subgroup.closure ({inv v, inv w} : Set G))
    with hlab
  have hsymm : ∀ v w, lab v w = lab w v := fun v w => by simp only [hlab, Set.pair_comm]
  set Y := lab v₀ w₀ with hY
  have hall : ∀ v, Relation.ReflTransGen E v₀ v → ∀ w, E v w → lab v w = Y := by
    intro v hv
    induction hv with
    | refl => exact fun w hw => hloc v₀ w w₀ hw h₀
    | @tail b c _ hstep ih =>
      intro w hw
      calc lab c w = lab c b := hloc c w b hw (hEsymm b c hstep)
        _ = lab b c := hsymm c b
        _ = Y := ih c hstep
  have hedge : ∀ v w, E v w → lab v w = Y := fun v w hvw => hall v (hconn v₀ v) w hvw
  have hconj : ∀ g, conjSub g Y = Y := by
    intro g
    have e1 := hedge (act g v₀) (act g w₀) (hEact g v₀ w₀ h₀)
    have e2 : lab (act g v₀) (act g w₀) = conjSub g Y := by
      simp only [hlab, hinv, closure_pair_conj, alphaCore_conjSub, hY]
    rw [← e2, e1]
  have hN : Y.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ ∈ conjSub g Y := conj_mem_conjSub hn
    rwa [hconj g] at this⟩
  have hle := CFSG.ComponentClassification.OddCore.maximal G Y hN (hodd v₀ w₀ h₀)
  rw [hO] at hle
  have hYbot : Y = ⊥ := le_bot_iff.mp hle
  exact hYbot

omit [Finite G] in
theorem OmegaConnected.mono {Ω : Set (Subgroup G)} (h : OmegaConnected Ω)
    {E : Subgroup G → Subgroup G → Prop} (hE : ∀ M N, Commutes M N → E M N) :
    ∀ L ∈ Ω, ∀ L' ∈ Ω, Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ E M N) L L' :=
  fun L hL L' hL' => Relation.ReflTransGen.mono
    (fun (_ N : Subgroup G) (hMN : N ∈ Ω ∧ Commutes _ N) => ⟨hMN.1, hE _ _ hMN.2⟩) L L'
    (h L hL L' hL')

end Propagation

end CFSG.ClassicalInvolution.Balance.Bootstrap
