module

public import CFSG.LieType.Steinberg.CoreTorus
import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.LieType.Steinberg

namespace RootGroupData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι} {K : Type*} [Group K]
variable (D : RootGroupData Φ K)

@[expose] def stBorel : Subgroup (StGroup Φ D.X) := D.stTorusPart ⊔ D.stSub Φ.pos

@[expose] def bruhatSet : Set (StGroup Φ D.X) :=
  {g | ∃ w : List ι, ∃ b₁ ∈ D.stBorel, ∃ b₂ ∈ D.stBorel, g = b₁ * D.stnw w * b₂}

theorem stTorusPart_le_stBorel : D.stTorusPart ≤ D.stBorel := le_sup_left

theorem stPos_le_stBorel : D.stSub Φ.pos ≤ D.stBorel := le_sup_right

theorem one_mem_bruhatSet : (1 : StGroup Φ D.X) ∈ D.bruhatSet :=
  ⟨[], 1, one_mem _, 1, one_mem _, by simp⟩

theorem surjective_stPi (hgen : ⨆ γ ∈ Φ.roots, D.X γ = ⊤) :
    Function.Surjective (stPi Φ D.X) := by
  rw [← MonoidHom.range_eq_top, MonoidHom.range_eq_map, ← D.stSub_roots,
    D.map_stSub subset_rfl, hgen]

variable {D}

namespace IsSteinberg

variable (hD : D.IsSteinberg)
include hD

theorem stTorusPart_le_normalizer_stPos :
    D.stTorusPart ≤ Subgroup.normalizer (D.stSub Φ.pos : Set (StGroup Φ D.X)) :=
  le_normalizer_stSub_of_le fun _ hγ => hD.stTorusPart_le_normalizer hγ.1

theorem mem_stBorel_iff {g : StGroup Φ D.X} :
    g ∈ D.stBorel ↔ ∃ h ∈ D.stTorusPart, ∃ u ∈ D.stSub Φ.pos, h * u = g := by
  rw [← SetLike.mem_coe, stBorel,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hD.stTorusPart_le_normalizer_stPos,
    Set.mem_mul]
  rfl

theorem map_stBorel : D.stBorel.map (stPi Φ D.X) = D.torusPart ⊔ D.posPart := by
  rw [stBorel, Subgroup.map_sup, hD.map_stTorusPart, D.map_stSub fun _ hγ => hγ.1]
  rfl

theorem stPi_mem_of_mem_stBorel {b : StGroup Φ D.X} (hb : b ∈ D.stBorel) :
    stPi Φ D.X b ∈ D.torusPart ⊔ D.posPart := by
  rw [← hD.map_stBorel]
  exact Subgroup.mem_map_of_mem _ hb

theorem injOn_stBorel : Set.InjOn (stPi Φ D.X) D.stBorel := by
  refine injOn_of_eq_one fun g hg h1 => ?_
  obtain ⟨h, hh, u, hu, rfl⟩ := hD.mem_stBorel_iff.1 hg
  rw [map_mul] at h1
  have hhK : stPi Φ D.X h ∈ D.torusPart := by
    rw [← hD.map_stTorusPart]
    exact Subgroup.mem_map_of_mem _ hh
  have huK : stPi Φ D.X u ∈ D.posPart := by
    rw [posPart, ← D.map_stSub fun _ hγ => hγ.1]
    exact Subgroup.mem_map_of_mem _ hu
  have hmem : stPi Φ D.X h ∈ D.torusPart ⊓ D.posPart :=
    Subgroup.mem_inf.2 ⟨hhK, by rw [eq_inv_of_mul_eq_one_left h1]; exact D.posPart.inv_mem huK⟩
  rw [hD.torusPart_inf_posPart, Subgroup.mem_bot] at hmem
  rw [hmem, one_mul] at h1
  rw [hD.injOn_stTorusPart hh (one_mem _) (by rw [hmem, map_one]),
    hD.injOn_stSub_pos hu (one_mem _) (by rw [h1, map_one]), one_mul]

theorem stSub_pos_eq_sup (i : ι) :
    D.stSub Φ.pos = D.stRoot (Pi.single i 1) ⊔ D.stSub (Φ.posExcept i) := by
  apply le_antisymm
  · rw [stSub_eq_iSup]
    refine iSup₂_le fun γ hγ => ?_
    by_cases h1 : γ = Pi.single i 1
    · subst h1
      exact le_sup_left
    by_cases h2 : γ = 2 • Pi.single i 1
    · subst h2
      exact (hD.stRoot_two_smul_le (Φ.single_mem i) hγ.1).trans le_sup_left
    refine (D.stRoot_le_stSub (Ψ := Φ.posExcept i) ⟨hγ, ?_⟩).trans le_sup_right
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1, h2⟩
  · exact sup_le (D.stRoot_le_stSub (Φ.single_mem_pos i))
      (D.stSub_mono (Φ.posExcept_subset_pos i))

theorem exists_mul_eq_mul (i : ι) {b ℓ : StGroup Φ D.X} (hb : b ∈ D.stBorel)
    (hℓ : ℓ ∈ D.stRankOne i) : ∃ ℓ' ∈ D.stRankOne i, ∃ b' ∈ D.stBorel, b * ℓ = ℓ' * b' := by
  obtain ⟨h, hh, u, hu, rfl⟩ := hD.mem_stBorel_iff.1 hb
  rw [hD.stSub_pos_eq_sup i, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hD.stRoot_le_normalizer_posExcept (Or.inl rfl)), Set.mem_mul] at hu
  obtain ⟨x, hx, u', hu', rfl⟩ := hu
  have hu'' : ℓ⁻¹ * u' * ℓ ∈ D.stSub (Φ.posExcept i) := by
    have := (Subgroup.mem_normalizer_iff.1
      (hD.stRankOne_le_normalizer_posExcept i (inv_mem hℓ)) u').1 hu'
    rwa [inv_inv] at this
  refine ⟨h * (x * ℓ) * h⁻¹, ?_, h * (ℓ⁻¹ * u' * ℓ), ?_, by group⟩
  · rw [← mem_normalizer_iff_map_conj.1 (hD.stTorusPart_le_normalizer_stRankOne i hh)]
    exact conj_mem_map_conj (mul_mem (D.stRoot_single_le_stRankOne i hx) hℓ)
  · exact mul_mem (D.stTorusPart_le_stBorel hh)
      (D.stPos_le_stBorel (D.stSub_mono (Φ.posExcept_subset_pos i) hu''))

theorem stRankOne_bruhat (i : ι) {g : StGroup Φ D.X} (hg : g ∈ D.stRankOne i) :
    (∃ h ∈ D.stTorus i, ∃ u ∈ D.stRoot (Pi.single i 1), g = h * u) ∨
      ∃ u ∈ D.stRoot (Pi.single i 1), ∃ h ∈ D.stTorus i, ∃ v ∈ D.stRoot (Pi.single i 1),
        g = u * D.stn i * h * v := by
  have hα := Φ.single_mem i
  have hgK : stPi Φ D.X g ∈ D.rankOne i := by
    rw [← D.map_stRankOne]
    exact Subgroup.mem_map_of_mem _ hg
  have hU : ∀ {u}, u ∈ D.stRoot (Pi.single i 1) → u ∈ D.stRankOne i :=
    fun hu => D.stRoot_single_le_stRankOne i hu
  have hH : ∀ {h}, h ∈ D.stTorus i → h ∈ D.stRankOne i := fun hh => D.stTorus_le_stRankOne i hh
  rcases hD.rankOne_bruhat i _ hgK with ⟨t, ht, x, hx, he⟩ | ⟨x, hx, t, ht, y, hy, he⟩
  · obtain ⟨h, hh, rfl⟩ := hD.exists_mem_stTorus ht
    obtain ⟨u, hu, rfl⟩ := D.exists_mem_stRoot hα hx
    refine Or.inl ⟨h, hh, u, hu, D.injOn_stRankOne i hg (mul_mem (hH hh) (hU hu)) ?_⟩
    rw [map_mul]
    exact he
  · obtain ⟨h, hh, rfl⟩ := hD.exists_mem_stTorus ht
    obtain ⟨u, hu, rfl⟩ := D.exists_mem_stRoot hα hx
    obtain ⟨v, hv, rfl⟩ := D.exists_mem_stRoot hα hy
    refine Or.inr ⟨u, hu, h, hh, v, hv, D.injOn_stRankOne i hg
      (mul_mem (mul_mem (mul_mem (hU hu) (hD.stn_mem i)) (hH hh)) (hU hv)) ?_⟩
    rw [map_mul, map_mul, map_mul, hD.stPi_stn]
    exact he

theorem mem_bruhatSet_of_mem_pos {w : List ι} {i : ι}
    (hw : wordAct Φ.refl w (Pi.single i 1) ∈ Φ.pos) {b₁ u b₂ : StGroup Φ D.X}
    (hb₁ : b₁ ∈ D.stBorel) (hu : u ∈ D.stRoot (Pi.single i 1)) (hb₂ : b₂ ∈ D.stBorel) :
    b₁ * D.stnw w * u * D.stn i * b₂ ∈ D.bruhatSet := by
  have hu' : D.stnw w * u * (D.stnw w)⁻¹ ∈ D.stBorel := by
    have := conj_mem_map_conj (g := D.stnw w) hu
    rw [hD.map_conj_stnw_stRoot w (Φ.single_mem i)] at this
    exact D.stPos_le_stBorel (D.stRoot_le_stSub hw this)
  refine ⟨w ++ [i], b₁ * (D.stnw w * u * (D.stnw w)⁻¹), mul_mem hb₁ hu', b₂, hb₂, ?_⟩
  rw [D.stnw_append, D.stnw_singleton]
  group

theorem mul_mem_bruhatSet {g ℓ : StGroup Φ D.X} (hg : g ∈ D.bruhatSet) {i : ι}
    (hℓ : ℓ ∈ D.stRankOne i) : g * ℓ ∈ D.bruhatSet := by
  have hα := Φ.single_mem i
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  obtain ⟨ℓ', hℓ', b', hb', he⟩ := hD.exists_mul_eq_mul i hb₂ hℓ
  have hH : ∀ {h}, h ∈ D.stTorus i → h ∈ D.stBorel :=
    fun hh => D.stTorusPart_le_stBorel (D.stTorus_le_stTorusPart i hh)
  have hU : ∀ {u}, u ∈ D.stRoot (Pi.single i 1) → u ∈ D.stBorel :=
    fun hu => D.stPos_le_stBorel (D.stRoot_le_stSub (Φ.single_mem_pos i) hu)
  have e1 : b₁ * D.stnw w * b₂ * ℓ = b₁ * D.stnw w * ℓ' * b' := by
    rw [mul_assoc _ b₂, he, ← mul_assoc]
  rw [e1]
  rcases hD.stRankOne_bruhat i hℓ' with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
  · exact ⟨w, b₁, hb₁, h * u * b', mul_mem (mul_mem (hH hh) (hU hu)) hb', by group⟩
  have hvb : h * v * b' ∈ D.stBorel := mul_mem (mul_mem (hH hh) (hU hv)) hb'
  rcases Φ.mem_pos_or_mem_neg (Φ.wordAct_mem w hα) with hpos | hneg
  · have e2 : b₁ * D.stnw w * (u * D.stn i * h * v) * b' =
        b₁ * D.stnw w * u * D.stn i * (h * v * b') := by group
    rw [e2]
    exact hD.mem_bruhatSet_of_mem_pos hpos hb₁ hu hvb
  have hz : (D.stn i)⁻¹ * u * D.stn i ∈ D.stRoot (-Pi.single i 1) := by
    have hn : (D.stRoot (-Pi.single i 1)).map (MulAut.conj (D.stn i)).toMonoidHom =
        D.stRoot (Pi.single i 1) := by
      rw [hD.map_conj_stn_stRoot i (Φ.neg_mem _ hα), Φ.refl_neg_single]
    have h0 := conj_mem_map_conj (g := (D.stn i)⁻¹) hu
    rwa [map_conj_inv_of_map_conj hn, inv_inv] at h0
  have e2 : b₁ * D.stnw w * (u * D.stn i * h * v) * b' =
      b₁ * D.stnw (w ++ [i]) * ((D.stn i)⁻¹ * u * D.stn i) * (h * v * b') := by
    rw [D.stnw_append, D.stnw_singleton]
    group
  rw [e2]
  rcases hD.stRankOne_bruhat i (D.stRoot_neg_single_le_stRankOne i hz) with
    ⟨h', hh', u', hu', hz'⟩ | ⟨u', hu', h', hh', v', hv', hz'⟩
  · rw [hz']
    exact ⟨w ++ [i], b₁, hb₁, h' * u' * (h * v * b'), mul_mem (mul_mem (hH hh') (hU hu')) hvb,
      by group⟩
  · rw [hz']
    have hpos' : wordAct Φ.refl (w ++ [i]) (Pi.single i 1) ∈ Φ.pos := by
      rw [wordAct_append, wordAct_cons, wordAct_nil, Φ.refl_single, wordAct_neg,
        Φ.neg_mem_pos_iff]
      exact hneg
    have e3 : b₁ * D.stnw (w ++ [i]) * (u' * D.stn i * h' * v') * (h * v * b') =
        b₁ * D.stnw (w ++ [i]) * u' * D.stn i * (h' * v' * (h * v * b')) := by group
    rw [e3]
    exact hD.mem_bruhatSet_of_mem_pos hpos' hb₁ hu'
      (mul_mem (mul_mem (hH hh') (hU hv')) hvb)

theorem mem_bruhatSet (g : StGroup Φ D.X) : g ∈ D.bruhatSet := by
  have hg : g ∈ ⨆ i, D.stRankOne i := by
    rw [hD.iSup_stRankOne_eq_top]
    exact Subgroup.mem_top g
  rw [Subgroup.iSup_eq_closure] at hg
  refine Subgroup.closure_induction_right (p := fun x _ => x ∈ D.bruhatSet)
    D.one_mem_bruhatSet (fun x _ y hy ih => ?_) (fun x _ y hy ih => ?_) hg
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
    exact hD.mul_mem_bruhatSet ih hi
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
    exact hD.mul_mem_bruhatSet ih (inv_mem hi)

theorem torusPart_sup_posPart_le_normalizer :
    D.torusPart ⊔ D.posPart ≤ Subgroup.normalizer (D.posPart : Set K) := by
  refine sup_le ?_ Subgroup.le_normalizer
  exact iSup_le fun i => le_normalizer_iSup fun γ => le_normalizer_iSup fun hγ =>
    hD.torus_le_normalizer i γ hγ.1

theorem wordAct_mem_pos {w : List ι} (hw : stPi Φ D.X (D.stnw w) ∈ D.torusPart ⊔ D.posPart)
    {γ : ι → ℤ} (hγ : γ ∈ Φ.pos) : wordAct Φ.refl w γ ∈ Φ.pos := by
  have hr := Φ.wordAct_mem w hγ.1
  rcases Φ.mem_pos_or_mem_neg hr with h | h
  · exact h
  exfalso
  apply hD.ne_bot _ hr
  rw [eq_bot_iff, ← hD.posPart_inf_negPart]
  refine le_inf ?_ (D.X_le_negPart h)
  rw [← hD.map_conj_stPi_stnw w hγ.1]
  exact (Subgroup.map_mono (D.X_le_posPart hγ)).trans
    (mem_normalizer_iff_map_conj.1 (hD.torusPart_sup_posPart_le_normalizer hw)).le

theorem stnw_mem_stTorusPart (w : List ι)
    (hw : stPi Φ D.X (D.stnw w) ∈ D.torusPart ⊔ D.posPart) : D.stnw w ∈ D.stTorusPart := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
  rcases List.eq_nil_or_concat' w with rfl | ⟨ρ, j, rfl⟩
  · exact one_mem _
  have hα := Φ.single_mem j
  have hρ : wordAct Φ.refl ρ (Pi.single j 1) ∉ Φ.pos := by
    intro hpos
    have h0 := hD.wordAct_mem_pos hw (Φ.single_mem_pos j)
    rw [wordAct_append, wordAct_cons, wordAct_nil, Φ.refl_single, wordAct_neg,
      Φ.neg_mem_pos_iff] at h0
    exact Φ.notMem_neg_of_mem_pos hpos h0
  obtain ⟨p, a, v, rfl, hv, hav⟩ :=
    exists_split_wordAct Φ.refl (P := (· ∈ Φ.pos)) (Φ.single_mem_pos j) ρ hρ
  have hβ : wordAct Φ.refl v (Pi.single j 1) = Pi.single a 1 := by
    by_contra hne
    have hne2 : wordAct Φ.refl v (Pi.single j 1) ≠ 2 • Pi.single a 1 :=
      Φ.isIndiv_wordAct v (Φ.isIndiv_single j) _ (Φ.single_mem a)
    have hmem : wordAct Φ.refl v (Pi.single j 1) ∈ Φ.posExcept a := by
      refine ⟨hv, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, hne2⟩
    exact hav (Φ.refl_mem_posExcept hmem).1
  have hβ' : wordAct Φ.refl v (-Pi.single j 1) = -Pi.single a 1 := by
    rw [wordAct_neg, hβ]
  have hs : D.IsSwap a (D.stnw v * D.stn j * (D.stnw v)⁻¹) := (hD.isSwap_stn j).conj
    (by rw [hD.map_conj_stnw_stRoot v hα, hβ])
    (by rw [hD.map_conj_stnw_stRoot v (Φ.neg_mem _ hα), hβ'])
  obtain ⟨h, hh, he⟩ := hD.exists_eq_stn_mul hs
  have hc : D.stn a * D.stn a * h ∈ D.stTorusPart :=
    mul_mem (D.stTorus_le_stTorusPart a (hD.stn_mul_stn_mem a)) (D.stTorus_le_stTorusPart a hh)
  have hc' : (D.stnw v)⁻¹ * (D.stn a * D.stn a * h) * D.stnw v ∈ D.stTorusPart := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hD.stnw_mem_normalizer v)) _).1 hc
    rwa [inv_inv] at this
  have hvj : D.stnw v * D.stn j = D.stn a * h * D.stnw v := by
    rw [← he]
    group
  have heq : D.stnw (p ++ a :: v ++ [j]) =
      D.stnw (p ++ v) * ((D.stnw v)⁻¹ * (D.stn a * D.stn a * h) * D.stnw v) := by
    rw [D.stnw_append, D.stnw_append, D.stnw_cons, D.stnw_singleton, D.stnw_append]
    calc D.stnw p * (D.stn a * D.stnw v) * D.stn j
        = D.stnw p * D.stn a * (D.stnw v * D.stn j) := by group
      _ = D.stnw p * D.stn a * (D.stn a * h * D.stnw v) := by rw [hvj]
      _ = D.stnw p * D.stnw v * ((D.stnw v)⁻¹ * (D.stn a * D.stn a * h) * D.stnw v) := by group
  rw [heq] at hw ⊢
  have hlen : (p ++ v).length < n := by
    rw [← hn]
    simp only [List.length_append, List.length_cons]
    omega
  have hw' : stPi Φ D.X (D.stnw (p ++ v)) ∈ D.torusPart ⊔ D.posPart := by
    have hcK : stPi Φ D.X ((D.stnw v)⁻¹ * (D.stn a * D.stn a * h) * D.stnw v) ∈
        D.torusPart ⊔ D.posPart := by
      refine le_sup_left (a := D.torusPart) ?_
      rw [← hD.map_stTorusPart]
      exact Subgroup.mem_map_of_mem _ hc'
    have := mul_mem hw (inv_mem hcK)
    rwa [map_mul, mul_inv_cancel_right] at this
  exact mul_mem (ih _ hlen (p ++ v) hw' rfl) hc'

theorem injective_stPi : Function.Injective (stPi Φ D.X) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := hD.mem_bruhatSet g
  have hw : stPi Φ D.X (D.stnw w) ∈ D.torusPart ⊔ D.posPart := by
    rw [map_mul, map_mul] at hg
    have e : stPi Φ D.X (D.stnw w) = (stPi Φ D.X b₁)⁻¹ * (stPi Φ D.X b₂)⁻¹ := by
      calc stPi Φ D.X (D.stnw w)
          = (stPi Φ D.X b₁)⁻¹ * (stPi Φ D.X b₁ * stPi Φ D.X (D.stnw w) * stPi Φ D.X b₂) *
              (stPi Φ D.X b₂)⁻¹ := by group
        _ = (stPi Φ D.X b₁)⁻¹ * (stPi Φ D.X b₂)⁻¹ := by rw [hg, mul_one]
    rw [e]
    exact mul_mem (inv_mem (hD.stPi_mem_of_mem_stBorel hb₁))
      (inv_mem (hD.stPi_mem_of_mem_stBorel hb₂))
  have hn := hD.stnw_mem_stTorusPart w hw
  have hg' : b₁ * D.stnw w * b₂ ∈ D.stBorel :=
    mul_mem (mul_mem hb₁ (D.stTorusPart_le_stBorel hn)) hb₂
  exact hD.injOn_stBorel hg' (one_mem _) (by rw [hg, map_one])

theorem bijective_stPi (hgen : ⨆ γ ∈ Φ.roots, D.X γ = ⊤) : Function.Bijective (stPi Φ D.X) :=
  ⟨hD.injective_stPi, D.surjective_stPi hgen⟩

omit hD in
@[expose] def stPiEquiv (hD : D.IsSteinberg) (hgen : ⨆ γ ∈ Φ.roots, D.X γ = ⊤) :
    StGroup Φ D.X ≃* K :=
  MulEquiv.ofBijective (stPi Φ D.X) (hD.bijective_stPi hgen)

omit hD in
@[simp] theorem stPiEquiv_apply (hD : D.IsSteinberg) (hgen : ⨆ γ ∈ Φ.roots, D.X γ = ⊤)
    (g : StGroup Φ D.X) : hD.stPiEquiv hgen g = stPi Φ D.X g :=
  rfl

theorem existsUnique_hom (hgen : ⨆ γ ∈ Φ.roots, D.X γ = ⊤) {G : Type*} [Group G]
    (φ : Symbol Φ D.X → G) (hφ : ∀ w ∈ rel1 Φ D.X ∪ rel2 Φ D.X, FreeGroup.lift φ w = 1) :
    ∃! ψ : K →* G, ∀ s : Symbol Φ D.X, ψ s.1.2 = φ s := by
  have hN : relN Φ D.X ≤ (FreeGroup.lift φ).ker :=
    Subgroup.normalClosure_le_normal fun w hw => hφ w hw
  set e := hD.stPiEquiv hgen
  set φ' : StGroup Φ D.X →* G := QuotientGroup.lift (relN Φ D.X) (FreeGroup.lift φ) hN
  have he : ∀ s : Symbol Φ D.X, e (QuotientGroup.mk' (relN Φ D.X) (FreeGroup.of s)) = s.1.2 :=
    fun s => by rw [stPiEquiv_apply, D.stPi_mk, D.piF_of]
  have hφ' : ∀ s : Symbol Φ D.X, φ' (QuotientGroup.mk' (relN Φ D.X) (FreeGroup.of s)) = φ s :=
    fun s => by rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk, FreeGroup.lift_apply_of]
  refine ⟨φ'.comp e.symm.toMonoidHom, fun s => ?_, fun ψ hψ => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← he s, MulEquiv.symm_apply_apply, hφ']
  · have hcomp : ψ.comp e.toMonoidHom = φ' := by
      refine QuotientGroup.monoidHom_ext _ (FreeGroup.ext_hom _ _ fun s => ?_)
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, he, hψ, hφ']
    ext k
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hcomp, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

end IsSteinberg

end RootGroupData

end CFSG.LieType.Steinberg
