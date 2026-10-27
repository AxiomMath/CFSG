module

public import CFSG.ClassicalInvolution.Q3.Sec13EndDEWylC

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

abbrev Lab2 : Type := ZMod 2 × ZMod 2

structure TwinShift (Ω : Set (Subgroup G)) where
  conj_mem : ∀ (g : G), ∀ K ∈ Ω, conjSub g K ∈ Ω
  shift : Lab2 → Subgroup G → Subgroup G
  shift_zero : ∀ K ∈ Ω, shift 0 K = K
  shift_add : ∀ (m m' : Lab2), ∀ K ∈ Ω, shift (m + m') K = shift m (shift m' K)
  shift_mem : ∀ (m : Lab2), ∀ K ∈ Ω, shift m K ∈ twinSet Ω K
  shift_conj : ∀ (m : Lab2) (g : G), ∀ K ∈ Ω, shift m (conjSub g K) = conjSub g (shift m K)
  shift_free : ∀ (m : Lab2), ∀ K ∈ Ω, shift m K = K → m = 0

@[expose] def dewDual2 (Ω : Set (Subgroup G)) : Set (G → Lab2) :=
  {F | F 1 = 0 ∧ (∀ x, x ∉ zGroup Ω → F x = 0) ∧
    ∀ x ∈ zGroup Ω, ∀ y ∈ zGroup Ω, F (x * y) = F x + F y}

open Classical in
@[expose] noncomputable def TwinShift.lam {Ω : Set (Subgroup G)} (S : TwinShift Ω) (q x : G) :
    Lab2 :=
  if hx : ∃ M, M ∈ dew1V Ω x then
    if hm : ∃ m : Lab2, conjSub q hx.choose = S.shift m hx.choose then hm.choose else 0
  else 0

@[expose] def IsTransport {Ω : Set (Subgroup G)} (S : TwinShift Ω) (π : Lab2 → Lab2) : Prop :=
  ∀ b : Lab2, b ≠ 0 → ∀ K ∈ Ω, ∀ k ∈ K, ∀ j ∈ S.shift b K, k * j⁻¹ ∈ pCore 2 G →
    ∀ x ∈ zGroup Ω, k * x * k⁻¹ ≠ x → S.lam (k * j⁻¹) x = π b

namespace TwinShift

variable {Ω : Set (Subgroup G)} (S : TwinShift Ω)

theorem shift_shift_self (m : Lab2) {K : Subgroup G} (hK : K ∈ Ω) :
    S.shift m (S.shift m K) = K := by
  rw [← S.shift_add m m K hK, show m + m = 0 from by ext <;> simp [CharTwo.add_self_eq_zero],
    S.shift_zero K hK]

theorem shift_injective {K : Subgroup G} (hK : K ∈ Ω) {m m' : Lab2}
    (hmm : S.shift m K = S.shift m' K) : m = m' := by
  have h1 : S.shift (m + m') K = K := by
    rw [S.shift_add m m' K hK, ← hmm, S.shift_shift_self m hK]
  have h2 : m + m' = 0 := S.shift_free _ K hK h1
  rw [add_eq_zero_iff_eq_neg] at h2
  rw [h2]
  ext <;> simp [CharTwo.neg_eq]

end TwinShift

private theorem dd_zmod_two (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

private theorem dd_lab2_add_self (m : Lab2) : m + m = 0 := by
  ext <;> simp [CharTwo.add_self_eq_zero]

private theorem dd_eq_of_add_eq_zero {a c : Lab2} (hac : a + c = 0) : c = a := by
  calc c = (a + a) + c := by rw [dd_lab2_add_self, zero_add]
    _ = a + (a + c) := by abel
    _ = a := by rw [hac, add_zero]

private theorem dd_lam_eq_zero_of_no_member {Ω : Set (Subgroup G)} (S : TwinShift Ω) {q x : G}
    (hx : ¬∃ M, M ∈ dew1V Ω x) : S.lam q x = 0 := by
  unfold TwinShift.lam
  rw [dif_neg hx]

abbrev DdAdm {Ω : Set (Subgroup G)} (S : TwinShift Ω) (b : Lab2) (K : Subgroup G) (k j x : G) :
    Prop :=
  K ∈ Ω ∧ k ∈ K ∧ j ∈ S.shift b K ∧ k * j⁻¹ ∈ pCore 2 G ∧ x ∈ zGroup Ω ∧ k * x * k⁻¹ ≠ x

private theorem dd_expand {Ω : Set (Subgroup G)} {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {F : G → M} (hF1 : F 1 = 0)
    (hadd : ∀ x ∈ zGroup Ω, ∀ y ∈ zGroup Ω, F (x * y) = F x + F y) (v : Fin 3 → ZMod 2) :
    F (TL4.e8Coord e v) = ∑ i, v i • F (e i) := by
  have hsingle : ∀ (i : Fin 3) (c : ZMod 2), F (TL4.e8Coord e (Pi.single i c)) = c • F (e i) := by
    intro i c
    rcases dd_zmod_two c with rfl | rfl
    · rw [Pi.single_zero, TL4.e8Coord_zero, hF1, zero_smul]
    · rw [TL4.e8Coord_single, one_smul]
  have key : F (TL4.e8Coord e v) = v 0 • F (e 0) + v 1 • F (e 1) + v 2 • F (e 2) := by
    have hA := TL4.e8Coord_mem he (Pi.single (0 : Fin 3) (v 0) : Fin 3 → ZMod 2)
    have hB := TL4.e8Coord_mem he (Pi.single (1 : Fin 3) (v 1) : Fin 3 → ZMod 2)
    have hC := TL4.e8Coord_mem he (Pi.single (2 : Fin 3) (v 2) : Fin 3 → ZMod 2)
    have hAB : TL4.e8Coord e (Pi.single (0 : Fin 3) (v 0) : Fin 3 → ZMod 2) *
        TL4.e8Coord e (Pi.single (1 : Fin 3) (v 1) : Fin 3 → ZMod 2) ∈ zGroup Ω :=
      (zGroup Ω).mul_mem hA hB
    have hv : v = (Pi.single (0 : Fin 3) (v 0) : Fin 3 → ZMod 2) + Pi.single (1 : Fin 3) (v 1) +
        Pi.single (2 : Fin 3) (v 2) := by
      funext i
      fin_cases i <;> simp
    conv_lhs => rw [hv]
    rw [TL4.e8Coord_add he, TL4.e8Coord_add he, hadd _ hAB _ hC, hadd _ hA _ hB, hsingle,
      hsingle, hsingle]
  rw [key, Fin.sum_univ_three]

open Classical in
private noncomputable def dd_coord {Ω : Set (Subgroup G)} {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) (x : G) : Fin 3 → ZMod 2 :=
  if hx : x ∈ zGroup Ω then (TL4.exists_e8Coord_eq he hx).choose else 0

private theorem dd_coord_spec {Ω : Set (Subgroup G)} {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) {x : G} (hx : x ∈ zGroup Ω) :
    TL4.e8Coord e (dd_coord he x) = x := by
  unfold dd_coord
  rw [dif_pos hx]
  exact (TL4.exists_e8Coord_eq he hx).choose_spec

private theorem dd_coord_e8Coord {Ω : Set (Subgroup G)} {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) (v : Fin 3 → ZMod 2) :
    dd_coord he (TL4.e8Coord e v) = v := by
  apply TL4.e8Coord_injective he
  exact dd_coord_spec he (TL4.e8Coord_mem he v)

private theorem dd_coord_mul {Ω : Set (Subgroup G)} {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) {x y : G} (hx : x ∈ zGroup Ω) (hy : y ∈ zGroup Ω) :
    dd_coord he (x * y) = dd_coord he x + dd_coord he y := by
  apply TL4.e8Coord_injective he
  rw [dd_coord_spec he ((zGroup Ω).mul_mem hx hy), TL4.e8Coord_add he, dd_coord_spec he hx,
    dd_coord_spec he hy]

private theorem dd_coord_one {Ω : Set (Subgroup G)} {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) : dd_coord he 1 = 0 := by
  have := dd_coord_e8Coord he 0
  rwa [TL4.e8Coord_zero] at this

private theorem dd_coord_single {Ω : Set (Subgroup G)} {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) (i : Fin 3) : dd_coord he (e i) = Pi.single i 1 := by
  have := dd_coord_e8Coord he (Pi.single i 1)
  rwa [TL4.e8Coord_single] at this

private theorem dd_fin_common_zero : ∀ f g : Fin 3 → ZMod 2, ∃ v : Fin 3 → ZMod 2,
    v ≠ 0 ∧ dotProduct f v = 0 ∧ dotProduct g v = 0 := by
  decide +kernel

namespace DE4Hyp

variable {Ω : Set (Subgroup G)} (h : DE4Hyp Ω)
include h

private theorem dd_dew1V_conj {g x : G} {M : Subgroup G} (hM : M ∈ dew1V Ω x) :
    conjSub g M ∈ dew1V Ω (g * x * g⁻¹) :=
  ⟨h.hyp.conjInvariant g M hM.1, hM.2.conj g⟩

private theorem dd_conj_mem_twinSet {L J : Subgroup G} (hJ : J ∈ twinSet Ω L) (g : G) :
    conjSub g J ∈ twinSet Ω (conjSub g L) := by
  obtain ⟨hJΩ, z, hLz, hJz⟩ := hJ
  exact ⟨h.hyp.conjInvariant g J hJΩ, g * z * g⁻¹, hLz.conj g, hJz.conj g⟩

private theorem dd_twins (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G} {u : G}
    (hK : K ∈ Ω) (hu : IsUniqueInvolution K u) : DewTwins Ω K (S.shift b K) u := by
  obtain ⟨hJ, z, hKz, hJz⟩ := S.shift_mem b K hK
  have hz : z = u := hKz.eq hu
  subst hz
  exact ⟨hK, hJ, hKz, hJz, fun e => hb (S.shift_free b K hK e.symm)⟩

theorem exists_unique_shift (S : TwinShift Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ twinSet Ω K) : ∃! m : Lab2, S.shift m K = J := by
  have hinj : Function.Injective (fun m : Lab2 => S.shift m K) := fun m m' hmm =>
    S.shift_injective hK hmm
  have himg : (Set.range fun m : Lab2 => S.shift m K) ⊆ twinSet Ω K := by
    rintro _ ⟨m, rfl⟩
    exact S.shift_mem m K hK
  have hfin : (twinSet Ω K).Finite := Set.toFinite _
  have hLab : Nat.card Lab2 = 4 := by
    rw [Nat.card_prod, Nat.card_zmod]
  have hcard : (Set.range fun m : Lab2 => S.shift m K).ncard = 4 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ, hLab]
  have heq : Set.range (fun m : Lab2 => S.shift m K) = twinSet Ω K :=
    Set.eq_of_subset_of_ncard_le himg (by rw [hcard, h.twin4 K hK]) hfin
  have hJ' : J ∈ Set.range (fun m : Lab2 => S.shift m K) := heq ▸ hJ
  obtain ⟨m, hm⟩ := hJ'
  exact ⟨m, hm, fun m' hm' => hinj (hm'.trans hm.symm)⟩

theorem exists_twinShift : Nonempty (TwinShift Ω) := by
  classical
  obtain ⟨K₀, hK₀, -, -, -⟩ := h.exists_ne
  obtain ⟨u₀, hu₀⟩ := h.exists_isUniqueInvolution hK₀
  have hu₀D : u₀ ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK₀ hu₀
  have hu₀1 : u₀ ≠ 1 := hu₀.ne_one
  have hK₀V : K₀ ∈ dew1V Ω u₀ := ⟨hK₀, hu₀⟩
  have hV : dew1V Ω u₀ = twinSet Ω K₀ := dew1V_eq_twinSet hK₀ hu₀
  have hcard : (dew1V Ω u₀).ncard = 4 := h.ncard_dew1V hK₀ hu₀
  have h3 : ((dew1V Ω u₀) \ {K₀}).ncard = 3 := by
    rw [Set.ncard_diff_singleton_of_mem hK₀V, hcard]
  obtain ⟨J₁, J₂, -, hJ₁, hJ₂, -, hJ₁J₂, -, -⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).mp (by omega : 2 < ((dew1V Ω u₀) \ {K₀}).ncard)
  have hJ₁V : J₁ ∈ dew1V Ω u₀ := hJ₁.1
  have hJ₂V : J₂ ∈ dew1V Ω u₀ := hJ₂.1
  have hJ₁K : J₁ ≠ K₀ := fun e => hJ₁.2 (Set.mem_singleton_iff.mpr e)
  have hJ₂K : J₂ ≠ K₀ := fun e => hJ₂.2 (Set.mem_singleton_iff.mpr e)
  have hJ₁tw : J₁ ∈ twinSet Ω K₀ := by
    rw [← hV]
    exact hJ₁V
  have hJ₂tw : J₂ ∈ twinSet Ω K₀ := by
    rw [← hV]
    exact hJ₂V
  obtain ⟨q₁, hq₁, hq₁K⟩ := h.exists_pCore_conj_of_mem_twinSet hK₀ hJ₁tw
  obtain ⟨q₂, hq₂, hq₂K⟩ := h.exists_pCore_conj_of_mem_twinSet hK₀ hJ₂tw
  obtain ⟨act, hact0, hact10, hact01, hact11, hactQ⟩ : ∃ act : Lab2 → G, act 0 = 1 ∧
      act (1, 0) = q₁ ∧ act (0, 1) = q₂ ∧ act (1, 1) = q₁ * q₂ ∧ ∀ m, act m ∈ pCore 2 G :=
    ⟨fun m => if m.1 = 0 then (if m.2 = 0 then 1 else q₂) else (if m.2 = 0 then q₁ else q₁ * q₂),
      by simp, by simp, by simp, by simp, fun m => by
        dsimp only
        split_ifs
        · exact (pCore 2 G).one_mem
        · exact hq₂
        · exact hq₁
        · exact (pCore 2 G).mul_mem hq₁ hq₂⟩
  have hqV : ∀ q ∈ pCore 2 G, ∀ M ∈ dew1V Ω u₀, conjSub q M ∈ dew1V Ω u₀ := fun q hq M hM =>
    dew1_conj_mem h.toDEHyp (h.pCore_le_centralizer_zGroup hq) hM
  have hA2 : ∀ M ∈ dew1V Ω u₀, conjSub q₁ (conjSub q₁ M) = M := fun M hM =>
    h.pCore_act_sq hu₀D hu₀1 hq₁ hM
  have hB2 : ∀ M ∈ dew1V Ω u₀, conjSub q₂ (conjSub q₂ M) = M := fun M hM =>
    h.pCore_act_sq hu₀D hu₀1 hq₂ hM
  have hAB : ∀ M ∈ dew1V Ω u₀, conjSub q₁ (conjSub q₂ M) = conjSub q₂ (conjSub q₁ M) :=
    fun M hM => h.pCore_act_comm hu₀D hu₀1 hq₁ hq₂ hM
  have hLab : ∀ m : Lab2, m = 0 ∨ m = (1, 0) ∨ m = (0, 1) ∨ m = (1, 1) := by decide
  have s1 : ((1, 0) : Lab2) + (1, 0) = 0 := by decide
  have s2 : ((1, 0) : Lab2) + (0, 1) = (1, 1) := by decide
  have s3 : ((1, 0) : Lab2) + (1, 1) = (0, 1) := by decide
  have s4 : ((0, 1) : Lab2) + (1, 0) = (1, 1) := by decide
  have s5 : ((0, 1) : Lab2) + (0, 1) = 0 := by decide
  have s6 : ((0, 1) : Lab2) + (1, 1) = (1, 0) := by decide
  have s7 : ((1, 1) : Lab2) + (1, 0) = (0, 1) := by decide
  have s8 : ((1, 1) : Lab2) + (0, 1) = (1, 0) := by decide
  have s9 : ((1, 1) : Lab2) + (1, 1) = 0 := by decide
  have hKlein : ∀ m m' : Lab2, ∀ M ∈ dew1V Ω u₀,
      conjSub (act (m + m')) M = conjSub (act m) (conjSub (act m') M) := by
    intro m m' M hM
    rcases hLab m with rfl | rfl | rfl | rfl <;> rcases hLab m' with rfl | rfl | rfl | rfl
    · simp [hact0]
    · simp [hact0, hact10]
    · simp [hact0, hact01]
    · simp [hact0, hact11]
    · simp [hact0, hact10]
    · rw [s1, hact0, conjSub_one, hact10, hA2 M hM]
    · rw [s2, hact11, hact10, hact01, conjSub_mul]
    · rw [s3, hact01, hact10, hact11, conjSub_mul, hA2 _ (hqV q₂ hq₂ M hM)]
    · simp [hact0, hact01]
    · rw [s4, hact11, hact01, hact10, conjSub_mul, hAB M hM]
    · rw [s5, hact0, conjSub_one, hact01, hB2 M hM]
    · rw [s6, hact10, hact01, hact11, conjSub_mul, hAB M hM, hB2 _ (hqV q₁ hq₁ M hM)]
    · simp [hact0, hact11]
    · rw [s7, hact01, hact11, hact10, conjSub_mul, ← hAB M hM, hA2 _ (hqV q₂ hq₂ M hM)]
    · rw [s8, hact10, hact11, hact01, conjSub_mul, hB2 M hM]
    · rw [s9, hact0, conjSub_one, hact11, conjSub_mul, conjSub_mul, hAB M hM,
        hB2 _ (hqV q₁ hq₁ M hM), hA2 M hM]
  have hindep : ∀ a b : G, conjSub a K₀ = conjSub b K₀ → ∀ X ∈ dew1V Ω u₀,
      conjSub a X = conjSub b X := by
    intro a b hab X hX
    have hn : a⁻¹ * b ∈ Subgroup.normalizer (K₀ : Set G) := by
      rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, ← hab, conjSub_inv_conjSub]
    have hfix := h.normalizer_fixes_twins hK₀V hn X hX
    calc conjSub a X = conjSub a (conjSub (a⁻¹ * b) X) := by rw [hfix]
      _ = conjSub (a * (a⁻¹ * b)) X := (conjSub_mul _ _ _).symm
      _ = conjSub b X := by rw [mul_inv_cancel_left]
  obtain ⟨gK, hgK⟩ : ∃ gK : Subgroup G → G, ∀ K ∈ Ω, conjSub (gK K) K₀ = K := by
    refine ⟨fun K => if hK : K ∈ Ω then Classical.choose (h.trans K₀ hK₀ K hK) else 1,
      fun K hK => ?_⟩
    simp only [dif_pos hK]
    exact Classical.choose_spec (h.trans K₀ hK₀ K hK)
  refine ⟨{ conj_mem := fun g K hK => h.hyp.conjInvariant g K hK
            shift := fun m K => conjSub (gK K * act m) K₀
            shift_zero := ?_
            shift_add := ?_
            shift_mem := ?_
            shift_conj := ?_
            shift_free := ?_ }⟩
  · intro K hK
    show conjSub (gK K * act 0) K₀ = K
    rw [hact0, mul_one, hgK K hK]
  · intro m m' K hK
    show conjSub (gK K * act (m + m')) K₀ = conjSub (gK (conjSub (gK K * act m') K₀) * act m) K₀
    have hK' : conjSub (gK K * act m') K₀ ∈ Ω := h.hyp.conjInvariant _ K₀ hK₀
    have hX : conjSub (act m) K₀ ∈ dew1V Ω u₀ := hqV _ (hactQ m) K₀ hK₀V
    have ea : conjSub (gK (conjSub (gK K * act m') K₀)) K₀ = conjSub (gK K * act m') K₀ :=
      hgK _ hK'
    calc conjSub (gK K * act (m + m')) K₀ = conjSub (gK K) (conjSub (act (m + m')) K₀) :=
          conjSub_mul _ _ _
      _ = conjSub (gK K) (conjSub (act m') (conjSub (act m) K₀)) := by
          rw [add_comm m m', hKlein m' m K₀ hK₀V]
      _ = conjSub (gK K * act m') (conjSub (act m) K₀) := (conjSub_mul _ _ _).symm
      _ = conjSub (gK (conjSub (gK K * act m') K₀)) (conjSub (act m) K₀) :=
          (hindep _ _ ea _ hX).symm
      _ = conjSub (gK (conjSub (gK K * act m') K₀) * act m) K₀ := (conjSub_mul _ _ _).symm
  · intro m K hK
    show conjSub (gK K * act m) K₀ ∈ twinSet Ω K
    rw [conjSub_mul]
    have hX : conjSub (act m) K₀ ∈ twinSet Ω K₀ := by
      rw [← hV]
      exact hqV _ (hactQ m) K₀ hK₀V
    have := h.dd_conj_mem_twinSet hX (gK K)
    rwa [hgK K hK] at this
  · intro m g K hK
    show conjSub (gK (conjSub g K) * act m) K₀ = conjSub g (conjSub (gK K * act m) K₀)
    have hK1 : conjSub g K ∈ Ω := h.hyp.conjInvariant g K hK
    have eb : conjSub (g * gK K) K₀ = conjSub g K := by rw [conjSub_mul, hgK K hK]
    have ea : conjSub (gK (conjSub g K)) K₀ = conjSub (g * gK K) K₀ := by
      rw [hgK _ hK1, eb]
    have hX : conjSub (act m) K₀ ∈ dew1V Ω u₀ := hqV _ (hactQ m) K₀ hK₀V
    calc conjSub (gK (conjSub g K) * act m) K₀
        = conjSub (gK (conjSub g K)) (conjSub (act m) K₀) := conjSub_mul _ _ _
      _ = conjSub (g * gK K) (conjSub (act m) K₀) := hindep _ _ ea _ hX
      _ = conjSub g (conjSub (gK K) (conjSub (act m) K₀)) := conjSub_mul _ _ _
      _ = conjSub g (conjSub (gK K * act m) K₀) := by rw [conjSub_mul]
  · intro m K hK hmK
    have hmK' : conjSub (gK K) (conjSub (act m) K₀) = K := by
      rw [← conjSub_mul]
      exact hmK
    have h1 : conjSub (act m) K₀ = K₀ := by
      apply conjSub_injective (gK K)
      rw [hmK', hgK K hK]
    rcases hLab m with rfl | rfl | rfl | rfl
    · rfl
    · exfalso
      rw [hact10] at h1
      exact hJ₁K (hq₁K.symm.trans h1)
    · exfalso
      rw [hact01] at h1
      exact hJ₂K (hq₂K.symm.trans h1)
    · exfalso
      rw [hact11, conjSub_mul, hq₂K] at h1
      have hJ : J₂ = J₁ := by
        calc J₂ = conjSub q₁ (conjSub q₁ J₂) := (hA2 J₂ hJ₂V).symm
          _ = conjSub q₁ K₀ := by rw [h1]
          _ = J₁ := hq₁K
      exact hJ₁J₂ hJ.symm

theorem lam_spec (S : TwinShift Ω) {q x : G} (hq : q ∈ pCore 2 G) {M : Subgroup G}
    (hM : M ∈ dew1V Ω x) : conjSub q M = S.shift (S.lam q x) M := by
  have hx : ∃ M', M' ∈ dew1V Ω x := ⟨M, hM⟩
  have hM₀ : hx.choose ∈ dew1V Ω x := hx.choose_spec
  have hJ : conjSub q hx.choose ∈ twinSet Ω hx.choose := by
    rw [← dew1V_eq_twinSet hM₀.1 hM₀.2]
    exact dew1_conj_mem h.toDEHyp (h.pCore_le_centralizer_zGroup hq) hM₀
  obtain ⟨m, hm, -⟩ := h.exists_unique_shift S hM₀.1 hJ
  have hm' : ∃ m : Lab2, conjSub q hx.choose = S.shift m hx.choose := ⟨m, hm.symm⟩
  have hlam : S.lam q x = hm'.choose := by
    unfold TwinShift.lam
    rw [dif_pos hx, dif_pos hm']
  have hspec : conjSub q hx.choose = S.shift (S.lam q x) hx.choose := by
    rw [hlam]
    exact hm'.choose_spec
  have hxD : x ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hM.1 hM.2
  have hx1 : x ≠ 1 := hM.2.ne_one
  have hMtw : M ∈ twinSet Ω hx.choose := by
    rw [← dew1V_eq_twinSet hM₀.1 hM₀.2]
    exact hM
  obtain ⟨r, hr, hrM⟩ := h.exists_pCore_conj_of_mem_twinSet hM₀.1 hMtw
  rw [← hrM, h.pCore_act_comm hxD hx1 hq hr hM₀, hspec, S.shift_conj _ _ _ hM₀.1]

theorem lam_eq_zero_of_not_mem (S : TwinShift Ω) {q x : G} (hx : x ∉ zGroup Ω ∨ x = 1) :
    S.lam q x = 0 := by
  apply dd_lam_eq_zero_of_no_member
  rintro ⟨M, hM⟩
  have hxD := dew1_involution_mem h.toDEHyp hM.1 hM.2
  rcases hx with hx | hx
  · exact hx hxD
  · exact hM.2.ne_one hx

theorem lam_mul (S : TwinShift Ω) {q q' : G} (hq : q ∈ pCore 2 G) (hq' : q' ∈ pCore 2 G)
    (x : G) : S.lam (q * q') x = S.lam q x + S.lam q' x := by
  by_cases hx : ∃ M, M ∈ dew1V Ω x
  · obtain ⟨M, hM⟩ := hx
    apply S.shift_injective hM.1
    rw [← h.lam_spec S ((pCore 2 G).mul_mem hq hq') hM, conjSub_mul, h.lam_spec S hq' hM,
      ← S.shift_conj _ _ _ hM.1, h.lam_spec S hq hM, ← S.shift_add _ _ _ hM.1, add_comm]
  · simp only [dd_lam_eq_zero_of_no_member S hx, add_zero]

theorem lam_one (S : TwinShift Ω) (x : G) : S.lam 1 x = 0 := by
  by_cases hx : ∃ M, M ∈ dew1V Ω x
  · obtain ⟨M, hM⟩ := hx
    apply S.shift_injective hM.1
    rw [← h.lam_spec S (pCore 2 G).one_mem hM, conjSub_one, S.shift_zero M hM.1]
  · exact dd_lam_eq_zero_of_no_member S hx

theorem lam_inv (S : TwinShift Ω) {q : G} (hq : q ∈ pCore 2 G) (x : G) :
    S.lam q⁻¹ x = S.lam q x := by
  have h1 := h.lam_mul S hq ((pCore 2 G).inv_mem hq) x
  rw [mul_inv_cancel, h.lam_one S x] at h1
  exact dd_eq_of_add_eq_zero h1.symm

theorem lam_of_mem_zGroup (S : TwinShift Ω) {d : G} (hd : d ∈ zGroup Ω) (x : G) :
    S.lam d x = 0 := by
  by_cases hx : ∃ M, M ∈ dew1V Ω x
  · obtain ⟨M, hM⟩ := hx
    have hdM : conjSub d M = M := mem_normalizer_iff_conjSub_eq.mp (h.dNorm M hM.1 hd)
    apply S.shift_injective hM.1
    rw [← h.lam_spec S (h.zGroup_le_pCore hd) hM, hdM, S.shift_zero M hM.1]
  · exact dd_lam_eq_zero_of_no_member S hx

theorem lam_conj (S : TwinShift Ω) {q : G} (hq : q ∈ pCore 2 G) (g x : G) :
    S.lam (g * q * g⁻¹) (g * x * g⁻¹) = S.lam q x := by
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  have hgq : g * q * g⁻¹ ∈ pCore 2 G := (inferInstance : (pCore 2 G).Normal).conj_mem q hq g
  by_cases hx : ∃ M, M ∈ dew1V Ω x
  · obtain ⟨M, hM⟩ := hx
    have hM' : conjSub g M ∈ dew1V Ω (g * x * g⁻¹) := dd_dew1V_conj h hM
    have e1 : conjSub (g * q * g⁻¹) (conjSub g M) = conjSub g (conjSub q M) := by
      rw [conjSub_mul (g * q) g⁻¹, conjSub_mul g q, conjSub_inv_conjSub]
    apply S.shift_injective (h.hyp.conjInvariant g M hM.1)
    rw [← h.lam_spec S hgq hM', e1, h.lam_spec S hq hM, S.shift_conj _ _ _ hM.1]
  · have hx' : ¬∃ M, M ∈ dew1V Ω (g * x * g⁻¹) := by
      rintro ⟨M', hM'⟩
      apply hx
      refine ⟨conjSub g⁻¹ M', ?_⟩
      have := dd_dew1V_conj h (g := g⁻¹) hM'
      rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
    rw [dd_lam_eq_zero_of_no_member S hx, dd_lam_eq_zero_of_no_member S hx']

theorem lam_eq_zero_iff (S : TwinShift Ω) {q : G} (hq : q ∈ pCore 2 G) :
    (∀ x, S.lam q x = 0) ↔ q ∈ zGroup Ω := by
  constructor
  · intro hall
    refine h.mem_zGroup_of_normalizes_all hq fun L hL => ?_
    obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hL
    rw [mem_normalizer_iff_conjSub_eq, h.lam_spec S hq (show L ∈ dew1V Ω u from ⟨hL, hu⟩),
      hall u, S.shift_zero L hL]
  · exact fun hq' x => h.lam_of_mem_zGroup S hq' x

theorem conjSub_eq_iff_lam_eq_zero (S : TwinShift Ω) {q x : G} (hq : q ∈ pCore 2 G)
    {M : Subgroup G} (hM : M ∈ dew1V Ω x) : conjSub q M = M ↔ S.lam q x = 0 := by
  rw [h.lam_spec S hq hM]
  constructor
  · exact fun h1 => S.shift_free _ M hM.1 h1
  · exact fun h1 => by rw [h1, S.shift_zero M hM.1]

private theorem dd_transport (S : TwinShift Ω) {b : Lab2} {K : Subgroup G} {k j x : G}
    (hadm : DdAdm S b K k j x) (g : G) :
    DdAdm S b (conjSub g K) (g * k * g⁻¹) (g * j * g⁻¹) (g * x * g⁻¹) ∧
      S.lam (g * k * g⁻¹ * (g * j * g⁻¹)⁻¹) (g * x * g⁻¹) = S.lam (k * j⁻¹) x := by
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  obtain ⟨hK, hk, hj, hkj, hx, hkx⟩ := hadm
  have hgkj : g * k * g⁻¹ * (g * j * g⁻¹)⁻¹ = g * (k * j⁻¹) * g⁻¹ := by group
  refine ⟨⟨h.hyp.conjInvariant g K hK, conj_mem_conjSub hk, ?_,
    ?_, h.zGroup_normal.conj_mem x hx g, ?_⟩, ?_⟩
  · rw [S.shift_conj b g K hK]
    exact conj_mem_conjSub hj
  · rw [hgkj]
    exact (inferInstance : (pCore 2 G).Normal).conj_mem _ hkj g
  · intro e
    apply hkx
    calc k * x * k⁻¹ = g⁻¹ * (g * k * g⁻¹ * (g * x * g⁻¹) * (g * k * g⁻¹)⁻¹) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [e]
      _ = x := by group
  · rw [hgkj]
    exact h.lam_conj S hkj g x

private theorem dd_same_K (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G}
    {k₁ k₂ j₁ j₂ x : G} (h₁ : DdAdm S b K k₁ j₁ x) (h₂ : DdAdm S b K k₂ j₂ x) :
    S.lam (k₁ * j₁⁻¹) x = S.lam (k₂ * j₂⁻¹) x := by
  obtain ⟨hK, hk₁, hj₁, hkj₁, hx, hkx₁⟩ := h₁
  obtain ⟨-, hk₂, hj₂, hkj₂, -, hkx₂⟩ := h₂
  obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK
  have tw : DewTwins Ω K (S.shift b K) u := h.dd_twins S hb hK hu
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hkx₁ (by simp)
  obtain ⟨M, hM⟩ := h.exists_mem_dew1V hx hx1
  have hc₁ : k₁ * x ≠ x * k₁ := fun e => hkx₁ (by rw [e, mul_inv_cancel_right])
  have hc₂ : k₂ * x ≠ x * k₂ := fun e => hkx₂ (by rw [e, mul_inv_cancel_right])
  have e₁ := h.dewDelta_act_of_not_commute tw hk₁ hj₁ hkj₁ hx hc₁ hM
  have e₂ := h.dewDelta_act_of_not_commute tw hk₂ hj₂ hkj₂ hx hc₂ hM
  have e : S.shift (S.lam (k₁ * j₁⁻¹) x) M = S.shift (S.lam (k₂ * j₂⁻¹) x) M := by
    rw [← h.lam_spec S hkj₁ hM, ← h.lam_spec S hkj₂ hM, e₁, e₂]
  exact S.shift_injective hM.1 e

private theorem dd_label_eq (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K₁ K₂ : Subgroup G}
    {k₁ k₂ j₁ j₂ x₁ x₂ : G} (h₁ : DdAdm S b K₁ k₁ j₁ x₁) (h₂ : DdAdm S b K₂ k₂ j₂ x₂) :
    S.lam (k₁ * j₁⁻¹) x₁ = S.lam (k₂ * j₂⁻¹) x₂ := by
  obtain ⟨hK₁, hk₁, hj₁, hkj₁, hx₁, hkx₁⟩ := h₁
  obtain ⟨hK₂, hk₂, hj₂, hkj₂, hx₂, hkx₂⟩ := h₂
  obtain ⟨y₁, hy₁⟩ := h.exists_isUniqueInvolution hK₁
  obtain ⟨y₂, hy₂⟩ := h.exists_isUniqueInvolution hK₂
  have hyD₁ : y₁ ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK₁ hy₁
  have hyD₂ : y₂ ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK₂ hy₂
  have hx₁1 : x₁ ≠ 1 := by
    rintro rfl
    exact hkx₁ (by simp)
  have hx₂1 : x₂ ≠ 1 := by
    rintro rfl
    exact hkx₂ (by simp)
  have hx₁y : y₁ ≠ x₁ := by
    intro e
    apply hkx₁
    rw [← e]
    exact conj_of_mem_mem hy₁ hk₁ (Or.inr rfl)
  have hx₂y : y₂ ≠ x₂ := by
    intro e
    apply hkx₂
    rw [← e]
    exact conj_of_mem_mem hy₂ hk₂ (Or.inr rfl)
  obtain ⟨g, hgy, hgx⟩ := h.exists_conj_pair hyD₁ hx₁ hyD₂ hx₂ hy₁.ne_one hx₁1 hy₂.ne_one hx₂1
    hx₁y hx₂y
  have T1 := h.dd_transport S ⟨hK₁, hk₁, hj₁, hkj₁, hx₁, hkx₁⟩ g
  rw [hgx] at T1
  obtain ⟨T1a, T1b⟩ := T1
  have hinv : IsUniqueInvolution (conjSub g K₁) y₂ := by
    have := hy₁.conj g
    rwa [hgy] at this
  have htw : K₂ ∈ twinSet Ω (conjSub g K₁) := ⟨hK₂, y₂, hinv, hy₂⟩
  obtain ⟨q, hq, hqK⟩ :=
    h.exists_pCore_conj_of_mem_twinSet (h.hyp.conjInvariant g K₁ hK₁) htw
  have hqx : q * x₂ * q⁻¹ = x₂ := by
    have hcomm : x₂ * q = q * x₂ :=
      Subgroup.mem_centralizer_iff.mp (h.pCore_le_centralizer_zGroup hq) x₂ hx₂
    rw [← hcomm, mul_inv_cancel_right]
  have T2 := h.dd_transport S T1a q
  rw [hqx, hqK] at T2
  obtain ⟨T2a, T2b⟩ := T2
  have T3 := h.dd_same_K S hb T2a ⟨hK₂, hk₂, hj₂, hkj₂, hx₂, hkx₂⟩
  rw [← T1b, ← T2b]
  exact T3

theorem exists_isTransport (S : TwinShift Ω) : ∃ π : Lab2 → Lab2, IsTransport S π := by
  classical
  refine ⟨fun b => if hb : ∃ m : Lab2, ∃ (K : Subgroup G) (k j x : G),
      DdAdm S b K k j x ∧ S.lam (k * j⁻¹) x = m then hb.choose else 0, ?_⟩
  unfold IsTransport
  intro b hb K hK k hk j hj hkj x hxD hkx
  have hadm : DdAdm S b K k j x := ⟨hK, hk, hj, hkj, hxD, hkx⟩
  have hex : ∃ m : Lab2, ∃ (K : Subgroup G) (k j x : G),
      DdAdm S b K k j x ∧ S.lam (k * j⁻¹) x = m :=
    ⟨S.lam (k * j⁻¹) x, K, k, j, x, hadm, rfl⟩
  simp only [dif_pos hex]
  obtain ⟨K', k', j', x', hadm', heq⟩ := hex.choose_spec
  rw [← heq]
  exact h.dd_label_eq S hb hadm hadm'

theorem lam_dewDelta_of_isTransport (S : TwinShift Ω) {π : Lab2 → Lab2} (hπ : IsTransport S π)
    {b : Lab2} (hb : b ≠ 0) {K : Subgroup G} {u : G} (hK : K ∈ Ω)
    (hu : IsUniqueInvolution K u) {φ : G → ZMod 2} (hφ : φ ∈ DE2Hyp.deq2Dual Ω) {k j : G}
    (hk : k ∈ K) (hj : j ∈ S.shift b K) (hkφ : IsElationOf Ω u φ k)
    (hkj : k * j⁻¹ ∈ pCore 2 G) (x : G) : S.lam (k * j⁻¹) x = φ x • π b := by
  by_cases hx : x ∈ zGroup Ω ∧ x ≠ 1
  · obtain ⟨hxD, hx1⟩ := hx
    obtain ⟨M, hM⟩ := h.exists_mem_dew1V hxD hx1
    rcases dd_zmod_two (φ x) with hφx | hφx
    · have hkx : k * x = x * k := by
        have e := hkφ x hxD
        rw [if_pos hφx] at e
        calc k * x = k * x * k⁻¹ * k := by group
          _ = x * k := by rw [e]
      have hact := h.dewDelta_act_of_commute (h.dd_twins S hb hK hu) hk hj hkj hxD hkx hM
      rw [(h.conjSub_eq_iff_lam_eq_zero S hkj hM).mp hact, hφx, zero_smul]
    · have hkx : k * x * k⁻¹ ≠ x := by
        rw [hkφ x hxD, if_neg (by rw [hφx]; exact one_ne_zero)]
        intro e
        exact hu.ne_one (mul_right_cancel (e.trans (one_mul x).symm))
      rw [hφx, one_smul]
      exact hπ b hb K hK k hk j hj hkj x hxD hkx
  · have hx' : x ∉ zGroup Ω ∨ x = 1 := by
      by_cases h1 : x = 1
      · exact Or.inr h1
      · exact Or.inl fun hD => hx ⟨hD, h1⟩
    have hφ0 : φ x = 0 := by
      rcases hx' with hx'' | hx''
      · exact hφ.2.1 x hx''
      · rw [hx'']
        exact hφ.1
    rw [h.lam_eq_zero_of_not_mem S hx', hφ0, zero_smul]

theorem lam_mem_dual (S : TwinShift Ω) {q : G} (hq : q ∈ pCore 2 G) : S.lam q ∈ dewDual2 Ω := by
  classical
  obtain ⟨π, hπ⟩ := h.exists_isTransport S
  have hadd : ∀ {q q' : G}, q ∈ pCore 2 G → q' ∈ pCore 2 G → S.lam q ∈ dewDual2 Ω →
      S.lam q' ∈ dewDual2 Ω → S.lam (q * q') ∈ dewDual2 Ω := by
    intro q q' hq hq' h1 h2
    refine ⟨?_, fun x hx => ?_, fun x hx y hy => ?_⟩
    · rw [h.lam_mul S hq hq', h1.1, h2.1, add_zero]
    · rw [h.lam_mul S hq hq', h1.2.1 x hx, h2.2.1 x hx, add_zero]
    · rw [h.lam_mul S hq hq', h.lam_mul S hq hq', h.lam_mul S hq hq', h1.2.2 x hx y hy,
        h2.2.2 x hx y hy]
      abel
  let H : Subgroup G :=
    { carrier := {q | q ∈ pCore 2 G ∧ S.lam q ∈ dewDual2 Ω}
      one_mem' := by
        refine ⟨(pCore 2 G).one_mem, ?_, fun x hx => ?_, fun x hx y hy => ?_⟩
        · rw [h.lam_one S]
        · rw [h.lam_one S]
        · simp only [h.lam_one S]; simp
      mul_mem' := fun ⟨hq, h1⟩ ⟨hq', h2⟩ => ⟨(pCore 2 G).mul_mem hq hq', hadd hq hq' h1 h2⟩
      inv_mem' := by
        rintro a ⟨ha, h1⟩
        refine ⟨(pCore 2 G).inv_mem ha, ?_⟩
        have : S.lam a⁻¹ = S.lam a := funext fun x => h.lam_inv S ha x
        rw [this]
        exact h1 }
  have hle : dewQstar Ω ≤ H := by
    refine iSup₂_le fun K hK => iSup₂_le fun J hJ x hx => ?_
    obtain ⟨hJΩ, u, hu, hJu⟩ := hJ
    by_cases hJK : J = K
    · subst hJK
      have hx' : x ∈ J ⊓ pCore 2 G := by simpa [dewDelta] using hx
      rw [h.inf_pCore hK hu] at hx'
      have hxD : x ∈ zGroup Ω :=
        (Subgroup.zpowers_le.mpr (dew1_involution_mem h.toDEHyp hK hu)) hx'
      have hxQ : x ∈ pCore 2 G := h.zGroup_le_pCore hxD
      refine ⟨hxQ, ?_⟩
      have : S.lam x = 0 := funext fun y => h.lam_of_mem_zGroup S hxD y
      rw [this]
      exact ⟨rfl, fun _ _ => rfl, fun _ _ _ _ => by simp⟩
    · have tw : DewTwins Ω K J u := ⟨hK, hJΩ, hu, hJu, fun h1 => hJK h1.symm⟩
      obtain ⟨k, hk, j, hj, hxkj, hxQ⟩ := (h.mem_dewDelta_iff tw).mp hx
      obtain ⟨b, hbJ, -⟩ := h.exists_unique_shift S hK ⟨hJΩ, u, hu, hJu⟩
      have hb : b ≠ 0 := by
        rintro rfl
        exact hJK (hbJ.symm.trans (S.shift_zero K hK))
      obtain ⟨φ, hφ, -, hkφ⟩ := h.exists_isElationOf hK hu hk
      refine ⟨hxQ, ?_⟩
      have hlam : ∀ y, S.lam x y = φ y • π b := by
        intro y
        rw [hxkj]
        exact h.lam_dewDelta_of_isTransport S hπ hb hK hu hφ hk (hbJ ▸ hj) hkφ (hxkj ▸ hxQ) y
      have : S.lam x = fun y => φ y • π b := funext hlam
      rw [this]
      refine ⟨by simp [hφ.1], fun y hy => by simp [hφ.2.1 y hy], fun y hy z hz => ?_⟩
      simp only [hφ.2.2 y hy z hz, add_smul]
  have := hle (h.dewQstar_eq_pCore ▸ hq)
  exact this.2

theorem isTransport_apply_eq (S : TwinShift Ω) {π : Lab2 → Lab2} (hπ : IsTransport S π)
    {b : Lab2} (hb : b ≠ 0) : π b = b := by
  obtain ⟨K, hK, -⟩ := h.exists_ne
  obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hu
  have hJ : S.shift b K ∈ twinSet Ω K := S.shift_mem b K hK
  obtain ⟨q, hq, hqK⟩ := h.exists_pCore_conj_of_mem_twinSet hK hJ
  have hqu : S.lam q u = b := by
    have h1 := h.lam_spec S hq (show K ∈ dew1V Ω u from ⟨hK, hu⟩)
    rw [hqK] at h1
    exact S.shift_injective hK h1.symm
  obtain ⟨k, hkK, hku⟩ : ∃ k ∈ K, k ∉ Subgroup.zpowers u := by
    by_contra hcon
    push Not at hcon
    have hle : K ≤ Subgroup.zpowers u := fun k hk => hcon k hk
    have h1 := Subgroup.card_le_of_le hle
    rw [h.card K hK, card_zpowers_of_involution hu.sq hu.ne_one] at h1
    omega
  obtain ⟨x, hxD, hkx⟩ : ∃ x ∈ zGroup Ω, k * x * k⁻¹ ≠ x := by
    by_contra hcon
    push Not at hcon
    have hkC : k ∈ K ⊓ Subgroup.centralizer (zGroup Ω : Set G) := by
      refine ⟨hkK, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
      have := hcon d hd
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [h.inf_centralizer_zGroup hK hu] at hkC
    exact hku hkC
  have hkxu : k * x * k⁻¹ = u * x := by
    rcases h.conj_eq_or_mul hK hu hkK hxD with h1 | h1
    · exact absurd h1 hkx
    · exact h1
  have hinv : k⁻¹ * x * k = u * x := by
    have hu' : k⁻¹ * u * k = u := by
      have := conj_of_mem_mem hu (K.inv_mem hkK) (Or.inr rfl)
      simpa using this
    have h1 : x = u * (k⁻¹ * x * k) := by
      calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
        _ = k⁻¹ * (u * x) * k := by rw [hkxu]
        _ = (k⁻¹ * u * k) * (k⁻¹ * x * k) := by group
        _ = u * (k⁻¹ * x * k) := by rw [hu']
    calc k⁻¹ * x * k = u * (u * (k⁻¹ * x * k)) := by rw [← mul_assoc, hu.sq, one_mul]
      _ = u * x := by rw [← h1]
  have hj₀ : q * k * q⁻¹ ∈ S.shift b K := by
    rw [← hqK]
    exact conj_mem_conjSub hkK
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  have hkq : k * q * k⁻¹ ∈ pCore 2 G := (inferInstance : (pCore 2 G).Normal).conj_mem q hq k
  have hδ : k * (q * k * q⁻¹)⁻¹ ∈ pCore 2 G := by
    have : k * (q * k * q⁻¹)⁻¹ = (k * q * k⁻¹) * q⁻¹ := by group
    rw [this]
    exact (pCore 2 G).mul_mem hkq ((pCore 2 G).inv_mem hq)
  have h1 := hπ b hb K hK k hkK (q * k * q⁻¹) hj₀ hδ x hxD hkx
  have h2 : S.lam (k * (q * k * q⁻¹)⁻¹) x = b := by
    have e : k * (q * k * q⁻¹)⁻¹ = (k * q * k⁻¹) * q⁻¹ := by group
    rw [e, h.lam_mul S hkq ((pCore 2 G).inv_mem hq), h.lam_inv S hq]
    have h3 := h.lam_conj S hq k (k⁻¹ * x * k)
    rw [show k * (k⁻¹ * x * k) * k⁻¹ = x by group] at h3
    rw [h3, hinv]
    have h4 := (h.lam_mem_dual S hq).2.2 u huD x hxD
    rw [h4, hqu]
    ext <;> simp [CharTwo.add_self_eq_zero, add_assoc]
  rw [← h1]
  exact h2

theorem lam_dewDelta (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G} {u : G}
    (hK : K ∈ Ω) (hu : IsUniqueInvolution K u) {φ : G → ZMod 2}
    (hφ : φ ∈ DE2Hyp.deq2Dual Ω) {k j : G} (hk : k ∈ K) (hj : j ∈ S.shift b K)
    (hkφ : IsElationOf Ω u φ k) (hkj : k * j⁻¹ ∈ pCore 2 G) (x : G) :
    S.lam (k * j⁻¹) x = φ x • b := by
  obtain ⟨π, hπ⟩ := h.exists_isTransport S
  rw [h.lam_dewDelta_of_isTransport S hπ hb hK hu hφ hk hj hkφ hkj x,
    h.isTransport_apply_eq S hπ hb]

theorem lam_dewDelta_range (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G} {u : G}
    (hK : K ∈ Ω) (hu : IsUniqueInvolution K u) :
    (∀ q ∈ dewDelta K (S.shift b K), ∃ f ∈ DE2Hyp.deq2Dual Ω, f u = 0 ∧
        ∀ x, S.lam q x = f x • b) ∧
      (∀ f ∈ DE2Hyp.deq2Dual Ω, f u = 0 → ∃ q ∈ dewDelta K (S.shift b K),
        ∀ x, S.lam q x = f x • b) := by
  have tw := h.dd_twins S hb hK hu
  constructor
  · intro q hq
    obtain ⟨k, hk, j, hj, rfl, hkj⟩ := (h.mem_dewDelta_iff tw).mp hq
    obtain ⟨φ, hφ, hφu, hkφ⟩ := h.exists_isElationOf hK hu hk
    exact ⟨φ, hφ, hφu, fun x => h.lam_dewDelta S hb hK hu hφ hk hj hkφ hkj x⟩
  · intro f hf hfu
    obtain ⟨k, hk, hkφ⟩ := h.exists_mem_isElationOf hK hu hf hfu
    obtain ⟨j, hj, hkj⟩ := h.exists_partner tw hk
    exact ⟨k * j⁻¹, (h.mem_dewDelta_iff tw).mpr ⟨k, hk, j, hj, rfl, hkj⟩,
      fun x => h.lam_dewDelta S hb hK hu hf hk hj hkφ hkj x⟩

theorem dewDelta_inf_zGroup {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u) :
    dewDelta K J ⊓ zGroup Ω = Subgroup.zpowers u := by
  obtain ⟨S⟩ := h.exists_twinShift
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp tw.memK tw.invK
  apply le_antisymm
  · rintro x ⟨hxΔ, hxD⟩
    obtain ⟨k, hk, j, hj, rfl, hkjQ⟩ := (h.mem_dewDelta_iff tw).mp hxΔ
    have hJtw : J ∈ twinSet Ω K := ⟨tw.memJ, u, tw.invK, tw.invJ⟩
    obtain ⟨b, hbJ, -⟩ := h.exists_unique_shift S tw.memK hJtw
    subst hbJ
    have hb : b ≠ 0 := by
      rintro rfl
      exact tw.ne (S.shift_zero K tw.memK).symm
    obtain ⟨φ, hφ, -, hkφ⟩ := h.exists_isElationOf tw.memK tw.invK hk
    have hlam : ∀ y ∈ zGroup Ω, φ y • b = 0 := fun y hy => by
      rw [← h.lam_dewDelta S hb tw.memK tw.invK hφ hk hj hkφ hkjQ y]
      exact h.lam_of_mem_zGroup S hxD y
    have hφ0 : ∀ y ∈ zGroup Ω, φ y = 0 := fun y hy => by
      rcases dd_zmod_two (φ y) with h0 | h1
      · exact h0
      · exfalso
        apply hb
        have := hlam y hy
        rw [h1, one_smul] at this
        exact this
    have hkC : k ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
      have e := hkφ d hd
      rw [if_pos (hφ0 d hd)] at e
      exact (calc k * d = (k * d * k⁻¹) * k := by group
        _ = d * k := by rw [e]).symm
    have hkK : k ∈ K ⊓ Subgroup.centralizer (zGroup Ω : Set G) := ⟨hk, hkC⟩
    rw [h.inf_centralizer_zGroup tw.memK tw.invK] at hkK
    have hkD : k ∈ zGroup Ω := (Subgroup.zpowers_le.mpr huD) hkK
    have hj' : j⁻¹ ∈ zGroup Ω := by
      have := (zGroup Ω).mul_mem ((zGroup Ω).inv_mem hkD) hxD
      simpa using this
    have hjD : j ∈ zGroup Ω := by
      simpa using (zGroup Ω).inv_mem hj'
    have hjJ : j ∈ S.shift b K ⊓ Subgroup.centralizer (zGroup Ω : Set G) :=
      ⟨hj, Subgroup.mem_centralizer_iff.mpr fun d hd => h.zGroup_comm d hd j hjD⟩
    rw [h.inf_centralizer_zGroup tw.memJ tw.invJ] at hjJ
    exact (Subgroup.zpowers u).mul_mem hkK ((Subgroup.zpowers u).inv_mem hjJ)
  · intro x hx
    exact ⟨h.zpowers_le_dewDelta tw hx, (Subgroup.zpowers_le.mpr huD) hx⟩

theorem exists_involution_ker {f g : G → ZMod 2} (hf : f ∈ DE2Hyp.deq2Dual Ω)
    (hg : g ∈ DE2Hyp.deq2Dual Ω) : ∃ u ∈ zGroup Ω, u ≠ 1 ∧ f u = 0 ∧ g u = 0 := by
  obtain ⟨e, he⟩ := h.exists_basis
  obtain ⟨v, hv0, hfv, hgv⟩ := dd_fin_common_zero (fun i => f (e i)) (fun i => g (e i))
  have hdot : ∀ φ : G → ZMod 2, φ ∈ DE2Hyp.deq2Dual Ω → ∀ w : Fin 3 → ZMod 2,
      φ (TL4.e8Coord e w) = dotProduct (fun i => φ (e i)) w := by
    intro φ hφ w
    rw [dd_expand he hφ.1 (fun a ha b hb => hφ.2.2 a ha b hb) w]
    unfold dotProduct
    exact Finset.sum_congr rfl fun i _ => by simp only [smul_eq_mul]; ring
  refine ⟨TL4.e8Coord e v, TL4.e8Coord_mem he v, ?_, ?_, ?_⟩
  · intro h1
    apply hv0
    apply TL4.e8Coord_injective he
    rw [h1, TL4.e8Coord_zero]
  · rw [hdot f hf v]
    exact hfv
  · rw [hdot g hg v]
    exact hgv

theorem exists_dual_ne {x y : G} (hx : x ∈ zGroup Ω) (hy : y ∈ zGroup Ω) (hxy : x ≠ y) :
    ∃ f ∈ DE2Hyp.deq2Dual Ω, f x ≠ f y := by
  classical
  obtain ⟨e, he⟩ := h.exists_basis
  have hne : dd_coord he x ≠ dd_coord he y := by
    intro hc
    apply hxy
    rw [← dd_coord_spec he hx, ← dd_coord_spec he hy, hc]
  obtain ⟨i, hi⟩ : ∃ i, dd_coord he x i ≠ dd_coord he y i := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  refine ⟨fun z => if z ∈ zGroup Ω then dd_coord he z i else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp [dd_coord_one he]
  · intro z hz
    simp [hz]
  · intro a ha b hb
    have hab := (zGroup Ω).mul_mem ha hb
    simp only [if_pos ha, if_pos hb, if_pos hab, dd_coord_mul he ha hb, Pi.add_apply]
  · simp only [if_pos hx, if_pos hy]
    exact hi

theorem lam_surj (S : TwinShift Ω) {F : G → Lab2} (hF : F ∈ dewDual2 Ω) :
    ∃ q ∈ pCore 2 G, ∀ x, S.lam q x = F x := by
  have hgen : ∀ f ∈ DE2Hyp.deq2Dual Ω, ∀ b : Lab2, b ≠ 0 →
      ∃ q ∈ pCore 2 G, ∀ x, S.lam q x = f x • b := by
    intro f hf b hb
    obtain ⟨u, huD, hu1, hfu, -⟩ := h.exists_involution_ker hf hf
    obtain ⟨K, hK⟩ := h.exists_mem_dew1V huD hu1
    obtain ⟨q, hq, hqx⟩ := (h.lam_dewDelta_range S hb hK.1 hK.2).2 f hf hfu
    exact ⟨q, dewDelta_le_pCore K _ hq, hqx⟩
  have h1 : (fun x => (F x).1) ∈ DE2Hyp.deq2Dual Ω := by
    refine ⟨?_, fun x hx => ?_, fun x hx y hy => ?_⟩
    · simp [hF.1]
    · simp [hF.2.1 x hx]
    · simp [hF.2.2 x hx y hy]
  have h2 : (fun x => (F x).2) ∈ DE2Hyp.deq2Dual Ω := by
    refine ⟨?_, fun x hx => ?_, fun x hx y hy => ?_⟩
    · simp [hF.1]
    · simp [hF.2.1 x hx]
    · simp [hF.2.2 x hx y hy]
  obtain ⟨q₁, hq₁, hq₁x⟩ := hgen _ h1 (1, 0) (by decide)
  obtain ⟨q₂, hq₂, hq₂x⟩ := hgen _ h2 (0, 1) (by decide)
  refine ⟨q₁ * q₂, (pCore 2 G).mul_mem hq₁ hq₂, fun x => ?_⟩
  rw [h.lam_mul S hq₁ hq₂ x, hq₁x x, hq₂x x]
  ext <;> simp

theorem card_pCore_eq : Nat.card (pCore 2 G) = 512 := by
  classical
  obtain ⟨S⟩ := h.exists_twinShift
  obtain ⟨e, he⟩ := h.exists_basis
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : pCore 2 G →* Multiplicative (Fin 3 → Lab2),
      ∀ q : pCore 2 G, Λ q = Multiplicative.ofAdd (fun i => S.lam (q : G) (e i)) :=
    ⟨{ toFun := fun q => Multiplicative.ofAdd (fun i => S.lam (q : G) (e i))
       map_one' := by
         simp only [Subgroup.coe_one, h.lam_one S]
         rfl
       map_mul' := fun q q' => by
         simp only [Subgroup.coe_mul, h.lam_mul S q.2 q'.2]
         rfl }, fun q => rfl⟩
  have hkerIff : ∀ q : pCore 2 G, Λ q = 1 ↔ (q : G) ∈ zGroup Ω := by
    intro q
    rw [hΛ, ofAdd_eq_one]
    constructor
    · intro hz
      rw [← h.lam_eq_zero_iff S q.2]
      intro x
      by_cases hx : x ∈ zGroup Ω
      · obtain ⟨v, rfl⟩ := TL4.exists_e8Coord_eq he hx
        have hexp := dd_expand he (F := fun y => S.lam (q : G) y) (h.lam_mem_dual S q.2).1
          (fun a ha b hb => (h.lam_mem_dual S q.2).2.2 a ha b hb) v
        have hz' : ∀ i, S.lam (q : G) (e i) = 0 := fun i => congrFun hz i
        simp only [hz', smul_zero, Finset.sum_const_zero] at hexp
        exact hexp
      · exact h.lam_eq_zero_of_not_mem S (Or.inl hx)
    · intro hq
      funext i
      exact h.lam_of_mem_zGroup S hq (e i)
  have hsurj : Function.Surjective Λ := by
    intro w
    obtain ⟨F, hF, hFe⟩ : ∃ F ∈ dewDual2 Ω, ∀ i, F (e i) = Multiplicative.toAdd w i := by
      refine ⟨fun x => if x ∈ zGroup Ω then
          ∑ i, (dd_coord he x i) • Multiplicative.toAdd w i else 0, ⟨?_, ?_, ?_⟩, ?_⟩
      · simp [dd_coord_one he]
      · intro x hx
        simp [hx]
      · intro a ha b hb
        have hab := (zGroup Ω).mul_mem ha hb
        simp only [if_pos ha, if_pos hb, if_pos hab, dd_coord_mul he ha hb, Pi.add_apply,
          add_smul, Finset.sum_add_distrib]
      · intro i
        simp [he.mem i, dd_coord_single he i]
    obtain ⟨q, hq, hqF⟩ := h.lam_surj S hF
    refine ⟨⟨q, hq⟩, ?_⟩
    rw [hΛ]
    show Multiplicative.ofAdd (fun i => S.lam q (e i)) = w
    have hfun : (fun i => S.lam q (e i)) = Multiplicative.toAdd w := funext fun i => by
      rw [hqF, hFe i]
    rw [hfun]
    rfl
  have hmem : ∀ x : Λ.ker, ((x : pCore 2 G) : G) ∈ zGroup Ω := fun x =>
    (hkerIff _).mp (MonoidHom.mem_ker.mp x.2)
  have hkerCard : Nat.card Λ.ker = 8 := by
    have e1 : Nat.card Λ.ker = Nat.card ↥(zGroup Ω) := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun x : Λ.ker => (⟨((x : pCore 2 G) : G), hmem x⟩ : ↥(zGroup Ω))) ⟨?_, ?_⟩)
      · intro x y hxy
        simp only [Subtype.mk.injEq] at hxy
        exact Subtype.ext (Subtype.ext hxy)
      · intro z
        exact ⟨⟨⟨z.1, h.zGroup_le_pCore z.2⟩, MonoidHom.mem_ker.mpr ((hkerIff _).mpr z.2)⟩, rfl⟩
    rw [e1, h.card_zGroup]
  have hidx : Λ.ker.index = 64 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    show Nat.card (Fin 3 → Lab2) = 64
    simp [Nat.card_pi, Fin.prod_univ_three, Nat.card_prod, Nat.card_zmod]
  rw [← Subgroup.card_mul_index Λ.ker, hkerCard, hidx]

end DE4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
