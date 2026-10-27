module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutSemilinear
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutGalois

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.UnitaryThreeRecognition.Model

section Generic

variable {K : Type} [Field K] [Finite K]

theorem card_le_card_fixed {W : Type*} (g : W → K) (hg : Function.Injective g) (τ : K ≃+* K)
    (h : ∀ w w', g w' ≠ 0 → τ (g w / g w') = g w / g w') :
    Nat.card W ≤ Nat.card {x : K // τ x = x} := by
  have : Finite W := Finite.of_injective g hg
  have hpos : 0 < Nat.card {x : K // τ x = x} :=
    Nat.card_pos_iff.2 ⟨⟨⟨0, map_zero τ⟩⟩, inferInstance⟩
  by_cases hz : ∃ w₀, g w₀ ≠ 0
  · obtain ⟨w₀, hw₀⟩ := hz
    refine Nat.card_le_card_of_injective (fun w => ⟨g w / g w₀, h w w₀ hw₀⟩) ?_
    intro w w' hww'
    have := congrArg Subtype.val hww'
    exact hg ((div_left_inj' hw₀).1 this)
  · push Not at hz
    have hsub : Subsingleton W := ⟨fun w w' => hg ((hz w).trans (hz w').symm)⟩
    have : Nat.card W ≤ 1 := by
      rcases isEmpty_or_nonempty W with hW | hW
      · simp
      · exact (Nat.card_eq_one_iff_unique.2 ⟨hsub, hW⟩).le
    omega

end Generic

section RootAbelian

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

omit [Finite K] [Fact p.Prime] in
theorem fstAdd_rootCoord (z : Coord J) : fstAdd J hJ (rootCoord J hJ z) = z.1.1 := by
  have : rootCoord J hJ z = ⟨root J hJ z, root_mem_rootGroup J hJ z⟩ := Subtype.ext rfl
  show Multiplicative.toAdd (fstHom J hJ (rootCoord J hJ z)) = z.1.1
  rw [this, fstHom_root]
  rfl

omit [Finite K] [Fact p.Prime] in
theorem fstAdd_comm_of_comm {u v : ↥(rootGroup J hJ)} (h : u * v = v * u) :
    fstAdd J hJ u * J.conj (fstAdd J hJ v) = fstAdd J hJ v * J.conj (fstAdd J hJ u) := by
  obtain ⟨z, rfl⟩ := (rootCoord J hJ).surjective u
  obtain ⟨w, rfl⟩ := (rootCoord J hJ).surjective v
  rw [← map_mul, ← map_mul] at h
  have h2 := (rootCoord J hJ).injective h
  have h3 := congrArg (fun y : Coord J => (y : K × K).2) h2
  simp only [coord_mul_val] at h3
  rw [fstAdd_rootCoord, fstAdd_rootCoord]
  linear_combination (-1) * h3

omit [Finite K] [Fact p.Prime] in
theorem fstAdd_eq_zero_of_sq_eq_one [CharP K 2] (u : ↥(rootGroup J hJ)) (hu : u ^ 2 = 1) :
    fstAdd J hJ u = 0 := by
  obtain ⟨z, rfl⟩ := (rootCoord J hJ).surjective u
  have h1 : z ^ 2 = 1 := (rootCoord J hJ).injective (by rw [map_pow, hu, map_one])
  have h2 := congrArg (fun y : Coord J => (y : K × K).2) h1
  simp only [pow_two, coord_mul_val, coord_one_val] at h2
  have h3 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h4 : z.1.1 * J.conj z.1.1 = 0 := by linear_combination (-1) * h2 + z.1.2 * h3
  rw [fstAdd_rootCoord]
  rcases mul_eq_zero.1 h4 with h | h
  · exact h
  · exact (map_eq_zero_iff J.conj J.conj.injective).1 h

omit [Fact p.Prime] in
include hfix in
theorem card_range_fst_le_of_comm (D : Subgroup ↥(rootGroup J hJ))
    (hD : ∀ u ∈ D, ∀ v ∈ D, u * v = v * u) :
    Nat.card ((fstHom J hJ).comp D.subtype).range ≤ p ^ f := by
  rw [← hfix]
  refine card_le_card_fixed
    (fun m : ↥((fstHom J hJ).comp D.subtype).range => Multiplicative.toAdd (m : Multiplicative K))
    ?_ J.conj ?_
  · intro m m' h
    exact Subtype.ext (Multiplicative.toAdd.injective h)
  · rintro ⟨_, ⟨⟨u, hu⟩, rfl⟩⟩ ⟨_, ⟨⟨v, hv⟩, rfl⟩⟩ hne
    change J.conj (fstAdd J hJ u / fstAdd J hJ v) = fstAdd J hJ u / fstAdd J hJ v
    change fstAdd J hJ v ≠ 0 at hne
    have hcomm := fstAdd_comm_of_comm J hJ (hD u hu v hv)
    have hc' : J.conj (fstAdd J hJ v) ≠ 0 := (map_ne_zero J.conj).2 hne
    rw [map_div₀, div_eq_div_iff hc' hne]
    linear_combination (-1) * hcomm

omit [Fact p.Prime] in
theorem card_range_fst_le_of_fixed (D : Subgroup ↥(rootGroup J hJ)) (c : K) (hc : c ≠ 0)
    (σ : K ≃+* K) (hD : ∀ u ∈ D, c * σ (fstAdd J hJ u) = fstAdd J hJ u) :
    Nat.card ((fstHom J hJ).comp D.subtype).range ≤ Nat.card {x : K // σ x = x} := by
  refine card_le_card_fixed
    (fun m : ↥((fstHom J hJ).comp D.subtype).range => Multiplicative.toAdd (m : Multiplicative K))
    ?_ σ ?_
  · intro m m' h
    exact Subtype.ext (Multiplicative.toAdd.injective h)
  · rintro ⟨_, ⟨⟨u, hu⟩, rfl⟩⟩ ⟨_, ⟨⟨v, hv⟩, rfl⟩⟩ hne
    change σ (fstAdd J hJ u / fstAdd J hJ v) = fstAdd J hJ u / fstAdd J hJ v
    change fstAdd J hJ v ≠ 0 at hne
    have h1 := hD u hu
    have h2 := hD v hv
    have hσu : σ (fstAdd J hJ u) = fstAdd J hJ u / c := by
      rw [eq_div_iff hc, mul_comm]
      exact h1
    have hσv : σ (fstAdd J hJ v) = fstAdd J hJ v / c := by
      rw [eq_div_iff hc, mul_comm]
      exact h2
    rw [map_div₀, hσu, hσv]
    field_simp

include hK hfix

theorem card_ker_fstHom : Nat.card (fstHom J hJ).ker = p ^ f := by
  have h1 := Subgroup.card_ker_mul_card_range (fstHom J hJ)
  have hrange : (fstHom J hJ).range = ⊤ :=
    MonoidHom.range_eq_top.2 (fstHom_surjective J hJ hK hfix)
  rw [hrange, Subgroup.card_top, card_rootGroup_eq J hJ hK hfix] at h1
  have h2 : Nat.card (Multiplicative K) = (p ^ f) ^ 2 := by
    rw [← hK]
    exact Nat.card_congr Multiplicative.toAdd
  rw [h2] at h1
  have h3 : p ^ (3 * f) = p ^ f * (p ^ f) ^ 2 := by ring
  rw [h3] at h1
  have hpos : 0 < (p ^ f) ^ 2 := pow_pos (pow_pos (Fact.out : p.Prime).pos _) _
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem card_le_mul_card_range (D : Subgroup ↥(rootGroup J hJ)) :
    Nat.card D ≤ p ^ f * Nat.card ((fstHom J hJ).comp D.subtype).range := by
  have h1 := Subgroup.card_ker_mul_card_range ((fstHom J hJ).comp D.subtype)
  have h2 : Nat.card ((fstHom J hJ).comp D.subtype).ker ≤ p ^ f := by
    rw [← card_ker_fstHom J hJ hK hfix]
    have hle : (((fstHom J hJ).comp D.subtype).ker).map D.subtype ≤ (fstHom J hJ).ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective D.subtype_injective] at this
  rw [← h1]
  exact Nat.mul_le_mul_right _ h2

end RootAbelian

section Main

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hJ hK hfix

theorem conj_injective (hq : 2 < p ^ f) :
    Function.Injective (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →*
      MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have hcenter := center_eq_bot J hJ hK hfix hq
  intro g h hgh
  have hc : g⁻¹ * h ∈ Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have key : h * x * h⁻¹ = g * x * g⁻¹ := by
      have := DFunLike.congr_fun hgh x
      simpa [MulAut.conj_apply] using this.symm
    calc x * (g⁻¹ * h) = g⁻¹ * (g * x * g⁻¹) * h := by group
      _ = g⁻¹ * (h * x * h⁻¹) * h := by rw [key]
      _ = g⁻¹ * h * x := by group
  rw [hcenter, Subgroup.mem_bot] at hc
  exact inv_mul_eq_one.1 hc

theorem card_elemAbelian_le (hq : 2 < p ^ f)
    (E : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hE : CFSG.Open.IsElemAbelian p E)
    (hER : ∀ α ∈ E, ∀ r ∈ rootGroup J hJ, α r ∈ rootGroup J hJ) :
    Nat.card E ≤ p ^ (2 * f) := by
  have hp : p.Prime := Fact.out
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hcharP : CharP K p := charP_of_card hp hK
  have hinj := conj_injective J hJ hK hfix hq
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have h1 : E ≤ Subgroup.centralizer (E : Set _) :=
      Subgroup.le_centralizer_iff_isMulCommutative.2 hE.1
    exact Subgroup.mem_centralizer_iff.1 (h1 hy) x hx
  have hEp : IsPGroup p E := fun x => ⟨1, by
    have : (x : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ^ p = 1 := hE.2 x x.2
    exact Subtype.ext (by simpa using this)⟩
  obtain ⟨φ, c, hrel, hker⟩ := exists_semilinear_hom J hJ hK hfix hq E hEp hER
  let Cj : ↥(rootGroup J hJ) →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).comp (rootGroup J hJ).subtype
  let D : Subgroup ↥(rootGroup J hJ) := E.comap Cj
  have hCjinj : Function.Injective Cj := fun u v h => Subtype.ext (hinj h)
  have hDcomm : ∀ u ∈ D, ∀ v ∈ D, u * v = v * u := by
    intro u hu v hv
    apply hCjinj
    rw [map_mul, map_mul]
    exact hcomm _ (Subgroup.mem_comap.1 hu) _ (Subgroup.mem_comap.1 hv)
  have hDexp : ∀ u ∈ D, u ^ p = 1 := by
    intro u hu
    apply hCjinj
    rw [map_pow, map_one]
    exact hE.2 _ (Subgroup.mem_comap.1 hu)
  have hker_le : Nat.card φ.ker ≤ Nat.card D := card_ker_le_card_comap J hJ E φ hker
  have hrange_le : Nat.card φ.range ≤ p := by
    have : IsCyclic (K ≃+* K) := isCyclic_ringEquiv K p
    have : Finite (K ≃+* K) := finite_ringEquiv K
    refine card_le_of_pow_eq_one φ.range hp.pos ?_
    rintro _ ⟨α, rfl⟩
    rw [← map_pow]
    have : α ^ p = 1 := Subtype.ext (hE.2 α α.2)
    rw [this, map_one]
  have hEcard : Nat.card E = Nat.card φ.ker * Nat.card φ.range :=
    (Subgroup.card_ker_mul_card_range φ).symm
  have hD_le := card_le_mul_card_range J hJ hK hfix D
  have hq' : p ^ (2 * f) = p ^ f * p ^ f := by rw [two_mul, pow_add]
  by_cases hp2 : p = 2
  · subst hp2
    have : CharP K 2 := hcharP
    have hFtriv : Nat.card ((fstHom J hJ).comp D.subtype).range = 1 := by
      have : ((fstHom J hJ).comp D.subtype).range = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨⟨u, hu⟩, rfl⟩
        have h0 := fstAdd_eq_zero_of_sq_eq_one J hJ u (hDexp u hu)
        show fstHom J hJ u = 1
        exact toAdd_eq_zero.1 h0
      rw [this]
      exact Subgroup.card_bot
    rw [hFtriv, mul_one] at hD_le
    calc Nat.card E = Nat.card φ.ker * Nat.card φ.range := hEcard
      _ ≤ Nat.card D * 2 := Nat.mul_le_mul hker_le hrange_le
      _ ≤ 2 ^ f * 2 := Nat.mul_le_mul_right 2 hD_le
      _ = 2 ^ (f + 1) := by ring
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    by_cases hφ : ∀ α : E, φ α = 1
    · have hr1 : Nat.card φ.range = 1 := by
        have : φ.range = ⊥ := by
          rw [eq_bot_iff]
          rintro _ ⟨α, rfl⟩
          exact hφ α
        rw [this]
        exact Subgroup.card_bot
      have hFle := card_range_fst_le_of_comm J hJ hfix D hDcomm
      calc Nat.card E = Nat.card φ.ker * Nat.card φ.range := hEcard
        _ ≤ Nat.card D * 1 := by rw [hr1]; exact Nat.mul_le_mul_right 1 hker_le
        _ ≤ p ^ f * Nat.card ((fstHom J hJ).comp D.subtype).range := by rw [mul_one]; exact hD_le
        _ ≤ p ^ f * p ^ f := Nat.mul_le_mul_left _ hFle
        _ = p ^ (2 * f) := hq'.symm
    · push Not at hφ
      obtain ⟨e, he⟩ := hφ
      set σ := φ e with hσ
      have hσp : σ ^ p = 1 := by
        rw [hσ, ← map_pow]
        have : e ^ p = 1 := Subtype.ext (hE.2 e e.2)
        rw [this, map_one]
      have hfix_e : ∀ u ∈ D, (c e : K) * σ (fstAdd J hJ u) = fstAdd J hJ u := by
        intro u hu
        have h1 : (e : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) * Cj u = Cj u * e :=
          hcomm _ e.2 _ (Subgroup.mem_comap.1 hu)
        have h2 : MulAut.conj ((e : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
            (u : ProjectiveSpecialUnitaryMatrixGroup J)) =
            MulAut.conj (u : ProjectiveSpecialUnitaryMatrixGroup J) := by
          have h3 : (e : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) *
              MulAut.conj (u : ProjectiveSpecialUnitaryMatrixGroup J) *
              (e : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))⁻¹ =
              MulAut.conj ((e : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
                (u : ProjectiveSpecialUnitaryMatrixGroup J)) := by
            ext x
            simp [MulAut.conj_apply, MulAut.mul_apply]
          rw [← h3]
          have h4 : (e : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) *
              MulAut.conj (u : ProjectiveSpecialUnitaryMatrixGroup J) =
              MulAut.conj (u : ProjectiveSpecialUnitaryMatrixGroup J) * e := h1
          rw [h4, mul_inv_cancel_right]
        have h5 := hinj h2
        have h6 := hrel e u
        have h7 : (⟨(e : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
            (u : ProjectiveSpecialUnitaryMatrixGroup J), hER e e.2 u u.2⟩ :
            ↥(rootGroup J hJ)) = u := Subtype.ext h5
        rw [h7] at h6
        exact h6.symm
      have hFfix := card_range_fst_le_of_fixed J hJ D (c e : K) (c e).ne_zero σ hfix_e
      have hKcard := card_eq_pow_card_fixed K σ p he hσp
      set m := Nat.card {x : K // σ x = x} with hm
      rw [hK] at hKcard
      have hmdvd : m ∣ p ^ (2 * f) := by
        have h1 : m ∣ m ^ p := dvd_pow_self m hp.ne_zero
        rw [← hKcard] at h1
        rwa [← pow_mul, mul_comm] at h1
      obtain ⟨g, -, hmg⟩ := (Nat.dvd_prime_pow hp).1 hmdvd
      have hgp : g * p = 2 * f := by
        have h1 : p ^ (f * 2) = p ^ (g * p) := by
          rw [pow_mul, hKcard, hmg, pow_mul]
        have := Nat.pow_right_injective hp.two_le h1
        omega
      have hpf : p ∣ f := by
        have h1 : p ∣ 2 * f := Dvd.intro_left g hgp
        rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
        · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
        · exact h
      obtain ⟨f', hf'⟩ := hpf
      have hg2 : g = 2 * f' := by
        have h1 : g * p = (2 * f') * p := by rw [hgp, hf']; ring
        exact Nat.eq_of_mul_eq_mul_right hp.pos h1
      have hf'1 : 1 ≤ f' := by
        rcases Nat.eq_zero_or_pos f' with h | h
        · rw [h] at hf'
          omega
        · exact h
      calc Nat.card E = Nat.card φ.ker * Nat.card φ.range := hEcard
        _ ≤ Nat.card D * p := Nat.mul_le_mul hker_le hrange_le
        _ ≤ (p ^ f * Nat.card ((fstHom J hJ).comp D.subtype).range) * p :=
          Nat.mul_le_mul_right p hD_le
        _ ≤ (p ^ f * m) * p := Nat.mul_le_mul_right p (Nat.mul_le_mul_left _ hFfix)
        _ = p ^ (f + g + 1) := by rw [hmg]; ring
        _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right hp.pos (by nlinarith)

end Main

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding

open CFSG.UnitaryThreeRecognition.Model (rootGroup)

theorem kFactUnitaryAutElemRank : KFactUnitaryAutElemRank := by
  intro L _ _ p _ d hd h E hE
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  have hEp : IsPGroup p E := fun x => ⟨1, by
    have : (x : MulAut L) ^ p = 1 := hE.2 x x.2
    exact Subtype.ext (by simpa using this)⟩
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_stable_rootGroup J hJ hK hfix hf e E hEp
  have hE' : CFSG.Open.IsElemAbelian p (E.map (MulAut.congr e').toMonoidHom) :=
    (UnitaryModel.isElemAbelian_map_iff (MulAut.congr e') E).2 hE
  have hcard : Nat.card (E.map (MulAut.congr e').toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (f := (MulAut.congr e').toMonoidHom) (MulAut.congr e').injective
  rw [← hcard]
  exact UnitaryModel.card_elemAbelian_le J hJ hK hfix hq _ hE' he'

end CFSG.AGLEmbedding
