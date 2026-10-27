module

public import CFSG.ClassicalGroups.Orthogonal.SiegelSLStar
import CFSG.Quasithin.Background.G1Module

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelSL

open CFSG.ClassicalGroups.Orthogonal.SiegelRT1 CFSG.HardMathSupport.Kantor79 CFSG.CGT.Timmesfeld75
open CFSG.CGT.T75E QuadraticMap Module Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {m' : ℕ} {Qf : QuadraticForm K V} {ρ : SL(m' + 2, K) →* (V ≃ₗ[K] V)}

omit [CharP K 2] [Finite K] in
private theorem single_zero_one_ne_zero :
    (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp at h0

omit [CharP K 2] [Finite K] in
private theorem exists_mulVec_single_zero_eq {x : Fin (m' + 2) → K} (hx : x ≠ 0) :
    ∃ g : SL(m' + 2, K), (g : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K) *ᵥ
      (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K) = x := by
  obtain ⟨g, hg⟩ := CFSG.Quasithin.G1.exists_smul_single_eq (by omega : 2 ≤ m' + 2) 0 hx
  exact ⟨g, by rwa [CFSG.Quasithin.G1.smul_eq_mulVec'] at hg⟩

private theorem exists_span_eq_axisInf (hs : SLSetting Qf ρ)
    (hst : IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ)) :
    ∃ r : V, r ≠ 0 ∧ axisInf ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ) =
      Submodule.span K {r} := by
  have h1 := (hs.axisInf_center_of_isStar single_zero_one_ne_zero hst).1
  have hbot : axisInf ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ) ≠ ⊥ :=
    fun h => by rw [h, finrank_bot] at h1; omega
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨r, hr0, (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm⟩
  · exact (Submodule.span_singleton_le_iff_mem r _).mpr hr
  · rw [h1, finrank_span_singleton hr0]

theorem SLSetting.exists_equivariant_of_isStar (hs : SLSetting Qf ρ)
    (hst : IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ)) :
    ∃ F : (Fin (m' + 2) → K) → V, F 0 = 0 ∧
      (∀ (g : SL(m' + 2, K)) x, F ((g : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K) *ᵥ x) =
        ρ g (F x)) ∧
      ∀ x : Fin (m' + 2) → K, x ≠ 0 →
        F x ≠ 0 ∧ axisInf ((tvCenterSL x).map ρ) = Submodule.span K {F x} := by
  classical
  obtain ⟨r, hr0, hrP⟩ := exists_span_eq_axisInf hs hst
  let F : (Fin (m' + 2) → K) → V := fun x =>
    if hx : x = 0 then 0 else ρ (Classical.choose (exists_mulVec_single_zero_eq hx)) r
  have hF0 : F 0 = 0 := by simp [F]
  have key : ∀ g : SL(m' + 2, K), F ((g : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K) *ᵥ
      (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K)) = ρ g r := by
    intro g
    have hga := mulVec_ne_zero' g (single_zero_one_ne_zero (K := K) (m' := m'))
    show (if hx : (g : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K) *ᵥ
      (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K) = 0 then 0
      else ρ (Classical.choose (exists_mulVec_single_zero_eq hx)) r) = ρ g r
    rw [dif_neg hga]
    set g' := Classical.choose (exists_mulVec_single_zero_eq hga) with hg'def
    have hg' := Classical.choose_spec (exists_mulVec_single_zero_eq hga)
    have hfix : ((g'⁻¹ * g : SL(m' + 2, K)) : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K) *ᵥ
        (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K) =
        (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← hg', inv_mulVec_mulVec']
    have h2 : ρ (g'⁻¹ * g) r = r := hs.apply_eq_self_of_mulVec_eq hst hfix
      (hrP ▸ Submodule.mem_span_singleton_self r)
    calc ρ g' r = ρ g' (ρ (g'⁻¹ * g) r) := by rw [h2]
      _ = ρ g r := by rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]
  refine ⟨F, hF0, fun g x => ?_, fun x hx => ?_⟩
  · by_cases hx : x = 0
    · subst hx
      rw [Matrix.mulVec_zero, hF0, map_zero]
    · obtain ⟨k, rfl⟩ := exists_mulVec_single_zero_eq hx
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, key (g * k), key k, map_mul]
      rfl
  · obtain ⟨k, rfl⟩ := exists_mulVec_single_zero_eq hx
    rw [key k]
    refine ⟨fun h => hr0 ((map_eq_zero_iff _ (ρ k).injective).mp h), ?_⟩
    rw [axisInf_map_center_mulVec, hrP, Submodule.map_span, Set.image_singleton]
    rfl

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem polar_eq_zero_of_mem_span {u v : V} (huv : polar Qf u v = 0) {x y : V}
    (hx : x ∈ Submodule.span K {u}) (hy : y ∈ Submodule.span K {v}) : polar Qf x y = 0 := by
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [polar_smul_left, polar_smul_right, huv, smul_zero, smul_zero]

omit [Finite K] [FiniteDimensional K V] in
private theorem swap_core (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {S S' : V ≃ₗ[K] V}
    (hS : IsLongRootElement Qf S) (hS' : IsLongRootElement Qf S') {u v : V} (hu : u ≠ 0)
    (hv : v ≠ 0) (hSv : v ∈ movedSpace S) (hS'u : u ∈ movedSpace S')
    (huv : polar Qf u v = 0)
    (hdisj : Submodule.span K {u} ⊓ Submodule.span K {v} = ⊥) (hw : S (S' (S u)) = v) :
    S u = u + v := by
  have h2 : ∀ x : V, x + x = 0 := fun x => by
    rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
  have hvu : polar Qf v u = 0 := by rw [polar_comm]; exact huv
  have hle : Submodule.span K {v} ≤ movedSpace S :=
    (Submodule.span_singleton_le_iff_mem v _).mpr hSv
  have hS'uu : S' u = u := hS'.apply_eq_self_of_mem_movedSpace hS'u
  obtain ⟨a, hSu, ha⟩ : ∃ a, S u = u + a ∧ a ∈ Submodule.span K {v} :=
    ⟨S u - u, by abel, sub_mem_span_singleton_of_polar_eq_zero hnd hS hSv hv huv⟩
  have hSa : S a = a := hS.apply_eq_self_of_mem_movedSpace (hle ha)
  obtain ⟨b, hS'a, hb⟩ : ∃ b, S' a = a + b ∧ b ∈ Submodule.span K {u} :=
    ⟨S' a - a, by abel, sub_mem_span_singleton_of_polar_eq_zero hnd hS' hS'u hu
      (polar_eq_zero_of_mem_span hvu ha (Submodule.mem_span_singleton_self u))⟩
  obtain ⟨c, hSb, hc⟩ : ∃ c, S b = b + c ∧ c ∈ Submodule.span K {v} :=
    ⟨S b - b, by abel, sub_mem_span_singleton_of_polar_eq_zero hnd hS hSv hv
      (polar_eq_zero_of_mem_span huv hb (Submodule.mem_span_singleton_self v))⟩
  have hv_eq : v = u + b + c := by
    have e : S (S' (S u)) = u + b + c := by
      rw [hSu, map_add, hS'uu, hS'a, map_add, map_add, hSu, hSa, hSb]
      calc u + a + (a + (b + c)) = u + (a + a) + (b + c) := by abel
        _ = u + b + c := by rw [h2 a, add_zero]; abel
    exact hw.symm.trans e
  have hub : u + b = 0 := by
    have h1 : u + b ∈ Submodule.span K {u} :=
      Submodule.add_mem _ (Submodule.mem_span_singleton_self u) hb
    have h3 : u + b ∈ Submodule.span K {v} := by
      rw [eq_sub_of_add_eq hv_eq.symm]
      exact Submodule.sub_mem _ (Submodule.mem_span_singleton_self v) hc
    have h4 : u + b ∈ Submodule.span K {u} ⊓ Submodule.span K {v} := ⟨h1, h3⟩
    rwa [hdisj, Submodule.mem_bot] at h4
  have hbu : b = -u := eq_neg_of_add_eq_zero_right hub
  have hc' : c = -a := by
    have h3 : S b = -(u + a) := by rw [hbu, map_neg, hSu]
    rw [hSb, hbu] at h3
    calc c = (-u + c) + u := by abel
      _ = -(u + a) + u := by rw [h3]
      _ = -a := by abel
  have hva : v = -a := by rw [hv_eq, hbu, hc']; abel
  have hav : a = v := by
    have h5 : a = -v := by rw [hva, neg_neg]
    rw [h5]
    exact neg_eq_of_add_eq_zero_right (h2 v)
  rw [hSu, hav]

omit [CharP K 2] [Finite K] in
private theorem linearIndependent_pair_data {c d : Fin (m' + 2) → K}
    (hli : LinearIndependent K ![c, d]) :
    c ≠ 0 ∧ d ≠ 0 ∧ (∀ μ : K, d ≠ μ • c) ∧ (∀ μ : K, c ≠ μ • d) := by
  have hli' : LinearIndependent K ![d, c] := LinearIndependent.pair_symm_iff.mp hli
  have hc : c ≠ 0 := by simpa using hli.ne_zero 0
  have hd : d ≠ 0 := by simpa using hli.ne_zero 1
  exact ⟨hc, hd, fun μ h => (LinearIndependent.pair_iff' hc).mp hli μ h.symm,
    fun μ h => (LinearIndependent.pair_iff' hd).mp hli' μ h.symm⟩

omit [Finite K] [FiniteDimensional K V] in
private theorem SLSetting.axisInf_center_le_movedSpace_tvSL (hs : SLSetting Qf ρ)
    {c a : Fin (m' + 2) → K} (h : a ⬝ᵥ c = 0) (hc : c ≠ 0) (ha : a ≠ 0) :
    axisInf ((tvCenterSL c).map ρ) ≤ movedSpace (ρ (tvSL c a h)) :=
  axisInf_le ⟨_, Subgroup.mem_map_of_mem ρ ⟨a, h, rfl⟩,
    fun h1 => not_isLongRootElement_one hs.nondeg (h1 ▸ hs.siegel c a h hc ha), rfl⟩

omit [Finite K] in
theorem SLSetting.map_add_of_equivariant (hs : SLSetting Qf ρ)
    {F : (Fin (m' + 2) → K) → V} (hF0 : F 0 = 0)
    (hF : ∀ (g : SL(m' + 2, K)) x, F ((g : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K) *ᵥ x) =
      ρ g (F x))
    (hFP : ∀ x : Fin (m' + 2) → K, x ≠ 0 →
      F x ≠ 0 ∧ axisInf ((tvCenterSL x).map ρ) = Submodule.span K {F x})
    (x y : Fin (m' + 2) → K) : F (x + y) = F x + F y := by
  refine map_add_of_linearIndependent (by omega : 2 ≤ m' + 2) hF0 ?_ x y
  intro c d hli
  obtain ⟨hc, hd, hdc, hcd⟩ := linearIndependent_pair_data hli
  obtain ⟨β, hβc, hβd⟩ := exists_dot_of_not_smul hdc
  obtain ⟨α, hαd, hαc⟩ := exists_dot_of_not_smul hcd
  have hα : α ≠ 0 := fun h => by rw [h, zero_dotProduct] at hαc; exact zero_ne_one hαc
  have hβ : β ≠ 0 := fun h => by rw [h, zero_dotProduct] at hβd; exact zero_ne_one hβd
  obtain ⟨hs1, hs2⟩ := swap_mulVec hαd hαc hβc hβd
  obtain ⟨hFc0, hPc⟩ := hFP c hc
  obtain ⟨hFd0, hPd⟩ := hFP d hd
  have hFcP : F c ∈ axisInf ((tvCenterSL c).map ρ) := by
    rw [hPc]; exact Submodule.mem_span_singleton_self _
  have hFdP : F d ∈ axisInf ((tvCenterSL d).map ρ) := by
    rw [hPd]; exact Submodule.mem_span_singleton_self _
  have hdisj := hs.axisInf_inf_eq_bot_of_isStar hli
  rw [hPc, hPd] at hdisj
  have key : ρ (tvSL d α hαd) (F c) = F c + F d := by
    refine swap_core hs.nondeg (hs.siegel d α hαd hd hα) (hs.siegel c β hβc hc hβ) hFc0 hFd0
      (hs.axisInf_center_le_movedSpace_tvSL hαd hd hα hFdP)
      (hs.axisInf_center_le_movedSpace_tvSL hβc hc hβ hFcP)
      (hs.polar_eq_zero_of_isStar hli hFcP hFdP) hdisj ?_
    have h3 := hF (tvSL d α hαd * tvSL c β hβc * tvSL d α hαd) c
    rw [hs2, map_mul, map_mul] at h3
    exact h3.symm
  rw [← hs1, hF]
  exact key

theorem SLSetting.exists_ringEquiv_of_equivariant (hs : SLSetting Qf ρ)
    {F : (Fin (m' + 2) → K) → V} (hF0 : F 0 = 0)
    (hF : ∀ (g : SL(m' + 2, K)) x, F ((g : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K) *ᵥ x) =
      ρ g (F x))
    (hFP : ∀ x : Fin (m' + 2) → K, x ≠ 0 →
      F x ≠ 0 ∧ axisInf ((tvCenterSL x).map ρ) = Submodule.span K {F x}) :
    ∃ σ : K ≃+* K, ∀ (ν : K) x, F (ν • x) = σ ν • F x := by
  classical
  have hadd := hs.map_add_of_equivariant hF0 hF hFP
  have hex : ∀ x : Fin (m' + 2) → K, x ≠ 0 → ∃ g : SL(m' + 2, K),
      (g : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K) *ᵥ
        (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K) = x :=
    fun x hx => exists_mulVec_single_zero_eq hx
  have he0 := single_zero_one_ne_zero (K := K) (m' := m')
  generalize (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K) = e₀ at he0 hex
  obtain ⟨hFe0, hPe0⟩ := hFP e₀ he0
  have hmem : ∀ ν : K, ∃ θ : K, F (ν • e₀) = θ • F e₀ := by
    intro ν
    by_cases hν : ν = 0
    · exact ⟨0, by simp [hν, hF0]⟩
    · obtain ⟨-, hPν⟩ := hFP (ν • e₀) (smul_ne_zero hν he0)
      have h1 : F (ν • e₀) ∈ axisInf ((tvCenterSL (ν • e₀)).map ρ) := by
        rw [hPν]; exact Submodule.mem_span_singleton_self _
      rw [map_center_smul ρ hν, hPe0] at h1
      obtain ⟨θ, hθ⟩ := Submodule.mem_span_singleton.mp h1
      exact ⟨θ, hθ.symm⟩
  choose θ hθ using hmem
  have hinj : ∀ a b : K, a • F e₀ = b • F e₀ → a = b := fun a b h => smul_left_injective K hFe0 h
  have hsemi : ∀ (ν : K) x, F (ν • x) = θ ν • F x := by
    intro ν x
    by_cases hx : x = 0
    · subst hx
      rw [smul_zero, hF0, smul_zero]
    · obtain ⟨g, rfl⟩ := hex x hx
      rw [← Matrix.mulVec_smul, hF, hF, hθ, map_smul]
  let θ' : K →+* K :=
    { toFun := θ
      map_one' := hinj _ _ (by rw [← hθ 1, one_smul, one_smul])
      map_mul' := fun a b => hinj _ _ (by
        rw [← hθ (a * b), mul_smul a b e₀, hsemi, hθ, smul_smul])
      map_zero' := hinj _ _ (by rw [← hθ 0]; simp [hF0])
      map_add' := fun a b => hinj _ _ (by
        rw [← hθ (a + b), add_smul a b e₀, hadd, hθ, hθ, add_smul]) }
  have hbij : Function.Bijective θ' := ⟨θ'.injective, Finite.surjective_of_injective θ'.injective⟩
  exact ⟨RingEquiv.ofBijective θ' hbij, hsemi⟩

theorem SLSetting.exists_twisted_of_isStar (hs : SLSetting Qf ρ)
    (hst : IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ)) :
    ∃ (σ : K ≃+* K) (F : (Fin (m' + 2) → K) →+ V) (W : Submodule K V),
      (∀ (c : K) x, F (c • x) = σ c • F x) ∧ Function.Injective F ∧
      (∀ (g : SL(m' + 2, K)) x, F ((g : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K) *ᵥ x) =
        ρ g (F x)) ∧
      (∀ x, F x ∈ W) ∧ (∀ w ∈ W, ∃ x, F x = w) ∧ (∀ w ∈ W, Qf w = 0) ∧
      finrank K W ≤ m' + 2 ∧
      (∀ c : Fin (m' + 2) → K, c ≠ 0 →
        axisInf ((tvCenterSL c).map ρ) = Submodule.span K {F c}) := by
  classical
  obtain ⟨F₀, hF0, hF, hFP⟩ := hs.exists_equivariant_of_isStar hst
  have hadd := hs.map_add_of_equivariant hF0 hF hFP
  obtain ⟨σ, hσ⟩ := hs.exists_ringEquiv_of_equivariant hF0 hF hFP
  let F : (Fin (m' + 2) → K) →+ V := AddMonoidHom.mk' F₀ hadd
  have hFx : ∀ x, F x = F₀ x := fun x => rfl
  let W : Submodule K V :=
    { carrier := Set.range F
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, map_add F x y⟩
      zero_mem' := ⟨0, map_zero F⟩
      smul_mem' := by
        rintro ν _ ⟨x, rfl⟩
        refine ⟨σ.symm ν • x, ?_⟩
        rw [hFx, hσ, RingEquiv.apply_symm_apply, hFx] }
  refine ⟨σ, F, W, hσ, ?_, hF, fun x => ⟨x, rfl⟩, fun w hw => hw, ?_, ?_, fun c hc => (hFP c hc).2⟩
  · refine (injective_iff_map_eq_zero F).mpr fun x hx => ?_
    by_contra hx0
    exact (hFP x hx0).1 hx
  · rintro _ ⟨x, rfl⟩
    by_cases hx : x = 0
    · rw [hx, map_zero, QuadraticMap.map_zero]
    · obtain ⟨γ, hγ0, hγx, -⟩ := exists_ne_zero_dot_eq_zero_pair hs.three_le x x
      have hmem : F₀ x ∈ axisInf ((tvCenterSL x).map ρ) := by
        rw [(hFP x hx).2]; exact Submodule.mem_span_singleton_self _
      exact (hs.siegel x γ hγx hx hγ0).qf_eq_zero_of_mem_movedSpace
        (hs.axisInf_center_le_movedSpace_tvSL hγx hx hγ0 hmem)
  · have hle : W ≤ Submodule.span K (Set.range fun i : Fin (m' + 2) => F₀ (Pi.single i 1)) := by
      rintro _ ⟨x, rfl⟩
      have h1 : F x = ∑ i, σ (x i) • F₀ (Pi.single i 1) := by
        conv_lhs => rw [pi_eq_sum_univ' x]
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => hσ (x i) (Pi.single i 1)
      rw [h1]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    calc finrank K W ≤ finrank K (Submodule.span K
          (Set.range fun i : Fin (m' + 2) => F₀ (Pi.single i 1))) := Submodule.finrank_mono hle
      _ ≤ Fintype.card (Fin (m' + 2)) := finrank_range_le_card _
      _ = m' + 2 := Fintype.card_fin _

end CFSG.ClassicalGroups.Orthogonal.SiegelSL
