module

public import CFSG.LargeExtraspecial.GLRFusTrans
public import CFSG.LargeExtraspecial.GLRLinInv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

omit [Finite G] in
theorem comm_contra {e e' p : S.Qt ≃ₗ[ZMod 2] S.Qt} {a₀ w w' u₁ α : S.Qt}
    (hcomm : e (e' a₀) = e' (e a₀)) (hea : e a₀ = a₀ + w) (heu : e u₁ = u₁ + α)
    (hpa : p a₀ = a₀) (hpw : p w = w' + u₁) (hpw' : p w' = w) (hpα : p α = α)
    (he' : ∀ v, e' (p v) = p (e v)) (hew : e w' = w' ∨ e w' = w' + α) : α = 0 := by
  have h1 : e' a₀ = a₀ + (w' + u₁) := by
    rw [← hpa, he', hea, map_add, hpa, hpw]
  have h2 : e' w = p (e w') := by rw [← hpw', he']
  have hL : e (e' a₀) = (a₀ + w) + (e w' + (u₁ + α)) := by
    rw [h1, map_add, map_add, hea, heu]
  have hR : e' (e a₀) = (a₀ + (w' + u₁)) + p (e w') := by
    rw [hea, map_add, h1, h2]
  have key := hL.symm.trans (hcomm.trans hR)
  rcases hew with h | h
  · rw [h, hpw'] at key
    have h3 : ((a₀ + (w' + u₁)) + w) + α = ((a₀ + (w' + u₁)) + w) + 0 := by
      calc ((a₀ + (w' + u₁)) + w) + α = (a₀ + w) + (w' + (u₁ + α)) := by abel
        _ = (a₀ + (w' + u₁)) + w := key
        _ = _ := by abel
    exact add_left_cancel h3
  · rw [h, map_add, hpw', hpα] at key
    have h3 : ((a₀ + (w' + u₁)) + (w + α)) + α = ((a₀ + (w' + u₁)) + (w + α)) + 0 := by
      calc ((a₀ + (w' + u₁)) + (w + α)) + α = (a₀ + w) + (w' + α + (u₁ + α)) := by abel
        _ = (a₀ + (w' + u₁)) + (w + α) := key
        _ = _ := by abel
    exact add_left_cancel h3

theorem transvection_twice {A : Submodule (ZMod 2) S.Qt} {t : S.Qt ≃ₗ[ZMod 2] S.Qt} {u c : S.Qt}
    (hu : u ∈ A) (huc : polar S.q u c = 0) (ht : ∀ a ∈ A, t a = a + polar S.q a c • u)
    {a : S.Qt} (ha : a ∈ A) : t (t a) = a := by
  rw [ht a ha, ht _ (A.add_mem ha (A.smul_mem _ hu)), polar_add_left, polar_smul_left, huc,
    smul_zero, add_zero, add_assoc, two_vec, add_zero]

namespace Mixed

variable {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt} {k : G} {α β : S.Qt}

theorem transvection_fix_β (hM : Mixed S X A B k α β) {t : S.O} (ht : t ∈ X) {u c : S.Qt}
    (hu : u ∈ kerB A β)
    (hta : ∀ a ∈ A, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a + polar S.q a c • u) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) β = β := by
  refine (hM.pair.apply_eq_self_iff ht hM.mem_B).mpr fun a ha => ?_
  have huβ : polar S.q u β = 0 := hu.2
  rw [hta a ha, polar_add_left, polar_smul_left, huβ, smul_zero, add_zero]

theorem not_both (hM : Mixed S X A B k α β) {e : S.O} (he : e ∈ S.Lbar k ⊓ X)
    {a₀ : S.Qt} (ha₀ : a₀ ∈ A) (ha₀β : polar S.q a₀ β = 1)
    {k₀ : S.Qt} (hk₀ : k₀ ∈ kerB A β) (hek₀ : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) k₀ = k₀ + α)
    (hw : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) a₀ - a₀ ∉ Submodule.span (ZMod 2) ({α} : Set S.Qt)) :
    False := by
  set E := (e : S.Qt ≃ₗ[ZMod 2] S.Qt) with hE
  set Nα := Submodule.span (ZMod 2) ({α} : Set S.Qt)
  set K := kerB A β with hK
  set w := E a₀ - a₀ with hw_def
  have hP := hM.pair
  have h5 := hM.five_le
  have hKdim : S.width - 1 ≤ finrank (ZMod 2) K := hM.finrank_kerB
  obtain ⟨heα, heβ⟩ := hM.fix_of_mem he
  have hKβ : ∀ v ∈ K, polar S.q v β = 0 := fun v hv => hv.2
  have hwK : w ∈ K := by
    refine ⟨A.sub_mem (hP.apply_A e he.2 a₀ ha₀) ha₀, ?_⟩
    change polar S.q (E a₀ - a₀) β = 0
    have h1 : polar S.q (E a₀) β = polar S.q a₀ β := by
      rw [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup e.2 a₀ β, ← hE, heβ]
    rw [polar_sub_left, h1, sub_self]
  set K₀ : Submodule (ZMod 2) S.Qt :=
    K ⊓ LinearMap.ker ((E : S.Qt →ₗ[ZMod 2] S.Qt) - LinearMap.id) with hK₀
  have hmemK₀ : ∀ u, u ∈ K₀ ↔ u ∈ K ∧ E u = u := fun u => by
    simp only [hK₀, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    rfl
  have hKle : K ≤ K₀ ⊔ Submodule.span (ZMod 2) ({k₀} : Set S.Qt) := by
    intro u hu
    rcases mem_span_singleton_iff.mp (hM.apply_K he hu) with h0 | h1
    · exact Submodule.mem_sup_left ((hmemK₀ u).mpr ⟨hu, sub_eq_zero.mp h0⟩)
    · have hd : u - k₀ ∈ K₀ := (hmemK₀ _).mpr ⟨K.sub_mem hu hk₀, by
        rw [map_sub, sub_eq_iff_eq_add.mp h1, hek₀]; abel⟩
      rw [show u = (u - k₀) + k₀ by abel]
      exact Submodule.add_mem_sup hd (Submodule.mem_span_singleton_self _)
  have hK₀dim : S.width - 2 ≤ finrank (ZMod 2) K₀ := by
    have h1 := Submodule.finrank_mono hKle
    have h2 := Submodule.finrank_add_le_finrank_add_finrank K₀
      (Submodule.span (ZMod 2) ({k₀} : Set S.Qt))
    have h3 : finrank (ZMod 2) (Submodule.span (ZMod 2) ({k₀} : Set S.Qt)) ≤ 1 := by
      have := finrank_span_le_card (R := ZMod 2) ({k₀} : Set S.Qt)
      simpa using this
    omega
  obtain ⟨y, hyK₀, hy⟩ : ∃ y ∈ K₀, k₀ + y ∉ Submodule.span (ZMod 2) ({α, w} : Set S.Qt) := by
    by_contra hc
    push Not at hc
    have hk : k₀ ∈ Submodule.span (ZMod 2) ({α, w} : Set S.Qt) := by
      simpa using hc 0 K₀.zero_mem
    have hle : K₀ ≤ Submodule.span (ZMod 2) ({α, w} : Set S.Qt) := fun y hy => by
      have := Submodule.sub_mem _ (hc y hy) hk
      rwa [add_sub_cancel_left] at this
    have := Submodule.finrank_mono hle
    have := finrank_span_le_two α w
    omega
  set u₁ := k₀ + y with hu₁_def
  have hu₁K : u₁ ∈ K := K.add_mem hk₀ ((hmemK₀ y).mp hyK₀).1
  have heu₁ : E u₁ = u₁ + α := by
    rw [hu₁_def, map_add, hek₀, ((hmemK₀ y).mp hyK₀).2]; abel
  obtain ⟨u₂, hu₂K, hu₂⟩ : ∃ u₂ ∈ K, u₂ ∉ Submodule.span (ZMod 2) ({α, w, u₁} : Set S.Qt) := by
    by_contra hc
    push Not at hc
    have := Submodule.finrank_mono (show K ≤ Submodule.span (ZMod 2) {α, w, u₁} from hc)
    have := finrank_span_le_three α w u₁
    omega
  have hαK : α ∈ K := hM.α_mem_kerB
  have hsp2 : Submodule.span (ZMod 2) ({α, u₁} : Set S.Qt) ≤ K := by
    rw [Submodule.span_le]; rintro v (rfl | rfl); exacts [hαK, hu₁K]
  have hsp3 : Submodule.span (ZMod 2) ({u₂, α, u₁} : Set S.Qt) ≤ K := by
    rw [Submodule.span_le]; rintro v (rfl | rfl | rfl); exacts [hu₂K, hαK, hu₁K]
  have hsub2 : Submodule.span (ZMod 2) ({α, u₁} : Set S.Qt) ≤
      Submodule.span (ZMod 2) ({α, w, u₁} : Set S.Qt) :=
    Submodule.span_mono (by
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv ⊢
      tauto)
  have hcoord : ∀ {v z : S.Qt} {c : ZMod 2}, v ∈ K → z ∈ K → v = c • a₀ + z → c = 0 := by
    intro v z c hv hz hvz
    have := hKβ v hv
    rw [hvz, polar_add_left, polar_smul_left, ha₀β, hKβ z hz, smul_eq_mul, mul_one,
      add_zero] at this
    exact this
  have hU₁ : Submodule.span (ZMod 2) ({a₀, α, u₁} : Set S.Qt) ≤ A := by
    rw [Submodule.span_le]; rintro v (rfl | rfl | rfl); exacts [ha₀, hαK.1, hu₁K.1]
  have hu₂U₁ : u₂ ∉ Submodule.span (ZMod 2) ({a₀, α, u₁} : Set S.Qt) := by
    intro hm
    obtain ⟨c, z, hz, hcz⟩ := Submodule.mem_span_insert.mp hm
    have hc := hcoord hu₂K (hsp2 hz) hcz
    rw [hc, zero_smul, zero_add] at hcz
    exact hu₂ (hcz ▸ hsub2 hz)
  obtain ⟨c₁, -, hc₁U, hc₁⟩ := hP.exists_polar_sep hU₁ hu₂K.1 hu₂U₁
  have ha₀1 : polar S.q a₀ c₁ = 0 := hc₁U a₀ (Submodule.subset_span (by simp))
  have hα1 : polar S.q α c₁ = 0 := hc₁U α (Submodule.subset_span (by simp))
  have hu₁1 : polar S.q u₁ c₁ = 0 := hc₁U u₁ (Submodule.subset_span (by simp))
  have hU₂ : Submodule.span (ZMod 2) ({a₀, u₂, α, u₁} : Set S.Qt) ≤ A := by
    rw [Submodule.span_le]
    rintro v (rfl | rfl | rfl | rfl)
    exacts [ha₀, hu₂K.1, hαK.1, hu₁K.1]
  have hwU₂ : w ∉ Submodule.span (ZMod 2) ({a₀, u₂, α, u₁} : Set S.Qt) := by
    intro hm
    obtain ⟨c, z, hz, hcz⟩ := Submodule.mem_span_insert.mp hm
    have hc := hcoord hwK (hsp3 hz) hcz
    rw [hc, zero_smul, zero_add] at hcz
    obtain ⟨c', z', hz', hcz'⟩ := Submodule.mem_span_insert.mp hz
    rcases zmod2_eq_zero_or_one c' with rfl | rfl
    · rw [zero_smul, zero_add] at hcz'
      obtain ⟨x, y', hxy⟩ := Submodule.mem_span_pair.mp hz'
      rcases zmod2_eq_zero_or_one y' with rfl | rfl
      · apply hw
        rw [hcz, hcz', ← hxy, zero_smul, add_zero]
        exact Nα.smul_mem _ (Submodule.mem_span_singleton_self α)
      · apply hy
        have e1 : u₁ = w - x • α := by rw [hcz, hcz', ← hxy, one_smul]; abel
        rw [e1]
        exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · apply hu₂
      have e1 : u₂ = w - z' := by rw [hcz, hcz', one_smul]; abel
      rw [e1]
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp)) (hsub2 hz')
  obtain ⟨c₂, -, hc₂U, hc₂⟩ := hP.exists_polar_sep hU₂ hwK.1 hwU₂
  have ha₀2 : polar S.q a₀ c₂ = 0 := hc₂U a₀ (Submodule.subset_span (by simp))
  have hu₂2 : polar S.q u₂ c₂ = 0 := hc₂U u₂ (Submodule.subset_span (by simp))
  have hα2 : polar S.q α c₂ = 0 := hc₂U α (Submodule.subset_span (by simp))
  have hu₁2 : polar S.q u₁ c₂ = 0 := hc₂U u₁ (Submodule.subset_span (by simp))
  obtain ⟨t₁, ht₁, ht₁a⟩ := hP.exists_transvection hu₁K.1 hu₁1
  obtain ⟨t₂, ht₂, ht₂a⟩ := hP.exists_transvection hu₂K.1 hu₂2
  set T₁ := (t₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)
  set T₂ := (t₂ : S.Qt ≃ₗ[ZMod 2] S.Qt)
  set p : S.O := t₁ * t₂ with hp_def
  have hpX : p ∈ X := X.mul_mem ht₁ ht₂
  have hpv : ∀ v, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) v = T₁ (T₂ v) := fun v => rfl
  have hpα : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α := by
    rw [hpv, ht₂a α hαK.1, hα2, zero_smul, add_zero, ht₁a α hαK.1, hα1, zero_smul, add_zero]
  have hpβ : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) β = β := by
    rw [hpv, hM.transvection_fix_β ht₂ hu₂K ht₂a, hM.transvection_fix_β ht₁ hu₁K ht₁a]
  have hpa₀ : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) a₀ = a₀ := by
    rw [hpv, ht₂a a₀ ha₀, ha₀2, zero_smul, add_zero, ht₁a a₀ ha₀, ha₀1, zero_smul, add_zero]
  set w' := T₂ (T₁ w) with hw'_def
  have hT₁w : T₁ w = w + polar S.q w c₁ • u₁ := ht₁a w hwK.1
  have hw'eq : w' = w + polar S.q w c₁ • u₁ + u₂ := by
    rw [hw'_def, hT₁w, ht₂a _ (A.add_mem hwK.1 (A.smul_mem _ hu₁K.1)), polar_add_left,
      polar_smul_left, hc₂, hu₁2, smul_zero, add_zero, one_smul]
  have hw'K : w' ∈ K := by
    rw [hw'eq]
    exact K.add_mem (K.add_mem hwK (K.smul_mem _ hu₁K)) hu₂K
  have hpw' : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) w' = w := by
    rw [hpv, hw'_def, transvection_twice hu₂K.1 hu₂2 ht₂a (ht₁a w hwK.1 ▸
      A.add_mem hwK.1 (A.smul_mem _ hu₁K.1)), transvection_twice hu₁K.1 hu₁1 ht₁a hwK.1]
  have hpw : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w' + u₁ := by
    rw [hpv, ht₂a w hwK.1, hc₂, one_smul, ht₁a _ (A.add_mem hwK.1 hu₂K.1), polar_add_left, hc₁,
      hw'eq, add_smul, one_smul]
    abel
  have he' := hM.conj_mem_E hpX hpα hpβ he
  have hcomm := Lbar_comm hM.conj_mem he.1 he'.1
  have hcomm' : E (((p * e * p⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a₀) =
      ((p * e * p⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (E a₀) := by
    have := congrArg (fun f : S.O => (f : S.Qt ≃ₗ[ZMod 2] S.Qt) a₀) hcomm
    simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply] using this
  have hew : E w' = w' ∨ E w' = w' + α := by
    rcases mem_span_singleton_iff.mp (hM.apply_K he hw'K) with h0 | h1
    · exact Or.inl (sub_eq_zero.mp h0)
    · exact Or.inr (sub_eq_iff_eq_add.mp h1 |>.trans (add_comm _ _))
  exact hM.ne_zero_A (comm_contra hcomm' (by rw [hw_def]; abel) heu₁ hpa₀ hpw hpw' hpα
    (fun v => apply_conj p e v) hew)

end Mixed

end CFSG.LargeExtraspecial.GLR
