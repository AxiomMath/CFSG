module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterAbstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Layer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section Abs

variable {Γ : Type*} [Group Γ] [Finite Γ]

structure SwapX (Γ : Type*) [Group Γ] [Finite Γ] (J : Subgroup Γ) (τ : Γ) : Prop where
  sq : τ * τ = 1
  cent : ∀ j ∈ J, j * τ = τ * j
  alt8 : Nonempty (↥J ≃* alternatingGroup (Fin 8))
  le_layer : J ≤ layer Γ
  comm_mem : ∀ w w' : Γ, w * τ = τ * w → w' * τ = τ * w' → ⁅w, w'⁆ ∈ J
  sq_mem : ∀ w : Γ, w * τ = τ * w → w * w ∈ J
  not_normal : ¬ J.Normal
  oddCore : CFSG.oddCore Γ = ⊥
  card_le : Nat.card (centralizer ({τ} : Set Γ)) ≤ 161280

variable {J : Subgroup Γ} {τ : Γ}

theorem SwapX.perfect (hX : SwapX Γ J τ) : ⁅J, J⁆ = J :=
  commutator_eq_self_of_equiv_alt8 hX.alt8.some

theorem SwapX.simple (hX : SwapX Γ J τ) : IsSimpleGroup ↥J := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by norm_num)
  exact hX.alt8.some.isSimpleGroup

theorem SwapX.not_comm (hX : SwapX Γ J τ) : ¬ ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := by
  intro hab
  have hbot : ⁅J, J⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hab a ha b hb
  have hJbot : J = ⊥ := hX.perfect.symm.trans hbot
  haveI := hX.simple.toNontrivial
  obtain ⟨j, hj1⟩ := exists_ne (1 : ↥J)
  exact hj1 (Subtype.ext ((Subgroup.eq_bot_iff_forall J).1 hJbot j j.2))

theorem SwapX.perfect_le (hX : SwapX Γ J τ) {Q : Subgroup Γ} (hQt : ∀ q ∈ Q, q * τ = τ * q)
    (hQ : ⁅Q, Q⁆ = Q) : Q ≤ J := by
  conv_lhs => rw [← hQ]
  rw [Subgroup.commutator_le]
  intro q hq q' hq'
  exact hX.comm_mem q q' (hQt q hq) (hQt q' hq')

theorem J_le_orbit_of_nc {t : Γ} (ht : t * t = 1) {J : Subgroup Γ} (hJs : IsSimpleGroup J)
    (hJp : ⁅J, J⁆ = J) (hJE : J ≤ layer Γ) (hJt : ∀ j ∈ J, j * t = t * j)
    (hHJ : ∀ Q : Subgroup Γ, Q ≤ layer Γ → (∀ q ∈ Q, q * t = t * q) → ⁅Q, Q⁆ = Q → Q ≤ J)
    {K : Subgroup Γ} (hK : IsComponent K) (hZ : ¬ ∀ k ∈ K, ∀ j ∈ J, k * j = j * k) :
    J ≤ K ⊔ PartA.cj t K := by
  have hcK := PartA.isComponent_cj t hK
  set N : Subgroup Γ := K ⊔ PartA.cj t K with hN
  set M : Subgroup Γ :=
    sSup {K' | IsComponent K' ∧ K' ≠ K ∧ K' ≠ PartA.cj t K} with hM
  have hNle : N ≤ layer Γ := sup_le (component_le_layer hK) (component_le_layer hcK)
  have hNMc : N ≤ Subgroup.centralizer (M : Set Γ) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact sSup_le fun K' hK' => PartA.le_centralizer_of_ne hK'.1 hK hK'.2.1
    · rw [Subgroup.le_centralizer_iff]
      exact sSup_le fun K' hK' => PartA.le_centralizer_of_ne hK'.1 hcK hK'.2.2
  have hNM : ∀ n ∈ N, ∀ m ∈ M, n * m = m * n := fun n hn m hm =>
    (Subgroup.mem_centralizer_iff.1 (hNMc hn) m hm).symm
  have hNt : ∀ n ∈ N, t * n * t⁻¹ ∈ N := by
    have : N ≤ N.comap (MulAut.conj t).toMonoidHom := by
      refine sup_le (fun k hk => ?_) (fun x hx => ?_)
      · show (MulAut.conj t).toMonoidHom k ∈ N
        exact Subgroup.mem_sup_right ⟨k, hk, rfl⟩
      · show (MulAut.conj t).toMonoidHom x ∈ N
        have := (PartA.mem_cj ht).1 hx
        simpa [MulAut.conj_apply] using Subgroup.mem_sup_left this
    intro n hn
    simpa [MulAut.conj_apply] using this hn
  have hMt : ∀ m ∈ M, t * m * t⁻¹ ∈ M := by
    have : M ≤ M.comap (MulAut.conj t).toMonoidHom := by
      refine sSup_le fun K' hK' k hk => ?_
      obtain ⟨hc, h1, h2⟩ := hK'
      show (MulAut.conj t).toMonoidHom k ∈ M
      have hcc : PartA.cj t K' ≤ M := by
        refine le_sSup ⟨PartA.isComponent_cj t hc, ?_, ?_⟩
        · intro h; exact h2 (by rw [← h, PartA.cj_cj ht])
        · intro h; exact h1 (by
            have := congrArg (PartA.cj t) h
            rwa [PartA.cj_cj ht, PartA.cj_cj ht] at this)
      exact hcc ⟨k, hk, rfl⟩
    intro m hm
    simpa [MulAut.conj_apply] using this hm
  have hJNM : J ≤ N ⊔ M := by
    refine hJE.trans (sSup_le fun K' hK' => ?_)
    by_cases h1 : K' = K
    · rw [h1]; exact le_sup_left.trans le_sup_left
    by_cases h2 : K' = PartA.cj t K
    · rw [h2]; exact le_sup_right.trans le_sup_left
    · exact (le_sSup ⟨hK', h1, h2⟩ : K' ≤ M).trans le_sup_right
  exact PartA.perfect_le_of_central_product t N M J hNM hNt hMt hJNM hJt hJs hJp
    (fun Q hQ => hHJ Q (hQ.trans hNle))
    (fun h => hZ fun k hk j hj => h k ((le_sup_left : K ≤ K ⊔ PartA.cj t K) hk) j hj)

structure SwapOrbit (J : Subgroup Γ) (τ : Γ) (K : Subgroup Γ) : Prop where
  comp : IsComponent K
  le : J ≤ K ⊔ PartA.cj τ K
  nc : ¬ ∀ k ∈ K, ∀ j ∈ J, k * j = j * k
  others : ∀ K' : Subgroup Γ, IsComponent K' → K' ≠ K → K' ≠ PartA.cj τ K →
    ∀ k ∈ K', ∀ j ∈ J, k * j = j * k

theorem SwapX.exists_orbit (hX : SwapX Γ J τ) : ∃ K : Subgroup Γ, SwapOrbit J τ K := by
  have hJs := hX.simple
  have hJp := hX.perfect
  have hHJ : ∀ Q : Subgroup Γ, Q ≤ layer Γ → (∀ q ∈ Q, q * τ = τ * q) → ⁅Q, Q⁆ = Q → Q ≤ J :=
    fun Q _ hQt hQ => hX.perfect_le hQt hQ
  have hex : ∃ K : Subgroup Γ, IsComponent K ∧ ¬ ∀ k ∈ K, ∀ j ∈ J, k * j = j * k := by
    by_contra hcon
    push Not at hcon
    apply hX.not_comm
    have hl : layer Γ ≤ centralizer (J : Set Γ) := by
      refine sSup_le fun K hK => ?_
      intro k hk
      rw [mem_centralizer_iff]
      intro j hj
      exact (hcon K hK k hk j hj).symm
    intro a ha b hb
    exact (mem_centralizer_iff.1 (hl (hX.le_layer ha)) b hb).symm
  obtain ⟨K, hK, hnc⟩ := hex
  have hle := J_le_orbit_of_nc hX.sq hJs hJp hX.le_layer hX.cent hHJ hK hnc
  refine ⟨K, hK, hle, hnc, fun K' hK' h1 h2 k hk j hj => ?_⟩
  by_contra hne
  have hnc' : ¬ ∀ k ∈ K', ∀ j ∈ J, k * j = j * k := fun h => hne (h k hk j hj)
  have hle' := J_le_orbit_of_nc hX.sq hJs hJp hX.le_layer hX.cent hHJ hK' hnc'
  apply hX.not_comm
  intro a ha b hb
  have := PartA.orbit_commute hX.sq hK hK' h1 h2 (hle ha)
  exact (mem_centralizer_iff.1 this b (hle' hb)).symm

omit [Finite Γ] in
theorem mem_cj_mk {g x : Γ} {K : Subgroup Γ} (hx : x ∈ K) : g * x * g⁻¹ ∈ PartA.cj g K :=
  ⟨x, hx, by simp [MulAut.conj_apply]⟩

omit [Finite Γ] in
theorem cj_mul_eq (g h : Γ) (K : Subgroup Γ) :
    PartA.cj (g * h) K = PartA.cj g (PartA.cj h K) := by
  unfold PartA.cj
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

variable {K : Subgroup Γ}

theorem SwapOrbit.cj_mem_all (hK : SwapOrbit J τ K)
    (hnoE8 : ∀ E : Subgroup Γ, E ≤ centralizer (J : Set Γ) → (∀ e ∈ E, e * e = 1) →
      Nat.card E ≤ 4)
    (hE : ∃ E : Subgroup Γ, E ≤ K ∧ (∀ e ∈ E, e * e = 1) ∧ 4 < Nat.card E) (g : Γ) :
    PartA.cj g K = K ∨ PartA.cj g K = PartA.cj τ K := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hc := hK.others _ (PartA.isComponent_cj g hK.comp) h1 h2
  obtain ⟨E, hEK, hE2, hE4⟩ := hE
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ centralizer (J : Set Γ) := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := hy
    have hyK : (MulAut.conj g).toMonoidHom e ∈ PartA.cj g K := ⟨e, hEK he, rfl⟩
    rw [mem_centralizer_iff]
    intro j hj
    exact (hc _ hyK j hj).symm
  have hsq : ∀ y ∈ E.map (MulAut.conj g).toMonoidHom, y * y = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, hE2 e he, map_one]
  have h4 := hnoE8 _ hle hsq
  have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  omega

omit [Finite Γ] in
theorem normal_of_cj_le {M : Subgroup Γ} (h : ∀ g : Γ, PartA.cj g M ≤ M) : M.Normal :=
  ⟨fun _ hn g => h g (mem_cj_mk hn)⟩

omit [Finite Γ] in
theorem normal_single_of_cj {τ : Γ} (hcj : PartA.cj τ K = K)
    (hall : ∀ g : Γ, PartA.cj g K = K ∨ PartA.cj g K = PartA.cj τ K) : K.Normal :=
  normal_of_cj_le fun g => by
    rcases hall g with h | h
    · exact h.le
    · rw [h, hcj]

omit [Finite Γ] in
theorem normal_pair_of_cj {τ : Γ}
    (hall : ∀ g : Γ, PartA.cj g K = K ∨ PartA.cj g K = PartA.cj τ K) :
    (K ⊔ PartA.cj τ K).Normal :=
  normal_of_cj_le fun g => by
    have h1 : PartA.cj g (K ⊔ PartA.cj τ K) = PartA.cj g K ⊔ PartA.cj g (PartA.cj τ K) :=
      Subgroup.map_sup _ _ _
    rw [h1]
    refine sup_le ?_ ?_
    · rcases hall g with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    · rw [← cj_mul_eq]
      rcases hall (g * τ) with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right

theorem isPGroup_center_component (hO : CFSG.oddCore Γ = ⊥) {K : Subgroup Γ}
    (hK : IsComponent K) : IsPGroup 2 (center ↥K) := by
  have hLN : (CFSG.layer Γ : Subgroup Γ).Normal :=
    have := CFSG.LocalCores.layer_characteristic (G := Γ)
    inferInstance
  set N : Subgroup Γ := (CFSG.layer Γ : Subgroup Γ) ⊓ centralizer ((CFSG.layer Γ : Subgroup Γ) : Set Γ)
    with hN
  have hNn : N.Normal := by
    have := hLN
    infer_instance
  have : IsMulCommutative ↥N := ⟨⟨fun a b => Subtype.ext (by
    have := mem_centralizer_iff.1 b.2.2 (a : Γ) a.2.1
    show (a : Γ) * b = b * a
    exact this)⟩⟩
  have hnil : Group.IsNilpotent ↥N := inferInstance
  have hle : N ≤ CFSG.fittingSubgroup Γ := le_sSup ⟨hNn, hnil⟩
  have h2 : CFSG.pPrimeCore 2 Γ = ⊥ := by
    have : CFSG.oddCore Γ = CFSG.pPrimeCore 2 Γ := by
      unfold CFSG.oddCore CFSG.pPrimeCore
      congr 1
      ext K
      simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]
    rw [← this]; exact hO
  have hF : CFSG.fittingSubgroup Γ = CFSG.pCore 2 Γ := CFSG.Fitting_eq_pcore Γ 2 h2
  have hp : IsPGroup 2 (CFSG.pCore 2 Γ) := CFSG.pCore_isPGroup
  intro z
  have hz : ((z : ↥K) : Γ) ∈ N := by
    have h1 := CFSG.LocalCores.center_component_le_center_layer hK ⟨z, z.2, rfl⟩
    obtain ⟨hz1, hz2⟩ := (CFSG.LocalCores.mem_map_center_iff _).1 h1
    exact ⟨hz1, hz2⟩
  have hzp : ((z : ↥K) : Γ) ∈ CFSG.pCore 2 Γ := hF ▸ hle hz
  obtain ⟨k, hk⟩ := hp ⟨((z : ↥K) : Γ), hzp⟩
  refine ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  apply Subtype.ext
  apply Subtype.ext
  simpa using this

end Abs

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
