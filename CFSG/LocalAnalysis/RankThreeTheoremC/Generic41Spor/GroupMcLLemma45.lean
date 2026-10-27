module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupMcLLem45Model
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupWitnessSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupBridge
public import CFSG.RankThree.Native.HSMcLFiveCentralizers
public import CFSG.Sporadic.Presentation.McLExact

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open Subgroup CFSG.RankThree.Native

private theorem conj_mem_closure_of_gen_mcl {G : Type*} [Group G] {S : Set G} (g : G)
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ Subgroup.closure S) :
    ∀ x ∈ Subgroup.closure S, g * x * g⁻¹ ∈ Subgroup.closure S := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ ihx ihy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact mul_mem ihx ihy
  | inv x _ ihx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem ihx

private theorem sq_eq_one_of_closure_comm_mcl {G : Type*} [Group G] {S : Set G}
    (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hs : ∀ x ∈ S, x ^ 2 = 1) :
    ∀ g ∈ Subgroup.closure S, g ^ 2 = 1 := by
  have h1 : ∀ g ∈ Subgroup.closure S, ∀ s ∈ S, s * g = g * s := by
    intro g hg s hs'
    have : Subgroup.closure S ≤ Subgroup.centralizer {s} := by
      rw [Subgroup.closure_le]
      intro x hx y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hc y hs' x hx
    exact this hg s rfl
  have h2 : ∀ g ∈ Subgroup.closure S, ∀ h ∈ Subgroup.closure S, h * g = g * h := by
    intro g hg h hh
    have : Subgroup.closure S ≤ Subgroup.centralizer {g} := by
      rw [Subgroup.closure_le]
      intro x hx y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (h1 y hg x hx).symm
    exact (this hh g rfl).symm
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := h2 y hy x hx
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem mcl_twoWitness_of_commuting_conjugates {G : Type} [Group G] {u w : G} (hu : u ^ 5 = 1)
    (hw : w * w = 1) (hne : u * w * u⁻¹ ≠ w)
    (hcomm : ∀ i j : ℕ, (u ^ i * w * (u ^ i)⁻¹) * (u ^ j * w * (u ^ j)⁻¹) =
      (u ^ j * w * (u ^ j)⁻¹) * (u ^ i * w * (u ^ i)⁻¹)) :
    TwoWitness u := by
  set S : Set G := Set.range (fun k : ℕ => u ^ k * w * (u ^ k)⁻¹) with hS
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hcomm i j
  have hSs : ∀ x ∈ S, x ^ 2 = 1 := by
    rintro _ ⟨i, rfl⟩
    rw [sq]
    calc u ^ i * w * (u ^ i)⁻¹ * (u ^ i * w * (u ^ i)⁻¹) = u ^ i * (w * w) * (u ^ i)⁻¹ := by group
      _ = 1 := by rw [hw]; group
  have hfwd : ∀ x ∈ S, u * x * u⁻¹ ∈ Subgroup.closure S := by
    rintro _ ⟨k, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨k + 1, ?_⟩
    simp only [pow_succ']
    group
  have h4 : u ^ 4 = u⁻¹ := by
    have : u ^ 4 * u = 1 := by rw [← pow_succ]; exact hu
    exact mul_eq_one_iff_eq_inv.mp this
  have hbwd : ∀ x ∈ S, u⁻¹ * x * u⁻¹⁻¹ ∈ Subgroup.closure S := by
    rintro _ ⟨k, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨k + 4, ?_⟩
    simp only [pow_add, h4]
    group
  set V := Subgroup.closure S with hV
  have hV2 : IsPGroup 2 V := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using sq_eq_one_of_closure_comm_mcl hSc hSs x.1 x.2
  have hwV : w ∈ V := Subgroup.subset_closure ⟨0, by simp⟩
  refine ⟨V, hV2, ?_, w, hwV, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact conj_mem_closure_of_gen_mcl u hfwd h
    · intro hh
      have := conj_mem_closure_of_gen_mcl u⁻¹ hbwd _ hh
      simpa [mul_assoc] using this
  · intro hcon
    apply hne
    calc u * w * u⁻¹ = w * u * u⁻¹ := by rw [hcon]
      _ = w := by group

theorem mcl_twoWitness_of_equiv_noncentral {K K' : Type} [Group K] [Group K'] [Finite K]
    [Finite K'] {p : ℕ} (hp : p.Prime) (e : K ≃* K') (T₀ : Sylow p K') {u₀ : K'}
    (hnc : ∃ s ∈ (T₀ : Subgroup K'), s * u₀ ≠ u₀ * s) (h₀ : TwoWitness u₀)
    (horb : ∀ x ∈ (T₀ : Subgroup K'), (∃ s ∈ (T₀ : Subgroup K'), s * x ≠ x * s) →
      ∃ n ∈ normalizer ((T₀ : Subgroup K') : Set K'), n * u₀ * n⁻¹ = x) :
    ∀ S : Sylow p K, ∀ u ∈ (S : Subgroup K), (∃ s ∈ (S : Subgroup K), s * u ≠ u * s) →
      TwoWitness u := by
  haveI : Fact p.Prime := ⟨hp⟩
  let S₀ : Sylow p K := Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective T₀
  have hS₀ : (S₀ : Subgroup K) = (T₀ : Subgroup K').map e.symm.toMonoidHom := rfl
  intro S u huS hnc'
  have hu1 : u ≠ 1 := by
    rintro rfl
    obtain ⟨s, -, hs⟩ := hnc'
    exact hs (by simp)
  have hPr : ∀ (S : Subgroup K) (x g : K), (∃ s ∈ S, s * x ≠ x * s) →
      (∃ s ∈ S.map (MulAut.conj g).toMonoidHom, s * (g * x * g⁻¹) ≠ (g * x * g⁻¹) * s) := by
    rintro S x g ⟨s, hs, hne⟩
    refine ⟨g * s * g⁻¹, ⟨s, hs, rfl⟩, ?_⟩
    intro h
    apply hne
    have h1 : g * (s * x) * g⁻¹ = g * (x * s) * g⁻¹ := by
      calc g * (s * x) * g⁻¹ = (g * s * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * s * g⁻¹) := h
        _ = g * (x * s) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  refine TwoWitness.of_sylow_pred hp (fun S x => ∃ s ∈ S, s * x ≠ x * s) hPr (S₀ := S₀)
    (u₀ := e.symm u₀) ?_ (h₀.of_mulEquiv e.symm) ?_ S huS hu1 hnc'
  · obtain ⟨s, hs, hne⟩ := hnc
    refine ⟨e.symm s, ?_, ?_⟩
    · rw [hS₀]
      exact ⟨s, hs, rfl⟩
    · intro h
      apply hne
      apply e.symm.injective
      simpa using h
  · intro x hx _ hPrx
    rw [hS₀] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨s, hs, hne⟩ := hPrx
    rw [hS₀] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have hne' : s' * y ≠ y * s' := by
      intro h
      apply hne
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, h]
    obtain ⟨n, hn, hny⟩ := horb y hy ⟨s', hs', hne'⟩
    refine ⟨e.symm n, ?_, ?_⟩
    · rw [hS₀, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨n, hn, rfl⟩
    · rw [← map_inv, ← map_mul, ← map_mul, hny]
      rfl

section


theorem mcl_witness_of_model (h : McLLem45Model) :
    ∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K →
      ∀ S : Sylow 5 K, ∀ u ∈ (S : Subgroup K), (∃ s ∈ (S : Subgroup K), s * u ≠ u * s) →
        TwoWitness u := by
  intro K _ _ hK
  obtain ⟨R₀, u₀, w₀, hR₀, -, hu₀5, hnc, hw₀, hne, hcomm, horb⟩ := h
  obtain ⟨-, ⟨e⟩⟩ := hK
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  let θ : K ≃* mcl275P := (e.trans eC.symm).trans mcl275Equiv
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : Nat.card R₀ = 5 ^ (Nat.card mcl275P).factorization 5 := by
    rw [hR₀, factorization_card_mcl275P_five]
  have hS : ((Sylow.ofCard R₀ hcard : Sylow 5 ↥mcl275P) : Subgroup ↥mcl275P) = R₀ :=
    Sylow.coe_ofCard R₀ hcard
  refine mcl_twoWitness_of_equiv_noncentral Nat.prime_five θ (Sylow.ofCard R₀ hcard)
    (u₀ := u₀) ?_ (mcl_twoWitness_of_commuting_conjugates hu₀5 hw₀ hne hcomm) ?_
  · rw [hS]
    exact hnc
  · intro x hx hPrx
    rw [hS] at hx hPrx ⊢
    exact horb x hx hPrx

theorem mcl_lemma45_of_model (h : McLLem45Model) : Lemma45Facts IsMcLType 5 McLShape := by
  refine lemma45Facts_of_inner Nat.prime_five (by norm_num) ?_
  intro X _ _ K hK R U₀ hUR hUe hUc hshape
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : K.Normal := hK.1
  obtain ⟨u, hu, s, hs, hsu⟩ := hshape
  have hu1' : u ≠ 1 := by
    rintro rfl
    exact hsu (by simp)
  have hU₀ : U₀ = Subgroup.zpowers u := eq_zpowers_of_card_prime Nat.prime_five hUc hu.1 hu1'
  have huK : u ∈ K := hu.2
  have hsK : s ∈ K := hs.2
  obtain ⟨P, hP⟩ := exists_sylow_inf_normal K R
  have hmemP : ∀ x : X, x ∈ (R : Subgroup X) ⊓ K → ∀ hxK : x ∈ K,
      (⟨x, hxK⟩ : K) ∈ (P : Subgroup K) := by
    intro x hx hxK
    rw [← hP] at hx
    obtain ⟨y, hyP, hyx⟩ := hx
    have hy : y = ⟨x, hxK⟩ := Subtype.ext hyx
    rw [← hy]
    exact hyP
  have huP : (⟨u, huK⟩ : K) ∈ (P : Subgroup K) := hmemP u ⟨hUR hu.1, huK⟩ huK
  have hsP : (⟨s, hsK⟩ : K) ∈ (P : Subgroup K) := hmemP s hs hsK
  have hW := mcl_witness_of_model h K hK.2.2 P ⟨u, huK⟩ huP
    ⟨⟨s, hsK⟩, hsP, fun hc => hsu (congrArg Subtype.val hc)⟩
  exact ⟨hU₀ ▸ (Subgroup.zpowers_le.2 huK), kwitness_to_x K huK hW hU₀⟩

end

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
