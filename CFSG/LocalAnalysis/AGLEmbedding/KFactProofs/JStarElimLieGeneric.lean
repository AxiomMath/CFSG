module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem conj_injective_of_center_eq_bot {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, ← hZ]
  refine le_antisymm (fun x hx => Subgroup.mem_center_iff.mpr fun g => ?_) ?_
  · have hxg : x * g * x⁻¹ = g := by
      simpa using congrArg (fun f : MulAut G => f g) (MonoidHom.mem_ker.mp hx)
    calc g * x = x * g * x⁻¹ * x := by rw [hxg]
      _ = x * g := by group
  · intro x hx
    rw [MonoidHom.mem_ker]
    ext g
    simp [(Subgroup.mem_center_iff.mp hx g).symm]

theorem JStarElimDataOf.card_dvd_card_of_perfect {L₀ T : Type} [Group L₀] [Finite L₀] [Group T]
    {p B : ℕ} (hperf : commutator T = ⊤) (hOut : Group.IsSolvable (Outer L₀))
    (h : JStarElimDataOf L₀ p B T) : Nat.card T ∣ Nat.card L₀ := by
  obtain ⟨A, J, -, -, -, φ, hφ, -⟩ := h
  let ψ : J →* Outer L₀ := (QuotientGroup.mk' (inner L₀)).comp J.subtype
  obtain ⟨n, hn⟩ := hOut.solvable
  have h1 : derivedSeries J n ≤ ψ.ker := by
    have := map_derivedSeries_le_derivedSeries ψ n
    rw [hn] at this
    exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp this)
  have hTn : ∀ m, derivedSeries T m = ⊤ := by
    intro m
    induction m with
    | zero => exact derivedSeries_zero T
    | succ m ih => rw [derivedSeries_succ, ih]; exact hperf
  have h2 : (ψ.ker.map φ) = ⊤ := by
    rw [eq_top_iff, ← hTn n, ← map_derivedSeries_eq hφ n]
    exact Subgroup.map_mono h1
  have h1' : Nat.card T ∣ Nat.card ψ.ker := by
    have := Subgroup.card_map_dvd (f := φ) ψ.ker
    rwa [h2, Subgroup.card_top] at this
  let I : Subgroup (MulAut L₀) := inner L₀
  let χ : ψ.ker →* I :=
    (J.subtype.comp ψ.ker.subtype).codRestrict I fun x =>
      (QuotientGroup.eq_one_iff (N := I) _).mp (MonoidHom.mem_ker.mp x.2)
  have hχ : Function.Injective χ := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : I => (z : MulAut L₀)) hxy
  exact h1'.trans ((Subgroup.card_dvd_of_injective χ hχ).trans (Subgroup.card_range_dvd _))

theorem JStarElimDataOf.orderTest_of_schreier_perfect {L₀ T : Type} [Group L₀] [Finite L₀]
    [Group T] {p B : ℕ} [Fact p.Prime] [IsSimpleGroup L₀] (hperf : commutator T = ⊤)
    (hnc : ∃ a b : T, a * b ≠ b * a)
    (hOut : (∃ a b : L₀, a * b ≠ b * a) → Group.IsSolvable (Outer L₀))
    (h : JStarElimDataOf L₀ p B T) :
    Nat.card T ∣ Nat.card L₀ ∧ ∀ k : ℕ, p ^ k ∣ Nat.card L₀ → p ^ k ∣ B := by
  by_cases hab : ∃ a b : L₀, a * b ≠ b * a
  · exact ⟨h.card_dvd_card_of_perfect hperf (hOut hab), fun _ hk =>
      h.pow_dvd_of_center_eq_bot (center_bot_of_simple_nonab hab) hk⟩
  · exfalso
    push Not at hab
    have hdvd := h.card_dvd_card_of_perfect hperf (outer_solvable_of_simple_comm hab)
    have : IsMulCommutative L₀ := ⟨⟨hab⟩⟩
    have hpr : (Nat.card L₀).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    obtain ⟨a, b, hab'⟩ := hnc
    rcases (Nat.dvd_prime hpr).mp hdvd with h1 | h1
    · have : Subsingleton T := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hab' (Subsingleton.elim _ _)
    · have : Fact (Nat.card T).Prime := ⟨h1 ▸ hpr⟩
      have : IsCyclic T := isCyclic_of_prime_card rfl
      exact hab' (IsCyclic.isMulCommutative.is_comm.comm a b)

theorem card_mul_pow_dvd_of_isPGroup {G : Type*} [Group G] [Finite G] {p B s : ℕ} [Fact p.Prime]
    {N S : Subgroup G} [N.Normal] (hS : IsPGroup p S) (hs : p ^ s ∣ Nat.card N)
    (hB : ∀ S' : Subgroup G, S' ≤ S ⊔ N → IsPGroup p S' → Nat.card S' ∣ B) :
    Nat.card S * p ^ s ∣ B * Nat.card ↥(N.subgroupOf S) := by
  have hp : p.Prime := Fact.out
  have hS1 : Nat.card ↥(N.subgroupOf S) * N.relIndex S = Nat.card S := Subgroup.card_mul_index _
  have hH : Nat.card N * N.relIndex S = Nat.card ↥(S ⊔ N) := by
    have h1 := Subgroup.card_mul_index (N.subgroupOf (S ⊔ N))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ S ⊔ N)).toEquiv] at h1
    rw [← h1, ← Subgroup.relIndex, Subgroup.relIndex_sup_right]
  obtain ⟨m, hm⟩ := hS.exists_card_eq
  have htdvd : N.relIndex S ∣ p ^ m := ⟨Nat.card ↥(N.subgroupOf S), by rw [← hm, ← hS1]; ring⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp htdvd
  have hdvd : p ^ (s + j) ∣ Nat.card ↥(S ⊔ N) := by
    rw [pow_add, ← hH, hj]
    exact mul_dvd_mul_right hs _
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  have hKS : Nat.card (K.map (S ⊔ N).subtype) = p ^ (s + j) := by
    rw [Subgroup.card_map_of_injective (S ⊔ N).subtype_injective, hK]
  have hBd := hB (K.map (S ⊔ N).subtype) (Subgroup.map_subtype_le K) (IsPGroup.of_card hKS)
  rw [hKS] at hBd
  have hrw : Nat.card S * p ^ s = Nat.card ↥(N.subgroupOf S) * p ^ (s + j) := by
    rw [← hS1, hj, pow_add]
    ring
  rw [hrw, mul_comm B]
  exact mul_dvd_mul_left _ hBd


theorem JStarElimDataOf.exists_sylow_embedding {L₀ T : Type} [Group L₀] [Finite L₀] [Group T]
    {p B : ℕ} [Fact p.Prime] (h : JStarElimDataOf L₀ p B T) :
    ∃ (A E : Subgroup (MulAut L₀)) (U : Sylow p T),
      (MulAut.conj : L₀ →* MulAut L₀).range ≤ A ∧ E ≤ A ∧
      (∀ S : Subgroup (MulAut L₀), S ≤ A → IsPGroup p S → Nat.card S ∣ B) ∧
      Nonempty (E ≃* U) := by
  obtain ⟨A, J, hInn, hJA, hpA, φ, hφ, hcop⟩ := h
  have : Finite T := Finite.of_surjective φ hφ
  have hkT : p ^ (Nat.card T).factorization p ∣ Nat.card J :=
    (Nat.ordProj_dvd _ _).trans (Subgroup.card_dvd_of_surjective hφ)
  obtain ⟨Ê, hÊ⟩ := Sylow.exists_subgroup_card_pow_prime p hkT
  have hinj : Function.Injective (φ.comp Ê.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : (x : J) ∈ φ.ker := hx
    have h1 : orderOf x ∣ p ^ (Nat.card T).factorization p := hÊ ▸ orderOf_dvd_natCard x
    have h2 : orderOf (⟨(x : J), hx1⟩ : φ.ker) ∣ Nat.card φ.ker := orderOf_dvd_natCard _
    have h3 : orderOf (⟨(x : J), hx1⟩ : φ.ker) = orderOf x :=
      (Subgroup.orderOf_coe (⟨(x : J), hx1⟩ : φ.ker)).symm.trans (Subgroup.orderOf_coe x)
    rw [h3] at h2
    have h4 : (p ^ (Nat.card T).factorization p).Coprime (Nat.card φ.ker) := hcop.pow_left _
    have h5 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd (h4.coprime_dvd_left h1) h2
    rw [orderOf_eq_one_iff] at h5
    exact h5
  set Q : Subgroup T := (φ.comp Ê.subtype).range with hQ
  have eQ : Ê ≃* Q := MonoidHom.ofInjective hinj
  have hQcard : Nat.card Q = p ^ (Nat.card T).factorization p := by
    rw [← Nat.card_congr eQ.toEquiv, hÊ]
  obtain ⟨U, hQU⟩ := (IsPGroup.of_card hQcard).exists_le_sylow
  have hUcard : Nat.card U = p ^ (Nat.card T).factorization p := U.card_eq_multiplicity
  have hQU' : Q = U := Subgroup.eq_of_le_of_card_ge hQU (by rw [hQcard, hUcard])
  let eU : Ê ≃* (U : Subgroup T) := eQ.trans (MulEquiv.subgroupCongr hQU')
  let eE : Ê.map J.subtype ≃* Ê :=
    (Subgroup.equivMapOfInjective Ê J.subtype J.subtype_injective).symm
  refine ⟨A, Ê.map J.subtype, U, hInn, ?_, hpA, ⟨eE.trans eU⟩⟩
  rintro _ ⟨x, -, rfl⟩
  exact hJA x.2


theorem JStarElimDataOf.exists_inner_copy {L₀ T : Type} [Group L₀] [Finite L₀] [Group T]
    {p B s : ℕ} [Fact p.Prime] (hZ : Subgroup.center L₀ = ⊥) (hs : p ^ s ∣ Nat.card L₀)
    (h : JStarElimDataOf L₀ p B T) :
    ∃ (U : Sylow p T) (D : Subgroup T) (D₀ : Subgroup L₀),
      D ≤ (U : Subgroup T) ∧ Nonempty (D₀ ≃* D) ∧ Nat.card U * p ^ s ∣ B * Nat.card D := by
  obtain ⟨A, E, U, hInn, hEA, hpA, ⟨e⟩⟩ := h.exists_sylow_embedding
  have hinj := conj_injective_of_center_eq_bot hZ
  have hNcard : Nat.card (inner L₀) = Nat.card L₀ :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hE : IsPGroup p E := U.isPGroup'.of_equiv e.symm
  have hmain := card_mul_pow_dvd_of_isPGroup (N := inner L₀) (S := E) (B := B) (s := s) hE
    (by rw [hNcard]; exact hs) fun S' hS' hS'p => hpA S' (hS'.trans (sup_le hEA hInn)) hS'p
  let f : E →* T := (U : Subgroup T).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hEU : Nat.card E = Nat.card U := Nat.card_congr e.toEquiv
  refine ⟨U, ((inner L₀).subgroupOf E).map f, E.comap (MulAut.conj : L₀ →* MulAut L₀), ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact (e y).2
  · let Θ₁ : E.comap (MulAut.conj : L₀ →* MulAut L₀) →* E :=
      ((MulAut.conj : L₀ →* MulAut L₀).comp
        (E.comap (MulAut.conj : L₀ →* MulAut L₀)).subtype).codRestrict E fun g => g.2
    let Θ : E.comap (MulAut.conj : L₀ →* MulAut L₀) →* ↥((inner L₀).subgroupOf E) :=
      Θ₁.codRestrict ((inner L₀).subgroupOf E) fun g => ⟨(g : L₀), rfl⟩
    have hΘ : Function.Bijective Θ := by
      constructor
      · intro g g' hgg'
        apply Subtype.ext
        apply hinj
        have := congrArg (fun z : ↥((inner L₀).subgroupOf E) => ((z : E) : MulAut L₀)) hgg'
        exact this
      · rintro ⟨⟨x, hxE⟩, hxN⟩
        obtain ⟨g, hg⟩ := hxN
        exact ⟨⟨g, show (MulAut.conj : L₀ →* MulAut L₀) g ∈ E by rw [hg]; exact hxE⟩,
          Subtype.ext (Subtype.ext hg)⟩
    exact ⟨(MulEquiv.ofBijective Θ hΘ).trans
      (Subgroup.equivMapOfInjective ((inner L₀).subgroupOf E) f hf)⟩
  · rw [Subgroup.card_map_of_injective hf, ← hEU]
    exact hmain

end CFSG.AGLEmbedding
