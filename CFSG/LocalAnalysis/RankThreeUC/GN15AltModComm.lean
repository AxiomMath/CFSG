module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.CanonicalHeart

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement

section Generic

variable {Γ : Type*} [Group Γ]

theorem altMod_commutator_le_of_conj_mem {W K : Subgroup Γ}
    (hWK : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) : ⁅W, K⁆ ≤ W := by
  rw [Subgroup.commutator_le]
  intro w hw k hk
  have : ⁅w, k⁆ = w * (k * w⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact W.mul_mem hw (hWK k hk w⁻¹ (W.inv_mem hw))

theorem altMod_mem_normalizer_commutator {W K : Subgroup Γ} {g : Γ}
    (hW : g ∈ Subgroup.normalizer (W : Set Γ)) (hK : g ∈ Subgroup.normalizer (K : Set Γ)) :
    g ∈ Subgroup.normalizer ((⁅W, K⁆ : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hW hK ⊢
  rw [Subgroup.map_commutator, hW, hK]

theorem altMod_mem_normalizer_of_conj_mem {W K : Subgroup Γ}
    (hWK : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) {k : Γ} (hk : k ∈ K) :
    k ∈ Subgroup.normalizer (W : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨hWK k hk w, fun h => ?_⟩
  have := hWK k⁻¹ (K.inv_mem hk) _ h
  simpa [mul_assoc] using this

theorem altMod_conj_mem_commutator {W K : Subgroup Γ}
    (hWK : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) {k : Γ} (hk : k ∈ K) {m : Γ}
    (hm : m ∈ (⁅W, K⁆ : Subgroup Γ)) : k * m * k⁻¹ ∈ (⁅W, K⁆ : Subgroup Γ) := by
  have h := altMod_mem_normalizer_commutator (altMod_mem_normalizer_of_conj_mem hWK hk)
    (Subgroup.le_normalizer hk)
  exact (Subgroup.mem_normalizer_iff.mp h m).mp hm

theorem altMod_commutator_perfect {W K : Subgroup Γ} {n : ℕ} (h5 : 5 ≤ n)
    (hWK : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v)
    (Φ : ↥K →* alternatingGroup (Fin n)) (hΦ : Function.Surjective Φ)
    (hΦker : ∀ k : ↥K, Φ k = 1 → ∀ w ∈ W, (k : Γ) * w * (k : Γ)⁻¹ = w) :
    ⁅W, K⁆ ≤ ⁅⁅W, K⁆, K⁆ := by
  classical
  set M : Subgroup Γ := ⁅W, K⁆ with hM
  set N : Subgroup Γ := ⁅M, K⁆ with hN
  have hMW : M ≤ W := altMod_commutator_le_of_conj_mem hWK
  have hMK : ∀ k ∈ K, ∀ m ∈ M, k * m * k⁻¹ ∈ M := fun k hk m hm =>
    altMod_conj_mem_commutator hWK hk hm
  have : IsMulCommutative ↥M :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (hWc _ (hMW a.2) _ (hMW b.2))
  have hmem : ∀ w ∈ W, ∀ k ∈ K, ⁅w, k⁆ ∈ M := fun w hw k hk =>
    Subgroup.commutator_mem_commutator hw hk
  have key : ∀ w ∈ W, ∀ k : ↥K, ⁅w, (k : Γ)⁆ ∈ N := by
    intro w hw
    let c : ↥K → ↥M := fun k => ⟨⁅w, (k : Γ)⁆, hmem w hw k k.2⟩
    have hc : ∀ k : ↥K, ((c k : ↥M) : Γ) = ⁅w, (k : Γ)⁆ := fun k => rfl
    let δ : ↥K →* (↥M ⧸ N.subgroupOf M) :=
      { toFun := fun k => QuotientGroup.mk (c k)
        map_one' := by
          have : c 1 = 1 := Subtype.ext (by simp [hc])
          rw [this]; rfl
        map_mul' := fun k₁ k₂ => by
          rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
          have hm2 : ⁅w, (k₂ : Γ)⁆ ∈ M := hmem w hw _ k₂.2
          have hd : ⁅(⁅w, (k₂ : Γ)⁆)⁻¹, (k₁ : Γ)⁆⁻¹ ∈ N :=
            N.inv_mem (Subgroup.commutator_mem_commutator (M.inv_mem hm2) k₁.2)
          have e : (((c (k₁ * k₂))⁻¹ * (c k₁ * c k₂) : ↥M) : Γ) =
              ⁅(⁅w, (k₂ : Γ)⁆)⁻¹, (k₁ : Γ)⁆⁻¹ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc, Subgroup.coe_mul,
              commutatorElement_def]
            group
          rw [e]
          exact hd }
    have hδ : ∀ k : ↥K, Φ k = 1 → δ k = 1 := by
      intro k hk
      show (QuotientGroup.mk (c k) : ↥M ⧸ N.subgroupOf M) = 1
      have : c k = 1 := by
        apply Subtype.ext
        have h1 := hΦker k hk w hw
        show ⁅w, (k : Γ)⁆ = 1
        exact commutatorElement_eq_one_iff_mul_comm.2 (mul_inv_eq_iff_eq_mul.1 h1).symm
      rw [this]; rfl
    let δ' : alternatingGroup (Fin n) →* (↥M ⧸ N.subgroupOf M) :=
      (MonoidHom.liftOfSurjective (G₃ := ↥M ⧸ N.subgroupOf M) Φ hΦ) ⟨δ, fun k hk => hδ k hk⟩
    have hδ'Φ : ∀ k : ↥K, δ' (Φ k) = δ k := fun k =>
      Φ.liftOfRightInverse_comp_apply _ _ ⟨δ, fun k hk => hδ k hk⟩ k
    have hcomm : ∀ a b : ↥M ⧸ N.subgroupOf M, a * b = b * a := by
      intro a b
      induction a using QuotientGroup.induction_on with
      | _ a =>
        induction b using QuotientGroup.induction_on with
        | _ b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          congr 1
          exact Subtype.ext (hWc _ (hMW a.2) _ (hMW b.2))
    have hpf : commutator (alternatingGroup (Fin n)) = ⊤ :=
      commutator_alternatingGroup_eq_top (by rw [Nat.card_fin]; exact h5)
    have hker : ∀ x : alternatingGroup (Fin n), δ' x = 1 := by
      have : commutator (alternatingGroup (Fin n)) ≤ δ'.ker := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2
          (hcomm _ _)]
      intro x
      have hx : x ∈ commutator (alternatingGroup (Fin n)) := by rw [hpf]; exact Subgroup.mem_top x
      exact MonoidHom.mem_ker.mp (this hx)
    intro k
    have h1 : δ k = 1 := by rw [← hδ'Φ, hker]
    have h2 := h1
    show _ ∈ _
    have h3 : (QuotientGroup.mk (c k) : ↥M ⧸ N.subgroupOf M) = 1 := h2
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
    exact h3
  exact Subgroup.commutator_le.2 fun w hw k hk => key w hw ⟨k, hk⟩

theorem altMod_pi_surjective {W K M : Subgroup Γ} {n : ℕ} (h4 : 4 ≤ n) (hM : M = ⁅W, K⁆)
    (hWK : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (Φ : ↥K →* alternatingGroup (Fin n)) (hΦ : Function.Surjective Φ)
    (hne : M ≠ ⊥) (hperf : M ≤ ⁅M, K⁆)
    (π : ↥M →* Multiplicative (altHeart n))
    (hπk : ∀ u : ↥M, π u = 1 → ∀ k ∈ K, (k : Γ) * u * (k : Γ)⁻¹ = u)
    (hπi : ∀ (l : ↥K) (u u' : ↥M), (u' : Γ) = l * u * l⁻¹ →
      ∀ x : evenWeight n, Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
        Multiplicative.toAdd (π u') =
          (QuotientAddGroup.mk (evenWeightPerm (Φ l : Perm (Fin n)) x) : altHeart n)) :
    Function.Surjective π := by
  classical
  subst hM
  let U : AddSubgroup (altHeart n) :=
    { carrier := {a | ∃ u : ↥(⁅W, K⁆ : Subgroup Γ), Multiplicative.toAdd (π u) = a}
      add_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u * v, by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, by rw [map_one, toAdd_one]⟩
      neg_mem' := by
        rintro _ ⟨u, rfl⟩
        exact ⟨u⁻¹, by rw [map_inv, toAdd_inv]⟩ }
  have hU : ∀ σ ∈ alternatingGroup (Fin n), ∀ x : evenWeight n,
      (QuotientAddGroup.mk x : altHeart n) ∈ U →
        (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart n) ∈ U := by
    rintro σ hσ x ⟨u, hu⟩
    obtain ⟨l, hl⟩ := hΦ ⟨σ, hσ⟩
    have hσl : (Φ l : Perm (Fin n)) = σ := by rw [hl]
    have hmem : (l : Γ) * u * (l : Γ)⁻¹ ∈ (⁅W, K⁆ : Subgroup Γ) :=
      altMod_conj_mem_commutator hWK l.2 u.2
    refine ⟨⟨_, hmem⟩, ?_⟩
    have := hπi l u ⟨_, hmem⟩ rfl x hu
    rw [hσl] at this
    exact this
  rcases altHeart_irreducible h4 U hU with hbot | htop
  · exfalso
    apply hne
    rw [eq_bot_iff]
    refine hperf.trans ?_
    rw [Subgroup.commutator_le]
    intro m hm k hk
    rw [Subgroup.mem_bot]
    have h1 : π ⟨m, hm⟩ = 1 := by
      have : Multiplicative.toAdd (π ⟨m, hm⟩) ∈ U := ⟨_, rfl⟩
      rw [hbot, AddSubgroup.mem_bot] at this
      exact Multiplicative.toAdd.injective this
    have h2 := hπk ⟨m, hm⟩ h1 k hk
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_inv_eq_iff_eq_mul.1 h2).symm
  · intro b
    have : Multiplicative.toAdd b ∈ U := htop ▸ AddSubgroup.mem_top _
    obtain ⟨u, hu⟩ := this
    exact ⟨u, Multiplicative.toAdd.injective hu⟩

end Generic

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
