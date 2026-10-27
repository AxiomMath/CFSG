module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP3

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped Pointwise

variable {X : Type} [Group X]

theorem card_support_mulEquiv_alt_five {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {k : ℕ} (hα : Fintype.card α = k) (hβ : Fintype.card β = k) (hk5 : 5 ≤ k)
    (hk6 : k ≠ 6) (φ : alternatingGroup α ≃* alternatingGroup β) (g : alternatingGroup α) :
    ((φ g : alternatingGroup β) : Perm β).support.card = (g : Perm α).support.card := by
  classical
  let εα : α ≃ Fin k := Fintype.equivFinOfCardEq hα
  let εβ : β ≃ Fin k := Fintype.equivFinOfCardEq hβ
  let ψ : alternatingGroup (Fin k) ≃* alternatingGroup (Fin k) :=
    (εα.altCongrHom.symm.trans φ).trans εβ.altCongrHom
  obtain ⟨π, hπ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj k
    hk5 hk6).2 ψ
  have hψ : ∀ x : alternatingGroup (Fin k),
      ((ψ x : alternatingGroup (Fin k)) : Perm (Fin k)) = π * x * π⁻¹ := by
    intro x
    rw [← hπ]
    rfl
  have h1 : ψ (εα.altCongrHom g) = εβ.altCongrHom (φ g) := by
    change εβ.altCongrHom (φ (εα.altCongrHom.symm (εα.altCongrHom g))) = _
    rw [MulEquiv.symm_apply_apply]
  have h2 : ((εβ.altCongrHom (φ g) : alternatingGroup (Fin k)) : Perm (Fin k)) =
      π * εα.permCongr (g : Perm α) * π⁻¹ := by
    rw [← h1, hψ]
    rfl
  have h3 : ((εβ.altCongrHom (φ g) : alternatingGroup (Fin k)) : Perm (Fin k)) =
      εβ.permCongr ((φ g : alternatingGroup β) : Perm β) := rfl
  rw [← card_support_permCongr εβ, ← h3, h2, Perm.card_support_conj, card_support_permCongr]

theorem card_support_of_le_fixAlt_five {r k : ℕ} (hk5 : 5 ≤ k) (hk6 : k ≠ 6)
    {τ : Perm (Fin r)} (hτk : r - τ.support.card = k) {P : Subgroup (alternatingGroup (Fin r))}
    (hP : P ≤ fixAlt τ) {β : Type*} [Fintype β] [DecidableEq β] (hβ : Fintype.card β = k)
    (ψ : alternatingGroup β ≃* P) (g : alternatingGroup β) :
    (((ψ g : P) : alternatingGroup (Fin r)) : Perm (Fin r)).support.card =
      (g : Perm β).support.card := by
  classical
  have : Nontrivial β := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hPc : Nat.card P = k.factorial / 2 := by
    rw [← Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card, hβ]
  have hFc : Nat.card (fixAlt τ) = k.factorial / 2 := by
    rw [card_fixAlt (by omega), hτk]
  have hPeq : P = fixAlt τ := eq_of_le_of_card_ge hP (by rw [hPc, hFc])
  have hcard : Fintype.card ↥(τ.supportᶜ : Finset (Fin r)) = k := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hτk]
  obtain ⟨φ, hφ⟩ := exists_fixAlt_equiv τ
  let Ψ : alternatingGroup β ≃* alternatingGroup ↥(τ.supportᶜ : Finset (Fin r)) :=
    (ψ.trans (MulEquiv.subgroupCongr hPeq)).trans φ.symm
  have hΨ : (((ψ g : P) : alternatingGroup (Fin r)) : Perm (Fin r)) =
      Perm.ofSubtype ((Ψ g : alternatingGroup ↥(τ.supportᶜ : Finset (Fin r))) :
        Perm ↥(τ.supportᶜ : Finset (Fin r))) := by
    have h1 : φ (Ψ g) = MulEquiv.subgroupCongr hPeq (ψ g) := by
      change φ (φ.symm _) = _
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [← hφ, h1]
    rfl
  rw [hΨ, card_support_ofSubtype]
  exact card_support_mulEquiv_alt_five hβ hcard hk5 hk6 Ψ g

theorem exists_image_equiv_of_component [Finite X] {M Je : Subgroup X} {r k : ℕ} (hk : 5 ≤ k)
    (hr5 : 5 ≤ r) (hr6 : r ≠ 6) (θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)} (hρ : IsPermAction θM ρ)
    (hJeN : Je ≤ normalizer (M : Set X)) (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Je = ⊤)
    {β : Type*} [Fintype β] [DecidableEq β] (hβ : Fintype.card β = k)
    (χ : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* alternatingGroup β)
    (hne : ∃ x : ↥Je, ρ ⟨x, hJeN x.2⟩ ≠ 1) {t : X} (htM : t ∈ normalizer (M : Set X))
    (htt : t * t = 1) (hJeM : Je ≤ M) (hJeC : Je ≤ centralizer ({t} : Set X))
    (hJepc : IsPComponent 2 (Je.subgroupOf (M ⊓ centralizer ({t} : Set X)))) :
    ∃ τ : Perm (Fin r), r - τ.support.card = k ∧
      ∃ ψ : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* fixAlt τ, ∀ x : ↥Je,
        (((ψ (x : ↥Je ⧸ pPrimeCore 2 ↥Je) : fixAlt τ) : alternatingGroup (Fin r)) :
          Perm (Fin r)) = ρ ⟨x, hJeN x.2⟩ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eJe : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* alternatingGroup (Fin k) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  obtain ⟨x₀, hx₀⟩ := hne
  set π : ↥M →* alternatingGroup (Fin r) :=
    θM.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥M)) with hπdef
  obtain ⟨τ, hP, hτk⟩ :=
    exists_perm_of_fixed_component htM htt hJeM hJeC hJepc hk hr5 hr6 eJe θM
  let φ : ↥Je →* alternatingGroup (Fin r) := π.comp (inclusion hJeM)
  have hρin : ∀ x : ↥Je, ρ ⟨x, hJeN x.2⟩ = ((φ x : alternatingGroup (Fin r)) : Perm (Fin r)) :=
    fun x => hρ.apply_of_mem (by omega) (inclusion hJeM x)
  have hφ : φ x₀ ≠ 1 := by
    intro h
    apply hx₀
    rw [hρin, h]
    rfl
  have hQ : ∀ x, φ x ∈ fixAlt τ := fun x => hP ⟨inclusion hJeM x, x.2, rfl⟩
  have hQc : Nat.card (fixAlt τ) ≤ k.factorial / 2 := by
    rw [card_fixAlt (by omega), hτk]
  obtain ⟨ψ, hψ⟩ := exists_coreQuot_equiv_of_hom hres hk eJe φ ⟨x₀, hφ⟩ hQ hQc
  exact ⟨τ, hτk, ψ, fun x => by rw [hψ x, hρin]⟩

theorem alt_sup_centralizer_eq_top {m : ℕ} (hm : Odd m) {S : Finset (Fin m)}
    {σ : Perm (Fin m)} (hσ2 : σ * σ = 1) (hσ4 : σ.support.card = 4) (hσS : σ.support ⊆ S)
    (hS5 : 4 < S.card) {G : Subgroup (alternatingGroup (Fin m))}
    (hS : ∀ b : alternatingGroup (Fin m), (∀ ω ∉ S, (b : Perm (Fin m)) ω = ω) → b ∈ G)
    (hC : ∀ b : alternatingGroup (Fin m), (b : Perm (Fin m)) * σ = σ * b → b ∈ G) :
    G = ⊤ := by
  classical
  have hD : ∀ b : alternatingGroup (Fin m), (∀ ω ∈ σ.support, (b : Perm (Fin m)) ω = ω) →
      b ∈ G := by
    intro b hb
    refine hC b ?_
    have hdisj : Perm.Disjoint (b : Perm (Fin m)) σ := by
      intro ω
      by_cases hω : ω ∈ σ.support
      · exact Or.inl (hb ω hω)
      · exact Or.inr (Perm.notMem_support.mp hω)
    exact hdisj.commute.eq
  by_cases hSu : ∀ ω, ω ∈ S
  · exact eq_top_iff.mpr fun b _ => hS b fun ω hω => absurd (hSu ω) hω
  push Not at hSu
  obtain ⟨w, hwS⟩ := hSu
  obtain ⟨x, hxS, hxD⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := σ.support) (t := S) (by omega)
  have hm7 : 7 ≤ m := by
    have h2 : S.card < (Finset.univ : Finset (Fin m)).card :=
      Finset.card_lt_card ⟨Finset.subset_univ _, fun h => hwS (h (Finset.mem_univ w))⟩
    rw [Finset.card_univ, Fintype.card_fin] at h2
    obtain ⟨k, hk⟩ := hm
    omega
  obtain ⟨y, hyD, hyw, hyx⟩ : ∃ y, y ∉ σ.support ∧ y ≠ w ∧ y ≠ x := by
    have h1 : (σ.support ∪ {w, x}).card < (Finset.univ : Finset (Fin m)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      calc (σ.support ∪ {w, x}).card ≤ σ.support.card + ({w, x} : Finset (Fin m)).card :=
            Finset.card_union_le _ _
        _ ≤ 4 + 2 := by rw [hσ4]; exact Nat.add_le_add_left Finset.card_le_two 4
        _ < m := by omega
    obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card h1
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    exact ⟨y, hy.1, hy.2.1, hy.2.2⟩
  have hwD : w ∉ σ.support := fun h => hwS (hσS h)
  have hwx : w ≠ x := fun h => hwS (h ▸ hxS)
  have hstab : MulAction.stabilizer (alternatingGroup (Fin m))
      ((Sᶜ : Finset (Fin m)) : Set (Fin m)) ≤ G := by
    intro b hb
    obtain ⟨σD, σF, hb', h1, h2, -, -⟩ :=
      exists_split Sᶜ fun v => Sol78.apply_mem_iff_of_mem_stabilizer hb v
    have h1' : ∀ v ∈ S, σD v = v := fun v hv => h1 v (by simpa using hv)
    have h2' : ∀ v ∉ S, σF v = v := fun v hv => h2 v (Finset.mem_compl.mpr hv)
    have hsign : Perm.sign σD * Perm.sign σF = 1 := by
      rw [← map_mul, ← hb']
      exact Perm.mem_alternatingGroup.mp b.2
    rcases Int.units_eq_one_or (Perm.sign σD) with hD1 | hD1
    · have hF1 : Perm.sign σF = 1 := by rw [hD1, one_mul] at hsign; exact hsign
      have hσD : (⟨σD, Perm.mem_alternatingGroup.mpr hD1⟩ : alternatingGroup (Fin m)) ∈ G :=
        hD _ fun v hv => h1' v (hσS hv)
      have hσF : (⟨σF, Perm.mem_alternatingGroup.mpr hF1⟩ : alternatingGroup (Fin m)) ∈ G :=
        hS _ h2'
      have hbe : b = ⟨σD, Perm.mem_alternatingGroup.mpr hD1⟩ *
          ⟨σF, Perm.mem_alternatingGroup.mpr hF1⟩ := Subtype.ext hb'
      rw [hbe]
      exact mul_mem hσD hσF
    · have hF1 : Perm.sign σF = -1 := by
        rcases Int.units_eq_one_or (Perm.sign σF) with h | h
        · rw [hD1, h] at hsign
          exact absurd hsign (by decide)
        · exact h
      obtain ⟨u, hu⟩ : ∃ u, σD u ≠ u := by
        by_contra hcon
        push Not at hcon
        have h1 : σD = 1 := Equiv.ext hcon
        rw [h1, map_one] at hD1
        exact absurd hD1 (by decide)
      have huS : u ∉ S := fun h => hu (h1' u h)
      have hu'S : σD u ∉ S := fun h => hu (σD.injective (h1' (σD u) h))
      have huu' : u ≠ σD u := fun h => hu h.symm
      obtain ⟨d, hd⟩ : ∃ d, d ∈ σ.support := Finset.card_pos.mp (by omega)
      have hdS : d ∈ S := hσS hd
      have hσdS : σ d ∈ S := hσS (Perm.apply_mem_support.mpr hd)
      have hdσd : d ≠ σ d := fun h => (Perm.mem_support.mp hd) h.symm
      have hcA : swap u (σD u) * swap d (σ d) ∈ alternatingGroup (Fin m) := by
        rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap huu', Perm.sign_swap hdσd]
        decide
      have hcG : (⟨swap u (σD u) * swap d (σ d), hcA⟩ : alternatingGroup (Fin m)) ∈ G := by
        refine hC _ ?_
        change swap u (σD u) * swap d (σ d) * σ = σ * (swap u (σD u) * swap d (σ d))
        have hswσ : swap u (σD u) * σ = σ * swap u (σD u) := by
          have hdisj : Perm.Disjoint (swap u (σD u)) σ := by
            intro v
            by_cases hv : v = u ∨ v = σD u
            · right
              rcases hv with rfl | rfl
              · exact Perm.notMem_support.mp fun h => huS (hσS h)
              · exact Perm.notMem_support.mp fun h => hu'S (hσS h)
            · left
              push Not at hv
              exact swap_apply_of_ne_of_ne hv.1 hv.2
          exact hdisj.commute.eq
        have hsdσ : swap d (σ d) * σ = σ * swap d (σ d) := swap_mul_comm_of_involution hσ2 d
        rw [mul_assoc, hsdσ, ← mul_assoc, hswσ, mul_assoc]
      have hD1' : Perm.sign (σD * swap u (σD u)) = 1 := by
        rw [map_mul, hD1, Perm.sign_swap huu']
        decide
      have hF1' : Perm.sign (swap d (σ d) * σF) = 1 := by
        rw [map_mul, hF1, Perm.sign_swap hdσd]
        decide
      have hσDG : (⟨σD * swap u (σD u), Perm.mem_alternatingGroup.mpr hD1'⟩ :
          alternatingGroup (Fin m)) ∈ G := by
        refine hD _ fun v hv => ?_
        have hvS := hσS hv
        have hvu : v ≠ u := fun h => huS (h ▸ hvS)
        have hvu' : v ≠ σD u := fun h => hu'S (h ▸ hvS)
        change σD (swap u (σD u) v) = v
        rw [swap_apply_of_ne_of_ne hvu hvu', h1' v hvS]
      have hσFG : (⟨swap d (σ d) * σF, Perm.mem_alternatingGroup.mpr hF1'⟩ :
          alternatingGroup (Fin m)) ∈ G := by
        refine hS _ fun v hv => ?_
        have hvd : v ≠ d := fun h => hv (h ▸ hdS)
        have hvσd : v ≠ σ d := fun h => hv (h ▸ hσdS)
        change swap d (σ d) (σF v) = v
        rw [h2' v hv, swap_apply_of_ne_of_ne hvd hvσd]
      have hbe : b = ⟨σD * swap u (σD u), Perm.mem_alternatingGroup.mpr hD1'⟩ *
          ⟨swap u (σD u) * swap d (σ d), hcA⟩ *
            ⟨swap d (σ d) * σF, Perm.mem_alternatingGroup.mpr hF1'⟩ := by
        apply Subtype.ext
        change (b : Perm (Fin m)) =
          σD * swap u (σD u) * (swap u (σD u) * swap d (σ d)) * (swap d (σ d) * σF)
        rw [hb']
        simp only [mul_assoc, swap_mul_self_mul]
      rw [hbe]
      exact mul_mem (mul_mem hσDG hcG) hσFG
  have hb₀A : swap w y * swap w x ∈ alternatingGroup (Fin m) := by
    rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (Ne.symm hyw), Perm.sign_swap hwx]
    decide
  have hb₀G : (⟨swap w y * swap w x, hb₀A⟩ : alternatingGroup (Fin m)) ∈ G := by
    refine hD _ fun v hv => ?_
    have hvw : v ≠ w := fun h => hwD (h ▸ hv)
    have hvx : v ≠ x := fun h => hxD (h ▸ hv)
    have hvy : v ≠ y := fun h => hyD (h ▸ hv)
    change (swap w y * swap w x) v = v
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hvw hvx, swap_apply_of_ne_of_ne hvw hvy]
  have hb₀S : (⟨swap w y * swap w x, hb₀A⟩ : alternatingGroup (Fin m)) ∉
      MulAction.stabilizer (alternatingGroup (Fin m)) ((Sᶜ : Finset (Fin m)) : Set (Fin m)) := by
    intro h
    have h1 := (Sol78.apply_mem_iff_of_mem_stabilizer h w).mpr (Finset.mem_compl.mpr hwS)
    change (swap w y * swap w x) w ∈ Sᶜ at h1
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hwx) hyx.symm] at h1
    exact (Finset.mem_compl.mp h1) hxS
  have hco := alternatingGroup.isCoatom_stabilizer (α := Fin m)
    (s := ((Sᶜ : Finset (Fin m)) : Set (Fin m))) ⟨w, by simpa using hwS⟩ ⟨x, by simpa using hxS⟩
    (by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      intro h
      obtain ⟨k, hk⟩ := hm
      omega)
  exact hco.2 _ (lt_of_le_of_ne hstab fun h => hb₀S (h ▸ hb₀G))

namespace SwapP2

theorem le_of_exact' [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
    {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
    {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X} {N₁ : Subgroup X}
    (hs : Setting t J n e E D M) (hd : Data t J n e E D M e₀ F DF r)
    (hOr : core (centralizer ({r} : Set X)) ≤ Hn E)
    (hFH : ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E)
    (hP : PumpData M e₀ r N₁) (hfix : conjBy N₁ e₀ = N₁)
    (hside : ∀ f ∈ F, ∃ a ∈ fixA M e₀ r, f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel N₁ ∧
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M)
    {m : ℕ} (hmo : Odd m) (hkm : n - 4 ≤ m)
    (θN : ↥N₁ ⧸ pPrimeCore 2 ↥N₁ ≃* alternatingGroup (Fin m)) : N₁ ≤ Hn E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  have hn9 := S.nine_le
  have hm6 : m ≠ 6 := by
    obtain ⟨a, ha⟩ := hmo
    omega
  have hk6 : n - 4 ≠ 6 := by
    obtain ⟨a, ha⟩ := S.pair.2.1
    omega
  obtain ⟨θ⟩ := hs.alt
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  have hJN : J ≤ normalizer (M : Set X) := le_normalizer_of_swap htH hs.le hs.pc hs.swap hs.diag
  obtain ⟨π, hπ⟩ := S.exists_perm_compat_of_swap hs.cent hs.le hs.pc hs.swap hs.diag hρ
  have he₀J : e₀ ∈ J := S.le hd.e₀E
  have he₀N : e₀ ∈ normalizer (M : Set X) := hJN he₀J
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀4 : (ρ ⟨e₀, he₀N⟩).support.card = 4 := by
    rw [hπ e₀ he₀J he₀N, Perm.card_support_conj]
    exact S.card_support_coreImage_E hd.e₀E hd.e₀1
  obtain ⟨hAle, hApc, ⟨χA⟩⟩ :=
    fixedLayer_facts_of_perm hs.le hs.pc hρ he₀N he₀2 he₀4.le (by omega)
  set A := GSLit.fixedLayer M (zpowers e₀) with hAdef
  have hAM : A ≤ M := (GSLit.fixedLayer_le_inf M (zpowers e₀)).trans inf_le_left
  have hAe : A ≤ centralizer ({e₀} : Set X) := hAle.trans inf_le_right
  have hAMe : A ≤ M ⊓ centralizer ({e₀} : Set X) := le_inf hAM hAe
  have hApcM : IsPComponent 2 (A.subgroupOf (M ⊓ centralizer ({e₀} : Set X))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hAMe (inf_le_inf_right _ hs.le) hApc
  obtain ⟨-, hAres, hAq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 A _ hAMe).mp hApcM
  have hAperf : ⁅A, A⁆ = A := UnbalancedCorr.commutator_eq_of_isPComponent hAMe hApcM
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hrK : r ∈ UnbalancedLayer.coreActionKernel M := hMtK hd.rM
  have hre₀ : r ∈ centralizer ({e₀} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀
  have hrA : r ∈ normalizer (A : Set X) := by
    refine GSLit.mem_normalizer_fixedLayer hrK.1 (centralizer_le_normalizer _ ?_)
    rw [centralizer_zpowers_eq' e₀]
    exact hre₀
  have hrKA : r ∈ UnbalancedLayer.coreActionKernel A := mem_coreActionKernel_of_le hAM hrK hrA
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have hR2 : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  have hArA : fixA M e₀ r ≤ A := (GSLit.fixedLayer_le_inf A (zpowers r)).trans inf_le_left
  obtain ⟨Φ, hΦ⟩ := exists_fixedLayer_coreQuot_equiv hAq (zpowers_le.mpr hrKA) hR2
  have hcardA : Fintype.card ↥((ρ ⟨e₀, he₀N⟩).supportᶜ : Finset (Fin n)) = n - 4 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, he₀4]
  obtain ⟨τM, hτM, ψM, hψM⟩ := exists_image_equiv_of_component (M := M) (Je := A) (by omega)
    (by omega) (by omega) θ hρ (hAM.trans le_normalizer) hAres hcardA χA
    (exists_rho_ne_one (by omega) hρ hAM (LocalCores.isQuasisimple_nontrivial hAq))
    he₀N he₀2 hAM hAe hApcM
  have he₀N₁ : e₀ ∈ normalizer (N₁ : Set X) := mem_normalizer_iff_map_conj_eq.mpr hfix
  obtain ⟨ρN, hρN⟩ := exists_isPermAction (M := N₁) (by omega) hm6 θN
  have hArN : fixA M e₀ r ≤ N₁ := by
    have h1 := hP.cover
    rwa [hfix, sup_idem] at h1
  have hlayer : IsPComponent 2 ((fixA M e₀ r).subgroupOf (N₁ ⊓ centralizer ({e₀} : Set X))) := by
    have h1 := hP.layer
    rwa [hfix, sup_idem] at h1
  have hAre : fixA M e₀ r ≤ centralizer ({e₀} : Set X) := hArA.trans hAe
  have hArY : fixA M e₀ r ≤ N₁ ⊓ centralizer ({e₀} : Set X) := le_inf hArN hAre
  obtain ⟨-, hArres, hArq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ _ hArY).mp hlayer
  have hArperf : ⁅fixA M e₀ r, fixA M e₀ r⁆ = fixA M e₀ r :=
    UnbalancedCorr.commutator_eq_of_isPComponent hArY hlayer
  obtain ⟨τ', hτ', ψN, hψN⟩ := exists_image_equiv_of_component (M := N₁) (Je := fixA M e₀ r)
    (k := n - 4) (by omega) (by omega) hm6 θN hρN (hArN.trans le_normalizer) hArres hcardA
    (Φ.trans χA) (exists_rho_ne_one (by omega) hρN hArN (LocalCores.isQuasisimple_nontrivial hArq))
    he₀N₁ he₀2 hArN hAre hlayer
  obtain ⟨f₁, -, -, hf₁F, -, -, hf₁1, -, -, -, -, -⟩ := exists_three_of_klein hd.Fk
  obtain ⟨a₁, ha₁, hfaN, hfaM⟩ := hside f₁ hf₁F
  have ha₁N : a₁ ∈ N₁ := hArN ha₁
  have ha₁A : a₁ ∈ A := hArA ha₁
  have hf₁J : f₁ ∈ J := hd.FJ hf₁F
  have hf₁M : f₁ ∈ normalizer (M : Set X) := hJN hf₁J
  have hf₁2 : f₁ * f₁ = 1 := by rw [← sq]; exact (card_sq_of_klein hd.Fk).2 f₁ hf₁F
  have hf₁N : f₁ ∈ normalizer (N₁ : Set X) := by
    have h1 : f₁ = (f₁ * a₁⁻¹) * a₁ := by group
    rw [h1]
    exact mul_mem hfaN.1 (le_normalizer ha₁N)
  have hρfa : ρ ⟨f₁, hf₁M⟩ = ρ ⟨a₁, le_normalizer (hAM ha₁A)⟩ := by
    have h1 := hρ.eq_one_of_mem_coreActionKernel (by omega) hfaM
    have h2 : (⟨f₁ * a₁⁻¹, hfaM.1⟩ : ↥(normalizer (M : Set X))) =
        ⟨f₁, hf₁M⟩ * (⟨a₁, le_normalizer (hAM ha₁A)⟩ : ↥(normalizer (M : Set X)))⁻¹ := rfl
    rw [h2, map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hρNfa : ρN ⟨f₁, hf₁N⟩ = ρN ⟨a₁, le_normalizer ha₁N⟩ := by
    have h1 := hρN.eq_one_of_mem_coreActionKernel (by omega) hfaN
    have h2 : (⟨f₁ * a₁⁻¹, hfaN.1⟩ : ↥(normalizer (N₁ : Set X))) =
        ⟨f₁, hf₁N⟩ * (⟨a₁, le_normalizer ha₁N⟩ : ↥(normalizer (N₁ : Set X)))⁻¹ := rfl
    rw [h2, map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hf₁4 : (ρ ⟨f₁, hf₁M⟩).support.card = 4 := by
    rw [hπ f₁ hf₁J hf₁M, Perm.card_support_conj]
    exact card_support_coreImage_of_four e hf₁J hf₁2 hf₁1 hd.DFc (hd.Fs ⟨f₁, hf₁J⟩ hf₁F)
  obtain ⟨φM, hφM⟩ := exists_fixAlt_equiv τM
  have hβ : Fintype.card ↥(τM.supportᶜ : Finset (Fin n)) = n - 4 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hτM]
  set q : ↥A ⧸ pPrimeCore 2 ↥A := ((⟨a₁, ha₁A⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) with hqdef
  have hq : Φ (((⟨a₁, ha₁⟩ : ↥(fixA M e₀ r)) : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r))) =
      q := hΦ ⟨a₁, ha₁⟩ ha₁A
  set ψ : alternatingGroup ↥(τM.supportᶜ : Finset (Fin n)) ≃* fixAlt τ' :=
    (φM.trans ψM.symm).trans (Φ.symm.trans ψN) with hψdef
  have hψg : ψ (φM.symm (ψM q)) = ψN (((⟨a₁, ha₁⟩ : ↥(fixA M e₀ r)) :
      ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r))) := by
    rw [hψdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply, ← hq, MulEquiv.symm_apply_apply]
  have hsupp := card_support_of_le_fixAlt_five (k := n - 4) (by omega) hk6 hτ'
    (le_refl (fixAlt τ')) hβ ψ (φM.symm (ψM q))
  rw [hψg, hψN ⟨a₁, ha₁⟩] at hsupp
  have hσ4 : (ρN ⟨f₁, hf₁N⟩).support.card = 4 := by
    rw [hρNfa]
    refine hsupp.trans ?_
    rw [← card_support_ofSubtype, ← hφM, MulEquiv.apply_symm_apply, hqdef, hψM ⟨a₁, ha₁A⟩,
      ← hρfa, hf₁4]
  have hσS : (ρN ⟨f₁, hf₁N⟩).support ⊆ τ'.supportᶜ := by
    rw [hρNfa, ← hψN ⟨a₁, ha₁⟩]
    exact mem_fixAlt.mp (ψN _).2
  have hScard : (τ'.supportᶜ).card = n - 4 := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  set πN : ↥N₁ →* alternatingGroup (Fin m) :=
    θN.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥N₁)) with hπNdef
  have hOH : (pPrimeCore 2 ↥N₁).map N₁.subtype ≤ Hn E :=
    (pPrimeCore_le_of_isPComponent hP.le hP.pc).trans hOr
  have hσ2 : ρN ⟨f₁, hf₁N⟩ * ρN ⟨f₁, hf₁N⟩ = 1 := by
    rw [← map_mul, show (⟨f₁, hf₁N⟩ : ↥(normalizer (N₁ : Set X))) * ⟨f₁, hf₁N⟩ = 1 from
      Subtype.ext hf₁2, map_one]
  refine le_of_map_eq_top θN hOH
    (alt_sup_centralizer_eq_top hmo hσ2 hσ4 hσS (by omega) ?_ ?_)
  ·
    intro b hb
    have hbF : b ∈ fixAlt τ' := by
      rw [mem_fixAlt]
      intro ω hω
      by_contra hωF
      exact (Perm.mem_support.mp hω) (hb ω hωF)
    obtain ⟨q', hq'⟩ := ψN.surjective ⟨b, hbF⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q'
    have hxH : (x : X) ∈ Hn E := hs.le (hAM (hArA x.2))
    refine ⟨⟨x, hArN x.2⟩, hxH, Subtype.ext ?_⟩
    have h1 := hψN x
    rw [hq'] at h1
    rw [h1]
    exact (hρN.apply_of_mem (by omega) ⟨x, hArN x.2⟩).symm
  ·
    intro b hb
    obtain ⟨x, hxC, hxb⟩ := hρN.exists_lift hf₁N hf₁2 (b := b) hb
    exact ⟨x, hFH f₁ hf₁F hf₁1 hxC, hxb⟩

end SwapP2

end CFSG.ComponentClassification.SolMax
