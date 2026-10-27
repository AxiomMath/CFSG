module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm
import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup Equiv Equiv.Perm

theorem a10c_cycleType_of_pow_five (σ : Perm (Fin 10)) (h5 : σ ^ 5 = 1) (h1 : σ ≠ 1) :
    σ.cycleType = {5} ∨ σ.cycleType = {5, 5} := by
  have hmem : ∀ n ∈ σ.cycleType, n = 5 := by
    intro n hn
    have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    have hd : n ∣ 5 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one h5)
    rcases (Nat.dvd_prime Nat.prime_five).1 hd with h | h
    · omega
    · exact h
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 5 :=
    Multiset.eq_replicate_card.2 hmem
  have hsum : σ.cycleType.sum ≤ 10 := by simpa using Equiv.Perm.sum_cycleType_le σ
  have hpos : 0 < Multiset.card σ.cycleType := Equiv.Perm.card_cycleType_pos.2 h1
  have hsum' : σ.cycleType.sum = Multiset.card σ.cycleType * 5 := by
    conv_lhs => rw [hrep]
    simp
  have hc : Multiset.card σ.cycleType = 1 ∨ Multiset.card σ.cycleType = 2 := by omega
  rcases hc with hc | hc
  · left; rw [hrep, hc]; rfl
  · right; rw [hrep, hc]; rfl

theorem a10c_card_centralizer_perm_five (σ : Perm (Fin 10)) (h : σ.cycleType = {5}) :
    Nat.card (centralizer ({σ} : Set (Perm (Fin 10)))) = 600 := by
  rw [Equiv.Perm.nat_card_centralizer, h]
  decide

theorem a10c_card_centralizer_perm_five_five (σ : Perm (Fin 10)) (h : σ.cycleType = {5, 5}) :
    Nat.card (centralizer ({σ} : Set (Perm (Fin 10)))) = 50 := by
  rw [Equiv.Perm.nat_card_centralizer, h]
  decide

theorem a10c_card_centralizer_equiv {K L : Type} [Group K] [Group L] (e : K ≃* L) (k : K) :
    Nat.card (centralizer ({k} : Set K)) = Nat.card (centralizer ({e k} : Set L)) := by
  refine Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg e h
    simpa [map_mul] using this
  · intro h
    apply e.injective
    simpa [map_mul] using h

theorem a10c_card_centralizer_alt (u : alternatingGroup (Fin 10)) (τ : Perm (Fin 10))
    (hτ : sign τ = -1) (hcomm : τ * (u : Perm (Fin 10)) = (u : Perm (Fin 10)) * τ) :
    Nat.card (centralizer ({u} : Set (alternatingGroup (Fin 10)))) * 2 =
      Nat.card (centralizer ({(u : Perm (Fin 10))} : Set (Perm (Fin 10)))) := by
  set C := centralizer ({(u : Perm (Fin 10))} : Set (Perm (Fin 10))) with hC
  let f : C →* ℤˣ := (sign : Perm (Fin 10) →* ℤˣ).comp C.subtype
  have hτC : τ ∈ C := by rw [hC, mem_centralizer_singleton_iff]; exact hcomm
  have hsurj : Function.Surjective f := by
    intro z
    rcases Int.units_eq_one_or z with rfl | rfl
    · exact ⟨1, by simp [f]⟩
    · exact ⟨⟨τ, hτC⟩, by simp [f, hτ]⟩
  have hidx : f.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top]
    simp
  have h1 := Subgroup.card_mul_index f.ker
  have hmemC : ∀ g : alternatingGroup (Fin 10), g ∈ centralizer ({u} : Set (alternatingGroup (Fin 10))) →
      (g : Perm (Fin 10)) ∈ C := by
    intro g hg
    rw [mem_centralizer_singleton_iff] at hg
    rw [hC, mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hg
  have hsgn : ∀ x : C, x ∈ f.ker → sign (x : Perm (Fin 10)) = 1 := by
    intro x hx
    simpa [f] using hx
  have h2 : Nat.card (centralizer ({u} : Set (alternatingGroup (Fin 10)))) = Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun g => ⟨⟨g.1.1, hmemC g.1 g.2⟩, by simpa [f] using mem_alternatingGroup.1 g.1.2⟩
        invFun := fun h => ⟨⟨h.1.1, mem_alternatingGroup.2 (hsgn h.1 h.2)⟩, ?_⟩
        left_inv := fun g => rfl
        right_inv := fun h => rfl }
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.1 h.1.2
  rw [h2, ← h1, hidx]

theorem a10c_cycleType_formPerm (l : List (Fin 10)) (hl : l.Nodup) (hn : l.length = 5) :
    l.formPerm.cycleType = {5} := by
  have hcyc : l.formPerm.IsCycle := List.isCycle_formPerm hl (by omega)
  have hne : ∀ x : Fin 10, l ≠ [x] := by
    intro x h
    rw [h] at hn
    simp at hn
  rw [hcyc.cycleType, List.support_formPerm_of_nodup l hl hne, List.toFinset_card_of_nodup hl, hn]

theorem a10c_exists_odd_of_conj {σ σ₀ τ₀ : Perm (Fin 10)} (hc : IsConj σ σ₀) (hτ₀ : sign τ₀ = -1)
    (hcomm : τ₀ * σ₀ = σ₀ * τ₀) : ∃ τ : Perm (Fin 10), sign τ = -1 ∧ τ * σ = σ * τ := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hc
  refine ⟨g⁻¹ * τ₀ * g, ?_, ?_⟩
  · simp [Equiv.Perm.sign_mul, hτ₀]
  · have hσ : σ = g⁻¹ * σ₀ * g := by rw [← hg]; group
    rw [hσ]
    calc g⁻¹ * τ₀ * g * (g⁻¹ * σ₀ * g) = g⁻¹ * (τ₀ * σ₀) * g := by group
      _ = g⁻¹ * (σ₀ * τ₀) * g := by rw [hcomm]
      _ = g⁻¹ * σ₀ * g * (g⁻¹ * τ₀ * g) := by group

def a10c_cyc1 : Perm (Fin 10) := c[0, 1, 2, 3, 4]
def a10c_cyc2 : Perm (Fin 10) := c[5, 6, 7, 8, 9]
def a10c_swp1 : Perm (Fin 10) := swap 5 6
def a10c_swp5 : Perm (Fin 10) := swap 0 5 * swap 1 6 * swap 2 7 * swap 3 8 * swap 4 9

theorem a10c_cyc1_cycleType : a10c_cyc1.cycleType = {5} :=
  a10c_cycleType_formPerm _ (by decide) rfl

theorem a10c_cyc2_cycleType : a10c_cyc2.cycleType = {5} :=
  a10c_cycleType_formPerm _ (by decide) rfl

theorem a10c_cyc_disjoint : a10c_cyc1.Disjoint a10c_cyc2 := by
  unfold Equiv.Perm.Disjoint a10c_cyc1 a10c_cyc2
  decide

theorem a10c_cyc12_cycleType : (a10c_cyc1 * a10c_cyc2).cycleType = {5, 5} := by
  rw [a10c_cyc_disjoint.cycleType_mul, a10c_cyc1_cycleType, a10c_cyc2_cycleType]
  rfl

theorem a10c_swp1_sign : sign a10c_swp1 = -1 := by decide

theorem a10c_swp1_comm : a10c_swp1 * a10c_cyc1 = a10c_cyc1 * a10c_swp1 := by
  unfold a10c_swp1 a10c_cyc1
  decide

theorem a10c_swp5_sign : sign a10c_swp5 = -1 := by decide

theorem a10c_swp5_comm : a10c_swp5 * (a10c_cyc1 * a10c_cyc2) = (a10c_cyc1 * a10c_cyc2) * a10c_swp5 := by
  unfold a10c_swp5 a10c_cyc1 a10c_cyc2
  decide

theorem a10c_exists_odd_comm (σ : Perm (Fin 10))
    (h : σ.cycleType = {5} ∨ σ.cycleType = {5, 5}) :
    ∃ τ : Perm (Fin 10), sign τ = -1 ∧ τ * σ = σ * τ := by
  rcases h with h | h
  · exact a10c_exists_odd_of_conj (σ₀ := a10c_cyc1)
      (isConj_iff_cycleType_eq.2 (by rw [h, a10c_cyc1_cycleType])) a10c_swp1_sign a10c_swp1_comm
  · exact a10c_exists_odd_of_conj (σ₀ := a10c_cyc1 * a10c_cyc2)
      (isConj_iff_cycleType_eq.2 (by rw [h, a10c_cyc12_cycleType])) a10c_swp5_sign a10c_swp5_comm

theorem a10_five_cent_card (u : alternatingGroup (Fin 10)) (hu : u ^ 5 = 1) (hu1 : u ≠ 1) :
    ((u : Perm (Fin 10)).cycleType = {5} ∧
        Nat.card (centralizer ({u} : Set (alternatingGroup (Fin 10)))) = 300) ∨
      ((u : Perm (Fin 10)).cycleType = {5, 5} ∧
        Nat.card (centralizer ({u} : Set (alternatingGroup (Fin 10)))) = 25) := by
  have h5 : (u : Perm (Fin 10)) ^ 5 = 1 := by
    have := congrArg Subtype.val hu
    simpa using this
  have h1 : (u : Perm (Fin 10)) ≠ 1 := fun h => hu1 (Subtype.ext h)
  rcases a10c_cycleType_of_pow_five _ h5 h1 with h | h
  · left
    refine ⟨h, ?_⟩
    obtain ⟨τ, hτ, hc⟩ := a10c_exists_odd_comm _ (Or.inl h)
    have := a10c_card_centralizer_alt u τ hτ hc
    rw [a10c_card_centralizer_perm_five _ h] at this
    omega
  · right
    refine ⟨h, ?_⟩
    obtain ⟨τ, hτ, hc⟩ := a10c_exists_odd_comm _ (Or.inr h)
    have := a10c_card_centralizer_alt u τ hτ hc
    rw [a10c_card_centralizer_perm_five_five _ h] at this
    omega

theorem a10_cycleType_of_centralizer_card (u : alternatingGroup (Fin 10)) (hu : u ^ 5 = 1)
    (hu1 : u ≠ 1) :
    (Nat.card (centralizer ({u} : Set (alternatingGroup (Fin 10)))) = 25 ↔
        (u : Perm (Fin 10)).cycleType = {5, 5}) ∧
    (Nat.card (centralizer ({u} : Set (alternatingGroup (Fin 10)))) = 300 ↔
        (u : Perm (Fin 10)).cycleType = {5}) := by
  have h55 : ({5, 5} : Multiset ℕ) ≠ {5} := by decide
  rcases a10_five_cent_card u hu hu1 with ⟨h, hc⟩ | ⟨h, hc⟩
  · refine ⟨⟨fun h' => by omega, fun h' => absurd (h.symm.trans h') h55.symm⟩, ⟨fun _ => h, fun _ => hc⟩⟩
  · refine ⟨⟨fun _ => h, fun _ => hc⟩, ⟨fun h' => by omega, fun h' => absurd (h.symm.trans h') h55⟩⟩

theorem a10_cycleType_of_centralizer_card_equiv {K : Type} [Group K]
    (e : K ≃* alternatingGroup (Fin 10)) {k : K} (hk : k ^ 5 = 1) (hk1 : k ≠ 1) :
    (Nat.card (centralizer ({k} : Set K)) = 25 ↔
        ((e k : alternatingGroup (Fin 10)) : Perm (Fin 10)).cycleType = {5, 5}) ∧
    (Nat.card (centralizer ({k} : Set K)) = 300 ↔
        ((e k : alternatingGroup (Fin 10)) : Perm (Fin 10)).cycleType = {5}) := by
  have h5 : (e k) ^ 5 = 1 := by rw [← map_pow, hk, map_one]
  have h1 : e k ≠ 1 := fun h => hk1 (e.injective (by rw [h, map_one]))
  rw [a10c_card_centralizer_equiv e k]
  exact a10_cycleType_of_centralizer_card (e k) h5 h1

theorem a10_shape_of_centralizer_card {X : Type} [Group X] (K R U₀ : Subgroup X)
    (hK : IsA10Type 5 ↥K) {u : X} (huK : u ∈ K) (hu : u ∈ U₀) (hu5 : u ^ 5 = 1) (hu1 : u ≠ 1)
    (hc : Nat.card (centralizer ({(⟨u, huK⟩ : ↥K)} : Set ↥K)) = 25) : A10Shape K R U₀ := by
  obtain ⟨-, ⟨e⟩⟩ := hK
  refine ⟨e, u, ⟨hu, huK⟩, huK, ?_⟩
  have hk5 : (⟨u, huK⟩ : ↥K) ^ 5 = 1 := Subtype.ext (by simpa using hu5)
  have hk1 : (⟨u, huK⟩ : ↥K) ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  exact (a10_cycleType_of_centralizer_card_equiv e hk5 hk1).1.1 hc

theorem a10c_card_of_fixed {u : alternatingGroup (Fin 10)} (hu : u ^ 5 = 1) (hu1 : u ≠ 1)
    {p : Fin 10} (hp : (u : Perm (Fin 10)) p = p) :
    Nat.card (centralizer ({u} : Set (alternatingGroup (Fin 10)))) = 300 := by
  rcases a10_five_cent_card u hu hu1 with ⟨_, hc⟩ | ⟨h, _⟩
  · exact hc
  · exfalso
    have hs := Equiv.Perm.sum_cycleType (u : Perm (Fin 10))
    rw [h] at hs
    have hsupp : (u : Perm (Fin 10)).support = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [← hs]
      simp
    have hmem : p ∈ (u : Perm (Fin 10)).support := hsupp ▸ Finset.mem_univ p
    exact (Equiv.Perm.mem_support.1 hmem) hp

theorem a10c_card_of_noFixed {u : alternatingGroup (Fin 10)} (hu : u ^ 5 = 1) (hu1 : u ≠ 1)
    (hp : ∀ p : Fin 10, (u : Perm (Fin 10)) p ≠ p) :
    Nat.card (centralizer ({u} : Set (alternatingGroup (Fin 10)))) = 25 := by
  rcases a10_five_cent_card u hu hu1 with ⟨h, _⟩ | ⟨_, hc⟩
  · exfalso
    have hs := Equiv.Perm.sum_cycleType (u : Perm (Fin 10))
    rw [h] at hs
    have hsupp : (u : Perm (Fin 10)).support = Finset.univ := by
      ext p
      simp [hp p]
    rw [hsupp] at hs
    simp at hs
  · exact hc

theorem a10c_line_sup : A10Perm.line₁ ⊔ A10Perm.line₂ = A10Perm.S₀ := by
  apply le_antisymm
  · exact sup_le A10Perm.line₁_le A10Perm.line₂_le
  · rintro x ⟨i, j, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ (mem_zpowers A10Perm.a₁) i))
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (mem_zpowers A10Perm.a₂) j))

theorem a10c_a₁_apply (n : ℕ) : ((A10Perm.a₁ ^ n : A10Perm.A10) : Perm (Fin 10)) 5 = 5 := by
  have h : ((A10Perm.a₁ : A10Perm.A10) : Perm (Fin 10)) 5 = 5 := by decide
  have := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h n
  simpa using this

theorem a10c_a₂_apply (n : ℕ) : ((A10Perm.a₂ ^ n : A10Perm.A10) : Perm (Fin 10)) 0 = 0 := by
  have h : ((A10Perm.a₂ : A10Perm.A10) : Perm (Fin 10)) 0 = 0 := by decide
  have := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h n
  simpa using this

theorem a10c_card_line₁ {u : A10Perm.A10} (hu : u ∈ A10Perm.line₁) (hu1 : u ≠ 1) :
    Nat.card (centralizer ({u} : Set A10Perm.A10)) = 300 := by
  obtain ⟨n, rfl⟩ := A10Perm.mem_zpowers_nat.1 hu
  have hu5 : (A10Perm.a₁ ^ n) ^ 5 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, A10Perm.a₁_pow, one_pow]
  exact a10c_card_of_fixed hu5 hu1 (a10c_a₁_apply n)

theorem a10c_card_line₂ {u : A10Perm.A10} (hu : u ∈ A10Perm.line₂) (hu1 : u ≠ 1) :
    Nat.card (centralizer ({u} : Set A10Perm.A10)) = 300 := by
  obtain ⟨n, rfl⟩ := A10Perm.mem_zpowers_nat.1 hu
  have hu5 : (A10Perm.a₂ ^ n) ^ 5 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, A10Perm.a₂_pow, one_pow]
  exact a10c_card_of_fixed hu5 hu1 (a10c_a₂_apply n)

theorem a10c_card_diag {s : A10Perm.A10} (hs : s ∈ A10Perm.S₀) (h1 : s ∉ A10Perm.line₁)
    (h2 : s ∉ A10Perm.line₂) : Nat.card (centralizer ({s} : Set A10Perm.A10)) = 25 := by
  obtain ⟨i, j, rfl⟩ := A10Perm.mem_S₀.1 hs
  have hne : A10Perm.a₁ ^ i * A10Perm.a₂ ^ j ≠ 1 := fun h => h1 (h ▸ one_mem _)
  have h5 : (A10Perm.a₁ ^ i * A10Perm.a₂ ^ j) ^ 5 = 1 := by
    rw [(Commute.pow_pow A10Perm.a₁₂_commute i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i 5,
      mul_comm j 5, pow_mul, pow_mul, A10Perm.a₁_pow, A10Perm.a₂_pow, one_pow, one_pow, mul_one]
  refine a10c_card_of_noFixed h5 hne fun p hp => ?_
  have hmod : A10Perm.a₁ ^ i * A10Perm.a₂ ^ j = A10Perm.a₁ ^ (i % 5) * A10Perm.a₂ ^ (j % 5) := by
    rw [pow_eq_pow_mod i A10Perm.a₁_pow, pow_eq_pow_mod j A10Perm.a₂_pow]
  have hfix := A10Perm.fixed_check ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩
    ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩ p (by rw [← hmod]; exact hp)
  rcases hfix with h | h
  · have hi : i % 5 = 0 := by simpa [Fin.ext_iff] using h
    apply h2
    rw [hmod, hi, pow_zero, one_mul]
    exact Subgroup.pow_mem _ (mem_zpowers A10Perm.a₂) _
  · have hj : j % 5 = 0 := by simpa [Fin.ext_iff] using h
    apply h1
    rw [hmod, hj, pow_zero, mul_one]
    exact Subgroup.pow_mem _ (mem_zpowers A10Perm.a₁) _

@[expose] def A10CentFacts (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow 5 K, ∃ A₁ A₂ : Subgroup K, A₁ ≠ A₂ ∧ A₁ ≤ (S : Subgroup K) ∧ A₂ ≤ (S : Subgroup K) ∧
    Nat.card A₁ = 5 ∧ Nat.card A₂ = 5 ∧ A₁ ⊔ A₂ = (S : Subgroup K) ∧
    (∀ i : Subgroup K, (i = A₁ ∨ i = A₂) → ∀ a ∈ i, a ≠ 1 →
      Nat.card (Subgroup.centralizer ({a} : Set K)) = 300) ∧
    (∀ s ∈ (S : Subgroup K), s ∉ A₁ → s ∉ A₂ → s ≠ 1 →
      Nat.card (Subgroup.centralizer ({s} : Set K)) = 25)

theorem a10_centFacts : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → A10CentFacts K := by
  intro K _ _ hK S
  obtain ⟨-, ⟨e⟩⟩ := hK
  obtain ⟨ψ, hψ⟩ := A10Perm.exists_iso_sylow e S
  have hmem : ∀ (B : Subgroup A10Perm.A10) (x : K), x ∈ B.map ψ.symm.toMonoidHom ↔ ψ x ∈ B := by
    intro B x
    rw [Subgroup.mem_map_equiv]; simp
  have hcard : ∀ B : Subgroup A10Perm.A10, Nat.card (B.map ψ.symm.toMonoidHom) = Nat.card B :=
    fun B => Subgroup.card_map_of_injective ψ.symm.injective
  have hne1 : ∀ a : K, a ≠ 1 → ψ a ≠ 1 := fun a ha h => ha (ψ.injective (by rw [h, map_one]))
  refine ⟨A10Perm.line₁.map ψ.symm.toMonoidHom, A10Perm.line₂.map ψ.symm.toMonoidHom,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    exact A10Perm.line₁_ne_line₂ (Subgroup.map_injective ψ.symm.injective heq)
  · intro x hx
    rw [hmem] at hx
    exact (hψ x).2 (A10Perm.line₁_le hx)
  · intro x hx
    rw [hmem] at hx
    exact (hψ x).2 (A10Perm.line₂_le hx)
  · rw [hcard]; exact A10Perm.card_line₁
  · rw [hcard]; exact A10Perm.card_line₂
  · rw [← Subgroup.map_sup, a10c_line_sup]
    ext x
    rw [hmem]
    exact (hψ x).symm
  · rintro i (rfl | rfl) a ha ha1
    · rw [a10c_card_centralizer_equiv ψ a]
      exact a10c_card_line₁ ((hmem _ a).1 ha) (hne1 a ha1)
    · rw [a10c_card_centralizer_equiv ψ a]
      exact a10c_card_line₂ ((hmem _ a).1 ha) (hne1 a ha1)
  · intro s hs h1 h2 _
    rw [a10c_card_centralizer_equiv ψ s]
    exact a10c_card_diag ((hψ s).1 hs) (fun h => h1 ((hmem _ s).2 h)) (fun h => h2 ((hmem _ s).2 h))

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
