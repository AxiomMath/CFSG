module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightTorBase
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOmBSkel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K]

section Planes

variable {N : ℕ}

@[expose] def planesLow (hN : 2 ≤ N) : Fin 2 → Fin N := fun i => ⟨i, by omega⟩

@[expose] def planesTop (hN : 2 ≤ N) : Fin 2 → Fin N := fun i => ⟨N - 1 - i, by omega⟩

theorem planesLow_injective (hN : 2 ≤ N) : Function.Injective (planesLow hN) := by
  intro i j h
  exact Fin.ext (by simpa [planesLow] using congrArg Fin.val h)

theorem planesTop_injective (hN : 2 ≤ N) : Function.Injective (planesTop hN) := by
  intro i j h
  have h1 := congrArg Fin.val h
  simp only [planesTop] at h1
  have := i.2
  have := j.2
  exact Fin.ext (by omega)

theorem range_planesLow_subset (hN : 2 ≤ N) :
    Set.range (Sum.map (planesLow hN) (planesLow hN)) ⊆
      coords (⟨0, by omega⟩ : Fin N) ∪ coords (⟨1, by omega⟩ : Fin N) := by
  rintro _ ⟨x, rfl⟩
  have hi : ∀ i : Fin 2, planesLow hN i = ⟨0, by omega⟩ ∨ planesLow hN i = ⟨1, by omega⟩ := by
    intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases x with i | i <;> rcases hi i with h | h <;> simp [h, mem_coords]

theorem coords_low_subset_compl_range_planesTop (hN : 4 ≤ N) :
    coords (⟨0, by omega⟩ : Fin N) ∪ coords (⟨1, by omega⟩ : Fin N) ⊆
      (Set.range (Sum.map (planesTop (by omega : 2 ≤ N)) (planesTop (by omega)))) ᶜ := by
  have hne : ∀ (i : Fin 2) (k : Fin N), k.val < 2 → planesTop (by omega : 2 ≤ N) i ≠ k := by
    intro i k hk h
    have h1 := congrArg Fin.val h
    simp only [planesTop] at h1
    have := i.2
    omega
  rintro r hr ⟨x, rfl⟩
  simp only [Set.mem_union, mem_coords] at hr
  rcases x with i | i
  · simp only [Sum.map_inl, Sum.inl.injEq, reduceCtorEq, or_false] at hr
    rcases hr with h | h
    · exact hne i _ (by simp) h
    · exact hne i _ (by simp) h
  · simp only [Sum.map_inr, Sum.inr.injEq, reduceCtorEq, false_or] at hr
    rcases hr with h | h
    · exact hne i _ (by simp) h
    · exact hne i _ (by simp) h

end Planes

section Embeddings

variable {N : ℕ}

theorem spEmbed_planesTop_mem_centralizer (hN : 4 ≤ N) (g : StatedSp 2 K) :
    spEmbed (planesTop (by omega : 2 ≤ N)) (planesTop_injective (by omega)) g ∈
      centralizer ({twoCentralElt N (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩ (0 : K) 1} :
        Set (StatedSp N K)) := by
  rw [mem_centralizer_singleton_iff]
  exact (commute_suppGroup_compl (isSupp_spEmbed _ g)
    (suppGroup_mono (coords_low_subset_compl_range_planesTop hN)
      (twoCentralElt_mem_suppGroup 0 1))).eq

theorem spEmbed_planesTop_nsElt (hN : 2 ≤ N) :
    spEmbed (planesTop hN) (planesTop_injective hN) (nsElt (K := K) (0 : Fin 2)) =
      nsElt (⟨N - 1, by omega⟩ : Fin N) := by
  rw [nsElt, spEmbed_longBlock]
  rfl

theorem spEmbed_planesLow_nsElt (hN : 2 ≤ N) :
    spEmbed (planesLow hN) (planesLow_injective hN) (nsElt (K := K) (0 : Fin 2)) =
      nsElt (⟨0, by omega⟩ : Fin N) := by
  rw [nsElt, spEmbed_longBlock]
  rfl

end Embeddings

section Main

variable {N : ℕ}

theorem spTwoAToralAt_one_of_four_le (hN4 : 4 ≤ N) : SpTwoAToralAt N 1 := by
  intro K _ _ _ hK hN H _ Φ₁ Φ₂ hΦ₁ hΦ₂ _ hodd₁ _
  have hN2 : 2 ≤ N := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (StatedSp N K) := by
    have : Finite (GL (Fin N ⊕ Fin N) K) := inferInstance
    exact Subtype.finite
  set p₀ : Fin N := ⟨0, by omega⟩ with hp₀
  set p₁ : Fin N := ⟨1, by omega⟩ with hp₁
  have hp : p₀ ≠ p₁ := fun h => by simp [hp₀, hp₁, Fin.ext_iff] at h
  have hb : (1 : K) ≠ 0 := one_ne_zero
  have ha : (spARep N 1 : StatedSp N K) = twoCentralElt N p₀ p₁ 0 1 :=
    spARep_one_eq_twoCentralElt hN2
  have hnot := not_commute_nsElt_spARep_one (K := K) hN2
  have hXC : nsTorusSp K (⟨N - 1, by omega⟩ : Fin N) ≤
      centralizer ({twoCentralElt N p₀ p₁ (0 : K) 1} : Set (StatedSp N K)) := by
    have := nsTorusSp_le_centralizer_spARep (K := K) (j := 1) (k := (⟨N - 1, by omega⟩ : Fin N))
      (by simp only; omega)
    rwa [ha] at this
  rw [ha] at hodd₁ hnot ⊢
  set a : StatedSp N K := twoCentralElt N p₀ p₁ 0 1 with ha'
  set C : Subgroup (StatedSp N K) := centralizer ({a} : Set (StatedSp N K)) with hC
  set Γ : Subgroup (StatedSp N K) := oddElemClosure C with hΓ
  set X : Subgroup (StatedSp N K) := nsTorusSp K (⟨N - 1, by omega⟩ : Fin N) with hX
  set M : Subgroup (StatedSp 2 K) := commutator (StatedSp 2 K) with hM
  set ιY := spEmbed (K := K) (planesTop hN2) (planesTop_injective hN2) with hιY
  set ιW := spEmbed (K := K) (planesLow hN2) (planesLow_injective hN2) with hιW
  have hιYC : ∀ g, ιY g ∈ C := fun g => spEmbed_planesTop_mem_centralizer hN4 g
  have hMΓ : M.map ιY ≤ Γ := by
    have h := map_mono (f := ιY) (commutator_statedSp_two_le_closure_odd hK)
    rw [MonoidHom.map_closure] at h
    refine h.trans ((closure_le _).2 ?_)
    rintro _ ⟨y, ⟨-, hyo⟩, rfl⟩
    exact mem_oddElemClosure (hιYC y) (by rwa [orderOf_injective ιY (spEmbed_injective _) y])
  have hXΓ : X ≤ ⁅Γ, Γ⁆ := by
    rw [hX, nsTorusSp, zpowers_le, ← spEmbed_planesTop_nsElt hN2]
    have h1 : nsElt (K := K) (0 : Fin 2) ∈ ⁅M, M⁆ := by
      rw [hM, commutator_commutator_statedSp_two hK]
      exact nsElt_mem_commutator_statedSp_two
    have h2 := mem_map_of_mem ιY h1
    rw [map_commutator] at h2
    exact commutator_mono hMΓ hMΓ h2
  set S : Subgroup (StatedSp N K) := (X.map Φ₁).comap Φ₂ with hS
  have hSker : S ≤ (a2Coord hp hb).ker.map C.subtype :=
    (comap_map_le_commutator_oddElemClosure hΦ₁ hΦ₂ hodd₁ hXΓ).trans
      (commutator_oddElemClosure_le_map_ker_a2Coord hK hp hb)
  have hXodd : ∀ ξ ∈ X, Odd (orderOf ξ) := by
    intro ξ hξ
    have h1 : orderOf (⟨ξ, hξ⟩ : X) ∣ Nat.card X := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hX, card_nsTorusSp] at h1
    exact Odd.of_dvd_nat (by decide) h1
  have hXrange : X.map Φ₁ ≤ Φ₂.range := by
    rintro _ ⟨ξ, hξ, rfl⟩
    obtain ⟨y, -, hy⟩ := hodd₁ ξ (hXC hξ) (hXodd ξ hξ)
    exact ⟨y, hy⟩
  have hScard : Nat.card S = 3 := by
    have hmap : S.map Φ₂ = X.map Φ₁ := by
      rw [hS, Subgroup.map_comap_eq, inf_eq_right.2 hXrange]
    have h3 : Nat.card (S.map Φ₂) = Nat.card S := Subgroup.card_map_of_injective hΦ₂
    rw [hmap, Subgroup.card_map_of_injective hΦ₁, hX, card_nsTorusSp] at h3
    exact h3.symm
  set Q : Subgroup (StatedSp N K) := wRadical K p₀ p₁ with hQ
  set L := leviHom hp (0 : K) hb with hL
  set T : Subgroup (StatedSp N K) := (S.subgroupOf C).map L with hT
  have hTN : T ≤ normalizer (Q : Set (StatedSp N K)) :=
    (map_le_range _ _).trans (range_leviHom_le_normalizer_wRadical hp hb)
  have hQT : Q ⊓ T = ⊥ :=
    disjoint_iff.1 ((disjoint_wRadical_range_leviHom hp hb).mono_right (map_le_range _ _))
  have hLQ : ∀ g : C, (g : StatedSp N K) * (L g)⁻¹ ∈ Q := by
    intro g
    set m' : C := ⟨L g, leviHom_mem_centralizer hp hb g⟩
    have h := (mem_wRadical_iff_leviHom_eq_one hp hb (g := g * m'⁻¹)).2 (by
      rw [map_mul, map_inv, leviHom_leviHom, mul_inv_cancel])
    simpa [m'] using h
  have hST : S ≤ T ⊔ Q := by
    intro s hs
    obtain ⟨c, -, rfl⟩ := hSker hs
    have hcT : L c ∈ T := ⟨c, hs, rfl⟩
    show (c : StatedSp N K) ∈ T ⊔ Q
    have e : (c : StatedSp N K) = ((c : StatedSp N K) * (L c)⁻¹) * L c := by group
    rw [e]
    exact mul_mem (mem_sup_right (hLQ c)) (mem_sup_left hcT)
  obtain ⟨u, hu, hle⟩ := F4Pilot.exists_mem_map_conj_le_of_le_sup (isPGroup_wRadical hp) hTN hQT
    hST (by rw [hScard]; decide)
  have huC : u ∈ C := wRadical_le_centralizer_twoCentralElt 0 1 hu
  refine ⟨(M.map ιW).map (MulAut.conj u⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · rw [← map_commutator, ← map_commutator, hM, commutator_commutator_statedSp_two hK]
  · rintro _ ⟨_, ⟨g, -, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro s hs
    obtain ⟨s', hs', hs'eq⟩ := hle ⟨s, hs, rfl⟩
    have hα : a2Coord hp hb s' = 1 := by
      obtain ⟨c, hc, hcs⟩ := hSker (show (s' : StatedSp N K) ∈ S from hs')
      have : c = s' := Subtype.ext hcs
      rw [← this]
      exact hc
    have hcomm : Commute (L s') (ιW g) :=
      (commute_suppGroup_compl
        (suppGroup_mono (range_planesLow_subset hN2) (isSupp_spEmbed _ g))
        (leviHom_mem_suppGroup_compl hp hb hα)).symm
    rw [hs'eq] at hcomm
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hcomm ⊢
    calc s * (u⁻¹ * ιW g * u) = u⁻¹ * ((u * s * u⁻¹) * ιW g) * u := by group
      _ = u⁻¹ * (ιW g * (u * s * u⁻¹)) * u := by rw [hcomm.eq]
      _ = u⁻¹ * ιW g * u * s := by group
  · intro hP
    have h0 : nsElt (K := K) (0 : Fin 2) ∈ M := nsElt_mem_commutator_statedSp_two
    have hmem := hP ⟨ιW (nsElt 0), ⟨_, h0, rfl⟩, rfl⟩
    rw [mem_centralizer_singleton_iff] at hmem
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hmem
    rw [hιW, spEmbed_planesLow_nsElt hN2] at hmem
    have hua : u * a = a * u := mem_centralizer_singleton_iff.1 huC
    have hua' : u⁻¹ * a = a * u⁻¹ := by
      calc u⁻¹ * a = u⁻¹ * (a * u) * u⁻¹ := by group
        _ = u⁻¹ * (u * a) * u⁻¹ := by rw [hua]
        _ = a * u⁻¹ := by group
    apply hnot
    set x : StatedSp N K := nsElt (⟨0, by omega⟩ : Fin N) with hx
    calc x * a = u * ((u⁻¹ * x * u) * (u⁻¹ * a)) := by group
      _ = u * ((u⁻¹ * x * u) * (a * u⁻¹)) := by rw [hua']
      _ = u * ((u⁻¹ * x * u) * a) * u⁻¹ := by group
      _ = u * (a * (u⁻¹ * x * u)) * u⁻¹ := by rw [hmem]
      _ = (u * a) * u⁻¹ * x := by group
      _ = (a * u) * u⁻¹ * x := by rw [hua]
      _ = a * x := by group

end Main

end CFSG.SeitzReduction.SymplecticPilot
