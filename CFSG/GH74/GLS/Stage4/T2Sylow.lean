module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

theorem t2S_closure_sq {G : Type} [Group G] {z u : G} (hz : z * z = 1) (hu : u * u = 1)
    (huz : u * z = z * u) :
    ∀ g ∈ Subgroup.closure ({z, u} : Set G), g * g = 1 := by
  have hcomm : ∀ x ∈ Subgroup.closure ({z, u} : Set G), ∀ y ∈ Subgroup.closure ({z, u} : Set G),
      x * y = y * x := by
    intro x hx y hy
    refine Subgroup.closure_induction₂ (p := fun x y _ _ => x * y = y * x) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      hx hy
    · intro a b ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · rw [Set.mem_singleton_iff] at hb
        rw [hb]
        exact huz.symm
      · rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact huz
      · rw [Set.mem_singleton_iff] at ha hb
        rw [ha, hb]
    · intro a _
      simp
    · intro a _
      simp
    · intro a b c _ _ _ hac hbc
      rw [mul_assoc, hbc, ← mul_assoc, hac, mul_assoc]
    · intro a b c _ _ _ hab hac
      rw [← mul_assoc, hab, mul_assoc, hac, ← mul_assoc]
    · intro a b _ _ hab
      exact Commute.inv_left (show Commute a b from hab)
    · intro a b _ _ hab
      exact Commute.inv_right (show Commute a b from hab)
  intro g hg
  refine Subgroup.closure_induction (p := fun g _ => g * g = 1) ?_ ?_ ?_ ?_ hg
  · intro x hx
    rcases hx with rfl | hx
    · exact hz
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hu
  · simp
  · intro x y hx hy hx2 hy2
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hcomm y hy x hx]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2, hy2, mul_one]
  · intro x _ hx2
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [hx2, inv_one]

theorem t2S_exists_core {G : Type} [Group G] [Finite G] {z u : G} (hz2 : z * z = 1)
    (P : Sylow 2 G) (hPz : ∀ s ∈ (P : Subgroup G), s * z = z * s) (hu : u * u = 1)
    (huz : u * z = z * u) :
    ∃ S : Subgroup G, IsPGroup 2 ↥S ∧ ¬ 2 ∣ S.index ∧ z ∈ S ∧ u ∈ S ∧
      ∀ s ∈ S, s * z = z * s := by
  set C : Subgroup G := centralizer ({z} : Set G) with hC
  have hmemC : ∀ g : G, g ∈ C ↔ g * z = z * g := fun g => Subgroup.mem_centralizer_singleton_iff
  have hPC : (P : Subgroup G) ≤ C := fun s hs => (hmemC s).2 (hPz s hs)
  have hzA : z ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  have huA : u ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  have hA : IsPGroup 2 ↥(Subgroup.closure ({z, u} : Set G)) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [pow_two] using t2S_closure_sq hz2 hu huz g g.2
  have hA' : IsPGroup 2 ↥((Subgroup.closure ({z, u} : Set G)).subgroupOf C) := hA.comap_subtype
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥C).map C.subtype, Q.isPGroup'.map C.subtype, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.index_map_subtype]
    intro h
    rcases (Nat.prime_two.dvd_mul).1 h with h | h
    · exact Q.not_dvd_index h
    · exact P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hPC))
  · exact ⟨⟨z, (hmemC z).2 rfl⟩, hQ hzA, rfl⟩
  · exact ⟨⟨u, (hmemC u).2 huz⟩, hQ huA, rfl⟩
  · rintro s ⟨c, _, rfl⟩
    exact (hmemC c.1).1 c.2

theorem exists_sylow_two_centralizer {G : Type} [Group G] [Finite G] {z u : G}
    (hz : IsCentralInvolution z) (hu : u * u = 1) (huz : u * z = z * u) :
    ∃ S : Subgroup G, IsPGroup 2 ↥S ∧ ¬ 2 ∣ S.index ∧ z ∈ S ∧ u ∈ S ∧
      ∀ s ∈ S, s * z = z * s := by
  obtain ⟨hord, P, _, hPz⟩ := hz
  have hz2 : z * z = 1 := by
    have h : z ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hord.dvd
    simpa [pow_two] using h
  exact t2S_exists_core hz2 P hPz hu huz

theorem t2S_closure_pow {G : Type} [Group G] {s : Set G} (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    {n : ℕ} (hn : ∀ a ∈ s, a ^ n = 1) : ∀ g ∈ Subgroup.closure s, g ^ n = 1 := by
  have hcomm : ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
    intro x hx y hy
    refine Subgroup.closure_induction₂ (p := fun x y _ _ => x * y = y * x) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      hx hy
    · intro a b ha hb
      exact hc a ha b hb
    · intro a _
      simp
    · intro a _
      simp
    · intro a b c _ _ _ hac hbc
      rw [mul_assoc, hbc, ← mul_assoc, hac, mul_assoc]
    · intro a b c _ _ _ hab hac
      rw [← mul_assoc, hab, mul_assoc, hac, ← mul_assoc]
    · intro a b _ _ hab
      exact Commute.inv_left (show Commute a b from hab)
    · intro a b _ _ hab
      exact Commute.inv_right (show Commute a b from hab)
  intro g hg
  refine Subgroup.closure_induction (p := fun g _ => g ^ n = 1) hn ?_ ?_ ?_ hg
  · simp
  · intro x y hx hy hx2 hy2
    have hxy : Commute x y := hcomm x hx y hy
    rw [hxy.mul_pow, hx2, hy2, mul_one]
  · intro x _ hx2
    rw [inv_pow, hx2, inv_one]

section SqExt

variable {G : Type} [Group G]

@[expose] def t2S_sqExtN (W : Subgroup G) (u : G) (hn : ∀ w ∈ W, u * w * u⁻¹ ∈ W)
    (hn' : ∀ w ∈ W, u⁻¹ * w * u ∈ W) (hs : u * u ∈ W) : Subgroup G where
  carrier := {x | x ∈ W ∨ ∃ m ∈ W, x = m * u}
  one_mem' := Or.inl W.one_mem
  mul_mem' := by
    rintro x y (hx | ⟨m, hm, rfl⟩) (hy | ⟨m', hm', rfl⟩)
    · exact Or.inl (W.mul_mem hx hy)
    · exact Or.inr ⟨x * m', W.mul_mem hx hm', by rw [mul_assoc]⟩
    · refine Or.inr ⟨m * (u * y * u⁻¹), W.mul_mem hm (hn y hy), ?_⟩
      group
    · refine Or.inl ?_
      have : m * u * (m' * u) = (m * (u * m' * u⁻¹)) * (u * u) := by group
      rw [this]
      exact W.mul_mem (W.mul_mem hm (hn m' hm')) hs
  inv_mem' := by
    rintro x (hx | ⟨m, hm, rfl⟩)
    · exact Or.inl (W.inv_mem hx)
    · refine Or.inr ⟨(u⁻¹ * m⁻¹ * u) * (u * u)⁻¹, W.mul_mem (hn' _ (W.inv_mem hm)) (W.inv_mem hs), ?_⟩
      group

theorem t2S_mem_sup_zpowers {W : Subgroup G} {u : G} (hn : ∀ w ∈ W, u * w * u⁻¹ ∈ W)
    (hn' : ∀ w ∈ W, u⁻¹ * w * u ∈ W) (hs : u * u ∈ W) {x : G} (hx : x ∈ W ⊔ Subgroup.zpowers u) :
    x ∈ W ∨ ∃ m ∈ W, x = m * u := by
  have hle : W ⊔ Subgroup.zpowers u ≤ t2S_sqExtN W u hn hn' hs := by
    refine sup_le (fun m hm => Or.inl hm) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr ⟨1, W.one_mem, by rw [one_mul]⟩
  exact hle hx

theorem t2S_pow_of_ext {W : Subgroup G} {u : G} (hn : ∀ w ∈ W, u * w * u⁻¹ ∈ W)
    (hn' : ∀ w ∈ W, u⁻¹ * w * u ∈ W) (hs : u * u ∈ W) {n : ℕ} (hW : ∀ w ∈ W, w ^ n = 1)
    {x : G} (hx : x ∈ W ⊔ Subgroup.zpowers u) : x ^ (2 * n) = 1 := by
  rcases t2S_mem_sup_zpowers hn hn' hs hx with hx | ⟨m, hm, rfl⟩
  · rw [pow_mul', hW x hx, one_pow]
  · have h2 : (m * u) ^ 2 = (m * (u * m * u⁻¹)) * (u * u) := by rw [pow_two]; group
    have hmem : (m * u) ^ 2 ∈ W := by
      rw [h2]; exact W.mul_mem (W.mul_mem hm (hn m hm)) hs
    rw [pow_mul, hW _ hmem]

end SqExt

theorem t2S_isPGroup_closure {G : Type} [Group G] {z u w₁ w₂ : G} (hzz : z * z = 1) (hu2 : u * u = 1)
    (hw₁ : w₁ * w₁ = z) (hw₂ : w₂ * w₂ = z) (hzw₁ : z * w₁ = w₁ * z) (hzw₂ : z * w₂ = w₂ * z)
    (hw₁₂ : w₁ * w₂ = w₂ * w₁) (hzu : z * u = u * z)
    (hu₁ : u * w₁ * u⁻¹ = w₁⁻¹) (hu₂ : u * w₂ * u⁻¹ = w₂⁻¹) :
    IsPGroup 2 ↥(Subgroup.closure ({z, u, w₁, w₂} : Set G)) := by
  set W : Subgroup G := Subgroup.closure ({z, w₁, w₂} : Set G) with hWdef
  have hzW : z ∈ W := Subgroup.subset_closure (by simp)
  have hw₁W : w₁ ∈ W := Subgroup.subset_closure (by simp)
  have hw₂W : w₂ ∈ W := Subgroup.subset_closure (by simp)
  have hW4 : ∀ w ∈ W, w ^ 4 = 1 := by
    refine t2S_closure_pow (n := 4) ?_ ?_
    · intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first | rfl | assumption | exact hw₁₂.symm | exact hzw₁.symm | exact hzw₂.symm
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      have p4 : ∀ x : G, x ^ 4 = (x * x) * (x * x) := fun x => by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      have h4 : ∀ x : G, x * x = z → x ^ 4 = 1 := fun x hx => by
        rw [p4, hx, hzz]
      rcases ha with rfl | rfl | rfl
      · rw [p4, hzz, mul_one]
      · exact h4 _ hw₁
      · exact h4 _ hw₂
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hn : ∀ w ∈ W, u * w * u⁻¹ ∈ W := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · have : u * x * u⁻¹ = x := by rw [← hzu]; group
        rw [this]; exact hzW
      · rw [hu₁]; exact W.inv_mem hw₁W
      · rw [hu₂]; exact W.inv_mem hw₂W
    | one => simp
    | mul x y _ _ hx hy =>
      have e : u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) := by group
      rw [e]; exact W.mul_mem hx hy
    | inv x _ hx =>
      have e : u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ := by group
      rw [e]; exact W.inv_mem hx
  have hn' : ∀ w ∈ W, u⁻¹ * w * u ∈ W := by
    intro w hw
    rw [hu_inv]
    have := hn w hw
    rwa [hu_inv] at this
  have hs : u * u ∈ W := by rw [hu2]; exact W.one_mem
  have hA : Subgroup.closure ({z, u, w₁, w₂} : Set G) ≤ W ⊔ Subgroup.zpowers u := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left hzW
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_left hw₁W
    · exact Subgroup.mem_sup_left hw₂W
  intro g
  refine ⟨3, ?_⟩
  apply Subtype.ext
  have := t2S_pow_of_ext hn hn' hs hW4 (hA g.2)
  simpa using this

theorem t2S_exists_core' {G : Type} [Group G] [Finite G] {z : G}
    (P : Sylow 2 G) (hPz : ∀ s ∈ (P : Subgroup G), s * z = z * s) (A : Subgroup G)
    (hA : IsPGroup 2 ↥A) (hAz : ∀ a ∈ A, a * z = z * a) :
    ∃ S : Subgroup G, IsPGroup 2 ↥S ∧ ¬ 2 ∣ S.index ∧ A ≤ S ∧ ∀ s ∈ S, s * z = z * s := by
  set C : Subgroup G := centralizer ({z} : Set G) with hC
  have hmemC : ∀ g : G, g ∈ C ↔ g * z = z * g := fun g => Subgroup.mem_centralizer_singleton_iff
  have hPC : (P : Subgroup G) ≤ C := fun s hs => (hmemC s).2 (hPz s hs)
  have hA' : IsPGroup 2 ↥(A.subgroupOf C) := hA.comap_subtype
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥C).map C.subtype, Q.isPGroup'.map C.subtype, ?_, ?_, ?_⟩
  · rw [Subgroup.index_map_subtype]
    intro h
    rcases (Nat.prime_two.dvd_mul).1 h with h | h
    · exact Q.not_dvd_index h
    · exact P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hPC))
  · intro a ha
    exact ⟨⟨a, (hmemC a).2 (hAz a ha)⟩, hQ (Subgroup.mem_subgroupOf.2 ha), rfl⟩
  · rintro s ⟨c, _, rfl⟩
    exact (hmemC c.1).1 c.2

theorem exists_sylow_two_contains {G : Type} [Group G] [Finite G] {z : G}
    (hz : IsCentralInvolution z) (A : Subgroup G) (hA : IsPGroup 2 ↥A)
    (hAz : ∀ a ∈ A, a * z = z * a) :
    ∃ S : Subgroup G, IsPGroup 2 ↥S ∧ ¬ 2 ∣ S.index ∧ A ≤ S ∧ ∀ s ∈ S, s * z = z * s := by
  obtain ⟨_, P, _, hPz⟩ := hz
  exact t2S_exists_core' P hPz A hA hAz

theorem relIndex_inf_sylow_of_index_two {G : Type} [Group G] [Finite G] {K C₁ S : Subgroup G}
    (hKC : K ≤ C₁) (hidx : K.relIndex C₁ = 2) (hSC : S ≤ C₁) (hS : ¬ 2 ∣ S.index) :
    (S ⊓ K).relIndex S = 2 := by
  have hle : K.relIndex S ≤ 2 := by
    rw [← hidx]
    exact Subgroup.relIndex_le_of_le_right hSC (by rw [hidx]; norm_num)
  have hne1 : K.relIndex S ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    apply hS
    have hSK : S ≤ K := h1
    have h2 : 2 ∣ K.index := by
      rw [← Subgroup.relIndex_mul_index hKC, hidx]
      exact Dvd.intro _ rfl
    exact h2.trans (Subgroup.index_dvd_of_le hSK)
  have hne0 : K.relIndex S ≠ 0 := by
    have : (K.subgroupOf S).FiniteIndex := inferInstance
    exact this.index_ne_zero
  rw [Subgroup.inf_relIndex_left]
  omega

theorem sup_eq_of_relIndex_two {G : Type} [Group G] [Finite G] {K L M : Subgroup G} (hKL : K ≤ L) (hLM : L ≤ M)
    (h2 : K.relIndex M = 2) (hne : ¬ L ≤ K) : L = M := by
  have hmul := Subgroup.relIndex_mul_relIndex K L M hKL hLM
  have h1 : K.relIndex L ≠ 1 := by
    intro h
    exact hne (Subgroup.relIndex_eq_one.1 h)
  have h0 : K.relIndex L ≠ 0 := by
    have : (K.subgroupOf L).FiniteIndex := inferInstance
    exact this.index_ne_zero
  have hdvd : K.relIndex L ∣ 2 := by rw [← h2, ← hmul]; exact Dvd.intro _ rfl
  have h2' : K.relIndex L = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h h1
    · exact h
  have h3 : L.relIndex M = 1 := by
    rw [h2'] at hmul
    omega
  exact le_antisymm hLM (Subgroup.relIndex_eq_one.1 h3)


theorem le_oPrimeResidualOf_centralizer {G : Type} [Group G] {z : G} {S : Subgroup G}
    (hS : IsPGroup 2 ↥S) (hSz : ∀ s ∈ S, s * z = z * s) :
    S ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
  intro s hs
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hsC : s ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 (hSz s hs)
  refine Subgroup.mem_map.2 ⟨⟨s, hsC⟩, Subgroup.subset_closure ⟨k, ?_⟩, rfl⟩
  apply Subtype.ext
  simpa using congrArg Subtype.val hk

end CFSG.GH74.GLS.Stage4.Rest
