module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Setting
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23Statements

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.Quasithin.Asc94
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def Stmt5_2_10_setting_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfTypeM23 M L H B D T →
      ∃ (M2 : Subgroup G) (π : ↥M2 →* Equiv.Perm (Fin 7)), IsM23Setting T H M2 π

@[expose] def Stmt5_2_19_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ) (M2 : Subgroup G)
    (π : ↥M2 →* Equiv.Perm (Fin 7)), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfTypeM23 M L H B D T → IsM23Setting T H M2 π →
      m23Gx T M L H B D ⊓ M2 = H ∧ H = setStabIn M2 π {5, 6}

@[expose] def Stmt5_2_17_20_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ) (M2 : Subgroup G)
    (π : ↥M2 →* Equiv.Perm (Fin 7)), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfTypeM23 M L H B D T → IsM23Setting T H M2 π →
      ∃ (ι : Fin 7 → Fin 23) (ζ : ↥M2 ≃* ↥(stabilizer ↥NativeSporadic.M23 heptad₀)),
        Function.Injective ι ∧ (∀ i, ι i ∈ heptad₀) ∧ IsPermEquiv M2 π ι ζ ∧
        ∀ (t : G) (habcd : [ι 3, ι 4, ι 5, ι 6].Nodup), t ∈ m23I M2 π → IsM23Swap M2 π t →
          m23Gx T M L H B D ⊓ stabilizer G ((t : G) : G ⧸ m23Gx T M L H B D) = L ∧
          m23Gx T M L H B D ≤
            m23Gx T M L H B D ⊓ stabilizer G ((t : G) : G ⧸ m23Gx T M L H B D) ⊔
              m23I M2 π ⊓ m23Gx T M L H B D ∧
          ∃ β : ↥(m23Gx T M L H B D) ≃* stabilizer ↥NativeSporadic.M23 (xbar habcd),
            (∀ (g : ↥(m23Gx T M L H B D)) (hgM : (g : G) ∈ M2), (g : G) ∈ m23I M2 π →
              (β g : ↥NativeSporadic.M23) = (ζ ⟨g, hgM⟩ : ↥NativeSporadic.M23)) ∧
            ∀ g : ↥(m23Gx T M L H B D),
              (g : G) ∈ stabilizer G ((t : G) : G ⧸ m23Gx T M L H B D) ↔
                (β g : ↥NativeSporadic.M23) ∈ stabilizer ↥NativeSporadic.M23 (ybar habcd)

@[expose] def Stmt5_2_21_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ) (M2 : Subgroup G)
    (π : ↥M2 →* Equiv.Perm (Fin 7)), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfTypeM23 M L H B D T → IsM23Setting T H M2 π →
      M ⊔ M2 = ⊤ ∧ m23Gx T M L H B D ⊔ m23I M2 π = ⊤

@[expose] def Stmt5_2_22_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ) (M2 : Subgroup G)
    (π : ↥M2 →* Equiv.Perm (Fin 7)) (t : G), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfTypeM23 M L H B D T → IsM23Setting T H M2 π → t ∈ m23I M2 π → IsM23Swap M2 π t →
      m23I M2 π = m23I M2 π ⊓ stabilizer G ({((1 : G) : G ⧸ m23Gx T M L H B D),
          ((t : G) : G ⧸ m23Gx T M L H B D)} : Set (G ⧸ m23Gx T M L H B D)) ⊔
        m23I M2 π ⊓ m23Gx T M L H B D

@[expose] def Stmt5_2_10_aut_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ) (M2 : Subgroup G)
    (π : ↥M2 →* Equiv.Perm (Fin 7)), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfTypeM23 M L H B D T → IsM23Setting T H M2 π →
      ∀ α : ↥L ≃* ↥L, (∀ k : ↥L, (k : G) ∈ m23I M2 π → α k = k) → α = MulEquiv.refl _

section PermEquiv

variable {M2 : Subgroup G} {π : ↥M2 →* Equiv.Perm (Fin 7)} {ι : Fin 7 → Fin 23}
  {ζ : ↥M2 ≃* ↥(stabilizer ↥NativeSporadic.M23 heptad₀)}

end PermEquiv

theorem stmt5_2_11_22_of_F4
    (hset : Stmt5_2_10_setting_F4) (h520 : Stmt5_2_17_20_F4)
    (h519 : Stmt5_2_19_F4) (h521 : Stmt5_2_21_F4) (h522 : Stmt5_2_22_F4) (haut : Stmt5_2_10_aut_F4) :
    Stmt5_2_11_22_F4 := by
  intro G _ _ T M L V H B D L₂ n hyp hM23
  obtain ⟨M2, π, hS⟩ := hset G T M L V H B D L₂ n hyp hM23
  obtain ⟨ι, ζ, hinj, hιB, hζ, h520⟩ := h520 G T M L V H B D L₂ n M2 π hyp hM23 hS
  obtain ⟨hGxM2, hH⟩ := h519 G T M L V H B D L₂ n M2 π hyp hM23 hS
  have hIM2 : m23I M2 π ≤ M2 := setStabIn_le M2 π _
  have hmulπ : ∀ (g k : G) (hg : g ∈ M2) (hk : k ∈ M2),
      π ⟨g * k, M2.mul_mem hg hk⟩ = π ⟨g, hg⟩ * π ⟨k, hk⟩ := fun g k hg hk =>
    map_mul π ⟨g, hg⟩ ⟨k, hk⟩
  have hπ1 : π ⟨1, M2.one_mem⟩ = 1 := map_one π

  have memGx : ∀ (g : G) (hg : g ∈ M2), g ∈ m23Gx T M L H B D ↔
      π ⟨g, hg⟩ • ({5, 6} : Set (Fin 7)) = {5, 6} := by
    intro g hg
    have e : g ∈ m23Gx T M L H B D ⊓ M2 ↔ g ∈ setStabIn M2 π {5, 6} := by rw [hGxM2, hH]
    rw [Subgroup.mem_inf, mem_setStabIn] at e
    constructor
    · intro h
      obtain ⟨_, h'⟩ := e.mp ⟨h, hg⟩
      exact h'
    · intro h
      exact (e.mpr ⟨hg, h⟩).1
  have hcos : ∀ (g k : G) (hg : g ∈ M2) (hk : k ∈ M2),
      ((g : G ⧸ m23Gx T M L H B D) = (k : G ⧸ m23Gx T M L H B D)) ↔
        π ⟨g, hg⟩ • ({5, 6} : Set (Fin 7)) = π ⟨k, hk⟩ • ({5, 6} : Set (Fin 7)) := by
    intro g k hg hk
    rw [QuotientGroup.eq, memGx _ (M2.mul_mem (M2.inv_mem hg) hk),
      show (⟨g⁻¹ * k, M2.mul_mem (M2.inv_mem hg) hk⟩ : ↥M2) = (⟨g, hg⟩ : ↥M2)⁻¹ * ⟨k, hk⟩
        from rfl, map_mul, map_inv, mul_smul, inv_smul_eq_iff, eq_comm]

  obtain ⟨σ, hσA, hσ56, hσ45, hσσ, hσI⟩ : ∃ σ : Equiv.Perm (Fin 7),
      σ ∈ alternatingGroup (Fin 7) ∧ σ • ({5, 6} : Set (Fin 7)) = {4, 5} ∧
      σ • ({4, 5} : Set (Fin 7)) = {5, 6} ∧ σ * σ = 1 ∧
      σ • ({3, 4, 5, 6} : Set (Fin 7)) = {3, 4, 5, 6} := by
    refine ⟨Equiv.swap 0 1 * Equiv.swap 4 6, ?_, ?_, ?_, by decide, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]
      decide
    · rw [smul_pair_set_eq_iff]; decide
    · rw [smul_pair_set_eq_iff]; decide
    · ext x
      simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_insert_iff, Set.mem_singleton_iff,
        Equiv.Perm.smul_def]
      fin_cases x <;> decide
  obtain ⟨t, htM2, hπt⟩ : ∃ (t : G) (h : t ∈ M2), π ⟨t, h⟩ = σ := by
    have : σ ∈ π.range := by rw [hS.range_eq]; exact hσA
    obtain ⟨t', ht'⟩ := this
    exact ⟨t', t'.2, ht'⟩
  have htI : t ∈ m23I M2 π := mem_setStabIn.mpr ⟨htM2, by rw [hπt]; exact hσI⟩
  have hsw : IsM23Swap M2 π t := ⟨htM2, by rw [hπt]; exact hσ56, by rw [hπt]; exact hσ45⟩
  have htGx : t ∉ m23Gx T M L H B D := by
    rw [memGx t htM2, hπt, hσ56, Set.pair_eq_pair_iff]
    decide
  have htt : t * t ∈ m23Gx T M L H B D := by
    rw [memGx (t * t) (M2.mul_mem htM2 htM2), hmulπ t t htM2 htM2, hπt, hσσ, one_smul]

  have hx : ∀ (g : G) (hg : g ∈ M2), g • ((1 : G) : G ⧸ m23Gx T M L H B D) =
      ((1 : G) : G ⧸ m23Gx T M L H B D) ↔ π ⟨g, hg⟩ • ({5, 6} : Set (Fin 7)) = {5, 6} := by
    intro g hg
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hcos g 1 hg M2.one_mem, hπ1, one_smul]
  have hxy : ∀ (g : G) (hg : g ∈ M2), g • ((1 : G) : G ⧸ m23Gx T M L H B D) =
      ((t : G) : G ⧸ m23Gx T M L H B D) ↔ π ⟨g, hg⟩ • ({5, 6} : Set (Fin 7)) = {4, 5} := by
    intro g hg
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hcos g t hg htM2, hπt, hσ56]
  have hyx : ∀ (g : G) (hg : g ∈ M2), g • ((t : G) : G ⧸ m23Gx T M L H B D) =
      ((1 : G) : G ⧸ m23Gx T M L H B D) ↔ π ⟨g, hg⟩ • ({4, 5} : Set (Fin 7)) = {5, 6} := by
    intro g hg
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, hcos (g * t) 1 (M2.mul_mem hg htM2) M2.one_mem,
      hmulπ g t hg htM2, hπt, hπ1, one_smul, mul_smul, hσ56]
  have hyy : ∀ (g : G) (hg : g ∈ M2), g • ((t : G) : G ⧸ m23Gx T M L H B D) =
      ((t : G) : G ⧸ m23Gx T M L H B D) ↔ π ⟨g, hg⟩ • ({4, 5} : Set (Fin 7)) = {4, 5} := by
    intro g hg
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, hcos (g * t) t (M2.mul_mem hg htM2) htM2,
      hmulπ g t hg htM2, hπt, mul_smul, hσ56]

  have habcd : [ι 3, ι 4, ι 5, ι 6].Nodup :=
    List.Nodup.map hinj (by decide : ([3, 4, 5, 6] : List (Fin 7)).Nodup)
  obtain ⟨hL, hGx, β, hβζ, hβy⟩ := h520 t habcd htI hsw

  have hζI : ∀ m : ↥M2, (ζ m : ↥NativeSporadic.M23) ∈
      quadStab ↥NativeSporadic.M23 (ι 3) (ι 4) (ι 5) (ι 6) ↔ (m : G) ∈ m23I M2 π := by
    intro m
    have e : ({ι 3, ι 4, ι 5, ι 6} : Set (Fin 23)) = ι '' {3, 4, 5, 6} := by
      simp only [Set.image_insert_eq, Set.image_singleton]
    rw [mem_stabilizer_iff, e, hζ.smul_image_eq_iff hinj, mem_setStabIn]
    exact ⟨fun h => ⟨m.2, h⟩, fun ⟨_, h⟩ => h⟩
  have hQS : ∀ g ∈ quadStab ↥NativeSporadic.M23 (ι 3) (ι 4) (ι 5) (ι 6),
      g ∈ stabilizer ↥NativeSporadic.M23 heptad₀ := fun g hg =>
    mem_stabilizer_heptad₀_of_mem_quadStab habcd (by simp [hιB]) hg
  let ζI : ↥(m23I M2 π) ≃* ↥(quadStab ↥NativeSporadic.M23 (ι 3) (ι 4) (ι 5) (ι 6)) :=
    { toFun := fun i => ⟨ζ ⟨i, hIM2 i.2⟩, (hζI ⟨i, hIM2 i.2⟩).mpr i.2⟩
      invFun := fun g => ⟨ζ.symm ⟨g, hQS g g.2⟩,
        (hζI _).mp (by rw [MulEquiv.apply_symm_apply]; exact g.2)⟩
      left_inv := fun i => by
        apply Subtype.ext
        simp
      right_inv := fun g => by
        apply Subtype.ext
        simp
      map_mul' := fun i j => by
        apply Subtype.ext
        change ((ζ (⟨i, hIM2 i.2⟩ * ⟨j, hIM2 j.2⟩) : ↥(stabilizer _ _)) : ↥NativeSporadic.M23) =
          (ζ ⟨i, hIM2 i.2⟩ : ↥NativeSporadic.M23) * (ζ ⟨j, hIM2 j.2⟩ : ↥NativeSporadic.M23)
        rw [map_mul]
        rfl }
  have hζIv : ∀ i : ↥(m23I M2 π), (ζI i : ↥NativeSporadic.M23) =
      (ζ ⟨i, hIM2 i.2⟩ : ↥NativeSporadic.M23) := fun i => rfl

  have hI6 : m23I M2 π ≤ m23I M2 π ⊓ m23Gx T M L H B D ⊔ Subgroup.zpowers t := by
    refine (h522 G T M L V H B D L₂ n M2 π t hyp hM23 hS htI hsw).le.trans (sup_le ?_ le_sup_left)
    intro g hg
    obtain ⟨hgI, hgs⟩ := Subgroup.mem_inf.mp hg
    rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton,
      Set.pair_eq_pair_iff] at hgs
    rcases hgs with ⟨h1, -⟩ | ⟨h1, -⟩
    · have : g ∈ m23Gx T M L H B D := by
        rw [← stabilizer_mk_one (m23Gx T M L H B D)]; exact h1
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hgI, this⟩)
    · have htx : t • ((1 : G) : G ⧸ m23Gx T M L H B D) = ((t : G) : G ⧸ m23Gx T M L H B D) := by
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      have h2 : t⁻¹ * g ∈ m23Gx T M L H B D := by
        rw [← stabilizer_mk_one (m23Gx T M L H B D), mem_stabilizer_iff, mul_smul, h1, ← htx,
          inv_smul_smul]
      have h3 : t⁻¹ * g ∈ m23I M2 π ⊓ m23Gx T M L H B D :=
        Subgroup.mem_inf.mpr ⟨(m23I M2 π).mul_mem ((m23I M2 π).inv_mem htI) hgI, h2⟩
      have := (m23I M2 π ⊓ m23Gx T M L H B D ⊔ Subgroup.zpowers t).mul_mem
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) (Subgroup.mem_sup_left h3)
      rwa [mul_inv_cancel_left] at this
  refine ⟨m23Gx T M L H B D, m23I M2 π, t, ι 3, ι 4, ι 5, ι 6, habcd, β, ζI, htI, htGx, htt,
    (h521 G T M L V H B D L₂ n M2 π hyp hM23 hS).2, hGx, hI6, ?_, ?_, hβy, ?_, ?_⟩
  ·
    intro i
    rw [memGx _ (hIM2 i.2), hζIv, mem_stabilizer_iff, xbar, hζ.smul_pair_eq_iff hinj]
  ·
    intro i hi
    rw [hζIv]
    exact hβζ ⟨i, hi⟩ (hIM2 i.2) i.2
  ·
    intro i
    have hi := hIM2 i.2
    rw [hζIv, mem_stabilizer_iff, mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton,
      Set.smul_set_insert, Set.smul_set_singleton, Set.pair_eq_pair_iff, Set.pair_eq_pair_iff,
      hx _ hi, hyy _ hi, hxy _ hi, hyx _ hi, xbar, ybar]
    simp only [hζ.smul_pair_eq_iff hinj]
  ·
    rw [hL]
    exact haut G T M L V H B D L₂ n M2 π hyp hM23 hS

end CFSG.Quasithin.H13
