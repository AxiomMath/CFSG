module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.LocalAnalysis.ComponentInitial

section Central

variable {L : Type} [Group L] [Finite L]

theorem commute_of_commutator_mem_center (hZ : IsPGroup 2 (Subgroup.center L)) (P : Sylow 2 L)
    {x : L} (hx : x ∈ Subgroup.centralizer ((P : Subgroup L) : Set L)) {g : L}
    (hg : g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center L) : g * x = x * g := by
  have hcen : ∀ c ∈ Subgroup.center L, ∀ g : L, g * c * g⁻¹ = c := fun c hc g => by
    rw [Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_right]
  let D : Subgroup L :=
    { carrier := {g | g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center L}
      mul_mem' := by
        intro g₁ g₂ h₁ h₂
        have e : g₁ * g₂ * x * (g₁ * g₂)⁻¹ * x⁻¹ =
            (g₁ * (g₂ * x * g₂⁻¹ * x⁻¹) * g₁⁻¹) * (g₁ * x * g₁⁻¹ * x⁻¹) := by group
        show g₁ * g₂ * x * (g₁ * g₂)⁻¹ * x⁻¹ ∈ Subgroup.center L
        rw [e, hcen _ h₂ g₁]
        exact Subgroup.mul_mem _ h₂ h₁
      one_mem' := by
        show (1 : L) * x * 1⁻¹ * x⁻¹ ∈ Subgroup.center L
        simp
      inv_mem' := by
        intro g h
        have e : g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ = g⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * g := by group
        show g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ ∈ Subgroup.center L
        rw [e]
        have h1 : g⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * g = (g * x * g⁻¹ * x⁻¹)⁻¹ := by
          have := hcen _ (Subgroup.inv_mem _ h) g⁻¹
          simpa using this
        rw [h1]
        exact Subgroup.inv_mem _ h }
  have hmemD : ∀ g : L, g ∈ D ↔ g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center L := fun g => Iff.rfl
  let φ : D →* Subgroup.center L :=
    { toFun := fun g => ⟨g * x * g⁻¹ * x⁻¹, g.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro g₁ g₂
        apply Subtype.ext
        show (g₁ : L) * g₂ * x * ((g₁ : L) * g₂)⁻¹ * x⁻¹ =
          ((g₁ : L) * x * (g₁ : L)⁻¹ * x⁻¹) * ((g₂ : L) * x * (g₂ : L)⁻¹ * x⁻¹)
        have e : (g₁ : L) * g₂ * x * ((g₁ : L) * g₂)⁻¹ * x⁻¹ =
            ((g₁ : L) * ((g₂ : L) * x * (g₂ : L)⁻¹ * x⁻¹) * (g₁ : L)⁻¹) *
              ((g₁ : L) * x * (g₁ : L)⁻¹ * x⁻¹) := by group
        rw [e, hcen _ g₂.2 g₁]
        exact Subgroup.mem_center_iff.mp ((hmemD _).mp g₁.2) _ }
  have hcommP : ∀ p ∈ (P : Subgroup L), p * x * p⁻¹ * x⁻¹ = 1 := fun p hp => by
    rw [(Subgroup.mem_centralizer_iff.mp hx) p hp, mul_assoc x p, mul_inv_cancel, mul_one,
      mul_inv_cancel]
  have hPD : (P : Subgroup L) ≤ D := fun p hp => by
    rw [hmemD, hcommP p hp]
    exact Subgroup.one_mem _
  have hker : (P : Subgroup L).subgroupOf D ≤ φ.ker := by
    intro p hp
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact hcommP p (Subgroup.mem_subgroupOf.mp hp)
  have h2 : IsPGroup 2 φ.range := hZ.to_subgroup φ.range
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  have hidx : φ.ker.index = 2 ^ n := by rw [Subgroup.index_ker, hn]
  have hodd : φ.ker.index ∣ (P : Subgroup L).index :=
    (Subgroup.index_dvd_of_le hker).trans (Subgroup.relIndex_dvd_index_of_le hPD)
  have hn0 : n = 0 := by
    by_contra hne
    exact P.not_dvd_index ((dvd_pow_self 2 hne).trans (hidx ▸ hodd))
  have hker1 : φ.ker.index = 1 := by rw [hidx, hn0, pow_zero]
  have hktop : φ.ker = ⊤ := Subgroup.index_eq_one.mp hker1
  have hφ : φ ⟨g, hg⟩ = 1 := by
    have : (⟨g, hg⟩ : D) ∈ φ.ker := by rw [hktop]; exact Subgroup.mem_top _
    exact MonoidHom.mem_ker.mp this
  have h3 : g * x * g⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hφ
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3

end Central

section Structure

variable {P : Type*} [Group P] [Finite P] [Group.IsPerfect P]

theorem alt_cover_structure {m : ℕ} (hm : 3 ≤ m) (η : P →* alternatingGroup (Fin (m + 2)))
    (hη : Function.Surjective η) (hK : η.ker ≤ Subgroup.center P) (hK2 : IsPGroup 2 η.ker)
    (hne : η.ker ≠ ⊥) :
    ∃ (x : Fin m → P) (z : P), (∀ i, η (x i) = altThreeCycle i) ∧ (∀ i, x i ^ 3 = 1) ∧
      z ∈ Subgroup.center P ∧ z ≠ 1 ∧ z * z = 1 ∧ ∀ i j, i ≠ j → (x i * x j) ^ 2 = z := by
  classical
  have hlift : ∀ i : Fin m, ∃ x : P, η x = altThreeCycle i ∧ x ^ 3 = 1 := fun i => by
    obtain ⟨y, hy⟩ := hη (altThreeCycle i)
    obtain ⟨x, hx, hx3⟩ := exists_lift_pow_three_eq_one hK hK2
      (by rw [hy]; exact altThreeCycle_pow_three i)
    exact ⟨x, hx.trans hy, hx3⟩
  choose x hxη hx3 using hlift
  have hL : Subgroup.closure (Set.range x) = ⊤ := by
    have hmap : (Subgroup.closure (Set.range x)).map η = ⊤ := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      have : η ∘ x = altThreeCycle := funext hxη
      rw [this, closure_altThreeCycle]
    have hsup : Subgroup.closure (Set.range x) ⊔ η.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
    have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central
      (Subgroup.closure (Set.range x)) η.ker hK
    rw [hsup, ← commutator_def, Group.IsPerfect.commutator_eq_top] at h
    exact eq_top_iff.mpr (h.le.trans (Subgroup.commutator_le_self _))
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  set z := (x i₀ * x i₁) ^ 2 with hzdef
  have hzc : z ∈ Subgroup.center P := hK (by
    rw [MonoidHom.mem_ker, map_pow, map_mul, hxη, hxη, altThreeCycle_mul_sq h01])
  have hz2 : z ^ 2 = 1 := sq_sq_lift_eq_one η hK hK2 h01 (hxη i₀) (hxη i₁) (hx3 i₀) (hx3 i₁)
  have hzij : ∀ i j, i ≠ j → (x i * x j) ^ 2 = z := fun i j hij =>
    lift_sq_eq η hη hK hK2 hxη hx3 hij h01
  refine ⟨x, z, hxη, hx3, hzc, ?_, by rw [← pow_two]; exact hz2, hzij⟩
  intro hz1
  have hcard := card_closure_le_of_carmichael m x hx3
    (fun i j hij => by rw [hzij i j hij, hz1])
  rw [hL, Subgroup.card_top] at hcard
  have hP2 : Nat.card P = Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card η.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup η.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv]
  have hA : Nat.card (alternatingGroup (Fin (m + 2))) = (m + 2).factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hApos : 0 < (m + 2).factorial / 2 := by
    rw [← hA]
    exact Nat.card_pos
  have hle : (m + 2).factorial / 2 * Nat.card η.ker ≤ (m + 2).factorial / 2 * 1 := by
    calc (m + 2).factorial / 2 * Nat.card η.ker = Nat.card P := by rw [hP2, hA]
      _ ≤ (m + 2).factorial / 2 := hcard
      _ = (m + 2).factorial / 2 * 1 := (mul_one _).symm
  have hk1 : Nat.card η.ker ≤ 1 := Nat.le_of_mul_le_mul_left hle hApos
  exact hne (Subgroup.eq_bot_of_card_eq _ (le_antisymm hk1 Nat.card_pos))

end Structure

section Block

variable {G : Type*} [Group G]

theorem block_comm {t s z : G} (hz : ∀ g, g * z = z * g) (hz2 : z * z = 1) (ht : t ^ 3 = 1)
    (hs : s ^ 3 = 1) (hts : (t * s) ^ 2 = z) (hst : (s * t) ^ 2 = z) :
    t * s * (t * s⁻¹ * t) = z * (t * s⁻¹ * t * (t * s)) := by
  have hzi : ∀ g, g * z⁻¹ = z⁻¹ * g := fun g => by
    calc g * z⁻¹ = z⁻¹ * (z * g) * z⁻¹ := by group
      _ = z⁻¹ * (g * z) * z⁻¹ := by rw [hz g]
      _ = z⁻¹ * g := by group
  have h3t : t * t * t = 1 := by
    have := ht
    rwa [pow_three'] at this
  have h3s : s * s * s = 1 := by
    have := hs
    rwa [pow_three'] at this
  have ht' : t * t = t⁻¹ := eq_inv_of_mul_eq_one_left h3t
  have hs' : s * s = s⁻¹ := eq_inv_of_mul_eq_one_left h3s
  have hs'' : s⁻¹ * s⁻¹ = s := by
    calc s⁻¹ * s⁻¹ = s⁻¹ * s⁻¹ * (s * s * s) := by rw [h3s, mul_one]
      _ = s := by group
  have hts' : t * s * (t * s) = z := by rw [← pow_two]; exact hts
  have hst' : s * t * (s * t) = z := by rw [← pow_two]; exact hst
  have hinv_ts : (t * s)⁻¹ = t * s * z⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc t * s * (t * s * z⁻¹) = (t * s * (t * s)) * z⁻¹ := by group
      _ = 1 := by rw [hts', mul_inv_cancel]
  have hinv_st : (s * t)⁻¹ = s * t * z⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc s * t * (s * t * z⁻¹) = (s * t * (s * t)) * z⁻¹ := by group
      _ = 1 := by rw [hst', mul_inv_cancel]
  have hzz : z⁻¹ * z⁻¹ = 1 := by
    rw [← mul_inv_rev, hz2, inv_one]
  have h1 : t * s * t = s⁻¹ * z := by
    calc t * s * t = s⁻¹ * (s * t * (s * t)) := by group
      _ = s⁻¹ * z := by rw [hst']
  have hL : t * s * (t * s⁻¹ * t) = z * (s * t) := by
    calc t * s * (t * s⁻¹ * t) = (t * s * t) * s⁻¹ * t := by group
      _ = s⁻¹ * z * s⁻¹ * t := by rw [h1]
      _ = z * s⁻¹ * s⁻¹ * t := by rw [hz s⁻¹]
      _ = z * (s⁻¹ * s⁻¹) * t := by group
      _ = z * (s * t) := by rw [hs'', mul_assoc]
  have hR : t * s⁻¹ * t * (t * s) = s * t := by
    calc t * s⁻¹ * t * (t * s) = t * s⁻¹ * (t * t) * s := by group
      _ = t * (t * s)⁻¹ * s := by rw [ht']; group
      _ = t * (t * s * z⁻¹) * s := by rw [hinv_ts]
      _ = t * (z⁻¹ * (t * s)) * s := by rw [hzi (t * s)]
      _ = (t * z⁻¹) * (t * s) * s := by group
      _ = (z⁻¹ * t) * (t * s) * s := by rw [hzi t]
      _ = z⁻¹ * ((t * t) * (s * s)) := by group
      _ = z⁻¹ * (t⁻¹ * s⁻¹) := by rw [ht', hs']
      _ = z⁻¹ * (s * t)⁻¹ := by rw [mul_inv_rev]
      _ = z⁻¹ * (s * t * z⁻¹) := by rw [hinv_st]
      _ = z⁻¹ * (z⁻¹ * (s * t)) := by rw [hzi (s * t)]
      _ = (z⁻¹ * z⁻¹) * (s * t) := by group
      _ = s * t := by rw [hzz, one_mul]
  rw [hR, hL]

end Block

end CFSG.QuasithinUnique.Ch1
