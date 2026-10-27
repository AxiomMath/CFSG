module

public import CFSG.CGT.PushingUpLit.SOLT.PermVec

public section

namespace CFSG.CGT.PushingUpLit.SOLT

open CFSG.RankThree.PartOne

structure NatBlock (L : Type) [Group L] (n : ℕ) where
  φ : (L ⧸ CFSG.pCore 2 L) ≃* alternatingGroup (Fin (2 * n + 1))
  ψ : ↥(shortU L) →* Multiplicative (Fin (2 * n + 1) → ZMod 2)
  sum_zero : ∀ u, ∑ i, Multiplicative.toAdd (ψ u) i = 0
  surj : ∀ v : Fin (2 * n + 1) → ZMod 2, ∑ i, v i = 0 → ∃ u, ψ u = Multiplicative.ofAdd v
  ker_eq : ψ.ker = (shortC L).subgroupOf (shortU L)
  equiv : ∀ (l u : L) (hu : u ∈ shortU L) (hu' : l * u * l⁻¹ ∈ shortU L),
    ψ ⟨l * u * l⁻¹, hu'⟩ = Multiplicative.ofAdd (permActionTwo
      ((φ (l : L ⧸ CFSG.pCore 2 L) : alternatingGroup (Fin (2 * n + 1))) : Equiv.Perm _)
      (Multiplicative.toAdd (ψ ⟨u, hu⟩)))

theorem natBlock_of_isNaturalAltModule {L : Type} [Group L] {n : ℕ} (h : IsNaturalAltModule L n) :
    Nonempty (NatBlock L n) := by
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := h
  exact ⟨⟨φ, ψ, h1, h2, h3, h4⟩⟩

theorem exists_two_moved {n : ℕ} (hn : 2 ≤ n) :
    ∃ σ ∈ alternatingGroup (Fin (2 * n + 1)),
      σ ⟨0, by omega⟩ = ⟨2, by omega⟩ ∧ σ ⟨1, by omega⟩ = ⟨3, by omega⟩ :=
  exists_perm_two (by omega) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])

namespace NatBlock

variable {L : Type} [Group L] {n : ℕ}

theorem shortU_normal : (shortU L).Normal := by
  unfold shortU
  infer_instance

theorem shortU_le_pCore : shortU L ≤ CFSG.pCore 2 L := by
  unfold shortU
  exact Subgroup.commutator_le_left _ _

def conj (l : L) (u : ↥(shortU L)) : ↥(shortU L) :=
  ⟨l * u * l⁻¹, (shortU_normal (L := L)).conj_mem u u.2 l⟩

variable (B : NatBlock L n)

include B

def perm (l : L) : Equiv.Perm (Fin (2 * n + 1)) :=
  ((B.φ (l : L ⧸ CFSG.pCore 2 L) : alternatingGroup (Fin (2 * n + 1))) : Equiv.Perm _)

theorem exists_perm {σ : Equiv.Perm (Fin (2 * n + 1))}
    (hσ : σ ∈ alternatingGroup (Fin (2 * n + 1))) : ∃ l : L, B.perm l = σ := by
  obtain ⟨q, hq⟩ := B.φ.surjective ⟨σ, hσ⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨l, by simpa [perm] using congrArg Subtype.val hq⟩

theorem psi_conj (l : L) (u : ↥(shortU L)) :
    B.ψ (conj l u) =
      Multiplicative.ofAdd (permActionTwo (B.perm l) (Multiplicative.toAdd (B.ψ u))) :=
  B.equiv l u u.2 _

theorem exists_unitVec_add (a b : Fin (2 * n + 1)) :
    ∃ u : ↥(shortU L), B.ψ u = Multiplicative.ofAdd (unitVec a + unitVec b) :=
  B.surj _ (sum_unitVec_add a b)

theorem exists_one_add_unitVec (a : Fin (2 * n + 1)) :
    ∃ u : ↥(shortU L),
      B.ψ u = Multiplicative.ofAdd ((fun _ => (1 : ZMod 2)) + unitVec a) :=
  B.surj _ (sum_one_add_unitVec n a)

theorem exists_noncomm (hn : 2 ≤ n) : ∃ (l : L) (u : ↥(shortU L)), conj l u ≠ u := by
  obtain ⟨u, hu⟩ := B.exists_unitVec_add ⟨0, by omega⟩ ⟨1, by omega⟩
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := exists_two_moved hn
  obtain ⟨l, hl⟩ := B.exists_perm hσ
  refine ⟨l, u, fun h => ?_⟩
  have h1 := B.psi_conj l u
  rw [h, hu, hl] at h1
  simp only [toAdd_ofAdd, permActionTwo_add, permActionTwo_unitVec, hσ0, hσ1] at h1
  have h2 := congrFun (Multiplicative.ofAdd.injective h1) ⟨0, by omega⟩
  simp [unitVec, Fin.ext_iff] at h2

end NatBlock

section Main

variable {G : Type} [Group G]

theorem exists_noncomm_of_natBlock {X : Subgroup G} {n : ℕ} (B : NatBlock ↥X n) (hn : 2 ≤ n) :
    ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨l, u, hlu⟩ := B.exists_noncomm hn
  refine ⟨(l : G), ((u : ↥X) : G), fun h => hlu ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  show (l : G) * ((u : ↥X) : G) * (l : G)⁻¹ = ((u : ↥X) : G)
  rw [h]
  group

theorem card_gt_of_natBlock [Finite G] {Q X : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (B : NatBlock ↥X n) (hQ : ∀ u : ↥(shortU ↥X), ((u : ↥X) : G) ∈ Q) :
    2 * n + 1 < Nat.card Q := by
  classical
  have h0 : 0 < 2 * n + 1 := by omega
  have h1 : 1 < 2 * n + 1 := by omega
  obtain ⟨u₁, hu₁⟩ := B.exists_unitVec_add ⟨0, h0⟩ ⟨1, h1⟩
  set V₁ : Set (Fin (2 * n + 1) → ZMod 2) := {w | ∃ σ ∈ alternatingGroup (Fin (2 * n + 1)),
    w = permActionTwo σ (unitVec (⟨0, h0⟩ : Fin (2 * n + 1)) + unitVec ⟨1, h1⟩)} with hV₁
  have hcard : 2 * n + 1 < V₁.ncard := card_orbit_two (m := 2 * n + 1) (by omega)
    (a := ⟨0, h0⟩) (b := ⟨1, h1⟩) (by simp [Fin.ext_iff])
  have hz : ∀ w ∈ V₁, ∃ z : ↥(shortU ↥X), B.ψ z = Multiplicative.ofAdd w := by
    rintro w ⟨σ, hσ, rfl⟩
    obtain ⟨l, hl⟩ := B.exists_perm hσ
    refine ⟨NatBlock.conj l u₁, ?_⟩
    rw [B.psi_conj, hu₁, hl, toAdd_ofAdd]
  choose! zf hzf using hz
  have hinj : Set.InjOn (fun w => (((zf w : ↥(shortU ↥X)) : ↥X) : G)) V₁ := by
    intro w hw w' hw' h
    have h1 : zf w = zf w' := Subtype.ext (Subtype.ext h)
    have h2 := congrArg B.ψ h1
    rw [hzf w hw, hzf w' hw'] at h2
    exact Multiplicative.ofAdd.injective h2
  have hle : V₁.ncard ≤ (Q : Set G).ncard :=
    Set.ncard_le_ncard_of_injOn (fun w => (((zf w : ↥(shortU ↥X)) : ↥X) : G))
      (fun w hw => hQ (zf w)) hinj (Set.toFinite _)
  have : (Q : Set G).ncard = Nat.card Q := (Nat.card_coe_set_eq (Q : Set G)).symm
  omega

theorem shortU_subset_of_pCore_le {X Q : Subgroup G}
    (hQ : (CFSG.pCore 2 ↥X).map X.subtype ≤ Q) (u : ↥(shortU ↥X)) : ((u : ↥X) : G) ∈ Q :=
  hQ ⟨(u : ↥X), NatBlock.shortU_le_pCore u.2, rfl⟩

theorem false_of_transitive_block [Finite G] {Q N X : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (htrans : ∀ x ∈ Q, x ≠ 1 → ∀ y ∈ Q, y ≠ 1 → ∃ g ∈ N, g * x * g⁻¹ = y)
    (hXN : ∀ g ∈ N, ∀ x ∈ X, g * x * g⁻¹ ∈ X)
    (hQ : (CFSG.pCore 2 ↥X).map X.subtype ≤ Q) (hnat : IsNaturalAltModule ↥X n) : False := by
  classical
  obtain ⟨B⟩ := natBlock_of_isNaturalAltModule hnat
  have h0 : 0 < 2 * n + 1 := by omega
  have h1 : 1 < 2 * n + 1 := by omega
  have hUQ : ∀ u : ↥(shortU ↥X), ((u : ↥X) : G) ∈ Q := shortU_subset_of_pCore_le hQ
  have hC : ∀ c ∈ shortC ↥X, c = 1 := by
    intro c hc
    by_contra hc1
    have hcQ : ((c : ↥X) : G) ∈ Q := hUQ ⟨c, hc.1⟩
    have hc1' : ((c : ↥X) : G) ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hcen : ∀ q ∈ Q, ∀ x ∈ X, q * x = x * q := by
      intro q hq x hx
      by_cases hq1 : q = 1
      · subst hq1
        simp
      obtain ⟨g, hg, hgq⟩ := htrans _ hcQ hc1' q hq hq1
      have hx0 : g⁻¹ * x * g ∈ X := by simpa using hXN g⁻¹ (N.inv_mem hg) x hx
      have hcc : ((c : ↥X) : G) * (g⁻¹ * x * g) = (g⁻¹ * x * g) * ((c : ↥X) : G) :=
        (congrArg (fun z : ↥X => (z : G))
          (Subgroup.mem_center_iff.1 hc.2 ⟨g⁻¹ * x * g, hx0⟩)).symm
      have e1 : q * x = g * (((c : ↥X) : G) * (g⁻¹ * x * g)) * g⁻¹ := by
        rw [← hgq]
        group
      have e2 : x * q = g * ((g⁻¹ * x * g) * ((c : ↥X) : G)) * g⁻¹ := by
        rw [← hgq]
        group
      rw [e1, e2, hcc]
    obtain ⟨l, u, hlu⟩ := B.exists_noncomm hn
    apply hlu
    have h := hcen _ (hUQ u) (l : G) l.2
    apply Subtype.ext
    apply Subtype.ext
    show (l : G) * ((u : ↥X) : G) * (l : G)⁻¹ = ((u : ↥X) : G)
    rw [← h]
    group
  have hψinj : ∀ u u' : ↥(shortU ↥X), B.ψ u = B.ψ u' → u = u' := by
    intro u u' h
    have hk : u⁻¹ * u' ∈ B.ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h]
      exact inv_mul_cancel _
    rw [B.ker_eq] at hk
    have hc : (((u⁻¹ * u' : ↥(shortU ↥X)) : ↥X)) ∈ shortC ↥X := Subgroup.mem_subgroupOf.1 hk
    exact inv_mul_eq_one.1 (Subtype.ext (hC _ hc))
  obtain ⟨u₁, hu₁⟩ := B.exists_unitVec_add ⟨0, h0⟩ ⟨1, h1⟩
  obtain ⟨u₂, hu₂⟩ := B.exists_one_add_unitVec ⟨0, h0⟩
  have hq₁1 : ((u₁ : ↥X) : G) ≠ 1 := by
    intro h
    have hu : u₁ = 1 := Subtype.ext (Subtype.ext h)
    have h' : B.ψ u₁ = 1 := by rw [hu, map_one]
    rw [hu₁, ← ofAdd_zero] at h'
    have := congrFun (Multiplicative.ofAdd.injective h') ⟨0, h0⟩
    simp [unitVec, Fin.ext_iff] at this
  have hq₂1 : ((u₂ : ↥X) : G) ≠ 1 := by
    intro h
    have hu : u₂ = 1 := Subtype.ext (Subtype.ext h)
    have h' : B.ψ u₂ = 1 := by rw [hu, map_one]
    rw [hu₂, ← ofAdd_zero] at h'
    have := congrFun (Multiplicative.ofAdd.injective h') ⟨1, h1⟩
    simp [unitVec, Fin.ext_iff] at this
  obtain ⟨g, hg, hgq⟩ := htrans _ (hUQ u₁) hq₁1 _ (hUQ u₂) hq₂1
  set V₁ : Set (Fin (2 * n + 1) → ZMod 2) := {w | ∃ σ ∈ alternatingGroup (Fin (2 * n + 1)),
    w = permActionTwo σ (unitVec (⟨0, h0⟩ : Fin (2 * n + 1)) + unitVec ⟨1, h1⟩)} with hV₁
  have hcard : 2 * n + 1 < V₁.ncard := card_orbit_two (m := 2 * n + 1) (by omega)
    (a := ⟨0, h0⟩) (b := ⟨1, h1⟩) (by simp [Fin.ext_iff])
  have claim : ∀ w ∈ V₁, ∃ (z z' : ↥(shortU ↥X)) (k : Fin (2 * n + 1)),
      B.ψ z = Multiplicative.ofAdd w ∧
      B.ψ z' = Multiplicative.ofAdd ((fun _ => (1 : ZMod 2)) + unitVec k) ∧
      g * ((z : ↥X) : G) * g⁻¹ = ((z' : ↥X) : G) := by
    rintro w ⟨σ, hσ, rfl⟩
    obtain ⟨l, hl⟩ := B.exists_perm hσ
    let l' : ↥X := ⟨g * (l : G) * g⁻¹, hXN g hg l l.2⟩
    refine ⟨NatBlock.conj l u₁, NatBlock.conj l' u₂, B.perm l' ⟨0, h0⟩, ?_, ?_, ?_⟩
    · rw [B.psi_conj, hu₁, hl, toAdd_ofAdd]
    · rw [B.psi_conj, hu₂, toAdd_ofAdd, permActionTwo_one_add]
    · show g * ((l : G) * ((u₁ : ↥X) : G) * (l : G)⁻¹) * g⁻¹ =
        (l' : G) * ((u₂ : ↥X) : G) * (l' : G)⁻¹
      have : (l' : G) = g * (l : G) * g⁻¹ := rfl
      rw [this, ← hgq]
      group
  choose! zf zf' kf hzf hzf' hgz using claim
  have hinj : Set.InjOn kf V₁ := by
    intro w hw w' hw' h
    have h1 : zf' w = zf' w' := by
      apply hψinj
      rw [hzf' w hw, hzf' w' hw', h]
    have h2 : g * ((zf w : ↥X) : G) * g⁻¹ = g * ((zf w' : ↥X) : G) * g⁻¹ := by
      rw [hgz w hw, hgz w' hw', h1]
    have h3 : ((zf w : ↥X) : G) = ((zf w' : ↥X) : G) := mul_left_cancel (mul_right_cancel h2)
    have h4 : zf w = zf w' := Subtype.ext (Subtype.ext h3)
    have h5 := congrArg B.ψ h4
    rw [hzf w hw, hzf w' hw'] at h5
    exact Multiplicative.ofAdd.injective h5
  have hle : V₁.ncard ≤ (Set.univ : Set (Fin (2 * n + 1))).ncard :=
    Set.ncard_le_ncard_of_injOn kf (fun w _ => Set.mem_univ _) hinj (Set.toFinite _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  omega

end Main

end CFSG.CGT.PushingUpLit.SOLT
