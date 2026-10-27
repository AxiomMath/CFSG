module

public import CFSG.LieType.Universal.Unitary.BinaryModel.Weight
public import CFSG.LieType.Universal.Unitary.CurtisDatum.TorusSums
public import CFSG.Quasithin.Background.SmithCurtisMain

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Quasithin.SmithCurtis

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]

instance isFullNode_decidablePred {n : ℕ} (ε : Fin f → Finset (Fin n)) :
    DecidablePred (IsFullNode ε) :=
  fun s => by unfold IsFullNode; infer_instance

@[expose] def muEps {k : Type} [Field k] {n : ℕ} (ε : Fin f → Finset (Fin n))
    (s : Fin (n / 2)) : k :=
  if IsFullNode ε s then -1 else 0

section Generic

variable {G : Type*} [Group G] [Finite G] {B : Type*} {M : CoxeterMatrix B} {W : Type*}
  [Group W] {cs : CoxeterSystem M W} {p : ℕ} (D : CurtisDatum G cs p)
  {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} {y : V} {μ : B → k}

theorem isCurtisType_congr_chi {χ χ' : G → k} (hχ : ∀ h ∈ D.H, χ h = χ' h) :
    D.IsCurtisType ρ y χ μ ↔ D.IsCurtisType ρ y χ' μ := by
  simp only [CurtisDatum.IsCurtisType]
  constructor
  · rintro ⟨hy, hy0, hH, hT⟩
    exact ⟨hy, hy0, fun h hh => by rw [← hχ h hh]; exact hH h hh, hT⟩
  · rintro ⟨hy, hy0, hH, hT⟩
    exact ⟨hy, hy0, fun h hh => by rw [hχ h hh]; exact hH h hh, hT⟩

end Generic

theorem bExp_erase_zero {n : ℕ} (hn : 0 < n) (ε : Fin f → Finset (Fin n)) (a : Fin n) :
    bExp (fun r => (ε r).erase ⟨0, hn⟩) a = bExp ε a := by
  simp only [bExp]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hfilter : ((ε r).erase ⟨0, hn⟩).filter (fun j => a < j) =
      (ε r).filter (fun j => a < j) := by
    rw [Finset.filter_erase, Finset.erase_eq_self]
    simp only [Finset.mem_filter, not_and]
    intro _
    exact not_lt.mpr (by
      rw [Fin.le_iff_val_le_val]
      exact Nat.zero_le _)
  rw [hfilter]

theorem chiEps_erase_zero {k : Type} [Field k] (φ₀ : F →+* k) {n : ℕ} (hn : 0 < n)
    (ε : Fin f → Finset (Fin n)) :
    chiEps φ₀ (fun r => (ε r).erase ⟨0, hn⟩) = chiEps φ₀ ε := by
  funext g
  simp only [chiEps]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [bExp_erase_zero hn]

theorem isFullNode_erase_zero_iff {n : ℕ} (hn : 0 < n) (ε : Fin f → Finset (Fin n))
    (s : Fin (n / 2)) :
    IsFullNode (fun r => (ε r).erase ⟨0, hn⟩) s ↔ IsFullNode ε s := by
  have hp : (⟨(s : ℕ) + 1, by omega⟩ : Fin n) ≠ ⟨0, hn⟩ := by
    intro h
    have hval : (s : ℕ) + 1 = 0 := by
      simpa only [Fin.val_mk] using congrArg Fin.val h
    omega
  have hq : (⟨n - 1 - (s : ℕ), by omega⟩ : Fin n) ≠ ⟨0, hn⟩ := by
    intro h
    have hval : n - 1 - (s : ℕ) = 0 := by
      simpa only [Fin.val_mk] using congrArg Fin.val h
    omega
  unfold IsFullNode
  simp only [Finset.mem_erase]
  constructor
  · rintro h r
    exact ⟨(h r).1.2, (h r).2.2⟩
  · intro h r
    exact ⟨⟨hp, (h r).1⟩, ⟨hq, (h r).2⟩⟩

theorem exists_eps_of_isCurtisType (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0) {k : Type} [Field k]
    [CharP k 2] (φ₀ : F →+* k) {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (SU (unitaryInvolution F 2 f) n) V} {y : V}
    {χ : SU (unitaryInvolution F 2 f) n → k} {μ : Fin (n / 2) → k}
    (ht : (curtisDatum hF n hn ζ hζ).IsCurtisType ρ y χ μ) :
    ∃ ε : Fin f → Finset (Fin n), (∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r) ∧
      (∀ h ∈ (curtisDatum hF n hn ζ hζ).H, χ h = chiEps φ₀ ε h) ∧ μ = muEps ε := by
  classical
  let D := curtisDatum hF n hn ζ hζ
  have hH : D.H = ⨆ s, levelTorus (unitaryInvolution F 2 f) (n := n) s := by
    show (curtisDatum hF n hn ζ hζ).H = _
    unfold curtisDatum
    rfl
  have hχmul : ∀ a ∈ D.H, ∀ b ∈ D.H, χ (a * b) = χ a * χ b :=
    fun a ha b hb => ht.chi_mul ha hb
  have hχmul' : ∀ a ∈ ⨆ s, levelTorus (unitaryInvolution F 2 f) (n := n) s,
      ∀ b ∈ ⨆ s, levelTorus (unitaryInvolution F 2 f) (n := n) s,
        χ (a * b) = χ a * χ b := by
    rw [← hH]
    exact hχmul
  let full : Fin (n / 2) → Prop := fun s => μ s = -1
  have hfull : ∀ s, full s → ∀ t ∈ levelTorus (unitaryInvolution F 2 f) s, χ t = 1 := by
    intro s hs t htmem
    by_contra hne
    have htH : t ∈ D.H := by
      rw [hH]
      exact Subgroup.mem_iSup_of_mem s htmem
    have hzero := curtisDatum_dScalar_eq_zero hF n hn ζ hζ χ hχmul s ⟨t, htmem, hne⟩
    have hneg : (-1 : k) ≠ 0 := by simp
    rcases ht.mu_eq s with h0 | hd
    · exact hneg (by rw [← hs, h0])
    · exact hneg (by rw [← hs, hd, hzero.2])
  obtain ⟨ε, hχε, hfullnode⟩ := exists_eps_eq_chi hF φ₀ χ ht.chi_one hχmul' full hfull
  let ε' : Fin f → Finset (Fin n) := fun r => (ε r).erase ⟨0, by omega⟩
  have hnode : ∀ s, IsFullNode ε' s ↔ μ s = -1 := by
    intro s
    exact (isFullNode_erase_zero_iff (by omega) ε s).trans (hfullnode s)
  refine ⟨ε', ?_, ?_, ?_⟩
  · intro r h
    exact (Finset.mem_erase.mp h).1 rfl
  · intro h hh
    have hh' : h ∈ ⨆ s, levelTorus (unitaryInvolution F 2 f) (n := n) s := by
      rwa [hH] at hh
    rw [hχε h hh']
    exact (congrFun (chiEps_erase_zero φ₀ (by omega : 0 < n) ε) h).symm
  · funext s
    by_cases hfs : IsFullNode ε' s
    · have hmu : μ s = -1 := (hnode s).mp hfs
      rw [muEps, if_pos hfs, hmu]
    · have hmu : μ s ≠ -1 := fun h => hfs ((hnode s).mpr h)
      rw [muEps, if_neg hfs]
      rcases ht.mu_eq s with h0 | hd
      · exact h0
      · by_cases htriv : ∃ t ∈ levelTorus (unitaryInvolution F 2 f) (n := n) s, χ t ≠ 1
        · have hzero := curtisDatum_dScalar_eq_zero hF n hn ζ hζ χ hχmul s htriv
          rw [hd, hzero.2]
        · push Not at htriv
          have hone := curtisDatum_dScalar_eq_neg_one hF n hn ζ hζ χ s htriv
          exact absurd (hd.trans hone.2) hmu

end CFSG.LieType.Universal.Unitary
