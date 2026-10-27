module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Coord
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit

open CFSG CFSG.LocalCores CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 (cjComp cjComp_one cjComp_mul mem_cjComp_iff
  mem_cjComp_of_mem)

structure SplitCfg (p : ℕ) {Y : Type} [Group Y] [Finite Y] (P : Subgroup Y) (x : Y) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  sylow : CFSG.ABGLocalTools.IsSylowOf p P ⊤
  x_mem : x ∈ P
  x_pow : x ^ p = 1
  rank_le : ∀ E : Subgroup Y, E ≤ P → IsElemAbelian p E → x ∈ normalizer (E : Set Y) →
    Nat.card E ≤ p ^ p
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections Y
  card_comp : Nat.card (ComponentIndex Y) = p
  centre : ∀ C : ComponentIndex Y, center C.1 = ⊥
  trans : ∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C'
  cyclic : ∀ C : ComponentIndex Y, IsCyclic ↥(P ⊓ C.1)
  cent : ∀ g ∈ P, g ∈ centralizer (layer Y : Set Y) → g = 1
  dvd : ∀ C : ComponentIndex Y, p ∣ Nat.card C.1

section Cycle

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite Ω]

theorem cycle_bijective {p : ℕ} (hp : p.Prime) (hcard : Nat.card Ω = p) {e : G} (he : e ^ p = 1)
    {ω : Ω} (hne : e • ω ≠ ω) : Function.Bijective (fun k : Fin p => e ^ (k : ℕ) • ω) := by
  have key : ∀ d : ℕ, 0 < d → d < p → e ^ d • ω = ω → e • ω = ω := by
    intro d hd0 hdp hd
    have hcop : Nat.Coprime d p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact fun h => absurd (Nat.le_of_dvd hd0 h) (by omega)
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have h1 : e = (e ^ d) ^ m := by
      rw [← pow_mul, pow_eq_pow_mod (d * m) he, hm, pow_one]
    have h2 : e ^ d ∈ MulAction.stabilizer G ω := MulAction.mem_stabilizer_iff.mpr hd
    have h3 := MulAction.mem_stabilizer_iff.mp ((MulAction.stabilizer G ω).pow_mem h2 m)
    rwa [← h1] at h3
  have aux : ∀ k l : ℕ, k < l → l < p → e ^ k • ω = e ^ l • ω → False := by
    intro k l hkl hlp h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkl
    have h2 : e ^ k • (e ^ (d + 1) • ω) = e ^ k • ω := by
      rw [← mul_smul, ← pow_add, ← add_assoc]
      exact h.symm
    have h3 : e ^ (d + 1) • ω = ω := smul_left_cancel (e ^ k) h2
    exact hne (key (d + 1) (by omega) (by omega) h3)
  have hinj : Function.Injective (fun k : Fin p => e ^ (k : ℕ) • ω) := by
    intro k l h
    rcases lt_trichotomy (k : ℕ) l with hkl | hkl | hkl
    · exact (aux k l hkl l.2 h).elim
    · exact Fin.ext hkl
    · exact (aux l k hkl k.2 h.symm).elim
  exact hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])

theorem cycle_trans {p : ℕ} (hp : p.Prime) (hcard : Nat.card Ω = p) {e : G} (he : e ^ p = 1)
    {ω : Ω} (hne : e • ω ≠ ω) (α β : Ω) : ∃ k : ℕ, e ^ k • α = β := by
  obtain ⟨a, ha⟩ := (cycle_bijective hp hcard he hne).2 α
  obtain ⟨b, hb⟩ := (cycle_bijective hp hcard he hne).2 β
  refine ⟨b + (p - a), ?_⟩
  simp only at ha hb
  rw [← ha, ← hb, ← mul_smul, ← pow_add]
  have hapos : (a : ℕ) ≤ p := a.2.le
  have : (p - a) + a = p := by omega
  rw [show (b : ℕ) + (p - a) + a = (b : ℕ) + p from by omega, pow_add, he, mul_one]

theorem smul_ne_of_trans {p : ℕ} (hp : p.Prime) (hcard : Nat.card Ω = p) {e : G}
    (htrans : ∀ α β : Ω, ∃ k : ℕ, e ^ k • α = β) (ω : Ω) : e • ω ≠ ω := by
  intro h
  have hall : ∀ k : ℕ, e ^ k • ω = ω := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_smul, ih, h]
  have hsub : Subsingleton Ω := by
    refine ⟨fun α β => ?_⟩
    obtain ⟨k, hk⟩ := htrans ω α
    obtain ⟨l, hl⟩ := htrans ω β
    rw [← hk, ← hl, hall, hall]
  have : Nat.card Ω ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
  have := hp.two_le
  omega

theorem exists_idx {p : ℕ} (hp : p.Prime) (hcard : Nat.card Ω = p) {e : G} (he : e ^ p = 1)
    (htrans : ∀ α β : Ω, ∃ k : ℕ, e ^ k • α = β) (ω₀ : Ω) :
    ∃ idx : Ω → ℕ, (∀ β, e ^ idx β • ω₀ = β) ∧ ∀ k : ℕ, e ^ idx (e ^ k • ω₀) = e ^ k := by
  have hbij := cycle_bijective hp hcard he (smul_ne_of_trans hp hcard htrans ω₀)
  let b : Fin p ≃ Ω := Equiv.ofBijective _ hbij
  refine ⟨fun β => ((b.symm β : Fin p) : ℕ), fun β => ?_, fun k => ?_⟩
  · have := b.apply_symm_apply β
    exact this
  · have hp0 : 0 < p := hp.pos
    have hk : b ⟨k % p, Nat.mod_lt k hp0⟩ = e ^ k • ω₀ := by
      show e ^ (k % p) • ω₀ = e ^ k • ω₀
      rw [← pow_eq_pow_mod k he]
    have : b.symm (e ^ k • ω₀) = ⟨k % p, Nat.mod_lt k hp0⟩ := by
      rw [← hk, b.symm_apply_apply]
    show e ^ ((b.symm (e ^ k • ω₀) : Fin p) : ℕ) = e ^ k
    rw [this]
    exact (pow_eq_pow_mod k he).symm

end Cycle

section Action

variable {Y : Type} [Group Y] [Finite Y]

@[expose, instance_reducible] noncomputable def compAction (Y : Type) [Group Y] [Finite Y] :
    MulAction Y (ComponentIndex Y) where
  smul g C := cjComp g C
  one_smul C := cjComp_one C
  mul_smul g h C := cjComp_mul g h C

theorem mem_normalizer_of_cjComp_eq {g : Y} {C : ComponentIndex Y} (h : cjComp g C = C) :
    g ∈ normalizer (C.1 : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  have h1 : g * c * g⁻¹ ∈ C.1 ↔ g * c * g⁻¹ ∈ (cjComp g C).1 := by rw [h]
  rw [h1, mem_cjComp_iff]
  simp [mul_assoc]

theorem cjComp_eq_of_mem_normalizer {g : Y} {C : ComponentIndex Y}
    (hg : g ∈ normalizer (C.1 : Set Y)) : cjComp g C = C := by
  apply Subtype.ext
  ext c
  rw [mem_cjComp_iff]
  have := (Subgroup.mem_normalizer_iff.mp hg) (g⁻¹ * c * g)
  rw [this]
  simp [mul_assoc]

@[expose] def compKer (P : Subgroup Y) : Subgroup Y where
  carrier := {g | g ∈ P ∧ ∀ C : ComponentIndex Y, cjComp g C = C}
  mul_mem' := by
    rintro a b ⟨haP, ha⟩ ⟨hbP, hb⟩
    exact ⟨P.mul_mem haP hbP, fun C => by rw [cjComp_mul, hb C, ha C]⟩
  one_mem' := ⟨P.one_mem, fun C => cjComp_one C⟩
  inv_mem' := by
    rintro a ⟨haP, ha⟩
    refine ⟨P.inv_mem haP, fun C => ?_⟩
    have := cjComp_mul a⁻¹ a C
    rw [inv_mul_cancel, cjComp_one, ha C] at this
    exact this.symm

variable {P : Subgroup Y}

theorem compKer_le : compKer P ≤ P := fun _ hg => hg.1

theorem conj_mem_compKer {g q : Y} (hg : g ∈ P) (hq : q ∈ compKer P) :
    g * q * g⁻¹ ∈ compKer P := by
  refine ⟨P.mul_mem (P.mul_mem hg hq.1) (P.inv_mem hg), fun C => ?_⟩
  rw [cjComp_mul, cjComp_mul, hq.2, ← cjComp_mul, mul_inv_cancel, cjComp_one]

theorem mem_normalizer_of_mem_compKer {q : Y} (hq : q ∈ compKer P) (C : ComponentIndex Y) :
    q ∈ normalizer (C.1 : Set Y) :=
  mem_normalizer_of_cjComp_eq (hq.2 C)

theorem layer_inf_le_compKer : P ⊓ layer Y ≤ compKer P := fun g hg =>
  ⟨hg.1, fun C => cjComp_eq_of_mem_normalizer (layer_le_normalizer C.2 hg.2)⟩

end Action

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit
