module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
public import CFSG.LocalAnalysis.AGLEmbedding.AltBetaGen

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section Perm

variable {n p : ℕ}

namespace AltThree

def shiftPerm (p : ℕ) (v : Fin 3 → ZMod p) : Equiv.Perm (Fin 3 × ZMod p) where
  toFun a := (a.1, a.2 + v a.1)
  invFun a := (a.1, a.2 - v a.1)
  left_inv a := by simp
  right_inv a := by simp

def shiftHom (p : ℕ) : Multiplicative (Fin 3 → ZMod p) →* Equiv.Perm (Fin 3 × ZMod p) where
  toFun v := shiftPerm p (Multiplicative.toAdd v)
  map_one' := by
    ext a <;> simp [shiftPerm]
  map_mul' u v := by
    ext a <;> simp [shiftPerm]
    ring

theorem shiftHom_injective (p : ℕ) : Function.Injective (shiftHom p) := by
  intro u v h
  have key : ∀ i : Fin 3, Multiplicative.toAdd u i = Multiplicative.toAdd v i := by
    intro i
    have := congrArg (fun σ : Equiv.Perm (Fin 3 × ZMod p) => (σ (i, 0)).2) h
    simpa [shiftHom, shiftPerm] using this
  exact Multiplicative.toAdd.injective (funext key)

theorem zmodCube_pow_eq_one (p : ℕ) (v : Multiplicative (Fin 3 → ZMod p)) : v ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  ext i
  simp

theorem natCard_zmodCube (p : ℕ) [NeZero p] :
    Nat.card (Multiplicative (Fin 3 → ZMod p)) = p ^ 3 := by
  simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem sign_eq_one_of_pow_eq_one {p : ℕ} {α : Type*} [DecidableEq α] [Fintype α] (hp : Odd p)
    {g : Equiv.Perm α} (hg : g ^ p = 1) : Equiv.Perm.sign g = 1 := by
  have h1 : Equiv.Perm.sign g ^ p = 1 := by rw [← map_pow, hg, map_one]
  rwa [Int.units_pow_eq_pow_mod_two, Nat.odd_iff.mp hp, pow_one] at h1

end AltThree

theorem three_le_pRank_alternatingGroup (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 * p ≤ n) :
    3 ≤ Open.pRank p (⊤ : Subgroup (alternatingGroup (Fin n))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hcard : Fintype.card (Fin 3 × ZMod p) ≤ Fintype.card (Fin n) := by
    simpa [Fintype.card_prod, ZMod.card] using hn
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  let ψ : Multiplicative (Fin 3 → ZMod p) →* Equiv.Perm (Fin n) :=
    (Equiv.Perm.viaEmbeddingHom ι).comp (AltThree.shiftHom p)
  have hψ : Function.Injective ψ :=
    (Equiv.Perm.viaEmbeddingHom_injective ι).comp (AltThree.shiftHom_injective p)
  have hE : IsElemAbelian p ψ.range := by
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨v, rfl⟩
    rw [← map_pow, AltThree.zmodCube_pow_eq_one, map_one]
  have hEA : ψ.range ≤ alternatingGroup (Fin n) := fun g hg =>
    Equiv.Perm.mem_alternatingGroup.mpr (AltThree.sign_eq_one_of_pow_eq_one hodd (hE.2 g hg))
  have hcardE : Nat.card ψ.range = p ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, AltThree.natCard_zmodCube]
  have hE' : IsElemAbelian p (ψ.range.subgroupOf (alternatingGroup (Fin n))) := by
    have : IsMulCommutative ψ.range := hE.1
    refine ⟨?_, fun x hx => Subtype.ext (hE.2 x hx)⟩
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_injective_isMulCommutative ψ.range
      (alternatingGroup (Fin n)).subtype_injective
  refine le_csSup (pRank_bddAbove p hp _) ⟨_, le_top, hE', ?_⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv, hcardE]

namespace AltOrbit

lemma exists_ne_one_of_one_lt_card {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (h : 1 < Nat.card S) : ∃ s ∈ S, s ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : S = ⊥ := (Subgroup.eq_bot_iff_forall S).2 hcon
  rw [hbot, Subgroup.card_bot] at h
  exact lt_irrefl _ h

lemma eq_one_of_mem_of_mem {G : Type*} [Group G] [Finite G] (hp : p.Prime) {S T : Subgroup G}
    (hS : Nat.card S = p) (hT : Nat.card T = p) (hne : S ≠ T) {s : G} (hsS : s ∈ S)
    (hsT : s ∈ T) : s = 1 := by
  have hdvd : Nat.card (S ⊓ T : Subgroup G) ∣ p := hS ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · have hbot : (S ⊓ T : Subgroup G) = ⊥ := Subgroup.eq_bot_of_card_eq _ h
    have hs : s ∈ (S ⊓ T : Subgroup G) := ⟨hsS, hsT⟩
    rw [hbot] at hs
    exact Subgroup.mem_bot.1 hs
  · exfalso
    apply hne
    have h1 : (S ⊓ T : Subgroup G) = S :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hS])
    have h2 : (S ⊓ T : Subgroup G) = T :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hT])
    rw [← h1, h2]

variable {E : Subgroup (Equiv.Perm (Fin n))}

lemma ncard_orbit_mul_card_stabilizer (hcard : Nat.card E = p ^ 2) (x : Fin n) :
    (MulAction.orbit E x).ncard * Nat.card (MulAction.stabilizer E x) = p ^ 2 := by
  rw [← MulAction.index_stabilizer, Subgroup.index_mul_card, hcard]

lemma ncard_orbit_le (x : Fin n) : (MulAction.orbit E x).ncard ≤ n := by
  calc (MulAction.orbit E x).ncard ≤ (Set.univ : Set (Fin n)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _)
    _ = n := by simp [Set.ncard_univ]

lemma ncard_orbit_eq_one_or (hp : p.Prime) (hp2 : p ≠ 2) (hn : n < 3 * p)
    (hcard : Nat.card E = p ^ 2) (x : Fin n) :
    (MulAction.orbit E x).ncard = 1 ∨ (MulAction.orbit E x).ncard = p := by
  have hmul := ncard_orbit_mul_card_stabilizer hcard x
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hdvd : (MulAction.orbit E x).ncard ∣ p ^ 2 := Dvd.intro _ hmul
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hle := ncard_orbit_le (E := E) x
  interval_cases k
  · left; simpa using hk'
  · right; simpa using hk'
  · exfalso
    have h3 : 3 * p ≤ p ^ 2 := by nlinarith
    omega

lemma ncard_orbit_of_stabilizer_ne_top (hp : p.Prime) (hp2 : p ≠ 2) (hn : n < 3 * p)
    (hcard : Nat.card E = p ^ 2) {x : Fin n} (hx : MulAction.stabilizer E x ≠ ⊤) :
    (MulAction.orbit E x).ncard = p ∧ Nat.card (MulAction.stabilizer E x) = p := by
  have hmul := ncard_orbit_mul_card_stabilizer hcard x
  have horb : (MulAction.orbit E x).ncard = p := by
    rcases ncard_orbit_eq_one_or hp hp2 hn hcard x with h | h
    · exfalso
      apply hx
      rw [h, one_mul, ← hcard] at hmul
      exact (Subgroup.card_eq_iff_eq_top _).1 hmul
    · exact h
  refine ⟨horb, ?_⟩
  rw [horb] at hmul
  exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [hmul]; ring)

lemma stabilizer_eq_of_mem_orbit (hcomm : ∀ a b : E, a * b = b * a) {x z : Fin n}
    (hz : z ∈ MulAction.orbit E x) :
    MulAction.stabilizer E z = MulAction.stabilizer E x := by
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 hz
  ext e
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← mul_smul, hcomm e g, mul_smul,
    smul_left_cancel_iff]

lemma disjoint_orbit_of_notMem {x z : Fin n} (h : z ∉ MulAction.orbit E x) :
    _root_.Disjoint (MulAction.orbit E z) (MulAction.orbit E x) := by
  rw [Set.disjoint_left]
  intro w hwz hwx
  apply h
  have h1 : MulAction.orbit E w = MulAction.orbit E z := MulAction.orbit_eq_iff.2 hwz
  have h2 : MulAction.orbit E w = MulAction.orbit E x := MulAction.orbit_eq_iff.2 hwx
  rw [← h2, h1]
  exact MulAction.mem_orbit_self z

lemma exists_ne_stabilizer (hp : p.Prime) (hp2 : p ≠ 2) (hn : n < 3 * p)
    (hcard : Nat.card E = p ^ 2) :
    ∃ x y : Fin n, MulAction.stabilizer E x ≠ ⊤ ∧ MulAction.stabilizer E y ≠ ⊤ ∧
      MulAction.stabilizer E x ≠ MulAction.stabilizer E y := by
  have hp1 : 1 < p := hp.one_lt
  have hE1 : 1 < Nat.card E := by
    rw [hcard]
    nlinarith
  obtain ⟨e, heE, he1⟩ := exists_ne_one_of_one_lt_card hE1
  have hmoved : ∃ x : Fin n, e x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact he1 (Equiv.ext hcon)
  obtain ⟨x, hx⟩ := hmoved
  have hSx : MulAction.stabilizer E x ≠ ⊤ := by
    intro h
    have hmem : (⟨e, heE⟩ : E) ∈ MulAction.stabilizer E x := by
      rw [h]; exact Subgroup.mem_top _
    exact hx (MulAction.mem_stabilizer_iff.1 hmem)
  by_contra hcon
  push Not at hcon
  have hSxcard := (ncard_orbit_of_stabilizer_ne_top hp hp2 hn hcard hSx).2
  obtain ⟨s, hs, hs1⟩ := exists_ne_one_of_one_lt_card (S := MulAction.stabilizer E x)
    (by rw [hSxcard]; exact hp1)
  apply hs1
  have hfix : ∀ z : Fin n, s • z = z := by
    intro z
    by_cases hz : MulAction.stabilizer E z = ⊤
    · apply MulAction.mem_stabilizer_iff.1
      rw [hz]; exact Subgroup.mem_top _
    · apply MulAction.mem_stabilizer_iff.1
      rw [← hcon x z hSx hz]
      exact hs
  exact Subtype.ext (Equiv.ext fun z => hfix z)

lemma stabilizer_eq_top_of_notMem (hp : p.Prime) (hp2 : p ≠ 2) (hn : n < 3 * p)
    (hcard : Nat.card E = p ^ 2) (hcomm : ∀ a b : E, a * b = b * a) {x y : Fin n}
    (hx : MulAction.stabilizer E x ≠ ⊤) (hy : MulAction.stabilizer E y ≠ ⊤)
    (hxy : MulAction.stabilizer E x ≠ MulAction.stabilizer E y) {z : Fin n}
    (hzx : z ∉ MulAction.orbit E x) (hzy : z ∉ MulAction.orbit E y) :
    MulAction.stabilizer E z = ⊤ := by
  by_contra hz
  have hxo := (ncard_orbit_of_stabilizer_ne_top hp hp2 hn hcard hx).1
  have hyo := (ncard_orbit_of_stabilizer_ne_top hp hp2 hn hcard hy).1
  have hzo := (ncard_orbit_of_stabilizer_ne_top hp hp2 hn hcard hz).1
  have hyx : y ∉ MulAction.orbit E x := fun h =>
    hxy (stabilizer_eq_of_mem_orbit hcomm h).symm
  have hd1 : _root_.Disjoint (MulAction.orbit E z) (MulAction.orbit E x) :=
    disjoint_orbit_of_notMem hzx
  have hd2 : _root_.Disjoint (MulAction.orbit E z) (MulAction.orbit E y) :=
    disjoint_orbit_of_notMem hzy
  have hd3 : _root_.Disjoint (MulAction.orbit E y) (MulAction.orbit E x) :=
    disjoint_orbit_of_notMem hyx
  have hd12 : _root_.Disjoint (MulAction.orbit E z)
      (MulAction.orbit E x ∪ MulAction.orbit E y) := Set.disjoint_union_right.2 ⟨hd1, hd2⟩
  have hcount : (MulAction.orbit E z ∪ (MulAction.orbit E x ∪ MulAction.orbit E y)).ncard =
      3 * p := by
    rw [Set.ncard_union_eq hd12, Set.ncard_union_eq hd3.symm, hxo, hyo, hzo]
    ring
  have hle : (MulAction.orbit E z ∪ (MulAction.orbit E x ∪ MulAction.orbit E y)).ncard ≤ n := by
    calc _ ≤ (Set.univ : Set (Fin n)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = n := by simp [Set.ncard_univ]
  omega

lemma smul_ne_self_iff (hp : p.Prime) (hp2 : p ≠ 2) (hn : n < 3 * p)
    (hcard : Nat.card E = p ^ 2) (hcomm : ∀ a b : E, a * b = b * a) {x y : Fin n}
    (hx : MulAction.stabilizer E x ≠ ⊤) (hy : MulAction.stabilizer E y ≠ ⊤)
    (hxy : MulAction.stabilizer E x ≠ MulAction.stabilizer E y) {a : E}
    (ha : a ∈ MulAction.stabilizer E y) (ha1 : a ≠ 1) (z : Fin n) :
    a • z ≠ z ↔ z ∈ MulAction.orbit E x := by
  have hxc := (ncard_orbit_of_stabilizer_ne_top hp hp2 hn hcard hx).2
  have hyc := (ncard_orbit_of_stabilizer_ne_top hp hp2 hn hcard hy).2
  constructor
  · intro hmove
    by_contra hzx
    apply hmove
    apply MulAction.mem_stabilizer_iff.1
    by_cases hzy : z ∈ MulAction.orbit E y
    · rw [stabilizer_eq_of_mem_orbit hcomm hzy]
      exact ha
    · rw [stabilizer_eq_top_of_notMem hp hp2 hn hcard hcomm hx hy hxy hzx hzy]
      exact Subgroup.mem_top _
  · intro hz hfix
    apply ha1
    refine eq_one_of_mem_of_mem hp hxc hyc hxy ?_ ha
    rw [← stabilizer_eq_of_mem_orbit hcomm hz]
    exact MulAction.mem_stabilizer_iff.2 hfix

end AltOrbit

theorem exists_cycles_of_isElemAbelian (hp : p.Prime) (hp2 : p ≠ 2) (hn : n < 3 * p)
    {E : Subgroup (Equiv.Perm (Fin n))} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) :
    ∃ a₁ ∈ E, ∃ a₂ ∈ E, ∃ O₁ O₂ : Finset (Fin n), O₁.card = p ∧ O₂.card = p ∧
      Disjoint O₁ O₂ ∧ (∀ x, a₁ x ≠ x ↔ x ∈ O₁) ∧ (∀ x, a₂ x ≠ x ↔ x ∈ O₂) := by
  have hcomm : ∀ a b : E, a * b = b * a := isMulCommutative_iff.1 hE.1
  obtain ⟨x, y, hx, hy, hxy⟩ := AltOrbit.exists_ne_stabilizer hp hp2 hn hcard
  have hxp := AltOrbit.ncard_orbit_of_stabilizer_ne_top hp hp2 hn hcard hx
  have hyp := AltOrbit.ncard_orbit_of_stabilizer_ne_top hp hp2 hn hcard hy
  obtain ⟨a₁, ha₁, ha₁1⟩ := AltOrbit.exists_ne_one_of_one_lt_card
    (S := MulAction.stabilizer E y) (by rw [hyp.2]; exact hp.one_lt)
  obtain ⟨a₂, ha₂, ha₂1⟩ := AltOrbit.exists_ne_one_of_one_lt_card
    (S := MulAction.stabilizer E x) (by rw [hxp.2]; exact hp.one_lt)
  have hyx : y ∉ MulAction.orbit E x := fun h =>
    hxy (AltOrbit.stabilizer_eq_of_mem_orbit hcomm h).symm
  have hdisj : _root_.Disjoint (MulAction.orbit E x) (MulAction.orbit E y) :=
    (AltOrbit.disjoint_orbit_of_notMem hyx).symm
  refine ⟨a₁, a₁.2, a₂, a₂.2, (Set.toFinite (MulAction.orbit E x)).toFinset,
    (Set.toFinite (MulAction.orbit E y)).toFinset, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Set.ncard_eq_toFinset_card (MulAction.orbit E x) (Set.toFinite _)).symm.trans hxp.1
  · exact (Set.ncard_eq_toFinset_card (MulAction.orbit E y) (Set.toFinite _)).symm.trans hyp.1
  · exact Set.Finite.disjoint_toFinset.2 hdisj
  · intro z
    rw [Set.Finite.mem_toFinset]
    exact AltOrbit.smul_ne_self_iff hp hp2 hn hcard hcomm hx hy hxy ha₁ ha₁1 z
  · intro z
    rw [Set.Finite.mem_toFinset]
    exact AltOrbit.smul_ne_self_iff hp hp2 hn hcard hcomm hy hx hxy.symm ha₂ ha₂1 z

namespace AltGen

open Equiv Equiv.Perm Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

alias swap_mul_swap_rotate := CFSG.AGLEmbedding.swap_mul_swap_rotate
alias swap_mul_swap_eq_mul := CFSG.AGLEmbedding.swap_mul_swap_eq_mul
alias support_swap_mul_swap_of_ne := CFSG.AGLEmbedding.support_swap_mul_swap_of_ne
alias isThreeCycle_swap_mul_swap := CFSG.AGLEmbedding.isThreeCycle_swap_mul_swap
alias alternatingGroup_le_of_swap_mul_swap_mem :=
  CFSG.AGLEmbedding.alternatingGroup_le_of_swap_mul_swap_mem
alias swap_mul_swap_mem_of_notMem := CFSG.AGLEmbedding.swap_mul_swap_mem_of_notMem
alias swap_mul_swap_mem_of_mem := CFSG.AGLEmbedding.swap_mul_swap_mem_of_mem
alias swap_mul_swap_mem_of_notMem_union := CFSG.AGLEmbedding.swap_mul_swap_mem_of_notMem_union
alias alternatingGroup_le_of_disjoint := CFSG.AGLEmbedding.alternatingGroup_le_of_disjoint

theorem mem_map_centralizer_of_disjoint {β : Type*} [Fintype β] [DecidableEq β]
    (a : alternatingGroup β) {g : Perm β} (hg : g.IsThreeCycle)
    (hd : _root_.Disjoint g.support (a : Perm β).support) :
    g ∈ (Subgroup.centralizer ({a} : Set (alternatingGroup β))).map
      (alternatingGroup β).subtype := by
  refine Subgroup.mem_map.mpr ⟨⟨g, hg.mem_alternatingGroup⟩, ?_, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (Equiv.Perm.disjoint_iff_disjoint_support.mpr hd).commute.eq

end AltGen

theorem closure_centralizers_eq_top (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 * p < n)
    (a₁ a₂ : alternatingGroup (Fin n)) (O₁ O₂ : Finset (Fin n)) (h₁ : O₁.card = p)
    (h₂ : O₂.card = p) (hO : Disjoint O₁ O₂) (ha₁ : ∀ x, (a₁ : Equiv.Perm (Fin n)) x ≠ x ↔ x ∈ O₁)
    (ha₂ : ∀ x, (a₂ : Equiv.Perm (Fin n)) x ≠ x ↔ x ∈ O₂) :
    Subgroup.centralizer ({a₁} : Set (alternatingGroup (Fin n))) ⊔
      Subgroup.centralizer ({a₂} : Set (alternatingGroup (Fin n))) = ⊤ := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hs₁ : (a₁ : Equiv.Perm (Fin n)).support = O₁ := by
    ext x
    rw [Equiv.Perm.mem_support]
    exact ha₁ x
  have hs₂ : (a₂ : Equiv.Perm (Fin n)).support = O₂ := by
    ext x
    rw [Equiv.Perm.mem_support]
    exact ha₂ x
  have hS₁ : ∀ g : Equiv.Perm (Fin n), g.IsThreeCycle → _root_.Disjoint g.support O₁ →
      g ∈ (Subgroup.centralizer ({a₁} : Set (alternatingGroup (Fin n))) ⊔
        Subgroup.centralizer ({a₂} : Set (alternatingGroup (Fin n)))).map
          (alternatingGroup (Fin n)).subtype := by
    intro g hg hd
    rw [← hs₁] at hd
    exact Subgroup.map_mono le_sup_left (AltGen.mem_map_centralizer_of_disjoint a₁ hg hd)
  have hS₂ : ∀ g : Equiv.Perm (Fin n), g.IsThreeCycle → _root_.Disjoint g.support O₂ →
      g ∈ (Subgroup.centralizer ({a₁} : Set (alternatingGroup (Fin n))) ⊔
        Subgroup.centralizer ({a₂} : Set (alternatingGroup (Fin n)))).map
          (alternatingGroup (Fin n)).subtype := by
    intro g hg hd
    rw [← hs₂] at hd
    exact Subgroup.map_mono le_sup_right (AltGen.mem_map_centralizer_of_disjoint a₂ hg hd)
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := O₁ ∪ O₂) (t := Finset.univ)
    (by rw [Finset.card_union_of_disjoint hO, h₁, h₂, Finset.card_univ, Fintype.card_fin]; omega)
  simp only [Finset.mem_union, not_or] at hx
  have hle := AltGen.alternatingGroup_le_of_disjoint hS₁ hS₂ hO (by omega) (by omega) hx.1 hx.2
  rw [eq_top_iff]
  intro g _
  obtain ⟨h, hh, hhg⟩ := Subgroup.mem_map.mp (hle g.2)
  rwa [Subtype.ext hhg] at hh

end Perm

end CFSG.AGLEmbeddingD2
