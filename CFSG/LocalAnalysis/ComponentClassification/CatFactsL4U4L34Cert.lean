module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Data.CFSGNative.PSL3Four.Certificate
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L34CertInputs
public import Certificates.Certificate2005
public import Certificates.Certificate2022

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem cosetCheck_eq_true :
    cosetCheck (enumBFS 42 gensS 20160).tabs (enumBFS 42 gTabs 241920).tabs = true :=
  Certificates.certificate2005

structure CosetFacts : Prop where
  orbit : ∀ i < 8, orbitOK 42 gensS gensSInv repT[i]! (orbS repT[i]!) = true
  cover : coverOK 42 enumR.tabs (repT.map fun x => (orbS x).tabs) = true
  distinct : ∀ i < 8, ∀ j < 8, i ≠ j →
    notInOK enumS.tabs (comp 42 (invTab 42 repT[i]!) repT[j]!) = true
  invSize : ∀ i < 8, (invTab 42 repT[i]!).size = 42
  invComp : ∀ i < 8, comp 42 (invTab 42 repT[i]!) repT[i]! = idTab 42
  g4iSize : g4iT.size = 42
  g4iComp : comp 42 g4iT g₄T = idTab 42

theorem cosetFacts : CosetFacts := by
  have h := cosetCheck_eq_true
  simp only [cosetCheck, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, fun i hi j hj hij => ?_, fun i hi => (h4 i hi).1, fun i hi => (h4 i hi).2,
    h5, h6⟩
  rcases h3 i hi j hj with h | h
  · exact absurd h hij
  · exact h

@[expose] def repP : ℕ → Equiv.Perm (Fin 42)
  | 0 => r₁
  | 1 => g₅
  | 2 => g₄ * g₅ * g₄⁻¹
  | 3 => (g₄ * g₄) * g₅ * (g₄ * g₄)⁻¹
  | 4 => g₆
  | 5 => g₄ * g₆ * g₄⁻¹
  | 6 => (g₄ * g₄) * g₆ * (g₄ * g₄)⁻¹
  | _ => r₄

theorem tabRep_g4i : TabRep g4iT g₄⁻¹ :=
  tabRep_g₄.inv cosetFacts.g4iSize cosetFacts.g4iComp

theorem tabRep_g44 : TabRep g44T (g₄ * g₄) := tabRep_g₄.comp tabRep_g₄

theorem tabRep_g44i : TabRep g44iT (g₄ * g₄)⁻¹ := by
  rw [mul_inv_rev]
  exact tabRep_g4i.comp tabRep_g4i

theorem repP_spec : ∀ i < 8, TabRep repT[i]! (repP i) ∧ repP i ∈ R := by
  intro i hi
  have h4 := g₄_mem_R
  have h44 : g₄ * g₄ ∈ R := mul_mem h4 h4
  interval_cases i
  · exact ⟨tabRep_r₁, r₁_mem_R⟩
  · exact ⟨tabRep_g₅, g₅_mem_R⟩
  · exact ⟨tabRep_g₄.conjTab tabRep_g₅ tabRep_g4i,
      mul_mem (mul_mem h4 g₅_mem_R) (inv_mem h4)⟩
  · exact ⟨tabRep_g44.conjTab tabRep_g₅ tabRep_g44i,
      mul_mem (mul_mem h44 g₅_mem_R) (inv_mem h44)⟩
  · exact ⟨tabRep_g₆, g₆_mem_R⟩
  · exact ⟨tabRep_g₄.conjTab tabRep_g₆ tabRep_g4i,
      mul_mem (mul_mem h4 g₆_mem_R) (inv_mem h4)⟩
  · exact ⟨tabRep_g44.conjTab tabRep_g₆ tabRep_g44i,
      mul_mem (mul_mem h44 g₆_mem_R) (inv_mem h44)⟩
  · exact ⟨tabRep_r₄, r₄_mem_R⟩

theorem map_getElem! {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β) {i : ℕ}
    (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos (a.map f) i (by simpa using hi), getElem!_pos a i hi, Array.getElem_map]

theorem exists_conj_repP {t : Equiv.Perm (Fin 42)} (ht : t ∈ R) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) : ∃ i < 8, ∃ c ∈ S, t = c * repP i * c⁻¹ := by
  obtain ⟨i, hi, x, hx, hrep⟩ := exists_of_coverOK enumerates_R cosetFacts.cover ht ht1 ht2
  have hi8 : i < 8 := by simpa [repT] using hi
  rw [map_getElem! _ _ (by simpa [repT] using hi8)] at hx
  obtain ⟨hs, -, -⟩ := conj_orbit gensS_cover gensS_tabs (repP_spec i hi8).1
    (cosetFacts.orbit i hi8)
  obtain ⟨c, hc, hcr⟩ := hs x hx
  exact ⟨i, hi8, c, hc, hrep.perm_eq hcr⟩

theorem repP_inv_mul_not_mem {i j : ℕ} (hi : i < 8) (hj : j < 8) (hij : i ≠ j) :
    (repP i)⁻¹ * repP j ∉ S := by
  have hinv : TabRep (invTab 42 repT[i]!) (repP i)⁻¹ :=
    (repP_spec i hi).1.inv (cosetFacts.invSize i hi) (cosetFacts.invComp i hi)
  exact not_mem_of_notInOK enumerates_S (cosetFacts.distinct i hi j hj hij)
    (hinv.comp (repP_spec j hj).1)

theorem conj_of_mul_mem_S {t t' : Equiv.Perm (Fin 42)} (ht : t ∈ R) (ht' : t' ∈ R)
    (ht2 : t * t = 1) (ht'2 : t' * t' = 1) (ht1 : t ≠ 1) (ht'1 : t' ≠ 1) (hS : t⁻¹ * t' ∈ S) :
    ∃ y ∈ S, y * t * y⁻¹ = t' := by
  obtain ⟨i, hi, c, hc, rfl⟩ := exists_conj_repP ht ht2 ht1
  obtain ⟨j, hj, c', hc', rfl⟩ := exists_conj_repP ht' ht'2 ht'1
  have hij : i = j := by
    by_contra hij
    apply repP_inv_mul_not_mem hi hj hij
    set d := c⁻¹ * c' with hd
    have hdS : d ∈ S := mul_mem (inv_mem hc) hc'
    have hX : (repP i)⁻¹ * d * repP j * d⁻¹ ∈ S := by
      have := conj_mem_S (inv_mem (S_le_R hc)) hS
      convert this using 1
      rw [hd]
      group
    have hY : (repP i)⁻¹ * d⁻¹ * (repP i)⁻¹⁻¹ ∈ S :=
      conj_mem_S (inv_mem (repP_spec i hi).2) (inv_mem hdS)
    have := mul_mem (mul_mem hY hX) hdS
    convert this using 1
    group
  subst hij
  refine ⟨c' * c⁻¹, mul_mem hc' (inv_mem hc), ?_⟩
  group

theorem eq_bot_of_commutator_eq_of_isPGroup {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} [Finite X] (hp : IsPGroup p X) (hX : ⁅X, X⁆ = X) : X = ⊥ := by
  have : Group.IsNilpotent X := hp.isNilpotent
  have htop : commutator X = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_subtype_commutator, hX, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hder : ∀ n, derivedSeries X n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := X)
  rw [hder] at hn
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : X) ∈ (⊥ : Subgroup X) := hn ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at hx' ⊢
  exact congrArg Subtype.val hx'

theorem card_centralizer_inf_S {x : Equiv.Perm (Fin 42)} (hx : x ∈ S) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : Nat.card ↥(Subgroup.centralizer {x} ⊓ S) = 64 := by
  set x' : R := ⟨x, S_le_R hx⟩
  have hx'2 : orderOf x' = 2 := by
    apply orderOf_eq_prime
    · exact Subtype.ext (by rw [pow_two]; exact hx2)
    · intro h
      exact hx1 (congrArg Subtype.val h)
  obtain ⟨-, -, -, -, -, hcls, -, -, -, -, -, -, hout, -⟩ := involution_enumeration
  have h1 : IsConj x' r₁R := by
    rcases (hcls x').1 hx'2 with h | h | h | h
    · exact h
    all_goals exact absurd hx (hout x' (by tauto))
  obtain ⟨c, hcR, hxc⟩ := eq_conj_of_isConj h1
  have hmap : C₁.map (MulAut.conj c).toMonoidHom = Subgroup.centralizer {x} ⊓ S := by
    ext w
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyc, hyS⟩ := Subgroup.mem_inf.1 hy
      refine Subgroup.mem_inf.2 ⟨?_, conj_mem_S hcR hyS⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
      show c * y * c⁻¹ * x = x * (c * y * c⁻¹)
      rw [show (x : Equiv.Perm (Fin 42)) = c * r₁ * c⁻¹ from hxc]
      calc c * y * c⁻¹ * (c * r₁ * c⁻¹) = c * (y * r₁) * c⁻¹ := by group
        _ = c * (r₁ * y) * c⁻¹ := by rw [hyc]
        _ = c * r₁ * c⁻¹ * (c * y * c⁻¹) := by group
    · intro hw
      obtain ⟨hwc, hwS⟩ := Subgroup.mem_inf.1 hw
      refine ⟨c⁻¹ * w * c, Subgroup.mem_inf.2 ⟨?_, ?_⟩, by group⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hwc ⊢
        rw [show (x : Equiv.Perm (Fin 42)) = c * r₁ * c⁻¹ from hxc] at hwc
        calc c⁻¹ * w * c * r₁ = c⁻¹ * (w * (c * r₁ * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * r₁ * c⁻¹) * w) * c := by rw [hwc]
          _ = r₁ * (c⁻¹ * w * c) := by group
      · have := conj_mem_S (inv_mem hcR) hwS
        simpa using this
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact card_C₁

theorem eq_bot_of_le_centralizer {x : Equiv.Perm (Fin 42)} (hx : x ∈ S) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) {X : Subgroup (Equiv.Perm (Fin 42))} (hXc : X ≤ Subgroup.centralizer {x} ⊓ S)
    (hX : ⁅X, X⁆ = X) : X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : IsPGroup 2 ↥(Subgroup.centralizer {x} ⊓ S) :=
    IsPGroup.of_card (n := 6) (by rw [card_centralizer_inf_S hx hx2 hx1]; norm_num)
  exact eq_bot_of_commutator_eq_of_isPGroup (hC.to_le hXc) hX

end CFSG.ComponentClassification.CatFactsL4U4
