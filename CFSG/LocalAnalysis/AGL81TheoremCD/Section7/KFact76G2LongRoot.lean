module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Components
import TauCeti.GroupTheory.Commutator

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7

open scoped commutatorElement

theorem exists_conj_not_commute_of_normalizer_lt {G : Type*} [Group G] {z t : G}
    (hQ : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({z} : Set G)))
    (hZ : Nat.card ↥(Subgroup.center ↥(Subgroup.centralizer ({z} : Set G))) = 3)
    (htz : Commute t z) (htZ : t ∉ Subgroup.zpowers z) {X : Subgroup G}
    (hX : Subgroup.normalizer (Subgroup.zpowers z : Set G) < X) :
    ∃ x ∈ X, ¬ Commute (x * t * x⁻¹) t ∧ ¬ Commute (x * t * x⁻¹) z := by
  classical
  set N := Subgroup.centralizer ({z} : Set G) with hNdef
  set H := Subgroup.normalizer (Subgroup.zpowers z : Set G) with hHdef
  have memN : ∀ {g : G}, g ∈ N ↔ Commute g z := fun {g} => by
    rw [hNdef, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hzN : z ∈ N := memN.2 (Commute.refl z)
  have htN : t ∈ N := memN.2 htz
  have hNH : N ≤ H := fun g hg => by
    rw [hHdef, Subgroup.mem_set_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe]
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      rw [((memN.1 hg).zpow_right k).eq, mul_inv_cancel_right]
      exact hh
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
      have : h = g⁻¹ * z ^ k * g := by rw [hk]; group
      rw [this, (((memN.1 hg).inv_left).zpow_right k).eq, inv_mul_cancel_right]
      exact Subgroup.zpow_mem_zpowers z k
  have hHX : H ≤ X := hX.le
  have hNX : N ≤ X := hNH.trans hHX
  have hz1 : z ≠ 1 := by
    rintro rfl
    refine hX.not_ge fun g _ => ?_
    rw [hHdef, Subgroup.mem_set_normalizer_iff]
    intro h
    simp only [Subgroup.zpowers_one_eq_bot, SetLike.mem_coe, Subgroup.mem_bot]
    constructor
    · rintro rfl; group
    · intro hh
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = 1 := by rw [hh]; group
  have hcen : ∀ c ∈ N, (∀ n ∈ N, Commute c n) → c ∈ Subgroup.zpowers z := by
    intro c hc hcN
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    set zc : ↥(Subgroup.center ↥N) := ⟨⟨z, hzN⟩, Subgroup.mem_center_iff.2 fun n =>
      Subtype.ext (memN.1 n.2).eq⟩
    set cc : ↥(Subgroup.center ↥N) := ⟨⟨c, hc⟩, Subgroup.mem_center_iff.2 fun n =>
      Subtype.ext (hcN n n.2).symm.eq⟩
    have hzc : zc ≠ 1 := fun h => hz1 (congrArg (fun y : ↥(Subgroup.center ↥N) =>
      ((y : ↥N) : G)) h)
    have hmem : cc ∈ Subgroup.zpowers zc := by
      rw [zpowers_eq_top_of_prime_card hZ hzc]
      trivial
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have : ((zc ^ k : ↥(Subgroup.center ↥N)) : ↥N) = ⟨c, hc⟩ := congrArg Subtype.val hk
    have : (((zc ^ k : ↥(Subgroup.center ↥N)) : ↥N) : G) = c := congrArg Subtype.val this
    rw [← this]
    simp only [SubgroupClass.coe_zpow]
    exact Subgroup.zpow_mem_zpowers z k
  set S : Set G := {y | ∃ k ∈ N, y = k * t * k⁻¹} with hS
  have hgen : N ≤ Subgroup.closure S := by
    set t' : ↥N := ⟨t, htN⟩
    have ht'Z : t' ∉ Subgroup.center ↥N := fun h =>
      htZ (hcen t htN fun n hn =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.1 h ⟨n, hn⟩) : n * t = t * n).symm)
    have hnc : Subgroup.normalClosure ({t'} : Set ↥N) = ⊤ := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ
        (Subgroup.normalClosure_normal (s := ({t'} : Set ↥N))) with h | h
      · exact h
      · exact absurd (h (Subgroup.subset_normalClosure (Set.mem_singleton _))) ht'Z
    intro k hk
    have h1 : (⟨k, hk⟩ : ↥N) ∈ Subgroup.normalClosure ({t'} : Set ↥N) := hnc ▸ trivial
    have h2 : k ∈ (Subgroup.normalClosure ({t'} : Set ↥N)).map N.subtype := ⟨_, h1, rfl⟩
    rw [Subgroup.normalClosure, MonoidHom.map_closure] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb, hbx⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    rw [Set.mem_singleton_iff] at hb
    subst hb
    obtain ⟨y, hy⟩ := isConj_iff.1 hbx
    exact ⟨y, y.2, by rw [← hy]; rfl⟩
  have hconj : ∀ y a b : G, Commute a b → Commute (y * a * y⁻¹) (y * b * y⁻¹) :=
    fun y a b h => by simpa [MulAut.conj_apply] using h.map (MulAut.conj y).toMonoidHom
  have hHz : ∀ h ∈ H, h⁻¹ * z * h ∈ Subgroup.zpowers z := fun h hh =>
    (Subgroup.mem_set_normalizer_iff''.1 hh z).1 (Subgroup.mem_zpowers z)
  have ha : ∃ g ∈ X, g * t * g⁻¹ ∉ H := by
    by_contra hcon
    push Not at hcon
    refine hX.not_ge fun x hx => ?_
    have hconjN : ∀ y ∈ X, ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
      intro y hy
      have hH : ∀ n ∈ N, y * n * y⁻¹ ∈ H := by
        have : Subgroup.closure S ≤ H.comap (MulAut.conj y).toMonoidHom := by
          rw [Subgroup.closure_le]
          rintro _ ⟨k, hk, rfl⟩
          show y * (k * t * k⁻¹) * y⁻¹ ∈ H
          have := hcon (y * k) (X.mul_mem hy (hNX hk))
          simpa [mul_assoc] using this
        exact fun n hn => this (hgen hn)
      set K' : Subgroup ↥N := (N.comap (MulAut.conj y).toMonoidHom).comap N.subtype
      have hK' : (⊤ : Subgroup ↥N) ≤ K' := by
        rw [← hQ.1.commutator_eq_top, commutator_def, Subgroup.commutator_le]
        intro a _ b _
        show y * ((⁅a, b⁆ : ↥N) : G) * y⁻¹ ∈ N
        have e : y * ((⁅a, b⁆ : ↥N) : G) * y⁻¹ =
            ⁅y * (a : G) * y⁻¹, y * (b : G) * y⁻¹⁆ := by
          simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]; group
        rw [e]
        exact memN.2 (TauCeti.commute_commutatorElement_of_inv_mul_mul_mem_zpowers
          (hHz _ (hH a a.2)) (hHz _ (hH b b.2)))
      exact fun n hn => hK' (Subgroup.mem_top (⟨n, hn⟩ : ↥N))
    have hxz : ∀ y ∈ X, y * z * y⁻¹ ∈ Subgroup.zpowers z := by
      intro y hy
      refine hcen _ (hconjN y hy z hzN) fun n hn => ?_
      have hm := hconjN y⁻¹ (X.inv_mem hy) n hn
      have h' := hconj y _ _ (memN.1 hm)
      have e : y * (y⁻¹ * n * y⁻¹⁻¹) * y⁻¹ = n := by group
      rw [e] at h'
      exact h'.symm
    rw [hHdef, Subgroup.mem_set_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe]
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ (hxz x hx) k
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
      have e : h = (x⁻¹ * z * x⁻¹⁻¹) ^ k := by rw [conj_zpow, hk]; group
      rw [e]
      exact Subgroup.zpow_mem _ (hxz x⁻¹ (X.inv_mem hx)) k
  obtain ⟨g, hgX, hgH⟩ := ha
  have hgz : ¬ Commute (g * t * g⁻¹) z := fun h => hgH (hNH (memN.2 h))
  have hb : ∃ n ∈ N, ¬ Commute (g * t * g⁻¹) (n * t * n⁻¹) := by
    by_contra hcon
    push Not at hcon
    refine hgz ?_
    have : Subgroup.closure S ≤ Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hcon k hk).eq
    have hz := this (hgen hzN)
    rw [Subgroup.mem_centralizer_iff] at hz
    exact hz _ rfl
  obtain ⟨n, hn, hnc⟩ := hb
  have e : n * (n⁻¹ * g * t * (n⁻¹ * g)⁻¹) * n⁻¹ = g * t * g⁻¹ := by group
  refine ⟨n⁻¹ * g, X.mul_mem (X.inv_mem (hNX hn)) hgX, fun h => hnc ?_, fun h => hgz ?_⟩
  · have h' := hconj n _ _ h
    rwa [e] at h'
  · have h' := hconj n _ _ h
    have e' : n * z * n⁻¹ = z := by rw [(memN.1 hn).eq, mul_inv_cancel_right]
    rwa [e, e'] at h'

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7
