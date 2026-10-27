module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoInAlpha
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamiliesAux
public import CFSG.LocalAnalysis.AGLEmbedding.CentralAlpha

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

@[expose] def KGenTwoModAb (p : ℕ) (K : Type) [Group K] : Prop :=
  ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ 2 →
    (∀ k l : K, MulAut.conj k ∈ E → MulAut.conj l ∈ E → k * l = l * k) →
    Subgroup.closure {k : K | ∃ e ∈ E, e ≠ 1 ∧ e k * k⁻¹ ∈ Subgroup.center K} = ⊤

theorem kGenTwoModAb_of_kGenTwoMod {p : ℕ} {K : Type} [Group K] (h : KGenTwoMod p K) :
    KGenTwoModAb p K :=
  fun E hE hEcard _ => h E hE hEcard

namespace ReducedNongeneration

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem isCyclic_centralizer (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K) :
    IsCyclic (Subgroup.centralizer (K : Set X)) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hmem : ∀ c ∈ Subgroup.centralizer (K : Set X), orderOf c = p → c ∈ K :=
    fun c hc hcp => mem_of_mem_centralizer_of_orderOf_eq R hKn (fun c hc hcp =>
      Subgroup.zpowers_le.mpr hzK
        (h.mem_zpowers_of_mem_inf_centralizer hz hzp hK hKn hzK c hc hcp)) hc hcp
  exact isCyclic_centralizer_of_forall_mem hp h.ne_two h.core_eq_bot hKn hmem
    (h.isCyclic_map_center hK hKn)

theorem commute_of_conjNormal_eq_conj (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K) {a b : X} (hab : a * b = b * a)
    {k l : K} (hk : MulAut.conjNormal (H := K) a = MulAut.conj k)
    (hl : MulAut.conjNormal (H := K) b = MulAut.conj l) : k * l = l * k := by
  have hcyc := h.isCyclic_centralizer hz hzp hK hKn hzK
  have hC : ∀ {x : X} {m : K}, MulAut.conjNormal (H := K) x = MulAut.conj m →
      (m : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
    intro x m hxm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : x * y * x⁻¹ = (m : X) * y * (m : X)⁻¹ := by
      have h2 := congrArg (fun φ : MulAut K => ((φ ⟨y, hy⟩ : K) : X)) hxm
      simpa [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_inv] using h2
    calc y * ((m : X)⁻¹ * x) = (m : X)⁻¹ * ((m : X) * y * (m : X)⁻¹) * x := by group
      _ = (m : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = (m : X)⁻¹ * x * y := by group
  have hcd : (k : X)⁻¹ * a * ((l : X)⁻¹ * b) = (l : X)⁻¹ * b * ((k : X)⁻¹ * a) :=
    congrArg Subtype.val (IsCyclic.isMulCommutative.is_comm.comm
      (⟨_, hC hk⟩ : Subgroup.centralizer (K : Set X)) ⟨_, hC hl⟩)
  have hcl : (k : X)⁻¹ * a * l = l * ((k : X)⁻¹ * a) :=
    (Subgroup.mem_centralizer_iff.mp (hC hk) l l.2).symm
  have hdk : (l : X)⁻¹ * b * k = k * ((l : X)⁻¹ * b) :=
    (Subgroup.mem_centralizer_iff.mp (hC hl) k k.2).symm
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  generalize hcc : (k : X)⁻¹ * a = cc at hcd hcl
  generalize hdd : (l : X)⁻¹ * b = dd at hcd hdk
  have ha' : a = k * cc := by rw [← hcc]; group
  have hb' : b = l * dd := by rw [← hdd]; group
  have e1 : a * b = (k : X) * l * (cc * dd) := by
    calc a * b = (k : X) * (cc * l) * dd := by rw [ha', hb']; group
      _ = (k : X) * (l * cc) * dd := by rw [hcl]
      _ = (k : X) * l * (cc * dd) := by group
  have e2 : b * a = (l : X) * k * (cc * dd) := by
    calc b * a = (l : X) * (dd * k) * cc := by rw [ha', hb']; group
      _ = (l : X) * (k * dd) * cc := by rw [hdk]
      _ = (l : X) * k * (dd * cc) := by group
      _ = (l : X) * k * (cc * dd) := by rw [hcd]
  exact mul_right_cancel (e1.symm.trans (hab.trans e2))

end ReducedNongeneration

end CFSG.AGLEmbedding
