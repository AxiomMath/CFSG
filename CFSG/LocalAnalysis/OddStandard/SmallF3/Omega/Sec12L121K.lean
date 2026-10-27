module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121PL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L120A

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S E : Subgroup G}

theorem sec121_closure_ker (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5)))
    {u : Fin 5 → G} (hu : ∀ i, u i ∈ E) (hfu : ∀ i, sec12f t (u i) = φ (wvec i)) :
    ∀ x ∈ Subgroup.closure ((secB S L : Set G) ∪ {z | ∃ i j, z = u i * u j}),
      sec12f t x = 1 → x ∈ secB S L := by
  classical
  have hB_le_E : secB S L ≤ E := le_sup_left.trans (sec120_A_le_E F hE)
  have hφ0 : φ 0 = 1 := by
    have h0ev : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
    have h00 : φ 0 = φ 0 * φ 0 := by simpa using hperm.1 0 0 h0ev h0ev
    exact mul_eq_left.mp h00.symm
  have hBex : ∀ b : G, b ∈ secB S L → ∃ v : Fin 5 → ZMod 2, IsEvenVec v ∧ φ v = b :=
    fun b hb => (hperm.2.2.1 b).1 hb
  choose! ξ hξ using hBex
  have hφmem : ∀ {v : Fin 5 → ZMod 2}, IsEvenVec v → φ v ∈ secB S L :=
    fun {v} hv => (hperm.2.2.1 (φ v)).2 ⟨v, hv, rfl⟩
  have hξφ : ∀ {v : Fin 5 → ZMod 2}, IsEvenVec v → ξ (φ v) = v := by
    intro v hv
    exact hperm.2.1 (ξ (φ v)) v (hξ (φ v) (hφmem hv)).1 hv (hξ (φ v) (hφmem hv)).2
  have heven_add : ∀ {v w : Fin 5 → ZMod 2}, IsEvenVec v → IsEvenVec w →
      IsEvenVec (v + w) := by
    intro v w hv hw
    unfold IsEvenVec at hv hw ⊢
    simp only [Pi.add_apply, Finset.sum_add_distrib, hv, hw, add_zero]
  have hξ0 : ξ 1 = 0 := by
    have h0ev : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
    simpa [hφ0] using hξφ h0ev
  have hξ_mul : ∀ {b b' : G}, b ∈ secB S L → b' ∈ secB S L →
      ξ (b * b') = ξ b + ξ b' := by
    intro b b' hb hb'
    have hmem : b * b' ∈ secB S L := (secB S L).mul_mem hb hb'
    have hsum : IsEvenVec (ξ b + ξ b') := heven_add (hξ b hb).1 (hξ b' hb').1
    have hφ : φ (ξ b + ξ b') = b * b' := by
      rw [hperm.1 (ξ b) (ξ b') (hξ b hb).1 (hξ b' hb').1, (hξ b hb).2, (hξ b' hb').2]
    exact hperm.2.1 (ξ (b * b')) (ξ b + ξ b') (hξ (b * b') hmem).1 hsum
      (by rw [(hξ (b * b') hmem).2, hφ])
  let ψ : ↥E →* Multiplicative (Fin 5 → ZMod 2) :=
    { toFun := fun e => Multiplicative.ofAdd (ξ (sec12f t (e : G)))
      map_one' := by
        change Multiplicative.ofAdd (ξ (sec12f t ((1 : ↥E) : G))) = 1
        have h1 : sec12f t ((1 : ↥E) : G) = 1 := by simp [sec12f]
        rw [h1, hξ0]
        rfl
      map_mul' := fun e e' => by
        change Multiplicative.ofAdd (ξ (sec12f t ((e : G) * (e' : G)))) =
          Multiplicative.ofAdd (ξ (sec12f t (e : G))) *
            Multiplicative.ofAdd (ξ (sec12f t (e' : G)))
        rw [sec12E_f_mul F (hE.1 e.2) (hE.1 e'.2)]
        rw [hξ_mul (sec12E_f_mem F (hE.1 e.2)) (sec12E_f_mem F (hE.1 e'.2))]
        rfl }
  let N : Subgroup ↥E := (secB S L).subgroupOf E
  have hNmem : ∀ n : ↥E, n ∈ N ↔ (n : G) ∈ secB S L := by
    intro n
    change n ∈ (secB S L).subgroupOf E ↔ (n : G) ∈ secB S L
    exact Subgroup.mem_subgroupOf
  have hNnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hNmem] at hn ⊢
    have hgB : (g : G) ∈ centralizer (secB S L : Set G) := by
      have hgP : (g : G) ∈ secM t S L ⊓ centralizer (secB S L : Set G) := hE.1 g.2
      exact (Subgroup.mem_inf.mp hgP).2
    have hgn : (g : G) * (n : G) = (n : G) * (g : G) :=
      ((Subgroup.mem_centralizer_iff.mp hgB) (n : G) hn).symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hconj : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
      rw [hgn]; group
    rwa [hconj]
  have hNker : N ≤ ψ.ker := by
    intro n hn
    change Multiplicative.ofAdd (ξ (sec12f t (n : G))) = 1
    have hnB : (n : G) ∈ secB S L := (hNmem n).1 hn
    have hf : sec12f t (n : G) = 1 :=
      (sec120_f_eq_one_iff F hE n.2).2 (Subgroup.mem_sup_left hnB)
    rw [hf, hξ0]
    rfl
  haveI : N.Normal := hNnormal
  let Q := ↥E ⧸ N
  let ℓ : Q → Fin 5 → ZMod 2 :=
    fun x => Multiplicative.toAdd
      (QuotientGroup.lift N ψ hNker (show ↥E ⧸ N from x))
  have hℓ : ∀ x y : Q, ℓ (x * y) = ℓ x + ℓ y := by
    intro x y
    change Multiplicative.toAdd
        (QuotientGroup.lift N ψ hNker (show ↥E ⧸ N from x * y)) =
      Multiplicative.toAdd (QuotientGroup.lift N ψ hNker (show ↥E ⧸ N from x)) +
        Multiplicative.toAdd (QuotientGroup.lift N ψ hNker (show ↥E ⧸ N from y))
    rw [map_mul, toAdd_mul]
  let q : Fin 5 → Q := fun i => QuotientGroup.mk (⟨u i, hu i⟩ : ↥E)
  have hq : ∀ i, ℓ (q i) = wvec i := by
    intro i
    change Multiplicative.toAdd
      (QuotientGroup.lift N ψ hNker (QuotientGroup.mk (⟨u i, hu i⟩ : ↥E))) = wvec i
    rw [QuotientGroup.lift_mk]
    change ξ (sec12f t (u i)) = wvec i
    rw [hfu i]
    exact hξφ (wvec_even i)
  have hsq : ∀ x : Q, x * x = 1 := by
    intro x
    refine QuotientGroup.induction_on x (fun a => ?_)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact (hNmem (a * a)).2 (by simpa using sec120_sq_mem_B F hE a.2)
  have hcomm : ∀ x y : Q, x * y = y * x := by
    intro x y
    refine QuotientGroup.induction_on x (fun a => ?_)
    refine QuotientGroup.induction_on y (fun b => ?_)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine (hNmem _).2 ?_
    have h := sec120_comm_mem_B F hE (e := (b : G)⁻¹) (e' := (a : G)⁻¹)
      (E.inv_mem b.2) (E.inv_mem a.2)
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc] using h
  intro x hx hfx
  have hxE : x ∈ E := by
    have hsub : Subgroup.closure ((secB S L : Set G) ∪ {z | ∃ i j, z = u i * u j}) ≤ E := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with hyB | ⟨i, j, rfl⟩
      · exact hB_le_E hyB
      · exact E.mul_mem (hu i) (hu j)
    exact hsub hx
  let H' : Subgroup Q := Subgroup.closure {z : Q | ∃ i j, z = q i * q j}
  have hxH : (QuotientGroup.mk (⟨x, hxE⟩ : ↥E) : Q) ∈ H' := by
    let p : (y : G) →
        y ∈ Subgroup.closure ((secB S L : Set G) ∪ {z | ∃ i j, z = u i * u j}) → Prop :=
      fun y _ => ∃ hy : y ∈ E, (QuotientGroup.mk (⟨y, hy⟩ : ↥E) : Q) ∈ H'
    have hp : p x hx := by
      refine Subgroup.closure_induction (p := p) ?_ ?_ ?_ ?_ hx
      · intro y hy
        rcases hy with hyB | ⟨i, j, rfl⟩
        · refine ⟨hB_le_E hyB, ?_⟩
          have hone : (QuotientGroup.mk (⟨y, hB_le_E hyB⟩ : ↥E) : Q) = 1 := by
            rw [QuotientGroup.eq_one_iff]
            exact (hNmem _).2 hyB
          rw [hone]
          exact H'.one_mem
        · refine ⟨E.mul_mem (hu i) (hu j), ?_⟩
          have he : (⟨u i * u j, E.mul_mem (hu i) (hu j)⟩ : ↥E) =
              ⟨u i, hu i⟩ * ⟨u j, hu j⟩ := Subtype.ext rfl
          rw [he, QuotientGroup.mk_mul]
          exact Subgroup.subset_closure ⟨i, j, rfl⟩
      · refine ⟨E.one_mem, ?_⟩
        have hone : (QuotientGroup.mk (⟨(1 : G), E.one_mem⟩ : ↥E) : Q) = 1 := by
          rw [show (⟨(1 : G), E.one_mem⟩ : ↥E) = 1 from Subtype.ext rfl]
          rfl
        rw [hone]
        exact H'.one_mem
      · intro y z hy hz ihy ihz
        obtain ⟨hyE, hyH⟩ := ihy
        obtain ⟨hzE, hzH⟩ := ihz
        refine ⟨E.mul_mem hyE hzE, ?_⟩
        have he : (⟨y * z, E.mul_mem hyE hzE⟩ : ↥E) = ⟨y, hyE⟩ * ⟨z, hzE⟩ :=
          Subtype.ext rfl
        rw [he, QuotientGroup.mk_mul]
        exact H'.mul_mem hyH hzH
      · intro y hy ihy
        obtain ⟨hyE, hyH⟩ := ihy
        refine ⟨E.inv_mem hyE, ?_⟩
        have he : (⟨y⁻¹, E.inv_mem hyE⟩ : ↥E) = (⟨y, hyE⟩ : ↥E)⁻¹ :=
          Subtype.ext rfl
        rw [he, QuotientGroup.mk_inv]
        exact H'.inv_mem hyH
    obtain ⟨hyE, hyH⟩ := hp
    have heq : (⟨x, hyE⟩ : ↥E) = ⟨x, hxE⟩ := Subtype.ext rfl
    rwa [heq] at hyH
  have hfx' : ℓ (QuotientGroup.mk (⟨x, hxE⟩ : ↥E) : Q) = 0 := by
    change Multiplicative.toAdd
      (QuotientGroup.lift N ψ hNker (QuotientGroup.mk (⟨x, hxE⟩ : ↥E))) = 0
    rw [QuotientGroup.lift_mk]
    change ξ (sec12f t x) = 0
    rw [hfx, hξ0]
  have hone : (QuotientGroup.mk (⟨x, hxE⟩ : ↥E) : Q) = 1 := by
    apply sec121_closure_pairs hcomm hsq q ℓ hℓ hq
    · exact hxH
    · exact hfx'
  rw [QuotientGroup.eq_one_iff] at hone
  change (⟨x, hxE⟩ : ↥E) ∈ (secB S L).subgroupOf E at hone
  rwa [Subgroup.mem_subgroupOf] at hone

end CFSG.OddStandard.SmallF3.Omega
