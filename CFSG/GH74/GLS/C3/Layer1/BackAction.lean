module

public import CFSG.GH74.GLS.C3.Layer1.Back91Setup
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.U1a
open CFSG.GH74.GLS.C3.Layer1.Back.Setup91 (mem_pPrimeCoreOf_iff)
open scoped commutatorElement

variable {G : Type} [Group G] {L M : Subgroup G}

theorem inducedQuotAut_mk (K : Subgroup G) (N : Subgroup ↥K) [N.Characteristic]
    (x : normalizer (K : Set G)) (k : ↥K) :
    inducedQuotAut K N x (QuotientGroup.mk k) =
      QuotientGroup.mk ⟨(x : G) * k * (x : G)⁻¹, (mem_normalizer_iff.1 x.2 k).1 k.2⟩ :=
  rfl

@[expose] noncomputable def actHom (hLM : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) :
    ↥M →* MulAut (kBar L) where
  toFun m := inducedQuotAut L (pPrimeCore 2 ↥L) ⟨m, mem_normalizer_of_norm hLM m.2⟩
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with | H l => ?_
    rw [inducedQuotAut_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    simp
  map_mul' m n := by
    ext x
    induction x using QuotientGroup.induction_on with | H l => ?_
    rw [MulAut.mul_apply, inducedQuotAut_mk, inducedQuotAut_mk, inducedQuotAut_mk]
    congr 1
    apply Subtype.ext
    simp [mul_assoc]

theorem actHom_mk (hLM : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (m : ↥M) (l : ↥L) :
    actHom hLM m (QuotientGroup.mk l) =
      QuotientGroup.mk ⟨(m : G) * l * (m : G)⁻¹, hLM m m.2 l l.2⟩ :=
  rfl

theorem actHom_eq_one_iff_commutator_mem (hLM : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (m : ↥M) :
    actHom hLM m = 1 ↔ ∀ k ∈ L, ⁅k, (m : G)⁆ ∈ pPrimeCoreOf 2 L := by
  have hdiv : ∀ (k : ↥L), (k / ⟨(m : G) * k * (m : G)⁻¹, hLM m m.2 k k.2⟩ : ↥L) =
      ⟨⁅(k : G), (m : G)⁆, by
        have h1 : ⁅(k : G), (m : G)⁆ = (k : G) * ((m : G) * (k : G)⁻¹ * (m : G)⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [h1]
        exact L.mul_mem k.2 (hLM m m.2 _ (L.inv_mem k.2))⟩ := by
    intro k
    apply Subtype.ext
    simp [commutatorElement_def, div_eq_mul_inv, mul_assoc]
  constructor
  · intro h k hk
    have h1 := actHom_mk hLM m ⟨k, hk⟩
    rw [h, MulAut.one_apply, QuotientGroup.eq_iff_div_mem, hdiv] at h1
    exact mem_pPrimeCoreOf_iff.2 ⟨_, h1⟩
  · intro h
    ext x
    induction x using QuotientGroup.induction_on with | H l => ?_
    rw [actHom_mk, MulAut.one_apply, eq_comm, QuotientGroup.eq_iff_div_mem, hdiv]
    obtain ⟨_, hc⟩ := mem_pPrimeCoreOf_iff.1 (h l l.2)
    exact hc

theorem actHom_ker (hLM : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) :
    (actHom hLM).ker = (CMK M L).subgroupOf M := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_CMK_iff]
  constructor
  · intro h
    exact ⟨m.2, mem_normalizer_of_norm hLM m.2, mem_normalizer_pPrimeCoreOf hLM m.2,
      (actHom_eq_one_iff_commutator_mem hLM m).1 h⟩
  · rintro ⟨-, -, -, h⟩
    exact (actHom_eq_one_iff_commutator_mem hLM m).2 h

theorem actHom_of_mem (hLM : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) {l : G} (hl : l ∈ L)
    (hlM : l ∈ M) :
    actHom hLM ⟨l, hlM⟩ = MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : kBar L) := by
  ext x
  induction x using QuotientGroup.induction_on with | H k => ?_
  rw [actHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

theorem lemma113d_ne6 {G : Type} [Group G] {K M : Subgroup G} (hKM : K ≤ M)
    (hnorm : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : kBar K ≃* alternatingGroup (Fin n)) :
    ∃ ψ : ↥M →* Equiv.Perm (Fin n), ψ.ker = (CMK M K).subgroupOf M := by
  have _ := hKM
  let c : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)
  refine ⟨c.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp (actHom hnorm)), ?_⟩
  rw [← actHom_ker hnorm]
  ext m
  simp [MonoidHom.mem_ker]

end CFSG.GH74.GLS.C3.Layer1.Back
