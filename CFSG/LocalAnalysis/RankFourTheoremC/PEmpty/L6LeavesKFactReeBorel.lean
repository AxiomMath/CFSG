module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)

theorem exists_reeG2_of_isReeIndex' {d : TauCeti.LieTypeIndex} (h : IsReeIndex d) :
    ∃ a, d = .reeG2 a := by
  cases d <;> first | exact ⟨_, rfl⟩ | exact False.elim h

theorem subgroupOf_normalizer_inf {A : Type} [Group A] {L E : Subgroup A} (hE : E ≤ L) :
    (normalizer (E : Set A) ⊓ L).subgroupOf L =
      normalizer ((E.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hE]
  exact Subgroup.inf_subgroupOf_right _ _

theorem kFactReeBorel_holds :
    KFactReeBorel := by
  intro A _ _ L E hL hE
  obtain ⟨i, hi, ⟨e⟩⟩ := hL
  cases i with
  | lie d =>
    have hd : IsReeIndex d.1 := hi
    obtain ⟨m, hm⟩ := exists_reeG2_of_isReeIndex' hd
    have hRee : CFSG.AGLEmbedding.IsReeGTwoIndex 3 d := ⟨rfl, m, hm⟩
    obtain ⟨Q, hQ⟩ := hE.exists_sylow_eq_subgroupOf
    have hcoat := CFSG.AGLEmbedding.kFactReeBorelMaximal ↥L d hRee ⟨e⟩ Q
    have hsolv := CFSG.AGLEmbedding.kFactReeSylowNormalizerSolvable ↥L d hRee ⟨e⟩ Q
    have hNQ : normalizer ((Q : Subgroup ↥L) : Set ↥L) =
        (normalizer (E : Set A) ⊓ L).subgroupOf L := by
      rw [hQ]
      exact (subgroupOf_normalizer_inf hE.le).symm
    refine ⟨?_, ?_⟩
    ·
      let Nsub : Subgroup ↥L := (normalizer (E : Set A) ⊓ L).subgroupOf L
      let g : ↥Nsub →* MulAut ↥L := (MulAut.conj : ↥L →* MulAut ↥L).comp Nsub.subtype
      have hrange : Group.IsSolvable ↥g.range := by
        refine hsolv g.range ?_
        rintro α ⟨n, rfl⟩
        have hn : (n : ↥L) ∈ normalizer ((Q : Subgroup ↥L) : Set ↥L) := by
          rw [hNQ]
          exact n.2
        have hn' := Subgroup.mem_normalizer_iff.mp hn
        have hn'' := Subgroup.mem_normalizer_iff.mp (inv_mem hn)
        ext x
        rw [Subgroup.mem_map]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact (hn' y).mp hy
        · intro hx
          refine ⟨(n : ↥L)⁻¹ * x * (n : ↥L), ?_, ?_⟩
          · have := (hn'' x).mp hx
            simpa using this
          · simp [g]
            group
      have hker : Group.IsSolvable ↥g.ker := by
        refine Group.isSolvable_of_comm ?_
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        have ha' : ∀ x : ↥L, (a : ↥L) * x * (a : ↥L)⁻¹ = x := fun x => by
          have := congrArg (fun f : MulAut ↥L => f x) ha
          simpa [g] using this
        have hb' : ∀ x : ↥L, (b : ↥L) * x * (b : ↥L)⁻¹ = x := fun x => by
          have := congrArg (fun f : MulAut ↥L => f x) hb
          simpa [g] using this
        apply Subtype.ext
        apply Subtype.ext
        have h1 := ha' (b : ↥L)
        calc ((a : ↥L) * (b : ↥L) : ↥L) = (a : ↥L) * (b : ↥L) * (a : ↥L)⁻¹ * (a : ↥L) := by group
          _ = (b : ↥L) * (a : ↥L) := by rw [h1]
      have hNsub : Group.IsSolvable ↥Nsub :=
        Group.isSolvable_of_ker_le_range (g.ker.subtype) g.rangeRestrict (by
          rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
      let eN := Subgroup.subgroupOfEquivOfLe
        (inf_le_right : normalizer (E : Set A) ⊓ L ≤ L)
      exact Group.isSolvable_of_isSolvable_injective (f := eN.symm.toMonoidHom) eN.symm.injective
    · intro J hNJ hJL
      have h1 : normalizer ((Q : Subgroup ↥L) : Set ↥L) ≤ J.subgroupOf L := by
        rw [hNQ]
        intro g hg
        exact hNJ hg
      rcases h1.eq_or_lt with h2 | h2
      · left
        have h3 : (normalizer (E : Set A) ⊓ L).subgroupOf L = J.subgroupOf L := hNQ.symm.trans h2
        have h4 := Subgroup.subgroupOf_inj.mp h3
        rw [inf_eq_left.mpr (inf_le_right : normalizer (E : Set A) ⊓ L ≤ L),
          inf_eq_left.mpr hJL] at h4
        exact h4.symm
      · right
        have h3 : J.subgroupOf L = ⊤ := hcoat.2 _ h2
        exact le_antisymm hJL (Subgroup.subgroupOf_eq_top.mp h3)
  | cyclic q hq => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | sporadic s => exact False.elim hi

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
