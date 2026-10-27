module

public import CFSG.ClassicalInvolution.Q3.TL4AECoverF

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AECov

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr

theorem kList_twin_comm_zQ : ∃ a ∈ kList, ∃ c' ∈ kStarList, (a * c').perm = 1 ∧
    ∃ c ∈ kList, a * c * a⁻¹ * c⁻¹ = zQ := by
  decide +kernel

theorem kStarList_twin_comm_zQ : ∃ a ∈ kStarList, ∃ c' ∈ kList, (a * c').perm = 1 ∧
    ∃ c ∈ kStarList, a * c * a⁻¹ * c⁻¹ = zQ := by
  decide +kernel

variable {n : ℕ}

theorem mkQ_embed_mem_memBar (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) {a : Wr 4}
    (ha : a ∈ (bif b then kList else kStarList)) :
    mkQ n (embed (emb α h) a) ∈ memBar α h b := by
  cases b
  · exact ⟨embed (emb α h) a, ⟨a, ha, rfl⟩, rfl⟩
  · exact ⟨embed (emb α h) a, ⟨a, ha, rfl⟩, rfl⟩

theorem exists_twin_comm_zQ (b : Bool) : ∃ a ∈ (bif b then kList else kStarList),
    ∃ c' ∈ (bif !b then kList else kStarList), (a * c').perm = 1 ∧
      ∃ c ∈ (bif b then kList else kStarList), a * c * a⁻¹ * c⁻¹ = zQ := by
  cases b
  · exact kStarList_twin_comm_zQ
  · exact kList_twin_comm_zQ

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {k : ℕ}

theorem mem_commutator_of_twin (I : AEIdent P k) (hk : 5 ≤ k)
    (h8 : ∀ L ∈ P, Nat.card ↥L = 8)
    (htc : ∀ (α : Finset (Fin k)) (h : α.card = 4), ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = memBar α h true →
      (L'.subgroupOf (pSpan P)).map I.φ = memBar α h false →
      ∀ x ∈ L, ∀ y ∈ L', x * y = y * x)
    {L : Subgroup G} (hL : L ∈ P) {u : G} (hu : IsUniqueInvolution L u) :
    (⟨u, le_pSpan hL hu.mem⟩ : ↥(pSpan P)) ∈ ⁅(permHom I).ker, (⊤ : Subgroup ↥(pSpan P))⁆ := by
  obtain ⟨α, h, b, hlab⟩ := I.label L hL
  obtain ⟨L', hL', hlab'⟩ := I.label_surj α h (!b)
  have hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x := by
    cases b
    · intro x hx y hy
      exact (htc α h L' hL' L hL hlab' hlab y hy x hx).symm
    · exact htc α h L hL L' hL' hlab hlab'
  obtain ⟨a, ha, c', hc', hac', c, hc, hcz⟩ := exists_twin_comm_zQ b
  have hma : mkQ k (embed (emb α h) a) ∈ (L.subgroupOf (pSpan P)).map I.φ := by
    rw [hlab]
    exact mkQ_embed_mem_memBar α h b ha
  have hmc : mkQ k (embed (emb α h) c) ∈ (L.subgroupOf (pSpan P)).map I.φ := by
    rw [hlab]
    exact mkQ_embed_mem_memBar α h b hc
  have hmc' : mkQ k (embed (emb α h) c') ∈ (L'.subgroupOf (pSpan P)).map I.φ := by
    rw [hlab']
    exact mkQ_embed_mem_memBar α h (!b) hc'
  obtain ⟨la, hla, hlae⟩ := I.exists_of_mem_map hL hma
  obtain ⟨lc, hlc, hlce⟩ := I.exists_of_mem_map hL hmc
  obtain ⟨lc', hlc', hlc'e⟩ := I.exists_of_mem_map hL' hmc'
  set xa : ↥(pSpan P) := ⟨la, le_pSpan hL hla⟩ with hxa
  set xc : ↥(pSpan P) := ⟨lc, le_pSpan hL hlc⟩ with hxc
  set xc' : ↥(pSpan P) := ⟨lc', le_pSpan hL' hlc'⟩ with hxc'
  have hf : xa * xc' ∈ (permHom I).ker := by
    rw [mem_ker_permHom, map_mul, hlae, hlc'e, ← map_mul, ← map_mul, permQ_mkQ, embed_perm,
      hac', embedPerm_one]
  have hcc : xc' * xc = xc * xc' := Subtype.ext (hcomm lc hlc lc' hlc').symm
  have hcomm2 : xa * xc' * xc * (xa * xc')⁻¹ * xc⁻¹ = xa * xc * xa⁻¹ * xc⁻¹ := by
    calc xa * xc' * xc * (xa * xc')⁻¹ * xc⁻¹ = xa * (xc' * xc) * xc'⁻¹ * xa⁻¹ * xc⁻¹ := by group
      _ = xa * (xc * xc') * xc'⁻¹ * xa⁻¹ * xc⁻¹ := by rw [hcc]
      _ = xa * xc * xa⁻¹ * xc⁻¹ := by group
  have hmem : la * lc * la⁻¹ * lc⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem (L.mul_mem hla hlc) (L.inv_mem hla)) (L.inv_mem hlc)
  have hφ : I.φ ⟨la * lc * la⁻¹ * lc⁻¹, le_pSpan hL hmem⟩ = I.φ ⟨u, le_pSpan hL hu.mem⟩ := by
    rw [I.map_eq_zBar hk hL (h8 L hL) hlab hu]
    have e : (⟨la * lc * la⁻¹ * lc⁻¹, le_pSpan hL hmem⟩ : ↥(pSpan P)) = xa * xc * xa⁻¹ * xc⁻¹ :=
      rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hlae, hlce, ← map_inv, ← map_inv,
      ← map_mul, ← map_mul, ← map_mul, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hcz]
    rfl
  have hue : (⟨u, le_pSpan hL hu.mem⟩ : ↥(pSpan P)) = xa * xc' * xc * (xa * xc')⁻¹ * xc⁻¹ := by
    rw [hcomm2]
    exact Subtype.ext (I.injOn hk hL (h8 L hL) hlab hu.mem hmem hφ.symm)
  rw [hue, ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator hf (Subgroup.mem_top _)

theorem zSpan_le_commutator (I : AEIdent P k) (hk : 5 ≤ k) (h8 : ∀ L ∈ P, Nat.card ↥L = 8)
    (htc : ∀ (α : Finset (Fin k)) (h : α.card = 4), ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = memBar α h true →
      (L'.subgroupOf (pSpan P)).map I.φ = memBar α h false →
      ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) :
    zSpan P ≤ ⁅(permHom I).ker, (⊤ : Subgroup ↥(pSpan P))⁆ := by
  rw [zSpan, Subgroup.closure_le]
  rintro x ⟨L, hL, hxL⟩
  exact mem_commutator_of_twin I hk h8 htc hL hxL

end CFSG.ClassicalInvolution.Q3.TL4.AECov
