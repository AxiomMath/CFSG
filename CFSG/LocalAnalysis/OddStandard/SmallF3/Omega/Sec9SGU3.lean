module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGU1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGU2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGD1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STOrth
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem projOrthToProjSim_projSimAct_aux (δ : ProjSim Q) (y : ProjOrth Q) :
    projOrthToProjSim Q (projSimAct Q δ y) = δ * projOrthToProjSim Q y * δ⁻¹ := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective δ
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
  change QuotientGroup.mk (orthToSim Q (simAct Q γ t)) =
    QuotientGroup.mk γ * QuotientGroup.mk (orthToSim Q t) * (QuotientGroup.mk γ)⁻¹
  rw [sec9u_orthToSim_simAct, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]

theorem sec9u_simInOmegaStar_conj (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (δ : ProjSim Q) {f : ProjSim Q}
    (hf : SimInOmegaStar hQ f) : SimInOmegaStar hQ (δ * f * δ⁻¹) := by
  obtain ⟨y, hy, rfl⟩ := hf
  exact ⟨projSimAct Q δ y, ff_projSimAct_mem_omegaProj hQ h2 δ hy,
    projOrthToProjSim_projSimAct_aux δ y⟩

theorem sec9u_exists_conj_cent (hQ : Q.Nondegenerate) (h6 : Module.finrank (ZMod 3) V = 6)
    (F : Subgroup (ProjSim Q)) (hF16 : Nat.card F = 2 ^ 4)
    (hlift : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f ∧ 2 ≤ invDim t ∧
      invDim t ≤ 4)
    {x : ProjSim Q} (hx : SimHasDim x 3) :
    ∃ δ : ProjSim Q, ∀ f ∈ F, x * (δ * f * δ⁻¹) = (δ * f * δ⁻¹) * x := by
  classical
  obtain ⟨b, hb⟩ := sec9t_exists_evenFrame hQ h6 F hF16 hlift
  have hn : 3 ≤ Module.finrank (ZMod 3) V := by rw [h6]; norm_num
  have hpol : ∀ i j : Fin (Module.finrank (ZMod 3) V), i ≠ j →
      QuadraticMap.polar Q (b i) (b j) = 0 :=
    fun i j hij => IsEvenFrame.polar_eq_zero hb hn hij
  let emb : Fin 3 ↪ Fin (Module.finrank (ZMod 3) V) :=
    ⟨fun k => ⟨k.val, lt_of_lt_of_le k.isLt hn⟩,
      fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
  let T : Finset (Fin (Module.finrank (ZMod 3) V)) := Finset.univ.map emb
  have hTcard : T.card = 3 := by
    show (Finset.univ.map emb).card = 3
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  obtain ⟨g, hg⟩ := sec9u_exists_diag hpol T
  have hgg : g * g = 1 := sec9g_mul_self_diag hg
  have hgdim : invDim g = 3 := by rw [sec9g_invDim_diag hg, hTcard]
  let y : ProjSim Q := phiSim Q g
  have hy : SimHasDim y 3 := ⟨g, hgg, hgdim, rfl⟩
  obtain ⟨δ, hδ⟩ := sec9u_conj_dim3 hQ h6 hx hy
  refine ⟨δ, fun f hf => ?_⟩
  have hyf : y * f = f * y := by
    obtain ⟨fl, hflmem, hflphi⟩ : ∃ fl ∈ F.comap (phiSim Q), phiSim Q fl = f := by
      by_cases hf1 : f = 1
      · exact ⟨1, by rw [Subgroup.mem_comap, map_one]; exact F.one_mem, by rw [map_one, hf1]⟩
      · obtain ⟨t, -, ht, -, -⟩ := hlift f hf hf1
        exact ⟨t, Subgroup.mem_comap.mpr (by rw [ht]; exact hf), ht⟩
    obtain ⟨S, -, hflact⟩ := (IsEvenFrame.mem_iff hb).mp hflmem
    have heq : g * fl = fl * g := by
      apply Subtype.ext
      apply b.ext'
      intro i
      have hsymm : symmDiff S T = symmDiff T S := symmDiff_comm S T
      rw [sec9g_mul_diag hg hflact i, sec9g_mul_diag hflact hg i, hsymm]
    have hphi := congrArg (phiSim Q) heq
    show phiSim Q g * f = f * phiSim Q g
    simpa only [map_mul, hflphi] using hphi
  calc x * (δ * f * δ⁻¹) = (δ * y * δ⁻¹) * (δ * f * δ⁻¹) := by rw [hδ]
    _ = δ * (y * f) * δ⁻¹ := by group
    _ = δ * (f * y) * δ⁻¹ := by rw [hyf]
    _ = (δ * f * δ⁻¹) * (δ * y * δ⁻¹) := by group
    _ = (δ * f * δ⁻¹) * x := by rw [hδ]

end CFSG.OddStandard.SmallF3.Omega
