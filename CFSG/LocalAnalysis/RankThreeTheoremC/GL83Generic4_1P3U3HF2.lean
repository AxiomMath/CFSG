module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3HF
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Aux
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Nongeneration
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Abel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem u3_hF {P : Sylow 3 G} {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsU3Normal M x J)
    (hgen : IsGenericPoint 3 P M x) (hR1 : U3Prop34 3 P J x) :
    ∀ F : Subgroup G, IsPGroup 3 F → u3VPlane (P : Subgroup G) J x ≤ F → F ≤ M →
      CFSG.Open.pRank 3 F ≤ 2 → IsMulCommutative F ∧ ∀ g : G,
        (zpowers x).map (MulAut.conj g).toMonoidHom ≤ F →
          (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro F hFp hUF _ hFrk
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := hgen
  obtain ⟨hPC, -, hexp, -, ⟨Z, hZc, hxZ, hZcomm, hTZ, hPeq⟩, hwc⟩ := hR1
  have hxF : x ∈ F := hUF (mem_sup_right (mem_zpowers x))
  obtain ⟨Q, hFQ⟩ := hFp.exists_le_sylow
  refine ⟨?_, fun g hg => weakClosed_sylow3 hwc Q (hFQ hxF) g (hg.trans hFQ)⟩
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P Q
  have h : ((c • P : Sylow 3 G) : Subgroup G) = (Q : Subgroup G) := by rw [hc]
  rw [Sylow.coe_subgroup_smul] at h
  have hmem : ∀ y ∈ (Q : Subgroup G), c⁻¹ * y * c ∈ (P : Subgroup G) := by
    intro y hy
    rw [← h, Subgroup.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have : c⁻¹ * (c * z * c⁻¹) * c = z := by group
    show c⁻¹ * (c * z * c⁻¹) * c ∈ (P : Subgroup G)
    rw [this]
    exact hz
  set F' : Subgroup G := F.map (MulAut.conj c⁻¹).toMonoidHom with hF'
  have hF'mem : ∀ f ∈ F, c⁻¹ * f * c ∈ F' := fun f hf => ⟨f, hf, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hF'P : F' ≤ (P : Subgroup G) := by
    rintro _ ⟨f, hf, rfl⟩
    simpa [MulAut.conj_apply] using hmem f (hFQ hf)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxF' : x ∈ F' := by
    have h2 : (zpowers x).map (MulAut.conj c⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
      rintro _ ⟨z, hz, rfl⟩
      have hz' : z ∈ (Q : Subgroup G) := hFQ (zpowers_le.mpr hxF hz)
      simpa [MulAut.conj_apply] using hmem z hz'
    have e2 := hwc _ h2
    have hx'mem : c⁻¹ * x * c ∈ zpowers x := by
      rw [← e2]
      exact ⟨x, mem_zpowers x, by simp⟩
    have hx'1 : c⁻¹ * x * c ≠ 1 := fun h1 => hx1 (by
      have : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      rw [this, h1]; group)
    have hzp := p34_zpowers_eq_of_mem hxo hx'mem hx'1
    have : x ∈ zpowers (c⁻¹ * x * c) := by rw [hzp]; exact mem_zpowers x
    exact zpowers_le.mpr (hF'mem x hxF) this
  have hF'p : IsPGroup 3 F' := hFp.map _
  have hF'rk : CFSG.Open.pRank 3 F' ≤ 2 := by
    rw [hF', CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three _
      (MulAut.conj c⁻¹).injective]
    exact hFrk
  set T : Subgroup G := (P : Subgroup G) ⊓ J with hT
  have hxT : x ∉ T := fun hxT => hx1 (by
    have : x ∈ T ⊓ Z := ⟨hxT, hxZ⟩
    rwa [hTZ, mem_bot] at this)
  have hTx : ∀ t ∈ T, t * x = x * t := fun t ht => mem_centralizer_singleton_iff.mp (hPC ht.1)
  have hZP : Z ≤ (P : Subgroup G) := hPeq ▸ le_sup_right
  have hF'ab : IsMulCommutative F' := by
    refine u3abel_isMulCommutative (P.isPGroup'.to_le hZP) hZc hZcomm (hPeq ▸ hF'P) ?_
    refine u3hf_inf_central hF'p (fun f hf t ht => ⟨?_, ?_⟩) ?_
    · exact (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem (hF'P hf) ht.1)
        ((P : Subgroup G).inv_mem (hF'P hf))
    · exact (mem_normalizer_iff.mp (hJ.centralizer_le (hPC (hF'P hf))) t).mp ht.2
    · exact fun S hS => u3hf_inf_card_le hx3 hxF' hxT hTx (fun t ht => hexp t ht) hF'rk S hS
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  show (a : G) * b = b * a
  have hcomm := congrArg Subtype.val (hF'ab.is_comm.comm ⟨c⁻¹ * (a : G) * c, hF'mem a a.2⟩
    ⟨c⁻¹ * (b : G) * c, hF'mem b b.2⟩)
  have h1 : c⁻¹ * ((a : G) * b) * c = c⁻¹ * ((b : G) * a) * c := by
    calc c⁻¹ * ((a : G) * b) * c = (c⁻¹ * (a : G) * c) * (c⁻¹ * (b : G) * c) := by group
      _ = (c⁻¹ * (b : G) * c) * (c⁻¹ * (a : G) * c) := hcomm
      _ = c⁻¹ * ((b : G) * a) * c := by group
  have h2 := (MulAut.conj c⁻¹).injective (by simpa [MulAut.conj_apply] using h1)
  exact h2

end CFSG.LocalAnalysis.RankThreeTheoremC
