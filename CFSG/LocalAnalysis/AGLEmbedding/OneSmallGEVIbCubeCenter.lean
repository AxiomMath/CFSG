module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbU33Data
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCubeBasic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbCubeConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem toThreeData (hc : D1IbCubeConfig p P M H R Rbar K z) :
    D1IbCubeThreeData p P M H R Rbar K z :=
  ⟨hc.data, hc.elt, hc.dec, hc.exp, hc.card_T⟩

theorem card_Z (hc : D1IbCubeConfig p P M H R Rbar K z) (hShape : KFactSmallSylowShape) :
    Nat.card (centerOf (d1LiftX p H R K)) = p :=
  hc.toThreeData.card_Z hShape

theorem commute_z (hc : D1IbCubeConfig p P M H R Rbar K z) {r : G} (hr : r ∈ R) :
    r * z = z * r :=
  hc.toThreeData.commute_z hr

theorem centerOf_le_centralizer (hc : D1IbCubeConfig p P M H R Rbar K z) {c : G}
    (hcZ : c ∈ centerOf (d1LiftX p H R K)) {r : G} (hr : r ∈ R) : c * r = r * c :=
  hc.toThreeData.centerOf_le_centralizer hcZ hr

theorem mem_centerOf_of_comm (_hc : D1IbCubeConfig p P M H R Rbar K z) {c : G}
    (hcT : c ∈ d1LiftX p H R K) (hcR : ∀ r ∈ R, c * r = r * c) :
    c ∈ centerOf (d1LiftX p H R K) :=
  _hc.toThreeData.mem_centerOf_of_comm hcT hcR

theorem commutator_le (hc : D1IbCubeConfig p P M H R Rbar K z) :
    ⁅R, R⁆ ≤ d1LiftX p H R K := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨t, ht, i, rfl⟩ := hc.dec a ha
  obtain ⟨s, hs, j, rfl⟩ := hc.dec b hb
  have htz : Commute t (z ^ j) := Commute.pow_right (hc.commute_z (d1LiftX_le p H R K ht)) j
  have hsz : Commute s (z ^ i) := Commute.pow_right (hc.commute_z (d1LiftX_le p H R K hs)) i
  rw [commutatorElement_def]
  have hzz : Commute (z ^ i) (z ^ j) := Commute.pow_pow_self z i j
  have h1 : t * z ^ i * (s * z ^ j) * (t * z ^ i)⁻¹ * (s * z ^ j)⁻¹ = t * s * t⁻¹ * s⁻¹ := by
    calc t * z ^ i * (s * z ^ j) * (t * z ^ i)⁻¹ * (s * z ^ j)⁻¹
        = t * (z ^ i * s) * z ^ j * (z ^ i)⁻¹ * t⁻¹ * (z ^ j)⁻¹ * s⁻¹ := by group
      _ = t * (s * z ^ i) * z ^ j * (z ^ i)⁻¹ * t⁻¹ * (z ^ j)⁻¹ * s⁻¹ := by rw [hsz.eq]
      _ = t * s * (z ^ i * z ^ j * (z ^ i)⁻¹) * t⁻¹ * (z ^ j)⁻¹ * s⁻¹ := by group
      _ = t * s * z ^ j * t⁻¹ * (z ^ j)⁻¹ * s⁻¹ := by rw [hzz.eq]; group
      _ = t * s * (z ^ j * t⁻¹) * (z ^ j)⁻¹ * s⁻¹ := by group
      _ = t * s * (t⁻¹ * z ^ j) * (z ^ j)⁻¹ * s⁻¹ := by rw [(htz.inv_left).eq.symm]
      _ = t * s * t⁻¹ * s⁻¹ := by group
  rw [h1]
  exact (d1LiftX p H R K).mul_mem ((d1LiftX p H R K).mul_mem
    ((d1LiftX p H R K).mul_mem ht hs) ((d1LiftX p H R K).inv_mem ht))
    ((d1LiftX p H R K).inv_mem hs)

theorem centerOf_le_commutator (hc : D1IbCubeConfig p P M H R Rbar K z)
    (hShape : KFactSmallSylowShape) : centerOf (d1LiftX p H R K) ≤ ⁅R, R⁆ :=
  (hc.toThreeData.centerOf_le_commutator_self hShape).trans
    (Subgroup.commutator_mono (d1LiftX_le p H R K) (d1LiftX_le p H R K))

theorem conj_not_mem (hc : D1IbCubeConfig p P M H R Rbar K z) (hShape : KFactSmallSylowShape)
    {x : G} (hx : x ∈ Subgroup.normalizer (R : Set G)) : x * z * x⁻¹ ∉ d1LiftX p H R K := by
  intro hw
  have hwR : ∀ r ∈ R, x * z * x⁻¹ * r = r * (x * z * x⁻¹) := by
    intro r hr
    have hr' : x⁻¹ * r * x ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) r).mp hr
      simpa using this
    have h1 := hc.commute_z hr'
    calc x * z * x⁻¹ * r = x * (z * (x⁻¹ * r * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * r * x) * z) * x⁻¹ := by rw [h1]
      _ = r * (x * z * x⁻¹) := by group
  have hwZ := hc.mem_centerOf_of_comm hw hwR
  have hwC := hc.centerOf_le_commutator hShape hwZ
  have hmap : (⁅R, R⁆).map (MulAut.conj x⁻¹).toMonoidHom = ⁅R, R⁆ := by
    have hR : R.map (MulAut.conj x⁻¹).toMonoidHom = R := by
      refine le_antisymm ?_ fun r hr => ⟨x * r * x⁻¹, ?_, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
      · rintro _ ⟨r, hr, rfl⟩
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) r).mp hr
        simpa [MulAut.conj_apply] using this
      · exact (Subgroup.mem_normalizer_iff.mp hx r).mp hr
    rw [Subgroup.map_commutator, hR]
  have hz : z ∈ ⁅R, R⁆ := by
    rw [← hmap]
    exact ⟨_, hwC, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  exact hc.card_d1LiftX.2 (hc.commutator_le hz)

theorem elem_sup_zpowers (hc : D1IbCubeConfig p P M H R Rbar K z) (hShape : KFactSmallSylowShape)
    {t : G} (ht : t ∈ d1LiftX p H R K) (htZ : t ∉ centerOf (d1LiftX p H R K)) :
    centerOf (d1LiftX p H R K) ⊔ Subgroup.zpowers t ≤ d1LiftX p H R K ∧
      IsElemAbelian p (centerOf (d1LiftX p H R K) ⊔ Subgroup.zpowers t) ∧
      Nat.card (centerOf (d1LiftX p H R K) ⊔ Subgroup.zpowers t : Subgroup G) = p ^ 2 :=
  hc.toThreeData.elem_sup_zpowers hShape ht htZ

end D1IbCubeConfig

end CFSG.AGLEmbedding
