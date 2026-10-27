module

public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem map_conj_zpowers_fa (g a : G) :
    (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (g * a * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

omit [Finite G] in
private theorem map_conj_map_conj_fa (g h : G) (A : Subgroup G) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
private theorem commutator_eq_top_fa [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with
    h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact (hab ((isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)) a b)).elim
  · exact h

theorem sylow_focal_gen_mem_commutator_normalizer {p : ℕ} [Fact p.Prime] (P : Sylow p G) {x : G}
    (hxP : x ∈ (P : Subgroup G)) (hcent : ∀ g ∈ (P : Subgroup G), g * x = x * g)
    (hwc : ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x)
    {z : G} (hz : z ∈ (P : Subgroup G)) {u : G} (hu : u * z * u⁻¹ ∈ (P : Subgroup G)) :
    z * u * z⁻¹ * u⁻¹ ∈ ⁅Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G),
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G)⁆ := by
  set Nx : Subgroup G := Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) with hNx
  have hPN : ∀ g ∈ (P : Subgroup G), g ∈ Nx := by
    intro g hg
    refine Subgroup.centralizer_le_normalizer _ ?_
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (hcent g hg).symm k)).eq
  have hmap : (Subgroup.zpowers z).map (MulAut.conj u⁻¹⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    simpa [MulAut.conj_apply] using hu
  obtain ⟨c, hdec, hc⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion P
    (Subgroup.zpowers_le.mpr hz) hmap
  have hcz : c⁻¹ * z * c = u * z * u⁻¹ := by simpa using hc z (Subgroup.mem_zpowers z)
  have key : ∀ c : G,
      CFSG.RankTwoShapes.AlperinDecomposition p (P : Subgroup G) (Subgroup.zpowers z) c →
      ∀ y ∈ Subgroup.zpowers z, y⁻¹ * (c⁻¹ * y * c) ∈ ⁅Nx, Nx⁆ := by
    intro c hc
    induction hc with
    | one => intro y _; simp
    | @step c n Q _ hQ hAQ hn ih =>
      intro y hy
      have hy1 : c⁻¹ * y * c ∈ Q := hAQ ⟨y, hy, by simp [MulAut.conj_apply]⟩
      have hQP : Q ≤ (P : Subgroup G) := hQ.1
      have hxQ : x ∈ Q := by
        refine hQ.2.2.1 (Subgroup.mem_inf.mpr ⟨?_, hxP⟩)
        intro h hh
        exact hcent h (hQP hh)
      have hnxP : n * x * n⁻¹ ∈ (P : Subgroup G) :=
        hQP ((Subgroup.mem_normalizer_iff.mp hn x).mp hxQ)
      have hle : (Subgroup.zpowers x).map (MulAut.conj n).toMonoidHom ≤ (P : Subgroup G) := by
        rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
        simpa [MulAut.conj_apply] using hnxP
      have hnN : n ∈ Nx := Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hwc n hle)
      have hy1N : c⁻¹ * y * c ∈ Nx := hPN _ (hQP hy1)
      have hcomm : ⁅(c⁻¹ * y * c)⁻¹, n⁻¹⁆ ∈ ⁅Nx, Nx⁆ :=
        commutator_mem_commutator (Nx.inv_mem hy1N) (Nx.inv_mem hnN)
      have hprod : y⁻¹ * ((c * n)⁻¹ * y * (c * n)) =
          (y⁻¹ * (c⁻¹ * y * c)) * ⁅(c⁻¹ * y * c)⁻¹, n⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [hprod]
      exact Subgroup.mul_mem _ (ih y hy) hcomm
  have h1 := key c hdec z⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers z))
  have hcz' : c⁻¹ * z⁻¹ * c = u * z⁻¹ * u⁻¹ := by
    calc c⁻¹ * z⁻¹ * c = (c⁻¹ * z * c)⁻¹ := by group
      _ = (u * z * u⁻¹)⁻¹ := by rw [hcz]
      _ = u * z⁻¹ * u⁻¹ := by group
  rw [inv_inv, hcz'] at h1
  have hfin : z * (u * z⁻¹ * u⁻¹) = z * u * z⁻¹ * u⁻¹ := by group
  rwa [hfin] at h1

theorem sylow_le_commutator_normalizer_of_simple [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {x : G}
    (hxP : x ∈ (P : Subgroup G)) (hcent : ∀ g ∈ (P : Subgroup G), g * x = x * g)
    (hwc : ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x) :
    (P : Subgroup G) ≤ ⁅Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G),
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G)⁆ := by
  have hfoc := Subgroup.commutator_inf_eq_focalSubgroup P
  rw [commutator_eq_top_fa hnonab, top_inf_eq] at hfoc
  rw [hfoc, Subgroup.focalSubgroup_def, Subgroup.closure_le]
  rintro _ ⟨hgP, z, hzP, u, rfl⟩
  have hux : u * z * u⁻¹ ∈ (P : Subgroup G) := by
    have h := (P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem hzP) hgP
    rw [commutatorElement_def] at h
    simpa [mul_assoc] using (P : Subgroup G).inv_mem h
  exact sylow_focal_gen_mem_commutator_normalizer P hxP hcent hwc hzP hux

theorem exists_mem_normalizer_swap {p : ℕ} [Fact p.Prime] (P : Sylow p G) {x e h : G}
    (hPx : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    (hPe : (P : Subgroup G) ≤ Subgroup.centralizer ({e} : Set G))
    (hh : (Subgroup.zpowers x).map (MulAut.conj h).toMonoidHom = Subgroup.zpowers e) :
    ∃ g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G),
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers e := by
  have hhx : h * x * h⁻¹ ∈ Subgroup.zpowers e := by
    rw [← hh]
    exact ⟨x, Subgroup.mem_zpowers x, by simp [MulAut.conj_apply]⟩
  have hPhx : ∀ s ∈ (P : Subgroup G), s * (h * x * h⁻¹) = (h * x * h⁻¹) * s := by
    intro s hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hhx
    rw [← hk]
    have hse : Commute s e := Subgroup.mem_centralizer_singleton_iff.mp (hPe hs)
    exact (hse.zpow_right k).eq
  have hB : (P : Subgroup G).map (MulAut.conj h⁻¹).toMonoidHom ≤
      Subgroup.centralizer ({x} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show (h⁻¹ * s * h⁻¹⁻¹) * x = x * (h⁻¹ * s * h⁻¹⁻¹)
    have hss := hPhx s hs
    calc (h⁻¹ * s * h⁻¹⁻¹) * x = h⁻¹ * (s * (h * x * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x * h⁻¹) * s) * h := by rw [hss]
      _ = x * (h⁻¹ * s * h⁻¹⁻¹) := by group
  have hS : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup G)
      (Subgroup.centralizer ({x} : Set G)) :=
    ⟨P.subtype hPx, by
      rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr hPx⟩
  have hBp : IsPGroup p ((P : Subgroup G).map (MulAut.conj h⁻¹).toMonoidHom) :=
    P.isPGroup'.map _
  obtain ⟨k, hkC, hk⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.exists_conj_le_of_isSylowOf hS hB hBp
  have hkx : k * x = x * k := Subgroup.mem_centralizer_singleton_iff.mp hkC
  have heq : (P : Subgroup G).map (MulAut.conj (k * h⁻¹)).toMonoidHom = (P : Subgroup G) := by
    rw [← map_conj_map_conj_fa]
    refine Subgroup.eq_of_le_of_card_ge hk ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective,
      Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective]
  have hnorm : k * h⁻¹ ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  refine ⟨(k * h⁻¹)⁻¹, Subgroup.inv_mem _ hnorm, ?_⟩
  rw [← hh, map_conj_zpowers_fa, map_conj_zpowers_fa]
  congr 1
  have hkx' : k⁻¹ * x * k = x := by
    calc k⁻¹ * x * k = k⁻¹ * (x * k) := by group
      _ = k⁻¹ * (k * x) := by rw [hkx]
      _ = x := by group
  calc (k * h⁻¹)⁻¹ * x * (k * h⁻¹)⁻¹⁻¹ = h * (k⁻¹ * x * k) * h⁻¹ := by group
    _ = h * x * h⁻¹ := by rw [hkx']

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
