module

public import CFSG.CGT.PushingUpLit.ThmOne.AmbKSharp

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6

variable {L : Type} [Group L] [Finite L]

theorem eq_top_of_normal_of_omegaFourOutcomeSharp {V Y D : Subgroup L} [V.Normal]
    (hV : CFSG.Open.IsElemAbelian 2 V) (hΩ : OmegaFourOutcomeSharp V Y D) (hYD : Y ≤ D)
    (hN0 : IsPGroup 2 ↥(D ⊓ Subgroup.centralizer (V : Set L))) {N : Subgroup ↥D} [hN : N.Normal]
    (hYN : Y.subgroupOf D ≤ N) : N = ⊤ := by
  obtain ⟨hres, -, -, -, n, hn, -, -, -, -, hnat, hYDh, hne, hSL, hcard⟩ := hΩ
  have hYV : Y ≤ Subgroup.normalizer (V : Set L) := by
    rw [Subgroup.normalizer_eq_top V]
    exact le_top
  have hcard' : Nat.card ↥(@commV ↥V (commGroupOfElemAbelian hV) (autOn Y V)) = 2 ^ (3 * n) := by
    rw [← hcard, ← BHS6.map_commOn hV hYV, Subgroup.card_map_of_injective V.subtype_injective]
    rfl
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  have hNo := (@embOmega_holds ↥V (commGroupOfElemAbelian hV) _ hV2 (autOn D V) (autOn Y V) n hn
    (hnat hV) hYDh hne hSL hcard').1
  have hN₀D : N.map D.subtype ≤ D := Subgroup.map_subtype_le N
  have hN₀sub : (N.map D.subtype).subgroupOf D = N :=
    Subgroup.comap_map_eq_self_of_injective D.subtype_injective N
  have hYN₀ : Y ≤ N.map D.subtype := fun y hy => ⟨⟨y, hYD hy⟩, hYN hy, rfl⟩
  have hDN : D ≤ Subgroup.normalizer ((N.map D.subtype : Subgroup L) : Set L) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀D).mp ?_
    rw [hN₀sub]
    exact hN
  have hle : autOn (N.map D.subtype) V ≤ autOn D V := autOn_le_autOn V hN₀D
  have heq : autOn (N.map D.subtype) V = autOn D V := hNo _ (autOn_le_autOn V hYN₀) hle (by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle, ← map_ambRho V D, ← map_ambRho V]
    rintro _ ⟨d, hd, rfl⟩
    exact map_mem_normalizer_map (ambRho V) (hDN hd))
  have hfac : ∀ d ∈ D, ∃ c ∈ D ⊓ Subgroup.centralizer (V : Set L), d⁻¹ * c ∈ N.map D.subtype := by
    intro d hd
    have h1 : ambRho V d ∈ (N.map D.subtype).map (ambRho V) := by
      rw [map_ambRho V, heq, ← map_ambRho V]
      exact ⟨d, hd, rfl⟩
    obtain ⟨m, hm, hmd⟩ := h1
    have hc : d * m⁻¹ ∈ Subgroup.centralizer (V : Set L) := by
      rw [← ker_ambRho V, MonoidHom.mem_ker, map_mul, map_inv, ← hmd, mul_inv_cancel]
    refine ⟨d * m⁻¹, Subgroup.mem_inf.mpr ⟨D.mul_mem hd (D.inv_mem (hN₀D hm)), hc⟩, ?_⟩
    simpa using (N.map D.subtype).inv_mem hm
  have hp : IsPGroup 2 (↥D ⧸ N) := by
    intro q
    obtain ⟨⟨d, hd⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨c, hc, hdc⟩ := hfac d hd
    obtain ⟨k, hk⟩ := hN0 ⟨c, hc⟩
    refine ⟨k, ?_⟩
    have hq : (QuotientGroup.mk (⟨d, hd⟩ : ↥D) : ↥D ⧸ N) = QuotientGroup.mk (⟨c, hc.1⟩ : ↥D) := by
      rw [QuotientGroup.eq, ← hN₀sub]
      exact hdc
    have hc1 : (⟨c, hc.1⟩ : ↥D) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [hq, ← QuotientGroup.mk_pow, hc1, QuotientGroup.mk_one]
  have hle' : oResidualTwo ↥D ≤ N := sInf_le ⟨hN, hp⟩
  rw [hres] at hle'
  exact top_le_iff.mp hle'

theorem eq_top_of_isSubnormal_of_omegaFourOutcomeSharp {V Y D : Subgroup L} [V.Normal]
    (hV : CFSG.Open.IsElemAbelian 2 V) (hΩ : OmegaFourOutcomeSharp V Y D) (hYD : Y ≤ D)
    (hN0 : IsPGroup 2 ↥(D ⊓ Subgroup.centralizer (V : Set L))) {S : Subgroup ↥D}
    (hS : S.IsSubnormal) (hYS : Y.subgroupOf D ≤ S) : S = ⊤ := by
  induction hS with
  | top => rfl
  | step H K hHK hK hN ih =>
    have hK' : K = ⊤ := ih (hYS.trans hHK)
    subst hK'
    have hHn : H.Normal := Subgroup.normalizer_eq_top_iff.mp
      (top_le_iff.mp ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN))
    exact eq_top_of_normal_of_omegaFourOutcomeSharp hV hΩ hYD hN0 hYS

theorem normalizer_le_normalizer_of_omegaFourOutcomeSharp {V Y D : Subgroup L} [V.Normal]
    (hV : CFSG.Open.IsElemAbelian 2 V) (hΩ : OmegaFourOutcomeSharp V Y D) (hYD : Y ≤ D)
    (hDs : D.IsSubnormal) (hN0 : IsPGroup 2 ↥(D ⊓ Subgroup.centralizer (V : Set L))) :
    Subgroup.normalizer (Y : Set L) ≤ Subgroup.normalizer (D : Set L) := by
  intro g hg
  have hD's : (D.map (MulAut.conj g).toMonoidHom).IsSubnormal :=
    Subgroup.IsSubnormal.map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective hDs
  have hYD' : Y ≤ D.map (MulAut.conj g).toMonoidHom := by
    intro y hy
    have hy' : g⁻¹ * y * g ∈ Y := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) y).mp hy
    exact ⟨g⁻¹ * y * g, hYD hy', by simp [MulAut.conj_apply, mul_assoc]⟩
  have hS := eq_top_of_isSubnormal_of_omegaFourOutcomeSharp hV hΩ hYD hN0
    (hD's.subgroupOf (K := D)) (Subgroup.comap_mono hYD')
  have hDD' : D ≤ D.map (MulAut.conj g).toMonoidHom := fun d hd => by
    have h1 : (⟨d, hd⟩ : ↥D) ∈ (D.map (MulAut.conj g).toMonoidHom).subgroupOf D := by
      rw [hS]
      exact Subgroup.mem_top _
    exact h1
  have hEq : D.map (MulAut.conj g).toMonoidHom = D :=
    (Subgroup.eq_of_le_of_card_ge hDD'
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])).symm
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · intro hd
    rw [← hEq]
    exact ⟨d, hd, by simp [MulAut.conj_apply]⟩
  · intro hd
    rw [← hEq] at hd
    obtain ⟨d', hd', he⟩ := hd
    have : d' = d := by
      have he' : g * d' * g⁻¹ = g * d * g⁻¹ := by simpa [MulAut.conj_apply] using he
      simpa using he'
    rwa [← this]

end CFSG.CGT.PushingUpLit.ThmOne
