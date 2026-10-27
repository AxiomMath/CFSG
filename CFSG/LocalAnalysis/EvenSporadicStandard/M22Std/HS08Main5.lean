module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Main4
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Aut

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

theorem hs08_hinv
    (hc : CoverSetting L t) [Group.IsPerfect L]
    (e : L ⧸ center L ≃* Carrier .M22) (hq : IsSporadic (L ⧸ center L) .M22)
    (x : ↥(centralizer ({t} : Set G)))
    (hxin : hs08PiOf hc e x ∈ innerImage (Carrier .M22) ⊤) (hx1 : hs08PiOf hc e x ≠ 1)
    (hxsq : hs08PiOf hc e x * hs08PiOf hc e x = 1) {u : G} (huL : u ∈ L) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hut : u ≠ t) :
    ∃ c ∈ L, c * u * c⁻¹ = (x : G) ∨ c * u * c⁻¹ = (x : G) * t := by
  have hcov := hc.isM22Cover hq
  have hinj := hs08_conj_injective
  have hLH := hc.le_centralizer
  have hxL : (x : G) ∈ L := (hs08PiOf_inner_iff hc e x).1 hxin
  set l : L := ⟨(x : G), hxL⟩ with hl
  have hxl : x = ⟨(l : G), hLH l.2⟩ := Subtype.ext rfl
  have hπ : hs08PiOf hc e x = MulAut.conj (e (l : L ⧸ center L)) := by
    rw [hxl]; exact hs08PiOf_of_mem hc e l
  have h1 : e (l : L ⧸ center L) * e (l : L ⧸ center L) = 1 := by
    apply hinj
    rw [hπ] at hxsq
    rw [map_mul, map_one]
    exact hxsq
  have h2 : (l : L ⧸ center L) * (l : L ⧸ center L) = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    exact h1
  have hl1 : (l : L ⧸ center L) ≠ 1 := by
    intro h3
    apply hx1
    rw [hπ, h3, map_one, map_one]
  have hlord : orderOf (l : L ⧸ center L) = 2 := orderOf_eq_prime (by rw [sq]; exact h2) hl1
  set v : L := ⟨u, huL⟩ with hv
  have hv2 : (v : L ⧸ center L) * (v : L ⧸ center L) = 1 := by
    rw [← QuotientGroup.mk_mul, show v * v = 1 from Subtype.ext hu2]
    rfl
  have hv1 : (v : L ⧸ center L) ≠ 1 := by
    intro h3
    rcases hcov.eq_one_or_eq_t_of_mk_eq_one h3 with h4 | h4
    · exact hu1 (congrArg Subtype.val h4)
    · exact hut (congrArg Subtype.val h4)
  have hvord : orderOf (v : L ⧸ center L) = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
  obtain ⟨cb, hcb⟩ := hcov.involution_conj hvord hlord
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cb
  have hmk : ((c * v * c⁻¹ : L) : L ⧸ center L) = (l : L ⧸ center L) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hcb.symm
  refine ⟨(c : G), c.2, ?_⟩
  rcases hcov.eq_or_eq_mul_t_of_mk_eq hmk with h4 | h4
  · exact Or.inl (congrArg Subtype.val h4)
  · exact Or.inr (congrArg Subtype.val h4)

theorem hs08_isolated_main
    [Finite G] [Group.IsPerfect L]
    (hc : CoverSetting L t) (e : L ⧸ center L ≃* Carrier .M22)
    (hq : IsSporadic (L ⧸ center L) .M22) {y : G} (hy : y ∈ centralizer ({t} : Set G))
    (hyL : y ∉ L) (hy2 : y * y = 1) :
    ∀ g : G, g * t * g⁻¹ ∈ centralizer ({t} : Set G) → g * t * g⁻¹ = t :=
  MainCtx.isolated
    { π := hs08PiOf hc e
      hπ := hs08_piData hc e hq hy hyL hy2
      A := autHyp_pinned
      hL := hs08PiOf_inner_iff hc e
      t_mem := hc.t_mem
      hinv := fun x hxin hx1 hxsq _ huL hu2 hu1 hut =>
        hs08_hinv hc e hq x hxin hx1 hxsq huL hu2 hu1 hut }

end CFSG.EvenSporadicStandard.M22Std
