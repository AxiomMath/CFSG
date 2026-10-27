module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndCfg
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.MinimalMod
public import CFSG.CGT.PushingUpLit.CGT6X.End3Mod
public import CFSG.CGT.PushingUpLit.CGT6X.K7aBridge

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End3

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.CGT6
open scoped commutatorElement

section Conj

variable {M : Type*} [Group M]

@[expose] def conjOn (L : Subgroup M) (t : M) (ht : t ∈ Subgroup.normalizer (L : Set M)) :
    MulAut ↥L where
  toFun x := ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht x).mp x.2⟩
  invFun x := ⟨t⁻¹ * x * t, by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (L : Set M)).inv_mem ht)
      x).mp x.2
    simpa using this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjOn_apply (L : Subgroup M) (t : M) (ht : t ∈ Subgroup.normalizer (L : Set M))
    (x : ↥L) : ((conjOn L t ht x : ↥L) : M) = t * x * t⁻¹ := rfl

theorem conjOn_sq (L : Subgroup M) (t : M) (ht : t ∈ Subgroup.normalizer (L : Set M))
    (ht2 : t ^ 2 = 1) : conjOn L t ht ^ 2 = 1 := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  have h0 : (conjOn L t ht ^ 2) x = conjOn L t ht (conjOn L t ht x) := by
    simp [pow_two, MulAut.mul_apply]
  rw [h0, conjOn_apply, conjOn_apply]
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  calc t * (t * (x : M) * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
    _ = x := by rw [htt]; simp

theorem conjOn_fixes (L : Subgroup M) (t : M) (ht : t ∈ Subgroup.normalizer (L : Set M))
    (y : ↥L) (hty : t * y = y * t) : conjOn L t ht y = y := by
  apply Subtype.ext
  rw [conjOn_apply, hty]
  group

end Conj

section Perfect

theorem aut_eq_one_of_central {Q : Type*} [Group Q] [Group.IsPerfect Q] (σ : MulAut Q)
    (h : ∀ x, σ x * x⁻¹ ∈ Subgroup.center Q) : σ = 1 := by
  have key := mult_trivial_of_perfect (Γ := Q) (M := ↥(Subgroup.center Q))
    (fun x => ⟨σ x * x⁻¹, h x⟩) (fun g k => by
      apply Subtype.ext
      show σ (g * k) * (g * k)⁻¹ = (σ g * g⁻¹) * (σ k * k⁻¹)
      have hc : (σ k * k⁻¹) * g⁻¹ = g⁻¹ * (σ k * k⁻¹) := (Subgroup.mem_center_iff.mp (h k) g⁻¹).symm
      calc σ (g * k) * (g * k)⁻¹ = σ g * ((σ k * k⁻¹) * g⁻¹) := by
            simp only [map_mul, mul_inv_rev]; group
        _ = σ g * (g⁻¹ * (σ k * k⁻¹)) := by rw [hc]
        _ = (σ g * g⁻¹) * (σ k * k⁻¹) := by group)
  ext x
  have := congrArg Subtype.val (key x)
  have h1 : σ x * x⁻¹ = 1 := this
  simpa using mul_inv_eq_one.mp h1

theorem centralizes_of_central_conj {M : Type*} [Group M] {L : Subgroup M} [Group.IsPerfect ↥L]
    {s : M} (hs : s ∈ Subgroup.normalizer (L : Set M))
    (h : ∀ l : ↥L, ∃ z ∈ Subgroup.center ↥L, s * (l : M) * s⁻¹ = l * z) :
    ∀ l ∈ L, s * l = l * s := by
  have hσ := aut_eq_one_of_central (conjOn L s hs) (fun l => by
    obtain ⟨z, hz, hl⟩ := h l
    have h1 : conjOn L s hs l = l * z := Subtype.ext (by rw [conjOn_apply, hl]; rfl)
    rw [h1]
    have hc : l * z = z * l := Subgroup.mem_center_iff.mp hz l
    have : (l * z) * l⁻¹ = z := by rw [hc]; group
    rw [this]
    exact hz)
  intro l hl
  have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : M)) hσ
  have h2 : s * l * s⁻¹ = l := h1
  calc s * l = (s * l * s⁻¹) * s := by group
    _ = l * s := by rw [h2]

end Perfect

section Outer

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

omit [Finite V] in
theorem normalizer_conjClosure {t : MulAut V} (htG : t ∈ G) :
    t ∈ Subgroup.normalizer (CGT6.conjClosure Y G : Set (MulAut V)) :=
  CGT6.le_normalizer_conjClosure htG

omit [Finite V] in
theorem centerAutHom_conjOn_ne_aux {L G : Subgroup (MulAut V)} (hLG : L ≤ G)
    [Group.IsPerfect ↥L] {t : MulAut V} (htG : t ∈ G)
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut V)))
    (hC : ∀ s ∈ G, (∀ l ∈ L, s * l = l * s) → s ∈ L) (htL : t ∉ L) :
    ∀ x : ↥L ⧸ Subgroup.center ↥L,
      K7a.centerAutHom ↥L (conjOn L t htN) ≠ MulAut.conj x := by
  intro xb hxb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  have hxN : (x : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
    Subgroup.le_normalizer x.2
  have hsN : (x : MulAut V)⁻¹ * t ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
    mul_mem (inv_mem hxN) htN
  have hcentral := centralizes_of_central_conj (L := L) hsN (fun l => by
    have h1 : (QuotientGroup.mk (conjOn L t htN l) : ↥L ⧸ Subgroup.center ↥L) =
        QuotientGroup.mk (x * l * x⁻¹) := by
      have := congrArg (fun φ => φ (QuotientGroup.mk l)) hxb
      simpa [K7a.centerAutHom_mk, MulAut.conj_apply, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv] using this
    have h2 : (x * l * x⁻¹)⁻¹ * conjOn L t htN l ∈ Subgroup.center ↥L :=
      QuotientGroup.eq.mp h1.symm
    have h3 : x⁻¹ * ((x * l * x⁻¹)⁻¹ * conjOn L t htN l) * x ∈ Subgroup.center ↥L := by
      have := (inferInstance : (Subgroup.center ↥L).Normal).conj_mem _ h2 x⁻¹
      simpa using this
    refine ⟨_, h3, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjOn_apply]
    group)
  have hsG : (x : MulAut V)⁻¹ * t ∈ G := mul_mem (inv_mem (hLG x.2)) htG
  have hsL : (x : MulAut V)⁻¹ * t ∈ L := hC _ hsG fun l hl => hcentral l hl
  apply htL
  have : t = (x : MulAut V) * ((x : MulAut V)⁻¹ * t) := by group
  rw [this]
  exact mul_mem x.2 hsL

theorem centralizer_le_of_cfg (cfg : EndCfg4 G T Y) :
    ∀ s ∈ G, (∀ l ∈ CGT6.conjClosure Y G, s * l = l * s) → s ∈ CGT6.conjClosure Y G := by
  intro s hsG hs
  have hsF : (⟨s, hsG⟩ : ↥G) ∈ generalizedFitting ↥G := by
    apply CFSG.centralizer_generalizedFitting_le ↥G
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [cfg.fstar] at hh
    apply Subtype.ext
    exact (hs h hh).symm
  rw [cfg.fstar] at hsF
  exact hsF

theorem centerAutHom_conjOn_ne (cfg : EndCfg4 G T Y) {t : MulAut V} (htG : t ∈ G)
    (htL : t ∉ CGT6.conjClosure Y G) :
    ∀ x : ↥(CGT6.conjClosure Y G) ⧸ Subgroup.center ↥(CGT6.conjClosure Y G),
      K7a.centerAutHom ↥(CGT6.conjClosure Y G)
          (conjOn (CGT6.conjClosure Y G) t (normalizer_conjClosure htG)) ≠ MulAut.conj x := by
  have hperf : Group.IsPerfect ↥(CGT6.conjClosure Y G) := ⟨cfg.quasi.1⟩
  exact centerAutHom_conjOn_ne_aux (G := G) (CGT6.conjClosure_le (cfg.adm.hYC.trans inf_le_left))
    htG (normalizer_conjClosure htG) (centralizer_le_of_cfg cfg) htL

end Outer

section Quot

variable {V : Type} [CommGroup V]

theorem commGen_of_perfect {Y : Subgroup (MulAut V)} (hperf : ⁅Y, Y⁆ = Y) : CommGen Y := by
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  intro N hN
  exact commV_le_of_perfect Y N fun g u => hN g g.2 u u.2

theorem simpleQuot_of_inClassX [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y) (hX : InClassX ↥(yuHol Y)) : SimpleQuot Y := by
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨hshort, hnat⟩ := hX
  have hU : shortU ↥(yuHol Y) = (yuInc Y).range := by
    rcases hnat with ⟨n, hn, φ, -⟩ | ⟨n, hn, φ, -⟩
    · exact shortU_eq_range Y φ hV hshort
    · exact shortU_eq_range Y φ hV hshort
  have hUA : commV Y ≠ commV Y ⊓ fixV Y := by
    intro h
    have hfix : ∀ (u : ↥(commV Y)) (g : MulAut V), g ∈ Y → g (u : V) = u := fun u g hg =>
      (h ▸ u.2 : (u : V) ∈ commV Y ⊓ fixV Y).2 g hg
    have hle : shortU ↥(yuHol Y) ≤ shortC ↥(yuHol Y) := by
      intro x hx
      obtain ⟨u, rfl⟩ : x ∈ (yuInc Y).range := hU ▸ hx
      refine ⟨hx, Subgroup.mem_center_iff.mpr fun x' => ?_⟩
      have h4 := conj_yuInc Y x' u
      have h5 : (⟨x'.1.right u, apply_mem_commV_self Y x'.2.2 u.2⟩ : ↥(commV Y)) = u :=
        Subtype.ext (hfix u x'.1.right x'.2.2)
      rw [h5] at h4
      exact mul_inv_eq_iff_eq_mul.mp h4
    exact absurd hshort.nonzero (not_lt_of_ge hle)
  exact ⟨hUA, fun N hN hAN hNU => invariant_irreducible Y hV hshort hU N hN hNU hAN⟩

end Quot

end CFSG.CGT.PushingUpLit.CGT6X.End3
