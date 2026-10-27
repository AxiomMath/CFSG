module

public import CFSG.GH74.GLS.LU.Local.A3Reduce
public import CFSG.GH74.GLS.LU.Local.Torus1

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
  CFSG.ComponentClassification
open scoped Pointwise MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local

section Y

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem perfect_of_isTwoComponent {C H : Subgroup Y} (hHC : H ≤ C)
    (h : TwoComponents.IsTwoComponent (H.subgroupOf C)) : ⁅H, H⁆ = H := by
  have hp : commutator ↥(H.subgroupOf C) = ⊤ := TwoComponents.perfect h
  have h1 : (commutator ↥(H.subgroupOf C)).map (H.subgroupOf C).subtype = H.subgroupOf C := by
    rw [hp, ← MonoidHom.range_eq_map, range_subtype]
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h1
  have h2 := congrArg (Subgroup.map C.subtype) h1
  rw [Subgroup.map_commutator, subgroupOf_map_subtype, inf_eq_left.mpr hHC] at h2
  exact h2

theorem KComp.of_perfect_le {s : Y} {K : Subgroup Y} (hs : orderOf s = 2) (hsK : s ∈ K)
    (hle : K ≤ centralizer ({s} : Set Y))
    (hnorm : ∀ c ∈ centralizer ({s} : Set Y), ∀ k ∈ K, c * k * c⁻¹ ∈ K) (hq : IsQuasisimple K)
    (hcen : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k ∈ zpowers s)
    (hperf : ∀ Λ : Subgroup Y, Λ ≤ centralizer ({s} : Set Y) → ⁅Λ, Λ⁆ = Λ → Λ ≤ K) :
    KComp Y s K := by
  refine ⟨hs, hsK, hle, hnorm, hq, hcen, ?_⟩
  intro Λ hΛ hΛ2
  have hΛK : Λ ≤ K := hperf Λ hΛ (perfect_of_isTwoComponent hΛ hΛ2)
  have h3 : TwoComponents.IsTwoComponent (Λ.subgroupOf K) :=
    TwoComponentTransport.restrict_nested Λ K (centralizer ({s} : Set Y)) hΛK hle hΛ2
  have : Group.IsPerfect ↥(Λ.subgroupOf K) := ⟨TwoComponents.perfect h3⟩
  rcases Quasisimple.perfect_subnormal_eq_bot_or_eq_top
      ((AssemblyBPredicates.isQuasisimple_iff_native ↥K).2 hq) (Λ.subgroupOf K) h3.1 with h | h
  · exfalso
    have := TwoComponents.nontrivial h3
    exact ((Λ.subgroupOf K).nontrivial_iff_ne_bot.mp inferInstance) h
  · exact le_antisymm hΛK (Subgroup.subgroupOf_eq_top.mp h)

end Y

variable {G : Type} [Group G] [Finite G] {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}
  {p f : ℕ} {ε : ℤ}

theorem cent_abelian {q : ℕ} (hc : LUComps G q z K₁ K₂) [IsCyclic ↥(A0 z)] {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) {a k : G} (ha : a ∈ A0 z) (hk : k ∈ K)
    (hnc : ¬ ∀ k' ∈ K, (a * k) * k' = k' * (a * k)) :
    ∀ d ∈ K, ∀ d' ∈ K, d * (a * k) = (a * k) * d → d' * (a * k) = (a * k) * d' →
      d * d' = d' * d := by
  have hKle : K ≤ K₁ ⊔ K₂ := by
    rcases hK with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hsl : HasSL2Model ↥K (fun r => r = q) := by
    rcases hK with rfl | rfl
    · exact hc.sl₁
    · exact hc.sl₂
  obtain ⟨F, hF, hFin, hFq, -⟩ := id hsl
  obtain ⟨e⟩ := exists_mulEquiv_SL2 hsl F hFq
  have hcentA : ∀ g ∈ K, a * g = g * a := fun g hg =>
    mem_centralizer_iff.mp (hc.le_centralizer_A0 (hKle hg)) a ha
  have hk' : e.symm ⟨k, hk⟩ ∉ Subgroup.center SL(2, F) := by
    intro hcen
    apply hnc
    intro g hg
    have h1 : (⟨k, hk⟩ : ↥K) ∈ center ↥K := by
      have := (mem_center_equiv_iff e (a := e.symm ⟨k, hk⟩)).mpr hcen
      simpa using this
    have h2 : k * g = g * k := by
      have := Subgroup.mem_center_iff.mp h1 ⟨g, hg⟩
      exact (congrArg Subtype.val this).symm
    calc (a * k) * g = a * (k * g) := by group
      _ = a * (g * k) := by rw [h2]
      _ = (a * g) * k := by group
      _ = (g * a) * k := by rw [hcentA g hg]
      _ = g * (a * k) := by group
  have hcomm : ∀ (d : G) (hd : d ∈ K), d * (a * k) = (a * k) * d →
      e.symm ⟨d, hd⟩ * e.symm ⟨k, hk⟩ = e.symm ⟨k, hk⟩ * e.symm ⟨d, hd⟩ := by
    intro d hd hdy
    have h1 : a * (d * k) = a * (k * d) := by
      calc a * (d * k) = (a * d) * k := by group
        _ = (d * a) * k := by rw [hcentA d hd]
        _ = d * (a * k) := by group
        _ = (a * k) * d := hdy
        _ = a * (k * d) := by group
    have hdk : d * k = k * d := mul_left_cancel h1
    apply e.injective
    apply Subtype.ext
    simpa using hdk
  intro d hd d' hd' hdy hd'y
  have := sl2_commute_of_centralizer hk' (a := e.symm ⟨d, hd⟩) (b := e.symm ⟨d', hd'⟩)
    (hcomm d hd hdy) (hcomm d' hd' hd'y)
  have h := congrArg (fun M : SL(2, F) => ((e M : ↥K) : G)) this
  simpa using h

structure XData (z : G) (K₁ K₂ : Subgroup G) (x : G) (r : ℕ) : Prop where
  cz : z * x = x * z
  c₁ : ∀ k ∈ K₁, x * k = k * x
  dec : ∃ a ∈ A0 z, ∃ k ∈ K₂, x = a * k ∧ orderOf k = r
  nc₂ : ¬ ∀ k ∈ K₂, x * k = k * x

theorem XData.abelian₂ {q : ℕ} (hc : LUComps G q z K₁ K₂) [IsCyclic ↥(A0 z)] {x : G} {r : ℕ}
    (hx : XData z K₁ K₂ x r) :
    ∀ d ∈ K₂, ∀ d' ∈ K₂, d * x = x * d → d' * x = x * d' → d * d' = d' * d := by
  obtain ⟨a, ha, k, hk, rfl, -⟩ := hx.dec
  exact cent_abelian hc (Or.inr rfl) ha hk hx.nc₂

theorem perfect_le_K₁ (X : LUCtx G p f z S K₁ K₂ t u ε) {x : G} {r : ℕ} (hx : XData z K₁ K₂ x r)
    {Λ : Subgroup G} (hΛz : ∀ l ∈ Λ, l * z = z * l) (hΛx : ∀ l ∈ Λ, l * x = x * l)
    (hΛ : ⁅Λ, Λ⁆ = Λ) : Λ ≤ K₁ := by
  have hc := X.comps
  have hs := X.syl
  have : IsCyclic ↥(A0 z) := X.eps.A0_cyc
  have hΛC : Λ ≤ Cz z := fun l hl => mem_centralizer_singleton_iff.mpr (hΛz l hl)
  have hΛK := perfect_le_K hc hs X.gen hΛC hΛ
  have hab := hx.abelian₂ hc
  have hdec : ∀ l ∈ Λ, ∃ a ∈ K₁, ∃ b ∈ K₂, l = a * b ∧ b * x = x * b := by
    intro l hl
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc.comm (hΛK hl)
    refine ⟨a, ha, b, hb, rfl, ?_⟩
    have h1 := hΛx _ hl
    have h2 := hx.c₁ a ha
    calc b * x = a⁻¹ * (a * b * x) := by group
      _ = a⁻¹ * (x * (a * b)) := by rw [h1]
      _ = a⁻¹ * (x * a) * b := by group
      _ = a⁻¹ * (a * x) * b := by rw [h2]
      _ = x * b := by group
  have hcomm_in : ∀ l ∈ Λ, ∀ l' ∈ Λ, ⁅l, l'⁆ ∈ K₁ := by
    intro l hl l' hl'
    obtain ⟨a, ha, b, hb, rfl, hbx⟩ := hdec l hl
    obtain ⟨a', ha', b', hb', rfl, hb'x⟩ := hdec l' hl'
    have hbb' : b * b' = b' * b := hab b hb b' hb' hbx hb'x
    rw [commutatorElement_def]
    have h1 := commutator_mul_of_commute (hc.comm a ha b' hb') (hc.comm a' ha' b hb)
      (hc.comm a ha b hb) (hc.comm a' ha' b' hb')
    rw [h1]
    have hb1 : b * b' * b⁻¹ * b'⁻¹ = 1 := by
      calc b * b' * b⁻¹ * b'⁻¹ = (b' * b) * b⁻¹ * b'⁻¹ := by rw [hbb']
        _ = 1 := by group
    rw [hb1, mul_one]
    exact K₁.mul_mem (K₁.mul_mem (K₁.mul_mem ha ha') (K₁.inv_mem ha)) (K₁.inv_mem ha')
  calc Λ = ⁅Λ, Λ⁆ := hΛ.symm
    _ ≤ K₁ := Subgroup.commutator_le.mpr hcomm_in

theorem kcomp_CY (X : LUCtx G p f z S K₁ K₂ t u ε) {x : G} {r : ℕ} (hx : XData z K₁ K₂ x r) :
    KComp (CY G x) (toCY hx.cz) (K₁.subgroupOf (centralizer ({x} : Set G))) := by
  have hc := X.comps
  have hs := X.syl
  have hK₁C : K₁ ≤ centralizer ({x} : Set G) := fun k hk =>
    mem_centralizer_singleton_iff.mpr (hx.c₁ k hk).symm
  refine KComp.of_perfect_le ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold toCY
    rw [Subgroup.orderOf_mk]
    exact hs.z_inv
  · exact Subgroup.mem_subgroupOf.mpr hc.z_mem₁
  · intro k hk
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact hc.cz₁ (Subgroup.mem_subgroupOf.mp hk)
  · intro c hc' k hk
    have hcz : (c : G) * z = z * (c : G) := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc')
    have hcC : (c : G) ∈ Cz z := mem_centralizer_singleton_iff.mpr hcz
    have hcx : (c : G) * x = x * (c : G) := mem_centralizer_singleton_iff.mp c.2
    rcases hc.perm hcC with ⟨e1, -⟩ | ⟨e1, -⟩
    · exact Subgroup.mem_subgroupOf.mpr (LUComps.mem_of_map e1 (Subgroup.mem_subgroupOf.mp hk))
    · exfalso
      apply hx.nc₂
      intro k₂ hk₂
      have hk₂' : (c : G)⁻¹ * k₂ * (c : G) ∈ K₁ := mem_of_map_inv e1 hk₂
      have hxc : Commute x (c : G) := (show Commute (c : G) x from hcx).symm
      have hxk₁ : Commute x ((c : G)⁻¹ * k₂ * (c : G)) := hx.c₁ _ hk₂'
      have h3 : Commute x ((c : G) * ((c : G)⁻¹ * k₂ * (c : G)) * (c : G)⁻¹) :=
        (hxc.mul_right hxk₁).mul_right hxc.inv_right
      have e : (c : G) * ((c : G)⁻¹ * k₂ * (c : G)) * (c : G)⁻¹ = k₂ := by group
      rw [e] at h3
      exact h3.eq
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK₁C).symm hc.quasi₁
  · intro k hk hkc
    have h1 : (⟨(k : G), Subgroup.mem_subgroupOf.mp hk⟩ : ↥K₁) ∈ center ↥K₁ := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have := hkc ⟨(g : G), hK₁C g.2⟩ (Subgroup.mem_subgroupOf.mpr g.2)
      exact (congrArg Subtype.val this).symm
    have h2 : (k : G) ∈ (center ↥K₁).map K₁.subtype := ⟨_, h1, rfl⟩
    rw [hc.cen₁] at h2
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h2
    refine mem_zpowers_iff.mpr ⟨i, ?_⟩
    apply Subtype.ext
    simpa [toCY] using hi
  · intro Λ hΛz hΛ
    have hΛG : ⁅Λ.map (centralizer ({x} : Set G)).subtype, Λ.map (centralizer ({x} : Set G)).subtype⁆ =
        Λ.map (centralizer ({x} : Set G)).subtype := by
      rw [← Subgroup.map_commutator, hΛ]
    have hle := perfect_le_K₁ X hx (Λ := Λ.map (centralizer ({x} : Set G)).subtype)
      (fun l hl => by
        obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.mp hl
        have := mem_centralizer_singleton_iff.mp (hΛz hl')
        exact congrArg Subtype.val this)
      (fun l hl => by
        obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.mp hl
        exact mem_centralizer_singleton_iff.mp l'.2) hΛG
    intro l hl
    exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_map_of_mem _ hl))

end CFSG.GH74.GLS.LU.Local
