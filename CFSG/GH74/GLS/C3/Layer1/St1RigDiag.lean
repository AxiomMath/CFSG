module

public import CFSG.GH74.GLS.C3.Layer1.St1RigOrd
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpRigid

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.C3.Layer1.PumpCalc
open scoped commutatorElement

section DiagData

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem x_mem_CxK {x : G} {K : Subgroup G} (hK : K ≤ centralizer ({x} : Set G)) :
    x ∈ CxK x K := by
  have hxK : x ∈ centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact mem_centralizer_singleton_iff.mp (hK hk)
  have hxO : x ∈ centralizer ((pPrimeCoreOf 2 K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact mem_centralizer_singleton_iff.mp (hK (pPrimeCoreOf_le K hk))
  refine Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl,
    Subgroup.centralizer_le_normalizer _ hxK, Subgroup.centralizer_le_normalizer _ hxO, fun k hk => ?_⟩
  have : x * k = k * x := (mem_centralizer_singleton_iff.mp (hK hk)).symm
  rw [commutatorElement_def]
  have h1 : k * x * k⁻¹ * x⁻¹ = 1 := by
    rw [← this]
    group
  rw [h1]
  exact one_mem _

omit [Finite G] in
theorem mem_CxK_of_pumpUpLT {x t : G} {K K' : Subgroup G} (hlt : PumpUpLT 2 x K t K') :
    t ∈ CxK x K :=
  Subgroup.mem_inf.mpr ⟨hlt.2.2.1, hlt.2.2.2.1⟩

omit [Finite G] in
theorem sbar_mul {u a b : G} (ha : a ∈ centralizer ({u} : Set G))
    (hb : b ∈ centralizer ({u} : Set G)) :
    sbar (a * b) (mul_mem ha hb) = sbar a ha * sbar b hb := by
  simp only [sbar]
  rw [← map_mul]
  rfl

omit [Finite G] in
theorem sbar_commute {u a b : G} (ha : a ∈ centralizer ({u} : Set G))
    (hb : b ∈ centralizer ({u} : Set G)) (hab : a * b = b * a) :
    sbar a ha * sbar b hb = sbar b hb * sbar a ha := by
  rw [← sbar_mul ha hb, ← sbar_mul hb ha]
  simp only [sbar]
  congr 1
  exact Subtype.ext hab

omit [Finite G] in
theorem isPGroup_two_center_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsPGroup 2 ↥(center A)) : IsPGroup 2 ↥(center B) := by
  intro z
  have hz : e.symm (z : B) ∈ center A := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.mp z.2 (e g)
    apply e.injective
    simpa using this
  obtain ⟨n, hn⟩ := h ⟨e.symm (z : B), hz⟩
  refine ⟨n, Subtype.ext ?_⟩
  have h1 : (e.symm (z : B)) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have h2 : (z : B) ^ (2 ^ n) = 1 := by
    have := congrArg e h1
    simpa [map_pow] using this
  simpa using h2

structure DiagData (x t : G) (K K' Λ : Subgroup G) (hxY : x ∈ centralizer ({t} : Set G)) :
    Prop where
  hxo : orderOf x = 2
  hto : orderOf t = 2
  hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K
  lam : IsLam x t K Λ
  hK'c : IsPCompIn 2 (centralizer ({t} : Set G)) K'
  cent : ∀ (q : G) (hq : q ∈ centralizer ({t} : Set G)), q ∈ CxK x K →
    ∀ w ∈ bar t Λ, sbar q hq * w * (sbar q hq)⁻¹ = w
  hdiag : x ∉ normalizer (K' : Set G)
  hAB : ⁅bar t K', conjSub (sbar x hxY)⁻¹ (bar t K')⁆ = ⊥
  inj : Function.Injective (swapDiag hAB)
  hD : bar t Λ = (swapDiag hAB).range
  ker : ∀ (a : G) (haY : a ∈ centralizer ({t} : Set G)), a ∈ pPrimeCoreOf 2 Λ →
    barMk ↥(centralizer ({t} : Set G)) ⟨a, haY⟩ = 1
  iso : Nonempty (kBar K ≃* ↥(bar t Λ))

theorem diagData_of_diag {x t : G} {K K' : Subgroup G} (hlt : PumpUpLT 2 x K t K')
    (hxY : x ∈ centralizer ({t} : Set G)) (hle : hatCard K' ≤ hatCard K)
    (hnd : x ∉ normalizer (K' : Set G)) : ∃ Λ : Subgroup G, DiagData x t K K' Λ hxY := by
  obtain ⟨Λ, hΛ, hK'c, hiso, hker, hcent, hcases⟩ := rigid_step hlt hxY hle
  rcases hcases with ⟨hxN, -⟩ | ⟨-, hAB, hinj, hD⟩
  · exact absurd hxN hnd
  · exact ⟨Λ, ⟨hlt.1.1, hlt.2.1.1, hlt.1.2.2, hΛ, hK'c, hcent, hnd, hAB, hinj, hD, hker, hiso⟩⟩

namespace DiagData

variable {x t : G} {K K' Λ : Subgroup G} {hxY : x ∈ centralizer ({t} : Set G)}

theorem hs2 (h : DiagData x t K K' Λ hxY) : orderOf (sbar x hxY) = 2 :=
  orderOf_sbar h.hxo hxY

theorem hss (h : DiagData x t K K' Λ hxY) : sbar x hxY * sbar x hxY = 1 := by
  have := pow_orderOf_eq_one (sbar x hxY)
  rwa [h.hs2, sq] at this

theorem hsinv (h : DiagData x t K K' Λ hxY) : (sbar x hxY)⁻¹ = sbar x hxY :=
  inv_eq_of_mul_eq_one_left h.hss

theorem isComponent_L₁ (h : DiagData x t K K' Λ hxY) : CFSG.IsComponent (bar t K') :=
  isComponent_bar h.hK'c

theorem isComponent_L₂ (h : DiagData x t K K' Λ hxY) :
    CFSG.IsComponent (conjSub (sbar x hxY)⁻¹ (bar t K')) :=
  isComponent_conjSub h.isComponent_L₁ _

theorem ne (h : DiagData x t K K' Λ hxY) : conjSub (sbar x hxY)⁻¹ (bar t K') ≠ bar t K' := by
  intro heq
  apply h.hdiag
  apply mem_normalizer_of_map_normalizes h.hK'c.1 (isPCompIn_two_iff.mp h.hK'c).2 hxY
  show (bar t K').map (MulAut.conj (sbar x hxY)).toMonoidHom = bar t K'
  have := heq
  rw [h.hsinv] at this
  exact this

theorem isPGroup_center (h : DiagData x t K K' Λ hxY) : IsPGroup 2 ↥(center ↥(bar t K')) := by
  obtain ⟨e⟩ := kBar_equiv_bar h.hK'c
  exact isPGroup_two_center_of_equiv e (isPGroup_two_center_hat ↥K')

theorem inf_eq_bot (h : DiagData x t K K' Λ hxY) :
    bar t K' ⊓ conjSub (sbar x hxY)⁻¹ (bar t K') = ⊥ :=
  inf_conj_eq_bot_of_injective h.hs2 h.isPGroup_center h.hAB h.inj

omit [Finite G] in
theorem hDle (h : DiagData x t K K' Λ hxY) :
    bar t Λ ≤ bar t K' ⊔ conjSub (sbar x hxY)⁻¹ (bar t K') := by
  rw [h.hD]
  rintro _ ⟨b, rfl⟩
  exact swapDiag_mem_sup h.hAB b

omit [Finite G] in
theorem hproj₁ (h : DiagData x t K K' Λ hxY) :
    ∀ b ∈ bar t K', ∃ b' ∈ conjSub (sbar x hxY)⁻¹ (bar t K'), b * b' ∈ bar t Λ := by
  intro b hb
  refine ⟨(sbar x hxY)⁻¹ * b * sbar x hxY, ⟨b, hb, by simp⟩, ?_⟩
  rw [h.hD]
  exact ⟨⟨b, hb⟩, by simp [swapDiag_apply]⟩

omit [Finite G] in
theorem hproj₂ (h : DiagData x t K K' Λ hxY) :
    ∀ c ∈ conjSub (sbar x hxY)⁻¹ (bar t K'), ∃ c' ∈ bar t K', c * c' ∈ bar t Λ := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := hc
  refine ⟨b, hb, ?_⟩
  have hcomm := commute_of_commutator_conj_eq_bot h.hAB hb
    (show (MulAut.conj (sbar x hxY)⁻¹).toMonoidHom b ∈ conjSub (sbar x hxY)⁻¹ (bar t K') from
      ⟨b, hb, rfl⟩)
  rw [h.hD]
  refine ⟨⟨b, hb⟩, ?_⟩
  rw [swapDiag_apply]
  rw [← hcomm]
  simp

theorem perm (h : DiagData x t K K' Λ hxY) {r : G} (hr : r ∈ centralizer ({t} : Set G))
    (hrC : r ∈ CxK x K) :
    conjSub (sbar r hr) (bar t K') = bar t K' ∨
      conjSub (sbar r hr) (bar t K') = conjSub (sbar x hxY)⁻¹ (bar t K') := by
  have hDc : conjSub (sbar r hr) (bar t Λ) = bar t Λ := by
    have hfix : ∀ w ∈ bar t Λ, (MulAut.conj (sbar r hr)).toMonoidHom w = w := fun w hw =>
      h.cent r hr hrC w hw
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hfix w hw]
      exact hw
    · intro hz
      exact ⟨z, hz, hfix z hz⟩
  have hDle' : bar t Λ ≤ conjSub (sbar r hr) (bar t K') ⊔
      conjSub (sbar r hr) (conjSub (sbar x hxY)⁻¹ (bar t K')) := by
    calc bar t Λ = conjSub (sbar r hr) (bar t Λ) := hDc.symm
      _ ≤ conjSub (sbar r hr) (bar t K' ⊔ conjSub (sbar x hxY)⁻¹ (bar t K')) :=
          Subgroup.map_mono h.hDle
      _ = _ := Subgroup.map_sup _ _ _
  have hAB' : ⁅conjSub (sbar x hxY)⁻¹ (bar t K'), bar t K'⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact h.hAB
  have h1 := eq_of_diag_le_sup h.isComponent_L₁ (isComponent_conjSub h.isComponent_L₁ _)
    (isComponent_conjSub h.isComponent_L₂ _) h.hAB hDle' h.hproj₁
  have h2 := eq_of_diag_le_sup h.isComponent_L₂ (isComponent_conjSub h.isComponent_L₁ _)
    (isComponent_conjSub h.isComponent_L₂ _) hAB' hDle' h.hproj₂
  rcases h1 with h1 | h1
  · exact Or.inl h1.symm
  · rcases h2 with h2 | h2
    · exact Or.inr h2.symm
    · exact absurd (h2.trans h1.symm) h.ne

omit [Finite G] in
theorem x_not_mem_CxK (h : DiagData x t K K' Λ hxY) : x ∉ CxK t K' := fun hx =>
  h.hdiag (Subgroup.mem_inf.mp hx).2.1

theorem stab_mem (h : DiagData x t K K' Λ hxY) {r : G} (hr : r ∈ centralizer ({t} : Set G))
    (hrC : r ∈ CxK x K) (hst : conjSub (sbar r hr) (bar t K') = bar t K') : r ∈ CxK t K' := by
  refine mem_CxK_of_centralizes h.hK'c hr (fun w hw => ?_)
  have hrx : r * x = x * r := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hrC).1
  have hrt := sbar_commute hr hxY hrx
  have hrL : ∀ b ∈ bar t K', sbar r hr * b * (sbar r hr)⁻¹ ∈ bar t K' := by
    intro b hb
    have : (MulAut.conj (sbar r hr)).toMonoidHom b ∈ conjSub (sbar r hr) (bar t K') :=
      Subgroup.mem_map_of_mem _ hb
    rw [hst] at this
    exact this
  have hrD : ∀ b : ↥(bar t K'), sbar r hr * swapDiag h.hAB b * (sbar r hr)⁻¹ =
      swapDiag h.hAB b := fun b =>
    h.cent r hr hrC _ (h.hD ▸ MonoidHom.mem_range.mpr ⟨b, rfl⟩)
  exact commute_of_swapDiag h.hAB h.inj hrt hrL hrD hw

theorem step1 (h : DiagData x t K K' Λ hxY) {r : G} (hr : r ∈ centralizer ({t} : Set G))
    (hrC : r ∈ CxK x K) : r ∈ CxK t K' ∨ x * r ∈ CxK t K' := by
  rcases h.perm hr hrC with h1 | h1
  · exact Or.inl (h.stab_mem hr hrC h1)
  · right
    have hxC : x ∈ CxK x K := x_mem_CxK h.hKc.1
    have hxr : x * r ∈ centralizer ({t} : Set G) := mul_mem hxY hr
    have hst : conjSub (sbar (x * r) hxr) (bar t K') = bar t K' := by
      rw [sbar_mul hxY hr, conjSub_mul, h1]
      exact conjSub_conjSub_inv _ _
    exact h.stab_mem hxr (mul_mem hxC hrC) hst


end DiagData

end DiagData

section Gilman

variable {Y : Type} [Group Y] [Finite Y]

theorem injective_barMk_comp {P : Subgroup Y} (hP : IsPGroup 2 P) :
    Function.Injective ((barMk Y).comp P.subtype) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have hu1 : (u : Y) ∈ pPrimeCore 2 Y := by
    have : barMk Y (u : Y) = 1 := hu
    exact (QuotientGroup.eq_one_iff _).mp this
  obtain ⟨k, hk⟩ := hP u
  have h1 : orderOf (u : Y) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf (u : Y) ∣ Nat.card (pPrimeCore 2 Y) := Subgroup.orderOf_dvd_natCard _ hu1
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 Y)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (odd_card_pPrimeCore Y))
  have : orderOf (u : Y) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact Subtype.ext (orderOf_eq_one_iff.mp this)

theorem equiv_map_barMk {P : Subgroup Y} (hP : IsPGroup 2 P) : Nonempty (↥P ≃* ↥(P.map (barMk Y))) := by
  have hinj := injective_barMk_comp hP
  have hrange : ((barMk Y).comp P.subtype).range = P.map (barMk Y) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

end Gilman

section Gilman2

variable {Z : Type} [Group Z] [Finite Z]

theorem pRank_subgroupOf_eq {X Y : Subgroup Z} (h : X ≤ Y) :
    pRank 2 ↥(X.subgroupOf Y) = pRank 2 ↥X := by
  rw [SectionRank.pRank_eq_open_pRank_top 2, SectionRank.pRank_eq_open_pRank_top 2]
  exact SectionRank.pRank_top_eq_of_mulEquiv Nat.one_lt_two (Subgroup.subgroupOfEquivOfLe h)

theorem pRank_conjSub (g : Z) (L : Subgroup Z) : pRank 2 ↥(conjSub g L) = pRank 2 ↥L := by
  rw [SectionRank.pRank_eq_open_pRank_top 2, SectionRank.pRank_eq_open_pRank_top 2]
  exact (SectionRank.pRank_top_eq_of_mulEquiv Nat.one_lt_two
    (Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)).symm

end Gilman2

section GilmanBounds

variable {G : Type} [Group G] [Finite G]

namespace DiagData

variable {x t : G} {K K' Λ : Subgroup G} {hxY : x ∈ centralizer ({t} : Set G)}

theorem gilman_bounds (h : DiagData x t K K' Λ hxY) {R₀ : Subgroup G} (hR₀ : IsPGroup 2 R₀)
    (hR₀C : ∀ r ∈ R₀, r ∈ CxK t K') (hR₀x : ∀ r ∈ R₀, r * x = x * r) :
    pRank 2 ↥(bar t K') + pRank 2 ↥R₀ ≤ pRank 2 ↥(CxK t K') ∧
      (Nat.card ↥(bar t K')).factorization 2 + (Nat.card ↥R₀).factorization 2 ≤
        (Nat.card ↥(CxK t K')).factorization 2 := by
  have hR₀Y : R₀ ≤ centralizer ({t} : Set G) := fun r hr => (Subgroup.mem_inf.mp (hR₀C r hr)).1
  have hCY : CxK t K' ≤ centralizer ({t} : Set G) := inf_le_left
  set R₀' : Subgroup ↥(centralizer ({t} : Set G)) := R₀.subgroupOf (centralizer ({t} : Set G))
    with hR₀'
  have hR₀'p : IsPGroup 2 R₀' := hR₀.comap_subtype
  set B := R₀'.map (barMk ↥(centralizer ({t} : Set G))) with hB
  set L₂ := conjSub (sbar x hxY)⁻¹ (bar t K') with hL₂
  have hBr : ∀ b ∈ B, ∃ (r : G) (hr : r ∈ centralizer ({t} : Set G)), r ∈ R₀ ∧ b = sbar r hr := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, m.2, Subgroup.mem_subgroupOf.mp hm, rfl⟩
  have hBcentL : ∀ b ∈ B, ∀ w ∈ bar t K', b * w * b⁻¹ = w := by
    intro b hb w hw
    obtain ⟨r, hr, hrR, rfl⟩ := hBr b hb
    exact centralizes_of_mem_CxK h.hK'c hr (hR₀C r hrR) w hw
  have hBs : ∀ b ∈ B, b * sbar x hxY = sbar x hxY * b := by
    intro b hb
    obtain ⟨r, hr, hrR, rfl⟩ := hBr b hb
    exact sbar_commute hr hxY (hR₀x r hrR)
  have hBcomm : ∀ a ∈ L₂, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨ℓ, hℓ, rfl⟩ := ha
    have h1 := hBcentL b hb ℓ hℓ
    have h2 := hBs b hb
    have h3 : b * (sbar x hxY)⁻¹ = (sbar x hxY)⁻¹ * b := by
      calc b * (sbar x hxY)⁻¹ = (sbar x hxY)⁻¹ * (sbar x hxY * b) * (sbar x hxY)⁻¹ := by group
        _ = (sbar x hxY)⁻¹ * (b * sbar x hxY) * (sbar x hxY)⁻¹ := by rw [← h2]
        _ = (sbar x hxY)⁻¹ * b := by group
    have hbℓ : b * (ℓ : barQ ↥(centralizer ({t} : Set G))) = ℓ * b := mul_inv_eq_iff_eq_mul.mp h1
    change (sbar x hxY)⁻¹ * ℓ * ((sbar x hxY)⁻¹)⁻¹ * b =
      b * ((sbar x hxY)⁻¹ * ℓ * ((sbar x hxY)⁻¹)⁻¹)
    rw [inv_inv]
    calc (sbar x hxY)⁻¹ * ℓ * sbar x hxY * b
        = (sbar x hxY)⁻¹ * ℓ * (sbar x hxY * b) := by group
      _ = (sbar x hxY)⁻¹ * ℓ * (b * sbar x hxY) := by rw [← h2]
      _ = (sbar x hxY)⁻¹ * (ℓ * b) * sbar x hxY := by group
      _ = (sbar x hxY)⁻¹ * (b * ℓ) * sbar x hxY := by rw [← hbℓ]
      _ = ((sbar x hxY)⁻¹ * b) * ℓ * sbar x hxY := by group
      _ = (b * (sbar x hxY)⁻¹) * ℓ * sbar x hxY := by rw [← h3]
      _ = b * ((sbar x hxY)⁻¹ * ℓ * sbar x hxY) := by group
  have hBinf : L₂ ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    obtain ⟨hcL, hcB⟩ := hc
    have hcs := hBs c hcB
    have hcL₁ : c ∈ bar t K' := by
      have h1 : (sbar x hxY) * c * (sbar x hxY)⁻¹ ∈ bar t K' := by
        have := (TwoThin.mem_conjSub_iff'.mp hcL)
        simpa using this
      have h2 : (sbar x hxY) * c * (sbar x hxY)⁻¹ = c := by
        rw [← hcs]; group
      rwa [h2] at h1
    have : c ∈ bar t K' ⊓ L₂ := ⟨hcL₁, hcL⟩
    rw [h.inf_eq_bot] at this
    exact this
  have hsup : L₂ ⊔ B ≤ centralizer ((bar t K' : Subgroup _) : Set _) := by
    refine sup_le ?_ ?_
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact h.hAB)
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have := hBcentL b hb w hw
      calc w * b = (b * w * b⁻¹) * b := by rw [this]
        _ = b * w := by group
  have hcomap : (L₂ ⊔ B).comap (barMk ↥(centralizer ({t} : Set G))) ≤
      (CxK t K').subgroupOf (centralizer ({t} : Set G)) := by
    intro y hy
    refine mem_CxK_of_centralizes h.hK'c y.2 (fun w hw => ?_)
    have hy' : barMk ↥(centralizer ({t} : Set G)) y ∈ L₂ ⊔ B := hy
    have := Subgroup.mem_centralizer_iff.mp (hsup hy') w hw
    change barMk _ y * w * (barMk _ y)⁻¹ = w
    calc barMk _ y * w * (barMk _ y)⁻¹ = (w * barMk _ y) * (barMk _ y)⁻¹ := by rw [← this]
      _ = w := by group
  have hrk : CFSG.Open.pRank 2 L₂ + CFSG.Open.pRank 2 B ≤ CFSG.Open.pRank 2 (L₂ ⊔ B) :=
    pRank_add_le_of_commute hBcomm hBinf le_rfl
  have hfac := factorization_add_le_of_commute hBcomm hBinf (le_refl (L₂ ⊔ B))
  obtain ⟨eB⟩ := equiv_map_barMk hR₀'p
  have eR : ↥R₀' ≃* ↥R₀ := Subgroup.subgroupOfEquivOfLe hR₀Y
  have hBrank : pRank 2 ↥B = pRank 2 ↥R₀ := by
    rw [SectionRank.pRank_eq_open_pRank_top 2, SectionRank.pRank_eq_open_pRank_top 2]
    exact (SectionRank.pRank_top_eq_of_mulEquiv Nat.one_lt_two eB).symm.trans
      (SectionRank.pRank_top_eq_of_mulEquiv Nat.one_lt_two eR)
  have hBcard : Nat.card ↥B = Nat.card ↥R₀ :=
    (Nat.card_congr eB.toEquiv).symm.trans (Nat.card_congr eR.toEquiv)
  have hXcard : Nat.card ↥((CxK t K').subgroupOf (centralizer ({t} : Set G))) =
      Nat.card ↥(CxK t K') := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCY).toEquiv
  refine ⟨?_, ?_⟩
  · calc pRank 2 ↥(bar t K') + pRank 2 ↥R₀ = pRank 2 ↥L₂ + pRank 2 ↥B := by
          rw [hL₂, pRank_conjSub, hBrank]
      _ ≤ pRank 2 ↥(L₂ ⊔ B) := by
          rw [pRank_two_subgroup_eq_open, pRank_two_subgroup_eq_open,
            pRank_two_subgroup_eq_open]
          exact hrk
      _ ≤ pRank 2 ↥((CxK t K').subgroupOf (centralizer ({t} : Set G))) :=
          pRank_le_of_le_comap hcomap
      _ = pRank 2 ↥(CxK t K') := pRank_subgroupOf_eq hCY
  · calc (Nat.card ↥(bar t K')).factorization 2 + (Nat.card ↥R₀).factorization 2
        = (Nat.card ↥L₂).factorization 2 + (Nat.card ↥B).factorization 2 := by
          rw [hL₂, card_conjSub, hBcard]
      _ ≤ (Nat.card ↥(L₂ ⊔ B)).factorization 2 := hfac
      _ ≤ (Nat.card ↥((CxK t K').subgroupOf (centralizer ({t} : Set G)))).factorization 2 :=
          factorization_le_of_le_comap hcomap
      _ = (Nat.card ↥(CxK t K')).factorization 2 := by rw [hXcard]

end DiagData

end GilmanBounds

end CFSG.GH74.GLS.C3.Layer1.PumpRigid
