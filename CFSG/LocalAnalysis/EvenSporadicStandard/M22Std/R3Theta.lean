module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Facts
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCAssemble
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCOuter2
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutBuild
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutConfig
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutEngineGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1AutModel

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L}

set_option quotPrecheck false in
local notation "Hc" => centralizer ({z} : Set G)

namespace OutData

variable (D : OutData L z t T₁ F tb)

@[expose] noncomputable def thetaOn {W : Subgroup G} (hW : W ≤ centralizer ({z} : Set G)) :
    ↥W →* MulAut (L ⧸ center L) :=
  (thetaH D.cfg.cent_le).comp (Subgroup.inclusion hW)

omit [Finite G] in
include D in
theorem thetaOn_eq_one_iff {W : Subgroup G} (hW : W ≤ centralizer ({z} : Set G)) (w : W) :
    D.thetaOn hW w = 1 ↔ (w : G) ∈ zpowers z := D.ker ⟨(w : G), hW w.2⟩

include D in
theorem card_le_two_mul_range {W : Subgroup G} (hW : W ≤ centralizer ({z} : Set G)) :
    Nat.card W ≤ 2 * Nat.card (D.thetaOn hW).range := by
  have h := Subgroup.card_ker_mul_card_range (D.thetaOn hW)
  have hk : Nat.card (D.thetaOn hW).ker ≤ 2 := by
    have h2 : Nat.card (zpowers z) = 2 := card_zpowers_invol D.cfg.z_sq D.cfg.z_ne
    rw [← h2]
    refine Nat.card_le_card_of_injective
      (fun w => (⟨((w : ↥W) : G), (D.thetaOn_eq_one_iff hW w).1 w.2⟩ : ↥(zpowers z))) ?_
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  rw [← h]
  exact Nat.mul_le_mul_right _ hk

include D in
theorem card_eq_two_mul_range {W : Subgroup G} (hW : W ≤ centralizer ({z} : Set G))
    (hzW : z ∈ W) : Nat.card W = 2 * Nat.card (D.thetaOn hW).range := by
  have h := Subgroup.card_ker_mul_card_range (D.thetaOn hW)
  have h2 : Nat.card (zpowers z) = 2 := card_zpowers_invol D.cfg.z_sq D.cfg.z_ne
  have hk : Nat.card (D.thetaOn hW).ker = 2 := by
    apply le_antisymm
    · rw [← h2]
      refine Nat.card_le_card_of_injective
        (fun w => (⟨((w : ↥W) : G), (D.thetaOn_eq_one_iff hW w).1 w.2⟩ : ↥(zpowers z))) ?_
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    · rw [← h2]
      refine Nat.card_le_card_of_injective
        (fun g => (⟨⟨(g : G), Subgroup.zpowers_le.2 hzW g.2⟩,
          (D.thetaOn_eq_one_iff hW _).2 g.2⟩ : ↥(D.thetaOn hW).ker)) ?_
      intro a b hab
      exact Subtype.ext (congrArg (fun x : ↥(D.thetaOn hW).ker => ((x : ↥W) : G)) hab)
  rw [← h, hk]

set_option linter.unusedSectionVars false in
include D in
theorem mem_T_iff {g : G} (hg : g ∈ centralizer ({z} : Set G)) :
    g ∈ (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) ↔ (⟨g, hg⟩ : ↥(centralizer
      ({z} : Set G))) ∈ T₁ := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro h
    exact ⟨_, h, rfl⟩

include D in
theorem range_le {W : Subgroup G}
    (hWT : W ≤ (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G)) :
    (D.thetaOn (hWT.trans D.cfg.T_le)).range ≤ T₁.map (thetaH D.cfg.cent_le) := by
  rintro _ ⟨w, rfl⟩
  have hwH : (w : G) ∈ centralizer ({z} : Set G) := D.cfg.T_le (hWT w.2)
  have hwT : (⟨(w : G), hwH⟩ : ↥Hc) ∈ T₁ :=
    (D.mem_T_iff hwH).1 (hWT w.2)
  exact ⟨⟨(w : G), hwH⟩, hwT, rfl⟩

include D in
theorem exists_E {T : Subgroup G} (hT : T = T₁.map (centralizer ({z} : Set G)).subtype)
    (hzsq : ∀ g : G, g * g ≠ z) (hF16 : Nat.card F = 16)
    {J : Subgroup (MulAut (L ⧸ center L))}
    (hJ : E32Facts (L ⧸ center L) (T₁.map (thetaH D.cfg.cent_le)) F J) :
    ∃ (E : Subgroup G) (b : G), E ≤ T ∧ (∀ a ∈ E, ∀ c ∈ E, a * c = c * a) ∧
      (∀ a ∈ E, a * a = 1) ∧ Nat.card E = 64 ∧ z ∈ E ∧
      (∀ W' : Subgroup G, W' ≤ T → (∀ a ∈ W', ∀ c ∈ W', a * c = c * a) →
        (∀ a ∈ W', a * a = 1) → Nat.card W' = 64 → W' = E) ∧
      (∀ V : Subgroup G, V ≤ T → (∀ s ∈ T, ∀ v ∈ V, s * v * s⁻¹ ∈ V) →
        (∀ a ∈ V, ∀ c ∈ V, a * c = c * a) → (∀ a ∈ V, a * a = 1) → Nat.card V = 32 →
        z ∈ V → Nat.card ↥(V ⊓ E) ≤ 8 → V = liftSub F ⊔ zpowers z) ∧
      b ∈ L ∧ b * b = 1 ∧ b ≠ 1 ∧ b ∉ liftSub F ∧ b ∈ E ∧
      (∀ j ∈ J, ∃ (e : G) (he : e ∈ centralizer ({z} : Set G)), e ∈ E ∧
        thetaH D.cfg.cent_le ⟨e, he⟩ = j) := by
  subst hT
  set θ := thetaH D.cfg.cent_le with hθ
  set T : Subgroup G := T₁.map (Subgroup.subtype Hc) with hTdef
  have hTH : T ≤ Hc := D.cfg.T_le
  set E : Subgroup G := (T₁ ⊓ J.comap θ).map (Subgroup.subtype Hc) with hEdef
  have hmemE : ∀ e, e ∈ E ↔ ∃ h : e ∈ Hc, (⟨e, h⟩ : ↥Hc) ∈ T₁ ∧ θ ⟨e, h⟩ ∈ J := by
    intro e
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx.1, hx.2⟩
    · rintro ⟨h, hT', hJ'⟩
      exact ⟨⟨e, h⟩, ⟨hT', hJ'⟩, rfl⟩
  have hET : E ≤ T := fun e he => by
    obtain ⟨h, hT', -⟩ := (hmemE e).1 he
    exact (D.mem_T_iff h).2 hT'
  have hEH : E ≤ Hc := hET.trans hTH
  have hzE : z ∈ E := by
    have hzH : z ∈ Hc := mem_centralizer_singleton_iff.2 rfl
    refine (hmemE z).2 ⟨hzH, D.zH_mem_T₁, ?_⟩
    have : θ ⟨z, hzH⟩ = 1 := (D.ker _).2 (mem_zpowers z)
    rw [this]
    exact J.one_mem
  have hzL : z ∉ L := D.cfg.z_not_mem_A
  have hgood : ∀ g h : G, ∀ (hg : g ∈ Hc) (hh : h ∈ Hc), θ ⟨g, hg⟩ ∈ J → θ ⟨h, hh⟩ ∈ J →
      g * h = h * g := by
    intro g h hg hh hgJ hhJ
    have hc : θ (⟨g, hg⟩ * ⟨h, hh⟩ * ⟨g, hg⟩⁻¹ * ⟨h, hh⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hJ.comm _ hgJ _ hhJ]
      group
    have h1 := (D.ker _).1 hc
    have h2 : g * h * g⁻¹ * h⁻¹ ∈ L := D.cfg.commutator_mem hg hh
    rcases mem_zpowers_involution D.cfg.z_sq h1 with h3 | h3
    · have h4 : g * h * g⁻¹ * h⁻¹ = 1 := h3
      calc g * h = (g * h * g⁻¹ * h⁻¹) * (h * g) := by group
        _ = h * g := by rw [h4, one_mul]
    · exact absurd (h3 ▸ h2 : z ∈ L) hzL
  have hEc : ∀ a ∈ E, ∀ c ∈ E, a * c = c * a := by
    intro a ha c hc
    obtain ⟨h1, -, h2⟩ := (hmemE a).1 ha
    obtain ⟨h3, -, h4⟩ := (hmemE c).1 hc
    exact hgood a c h1 h3 h2 h4
  have hEs : ∀ a ∈ E, a * a = 1 := by
    intro a ha
    obtain ⟨h1, -, h2⟩ := (hmemE a).1 ha
    have hc : θ (⟨a, h1⟩ * ⟨a, h1⟩) = 1 := by
      rw [map_mul]
      exact hJ.sq _ h2
    rcases mem_zpowers_involution D.cfg.z_sq ((D.ker _).1 hc) with h3 | h3
    · exact h3
    · exact absurd h3 (hzsq a)
  have hrangeE : (D.thetaOn hEH).range = J := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      obtain ⟨h1, -, h2⟩ := (hmemE (w : G)).1 w.2
      exact h2
    · intro j hj
      obtain ⟨x, hx, hxj⟩ := hJ.le hj
      have hxE : (x : G) ∈ E := (hmemE _).2 ⟨x.2, hx, by
        rw [show (⟨(x : G), x.2⟩ : ↥Hc) = x from rfl, hxj]
        exact hj⟩
      exact ⟨⟨(x : G), hxE⟩, hxj⟩
  have hEcard : Nat.card E = 64 := by
    have := D.card_eq_two_mul_range hEH hzE
    rw [hrangeE, hJ.card] at this
    omega
  have hT1 : ∀ W' : Subgroup G, W' ≤ T → (∀ a ∈ W', ∀ c ∈ W', a * c = c * a) →
      (∀ a ∈ W', a * a = 1) → Nat.card W' = 64 → W' = E := by
    intro W' hWT hWc hWs hWcard
    have hWH : W' ≤ Hc := hWT.trans hTH
    have hge := D.card_le_two_mul_range hWH
    have hR : (D.thetaOn hWH).range = J := by
      refine hJ.unique _ (D.range_le hWT) ?_ ?_ (by omega)
      · rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
        show D.thetaOn hWH a * D.thetaOn hWH c = D.thetaOn hWH c * D.thetaOn hWH a
        rw [← map_mul, ← map_mul]
        exact congrArg _ (Subtype.ext (hWc a a.2 c c.2))
      · rintro _ ⟨a, rfl⟩
        show D.thetaOn hWH a * D.thetaOn hWH a = 1
        have h1 : a * a = 1 := Subtype.ext (hWs a a.2)
        rw [← map_mul, h1, map_one]
    have hWE : W' ≤ E := by
      intro w hw
      have hwH : w ∈ Hc := hWH hw
      refine (hmemE w).2 ⟨hwH, (D.mem_T_iff hwH).1 (hWT hw), ?_⟩
      have : θ ⟨w, hwH⟩ ∈ (D.thetaOn hWH).range := ⟨⟨w, hw⟩, rfl⟩
      rwa [hR] at this
    exact Subgroup.eq_of_le_of_card_ge hWE (by rw [hWcard, hEcard])
  have hT2 : ∀ V : Subgroup G, V ≤ T → (∀ s ∈ T, ∀ v ∈ V, s * v * s⁻¹ ∈ V) →
      (∀ a ∈ V, ∀ c ∈ V, a * c = c * a) → (∀ a ∈ V, a * a = 1) → Nat.card V = 32 →
      z ∈ V → Nat.card ↥(V ⊓ E) ≤ 8 → V = liftSub F ⊔ zpowers z := by
    intro V hVT hVn hVc hVs hVcard hzV hVE
    have hVH : V ≤ Hc := hVT.trans hTH
    set R := (D.thetaOn hVH).range with hRdef
    have hR16 : Nat.card R = 16 := by
      have := D.card_eq_two_mul_range hVH hzV
      rw [← hRdef] at this
      omega
    have hRS : R ≤ T₁.map θ := D.range_le hVT
    have hRn : ∀ α ∈ T₁.map θ, ∀ β ∈ R, α * β * α⁻¹ ∈ R := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨v, rfl⟩
      have hxT : (x : G) ∈ T := ⟨x, hx, rfl⟩
      have hv' := hVn (x : G) hxT (v : G) v.2
      refine ⟨⟨(x : G) * (v : G) * (x : G)⁻¹, hv'⟩, ?_⟩
      show θ ⟨(x : G) * (v : G) * (x : G)⁻¹, _⟩ = θ x * θ ⟨(v : G), hVH v.2⟩ * (θ x)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have hRc : ∀ α ∈ R, ∀ β ∈ R, α * β = β * α := by
      rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
      show D.thetaOn hVH a * D.thetaOn hVH c = D.thetaOn hVH c * D.thetaOn hVH a
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (hVc a a.2 c c.2))
    have hRs : ∀ α ∈ R, α * α = 1 := by
      rintro _ ⟨a, rfl⟩
      show D.thetaOn hVH a * D.thetaOn hVH a = 1
      have h1 : a * a = 1 := Subtype.ext (hVs a a.2)
      rw [← map_mul, h1, map_one]
    have hVEH : V ⊓ E ≤ Hc := inf_le_left.trans hVH
    have hzVE : z ∈ V ⊓ E := Subgroup.mem_inf.2 ⟨hzV, hzE⟩
    have hRJ : Nat.card ↥(R ⊓ J) ≤ 4 := by
      have h1 := D.card_eq_two_mul_range hVEH hzVE
      have hle : R ⊓ J ≤ (D.thetaOn hVEH).range := by
        intro β hβ
        obtain ⟨hβR, hβJ⟩ := Subgroup.mem_inf.1 hβ
        obtain ⟨v, rfl⟩ := hβR
        have hvE : (v : G) ∈ E := (hmemE _).2 ⟨hVH v.2, (D.mem_T_iff _).1 (hVT v.2), hβJ⟩
        exact ⟨⟨(v : G), Subgroup.mem_inf.2 ⟨v.2, hvE⟩⟩, rfl⟩
      have h2 := Subgroup.card_le_of_le hle
      omega
    have hReq : R = innerImage (L ⧸ center L) F :=
      hJ.normal_E16 R hRS hRn hRc hRs hR16 hRJ
    have hVle : V ≤ liftSub F ⊔ zpowers z := by
      intro v hv
      have hvH : v ∈ Hc := hVH hv
      have hθv : θ ⟨v, hvH⟩ ∈ innerImage (L ⧸ center L) F := by
        rw [← hReq]
        exact ⟨⟨v, hv⟩, rfl⟩
      obtain ⟨f, hf, hfv⟩ := hθv
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective f
      have hlH : (l : G) ∈ Hc := D.l_mem_H l.2
      have h1 : θ ⟨(l : G), hlH⟩ = θ ⟨v, hvH⟩ := by
        rw [D.theta_conj l]
        exact hfv
      have h2 : (⟨(l : G), hlH⟩ : ↥Hc)⁻¹ * ⟨v, hvH⟩ ∈ θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      have h3 : (l : G)⁻¹ * v ∈ zpowers z := (D.ker _).1 h2
      have hlF : (l : G) ∈ liftSub F := mem_liftSub.2 ⟨l, rfl, hf⟩
      have : v = (l : G) * ((l : G)⁻¹ * v) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlF) (Subgroup.mem_sup_right h3)
    have hE1 : Nat.card ↥(liftSub F ⊔ zpowers z : Subgroup G) = 32 := D.card_E1 hF16
    exact Subgroup.eq_of_le_of_card_ge hVle (by rw [hVcard, hE1])
  obtain ⟨b₀, hb₀2, hb₀F, hb₀J⟩ := hJ.exists_b
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective b₀
  have hlH : (l : G) ∈ Hc := D.l_mem_H l.2
  have hl2 : (l : G) * (l : G) = 1 := by
    have h1 : ((l * l : L) : L ⧸ center L) = ((1 : L) : L ⧸ center L) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_one]
      exact hb₀2
    have h2 := D.mk_injective h1
    simpa using congrArg Subtype.val h2
  have hl1 : (l : G) ≠ 1 := by
    intro h1
    apply hb₀F
    have : l = 1 := Subtype.ext h1
    rw [this, QuotientGroup.mk_one]
    exact Subgroup.one_mem _
  have hlF : (l : G) ∉ liftSub F := by
    intro h1
    obtain ⟨l', hl', hl'F⟩ := mem_liftSub.1 h1
    rw [show l' = l from Subtype.ext hl'] at hl'F
    exact hb₀F hl'F
  have hbθ : θ ⟨(l : G), hlH⟩ ∈ J := by
    rw [D.theta_conj l]
    exact hb₀J
  have hbT : (⟨(l : G), hlH⟩ : ↥Hc) ∈ T₁ := by
    obtain ⟨x, hx, hxj⟩ := hJ.le hbθ
    exact D.mem_T₁_of_theta hx hxj.symm
  have hbE : (l : G) ∈ E := (hmemE _).2 ⟨hlH, hbT, hbθ⟩
  have hsurj : ∀ j ∈ J, ∃ (e : G) (he : e ∈ centralizer ({z} : Set G)), e ∈ E ∧
      thetaH D.cfg.cent_le ⟨e, he⟩ = j := by
    intro j hj
    have : j ∈ (D.thetaOn hEH).range := hrangeE ▸ hj
    obtain ⟨w, hw⟩ := this
    exact ⟨(w : G), hEH w.2, w.2, hw⟩
  exact ⟨E, l, hET, hEc, hEs, hEcard, hzE, hT1, hT2, l.2, hl2, hl1, hlF, hbE, hsurj⟩

end OutData

end CFSG.EvenSporadicStandard.M22Std
