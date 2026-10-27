module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelTorusNum
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalToralBasic
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Main
public import CFSG.ClassicalInvolution.RouteD.TypeE8Block
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutWitt
public import CFSG.ClassicalInvolution.RouteD.GapsChainConfig
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBAdapt
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakNodes
public import CFSG.ClassicalInvolution.RouteD.TypeEAdapt
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorGeom
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternToral

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.ModelFacts.ChevAut
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Generic

section Diag

variable {F : Type} [Field F]

theorem torus_fixed_of_A1A4 [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (hq : 5 ≤ Nat.card F) {X : Type} [Group X] (f : ↥(e7Data_valid.minGroup F) →* X)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center ↥(e7Data_valid.minGroup F))
    (σ : X ≃* X)
    (H1 : ∀ y ∈ (e7Datum F).rootGroup θE7 ⊔ (e7Datum F).rootGroup (-θE7), σ (f y) = f y)
    (H4 : ∀ j : Fin 7, (j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) →
      ∀ y ∈ rankOne (e7Datum F).rootGroup j, σ (f y) = f y) (j : Fin 7) (s : Fˣ) :
    σ (f (torusGen (e7Data_valid.xm F) j s)) = f (torusGen (e7Data_valid.xm F) j s) := by
  have hS := torusSetup_E7 F
  have hfin := finite_minGroup e7Data_valid F
  obtain ⟨α, g, a, φ, ε, hαθ, h⟩ := excAut_E7 (p := p) f hf hker σ
  have hN : NormalForm (e7Data_valid.xm F) α.toMonoidHom g a φ
      (1 : Equiv.Perm (Fin (e7Datum F).rank)) :=
    ⟨fun i c => (h i c).1, fun i c => (h i c).2⟩
  have hZ : ∀ t, σ (f t) = f t → t ∈ Zfix α.toMonoidHom := fun t ht =>
    mem_Zfix.2 (mul_inv_mem_center_of_fix f hker σ α.toMonoidHom hαθ ht)
  have hnode : ∀ j : Fin 7, (j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) → ∀ s : Fˣ,
      tdir (e7Data_valid.xm F) (Pi.single j 1) s ∈ Zfix α.toMonoidHom := fun j hj s =>
    tdir_single_mem_Zfix hS j s
      (hZ _ (H4 j hj _ (hS.ct.H_le j ((hS.H_iff j _).2 ⟨s, rfl⟩))))
  have hfix : ∀ (i : Fin 5) (s : Fˣ),
      α.toMonoidHom (tdir (e7Data_valid.xm F) (cvec5 i) s) *
        (tdir (e7Data_valid.xm F) (cvec5 i) s)⁻¹ ∈ Subgroup.center ↥(e7Data_valid.minGroup F) := by
    intro i s
    refine mem_Zfix.1 ?_
    fin_cases i
    · exact hnode 3 (Or.inl rfl) s
    · exact hnode 4 (Or.inr (Or.inl rfl)) s
    · exact hnode 5 (Or.inr (Or.inr (Or.inl rfl))) s
    · exact hnode 6 (Or.inr (Or.inr (Or.inr rfl))) s
    · exact tdir_theta_mem_Zfix hS (fun k => isLongest_single_E7 rfl _ k) (θE7_mem_roots F) α
        (fun y hy => hZ y (H1 y hy)) s
  have hnum := e7_char_num (F := F) hp2 hq
  have hc := e7_hc (F := F)
  have hb' := exists_diag_of_fixes_fam (D := e7Datum F) (x := e7Data_valid.xm F)
    (n := e7Data_valid.nm F) (H := e7Data_valid.torus F) cvec5 hS hq hc hnum hN
  obtain ⟨b, hb⟩ := hb' hfix
  have h1 := alpha_torusGen_eq_of_diag hS hb j s
  rw [← hαθ]
  exact congrArg f h1

end Diag

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem e7A1A4Toral_sc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    ∀ (Y : Type) [Group Y] (ψ : E7sc p f →* Y), ψ.ker ≤ Subgroup.center (E7sc p f) →
      ∀ σ : Y ≃* Y, (∀ y, σ (σ y) = y) → (∀ k, σ (ψ k) ∈ ψ.range) → ∀ k₀ : E7sc p f,
        (∀ y ∈ (e7Datum (GaloisField p f)).rootGroup θE7 ⊔
            (e7Datum (GaloisField p f)).rootGroup (-θE7),
          σ (ψ (k₀ * y * k₀⁻¹)) = ψ (k₀ * y * k₀⁻¹)) →
        (∀ i : Fin 4, ∀ y ∈ rankOne (e7Datum (GaloisField p f)).rootGroup
            ((![6, 5, 4, 3] : Fin 4 → Fin 7) i),
          σ (ψ (k₀ * y * k₀⁻¹)) = ψ (k₀ * y * k₀⁻¹)) →
        ∀ j : Fin 7, j ≠ 0 → ∀ h ∈ e7Data_valid.torus (GaloisField p f) j,
          σ (ψ (k₀ * h * k₀⁻¹)) = ψ (k₀ * h * k₀⁻¹) := by
  intro Y _ ψ hψ σ hσ2 hσr k₀ H1 H4 j _ h hh
  obtain ⟨-, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have hS := torusSetup_E7 (GaloisField p f)
  obtain ⟨s, rfl⟩ := (hS.H_iff j h).1 hh
  set θ₁ : E7sc p f →* Y := ψ.comp (MulAut.conj k₀).toMonoidHom with hθ₁
  have hθ₁ap : ∀ k, θ₁ k = ψ (k₀ * k * k₀⁻¹) := fun k => rfl
  have hrange : ∀ k, ψ k ∈ θ₁.range := fun k => ⟨k₀⁻¹ * k * k₀, by
    rw [hθ₁ap]
    congr 1
    group⟩
  have hσR : ∀ r ∈ θ₁.range, σ r ∈ θ₁.range := by
    rintro r ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ := hσr (k₀ * k * k₀⁻¹)
    rw [hθ₁ap, ← hk']
    exact hrange k'
  let σR : θ₁.range ≃* θ₁.range :=
    { toFun := fun r => ⟨σ r, hσR r r.2⟩
      invFun := fun r => ⟨σ r, hσR r r.2⟩
      left_inv := fun r => Subtype.ext (hσ2 r)
      right_inv := fun r => Subtype.ext (hσ2 r)
      map_mul' := fun a b => Subtype.ext (map_mul σ (a : Y) (b : Y)) }
  have hkerθ : θ₁.rangeRestrict.ker ≤ Subgroup.center (E7sc p f) := by
    intro y hy
    have h1 : θ₁ y = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
    have hz : k₀ * y * k₀⁻¹ ∈ Subgroup.center (E7sc p f) :=
      hψ (MonoidHom.mem_ker.2 (by rwa [hθ₁ap] at h1))
    have hy' : y = k₀ * y * k₀⁻¹ := by
      have := Subgroup.mem_center_iff.1 hz k₀⁻¹
      calc y = k₀⁻¹ * (k₀ * y * k₀⁻¹) * k₀ := by group
        _ = (k₀ * y * k₀⁻¹) * k₀⁻¹ * k₀ := by rw [this]
        _ = k₀ * y * k₀⁻¹ := by group
    rw [hy']
    exact hz
  have hchar : CharP (GaloisField p f) p := inferInstance
  have key := torus_fixed_of_A1A4 (F := GaloisField p f) (p := p) hp2 h5 θ₁.rangeRestrict
    θ₁.rangeRestrict_surjective hkerθ σR (fun y hy => Subtype.ext (H1 y hy))
    (fun j' hj' y hy => Subtype.ext (by
      rcases hj' with rfl | rfl | rfl | rfl
      · exact H4 3 y hy
      · exact H4 2 y hy
      · exact H4 1 y hy
      · exact H4 0 y hy)) j s
  exact congrArg Subtype.val key

theorem e7A1A4Toral (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    CFSG.ClassicalInvolution.RouteD.TypeE8.E7A1A4Toral p f :=
  e7A1A4Toral_sc hp2 hq

end Main

end CFSG.ClassicalInvolution.ModelFacts.E7Model
