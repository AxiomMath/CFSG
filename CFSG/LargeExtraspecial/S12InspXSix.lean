module

public import CFSG.LargeExtraspecial.S12InspXOrd
public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.Timmesfeld.Transvection.QTwoSp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Equiv Equiv.Perm
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open scoped commutatorElement

namespace S12Insp4

@[expose] def cyc₁ : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def cyc₂ : Perm (Fin 6) := swap 2 3 * swap 3 4

theorem cyc₁_mem : cyc₁ ∈ alternatingGroup (Fin 6) := mem_alternatingGroup.mpr (by decide)

theorem cyc₂_mem : cyc₂ ∈ alternatingGroup (Fin 6) := mem_alternatingGroup.mpr (by decide)

theorem eq_one_of_commute_six :
    ∀ σ : Perm (Fin 6), σ * cyc₁ = cyc₁ * σ → σ * cyc₂ = cyc₂ * σ → σ = 1 := by
  decide +kernel

theorem nonempty_mulEquiv_perm_six_of_sp {H : Type} [Group H] {D : Set H}
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * 2) → ZMod 2)} (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hmod : CFSG.Open.fischerLinearModel D
      (CFSG.Open.fischerMatrixGroup fun A => ∀ x y, b (A.mulVec x) (A.mulVec y) = b x y)
      (CFSG.Open.fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    Nonempty (H ≃* Perm (Fin 6)) := by
  obtain ⟨φ, hφ⟩ := hmod
  obtain ⟨ψ, -⟩ := CFSG.Timmesfeld.Transvection.QTwo.exists_sympEquiv_of_isometry b halt hnd φ hφ
  let ω : CFSG.ComponentClassification.PresentationLocal.sympFour ≃* Perm (Fin 6) :=
    MulEquiv.ofBijective CFSG.ComponentClassification.PresentationLocal.omegaPerm
      ⟨CFSG.ComponentClassification.PresentationLocal.omegaPerm_injective,
        CFSG.ComponentClassification.PresentationLocal.omegaPerm_surjective⟩
  let ρ : CFSG.ComponentClassification.PresentationLocal.sympFour ≃*
      TauCeti.GLSymplectic (Fin 2) (ZMod 2) :=
    (CFSG.Timmesfeld.Transvection.QTwo.glFourEquiv.subgroupMap _).trans
      (MulEquiv.subgroupCongr CFSG.Timmesfeld.Transvection.QTwo.map_sympFour)
  exact ⟨ψ.trans (ρ.symm.trans ω)⟩

end S12Insp4

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_mulEquiv_perm_six {g : G} {t : S.O} (hS : S.S12Standing g t)
    (hM : 25920 ∣ Nat.card S.Mbar) (φ : S.Xbar12 g ≃* Perm (Fin 6)) : False := by
  set θ : Perm (Fin 6) →* S.O := (S.Xbar12 g).subtype.comp φ.symm.toMonoidHom with hθ
  have hθinj : Function.Injective θ := (subtype_injective _).comp φ.symm.injective
  have hX : S.Xbar12 g = (⊤ : Subgroup (Perm (Fin 6))).map θ := by
    ext x
    constructor
    · intro hx
      exact ⟨φ ⟨x, hx⟩, mem_top _, by simp [hθ]⟩
    · rintro ⟨y, -, rfl⟩
      simp [hθ]
  set N : Subgroup S.O := ⁅S.Xbar12 g, S.Xbar12 g⁆ with hN
  have hNmap : N = (alternatingGroup (Fin 6)).map θ := by
    rw [hN, hX, ← map_commutator, ← _root_.commutator_def,
      alternatingGroup.commutator_perm_eq (by simp)]
  have hNX : N ≤ S.Xbar12 g := commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hNM : N ≤ S.Mbar := hNX.trans Xbar12_le_Mbar
  have hkey : ∀ c ∈ S.Xbar12 g, c * θ S12Insp4.cyc₁ = θ S12Insp4.cyc₁ * c →
      c * θ S12Insp4.cyc₂ = θ S12Insp4.cyc₂ * c → c = 1 := by
    intro c hc h1 h2
    rw [hX] at hc
    obtain ⟨σ, -, rfl⟩ := hc
    rw [← map_mul, ← map_mul] at h1 h2
    rw [S12Insp4.eq_one_of_commute_six σ (hθinj h1) (hθinj h2), map_one]
  have hc₁ : θ S12Insp4.cyc₁ ∈ N := hNmap ▸ mem_map_of_mem θ S12Insp4.cyc₁_mem
  have hc₂ : θ S12Insp4.cyc₂ ∈ N := hNmap ▸ mem_map_of_mem θ S12Insp4.cyc₂_mem
  have hNorm : ∀ m ∈ S.Mbar, N.map (MulAut.conj m).toMonoidHom = N := by
    intro m hm
    have h1 : (S.Xbar12 g).map (MulAut.conj m).toMonoidHom = S.Xbar12 g :=
      mem_normalizer_iff_map_conj_eq.mp (Mbar_le_normalizer_Xbar12 hm)
    rw [hN, map_commutator, h1]
  have hconjN : ∀ m ∈ S.Mbar, ∀ n ∈ N, m * n * m⁻¹ ∈ N := fun m hm n hn => by
    rw [← hNorm m hm]
    exact ⟨n, hn, rfl⟩
  set N' : Subgroup S.Mbar := N.subgroupOf S.Mbar with hN'
  have hN'n : N'.Normal := ⟨fun n hn m => by
    rw [hN', mem_subgroupOf] at hn ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconjN m m.2 n hn⟩
  have hC : centralizer (N' : Set S.Mbar) = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have hmN : ∀ n ∈ N, (m : S.O) * n = n * m := fun n hn => by
      have h := mem_centralizer_iff.mp hm ⟨n, hNM hn⟩
        (show (⟨n, hNM hn⟩ : S.Mbar) ∈ N' from hn)
      exact (congrArg Subtype.val h).symm
    have hmX : (m : S.O) ∈ S.CXbar12 g := by
      refine ⟨m.2, mem_centralizer_iff.mpr fun x hx => ?_⟩
      have hxM := Xbar12_le_Mbar hx
      set c := (m : S.O) * x * (m : S.O)⁻¹ * x⁻¹ with hcdef
      have hcX : c ∈ S.Xbar12 g := mul_mem ((mem_normalizer_iff.mp
        (Mbar_le_normalizer_Xbar12 m.2) x).mp hx) (inv_mem hx)
      have hcN : ∀ n ∈ N, c * n = n * c := by
        intro n hn
        have hn' : x⁻¹ * n * x⁻¹⁻¹ ∈ N := hconjN x⁻¹ (inv_mem hxM) n hn
        rw [inv_inv] at hn'
        have hm' : (m : S.O)⁻¹ * (x⁻¹ * n * x) = (x⁻¹ * n * x) * (m : S.O)⁻¹ := by
          have := hmN _ hn'
          calc (m : S.O)⁻¹ * (x⁻¹ * n * x)
              = (m : S.O)⁻¹ * ((x⁻¹ * n * x) * (m : S.O)) * (m : S.O)⁻¹ := by group
            _ = (m : S.O)⁻¹ * ((m : S.O) * (x⁻¹ * n * x)) * (m : S.O)⁻¹ := by rw [this]
            _ = (x⁻¹ * n * x) * (m : S.O)⁻¹ := by group
        calc c * n = (m : S.O) * x * ((m : S.O)⁻¹ * (x⁻¹ * n * x)) * x⁻¹ := by
              rw [hcdef]; group
          _ = (m : S.O) * x * ((x⁻¹ * n * x) * (m : S.O)⁻¹) * x⁻¹ := by rw [hm']
          _ = (m : S.O) * n * x * (m : S.O)⁻¹ * x⁻¹ := by group
          _ = n * (m : S.O) * x * (m : S.O)⁻¹ * x⁻¹ := by rw [hmN n hn]
          _ = n * c := by rw [hcdef]; group
      have hc1 : c = 1 := hkey c hcX (hcN _ hc₁) (hcN _ hc₂)
      calc x * (m : S.O) = c⁻¹ * ((m : S.O) * x) := by rw [hcdef]; group
        _ = (m : S.O) * x := by rw [hc1, inv_one, one_mul]
    rw [hS.cent, mem_bot] at hmX
    exact (mem_bot).mpr (Subtype.ext hmX)
  have hZ : center N' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzN : ((z : S.Mbar) : S.O) ∈ N := z.2
    have hcomm : ∀ n (hn : n ∈ N), n * (z : S.Mbar) = (z : S.Mbar) * n := fun n hn => by
      have h := mem_center_iff.mp hz ⟨⟨n, hNM hn⟩, hn⟩
      exact congrArg (fun w : N' => ((w : S.Mbar) : S.O)) h
    have h1 := hkey _ (hNX hzN) (hcomm _ hc₁).symm (hcomm _ hc₂).symm
    exact (mem_bot).mpr (Subtype.ext (Subtype.ext h1))
  have h := card_dvd_card_mul_card_outer_of_normal hC hZ
  let e : N' ≃* alternatingGroup (Fin 6) :=
    (subgroupOfEquivOfLe hNM).trans ((MulEquiv.subgroupCongr hNmap).trans
      (Subgroup.equivMapOfInjective _ _ hθinj).symm)
  have hcN : Nat.card N' = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
    (CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six.of_equiv (equivalence e).symm)
  have h3 : 3 ^ 4 ∣ 360 * 2 ^ k := by
    rw [← hcN, ← hk]
    exact ((by norm_num : 3 ^ 4 ∣ 25920).trans hM).trans h
  have hcop : Nat.Coprime (3 ^ 4) (2 ^ k) := Nat.Coprime.pow _ _ (by decide)
  exact absurd (hcop.dvd_of_dvd_mul_right h3) (by decide)

end Setting

end CFSG.LargeExtraspecial
