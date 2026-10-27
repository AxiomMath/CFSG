module

public import CFSG.CGT.PushingUpLit.C2L.SecondBlockData
public import CFSG.CGT.PushingUpLit.C2L.Defs
public import CFSG.CGT.PushingUpLit.C2L.NatQuad

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2KSW
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T D D₂ L₂ : Subgroup G} {n : ℕ} {a : G}

theorem centralizer_L₂_inf_D₂ (hin : SecondBlockInput G L M T n D D₂ a)
    (hf : BlockTwoFacts G (Subgroup.normalizer (D₂ : Set G)) D₂ T L₂ n) :
    D₂ ⊓ Subgroup.centralizer (L₂ : Set G) =
      zc T ⊓ (zc T).map (MulAut.conj a).toMonoidHom := by
  have hgen : L₂ = T ⊔ T.map (MulAut.conj a).toMonoidHom := hf.gen a hin.a_mem hin.a_not
  have hTaL : T.map (MulAut.conj a).toMonoidHom ≤ L₂ := hgen ▸ le_sup_right
  apply le_antisymm
  · rintro x ⟨hxD, hxC⟩
    have hxT : x ∈ T := hin.D₂_le hxD
    have hcL : ∀ l ∈ L₂, l * x = x * l := fun l hl => Subgroup.mem_centralizer_iff.1 hxC l hl
    refine ⟨⟨hxT, Subgroup.mem_centralizer_iff.2 fun t ht => hcL t (hf.T_le ht)⟩, ?_⟩
    have ha' : a⁻¹ ∈ Subgroup.normalizer (D₂ : Set G) := (Subgroup.normalizer _).inv_mem hin.a_mem
    have hxa : a⁻¹ * x * a⁻¹⁻¹ ∈ D₂ := (Subgroup.mem_normalizer_iff.1 ha' x).1 hxD
    rw [inv_inv] at hxa
    refine ⟨a⁻¹ * x * a, ⟨hin.D₂_le hxa, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩, ?_⟩
    · have h1 := hcL (a * t * a⁻¹) (hTaL ⟨t, ht, by simp [MulAut.conj_apply]⟩)
      calc t * (a⁻¹ * x * a) = a⁻¹ * ((a * t * a⁻¹) * x) * a := by group
        _ = a⁻¹ * (x * (a * t * a⁻¹)) * a := by rw [h1]
        _ = (a⁻¹ * x * a) * t := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro x ⟨hxX, hxX₂⟩
    refine ⟨hin.zc_le_D₂ hxX, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have hle : L₂ ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [hgen]
      refine sup_le (fun t ht => ?_) ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 hxX.2) t ht
      · rintro _ ⟨t, ht, rfl⟩
        obtain ⟨y, hy, rfl⟩ := hxX₂
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := (Subgroup.mem_centralizer_iff.1 hy.2) t ht
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc a * t * a⁻¹ * (a * y * a⁻¹) = a * (t * y) * a⁻¹ := by group
          _ = a * (y * t) * a⁻¹ := by rw [h1]
          _ = a * y * a⁻¹ * (a * t * a⁻¹) := by group
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hl)

theorem isNatSL_second (hs : Sec4Core G L M T n) (hc : ClassLETwo T)
    (hin : SecondBlockInput G L M T n D D₂ a)
    (hf : BlockTwoFacts G (Subgroup.normalizer (D₂ : Set G)) D₂ T L₂ n) :
    BHS.IsNatSL L₂ D₂ n := by
  obtain ⟨φ, hφs, hφk, hφA⟩ := hf.quot
  have hn2 : 2 ≤ n := hs.hyp.two_le
  have hcentD₂ : Subgroup.centralizer (D₂ : Set G) ≤ D₂ :=
    GomiH.centralizer_le hs.hyp.charTwo hin.gomiH
  have hLD : L₂ ⊓ Subgroup.centralizer (D₂ : Set G) = D₂ :=
    le_antisymm (fun x hx => hcentD₂ hx.2) fun x hx =>
      ⟨hf.D_le hx, Subgroup.mem_centralizer_iff.2 fun y hy => hin.D₂_comm y hy x hx⟩
  have hZ := centralizer_L₂_inf_D₂ hin hf
  obtain ⟨x₀, hx₀X, hx₀X₂⟩ := hin.exists_zc_not_mem (by omega)
  refine isNatSL_of_quadratic hn2 φ hφs (by rw [hLD]; exact hφk)
    (fun x hx w hw => (Subgroup.mem_normalizer_iff.1 (hf.le_N hx) w).1 hw) hin.D₂_comm
    hf.T_le hφA ?_ (hin.zc_le_D₂ hx₀X) ?_ ?_ ?_
  · intro a' ha' a'' ha'' w hw
    have h1 : ⁅⁅a', w⁆, a''⁆ = 1 := hc a' ha' w (hin.D₂_le hw) a'' ha''
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  · intro a' ha'
    have h1 : a' * x₀ = x₀ * a' := Subgroup.mem_centralizer_iff.1 hx₀X.2 a' ha'
    have : a' * x₀ * a'⁻¹ * x₀⁻¹ = 1 := by
      rw [h1]
      group
    rw [this]
    exact Subgroup.one_mem _
  · rw [hZ]
    exact fun h => hx₀X₂ h.2
  · rw [hZ]
    exact hin.card_D₂

end CFSG.CGT.PushingUpLit.C2L
