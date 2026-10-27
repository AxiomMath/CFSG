module

public import CFSG.CGT.T75I.NHat
public import CFSG.Quasithin.Background.HA7Rec

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped Matrix

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem normalizer_le_of_seven [Finite G] (hC : Subgroup.centralizer (T : Set G) = T)
    (e : ↥T ≃* Multiplicative (Fin 4 → ZMod 2))
    (hiso : Nonempty (↥(hGamma T₁ e) ≃* alternatingGroup (Fin 7))) :
    Subgroup.normalizer (T : Set G) ≤ hSub T (normIn T₁ T) := by
  classical
  obtain ⟨eΓ⟩ := hiso
  have hcard : Nat.card ↥(hGamma T₁ e) = 2520 := by
    rw [Nat.card_congr eΓ.toEquiv]
    exact CFSG.Quasithin.H.A7.card_A7
  have hidx : (hGamma T₁ e).index = 8 := by
    have h := (hGamma T₁ e).index_mul_card
    rw [hcard, CFSG.GH74.Exceptional.card_GL_four_two] at h
    omega
  obtain ⟨α, hα⟩ := CFSG.Quasithin.H.A7.exists_alpha_of_index hidx
  have hle : CFSG.Quasithin.H.A7.Γ α ≤ hGamma T₁ e := by
    rintro _ ⟨σ, rfl⟩
    exact hα σ
  have heq : CFSG.Quasithin.H.A7.Γ α = hGamma T₁ e :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, CFSG.Quasithin.H.A7.card_Γ α])
  have hnorm' : Subgroup.normalizer (hGamma T₁ e : Set (GL (Fin 4) (ZMod 2))) =
      hGamma T₁ e := by
    rw [← heq]
    exact CFSG.Quasithin.H.A7.normalizer_eq α
  intro n hn
  have h1 := actGL_mem_normalizer_hGamma (T₁ := T₁) (e := e) ⟨n, hn⟩
  rw [hnorm'] at h1
  exact mem_hSub_of_actGL_mem hC ⟨n, hn⟩ h1

end CFSG.CGT.T75I
