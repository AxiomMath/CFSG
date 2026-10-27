module

public import CFSG.ClassicalInvolution.Q3.TL4S3DichD
public import CFSG.ClassicalInvolution.Q3.TL4S3DichG
public import CFSG.ClassicalInvolution.Q3.TL4S3DichU
public import CFSG.ClassicalInvolution.Q3.TL4SecIdMu

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Q3.TL4.S3Dich

namespace S3Dich

theorem invDich_of_q8Shape {c : CompData} (hZ : Subgroup.center c.G = ⊥)
    (hrow : ∀ R ∈ c.fund, ∀ L₀ : Subgroup c.G, IsSylow2In L₀ R → InvDich c.G L₀)
    {X : Type} [Group X] {Φ : Set (Subgroup X)} (h : SecIdQ8Shape c Φ) {L : Subgroup X}
    (hL : L ∈ Φ) : InvDich X L := by
  obtain ⟨ψ, hsurj, hker, hfund⟩ := h
  obtain ⟨R, hR, hLR⟩ := hfund L hL
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  set e : c.G ≃* X := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩ with he
  have hRe : (R.map ψ).map e.symm.toMonoidHom = R := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id R
    ext x
    exact e.symm_apply_apply x
  have h1 := isSylow2In_map e.symm hLR
  rw [hRe] at h1
  have h2 := (hrow R hR _ h1).map e
  have hL' : (L.map e.symm.toMonoidHom).map e.toMonoidHom = L := by
    rw [Subgroup.map_map]
    ext x
    simp
  rwa [hL'] at h2

theorem center_psu3_model : Subgroup.center (CompData.model .PSU 3).G = ⊥ := by
  obtain ⟨e', -⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num)
    (show CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 3 3 1 from
      ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩)
  rw [eq_bot_iff]
  intro x hx
  have h1 : e' x ∈ Subgroup.center Q3PP.SU3 := by
    rw [← Subgroup.map_center_eq e']
    exact ⟨x, hx, rfl⟩
  rw [Q3PP.center_su3_eq_bot, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (e'.injective (by rw [h1, map_one]))

end S3Dich

theorem secIdS3Dich3_proved :
    ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), SecIdLieS3 Φ → ∀ L ∈ Φ, ∀ a : X,
      IsUniqueInvolution L a → ∀ β : MulAut X, β * β = 1 → (∀ x ∈ L, β x = x) →
        β = 1 ∨ β = MulAut.conj a := by
  intro X _ _ Φ hΦ L hL a ha β hβ2 hβL
  have hD : InvDich X L := by
    rcases hΦ with h | h | h
    · exact invDich_of_q8Shape center_psu3_model (fun R hR L₀ hL₀ => invDich_psu3 hR hL₀) h hL
    · exact invDich_of_q8Shape
        (RouteD.G2D4.center_modelUniv_g2d4_eq_bot (p := 3) (by norm_num) (Or.inl rfl) 0 le_rfl)
        (fun R hR L₀ hL₀ => invDich_g2 (p := 3) (by norm_num) (e := 1) le_rfl (by norm_num)
          hR hL₀) h hL
    · exact invDich_of_q8Shape
        (RouteD.G2D4.center_modelUniv_g2d4_eq_bot (p := 3) (by norm_num) (Or.inr rfl) 0 le_rfl)
        (fun R hR L₀ hL₀ => invDich_td4 (p := 3) (by norm_num) (e := 1) le_rfl odd_one hR hL₀)
        h hL
  obtain ⟨k, hkL, hk2, hβk⟩ := hD β hβ2 hβL
  rcases ha.unique k hkL hk2 with rfl | rfl
  · left
    rw [hβk, map_one]
  · right
    exact hβk

end CFSG.ClassicalInvolution.Q3.TL4
