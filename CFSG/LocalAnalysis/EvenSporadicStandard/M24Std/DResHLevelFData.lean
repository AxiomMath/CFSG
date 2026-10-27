module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSF
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResHLevelC

public section

namespace CFSG.EvenSporadicStandard.M24Std.DResH

open Subgroup CFSG.EvenSporadicStandard.M24Std.DRes

namespace LevelF

variable {N : Type} [Group N] (C' : Subgroup N) [C'.Normal]

@[expose] def conjAction (hC2 : ∀ c ∈ C', ∀ c' ∈ C', c * c' = c' * c) : (N ⧸ C') →* MulAut C' :=
  QuotientGroup.lift C' (MulAut.conjNormal : N →* MulAut C') (fun c hc =>
    (MonoidHom.mem_ker).2 (MulEquiv.ext fun h => Subtype.ext (by
      simp only [MulAut.conjNormal_apply, MulAut.one_apply]
      rw [hC2 c hc h h.2, mul_inv_cancel_right])))

theorem conjAction_coe (hC2 : ∀ c ∈ C', ∀ c' ∈ C', c * c' = c' * c) (n : N) (v : C') :
    ((conjAction C' hC2 (n : N ⧸ C') v : C') : N) = n * v * n⁻¹ := by
  simp only [conjAction, QuotientGroup.lift_mk, MulAut.conjNormal_apply]

end LevelF

open LevelC LevelF

theorem levelFData_of_levelC
    {N : Type} [Group N] [Finite N] (C' : Subgroup N) [C'.Normal]
    (hC2 : ∀ c ∈ C', ∀ c' ∈ C', c * c' = c' * c) (hCe : ∀ c ∈ C', c * c = 1)
    (hCcard : Nat.card C' = 2 ^ 12)
    {S1 S2 Z1 Z2 : Subgroup (N ⧸ C')} {π1 : S1 →* alternatingGroup (Fin 6)}
    {π2 : S2 →* alternatingGroup (Fin 6)}
    (q1 : DRes.QuasiData S1 Z1 π1) (q2 : DRes.QuasiData S2 Z2 π2)
    (hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a)
    (z : N) (hz : z * z = 1)
    (hts : ∀ a ∈ S1, (z : N ⧸ C') * a * (z : N ⧸ C')⁻¹ ∈ S2)
    (hts' : ∀ a ∈ S2, (z : N ⧸ C') * a * (z : N ⧸ C')⁻¹ ∈ S1)
    (z1 : N ⧸ C') (hz1 : z1 ∈ Z1) (hz1ne : z1 ≠ 1)
    (hz2 : (z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹ ∈ Z2)
    (hfpf : ∀ n : N, (n : N ⧸ C') = z1 * ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) →
      ∀ c ∈ C', n * c * n⁻¹ = c → c = 1)
    (c d : N ⧸ C') (hc : c ∈ S2) (hd : d ∈ S2) (hc3 : c * c * c = 1) (hd3 : d * d * d = 1)
    (hcd : c * d * c⁻¹ * d⁻¹ = (z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) :
    ∃ D1 D2 : Subgroup N, Nat.card D1 = 2 ^ 6 ∧
      DRes.LevelFData C' S1 S2 D1 D2 z ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) := by
  let _ : CommGroup ↥C' := { (inferInstance : Group ↥C') with
    mul_comm := fun a b => Subtype.ext (hC2 _ a.2 _ b.2) }
  have hV2 : ∀ v : ↥C', v * v = 1 := fun v => Subtype.ext (hCe v v.2)
  let ρ : (N ⧸ C') →* MulAut ↥C' := conjAction C' hC2
  have hρc : ∀ (n : N) (v : ↥C'), ((ρ (n : N ⧸ C') v : ↥C') : N) = n * v * n⁻¹ :=
    conjAction_coe C' hC2
  have ht : (z : N ⧸ C') * (z : N ⧸ C') = 1 := by
    rw [← QuotientGroup.mk_mul, hz]
    rfl
  have hfpf' : ∀ v : ↥C', ρ (z1 * ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹)) v = v → v = 1 := by
    intro v hv
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (z1 * ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹))
    rw [← hn] at hv
    have h1 : n * (v : N) * n⁻¹ = v := by
      rw [← hρc n v]
      exact congrArg Subtype.val hv
    exact Subtype.ext (hfpf n hn v v.2 h1)
  obtain ⟨D1, D2, hD1c, hD2c, hinf, hsup, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    levelC hV2 hCcard ρ q1 q2 hcomm (z : N ⧸ C') ht hts hts' z1 hz1 hz1ne hz2 hfpf' c d hc hd
      hc3 hd3 hcd
  have hz2S : (z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹ ∈ S2 := q2.Z_le hz2
  have hz1S : z1 ∈ S1 := q1.Z_le hz1
  have hD2inv : ∀ w ∈ D2, ρ ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) w ∈ D2 := by
    intro w hw
    apply h8
    intro s hs
    have hsz : s * ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) =
        ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) * s := hcomm s hs _ hz2S
    calc ρ s (ρ ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) w)
        = ρ (s * ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹)) w :=
          (Fixed.rho_mul_apply ρ s _ w).symm
      _ = ρ (((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) * s) w := by rw [hsz]
      _ = ρ ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) (ρ s w) := Fixed.rho_mul_apply ρ _ s w
      _ = ρ ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) w := by rw [h6 s hs w hw]
  refine ⟨D1.map C'.subtype, D2.map C'.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective C'.subtype_injective, hD1c]
  · refine
      { card_C := ?_, D1_le := ?_, D2_le := ?_, prod := ?_, inf := ?_, comm12 := ?_,
        comm := hcomm, perf1 := q1.perfect, S12 := h13, triv1 := ?_, triv2 := ?_, fpf1 := ?_,
        z2_mem := hz2S, z2_cube := cube_eq_one_of_card_three q2.card_Z hz2, z2_ne := ?_,
        fpf2 := ?_, z_sq := hz, zD := ?_, zD' := ?_, zS12 := hts, zS21 := hts' }
    · rw [hCcard]
      norm_num
    · exact Subgroup.map_subtype_le D1
    · exact Subgroup.map_subtype_le D2
    · intro x hx
      have hmem : (⟨x, hx⟩ : ↥C') ∈ D1 ⊔ D2 := by rw [hsup]; trivial
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hmem
      exact ⟨a, ⟨a, ha, rfl⟩, b, ⟨b, hb, rfl⟩, (congrArg Subtype.val hab).symm⟩
    · rw [← Subgroup.map_inf_eq _ _ _ C'.subtype_injective, hinf, Subgroup.map_bot]
    · intro a ha b hb
      exact hC2 a (Subgroup.map_subtype_le D1 ha) b (Subgroup.map_subtype_le D2 hb)
    · intro g hg d hd
      obtain ⟨v, hv, rfl⟩ := hd
      have h1 : g * (v : N) * g⁻¹ = v := by
        rw [← hρc g v]
        exact congrArg Subtype.val (h6 _ hg v hv)
      exact mul_inv_eq_iff_eq_mul.1 h1
    · intro g hg d hd
      obtain ⟨v, hv, rfl⟩ := hd
      have h1 : g * (v : N) * g⁻¹ = v := by
        rw [← hρc g v]
        exact congrArg Subtype.val (h5 _ hg v hv)
      exact mul_inv_eq_iff_eq_mul.1 h1
    · obtain ⟨g1, hg1⟩ := QuotientGroup.mk_surjective z1
      refine ⟨g1, by rw [hg1]; exact hz1S, ?_⟩
      intro d hd
      obtain ⟨v, hv, rfl⟩ := hd
      obtain ⟨w, hw, hwv⟩ := h9 v hv
      refine ⟨w, ⟨w, hw, rfl⟩, ?_⟩
      have h1 : ((ρ z1 w : ↥C') : N) = g1 * w * g1⁻¹ := by
        rw [← hg1]
        exact hρc g1 w
      have h2 := congrArg Subtype.val hwv
      show g1 * (w : N) * g1⁻¹ * (w : N)⁻¹ = v
      rw [← h1]
      exact h2
    · intro h
      apply hz1ne
      calc z1 = (z : N ⧸ C')⁻¹ * ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) * (z : N ⧸ C') := by group
        _ = 1 := by rw [h]; group
    · intro g hg d hd hgd
      obtain ⟨v, hv, rfl⟩ := hd
      have hρv : ρ ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) v = v := by
        rw [← hg]
        apply Subtype.ext
        rw [hρc g v]
        exact hgd
      let φ : ↥D2 → ↥D2 := fun w => ⟨ρ ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) w * (w : ↥C')⁻¹,
        D2.mul_mem (hD2inv w w.2) (D2.inv_mem w.2)⟩
      have hsurj : Function.Surjective φ := by
        intro u
        obtain ⟨w, hw, hwu⟩ := h10 u u.2
        exact ⟨⟨w, hw⟩, Subtype.ext hwu⟩
      have hinj := Finite.injective_iff_surjective.2 hsurj
      have h1 : φ ⟨v, hv⟩ = φ 1 := by
        apply Subtype.ext
        show ρ ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) v * (v : ↥C')⁻¹ =
          ρ ((z : N ⧸ C') * z1 * (z : N ⧸ C')⁻¹) 1 * (1 : ↥C')⁻¹
        rw [hρv, mul_inv_cancel, map_one, inv_one, mul_one]
      have hv1 : v = 1 := congrArg Subtype.val (hinj h1)
      rw [hv1]
      rfl
    · intro d hd
      obtain ⟨v, hv, rfl⟩ := hd
      exact ⟨ρ (z : N ⧸ C') v, h11 v hv, hρc z v⟩
    · intro d hd
      obtain ⟨v, hv, rfl⟩ := hd
      exact ⟨ρ (z : N ⧸ C') v, h12 v hv, hρc z v⟩

end CFSG.EvenSporadicStandard.M24Std.DResH
