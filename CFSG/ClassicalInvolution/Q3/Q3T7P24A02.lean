module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24A01
public import CFSG.ClassicalInvolution.Asc77.AscT7DFrame
public import CFSG.ClassicalInvolution.Asc77.AscT7DMu
public import CFSG.ClassicalInvolution.AschTight.Sec71Good2
public import CFSG.ClassicalInvolution.AschTight.Sec71Orbit
public import CFSG.ClassicalInvolution.Asc77.AscT7DPerm
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A02

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Conj
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem Hyp23Setting.conj (h : Hyp23Setting Ω K K' z) (g : G) :
    Hyp23Setting Ω (conjSub g K) (conjSub g K') (g * z * g⁻¹) where
  stand := h.stand.of_mem (h.stand.hyp.conjInvariant g K h.stand.mem)
  disconnected := h.disconnected
  hz := h.hz.conj g
  hK' := twinSet_conj h.stand.hyp.conjInvariant h.hK' g
  hne := fun e => h.hne ((conjSub_inj g).mp e)
  perp := by
    have hΩ := h.stand.hyp.conjInvariant
    ext J
    constructor
    · intro hJ
      have h1 : conjSub g⁻¹ J ∈ KPerp Ω (conjSub g⁻¹ (conjSub g K)) := KPerp_conj hΩ hJ g⁻¹
      rw [conjSub_inv_conjSub, h.perp] at h1
      have h2 : J = conjSub g (conjSub g⁻¹ J) := (conjSub_conjSub_inv g J).symm
      rcases h1 with e | e
      · exact Or.inl (h2.trans (congrArg (conjSub g) e))
      · exact Or.inr (h2.trans (congrArg (conjSub g) e))
    · rintro (rfl | rfl)
      · exact KPerp_conj hΩ (by rw [h.perp]; exact Or.inl rfl) g
      · exact KPerp_conj hΩ (by rw [h.perp]; exact Or.inr rfl) g
end Conj
namespace T7D
open CFSG.ClassicalInvolution.Asc77.T7D
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem muDelta_nonempty (hΩ : HypOmegaMod Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hW : W ∈ WSet Ω) : (Thompson.muDelta Ω W).Nonempty := by
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : Subgroup G, IsSylow2In R₀ K := by
    obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    exact ⟨R₀, hR₀⟩
  obtain ⟨S, hRS⟩ := hR₀.2.1.exists_le_sylow
  obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.Q3.Q3T7P24.exists_conj_mem_DSet hΩ hW S
  have hRD : conjSub g R₀ ∈ DSet Ω W := hg R₀ (mem_RSet_of_isSylow2In hK hR₀) hRS
  obtain ⟨ρ, -, -⟩ := exists_rep hΩ hW (hΩ.conjInvariant g K hK) (hR₀.conj g) hRD
  exact ⟨_, rep_mem_muDelta ρ⟩

theorem ncard_cent_le_two {K K' : Subgroup G} {z : G} (hs : Hyp23Setting Ω K K' z)
    (hW : W ∈ WSet Ω) {d : ↥(muGroup Ω W)} (hd : d ∈ Thompson.muDelta Ω W) :
    (Star3T.cent (Thompson.muDelta Ω W) d).ncard ≤ 2 := by
  have hst : AscStand Ω K := hs.stand
  have hc : Q3CL.Thompson.Ctx Ω W := ctx_of_stand hst hW
  have : Nonempty (Thompson.Rep Ω W) := ⟨(Thompson.exists_rep_of_mem_muDelta hd).choose⟩
  choose! rep hrep using fun (x : ↥(muGroup Ω W)) (hx : x ∈ Thompson.muDelta Ω W) =>
    Thompson.exists_rep_of_mem_muDelta hx
  obtain ⟨g, hg⟩ := hst.trans (rep d).K (rep d).hK
  have hperp := (hs.conj g).perp
  rw [hg] at hperp
  have hmaps : ∀ x ∈ Star3T.cent (Thompson.muDelta Ω W) d, (rep x).K ∈ KPerp Ω (rep d).K := by
    intro x hx
    by_cases hxd : x = d
    · subst hxd
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hc.rep_omega rep hrep hd hx.1 (fun e => hxd e.symm)
        hx.2.symm)
  have hinj : Set.InjOn (fun x => (rep x).K) (Star3T.cent (Thompson.muDelta Ω W) d) := by
    intro x hx y hy hxy
    have h1 := hc.img_eq_of_K_eq (rep x) (rep y) hxy
    rw [hrep x hx.1, hrep y hy.1] at h1
    exact Subtype.ext h1
  calc (Star3T.cent (Thompson.muDelta Ω W) d).ncard ≤ (KPerp Ω (rep d).K).ncard :=
        Set.ncard_le_ncard_of_injOn (fun x => (rep x).K) hmaps hinj
          (by rw [hperp]; exact Set.toFinite _)
    _ ≤ 2 := by
        rw [hperp]
        exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

theorem exists_cent_ne {K K' : Subgroup G} {z : G} (hs : Hyp23Setting Ω K K' z)
    (hW : W ∈ WSet Ω) {d : ↥(muGroup Ω W)} (hd : d ∈ Thompson.muDelta Ω W) :
    ∃ x ∈ Thompson.muDelta Ω W, x ≠ d ∧ x * d = d * x := by
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hc : Q3CL.Thompson.Ctx Ω W := ctx_of_stand hst hW
  obtain ⟨ρ, hρd⟩ := Thompson.exists_rep_of_mem_muDelta hd
  obtain ⟨g, hg⟩ := hst.trans ρ.K ρ.hK
  have hs' := hs.conj g
  rw [hg] at hs'

  obtain ⟨hRW, hUW, -, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D hΩ hW ρ.hR ρ.hK ρ.hRK
  have h2 : IsPGroup 2 ↥(ρ.K ⊓ W) := hΩ.isPGroup_of_mem_USet hUW
  obtain ⟨x₀, hx₀, o₀⟩ := AscP1Nine3.exists_orderOf_four_of_four_le hs'.hz inf_le_left h2
    (by rw [← hRW]; exact h4)
  have hzdW : g * z * g⁻¹ ∈ W := by
    rw [← T7A.sq_eq_of_orderOf_four hs'.hz hx₀.1 o₀]
    exact W.mul_mem hx₀.2 hx₀.2
  obtain ⟨S₁, R₁, R₁', hWS₁, hR₁, hR₁', hR₁S, hR₁'S⟩ := exists_sylow_frame hs' hW hzdW
  have hK₁' : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hs.hK'.1
  have hR₁'D : R₁' ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS₁ (mem_RSet_of_isSylow2In hK₁' hR₁') hR₁'S
  obtain ⟨ρ', hρ'K, -⟩ := exists_rep hΩ hW hK₁' hR₁' hR₁'D
  have hnbr : ρ'.K ∈ omegaNbr Ω ρ.K := by
    have hmem : conjSub g K' ∈ KPerp Ω ρ.K := by rw [hs'.perp]; exact Or.inr rfl
    rw [hρ'K]
    rcases hmem with e | e
    · exact absurd e hs'.hne
    · exact e
  refine ⟨⟨ρ'.img, rep_img_mem ρ'⟩, rep_mem_muDelta ρ', ?_, ?_⟩
  · intro hx
    have h1 : ρ'.img = ρ.img := congrArg Subtype.val hx |>.trans hρd.symm
    exact hs'.hne (hρ'K ▸ (hc.K_eq_of_img_eq ρ' ρ h1))
  · apply Subtype.ext
    show ρ'.img * (d : NQuot (W ⊔ OCW W)) = (d : NQuot (W ⊔ OCW W)) * ρ'.img
    rw [← hρd]
    exact (hc.comm_of_omega ρ ρ' hnbr).symm
end T7D

theorem c23_1_clique_proved : C23_1_clique := by
  intro G _ _ _ Ω K K' z hs W hW
  have hst : AscStand Ω K := hs.stand
  refine ⟨T7D.muDelta_nonempty hst.hyp hst.mem hW, fun d hd => ?_⟩
  have hle := T7D.ncard_cent_le_two hs hW hd
  obtain ⟨x, hx, hxd, hcomm⟩ := T7D.exists_cent_ne hs hW hd
  have hsub : ({d, x} : Set ↥(muGroup Ω W)) ⊆ Star3T.cent (Thompson.muDelta Ω W) d := by
    rintro y (rfl | rfl)
    · exact Star3T.self_mem_cent hd
    · exact ⟨hx, hcomm⟩
  have hge : 2 ≤ (Star3T.cent (Thompson.muDelta Ω W) d).ncard := by
    calc 2 = ({d, x} : Set ↥(muGroup Ω W)).ncard := (Set.ncard_pair hxd.symm).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega
end Asc77

end

section

namespace Disconnected.AschTight.Sec71
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}
omit [Finite G] in

theorem DData.conj (hΩ : Asc77.HypOmegaMod Ω) (hd : DData Ω W R K u r z) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    DData Ω W (conjSub g R) (conjSub g K) (g * u * g⁻¹) (g * r * g⁻¹) (g * z * g⁻¹) := by
  have hgW : conjSub g W = W := mem_normalizer_iff_conjSub_eq.mp hg
  have hU : conjSub g (Subgroup.zpowers u) = Subgroup.zpowers (g * u * g⁻¹) :=
    AscL62.conjSub_zpowers_eq g u
  refine ⟨hΩ.conjInvariant g K hd.memK, hd.sylow.conj g, ⟨RSet.conj hΩ.conjInvariant hd.memD.1 g,
    hgW ▸ Sec7.conjSub_le_normalizer hd.memD.2 g⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [← hU, ← hd.inf_eq, conjSub_inf, hgW]
  · rw [← hU]
    exact conjSub_mono hd.U_le_R
  · rw [← hU]
    exact USet.conj hΩ.conjInvariant hd.memU g
  · rw [← hgW]
    exact Sec7.conjSub_le_normalizer hd.le_normalizer g
  · rw [orderOf_conj', natCard_conjSub]
    exact hd.card
  · rw [orderOf_conj']
    exact hd.orderOf_eq
  · rw [orderOf_conj']
    exact hd.four_le
  · exact hd.uinv.conj g
  · rw [orderOf_conj', conj_pow, hd.z_eq]
  · exact conj_mem_conjSub hd.r_mem
  · rw [← hU, mem_conjSub_iff]
    intro h
    apply hd.r_not_mem
    simpa [mul_assoc] using h
  · calc g * r * g⁻¹ * (g * u * g⁻¹) * (g * r * g⁻¹)⁻¹ = g * (r * u * r⁻¹) * g⁻¹ := by group
      _ = (g * u * g⁻¹)⁻¹ := by rw [hd.conj_u]; group
  · calc g * r * g⁻¹ * (g * r * g⁻¹) = g * (r * r) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hd.sq_r]
  · intro x hx
    rw [mem_conjSub_iff] at hx
    rw [← hU]
    rcases hd.cover _ hx with h | ⟨y, hy, he⟩
    · left
      rw [mem_conjSub_iff]
      exact h
    · right
      refine ⟨g * y * g⁻¹, conj_mem_conjSub hy, ?_⟩
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g * (y * r) * g⁻¹ := by rw [he]
        _ = g * y * g⁻¹ * (g * r * g⁻¹) := by group
end Disconnected.AschTight.Sec71

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7D
open CFSG.ClassicalInvolution.Asc77.T7D
section Frame
variable {G : Type} [Group G] {W : Subgroup G}
end Frame
section CtxFrame
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem frame_fixed (c : Q3CL.Thompson.Ctx Ω W) (ρ ρ' ρ₃ : Thompson.Rep Ω W) {z j b b' : G}
    (hK'K : ρ'.K ∈ omegaNbr Ω ρ.K) (hKK' : ρ.K ∈ omegaNbr Ω ρ'.K)
    (hne₁ : ρ.K ≠ ρ₃.K) (hne₂ : ρ'.K ≠ ρ₃.K)
    (hn₁ : ρ₃.K ∉ omegaNbr Ω ρ.K) (hn₂ : ρ₃.K ∉ omegaNbr Ω ρ'.K)
    (hn₁' : ρ.K ∉ omegaNbr Ω ρ₃.K) (hn₂' : ρ'.K ∉ omegaNbr Ω ρ₃.K)
    (hz : IsUniqueInvolution ρ.K z) (hz' : IsUniqueInvolution ρ'.K z)
    (hj : IsUniqueInvolution ρ₃.K j)
    (hb : b ∈ ρ.K ⊓ W) (hb' : b' ∈ ρ'.K ⊓ W) (ob : orderOf b = 4) (ob' : orderOf b' = 4) :
    ∃ u₁, (u₁ = b * b' ∨ u₁ = b⁻¹ * b') ∧ ρ₃.r * u₁ * ρ₃.r⁻¹ = u₁ ∧
      ρ.r * (u₁ * j) * ρ.r⁻¹ = u₁ * j ∧ ρ'.r * (u₁ * j) * ρ'.r⁻¹ = u₁ * j ∧
      ρ₃.r * (u₁ * j) * ρ₃.r⁻¹ = u₁ * j := by
  have hWab := c.comm_W
  have hbb : b * b = z := T7A.sq_eq_of_orderOf_four hz hb.1 ob
  have hb'b' : b' * b' = z := T7A.sq_eq_of_orderOf_four hz' hb'.1 ob'
  have hz2 : z * z = 1 := hz.sq
  have hjW : j ∈ ρ₃.K ⊓ W :=
    Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW ρ₃.hK ρ₃.hR ρ₃.hRK hj
  have hzW : z ∈ W := by
    rw [← hbb]
    exact W.mul_mem hb.2 hb.2
  have hbinv : b⁻¹ = z * b := (eq_inv_of_mul_eq_one_left (by rw [mul_assoc, hbb, hz2])).symm
  have hb'inv : b'⁻¹ = z * b' := (eq_inv_of_mul_eq_one_left (by rw [mul_assoc, hb'b', hz2])).symm
  have e1 : ρ.r * b * ρ.r⁻¹ = b⁻¹ := c.conj_inv ρ hb
  have e1' : ρ.r * b' * ρ.r⁻¹ = b' := by
    rw [c.centralizes ρ ρ' hK'K hb']
    group
  have e2 : ρ.r * j * ρ.r⁻¹ = z * j := c.conj_involution ρ ρ₃ hne₁ hn₁ hz hj
  have f1 : ρ'.r * b' * ρ'.r⁻¹ = b'⁻¹ := c.conj_inv ρ' hb'
  have f1' : ρ'.r * b * ρ'.r⁻¹ = b := by
    rw [c.centralizes ρ' ρ hKK' hb]
    group
  have f2 : ρ'.r * j * ρ'.r⁻¹ = z * j := c.conj_involution ρ' ρ₃ hne₂ hn₂ hz' hj
  have g2 : ρ₃.r * j * ρ₃.r⁻¹ = j := by
    have := c.conj_inv ρ₃ hjW
    rw [this]
    exact inv_eq_of_mul_eq_one_left hj.sq
  have hdich := c.stab_dichotomy ρ₃ ρ ρ' hne₁.symm hne₂.symm hn₁' hn₂' hb hb' hj hz hz' hbb hb'b'
  have hcz : ∀ x ∈ W, z * x = x * z := fun x hx => hWab z hzW x hx
  have hzu : z * (b * b') = (b * b') * z := hcz _ (W.mul_mem hb.2 hb'.2)
  have hzu' : z * (b⁻¹ * b') = (b⁻¹ * b') * z := hcz _ (W.mul_mem (W.inv_mem hb.2) hb'.2)
  have hbz : b * z = z * b := (hcz b hb.2).symm
  have hbiz : b⁻¹ * z = z * b⁻¹ := (hcz b⁻¹ (W.inv_mem hb.2)).symm
  rcases hdich with h | h
  ·
    have hr : ρ.r * (b * b') * ρ.r⁻¹ = z * (b * b') := by
      calc ρ.r * (b * b') * ρ.r⁻¹ = (ρ.r * b * ρ.r⁻¹) * (ρ.r * b' * ρ.r⁻¹) := by group
        _ = b⁻¹ * b' := by rw [e1, e1']
        _ = z * (b * b') := by rw [hbinv, mul_assoc]
    have hr' : ρ'.r * (b * b') * ρ'.r⁻¹ = z * (b * b') := by
      calc ρ'.r * (b * b') * ρ'.r⁻¹ = (ρ'.r * b * ρ'.r⁻¹) * (ρ'.r * b' * ρ'.r⁻¹) := by group
        _ = b * b'⁻¹ := by rw [f1, f1']
        _ = z * (b * b') := by rw [hb'inv, ← mul_assoc, hbz, mul_assoc]
    refine ⟨b * b', Or.inl rfl, h, ?_, ?_, ?_⟩
    · have : ρ.r * (b * b' * j) * ρ.r⁻¹ = (ρ.r * (b * b') * ρ.r⁻¹) * (ρ.r * j * ρ.r⁻¹) := by
        group
      rw [this, hr, e2]
      exact mul_aux hzu hz2 rfl
    · have : ρ'.r * (b * b' * j) * ρ'.r⁻¹ =
          (ρ'.r * (b * b') * ρ'.r⁻¹) * (ρ'.r * j * ρ'.r⁻¹) := by group
      rw [this, hr', f2]
      exact mul_aux hzu hz2 rfl
    · have : ρ₃.r * (b * b' * j) * ρ₃.r⁻¹ =
          (ρ₃.r * (b * b') * ρ₃.r⁻¹) * (ρ₃.r * j * ρ₃.r⁻¹) := by group
      rw [this, h, g2]
  ·
    have hr : ρ.r * (b⁻¹ * b') * ρ.r⁻¹ = z * (b⁻¹ * b') := by
      calc ρ.r * (b⁻¹ * b') * ρ.r⁻¹ = (ρ.r * b * ρ.r⁻¹)⁻¹ * (ρ.r * b' * ρ.r⁻¹) := by group
        _ = b * b' := by rw [e1, e1', inv_inv]
        _ = z * (b⁻¹ * b') := by
          rw [hbinv, ← mul_assoc, ← mul_assoc, hz2, one_mul]
    have hr' : ρ'.r * (b⁻¹ * b') * ρ'.r⁻¹ = z * (b⁻¹ * b') := by
      calc ρ'.r * (b⁻¹ * b') * ρ'.r⁻¹ = (ρ'.r * b * ρ'.r⁻¹)⁻¹ * (ρ'.r * b' * ρ'.r⁻¹) := by group
        _ = b⁻¹ * b'⁻¹ := by rw [f1, f1']
        _ = z * (b⁻¹ * b') := by
          conv_lhs => rw [hb'inv]
          rw [← mul_assoc, hbiz, mul_assoc]
    refine ⟨b⁻¹ * b', Or.inr rfl, h, ?_, ?_, ?_⟩
    · have : ρ.r * (b⁻¹ * b' * j) * ρ.r⁻¹ = (ρ.r * (b⁻¹ * b') * ρ.r⁻¹) * (ρ.r * j * ρ.r⁻¹) := by
        group
      rw [this, hr, e2]
      exact mul_aux hzu' hz2 rfl
    · have : ρ'.r * (b⁻¹ * b' * j) * ρ'.r⁻¹ =
          (ρ'.r * (b⁻¹ * b') * ρ'.r⁻¹) * (ρ'.r * j * ρ'.r⁻¹) := by group
      rw [this, hr', f2]
      exact mul_aux hzu' hz2 rfl
    · have : ρ₃.r * (b⁻¹ * b' * j) * ρ₃.r⁻¹ =
          (ρ₃.r * (b⁻¹ * b') * ρ₃.r⁻¹) * (ρ₃.r * j * ρ₃.r⁻¹) := by group
      rw [this, h, g2]
end CtxFrame
end T7D
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7D
open CFSG.ClassicalInvolution.Asc77.T7D
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_swap_equiv [IsSimpleGroup G] {K K' : Subgroup G} {z : G}
    (hs : Hyp23Setting Ω K K' z)
    (hW : W ∈ WSet Ω) (hS4 : MuIsoS4 Ω W) :
    ∃ e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4), ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap := by
  obtain ⟨⟨d₀, hd₀⟩, hcl⟩ := c23_1_clique_proved G Ω K K' z hs W hW
  have hst : AscStand Ω K := hs.stand
  have hP : PartIHyp Ω := ⟨hst.hyp, hst.cls, hst.aEmpty⟩
  have hTT : Star3T.IsTT (Thompson.muDelta Ω W) :=
    Thompson.isTT_muDelta hst.hyp hW (Q3CL.thompsonCube hP W hW)
  have hS : Star3T.IsStar (Thompson.muDelta Ω W) :=
    Thompson.isStar_muDelta hst.hyp hW (thompsonStar G Ω hP W hW)
  by_cases hconn : ∀ d ∈ Thompson.muDelta Ω W, ∀ a ∈ Thompson.muDelta Ω W,
      Star3T.Conn (Thompson.muDelta Ω W) d a
  · exfalso
    set Δ := Thompson.muDelta Ω W with hΔ
    obtain ⟨d', hne, hcent⟩ : ∃ d', d₀ ≠ d' ∧ Star3T.cent Δ d₀ = {d₀, d'} := by
      obtain ⟨x, y, hxy, hxy'⟩ := Set.ncard_eq_two.mp (hcl d₀ hd₀)
      have hdx : d₀ ∈ ({x, y} : Set _) := hxy' ▸ Star3T.self_mem_cent hd₀
      rcases hdx with rfl | hdy
      · exact ⟨y, hxy, hxy'⟩
      · rw [Set.mem_singleton_iff] at hdy
        subst hdy
        exact ⟨x, fun e => hxy e.symm, by rw [hxy', Set.pair_comm]⟩
    have hd'c : d' ∈ Star3T.cent Δ d₀ := by rw [hcent]; exact Or.inr rfl
    have hd'Δ : d' ∈ Δ := hd'c.1
    have hcomm : d₀ * d' = d' * d₀ := hd'c.2.symm
    have hcent' : Star3T.cent Δ d' = {d₀, d'} := by
      have hsub : ({d₀, d'} : Set _) ⊆ Star3T.cent Δ d' := by
        intro x hx
        rcases hx with rfl | rfl
        · exact ⟨hd₀, hcomm⟩
        · exact Star3T.self_mem_cent hd'Δ
      exact (Set.eq_of_subset_of_ncard_le hsub
        (by rw [hcl d' hd'Δ, Set.ncard_pair hne]) (Set.toFinite _)).symm
    have hall : ∀ a, Relation.ReflTransGen (Star3T.Adj Δ) d₀ a → a = d₀ ∨ a = d' := by
      intro a hb
      induction hb with
      | refl => exact Or.inl rfl
      | @tail b c _ hbc ih =>
        obtain ⟨-, hc, hbc⟩ := hbc
        rcases ih with rfl | rfl
        · have : c ∈ Star3T.cent Δ b := ⟨hc, hbc.symm⟩
          rw [hcent] at this
          exact this
        · have : c ∈ Star3T.cent Δ b := ⟨hc, hbc.symm⟩
          rw [hcent'] at this
          exact this
    have hΔeq : Δ = {d₀, d'} := by
      ext a
      constructor
      · exact fun ha => hall a (hconn d₀ hd₀ a ha)
      · rintro (rfl | rfl)
        · exact hd₀
        · exact hd'Δ
    have hgen : Subgroup.closure ({d₀, d'} : Set ↥(muGroup Ω W)) = ⊤ := by
      rw [← hΔeq]
      exact hTT.closure_eq_top
    obtain ⟨e₁⟩ := T7B.nonempty_mulEquiv_klein (hTT.mul_self d₀ hd₀) (hTT.mul_self d' hd'Δ)
      (hTT.ne_one d₀ hd₀) (hTT.ne_one d' hd'Δ) hne hcomm hgen
    obtain ⟨e₂⟩ := hS4
    have h1 := Nat.card_congr e₁.toEquiv
    have h2 := Nat.card_congr e₂.toEquiv
    rw [h2] at h1
    have h3 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      rfl
    have h4 : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    omega
  · push Not at hconn
    obtain ⟨d, hd, a, ha, hnc⟩ := hconn
    exact Star3T.exists_mulEquiv_perm_four hTT hS hd ha hnc (hcl d hd)

@[expose] def conjRep (hΩ : HypOmegaMod Ω) {n : G} (hn : n ∈ Subgroup.normalizer (W : Set G))
    (ρ : Thompson.Rep Ω W) : Thompson.Rep Ω W where
  K := conjSub n ρ.K
  R := conjSub n ρ.R
  r := n * ρ.r * n⁻¹
  hK := hΩ.conjInvariant n ρ.K ρ.hK
  hR := Q3CL.Thompson.conjSub_mem_D hΩ ρ.hR hn
  hRK := ρ.hRK.conj n
  hr := conj_mem_conjSub ρ.hr
  hrW := fun h => ρ.hrW ((Thompson.mem_normalizer_iff_of_mem hn _).mp h)

theorem conjRep_img (hΩ : HypOmegaMod Ω) {n : G} (hn : n ∈ Subgroup.normalizer (W : Set G))
    (ρ : Thompson.Rep Ω W) :
    (conjRep hΩ hn ρ).img = Thompson.piG W n * ρ.img * (Thompson.piG W n)⁻¹ := by
  show Thompson.piG W (n * ρ.r * n⁻¹) = Thompson.piG W n * Thompson.piG W ρ.r *
    (Thompson.piG W n)⁻¹
  rw [Thompson.piG_mul (Subgroup.mul_mem _ hn ρ.r_mem_normalizer) (Subgroup.inv_mem _ hn),
    Thompson.piG_mul hn ρ.r_mem_normalizer, Thompson.piG_inv hn]

theorem conj_stable (c : Q3CL.Thompson.Ctx Ω W) {n : G} (hn : n ∈ Subgroup.normalizer (W : Set G))
    (ρ : Thompson.Rep Ω W)
    (h : Thompson.piG W n * ρ.img * (Thompson.piG W n)⁻¹ = ρ.img) :
    conjSub n ρ.K = ρ.K ∧
      ∀ w ∈ W, (n * ρ.r * n⁻¹) * w * (n * ρ.r * n⁻¹)⁻¹ = ρ.r * w * ρ.r⁻¹ := by
  have himg : (conjRep c.hΩ hn ρ).img = ρ.img := by rw [conjRep_img, h]
  refine ⟨c.K_eq_of_img_eq (conjRep c.hΩ hn ρ) ρ himg, fun w hw => ?_⟩
  exact Q3CL.Thompson.conj_eq_of_piG_eq c.hΩ c.hW ρ.r_mem_normalizer
    (conjRep c.hΩ hn ρ).r_mem_normalizer himg.symm hw
end T7D
end Asc77

end

section

namespace Disconnected.AschTight.Sec71
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

theorem conj_eq_of_four_dvd (hΩ : Asc77.HypOmegaMod Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hW2 : IsPGroup 2 W) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hzj : z ≠ j) {i k : ℤ} (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k)
    (hio : Odd i) (h4 : (4 : ℤ) ∣ i * k - 1) : conjSub t K = conjSub r J := by
  have hNv : orderOf v = orderOf u := (orderOf_eq_orderOf hΩ hd hd').symm
  obtain ⟨n, hn⟩ := hd.orderOf_eq
  have h4N := hd.four_le
  have hn2 : 2 ≤ n := by
    by_contra h
    interval_cases n <;> simp_all
  obtain ⟨m, hm⟩ : ∃ m : ℕ, orderOf u = 4 * m := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    exact ⟨2 ^ n', by rw [hn, pow_add]; ring⟩
  have huv : Commute u v := hWc u hd.u_memW v hd'.u_memW
  have hvui : Commute v (u ^ i) := (huv.zpow_left i).symm
  obtain ⟨c, hc⟩ := h4
  have hxa : (u * v ^ k) ^ (i * (m : ℤ)) = (v * u ^ i) ^ m := by
    rw [mul_zpow_zpow huv, hvui.mul_pow, ← zpow_natCast (u ^ i), ← zpow_mul]
    have hvk : v ^ (k * (i * (m : ℤ))) = v ^ (m : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq, hNv, hm, Int.modEq_iff_dvd]
      exact ⟨-c, by push_cast; linear_combination (-(m : ℤ)) * hc⟩
    rw [hvk, zpow_natCast, ((huv.zpow_left (i * (m : ℤ))).pow_right m).eq]
  set x := (v * u ^ i) ^ m with hx
  have hb : v * u ^ i ∈ conjSub r J := by rw [← hi]; exact conj_mem_conjSub hd'.u_memK
  have ha : u * v ^ k ∈ conjSub t K := by rw [← hk]; exact conj_mem_conjSub hd.u_memK
  have hxJ : Subgroup.zpowers x ≤ conjSub r J :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hb m)
  have hxK : Subgroup.zpowers x ≤ conjSub t K :=
    Subgroup.zpowers_le.mpr (hxa ▸ Subgroup.zpow_mem _ ha _)
  have hbW : v * u ^ i ∈ W := W.mul_mem hd'.u_memW (W.zpow_mem hd.u_memW i)
  have hx2 : IsPGroup 2 ↥(Subgroup.zpowers x) :=
    hW2.to_le (Subgroup.zpowers_le.mpr (W.pow_mem hbW m))
  have hsq : x ^ 2 = j * z := by
    rw [hx, ← pow_mul, ← hi, conj_pow, show m * 2 = orderOf u / 2 by omega,
      conj_pow_eq huv hi, hd.j_eq hΩ hd', hd.z_eq, zpow_eq_self_of_odd hd.uinv.sq hio]
  have hx1 : x ^ 2 ≠ 1 := by
    rw [hsq]
    intro h
    apply hzj
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hd.uinv.sq]
  have hx4 : x ^ 4 = 1 := by
    have hob : orderOf (v * u ^ i) = orderOf u := by rw [← hi, orderOf_conj', hNv]
    rw [hx, ← pow_mul, show m * 4 = orderOf u by omega, ← hob, pow_orderOf_eq_one]
  have hord : orderOf x = 4 := by
    have hdvd : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
    have hndvd : ¬ orderOf x ∣ 2 := fun h => hx1 (orderOf_dvd_iff_pow_eq_one.mp h)
    have hpos := orderOf_pos x
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hcases : orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 4 := by omega
    rcases hcases with h | h | h | h
    · rw [h] at hndvd
      exact absurd (one_dvd 2) hndvd
    · rw [h] at hndvd
      exact absurd (dvd_refl 2) hndvd
    · rw [h] at hdvd
      norm_num at hdvd
    · exact h
  exact hΩ.eq_of_le_of_le (hΩ.conjInvariant t K hd.memK) (hΩ.conjInvariant r J hd'.memK) hx2
    (by rw [Nat.card_zpowers, hord]) hxK hxJ

theorem rel_of_conj_eq (hΩ : Asc77.HypOmegaMod Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hzj : z ≠ j)
    {i k : ℤ} (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k)
    (hL : conjSub t K = conjSub r J) : u ^ (i * k) = u := by
  have hNv : orderOf v = orderOf u := (orderOf_eq_orderOf hΩ hd hd').symm
  have huv : Commute u v := hWc u hd.u_memW v hd'.u_memW
  have hUV := inf_eq_bot_of_ne hd hd' hzj
  have h3 : v * u ^ i ∈ Subgroup.zpowers (u * v ^ k) := by
    rw [← hk, ← hd.conj_inf_eq hd'.r_normW, hL, hd'.conj_inf_eq hd.r_normW, hi]
    exact Subgroup.mem_zpowers _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h3
  rw [mul_zpow_zpow huv] at hm
  have hm' : u ^ m * v ^ (k * m) = u ^ i * v ^ (1 : ℤ) := by
    rw [zpow_one, hm, ((huv.zpow_left i).symm).eq]
  have h1 := zpow_sub_mul_zpow_sub huv hm'
  have hu1 : u ^ (m - i) = 1 := eq_one_of_mul_eq_one hUV (Subgroup.zpow_mem_zpowers u _)
    (Subgroup.zpow_mem_zpowers v _) h1
  rw [hu1, one_mul] at h1
  rw [zpow_eq_one_iff_modEq] at hu1 h1
  rw [← zpow_one u, ← zpow_mul, one_mul, zpow_eq_zpow_iff_modEq]
  rw [hNv] at h1
  have e1 := Int.ModEq.dvd hu1.symm
  have e2 := Int.ModEq.dvd h1.symm
  refine (Int.modEq_iff_dvd.mpr ?_).symm
  simp only [sub_zero] at e1 e2
  have : i * k - 1 = (k * m - 1) - k * (m - i) := by ring
  rw [this]
  exact dvd_sub e2 (dvd_mul_of_dvd_right e1 k)

theorem braid_of_conj_eq [hcl : Fact (Q3CL.ClassicalClause Ω)] (hΩ : Asc77.HypOmegaMod Ω) (hd :
    DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {i k : ℤ}
    (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k)
    (hL : conjSub t K = conjSub r J) :
    ∃ y ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W, t * r * t = y * (r * t * r) := by
  set Y₀ := Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W with hY₀
  have hrN : r ∈ Subgroup.normalizer (Y₀ : Set G) := hd.r_mem_normalizer_Y₀ hi
  have htN : t ∈ Subgroup.normalizer (Y₀ : Set G) := hd'.t_mem_normalizer_Y₀ hk
  have hdL := hd.conj hΩ hd'.r_normW
  have hkey := hdL.inf_normalizer_le hΩ
  have hmem : r * t * r⁻¹ ∈ conjSub t K ⊓ Subgroup.normalizer (W : Set G) := by
    refine ⟨?_, ?_⟩
    · rw [hL]
      exact conj_mem_conjSub hd'.r_memK
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hd.r_normW hd'.r_normW)
        (Subgroup.inv_mem _ hd.r_normW)
  have hLE : conjSub t R ≤ Subgroup.normalizer ((OCW W : Subgroup G) : Set G) :=
    fun x hx => Sec7.normalizer_le_normalizer_OCW W (hdL.memD.2 hx)
  obtain ⟨ρ', hρ', x, hx, he⟩ := exists_mul_of_mem_sup hLE (hkey hmem)
  rw [mem_conjSub_iff] at hρ'
  rcases hd.cover _ hρ' with hU | ⟨c, hc, hce⟩
  · exfalso
    have hρY : ρ' ∈ Y₀ := by
      have := conj_mem_of_mem_normalizer htN (U_le_Y₀ u v W hU)
      rwa [show t * (t⁻¹ * ρ' * t) * t⁻¹ = ρ' by group] at this
    have htY : t ∈ Y₀ := by
      have := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hrN)
        (Y₀.mul_mem hρY (Subgroup.mem_sup_right hx))
      rwa [← he, show r⁻¹ * (r * t * r⁻¹) * r⁻¹⁻¹ = t by group] at this
    have h1 := Y₀_comm_v hWc hd.u_memW hd'.u_memW htY
    exact not_comm_of_inv hd'.conj_u hd'.u_sq_ne h1
  · have hρ'' : ρ' = t * (c * r) * t⁻¹ := by rw [← hce]; group
    have he' : r * t * r⁻¹ = t * (c * r) * t⁻¹ * x := by rw [he, hρ'']
    have h1 : t * r * t = (t * c * t⁻¹)⁻¹ * (r * t * r⁻¹) * x⁻¹ * (t * t) := by
      rw [he']
      group
    refine ⟨(t * c * t⁻¹)⁻¹ * ((r * t * r) * ((x * z)⁻¹ * j) * (r * t * r)⁻¹), ?_, ?_⟩
    · refine Y₀.mul_mem (Y₀.inv_mem (conj_mem_of_mem_normalizer htN (U_le_Y₀ u v W hc)))
        (conj_mem_of_mem_normalizer (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN htN) hrN)
          (Y₀.mul_mem (Y₀.inv_mem (Y₀.mul_mem (Subgroup.mem_sup_right hx) (U_le_Y₀ u v W hd.z_mem)))
            (V_le_Y₀ u v W hd'.z_mem)))
    · rw [h1, ← hd.sq_r, ← hd'.sq_r]
      group
end Disconnected.AschTight.Sec71

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7D
open CFSG.ClassicalInvolution.Asc77.T7D
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_stab_split (c : Q3CL.Thompson.Ctx Ω W)
    {e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap) {ρ ρ' ρ₃ : Thompson.Rep Ω W}
    (hab : imgQ ρ ≠ imgQ ρ') (hcomm : imgQ ρ * imgQ ρ' = imgQ ρ' * imgQ ρ)
    (hac : imgQ ρ * imgQ ρ₃ ≠ imgQ ρ₃ * imgQ ρ) {ε : G} (hε : ε ∈ W)
    (h₁ : ρ.r * ε * ρ.r⁻¹ = ε) (h₂ : ρ'.r * ε * ρ'.r⁻¹ = ε) (h₃ : ρ₃.r * ε * ρ₃.r⁻¹ = ε)
    {n : G} (hn : n ∈ Subgroup.normalizer (W : Set G)) :
    ∃ m ∈ Subgroup.normalizer (W : Set G), m * ε * m⁻¹ = ε ∧
      Thompson.piG W (m⁻¹ * n) * ρ.img * (Thompson.piG W (m⁻¹ * n))⁻¹ = ρ.img ∧
      Thompson.piG W (m⁻¹ * n) * ρ'.img * (Thompson.piG W (m⁻¹ * n))⁻¹ = ρ'.img ∧
      Thompson.piG W (m⁻¹ * n) * ρ₃.img * (Thompson.piG W (m⁻¹ * n))⁻¹ = ρ₃.img := by
  have ha := imgQ_mem ρ
  have ha' := imgQ_mem ρ'
  have ha₃ := imgQ_mem ρ₃
  have hmem : ∀ σ : Thompson.Rep Ω W, σ.r * ε * σ.r⁻¹ = ε →
      imgQ σ ∈ Thompson.muStab Ω W ε := fun σ h =>
    (c.mem_muStab_iff hε σ.hR σ.hr (q := imgQ σ) rfl).mpr h
  have hΔ : ∀ x ∈ Thompson.muDelta Ω W, x ∈ Thompson.muStab Ω W ε := fun x hx => by
    have hx' := S4.mem_closure_frame he ha ha' ha₃ hab hcomm hac hx
    refine (Subgroup.closure_le (Thompson.muStab Ω W ε)).mpr ?_ hx'
    rintro y (rfl | rfl | rfl)
    · exact hmem ρ h₁
    · exact hmem ρ' h₂
    · exact hmem ρ₃ h₃
  have hall : ∀ y : ↥(muGroup Ω W), y ∈ Thompson.muStab Ω W ε := fun y => by
    have : y ∈ Subgroup.closure (Thompson.muDelta Ω W) := by
      rw [Thompson.closure_muDelta_eq_top]
      trivial
    exact (Subgroup.closure_le (Thompson.muStab Ω W ε)).mpr hΔ this
  have hb₁ := Thompson.conjQ_mem_muDelta c.hΩ hn ha
  have hb₂ := Thompson.conjQ_mem_muDelta c.hΩ hn ha'
  have hb₃ := Thompson.conjQ_mem_muDelta c.hΩ hn ha₃
  obtain ⟨y, hy1, hy2, hy3⟩ := S4.exists_frame_conj he ha ha' ha₃ hb₁ hb₂ hb₃ hab hcomm hac
    (fun h => hab ((Thompson.conjQ c.hΩ hn).injective h))
    (by rw [← map_mul, ← map_mul, hcomm])
    (fun h => hac ((Thompson.conjQ c.hΩ hn).injective (by rw [map_mul, map_mul]; exact h)))
  obtain ⟨m, hm, hym, hmε⟩ := hall y
  have key : ∀ σ : Thompson.Rep Ω W,
      y * imgQ σ * y⁻¹ = Thompson.conjQ c.hΩ hn (imgQ σ) →
      Thompson.piG W (m⁻¹ * n) * σ.img * (Thompson.piG W (m⁻¹ * n))⁻¹ = σ.img := by
    intro σ hσ
    have h1 : (y : NQuot (W ⊔ OCW W)) * σ.img * (y : NQuot (W ⊔ OCW W))⁻¹ =
        Thompson.piG W n * σ.img * (Thompson.piG W n)⁻¹ := by
      have := congrArg Subtype.val hσ
      rw [Thompson.conjQ_apply] at this
      exact this
    rw [Thompson.piG_mul (Subgroup.inv_mem _ hm) hn, Thompson.piG_inv hm, ← hym]
    calc (y : NQuot (W ⊔ OCW W))⁻¹ * Thompson.piG W n * σ.img *
          ((y : NQuot (W ⊔ OCW W))⁻¹ * Thompson.piG W n)⁻¹
        = (y : NQuot (W ⊔ OCW W))⁻¹ * (Thompson.piG W n * σ.img * (Thompson.piG W n)⁻¹) *
            (y : NQuot (W ⊔ OCW W)) := by group
      _ = (y : NQuot (W ⊔ OCW W))⁻¹ * ((y : NQuot (W ⊔ OCW W)) * σ.img *
            (y : NQuot (W ⊔ OCW W))⁻¹) * (y : NQuot (W ⊔ OCW W)) := by rw [h1]
      _ = σ.img := by group
  exact ⟨m, hm, hmε, key ρ hy1, key ρ' hy2, key ρ₃ hy3⟩

theorem c24_2_of_frame [IsSimpleGroup G] {K K' : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u b b' : G} (hs : Hyp23Setting Ω K K' z)
    (hyp : Hyp24Data Ω K K' W S R R' z u) (hb : b ∈ K ⊓ W) (hb' : b' ∈ K' ⊓ W)
    (ob : orderOf b = 4) (ob' : orderOf b' = 4) (hu : u = b * b') :
    ∃ g ∈ Subgroup.normalizer (W : Set G), g⁻¹ * z * g = u := by
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hW : W ∈ WSet Ω := hyp.hW
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  have c : Q3CL.Thompson.Ctx Ω W := ctx_of_stand hst hW
  obtain ⟨e, he⟩ := exists_swap_equiv hs hW hyp.hS4

  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  have hRD : R ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hyp.hWS hyp.hR.1 hyp.hR.2.2
  have hR'D : R' ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hyp.hWS hyp.hR'.1 hyp.hR'.2.2
  obtain ⟨ρ, hρK, -⟩ := exists_rep hΩ hW hK hRsyl hRD
  obtain ⟨ρ', hρ'K, -⟩ := exists_rep hΩ hW hK' hR'syl hR'D
  have hzρ : IsUniqueInvolution ρ.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρ'.K z := by rw [hρ'K]; exact hz'
  have hne : ρ.K ≠ ρ'.K := by
    rw [hρK, hρ'K]
    exact hs.hne.symm
  have hρnbr : ρ'.K ∈ omegaNbr Ω ρ.K := by
    have hperp : K' ∈ KPerp Ω K := by rw [hs.perp]; exact Or.inr rfl
    rw [hρK, hρ'K]
    rcases hperp with e | e
    · exact absurd e hs.hne
    · exact e
  have hcomm : ρ.img * ρ'.img = ρ'.img * ρ.img := c.comm_of_omega ρ ρ' hρnbr
  have hρnbr' : ρ.K ∈ omegaNbr Ω ρ'.K := c.omega_of_comm ρ' ρ hne.symm hcomm.symm
  have hab : imgQ ρ ≠ imgQ ρ' := fun h => hne (c.K_eq_of_img_eq ρ ρ' (congrArg Subtype.val h))
  have hcommQ : imgQ ρ * imgQ ρ' = imgQ ρ' * imgQ ρ := Subtype.ext hcomm

  obtain ⟨c₃, hc₃Δ, hac, hbc⟩ := S4.exists_third he (imgQ_mem ρ) (imgQ_mem ρ') hab hcommQ
  obtain ⟨ρ₃, hρ₃⟩ := Thompson.exists_rep_of_mem_muDelta hc₃Δ
  have hc₃ : imgQ ρ₃ = c₃ := Subtype.ext hρ₃
  have hac' : imgQ ρ * imgQ ρ₃ ≠ imgQ ρ₃ * imgQ ρ := by rw [hc₃]; exact hac
  have hbc' : imgQ ρ' * imgQ ρ₃ ≠ imgQ ρ₃ * imgQ ρ' := by rw [hc₃]; exact hbc
  have hne₁ : ρ.K ≠ ρ₃.K := fun h => hac' (by
    have h1 : imgQ ρ = imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ ρ₃ h)
    rw [← h1])
  have hne₂ : ρ'.K ≠ ρ₃.K := fun h => hbc' (by
    have h1 : imgQ ρ' = imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ' ρ₃ h)
    rw [← h1])
  have hn₁ : ρ₃.K ∉ omegaNbr Ω ρ.K := fun h => hac' (Subtype.ext (c.comm_of_omega ρ ρ₃ h))
  have hn₂ : ρ₃.K ∉ omegaNbr Ω ρ'.K := fun h => hbc' (Subtype.ext (c.comm_of_omega ρ' ρ₃ h))
  have hn₁' : ρ.K ∉ omegaNbr Ω ρ₃.K := fun h =>
    hac' (Subtype.ext (c.comm_of_omega ρ₃ ρ h).symm)
  have hn₂' : ρ'.K ∉ omegaNbr Ω ρ₃.K := fun h =>
    hbc' (Subtype.ext (c.comm_of_omega ρ₃ ρ' h).symm)
  obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution ρ₃.hK
  have hjW : j ∈ W :=
    (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW ρ₃.hK ρ₃.hR ρ₃.hRK hj).2
  have hbρ : b ∈ ρ.K ⊓ W := by rw [hρK]; exact hb
  have hb'ρ : b' ∈ ρ'.K ⊓ W := by rw [hρ'K]; exact hb'
  obtain ⟨u₁, hu₁, hr₃, hr₁, hr₂, hr₃'⟩ := frame_fixed c ρ ρ' ρ₃ hρnbr hρnbr' hne₁ hne₂ hn₁ hn₂
    hn₁' hn₂' hzρ hzρ' hj hbρ hb'ρ ob ob'
  have hu₁W : u₁ ∈ W := by
    rcases hu₁ with rfl | rfl
    · exact W.mul_mem hb.2 hb'.2
    · exact W.mul_mem (W.inv_mem hb.2) hb'.2
  have hεW : u₁ * j ∈ W := W.mul_mem hu₁W hjW
  have hsz : ρ₃.r * z * ρ₃.r⁻¹ ≠ z := by
    rw [c.conj_involution ρ₃ ρ hne₁.symm hn₁' hj hzρ]
    intro h
    exact hj.ne_one (mul_right_cancel (h.trans (one_mul z).symm))
  have hF : FrameEps W K K' ρ₃.r j (u₁ * j) := by
    rcases hu₁ with rfl | rfl
    · exact ⟨b, b', hb, hb', ob, ob', hr₃, rfl⟩
    · exact ⟨b⁻¹, b', ⟨K.inv_mem hb.1, W.inv_mem hb.2⟩, hb', by rw [orderOf_inv]; exact ob, ob',
        hr₃, rfl⟩

  have hεinv : ∀ n ∈ Subgroup.normalizer (W : Set G), n * (u₁ * j) * n⁻¹ = u₁ * j := by
    intro n hn
    obtain ⟨m, hm, hmε, k₁, k₂, k₃⟩ := exists_stab_split c he hab hcommQ hac' hεW hr₁ hr₂ hr₃' hn
    have hn' : m⁻¹ * n ∈ Subgroup.normalizer (W : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hn
    obtain ⟨hKn, -⟩ := conj_stable c hn' ρ k₁
    obtain ⟨hK'n, -⟩ := conj_stable c hn' ρ' k₂
    obtain ⟨hJn, hact⟩ := conj_stable c hn' ρ₃ k₃
    have hKn' : conjSub (m⁻¹ * n) K = K := by rw [← hρK]; exact hKn
    have hK'n' : conjSub (m⁻¹ * n) K' = K' := by rw [← hρ'K]; exact hK'n
    have hjn : (m⁻¹ * n) * j * (m⁻¹ * n)⁻¹ = j := by
      have := hj.conj (m⁻¹ * n)
      rw [hJn] at this
      exact (hj.eq this).symm
    have hF' := FrameEps.conj hn' hF
    rw [hKn', hK'n', hjn] at hF'
    have huniq := FrameEps.unique hz hz' hWab hsz (fun w hw => (hact w hw).symm) hF hF'
    calc n * (u₁ * j) * n⁻¹
        = m * ((m⁻¹ * n) * (u₁ * j) * (m⁻¹ * n)⁻¹) * m⁻¹ := by group
      _ = m * (u₁ * j) * m⁻¹ := by rw [← huniq]
      _ = u₁ * j := hmε
  have hε1 : u₁ * j = 1 := by
    have hmemC : u₁ * j ∈ Asc77.centerIn (Subgroup.normalizer (W : Set G)) := by
      refine ⟨⟨u₁ * j, Subgroup.le_normalizer hεW⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 := hεinv g g.2
      show (g : G) * (u₁ * j) = (u₁ * j) * g
      calc (g : G) * (u₁ * j) = ((g : G) * (u₁ * j) * (g : G)⁻¹) * g := by group
        _ = (u₁ * j) * g := by rw [h1]
    have hmem : u₁ * j ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) := ⟨hεW, hmemC⟩
    rw [hyp.hZ] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hu₁j : u₁ = j := by
    rw [eq_inv_of_mul_eq_one_left hε1]
    exact inv_eq_of_mul_eq_one_left hj.sq

  obtain ⟨y, hy⟩ := S4.exists_conj_of_mem he (imgQ_mem ρ) (imgQ_mem ρ₃)
  obtain ⟨m, hm, hym⟩ := exists_normalizer_of_mem_muGroup y
  have himg : Thompson.piG W m * ρ.img * (Thompson.piG W m)⁻¹ = ρ₃.img := by
    rw [← hym]
    exact congrArg Subtype.val hy
  have hKm : conjSub m ρ.K = ρ₃.K :=
    c.K_eq_of_img_eq (conjRep c.hΩ hm ρ) ρ₃ (by rw [conjRep_img, himg])
  have hzm : m * z * m⁻¹ = j := by
    have := hzρ.conj m
    rw [hKm] at this
    exact (hj.eq this).symm
  have hbinv : b⁻¹ = z * b := by
    have hbb : b * b = z := T7A.sq_eq_of_orderOf_four hz hb.1 ob
    exact (eq_inv_of_mul_eq_one_left (by rw [mul_assoc, hbb, hz.sq])).symm
  rcases hu₁ with hu₁ | hu₁
  · refine ⟨m⁻¹, Subgroup.inv_mem _ hm, ?_⟩
    rw [inv_inv, hzm, hu, ← hu₁, hu₁j]
  · refine ⟨(ρ.r * m)⁻¹, Subgroup.inv_mem _ (Subgroup.mul_mem _ ρ.r_mem_normalizer hm), ?_⟩
    have e2 : ρ.r * j * ρ.r⁻¹ = z * j := c.conj_involution ρ ρ₃ hne₁ hn₁ hzρ hj
    have hu2 : u = z * j := by
      rw [hu, ← hu₁j, hu₁, hbinv, ← mul_assoc, ← mul_assoc, hz.sq, one_mul]
    calc (ρ.r * m)⁻¹⁻¹ * z * (ρ.r * m)⁻¹ = ρ.r * (m * z * m⁻¹) * ρ.r⁻¹ := by group
      _ = ρ.r * j * ρ.r⁻¹ := by rw [hzm]
      _ = z * j := e2
      _ = u := hu2.symm
end T7D
end Asc77

end

section

namespace Disconnected.AschTight.Sec71
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

theorem conj_ne_of_quad (hΩ : Asc77.HypOmegaMod Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hzj : z ≠ j)
    {i k : ℤ} (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k) (hko : Odd k)
    (hbad : ¬ (4 : ℤ) ∣ i * k - 1) {w : G} (hw : w ∈ Subgroup.closure {r, t})
    (hwW : w ∈ Subgroup.normalizer (W : Set G)) : conjSub w K ≠ J := by
  intro hwK
  have hUV := inf_eq_bot_of_ne hd hd' hzj
  have hNv : orderOf v = orderOf u := (orderOf_eq_orderOf hΩ hd hd').symm
  have hconjU : conjSub w (Subgroup.zpowers u) = Subgroup.zpowers v := by
    rw [← hd.inf_eq, conjSub_inf, hwK, mem_normalizer_iff_conjSub_eq.mp hwW, hd'.inf_eq]
  have hwu : w * u * w⁻¹ ∈ Subgroup.zpowers v :=
    hconjU ▸ conj_mem_conjSub (Subgroup.mem_zpowers u)
  obtain ⟨a', b', he, hq⟩ := exists_quad hd hd' hWc hi hk hw 1 0
  rw [zpow_one, zpow_zero, mul_one] at he
  have hua : u ^ a' = 1 := by
    have h1 : u ^ a' ∈ Subgroup.zpowers u ⊓ Subgroup.zpowers v := by
      refine ⟨Subgroup.zpow_mem_zpowers u a', ?_⟩
      have := Subgroup.mul_mem _ (he ▸ hwu) (Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers v b'))
      rwa [mul_inv_cancel_right] at this
    rw [hUV] at h1
    exact h1
  rw [hua, one_mul] at he
  obtain ⟨n, hn⟩ := hd.orderOf_eq
  have h4N := hd.four_le
  have hn2 : 2 ≤ n := by
    by_contra h
    interval_cases n <;> simp_all
  have h4 : (4 : ℤ) ∣ (orderOf u : ℤ) := by
    rw [hn]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    exact ⟨2 ^ n', by push_cast; ring⟩
  have h4a : (4 : ℤ) ∣ a' := by
    rw [zpow_eq_one_iff_modEq, Int.modEq_zero_iff_dvd] at hua
    exact h4.trans hua
  have hb' : Odd b' := by
    by_contra hb
    obtain ⟨c, hc⟩ := Int.not_odd_iff_even.mp hb
    have hhalf : orderOf u / 2 * 2 = orderOf u := by
      rw [hn]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, Nat.mul_div_cancel _ two_pos]
    have h1 : (w * u * w⁻¹) ^ (orderOf u / 2) = w * z * w⁻¹ := by rw [conj_pow, hd.z_eq]
    have hcast : (orderOf u : ℤ) = ((orderOf u / 2 : ℕ) : ℤ) * 2 := by exact_mod_cast hhalf.symm
    have h2 : (v ^ b') ^ (orderOf u / 2) = 1 := by
      rw [← zpow_natCast, ← zpow_mul, zpow_eq_one_iff_modEq, hNv, Int.modEq_zero_iff_dvd, hc]
      exact ⟨c, by rw [hcast]; ring⟩
    rw [he, h2] at h1
    have h3 := h1.symm
    rw [conj_eq_one_iff] at h3
    exact hd.uinv.ne_one h3
  exact hbad (four_dvd_of_quad hko h4a hb' hq)
end Disconnected.AschTight.Sec71

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def C24_setupU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoS4 Ω W →
      W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) = ⊥ →
        ∃ (S : Sylow 2 G) (R R' : Subgroup G) (b b' : G), b ∈ K ⊓ W ∧ b' ∈ K' ⊓ W ∧
          orderOf b = 4 ∧ orderOf b' = 4 ∧ Hyp24 Ω K K' W S R R' z (b * b')

theorem c24_setupU : C24_setupU := by
  intro G _ _ _ Ω K K' z hs W hW hzW hS4 hZ
  have hst : AscStand Ω K := hs.1.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.1.hK'.1
  have hKK' : K' ≠ K := hs.1.hne
  have hz : IsUniqueInvolution K z := hs.1.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.1.hK'
  have hW2 : IsPGroup 2 W := Thompson.isPGroup_of_mem_WSet hW
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw z hzW)
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge hW2 hWC
  have hR : IsSylow2In (T ⊓ K) K :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (T7A.isSubnormal_centralizer hst.modU hK hz)
  have hR' : IsSylow2In (T ⊓ K') K' :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (T7A.isSubnormal_centralizer hst.modU hK' hz')
  obtain ⟨S, hTS⟩ := hT.2.1.exists_le_sylow
  have hWS : W ≤ (S : Subgroup G) := hWT.trans hTS
  have hRS : T ⊓ K ≤ (S : Subgroup G) := inf_le_left.trans hTS
  have hR'S : T ⊓ K' ≤ (S : Subgroup G) := inf_le_left.trans hTS
  obtain ⟨x₁, hx₁, o₁⟩ := T7C.exists_orderOf_four_mem_inf hΩ hW hWS hK hR hRS hz
  obtain ⟨x₂, hx₂, o₂⟩ := T7C.exists_orderOf_four_mem_inf hΩ hW hWS hK' hR' hR'S hz'
  have s₁ : x₁ * x₁ = z := T7A.sq_eq_of_orderOf_four hz hx₁.1 o₁
  have s₂ : x₂ * x₂ = z := T7A.sq_eq_of_orderOf_four hz' hx₂.1 o₂
  have hc : x₁ * x₂ = x₂ * x₁ := hWab x₁ hx₁.2 x₂ hx₂.2
  have hx₁₂ : x₁ ∈ K ⊓ W := ⟨hx₁.1, hx₁.2⟩
  have hx₂₂ : x₂ ∈ K' ⊓ W := ⟨hx₂.1, hx₂.2⟩
  refine ⟨S, T ⊓ K, T ⊓ K', x₁, x₂, hx₁₂, hx₂₂, o₁, o₂, hs, hW, hzW, hS4, hZ, hWS,
    ⟨mem_RSet_of_isSylow2In hK hR, inf_le_right, hRS⟩,
    ⟨mem_RSet_of_isSylow2In hK' hR', inf_le_right, hR'S⟩,
    Subgroup.mul_mem_sup hx₁.1 hx₂.1, W.mul_mem hx₁.2 hx₂.2, ?_, ?_, ?_⟩
  · calc x₁ * x₂ * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
      _ = x₁ * (x₁ * x₂) * x₂ := by rw [← hc]
      _ = (x₁ * x₁) * (x₂ * x₂) := by group
      _ = 1 := by rw [s₁, s₂, hz.sq]
  · intro he
    refine T7A.not_mem_inf_of_orderOf_four hΩ hK hK' hKK' o₂ ?_ hx₂.1
    have : x₂ = x₁⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact K.inv_mem hx₁.1
  · intro he
    refine T7A.not_mem_inf_of_orderOf_four hΩ hK hK' hKK' o₂ ?_ hx₂.1
    have : x₂ = x₁⁻¹ * z := by rw [← he]; group
    rw [this]
    exact K.mul_mem (K.inv_mem hx₁.1) hz.mem
namespace T7D
open CFSG.ClassicalInvolution.Asc77.T7D
end T7D
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
