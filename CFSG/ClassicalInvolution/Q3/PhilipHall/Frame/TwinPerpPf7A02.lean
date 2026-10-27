module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf7A01
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M2
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A02

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

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
    (hK : K ∈ Ω) (hW : W ∈ WSet Ω) : (Thompson.muDelta Ω W).Nonempty :=
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7D.muDelta_nonempty hΩ hK hW

theorem ncard_cent_le_two {K K' : Subgroup G} {z : G} (hs : Hyp23Setting Ω K K' z)
    (hW : W ∈ WSet Ω) {d : ↥(muGroup Ω W)} (hd : d ∈ Thompson.muDelta Ω W) :
    (Star3T.cent (Thompson.muDelta Ω W) d).ncard ≤ 2 := by
  have hst : AscStand Ω K := hs.stand
  have hc : Q3.Q3CL.Thompson.Ctx Ω W := ctx_of_stand hst hW
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
  have hc : Q3.Q3CL.Thompson.Ctx Ω W := ctx_of_stand hst hW
  obtain ⟨ρ, hρd⟩ := Thompson.exists_rep_of_mem_muDelta hd
  obtain ⟨g, hg⟩ := hst.trans ρ.K ρ.hK
  have hs' := hs.conj g
  rw [hg] at hs'

  obtain ⟨hRW, hUW, -, h4, -⟩ := Q3.Q3CL.Thompson.inf_W_of_mem_D hΩ hW ρ.hR ρ.hK ρ.hRK
  have h2 : IsPGroup 2 ↥(ρ.K ⊓ W) := hΩ.isPGroup_of_mem_USet hUW
  obtain ⟨x₀, hx₀, o₀⟩ := AscP1Nine3.exists_orderOf_four_of_four_le hs'.hz inf_le_left h2
    (by rw [← hRW]; exact h4)
  have hzdW : g * z * g⁻¹ ∈ W := by
    rw [← T7A.sq_eq_of_orderOf_four hs'.hz hx₀.1 o₀]
    exact W.mul_mem hx₀.2 hx₀.2
  obtain ⟨S₁, R₁, R₁', hWS₁, hR₁, hR₁', hR₁S, hR₁'S⟩ := exists_sylow_frame hs' hW hzdW
  have hK₁' : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hs.hK'.1
  have hR₁'D : R₁' ∈ DSet Ω W :=
    Q3.Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS₁ (mem_RSet_of_isSylow2In hK₁' hR₁') hR₁'S
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

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7D
open CFSG.ClassicalInvolution.Asc77.T7D
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_swap_equiv [CoreLike G] {K K' : Subgroup G} {z : G}
    (hs : Hyp23Setting Ω K K' z)
    (hW : W ∈ WSet Ω) (hS4 : MuIsoS4 Ω W) :
    ∃ e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4), ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap := by
  obtain ⟨⟨d₀, hd₀⟩, hcl⟩ := c23_1_clique_proved G Ω K K' z hs W hW
  have hst : AscStand Ω K := hs.stand
  have hP : PartIHyp Ω := ⟨hst.hyp, hst.cls, hst.aEmpty⟩
  have hTT : Star3T.IsTT (Thompson.muDelta Ω W) :=
    Q3.Q3T8.Asc77.Thompson.isTT_muDelta hst.hyp hW (Q3.Q3CL.thompsonCube hP W hW)
  have hS : Star3T.IsStar (Thompson.muDelta Ω W) :=
    Q3.Q3T8.Asc77.Thompson.isStar_muDelta hst.hyp hW (Q3.Q3T8.Asc77.thompsonStar G Ω hP W hW)
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
  hR := Q3.Q3CL.Thompson.conjSub_mem_D hΩ ρ.hR hn
  hRK := ρ.hRK.conj n
  hr := conj_mem_conjSub ρ.hr
  hrW := fun h => ρ.hrW ((Thompson.mem_normalizer_iff_of_mem hn _).mp h)

theorem conjRep_img (hΩ : HypOmegaMod Ω) {n : G} (hn : n ∈ Subgroup.normalizer (W : Set G))
    (ρ : Thompson.Rep Ω W) :
    (conjRep hΩ hn ρ).img = Thompson.piG W n * ρ.img * (Thompson.piG W n)⁻¹ :=
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7D.conjRep_img hΩ hn ρ

end T7D
end Asc77

end

end CFSG.ClassicalInvolution.Q8P
