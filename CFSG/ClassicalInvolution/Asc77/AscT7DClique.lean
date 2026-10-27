module

public import CFSG.ClassicalInvolution.Asc77.AscT7DRS
public import CFSG.ClassicalInvolution.Asc77.AscT7BMu23
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenSubStab
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenClique

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

section Conj

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem Hyp23Setting.conj (h : Hyp23Setting p f Ω K K' z) (g : G) :
    Hyp23Setting p f Ω (conjSub g K) (conjSub g K') (g * z * g⁻¹) where
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

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

omit [Finite G] in
theorem rep_mem_muDelta (ρ : Thompson.Rep Ω W) :
    (⟨ρ.img, rep_img_mem ρ⟩ : ↥(muGroup Ω W)) ∈ Thompson.muDelta Ω W :=
  ⟨ρ.R, ρ.hR, ρ.r, ρ.hr, ρ.hrW, rfl⟩

theorem muDelta_nonempty (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hW : W ∈ WSet Ω) : (Thompson.muDelta Ω W).Nonempty := by
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : Subgroup G, IsSylow2In R₀ K := by
    obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    exact ⟨R₀, hR₀⟩
  obtain ⟨S, hRS⟩ := hR₀.2.1.exists_le_sylow
  obtain ⟨g, hg⟩ := Thompson.exists_conj_mem_DSet hp hq hΩ hW S
  have hRD : conjSub g R₀ ∈ DSet Ω W := hg R₀ (mem_RSet_of_isSylow2In hK hR₀) hRS
  obtain ⟨ρ, -, -⟩ := exists_rep hp hq hΩ hW (hΩ.conjInvariant g K hK) (hR₀.conj g) hRD
  exact ⟨_, rep_mem_muDelta ρ⟩

theorem ncard_cent_le_two {K K' : Subgroup G} {z : G} (hs : Hyp23Setting p f Ω K K' z)
    (hW : W ∈ WSet Ω) {d : ↥(muGroup Ω W)} (hd : d ∈ Thompson.muDelta Ω W) :
    (Star3T.cent (Thompson.muDelta Ω W) d).ncard ≤ 2 := by
  have hst : AscStand p f Ω K := hs.stand
  have hc : Thompson.Ctx p f Ω W := ctx_of_stand hst hW
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

theorem exists_cent_ne {K K' : Subgroup G} {z : G} (hs : Hyp23Setting p f Ω K K' z)
    (hW : W ∈ WSet Ω) {d : ↥(muGroup Ω W)} (hd : d ∈ Thompson.muDelta Ω W) :
    ∃ x ∈ Thompson.muDelta Ω W, x ≠ d ∧ x * d = d * x := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hc : Thompson.Ctx p f Ω W := ctx_of_stand hst hW
  obtain ⟨ρ, hρd⟩ := Thompson.exists_rep_of_mem_muDelta hd
  obtain ⟨g, hg⟩ := hst.trans ρ.K ρ.hK
  have hs' := hs.conj g
  rw [hg] at hs'
  obtain ⟨hRW, hUW, -, h4, -⟩ := Thompson.inf_W_of_mem_D hp hq hΩ hW ρ.hR ρ.hK ρ.hRK
  have h2 : IsPGroup 2 ↥(ρ.K ⊓ W) := hΩ.isPGroup_of_mem_USet hp hUW
  obtain ⟨x₀, hx₀, o₀⟩ := AscP1Nine3.exists_orderOf_four_of_four_le hs'.hz inf_le_left h2
    (by rw [← hRW]; exact h4)
  have hzdW : g * z * g⁻¹ ∈ W := by
    rw [← T7A.sq_eq_of_orderOf_four hs'.hz hx₀.1 o₀]
    exact W.mul_mem hx₀.2 hx₀.2
  obtain ⟨S₁, R₁, R₁', hWS₁, hR₁, hR₁', hR₁S, hR₁'S⟩ := exists_sylow_frame hs' hW hzdW
  have hK₁' : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hs.hK'.1
  have hR₁'D : R₁' ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hWS₁ (mem_RSet_of_isSylow2In hK₁' hR₁') hR₁'S
  obtain ⟨ρ', hρ'K, -⟩ := exists_rep hp hq hΩ hW hK₁' hR₁' hR₁'D
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

variable {p f : ℕ} [Fact p.Prime]

theorem c23_1_clique_proved : C23_1_clique p f := by
  intro G _ _ _ Ω K K' z hs W hW
  have hst : AscStand p f Ω K := hs.stand
  refine ⟨T7D.muDelta_nonempty hst.odd hst.five hst.hyp hst.mem hW, fun d hd => ?_⟩
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

end CFSG.ClassicalInvolution.Asc77
