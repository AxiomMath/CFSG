module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step39Core
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step39Suz
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step37Cent
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38Model
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38Suz

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.ABGLocalTools Sec3

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}

theorem exists_sec38Hyp_omega
    (h17 : Step17G24Odd) (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) :
    ∃ H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀,
      (∃ τ : G, IsTau A₁ V x z τ) ∧
        omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range := by
  have hS := hQ.dData.suz
  obtain ⟨hT, hext, hcard, hsyl, hB₀⟩ :=
    step37_of h17 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ
  obtain ⟨hQB₀, hB₀N, φ, hφs, hφk⟩ := sec3B0_proof G A A₁ R g E F x Zs P T Q B₀ z y hS
  have hB₀card : Nat.card B₀ = 25920 * Nat.card Q := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hφk, Nat.card_congr (subgroupOfEquivOfLe hQB₀).toEquiv, MonoidHom.range_eq_top.mpr hφs,
      card_top, (SuzB0.omega_facts SuzB0.b0_parts.2.2.2.2.2.2).1] at h
    rw [← h, mul_comm]
  let H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ :=
    { q0 := hQ
      T_le := hT
      ext := hext
      card := hcard
      sylow := hsyl
      B₀_le := hB₀
      x_not := (sec3Q0_facts hQ).2
      B₀_perf := (perfect_B₀_and_T_le hS).1
      B₀_simple := fun _ hNB hBN hNQ => eq_of_normal_of_not_le hS hNB hBN hNQ
      B₀_quot := ⟨hQB₀, hB₀N⟩
      B₀_card := hB₀card }
  have hTx : T ≤ centralizer ({x} : Set G) :=
    hS.T_le.trans (map_subtype_le _ : sec3B A₁ x ≤ centralizer ({x} : Set G))
  have hTC : Nat.card ↥(T ⊓ centralizer (Q : Set G)) ≤ 2 :=
    card_le_two_of_le_centralizer_Q hS (hS.T_two.to_le inf_le_left) inf_le_right
      (inf_le_left.trans hTx)
  obtain ⟨τ, v₀, hτ, hV⟩ := exists_tau_sec38V hQ (T_le_normalizer_V hQ) hTC
  have hclaim := centQCommX_of hS
  have hW₀a : ∀ w ∈ H.xsub.clSub Q₀, H.xsub.q w = 0 → w = 0 := fun _ hw hq => H.W₀_aniso hw hq
  have hstab : ∀ k ∈ omegaGroup H.xsub.q H.xsub.q_nondegenerate,
      (H.xsub.clSub Q₀).map (k : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) = H.xsub.clSub Q₀ →
        k ∈ H.ρG.range ⊓ omegaGroup H.xsub.q H.xsub.q_nondegenerate := fun k hk hkW =>
    mem_inf.mpr ⟨H.mem_range_of_stab hτ hclaim
      (MinusLines.card_omegaStab H.xsub.q_nondegenerate H.finrank_Qt H.isPlusType H.finrank_W₀
        hW₀a).le hk hkW, hk⟩
  have hmove : ∃ k ∈ H.ρG.range ⊓ omegaGroup H.xsub.q H.xsub.q_nondegenerate,
      (H.xsub.clSub Q₀).map (k : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) ≠ H.xsub.clSub Q₀ := by
    obtain ⟨n, hn, hne⟩ := H.exists_move hV
    exact ⟨H.ρG n, mem_inf.mpr ⟨⟨n, rfl⟩, hn⟩, hne⟩
  have hΩ' := MinusLines.eq_omegaGroup_of_stab_le H.xsub.q_nondegenerate H.finrank_Qt
    H.isPlusType H.finrank_W₀ hW₀a inf_le_right hstab hmove
  exact ⟨H, ⟨τ, hτ⟩, fun k hk => (mem_inf.mp (hΩ'.ge hk)).1⟩

theorem step39_of
    (h17 : Step17G24Odd) : Step39 := by
  intro G _ _ A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ hO
  have hS := hQ.dData.suz
  obtain ⟨H, ⟨τ, hτ⟩, hΩ⟩ := exists_sec38Hyp_omega h17 hQ
  have hC := H.centralizer_le_zpowers hO
  have hle := H.range_le_omega hC hΩ
    (fun w hw => exists_mem_sec3B_of_comm hS hτ.normB hτ.inv_x hw)
    (fun k hk => exists_mem_B₀_of_mem_centralizer hS hk)
  have hrange : H.ρG.range = omegaGroup H.xsub.q H.xsub.q_nondegenerate := le_antisymm hle hΩ
  obtain ⟨e⟩ := CFSG.LargeExtraspecial.S14.nonempty_omegaGroup_equiv_omegaPlus
    H.xsub.q_nondegenerate (m := 4) (by rw [H.finrank_Qt]) (by norm_num) H.isPlusType
  let ρΩ : ↥(normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) →*
      ↥(omegaGroup H.xsub.q H.xsub.q_nondegenerate) :=
    H.ρG.codRestrict _ fun n => hle ⟨n, rfl⟩
  refine ⟨e.toMonoidHom.comp ρΩ, fun k => ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hΩ (e.symm k).2
    refine ⟨n, ?_⟩
    have h1 : ρΩ n = e.symm k := Subtype.ext hn
    show e (ρΩ n) = k
    rw [h1, MulEquiv.apply_symm_apply]
  · rw [hO, sup_bot_eq]
    ext n
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    show e (ρΩ n) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    constructor
    · intro h
      have h1 : H.ρG n = 1 := congrArg Subtype.val h
      exact H.mem_Q₁_of_ρ_eq_one hC ((H.ρG_eq_one_iff n).mp h1)
    · intro h
      apply Subtype.ext
      exact (H.ρG_eq_one_iff n).mpr (H.xsub.ρ_eq_one_of_mem h)

end CFSG.ComponentClassification.AS81
