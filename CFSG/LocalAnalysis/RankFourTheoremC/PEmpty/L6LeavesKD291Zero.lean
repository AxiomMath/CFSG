module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291Zero

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291

open CFSG.Open
open scoped commutatorElement

section Classification


theorem zero_of_cfg {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x z : Y}
    {L : Subgroup Y} (cfg : K62B.Cfg p P x z) (hLcomp : IsComponentOf L ⊤)
    (huniq : ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = L) : LinUniZero p L := by
  haveI : Fact p.Prime := ⟨cfg.prime⟩
  have hp5 : 5 ≤ p := cfg.five_le
  have hp2 : p ≠ 2 := by omega
  have hLq : CFSG.Open.IsQuasisimple ↥L := hLcomp.2.2
  have hLn : L.Normal := I291Zero.component_normal hLcomp huniq
  have hLne : L ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot L).1 (I291Zero.quasisimple_nontrivial hLq)
  have hdvdL : p ∣ Nat.card ↥L := by
    by_contra hnd
    have hcop : p.Coprime (Nat.card ↥L) := (Nat.Prime.coprime_iff_not_dvd cfg.prime).2 hnd
    have hle := CFSG.RankThreeCoreUniqueness.Helpers.normal_coprime_le_primeComplementCore
      p L hLn hcop
    rw [cfg.core, le_bot_iff] at hle
    exact hLne hle
  by_cases hR : CFSG.pCore p Y = ⊥
  · refine ⟨?_, fun g hg _ => ?_⟩
    · rw [hR]
      exact isCyclic_of_subsingleton
    · rw [hR, Subgroup.mem_bot] at hg
      rw [hg]
      exact L.one_mem
  · have hRP : CFSG.pCore p Y ≤ P := I291Zero.pCore_le_of_cfg cfg
    have hRn : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
    have hzR : z ∈ CFSG.pCore p Y := I291Zero.z_mem_normal cfg CFSG.pCore_normal hR
    have hzL : z ∈ L := I291Zero.z_mem_normal cfg hLn hLne
    have hLnR : ¬ L ≤ CFSG.pCore p Y := by
      intro h
      apply I291Zero.quasisimple_not_isPGroup (p := p) hLq
      intro g
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := Y)) ⟨(g : Y), h g.2⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have hRLc : ∀ g ∈ CFSG.pCore p Y, g ∈ L → ∀ h ∈ L, g * h = h * g := by
      intro g hg hgL h hh
      haveI : ((CFSG.pCore p Y).subgroupOf L).Normal := hRn.subgroupOf L
      have hNtop : (CFSG.pCore p Y).subgroupOf L ≠ ⊤ := by
        intro htop
        apply hLnR
        intro w hw
        have hwmem : (⟨w, hw⟩ : ↥L) ∈ (CFSG.pCore p Y).subgroupOf L := by
          rw [htop]
          exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.1 hwmem
      have hcen := I291Zero.normal_le_center_of_quasisimple hLq _ hNtop
      have hmem : (⟨g, hgL⟩ : ↥L) ∈ Subgroup.center ↥L :=
        hcen (Subgroup.mem_subgroupOf.2 hg)
      have hc := Subgroup.mem_center_iff.1 hmem ⟨h, hh⟩
      exact (congrArg Subtype.val hc).symm
    have hRcent : ∀ r ∈ CFSG.pCore p Y, ∀ g ∈ L, r * g = g * r := fun r hr g hg =>
      I291Zero.centralizes_of_perfect hLn hRn hLq.1 hRLc hr hg
    have hzcent : ∀ h ∈ L, h * z = z * h := fun h hh => (hRLc z hzR hzL h hh).symm
    have hRcyc : IsCyclic ↥(CFSG.pCore p Y) := by
      by_contra hRnc
      obtain ⟨U₂, hU₂R, hU₂pl, hU₂P⟩ :=
        CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1111b.input31_5_holds Y p cfg.prime hp2 P
          (CFSG.pCore p Y) cfg.isPGroup hRP (hRn.subgroupOf P) hRnc
      have hSn : ((L ⊓ P).subgroupOf P).Normal := by
        constructor
        intro n hn g
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact Subgroup.mem_inf.2 ⟨hLn.conj_mem _ (Subgroup.mem_inf.1 hn).1 g,
          P.mul_mem (P.mul_mem g.2 (Subgroup.mem_inf.1 hn).2) (P.inv_mem g.2)⟩
      have hSnc : ¬ IsCyclic ↥(L ⊓ P) := by
        intro hc
        obtain ⟨g₀, hg₀o, hg₀c⟩ :=
          CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
            hLq cfg.prime hp2 hdvdL
        have hg₀Y : orderOf (g₀ : Y) = p := by
          rw [Subgroup.orderOf_coe]
          exact hg₀o
        have hgp₀ : (g₀ : Y) ^ p = 1 := by
          rw [← hg₀Y]
          exact pow_orderOf_eq_one _
        obtain ⟨k, hk⟩ := I291Zero.exists_conj_mem_of_isSylowOf cfg.sylow
          (CFSG.LocalAnalysis.RankFourTheoremC.isPGroup_zpowers_of_pow_prime_eq_one hgp₀)
        set y : Y := k⁻¹ * (g₀ : Y) * k with hy
        have hyP : y ∈ P := hk _ (Subgroup.mem_zpowers _)
        have hyL : y ∈ L := by
          have := hLn.conj_mem (g₀ : Y) g₀.2 k⁻¹
          simpa [hy] using this
        have hyo : orderOf y = p := by
          have e : y = k⁻¹ * (g₀ : Y) * k⁻¹⁻¹ := by rw [hy, inv_inv]
          have hpow : y ^ p = 1 := by
            rw [e, conj_pow, hgp₀]
            group
          have hy1 : y ≠ 1 := by
            intro h1
            have h2 : (g₀ : Y) = 1 := by
              have h3 : (g₀ : Y) = k * (k⁻¹ * (g₀ : Y) * k) * k⁻¹ := by group
              rw [← hy, h1] at h3
              rw [h3]
              group
            have h4 : orderOf (g₀ : Y) = 1 := by rw [h2, orderOf_one]
            rw [hg₀Y] at h4
            exact cfg.prime.one_lt.ne' h4
          exact orderOf_eq_prime hpow hy1
        have hync : ¬ ∀ h ∈ L, h * y = y * h := by
          intro hcy
          apply hg₀c
          rw [Subgroup.mem_center_iff]
          intro h
          apply Subtype.ext
          have hh' : k⁻¹ * (h : Y) * k ∈ L := by
            simpa using hLn.conj_mem (h : Y) h.2 k⁻¹
          have hc' := hcy _ hh'
          have hg₀eq : (g₀ : Y) = k * y * k⁻¹ := by
            rw [hy]
            group
          show (h : Y) * (g₀ : Y) = (g₀ : Y) * (h : Y)
          rw [hg₀eq]
          calc (h : Y) * (k * y * k⁻¹) = k * ((k⁻¹ * (h : Y) * k) * y) * k⁻¹ := by group
            _ = k * (y * (k⁻¹ * (h : Y) * k)) * k⁻¹ := by rw [hc']
            _ = (k * y * k⁻¹) * (h : Y) := by group
        have hyS : y ∈ L ⊓ P := Subgroup.mem_inf.2 ⟨hyL, hyP⟩
        have hzS : z ∈ L ⊓ P := Subgroup.mem_inf.2 ⟨hzL, cfg.z_mem⟩
        have hyz : y ∈ Subgroup.zpowers z :=
          I291Zero.mem_zpowers_of_isCyclic hc hyS hzS
            (by rw [Nat.card_zpowers, hyo]) (by rw [Nat.card_zpowers, cfg.orderOf_z])
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hyz
        apply hync
        intro h hh
        rw [← hn]
        exact ((show Commute h z from hzcent h hh).zpow_right n).eq
      obtain ⟨U₁, hU₁S, hU₁pl, hU₁P⟩ :=
        CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1111b.input31_5_holds Y p cfg.prime hp2 P
          (L ⊓ P) cfg.isPGroup inf_le_right hSn hSnc
      have hU₁L : U₁ ≤ L := fun u hu => (Subgroup.mem_inf.1 (hU₁S hu)).1
      have hU₁P' : U₁ ≤ P := fun u hu => (Subgroup.mem_inf.1 (hU₁S hu)).2
      have hU₂P' : U₂ ≤ P := hU₂R.trans hRP
      have hnorm : ∀ V : Subgroup Y, P ≤ Subgroup.normalizer (V : Set Y) →
          ∀ g ∈ P, ∀ u ∈ V, g * u * g⁻¹ ∈ V := fun V hV g hg u hu =>
        (Subgroup.mem_normalizer_iff.1 (hV hg) u).1 hu
      have hcU₁ := cfg.comm_mem_zpowers hU₁P' (hnorm U₁ hU₁P) hU₁pl.2
      have hcU₂ := cfg.comm_mem_zpowers hU₂P' (hnorm U₂ hU₂P) hU₂pl.2
      obtain ⟨D, hD⟩ := I291Zero.exists_subgroup_commutator_mem x (I291Zero.zpowers_conj_eq cfg)
      have hU₁D : U₁ ≤ D := fun u hu => (hD u).2 ⟨hU₁P' hu, hcU₁ x cfg.x_mem u hu⟩
      have hU₂D : U₂ ≤ D := fun u hu => (hD u).2 ⟨hU₂P' hu, hcU₂ x cfg.x_mem u hu⟩
      have hcomm : ∀ a ∈ U₁, ∀ b ∈ U₂, a * b = b * a := fun a ha b hb =>
        (hRcent b (hU₂R hb) a (hU₁L ha)).symm
      have hFea := K62B.isElemAbelian_sup hU₁pl.1 hU₂pl.1 hcomm
      have hFcard : Nat.card ↥(U₁ ⊔ U₂) ≤ p ^ 2 :=
        cfg.card_le_sq_of_comm (sup_le hU₁P' hU₂P') hFea
          (fun e he => ((hD e).1 (sup_le hU₁D hU₂D he)).2)
      have hEq : U₁ = U₁ ⊔ U₂ :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hU₁pl.2]; exact hFcard)
      have hU₂U₁ : U₂ ≤ U₁ := by
        have h := (le_sup_right : U₂ ≤ U₁ ⊔ U₂)
        rw [← hEq] at h
        exact h
      exact I291Zero.plane_not_central cfg.prime hp5 hLcomp cfg.catalog hU₂pl (hU₂U₁.trans hU₁L)
        (fun v hv h hh => (hRLc v (hU₂R hv) (hU₁L (hU₂U₁ hv)) h hh).symm)
    refine ⟨hRcyc, fun g hg hgp => ?_⟩
    by_cases hg1 : g = 1
    · rw [hg1]
      exact L.one_mem
    have hgo : orderOf g = p := orderOf_eq_prime hgp hg1
    have hgz : g ∈ Subgroup.zpowers z :=
      I291Zero.mem_zpowers_of_isCyclic hRcyc hg hzR (by rw [Nat.card_zpowers, hgo])
        (by rw [Nat.card_zpowers, cfg.orderOf_z])
    exact (Subgroup.zpowers_le.2 hzL) hgz

end Classification

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291
