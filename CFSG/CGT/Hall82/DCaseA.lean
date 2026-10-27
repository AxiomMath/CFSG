module

public import CFSG.CGT.Hall82.DBasic
public import CFSG.RankThree.PartTwo.Sec15.Item1424Proof
public import CFSG.CGT.Hall82.Fusion

public section

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Hexa
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} {R : Subgroup G}
  {rep : Fin 64 → G}

theorem centralizer_rep_le_of_oval (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) {h : Fin 64} (hh : IsOvalVec h) :
    Subgroup.centralizer ({rep h} : Set G) ≤ M := by
  classical
  have htV : rep h ∈ blockU L := hc.mem h
  have htJ : rep h ∈ CFSG.Open.pCoreOf 2 M := by
    rw [S.pCoreOf_eq_blockU hF hc hC1]
    exact htV
  have ht1 : rep h ≠ 1 := by
    intro h0
    have hh0 : h = 0 := (rep_eq_one_iff hc).mp h0
    have hmem : (0 : Fin 64).val ∈ hallKList := by
      rw [← hh0]
      exact hh
    exact (by decide : (0 : Fin 64).val ∉ hallKList) hmem
  let R₀ : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({rep h} : Set G))
  have hR2 : IsPGroup 2 R₀ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRM : R₀ ≤ M :=
    S.pCoreOf_centralizer_singleton_le hF hc (S.hW2_of_eq_bot hC1) (S.hWab_of_eq_bot hC1) htJ
  let B : Subgroup (Equiv.Perm (Fin 64)) := S.psiSub hc R₀
  have hBle : B ≤ hexaM := S.psiSub_le_hexaM hc R₀
  have hB2 : IsPGroup 2 B := S.isPGroup_psiSub hc hR2
  have hBfix : ∀ b ∈ B, b h = h := by
    intro b hb
    rw [show B = S.psiSub hc R₀ from rfl, mem_psiSub S hc hRM] at hb
    obtain ⟨r, hrR, hrM, rfl⟩ := hb
    have hrc : r ∈ Subgroup.centralizer ({rep h} : Set G) :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hrR
    have hcomm : r * rep h = rep h * r :=
      (Subgroup.mem_centralizer_iff.mp hrc (rep h) (by simp)).symm
    apply hc.inj
    rw [S.rep_psiM hc ⟨r, hrM⟩ h]
    calc r * rep h * r⁻¹ = rep h * r * r⁻¹ := by rw [hcomm]
      _ = rep h := by group
  have hBnorm : ∀ a ∈ hexaL, a h = h → ∀ b ∈ B, a * b * a⁻¹ ∈ B := by
    intro a ha hah b hb
    obtain ⟨l, hlL, hlψ⟩ := S.exists_mem_L_psiM_eq hF hc ha
    rw [show B = S.psiSub hc R₀ from rfl, mem_psiSub S hc hRM] at hb ⊢
    obtain ⟨r, hrR, hrM, rfl⟩ := hb
    have hlC : (l : G) ∈ Subgroup.centralizer ({rep h} : Set G) := by
      have hp : (l : G) * rep h * (l : G)⁻¹ = rep h :=
        (conj_rep_eq_iff S hc l h).mpr (by rw [hlψ]; exact hah)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact (calc (l : G) * rep h = ((l : G) * rep h * (l : G)⁻¹) * (l : G) := by group
        _ = rep h * (l : G) := by rw [hp]).symm
    have hlnorm : (l : G) ∈ Subgroup.normalizer (R₀ : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hlC
    have hlrlR : (l : G) * r * (l : G)⁻¹ ∈ R₀ :=
      (Subgroup.mem_normalizer_iff.mp hlnorm r).mp hrR
    refine ⟨(l : G) * r * (l : G)⁻¹, hlrlR,
      M.mul_mem (M.mul_mem l.2 hrM) (M.inv_mem l.2), ?_⟩
    have hsub : (⟨(l : G) * r * (l : G)⁻¹,
        M.mul_mem (M.mul_mem l.2 hrM) (M.inv_mem l.2)⟩ : ↥M) =
        l * ⟨r, hrM⟩ * l⁻¹ := Subtype.ext rfl
    rw [hsub, map_mul, map_inv, map_mul, hlψ]
  have hBbot : B = ⊥ := hD.eq_bot_of_oval h hh B hBle hB2 hBfix hBnorm
  have hRV : R₀ ≤ blockU L := by
    intro r hr
    have hψ1 : S.psiM hc ⟨r, hRM hr⟩ = 1 := by
      have hmem : S.psiM hc ⟨r, hRM hr⟩ ∈ B := by
        rw [show B = S.psiSub hc R₀ from rfl, mem_psiSub S hc hRM]
        exact ⟨r, hr, hRM hr, rfl⟩
      rw [hBbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact (S.psiM_eq_one_iff_mem_blockU hc hC1 ⟨r, hRM hr⟩).mp hψ1
  have hVle : blockU L ≤ Subgroup.centralizer ({rep h} : Set G) ⊓
      Subgroup.centralizer (R₀ : Set G) := by
    refine le_inf ?_ ?_
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact (S.blockU_comm hv htV).symm
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (S.blockU_comm hv (hRV hr)).symm
  have hVleR : blockU L ≤ R₀ := hVle.trans
    (CFSG.RankThree.PartTwo.Sec15.inf_centralizer_le_pCoreOf_of_fitting
      (G := G) (Y := Subgroup.centralizer ({rep h} : Set G)) (S.cent (rep h) htJ ht1))
  have hReq : R₀ = blockU L := le_antisymm hRV hVleR
  intro x hx
  have hxnorm : x ∈ Subgroup.normalizer (R₀ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hx
  rwa [hReq, S.normalizer_blockU_eq] at hxnorm

theorem mem_of_conj_oval (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) {g : G} {h h' : Fin 64}
    (hh : IsOvalVec h) (hh' : IsOvalVec h') (hg : g * rep h * g⁻¹ = rep h') :
    g ∈ M := by
  obtain ⟨a, haL, ha⟩ := hD.oval_trans h h' hh hh'
  obtain ⟨m, hmL, hmψ⟩ := S.exists_mem_L_psiM_eq hF hc haL
  have hmconj : (m : G) * rep h * (m : G)⁻¹ = rep h' := by
    rw [← S.rep_psiM hc m h, hmψ, ha]
  have hgt : (m : G)⁻¹ * g ∈ Subgroup.centralizer ({rep h} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact (calc ((m : G)⁻¹ * g) * rep h
        = (m : G)⁻¹ * (g * rep h * g⁻¹) * g := by group
      _ = (m : G)⁻¹ * rep h' * g := by rw [hg]
      _ = (m : G)⁻¹ * ((m : G) * rep h * (m : G)⁻¹) * g := by rw [hmconj]
      _ = rep h * ((m : G)⁻¹ * g) := by group).symm
  have hgtM : (m : G)⁻¹ * g ∈ M :=
    centralizer_rep_le_of_oval S hF hD hc hC1 hh hgt
  have hgM : g ∈ M := by
    have h := M.mul_mem (S.le hmL) hgtM
    rwa [show (m : G) * ((m : G)⁻¹ * g) = g by group] at h
  exact hgM

theorem conj_rep_ne_of_oval (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) {h v : Fin 64} (hh : IsOvalVec h)
    (hv : v ≠ 0) (hvK : ¬ IsOvalVec v) (g : G) :
    g * rep h * g⁻¹ ≠ rep v := by
  intro hconj
  have hChM : Subgroup.centralizer ({rep h} : Set G) ≤ M :=
    centralizer_rep_le_of_oval S hF hD hc hC1 hh
  have hcardCh : Nat.card (Subgroup.centralizer ({rep h} : Set G)) =
      64 * Nat.card (stabSub (S.psiSub hc M) h) := by
    have h := S.card_centralizer_rep hc hC1 h
    rwa [inf_eq_right.mpr hChM] at h
  have hCv_eq : Subgroup.centralizer ({rep v} : Set G) =
      (Subgroup.centralizer ({rep h} : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [← centralizer_zpowers_eq_centralizer_singleton (rep v),
      ← centralizer_zpowers_eq_centralizer_singleton (rep h),
      CFSG.Glauberman.map_centralizer_eq_of_equiv (MulAut.conj g)
        (Subgroup.zpowers (rep h))]
    congr 1
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply, hconj]
  have hcardCv : Nat.card (Subgroup.centralizer ({rep v} : Set G)) =
      Nat.card (Subgroup.centralizer ({rep h} : Set G)) := by
    rw [hCv_eq, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hdiv : Nat.card ↥(M ⊓ Subgroup.centralizer ({rep v} : Set G)) ∣
      Nat.card (Subgroup.centralizer ({rep v} : Set G)) :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [hcardCv, hcardCh, S.card_centralizer_rep hc hC1 v] at hdiv
  rcases S.psiSub_M_eq hF hc hC1 with hψ | hψ
  · rw [hψ, hD.card_stabL_oval h hh, hD.card_stabL v hv hvK] at hdiv
    norm_num at hdiv
  · rw [hψ, hD.card_stab_oval h hh, hD.card_stab v hv hvK] at hdiv
    norm_num at hdiv

theorem exists_conj_of_conj (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) {v w : Fin 64} (hv : v ≠ 0) {g : G}
    (hg : g * rep v * g⁻¹ = rep w) :
    ∃ l ∈ L, l * rep v * l⁻¹ = rep w := by
  have hw0 : w ≠ 0 := by
    intro hw
    have h1 : rep w = 1 := by rw [hw, hc.rep_zero]
    have h2 : rep v = 1 := by
      calc rep v = g⁻¹ * (g * rep v * g⁻¹) * g := by group
        _ = g⁻¹ * rep w * g := by rw [hg]
        _ = 1 := by rw [h1]; group
    exact hv ((rep_eq_one_iff hc).mp h2)
  by_cases hvo : IsOvalVec v
  · have hwo : IsOvalVec w := by
      by_contra hwo
      exact conj_rep_ne_of_oval S hF hD hc hC1 (h := v) (v := w) hvo hw0 hwo g hg
    obtain ⟨a, haL, ha⟩ := hD.oval_trans v w hvo hwo
    obtain ⟨l, hlL, hlψ⟩ := S.exists_mem_L_psiM_eq hF hc haL
    exact ⟨l, hlL, by rw [← S.rep_psiM hc l v, hlψ, ha]⟩
  · have hwo : ¬ IsOvalVec w := by
      intro hwo
      refine conj_rep_ne_of_oval S hF hD hc hC1 (h := w) (v := v) hwo hv hvo
        (g := g⁻¹) ?_
      calc g⁻¹ * rep w * (g⁻¹)⁻¹ = g⁻¹ * (g * rep v * g⁻¹) * g := by
            rw [hg]; group
        _ = rep v := by group
    obtain ⟨a, haL, ha⟩ := hD.five_trans v hv hvo
    obtain ⟨b, hbL, hb⟩ := hD.five_trans w hw0 hwo
    have hba : b * a⁻¹ ∈ hexaL := hexaL.mul_mem hbL (hexaL.inv_mem haL)
    obtain ⟨l, hlL, hlψ⟩ := S.exists_mem_L_psiM_eq hF hc hba
    have hav : a⁻¹ v = 5 := by
      have h := congrArg (fun x => a⁻¹ x) ha
      simpa using h.symm
    have hbav : (b * a⁻¹) v = w := by
      calc (b * a⁻¹) v = b (a⁻¹ v) := rfl
        _ = b 5 := by rw [hav]
        _ = w := hb
    refine ⟨l, hlL, ?_⟩
    rw [← S.rep_psiM hc l v, hlψ, hbav]

theorem centralizer_rep_le (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : Subgroup.centralizer ({rep 5} : Set G) ≤ M) {v : Fin 64} (hv : v ≠ 0) :
    Subgroup.centralizer ({rep v} : Set G) ≤ M := by
  by_cases hvo : IsOvalVec v
  · exact centralizer_rep_le_of_oval S hF hD hc hC1 hvo
  · obtain ⟨a, haL, ha⟩ := hD.five_trans v hv hvo
    obtain ⟨l, hlL, hlψ⟩ := S.exists_mem_L_psiM_eq hF hc haL
    have hlconj : (l : G) * rep 5 * (l : G)⁻¹ = rep v := by
      rw [← S.rep_psiM hc l 5, hlψ, ha]
    intro x hx
    have hx' : (l : G)⁻¹ * x * (l : G) ∈ Subgroup.centralizer ({rep 5} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      have hcomm : x * rep v = rep v * x :=
        (Subgroup.mem_centralizer_iff.mp hx (rep v) (by simp)).symm
      exact (calc ((l : G)⁻¹ * x * (l : G)) * rep 5
          = (l : G)⁻¹ * (x * ((l : G) * rep 5 * (l : G)⁻¹)) * (l : G) := by group
        _ = (l : G)⁻¹ * (x * rep v) * (l : G) := by rw [hlconj]
        _ = (l : G)⁻¹ * (rep v * x) * (l : G) := by rw [hcomm]
        _ = rep 5 * ((l : G)⁻¹ * x * (l : G)) := by
            rw [← hlconj]; group).symm
    have hxM : x ∈ M := by
      have h := M.mul_mem (M.mul_mem (S.le hlL) (hcM hx')) (M.inv_mem (S.le hlL))
      rwa [show (l : G) * ((l : G)⁻¹ * x * (l : G)) * (l : G)⁻¹ = x by group] at h
    exact hxM

theorem mem_of_conj_le (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : Subgroup.centralizer ({rep 5} : Set G) ≤ M) {g : G}
    (hg : CFSG.CGT.Timmesfeld75.conjSubgroup g (blockU L) ≤ M) : g ∈ M := by
  classical
  let A : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup g (blockU L)
  have hAM : A ≤ M := hg
  have hA2 : IsPGroup 2 A := by
    rw [show A = (blockU L).map (MulAut.conj g).toMonoidHom from rfl]
    exact (IsPGroup.of_card (n := 6) (by rw [S.card_blockU]; norm_num)).map
      (MulAut.conj g).toMonoidHom
  have hAcard : Nat.card A = 64 := by
    rw [show A = (blockU L).map (MulAut.conj g).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, S.card_blockU]
  let B : Subgroup (Equiv.Perm (Fin 64)) := S.psiSub hc A
  have hBle : B ≤ hexaM := S.psiSub_le_hexaM hc A
  have hB2 : IsPGroup 2 B := S.isPGroup_psiSub hc hA2
  have hcard : Nat.card A = Nat.card ↥(A ⊓ blockU L) * Nat.card B :=
    S.card_eq_card_inf_blockU_mul hc hC1 hAM
  have hBdvd64 : Nat.card B ∣ 64 := by
    refine ⟨Nat.card ↥(A ⊓ blockU L), ?_⟩
    rw [mul_comm]
    exact hAcard.symm.trans hcard
  have hBle32 : Nat.card B ≤ 32 := by
    by_cases hBL : B ≤ hexaL
    · have hdvdL : Nat.card B ∣ 1080 := by
        rw [← hF.card]
        exact Subgroup.card_dvd_of_le hBL
      have hdvd8 : Nat.card B ∣ 8 := by
        have h := Nat.dvd_gcd hBdvd64 hdvdL
        norm_num at h ⊢
        exact h
      exact (Nat.le_of_dvd (by norm_num) hdvd8).trans (by norm_num)
    · have hfix0 : (0 : Fin 64) ∈ fixPts B := by
        intro b hb
        exact hF.apply_zero b (hBle hb)
      haveI : Nonempty ↥(fixPts B) := ⟨⟨0, hfix0⟩⟩
      have hfixpos : 0 < Nat.card (fixPts B) := Nat.card_pos
      have h1 : Nat.card B ≤ Nat.card B * Nat.card (fixPts B) := by
        calc Nat.card B = Nat.card B * 1 := by rw [mul_one]
          _ ≤ Nat.card B * Nat.card (fixPts B) := Nat.mul_le_mul_left _ hfixpos
      exact h1.trans (hF.le_32_of_not_le B hBle hB2 hBL)
  have hAle2 : 2 ≤ Nat.card ↥(A ⊓ blockU L) := by
    have hle : 64 ≤ Nat.card ↥(A ⊓ blockU L) * 32 := by
      calc 64 = Nat.card A := hAcard.symm
        _ = Nat.card ↥(A ⊓ blockU L) * Nat.card B := hcard
        _ ≤ Nat.card ↥(A ⊓ blockU L) * 32 := Nat.mul_le_mul_left _ hBle32
    omega
  have hnt : Nontrivial ↥(A ⊓ blockU L) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr fun hbot => by
      rw [hbot, Subgroup.card_bot] at hAle2
      omega
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(A ⊓ blockU L))
  have hzV : (z : G) ∈ blockU L := z.2.2
  have hzA : (z : G) ∈ A := z.2.1
  have hz1' : (z : G) ≠ 1 := by
    intro h0
    exact hz1 (Subtype.ext h0)
  have hzA' : g⁻¹ * (z : G) * g ∈ blockU L :=
    (CFSG.CGT.Timmesfeld75.mem_conjSubgroup).mp hzA
  obtain ⟨u, hu⟩ := (mem_blockU_iff hc).mp hzA'
  obtain ⟨w, hw⟩ := (mem_blockU_iff hc).mp hzV
  have hu0 : u ≠ 0 := by
    intro h0
    apply hz1'
    have h1 : rep u = 1 := by rw [h0, hc.rep_zero]
    rw [hu] at h1
    calc (z : G) = g * (g⁻¹ * (z : G) * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h1]
      _ = 1 := by group
  have hconj_uw : g * rep u * g⁻¹ = rep w := by
    rw [hu, hw]
    group
  obtain ⟨l, hlL, hlconj⟩ := exists_conj_of_conj S hF hD hc hC1 hu0 hconj_uw
  have hlgC : (l : G)⁻¹ * g ∈ Subgroup.centralizer ({rep u} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact (calc ((l : G)⁻¹ * g) * rep u
        = (l : G)⁻¹ * (g * rep u * g⁻¹) * g := by group
      _ = (l : G)⁻¹ * ((l : G) * rep u * (l : G)⁻¹) * g := by rw [hconj_uw, hlconj]
      _ = rep u * ((l : G)⁻¹ * g) := by group).symm
  have hlgM : (l : G)⁻¹ * g ∈ M :=
    centralizer_rep_le S hF hD hc hC1 hcM hu0 hlgC
  have hgM : g ∈ M := by
    have h := M.mul_mem (S.le hlL) hlgM
    rwa [show (l : G) * ((l : G)⁻¹ * g) = g by group] at h
  exact hgM

theorem isTI_blockU (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : Subgroup.centralizer ({rep 5} : Set G) ≤ M) :
    CFSG.CGT.Timmesfeld75.IsTI (blockU L) := by
  classical
  intro g
  by_cases hbot : blockU L ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g (blockU L) = ⊥
  · exact Or.inl hbot
  · right
    have hnt : Nontrivial ↥(blockU L ⊓
        CFSG.CGT.Timmesfeld75.conjSubgroup g (blockU L)) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hbot
    obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(blockU L ⊓
      CFSG.CGT.Timmesfeld75.conjSubgroup g (blockU L)))
    have hzV : (z : G) ∈ blockU L := z.2.1
    have hzA : (z : G) ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g (blockU L) := z.2.2
    have hz1' : (z : G) ≠ 1 := by
      intro h0
      exact hz1 (Subtype.ext h0)
    have hAab : ∀ a ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g (blockU L),
        ∀ b ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g (blockU L), a * b = b * a := by
      intro a ha b hb
      rw [CFSG.CGT.Timmesfeld75.conjSubgroup, Subgroup.mem_map] at ha hb
      obtain ⟨a0, ha0, rfl⟩ := ha
      obtain ⟨b0, hb0, rfl⟩ := hb
      rw [← map_mul, ← map_mul, S.blockU_comm ha0 hb0]
    have hAcent : CFSG.CGT.Timmesfeld75.conjSubgroup g (blockU L) ≤
        Subgroup.centralizer ({(z : G)} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact (hAab a ha z hzA).symm
    obtain ⟨w, hw⟩ := (mem_blockU_iff hc).mp hzV
    have hw0 : w ≠ 0 := by
      intro h0
      apply hz1'
      rw [← hw, h0, hc.rep_zero]
    have hAM : CFSG.CGT.Timmesfeld75.conjSubgroup g (blockU L) ≤ M :=
      hAcent.trans (by simpa [hw] using centralizer_rep_le S hF hD hc hC1 hcM hw0)
    have hgM : g ∈ M := mem_of_conj_le S hF hD hc hC1 hcM hAM
    have hgnorm : g ∈ Subgroup.normalizer (blockU L : Set G) := by
      rw [S.normalizer_blockU_eq]
      exact hgM
    have hAeq : CFSG.CGT.Timmesfeld75.conjSubgroup g (blockU L) = blockU L := by
      rw [CFSG.CGT.Timmesfeld75.conjSubgroup]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgnorm
    rw [hAeq, inf_idem]

theorem weaklyClosedIn_blockU (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : Subgroup.centralizer ({rep 5} : Set G) ≤ M) :
    CFSG.CGT.Timmesfeld75.WeaklyClosedIn (blockU L)
      (Subgroup.normalizer (blockU L : Set G)) := by
  refine ⟨Subgroup.le_normalizer, ?_⟩
  intro g hg
  have hAM : CFSG.CGT.Timmesfeld75.conjSubgroup g (blockU L) ≤ M := by
    simpa [S.normalizer_blockU_eq] using hg
  have hgM : g ∈ M := mem_of_conj_le S hF hD hc hC1 hcM hAM
  rw [CFSG.CGT.Timmesfeld75.conjSubgroup]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (by rw [S.normalizer_blockU_eq]; exact hgM)

theorem inCatalog_of_centralizer_le
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement)
    (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : Subgroup.centralizer ({rep 5} : Set G) ≤ M) :
    CFSG.Assembly.InCatalog G := by
  have hV1 : blockU L ≠ ⊥ := by
    intro hbot
    have h : Nat.card (blockU L) = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    rw [S.card_blockU] at h
    norm_num at h
  exact inCatalog_of_isTI_of_weaklyClosedIn hNode S.simple S.nonab S.elemU hV1
    (isTI_blockU S hF hD hc hC1 hcM) (weaklyClosedIn_blockU S hF hD hc hC1 hcM)

end CFSG.CGT.Hall82.Setting
