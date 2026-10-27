module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5S22Set
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Six20
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P09Syl
public import CFSG.Goldschmidt.Steps.Balance
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Odd
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Five
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Perm
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5JStar

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}

theorem oddCoreSub_conj {h o : MulAut ↥d.s56V} (hh : h ∈ Hs d) (ho : o ∈ oddCoreSub (Hs d)) :
    h * o * h⁻¹ ∈ oddCoreSub (Hs d) :=
  CFSG.Goldschmidt.Balance.conj_mem_oddCoreOf (H := Hs d) hh ho

theorem oddCoreSub_odd : Odd (Nat.card (oddCoreSub (Hs d))) :=
  CFSG.Goldschmidt.Balance.odd_card_oddCoreOf (Hs d)

theorem oddCoreSub_le : oddCoreSub (Hs d) ≤ Hs d := Subgroup.map_subtype_le _

theorem not_zpowers_x5_le_oddCore (h49 : d.Thm49Statement) (hd : d.Hyp)
    (hWcard : Nat.card (Ws d) = 2 ^ 8) : ¬ zpowers (star d d.x₅) ≤ oddCoreSub (Hs d) := by
  intro hXO
  have hW0Hs : W0s d ≤ Hs d := (CFSG.LieType.BorelTits.pCoreOf_le 2 (Ks d)).trans inf_le_right
  have hW : Ws d ≤ oddCoreSub (Hs d) := by
    rw [Ws_eq h49 hd, Subgroup.commutator_le]
    intro a ha b hb
    have e : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact mul_mem (oddCoreSub_conj (hW0Hs ha) (hXO hb)) (Subgroup.inv_mem _ (hXO hb))
  have h1 := Subgroup.card_dvd_of_le hW
  rw [hWcard] at h1
  have h2 : 2 ∣ Nat.card (oddCoreSub (Hs d)) := (dvd_pow_self 2 (by norm_num : 8 ≠ 0)).trans h1
  exact (Nat.not_even_iff_odd.2 (oddCoreSub_odd (d := d))) (even_iff_two_dvd.2 h2)

theorem Ws_centralizes_oddCore (h49 : d.Thm49Statement) (hd : d.Hyp)
    (hxO : ∀ o ∈ oddCoreSub (Hs d), star d d.x₅ * o = o * star d d.x₅) :
    ∀ w ∈ Ws d, ∀ o ∈ oddCoreSub (Hs d), w * o = o * w := by
  have hW0Hs : W0s d ≤ Hs d := (CFSG.LieType.BorelTits.pCoreOf_le 2 (Ks d)).trans inf_le_right
  have hle : Ws d ≤ centralizer ((oddCoreSub (Hs d) : Subgroup (MulAut ↥d.s56V)) :
      Set (MulAut ↥d.s56V)) := by
    rw [Ws_eq h49 hd, Subgroup.commutator_le]
    intro a ha b hb
    refine mem_centralizer_iff.2 fun o ho => ?_
    have hbO : ∀ o ∈ oddCoreSub (Hs d), b * o = o * b := by
      intro o ho
      obtain ⟨n, rfl⟩ := hb
      exact (Commute.zpow_left (show Commute (star d d.x₅) o from hxO o ho) n).eq
    have hc : a⁻¹ * o * a ∈ oddCoreSub (Hs d) := by
      have := oddCoreSub_conj (Subgroup.inv_mem _ (hW0Hs ha)) ho
      simpa using this
    have hb1 : b * (a⁻¹ * o * a) = (a⁻¹ * o * a) * b := hbO _ hc
    have hb2 : o * b⁻¹ = b⁻¹ * o := by
      have h := hbO o ho
      calc o * b⁻¹ = b⁻¹ * (b * o) * b⁻¹ := by group
        _ = b⁻¹ * (o * b) * b⁻¹ := by rw [h]
        _ = b⁻¹ * o := by group
    have e : ⁅a, b⁆ = a * b * a⁻¹ * b⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    calc o * (a * b * a⁻¹ * b⁻¹) = a * ((a⁻¹ * o * a) * b) * a⁻¹ * b⁻¹ := by group
      _ = a * (b * (a⁻¹ * o * a)) * a⁻¹ * b⁻¹ := by rw [hb1]
      _ = a * b * a⁻¹ * (o * b⁻¹) := by group
      _ = a * b * a⁻¹ * (b⁻¹ * o) := by rw [hb2]
      _ = a * b * a⁻¹ * b⁻¹ * o := by group
  intro w hw o ho
  exact (mem_centralizer_iff.1 (hle hw) o ho).symm

theorem commutes_of_star_mem (hWg : img d (Wg d z₀) = Ws d) {g v : G} (hg : g ∈ Hg d)
    (hgW : star d g ∈ Ws d) (hv : v ∈ centralizer ((Wg d z₀ : Subgroup G) : Set G))
    (hvV : v ∈ d.s56V) : g * v = v * g := by
  rw [← hWg] at hgW
  obtain ⟨w, hw, hwN, hwg⟩ := (mem_imgIn_iff d.s56V (Wg d z₀)).1 hgW
  have hc : w⁻¹ * g ∈ centralizer ((d.s56V : Subgroup G) : Set G) :=
    (actFun_eq_iff d.s56V hwN hg).1 hwg
  have h1 : v * (w⁻¹ * g) = (w⁻¹ * g) * v := mem_centralizer_iff.1 hc v hvV
  have h2 : w * v = v * w := mem_centralizer_iff.1 hv w hw
  calc g * v = w * ((w⁻¹ * g) * v) := by group
    _ = w * (v * (w⁻¹ * g)) := by rw [h1]
    _ = (w * v) * (w⁻¹ * g) := by group
    _ = (v * w) * (w⁻¹ * g) := by rw [h2]
    _ = v * g := by group

theorem Zz_le_V (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) : Zz d z₀ ≤ d.s56V :=
  sup_le (zpowers_le.2 (hd.s56_E_le_V h49 hd.s56_z_mem_E)) (zpowers_le.2 hz.mem_V)

theorem Zz_eq_inf_centralizer (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hCV : d.s56V ⊓ centralizer ((Ug d : Subgroup G) : Set G) = Zz d z₀)
    (hWg : img d (Wg d z₀) = Ws d) (hUW : Us d ≤ Ws d)
    (hKz : ∀ k ∈ Kg d, k * d.z = d.z * k) :
    Zz d z₀ = d.s56V ⊓ centralizer ((Wg d z₀ : Subgroup G) : Set G) := by
  apply le_antisymm
  · intro v hv
    refine ⟨Zz_le_V h49 hd hz hv, mem_centralizer_iff.2 fun w hw => ?_⟩
    have hwz₀ : w * z₀ = z₀ * w := mem_centralizer_singleton_iff.1 hw.2
    have hwK : w ∈ Kg d :=
      preIn_mono d.s56V (CFSG.LieType.BorelTits.pCoreOf_le 2 (Ks d)) hw.1
    have hwz : w * d.z = d.z * w := hKz w hwK
    have hS : Zz d z₀ ≤ centralizer ({w} : Set G) :=
      sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hwz.symm))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 hwz₀.symm))
    exact (mem_centralizer_singleton_iff.1 (hS hv)).symm
  · rintro v ⟨hvV, hvC⟩
    rw [← hCV]
    refine ⟨hvV, mem_centralizer_iff.2 fun u hu => ?_⟩
    have huH : u ∈ Hg d := preIn_le_normalizer d.s56V (Us d) hu
    have hstar : star d u ∈ Ws d := hUW ((mem_preIn_iff d.s56V (Us d)).1 hu).2
    exact commutes_of_star_mem hWg huH hstar hvC hvV

theorem Zz_normalized (hZ : Zz d z₀ = d.s56V ⊓ centralizer ((Wg d z₀ : Subgroup G) : Set G))
    (hWg : img d (Wg d z₀) = Ws d) (hWn : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d) :
    ∀ h ∈ Hg d, ∀ x ∈ Zz d z₀, h * x * h⁻¹ ∈ Zz d z₀ := by
  intro h hh x hx
  rw [hZ] at hx ⊢
  obtain ⟨hxV, hxC⟩ := hx
  refine ⟨(mem_normalizer_iff.1 hh x).1 hxV, mem_centralizer_iff.2 fun w hw => ?_⟩
  have hwH : w ∈ Hg d := preIn_le_normalizer d.s56V _ hw.1
  have hg : h⁻¹ * w * h ∈ Hg d :=
    mul_mem (mul_mem (Subgroup.inv_mem _ hh) hwH) hh
  have hstarw : star d w ∈ Ws d := hWg ▸ actFun_mem_imgIn hw hwH
  have hhS : star d h ∈ Hs d := actFun_mem_imgIn hh hh
  have hgW : star d (h⁻¹ * w * h) ∈ Ws d := by
    have h1 := hWn _ (Subgroup.inv_mem _ hhS) _ hstarw
    have e : star d (h⁻¹ * w * h) = (star d h)⁻¹ * star d w * ((star d h)⁻¹)⁻¹ := by
      show actFun d.s56V (h⁻¹ * w * h) = (actFun d.s56V h)⁻¹ * actFun d.s56V w * ((actFun d.s56V h)⁻¹)⁻¹
      rw [actFun_mul d.s56V (mul_mem (Subgroup.inv_mem _ hh) hwH) hh,
        actFun_mul d.s56V (Subgroup.inv_mem _ hh) hwH, actFun_inv d.s56V hh, inv_inv]
    rw [e]
    exact h1
  have hc := commutes_of_star_mem hWg hg hgW hxC hxV
  calc w * (h * x * h⁻¹) = h * ((h⁻¹ * w * h) * x) * h⁻¹ := by group
    _ = h * (x * (h⁻¹ * w * h)) * h⁻¹ := by rw [hc]
    _ = (h * x * h⁻¹) * w := by group

theorem Hg_le_normalizer_Zz
    (hZn : ∀ h ∈ Hg d, ∀ x ∈ Zz d z₀, h * x * h⁻¹ ∈ Zz d z₀) :
    Hg d ≤ normalizer ((Zz d z₀ : Subgroup G) : Set G) := by
  intro h hh
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hZn h hh x hx, fun hx => ?_⟩
  have := hZn h⁻¹ (Subgroup.inv_mem _ hh) _ hx
  simpa [mul_assoc] using this

theorem Zz_card_four (hd : d.Hyp) (hz : d.S56Z0 z₀) (hinv : d.S56Z0Inv) :
    Nat.card (Zz d z₀) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz02 : z₀ * z₀ = 1 := hinv z₀ hz
  have hzt : d.t * d.z = d.z * d.t :=
    (mem_centralizer_singleton_iff.1 (hd.L_le d.z_mem)).symm
  have hz1 : z₀ ≠ 1 := fun e => t_not_comm_z0 hd hz (by rw [e]; simp)
  have hzz0 : z₀ ≠ d.z := fun e => t_not_comm_z0 hd hz (by rw [e]; exact hzt)
  have hzsq : d.z * d.z = 1 := by
    have := pow_orderOf_eq_one d.z
    rw [hd.s56_orderOf_z, pow_two] at this
    exact this
  have hz0ord : Nat.card (zpowers z₀) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by simpa [pow_two] using hz02) hz1
  have hdisj : Disjoint (zpowers d.z) (zpowers z₀) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro a ⟨haz, haz0⟩
    rcases mem_zpowers_sq_one hz02 haz0 with h1 | h1
    · rw [h1]; exact one_mem _
    · exfalso
      rw [h1] at haz
      rcases mem_zpowers_sq_one hzsq haz with h2 | h2
      · exact hz1 h2
      · exact hzz0 h2
  have hn : zpowers z₀ ≤ normalizer ((zpowers d.z : Subgroup G) : Set G) :=
    zpowers_le.2 (normalizer_zpowers_of_commute (hz.cen hd.s56_z_mem_E))
  rw [Zz, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hn hdisj,
    hd.s56_card_zpowers_z, hz0ord]

theorem t_not_mem_H0 (hd : d.Hyp) (hz : d.S56Z0 z₀) : d.t ∉ H0 d z₀ := by
  intro h
  have h1 : z₀ * d.t = d.t * z₀ := mem_centralizer_iff.1 h.2 z₀ (mem_sup_right (mem_zpowers z₀))
  exact t_not_comm_z0 hd hz h1.symm

theorem Hg_quotient_perm (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hinv : d.S56Z0Inv) (hZn : ∀ h ∈ Hg d, ∀ x ∈ Zz d z₀, h * x * h⁻¹ ∈ Zz d z₀) :
    ∃ _ : ((H0 d z₀).subgroupOf (Hg d)).Normal,
      Nonempty (↥(Hg d) ⧸ (H0 d z₀).subgroupOf (Hg d) ≃* Equiv.Perm (Fin 2)) ∨
        Nonempty (↥(Hg d) ⧸ (H0 d z₀).subgroupOf (Hg d) ≃* Equiv.Perm (Fin 3)) := by
  have hle : Hg d ≤ normalizer ((Zz d z₀ : Subgroup G) : Set G) := Hg_le_normalizer_Zz hZn
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥(Hg d) →* MulAut ↥(Zz d z₀),
      ∀ g : ↥(Hg d), ρ g = actFun (Zz d z₀) (g : G) :=
    ⟨(conjActHom (Zz d z₀)).comp (Subgroup.inclusion hle),
      fun g => (actFun_of_mem _ (hle g.2)).symm⟩
  have hker : ρ.ker = (H0 d z₀).subgroupOf (Hg d) := by
    ext g
    rw [MonoidHom.mem_ker, hρ, Subgroup.mem_subgroupOf, actFun_eq_one_iff _ (hle g.2)]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  have hn : ((H0 d z₀).subgroupOf (Hg d)).Normal := hker ▸ ρ.normal_ker
  have htH : d.t ∈ Hg d := t_mem_Hg h49 hd
  have ht : ρ ⟨d.t, htH⟩ ≠ 1 := by
    intro h
    rw [hρ, actFun_eq_one_iff _ (hle htH)] at h
    exact t_not_comm_z0 hd hz
      (mem_centralizer_iff.1 h z₀ (mem_sup_right (mem_zpowers z₀))).symm
  have ht2 : (⟨d.t, htH⟩ : ↥(Hg d)) * ⟨d.t, htH⟩ = 1 := Subtype.ext hd.t_mul_self
  refine ⟨hn, ?_⟩
  rcases quotient_equiv_perm_of_mulAut (Zz_card_four hd hz hinv) ρ ht ht2 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans e⟩
  · exact Or.inr ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans e⟩

theorem step23a_holds : Step23a := by
  intro G _ _ d z₀ h49 hd hz hinv h10 h14 h16 h17s h17 h19 h20 h21 h22
  obtain ⟨-, -, -, hSC⟩ := h14
  obtain ⟨-, hUcard, -⟩ := h17s
  obtain ⟨hCV, -, -, hCcent, -, -⟩ := h17
  obtain ⟨-, -, ⟨-, hKz⟩, -, hWg, hWquot, hWab, hWcard⟩ := h19
  obtain ⟨-, -, hTI, -, hSylW, -, -, -⟩ := h20
  have hxH : d.x₅ ∈ Hg d := x5_mem_Hg h49 hd
  have htH : d.t ∈ Hg d := t_mem_Hg h49 hd
  have hxHs : star d d.x₅ ∈ Hs d := actFun_mem_imgIn hxH hxH
  have htHs : star d d.t ∈ Hs d := actFun_mem_imgIn htH htH
  have hx1 : star d d.x₅ ≠ 1 := star_x5_ne_one_of_card h49 hd hUcard
  have hx5 : star d d.x₅ ^ 5 = 1 := star_x5_pow_five h49 hd
  have hxC : star d d.x₅ ∈ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d :=
    ⟨mem_centralizer_singleton_iff.2 (actFun_comm_of_comm d.s56V hd.s56_x5_comm_t), hxHs⟩
  have hinvO : ∀ o ∈ oddCoreSub (Hs d), star d d.t * o * (star d d.t)⁻¹ = o⁻¹ :=
    inverts_of_hall (O := oddCoreSub (Hs d)) (Hs := Hs d) (oddCoreSub_odd (d := d))
      (oddCoreSub_le (d := d)) (fun h hh o ho => oddCoreSub_conj hh ho) htHs
      (star_t_mul_self h49 hd) (star_t_ne h49 hd hz) (card_centralizer_star_t_dvd h49 hd hCcent)
      hx5 hx1 hxC (not_zpowers_x5_le_oddCore h49 hd hWcard)
  obtain ⟨h, hhH, hh⟩ := hSC
  have hconj : star d (h * d.t * h⁻¹) = star d h * star d d.t * (star d h)⁻¹ :=
    actFun_conj d.s56V hhH htH
  have hg : ∃ h ∈ Hs d, star d (d.t * d.pv 2) = h * star d d.t * h⁻¹ :=
    ⟨star d h, actFun_mem_imgIn hhH hhH, by rw [← hh, hconj]⟩
  have hgx : star d (d.t * d.pv 2) * star d d.x₅ * (star d (d.t * d.pv 2))⁻¹ = (star d d.x₅)⁻¹ := by
    have e : star d (d.t * d.pv 2) = star d d.t * star d (d.pv 2) :=
      actFun_mul d.s56V htH (pv2_mem_Hg h49 hd)
    have hax : star d d.t * star d d.x₅ = star d d.x₅ * star d d.t :=
      (actFun_comm_of_comm d.s56V hd.s56_x5_comm_t).symm
    have hax' : star d d.t * star d d.x₅ * (star d d.t)⁻¹ = star d d.x₅ := by
      rw [hax]; group
    rw [e]
    calc star d d.t * star d (d.pv 2) * star d d.x₅ * (star d d.t * star d (d.pv 2))⁻¹
        = star d d.t * (star d (d.pv 2) * star d d.x₅ * (star d (d.pv 2))⁻¹) * (star d d.t)⁻¹ := by
          group
      _ = star d d.t * (star d d.x₅)⁻¹ * (star d d.t)⁻¹ := by rw [star_pv2_inv_x5 h49 hd]
      _ = (star d d.t * star d d.x₅ * (star d d.t)⁻¹)⁻¹ := by group
      _ = (star d d.x₅)⁻¹ := by rw [hax']
  have hxO : ∀ o ∈ oddCoreSub (Hs d), star d d.x₅ * o = o * star d d.x₅ :=
    centralizes_of_inverted (O := oddCoreSub (Hs d)) (Hs := Hs d)
      (fun h hh o ho => oddCoreSub_conj hh ho) htHs hinvO hg hgx hxHs hx5
  obtain ⟨S, hTS, hS⟩ := exists_le_fusionIsSylowIn_two (p09_sylow hd).2.1 hTI
  have hN := (h22 S ⟨hS, hTS⟩).2.2
  have hWn : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d :=
    normalizes_of_sup_odd hWab (oddCoreSub_odd (d := d)) (Ws_centralizes_oddCore h49 hd hxO) hN
  have hUW : Us d ≤ Ws d := hWquot.1
  have hZ : Zz d z₀ = d.s56V ⊓ centralizer ((Wg d z₀ : Subgroup G) : Set G) :=
    Zz_eq_inf_centralizer h49 hd hz hCV hWg hUW hKz
  have hZn : ∀ h ∈ Hg d, ∀ x ∈ Zz d z₀, h * x * h⁻¹ ∈ Zz d z₀ := Zz_normalized hZ hWg hWn
  have hxz : ∀ x ∈ Zz d z₀, d.x₅ * x = x * d.x₅ := by
    intro x hx
    have hle : Zz d z₀ ≤ centralizer ({d.x₅} : Set G) :=
      sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hd.s56_x5_comm_z.symm))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 hz.comm_x.symm))
    exact (mem_centralizer_singleton_iff.1 (hle hx)).symm
  have hJZ : Jg d ≤ centralizer ((Zz d z₀ : Subgroup G) : Set G) :=
    (Jg_le_H0 hZn hxz hxH).trans inf_le_right
  have hWJ : Ws d ≤ img d (Jg d) := Ws_le_Js h49 hd
  have hJC := Js_inf_centralizer h10 hWab hWg hZ hJZ hSylW hWJ
  refine ⟨hinvO, ⟨hWn, ?_⟩, ⟨hZ, hZn⟩, t_not_mem_H0 hd hz, Hg_quotient_perm h49 hd hz hinv hZn, hWJ,
    Js_quotient hxH hWn hJC h21⟩
  rw [img_Xg h49 hd]
  exact zpowers_le.2 (mem_centralizer_iff.2 fun o ho => (hxO o ho).symm)

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
