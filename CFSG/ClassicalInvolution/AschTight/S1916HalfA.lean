module

public import CFSG.ClassicalInvolution.AschTight.S1916Dich
public import CFSG.ClassicalInvolution.AschTight.Sec19L98
public import CFSG.ClassicalInvolution.AschTight.S1916InA

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_comm_of_normalizes {H : Subgroup G} {x t : G}
    (hxH : ∀ q ∈ H, x * q = q * x) (htH : t ∈ Subgroup.normalizer (H : Set G)) :
    ∀ q ∈ H, (x * t * x⁻¹ * t⁻¹) * q = q * (x * t * x⁻¹ * t⁻¹) := by
  intro q hq
  have hq' : t⁻¹ * q * t ∈ H := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (H : Set G)).inv_mem htH) q).mp
      hq
    rwa [inv_inv] at this
  have h1 := hxH _ hq'
  have h2 : x⁻¹ * (t⁻¹ * q * t) = (t⁻¹ * q * t) * x⁻¹ := by
    calc x⁻¹ * (t⁻¹ * q * t) = x⁻¹ * ((t⁻¹ * q * t) * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * (t⁻¹ * q * t)) * x⁻¹ := by rw [h1]
      _ = (t⁻¹ * q * t) * x⁻¹ := by group
  calc x * t * x⁻¹ * t⁻¹ * q = x * t * (x⁻¹ * (t⁻¹ * q * t)) * t⁻¹ := by group
    _ = x * t * ((t⁻¹ * q * t) * x⁻¹) * t⁻¹ := by rw [h2]
    _ = (x * q) * t * x⁻¹ * t⁻¹ := by group
    _ = (q * x) * t * x⁻¹ * t⁻¹ := by rw [hxH q hq]
    _ = q * (x * t * x⁻¹ * t⁻¹) := by group

variable {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G}

theorem Ctx12.centralizer_le_normalizer_L (c : Ctx12 p f K z S W L t) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hd := c.hd
  have hzK := isUniqueInvolution_of_tight hd.tight.toTightBranch
  obtain ⟨g, hg⟩ := c.data.memL
  change conjSub g K = L at hg
  have e : t = g * z * g⁻¹ := c.data.invL.eq (hg ▸ hzK.conj g)
  rw [e, ← hg]
  exact centralizer_le_normalizer_conjSub (sd_normalizer_eq hd).ge g

theorem Ctx12.four_le_card_V [IsSimpleGroup G] (c : Ctx12 p f K z S W L t) :
    4 ≤ Nat.card ↥(L ⊓ W) := by
  have ht := c.hd.tight
  have h8 := (exists_ne_comm_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member
    (mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self K) (sd_isSylow2In_R c.hd))).2
  have := c.card_R
  omega

theorem Ctx12.two_lt_card_L_inf_S [IsSimpleGroup G] (c : Ctx12 p f K z S W L t) :
    2 < Nat.card ↥(L ⊓ (S : Subgroup G)) := by
  have h1 := c.four_le_card_V
  have h2 := Subgroup.card_le_of_le (inf_le_inf_left L c.hd.hWS)
  omega

theorem Ctx12.mem_R_of_centralizes_t [IsSimpleGroup G] (c : Ctx12 p f K z S W L t)
    (h98 : L9_8GenSTmp) (h11 : C19_11Tmp p f) {x : G} (hxS : x ∈ (S : Subgroup G))
    (hxQ : ∀ q ∈ (S : Subgroup G) ⊓ sec19Y K z, x * q = q * x) (hxt : x * t = t * x) :
    x ∈ (S : Subgroup G) ⊓ K := by
  have hd := c.hd
  have ht := hd.tight
  set Q := (S : Subgroup G) ⊓ sec19Y K z with hQdef
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set Y' := conjClosure C Q with hY'def
  have hY : YPrimeData K z Y' Q := sd_yPrimeData hd c.quat c.card
  have hY'Y : Y' ≤ sec19Y K z := conjClosure_le_of_normalizes inf_le_right fun d hd' =>
    mem_normalizer_iff_conjSub_eq.mp (sd_centralizer_le_normalizer_Y hd hd')
  have hzY := isUniqueInvolution_of_isSylow2In hY.sylow hY.inv hY.le
  have hY'K := not_mem_conjClass_of_centralizes ht hzY hY.cent
  have hKY' : K ≠ Y' := fun h => hY'K (h ▸ CoreAssembly.mem_conjClass_self K)
  have hNK : C ≤ Subgroup.normalizer (K : Set G) := (sd_normalizer_eq hd).ge
  set Xg : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer (Q : Set G) ⊓
    Subgroup.centralizer ({t} : Set G) with hXg
  have hXgS : Xg ≤ (S : Subgroup G) := inf_le_left.trans inf_le_left
  have hMsyl := (inf_sup_eq_and_isSylow2In S hd.hSz (sup_le hY.le (sd_le_centralizer_K hd))
    inf_le_right (fun y hy => mem_normalizer_sup (hY.normal hy) (hNK hy)) c.isSylow2In_V
    (inf_le_right.trans hd.hWS)).2
  obtain ⟨W', hW', hW'S⟩ := exists_mem_WSet_omegaPrime_le ht hY c.quat S
  have hPinv : ∀ y ∈ Xg, conjSub y ((S : Subgroup G) ⊓ ((Y' ⊔ K) ⊔ (L ⊓ C))) =
      (S : Subgroup G) ⊓ ((Y' ⊔ K) ⊔ (L ⊓ C)) := by
    intro y hy
    have hyC : y ∈ C := hd.hSz hy.1.1
    have hyL : y ∈ Subgroup.normalizer (L : Set G) := c.centralizer_le_normalizer_L hy.2
    refine mem_normalizer_iff_conjSub_eq.mp
      (mem_normalizer_inf (Subgroup.le_normalizer hy.1.1) ?_)
    exact mem_normalizer_sup (mem_normalizer_sup (hY.normal hyC) (hNK hyC))
      (mem_normalizer_inf hyL (Subgroup.le_normalizer hyC))
  have hXgC : Xg ≤ Subgroup.centralizer ({z, t} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    rintro w (rfl | rfl)
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hy.1.1)).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
  obtain ⟨-, h2⟩ := h98 G (omegaPrime K Y') (hypOmegaGen_omegaPrime ht hY) Y'
    (Or.inr (CoreAssembly.mem_conjClass_self Y')) L (Or.inl c.data.memL) (c.inA_L hY) z t hzY
    c.data.invL K (Or.inl (CoreAssembly.mem_conjClass_self K)) hKY' (twinSet_omegaPrime' ht hY)
    Xg (S.isPGroup'.to_le hXgS) hXgC _ hMsyl hPinv S (sup_le inf_le_left hXgS)
    c.two_lt_card_L_inf_S W' hW' hW'S
  obtain ⟨A, hAeq, -, -, hA1, hA2⟩ := h2 fun y hy w hw =>
    (Subgroup.mem_centralizer_iff.mp hy.1.2 w ⟨hW'S hw.1, hY'Y hw.2⟩).symm
  have hB1 : W' ⊓ L ≤ sec19X K z :=
    c.le_X_of_le_inf (S.isPGroup'.to_le (inf_le_left.trans hW'S))
      (le_inf inf_le_right (inf_le_left.trans (hW'S.trans hd.hSz)))
  have hB2 : W' ⊓ Y' ≤ sec19X K z := inf_le_right.trans (hY'Y.trans (sec19Y_le_sec19X K z))
  have hBS : (W' ⊓ L) ⊔ (W' ⊓ Y') ≤ (S : Subgroup G) :=
    sup_le (inf_le_left.trans hW'S) (inf_le_left.trans hW'S)
  have hAS : A ≤ (S : Subgroup G) := by
    have h1 : ((W' ⊓ L) ⊔ (W' ⊓ Y')) ⊔ A ≤ (S : Subgroup G) := by
      rw [← hAeq]
      exact sup_le hBS hXgS
    exact le_sup_right.trans h1
  have hAX : A ≤ sec19X K z := by
    intro a ha
    have haS := hAS ha
    have ha2 := hA2 ha
    have hav : ∀ v ∈ L ⊓ W, a * v = v * a := fun v hv =>
      commute_of_mem_centralizerModOdd ha2 (inf_le_left : L ⊓ (S : Subgroup G) ≤ L)
        (S.isPGroup'.to_le inf_le_right)
        (mem_normalizer_inf ha2.2.1 (Subgroup.le_normalizer haS)) ⟨hv.1, hd.hWS hv.2⟩
    exact c.W_le_X (h11 G K z S W hd ⟨haS, c.mem_cStar_X hY hY'Y haS (hA1 ha) hav⟩)
  have hxXg : x ∈ Xg := ⟨⟨hxS, Subgroup.mem_centralizer_iff.mpr fun q hq => (hxQ q hq).symm⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩
  have h1 : x ∈ ((W' ⊓ L) ⊔ (W' ⊓ Y')) ⊔ A := by
    rw [← hAeq]
    exact Subgroup.mem_sup_right hxXg
  exact c.mem_R_of_centralizes (sup_le (sup_le hB1 hB2) hAX h1) hxS hxQ

theorem Ctx12.mem_R_of_centralizes_Q [IsSimpleGroup G] (c : Ctx12 p f K z S W L t)
    (h98 : L9_8GenSTmp) (h11 : C19_11Tmp p f) {x : G} (hxS : x ∈ (S : Subgroup G))
    (hxQ : ∀ q ∈ (S : Subgroup G) ⊓ sec19Y K z, x * q = q * x) : x ∈ (S : Subgroup G) ⊓ K := by
  have hd := c.hd
  obtain ⟨r₀, hr₀, hr₀t⟩ := S1911.exists_conj_eq_mul c.data
  have htW : t ∈ W := c.data.leW c.data.memT
  have htS : t ∈ (S : Subgroup G) := hd.hWS htW
  have htX : t ∈ sec19X K z := c.W_le_X htW
  have hxW : x * t * x⁻¹ ∈ W := c.inv x hxS ▸ conj_mem_conjSub htW
  have hxX : x * t * x⁻¹ * t⁻¹ ∈ sec19X K z :=
    Subgroup.mul_mem _ (conjSub_sec19X K (hd.hSz hxS) ▸ conj_mem_conjSub htX)
      (Subgroup.inv_mem _ htX)
  have htN : t ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ sec19Y K z : Subgroup G) : Set G) :=
    mem_normalizer_inf_of_mem htS (sd_centralizer_le_normalizer_Y hd (hd.hSz htS))
  have hcR := c.mem_R_of_centralizes hxX
    (S.mul_mem (S.mul_mem (S.mul_mem hxS htS) (S.inv_mem hxS)) (S.inv_mem htS))
    (commutator_comm_of_normalizes hxQ htN)
  have hdich := conj_eq_or_of_mem c.ab htW c.data.invL.sq hxW (sd_isUniqueInvolution_R hd) hcR
  refine mem_of_conj_mem_pair hr₀ hr₀t hdich (c.mem_R_of_centralizes_t h98 h11 hxS hxQ) ?_
  refine c.mem_R_of_centralizes_t h98 h11 (S.mul_mem (S.inv_mem hr₀.1) hxS) fun q hq => ?_
  have h1 := sd_commute_R_Q hd r₀ hr₀ q hq
  calc r₀⁻¹ * x * q = r₀⁻¹ * (q * x) := by rw [mul_assoc, hxQ q hq]
    _ = r₀⁻¹ * (q * r₀) * r₀⁻¹ * x := by group
    _ = r₀⁻¹ * (r₀ * q) * r₀⁻¹ * x := by rw [h1]
    _ = q * (r₀⁻¹ * x) := by group

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
