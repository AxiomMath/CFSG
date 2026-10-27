module

public import CFSG.ClassicalInvolution.AschTight.S1916Fus
public import CFSG.ClassicalInvolution.AschTight.S1911C8b

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G}

theorem Ctx12.card_Q [IsSimpleGroup G] (c : Ctx12 p f K z S W L t) :
    Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) = 2 * Nat.card ↥(W ⊓ sec19Y K z) := by
  rw [S1911.card_inf_sec19Y c.data, c.card, c.card_R]

theorem Ctx12.mem_Q_of_centralizes_t [IsSimpleGroup G] (c : Ctx12 p f K z S W L t)
    (h98 : L9_8GenSTmp) (h11 : C19_11Tmp p f) {x : G} (hxS : x ∈ (S : Subgroup G))
    (hxR : ∀ r ∈ (S : Subgroup G) ⊓ K, x * r = r * x) (hxt : x * t = t * x) :
    x ∈ (S : Subgroup G) ⊓ sec19Y K z := by
  have hd := c.hd
  have ht := hd.tight
  have hA := fun (y : G) (hy : y ∈ (S : Subgroup G)) hyQ => c.mem_R_of_centralizes_Q h98 h11 hy hyQ
  have hU₀card := c.card_Q
  have hU₀cyc := S1911.isCyclic_inf_sec19Y c.data
  obtain ⟨h, hhW, hzh⟩ := c.exists_conj_eq
  have hzK := isUniqueInvolution_of_tight ht.toTightBranch
  set Q := (S : Subgroup G) ⊓ sec19Y K z with hQdef
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set Y' := conjClosure C Q with hY'def
  have hY : YPrimeData K z Y' Q := sd_yPrimeData hd c.quat c.card
  have hY'Y : Y' ≤ sec19Y K z := conjClosure_le_of_normalizes inf_le_right fun d hd' =>
    mem_normalizer_iff_conjSub_eq.mp (sd_centralizer_le_normalizer_Y hd hd')
  have hzY := isUniqueInvolution_of_isSylow2In hY.sylow hY.inv hY.le
  have hY'K := not_mem_conjClass_of_centralizes ht hzY hY.cent
  have hY'ne : Y' ≠ K := fun h => hY'K (h ▸ CoreAssembly.mem_conjClass_self K)
  have hNK : C ≤ Subgroup.normalizer (K : Set G) := (sd_normalizer_eq hd).ge
  have hU₀Q : W ⊓ sec19Y K z ≤ Q := le_inf (inf_le_left.trans hd.hWS) inf_le_right
  have hUW : conjSub h (W ⊓ sec19Y K z) ≤ W := by
    have := conjSub_mono (n := h) (inf_le_left : W ⊓ sec19Y K z ≤ W)
    rwa [hhW] at this
  have hUS : conjSub h (W ⊓ sec19Y K z) ≤ (S : Subgroup G) := hUW.trans hd.hWS
  have hUJ : conjSub h (W ⊓ sec19Y K z) ≤ conjSub h Y' := conjSub_mono (hU₀Q.trans hY.sylow.1)
  have hJΩ : conjSub h Y' ∈ omegaPrime K Y' := Or.inr ⟨h, rfl⟩
  have hJQ : IsSylow2In (conjSub h Q) (conjSub h Y') := hY.sylow.conj h
  have hUmem : conjSub h (W ⊓ sec19Y K z) ∈ USet (omegaPrime K Y') :=
    mem_USet_of_natCard hJΩ hJQ (conjSub_mono hU₀Q) (isCyclic_conjSub hU₀cyc h)
      (by rw [natCard_conjSub, natCard_conjSub]; exact hU₀card)
  have hInA := c.inA_J hY hA hzh hUmem hUJ hUS
  have hJt : IsUniqueInvolution (conjSub h Y') t := hzh ▸ hzY.conj h
  have hUsyl : IsSylow2In (conjSub h (W ⊓ sec19Y K z)) (conjSub h Y' ⊓ C) := by
    refine isSylow2In_inf_of_half (S.isPGroup'.to_le hUS) (le_inf hUJ (hUS.trans hd.hSz))
      (fun T hT => ?_) (fun T hT hTC => ?_)
    · rw [hT.natCard_eq hJQ, natCard_conjSub, natCard_conjSub]
      exact hU₀card
    · exact hInA.2.1 ⟨hJΩ, hInA.1.2.1, T, mem_RSet_of_isSylow2In hJΩ hT, hT.1, hTC.trans hNK⟩
  have hMsyl := (inf_sup_eq_and_isSylow2In S hd.hSz (sup_le (sd_le_centralizer_K hd) hY.le)
    inf_le_right (fun y hy => mem_normalizer_sup (hNK hy) (hY.normal hy)) hUsyl hUS).2
  obtain ⟨W', hW', hW'S⟩ := exists_mem_WSet_omegaPrime_le ht hY c.quat S
  set Xg : Subgroup G := (S : Subgroup G) ⊓
    Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
    Subgroup.centralizer ({t} : Set G) with hXg
  have hXgS : Xg ≤ (S : Subgroup G) := inf_le_left.trans inf_le_left
  have hJN : Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer ((conjSub h Y' : Subgroup G) : Set G) := by
    have := centralizer_le_normalizer_conjSub hY.normal h
    rwa [hzh] at this
  have hPinv : ∀ y ∈ Xg, conjSub y ((S : Subgroup G) ⊓ ((K ⊔ Y') ⊔ (conjSub h Y' ⊓ C))) =
      (S : Subgroup G) ⊓ ((K ⊔ Y') ⊔ (conjSub h Y' ⊓ C)) := by
    intro y hy
    have hyC : y ∈ C := hd.hSz hy.1.1
    refine mem_normalizer_iff_conjSub_eq.mp
      (mem_normalizer_inf (Subgroup.le_normalizer hy.1.1) ?_)
    exact mem_normalizer_sup (mem_normalizer_sup (hNK hyC) (hY.normal hyC))
      (mem_normalizer_inf (hJN hy.2) (Subgroup.le_normalizer hyC))
  have hXgC : Xg ≤ Subgroup.centralizer ({z, t} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    rintro w (rfl | rfl)
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hy.1.1)).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
  have hJS : 2 < Nat.card ↥(conjSub h Y' ⊓ (S : Subgroup G)) := by
    have h1 := Subgroup.card_le_of_le (le_inf hUJ hUS)
    rw [natCard_conjSub, S1911.card_inf_sec19Y c.data] at h1
    have := c.four_le_card_V
    omega
  obtain ⟨-, h2⟩ := h98 G (omegaPrime K Y') (hypOmegaGen_omegaPrime ht hY) K
    (Or.inl (CoreAssembly.mem_conjClass_self K)) (conjSub h Y') hJΩ hInA z t hzK hJt Y'
    (Or.inr (CoreAssembly.mem_conjClass_self Y')) hY'ne (twinSet_omegaPrime ht hY)
    Xg (S.isPGroup'.to_le hXgS) hXgC _ hMsyl hPinv S (sup_le inf_le_left hXgS) hJS W' hW' hW'S
  obtain ⟨A, hAeq, -, -, hA1, hA2⟩ := h2 fun y hy w hw =>
    (Subgroup.mem_centralizer_iff.mp hy.1.2 w ⟨hW'S hw.1, hw.2⟩).symm
  have hB1 : W' ⊓ conjSub h Y' ≤ sec19X K z :=
    le_sec19X_of_isSylow2In hUsyl (hUW.trans c.W_le_X) inf_le_right
      (S.isPGroup'.to_le (inf_le_left.trans hW'S))
      (le_inf inf_le_right (inf_le_left.trans (hW'S.trans hd.hSz)))
  have hB2 : W' ⊓ K ≤ sec19X K z := inf_le_right.trans (le_sec19X ht.branch.member)
  have hBS : (W' ⊓ conjSub h Y') ⊔ (W' ⊓ K) ≤ (S : Subgroup G) :=
    sup_le (inf_le_left.trans hW'S) (inf_le_left.trans hW'S)
  have hAS : A ≤ (S : Subgroup G) := by
    have h1 : ((W' ⊓ conjSub h Y') ⊔ (W' ⊓ K)) ⊔ A ≤ (S : Subgroup G) := by
      rw [← hAeq]
      exact sup_le hBS hXgS
    exact le_sup_right.trans h1
  have hAX : A ≤ sec19X K z := by
    intro a ha
    have haS := hAS ha
    have ha1 := hA1 ha
    have hat : a * t = t * a := by
      have h3 := hJt.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hA2 ha).2.1)
      calc a * t = a * t * a⁻¹ * a := by group
        _ = t * a := by rw [h3]
    have haR : ∀ r ∈ (S : Subgroup G) ⊓ K, a * r = r * a := fun r hr =>
      commute_of_mem_centralizerModOdd ha1 (inf_le_right.trans le_sup_left)
        (S.isPGroup'.to_le inf_le_left)
        (mem_normalizer_inf_of_mem haS (hNK (hd.hSz haS))) hr
    have hav := S1911.comm_V_of_mem_A c.data haS
      (Subgroup.mem_centralizer_iff.mpr fun r hr => (haR r hr).symm)
      (Subgroup.mem_centralizer_singleton_iff.mpr hat)
    have ha1' : a ∈ centralizerModOdd ⊤ (Y' ⊔ K) := by
      rw [sup_comm]
      exact ha1
    exact c.W_le_X (h11 G K z S W hd ⟨haS, c.mem_cStar_X hY hY'Y haS ha1' hav⟩)
  have hxXg : x ∈ Xg := ⟨⟨hxS, Subgroup.mem_centralizer_iff.mpr fun r hr => (hxR r hr).symm⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩
  have h1 : x ∈ ((W' ⊓ conjSub h Y') ⊔ (W' ⊓ K)) ⊔ A := by
    rw [← hAeq]
    exact Subgroup.mem_sup_right hxXg
  have hxX : x ∈ sec19X K z := sup_le (sup_le hB1 hB2) hAX h1
  exact ⟨hxS, mem_sec19Y_of_centralizes ht (sd_isSylow2In_R hd) hxX
    (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxS)) fun r hr => (hxR r hr).symm⟩

theorem Ctx12.mem_Q_of_centralizes_R [IsSimpleGroup G] (c : Ctx12 p f K z S W L t)
    (h98 : L9_8GenSTmp) (h11 : C19_11Tmp p f) {x : G} (hxS : x ∈ (S : Subgroup G))
    (hxR : ∀ r ∈ (S : Subgroup G) ⊓ K, x * r = r * x) : x ∈ (S : Subgroup G) ⊓ sec19Y K z := by
  have hd := c.hd
  have ht := hd.tight
  have hzK := isUniqueInvolution_of_tight ht.toTightBranch
  have hzQ := sd_isUniqueInvolution_Q hd c.quat
  have htW : t ∈ W := c.data.leW c.data.memT
  have htS : t ∈ (S : Subgroup G) := hd.hWS htW
  have htX : t ∈ sec19X K z := c.W_le_X htW
  have ht2 := c.data.invL.sq
  have htz : t * z = z * t := (Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz htS))
  have hCQ : W ⊓ sec19Y K z ≤ (S : Subgroup G) ⊓ sec19Y K z :=
    le_inf (inf_le_left.trans hd.hWS) inf_le_right
  have hidx : (W ⊓ sec19Y K z).relIndex ((S : Subgroup G) ⊓ sec19Y K z) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := W ⊓ sec19Y K z)
      (K := (S : Subgroup G) ⊓ sec19Y K z)
    rw [inf_eq_left.mpr hCQ, c.card_Q] at h1
    have hpos : 0 < Nat.card ↥(W ⊓ sec19Y K z) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have htN : t ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ sec19Y K z : Subgroup G) : Set G) :=
    mem_normalizer_inf_of_mem htS (sd_centralizer_le_normalizer_Y hd (hd.hSz htS))
  have hnc : ∃ b ∈ (S : Subgroup G) ⊓ sec19Y K z, t * b ≠ b * t := by
    by_contra hcon
    push Not at hcon
    have h1 := c.mem_R_of_centralizes_Q h98 h11 htS hcon
    have h2 := (sd_isUniqueInvolution_R hd).unique t h1 ht2
    rcases h2 with h2 | h2
    · exact c.data.invL.ne_one h2
    · exact c.data.ne h2
  obtain ⟨q₀, hq₀, hq₀t⟩ := exists_conj_eq_mul_of_relIndex_two hCQ hidx htN
    (fun w hw => c.ab t htW w hw.1) hnc hzQ ht2 htz
  have hxW : x * t * x⁻¹ ∈ W := c.inv x hxS ▸ conj_mem_conjSub htW
  have hxX : x * t * x⁻¹ * t⁻¹ ∈ sec19X K z :=
    Subgroup.mul_mem _ (conjSub_sec19X K (hd.hSz hxS) ▸ conj_mem_conjSub htX)
      (Subgroup.inv_mem _ htX)
  have htNR : t ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    mem_normalizer_inf_of_mem htS ((sd_normalizer_eq hd).ge (hd.hSz htS))
  have hcomm := commutator_comm_of_normalizes hxR htNR
  have hcS : x * t * x⁻¹ * t⁻¹ ∈ (S : Subgroup G) :=
    S.mul_mem (S.mul_mem (S.mul_mem hxS htS) (S.inv_mem hxS)) (S.inv_mem htS)
  have hcY : x * t * x⁻¹ * t⁻¹ ∈ sec19Y K z :=
    mem_sec19Y_of_centralizes ht (sd_isSylow2In_R hd) hxX
      (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hcS)) fun r hr => (hcomm r hr).symm
  have hdich := conj_eq_or_of_mem c.ab htW ht2 hxW hzQ ⟨hcS, hcY⟩
  refine mem_of_conj_mem_pair hq₀ hq₀t hdich (c.mem_Q_of_centralizes_t h98 h11 hxS hxR) ?_
  refine c.mem_Q_of_centralizes_t h98 h11 (S.mul_mem (S.inv_mem hq₀.1) hxS) fun r hr => ?_
  have h1 := sd_commute_R_Q hd r hr q₀ hq₀
  calc q₀⁻¹ * x * r = q₀⁻¹ * (r * x) := by rw [mul_assoc, hxR r hr]
    _ = q₀⁻¹ * (r * q₀) * q₀⁻¹ * x := by group
    _ = q₀⁻¹ * (q₀ * r) * q₀⁻¹ * x := by rw [h1]
    _ = r * (q₀⁻¹ * x) := by group

theorem Ctx12.c19_12 [IsSimpleGroup G] (c : Ctx12 p f K z S W L t) (h98 : L9_8GenSTmp)
    (h11 : C19_11Tmp p f) :
    (S : Subgroup G) ⊓ K = (S : Subgroup G) ⊓
        Subgroup.centralizer (((S : Subgroup G) ⊓ sec19Y K z : Subgroup G) : Set G) ∧
      (S : Subgroup G) ⊓ sec19Y K z = (S : Subgroup G) ⊓
        Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  have hd := c.hd
  refine ⟨le_antisymm (fun x hx => ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    (sd_commute_R_Q hd x hx q hq).symm⟩) (fun x hx => c.mem_R_of_centralizes_Q h98 h11 hx.1
      fun q hq => (Subgroup.mem_centralizer_iff.mp hx.2 q hq).symm),
    le_antisymm (fun x hx => ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun r hr =>
      sd_commute_R_Q hd r hr x hx⟩) (fun x hx => c.mem_Q_of_centralizes_R h98 h11 hx.1
      fun r hr => (Subgroup.mem_centralizer_iff.mp hx.2 r hr).symm)⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
