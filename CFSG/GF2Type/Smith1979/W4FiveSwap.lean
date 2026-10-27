module

public import CFSG.GF2Type.Smith1979.W4FiveOne
public import CFSG.LargeExtraspecial.S5Eight

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Five

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S5 CFSG.Open CFSG.ComponentClassification

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem conj_mem_Nbar_w4 (haQ : g * S.z * g⁻¹ ∈ S.QG) {t r n : S.O} (hr : r ∈ Rbar S g t)
    (hn : n ∈ Nbar S g t) : r * n * r⁻¹ ∈ Nbar S g t := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
  exact conj_mem_Nbar haQ (commute_of_mem_Rbar haQ hr) hn

theorem swap_step1 (D : SwapData S g) (H : Hyp4 S g) (C : Cons311 S g) :
    ∃ (s : S.O) (hsZ : s ∈ D.Z), s ≠ 1 ∧ (∃ k : ℕ, s ^ (2 ^ k) = 1) ∧
      D.chi ⟨s, hsZ⟩ ∈ S.Lbar g ∧ ∃ B : Subgroup S.O, B ≤ S.Lbar g ∧ IsSylowTwoIn B D.Xhat := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haQ := H.conj_mem
  obtain ⟨T, hT, hLT⟩ := exists_isSylowTwoIn_ge (S.Lbar_le_Mbar g) (S4.isPGroup_Lbar S haQ)
  have hTN : T ≤ normalizer (S.Lbar g : Set S.O) :=
    S4.le_normalizer_of_weaklyClosed C.weaklyClosed hT.isPGroup hT.le hLT
  have hP := hT.inf_of_isSubnormal D.isComponentOf.2.1
  have hPne := hP.ne_bot (two_dvd_card_of_isQuasisimple D.isQuasisimple_Z)
  obtain ⟨⟨s, hsP⟩, hs1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hPne
  have hs1 : s ≠ 1 := fun h => hs1' (Subtype.ext h)
  have hsZ : s ∈ D.Z := hsP.2
  obtain ⟨ks, hks⟩ := hP.exists_pow_eq_one hsP
  have hPL : ∀ x (hx : x ∈ T ⊓ D.Z), D.chi ⟨x, hx.2⟩ ∈ S.Lbar g := fun x hx => by
    obtain ⟨k, hk⟩ := hP.exists_pow_eq_one hx
    exact D.chi_mem_Lbar H ⟨x, hx.2⟩ (hTN hx.1) hk
  have hsL : D.chi ⟨s, hsZ⟩ ∈ S.Lbar g := hPL s hsP
  set B := ((T ⊓ D.Z).subgroupOf D.Z).map D.chi with hB
  have hBL : B ≤ S.Lbar g := by
    rintro _ ⟨⟨x, hxZ⟩, hx, rfl⟩
    exact hPL x (mem_subgroupOf.mp hx)
  have hBX : IsSylowTwoIn B D.Xhat := by
    have := hP.subgroupOf_top.map D.chi
    rwa [← MonoidHom.range_eq_map] at this
  exact ⟨s, hsZ, hs1, ⟨ks, hks⟩, hsL, B, hBL, hBX⟩

structure SwapFacts (D : SwapData S g) (H : Hyp4 S g) : Prop where
  XR : D.Xhat ≤ Rbar S g D.t
  XN : ¬ D.Xhat ≤ Nbar S g D.t
  RL : Rbar S g D.t ≠ S.Lbar g
  Xsub : IsSubnormal D.Xhat (Rbar S g D.t)
  fac : ∀ x ∈ RmodN S g D.t, ∃ k ∈ imgR H.conj_mem D.t D.Xhat, ∃ e ∈ LmodN S g D.t, x = k * e
  VQ : ¬ V S g D.t ≤ S.Qa g
  LN : ∀ τ ∈ S.Lbar g ⊓ Nbar S g D.t, τ = 1 ∨ τ = D.t

theorem swap_facts (D : SwapData S g) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (Q : Hyp45Q H C) : SwapFacts D H := by
  have haQ := H.conj_mem
  have htL := D.mem_Lbar
  have ht1 := D.t_ne_one
  obtain ⟨s, hsZ, hs1, ⟨ks, hks⟩, hsL, B, hBL, hBX⟩ := swap_step1 D H C
  have hXR := D.Xhat_le_Rbar H hsZ hs1 hks hsL
  have hXq := D.isQuasisimple_Xhat
  have hXN := D.not_Xhat_le_Nbar H hsZ hs1 hks hsL
  have hRL : Rbar S g D.t ≠ S.Lbar g := fun h =>
    not_isSolvable_of_isQuasisimple hXq (SwapData.isSolvable_of_le_Lbar H (h ▸ hXR))
  have hXsubR : IsSubnormal D.Xhat (Rbar S g D.t) :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le (D.isSubnormal_Xhat H) hXR
      (le_inf Rbar_le_Mbar (Rbar_le_centralizer haQ))
  obtain ⟨⟨hfac, -⟩, -, h3⟩ := Q.quasisimple hNo htL ht1 hRL
    (isSubnormal_imgR haQ hXR hXsubR) (isQuasisimple_imgR haQ hXR hXq hXN)
  have hBXR := (hBX.subgroupOf hXR).map (resV haQ D.t)
  obtain ⟨hVQ, -⟩ := h3 ⟨imgR haQ D.t B, hBXR.le, hBXR.isPGroup, hBXR.not_dvd, by
    rintro _ ⟨b1, hb1, rfl⟩ _ ⟨b2, hb2, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (S4.Lbar_comm S haQ (hBL (mem_subgroupOf.mp hb1))
      (hBL (mem_subgroupOf.mp hb2)))⟩
  refine ⟨hXR, hXN, hRL, hXsubR, hfac, hVQ, fun τ hτ => ?_⟩
  refine eq_one_or_eq_of_factor H C htL ht1 hVQ hfac hτ.1 fun y hy => ?_
  exact commute_of_mem_Lbar_inf_Nbar H htL hXR hXq hXN
    (fun s' hs' y' hy' => D.conj_mem_Xhat H hsZ hs1 hks hsL hs' hy')
    (fun z hz hc k hk => D.eq_one_of_mem_center_Xhat hz hc hk) hτ.1 hτ.2 hy

theorem swap_central_inf (D : SwapData S g) (H : Hyp4 S g) (F : SwapFacts D H) :
    ∀ c ∈ D.Xhat ⊓ Nbar S g D.t, ∀ y ∈ D.Xhat, c * y = y * c := by
  have hnorm : ∀ a ∈ D.Xhat, ∀ n ∈ D.Xhat ⊓ Nbar S g D.t,
      a * n * a⁻¹ ∈ D.Xhat ⊓ Nbar S g D.t := fun a ha n hn =>
    ⟨D.Xhat.mul_mem (D.Xhat.mul_mem ha hn.1) (D.Xhat.inv_mem ha),
      conj_mem_Nbar_w4 H.conj_mem (F.XR ha) hn.2⟩
  rcases commute_or_eq_of_normalized D.isQuasisimple_Xhat inf_le_left hnorm with hcen | heq
  · exact hcen
  · exact absurd (heq ▸ inf_le_right : D.Xhat ≤ Nbar S g D.t) F.XN

theorem swap_Rbar_le_normalizer (D : SwapData S g) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4) (F : SwapFacts D H) :
    Rbar S g D.t ≤ normalizer (D.Xhat : Set S.O) := by
  have haQ := H.conj_mem
  have hcomp : IsComponentOf D.Xhat (Rbar S g D.t) := ⟨F.XR, F.Xsub, D.isQuasisimple_Xhat⟩
  intro r hr
  rw [mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set Y := D.Xhat.map (MulAut.conj r).toMonoidHom with hY
  have hYc : IsComponentOf Y (Rbar S g D.t) := isComponentOf_map_conj hcomp hr
  have hYN : ¬ Y ≤ Nbar S g D.t := by
    intro hle
    apply F.XN
    intro x hx
    have h1 : r * x * r⁻¹ ∈ Nbar S g D.t := hle ⟨x, hx, rfl⟩
    have h2 := conj_mem_Nbar_w4 haQ ((Rbar S g D.t).inv_mem hr) h1
    have e : r⁻¹ * (r * x * r⁻¹) * r⁻¹⁻¹ = x := by group
    rwa [e] at h2
  have hqX := isQuasisimple_imgR haQ F.XR D.isQuasisimple_Xhat F.XN
  have hqY := isQuasisimple_imgR haQ hYc.1 hYc.2.2 hYN
  obtain ⟨hKX, -⟩ := quasisimple_w4 Q hNo hw D.mem_Lbar D.t_ne_one F.RL F.VQ
    (isSubnormal_imgR haQ F.XR F.Xsub) hqX
  obtain ⟨hKY, -⟩ := quasisimple_w4 Q hNo hw D.mem_Lbar D.t_ne_one F.RL F.VQ
    (isSubnormal_imgR haQ hYc.1 hYc.2.1) hqY
  apply not_isSolvable_of_isQuasisimple hqY
  refine Group.isSolvable_of_comm fun e₁ e₂ => Subtype.ext ?_
  obtain ⟨y₁, hy₁, he₁⟩ := mem_imgR.mp e₁.2
  have he₂ : (e₂ : Vt S g D.t ≃ₗ[ZMod 2] Vt S g D.t) ∈ imgR haQ D.t D.Xhat := by
    rw [hKX, ← hKY]
    exact e₂.2
  obtain ⟨y₂, hy₂, he₂'⟩ := mem_imgR.mp he₂
  change (e₁ : Vt S g D.t ≃ₗ[ZMod 2] Vt S g D.t) * e₂ = e₂ * e₁
  rw [← he₁, ← he₂', ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mul_comm_of_isComponentOf_ne hYc hcomp hne hy₁ hy₂)

theorem swap_comm_Nbar (D : SwapData S g) (H : Hyp4 S g) (F : SwapFacts D H)
    (h2 : IsPGroup 2 (Nbar S g D.t)) (hRn : Rbar S g D.t ≤ normalizer (D.Xhat : Set S.O)) :
    ∀ n ∈ Nbar S g D.t, ∀ x ∈ D.Xhat, n * x = x * n := by
  have haQ := H.conj_mem
  intro n hn y hy
  have hnX : n * y * n⁻¹ ∈ D.Xhat := (mem_normalizer_iff.mp (hRn (Nbar_le_Rbar hn)) y).mp hy
  have hyN : y * n⁻¹ * y⁻¹ ∈ Nbar S g D.t := conj_mem_Nbar_w4 haQ (F.XR hy) (inv_mem hn)
  obtain ⟨c, hc⟩ : ∃ c, c = n * y * n⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hcX : c ∈ D.Xhat := hc ▸ D.Xhat.mul_mem hnX (D.Xhat.inv_mem hy)
  have hcN : c ∈ Nbar S g D.t := by
    have := mul_mem hn hyN
    rw [hc]
    simpa [mul_assoc] using this
  obtain ⟨j, hj⟩ := h2 ⟨c, hcN⟩
  have hj' : c ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have hc1 : c = 1 := D.eq_one_of_mem_center_Xhat hcX (swap_central_inf D H F c ⟨hcX, hcN⟩) hj'
  calc n * y = c * (y * n) := by rw [hc]; group
    _ = y * n := by rw [hc1, one_mul]

theorem swap_structure_w4 (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4) (D : SwapData S g) :
    ¬ V S g D.t ≤ S.Qa g ∧ Nat.card (LmodN S g D.t) = 4 ∧
      Nat.card (S.Lbar g ⊓ Nbar S g D.t : Subgroup S.O) = 2 ∧
      imgR H.conj_mem D.t D.Xhat = RmodN S g D.t ∧ D.Xhat ⊓ Nbar S g D.t = ⊥ ∧
      Nbar S g D.t = zpowers D.t ∧ Rbar S g D.t = zpowers D.t ⊔ D.Xhat := by
  have haQ := H.conj_mem
  have htL := D.mem_Lbar
  have ht1 := D.t_ne_one
  have F := swap_facts D H hNo C Q
  have hXq := D.isQuasisimple_Xhat
  obtain ⟨hKR, h4⟩ := quasisimple_w4 Q hNo hw htL ht1 F.RL F.VQ
    (isSubnormal_imgR haQ F.XR F.Xsub) (isQuasisimple_imgR haQ F.XR hXq F.XN)
  have hcard8 : Nat.card (S.Lbar g) = 8 := by
    rw [C.card_Lbar, hw]
    norm_num
  have hLN2 : Nat.card (S.Lbar g ⊓ Nbar S g D.t : Subgroup S.O) = 2 := by
    have h := card_Lbar_eq haQ htL (t := D.t)
    rw [hcard8, h4] at h
    omega
  obtain ⟨h2, -, hsup⟩ := timmesfeld_4_7_a_of_not_a6 hCE H hNo C htL ht1 F.RL
    (fun hVQ => W4ThmA.not_pgl25Case hw H C htL ht1 hVQ)
    (fun hVQ => W4ThmA.not_a6Case hw H C htL ht1 hVQ)
  have hRn := swap_Rbar_le_normalizer D H hNo C Q hw F
  have hNL : Nbar S g D.t ≤ S.Lbar g :=
    Nbar_le_Lbar_of_factor H hNo C htL ht1 F.RL F.fac (swap_comm_Nbar D H F h2 hRn) hsup
  have hNzp : Nbar S g D.t = zpowers D.t := by
    refine le_antisymm (fun x hx => ?_) (zpowers_le.mpr (mem_Nbar_self H htL))
    rcases F.LN x ⟨hNL hx, hx⟩ with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  have hXbot : D.Xhat ⊓ Nbar S g D.t = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [mem_bot]
    obtain ⟨j, hj⟩ := h2 ⟨c, hc.2⟩
    exact D.eq_one_of_mem_center_Xhat hc.1 (swap_central_inf D H F c hc) (k := j)
      (by simpa using congrArg Subtype.val hj)
  refine ⟨F.VQ, h4, hLN2, hKR, hXbot, hNzp, le_antisymm (fun r hr => ?_) ?_⟩
  · have hres : resV haQ D.t ⟨r, hr⟩ ∈ imgR haQ D.t D.Xhat := by
      rw [hKR, ← range_resV haQ D.t]
      exact ⟨⟨r, hr⟩, rfl⟩
    obtain ⟨y, hyX, hy⟩ := mem_imgR.mp hres
    have hN : ((y⁻¹ * ⟨r, hr⟩ : Rbar S g D.t) : S.O) ∈ Nbar S g D.t := by
      rw [← resV_eq_one_iff haQ, map_mul, map_inv, hy, inv_mul_cancel]
    rw [hNzp] at hN
    have e : r = (y : S.O) * ((y⁻¹ * ⟨r, hr⟩ : Rbar S g D.t) : S.O) := by simp
    rw [e]
    exact mul_mem (mem_sup_right hyX) (mem_sup_left hN)
  · exact sup_le (zpowers_le.mpr (Lbar_le_Rbar htL htL)) F.XR

end CFSG.GF2Type.Smith1979.W4Five
