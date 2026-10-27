module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Glue2
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Out
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.M24Cat
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Glue1

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44

open Subgroup MulAction CFSG.Blueprint

set_option linter.unusedSectionVars false


variable {G : Type} [Group G]

theorem normClass_eq_image {E : Subgroup G} (x : ↥E) :
    normClass E (x : G) = Subtype.val '' orbit (XE E) x := by
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨actN E ⟨n, hn⟩ x, ⟨⟨actN E ⟨n, hn⟩, ⟨⟨n, hn⟩, rfl⟩⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨⟨m, ⟨n, rfl⟩⟩, rfl⟩, rfl⟩
    exact ⟨n, n.2, rfl⟩

theorem m24Out_of_frame (hMain : CocodeMainStmt) [Finite G] {L : Subgroup G} (h : StdHyp G L)
    {t : G} {E : Subgroup G} (D : Facts G t L E)
    (hCE : centralizer (E : Set G) = E)
    (hLH : L.relIndex (centralizer ({t} : Set G)) = 2)
    (hmove : ∃ n ∈ normalizer (E : Set G), n⁻¹ * t * n ≠ t)
    (hout : ∃ n ∈ normalizer (E : Set G), n ∈ centralizer ({t} : Set G) ∧ n ∉ L)
    {O : Fin 5 → Set G} (F : FrameModelG G L E t O) : M24Out G E t := by
  classical
  have hcomm := D.E_comm
  let _ : CommGroup ↥E := commE hcomm
  have hsq : ∀ v : ↥E, v ^ 2 = 1 := fun v => Subtype.ext (D.E_sq v.1 v.2)
  have hV : Nat.card ↥E = 2 ^ 11 := D.card_E
  have hOE := frame_subset F
  have hOD := orbitData_of_frame hcomm D.le_centralizer F
  have hEL : E ≤ L := D.E_le
  have hEN : E ≤ normalizer (E : Set G) := le_normalizer
  have hEH : E ≤ centralizer ({t} : Set G) := hEL.trans D.le_centralizer
  have hpos : 0 < 2 ^ 11 := by norm_num
  have hM : Nat.card (MXE E L) = 443520 := by
    have h1 := card_image_mul hCE (S := normalizer (E : Set G) ⊓ L) inf_le_left (le_inf hEN hEL)
    rw [F.card_N, hV] at h1
    have h2 : Nat.card (MXE E L) * 2 ^ 11 = 443520 * 2 ^ 11 := by
      rw [mul_comm 443520]
      exact h1
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hYeq : XE E ⊓ stabilizer (MulAut ↥E) (⟨t, F.t_mem⟩ : ↥E) =
      ((normalizer (E : Set G) ⊓ centralizer ({t} : Set G)).subgroupOf
        (normalizer (E : Set G))).map (actN E) := by
    ext x
    constructor
    · rintro ⟨⟨n, rfl⟩, hx⟩
      refine Subgroup.mem_map.2 ⟨n, ?_, rfl⟩
      have hx' : (actN E n) ⟨t, F.t_mem⟩ = ⟨t, F.t_mem⟩ := MulAction.mem_stabilizer_iff.1 hx
      have hxc : (n : G) * t * (n : G)⁻¹ = t := congrArg Subtype.val hx'
      refine ⟨n.2, ?_⟩
      exact mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hxc)
    · intro hx
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hx
      refine ⟨⟨n, rfl⟩, MulAction.mem_stabilizer_iff.2 ?_⟩
      apply Subtype.ext
      show (n : G) * t * (n : G)⁻¹ = t
      rw [mul_inv_eq_iff_eq_mul]
      exact mem_centralizer_singleton_iff.1 hn.2
  have hY : Nat.card ↥(XE E ⊓ stabilizer (MulAut ↥E) (⟨t, F.t_mem⟩ : ↥E)) = 887040 := by
    rw [hYeq]
    have h1 := card_image_mul hCE (S := normalizer (E : Set G) ⊓ centralizer ({t} : Set G))
      inf_le_left (le_inf hEN hEH)
    rw [card_normalizer_inf_centralizer D hLH, F.card_N, hV] at h1
    have h2 : Nat.card ↥(((normalizer (E : Set G) ⊓ centralizer ({t} : Set G)).subgroupOf
        (normalizer (E : Set G))).map (actN E)) * 2 ^ 11 = 887040 * 2 ^ 11 := by
      rw [h1]
      norm_num
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hMX : MXE E L ≤ XE E := MXE_le_XE
  have hmove' : ∃ x ∈ XE E, x ⟨t, F.t_mem⟩ ≠ ⟨t, F.t_mem⟩ := by
    obtain ⟨n, hn, hne⟩ := hmove
    refine ⟨actN E ⟨n⁻¹, inv_mem hn⟩, ⟨_, rfl⟩, fun h => hne ?_⟩
    have h1 : n⁻¹ * t * n⁻¹⁻¹ = t := congrArg Subtype.val h
    simpa using h1
  have hν : ∃ ν ∈ XE E, ν ⟨t, F.t_mem⟩ = ⟨t, F.t_mem⟩ ∧
      (fun v => ν v) '' {v : ↥E | (v : G) ∈ O 0} = {v : ↥E | (v : G) ∈ O 1} := by
    obtain ⟨ν, hνN, hνH, hνL⟩ := hout
    have hswap := exists_swap F D hCE hνN hνH hνL
    refine ⟨actN E ⟨ν, hνN⟩, ⟨_, rfl⟩, ?_, ?_⟩
    · apply Subtype.ext
      show ν * t * ν⁻¹ = t
      rw [mul_inv_eq_iff_eq_mul]
      exact mem_centralizer_singleton_iff.1 hνH
    · ext v
      constructor
      · rintro ⟨u, hu, rfl⟩
        have h1 : ν * (u : G) * ν⁻¹ ∈ (fun e => ν * e * ν⁻¹) '' O 0 := ⟨u, hu, rfl⟩
        rw [hswap] at h1
        exact h1
      · intro hv
        have hv' : (v : G) ∈ (fun e => ν * e * ν⁻¹) '' O 0 := by
          rw [hswap]
          exact hv
        obtain ⟨w, hw, hwv⟩ := hv'
        exact ⟨⟨w, hOE 0 hw⟩, hw, Subtype.ext hwv⟩
  obtain ⟨hsimp, hXc, hΩ, y, hy1, hyΩ, hyc, hyall⟩ :=
    hMain hV hsq (XE E) (MXE E L) ⟨t, F.t_mem⟩ (fun i => {v : ↥E | (v : G) ∈ O i}) hMX hOD hM
      hY hmove' hν
  have hker := ker_actN_eq hCE
  let e1 : ↥(normalizer (E : Set G)) ⧸ E.subgroupOf (normalizer (E : Set G)) ≃* XE E :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange (actN E))
  have hsimpQ : IsSimpleGroup (↥(normalizer (E : Set G)) ⧸ E.subgroupOf (normalizer (E : Set G))) :=
    e1.isSimpleGroup
  have hordQ : Nat.card (↥(normalizer (E : Set G)) ⧸ E.subgroupOf (normalizer (E : Set G))) =
      244823040 := (Nat.card_congr e1.toEquiv).trans hXc
  have hNtop : normalizer (E : Set G) ≠ ⊤ := by
    intro htop
    have hnorm : E.Normal := normalizer_eq_top_iff.1 htop
    have := h.simple
    rcases Subgroup.Normal.eq_bot_or_eq_top E with hb | ht
    · have : Nat.card E = 1 := by rw [hb]; exact Subgroup.card_bot
      rw [hV] at this
      norm_num at this
    · obtain ⟨a, b, hab⟩ := h.nonabelian
      exact hab (D.E_comm a (by rw [ht]; trivial) b (by rw [ht]; trivial))
  have hM24 := isSporadic_M24_of_kProper_section h.kProper hNtop hEN hsimpQ hordQ
  refine ⟨hV, D.E_sq, hCE, hM24, F.t_mem, F.t_ne_one, ?_, ?_⟩
  · have h1 := normClass_eq_image (E := E) ⟨t, F.t_mem⟩
    rw [h1, Set.ncard_image_of_injective _ Subtype.val_injective]
    exact hΩ
  · refine ⟨(y : G), y.2, fun h1 => hy1 (Subtype.ext h1), ?_, ?_, ?_⟩
    · rw [normClass_eq_image (E := E) ⟨t, F.t_mem⟩]
      rintro ⟨v, hv, hvy⟩
      apply hyΩ
      rwa [Subtype.val_injective hvy] at hv
    · rw [normClass_eq_image y, Set.ncard_image_of_injective _ Subtype.val_injective]
      exact hyc
    · intro w hwE hw1 hwn
      obtain ⟨w', rfl⟩ : ∃ w' : ↥E, (w' : G) = w := ⟨⟨w, hwE⟩, rfl⟩
      rw [normClass_eq_image y]
      refine ⟨w', hyall w' (fun h1 => hw1 (by rw [h1]; rfl)) ?_, rfl⟩
      intro hmem
      apply hwn
      rw [normClass_eq_image (E := E) ⟨t, F.t_mem⟩]
      exact ⟨w', hmem, rfl⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44
