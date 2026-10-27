module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3GenA
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3Lift2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26L2Z
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocGlue
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22RestAut
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Gen

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj DEdgeless)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
open CFSG.ClassicalInvolution.Q3.TA3 (SmallL3Ne3 SmallU3Ne3)
open scoped commutatorElement

section Cert


variable {r n : ℕ}

theorem z_mem_L_of_exit (hr : 4 ≤ r) {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    [L.Normal] (hLC : Subgroup.centralizer (L : Set Q) = Subgroup.center Q)
    (hZL : Subgroup.center ↥L = ⊥)
    (hTC : Subgroup.centralizer ((socleOf L : Subgroup (Q ⧸ Subgroup.center Q)) :
      Set (Q ⧸ Subgroup.center Q)) = ⊥)
    (hcomm : SocleComm2 ↥(socleOf L)) {R : Subgroup Q} {S : Sylow 2 R} {z : Q}
    (hd : TightDatum R S z) (hc : TightClsR r Q R S z) : z ∈ L := by
  classical
  obtain ⟨x, b, hxS, hbS, hxo, hbx, hbb⟩ := exists_quat_full_of_datum (by omega : 3 ≤ r) hc
  have hxR : x ∈ R := mem_sylowSet_le S hxS
  have hzx : x ^ 2 ^ (r - 2) = z := by
    apply hd.eq_of_orderOf_eq_two (Subgroup.pow_mem _ hxR _)
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
      (by rw [hxo]; exact pow_dvd_pow 2 (by omega)), hxo,
      show 2 ^ (r - 1) = 2 * 2 ^ (r - 2) by rw [← pow_succ']; congr 1; omega]
    exact Nat.mul_div_cancel 2 (by positivity)
  have hP : IsPGroup 2 ((sylowSet S).map (QuotientGroup.mk' (Subgroup.center Q))) :=
    (S.isPGroup'.map _).map _
  have hle := hcomm (Q ⧸ Subgroup.center Q) (socleOf L) inferInstance ⟨MulEquiv.refl _⟩ hTC _ hP
  have hx2 : x ^ 2 = ⁅b, x⁻¹⁆ := by
    have h0 : b * x⁻¹ * b⁻¹ = x := by
      rw [show b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ by group, hbx, inv_inv]
    rw [commutatorElement_def, h0, inv_inv, pow_two]
  have hmem : (QuotientGroup.mk (x ^ 2) : Q ⧸ Subgroup.center Q) ∈ socleOf L := by
    apply hle
    rw [hx2]
    have h1 : (QuotientGroup.mk b : Q ⧸ Subgroup.center Q) ∈
        (sylowSet S).map (QuotientGroup.mk' (Subgroup.center Q)) := ⟨b, hbS, rfl⟩
    have h2 : (QuotientGroup.mk x⁻¹ : Q ⧸ Subgroup.center Q) ∈
        (sylowSet S).map (QuotientGroup.mk' (Subgroup.center Q)) :=
      ⟨x⁻¹, (sylowSet S).inv_mem hxS, rfl⟩
    have h3 := Subgroup.commutator_mem_commutator h1 h2
    have h4 : (QuotientGroup.mk ⁅b, x⁻¹⁆ : Q ⧸ Subgroup.center Q) =
        ⁅(QuotientGroup.mk b : Q ⧸ Subgroup.center Q), (QuotientGroup.mk x⁻¹ : Q ⧸ Subgroup.center Q)⁆ :=
      map_commutatorElement (QuotientGroup.mk' (Subgroup.center Q)) b x⁻¹
    rw [h4]
    exact h3
  obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp hmem
  have hlc : l⁻¹ * x ^ 2 ∈ Subgroup.center Q := QuotientGroup.eq.mp hlx
  set c := l⁻¹ * x ^ 2 with hcdef
  have hxlc : x ^ 2 = l * c := by rw [hcdef]; group
  have hcc : ∀ g : Q, g * c = c * g := fun g => Subgroup.mem_center_iff.mp hlc g
  have hbl : b * l * b⁻¹ ∈ L := Subgroup.Normal.conj_mem ‹L.Normal› l hl b
  have hb2 : b * x ^ 2 * b⁻¹ = (x ^ 2)⁻¹ := by rw [← inv_pow, ← hbx, conj_pow]
  have e1 : (b * l * b⁻¹) * c = (x ^ 2)⁻¹ := by
    have hbc : b * c * b⁻¹ = c := by rw [hcc b, mul_inv_cancel_right]
    calc (b * l * b⁻¹) * c = b * l * b⁻¹ * (b * c * b⁻¹) := by rw [hbc]
      _ = b * (l * c) * b⁻¹ := by group
      _ = b * x ^ 2 * b⁻¹ := by rw [hxlc]
      _ = (x ^ 2)⁻¹ := hb2
  have hm : (b * l * b⁻¹) * l * (c * c) = 1 := by
    calc (b * l * b⁻¹) * l * (c * c) = (b * l * b⁻¹) * (l * c) * c := by group
      _ = (b * l * b⁻¹) * x ^ 2 * c := by rw [← hxlc]
      _ = (b * l * b⁻¹) * (x ^ 2 * c) := by group
      _ = (b * l * b⁻¹) * (c * x ^ 2) := by rw [hcc (x ^ 2)]
      _ = (b * l * b⁻¹ * c) * x ^ 2 := by group
      _ = 1 := by rw [e1, inv_mul_cancel]
  have hmL : (b * l * b⁻¹) * l ∈ L := L.mul_mem hbl hl
  have hmZ : (b * l * b⁻¹) * l ∈ Subgroup.center Q := by
    have : (b * l * b⁻¹) * l = (c * c)⁻¹ := eq_inv_of_mul_eq_one_left hm
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hlc hlc)
  have hm1 : (b * l * b⁻¹) * l = 1 := by
    have := (mem_center_subtype_iff hLC ⟨_, hmL⟩).mpr hmZ
    rw [hZL, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hc2 : c * c = 1 := by
    rw [hm1, one_mul] at hm
    exact hm
  have hk : 2 ^ (r - 2) = 2 * 2 ^ (r - 3) := by
    rw [← pow_succ']; congr 1; omega
  have hk' : 2 ^ (r - 3) = 2 * 2 ^ (r - 4) := by
    rw [← pow_succ']; congr 1; omega
  have hz : z = l ^ 2 ^ (r - 3) := by
    have hcl : Commute l c := hcc l
    have h1 : c ^ 2 ^ (r - 3) = 1 := by
      rw [hk', pow_mul, sq, hc2, one_pow]
    calc z = x ^ 2 ^ (r - 2) := hzx.symm
      _ = (x ^ 2) ^ 2 ^ (r - 3) := by rw [hk, pow_mul]
      _ = (l * c) ^ 2 ^ (r - 3) := by rw [hxlc]
      _ = l ^ 2 ^ (r - 3) * c ^ 2 ^ (r - 3) := hcl.mul_pow _
      _ = l ^ 2 ^ (r - 3) := by rw [h1, mul_one]
  rw [hz]
  exact L.pow_mem hl _

theorem fix_of_mod_center {Q : Type} [Group Q] {L : Subgroup Q} (hL : ⁅L, L⁆ = L)
    (γ : Q ≃* Q) (h : ∀ y ∈ L, (y : Q)⁻¹ * γ y ∈ Subgroup.center Q) :
    ∀ y ∈ L, γ y = y := by
  let δ : ↥L →* ↥(Subgroup.center Q) :=
    { toFun := fun y => ⟨(y : Q)⁻¹ * γ y, h y y.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro y y'
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (h y y.2)
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        calc (y' : Q)⁻¹ * (y : Q)⁻¹ * (γ y * γ y')
            = (y' : Q)⁻¹ * ((y : Q)⁻¹ * γ y) * γ y' := by group
          _ = ((y : Q)⁻¹ * γ y) * (y' : Q)⁻¹ * γ y' := by rw [← hc (y' : Q)⁻¹]
          _ = ((y : Q)⁻¹ * γ y) * ((y' : Q)⁻¹ * γ y') := by group }
  have hle : ⁅L, L⁆ ≤ (δ.ker).map L.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : ↥L), (⟨b, hb⟩ : ↥L)⁆, ?_, rfl⟩
    show ⁅(⟨a, ha⟩ : ↥L), (⟨b, hb⟩ : ↥L)⁆ ∈ δ.ker
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subtype.ext (Subgroup.mem_center_iff.mp (δ ⟨b, hb⟩).2 (δ ⟨a, ha⟩)))
  intro y hy
  rw [hL] at hle
  obtain ⟨y', hy', hyy⟩ := hle hy
  have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy')
  have h2 : (y' : Q)⁻¹ * γ y' = 1 := h1
  have h3 : (y' : Q) = y := hyy
  rw [h3] at h2
  have := mul_eq_one_iff_eq_inv.mp h2
  exact (inv_injective this).symm

theorem commutator_self_eq_of_perfect {Q : Type} [Group Q] {L : Subgroup Q}
    (hL : Group.IsPerfect ↥L) : ⁅L, L⁆ = L := by
  have h1 : (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆) = ⊤ := by
    have := hL.commutator_eq_top
    rwa [_root_.commutator_def] at this
  have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥L) (⊤ : Subgroup ↥L) L.subtype
  rw [h1] at h2
  have h3 : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h3] at h2
  exact h2.symm

@[expose] def ExitLU {Q : Type} [Group Q] [Finite Q] (R : Subgroup Q) (S : Sylow 2 ↥R) (z : Q) :
    Prop :=
  ∃ L₀ : Subgroup Q, L₀.Normal ∧ IsSimpleGroup ↥L₀ ∧
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
      (CFSG.Blueprint.LieModel ↥L₀ .PSL 3 p f ∨ CFSG.Blueprint.LieModel ↥L₀ .PSU 3 p f)) ∧
    z ∈ L₀ ∧
    (∀ β : MulAut Q, β * β = 1 → (∀ s ∈ sylowSet S, β s = s) →
      (∀ y ∈ L₀, β y = y) ∨ (∀ y ∈ L₀, β y = z * y * z⁻¹)) ∧
    (∀ s : Q, z * s = s * z → s ≠ z → (∃ g : Q, s = g * z * g⁻¹) →
      Subgroup.centralizer ({z} : Set Q) ⊔ Subgroup.centralizer ({s} : Set Q) = ⊤)

theorem exitLU_of_ident (hr : 4 ≤ r) {Q : Type} [Group Q] [Finite Q] {R : Subgroup Q}
    {S : Sylow 2 ↥R} {z : Q} (hd : TightDatum R S z) (hc : TightClsR r Q R S z)
    {L : Subgroup Q} [L.Normal] (hLq : CFSG.IsQuasisimple ↥L)
    (hLC : Subgroup.centralizer (L : Set Q) = Subgroup.center Q)
    (hnt : ∀ y : Q, ∀ m ∈ Subgroup.center Q, y * z * y⁻¹ = z * m → m = 1)
    {R' : Subgroup (Q ⧸ Subgroup.center Q)} {S' : Sylow 2 ↥R'} {z' : Q ⧸ Subgroup.center Q}
    (hd' : TightDatum R' S' z') (hc' : TightClsR r (Q ⧸ Subgroup.center Q) R' S' z')
    (hz' : z' = QuotientGroup.mk z)
    (hTC : Subgroup.centralizer ((socleOf L : Subgroup (Q ⧸ Subgroup.center Q)) :
      Set (Q ⧸ Subgroup.center Q)) = ⊥)
    (hLU : SmallL3Ne3 ↥(socleOf L) ∨ SmallU3Ne3 ↥(socleOf L))
    (hdich : ∀ φ : Q ≃* Q, (∀ x, φ (φ x) = x) → (∀ s ∈ sylowSet S, φ s = s) →
      (∀ y, Perp22Rest.quotCenterAut φ y = y) ∨
        (∀ y, Perp22Rest.quotCenterAut φ y = QuotientGroup.mk z * y * (QuotientGroup.mk z)⁻¹)) :
    ExitLU R S z := by
  classical
  obtain ⟨e⟩ := nonempty_socle_equiv hLC
  have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥L) := by
    intro g
    obtain ⟨k, hk⟩ := (Perp22Rest.isPGroup_center_R hc) ⟨((g : ↥L) : Q), (mem_center_subtype_iff hLC g).mp g.2⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun w => ((w : ↥(Subgroup.center Q)) : Q)) hk
    simpa using this
  have hmodel : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
      (CFSG.Blueprint.LieModel ↥(socleOf L) .PSL 3 p f ∨
        CFSG.Blueprint.LieModel ↥(socleOf L) .PSU 3 p f)) ∧
      Odd (Nat.card (griessHopfMultiplier ↥(socleOf L))) := by
    rcases hLU with ⟨p, f, hp, hp2, hf, hq3, hm⟩ | ⟨p, f, hp, hp2, hf, hq3, hm⟩
    · have hlm : CFSG.Blueprint.LieModel ↥(socleOf L) .PSL 3 p f := Or.inl ⟨by decide, hm⟩
      exact ⟨⟨p, f, hp, hp2, Or.inl hlm⟩, E3S3M.odd_natCard_hopf_psl3 hlm hp2⟩
    · have hlm : CFSG.Blueprint.LieModel ↥(socleOf L) .PSU 3 p f := Or.inl ⟨by decide, hm⟩
      exact ⟨⟨p, f, hp, hp2, Or.inr hlm⟩, E3S3M.odd_natCard_hopf_psu3 hlm hp2⟩
  have hZL : Subgroup.center ↥L = ⊥ := E3S3M.center_eq_bot_of_odd hLq e.symm hZ2 hmodel.2
  have eL : ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
    (QuotientGroup.quotientBot (G := ↥L)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZL.symm)
  have hsimp : IsSimpleGroup ↥L := by
    haveI := hLq.2.1
    exact eL.isSimpleGroup
  have hLperf : ⁅L, L⁆ = L := commutator_self_eq_of_perfect hLq.1
  have hcomm : SocleComm2 ↥(socleOf L) := by
    rcases hLU with h3 | h3
    · exact (socleFactsR_l3 h3).comm2
    · exact (socleFactsR_u3 h3).comm2
  refine ⟨L, inferInstance, hsimp, ?_, z_mem_L_of_exit hr hLC hZL hTC hcomm hd hc, ?_, ?_⟩
  · obtain ⟨⟨p, f, hp, hp2, hlm⟩, -⟩ := hmodel
    refine ⟨p, f, hp, hp2, ?_⟩
    rcases hlm with hlm | hlm
    · exact Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv (e.trans eL.symm) hlm)
    · exact Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv (e.trans eL.symm) hlm)
  ·
    intro β hβ hβS
    have hinv : ∀ x, β (β x) = x := fun x => by
      have h := congrArg (fun γ : MulAut Q => γ x) hβ
      simpa [MulAut.mul_apply, MulAut.one_apply] using h
    rcases hdich β hinv hβS with h1 | h2
    · left
      refine fix_of_mod_center hLperf β (fun y _ => ?_)
      have := h1 (QuotientGroup.mk y)
      rw [Perp22Rest.quotCenterAut_mk] at this
      exact QuotientGroup.eq.mp this.symm
    · right
      let γ : Q ≃* Q := β.trans (MulAut.conj z⁻¹)
      have hγ : ∀ y ∈ L, γ y = y := by
        refine fix_of_mod_center hLperf γ (fun y _ => ?_)
        have h3 := h2 (QuotientGroup.mk y)
        rw [Perp22Rest.quotCenterAut_mk] at h3
        have h4 : (z * y * z⁻¹)⁻¹ * β y ∈ Subgroup.center Q := by
          apply QuotientGroup.eq.mp
          rw [h3]
          simp
        have h5 : (y : Q)⁻¹ * γ y = z⁻¹ * ((z * y * z⁻¹)⁻¹ * β y) * z := by
          simp only [γ, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
          group
        rw [h5]
        have h7 := Subgroup.Normal.conj_mem (Subgroup.center Q).normal_of_characteristic _ h4 z⁻¹
        rwa [inv_inv] at h7
      intro y hy
      have h6 := hγ y hy
      simp only [γ, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv] at h6
      calc β y = z * (z⁻¹ * β y * z) * z⁻¹ := by group
        _ = z * y * z⁻¹ := by rw [h6]
  ·
    intro s hcomm_s hsz hconj
    obtain ⟨g, hg⟩ := hconj
    apply sup_centralizer_of_quot hnt ⟨g, hg⟩
    have hs_ne : (QuotientGroup.mk s : Q ⧸ Subgroup.center Q) ≠ QuotientGroup.mk z := by
      intro h
      apply hsz
      rw [QuotientGroup.eq] at h
      have hm' : z⁻¹ * s ∈ Subgroup.center Q := by
        have := (Subgroup.center Q).inv_mem h
        simpa [mul_inv_rev] using this
      obtain ⟨m, hm, hsm⟩ : ∃ m ∈ Subgroup.center Q, s = z * m :=
        ⟨z⁻¹ * s, hm', by group⟩
      have := hnt g m hm (by rw [← hg, hsm])
      rw [hsm, this, mul_one]
    have hAz : orderOf (QuotientGroup.mk z : Q ⧸ Subgroup.center Q) = 2 := hz' ▸ hd'.order
    have hcommA : (QuotientGroup.mk z : Q ⧸ Subgroup.center Q) * QuotientGroup.mk s =
        QuotientGroup.mk s * QuotientGroup.mk z := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm_s]
    have hconjA : ∃ h : Q ⧸ Subgroup.center Q,
        (QuotientGroup.mk s : Q ⧸ Subgroup.center Q) = h * QuotientGroup.mk z * h⁻¹ :=
      ⟨QuotientGroup.mk g, by rw [hg]; simp⟩
    rcases hLU with hL3' | hU3'
    · have hzT : (QuotientGroup.mk z : Q ⧸ Subgroup.center Q) ∈ socleOf L :=
        hz' ▸ (z_mem_of_comm2 hr hTC (socleFactsR_l3 hL3').comm2 hd' hc').1
      exact gen_l3_of_normal (socleOf L) (by
        obtain ⟨p, f, hp, hp2, hf, -, hm⟩ := hL3'
        exact ⟨p, f, hp, hp2, hf, hm⟩) hzT hAz hcommA hs_ne hconjA
    · have hzT : (QuotientGroup.mk z : Q ⧸ Subgroup.center Q) ∈ socleOf L :=
        hz' ▸ (z_mem_of_comm2 hr hTC (socleFactsR_u3 hU3').comm2 hd' hc').1
      exact gen_u3_of_normal (socleOf L) (by
        obtain ⟨p, f, hp, hp2, hf, -, hm⟩ := hU3'
        exact ⟨p, f, hp, hp2, hf, hm⟩) hzT hAz hcommA hs_ne hconjA


end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
