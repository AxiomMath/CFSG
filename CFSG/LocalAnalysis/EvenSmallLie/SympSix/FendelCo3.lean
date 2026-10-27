module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.FendelData
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.FendelM12
public import CFSG.Sporadic.Schreier.Co3First

public noncomputable section

namespace CFSG.EvenSmallLie.SympSix

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native
  CFSG.GH74.M12 CFSG.GH74.M12.Hyp CFSG.Blueprint

theorem fendelMElts_spec
    {x : Array ℕ} (hx : x ∈ fendelMElts) :
    Rep 276 x (permOfArr 276 x) ∧ Rep 276 (invCand 276 x) (permOfArr 276 x)⁻¹ ∧
      permOfArr 276 x ∈ co3M := by
  obtain ⟨h1, h2⟩ := fendel_check_elts x hx
  have hr := rep_permOfArr h1
  exact ⟨hr.1, hr.2, mem_co3M_of_sift hr.1 h2⟩

@[expose] def fendelElt
    (x : Array ℕ) (hx : x ∈ fendelMElts) : co3M :=
  ⟨permOfArr 276 x, (fendelMElts_spec hx).2.2⟩

theorem rep_fendelElt
    {x : Array ℕ} (hx : x ∈ fendelMElts) :
    Rep 276 x ((fendelElt x hx : co3M) : Equiv.Perm (Fin 276)) :=
  (fendelMElts_spec hx).1

theorem rep_fendelElt_inv
    {x : Array ℕ} (hx : x ∈ fendelMElts) :
    Rep 276 (invCand 276 x) (((fendelElt x hx)⁻¹ : co3M) : Equiv.Perm (Fin 276)) := by
  rw [Subgroup.coe_inv]
  exact (fendelMElts_spec hx).2.1

theorem mem_fendelMElts {x : Array ℕ} (h : x = fendelAArr ∨ x = fendelCArr ∨ x = fendelKArr ∨
    x = fendelYArr ∨ x = fendelYHArr ∨ x = fendelY'Arr ∨ x = fendelY'HArr ∨ x = fendelY'ZHArr ∨
    x = fendelGArr 0 ∨ x = fendelGArr 1 ∨ x = fendelGArr 2 ∨ x = fendelGArr 3 ∨
    x = fendelGHArr 0 ∨ x = fendelGHArr 1 ∨ x = fendelGHArr 2 ∨ x = fendelGHArr 3 ∨
    x = fendelK2Arr) : x ∈ fendelMElts := by
  simp only [fendelMElts, List.mem_cons, List.not_mem_nil, or_false]
  exact h

theorem mem_fendelAArr : fendelAArr ∈ fendelMElts := mem_fendelMElts <|
  Or.inl rfl

theorem mem_fendelCArr : fendelCArr ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inl rfl

theorem mem_fendelKArr : fendelKArr ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inl rfl

theorem mem_fendelYArr : fendelYArr ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

theorem mem_fendelYHArr : fendelYHArr ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

theorem mem_fendelYpArr : fendelY'Arr ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

theorem mem_fendelYpHArr : fendelY'HArr ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

theorem mem_fendelYpZHArr : fendelY'ZHArr ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

theorem mem_fendelGArr_0 : (fendelGArr 0) ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

theorem mem_fendelGArr_1 : (fendelGArr 1) ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
  Or.inr <| Or.inl rfl

theorem mem_fendelGArr_2 : (fendelGArr 2) ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
  Or.inr <| Or.inr <| Or.inl rfl

theorem mem_fendelGArr_3 : (fendelGArr 3) ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
  Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

theorem mem_fendelGHArr_0 : (fendelGHArr 0) ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

theorem mem_fendelGHArr_1 : (fendelGHArr 1) ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

theorem mem_fendelGHArr_2 : (fendelGHArr 2) ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

theorem mem_fendelGHArr_3 : (fendelGHArr 3) ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

theorem mem_fendelK2Arr : fendelK2Arr ∈ fendelMElts := mem_fendelMElts <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
  rfl

@[expose] def fendelA :
    co3M := fendelElt fendelAArr mem_fendelAArr

@[expose] def co3TtM :
    co3M := ⟨co3Tt, co3Tt_mem_M⟩

theorem co3TtM_coe :
    (co3TtM : Equiv.Perm (Fin 276)) = co3Tt := rfl

theorem co3ZM_coe
    : (co3ZM : Equiv.Perm (Fin 276)) = co3Z := rfl

theorem rep_fendelA :
    Rep 276 fendelAArr ((fendelA : co3M) : Equiv.Perm (Fin 276)) :=
  rep_fendelElt _

theorem rep_co3ZM
    : Rep 276 co3ZArr ((co3ZM : co3M) : Equiv.Perm (Fin 276)) := rep_co3Z

theorem rep_co3TtM
    : Rep 276 co3TtArr ((co3TtM : co3M) : Equiv.Perm (Fin 276)) := rep_co3Tt

theorem fendel_eq_of_eqA
    {x y u v : co3M} {X Y U V : Array ℕ}
    (hx : Rep 276 X (x : Equiv.Perm (Fin 276))) (hy : Rep 276 Y (y : Equiv.Perm (Fin 276)))
    (hu : Rep 276 U (u : Equiv.Perm (Fin 276))) (hv : Rep 276 V (v : Equiv.Perm (Fin 276)))
    (h : eqA 276 (compA 276 X Y) (compA 276 U V) = true) : x * y = u * v := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact eq_of_eqA (rep_compA hx hy) (rep_compA hu hv) h

theorem fendel_comm_of_commutesA
    {x y : co3M} {X Y : Array ℕ}
    (hx : Rep 276 X (x : Equiv.Perm (Fin 276))) (hy : Rep 276 Y (y : Equiv.Perm (Fin 276)))
    (h : commutesA 276 X Y = true) : x * y = y * x :=
  fendel_eq_of_eqA hx hy hy hx h

theorem fendel_isConj_of_eqA
    {h x u : co3M} {X U Hh : Array ℕ}
    (hh : Rep 276 Hh (h : Equiv.Perm (Fin 276))) (hx : Rep 276 X (x : Equiv.Perm (Fin 276)))
    (hu : Rep 276 U (u : Equiv.Perm (Fin 276)))
    (he : eqA 276 (compA 276 Hh X) (compA 276 U Hh) = true) : IsConj u x := by
  have e := fendel_eq_of_eqA hh hx hu hh he
  refine isConj_iff.2 ⟨h⁻¹, ?_⟩
  calc h⁻¹ * u * h⁻¹⁻¹ = h⁻¹ * (u * h) := by group
    _ = h⁻¹ * (h * x) := by rw [e]
    _ = x := by group

theorem co3ZM_central
    (g : co3M) : g * co3ZM = co3ZM * g :=
  mem_center_iff.1 (co3M_center ▸ mem_zpowers co3ZM) g

abbrev fendelK :
    Subgroup co3M := centralizer ({co3TtM} : Set co3M)

theorem co3ZM_mem_K :
    co3ZM ∈ fendelK :=
  mem_centralizer_singleton_iff.2 (co3ZM_central co3TtM).symm

@[expose] def fendelZK :
    fendelK := ⟨co3ZM, co3ZM_mem_K⟩

theorem fendelK_mem_M1
    (k : fendelK) : ((k : co3M) : Equiv.Perm (Fin 276)) ∈ co3M1 := by
  rw [co3M1_eq_centralizer]
  refine mem_inf.2 ⟨co3M_le_P (k : co3M).2, mem_centralizer_singleton_iff.2 ?_⟩
  have h := congrArg Subtype.val (mem_centralizer_singleton_iff.1 k.2)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, co3TtM_coe] at h
  exact h

@[expose] def fendelKtoM1 :
    fendelK →* co3M1 :=
  (co3M.subtype.comp fendelK.subtype).codRestrict co3M1 fun k => by
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact fendelK_mem_M1 k

theorem fendelKtoM1_coe
    (k : fendelK) :
    ((fendelKtoM1 k : co3M1) : Equiv.Perm (Fin 276)) = ((k : co3M) : Equiv.Perm (Fin 276)) := by
  simp [fendelKtoM1]

theorem fendelKtoM1_mk
    {x : co3M} (hx : x ∈ fendelK) (m : co3M1)
    (h : (m : Equiv.Perm (Fin 276)) = (x : Equiv.Perm (Fin 276))) : fendelKtoM1 ⟨x, hx⟩ = m :=
  Subtype.ext ((fendelKtoM1_coe _).trans h.symm)

@[expose] def fendelWG : G12 := ⟨wordP fendelW, wordP_mem _⟩

theorem fendelWG_coe : (fendelWG : Equiv.Perm (Fin 12)) = wordP fendelW := rfl

@[expose] def fendelK1G
    : fendelK →* G12 :=
  (co3Kappa1.comp fendelKtoM1).codRestrict NativeSporadic.M12 fun k => by
    rw [← co3Kappa1_range]
    exact MonoidHom.mem_range.2 ⟨_, rfl⟩

theorem fendelK1G_coe
    (k : fendelK) :
    (fendelK1G k : Equiv.Perm (Fin 12)) = co3Kappa1 (fendelKtoM1 k) := by
  simp [fendelK1G]

@[expose] def fendelKappaG
    : fendelK →* G12 :=
  (MulAut.conj fendelWG).toMonoidHom.comp fendelK1G

theorem fendelKappaG_apply
    (k : fendelK) :
    fendelKappaG k = fendelWG * fendelK1G k * fendelWG⁻¹ := by
  simp [fendelKappaG]

theorem tbl_eq_fendelTbl {x : Array ℕ} {σ : Equiv.Perm (Fin 12)} (h : Rep 12 x σ) :
    tbl σ = fendelTbl x := by
  apply List.ext_getElem
  · simp [tbl, fendelTbl]
  · intro i h1 h2
    have hi : i < 12 := by simpa [tbl] using h1
    simp only [tbl, fendelTbl, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    rw [h.apply hi]

theorem tbl_fendelKappaG
    {k : fendelK} {x : Array ℕ}
    (hx : Rep 276 x ((k : co3M) : Equiv.Perm (Fin 276))) :
    tbl ((fendelKappaG k : G12) : Equiv.Perm (Fin 12)) = fendelKTbl x := by
  have hx' : Rep 276 x ((fendelKtoM1 k : co3M1) : Equiv.Perm (Fin 276)) := by
    rw [fendelKtoM1_coe]
    exact hx
  have h1 : Rep 12 (fendelK1 x) (co3Kappa1 (fendelKtoM1 k)) := rep_kappa1 hx'
  rw [fendelKappaG_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, fendelK1G_coe,
    fendelWG_coe, tbl_mul, tbl_mul, tbl_inv, tbl_wordP, tbl_eq_fendelTbl h1]
  rfl

theorem fendelKappaG_z
    : fendelKappaG fendelZK = Jelt := by
  apply Subtype.ext
  apply tbl_injective
  rw [tbl_fendelKappaG (k := fendelZK) rep_co3ZM, fendel_check_w]
  exact tbl_bfJ.symm

theorem fendelKappaG_mem_CJ
    (k : fendelK) : fendelKappaG k ∈ CJ := by
  rw [mem_CJ]
  have hc : k * fendelZK = fendelZK * k := Subtype.ext (co3ZM_central k)
  have h1 := congrArg fendelKappaG hc
  rw [map_mul, map_mul, fendelKappaG_z] at h1
  have h2 := congrArg Subtype.val h1
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
  exact h2.symm

@[expose] def fendelKappa
    : fendelK →* CJ := fendelKappaG.codRestrict CJ fendelKappaG_mem_CJ

theorem fendelKappa_coe
    (k : fendelK) : (fendelKappa k : G12) = fendelKappaG k := by
  simp [fendelKappa]

theorem fendelKappa_z
    (h : co3ZM ∈ fendelK) : fendelKappa ⟨co3ZM, h⟩ = zJ :=
  Subtype.ext ((fendelKappa_coe _).trans fendelKappaG_z)

theorem fendelKappa_zK
    : fendelKappa fendelZK = zJ := fendelKappa_z co3ZM_mem_K

theorem tauC_fendelKappa
    {k : fendelK} {x : Array ℕ}
    (hx : Rep 276 x ((k : co3M) : Equiv.Perm (Fin 276))) : tauC (fendelKappa k) = fendelKTbl x := by
  rw [tauC, fendelKappa_coe]
  exact tbl_fendelKappaG hx

@[expose] def fendelG0 :
    co3M := fendelElt (fendelGArr 0) mem_fendelGArr_0

@[expose] def fendelK2 :
    co3M := fendelElt fendelK2Arr mem_fendelK2Arr

theorem fendelG0_mem_K :
    fendelG0 ∈ fendelK :=
  mem_centralizer_singleton_iff.2
    (fendel_comm_of_commutesA (rep_fendelElt _) rep_co3TtM (fendel_check_g 0 (by norm_num)).1)

theorem fendelK2_mem_K :
    fendelK2 ∈ fendelK :=
  mem_centralizer_singleton_iff.2
    (fendel_comm_of_commutesA (rep_fendelElt _) rep_co3TtM fendel_check_comm.1)

theorem fendel_comm_z :
    fendelG0 * fendelK2 * fendelG0⁻¹ * fendelK2⁻¹ = co3ZM := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul]
  exact eq_of_eqA (rep_compA (rep_compA (rep_compA (rep_fendelElt _) (rep_fendelElt _))
    (rep_fendelElt_inv _)) (rep_fendelElt_inv _)) rep_co3ZM fendel_check_comm.2

theorem co3ZM_mem_L1
    : fendelKtoM1 fendelZK ∈ co3L1 := by
  set g : fendelK := ⟨fendelG0, fendelG0_mem_K⟩
  set k : fendelK := ⟨fendelK2, fendelK2_mem_K⟩
  have h := comm_mem_of_index_two co3L1 co3L1_index (fendelKtoM1 g)⁻¹ (fendelKtoM1 k)
  have hgk : g * k * g⁻¹ * k⁻¹ = fendelZK := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
    exact fendel_comm_z
  have e : (fendelKtoM1 g)⁻¹⁻¹ * fendelKtoM1 k * (fendelKtoM1 g)⁻¹ * (fendelKtoM1 k)⁻¹ =
      fendelKtoM1 fendelZK := by
    rw [inv_inv, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hgk]
  rw [← e]
  exact h

theorem fendelKappa_surjective
    : Function.Surjective fendelKappa := by
  rintro ⟨c, hc⟩
  obtain ⟨m, hm⟩ : ∃ m : co3M1,
      co3Kappa1 m = ((fendelWG⁻¹ * c * fendelWG : G12) : Equiv.Perm (Fin 12)) := by
    have h : ((fendelWG⁻¹ * c * fendelWG : G12) : Equiv.Perm (Fin 12)) ∈ co3Kappa1.range := by
      rw [co3Kappa1_range]
      exact (fendelWG⁻¹ * c * fendelWG).2
    exact MonoidHom.mem_range.1 h
  have hzJ : fendelK1G fendelZK = fendelWG⁻¹ * Jelt * fendelWG := by
    have h := fendelKappaG_z
    rw [fendelKappaG_apply] at h
    rw [← h]
    group
  have hcJ : c * Jelt = Jelt * c := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (mem_CJ.1 hc).symm
  have hcomm : co3Kappa1 m * co3Kappa1 (fendelKtoM1 fendelZK) =
      co3Kappa1 (fendelKtoM1 fendelZK) * co3Kappa1 m := by
    rw [← fendelK1G_coe, hzJ, hm, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
    refine congrArg Subtype.val ?_
    calc (fendelWG⁻¹ * c * fendelWG) * (fendelWG⁻¹ * Jelt * fendelWG)
        = fendelWG⁻¹ * (c * Jelt) * fendelWG := by group
      _ = fendelWG⁻¹ * (Jelt * c) * fendelWG := by rw [hcJ]
      _ = (fendelWG⁻¹ * Jelt * fendelWG) * (fendelWG⁻¹ * c * fendelWG) := by group
  have hker : m * fendelKtoM1 fendelZK * m⁻¹ * (fendelKtoM1 fendelZK)⁻¹ ∈ zpowers co3TtM1 := by
    rw [← co3Kappa1_ker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_two orderOf_co3TtM1 hker with h1 | h1
  · have hmz : m * fendelKtoM1 fendelZK = fendelKtoM1 fendelZK * m := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hmz' : (m : Equiv.Perm (Fin 276)) * co3Z = co3Z * m := by
      have h2 := congrArg Subtype.val hmz
      rw [Subgroup.coe_mul, Subgroup.coe_mul, fendelKtoM1_coe] at h2
      exact h2
    have hmM : (m : Equiv.Perm (Fin 276)) ∈ co3M := by
      rw [co3M_eq_centralizer]
      exact mem_inf.2 ⟨co3M1_le_P m.2, mem_centralizer_singleton_iff.2 hmz'⟩
    have hmK : (⟨m, hmM⟩ : co3M) ∈ fendelK := by
      refine mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, co3TtM_coe]
      exact mem_centralizer_singleton_iff.1 (co3M1_le_centralizer m.2)
    refine ⟨⟨⟨m, hmM⟩, hmK⟩, Subtype.ext ?_⟩
    rw [fendelKappa_coe, fendelKappaG_apply]
    have e : fendelK1G ⟨⟨m, hmM⟩, hmK⟩ = fendelWG⁻¹ * c * fendelWG := by
      have e0 : fendelKtoM1 ⟨⟨m, hmM⟩, hmK⟩ = m :=
        fendelKtoM1_mk (x := ⟨m, hmM⟩) hmK m rfl
      apply Subtype.ext
      rw [fendelK1G_coe, e0, hm]
    rw [e]
    group
  · exfalso
    have hL := mul_mem (co3L1_normal.conj_mem _ co3ZM_mem_L1 m) (inv_mem co3ZM_mem_L1)
    rw [h1] at hL
    exact co3Tt_not_mem_L (mem_subgroupOf.1 hL)

theorem fendelKappa_eq_one_iff
    (k : fendelK) :
    fendelKappa k = 1 ↔ (k : co3M) = 1 ∨ (k : co3M) = co3TtM := by
  have hiff : fendelKappa k = 1 ↔ fendelK1G k = 1 := by
    rw [← Subtype.coe_inj, OneMemClass.coe_one, fendelKappa_coe, fendelKappaG_apply]
    constructor
    · intro h
      have h3 : fendelK1G k = fendelWG⁻¹ * (fendelWG * fendelK1G k * fendelWG⁻¹) * fendelWG := by
        group
      rw [h3, h]
      group
    · intro h
      rw [h]
      group
  rw [hiff, ← Subtype.coe_inj, OneMemClass.coe_one, fendelK1G_coe, ← MonoidHom.mem_ker,
    co3Kappa1_ker]
  constructor
  · intro h
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_two orderOf_co3TtM1 h with h3 | h3
    · left
      apply Subtype.ext
      rw [← fendelKtoM1_coe, h3, OneMemClass.coe_one, OneMemClass.coe_one]
    · right
      apply Subtype.ext
      rw [← fendelKtoM1_coe, h3, co3TtM_coe]
      rfl
  · rintro (h | h)
    · have h1 : fendelKtoM1 k = 1 := by
        apply Subtype.ext
        rw [fendelKtoM1_coe, h, OneMemClass.coe_one, OneMemClass.coe_one]
      rw [h1]
      exact one_mem _
    · have h1 : fendelKtoM1 k = co3TtM1 := by
        apply Subtype.ext
        rw [fendelKtoM1_coe, h, co3TtM_coe]
        rfl
      rw [h1]
      exact mem_zpowers _

theorem co3T_le_M :
    co3T ≤ co3M := fun x hx => by
  rw [co3M_eq_centralizer]
  exact mem_inf.2 ⟨co3T_le_P hx, co3T_le_centralizer_Z hx⟩

theorem fendel_T_involution
    {x : Equiv.Perm (Fin 276)} (hx : x ∈ co3T) (h2 : x * x = 1)
    (h1 : x ≠ 1) : x = co3Z ∨ ∃ h : co3M, ((h : Equiv.Perm (Fin 276)) * x =
      (fendelA : Equiv.Perm (Fin 276)) * h ∨ (h : Equiv.Perm (Fin 276)) * x = co3Tt * h) := by
  have hF := chainCheckFacts co3TChain_check.1
  obtain ⟨a, ha, b, hb, c, hc', hprod⟩ := ChainArrays.exists_prod3 co3TArrays (by norm_num)
    co3TChain_check.1 (by decide) (fun i h3 hi => absurd hi (by change ¬ i < 3; omega)) hx
  have h0 : (0 : ℕ) < co3TChain.baseCount := by decide
  have h1' : (1 : ℕ) < co3TChain.baseCount := by decide
  have h2' : (2 : ℕ) < co3TChain.baseCount := by decide
  have hrep : Rep 276 (fendelTArr a b c) x := by
    rw [← hprod]
    exact rep_compA (rep_compA (co3TArrays.rep_levT hF h0 ha) (co3TArrays.rep_levT hF h1' hb))
      (co3TArrays.rep_levT hF h2' hc')
  obtain ⟨s0, s1, s2⟩ := fendel_check_Tsizes
  have ha' : a < 128 := by
    have : (ChainArrays.lev 276 co3TArrs co3TBaseArr 0).pts.size = 128 := s0
    omega
  have hb' : b < 4 := by
    have : (ChainArrays.lev 276 co3TArrs co3TBaseArr 1).pts.size = 4 := s1
    omega
  have hc'' : c < 2 := by
    have : (ChainArrays.lev 276 co3TArrs co3TBaseArr 2).pts.size = 2 := s2
    omega
  have hok := fendelWit_check (⟨a, ha'⟩, ⟨b, hb'⟩, ⟨c, hc''⟩)
  simp only [fendelWitOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at hok
  have hne : eqA 276 (fendelTArr a b c) (idA 276) = false := by
    rw [← Bool.not_eq_true, eqA_iff hrep rep_idA]
    exact h1
  have hsq : eqA 276 (compA 276 (fendelTArr a b c) (fendelTArr a b c)) (idA 276) = true :=
    (eqA_iff (rep_compA hrep hrep) rep_idA).2 h2
  set w := fendelWit[(a * 4 + b) * 2 + c]!
  rcases hok with (((h | h) | ⟨-, h⟩) | ⟨⟨⟨-, hi⟩, hs⟩, he⟩) | ⟨⟨⟨-, hi⟩, hs⟩, he⟩
  · rw [hne] at h
    exact absurd h (by decide)
  · rw [hsq] at h
    exact absurd h (by decide)
  · exact Or.inl (eq_of_eqA hrep rep_co3Z h)
  · have hr := rep_permOfArr hi
    refine Or.inr ⟨⟨_, mem_co3M_of_sift hr.1 hs⟩, Or.inl ?_⟩
    exact eq_of_eqA (rep_compA hr.1 hrep) (rep_compA rep_fendelA hr.1) he
  · have hr := rep_permOfArr hi
    refine Or.inr ⟨⟨_, mem_co3M_of_sift hr.1 hs⟩, Or.inr ?_⟩
    exact eq_of_eqA (rep_compA hr.1 hrep) (rep_compA rep_co3Tt hr.1) he

theorem factorization_2903040_two : Nat.factorization 2903040 2 = 10 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  have h : (2903040 : ℕ) = 2 ^ 10 * 2835 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem card_co3T_subgroupOf_M :
    Nat.card (co3T.subgroupOf co3M) = 1024 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe co3T_le_M).toEquiv, card_co3T]

theorem fendel_co3_involutions
    (y : co3M) (hy : orderOf y = 2) :
    y = co3ZM ∨ IsConj fendelA y ∨ IsConj co3TtM y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTS : Nat.card (co3T.subgroupOf co3M) = 2 ^ (Nat.card co3M).factorization 2 := by
    rw [card_co3T_subgroupOf_M, card_co3M, factorization_2903040_two]
    norm_num
  obtain ⟨P, hP⟩ := ((isPGroup_zpowers_iff y).2 ⟨1, by rw [hy, pow_one]⟩).exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_sylow_iff (Sylow.ofCard _ hTS) P
  have hyT := (hg y).1 (hP (mem_zpowers y))
  rw [Sylow.coe_ofCard, mem_subgroupOf] at hyT
  have hx2 : g⁻¹ * y * g * (g⁻¹ * y * g) = 1 := by
    have h := fendel_mul_self_eq_one hy
    calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
      _ = 1 := by rw [h]; group
  have hx1 : g⁻¹ * y * g ≠ 1 := by
    intro h
    apply fendel_ne_one hy
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hx2' : ((g⁻¹ * y * g : co3M) : Equiv.Perm (Fin 276)) *
      ((g⁻¹ * y * g : co3M) : Equiv.Perm (Fin 276)) = 1 := by
    rw [← Subgroup.coe_mul, hx2, OneMemClass.coe_one]
  have hx1' : ((g⁻¹ * y * g : co3M) : Equiv.Perm (Fin 276)) ≠ 1 := by
    intro h
    apply hx1
    apply Subtype.ext
    rw [h, OneMemClass.coe_one]
  have hyg : IsConj (g⁻¹ * y * g) y := isConj_iff.2 ⟨g, by group⟩
  rcases fendel_T_involution hyT hx2' hx1' with h | ⟨h, hh | hh⟩
  · left
    have h1 : g⁻¹ * y * g = co3ZM := Subtype.ext h
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = g * co3ZM * g⁻¹ := by rw [h1]
      _ = co3ZM := by rw [co3ZM_central g, mul_inv_cancel_right]
  · right
    left
    have e : h * (g⁻¹ * y * g) = fendelA * h := by
      apply Subtype.ext
      rw [Subgroup.coe_mul _ h, Subgroup.coe_mul _ fendelA h]
      exact hh
    have hc : IsConj fendelA (g⁻¹ * y * g) := isConj_iff.2 ⟨h⁻¹, by
      calc h⁻¹ * fendelA * h⁻¹⁻¹ = h⁻¹ * (fendelA * h) := by group
        _ = h⁻¹ * (h * (g⁻¹ * y * g)) := by rw [e]
        _ = g⁻¹ * y * g := by group⟩
    exact hc.trans hyg
  · right
    right
    have e : h * (g⁻¹ * y * g) = co3TtM * h := by
      apply Subtype.ext
      rw [Subgroup.coe_mul _ h, Subgroup.coe_mul _ co3TtM h, co3TtM_coe]
      exact hh
    have hc : IsConj co3TtM (g⁻¹ * y * g) := isConj_iff.2 ⟨h⁻¹, by
      calc h⁻¹ * co3TtM * h⁻¹⁻¹ = h⁻¹ * (co3TtM * h) := by group
        _ = h⁻¹ * (h * (g⁻¹ * y * g)) := by rw [e]
        _ = g⁻¹ * y * g := by group⟩
    exact hc.trans hyg

theorem orderOf_fendelA :
    orderOf fendelA = 2 := by
  obtain ⟨h1, h2, -⟩ := fendel_check_a
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two]
    apply Subtype.ext
    rw [Subgroup.coe_mul, OneMemClass.coe_one]
    exact eq_of_eqA (rep_compA rep_fendelA rep_fendelA) rep_idA h1
  · intro h
    have h3 := (eqA_iff rep_fendelA rep_idA).2 (by rw [h, OneMemClass.coe_one])
    rw [h3] at h2
    exact absurd h2 (by decide)

theorem orderOf_co3TtM :
    orderOf co3TtM = 2 := by
  rw [← Subgroup.orderOf_coe, co3TtM_coe, orderOf_co3Tt]

theorem co3TtM_ne_co3ZM :
    co3TtM ≠ co3ZM := by
  intro h
  have h1 := congrArg Subtype.val h
  rw [co3TtM_coe, co3ZM_coe] at h1
  have h2 := (eqA_iff rep_co3Tt rep_co3Z).2 h1
  rw [fendel_check_a.2.2] at h2
  exact absurd h2 (by decide)

@[expose] def fendelC :
    co3M := fendelElt fendelCArr mem_fendelCArr

@[expose] def fendelKz :
    co3M := fendelElt fendelKArr mem_fendelKArr

theorem rep_co3ZM_mul_co3TtM :
    Rep 276 (compA 276 co3ZArr co3TtArr) ((co3ZM * co3TtM : co3M) : Equiv.Perm (Fin 276)) := by
  rw [Subgroup.coe_mul]
  exact rep_compA rep_co3ZM rep_co3TtM

theorem bfS'_le_CJ : bfS' ≤ CJ := fun x hx => by
  rw [mem_CJ]
  have h := congrArg Subtype.val (bfS'_comm_Jelt hx)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
  exact h.symm

abbrev fendelBS : Subgroup CJ := bfS'.subgroupOf CJ

theorem card_fendelBS : Nat.card fendelBS = 64 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe bfS'_le_CJ).toEquiv, card_bfS']

theorem fendelBS_center
    {b : CJ} (hb : b ∈ fendelBS) (hc : ∀ c ∈ fendelBS, c * b = b * c) :
    b = 1 ∨ b = zJ := by
  have hbT : tauC b ∈ BT := mem_bfS_iff.1 (mem_subgroupOf.1 hb)
  have hcT : ∀ u ∈ BT, tmul (tauC b) u = tmul u (tauC b) := by
    intro u hu
    obtain ⟨n, -, hn⟩ := mem_BT_iff.1 hu
    have hσ : bfElt (n / 32) ((n / 16) % 2) ((n / 8) % 2) (n % 8) ∈ bfS := bfElt_mem _ _ _ _
    have hs : (⟨_, bfS_le_M12 hσ⟩ : G12) ∈ bfS' := hσ
    set e : CJ := ⟨_, bfS'_le_CJ hs⟩
    have he : tauC e = u := by
      rw [hn, ← tbl_bfElt]
      rfl
    have h1 := congrArg tauC (hc e (mem_subgroupOf.2 hs))
    rw [tauC_mul, tauC_mul, he] at h1
    exact h1.symm
  rcases fendel_bfS_center _ hbT hcT with h | h
  · exact Or.inl (tauC_injective (h.trans tauC_one.symm))
  · exact Or.inr (tauC_injective (h.trans tauC_zJ.symm))

abbrev fendelR0
    : Subgroup fendelK := fendelBS.comap fendelKappa

abbrev fendelR
    : Subgroup co3M := fendelR0.map fendelK.subtype

@[expose] def fendelTK :
    fendelK := ⟨co3TtM, mem_centralizer_singleton_iff.2 rfl⟩

theorem fendelKappa_t :
    fendelKappa fendelTK = 1 :=
  (fendelKappa_eq_one_iff _).2 (Or.inr rfl)

theorem isPGroup_fendelR0 :
    IsPGroup 2 fendelR0 := by
  intro g
  refine ⟨7, ?_⟩
  have hg : fendelKappa g ∈ fendelBS := g.2
  have h64 : (fendelKappa (g : fendelK)) ^ 64 = 1 := by
    have h := pow_card_eq_one' (G := fendelBS) (x := ⟨_, hg⟩)
    rw [card_fendelBS] at h
    have h2 := congrArg Subtype.val h
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    exact h2
  have h1 : fendelKappa ((g : fendelK) ^ 64) = 1 := by rw [map_pow, h64]
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rcases (fendelKappa_eq_one_iff _).1 h1 with h2 | h2
  · rw [show (2 : ℕ) ^ 7 = 64 * 2 by norm_num, pow_mul]
    have h3 : (g : fendelK) ^ 64 = 1 := Subtype.ext (by rw [h2, OneMemClass.coe_one])
    rw [h3, one_pow]
  · rw [show (2 : ℕ) ^ 7 = 64 * 2 by norm_num, pow_mul]
    have h3 : (g : fendelK) ^ 64 = fendelTK := Subtype.ext h2
    rw [h3]
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    show co3TtM ^ 2 = 1
    rw [← orderOf_co3TtM, pow_orderOf_eq_one]

theorem fendelR_subgroupOf
    : fendelR.subgroupOf fendelK = fendelR0 :=
  comap_map_eq_self_of_injective fendelK.subtype_injective _

theorem fendelR0_index
    : fendelR0.index = 3 := by
  rw [index_comap_of_surjective _ fendelKappa_surjective]
  have h := fendelBS.card_mul_index
  rw [card_fendelBS, card_CJ] at h
  omega

theorem fendelR_center
    {x : co3M} (hx : x ∈ fendelR) (hc : ∀ y ∈ fendelR, x * y = y * x) :
    x = 1 ∨ x = co3ZM ∨ x = co3TtM ∨ x = co3ZM * co3TtM := by
  obtain ⟨x', hx', rfl⟩ := mem_map.1 hx
  have hxc : ∀ c ∈ fendelBS, c * fendelKappa x' = fendelKappa x' * c := by
    intro c hc'
    obtain ⟨y', rfl⟩ := fendelKappa_surjective c
    have hy' : (y' : co3M) ∈ fendelR := mem_map.2 ⟨y', hc', rfl⟩
    have h1 : x' * y' = y' * x' := Subtype.ext (hc _ hy')
    rw [← map_mul, ← map_mul, h1]
  rcases fendelBS_center hx' hxc with h | h
  · rcases (fendelKappa_eq_one_iff _).1 h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
  · have h2 : fendelKappa (x' * fendelZK⁻¹) = 1 := by
      rw [map_mul, map_inv, h, fendelKappa_zK]
      exact mul_inv_cancel _
    rcases (fendelKappa_eq_one_iff _).1 h2 with h3 | h3
    · right
      left
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_eq_one] at h3
      exact h3
    · right
      right
      right
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_eq_iff_eq_mul] at h3
      rw [Subgroup.coe_subtype, h3]
      exact (co3ZM_central co3TtM)

theorem fendel_co3_noncomm
    : ¬ ∀ x y : co3M, x * y = y * x := by
  intro hc
  have hZ : center co3M = ⊤ := eq_top_iff.2 fun x _ => mem_center_iff.2 fun g => hc g x
  have h := card_co3M_center
  rw [hZ, card_top, card_co3M] at h
  omega

theorem fendel_co3_sylow :
    ∃ T : Subgroup co3M, IsPGroup 2 T ∧ ¬ 2 ∣ T.index ∧ co3ZM ∈ T ∧
    ∀ x ∈ T, (∀ y ∈ T, x * y = y * x) → x = 1 ∨ x = co3ZM := by
  refine ⟨co3T.subgroupOf co3M, ?_, ?_, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 10) (by rw [card_co3T_subgroupOf_M]; norm_num)
  · have h := (co3T.subgroupOf co3M).card_mul_index
    rw [card_co3T_subgroupOf_M, card_co3M] at h
    omega
  · rw [mem_subgroupOf, co3ZM_coe]
    exact co3Z_mem_T
  · intro x hx hxc
    have hcomm : ∀ y ∈ co3T, (x : Equiv.Perm (Fin 276)) * y = y * x := by
      intro y hy
      have h1 := hxc ⟨y, co3T_le_M hy⟩ (mem_subgroupOf.2 hy)
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
      exact h2
    rcases (co3T_center_iff (x : Equiv.Perm (Fin 276))).1 ⟨mem_subgroupOf.1 hx, hcomm⟩ with h | h
    · left
      apply Subtype.ext
      rw [h, OneMemClass.coe_one]
    · right
      apply Subtype.ext
      rw [h, co3ZM_coe]

theorem fendel_co3_conj_t0 :
    IsConj co3TtM (co3ZM * co3TtM) :=
  isConj_comm.1 (fendel_isConj_of_eqA (h := fendelC) (rep_fendelElt _) rep_co3TtM
    rep_co3ZM_mul_co3TtM fendel_check_c)

theorem fendel_co3_sq_z :
    ∃ k : co3M, k * co3TtM = co3TtM * k ∧ k * k = co3ZM := by
  refine ⟨fendelKz, fendel_comm_of_commutesA (rep_fendelElt _) rep_co3TtM fendel_check_k.1, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul]
  exact eq_of_eqA (rep_compA (rep_fendelElt _) (rep_fendelElt _)) rep_co3ZM fendel_check_k.2

theorem fendel_co3_not_sq_t0
    : ∀ k : co3M, k * co3TtM = co3TtM * k → k * k ≠ co3TtM := by
  intro k hk hsq
  have h1 := sq_mem_of_index_two co3L1_index
    (fendelKtoM1 ⟨k, mem_centralizer_singleton_iff.2 hk⟩)
  have h2 : fendelKtoM1 ⟨k, mem_centralizer_singleton_iff.2 hk⟩ ^ 2 = co3TtM1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, fendelKtoM1_coe, pow_two, ← Subgroup.coe_mul, hsq, co3TtM_coe]
    rfl
  rw [h2] at h1
  exact co3Tt_not_mem_L (mem_subgroupOf.1 h1)

theorem fendel_co3_sylow_t0
    : ∃ R : Subgroup co3M, R ≤ centralizer {co3TtM} ∧ IsPGroup 2 R ∧
    ¬ 2 ∣ (R.subgroupOf (centralizer {co3TtM})).index ∧ co3ZM ∈ R ∧ co3TtM ∈ R ∧
    ∀ x ∈ R, (∀ y ∈ R, x * y = y * x) →
      x = 1 ∨ x = co3ZM ∨ x = co3TtM ∨ x = co3ZM * co3TtM := by
  refine ⟨fendelR, map_subtype_le _, isPGroup_fendelR0.map _, ?_, ?_, ?_,
    fun x hx hc => fendelR_center hx hc⟩
  · rw [fendelR_subgroupOf, fendelR0_index]
    decide
  · refine mem_map.2 ⟨fendelZK, ?_, rfl⟩
    show fendelKappa fendelZK ∈ fendelBS
    rw [fendelKappa_zK]
    exact mem_subgroupOf.2 Jelt_mem_bfS'
  · refine mem_map.2 ⟨fendelTK, ?_, rfl⟩
    show fendelKappa fendelTK ∈ fendelBS
    rw [fendelKappa_t]
    exact one_mem _

theorem fendelLocalData_co3
    : FendelLocalData co3M co3ZM fendelA co3TtM :=
  ⟨co3ZM_central, orderOf_co3ZM, orderOf_fendelA, orderOf_co3TtM, co3TtM_ne_co3ZM,
    fendel_co3_noncomm, fendel_co3_involutions, fendel_co3_sylow, fendel_co3_conj_t0,
    fendel_co3_sq_z, fendel_co3_not_sq_t0, fendel_co3_sylow_t0⟩

theorem closure_genC_eq_top
    : closure {x | x ∈ genC} = (⊤ : Subgroup CJ) := by
  rw [eq_top_iff]
  intro x _
  have hR : ∀ t ∈ HT, ∃ y ∈ closure {x | x ∈ genC}, tauC y = t := by
    refine foldl_stepHT (fun t => ∃ y ∈ closure {x | x ∈ genC}, tauC y = t)
      ⟨1, one_mem _, tauC_one⟩ ?_ ?_ certHT [tid] ?_
    · intro g hg
      rw [← tauC_genC] at hg
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hg
      exact ⟨y, subset_closure hy, rfl⟩
    · rintro s t ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
      exact ⟨y * y', mul_mem hy hy', tauC_mul y y'⟩
    · intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      exact ⟨1, one_mem _, tauC_one⟩
  obtain ⟨y, hy, hyx⟩ := hR _ (tauC_mem x)
  rwa [tauC_injective hyx] at hy

theorem fendelGArr_mem (n : ℕ) : fendelGArr n ∈ fendelMElts := by
  rcases n with _ | _ | _ | n
  · exact mem_fendelGArr_0
  · exact mem_fendelGArr_1
  · exact mem_fendelGArr_2
  · exact mem_fendelGArr_3

theorem fendelGHArr_mem (n : ℕ) : fendelGHArr n ∈ fendelMElts := by
  rcases n with _ | _ | _ | n
  · exact mem_fendelGHArr_0
  · exact mem_fendelGHArr_1
  · exact mem_fendelGHArr_2
  · exact mem_fendelGHArr_3

theorem fendelGArr_mem_K
    {n : ℕ} (hn : n < 4) :
    fendelElt (fendelGArr n) (fendelGArr_mem n) ∈ fendelK :=
  mem_centralizer_singleton_iff.2
    (fendel_comm_of_commutesA (rep_fendelElt _) rep_co3TtM (fendel_check_g n hn).1)

@[expose] def fendelGK
    (n : ℕ) : fendelK :=
  if h : n < 4 then ⟨fendelElt (fendelGArr n) (fendelGArr_mem n), fendelGArr_mem_K h⟩ else 1

theorem fendelGK_coe
    {n : ℕ} (hn : n < 4) :
    ((fendelGK n : fendelK) : co3M) = fendelElt (fendelGArr n) (fendelGArr_mem n) := by
  rw [fendelGK, dite_eq_left hn]

theorem tauC_fendelGK
    {n : ℕ} (hn : n < 4) :
    tauC (fendelKappa (fendelGK n)) = fendelKTbl (fendelGArr n) := by
  refine tauC_fendelKappa ?_
  rw [fendelGK_coe hn]
  exact rep_fendelElt _

theorem fendelGK_isConj
    {n : ℕ} (hn : n < 4) : IsConj fendelA ((fendelGK n : fendelK) : co3M) := by
  rw [fendelGK_coe hn]
  exact fendel_isConj_of_eqA (rep_fendelElt (fendelGHArr_mem n)) (rep_fendelElt _) rep_fendelA
    (fendel_check_g n hn).2

@[expose] def fendelWordProd
    (u : List ℕ) : CJ :=
  (u.map fun i => fendelKappa (fendelGK (i - 1))).prod

theorem tauC_fendelWordProd :
    ∀ u : List ℕ, (∀ i ∈ u, 1 ≤ i ∧ i ≤ 4) → tauC (fendelWordProd u) = fendelGWordTbl u
  | [], _ => by simp [fendelWordProd, fendelGWordTbl, tauC_one]
  | i :: u, hu => by
    have hi := hu i (List.mem_cons_self ..)
    have ih := tauC_fendelWordProd u fun j hj => hu j (List.mem_cons_of_mem _ hj)
    rw [fendelWordProd, List.map_cons, List.prod_cons, tauC_mul] at *
    rw [ih, tauC_fendelGK (by omega)]
    rfl

abbrev fendelY :
    Set fendelK := {y | ∃ n < 4, y = fendelGK n}

theorem fendelWordProd_mem :
    ∀ u : List ℕ, (∀ i ∈ u, 1 ≤ i ∧ i ≤ 4) →
      fendelWordProd u ∈ closure (fendelKappa '' fendelY)
  | [], _ => by simp [fendelWordProd, one_mem]
  | i :: u, hu => by
    have hi := hu i (List.mem_cons_self ..)
    have ih := fendelWordProd_mem u fun j hj => hu j (List.mem_cons_of_mem _ hj)
    rw [fendelWordProd, List.map_cons, List.prod_cons]
    refine mul_mem (subset_closure ⟨fendelGK (i - 1), ⟨i - 1, by omega, rfl⟩, rfl⟩) ?_
    exact ih

theorem fendel_closure_gens
    : closure (fendelKappa '' fendelY) = ⊤ := by
  rw [eq_top_iff, ← closure_genC_eq_top, closure_le]
  intro x hx
  have hx' : tauC x ∈ gensT := by
    rw [← tauC_genC]
    exact List.mem_map_of_mem hx
  rw [← fendel_check_words.1] at hx'
  obtain ⟨u, hu, hux⟩ := List.mem_map.1 hx'
  have hu' := fendel_check_words.2 u hu
  have h := tauC_injective ((tauC_fendelWordProd u hu').trans hux)
  rw [← h]
  exact fendelWordProd_mem u hu'

@[expose] def fendelYK :
    fendelK :=
  ⟨fendelElt fendelYArr mem_fendelYArr, mem_centralizer_singleton_iff.2
    (fendel_comm_of_commutesA (rep_fendelElt _) rep_co3TtM fendel_check_y.1)⟩

@[expose] def fendelY'K :
    fendelK :=
  ⟨fendelElt fendelY'Arr mem_fendelYpArr, mem_centralizer_singleton_iff.2
    (fendel_comm_of_commutesA (rep_fendelElt _) rep_co3TtM fendel_check_y'.1)⟩

theorem fendel_co3_nwc
    : ∃ y : fendelK, IsConj fendelA (y : co3M) ∧ fendelKappa y ∈ Qsub ∧
    fendelKappa y ≠ zJ := by
  obtain ⟨-, h2, h3, h4⟩ := fendel_check_y
  have hrep : Rep 276 fendelYArr ((fendelYK : fendelK) : co3M) := rep_fendelElt mem_fendelYArr
  refine ⟨fendelYK, ?_, ?_, ?_⟩
  · exact fendel_isConj_of_eqA (rep_fendelElt mem_fendelYHArr) hrep rep_fendelA h2
  · rw [mem_Qsub, tauC_fendelKappa hrep]
    exact h3
  · intro h
    have h5 := congrArg tauC h
    rw [tauC_fendelKappa hrep, tauC_zJ] at h5
    exact h4 h5

theorem fendel_co3_fpf :
    ∃ y : fendelK, IsConj fendelA (y : co3M) ∧
    IsConj fendelA (co3ZM * (y : co3M)) := by
  obtain ⟨-, h2, h3⟩ := fendel_check_y'
  have hrep : Rep 276 fendelY'Arr ((fendelY'K : fendelK) : co3M) := rep_fendelElt mem_fendelYpArr
  have hrep' : Rep 276 (compA 276 co3ZArr fendelY'Arr)
      ((co3ZM * ((fendelY'K : fendelK) : co3M) : co3M) : Equiv.Perm (Fin 276)) := by
    rw [Subgroup.coe_mul]
    exact rep_compA rep_co3ZM hrep
  refine ⟨fendelY'K, ?_, ?_⟩
  · exact fendel_isConj_of_eqA (rep_fendelElt mem_fendelYpHArr) hrep rep_fendelA h2
  · exact fendel_isConj_of_eqA (rep_fendelElt mem_fendelYpZHArr) hrep' rep_fendelA h3

@[expose] def fendelM12Data_co3
    : FendelM12Data co3M co3ZM fendelA co3TtM where
  κ := fendelKappa
  surj := fendelKappa_surjective
  ker := fendelKappa_eq_one_iff
  κ_z := fendelKappa_z
  nwc := fendel_co3_nwc
  fpf := fendel_co3_fpf
  gens := ⟨fendelY, fun _ ⟨_, hn, hy⟩ => hy ▸ fendelGK_isConj hn, fendel_closure_gens⟩
  comm := ⟨fendelG0, fendelK2, mem_centralizer_singleton_iff.1 fendelG0_mem_K,
    mem_centralizer_singleton_iff.1 fendelK2_mem_K, fendel_comm_z⟩

end CFSG.EvenSmallLie.SympSix
