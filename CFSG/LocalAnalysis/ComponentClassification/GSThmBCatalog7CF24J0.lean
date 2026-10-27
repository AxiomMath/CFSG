module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7CF24Lift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7SuzCSZero
public import Certificates.Certificate15030
public import CFSG.Sporadic.HeldB.Common

public section

namespace CFSG.ComponentClassification.GSThmB.CF24

open CFSG CFSG.LocalCores CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits CFSG.ComponentClassification.CatFactsL4U4.SuzCS
  CFSG.PSL3Four.Native CFSG.LieType.Multipliers.Tits CFSG.Certificates
  CFSG.ComponentClassification.PSL3Four Subgroup
open scoped commutatorElement

@[expose] noncomputable def ellPerm (j : ℕ) : Equiv.Perm (Fin 1782) :=
  ⁅invInnerGen 0 1, invInnerGen 0 (j + 2)⁆

@[expose] noncomputable def J0 : Subgroup (Equiv.Perm (Fin 1782)) :=
  closure (Set.range fun j : Fin 5 => ellPerm j)

theorem perm_facts :
    allLt 7 (fun k => isInvA 1782 (invInnerGenArrs 0)[k]! (invCand 1782 (invInnerGenArrs 0)[k]!))
      = true ∧
    allPermsOK 1782 cf24EllArrs = true ∧
    lettersOK Sporadic.Recognition.SuzMultiplier.gcS (zword cf24X) = true ∧
    lettersOK Sporadic.Recognition.SuzMultiplier.gcS (zword cf24Y) = true ∧
    lettersOK 5 cf24XP = true ∧ lettersOK 5 cf24YP = true ∧
    eqA 1782 cf24XArr (wordArr 1782 cf24EllArrs cf24XP) = true ∧
    eqA 1782 cf24YArr (wordArr 1782 cf24EllArrs cf24YP) = true ∧
    eqA 1782 (compA 1782 cf24XArr cf24YArr) (compA 1782 cf24YArr cf24XArr) = true ∧
    allBelow 5 (fun j => allBelow 1782 fun x => cf24InO1 (cf24EllArrs[j]!)[x]! == cf24InO1 x)
      = true ∧
    allBelow 5 (fun j => eqA 1782 (compA 1782 betaArr cf24EllArrs[j]!)
      (compA 1782 cf24EllArrs[j]! betaArr)) = true ∧
    cf24InO1 6 = true ∧ cf24InO1 (tArr 0)[6]! = false ∧ cf24InO1 betaArr[6]! = false ∧
    cf24InO1 tBetaArr[6]! = false := by
  have h := cf24_perm_check
  unfold cf24PermCheck at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem size_cf24EllArrs : cf24EllArrs.size = 5 := by
  simp [cf24EllArrs]

theorem rep_ellArr {j : ℕ}
    (hj : j < 5) : Rep 1782 cf24EllArrs[j]! (ellPerm j) := by
  have hs : (invInnerGenArrs 0).size = 22 := invInnerGenArrs_size0'
  have h1 := rep_invInnerGen (i := 0) (j := 1) (by norm_num) (by omega)
  have h2 := rep_invInnerGen (i := 0) (j := j + 2) (by norm_num) (by omega)
  have i1 := rep_inv_of_isInvA h1 (allLt_spec perm_facts.1 (show 1 < 7 by norm_num))
  have i2 := rep_inv_of_isInvA h2 (allLt_spec perm_facts.1 (show j + 2 < 7 by omega))
  rw [cf24EllArrs, getElem!_ofFn_of_lt _ hj, ellPerm, commutatorElement_def]
  exact rep_compA (rep_compA (rep_compA h1 h2) i1) i2

theorem ellPerm_mem {j : ℕ} (hj : j < 5) : ellPerm j ∈ invE 0 := by
  have hs : (invInnerGenArrs 0).size = 22 := invInnerGenArrs_size0'
  have h1 := invInnerGen_mem (i := 0) (j := 1) (by norm_num) (by omega)
  have h2 := invInnerGen_mem (i := 0) (j := j + 2) (by norm_num) (by omega)
  rw [ellPerm, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem h1 h2) (inv_mem h1)) (inv_mem h2)

theorem J0_le_invE : J0 ≤ invE 0 := by
  rw [J0, closure_le]
  rintro _ ⟨j, rfl⟩
  exact ellPerm_mem j.2

theorem rho0_ell
    {j : ℕ} (hj : j < 5) : rho0 ⟨ellPerm j, ellPerm_mem hj⟩ = dperm j := by
  have hs : (invInnerGenArrs 0).size = 22 := invInnerGenArrs_size0'
  have e : (⟨ellPerm j, ellPerm_mem hj⟩ : invE 0) =
      ⁅innerGenE (i := 0) (by norm_num) 1, innerGenE (i := 0) (by norm_num) (j + 2)⁆ := by
    apply Subtype.ext
    have h1 : 1 < (invInnerGenArrs 0).size := by omega
    have h2 : j + 2 < (invInnerGenArrs 0).size := by omega
    simp only [ellPerm, commutatorElement_def, innerGenE, h1, h2, ↓reduceDIte, Subgroup.coe_mul,
      Subgroup.coe_inv]
  rw [e, map_commutatorElement]
  rfl

theorem exists_J0_of_suzD
    {d : Equiv.Perm (Fin 42)} (hd : d ∈ suzD) :
    ∃ g : invE 0, (g : Equiv.Perm (Fin 1782)) ∈ J0 ∧ rho0 g = d := by
  have hle : suzD ≤ (J0.subgroupOf (invE 0)).map rho0 := by
    rw [suzD, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨⟨ellPerm j, ellPerm_mem hj⟩, mem_subgroupOf.2 (subset_closure ⟨⟨j, hj⟩, rfl⟩),
      rho0_ell hj⟩
  obtain ⟨g, hg, rfl⟩ := hle hd
  exact ⟨g, hg, rfl⟩

theorem rho0_mem_suzD
    {g : invE 0} (hg : (g : Equiv.Perm (Fin 1782)) ∈ J0) : rho0 g ∈ suzD := by
  have key : J0 ≤ (suzD.comap rho0).map (invE 0).subtype := by
    rw [J0, closure_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨⟨ellPerm j, ellPerm_mem j.2⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_comap, rho0_ell j.2]
    exact subset_closure ⟨j, j.2, rfl⟩
  obtain ⟨g', hg', he⟩ := key hg
  rw [← Subtype.ext he]
  exact hg'

@[expose] def labStab : Subgroup (Equiv.Perm (Fin 1782)) where
  carrier := {g | ∀ x : Fin 1782, cf24InO1 (g x : ℕ) = cf24InO1 (x : ℕ)}
  mul_mem' := fun {a b} ha hb x => by rw [Equiv.Perm.mul_apply, ha, hb]
  one_mem' := fun x => rfl
  inv_mem' := fun {a} ha x => by
    have := ha (a⁻¹ x)
    rw [perm_apply_inv] at this
    exact this.symm

theorem J0_le_labStab :
    J0 ≤ labStab := by
  rw [J0, closure_le]
  rintro _ ⟨j, rfl⟩ x
  have h := allBelow_eq_true.1 perm_facts.2.2.2.2.2.2.2.2.2.1 j j.2
  have hx := allBelow_eq_true.1 h x x.2
  rw [beq_iff_eq, rep_ellArr j.2 x] at hx
  exact hx

theorem not_mem_J0_of_lab
    {g : Equiv.Perm (Fin 1782)} {t : Array ℕ} (ht : Rep 1782 t g)
    (h6 : cf24InO1 t[6]! = false) : g ∉ J0 := by
  intro hg
  have h := J0_le_labStab hg (6 : Fin 1782)
  have e : ((g (6 : Fin 1782) : Fin 1782) : ℕ) = t[6]! := (ht 6).symm
  rw [e, h6, show ((6 : Fin 1782) : ℕ) = 6 from rfl, perm_facts.2.2.2.2.2.2.2.2.2.2.2.1] at h
  exact Bool.false_ne_true h

theorem eq_one_of_mem_J0_ker
    {g : invE 0} (hg : (g : Equiv.Perm (Fin 1782)) ∈ J0) (hk : g ∈ rho0.ker) :
    (g : Equiv.Perm (Fin 1782)) = 1 := by
  have f := perm_facts.2.2.2.2.2.2.2.2.2.2.2.2
  rcases mem_ker_rho0 hk with h | h | h | h
  · exact h
  · exact absurd (h ▸ hg) (not_mem_J0_of_lab (rep_suzInv (i := 0) (by norm_num)) f.1)
  · exact absurd (h ▸ hg) (not_mem_J0_of_lab rep_betaPerm f.2.1)
  · exact absurd (h ▸ hg)
      (not_mem_J0_of_lab (rep_compA (rep_suzInv (i := 0) (by norm_num)) rep_betaPerm) f.2.2)

theorem card_J0_le :
    Nat.card J0 ≤ 20160 := by
  let f : J0 → suzD := fun g => ⟨rho0 ⟨g, J0_le_invE g.2⟩, rho0_mem_suzD g.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : rho0 ⟨a, J0_le_invE a.2⟩ = rho0 ⟨b, J0_le_invE b.2⟩ := congrArg Subtype.val hab
    have hm : (b : Equiv.Perm (Fin 1782))⁻¹ * a ∈ J0 := J0.mul_mem (J0.inv_mem b.2) a.2
    have hk : (⟨(b : Equiv.Perm (Fin 1782))⁻¹ * a, J0_le_invE hm⟩ : invE 0) ∈ rho0.ker := by
      have e : (⟨(b : Equiv.Perm (Fin 1782))⁻¹ * a, J0_le_invE hm⟩ : invE 0) =
          (⟨b, J0_le_invE b.2⟩ : invE 0)⁻¹ * ⟨a, J0_le_invE a.2⟩ := rfl
      rw [MonoidHom.mem_ker, e, map_mul, map_inv, h1, inv_mul_cancel]
    have h2 := eq_one_of_mem_J0_ker hm hk
    exact Subtype.ext (inv_mul_eq_one.1 h2).symm
  calc Nat.card J0 ≤ Nat.card suzD := Nat.card_le_card_of_injective f hf
    _ = 20160 := card_suzD

theorem commutatorElement_mul_of_commute {G : Type*} [Group G] {j j' v v' : G}
    (h1 : Commute v j') (h2 : Commute v v') (h3 : Commute v' j) :
    ⁅j * v, j' * v'⁆ = ⁅j, j'⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc j * v * (j' * v') * (j * v)⁻¹ * (j' * v')⁻¹ =
      j * (v * j') * v' * v⁻¹ * j⁻¹ * v'⁻¹ * j'⁻¹ := by group
    _ = j * j' * (v * v') * v⁻¹ * j⁻¹ * v'⁻¹ * j'⁻¹ := by rw [h1.eq]; group
    _ = j * j' * (v' * j⁻¹) * v'⁻¹ * j'⁻¹ := by rw [h2.eq]; group
    _ = j * j' * j⁻¹ * j'⁻¹ := by rw [h3.inv_right.eq]; group

theorem beta_comm_J0
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ J0) :
    Commute betaPerm g := by
  have hle : J0 ≤ centralizer {betaPerm} := by
    rw [J0, closure_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact (eq_of_eqA (rep_compA rep_betaPerm (rep_ellArr j.2))
      (rep_compA (rep_ellArr j.2) rep_betaPerm)
      (allBelow_eq_true.1 perm_facts.2.2.2.2.2.2.2.2.2.2.1 j j.2)).symm
  exact (mem_centralizer_singleton_iff.1 (hle hg)).symm

@[expose] def IsV (v : Equiv.Perm (Fin 1782)) : Prop :=
  v = 1 ∨ v = suzInv 0 ∨ v = betaPerm ∨ v = suzInv 0 * betaPerm

theorem isV_comm_J0
    {v g : Equiv.Perm (Fin 1782)} (hv : IsV v) (hg : g ∈ J0) :
    Commute v g := by
  have ht : Commute (suzInv 0) g := (comm_t0 (J0_le_invE hg)).symm
  rcases hv with rfl | rfl | rfl | rfl
  · exact Commute.one_left g
  · exact ht
  · exact beta_comm_J0 hg
  · exact ht.mul_left (beta_comm_J0 hg)

theorem isV_comm
    {v v' : Equiv.Perm (Fin 1782)} (hv : IsV v) (hv' : IsV v') : Commute v v' := by
  have htb : Commute betaPerm (suzInv 0) := comm_t0 betaPerm_mem
  have hall : ∀ w, IsV w → Commute (suzInv 0) w ∧ Commute betaPerm w := by
    rintro w (rfl | rfl | rfl | rfl)
    · exact ⟨Commute.one_right _, Commute.one_right _⟩
    · exact ⟨Commute.refl _, htb⟩
    · exact ⟨htb.symm, Commute.refl _⟩
    · exact ⟨(Commute.refl _).mul_right htb.symm, htb.mul_right (Commute.refl _)⟩
  obtain ⟨h1, h2⟩ := hall v' hv'
  rcases hv with rfl | rfl | rfl | rfl
  · exact Commute.one_left _
  · exact h1
  · exact h2
  · exact h1.mul_left h2

theorem component_le_J0
    (B : Subgroup (invE 0)) (hB : IsComponent B) :
    B.map (invE 0).subtype ≤ J0 := by
  have hBD := map_rho0_eq_suzD B hB
  have hdec : ∀ b ∈ B, ∃ j : invE 0, (j : Equiv.Perm (Fin 1782)) ∈ J0 ∧
      IsV ((j : Equiv.Perm (Fin 1782))⁻¹ * b) := by
    intro b hb
    have hd : rho0 b ∈ suzD := by rw [← hBD]; exact mem_map_of_mem _ hb
    obtain ⟨j, hj, hjb⟩ := exists_J0_of_suzD hd
    refine ⟨j, hj, ?_⟩
    have hk : j⁻¹ * b ∈ rho0.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hjb, inv_mul_cancel]
    exact mem_ker_rho0 hk
  have hperf : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp hB.1.1
  have hcomm : ⁅B, B⁆ ≤ J0.comap (invE 0).subtype := by
    rw [commutator_le]
    intro b hb b' hb'
    obtain ⟨j, hj, hv⟩ := hdec b hb
    obtain ⟨j', hj', hv'⟩ := hdec b' hb'
    rw [mem_comap, Subgroup.coe_subtype, show ((⁅b, b'⁆ : invE 0) : Equiv.Perm (Fin 1782)) =
      ⁅(b : Equiv.Perm (Fin 1782)), (b' : Equiv.Perm (Fin 1782))⁆ from rfl]
    have eb : (b : Equiv.Perm (Fin 1782)) =
        j * ((j : Equiv.Perm (Fin 1782))⁻¹ * b) := by group
    have eb' : (b' : Equiv.Perm (Fin 1782)) =
        j' * ((j' : Equiv.Perm (Fin 1782))⁻¹ * b') := by group
    rw [eb, eb', commutatorElement_mul_of_commute (isV_comm_J0 hv hj') (isV_comm hv hv')
      (isV_comm_J0 hv' hj)]
    rw [commutatorElement_def]
    exact J0.mul_mem (J0.mul_mem (J0.mul_mem hj hj') (J0.inv_mem hj)) (J0.inv_mem hj')
  rw [map_le_iff_le_comap, ← hperf]
  exact hcomm

theorem component_eq_J0
    (B : Subgroup (invE 0)) (hB : IsComponent B) :
    B.map (invE 0).subtype = J0 := by
  have hq := CTI_Suz_first_involution_local_component_simple_quotient_order B hB
  have hZ : 0 < Nat.card (center B) := Nat.card_pos
  have hB' := (center B).card_eq_card_quotient_mul_card_subgroup
  rw [hq] at hB'
  refine Subgroup.eq_of_le_of_card_ge (component_le_J0 B hB) ?_
  rw [Subgroup.card_map_of_injective (invE 0).subtype_injective, hB']
  calc Nat.card J0 ≤ 20160 := card_J0_le
    _ ≤ 20160 * Nat.card (center B) := Nat.le_mul_of_pos_right _ hZ

theorem eq_one_of_mem_center_J0
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ J0)
    (hc : ∀ h ∈ J0, g * h = h * g) : g = 1 := by
  set g' : invE 0 := ⟨g, J0_le_invE hg⟩
  have hD : rho0 g' ∈ suzD := rho0_mem_suzD hg
  have hcen : (⟨rho0 g', hD⟩ : suzD) ∈ center suzD := by
    rw [mem_center_iff]
    rintro ⟨d, hd⟩
    obtain ⟨h, hh, rfl⟩ := exists_J0_of_suzD hd
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc _ hh).symm
  have hbot : center suzD = ⊥ := by
    have := suzD_simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center suzD) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := suzD_noncomm
      have ha : a ∈ center suzD := h ▸ mem_top a
      exact hab (mem_center_iff.mp ha b).symm
  rw [hbot, mem_bot] at hcen
  have hk : g' ∈ rho0.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hcen
  exact eq_one_of_mem_J0_ker hg hk

theorem rep_ellWord {w : List ℤ}
    (hw : lettersOK 5 w = true) : Rep 1782 (wordArr 1782 cf24EllArrs w) (wordIn 5 ellPerm w) :=
  rep_wordArr (by rw [size_cf24EllArrs]) (fun _ hi => rep_ellArr hi)
    (fun _ hi => isInvA_of_allPermsOK perm_facts.2.1 (by rw [size_cf24EllArrs]; exact hi)) hw

theorem wordIn_ell_mem (w : List ℤ) : wordIn 5 ellPerm w ∈ J0 :=
  wordIn_mem (fun i hi => Subgroup.subset_closure (k := Set.range fun j : Fin 5 => ellPerm j)
    ⟨⟨i, hi⟩, rfl⟩) w

theorem rep_cf24X :
    Rep 1782 cf24XArr cf24XPerm :=
  Sporadic.Recognition.SuzMultiplier.rep_suzWord Certificates.certificate15030
    perm_facts.2.2.1

theorem rep_cf24Y :
    Rep 1782 cf24YArr cf24YPerm :=
  Sporadic.Recognition.SuzMultiplier.rep_suzWord Certificates.certificate15030
    perm_facts.2.2.2.1

theorem cf24XPerm_mem_J0 :
    cf24XPerm ∈ J0 := by
  rw [eq_of_eqA rep_cf24X (rep_ellWord perm_facts.2.2.2.2.1) perm_facts.2.2.2.2.2.2.1]
  exact wordIn_ell_mem _

theorem cf24YPerm_mem_J0 :
    cf24YPerm ∈ J0 := by
  rw [eq_of_eqA rep_cf24Y (rep_ellWord perm_facts.2.2.2.2.2.1) perm_facts.2.2.2.2.2.2.2.1]
  exact wordIn_ell_mem _

theorem cf24_comm :
    cf24XPerm * cf24YPerm = cf24YPerm * cf24XPerm :=
  eq_of_eqA (rep_compA rep_cf24X rep_cf24Y) (rep_compA rep_cf24Y rep_cf24X)
    perm_facts.2.2.2.2.2.2.2.2.1

end CFSG.ComponentClassification.GSThmB.CF24
