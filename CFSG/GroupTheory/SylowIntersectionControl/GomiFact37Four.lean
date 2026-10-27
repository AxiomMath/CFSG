module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact37Common
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact37CSPAlt
public import CFSG.CGT.PushingUpLit.BHS6.FaithfulAlt
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.StabSubBasics

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (fixV commV IsElemAbelian2 ffJ IsFFStarOffender IsSylowIn centSub stabSub
  FFModel commV_apply_mem_of_mem autSub mem_autSub autSub_mono commSub isPGroup_autSub
  card_autSub_mul map_subtype_fixV_autSub commSub_eq_map_commV resHom ker_resHom
  mem_fixV mem_fixV_zpowers_iff_apply)
open CFSG.Quasithin.G6 (coreMod coreAct)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

private theorem gomiFour_index_fixV_swap_le_two {n : ℕ} {t : Equiv.Perm (Fin n)} (ht : t.IsSwap) :
    (fixV ((Subgroup.zpowers t).map (coreAct n))).index ≤ 2 := by
  rw [Subgroup.zpowers_eq_closure]
  set C := fixV ((Subgroup.closure ({t} : Set (Equiv.Perm (Fin n)))).map (coreAct n)) with hC
  have hcard := card_le_two_pow_mul_card_fixV ({t} : Set (Equiv.Perm (Fin n)))
    (by simpa using ht)
  have htc : Nat.card ({t} : Set (Equiv.Perm (Fin n))) = 1 := by
    rw [Nat.card_eq_fintype_card]
    simp
  rw [htc, pow_one, ← hC] at hcard
  have hmul := Subgroup.card_mul_index C
  have hle : Nat.card C * C.index ≤ Nat.card C * 2 := by
    calc Nat.card C * C.index = Nat.card ↥(coreMod n) := hmul
      _ ≤ 2 * Nat.card C := hcard
      _ = Nat.card C * 2 := by rw [mul_comm]
  exact Nat.le_of_mul_le_mul_left hle Nat.card_pos

variable {W : Type} [CommGroup W] [Finite W]

private theorem gomiFour_normal_of_isAlt {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hsn : (L.subgroupOf Y).IsSubnormal) {n : ℕ} (h5 : 5 ≤ n)
    (hL : IsAlt ↥L n) (hC : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥) :
    (L.subgroupOf Y).Normal := by
  obtain ⟨e⟩ := hL
  have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using h5)
  have hs : IsSimpleGroup ↥(L.subgroupOf Y) :=
    MulEquiv.isSimpleGroup ((Subgroup.subgroupOfEquivOfLe hLY).trans e)
  refine normal_of_isSubnormal_of_centralizer_eq_bot hs ?_ hsn
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hyC : (y : MulAut W) ∈ Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) := by
    refine ⟨y.2, fun l hl => ?_⟩
    have h := hy ⟨l, hLY hl⟩ (Subgroup.mem_subgroupOf.mpr hl)
    exact congrArg Subtype.val h
  rw [hC, Subgroup.mem_bot] at hyC
  exact Subtype.ext hyC

private def gomiFourGamEquiv (n : ℕ) :
    (FFModel.altDn n).Gam ≃* alternatingGroup (Fin n) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def gomiFourSecEquiv (n : ℕ) :
    (FFModel.altDn n).sec ≃* coreMod n where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem gomiFourSecEquiv_act (n : ℕ) (σ : (FFModel.altDn n).Gam)
    (x : ↥(FFModel.altDn n).sec)
    (hx : (FFModel.altDn n).act σ ((x : (FFModel.altDn n).sec) : (FFModel.altDn n).Amb) ∈
      (FFModel.altDn n).sec) :
    gomiFourSecEquiv n
        ⟨(FFModel.altDn n).act σ ((x : (FFModel.altDn n).sec) : (FFModel.altDn n).Amb), hx⟩ =
      coreAct n ((gomiFourGamEquiv n σ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))
        (gomiFourSecEquiv n x) := rfl

omit [Finite W] in
private theorem gomiFour_coreData {H : Subgroup (MulAut W)} {U Z : Subgroup W} {n : ℕ}
    (hn : Odd n) (h5 : 5 ≤ n) (hH : H ≠ ⊥)
    (h : (FFModel.altDn n).Realizes H U Z) :
    ∃ (θ : ↥H ≃* alternatingGroup (Fin n)) (β : ↥U →* coreMod n),
      Function.Surjective β ∧ β.ker = Z.subgroupOf U ∧
        ∀ (x : ↥H) (u : ↥U) (hu : (x : MulAut W) (u : W) ∈ U),
          β ⟨(x : MulAut W) (u : W), hu⟩ = coreAct n (θ x) (β u) := by
  obtain ⟨θD, βD, hβs, hβk, hβe⟩ := altDn_realizes_data hn h5 hH h
  let θ : ↥H ≃* alternatingGroup (Fin n) := θD.trans (gomiFourGamEquiv n)
  let β : ↥U →* coreMod n := (gomiFourSecEquiv n).toMonoidHom.comp βD
  have hβs' : Function.Surjective β := by
    intro y
    obtain ⟨u, hu⟩ := hβs ((gomiFourSecEquiv n).symm y)
    refine ⟨u, ?_⟩
    show gomiFourSecEquiv n (βD u) = y
    rw [hu]
    exact (gomiFourSecEquiv n).apply_symm_apply y
  have hβk' : β.ker = Z.subgroupOf U := by
    ext u
    change gomiFourSecEquiv n (βD u) = 1 ↔ u ∈ Z.subgroupOf U
    constructor
    · intro h
      have h1 : βD u = 1 := (gomiFourSecEquiv n).injective (by rw [h, map_one])
      have h2 : u ∈ βD.ker := MonoidHom.mem_ker.mpr h1
      rwa [hβk] at h2
    · intro h
      have h1 : u ∈ βD.ker := by rwa [hβk]
      have h2 : βD u = 1 := MonoidHom.mem_ker.mp h1
      exact (gomiFourSecEquiv n).injective (by rw [h2, map_one])
  refine ⟨θ, β, hβs', hβk', ?_⟩
  intro x u hu
  have h' := hβe x u hu
  have hx : (FFModel.altDn n).act (θD x) (βD u) ∈ (FFModel.altDn n).sec :=
    h' ▸ (βD ⟨(x : MulAut W) (u : W), hu⟩).2
  show gomiFourSecEquiv n (βD ⟨(x : MulAut W) (u : W), hu⟩) =
    coreAct n (θ x) (gomiFourSecEquiv n (βD u))
  have hsub : βD ⟨(x : MulAut W) (u : W), hu⟩ =
      ⟨(FFModel.altDn n).act (θD x) (βD u), hx⟩ := Subtype.ext h'
  rw [hsub]
  simpa [θ, MulEquiv.trans_apply] using gomiFourSecEquiv_act n (θD x) (βD u) hx

omit [Finite W] in
private theorem gomiFour_eq_one_of_fix_commV {L : Subgroup (MulAut W)} {n : ℕ} (hn : Odd n)
    (h5 : 5 ≤ n) (hH : L ≠ ⊥)
    (hnat : (FFModel.altDn n).Realizes L (commV L) (gomiWXKer L))
    {l : MulAut W} (hl : l ∈ L) (hfix : ∀ u ∈ commV L, l u = u) : l = 1 := by
  obtain ⟨θ, β, hβs, -, hβe⟩ := gomiFour_coreData hn h5 hH hnat
  have h3 : 3 ≤ n := by omega
  have hcore : coreAct n ((θ ⟨l, hl⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = 1 := by
    refine MulEquiv.ext fun d => ?_
    obtain ⟨u, rfl⟩ := hβs d
    have hu : l (u : W) ∈ commV L := commV_apply_mem_of_mem hl u.2
    have hlu : l (u : W) = (u : W) := hfix _ u.2
    have hlu' : (⟨l (u : W), hu⟩ : ↥(commV L)) = u := Subtype.ext hlu
    have hmain : coreAct n ((θ ⟨l, hl⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))
        (β u) = β u := by
      rw [← hβe ⟨l, hl⟩ u hu, hlu']
    simpa using hmain
  have hθ1 : θ ⟨l, hl⟩ = 1 := by
    apply Subtype.ext
    exact coreAct_injective h3 (hcore.trans (map_one (coreAct n)).symm)
  have h1 : (⟨l, hl⟩ : ↥L) = 1 := θ.injective (hθ1.trans (map_one θ).symm)
  exact congrArg Subtype.val h1

omit [Finite W] in
private theorem gomiFour_commSub_commV {L : Subgroup (MulAut W)} {n : ℕ} (h5 : 5 ≤ n)
    (θ : ↥L ≃* alternatingGroup (Fin n)) : commSub (commV L) L = commV L := by
  have hEq : CFSG.Open.IsQuasisimple ↥L := isQuasisimple_of_mulEquiv' θ.symm
    (isQuasisimple_alternatingGroup h5)
  have hperf : ⁅L, L⁆ = L := by
    have htop : (⊤ : Subgroup ↥L).map L.subtype = L := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥L)) (H₂ := ⊤) L.subtype
    rw [htop] at h
    rw [← h, ← commutator_def, hEq.1, htop]
  exact CFSG.Quasithin.B15P4.commSub_commV_of_perfect hperf

omit [Finite W] in
private theorem gomiFour_exists_restriction {L : Subgroup (MulAut W)} {n : ℕ} (hn : Odd n)
    (h5 : 5 ≤ n) (hH : L ≠ ⊥)
    (hnat : (FFModel.altDn n).Realizes L (commV L) (gomiWXKer L)) :
    ∃ φE : ↥L ≃* ↥(autSub L (commV L)),
      (∀ (x : ↥L) (u : ↥(commV L)),
        ((((φE x : ↥(autSub L (commV L))) : MulAut ↥(commV L)) u : ↥(commV L)) : W) =
          (x : MulAut W) (u : W)) ∧
      L ⊓ centSub (commV L) = ⊥ := by
  have hEst : L ≤ stabSub (commV L) :=
    Subgroup.le_normalizer.trans (normalizer_commV_le_stabSub L)
  have hEcen : L ⊓ centSub (commV L) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun l hl => ?_
    exact gomiFour_eq_one_of_fix_commV hn h5 hH hnat
      (Subgroup.mem_inf.mp hl).1 (Subgroup.mem_inf.mp hl).2
  obtain ⟨φE, hφE⟩ := exists_mulEquiv_autSub hEst hEcen
  exact ⟨φE, hφE, hEcen⟩

private noncomputable def gomiFourAltNatData {L : Subgroup (MulAut W)} {n : ℕ} (hn : Odd n)
    (h5 : 5 ≤ n) (hH : L ≠ ⊥)
    (hnat : (FFModel.altDn n).Realizes L (commV L) (gomiWXKer L))
    (θ : ↥L ≃* alternatingGroup (Fin n))
    (β : ↥(commV L) →* coreMod n) (hβs : Function.Surjective β)
    (hβk : β.ker = (commV L ⊓ fixV L).subgroupOf (commV L))
    (hβe : ∀ (x : ↥L) (p : ↥(commV L)) (hp : (x : MulAut W) p ∈ commV L),
      β ⟨(x : MulAut W) p, hp⟩ = coreAct n (θ x) (β p)) :
    AltNatData (autSub L (commV L)) n := by
  classical
  let φE : ↥L ≃* ↥(autSub L (commV L)) :=
    Classical.choose (gomiFour_exists_restriction hn h5 hH hnat)
  have hφE : ∀ (x : ↥L) (u : ↥(commV L)),
      ((((φE x : ↥(autSub L (commV L))) : MulAut ↥(commV L)) u : ↥(commV L)) : W) =
        (x : MulAut W) (u : W) :=
    (Classical.choose_spec (gomiFour_exists_restriction hn h5 hH hnat)).1
  have hcomm : commSub (commV L) L = commV L := gomiFour_commSub_commV h5 θ
  have htopW : (⊤ : Subgroup ↥(commV L)).map (commV L).subtype = commV L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hEst : L ≤ stabSub (commV L) :=
    Subgroup.le_normalizer.trans (normalizer_commV_le_stabSub L)
  exact { θ := φE.symm.trans θ
          β := β
          surj := hβs
          ker_fix := fun w hw g hg => by
            obtain ⟨e, he⟩ := φE.surjective ⟨g, hg⟩
            have h1 : (w : W) ∈ commV L ⊓ fixV L := by
              have h2 : w ∈ β.ker := hw
              rw [hβk, Subgroup.mem_subgroupOf] at h2
              exact h2
            have h2 : (e : MulAut W) w = w := h1.2 e e.2
            apply Subtype.ext
            have h3 := hφE e w
            rw [he] at h3
            rw [h3]
            exact h2
          equivar := fun e' w => by
            obtain ⟨e, rfl⟩ := φE.surjective e'
            have hp : (e : MulAut W) w ∈ commV L := by
              have h2 := (((φE e : ↥(autSub L (commV L))) : MulAut ↥(commV L)) w).2
              rw [hφE e w] at h2
              exact h2
            have h3 : (((φE e : ↥(autSub L (commV L))) : MulAut ↥(commV L)) w) =
                ⟨(e : MulAut W) w, hp⟩ := Subtype.ext (hφE e w)
            rw [h3, hβe e w hp]
            simp
          comm_top := by
            refine Subgroup.map_injective (commV L).subtype_injective ?_
            rw [← commSub_eq_map_commV hEst, hcomm, htopW] }

omit [Finite W] in
private theorem gomiFour_mem_commV_of_normal {Y L : Subgroup (MulAut W)}
    (hLn : (L.subgroupOf Y).Normal) (hLY : L ≤ Y) {y : MulAut W} (hy : y ∈ Y)
    {u : W} (hu : u ∈ commV L) : y u ∈ commV L := by
  have hconj : ∀ x ∈ L, y * x * y⁻¹ ∈ L := by
    intro x hx
    have h1 := hLn.conj_mem ⟨x, hLY hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨y, hy⟩
    simpa using Subgroup.mem_subgroupOf.mp h1
  have hle : commV L ≤ (commV L).comap (y : MulAut W).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    show y (x v * v⁻¹) ∈ commV L
    refine Subgroup.subset_closure ⟨y * x * y⁻¹, hconj x hx, y v, ?_⟩
    simp [MulAut.mul_apply]
  exact hle hu

omit [Finite W] in
private theorem gomiFour_inf_centSub_eq_bot {Y L : Subgroup (MulAut W)} {n : ℕ}
    (hn : Odd n) (h5 : 5 ≤ n) (hH : L ≠ ⊥)
    (hnat : (FFModel.altDn n).Realizes L (commV L) (gomiWXKer L))
    (hLn : (L.subgroupOf Y).Normal) (hLY : L ≤ Y)
    (hC : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥) :
    Y ⊓ centSub (commV L) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
  have hyY : (y : MulAut W) ∈ Y := (Subgroup.mem_inf.mp hy).1
  have hyD : ∀ u ∈ commV L, (y : MulAut W) u = u := fun u hu =>
    (Subgroup.mem_inf.mp hy).2 u hu
  have hyinvD : ∀ u ∈ commV L, (y : MulAut W)⁻¹ u = u := by
    intro u hu
    have h1 := hyD _ (gomiFour_mem_commV_of_normal hLn hLY (Y.inv_mem hyY) hu)
    have h2 : (y : MulAut W) ((y : MulAut W)⁻¹ u) = u := by simp
    rw [h2] at h1
    exact h1.symm
  have hyC : (y : MulAut W) ∈ Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) := by
    refine ⟨hyY, fun l hl => ?_⟩
    have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hLn
    have hconj : (y : MulAut W) * l * (y : MulAut W)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hYN hyY) l).mp hl
    have hcomm : (y : MulAut W) * l * (y : MulAut W)⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem hconj (L.inv_mem hl)
    have hfix : ∀ u ∈ commV L,
        ((y : MulAut W) * l * (y : MulAut W)⁻¹ * l⁻¹) u = u := by
      intro u hu
      have h1 : l⁻¹ u ∈ commV L := commV_apply_mem_of_mem (L.inv_mem hl) hu
      have h2 : (y : MulAut W)⁻¹ (l⁻¹ u) = l⁻¹ u := hyinvD _ h1
      have h3 : l (l⁻¹ u) = u := by simp
      simp only [MulAut.mul_apply]
      rw [h2, h3, hyD _ hu]
    have h1 : (y : MulAut W) * l * (y : MulAut W)⁻¹ * l⁻¹ = 1 :=
      gomiFour_eq_one_of_fix_commV hn h5 hH hnat hcomm hfix
    have h2 : (y : MulAut W) * l * (y : MulAut W)⁻¹ = l := mul_inv_eq_one.mp h1
    have h3 : (y : MulAut W) * l = l * (y : MulAut W) := by
      calc (y : MulAut W) * l = ((y : MulAut W) * l * (y : MulAut W)⁻¹) * y := by group
        _ = l * (y : MulAut W) := by rw [h2]
    exact h3.symm
  rw [hC, Subgroup.mem_bot] at hyC
  exact hyC

omit [Finite W] in
private theorem gomiFour_ne_bot_of_isAlt {L : Subgroup (MulAut W)} {n : ℕ} (h3 : 3 ≤ n)
    (hL : IsAlt ↥L n) : L ≠ ⊥ := by
  obtain ⟨e⟩ := hL
  have hnt : Nontrivial (alternatingGroup (Fin n)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simpa using h3)
  obtain ⟨a, b, hab⟩ := @exists_pair_ne (alternatingGroup (Fin n)) hnt
  intro hbot
  have hsub : Subsingleton ↥L := by rw [hbot]; infer_instance
  exact hab (e.symm.injective (hsub.elim (e.symm a) (e.symm b)))

omit [Finite W] in
private theorem gomiFour_subgroupOf_iSup {ι : Type*} {f : ι → Subgroup (MulAut W)}
    {H : Subgroup (MulAut W)} (hf : ∀ i, f i ≤ H) :
    (⨆ i, f i).subgroupOf H = ⨆ i, (f i).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (iSup_le hf), Subgroup.map_iSup]
  simp_rw [Subgroup.map_subgroupOf_eq_of_le (hf _)]

omit [Finite W] in
private theorem gomiFour_iSup_range_autSub (S L : Subgroup (MulAut W)) :
    (⨆ A' ∈ Set.range (fun A : Pset S => autSub (A : Subgroup (MulAut W)) (commV L)), A') =
      ⨆ A : Pset S, autSub (A : Subgroup (MulAut W)) (commV L) := by
  rw [iSup_range]

omit [Finite W] in
private theorem gomiFour_autSub_ffJ {S L : Subgroup (MulAut W)}
    (hSst : ∀ A : Pset S, (A : Subgroup (MulAut W)) ≤ stabSub (commV L)) :
    (⨆ A : Pset S, autSub (A : Subgroup (MulAut W)) (commV L)) =
      autSub (ffJ S) (commV L) := by
  have hffJ : ffJ S = ⨆ A : Pset S, (A : Subgroup (MulAut W)) := by
    rw [ffJ]
    exact (iSup_subtype (p := fun A => IsFFStarOffender S A)
      (f := fun A => (A : Subgroup (MulAut W)))).symm
  rw [hffJ, autSub, gomiFour_subgroupOf_iSup (fun A => hSst A), Subgroup.map_iSup]
  rfl

omit [Finite W] in
private theorem gomiFour_not_le_centSub_commV {Y S L : Subgroup (MulAut W)} {n : ℕ}
    (hn : Odd n) (h5 : 5 ≤ n) (hH : L ≠ ⊥)
    (hnat : (FFModel.altDn n).Realizes L (commV L) (gomiWXKer L))
    (hLn : (L.subgroupOf Y).Normal) (hLY : L ≤ Y) (hSY : S ≤ Y)
    (hC : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥)
    {A : Subgroup (MulAut W)} (hA : IsFFStarOffender S A) :
    ¬ A ≤ centSub (commV L) := by
  intro hAc
  apply hA.2.1
  rw [eq_bot_iff]
  intro a ha
  have haS : a ∈ S := hA.1 ha
  have haY : a ∈ Y := hSY haS
  have hafix : ∀ u ∈ commV L, a u = u := fun u hu => hAc ha u hu
  have hainv : ∀ u ∈ commV L, a⁻¹ u = u := by
    intro u hu
    have h1 := hafix _ (gomiFour_mem_commV_of_normal hLn hLY (Y.inv_mem haY) hu)
    have h2 : a (a⁻¹ u) = u := by simp
    rw [h2] at h1
    exact h1.symm
  have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hLn
  have hcomm : a ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
    intro l hl
    have hconj : a * l * a⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hYN haY) l).mp hl
    have hc : a * l * a⁻¹ * l⁻¹ ∈ L := L.mul_mem hconj (L.inv_mem hl)
    have hfix : ∀ u ∈ commV L, (a * l * a⁻¹ * l⁻¹) u = u := by
      intro u hu
      have h1 : l⁻¹ u ∈ commV L := commV_apply_mem_of_mem (L.inv_mem hl) hu
      have h3 : l (l⁻¹ u) = u := by simp
      simp only [MulAut.mul_apply]
      rw [hainv _ h1, h3, hafix _ hu]
    have h1 : a * l * a⁻¹ * l⁻¹ = 1 :=
      gomiFour_eq_one_of_fix_commV hn h5 hH hnat hc hfix
    have h2 : a * l * a⁻¹ = l := mul_inv_eq_one.mp h1
    have h3 : a * l = l * a := by
      calc a * l = (a * l * a⁻¹) * a := by group
        _ = l * a := by rw [h2]
    exact h3.symm
  have hCS : S ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxY : x ∈ Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) :=
      ⟨hSY (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩
    rw [hC, Subgroup.mem_bot] at hxY
    rwa [Subgroup.mem_bot]
  have hmem : a ∈ S ⊓ Subgroup.centralizer (L : Set (MulAut W)) := ⟨haS, hcomm⟩
  rwa [hCS, Subgroup.mem_bot] at hmem

private theorem gomiFour_family_mem {Y S L : Subgroup (MulAut W)}
    (hSY : S ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hLY : L ≤ Y)
    (hnt : ∀ A ∈ Pset S, ¬ A ≤ centSub (commV L))
    {A : Subgroup (MulAut W)} (hA : A ∈ Pset S) :
    autSub A (commV L) ≤ autSub S (commV L) ∧ IsElemAbelian2 (autSub A (commV L)) ∧
      autSub A (commV L) ≠ ⊥ ∧
      Nat.card ↥(commV L) ≤ Nat.card (autSub A (commV L)) *
        Nat.card (fixV (autSub A (commV L))) := by
  have hAW : ∀ a ∈ A, ∀ w ∈ commV L, a w ∈ commV L := fun a ha w hw =>
    gomiFour_mem_commV_of_normal hLn hLY (hSY (hA.1 ha)) hw
  have hoff := CFSG.Quasithin.B1Red.isFFStarOffender_autSub hA hAW (hnt A hA)
  refine ⟨autSub_mono hA.1 _, isElemAbelian2_autSub hA.2.2.1, ?_, ?_⟩
  · intro hbot
    apply hnt A hA
    intro a ha
    have haY : a ∈ Y := hSY (hA.1 ha)
    have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hLn
    have haz : a ∈ stabSub (commV L) := normalizer_commV_le_stabSub L (hYN haY)
    have h1 : resHom (commV L) ⟨a, haz⟩ ∈ autSub A (commV L) :=
      mem_autSub.mpr ⟨⟨a, haz⟩, ha, rfl⟩
    rw [hbot] at h1
    have h2 : (⟨a, haz⟩ : stabSub (commV L)) ∈ (resHom (commV L)).ker := h1
    rw [ker_resHom, Subgroup.mem_subgroupOf] at h2
    exact h2
  · have h := (offender_iff.mp hoff).2.card_le (bot_le :
        (⊥ : Subgroup (MulAut ↥(commV L))) ≤ autSub A (commV L))
    rwa [CFSG.Quasithin.B1.card_bot_mul_card_fixV] at h

private theorem gomiFour_family_setup {Y S L : Subgroup (MulAut W)} {n : ℕ}
    (hn : Odd n) (h5 : 5 ≤ n) (hH : L ≠ ⊥)
    (hnat : (FFModel.altDn n).Realizes L (commV L) (gomiWXKer L))
    (hLn : (L.subgroupOf Y).Normal) (hLY : L ≤ Y) (hSY : S ≤ Y)
    (hS2 : IsPGroup 2 S)
    (hC : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥)
    (hPS : (Pset S).Nonempty)
    (𝒜 : Set (Subgroup (MulAut ↥(commV L))))
    (h𝒜 : 𝒜 = Set.range (fun A : Pset S => autSub (A : Subgroup (MulAut W)) (commV L))) :
    IsPGroup 2 (autSub S (commV L)) ∧
      autSub S (commV L) ≤
        Subgroup.normalizer (autSub L (commV L) : Set (MulAut ↥(commV L))) ∧
      𝒜.Nonempty ∧
      (∀ A' ∈ 𝒜, A' ≤ autSub S (commV L) ∧ IsElemAbelian2 A' ∧ A' ≠ ⊥ ∧
        Nat.card ↥(commV L) ≤ Nat.card A' * Nat.card (fixV A')) ∧
      (∀ A : Pset S, (A : Subgroup (MulAut W)) ≤ stabSub (commV L)) := by
  have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hLn
  have hSN : S ≤ Subgroup.normalizer (L : Set (MulAut W)) := hSY.trans hYN
  have hSst : ∀ A : Pset S, (A : Subgroup (MulAut W)) ≤ stabSub (commV L) := fun A =>
    A.2.1.trans (hSN.trans (normalizer_commV_le_stabSub L))
  have hnt : ∀ A ∈ Pset S, ¬ A ≤ centSub (commV L) := fun A hA =>
    gomiFour_not_le_centSub_commV hn h5 hH hnat hLn hLY hSY hC hA
  have hQ : IsPGroup 2 (autSub S (commV L)) := isPGroup_autSub hS2
  have hQN : autSub S (commV L) ≤
      Subgroup.normalizer (autSub L (commV L) : Set (MulAut ↥(commV L))) :=
    autSub_le_normalizer hSN
  have hne : 𝒜.Nonempty := by
    obtain ⟨A₀, hA₀⟩ := hPS
    rw [h𝒜]
    exact ⟨_, ⟨⟨A₀, hA₀⟩, rfl⟩⟩
  refine ⟨hQ, hQN, hne, ?_, hSst⟩
  rw [h𝒜]
  rintro A' ⟨⟨A, hA⟩, rfl⟩
  exact gomiFour_family_mem hSY hLn hLY hnt hA

private abbrev gomiFourN (L : Subgroup (MulAut W)) : Subgroup (MulAut ↥(commV L)) :=
  Subgroup.normalizer (autSub L (commV L) : Set (MulAut ↥(commV L)))

private theorem gomiFour_altFamily {Y S L : Subgroup (MulAut W)} {n : ℕ}
    (hW : ∀ w : W, w ^ 2 = 1) (hn : Odd n) (h5 : 5 ≤ n) (hH : L ≠ ⊥)
    (hnat : (FFModel.altDn n).Realizes L (commV L) (gomiWXKer L))
    (hLn : (L.subgroupOf Y).Normal) (hLY : L ≤ Y) (hSY : S ≤ Y) (hS2 : IsPGroup 2 S)
    (hC : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥)
    (hPS : (Pset S).Nonempty) (D : AltNatData (autSub L (commV L)) n) :
    ∃ T : Set (Equiv.Perm (Fin n)), (∀ t ∈ T, t.IsSwap) ∧
      (∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) ∧ T.Nonempty ∧
      ((autSub (ffJ S) (commV L)).subgroupOf (gomiFourN L)).map (D.psi hn h5) =
        Subgroup.closure T ∧
      Function.Bijective (D.psi hn h5) ∧ Function.Bijective D.β ∧
      autSub Y (commV L) = gomiFourN L ∧
      ∀ Q'' : Subgroup (MulAut ↥(commV L)), IsPGroup 2 Q'' → Q'' ≤ gomiFourN L →
        fixV (autSub (ffJ S) (commV L)) ≤ fixV Q'' → Q'' ≤ autSub (ffJ S) (commV L) := by
  classical
  have hW' : ∀ w : ↥(commV L), w ^ 2 = 1 := fun w => Subtype.ext (by
    simpa using hW (w : W))
  set 𝒜 : Set (Subgroup (MulAut ↥(commV L))) :=
    Set.range (fun A : Pset S => autSub (A : Subgroup (MulAut W)) (commV L)) with h𝒜
  obtain ⟨hQ, hQN, hne, hfam, hSst⟩ :=
    gomiFour_family_setup hn h5 hH hnat hLn hLY hSY hS2 hC hPS 𝒜 h𝒜
  have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hLn
  obtain ⟨A₀, hA₀⟩ := hPS
  obtain ⟨-, hβbij, hψbij, hsup, ⟨k, hk1, -, hswap, hcard, -⟩, hQmax⟩ :=
    CFSG.CGT.PushingUpLit.BHS6.alt_family hW' hn h5 D hQ hQN hne hfam
  obtain ⟨T, hTsw, hTcomm, hTcard, hTeq⟩ := hswap
  have hJ : (⨆ A' ∈ 𝒜, A') = autSub (ffJ S) (commV L) := by
    rw [h𝒜, gomiFour_iSup_range_autSub]
    exact gomiFour_autSub_ffJ hSst
  have hA₀𝒜 : autSub A₀ (commV L) ∈ 𝒜 := ⟨⟨A₀, hA₀⟩, rfl⟩
  have hsupA : autSub L (commV L) ⊔ autSub A₀ (commV L) =
      Subgroup.normalizer (autSub L (commV L) : Set (MulAut ↥(commV L))) :=
    hsup _ hA₀𝒜
  have hNle : autSub Y (commV L) ≤ Subgroup.normalizer
      (autSub L (commV L) : Set (MulAut ↥(commV L))) := autSub_le_normalizer hYN
  have hNge : Subgroup.normalizer (autSub L (commV L) : Set (MulAut ↥(commV L))) ≤
      autSub Y (commV L) := by
    rw [← hsupA]
    exact sup_le (autSub_mono hLY _) (autSub_mono (hA₀.1.trans hSY) _)
  refine ⟨T, hTsw, hTcomm, ?_, ?_, hψbij, hβbij, le_antisymm hNle hNge, ?_⟩
  · by_contra hT
    rw [Set.not_nonempty_iff_eq_empty] at hT
    rw [hT, Set.ncard_empty] at hTcard
    omega
  · rw [← hJ]
    exact hTeq
  · intro Q'' h1 h2 h3
    have h4 := hQmax Q'' h1 h2 (by rwa [hJ])
    rwa [hJ] at h4

private noncomputable def gomiFourPhi {Y L : Subgroup (MulAut W)} {n : ℕ}
    (hn : Odd n) (h5 : 5 ≤ n) (D : AltNatData (autSub L (commV L)) n)
    (hYst : Y ≤ stabSub (commV L)) (hYcen : Y ⊓ centSub (commV L) = ⊥)
    (hψbij : Function.Bijective (D.psi hn h5))
    (hYeqN : autSub Y (commV L) =
      Subgroup.normalizer (autSub L (commV L) : Set (MulAut ↥(commV L)))) :
    ↥Y ≃* Equiv.Perm (Fin n) :=
  let eY : ↥Y ≃* ↥(autSub Y (commV L)) :=
    Classical.choose (exists_mulEquiv_autSub hYst hYcen)
  let eN : ↥(autSub Y (commV L)) ≃*
      ↥(Subgroup.normalizer (autSub L (commV L) : Set (MulAut ↥(commV L)))) :=
    MulEquiv.subgroupCongr hYeqN
  let ψN : ↥(Subgroup.normalizer (autSub L (commV L) : Set (MulAut ↥(commV L)))) ≃*
      Equiv.Perm (Fin n) := MulEquiv.ofBijective (D.psi hn h5) hψbij
  eY.trans (eN.trans ψN)

omit [Finite W] in
private theorem gomiFourPhi_action {Y L : Subgroup (MulAut W)} {n : ℕ}
    (hn : Odd n) (h5 : 5 ≤ n) (D : AltNatData (autSub L (commV L)) n)
    (hYst : Y ≤ stabSub (commV L)) (hYcen : Y ⊓ centSub (commV L) = ⊥)
    (hψbij : Function.Bijective (D.psi hn h5))
    (hYeqN : autSub Y (commV L) =
      Subgroup.normalizer (autSub L (commV L) : Set (MulAut ↥(commV L))))
    (y : ↥Y) (u : ↥(commV L)) (hu : (y : MulAut W) u ∈ commV L) :
    D.β ⟨(y : MulAut W) u, hu⟩ =
      coreAct n (gomiFourPhi hn h5 D hYst hYcen hψbij hYeqN y) (D.β u) := by
  classical
  let eY : ↥Y ≃* ↥(autSub Y (commV L)) :=
    Classical.choose (exists_mulEquiv_autSub hYst hYcen)
  let eN : ↥(autSub Y (commV L)) ≃*
      ↥(Subgroup.normalizer (autSub L (commV L) : Set (MulAut ↥(commV L)))) :=
    MulEquiv.subgroupCongr hYeqN
  have hφE := Classical.choose_spec (exists_mulEquiv_autSub hYst hYcen)
  have hx : ((eN (eY y) : ↥(Subgroup.normalizer (autSub L (commV L) :
        Set (MulAut ↥(commV L))))) : MulAut ↥(commV L)) =
      ((eY y : ↥(autSub Y (commV L))) : MulAut ↥(commV L)) := rfl
  have h1 : (⟨(y : MulAut W) u, hu⟩ : ↥(commV L)) =
      ((eY y : ↥(autSub Y (commV L))) : MulAut ↥(commV L)) u := by
    exact Subtype.ext (hφE y u).symm
  have h2 : D.β ⟨(y : MulAut W) u, hu⟩ =
      D.β (((eN (eY y) : ↥(Subgroup.normalizer (autSub L (commV L) :
        Set (MulAut ↥(commV L))))) : MulAut ↥(commV L)) u) := by rw [hx, h1]
  rw [h2, D.psi_spec hn h5]
  rfl

omit [Finite W] in
private theorem gomiFour_fixV_map_eq {Y L : Subgroup (MulAut W)} {n : ℕ}
    (hLn : (L.subgroupOf Y).Normal) (hLY : L ≤ Y)
    (D : AltNatData (autSub L (commV L)) n) (φ : ↥Y ≃* Equiv.Perm (Fin n))
    (hφ : ∀ (y : ↥Y) (u : ↥(commV L)) (hu : (y : MulAut W) u ∈ commV L),
      D.β ⟨(y : MulAut W) u, hu⟩ = coreAct n (φ y) (D.β u))
    (hβbij : Function.Bijective D.β) {t : MulAut W} (htY : t ∈ Y) :
    ((fixV (Subgroup.zpowers t)).subgroupOf (commV L)).map
        (MulEquiv.ofBijective D.β hβbij).toMonoidHom =
      fixV ((Subgroup.zpowers (φ ⟨t, htY⟩)).map (coreAct n)) := by
  classical
  let βe : ↥(commV L) ≃* coreMod n := MulEquiv.ofBijective D.β hβbij
  ext d
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : (t : MulAut W) (u : W) = (u : W) :=
      (mem_fixV_zpowers_iff_apply).mp (Subgroup.mem_subgroupOf.mp hu)
    have hstab : (t : MulAut W) (u : W) ∈ commV L :=
      gomiFour_mem_commV_of_normal hLn hLY htY u.2
    have h1 := hφ ⟨t, htY⟩ u hstab
    have h2 : D.β ⟨(t : MulAut W) (u : W), hstab⟩ = D.β u :=
      congrArg D.β (Subtype.ext hu')
    have hc : coreAct n (φ ⟨t, htY⟩) (D.β u) = D.β u := (h2.symm.trans h1).symm
    refine (mem_fixV).mpr ?_
    rintro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    have hle : Subgroup.zpowers (φ ⟨t, htY⟩) ≤
        (MulAction.stabilizer (MulAut ↥(coreMod n)) (D.β u)).comap (coreAct n) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
      exact hc
    have hx' := hle hx
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hx'
    exact hx'
  · intro hd
    have hmem : coreAct n (φ ⟨t, htY⟩) ∈
        (Subgroup.zpowers (φ ⟨t, htY⟩)).map (coreAct n) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers _)
    have hc : coreAct n (φ ⟨t, htY⟩) d = d := hd _ hmem
    set u : ↥(commV L) := βe.symm d with hu_def
    have hβu : D.β u = d := βe.apply_symm_apply d
    have hstab : (t : MulAut W) (u : W) ∈ commV L :=
      gomiFour_mem_commV_of_normal hLn hLY htY u.2
    have h1 : D.β ⟨(t : MulAut W) (u : W), hstab⟩ = D.β u := by
      rw [hφ ⟨t, htY⟩ u hstab, hβu]
      exact hc
    have h2 : (⟨(t : MulAut W) (u : W), hstab⟩ : ↥(commV L)) = u := hβbij.1 h1
    refine ⟨u, Subgroup.mem_subgroupOf.mpr ?_, hβu⟩
    exact (mem_fixV_zpowers_iff_apply).mpr (congrArg Subtype.val h2)

private theorem gomiFour_relIndex_fixV_zpowers_le {Y L : Subgroup (MulAut W)} {n : ℕ}
    (hLn : (L.subgroupOf Y).Normal) (hLY : L ≤ Y)
    (D : AltNatData (autSub L (commV L)) n) (φ : ↥Y ≃* Equiv.Perm (Fin n))
    (hφ : ∀ (y : ↥Y) (u : ↥(commV L)) (hu : (y : MulAut W) u ∈ commV L),
      D.β ⟨(y : MulAut W) u, hu⟩ = coreAct n (φ y) (D.β u))
    (hβbij : Function.Bijective D.β) {t : MulAut W} (htY : t ∈ Y)
    (hswap : (φ ⟨t, htY⟩).IsSwap) :
    (fixV (Subgroup.zpowers t)).relIndex (commV L) ≤ 2 := by
  classical
  let βe : ↥(commV L) ≃* coreMod n := MulEquiv.ofBijective D.β hβbij
  let H : Subgroup ↥(commV L) := (fixV (Subgroup.zpowers t)).subgroupOf (commV L)
  have hH : H.map βe.toMonoidHom =
      fixV ((Subgroup.zpowers (φ ⟨t, htY⟩)).map (coreAct n)) :=
    gomiFour_fixV_map_eq hLn hLY D φ hφ hβbij htY
  have h3 : (fixV ((Subgroup.zpowers (φ ⟨t, htY⟩)).map (coreAct n))).index ≤ 2 :=
    gomiFour_index_fixV_swap_le_two hswap
  have hHcard : Nat.card H =
      Nat.card (fixV ((Subgroup.zpowers (φ ⟨t, htY⟩)).map (coreAct n))) := by
    rw [← hH]
    exact (Subgroup.card_map_of_injective βe.injective).symm
  have hDg : Nat.card ↥(commV L) = Nat.card ↥(coreMod n) :=
    Nat.card_congr βe.toEquiv
  have hcardH := Subgroup.card_mul_index H
  have hcardK := Subgroup.card_mul_index
    (fixV ((Subgroup.zpowers (φ ⟨t, htY⟩)).map (coreAct n)))
  have hidx : H.index =
      (fixV ((Subgroup.zpowers (φ ⟨t, htY⟩)).map (coreAct n))).index := by
    apply Nat.mul_left_cancel (Nat.card_pos (α := H))
    calc Nat.card H * H.index = Nat.card ↥(commV L) := hcardH
      _ = Nat.card ↥(coreMod n) := hDg
      _ = Nat.card (fixV ((Subgroup.zpowers (φ ⟨t, htY⟩)).map (coreAct n))) *
            (fixV ((Subgroup.zpowers (φ ⟨t, htY⟩)).map (coreAct n))).index := hcardK.symm
      _ = Nat.card H *
            (fixV ((Subgroup.zpowers (φ ⟨t, htY⟩)).map (coreAct n))).index := by
            rw [hHcard]
  show H.index ≤ 2
  rw [hidx]
  exact h3

omit [Finite W] in
private theorem gomiFour_fixV_map_eq' {Y L : Subgroup (MulAut W)} {n : ℕ}
    (hLn : (L.subgroupOf Y).Normal) (hLY : L ≤ Y)
    (D : AltNatData (autSub L (commV L)) n) (φ : ↥Y ≃* Equiv.Perm (Fin n))
    (hφ : ∀ (y : ↥Y) (u : ↥(commV L)) (hu : (y : MulAut W) u ∈ commV L),
      D.β ⟨(y : MulAut W) u, hu⟩ = coreAct n (φ y) (D.β u))
    (hβbij : Function.Bijective D.β) {B : Subgroup (MulAut W)} (hBY : B ≤ Y) :
    ((fixV B).subgroupOf (commV L)).map
        (MulEquiv.ofBijective D.β hβbij).toMonoidHom =
      fixV (((B.subgroupOf Y).map φ.toMonoidHom).map (coreAct n)) := by
  classical
  let βe : ↥(commV L) ≃* coreMod n := MulEquiv.ofBijective D.β hβbij
  ext d
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : ∀ b ∈ B, b (u : W) = (u : W) := Subgroup.mem_subgroupOf.mp hu
    refine (mem_fixV).mpr ?_
    rintro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    have hyB : (y : MulAut W) ∈ B := Subgroup.mem_subgroupOf.mp hy
    have hstab : (y : MulAut W) (u : W) ∈ commV L := by
      rw [hu' _ hyB]; exact u.2
    have h1 := hφ y u hstab
    rw [← hxy]
    change coreAct n (φ y) (D.β u) = D.β u
    rw [← h1]
    congr 1
    exact Subtype.ext (hu' _ hyB)
  · intro hd
    refine ⟨βe.symm d, Subgroup.mem_subgroupOf.mpr ?_, βe.apply_symm_apply d⟩
    intro b hb
    have hstab : (b : MulAut W) (βe.symm d : W) ∈ commV L :=
      gomiFour_mem_commV_of_normal hLn hLY (hBY hb) (βe.symm d).2
    have hbY : (⟨b, hBY hb⟩ : ↥Y) ∈ B.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hb
    have hmem : coreAct n (φ ⟨b, hBY hb⟩) ∈
        ((B.subgroupOf Y).map φ.toMonoidHom).map (coreAct n) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hbY)
    have hfixd : coreAct n (φ ⟨b, hBY hb⟩) d = d := hd _ hmem
    have hβeq : βe ⟨(b : MulAut W) (βe.symm d : W), hstab⟩ = βe (βe.symm d) := by
      change D.β ⟨(b : MulAut W) (βe.symm d : W), hstab⟩ = βe (βe.symm d)
      rw [hφ ⟨b, hBY hb⟩ (βe.symm d) hstab]
      change coreAct n (φ ⟨b, hBY hb⟩) (βe (βe.symm d)) = βe (βe.symm d)
      rw [βe.apply_symm_apply d, hfixd]
    have hU : (⟨(b : MulAut W) (βe.symm d : W), hstab⟩ : ↥(commV L)) = βe.symm d :=
      βe.injective hβeq
    exact congrArg Subtype.val hU

private structure GomiFourSetup (Y S L : Subgroup (MulAut W)) (n : ℕ) where
  hW : ∀ w : W, w ^ 2 = 1
  hn : Odd n
  h5 : 5 ≤ n
  hH : L ≠ ⊥
  hLn : (L.subgroupOf Y).Normal
  hLY : L ≤ Y
  hSY : S ≤ Y
  hS2 : IsPGroup 2 S
  hYst : Y ≤ stabSub (commV L)
  hYcen : Y ⊓ centSub (commV L) = ⊥
  D : AltNatData (autSub L (commV L)) n
  hDψ : Function.Bijective (D.psi hn h5)
  hDβ : Function.Bijective D.β
  φ : ↥Y ≃* Equiv.Perm (Fin n)
  hφ : ∀ (y : ↥Y) (u : ↥(commV L)) (hu : (y : MulAut W) u ∈ commV L),
      D.β ⟨(y : MulAut W) u, hu⟩ = coreAct n (φ y) (D.β u)
  hQmax : ∀ Q'' : Subgroup (MulAut ↥(commV L)), IsPGroup 2 Q'' →
      Q'' ≤ Subgroup.normalizer (autSub L (commV L) : Set (MulAut ↥(commV L))) →
      fixV (autSub (ffJ S) (commV L)) ≤ fixV Q'' → Q'' ≤ autSub (ffJ S) (commV L)

variable {Y S L : Subgroup (MulAut W)} {n : ℕ}

omit [Finite W] in
private theorem gomiFour_image_comm (h : GomiFourSetup Y S L n) {A : Subgroup (MulAut W)}
    (hA : A ∈ Pset S) :
    ∀ a ∈ (A.subgroupOf Y).map h.φ.toMonoidHom, ∀ b ∈ (A.subgroupOf Y).map h.φ.toMonoidHom,
      a * b = b * a := by
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hA.2.2.1.1 _ (Subgroup.mem_subgroupOf.mp hx) _
    (Subgroup.mem_subgroupOf.mp hy))

omit [Finite W] in
private theorem gomiFour_inf_fixingSubgroup_eq_bot (h : GomiFourSetup Y S L n)
    {A : Subgroup (MulAut W)} (hA : A ∈ Pset S) :
    A ⊓ fixingSubgroup (MulAut W) ((commV L : Subgroup W) : Set W) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have haY : a ∈ Y := h.hSY (hA.1 (Subgroup.mem_inf.mp ha).1)
  have haC : a ∈ centSub (commV L) := by
    rw [CFSG.Quasithin.mem_centSub]
    intro u hu
    have h1 := (mem_fixingSubgroup_iff (MulAut W)).mp (Subgroup.mem_inf.mp ha).2 u hu
    rwa [MulAut.smul_def] at h1
  have hmem : a ∈ Y ⊓ centSub (commV L) := ⟨haY, haC⟩
  rw [h.hYcen, Subgroup.mem_bot] at hmem
  rwa [Subgroup.mem_bot]

private theorem gomiFour_offender_le_commV (h : GomiFourSetup Y S L n)
    {A : Subgroup (MulAut W)} (hA : A ∈ Pset S) :
    Nat.card ↥(commV L) ≤ Nat.card A * Nat.card ↥(commV L ⊓ fixV A) := by
  set F := fixingSubgroup (MulAut W) ((commV L : Subgroup W) : Set W) with hF
  have hle := card_le_index_mul_card_fixV hA (commV L)
  have hfaith := gomiFour_inf_fixingSubgroup_eq_bot h hA
  have hcardF : Nat.card ↥(A ⊓ F) = 1 := by rw [hfaith, Subgroup.card_bot]
  have hFF : (A ⊓ F) ⊓ A = A ⊓ F := by rw [inf_comm (A ⊓ F) A, ← inf_assoc, inf_idem]
  have h1 := Subgroup.relIndex_mul_card (A ⊓ F) A
  rw [hFF, hcardF, mul_one] at h1
  rw [← hF] at hle
  rw [h1] at hle
  exact hle

omit [Finite W] in
private theorem gomiFour_card_image (h : GomiFourSetup Y S L n) {A : Subgroup (MulAut W)}
    (hA : A ≤ Y) :
    Nat.card ((A.subgroupOf Y).map h.φ.toMonoidHom) = Nat.card A := by
  rw [Subgroup.card_map_of_injective h.φ.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

omit [Finite W] in
private theorem gomiFour_card_fixV_image (h : GomiFourSetup Y S L n) {A : Subgroup (MulAut W)}
    (hA : A ≤ Y) :
    Nat.card (fixV (((A.subgroupOf Y).map h.φ.toMonoidHom).map (coreAct n))) =
      Nat.card ↥(commV L ⊓ fixV A) := by
  have hmap := gomiFour_fixV_map_eq' h.hLn h.hLY h.D h.φ h.hφ h.hDβ hA
  have h1 : Nat.card ↥((fixV A).subgroupOf (commV L)) =
      Nat.card (fixV (((A.subgroupOf Y).map h.φ.toMonoidHom).map (coreAct n))) := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective
      (K := (fixV A).subgroupOf (commV L))
      (f := (MulEquiv.ofBijective h.D.β h.hDβ).toMonoidHom)
      (MulEquiv.injective (MulEquiv.ofBijective h.D.β h.hDβ))).symm
  rw [← h1, ← Subgroup.inf_subgroupOf_right (fixV A) (commV L), inf_comm (fixV A) (commV L)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

private theorem gomiFour_image_offender (h : GomiFourSetup Y S L n)
    {A : Subgroup (MulAut W)} (hA : A ∈ Pset S) :
    Nat.card (coreMod n) ≤ Nat.card ((A.subgroupOf Y).map h.φ.toMonoidHom) *
      Nat.card (fixV (((A.subgroupOf Y).map h.φ.toMonoidHom).map (coreAct n))) := by
  have hAY : A ≤ Y := hA.1.trans h.hSY
  have hPf : Nat.card ↥(commV L) = Nat.card (coreMod n) :=
    Nat.card_congr (MulEquiv.ofBijective h.D.β h.hDβ).toEquiv
  rw [gomiFour_card_image h hAY, gomiFour_card_fixV_image h hAY, ← hPf]
  exact gomiFour_offender_le_commV h hA

private theorem gomiFour_offender_closure (h : GomiFourSetup Y S L n)
    {A : Subgroup (MulAut W)} (hA : A ∈ Pset S) :
    ∃ T : Set (Equiv.Perm (Fin n)), (∀ t ∈ T, t.IsSwap) ∧
      (∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) ∧
      (A.subgroupOf Y).map h.φ.toMonoidHom = Subgroup.closure T := by
  have h3 : 3 ≤ n := by have := h.h5; omega
  obtain ⟨⟨T, hTsw, hTcomm, hTeq⟩, -, -⟩ :=
    sym_offender_generated_weak n h.hn h3 (gomiFour_image_comm h hA)
      (gomiFour_image_offender h hA)
  exact ⟨T, hTsw, hTcomm, hTeq⟩

private theorem gomiFour_offender_card (h : GomiFourSetup Y S L n)
    {A : Subgroup (MulAut W)} (hA : A ∈ Pset S) :
    Nat.card ↥(commV L) = Nat.card A * Nat.card ↥(commV L ⊓ fixV A) := by
  have h3 : 3 ≤ n := by have := h.h5; omega
  have hAY : A ≤ Y := hA.1.trans h.hSY
  obtain ⟨⟨T, -, -, -⟩, -, hcard⟩ :=
    sym_offender_generated_weak n h.hn h3 (gomiFour_image_comm h hA)
      (gomiFour_image_offender h hA)
  have h1 : Nat.card (coreMod n) = Nat.card ((A.subgroupOf Y).map h.φ.toMonoidHom) *
      Nat.card (fixV (((A.subgroupOf Y).map h.φ.toMonoidHom).map (coreAct n))) := by
    rw [hcard, Subgroup.card_map_of_injective
      (K := (A.subgroupOf Y).map h.φ.toMonoidHom) (coreAct_injective h3)]
  rw [Nat.card_congr (MulEquiv.ofBijective h.D.β h.hDβ).toEquiv, h1,
    gomiFour_card_image h hAY, gomiFour_card_fixV_image h hAY]

private theorem gomiFour_offender_relIndex (h : GomiFourSetup Y S L n)
    {A : Subgroup (MulAut W)} (hA : A ∈ Pset S) :
    (fixV A).relIndex (commV L) = Nat.card A := by
  have h1 := Subgroup.relIndex_mul_card (fixV A) (commV L)
  rw [inf_comm] at h1
  have h2 := gomiFour_offender_card h hA
  have h3 : (fixV A).relIndex (commV L) * Nat.card ↥(commV L ⊓ fixV A) =
      Nat.card A * Nat.card ↥(commV L ⊓ fixV A) := by rw [h1, h2]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h3

private theorem gomiFour_sup_fixV_eq_top (h : GomiFourSetup Y S L n)
    {A : Subgroup (MulAut W)} (hA : A ∈ Pset S) :
    commV L ⊔ fixV A = ⊤ ∧ Nat.card W = Nat.card A * Nat.card (fixV A) := by
  set C := fixV A with hC
  have hoff : Nat.card W ≤ Nat.card A * Nat.card C := by
    have h1 := hA.2.2.2 ⊥ (bot_le : (⊥ : Subgroup (MulAut W)) ≤ A)
    rw [CFSG.Quasithin.B1.card_bot_mul_card_fixV, ← hC] at h1
    exact h1
  have hri := gomiFour_offender_relIndex h hA
  rw [← hC] at hri
  have hcardSup : Nat.card ↥(commV L ⊔ C) = Nat.card A * Nat.card C := by
    have h1 := Subgroup.relIndex_mul_card C (commV L ⊔ C)
    rw [inf_eq_left.mpr le_sup_right, Subgroup.relIndex_sup_right, hri] at h1
    exact h1.symm
  have hle : Nat.card ↥(commV L ⊔ C) ≤ Nat.card W := by
    rw [← Subgroup.card_top (G := W)]
    exact Subgroup.card_le_of_le (le_top : commV L ⊔ C ≤ (⊤ : Subgroup W))
  have hW : Nat.card W = Nat.card A * Nat.card C := le_antisymm hoff (hcardSup ▸ hle)
  have hfin : Nat.card ↥(commV L ⊔ C) = Nat.card W := by rw [hcardSup, ← hW]
  have htop : commV L ⊔ C = (⊤ : Subgroup W) :=
    Subgroup.eq_top_of_card_eq (H := commV L ⊔ C) hfin
  exact ⟨htop, hW⟩

private theorem gomiFour_Pset_nonempty {Y S : Subgroup (MulAut W)} (hS : IsSylowIn 2 S Y)
    (hP : (Pset Y).Nonempty) : (Pset S).Nonempty := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B, hB⟩ := hP
  have hB' : IsFFStarOffender Y B := hB
  have hBp : IsPGroup 2 (B.subgroupOf Y) := by
    intro b
    have h1 := hB'.2.2.1.2 _ (Subgroup.mem_subgroupOf.mp b.2)
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using h1))⟩
  obtain ⟨Q, hBQ⟩ := hBp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Y Q hS.toSylow
  have h1 := CFSG.Quasithin.isFFStarOffender_map_conj hB' g.2
  refine ⟨B.map (MulAut.conj (g : MulAut W)).toMonoidHom, ?_, h1.2.1, h1.2.2⟩
  rintro _ ⟨b, hb, rfl⟩
  have hbY : b ∈ Y := hB'.1 hb
  have hbQ : (⟨b, hbY⟩ : ↥Y) ∈ (Q : Subgroup ↥Y) := hBQ (Subgroup.mem_subgroupOf.mpr hb)
  have h2 : MulAut.conj g • (⟨b, hbY⟩ : ↥Y) ∈ ((g • Q : Sylow 2 ↥Y) : Subgroup ↥Y) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hbQ
  rw [hg, IsSylowIn.coe_toSylow] at h2
  have h3 := Subgroup.mem_subgroupOf.mp h2
  simpa [MulAut.smul_def, MulAut.conj_apply] using h3

private theorem gomiFour_setup {Y S L : Subgroup (MulAut W)} {n : ℕ}
    (hW : ∀ w : W, w ^ 2 = 1) (hn : Odd n) (h5 : 5 ≤ n)
    (hLn : (L.subgroupOf Y).IsSubnormal) (hLY : L ≤ Y) (hL : IsAlt ↥L n)
    (hC : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥)
    (hnat : (FFModel.altDn n).Realizes L (commV L) (gomiWXKer L))
    (hSY : S ≤ Y) (hS2 : IsPGroup 2 S) (hPS : (Pset S).Nonempty) :
    Nonempty (GomiFourSetup Y S L n) := by
  have h3 : 3 ≤ n := by omega
  have hH : L ≠ ⊥ := gomiFour_ne_bot_of_isAlt h3 hL
  have hNormal : (L.subgroupOf Y).Normal := gomiFour_normal_of_isAlt hLY hLn h5 hL hC
  have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hNormal
  have hYst : Y ≤ stabSub (commV L) := hYN.trans (normalizer_commV_le_stabSub L)
  have hYcen : Y ⊓ centSub (commV L) = ⊥ :=
    gomiFour_inf_centSub_eq_bot hn h5 hH hnat hNormal hLY hC
  obtain ⟨θ, β, hβs, hβk, hβe⟩ := gomiFour_coreData hn h5 hH hnat
  let D : AltNatData (autSub L (commV L)) n := gomiFourAltNatData hn h5 hH hnat θ β hβs hβk hβe
  obtain ⟨T, -, -, -, -, hψbij, hβbij, hYeqN, hQmax⟩ :=
    gomiFour_altFamily hW hn h5 hH hnat hNormal hLY hSY hS2 hC hPS D
  let φ : ↥Y ≃* Equiv.Perm (Fin n) := gomiFourPhi hn h5 D hYst hYcen hψbij hYeqN
  exact ⟨hW, hn, h5, hH, hNormal, hLY, hSY, hS2, hYst, hYcen, D, hψbij, hβbij, φ,
    gomiFourPhi_action hn h5 D hYst hYcen hψbij hYeqN, hQmax⟩

private theorem gomiFour_cycleType_of_isSwap {σ : Equiv.Perm (Fin n)} (hσ : σ.IsSwap) :
    σ.cycleType = {2} := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  rw [(Equiv.Perm.isCycle_swap hab).cycleType, Equiv.Perm.card_support_swap hab]

private theorem gomiFour_exists_transvection (h : GomiFourSetup Y S L n)
    (hPS : (Pset S).Nonempty) :
    ∃ (t₀ : MulAut W) (ht₀ : t₀ ∈ Y), (h.φ ⟨t₀, ht₀⟩).IsSwap ∧
      (fixV (Subgroup.zpowers t₀)).relIndex (commV L) ≤ 2 ∧
      (fixV (Subgroup.zpowers t₀)).index ≤ 2 := by
  obtain ⟨A₀, hA₀⟩ := hPS
  obtain ⟨T, hTsw, -, hTeq⟩ := gomiFour_offender_closure h hA₀
  have hTne : T.Nonempty := by
    by_contra hT
    rw [Set.not_nonempty_iff_eq_empty] at hT
    apply hA₀.2.1
    have h1 : (A₀.subgroupOf Y).map h.φ.toMonoidHom = ⊥ := by
      rw [hTeq, hT, Subgroup.closure_empty]
    have h2 : A₀.subgroupOf Y = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ h.φ.injective).1 h1
    calc A₀ = (A₀.subgroupOf Y).map Y.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (hA₀.1.trans h.hSY)).symm
      _ = ⊥ := by rw [h2, Subgroup.map_bot]
  obtain ⟨t', ht'T⟩ := hTne
  have hmem : t' ∈ (A₀.subgroupOf Y).map h.φ.toMonoidHom := by
    rw [hTeq]
    exact Subgroup.subset_closure ht'T
  obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hmem
  have hsw : (h.φ a).IsSwap := hae ▸ hTsw t' ht'T
  have hri := gomiFour_relIndex_fixV_zpowers_le h.hLn h.hLY h.D h.φ h.hφ h.hDβ a.2 hsw
  refine ⟨(a : MulAut W), a.2, hsw, hri, ?_⟩
  have htop : commV L ⊔ fixV A₀ = ⊤ := (gomiFour_sup_fixV_eq_top h hA₀).1
  have hle : fixV A₀ ≤ fixV (Subgroup.zpowers (a : MulAut W)) := by
    intro v hv
    rw [mem_fixV_zpowers_iff_apply]
    exact hv (a : MulAut W) (Subgroup.mem_subgroupOf.mp ha)
  have hsup : commV L ⊔ fixV (Subgroup.zpowers (a : MulAut W)) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact sup_le_sup_left hle (commV L)
  calc (fixV (Subgroup.zpowers (a : MulAut W))).index
      = (fixV (Subgroup.zpowers (a : MulAut W))).relIndex (⊤ : Subgroup W) :=
        (Subgroup.relIndex_top_right _).symm
    _ = (fixV (Subgroup.zpowers (a : MulAut W))).relIndex
          (commV L ⊔ fixV (Subgroup.zpowers (a : MulAut W))) := by rw [hsup]
    _ = (fixV (Subgroup.zpowers (a : MulAut W))).relIndex (commV L) :=
        Subgroup.relIndex_sup_right (commV L) _
    _ ≤ 2 := hri

private theorem gomiFour_index_fixV_swap (h : GomiFourSetup Y S L n)
    (hPS : (Pset S).Nonempty) {s : MulAut W} (hsY : s ∈ Y)
    (hswap : (h.φ ⟨s, hsY⟩).IsSwap) :
    (fixV (Subgroup.zpowers s)).index ≤ 2 := by
  obtain ⟨t₀, ht₀, hsw0, -, hidx0⟩ := gomiFour_exists_transvection h hPS
  have hcyc : (h.φ ⟨t₀, ht₀⟩).cycleType = (h.φ ⟨s, hsY⟩).cycleType := by
    rw [gomiFour_cycleType_of_isSwap hsw0, gomiFour_cycleType_of_isSwap hswap]
  obtain ⟨ψ, hψ⟩ := isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr hcyc)
  let y : ↥Y := h.φ.symm ψ
  have hs_eq : (y : MulAut W) * t₀ * (y : MulAut W)⁻¹ = s := by
    have h1 := congrArg h.φ.symm hψ
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply] at h1
    simpa using congrArg Subtype.val h1
  have hconj : (Subgroup.zpowers t₀).map (MulAut.conj (y : MulAut W)).toMonoidHom =
      Subgroup.zpowers s := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, MonoidHom.map_closure]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, rfl, rfl⟩
      simpa [MulAut.conj_apply] using hs_eq
    · rintro rfl
      exact ⟨t₀, rfl, by simpa [MulAut.conj_apply] using hs_eq⟩
  have hfixeq : fixV (Subgroup.zpowers s) =
      (fixV (Subgroup.zpowers t₀)).map (y : MulAut W).toMonoidHom := by
    rw [← hconj]
    exact CFSG.Quasithin.fixV_map_conj_eq (Subgroup.zpowers t₀) (y : MulAut W)
  have hcard : Nat.card (fixV (Subgroup.zpowers s)) =
      Nat.card (fixV (Subgroup.zpowers t₀)) := by
    rw [hfixeq]
    exact Subgroup.card_map_of_injective (K := fixV (Subgroup.zpowers t₀))
      (f := (y : MulAut W).toMonoidHom) (y : MulAut W).injective
  have h1 := Subgroup.card_mul_index (fixV (Subgroup.zpowers s))
  have h2 := Subgroup.card_mul_index (fixV (Subgroup.zpowers t₀))
  rw [hcard] at h1
  have h3 : Nat.card (fixV (Subgroup.zpowers t₀)) * (fixV (Subgroup.zpowers s)).index ≤
      Nat.card (fixV (Subgroup.zpowers t₀)) * 2 := by
    rw [h1, ← h2]
    exact Nat.mul_le_mul_left _ hidx0
  exact Nat.le_of_mul_le_mul_left h3 Nat.card_pos

omit [Finite W] in
private theorem gomiFour_sq_eq_one_of_isSwap (h : GomiFourSetup Y S L n) {s : MulAut W}
    (hsY : s ∈ Y) (hswap : (h.φ ⟨s, hsY⟩).IsSwap) : s ^ 2 = 1 := by
  have h2 : (⟨s, hsY⟩ : ↥Y) ^ 2 = 1 := by
    apply h.φ.injective
    rw [map_pow, map_one]
    exact sq_eq_one_of_isSwap hswap
  exact congrArg Subtype.val h2

omit [Finite W] in
private theorem gomiFour_isElemAbelian2_zpowers (h : GomiFourSetup Y S L n) {s : MulAut W}
    (hsY : s ∈ Y) (hswap : (h.φ ⟨s, hsY⟩).IsSwap) :
    IsElemAbelian2 (Subgroup.zpowers s) :=
  CFSG.Quasithin.StabLat.isElemAbelian2_zpowers
    (gomiFour_sq_eq_one_of_isSwap h hsY hswap)

private theorem gomiFour_offender_ineq_zpowers (h : GomiFourSetup Y S L n)
    (hPS : (Pset S).Nonempty) {s : MulAut W} (hsY : s ∈ Y)
    (hswap : (h.φ ⟨s, hsY⟩).IsSwap) :
    ∀ B : Subgroup (MulAut W), B ≤ Subgroup.zpowers s →
      Nat.card B * Nat.card (fixV B) ≤
        Nat.card (Subgroup.zpowers s) * Nat.card (fixV (Subgroup.zpowers s)) := by
  have hidx := gomiFour_index_fixV_swap h hPS hsY hswap
  have hsq : s ^ 2 = 1 := gomiFour_sq_eq_one_of_isSwap h hsY hswap
  have hsne : s ≠ 1 := by
    intro hs1
    have hφ1 : h.φ ⟨s, hsY⟩ = 1 := by
      rw [show (⟨s, hsY⟩ : ↥Y) = 1 from Subtype.ext hs1]
      simp
    have h2 := Equiv.Perm.IsSwap.orderOf hswap
    rw [hφ1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hcardz : Nat.card ↥(Subgroup.zpowers s) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hsq hsne
  have : Fact (Nat.Prime (Nat.card ↥(Subgroup.zpowers s))) := by
    rw [hcardz]
    exact ⟨Nat.prime_two⟩
  have hW : Nat.card W ≤ 2 * Nat.card (fixV (Subgroup.zpowers s)) := by
    have h1 := Subgroup.card_mul_index (fixV (Subgroup.zpowers s))
    calc Nat.card W = Nat.card (fixV (Subgroup.zpowers s)) *
          (fixV (Subgroup.zpowers s)).index := h1.symm
      _ ≤ Nat.card (fixV (Subgroup.zpowers s)) * 2 := Nat.mul_le_mul_left _ hidx
      _ = 2 * Nat.card (fixV (Subgroup.zpowers s)) := mul_comm _ _
  intro B hB
  have hBmap : B = (B.subgroupOf (Subgroup.zpowers s)).map (Subgroup.zpowers s).subtype :=
    (Subgroup.map_subgroupOf_eq_of_le hB).symm
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card
    (B.subgroupOf (Subgroup.zpowers s)) with hbot | htop
  · have hBbot : B = ⊥ := by rw [hBmap, hbot, Subgroup.map_bot]
    rw [hBbot, Subgroup.card_bot, one_mul, hcardz, CFSG.Quasithin.B1.fixV_bot, Subgroup.card_top]
    exact hW
  · have hBtop : B = Subgroup.zpowers s := by
      have h1 : (B.subgroupOf (Subgroup.zpowers s)) =
          (Subgroup.zpowers s).subgroupOf (Subgroup.zpowers s) := by
        rw [htop, Subgroup.subgroupOf_self]
      rw [hBmap, h1]
      exact Subgroup.map_subgroupOf_eq_of_le le_rfl
    rw [hBtop]

private theorem gomiFour_isFFStarOffender_zpowers (h : GomiFourSetup Y S L n)
    (hPS : (Pset S).Nonempty) {s : MulAut W} (hsY : s ∈ Y) (hsS : s ∈ S)
    (hswap : (h.φ ⟨s, hsY⟩).IsSwap) :
    IsFFStarOffender S (Subgroup.zpowers s) := by
  refine ⟨Subgroup.zpowers_le.mpr hsS, ?_, gomiFour_isElemAbelian2_zpowers h hsY hswap,
    gomiFour_offender_ineq_zpowers h hPS hsY hswap⟩
  intro hbot
  have hs1 : s = 1 := by
    have h1 : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
    rw [hbot, Subgroup.mem_bot] at h1
    exact h1
  have hφ1 : h.φ ⟨s, hsY⟩ = 1 := by
    rw [show (⟨s, hsY⟩ : ↥Y) = 1 from Subtype.ext hs1]
    simp
  have h2 := Equiv.Perm.IsSwap.orderOf hswap
  rw [hφ1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

private theorem gomiFour_mem_ffJ_of_isSwap (h : GomiFourSetup Y S L n)
    (hPS : (Pset S).Nonempty) {s : MulAut W} (hsY : s ∈ Y) (hsS : s ∈ S)
    (hswap : (h.φ ⟨s, hsY⟩).IsSwap) : s ∈ ffJ S := by
  have hle : Subgroup.zpowers s ≤ ffJ S :=
    le_iSup₂_of_le (Subgroup.zpowers s)
      (gomiFour_isFFStarOffender_zpowers h hPS hsY hsS hswap) le_rfl
  exact hle (Subgroup.mem_zpowers s)

private theorem gomiFour_closure_le_ffJ (h : GomiFourSetup Y S L n)
    (hPS : (Pset S).Nonempty) :
    Subgroup.closure {s : MulAut W | ∃ hs : s ∈ Y, s ∈ S ∧ (h.φ ⟨s, hs⟩).IsSwap} ≤
      ffJ S :=
  (Subgroup.closure_le (ffJ S)).mpr fun _ hs =>
    gomiFour_mem_ffJ_of_isSwap h hPS hs.1 hs.2.1 hs.2.2

private theorem gomiFour_ffJ_le_closure (h : GomiFourSetup Y S L n) :
    ffJ S ≤
      Subgroup.closure {s : MulAut W | ∃ hs : s ∈ Y, s ∈ S ∧ (h.φ ⟨s, hs⟩).IsSwap} := by
  rw [ffJ]
  refine iSup₂_le fun A hA => ?_
  obtain ⟨T, hTsw, -, hTeq⟩ := gomiFour_offender_closure h hA
  have hAY : A ≤ Y := hA.1.trans h.hSY
  have hclosure : A.subgroupOf Y = Subgroup.closure (h.φ.symm '' T) := by
    have hcomp : (h.φ.symm.toMonoidHom).comp h.φ.toMonoidHom = MonoidHom.id ↥Y :=
      MonoidHom.ext fun x => h.φ.symm_apply_apply x
    have h1 : Subgroup.map h.φ.symm.toMonoidHom (Subgroup.closure T) = A.subgroupOf Y := by
      rw [← hTeq, Subgroup.map_map, hcomp, Subgroup.map_id]
    rw [← h1, MonoidHom.map_closure]
    rfl
  have hAeq : A = Subgroup.closure ((h.φ.symm '' T).image Y.subtype) := by
    calc A = (A.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hAY).symm
      _ = (Subgroup.closure (h.φ.symm '' T)).map Y.subtype := by rw [hclosure]
      _ = Subgroup.closure ((h.φ.symm '' T).image Y.subtype) := by rw [MonoidHom.map_closure]
  rw [hAeq]
  refine Subgroup.closure_mono ?_
  rintro x hx
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨t, htT, rfl⟩ := ha
  refine ⟨(h.φ.symm t).2, ?_, ?_⟩
  · have hmem : h.φ.symm t ∈ A.subgroupOf Y := by
      rw [hclosure]
      exact Subgroup.subset_closure ⟨t, htT, rfl⟩
    exact hA.1 (Subgroup.mem_subgroupOf.mp hmem)
  · have h2 : (⟨Y.subtype (h.φ.symm t), (h.φ.symm t).2⟩ : ↥Y) = h.φ.symm t := Subtype.ext rfl
    rw [h2, h.φ.apply_symm_apply t]
    exact hTsw t htT

private theorem gomiFour_ffJ_eq_closure (h : GomiFourSetup Y S L n)
    (hPS : (Pset S).Nonempty) :
    ffJ S = Subgroup.closure {s : MulAut W | ∃ hs : s ∈ Y, s ∈ S ∧ (h.φ ⟨s, hs⟩).IsSwap} :=
  le_antisymm (gomiFour_ffJ_le_closure h) (gomiFour_closure_le_ffJ h hPS)

private theorem gomiFour_ffJ_le_gomiCSP (h : GomiFourSetup Y S L n)
    (hPS : (Pset S).Nonempty) : ffJ S ≤ gomiCSP S L := by
  rw [gomiFour_ffJ_eq_closure h hPS]
  refine (Subgroup.closure_le (gomiCSP S L)).mpr ?_
  rintro s ⟨hsY, hsS, hswap⟩
  refine Subgroup.mem_inf.mpr ⟨hsS, ?_⟩
  rw [mem_fixingSubgroup_iff]
  intro u hu
  rw [MulAut.smul_def]
  exact (mem_fixV.mp (Subgroup.mem_inf.mp hu).2) s
    (gomiFour_mem_ffJ_of_isSwap h hPS hsY hsS hswap)

omit [Finite W] in
private theorem gomiFour_fixV_autSub_ffJ_le (h : GomiFourSetup Y S L n) :
    fixV (autSub (ffJ S) (commV L)) ≤ fixV (autSub (gomiCSP S L) (commV L)) := by
  intro u hu
  rw [CFSG.Quasithin.mem_fixV_autSub] at hu ⊢
  intro g hg hgst
  have huFix : (u : W) ∈ fixV (ffJ S) := by
    rw [mem_fixV]
    intro x hx
    exact hu x hx (h.hYst (h.hSY (CFSG.Quasithin.B6.ffJ_le S hx)))
  have h2 := (mem_fixingSubgroup_iff (MulAut W)).mp (Subgroup.mem_inf.mp hg).2 (u : W)
    ⟨u.2, huFix⟩
  rwa [MulAut.smul_def] at h2

omit [Finite W] in
private theorem gomiFour_gomiCSP_le_ffJ (h : GomiFourSetup Y S L n) :
    gomiCSP S L ≤ ffJ S := by
  have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.hLY).mp h.hLn
  have hT2 : IsPGroup 2 (autSub (gomiCSP S L) (commV L)) :=
    isPGroup_autSub (h.hS2.to_le inf_le_left)
  have hTN : autSub (gomiCSP S L) (commV L) ≤
      Subgroup.normalizer (autSub L (commV L) : Set (MulAut ↥(commV L))) :=
    autSub_le_normalizer ((le_trans inf_le_left h.hSY).trans hYN)
  have hle := h.hQmax (autSub (gomiCSP S L) (commV L)) hT2 hTN
    (gomiFour_fixV_autSub_ffJ_le h)
  intro x hx
  have hxS : x ∈ S := (Subgroup.mem_inf.mp hx).1
  have hxY : x ∈ Y := h.hSY hxS
  have hxst : x ∈ stabSub (commV L) := h.hYst hxY
  have hxaut : resHom (commV L) ⟨x, hxst⟩ ∈ autSub (gomiCSP S L) (commV L) :=
    mem_autSub.mpr ⟨⟨x, hxst⟩, hx, rfl⟩
  obtain ⟨g, hg, hgres⟩ := mem_autSub.mp (hle hxaut)
  have hgY : (g : MulAut W) ∈ Y := h.hSY (CFSG.Quasithin.B6.ffJ_le S hg)
  have hgcent : (g : MulAut W) * x⁻¹ ∈ Y ⊓ centSub (commV L) := by
    have hc : (g : MulAut W) * x⁻¹ ∈ centSub (commV L) := by
      rw [CFSG.Quasithin.mem_centSub]
      intro u hu
      have hu' : (x⁻¹ : MulAut W) u ∈ commV L :=
        (CFSG.Quasithin.mem_stabSub.mp ((stabSub (commV L)).inv_mem hxst) u).mpr hu
      have h2 : resHom (commV L) g ⟨(x⁻¹ : MulAut W) u, hu'⟩ =
          resHom (commV L) ⟨x, hxst⟩ ⟨(x⁻¹ : MulAut W) u, hu'⟩ := by rw [hgres]
      have h3 : (g : MulAut W) ((x⁻¹ : MulAut W) u) = x ((x⁻¹ : MulAut W) u) := by
        simpa [CFSG.Quasithin.resHom_apply] using
          congrArg (fun w : ↥(commV L) => (w : W)) h2
      rw [MulAut.mul_apply, h3]
      simp
    exact ⟨Y.mul_mem hgY (Y.inv_mem hxY), hc⟩
  rw [h.hYcen, Subgroup.mem_bot] at hgcent
  have hgx : (g : MulAut W) = x := mul_inv_eq_one.mp hgcent
  rw [← hgx]
  exact hg

private theorem gomiFour_gomiCSP_eq_ffJ (h : GomiFourSetup Y S L n)
    (hPS : (Pset S).Nonempty) : gomiCSP S L = ffJ S :=
  le_antisymm (gomiFour_gomiCSP_le_ffJ h) (gomiFour_ffJ_le_gomiCSP h hPS)

theorem gomiFact37Four_holds : GomiFact37Four := by
  intro W _ _ hW Y S L m hm hPY hS hLY hLn hL hC hnat
  have hn : Odd (2 * m - 1) := ⟨m - 1, by omega⟩
  have h5 : 5 ≤ 2 * m - 1 := by omega
  have hPS : (Pset S).Nonempty := gomiFour_Pset_nonempty hS hPY
  obtain ⟨h⟩ := gomiFour_setup (Y := Y) (S := S) (L := L) hW hn h5 hLn hLY hL hC hnat
    hS.le hS.isPGroup hPS
  exact ⟨h.φ, (gomiFour_gomiCSP_eq_ffJ h hPS).trans (gomiFour_ffJ_eq_closure h hPS)⟩

end CFSG.GroupTheory

end
