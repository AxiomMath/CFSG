module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RY2
public import CFSG.Sporadic.SmallOddCore.LocalSpec

public section

namespace CFSG.EvenSporadicStandard.Fin76b.S16

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b

theorem s16_model_of_check {n : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))} {pg : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool} (hD : GroupData n P pg gg sift)
    (hPR : P ≤ R) (e : ↥R ≃* MulAut ↥P)
    (he : ∀ (x : ↥R) (p : ↥P), (((e x) p : ↥P) : Equiv.Perm (Fin n)) = (x : Equiv.Perm (Fin n)) *
      (p : Equiv.Perm (Fin n)) * (x : Equiv.Perm (Fin n))⁻¹)
    {cap : ℕ} {uT tT bT rT vT xT : Table} {rootsL es : List Table} {flags : List Bool}
    (hu : tp n uT ∈ R)
    (hroot : ∀ ht : tp n tT ∈ P, Nat.card ↥(rootGroup ↥P ⟨tp n tT, ht⟩) = 32)
    (h : s16Check n cap sift uT tT bT rT vT xT rootsL es flags = true) :
    ∃ (ht : tp n tT ∈ P) (hb : tp n bT ∈ P), S16Model ↥P ⟨tp n tT, ht⟩ ⟨tp n bT, hb⟩ := by
  classical
  have hn : n < 2 ^ 32 := hD.lt
  simp only [s16Check, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, beq_iff_eq,
    and_assoc] at h
  obtain ⟨hpu, hpt, hpb, hpr, hpv, hpx, hproots, hpes, hst, hsb, hsv, hsx, hsroots, hses, hsru,
    hsr, hrr, hrt, hbinv, hrb, hvt, hxt, hv4, hv8, hxinv, hx1, hxt', hvinv, hxv, hrv, hrx, hvb,
    hxb, hrootsq, henumE, hcent, hpvv, hpvx, henumCE, hmemvv, hmemvx, hcvvr, hcvxr, henumY, hesT,
    hpc, henumC, hcx, hmemt, hmemx, hquad⟩ := h
  set u := tp n uT with hu_def
  set t := tp n tT with ht_def
  set b := tp n bT with hb_def
  set r := tp n rT with hr_def
  set v := tp n vT with hv_def
  set x := tp n xT with hx_def
  have Ru : Rep n uT u := rep_tp hpu
  have Rt : Rep n tT t := rep_tp hpt
  have Rb : Rep n bT b := rep_tp hpb
  have Rr : Rep n rT r := rep_tp hpr
  have Rv : Rep n vT v := rep_tp hpv
  have Rx : Rep n xT x := rep_tp hpx
  have htP : t ∈ P := (hD.sift _ _ Rt).1 hst
  have hbP : b ∈ P := (hD.sift _ _ Rb).1 hsb
  have hvP : v ∈ P := (hD.sift _ _ Rv).1 hsv
  have hxP : x ∈ P := (hD.sift _ _ Rx).1 hsx
  have hrP : r ∉ P := fun hmem => by
    have := (hD.sift _ _ Rr).2 hmem
    rw [this] at hsr
    exact Bool.noConfusion hsr
  have hruP : r * u ∈ P := (hD.sift _ _ (Rep.compT Rr Ru)).1 hsru
  have hrR : r ∈ R := by
    have : r = (r * u) * u⁻¹ := by group
    rw [this]
    exact mul_mem (hPR hruP) (inv_mem hu)
  have hr2 : r * r = 1 := by
    have := sq_eq_one_of_invoOK Rr hrr
    rwa [pow_two] at this
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hx2 : x * x = 1 := by
    have := sq_eq_one_of_invoOK Rx hxinv
    rwa [pow_two] at this
  have hxinv' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have Rbi : Rep n (invT n bT) b⁻¹ := rep_invT Rb hbinv
  have Rvi : Rep n (invT n vT) v⁻¹ := rep_invT Rv hvinv
  have r_t : r * t * r⁻¹ = t := by
    rw [hrinv]
    exact (tblEq_iff_eq (Rep.compT (Rep.compT Rr Rt) Rr) Rt).1 hrt
  have r_b : r * b * r⁻¹ = b⁻¹ := by
    rw [hrinv]
    exact (tblEq_iff_eq (Rep.compT (Rep.compT Rr Rb) Rr) Rbi).1 hrb
  have v_t : v * t = t * v := (commTT_iff Rv Rt).1 hvt
  have x_t : x * t = t * x := (commTT_iff Rx Rt).1 hxt
  have v4 : v ^ 4 = t := (tblEq_iff_eq (Rep.powT hn Rv 4) Rt).1 hv4
  have v8 : v ^ 8 = 1 := (tblEq_iff_eq (Rep.powT hn Rv 8) (Rep.idT hn)).1 hv8
  have x_ne_one : x ≠ 1 := fun hh => by
    have := (tblEq_iff_eq Rx (Rep.idT hn)).2 hh
    rw [this] at hx1
    exact Bool.noConfusion hx1
  have x_ne_t : x ≠ t := fun hh => by
    have := (tblEq_iff_eq Rx Rt).2 hh
    rw [this] at hxt'
    exact Bool.noConfusion hxt'
  have x_v : x * v * x⁻¹ = v⁻¹ := by
    rw [hxinv']
    exact (tblEq_iff_eq (Rep.compT (Rep.compT Rx Rv) Rx) Rvi).1 hxv
  have r_v : r * v * r⁻¹ = v * t := by
    rw [hrinv]
    exact (tblEq_iff_eq (Rep.compT (Rep.compT Rr Rv) Rr) (Rep.compT Rv Rt)).1 hrv
  have r_x : r * x * r⁻¹ = x * t := by
    rw [hrinv]
    exact (tblEq_iff_eq (Rep.compT (Rep.compT Rr Rx) Rr) (Rep.compT Rx Rt)).1 hrx
  have v_b : v * b * v⁻¹ = b⁻¹ :=
    (tblEq_iff_eq (Rep.compT (Rep.compT Rv Rb) Rvi) Rbi).1 hvb
  have x_b : x * b * x⁻¹ = b⁻¹ := by
    rw [hxinv']
    exact (tblEq_iff_eq (Rep.compT (Rep.compT Rx Rb) Rx) Rbi).1 hxb
  set roots : Set (Equiv.Perm (Fin n)) := tp n '' {y | y ∈ rootsL.toArray} with hroots_def
  have hrootmem : ∀ y ∈ roots, y ∈ P ∧ y * y = t := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ rootsL := by simpa using hz
    have Rz : Rep n z (tp n z) := rep_tp (hproots z hz')
    exact ⟨(hD.sift _ _ Rz).1 (hsroots z hz'),
      (tblEq_iff_eq (Rep.compT Rz Rz) Rt).1 (hrootsq z hz')⟩
  have hE1 := enumOK_spec hn hproots henumE
  have hE1card : Nat.card ↥(closure roots) = 32 := hE1.1
  have hgenr : (genOf n [rT] : Subgroup (Equiv.Perm (Fin n))) = closure {r} := by
    unfold genOf
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have : z = rT := by simpa using hz
      subst this
      rfl
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      exact ⟨rT, by simp, hy.symm⟩
  have hCEcard : Nat.card ↥(closure roots ⊓ centralizer ({r} : Set (Equiv.Perm (Fin n)))) = 8 := by
    have := centCount_spec (cap := cap) hn (cs := rootsL) (gs := [rT]) hproots henumE
      (by simpa using hpr)
    rw [hgenr, centralizer_closure] at this
    rw [hcent] at this
    exact this
  have Rvv : Rep n (compT n vT vT) (v * v) := Rep.compT Rv Rv
  have Rvx : Rep n (compT n vT xT) (v * x) := Rep.compT Rv Rx
  have hvvT : tp n (compT n vT vT) = v * v := rep_unique (rep_tp hpvv) Rvv
  have hvxT : tp n (compT n vT xT) = v * x := rep_unique (rep_tp hpvx) Rvx
  have hgenCE : (genOf n [compT n vT vT, compT n vT xT] : Subgroup (Equiv.Perm (Fin n))) =
      closure ({v * v, v * x} : Set (Equiv.Perm (Fin n))) := by
    unfold genOf
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, (rfl | rfl), rfl⟩
      · left; exact hvvT
      · right; exact hvxT
    · rintro (rfl | rfl)
      · exact ⟨compT n vT vT, Or.inl rfl, hvvT⟩
      · exact ⟨compT n vT xT, Or.inr rfl, hvxT⟩
  have hpCE : ∀ g ∈ [compT n vT vT, compT n vT xT], permOK n g = true := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hpvv
    · exact hpvx
  have hCE8 : Nat.card ↥(closure ({v * v, v * x} : Set (Equiv.Perm (Fin n)))) = 8 := by
    rw [← hgenCE]
    exact (enumOK_spec hn hpCE henumCE).1
  have hmemE1 : ∀ {T : Table} {g : Equiv.Perm (Fin n)}, Rep n T g →
      memT n (mulClosureH n rootsL.toArray cap).1 T = true → g ∈ closure roots := by
    intro T g hT hmem
    obtain ⟨k, hk, hgk⟩ := memT_spec (fun k hk => (hE1.2.1 k hk).1) hT hmem
    rw [hgk]
    exact (hE1.2.1 k hk).2
  have hCEle : closure ({v * v, v * x} : Set (Equiv.Perm (Fin n))) ≤
      closure roots ⊓ centralizer ({r} : Set (Equiv.Perm (Fin n))) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact ⟨hmemE1 Rvv hmemvv, mem_centralizer_singleton_iff.2 ((commTT_iff Rvv Rr).1 hcvvr)⟩
    · exact ⟨hmemE1 Rvx hmemvx, mem_centralizer_singleton_iff.2 ((commTT_iff Rvx Rr).1 hcvxr)⟩
  have hCE : closure ({v * v, v * x} : Set (Equiv.Perm (Fin n))) =
      closure roots ⊓ centralizer ({r} : Set (Equiv.Perm (Fin n))) :=
    Subgroup.eq_of_le_of_card_ge hCEle (by rw [hCEcard, hCE8])
  have hpY : ∀ g ∈ [vT, xT, rT], permOK n g = true := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact hpv
    · exact hpx
    · exact hpr
  have hgenY : (genOf n [vT, xT, rT] : Subgroup (Equiv.Perm (Fin n))) =
      closure ({v, x, r} : Set (Equiv.Perm (Fin n))) := by
    unfold genOf
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, (rfl | rfl | rfl), rfl⟩
      · left; rfl
      · right; left; rfl
      · right; right; rfl
    · rintro (rfl | rfl | rfl)
      · exact ⟨vT, Or.inl rfl, rfl⟩
      · exact ⟨xT, Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨rT, Or.inr (Or.inr rfl), rfl⟩
  have hY : Nat.card ↥(closure ({v, x, r} : Set (Equiv.Perm (Fin n)))) = 32 := by
    rw [← hgenY]
    exact (enumOK_spec hn hpY henumY).1
  set cL := cTbls n rT es flags with hcL
  set cs : Set (Equiv.Perm (Fin n)) := tp n '' {y | y ∈ cL.toArray} with hcs_def
  have hC1 := enumOK_spec hn hpc henumC
  have hC32 : Nat.card ↥(closure cs) = 32 := hC1.1
  have hcsprop : ∀ c ∈ cs, c ∈ R ∧ ((c ∈ P ∧ c * t = t * c) ∨
      (∃ y, y ∈ P ∧ y * t = t * y ∧ c = y * r)) ∧ c * x = x * c := by
    rintro _ ⟨T, hT, rfl⟩
    have hT' : T ∈ cL := by simpa using hT
    obtain ⟨⟨e', fl⟩, hp, hTe⟩ := List.mem_map.1 hT'
    obtain ⟨he', -⟩ := List.of_mem_zip hp
    have Re : Rep n e' (tp n e') := rep_tp (hpes e' he')
    have heP : tp n e' ∈ P := (hD.sift _ _ Re).1 (hses e' he')
    have het : tp n e' * t = t * tp n e' := (commTT_iff Re Rt).1 (hesT e' he')
    have RT : Rep n T (tp n T) := rep_tp (hpc T hT')
    have hxc : tp n T * x = x * tp n T := (commTT_iff RT Rx).1 (hcx T hT')
    simp only at hTe
    by_cases hfl : fl = true
    · rw [if_pos hfl] at hTe
      have hTeq : tp n T = tp n e' * r := by
        apply rep_unique RT
        rw [← hTe]
        exact Rep.compT Re Rr
      refine ⟨?_, Or.inr ⟨tp n e', heP, het, hTeq⟩, hxc⟩
      rw [hTeq]
      exact mul_mem (hPR heP) hrR
    · rw [if_neg hfl] at hTe
      have hTeq : tp n T = tp n e' := by
        apply rep_unique RT
        rw [← hTe]
        exact Re
      refine ⟨?_, Or.inl ⟨?_, ?_⟩, hxc⟩
      · rw [hTeq]; exact hPR heP
      · rw [hTeq]; exact heP
      · rw [hTeq]; exact het
  have hmemC : ∀ {T : Table} {g : Equiv.Perm (Fin n)}, Rep n T g →
      memT n (mulClosureH n cL.toArray cap).1 T = true → g ∈ closure cs := by
    intro T g hT hmem
    obtain ⟨k, hk, hgk⟩ := memT_spec (fun k hk => (hC1.2.1 k hk).1) hT hmem
    rw [hgk]
    exact (hC1.2.1 k hk).2
  have htC : t ∈ closure cs := hmemC Rt hmemt
  have hxC : x ∈ closure cs := hmemC Rx hmemx
  have quadIn_spec : ∀ {y : Table} {g : Equiv.Perm (Fin n)}, Rep n y g → quadIn n tT xT y = true →
      g = 1 ∨ g = t ∨ g = x ∨ g = t * x := by
    intro y g Ry hq
    simp only [quadIn, Bool.or_eq_true] at hq
    rcases hq with ((hq | hq) | hq) | hq
    · left; exact (tblEq_iff_eq Ry (Rep.idT hn)).1 hq
    · right; left; exact (tblEq_iff_eq Ry Rt).1 hq
    · right; right; left; exact (tblEq_iff_eq Ry Rx).1 hq
    · right; right; right; exact (tblEq_iff_eq Ry (Rep.compT Rt Rx)).1 hq
  simp only [quadCheck, Array.all_eq_true, Bool.and_eq_true] at hquad
  have hquad' : ∀ c ∈ closure cs, c * c = 1 ∨ c * c = t ∨ c * c = x ∨ c * c = t * x := by
    intro c hc
    obtain ⟨k, hk, Rk⟩ := hC1.2.2.1 c hc
    have hq := (hquad k hk).1.2
    rw [getElem!_pos _ k hk] at Rk
    exact quadIn_spec (Rep.compT Rk Rk) hq
  have hcomm' : ∀ c ∈ closure cs, ∀ d ∈ closure cs, c * d * c⁻¹ * d⁻¹ = 1 ∨
      c * d * c⁻¹ * d⁻¹ = t ∨ c * d * c⁻¹ * d⁻¹ = x ∨ c * d * c⁻¹ * d⁻¹ = t * x := by
    intro c hc d hd
    obtain ⟨k, hk, Rk⟩ := hC1.2.2.1 c hc
    obtain ⟨l, hl, Rl⟩ := hC1.2.2.1 d hd
    rw [getElem!_pos _ k hk] at Rk
    rw [getElem!_pos _ l hl] at Rl
    have hk1 := (hquad k hk).1.1
    have hl1 := (hquad l hl).1.1
    have hq := (hquad k hk).2 l hl
    have Rki := rep_invT Rk hk1
    have Rli := rep_invT Rl hl1
    have := quadIn_spec (Rep.compT (Rep.compT Rk Rl) (Rep.compT Rki Rli)) hq
    simpa only [mul_assoc] using this
  refine ⟨htP, hbP, ?_⟩
  exact S16Model.of_realization hPR e he htP hbP hrR hrP hvP hxP hr2 r_t r_b v_t x_t v4 v8 hx2
    x_ne_one x_ne_t x_v r_v r_x v_b x_b roots hrootmem (hroot htP) hE1card hCEcard hCE hY cs
    (fun c hc => (hcsprop c hc).1) (fun c hc => (hcsprop c hc).2.1)
    (fun c hc => (hcsprop c hc).2.2) hC32 htC hxC hquad' hcomm'

end CFSG.EvenSporadicStandard.Fin76b.S16
