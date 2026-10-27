module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFieldModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutMono

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

private theorem sec8t84tw_isSylow2Of_normalizer {H : Type} [Group H] {P B : Subgroup H}
    (hP : IsSylow2Of P ⊤) (hNB : P ≤ Subgroup.normalizer (B : Set H)) :
    IsSylow2Of P (Subgroup.normalizer (B : Set H)) := by
  refine ⟨hNB, hP.2.1, ?_⟩
  intro hdvd
  apply hP.2.2
  have hrel := Subgroup.relIndex_mul_relIndex (H := P)
    (K := Subgroup.normalizer (B : Set H)) (L := ⊤) hNB le_top
  rw [← hrel]
  exact dvd_mul_of_dvd_left hdvd _

private theorem sec8t84tw_map_conj_eq_self {H : Type} [Group H] {a : H} {U : Subgroup H}
    (ha : a ∈ Subgroup.normalizer (U : Set H)) :
    U.map (MulAut.conj a).toMonoidHom = U := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp ha u).mp hu
  · intro hx
    refine ⟨a⁻¹ * x * a, (Subgroup.mem_normalizer_iff.mp ha (a⁻¹ * x * a)).mpr ?_, ?_⟩
    · rw [show a * (a⁻¹ * x * a) * a⁻¹ = x by group]
      exact hx
    · show MulAut.conj a (a⁻¹ * x * a) = x
      rw [MulAut.conj_apply]
      group

private theorem sec8t84tw_map_conj_eq_of_iff {H : Type} [Group H] {a : H} {U Q : Subgroup H}
    (h : ∀ x : H, x ∈ Q ↔ a⁻¹ * x * a ∈ U) :
    U.map (MulAut.conj a).toMonoidHom = Q := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine (h (a * u * a⁻¹)).mpr ?_
    rwa [show a⁻¹ * (a * u * a⁻¹) * a = u by group]
  · intro hx
    refine ⟨a⁻¹ * x * a, (h x).mp hx, ?_⟩
    show MulAut.conj a (a⁻¹ * x * a) = x
    rw [MulAut.conj_apply]
    group

private theorem sec8t84tw_act_omega {hQ : Q.Nondegenerate}
    {h2 : 2 ≤ Module.finrank (ZMod 3) V} (a : ↥(omegaProj hQ)) :
    ffSimOmegaAct hQ h2 (ffOmegaToSim hQ a) = MulAut.conj a := by
  apply MulEquiv.ext; intro w
  apply ffOmegaToSim_injective hQ
  rw [ff_omegaToSim_act, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem sec8t84tw_adapt [Finite G] (hL : IsOm6M L) {P B : Subgroup G} (hP : IsSylow2Of P L)
    (hB : IsNormalE16In P B) {hQ : Q.Nondegenerate} (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hxx : x * x = 1)
    (hxG : ¬ SimInGStar x) :
    ∃ (e' : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (fr : NFrame Q (Fin 6) 1) (x' : ProjSim Q),
      ffImg (ff6mPhi e') B = ffB1 hQ fr ∧ ffImg (ff6mPhi e') P = ffP1 hQ fr ∧
        InducesViaP L (Subgroup.center ↥L) hQ e' s x' ∧ x' * x' = 1 ∧ ¬ SimInGStar x' := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  have hodd := ff6m_odd_center hL
  have hBL : B ≤ L := hB.1.trans hP.1
  obtain ⟨y, hy⟩ := ff_adapt_exists hQ hdim hsgn h2 e hodd fr hBL hB.2.1
  have hφ : OddCentralCover (ff6mPhi (ffAdapt h2 e y)) := ff6m_phi_cover _ hodd
  have hP1 := ffP1_sylow hQ hdim hsgn fr
  have hQ1 := ff_cover_isSylow2Of hφ hP
  have hNE : IsNormalE16In (ffImg (ff6mPhi (ffAdapt h2 e y)) P) (ffB1 hQ fr) := by
    have h := (ff_cover_normalE16_iff hφ hP.1 hP.2.1 hB.1).mp hB
    rwa [hy] at h
  have hP1N : IsSylow2Of (ffP1 hQ fr)
      (Subgroup.normalizer (ffB1 hQ fr : Set ↥(omegaProj hQ))) :=
    sec8t84tw_isSylow2Of_normalizer hP1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (ffB1_le_ffP1 hQ fr)).mp
        (ffB1_normalE16 hQ hdim hsgn fr).2.2)
  have hQ1N : IsSylow2Of (ffImg (ff6mPhi (ffAdapt h2 e y)) P)
      (Subgroup.normalizer (ffB1 hQ fr : Set ↥(omegaProj hQ))) :=
    sec8t84tw_isSylow2Of_normalizer hQ1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hNE.1).mp hNE.2.2)
  obtain ⟨a, haN, hcond⟩ := IsSylow2Of.exists_conj_mem hP1N hQ1N
  have hact : ffSimOmegaAct hQ h2 (ffOmegaToSim hQ a) = MulAut.conj a :=
    sec8t84tw_act_omega a
  have hPmap : ffImg (ff6mPhi (ffAdapt h2 e y)) P =
      (ffP1 hQ fr).map (ffSimOmegaAct hQ h2 (ffOmegaToSim hQ a)).toMonoidHom := by
    rw [hact]
    exact (sec8t84tw_map_conj_eq_of_iff hcond).symm
  have hBmap : ffImg (ff6mPhi (ffAdapt h2 e y)) B =
      (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 (ffOmegaToSim hQ a)).toMonoidHom := by
    rw [hact, sec8t84tw_map_conj_eq_self haN, hy]
  refine ⟨ffAdapt h2 (ffAdapt h2 e y) (ffOmegaToSim hQ a), fr,
    (y * ffOmegaToSim hQ a)⁻¹ * x * (y * ffOmegaToSim hQ a), ?_, ?_, ?_, ?_, ?_⟩
  · exact ffImg_ffAdapt h2 (ffAdapt h2 e y) (ffOmegaToSim hQ a) B (ffB1 hQ fr) hBmap
  · exact ffImg_ffAdapt h2 (ffAdapt h2 e y) (ffOmegaToSim hQ a) P (ffP1 hQ fr) hPmap
  · have h := inducesViaP_ffAdapt h2 (ffAdapt h2 e y) (ffOmegaToSim hQ a)
      (inducesViaP_ffAdapt h2 e y hs)
    rwa [show (ffOmegaToSim hQ a)⁻¹ * (y⁻¹ * x * y) * ffOmegaToSim hQ a =
      (y * ffOmegaToSim hQ a)⁻¹ * x * (y * ffOmegaToSim hQ a) by group] at h
  · calc (y * ffOmegaToSim hQ a)⁻¹ * x * (y * ffOmegaToSim hQ a) *
          ((y * ffOmegaToSim hQ a)⁻¹ * x * (y * ffOmegaToSim hQ a))
        = (y * ffOmegaToSim hQ a)⁻¹ * (x * x) * (y * ffOmegaToSim hQ a) := by group
      _ = 1 := by rw [hxx]; group
  · exact fun h => hxG ((simInGStar_conj_iff x (y * ffOmegaToSim hQ a)).mp h)

private theorem sec8t84tw_inducesViaP_inv {hQ : Q.Nondegenerate}
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) :
    InducesViaP L (Subgroup.center ↥L) hQ e s⁻¹ x⁻¹ := by
  refine ⟨(Subgroup.normalizer (L : Set G)).inv_mem hs.1, ?_⟩
  intro l l' hl'
  have hl : (l : G) = s * (l' : G) * s⁻¹ := by rw [hl']; group
  have h := hs.2 l' l hl
  rw [h, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem sec8t84tw_mem_map_iff {hQ : Q.Nondegenerate}
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {B : Subgroup G}
    {U : Subgroup ↥(omegaProj hQ)} (hU : ffImg (ff6mPhi e) B = U) {z : ProjSim Q} :
    z ∈ U.map (ffOmegaToSim hQ) ↔
      ∃ l : ↥L, (l : G) ∈ B ∧ ffOmegaToSim hQ (ff6mPhi e l) = z := by
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← hU] at hw
    obtain ⟨l, hl, rfl⟩ := mem_ffImg_iff.mp hw
    exact ⟨l, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    refine Subgroup.mem_map.mpr ⟨ff6mPhi e l, ?_, rfl⟩
    rw [← hU]
    exact mem_ffImg_iff.mpr ⟨l, hl, rfl⟩

private theorem sec8t84tw_conj_mem_ffPS {hQ : Q.Nondegenerate}
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    {fr : NFrame Q (Fin 6) 1} {P : Subgroup G} (hPL : P ≤ L)
    (hPfr : ffImg (ff6mPhi e) P = ffP1 hQ fr) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hsP : s ∈ Subgroup.normalizer (P : Set G)) {h : ProjSim Q} (hh : h ∈ ffPS hQ fr) :
    x * h * x⁻¹ ∈ ffPS hQ fr := by
  obtain ⟨l, hlP, rfl⟩ := (sec8t84tw_mem_map_iff hPfr).mp hh
  have hl'P : s * (l : G) * s⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hsP (l : G)).mp hlP
  let l' : ↥L := ⟨s * (l : G) * s⁻¹, hPL hl'P⟩
  have hact := ff6m_phi_conj hQ h2 e hs l l' rfl
  have hconj : x * ffOmegaToSim hQ (ff6mPhi e l) * x⁻¹ = ffOmegaToSim hQ (ff6mPhi e l') := by
    rw [← ff_omegaToSim_act hQ h2 x, hact]
  rw [hconj]
  exact (sec8t84tw_mem_map_iff hPfr).mpr ⟨l', hl'P, rfl⟩

theorem sec8t84tw_mem_normalizer {hQ : Q.Nondegenerate}
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    {fr : NFrame Q (Fin 6) 1} {P : Subgroup G} (hPL : P ≤ L)
    (hPfr : ffImg (ff6mPhi e) P = ffP1 hQ fr) {γ : G}
    (hγP : γ ∈ Subgroup.normalizer (P : Set G)) {x : ProjSim Q}
    (hx : InducesViaP L (Subgroup.center ↥L) hQ e γ x) :
    x ∈ Subgroup.normalizer (ffPS hQ fr : Set (ProjSim Q)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => sec8t84tw_conj_mem_ffPS h2 hPL hPfr hx hγP hh
  · intro hh
    have hγinv : γ⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
      (Subgroup.normalizer (P : Set G)).inv_mem hγP
    have h1 := sec8t84tw_conj_mem_ffPS h2 hPL hPfr (sec8t84tw_inducesViaP_inv hx) hγinv hh
    rwa [show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h by group] at h1

theorem sec8t84tw_cent_model {hQ : Q.Nondegenerate} (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} (hφ : OddCentralCover (ff6mPhi e))
    {P : Subgroup G} (hPL : P ≤ L) (hP2 : IsPGroup 2 P) {g : G} {y : ProjSim Q}
    (hy : InducesViaP L (Subgroup.center ↥L) hQ e g y)
    (hgP : g ∈ Subgroup.normalizer (P : Set G)) (l : ↥L) (hl : (l : G) ∈ P) :
    (l : G) ∈ Subgroup.centralizer ({g} : Set G) ↔
      y * ffOmegaToSim hQ (ff6mPhi e l) = ffOmegaToSim hQ (ff6mPhi e l) * y := by
  have hl'P : g * (l : G) * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hgP (l : G)).mp hl
  let l' : ↥L := ⟨g * (l : G) * g⁻¹, hPL hl'P⟩
  have hconj : y * ffOmegaToSim hQ (ff6mPhi e l) * y⁻¹ = ffOmegaToSim hQ (ff6mPhi e l') := by
    rw [← ff_omegaToSim_act hQ h2 y, ff6m_phi_conj hQ h2 e hy l l' rfl]
  have e1 : y * ffOmegaToSim hQ (ff6mPhi e l) = ffOmegaToSim hQ (ff6mPhi e l) * y ↔
      y * ffOmegaToSim hQ (ff6mPhi e l) * y⁻¹ = ffOmegaToSim hQ (ff6mPhi e l) :=
    mul_inv_eq_iff_eq_mul.symm
  rw [e1, hconj, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc
    have h1 : g * (l : G) = (l : G) * g := hc g (Set.mem_singleton g)
    have hll : l' = l := by
      apply Subtype.ext
      show g * (l : G) * g⁻¹ = (l : G)
      rw [h1]; group
    rw [hll]
  · intro h
    have hφeq : ff6mPhi e l' = ff6mPhi e l := ffOmegaToSim_injective hQ h
    have heq : l' = l := ff_cover_eq_of_pGroup hφ hP2 hl'P hl hφeq
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    rw [hc]
    have hgl : g * (l : G) * g⁻¹ = (l : G) := congrArg Subtype.val heq
    calc g * (l : G) = g * (l : G) * g⁻¹ * g := by group
      _ = (l : G) * g := by rw [hgl]

theorem sec8t84tw_transfer {H : Type} [Group H] {P C : Subgroup G} (ψ : ↥L →* H)
    (hPL : P ≤ L) (hCP : C ≤ P)
    (hinj : ∀ a b : ↥L, (a : G) ∈ P → (b : G) ∈ P → ψ a = ψ b → a = b) {T : Set H}
    (hT : ∀ l : ↥L, (l : G) ∈ P → ((l : G) ∈ C ↔ ψ l ∈ T))
    (hsurj : ∀ z ∈ T, ∃ l : ↥L, (l : G) ∈ P ∧ ψ l = z)
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hsq : ∀ a ∈ T, a * a = 1) :
    Nat.card C = T.ncard ∧ CFSG.Open.IsElemAbelian 2 C := by
  have hCL : ∀ c : ↥C, (c : G) ∈ L := fun c => hPL (hCP c.2)
  let f : ↥C → ↥T := fun c =>
    ⟨ψ ⟨(c : G), hCL c⟩, (hT _ (hCP c.2)).mp c.2⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      have hψ : ψ ⟨(a : G), hCL a⟩ = ψ ⟨(b : G), hCL b⟩ := congrArg Subtype.val hab
      have h3 := hinj _ _ (hCP a.2) (hCP b.2) hψ
      exact Subtype.ext (Subtype.mk.inj h3)
    · rintro ⟨z, hz⟩
      obtain ⟨l, hlP, hlz⟩ := hsurj z hz
      have hlC : (l : G) ∈ C := (hT l hlP).mpr (by rw [hlz]; exact hz)
      exact ⟨⟨(l : G), hlC⟩, Subtype.ext hlz⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.ofBijective f hf)
  · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have haT : ψ ⟨(a : G), hCL a⟩ ∈ T := (hT _ (hCP a.2)).mp a.2
    have hbT : ψ ⟨(b : G), hCL b⟩ ∈ T := (hT _ (hCP b.2)).mp b.2
    have hψ : ψ (⟨(a : G), hCL a⟩ * ⟨(b : G), hCL b⟩) =
        ψ (⟨(b : G), hCL b⟩ * ⟨(a : G), hCL a⟩) := by
      rw [map_mul, map_mul]
      exact hcomm _ haT _ hbT
    have h3 := hinj _ _ (P.mul_mem (hCP a.2) (hCP b.2)) (P.mul_mem (hCP b.2) (hCP a.2)) hψ
    have h4 := congrArg Subtype.val h3
    exact h4
  · intro x hx
    have hxT : ψ ⟨(x : G), hCL ⟨x, hx⟩⟩ ∈ T := (hT _ (hCP hx)).mp hx
    have hψ : ψ (⟨(x : G), hCL ⟨x, hx⟩⟩ * ⟨(x : G), hCL ⟨x, hx⟩⟩) = ψ 1 := by
      rw [map_mul, map_one]
      exact hsq _ hxT
    have := hinj _ 1 (P.mul_mem (hCP hx) (hCP hx)) P.one_mem hψ
    rw [pow_two]
    exact congrArg Subtype.val this

end CFSG.OddStandard.SmallF3.Omega
