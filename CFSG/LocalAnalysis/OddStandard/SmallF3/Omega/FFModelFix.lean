module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimCard
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_piOrth_not_mem_omega (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) : piOrth Q ∉ omegaGroup hQ := by
  exact ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn

theorem ff_fixSub_orthToSim (t : OGroup Q) :
    fixSub (simAct Q (orthToSim Q t)) = Subgroup.centralizer ({t} : Set (OGroup Q)) := by
  ext g
  rw [mem_fixSub_iff, simAct_orthToSim, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * t = (t * g * t⁻¹) * t := by rw [h]
      _ = t * g := by group
  · intro h
    calc t * g * t⁻¹ = (g * t) * t⁻¹ := by rw [h]
      _ = g := by group

theorem ff_mem_ffFix_sim_iff (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (ρ : ↥(simGroup Q)) (w : ↥(omegaProj hQ)) :
    w ∈ ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q) ↔
      ∃ g ∈ omegaGroup hQ ⊓ fixSub (simAct Q ρ), toProj Q g = (w : ProjOrth Q) := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hπ := ff_piOrth_not_mem_omega hQ hdim hsgn
  obtain ⟨w, hw⟩ := w
  obtain ⟨g₀, hg₀, rfl⟩ := (mem_omegaProj_iff hQ).mp hw
  constructor
  · intro hfix
    have h1 : toProj Q (simAct Q ρ g₀) = toProj Q g₀ := by
      have h0 := congrArg Subtype.val (mem_fixSub_iff.mp hfix)
      rwa [coe_ffSimOmegaAct, projSimAct_mk, projActAux_toProj] at h0
    have h3 : (simAct Q ρ g₀)⁻¹ * g₀ ∈ piGroup Q := QuotientGroup.eq.mp h1
    rcases mem_piGroup_iff.mp h3 with h4 | h4
    · exact ⟨g₀, Subgroup.mem_inf.mpr ⟨hg₀, mem_fixSub_iff.mpr (inv_mul_eq_one.mp h4)⟩, rfl⟩
    · exfalso
      apply hπ
      rw [← h4]
      exact mul_mem (inv_mem (ff_simAct_mem_omegaGroup hQ h2 ρ hg₀)) hg₀
  · rintro ⟨g, hg, hgw⟩
    apply mem_fixSub_iff.mpr
    apply Subtype.ext
    rw [coe_ffSimOmegaAct, projSimAct_mk, ← hgw, projActAux_toProj,
      mem_fixSub_iff.mp (Subgroup.mem_inf.mp hg).2]

theorem ff_fixEquiv_sim (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (ρ : ↥(simGroup Q)) :
    ∃ e : ↥(omegaGroup hQ ⊓ fixSub (simAct Q ρ)) ≃*
        ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)),
      ∀ g, (((e g : ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q))) :
        ↥(omegaProj hQ)) : ProjOrth Q) = toProj Q (g : OGroup Q) := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hπ := ff_piOrth_not_mem_omega hQ hdim hsgn
  let f1 : ↥(omegaGroup hQ ⊓ fixSub (simAct Q ρ)) →* ↥(omegaProj hQ) :=
    ((toProj Q).comp (Subgroup.subtype _)).codRestrict (omegaProj hQ) (fun c =>
      (mem_omegaProj_iff hQ).mpr ⟨c, (Subgroup.mem_inf.mp c.2).1, rfl⟩)
  have hmem : ∀ c, f1 c ∈ ffFix hQ h2 (QuotientGroup.mk ρ : ProjSim Q) := fun c =>
    (ff_mem_ffFix_sim_iff hQ hdim hsgn ρ (f1 c)).mpr ⟨c, c.2, rfl⟩
  let f0 : ↥(omegaGroup hQ ⊓ fixSub (simAct Q ρ)) →*
      ↥(ffFix hQ h2 (QuotientGroup.mk ρ : ProjSim Q)) := f1.codRestrict _ hmem
  have hinj : Function.Injective f0 := by
    intro c c' h
    have h1 : toProj Q (c : OGroup Q) = toProj Q (c' : OGroup Q) :=
      congrArg (fun z : ↥(ffFix hQ h2 (QuotientGroup.mk ρ : ProjSim Q)) =>
        ((z : ↥(omegaProj hQ)) : ProjOrth Q)) h
    have h3 : (c : OGroup Q)⁻¹ * (c' : OGroup Q) ∈ piGroup Q := QuotientGroup.eq.mp h1
    rcases mem_piGroup_iff.mp h3 with h4 | h4
    · exact Subtype.ext (inv_mul_eq_one.mp h4)
    · exfalso
      apply hπ
      rw [← h4]
      exact mul_mem (inv_mem (Subgroup.mem_inf.mp c.2).1) (Subgroup.mem_inf.mp c'.2).1
  have hsurj : Function.Surjective f0 := by
    intro w
    obtain ⟨g, hg, hgw⟩ := (ff_mem_ffFix_sim_iff hQ hdim hsgn ρ w).mp w.2
    exact ⟨⟨g, hg⟩, Subtype.ext (Subtype.ext hgw)⟩
  exact ⟨MulEquiv.ofBijective f0 ⟨hinj, hsurj⟩, fun g => rfl⟩

theorem ff_mem_ffFix_iff (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1) (w : ↥(omegaProj hQ)) :
    w ∈ ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t)) ↔
      ∃ g ∈ omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q)),
        toProj Q g = (w : ProjOrth Q) := by
  have hx : projOrthToProjSim Q (toProj Q t) = QuotientGroup.mk (orthToSim Q t) := rfl
  rw [hx, ff_mem_ffFix_sim_iff hQ hdim hsgn (orthToSim Q t) w, ff_fixSub_orthToSim]

theorem ff_fixEquiv (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1) :
    ∃ e : ↥(omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q))) ≃*
        ↥(ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t))),
      ∀ g, (((e g : ↥(ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t)))) :
        ↥(omegaProj hQ)) : ProjOrth Q) = toProj Q (g : OGroup Q) := by
  have hx : projOrthToProjSim Q (toProj Q t) = QuotientGroup.mk (orthToSim Q t) := rfl
  obtain ⟨e, he⟩ := ff_fixEquiv_sim hQ hdim hsgn (orthToSim Q t)
  rw [hx]
  refine ⟨(MulEquiv.subgroupCongr (by rw [ff_fixSub_orthToSim])).trans e, fun g => ?_⟩
  exact he _

theorem ff_mem_X_of_simple {G : Type} [Group G] (C E : Subgroup G) [Finite E] (hEC : E ≤ C)
    (hS : IsSimpleGroup ↥E) (hnc : ∃ a b : ↥E, a * b ≠ b * a) {w : G} (hw : w ∈ E)
    (hw2 : w * w = 1) : w ∈ twoPrimeRes (twoRes C) := by
  classical
  haveI := hS
  let S : Set ↥E := {g | Odd (orderOf g)}
  let K : Subgroup ↥E := Subgroup.closure S
  have hKnorm : K.Normal := by
    refine ⟨fun n hn k => ?_⟩
    have hmap : K.map (MulAut.conj k).toMonoidHom ≤ K := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨g, hg, rfl⟩
      have h1 := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective g
      show Odd (orderOf ((MulAut.conj k).toMonoidHom g))
      rw [h1]; exact hg
    exact hmap (Subgroup.mem_map.mpr ⟨n, hn, by simp⟩)
  have hKne : K ≠ ⊥ := by
    intro hbot
    have hS1 : ∀ g ∈ S, g = 1 := by
      intro g hg
      have : g ∈ K := Subgroup.subset_closure hg
      rw [hbot] at this
      exact this
    obtain ⟨k, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd
      (n := Nat.card ↥E) Nat.card_pos.ne'
    by_cases hm1 : m = 1
    · have hp : IsPGroup 2 ↥E := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact IsPGroup.of_card (by rw [hcard, hm1, mul_one])
      haveI : Group.IsNilpotent ↥E := hp.isNilpotent
      obtain ⟨a, b, hab⟩ := hnc
      exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := ↥E)).mpr inferInstance a b)
    · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
      haveI : Fact p.Prime := ⟨hp⟩
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hpm)
      have hdvd : p ∣ Nat.card ↥E := by
        rw [hcard]; exact dvd_mul_of_dvd_right hpm _
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
      have hgS : g ∈ S := by
        show Odd (orderOf g)
        rw [hg]; exact hp.odd_of_ne_two hp2
      have := hS1 g hgS
      rw [this, orderOf_one] at hg
      exact hp.one_lt.ne hg
  haveI := hKnorm
  have hKtop : K = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal K).resolve_left hKne
  have hall : ∀ x ∈ K, ((x : ↥E) : G) ∈ twoRes C := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => ((x : ↥E) : G) ∈ twoRes C)
      ?_ ?_ ?_ ?_ hx
    · intro g hg
      refine Subgroup.subset_closure ⟨hEC g.2, ?_⟩
      show Odd (orderOf ((g : ↥E) : G))
      rw [Subgroup.orderOf_coe]
      exact hg
    · exact (twoRes C).one_mem
    · intro y z _ _ hy hz
      exact (twoRes C).mul_mem hy hz
    · intro y _ hy
      exact (twoRes C).inv_mem hy
  have hwR : w ∈ twoRes C := hall ⟨w, hw⟩ (by rw [hKtop]; exact Subgroup.mem_top _)
  by_cases hw1 : w = 1
  · rw [hw1]; exact (twoPrimeRes (twoRes C)).one_mem
  · have hw2' : w ^ 2 = 1 := by rw [pow_two]; exact hw2
    have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hw2'
    have hord : orderOf w = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hw1
      · exact h
    exact Subgroup.subset_closure ⟨hwR, 1, by rw [hord]; rfl⟩

theorem ff_layerModel_congr {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {t : CFSG.Open.StatedLieTag} {n k : ℕ} (h : LayerModel A t n k) : LayerModel B t n k := by
  obtain ⟨E, hE, hlie, hp⟩ := h
  haveI hE' : (E.map e.toMonoidHom).Normal := hE.map e.toMonoidHom e.surjective
  refine ⟨E.map e.toMonoidHom, hE',
    CFSG.Blueprint.LieModel.of_mulEquiv (e.subgroupMap E) hlie, ?_⟩
  refine hp.of_surjective (QuotientGroup.map E (E.map e.toMonoidHom) e.toMonoidHom
    (fun x hx => Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)) (fun y => ?_)
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨a, rfl⟩ := e.surjective b
  exact ⟨QuotientGroup.mk a, rfl⟩

theorem ff_solvable_congr {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : Group.IsSolvable A) : Group.IsSolvable B := by
  haveI := h
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

end CFSG.OddStandard.SmallF3.Omega
