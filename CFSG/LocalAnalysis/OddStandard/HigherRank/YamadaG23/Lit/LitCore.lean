module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitPerf

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {X : Type*} [Group X] [Finite X] {G : Type*} [Group G] [Finite G] {π : X →* G}

private lemma isPerfect_of_isSimpleGroup_of_not_comm {A : Type*} [Group A] (hA : IsSimpleGroup A)
    (hnc : ¬ ∀ a b : A, a * b = b * a) : Group.IsPerfect A := by
  rw [Group.isPerfect_def]
  rcases hA.eq_bot_or_eq_top_of_normal (commutator A) with h | h
  · exfalso
    haveI : IsMulCommutative A := (commutator_eq_bot_iff A).mp h
    exact hnc fun a b => mul_comm a b
  · exact h

private lemma center_eq_bot_of_isSimpleGroup_of_not_comm {A : Type*} [Group A]
    (hA : IsSimpleGroup A) (hnc : ¬ ∀ a b : A, a * b = b * a) : center A = ⊥ := by
  rcases hA.eq_bot_or_eq_top_of_normal (center A) with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative A := center_eq_top_iff.mp h
    exact hnc fun a b => mul_comm a b

private lemma map_symm_map_self {Y : Type*} [Group Y] (e : Y ≃* Y) (K : Subgroup Y) :
    (K.map e.symm.toMonoidHom).map e.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have h : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by
    ext x; simp
  rw [h, Subgroup.map_id]

theorem lit_H_hom {M : Subgroup G} (hMs : IsSimpleGroup ↥M)
    (hMn : ¬ ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) {H : Subgroup X} (hHM : H.map π = M)
    (hcent : ∀ x ∈ H, ∀ y ∈ π.ker, x * y = y * x) :
    ∃ ρ : ↥H →* ↥M, Function.Surjective ρ ∧ (∀ x : ↥H, ((ρ x : ↥M) : G) = π (x : X)) ∧
      ρ.ker = center ↥H := by
  have hncM : ¬ ∀ a b : ↥M, a * b = b * a := by
    intro h
    exact hMn fun a ha b hb => congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩)
  have hcenterM : center ↥M = ⊥ := center_eq_bot_of_isSimpleGroup_of_not_comm hMs hncM
  let ρ : ↥H →* ↥M := (π.domRestrict H).codRestrict M fun x => by
    change π (x : X) ∈ M
    rw [← hHM]
    exact ⟨(x : X), x.2, rfl⟩
  have hρcoe : ∀ x : ↥H, ((ρ x : ↥M) : G) = π (x : X) := fun x => rfl
  have hρsurj : Function.Surjective ρ := by
    intro m
    have hm : (m : G) ∈ H.map π := by rw [hHM]; exact m.2
    obtain ⟨x, hxH, hx⟩ := Subgroup.mem_map.mp hm
    refine ⟨⟨x, hxH⟩, ?_⟩
    apply Subtype.ext
    rw [hρcoe]
    exact hx
  have hρker : ρ.ker = center ↥H := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hx1 : π (x : X) = 1 := by
        have h1 : ρ x = 1 := MonoidHom.mem_ker.mp hx
        have h2 := congrArg (fun z : ↥M => (z : G)) h1
        simpa [hρcoe x] using h2
      exact hcent (y : X) y.2 (x : X) (MonoidHom.mem_ker.mpr hx1)
    · intro hx
      rw [MonoidHom.mem_ker]
      have hmem : ρ x ∈ center ↥M := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨y, hy⟩ := hρsurj g
        rw [← hy, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx) y]
      rw [hcenterM] at hmem
      exact Subgroup.mem_bot.mp hmem
  exact ⟨ρ, hρsurj, hρcoe, hρker⟩

theorem lit_quasisimple {M : Subgroup G} (hMs : IsSimpleGroup ↥M)
    (hMn : ¬ ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) {H : Subgroup X} (hH : ⁅H, H⁆ = H)
    (hHM : H.map π = M) (hcent : ∀ x ∈ H, ∀ y ∈ π.ker, x * y = y * x) :
    CFSG.IsQuasisimple ↥H := by
  obtain ⟨ρ, hρsurj, hρcoe, hρker⟩ := lit_H_hom hMs hMn hHM hcent
  have hHperf : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hH
  let e₁ : ↥H ⧸ ρ.ker ≃* ↥M := QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj
  let e : ↥H ⧸ center ↥H ≃* ↥M :=
    (QuotientGroup.quotientMulEquivOfEq hρker.symm).trans e₁
  refine ⟨hHperf, ?_, ?_⟩
  · exact e.isSimpleGroup_congr.mpr hMs
  · push Not at hMn
    obtain ⟨a, ha, b, hb, hab⟩ := hMn
    refine ⟨e.symm ⟨a, ha⟩, e.symm ⟨b, hb⟩, fun hcon => hab ?_⟩
    have hcon' : (⟨a, ha⟩ : ↥M) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      have := congrArg e hcon
      simpa using this
    exact congrArg Subtype.val hcon'

theorem lit_centralizer_H {M : Subgroup G} (hC : centralizer (M : Set G) = ⊥) {H : Subgroup X}
    (hHM : H.map π = M) (hcent : ∀ x ∈ H, ∀ y ∈ π.ker, x * y = y * x) :
    centralizer (H : Set X) = π.ker := by
  ext c
  constructor
  · intro hc
    rw [MonoidHom.mem_ker]
    have hmem : π c ∈ centralizer (M : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      obtain ⟨x, hxH, rfl⟩ := Subgroup.mem_map.mp (by rw [hHM]; exact hm)
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hc) x hxH]
    rw [hC] at hmem
    exact Subgroup.mem_bot.mp hmem
  · intro hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcent x hx c (MonoidHom.mem_ker.mp hc)

theorem lit_perf_char (hπ : Function.Surjective π) (hsolv : Group.IsSolvable ↥π.ker)
    {M : Subgroup G} [M.Normal] (hMs : IsSimpleGroup ↥M)
    (hMn : ¬ ∀ a ∈ M, ∀ b ∈ M, a * b = b * a)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≠ ⊥ → M ≤ K) :
    (litPerf (M.comap π)).Characteristic := by
  haveI hπker_solv : Group.IsSolvable ↥π.ker := hsolv
  haveI : Nontrivial ↥M := hMs.toNontrivial
  have hncM : ¬ ∀ a b : ↥M, a * b = b * a := by
    intro h
    exact hMn fun a ha b hb => congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩)
  haveI : Group.IsPerfect ↥M := isPerfect_of_isSimpleGroup_of_not_comm hMs hncM
  have hMne : M ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot M).mp inferInstance
  have key : ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N ≤ π.ker := by
    intro N hNn hNsolv
    by_contra hNle
    have hmapne : N.map π ≠ ⊥ := fun h => hNle ((Subgroup.map_eq_bot_iff N).mp h)
    have hmapn : (N.map π).Normal := hNn.map π hπ
    have hMle : M ≤ N.map π := hmin (N.map π) hmapn hmapne
    haveI : Group.IsSolvable ↥N := hNsolv
    haveI : Group.IsSolvable ↥(N.map π) :=
      Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective π N)
    haveI : Group.IsSolvable ↥M :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hMle)
    exact (Group.IsPerfect.not_isSolvable ↥M) inferInstance
  have hPmap_solv : ∀ f : X ≃* X, Group.IsSolvable ↥(π.ker.map f.toMonoidHom) := fun f =>
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective (f : X →* X) π.ker)
  have hPchar : π.ker.Characteristic := by
    refine ⟨fun e => ?_⟩
    rw [Subgroup.comap_equiv_eq_map_symm' e (π.ker)]
    refine Subgroup.eq_of_le_of_card_ge (H := π.ker.map e.symm.toMonoidHom) (K := π.ker) ?_ ?_
    · exact key (π.ker.map e.symm.toMonoidHom)
        ((inferInstance : (π.ker).Normal).map e.symm.toMonoidHom e.symm.surjective)
        (hPmap_solv e.symm)
    · exact le_of_eq (Subgroup.card_map_of_injective e.symm.injective).symm
  have hPmap_all' : ∀ f : X ≃* X, π.ker.map f.toMonoidHom = π.ker := by
    intro f
    have h : (π.ker).comap f.symm.toMonoidHom = π.ker := hPchar.fixed f.symm
    rw [Subgroup.comap_equiv_eq_map_symm' f.symm (π.ker)] at h
    simpa using h
  have hPleK : π.ker ≤ M.comap π := by
    intro y hy
    rw [Subgroup.mem_comap]
    rw [MonoidHom.mem_ker.mp hy]
    exact M.one_mem
  have hKchar : (M.comap π).Characteristic := by
    refine ⟨fun e => ?_⟩
    rw [Subgroup.comap_equiv_eq_map_symm' e (M.comap π)]
    have hPleKmap : π.ker ≤ (M.comap π).map e.symm.toMonoidHom := by
      calc π.ker = (π.ker).map e.symm.toMonoidHom := (hPmap_all' e.symm).symm
        _ ≤ (M.comap π).map e.symm.toMonoidHom := Subgroup.map_mono hPleK
    have hmapne : ((M.comap π).map e.symm.toMonoidHom).map π ≠ ⊥ := by
      intro hbot
      have hleP : (M.comap π).map e.symm.toMonoidHom ≤ π.ker :=
        (Subgroup.map_eq_bot_iff _).mp hbot
      have hKeq : ((M.comap π).map e.symm.toMonoidHom).map e.toMonoidHom = M.comap π :=
        map_symm_map_self e (M.comap π)
      have hKleP : M.comap π ≤ π.ker := by
        calc M.comap π = ((M.comap π).map e.symm.toMonoidHom).map e.toMonoidHom := hKeq.symm
          _ ≤ (π.ker).map e.toMonoidHom := Subgroup.map_mono hleP
          _ = π.ker := hPmap_all' e
      have hMleBot : M ≤ ⊥ := by
        calc M = (M.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπ M).symm
          _ ≤ (π.ker).map π := Subgroup.map_mono hKleP
          _ = ⊥ := Subgroup.map_ker_self π
      exact hMne (le_bot_iff.mp hMleBot)
    have hmapn : (((M.comap π).map e.symm.toMonoidHom).map π).Normal :=
      (((inferInstance : (M.comap π).Normal).map e.symm.toMonoidHom e.symm.surjective)).map π hπ
    have hMle : M ≤ ((M.comap π).map e.symm.toMonoidHom).map π := hmin _ hmapn hmapne
    have hle : M.comap π ≤ (M.comap π).map e.symm.toMonoidHom := by
      calc M.comap π ≤ (((M.comap π).map e.symm.toMonoidHom).map π).comap π :=
            Subgroup.comap_mono hMle
        _ = (M.comap π).map e.symm.toMonoidHom ⊔ π.ker :=
              Subgroup.comap_map_eq π ((M.comap π).map e.symm.toMonoidHom)
        _ = (M.comap π).map e.symm.toMonoidHom := sup_eq_left.mpr hPleKmap
    exact (Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Subgroup.card_map_of_injective e.symm.injective))).symm
  refine ⟨fun e => ?_⟩
  have hKmap : (M.comap π).map e.symm.toMonoidHom = M.comap π := by
    have h : (M.comap π).comap e.toMonoidHom = M.comap π := hKchar.fixed e
    rw [Subgroup.comap_equiv_eq_map_symm' e (M.comap π)] at h
    simpa using h
  rw [Subgroup.comap_equiv_eq_map_symm' e (litPerf (M.comap π))]
  rw [litPerf_map e.symm (M.comap π)]
  rw [hKmap]

end CFSG.OddStandard.HigherRank.YamadaG23
