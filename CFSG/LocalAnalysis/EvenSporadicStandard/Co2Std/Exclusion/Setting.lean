module

public import CFSG.Sporadic.Co2Jc.JcFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Hyp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Jc

private noncomputable def conjAut {H : Type} [Group H] (k : H) : H ≃* H :=
  @MulAut.conj H ‹Group H› k

private theorem isSylow_map_subgroupOf {G H : Type} [Group G] [Group H] {L SL : Subgroup G}
    {e : ↥L ≃* H} (hSL : SL ≤ L)
    (hmax : ∀ R : Subgroup G, R ≤ L → IsPGroup 2 R → SL ≤ R → R = SL) :
    ∀ R : Subgroup H, IsPGroup 2 R → (SL.subgroupOf L).map (e : ↥L →* H) ≤ R →
      R = (SL.subgroupOf L).map (e : ↥L →* H) := by
  intro R hRp hle
  have hR'p : IsPGroup 2 (R.comap (e : ↥L →* H)) :=
    hRp.comap_of_injective (e : ↥L →* H) e.injective
  have hR''p : IsPGroup 2 ((R.comap (e : ↥L →* H)).map L.subtype) := hR'p.map L.subtype
  have hSLle : SL ≤ (R.comap (e : ↥L →* H)).map L.subtype := by
    rintro s hs
    exact ⟨⟨s, hSL hs⟩, hle (Subgroup.mem_map_of_mem (e : ↥L →* H) (by exact hs)), rfl⟩
  have hR'' : (R.comap (e : ↥L →* H)).map L.subtype = SL :=
    hmax _ (by rintro _ ⟨y, -, rfl⟩; exact y.2) hR''p hSLle
  ext r
  constructor
  · intro hr
    have hxR : e.symm r ∈ R.comap (e : ↥L →* H) := by
      rw [Subgroup.mem_comap]
      simpa using hr
    have hxSL : ((e.symm r : ↥L) : G) ∈ SL := by
      rw [← hR'']
      exact Subgroup.mem_map_of_mem L.subtype hxR
    have hxSL' : e.symm r ∈ SL.subgroupOf L := Subgroup.mem_subgroupOf.mpr hxSL
    simpa using Subgroup.mem_map_of_mem (e : ↥L →* H) hxSL'
  · intro hr
    exact hle hr

private theorem exists_iso {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {SL : Subgroup G} {Jc T0 : Subgroup Co2} {tA : ↥Jc}
    (hset : TwoCentralSetting G L z t SL) (hL : IsSporadic L .Co2) (hJc_le : Jc ≤ T0)
    (hT0p : IsPGroup 2 T0)
    (hT0max : ∀ R : Subgroup Co2, IsPGroup 2 R → T0 ≤ R → R = T0)
    (hcomm : ∀ s ∈ T0, s * (tA : Co2) = (tA : Co2) * s) (htA1 : (tA : Co2) ≠ 1) :
    ∃ φ : ↥L ≃* Co2, (∀ x : ↥L, (x : G) ∈ SL ↔ φ x ∈ T0) ∧
      φ ⟨t, hset.t_mem⟩ = (tA : Co2) := by
  obtain ⟨e₀⟩ := hL
  let e : ↥L ≃* Co2 := e₀
  let SL' : Subgroup Co2 := (SL.subgroupOf L).map (e : ↥L →* Co2)
  have hSL'p : IsPGroup 2 SL' :=
    (hset.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hset.le).symm).of_equiv
      (Subgroup.equivMapOfInjective (SL.subgroupOf L) (e : ↥L →* Co2) e.injective)
  have hSL'max : ∀ R : Subgroup Co2, IsPGroup 2 R → SL' ≤ R → R = SL' :=
    isSylow_map_subgroupOf hset.le hset.maximal
  let hSL'sylow : Sylow 2 Co2 := ⟨SL', hSL'p, fun {R} hR hle => hSL'max R hR hle⟩
  let hT0sylow : Sylow 2 Co2 := ⟨T0, hT0p, fun {_R} hR hT0R => hT0max _ hR hT0R⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 Co2) :=
    Finite.of_injective (fun P : Sylow 2 Co2 => (P : Subgroup Co2))
      (fun _ _ hPQ => Sylow.ext hPQ)
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (M := Co2) hSL'sylow hT0sylow
  have hconj : ((k • hSL'sylow : Sylow 2 Co2) : Subgroup Co2) =
      SL'.map (conjAut k : Co2 →* Co2) := by
    have hcoe : ((hSL'sylow : Sylow 2 Co2) : Subgroup Co2) = SL' := by
      dsimp only [hSL'sylow, SL']
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hcoe]
    rfl
  have hT0 : T0 = SL'.map (conjAut k : Co2 →* Co2) := by
    have hkQ : ((hT0sylow : Sylow 2 Co2) : Subgroup Co2) =
        ((k • hSL'sylow : Sylow 2 Co2) : Subgroup Co2) :=
      (congrArg (fun P : Sylow 2 Co2 => (P : Subgroup Co2)) hk).symm
    have hlocal : ((hT0sylow : Sylow 2 Co2) : Subgroup Co2) =
        SL'.map (conjAut k : Co2 →* Co2) := by
      rw [hkQ]
      exact hconj
    exact hlocal
  have h2 : ∀ x : ↥L, (x : G) ∈ SL ↔ e x ∈ SL' := by
    intro x
    dsimp only [SL']
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      rw [← e.injective hxy]
      exact hy
  have h3 : ∀ y : Co2, y ∈ SL' ↔ (conjAut k) y ∈ T0 := by
    intro y
    rw [hT0, Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨y, hx, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      rwa [show z = y from (conjAut k).injective hzy] at hz
  have htA_mem : (tA : Co2) ∈ T0 := hJc_le tA.2
  let u : ↥L := e.symm ((conjAut k).symm (tA : Co2))
  have hφu : (conjAut k) (e u) = (tA : Co2) := by
    dsimp only [u]
    simp
  have huSL : (u : G) ∈ SL := (h2 u).mpr ((h3 (e u)).mpr (by rw [hφu]; exact htA_mem))
  have hucomm : ∀ s ∈ SL, s * (u : G) = (u : G) * s := by
    intro s hs
    have hsT : (conjAut k) (e ⟨s, hset.le hs⟩) ∈ T0 :=
      (h3 (e ⟨s, hset.le hs⟩)).mp ((h2 _).mp hs)
    have h := hcomm _ hsT
    have heq : (⟨s, hset.le hs⟩ : ↥L) * u = u * ⟨s, hset.le hs⟩ := by
      apply e.injective
      apply (conjAut k).injective
      simp only [map_mul, hφu]
      exact h
    exact congrArg Subtype.val heq
  have hu1 : u ≠ 1 := by
    intro h1
    apply htA1
    rw [← hφu, h1]
    simp
  have hu_eq : (u : G) = t := by
    rcases hset.center_eq (u : G) huSL hucomm with h1 | h1
    · exact absurd (Subtype.ext h1) hu1
    · exact h1
  refine ⟨{ toFun := fun x => (conjAut k) (e x)
            invFun := fun y => e.symm ((conjAut k).symm y)
            left_inv := fun x => by simp
            right_inv := fun y => by simp
            map_mul' := fun x y => by simp [map_mul] }, ?_, ?_⟩
  · intro x
    exact (h2 x).trans (h3 (e x))
  · change (conjAut k) (e ⟨t, hset.t_mem⟩) = (tA : Co2)
    have hsub : (⟨t, hset.t_mem⟩ : ↥L) = u := Subtype.ext (by simpa using hu_eq.symm)
    rw [hsub, hφu]

private theorem exists_jc {G : Type} [Group G] [Finite G] {L SL : Subgroup G} {z t : G}
    {Jc T0 : Subgroup Co2} {tA : ↥Jc} (hset : TwoCentralSetting G L z t SL)
    (hL : IsSporadic L .Co2) (hJc_le : Jc ≤ T0)
    (hT0p : IsPGroup 2 T0)
    (hT0max : ∀ R : Subgroup Co2, IsPGroup 2 R → T0 ≤ R → R = T0)
    (hcomm : ∀ s ∈ T0, s * (tA : Co2) = (tA : Co2) * s)
    (hjc : JcFacts (⊤ : Subgroup Co2) Jc T0 (tA : Co2)) (htA1 : (tA : Co2) ≠ 1) :
    ∃ A : Subgroup G, JcFacts L A SL t := by
  obtain ⟨φ, hT, hφt⟩ := exists_iso hset hL hJc_le hT0p hT0max hcomm htA1
  let A : Subgroup G := (Jc.comap (φ : ↥L →* Co2)).map L.subtype
  have hAL : A ≤ L := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hA : ∀ x : ↥L, (x : G) ∈ A ↔ φ x ∈ Jc := by
    intro x
    dsimp only [A]
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = x := Subtype.ext hxy
      rw [hyx] at hy
      exact Subgroup.mem_comap.mp hy
    · intro hx
      exact ⟨x, Subgroup.mem_comap.mpr hx, rfl⟩
  exact ⟨A, @JcFacts.of_mulEquiv G Co2 _ _ L A SL t Jc T0 (tA : Co2) φ hAL hset.le hset.t_mem
    hA hT hφt hjc⟩

theorem exists_hyp
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) (hL : IsSporadic L .Co2) :
    ∃ (A T : Subgroup G) (z t : G), Hyp G L A T z t := by
  classical
  haveI := h.simple
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic hL
  have hq : IsSporadic (L ⧸ center L) .Co2 := isSporadic_quotient_of_center_eq_bot hZ hL
  have hfull := HypOne.Co2.fullRowData_of_isSporadic hq
  have hinn : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q := by
    obtain ⟨e⟩ := hq
    exact HypOne.forall_eq_conj_of_mulEquiv e.symm HypOne.Co2.allInner_native
  have hS := h.card_sylow_eq_two_of_inner hfull.rowData.hypothesisOne hinn
  obtain ⟨z, hz, hz2⟩ := h.exists_involution_centralizer
  obtain ⟨hC, hd, -⟩ := h.centralizer_eq_prod_of_center_eq_bot hS hz hz2
    (h.centralizer_le_sup_centralizer_of_inner hz hz2 hinn) hZ
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hz2; exact absurd hz2 (by decide)
  obtain ⟨t, SL, hset⟩ := TwoCentralSetting.of_facts hz1 hzz hC hd (co2Facts_of_isSporadic hL)
  obtain ⟨-, hconj⟩ := hset.odd_index_centralizer h.nonabelian
  have hnc : ∀ l ∈ L, ¬ IsConj z l := by
    intro l hl hlz
    have hl2 : l * l = 1 := by
      obtain ⟨g, rfl⟩ := isConj_iff.1 hlz
      calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [hzz]; group
    have hl1 : l ≠ 1 := by
      rintro rfl
      exact hz1 (isConj_one_right.1 hlz.symm)
    obtain ⟨w, -, hw⟩ := hset.sq_of_invol l hl hl2 hl1
    exact not_isConj_of_mem_of_sq hz1 hzz hC hd hw hlz
  have htA1 : (tA : K) ≠ 1 := by
    rw [coe_tA]
    exact z0_ne_one
  obtain ⟨A, hjc⟩ := exists_jc hset hL Jc_le_T0 isPGroup_T0
    (fun R hR hT0R => eq_T0_of_le hR hT0R) (fun s hs => commute_tA_of_mem_T0 hs) jcFacts_T0 htA1
  exact ⟨A, SL, z, t, h, hset, hconj, hnc, hjc⟩

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
