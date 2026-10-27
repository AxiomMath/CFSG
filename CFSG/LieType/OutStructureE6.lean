module

public import CFSG.LieType.OutStructureA2
public import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalThree
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Diag
public import CFSG.Adapters.TauCetiExceptional.EvenB1

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.Chevalley
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem normal_of_ker_dvd_three
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    (Φ : G →* V) (hDvd : Nat.card Φ.ker ∣ 3)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {P : Subgroup V} (hPN : P.Normal)
    {P0 : Subgroup G} (hP0p : IsPGroup p P0) (hP0map : P0.map Φ = P) :
    P0.Normal := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let D : Subgroup G := Φ.ker
  have hDnormal : D.Normal := inferInstance
  have hDle : Nat.card D ≤ 3 := Nat.le_of_dvd (by norm_num) hDvd
  haveI : IsCyclic D := isCyclic_of_card_dvd_prime (p := 3) hDvd
  have hcardAut2 : Nat.card (MulAut D) ≤ 2 := by
    rw [IsCyclic.card_mulAut]
    rcases (Nat.dvd_prime Nat.prime_three).mp hDvd with h1 | h3
    · rw [h1]
      decide
    · rw [h3]
      decide
  let ψ : P0 →* MulAut D := (MulAut.conjNormal (H := D)).comp P0.subtype
  have hψtriv : ∀ x : P0, ψ x = 1 := by
    intro x
    obtain ⟨k, hk⟩ := hP0p x
    have h1 : (ψ x) ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
    have h2 : orderOf (ψ x) ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf (ψ x) ∣ Nat.card (MulAut D) := orderOf_dvd_natCard _
    have h4 : Nat.Coprime (p ^ k) (Nat.card (MulAut D)) := by
      refine Nat.Coprime.pow_left k ((hp.coprime_iff_not_dvd).mpr ?_)
      intro hpd
      have := Nat.le_of_dvd (Nat.card_pos) hpd
      omega
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h4 h2 h3)
  have hcomm : ∀ d : G, d ∈ D → ∀ x : G, x ∈ P0 → d * x = x * d := by
    intro d hd x hx
    have h := congrArg (fun f : MulAut D => f ⟨d, hd⟩) (hψtriv ⟨x, hx⟩)
    have h1 : ((MulAut.conjNormal (H := D) x) ⟨d, hd⟩ : G) = d := by
      simpa [ψ] using congrArg Subtype.val h
    rw [MulAut.conjNormal_apply] at h1
    have h2 : x * d = d * x := by
      have := congrArg (fun y => y * x) h1
      rwa [mul_assoc, inv_mul_cancel, mul_one] at this
    exact h2.symm
  let N : Subgroup G := P.comap Φ
  have hP0N : P0 ≤ N := by
    intro x hx
    rw [Subgroup.mem_comap, ← hP0map]
    exact Subgroup.mem_map_of_mem Φ hx
  have hNnormal : N.Normal := hPN.comap Φ
  haveI : N.Normal := hNnormal
  have hdecomp : ∀ x : G, x ∈ N → ∃ p ∈ P0, ∃ d ∈ D, x = p * d := by
    intro x hx
    have hx' : Φ x ∈ P := hx
    obtain ⟨p, hpP0, hpmap⟩ := Subgroup.mem_map.mp (show Φ x ∈ P0.map Φ from by rwa [hP0map])
    refine ⟨p, hpP0, p⁻¹ * x, ?_, ?_⟩
    · show Φ (p⁻¹ * x) = 1
      rw [map_mul, map_inv, hpmap, inv_mul_cancel]
    · group
  have hP0normalN : (P0.subgroupOf N).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn x
    have hnP0 : (n : G) ∈ P0 := hn
    obtain ⟨p, hpP0, d, hdD, hxdecomp⟩ := hdecomp x.1 x.2
    have hdn : d * (n : G) * d⁻¹ = (n : G) := by
      rw [hcomm d hdD (n : G) hnP0, mul_inv_cancel_right]
    have hconj : ((x * n * x⁻¹ : N) : G) = p * (n : G) * p⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show (x : N).1 = p * d from hxdecomp, mul_inv_rev,
        show p * d * (n : G) * (d⁻¹ * p⁻¹) = p * (d * (n : G) * d⁻¹) * p⁻¹ by group,
        hdn]
    show ((x * n * x⁻¹ : N) : G) ∈ P0
    rw [hconj]
    exact Subgroup.mul_mem P0 (Subgroup.mul_mem P0 hpP0 hnP0) (Subgroup.inv_mem P0 hpP0)
  have hfker : (Φ.comp N.subtype).ker = D.subgroupOf N := by
    ext x
    simp [D, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hfr : (Φ.comp N.subtype).range = P := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hy
      obtain ⟨p, hpP0, hpmap⟩ := Subgroup.mem_map.mp (show y ∈ P0.map Φ from by rwa [hP0map])
      exact ⟨⟨p, hP0N hpP0⟩, hpmap⟩
  have hcardN : Nat.card N = Nat.card D * Nat.card P := by
    rw [← Subgroup.card_ker_mul_card_range (Φ.comp N.subtype), hfker, hfr,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show D ≤ N from by
        intro x hx
        rw [Subgroup.mem_comap, show Φ x = 1 from hx]
        exact P.one_mem)).toEquiv]
  have hgker : (Φ.comp P0.subtype).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx1 : (x : G) ∈ P0 ⊓ D := ⟨x.2, by simpa [D] using hx⟩
    have hP0infD : P0 ⊓ D = ⊥ := by
      obtain ⟨n, hn⟩ := (hP0p.to_inf_left (K := D)).exists_card_eq
      have hdvd : Nat.card ↥(P0 ⊓ D) ∣ Nat.card D :=
        Subgroup.card_dvd_of_le (inf_le_right : P0 ⊓ D ≤ D)
      have hpnd : ¬ p ∣ Nat.card D := by
        intro h
        have := Nat.le_of_dvd (Nat.card_pos) h
        omega
      have hn0 : n = 0 := by
        by_contra hn0
        apply hpnd
        exact (dvd_pow_self p hn0).trans (hn ▸ hdvd)
      exact Subgroup.card_eq_one.mp (by rw [hn, hn0, pow_zero])
    rw [hP0infD] at hx1
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hx1))
  have hgr : (Φ.comp P0.subtype).range = P := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [← hP0map]
      exact Subgroup.mem_map_of_mem Φ x.2
    · intro hy
      obtain ⟨p, hpP0, hpmap⟩ := Subgroup.mem_map.mp (show y ∈ P0.map Φ from by rwa [hP0map])
      exact ⟨⟨p, hpP0⟩, hpmap⟩
  have hcardP0 : Nat.card P0 = Nat.card P := by
    have h := Subgroup.card_ker_mul_card_range (Φ.comp P0.subtype)
    rw [hgker, hgr, Subgroup.card_bot, one_mul] at h
    exact h.symm
  have hQindex : (P0.subgroupOf N).index = Nat.card D := by
    have hmul : Nat.card (P0.subgroupOf N) * (P0.subgroupOf N).index = Nat.card N :=
      Subgroup.card_mul_index _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP0N).toEquiv, hcardP0, hcardN] at hmul
    rw [mul_comm (Nat.card D) (Nat.card P)] at hmul
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos) hmul
  have hQp : IsPGroup p (P0.subgroupOf N) :=
    hP0p.of_equiv (Subgroup.subgroupOfEquivOfLe hP0N).symm
  have hQindex' : ¬ p ∣ (P0.subgroupOf N).index := by
    rw [hQindex]
    intro h
    have := Nat.le_of_dvd (Nat.card_pos) h
    omega
  let Q : Sylow p N := hQp.toSylow hQindex'
  have hQnormal : (Q : Subgroup N).Normal := hP0normalN
  have hQchar : (Q : Subgroup N).Characteristic := Sylow.characteristic_of_normal Q hQnormal
  refine Subgroup.Normal.mk fun n hn g => ?_
  have hmem : (⟨n, hP0N hn⟩ : N) ∈ (Q : Subgroup N) := hn
  have hfix : (Q : Subgroup N).map (MulAut.conjNormal g).toMonoidHom = (Q : Subgroup N) :=
    (Subgroup.characteristic_iff_map_eq.mp hQchar) (MulAut.conjNormal g)
  have hmapmem : (MulAut.conjNormal g) (⟨n, hP0N hn⟩ : N) ∈ (Q : Subgroup N) := by
    rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hmem
  have hP0mem : ((MulAut.conjNormal g) (⟨n, hP0N hn⟩ : N) : G) ∈ P0 := hmapmem
  rwa [MulAut.conjNormal_apply] at hP0mem

private theorem not_dvd_index_of_card_dvd_six_mul
    {G : Type*} [Group G] [Finite G] {F : Subgroup G} {p f : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f.factorization p)
    (hOut : Nat.card G ∣ 6 * f) : ¬ p ∣ F.index := by
  intro hpd
  have hf0 : f ≠ 0 := by omega
  set a := f.factorization p
  set q := p ^ a
  set m := ordCompl[p] f
  have hqpos : 0 < q := pow_pos hp.pos a
  have hdecomp : f = q * m := by
    rw [show q = ordProj[p] f from rfl, show m = ordCompl[p] f from rfl,
      Nat.ordProj_mul_ordCompl_eq_self f p]
  have hpm : ¬ p ∣ m := by
    simpa [m] using Nat.not_dvd_ordCompl hp hf0
  have hp6 : ¬ p ∣ 6 := by
    intro h
    have h' : p ∣ 2 * 3 := by simpa using h
    rcases hp.dvd_mul.mp h' with h2 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      omega
  have h1 : p ^ (a + 1) ∣ Nat.card F * F.index := by
    rw [hF, pow_succ]
    exact mul_dvd_mul_left (p ^ a) hpd
  have h2 : p ^ (a + 1) ∣ Nat.card G := by
    rwa [← Subgroup.card_mul_index F]
  have h3 : p ^ (a + 1) ∣ 6 * f := h2.trans hOut
  have h4 : q * p ∣ q * (6 * m) := by
    have h3' : p ^ (a + 1) ∣ 6 * f := h3
    rw [hdecomp, pow_succ] at h3'
    simpa [mul_assoc, mul_comm, mul_left_comm] using h3' 
  have h5 : p ∣ 6 * m := Nat.dvd_of_mul_dvd_mul_left hqpos h4
  rcases hp.dvd_mul.mp h5 with h | h
  · exact hp6 h
  · exact hpm h


theorem exists_fieldPart_adjointGroup_E6
    {p₀ f : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = p₀ ^ f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ∃ F : Subgroup (MulAut (adjointGroup Tag.E6 K)),
      (inner (adjointGroup Tag.E6 K) ⊔ F).Normal ∧ IsCyclic ↥F ∧
      F ⊓ inner (adjointGroup Tag.E6 K) = ⊥ ∧
      ¬ p ∣ (inner (adjointGroup Tag.E6 K) ⊔ F).index ∧
      ∀ x : MulAut (adjointGroup Tag.E6 K), (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ inner (adjointGroup Tag.E6 K) ⊔ F := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  set I : Subgroup (MulAut (adjointGroup Tag.E6 K)) := inner _
  obtain ⟨Θ, hΘsurj, hΘform, hΘker, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) (K := K)
  have hkerΘ : ∀ α : MulAut (adjointGroup Tag.E6 K),
      α ∈ Θ.ker ↔ ∃ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ),
        α = MulAut.conj g * rootDiagAut Tag.E6 K a := by
    intro α
    rw [hΘker]
    constructor
    · rintro ⟨g, a, h⟩
      refine ⟨g, a, MulEquiv.ext fun x => Subtype.ext ?_⟩
      rw [h x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
    · rintro ⟨g, a, rfl⟩
      refine ⟨g, a, fun x => ?_⟩
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
  have hrootone : rootDiagAut Tag.E6 K 1 = 1 := (rootDiagAutHom Tag.E6 K).map_one
  have hIker : I ≤ Θ.ker := by
    rintro _ ⟨g, rfl⟩
    exact (hkerΘ _).2 ⟨g, 1, by rw [hrootone, mul_one]⟩
  let Φ : Outer (adjointGroup Tag.E6 K) →*
      (RingAut K × Multiplicative (ZMod (exactE Tag.E6))) :=
    QuotientGroup.lift I Θ hIker
  have hΦsurj : Function.Surjective Φ := fun y => by
    obtain ⟨α, rfl⟩ := hΘsurj y
    exact ⟨α, QuotientGroup.lift_mk _ hIker α⟩
  have hΦker : Φ.ker = ((QuotientGroup.mk' I).comp (rootDiagAutHom Tag.E6 K)).range := by
    refine le_antisymm (fun x hx => ?_) ?_
    · obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective I x
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.lift_mk] at hx
      obtain ⟨g, a, rfl⟩ := (hkerΘ _).1 hx
      refine ⟨a, ?_⟩
      change (QuotientGroup.mk (rootDiagAut Tag.E6 K a) : Outer _) =
        QuotientGroup.mk' I (MulAut.conj g * rootDiagAut Tag.E6 K a)
      rw [map_mul, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff
        (N := I) (MulAut.conj g)).2 (MonoidHom.mem_range.2 ⟨g, rfl⟩), one_mul]
      rfl
    · rintro _ ⟨a, rfl⟩
      change QuotientGroup.lift I Θ hIker (QuotientGroup.mk (rootDiagAut Tag.E6 K a)) = 1
      rw [QuotientGroup.lift_mk]
      exact (hkerΘ _).2 ⟨1, a, by rw [map_one, one_mul]⟩
  have hΦdvd : Nat.card Φ.ker ∣ 3 := by
    obtain ⟨ΦE, -, hΦEker, hΦEdvd⟩ :=
      exists_outer_hom_E (τ := Tag.E6) (Or.inl rfl) (K := K)
    rw [hΦker, ← hΦEker]
    have hdet : Tag.E6.cartan.det.natAbs = 3 := by rw [det_cartan_E6]; rfl
    simpa [hdet] using hΦEdvd
  let E : RingAut K →* MulAut (adjointGroup Tag.E6 K) :=
    { toFun := fun σ => exactNormalAut Tag.E6 K 1 σ 0
      map_one' := exactNormalAut_one_one_zero
      map_mul' := fun σ σ' => (exactNormalAut_one_zero_mul σ σ').symm }
  have hΦE : ∀ σ : RingAut K, Φ (QuotientGroup.mk' I (E σ)) = (σ, 1) := by
    intro σ
    change QuotientGroup.lift I Θ hIker ((QuotientGroup.mk' I) (E σ)) = (σ, 1)
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
    let ε : Fin (exactE Tag.E6) := ⟨0, by decide⟩
    have hε0 : (ε : ℕ) = 0 := rfl
    have hform : ∀ h : adjointGroup Tag.E6 K,
        (E σ h : ModGL Tag.E6 K) =
          ((1 : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) *
            rootDiagUnit Tag.E6 (1 : Fin Tag.E6.rank → Kˣ) * exactQ Tag.E6 K ε *
            Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.E6 K) *
            (exactQ Tag.E6 K ε)⁻¹ * (rootDiagUnit Tag.E6 (1 : Fin Tag.E6.rank → Kˣ))⁻¹ *
            (((1 : adjointGroup Tag.E6 K)) : ModGL Tag.E6 K)⁻¹ := by
      intro h
      change (exactNormalAut Tag.E6 K 1 σ 0 h : ModGL Tag.E6 K) = _
      rw [coe_exactNormalAut_zero]
      simp only [Subgroup.coe_one, rootDiagUnit_one, hε0, exactQ_zero, mul_one, inv_one]
    have h := hΘform (E σ) 1 1 σ ε hform
    simpa [ε] using h
  have hEinj : Function.Injective E := by
    intro σ σ' h
    have h' : Φ (QuotientGroup.mk' I (E σ)) = Φ (QuotientGroup.mk' I (E σ')) := by
      rw [h]
    have h1 : (σ, (1 : Multiplicative (ZMod (exactE Tag.E6)))) =
        (σ', (1 : Multiplicative (ZMod (exactE Tag.E6)))) := by
      rw [hΦE σ, hΦE σ'] at h'
      exact h'
    exact congrArg Prod.fst h1
  haveI : Finite (RingAut K) :=
    Finite.of_injective (fun σ : RingAut K => (σ : K → K)) DFunLike.coe_injective
  haveI : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic hp₀ K hK).2
  have hcardAut : Nat.card (RingAut K) = f := (card_ringAut_and_isCyclic hp₀ K hK).1
  let S : Sylow p (RingAut K) := Classical.choice (Sylow.nonempty)
  let F : Subgroup (MulAut (adjointGroup Tag.E6 K)) := (S : Subgroup (RingAut K)).map E
  have hFp : IsPGroup p F := S.isPGroup'.map E
  have hFcyc : IsCyclic ↥F := by
    have hScyc : IsCyclic ↥(S : Subgroup (RingAut K)) := Subgroup.isCyclic _
    exact (Subgroup.equivMapOfInjective (S : Subgroup (RingAut K)) E hEinj).isCyclic.mp hScyc
  have hFcardS : Nat.card (S : Subgroup (RingAut K)) =
      p ^ f.factorization p := by
    rw [Sylow.card_eq_multiplicity, hcardAut]
  have hFcard : Nat.card F = p ^ f.factorization p := by
    rw [show F = (S : Subgroup (RingAut K)).map E from rfl,
      Subgroup.card_map_of_injective hEinj, hFcardS]
  have hFbot : F ⊓ I = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxF, hxI⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp hxF
    have h1 : (QuotientGroup.mk' I (E σ) : Outer _) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hxI
    have h2 : (σ, (1 : Multiplicative (ZMod (exactE Tag.E6)))) = 1 := by
      calc (σ, (1 : Multiplicative (ZMod (exactE Tag.E6)))) =
          Φ (QuotientGroup.mk' I (E σ)) := (hΦE σ).symm
        _ = Φ 1 := congrArg Φ h1
        _ = 1 := map_one Φ
    have hσ : σ = 1 := congrArg Prod.fst h2
    rw [Subgroup.mem_bot, hσ, map_one]
  let mk : MulAut (adjointGroup Tag.E6 K) →* Outer (adjointGroup Tag.E6 K) :=
    QuotientGroup.mk' I
  let P_out : Subgroup (Outer (adjointGroup Tag.E6 K)) := F.map mk
  let P_V : Subgroup (RingAut K × Multiplicative (ZMod (exactE Tag.E6))) :=
    (S : Subgroup (RingAut K)).map (MonoidHom.inl _ _)
  haveI : Finite (RingAut K × Multiplicative (ZMod (exactE Tag.E6))) := by
    have : Finite (Multiplicative (ZMod (exactE Tag.E6))) :=
      Nat.finite_of_card_ne_zero (by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
        decide)
    infer_instance
  haveI : IsMulCommutative (RingAut K) := IsCyclic.isMulCommutative
  have hPVnormal : P_V.Normal := inferInstance
  have hP0p : IsPGroup p P_out := hFp.map mk
  have hmap : P_out.map Φ = P_V := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hz
      rw [hΦE σ]
      exact Subgroup.mem_map_of_mem
        (MonoidHom.inl (RingAut K) (Multiplicative (ZMod (exactE Tag.E6)))) hσ
    · intro hy
      obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨QuotientGroup.mk' I (E σ),
        Subgroup.mem_map_of_mem mk (Subgroup.mem_map_of_mem E hσ), hΦE σ⟩
  have hPoutnormal : P_out.Normal :=
    normal_of_ker_dvd_three Φ hΦdvd hp hp5 hPVnormal hP0p hmap
  have hOutdvd : Nat.card (Outer (adjointGroup Tag.E6 K)) ∣ 6 * f := by
    have h := (ordinary_E_outer_order_Cartan_divisor Tag.E6 (Or.inl rfl) hp₀ hf K hK 3 2
      (Or.inl ⟨rfl, rfl, rfl⟩)).1
    simpa [mul_assoc] using h
  have hFmapcard : Nat.card (P_out) = Nat.card F := by
    let g : F →* Outer (adjointGroup Tag.E6 K) := mk.comp F.subtype
    have hgker : g.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxmk : (QuotientGroup.mk' I (x : MulAut (adjointGroup Tag.E6 K))) = 1 := by
        change g x = 1
        exact hx
      have hxI : (x : MulAut (adjointGroup Tag.E6 K)) ∈ I :=
        (QuotientGroup.eq_one_iff (N := I) (x : MulAut (adjointGroup Tag.E6 K))).mp
          (by simpa using hxmk)
      have hx1 : (x : MulAut (adjointGroup Tag.E6 K)) ∈ F ⊓ I := ⟨x.2, hxI⟩
      rw [hFbot] at hx1
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hx1))
    have h := Subgroup.card_ker_mul_card_range g
    rw [hgker, Subgroup.card_bot, one_mul] at h
    have hrange : g.range = P_out := by
      rw [show g.range = F.map mk from by rw [MonoidHom.range_comp, Subgroup.range_subtype]]
    rwa [hrange] at h
  have hPoutidx : ¬ p ∣ P_out.index := by
    have h := not_dvd_index_of_card_dvd_six_mul (G := Outer (adjointGroup Tag.E6 K))
      (F := P_out) hp hp5 hf (hFmapcard.trans hFcard) hOutdvd
    exact h
  have hsupidx : (I ⊔ F).index = P_out.index := by
    have hmap_sup : (I ⊔ F).map mk = P_out := by
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    rw [← hmap_sup]
    exact (Subgroup.index_map_eq (G := MulAut (adjointGroup Tag.E6 K))
      (G' := Outer (adjointGroup Tag.E6 K)) (H := I ⊔ F) (f := mk)
      (QuotientGroup.mk'_surjective I) (by rw [QuotientGroup.ker_mk']; exact le_sup_left)).symm
  have hHidx : ¬ p ∣ (I ⊔ F).index := by rw [hsupidx]; exact hPoutidx
  have hSylow : ∀ T : Sylow p (Outer (adjointGroup Tag.E6 K)),
      (T : Subgroup (Outer (adjointGroup Tag.E6 K))).Normal := by
    intro T
    let Q : Sylow p (Outer (adjointGroup Tag.E6 K)) := hP0p.toSylow hPoutidx
    have hQnormal : (Q : Subgroup (Outer (adjointGroup Tag.E6 K))).Normal := hPoutnormal
    haveI : Unique (Sylow p (Outer (adjointGroup Tag.E6 K))) := Sylow.unique_of_normal Q hQnormal
    exact Sylow.normal_of_subsingleton T
  exact exists_fieldPart_of_isPGroup hp F hFp hFcyc hFbot hSylow hHidx


theorem exists_fieldPart_twistedE6
    {p₀ f : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p₀ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p₀ ^ f))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ∃ F : Subgroup (MulAut (twistedE6RootGroup K σ)),
      (inner (twistedE6RootGroup K σ) ⊔ F).Normal ∧ IsCyclic ↥F ∧
      F ⊓ inner (twistedE6RootGroup K σ) = ⊥ ∧
      ¬ p ∣ (inner (twistedE6RootGroup K σ) ⊔ F).index ∧
      ∀ x : MulAut (twistedE6RootGroup K σ), (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ inner (twistedE6RootGroup K σ) ⊔ F := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  set C := twistedE6RootGroup K σ with hC
  set I : Subgroup (MulAut C) := inner C with hI
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘform, hΘsurj, hΘker, -, hcube, -⟩, -, -, -,
    -⟩ := twisted_E6_all_characteristic_exact_automorphism_normal_form hp₀ hf K hK σ hσ
  have hinner : I ≤ Θ.ker := by rw [hΘker]; exact le_sup_left
  let Φ : Outer C →* RingAut K := QuotientGroup.lift I Θ hinner
  have hΦsurj : Function.Surjective Φ := fun y => by
    obtain ⟨α, rfl⟩ := hΘsurj y
    exact ⟨α, QuotientGroup.lift_mk _ hinner α⟩
  let ψ : CFSG.HardMathSupport.Dickson.Sec6.I923.TwM σ →* Outer C :=
    (QuotientGroup.mk' I).comp (compatDiagAutHom TwistTag.E6 K σ.toRingHom)
  have hΦker : Φ.ker = ψ.range := by
    rw [show Φ = QuotientGroup.lift I Θ hinner from rfl, QuotientGroup.ker_lift, hΘker,
      Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    rw [show ψ = (QuotientGroup.mk' I).comp
      (compatDiagAutHom TwistTag.E6 K σ.toRingHom) from rfl, MonoidHom.range_comp]
  have hψker : CFSG.HardMathSupport.Dickson.Sec6.I923.twIm σ ≤ ψ.ker := by
    intro u hu
    exact (QuotientGroup.eq_one_iff _).2
      (CFSG.HardMathSupport.Dickson.Sec6.I923.compatDiagAutHom_mem_inner_of_mem_twIm σ hu)
  have hΦdvd : Nat.card Φ.ker ∣ 3 := by
    rw [hΦker]
    rw [← Subgroup.index_ker]
    refine (Subgroup.index_dvd_of_le hψker).trans ?_
    rw [CFSG.HardMathSupport.Dickson.Sec6.I923.twIm_index σ hK hσ]
    exact Nat.gcd_dvd_left 3 (p₀ ^ f + 1)
  let E : RingAut K →* MulAut C := fieldActorHom (t := TwistTag.E6) σ
  have hΦE : ∀ δ : RingAut K, Φ (QuotientGroup.mk' I (E δ)) = δ := by
    intro δ
    change QuotientGroup.lift I Θ hinner ((QuotientGroup.mk' I) (E δ)) = δ
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
    refine hΘform (fieldActor σ δ) 1 1 δ ?_
    change fieldActor σ δ =
      MulAut.conj (1 : ↥(twistedE6RootGroup K σ)) *
        (compatDiagAutHom TwistTag.E6 K σ.toRingHom)
          (1 : CFSG.HardMathSupport.Dickson.Sec6.I923.TwM σ) * fieldActor σ δ
    rw [map_one, map_one, one_mul, one_mul]
  have hEinj : Function.Injective E := by
    intro δ δ' h
    have h' : Φ (QuotientGroup.mk' I (E δ)) = Φ (QuotientGroup.mk' I (E δ')) := by
      rw [h]
    rw [hΦE δ, hΦE δ'] at h'
    exact h'
  have hK2 : Nat.card K = p₀ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : Finite (RingAut K) :=
    Finite.of_injective (fun σ : RingAut K => (σ : K → K)) DFunLike.coe_injective
  haveI : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic hp₀ K hK2).2
  have hcardAut : Nat.card (RingAut K) = 2 * f := (card_ringAut_and_isCyclic hp₀ K hK2).1
  let S : Sylow p (RingAut K) := Classical.choice (Sylow.nonempty)
  let F : Subgroup (MulAut C) := (S : Subgroup (RingAut K)).map E
  have hFp : IsPGroup p F := S.isPGroup'.map E
  have hFcyc : IsCyclic ↥F := by
    have hScyc : IsCyclic ↥(S : Subgroup (RingAut K)) := Subgroup.isCyclic _
    exact (Subgroup.equivMapOfInjective (S : Subgroup (RingAut K)) E hEinj).isCyclic.mp hScyc
  have hFcard : Nat.card F = p ^ (2 * f).factorization p := by
    rw [show F = (S : Subgroup (RingAut K)).map E from rfl,
      Subgroup.card_map_of_injective hEinj, Sylow.card_eq_multiplicity, hcardAut]
  have hFbot : F ⊓ I = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxF, hxI⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨δ, -, rfl⟩ := Subgroup.mem_map.mp hxF
    have h1 : (QuotientGroup.mk' I (E δ) : Outer C) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hxI
    have h2 : δ = 1 := by
      have h3 : Φ (QuotientGroup.mk' I (E δ)) = Φ 1 := congrArg Φ h1
      rwa [hΦE δ, map_one] at h3
    rw [Subgroup.mem_bot, h2, map_one]
  let mk : MulAut C →* Outer C := QuotientGroup.mk' I
  let P_out : Subgroup (Outer C) := F.map mk
  let P_V : Subgroup (RingAut K) := (S : Subgroup (RingAut K))
  haveI : IsMulCommutative (RingAut K) := IsCyclic.isMulCommutative
  have hPVnormal : P_V.Normal := inferInstance
  have hP0p : IsPGroup p P_out := hFp.map mk
  have hmap : P_out.map Φ = P_V := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hz
      rw [hΦE δ]
      exact hδ
    · intro hy
      exact ⟨QuotientGroup.mk' I (E y),
        Subgroup.mem_map_of_mem mk (Subgroup.mem_map_of_mem E hy), hΦE y⟩
  have hPoutnormal : P_out.Normal :=
    normal_of_ker_dvd_three Φ hΦdvd hp hp5 hPVnormal hP0p hmap
  have hOutEq : Nat.card (Outer C) = Nat.card Φ.ker * (2 * f) := by
    rw [← Subgroup.card_mul_index Φ.ker, Subgroup.index_ker,
      MonoidHom.range_eq_top.2 hΦsurj, Subgroup.card_top, hcardAut]
  have hOutdvd : Nat.card (Outer C) ∣ 6 * (2 * f) := by
    rw [hOutEq]
    exact (Nat.mul_dvd_mul_right hΦdvd (2 * f)).trans (by
      have h6 : (6 : ℕ) ∣ 12 := by norm_num
      simpa [mul_assoc, mul_comm, mul_left_comm] using Nat.mul_dvd_mul_right h6 f)
  have hFmapcard : Nat.card P_out = Nat.card F := by
    let g : F →* Outer C := mk.comp F.subtype
    have hgker : g.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxmk : (QuotientGroup.mk' I (x : MulAut C)) = 1 := by
        change g x = 1
        exact hx
      have hxI : (x : MulAut C) ∈ I :=
        (QuotientGroup.eq_one_iff (N := I) (x : MulAut C)).mp (by simpa using hxmk)
      have hx1 : (x : MulAut C) ∈ F ⊓ I := ⟨x.2, hxI⟩
      rw [hFbot] at hx1
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hx1))
    have h := Subgroup.card_ker_mul_card_range g
    rw [hgker, Subgroup.card_bot, one_mul] at h
    have hrange : g.range = P_out := by
      rw [show g.range = F.map mk from by rw [MonoidHom.range_comp, Subgroup.range_subtype]]
    rwa [hrange] at h
  have hPoutidx : ¬ p ∣ P_out.index :=
    not_dvd_index_of_card_dvd_six_mul (G := Outer C) (F := P_out) hp hp5 (by omega)
      (hFmapcard.trans hFcard) hOutdvd
  have hsupidx : (I ⊔ F).index = P_out.index := by
    have hmap_sup : (I ⊔ F).map mk = P_out := by
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    rw [← hmap_sup]
    exact (Subgroup.index_map_eq (G := MulAut C) (G' := Outer C) (H := I ⊔ F) (f := mk)
      (QuotientGroup.mk'_surjective I) (by rw [QuotientGroup.ker_mk']; exact le_sup_left)).symm
  have hHidx : ¬ p ∣ (I ⊔ F).index := by rw [hsupidx]; exact hPoutidx
  have hSylow : ∀ T : Sylow p (Outer C), (T : Subgroup (Outer C)).Normal := by
    intro T
    let Q : Sylow p (Outer C) := hP0p.toSylow hPoutidx
    have hQnormal : (Q : Subgroup (Outer C)).Normal := hPoutnormal
    haveI : Unique (Sylow p (Outer C)) := Sylow.unique_of_normal Q hQnormal
    exact Sylow.normal_of_subsingleton T
  exact exists_fieldPart_of_isPGroup hp F hFp hFcyc hFbot hSylow hHidx


theorem i713ClauseFor_lie_E6
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let S := (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group
  haveI : Finite S := Finite.of_equiv K eK.toEquiv
  have hm : ChevalleyExceptionalModel S .E6 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq2 : q.p = 2
    · exact CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hq2 (MulEquiv.refl S)
    · exact CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.untwistedBridge_E6 q hv hq2 (MulEquiv.refl S)
  have hp3 : p ≠ 3 := by
    intro h3
    subst h3
    have h4 := GL83.I713.four_le_pRank_three_of_untwistedModel_E6 hm.2
    have hEq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eK
    rw [hEq] at hpRank
    omega
  obtain ⟨L, hLfield, hLfin, hLcard, ⟨eL⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm.2
  letI := hLfield
  letI := hLfin
  haveI : Finite (adjointGroup Tag.E6 L) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_adjointGroup_E6 q.prime_p q.exponent_pos L hLcard hp hp2 hp3)))

theorem i713ClauseFor_lie_twistedE6
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let S := (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group
  haveI : Finite S := Finite.of_equiv K eK.toEquiv
  have hm : ChevalleyExceptionalModel S .twistedE6 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq2 : q.p = 2
    · exact CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.twistedBridgeEven_twistedE6 q hv hq2 (by decide)
        (MulEquiv.refl S)
    · exact CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hq2 (by decide)
        (MulEquiv.refl S)
  have hp3 : p ≠ 3 := by
    intro h3
    subst h3
    have h2 := GL83.I713.two_le_pRank_three_of_twistedE6Model q.prime_p q.exponent_pos hm.2
    have hEq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eK
    rw [hEq] at hpRank
    omega
  obtain ⟨L, hLfield, hLfin, σ, hLcard, hσ, ⟨eL⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_E6 hm
  letI := hLfield
  letI := hLfin
  haveI : Finite (twistedE6RootGroup L σ) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_twistedE6 q.prime_p q.exponent_pos L hLcard σ hσ hp hp2 hp3)))

end CFSG.LieType.OutStructure
