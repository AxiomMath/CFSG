module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Defs
import CFSG.LocalAnalysis.GL83PartI.Goldschmidt_2_5
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm52AuxSmear
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515f.Orbit
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Sol
import CFSG.RankThree.Automorphisms.CoprimeCyclicTools

public section

universe u

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride
open scoped commutatorElement

namespace GL83.GL1

section CyclicAction

variable {Γ : Type u} [Group Γ]

theorem exists_ne_one_centralizes_of_cyclic {p : ℕ} (hp : p.Prime) {E J : Subgroup Γ}
    (hE : IsElemAbelian p E) (hE2 : p ^ 2 ≤ Nat.card E)
    (hEJ : E ≤ Subgroup.normalizer (J : Set Γ))
    (hcyc : ∀ P : Subgroup (MulAut ↥J), IsPGroup p P → IsCyclic P) :
    ∃ e ∈ E, e ≠ 1 ∧ J ≤ Subgroup.centralizer ({e} : Set Γ) := by
  have : Fact p.Prime := ⟨hp⟩
  let ρ : ↥E →* MulAut ↥J := J.normalizerMonoidHom.comp (Subgroup.inclusion hEJ)
  have hpow : ∀ b : E, b ^ p = 1 := fun b => Subtype.ext (by simpa using hE.2 b b.2)
  have hRp : IsPGroup p ρ.range :=
    IsPGroup.of_surjective (fun b : E => ⟨1, by simpa using hpow b⟩) ρ.rangeRestrict
      ρ.rangeRestrict_surjective
  obtain ⟨g, hg⟩ := (hcyc ρ.range hRp).exists_ofOrder_eq_natCard
  have hgp : g ^ p = 1 := by
    obtain ⟨b, hb⟩ := g.2
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, ← hb, ← map_pow, hpow b, map_one]
    rfl
  have hrange : Nat.card ρ.range ∣ p := hg ▸ orderOf_dvd_of_pow_eq_one hgp
  by_contra hcon
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    by_contra hb1
    refine hcon ⟨b, b.2, fun h => hb1 (Subtype.ext h), fun j hj => ?_⟩
    have h1 := congrArg (fun f : MulAut ↥J => ((f ⟨j, hj⟩ : ↥J) : Γ)) hb
    have h2 : ((ρ b ⟨j, hj⟩ : ↥J) : Γ) = (b : Γ) * j * (b : Γ)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨(b : Γ), hEJ b.2⟩ ⟨j, hj⟩
    simp only [h2] at h1
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have h3 : (b : Γ) * j * (b : Γ)⁻¹ = j := h1
    calc (b : Γ) * j = (b : Γ) * j * (b : Γ)⁻¹ * (b : Γ) := by group
      _ = j * (b : Γ) := by rw [h3]
  have hcard : Nat.card ρ.range = Nat.card E :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hle : Nat.card E ≤ p := hcard ▸ Nat.le_of_dvd hp.pos hrange
  have : p ^ 2 ≤ p := hE2.trans hle
  nlinarith [hp.two_le]

end CyclicAction

section Basic

variable {Γ : Type u} [Group Γ] [Finite Γ]

theorem commute_of_mem_lcal_of_mem_sol {C J : Subgroup Γ} (hJ : J ∈ lcal C) {x : Γ}
    (hx : x ∈ sol C) {j : Γ} (hj : j ∈ J) : j * x = x * j := by
  obtain ⟨hJC, hsub, hs, hnc⟩ := mem_lcal_iff.mp hJ
  have hnc' : ∃ a b : ↥J, a * b ≠ b * a := by
    by_contra h
    exact hnc ⟨⟨fun a b => by_contra fun hab => h ⟨a, b, hab⟩⟩⟩
  have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc').1
  have hK : CFSG.IsComponent (J.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hq, hsub⟩
  have hR : (sol C).subgroupOf C = CFSG.solvableRadical ↥C := subgroupOf_sol C
  have hRs : Group.IsSolvable ((sol C).subgroupOf C) := by
    rw [hR]
    exact CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hRn : ((sol C).subgroupOf C).IsSubnormal := by
    rw [hR]
    exact Subgroup.Normal.isSubnormal inferInstance
  have h1 := (CFSG.LocalCores.component_solvable_centralizer hRs hRn).1 _ hK
  have hxC : x ∈ C := sol_le C hx
  have h2 : (⁅(⟨j, hJC hj⟩ : ↥C), (⟨x, hxC⟩ : ↥C)⁆ : ↥C) ∈ ⁅J.subgroupOf C, (sol C).subgroupOf C⁆ :=
    Subgroup.commutator_mem_commutator hj hx
  rw [h1, Subgroup.mem_bot] at h2
  have h3 : ((⟨j, hJC hj⟩ : ↥C) * ⟨x, hxC⟩) = ⟨x, hxC⟩ * ⟨j, hJC hj⟩ :=
    commutatorElement_eq_one_iff_mul_comm.mp h2
  exact congrArg Subtype.val h3

end Basic

section Core

variable {Γ : Type u} [Group Γ] [Finite Γ]

open CFSG.SignalizerFunctorTheorem.McBride.Near CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

omit [Finite Γ] in
theorem smear_zpowers_eq_self {J : Subgroup Γ} {e : Γ}
    (hn : e ∈ Subgroup.normalizer (J : Set Γ)) (hc : J ≤ Subgroup.centralizer ({e} : Set Γ)) :
    smear J (Subgroup.zpowers e) = J := by
  have hAJ : Subgroup.zpowers e ≤ Subgroup.normalizer (J : Set Γ) := Subgroup.zpowers_le.mpr hn
  have hL : orbitClosure J (Subgroup.zpowers e) = J := by
    refine le_antisymm (orbitClosure_le fun a ha => ?_) (le_orbitClosure J _)
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAJ ha)).le
  rw [smear, hL, Thm52Aux.centralizer_zpowers_eq]
  exact inf_eq_left.mpr hc

theorem centralizes_of_not_normalizes {p : ℕ} (hp : p.Prime) {Z J : Subgroup Γ} {e x : Γ}
    (hcop : p.Coprime (Nat.card Z)) (hsol : sol Z = ⊥) (hJ : J ∈ lcal Z)
    (heZ : e ∈ Subgroup.normalizer (Z : Set Γ)) (hep : e ^ p = 1)
    (heJ : e ∉ Subgroup.normalizer (J : Set Γ)) (hxZ : x ∈ Z)
    (hxe : x ∈ Subgroup.centralizer ({e} : Set Γ))
    (hxT : ∀ t ∈ smear J (Subgroup.zpowers e), t * x = x * t) :
    ∀ j ∈ J, j * x = x * j := by
  have hnorm_x : x ∈ Subgroup.normalizer (Z : Set Γ) := Subgroup.le_normalizer hxZ
  set B := Subgroup.zpowers e with hB
  have hBZ : B ≤ Subgroup.normalizer (Z : Set Γ) := Subgroup.zpowers_le.mpr heZ
  have hxB : ∀ b ∈ B, b * x = x * b := by
    intro b hb
    have : x ∈ Subgroup.centralizer (B : Set Γ) := by
      rw [hB, Thm52Aux.centralizer_zpowers_eq]
      exact hxe
    exact Subgroup.mem_centralizer_iff.1 this b hb
  set J' := J.map (MulAut.conj x).toMonoidHom with hJ'
  have hJ'mem : J' ∈ lcal Z := map_conj_mem_lcal hJ hnorm_x
  set T := smear J B with hT
  have hTne : T ≠ ⊥ := by
    obtain ⟨φ⟩ := Thm52Aux.nonempty_mulEquiv_smear hp heZ hep hJ heJ
    have hJs : IsSimpleGroup ↥J := (mem_lcal_iff.mp hJ).2.2.1
    have : Nontrivial ↥J := hJs.toNontrivial
    have : Nontrivial ↥T := φ.symm.injective.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot T).mp this
  have hconj : ∀ y ∈ orbitClosure J B, x * y * x⁻¹ ∈ orbitClosure J' B := by
    have : orbitClosure J B ≤ (orbitClosure J' B).comap (MulAut.conj x).toMonoidHom := by
      refine orbitClosure_le fun a ha => ?_
      rintro _ ⟨y, hy, rfl⟩
      show x * (a * y * a⁻¹) * x⁻¹ ∈ orbitClosure J' B
      have hxa : x * a = a * x := (hxB a ha).symm
      have h1 : x * a * x⁻¹ = a := by rw [hxa]; group
      have h2 : x * a⁻¹ * x⁻¹ = a⁻¹ := by
        calc x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
          _ = a⁻¹ := by rw [h1]
      have h3 : x * (a * y * a⁻¹) * x⁻¹ = a * (x * y * x⁻¹) * a⁻¹ := by
        calc x * (a * y * a⁻¹) * x⁻¹ = (x * a * x⁻¹) * (x * y * x⁻¹) * (x * a⁻¹ * x⁻¹) := by group
          _ = a * (x * y * x⁻¹) * a⁻¹ := by rw [h1, h2]
      rw [h3]
      exact map_conj_le_orbitClosure J' ha ⟨x * y * x⁻¹, ⟨y, hy, rfl⟩, rfl⟩
    exact fun y hy => this hy
  have hJ'orb : J' ∈ Nonsolv.L514.conjOrbit B J := by
    by_contra hnot
    have h0 := Nonsolv.T515f.inf_orbitClosure_eq_bot_of_not_mem_conjOrbit hBZ hsol hJ hJ'mem hnot
    apply hTne
    rw [eq_bot_iff, ← h0]
    refine le_inf (smear_le_orbitClosure J B) fun t ht => ?_
    have h1 : x * t * x⁻¹ = t := by rw [← hxT t ht]; group
    rw [← h1]
    exact hconj t (smear_le_orbitClosure J B ht)
  have hJ'eq : J' = J := by
    obtain ⟨a, ha, haJ⟩ := hJ'orb
    have hax : Commute a x := hxB a ha
    have h1 : a⁻¹ * x ∈ Subgroup.normalizer (J : Set Γ) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      calc J.map (MulAut.conj (a⁻¹ * x)).toMonoidHom
          = (J.map (MulAut.conj x).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom :=
            (Thm52Aux.map_conj_map_conj J a⁻¹ x).symm
        _ = (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom := by
            rw [← hJ', haJ]
        _ = J.map (MulAut.conj (a⁻¹ * a)).toMonoidHom := Thm52Aux.map_conj_map_conj J a⁻¹ a
        _ = J := by
            rw [inv_mul_cancel]
            ext y
            simp
    have hap : a ^ p = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hep, one_zpow]
    have hm : Nat.Coprime p (orderOf x) :=
      hcop.coprime_dvd_right (Subgroup.orderOf_dvd_natCard Z hxZ)
    have h2 : (a⁻¹ * x) ^ orderOf x = (a ^ orderOf x)⁻¹ := by
      rw [(hax.inv_left).mul_pow, pow_orderOf_eq_one, mul_one, inv_pow]
    have h3 : a ^ orderOf x ∈ Subgroup.normalizer (J : Set Γ) := by
      have := pow_mem h1 (orderOf x)
      rw [h2] at this
      simpa using inv_mem this
    have h4 : a ^ orderOf x ∈ B ⊓ Subgroup.normalizer (J : Set Γ) := ⟨pow_mem ha _, h3⟩
    rw [Thm52Aux.zpowers_inf_normalizer_eq_bot hp hep heJ, Subgroup.mem_bot] at h4
    have h5 : orderOf a ∣ orderOf x := orderOf_dvd_of_pow_eq_one h4
    have h6 : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one hap
    have h7 : orderOf a = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h6 hm) h5
    have h8 : a = 1 := orderOf_eq_one_iff.mp h7
    rw [haJ, h8]
    ext y
    simp
  have hdp := isDirectProduct_orbit hBZ hJ
  set S : Set (Subgroup Γ) := {K | ∃ a ∈ B, K = J.map (MulAut.conj a).toMonoidHom} with hS
  have hJS : J ∈ S := ⟨1, one_mem B, by ext y; simp⟩
  have hAS : ∀ a ∈ B, ∀ K ∈ S, K.map (MulAut.conj a).toMonoidHom ∈ S := by
    rintro a ha _ ⟨a', ha', rfl⟩
    exact ⟨a * a', mul_mem ha ha', Thm52Aux.map_conj_map_conj J a a'⟩
  have hxS : ∀ K ∈ S, K.map (MulAut.conj x).toMonoidHom ∈ S := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a, ha, ?_⟩
    have hxa : x * a = a * x := (hxB a ha).symm
    calc (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj x).toMonoidHom
        = J.map (MulAut.conj (x * a)).toMonoidHom := Thm52Aux.map_conj_map_conj J x a
      _ = J.map (MulAut.conj (a * x)).toMonoidHom := by rw [hxa]
      _ = (J.map (MulAut.conj x).toMonoidHom).map (MulAut.conj a).toMonoidHom :=
          (Thm52Aux.map_conj_map_conj J a x).symm
      _ = J.map (MulAut.conj a).toMonoidHom := by rw [← hJ', hJ'eq]
  have hN : B ⊓ Subgroup.normalizer (J : Set Γ) = ⊥ :=
    Thm52Aux.zpowers_inf_normalizer_eq_bot hp hep heJ
  intro j hj
  have hproj : j ∈ projIn S J (orbitClosure J B ⊓ Subgroup.centralizer (B : Set Γ)) := by
    rw [projIn_centralizer_eq hdp hAS hJS, hN]
    refine Subgroup.mem_inf.mpr ⟨hj, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
    rw [hh]
    simp
  obtain ⟨y, hy, hyj⟩ := (hdp.mem_projIn_iff hJS).mp hproj
  have hyT : (y : Γ) ∈ T := hy
  have hxy : x * (y : Γ) * x⁻¹ = y := by rw [← hxT y hyT]; group
  have h1 := hdp.coord_conj hxS hJS y.2
  have h2 := hdp.coord_val_congr (hxS J hJS) hJS hJ'eq
    ⟨x * (y : Γ) * x⁻¹, hdp.conj_mem hxS y.2⟩
  have h3 : (⟨x * (y : Γ) * x⁻¹, hdp.conj_mem hxS y.2⟩ : ↥(orbitClosure J B)) = y :=
    Subtype.ext hxy
  rw [h2, h3] at h1
  have h4 : ((hdp.coord hJS ⟨(y : Γ), y.2⟩ : ↥J) : Γ) = j := hyj
  rw [h4] at h1
  calc j * x = x * j * x⁻¹ * x := by rw [← h1]
    _ = x * j := by group

theorem iInf_sol_le_bot {p : ℕ} (hp : p.Prime) {Z E : Subgroup Γ} (hE : IsElemAbelian p E)
    (hEZ : E ≤ Subgroup.normalizer (Z : Set Γ)) (hE2 : p ^ 2 ≤ Nat.card E)
    (hcop : p.Coprime (Nat.card Z)) (hsol : sol Z = ⊥)
    (hOC : ∀ J ∈ lcal Z, E ≤ Subgroup.normalizer (J : Set Γ) →
      ∃ e ∈ E, e ≠ 1 ∧ J ≤ Subgroup.centralizer ({e} : Set Γ)) :
    (⨅ (e : Γ) (_ : e ∈ E) (_ : e ≠ 1), sol (Z ⊓ Subgroup.centralizer ({e} : Set Γ))) ≤ ⊥ := by
  obtain ⟨e₀, he₀, he₀1⟩ := GL83.Goldschmidt.exists_ne_one_mem hp hE2
  intro x hx
  have hxe : ∀ e ∈ E, e ≠ 1 → x ∈ sol (Z ⊓ Subgroup.centralizer ({e} : Set Γ)) :=
    fun e he he1 => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx e) he) he1
  have hxZ : x ∈ Z := (sol_le _ (hxe e₀ he₀ he₀1)).1
  have hxC : ∀ e ∈ E, e ≠ 1 → x ∈ Subgroup.centralizer ({e} : Set Γ) :=
    fun e he he1 => (sol_le _ (hxe e he he1)).2
  have key : ∀ J ∈ lcal Z, ∀ j ∈ J, j * x = x * j := by
    intro J hJ j hj
    obtain ⟨hJZ, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
    by_cases hEJ : E ≤ Subgroup.normalizer (J : Set Γ)
    · obtain ⟨e, he, he1, hJe⟩ := hOC J hJ hEJ
      have hsub := Near.Thm52Aux.isSubnormal_smear hsol (hEZ he) hJ
      rw [smear_zpowers_eq_self (hEJ he) hJe] at hsub
      have hJC : J ∈ lcal (Z ⊓ Subgroup.centralizer ({e} : Set Γ)) :=
        mem_lcal_iff.mpr ⟨le_inf hJZ hJe, hsub, hs, hnc⟩
      exact commute_of_mem_lcal_of_mem_sol hJC (hxe e he he1) hj
    · obtain ⟨e, he, heJ⟩ := IsConcreteLE.not_le_iff_exists.mp hEJ
      have he1 : e ≠ 1 := fun h => heJ (h ▸ one_mem _)
      have heZ := hEZ he
      have hep : e ^ p = 1 := hE.2 e he
      obtain ⟨φ⟩ := Near.Thm52Aux.nonempty_mulEquiv_smear hp heZ hep hJ heJ
      have hT : smear J (Subgroup.zpowers e) ∈ lcal (Z ⊓ Subgroup.centralizer ({e} : Set Γ)) :=
        mem_lcal_iff.mpr ⟨Near.Thm52Aux.smear_le_inf_centralizer hsol heZ hJ,
          Near.Thm52Aux.isSubnormal_smear hsol heZ hJ, φ.isSimpleGroup,
          fun hc => hnc ((isMulCommutative_congr φ).mp hc)⟩
      exact centralizes_of_not_normalizes hp hcop hsol hJ heZ hep heJ hxZ (hxC e he he1)
        (fun t ht => commute_of_mem_lcal_of_mem_sol hT (hxe e he he1) ht) j hj
  have hdp := isDirectProduct_lcal_kOf hsol
  have hk : kOf Z ≤ Subgroup.centralizer ({x} : Set Γ) := by
    rw [← hdp.sSup_eq]
    refine sSup_le fun J hJ j hj => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (key J hJ j hj).symm
  have hx' : x ∈ Z ⊓ Subgroup.centralizer (kOf Z : Set Γ) :=
    ⟨hxZ, Subgroup.mem_centralizer_iff.2 fun k hk' =>
      (Subgroup.mem_centralizer_iff.1 (hk hk') x (Set.mem_singleton x)).symm⟩
  rw [centralizer_kOf_eq_bot hsol] at hx'
  exact hx'

end Core

end GL83.GL1

namespace GL83

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv GL83.GL1

variable {Γ : Type u} [Group Γ] [Finite Γ]

theorem GL1_4_2 {p : ℕ} (hp : p.Prime) {K E : Subgroup Γ}
    (hEK : E ≤ Subgroup.normalizer (K : Set Γ)) (hE : IsElemAbelian p E)
    (hE2 : p ^ 2 ≤ Nat.card E) (hpK : p.Coprime (Nat.card K))
    (hcyc : ∀ J ∈ lcalOf (↥K ⧸ CFSG.solvableRadical ↥K),
      ∀ P : Subgroup (MulAut ↥J), IsPGroup p P → IsCyclic P) :
    (⨅ (e : Γ) (_ : e ∈ E) (_ : e ≠ 1), sol (K ⊓ Subgroup.centralizer ({e} : Set Γ))) ≤
      sol K := by
  set N := sol K with hN
  have hKN : K ≤ AChief.nrm N := SolQuot.le_nrm_sol K
  have hEN : E ≤ AChief.nrm N := hEK.trans (SolQuot.normalizer_le_nrm_sol K)
  have hQ : SolQuot.QSetting p N E K := ⟨hp, isSolvable_sol K, hE, hEK, hpK, hKN, hEN⟩
  set Kb := AChief.qimg N K with hKb
  set Eb := AChief.qimg N E with hEb
  have hsolKb : sol Kb = ⊥ := SolQuot.sol_qimg_sol K
  have hEb_el : IsElemAbelian p Eb := AChief.isElemAbelian_qimg hE
  have hEbK : Eb ≤ Subgroup.normalizer (Kb : Set (AChief.QG N)) := AChief.qimg_le_normalizer hEK
  have hEb2 : p ^ 2 ≤ Nat.card Eb := by
    rw [hQ.card_qimg (sol_le K)]
    exact hE2
  have hcopKb : p.Coprime (Nat.card Kb) := by
    have h := AChief.card_qimg_mul_card (sol_le K) hKN
    exact hpK.coprime_dvd_right (Dvd.intro _ h)
  have hOC : ∀ J ∈ lcal Kb, Eb ≤ Subgroup.normalizer (J : Set (AChief.QG N)) →
      ∃ e ∈ Eb, e ≠ 1 ∧ J ≤ Subgroup.centralizer ({e} : Set (AChief.QG N)) := by
    intro J hJ hEbJ
    refine exists_ne_one_centralizes_of_cyclic hp hEb_el hEb2 hEbJ fun P hP => ?_
    let ψ := SolQuot.quotSolEquiv K
    have hJ0 : (J.subgroupOf Kb).map ψ.symm.toMonoidHom ∈
        lcalOf (↥K ⧸ CFSG.solvableRadical ↥K) := (map_mem_lcalOf_iff ψ.symm).2 hJ.2
    let e : ↥J ≃* ↥((J.subgroupOf Kb).map ψ.symm.toMonoidHom) :=
      (Subgroup.subgroupOfEquivOfLe hJ.1).symm.trans
        (Subgroup.equivMapOfInjective _ ψ.symm.toMonoidHom ψ.symm.injective)
    exact CFSG.RankThree.Automorphisms.isCyclic_of_isPGroup_of_mulEquiv e (hcyc _ hJ0) hP
  have hcore := iInf_sol_le_bot hp hEb_el hEbK hEb2 hcopKb hsolKb hOC
  obtain ⟨e₀, he₀, he₀1⟩ := GL83.Goldschmidt.exists_ne_one_mem hp hE2
  set X := ⨅ (e : Γ) (_ : e ∈ E) (_ : e ≠ 1), sol (K ⊓ Subgroup.centralizer ({e} : Set Γ))
    with hX
  have hXe : ∀ e ∈ E, e ≠ 1 → X ≤ sol (K ⊓ Subgroup.centralizer ({e} : Set Γ)) :=
    fun e he he1 => (iInf_le _ e).trans ((iInf_le _ he).trans (iInf_le _ he1))
  have hXK : X ≤ K := (hXe e₀ he₀ he₀1).trans ((sol_le _).trans inf_le_left)
  have hXN : X ≤ AChief.nrm N := hXK.trans hKN
  have hle : AChief.qimg N X ≤ ⊥ := by
    refine le_trans ?_ hcore
    refine le_iInf fun eb => le_iInf fun heb => le_iInf fun heb1 => ?_
    obtain ⟨y, hyE, rfl⟩ := (AChief.mem_qimg_iff N E eb).1 heb
    have he1 : (y : Γ) ≠ 1 := fun h => heb1 (by
      have : y = 1 := Subtype.ext h
      rw [this, map_one])
    have hEz : IsElemAbelian p (Subgroup.zpowers (y : Γ)) := by
      refine ⟨inferInstance, fun x hx => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hE.2 _ hyE, one_zpow]
    have hzK : Subgroup.zpowers (y : Γ) ≤ Subgroup.normalizer (K : Set Γ) :=
      Subgroup.zpowers_le.mpr (hEK hyE)
    have hzN : Subgroup.zpowers (y : Γ) ≤ AChief.nrm N := Subgroup.zpowers_le.mpr y.2
    have h3 := AChief.qimg_inf_centralizer hp hEz hzK hzN hKN hpK
    rw [Near.Thm52Aux.centralizer_zpowers_eq, SolQuot.qimg_zpowers y.2,
      Near.Thm52Aux.centralizer_zpowers_eq] at h3
    have h4 : (AChief.qmap N ⟨(y : Γ), y.2⟩ : AChief.QG N) = AChief.qmap N y := rfl
    rw [h4] at h3
    calc AChief.qimg N X ≤ AChief.qimg N (sol (K ⊓ Subgroup.centralizer ({(y : Γ)} : Set Γ))) :=
          SolQuot.qimg_mono (hXe _ hyE he1)
      _ = sol (AChief.qimg N (K ⊓ Subgroup.centralizer ({(y : Γ)} : Set Γ))) :=
          (SolQuot.sol_qimg_sol_of_le inf_le_left).symm
      _ = sol (Kb ⊓ Subgroup.centralizer ({AChief.qmap N y} : Set (AChief.QG N))) := by rw [h3]
  have := (SolQuot.qimg_le_iff hXN).1 hle
  rwa [SolQuot.qpre_bot] at this

end GL83
