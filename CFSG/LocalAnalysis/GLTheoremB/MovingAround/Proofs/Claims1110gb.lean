module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110g
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.BalanceLp
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagSUTwisted
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponentUnitary
import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicLift
import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04Cover
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110fb

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110g

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (OutEasy)

theorem outEasy_five_of_ne {t : StatedLieTag} {n r f : ℕ} (hL : t ≠ .PSL) (hU : t ≠ .PSU) :
    OutEasy 5 t n r f := by
  cases t
  · exact absurd rfl hL
  · exact absurd rfl hU
  all_goals first
    | exact trivial
    | exact fun _ => by norm_num
    | exact Or.inl (by norm_num)

section Out5


theorem pRank_outer_le_one_of_lieModel {S : Type} [Group S] [Finite S] {t : StatedLieTag} {n r f : ℕ}
    (hm : CFSG.Models.LieModel S t n r f) (h : OutEasy 5 t n r f) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer S)) ≤ 1 :=
  CFSG.LocalAnalysis.RankThreeTheoremC.pRank_outer_le_one_of_outPChain (by norm_num)
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPChain_of_lieModel (by norm_num) (by norm_num)
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hm) h)

theorem inputOut5Lie_holds : Claims1110f.InputOut5Lie := by
  intro S _ _ _ _ idx hidx h2
  obtain ⟨e⟩ := hidx
  have key : ∀ {t : StatedLieTag} {n r f : ℕ}, CFSG.Models.LieModel S t n r f → OutEasy 5 t n r f →
      False := fun hm h => by
    have := pRank_outer_le_one_of_lieModel hm h
    omega
  have keyNe : ∀ {t : StatedLieTag} {n r f : ℕ}, CFSG.Models.LieModel S t n r f → t ≠ .PSL → t ≠ .PSU →
      False := fun hm hL hU => key hm (outEasy_five_of_ne hL hU)
  obtain ⟨d, hv⟩ := idx
  cases d with
  | A r q =>
    by_cases h5 : 5 ∣ Nat.gcd (r + 1) (CFSG.LocalAnalysis.GLTheoremA.qEps true q.card)
    · exact ⟨r + 1, q.card, true, ⟨.lie ⟨.A r q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩, h5⟩
    · exfalso
      refine key (CFSG.Models.lieModel_A r q hv e) fun _ => ?_
      rwa [Claims1110f.qEps_true_card'] at h5
  | twistedA r q =>
    by_cases h5 : 5 ∣ Nat.gcd (r + 1) (CFSG.LocalAnalysis.GLTheoremA.qEps false q.card)
    · exact ⟨r + 1, q.card, false, ⟨.lie ⟨.twistedA r q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩, h5⟩
    · exfalso
      refine key (Claims1110f.lieModel_twistedA' r q hv e) ?_
      show ¬ 5 ∣ Nat.gcd (r + 1) (q.p ^ q.exponent + 1)
      rwa [Claims1110f.qEps_false_card'] at h5
  | B r q =>
    exfalso
    rcases CFSG.Models.lieModel_B r q hv e with hm | hm
    · exact keyNe hm (by decide) (by decide)
    · exact keyNe hm (by decide) (by decide)
  | C r q => exact (keyNe (CFSG.Models.lieModel_C r q hv e) (by decide) (by decide)).elim
  | D r q => exact (keyNe (CFSG.Models.lieModel_D r q hv e) (by decide) (by decide)).elim
  | twistedD r q =>
    exact (keyNe (CFSG.Models.lieModel_twistedD r q hv e) (by decide) (by decide)).elim
  | E6 q =>
    exact (keyNe (CFSG.Models.lieModel_of_namesTag (t := .E6) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩ ⟨rfl, rfl⟩ e) (by decide) (by decide)).elim
  | E7 q =>
    exact (keyNe (CFSG.Models.lieModel_of_namesTag (t := .E7) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E7 q, hv⟩ ⟨rfl, rfl⟩ e) (by decide) (by decide)).elim
  | E8 q =>
    exact (keyNe (CFSG.Models.lieModel_of_namesTag (t := .E8) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E8 q, hv⟩ ⟨rfl, rfl⟩ e) (by decide) (by decide)).elim
  | F4 q =>
    exact (keyNe (CFSG.Models.lieModel_of_namesTag (t := .F4) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.F4 q, hv⟩ ⟨rfl, rfl⟩ e) (by decide) (by decide)).elim
  | G2 q =>
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact (keyNe (CFSG.Models.lieModel_of_namesTag (t := .G2) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl, by rw [← TauCeti.PrimePower.card_def]; exact hq3⟩
      ⟨.G2 q, hv⟩ ⟨rfl, rfl⟩ e) (by decide) (by decide)).elim
  | twistedE6 q =>
    exact (keyNe (CFSG.Models.lieModel_of_namesTag (t := .twistedE6) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩ e) (by decide) (by decide)).elim
  | trialityD4 q =>
    exact (keyNe (CFSG.Models.lieModel_of_namesTag (t := .trialityD4) (p := q.p)
      (f := q.exponent) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩ e)
      (by decide) (by decide)).elim
  | suzuki m =>
    have hm1 : 1 ≤ m :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact (keyNe (CFSG.Models.lieModel_of_namesTag (t := .twistedB2) (p := 2)
      (f := 2 * m + 1) ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.suzuki m, hv⟩
      ⟨rfl, rfl⟩ e) (by decide) (by decide)).elim
  | reeG2 m =>
    have hm1 : 1 ≤ m :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact (keyNe (CFSG.Models.lieModel_of_namesTag (t := .twistedG2) (p := 3)
      (f := 2 * m + 1) ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeG2 m, hv⟩
      ⟨rfl, rfl⟩ e) (by decide) (by decide)).elim
  | reeF4 m =>
    have hm1 : 1 ≤ m :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact (keyNe (CFSG.Models.lieModel_of_namesTag (t := .twistedF4) (p := 2)
      (f := 2 * m + 1) ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeF4 m, hv⟩
      ⟨rfl, rfl⟩ e) (by decide) (by decide)).elim
  | tits =>
    exact (keyNe (CFSG.Models.lieModel_of_namesTag (t := .Tits) (p := 2) (f := 1)
      ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨.tits, hv⟩ ⟨rfl, rfl⟩ e) (by decide) (by decide)).elim

end Out5

section PGLFive

open CFSG.HardMathSupport.Timmesfeld.LinearRank

variable {L : Type} [Field L] [Finite L]

theorem card_orbitRel_quotient_five {F : Subgroup (Equiv.Perm (Fin 5))} (hF : IsPGroup 5 F)
    (hne : F ≠ ⊥) : Nat.card (MulAction.orbitRel.Quotient F (Fin 5)) = 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨σ, hσ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  obtain ⟨x, hx⟩ : ∃ x : Fin 5, (σ : Equiv.Perm (Fin 5)) x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact hσ1 (Subtype.ext (Equiv.ext hcon))
  obtain ⟨k, hk⟩ := hF.exists_card_eq
  have hdvd : (MulAction.orbit F x).ncard ∣ 5 ^ k := by
    rw [← MulAction.index_stabilizer, ← hk]
    exact Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hdvd
  have h2 : 2 ≤ (MulAction.orbit F x).ncard := by
    have hsub : ({x, σ • x} : Set (Fin 5)) ⊆ MulAction.orbit F x := by
      rintro y (rfl | rfl)
      · exact MulAction.mem_orbit_self y
      · exact MulAction.mem_orbit x σ
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hx' : x ≠ σ • x := fun h => hx h.symm
    rwa [Set.ncard_pair hx'] at this
  have h5 : (MulAction.orbit F x).ncard ≤ 5 := by
    have := Set.ncard_le_ncard (Set.subset_univ (MulAction.orbit F x)) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_fin] at this
  have hj1 : j = 1 := by
    rcases j with _ | _ | j
    · rw [hj, pow_zero] at h2
      omega
    · rfl
    · rw [hj] at h5
      have : 5 ^ 2 ≤ 5 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have horb : MulAction.orbit F x = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, hj, hj1, pow_one]
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => ?_⟩, ⟨Quotient.mk _ x⟩⟩
  induction a using Quotient.inductionOn with
  | h y =>
    induction b using Quotient.inductionOn with
    | h z =>
      have hy : y ∈ MulAction.orbit F x := horb ▸ Set.mem_univ y
      have hz : z ∈ MulAction.orbit F x := horb ▸ Set.mem_univ z
      exact (Quotient.sound hy).trans (Quotient.sound hz).symm

theorem card_inf_torus_le (hp5 : 5 ∣ Nat.card Lˣ) {E : Subgroup (PGL 5 L)} (hEm : E ≤ monoImage 5 L)
    (hE : IsElemAbelian 5 E) (F : Subgroup (Equiv.Perm (Fin 5)))
    (hFE : ∀ σ ∈ F, ∃ e ∈ E, ∃ he : e ∈ monoImage 5 L, monoPerm 5 L ⟨e, he⟩ = σ)
    (hF : IsElemAbelian 5 F) (hm : Nat.card (MulAction.orbitRel.Quotient F (Fin 5)) = 1) :
    Nat.card ↥(E ⊓ torusImage 5 L) ≤ Nat.card F := by
  classical
  have hp : Nat.Prime 5 := by norm_num
  set S : Subgroup (PGL 5 L) := E ⊓ torusImage 5 L with hSdef
  set S' : Subgroup (Fin 5 → Lˣ) := S.comap (torusProj 5 L) with hS'
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.1.is_comm.comm (⟨a, ha⟩ : F) ⟨b, hb⟩)
  have hfix : ∀ h ∈ S, ∀ e : monoImage 5 L, monoPerm 5 L e ∈ F →
      (e : PGL 5 L) * h * (e : PGL 5 L)⁻¹ = h := by
    intro h hh e he
    obtain ⟨e₀, he₀E, he₀m, he₀⟩ := hFE _ he
    have ht : monoPerm 5 L (⟨e₀, he₀m⟩⁻¹ * e) = 1 := by
      rw [map_mul, map_inv, he₀, inv_mul_cancel]
    have htT : (e₀⁻¹ * (e : PGL 5 L)) ∈ torusImage 5 L := (monoPerm_eq_one_iff _).1 ht
    have hhT : h ∈ torusImage 5 L := hh.2
    have h1 : (e₀⁻¹ * (e : PGL 5 L)) * h = h * (e₀⁻¹ * (e : PGL 5 L)) :=
      torusImage_comm _ htT _ hhT
    have h2 : e₀ * h = h * e₀ := hEc _ he₀E _ hh.1
    calc (e : PGL 5 L) * h * (e : PGL 5 L)⁻¹
        = e₀ * ((e₀⁻¹ * (e : PGL 5 L)) * h) * (e : PGL 5 L)⁻¹ := by group
      _ = e₀ * (h * (e₀⁻¹ * (e : PGL 5 L))) * (e : PGL 5 L)⁻¹ := by rw [h1]
      _ = (e₀ * h) * e₀⁻¹ := by group
      _ = (h * e₀) * e₀⁻¹ := by rw [h2]
      _ = h := by group
  have hC : ∀ c : Lˣ, (fun _ => c) ∈ S' := fun c => by
    rw [hS', Subgroup.mem_comap, torusProj_eq_one_iff.mpr ⟨c, fun _ => rfl⟩]
    exact S.one_mem
  have hpow : ∀ d ∈ S', ∃ c : Lˣ, ∀ i, d i ^ 5 = c := by
    intro d hd
    have h1 : torusProj 5 L (d ^ 5) = 1 := by
      rw [map_pow]
      exact hE.2 _ (Subgroup.mem_comap.1 hd).1
    obtain ⟨c, hc⟩ := torusProj_eq_one_iff.mp h1
    exact ⟨c, fun i => by simpa using hc i⟩
  have hFt : ∀ σ ∈ F, ∀ d ∈ S', ∃ c : Lˣ, ∀ i, d (σ i) = c * d i := by
    intro σ hσ d hd
    set e : monoImage 5 L := (projMono 5 L).rangeRestrict (SemidirectProduct.inr σ⁻¹) with he
    have heF : monoPerm 5 L e ∈ F := by
      rw [he, monoPerm_apply]
      simpa using F.inv_mem hσ
    have h1 := hfix _ hd e heF
    have h2 : (e : PGL 5 L) * torusProj 5 L d * (e : PGL 5 L)⁻¹ =
        torusProj 5 L (CFSG.HardMathSupport.Timmesfeld.LinearRank.permAct 5 L σ⁻¹ d) := by
      have hY := CFSG.HardMathSupport.Timmesfeld.LinearRank.permGL_mul_diagHom_mul_inv σ⁻¹ d
      change (QuotientGroup.mk (monoHom 5 L (SemidirectProduct.inr σ⁻¹)) : PGL 5 L) *
        QuotientGroup.mk (monoHom 5 L (SemidirectProduct.inl d)) *
        (QuotientGroup.mk (monoHom 5 L (SemidirectProduct.inr σ⁻¹)))⁻¹ =
        QuotientGroup.mk (monoHom 5 L (SemidirectProduct.inl (CFSG.HardMathSupport.Timmesfeld.LinearRank.permAct 5 L σ⁻¹ d)))
      rw [monoHom_inl, monoHom_inr, monoHom_inl, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul, hY]
    rw [h2] at h1
    generalize hd' : CFSG.HardMathSupport.Timmesfeld.LinearRank.permAct 5 L σ⁻¹ d = d' at h1
    have h3 : torusProj 5 L (d' * d⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    obtain ⟨c, hc⟩ := torusProj_eq_one_iff.mp h3
    refine ⟨c, fun i => ?_⟩
    have := hc i
    have h4 : d' i = d (σ i) := by
      rw [← hd', CFSG.HardMathSupport.Timmesfeld.LinearRank.permAct_apply]
      rfl
    simp only [Pi.mul_apply, Pi.inv_apply, h4] at this
    rw [← this]
    group
  have hcard : Nat.card S' = Nat.card Lˣ * Nat.card S := by
    let Θ' : S' →* PGL 5 L := (torusProj 5 L).comp S'.subtype
    have hrange : Θ'.range = S := by
      ext s
      constructor
      · rintro ⟨⟨d, hd⟩, rfl⟩
        exact hd
      · intro hs
        obtain ⟨d, hd⟩ := hs.2
        exact ⟨⟨d, by rw [hS', Subgroup.mem_comap, hd]; exact hs⟩, hd⟩
    have hker : Nat.card Θ'.ker = Nat.card Lˣ := by
      symm
      refine Nat.card_eq_of_bijective
        (fun c : Lˣ => (⟨⟨fun _ => c, hC c⟩, ?_⟩ : Θ'.ker)) ⟨?_, ?_⟩
      · exact torusProj_eq_one_iff.mpr ⟨c, fun _ => rfl⟩
      · intro c₁ c₂ h
        have := congrFun (congrArg (fun x : Θ'.ker => (x.1.1 : Fin 5 → Lˣ)) h) 0
        exact this
      · rintro ⟨⟨d, hd⟩, hk⟩
        obtain ⟨c, hc⟩ := torusProj_eq_one_iff.mp (MonoidHom.mem_ker.mp hk)
        exact ⟨c, Subtype.ext (Subtype.ext (funext fun i => (hc i).symm))⟩
    have h1 := Subgroup.card_ker_mul_card_range Θ'
    have h2 : Nat.card Θ'.range = Nat.card S :=
      congrArg (fun H : Subgroup (PGL 5 L) => Nat.card H) hrange
    rw [hker, h2] at h1
    exact h1.symm
  have h1 := card_twisted_le hp (by norm_num) F hFc S' hC hpow hFt
  rw [hcard, hm, pow_one] at h1
  have hpos : 0 < Nat.card Lˣ := Nat.card_pos
  have h3 : Nat.card Lˣ * (Nat.card S * 5) ≤ Nat.card Lˣ * (Nat.card F * 5) := by
    calc Nat.card Lˣ * (Nat.card S * 5) = Nat.card Lˣ * Nat.card S * 5 := by ring
      _ ≤ Nat.card Lˣ * Nat.card F * 5 := h1
      _ = Nat.card Lˣ * (Nat.card F * 5) := by ring
  have h4 := Nat.le_of_mul_le_mul_left h3 hpos
  omega

theorem le_torusImage_of_card (hp5 : 5 ∣ Nat.card Lˣ) {E : Subgroup (PGL 5 L)}
    (hEm : E ≤ monoImage 5 L) (hE : IsElemAbelian 5 E) (hc : 5 ^ 3 ≤ Nat.card E) :
    E ≤ torusImage 5 L := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set ψ : ↥E →* Equiv.Perm (Fin 5) := (monoPerm 5 L).comp (Subgroup.inclusion hEm) with hψ
  have hker : ∀ e : ↥E, ψ e = 1 ↔ (e : PGL 5 L) ∈ torusImage 5 L := fun e =>
    monoPerm_eq_one_iff (Subgroup.inclusion hEm e)
  by_cases hF : ψ.range = ⊥
  · intro x hx
    have h1 : ψ ⟨x, hx⟩ = 1 := by
      have : ψ ⟨x, hx⟩ ∈ ψ.range := ⟨_, rfl⟩
      rw [hF, Subgroup.mem_bot] at this
      exact this
    exact (hker ⟨x, hx⟩).1 h1
  · exfalso
    have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
    have hFel : IsElemAbelian 5 ψ.range := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
      · obtain ⟨x, hx⟩ := a.2
        obtain ⟨z, hz⟩ := b.2
        apply Subtype.ext
        change (a : Equiv.Perm (Fin 5)) * b = b * a
        rw [← hx, ← hz, ← map_mul, ← map_mul]
        exact congrArg (fun w : E => ψ w) (Subtype.ext (hEc _ x.2 _ z.2))
      · obtain ⟨x, rfl⟩ := hy
        rw [← map_pow]
        have hx : x ^ 5 = 1 := Subtype.ext (hE.2 x x.2)
        rw [hx, map_one]
    have hFp : IsPGroup 5 ψ.range := fun y => ⟨1, Subtype.ext (by simpa using hFel.2 y y.2)⟩
    have hm := card_orbitRel_quotient_five hFp hF
    have hFE : ∀ σ ∈ ψ.range, ∃ e ∈ E, ∃ he : e ∈ monoImage 5 L, monoPerm 5 L ⟨e, he⟩ = σ := by
      rintro σ ⟨e, rfl⟩
      exact ⟨e, e.2, hEm e.2, rfl⟩
    have hS := card_inf_torus_le hp5 hEm hE ψ.range hFE hFel hm
    have hF5 : Nat.card ψ.range ≤ 5 := by
      obtain ⟨k, hk⟩ := hFp.exists_card_eq
      have hdvd : 5 ^ k ∣ 120 := by
        rw [← hk]
        have := Subgroup.card_subgroup_dvd_card ψ.range
        rwa [Nat.card_perm, Nat.card_fin] at this
      have hk1 : k ≤ 1 := by
        by_contra hk2
        have : 5 ^ 2 ∣ 120 := (Nat.pow_dvd_pow 5 (by omega)).trans hdvd
        norm_num at this
      rw [hk]
      calc 5 ^ k ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 5 := by norm_num
    have hsplit : Nat.card E = Nat.card ψ.range * Nat.card ↥(E ⊓ torusImage 5 L) := by
      have h1 : Nat.card E = Nat.card ψ.range * Nat.card ψ.ker := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
          Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
      have h2 : Nat.card ψ.ker = Nat.card ↥(E ⊓ torusImage 5 L) := by
        refine Nat.card_congr ⟨fun k => ⟨k.1.1, k.1.2, (hker k.1).1 k.2⟩,
          fun t => ⟨⟨t.1, t.2.1⟩, (hker ⟨t.1, t.2.1⟩).2 t.2.2⟩, fun k => rfl, fun t => rfl⟩
      rw [h1, h2]
    have : Nat.card E ≤ 25 := by
      rw [hsplit]
      calc Nat.card ψ.range * Nat.card ↥(E ⊓ torusImage 5 L) ≤ 5 * 5 :=
            Nat.mul_le_mul hF5 (hS.trans hF5)
        _ = 25 := by norm_num
    omega

theorem exists_conj_le_monoImage (hp5 : 5 ∣ Nat.card Lˣ) {Q : Subgroup (PGL 5 L)} (hQ : IsPGroup 5 Q) :
    ∃ g : PGL 5 L, Q.map (MulAut.conj g).toMonoidHom ≤ monoImage 5 L := by
  classical
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hidx := not_dvd_index_monoImage (n := 5) hp (by norm_num) hp5
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow 5 (monoImage 5 L)))
  set P₀ : Subgroup (PGL 5 L) := (Q₀ : Subgroup (monoImage 5 L)).map (monoImage 5 L).subtype
    with hP₀def
  have hP₀le : P₀ ≤ monoImage 5 L := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hP₀card : Nat.card P₀ = 5 ^ (Nat.card (PGL 5 L)).factorization 5 := by
    have h1 : Nat.card P₀ = Nat.card (Q₀ : Subgroup (monoImage 5 L)) :=
      Subgroup.card_map_of_injective (monoImage 5 L).subtype_injective
    rw [h1, Sylow.card_eq_multiplicity]
    have h2 : Nat.card (PGL 5 L) = (monoImage 5 L).index * Nat.card (monoImage 5 L) := by
      rw [mul_comm]
      exact (Subgroup.card_mul_index (monoImage 5 L)).symm
    have hX0 : (monoImage 5 L).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hN0 : Nat.card (monoImage 5 L) ≠ 0 := Nat.card_pos.ne'
    rw [h2, Nat.factorization_mul hX0 hN0]
    simp [Nat.factorization_eq_zero_of_not_dvd hidx]
  let S₀ : Sylow 5 (PGL 5 L) := Sylow.ofCard P₀ hP₀card
  obtain ⟨S₁, hQS₁⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PGL 5 L) S₁ S₀
  refine ⟨g, ?_⟩
  have h1 : (S₁ : Subgroup (PGL 5 L)).map (MulAut.conj g).toMonoidHom = P₀ := by
    have h2 : ((g • S₁ : Sylow 5 (PGL 5 L)) : Subgroup (PGL 5 L)) = (S₀ : Subgroup (PGL 5 L)) := by
      rw [hg]
    rw [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at h2
    exact h2
  calc Q.map (MulAut.conj g).toMonoidHom ≤ (S₁ : Subgroup (PGL 5 L)).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hQS₁
    _ = P₀ := h1
    _ ≤ monoImage 5 L := hP₀le

theorem exists_conj_toral (hp5 : 5 ∣ Nat.card Lˣ) {Q E₁ E₂ : Subgroup (PGL 5 L)} (hQ : IsPGroup 5 Q)
    (h₁ : E₁ ≤ Q) (h₂ : E₂ ≤ Q) (hE₁ : IsElemAbelian 5 E₁) (hE₂ : IsElemAbelian 5 E₂)
    (hc₁ : 5 ^ 3 ≤ Nat.card E₁) (hc₂ : 5 ^ 3 ≤ Nat.card E₂) :
    ∃ g : PGL 5 L, (∀ x ∈ E₁, g * x * g⁻¹ ∈ torusImage 5 L) ∧ ∀ x ∈ E₂, g * x * g⁻¹ ∈ torusImage 5 L := by
  obtain ⟨g, hg⟩ := exists_conj_le_monoImage hp5 hQ
  have key : ∀ {E : Subgroup (PGL 5 L)}, E ≤ Q → IsElemAbelian 5 E → 5 ^ 3 ≤ Nat.card E →
      ∀ x ∈ E, g * x * g⁻¹ ∈ torusImage 5 L := by
    intro E hEQ hE hc x hx
    have hle : E.map (MulAut.conj g).toMonoidHom ≤ monoImage 5 L :=
      (Subgroup.map_mono hEQ).trans hg
    have hel : IsElemAbelian 5 (E.map (MulAut.conj g).toMonoidHom) :=
      CFSG.SectionRank.isElemAbelian_map hE _
    have hcard : 5 ^ 3 ≤ Nat.card (E.map (MulAut.conj g).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hc
    exact le_torusImage_of_card hp5 hle hel hcard ⟨x, hx, rfl⟩
  exact ⟨g, key h₁ hE₁ hc₁, key h₂ hE₂ hc₂⟩

theorem exists_diag_of_mk_mem {X : GL (Fin 5) L}
    (hX : (QuotientGroup.mk X : PGL 5 L) ∈ torusImage 5 L) :
    ∃ d : Fin 5 → Lˣ, X = CFSG.SectionRank.OddCover.diagHom 5 d := by
  obtain ⟨d, hd⟩ := hX
  have h1 : torusProj 5 L d = QuotientGroup.mk (CFSG.SectionRank.OddCover.diagHom 5 d) := by
    change QuotientGroup.mk' _ (monoHom 5 L (SemidirectProduct.inl d)) = _
    rw [monoHom_inl, QuotientGroup.mk'_apply]
  rw [h1] at hd
  obtain ⟨c, hc⟩ :=
    (CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff).1 (QuotientGroup.eq.1 hd)
  refine ⟨d * fun _ => c, ?_⟩
  rw [map_mul, diagHom_const, ← hc, mul_inv_cancel_left]

end PGLFive

section U5

open CFSG.HardMathSupport.Timmesfeld.LinearRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.RankThree.PerfectCover (hopfMultiplier)

theorem hom_eq_of_mk_eq {H Y : Type*} [Group H] [Group Y] (hH : commutator H = ⊤) (f₁ f₂ : H →* Y)
    (h : ∀ s, (QuotientGroup.mk (f₁ s) : Y ⧸ Subgroup.center Y) = QuotientGroup.mk (f₂ s)) :
    f₁ = f₂ := by
  have hc : ∀ s, (f₁ s)⁻¹ * f₂ s ∈ Subgroup.center Y := fun s => QuotientGroup.eq.1 (h s)
  let z : H →* Subgroup.center Y :=
    { toFun := fun s => ⟨(f₁ s)⁻¹ * f₂ s, hc s⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s t => Subtype.ext (by
        have ha := Subgroup.mem_center_iff.1 (hc s)
        show (f₁ (s * t))⁻¹ * f₂ (s * t) = (f₁ s)⁻¹ * f₂ s * ((f₁ t)⁻¹ * f₂ t)
        rw [map_mul, map_mul]
        calc (f₁ s * f₁ t)⁻¹ * (f₂ s * f₂ t) = (f₁ t)⁻¹ * ((f₁ s)⁻¹ * f₂ s) * f₂ t := by group
          _ = (f₁ s)⁻¹ * f₂ s * (f₁ t)⁻¹ * f₂ t := by rw [ha (f₁ t)⁻¹]
          _ = (f₁ s)⁻¹ * f₂ s * ((f₁ t)⁻¹ * f₂ t) := by group) }
  have hker : commutator H ≤ z.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (Subgroup.mem_center_iff.1 (z b).2 (z a : Y))
  ext s
  have hs : z s = 1 := by
    have : s ∈ z.ker := hker (hH ▸ Subgroup.mem_top s)
    exact this
  have h1 : (f₁ s)⁻¹ * f₂ s = 1 := congrArg Subtype.val hs
  exact (inv_mul_eq_one.1 h1)

theorem exists_cover_su4 (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type} [Field L] [Finite L]
    (hL : Nat.card L = (2 ^ 2) ^ 2) {n : ℕ} (hn : 3 ≤ n) (hn5 : 5 ∣ n) {K : Type} [Group K] [Finite K]
    (hK : commutator K = ⊤) (hZ : IsPGroup 5 (Subgroup.center K))
    (e₀ : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU n (2 ^ 2) L)) :
    ∃ φ : ↥(StatedSU n (2 ^ 2) L) →* K, Function.Surjective φ ∧
      ∀ s, e₀ (QuotientGroup.mk (φ s)) = QuotientGroup.mk s := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype L := Fintype.ofFinite L
  haveI : CharP L 2 := charP_of_card_eq_prime_pow (f := 4) (by rw [← Nat.card_eq_fintype_card, hL]; norm_num)
  have hq : (n, 2 ^ 2) ≠ (3, 2) := fun h => absurd (congrArg Prod.snd h) (by norm_num)
  let H₀ := StatedSU n (2 ^ 2) L
  let N : Subgroup H₀ := (StatedScalars (Fin n) L).subgroupOf H₀
  have hNc : N ≤ Subgroup.center H₀ := fun z hz => by
    have hz' : (z : GL (Fin n) L) ∈ Subgroup.center (GL (Fin n) L) := by
      have h1 := Subgroup.mem_subgroupOf.1 hz
      rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 hz' g)
  have hcenter : Nat.card N = Nat.gcd n (2 ^ 2 + 1) :=
    (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hL (n := n) (by omega)).2.2
  have hHperf : Group.IsPerfect H₀ :=
    CFSG.LieType.Steinberg.CentralExt.SUOdd.isPerfect_statedSU_odd hL hn hq
  have hKperf : Group.IsPerfect K := Group.isPerfect_def.2 hK
  let ρ : K →* H₀ ⧸ N := e₀.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρ : Function.Surjective ρ := e₀.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ρ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e₀ e₀.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU n 2 2 :=
    ⟨Nat.prime_two, by norm_num, hn, hq⟩
  have hmodel : CFSG.Models.LieModel (StatedProj H₀) .PSU n 2 2 :=
    ⟨hadm, Or.inl ⟨hadm, L, inferInstance, inferInstance, hL, ⟨MulEquiv.refl _⟩⟩⟩
  haveI : Finite (hopfMultiplier (StatedProj H₀)) :=
    CFSG.LocalAnalysis.GLTheoremA.YS04G.finite_hopf_of_model hGA hmodel
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSU n 2 2 = (Nat.gcd n (2 ^ 2 + 1), 1) := rfl
  have hM := CFSG.LocalAnalysis.GLTheoremA.YS04G.hopf_factorization_le hGA hmodel (Or.inr rfl)
    (by norm_num : Nat.Prime 5) (by norm_num) hn5 hn hg (Nat.gcd_pos_of_pos_right _ (by norm_num)).ne'
  have hM' : (Nat.card (hopfMultiplier (H₀ ⧸ N))).factorization 5 ≤
      (Nat.card (QuotientGroup.mk' N).ker).factorization 5 := by
    rw [QuotientGroup.ker_mk', hcenter]
    exact hM
  obtain ⟨φ, hφs, hφ⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.exists_hom_of_cover hHperf
    hKperf (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (by rw [QuotientGroup.ker_mk']; exact hNc) ρ hρ (by rw [hρk]) (by norm_num) (by rw [hρk]; exact hZ)
    hM'
  exact ⟨φ, hφs, fun s => DFunLike.congr_fun hφ s⟩

theorem exists_cover_su54 (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type} [Field L] [Finite L]
    (hL : Nat.card L = (2 ^ 2) ^ 2) {K : Type} [Group K] [Finite K] (hK : commutator K = ⊤)
    (hZ : IsPGroup 5 (Subgroup.center K))
    (e₀ : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU 5 (2 ^ 2) L)) :
    ∃ φ : ↥(StatedSU 5 (2 ^ 2) L) →* K, Function.Surjective φ ∧
      ∀ s, e₀ (QuotientGroup.mk (φ s)) = QuotientGroup.mk s :=
  exists_cover_su4 hGA hL (by norm_num) (dvd_refl 5) hK hZ e₀

theorem commutator_statedSU4 {L : Type} [Field L] [Finite L] (hL : Nat.card L = (2 ^ 2) ^ 2) {n : ℕ}
    (hn : 3 ≤ n) : commutator ↥(StatedSU n (2 ^ 2) L) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype L := Fintype.ofFinite L
  haveI : CharP L 2 :=
    charP_of_card_eq_prime_pow (f := 4) (by rw [← Nat.card_eq_fintype_card, hL]; norm_num)
  exact Group.isPerfect_def.1 (CFSG.LieType.Steinberg.CentralExt.SUOdd.isPerfect_statedSU_odd hL hn
    fun h => absurd (congrArg Prod.snd h) (by norm_num))

theorem mem_primeFormD_of_pow' {L : Type} [Field L] [Finite L] (h : UnitaryFieldData 2 2 L) {n : ℕ}
    (hn : 3 ≤ n) (b : MulAut (primeFormP h (idGram L n))) {k : ℕ} (hb : b ^ (5 ^ k) = 1) :
    b ∈ primeFormD h (idGram L n) := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) L) := UnitaryHigher.isPrimeFormGram_one
  have hq : ¬(n = 3 ∧ 2 ^ 2 = 2) := fun h => absurd h.2 (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, hFker, -⟩ := unitary_prime_form_full_semilinear_realization h hC hn hq
  rw [← hFker, MonoidHom.mem_ker]
  set φ := primeFormFieldFactor h hC hn hq b
  have hcard : Nat.card (L ≃+* L) = 2 * 2 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two L h.card).1
  haveI : Finite (L ≃+* L) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h1 : φ ^ (5 ^ k) = 1 := by rw [← map_pow, hb, map_one]
  have h2 : orderOf φ ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf φ ∣ 4 := by
    have := orderOf_dvd_natCard φ
    rwa [hcard] at this
  have h4 : orderOf φ ∣ Nat.gcd (5 ^ k) 4 := Nat.dvd_gcd h2 h3
  have h5 : Nat.gcd (5 ^ k) 4 = 1 := Nat.Coprime.pow_left k (by norm_num)
  rw [h5, Nat.dvd_one, orderOf_eq_one_iff] at h4
  exact h4

theorem cover_conj {L : Type} [Field L] (h : UnitaryFieldData 2 2 L) {n : ℕ} (hn : 1 ≤ n) {K : Type*}
    [Group K] (e₁ : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU n (2 ^ 2) L))
    (hSU : commutator ↥(StatedSU n (2 ^ 2) L) = ⊤) (φ : ↥(StatedSU n (2 ^ 2) L) →* K)
    (hφ : ∀ s, e₁ (QuotientGroup.mk (φ s)) = QuotientGroup.mk s) (β : MulAut K)
    (A : primeFormUnitary h (idGram L n))
    (hA : BalanceLp.modelHom (e₁.trans (BalanceLp.statedProjEquivPrimeFormP h hn)) β =
      primeFormConjHom h (idGram L n) A)
    (s t : ↥(StatedSU n (2 ^ 2) L)) (hst : (t : GL (Fin n) L) = A * s * (A : GL (Fin n) L)⁻¹) :
    β (φ s) = φ t := by
  obtain ⟨ψ, ⟨hAN, hψ⟩, hβψ⟩ := BalanceLp.actsAsConj_unitary h hn e₁ β A hA
  let cA : ↥(StatedSU n (2 ^ 2) L) →* ↥(StatedSU n (2 ^ 2) L) :=
    { toFun := fun t => ⟨(A : GL (Fin n) L) * t * (A : GL (Fin n) L)⁻¹,
        (Subgroup.mem_normalizer_iff.1 hAN t).1 t.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s t => Subtype.ext (by
        show (A : GL (Fin n) L) * ((s * t : ↥(StatedSU n (2 ^ 2) L)) : GL (Fin n) L) *
            (A : GL (Fin n) L)⁻¹ =
          ((A : GL (Fin n) L) * (s : GL (Fin n) L) * (A : GL (Fin n) L)⁻¹) *
            ((A : GL (Fin n) L) * (t : GL (Fin n) L) * (A : GL (Fin n) L)⁻¹)
        rw [Subgroup.coe_mul]
        group) }
  have heq := hom_eq_of_mk_eq hSU (β.toMonoidHom.comp φ) (φ.comp cA)
    (fun t => by
      apply e₁.injective
      show e₁ (QuotientGroup.mk (β (φ t))) = e₁ (QuotientGroup.mk (φ (cA t)))
      rw [hβψ, hφ, hφ]
      exact hψ t (cA t) rfl)
  have h2 : cA s = t := Subtype.ext hst.symm
  calc β (φ s) = φ (cA s) := DFunLike.congr_fun heq s
    _ = φ t := by rw [h2]

variable {L : Type} [Field L] [Finite L] (h : UnitaryFieldData 2 2 L)

@[expose] noncomputable def thetaD : ↥(primeFormD h (idGram L 5)) →* PGL 5 L :=
  MonoidHom.liftOfSurjective (primeFormConjHom h (idGram L 5)).rangeRestrict
    (primeFormConjHom h (idGram L 5)).rangeRestrict_surjective
    ⟨(QuotientGroup.mk' (Subgroup.center (GL (Fin 5) L))).comp
      (primeFormUnitary h (idGram L 5)).subtype, fun A hA => by
        rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hA
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
        exact (primeFormConjHom_eq_one_iff_center h (by norm_num) (by norm_num) A).1 hA⟩

theorem thetaD_apply (A : primeFormUnitary h (idGram L 5)) :
    thetaD h ((primeFormConjHom h (idGram L 5)).rangeRestrict A) =
      QuotientGroup.mk (A : GL (Fin 5) L) := by
  unfold thetaD
  erw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

theorem thetaD_injective : Function.Injective (thetaD h) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  obtain ⟨A, rfl⟩ := (primeFormConjHom h (idGram L 5)).rangeRestrict_surjective y
  have hy' : thetaD h ((primeFormConjHom h (idGram L 5)).rangeRestrict A) = 1 := hy
  rw [thetaD_apply, QuotientGroup.eq_one_iff] at hy'
  show (primeFormConjHom h (idGram L 5)).rangeRestrict A = 1
  apply Subtype.ext
  exact (primeFormConjHom_eq_one_iff_center h (by norm_num) (by norm_num) A).2 hy'

theorem mem_primeFormD_of_pow (b : MulAut (primeFormP h (idGram L 5))) {k : ℕ} (hb : b ^ (5 ^ k) = 1) :
    b ∈ primeFormD h (idGram L 5) :=
  mem_primeFormD_of_pow' h (by norm_num) b hb

theorem conj_mk_eq (s : gramSU h (idGram L 5)) :
    MulAut.conj (QuotientGroup.mk s : primeFormP h (idGram L 5)) =
      primeFormConjHom h (idGram L 5) ⟨s, s.2.1⟩ := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [MulAut.conj_apply, primeFormConjHom_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

end U5

section U5Main

open CFSG.HardMathSupport.Timmesfeld.LinearRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem isElemAbelian_subgroupOf {G : Type*} [Group G] {p : ℕ} {H K : Subgroup G}
    (hH : IsElemAbelian p H) : IsElemAbelian p (H.subgroupOf K) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    have h1 := congrArg Subtype.val
      (hH.1.is_comm.comm (⟨((a : K) : G), a.2⟩ : H) ⟨((b : K) : G), b.2⟩)
    exact h1
  · apply Subtype.ext
    exact hH.2 _ hx

theorem commutator_statedSU54 {L : Type} [Field L] [Finite L] (hL : Nat.card L = (2 ^ 2) ^ 2) :
    commutator ↥(StatedSU 5 (2 ^ 2) L) = ⊤ :=
  commutator_statedSU4 hL (by norm_num)

theorem inputU5Sylow_of (hGA : CFSG.Open.GriessAllModelsStatement) : Claims1110f.InputU5Sylow := by
  intro K _ _ hK hO hU P hP E hEP hE hEc F hF hFP hFc β hβ f hf
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨L, _, _, hL, ⟨e₀⟩⟩ := hU
  have hL' : Nat.card L = (2 ^ 2) ^ 2 := hL.trans (by norm_num)
  have h : UnitaryFieldData 2 2 L := ⟨Nat.prime_two, by norm_num, hL.trans (by norm_num)⟩
  have hKc : commutator K = ⊤ := hK.1.1
  have hZ : IsPGroup 5 (Subgroup.center K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i271h_center_isPGroup (by norm_num) hO
  let e₁ : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU 5 (2 ^ 2) L) := e₀
  obtain ⟨φ, hφs, hφ⟩ := exists_cover_su54 hGA hL' hKc hZ e₁
  let ε := e₁.trans (BalanceLp.statedProjEquivPrimeFormP h (by norm_num : 1 ≤ 5))
  let Φ : MulAut K →* MulAut (primeFormP h (idGram L 5)) := BalanceLp.modelHom ε
  have hΦ : Function.Injective Φ := BalanceLp.modelHom_injective hKc ε
  have hPD : ∀ b : ↥P, Φ (b : MulAut K) ∈ primeFormD h (idGram L 5) := by
    intro b
    obtain ⟨k, hk⟩ := hP b
    refine mem_primeFormD_of_pow h (Φ (b : MulAut K)) (k := k) ?_
    have hb : (b : MulAut K) ^ (5 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [← map_pow, hb, map_one]
  let ι₀ : ↥P →* ↥(primeFormD h (idGram L 5)) := (Φ.comp P.subtype).codRestrict _ hPD
  let ι : ↥P →* PGL 5 L := (thetaD h).comp ι₀
  have hι : Function.Injective ι := by
    intro a b hab
    have h1 : ι₀ a = ι₀ b := thetaD_injective h hab
    have h2 : Φ (a : MulAut K) = Φ (b : MulAut K) := congrArg Subtype.val h1
    exact Subtype.ext (hΦ h2)
  have hι_apply : ∀ (b : ↥P) (A : primeFormUnitary h (idGram L 5)),
      primeFormConjHom h (idGram L 5) A = Φ (b : MulAut K) →
        ι b = QuotientGroup.mk (A : GL (Fin 5) L) := by
    intro b A hA
    have h1 : ι₀ b = (primeFormConjHom h (idGram L 5)).rangeRestrict A := Subtype.ext hA.symm
    show thetaD h (ι₀ b) = _
    rw [h1, thetaD_apply]
  have hElem : ∀ {H : Subgroup (MulAut K)}, IsElemAbelian 5 H →
      IsElemAbelian 5 ((H.subgroupOf P).map ι) := fun hH =>
    CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hH) ι
  have hCard : ∀ {H : Subgroup (MulAut K)}, H ≤ P →
      Nat.card ((H.subgroupOf P).map ι) = Nat.card H := by
    intro H hHP
    rw [Subgroup.card_map_of_injective hι]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHP).toEquiv
  have hQ : IsPGroup 5 ι.range := hP.of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  have hp5 : 5 ∣ Nat.card Lˣ := by
    rw [Nat.card_units, hL]
    norm_num
  obtain ⟨g, hg₁, hg₂⟩ := exists_conj_toral hp5 hQ (Subgroup.map_le_range ι (E.subgroupOf P))
    (Subgroup.map_le_range ι ((F.map (MulAut.conj : K →* MulAut K)).subgroupOf P)) (hElem hE)
    (hElem (CFSG.SectionRank.isElemAbelian_map hF _)) (by rw [hCard hEP]; exact hEc)
    (by rw [hCard hFP]; exact hFc)
  obtain ⟨ĝ, rfl⟩ := QuotientGroup.mk_surjective g
  have hdiag : ∀ X : GL (Fin 5) L,
      (QuotientGroup.mk ĝ : PGL 5 L) * QuotientGroup.mk X * (QuotientGroup.mk ĝ)⁻¹ ∈
        torusImage 5 L → ∃ d : Fin 5 → Lˣ, ĝ * X * ĝ⁻¹ = CFSG.SectionRank.OddCover.diagHom 5 d := by
    intro X hX
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hX
    exact exists_diag_of_mk_mem hX
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.1 (hPD ⟨β, hEP hβ⟩)
  have hβι : ι ⟨β, hEP hβ⟩ = QuotientGroup.mk (A : GL (Fin 5) L) := hι_apply _ A hA
  obtain ⟨d₁, hd₁⟩ := hdiag A (by
    rw [← hβι]
    exact hg₁ _ ⟨⟨β, hEP hβ⟩, hβ, rfl⟩)
  obtain ⟨s₀, rfl⟩ := hφs f
  have hcf : MulAut.conj (φ s₀) ∈ P := hFP ⟨φ s₀, hf, rfl⟩
  have hs₀ : (s₀ : GL (Fin 5) L) ∈ gramSU h (idGram L 5) := BalanceLp.statedSU_eq_gramSU h 5 ▸ s₀.2
  have hs' : primeFormConjHom h (idGram L 5) ⟨(s₀ : GL (Fin 5) L), hs₀.1⟩ =
      Φ (MulAut.conj (φ s₀)) := by
    rw [← conj_mk_eq h ⟨(s₀ : GL (Fin 5) L), hs₀⟩]
    show _ = MulAut.congr ε (Lemma123.autQ K (MulAut.conj (φ s₀)))
    rw [Lemma123.autQ_conj, Inputs123a.congr_conj]
    congr 1
    show _ = BalanceLp.statedProjEquivPrimeFormP h (by norm_num : 1 ≤ 5) (e₁ (QuotientGroup.mk (φ s₀)))
    rw [hφ, BalanceLp.statedProjEquivPrimeFormP_mk]
  have hsι : ι ⟨MulAut.conj (φ s₀), hcf⟩ = QuotientGroup.mk (s₀ : GL (Fin 5) L) :=
    hι_apply _ ⟨(s₀ : GL (Fin 5) L), hs₀.1⟩ hs'
  obtain ⟨d₂, hd₂⟩ := hdiag (s₀ : GL (Fin 5) L) (by
    rw [← hsι]
    exact hg₂ _ ⟨⟨MulAut.conj (φ s₀), hcf⟩, ⟨φ s₀, hf, rfl⟩, rfl⟩)
  have hcomm : (A : GL (Fin 5) L) * (s₀ : GL (Fin 5) L) = (s₀ : GL (Fin 5) L) * (A : GL (Fin 5) L) := by
    have h1 := congrArg (CFSG.SectionRank.OddCover.diagHom (K := L) 5) (mul_comm d₁ d₂)
    rw [map_mul, map_mul, ← hd₁, ← hd₂] at h1
    calc (A : GL (Fin 5) L) * (s₀ : GL (Fin 5) L)
        = ĝ⁻¹ * ((ĝ * A * ĝ⁻¹) * (ĝ * (s₀ : GL (Fin 5) L) * ĝ⁻¹)) * ĝ := by group
      _ = ĝ⁻¹ * ((ĝ * (s₀ : GL (Fin 5) L) * ĝ⁻¹) * (ĝ * A * ĝ⁻¹)) * ĝ := by rw [h1]
      _ = (s₀ : GL (Fin 5) L) * (A : GL (Fin 5) L) := by group
  exact cover_conj h (by norm_num : 1 ≤ 5) e₁ (commutator_statedSU54 hL') φ hφ β A hA.symm s₀ s₀
    (by rw [hcomm, mul_inv_cancel_right])

end U5Main

section Twisted

open Matrix

open Polynomial in
theorem commute_of_commute_of_pow_eq_scalar {L : Type} [Field L] {A B C : Matrix (Fin 5) (Fin 5) L} {c : L}
    (hc : ∀ b : L, b ^ 5 ≠ c) (hA : A ^ 5 = Matrix.scalar (Fin 5) c)
    (hB : Commute A B) (hC : Commute A C) : Commute B C := by
  classical
  set P : L[X] := X ^ 5 - Polynomial.C c with hPdef
  have hP : Irreducible P := X_pow_sub_C_irreducible_of_prime (by norm_num) hc
  have hPA : aeval A P = 0 := by
    rw [hPdef, map_sub, map_pow, aeval_X, aeval_C, hA, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
    exact sub_self _
  have hPdeg : P.degree = 5 := degree_X_pow_sub_C (by norm_num) c
  set v : Fin 5 → L := Pi.single 0 1 with hv
  have hv0 : v ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp [hv] at this
  have hdvd : ∀ p : L[X], aeval A p *ᵥ v = 0 → P ∣ p := by
    intro p hp
    by_contra hnd
    obtain ⟨a, b, hab⟩ := (hP.coprime_iff_not_dvd).2 hnd
    apply hv0
    have h1 : aeval A (a * P + b * p) = 1 := by rw [hab, map_one]
    rw [map_add, map_mul, map_mul, hPA, mul_zero, zero_add] at h1
    calc v = (1 : Matrix (Fin 5) (Fin 5) L) *ᵥ v := (Matrix.one_mulVec v).symm
      _ = (aeval A b * aeval A p) *ᵥ v := by rw [h1]
      _ = aeval A b *ᵥ (aeval A p *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hp, Matrix.mulVec_zero]
  let ψ : degreeLT L 5 →ₗ[L] (Fin 5 → L) :=
    { toFun := fun p => aeval A (p : L[X]) *ᵥ v
      map_add' := fun p q => by
        simp only [Submodule.coe_add, map_add, Matrix.add_mulVec]
      map_smul' := fun r p => by
        simp only [Submodule.coe_smul, map_smul, Matrix.smul_mulVec, RingHom.id_apply] }
  have hψi : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro p hp
    rw [LinearMap.mem_ker] at hp
    have h1 := hdvd p hp
    have h2 : (p : L[X]).degree < P.degree := by
      rw [hPdeg]
      exact mem_degreeLT.1 p.2
    rw [Submodule.mem_bot]
    exact Subtype.ext (eq_zero_of_dvd_of_degree_lt h1 h2)
  have hfin : Module.finrank L (degreeLT L 5) = Module.finrank L (Fin 5 → L) :=
    (degreeLTEquiv L 5).finrank_eq
  have hψs : Function.Surjective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hψi
  have hpoly : ∀ B : Matrix (Fin 5) (Fin 5) L, Commute A B → ∃ p : L[X], B = aeval A p := by
    intro B hB
    obtain ⟨p, hp⟩ := hψs (B *ᵥ v)
    refine ⟨p, ?_⟩
    have hp' : aeval A (p : L[X]) *ᵥ v = B *ᵥ v := hp
    have hcomm : ∀ q : L[X], Commute B (aeval A q) := fun q =>
      Algebra.commute_of_mem_adjoin_singleton_of_commute
        (by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨q, rfl⟩) hB.symm
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    obtain ⟨q, rfl⟩ := hψs w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    change B *ᵥ (aeval A (q : L[X]) *ᵥ v) = aeval A (p : L[X]) *ᵥ (aeval A (q : L[X]) *ᵥ v)
    calc B *ᵥ (aeval A (q : L[X]) *ᵥ v) = (B * aeval A (q : L[X])) *ᵥ v := Matrix.mulVec_mulVec _ _ _
      _ = (aeval A (q : L[X]) * B) *ᵥ v := by rw [(hcomm q).eq]
      _ = aeval A (q : L[X]) *ᵥ (B *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = aeval A (q : L[X]) *ᵥ (aeval A (p : L[X]) *ᵥ v) := by rw [hp']
      _ = (aeval A (q : L[X]) * aeval A (p : L[X])) *ᵥ v := Matrix.mulVec_mulVec _ _ _
      _ = (aeval A (p : L[X]) * aeval A (q : L[X])) *ᵥ v := by rw [← map_mul, ← map_mul, mul_comm]
      _ = aeval A (p : L[X]) *ᵥ (aeval A (q : L[X]) *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
  obtain ⟨p, rfl⟩ := hpoly B hB
  obtain ⟨q, rfl⟩ := hpoly C hC
  exact ((Commute.all p q).map (aeval A))

@[expose] def commHom {G : Type*} [Group G] (a : G) (N : Subgroup G)
    (hN : ∀ n ∈ N, a * n * a⁻¹ * n⁻¹ ∈ Subgroup.center G) : ↥N →* ↥(Subgroup.center G) where
  toFun n := ⟨a * n * a⁻¹ * (n : G)⁻¹, hN n n.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' m n := Subtype.ext (by
    have hz := Subgroup.mem_center_iff.1 (hN n n.2)
    show a * ((m : G) * n) * a⁻¹ * ((m : G) * n)⁻¹ =
      a * m * a⁻¹ * (m : G)⁻¹ * (a * n * a⁻¹ * (n : G)⁻¹)
    calc a * ((m : G) * n) * a⁻¹ * ((m : G) * n)⁻¹
        = a * m * a⁻¹ * ((a * n * a⁻¹ * (n : G)⁻¹) * (m : G)⁻¹) := by group
      _ = a * m * a⁻¹ * ((m : G)⁻¹ * (a * n * a⁻¹ * (n : G)⁻¹)) := by rw [← hz (m : G)⁻¹]
      _ = a * m * a⁻¹ * (m : G)⁻¹ * (a * n * a⁻¹ * (n : G)⁻¹) := by group)

theorem commHom_eq_one_iff {G : Type*} [Group G] {a : G} {N : Subgroup G}
    {hN : ∀ n ∈ N, a * n * a⁻¹ * n⁻¹ ∈ Subgroup.center G} (n : ↥N) :
    commHom a N hN n = 1 ↔ a * n = n * a := by
  constructor
  · intro h1
    have h2 : a * n * a⁻¹ * (n : G)⁻¹ = 1 := congrArg Subtype.val h1
    calc a * n = (a * n * a⁻¹ * (n : G)⁻¹) * (n * a) := by group
      _ = n * a := by rw [h2, one_mul]
  · intro h1
    apply Subtype.ext
    show a * n * a⁻¹ * (n : G)⁻¹ = 1
    rw [h1]
    group

theorem not_isSolvable_alternatingGroup_five : ¬ Group.IsSolvable ↥(alternatingGroup (Fin 5)) := by
  intro hA
  haveI := hA
  haveI : Group.IsSolvable ℤˣ := Group.isSolvable_of_comm fun a b => mul_comm a b
  apply Equiv.Perm.not_isSolvable_fin_5
  exact Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 5)).subtype Equiv.Perm.sign
    (by rw [Subgroup.range_subtype]; exact le_rfl)

end Twisted

section Lift

open CFSG.HardMathSupport.Timmesfeld.LinearRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

@[expose] def Input8_2Lift (k₀ : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → GLAPPrimeCore 5 K = ⊥ →
    ∀ x : MulAut K, Lemma1314.PumpupVia 5 ↥(alternatingGroup (Fin 5)) K x →
      ∀ k : ℕ, k₀ ≤ k → ∀ (hk : 1 ≤ k) (L : Type) [Field L] [Finite L] (h : UnitaryFieldData 2 2 L)
        (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU (5 * k) (2 ^ 2) L))
        (A : primeFormUnitary h (idGram L (5 * k))),
        BalanceLp.modelHom (e.trans (BalanceLp.statedProjEquivPrimeFormP h (by omega))) x =
            primeFormConjHom h (idGram L (5 * k)) A →
          (A : GL (Fin (5 * k)) L) ^ 5 = 1

theorem pow_five_eq_one_of_pumpup (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hK : CFSG.LocalAnalysis.GLTheoremA.IsKHat K) (hO : GLAPPrimeCore 5 K = ⊥) (x : MulAut K)
    (hx : Lemma1314.PumpupVia 5 ↥(alternatingGroup (Fin 5)) K x) {L : Type} [Field L] [Finite L]
    (h : UnitaryFieldData 2 2 L) (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU 5 (2 ^ 2) L))
    (A : primeFormUnitary h (idGram L 5))
    (hA : BalanceLp.modelHom (e.trans (BalanceLp.statedProjEquivPrimeFormP h (by norm_num))) x =
      primeFormConjHom h (idGram L 5) A) :
    (A : GL (Fin 5) L) ^ 5 = 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hL : Nat.card L = (2 ^ 2) ^ 2 := h.card.trans (by norm_num)
  have hKc : commutator K = ⊤ := hK.1.1
  have hZ : IsPGroup 5 (Subgroup.center K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i271h_center_isPGroup (by norm_num) hO
  obtain ⟨φ, hφs, hφ⟩ := exists_cover_su54 hGA hL hKc hZ e
  have hSU := commutator_statedSU54 hL
  have hx5 : x ^ 5 = 1 := by rw [← hx.1]; exact pow_orderOf_eq_one x
  have hA5 : primeFormConjHom h (idGram L 5) (A ^ 5) = 1 := by
    rw [map_pow, ← hA, ← map_pow, hx5, map_one]
  obtain ⟨c, hc⟩ := (CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff).1
    ((primeFormConjHom_eq_one_iff_center h (by norm_num) (by norm_num) (A ^ 5)).1 hA5)
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 5) c ∈ primeFormUnitary h (idGram L 5) := by
    rw [← hc]
    exact (A ^ 5).2
  rw [Subgroup.coe_pow] at hc
  by_contra hne
  have hc1 : c ≠ 1 := fun hc1 => hne (by rw [hc, hc1, map_one])
  have hc5 : (c : L) ^ 5 = 1 := by
    have h1 := norm_eq_one_of_scalar_mem_primeFormUnitary h (by norm_num) 1 hmem
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at h1
    calc (c : L) ^ 5 = (c : L) * (c : L) ^ 2 ^ 2 := by ring
      _ = 1 := h1
  have hcp : ∀ b : L, b ^ 5 ≠ (c : L) := by
    intro b hb
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by rw [← hb]; norm_num)
    haveI : Fintype L := Fintype.ofFinite L
    have h15 : b ^ 15 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one b hb0
      rwa [← Nat.card_eq_fintype_card, hL] at this
    have h25 : b ^ 25 = 1 := by rw [show (25 : ℕ) = 5 * 5 by rfl, pow_mul, hb, hc5]
    have h5 : b ^ 5 = 1 := by
      calc b ^ 5 = b ^ 25 * b ^ 5 := by rw [h25, one_mul]
        _ = (b ^ 15) ^ 2 := by ring
        _ = 1 := by rw [h15, one_pow]
    exact hc1 (Units.ext (by rw [Units.val_one, ← hb, h5]))
  have hAmat : ((A : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) ^ 5 = Matrix.scalar (Fin 5) (c : L) := by
    rw [← Units.val_pow_eq_pow_val, hc, Matrix.GeneralLinearGroup.coe_scalar]
  have hcomm : ∀ s t : GL (Fin 5) L, (A : GL (Fin 5) L) * s = s * A → (A : GL (Fin 5) L) * t = t * A →
      s * t = t * s := by
    intro s t hs ht
    have h1 := commute_of_commute_of_pow_eq_scalar hcp hAmat (B := (s : Matrix (Fin 5) (Fin 5) L))
      (C := (t : Matrix (Fin 5) (Fin 5) L)) (congrArg Units.val hs) (congrArg Units.val ht)
    exact Units.ext h1.eq
  have hscal : ∀ u : ↥(StatedSU 5 (2 ^ 2) L), φ u = 1 →
      (u : GL (Fin 5) L) ∈ Subgroup.center (GL (Fin 5) L) := by
    intro u hu
    have h1 : (QuotientGroup.mk u : StatedProj (StatedSU 5 (2 ^ 2) L)) = 1 := by
      rw [← hφ, hu, QuotientGroup.mk_one, map_one]
    have h2 := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff u).1 h1)
    rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h2
  set N₀ : Subgroup ↥(StatedSU 5 (2 ^ 2) L) := (Lemma1314.fixSub x).comap φ with hN₀
  set N : Subgroup (GL (Fin 5) L) := N₀.map (StatedSU 5 (2 ^ 2) L).subtype with hNdef
  have hAN := BalanceLp.mem_normalizer_statedSU h A (n := 5) (ℓ := 2) (f := 2)
  have hδ : ∀ g ∈ N, (A : GL (Fin 5) L) * g * (A : GL (Fin 5) L)⁻¹ * g⁻¹ ∈ Subgroup.center (GL (Fin 5) L) := by
    rintro _ ⟨s, hs, rfl⟩
    let t : ↥(StatedSU 5 (2 ^ 2) L) :=
      ⟨(A : GL (Fin 5) L) * s * (A : GL (Fin 5) L)⁻¹, (Subgroup.mem_normalizer_iff.1 hAN s).1 s.2⟩
    have h1 : x (φ s) = φ t := cover_conj h (by norm_num) e hSU φ hφ x A hA s t rfl
    have h2 : x (φ s) = φ s := hs
    have h3 : φ (t * s⁻¹) = 1 := by rw [map_mul, map_inv, ← h1, h2, mul_inv_cancel]
    exact hscal _ h3
  let δ := commHom (A : GL (Fin 5) L) N hδ
  haveI : Group.IsSolvable ↥δ.ker := Group.isSolvable_of_comm fun a b => by
    have ha := (commHom_eq_one_iff (a : ↥N)).1 a.2
    have hb := (commHom_eq_one_iff (b : ↥N)).1 b.2
    exact Subtype.ext (Subtype.ext (hcomm _ _ ha hb))
  haveI : Group.IsSolvable ↥(Subgroup.center (GL (Fin 5) L)) := Group.isSolvable_of_comm fun a b =>
    Subtype.ext ((Subgroup.mem_center_iff.1 b.2) a)
  haveI hNs : Group.IsSolvable ↥N :=
    Group.isSolvable_of_ker_le_range δ.ker.subtype δ (by rw [Subgroup.range_subtype])
  let ι : ↥N₀ →* ↥N :=
    ((StatedSU 5 (2 ^ 2) L).subtype.comp N₀.subtype).codRestrict N fun s => ⟨s, s.2, rfl⟩
  have hι : Function.Injective ι := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun g : ↥N => (g : GL (Fin 5) L)) hab))
  haveI : Group.IsSolvable ↥N₀ := Group.isSolvable_of_isSolvable_injective hι
  let ψ : ↥N₀ →* ↥(Lemma1314.fixSub x) := (φ.comp N₀.subtype).codRestrict _ fun s => s.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨s, rfl⟩ := hφs y
    exact ⟨⟨s, hy⟩, rfl⟩
  haveI : Group.IsSolvable ↥(Lemma1314.fixSub x) := Group.isSolvable_of_surjective hψ
  obtain ⟨-, J₁, hJ₁, ⟨eJ⟩⟩ := hx
  haveI : Group.IsSolvable ↥J₁ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJ₁.1)
  haveI : Group.IsSolvable (CFSG.HardMathSupport.Solomon.LocalBalance.barOf 5 J₁) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  exact not_isSolvable_alternatingGroup_five
    (Group.isSolvable_of_surjective (f := eJ.toMonoidHom) eJ.surjective)

theorem input8_2Lift_one (hGA : CFSG.Open.GriessAllModelsStatement) (h2 : Input8_2Lift 2) :
    Input8_2Lift 1 := by
  intro K _ _ hK hO x hx k hk1 hk L _ _ h e A hA
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    exact pow_five_eq_one_of_pumpup hGA hK hO x hx h e A hA
  · exact h2 K hK hO x hx k hk2 hk L h e A hA

end Lift

section Diag

open Matrix
open CFSG.HardMathSupport.Timmesfeld.LinearRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm toLinU toLinU_mem idForm_isSymm idForm_separatingLeft)

theorem exists_orthonormal_eigenbasis_five {n : ℕ} {L : Type} [Field L] (h : UnitaryFieldData 2 2 L)
    {X : primeFormUnitary h (idGram L n)} (hX : X ^ 5 = 1) :
    ∃ b : Fin n → Fin n → L, (∀ i j, idForm h n (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ i, ∃ μ : L, ((X : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ b i = μ • b i := by
  classical
  have := h.finite
  haveI : NeZero (5 : ℕ) := ⟨by norm_num⟩
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KCUnitaryPlane.exists_primitiveRoot_of_dvd h
    (by norm_num : Nat.Prime 5) (by norm_num : 5 ∣ 2 ^ 2 + 1)
  set T : Module.End L (Fin n → L) := ((toLinU h n X :
      LinearMap.GeneralLinearGroup L (Fin n → L)) : Module.End L (Fin n → L)) with hT
  have hpow : T ^ 5 = 1 := by
    have h1 : (toLinU h n X) ^ 5 = 1 := by rw [← map_pow, hX, map_one]
    have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup L (Fin n → L) =>
      (g : Module.End L (Fin n → L))) h1
    simpa [Units.val_pow_eq_pow_val] using h2
  have hiso : ∀ v w, idForm h n (T v) (T w) = idForm h n v w := fun v w => toLinU_mem X v w
  obtain ⟨b, μ, hbμ, hbo⟩ := CFSG.RankThree.PartOne.KCUnitaryPlane.exists_orthonormal_common_eigenbasis h hζ
    (by norm_num : 5 ∣ 2 ^ 2 + 1) (idForm_isSymm h n) (idForm_separatingLeft h n) (ι := Unit)
    (fun _ => T) (fun _ _ => Commute.refl _) (fun _ => hpow) (fun _ v w => hiso v w)
  refine ⟨b.reindex (finCongr (Module.finrank_fin_fun L)), fun i j => ?_, fun i => ?_⟩
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hbo]
    simp
  · rw [Module.Basis.reindex_apply]
    exact ⟨μ () _, hbμ () _⟩

theorem exists_unitary_conj_diagonal {n : ℕ} {L : Type} [Field L] (h : UnitaryFieldData 2 2 L)
    {X : primeFormUnitary h (idGram L n)} (hX : X ^ 5 = 1) :
    ∃ (S : primeFormUnitary h (idGram L n)) (μ : Fin n → L),
      ((X : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((S : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        ((S : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * diagonal μ := by
  classical
  obtain ⟨b, hbo, hbe⟩ := exists_orthonormal_eigenbasis_five h hX
  choose μ hμ using hbe
  set M : Matrix (Fin n) (Fin n) L := Matrix.of fun i j => b j i with hM
  have hMM : (M.map h.bar)ᵀ * M = 1 := by
    ext i j
    have h1 := hbo i j
    rw [CFSG.RankThree.PartOne.KCUnitaryFrame.idForm_eq_dotProduct] at h1
    rw [Matrix.mul_apply, Matrix.one_apply, ← h1]
    simp [hM, dotProduct]
  have hMM' : M * (M.map h.bar)ᵀ = 1 := mul_eq_one_comm.1 hMM
  let S : GL (Fin n) L := ⟨M, (M.map h.bar)ᵀ, hMM', hMM⟩
  have hS : S ∈ primeFormUnitary h (idGram L n) := by
    rw [mem_primeFormUnitary]
    show (M.map h.bar)ᵀ * ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M =
      ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
    rw [Units.val_one, Matrix.mul_one, hMM]
  refine ⟨⟨S, hS⟩, μ, ?_⟩
  show ((X : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M = M * diagonal μ
  ext i j
  have h1 : (((X : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i j =
      (((X : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ b j) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hM]
  rw [h1, hμ j, Pi.smul_apply, smul_eq_mul, Matrix.mul_diagonal, hM, Matrix.of_apply, mul_comm]

@[expose] def prodHom (M : Type*) [CommGroup M] (n : ℕ) : (Fin n → M) →* M where
  toFun d := ∏ i, d i
  map_one' := by simp
  map_mul' a b := by simp [Finset.prod_mul_distrib]

theorem card_ker_prodHom {M : Type*} [CommGroup M] [Finite M] {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (prodHom M n).ker * Nat.card M = Nat.card M ^ n := by
  classical
  have hs : Function.Surjective (prodHom M n) := fun z =>
    ⟨Pi.mulSingle ⟨0, hn⟩ z, by simp [prodHom]⟩
  rw [Subgroup.card_ker_mul_card_of_surjective hs, Nat.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

@[expose] noncomputable def conjDiag {L : Type} [Field L] {n : ℕ} (S : GL (Fin n) L) :
    (Fin n → ↥(rootsOfUnity 5 L)) →* GL (Fin n) L :=
  (MulAut.conj S).toMonoidHom.comp
    ((CFSG.SectionRank.OddCover.diagHom n).comp ((rootsOfUnity 5 L).subtype.compLeft (Fin n)))

theorem conjDiag_apply {L : Type} [Field L] {n : ℕ} (S : GL (Fin n) L) (d : Fin n → ↥(rootsOfUnity 5 L)) :
    conjDiag S d = S * CFSG.SectionRank.OddCover.diagHom n (fun i => (d i : Lˣ)) * S⁻¹ := rfl

theorem conjDiag_injective {L : Type} [Field L] {n : ℕ} (S : GL (Fin n) L) :
    Function.Injective (conjDiag S) := by
  intro a b hab
  rw [conjDiag_apply, conjDiag_apply, mul_left_inj, mul_right_inj] at hab
  funext i
  exact Subtype.ext (congrFun (CFSG.SectionRank.OddCover.diagHom_injective n hab) i)

theorem diagHom_mem_primeFormUnitary {L : Type} [Field L] (h : UnitaryFieldData 2 2 L) {n : ℕ}
    (d : Fin n → Lˣ) (hd : ∀ i, (d i : L) ^ 5 = 1) :
    CFSG.SectionRank.OddCover.diagHom n d ∈ primeFormUnitary h (idGram L n) := by
  rw [mem_primeFormUnitary, CFSG.SectionRank.OddCover.coe_diagHom]
  show ((diagonal fun i => (d i : L)).map h.bar)ᵀ * ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      diagonal (fun i => (d i : L)) = ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  rw [Units.val_one, Matrix.mul_one, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  rw [UnitaryFieldData.bar_apply]
  calc (d i : L) ^ 2 ^ 2 * d i = (d i : L) ^ 5 := by ring
    _ = 1 := hd i

theorem exists_F_of_lift {L : Type} [Field L] [Finite L] (h : UnitaryFieldData 2 2 L) {n : ℕ} (hn : 3 ≤ n)
    (hn5 : 5 ∣ n) {K : Type} [Group K] (e₁ : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU n (2 ^ 2) L))
    (φ : ↥(StatedSU n (2 ^ 2) L) →* K) (hφs : Function.Surjective φ)
    (hφ : ∀ s, e₁ (QuotientGroup.mk (φ s)) = QuotientGroup.mk s) (x : MulAut K)
    (A : primeFormUnitary h (idGram L n))
    (hA : BalanceLp.modelHom (e₁.trans (BalanceLp.statedProjEquivPrimeFormP h (by omega))) x =
      primeFormConjHom h (idGram L n) A)
    (hA5 : A ^ 5 = 1) :
    ∃ F : Subgroup K, F ≤ Lemma1314.fixSub x ∧ IsElemAbelian 5 F ∧
      omegaOne 5 (Subgroup.center K) ≤ F ∧
      Nat.card F = 5 ^ (n - 2) * Nat.card (omegaOne 5 (Subgroup.center K)) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hL : Nat.card L = (2 ^ 2) ^ 2 := h.card.trans (by norm_num)
  have hSU := commutator_statedSU4 hL hn
  obtain ⟨S, μ, hAS⟩ := exists_unitary_conj_diagonal h hA5
  haveI : NeZero (5 : ℕ) := ⟨by norm_num⟩
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KCUnitaryPlane.exists_primitiveRoot_of_dvd h
    (by norm_num : Nat.Prime 5) (by norm_num : 5 ∣ 2 ^ 2 + 1)
  have hμ5 : Nat.card ↥(rootsOfUnity 5 L) = 5 := hζ.card_rootsOfUnity
  haveI : Finite ↥(rootsOfUnity 5 L) := Nat.finite_of_card_ne_zero (by rw [hμ5]; norm_num)
  have hroot : ∀ u : ↥(rootsOfUnity 5 L), ((u : Lˣ) : L) ^ 5 = 1 := fun u =>
    (mem_rootsOfUnity' 5 (u : Lˣ)).1 u.2
  set T₀ : Subgroup (Fin n → ↥(rootsOfUnity 5 L)) := (prodHom (↥(rootsOfUnity 5 L)) n).ker with hT₀
  set Fh : Subgroup (GL (Fin n) L) := T₀.map (conjDiag (S : GL (Fin n) L)) with hFh
  have hFhc : Nat.card Fh = 5 ^ (n - 1) := by
    rw [hFh, Subgroup.card_map_of_injective (conjDiag_injective _)]
    have h1 := card_ker_prodHom (M := ↥(rootsOfUnity 5 L)) hn1
    rw [hμ5] at h1
    have h2 : 5 ^ n = 5 ^ (n - 1) * 5 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have hSm : ((S : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (((S : GL (Fin n) L)⁻¹ : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hSm' : (((S : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      ((S : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hFhSU : Fh ≤ StatedSU n (2 ^ 2) L := by
    rintro _ ⟨d, hd, rfl⟩
    rw [BalanceLp.statedSU_eq_gramSU h n, mem_gramSU_iff_unitary, conjDiag_apply]
    refine ⟨(primeFormUnitary h (idGram L n)).mul_mem ((primeFormUnitary h (idGram L n)).mul_mem S.2
      (diagHom_mem_primeFormUnitary h _ fun i => hroot (d i))) ((primeFormUnitary h (idGram L n)).inv_mem S.2),
      ?_⟩
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, hSm,
      Matrix.det_one, one_mul, CFSG.SectionRank.OddCover.det_diagHom]
    have h1 : (prodHom (↥(rootsOfUnity 5 L)) n) d = 1 := hd
    have h2 : ∏ i, ((d i : Lˣ) : L) = (((∏ i, d i : ↥(rootsOfUnity 5 L)) : Lˣ) : L) := by
      rw [← Units.coe_prod]
      congr 1
      exact (map_prod (rootsOfUnity 5 L).subtype d Finset.univ).symm
    rw [h2]
    have h3 : (∏ i, d i : ↥(rootsOfUnity 5 L)) = 1 := h1
    rw [h3]
    rfl
  have hFhA : ∀ g ∈ Fh, (A : GL (Fin n) L) * g = g * A := by
    rintro _ ⟨d, -, rfl⟩
    apply Units.ext
    rw [conjDiag_apply]
    set Sm := ((S : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
    set Si := (((S : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
    set Am := ((A : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAmdef
    set D := ((CFSG.SectionRank.OddCover.diagHom n (fun i => (d i : Lˣ)) : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) with hD
    have hDd : D = diagonal fun i => ((d i : Lˣ) : L) := CFSG.SectionRank.OddCover.coe_diagHom _
    have hAm : Am = Sm * diagonal μ * Si := by
      calc Am = Am * (Sm * Si) := by rw [hSm, Matrix.mul_one]
        _ = (Am * Sm) * Si := by rw [Matrix.mul_assoc]
        _ = Sm * diagonal μ * Si := by rw [hAS]
    have hDD : diagonal μ * D = D * diagonal μ := by
      rw [hDd, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    show Am * (Sm * D * Si) = Sm * D * Si * Am
    calc Am * (Sm * D * Si) = Sm * diagonal μ * (Si * Sm) * D * Si := by
          rw [hAm]; simp only [Matrix.mul_assoc]
      _ = Sm * (diagonal μ * D) * Si := by rw [hSm', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Sm * (D * diagonal μ) * Si := by rw [hDD]
      _ = Sm * D * (Si * Sm) * diagonal μ * Si := by rw [hSm', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Sm * D * Si * Am := by rw [hAm]; simp only [Matrix.mul_assoc]
  set Zs : Subgroup ↥(StatedSU n (2 ^ 2) L) :=
    (StatedScalars (Fin n) L).subgroupOf (StatedSU n (2 ^ 2) L) with hZs
  set F' : Subgroup ↥(StatedSU n (2 ^ 2) L) := Fh.subgroupOf (StatedSU n (2 ^ 2) L) with hF'
  have hkerZs : φ.ker ≤ Zs := by
    intro u hu
    have h1 : (QuotientGroup.mk u : StatedProj (StatedSU n (2 ^ 2) L)) = 1 := by
      rw [← hφ, (MonoidHom.mem_ker).1 hu, QuotientGroup.mk_one, map_one]
    exact (QuotientGroup.eq_one_iff u).1 h1
  have hZsc : ∀ s ∈ Zs, ∃ c : Lˣ, c ^ 5 = 1 ∧ c ^ n = 1 ∧
      (s : GL (Fin n) L) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    intro s hs
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hs
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (2 ^ 2) L := by rw [hc]; exact s.2
    obtain ⟨hcn, hcq⟩ := ((CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hL hn1).2.1 c).1 hmem
    exact ⟨c, hcq, hcn, hc.symm⟩
  have hZsF' : Zs ≤ F' := by
    intro s hs
    obtain ⟨c, hc5, hcn, hsc⟩ := hZsc s hs
    rw [hF', Subgroup.mem_subgroupOf, hsc]
    let c' : ↥(rootsOfUnity 5 L) := ⟨c, (mem_rootsOfUnity 5 c).2 hc5⟩
    refine ⟨fun _ => c', ?_, ?_⟩
    · show ∏ _i : Fin n, c' = 1
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact Subtype.ext (by simpa using hcn)
    · rw [conjDiag_apply]
      show (S : GL (Fin n) L) * CFSG.SectionRank.OddCover.diagHom n (fun _ => c) * (S : GL (Fin n) L)⁻¹ = _
      rw [diagHom_const, ← Matrix.GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]
  have hZK : Subgroup.center K = Zs.map φ := by
    apply le_antisymm
    · intro z hz
      obtain ⟨s, rfl⟩ := hφs z
      refine ⟨s, ?_, rfl⟩
      have h1 : (QuotientGroup.mk s : StatedProj (StatedSU n (2 ^ 2) L)) = 1 := by
        rw [← hφ, (QuotientGroup.eq_one_iff (φ s)).2 hz, map_one]
      exact (QuotientGroup.eq_one_iff s).1 h1
    · rintro _ ⟨s, hs, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨t, rfl⟩ := hφs y
      obtain ⟨c, -, -, hsc⟩ := hZsc s hs
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hsc, Matrix.GeneralLinearGroup.scalar_commute]
  have hZ5 : ∀ z ∈ Subgroup.center K, z ^ 5 = 1 := by
    intro z hz
    rw [hZK] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    obtain ⟨c, hc5, -, hsc⟩ := hZsc s hs
    rw [← map_pow]
    have : s ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hsc, ← map_pow, hc5, map_one]; rfl)
    rw [this, map_one]
  have hΩ : omegaOne 5 (Subgroup.center K) = Subgroup.center K := by
    have h1 : {x | x ∈ Subgroup.center K ∧ x ^ 5 = 1} = (Subgroup.center K : Set K) := by
      ext z
      exact ⟨fun hz => hz.1, fun hz => ⟨hz, hZ5 z hz⟩⟩
    rw [omegaOne, h1, Subgroup.closure_eq]
  refine ⟨F'.map φ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    have h1 := hFhA (s : GL (Fin n) L) hs
    exact cover_conj h hn1 e₁ hSU φ hφ x A hA s s (by rw [h1, mul_inv_cancel_right])
  · have hT₀el : IsElemAbelian 5 T₀ := by
      refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm (a : Fin n → ↥(rootsOfUnity 5 L)) b)⟩⟩, fun d _ => ?_⟩
      funext i
      exact Subtype.ext (Units.ext (by simpa using hroot (d i)))
    exact CFSG.SectionRank.isElemAbelian_map
      (isElemAbelian_subgroupOf (CFSG.SectionRank.isElemAbelian_map hT₀el _)) φ
  · rw [hΩ, hZK]
    exact Subgroup.map_mono hZsF'
  · have hF'c : Nat.card F' = 5 ^ (n - 1) := by
      rw [← hFhc]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFhSU).toEquiv
    have hZsc' : Nat.card Zs = 5 := by
      have := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hL hn1).2.2
      rw [this]
      exact Nat.gcd_eq_right hn5
    have h1 := Claims1110e.card_map_mul_card_inf_ker φ F'
    have h2 := Claims1110e.card_map_mul_card_inf_ker φ Zs
    rw [inf_eq_right.2 (hkerZs.trans hZsF'), hF'c] at h1
    rw [inf_eq_right.2 hkerZs, hZsc'] at h2
    rw [hΩ, hZK]
    have hm : 0 < Nat.card φ.ker := Nat.card_pos
    have h3 : 5 ^ (n - 1) = 5 ^ (n - 2) * 5 := by
      rw [← pow_succ]
      congr 1
      omega
    apply Nat.eq_of_mul_eq_mul_right hm
    rw [h1, h3, ← h2, mul_assoc]

end Diag

theorem input30_5_of (hGA : CFSG.Open.GriessAllModelsStatement) (hLift : Input8_2Lift 1) :
    Claims1110f.Input30_5 := by
  intro K _ _ hK hO x hx k hk hU
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨L, _, _, hL, ⟨e₀⟩⟩ := hU
  have hL' : Nat.card L = (2 ^ 2) ^ 2 := hL.trans (by norm_num)
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 2 L :=
    ⟨Nat.prime_two, by norm_num, hL.trans (by norm_num)⟩
  have hn : 3 ≤ 5 * k := by omega
  have hKc : commutator K = ⊤ := hK.1.1
  have hZ : IsPGroup 5 (Subgroup.center K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i271h_center_isPGroup (by norm_num) hO
  let e₁ : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU (5 * k) (2 ^ 2) L) := e₀
  obtain ⟨φ, hφs, hφ⟩ := exists_cover_su4 hGA hL' hn (dvd_mul_right 5 k) hKc hZ e₁
  have hx5 : x ^ 5 = 1 := by rw [← hx.1]; exact pow_orderOf_eq_one x
  have hxD : BalanceLp.modelHom (e₁.trans (BalanceLp.statedProjEquivPrimeFormP h (by omega : 1 ≤ 5 * k))) x ∈
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormD h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram L (5 * k)) :=
    mem_primeFormD_of_pow' h hn _ (k := 1) (by rw [pow_one, ← map_pow, hx5, map_one])
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.1 hxD
  have hA5 : (A : GL (Fin (5 * k)) L) ^ 5 = 1 := hLift K hK hO x hx k hk hk L h e₁ A hA.symm
  have hA5' : A ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hA5]; rfl)
  obtain ⟨F, hF⟩ := exists_F_of_lift h hn (dvd_mul_right 5 k) e₁ φ hφs hφ x A hA.symm hA5'
  exact ⟨F, hF⟩

section HighTools

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem exists_derivedSeries_succ_eq (G : Type*) [Group G] [Finite G] :
    ∃ i, derivedSeries G (i + 1) = derivedSeries G i := by
  by_contra hne
  push Not at hne
  have hlt : ∀ i, Nat.card (derivedSeries G (i + 1)) < Nat.card (derivedSeries G i) := fun i =>
    Subgroup.card_lt_of_lt (lt_of_le_of_ne (derivedSeries_antitone G (Nat.le_succ i)) (hne i))
  have hle : ∀ i, Nat.card (derivedSeries G i) + i ≤ Nat.card G := by
    intro i
    induction i with
    | zero => rw [derivedSeries_zero, Subgroup.card_top, add_zero]
    | succ i ih => have := hlt i; omega
  have h1 := hle (Nat.card G + 1)
  have h2 : 0 < Nat.card (derivedSeries G (Nat.card G + 1)) := Nat.card_pos
  omega

theorem eq_of_perfect_subnormal {F : Type*} [Group F] {S P : Subgroup F}
    (hS : CFSG.Open.IsQuasisimple ↥S) (hPS : P ≤ S) (hsub : CFSG.Open.IsSubnormal P S)
    (hperf : ⁅P, P⁆ = P) (hne : P ≠ ⊥) : P = S := by
  have h1 : CFSG.Open.IsSubnormal (P.subgroupOf S) ⊤ := by
    have := hsub.comap S.subtype
    rwa [show S.comap S.subtype = ⊤ from Subgroup.subgroupOf_self S] at this
  rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hS _ h1 with hc | ht
  · exfalso
    apply hne
    rw [← hperf, eq_bot_iff, Subgroup.commutator_le]
    intro p hp q hq
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hpc : (⟨p, hPS hp⟩ : S) ∈ Subgroup.center S := hc (Subgroup.mem_subgroupOf.2 hp)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hpc ⟨q, hPS hq⟩).symm
  · exact le_antisymm hPS (Subgroup.subgroupOf_eq_top.1 ht)

theorem isQuasisimple_unitarySpecial_two {f : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 f E)
    (hf : 2 ≤ f) {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (hW : 2 ≤ Module.finrank E W) {C : W →ₛₗ[hE.bar] W →ₗ[E] E} (hC : C.IsSymm)
    (hCl : C.SeparatingLeft) : CFSG.IsQuasisimple (unitarySpecial C) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite E := hE.finite
  obtain ⟨hsigma, hne, hk0⟩ :=
    CFSG.ComponentClassification.CatalogueBUnitaryTwo.unitaryFieldConjugation_data 2 f hE.card_eq_sq
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq := (CFSG.ComponentClassification.CatalogueBUnitaryIsometry.isometry_all_dimensions_nonsmall C hC
    (CFSG.ComponentClassification.CatalogueBUnitaryB.nondegenerate_of_isSymm hC hCl) hsigma hne
    (by omega) (by rw [hk0]; omega) (by omega) (fun h' => by
      have h3 := congrArg Prod.snd h'
      simp only at h3
      rw [hk0] at h3
      omega)).1
  set e := CFSG.ComponentClassification.CatalogueBUnitaryB.sesqUnitaryIsometryEquiv hE C with he
  have hmap : (unitarySpecial C).map e.toMonoidHom =
      CFSG.ComponentClassification.CatalogueBUnitaryIsometry.specialIsometry
        (sigma := CFSG.ComponentClassification.CatalogueBUnitaryTwo.unitaryFieldConjugation 2 f
          hE.card_eq_sq) C := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (CFSG.ComponentClassification.CatalogueBUnitaryIsometry.mem_specialIsometry_iff
        (sigma := CFSG.ComponentClassification.CatalogueBUnitaryTwo.unitaryFieldConjugation 2 f
          hE.card_eq_sq) C (e.toMonoidHom g)).mpr (mem_unitarySpecial.mp hg)
    · intro hx
      have h1 := (CFSG.ComponentClassification.CatalogueBUnitaryIsometry.mem_specialIsometry_iff
        (sigma := CFSG.ComponentClassification.CatalogueBUnitaryTwo.unitaryFieldConjugation 2 f
          hE.card_eq_sq) C x).mp hx
      exact ⟨e.symm x, mem_unitarySpecial.mpr h1, e.apply_symm_apply x⟩
  exact (isQuasisimple_congr (((unitarySpecial C).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr hmap))).2 hq

theorem derivedSeries_alternatingGroup_five (i : ℕ) :
    derivedSeries ↥(alternatingGroup (Fin 5)) i = ⊤ := by
  induction i with
  | zero => exact derivedSeries_zero _
  | succ i ih =>
    rw [derivedSeries_succ, ih, ← commutator_def]
    haveI := alternatingGroup.isSimpleGroup_five
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥(alternatingGroup (Fin 5))) with h | h
    · exfalso
      exact not_isSolvable_alternatingGroup_five ⟨⟨1, by rw [derivedSeries_one, h]⟩⟩
    · exact h

end HighTools

section High

open Polynomial Matrix
open CFSG.HardMathSupport.Timmesfeld.LinearRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem pow_five_eq_one_of_pumpup_high (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hK : CFSG.LocalAnalysis.GLTheoremA.IsKHat K) (hO : GLAPPrimeCore 5 K = ⊥) (x : MulAut K)
    (hx : Lemma1314.PumpupVia 5 ↥(alternatingGroup (Fin 5)) K x) {L : Type} [Field L] [Finite L]
    (h : UnitaryFieldData 2 2 L) {n : ℕ} (hn : 10 ≤ n) (hn5 : 5 ∣ n)
    (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU n (2 ^ 2) L))
    (A : primeFormUnitary h (idGram L n))
    (hA : BalanceLp.modelHom (e.trans (BalanceLp.statedProjEquivPrimeFormP h (by omega))) x =
      primeFormConjHom h (idGram L n) A) :
    (A : GL (Fin n) L) ^ 5 = 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hL : Nat.card L = (2 ^ 2) ^ 2 := h.card.trans (by norm_num)
  have hKc : commutator K = ⊤ := hK.1.1
  have hZ : IsPGroup 5 (Subgroup.center K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i271h_center_isPGroup (by norm_num) hO
  obtain ⟨φ, hφs, hφ⟩ := exists_cover_su4 hGA hL hn3 hn5 hKc hZ e
  have hSU := commutator_statedSU4 hL hn3
  have hx5 : x ^ 5 = 1 := by rw [← hx.1]; exact pow_orderOf_eq_one x
  have hA5 : primeFormConjHom h (idGram L n) (A ^ 5) = 1 := by
    rw [map_pow, ← hA, ← map_pow, hx5, map_one]
  obtain ⟨c, hc⟩ := (CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff).1
    ((primeFormConjHom_eq_one_iff_center h hn3 (fun h' => absurd h'.1 (by omega)) (A ^ 5)).1 hA5)
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (idGram L n) := by
    rw [← hc]
    exact (A ^ 5).2
  rw [Subgroup.coe_pow] at hc
  by_contra hne
  have hc1 : c ≠ 1 := fun hc1 => hne (by rw [hc, hc1, map_one])
  have hc5 : (c : L) ^ 5 = 1 := by
    have h1 := norm_eq_one_of_scalar_mem_primeFormUnitary h hn1 1 hmem
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at h1
    calc (c : L) ^ 5 = (c : L) * (c : L) ^ 2 ^ 2 := by ring
      _ = 1 := h1
  have hcp : ∀ b : L, b ^ 5 ≠ (c : L) := by
    intro b hb
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by rw [← hb]; norm_num)
    haveI : Fintype L := Fintype.ofFinite L
    have h15 : b ^ 15 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one b hb0
      rwa [← Nat.card_eq_fintype_card, hL] at this
    have h25 : b ^ 25 = 1 := by rw [show (25 : ℕ) = 5 * 5 by rfl, pow_mul, hb, hc5]
    have h5 : b ^ 5 = 1 := by
      calc b ^ 5 = b ^ 25 * b ^ 5 := by rw [h25, one_mul]
        _ = (b ^ 15) ^ 2 := by ring
        _ = 1 := by rw [h15, one_pow]
    exact hc1 (Units.ext (by rw [Units.val_one, ← hb, h5]))
  set Zs : Subgroup ↥(StatedSU n (2 ^ 2) L) :=
    (StatedScalars (Fin n) L).subgroupOf (StatedSU n (2 ^ 2) L) with hZs
  have hkerZs : ∀ u : ↥(StatedSU n (2 ^ 2) L), φ u = 1 → u ∈ Zs := by
    intro u hu
    have h1 : (QuotientGroup.mk u : StatedProj (StatedSU n (2 ^ 2) L)) = 1 := by
      rw [← hφ, hu, QuotientGroup.mk_one, map_one]
    exact (QuotientGroup.eq_one_iff u).1 h1
  have hZsc : ∀ s ∈ Zs, ∃ ζ : Lˣ, ζ ^ 5 = 1 ∧
      (s : GL (Fin n) L) = Matrix.GeneralLinearGroup.scalar (Fin n) ζ := by
    intro s hs
    obtain ⟨ζ, hζ⟩ := Subgroup.mem_subgroupOf.1 hs
    have hmem' : Matrix.GeneralLinearGroup.scalar (Fin n) ζ ∈ StatedSU n (2 ^ 2) L := by
      rw [hζ]; exact s.2
    obtain ⟨-, hζq⟩ := ((CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hL hn1).2.1 ζ).1 hmem'
    exact ⟨ζ, hζq, hζ.symm⟩
  have hZsc5 : Nat.card Zs = 5 := by
    rw [hZs, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hL hn1).2.2]
    exact Nat.gcd_eq_right hn5
  have hcen : ∀ u : ↥(StatedSU n (2 ^ 2) L), φ u = 1 →
      (u : GL (Fin n) L) ∈ Subgroup.center (GL (Fin n) L) := by
    intro u hu
    obtain ⟨ζ, -, hζ⟩ := hZsc u (hkerZs u hu)
    rw [hζ, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨ζ, rfl⟩
  set N₀ : Subgroup ↥(StatedSU n (2 ^ 2) L) := (Lemma1314.fixSub x).comap φ with hN₀
  set N : Subgroup (GL (Fin n) L) := N₀.map (StatedSU n (2 ^ 2) L).subtype with hNdef
  have hAN := BalanceLp.mem_normalizer_statedSU h A (n := n) (ℓ := 2) (f := 2)
  have hfixA : ∀ s : ↥(StatedSU n (2 ^ 2) L), (A : GL (Fin n) L) * s = s * A → s ∈ N₀ := by
    intro s hs
    show x (φ s) = φ s
    exact cover_conj h hn1 e hSU φ hφ x A hA s s (by rw [hs, mul_inv_cancel_right])
  have hδ : ∀ g ∈ N, (A : GL (Fin n) L) * g * (A : GL (Fin n) L)⁻¹ * g⁻¹ ∈
      Subgroup.center (GL (Fin n) L) := by
    rintro _ ⟨s, hs, rfl⟩
    let t : ↥(StatedSU n (2 ^ 2) L) :=
      ⟨(A : GL (Fin n) L) * s * (A : GL (Fin n) L)⁻¹, (Subgroup.mem_normalizer_iff.1 hAN s).1 s.2⟩
    have h1 : x (φ s) = φ t := cover_conj h hn1 e hSU φ hφ x A hA s t rfl
    have h2 : x (φ s) = φ s := hs
    have h3 : φ (t * s⁻¹) = 1 := by rw [map_mul, map_inv, ← h1, h2, mul_inv_cancel]
    exact hcen _ h3
  let δ := commHom (A : GL (Fin n) L) N hδ
  have hNA : ⁅N, N⁆ ≤ Subgroup.centralizer ({(A : GL (Fin n) L)} : Set (GL (Fin n) L)) := by
    have h1 : commutator ↥N ≤ δ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (Subgroup.mem_center_iff.1 (δ b).2 (δ a : GL (Fin n) L))
    have h2 : ⁅N, N⁆ = (commutator ↥N).map N.subtype := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [h2]
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((commHom_eq_one_iff g).1 (h1 hg)).symm
  obtain ⟨-, J₁, hJ₁, ⟨eJ⟩⟩ := hx
  set J₀ : Subgroup ↥(StatedSU n (2 ^ 2) L) := J₁.comap φ with hJ₀
  have hJ₀N : CFSG.Open.IsSubnormal J₀ N₀ := CFSG.Open.IsSubnormal.comap φ hJ₁.2.1
  obtain ⟨i₀, hi₀⟩ := exists_derivedSeries_succ_eq ↥J₀
  set D₀ : Subgroup ↥J₀ := derivedSeries ↥J₀ i₀ with hD₀
  set D : Subgroup ↥(StatedSU n (2 ^ 2) L) := D₀.map J₀.subtype with hD
  have hDJ : D ≤ J₀ := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  have hDsub : CFSG.Open.IsSubnormal D N₀ := by
    refine CFSG.Open.IsSubnormal.step hDJ ?_ hJ₀N
    have h1 : D.subgroupOf J₀ = D₀ :=
      Subgroup.comap_map_eq_self_of_injective J₀.subtype_injective _
    rw [h1, hD₀]
    exact derivedSeries_normal _ _
  have hDperf : ⁅D, D⁆ = D := by
    rw [hD, ← Subgroup.map_commutator, hD₀, ← derivedSeries_succ, hi₀]
  set Dg : Subgroup (GL (Fin n) L) := D.map (StatedSU n (2 ^ 2) L).subtype with hDg
  have hDgsub : CFSG.Open.IsSubnormal Dg N := hDsub.map _
  have hDgperf : ⁅Dg, Dg⁆ = Dg := by rw [hDg, ← Subgroup.map_commutator, hDperf]
  have hDgN : Dg ≤ N := hDgsub.le
  have hDgA : ∀ d ∈ Dg, (A : GL (Fin n) L) * d = d * A := by
    intro d hd
    rw [← hDgperf] at hd
    exact (Subgroup.mem_centralizer_singleton_iff.1
      (hNA (Subgroup.commutator_mono hDgN hDgN hd))).symm
  set P : L[X] := X ^ 5 - Polynomial.C (c : L) with hP
  have hPirr : Irreducible P := X_pow_sub_C_irreducible_of_prime (by norm_num) hcp
  haveI : Fact (Irreducible P) := ⟨hPirr⟩
  have hP0 : P ≠ 0 := hPirr.ne_zero
  set xA : Module.End L (Fin n → L) :=
    Matrix.toLinAlgEquiv' ((A : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hxA
  have haeval : aeval xA P = 0 := by
    have h1 : xA ^ 5 = algebraMap L (Module.End L (Fin n → L)) (c : L) := by
      rw [hxA, ← map_pow, ← Units.val_pow_eq_pow_val, hc, Matrix.GeneralLinearGroup.coe_scalar,
        ← AlgEquiv.commutes Matrix.toLinAlgEquiv' (c : L)]
      rfl
    rw [hP, map_sub, aeval_X_pow, aeval_C, h1, sub_self]
  set φQ : AdjoinRoot P →ₐ[L] Module.End L (Fin n → L) :=
    Ideal.Quotient.liftₐ (Ideal.span {P}) (aeval xA) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, haeval, mul_zero]) with hφQ
  have hφroot : φQ (AdjoinRoot.root P) = xA := by
    rw [← AdjoinRoot.mk_X]
    exact aeval_X xA
  letI : Module (AdjoinRoot P) (Fin n → L) := Module.compHom (Fin n → L) φQ.toRingHom
  have hsmul : ∀ (l : AdjoinRoot P) (v : Fin n → L), l • v = φQ l v := fun _ _ => rfl
  haveI : IsScalarTower L (AdjoinRoot P) (Fin n → L) := ⟨fun a l v => by
    rw [hsmul, hsmul, map_smul, LinearMap.smul_apply]⟩
  haveI : Module.Finite L (AdjoinRoot P) := (AdjoinRoot.powerBasis hP0).finite
  haveI : Finite (AdjoinRoot P) := Module.finite_of_finite L
  haveI : Module.Finite (AdjoinRoot P) (Fin n → L) :=
    Module.Finite.of_restrictScalars_finite L (AdjoinRoot P) (Fin n → L)
  have hdimL : Module.finrank L (AdjoinRoot P) = 5 := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hP0), AdjoinRoot.powerBasis_dim hP0,
      natDegree_X_pow_sub_C]
  set m := Module.finrank (AdjoinRoot P) (Fin n → L) with hm
  have hdim : 5 * m = n := by
    rw [hm, ← hdimL, Module.finrank_mul_finrank L (AdjoinRoot P) (Fin n → L), Module.finrank_fin_fun]
  have hm2 : 2 ≤ m := by omega
  have hcardQ : Nat.card (AdjoinRoot P) = 2 ^ (2 * (2 * 5)) := by
    rw [Module.natCard_eq_pow_finrank (K := L), hdimL, h.card, ← pow_mul]
  have hQ : UnitaryFieldData 2 (2 * 5) (AdjoinRoot P) := ⟨Nat.prime_two, by norm_num, hcardQ⟩
  have hbarK : ∀ a : L, hQ.bar (algebraMap L (AdjoinRoot P) a) =
      algebraMap L (AdjoinRoot P) (h.bar a) := by
    intro a
    rw [UnitaryFieldData.bar_apply, ← map_pow,
      CFSG.StandardType.OrdPOutSU.pow_two_pow_mul_odd h (by decide : Odd 5)]
  have hrootp : AdjoinRoot.root P ^ 5 = algebraMap L (AdjoinRoot P) (c : L) := by
    have h0 := AdjoinRoot.eval₂_root P
    rw [hP, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h0
    rw [h0, AdjoinRoot.algebraMap_eq]
  have hbarRoot : hQ.bar (AdjoinRoot.root P) * AdjoinRoot.root P = 1 := by
    rw [UnitaryFieldData.bar_apply, ← pow_succ, show 2 ^ (2 * 5) + 1 = 5 * 205 by norm_num, pow_mul,
      hrootp, ← map_pow, show (c : L) ^ 205 = ((c : L) ^ 5) ^ 41 by ring, hc5, one_pow, map_one]
  have hAiso := (gramForm_isometry_iff h 1 ((A : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).mpr
    (mem_primeFormUnitary.mp A.2)
  have hroot_smul : ∀ v : Fin n → L,
      AdjoinRoot.root P • v = ((A : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v := by
    intro v
    rw [hsmul, hφroot, hxA, Matrix.toLinAlgEquiv'_apply]
  have hadj : ∀ (l : AdjoinRoot P) (v w : Fin n → L),
      gramForm h 1 (l • v) w = gramForm h 1 v (hQ.bar l • w) := by
    let S : Subalgebra L (AdjoinRoot P) :=
      { carrier := {l | ∀ v w : Fin n → L, gramForm h (1 : Matrix (Fin n) (Fin n) L) (l • v) w =
          gramForm h (1 : Matrix (Fin n) (Fin n) L) v (hQ.bar l • w)}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          intro v w
          rw [mul_smul, ha (b • v) w, hb v (hQ.bar a • w), ← mul_smul, map_mul,
            mul_comm (hQ.bar b)]
        add_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          intro v w
          rw [add_smul, map_add (gramForm h 1), LinearMap.add_apply, ha v w, hb v w,
            map_add hQ.bar, add_smul, map_add (gramForm h 1 v)]
        algebraMap_mem' := by
          intro a
          simp only [Set.mem_ofPred_eq]
          intro v w
          rw [algebraMap_smul, hbarK, algebraMap_smul, LinearMap.map_smulₛₗ₂,
            LinearMap.map_smul] }
    have hroot : AdjoinRoot.root P ∈ S := by
      change ∀ v w, gramForm h 1 (AdjoinRoot.root P • v) w =
        gramForm h 1 v (hQ.bar (AdjoinRoot.root P) • w)
      intro v w
      set u := hQ.bar (AdjoinRoot.root P) • w with hu
      have hAu : ((A : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ u = w := by
        rw [← hroot_smul, hu, smul_smul, mul_comm, hbarRoot, one_smul]
      rw [hroot_smul, ← hAu, hAiso]
    have htop : S = ⊤ := by
      rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top]
      exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hroot)
    intro l v w
    have hl : l ∈ S := htop ▸ Algebra.mem_top
    exact hl v w
  obtain ⟨H, hHs, hHsep, hHtr⟩ := CFSG.StandardType.OrdPOutSU.exists_transfer (hK := h) (hL := hQ) hbarK
    (gramForm h (1 : Matrix (Fin n) (Fin n) L)) (gramForm_isSymm h (by simp))
    (gramForm_separatingLeft h (by simp)) hadj
  let R : Module.End (AdjoinRoot P) (Fin n → L) →* Module.End L (Fin n → L) :=
    { toFun := fun g => g.restrictScalars L, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hR : Function.Injective R := LinearMap.restrictScalars_injective L
  let e₃ : (Module.End L (Fin n → L))ˣ ≃* GL (Fin n) L :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv' :
      Module.End L (Fin n → L) ≃ₐ[L] Matrix (Fin n) (Fin n) L).toMulEquiv
  let τ : ↥(sesqUnitaryGroup H) →* GL (Fin n) L :=
    e₃.toMonoidHom.comp ((Units.map R).comp (sesqUnitaryGroup H).subtype)
  have hτi : Function.Injective τ :=
    e₃.injective.comp ((Units.map_injective hR).comp Subtype.val_injective)
  have hτv : ∀ (g : ↥(sesqUnitaryGroup H)) (v : Fin n → L),
      ((τ g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v =
        ((g : LinearMap.GeneralLinearGroup (AdjoinRoot P) (Fin n → L)) :
          Module.End (AdjoinRoot P) (Fin n → L)) v := by
    intro g v
    have e' : ((τ g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        LinearMap.toMatrix' (R ((g : LinearMap.GeneralLinearGroup (AdjoinRoot P) (Fin n → L)) :
          Module.End (AdjoinRoot P) (Fin n → L))) := rfl
    rw [e', LinearMap.toMatrix'_mulVec]
    rfl
  have hτU : ∀ g : ↥(sesqUnitaryGroup H), τ g ∈ primeFormUnitary h (idGram L n) := by
    intro g
    have hiso : ∀ x y, gramForm h (1 : Matrix (Fin n) (Fin n) L)
        (((τ g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ x)
        (((τ g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ y) =
        gramForm h (1 : Matrix (Fin n) (Fin n) L) x y := by
      intro x y
      rw [hτv, hτv, ← hHtr, ← hHtr, mem_sesqUnitaryGroup.mp g.2]
    exact mem_primeFormUnitary.mpr ((gramForm_isometry_iff h 1 _).mp hiso)
  have hτA : ∀ g : ↥(sesqUnitaryGroup H), τ g * A = A * τ g := by
    intro g
    apply Units.ext
    have hA' : ((A : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = LinearMap.toMatrixAlgEquiv' xA := by
      rw [hxA, LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv']
    rw [Units.val_mul, Units.val_mul, hA']
    change LinearMap.toMatrixAlgEquiv' (R ((g : LinearMap.GeneralLinearGroup (AdjoinRoot P) (Fin n → L)) :
        Module.End (AdjoinRoot P) (Fin n → L))) * _ =
      _ * LinearMap.toMatrixAlgEquiv' (R ((g : LinearMap.GeneralLinearGroup (AdjoinRoot P) (Fin n → L)) :
        Module.End (AdjoinRoot P) (Fin n → L)))
    rw [← map_mul, ← map_mul]
    congr 1
    refine LinearMap.ext fun v => ?_
    change ((g : LinearMap.GeneralLinearGroup (AdjoinRoot P) (Fin n → L)) :
        Module.End (AdjoinRoot P) (Fin n → L)) (xA v) =
      xA (((g : LinearMap.GeneralLinearGroup (AdjoinRoot P) (Fin n → L)) :
        Module.End (AdjoinRoot P) (Fin n → L)) v)
    have hx' : ∀ w : Fin n → L, xA w = AdjoinRoot.root P • w := fun w => by rw [hsmul, hφroot]
    rw [hx', hx', LinearMap.map_smul]
  have hτdet : ∀ g : ↥(sesqUnitaryGroup H), g ∈ unitarySpecial H →
      ((τ g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = 1 := by
    intro g hg
    have h1 := mem_unitarySpecial.mp hg
    show (LinearMap.toMatrix' (R ((g : LinearMap.GeneralLinearGroup (AdjoinRoot P) (Fin n → L)) :
      Module.End (AdjoinRoot P) (Fin n → L)))).det = 1
    rw [LinearMap.det_toMatrix']
    show LinearMap.det (((g : LinearMap.GeneralLinearGroup (AdjoinRoot P) (Fin n → L)) :
      Module.End (AdjoinRoot P) (Fin n → L)).restrictScalars L) = 1
    rw [LinearMap.det_restrictScalars, h1, map_one]
  set Sg : Subgroup (GL (Fin n) L) := (unitarySpecial H).map τ with hSg
  have hSgq : CFSG.Open.IsQuasisimple ↥Sg := by
    have hq := isQuasisimple_unitarySpecial_two hQ (by norm_num) hm2 hHs hHsep
    exact CFSG.Open.IsQuasisimple.of_mulEquiv ((unitarySpecial H).equivMapOfInjective τ hτi).symm
      ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩
  have hSgSU : Sg ≤ StatedSU n (2 ^ 2) L := by
    rintro _ ⟨g, hg, rfl⟩
    rw [BalanceLp.statedSU_eq_gramSU h n, mem_gramSU_iff_unitary]
    exact ⟨hτU g, hτdet g hg⟩
  have hSgN : Sg ≤ N := by
    intro s hs
    have hsA : (A : GL (Fin n) L) * s = s * A := by
      obtain ⟨g, -, rfl⟩ := hs
      exact (hτA g).symm
    exact ⟨⟨s, hSgSU hs⟩, hfixA ⟨s, hSgSU hs⟩ hsA, rfl⟩
  have hcommQ : ∀ t : GL (Fin n) L, (A : GL (Fin n) L) * t = t * A → ∀ (l : AdjoinRoot P) (v : Fin n → L),
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (l • v) =
        l • (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v) := by
    intro t ht l v
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective l
    rw [hsmul, hsmul]
    have e1 : φQ (AdjoinRoot.mk P p) = aeval xA p := rfl
    rw [e1]
    have hc0 : Commute ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
        ((A : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
      show ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((A : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        ((A : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
      rw [← Units.val_mul, ← Units.val_mul, ht]
    have hc1 : Commute (Matrix.toLinAlgEquiv' ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) xA := by
      rw [hxA]
      exact hc0.map Matrix.toLinAlgEquiv'
    have hc2 : Commute (Matrix.toLinAlgEquiv' ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
        (aeval xA p) :=
      Algebra.commute_of_mem_adjoin_singleton_of_commute (R := L)
        (by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨p, rfl⟩) hc1
    have h3 := LinearMap.congr_fun hc2.eq v
    rw [Module.End.mul_apply, Module.End.mul_apply, Matrix.toLinAlgEquiv'_apply,
      Matrix.toLinAlgEquiv'_apply] at h3
    exact h3
  have hlift : ∀ s : GL (Fin n) L, s ∈ primeFormUnitary h (idGram L n) →
      (A : GL (Fin n) L) * s = s * A → s ∈ τ.range := by
    intro s hsU hsA
    have hsA' : (A : GL (Fin n) L) * s⁻¹ = s⁻¹ * A := by
      calc (A : GL (Fin n) L) * s⁻¹ = s⁻¹ * (s * A) * s⁻¹ := by group
        _ = s⁻¹ * (A * s) * s⁻¹ := by rw [hsA]
        _ = s⁻¹ * A := by group
    let gQ : (Fin n → L) →ₗ[AdjoinRoot P] (Fin n → L) :=
      { toFun := fun v => ((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v
        map_add' := fun v w => Matrix.mulVec_add _ v w
        map_smul' := fun l v => hcommQ s hsA l v }
    let gQ' : (Fin n → L) →ₗ[AdjoinRoot P] (Fin n → L) :=
      { toFun := fun v => ((s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v
        map_add' := fun v w => Matrix.mulVec_add _ v w
        map_smul' := fun l v => hcommQ s⁻¹ hsA' l v }
    have h1 : gQ * gQ' = 1 := LinearMap.ext fun v => by
      show ((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ
        (((s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have h2 : gQ' * gQ = 1 := LinearMap.ext fun v => by
      show ((s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ
        (((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    let gU : LinearMap.GeneralLinearGroup (AdjoinRoot P) (Fin n → L) := ⟨gQ, gQ', h1, h2⟩
    have hsiso := (gramForm_isometry_iff h 1 ((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).mpr
      (mem_primeFormUnitary.mp hsU)
    have hgU : gU ∈ sesqUnitaryGroup H := by
      rw [mem_sesqUnitaryGroup]
      intro v w
      have hnd := traceForm_nondegenerate L (AdjoinRoot P)
      have key : ∀ c' : AdjoinRoot P, Algebra.trace L (AdjoinRoot P) (H (gQ v) (gQ w) * c') =
          Algebra.trace L (AdjoinRoot P) (H v w * c') := by
        intro c'
        have e1 : ∀ v w : Fin n → L, H v w * c' = H v (c' • w) := fun v w => by
          rw [LinearMap.map_smul, smul_eq_mul, mul_comm]
        rw [e1, e1, hHtr, hHtr]
        show gramForm h 1 (((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v)
            (c' • (((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ w)) = gramForm h 1 v (c' • w)
        rw [← hcommQ s hsA c' w, hsiso]
      have h0 := hnd.1 (H (gQ v) (gQ w) - H v w) fun c' => by
        rw [Algebra.traceForm_apply, sub_mul, map_sub, key c', sub_self]
      exact sub_eq_zero.mp h0
    refine ⟨⟨gU, hgU⟩, Units.ext ?_⟩
    show LinearMap.toMatrix' (R gQ) = ((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
    have h3 : R gQ = Matrix.toLin' ((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) :=
      LinearMap.ext fun v => (Matrix.toLin'_apply _ v).symm
    rw [h3, LinearMap.toMatrix'_toLin']
  have hDgR : Dg ≤ τ.range := by
    intro d hd
    obtain ⟨s, -, rfl⟩ := hDgN hd
    have hsU : ((s : ↥(StatedSU n (2 ^ 2) L)) : GL (Fin n) L) ∈ primeFormUnitary h (idGram L n) := by
      have h1 : ((s : ↥(StatedSU n (2 ^ 2) L)) : GL (Fin n) L) ∈ gramSU h (idGram L n) :=
        BalanceLp.statedSU_eq_gramSU h n ▸ s.2
      exact ((mem_gramSU_iff_unitary h).1 h1).1
    exact hlift _ hsU (hDgA _ hd)
  have hDgS : Dg ≤ Sg := by
    rw [← hDgperf]
    calc ⁅Dg, Dg⁆ ≤ ⁅τ.range, τ.range⁆ := Subgroup.commutator_mono hDgR hDgR
      _ = (commutator ↥(sesqUnitaryGroup H)).map τ := by
        rw [MonoidHom.range_eq_map, commutator_def, Subgroup.map_commutator]
      _ ≤ (unitarySpecial H).map τ := Subgroup.map_mono (commutator_le_unitarySpecial H)
  have hDgSsub : CFSG.Open.IsSubnormal Dg Sg := by
    have := hDgsub.inf_of_le hSgN
    rwa [inf_eq_left.2 hDgS] at this
  let ψJ : ↥J₀ →* ↥J₁ := (φ.comp J₀.subtype).codRestrict J₁ fun s => s.2
  have hψJ : Function.Surjective ψJ := by
    rintro ⟨y, hy⟩
    obtain ⟨s, rfl⟩ := hφs y
    exact ⟨⟨s, hy⟩, rfl⟩
  by_cases hD1 : Dg = ⊥
  ·
    have hD0 : D₀ = ⊥ := by
      have h1 : D = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ (StatedSU n (2 ^ 2) L).subtype_injective).1 hD1
      exact (Subgroup.map_eq_bot_iff_of_injective _ J₀.subtype_injective).1 h1
    haveI : Group.IsSolvable ↥J₀ := ⟨⟨i₀, hD0⟩⟩
    haveI : Group.IsSolvable ↥J₁ := Group.isSolvable_of_surjective hψJ
    haveI : Group.IsSolvable (CFSG.HardMathSupport.Solomon.LocalBalance.barOf 5 J₁) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
    exact not_isSolvable_alternatingGroup_five
      (Group.isSolvable_of_surjective (f := eJ.toMonoidHom) eJ.surjective)
  have hDS := eq_of_perfect_subnormal hSgq hDgS hDgSsub hDgperf hD1
  have hcardS : (Nat.card Sg : ℤ) = ((2 ^ (2 * 5) : ℕ) : ℤ) ^ (m * (m - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 m, (((2 ^ (2 * 5) : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    obtain ⟨-, hSU', -, -, hker, -, -⟩ :=
      CFSG.LinearGroups.unitary_full_group_order hQ hHs hHsep hm.symm (by omega)
    have h1 : Nat.card Sg = Nat.card (unitarySpecial H) :=
      Nat.card_congr ((unitarySpecial H).equivMapOfInjective τ hτi).symm.toEquiv
    have h2 : Nat.card (unitarySpecial H) = Nat.card (sesqSpecialUnitaryGroup H) := by
      have hker' : unitarySpecial H = (sesqSpecialUnitaryGroup H).subgroupOf (sesqUnitaryGroup H) := hker
      rw [hker']
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le H)).toEquiv
    rw [h1, h2]
    exact hSU'
  have hcardD₀ : Nat.card D₀ = Nat.card Sg := by
    rw [← hDS, hDg, hD, Subgroup.card_map_of_injective (StatedSU n (2 ^ 2) L).subtype_injective,
      Subgroup.card_map_of_injective J₀.subtype_injective]
  let ψ₀ : ↥J₀ →* ↥(alternatingGroup (Fin 5)) :=
    eJ.toMonoidHom.comp ((QuotientGroup.mk' (GLAPPrimeCore 5 ↥J₁)).comp ψJ)
  have hψ₀ : Function.Surjective ψ₀ :=
    eJ.surjective.comp ((QuotientGroup.mk'_surjective _).comp hψJ)
  have hD₀map : D₀.map ψ₀ = ⊤ := by
    rw [hD₀, map_derivedSeries_eq hψ₀, derivedSeries_alternatingGroup_five]
  have h60 : Nat.card (D₀.map ψ₀) = 60 := by
    rw [hD₀map, Subgroup.card_top, nat_card_alternatingGroup]
    simp [Nat.factorial]
  set W : Subgroup ↥J₀ := D₀ ⊓ ψ₀.ker with hW
  have hWc : W.map ψJ ≤ GLAPPrimeCore 5 ↥J₁ := by
    rintro _ ⟨u, hu, rfl⟩
    have h1 : ψ₀ u = 1 := hu.2
    have h2 : (QuotientGroup.mk' (GLAPPrimeCore 5 ↥J₁)) (ψJ u) = 1 :=
      eJ.injective (by rw [map_one]; exact h1)
    exact (QuotientGroup.eq_one_iff _).1 h2
  have hcop : Nat.Coprime 5 (Nat.card (W.map ψJ)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hWc)
      (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥J₁)
  have hb : Nat.card ↥(W ⊓ ψJ.ker) ∣ 5 := by
    have h1 : (W ⊓ ψJ.ker).map J₀.subtype ≤ Zs := by
      rintro _ ⟨u, hu, rfl⟩
      exact hkerZs _ (congrArg Subtype.val (hu.2 : ψJ u = 1))
    have h2 := Subgroup.card_dvd_of_le h1
    rwa [Subgroup.card_map_of_injective J₀.subtype_injective, hZsc5] at h2
  have hW1 := Claims1110e.card_map_mul_card_inf_ker ψ₀ D₀
  have hW2 := Claims1110e.card_map_mul_card_inf_ker ψJ W
  rw [h60] at hW1
  have htot : Nat.card Sg = 60 * Nat.card (W.map ψJ) * Nat.card ↥(W ⊓ ψJ.ker) := by
    rw [← hcardD₀, ← hW1, ← hW2, mul_assoc]
  have hcop' : ∀ j, Nat.Coprime (5 ^ j) (Nat.card (W.map ψJ)) := fun j => Nat.Coprime.pow_left j hcop
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  ·
    have hm2' : m = 2 := by omega
    have hb1 : Nat.card ↥(W ⊓ ψJ.ker) = 1 := by
      rw [Subgroup.card_eq_one, eq_bot_iff]
      intro u hu
      have hφu : φ (u : ↥(StatedSU n (2 ^ 2) L)) = 1 := congrArg Subtype.val (hu.2 : ψJ u = 1)
      obtain ⟨ζ, hζ5, hζ⟩ := hZsc _ (hkerZs _ hφu)
      have huS : (((u : ↥(StatedSU n (2 ^ 2) L)) : GL (Fin n) L)) ∈ Sg := by
        rw [← hDS]
        exact ⟨u, ⟨u, hu.1.1, rfl⟩, rfl⟩
      obtain ⟨g, hg, hgu⟩ := huS
      have hgζ : ((g : LinearMap.GeneralLinearGroup (AdjoinRoot P) (Fin n → L)) :
          Module.End (AdjoinRoot P) (Fin n → L)) = algebraMap L (AdjoinRoot P) (ζ : L) • 1 := by
        refine LinearMap.ext fun v => ?_
        rw [← hτv, hgu, hζ, LinearMap.smul_apply, Module.End.one_apply, algebraMap_smul,
          Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
        funext i
        rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      have hdet := mem_unitarySpecial.mp hg
      rw [hgζ, LinearMap.det_smul, map_one, mul_one, ← map_pow] at hdet
      have h2 : (ζ : L) ^ m = 1 :=
        (algebraMap L (AdjoinRoot P)).injective (by rw [hdet, map_one])
      rw [hm2'] at h2
      have hζ2 : ζ ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h2, Units.val_one])
      have hζ1 : ζ = 1 := by
        calc ζ = ζ ^ 5 * ((ζ ^ 2)⁻¹) ^ 2 := by group
          _ = 1 := by rw [hζ5, hζ2]; group
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      apply Subtype.ext
      rw [hζ, hζ1, map_one]
      rfl
    have h25 : (25 : ℤ) ∣ (Nat.card Sg : ℤ) := by
      rw [hcardS, hm2', show Finset.Icc 2 2 = {2} from rfl, Finset.prod_singleton]
      exact Dvd.dvd.mul_left (by norm_num) _
    have h25' : 5 ^ 2 ∣ 60 * Nat.card (W.map ψJ) := by
      have h1 := Int.natCast_dvd_natCast.mp h25
      rw [htot, hb1, mul_one] at h1
      exact h1
    have h2 := (hcop' 2).dvd_of_dvd_mul_left (by rwa [mul_comm] at h25')
    revert h2
    norm_num
  ·
    have h625 : (625 : ℤ) ∣ (Nat.card Sg : ℤ) := by
      rw [hcardS]
      refine Dvd.dvd.mul_left ?_ _
      have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 m := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rw [Finset.mem_Icc]
        omega
      refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
      rw [Finset.prod_pair (by norm_num)]
      norm_num
    have h625' : 5 ^ 4 ∣ 60 * Nat.card (W.map ψJ) * Nat.card ↥(W ⊓ ψJ.ker) := by
      have h1 := Int.natCast_dvd_natCast.mp h625
      rw [htot] at h1
      exact h1
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hb with hb' | hb'
    · rw [hb', mul_one, mul_comm] at h625'
      have h2 := (hcop' 4).dvd_of_dvd_mul_left h625'
      revert h2
      norm_num
    · rw [hb', mul_right_comm, mul_comm] at h625'
      have h2 := (hcop' 4).dvd_of_dvd_mul_left h625'
      revert h2
      norm_num

theorem input8_2Lift_two (hGA : CFSG.Open.GriessAllModelsStatement) : Input8_2Lift 2 := by
  intro K _ _ hK hO x hx k hk2 hk L _ _ h e A hA
  exact pow_five_eq_one_of_pumpup_high hGA hK hO x hx h (by omega) (dvd_mul_right 5 k) e A hA

theorem input30_5_holds (hGA : CFSG.Open.GriessAllModelsStatement) : Claims1110f.Input30_5 :=
  input30_5_of hGA (input8_2Lift_one hGA (input8_2Lift_two hGA))

end High

section Assembly


theorem lemma1110CaseB_of_pieces_g (h119 : Lemma119Statement) (h111 : Prop111Statement)
    (h112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2) (h183 : Prop115.Input18_3Gen)
    (hSeitz : Claims1116.Input23_10) (hSchur : Lemma123.InputSchurAlt')
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hO : Claims1314.Exc5Orders)
    (hLn : Claims1110f.InputA5UpLn) (h6 : Claims1110f.Step6K1Claim) : Lemma1110CaseB :=
  Claims1110f.lemma1110CaseB_of_pieces'_cert h119 h111 h112 h183 hSeitz hSchur hSpM hOut hGA hO hLn
    inputOut5Lie_holds (input30_5_holds hGA) (inputU5Sylow_of hGA) inputGammaD4_holds h6

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110g
