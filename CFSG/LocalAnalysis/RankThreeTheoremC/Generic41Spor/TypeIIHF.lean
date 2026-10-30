module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIStruct
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PlaneInT

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T U3LineWC
  card_center_of_nonabelian_card_p_cube exists_isElemAbelian_card_sq_of_nonabelian)

theorem typeII_hF_add_le_pRank {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    {E₁ E₂ H : Subgroup G} (hE₁ : IsElemAbelian p E₁) (hE₂ : IsElemAbelian p E₂) {r₁ r₂ : ℕ}
    (h₁ : Nat.card E₁ = p ^ r₁) (h₂ : Nat.card E₂ = p ^ r₂)
    (hc : ∀ x ∈ E₁, ∀ y ∈ E₂, Commute x y) (hdisj : E₁ ⊓ E₂ = ⊥)
    (h₁H : E₁ ≤ H) (h₂H : E₂ ≤ H) : r₁ + r₂ ≤ CFSG.Open.pRank p H := by
  let f : E₁ × E₂ →* G := MonoidHom.noncommCoprod E₁.subtype E₂.subtype
    (fun x y => hc x x.2 y y.2)
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have h : (x : G) * y = 1 := hxy
    have hx : (x : G) ∈ E₁ ⊓ E₂ := Subgroup.mem_inf.2 ⟨x.2, by
      rw [eq_inv_of_mul_eq_one_left h]
      exact E₂.inv_mem y.2⟩
    rw [hdisj, Subgroup.mem_bot] at hx
    have hy : (y : G) = 1 := by rw [hx, one_mul] at h; exact h
    rw [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext hx, Subtype.ext hy⟩
  have hc₁ := hE₁.1
  have hc₂ := hE₂.1
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (A := E₁ × E₂) ?_ ?_ ?_ f hf ?_
  · rintro ⟨a, b⟩ ⟨c, d⟩
    exact Prod.ext (mul_comm' a c) (mul_comm' b d)
  · rintro ⟨a, b⟩
    exact Prod.ext (Subtype.ext (hE₁.2 a a.2)) (Subtype.ext (hE₂.2 b b.2))
  · rw [Nat.card_prod, h₁, h₂, pow_add]
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact H.mul_mem (h₁H a.2) (h₂H b.2)


theorem typeII_hF_commutator_mem {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] {T : Subgroup G}
    (hcard : Nat.card T = p ^ 3) (hnc : ¬ IsMulCommutative T) {a b : G} (ha : a ∈ T)
    (hb : b ∈ T) :
    a * b * a⁻¹ * b⁻¹ ∈ T ⊓ Subgroup.centralizer (T : Set G) := by
  have hZ : Nat.card (Subgroup.center T) = p := card_center_of_nonabelian_card_p_cube hcard hnc
  have hq : Nat.card (T ⧸ Subgroup.center T) = p ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center T)
    rw [hcard, hZ] at h
    apply Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos
    rw [← h]
    ring
  have hcomm : IsMulCommutative (T ⧸ Subgroup.center T) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  have hmem : (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : T)⁻¹ * (⟨b, hb⟩ : T)⁻¹ : T) ∈
      Subgroup.center T := by
    rw [← QuotientGroup.eq_one_iff (N := Subgroup.center T)]
    have h1 := hcomm.is_comm.comm (QuotientGroup.mk (⟨a, ha⟩ : T) : T ⧸ Subgroup.center T)
      (QuotientGroup.mk (⟨b, hb⟩ : T))
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1 ⊢
    rw [h1]
    group
  refine Subgroup.mem_inf.mpr ⟨T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha))
    (T.inv_mem hb), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have := Subgroup.mem_center_iff.mp hmem ⟨h, hh⟩
  exact congrArg Subtype.val this

theorem typeII_hF_exists_mul_of_sup_eq {G : Type*} [Group G] {T Z S : Subgroup G}
    (hcomm : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hsup : T ⊔ Z = S) :
    ∀ s ∈ S, ∃ t ∈ T, ∃ z ∈ Z, s = t * z := by
  have hrange := MonoidHom.noncommCoprod_range T.subtype Z.subtype
    (fun a b => (hcomm b b.2 a a.2).symm)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  intro s hs
  rw [← hsup, ← hrange] at hs
  obtain ⟨⟨a, b⟩, rfl⟩ := hs
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem typeII_hF_exists_elem_sq {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T A : Subgroup G}
    (hcard : Nat.card T = p ^ 3) (hexp : ∀ t ∈ T, t ^ p = 1) (hnc : ¬ IsMulCommutative T)
    (hAT : A ≤ T) (hdvd : p ^ 2 ∣ Nat.card A) :
    ∃ E : Subgroup G, E ≤ A ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have hp : p.Prime := Fact.out
  have hAdvd : Nat.card A ∣ p ^ 3 := by
    have h := Subgroup.card_dvd_of_le hAT
    rwa [hcard] at h
  obtain ⟨i, hi, hAi⟩ := (Nat.dvd_prime_pow hp).mp hAdvd
  rw [hAi] at hdvd
  have h2i : 2 ≤ i := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  interval_cases i
  · have hcomm : IsMulCommutative A := IsPGroup.isMulCommutative_of_card_eq_prime_sq hAi
    exact ⟨A, le_rfl, ⟨hcomm, fun a ha => hexp a (hAT ha)⟩, hAi⟩
  · have hAT' : A = T := Subgroup.eq_of_le_of_card_ge hAT (le_of_eq (by rw [hAi, hcard]))
    obtain ⟨E, hET, hE, hEcard, -⟩ := exists_isElemAbelian_card_sq_of_nonabelian hcard hexp hnc
    exact ⟨E, hAT' ▸ hET, hE, hEcard⟩

theorem typeII_hF_rank_contra {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T Z F E : Subgroup G} {x : G}
    (hxZ : x ∈ Z) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hZT : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hTZ : T ⊓ Z = ⊥)
    (hxF : x ∈ F) (hrk : CFSG.Open.pRank p F ≤ 2)
    (hET : E ≤ T) (hEF : E ≤ F) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) : False := by
  have hp : p.Prime := Fact.out
  have hXZ : Subgroup.zpowers x ≤ Z := Subgroup.zpowers_le.mpr hxZ
  have hXF : Subgroup.zpowers x ≤ F := Subgroup.zpowers_le.mpr hxF
  have hXcard : Nat.card (Subgroup.zpowers x) = p ^ 1 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1, pow_one]
  have hXel : IsElemAbelian p (Subgroup.zpowers x) := by
    refine ⟨inferInstance, ?_⟩
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hcomm : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers x, Commute a b := fun a ha b hb =>
    (hZT b (hXZ hb) a (hET ha)).symm
  have hdisj : E ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ T ⊓ Z := ⟨hET hg.1, hXZ hg.2⟩
    rwa [hTZ] at this
  have h := typeII_hF_add_le_pRank hp hE hXel hEcard hXcard hcomm hdisj hEF hXF
  omega


theorem typeII_hF_card_inf_le {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T Z F : Subgroup G} {x : G}
    (hTcard : Nat.card T = p ^ 3) (hTexp : ∀ t ∈ T, t ^ p = 1) (hTnab : ¬ IsMulCommutative T)
    (hxZ : x ∈ Z) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hZT : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hTZ : T ⊓ Z = ⊥)
    (hxF : x ∈ F) (hrk : CFSG.Open.pRank p F ≤ 2) :
    Nat.card (F ⊓ T : Subgroup G) ≤ p := by
  have hp : p.Prime := Fact.out
  have hAT : F ⊓ T ≤ T := inf_le_right
  have hAdvd : Nat.card (F ⊓ T : Subgroup G) ∣ p ^ 3 := by
    have h := Subgroup.card_dvd_of_le hAT
    rwa [hTcard] at h
  obtain ⟨i, hi, hAi⟩ := (Nat.dvd_prime_pow hp).mp hAdvd
  by_contra hlt
  push Not at hlt
  have h2i : 2 ≤ i := by
    by_contra hi2
    push Not at hi2
    have : Nat.card (F ⊓ T : Subgroup G) ≤ p := by
      rw [hAi]
      calc p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        _ = p := pow_one p
    omega
  obtain ⟨E, hEA, hE, hEcard⟩ := typeII_hF_exists_elem_sq hTcard hTexp hTnab hAT
    (by rw [hAi]; exact pow_dvd_pow p h2i)
  exact typeII_hF_rank_contra hxZ hx1 hxp hZT hTZ hxF hrk (hEA.trans hAT)
    (hEA.trans inf_le_left) hE hEcard

theorem typeII_hF_commute_of_mem_inf {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T Z F : Subgroup G} {x : G}
    (hTcard : Nat.card T = p ^ 3) (hTexp : ∀ t ∈ T, t ^ p = 1) (hTnab : ¬ IsMulCommutative T)
    (hxZ : x ∈ Z) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hZT : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hTZ : T ⊓ Z = ⊥)
    (hFP : F ≤ T ⊔ Z) (hxF : x ∈ F) (hrk : CFSG.Open.pRank p F ≤ 2)
    {a f : G} (haF : a ∈ F) (haT : a ∈ T) (hfF : f ∈ F) : f * a = a * f := by
  have hp : p.Prime := Fact.out
  have hcard := typeII_hF_card_inf_le hTcard hTexp hTnab hxZ hx1 hxp hZT hTZ hxF hrk
  obtain ⟨t, htT, z, hzZ, hfeq⟩ := typeII_hF_exists_mul_of_sup_eq hZT rfl f (hFP hfF)
  by_contra hne
  set c : G := a * f * a⁻¹ * f⁻¹ with hc
  have hcF : c ∈ F := F.mul_mem (F.mul_mem (F.mul_mem haF hfF) (F.inv_mem haF)) (F.inv_mem hfF)
  have hza : z * a = a * z := hZT z hzZ a haT
  have hza' : z * a⁻¹ = a⁻¹ * z := (show Commute z a from hza).inv_right
  have hc_eq : c = a * t * a⁻¹ * t⁻¹ := by
    rw [hc, hfeq]
    calc a * (t * z) * a⁻¹ * (t * z)⁻¹ = a * t * (z * a⁻¹) * z⁻¹ * t⁻¹ := by group
      _ = a * t * (a⁻¹ * z) * z⁻¹ * t⁻¹ := by rw [hza']
      _ = a * t * a⁻¹ * t⁻¹ := by group
  have hcT : c ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
    hc_eq ▸ typeII_hF_commutator_mem hTcard hTnab haT htT
  have hc1 : c ≠ 1 := by
    intro h
    apply hne
    rw [hc, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hcp : c ^ p = 1 := hTexp c hcT.1
  have hcord : orderOf c = p := orderOf_eq_prime hcp hc1
  have hle : Subgroup.zpowers c ≤ F ⊓ T := Subgroup.zpowers_le.mpr ⟨hcF, hcT.1⟩
  have heq : Subgroup.zpowers c = F ⊓ T :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hcord]; exact hcard)
  have haz : a ∈ Subgroup.zpowers c := by
    rw [heq]
    exact ⟨haF, haT⟩
  have hzc : Subgroup.zpowers c ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
    Subgroup.zpowers_le.mpr hcT
  have hat : t * a = a * t := Subgroup.mem_centralizer_iff.mp (hzc haz).2 t htT
  apply hc1
  rw [hc_eq, ← hat]
  group

theorem typeII_hF_comm_of_le {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T Z F : Subgroup G} {x : G}
    (hTcard : Nat.card T = p ^ 3) (hTexp : ∀ t ∈ T, t ^ p = 1) (hTnab : ¬ IsMulCommutative T)
    (hZcyc : IsCyclic Z) (hxZ : x ∈ Z) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hZT : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hTZ : T ⊓ Z = ⊥)
    (hFP : F ≤ T ⊔ Z) (hxF : x ∈ F) (hrk : CFSG.Open.pRank p F ≤ 2) :
    IsMulCommutative F := by
  let Φ : ↥T × ↥Z →* G := MonoidHom.noncommCoprod T.subtype Z.subtype
    (fun t z => (hZT z z.2 t t.2).symm)
  have hΦinj : Function.Injective Φ := by
    refine (MonoidHom.noncommCoprod_injective _ _ _).2
      ⟨T.subtype_injective, Z.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.mpr hTZ
  have hΦrange : Φ.range = T ⊔ Z := by
    have h := MonoidHom.noncommCoprod_range T.subtype Z.subtype
      (fun t z => (hZT z z.2 t t.2).symm)
    rw [Subgroup.range_subtype, Subgroup.range_subtype] at h
    exact h
  let e : ↥T × ↥Z ≃* Φ.range := MonoidHom.ofInjective hΦinj
  have hFR : F ≤ Φ.range := hΦrange ▸ hFP
  let φ : ↥F →* ↥Z :=
    (MonoidHom.snd ↥T ↥Z).comp (e.symm.toMonoidHom.comp (Subgroup.inclusion hFR))
  haveI : IsCyclic ↥Z := hZcyc
  refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center φ ?_
  intro a ha
  have haT : (a : G) ∈ T := by
    have hφa : φ a = 1 := ha
    set w : ↥T × ↥Z := e.symm (Subgroup.inclusion hFR a) with hw
    have hz : w.2 = 1 := hφa
    have hew : (w.1 : G) * (w.2 : G) = a := by
      have h := congrArg (fun y : Φ.range => (y : G))
        (e.apply_symm_apply (Subgroup.inclusion hFR a))
      exact h
    rw [hz, Subgroup.coe_one, mul_one] at hew
    rw [← hew]
    exact w.1.2
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (typeII_hF_commute_of_mem_inf hTcard hTexp hTnab hxZ hx1 hxp hZT hTZ hFP hxF hrk
    a.2 haT g.2)


theorem typeII_hF_exists_conj_le {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (P : Sylow p G) {F : Subgroup G} (hF : IsPGroup p F) :
    ∃ c : G, F.map (MulAut.conj c).toMonoidHom ≤ (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hF.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hmem : MulAut.conj g • y ∈ ((g • Q : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (Q : Subgroup G) (hQ hy)
  rw [hg] at hmem
  simpa [MulAut.smul_def] using hmem

theorem typeII_hF_pRank_map_conj_le {p : ℕ} (hp : 1 < p) {G : Type*} [Group G] [Finite G]
    (F : Subgroup G) (c : G) :
    CFSG.Open.pRank p (F.map (MulAut.conj c).toMonoidHom) ≤ CFSG.Open.pRank p F := by
  have h := CFSG.SectionRank.pRank_le_map hp (MulAut.conj c⁻¹).toMonoidHom
    (MulAut.conj c⁻¹).injective (F.map (MulAut.conj c).toMonoidHom)
  have hmap : (F.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = F := by
    ext y
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using ha
    · intro hy
      exact ⟨c * y * c⁻¹, ⟨y, hy, rfl⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
  rwa [hmap] at h

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G} {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
  {Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop}

theorem typeII_hF (hS : Setting G) (hX : ExtraFacts Typ p Shape) (hc : PointConfig Typ G p P M x J)
    (hfus : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G))
    {U : Subgroup G} (hU : IIPlane p P x J U) :
    ∀ F : Subgroup G, IsPGroup p F → U ≤ F → F ≤ M → CFSG.Open.pRank p F ≤ 2 →
      IsMulCommutative F ∧ ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ F →
        (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x := by
  intro F hFp hUF _ hrk
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hTcard, hTexp, hTnab, -⟩ := typeII_T_structure hX hc
  obtain ⟨Z, hZcyc, hxZ, -, hZT, hTZ, hsup⟩ := typeII_S_decomp hX hc
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ p = 1 := hc.generic.2.1.2.2.1
  have hSP : u3S P x = (P : Subgroup G) := inf_eq_left.mpr hfus.1
  rw [hSP] at hsup
  have hxF : x ∈ F := hUF hU.mem
  obtain ⟨c, hcP⟩ := typeII_hF_exists_conj_le P hFp
  set F₁ : Subgroup G := F.map (MulAut.conj c).toMonoidHom with hF₁
  have hxc : (Subgroup.zpowers x).map (MulAut.conj c).toMonoidHom = Subgroup.zpowers x := by
    apply hfus.2 c
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact hcP ⟨x, hxF, rfl⟩
  have hxF₁ : x ∈ F₁ := by
    have h1 : (Subgroup.zpowers x).map (MulAut.conj c).toMonoidHom ≤ F₁ :=
      Subgroup.map_mono (Subgroup.zpowers_le.mpr hxF)
    rw [hxc] at h1
    exact h1 (Subgroup.mem_zpowers x)
  have hrk₁ : CFSG.Open.pRank p F₁ ≤ 2 :=
    (typeII_hF_pRank_map_conj_le hp.one_lt F c).trans hrk
  have hF₁comm : IsMulCommutative F₁ :=
    typeII_hF_comm_of_le hTcard hTexp hTnab hZcyc hxZ hx1 hxp hZT hTZ (hcP.trans hsup.ge) hxF₁ hrk₁
  refine ⟨?_, ?_⟩
  · refine IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_
    have h := hF₁comm.is_comm.comm ⟨c * a * c⁻¹, ⟨a, ha, rfl⟩⟩ ⟨c * b * c⁻¹, ⟨b, hb, rfl⟩⟩
    have h' := congrArg Subtype.val h
    have h2 : c * (a * b) * c⁻¹ = c * (b * a) * c⁻¹ := by
      calc c * (a * b) * c⁻¹ = c * a * c⁻¹ * (c * b * c⁻¹) := by group
        _ = c * b * c⁻¹ * (c * a * c⁻¹) := h'
        _ = c * (b * a) * c⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  · intro g hg
    set N : Subgroup G := (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom with hN
    have hNP : N.map (MulAut.conj c).toMonoidHom ≤ (P : Subgroup G) :=
      (Subgroup.map_mono hg).trans hcP
    have hmapmap : N.map (MulAut.conj c).toMonoidHom =
        (Subgroup.zpowers x).map (MulAut.conj (c * g)).toMonoidHom := by
      rw [hN, Subgroup.map_map]
      congr 1
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    have hcg : (Subgroup.zpowers x).map (MulAut.conj (c * g)).toMonoidHom =
        Subgroup.zpowers x := hfus.2 (c * g) (hmapmap ▸ hNP)
    apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [hmapmap, hcg, hxc]

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
