module

public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
public import CFSG.GH74.GLS.Bg.Statements
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecTransport
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer

namespace CentralQuotient

section Elements

variable {G B : Type*} [Group G] [Group B] {p : ℕ}

theorem pow_pow_eq_one_of_le {x : G} {i M : ℕ} (h : x ^ p ^ i = 1) (hle : i ≤ M) :
    x ^ p ^ M = 1 := by
  obtain ⟨k, hk⟩ := pow_dvd_pow p hle
  rw [hk, pow_mul, h, one_pow]

theorem eq_one_of_pow_eq_one_of_coprime {N : Subgroup G} {n : G} (hn : n ∈ N)
    (hcop : Nat.Coprime p (Nat.card N)) {m : ℕ} (h : n ^ p ^ m = 1) : n = 1 := by
  have h1 : orderOf n ∣ p ^ m := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
  have h3 : Nat.gcd (p ^ m) (Nat.card N) = 1 := Nat.Coprime.pow_left m hcop
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (h3 ▸ Nat.dvd_gcd h1 h2))

theorem eq_of_map_eq_of_pow_eq_one (φ : G →* B) (hcen : φ.ker ≤ center G)
    (hcop : Nat.Coprime p (Nat.card φ.ker)) {x g : G} {m : ℕ} (hx : x ^ p ^ m = 1)
    (hg : g ^ p ^ m = 1) (h : φ x = φ g) : x = g := by
  obtain ⟨n, hn, rfl⟩ : ∃ n ∈ φ.ker, g = x * n :=
    ⟨x⁻¹ * g, by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel], by group⟩
  have hcomm : Commute x n := (Subgroup.mem_center_iff.mp (hcen hn)) x
  rw [hcomm.mul_pow, hx, one_mul] at hg
  rw [eq_one_of_pow_eq_one_of_coprime hn hcop hg, mul_one]

theorem mem_of_map_mem_of_pow_eq_one (φ : G →* B) (hcen : φ.ker ≤ center G)
    (hcop : Nat.Coprime p (Nat.card φ.ker)) {S : Subgroup G} (hS : IsPGroup p S) {g : G} {m : ℕ}
    (hg : g ^ p ^ m = 1) (h : φ g ∈ S.map φ) : g ∈ S := by
  obtain ⟨s, hs, hsg⟩ := h
  obtain ⟨i, hi⟩ := hS ⟨s, hs⟩
  have hi' : s ^ p ^ i = 1 := by simpa using congrArg Subtype.val hi
  have := eq_of_map_eq_of_pow_eq_one φ hcen hcop (m := i + m)
    (pow_pow_eq_one_of_le hi' (Nat.le_add_right i m))
    (pow_pow_eq_one_of_le hg (Nat.le_add_left m i)) hsg
  exact this ▸ hs

theorem mem_normalizer_of_map_mem_normalizer (φ : G →* B) (hcen : φ.ker ≤ center G)
    (hcop : Nat.Coprime p (Nat.card φ.ker)) {S : Subgroup G} (hS : IsPGroup p S) {g : G}
    (hg : φ g ∈ normalizer ((S.map φ : Subgroup B) : Set B)) : g ∈ normalizer (S : Set G) := by
  have key : ∀ g : G, φ g ∈ normalizer ((S.map φ : Subgroup B) : Set B) →
      ∀ h ∈ S, g * h * g⁻¹ ∈ S := by
    intro g hg h hh
    obtain ⟨m, hm⟩ := hS ⟨h, hh⟩
    have hm' : h ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine mem_of_map_mem_of_pow_eq_one φ hcen hcop hS (m := m) ?_ ?_
    · rw [conj_pow, hm', mul_one, mul_inv_cancel]
    · have := (Subgroup.mem_normalizer_iff.mp hg (φ h)).mp (Subgroup.mem_map_of_mem φ hh)
      simpa using this
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
  have := key g⁻¹ (by rw [map_inv]; exact inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem commute_of_map_commute (φ : G →* B) (hcen : φ.ker ≤ center G)
    (hodd : Odd (Nat.card φ.ker)) {a j : G} (ha : a * a = 1)
    (h : φ j * φ a = φ a * φ j) : j * a = a * j := by
  have hm : (j * a * j⁻¹) * (j * a * j⁻¹) = 1 := by
    calc (j * a * j⁻¹) * (j * a * j⁻¹) = j * (a * a) * j⁻¹ := by group
      _ = 1 := by rw [ha]; group
  have hn : a * (j * a * j⁻¹) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, h]
    have : φ a * φ j * (φ j)⁻¹ = φ a := by group
    rw [this, ← map_mul, ha, map_one]
  have hc : a * (a * (j * a * j⁻¹)) = (a * (j * a * j⁻¹)) * a :=
    Subgroup.mem_center_iff.mp (hcen hn) a
  have hm2 : j * a * j⁻¹ = a * (j * a * j⁻¹) * a := by
    calc j * a * j⁻¹ = (a * a) * (j * a * j⁻¹) := by rw [ha, one_mul]
      _ = a * (a * (j * a * j⁻¹)) := by rw [mul_assoc]
      _ = _ := hc
  have hnn : (a * (j * a * j⁻¹)) * (a * (j * a * j⁻¹)) = 1 := by
    calc (a * (j * a * j⁻¹)) * (a * (j * a * j⁻¹))
        = (a * (j * a * j⁻¹) * a) * (j * a * j⁻¹) := by group
      _ = (j * a * j⁻¹) * (j * a * j⁻¹) := by rw [← hm2]
      _ = 1 := hm
  have hn1 : a * (j * a * j⁻¹) = 1 := by
    refine eq_one_of_pow_eq_one_of_coprime (p := 2) (m := 1) hn (Nat.coprime_two_left.mpr hodd) ?_
    rw [pow_one, pow_two, hnn]
  have hmeq : j * a * j⁻¹ = a := by
    have : a * (j * a * j⁻¹) = a * a := by rw [hn1, ha]
    exact mul_left_cancel this
  rw [mul_inv_eq_iff_eq_mul] at hmeq
  exact hmeq

end Elements

section Parabolic

variable {G H : Type*} [Group G] [Group H] {p : ℕ}

@[expose] def IsParabolicGrp (p : ℕ) {G : Type*} [Group G] (Q : Subgroup G) : Prop :=
  ∃ S : Sylow p G, normalizer ((S : Subgroup G) : Set G) ≤ Q

@[expose] def IsMaxParabolicGrp (p : ℕ) {G : Type*} [Group G] (Q : Subgroup G) : Prop :=
  IsParabolicGrp p Q ∧ Q ≠ ⊤ ∧ ∀ R : Subgroup G, IsParabolicGrp p R → R ≠ ⊤ → Q ≤ R → R = Q

theorem isParabolicGrp_map_iff [Finite G] [Fact p.Prime] (ψ : G →* H)
    (hψ : Function.Surjective ψ) (hcen : ψ.ker ≤ center G)
    (hcop : Nat.Coprime p (Nat.card ψ.ker)) {Q : Subgroup G} (hQ : ψ.ker ≤ Q) :
    IsParabolicGrp p (Q.map ψ) ↔ IsParabolicGrp p Q := by
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hψ p T
    refine ⟨S, fun g hg => ?_⟩
    have h1 : ψ g ∈ normalizer (((S.mapSurjective hψ : Sylow p H) : Subgroup H) : Set H) := by
      rw [Sylow.coe_mapSurjective]
      exact Subgroup.le_normalizer_map ψ (Subgroup.mem_map_of_mem ψ hg)
    have h2 : g ∈ (Q.map ψ).comap ψ := hT h1
    rwa [Subgroup.comap_map_eq, sup_eq_left.mpr hQ] at h2
  · rintro ⟨S, hS⟩
    refine ⟨S.mapSurjective hψ, fun t ht => ?_⟩
    obtain ⟨g, rfl⟩ := hψ t
    rw [Sylow.coe_mapSurjective] at ht
    exact Subgroup.mem_map_of_mem ψ
      (hS (mem_normalizer_of_map_mem_normalizer ψ hcen hcop S.isPGroup' ht))

theorem isMaxParabolicGrp_map_iff [Finite G] [Fact p.Prime] (ψ : G →* H)
    (hψ : Function.Surjective ψ) (hcen : ψ.ker ≤ center G)
    (hcop : Nat.Coprime p (Nat.card ψ.ker)) {Q : Subgroup G} (hQ : ψ.ker ≤ Q) :
    IsMaxParabolicGrp p (Q.map ψ) ↔ IsMaxParabolicGrp p Q := by
  have htop : ∀ R : Subgroup G, ψ.ker ≤ R → (R.map ψ = ⊤ ↔ R = ⊤) := by
    intro R hR
    constructor
    · intro h
      have := congrArg (Subgroup.comap ψ) h
      rwa [Subgroup.comap_map_eq, sup_eq_left.mpr hR, Subgroup.comap_top] at this
    · rintro rfl
      exact Subgroup.map_top_of_surjective ψ hψ
  constructor
  · rintro ⟨hpar, hne, hmax⟩
    refine ⟨(isParabolicGrp_map_iff ψ hψ hcen hcop hQ).mp hpar,
      fun h => hne ((htop Q hQ).mpr h), ?_⟩
    intro R hR hRne hle
    have hker : ψ.ker ≤ R := hQ.trans hle
    have h1 := hmax (R.map ψ) ((isParabolicGrp_map_iff ψ hψ hcen hcop hker).mpr hR)
      (fun h => hRne ((htop R hker).mp h)) (Subgroup.map_mono hle)
    have h2 := congrArg (Subgroup.comap ψ) h1
    rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, sup_eq_left.mpr hker,
      sup_eq_left.mpr hQ] at h2
  · rintro ⟨hpar, hne, hmax⟩
    refine ⟨(isParabolicGrp_map_iff ψ hψ hcen hcop hQ).mpr hpar,
      fun h => hne ((htop Q hQ).mp h), ?_⟩
    intro R' hR' hR'ne hle
    have hker : ψ.ker ≤ R'.comap ψ := fun x hx => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
      exact one_mem _
    have hRmap : (R'.comap ψ).map ψ = R' := Subgroup.map_comap_eq_self_of_surjective hψ R'
    have hRpar : IsParabolicGrp p (R'.comap ψ) :=
      (isParabolicGrp_map_iff ψ hψ hcen hcop hker).mp (by rw [hRmap]; exact hR')
    have hRne : R'.comap ψ ≠ ⊤ := fun h => hR'ne (by
      rw [← hRmap, h]
      exact Subgroup.map_top_of_surjective ψ hψ)
    have hQR : Q ≤ R'.comap ψ := fun x hx => hle (Subgroup.mem_map_of_mem ψ hx)
    have := hmax _ hRpar hRne hQR
    rw [← hRmap, this]

end Parabolic

section Ambient

variable {A : Type} [Group A] {p : ℕ}

theorem mem_normalizer_subgroupOf_iff {U K : Subgroup A} (hUK : U ≤ K) (g : ↥K) :
    g ∈ normalizer ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) ↔
      (g : A) ∈ normalizer (U : Set A) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hUK]
  rfl

theorem isParabolicP_iff_subgroupOf {K Q : Subgroup A} :
    IsParabolicP p K Q ↔ Q ≤ K ∧ IsParabolicGrp p (Q.subgroupOf K) := by
  constructor
  · rintro ⟨hQK, U, ⟨S, hSU⟩, hle⟩
    refine ⟨hQK, S, fun g hg => ?_⟩
    have hUK : U ≤ K := hSU ▸ Subgroup.map_subtype_le _
    have hSU' : U.subgroupOf K = (S : Subgroup ↥K) := by
      rw [← hSU, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    rw [← hSU', mem_normalizer_subgroupOf_iff hUK] at hg
    exact hle ⟨g.2, hg⟩
  · rintro ⟨hQK, S, hS⟩
    refine ⟨hQK, (S : Subgroup ↥K).map K.subtype, ⟨S, rfl⟩, ?_⟩
    rintro x ⟨hxK, hxN⟩
    have hUK : (S : Subgroup ↥K).map K.subtype ≤ K := Subgroup.map_subtype_le _
    have hSU' : ((S : Subgroup ↥K).map K.subtype).subgroupOf K = (S : Subgroup ↥K) := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    have := (mem_normalizer_subgroupOf_iff hUK ⟨x, hxK⟩).mpr hxN
    rw [hSU'] at this
    exact hS this

theorem isMaxParabolicP_iff_subgroupOf {K Q : Subgroup A} :
    IsMaxParabolicP p K Q ↔ Q ≤ K ∧ IsMaxParabolicGrp p (Q.subgroupOf K) := by
  constructor
  · rintro ⟨hP, hne, hmax⟩
    obtain ⟨hQK, hPg⟩ := isParabolicP_iff_subgroupOf.mp hP
    refine ⟨hQK, hPg, fun htop => hne (le_antisymm hQK (Subgroup.subgroupOf_eq_top.mp htop)), ?_⟩
    intro R hR hRtop hle
    have hR0K : R.map K.subtype ≤ K := Subgroup.map_subtype_le R
    have hR0 : (R.map K.subtype).subgroupOf K = R :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective R
    have hpar : IsParabolicP p K (R.map K.subtype) :=
      isParabolicP_iff_subgroupOf.mpr ⟨hR0K, by rwa [hR0]⟩
    have hne' : R.map K.subtype ≠ K := fun h => hRtop (by rw [← hR0, h, Subgroup.subgroupOf_self])
    have hle' : Q ≤ R.map K.subtype := fun x hx =>
      ⟨⟨x, hQK hx⟩, hle (show (⟨x, hQK hx⟩ : K) ∈ Q.subgroupOf K from hx), rfl⟩
    rw [← hR0, hmax _ hpar hne' hle']
  · rintro ⟨hQK, hPg, htop, hmax⟩
    refine ⟨isParabolicP_iff_subgroupOf.mpr ⟨hQK, hPg⟩,
      fun h => htop (by rw [h, Subgroup.subgroupOf_self]), ?_⟩
    intro R hR hRK hle
    obtain ⟨hRK', hRg⟩ := isParabolicP_iff_subgroupOf.mp hR
    have h1 : R.subgroupOf K = Q.subgroupOf K :=
      hmax _ hRg (fun h => hRK (le_antisymm hRK' (Subgroup.subgroupOf_eq_top.mp h)))
        (fun x hx => hle hx)
    have h2 := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr hRK', inf_eq_left.mpr hQK] at h2

theorem Op_subgroupOf (M : Subgroup A) : (Op p M).subgroupOf M = pCore p ↥M :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

theorem Op_le (M : Subgroup A) : Op p M ≤ M := Subgroup.map_subtype_le _

theorem isPGroup_Op (M : Subgroup A) : IsPGroup p ↥(Op p M) := (pCore_isPGroup).map M.subtype

theorem le_normalizer_Op (M : Subgroup A) : M ≤ normalizer ((Op p M : Subgroup A) : Set A) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Op_le M)).mp
    (by rw [Op_subgroupOf]; exact pCore_normal)

theorem le_Op {M R : Subgroup A} (hRM : R ≤ M) (hRp : IsPGroup p ↥R)
    (hRn : M ≤ normalizer (R : Set A)) : R ≤ Op p M := by
  have hnorm : (R.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRM).mpr hRn
  have hle : R.subgroupOf M ≤ pCore p ↥M :=
    le_sSup (show R.subgroupOf M ∈ {K : Subgroup ↥M | K.Normal ∧ IsPGroup p ↥K} from
      ⟨hnorm, hRp.comap_subtype⟩)
  calc R = (R.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hRM).symm
    _ ≤ Op p M := Subgroup.map_mono hle

theorem eq_Op_iff {M Q : Subgroup A} :
    Q = Op p M ↔ Q ≤ M ∧ IsPGroup p ↥Q ∧ M ≤ normalizer (Q : Set A) ∧
      ∀ R : Subgroup A, R ≤ M → IsPGroup p ↥R → M ≤ normalizer (R : Set A) → R ≤ Q := by
  constructor
  · rintro rfl
    exact ⟨Op_le M, isPGroup_Op M, le_normalizer_Op M, fun R hRM hRp hRn => le_Op hRM hRp hRn⟩
  · rintro ⟨hQM, hQp, hQn, hmax⟩
    exact le_antisymm (le_Op hQM hQp hQn) (hmax _ (Op_le M) (isPGroup_Op M) (le_normalizer_Op M))

end Ambient

section Center

theorem center_projectiveSpecialLinear_three {F : Type} [Field F] :
    center (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = ⊥ := by
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3)
    (by norm_num) (Or.inl le_rfl)
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := F) (n := 3) (by norm_num)
    (Or.inl le_rfl)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (center (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) with h | h
  · exact h
  · exact absurd (Subgroup.center_eq_top_iff.mp h) hperf.not_isMulCommutative

theorem center_eq_bot_of_lieModel_psl3 {K' : Type} [Group K'] {p n : ℕ}
    (h : LieModel K' .PSL 3 p n) : center K' = ⊥ := by
  rcases h with ⟨-, -, F, hF, hFin, -, ⟨e⟩⟩ | ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨h3, -⟩
  · let e' : K' ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
      e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
    have := center_projectiveSpecialLinear_three (F := F)
    rw [← Subgroup.map_center_eq e'] at this
    exact (Subgroup.map_eq_bot_iff_of_injective _ e'.injective).1 this
  all_goals exact absurd h3 (by norm_num)

end Center

end CentralQuotient

theorem central_quotient_parabolic {A B : Type} [Group A] [Finite A] [Group B] [Finite B] {p : ℕ}
    [Fact p.Prime] {J : Subgroup A} {K' : Subgroup B} (ψ : ↥J →* ↥K')
    (hψ : Function.Surjective ψ) (hcen : ψ.ker ≤ center ↥J) (hodd : Odd (Nat.card ψ.ker))
    (hcop : Nat.Coprime p (Nat.card ψ.ker)) {a : A} (ha2 : a * a = 1) (haJ : a ∈ J)
    {X : Subgroup A} (hXJ : X ≤ J) (hXp : IsPGroup p ↥X) {X' : Subgroup B}
    (hXX' : X' = ((X.subgroupOf J).map ψ).map K'.subtype) {P' : Subgroup B}
    (hP' : IsMaxParabolicP p K' P') (hXOp : X' = Op p P')
    (hPeq : P' = X' ⊔ K' ⊓ centralizer ({((ψ ⟨a, haJ⟩ : ↥K') : B)} : Set B)) :
    IsMaxParabolicP p J (X ⊔ J ⊓ centralizer ({a} : Set A)) ∧
      X = Op p (X ⊔ J ⊓ centralizer ({a} : Set A)) ∧
      Nat.card ↥X = Nat.card ↥X' ∧ (IsElementaryAbelian p ↥X' → IsElementaryAbelian p ↥X) := by
  classical
  set a' : ↥J := ⟨a, haJ⟩ with ha'
  have ha'2 : a' * a' = 1 := Subtype.ext ha2
  let φ : ↥J →* B := K'.subtype.comp ψ
  have hφker : φ.ker = ψ.ker := by
    ext x
    simp only [MonoidHom.mem_ker, φ, MonoidHom.comp_apply]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  have hcenφ : φ.ker ≤ center ↥J := hφker ▸ hcen
  have hcopφ : Nat.Coprime p (Nat.card φ.ker) := hφker ▸ hcop
  let Xg : Subgroup ↥J := X.subgroupOf J
  let Cg : Subgroup ↥J := centralizer ({a'} : Set ↥J)
  have hXg : IsPGroup p ↥Xg := hXp.comap_subtype
  have hX'φ : X' = Xg.map φ := by
    rw [hXX', Subgroup.map_map]
  have hCφ : K' ⊓ centralizer ({((ψ a' : ↥K') : B)} : Set B) = Cg.map φ := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_map, Cg, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hy, hyc⟩
      obtain ⟨j, hj⟩ := hψ ⟨y, hy⟩
      refine ⟨j, ?_, ?_⟩
      · refine CentralQuotient.commute_of_map_commute ψ hcen hodd ha'2 ?_
        apply Subtype.ext
        simp only [Subgroup.coe_mul, hj]
        exact hyc
      · simp [φ, hj]
    · rintro ⟨c, hc, rfl⟩
      refine ⟨(ψ c).2, ?_⟩
      have : ψ c * ψ a' = ψ a' * ψ c := by rw [← map_mul, ← map_mul, hc]
      exact congrArg Subtype.val this
  have hP'φ : P' = (Xg ⊔ Cg).map φ := by
    rw [hPeq, hX'φ, hCφ, Subgroup.map_sup]
  have hkerC : φ.ker ≤ Cg := fun n hn => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp (hcenφ hn) a').symm
  have hkerP : φ.ker ≤ Xg ⊔ Cg := hkerC.trans le_sup_right
  have hsat : ∀ j : ↥J, j ∈ Xg ⊔ Cg ↔ φ j ∈ P' := by
    intro j
    rw [hP'φ]
    constructor
    · exact fun h => Subgroup.mem_map_of_mem φ h
    · intro h
      have h' : j ∈ ((Xg ⊔ Cg).map φ).comap φ := h
      rwa [Subgroup.comap_map_eq, sup_eq_left.mpr hkerP] at h'
  have hCg : (J ⊓ centralizer ({a} : Set A)).subgroupOf J = Cg := by
    ext g
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Cg,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h.2, fun h => ⟨g.2, congrArg Subtype.val h⟩⟩
  have hPJ : X ⊔ J ⊓ centralizer ({a} : Set A) ≤ J := sup_le hXJ inf_le_left
  have hPg : (X ⊔ J ⊓ centralizer ({a} : Set A)).subgroupOf J = Xg ⊔ Cg := by
    rw [Subgroup.subgroupOf_sup hXJ inf_le_left, hCg]
  have hP'K : P'.subgroupOf K' = (Xg ⊔ Cg).map ψ := by
    rw [hP'φ, Subgroup.subgroupOf, show (Xg ⊔ Cg).map φ = ((Xg ⊔ Cg).map ψ).map K'.subtype from
      (Subgroup.map_map _ _ _).symm]
    exact Subgroup.comap_map_eq_self_of_injective K'.subtype_injective _
  have hmaxJ : IsMaxParabolicP p J (X ⊔ J ⊓ centralizer ({a} : Set A)) := by
    rw [CentralQuotient.isMaxParabolicP_iff_subgroupOf, hPg]
    refine ⟨hPJ, ?_⟩
    rw [← CentralQuotient.isMaxParabolicGrp_map_iff ψ hψ hcen hcop (hφker ▸ hkerP), ← hP'K]
    exact (CentralQuotient.isMaxParabolicP_iff_subgroupOf.mp hP').2
  obtain ⟨hX'P', hX'p, hnormX', hmaxX'⟩ := CentralQuotient.eq_Op_iff.mp hXOp
  have hXP : X = Op p (X ⊔ J ⊓ centralizer ({a} : Set A)) := by
    rw [CentralQuotient.eq_Op_iff]
    refine ⟨le_sup_left, hXp, ?_, ?_⟩
    · refine sup_le Subgroup.le_normalizer ?_
      rintro c ⟨hcJ, hcC⟩
      have hgC : (⟨c, hcJ⟩ : ↥J) ∈ Cg := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hcC)
      have hφg : φ ⟨c, hcJ⟩ ∈ P' := (hsat _).mp (Subgroup.mem_sup_right hgC)
      have hnX' : φ ⟨c, hcJ⟩ ∈ normalizer ((Xg.map φ : Subgroup B) : Set B) := by
        rw [← hX'φ]
        exact hnormX' hφg
      exact (CentralQuotient.mem_normalizer_subgroupOf_iff hXJ _).mp
        (CentralQuotient.mem_normalizer_of_map_mem_normalizer φ hcenφ hcopφ hXg hnX')
    · intro R hRP hRp hRn
      have hRJ : R ≤ J := hRP.trans hPJ
      have hRg : IsPGroup p ↥(R.subgroupOf J) := hRp.comap_subtype
      have hRgP : R.subgroupOf J ≤ Xg ⊔ Cg := by
        rw [← hPg]
        exact Subgroup.comap_mono hRP
      have hR'le : (R.subgroupOf J).map φ ≤ P' := by
        rw [hP'φ]
        exact Subgroup.map_mono hRgP
      have hR'n : P' ≤ normalizer (((R.subgroupOf J).map φ : Subgroup B) : Set B) := by
        intro y' hy'
        rw [hP'φ] at hy'
        obtain ⟨y, hy, rfl⟩ := hy'
        have hyP : (y : A) ∈ X ⊔ J ⊓ centralizer ({a} : Set A) := by
          rw [← Subgroup.mem_subgroupOf, hPg]
          exact hy
        exact Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ
          ((CentralQuotient.mem_normalizer_subgroupOf_iff hRJ y).mpr (hRn hyP)))
      have hR'X' := hmaxX' _ hR'le (hRg.map φ) hR'n
      intro r hr
      have hrg : (⟨r, hRJ hr⟩ : ↥J) ∈ R.subgroupOf J := hr
      obtain ⟨m, hm⟩ := hRp ⟨r, hr⟩
      have hm' : (⟨r, hRJ hr⟩ : ↥J) ^ p ^ m = 1 := by
        apply Subtype.ext
        simpa using congrArg Subtype.val hm
      exact CentralQuotient.mem_of_map_mem_of_pow_eq_one φ hcenφ hcopφ hXg hm'
        (hX'φ ▸ hR'X' (Subgroup.mem_map_of_mem φ hrg))
  let f : ↥X →* B := φ.comp (Subgroup.inclusion hXJ)
  have hfinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨i, hi⟩ := hXp x
    obtain ⟨j, hj⟩ := hXp y
    have hx' : Subgroup.inclusion hXJ x ^ p ^ (i + j) = 1 := by
      rw [← map_pow, CentralQuotient.pow_pow_eq_one_of_le hi (Nat.le_add_right i j), map_one]
    have hy' : Subgroup.inclusion hXJ y ^ p ^ (i + j) = 1 := by
      rw [← map_pow, CentralQuotient.pow_pow_eq_one_of_le hj (Nat.le_add_left j i), map_one]
    exact Subgroup.inclusion_injective hXJ
      (CentralQuotient.eq_of_map_eq_of_pow_eq_one φ hcenφ hcopφ hx' hy' hxy)
  have hrange : f.range = X' := by
    ext y
    rw [hX'φ, MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hXJ x, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  let e : ↥X ≃* ↥X' := (MonoidHom.ofInjective hfinj).trans (MulEquiv.subgroupCongr hrange)
  exact ⟨hmaxJ, hXP, Nat.card_congr e.toEquiv,
    fun h => Transport.isElementaryAbelian_of_mulEquiv e.symm h⟩

theorem lieModel_quotient_center {J K' : Type} [Group J] [Finite J] [Group K'] (ψ : J →* K')
    (hψ : Function.Surjective ψ) (hcen : ψ.ker ≤ center J) (hperf : Group.IsPerfect J)
    {p n : ℕ} (h : LieModel K' .PSL 3 p n) : LieModel (J ⧸ center J) .PSL 3 p n := by
  have _ := hperf
  have hZ : center K' = ⊥ := CentralQuotient.center_eq_bot_of_lieModel_psl3 h
  have hker : center J = ψ.ker := by
    refine le_antisymm (fun x hx => ?_) hcen
    have hx' : ψ x ∈ center K' := map_center_le_center hψ (Subgroup.mem_map_of_mem _ hx)
    rw [hZ, Subgroup.mem_bot] at hx'
    exact hx'
  let e : K' ≃* J ⧸ center J :=
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker.symm)
  exact Transport.lieModel_of_mulEquiv e h

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
