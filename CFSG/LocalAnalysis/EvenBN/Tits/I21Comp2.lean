module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Comp
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.Comp2

open Subgroup CFSG.Open

section Elementary

variable {G : Type*} [Group G]

theorem eq_one_of_inv_eq_self {x : G} (h5 : x ^ 5 = 1) (h : x⁻¹ = x) : x = 1 := by
  have h2 : x ^ 2 = 1 := by
    calc x ^ 2 = x * x⁻¹ := by rw [h, sq]
      _ = 1 := mul_inv_cancel x
  have := (pow_gcd_eq_one (a := x) (m := 2) (n := 5)).2 ⟨h2, h5⟩
  simpa using this

theorem eq_one_of_commute_conj {w x : G} (hw : w ^ 2 = 1) (hwx : w * x * w⁻¹ = x⁻¹)
    (hx5 : x ^ 5 = 1) (hc : w * (x * w * x⁻¹) = x * w * x⁻¹ * w) : x = 1 := by
  have hwinv : w⁻¹ = w := by
    rw [inv_eq_iff_mul_eq_one, ← sq]
    exact hw
  rw [hwinv] at hwx
  have h1 : w * (x * w * x⁻¹) = x⁻¹ * x⁻¹ := by
    calc w * (x * w * x⁻¹) = (w * x * w) * x⁻¹ := by group
      _ = x⁻¹ * x⁻¹ := by rw [hwx]
  have h3 : w * x⁻¹ * w = x := by
    have h4 : (w * x * w)⁻¹ = x := by rw [hwx, inv_inv]
    calc w * x⁻¹ * w = (w * x * w)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, hwinv]
          exact mul_assoc _ _ _
      _ = x := h4
  have h2 : x * w * x⁻¹ * w = x * x := by
    calc x * w * x⁻¹ * w = x * (w * x⁻¹ * w) := by group
      _ = x * x := by rw [h3]
  have h4 : x ^ 4 = 1 := by
    have e : x⁻¹ * x⁻¹ = x * x := h1.symm.trans (hc.trans h2)
    calc x ^ 4 = (x * x) * (x * x) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
      _ = (x * x) * (x⁻¹ * x⁻¹) := by rw [e]
      _ = 1 := by group
  have := (pow_gcd_eq_one (a := x) (m := 4) (n := 5)).2 ⟨h4, hx5⟩
  simpa using this

theorem mul_comm_of_commutator_eq_bot {K K' : Subgroup G} (hc : ⁅K, K'⁆ = ⊥) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K') : a * b = b * a :=
  ((mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc ha)) b hb).symm

end Elementary

section CaseA

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem x_mem_and_sq_mem (h : Sec622Bar G t u x) (hx : x ≠ 1)
    (hN : ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧ t ∉ N)
    (hfus : ∀ j : ℕ, ∃ g : G, g * t * g⁻¹ = t * (x ^ j * u ^ 2)) {K : Subgroup G}
    (hK : CFSG.IsComponent K) (htK : K.map (MulAut.conj t).toMonoidHom = K) :
    x ∈ K ∧ u ^ 2 ∈ K := by
  obtain ⟨j, hj⟩ := sec622_component_contains_zj h hN hfus hK htK
  obtain ⟨hw2, -, hwx, -, -⟩ := sec622_zj_facts h hx j 0
  have hK' : CFSG.IsComponent (K.map (MulAut.conj x).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hK
  have hmem : x * (x ^ j * u ^ 2) * x⁻¹ ∈ K.map (MulAut.conj x).toMonoidHom :=
    ⟨x ^ j * u ^ 2, hj, by simp [MulAut.conj_apply]⟩
  have hKx : K.map (MulAut.conj x).toMonoidHom = K := by
    rcases CFSG.LocalCores.distinct_components_commute hK hK' with heq | hcomm
    · exact heq.symm
    · exact absurd (eq_one_of_commute_conj hw2 hwx h.x_five
        (mul_comm_of_commutator_eq_bot hcomm hj hmem)) hx
  have hmem' : x * (x ^ j * u ^ 2) * x⁻¹ ∈ K := hKx ▸ hmem
  have hx2 : x ^ 2 ∈ K := by
    have e : x * (x ^ j * u ^ 2) * x⁻¹ * (x ^ j * u ^ 2)⁻¹ = x ^ 2 := by
      calc x * (x ^ j * u ^ 2) * x⁻¹ * (x ^ j * u ^ 2)⁻¹
          = x * ((x ^ j * u ^ 2) * x * (x ^ j * u ^ 2)⁻¹)⁻¹ := by group
        _ = x * x := by rw [hwx, inv_inv]
        _ = x ^ 2 := (sq x).symm
    rw [← e]
    exact K.mul_mem hmem' (K.inv_mem hj)
  have hxK : x ∈ K := by
    have h6 : x = (x ^ 2) ^ 3 := by
      rw [← pow_mul]
      calc x = x ^ 5 * x := by rw [h.x_five, one_mul]
        _ = x ^ 6 := by rw [← pow_succ]
    rw [h6]
    exact pow_mem hx2 3
  refine ⟨hxK, ?_⟩
  have : u ^ 2 = (x ^ j)⁻¹ * (x ^ j * u ^ 2) := by group
  rw [this]
  exact K.mul_mem (K.inv_mem (pow_mem hxK j)) hj

end CaseA

section Layer

variable {G : Type} [Group G] [Finite G]

theorem layer_normal : (CFSG.layer G).Normal := by
  haveI := CFSG.LocalCores.layer_characteristic (G := G)
  infer_instance

theorem layer_center_normal : (centralizer (CFSG.layer G : Set G) ⊓ CFSG.layer G).Normal := by
  haveI := layer_normal (G := G)
  infer_instance

theorem isPGroup_two_of_normal_comm (hO : standardComponentOddCore G = ⊥) {A : Subgroup G}
    (hA : A.Normal) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : IsPGroup 2 A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsMulCommutative A :=
    isMulCommutative_iff.mpr fun a b => Subtype.ext (hcomm a a.2 b b.2)
  exact CFSG.isPGroup_of_nilpotent_normal A hA inferInstance (I21.Comp.pPrimeCore_eq_bot hO)

theorem layer_center_isPGroup (hO : standardComponentOddCore G = ⊥) :
    IsPGroup 2 (centralizer (CFSG.layer G : Set G) ⊓ CFSG.layer G : Subgroup G) :=
  isPGroup_two_of_normal_comm hO layer_center_normal fun a ha b hb =>
    (mem_centralizer_iff.mp ha.1 b hb.2).symm

end Layer

section PCoreStep

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem comm_of_mem_pCore {q e : G} (hq : q ∈ CFSG.pCore 2 G) (he : e ∈ CFSG.layer G) :
    e * q = q * e := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : q ∈ centralizer (CFSG.layer G : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (CFSG.LocalCores.fitting_layer_commute (G := G))
      (CFSG.pCore_le_fitting G 2 hq)
  exact mem_centralizer_iff.mp h1 e he

theorem exists_fixed_involution_mem (ht : t * t = 1) {Q : Subgroup G}
    (hQ : ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) (heven : 2 ∣ Nat.card Q) :
    ∃ i : G, i ∈ Q ∧ i ≠ 1 ∧ i ^ 2 = 1 ∧ t * i * t⁻¹ = i := by
  let α : Q →* Q := MonoidHom.mk' (fun q => ⟨t * (q : G) * t⁻¹, hQ q q.2⟩) (by
    intro a b
    apply Subtype.ext
    change t * ((a : G) * b) * t⁻¹ = (t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹)
    group)
  have hα : ∀ q, α (α q) = q := by
    intro q
    apply Subtype.ext
    change t * (t * (q : G) * t⁻¹) * t⁻¹ = q
    rw [inv_eq_of_mul_eq_one_right ht]
    calc t * (t * (q : G) * t) * t = (t * t) * q * (t * t) := by simp only [mul_assoc]
      _ = q := by rw [ht, one_mul, mul_one]
  obtain ⟨i, hi1, hi2, hiα⟩ := Comp.exists_fixed_involution α hα heven
  exact ⟨i, i.2, fun h1 => hi1 (Subtype.ext h1), congrArg Subtype.val hi2,
    congrArg Subtype.val hiα⟩

theorem false_of_component_centralizes_conj (h : Sec622Bar G t u x) {L : Subgroup G}
    (hL : CFSG.IsComponent L) {g s : G} (hgs : g * t * g⁻¹ = s) (hLs : ∀ l ∈ L, l * s = s * l) :
    False := by
  haveI : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  haveI : Group.IsPerfect L := hL.1.1
  haveI := sec622_centralizer_solvable h
  have ht : t = g⁻¹ * s * g := by
    rw [← hgs]
    group
  have hmem : ∀ l : L, g⁻¹ * (l : G) * g ∈ centralizer ({t} : Set G) := by
    intro l
    rw [mem_centralizer_singleton_iff, ht]
    calc g⁻¹ * (l : G) * g * (g⁻¹ * s * g) = g⁻¹ * ((l : G) * s) * g := by group
      _ = g⁻¹ * (s * (l : G)) * g := by rw [hLs l l.2]
      _ = g⁻¹ * s * g * (g⁻¹ * (l : G) * g) := by group
  let φ : L →* centralizer ({t} : Set G) :=
    MonoidHom.mk' (fun l => ⟨g⁻¹ * (l : G) * g, hmem l⟩) (by
      intro a b
      apply Subtype.ext
      change g⁻¹ * ((a : G) * b) * g = g⁻¹ * (a : G) * g * (g⁻¹ * (b : G) * g)
      group)
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    change g⁻¹ * (a : G) * g = g⁻¹ * (b : G) * g at this
    simpa using this
  exact Group.IsPerfect.not_isSolvable L (Group.isSolvable_of_isSolvable_injective hφ)

theorem sq_mem_of_zj_mem (h : Sec622Bar G t u x) {Q : Subgroup G} (hQ : Q.Normal) {j : ℕ}
    (hj : x ^ j * u ^ 2 ∈ Q) : u ^ 2 ∈ Q := by
  have hc := h.crel
  have hinv : (x ^ (2 * j))⁻¹ = x ^ (8 * j) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show 2 * j + 8 * j = 5 * (2 * j) by ring, pow_mul,
      h.x_five, one_pow]
  have h1 : u ^ 2 * x ^ (8 * j) = x ^ (8 * j * 2 ^ 2) * u ^ 2 := hc.pow_u_mul_x_pow 2 (8 * j)
  have key : x ^ (2 * j) * (x ^ j * u ^ 2) * (x ^ (2 * j))⁻¹ = u ^ 2 := by
    calc x ^ (2 * j) * (x ^ j * u ^ 2) * (x ^ (2 * j))⁻¹
        = x ^ (2 * j) * x ^ j * (u ^ 2 * x ^ (8 * j)) := by rw [hinv]; group
      _ = x ^ (2 * j) * x ^ j * (x ^ (8 * j * 2 ^ 2) * u ^ 2) := by rw [h1]
      _ = x ^ (5 * (7 * j)) * u ^ 2 := by
          rw [← mul_assoc, ← pow_add, ← pow_add]
          congr 2
          ring
      _ = u ^ 2 := by rw [pow_mul, h.x_five, one_pow, one_mul]
  rw [← key]
  exact hQ.conj_mem _ hj _

end PCoreStep

end CFSG.LocalAnalysis.EvenBN.Tits.I21.Comp2

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem sec622_case_A_unique_component (h : Sec622Bar G t u x) (hx : x ≠ 1)
    (hN : ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧ t ∉ N)
    (hfus : ∀ j : ℕ, ∃ g : G, g * t * g⁻¹ = t * (x ^ j * u ^ 2))
    (htinv : ∀ K : Subgroup G, CFSG.IsComponent K → K.map (MulAut.conj t).toMonoidHom = K)
    (hex : ∃ K : Subgroup G, CFSG.IsComponent K) :
    ∃ L : Subgroup G, CFSG.IsComponent L ∧ (∀ K : Subgroup G, CFSG.IsComponent K → K = L) ∧
      x ∈ L ∧ u ^ 2 ∈ L := by
  obtain ⟨L, hL⟩ := hex
  obtain ⟨hxL, hzL⟩ := I21.Comp2.x_mem_and_sq_mem h hx hN hfus hL (htinv L hL)
  refine ⟨L, hL, fun K hK => ?_, hxL, hzL⟩
  obtain ⟨-, hzK⟩ := I21.Comp2.x_mem_and_sq_mem h hx hN hfus hK (htinv K hK)
  rcases CFSG.LocalCores.distinct_components_commute hK hL with heq | hcomm
  · exact heq
  · exfalso
    have hc : u ^ 2 * x = x * u ^ 2 := I21.Comp2.mul_comm_of_commutator_eq_bot hcomm hzK hxL
    obtain ⟨-, -, hwx, -, -⟩ := sec622_zj_facts h hx 0 0
    rw [pow_zero, one_mul] at hwx
    have hinv : x⁻¹ = x := by
      rw [← hwx, hc]
      group
    exact hx (I21.Comp2.eq_one_of_inv_eq_self h.x_five hinv)

theorem sec622_case_B_two_components (h : Sec622Bar G t u x) (hx : x = 1)
    (hN : ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧ t ∉ N)
    (hfus : ∀ j : ℕ, ∃ g : G, g * t * g⁻¹ = t * (x ^ j * u ^ 2))
    (htinv : ∀ K : Subgroup G, CFSG.IsComponent K → K.map (MulAut.conj t).toMonoidHom = K)
    {K₁ K₂ : Subgroup G} (h1 : CFSG.IsComponent K₁) (h2 : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂) :
    u ^ 2 ∈ CFSG.layer G ∧ ∀ e ∈ CFSG.layer G, e * u ^ 2 = u ^ 2 * e := by
  have hz : ∀ K : Subgroup G, CFSG.IsComponent K → u ^ 2 ∈ K := by
    intro K hK
    obtain ⟨j, hj⟩ := sec622_component_contains_zj h hN hfus hK (htinv K hK)
    simpa [hx] using hj
  have hz1 := hz K₁ h1
  have hz2 := hz K₂ h2
  refine ⟨CFSG.LocalCores.component_le_layer h1 hz1, fun e he => ?_⟩
  have hle : CFSG.layer G ≤ centralizer ({u ^ 2} : Set G) := by
    rw [CFSG.layer.eq_sSup G]
    refine sSup_le fun K hK => ?_
    intro k hk
    rw [mem_centralizer_singleton_iff]
    by_cases hK1 : K = K₁
    · subst hK1
      exact I21.Comp2.mul_comm_of_commutator_eq_bot
        ((CFSG.LocalCores.distinct_components_commute h1 h2).resolve_left hne) hk hz2
    · exact I21.Comp2.mul_comm_of_commutator_eq_bot
        ((CFSG.LocalCores.distinct_components_commute hK h1).resolve_left hK1) hk hz1
  exact mem_centralizer_singleton_iff.mp (hle he)

theorem sec622_T_of_central_layer (h : Sec622Bar G t u x)
    (hz : u ^ 2 ∈ CFSG.layer G ∧ ∀ e ∈ CFSG.layer G, e * u ^ 2 = u ^ 2 * e) : Sec622T1 u :=
  ⟨centralizer (CFSG.layer G : Set G) ⊓ CFSG.layer G, I21.Comp2.layer_center_normal,
    I21.Comp2.layer_center_isPGroup h.oddCore,
    mem_inf.mpr ⟨mem_centralizer_iff.mpr fun e he => hz.2 e he, hz.1⟩⟩

theorem sec622_pCore_two (h : Sec622Bar G t u x)
    (hN : ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧ t ∉ N)
    (hfus : ∀ j : ℕ, ∃ g : G, g * t * g⁻¹ = t * (x ^ j * u ^ 2)) {L : Subgroup G}
    (hL : CFSG.IsComponent L) (hLE : CFSG.layer G = L) (hQ : CFSG.pCore 2 G ≠ ⊥) :
    Sec622T1 u := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : (CFSG.pCore 2 G).Normal := CFSG.pCore_normal
  have hQ2 : IsPGroup 2 (CFSG.pCore 2 G) := CFSG.pCore_isPGroup
  have heven : 2 ∣ Nat.card (CFSG.pCore 2 G) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hn, pow_zero])) hQ
    · rw [hn]
      exact dvd_pow_self 2 hpos.ne'
  obtain ⟨i, hiQ, hi1, hi2, hit⟩ := I21.Comp2.exists_fixed_involution_mem h.secTwo.t_mul_t
    (fun q hq => hQn.conj_mem q hq t) heven
  have hiC : i ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hit).symm
  have hLi : ∀ l ∈ L, l * i = i * l := fun l hl =>
    I21.Comp2.comm_of_mem_pCore hiQ (hLE ▸ hl)
  rcases sec622_involutions_centralizer h hiC hi1 hi2 with hi | ⟨j, hj⟩ | ⟨j, hj⟩
  · exact (I21.Comp2.false_of_component_centralizes_conj h hL (g := 1) (by simp)
      (hi ▸ hLi)).elim
  · exact ⟨CFSG.pCore 2 G, hQn, hQ2, I21.Comp2.sq_mem_of_zj_mem h hQn (j := j) (hj ▸ hiQ)⟩
  · obtain ⟨g, hg⟩ := hfus j
    exact (I21.Comp2.false_of_component_centralizes_conj h hL hg (hj ▸ hLi)).elim

theorem sec622_layer_simple (h : Sec622Bar G t u x) {L : Subgroup G} (hL : CFSG.IsComponent L)
    (hLE : CFSG.layer G = L) (hQ : CFSG.pCore 2 G = ⊥) :
    L.Normal ∧ IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ CFSG.generalizedFitting G = L ∧
      centralizer (L : Set G) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn : L.Normal := hLE ▸ I21.Comp2.layer_normal
  have hle : (centralizer (CFSG.layer G : Set G) ⊓ CFSG.layer G : Subgroup G) ≤
      CFSG.pCore 2 G :=
    le_sSup ⟨I21.Comp2.layer_center_normal, I21.Comp2.layer_center_isPGroup h.oddCore⟩
  have hZ : ∀ a : L, a ∈ center L → a = 1 := by
    intro a ha
    have hmem : (a : G) ∈ (centralizer (CFSG.layer G : Set G) ⊓ CFSG.layer G : Subgroup G) := by
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun e he => ?_, hLE ▸ a.2⟩
      have he' : e ∈ L := hLE ▸ he
      exact congrArg Subtype.val (mem_center_iff.mp ha ⟨e, he'⟩)
    have := hle hmem
    rw [hQ] at this
    exact Subtype.ext (mem_bot.mp this)
  have hcen : center L = ⊥ := (eq_bot_iff_forall _).mpr hZ
  have hinj : Function.Injective (QuotientGroup.mk' (center L)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hcen
  haveI : IsSimpleGroup (L ⧸ center L) := hL.1.2.1
  let e : L ≃* L ⧸ center L :=
    MulEquiv.ofBijective (QuotientGroup.mk' (center L)) ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have hna : ∃ a b : L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hL.1.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun hba => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hba])⟩
  have hF : CFSG.fittingSubgroup G = ⊥ := by
    rw [CFSG.Fitting_eq_pcore G 2 (I21.Comp.pPrimeCore_eq_bot h.oddCore), hQ]
  have hFS : CFSG.generalizedFitting G = L := by
    rw [CFSG.generalizedFitting.eq_sup G, hF, hLE, bot_sup_eq]
  refine ⟨hLn, e.isSimpleGroup, hna, hFS, ?_⟩
  rw [eq_bot_iff_forall]
  intro g hg
  have hg1 : g ∈ centralizer (CFSG.generalizedFitting G : Set G) := by
    rw [hFS]
    exact hg
  have hgL : g ∈ L := hFS ▸ CFSG.centralizer_generalizedFitting_le G hg1
  have hgc : (⟨g, hgL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (mem_centralizer_iff.mp hg k k.2)
  exact congrArg Subtype.val (hZ _ hgc)

theorem sec622_three_one (h : Sec622Bar G t u x)
    (hnc : ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 Q → ¬ centralizer (Q : Set G) ≤ Q)
    (hN : ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧ t ∉ N)
    (hfus : ∀ j : ℕ, ∃ g : G, g * t * g⁻¹ = t * (x ^ j * u ^ 2)) :
    Sec622T1 u ∨ ∃ L : Subgroup G, L.Normal ∧ IsSimpleGroup L ∧
      (∃ a b : L, a * b ≠ b * a) ∧ centralizer (L : Set G) = ⊥ ∧ u ^ 2 ∈ L ∧
      (x ≠ 1 → x ∈ L) ∧ (∀ g : G, g * t * g⁻¹ ∉ L) ∧
      ∀ j : ℕ, t * (x ^ j * u ^ 2) ∉ L := by
  have hex : ∃ K : Subgroup G, CFSG.IsComponent K := by
    by_contra hno
    exact sec622_layer_ne_bot h hnc
      (CFSG.LocalCores.layer_eq_bot_of_forall fun K hK => hno ⟨K, hK⟩)
  have htinv : ∀ K : Subgroup G, CFSG.IsComponent K →
      K.map (MulAut.conj t).toMonoidHom = K := fun K hK => sec622_component_t_invariant h hK
  have key : ∀ L : Subgroup G, CFSG.IsComponent L → (∀ K : Subgroup G, CFSG.IsComponent K → K = L) →
      u ^ 2 ∈ L → (x ≠ 1 → x ∈ L) → Sec622T1 u ∨ ∃ L : Subgroup G, L.Normal ∧ IsSimpleGroup L ∧
        (∃ a b : L, a * b ≠ b * a) ∧ centralizer (L : Set G) = ⊥ ∧ u ^ 2 ∈ L ∧
        (x ≠ 1 → x ∈ L) ∧ (∀ g : G, g * t * g⁻¹ ∉ L) ∧ ∀ j : ℕ, t * (x ^ j * u ^ 2) ∉ L := by
    intro L hL huniq hzL hxL
    have hLE : CFSG.layer G = L := by
      rw [CFSG.layer.eq_sSup G]
      exact le_antisymm (sSup_le fun K hK => (huniq K hK).le) (le_sSup hL)
    by_cases hQ : CFSG.pCore 2 G = ⊥
    · right
      obtain ⟨hn, hs, hna, -, hc⟩ := sec622_layer_simple h hL hLE hQ
      obtain ⟨N, hNn, hNi, htN⟩ := hN
      have hLN : L ≤ N := sec622_le_of_perfect hNn hNi hL.1.1
      have hconj : ∀ g : G, g * t * g⁻¹ ∉ L := by
        intro g hg
        have h1 := hNn.conj_mem _ (hLN hg) g⁻¹
        have e : g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t := by group
        rw [e] at h1
        exact htN h1
      refine ⟨L, hn, hs, hna, hc, hzL, hxL, hconj, fun j => ?_⟩
      obtain ⟨g, hg⟩ := hfus j
      rw [← hg]
      exact hconj g
    · exact Or.inl (sec622_pCore_two h hN hfus hL hLE hQ)
  by_cases hx : x = 1
  · by_cases htwo : ∃ K₁ K₂ : Subgroup G, CFSG.IsComponent K₁ ∧ CFSG.IsComponent K₂ ∧ K₁ ≠ K₂
    · obtain ⟨K₁, K₂, h1, h2, hne⟩ := htwo
      exact Or.inl (sec622_T_of_central_layer h
        (sec622_case_B_two_components h hx hN hfus htinv h1 h2 hne))
    · have hone : ∀ K₁ K₂ : Subgroup G, CFSG.IsComponent K₁ → CFSG.IsComponent K₂ → K₁ = K₂ :=
        fun K₁ K₂ h1 h2 => by
          by_contra hne
          exact htwo ⟨K₁, K₂, h1, h2, hne⟩
      obtain ⟨L, hL⟩ := hex
      obtain ⟨j, hj⟩ := sec622_component_contains_zj h hN hfus hL (htinv L hL)
      exact key L hL (fun K hK => hone K L hK hL) (by simpa [hx] using hj)
        fun hx1 => absurd hx hx1
  · obtain ⟨L, hL, huniq, hxL, hzL⟩ :=
      sec622_case_A_unique_component h hx hN hfus htinv hex
    exact key L hL huniq hzL fun _ => hxL

end CFSG.LocalAnalysis.EvenBN.Tits
