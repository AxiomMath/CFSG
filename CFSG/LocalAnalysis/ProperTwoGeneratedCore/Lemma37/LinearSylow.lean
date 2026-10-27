module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearTorus

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

theorem central_involution_mul_mul_self {K : Type*} [Group K] {c : K} (hc : ∀ g : K, Commute g c)
    (hcc : c * c = 1) (y : K) : c * y * (c * y) = y * y := by
  rw [mul_assoc, ← mul_assoc y, (hc y).eq, mul_assoc, ← mul_assoc c, hcc, one_mul]

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
  (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H) {J : Subgroup (EscapingQuotient z)}
  (hJ : CFSG.IsComponent J) (hzJ : escapingBar z ∉ J) {D : Subgroup (EscapingQuotient z)} {q : ℕ}
  (hlin : LinearSylowData J ((sylowBar hz).range ⊓ J) D q)
include hset hz hesc hJ hzJ hlin

theorem caseOne_outer_sq {u : EscapingQuotient z} (huS : u ∈ (sylowBar hz).range)
    (hu : ¬ (u ∈ J ∨ escapingBar z * u ∈ J)) (hu2 : u * u ∈ J ∨ escapingBar z * (u * u) ∈ J) :
    u * u ∉ J ∧ ∃ x ∈ (sylowBar hz).range ⊓ J, x * u * (x * u) = escapingBar z := by
  have hq := caseOne_quotientData hset hz hesc
  have hJn := caseOne_component_normal hset hz hesc hJ hzJ
  have hzz := escapingBar_mul_self hz.2.1
  set R := (sylowBar hz).range ⊓ J with hR
  have huJ : u ∈ Subgroup.normalizer (J : Set (EscapingQuotient z)) :=
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hJn.conj_mem y hy u, fun hy => by
      simpa [mul_assoc] using hJn.conj_mem _ hy u⁻¹⟩
  have huR : u ∈ Subgroup.normalizer (R : Set (EscapingQuotient z)) := by
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · exact ⟨(sylowBar hz).range.mul_mem ((sylowBar hz).range.mul_mem huS hy.1)
        ((sylowBar hz).range.inv_mem huS), hJn.conj_mem y hy.2 u⟩
    · have h1 : y = u⁻¹ * (u * y * u⁻¹) * u := by group
      refine ⟨?_, ?_⟩
      · rw [h1]
        exact (sylowBar hz).range.mul_mem ((sylowBar hz).range.mul_mem
          ((sylowBar hz).range.inv_mem huS) hy.1) huS
      · rw [h1]
        simpa using hJn.conj_mem _ hy.2 u⁻¹
  have hA : ∀ c, c ∈ J ∨ escapingBar z * c ∈ J → c ∈ (sylowBar hz).range →
      ∀ x ∈ R, c * x = x * c := by
    intro c hc hcS x hx
    rcases hc with hc | hc
    · exact hlin.comm c ⟨hcS, hc⟩ x hx
    · have hcR : escapingBar z * c ∈ R :=
        ⟨(sylowBar hz).range.mul_mem (by rw [← sylowBar_self hz]; exact ⟨_, rfl⟩) hcS, hc⟩
      have h := hlin.comm _ hcR x hx
      have hzx := (hq.commute_bar x).eq
      calc c * x = escapingBar z * (escapingBar z * c * x) := by
            rw [← mul_assoc, ← mul_assoc, hzz, one_mul]
        _ = escapingBar z * (x * (escapingBar z * c)) := by rw [h]
        _ = x * c := by rw [← mul_assoc, ← mul_assoc, ← hzx, mul_assoc x, hzz, mul_one]
  have huuS : u * u ∈ (sylowBar hz).range := (sylowBar hz).range.mul_mem huS huS
  have hu2R := hA _ hu2 huuS
  have hunc : ∃ x ∈ R, u * x ≠ x * u := by
    by_contra h
    push Not at h
    exact hu (caseOne_mem_or_of_centralizes hset hz hesc hJ hzJ hlin h)
  have key : ∀ c₀ ∈ R, u * c₀ = c₀ * u → ∃ x ∈ R, x * u * (x * u) = c₀ * (u * u) := by
    intro c₀ hc₀ hc₀u
    obtain ⟨x, hx, hxc⟩ := hlin.exists_mul_conj_eq huJ huR (fun x hx => hu2R x hx) hunc hc₀ hc₀u
    exact ⟨x, hx, by rw [← hxc]; group⟩
  have hnot : u * u ∉ J := by
    intro huuJ
    obtain ⟨x, hx, hxu⟩ := key (u * u) ⟨huuS, huuJ⟩ (by group)
    rw [hlin.sq _ ⟨huuS, huuJ⟩] at hxu
    have hxu1 : x * u ≠ 1 := by
      intro h
      apply hu
      left
      have : u = x⁻¹ := by rw [← mul_eq_one_iff_eq_inv']; exact h
      rw [this]
      exact J.inv_mem hx.2
    have hxu2 : orderOf (x * u) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxu) hxu1
    apply hu
    rcases hq.involution_mem_component_or hJ hzJ hxu2 with h | h
    · left
      have := J.mul_mem (J.inv_mem hx.2) h
      rwa [inv_mul_cancel_left] at this
    · right
      have h' : escapingBar z * u = x⁻¹ * (escapingBar z * (x * u)) := by
        rw [← mul_assoc x⁻¹, (hq.commute_bar x⁻¹).eq, mul_assoc, inv_mul_cancel_left]
      rw [h']
      exact J.mul_mem (J.inv_mem hx.2) h
  refine ⟨hnot, ?_⟩
  have hc₀J : escapingBar z * (u * u) ∈ J := hu2.resolve_left hnot
  set c₀ := escapingBar z * (u * u) with hc₀
  have hc₀R : c₀ ∈ R :=
    ⟨(sylowBar hz).range.mul_mem (by rw [← sylowBar_self hz]; exact ⟨_, rfl⟩) huuS, hc₀J⟩
  have hc₀u : u * c₀ = c₀ * u := by
    rw [hc₀, ← mul_assoc, (hq.commute_bar u).eq]
    group
  obtain ⟨x, hx, hxu⟩ := key _ hc₀R hc₀u
  refine ⟨x, hx, ?_⟩
  have huu : u * u = escapingBar z * c₀ := by rw [hc₀, ← mul_assoc, hzz, one_mul]
  rw [hxu, huu, ← mul_assoc, (hq.commute_bar c₀).eq, mul_assoc, hlin.sq c₀ hc₀R, mul_one]

theorem caseOne_sylowBar_mem_or {s : EscapingQuotient z} (hs : s ∈ (sylowBar hz).range) :
    s ∈ J ∨ escapingBar z * s ∈ J := by
  have hq := caseOne_quotientData hset hz hesc
  have hzz := escapingBar_mul_self hz.2.1
  by_contra hsA
  obtain ⟨t, rfl⟩ := hs
  obtain ⟨m, hm⟩ := S.isPGroup' t
  have hP : ∃ k, sylowBar hz t ^ 2 ^ k ∈ J ∨ escapingBar z * sylowBar hz t ^ 2 ^ k ∈ J :=
    ⟨m, Or.inl (by rw [← map_pow, hm, map_one]; exact J.one_mem)⟩
  classical
  set k₀ := Nat.find hP with hk₀
  have hk₀0 : k₀ ≠ 0 := by
    intro h
    have := Nat.find_spec hP
    rw [← hk₀, h, pow_zero, pow_one] at this
    exact hsA this
  set u := sylowBar hz t ^ 2 ^ (k₀ - 1)
  have huS : u ∈ (sylowBar hz).range := (sylowBar hz).range.pow_mem ⟨t, rfl⟩ _
  have hu : ¬ (u ∈ J ∨ escapingBar z * u ∈ J) := Nat.find_min hP (by omega)
  have huu : u * u = sylowBar hz t ^ 2 ^ k₀ := by
    rw [← pow_two, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk₀0)]
  have hu2 : u * u ∈ J ∨ escapingBar z * (u * u) ∈ J := by
    rw [huu]
    exact Nat.find_spec hP
  obtain ⟨-, x, hx, hxu⟩ := caseOne_outer_sq hset hz hesc hJ hzJ hlin huS hu hu2
  obtain ⟨w₀, hw₀⟩ : x * u ∈ (sylowBar hz).range := (sylowBar hz).range.mul_mem hx.1 huS
  have hw₀z : (w₀ : G) * w₀ = z := by
    have h : sylowBar hz (w₀ * w₀) = sylowBar hz ⟨z, hz.1⟩ := by
      rw [map_mul, hw₀, hxu, sylowBar_self]
    exact congrArg Subtype.val (sylowBar_injective hz h)
  obtain ⟨r, hr, -, hrJ, -⟩ := coreSetting_component_fused_class hset hz hesc hJ hzJ
  obtain ⟨n, hn, hnr⟩ := caseOne_exists_normalizer_conj_eq hset hz hesc hJ hzJ hlin hr
  have hw'S : n⁻¹ * w₀ * n ∈ (S : Subgroup G) := (Subgroup.mem_normalizer_iff''.mp hn _).mp w₀.2
  set s' := sylowBar hz ⟨_, hw'S⟩
  have hs's' : s' * s' = escapingMk z r := by
    have h : (⟨_, hw'S⟩ : (S : Subgroup G)) * ⟨_, hw'S⟩ = ⟨r, hr.1⟩ := by
      apply Subtype.ext
      change n⁻¹ * w₀ * n * (n⁻¹ * w₀ * n) = r
      rw [← hnr, ← hw₀z]
      group
    rw [← map_mul, h]
    rfl
  have hr1 : escapingMk z r ≠ 1 := by
    intro h
    have h2 : sylowBar hz ⟨r, hr.1⟩ = sylowBar hz 1 := by rw [map_one]; exact h
    have h3 : (r : G) = 1 := congrArg Subtype.val (sylowBar_injective hz h2)
    have h4 := hr.2.1
    rw [h3, orderOf_one] at h4
    exact absurd h4 (by decide)
  have hs'S : s' ∈ (sylowBar hz).range := ⟨_, rfl⟩
  have hs'A : ¬ (s' ∈ J ∨ escapingBar z * s' ∈ J) := by
    rintro (h | h)
    · exact hr1 (by rw [← hs's']; exact hlin.sq _ ⟨hs'S, h⟩)
    · apply hr1
      rw [← hs's', ← central_involution_mul_mul_self hq.commute_bar hzz s']
      exact hlin.sq _ ⟨(sylowBar hz).range.mul_mem
        (by rw [← sylowBar_self hz]; exact ⟨_, rfl⟩) hs'S, h⟩
  have hs'2 : s' * s' ∈ J ∨ escapingBar z * (s' * s') ∈ J := Or.inl (hs's' ▸ hrJ)
  exact (caseOne_outer_sq hset hz hesc hJ hzJ hlin hs'S hs'A hs'2).1 (hs's' ▸ hrJ)

end CFSG.ProperTwoGeneratedCore.Lemma37
