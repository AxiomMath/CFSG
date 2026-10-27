module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1112b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1111
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KEvenSLTwo
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Bridges1

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1112

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut innerAut)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1112b
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1111
  (isElemAbelian_sup card_zpowers_three)

section Generic

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_top_subgroupOf {Y P : Subgroup G} (hP : IsSylowIn 3 Y P) :
    IsSylowIn 3 (⊤ : Subgroup ↥Y) (P.subgroupOf Y) := by
  refine ⟨le_top, hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm, ?_⟩
  intro R' _ hR'3 hPR'
  have hmap : R'.map Y.subtype = P := by
    refine hP.2.2 (R'.map Y.subtype) ?_ (hR'3.map Y.subtype) ?_
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · intro p hp
      exact ⟨⟨p, hP.1 hp⟩, hPR' (by simpa [Subgroup.mem_subgroupOf] using hp), rfl⟩
  rw [← hmap]
  exact (Subgroup.comap_map_eq_self_of_injective Y.subtype_injective R').symm

theorem exists_conj_le_of_isSylowIn {Y P R : Subgroup G} (hP : IsSylowIn 3 Y P) (hRY : R ≤ Y)
    (hR : IsPGroup 3 R) : ∃ y ∈ Y, ∀ r ∈ R, y⁻¹ * r * y ∈ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP' := isSylowIn_top_subgroupOf hP
  obtain ⟨g, hg⟩ := exists_glbConj_le_of_isSylowIn hP'
    (hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRY).symm : IsPGroup 3 (R.subgroupOf Y))
  refine ⟨(g : G), g.2, fun r hr => ?_⟩
  have hmem : (⟨r, hRY hr⟩ : ↥Y) ∈ R.subgroupOf Y := by simpa [Subgroup.mem_subgroupOf] using hr
  have h1 : (g⁻¹ * ⟨r, hRY hr⟩ * g : ↥Y) ∈ GLBConj g (R.subgroupOf Y) :=
    mem_glbConj.2 ⟨_, hmem, rfl⟩
  have h2 := hg h1
  simpa [Subgroup.mem_subgroupOf] using h2

theorem isSylowIn_inf_of_normal {Y N P : Subgroup G} (hP : IsSylowIn 3 Y P) (hNY : N ≤ Y)
    (hn : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N) : IsSylowIn 3 N (P ⊓ N) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨inf_le_right, hP.2.1.to_le inf_le_left, ?_⟩
  intro T hTN hT3 hPT
  obtain ⟨Q, hQ, hTQ⟩ := exists_isSylowIn_ge hTN hT3
  obtain ⟨y, hyY, hy⟩ := exists_conj_le_of_isSylowIn hP (hQ.1.trans hNY) hQ.2.1
  have hcard : Nat.card Q ≤ Nat.card ↥(P ⊓ N) := by
    refine Nat.card_le_card_of_injective
      (fun q : Q => (⟨y⁻¹ * (q : G) * y, Subgroup.mem_inf.2 ⟨hy q q.2, ?_⟩⟩ : ↥(P ⊓ N))) ?_
    · have := hn y⁻¹ (Y.inv_mem hyY) q (hQ.1 q.2)
      simpa using this
    · intro q q' h
      apply Subtype.ext
      have h1 := congrArg Subtype.val h
      simp only [mul_left_inj, mul_right_inj] at h1
      exact h1
  have hTcard : Nat.card T ≤ Nat.card ↥(P ⊓ N) :=
    le_trans (Subgroup.card_le_of_le hTQ) hcard
  exact (Subgroup.eq_of_le_of_card_ge hPT hTcard).symm

theorem commute_of_mem_normalizer_zpowers {a x : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hx : IsPGroup 3 (Subgroup.zpowers x))
    (hn : x ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G)) :
    x * a = a * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : x * a * x⁻¹ ∈ Subgroup.zpowers a :=
    (Subgroup.mem_normalizer_iff.1 hn a).1 (Subgroup.mem_zpowers a)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hred : a ^ i = a ^ (i % 3) := by
    have := zpow_mod_orderOf a i
    rw [hord] at this
    exact_mod_cast this.symm
  have h3 : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha3
  have hr : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hr with h0 | h1 | h2
  · exfalso
    rw [hred, h0, zpow_zero] at hi
    apply ha1
    have : a = x⁻¹ * (x * a * x⁻¹) * x := by group
    rw [← hi] at this
    simpa using this
  · rw [hred, h1, zpow_one] at hi
    calc x * a = (x * a * x⁻¹) * x := by group
      _ = a * x := by rw [← hi]
  · exfalso
    rw [hred, h2] at hi
    have hinv : x * a * x⁻¹ = a⁻¹ := by
      refine hi.symm.trans ?_
      have : a ^ (2 : ℤ) * a = 1 := by
        have h := h3
        rw [show (3 : ℤ) = 2 + 1 by norm_num, zpow_add, zpow_one] at h
        exact h
      exact eq_inv_of_mul_eq_one_left this
    have hsq : (x * x) * a * (x * x)⁻¹ = a := by
      have e1 : (x * x) * a * (x * x)⁻¹ = x * (x * a * x⁻¹) * x⁻¹ := by group
      have e2 : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      rw [e1, hinv, e2, hinv, inv_inv]
    have hcomm : Commute (x * x) a := by
      show (x * x) * a = a * (x * x)
      calc (x * x) * a = ((x * x) * a * (x * x)⁻¹) * (x * x) := by group
        _ = a * (x * x) := by rw [hsq]
    have hfix : ∀ m : ℕ, (x * x) ^ m * a * ((x * x) ^ m)⁻¹ = a := by
      intro m
      rw [(hcomm.pow_left m).eq]
      simp
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hx) ⟨x, Subgroup.mem_zpowers x⟩
    rw [Subgroup.orderOf_mk] at hk
    obtain ⟨t, ht⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    have hxm : (x * x) ^ (t + 1) = x := by
      have e1 : (x * x) ^ (t + 1) = x ^ (2 * (t + 1)) := by
        rw [← sq, ← pow_mul]
      have e2 : 2 * (t + 1) = 3 ^ k + 1 := by omega
      rw [e1, e2, pow_succ, ← hk, pow_orderOf_eq_one, one_mul]
    have hxa : x * a * x⁻¹ = a := by
      have := hfix (t + 1)
      rwa [hxm] at this
    rw [hxa] at hinv
    apply ha1
    have h1' : a * a = 1 := by
      calc a * a = a * a⁻¹ := congrArg (fun w => a * w) hinv
        _ = 1 := mul_inv_cancel a
    calc a = a * (a * a) := by rw [h1', mul_one]
      _ = a ^ 3 := (pow_three a).symm
      _ = 1 := ha3

theorem isSylowIn_top_of_normalizes {Q : Subgroup G} {a : G} (hQ : IsSylowIn 3 (Cg a) Q)
    (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1)
    (hnorm : ∀ x ∈ Subgroup.normalizer (Q : Set G),
      x ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G)) :
    IsSylowIn 3 ⊤ Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP, hQP⟩ := exists_isSylowIn_ge (le_top : Q ≤ ⊤) hQ.2.1
  by_cases hPQ : Q = P
  · rw [hPQ]
    exact hP
  · exfalso
    obtain ⟨x, hxP, hxN, hxQ⟩ := exists_mem_normalizer_not_mem hP.2.1 hQP hPQ
    have hx3 : IsPGroup 3 (Subgroup.zpowers x) := hP.2.1.to_le (Subgroup.zpowers_le.2 hxP)
    have hcomm := commute_of_mem_normalizer_zpowers ha3 ha1 hx3 (hnorm x hxN)
    have hxC : x ∈ Cg a :=
      Subgroup.mem_centralizer_iff.2 (fun g hg => by
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact hcomm.symm)
    have hsup3 : IsPGroup 3 ↥(Q ⊔ Subgroup.zpowers x) :=
      hP.2.1.to_le (sup_le hQP (Subgroup.zpowers_le.2 hxP))
    have heq := hQ.2.2 (Q ⊔ Subgroup.zpowers x) (sup_le hQ.1 (Subgroup.zpowers_le.2 hxC))
      hsup3 le_sup_left
    apply hxQ
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem isPGroup_zpowers_of_pow {H : Type*} [Group H] {h : H} {k : ℕ} (hk : h ^ (3 ^ k) = 1) :
    IsPGroup 3 (Subgroup.zpowers h) := by
  have hd : orderOf h ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])

theorem mem_sup_of_normalizes_sylow {H : Type*} [Group H] [Finite H] {N S : Subgroup H}
    [N.Normal] (hS : IsSylowIn 3 (⊤ : Subgroup H) S) {h : H}
    (hn : ∀ s ∈ S, h * s * h⁻¹ ∈ S ⊔ N) (h3 : ∃ k : ℕ, h ^ (3 ^ k) ∈ N) : h ∈ S ⊔ N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := h3
  let S' : Sylow 3 H := ⟨S, hS.2.1, fun {Q} hQ hSQ => hS.2.2 Q le_top hQ hSQ⟩
  let π : H →* H ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  let S2 : Sylow 3 (H ⧸ N) := S'.mapSurjective hπ
  have hS2 : (S2 : Subgroup (H ⧸ N)) = S.map π := rfl
  have hle : ∀ y ∈ S.map π, π h * y * (π h)⁻¹ ∈ S.map π := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 := hn s hs
    have h2 : π (h * s * h⁻¹) ∈ (S ⊔ N).map π := ⟨_, h1, rfl⟩
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h2
    simpa [map_mul, map_inv] using h2
  have hnormal : π h ∈ Subgroup.normalizer ((S.map π : Subgroup (H ⧸ N)) : Set (H ⧸ N)) := by
    have hmap : (S.map π).map (MulAut.conj (π h)).toMonoidHom ≤ S.map π := by
      rintro _ ⟨y, hy, rfl⟩
      exact hle y hy
    have heq : (S.map π).map (MulAut.conj (π h)).toMonoidHom = S.map π :=
      Subgroup.eq_of_le_of_card_ge hmap
        (Subgroup.card_map_of_injective
          (f := (MulAut.conj (π h)).toMonoidHom) (MulAut.conj (π h)).injective).ge
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hle y hy
    · intro hy
      have : π h * y * (π h)⁻¹ ∈ (S.map π).map (MulAut.conj (π h)).toMonoidHom := by
        rw [heq]
        exact hy
      obtain ⟨z, hz, hzy⟩ := this
      have : z = y := by
        have := hzy
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
        simpa [mul_assoc] using this
      rw [← this]
      exact hz
  have hpow : (π h) ^ (3 ^ k) = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hk
  have hz3 : IsPGroup 3 (Subgroup.zpowers (π h)) := isPGroup_zpowers_of_pow hpow
  have hinf := hz3.inf_normalizer_sylow S2
  have hnormal' : π h ∈ Subgroup.normalizer ((S2 : Subgroup (H ⧸ N)) : Set (H ⧸ N)) := by
    rw [hS2]
    exact hnormal
  have hmem : π h ∈ Subgroup.zpowers (π h) ⊓ Subgroup.normalizer (S2 : Set (H ⧸ N)) :=
    ⟨Subgroup.mem_zpowers _, hnormal'⟩
  rw [hinf] at hmem
  have hmem2 : π h ∈ S.map π := by
    have := hmem.2
    rw [hS2] at this
    exact this
  obtain ⟨s, hs, hsh⟩ := hmem2
  have : s⁻¹ * h ∈ N := (QuotientGroup.eq).1 hsh
  have e : h = s * (s⁻¹ * h) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right this)

end Generic

section Bar

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut_mk mk_eq_iff_glaPPrimeCoreOf)

theorem mem_centBar_iff' {X K : Subgroup G} {x : G} :
    x ∈ centBar 3 X K ↔ x ∈ X ∧ ∃ hx : x ∈ Subgroup.normalizer (K : Set G),
      barAut 3 K ⟨x, hx⟩ = 1 := by
  unfold centBar
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨γ, hγ, hγx⟩ := Subgroup.mem_map.1 hx1
    refine ⟨hx2, ?_, ?_⟩
    · rw [← hγx]
      exact γ.2
    · have : γ = ⟨x, by rw [← hγx]; exact γ.2⟩ := Subtype.ext hγx
      rw [← this]
      exact MonoidHom.mem_ker.1 hγ
  · rintro ⟨hxX, hxN, h1⟩
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨⟨x, hxN⟩, MonoidHom.mem_ker.2 h1, rfl⟩, hxX⟩

theorem comm_mem_of_mem_centBar {X K : Subgroup G} {c p : G} (hc : c ∈ centBar 3 X K)
    (hp : p ∈ K) : c * p * c⁻¹ * p⁻¹ ∈ GLAPPrimeCoreOf 3 K := by
  obtain ⟨-, hcN, h1⟩ := mem_centBar_iff'.1 hc
  have h2 := barAut_mk 3 K ⟨c, hcN⟩ ⟨p⁻¹, K.inv_mem hp⟩
  rw [h1] at h2
  have h3 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)
      (K.normalizerMonoidHom ⟨c, hcN⟩ ⟨p⁻¹, K.inv_mem hp⟩) =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨p⁻¹, K.inv_mem hp⟩ := by
    simpa using h2.symm
  have h4 := (mk_eq_iff_glaPPrimeCoreOf _ _).1 h3
  have e : ((K.normalizerMonoidHom ⟨c, hcN⟩ ⟨p⁻¹, K.inv_mem hp⟩ : ↥K) : G)⁻¹ * ((⟨p⁻¹, K.inv_mem hp⟩ : ↥K) : G)
      = c * p * c⁻¹ * p⁻¹ := by
    show (c * p⁻¹ * c⁻¹)⁻¹ * p⁻¹ = c * p * c⁻¹ * p⁻¹
    group
  rw [e] at h4
  exact h4

theorem mem_centBar_of_comm {X K : Subgroup G} {x : G} (hxX : x ∈ X)
    (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (h : ∀ p ∈ K, x * p * x⁻¹ * p⁻¹ ∈ GLAPPrimeCoreOf 3 K) : x ∈ centBar 3 X K := by
  refine mem_centBar_iff'.2 ⟨hxX, hxN, ?_⟩
  refine MulEquiv.ext fun y => ?_
  induction y using QuotientGroup.induction_on with
  | H p =>
    rw [barAut_mk, MulAut.one_apply]
    have h4 := h (p : G)⁻¹ (K.inv_mem p.2)
    have h5 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) (K.normalizerMonoidHom ⟨x, hxN⟩ p) =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) p := by
      refine (mk_eq_iff_glaPPrimeCoreOf _ _).2 ?_
      have e : ((K.normalizerMonoidHom ⟨x, hxN⟩ p : ↥K) : G)⁻¹ * (p : G) =
          x * (p : G)⁻¹ * x⁻¹ * ((p : G)⁻¹)⁻¹ := by
        show (x * (p : G) * x⁻¹)⁻¹ * (p : G) = x * (p : G)⁻¹ * x⁻¹ * ((p : G)⁻¹)⁻¹
        group
      rw [e]
      exact h4
    exact h5

theorem conj_mem_centBar {X K : Subgroup G} {y c : G} (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hyX : y ∈ X) (hc : c ∈ centBar 3 X K) : y * c * y⁻¹ ∈ centBar 3 X K := by
  obtain ⟨hcX, hcN, h1⟩ := mem_centBar_iff'.1 hc
  refine mem_centBar_iff'.2 ⟨X.mul_mem (X.mul_mem hyX hcX) (X.inv_mem hyX),
    (Subgroup.normalizer (K : Set G)).mul_mem ((Subgroup.normalizer (K : Set G)).mul_mem hyN hcN)
      ((Subgroup.normalizer (K : Set G)).inv_mem hyN), ?_⟩
  have : (⟨y * c * y⁻¹, _⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨y, hyN⟩ * ⟨c, hcN⟩ * ⟨y, hyN⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, h1]
  simp

theorem pPrimeCoreOf_le_centBar {X K : Subgroup G} (hKX : K ≤ X) :
    GLAPPrimeCoreOf 3 K ≤ centBar 3 X K := by
  intro o ho
  obtain ⟨o', ho', rfl⟩ := ho
  refine mem_centBar_of_comm (hKX o'.2) (Subgroup.le_normalizer o'.2) fun p hp => ?_
  have h1 : (⟨p, hp⟩ : ↥K) * o'⁻¹ * (⟨p, hp⟩ : ↥K)⁻¹ ∈ GLAPPrimeCore 3 ↥K :=
    (GLAPPrimeCore.normal 3 ↥K).conj_mem _ ((GLAPPrimeCore 3 ↥K).inv_mem ho') ⟨p, hp⟩
  have h2 : (o' : G) * ((⟨p, hp⟩ : ↥K) * o'⁻¹ * (⟨p, hp⟩ : ↥K)⁻¹ : ↥K) ∈ GLAPPrimeCoreOf 3 K :=
    ⟨o' * ((⟨p, hp⟩ : ↥K) * o'⁻¹ * (⟨p, hp⟩ : ↥K)⁻¹),
      (GLAPPrimeCore 3 ↥K).mul_mem ho' h1, rfl⟩
  have e : (o' : G) * (((⟨p, hp⟩ : ↥K) * o'⁻¹ * (⟨p, hp⟩ : ↥K)⁻¹ : ↥K) : G) =
      (o' : G) * p * (o' : G)⁻¹ * p⁻¹ := by
    show (o' : G) * (p * (o' : G)⁻¹ * p⁻¹) = (o' : G) * p * (o' : G)⁻¹ * p⁻¹
    group
  change (o' : G) * p * (o' : G)⁻¹ * p⁻¹ ∈ GLAPPrimeCoreOf 3 K
  rw [← e]
  exact h2

theorem mk_mem_center_of_centBar {X K : Subgroup G} {k : G} (hk : k ∈ K)
    (hkc : k ∈ centBar 3 X K) :
    (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : barOf 3 K) ∈ Subgroup.center (barOf 3 K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
  have h1 := comm_mem_of_mem_centBar hkc y.2
  have h2 : (⟨k, hk⟩ : ↥K) * y * (⟨k, hk⟩ : ↥K)⁻¹ * y⁻¹ ∈ GLAPPrimeCore 3 ↥K :=
    (CFSG.HardMathSupport.Solomon.LocalBalance.mem_glaPPrimeCoreOf_iff
      ((⟨k, hk⟩ : ↥K) * y * (⟨k, hk⟩ : ↥K)⁻¹ * y⁻¹)).1 h1
  have h3 := (QuotientGroup.eq_one_iff _).2 h2
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv] at h3
  set u : barOf 3 K := QuotientGroup.mk ⟨k, hk⟩
  set v : barOf 3 K := QuotientGroup.mk y
  calc v * u = (u * v * u⁻¹ * v⁻¹)⁻¹ * (u * v) := by group
    _ = u * v := by rw [h3, inv_one, one_mul]

theorem mem_pPrimeCoreOf_of_centBar {X K : Subgroup G}
    (hZ : Subgroup.center (barOf 3 K) = ⊥) {k : G} (hk : k ∈ K) (hkc : k ∈ centBar 3 X K) :
    k ∈ GLAPPrimeCoreOf 3 K := by
  have hz := mk_mem_center_of_centBar hk hkc
  rw [hZ] at hz
  have h1 : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : barOf 3 K) = 1 := Subgroup.mem_bot.1 hz
  have h2 : (⟨k, hk⟩ : ↥K) ∈ GLAPPrimeCore 3 ↥K := (QuotientGroup.eq_one_iff _).1 h1
  exact (CFSG.HardMathSupport.Solomon.LocalBalance.mem_glaPPrimeCoreOf_iff
    (⟨k, hk⟩ : ↥K)).2 h2

theorem pow_three_mem_pPrimeCoreOf_of_centBar {X K : Subgroup G}
    (hZ3 : ∀ z ∈ Subgroup.center (barOf 3 K), z ^ 3 = 1) {k : G} (hk : k ∈ K)
    (hkc : k ∈ centBar 3 X K) : k ^ 3 ∈ GLAPPrimeCoreOf 3 K := by
  have hz := hZ3 _ (mk_mem_center_of_centBar hk hkc)
  have h2 : (⟨k, hk⟩ : ↥K) ^ 3 ∈ GLAPPrimeCore 3 ↥K := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    rw [QuotientGroup.mk_pow]
    exact hz
  have := (CFSG.HardMathSupport.Solomon.LocalBalance.mem_glaPPrimeCoreOf_iff
    ((⟨k, hk⟩ : ↥K) ^ 3)).2 h2
  simpa using this

theorem eq_one_of_mem_pPrimeCoreOf {K P : Subgroup G} (hP : IsPGroup 3 ↥P) {x : G}
    (hxO : x ∈ GLAPPrimeCoreOf 3 K) (hxP : x ∈ P) : x = 1 := by
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨x, hxP⟩
  rw [Subgroup.orderOf_mk] at hj
  by_contra hx1
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.1 (by rw [hj]; rfl))
  have hdvd : orderOf x ∣ Nat.card (GLAPPrimeCoreOf 3 K) := by
    have := orderOf_dvd_natCard (⟨x, hxO⟩ : ↥(GLAPPrimeCoreOf 3 K))
    rwa [Subgroup.orderOf_mk] at this
  apply not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
  refine dvd_trans ?_ hdvd
  rw [hj]
  exact dvd_pow_self 3 hj0

theorem exists_mem_sylow_mul_mem_centBar {X K S : Subgroup G}
    (hZ3 : ∀ z ∈ Subgroup.center (barOf 3 K), z ^ 3 = 1) (hKX : K ≤ X) (hS : IsSylowIn 3 K S) {x : G}
    (hxX : x ∈ X) (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx3 : x ^ 3 = 1)
    (hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S) (hinn : ∃ k ∈ K, k⁻¹ * x ∈ centBar 3 ⊤ K) :
    ∃ s ∈ S, s⁻¹ * x ∈ centBar 3 X K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk, hc₀⟩ := hinn
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
  obtain ⟨-, hc₀N, hc₀1⟩ := mem_centBar_iff'.1 hc₀
  have hc₀X : k⁻¹ * x ∈ centBar 3 X K := by
    refine mem_centBar_iff'.2 ⟨X.mul_mem (X.inv_mem (hKX hk)) hxX, hc₀N, hc₀1⟩
  have hxk : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨k, hkN⟩ * ⟨k⁻¹ * x, hc₀N⟩ := Subtype.ext (by simp)
  have hρ : barAut 3 K ⟨x, hxN⟩ = barAut 3 K ⟨k, hkN⟩ := by
    rw [hxk, map_mul, hc₀1, mul_one]
  have hS' := isSylowIn_top_subgroupOf hS
  have hn : ∀ s ∈ S.subgroupOf K, (⟨k, hk⟩ : ↥K) * s * (⟨k, hk⟩ : ↥K)⁻¹ ∈
      S.subgroupOf K ⊔ GLAPPrimeCore 3 ↥K := by
    intro s hs
    have hs0 : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
    have e1 := barAut_mk 3 K ⟨x, hxN⟩ s
    have e2 := barAut_mk 3 K ⟨k, hkN⟩ s
    rw [hρ] at e1
    have e3 := e2.symm.trans e1
    have h4 := QuotientGroup.eq.1 e3
    have hxs' : (K.normalizerMonoidHom ⟨x, hxN⟩ s : ↥K) ∈ S.subgroupOf K :=
      Subgroup.mem_subgroupOf.2 (hxS _ hs0)
    set n : ↥K := (K.normalizerMonoidHom ⟨k, hkN⟩ s)⁻¹ * K.normalizerMonoidHom ⟨x, hxN⟩ s
      with hn_def
    have hnN : n ∈ GLAPPrimeCore 3 ↥K := h4
    have hσk : K.normalizerMonoidHom ⟨k, hkN⟩ s = (⟨k, hk⟩ : ↥K) * s * (⟨k, hk⟩ : ↥K)⁻¹ :=
      Subtype.ext rfl
    have e : (⟨k, hk⟩ : ↥K) * s * (⟨k, hk⟩ : ↥K)⁻¹ =
        K.normalizerMonoidHom ⟨x, hxN⟩ s * n⁻¹ := by
      rw [← hσk, hn_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxs')
      (Subgroup.mem_sup_right ((GLAPPrimeCore 3 ↥K).inv_mem hnN))
  have h3 : ∃ j : ℕ, (⟨k, hk⟩ : ↥K) ^ (3 ^ j) ∈ GLAPPrimeCore 3 ↥K := by
    refine ⟨2, ?_⟩
    have hkc : barAut 3 K ⟨k, hkN⟩ ^ 3 = 1 := by
      rw [← hρ, ← map_pow]
      have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have hk3 : k ^ 3 ∈ centBar 3 ⊤ K := by
      refine mem_centBar_iff'.2 ⟨Subgroup.mem_top _, (Subgroup.normalizer (K : Set G)).pow_mem hkN 3, ?_⟩
      have : (⟨k ^ 3, (Subgroup.normalizer (K : Set G)).pow_mem hkN 3⟩ :
          ↥(Subgroup.normalizer (K : Set G))) = ⟨k, hkN⟩ ^ 3 := Subtype.ext rfl
      rw [this, map_pow]
      exact hkc
    have hk3O : (k ^ 3) ^ 3 ∈ GLAPPrimeCoreOf 3 K :=
      pow_three_mem_pPrimeCoreOf_of_centBar hZ3 (K.pow_mem hk 3) hk3
    have := (CFSG.HardMathSupport.Solomon.LocalBalance.mem_glaPPrimeCoreOf_iff
      ((⟨k, hk⟩ : ↥K) ^ 9)).1 (by simpa [← pow_mul] using hk3O)
    simpa using this
  have hmem := mem_sup_of_normalizes_sylow hS' hn h3
  obtain ⟨s, hs, n, hnN, hsn⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  have hs0 : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
  have hk_eq : k = (s : G) * (n : G) := by
    have := congrArg Subtype.val hsn
    simpa using this.symm
  refine ⟨(s : G), hs0, ?_⟩
  have hnO : (n : G) ∈ centBar 3 X K :=
    pPrimeCoreOf_le_centBar hKX ⟨n, hnN, rfl⟩
  have e : (s : G)⁻¹ * x = (n : G) * (k⁻¹ * x) := by
    rw [hk_eq]
    group
  rw [e]
  exact Subgroup.mul_mem _ hnO hc₀X

end Bar

section Facts

variable {G : Type} [Group G] [Finite G]

structure FactsBase (E A K : Subgroup G) (a : G) : Prop where
  hAel : IsElemAbelian 3 A
  hsc : IsSCp 3 ⊤ A
  hcardA : Nat.card A = 27
  hcardA0 : Nat.card ↥(E ⊓ A) = 9
  hA0el : IsElemAbelian 3 (E ⊓ A)
  ha : a ∈ A
  ha1 : a ≠ 1
  ha3 : a ^ 3 = 1
  haE : a ∉ E ⊓ A
  hAsup : (E ⊓ A) ⊔ Subgroup.zpowers a = A
  hKC : K ≤ Cg a
  hAN : A ≤ Subgroup.normalizer (K : Set G)
  hAin : A ≤ innerSub K
  hAK : A ≤ K ⊔ centBar 3 (Cg a) K
  hfaith : InducesFaithfulInner 3 (E ⊓ A) K

structure Facts (E A K : Subgroup G) (a : G) : Prop extends FactsBase E A K a where
  hL : IsLThreeFour (barOf 3 K)
  haK : a ∉ K
  hnotA : ¬ A ≤ K

structure FactsSL (E A K : Subgroup G) (a : G) : Prop extends FactsBase E A K a where
  hSL : IsSLThreeFour (barOf 3 K)

theorem facts_base_of {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K) (hpA : CFSG.Open.pRank 3 A = 3)
    (h119 : CFSG.Open.pRank 3 (E ⊓ A) = 2 ∧ InducesFaithfulInner 3 (E ⊓ A) K)
    (hsc : IsSCp 3 ⊤ A) : FactsBase E A K a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hE9, hEfaith⟩ := h119
  have hAel : IsElemAbelian 3 A := hsc.2.1
  have hcardA : Nat.card A = 27 := by
    rw [Lemma1112.card_eq_pow_pRank hAel, hpA]
    norm_num
  have hEA_el : IsElemAbelian 3 (E ⊓ A) := Lemma1112.isElemAbelian_of_le hAel inf_le_right
  have hcardEA : Nat.card ↥(E ⊓ A) = 9 := by
    rw [Lemma1112.card_eq_pow_pRank hEA_el, hE9]
    norm_num
  obtain ⟨ha, ha1⟩ := h.ha
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have hKC : K ≤ Cg a := h.hK.1
  have hcomm : ∀ k ∈ K, a * k = k * a := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 (hKC hk)) a (Set.mem_singleton a)
  have haE : a ∉ E ⊓ A := by
    intro haEA
    exact h.notD ⟨E, h.pair.1.1, (Subgroup.mem_inf.1 haEA).1⟩
  have hAsup : (E ⊓ A) ⊔ Subgroup.zpowers a = A :=
    sup_eq_of_card_nine hcardA inf_le_right hcardEA ha haE
  have haN : a ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_central hcomm
  have hEN : E ⊓ A ≤ Subgroup.normalizer (K : Set G) := hEfaith.1
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := by
    rw [← hAsup]
    exact sup_le hEN (Subgroup.zpowers_le.2 haN)
  have hAin : A ≤ innerSub K := by
    rw [← hAsup]
    refine sup_le (fun x hx => mem_innerSub.2 ⟨hEN hx, hEfaith.2.2 x hx⟩) ?_
    refine Subgroup.zpowers_le.2 (mem_innerSub.2 ⟨haN, 1, Subgroup.one_mem _, ?_⟩)
    rw [inv_one, one_mul]
    exact mem_centBar_top_of_central haN hcomm
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 (fun g hg => by
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact hAc a ha x hx)
  exact ⟨hAel, hsc, hcardA, hcardEA, hEA_el, ha, ha1, ha3, haE, hAsup, hKC, hAN, hAin,
    le_sup_centBar_of_le_innerSub hKC hAa hAin, hEfaith⟩

theorem facts_of {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K) (hL : IsLThreeFour (barOf 3 K))
    (hpA : CFSG.Open.pRank 3 A = 3)
    (h119 : CFSG.Open.pRank 3 (E ⊓ A) = 2 ∧ InducesFaithfulInner 3 (E ⊓ A) K)
    (hsc : IsSCp 3 ⊤ A) : Facts E A K a := by
  have hB := facts_base_of h hpA h119 hsc
  have hcomm : ∀ k ∈ K, a * k = k * a := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 (hB.hKC hk)) a (Set.mem_singleton a)
  have haK : a ∉ K := fun haK => not_mem_of_centralizes hL haK hcomm hB.ha3 hB.ha1
  have hnotA : ¬ A ≤ K := Lemma1112.not_le_K h hB.hAel hL
  exact { hB with hL := hL, haK := haK, hnotA := hnotA }

variable {E A K : Subgroup G} {a : G}

theorem FactsBase.hAc (F : FactsBase E A K a) : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (F.hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem FactsBase.inf_centBar_le (F : FactsBase E A K a) : A ⊓ centBar 3 (Cg a) K ≤ Subgroup.zpowers a := by
  intro x hx
  obtain ⟨hxA, hxc⟩ := Subgroup.mem_inf.1 hx
  have hc : ∀ y ∈ E ⊓ A, ∀ z ∈ Subgroup.zpowers a, y * z = z * y := by
    intro y hy z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_right (F.hAc y (Subgroup.mem_inf.1 hy).2 a F.ha : Commute y a) i).eq
  have hxsup : x ∈ (E ⊓ A) ⊔ Subgroup.zpowers a := by rw [F.hAsup]; exact hxA
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hxsup
  have hacomm : ∀ k ∈ K, a * k = k * a := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 (F.hKC hk)) a (Set.mem_singleton a)
  have haN : a ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_central hacomm
  have hzc : z ∈ centBar 3 ⊤ K := by
    have ha' : a ∈ centBar 3 ⊤ K := mem_centBar_top_of_central haN hacomm
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact Subgroup.zpow_mem _ ha' i
  have hxc' : y * z ∈ centBar 3 ⊤ K := by
    obtain ⟨-, hN, h1⟩ := mem_centBar_iff'.1 hxc
    exact mem_centBar_iff'.2 ⟨Subgroup.mem_top _, hN, h1⟩
  have hyc : y ∈ centBar 3 ⊤ K := by
    have := Subgroup.mul_mem _ hxc' (Subgroup.inv_mem _ hzc)
    simpa using this
  have hy1 : y = 1 := F.hfaith.2.1 y hy hyc
  rw [hy1, one_mul]
  exact hz

theorem FactsBase.mem_centBar_a (F : FactsBase E A K a) : a ∈ centBar 3 (Cg a) K := by
  have hacomm : ∀ k ∈ K, a * k = k * a := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 (F.hKC hk)) a (Set.mem_singleton a)
  exact mem_centBar_of_mem_top (mem_centBar_top_of_central (mem_normalizer_of_central hacomm) hacomm)
    (Subgroup.mem_centralizer_iff.2 (fun g hg => by rw [Set.mem_singleton_iff] at hg; rw [hg]))

end Facts

section RankOne

variable {G : Type} [Group G] [Finite G] {E A K : Subgroup G} {a : G}

theorem Facts.main (F : Facts E A K a) :
    A ≤ K ⊔ Subgroup.zpowers a ∧
      ∀ U : Subgroup G, U ≤ centBar 3 (Cg a) K → IsElemAbelian 3 U → Nat.card U ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center (barOf 3 K) = ⊥ := Lemma1112.center_eq_bot_of_isLThreeFour F.hL
  set C₁ := centBar 3 (Cg a) K with hC₁def
  set Y := K ⊔ C₁ with hYdef
  have hC₁N : C₁ ≤ Subgroup.normalizer (K : Set G) := centBar_le_normalizer 3 _ K
  have hC₁C : C₁ ≤ Cg a := inf_le_right
  have hKY : K ≤ Y := le_sup_left
  have hC₁Y : C₁ ≤ Y := le_sup_right
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hC₁N
  have hYC : Y ≤ Cg a := sup_le F.hKC hC₁C
  have hKnorm : ∀ y ∈ Y, ∀ n ∈ K, y * n * y⁻¹ ∈ K := fun y hy n hn =>
    (Subgroup.mem_normalizer_iff.1 (hYN hy) n).1 hn
  have hC₁norm : ∀ y ∈ Y, ∀ n ∈ C₁, y * n * y⁻¹ ∈ C₁ := fun y hy n hn =>
    conj_mem_centBar (hYN hy) (hYC hy) hn
  have hA3 : IsPGroup 3 ↥A := isPGroup_of_isElemAbelian F.hAel
  obtain ⟨P, hP, hAP⟩ := exists_isSylowIn_ge F.hAK hA3
  have hP3 : IsPGroup 3 ↥P := hP.2.1
  have hP₁ : IsSylowIn 3 K (P ⊓ K) := isSylowIn_inf_of_normal hP hKY hKnorm
  have hint : ∀ z ∈ P ⊓ K, z ∈ P ⊓ C₁ → z = 1 := by
    intro z hzK hzC
    have hzO : z ∈ GLAPPrimeCoreOf 3 K :=
      mem_pPrimeCoreOf_of_centBar hZ (Subgroup.mem_inf.1 hzK).2 (Subgroup.mem_inf.1 hzC).2
    exact eq_one_of_mem_pPrimeCoreOf hP3 hzO (Subgroup.mem_inf.1 hzK).1
  have hcomm12 : ∀ s ∈ P ⊓ K, ∀ p ∈ P ⊓ C₁, s * p = p * s := by
    intro s hs p hp
    have h1 := comm_mem_of_mem_centBar (Subgroup.mem_inf.1 hp).2 (Subgroup.mem_inf.1 hs).2
    have h2 : p * s * p⁻¹ * s⁻¹ = 1 := by
      refine eq_one_of_mem_pPrimeCoreOf hP3 h1 ?_
      exact P.mul_mem (P.mul_mem (P.mul_mem (Subgroup.mem_inf.1 hp).1 (Subgroup.mem_inf.1 hs).1)
        (P.inv_mem (Subgroup.mem_inf.1 hp).1)) (P.inv_mem (Subgroup.mem_inf.1 hs).1)
    calc s * p = (p * s * p⁻¹ * s⁻¹)⁻¹ * (p * s) := by group
      _ = p * s := by rw [h2, inv_one, one_mul]
  have hD : ∀ x ∈ A, ∃ s ∈ P ⊓ K, s⁻¹ * x ∈ P ⊓ C₁ := by
    intro x hx
    obtain ⟨hxN, hinn⟩ := mem_innerSub.1 (F.hAin hx)
    have hxP : x ∈ P := hAP hx
    obtain ⟨s, hs, hsc⟩ := exists_mem_sylow_mul_mem_centBar (X := Cg a)
      (fun z hz => by rw [hZ] at hz; rw [Subgroup.mem_bot.1 hz, one_pow]) F.hKC hP₁
      (hYC (F.hAK hx)) hxN (F.hAel.2 x hx)
      (fun s hs => Subgroup.mem_inf.2 ⟨P.mul_mem (P.mul_mem hxP (Subgroup.mem_inf.1 hs).1)
        (P.inv_mem hxP), (Subgroup.mem_normalizer_iff.1 hxN s).1 (Subgroup.mem_inf.1 hs).2⟩) hinn
    exact ⟨s, hs, Subgroup.mem_inf.2 ⟨P.mul_mem (P.inv_mem (Subgroup.mem_inf.1 hs).1) hxP, hsc⟩⟩
  let F₂ : Subgroup G :=
    { carrier := {p | p ∈ P ⊓ C₁ ∧ ∃ s ∈ P ⊓ K, s * p ∈ A}
      one_mem' := ⟨Subgroup.one_mem _, 1, Subgroup.one_mem _, by simpa using A.one_mem⟩
      mul_mem' := by
        rintro p p' ⟨hp, s, hs, hsp⟩ ⟨hp', s', hs', hsp'⟩
        refine ⟨Subgroup.mul_mem _ hp hp', s * s', Subgroup.mul_mem _ hs hs', ?_⟩
        have e : s * s' * (p * p') = (s * p) * (s' * p') := by
          calc s * s' * (p * p') = s * (s' * p) * p' := by group
            _ = s * (p * s') * p' := by rw [hcomm12 s' hs' p hp]
            _ = (s * p) * (s' * p') := by group
        rw [e]
        exact A.mul_mem hsp hsp'
      inv_mem' := by
        rintro p ⟨hp, s, hs, hsp⟩
        refine ⟨Subgroup.inv_mem _ hp, s⁻¹, Subgroup.inv_mem _ hs, ?_⟩
        have e : s⁻¹ * p⁻¹ = (s * p)⁻¹ := by
          calc s⁻¹ * p⁻¹ = (p * s)⁻¹ := by group
            _ = (s * p)⁻¹ := by rw [hcomm12 s hs p hp]
        rw [e]
        exact A.inv_mem hsp }
  have hAdec : ∀ x ∈ A, ∃ s ∈ P ⊓ K, ∃ p ∈ F₂, x = s * p := by
    intro x hx
    obtain ⟨s, hs, hsp⟩ := hD x hx
    exact ⟨s, hs, s⁻¹ * x, ⟨hsp, s, hs, by simpa using hx⟩, by group⟩
  have hF₂comm : ∀ p ∈ F₂, ∀ p' ∈ F₂, p * p' = p' * p := by
    rintro p ⟨hp, s, hs, hsp⟩ p' ⟨hp', s', hs', hsp'⟩
    have hA := F.hAc _ hsp _ hsp'
    have e : s * s' * (p * p') = s' * s * (p' * p) := by
      calc s * s' * (p * p') = s * (s' * p) * p' := by group
        _ = s * (p * s') * p' := by rw [hcomm12 s' hs' p hp]
        _ = (s * p) * (s' * p') := by group
        _ = (s' * p') * (s * p) := hA
        _ = s' * (p' * s) * p := by group
        _ = s' * (s * p') * p := by rw [hcomm12 s hs p' hp']
        _ = s' * s * (p' * p) := by group
    have hw : (s' * s)⁻¹ * (s * s') = (p' * p) * (p * p')⁻¹ := by
      calc (s' * s)⁻¹ * (s * s') = (s' * s)⁻¹ * (s * s' * (p * p')) * (p * p')⁻¹ := by group
        _ = (s' * s)⁻¹ * (s' * s * (p' * p)) * (p * p')⁻¹ := by rw [e]
        _ = (p' * p) * (p * p')⁻¹ := by group
    have hw1 : (s' * s)⁻¹ * (s * s') ∈ P ⊓ K :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hs' hs)) (Subgroup.mul_mem _ hs hs')
    have hw2 : (p' * p) * (p * p')⁻¹ ∈ P ⊓ C₁ :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hp' hp) (Subgroup.inv_mem _ (Subgroup.mul_mem _ hp hp'))
    have h1 := hint _ hw1 (by rw [hw]; exact hw2)
    rw [hw] at h1
    exact (mul_inv_eq_one.1 h1).symm
  have hF₂el : IsElemAbelian 3 F₂ := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hF₂comm x x.2 y y.2)⟩⟩, fun p hp => ?_⟩
    obtain ⟨hpC, s, hs, hsp⟩ := hp
    have h3 : (s * p) ^ 3 = 1 := F.hAel.2 _ hsp
    have hcm : Commute s p := hcomm12 s hs p hpC
    rw [hcm.mul_pow] at h3
    have hs3 : s ^ 3 ∈ P ⊓ K := Subgroup.pow_mem _ hs 3
    have hp3 : (p ^ 3)⁻¹ ∈ P ⊓ C₁ := Subgroup.inv_mem _ (Subgroup.pow_mem _ hpC 3)
    have hsp3 : s ^ 3 = (p ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h3
    have := hint _ hs3 (by rw [hsp3]; exact hp3)
    rw [hsp3, inv_eq_one] at this
    exact this
  have hAF₂comm : ∀ x ∈ A, ∀ q ∈ F₂, x * q = q * x := by
    intro x hx q hq
    obtain ⟨s, hs, p, hp, rfl⟩ := hAdec x hx
    have hqP : q ∈ P ⊓ C₁ := hq.1
    calc s * p * q = s * (p * q) := by group
      _ = s * (q * p) := by rw [hF₂comm p hp q hq]
      _ = (s * q) * p := by group
      _ = (q * s) * p := by rw [hcomm12 s hs q hqP]
      _ = q * (s * p) := by group
  have hAF₂ : F₂ ≤ A := by
    have hel := isElemAbelian_sup F.hAel hF₂el hAF₂comm
    have := F.hsc.2.2 (A ⊔ F₂) le_top hel le_sup_left
    intro q hq
    rw [← this]
    exact Subgroup.mem_sup_right hq
  have hF₂a : F₂ ≤ Subgroup.zpowers a := fun q hq =>
    F.inf_centBar_le (Subgroup.mem_inf.2 ⟨hAF₂ hq, (Subgroup.mem_inf.1 hq.1).2⟩)
  have hAle : A ≤ K ⊔ Subgroup.zpowers a := by
    intro x hx
    obtain ⟨s, hs, p, hp, rfl⟩ := hAdec x hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.1 hs).2)
      (Subgroup.mem_sup_right (hF₂a hp))
  refine ⟨hAle, ?_⟩
  intro U hUC hUel
  have hU3 : IsPGroup 3 ↥U := isPGroup_of_isElemAbelian hUel
  have hUY : U ≤ Y := hUC.trans hC₁Y
  obtain ⟨y, hyY, hy⟩ := exists_conj_le_of_isSylowIn hP hUY hU3
  have hU'el : IsElemAbelian 3 (GLBConj y U) := isElemAbelian_glbConj hUel y
  have hU'card : Nat.card (GLBConj y U) = Nat.card U := card_glbConj y U
  have hU'P : GLBConj y U ≤ P ⊓ C₁ := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := mem_glbConj.1 hw
    refine Subgroup.mem_inf.2 ⟨hy u hu, ?_⟩
    have := hC₁norm y⁻¹ (Y.inv_mem hyY) u (hUC hu)
    simpa using this
  have haC₁ : a ∈ C₁ := by
    have hacomm : ∀ k ∈ K, a * k = k * a := fun k hk =>
      (Subgroup.mem_centralizer_iff.1 (F.hKC hk)) a (Set.mem_singleton a)
    have haN : a ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_central hacomm
    exact mem_centBar_of_mem_top (mem_centBar_top_of_central haN hacomm)
      (Subgroup.mem_centralizer_iff.2 (fun g hg => by rw [Set.mem_singleton_iff] at hg; rw [hg]))
  have haP : a ∈ P ⊓ C₁ := Subgroup.mem_inf.2 ⟨hAP F.ha, haC₁⟩
  have hacomm' : ∀ w ∈ GLBConj y U, ∀ z ∈ Subgroup.zpowers a, w * z = z * w := by
    intro w hw z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hwC : w ∈ Cg a := hC₁C (Subgroup.mem_inf.1 (hU'P hw)).2
    have hwa : a * w = w * a := (Subgroup.mem_centralizer_iff.1 hwC) a (Set.mem_singleton a)
    exact (Commute.zpow_right (hwa.symm : Commute w a) i).eq
  have hWel : IsElemAbelian 3 (GLBConj y U ⊔ Subgroup.zpowers a) :=
    isElemAbelian_sup hU'el (Lemma1111.isElemAbelian_zpowers F.ha3) hacomm'
  have hWP : GLBConj y U ⊔ Subgroup.zpowers a ≤ P ⊓ C₁ :=
    sup_le hU'P (Subgroup.zpowers_le.2 haP)
  have hAWcomm : ∀ x ∈ A, ∀ w ∈ GLBConj y U ⊔ Subgroup.zpowers a, x * w = w * x := by
    intro x hx w hw
    obtain ⟨s, hs, p, hp, rfl⟩ := hAdec x hx
    have hpa := hF₂a hp
    have hwP := hWP hw
    have hpW : p ∈ GLBConj y U ⊔ Subgroup.zpowers a := Subgroup.mem_sup_right hpa
    have hpw : p * w = w * p :=
      congrArg Subtype.val (hWel.1.is_comm.comm ⟨p, hpW⟩ ⟨w, hw⟩)
    calc s * p * w = s * (p * w) := by group
      _ = s * (w * p) := by rw [hpw]
      _ = (s * w) * p := by group
      _ = (w * s) * p := by rw [hcomm12 s hs w hwP]
      _ = w * (s * p) := by group
  have hAWel := isElemAbelian_sup F.hAel hWel hAWcomm
  have hWA : GLBConj y U ⊔ Subgroup.zpowers a ≤ A := by
    have := F.hsc.2.2 (A ⊔ (GLBConj y U ⊔ Subgroup.zpowers a)) le_top hAWel le_sup_left
    intro w hw
    rw [← this]
    exact Subgroup.mem_sup_right hw
  have hWa : GLBConj y U ⊔ Subgroup.zpowers a ≤ Subgroup.zpowers a := fun w hw =>
    F.inf_centBar_le (Subgroup.mem_inf.2 ⟨hWA hw, (Subgroup.mem_inf.1 (hWP hw)).2⟩)
  calc Nat.card U = Nat.card (GLBConj y U) := hU'card.symm
    _ ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le (le_trans le_sup_left hWa)
    _ = 3 := card_zpowers_three F.ha1 F.ha3

theorem Facts.rankOne (F : Facts E A K a) :
    ∀ U : Subgroup G, U ≤ centBar 3 (Cg a) K → IsElemAbelian 3 U → Nat.card U ≤ 3 :=
  F.main.2

theorem Facts.le_sup_zpowers (F : Facts E A K a) : A ≤ K ⊔ Subgroup.zpowers a := F.main.1

theorem Facts.card_inf_eq_nine (F : Facts E A K a) : Nat.card ↥(K ⊓ A) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hacomm : ∀ k ∈ K, a * k = k * a := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 (F.hKC hk)) a (Set.mem_singleton a)
  have haN : a ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_central hacomm
  refine Lemma1112b.card_inf_eq_nine F.hcardA F.hnotA F.hAN
    (Subgroup.zpowers_le.2 haN) F.le_sup_zpowers ?_
  rw [Nat.card_zpowers, orderOf_eq_prime F.ha3 F.ha1]
  norm_num

end RankOne

section Normal

variable {G : Type} [Group G] [Finite G] {E A K : Subgroup G} {a : G}

theorem mem_normalizer_of_mem_normalizer_subgroupOf {C S : Subgroup G} (hSC : S ≤ C) {c : ↥C}
    (hc : c ∈ Subgroup.normalizer ((S.subgroupOf C : Subgroup ↥C) : Set ↥C)) :
    (c : G) ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h1 := (Subgroup.mem_normalizer_iff.1 hc ⟨h, hSC hh⟩).1 (Subgroup.mem_subgroupOf.2 hh)
    exact Subgroup.mem_subgroupOf.1 h1
  · intro hh
    have hhC : c * h * c⁻¹ ∈ C := hSC hh
    have hhC' : h ∈ C := by
      have := C.mul_mem (C.mul_mem (C.inv_mem c.2) hhC) c.2
      simpa [mul_assoc] using this
    have h1 := (Subgroup.mem_normalizer_iff.1 hc ⟨h, hhC'⟩).2
      (Subgroup.mem_subgroupOf.2 (by simpa using hh))
    exact Subgroup.mem_subgroupOf.1 h1

theorem Facts.cg_le_normalizer (F : Facts E A K a) (hK : GLAPComponent 3 (Cg a) K) :
    Cg a ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  by_contra hgN
  set K' := GLBConj g⁻¹ K with hK'def
  have hX : GLBConj g⁻¹ (Cg a) = Cg a := by
    ext z
    rw [mem_glbConj]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using (Cg a).mul_mem ((Cg a).mul_mem hg hy) ((Cg a).inv_mem hg)
    · intro hz
      refine ⟨g⁻¹ * z * g, (Cg a).mul_mem ((Cg a).mul_mem ((Cg a).inv_mem hg) hz) hg, by group⟩
  have hK' : GLAPComponent 3 (Cg a) K' := by
    have := glaPComponent_gLBConj hK g⁻¹
    rwa [hX] at this
  have hne : K' ≠ K := by
    intro h
    apply hgN
    have h1 : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_gLBConj_eq.2 h
    simpa using (Subgroup.normalizer (K : Set G)).inv_mem h1
  have hKs := (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
    Nat.prime_three).1 hK
  have hK's := (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
    Nat.prime_three).1 hK'
  have hne' : K'.subgroupOf (Cg a) ≠ K.subgroupOf (Cg a) := by
    intro h
    apply hne
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_of_le_left hK'.1, inf_of_le_left hK.1] at this
  obtain ⟨hn1, hn2, hcomm, -⟩ :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation 3
      Nat.prime_three _ _ hK's.2 hKs.2).2 hne'
  have hK'C : K' ≤ centBar 3 (Cg a) K := by
    intro k' hk'
    have hk'C : k' ∈ Cg a := hK'.1 hk'
    have hk's : (⟨k', hk'C⟩ : ↥(Cg a)) ∈ K'.subgroupOf (Cg a) := Subgroup.mem_subgroupOf.2 hk'
    have hnorm : k' ∈ Subgroup.normalizer (K : Set G) :=
      mem_normalizer_of_mem_normalizer_subgroupOf (c := ⟨k', hk'C⟩) hK.1 (hn2 hk's)
    refine mem_centBar_of_comm hk'C hnorm fun p hp => ?_
    have hps : (⟨p, hK.1 hp⟩ : ↥(Cg a)) ∈ K.subgroupOf (Cg a) := Subgroup.mem_subgroupOf.2 hp
    have h1 := hcomm (Subgroup.commutator_mem_commutator hk's hps)
    obtain ⟨z, hz, hzc⟩ := (Subgroup.mem_inf.1 h1).2
    let e : ↥(K.subgroupOf (Cg a)) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hK.1
    have hez : e z ∈ GLAPPrimeCore 3 ↥K := by
      have := glaPPrimeCore_map_iso 3 e
      rw [← this]
      exact ⟨z, hz, rfl⟩
    refine ⟨e z, hez, ?_⟩
    have : ((e z : ↥K) : G) = ((z : ↥(Cg a)) : G) := rfl
    show ((e z : ↥K) : G) = k' * p * k'⁻¹ * p⁻¹
    rw [this]
    have h2 := congrArg (fun w : ↥(Cg a) => (w : G)) hzc
    simpa [commutatorElement_def] using h2
  have hKA9 := F.card_inf_eq_nine
  have hKAel : IsElemAbelian 3 (K ⊓ A) := Lemma1112.isElemAbelian_of_le F.hAel inf_le_right
  have hconj : GLBConj g⁻¹ (K ⊓ A) ≤ centBar 3 (Cg a) K :=
    (gLBConj_mono g⁻¹ (inf_le_left : K ⊓ A ≤ K)).trans hK'C
  have hle := F.rankOne _ hconj (isElemAbelian_glbConj hKAel g⁻¹)
  rw [card_glbConj, hKA9] at hle
  omega

end Normal

section SylowClaim

variable {G : Type} [Group G] [Finite G] {E A K : Subgroup G} {a : G}

@[expose] def InputAutL34Exp3 : Prop :=
  ∀ (X : Type) [Group X], IsLThreeFour X → ∀ φ : MulAut X, IsPGroup 3 (Subgroup.zpowers φ) →
    φ ^ 3 = 1

theorem Facts.mem_zpowers_of_cube (F : Facts E A K a) {w : G} (hwC : w ∈ centBar 3 (Cg a) K)
    (hw3 : w ^ 3 = 1) : w ∈ Subgroup.zpowers a := by
  have hwCg : w ∈ Cg a := (Subgroup.mem_inf.1 hwC).2
  have hwa : a * w = w * a := (Subgroup.mem_centralizer_iff.1 hwCg) a (Set.mem_singleton a)
  have hcomm : ∀ x ∈ Subgroup.zpowers w, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow (hwa.symm : Commute w a) i j).eq
  have hel : IsElemAbelian 3 (Subgroup.zpowers w ⊔ Subgroup.zpowers a) :=
    isElemAbelian_sup (Lemma1111.isElemAbelian_zpowers hw3) (Lemma1111.isElemAbelian_zpowers F.ha3) hcomm
  have hle : Subgroup.zpowers w ⊔ Subgroup.zpowers a ≤ centBar 3 (Cg a) K :=
    sup_le (Subgroup.zpowers_le.2 hwC) (Subgroup.zpowers_le.2 F.mem_centBar_a)
  have hcard := F.rankOne _ hle hel
  have heq : Subgroup.zpowers a = Subgroup.zpowers w ⊔ Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge le_sup_right
      (by rw [card_zpowers_three F.ha1 F.ha3]; exact hcard)
  rw [heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers w)

theorem Facts.isSylowIn_centBar (F : Facts E A K a) (hCN : Cg a ≤ Subgroup.normalizer (K : Set G))
    (hExp3 : InputAutL34Exp3) (hnc : ¬ IsPCentralIn 3 ⊤ a) :
    IsSylowIn 3 (centBar 3 (Cg a) K) (Subgroup.zpowers a) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C₁ := centBar 3 (Cg a) K with hC₁def
  have hC₁C : C₁ ≤ Cg a := inf_le_right
  have haC₁ : a ∈ C₁ := F.mem_centBar_a
  have hA3 : IsPGroup 3 ↥A := isPGroup_of_isElemAbelian F.hAel
  have hAC : A ≤ Cg a := fun x hx => Subgroup.mem_centralizer_iff.2 (fun g hg => by
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact F.hAc a F.ha x hx)
  obtain ⟨Q₀, hQ₀, hAQ₀⟩ := exists_isSylowIn_ge hAC hA3
  have haQ₀ : a ∈ Q₀ := hAQ₀ F.ha
  have hQ₀3 : IsPGroup 3 ↥Q₀ := hQ₀.2.1
  have hcube : ∀ x ∈ Q₀, x ^ 3 ∈ C₁ := by
    intro x hx
    have hxC : x ∈ Cg a := hQ₀.1 hx
    have hxN : x ∈ Subgroup.normalizer (K : Set G) := hCN hxC
    obtain ⟨t, ht⟩ := (IsPGroup.iff_orderOf.1 hQ₀3) ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at ht
    have hxt : x ^ (3 ^ t) = 1 := by rw [← ht]; exact pow_orderOf_eq_one x
    have hγt : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ (3 ^ t) = 1 :=
      Subtype.ext (by simpa using hxt)
    have hρt : (barAut 3 K ⟨x, hxN⟩) ^ (3 ^ t) = 1 := by rw [← map_pow, hγt, map_one]
    have hρ3 : (barAut 3 K ⟨x, hxN⟩) ^ 3 = 1 :=
      hExp3 (barOf 3 K) F.hL _ (isPGroup_zpowers_of_pow hρt)
    refine mem_centBar_iff'.2 ⟨(Cg a).pow_mem hxC 3, (Subgroup.normalizer (K : Set G)).pow_mem hxN 3, ?_⟩
    have : (⟨x ^ 3, (Subgroup.normalizer (K : Set G)).pow_mem hxN 3⟩ :
        ↥(Subgroup.normalizer (K : Set G))) = ⟨x, hxN⟩ ^ 3 := Subtype.ext rfl
    rw [this, map_pow]
    exact hρ3
  have hmain : Q₀ ⊓ C₁ ≤ Subgroup.zpowers a := by
    by_contra hnot
    obtain ⟨y, hyC₂, hya⟩ : ∃ y ∈ Q₀ ⊓ C₁, y ∉ Subgroup.zpowers a := by
      by_contra hcon
      exact hnot fun y hy => by_contra fun hyn => hcon ⟨y, hy, hyn⟩
    obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.1 hyC₂
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQ₀3) ⟨y, hyQ⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk1 : k ≤ 1 := by omega
      apply hya
      refine F.mem_zpowers_of_cube hyC ?_
      have hdvd : orderOf y ∣ 3 := by
        rw [hk]
        calc 3 ^ k ∣ 3 ^ 1 := pow_dvd_pow 3 hk1
          _ = 3 := by norm_num
      exact orderOf_dvd_iff_pow_eq_one.1 hdvd
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    set z : G := (y ^ 3) ^ (3 ^ k') with hz
    have hzy : z = y ^ (3 ^ (k' + 1)) := by
      rw [hz, ← pow_mul]
      congr 1
      rw [pow_succ]
      ring
    have hz3 : z ^ 3 = 1 := by
      rw [hzy, ← pow_mul, ← pow_succ, ← hk]
      exact pow_orderOf_eq_one y
    have hz1 : z ≠ 1 := by
      rw [hzy]
      refine pow_ne_one_of_lt_orderOf (by positivity) ?_
      rw [hk]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hzC₁ : z ∈ C₁ := by
      rw [hzy]
      exact C₁.pow_mem hyC _
    have hza : z ∈ Subgroup.zpowers a := F.mem_zpowers_of_cube hzC₁ hz3
    have hzc : Nat.card (Subgroup.zpowers z) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
    have haz : Subgroup.zpowers a = Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hza)
        (by rw [card_zpowers_three F.ha1 F.ha3, hzc]) |>.symm
    obtain ⟨m, hm⟩ : ∃ m : ℤ, z ^ m = a := Subgroup.mem_zpowers_iff.1 (by
      rw [← haz]; exact Subgroup.mem_zpowers a)
    have hnorm1 : ∀ g ∈ Subgroup.normalizer (Q₀ : Set G), g * a * g⁻¹ ∈ Subgroup.zpowers a := by
      intro g hg
      have hgyQ : g * y * g⁻¹ ∈ Q₀ := (Subgroup.mem_normalizer_iff.1 hg y).1 hyQ
      have hc3 : (g * y * g⁻¹) ^ 3 ∈ C₁ := hcube _ hgyQ
      have hc3Q : (g * y * g⁻¹) ^ 3 ∈ Q₀ := Q₀.pow_mem hgyQ 3
      have e : g * a * g⁻¹ = (((g * y * g⁻¹) ^ 3) ^ (3 ^ k')) ^ m := by
        rw [conj_pow, conj_pow, conj_zpow, ← hm]
      have hcm : g * a * g⁻¹ ∈ C₁ := by
        rw [e]
        exact C₁.zpow_mem (C₁.pow_mem hc3 _) m
      have hcm3 : (g * a * g⁻¹) ^ 3 = 1 := by
        rw [conj_pow, F.ha3]
        group
      exact F.mem_zpowers_of_cube hcm hcm3
    have hnorm : ∀ g ∈ Subgroup.normalizer (Q₀ : Set G),
        g ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        rw [← conj_zpow]
        exact Subgroup.zpow_mem _ (hnorm1 g hg) i
      · intro hw
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hw
        have h1 := hnorm1 g⁻¹ ((Subgroup.normalizer (Q₀ : Set G)).inv_mem hg)
        have : w = (g⁻¹ * a * g⁻¹⁻¹) ^ i := by
          rw [conj_zpow, hi]
          group
        rw [this]
        exact Subgroup.zpow_mem _ h1 i
    have hQtop := isSylowIn_top_of_normalizes hQ₀ F.ha1 F.ha3 hnorm
    exact hnc ⟨Q₀, hQtop, mem_centerOf_of_mem haQ₀ hQ₀.1⟩
  refine ⟨Subgroup.zpowers_le.2 haC₁, isPGroup_zpowers_of_pow (k := 1) (by simpa using F.ha3), ?_⟩
  intro R' hR'C hR'3 haR'
  have hR'Cg : R' ≤ Cg a := hR'C.trans hC₁C
  obtain ⟨y, hyC, hy⟩ := exists_conj_le_of_isSylowIn hQ₀ hR'Cg hR'3
  refine le_antisymm (fun r hr => ?_) haR'
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := hCN hyC
  have h1 : y⁻¹ * r * y ∈ C₁ := by
    have := conj_mem_centBar (X := Cg a) ((Subgroup.normalizer (K : Set G)).inv_mem hyN)
      ((Cg a).inv_mem hyC) (hR'C hr)
    simpa using this
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hmain (Subgroup.mem_inf.2 ⟨hy r hr, h1⟩))
  have hya : y * a = a * y := (Subgroup.mem_centralizer_iff.1 hyC) a (Set.mem_singleton a) |>.symm
  have : r = a ^ i := by
    have e : r = y * (y⁻¹ * r * y) * y⁻¹ := by group
    rw [e, ← hi]
    have hc : Commute y a := hya
    calc y * a ^ i * y⁻¹ = a ^ i * y * y⁻¹ := by rw [(hc.zpow_right i).eq]
      _ = a ^ i := by group
  rw [this]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) i

section Exp3

open CFSG.RankThree.PartTwo.KFacts.L34 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

theorem exp3_of_card_four {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4)
    (φ : MulAut (projectiveSL 3 k)) (hφ : IsPGroup 3 (Subgroup.zpowers φ)) : φ ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  set x := conjAut 3 k (LinearThreeFourOuter.diagGL u)
  set y := (MulAut.conj (bP : projectiveSL 3 k) : MulAut (projectiveSL 3 k))
  have h3 := LinearThreeFourOuter.units_pow_three hk u
  have hx3 : x ^ 3 = 1 := by
    rw [← map_pow, pow_three, LinearThreeFourOuter.diagGL_mul, LinearThreeFourOuter.diagGL_mul,
      ← pow_three, h3, LinearThreeFourOuter.diagGL_one, map_one]
  have hy3 : y ^ 3 = 1 := by
    rw [← map_pow, pow_three_of_mem_eZero hk bP_mem_eZero, map_one]
  have hab : aP u * bP = bP * aP u := commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero
  have hxa : x (aP u)⁻¹ = (aP u)⁻¹ := by rw [map_inv, conjAut_diagGL_aP]
  have hz : ⁅x, y⁆ = MulAut.conj (aP u)⁻¹ := by
    rw [commutatorElement_def, CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv,
      conjAut_diagGL_bP hk hu, ← map_inv, ← map_mul]
    congr 1
    calc bP * (aP u)⁻¹ * bP⁻¹ = bP * ((aP u)⁻¹ * bP⁻¹) := by group
      _ = bP * (bP⁻¹ * (aP u)⁻¹) := by
          rw [show (aP u)⁻¹ * bP⁻¹ = (bP * aP u)⁻¹ by group, ← hab]
          group
      _ = (aP u)⁻¹ := by group
  have hzx : Commute ⁅x, y⁆ x := by
    rw [hz]
    show MulAut.conj (aP u)⁻¹ * x = x * MulAut.conj (aP u)⁻¹
    have := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv x (aP u)⁻¹
    rw [hxa] at this
    calc MulAut.conj (aP u)⁻¹ * x = x * MulAut.conj (aP u)⁻¹ * x⁻¹ * x := by rw [this]
      _ = x * MulAut.conj (aP u)⁻¹ := by group
  have hzy : Commute ⁅x, y⁆ y := by
    rw [hz]
    show MulAut.conj (aP u)⁻¹ * MulAut.conj bP = MulAut.conj bP * MulAut.conj (aP u)⁻¹
    rw [← map_mul, ← map_mul]
    congr 1
    calc (aP u)⁻¹ * bP = (aP u)⁻¹ * (bP * aP u) * (aP u)⁻¹ := by group
      _ = (aP u)⁻¹ * (aP u * bP) * (aP u)⁻¹ := by rw [hab]
      _ = bP * (aP u)⁻¹ := by group
  have hz1 : ⁅x, y⁆ ≠ 1 := by
    rw [hz]
    intro h
    exact aP_ne_one hk hu (inv_eq_one.mp (conj_injective hk (h.trans (map_one _).symm)))
  have hL : (Nat.card (MulAut (projectiveSL 3 k))).factorization 3 = 3 := by
    rw [card_mulAut hk]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 241920 = 3 ^ 3 * 8960 by norm_num) (by norm_num)
  have hP : Nat.card (Subgroup.closure ({x, y} : Set (MulAut (projectiveSL 3 k)))) =
      3 ^ (Nat.card (MulAut (projectiveSL 3 k))).factorization 3 := by
    rw [hL, CFSG.RankThree.Asc83Table.ex27_card hx3 hy3 hzx hzy hz1]
    norm_num
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_map_conj_le hP hφ
  have hmem : (MulAut.conj g) φ ∈ Subgroup.closure ({x, y} : Set (MulAut (projectiveSL 3 k))) :=
    hg ⟨φ, Subgroup.mem_zpowers φ, rfl⟩
  have h1 := CFSG.RankThree.Asc83Table.pow_three_eq_one_of_mem hx3 hzx hzy hy3 hmem
  rw [← map_pow] at h1
  exact (MulAut.conj g).injective (h1.trans (map_one _).symm)

end Exp3

theorem inputAutL34Exp3_holds : InputAutL34Exp3 := by
  intro X _ hX φ hφ
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hX
  let e' : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)
  obtain ⟨t, ht⟩ := (IsPGroup.iff_orderOf.1 hφ) ⟨φ, Subgroup.mem_zpowers φ⟩
  rw [Subgroup.orderOf_mk] at ht
  have hφt : φ ^ (3 ^ t) = 1 := by rw [← ht]; exact pow_orderOf_eq_one φ
  have hψ : IsPGroup 3 (Subgroup.zpowers (MulAut.congr e' φ)) :=
    isPGroup_zpowers_of_pow (k := t) (by rw [← map_pow, hφt, map_one])
  have h3 := exp3_of_card_four hcard (MulAut.congr e' φ) hψ
  exact (MulAut.congr e').injective (by rw [map_pow, map_one]; exact h3)

end SylowClaim

section Extra

variable {G : Type} [Group G] [Finite G]

theorem card_sup_mul_card_inf_of_le_normalizer {K X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(K ⊔ X) * Nat.card ↥(K ⊓ X) = Nat.card ↥K * Nat.card ↥X := by
  have h1 := relIndex_sup_eq_of_le_normalizer hX
  have h2 : K.relIndex (K ⊔ X) * Nat.card ↥(K ⊓ (K ⊔ X)) = Nat.card ↥(K ⊔ X) :=
    Subgroup.relIndex_mul_card (H := K) (K := K ⊔ X)
  have h3 : K.relIndex X * Nat.card ↥(K ⊓ X) = Nat.card ↥X :=
    Subgroup.relIndex_mul_card (H := K) (K := X)
  have h4 : K ⊓ (K ⊔ X) = K := inf_eq_left.2 le_sup_left
  rw [h4] at h2
  rw [← h2, h1, ← h3]
  ring

theorem nonab27 {S : Subgroup G} {a : G} (hScard : Nat.card S = 27)
    (hSnonab : ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x) (haS : a ∈ S) (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1)
    (hSa : ∀ s ∈ S, s * a = a * s) :
    (∀ z ∈ S, (∀ s ∈ S, z * s = s * z) → z ∈ Subgroup.zpowers a) ∧
      ∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set c : ↥S := ⟨a, haS⟩ with hc
  have hc1 : c ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hc3 : c ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have hcc : c ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.2 (fun g => Subtype.ext (hSa g g.2))
  have hcard_c : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hcomm : ¬ ∀ x y : ↥S, x * y = y * x := by
    intro h
    obtain ⟨x, hx, y, hy, hne⟩ := hSnonab
    exact hne (congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩))
  constructor
  · intro z hz hzc
    by_contra hnot
    set zz : ↥S := ⟨z, hz⟩ with hzz
    have hzzc : zz ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.2 (fun g => Subtype.ext (hzc g g.2).symm)
    have hnotc : zz ∉ Subgroup.zpowers c := by
      intro h
      apply hnot
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 h
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨i, by simpa [hc, hzz] using congrArg Subtype.val hi⟩
    set Z' : Subgroup ↥S := Subgroup.zpowers c ⊔ Subgroup.zpowers zz with hZ'
    have hZ'c : Z' ≤ Subgroup.center ↥S :=
      sup_le (Subgroup.zpowers_le.2 hcc) (Subgroup.zpowers_le.2 hzzc)
    haveI : Z'.Normal := ⟨fun n hn g => by
      have := (Subgroup.mem_center_iff.1 (hZ'c hn)) g
      rwa [show g * n * g⁻¹ = n by rw [this]; group]⟩
    have h3dvd : 3 ∣ Nat.card Z' := by
      have := Subgroup.card_dvd_of_le (le_sup_left : Subgroup.zpowers c ≤ Z')
      rwa [hcard_c] at this
    have hdvd27 : Nat.card Z' ∣ 27 := by
      rw [← hScard]
      exact Subgroup.card_subgroup_dvd_card Z'
    have hne3 : Nat.card Z' ≠ 3 := by
      intro h3
      apply hnotc
      have heq : Subgroup.zpowers c = Z' :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3, hcard_c])
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers zz)
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
    have hcyc : IsCyclic (↥S ⧸ Z') := by
      have hdiv : Nat.card Z' ∣ 27 := hdvd27
      have hcases : Nat.card Z' = 3 ∨ Nat.card Z' = 9 ∨ Nat.card Z' = 27 := by
        have hmem := Nat.mem_divisors.2 ⟨hdiv, by norm_num⟩
        rw [show Nat.divisors 27 = {1, 3, 9, 27} from by decide] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h | h | h
        · rw [h] at h3dvd; norm_num at h3dvd
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      rcases hcases with h | h | h
      · exact absurd h hne3
      · have : Nat.card (↥S ⧸ Z') = 3 := by
          rw [hScard, h] at hq
          omega
        exact isCyclic_of_prime_card this
      · have : Nat.card (↥S ⧸ Z') = 1 := by
          rw [hScard, h] at hq
          omega
        haveI : Subsingleton (↥S ⧸ Z') := (Nat.card_eq_one_iff_unique.1 this).1
        infer_instance
    exact hcomm (commutative_of_cyclic_center_quotient (QuotientGroup.mk' Z')
      (by rw [QuotientGroup.ker_mk']; exact hZ'c))
  · intro x hx y hy
    set Zc : Subgroup ↥S := Subgroup.zpowers c with hZc
    haveI : Zc.Normal := ⟨fun n hn g => by
      have hnc : n ∈ Subgroup.center ↥S := by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
        exact Subgroup.zpow_mem _ hcc i
      have := (Subgroup.mem_center_iff.1 hnc) g
      rwa [show g * n * g⁻¹ = n by rw [this]; group]⟩
    have hq : Nat.card (↥S ⧸ Zc) = 3 ^ 2 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup Zc
      rw [hScard, hcard_c] at this
      omega
    haveI : IsMulCommutative (↥S ⧸ Zc) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
    have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥S) : ↥S ⧸ Zc) * QuotientGroup.mk ⟨y, hy⟩ =
        QuotientGroup.mk ⟨y, hy⟩ * QuotientGroup.mk ⟨x, hx⟩ := mul_comm' _ _
    have h2 : (⟨x, hx⟩ : ↥S) * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥S)⁻¹ * (⟨y, hy⟩ : ↥S)⁻¹ ∈ Zc := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv]
      set u : ↥S ⧸ Zc := QuotientGroup.mk ⟨x, hx⟩
      set v : ↥S ⧸ Zc := QuotientGroup.mk ⟨y, hy⟩
      calc u * v * u⁻¹ * v⁻¹ = v * u * u⁻¹ * v⁻¹ := by rw [h1]
        _ = 1 := by group
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 h2
    have := congrArg Subtype.val hi
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨i, by simpa using this⟩

theorem extraspecial_of_conf {A S F₂ : Subgroup G} {a : G}
    (hAel : IsElemAbelian 3 A) (hsc : IsSCp 3 ⊤ A) (hcardA : Nat.card A = 27)
    (ha : a ∈ A) (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1)
    (hScard : Nat.card S = 27) (hSexp : ∀ x ∈ S, x ^ 3 = 1)
    (hSnonab : ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x)
    (haS : a ∈ S) (hSa : ∀ s ∈ S, s * a = a * s)
    (haF : a ∈ F₂) (hFa : ∀ p ∈ F₂, p * a = a * p)
    (hcomm : ∀ s ∈ S, ∀ p ∈ F₂, s * p = p * s)
    (hSF : ∀ z ∈ S, z ∈ F₂ → z ∈ Subgroup.zpowers a)
    (hdec : ∀ x ∈ A, ∃ s ∈ S, ∃ p ∈ F₂, x = s * p)
    (hF₂dec : ∀ p ∈ F₂, ∃ s ∈ S, s * p ∈ A)
    (hF₂3 : ∀ p ∈ F₂, p ^ 3 = 1)
    (hF₂A : ∀ p ∈ F₂, p ∈ A → p ∈ Subgroup.zpowers a) :
    A ≤ S ⊔ F₂ ∧ Lemma1111.IsExtraspecialFive (S ⊔ F₂) a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZS, hSc⟩ := nonab27 hScard hSnonab haS ha1 ha3 hSa
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have haSF : Subgroup.zpowers a ≤ S := Subgroup.zpowers_le.2 haS
  have hASF : A ≤ S ⊔ F₂ := fun x hx => by
    obtain ⟨s, hs, p, hp, rfl⟩ := hdec x hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hp)
  have hF₂SA : F₂ ≤ S ⊔ A := fun p hp => by
    obtain ⟨s, hs, hsp⟩ := hF₂dec p hp
    have : p = s⁻¹ * (s * p) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hs)) (Subgroup.mem_sup_right hsp)
  have hFeq : S ⊔ F₂ = S ⊔ A :=
    le_antisymm (sup_le le_sup_left hF₂SA) (sup_le le_sup_left hASF)
  have hAnorm : A ≤ Subgroup.normalizer (S : Set G) := by
    intro x hx
    obtain ⟨s, hs, p, hp, rfl⟩ := hdec x hx
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have e : s * p * t * (s * p)⁻¹ = s * t * s⁻¹ := by
        have h1 : p * t = t * p := (hcomm t ht p hp).symm
        calc s * p * t * (s * p)⁻¹ = s * (p * t) * p⁻¹ * s⁻¹ := by group
          _ = s * (t * p) * p⁻¹ * s⁻¹ := by rw [h1]
          _ = s * t * s⁻¹ := by group
      rw [e]
      exact S.mul_mem (S.mul_mem hs ht) (S.inv_mem hs)
    · intro ht
      have hw : s * p * t * (s * p)⁻¹ ∈ S := ht
      have e : t = p⁻¹ * (s⁻¹ * (s * p * t * (s * p)⁻¹) * s) * p := by group
      have hc : p⁻¹ * (s⁻¹ * (s * p * t * (s * p)⁻¹) * s) = (s⁻¹ * (s * p * t * (s * p)⁻¹) * s) * p⁻¹ := by
        have := hcomm (s⁻¹ * (s * p * t * (s * p)⁻¹) * s) (S.mul_mem (S.mul_mem (S.inv_mem hs) hw) hs)
          p⁻¹ (F₂.inv_mem hp)
        exact this.symm
      rw [e, hc]
      simpa using S.mul_mem (S.mul_mem (S.inv_mem hs) hw) hs
  have hWcard : Nat.card ↥(A ⊓ S) = 3 := by
    have hzW : Subgroup.zpowers a ≤ A ⊓ S := Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨ha, haS⟩)
    have h3 : 3 ∣ Nat.card ↥(A ⊓ S) := by
      have := Subgroup.card_dvd_of_le hzW
      rwa [card_zpowers_three ha1 ha3] at this
    have hdvd : Nat.card ↥(A ⊓ S) ∣ 27 := by
      rw [← hcardA]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hcases : Nat.card ↥(A ⊓ S) = 3 ∨ Nat.card ↥(A ⊓ S) = 9 ∨ Nat.card ↥(A ⊓ S) = 27 := by
      have hmem := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
      rw [show Nat.divisors 27 = {1, 3, 9, 27} from by decide] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h | h
      · rw [h] at h3; norm_num at h3
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    rcases hcases with h | h | h
    · exact h
    · exfalso
      have hWel : IsElemAbelian 3 (A ⊓ S) := Lemma1111.isElemAbelian_of_le hAel inf_le_left
      have hAW : A ≤ A ⊓ S := by
        intro x hx
        obtain ⟨s, hs, p, hp, rfl⟩ := hdec x hx
        have hsW : s ∈ A ⊓ S := by
          by_contra hsW
          have hcs : ∀ w ∈ A ⊓ S, w * s = s * w := by
            intro w hw
            have hwS : w ∈ S := (Subgroup.mem_inf.1 hw).2
            have h1 := hAc (s * p) hx w (Subgroup.mem_inf.1 hw).1
            have hpw : p * w = w * p := (hcomm w hwS p hp).symm
            have h2 : s * w * p = w * s * p := by
              calc s * w * p = s * (w * p) := by group
                _ = s * (p * w) := by rw [hpw]
                _ = s * p * w := by group
                _ = w * (s * p) := h1
                _ = w * s * p := by group
            exact (mul_right_cancel h2).symm
          have hV := Lemma1111.isElemAbelian_sup hWel
            (Lemma1111.isElemAbelian_zpowers (hSexp s hs)) (fun w hw z hz => by
              obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
              exact (Commute.zpow_right (hcs w hw : Commute w s) i).eq)
          have hVS : A ⊓ S ⊔ Subgroup.zpowers s ≤ S :=
            sup_le inf_le_right (Subgroup.zpowers_le.2 hs)
          have hd9 : 9 ∣ Nat.card ↥(A ⊓ S ⊔ Subgroup.zpowers s) := by
            have := Subgroup.card_dvd_of_le (le_sup_left : A ⊓ S ≤ A ⊓ S ⊔ Subgroup.zpowers s)
            rwa [h] at this
          have hd27 : Nat.card ↥(A ⊓ S ⊔ Subgroup.zpowers s) ∣ 27 := by
            rw [← hScard]
            exact Subgroup.card_dvd_of_le hVS
          have hne9 : Nat.card ↥(A ⊓ S ⊔ Subgroup.zpowers s) ≠ 9 := by
            intro h9
            apply hsW
            have heq : A ⊓ S = A ⊓ S ⊔ Subgroup.zpowers s :=
              Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h9, h])
            rw [heq]
            exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
          have h27 : Nat.card ↥(A ⊓ S ⊔ Subgroup.zpowers s) = 27 := by
            have hmem := Nat.mem_divisors.2 ⟨hd27, by norm_num⟩
            rw [show Nat.divisors 27 = {1, 3, 9, 27} from by decide] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h' | h' | h'
            · rw [h'] at hd9; norm_num at hd9
            · rw [h'] at hd9; norm_num at hd9
            · exact absurd h' hne9
            · exact h'
          have hVeq : A ⊓ S ⊔ Subgroup.zpowers s = S :=
            Subgroup.eq_of_le_of_card_ge hVS (by rw [h27, hScard])
          obtain ⟨x₁, hx₁, y₁, hy₁, hne⟩ := hSnonab
          apply hne
          rw [← hVeq] at hx₁ hy₁
          exact congrArg Subtype.val (hV.1.is_comm.comm ⟨x₁, hx₁⟩ ⟨y₁, hy₁⟩)
        have hsA : s ∈ A := (Subgroup.mem_inf.1 hsW).1
        have hpA : p ∈ A := by
          have := A.mul_mem (A.inv_mem hsA) hx
          simpa using this
        have hpa : p ∈ Subgroup.zpowers a := hF₂A p hp hpA
        exact Subgroup.mem_inf.2 ⟨hx, S.mul_mem (Subgroup.mem_inf.1 hsW).2 (haSF hpa)⟩
      have := Subgroup.card_le_of_le hAW
      rw [h, hcardA] at this
      omega
    · exfalso
      have heq : A ⊓ S = S := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hScard])
      obtain ⟨x₁, hx₁, y₁, hy₁, hne⟩ := hSnonab
      have hSA : S ≤ A := by
        intro z hz
        have : z ∈ A ⊓ S := by rw [heq]; exact hz
        exact (Subgroup.mem_inf.1 this).1
      exact hne (hAc x₁ (hSA hx₁) y₁ (hSA hy₁))
  have hFcard : Nat.card ↥(S ⊔ F₂) = 3 ^ 5 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hAnorm
    rw [inf_comm, hWcard, hScard, hcardA] at h
    rw [hFeq]
    show Nat.card ↥(S ⊔ A) = 243
    omega
  have hFexp : ∀ f ∈ S ⊔ F₂, f ^ 3 = 1 := by
    intro f hf
    obtain ⟨s, hs, p, hp, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hf
    rw [Commute.mul_pow (show Commute s p from hcomm s hs p hp) 3, hSexp s hs, hF₂3 p hp, one_mul]
  have hFc : ∀ p ∈ F₂, ∀ p' ∈ F₂, p * p' * p⁻¹ * p'⁻¹ ∈ Subgroup.zpowers a := by
    intro p hp p' hp'
    obtain ⟨s, hs, hsp⟩ := hF₂dec p hp
    obtain ⟨s', hs', hsp'⟩ := hF₂dec p' hp'
    have hA' := hAc _ hsp _ hsp'
    have e : s' * s * (p' * p) = s * s' * (p * p') := by
      calc s' * s * (p' * p) = (s' * p') * (s * p) := by
            calc s' * s * (p' * p) = s' * (s * p') * p := by group
              _ = s' * (p' * s) * p := by rw [hcomm s hs p' hp']
              _ = (s' * p') * (s * p) := by group
        _ = (s * p) * (s' * p') := hA'.symm
        _ = s * s' * (p * p') := by
            calc (s * p) * (s' * p') = s * (p * s') * p' := by group
              _ = s * (s' * p) * p' := by rw [(hcomm s' hs' p hp).symm]
              _ = s * s' * (p * p') := by group
    have hw : (s * s')⁻¹ * (s' * s) = (p * p') * (p' * p)⁻¹ := by
      calc (s * s')⁻¹ * (s' * s) = (s * s')⁻¹ * (s' * s * (p' * p)) * (p * p')⁻¹ * (p * p')
            * (p' * p)⁻¹ := by group
        _ = (s * s')⁻¹ * (s * s' * (p * p')) * (p * p')⁻¹ * (p * p') * (p' * p)⁻¹ := by rw [e]
        _ = (p * p') * (p' * p)⁻¹ := by group
    have hS' : (s * s')⁻¹ * (s' * s) ∈ S := S.mul_mem (S.inv_mem (S.mul_mem hs hs')) (S.mul_mem hs' hs)
    have hF' : (p * p') * (p' * p)⁻¹ ∈ F₂ :=
      F₂.mul_mem (F₂.mul_mem hp hp') (F₂.inv_mem (F₂.mul_mem hp' hp))
    have h1 : (p * p') * (p' * p)⁻¹ ∈ S := by rw [← hw]; exact hS'
    have e2 : p * p' * p⁻¹ * p'⁻¹ = (p * p') * (p' * p)⁻¹ := by group
    rw [e2]
    exact hSF _ h1 hF'
  have hZcS : ∀ z ∈ Subgroup.zpowers a, ∀ s ∈ S, s * z = z * s := by
    intro z hz s hs
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ((show Commute s a from hSa s hs).zpow_right i).eq
  have hZcF : ∀ z ∈ Subgroup.zpowers a, ∀ p ∈ F₂, p * z = z * p := by
    intro z hz p hp
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ((show Commute p a from hFa p hp).zpow_right i).eq
  have haF₂ : Subgroup.zpowers a ≤ F₂ := Subgroup.zpowers_le.2 haF
  have hcen : centerOf (S ⊔ F₂) = Subgroup.zpowers a := by
    apply le_antisymm
    · intro z hz
      obtain ⟨hzF, hzc⟩ := (Lemma1111.mem_centerOf_iff _ z).1 hz
      obtain ⟨s, hs, p, hp, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hzF
      have hsZ : s ∈ Subgroup.zpowers a := by
        apply hZS s hs
        intro t ht
        have h1 := hzc t (Subgroup.mem_sup_left ht)
        have h2 : t * p = p * t := hcomm t ht p hp
        have h3 : t * s * p = s * t * p := by
          calc t * s * p = t * (s * p) := by group
            _ = s * p * t := h1
            _ = s * (p * t) := by group
            _ = s * (t * p) := by rw [h2]
            _ = s * t * p := by group
        exact (mul_right_cancel h3).symm
      have hz₂ : s * p ∈ F₂ := F₂.mul_mem (haF₂ hsZ) hp
      have hz3 : (s * p) ^ 3 = 1 := hF₂3 _ hz₂
      have hel := Lemma1111.isElemAbelian_sup hAel (Lemma1111.isElemAbelian_zpowers hz3)
        (fun w hw y hy => by
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
          exact ((show Commute w (s * p) from hzc w (hASF hw)).zpow_right i).eq)
      have heq := hsc.2.2 (A ⊔ Subgroup.zpowers (s * p)) le_top hel le_sup_left
      have hzA : s * p ∈ A := by
        have : s * p ∈ A ⊔ Subgroup.zpowers (s * p) := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
        rwa [heq] at this
      exact hF₂A _ hz₂ hzA
    · intro z hz
      rw [Lemma1111.mem_centerOf_iff]
      refine ⟨Subgroup.mem_sup_left (haSF hz), fun f hf => ?_⟩
      obtain ⟨s, hs, p, hp, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hf
      have hsz : s * z = z * s := hZcS z hz s hs
      have hpz : p * z = z * p := hZcF z hz p hp
      calc s * p * z = s * (p * z) := by group
        _ = s * (z * p) := by rw [hpz]
        _ = (s * z) * p := by group
        _ = (z * s) * p := by rw [hsz]
        _ = z * (s * p) := by group
  have hder : ⁅S ⊔ F₂, S ⊔ F₂⁆ = Subgroup.zpowers a := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro f₁ hf₁ f₂ hf₂
      obtain ⟨s₁, hs₁, p₁, hp₁, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hf₁
      obtain ⟨s₂, hs₂, p₂, hp₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hf₂
      rw [commutatorElement_def]
      have e : s₁ * p₁ * (s₂ * p₂) * (s₁ * p₁)⁻¹ * (s₂ * p₂)⁻¹ =
          (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) * (p₁ * p₂ * p₁⁻¹ * p₂⁻¹) := by
        have h1 : p₁ * s₂ = s₂ * p₁ := (hcomm s₂ hs₂ p₁ hp₁).symm
        have h2 : (p₁ * p₂ * p₁⁻¹) * s₁⁻¹ = s₁⁻¹ * (p₁ * p₂ * p₁⁻¹) :=
          (hcomm s₁⁻¹ (S.inv_mem hs₁) _ (F₂.mul_mem (F₂.mul_mem hp₁ hp₂) (F₂.inv_mem hp₁))).symm
        have h3 : (p₁ * p₂ * p₁⁻¹ * p₂⁻¹) * s₂⁻¹ = s₂⁻¹ * (p₁ * p₂ * p₁⁻¹ * p₂⁻¹) :=
          (hcomm s₂⁻¹ (S.inv_mem hs₂) _ (F₂.mul_mem (F₂.mul_mem (F₂.mul_mem hp₁ hp₂)
            (F₂.inv_mem hp₁)) (F₂.inv_mem hp₂))).symm
        calc s₁ * p₁ * (s₂ * p₂) * (s₁ * p₁)⁻¹ * (s₂ * p₂)⁻¹
            = s₁ * (p₁ * s₂) * p₂ * p₁⁻¹ * s₁⁻¹ * p₂⁻¹ * s₂⁻¹ := by group
          _ = s₁ * (s₂ * p₁) * p₂ * p₁⁻¹ * s₁⁻¹ * p₂⁻¹ * s₂⁻¹ := by rw [h1]
          _ = s₁ * s₂ * ((p₁ * p₂ * p₁⁻¹) * s₁⁻¹) * p₂⁻¹ * s₂⁻¹ := by group
          _ = s₁ * s₂ * (s₁⁻¹ * (p₁ * p₂ * p₁⁻¹)) * p₂⁻¹ * s₂⁻¹ := by rw [h2]
          _ = s₁ * s₂ * s₁⁻¹ * ((p₁ * p₂ * p₁⁻¹ * p₂⁻¹) * s₂⁻¹) := by group
          _ = s₁ * s₂ * s₁⁻¹ * (s₂⁻¹ * (p₁ * p₂ * p₁⁻¹ * p₂⁻¹)) := by rw [h3]
          _ = (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) * (p₁ * p₂ * p₁⁻¹ * p₂⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (hSc s₁ hs₁ s₂ hs₂) (hFc p₁ hp₁ p₂ hp₂)
    · obtain ⟨x, hx, y, hy, hne⟩ := hSnonab
      have hc : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers a := hSc x hx y hy
      have hc1 : x * y * x⁻¹ * y⁻¹ ≠ 1 := by
        intro h
        apply hne
        calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
          _ = y * x := by rw [h, one_mul]
      have hc3 : (x * y * x⁻¹ * y⁻¹) ^ 3 = 1 := (Lemma1111.isElemAbelian_zpowers ha3).2 _ hc
      have heq' : Subgroup.zpowers (x * y * x⁻¹ * y⁻¹) = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hc)
          (by rw [card_zpowers_three ha1 ha3, card_zpowers_three hc1 hc3])
      have hmem : x * y * x⁻¹ * y⁻¹ ∈ ⁅S ⊔ F₂, S ⊔ F₂⁆ := by
        have := Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hx : x ∈ S ⊔ F₂)
          (Subgroup.mem_sup_left hy : y ∈ S ⊔ F₂)
        rwa [commutatorElement_def] at this
      rw [← heq']
      exact Subgroup.zpowers_le.2 hmem
  refine ⟨hASF, ?_⟩
  unfold Lemma1111.IsExtraspecialFive
  exact ⟨hFcard, hFexp, ha1, hcen, hder⟩

end Extra

section SLSylow

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (card_slThreeFour card_center_slThreeFour)

theorem piK_inj {K S : Subgroup G} (hS3 : IsPGroup 3 ↥S) {s t : G} (hs : s ∈ S) (ht : t ∈ S)
    (hsK : s ∈ K) (htK : t ∈ K)
    (h : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨s, hsK⟩ =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨t, htK⟩) : s = t := by
  have h1 := (CFSG.HardMathSupport.Solomon.LocalBalance.mk_eq_iff_glaPPrimeCoreOf (p := 3) (C := K)
    ⟨s, hsK⟩ ⟨t, htK⟩).1 h
  have h3 : s⁻¹ * t ∈ S := S.mul_mem (S.inv_mem hs) ht
  exact inv_mul_eq_one.1 (eq_one_of_mem_pPrimeCoreOf hS3 h1 h3)

theorem sylow_of_isSLThreeFour {X K S : Subgroup G} (hK : GLAPComponent 3 X K)
    (hSL : IsSLThreeFour (barOf 3 K))
    (hSyl : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.InputSL34Sylow)
    (hS : IsSylowIn 3 K S) :
    Nat.card S = 27 ∧ (∀ x ∈ S, x ^ 3 = 1) ∧ (∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x) ∧
      ∃ z ∈ S, ∃ hzK : z ∈ K, QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨z, hzK⟩ ≠ 1 ∧
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨z, hzK⟩ ∈ Subgroup.center (barOf 3 K) ∧
        ∀ w ∈ S, ∀ hwK : w ∈ K,
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨w, hwK⟩ ∈ Subgroup.center (barOf 3 K) →
            w ∈ Subgroup.zpowers z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : ↥K →* barOf 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcard60 : Nat.card (barOf 3 K) = 60480 := card_slThreeFour hSL
  have hZcard : Nat.card (Subgroup.center (barOf 3 K)) = 3 := card_center_slThreeFour hSL
  have hnt : Nontrivial (barOf 3 K) := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard60]; norm_num)
  have hq := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.isQuasisimple_barOf
    Nat.prime_three hK hnt
  have hS3 : IsPGroup 3 ↥S := hS.2.1
  have hS' := isSylowIn_top_subgroupOf hS
  let S1 : Sylow 3 ↥K := ⟨S.subgroupOf K, hS'.2.1, fun {Q} hQ hSQ => hS'.2.2 Q le_top hQ hSQ⟩
  let S2 : Sylow 3 (barOf 3 K) := S1.mapSurjective hπs
  have hS2 : (S2 : Subgroup (barOf 3 K)) = (S.subgroupOf K).map π := rfl
  have hS2card : Nat.card (S2 : Subgroup (barOf 3 K)) = 27 := by
    rw [Sylow.card_eq_multiplicity, hcard60,
      CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
        (show 60480 = 3 ^ 3 * 2240 by norm_num) (by norm_num)]
    norm_num
  have hinj : ∀ s t : G, ∀ hs : s ∈ S, ∀ ht : t ∈ S, ∀ hsK : s ∈ K, ∀ htK : t ∈ K,
      π ⟨s, hsK⟩ = π ⟨t, htK⟩ → s = t := fun s t hs ht hsK htK h => piK_inj hS3 hs ht hsK htK h
  have hScard : Nat.card S = 27 := by
    rw [← hS2card, hS2]
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : ↥S => (⟨π ⟨x, hS.1 x.2⟩, Subgroup.mem_map.2 ⟨⟨x, hS.1 x.2⟩, Subgroup.mem_subgroupOf.2 x.2,
        rfl⟩⟩ : ↥((S.subgroupOf K).map π))) ⟨?_, ?_⟩)
    · intro x y hxy
      exact Subtype.ext (hinj x y x.2 y.2 (hS.1 x.2) (hS.1 y.2) (congrArg Subtype.val hxy))
    · rintro ⟨_, ⟨k, hk, rfl⟩⟩
      exact ⟨⟨k, Subgroup.mem_subgroupOf.1 hk⟩, Subtype.ext rfl⟩
  have hZ3 : IsPGroup 3 (Subgroup.center (barOf 3 K)) :=
    IsPGroup.of_card (n := 1) (by rw [hZcard]; norm_num)
  have hZle : Subgroup.center (barOf 3 K) ≤ (S2 : Subgroup (barOf 3 K)) := hZ3.le_sylow_of_normal S2
  have hZ1 : Subgroup.center (barOf 3 K) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZcard
    omega
  obtain ⟨hnonab, hexp⟩ := hSyl (barOf 3 K) hq hZ3 hZ1
    (CFSG.HardMathSupport.Solomon.UniquenessMaximal.EvenSL.isLThreeFour_quot_center_of_isSLThreeFour hSL)
    (S2 : Subgroup (barOf 3 K)) S2.isPGroup' hZle (by rw [hS2card, hZcard])
  refine ⟨hScard, ?_, ?_, ?_⟩
  ·
    intro x hx
    have hxK : x ∈ K := hS.1 hx
    have h1 : π ⟨x, hxK⟩ ∈ (S2 : Subgroup (barOf 3 K)) :=
      Subgroup.mem_map.2 ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    have h2 := hexp _ h1
    have h3 : (⟨x, hxK⟩ : ↥K) ^ 3 ∈ GLAPPrimeCore 3 ↥K := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      show π ((⟨x, hxK⟩ : ↥K) ^ 3) = 1
      rw [map_pow]
      exact h2
    have h4 := (CFSG.HardMathSupport.Solomon.LocalBalance.mem_glaPPrimeCoreOf_iff
      ((⟨x, hxK⟩ : ↥K) ^ 3)).2 h3
    exact eq_one_of_mem_pPrimeCoreOf hS3 (by simpa using h4) (S.pow_mem hx 3)
  ·
    obtain ⟨u, hu, v, hv, huv⟩ := hnonab
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
    obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.1 hv
    refine ⟨u', Subgroup.mem_subgroupOf.1 hu', v', Subgroup.mem_subgroupOf.1 hv', fun h => huv ?_⟩
    have h' : u' * v' = v' * u' := Subtype.ext h
    rw [← map_mul, ← map_mul, h']
  ·
    obtain ⟨z0, hz01⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ1
    obtain ⟨z1, hz1, hz1π⟩ := Subgroup.mem_map.1 (hZle z0.2)
    have hz1S : (z1 : G) ∈ S := Subgroup.mem_subgroupOf.1 hz1
    have hπz1 : π z1 = z0 := hz1π
    have hz0c : (z0 : barOf 3 K) ∈ Subgroup.center (barOf 3 K) := z0.2
    have hz03 : (z0 : barOf 3 K) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := Subgroup.center (barOf 3 K)) (x := z0)
      rw [hZcard] at this
      exact congrArg Subtype.val this
    have hz0ne : (z0 : barOf 3 K) ≠ 1 := fun h => hz01 (Subtype.ext h)
    have hzp : Subgroup.zpowers (z0 : barOf 3 K) = Subgroup.center (barOf 3 K) := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz0c) ?_
      rw [hZcard, Nat.card_zpowers, orderOf_eq_prime hz03 hz0ne]
    refine ⟨z1, hz1S, z1.2, ?_, ?_, ?_⟩
    · show π z1 ≠ 1
      rw [hπz1]
      exact hz0ne
    · show π z1 ∈ _
      rw [hπz1]
      exact hz0c
    · intro w hw hwK hwc
      have hwc' : π ⟨w, hwK⟩ ∈ Subgroup.zpowers (z0 : barOf 3 K) := by rw [hzp]; exact hwc
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hwc'
      have hzi : π ⟨(z1 : G) ^ i, by exact Subgroup.zpow_mem _ z1.2 i⟩ = π ⟨w, hwK⟩ := by
        have : (⟨(z1 : G) ^ i, Subgroup.zpow_mem _ z1.2 i⟩ : ↥K) = z1 ^ i := Subtype.ext (by simp)
        rw [this, map_zpow, hπz1, hi]
      have := hinj _ _ (S.zpow_mem hz1S i) hw (Subgroup.zpow_mem _ z1.2 i) hwK hzi
      rw [← this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) i

@[expose] def InputSL34SylowCent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSLThreeFour Y → ∀ P : Subgroup Y, IsPGroup 3 ↥P →
    Subgroup.center Y ≤ P → Nat.card P = 27 → ∀ y : Y, (∀ x ∈ P, y * x = x * y) →
      y ∈ Subgroup.center Y

theorem sylow_image_facts {K S : Subgroup G} (hSL : IsSLThreeFour (barOf 3 K))
    (hS : IsSylowIn 3 K S) :
    IsPGroup 3 ↥((S.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K))) ∧
      Subgroup.center (barOf 3 K) ≤ (S.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) ∧
      Nat.card ↥((S.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K))) = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : ↥K →* barOf 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcard60 : Nat.card (barOf 3 K) = 60480 := card_slThreeFour hSL
  have hZcard : Nat.card (Subgroup.center (barOf 3 K)) = 3 := card_center_slThreeFour hSL
  have hS' := isSylowIn_top_subgroupOf hS
  let S1 : Sylow 3 ↥K := ⟨S.subgroupOf K, hS'.2.1, fun {Q} hQ hSQ => hS'.2.2 Q le_top hQ hSQ⟩
  let S2 : Sylow 3 (barOf 3 K) := S1.mapSurjective hπs
  have hS2 : (S2 : Subgroup (barOf 3 K)) = (S.subgroupOf K).map π := rfl
  have hS2card : Nat.card (S2 : Subgroup (barOf 3 K)) = 27 := by
    rw [Sylow.card_eq_multiplicity, hcard60,
      CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
        (show 60480 = 3 ^ 3 * 2240 by norm_num) (by norm_num)]
    norm_num
  have hZ3 : IsPGroup 3 (Subgroup.center (barOf 3 K)) :=
    IsPGroup.of_card (n := 1) (by rw [hZcard]; norm_num)
  have hZle : Subgroup.center (barOf 3 K) ≤ (S2 : Subgroup (barOf 3 K)) := hZ3.le_sylow_of_normal S2
  rw [← hS2]
  exact ⟨S2.isPGroup', hZle, hS2card⟩

end SLSylow

section SLConf

variable {G : Type} [Group G] [Finite G] {E A K : Subgroup G} {a : G}

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (card_center_slThreeFour)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut_mk)

theorem FactsSL.exists_conf (F : FactsSL E A K a) (hK : GLAPComponent 3 (Cg a) K)
    (hSyl : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.InputSL34Sylow) :
    ∃ S F₂ : Subgroup G, Nat.card S = 27 ∧ (∀ x ∈ S, x ^ 3 = 1) ∧
      (∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x) ∧ a ∈ S ∧ (∀ s ∈ S, s * a = a * s) ∧ a ∈ F₂ ∧
      (∀ p ∈ F₂, p * a = a * p) ∧ (∀ s ∈ S, ∀ p ∈ F₂, s * p = p * s) ∧
      (∀ z ∈ S, z ∈ F₂ → z ∈ Subgroup.zpowers a) ∧ (∀ x ∈ A, ∃ s ∈ S, ∃ p ∈ F₂, x = s * p) ∧
      (∀ p ∈ F₂, ∃ s ∈ S, s * p ∈ A) ∧ (∀ p ∈ F₂, p ^ 3 = 1) ∧
      (∀ p ∈ F₂, p ∈ A → p ∈ Subgroup.zpowers a) ∧ IsSylowIn 3 K S ∧
      ∃ Q : Subgroup G, IsSylowIn 3 (Cg a) Q ∧ S ≤ Q ∧ A ≤ Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ3 : ∀ z ∈ Subgroup.center (barOf 3 K), z ^ 3 = 1 := by
    intro z hz
    have := pow_card_eq_one' (G := Subgroup.center (barOf 3 K)) (x := ⟨z, hz⟩)
    rw [card_center_slThreeFour F.hSL] at this
    exact congrArg Subtype.val this
  set C₁ := centBar 3 (Cg a) K with hC₁def
  set Y := K ⊔ C₁ with hYdef
  have hC₁N : C₁ ≤ Subgroup.normalizer (K : Set G) := centBar_le_normalizer 3 _ K
  have hC₁C : C₁ ≤ Cg a := inf_le_right
  have hKY : K ≤ Y := le_sup_left
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hC₁N
  have hYC : Y ≤ Cg a := sup_le F.hKC hC₁C
  have hKnorm : ∀ y ∈ Y, ∀ n ∈ K, y * n * y⁻¹ ∈ K := fun y hy n hn =>
    (Subgroup.mem_normalizer_iff.1 (hYN hy) n).1 hn
  have hA3 : IsPGroup 3 ↥A := isPGroup_of_isElemAbelian F.hAel
  obtain ⟨P, hP, hAP⟩ := exists_isSylowIn_ge F.hAK hA3
  have hP3 : IsPGroup 3 ↥P := hP.2.1
  have hP₁ : IsSylowIn 3 K (P ⊓ K) := isSylowIn_inf_of_normal hP hKY hKnorm
  have hcomm12 : ∀ s ∈ P ⊓ K, ∀ p ∈ P ⊓ C₁, s * p = p * s := by
    intro s hs p hp
    have h1 := comm_mem_of_mem_centBar (Subgroup.mem_inf.1 hp).2 (Subgroup.mem_inf.1 hs).2
    have h2 : p * s * p⁻¹ * s⁻¹ = 1 := by
      refine eq_one_of_mem_pPrimeCoreOf hP3 h1 ?_
      exact P.mul_mem (P.mul_mem (P.mul_mem (Subgroup.mem_inf.1 hp).1 (Subgroup.mem_inf.1 hs).1)
        (P.inv_mem (Subgroup.mem_inf.1 hp).1)) (P.inv_mem (Subgroup.mem_inf.1 hs).1)
    calc s * p = (p * s * p⁻¹ * s⁻¹)⁻¹ * (p * s) := by group
      _ = p * s := by rw [h2, inv_one, one_mul]
  have hD : ∀ x ∈ A, ∃ s ∈ P ⊓ K, s⁻¹ * x ∈ P ⊓ C₁ := by
    intro x hx
    obtain ⟨hxN, hinn⟩ := mem_innerSub.1 (F.hAin hx)
    have hxP : x ∈ P := hAP hx
    obtain ⟨s, hs, hsc⟩ := exists_mem_sylow_mul_mem_centBar (X := Cg a) hZ3 F.hKC hP₁
      (hYC (F.hAK hx)) hxN (F.hAel.2 x hx)
      (fun s hs => Subgroup.mem_inf.2 ⟨P.mul_mem (P.mul_mem hxP (Subgroup.mem_inf.1 hs).1)
        (P.inv_mem hxP), (Subgroup.mem_normalizer_iff.1 hxN s).1 (Subgroup.mem_inf.1 hs).2⟩) hinn
    exact ⟨s, hs, Subgroup.mem_inf.2 ⟨P.mul_mem (P.inv_mem (Subgroup.mem_inf.1 hs).1) hxP, hsc⟩⟩
  let F₂ : Subgroup G :=
    { carrier := {p | p ∈ P ⊓ C₁ ∧ ∃ s ∈ P ⊓ K, s * p ∈ A}
      one_mem' := ⟨Subgroup.one_mem _, 1, Subgroup.one_mem _, by simpa using A.one_mem⟩
      mul_mem' := by
        rintro p p' ⟨hp, s, hs, hsp⟩ ⟨hp', s', hs', hsp'⟩
        refine ⟨Subgroup.mul_mem _ hp hp', s * s', Subgroup.mul_mem _ hs hs', ?_⟩
        have e : s * s' * (p * p') = (s * p) * (s' * p') := by
          calc s * s' * (p * p') = s * (s' * p) * p' := by group
            _ = s * (p * s') * p' := by rw [hcomm12 s' hs' p hp]
            _ = (s * p) * (s' * p') := by group
        rw [e]
        exact A.mul_mem hsp hsp'
      inv_mem' := by
        rintro p ⟨hp, s, hs, hsp⟩
        refine ⟨Subgroup.inv_mem _ hp, s⁻¹, Subgroup.inv_mem _ hs, ?_⟩
        have e : s⁻¹ * p⁻¹ = (s * p)⁻¹ := by
          calc s⁻¹ * p⁻¹ = (p * s)⁻¹ := by group
            _ = (s * p)⁻¹ := by rw [hcomm12 s hs p hp]
        rw [e]
        exact A.inv_mem hsp }
  have hF₂mem : ∀ p, p ∈ F₂ ↔ p ∈ P ⊓ C₁ ∧ ∃ s ∈ P ⊓ K, s * p ∈ A := fun p => Iff.rfl
  have hAdec : ∀ x ∈ A, ∃ s ∈ P ⊓ K, ∃ p ∈ F₂, x = s * p := by
    intro x hx
    obtain ⟨s, hs, hsp⟩ := hD x hx
    exact ⟨s, hs, s⁻¹ * x, ⟨hsp, s, hs, by simpa using hx⟩, by group⟩
  obtain ⟨hScard, hSexp, hSnonab, z, hzS, hzK, hz1, hzc, hzgen⟩ :=
    sylow_of_isSLThreeFour hK F.hSL hSyl hP₁
  have hzC₁ : z ∈ C₁ := by
    refine mem_centBar_of_comm (hYC (hP.1 (Subgroup.mem_inf.1 hzS).1)) (Subgroup.le_normalizer hzK)
      fun p hp => ?_
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)
        ((⟨z, hzK⟩ : ↥K) * ⟨p, hp⟩ * (⟨z, hzK⟩ : ↥K)⁻¹ * (⟨p, hp⟩ : ↥K)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have := (Subgroup.mem_center_iff.1 hzc) (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨p, hp⟩)
      calc _ = (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨p, hp⟩ *
              QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨z, hzK⟩) *
            (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨z, hzK⟩)⁻¹ *
            (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨p, hp⟩)⁻¹ := by rw [this]
        _ = 1 := by group
    have h2 : ((⟨z, hzK⟩ : ↥K) * ⟨p, hp⟩ * (⟨z, hzK⟩ : ↥K)⁻¹ * (⟨p, hp⟩ : ↥K)⁻¹) ∈
        GLAPPrimeCore 3 ↥K := (QuotientGroup.eq_one_iff _).1 h1
    exact (CFSG.HardMathSupport.Solomon.LocalBalance.mem_glaPPrimeCoreOf_iff _).2 h2
  have hzP : z ∈ P ⊓ C₁ := Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hzS).1, hzC₁⟩
  have hz3 : z ^ 3 = 1 := hSexp z hzS
  have hzA : ∀ x ∈ A, x * z = z * x := by
    intro x hx
    obtain ⟨s, hs, p, hp, rfl⟩ := hAdec x hx
    have h1 : z * p = p * z := hcomm12 z hzS p (hF₂mem p |>.1 hp).1
    have h2 : s * z = z * s := hcomm12 s hs z hzP
    calc s * p * z = s * (p * z) := by group
      _ = s * (z * p) := by rw [h1]
      _ = (s * z) * p := by group
      _ = (z * s) * p := by rw [h2]
      _ = z * (s * p) := by group
  have hzmem : z ∈ A := by
    have hc : ∀ x ∈ A, ∀ y ∈ Subgroup.zpowers z, x * y = y * x := by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((show Commute x z from hzA x hx).zpow_right i).eq
    have hel := isElemAbelian_sup F.hAel (Lemma1111.isElemAbelian_zpowers hz3) hc
    have heq := F.hsc.2.2 (A ⊔ Subgroup.zpowers z) le_top hel le_sup_left
    have : z ∈ A ⊔ Subgroup.zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    rwa [heq] at this
  have hza : z ∈ Subgroup.zpowers a := F.inf_centBar_le (Subgroup.mem_inf.2 ⟨hzmem, hzC₁⟩)
  have hz1' : z ≠ 1 := by
    rintro rfl
    exact hz1 (by rw [show (⟨1, hzK⟩ : ↥K) = 1 from rfl, map_one])
  have hzpa : Subgroup.zpowers z = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hza)
      (by rw [card_zpowers_three F.ha1 F.ha3, card_zpowers_three hz1' hz3])
  have haS : a ∈ P ⊓ K := by
    have : a ∈ Subgroup.zpowers z := by rw [hzpa]; exact Subgroup.mem_zpowers a
    exact (Subgroup.zpowers_le.2 hzS) this
  have haC₁ : a ∈ C₁ := F.mem_centBar_a
  have haP : a ∈ P ⊓ C₁ := Subgroup.mem_inf.2 ⟨hAP F.ha, haC₁⟩
  have haF₂ : a ∈ F₂ := ⟨haP, 1, Subgroup.one_mem _, by simpa using F.ha⟩
  obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowIn_ge (hP.1.trans hYC) hP3
  refine ⟨P ⊓ K, F₂, hScard, hSexp, hSnonab, haS, ?_, haF₂, ?_, ?_, ?_, hAdec, fun p hp => hp.2, ?_, ?_,
    hP₁, Q, hQ, inf_le_left.trans hPQ, hAP.trans hPQ⟩
  · intro s hs
    exact ((Subgroup.mem_centralizer_iff.1 (F.hKC (Subgroup.mem_inf.1 hs).2)) a
      (Set.mem_singleton a)).symm
  · intro p hp
    exact ((Subgroup.mem_centralizer_iff.1 (hC₁C (Subgroup.mem_inf.1 hp.1).2)) a
      (Set.mem_singleton a)).symm
  · intro s hs p hp
    exact hcomm12 s hs p hp.1
  · intro w hw hwF
    have hwK : w ∈ K := (Subgroup.mem_inf.1 hw).2
    have hwC : w ∈ C₁ := (Subgroup.mem_inf.1 hwF.1).2
    have := hzgen w hw hwK (mk_mem_center_of_centBar hwK hwC)
    rwa [hzpa] at this
  · intro p hp
    obtain ⟨hpC, s, hs, hsp⟩ := hp
    have h3 : (s * p) ^ 3 = 1 := F.hAel.2 _ hsp
    have hcm : Commute s p := hcomm12 s hs p hpC
    rw [hcm.mul_pow, hSexp s hs, one_mul] at h3
    exact h3
  · intro p hp hpA
    exact F.inf_centBar_le (Subgroup.mem_inf.2 ⟨hpA, (Subgroup.mem_inf.1 hp.1).2⟩)

theorem FactsSL.exists_sylow_top (F : FactsSL E A K a) (hK : GLAPComponent 3 (Cg a) K)
    (hSyl : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.InputSL34Sylow)
    (hCent : InputSL34SylowCent) :
    ∃ Q : Subgroup G, IsSylowIn 3 ⊤ Q ∧ A ≤ Q ∧ Q ≤ Cg a ∧
      ∀ w ∈ Q, (∀ q ∈ Q, w * q = q * w) → w ^ 3 = 1 → w ∈ Subgroup.zpowers a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, F₂, -, -, -, -, -, -, -, -, -, -, -, -, -, hSs, Q, hQ, hSQ, hAQ⟩ := F.exists_conf hK hSyl
  obtain ⟨hS2p, hS2c, hS2card⟩ := sylow_image_facts F.hSL hSs
  set π : ↥K →* barOf 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) with hπ
  have hAC : A ≤ Cg a := fun x hx => Subgroup.mem_centralizer_iff.2 (fun g hg => by
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact F.hAc a F.ha x hx)
  have key : ∀ w ∈ Q, (∀ q ∈ Q, w * q = q * w) → w ^ 3 = 1 → w ∈ Subgroup.zpowers a := by
    intro w hwQ hwc hw3
    have hwA : w ∈ A := by
      have hc : ∀ x ∈ A, ∀ y ∈ Subgroup.zpowers w, x * y = y * x := by
        intro x hx y hy
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact ((show Commute x w from (hwc x (hAQ hx)).symm).zpow_right i).eq
      have hel := isElemAbelian_sup F.hAel (Lemma1111.isElemAbelian_zpowers hw3) hc
      have heq := F.hsc.2.2 (A ⊔ Subgroup.zpowers w) le_top hel le_sup_left
      have : w ∈ A ⊔ Subgroup.zpowers w := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
      rwa [heq] at this
    obtain ⟨hwN, k, hk, hkc⟩ := mem_innerSub.1 (F.hAin hwA)
    have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
    obtain ⟨-, hkcN, hkc1⟩ := mem_centBar_iff'.1 hkc
    have hxk : (⟨w, hwN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨k, hkN⟩ * ⟨k⁻¹ * w, hkcN⟩ := Subtype.ext (by simp)
    have hρ : barAut 3 K ⟨w, hwN⟩ = barAut 3 K ⟨k, hkN⟩ := by
      rw [hxk, map_mul, hkc1, mul_one]
    have hkcent : π ⟨k, hk⟩ ∈ Subgroup.center (barOf 3 K) := by
      refine hCent (barOf 3 K) F.hSL _ hS2p hS2c hS2card _ ?_
      rintro _ ⟨s, hs, rfl⟩
      have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
      have e1 := barAut_mk 3 K ⟨w, hwN⟩ s
      have e2 := barAut_mk 3 K ⟨k, hkN⟩ s
      rw [hρ] at e1
      have e3 : K.normalizerMonoidHom ⟨w, hwN⟩ s = s := Subtype.ext (by
        show w * (s : G) * w⁻¹ = s
        have h1 : w * (s : G) = (s : G) * w := hwc s (hSQ hsS)
        rw [h1]
        group)
      have e4 : K.normalizerMonoidHom ⟨k, hkN⟩ s = (⟨k, hk⟩ : ↥K) * s * (⟨k, hk⟩ : ↥K)⁻¹ :=
        Subtype.ext rfl
      rw [e3] at e1
      rw [e4] at e2
      have e5 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ((⟨k, hk⟩ : ↥K) * s * (⟨k, hk⟩ : ↥K)⁻¹) =
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) s := e2.symm.trans e1
      rw [map_mul, map_mul, map_inv] at e5
      exact mul_inv_eq_iff_eq_mul.1 e5
    have hw1 : barAut 3 K ⟨w, hwN⟩ = 1 := by
      rw [hρ]
      refine MulEquiv.ext fun y => ?_
      induction y using QuotientGroup.induction_on with
      | H t =>
        rw [barAut_mk, MulAut.one_apply]
        have e4 : K.normalizerMonoidHom ⟨k, hkN⟩ t = (⟨k, hk⟩ : ↥K) * t * (⟨k, hk⟩ : ↥K)⁻¹ :=
          Subtype.ext rfl
        rw [e4]
        have hc := (Subgroup.mem_center_iff.1 hkcent) (π t)
        show π ((⟨k, hk⟩ : ↥K) * t * (⟨k, hk⟩ : ↥K)⁻¹) = π t
        rw [map_mul, map_mul, map_inv, ← hc]
        group
    have hwC : w ∈ centBar 3 (Cg a) K := mem_centBar_iff'.2 ⟨hAC hwA, hwN, hw1⟩
    exact F.inf_centBar_le (Subgroup.mem_inf.2 ⟨hwA, hwC⟩)
  have haQ : a ∈ Q := hAQ F.ha
  have hQC : Q ≤ Cg a := hQ.1
  have hnorm1 : ∀ x ∈ Subgroup.normalizer (Q : Set G), x * a * x⁻¹ ∈ Subgroup.zpowers a := by
    intro x hx
    refine key _ ((Subgroup.mem_normalizer_iff.1 hx a).1 haQ) (fun q hq => ?_) ?_
    · have hqt : x⁻¹ * q * x ∈ Q := by
        refine (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * q * x)).2 ?_
        have : x * (x⁻¹ * q * x) * x⁻¹ = q := by group
        rw [this]
        exact hq
      have hact : a * (x⁻¹ * q * x) = (x⁻¹ * q * x) * a :=
        (Subgroup.mem_centralizer_iff.1 (hQC hqt)) a (Set.mem_singleton a)
      calc x * a * x⁻¹ * q = x * (a * (x⁻¹ * q * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * q * x) * a) * x⁻¹ := by rw [hact]
        _ = q * (x * a * x⁻¹) := by group
    · rw [conj_pow, F.ha3]
      group
  have hnorm : ∀ x ∈ Subgroup.normalizer (Q : Set G),
      x ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ (hnorm1 x hx) i
    · intro hw
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hw
      have h1 := hnorm1 x⁻¹ ((Subgroup.normalizer (Q : Set G)).inv_mem hx)
      have : w = (x⁻¹ * a * x⁻¹⁻¹) ^ i := by
        rw [conj_zpow, hi]
        group
      rw [this]
      exact Subgroup.zpow_mem _ h1 i
  exact ⟨Q, isSylowIn_top_of_normalizes hQ F.ha1 F.ha3 hnorm, hAQ, hQC, key⟩

end SLConf

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1112

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut innerAut)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1112b
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1112

section Claims

variable {G : Type} [Group G] [Finite G]

theorem Claims1112.facts_of_siblings (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h104ii : Lemma104_iiStatement) {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K) : Facts E A K a := by
  obtain ⟨-, hA3, hL⟩ := h1111 h
  exact facts_of h hL hA3 (h119 h) ((h104ii h.toCex117Base.toSec11.toSec10Fails h.pair).2)

end Claims

theorem Claims1112.finite_of_isLThreeFour {X : Type} [Group X] (hX : IsLThreeFour X) : Finite X := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hX
  exact Finite.of_equiv _ e.symm.toEquiv

theorem Claims1112.inputAutL34Order9_holds : InputAutL34Order9 := by
  intro X _ hX E hE
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite X := Claims1112.finite_of_isLThreeFour hX
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (isPGroup_of_isElemAbelian hE)
  have hn2 : n ≤ 2 :=
    (le_pRank_of_card (le_top : E ≤ ⊤) hE hn).trans (pRank_mulAut_le_two_of_isLThreeFour hX)
  rw [hn]
  calc (3 : ℕ) ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    _ = 9 := by norm_num

theorem Claims1112.inputCgNormalizesK_holds (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h104ii : Lemma104_iiStatement) : InputCgNormalizesK := by
  intro G _ _ m B M E A a K h
  exact (Claims1112.facts_of_siblings h1111 h119 h104ii h).cg_le_normalizer h.hK

theorem Claims1112.inputCentBarRankOne_holds (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h104ii : Lemma104_iiStatement) : InputCentBarRankOne := by
  intro G _ _ m B M E A a K h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have F := Claims1112.facts_of_siblings h1111 h119 h104ii h
  refine le_antisymm ?_ ?_
  · unfold CFSG.Open.pRank
    apply csSup_le
    · exact ⟨0, ⊥, bot_le, ⟨⟨⟨fun x y => Subtype.ext (by
        simp [Subgroup.mem_bot.1 x.2, Subgroup.mem_bot.1 y.2])⟩⟩,
        fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]⟩, by simp⟩
    · rintro k ⟨U, hUC, hUel, hUk⟩
      have h1 := F.rankOne U hUC hUel
      rw [hUk] at h1
      have : 3 ^ k ≤ 3 ^ 1 := by simpa using h1
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  · refine le_pRank_of_card (E := Subgroup.zpowers a) (Subgroup.zpowers_le.2 F.mem_centBar_a)
      (Lemma1111.isElemAbelian_zpowers F.ha3) ?_
    rw [Lemma1111.card_zpowers_three F.ha1 F.ha3, pow_one]

theorem Claims1112.p1SylowClaim_holds (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h104ii : Lemma104_iiStatement) (h113 : Lemma113_iStatement) (hExp3 : InputAutL34Exp3) :
    P1SylowClaim := by
  intro G _ _ m B M E A a K h
  have F := Claims1112.facts_of_siblings h1111 h119 h104ii h
  have hCN := F.cg_le_normalizer h.hK
  have hC : CFSG.Open.pRank 3 (Cg a) = 3 :=
    p1rank_of_inputs h1111 (Claims1112.inputCgNormalizesK_holds h1111 h119 h104ii)
      (Claims1112.inputCentBarRankOne_holds h1111 h119 h104ii)
      Claims1112.inputAutL34Order9_holds h
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
    le_trans (h113 h.toCex117Base.toSec11 h.ha.1 h.ha.2 (fun hx => h.notD hx)) (pRank_mono le_top)
  exact F.isSylowIn_centBar hCN hExp3 (not_isPCentral_of_pRank hC h4)

theorem lemma1112P1Claim_of_inputs (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h104ii : Lemma104_iiStatement) (h113 : Lemma113_iStatement) (hExp3 : InputAutL34Exp3) :
    Lemma1112.P1Claim :=
  p1Claim_of_inputs (Claims1112.p1SylowClaim_holds h1111 h119 h104ii h113 hExp3) h1111
    (Claims1112.inputCgNormalizesK_holds h1111 h119 h104ii)
    (Claims1112.inputCentBarRankOne_holds h1111 h119 h104ii) Claims1112.inputAutL34Order9_holds

theorem lemma1112P2Claim_of_inputs (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h104ii : Lemma104_iiStatement) (h113 : Lemma113_iStatement) (hExp3 : InputAutL34Exp3)
    (hL34 : InputL34FusionK) : Lemma1112.P2Claim :=
  p2Claim_of_inputs h1111 h119 h113 hL34
    (Claims1112.p1SylowClaim_holds h1111 h119 h104ii h113 hExp3)

theorem lemma1112P3Claim_of_inputs (h113 : Lemma113_iStatement) (hP1 : Lemma1112.P1Claim) :
    Lemma1112.P3Claim := by
  intro G _ _ m B M E A a K h U hU hconj
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := hconj
  have hE4 : 4 ≤ CFSG.Open.pRank 3 E :=
    h113 h.toCex117Base.toSec11 h.ha.1 h.ha.2 (fun hx => h.notD hx)
  have hC3 : CFSG.Open.pRank 3 (Cg a) = 3 := (hP1 h).2
  obtain ⟨E₁, hE₁E, hE₁el, hE₁c⟩ := exists_elemAb_card_pRank (p := 3) E
  have hEel : IsElemAbelian 3 E := h.pair.1.1.1.1.2.1
  have hu : g⁻¹ * a * g ∈ U := by
    rw [← hg]
    exact mem_glbConj.2 ⟨a, Subgroup.mem_zpowers a, rfl⟩
  have huE : g⁻¹ * a * g ∈ E := (Subgroup.mem_inf.1 (hU.1 hu)).1
  have hcomm : ∀ e ∈ E, g * e * g⁻¹ ∈ Cg a := by
    intro e he
    refine Subgroup.mem_centralizer_iff.2 (fun x hx => ?_)
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have h1 : e * (g⁻¹ * a * g) = (g⁻¹ * a * g) * e :=
      congrArg Subtype.val (hEel.1.is_comm.comm ⟨e, he⟩ ⟨_, huE⟩)
    calc a * (g * e * g⁻¹) = g * (g⁻¹ * a * g) * e * g⁻¹ := by group
      _ = g * (e * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]; group
      _ = g * e * g⁻¹ * a := by group
  have hle : GLBConj g⁻¹ E₁ ≤ Cg a := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := mem_glbConj.1 hw
    simpa using hcomm e (hE₁E he)
  have h1 := le_pRank_of_card hle (isElemAbelian_glbConj hE₁el g⁻¹)
    (by rw [card_glbConj, hE₁c] : Nat.card (GLBConj g⁻¹ E₁) = 3 ^ CFSG.Open.pRank 3 E)
  omega

theorem lemma1112_of_inputs' (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h104ii : Lemma104_iiStatement) (h113 : Lemma113_iStatement) (hExp3 : InputAutL34Exp3)
    (hL34 : InputL34FusionK) : Lemma1112Statement :=
  lemma1112_of_inputs h1111 h119 h104ii (lemma1112P1Claim_of_inputs h1111 h119 h104ii h113 hExp3)
    (lemma1112P2Claim_of_inputs h1111 h119 h104ii h113 hExp3 hL34)
    (lemma1112P3Claim_of_inputs h113 (lemma1112P1Claim_of_inputs h1111 h119 h104ii h113 hExp3))

section Claims1111

variable {G : Type} [Group G] [Finite G]

theorem Claims1112.factsSL_of_siblings (h1110 : Lemma1110Statement) (h119 : Lemma119Statement)
    (h104ii : Lemma104_iiStatement) {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K) (hSL : IsSLThreeFour (barOf 3 K)) : FactsSL E A K a := by
  have hT := h1110 h
  unfold Type117c at hT
  obtain ⟨-, hA3, -⟩ := hT
  have hB := facts_base_of h hA3 (h119 h) ((h104ii h.toCex117Base.toSec11.toSec10Fails h.pair).2)
  exact { hB with hSL := hSL }

theorem Claims1112.mem_inf_of_omegaOne {E A R : Subgroup G} (hE : IsSCp 3 ⊤ E) (hA : IsSCp 3 ⊤ A)
    (hER : E ≤ R) (hAR : A ≤ R) {e : G} (he : e ∈ omegaOne 3 (centerOf R)) : e ∈ E ⊓ A :=
  Subgroup.mem_inf.2 ⟨l1110_omegaOne_centerOf_le hE hER he, l1110_omegaOne_centerOf_le hA hAR he⟩

theorem Claims1112.normalizer_le_of_normal_plane (h104v : Lemma104_vStatement) {m : ℕ}
    {B M E A : Subgroup G} (h : Sec11 G m 3 B M E A) (hA3 : CFSG.Open.pRank 3 A = 3)
    (hE4 : 4 ≤ CFSG.Open.pRank 3 E) {R : Subgroup G} (hR : IsSylowIn 3 M R) (hER : E ≤ R)
    {U : Subgroup G} (hU : IsPPlane 3 U) (hUR : U ≤ R)
    (hN : R ≤ Subgroup.normalizer (U : Set G)) : Subgroup.normalizer (U : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEel : IsElemAbelian 3 E := h.pair.1.1.1.1.2.1
  obtain ⟨W, hWE, hWel, hWcard⟩ := exists_le_isElemAbelian_card hEel (n := 4) (by
    rw [Lemma1112.card_eq_pow_pRank hEel]
    exact pow_dvd_pow 3 hE4)
  have hW : IsEkIn 3 4 R W := ⟨hWE.trans hER, hWel, hWcard⟩
  obtain ⟨W', hW', hUW', -⟩ := input31_chain_to_plane (by norm_num) hR.2.1 hU hUR hN hW
  obtain ⟨-, -, A', hA'D, hW'A'⟩ := (h104v h.toSec10Fails h.pair (Or.inr hA3) hR).1 W' hW'
  have hUA' : U ≤ A' := hUW'.trans hW'A'
  have hrank : 2 ≤ CFSG.Open.pRank 3 U := le_pRank_of_card (le_refl U) hU.1 (by rw [hU.2])
  intro x hx
  have hle : Subgroup.normalizer (U : Set G) ≤ GLBCore 3 2 A' :=
    le_sSup (⟨U, hUA', hrank, rfl⟩ : ∃ Q : Subgroup G, Q ≤ A' ∧ 2 ≤ CFSG.Open.pRank 3 Q ∧
      Subgroup.normalizer (U : Set G) = Subgroup.normalizer (Q : Set G))
  exact hA'D.2.clause_d (hle hx)

@[expose] def Claims1112.Input31_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ R Q : Subgroup G, IsPGroup p ↥R →
    Q ≤ R → (Q.subgroupOf R).Normal → ¬ IsCyclic ↥Q →
      ∃ U : Subgroup G, U ≤ Q ∧ IsPPlane p U ∧ R ≤ Subgroup.normalizer (U : Set G)

@[expose] def Claims1112.InputSL34PlaneTransitive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J S : Subgroup G), IsSLThreeFour (barOf 3 J) → IsSylowIn 3 J S →
    ∀ U U' : Subgroup G, U ≤ S → U' ≤ S → IsPPlane 3 U → IsPPlane 3 U' →
      ∃ x ∈ J, x ∈ Subgroup.normalizer (S : Set G) ∧ GLBConj x U = U'

@[expose] def Claims1112.Lemma1111P2Many : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) (B M E A : Subgroup G) (a : G) (K : Subgroup G),
    Cex117 G m 3 B M E A a K → IsSLThreeFour (barOf 3 K) →
      ∀ R : Subgroup G, IsSylowIn 3 M R → E ⊔ A ≤ R →
        ∀ e ∈ omegaOne 3 (centerOf R), e ≠ 1 → ∀ J : Subgroup G, GLAPComponent 3 (Cg e) J →
          IsSLThreeFour (barOf 3 J) → ¬ Cg e ≤ Subgroup.normalizer (J : Set G) → Cg e ≤ M

theorem Claims1112.cg_eq_of_zpowers_eq {x y : G} (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    Cg x = Cg y := by
  have key : ∀ {u v : G}, v ∈ Subgroup.zpowers u → Cg u ≤ Cg v := by
    intro u v hv z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    refine Subgroup.mem_centralizer_iff.2 (fun g hg => ?_)
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    have hzu : u * z = z * u := (Subgroup.mem_centralizer_iff.1 hz) u (Set.mem_singleton u)
    exact ((show Commute u z from hzu).zpow_left i).eq
  exact le_antisymm (key (h ▸ Subgroup.mem_zpowers y)) (key (h.symm ▸ Subgroup.mem_zpowers x))

theorem Claims1112.p2_setup (h1110 : Lemma1110Statement) (h119 : Lemma119Statement)
    (h104ii : Lemma104_iiStatement) (h104iv : Lemma104_ivStatement)
    (hSyl : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.InputSL34Sylow)
    (hCent : Claims1112.InputSL34SylowCent) {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K) (hSL : IsSLThreeFour (barOf 3 K)) {R : Subgroup G}
    (hR : IsSylowIn 3 M R) (hER : E ⊔ A ≤ R) {e : G} (he : e ∈ omegaOne 3 (centerOf R))
    (he1 : e ≠ 1) :
    IsSylowIn 3 ⊤ R ∧ ∃ J : Subgroup G, GLAPComponent 3 (Cg e) J ∧ IsSLThreeFour (barOf 3 J) ∧ J ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have F := Claims1112.factsSL_of_siblings h1110 h119 h104ii h hSL
  have hsc := h104ii h.toCex117Base.toSec11.toSec10Fails h.pair
  have hRtop : IsSylowIn 3 ⊤ R :=
    (h104iv h.toCex117Base.toSec11.toSec10Fails h.pair (h119 h).1 hR).2.2
  have heEA : e ∈ E ⊓ A := Claims1112.mem_inf_of_omegaOne hsc.1 hsc.2 (le_sup_left.trans hER)
    (le_sup_right.trans hER) he
  have heE : e ∈ E := (Subgroup.mem_inf.1 heEA).1
  have heA : e ∈ A := (Subgroup.mem_inf.1 heEA).2
  have he3 : e ^ 3 = 1 := F.hAel.2 e heA
  have heCen : e ∈ centerOf R := ((Subgroup.closure_le _).2 (fun x hx => hx.1) : omegaOne 3 (centerOf R) ≤
    centerOf R) he
  obtain ⟨heR, hecomm⟩ := (Lemma1111.mem_centerOf_iff R e).1 heCen
  obtain ⟨Q, hQtop, hAQ, hQC, hkey⟩ := F.exists_sylow_top h.hK hSyl hCent
  obtain ⟨y, -, hy⟩ := exists_conj_le_of_isSylowIn hQtop (le_top : R ≤ ⊤) hRtop.2.1
  have hRle : R ≤ GLBConj y⁻¹ Q := by
    intro r hr
    rw [mem_gLBConj]
    simpa using hy r hr
  have hconj3 : IsPGroup 3 ↥(GLBConj y⁻¹ Q) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQtop.2.1
    exact (IsPGroup.iff_card).2 ⟨n, by rw [card_glbConj, hn]⟩
  have hReq : R = GLBConj y⁻¹ Q := (hRtop.2.2 _ le_top hconj3 hRle).symm
  have he'Q : y⁻¹ * e * y ∈ Q := hy e heR
  have he'c : ∀ q ∈ Q, (y⁻¹ * e * y) * q = q * (y⁻¹ * e * y) := by
    intro q hq
    have hr : y * q * y⁻¹ ∈ R := by
      rw [hReq, mem_gLBConj]
      have e : y⁻¹ * (y * q * y⁻¹) * y⁻¹⁻¹ = q := by group
      rw [e]
      exact hq
    have h1 := hecomm _ hr
    calc y⁻¹ * e * y * q = y⁻¹ * (e * (y * q * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * q * y⁻¹) * e) * y := by rw [h1.symm]
      _ = q * (y⁻¹ * e * y) := by group
  have he'3 : (y⁻¹ * e * y) ^ 3 = 1 := by
    have h1 : (y⁻¹ * e * y) ^ 3 = y⁻¹ * e ^ 3 * y := by
      have := conj_pow (a := y⁻¹) (b := e) (i := 3)
      simpa using this
    rw [h1, he3]
    group
  have he'a : y⁻¹ * e * y ∈ Subgroup.zpowers a := hkey _ he'Q (fun q hq => (he'c q hq).symm.symm) he'3
  have he'1 : y⁻¹ * e * y ≠ 1 := by
    intro h1
    apply he1
    have : e = y * (y⁻¹ * e * y) * y⁻¹ := by group
    rw [this, h1]
    group
  have hzp : Subgroup.zpowers (y⁻¹ * e * y) = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 he'a)
      (by rw [Lemma1111.card_zpowers_three F.ha1 F.ha3, Lemma1111.card_zpowers_three he'1 he'3])
  have hCe : Cg e = GLBConj y⁻¹ (Cg a) := by
    rw [← Claims1112.cg_eq_of_zpowers_eq hzp]
    ext x
    rw [mem_gLBConj, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      have := hx e (Set.mem_singleton e)
      calc y⁻¹ * e * y * (y⁻¹ * x * y⁻¹⁻¹) = y⁻¹ * (e * x) * y := by group
        _ = y⁻¹ * (x * e) * y := by rw [this]
        _ = y⁻¹ * x * y⁻¹⁻¹ * (y⁻¹ * e * y) := by group
    · intro hx g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      have := hx (y⁻¹ * e * y) (Set.mem_singleton _)
      have h2 : y⁻¹ * (e * x) * y = y⁻¹ * (x * e) * y := by
        calc y⁻¹ * (e * x) * y = y⁻¹ * e * y * (y⁻¹ * x * y⁻¹⁻¹) := by group
          _ = y⁻¹ * x * y⁻¹⁻¹ * (y⁻¹ * e * y) := this
          _ = y⁻¹ * (x * e) * y := by group
      have := mul_left_cancel (mul_right_cancel h2)
      exact this
  have hJc : GLAPComponent 3 (Cg e) (GLBConj y⁻¹ K) := by
    rw [hCe]
    exact glaPComponent_gLBConj h.hK y⁻¹
  have hJSL : IsSLThreeFour (barOf 3 (GLBConj y⁻¹ K)) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.EvenSL.isSLThreeFour_of_mulEquiv
      (conjQuotEquiv 3 y⁻¹ K).symm hSL
  refine ⟨hRtop, GLBConj y⁻¹ K, hJc, hJSL, ?_⟩
  exact h.pair.1.1.2.clause_e rfl e heE he1 _ hJc (Or.inr hJSL)

theorem Claims1112.le_cg_of_omegaOne {R : Subgroup G} {e : G} (he : e ∈ omegaOne 3 (centerOf R)) :
    R ≤ Cg e := by
  have heCen : e ∈ centerOf R :=
    ((Subgroup.closure_le _).2 (fun x hx => hx.1) : omegaOne 3 (centerOf R) ≤ centerOf R) he
  obtain ⟨-, hecomm⟩ := (Lemma1111.mem_centerOf_iff R e).1 heCen
  intro r hr
  exact Subgroup.mem_centralizer_iff.2 (fun g hg => by
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact (hecomm r hr).symm)

theorem Claims1112.cg_le_of_normal_component (h104v : Lemma104_vStatement)
    (hI315 : Claims1112.Input31_5) (hTrans : Claims1112.InputSL34PlaneTransitive)
    (hSyl : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.InputSL34Sylow) {m : ℕ}
    {B M E A : Subgroup G} (h : Sec11 G m 3 B M E A) (hA3 : CFSG.Open.pRank 3 A = 3)
    (hE4 : 4 ≤ CFSG.Open.pRank 3 E) {R : Subgroup G} (hR : IsSylowIn 3 M R) (hER : E ≤ R)
    (hRtop : IsSylowIn 3 ⊤ R) {e : G} (hReC : R ≤ Cg e) {J : Subgroup G}
    (hJ : GLAPComponent 3 (Cg e) J) (hJSL : IsSLThreeFour (barOf 3 J)) (hJM : J ≤ M)
    (hJN : Cg e ≤ Subgroup.normalizer (J : Set G)) : Cg e ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRC : IsSylowIn 3 (Cg e) R :=
    ⟨hReC, hRtop.2.1, fun R' _ hR'3 hRR' => hRtop.2.2 R' le_top hR'3 hRR'⟩
  have hJC : J ≤ Cg e := hJ.1
  have hJnorm : ∀ y ∈ Cg e, ∀ n ∈ J, y * n * y⁻¹ ∈ J := fun y hy n hn =>
    (Subgroup.mem_normalizer_iff.1 (hJN hy) n).1 hn
  have hSsyl : IsSylowIn 3 J (R ⊓ J) := isSylowIn_inf_of_normal hRC hJC hJnorm
  obtain ⟨-, -, ⟨x₀, hx₀, y₀, hy₀, hxy⟩, -⟩ := Claims1112.sylow_of_isSLThreeFour hJ hJSL hSyl hSsyl
  have hSnorm : ((R ⊓ J).subgroupOf R).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨-, hnJ⟩ := Subgroup.mem_inf.1 hn
    exact Subgroup.mem_inf.2 ⟨R.mul_mem (R.mul_mem g.2 n.2) (R.inv_mem g.2),
      (Subgroup.mem_normalizer_iff.1 (hJN (hReC g.2)) n).1 hnJ⟩⟩
  have hnc : ¬ IsCyclic ↥(R ⊓ J) := by
    intro hcyc
    letI : CommGroup ↥(R ⊓ J) := IsCyclic.commGroup
    exact hxy (congrArg Subtype.val (mul_comm (⟨x₀, hx₀⟩ : ↥(R ⊓ J)) ⟨y₀, hy₀⟩))
  obtain ⟨U, hUS, hU, hUN⟩ := hI315 G 3 Nat.prime_three (by norm_num) R (R ⊓ J) hRtop.2.1
    inf_le_left hSnorm hnc
  have hNU : Subgroup.normalizer (U : Set G) ≤ M :=
    Claims1112.normalizer_le_of_normal_plane h104v h hA3 hE4 hR hER hU (hUS.trans inf_le_left) hUN
  intro g hg
  have hgN : g ∈ Subgroup.normalizer (J : Set G) := hJN hg
  set S : Subgroup G := R ⊓ J with hSdef
  have hS₁J : GLBConj g⁻¹ S ≤ J := by
    intro r hr
    rw [mem_gLBConj] at hr
    have hrJ : g⁻¹ * r * g⁻¹⁻¹ ∈ J := (Subgroup.mem_inf.1 hr).2
    have := (Subgroup.mem_normalizer_iff.1 hgN _).1 hrJ
    have e : g * (g⁻¹ * r * g⁻¹⁻¹) * g⁻¹ = r := by group
    rwa [e] at this
  have hS₁3 : IsPGroup 3 ↥(GLBConj g⁻¹ S) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hSsyl.2.1
    exact (IsPGroup.iff_card).2 ⟨n, by rw [card_glbConj, hn]⟩
  obtain ⟨j, hjJ, hj⟩ := exists_conj_le_of_isSylowIn hSsyl hS₁J hS₁3
  have hg'S : ∀ s ∈ S, (j⁻¹ * g) * s * (j⁻¹ * g)⁻¹ ∈ S := by
    intro s hs
    have hs₁ : g * s * g⁻¹ ∈ GLBConj g⁻¹ S := by
      rw [mem_gLBConj]
      have e : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s := by group
      rw [e]
      exact hs
    have := hj _ hs₁
    have e : (j⁻¹ * g) * s * (j⁻¹ * g)⁻¹ = j⁻¹ * (g * s * g⁻¹) * j := by group
    rw [e]
    exact this
  set g' : G := j⁻¹ * g with hg'
  have hg'N : g' ∈ Subgroup.normalizer (S : Set G) := Subgroup.mem_normalizer_fintype hg'S
  have hU' : IsPPlane 3 (GLBConj g'⁻¹ U) :=
    ⟨isElemAbelian_glbConj hU.1 _, by rw [card_glbConj]; exact hU.2⟩
  have hU'S : GLBConj g'⁻¹ U ≤ S := by
    intro z hz
    rw [mem_gLBConj] at hz
    have h1 : g'⁻¹ * z * g'⁻¹⁻¹ ∈ S := hUS hz
    have h2 := (Subgroup.mem_normalizer_iff.1 hg'N _).1 h1
    have e : g' * (g'⁻¹ * z * g'⁻¹⁻¹) * g'⁻¹ = z := by group
    rwa [e] at h2
  obtain ⟨x, hxJ, hxN, hxU⟩ := hTrans G J S hJSL hSsyl _ U hU'S hUS hU' hU
  have hnU : g'⁻¹ * x ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h1 : z ∈ U ↔ z ∈ GLBConj x (GLBConj g'⁻¹ U) := by rw [hxU]
    rw [h1, mem_gLBConj, mem_gLBConj]
    have e : g'⁻¹ * (x * z * x⁻¹) * g'⁻¹⁻¹ = g'⁻¹ * x * z * (g'⁻¹ * x)⁻¹ := by group
    rw [e]
  have hgeq : g = j * x * (g'⁻¹ * x)⁻¹ := by
    rw [hg']
    group
  rw [hgeq]
  exact M.mul_mem (M.mul_mem (hJM hjJ) (hJM hxJ)) (M.inv_mem (hNU hnU))

end Claims1111

theorem lemma1111P1Claim_of_inputs (h1110 : Lemma1110Statement) (h119 : Lemma119Statement)
    (h104ii : Lemma104_iiStatement)
    (hSyl : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.InputSL34Sylow) :
    Lemma1111.Lemma1111P1Claim := by
  intro G _ _ m B M E A a K h hSL
  have F := Claims1112.factsSL_of_siblings h1110 h119 h104ii h hSL
  obtain ⟨S, F₂, hScard, hSexp, hSnonab, haS, hSa, haF, hFa, hcomm, hSF, hdec, hF₂dec, hF₂3, hF₂A, -⟩ :=
    F.exists_conf h.hK hSyl
  obtain ⟨hAF, hF⟩ := Claims1112.extraspecial_of_conf F.hAel F.hsc F.hcardA F.ha F.ha1 F.ha3 hScard hSexp
    hSnonab haS hSa haF hFa hcomm hSF hdec hF₂dec hF₂3 hF₂A
  exact ⟨S ⊔ F₂, hAF, hF⟩

theorem lemma1111P2Claim_of_inputs (h1110 : Lemma1110Statement) (h119 : Lemma119Statement)
    (h104ii : Lemma104_iiStatement) (h104iv : Lemma104_ivStatement) (h104v : Lemma104_vStatement)
    (h113 : Lemma113_iStatement)
    (hSyl : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.InputSL34Sylow)
    (hCent : Claims1112.InputSL34SylowCent) (hI315 : Claims1112.Input31_5)
    (hTrans : Claims1112.InputSL34PlaneTransitive) (hMany : Claims1112.Lemma1111P2Many) :
    Lemma1111.Lemma1111P2Claim := by
  intro G _ _ m B M E A a K h hSL R hR hER e he he1
  obtain ⟨hRtop, J, hJ, hJSL, hJM⟩ :=
    Claims1112.p2_setup h1110 h119 h104ii h104iv hSyl hCent h hSL hR hER he he1
  by_cases hJN : Cg e ≤ Subgroup.normalizer (J : Set G)
  · have hT := h1110 h
    unfold Type117c at hT
    obtain ⟨-, hA3, -⟩ := hT
    have hE4 : 4 ≤ CFSG.Open.pRank 3 E :=
      h113 h.toCex117Base.toSec11 h.ha.1 h.ha.2 (fun hx => h.notD hx)
    exact Claims1112.cg_le_of_normal_component h104v hI315 hTrans hSyl h.toCex117Base.toSec11 hA3 hE4
      hR (le_sup_left.trans hER) hRtop (Claims1112.le_cg_of_omegaOne he) hJ hJSL hJM hJN
  · exact hMany G m B M E A a K h hSL R hR hER e he he1 J hJ hJSL hJN

theorem lemma1111_of_inputs''
    (hcov : CFSG.HardMathSupport.Solomon.UniquenessMaximal.InputL34Cover)
    (h1110 : Lemma1110Statement) (h119 : Lemma119Statement) (h104ii : Lemma104_iiStatement)
    (h104iv : Lemma104_ivStatement) (h104v : Lemma104_vStatement) (h113 : Lemma113_iStatement)
    (hSyl : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.InputSL34Sylow)
    (hCent : Claims1112.InputSL34SylowCent) (hI315 : Claims1112.Input31_5)
    (hTrans : Claims1112.InputSL34PlaneTransitive) (hMany : Claims1112.Lemma1111P2Many) :
    Lemma1111Statement :=
  lemma1111_of_inputs' hcov h1110 (lemma1111P1Claim_of_inputs h1110 h119 h104ii hSyl)
    (lemma1111P2Claim_of_inputs h1110 h119 h104ii h104iv h104v h113 hSyl hCent hI315 hTrans hMany)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
