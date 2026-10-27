module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1116

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

namespace AltFacts2

theorem isPiGroup_of_mulEquiv {p : ℕ} {L L' : Type*} [Group L] [Group L'] (φ : L ≃* L')
    (h : IsPiGroup p L) : IsPiGroup p L' := by
  obtain ⟨hq, hO, hcase⟩ := h
  let ψ : (L ⧸ Subgroup.center L) ≃* (L' ⧸ Subgroup.center L') :=
    QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
  refine ⟨CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv φ hq, ?_, ?_⟩
  · rw [← glaPPrimeCore_map_iso p φ, hO, Subgroup.map_bot]
  · rcases hcase with ⟨k, ⟨f⟩⟩ | ⟨n, ε, hn, hΩ, hfp⟩ | ⟨hp3, ⟨f⟩⟩
    · exact Or.inl ⟨k, ⟨ψ.symm.trans f⟩⟩
    · refine Or.inr (Or.inl ⟨n, ε, hn, ?_, hfp⟩)
      cases ε with
      | true => obtain ⟨f⟩ := hΩ; exact ⟨ψ.symm.trans f⟩
      | false => obtain ⟨f⟩ := hΩ; exact ⟨ψ.symm.trans f⟩
    · exact Or.inr (Or.inr ⟨hp3, ⟨ψ.symm.trans f⟩⟩)

section Generic

variable {G : Type} [Group G] [Finite G]

theorem piLayer_le {p : ℕ} (H : Subgroup G) : piLayer p H ≤ H :=
  iSup_le fun _ => iSup_le fun hL => hL.1.1

theorem Ke_le (p : ℕ) (K : Subgroup G) (e : G) : Prop1116.Ke p K e ≤ K :=
  sup_le ((gLAPPrimeCoreOf_le p _).trans inf_le_left) ((piLayer_le _).trans inf_le_left)

theorem core_le_Ke (p : ℕ) (K : Subgroup G) (e : G) :
    GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({e} : Set G)) ≤ Prop1116.Ke p K e :=
  le_sup_left

theorem le_Ke_of_component {p : ℕ} {K J : Subgroup G} {e : G}
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({e} : Set G)) J)
    (hπ : IsPiGroup p (barOf p J)) : J ≤ Prop1116.Ke p K e :=
  le_sup_of_le_right (le_iSup_of_le J (le_iSup_of_le ⟨hJ, hπ⟩ le_rfl))

end Generic

theorem isPGroup_center_of_core_eq_bot {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] [Finite Y]
    (hO : GLAPPrimeCore p Y = ⊥) : IsPGroup p ↥(Subgroup.center Y) := by
  intro z
  have hn : orderOf (z : Y) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  refine ⟨a, ?_⟩
  have hz' : (z : Y) ^ p ^ a ∈ Subgroup.center Y := Subgroup.pow_mem _ z.2 _
  have hord : orderOf ((z : Y) ^ p ^ a) = b := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a hp.ne_zero) ⟨b, hab⟩, hab,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos a)]
  haveI : (Subgroup.zpowers ((z : Y) ^ p ^ a)).Normal :=
    Subgroup.normal_of_le_center (by rw [Subgroup.zpowers_le]; exact hz')
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers ((z : Y) ^ p ^ a))) := by
    rw [Nat.card_zpowers, hord]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hb
  have hle := CFSG.le_pPrimeCore_of_normal_coprime inferInstance hcop
  have h1 : (z : Y) ^ p ^ a = 1 := by
    have h2 : (z : Y) ^ p ^ a ∈ GLAPPrimeCore p Y := hle (Subgroup.mem_zpowers _)
    rw [hO] at h2
    exact h2
  apply Subtype.ext
  exact h1

section TwoLift

theorem isPGroup_zpowers_two {T : Type*} [Group T] {a : T} (ha : ∃ k : ℕ, a ^ 2 ^ k = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers a) := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])

theorem mul_two_of_isNilpotent {T : Type*} [Group T] [Finite T] [Group.IsNilpotent T] {a b : T}
    (ha : ∃ k : ℕ, a ^ 2 ^ k = 1) (hb : ∃ k : ℕ, b ^ 2 ^ k = 1) :
    ∃ k : ℕ, (a * b) ^ 2 ^ k = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 T))
  haveI : Unique (Sylow 2 T) := Sylow.unique_of_normal P inferInstance
  have hmem : ∀ x : T, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ P := by
    intro x hx
    obtain ⟨Q, hQ⟩ := (isPGroup_zpowers_two hx).exists_le_sylow
    have hQP : Q = P := Subsingleton.elim Q P
    exact hQP ▸ hQ (Subgroup.mem_zpowers x)
  have hab : a * b ∈ P := P.mul_mem (hmem a ha) (hmem b hb)
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨a * b, hab⟩
  exact ⟨k, congrArg Subtype.val hk⟩

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_two_lift (hZ : IsPGroup 3 ↥(Subgroup.center Y)) (α : MulAut Y)
    {w : Y ⧸ Subgroup.center Y} (hw : ∃ k : ℕ, w ^ 2 ^ k = 1)
    (hfix : quotientCenterAut' Y α w = w) :
    ∃ y : Y, α y = y ∧ (∃ k : ℕ, y ^ 2 ^ k = 1) ∧
      (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = w := by
  obtain ⟨k, hk⟩ := hw
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · refine ⟨1, map_one α, ⟨0, by simp⟩, ?_⟩
    simpa using hk.symm
  have hxk : x ^ 2 ^ k ∈ Subgroup.center Y := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hk
  obtain ⟨j, hj⟩ := hZ ⟨x ^ 2 ^ k, hxk⟩
  have hj' : (x ^ 2 ^ k) ^ 3 ^ j = 1 := congrArg Subtype.val hj
  have h2k : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime (n := 3 ^ j) (k := 2 ^ k)
    (Nat.Coprime.pow j k (by norm_num)) h2k
  set y : Y := x ^ (3 ^ j * u) with hy
  have hy2 : y ^ 2 ^ k = 1 := by
    rw [hy, ← pow_mul, show 3 ^ j * u * 2 ^ k = (2 ^ k * 3 ^ j) * u by ring, pow_mul, pow_mul, hj',
      one_pow]
  have hmk : (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = QuotientGroup.mk x := by
    have hdm := Nat.div_add_mod (3 ^ j * u) (2 ^ k)
    rw [hu] at hdm
    rw [hy, ← hdm, QuotientGroup.mk_pow, pow_add, pow_mul, hk, one_pow, one_mul, pow_one]
  have hαy : (QuotientGroup.mk (α y) : Y ⧸ Subgroup.center Y) = QuotientGroup.mk y := by
    have h1 : quotientCenterAut' Y α (QuotientGroup.mk y) = QuotientGroup.mk (α y) := rfl
    rw [← h1, hmk]
    exact hfix
  have hz : y⁻¹ * α y ∈ Subgroup.center Y := QuotientGroup.eq.1 hαy.symm
  have hαy2 : (α y) ^ 2 ^ k = 1 := by rw [← map_pow, hy2, map_one]
  have hzpow : (y⁻¹ * α y) ^ 2 ^ k = 1 := by
    have hcomm : Commute y (y⁻¹ * α y) := (Subgroup.mem_center_iff.1 hz y)
    have e : α y = y * (y⁻¹ * α y) := by group
    have h3 : (y * (y⁻¹ * α y)) ^ 2 ^ k = 1 := by rw [← e]; exact hαy2
    rwa [hcomm.mul_pow, hy2, one_mul] at h3
  obtain ⟨i, hi⟩ := hZ ⟨y⁻¹ * α y, hz⟩
  have hi' : (y⁻¹ * α y) ^ 3 ^ i = 1 := congrArg Subtype.val hi
  have hord : orderOf (y⁻¹ * α y) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow k i (by norm_num))
      (orderOf_dvd_of_pow_eq_one hzpow) (orderOf_dvd_of_pow_eq_one hi')
  have hz1 : y⁻¹ * α y = 1 := orderOf_eq_one_iff.1 hord
  refine ⟨y, ?_, ⟨k, hy2⟩, hmk⟩
  calc α y = y * (y⁻¹ * α y) := by group
    _ = y := by rw [hz1, mul_one]

theorem exists_mem_pCoreOf_lift (hZ : IsPGroup 3 ↥(Subgroup.center Y)) (α : MulAut Y)
    {w : Y ⧸ Subgroup.center Y}
    (hw : w ∈ pCoreOf 2 (fixSub (quotientCenterAut' Y α))) :
    ∃ y : Y, y ∈ pCoreOf 2 (fixSub α) ∧ (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ᾱ := quotientCenterAut' Y α with hᾱ
  set W : Subgroup (Y ⧸ Subgroup.center Y) := pCoreOf 2 (fixSub ᾱ) with hW
  have hW2 : IsPGroup 2 ↥W := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  obtain ⟨k, hk⟩ := hW2 ⟨w, hw⟩
  have hfix : ᾱ w = w := mem_fixSub.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hw)
  obtain ⟨y, hyα, hy2, hyw⟩ := exists_two_lift hZ α ⟨k, congrArg Subtype.val hk⟩ hfix
  refine ⟨y, ?_, hyw⟩
  set π := QuotientGroup.mk' (Subgroup.center Y) with hπ
  set S : Subgroup Y := fixSub α ⊓ W.comap π with hS
  let f : ↥S →* ↥W := (π.comp S.subtype).codRestrict W (fun s => s.2.2)
  have hker : f.ker ≤ Subgroup.center ↥S := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have hs1 : π (s : Y) = 1 := congrArg Subtype.val hs
    have hsc : (s : Y) ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff _).1 hs1
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 hsc (g : Y))
  haveI : Group.IsNilpotent ↥W := hW2.isNilpotent
  haveI : Group.IsNilpotent ↥S := Subgroup.isNilpotent_of_ker_le_center f hker
  let Q : Subgroup Y :=
    { carrier := {y | y ∈ S ∧ ∃ k : ℕ, y ^ 2 ^ k = 1}
      mul_mem' := by
        rintro a b ⟨haS, ha2⟩ ⟨hbS, hb2⟩
        refine ⟨S.mul_mem haS hbS, ?_⟩
        obtain ⟨k, hk⟩ := mul_two_of_isNilpotent (a := (⟨a, haS⟩ : ↥S)) (b := (⟨b, hbS⟩ : ↥S))
          (by obtain ⟨k, hk⟩ := ha2; exact ⟨k, Subtype.ext hk⟩)
          (by obtain ⟨k, hk⟩ := hb2; exact ⟨k, Subtype.ext hk⟩)
        exact ⟨k, congrArg Subtype.val hk⟩
      one_mem' := ⟨S.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro a ⟨haS, k, hk⟩
        exact ⟨S.inv_mem haS, k, by rw [inv_pow, hk, inv_one]⟩ }
  have hQS : Q ≤ S := fun a ha => ha.1
  have hQp : IsPGroup 2 ↥Q := fun g => by
    obtain ⟨k, hk⟩ := g.2.2
    exact ⟨k, Subtype.ext hk⟩
  have hconj : ∀ g ∈ fixSub α, ∀ u ∈ Q, g * u * g⁻¹ ∈ Q := by
    rintro g hg u ⟨⟨huα, huW⟩, k, hk⟩
    have hgα : α g = g := mem_fixSub.1 hg
    have hπg : π g ∈ fixSub ᾱ := by
      rw [mem_fixSub]
      exact congrArg (fun z : Y => (QuotientGroup.mk z : Y ⧸ Subgroup.center Y)) hgα
    have hnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (fixSub ᾱ) hπg
    have huW' : π u ∈ W := huW
    refine ⟨⟨?_, ?_⟩, k, ?_⟩
    · show α (g * u * g⁻¹) = g * u * g⁻¹
      have huα' : α u = u := huα
      simp only [map_mul, map_inv, hgα, huα']
    · show π (g * u * g⁻¹) ∈ W
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hnorm (π u)).1 huW'
    · rw [conj_pow, hk, mul_one, mul_inv_cancel]
  have hFn : fixSub α ≤ Subgroup.normalizer (Q : Set Y) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact fun hu => hconj g hg u hu
    · intro hu
      have := hconj g⁻¹ ((fixSub α).inv_mem hg) _ hu
      simpa [mul_assoc] using this
  have hQF : Q ≤ fixSub α := fun a ha => ha.1.1
  have hπyW : π y ∈ W := by
    have h1 : π y = w := hyw
    rw [h1]
    exact hw
  have hyQ : y ∈ Q := ⟨⟨hyα, hπyW⟩, hy2⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQF hFn hQp hyQ

end TwoLift

section CoreLift

theorem comap_le_pPrimeCore {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {Cg Y : Type*} [Group Cg] [Finite Cg] [Group Y] (ρ : Cg →* Y)
    (hker : ∀ x : Cg, ρ x = 1 → ¬ p ∣ orderOf x)
    (Q : Subgroup Y) (hQ : IsPGroup q ↥Q)
    (hnorm : ∀ x : Cg, ρ x ∈ Subgroup.normalizer (Q : Set Y)) :
    Q.comap ρ ≤ CFSG.pPrimeCore p Cg := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hN : (Q.comap ρ).Normal := by
    refine ⟨fun r hr g => ?_⟩
    rw [Subgroup.mem_comap] at hr ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hnorm g) (ρ r)).1 hr
  have hcop : Nat.Coprime p (Nat.card (Q.comap ρ)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hzord : orderOf (x : Cg) = p := by rw [Subgroup.orderOf_coe]; exact hx
    have hρz : ρ (x : Cg) ∈ Q := x.2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQ) ⟨ρ (x : Cg), hρz⟩
    have h1 : orderOf (ρ (x : Cg)) = q ^ k := by
      rw [← Subgroup.orderOf_mk (ρ (x : Cg)) hρz]
      exact hk
    have h2 : orderOf (ρ (x : Cg)) ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, ← hzord, pow_orderOf_eq_one, map_one]
    have h3 : orderOf (ρ (x : Cg)) = 1 := by
      rcases (Nat.dvd_prime hp).1 h2 with h | h
      · exact h
      · exfalso
        rw [h1] at h
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · simp at h
          exact hp.one_lt.ne' h.symm
        · have hqp : q ∣ p := h ▸ dvd_pow_self q hkpos.ne'
          exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 hqp).symm
    have h4 : ρ (x : Cg) = 1 := orderOf_eq_one_iff.1 h3
    exact hker (x : Cg) h4 (by rw [hzord])
  exact CFSG.le_pPrimeCore_of_normal_coprime hN hcop

end CoreLift

section LiftTwo

variable {G : Type} [Group G] [Finite G]

theorem fixSub_eq_fixedSub {Y : Type} [Group Y] (α : MulAut Y) : fixSub α = fixedSub α := by
  ext x
  exact Iff.rfl

theorem lift_two_core {K : Subgroup G} {d : G} (hdN : d ∈ Subgroup.normalizer (K : Set G))
    (hd3 : d ^ 3 = 1) {y : barOf 3 K}
    (hy : y ∈ pCoreOf 2 (fixSub (barAut 3 K ⟨d, hdN⟩))) :
    ∃ (c : G) (hc : c ∈ K), c ∈ GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({d} : Set G)) ∧
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨c, hc⟩ : barOf 3 K) = y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := barAut 3 K ⟨d, hdN⟩ with hα
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({d} : Set G) with hC
  have hCK : C ≤ K := inf_le_left
  have hF : fixSub α = barX 3 K C := by
    rw [fixSub_eq_fixedSub]
    exact fixedSub_barAut_eq hd3 hdN
  set Q : Subgroup (barOf 3 K) := pCoreOf 2 (fixSub α) with hQ
  have hyF : y ∈ fixSub α := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy
  rw [hF] at hyF
  obtain ⟨c', hc'C, hc'y⟩ := Subgroup.mem_map.1 hyF
  let c₀ : ↥C := ⟨(c' : G), Subgroup.mem_subgroupOf.1 hc'C⟩
  let ρ : ↥C →* barOf 3 K := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (Subgroup.inclusion hCK)
  have hker : ∀ x : ↥C, ρ x = 1 → ¬ 3 ∣ orderOf x := by
    intro x hx h3
    have h1 : (x : G) ∈ GLAPPrimeCoreOf 3 K :=
      (mem_gLAPPrimeCoreOf_iff 3 K _).2 ⟨hCK x.2, (QuotientGroup.eq_one_iff _).1 hx⟩
    have h2 : orderOf (⟨(x : G), h1⟩ : ↥(GLAPPrimeCoreOf 3 K)) ∣ Nat.card (GLAPPrimeCoreOf 3 K) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h2
    have h4 : orderOf x = orderOf (x : G) := (Subgroup.orderOf_coe x).symm
    have h5 : orderOf x ∣ Nat.card (GLAPPrimeCoreOf 3 K) := by rw [h4]; exact h2
    exact absurd (Nat.eq_one_of_dvd_coprimes (card_gLAPPrimeCoreOf_coprime 3 K) (dvd_refl 3)
      (h3.trans h5)) (by norm_num)
  have hnorm : ∀ x : ↥C, ρ x ∈ Subgroup.normalizer (Q : Set (barOf 3 K)) := by
    intro x
    have hmem : ρ x ∈ fixSub α := by
      rw [hF]
      exact ⟨⟨(x : G), hCK x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (fixSub α) hmem
  have hle := comap_le_pPrimeCore (Nat.prime_three) (Nat.prime_two) (by norm_num) ρ hker Q
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hnorm
  have hc₀Q : c₀ ∈ Q.comap ρ := by
    have h1 : ρ c₀ = (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) c' := rfl
    rw [Subgroup.mem_comap, h1, hc'y]
    exact hy
  have hc₀core : c₀ ∈ GLAPPrimeCore 3 ↥C := hle hc₀Q
  exact ⟨(c' : G), c'.2, (mem_gLAPPrimeCoreOf_iff 3 C _).2 ⟨c₀.2, hc₀core⟩, hc'y⟩

end LiftTwo

section Cover

variable {G : Type} [Group G] [Finite G]

theorem exists_piComponent_of_barX_eq_top {p : ℕ} (hp : p.Prime) {K C : Subgroup G} (hCK : C ≤ K)
    (hC : barX p K C = ⊤) (hπ : IsPiGroup p (barOf p K)) :
    ∃ J : Subgroup G, GLAPComponent p C J ∧ barX p C J = ⊤ ∧ IsPiGroup p (barOf p J) := by
  have hq : CFSG.Open.IsQuasisimple (barOf p K) := hπ.1
  have hO : GLAPPrimeCore p (barOf p K) = ⊥ := hπ.2.1
  let e₀ : ↥(barX p K C) ≃* barOf p K := (MulEquiv.subgroupCongr hC).trans Subgroup.topEquiv
  have hF : GLAPPrimeCore p ↥(barX p K C) = ⊥ := by
    have hmap := glaPPrimeCore_map_iso p e₀
    rw [hO] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e₀.injective).1 hmap
  have hker : (barXHom p hCK).ker = GLAPPrimeCore p ↥C := by
    refine le_antisymm (barXHom_ker_le_core p hCK) ?_
    intro y hy
    have h1 := map_gLAPPrimeCore_le' p (barXHom p hCK) (barXHom_surjective p hCK)
      (Subgroup.mem_map.2 ⟨y, hy, rfl⟩)
    rw [hF, Subgroup.mem_bot] at h1
    exact h1
  let e₁ : barOf p C ≃* ↥(barX p K C) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (barXHom_surjective p hCK))
  have hq₁ : CFSG.Open.IsQuasisimple ↥(barX p K C) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₀.symm hq
  have hQq : CFSG.Open.IsQuasisimple (barOf p C) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₁.symm hq₁
  have hcomp : IsComponentOf (⊤ : Subgroup (barOf p C)) ⊤ :=
    ⟨le_rfl, IsSubnormal.refl _,
      CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
        (Subgroup.topEquiv : ↥(⊤ : Subgroup (barOf p C)) ≃* _).symm hQq⟩
  obtain ⟨J, hJ, hJtop⟩ := exists_glaPComponent_barX_eq (p := p) C hcomp
  refine ⟨J, hJ, hJtop, ?_⟩
  let φ : barOf p J ≃* barOf p K :=
    (barXEquiv hp hJ.2.1).trans ((MulEquiv.subgroupCongr hJtop).trans
      (Subgroup.topEquiv.trans (e₁.trans e₀)))
  exact isPiGroup_of_mulEquiv φ.symm hπ

theorem cover_of_barX_eq_top {p : ℕ} (hp : p.Prime) {K : Subgroup G} {e : G}
    (hCtop : barX p K (K ⊓ Subgroup.centralizer ({e} : Set G)) = ⊤)
    (hπ : IsPiGroup p (barOf p K)) :
    ∀ k ∈ K, ∃ h ∈ Prop1116.Ke p K e, h⁻¹ * k ∈ GLAPPrimeCoreOf p K := by
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({e} : Set G) with hC
  obtain ⟨J, hJ, hJtop, hJπ⟩ := exists_piComponent_of_barX_eq_top hp
    (inf_le_left : C ≤ K) hCtop hπ
  intro k hk
  have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨k, hk⟩ : barOf p K) ∈ barX p K C := by
    rw [hCtop]; exact Subgroup.mem_top _
  obtain ⟨⟨c, hcK⟩, hcC, hck⟩ := hmem
  have hcC' : c ∈ C := Subgroup.mem_subgroupOf.1 hcC
  obtain ⟨j, hj, hjn⟩ := (barX_eq_top_iff p hJ.1).1 hJtop c hcC'
  have hcKe : c ∈ Prop1116.Ke p K e := by
    have hjKe : j ∈ Prop1116.Ke p K e := le_Ke_of_component hJ hJπ hj
    have hnKe : j⁻¹ * c ∈ Prop1116.Ke p K e := core_le_Ke p K e hjn
    simpa using (Prop1116.Ke p K e).mul_mem hjKe hnKe
  refine ⟨c, hcKe, ?_⟩
  have h1 : (⟨c, hcK⟩ : ↥K)⁻¹ * ⟨k, hk⟩ ∈ GLAPPrimeCore p ↥K := QuotientGroup.eq.1 hck
  exact (mem_gLAPPrimeCoreOf_iff p K _).2 ⟨K.mul_mem (K.inv_mem hcK) hk, h1⟩

end Cover

theorem eq_top_of_map_center_eq_top {Y : Type*} [Group Y] (hperf : commutator Y = ⊤)
    {M : Subgroup Y} (hM : M.map (QuotientGroup.mk' (Subgroup.center Y)) = ⊤) : M = ⊤ := by
  have hdec : ∀ x : Y, ∃ m ∈ M, ∃ z ∈ Subgroup.center Y, x = m * z := by
    intro x
    have hx : QuotientGroup.mk' (Subgroup.center Y) x ∈
        M.map (QuotientGroup.mk' (Subgroup.center Y)) := by
      rw [hM]; exact Subgroup.mem_top _
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 hx
    exact ⟨m, hm, m⁻¹ * x, QuotientGroup.eq.1 hmx, by group⟩
  have hcomm : commutator Y ≤ M := by
    show ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ ≤ M
    rw [Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := hdec a
    obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := hdec b
    rw [commutatorElement_def, commutator_mul_central hz₁ hz₂]
    exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)
  rw [hperf] at hcomm
  exact top_le_iff.1 hcomm

theorem inputA7Gen_holds : Prop1116.InputA7Gen := by
  intro G _ _ X K B hK hBX hBn hBel hBrk hA7
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  set H : Subgroup G := ⨆ (e : G) (_ : e ∈ B) (_ : e ≠ 1), Prop1116.Ke 3 K e with hH
  have hHK : H ≤ K := iSup_le fun e => iSup_le fun _ => iSup_le fun _ => Ke_le 3 K e
  have hKe_le : ∀ e ∈ B, e ≠ 1 → Prop1116.Ke 3 K e ≤ H := fun e he he1 =>
    le_iSup_of_le e (le_iSup_of_le he (le_iSup_of_le he1 le_rfl))
  suffices hcov : ∀ k ∈ K, ∃ h ∈ H, h⁻¹ * k ∈ GLAPPrimeCoreOf 3 K from
    ((barX_eq_iff_cov hp hK.2.1 hHK).2 hcov).ge
  obtain ⟨e7⟩ := hA7
  haveI hnt7 : Nontrivial (alternatingGroup (Fin 7)) := S7.isSimple_Alt7.toNontrivial
  haveI hntQ : Nontrivial (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) :=
    e7.symm.injective.nontrivial
  haveI hntK : Nontrivial (barOf 3 K) :=
    (QuotientGroup.mk_surjective (s := Subgroup.center (barOf 3 K))).nontrivial
  have hq : CFSG.Open.IsQuasisimple (barOf 3 K) := isQuasisimple_barOf hp hK hntK
  have hO : GLAPPrimeCore 3 (barOf 3 K) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) (p := 3)
  have hPi : IsPiGroup 3 (barOf 3 K) := ⟨hq, hO, Or.inr (Or.inr ⟨rfl, ⟨e7⟩⟩)⟩
  have hperf : commutator (barOf 3 K) = ⊤ := hq.1
  have hZ3 : IsPGroup 3 ↥(Subgroup.center (barOf 3 K)) := isPGroup_center_of_core_eq_bot hp hO
  have hB3 : IsPGroup 3 ↥B := fun g => ⟨1, Subtype.ext (by simpa using hBel.2 g g.2)⟩
  let ψ : ↥B →* MulAut (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) :=
    (quotientCenterAut' (barOf 3 K)).comp ((barAut 3 K).comp (Subgroup.inclusion hBn))
  by_cases hψ : Function.Injective ψ
  ·
    have hcard : Nat.card ↥B = 9 := by
      have hle : Nat.card ↥B ≤ 9 := by
        have hinj : Function.Injective ((S7.permOfAut e7).comp ψ) :=
          (S7.permOfAut_injective e7).comp hψ
        have hR3 : IsPGroup 3 ↥((S7.permOfAut e7).comp ψ).range :=
          hB3.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
        have h9 := S7.card_le_nine hR3
        rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h9
      have hge : 9 ≤ Nat.card ↥B := by
        obtain ⟨E, hEB, -, hE⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hBrk
        have h9 := Subgroup.card_le_of_le hEB
        rw [hE] at h9
        simpa using h9
      omega
    have hgen := AltFacts.input23_2Aut_holds (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) ↥B ψ hψ
      ⟨e7⟩ hB3 hcard
    set M : Subgroup (barOf 3 K) := barX 3 K H with hM
    have hMtop : M.map (QuotientGroup.mk' (Subgroup.center (barOf 3 K))) = ⊤ := by
      refine eq_top_iff.2 (hgen.trans (iSup_le fun d => iSup_le fun hd => ?_))
      intro w hw
      have hdB : (d : G) ∈ B := d.2
      have hd1 : (d : G) ≠ 1 := fun h => hd (Subtype.ext h)
      have hdN : (d : G) ∈ Subgroup.normalizer (K : Set G) := hBn hdB
      have hd3 : (d : G) ^ 3 = 1 := hBel.2 _ hdB
      obtain ⟨y, hy, hyw⟩ := exists_mem_pCoreOf_lift hZ3 (barAut 3 K ⟨(d : G), hdN⟩) hw
      obtain ⟨c, hcK, hcC, hcy⟩ := lift_two_core hdN hd3 hy
      have hcH : c ∈ H := hKe_le _ hdB hd1 (core_le_Ke 3 K _ hcC)
      refine Subgroup.mem_map.2 ⟨y, ?_, hyw⟩
      exact ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.2 hcH, hcy⟩
    have hMeq : M = ⊤ := eq_top_of_map_center_eq_top hperf hMtop
    intro k hk
    have hmem : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨k, hk⟩ : barOf 3 K) ∈ M := by
      rw [hMeq]; exact Subgroup.mem_top _
    obtain ⟨⟨h, hhK⟩, hhH, hhk⟩ := hmem
    refine ⟨h, Subgroup.mem_subgroupOf.1 hhH, ?_⟩
    have h1 : (⟨h, hhK⟩ : ↥K)⁻¹ * ⟨k, hk⟩ ∈ GLAPPrimeCore 3 ↥K := QuotientGroup.eq.1 hhk
    exact (mem_gLAPPrimeCoreOf_iff 3 K _).2 ⟨K.mul_mem (K.inv_mem hhK) hk, h1⟩
  ·
    rw [injective_iff_map_eq_one] at hψ
    push Not at hψ
    obtain ⟨b, hb, hb1⟩ := hψ
    have heB : (b : G) ∈ B := b.2
    have he1 : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
    have heN : (b : G) ∈ Subgroup.normalizer (K : Set G) := hBn heB
    have he3 : (b : G) ^ 3 = 1 := hBel.2 _ heB
    have hβ : barAut 3 K ⟨(b : G), heN⟩ = 1 :=
      quotientCenterAut'_injective hperf (hb.trans (map_one _).symm)
    have hCtop : barX 3 K (K ⊓ Subgroup.centralizer ({(b : G)} : Set G)) = ⊤ := by
      rw [← fixedSub_barAut_eq he3 heN, hβ]
      exact eq_top_iff.2 fun x _ => rfl
    intro k hk
    obtain ⟨h, hh, hhk⟩ := cover_of_barX_eq_top hp hCtop hPi k hk
    exact ⟨h, hKe_le _ heB he1 hh, hhk⟩

end AltFacts2

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
