module

public import CFSG.GH74.Generic.S3.V1Inner
public import CFSG.GH74.Generic.S3.NoNormalMinus
public import CFSG.GH74.KGroups.L3EpsOutExp

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open CFSG.QuasithinUnique.Setup.X5 (normalizerAct normalizerAct_of_mem
  mem_centralizer_of_normalizerAct_eq_one)
open CFSG.GH74.KGroups.L3Eps (l3eps_wreathed l3eps_pow_mem_inner l3eps_unique_central_involution)

section Eps

variable {G : Type} [Group G] [Finite G]

theorem v1_inner_of_congEps {t : StatedLieTag} {p f : ℕ} {v w : G} {Iv Iw Ivw P : Subgroup G}
    (C : Conf2A G t p f v w Iv Iw Ivw P)
    (hcong : (t = .PSL → p ^ f % 4 = 1) ∧ (t = .PSU → p ^ f % 4 = 3))
    {v₁ : G} (hv₁R : v₁ ∈ P ⊓ Ivw) (hv₁2 : v₁ * v₁ = 1) (hv₁1 : v₁ ≠ 1) (hv₁v : v₁ ≠ v)
    (hsq : (∃ u ∈ P ⊓ Ivw, u * u = 1 ∧ u ≠ 1 ∧ u ≠ v ∧ ∃ s ∈ P ⊓ Ivw, s * s = u) →
      ∃ s ∈ P ⊓ Ivw, s * s = v₁) :
    ∃ m ∈ Iw, v₁ * m⁻¹ ∈ centralizer (Iw : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 := C.prime.2.1
  have h5 := C.prime.2.2
  have hv2 : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [C.v_inv, pow_two] at this
  have hv1 : v ≠ 1 := fun h => by
    have := C.v_inv
    rw [h, orderOf_one] at this
    omega
  have hvI : v ∈ Ivw := C.le_vw C.v_mem
  have hR : IsSylowOf 2 (P ⊓ Ivw) Ivw :=
    C.sylow_vw.inf_of_le_normalizer C.comp_vw.1.1 C.comp_vw.le_normalizer
  obtain ⟨Q, hQ⟩ := hR
  have hodd := C.odd_vw
  set π : ↥Ivw →* ↥Ivw ⧸ center ↥Ivw := QuotientGroup.mk' (center ↥Ivw) with hπ
  obtain ⟨hR2, hRmax⟩ := isMax_map_center Q hodd
  have hinj := injOn_map_center Q hodd
  have hQ2 : IsPGroup 2 (Q : Subgroup ↥Ivw) := Q.isPGroup'
  have hQZ : ∀ z : ↥Ivw, z ∈ (Q : Subgroup ↥Ivw) → z ∈ center ↥Ivw → z = 1 :=
    fun z hzQ hzZ => eq_one_of_mem_pGroup_of_mem_center_odd hQ2 hodd hzQ hzZ
  have hsqQ : ∀ q ∈ (Q : Subgroup ↥Ivw), π q * π q = 1 → q * q = 1 := by
    intro q hq h
    have h1 : π (q * q) = 1 := by rw [map_mul]; exact h
    exact hQZ _ (Q.mul_mem hq hq) ((QuotientGroup.eq_one_iff _).1 h1)
  have hQmem : ∀ g : G, g ∈ P ⊓ Ivw → ∃ q : ↥Ivw, q ∈ (Q : Subgroup ↥Ivw) ∧ (q : G) = g := by
    intro g hg
    rw [← hQ] at hg
    obtain ⟨q, hq, rfl⟩ := hg
    exact ⟨q, hq, rfl⟩
  have hmemP : ∀ q : ↥Ivw, q ∈ (Q : Subgroup ↥Ivw) → (q : G) ∈ P ⊓ Ivw := fun q hq => by
    rw [← hQ]
    exact ⟨q, hq, rfl⟩
  have hX : StatedClassicalModel (↥Ivw ⧸ center ↥Ivw) t 3 p f := by
    rcases C.tag with rfl | rfl
    · exact stated_of_lieModel_PSL C.model_vw
    · exact stated_of_lieModel_PSU C.model_vw
  have hXw : StatedClassicalModel (↥Iw ⧸ center ↥Iw) t 3 p f := by
    rcases C.tag with rfl | rfl
    · exact stated_of_lieModel_PSL C.model_w
    · exact stated_of_lieModel_PSU C.model_w
  obtain ⟨n, hWr, hs1, hs2⟩ := l3eps_wreathed C.tag hp2 h5 hcong hX hR2 hRmax
  have huniq := l3eps_unique_central_involution C.tag hp2 hX hR2 hRmax
  set Rb : Subgroup (↥Ivw ⧸ center ↥Ivw) := (Q : Subgroup ↥Ivw).map π with hRb
  have hπmem : ∀ q : ↥Ivw, q ∈ (Q : Subgroup ↥Ivw) → π q ∈ Rb := fun q hq => ⟨q, hq, rfl⟩
  obtain ⟨qv, hqv, hqvG⟩ := hQmem v ⟨C.v_P, hvI⟩
  obtain ⟨q₁, hq₁, hq₁G⟩ := hQmem v₁ hv₁R
  have hqv2 : qv * qv = 1 := Subtype.ext (by simp only [Subgroup.coe_mul, hqvG, hv2]; rfl)
  have hq₁2 : q₁ * q₁ = 1 := Subtype.ext (by simp only [Subgroup.coe_mul, hq₁G, hv₁2]; rfl)
  have hqv1 : qv ≠ 1 := fun h => hv1 (by rw [← hqvG, h]; rfl)
  have hq₁1 : q₁ ≠ 1 := fun h => hv₁1 (by rw [← hq₁G, h]; rfl)
  have hq₁qv : q₁ ≠ qv := fun h => hv₁v (by rw [← hq₁G, ← hqvG, h])
  have hπ1 : ∀ q ∈ (Q : Subgroup ↥Ivw), q ≠ 1 → π q ≠ 1 := fun q hq hq1 h =>
    hq1 (hinj hq (one_mem _) (by rw [h, map_one]))
  let z : ↥Rb := ⟨π qv, hπmem qv hqv⟩
  let v₁b : ↥Rb := ⟨π q₁, hπmem q₁ hq₁⟩
  have hzc : ∀ r : ↥Rb, z * r = r * z := by
    rintro ⟨x, q, hq, rfl⟩
    apply Subtype.ext
    show π qv * π q = π q * π qv
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (qv : G) * (q : G) = (q : G) * (qv : G)
    rw [hqvG]
    exact (C.v_central q (hmemP q hq).1).symm
  have hz2 : z * z = 1 := by
    apply Subtype.ext
    show π qv * π qv = 1
    rw [← map_mul, hqv2, map_one]
  have hz1 : z ≠ 1 := fun h => hπ1 qv hqv hqv1 (congrArg Subtype.val h)
  have hv₁b2 : v₁b * v₁b = 1 := by
    apply Subtype.ext
    show π q₁ * π q₁ = 1
    rw [← map_mul, hq₁2, map_one]
  have hv₁b1 : v₁b ≠ 1 := fun h => hπ1 q₁ hq₁ hq₁1 (congrArg Subtype.val h)
  have hv₁bz : v₁b ≠ z := fun h =>
    hq₁qv (hinj hq₁ hqv (congrArg Subtype.val h))
  have hsq' : (∃ u : ↥Rb, u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧ ∃ t : ↥Rb, t * t = u) →
      ∃ t : ↥Rb, t * t = v₁b := by
    rintro ⟨⟨x, qu, hqu, rfl⟩, hu2, hu1, huz, ⟨x', qt, hqt, rfl⟩, htu⟩
    have hqu2 : qu * qu = 1 := hsqQ qu hqu (congrArg Subtype.val hu2)
    have hqt2 : qt * qt = qu := by
      apply hinj (Q.mul_mem hqt hqt) hqu
      rw [map_mul]
      exact congrArg Subtype.val htu
    have hqu1 : qu ≠ 1 := fun h => hu1 (Subtype.ext (by
      show π qu = 1
      rw [h, map_one]))
    have hquqv : qu ≠ qv := fun h => huz (Subtype.ext (by
      show π qu = π qv
      rw [h]))
    obtain ⟨s, hsm, hss⟩ := hsq ⟨(qu : G), hmemP qu hqu, congrArg Subtype.val hqu2,
      fun h => hqu1 (Subtype.ext h), fun h => hquqv (Subtype.ext (h.trans hqvG.symm)),
      (qt : G), hmemP qt hqt, congrArg Subtype.val hqt2⟩
    obtain ⟨qs, hqs, hqsG⟩ := hQmem s hsm
    refine ⟨⟨π qs, hπmem qs hqs⟩, Subtype.ext ?_⟩
    show π qs * π qs = π q₁
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show (qs : G) * (qs : G) = (q₁ : G)
    rw [hqsG, hq₁G]
    exact hss
  have hK : 0 < 2 ^ n := Nat.two_pow_pos n
  obtain ⟨y, hy⟩ := hWr.exists_root hK huniq hzc hz2 hz1 hv₁b2 hv₁b1 hv₁bz hsq'
  obtain ⟨x, qy, hqy, rfl⟩ := y
  have h2n : 2 * 2 ^ n = 2 ^ (n + 1) := by ring
  have hqy_pow : qy ^ 2 ^ (n + 1) = q₁ := by
    apply hinj (Subgroup.pow_mem _ hqy _) hq₁
    rw [map_pow]
    rw [← h2n]
    exact congrArg Subtype.val hy
  have hvy : (qy : G) ^ 2 ^ (n + 1) = v₁ := by
    have := congrArg (fun q : ↥Ivw => (q : G)) hqy_pow
    simpa [hq₁G] using this
  have hyP : (qy : G) ∈ P := (hmemP qy hqy).1
  have hyN : (qy : G) ∈ normalizer (Iw : Set G) := C.comp_w.le_normalizer (C.sylow_w.le hyP)
  have hv₁N : v₁ ∈ normalizer (Iw : Set G) := C.comp_w.le_normalizer (C.sylow_w.le hv₁R.1)
  have hIwq : IsQuasisimple ↥Iw := C.comp_w.1.isQuasisimple
  have : Group.IsPerfect ↥Iw := hIwq.1
  let σ : MulAut (↥Iw ⧸ center ↥Iw) := normalizerAct Iw ⟨(qy : G), hyN⟩
  obtain ⟨k, hk⟩ := hQ2 ⟨qy, hqy⟩
  have hqyk : (qy : G) ^ 2 ^ k = 1 := by
    have := congrArg (fun x : ↥(Q : Subgroup ↥Ivw) => ((x : ↥Ivw) : G)) hk
    simpa using this
  have hσk : σ ^ 2 ^ k = 1 := by
    have h1 : (⟨(qy : G), hyN⟩ : ↥(normalizer (Iw : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hqyk)
    show normalizerAct Iw ⟨(qy : G), hyN⟩ ^ 2 ^ k = 1
    rw [← map_pow, h1, map_one]
  have hσinner := l3eps_pow_mem_inner C.tag hp2 h5 hcong hXw ⟨hs1, hs2⟩ hσk
  have hσpow : σ ^ 2 ^ (n + 1) = normalizerAct Iw ⟨v₁, hv₁N⟩ := by
    show normalizerAct Iw ⟨(qy : G), hyN⟩ ^ 2 ^ (n + 1) = _
    rw [← map_pow]
    congr 1
    apply Subtype.ext
    exact hvy
  rw [hσpow] at hσinner
  obtain ⟨k0, hk0⟩ := hσinner
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective k0
  have hmN : (m : G) ∈ normalizer (Iw : Set G) := Subgroup.le_normalizer m.2
  refine ⟨(m : G), m.2, ?_⟩
  have hmact : normalizerAct Iw ⟨(m : G), hmN⟩ = normalizerAct Iw ⟨v₁, hv₁N⟩ := by
    rw [← hk0]
    exact normalizerAct_of_mem Iw m.2
  have hc : normalizerAct Iw (⟨v₁, hv₁N⟩ * ⟨(m : G), hmN⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, hmact, mul_inv_cancel]
  exact mem_centralizer_of_normalizerAct_eq_one Iw hc

end Eps

@[expose] def B_S3_v1_inner_neg : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (t : StatedLieTag) (p f : ℕ) (v w : G) (Iv Iw Ivw P : Subgroup G),
      Conf2A G t p f v w Iv Iw Ivw P →
      ((t = .PSL → p ^ f % 4 = 3) ∧ (t = .PSU → p ^ f % 4 = 1)) →
      ∀ v₁ : G, v₁ ∈ P ⊓ Ivw → v₁ * v₁ = 1 → v₁ ≠ 1 → v₁ ≠ v →
        ((∃ u ∈ P ⊓ Ivw, u * u = 1 ∧ u ≠ 1 ∧ u ≠ v ∧ ∃ s ∈ P ⊓ Ivw, s * s = u) →
          ∃ s ∈ P ⊓ Ivw, s * s = v₁) →
        ∃ m ∈ Iw, v₁ * m⁻¹ ∈ centralizer (Iw : Set G)

theorem b_S3_v1_inner_of_neg (h : B_S3_v1_inner_neg) : B_S3_v1_inner := by
  intro G _ _ hG t p f v w Iv Iw Ivw P hconf v₁ hv₁R hv₁2 hv₁1 hv₁v hsq
  have hodd : (p ^ f) % 2 = 1 :=
    Nat.odd_iff.1 ((hconf.prime.1.odd_of_ne_two hconf.prime.2.1).pow)
  have h4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by omega
  rcases hconf.tag with rfl | rfl
  · rcases h4 with h1 | h3
    · exact v1_inner_of_congEps hconf ⟨fun _ => h1, fun h => absurd h (by decide)⟩ hv₁R hv₁2 hv₁1
        hv₁v hsq
    · exact h G hG .PSL p f v w Iv Iw Ivw P hconf ⟨fun _ => h3, fun h => absurd h (by decide)⟩ v₁
        hv₁R hv₁2 hv₁1 hv₁v hsq
  · rcases h4 with h1 | h3
    · exact h G hG .PSU p f v w Iv Iw Ivw P hconf ⟨fun h => absurd h (by decide), fun _ => h1⟩ v₁
        hv₁R hv₁2 hv₁1 hv₁v hsq
    · exact v1_inner_of_congEps hconf ⟨fun h => absurd h (by decide), fun _ => h3⟩ hv₁R hv₁2 hv₁1
        hv₁v hsq

end CFSG.GH74.Generic.S3
