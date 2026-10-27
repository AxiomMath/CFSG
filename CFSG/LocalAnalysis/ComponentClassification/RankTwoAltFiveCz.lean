module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveQNormal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFivePoints

public section

open Subgroup CFSG.GH74.Uniqueness.SU.SU5 CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

attribute [local instance] CFSG.LieType.BorelTits.pCore_normal

namespace CFSG.ComponentClassification.RankTwoAltFive

section Model

def rGen₁ : J2Syl := J2Syl.x0

def rGen₂ : J2Syl := ⟨⟨0, 0, F4c.w⟩, 1⟩

def rGen₃ : J2Syl := ⟨⟨1, 1, 0⟩, Multiplicative.ofAdd 1⟩

def rGen₄ : J2Syl := ⟨⟨F4c.w, F4c.w2, 0⟩, Multiplicative.ofAdd 1⟩

theorem j2Syl_R_eq_prod : ∀ r : J2Syl, r ∈ J2Syl.R → ∃ b₁ b₂ b₃ b₄ b₅ : Bool,
    r = (if b₁ then rGen₁ else 1) * (if b₂ then rGen₂ else 1) * (if b₃ then rGen₃ else 1) *
      (if b₄ then rGen₄ else 1) * (if b₅ then J2Syl.z0 else 1) := by
  decide +kernel

theorem j2Syl_rGen :
    (rGen₁ ∈ J2Syl.R ∧ rGen₁ * rGen₁ = 1 ∧ rGen₁ ≠ 1 ∧ rGen₁ ≠ J2Syl.z0) ∧
      (rGen₂ ∈ J2Syl.R ∧ rGen₂ * rGen₂ = 1 ∧ rGen₂ ≠ 1 ∧ rGen₂ ≠ J2Syl.z0) ∧
      (rGen₃ ∈ J2Syl.R ∧ rGen₃ * rGen₃ = 1 ∧ rGen₃ ≠ 1 ∧ rGen₃ ≠ J2Syl.z0) ∧
      (rGen₄ ∈ J2Syl.R ∧ rGen₄ * rGen₄ = 1 ∧ rGen₄ ≠ 1 ∧ rGen₄ ≠ J2Syl.z0) ∧
      J2Syl.z0 * J2Syl.z0 = 1 := by
  decide +kernel

theorem j2Syl_mem_R_of_conj_x0 : ∀ m : J2Syl, (m * J2Syl.x0 * m⁻¹ = J2Syl.x0 ∨
    m * J2Syl.x0 * m⁻¹ = J2Syl.z0 * J2Syl.x0) → m ∈ J2Syl.R := by
  decide +kernel

theorem j2Syl_card_invol :
    Fintype.card {r : J2Syl // r ∈ J2Syl.R ∧ r * r = 1 ∧ r ≠ 1 ∧ r ≠ J2Syl.z0} = 10 := by
  decide +kernel

end Model

section Transport

variable {G : Type} [Group G] {f : J2Syl →* G} (hf : Function.Injective f)
include hf

theorem commute_of_commute_invol {k : G} (hkz : k * f J2Syl.z0 = f J2Syl.z0 * k)
    (hku : ∀ u ∈ J2Syl.R.map f, u * u = 1 → u ∉ zpowers (f J2Syl.z0) → k * u = u * k)
    {q : G} (hq : q ∈ J2Syl.R.map f) : k * q = q * k := by
  obtain ⟨r, hr, rfl⟩ := hq
  obtain ⟨g₁, g₂, g₃, g₄, hz2⟩ := j2Syl_rGen
  have hfz2 : f J2Syl.z0 * f J2Syl.z0 = 1 := by rw [← map_mul, hz2, map_one]
  have hc : ∀ s : J2Syl, (s ∈ J2Syl.R ∧ s * s = 1 ∧ s ≠ 1 ∧ s ≠ J2Syl.z0) →
      ∀ b : Bool, Commute k (f (if b then s else 1)) := by
    rintro s ⟨hs, hs2, hs1, hsz⟩ (_ | _)
    · show Commute k (f 1)
      rw [map_one]
      exact Commute.one_right k
    · show Commute k (f s)
      refine hku (f s) (mem_map_of_mem f hs) (by rw [← map_mul, hs2, map_one]) fun hm => ?_
      rcases eq_one_or_eq_of_mem_zpowers_of_sq hfz2 hm with h1 | h1
      · exact hs1 (hf (by rw [h1, map_one]))
      · exact hsz (hf h1)
  have hcz : ∀ b : Bool, Commute k (f (if b then J2Syl.z0 else 1)) := by
    rintro (_ | _)
    · show Commute k (f 1)
      rw [map_one]
      exact Commute.one_right k
    · exact hkz
  obtain ⟨b₁, b₂, b₃, b₄, b₅, rfl⟩ := j2Syl_R_eq_prod r hr
  simp only [map_mul]
  exact ((((hc _ g₁ b₁).mul_right (hc _ g₂ b₂)).mul_right (hc _ g₃ b₃)).mul_right
    (hc _ g₄ b₄)).mul_right (hcz b₅) |>.eq

theorem mem_map_R_of_conj {k : G} (hk : k ∈ f.range)
    (hkx : k * f J2Syl.x0 * k⁻¹ = f J2Syl.x0 ∨
      k * f J2Syl.x0 * k⁻¹ = f J2Syl.z0 * f J2Syl.x0) : k ∈ J2Syl.R.map f := by
  obtain ⟨m, rfl⟩ := hk
  refine mem_map_of_mem f (j2Syl_mem_R_of_conj_x0 m ?_)
  rcases hkx with h1 | h1
  · exact Or.inl (hf (by rw [map_mul, map_mul, map_inv]; exact h1))
  · exact Or.inr (hf (by rw [map_mul, map_mul, map_inv, map_mul]; exact h1))

theorem card_invol_map_R :
    Nat.card {y : J2Syl.R.map f // (y : G) * y = 1 ∧ (y : G) ∉ zpowers (f J2Syl.z0)} = 10 := by
  classical
  obtain ⟨-, -, -, -, hz2⟩ := j2Syl_rGen
  have hfz2 : f J2Syl.z0 * f J2Syl.z0 = 1 := by rw [← map_mul, hz2, map_one]
  set F : {r : J2Syl // r ∈ J2Syl.R ∧ r * r = 1 ∧ r ≠ 1 ∧ r ≠ J2Syl.z0} →
      {y : J2Syl.R.map f // (y : G) * y = 1 ∧ (y : G) ∉ zpowers (f J2Syl.z0)} := fun r =>
    ⟨⟨f r.1, mem_map_of_mem f r.2.1⟩, by rw [← map_mul, r.2.2.1, map_one], fun hm => by
      rcases eq_one_or_eq_of_mem_zpowers_of_sq hfz2 hm with h1 | h1
      · have h1' : f r.1 = f 1 := by rw [map_one]; exact h1
        exact r.2.2.2.1 (hf h1')
      · exact r.2.2.2.2 (hf h1)⟩ with hF
  rw [← j2Syl_card_invol, ← Nat.card_eq_fintype_card]
  refine (Nat.card_eq_of_bijective F ⟨?_, ?_⟩).symm
  · intro a b hab
    exact Subtype.ext (hf (congrArg (fun y => ((y.1 : J2Syl.R.map f) : G)) hab))
  · rintro ⟨⟨_, r, hr, rfl⟩, hy2, hyz⟩
    refine ⟨⟨r, hr, hf (by rw [map_mul, hy2, map_one]), fun h1 => hyz ?_, fun h1 => hyz ?_⟩, rfl⟩
    · show f r ∈ zpowers (f J2Syl.z0)
      rw [h1, map_one]
      exact one_mem _
    · show f r ∈ zpowers (f J2Syl.z0)
      rw [h1]
      exact mem_zpowers _

end Transport

section Generic

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_orderOf {R : Subgroup G} (hR : Nat.card R = 4) {y : G}
    (hyN : y ∈ normalizer (R : Set G)) (hyC : y ∉ centralizer (R : Set G))
    (hodd : Odd (orderOf y)) : 3 ∣ orderOf y := by
  have h24 : y ^ 24 ∈ centralizer (R : Set G) := by
    have h1 : (MulAut.toPerm R).comp R.normalizerMonoidHom (⟨y, hyN⟩ ^ 24) = 1 := by
      rw [map_pow, show (24 : ℕ) = Nat.card (Equiv.Perm R) by rw [Nat.card_perm, hR]; rfl,
        pow_card_eq_one']
    rw [mem_centralizer_iff]
    intro r hr
    have h2 := congrArg Subtype.val (Equiv.ext_iff.mp h1 ⟨r, hr⟩)
    rw [Equiv.Perm.one_apply] at h2
    have h3 : (((MulAut.toPerm R).comp R.normalizerMonoidHom (⟨y, hyN⟩ ^ 24) ⟨r, hr⟩ : R) : G) =
        y ^ 24 * r * (y ^ 24)⁻¹ := by
      show ((R.normalizerMonoidHom (⟨y, hyN⟩ ^ 24) ⟨r, hr⟩ : R) : G) = _
      rw [normalizerMonoidHom_apply_apply_coe, SubmonoidClass.coe_pow]
    rw [h3] at h2
    calc r * y ^ 24 = y ^ 24 * r * (y ^ 24)⁻¹ * y ^ 24 := by rw [h2]
      _ = y ^ 24 * r := by group
  by_contra h3
  have hcop : Nat.Coprime 24 (orderOf y) := by
    rw [show (24 : ℕ) = 2 ^ 3 * 3 from rfl]
    exact Nat.Coprime.mul_left (Nat.Coprime.pow_left 3 (Nat.coprime_comm.mp hodd.coprime_two_right))
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  apply hyC
  have hy : y = (y ^ 24) ^ (Nat.gcdA 24 (orderOf y)) *
      (y ^ orderOf y) ^ (Nat.gcdB 24 (orderOf y)) := by
    rw [← zpow_natCast, ← zpow_natCast y (orderOf y), ← zpow_mul, ← zpow_mul, ← zpow_add,
      ← Nat.gcd_eq_gcd_ab, hcop, Nat.cast_one, zpow_one]
  rw [hy, pow_orderOf_eq_one, one_zpow, mul_one]
  exact zpow_mem h24 _

theorem centralizer_inf_eq_zpowers {S Q : Subgroup G} {z : G}
    (hS : IsSylowOf 2 S (centralizer ({z} : Set G))) (hzS : z ∈ S)
    (hN : centralizer ({z} : Set G) ≤ normalizer (Q : Set G))
    (hO : oddCoreIn (centralizer ({z} : Set G)) = ⊥) (hzQ : ∀ q ∈ Q, z * q = q * z)
    (hCS : ∀ s ∈ S, (∀ q ∈ Q, s * q = q * s) → s = 1 ∨ s = z) :
    centralizer ({z} : Set G) ⊓ centralizer (Q : Set G) = zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set G) with hC
  set L := C ⊓ centralizer (Q : Set G) with hL
  have hconj : ∀ c ∈ C, ∀ l ∈ L, c * l * c⁻¹ ∈ L := by
    intro c hc l hl
    obtain ⟨hlC, hlQ⟩ := mem_inf.mp hl
    refine mem_inf.mpr ⟨mul_mem (mul_mem hc hlC) (inv_mem hc),
      mem_centralizer_iff.mpr fun q hq => ?_⟩
    have hq' : c⁻¹ * q * c ∈ Q := by
      have := (mem_normalizer_iff.mp (hN (inv_mem hc)) q).mp hq
      rwa [inv_inv] at this
    have h1 := mem_centralizer_iff.mp hlQ _ hq'
    calc q * (c * l * c⁻¹) = c * ((c⁻¹ * q * c) * l) * c⁻¹ := by group
      _ = c * (l * (c⁻¹ * q * c)) * c⁻¹ := by rw [h1]
      _ = c * l * c⁻¹ * q := by group
  have hCL : C ≤ normalizer (L : Set G) := fun c hc => mem_normalizer_iff.mpr fun l =>
    ⟨hconj c hc l, fun h => by
      have := hconj c⁻¹ (inv_mem hc) _ h
      rwa [show c⁻¹ * (c * l * c⁻¹) * c⁻¹⁻¹ = l by group] at this⟩
  have hzL : z ∈ L := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl,
    mem_centralizer_iff.mpr fun q hq => (hzQ q hq).symm⟩
  have hSL : S ⊓ L = zpowers z := by
    apply le_antisymm
    · intro s hs
      obtain ⟨hsS, hsL⟩ := mem_inf.mp hs
      rcases hCS s hsS fun q hq => (mem_centralizer_iff.mp (mem_inf.mp hsL).2 q hq).symm with
        h1 | h1
      · rw [h1]
        exact one_mem _
      · rw [h1]
        exact mem_zpowers z
    · exact zpowers_le.mpr (mem_inf.mpr ⟨hzS, hzL⟩)
  have hsyl := hS.inf_of_le_normalizer inf_le_left hCL
  rw [hSL, isSylowOf_iff] at hsyl
  obtain ⟨hzL', hz2g, hodd⟩ := hsyl
  have hLeq := AS81.eq_sup_oddCoreIn_of_central hz2g hzL'
    (zpowers_le.mpr (mem_centralizer_iff.mpr fun l hl =>
      mem_centralizer_singleton_iff.mp (mem_inf.mp hl).1))
    (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))
  have hOL : oddCoreIn L = ⊥ := by
    have hle : oddCoreIn L ≤ C := (oddCoreIn_le L).trans inf_le_left
    have hn : ((oddCoreIn L).subgroupOf C).Normal :=
      (normal_subgroupOf_iff_le_normalizer hle).mpr
        (hCL.trans (normalizer_le_normalizer_oddCoreIn L))
    have hodd' : Odd (Nat.card ((oddCoreIn L).subgroupOf C)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
      exact odd_card_oddCoreIn L
    have h1 := le_assemblyOddCore hn hodd'
    rw [eq_bot_iff]
    intro x hx
    have h2 : x ∈ oddCoreIn C :=
      ⟨⟨x, hle hx⟩, h1 (show (⟨x, hle hx⟩ : C) ∈ (oddCoreIn L).subgroupOf C from hx), rfl⟩
    rwa [hO] at h2
  have hLeq' : L = zpowers z ⊔ oddCoreIn L := hLeq
  rw [hLeq', hOL, sup_bot_eq]

end Generic

namespace Setting310

variable {G : Type} [Group G] [Finite G]
variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

section IIa

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIa

theorem ptAction_facts_of_eps_one
    (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    {z : G} {Q : Subgroup G} (hQ : QFacts (S : Subgroup G) V₀ z Q)
    (hN : centralizer ({z} : Set G) ≤ normalizer (Q : Set G)) :
    centralizer ({z} : Set G) ⊓ centralizer (Q : Set G) = zpowers z ∧
      Nat.card (points Q z) = 5 ∧
      (ptAction hN (le_refl (centralizer ({z} : Set G)))).ker =
        Q.subgroupOf (centralizer ({z} : Set G)) ∧
      Nat.card (ptAction hN (le_refl (centralizer ({z} : Set G)))).range = 60 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set G) with hCdef
  set ρ := ptAction hN (le_refl C) with hρ
  have hV₀2 : ∀ w ∈ V₀, w * w = 1 := fun w hw => h.mul_self (h.V₀_le hw)
  have hz2 : z * z = 1 := hV₀2 z hQ.z_mem_V₀
  have hz1 := hQ.z_ne_one
  have hzP : z ∈ P := hVP (h.V₀_le hQ.z_mem_V₀)
  have hzS : z ∈ (S : Subgroup G) := hPS hzP
  have hzQc : ∀ q ∈ Q, z * q = q * z := fun q hq => hQ.z_central q (hQ.le hq)
  have hSC : (S : Subgroup G) ≤ C := fun y hy =>
    mem_centralizer_singleton_iff.mpr (hQ.z_central y hy).symm
  have hQC : Q ≤ C := hQ.le.trans hSC
  obtain ⟨hQ32, -⟩ := hQ.q8d8.facts
  obtain ⟨x, hzx, hemb⟩ := h.j2Emb_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e
    hV'16 hinf hsup hV'inv S hPS hQ.z_mem_V₀ hz1
  obtain ⟨f, hf, hrange, -, hfx⟩ := id hemb
  have hZ := isZGen_f hf
  rw [hrange] at hZ
  have hzf : z = f J2Syl.z0 :=
    ((hZ.2.2 z hzS).mp fun s hs => hQ.z_central s hs).resolve_left hz1
  have hZz : IsZGen (S : Subgroup G) z := hzf ▸ hZ
  have hJ := hemb.facts hZz
  obtain ⟨R', -, -, -, -, -, huniq, -, -, -, -, -, hinv, -, -, -⟩ := hJ.RV
  have hQR' : Q = R' := huniq Q hQ.le hQ.normal hQ.q8d8
  have hfR : J2Syl.R.map f = R' := by
    refine huniq _ (hrange ▸ map_le_range f _) ?_ ((isQ8D8_map_iff hf).2 J2Syl.isQ8D8_R)
    rw [← hrange]
    rintro _ ⟨m, rfl⟩ _ ⟨r, hr, rfl⟩
    exact ⟨m * r * m⁻¹, J2Syl.R_normal m r hr, by simp⟩
  have hQf : Q = J2Syl.R.map f := hQR'.trans hfR.symm
  have hx2 : x * x = 1 := by rw [← sq]; exact hJ.x_sq
  have hxQ : x ∈ Q := by
    rw [hQR']
    exact ((hinv x hJ.x_mem).mpr (Or.inr ⟨hJ.x_not_mem, hJ.x_sq⟩)).1
  have hxz : x ∉ zpowers z := fun hm => by
    rcases eq_one_or_eq_of_mem_zpowers_of_sq hz2 hm with h1 | h1
    · exact hJ.x_not_mem (h1 ▸ one_mem P)
    · exact hJ.x_not_mem (h1 ▸ hzP)
  have hpts : Nat.card (points Q z) = 5 := by
    have h1 := card_points hQ.z_mem hz2 hz1 hzQc
    have h2 := card_invol_map_R hf
    rw [← hQf, ← hzf] at h2
    omega
  have hO := h.oddCoreIn_centralizer_eq_bot_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS hQ.z_mem_V₀ hz1 hQ.z_central
  have hCQ : C ⊓ centralizer (Q : Set G) = zpowers z :=
    centralizer_inf_eq_zpowers (isSylowOf_of_sylow_le S hSC) hzS hN hO hzQc hQ.centralizer_eq
  have hodd1 : ∀ k : C, ρ k = 1 → Odd (orderOf (k : G)) → k = 1 := by
    intro k hk hodd
    have hkQ : ∀ q ∈ Q, (k : G) * q = q * k := by
      intro q hq
      rw [hQf] at hq
      refine commute_of_commute_invol hf (by rw [← hzf]; exact mem_centralizer_singleton_iff.mp k.2)
        (fun u hu hu2 hu1 => ?_) hq
      rw [← hQf] at hu
      rw [← hzf] at hu1
      exact commute_of_ptAction_eq_one hQ.z_mem hz2 hz1 hzQc hN (le_refl C) hk hodd hu hu2 hu1
    have hkL : (k : G) ∈ C ⊓ centralizer (Q : Set G) :=
      mem_inf.mpr ⟨k.2, mem_centralizer_iff.mpr fun q hq => (hkQ q hq).symm⟩
    rw [hCQ] at hkL
    rcases eq_one_or_eq_of_mem_zpowers_of_sq hz2 hkL with h1 | h1
    · exact Subtype.ext h1
    · exfalso
      rw [h1, orderOf_eq_prime (by rw [sq]; exact hz2) hz1] at hodd
      exact Nat.not_odd_iff_even.mpr even_two hodd
  have hker2 : IsPGroup 2 ρ.ker := by
    intro k
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos ((k : C) : G)).ne'
    refine ⟨a, ?_⟩
    have hk' : ρ ((k : C) ^ 2 ^ a) = 1 := by
      rw [map_pow, MonoidHom.mem_ker.mp k.2, one_pow]
    have hodd' : Odd (orderOf (((k : C) ^ 2 ^ a : C) : G)) := by
      rw [SubmonoidClass.coe_pow, orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hab,
        Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
      exact hb
    have h1 := hodd1 _ hk' hodd'
    ext
    simpa using congrArg Subtype.val h1
  obtain ⟨S', hS'⟩ := (isSylowOf_of_sylow_le S hSC).exists_sylow_eq_subgroupOf
  have hkerS : ρ.ker ≤ (S : Subgroup G).subgroupOf C := by
    rw [← hS']
    exact hker2.le_sylow_of_normal S'
  have hker : ρ.ker = Q.subgroupOf C := by
    refine le_antisymm (fun k hk => ?_) fun q hq =>
      MonoidHom.mem_ker.mpr (ptAction_eq_one hN (le_refl C) hQ.comm_mem hq)
    have hkS : (k : G) ∈ (S : Subgroup G) := hkerS hk
    rw [mem_subgroupOf, hQf]
    refine mem_map_R_of_conj hf (hrange ▸ hkS) ?_
    rw [hfx, ← hzf]
    exact conj_eq_or_of_ptAction_eq_one hQ.z_mem hz2 hz1 hzQc hN (le_refl C)
      (MonoidHom.mem_ker.mp hk) hxQ hx2 hxz
  obtain ⟨y, hy, hyC, hyodd⟩ := exists_odd_of_not_le h.sylowR
    (le_centralizer_self_of_isElemAbelian h.elemR) hIIa
  obtain ⟨hyK, hyN⟩ := mem_inf.mp hy
  have hyz : y ∈ C := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp hyK z (h.V₀_le_A hQ.z_mem_V₀)).symm
  have h3 : 3 ∣ Nat.card ρ.range := by
    refine (three_dvd_orderOf h.cardR hyN hyC hyodd).trans (dvd_trans ?_
      (Subgroup.orderOf_dvd_natCard ρ.range (MonoidHom.mem_range.mpr ⟨⟨y, hyz⟩, rfl⟩)))
    have h1 : (⟨y, hyz⟩ : C) ^ orderOf (ρ ⟨y, hyz⟩) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
    rw [hker, mem_subgroupOf, SubmonoidClass.coe_pow] at h1
    have h4 : orderOf (y ^ orderOf (ρ ⟨y, hyz⟩)) ∣ 2 ^ 5 := by
      rw [show (2 : ℕ) ^ 5 = 32 from rfl, ← hQ32]
      exact Subgroup.orderOf_dvd_natCard Q h1
    have h5 : Odd (orderOf (y ^ orderOf (ρ ⟨y, hyz⟩))) := hyodd.of_dvd_nat (orderOf_pow_dvd _)
    exact orderOf_dvd_of_pow_eq_one (orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 5 h5.coprime_two_right) h4))
  have hV₀pt : V₀ ∈ points Q z := ⟨hQ.V₀_le, hQ.z_mem_V₀, h.card_V₀, hV₀2⟩
  obtain ⟨k, hkx, hCk⟩ := exists_conj_sylow_of_isConj S hQ.z_central hzx
  obtain ⟨w, hw, hxw⟩ := h.exists_not_commute_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS hJ.x_mem hJ.x_not_mem
  have hkz : k⁻¹ * z * k ∈ V₀ := h.conj_mem_V₀_of_not_tau hP hPC hIIa hGold hGs hP64 hVP hε
    hV'P hV'e hV'16 hinf hsup hV'inv S hPS ⟨x, hJ.x_mem, w, hw, hxw⟩ hQ.z_mem_V₀ hz1
    hQ.z_central hJ.x_mem hJ.x_not_mem hx2 hCk
  obtain ⟨eA⟩ := h.equiv
  obtain ⟨b, -, hbN, -, hbtr, -⟩ := exists_klein_three eA h.V₀_le_A h.card_V₀
  have hkz1 : k⁻¹ * z * k ≠ 1 := fun h1 => hz1 (by
    calc z = k * (k⁻¹ * z * k) * k⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  obtain ⟨j, hj⟩ := hbtr z hQ.z_mem_V₀ _ hkz hz1 hkz1
  have hh₀C : k * (b ^ j)⁻¹ ∈ C := by
    rw [mem_centralizer_singleton_iff]
    calc k * (b ^ j)⁻¹ * z = k * ((b ^ j)⁻¹ * z * b ^ j) * (b ^ j)⁻¹ := by group
      _ = k * (k⁻¹ * z * k) * (b ^ j)⁻¹ := by rw [hj]
      _ = z * (k * (b ^ j)⁻¹) := by group
  have hxV₀ : (k * (b ^ j)⁻¹)⁻¹ * x * (k * (b ^ j)⁻¹) ∈ V₀ := by
    rw [← hkx, show (k * (b ^ j)⁻¹)⁻¹ * (k * z * k⁻¹) * (k * (b ^ j)⁻¹) =
      b ^ j * z * (b ^ j)⁻¹ by group]
    exact (mem_normalizer_iff.mp (pow_mem hbN j) z).mp hQ.z_mem_V₀
  have htr : ∀ U : points Q z, ∃ σ ∈ ρ.range, σ ⟨V₀, hV₀pt⟩ = U := by
    intro U
    by_cases hU : (U : Subgroup G) = V₀
    · exact ⟨1, one_mem _, Subtype.ext hU.symm⟩
    obtain ⟨hUQ, hzU, hU4, hU2⟩ := U.2
    obtain ⟨u, huU, hu⟩ : ∃ u ∈ (U : Subgroup G), u ∉ zpowers z := by
      by_contra hno
      push Not at hno
      have h1 := card_le_of_le (show (U : Subgroup G) ≤ zpowers z from hno)
      rw [hU4, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hz2) hz1] at h1
      omega
    have huV : u ∉ V₀ := fun huV => hU ((eq_ptOf_of_mem_points U.2 hz2 hz1 huU hu).trans
      (eq_ptOf_of_mem_points hV₀pt hz2 hz1 huV hu).symm)
    have hu1 : u ≠ 1 := fun h1 => hu (h1 ▸ one_mem _)
    have huS : u ∈ (S : Subgroup G) := hQ.le (hUQ huU)
    have hu2 : u ^ 2 = 1 := by rw [sq]; exact hU2 u huU
    have huP : u ∉ P := by
      rcases (hinv u huS).mp ⟨hQR' ▸ hUQ huU, hu1, hu2⟩ with ⟨hZc, -⟩ | ⟨hP', -⟩
      · exact absurd (h.mem_V₀_of_mem_Zc hP hPC hP64 hVP hZc) huV
      · exact hP'
    obtain ⟨s, hsS, hsx⟩ := hJ.conj_invol u huS huP hu2
    have hsh : s * (k * (b ^ j)⁻¹) ∈ C := mul_mem (hSC hsS) hh₀C
    refine ⟨ρ ⟨_, hsh⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩, Subtype.ext ?_⟩
    have hmem := map_conj_mem_points (hN hsh) hsh hV₀pt
    have hu' : u ∈ V₀.map (MulAut.conj (s * (k * (b ^ j)⁻¹))).toMonoidHom := by
      rw [mem_map_equiv, MulAut.conj_symm_apply, ← hsx,
        show (s * (k * (b ^ j)⁻¹))⁻¹ * (s * x * s⁻¹) * (s * (k * (b ^ j)⁻¹)) =
          (k * (b ^ j)⁻¹)⁻¹ * x * (k * (b ^ j)⁻¹) by group]
      exact hxV₀
    exact (eq_ptOf_of_mem_points hmem hz2 hz1 hu' hu).trans
      (eq_ptOf_of_mem_points U.2 hz2 hz1 huU hu).symm
  have h5 : 5 ∣ Nat.card ρ.range := five_dvd_card_of_transitive hpts ⟨V₀, hV₀pt⟩ htr
  have hidx : Odd ((S : Subgroup G).relIndex C) := by
    have h1 := relIndex_mul_index hSC
    have h2 : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
    rw [← h1] at h2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h3 => h2 (dvd_mul_of_dvd_left h3 _))
  have hcardC : Nat.card C = (S : Subgroup G).relIndex C * 128 := by
    rw [← relIndex_mul_card (S : Subgroup G) C, inf_eq_left.mpr hSC, hJ.card_S]
  have hcardC' : Nat.card C = Nat.card ρ.range * 32 := by
    rw [card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, hker,
      Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, hQ32]
  have hdvd : Nat.card ρ.range ∣ 120 := by
    have h1 := card_subgroup_dvd_card ρ.range
    rwa [Nat.card_perm, hpts, show (5 : ℕ).factorial = 120 from rfl] at h1
  have hle : Nat.card ρ.range ≤ 120 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card ρ.range := Nat.card_pos
  obtain ⟨r, hr⟩ := hidx
  refine ⟨hCQ, hpts, hker, ?_⟩
  omega

theorem centralizer_facts_of_eps_one
    (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    {z : G} {Q : Subgroup G} (hQ : QFacts (S : Subgroup G) V₀ z Q) :
    pCoreOf 2 (centralizer ({z} : Set G)) = Q ∧
      CFSG.QuasithinUnique.CharTwo (centralizer ({z} : Set G)) ∧
      Nonempty (↥(centralizer ({z} : Set G)) ⧸ CFSG.Open.pCore 2 ↥(centralizer ({z} : Set G)) ≃*
        alternatingGroup (Fin 5)) ∧
      ∃ c : G, c * z * c⁻¹ ∈ pCoreOf 2 (centralizer ({z} : Set G)) ∧ c * z * c⁻¹ ≠ z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set G) with hCdef
  have hN := h.centralizer_le_normalizer_Q_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS hQ
  obtain ⟨hCQ, hpts, hker, h60⟩ := h.ptAction_facts_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε
    hV'P hV'e hV'16 hinf hsup hV'inv S hPS hQ hN
  set ρ := ptAction hN (le_refl C) with hρ
  have : Fintype (points Q z) := Fintype.ofFinite _
  have hrange : ρ.range = alternatingGroup (points Q z) := eq_alternatingGroup_of_card hpts h60
  have hQC : Q ≤ C := fun y hy =>
    mem_centralizer_singleton_iff.mpr (hQ.z_central y (hQ.le hy)).symm
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 5) (by rw [hQ.q8d8.facts.1]; rfl)
  have hker2 : IsPGroup 2 ρ.ker := by
    rw [hker]
    exact hQ2.comap_subtype
  have hpCore : CFSG.Open.pCore 2 C = Q.subgroupOf C := by
    rw [← hker]
    exact pCore_eq_ker ρ hpts hrange hker2
  have hpCoreOf : pCoreOf 2 C = Q := by
    show (CFSG.Open.pCore 2 C).map C.subtype = Q
    rw [hpCore, subgroupOf_map_subtype, inf_eq_left.mpr hQC]
  refine ⟨hpCoreOf, ?_, nonempty_quot_mulEquiv ρ hpts hrange (by rw [hpCore, hker]), ?_⟩
  · show C ⊓ centralizer (pCoreOf 2 C : Set G) ≤ pCoreOf 2 C
    rw [hpCoreOf, hCQ]
    exact zpowers_le.mpr hQ.z_mem
  · have hV₀2 : ∀ w ∈ V₀, w * w = 1 := fun w hw => h.mul_self (h.V₀_le hw)
    obtain ⟨v, hv, hv1, hvz⟩ := exists_ne_one_ne h.card_V₀ hV₀2 hQ.z_mem_V₀
    obtain ⟨c, hc⟩ := isConj_iff.mp (hQ.isConj v (hQ.V₀_le hv) hv1 (hV₀2 v hv))
    refine ⟨c, ?_, ?_⟩
    · rw [hc, hpCoreOf]
      exact hQ.V₀_le hv
    · rw [hc]
      exact hvz

end IIa

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
