module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.CentralFixed

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open CFSG.ABGLocalTools Equiv Equiv.Perm

@[expose] def sigma7 : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5

theorem sigma7_mem : sigma7 ∈ alternatingGroup (Fin 7) :=
  Equiv.Perm.mem_alternatingGroup.2 (by simp [sigma7, Equiv.Perm.sign_mul])

theorem orderOf_sigma7 : orderOf (⟨sigma7, sigma7_mem⟩ : alternatingGroup (Fin 7)) = 4 := by
  rw [Subgroup.orderOf_mk, show (4 : ℕ) = 2 ^ (1 + 1) by norm_num]
  exact orderOf_eq_prime_pow (by decide : ¬ sigma7 ^ 2 ^ 1 = 1) (by decide)

theorem exists_conj_mem_sylow {Y : Type} [Group Y] [Finite Y] (R : Sylow 2 Y) {g : Y}
    (hg : IsPGroup 2 (zpowers g)) : ∃ h : Y, h * g * h⁻¹ ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R₀, hR₀⟩ := hg.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq Y R₀ R
  have hR : (R : Subgroup Y) = (R₀ : Subgroup Y).map (MulAut.conj h).toMonoidHom := by
    rw [← hh, Sylow.coe_subgroup_smul]
    rfl
  refine ⟨h, ?_⟩
  show h * g * h⁻¹ ∈ (R : Subgroup Y)
  rw [hR]
  exact ⟨g, hR₀ (mem_zpowers g), rfl⟩

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

namespace Setup

variable (S : Setup L z t F L1 N)

include S

omit [Finite G] in
theorem piY_eq_one_of_mem_L1 {l : G} (hl : l ∈ L1) (hlX : l ∈ normalizer (L1 : Set G)) :
    piY L1 ⟨l, hlX⟩ = 1 := by
  have hlC : l ∈ centralizer (L1 : Set G) :=
    mem_centralizer_iff.2 fun h hh => S.L1_comm h hh l hl
  have : (QuotientGroup.mk ⟨l, hlX⟩ : Xbar L1) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hlC)
  rw [piY_apply, this, QuotientGroup.mk_one]

theorem card_sylowQ_le (hL2 : ¬ 256 ∣ Nat.card L) {Q : Subgroup G}
    (hQ : IsSylowOf 2 Q (centralizer ({z} : Set G))) : Nat.card Q ≤ 256 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCL : Nat.card (centralizer ({z} : Set G)) = Nat.card L * 2 := by
    rw [centralizer_z_eq S.one]
    exact card_sup_zpowers S.one le_rfl
  have h128 : 128 ∣ Nat.card L :=
    (S.nd.N_two).trans (Subgroup.card_dvd_of_le (inf_le_right : normalizer (F : Set G) ⊓ L ≤ L))
  obtain ⟨m, hm⟩ := h128
  have hmodd : Odd m := by
    by_contra h
    exact hL2 ⟨m / 2, by rcases Nat.even_or_odd m with ⟨k, hk⟩ | ho
                         · omega
                         · exact absurd ho h⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hQ.isPGroup
  have hdvd : Nat.card Q ∣ Nat.card (centralizer ({z} : Set G)) :=
    Subgroup.card_dvd_of_le hQ.le
  rw [hCL, hm] at hdvd
  have hcop : Nat.Coprime (Nat.card Q) m := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hmodd)
  have h256 : Nat.card Q ∣ 256 := by
    refine hcop.dvd_of_dvd_mul_right ?_
    have : 128 * m * 2 = 256 * m := by ring
    rwa [this] at hdvd
  exact Nat.le_of_dvd (by norm_num) h256

theorem exists_order_four (hA7 : NormQuotA7 (normalizer (F : Set G) ⊓ L) F) :
    ∃ g₀ : Ybar L1, orderOf g₀ = 4 := by
  obtain ⟨ψ, hψ, hker⟩ := id hA7
  obtain ⟨d₀, hd₀⟩ := hψ ⟨sigma7, sigma7_mem⟩
  have hdX : (d₀ : G) ∈ normalizer (L1 : Set G) := S.D_le_X d₀.2
  refine ⟨piY L1 ⟨d₀, hdX⟩, ?_⟩
  rw [← orderOf_sigma7, orderOf_eq_orderOf_iff]
  intro n
  have hpowX : (⟨(d₀ : G), hdX⟩ : ↥(normalizer (L1 : Set G))) ^ n =
      ⟨(d₀ : G) ^ n, (normalizer (L1 : Set G)).pow_mem hdX n⟩ := rfl
  have hDpow : ψ (d₀ ^ n) = (⟨sigma7, sigma7_mem⟩ : alternatingGroup (Fin 7)) ^ n := by
    rw [map_pow, hd₀]
  have hkerD : ψ (d₀ ^ n) = 1 ↔ (d₀ : G) ^ n ∈ F := by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    rfl
  rw [← hDpow, hkerD, ← map_pow, hpowX]
  constructor
  · intro h
    have hcomm : (d₀ : G) * z = z * (d₀ : G) := (S.one.z_comm _ (mem_inf.1 d₀.2).2).symm
    refine S.mem_F_of_piY_eq_one hA7 (c := ⟨(d₀ : G) ^ n, _⟩) ?_ h
    exact mem_centralizer_singleton_iff.2
      (Commute.pow_left (show Commute (d₀ : G) z from hcomm) n).eq
  · intro h
    exact S.piY_eq_one_of_mem_L1 (S.F_le h) _

theorem exists_order_four_mem_sylow (hA7 : NormQuotA7 (normalizer (F : Set G) ⊓ L) F)
    (R : Sylow 2 (Ybar L1)) : ∃ g₁ ∈ R, orderOf g₁ = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g₀, hg₀⟩ := S.exists_order_four hA7
  have hpg : IsPGroup 2 (zpowers g₀) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg₀]; norm_num)
  obtain ⟨h, hh⟩ := exists_conj_mem_sylow R hpg
  refine ⟨h * g₀ * h⁻¹, hh, ?_⟩
  have := MulEquiv.orderOf_eq (MulAut.conj h) g₀
  rw [MulAut.conj_apply] at this
  rw [this, hg₀]

theorem F_le_sylowQ {P : Subgroup G} (hP : IsSylowOf 2 P (normalizer (L1 : Set G))) :
    F ≤ P ⊓ centralizer ({z} : Set G) := fun f hf =>
  mem_inf.2 ⟨S.L1_le_of_isSylowOf hP (S.F_le hf),
    mem_centralizer_singleton_iff.2 (S.one.z_comm f (S.nd.F_le hf)).symm⟩

theorem card_sylow_piY_le (hL2 : ¬ 256 ∣ Nat.card L) {P : Subgroup G}
    (hP : IsSylowOf 2 P (normalizer (L1 : Set G)))
    (hT : IsSylowOf 2 (P ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)))
    (R : Sylow 2 (Ybar L1))
    (hRQ : ∀ y ∈ R, ∃ q ∈ P ⊓ centralizer ({z} : Set G), ∃ hq : q ∈ normalizer (L1 : Set G),
      piY L1 ⟨q, hq⟩ = y) : Nat.card ↥(R : Subgroup (Ybar L1)) ≤ 16 := by
  set Q := P ⊓ centralizer ({z} : Set G) with hQ
  have hQX : Q ≤ normalizer (L1 : Set G) := inf_le_left.trans hP.le
  let f : ↥Q →* Ybar L1 := (piY L1).comp (Subgroup.inclusion hQX)
  have hFQ := S.F_le_sylowQ hP
  have hRle : (R : Subgroup (Ybar L1)) ≤ f.range := by
    intro y hy
    obtain ⟨q, hqQ, hqX, rfl⟩ := hRQ y hy
    exact ⟨⟨q, hqQ⟩, rfl⟩
  have hker : F.subgroupOf Q ≤ f.ker := by
    intro a ha
    have haF : (a : G) ∈ F := Subgroup.mem_subgroupOf.1 ha
    exact S.piY_eq_one_of_mem_L1 (S.F_le haF) (hQX a.2)
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 : Nat.card ↥(F.subgroupOf Q) = 16 := by
    rw [← S.nd.F_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFQ).toEquiv
  have h3 : 16 ≤ Nat.card f.ker := h2 ▸ Subgroup.card_le_of_le hker
  have h4 : Nat.card Q ≤ 256 := S.card_sylowQ_le hL2 hT
  have h5 : Nat.card ↥(R : Subgroup (Ybar L1)) ≤ Nat.card f.range := Subgroup.card_le_of_le hRle
  have h6 : 16 * Nat.card f.range ≤ 256 := by
    calc 16 * Nat.card f.range ≤ Nat.card f.ker * Nat.card f.range := Nat.mul_le_mul_right _ h3
      _ = Nat.card Q := h1
      _ ≤ 256 := h4
  omega

theorem weakly_closed (hFix : FixFour L F) (hA7 : NormQuotA7 (normalizer (F : Set G) ⊓ L) F)
    (hL2 : ¬ 256 ∣ Nat.card L) (hcen : ∀ y : Ybar L1, y * piY L1 S.zX = piY L1 S.zX * y)
    {P : Subgroup G} (hP : IsSylowOf 2 P (normalizer (L1 : Set G)))
    (hT : IsSylowOf 2 (P ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G))) :
    ∀ g : G, (∀ x ∈ L1, g * x * g⁻¹ ∈ P) → ∀ x ∈ L1, g * x * g⁻¹ ∈ L1 := by
  intro g hg
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, hxn⟩ := hcon
  have hPX : P ≤ normalizer (L1 : Set G) := hP.le
  have hL1P : L1 ≤ P := S.L1_le_of_isSylowOf hP
  obtain ⟨R, hRP, hRQ⟩ := S.exists_sylow_piY hcen hP hT
  have hR16 := S.card_sylow_piY_le hL2 hP hT R hRQ
  obtain ⟨g₁, hg₁R, hg₁o⟩ := S.exists_order_four_mem_sylow hA7 R
  have hℓP : g * x * g⁻¹ ∈ P := hg x hx
  have hℓ2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [S.L1_sq x hx]; group
  have hcard16 := S.card_centralizer_L1_involution hFix hcen hP hT hℓP hℓ2 hxn
  set L' : Subgroup G := L1.map (MulAut.conj g).toMonoidHom with hL'
  have hL'mem : ∀ y, y ∈ L' ↔ ∃ w ∈ L1, y = g * w * g⁻¹ := by
    intro y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  have hL'P : L' ≤ P := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := (hL'mem y).1 hy
    exact hg w hw
  have hL'X : L' ≤ normalizer (L1 : Set G) := hL'P.trans hPX
  have hL'card : Nat.card L' = 256 := by
    rw [hL', Subgroup.card_map_of_injective (MulAut.conj g).injective, S.L1_card]
  have hL'sq : ∀ y ∈ L', y * y = 1 := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := (hL'mem y).1 hy
    calc g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
      _ = 1 := by rw [S.L1_sq w hw]; group
  let ρ : ↥L' →* Ybar L1 := (piY L1).comp (Subgroup.inclusion hL'X)
  have hρR : ∀ a : ↥L', ρ a ∈ (R : Subgroup (Ybar L1)) := fun a => hRP a (hL'P a.2)
  have hkey : ∀ a : ↥ρ.ker, ((a.1 : ↥L') : G) ∈ L1 ⊓ centralizer ({g * x * g⁻¹} : Set G) := by
    intro a
    have hy1 : ((a.1 : ↥L') : G) ∈ L1 :=
      S.mem_L1_of_piY_eq_one hP.isPGroup hL1P (hL'P a.1.2) (hL'X a.1.2) a.2
    refine mem_inf.2 ⟨hy1, mem_centralizer_singleton_iff.2 ?_⟩
    obtain ⟨w, hw, hwy⟩ := (hL'mem _).1 a.1.2
    rw [hwy]
    calc g * w * g⁻¹ * (g * x * g⁻¹) = g * (w * x) * g⁻¹ := by group
      _ = g * (x * w) * g⁻¹ := by rw [S.L1_comm w hw x hx]
      _ = g * x * g⁻¹ * (g * w * g⁻¹) := by group
  have hkerle : Nat.card ρ.ker ≤ 16 := by
    rw [← hcard16]
    refine Nat.card_le_card_of_injective (fun a : ↥ρ.ker => ⟨_, hkey a⟩) (fun a b h => ?_)
    have h' := congrArg (fun u : ↥(L1 ⊓ centralizer ({g * x * g⁻¹} : Set G)) => (u : G)) h
    exact Subtype.ext (Subtype.ext h')
  have h1 := Subgroup.card_ker_mul_card_range ρ
  rw [hL'card] at h1
  have hrange16 : 16 ≤ Nat.card ρ.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ρ.ker * Nat.card ρ.range < 16 * 16 := by
      calc Nat.card ρ.ker * Nat.card ρ.range ≤ 16 * Nat.card ρ.range :=
            Nat.mul_le_mul_right _ hkerle
        _ < 16 * 16 := by omega
    omega
  have hρle : ρ.range ≤ (R : Subgroup (Ybar L1)) := by
    rintro _ ⟨a, rfl⟩
    exact hρR a
  have hρeq : ρ.range = (R : Subgroup (Ybar L1)) :=
    Subgroup.eq_of_le_of_card_ge hρle (by omega)
  have hg₁range : g₁ ∈ ρ.range := hρeq ▸ hg₁R
  obtain ⟨a, rfl⟩ := hg₁range
  have ha : a * a = 1 := Subtype.ext (hL'sq a a.2)
  have : ρ a ^ 2 = 1 := by rw [pow_two, ← map_mul, ha, map_one]
  have := orderOf_dvd_of_pow_eq_one this
  rw [hg₁o] at this
  omega

end Setup

end CFSG.EvenSporadicStandard.M23Std
