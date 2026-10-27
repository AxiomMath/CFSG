module

public import CFSG.GH74.GLS.Stage2.Signalizer.L52Gen
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Basic
public import CFSG.GH74.GLS.Stage1.Main.Basic
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.L52Split

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage1.Main CFSG.ABGLocalTools
open scoped commutatorElement

namespace L52One


variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_pPrimeCoreOf (H : Subgroup G) (r : ℕ) :
    H ≤ normalizer ((pPrimeCoreOf r H : Subgroup G) : Set G) := by
  intro c hc
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, (CFSG.pPrimeCore_normal).conj_mem y hy ⟨c, hc⟩, rfl⟩

theorem odd_card_pPrimeCoreOf (H : Subgroup G) : Odd (Nat.card ↥(pPrimeCoreOf 2 H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥(pPrimeCoreOf 2 H) = Nat.card ↥(pPrimeCore 2 ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  rw [h1]
  exact Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥H))

variable {k : Kind} {z : G} {S T Tstar : Subgroup G} {p : ℕ} {H P : Subgroup G}

omit [Finite G] in
theorem invCover_of (hSH : S ≤ H) {Q : Subgroup G} (hQH : Q ≤ H) (hQp : IsPGroup p ↥Q)
    (hSQ : S ≤ normalizer (Q : Set G)) : InvCover p H S S Q :=
  ⟨hQH, hQp, hSQ, le_sup_of_le_left (le_inf (le_inf hSH hSQ) le_rfl)⟩

omit [Finite G] in
theorem maxInv_of (hctx : Ctx51 k z S T Tstar p H P) (hT : T = S) (hTs : Tstar = S) :
    MaxInv p H S S P := by
  have h := hctx.maxi
  rw [hT, hTs] at h
  exact h

theorem part_b (hctx : Ctx51 k z S T Tstar p H P) (hT : T = S) (hTs : Tstar = S) : Op p H ≤ P := by
  have hSH : S ≤ H := hT ▸ hctx.T_le
  have hmax := maxInv_of hctx hT hTs
  obtain ⟨hPH, hPp, hSP, -⟩ := hmax.1
  have hQp : IsPGroup p ↥(Op p H ⊔ P) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_Op p hctx.prime H) hPp
      (hPH.trans (le_normalizer_Op p H))
  have hSQ : S ≤ normalizer ((Op p H ⊔ P : Subgroup G) : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_sup (Op p H) P
      ⟨le_normalizer_Op p H (hSH ht), hSP ht⟩
  have hinv : InvCover p H S S (Op p H ⊔ P) :=
    invCover_of hSH (sup_le (Op_le p H) hPH) hQp hSQ
  have := hmax.2 _ hinv le_sup_right
  exact le_sup_left.trans this.le

theorem odd_card_sup [Fact p.Prime] (hp : p ≠ 2) (hPH : P ≤ H) (hPp : IsPGroup p ↥P) :
    Odd (Nat.card ↥(pPrimeCoreOf 2 H ⊔ P)) := by
  set O := pPrimeCoreOf 2 H with hO
  set K := O ⊔ P with hK
  have hOK : O ≤ K := le_sup_left
  have hPK : P ≤ K := le_sup_right
  have hKH : K ≤ H := sup_le (Subgroup.map_subtype_le _) hPH
  have hKN : K ≤ normalizer (O : Set G) := hKH.trans (le_normalizer_pPrimeCoreOf H 2)
  have hOn : (O.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOK).2 hKN
  have hsup : O.subgroupOf K ⊔ P.subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hOK hPK]
    exact Subgroup.subgroupOf_self K
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (O.subgroupOf K)).comp (P.subgroupOf K).subtype) := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hk : k ∈ O.subgroupOf K ⊔ P.subgroupOf K := by rw [hsup]; trivial
    rw [Subgroup.mem_sup_of_normal_left] at hk
    obtain ⟨o, ho, x, hx, rfl⟩ := hk
    refine ⟨⟨x, hx⟩, ?_⟩
    simp [(QuotientGroup.eq_one_iff o).2 ho]
  have hPp' : IsPGroup p ↥(P.subgroupOf K) := hPp.comap_subtype
  have hq : IsPGroup p (↥K ⧸ O.subgroupOf K) := hPp'.of_surjective _ hsurj
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hq
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (O.subgroupOf K)
  have hO' : Nat.card ↥(O.subgroupOf K) = Nat.card ↥O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOK).toEquiv
  rw [hcard, hn, hO']
  exact (hp_odd hp).pow.mul (odd_card_pPrimeCoreOf H)
where
  hp_odd (hp : p ≠ 2) : Odd p := ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp)

theorem part_c (ctx : Stage2Ctx G z k S) (hctx : Ctx51 k z S T Tstar p H P) (hT : T = S)
    (hTs : Tstar = S) : IsSylowOf p (P ⊓ pPrimeCoreOf 2 H) (pPrimeCoreOf 2 H) := by
  have : Fact p.Prime := ⟨hctx.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSH : S ≤ H := hT ▸ hctx.T_le
  have hmax := maxInv_of hctx hT hTs
  obtain ⟨hPH, hPp, hSP, -⟩ := hmax.1
  set O := pPrimeCoreOf 2 H with hO
  set K := O ⊔ P with hK
  have hKH : K ≤ H := sup_le (Subgroup.map_subtype_le _) hPH
  have hodd : Odd (Nat.card ↥K) := odd_card_sup hctx.odd hPH hPp
  have hS2 : IsPGroup 2 ↥S := ctx.sylow.isPGroup
  have hSK : S ≤ normalizer (K : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_sup O P
      ⟨le_normalizer_pPrimeCoreOf H 2 (hSH hs), hSP hs⟩
  obtain ⟨P', hP'syl, hPP', hSP'⟩ := exists_invariant_sylowOf_containing (p := p) (q := 2) hS2 hSK
    (fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)) le_sup_right hPp hSP
  have hP'H : P' ≤ H := hP'syl.le.trans hKH
  have hinv : InvCover p H S S P' := invCover_of hSH hP'H hP'syl.isPGroup hSP'
  have hEq : P' = P := hmax.2 _ hinv hPP'
  rw [hEq] at hP'syl
  exact hP'syl.inf_of_le_normalizer le_sup_left (hKH.trans (le_normalizer_pPrimeCoreOf H 2))

theorem part_d_bar (ctx : Stage2Ctx G z k S) (hctx : Ctx51 k z S T Tstar p H P) (hT : T = S)
    (hTs : Tstar = S) :
    ∀ D ∈ pCore 2 (HBar H), ∀ g : ↥H, g ∈ P.subgroupOf H →
      D * (QuotientGroup.mk g : HBar H) = (QuotientGroup.mk g : HBar H) * D := by
  have : Fact p.Prime := ⟨hctx.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSH : S ≤ H := hT ▸ hctx.T_le
  have hmax := maxInv_of hctx hT hTs
  obtain ⟨hPH, hPp, hSP, -⟩ := hmax.1
  have hSsyl : IsSylowOf 2 S H := (sylow_top_of_central ctx.central ctx.sylow).of_le hSH le_top
  obtain ⟨Q, hQ⟩ := hSsyl.exists_sylow_eq_subgroupOf
  let Q' : Sylow 2 (HBar H) := Q.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H))
  have hQ' : (Q' : Subgroup (HBar H)) = (Q : Subgroup ↥H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) :=
    rfl
  intro D hD g hg
  have hDQ : D ∈ (Q' : Subgroup (HBar H)) :=
    (IsPGroup.le_sylow_of_normal (pCore_isPGroup (p := 2) (G := HBar H)) Q') hD
  rw [hQ'] at hDQ
  obtain ⟨q, hq, rfl⟩ := hDQ
  have hqS : (q : G) ∈ S := by
    have : q ∈ (Q : Subgroup ↥H) := hq
    rw [hQ] at this
    exact this
  have hgP : (g : G) ∈ P := hg
  have hqgP : q * g * q⁻¹ ∈ P.subgroupOf H := by
    show (q : G) * (g : G) * (q : G)⁻¹ ∈ P
    exact (Subgroup.mem_normalizer_iff.1 (hSP hqS) _).1 hgP
  set Pb : Subgroup (HBar H) := (P.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) with hPbar
  have hPbarp : IsPGroup p ↥Pb := (hPp.comap_subtype).map _
  set c : HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H) q * QuotientGroup.mk g *
    (QuotientGroup.mk' (pPrimeCore 2 ↥H) q)⁻¹ * (QuotientGroup.mk g)⁻¹ with hc
  have hcP : c ∈ Pb := by
    refine Pb.mul_mem ?_ (Pb.inv_mem ⟨g, hg, rfl⟩)
    refine ⟨q * g * q⁻¹, hqgP, ?_⟩
    simp
  have hcD : c ∈ pCore 2 (HBar H) := by
    have h1 : (QuotientGroup.mk g : HBar H) * (QuotientGroup.mk' (pPrimeCore 2 ↥H) q)⁻¹ *
        (QuotientGroup.mk g)⁻¹ ∈ pCore 2 (HBar H) := by
      have := (CFSG.pCore_normal (p := 2) (G := HBar H)).conj_mem _ ((pCore 2 (HBar H)).inv_mem hD)
        (QuotientGroup.mk g)
      simpa using this
    have : c = QuotientGroup.mk' (pPrimeCore 2 ↥H) q * ((QuotientGroup.mk g : HBar H) *
        (QuotientGroup.mk' (pPrimeCore 2 ↥H) q)⁻¹ * (QuotientGroup.mk g)⁻¹) := by
      simp only [hc]; group
    rw [this]
    exact (pCore 2 (HBar H)).mul_mem hD h1
  have hc1 : c = 1 := by
    obtain ⟨n, hn⟩ := hPbarp ⟨c, hcP⟩
    obtain ⟨m, hm⟩ := (pCore_isPGroup (p := 2) (G := HBar H)) ⟨c, hcD⟩
    have hn' : c ^ (p ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hm' : c ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
    have hcop : Nat.Coprime (p ^ n) (2 ^ m) :=
      Nat.Coprime.pow n m ((Nat.coprime_primes hctx.prime Nat.prime_two).mpr hctx.odd)
    have := (pow_gcd_eq_one (a := c)).mpr ⟨hn', hm'⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have : QuotientGroup.mk' (pPrimeCore 2 ↥H) q * QuotientGroup.mk g =
      QuotientGroup.mk g * QuotientGroup.mk' (pPrimeCore 2 ↥H) q := by
    calc _ = c * (QuotientGroup.mk g * QuotientGroup.mk' (pPrimeCore 2 ↥H) q) := by
          simp only [hc]; group
      _ = _ := by rw [hc1, one_mul]
  exact this

theorem part_d (ctx : Stage2Ctx G z k S) (hctx : Ctx51 k z S T Tstar p H P) (hT : T = S)
    (hTs : Tstar = S) : ⁅O22Of H, P⁆ ≤ pPrimeCoreOf 2 H := by
  have hmax := maxInv_of hctx hT hTs
  obtain ⟨hPH, -, -, -⟩ := hmax.1
  rw [Subgroup.commutator_le]
  rintro d ⟨d', hd', rfl⟩ g hg
  have hd'' : (QuotientGroup.mk d' : HBar H) ∈ pCore 2 (HBar H) := hd'
  have hg' : (⟨g, hPH hg⟩ : ↥H) ∈ P.subgroupOf H := hg
  have hcomm := part_d_bar ctx hctx hT hTs _ hd'' _ hg'
  have hk : ⁅d', (⟨g, hPH hg⟩ : ↥H)⁆ ∈ pPrimeCore 2 ↥H := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥H), MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  exact ⟨_, hk, rfl⟩

theorem part_e (ctx : Stage2Ctx G z k S) (hctx : Ctx51 k z S T Tstar p H P) (hT : T = S)
    (hTs : Tstar = S) :
    barIn H P ≤ centralizer ((centralizer ((layer (HBar H) : Subgroup (HBar H)) : Set (HBar H)) :
      Subgroup (HBar H)) : Set (HBar H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax := maxInv_of hctx hT hTs
  obtain ⟨hPH, hPp, -, -⟩ := hmax.1
  have hO : pPrimeCore 2 (HBar H) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hpodd : Odd p := hctx.prime.eq_two_or_odd'.resolve_left hctx.odd
  rintro a ⟨g', hg', rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨n, hn⟩ := (hPp.comap_subtype) ⟨g', hg'⟩
  have hn' : g' ^ (p ^ n) = 1 := by
    have h2 := congrArg (fun y : ↥(P.subgroupOf H) => (y : ↥H)) hn
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact h2
  have ham : (QuotientGroup.mk' (pPrimeCore 2 ↥H) g') ^ (p ^ n) = 1 := by
    rw [← map_pow, hn', map_one]
  have hD : ∀ d ∈ pCore 2 (HBar H), d * QuotientGroup.mk' (pPrimeCore 2 ↥H) g' =
      QuotientGroup.mk' (pPrimeCore 2 ↥H) g' * d := fun d hd =>
    part_d_bar ctx hctx hT hTs d hd g' hg'
  exact centralizes_centralizer_layer hO (hpodd.pow) ham hD x (Subgroup.mem_centralizer_iff.mpr
    (fun h hh => Subgroup.mem_centralizer_iff.mp hx h hh))


end L52One

theorem lemma5_2One_thm : Lemma5_2One := by
  intro G _ _ z k S ctx T Tstar p H P hctx h
  obtain ⟨-, hT, hTs⟩ := h
  exact ⟨L52One.part_b hctx hT hTs, fun _ => L52One.part_c ctx hctx hT hTs,
    L52One.part_d ctx hctx hT hTs, L52One.part_e ctx hctx hT hTs⟩

end CFSG.GH74.GLS.Stage2.Signalizer
