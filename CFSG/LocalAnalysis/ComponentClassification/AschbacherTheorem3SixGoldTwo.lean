module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixGoldOne

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem oddCore_map_eq_bot {G C : Subgroup X} [C.Normal] (hGn : G.Normal) (hCG : C ≤ G)
    (hC2 : IsPGroup 2 C) (hcen : C ≤ Subgroup.centralizer (G : Set X))
    (hO : CFSG.oddCore G = ⊥) : CFSG.oddCore (G.map (QuotientGroup.mk' C)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' C with hπ
  have hkerπ : π.ker = C := QuotientGroup.ker_mk' C
  set Gb := G.map π with hGb
  set Rb : Subgroup (X ⧸ C) := (CFSG.oddCore Gb).map Gb.subtype with hRb
  have hRbodd : Odd (Nat.card Rb) := by
    rw [hRb, Subgroup.card_map_of_injective Gb.subtype_injective]
    exact odd_card_oddCore _
  have hRbn : Rb.Normal := by
    have : (CFSG.oddCore Gb).Characteristic := OddCore.characteristic _
    have hGbn : Gb.Normal := hGn.map π (QuotientGroup.mk'_surjective C)
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    intro y _
    exact mem_normalizer_map_of_characteristic _ (by
      rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top y)
  set R := Rb.comap π with hRdef
  have hRn : R.Normal := hRbn.comap π
  have hCR : C ≤ R := fun z hz => by
    show π z ∈ Rb
    have h1 : π z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [h1]
    exact Rb.one_mem
  have hRG : R ≤ G := by
    intro x hx
    have h1 : π x ∈ Gb := Subgroup.map_subtype_le _ hx
    have h2 := mk_mem_map_iff.mp h1
    rwa [sup_eq_left.mpr hCG] at h2
  have hRmap : R.map π = Rb := Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective C) Rb
  have hidx : C.relIndex R = Nat.card Rb := by
    have h := Subgroup.relIndex_ker (K := R) π
    rwa [hkerπ, hRmap] at h
  set N := C.subgroupOf R with hNdef
  have hNn : N.Normal := Subgroup.Normal.subgroupOf inferInstance R
  have hNcard : Nat.card N = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCR).toEquiv
  have hNidx : N.index = Nat.card Rb := hidx
  obtain ⟨k₂, hk₂⟩ := hC2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hNcard, hk₂, hNidx]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hRbodd)
  obtain ⟨K', hK'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set K := K'.map R.subtype with hKdef
  have hKR : K ≤ R := Subgroup.map_subtype_le _
  have hKcard : Nat.card K = Nat.card Rb := by
    rw [hKdef, Subgroup.card_map_of_injective R.subtype_injective, ← hNidx]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hK'.card_mul_card.trans N.card_mul_index.symm)
  have hKodd : Odd (Nat.card K) := hKcard ▸ hRbodd
  have hdec : ∀ r ∈ R, ∃ c ∈ C, ∃ k ∈ K, r = c * k := by
    intro r hr
    have h1 : (⟨r, hr⟩ : R) ∈ ((N ⊔ K' : Subgroup R) : Set R) := by
      rw [hK'.sup_eq_top]; trivial
    rw [Subgroup.normal_mul] at h1
    obtain ⟨n, hn, k, hk, hnk⟩ := Set.mem_mul.mp h1
    exact ⟨n, Subgroup.mem_subgroupOf.mp hn, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val hnk).symm⟩
  have hKC : ∀ x ∈ K, x ∈ C → x = 1 := fun x hxK hxC => by
    obtain ⟨e, he⟩ := hC2 ⟨x, hxC⟩
    exact eq_one_of_two_pow_of_odd hxK hKodd (by simpa using congrArg Subtype.val he)
  have hodd_mem : ∀ r ∈ R, Odd (orderOf r) → r ∈ K := by
    intro r hr hodd
    obtain ⟨c, hc, k, hk, rfl⟩ := hdec r hr
    have hck : Commute c k :=
      (Subgroup.mem_centralizer_iff.mp (hcen hc) k (hRG (hKR hk))).symm
    have h1 : (c * k) ^ orderOf (c * k) = 1 := pow_orderOf_eq_one _
    rw [hck.mul_pow] at h1
    have h2 : c ^ orderOf (c * k) ∈ K := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact K.inv_mem (K.pow_mem hk _)
    have h3 : c ^ orderOf (c * k) = 1 := hKC _ h2 (C.pow_mem hc _)
    obtain ⟨e, he⟩ := hC2 ⟨c, hc⟩
    have he' : c ^ (2 ^ e) = 1 := by simpa using congrArg Subtype.val he
    have hdvd : orderOf c ∣ Nat.gcd (2 ^ e) (orderOf (c * k)) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one he') (orderOf_dvd_of_pow_eq_one h3)
    rw [Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd), Nat.dvd_one,
      orderOf_eq_one_iff] at hdvd
    rw [hdvd, one_mul]
    exact hk
  have hKN : G ≤ Subgroup.normalizer (K : Set X) := by
    have hconj : ∀ x ∈ G, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
      intro x hx k hk
      apply hodd_mem _ (hRn.conj_mem k (hKR hk) x)
      have h1 := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective k
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      rw [h1]
      exact Odd.of_dvd_nat hKodd (Subgroup.orderOf_dvd_natCard K hk)
    intro x hx
    exact mem_normalizer_of_conj_le (hconj x hx) (by simpa using hconj x⁻¹ (G.inv_mem hx))
  have hKbot : K = ⊥ := by
    have hle := le_map_oddCore (hKR.trans hRG) hKN hKodd
    rwa [hO, Subgroup.map_bot, le_bot_iff] at hle
  have hRb1 : Nat.card Rb = 1 := by rw [← hKcard, hKbot, Subgroup.card_bot]
  have hRbbot : Rb = ⊥ := Subgroup.card_eq_one.mp hRb1
  exact (Subgroup.map_eq_bot_iff_of_injective _ Gb.subtype_injective).mp hRbbot

theorem pCore_map_eq_bot {G C : Subgroup X} [C.Normal] (hC : C = pCoreOf 2 G) (hGn : G.Normal) :
    CFSG.Open.pCore 2 (G.map (QuotientGroup.mk' C)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' C with hπ
  set Gb := G.map π with hGb
  have hCG : C ≤ G := hC ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 G
  have hC2 : IsPGroup 2 C := hC ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  set Pb : Subgroup (X ⧸ C) := (CFSG.Open.pCore 2 Gb).map Gb.subtype with hPb
  have hPb2 : IsPGroup 2 Pb := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := Gb)).map _
  have hPbn : Pb.Normal := by
    have : (CFSG.Open.pCore 2 Gb).Characteristic := CFSG.LieType.BorelTits.pCore_characteristic 2
    have hGbn : Gb.Normal := hGn.map π (QuotientGroup.mk'_surjective C)
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    intro y _
    exact mem_normalizer_map_of_characteristic _ (by
      rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top y)
  set P := Pb.comap π with hPdef
  have hPn : P.Normal := hPbn.comap π
  have hPG : P ≤ G := by
    intro x hx
    have h1 : π x ∈ Gb := Subgroup.map_subtype_le _ hx
    have h2 := mk_mem_map_iff.mp h1
    rwa [sup_eq_left.mpr hCG] at h2
  have hP2 : IsPGroup 2 P := fun x => by
    obtain ⟨a, ha⟩ := hPb2 ⟨π x, x.2⟩
    have h1 : (x : X) ^ (2 ^ a) ∈ C := by
      have h2 : π ((x : X) ^ (2 ^ a)) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val ha
      exact (QuotientGroup.eq_one_iff _).mp h2
    obtain ⟨b, hb⟩ := hC2 ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
    rwa [pow_add, pow_mul]
  have hPC : P ≤ C := hC ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPG
    (fun x _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x) hP2
  have hPbbot : Pb = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    have hx : x ∈ P := hy
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff x).mpr (hPC hx))
  exact (Subgroup.map_eq_bot_iff_of_injective _ Gb.subtype_injective).mp hPbbot

theorem center_eq_bot_of_cores {G : Subgroup X} (hO : CFSG.oddCore G = ⊥)
    (hP : CFSG.Open.pCore 2 G = ⊥) : Subgroup.center G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Zc := (Subgroup.center G).map G.subtype with hZc
  have hab : IsMulCommutative Zc := inferInstance
  have hZG : Zc ≤ G := Subgroup.map_subtype_le _
  have hGZ : G ≤ Subgroup.normalizer (Zc : Set X) := fun x hx =>
    mem_normalizer_map_of_characteristic _ (Subgroup.le_normalizer hx)
  have hZ2 := isPGroup_of_abelian hZG hGZ hab hO
  have hle : Zc ≤ pCoreOf 2 G := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZG hGZ hZ2
  rw [pCoreOf, hP, Subgroup.map_bot, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ G.subtype_injective).mp hle

end CFSG.ComponentClassification.AschbacherTheorem3
