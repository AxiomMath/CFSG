module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.I417Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.I417Gen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.I417Auto
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverConsumers
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofIn

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.Asc83Table CFSG.Blueprint Subgroup


set_option linter.unusedSectionVars false

theorem pow3_aux : ∀ j : ℕ, j ≤ 3 → 9 ≤ 3 ^ j → 3 ^ j ≠ 9 → 3 ^ j = 27 := by decide

set_option maxHeartbeats 4000000 in
theorem item417InJ3Rest_holds :
    Item417InJ3Rest := by
  intro G _ _ L A E c m hconf hZ3 he0
  obtain ⟨e0⟩ := he0
  obtain ⟨hS4, hp2, hLc, hbound, hQ, hAN, hnf, hnS, hinner, hcL⟩ := hconf
  have hm4 : m ≤ 4 := hbound A E c m hQ
  obtain ⟨hmax, hAm, hAC, hc3, hE27, hEA, T, hTmem, hTE⟩ := hQ
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hmax.1
  have hAe' := isElemAbelian_iff.1 hAe
  have hq : IsQuasisimple ↥L := hLc.1
  have hθ := theta_eq_bot_of_center_three hq hZ3
  have hTri : IsTripleCover ↥L NativeSporadic.J3 := ⟨hZ3, ⟨e0⟩⟩
  have hcA : c ∈ A := (hAC ▸ Subgroup.mem_zpowers c : c ∈ A ⊓ Subgroup.centralizer (L : Set G)).1
  set ρ : ↥A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAN) with hρ
  have hρapp : ∀ (a : ↥A) (x : ↥L), (((ρ a) x : ↥L) : G) = (a : G) * x * (a : G)⁻¹ :=
    fun a x => rfl
  have hinn : ∀ a : ↥A, ∃ k : ↥L, ρ a = MulAut.conj k := by
    intro a
    have h1 := hinner (a : G) a.2
    apply inner_of_theta_inner hθ
    by_contra hnot
    exact h1 ⟨hAN a.2, hnot⟩
  have hkerρ : ρ.ker = (Subgroup.zpowers c).subgroupOf A := by
    ext ⟨a, ha⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hAC]
    constructor
    · intro h
      refine ⟨ha, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      have h1 := hρapp ⟨a, ha⟩ ⟨x, hx⟩
      rw [h, MulAut.one_apply] at h1
      have h2 : x = a * x * a⁻¹ := h1
      calc x * a = (a * x * a⁻¹) * a := by rw [← h2]
        _ = a * x := by group
    · rintro ⟨-, hc⟩
      ext x
      rw [hρapp, MulAut.one_apply]
      have h1 := Subgroup.mem_centralizer_iff.1 hc x x.2
      rw [← h1]
      group
  have hker3 : Nat.card ρ.ker = 3 := by
    have hzA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
    rw [hkerρ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzA).toEquiv, Nat.card_zpowers, hc3]
  have hrange3 : 3 * Nat.card ρ.range = 3 ^ m := by
    have h := Subgroup.card_ker_mul_card_range ρ
    rw [hker3, Nat.card_congr (Equiv.refl _)] at h
    rw [← hAm, h]
  set K : Subgroup ↥L := ρ.range.comap (MulAut.conj : ↥L →* MulAut ↥L) with hK
  have hmemK : ∀ k : ↥L, k ∈ K ↔ MulAut.conj k ∈ ρ.range := fun k => Iff.rfl
  have hZK : Subgroup.center ↥L ≤ K := fun z hz => by
    rw [hmemK, CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof.conj_eq_one_iff_mem_center.mpr hz]
    exact ρ.range.one_mem
  set κ : K →* MulAut ↥L := (MulAut.conj : ↥L →* MulAut ↥L).comp K.subtype with hκ
  have hκker : κ.ker = (Subgroup.center ↥L).subgroupOf K := by
    ext ⟨k, hk⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof.conj_eq_one_iff_mem_center (k := k)
  have hκrange : κ.range = ρ.range := by
    ext σ
    constructor
    · intro hσ
      obtain ⟨⟨k, hk⟩, rfl⟩ := MonoidHom.mem_range.mp hσ
      exact (hmemK k).mp hk
    · intro hσ
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hσ
      obtain ⟨k, hk⟩ := hinn a
      have hkK : k ∈ K := by rw [hmemK, ← hk]; exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨⟨k, hkK⟩, hk.symm⟩
  have hKcard : Nat.card K = 3 ^ m := by
    have h := Subgroup.card_ker_mul_card_range κ
    rw [hκker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv, hZ3, hκrange] at h
    rw [← h, ← hrange3]
  have hρcomm : ∀ σ ∈ ρ.range, ∀ τ ∈ ρ.range, σ * τ = τ * σ := by
    intro σ hσ τ hτ
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hσ
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hτ
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext (hAe'.1 a a.2 b b.2))
  have hρcube : ∀ σ ∈ ρ.range, σ ^ 3 = 1 := by
    intro σ hσ
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hσ
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (by simpa using hAe'.2 a a.2)
    rw [this, map_one]
  have hKcomm : ∀ x ∈ K, ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center ↥L := by
    intro x hx y hy
    rw [← CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof.conj_eq_one_iff_mem_center, map_mul,
      map_mul, map_mul, map_inv, map_inv, hρcomm _ ((hmemK x).mp hx) _ ((hmemK y).mp hy),
      mul_inv_cancel_right, mul_inv_cancel]
  have hKcube : ∀ x ∈ K, x ^ 3 ∈ Subgroup.center ↥L := by
    intro x hx
    rw [← CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof.conj_eq_one_iff_mem_center, map_pow]
    exact hρcube _ ((hmemK x).mp hx)
  have hAK : ∀ a ∈ A, ∃ k ∈ K, ∀ x : ↥L, (a : G) * x * (a : G)⁻¹ = k * x * (k : G)⁻¹ := by
    intro a ha
    obtain ⟨k, hk⟩ := hinn ⟨a, ha⟩
    refine ⟨k, by rw [hmemK, ← hk]; exact MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩, fun x => ?_⟩
    have h1 := hρapp ⟨a, ha⟩ x
    rw [hk] at h1
    exact h1.symm
  have hAcentral : ∀ P : Subgroup ↥L, K ≤ P → (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) →
      ∀ a ∈ A, ∀ p ∈ P, a * (p : G) = p * a := by
    intro P hKP hP a ha p hp
    obtain ⟨k, hk, hkx⟩ := hAK a ha
    have h1 := hkx p
    have h2 : (k : ↥L) * p = p * k := hP k (hKP hk) p hp
    have h3 : (k : G) * p = p * k := congrArg Subtype.val h2
    have h4 : (a : G) * p * (a : G)⁻¹ = p := by rw [h1, h3]; group
    calc (a : G) * p = (a * p * a⁻¹) * a := by group
      _ = p * a := by rw [h4]
  have hmaxtrick : ∀ P : Subgroup ↥L, K ≤ P → (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) →
      (∀ x ∈ P, x ^ 3 = 1) → P.map L.subtype ≤ A := by
    intro P hKP hPc hP3
    have hP'e : CFSG.Assembly.IsElemAbelian 3 (P.map L.subtype) := by
      rw [isElemAbelian_iff]
      refine ⟨?_, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        exact congrArg Subtype.val (hPc x hx y hy)
      · rintro _ ⟨x, hx, rfl⟩
        exact congrArg Subtype.val (hP3 x hx)
    have hsup := isElemAbelian_sup_of_commute hAe hP'e (by
      rintro a ha _ ⟨p, hp, rfl⟩
      exact hAcentral P hKP hPc a ha p hp)
    exact le_sup_right.trans (hmax.2 hsup le_sup_left)
  have hE27c : Nat.card E = 27 := hE27.2
  have hm3 : 3 ≤ m := by
    by_contra h
    have h1 : Nat.card E ≤ Nat.card A := Subgroup.card_le_of_le hEA
    rw [hE27c, hAm] at h1
    have : 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hm34 : m = 3 ∨ m = 4 := by omega
  set π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  have hker_π : π.ker = Subgroup.center ↥L := QuotientGroup.ker_mk' _
  have hker_K : π.ker ≤ K := by rw [hker_π]; exact hZK
  have hKbar_cube : ∀ x ∈ K, π x ^ 3 = 1 := by
    intro x hx
    rw [← map_pow, ← MonoidHom.mem_ker, hker_π]
    exact hKcube x hx
  have hKbar_comm : ∀ x ∈ K, ∀ y ∈ K, π x * π y = π y * π x := by
    intro x hx y hy
    have h1 : π (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, hker_π]
      exact hKcomm x hx y hy
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π x * π y = (π x * π y * (π x)⁻¹ * (π y)⁻¹) * (π y * π x) := by group
      _ = π y * π x := by rw [h1, one_mul]
  have hKbar_ea : CFSG.Assembly.IsElemAbelian 3 (K.map π) := by
    rw [isElemAbelian_iff]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact hKbar_comm x hx y hy
    · rintro _ ⟨x, hx, rfl⟩
      exact hKbar_cube x hx
  have hKbar_card : Nat.card ↥(K.map π) * 3 = Nat.card K := by
    have := card_map_mul_ker π K hker_K
    rw [hker_π, hZ3] at this
    exact this.symm
  rcases hm34 with rfl | rfl
  · exfalso
    have hEA_eq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [hAm, hE27c]; norm_num)
    have hK27 : Nat.card K = 27 := by rw [hKcard]; norm_num
    have hKbar9 : Nat.card ↥(K.map π) = 9 := by omega
    have hD1 : ∀ x : ↥L ⧸ Subgroup.center ↥L, x ^ 3 = 1 → (∀ d ∈ K.map π, x * d = d * x) →
        x ∈ K.map π := by
      intro xb hx3 hxc
      by_contra hxn
      have hzp_ea : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers xb) := by
        rw [isElemAbelian_iff]
        refine ⟨?_, ?_⟩
        · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
          exact (Commute.zpow_zpow_self xb i j).eq
        · rintro _ ⟨i, rfl⟩
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
      have hcomm : ∀ a ∈ K.map π, ∀ b ∈ Subgroup.zpowers xb, a * b = b * a := by
        intro a ha b hb
        obtain ⟨j, rfl⟩ := hb
        have hc : Commute xb a := hxc a ha
        exact ((hc.symm.zpow_right j).eq)
      set Pb : Subgroup (↥L ⧸ Subgroup.center ↥L) := K.map π ⊔ Subgroup.zpowers xb with hPb
      have hPb_ea : CFSG.Assembly.IsElemAbelian 3 Pb :=
        isElemAbelian_sup_of_commute hKbar_ea hzp_ea hcomm
      have hxPb : xb ∈ Pb := Subgroup.mem_sup_right (Subgroup.mem_zpowers xb)
      have hKPb : K.map π ≤ Pb := le_sup_left
      have hPb27 : Nat.card Pb = 27 := by
        obtain ⟨j, hj3, hj⟩ := card_eq_pow_of_isElemAbelian_of_equiv_J3 e0 hPb_ea
        have hge : 9 ≤ Nat.card Pb := hKbar9 ▸ Subgroup.card_le_of_le hKPb
        have hne : Nat.card Pb ≠ 9 := by
          intro h9
          have : K.map π = Pb :=
            Subgroup.eq_of_le_of_card_ge hKPb (by rw [h9, hKbar9])
          exact hxn (this ▸ hxPb)
        rw [hj] at hge hne ⊢
        exact pow3_aux j hj3 hge hne
      set P : Subgroup ↥L := Pb.comap π with hP
      have hZP : Subgroup.center ↥L ≤ P := by
        intro z hz
        rw [hP, Subgroup.mem_comap]
        have : π z = 1 := (QuotientGroup.eq_one_iff z).2 hz
        rw [this]; exact Pb.one_mem
      have hker_P : π.ker ≤ P := by rw [hker_π]; exact hZP
      have hPmap : P.map π = Pb := Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective _) Pb
      have hP81 : Nat.card P = 3 ^ 4 := by
        have := card_map_mul_ker π P hker_P
        rw [hPmap, hPb27, hker_π, hZ3] at this
        exact this.trans (by norm_num)
      have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center ↥L := by
        intro x hx y hy
        rw [← hker_π, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
        have h1 := (isElemAbelian_iff.1 hPb_ea).1 (π x) hx (π y) hy
        rw [h1]; group
      have hPcube : ∀ x ∈ P, x ^ 3 ∈ Subgroup.center ↥L := by
        intro x hx
        rw [← hker_π, MonoidHom.mem_ker, map_pow]
        exact (isElemAbelian_iff.1 hPb_ea).2 (π x) hx
      have hPea : CFSG.Assembly.IsElemAbelian 3 P :=
        ks217J3CoverPreimage_holds ↥L hq hTri P hZP hP81 hPcomm hPcube
      have hKP : K ≤ P := fun x hx => hKPb (Subgroup.mem_map_of_mem π hx)
      have hPA := hmaxtrick P hKP (isElemAbelian_iff.1 hPea).1 (isElemAbelian_iff.1 hPea).2
      have := Subgroup.card_le_of_le hPA
      rw [Subgroup.card_map_of_injective L.subtype_injective, hP81, hAm] at this
      norm_num at this
    obtain ⟨hTL, hTpi, hETn⟩ := mem_invariantPiSubgroups_iff.1 hTmem
    set T0 : Subgroup ↥L := T.subgroupOf L with hT0
    have hmemT0 : ∀ t : ↥L, t ∈ T0 ↔ (t : G) ∈ T := fun t => Subgroup.mem_subgroupOf
    have hT0card : Nat.card T0 = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
    have hT2 : IsPGroup 2 T0 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hn : Nat.card T ≠ 0 := Nat.card_pos.ne'
      have hpow : Nat.card T = 2 ^ (Nat.card T).primeFactorsList.length :=
        Nat.eq_prime_pow_of_unique_prime_dvd hn fun {d} hd hdd => hTpi ⟨d, hd⟩ hdd
      exact IsPGroup.of_card (n := (Nat.card T).primeFactorsList.length) (hT0card.trans hpow)
    have hKnorm : K ≤ Subgroup.normalizer (T0 : Set ↥L) := by
      intro k hk
      have hρk : MulAut.conj k ∈ ρ.range := (hmemK k).1 hk
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hρk
      have haE : (a : G) ∈ E := hEA_eq ▸ a.2
      have hn := Subgroup.mem_normalizer_iff.1 (hETn haE)
      rw [Subgroup.mem_normalizer_iff]
      intro t
      rw [hmemT0, hmemT0]
      have h1 : ((k * t * k⁻¹ : ↥L) : G) = (a : G) * (t : G) * (a : G)⁻¹ := by
        have := hρapp a t
        rw [ha] at this
        exact this
      rw [h1]
      exact hn (t : G)
    have hKbar_norm : K.map π ≤ Subgroup.normalizer ((T0.map π : Subgroup _) : Set _) :=
      (Subgroup.map_mono hKnorm).trans (Subgroup.le_normalizer_map π)
    have hnc : ¬ (T0.map π) ≤ Subgroup.centralizer ((K.map π : Subgroup _) : Set _) := by
      intro hle
      apply hTE
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro a haE
      have haA : a ∈ A := hEA haE
      obtain ⟨k, hk, hkx⟩ := hAK a haA
      set t' : ↥L := ⟨t, hTL ht⟩ with ht'
      have ht'T : t' ∈ T0 := (hmemT0 t').2 ht
      have hcomm := Subgroup.mem_centralizer_iff.1 (hle (Subgroup.mem_map_of_mem π ht'T))
        (π k) (Subgroup.mem_map_of_mem π hk)
      have hz : k * t' * k⁻¹ * t'⁻¹ ∈ Subgroup.center ↥L := by
        rw [← hker_π, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
        rw [hcomm]
        group
      have hzT0 : k * t' * k⁻¹ * t'⁻¹ ∈ T0 := by
        refine mul_mem ?_ (inv_mem ht'T)
        exact (Subgroup.mem_normalizer_iff.1 (hKnorm hk) t').1 ht'T
      have hz3 : (k * t' * k⁻¹ * t'⁻¹) ^ 3 = 1 := by
        have := pow_card_eq_one' (G := Subgroup.center ↥L) (x := ⟨_, hz⟩)
        rw [hZ3] at this
        exact congrArg Subtype.val this
      have hz1 : k * t' * k⁻¹ * t'⁻¹ = 1 := by
        obtain ⟨j, hj⟩ := hT2 ⟨_, hzT0⟩
        have hj' : (k * t' * k⁻¹ * t'⁻¹) ^ (2 ^ j) = 1 := congrArg Subtype.val hj
        have h1 : orderOf (k * t' * k⁻¹ * t'⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
        have h2 : orderOf (k * t' * k⁻¹ * t'⁻¹) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
        have hcop : Nat.Coprime 3 (2 ^ j) := Nat.Coprime.pow_right j (by norm_num)
        exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
      have h3 : k * t' * k⁻¹ = t' := by
        have := congrArg (· * t') hz1
        simpa using this
      have h4 := hkx t'
      have h3' : (k : G) * (t' : G) * (k : G)⁻¹ = (t : G) := congrArg Subtype.val h3
      have h5 : (a : G) * t * (a : G)⁻¹ = t := h4.trans h3'
      calc (a : G) * t = (a * t * a⁻¹) * a := by group
        _ = t * a := by rw [h5]
    have e0' : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .J3 := e0
    have hdatum : Res417Three.IsDatum417 (↥L ⧸ Subgroup.center ↥L) (K.map π) :=
      ⟨hKbar_ea, hD1, K.map π, le_rfl, by omega, T0.map π, hT2.map π, hKbar_norm, hnc⟩
    have h27 := Res417Four.k417OutJ3_holds _ (Res417Three.IsDatum417.map e0' hdatum)
    rw [Subgroup.card_map_of_injective e0'.injective, hKbar9] at h27
    exact absurd h27 (by norm_num)
  · have hKea : CFSG.Assembly.IsElemAbelian 3 K :=
      ks217J3CoverPreimage_holds ↥L hq hTri K hZK hKcard hKcomm hKcube
    have hAeq : K.map L.subtype = A :=
      Subgroup.eq_of_le_of_card_ge
        (hmaxtrick K le_rfl (isElemAbelian_iff.1 hKea).1 (isElemAbelian_iff.1 hKea).2)
        (by rw [Subgroup.card_map_of_injective L.subtype_injective, hKcard, hAm])
    have hKea' : IsElementaryAbelian 3 (K.map π) :=
      isElemAbelian_iff_isElementaryAbelian.1 hKbar_ea
    have e0' : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .J3 := e0
    obtain ⟨kk, hkk, hFK, hNn⟩ := j3_frame gammaWordFacts_holds hq hZ3 e0 (F := K) hKea' hZK
      (hKcard.trans (by norm_num))
    have hcent : ∀ y ∈ Subgroup.normalizer (K : Set ↥L),
        π y ∈ Subgroup.centralizer ((K.map π : Subgroup _) : Set _) →
          ∀ x ∈ K, y * x = x * y := by
      intro y hy hc
      refine cent_of_frame hkk hZ3 hFK hNn hZK hy (fun x hx => ?_)
      rw [← hker_π, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      have := Subgroup.mem_centralizer_iff.1 hc (π x) (Subgroup.mem_map_of_mem π hx)
      rw [← this]
      group
    obtain ⟨e⟩ := autIn_equiv_automizer L π (QuotientGroup.mk'_surjective _) K hker_K hcent
    rw [← hAeq]
    refine ⟨rfl, ?_⟩
    have hK27 : Nat.card ↥(K.map π) = 27 := by
      have h1 : Nat.card K = 81 := hKcard.trans (by norm_num)
      omega
    have hE9 := Res417Three.isE9Z8_of_j3 (L := ↥L ⧸ Subgroup.center ↥L) ⟨e0'⟩ (K.map π) hKea' hK27
    exact IsExtOf.of_mulEquiv e.symm (Res417Three.isExtOf_of_isE9Z8 hE9)

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
